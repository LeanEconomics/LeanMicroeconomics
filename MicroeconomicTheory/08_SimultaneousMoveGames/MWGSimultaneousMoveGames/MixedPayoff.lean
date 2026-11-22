/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGSimultaneousMoveGames.Dominance
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Tactic.Linarith

/-!
# The algebra of mixed payoffs

MWG, Sections 7.E and 8.B, pp. 232 and 240.

The mixed payoff `u_i(σ) = ∑_s σ₁(s₁) ⋯ σ_I(s_I) u_i(s)` is Chapter 7's
`NormalForm.mixedPayoff`. This module proves the identities that the chapter uses throughout:

* `mixedPayoff_update`: `u_k(τ, σ_{-i}) = ∑_s τ(s_i) [∏_{j ≠ i} σ_j(s_j)] u_k(s)`.
* `mixedPayoff_update_eq_sum_pure`: `u_k(τ, σ_{-i}) = ∑_{s_i} τ(s_i) u_k(s_i, σ_{-i})`, so a
  player's payoff is linear in his own mixed strategy (`mixedPayoff_update_add_smul`).
* `mixedPayoff_update_eq_expect`: the formula of p. 240,
  `u_k(τ, σ_{-i}) = ∑_{s_{-i}} [∏_{k ≠ i} σ_k(s_k)] u_k(τ, s_{-i})`, written as a sum over full
  pure profiles drawn from the mixed profile `σ` (whose `i`-th coordinate sums to one).
* `mixedPayoff_compound`: a mixed profile drawn from independent beliefs over mixed strategies
  has the payoff of the compound profile (used for footnote 1, p. 243).
-/

namespace MWG.SimultaneousMoveGames

open MWG.NoncooperativeGames Function Finset

variable {I : Type*} {S : I → Type*} [Fintype I] [DecidableEq I] [∀ i, Fintype (S i)]

/-- A profile `σ = (σ₁, …, σ_I)` of mixed strategies. -/
def IsMixedProfile (σ : (i : I) → S i → ℝ) : Prop := ∀ i, IsMixedStrategy (σ i)

/-- The degenerate mixed profile that plays the pure profile `s` with probability one. -/
def pureProfile [∀ i, DecidableEq (S i)] (s : (i : I) → S i) : (i : I) → S i → ℝ :=
  fun i => pureMixed (s i)

omit [Fintype I] [DecidableEq I] in
theorem isMixedProfile_pureProfile [∀ i, DecidableEq (S i)] (s : (i : I) → S i) :
    IsMixedProfile (pureProfile s) := fun i => isMixedStrategy_pureMixed (s i)

omit [Fintype I] [∀ i, Fintype (S i)] in
/-- Replacing one coordinate of a pure profile commutes with taking the degenerate profile. -/
theorem pureProfile_update [∀ i, DecidableEq (S i)] (s : (i : I) → S i) (i : I) (a : S i) :
    update (pureProfile s) i (pureMixed a) = pureProfile (update s i a) := by
  funext j
  by_cases h : j = i
  · subst h
    simp [pureProfile]
  · simp [pureProfile, update_of_ne h]

omit [∀ i, Fintype (S i)] in
/-- The weight of a pure profile when coordinate `i` is replaced. -/
theorem prod_update_eq (σ : (i : I) → S i → ℝ) (i : I) (τ : S i → ℝ) (s : (i : I) → S i) :
    ∏ j, update σ i τ j (s j) = τ (s i) * ∏ j ∈ univ.erase i, σ j (s j) := by
  rw [← Finset.mul_prod_erase univ _ (mem_univ i), update_self]
  congr 1
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [update_of_ne (ne_of_mem_erase hj)]

/-- **Section 8.B** (MWG, p. 240). `u_k(τ, σ_{-i}) = ∑_s τ(s_i) [∏_{j ≠ i} σ_j(s_j)] u_k(s)`. -/
theorem mixedPayoff_update (N : NormalForm I S) (σ : (i : I) → S i → ℝ) (i : I)
    (τ : S i → ℝ) (k : I) :
    N.mixedPayoff (update σ i τ) k =
      ∑ s : (i : I) → S i, τ (s i) * ((∏ j ∈ univ.erase i, σ j (s j)) * N.payoff k s) := by
  unfold NormalForm.mixedPayoff
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [prod_update_eq, mul_assoc]

/-- The payoff of player `k` does not depend on the `i`-th coordinate of `σ` once that
coordinate is replaced. -/
theorem mixedPayoff_update_update (N : NormalForm I S) (σ : (i : I) → S i → ℝ) (i : I)
    (τ τ' : S i → ℝ) (k : I) :
    N.mixedPayoff (update (update σ i τ') i τ) k = N.mixedPayoff (update σ i τ) k := by
  rw [update_idem]

/-- Linearity of `u_k(·, σ_{-i})` in player `i`'s own mixed strategy:
`u_k(τ + c • τ', σ_{-i}) = u_k(τ, σ_{-i}) + c u_k(τ', σ_{-i})`. -/
theorem mixedPayoff_update_add_smul (N : NormalForm I S) (σ : (i : I) → S i → ℝ) (i : I)
    (τ τ' : S i → ℝ) (c : ℝ) (k : I) :
    N.mixedPayoff (update σ i (τ + c • τ')) k =
      N.mixedPayoff (update σ i τ) k + c * N.mixedPayoff (update σ i τ') k := by
  simp only [mixedPayoff_update, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  ring

/-- Linearity: `u_k(∑_x c_x τ_x, σ_{-i}) = ∑_x c_x u_k(τ_x, σ_{-i})`. -/
theorem mixedPayoff_update_sum_smul (N : NormalForm I S) (σ : (i : I) → S i → ℝ) (i : I)
    {K : Type*} [Fintype K] (c : K → ℝ) (τ : K → S i → ℝ) (k : I) :
    N.mixedPayoff (update σ i (∑ x, c x • τ x)) k =
      ∑ x, c x * N.mixedPayoff (update σ i (τ x)) k := by
  simp only [mixedPayoff_update, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun x _ => ?_
  ring

variable [∀ i, DecidableEq (S i)]

/-- **Section 8.D** (MWG, p. 251). A player's payoff is the average, under his own mixed
strategy, of the payoffs of his pure strategies: `u_k(τ, σ_{-i}) = ∑_a τ(a) u_k(a, σ_{-i})`. -/
theorem mixedPayoff_update_eq_sum_pure (N : NormalForm I S) (σ : (i : I) → S i → ℝ) (i : I)
    (τ : S i → ℝ) (k : I) :
    N.mixedPayoff (update σ i τ) k =
      ∑ a, τ a * N.mixedPayoff (update σ i (pureMixed a)) k := by
  have hτ : τ = ∑ a, τ a • pureMixed a := by
    funext b
    simp [Finset.sum_apply, pureMixed]
  conv_lhs => rw [hτ]
  exact mixedPayoff_update_sum_smul N σ i τ (fun a => pureMixed a) k

/-- The payoff against a pure profile with player `i` replaced by the pure strategy `a`. -/
theorem mixedPayoff_pureProfile_update (N : NormalForm I S) (s : (i : I) → S i) (i : I)
    (a : S i) (k : I) :
    N.mixedPayoff (update (pureProfile s) i (pureMixed a)) k = N.payoff k (update s i a) := by
  rw [pureProfile_update]
  exact N.mixedPayoff_pure _ k

/-- The payoff of a degenerate profile is the pure payoff. -/
theorem mixedPayoff_pureProfile (N : NormalForm I S) (s : (i : I) → S i) (k : I) :
    N.mixedPayoff (pureProfile s) k = N.payoff k s :=
  N.mixedPayoff_pure s k

/-- Against a pure rival profile, `u_k(τ, s_{-i}) = ∑_a τ(a) u_k(a, s_{-i})`. -/
theorem mixedPayoff_pureProfile_update_mixed (N : NormalForm I S) (s : (i : I) → S i) (i : I)
    (τ : S i → ℝ) (k : I) :
    N.mixedPayoff (update (pureProfile s) i τ) k = ∑ a, τ a * N.payoff k (update s i a) := by
  rw [mixedPayoff_update_eq_sum_pure]
  simp only [mixedPayoff_pureProfile_update]

omit [DecidableEq I] [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] in
/-- The probability that the mixed profile `σ` plays the pure profile `s` is nonnegative. -/
theorem prod_mixed_nonneg {σ : (i : I) → S i → ℝ} (hσ : ∀ i a, 0 ≤ σ i a)
    (s : (i : I) → S i) : 0 ≤ ∏ j, σ j (s j) :=
  Finset.prod_nonneg fun j _ => hσ j _

omit [∀ i, DecidableEq (S i)] in
/-- The weights `∏_{j} σ_j(s_j)` of a mixed profile sum to one. -/
theorem sum_prod_mixed_eq_one {σ : (i : I) → S i → ℝ} (hσ : ∀ i, ∑ a, σ i a = 1) :
    ∑ s : (i : I) → S i, ∏ j, σ j (s j) = 1 := by
  rw [← Fintype.prod_sum]
  exact Finset.prod_eq_one fun j _ => hσ j

/-- **Section 8.B** (MWG, p. 240). The payoff against a mixed profile is the expectation of
the payoffs against the pure rival profiles drawn from it:
`u_k(τ, σ_{-i}) = ∑_{s} [∏_j σ_j(s_j)] u_k(τ, s_{-i})`, where the `i`-th coordinate of `σ` only
needs to sum to one (it integrates out). -/
theorem mixedPayoff_update_eq_expect (N : NormalForm I S) (σ : (i : I) → S i → ℝ) (i : I)
    (hσi : ∑ a, σ i a = 1) (τ : S i → ℝ) (k : I) :
    N.mixedPayoff (update σ i τ) k =
      ∑ s : (i : I) → S i, (∏ j, σ j (s j)) * N.mixedPayoff (update (pureProfile s) i τ) k := by
  simp only [mixedPayoff_update, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  -- the weight of `t` among the pure rival profiles drawn from `σ`
  have key : ∑ s : (i : I) → S i,
      (∏ j, σ j (s j)) * ∏ j ∈ univ.erase i, pureProfile s j (t j) =
        ∏ j ∈ univ.erase i, σ j (t j) := by
    have hG : ∀ s : (i : I) → S i, (∏ j, σ j (s j)) * ∏ j ∈ univ.erase i, pureProfile s j (t j)
        = ∏ j, (σ j (s j) * if j = i then 1 else pureMixed (s j) (t j)) := by
      intro s
      rw [Finset.prod_mul_distrib, ← Finset.mul_prod_erase univ
        (fun j => if j = i then (1 : ℝ) else pureMixed (s j) (t j)) (mem_univ i)]
      simp only [ite_true, one_mul]
      congr 1
      refine Finset.prod_congr rfl fun j hj => ?_
      simp only [ne_of_mem_erase hj, ↓reduceIte]
      rfl
    simp_rw [hG]
    rw [← Fintype.prod_sum (fun j x => σ j x * if j = i then 1 else pureMixed x (t j)),
      ← Finset.mul_prod_erase univ _ (mem_univ i)]
    simp only [ite_true, mul_one, hσi, one_mul]
    refine Finset.prod_congr rfl fun j hj => ?_
    simp only [ne_of_mem_erase hj, ↓reduceIte, pureMixed, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    simp
  calc τ (t i) * ((∏ j ∈ univ.erase i, σ j (t j)) * N.payoff k t)
      = (∑ s : (i : I) → S i,
          (∏ j, σ j (s j)) * ∏ j ∈ univ.erase i, pureProfile s j (t j)) *
          (τ (t i) * N.payoff k t) := by rw [key]; ring
    _ = _ := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun s _ => ?_
      ring

/-- **Section 8.B** (MWG, p. 240). If `u_i(τ, s_{-i}) ≤ u_i(τ', s_{-i})` against every pure rival
profile, the same holds against every mixed profile. -/
theorem mixedPayoff_le_of_pure (N : NormalForm I S) {σ : (i : I) → S i → ℝ}
    (hσ : IsMixedProfile σ) (i : I) {τ τ' : S i → ℝ} (k : I)
    (h : ∀ s, N.mixedPayoff (update (pureProfile s) i τ) k ≤
      N.mixedPayoff (update (pureProfile s) i τ') k) :
    N.mixedPayoff (update σ i τ) k ≤ N.mixedPayoff (update σ i τ') k := by
  rw [mixedPayoff_update_eq_expect N σ i (hσ i).2, mixedPayoff_update_eq_expect N σ i (hσ i).2]
  exact Finset.sum_le_sum fun s _ =>
    mul_le_mul_of_nonneg_left (h s) (prod_mixed_nonneg (fun j a => (hσ j).1 a) s)

/-- **Section 8.B** (MWG, p. 240). Strict version: if `u_i(τ, s_{-i}) < u_i(τ', s_{-i})` against
every pure rival profile, the same holds against every mixed profile. -/
theorem mixedPayoff_lt_of_pure (N : NormalForm I S) {σ : (i : I) → S i → ℝ}
    (hσ : IsMixedProfile σ) (i : I) {τ τ' : S i → ℝ} (k : I)
    (h : ∀ s, N.mixedPayoff (update (pureProfile s) i τ) k <
      N.mixedPayoff (update (pureProfile s) i τ') k) :
    N.mixedPayoff (update σ i τ) k < N.mixedPayoff (update σ i τ') k := by
  rw [mixedPayoff_update_eq_expect N σ i (hσ i).2, mixedPayoff_update_eq_expect N σ i (hσ i).2]
  have hsum := sum_prod_mixed_eq_one (fun j => (hσ j).2)
  obtain ⟨s₀, -, hs₀⟩ : ∃ s ∈ (univ : Finset ((i : I) → S i)), 0 < ∏ j, σ j (s j) := by
    by_contra hno
    push Not at hno
    have : ∑ s : (i : I) → S i, ∏ j, σ j (s j) ≤ 0 := Finset.sum_nonpos hno
    linarith
  exact Finset.sum_lt_sum
    (fun s _ => mul_le_mul_of_nonneg_left (h s).le
      (prod_mixed_nonneg (fun j a => (hσ j).1 a) s))
    ⟨s₀, mem_univ _, mul_lt_mul_of_pos_left (h s₀) hs₀⟩

omit [∀ i, DecidableEq (S i)] in
/-- The mixed payoff of player `k` against a mixed profile is bounded by `∑_s |u_k(s)|`. -/
theorem abs_mixedPayoff_le (N : NormalForm I S) {σ : (i : I) → S i → ℝ}
    (hσ : IsMixedProfile σ) (k : I) :
    |N.mixedPayoff σ k| ≤ ∑ s, |N.payoff k s| := by
  unfold NormalForm.mixedPayoff
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun s _ => ?_)
  rw [abs_mul, abs_of_nonneg (prod_mixed_nonneg (fun j a => (hσ j).1 a) s)]
  have h1 : ∏ j, σ j (s j) ≤ 1 := by
    rw [← sum_prod_mixed_eq_one (fun j => (hσ j).2)]
    exact Finset.single_le_sum (fun t _ => prod_mixed_nonneg (fun j a => (hσ j).1 a) t)
      (mem_univ s)
  exact (mul_le_of_le_one_left (abs_nonneg _) h1)

omit [∀ i, DecidableEq (S i)] in
/-- **Footnote 1** (MWG, p. 243), the computation behind it. If each player `j`'s strategy is
drawn independently from finitely many mixed strategies `τ_j(x)` with probabilities `π_j(x)`,
the expected payoff is the payoff of the compound profile `ρ_j = ∑_x π_j(x) τ_j(x)`. -/
theorem mixedPayoff_compound (N : NormalForm I S) {K : I → Type*} [∀ j, Fintype (K j)]
    (π : (j : I) → K j → ℝ) (τ : (j : I) → K j → S j → ℝ) (k : I) :
    ∑ x : (j : I) → K j, (∏ j, π j (x j)) * N.mixedPayoff (fun j => τ j (x j)) k =
      N.mixedPayoff (fun j => ∑ y, π j y • τ j y) k := by
  unfold NormalForm.mixedPayoff
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Fintype.prod_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.prod_mul_distrib]
  ring

end MWG.SimultaneousMoveGames
