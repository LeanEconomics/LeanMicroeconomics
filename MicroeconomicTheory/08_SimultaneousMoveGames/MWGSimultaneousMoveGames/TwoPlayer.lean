/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGSimultaneousMoveGames.Rationalizable
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Pi

/-!
# Never a best response versus strictly dominated: the separating-hyperplane argument

MWG, Section 8.C, pp. 243-245, and Exercise 8.C.3 (p. 262).

* `bestResponse_correlated_of_not_dominated`: in any finite game, a pure strategy `s_i` that is
  not strictly dominated by a mixed strategy is a best response to some *correlated* belief
  `μ` over the rivals' pure strategy profiles. The proof separates the convex set
  `{(u_i(σ_i', s_{-i}) - u_i(s_i, s_{-i}))_{s_{-i}} : σ_i' ∈ Δ(S_i)}` from the open positive
  orthant by a hyperplane (Mathlib's Hahn-Banach `geometric_hahn_banach_open`); the normal of
  the hyperplane, normalized, is `μ`. This is the remark on p. 245 that the equivalence
  reemerges when the rivals' randomizations may be correlated (`correlated_iff_not_dominated`).
* `expect_eq_mixedPayoff_marginals`: a payoff that depends only on the strategy of one rival
  has the same expectation under `μ` and under the product of the marginals of `μ`.
* **Exercise 8.C.3** (`exercise_8_C_3`): in a two-player game with finite strategy sets, a pure
  strategy that is never a best response to a mixed strategy of the opponent is strictly
  dominated by some mixed strategy (Figure 8.C.2 is the picture).
-/

namespace MWG.SimultaneousMoveGames

open MWG.NoncooperativeGames Function Finset

variable {I : Type*} {S : I → Type*} [Fintype I] [DecidableEq I] [∀ i, Fintype (S i)]
  [∀ i, DecidableEq (S i)]

/-- A (correlated) belief over pure strategy profiles: a probability vector on `S`. -/
def IsBelief (μ : ((i : I) → S i) → ℝ) : Prop := (∀ s, 0 ≤ μ s) ∧ ∑ s, μ s = 1

/-- The expected payoff to player `i` from the mixed strategy `τ` when the rivals' pure strategy
profile `s_{-i}` is drawn from the belief `μ` (the `i`-th coordinate of `s` is ignored). -/
def beliefPayoff (N : NormalForm I S) (i : I) (μ : ((i : I) → S i) → ℝ) (τ : S i → ℝ) : ℝ :=
  ∑ s, μ s * N.mixedPayoff (update (pureProfile s) i τ) i

/-- **Section 8.C** (MWG, p. 245, small type). In a finite game, a pure strategy `a` of player `i`
that is not strictly dominated by any mixed strategy is a best response to some correlated belief
over the rivals' pure strategy profiles. -/
theorem bestResponse_correlated_of_not_dominated (N : NormalForm I S) (i : I) (a : S i)
    (hnd : ¬ MixedStrictlyDominated N i (pureMixed a)) :
    ∃ μ, IsBelief μ ∧ ∀ τ', IsMixedStrategy τ' →
      beliefPayoff N i μ τ' ≤ beliefPayoff N i μ (pureMixed a) := by
  classical
  -- the gains `d(τ')(s) = u_i(τ', s_{-i}) - u_i(a, s_{-i})`
  set d : (S i → ℝ) → ((i : I) → S i) → ℝ := fun τ' s =>
    N.mixedPayoff (update (pureProfile s) i τ') i -
      N.mixedPayoff (update (pureProfile s) i (pureMixed a)) i with hd
  set C : Set (((i : I) → S i) → ℝ) := d '' mixedExtension (S i) with hC
  set P : Set (((i : I) → S i) → ℝ) := {x | ∀ s, 0 < x s} with hP
  have hPopen : IsOpen P := by
    rw [hP, Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun s => isOpen_lt continuous_const (continuous_apply s)
  have hPconv : Convex ℝ P := by
    intro x hx y hy p q hp hq hpq s
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases hp.eq_or_lt with rfl | hp'
    · simp only [zero_add] at hpq; subst hpq; simpa using hy s
    · nlinarith [hx s, hy s]
  have hdaff : ∀ τ₁ τ₂ (p q : ℝ), p + q = 1 → d (p • τ₁ + q • τ₂) = p • d τ₁ + q • d τ₂ := by
    intro τ₁ τ₂ p q hpq
    funext s
    simp only [hd, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have h1 := mixedPayoff_update_add_smul N (pureProfile s) i (p • τ₁) τ₂ q i
    have h2 : N.mixedPayoff (update (pureProfile s) i (p • τ₁)) i =
        p * N.mixedPayoff (update (pureProfile s) i τ₁) i := by
      have := mixedPayoff_update_add_smul N (pureProfile s) i 0 τ₁ p i
      simp only [zero_add] at this
      rw [this]
      simp [mixedPayoff_update]
    rw [h1, h2]
    have : p * N.mixedPayoff (update (pureProfile s) i (pureMixed a)) i +
        q * N.mixedPayoff (update (pureProfile s) i (pureMixed a)) i =
        N.mixedPayoff (update (pureProfile s) i (pureMixed a)) i := by rw [← add_mul, hpq, one_mul]
    linarith
  have hCconv : Convex ℝ C := by
    rintro _ ⟨τ₁, h₁, rfl⟩ _ ⟨τ₂, h₂, rfl⟩ p q hp hq hpq
    exact ⟨p • τ₁ + q • τ₂, convex_mixedExtension (S i) h₁ h₂ hp hq hpq, hdaff τ₁ τ₂ p q hpq⟩
  have hdisj : Disjoint P C := by
    rw [Set.disjoint_left]
    rintro x hx ⟨τ', hτ', rfl⟩
    refine hnd ⟨τ', hτ', (mixedStrictlyDominates_iff_pure N i τ' _).2 fun s => ?_⟩
    have := hx s
    simp only [hd] at this
    linarith
  obtain ⟨f, u₀, hfP, hfC⟩ := geometric_hahn_banach_open hPconv hPopen hCconv hdisj
  -- coordinates of the separating functional
  set p : ((i : I) → S i) → ℝ := fun s => f (Pi.single s 1) with hpdef
  have hf : ∀ x, f x = ∑ s, x s * p s := by
    intro x
    have := LinearMap.pi_apply_eq_sum_univ (f : (((i : I) → S i) → ℝ) →ₗ[ℝ] ℝ) x
    simp only [ContinuousLinearMap.coe_coe] at this
    rw [this]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [smul_eq_mul, hpdef]
    congr 2
    funext t
    simp only [Pi.single_apply, eq_comm]
  have h0C : (0 : ((i : I) → S i) → ℝ) ∈ C :=
    ⟨pureMixed a, isMixedStrategy_pureMixed a, by funext s; simp [hd]⟩
  have hu₀ : u₀ ≤ 0 := by simpa using hfC 0 h0C
  have hone : (fun _ => (1 : ℝ)) ∈ P := fun _ => one_pos
  have hgap : ∑ s, p s < u₀ := by
    have := hfP _ hone
    rw [hf] at this
    simpa only [one_mul] using this
  have hsump : ∑ s, p s < 0 := by linarith
  -- the separating normal points into the negative orthant
  have hpneg : ∀ s₀, p s₀ ≤ 0 := by
    intro s₀
    by_contra hpos
    push Not at hpos
    set t : ℝ := (u₀ - ∑ s, p s) / p s₀ + 1 with ht
    have htpos : 0 < t := by
      have : 0 ≤ (u₀ - ∑ s, p s) / p s₀ := div_nonneg (by linarith) hpos.le
      linarith
    have hx : (fun s => (1 : ℝ) + if s = s₀ then t else 0) ∈ P := by
      intro s
      change 0 < 1 + (if s = s₀ then t else 0)
      split_ifs <;> linarith
    have := hfP _ hx
    rw [hf] at this
    simp only [add_mul, one_mul, Finset.sum_add_distrib, ite_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true] at this
    have h2 : t * p s₀ = u₀ - ∑ s, p s + p s₀ := by
      rw [ht, add_mul, div_mul_cancel₀ _ hpos.ne', one_mul]
    linarith
  -- the belief: the normalized negative of the normal
  set Z : ℝ := -∑ s, p s with hZ
  have hZpos : 0 < Z := by linarith
  refine ⟨fun s => -p s / Z, ⟨fun s => div_nonneg (by linarith [hpneg s]) hZpos.le, ?_⟩,
    fun τ' hτ' => ?_⟩
  · rw [← Finset.sum_div, Finset.sum_neg_distrib, ← hZ, div_self hZpos.ne']
  · -- `f(d(τ')) ≥ 0`
    have hfd : 0 ≤ f (d τ') := by
      by_contra hneg
      push Not at hneg
      have hε : 0 < f (d τ') / ∑ s, p s := div_pos_of_neg_of_neg hneg hsump
      have hx : (fun _ => f (d τ') / ∑ s, p s) ∈ P := fun _ => hε
      have h1 := hfP _ hx
      have h2 := hfC _ ⟨τ', hτ', rfl⟩
      rw [hf (fun _ => _)] at h1
      rw [← Finset.mul_sum, div_mul_cancel₀ _ hsump.ne] at h1
      linarith
    rw [hf] at hfd
    unfold beliefPayoff
    have key : ∑ s, -p s / Z * N.mixedPayoff (update (pureProfile s) i τ') i -
        ∑ s, -p s / Z * N.mixedPayoff (update (pureProfile s) i (pureMixed a)) i =
        -(∑ s, d τ' s * p s) / Z := by
      rw [← Finset.sum_sub_distrib, neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun s _ => ?_
      simp only [hd]
      ring
    have : -(∑ s, d τ' s * p s) / Z ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hZpos.le
    linarith

/-- **Section 8.C** (MWG, p. 245, small type). With correlated beliefs the equivalence holds for
any number of players: a pure strategy is a best response to some correlated belief iff it is
not strictly dominated. -/
theorem correlated_iff_not_dominated (N : NormalForm I S) (i : I) (a : S i) :
    (∃ μ, IsBelief μ ∧ ∀ τ', IsMixedStrategy τ' →
      beliefPayoff N i μ τ' ≤ beliefPayoff N i μ (pureMixed a)) ↔
      ¬ MixedStrictlyDominated N i (pureMixed a) := by
  refine ⟨?_, bestResponse_correlated_of_not_dominated N i a⟩
  rintro ⟨μ, hμ, hbr⟩ ⟨τ', hτ', hdom⟩
  have hlt := (mixedStrictlyDominates_iff_pure N i τ' _).1 hdom
  obtain ⟨s₀, hs₀⟩ : ∃ s, 0 < μ s := by
    by_contra hno
    push Not at hno
    have : ∑ s, μ s ≤ 0 := Finset.sum_nonpos fun s _ => hno s
    linarith [hμ.2]
  have : beliefPayoff N i μ (pureMixed a) < beliefPayoff N i μ τ' := by
    refine Finset.sum_lt_sum (fun s _ => mul_le_mul_of_nonneg_left (hlt s).le (hμ.1 s))
      ⟨s₀, mem_univ _, mul_lt_mul_of_pos_left (hlt s₀) hs₀⟩
  linarith [hbr τ' hτ']

/-- The marginal of a belief `μ` on player `k`'s pure strategies. -/
def marginal (μ : ((i : I) → S i) → ℝ) (k : I) : S k → ℝ :=
  fun b => ∑ s ∈ univ.filter (fun s : (i : I) → S i => s k = b), μ s

/-- The marginals of a belief are mixed strategies. -/
theorem isMixedProfile_marginal {μ : ((i : I) → S i) → ℝ} (hμ : IsBelief μ) :
    IsMixedProfile (marginal μ) := by
  intro k
  refine ⟨fun b => Finset.sum_nonneg fun s _ => hμ.1 s, ?_⟩
  unfold marginal
  rw [Finset.sum_fiberwise univ (fun s : (i : I) → S i => s k) μ]
  exact hμ.2

/-- A function of the profile that depends only on player `j`'s strategy has the same expectation
under a belief `μ` and under the independent product of its marginals. -/
theorem expect_eq_mixedPayoff_marginals {μ : ((i : I) → S i) → ℝ} (hμ : IsBelief μ) (j : I)
    (g : ((i : I) → S i) → ℝ) (hg : ∀ s s' : (i : I) → S i, s j = s' j → g s = g s') :
    ∑ s, μ s * g s = ∑ s, (∏ k, marginal μ k (s k)) * g s := by
  obtain ⟨s₀⟩ : Nonempty ((i : I) → S i) := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := hμ.2
    simp at this
  set h : S j → ℝ := fun b => g (update s₀ j b) with hh
  have hgh : ∀ s, g s = h (s j) := fun s => hg _ _ (by simp)
  -- the left side, fiber by fiber
  have hL : ∑ s, μ s * g s = ∑ b, marginal μ j b * h b := by
    rw [← Finset.sum_fiberwise univ (fun s : (i : I) → S i => s j)]
    refine Finset.sum_congr rfl fun b _ => ?_
    unfold marginal
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [hgh s, (Finset.mem_filter.1 hs).2]
  -- the right side, via the auxiliary game whose payoff is `h(s_j)`
  set G : NormalForm I S := ⟨fun _ s => h (s j)⟩ with hG
  have hR : ∑ s, (∏ k, marginal μ k (s k)) * g s = G.mixedPayoff (marginal μ) j := by
    unfold NormalForm.mixedPayoff
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hgh s]
  have hpure : ∀ b, G.mixedPayoff (update (marginal μ) j (pureMixed b)) j = h b := by
    intro b
    unfold NormalForm.mixedPayoff
    have hterm : ∀ s : (i : I) → S i,
        (∏ k, update (marginal μ) j (pureMixed b) k (s k)) * G.payoff j s =
          (∏ k, update (marginal μ) j (pureMixed b) k (s k)) * h b := by
      intro s
      by_cases hsb : s j = b
      · simp [hG, hsb]
      · rw [prod_update_eq]
        simp [pureMixed, hsb]
    simp_rw [hterm]
    rw [← Finset.sum_mul, sum_prod_mixed_eq_one, one_mul]
    intro k
    by_cases hk : k = j
    · subst hk; simpa using (isMixedStrategy_pureMixed b).2
    · rw [update_of_ne hk]; exact (isMixedProfile_marginal hμ k).2
  rw [hL, hR]
  conv_rhs => rw [← update_eq_self j (marginal μ), mixedPayoff_update_eq_sum_pure]
  simp only [hpure]

/-- **Exercise 8.C.3** (MWG, p. 262). In a two-player game with finite strategy sets, if the pure
strategy `s_i` is never a best response to any mixed strategy of `i`'s opponent, then `s_i` is
strictly dominated by some mixed strategy `σ_i ∈ Δ(S_i)`. -/
theorem exercise_8_C_3 (N : NormalForm I S) {i j : I} (hij : i ≠ j)
    (htwo : ∀ k, k = i ∨ k = j) (a : S i) (hnbr : NeverBestResponse N i (pureMixed a)) :
    MixedStrictlyDominated N i (pureMixed a) := by
  by_contra hnd
  obtain ⟨μ, hμ, hbr⟩ := bestResponse_correlated_of_not_dominated N i a hnd
  -- the payoff against `s_{-i}` depends only on the opponent's strategy `s_j`
  have hdep : ∀ τ : S i → ℝ, ∀ s s' : (k : I) → S k, s j = s' j →
      N.mixedPayoff (update (pureProfile s) i τ) i =
        N.mixedPayoff (update (pureProfile s') i τ) i := by
    intro τ s s' hss'
    congr 1
    funext k
    rcases htwo k with rfl | rfl
    · simp
    · simp [update_of_ne (Ne.symm hij), pureProfile, hss']
  have hσ := isMixedProfile_marginal hμ
  refine hnbr (marginal μ) hσ ⟨isMixedStrategy_pureMixed a, fun τ' hτ' => ?_⟩
  have hconv : ∀ τ : S i → ℝ, beliefPayoff N i μ τ = N.mixedPayoff (update (marginal μ) i τ) i := by
    intro τ
    unfold beliefPayoff
    rw [expect_eq_mixedPayoff_marginals hμ j _ (hdep τ),
      mixedPayoff_update_eq_expect N (marginal μ) i (hσ i).2]
  rw [← hconv, ← hconv]
  exact hbr τ' hτ'

end MWG.SimultaneousMoveGames
