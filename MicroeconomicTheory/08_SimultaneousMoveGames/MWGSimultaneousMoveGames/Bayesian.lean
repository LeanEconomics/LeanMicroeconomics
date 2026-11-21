/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGSimultaneousMoveGames.Examples8CD

/-!
# Games of incomplete information: Bayesian Nash equilibrium

MWG, Section 8.E, pp. 253-257.

A Bayesian game `[I, {S_i}, {u_i(·)}, Θ, F(·)]` has finitely many types `Θ_i` for each player
(footnote 8 restricts Proposition 8.E.1 to this case), a prior `F` on `Θ = Θ_1 × ⋯ × Θ_I`, and
payoffs `u_i(s, θ)`. MWG write `u_i(s_i, s_{-i}, θ_i)`; the payoffs here may depend on the whole
type profile `θ` (needed in Exercise 8.E.1), which contains MWG's case (correction 4).

* `expectedPayoff`, (8.E.1): `ũ_i(s_1(·), …, s_I(·)) = E_θ[u_i(s_1(θ_1), …, s_I(θ_I), θ)]`;
  `toNormalForm` is the game `[I, {𝒮_i}, {ũ_i(·)}]` whose strategies are decision rules.
* **Definition 8.E.1** (`IsBNE`): a Nash equilibrium of that game.
* **Proposition 8.E.1** (`proposition_8_E_1`): with finitely many types, `s(·)` is a Bayesian
  Nash equilibrium iff every type of every player that occurs with positive probability plays a
  best response to the conditional distribution of the others' strategies (8.E.2).
* With finitely many strategies and types a mixed strategy Bayesian Nash equilibrium exists
  (`exists_mixed_BNE`, Proposition 8.D.2 applied to `toNormalForm`).
* **Example 8.E.1** (`example_8_E_1`): the DA's Brother with incomplete information: type I of
  prisoner 2 confesses, type II does not, and prisoner 1 does not confess if `μ < 1/6` and
  confesses if `μ > 1/6`.
-/

namespace MWG.SimultaneousMoveGames

open MWG.NoncooperativeGames Function Finset

/-- **Section 8.E** (MWG, p. 255). A Bayesian game: a prior `F` on type profiles `θ ∈ Θ` and
payoffs `u_i(s, θ)`. -/
structure BayesianGame (I : Type*) (S Θ : I → Type*) where
  /-- The joint distribution `F(θ_1, …, θ_I)` of the types (a probability vector). -/
  prior : ((i : I) → Θ i) → ℝ
  /-- Player `i`'s payoff `u_i(s, θ)` at the strategy profile `s` and type profile `θ`. -/
  payoff : I → ((i : I) → S i) → ((i : I) → Θ i) → ℝ

variable {I : Type*} {S Θ : I → Type*} [Fintype I] [DecidableEq I] [∀ i, Fintype (Θ i)]
  [∀ i, DecidableEq (Θ i)]

namespace BayesianGame

/-- The prior is a probability distribution. -/
def IsPrior (G : BayesianGame I S Θ) : Prop :=
  (∀ θ, 0 ≤ G.prior θ) ∧ ∑ θ, G.prior θ = 1

/-- The strategies actually played at the type profile `θ` under the decision rules `s(·)`. -/
def play (s : (i : I) → Θ i → S i) (θ : (i : I) → Θ i) : (i : I) → S i := fun j => s j (θ j)

/-- **(8.E.1)** (MWG, p. 255). Player `i`'s expected payoff
`ũ_i(s_1(·), …, s_I(·)) = E_θ[u_i(s_1(θ_1), …, s_I(θ_I), θ)]`. -/
def expectedPayoff (G : BayesianGame I S Θ) (s : (i : I) → Θ i → S i) (i : I) : ℝ :=
  ∑ θ, G.prior θ * G.payoff i (play s θ) θ

/-- **Section 8.E** (MWG, p. 255). The normal form `[I, {𝒮_i}, {ũ_i(·)}]` of a Bayesian game: pure
strategies are decision rules `s_i : Θ_i → S_i`. -/
def toNormalForm (G : BayesianGame I S Θ) : NormalForm I (fun i => Θ i → S i) where
  payoff i s := G.expectedPayoff s i

/-- **Definition 8.E.1** (MWG, p. 255). A (pure strategy) Bayesian Nash equilibrium: a profile of
decision rules that is a Nash equilibrium of `[I, {𝒮_i}, {ũ_i(·)}]`. -/
def IsBNE (G : BayesianGame I S Θ) (s : (i : I) → Θ i → S i) : Prop :=
  IsNashEquilibrium G.toNormalForm s

omit [∀ i, DecidableEq (Θ i)] in
/-- **Definition 8.E.1** (MWG, p. 255), unfolded: `ũ_i(s_i(·), s_{-i}(·)) ≥ ũ_i(s_i'(·), s_{-i}(·))`
for all `s_i'(·)` and all `i`. -/
theorem isBNE_iff (G : BayesianGame I S Θ) (s : (i : I) → Θ i → S i) :
    G.IsBNE s ↔ ∀ i (s' : Θ i → S i), G.expectedPayoff (update s i s') i ≤ G.expectedPayoff s i :=
  Iff.rfl

/-- The probability `Prob(θ_i = t)` that player `i` has type `t`. -/
def typeProb (G : BayesianGame I S Θ) (i : I) (t : Θ i) : ℝ :=
  ∑ θ ∈ univ.filter (fun θ : (i : I) → Θ i => θ i = t), G.prior θ

/-- The expected payoff of type `t` of player `i` from the strategy `a`, before dividing by the
probability of `t`: `∑_{θ : θ_i = t} F(θ) u_i(a, s_{-i}(θ_{-i}), θ)`. -/
def typeGain (G : BayesianGame I S Θ) (s : (i : I) → Θ i → S i) (i : I) (t : Θ i) (a : S i) :
    ℝ :=
  ∑ θ ∈ univ.filter (fun θ : (i : I) → Θ i => θ i = t), G.prior θ * G.payoff i
    (update (play s θ) i a) θ

/-- **(8.E.2)** (MWG, p. 256). The conditional expected payoff of type `t` of player `i` from
playing `a`: `E_{θ_{-i}}[u_i(a, s_{-i}(θ_{-i}), θ) | θ_i = t]`. -/
noncomputable def condPayoff (G : BayesianGame I S Θ) (s : (i : I) → Θ i → S i) (i : I)
    (t : Θ i) (a : S i) : ℝ :=
  G.typeGain s i t a / G.typeProb i t

omit [Fintype I] [∀ i, Fintype (Θ i)] [∀ i, DecidableEq (Θ i)] in
theorem play_update (s : (i : I) → Θ i → S i) (i : I) (s' : Θ i → S i)
    (θ : (i : I) → Θ i) : play (update s i s') θ = update (play s θ) i (s' (θ i)) := by
  funext j
  by_cases hj : j = i
  · subst hj; simp [play]
  · simp [play, update_of_ne hj]

/-- The expected payoff of player `i` is the sum, over his types, of the types' gains. -/
theorem expectedPayoff_update_eq (G : BayesianGame I S Θ) (s : (i : I) → Θ i → S i) (i : I)
    (s' : Θ i → S i) :
    G.expectedPayoff (update s i s') i = ∑ t, G.typeGain s i t (s' t) := by
  unfold expectedPayoff typeGain
  rw [← Finset.sum_fiberwise univ (fun θ : (i : I) → Θ i => θ i)]
  refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun θ hθ => ?_
  rw [play_update, (Finset.mem_filter.1 hθ).2]

/-- Playing the decision rule itself gives the types' gains at their own strategies. -/
theorem expectedPayoff_eq (G : BayesianGame I S Θ) (s : (i : I) → Θ i → S i) (i : I) :
    G.expectedPayoff s i = ∑ t, G.typeGain s i t (s i t) := by
  rw [← expectedPayoff_update_eq, update_eq_self]

/-- A type with probability zero has zero gain from every strategy. -/
theorem typeGain_eq_zero (G : BayesianGame I S Θ) (hG : G.IsPrior) (s : (i : I) → Θ i → S i)
    (i : I) (t : Θ i) (ht : G.typeProb i t = 0) (a : S i) : G.typeGain s i t a = 0 := by
  have hz : ∀ θ ∈ univ.filter (fun θ : (i : I) → Θ i => θ i = t), G.prior θ = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun θ _ => hG.1 θ).1 ht
  exact Finset.sum_eq_zero fun θ hθ => by rw [hz θ hθ, zero_mul]

/-- **Proposition 8.E.1** (MWG, pp. 255-256). With finitely many types, a profile of decision rules
is a Bayesian Nash equilibrium iff for every player `i` and every type `θ_i` that occurs with
positive probability, `s_i(θ_i)` maximizes the conditional expected payoff (8.E.2):
`E[u_i(s_i(θ_i), s_{-i}(θ_{-i}), θ) | θ_i] ≥ E[u_i(s_i', s_{-i}(θ_{-i}), θ) | θ_i]` for all
`s_i' ∈ S_i`. -/
theorem proposition_8_E_1 (G : BayesianGame I S Θ) (hG : G.IsPrior)
    (s : (i : I) → Θ i → S i) :
    G.IsBNE s ↔ ∀ i (t : Θ i), 0 < G.typeProb i t → ∀ a : S i,
      G.condPayoff s i t a ≤ G.condPayoff s i t (s i t) := by
  rw [isBNE_iff]
  constructor
  · intro h i t ht a
    -- deviate only at the type `t`
    have hdev := h i (update (s i) t a)
    rw [expectedPayoff_update_eq, expectedPayoff_eq,
      ← Finset.add_sum_erase _ _ (mem_univ t), ← Finset.add_sum_erase _ _ (mem_univ t)] at hdev
    have hrest : ∑ x ∈ univ.erase t, G.typeGain s i x (update (s i) t a x) =
        ∑ x ∈ univ.erase t, G.typeGain s i x (s i x) :=
      Finset.sum_congr rfl fun x hx => by rw [update_of_ne (ne_of_mem_erase hx)]
    rw [hrest, update_self] at hdev
    unfold condPayoff
    exact div_le_div_of_nonneg_right (by linarith) ht.le
  · intro h i s'
    rw [expectedPayoff_update_eq, expectedPayoff_eq]
    refine Finset.sum_le_sum fun t _ => ?_
    have hnn : 0 ≤ G.typeProb i t := Finset.sum_nonneg fun θ _ => hG.1 θ
    rcases hnn.eq_or_lt with h0 | hpos
    · rw [typeGain_eq_zero G hG s i t h0.symm, typeGain_eq_zero G hG s i t h0.symm]
    · have := h i t hpos (s' t)
      unfold condPayoff at this
      exact (div_le_div_iff_of_pos_right hpos).1 this

/-- With finitely many strategies and types, a Bayesian game has a mixed strategy Bayesian Nash
equilibrium: a mixed Nash equilibrium of `[I, {Δ(𝒮_i)}, {ũ_i(·)}]` (Proposition 8.D.2). -/
theorem exists_mixed_BNE [∀ i, Fintype (S i)] [∀ i, Nonempty (S i)]
    (G : BayesianGame I S Θ) : ∃ σ, IsMixedNash G.toNormalForm σ := by
  classical
  exact proposition_8_D_2 G.toNormalForm

end BayesianGame

/-! ### Example 8.E.1: the DA's Brother with incomplete information -/

/-- The number of types of each prisoner in Example 8.E.1: one for prisoner 1 (`false`), two for
prisoner 2 (`true`). -/
abbrev daDims : Bool → ℕ
  | false => 1
  | true => 2

/-- The type sets of Example 8.E.1. -/
abbrev DAΘ (b : Bool) : Type := Fin (daDims b)

/-- **Example 8.E.1** (MWG, p. 254). Prisoner 1 (`false`) has a single type; prisoner 2 (`true`) has
type I (`0`, the preferences of Figure 8.B.4) with probability `μ` and type II (`1`, a psychic
penalty of six years for confessing) with probability `1 - μ`. Actions: `0` = don't confess,
`1` = confess. -/
noncomputable def daBayes (μ : ℝ) : BayesianGame Bool (fun _ => Fin 2) DAΘ where
  prior θ := if θ true = 0 then μ else 1 - μ
  payoff i s θ := if i = false then daU₁ (s false) (s true) else
    daU₂ (s false) (s true) - if θ true = 1 ∧ s true = 1 then 6 else 0

/-- The type profile in which prisoner 2 has type `t`. -/
def daθ (t : Fin 2) : (b : Bool) → DAΘ b
  | false => 0
  | true => t

/-- Type profiles of Example 8.E.1 as pairs. -/
def daΘEquiv : ((b : Bool) → DAΘ b) ≃ DAΘ false × DAΘ true where
  toFun θ := (θ false, θ true)
  invFun p b := match b with
    | false => p.1
    | true => p.2
  left_inv θ := by funext b; cases b <;> rfl
  right_inv p := rfl

/-- Sums over the type profiles of Example 8.E.1. -/
theorem sum_daΘ (f : ((b : Bool) → DAΘ b) → ℝ) : ∑ θ, f θ = f (daθ 0) + f (daθ 1) := by
  rw [← daΘEquiv.symm.sum_comp, Fintype.sum_prod_type, Fin.sum_univ_one, Fin.sum_univ_two]
  rfl

theorem daBayes_isPrior {μ : ℝ} (h0 : 0 ≤ μ) (h1 : μ ≤ 1) : (daBayes μ).IsPrior := by
  refine ⟨fun θ => ?_, ?_⟩
  · simp only [daBayes]
    split_ifs <;> linarith
  · rw [sum_daΘ]
    simp [daBayes, daθ]

/-- **Example 8.E.1** (MWG, pp. 254-256). For `0 < μ < 1`, a profile of decision rules is a Bayesian
Nash equilibrium of the DA's Brother with incomplete information iff type I of prisoner 2
confesses, type II does not, and prisoner 1 does not confess when `μ < 1/6` and confesses when
`μ > 1/6` (either is optimal at `μ = 1/6`). -/
theorem example_8_E_1 {μ : ℝ} (h0 : 0 < μ) (h1 : μ < 1) (s : (b : Bool) → DAΘ b → Fin 2) :
    (daBayes μ).IsBNE s ↔ s true 0 = 1 ∧ s true 1 = 0 ∧
      (μ < 1 / 6 → s false 0 = 0) ∧ (1 / 6 < μ → s false 0 = 1) := by
  rw [BayesianGame.proposition_8_E_1 _ (daBayes_isPrior h0.le h1.le), Bool.forall_bool]
  -- the type probabilities and the conditional payoffs
  have hp0 : (daBayes μ).typeProb false 0 = 1 := by
    unfold BayesianGame.typeProb
    rw [Finset.sum_filter, sum_daΘ]
    simp [daBayes, daθ]
  have hp1 : ∀ t : Fin 2, (daBayes μ).typeProb true t = if t = 0 then μ else 1 - μ := by
    intro t
    unfold BayesianGame.typeProb
    rw [Finset.sum_filter, sum_daΘ]
    fin_cases t <;> simp [daBayes, daθ]
  have hc0 : ∀ a : Fin 2, (daBayes μ).condPayoff s false 0 a =
      μ * daU₁ a (s true 0) + (1 - μ) * daU₁ a (s true 1) := by
    intro a
    unfold BayesianGame.condPayoff BayesianGame.typeGain
    rw [hp0, div_one, Finset.sum_filter, sum_daΘ]
    simp [daBayes, daθ, BayesianGame.play, Function.update]
  have hc1 : ∀ t a : Fin 2, (daBayes μ).condPayoff s true t a =
      daU₂ (s false 0) a - if t = 1 ∧ a = 1 then 6 else 0 := by
    intro t a
    unfold BayesianGame.condPayoff BayesianGame.typeGain
    rw [hp1, Finset.sum_filter, sum_daΘ]
    have hμ : μ ≠ 0 := h0.ne'
    have hμ' : 1 - μ ≠ 0 := by linarith
    fin_cases t <;> simp [daBayes, daθ, BayesianGame.play, Function.update] <;> field_simp
  have hpos1 : ∀ t : Fin 2, 0 < (daBayes μ).typeProb true t := by
    intro t
    rw [hp1]
    split_ifs <;> linarith
  have hall0 : ∀ P : DAΘ false → Prop, (∀ t, P t) ↔ P 0 := fun P =>
    ⟨fun h => h 0, fun h t => (Subsingleton.elim t 0) ▸ h⟩
  rw [hall0, Fin.forall_fin_two]
  simp only [hp0, hpos1, zero_lt_one, true_imp_iff, hc0, hc1, Fin.forall_fin_two]
  generalize s false 0 = x
  generalize s true 0 = y
  generalize s true 1 = z
  constructor
  · rintro ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩, hz0, hz1⟩
    have hy : y = 1 := by
      fin_cases y
      · fin_cases x
        all_goals simp [daU₂] at hy1
        all_goals linarith
      · rfl
    have hz : z = 0 := by
      fin_cases z
      · rfl
      · fin_cases x
        all_goals simp [daU₂] at hz0
        all_goals linarith
    subst hy hz
    refine ⟨rfl, rfl, fun hμ => ?_, fun hμ => ?_⟩
    · fin_cases x
      · rfl
      · simp [daU₁] at hx0; linarith
    · fin_cases x
      · simp [daU₁] at hx1; linarith
      · rfl
  · rintro ⟨rfl, rfl, hlo, hhi⟩
    have hcase : x = 0 ∧ μ ≤ 1 / 6 ∨ x = 1 ∧ 1 / 6 ≤ μ := by
      rcases lt_trichotomy μ (1 / 6) with h | h | h
      · exact Or.inl ⟨hlo h, h.le⟩
      · fin_cases x
        · exact Or.inl ⟨rfl, h.le⟩
        · exact Or.inr ⟨rfl, h.ge⟩
      · exact Or.inr ⟨hhi h, h.le⟩
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;>
      rcases hcase with ⟨rfl, hμ⟩ | ⟨rfl, hμ⟩ <;> simp [daU₁, daU₂] <;> linarith

end MWG.SimultaneousMoveGames
