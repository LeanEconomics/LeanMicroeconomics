/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGSimultaneousMoveGames.MixedPayoff
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Module.Pi

/-!
# Mixed strategies: domination, best responses and mixed Nash equilibrium

MWG, Section 8.B (pp. 240-242), Definition 8.C.1 and footnote 1 (pp. 242-243) and Section 8.D
(pp. 250-251).

Throughout, `N : NormalForm I S` has finitely many players and finite pure strategy sets, and
the game `Γ_N = [I, {Δ(S_i)}, {u_i(·)}]` is its mixed extension; mixed strategies are probability
vectors `σ_i : S_i → ℝ` and `u_i(σ)` is `N.mixedPayoff σ i`.

* **Definition 8.B.4**: `MixedStrictlyDominates`, `MixedStrictlyDominated`,
  `MixedStrictlyDominant`; the pure test of p. 240 (`mixedStrictlyDominates_iff_pure`).
* **Proposition 8.B.1** (`proposition_8_B_1`) and **Exercise 8.B.6** (`exercise_8_B_6`).
* **Exercise 8.B.7** (`exercise_8_B_7`): a strictly dominant strategy is pure.
* **Definition 8.C.1**: `IsBestResponse`, `NeverBestResponse`; a strictly dominated strategy is
  never a best response (`neverBestResponse_of_mixedStrictlyDominated`, p. 243).
* **Footnote 1** (p. 243): a strategy that is optimal against an independent probabilistic
  conjecture is a best response to the compound profile (`footnote_8_1`).
* **Definition 8.D.2** (`IsMixedNash`) and its identity with Definition 8.D.1 applied to the
  mixed extension (`isMixedNash_iff_mixedExtensionGame`).
* **Proposition 8.D.1** (`proposition_8_D_1`), the pure-deviation test that follows from it
  (`isMixedNash_iff_pure_deviations`) and **Corollary 8.D.1** (`corollary_8_D_1`).
-/

namespace MWG.SimultaneousMoveGames

open MWG.NoncooperativeGames Function Finset

variable {I : Type*} {S : I → Type*} [Fintype I] [DecidableEq I] [∀ i, Fintype (S i)]
  [∀ i, DecidableEq (S i)]

/-- **Definition 8.B.4** (MWG, p. 240). `τ'` strictly dominates `τ` for player `i` in
`Γ_N = [I, {Δ(S_i)}, {u_i(·)}]`: `u_i(τ', σ_{-i}) > u_i(τ, σ_{-i})` for every profile `σ_{-i}`
of the rivals' mixed strategies (the `i`-th coordinate of `σ` is ignored). -/
def MixedStrictlyDominates (N : NormalForm I S) (i : I) (τ' τ : S i → ℝ) : Prop :=
  ∀ σ : (j : I) → S j → ℝ, IsMixedProfile σ →
    N.mixedPayoff (update σ i τ) i < N.mixedPayoff (update σ i τ') i

/-- **Definition 8.B.4** (MWG, p. 240). The mixed strategy `τ` is strictly dominated. -/
def MixedStrictlyDominated (N : NormalForm I S) (i : I) (τ : S i → ℝ) : Prop :=
  ∃ τ', IsMixedStrategy τ' ∧ MixedStrictlyDominates N i τ' τ

/-- **Definition 8.B.4** (MWG, p. 240). `τ` is a strictly dominant strategy: it strictly dominates
every other mixed strategy. -/
def MixedStrictlyDominant (N : NormalForm I S) (i : I) (τ : S i → ℝ) : Prop :=
  IsMixedStrategy τ ∧ ∀ τ', IsMixedStrategy τ' → τ' ≠ τ → MixedStrictlyDominates N i τ τ'

/-- **Section 8.B** (MWG, p. 240). To test whether `τ'` strictly dominates `τ` it suffices to
compare them against the pure strategies of the rivals:
`u_i(τ', σ_{-i}) > u_i(τ, σ_{-i})` for all `σ_{-i}` iff `u_i(τ', s_{-i}) > u_i(τ, s_{-i})` for all
`s_{-i}`. -/
theorem mixedStrictlyDominates_iff_pure (N : NormalForm I S) (i : I) (τ' τ : S i → ℝ) :
    MixedStrictlyDominates N i τ' τ ↔ ∀ s : (j : I) → S j,
      N.mixedPayoff (update (pureProfile s) i τ) i <
        N.mixedPayoff (update (pureProfile s) i τ') i :=
  ⟨fun h s => h _ (isMixedProfile_pureProfile s),
    fun h _ hσ => mixedPayoff_lt_of_pure N hσ i i h⟩

/-- **Proposition 8.B.1** (MWG, p. 241). Player `i`'s pure strategy `s_i` is strictly dominated
in `Γ_N = [I, {Δ(S_i)}, {u_i(·)}]` iff some mixed strategy `σ_i'` has
`u_i(σ_i', s_{-i}) > u_i(s_i, s_{-i})` for all `s_{-i}`. -/
theorem proposition_8_B_1 (N : NormalForm I S) (i : I) (a : S i) :
    MixedStrictlyDominated N i (pureMixed a) ↔ ∃ τ', IsMixedStrategy τ' ∧
      ∀ s : (j : I) → S j, N.payoff i (update s i a) <
        N.mixedPayoff (update (pureProfile s) i τ') i := by
  simp only [MixedStrictlyDominated, mixedStrictlyDominates_iff_pure,
    mixedPayoff_pureProfile_update]

/-- Moving the probability `c` of player `i`'s mixed strategy `τ` from the pure strategy `a`
to the mixed strategy `τ'` changes his payoff by `c (u_i(τ', σ_{-i}) - u_i(a, σ_{-i}))`. -/
theorem mixedPayoff_shift (N : NormalForm I S) (σ : (j : I) → S j → ℝ) (i : I)
    (τ τ' : S i → ℝ) (a : S i) (c : ℝ) (k : I) :
    N.mixedPayoff (update σ i (τ + c • (τ' - pureMixed a))) k =
      N.mixedPayoff (update σ i τ) k + c * (N.mixedPayoff (update σ i τ') k -
        N.mixedPayoff (update σ i (pureMixed a)) k) := by
  have h : τ' - pureMixed a = τ' + (-1 : ℝ) • pureMixed a := by
    funext b; simp [sub_eq_add_neg]
  rw [mixedPayoff_update_add_smul, h, mixedPayoff_update_add_smul]
  ring

omit [Fintype I] [DecidableEq I] in
/-- Moving the probability `c ≤ τ(a)` from the pure strategy `a` to a mixed strategy `τ'`
keeps `τ` a mixed strategy. -/
theorem isMixedStrategy_shift {i : I} {τ τ' : S i → ℝ} (hτ : IsMixedStrategy τ)
    (hτ' : IsMixedStrategy τ') {a : S i} {c : ℝ} (hc0 : 0 ≤ c) (hca : c ≤ τ a) :
    IsMixedStrategy (τ + c • (τ' - pureMixed a)) := by
  refine ⟨fun b => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, pureMixed]
    split_ifs with hb
    · subst hb
      nlinarith [hτ'.1 b]
    · nlinarith [hτ.1 b, hτ'.1 b]
  · simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, Finset.sum_sub_distrib, hτ.2, hτ'.2, (isMixedStrategy_pureMixed a).2]
    ring

/-- **Exercise 8.B.6** (MWG, p. 241). If the pure strategy `s_i` is strictly dominated in
`Γ_N = [I, {Δ(S_i)}, {u_i(·)}]`, so is every mixed strategy that plays `s_i` with positive
probability. -/
theorem exercise_8_B_6 (N : NormalForm I S) (i : I) (a : S i)
    (ha : MixedStrictlyDominated N i (pureMixed a)) {τ : S i → ℝ} (hτ : IsMixedStrategy τ)
    (hpos : 0 < τ a) : MixedStrictlyDominated N i τ := by
  obtain ⟨τ', hτ', hdom⟩ := ha
  refine ⟨τ + τ a • (τ' - pureMixed a), isMixedStrategy_shift hτ hτ' hpos.le le_rfl,
    fun σ hσ => ?_⟩
  rw [mixedPayoff_shift]
  have := hdom σ hσ
  nlinarith

/-- A mixed strategy is the average of its pure strategies: if all of them do at most `M`,
so does the mixed strategy. -/
theorem mixedPayoff_le_of_pure_le (N : NormalForm I S) (σ : (j : I) → S j → ℝ) (i : I)
    {τ : S i → ℝ} (hτ : IsMixedStrategy τ) {M : ℝ} (k : I)
    (h : ∀ a, N.mixedPayoff (update σ i (pureMixed a)) k ≤ M) :
    N.mixedPayoff (update σ i τ) k ≤ M := by
  rw [mixedPayoff_update_eq_sum_pure]
  calc ∑ a, τ a * N.mixedPayoff (update σ i (pureMixed a)) k ≤ ∑ a, τ a * M :=
        Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (h a) (hτ.1 a)
    _ = M := by rw [← Finset.sum_mul, hτ.2, one_mul]

/-- The uniform mixed strategy. -/
noncomputable def uniformMixed (T : Type*) [Fintype T] : T → ℝ :=
  fun _ => 1 / (Fintype.card T : ℝ)

theorem isMixedStrategy_uniformMixed (T : Type*) [Fintype T] [Nonempty T] :
    IsMixedStrategy (uniformMixed T) := by
  refine ⟨fun _ => by unfold uniformMixed; positivity, ?_⟩
  simp only [uniformMixed, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have : (Fintype.card T : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [mul_one_div_cancel this]

theorem uniformMixed_pos (T : Type*) [Fintype T] [Nonempty T] (t : T) :
    0 < uniformMixed T t := by
  unfold uniformMixed
  have : (0 : ℝ) < Fintype.card T := by exact_mod_cast Fintype.card_pos
  positivity

omit [Fintype I] [DecidableEq I] [∀ i, DecidableEq (S i)] in
/-- A mixed profile exists when every pure strategy set is nonempty. -/
theorem isMixedProfile_uniform [∀ i, Nonempty (S i)] :
    IsMixedProfile (fun i => uniformMixed (S i)) :=
  fun i => isMixedStrategy_uniformMixed (S i)

/-- **Exercise 8.B.7** (MWG, p. 262). A strictly dominant strategy in
`[I, {Δ(S_i)}, {u_i(·)}]` is a pure strategy (when every `S_j` is nonempty). -/
theorem exercise_8_B_7 [∀ i, Nonempty (S i)] (N : NormalForm I S) (i : I) {τ : S i → ℝ}
    (h : MixedStrictlyDominant N i τ) : ∃ a, τ = pureMixed a := by
  set σ : (j : I) → S j → ℝ := fun j => uniformMixed (S j)
  obtain ⟨a, -, hmax⟩ := Finset.exists_max_image univ
    (fun b => N.mixedPayoff (update σ i (pureMixed b)) i) univ_nonempty
  refine ⟨a, by_contra fun hne => ?_⟩
  have h1 := h.2 (pureMixed a) (isMixedStrategy_pureMixed a) (Ne.symm hne) σ
    isMixedProfile_uniform
  have h2 := mixedPayoff_le_of_pure_le N σ i h.1 i (fun b => hmax b (mem_univ b))
  linarith

/-- **Definition 8.C.1** (MWG, p. 242). `τ` is a best response for player `i` to the rivals'
strategies `σ_{-i}` (the `i`-th coordinate of `σ` is ignored): `u_i(τ, σ_{-i}) ≥ u_i(τ', σ_{-i})`
for all `τ' ∈ Δ(S_i)`. -/
def IsBestResponse (N : NormalForm I S) (i : I) (τ : S i → ℝ) (σ : (j : I) → S j → ℝ) :
    Prop :=
  IsMixedStrategy τ ∧ ∀ τ', IsMixedStrategy τ' →
    N.mixedPayoff (update σ i τ') i ≤ N.mixedPayoff (update σ i τ) i

/-- **Definition 8.C.1** (MWG, p. 242). `τ` is never a best response: there is no profile
`σ_{-i}` of mixed strategies of the rivals to which it is a best response. -/
def NeverBestResponse (N : NormalForm I S) (i : I) (τ : S i → ℝ) : Prop :=
  ∀ σ : (j : I) → S j → ℝ, IsMixedProfile σ → ¬ IsBestResponse N i τ σ

omit [∀ i, DecidableEq (S i)] in
/-- Best responses depend only on the rivals' strategies. -/
theorem isBestResponse_update (N : NormalForm I S) (i : I) (τ : S i → ℝ)
    (σ : (j : I) → S j → ℝ) (x : S i → ℝ) :
    IsBestResponse N i τ (update σ i x) ↔ IsBestResponse N i τ σ := by
  simp only [IsBestResponse, update_idem]

omit [∀ i, DecidableEq (S i)] in
/-- **Section 8.C** (MWG, p. 243). A strictly dominated strategy is never a best response. -/
theorem neverBestResponse_of_mixedStrictlyDominated (N : NormalForm I S) (i : I)
    {τ : S i → ℝ} (h : MixedStrictlyDominated N i τ) : NeverBestResponse N i τ := by
  rintro σ hσ ⟨-, hbr⟩
  obtain ⟨τ', hτ', hdom⟩ := h
  exact absurd (hbr τ' hτ') (not_le.2 (hdom σ hσ))

/-- **Section 8.D** (MWG, pp. 250-251). A mixed strategy is a best response iff every pure
strategy it plays with positive probability is a best response among the pure strategies. -/
theorem isBestResponse_iff_support (N : NormalForm I S) (i : I) {τ : S i → ℝ}
    (hτ : IsMixedStrategy τ) (σ : (j : I) → S j → ℝ) :
    IsBestResponse N i τ σ ↔ ∀ a, 0 < τ a → ∀ b,
      N.mixedPayoff (update σ i (pureMixed b)) i ≤
        N.mixedPayoff (update σ i (pureMixed a)) i := by
  constructor
  · rintro ⟨-, hbr⟩ a ha b
    by_contra hlt
    push Not at hlt
    have := hbr _ (isMixedStrategy_shift hτ (isMixedStrategy_pureMixed b) ha.le le_rfl)
    rw [mixedPayoff_shift] at this
    nlinarith
  · intro h
    refine ⟨hτ, fun τ' hτ' => ?_⟩
    obtain ⟨a₀, ha₀⟩ : ∃ a, 0 < τ a := by
      by_contra hno
      push Not at hno
      have : ∑ a, τ a ≤ 0 := Finset.sum_nonpos fun a _ => hno a
      linarith [hτ.2]
    have hM := h a₀ ha₀
    refine (mixedPayoff_le_of_pure_le N σ i hτ' i hM).trans (le_of_eq ?_)
    rw [mixedPayoff_update_eq_sum_pure N σ i τ i]
    calc N.mixedPayoff (update σ i (pureMixed a₀)) i
        = ∑ a, τ a * N.mixedPayoff (update σ i (pureMixed a₀)) i := by
          rw [← Finset.sum_mul, hτ.2, one_mul]
      _ = _ := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rcases (hτ.1 a).eq_or_lt with h0 | hpos
          · rw [← h0, zero_mul, zero_mul]
          · rw [le_antisymm (h a hpos a₀) (hM a)]

/-- A pure strategy maximizing the payoff against `σ_{-i}` is a best response. -/
theorem isBestResponse_pureMixed_of_max (N : NormalForm I S) (i : I) (σ : (j : I) → S j → ℝ)
    {a : S i} (ha : ∀ b, N.mixedPayoff (update σ i (pureMixed b)) i ≤
      N.mixedPayoff (update σ i (pureMixed a)) i) :
    IsBestResponse N i (pureMixed a) σ :=
  ⟨isMixedStrategy_pureMixed a, fun _ hτ' => mixedPayoff_le_of_pure_le N σ i hτ' i ha⟩

/-- Every player has a pure best response to any `σ_{-i}` (when `S_i` is nonempty). -/
theorem exists_pure_bestResponse [∀ i, Nonempty (S i)] (N : NormalForm I S) (i : I)
    (σ : (j : I) → S j → ℝ) : ∃ a, IsBestResponse N i (pureMixed a) σ := by
  obtain ⟨a, -, hmax⟩ := Finset.exists_max_image univ
    (fun b => N.mixedPayoff (update σ i (pureMixed b)) i) univ_nonempty
  exact ⟨a, isBestResponse_pureMixed_of_max N i σ fun b => hmax b (mem_univ b)⟩

omit [∀ i, DecidableEq (S i)] in
/-- **Footnote 1** (MWG, p. 243). Suppose player `i` believes that each rival `j` plays the mixed
strategy `τ_j(x)` with probability `π_j(x)`, independently across rivals (player `i`'s own
coordinate of the conjecture is irrelevant). If `τ` is optimal against this probabilistic
conjecture, it is a best response to the compound profile `ρ_j = ∑_x π_j(x) τ_j(x)`, because the
expected payoffs coincide. -/
theorem footnote_8_1 (N : NormalForm I S) (i : I) {K : I → Type*} [∀ j, Fintype (K j)]
    (π : (j : I) → K j → ℝ) (hπ : ∑ x, π i x = 1) (τfam : (j : I) → K j → S j → ℝ)
    (τ : S i → ℝ) :
    ∑ x : (j : I) → K j, (∏ j, π j (x j)) *
        N.mixedPayoff (update (fun j => τfam j (x j)) i τ) i =
      N.mixedPayoff (update (fun j => ∑ y, π j y • τfam j y) i τ) i := by
  have h1 : ∀ x : (j : I) → K j, update (fun j => τfam j (x j)) i τ =
      fun j => update τfam i (fun _ => τ) j (x j) := by
    intro x
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [update_of_ne hj]
  have h2 : update (fun j => ∑ y, π j y • τfam j y) i τ =
      fun j => ∑ y, π j y • update τfam i (fun _ => τ) j y := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp only [update_self]
      rw [← Finset.sum_smul (s := univ) (f := π j) (x := τ), hπ, one_smul]
    · simp [update_of_ne hj]
  simp_rw [h1, h2]
  exact mixedPayoff_compound N π (update τfam i (fun _ => τ)) i

/-- **Definition 8.D.2** (MWG, p. 250). A mixed strategy profile `σ` is a Nash equilibrium of
`Γ_N = [I, {Δ(S_i)}, {u_i(·)}]`: `u_i(σ_i, σ_{-i}) ≥ u_i(σ_i', σ_{-i})` for all `σ_i' ∈ Δ(S_i)`
and every `i`. -/
def IsMixedNash (N : NormalForm I S) (σ : (i : I) → S i → ℝ) : Prop :=
  IsMixedProfile σ ∧ ∀ i τ, IsMixedStrategy τ → N.mixedPayoff (update σ i τ) i ≤ N.mixedPayoff σ i

omit [∀ i, DecidableEq (S i)] in
/-- In a mixed Nash equilibrium every player's strategy is a best response to the others'. -/
theorem isMixedNash_iff_bestResponse (N : NormalForm I S) (σ : (i : I) → S i → ℝ) :
    IsMixedNash N σ ↔ IsMixedProfile σ ∧ ∀ i, IsBestResponse N i (σ i) σ := by
  simp only [IsMixedNash, IsBestResponse, update_eq_self]
  exact ⟨fun h => ⟨h.1, fun i => ⟨h.1 i, h.2 i⟩⟩, fun h => ⟨h.1, fun i => (h.2 i).2⟩⟩

omit [∀ i, DecidableEq (S i)] in
/-- **Definition 8.D.2 = Definition 8.D.1 for the mixed extension** (MWG, p. 250). A mixed
profile is a Nash equilibrium in the sense of Definition 8.D.2 iff it is a Nash equilibrium
(Definition 8.D.1) of Chapter 7's mixed-extension game `Γ_N = [I, {Δ(S_i)}, {u_i(·)}]`. -/
theorem isMixedNash_iff_mixedExtensionGame (N : NormalForm I S) (σ : (i : I) → S i → ℝ)
    (hσ : IsMixedProfile σ) :
    IsMixedNash N σ ↔ IsNashEquilibrium N.mixedExtensionGame (fun i => ⟨σ i, hσ i⟩) := by
  have hval : ∀ i (τ : {τ : S i → ℝ // IsMixedStrategy τ}),
      (fun j => (update (fun j => (⟨σ j, hσ j⟩ : {τ : S j → ℝ // IsMixedStrategy τ})) i τ j).1)
        = update σ i τ.1 := by
    intro i τ
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [update_of_ne hj]
  constructor
  · intro h i τ
    simp only [NormalForm.mixedExtensionGame]
    rw [hval]
    exact h.2 i τ.1 τ.2
  · intro h
    refine ⟨hσ, fun i τ hτ => ?_⟩
    have := h i ⟨τ, hτ⟩
    simp only [NormalForm.mixedExtensionGame] at this
    rwa [hval] at this

/-- **Proposition 8.D.1** (MWG, p. 250). Let `S_i⁺` be the pure strategies that player `i` plays
with positive probability under `σ`. Then `σ` is a Nash equilibrium of
`Γ_N = [I, {Δ(S_i)}, {u_i(·)}]` iff for every `i`:
(i) `u_i(s_i, σ_{-i}) = u_i(s_i', σ_{-i})` for all `s_i, s_i' ∈ S_i⁺`, and
(ii) `u_i(s_i, σ_{-i}) ≥ u_i(s_i', σ_{-i})` for all `s_i ∈ S_i⁺` and `s_i' ∉ S_i⁺`. -/
theorem proposition_8_D_1 (N : NormalForm I S) {σ : (i : I) → S i → ℝ}
    (hσ : IsMixedProfile σ) :
    IsMixedNash N σ ↔ ∀ i,
      (∀ a b, 0 < σ i a → 0 < σ i b → N.mixedPayoff (update σ i (pureMixed a)) i =
        N.mixedPayoff (update σ i (pureMixed b)) i) ∧
      (∀ a b, 0 < σ i a → ¬ 0 < σ i b → N.mixedPayoff (update σ i (pureMixed b)) i ≤
        N.mixedPayoff (update σ i (pureMixed a)) i) := by
  rw [isMixedNash_iff_bestResponse]
  simp only [hσ, true_and]
  refine forall_congr' fun i => ?_
  rw [isBestResponse_iff_support N i (hσ i)]
  constructor
  · intro h
    exact ⟨fun a b ha hb => le_antisymm (h b hb a) (h a ha b), fun a b ha _ => h a ha b⟩
  · rintro ⟨h1, h2⟩ a ha b
    by_cases hb : 0 < σ i b
    · exact (h1 a b ha hb).ge
    · exact h2 a b ha hb

/-- **Section 8.D** (MWG, p. 251). To test whether `σ` is a Nash equilibrium it suffices to
consider pure strategy deviations. -/
theorem isMixedNash_iff_pure_deviations (N : NormalForm I S) {σ : (i : I) → S i → ℝ}
    (hσ : IsMixedProfile σ) :
    IsMixedNash N σ ↔ ∀ i b, N.mixedPayoff (update σ i (pureMixed b)) i ≤ N.mixedPayoff σ i := by
  constructor
  · exact fun h i b => h.2 i _ (isMixedStrategy_pureMixed b)
  · intro h
    exact ⟨hσ, fun i τ hτ => mixedPayoff_le_of_pure_le N σ i hτ i (h i)⟩

/-- **Corollary 8.D.1** (MWG, p. 251). The pure profile `s` is a Nash equilibrium of
`Γ_N = [I, {S_i}, {u_i(·)}]` iff it is a (degenerate) mixed strategy Nash equilibrium of
`Γ_N = [I, {Δ(S_i)}, {u_i(·)}]`. -/
theorem corollary_8_D_1 (N : NormalForm I S) (s : (i : I) → S i) :
    IsNashEquilibrium N s ↔ IsMixedNash N (pureProfile s) := by
  rw [isMixedNash_iff_pure_deviations N (isMixedProfile_pureProfile s)]
  simp only [mixedPayoff_pureProfile_update, mixedPayoff_pureProfile]
  rfl

end MWG.SimultaneousMoveGames
