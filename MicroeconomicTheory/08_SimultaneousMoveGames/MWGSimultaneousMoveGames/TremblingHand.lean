/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGSimultaneousMoveGames.TwoPlayer
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Trembling-hand perfection

MWG, Section 8.F, pp. 258-260, and Exercises 8.F.1 and 8.F.3 (pp. 265-266).

* Perturbed games (p. 258): `IsPerturbation ε` (`ε_i(s_i) ∈ (0, 1)`, `∑_{s_i} ε_i(s_i) < 1`),
  `perturbedSet ε i = Δ_ε(S_i)` and `IsPerturbedNash` (Nash equilibrium of `Γ_ε`).
* **Definition 8.F.1** (`IsTHP`): a Nash equilibrium that is the limit of Nash equilibria of
  a sequence of perturbed games whose trembles go to zero.
* **Proposition 8.F.1** (`proposition_8_F_1`, which is **Exercise 8.F.1**): a Nash equilibrium
  is trembling-hand perfect iff it is a best response to every element of some sequence of
  totally mixed profiles converging to it.
* Weak domination in `[I, {Δ(S_i)}, {u_i(·)}]` (Definition 8.B.3 for the mixed extension,
  `MixedWeaklyDominates`) and its pure test (`mixedWeaklyDominates_iff_pure`).
* **Proposition 8.F.2** (`proposition_8_F_2`, `proposition_8_F_2_pure`): no player's strategy in
  a trembling-hand perfect equilibrium is weakly dominated, and no weakly dominated pure
  strategy is played with positive probability.
* **Exercise 8.F.3** (`exercise_8_F_3`, Selten's theorem): every game with finite (nonempty)
  strategy sets has a trembling-hand perfect equilibrium: every perturbed game has an
  equilibrium (`exists_perturbedNash`, Proposition 8.D.3 on `Δ_ε(S_i)`) and a subsequence of the
  equilibria of the uniformly perturbed games converges to an equilibrium of `Γ_N`. Hence a Nash
  equilibrium in which no weakly dominated strategy is played exists
  (`exists_nash_no_weakly_dominated`, p. 259).
-/

namespace MWG.SimultaneousMoveGames

open MWG.NoncooperativeGames Function Finset Filter Topology

variable {I : Type*} {S : I → Type*} [Fintype I] [DecidableEq I] [∀ i, Fintype (S i)]
  [∀ i, DecidableEq (S i)]

/-- **Section 8.F** (MWG, p. 258). A perturbation: for each player `i` and pure strategy `s_i`
a number `ε_i(s_i) ∈ (0, 1)`, with `∑_{s_i ∈ S_i} ε_i(s_i) < 1`. -/
def IsPerturbation (ε : (i : I) → S i → ℝ) : Prop :=
  (∀ i s, 0 < ε i s ∧ ε i s < 1) ∧ ∀ i, ∑ s, ε i s < 1

/-- **Section 8.F** (MWG, p. 258). The perturbed strategy set
`Δ_ε(S_i) = {σ_i : σ_i(s_i) ≥ ε_i(s_i) for all s_i ∈ S_i and ∑_{s_i} σ_i(s_i) = 1}`. -/
def perturbedSet (ε : (i : I) → S i → ℝ) (i : I) : Set (S i → ℝ) :=
  {τ | (∀ s, ε i s ≤ τ s) ∧ ∑ s, τ s = 1}

/-- A Nash equilibrium of the perturbed game `Γ_ε = [I, {Δ_ε(S_i)}, {u_i(·)}]`. -/
def IsPerturbedNash (N : NormalForm I S) (ε : (i : I) → S i → ℝ) (σ : (i : I) → S i → ℝ) :
    Prop :=
  (∀ i, σ i ∈ perturbedSet ε i) ∧
    ∀ i, ∀ τ ∈ perturbedSet ε i, N.mixedPayoff (update σ i τ) i ≤ N.mixedPayoff σ i

/-- **Definition 8.F.1** (MWG, p. 258). A Nash equilibrium `σ` of `Γ_N = [I, {Δ(S_i)}, {u_i(·)}]`
is (normal form) trembling-hand perfect if there is a sequence of perturbed games `Γ_{εᵏ}` with
`εᵏ_i(s_i) → 0` for all `i` and `s_i`, and Nash equilibria `σᵏ` of `Γ_{εᵏ}` with `σᵏ → σ`. -/
def IsTHP (N : NormalForm I S) (σ : (i : I) → S i → ℝ) : Prop :=
  IsMixedNash N σ ∧ ∃ (ε : ℕ → (i : I) → S i → ℝ) (σs : ℕ → (i : I) → S i → ℝ),
    (∀ k, IsPerturbation (ε k)) ∧ (∀ i s, Tendsto (fun k => ε k i s) atTop (𝓝 0)) ∧
    (∀ k, IsPerturbedNash N (ε k) (σs k)) ∧ Tendsto σs atTop (𝓝 σ)

/-- **Section 8.F** (MWG, p. 259). A totally mixed strategy gives every pure strategy positive
probability. -/
def IsTotallyMixed {T : Type*} [Fintype T] (τ : T → ℝ) : Prop :=
  IsMixedStrategy τ ∧ ∀ s, 0 < τ s

omit [Fintype I] [DecidableEq I] [∀ i, DecidableEq (S i)] in
/-- Perturbed strategies are mixed strategies. -/
theorem isMixedStrategy_of_mem_perturbedSet {ε : (i : I) → S i → ℝ} (hε : IsPerturbation ε)
    {i : I} {τ : S i → ℝ} (hτ : τ ∈ perturbedSet ε i) : IsMixedStrategy τ :=
  ⟨fun s => (hε.1 i s).1.le.trans (hτ.1 s), hτ.2⟩

/-- In a Nash equilibrium of a perturbed game, a pure strategy that is not a best response is
played with its minimal probability `ε_i(s_i)`. -/
theorem perturbedNash_eq_of_not_best {N : NormalForm I S} {ε : (i : I) → S i → ℝ}
    {σ : (i : I) → S i → ℝ} (h : IsPerturbedNash N ε σ) (i : I) {a b : S i}
    (hab : N.mixedPayoff (update σ i (pureMixed a)) i <
      N.mixedPayoff (update σ i (pureMixed b)) i) : σ i a = ε i a := by
  refine le_antisymm ?_ ((h.1 i).1 a)
  by_contra hgt
  push Not at hgt
  have hba : b ≠ a := by rintro rfl; exact lt_irrefl _ hab
  set c := σ i a - ε i a with hc
  have hcpos : 0 < c := by linarith
  have hmem : σ i + c • (pureMixed b - pureMixed a) ∈ perturbedSet ε i := by
    refine ⟨fun t => ?_, ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, pureMixed]
      rcases eq_or_ne t a with rfl | hta
      · simp [hba.symm]; linarith
      · by_cases htb : t = b
        · subst htb; simp [hta]; linarith [(h.1 i).1 t]
        · simp only [hta, htb, ↓reduceIte, sub_self, mul_zero, add_zero]; exact (h.1 i).1 t
    · simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Finset.sum_add_distrib,
        ← Finset.mul_sum, Finset.sum_sub_distrib, (h.1 i).2, (isMixedStrategy_pureMixed b).2,
        (isMixedStrategy_pureMixed a).2, sub_self, mul_zero, add_zero]
  have hle := h.2 i _ hmem
  rw [mixedPayoff_shift] at hle
  rw [update_eq_self] at hle
  nlinarith

omit [∀ i, DecidableEq (S i)] in
/-- A perturbed equilibrium is a profile of totally mixed strategies. -/
theorem isTotallyMixed_of_perturbedNash {N : NormalForm I S} {ε : (i : I) → S i → ℝ}
    (hε : IsPerturbation ε) {σ : (i : I) → S i → ℝ} (h : IsPerturbedNash N ε σ) (i : I) :
    IsTotallyMixed (σ i) :=
  ⟨isMixedStrategy_of_mem_perturbedSet hε (h.1 i),
    fun s => (hε.1 i s).1.trans_le ((h.1 i).1 s)⟩

omit [∀ i, DecidableEq (S i)] in
/-- A mixed strategy gives at most probability one to each pure strategy. -/
theorem mixed_le_one {T : Type*} [Fintype T] {τ : T → ℝ} (h : IsMixedStrategy τ)
    (s : T) : τ s ≤ 1 := by
  rw [← h.2]
  exact Finset.single_le_sum (fun t _ => h.1 t) (mem_univ s)

omit [∀ i, DecidableEq (S i)] in
/-- A mixed strategy plays some pure strategy with positive probability. -/
theorem mixed_exists_pos {T : Type*} [Fintype T] {τ : T → ℝ} (h : IsMixedStrategy τ) :
    ∃ s, 0 < τ s := by
  by_contra hno
  push Not at hno
  have : ∑ s, τ s ≤ 0 := Finset.sum_nonpos fun s _ => hno s
  linarith [h.2]

omit [∀ i, DecidableEq (S i)] in
/-- **Proposition 8.F.1** (MWG, p. 259; **Exercise 8.F.1**, p. 265). A Nash equilibrium `σ` of
`Γ_N = [I, {Δ(S_i)}, {u_i(·)}]` is (normal form) trembling-hand perfect iff there is a sequence
of totally mixed profiles `σᵏ → σ` such that `σ_i` is a best response to every `σᵏ_{-i}`, for all
`i`. -/
theorem proposition_8_F_1 (N : NormalForm I S) {σ : (i : I) → S i → ℝ} (hσ : IsMixedNash N σ) :
    IsTHP N σ ↔ ∃ ρ : ℕ → (i : I) → S i → ℝ, (∀ k i, IsTotallyMixed (ρ k i)) ∧
      Tendsto ρ atTop (𝓝 σ) ∧ ∀ k i, IsBestResponse N i (σ i) (ρ k) := by
  classical
  constructor
  · rintro ⟨-, ε, σs, hε, hε0, hNE, hlim⟩
    -- eventually every strategy played by `σ_i` is played with more than its minimum
    have hev : ∀ᶠ k in atTop, ∀ i a, 0 < σ i a → ε k i a < σs k i a := by
      rw [eventually_all]
      intro i
      rw [eventually_all]
      intro a
      by_cases ha : 0 < σ i a
      · have h1 : Tendsto (fun k => σs k i a - ε k i a) atTop (𝓝 (σ i a - 0)) :=
          (((continuous_apply a).comp (continuous_apply i)).tendsto σ |>.comp hlim).sub (hε0 i a)
        rw [sub_zero] at h1
        filter_upwards [h1.eventually (lt_mem_nhds ha)] with k hk _
        linarith
      · exact Eventually.of_forall fun k h => absurd h ha
    obtain ⟨K, hK⟩ := eventually_atTop.1 hev
    refine ⟨fun k => σs (k + K), fun k i => isTotallyMixed_of_perturbedNash (hε _) (hNE _) i,
      hlim.comp (tendsto_add_atTop_nat K), fun k i => ?_⟩
    rw [isBestResponse_iff_support N i (hσ.1 i)]
    intro a ha b
    by_contra hlt
    push Not at hlt
    have := perturbedNash_eq_of_not_best (hNE (k + K)) i hlt
    have := hK (k + K) (Nat.le_add_left K k) i a ha
    linarith
  · rintro ⟨ρ, hρ, hlim, hbr⟩
    refine ⟨hσ, fun k i s => if 0 < σ i s then min (ρ k i s / 2) (1 / ((k : ℝ) + 2))
      else ρ k i s, ρ, fun k => ?_, fun i s => ?_, fun k => ?_, hlim⟩
    · -- the trembles form a perturbation
      have hρle : ∀ i s, ρ k i s ≤ 1 := fun i s => mixed_le_one (hρ k i).1 s
      have hεle : ∀ i s, (if 0 < σ i s then min (ρ k i s / 2) (1 / ((k : ℝ) + 2))
          else ρ k i s) ≤ ρ k i s := by
        intro i s
        split_ifs
        · exact (min_le_left _ _).trans (by linarith [(hρ k i).2 s])
        · exact le_rfl
      refine ⟨fun i s => ⟨?_, ?_⟩, fun i => ?_⟩
      · dsimp only
        split_ifs
        · exact lt_min (by linarith [(hρ k i).2 s]) (by positivity)
        · exact (hρ k i).2 s
      · dsimp only
        split_ifs with hs
        · exact (min_le_left _ _).trans_lt (by linarith [hρle i s])
        · -- some other strategy has positive probability under `ρᵏ_i`
          obtain ⟨a, ha⟩ := mixed_exists_pos (hσ.1 i)
          have hne : s ≠ a := fun h => hs (h ▸ ha)
          have h1 : ρ k i s + ρ k i a ≤ 1 := by
            rw [← (hρ k i).1.2]
            have := Finset.sum_le_sum_of_subset_of_nonneg (s := {s, a}) (t := univ)
              (f := ρ k i) (subset_univ _) (fun x _ _ => (hρ k i).1.1 x)
            rwa [Finset.sum_pair hne] at this
          linarith [(hρ k i).2 a]
      · obtain ⟨a, ha⟩ := mixed_exists_pos (hσ.1 i)
        have hlt : (if 0 < σ i a then min (ρ k i a / 2) (1 / ((k : ℝ) + 2)) else ρ k i a) <
            ρ k i a := by
          simp only [ha, ↓reduceIte]
          exact (min_le_left _ _).trans_lt (by linarith [(hρ k i).2 a])
        calc ∑ s, (if 0 < σ i s then min (ρ k i s / 2) (1 / ((k : ℝ) + 2)) else ρ k i s)
            < ∑ s, ρ k i s := Finset.sum_lt_sum (fun s _ => hεle i s) ⟨a, mem_univ _, hlt⟩
          _ = 1 := (hρ k i).1.2
    · -- the trembles vanish
      by_cases hs : 0 < σ i s
      · simp only [hs, ↓reduceIte]
        have h1 : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 2)) atTop (𝓝 0) := by
          have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
          refine squeeze_zero (fun k => by positivity) (fun k => ?_) this
          gcongr
          linarith
        refine squeeze_zero (fun k => le_min (by linarith [(hρ k i).2 s]) (by positivity))
          (fun k => min_le_right _ _) h1
      · simp only [hs, ↓reduceIte]
        have h1 : Tendsto (fun k => ρ k i s) atTop (𝓝 (σ i s)) :=
          tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hlim i) s
        rwa [le_antisymm (not_lt.1 hs) ((hσ.1 i).1 s)] at h1
    · -- `ρᵏ` is an equilibrium of the perturbed game
      refine ⟨fun i => ⟨fun s => ?_, (hρ k i).1.2⟩, fun i τ hτ => ?_⟩
      · dsimp only
        split_ifs
        · exact (min_le_left _ _).trans (by linarith [(hρ k i).2 s])
        · exact le_rfl
      · have hsupp := (isBestResponse_iff_support N i (hσ.1 i) (ρ k)).1 (hbr k i)
        obtain ⟨a₀, ha₀⟩ := mixed_exists_pos (hσ.1 i)
        set v : S i → ℝ := fun s => N.mixedPayoff (update (ρ k) i (pureMixed s)) i with hv
        set M := v a₀
        have hvM : ∀ s, v s ≤ M := fun s => hsupp a₀ ha₀ s
        have hvsupp : ∀ s, 0 < σ i s → v s = M := fun s hs => le_antisymm (hvM s) (hsupp s hs a₀)
        conv_rhs => rw [← update_eq_self i (ρ k)]
        rw [mixedPayoff_update_eq_sum_pure N (ρ k) i τ i,
          mixedPayoff_update_eq_sum_pure N (ρ k) i (ρ k i) i]
        have hterm : ∀ s, (τ s - ρ k i s) * v s ≤ (τ s - ρ k i s) * M := by
          intro s
          by_cases hs : 0 < σ i s
          · rw [hvsupp s hs]
          · have : ρ k i s ≤ τ s := by
              have := hτ.1 s
              simp only [hs, ↓reduceIte] at this
              exact this
            exact mul_le_mul_of_nonneg_left (hvM s) (by linarith)
        have hsum := Finset.sum_le_sum fun s (_ : s ∈ univ) => hterm s
        rw [← Finset.sum_mul, Finset.sum_sub_distrib, hτ.2, (hρ k i).1.2, sub_self,
          zero_mul] at hsum
        simp only [sub_mul, Finset.sum_sub_distrib] at hsum
        linarith

/-- **Definition 8.B.3 for `[I, {Δ(S_i)}, {u_i(·)}]`** (MWG, pp. 238 and 259). `τ'` weakly
dominates `τ`: at least as good against every profile of the rivals' mixed strategies and
strictly better against some. -/
def MixedWeaklyDominates (N : NormalForm I S) (i : I) (τ' τ : S i → ℝ) : Prop :=
  (∀ ρ : (j : I) → S j → ℝ, IsMixedProfile ρ →
      N.mixedPayoff (update ρ i τ) i ≤ N.mixedPayoff (update ρ i τ') i) ∧
    ∃ ρ : (j : I) → S j → ℝ, IsMixedProfile ρ ∧
      N.mixedPayoff (update ρ i τ) i < N.mixedPayoff (update ρ i τ') i

/-- The mixed strategy `τ` of player `i` is weakly dominated. -/
def MixedWeaklyDominated (N : NormalForm I S) (i : I) (τ : S i → ℝ) : Prop :=
  ∃ τ', IsMixedStrategy τ' ∧ MixedWeaklyDominates N i τ' τ

/-- Weak domination can be tested against the rivals' pure strategy profiles. -/
theorem mixedWeaklyDominates_iff_pure (N : NormalForm I S) (i : I) (τ' τ : S i → ℝ) :
    MixedWeaklyDominates N i τ' τ ↔
      (∀ s, N.mixedPayoff (update (pureProfile s) i τ) i ≤
        N.mixedPayoff (update (pureProfile s) i τ') i) ∧
      ∃ s, N.mixedPayoff (update (pureProfile s) i τ) i <
        N.mixedPayoff (update (pureProfile s) i τ') i := by
  constructor
  · rintro ⟨hle, ρ, hρ, hlt⟩
    refine ⟨fun s => hle _ (isMixedProfile_pureProfile s), ?_⟩
    by_contra hno
    push Not at hno
    have := mixedPayoff_le_of_pure N hρ i i (τ := τ') (τ' := τ) hno
    linarith
  · rintro ⟨hle, s, hs⟩
    exact ⟨fun ρ hρ => mixedPayoff_le_of_pure N hρ i i hle, _, isMixedProfile_pureProfile s, hs⟩

omit [∀ i, DecidableEq (S i)] in
/-- Against a totally mixed profile, a weakly dominating strategy does strictly better. -/
theorem MixedWeaklyDominates.lt_of_totallyMixed {N : NormalForm I S} {i : I} {τ' τ : S i → ℝ}
    (h : MixedWeaklyDominates N i τ' τ) {ρ : (j : I) → S j → ℝ}
    (hρ : ∀ j, IsTotallyMixed (ρ j)) :
    N.mixedPayoff (update ρ i τ) i < N.mixedPayoff (update ρ i τ') i := by
  classical
  obtain ⟨hle, s₀, hs₀⟩ := (mixedWeaklyDominates_iff_pure N i τ' τ).1 h
  rw [mixedPayoff_update_eq_expect N ρ i (hρ i).1.2, mixedPayoff_update_eq_expect N ρ i (hρ i).1.2]
  have hw : ∀ s : (j : I) → S j, 0 ≤ ∏ j, ρ j (s j) :=
    prod_mixed_nonneg fun j a => (hρ j).1.1 a
  exact Finset.sum_lt_sum (fun s _ => mul_le_mul_of_nonneg_left (hle s) (hw s))
    ⟨s₀, mem_univ _, mul_lt_mul_of_pos_left hs₀ (Finset.prod_pos fun j _ => (hρ j).2 _)⟩

omit [∀ i, DecidableEq (S i)] in
/-- **Proposition 8.F.2** (MWG, p. 259). In a (normal form) trembling-hand perfect Nash
equilibrium `σ`, no `σ_i` is a weakly dominated strategy. -/
theorem proposition_8_F_2 (N : NormalForm I S) {σ : (i : I) → S i → ℝ} (h : IsTHP N σ)
    (i : I) : ¬ MixedWeaklyDominated N i (σ i) := by
  classical
  obtain ⟨ρ, hρ, -, hbr⟩ := (proposition_8_F_1 N h.1).1 h
  rintro ⟨τ', hτ', hdom⟩
  have := hdom.lt_of_totallyMixed (hρ 0)
  linarith [(hbr 0 i).2 τ' hτ']

/-- If the pure strategy `a` is weakly dominated, so is every mixed strategy that plays it with
positive probability. -/
theorem mixedWeaklyDominated_of_pure (N : NormalForm I S) (i : I) {a : S i}
    (ha : MixedWeaklyDominated N i (pureMixed a)) {τ : S i → ℝ} (hτ : IsMixedStrategy τ)
    (hpos : 0 < τ a) : MixedWeaklyDominated N i τ := by
  obtain ⟨τ', hτ', hle, ρ₀, hρ₀, hlt⟩ := ha
  refine ⟨τ + τ a • (τ' - pureMixed a), isMixedStrategy_shift hτ hτ' hpos.le le_rfl,
    fun ρ hρ => ?_, ρ₀, hρ₀, ?_⟩
  · rw [mixedPayoff_shift]
    nlinarith [hle ρ hρ]
  · rw [mixedPayoff_shift]
    nlinarith

/-- **Proposition 8.F.2** (MWG, p. 259), second statement. In a trembling-hand perfect Nash
equilibrium no weakly dominated pure strategy is played with positive probability. -/
theorem proposition_8_F_2_pure (N : NormalForm I S) {σ : (i : I) → S i → ℝ} (h : IsTHP N σ)
    (i : I) (a : S i) (ha : MixedWeaklyDominated N i (pureMixed a)) : σ i a = 0 := by
  by_contra hne
  have hpos : 0 < σ i a := lt_of_le_of_ne ((h.1.1 i).1 a) (Ne.symm hne)
  exact proposition_8_F_2 N h i (mixedWeaklyDominated_of_pure N i ha (h.1.1 i) hpos)

/-! ### Existence (Exercise 8.F.3) -/

omit [Fintype I] [DecidableEq I] [∀ i, DecidableEq (S i)] in
/-- `Δ_ε(S_i)` is convex. -/
theorem convex_perturbedSet (ε : (i : I) → S i → ℝ) (i : I) : Convex ℝ (perturbedSet ε i) := by
  intro x hx y hy p q hp hq hpq
  refine ⟨fun t => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have h1 := mul_le_mul_of_nonneg_left (hx.1 t) hp
    have h2 := mul_le_mul_of_nonneg_left (hy.1 t) hq
    have h3 : ε i t = p * ε i t + q * ε i t := by rw [← add_mul, hpq, one_mul]
    linarith
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hx.2, hy.2, mul_one, hpq]

omit [Fintype I] [DecidableEq I] [∀ i, DecidableEq (S i)] in
/-- `Δ_ε(S_i)` is compact. -/
theorem isCompact_perturbedSet {ε : (i : I) → S i → ℝ} (hε : IsPerturbation ε) (i : I) :
    IsCompact (perturbedSet ε i) := by
  refine (isCompact_mixedExtension (S i)).of_isClosed_subset ?_
    fun τ hτ => isMixedStrategy_of_mem_perturbedSet hε hτ
  have h1 : IsClosed {τ : S i → ℝ | ∀ s, ε i s ≤ τ s} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun s => isClosed_le continuous_const (continuous_apply s)
  have h2 : IsClosed {τ : S i → ℝ | ∑ s, τ s = 1} :=
    isClosed_eq (continuous_finsetSum _ fun s _ => continuous_apply s) continuous_const
  exact h1.inter h2

omit [Fintype I] [DecidableEq I] [∀ i, DecidableEq (S i)] in
/-- `Δ_ε(S_i)` is nonempty: spread the slack `1 - ∑ ε_i` uniformly. -/
theorem perturbedSet_nonempty [∀ i, Nonempty (S i)] {ε : (i : I) → S i → ℝ}
    (hε : IsPerturbation ε) (i : I) : (perturbedSet ε i).Nonempty := by
  refine ⟨fun s => ε i s + (1 - ∑ t, ε i t) * uniformMixed (S i) s, fun s => ?_, ?_⟩
  · have := hε.2 i
    have := uniformMixed_pos (S i) s
    nlinarith
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum, (isMixedStrategy_uniformMixed (S i)).2]
    ring

omit [∀ i, DecidableEq (S i)] in
/-- **Exercise 8.F.3**, first step (MWG, p. 266). Every perturbed game has a Nash equilibrium. -/
theorem exists_perturbedNash [∀ i, Nonempty (S i)] (N : NormalForm I S)
    {ε : (i : I) → S i → ℝ} (hε : IsPerturbation ε) : ∃ σ, IsPerturbedNash N ε σ := by
  obtain ⟨σ, hσ, hne⟩ := nash_exists_of_quasiconcave (E := fun i => S i → ℝ)
    (u := fun i σ => N.mixedPayoff σ i) (S := perturbedSet ε)
    (fun i => perturbedSet_nonempty hε i) (fun i => isCompact_perturbedSet hε i)
    (fun i => convex_perturbedSet ε i) (fun i => (continuous_mixedPayoff N i).continuousOn)
    (fun i σ _ => (concaveOn_mixedPayoff_update N σ i (convex_perturbedSet ε i)).quasiconcaveOn)
  exact ⟨σ, fun i => hσ i (Set.mem_univ i), hne⟩

omit [∀ i, DecidableEq (S i)] in
/-- Payoffs are jointly continuous in the profile and the replacing strategy. -/
theorem tendsto_mixedPayoff_update (N : NormalForm I S) (i : I) {σs : ℕ → (j : I) → S j → ℝ}
    {τs : ℕ → S i → ℝ} {σ : (j : I) → S j → ℝ} {τ : S i → ℝ} (h1 : Tendsto σs atTop (𝓝 σ))
    (h2 : Tendsto τs atTop (𝓝 τ)) :
    Tendsto (fun n => N.mixedPayoff (update (σs n) i (τs n)) i) atTop
      (𝓝 (N.mixedPayoff (update σ i τ) i)) := by
  have hupd : Continuous fun p : ((j : I) → S j → ℝ) × (S i → ℝ) => update p.1 i p.2 :=
    continuous_fst.update i continuous_snd
  have hc : Continuous fun p : ((j : I) → S j → ℝ) × (S i → ℝ) =>
      N.mixedPayoff (update p.1 i p.2) i := (continuous_mixedPayoff N i).comp hupd
  have h3 : Tendsto (fun n => (σs n, τs n)) atTop (𝓝 (σ, τ)) := h1.prodMk_nhds h2
  have h4 := (hc.tendsto (σ, τ)).comp h3
  exact h4

/-- The uniform trembles `εⁿ_i(s_i) = 1 / ((n + 2) |S_i|)`. -/
noncomputable def uniformTremble (S : I → Type*) [∀ i, Fintype (S i)] (n : ℕ) :
    (i : I) → S i → ℝ :=
  fun i _ => 1 / (((n : ℝ) + 2) * Fintype.card (S i))

omit [Fintype I] [DecidableEq I] [∀ i, DecidableEq (S i)] in
theorem isPerturbation_uniformTremble [∀ i, Nonempty (S i)] (n : ℕ) :
    IsPerturbation (uniformTremble S n) := by
  have hc : ∀ i, (1 : ℝ) ≤ Fintype.card (S i) := fun i => by
    exact_mod_cast Fintype.card_pos
  refine ⟨fun i s => ⟨by unfold uniformTremble; have := hc i; positivity, ?_⟩, fun i => ?_⟩
  · unfold uniformTremble
    rw [div_lt_one (by have := hc i; positivity)]
    nlinarith [hc i]
  · simp only [uniformTremble, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have := hc i
    rw [mul_one_div, div_lt_one (by positivity)]
    nlinarith

omit [Fintype I] [DecidableEq I] [∀ i, DecidableEq (S i)] in
theorem tendsto_uniformTremble [∀ i, Nonempty (S i)] (i : I) (s : S i) :
    Tendsto (fun n => uniformTremble S n i s) atTop (𝓝 0) := by
  have hc : (1 : ℝ) ≤ Fintype.card (S i) := by exact_mod_cast Fintype.card_pos
  refine squeeze_zero (fun n => by unfold uniformTremble; positivity) (fun n => ?_)
    tendsto_one_div_add_atTop_nhds_zero_nat
  unfold uniformTremble
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

omit [∀ i, DecidableEq (S i)] in
/-- **Exercise 8.F.3** (MWG, p. 266; Selten 1975, p. 259). Every game
`Γ_N = [I, {Δ(S_i)}, {u_i(·)}]` in which the `S_i` are finite (nonempty) sets has a (normal form)
trembling-hand perfect Nash equilibrium. -/
theorem exercise_8_F_3 [∀ i, Nonempty (S i)] (N : NormalForm I S) : ∃ σ, IsTHP N σ := by
  choose σs hσs using fun n => exists_perturbedNash N (isPerturbation_uniformTremble (S := S) n)
  set K : Set ((i : I) → S i → ℝ) := Set.pi Set.univ fun i => mixedExtension (S i)
  have hK : IsCompact K := isCompact_univ_pi fun i => isCompact_mixedExtension (S i)
  have hmem : ∀ n, σs n ∈ K := fun n i _ =>
    isMixedStrategy_of_mem_perturbedSet (isPerturbation_uniformTremble n) ((hσs n).1 i)
  obtain ⟨σ, hσK, φ, hφ, hlim⟩ := hK.tendsto_subseq hmem
  have hσ : IsMixedProfile σ := fun i => hσK i (Set.mem_univ i)
  have hφtop : Tendsto φ atTop atTop := hφ.tendsto_atTop
  -- the limit is a Nash equilibrium of `Γ_N`
  have hNE : IsMixedNash N σ := by
    refine ⟨hσ, fun i τ hτ => ?_⟩
    -- approximate `τ` by perturbed strategies
    set c : ℕ → ℝ := fun n => 1 / ((φ n : ℝ) + 2) with hcdef
    set τs : ℕ → S i → ℝ := fun n => (1 - c n) • τ + uniformTremble S (φ n) i with hτs
    have hc0 : Tendsto c atTop (𝓝 0) :=
      squeeze_zero (fun n => by positivity) (fun n => by
        change 1 / ((φ n : ℝ) + 2) ≤ 1 / ((φ n : ℝ) + 1)
        gcongr
        linarith) ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hφtop)
    have hτlim : Tendsto τs atTop (𝓝 τ) := by
      have h1 : Tendsto (fun n => (1 - c n) • τ) atTop (𝓝 ((1 - 0 : ℝ) • τ)) :=
        (tendsto_const_nhds.sub hc0).smul_const τ
      have h2 : Tendsto (fun n => uniformTremble S (φ n) i) atTop (𝓝 0) :=
        tendsto_pi_nhds.2 fun s => (tendsto_uniformTremble i s).comp hφtop
      simpa using h1.add h2
    have hτmem : ∀ n, τs n ∈ perturbedSet (uniformTremble S (φ n)) i := by
      intro n
      have hc1 : c n ≤ 1 := by
        simp only [hcdef]
        rw [div_le_one (by positivity)]
        linarith [(φ n).cast_nonneg (α := ℝ)]
      refine ⟨fun s => ?_, ?_⟩
      · simp only [hτs, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        nlinarith [hτ.1 s]
      · simp only [hτs, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
          ← Finset.mul_sum, hτ.2, mul_one, uniformTremble, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul, hcdef]
        have : (Fintype.card (S i) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
        field_simp
        ring
    have hineq : ∀ n, N.mixedPayoff (update (σs (φ n)) i (τs n)) i ≤
        N.mixedPayoff (σs (φ n)) i := fun n => (hσs (φ n)).2 i _ (hτmem n)
    have hl1 := tendsto_mixedPayoff_update N i hlim hτlim
    have hl2 : Tendsto (fun n => N.mixedPayoff ((σs ∘ φ) n) i) atTop
        (𝓝 (N.mixedPayoff σ i)) := ((continuous_mixedPayoff N i).tendsto σ).comp hlim
    exact le_of_tendsto_of_tendsto' hl1 hl2 hineq
  refine ⟨σ, hNE, fun n => uniformTremble S (φ n), fun n => σs (φ n),
    fun n => isPerturbation_uniformTremble _, fun i s => (tendsto_uniformTremble i s).comp hφtop,
    fun n => hσs (φ n), hlim⟩

/-- **Section 8.F** (MWG, pp. 259-260). Every finite game has a Nash equilibrium in which no player
plays a weakly dominated strategy, and no weakly dominated pure strategy is played with positive
probability. -/
theorem exists_nash_no_weakly_dominated [∀ i, Nonempty (S i)] (N : NormalForm I S) :
    ∃ σ, IsMixedNash N σ ∧ (∀ i, ¬ MixedWeaklyDominated N i (σ i)) ∧
      ∀ i a, MixedWeaklyDominated N i (pureMixed a) → σ i a = 0 := by
  obtain ⟨σ, hσ⟩ := exercise_8_F_3 N
  exact ⟨σ, hσ.1, proposition_8_F_2 N hσ, proposition_8_F_2_pure N hσ⟩

end MWG.SimultaneousMoveGames
