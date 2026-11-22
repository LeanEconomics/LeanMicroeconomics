/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGMarketPower.RepeatedBertrand
import MWGMarketPower.BertrandCosts

/-!
# The finitely repeated Bertrand game

MWG, Section 12.D, p. 401.

The `T`-period repetition of a stage game `g` is Chapter 9's multi-stage game with observed
actions (`OSHist`, `OSProfile`): a pure strategy maps histories to actions. Player `i`'s payoff
over the `k` periods following the history `h` is `fhValue g δ σ k h i`, the discounted sum
`∑_{n<k} δⁿ g_i(q_n)` defined by the one-step recursion. A history `h` with `|h| ≤ T` starts a
subgame of `T − |h|` periods; `IsFiniteRepeatedSPNE` is subgame perfection: at every such
history no player gains by any change of strategy.

* `finite_repeated_unique_spne`: if the stage game has a unique pure Nash equilibrium `q*`, then
  in every SPNE `q*` is played after every history of length `< T` (any discount factor `δ`,
  backward induction); `finite_repeated_spne_iff`: for `δ ≥ 0` these are exactly the SPNE.
* `bertrandStage_nash_iff`: the unique Nash equilibrium of the Bertrand duopoly with prices
  `p ≥ 0` is `p₁ = p₂ = c` (from `proposition_12_C_1`).
* `finite_repeated_bertrand` (MWG, p. 401): the unique SPNE of the `T`-period Bertrand duopoly
  has both firms charging `c` in every period after every history, with zero profits;
  `finite_repeated_bertrand_instance`: linear demand.

The discount factor is arbitrary in the uniqueness part; existence (that charging `c` always is
an SPNE) uses `δ ≥ 0`. Stage-game Nash equilibrium is the pure-strategy notion of
`IsStageNash` (Appendix A); strategies are pure, as in Section 12.D.
-/

namespace MWG.MarketPower

open MWG.DynamicGames MWG.NoncooperativeGames MWG.SimultaneousMoveGames Function Set

variable {I : Type*} [DecidableEq I] {A : I → Type*}

/-- Player `i`'s discounted payoff `∑_{n<k} δⁿ g_i(q_n)` over the `k` periods following the
history `h` when the profile `σ` is played. -/
noncomputable def fhValue (g : I → ((i : I) → A i) → ℝ) (δ : ℝ) (σ : OSProfile A) :
    ℕ → OSHist A → I → ℝ
  | 0, _, _ => 0
  | k + 1, h, i => g i (osPlay σ h) + δ * fhValue g δ σ k (osPlay σ h :: h) i

/-- **Subgame perfection in the `T`-period repeated game** (MWG, pp. 275 and 401). At every
history `h` with `|h| ≤ T` (the start of a subgame of `T − |h|` periods), no player `i` gains by
switching to any other strategy `τ`. -/
def IsFiniteRepeatedSPNE (g : I → ((i : I) → A i) → ℝ) (δ : ℝ) (T : ℕ) (σ : OSProfile A) :
    Prop :=
  ∀ h : OSHist A, h.length ≤ T → ∀ i (τ : OSHist A → A i),
    fhValue g δ (update σ i τ) (T - h.length) h i ≤ fhValue g δ σ (T - h.length) h i

/-- The payoff `∑_{n<k} δⁿ g_i(q*)` of playing `q*` for `k` periods. -/
noncomputable def finiteNashValue (g : I → ((i : I) → A i) → ℝ) (δ : ℝ)
    (qs : (i : I) → A i) : ℕ → I → ℝ
  | 0, _ => 0
  | k + 1, i => g i qs + δ * finiteNashValue g δ qs k i

omit [DecidableEq I] in
/-- The `k`-period payoff from `h` depends only on play at histories at least as long as `h`. -/
theorem fhValue_congr {g : I → ((i : I) → A i) → ℝ} {δ : ℝ} {σ σ' : OSProfile A} {L : ℕ}
    (hag : ∀ h : OSHist A, L ≤ h.length → osPlay σ' h = osPlay σ h) (k : ℕ) :
    ∀ h : OSHist A, L ≤ h.length → ∀ i, fhValue g δ σ' k h i = fhValue g δ σ k h i := by
  induction k with
  | zero => intro h _ i; rfl
  | succ k ih =>
    intro h hh i
    simp only [fhValue, hag h hh]
    rw [ih _ (by simp only [List.length_cons]; omega)]

/-- **Backward induction, one step.** If `σ` is subgame perfect and the payoff over the last `k`
periods is `∑_{n<k} δⁿ g_i(q*)` after every history of length `T − k`, then after every history
of length `T − k − 1` the profile played is a stage Nash equilibrium. -/
theorem finite_repeated_step {g : I → ((i : I) → A i) → ℝ} {δ : ℝ} {T : ℕ} {σ : OSProfile A}
    {qs : (i : I) → A i} (hspne : IsFiniteRepeatedSPNE g δ T σ) {k : ℕ}
    (ih : ∀ h : OSHist A, h.length + k = T → ∀ i, fhValue g δ σ k h i = finiteNashValue g δ qs k i)
    {h : OSHist A} (hh : h.length + (k + 1) = T) : IsStageNash g (osPlay σ h) := by
  intro i a
  set τ : OSHist A → A i := fun h' => if h'.length = h.length then a else σ i h' with hτ
  have hsp := hspne h (by omega) i τ
  rw [show T - h.length = k + 1 by omega] at hsp
  simp only [fhValue] at hsp
  rw [osPlay_update σ i τ h, show τ h = a by simp [hτ]] at hsp
  have hcong : fhValue g δ (update σ i τ) k (update (osPlay σ h) i a :: h) i =
      fhValue g δ σ k (update (osPlay σ h) i a :: h) i := by
    refine fhValue_congr (L := h.length + 1) (fun h' hh' => ?_) k _ (by simp) i
    rw [osPlay_update]
    have hne : h'.length ≠ h.length := by omega
    have : τ h' = σ i h' := by simp [hτ, hne]
    rw [this]
    funext j
    by_cases hj : j = i
    · subst hj; simp [osPlay]
    · simp [update_of_ne hj]
  rw [hcong, ih _ (by simp only [List.length_cons]; omega),
    ih _ (by simp only [List.length_cons]; omega)] at hsp
  linarith

/-- **Unique SPNE of a finitely repeated game** (MWG, p. 401; Proposition 9.B.4 for pure
strategies). If the stage game has the unique pure Nash equilibrium `q*`, then for every
discount factor `δ`, every SPNE of the `T`-period repetition plays `q*` after every history of
length `< T`, and gives every player `∑_{n<T−|h|} δⁿ g_i(q*)` from every history `h`. -/
theorem finite_repeated_unique_spne {g : I → ((i : I) → A i) → ℝ} {δ : ℝ} {T : ℕ}
    {qs : (i : I) → A i} (huniq : ∀ q, IsStageNash g q → q = qs) {σ : OSProfile A}
    (hspne : IsFiniteRepeatedSPNE g δ T σ) :
    (∀ h : OSHist A, h.length < T → osPlay σ h = qs) ∧
      ∀ h : OSHist A, h.length ≤ T → ∀ i,
        fhValue g δ σ (T - h.length) h i = finiteNashValue g δ qs (T - h.length) i := by
  have hP : ∀ k, ∀ h : OSHist A, h.length + k = T → ∀ i,
      fhValue g δ σ k h i = finiteNashValue g δ qs k i := by
    intro k
    induction k with
    | zero => intro h _ i; rfl
    | succ k ih =>
      intro h hh i
      have hplay := huniq _ (finite_repeated_step hspne ih hh)
      simp only [fhValue, finiteNashValue, hplay]
      rw [ih _ (by simp only [List.length_cons]; omega)]
  refine ⟨fun h hh => huniq _ (finite_repeated_step (k := T - h.length - 1) hspne
    (hP _) (by omega)), fun h hh i => hP _ h (by omega) i⟩

/-- **The finitely repeated game: characterization** (MWG, p. 401). With a unique pure stage
Nash equilibrium `q*` and `δ ≥ 0`, a profile is an SPNE of the `T`-period repetition iff it plays
`q*` after every history of length `< T`. -/
theorem finite_repeated_spne_iff {g : I → ((i : I) → A i) → ℝ} {δ : ℝ} (hδ : 0 ≤ δ) {T : ℕ}
    {qs : (i : I) → A i} (hqs : IsStageNash g qs) (huniq : ∀ q, IsStageNash g q → q = qs)
    (σ : OSProfile A) :
    IsFiniteRepeatedSPNE g δ T σ ↔ ∀ h : OSHist A, h.length < T → osPlay σ h = qs := by
  refine ⟨fun h => (finite_repeated_unique_spne huniq h).1, fun hplay => ?_⟩
  have hQ : ∀ k, ∀ h : OSHist A, h.length + k = T → ∀ i (τ : OSHist A → A i),
      fhValue g δ (update σ i τ) k h i ≤ finiteNashValue g δ qs k i ∧
        fhValue g δ σ k h i = finiteNashValue g δ qs k i := by
    intro k
    induction k with
    | zero => intro h _ i τ; exact ⟨le_rfl, rfl⟩
    | succ k ih =>
      intro h hh i τ
      have hp := hplay h (by omega)
      have hlen : (osPlay (update σ i τ) h :: h).length + k = T := by
        simp only [List.length_cons]; omega
      have hlen' : (osPlay σ h :: h).length + k = T := by simp only [List.length_cons]; omega
      constructor
      · simp only [fhValue, finiteNashValue]
        have h1 := (ih _ hlen i τ).1
        rw [osPlay_update σ i τ h, hp] at h1 ⊢
        have h2 := hqs i (τ h)
        nlinarith [mul_le_mul_of_nonneg_left h1 hδ]
      · simp only [fhValue, finiteNashValue]
        rw [(ih _ hlen' i τ).2, hp]
  intro h hh i τ
  have := hQ (T - h.length) h (by omega) i τ
  rw [this.2]
  exact this.1

/-! ### The Bertrand duopoly -/

/-- **The stage game has a unique Nash equilibrium** (Proposition 12.C.1, prices `p ≥ 0`). In the
Bertrand duopoly with `c > 0` and `x(c) > 0`, the unique pure Nash equilibrium is
`p₁ = p₂ = c`. -/
theorem bertrandStage_nash_iff {x : ℝ → ℝ} {pbar : ℝ} (hx : IsBertrandDemand x pbar)
    (cc : Ici (0 : ℝ)) (hc : 0 < (cc : ℝ)) (hxc : 0 < x cc) (q : Fin 2 → Ici (0 : ℝ)) :
    IsStageNash (bertrandStage x cc) q ↔ q = constPrice (Fin 2) cc := by
  constructor
  · intro hq
    have hval : ∀ (j : Fin 2) (a : Ici (0 : ℝ)),
        (fun k => ((update q j a k : Ici (0 : ℝ)) : ℝ)) = update (fun k => (q k : ℝ)) j a := by
      intro j a
      funext k
      by_cases hk : k = j
      · subst hk; simp
      · simp [update_of_ne hk]
    have hne : IsNashEquilibrium (bertrandGame (Fin 2) x cc) (fun k => (q k : ℝ)) := by
      intro j t
      change bertrandProfit x cc (update (fun k => (q k : ℝ)) j t) j ≤
        bertrandProfit x cc (fun k => (q k : ℝ)) j
      have h0 : 0 ≤ bertrandProfit x cc (fun k => (q k : ℝ)) j := by
        have := hq j cc
        unfold bertrandStage at this
        rw [hval] at this
        refine le_trans ?_ this
        unfold bertrandProfit
        simp
      rcases le_or_gt 0 t with ht | ht
      · have := hq j ⟨t, ht⟩
        unfold bertrandStage at this
        rw [hval] at this
        exact this
      · exact le_trans (bertrandProfit_le_zero (ι := Fin 2) hx.nonneg
          (by rw [update_self]; linarith [cc.2])) h0
    have := (proposition_12_C_1 hx hc hxc).2 _ hne
    funext k
    exact Subtype.ext (congrFun this k)
  · rintro rfl
    exact bertrandStage_nash hx cc (by simp)

/-- **The finitely repeated Bertrand duopoly** (MWG, p. 401). Let demand satisfy the Bertrand
assumptions, `c > 0` and `x(c) > 0`. For any discount factor `δ` and horizon `T`, every SPNE of
the `T`-period repeated Bertrand duopoly has both firms charging `c` after every history of
length `< T`, and gives both firms zero profit from every history; for `δ ≥ 0`, the profile that
charges `c` after every history is an SPNE (so it is the unique SPNE). -/
theorem finite_repeated_bertrand {x : ℝ → ℝ} {pbar δ : ℝ} (hx : IsBertrandDemand x pbar)
    (cc : Ici (0 : ℝ)) (hc : 0 < (cc : ℝ)) (hxc : 0 < x cc) (T : ℕ)
    (σ : OSProfile fun _ : Fin 2 => Ici (0 : ℝ)) :
    (IsFiniteRepeatedSPNE (bertrandStage (ι := Fin 2) x cc) δ T σ →
      (∀ h : OSHist (fun _ : Fin 2 => Ici (0 : ℝ)), h.length < T →
        osPlay σ h = constPrice (Fin 2) cc) ∧
      ∀ h : OSHist (fun _ : Fin 2 => Ici (0 : ℝ)), h.length ≤ T → ∀ j,
        fhValue (bertrandStage (ι := Fin 2) x cc) δ σ (T - h.length) h j = 0) ∧
    (0 ≤ δ → IsFiniteRepeatedSPNE (bertrandStage (ι := Fin 2) x cc) δ T
      (fun _ _ => cc : OSProfile fun _ : Fin 2 => Ici (0 : ℝ))) := by
  have huniq : ∀ q, IsStageNash (bertrandStage (ι := Fin 2) x cc) q → q = constPrice (Fin 2) cc :=
    fun q hq => (bertrandStage_nash_iff hx cc hc hxc q).1 hq
  have hqs : IsStageNash (bertrandStage (ι := Fin 2) x cc) (constPrice (Fin 2) cc) :=
    (bertrandStage_nash_iff hx cc hc hxc _).2 rfl
  have hzero : ∀ k j,
      finiteNashValue (bertrandStage (ι := Fin 2) x cc) δ (constPrice (Fin 2) cc) k j = 0 := by
    intro k j
    induction k with
    | zero => rfl
    | succ k ih =>
      simp only [finiteNashValue, ih, mul_zero, add_zero]
      simp [bertrandStage, bertrandProfit, constPrice]
  refine ⟨fun hs => ⟨(finite_repeated_unique_spne huniq hs).1, fun h hh j => ?_⟩, fun hδ => ?_⟩
  · rw [(finite_repeated_unique_spne huniq hs).2 h hh j, hzero]
  · exact (finite_repeated_spne_iff hδ hqs huniq _).2 fun _ _ => rfl

/-- The hypotheses of `finite_repeated_bertrand` hold for `x(p) = max{0, 10 − p}` and `c = 1`:
for every `T` and `δ ≥ 0` the unique SPNE charges `1` in every period. -/
theorem finite_repeated_bertrand_instance (T : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    IsFiniteRepeatedSPNE (bertrandStage (ι := Fin 2) (bcLinDemand 10) cexC1) δ T
      (fun _ _ => cexC1) ∧
    ∀ σ : OSProfile fun _ : Fin 2 => Ici (0 : ℝ),
      IsFiniteRepeatedSPNE (bertrandStage (ι := Fin 2) (bcLinDemand 10) cexC1) δ T σ →
      ∀ h : OSHist (fun _ : Fin 2 => Ici (0 : ℝ)), h.length < T →
        osPlay σ h = constPrice (Fin 2) cexC1 := by
  have hxc : 0 < bcLinDemand 10 (cexC1 : ℝ) := by
    simp only [bcLinDemand, cexC1]; norm_num
  have hc : 0 < (cexC1 : ℝ) := by simp only [cexC1]; norm_num
  refine ⟨(finite_repeated_bertrand (bcLinDemand_isBertrand 10) _ hc hxc T
    (fun _ _ => cexC1)).2 hδ, fun σ hs => ?_⟩
  exact ((finite_repeated_bertrand (bcLinDemand_isBertrand 10) _ hc hxc T σ).1 hs).1

end MWG.MarketPower
