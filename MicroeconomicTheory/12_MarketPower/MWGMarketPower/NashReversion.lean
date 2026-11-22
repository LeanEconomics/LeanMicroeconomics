/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGMarketPower.RepeatedGames

/-!
# Nash reversion: Propositions 12.AA.2-12.AA.3, Exercise 12.AA.1, minimax payoffs

MWG, Appendix A of Chapter 12, pp. 419-421.

* `counterexample_12_AA`: a stage game with the unique Nash equilibrium `q* = (D, L)` and the
  stationary path `q = (U, R)`, where player 1 gets `1 < 2 = π₁(q*)`. Its Nash reversion profile
  is an SPNE at `δ = 1/2`, although (12.AA.1) fails there (so Lemma 12.AA.1's "only if" is false),
  and it is not an SPNE at `δ' = 3/5 > 1/2` (so Proposition 12.AA.2 is false), and it is a
  stationary SPNE path giving player 1 less than `π₁(q*)` (so Exercise 12.AA.1 is false).
* `proposition_12_AA_2_corrected`: if (12.AA.1) holds at `δ > 0`, it holds at every
  `δ' ∈ [δ, 1)`, so `Q` is then sustained at `δ'` too.
* `proposition_12_AA_3`: Friedman's Nash reversion folk theorem.
* `exercise_12_AA_1_corrected`, `exercise_12_AA_1_printed_condition`.
* `minimax_le_nash`, `minimax_le_spne_value`.
-/

namespace MWG.MarketPower

open MWG.DynamicGames Function Filter Topology

/-! ### The counterexample -/

/-- Player 1's stage payoffs (`true` = U, L; `false` = D, R): `(U,L) ↦ 0`, `(U,R) ↦ 1`,
`(D,L) ↦ 2`, `(D,R) ↦ 0`. -/
def cexG0 : Bool → Bool → ℝ
  | true, true => 0
  | true, false => 1
  | false, true => 2
  | false, false => 0

/-- Player 2's stage payoffs: `(U,L) ↦ 4`, `(U,R) ↦ 3`, `(D,L) ↦ 1`, `(D,R) ↦ 0`. -/
def cexG1 : Bool → Bool → ℝ
  | true, true => 4
  | true, false => 3
  | false, true => 1
  | false, false => 0

/-- The stage game of the counterexample. -/
def cexG (i : Fin 2) (x : Fin 2 → Bool) : ℝ :=
  if i = 0 then cexG0 (x 0) (x 1) else cexG1 (x 0) (x 1)

theorem cexG_bound : ∀ i x, |cexG i x| ≤ 4 := by
  intro i x
  unfold cexG
  split_ifs <;> cases x 0 <;> cases x 1 <;> norm_num [cexG0, cexG1]

/-- The stage game has the unique pure Nash equilibrium `q* = (D, L)`. -/
theorem cexG_unique_nash :
    IsStageNash cexG ![false, true] ∧ ∀ x, IsStageNash cexG x → x = ![false, true] := by
  constructor
  · intro i a
    fin_cases i <;> cases a <;> simp [cexG, cexG0, cexG1, update]
  · intro x hx
    have e0 : ∀ b, update x 0 b 0 = b := fun b => update_self _ _ _
    have e1 : ∀ b, update x 0 b 1 = x 1 := fun b => update_of_ne (by decide) _ _
    have f0 : ∀ b, update x 1 b 0 = x 0 := fun b => update_of_ne (by decide) _ _
    have f1 : ∀ b, update x 1 b 1 = b := fun b => update_self _ _ _
    have h0 : cexG0 false (x 1) ≤ cexG0 (x 0) (x 1) := by
      simpa [cexG, e0, e1] using hx 0 false
    have h1 : cexG1 (x 0) true ≤ cexG1 (x 0) (x 1) := by simpa [cexG, f0, f1] using hx 1 true
    funext k
    fin_cases k <;> cases hx0 : x 0 <;> cases hx1 : x 1 <;> simp_all [cexG0, cexG1] <;>
      norm_num at *

/-- **Lemma 12.AA.1, Proposition 12.AA.2 and Exercise 12.AA.1 are false as printed**
(MWG, pp. 418-420; corrections). In the game `cexG` with the unique stage Nash equilibrium
`q* = (D, L)` and payoffs `π(q*) = (2, 1)`, take the stationary path `q = (U, R)` with
`π(q) = (1, 3)`.
1. At `δ = 1/2` its Nash reversion profile is an SPNE, but condition (12.AA.1) fails for player 1
   (U is player 1's best response to R, so `π̂₁(R) = π₁(q)`): Lemma 12.AA.1's "only if" fails.
2. At `δ' = 3/5 > 1/2` the same profile is not an SPNE: Proposition 12.AA.2 fails.
3. Player 1 gets `π₁(q) = 1 < 2 = π₁(q*)` on this stationary SPNE path: Exercise 12.AA.1 fails. -/
theorem counterexample_12_AA :
    IsRepeatedSPNE cexG (1 / 2) (nashReversion (fun _ => ![true, false]) ![false, true]) ∧
    ¬ (bestReplyValue cexG 0 ![true, false] + (1 / 2) / (1 - 1 / 2) * cexG 0 ![false, true] ≤
      pathValue cexG (1 / 2) (fun _ => ![true, false]) 0 0) ∧
    ¬ IsRepeatedSPNE cexG (3 / 5) (nashReversion (fun _ => ![true, false]) ![false, true]) ∧
    cexG 0 ![true, false] < cexG 0 ![false, true] := by
  have hN := cexG_unique_nash.1
  refine ⟨?_, ?_, ?_, by norm_num [cexG, cexG0]⟩
  · rw [nashReversion_spne_iff (by norm_num) (by norm_num) cexG_bound _ hN]
    intro t i a ha
    rw [pathValue_const cexG (by norm_num) (by norm_num)]
    fin_cases i <;> cases a <;> simp_all [cexG, cexG0, cexG1, update] <;> norm_num
  · intro h
    have h1 := le_bestReplyValue cexG_bound 0 ![true, false] true
    rw [pathValue_const cexG (by norm_num) (by norm_num)] at h
    simp [cexG, cexG0, update] at h h1
    norm_num at h h1
    linarith
  · rw [nashReversion_spne_iff (by norm_num) (by norm_num) cexG_bound _ hN]
    intro h
    have := h 0 0 false (by decide)
    rw [pathValue_const cexG (by norm_num) (by norm_num)] at this
    simp [cexG, cexG0, update] at this
    norm_num at this

/-- **Proposition 12.AA.2, corrected** (MWG, p. 420). If condition (12.AA.1) holds for the
outcome path `Q` at the discount factor `δ > 0`, it holds at every `δ' ∈ [δ, 1)`; hence the Nash
reversion profile for `Q` is then an SPNE at `δ'` (`lemma_12_AA_1_if`). -/
theorem proposition_12_AA_2_corrected {I : Type*} [DecidableEq I] {A : I → Type*}
    {g : I → ((i : I) → A i) → ℝ} {δ δ' M : ℝ} (hδ0 : 0 < δ) (hδδ' : δ ≤ δ') (hδ'1 : δ' < 1)
    (hg : ∀ i x, |g i x| ≤ M) (Q : ℕ → (i : I) → A i) (qs : (i : I) → A i)
    (h12 : ∀ t i, bestReplyValue g i (Q t) + δ / (1 - δ) * g i qs ≤ pathValue g δ Q t i) :
    ∀ t i, bestReplyValue g i (Q t) + δ' / (1 - δ') * g i qs ≤ pathValue g δ' Q t i := by
  have hδ1 : δ < 1 := lt_of_le_of_lt hδδ' hδ'1
  have hδ'0 : 0 ≤ δ' := hδ0.le.trans hδδ'
  intro t i
  -- `D s d = v_i(Q, s) − π_i(q*)/(1 − d)` at the discount factor `d`
  set D : ℝ → ℕ → ℝ := fun d s => pathValue g d Q s i - g i qs / (1 - d) with hD
  have hDrec : ∀ d, 0 ≤ d → d < 1 → ∀ s, D d s = (g i (Q s) - g i qs) + d * D d (s + 1) := by
    intro d hd0 hd1 s
    simp only [hD]
    rw [pathValue_succ hd0 hd1 hg Q s i]
    have : (1 - d) ≠ 0 := by linarith
    field_simp
    ring
  have hbr : ∀ s, g i (Q s) ≤ bestReplyValue g i (Q s) := fun s => by
    have := le_bestReplyValue hg i (Q s) (Q s i)
    rwa [update_eq_self] at this
  -- (12.AA.1) at `δ` makes `D δ s ≥ 0` for `s ≥ 1`
  have hDnn : ∀ s, 0 ≤ D δ (s + 1) := by
    intro s
    have h1 := (eq_12_AA_2 hδ0.le hδ1 hg Q qs s i _).1 (h12 s i)
    have h2 := hbr s
    have : 0 ≤ δ * D δ (s + 1) := by simp only [hD]; linarith
    exact nonneg_of_mul_nonneg_right (by linarith) hδ0
  -- the difference `D δ' s − D δ s` is nonnegative
  have hB : ∀ d, 0 ≤ d → d < 1 → ∀ s, |D d s| ≤ 2 * M / (1 - d) := by
    intro d hd0 hd1 s
    have h1 := pathValue_abs_le hd0 hd1 hg Q s i
    have h2 : |g i qs / (1 - d)| ≤ M / (1 - d) := by
      rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < 1 - d)]
      exact div_le_div_of_nonneg_right (hg i qs) (by linarith)
    calc |D d s| ≤ |pathValue g d Q s i| + |g i qs / (1 - d)| := abs_sub _ _
      _ ≤ M / (1 - d) + M / (1 - d) := add_le_add h1 h2
      _ = 2 * M / (1 - d) := by ring
  set K := 2 * M / (1 - δ') + 2 * M / (1 - δ) with hK
  have hgap : ∀ n s, -(δ' ^ n * K) ≤ D δ' s - D δ s := by
    intro n
    induction n with
    | zero =>
      intro s
      have := hB δ' hδ'0 hδ'1 s
      have := hB δ hδ0.le hδ1 s
      rw [pow_zero, one_mul, hK]
      have h3 := neg_abs_le (D δ' s)
      have h4 := le_abs_self (D δ s)
      linarith
    | succ n ih =>
      intro s
      rw [hDrec δ' hδ'0 hδ'1 s, hDrec δ hδ0.le hδ1 s]
      have h5 := ih (s + 1)
      have h6 := hDnn s
      have h7 : 0 ≤ (δ' - δ) * D δ (s + 1) := mul_nonneg (by linarith) h6
      have : g i (Q s) - g i qs + δ' * D δ' (s + 1) - (g i (Q s) - g i qs + δ * D δ (s + 1)) =
          δ' * (D δ' (s + 1) - D δ (s + 1)) + (δ' - δ) * D δ (s + 1) := by ring
      rw [this, pow_succ]
      have h8 : δ' * (-(δ' ^ n * K)) ≤ δ' * (D δ' (s + 1) - D δ (s + 1)) :=
        mul_le_mul_of_nonneg_left h5 hδ'0
      nlinarith
  have hmono : ∀ s, D δ s ≤ D δ' s := by
    intro s
    have ht : Tendsto (fun n : ℕ => -(δ' ^ n * K)) atTop (𝓝 0) := by
      simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hδ'0 hδ'1).mul_const K).neg
    have := le_of_tendsto ht (Eventually.of_forall fun n => hgap n s)
    linarith
  have hfin := (eq_12_AA_2 hδ0.le hδ1 hg Q qs t i _).1 (h12 t i)
  rw [eq_12_AA_2 hδ'0 hδ'1 hg Q qs t i]
  have h9 : δ * D δ (t + 1) ≤ δ' * D δ' (t + 1) :=
    mul_le_mul hδδ' (hmono (t + 1)) (hDnn t) hδ'0
  simp only [hD] at h9
  linarith

/-- **Proposition 12.AA.3** (Friedman's Nash reversion folk theorem; MWG, p. 420). Let payoffs
be bounded by `M`, `q*` a stage Nash equilibrium, and `q` a profile with `π_i(q) > π_i(q*)` for
every player. Then there is `δ̲ < 1` such that for every `δ ∈ (δ̲, 1)` the infinite repetition of
`q` is the outcome path of an SPNE that uses Nash reversion. -/
theorem proposition_12_AA_3 {I : Type*} [Finite I] [Nonempty I] [DecidableEq I] {A : I → Type*}
    {g : I → ((i : I) → A i) → ℝ} {M : ℝ} (hg : ∀ i x, |g i x| ≤ M) {qs q : (i : I) → A i}
    (hqs : IsStageNash g qs) (hgt : ∀ i, g i qs < g i q) :
    ∃ δ₀ < 1, ∀ δ, δ₀ < δ → δ < 1 → 0 ≤ δ →
      IsRepeatedSPNE g δ (nashReversion (fun _ => q) qs) := by
  have := Fintype.ofFinite I
  have hMq : ∀ i, g i q ≤ M := fun i => (le_abs_self _).trans (hg i q)
  have hpos : ∀ i, 0 < M - g i qs := fun i => by linarith [hMq i, hgt i]
  set δ₀ := Finset.univ.sup' Finset.univ_nonempty fun i => (M - g i q) / (M - g i qs) with hδ₀
  have hlt : δ₀ < 1 := by
    rw [hδ₀, Finset.sup'_lt_iff]
    intro i _
    rw [div_lt_one (hpos i)]
    linarith [hgt i]
  refine ⟨δ₀, hlt, fun δ hδ hδ1 hδ0 => lemma_12_AA_1_if hδ0 hδ1 hg _ hqs fun t i => ?_⟩
  have hi : (M - g i q) / (M - g i qs) ≤ δ₀ := Finset.le_sup' (fun i => (M - g i q) /
    (M - g i qs)) (Finset.mem_univ i)
  have : Nonempty (A i) := ⟨q i⟩
  have hbr : bestReplyValue g i q ≤ M :=
    ciSup_le (fun a => (le_abs_self _).trans (hg i _))
  rw [pathValue_const g hδ0 hδ1]
  have h1δ : 0 < 1 - δ := by linarith
  have key : M - g i q ≤ δ * (M - g i qs) := by
    have := (div_le_iff₀ (hpos i)).1 (hi.trans hδ.le)
    linarith
  have e : M + δ / (1 - δ) * g i qs = (M * (1 - δ) + δ * g i qs) / (1 - δ) := by
    field_simp
  calc bestReplyValue g i q + δ / (1 - δ) * g i qs ≤ M + δ / (1 - δ) * g i qs := by linarith
    _ = (M * (1 - δ) + δ * g i qs) / (1 - δ) := e
    _ ≤ g i q / (1 - δ) := div_le_div_of_nonneg_right (by linarith) h1δ.le

/-- **Exercise 12.AA.1, corrected** (MWG, p. 420). If the infinite repetition of `q` is the
outcome path of a Nash reversion SPNE at `δ ∈ [0, 1)` and `π_i(q) < π_i(q*)`, then `q_i` is a
best response to `q_{-i}` with a margin: every other action loses at least
`δ/(1 − δ)(π_i(q*) − π_i(q))`; for `δ > 0` it is a strict best response. -/
theorem exercise_12_AA_1_corrected {I : Type*} [DecidableEq I] {A : I → Type*}
    {g : I → ((i : I) → A i) → ℝ} {δ M : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hg : ∀ i x, |g i x| ≤ M) {qs q : (i : I) → A i} (hqs : IsStageNash g qs)
    (hspne : IsRepeatedSPNE g δ (nashReversion (fun _ => q) qs)) (i : I) (a : A i)
    (ha : a ≠ q i) :
    g i (update q i a) ≤ g i q - δ / (1 - δ) * (g i qs - g i q) := by
  have h := (nashReversion_spne_iff hδ0 hδ1 hg _ hqs).1 hspne 0 i a ha
  rw [pathValue_const g hδ0 hδ1] at h
  have h1δ : (1 - δ) ≠ 0 := by linarith
  have e : g i q / (1 - δ) = g i q + δ * (g i q / (1 - δ)) := by field_simp; ring
  have e2 : δ / (1 - δ) * (g i qs - g i q) = δ * (g i qs / (1 - δ)) - δ * (g i q / (1 - δ)) := by
    ring
  linarith

/-- **Exercise 12.AA.1 under MWG's condition (12.AA.3)** (MWG, p. 420). If `q` satisfies
(12.AA.3), `π̂_i(q_j) − π_i(q) ≤ δ/(1 − δ)[π_i(q) − π_i(q*)]`, with `δ > 0`, then
`π_i(q) ≥ π_i(q*)`: under the printed characterization no `q` giving some player less than
`π_i(q*)` is sustainable. -/
theorem exercise_12_AA_1_printed_condition {I : Type*} [DecidableEq I] {A : I → Type*}
    {g : I → ((i : I) → A i) → ℝ} {δ M : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hg : ∀ i x, |g i x| ≤ M) (q qs : (i : I) → A i) (i : I)
    (h : bestReplyValue g i q - g i q ≤ δ / (1 - δ) * (g i q - g i qs)) : g i qs ≤ g i q := by
  have h1 := le_bestReplyValue hg i q (q i)
  rw [update_eq_self] at h1
  have hpos : 0 < δ / (1 - δ) := div_pos hδ0 (by linarith)
  by_contra hlt
  push Not at hlt
  have := mul_neg_of_pos_of_neg hpos (by linarith : g i q - g i qs < 0)
  linarith

/-- Player `i`'s (pure strategy) minimax payoff `π̲_i = inf_{q_{-i}} sup_{q_i} π_i(q)`
(MWG, p. 421). -/
noncomputable def minimaxValue {I : Type*} [DecidableEq I] {A : I → Type*}
    (g : I → ((i : I) → A i) → ℝ) (i : I) : ℝ :=
  ⨅ x : (i : I) → A i, bestReplyValue g i x

theorem bestReplyValue_ge {I : Type*} [DecidableEq I] {A : I → Type*}
    {g : I → ((i : I) → A i) → ℝ} {M : ℝ} (hg : ∀ i x, |g i x| ≤ M) (i : I)
    (x : (i : I) → A i) : -M ≤ bestReplyValue g i x := by
  have := le_bestReplyValue hg i x (x i)
  rw [update_eq_self] at this
  exact (neg_le_of_abs_le (hg i x)).trans this

/-- **Stage Nash payoffs are individually rational** (MWG, p. 421): `π_i(q*) ≥ π̲_i`. -/
theorem minimax_le_nash {I : Type*} [DecidableEq I] {A : I → Type*}
    {g : I → ((i : I) → A i) → ℝ} {M : ℝ} (hg : ∀ i x, |g i x| ≤ M) {qs : (i : I) → A i}
    (hqs : IsStageNash g qs) (i : I) : minimaxValue g i ≤ g i qs := by
  have : Nonempty (A i) := ⟨qs i⟩
  refine (ciInf_le ⟨-M, fun _ ⟨x, hx⟩ => hx ▸ bestReplyValue_ge hg i x⟩ qs).trans ?_
  exact ciSup_le fun a => hqs i a

/-- **SPNE payoffs are individually rational in every subgame** (MWG, p. 421). If `σ` is an SPNE
of the repeated game, then at every history player `i`'s average payoff `(1 − δ)V_i(h)` is at
least the minimax payoff `π̲_i` (a deviation to a period-by-period near best response secures
almost `π̲_i` in every period). -/
theorem minimax_le_spne_value {I : Type*} [DecidableEq I] {A : I → Type*}
    {g : I → ((i : I) → A i) → ℝ} {δ M : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hg : ∀ i x, |g i x| ≤ M) {σ : OSProfile A} (hσ : IsRepeatedSPNE g δ σ) (i : I)
    (h : OSHist A) : minimaxValue g i ≤ (1 - δ) * osValue (stageU g) δ σ h i := by
  have h1δ : 0 < 1 - δ := by linarith
  have hne : Nonempty (A i) := ⟨σ i h⟩
  refine le_of_forall_pos_le_add fun ε hε => ?_
  -- a near best response at every history
  have hex : ∀ h' : OSHist A, ∃ a : A i,
      bestReplyValue g i (osPlay σ h') - ε < g i (update (osPlay σ h') i a) := by
    intro h'
    have hb : BddAbove (Set.range fun a : A i => g i (update (osPlay σ h') i a)) :=
      ⟨M, fun _ ⟨b, hb⟩ => hb ▸ (le_abs_self _).trans (hg i _)⟩
    exact exists_lt_of_lt_ciSup (by unfold bestReplyValue at *; linarith)
  choose τ hτ using hex
  have hdev := hσ i τ h
  -- per-period payoffs of the deviation exceed `π̲_i − ε`
  have hterm : ∀ h' : OSHist A, minimaxValue g i - ε ≤
      stageU g i h' (osPlay (update σ i τ) h') := by
    intro h'
    rw [osPlay_update]
    have h2 : minimaxValue g i ≤ bestReplyValue g i (osPlay σ h') :=
      ciInf_le ⟨-M, fun _ ⟨x, hx⟩ => hx ▸ bestReplyValue_ge hg i x⟩ _
    have h3 := hτ h'
    simp only [stageU]
    linarith
  have hs := osValue_summable hδ0 hδ1 (stageU_bound hg) (update σ i τ) h i
  have hgeo := (summable_geometric_of_lt_one hδ0 hδ1).mul_right (minimaxValue g i - ε)
  have hlow : (minimaxValue g i - ε) / (1 - δ) ≤ osValue (stageU g) δ (update σ i τ) h i := by
    have := hgeo.tsum_le_tsum (fun n => mul_le_mul_of_nonneg_left (hterm _)
      (pow_nonneg hδ0 n)) hs
    rw [tsum_mul_right, tsum_geometric_of_lt_one hδ0 hδ1] at this
    rw [div_eq_inv_mul]
    exact this
  have := hlow.trans hdev
  rw [div_le_iff₀ h1δ] at this
  linarith

end MWG.MarketPower
