/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGDynamicGames.OneShotDeviation
import Mathlib.Order.Filter.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic.FinCases

/-!
# Infinitely repeated games and Nash reversion

MWG, Appendix A of Chapter 12, pp. 417-421.

The repeated game is Chapter 9's multi-stage game with observed actions (`OSHist`,
`OSProfile`, `osValue`), with the stage-game payoffs `π_i(q)` as per-period payoffs (`stageU`):
a pure strategy maps histories to actions, and `osValue (stageU g) δ σ h i` is player `i`'s
discounted payoff `∑ₙ δⁿ π_i(qₙ)` from history `h`. `IsRepeatedSPNE` is subgame perfection: at
every history no player gains by any change of strategy. For an outcome path `Q`,
`pathValue g δ Q t i = v_i(Q, t) = ∑_τ δ^τ π_i(q_{t+τ})`.

* `osValue_eq_of_rec`: a bounded function satisfying the one-step recursion is the value.
* `stage_nash_spne`: playing a stage Nash equilibrium after every history is an SPNE (p. 418).
* `nashReversion` (Definition 12.AA.1) and `nashReversion_spne_iff`: the Nash reversion profile
  for `Q` is an SPNE iff for all `t`, `i` and all actions `a ≠ q_{it}`,
  `π_i(a, q_{jt}) + δπ_i(q*)/(1 − δ) ≤ v_i(Q, t)` (corrected Lemma 12.AA.1).
* `lemma_12_AA_1_if`: condition (12.AA.1) is sufficient. `counterexample_12_AA`: it is not
  necessary (correction), and in the same game Proposition 12.AA.2 and Exercise 12.AA.1 fail.
* `eq_12_AA_2`, `eq_12_AA_3`: the forms (12.AA.2) and (12.AA.3).
* `proposition_12_AA_2_corrected`: condition (12.AA.1) at `δ` implies it at every `δ' ≥ δ`.
* `proposition_12_AA_3`: Friedman's Nash reversion folk theorem.
* `exercise_12_AA_1_corrected`: a stationary path giving player `i` less than `π_i(q*)` can be
  sustained only if `q_i` is a strict best response to `q_j`.
* `minimax_le_nash`, `minimax_le_spne_value` (p. 421): stage Nash payoffs and SPNE average
  payoffs in every subgame are at least the minimax payoff.
-/

namespace MWG.MarketPower

open MWG.DynamicGames Function Filter Topology

variable {I : Type*} [DecidableEq I] {A : I → Type*}

/-- The stage-game payoffs `π_i(q)` as per-period payoffs of the repeated game. -/
def stageU (g : I → ((i : I) → A i) → ℝ) : I → OSHist A → ((i : I) → A i) → ℝ :=
  fun i _ x => g i x

/-- **Subgame perfection in the repeated game** (MWG, pp. 418, 275). At every history `h`, no
player `i` gains by switching to any other strategy `τ`. -/
def IsRepeatedSPNE (g : I → ((i : I) → A i) → ℝ) (δ : ℝ) (σ : OSProfile A) : Prop :=
  ∀ i (τ : OSHist A → A i) h, osValue (stageU g) δ (update σ i τ) h i ≤ osValue (stageU g) δ σ h i

omit [DecidableEq I] in
/-- **Values from a recursion.** If `V` is bounded and satisfies
`V(h) = u_i(h, σ(h)) + δV(σ(h) :: h)`, then `V` is player `i`'s continuation payoff. -/
theorem osValue_eq_of_rec {u : I → OSHist A → ((i : I) → A i) → ℝ} {δ M B : ℝ} (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1) (hu : ∀ i h x, |u i h x| ≤ M) (σ : OSProfile A) (i : I) (V : OSHist A → ℝ)
    (hV : ∀ h, |V h| ≤ B) (hrec : ∀ h, V h = u i h (osPlay σ h) + δ * V (osPlay σ h :: h))
    (h : OSHist A) : osValue u δ σ h i = V h := by
  set K := M / (1 - δ) + B with hK
  have hD : ∀ n : ℕ, ∀ h, |osValue u δ σ h i - V h| ≤ δ ^ n * K := by
    intro n
    induction n with
    | zero =>
      intro h
      rw [pow_zero, one_mul]
      exact (abs_sub _ _).trans (add_le_add (osValue_abs_le hδ0 hδ1 hu σ h i) (hV h))
    | succ n ih =>
      intro h
      rw [osValue_succ hδ0 hδ1 hu σ h i, hrec h]
      have : u i h (osPlay σ h) + δ * osValue u δ σ (osPlay σ h :: h) i -
          (u i h (osPlay σ h) + δ * V (osPlay σ h :: h)) =
          δ * (osValue u δ σ (osPlay σ h :: h) i - V (osPlay σ h :: h)) := by ring
      rw [this, abs_mul, abs_of_nonneg hδ0, pow_succ]
      calc δ * |osValue u δ σ (osPlay σ h :: h) i - V (osPlay σ h :: h)|
          ≤ δ * (δ ^ n * K) := mul_le_mul_of_nonneg_left (ih _) hδ0
        _ = δ ^ n * δ * K := by ring
  have ht : Tendsto (fun n : ℕ => δ ^ n * K) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hδ0 hδ1).mul_const K
  have h0 : |osValue u δ σ h i - V h| ≤ 0 := ge_of_tendsto ht (Eventually.of_forall fun n => hD n h)
  have := abs_nonpos_iff.1 h0
  linarith

omit [DecidableEq I] in
theorem stageU_bound {g : I → ((i : I) → A i) → ℝ} {M : ℝ} (hg : ∀ i x, |g i x| ≤ M) :
    ∀ i h x, |stageU g i h x| ≤ M := fun i _ x => hg i x

/-! ### Outcome paths -/

/-- Player `i`'s discounted payoff `v_i(Q, t) = ∑_τ δ^τ π_i(q_{t+τ})` from period `t` of the
outcome path `Q` (MWG, p. 418). -/
noncomputable def pathValue (g : I → ((i : I) → A i) → ℝ) (δ : ℝ) (Q : ℕ → (i : I) → A i)
    (t : ℕ) (i : I) : ℝ :=
  ∑' n : ℕ, δ ^ n * g i (Q (t + n))

omit [DecidableEq I] in
theorem pathValue_summable {g : I → ((i : I) → A i) → ℝ} {δ M : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hg : ∀ i x, |g i x| ≤ M) (Q : ℕ → (i : I) → A i) (t : ℕ) (i : I) :
    Summable fun n : ℕ => δ ^ n * g i (Q (t + n)) := by
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hδ0 hδ1).mul_right M)
    fun n => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hδ0 n)]
  exact mul_le_mul_of_nonneg_left (hg _ _) (pow_nonneg hδ0 n)

omit [DecidableEq I] in
/-- `v_i(Q, t) = π_i(q_t) + δv_i(Q, t + 1)`. -/
theorem pathValue_succ {g : I → ((i : I) → A i) → ℝ} {δ M : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hg : ∀ i x, |g i x| ≤ M) (Q : ℕ → (i : I) → A i) (t : ℕ) (i : I) :
    pathValue g δ Q t i = g i (Q t) + δ * pathValue g δ Q (t + 1) i := by
  unfold pathValue
  rw [(pathValue_summable hδ0 hδ1 hg Q t i).tsum_eq_zero_add, ← tsum_mul_left]
  simp only [pow_zero, one_mul, add_zero, pow_succ]
  congr 1
  refine tsum_congr fun n => ?_
  rw [show t + (n + 1) = t + 1 + n by ring]
  ring

omit [DecidableEq I] in
theorem pathValue_abs_le {g : I → ((i : I) → A i) → ℝ} {δ M : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hg : ∀ i x, |g i x| ≤ M) (Q : ℕ → (i : I) → A i) (t : ℕ) (i : I) :
    |pathValue g δ Q t i| ≤ M / (1 - δ) := by
  have hs := pathValue_summable hδ0 hδ1 hg Q t i
  have hgeo := (summable_geometric_of_lt_one hδ0 hδ1).mul_right M
  have hle : ∀ n : ℕ, |δ ^ n * g i (Q (t + n))| ≤ δ ^ n * M := by
    intro n
    rw [abs_mul, abs_of_nonneg (pow_nonneg hδ0 n)]
    exact mul_le_mul_of_nonneg_left (hg _ _) (pow_nonneg hδ0 n)
  have h1 : |pathValue g δ Q t i| ≤ ∑' n : ℕ, δ ^ n * M := by
    unfold pathValue
    rw [abs_le]
    constructor
    · rw [← tsum_neg]
      exact hgeo.neg.tsum_le_tsum (fun n => neg_le_of_abs_le (hle n)) hs
    · exact hs.tsum_le_tsum (fun n => le_of_abs_le (hle n)) hgeo
  rw [tsum_mul_right, tsum_geometric_of_lt_one hδ0 hδ1] at h1
  rw [div_eq_inv_mul]
  exact h1

omit [DecidableEq I] in
/-- A constant path gives `v_i = π_i(q)/(1 − δ)`. -/
theorem pathValue_const (g : I → ((i : I) → A i) → ℝ) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (q : (i : I) → A i) (t : ℕ) (i : I) :
    pathValue g δ (fun _ => q) t i = g i q / (1 - δ) := by
  unfold pathValue
  rw [tsum_mul_right, tsum_geometric_of_lt_one hδ0 hδ1, div_eq_inv_mul]

/-- The history consisting of the first `n` profiles of the path `Q` (most recent first). -/
def pathHist (Q : ℕ → (i : I) → A i) : ℕ → OSHist A
  | 0 => []
  | n + 1 => Q n :: pathHist Q n

omit [DecidableEq I] in
theorem pathHist_length (Q : ℕ → (i : I) → A i) (n : ℕ) : (pathHist Q n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [pathHist, ih]

omit [DecidableEq I] in
/-- Once play has left the path, it never returns. -/
theorem not_pathHist_cons {Q : ℕ → (i : I) → A i} {h : OSHist A} (hh : h ≠ pathHist Q h.length)
    (x : (i : I) → A i) : x :: h ≠ pathHist Q (x :: h).length := by
  intro heq
  simp only [List.length_cons, pathHist] at heq
  exact hh (List.cons.inj heq).2

open Classical in
/-- **Definition 12.AA.1** (MWG, p. 418). The Nash reversion profile for the outcome path `Q`:
play `q_t` in period `t` as long as play has followed `Q`, and the stage Nash equilibrium `q*`
after any deviation. -/
noncomputable def nashReversion (Q : ℕ → (i : I) → A i) (qs : (i : I) → A i) : OSProfile A :=
  fun i h => if h = pathHist Q h.length then Q h.length i else qs i

omit [DecidableEq I] in
theorem osPlay_nashReversion_on {Q : ℕ → (i : I) → A i} {qs : (i : I) → A i} (t : ℕ) :
    osPlay (nashReversion Q qs) (pathHist Q t) = Q t := by
  funext i
  simp [osPlay, nashReversion, pathHist_length]

omit [DecidableEq I] in
theorem osPlay_nashReversion_off {Q : ℕ → (i : I) → A i} {qs : (i : I) → A i} {h : OSHist A}
    (hh : h ≠ pathHist Q h.length) : osPlay (nashReversion Q qs) h = qs := by
  funext i
  simp [osPlay, nashReversion, hh]

/-- A pure strategy Nash equilibrium of the stage game. -/
def IsStageNash (g : I → ((i : I) → A i) → ℝ) (qs : (i : I) → A i) : Prop :=
  ∀ i a, g i (update qs i a) ≤ g i qs

open Classical in
/-- The value of the Nash reversion profile: `v_i(Q, t)` on the path and `π_i(q*)/(1 − δ)` off
it. -/
noncomputable def nashReversionValue (g : I → ((i : I) → A i) → ℝ) (δ : ℝ)
    (Q : ℕ → (i : I) → A i) (qs : (i : I) → A i) (i : I) (h : OSHist A) : ℝ :=
  if h = pathHist Q h.length then pathValue g δ Q h.length i else g i qs / (1 - δ)

omit [DecidableEq I] in
theorem nashReversionValue_on (g : I → ((i : I) → A i) → ℝ) (δ : ℝ) (Q : ℕ → (i : I) → A i)
    (qs : (i : I) → A i) (i : I) (t : ℕ) :
    nashReversionValue g δ Q qs i (pathHist Q t) = pathValue g δ Q t i := by
  simp [nashReversionValue, pathHist_length]

omit [DecidableEq I] in
theorem nashReversionValue_off (g : I → ((i : I) → A i) → ℝ) (δ : ℝ) {Q : ℕ → (i : I) → A i}
    (qs : (i : I) → A i) (i : I) {h : OSHist A} (hh : h ≠ pathHist Q h.length) :
    nashReversionValue g δ Q qs i h = g i qs / (1 - δ) := by
  simp [nashReversionValue, hh]

omit [DecidableEq I] in
theorem pathHist_succ_eq (Q : ℕ → (i : I) → A i) (t : ℕ) :
    Q t :: pathHist Q t = pathHist Q (t + 1) := rfl

omit [DecidableEq I] in
theorem update_cons_off [DecidableEq I] {Q : ℕ → (i : I) → A i} {t : ℕ} {i : I} {a : A i}
    (ha : a ≠ Q t i) :
    update (Q t) i a :: pathHist Q t ≠ pathHist Q (update (Q t) i a :: pathHist Q t).length := by
  simp only [List.length_cons, pathHist_length, pathHist]
  intro heq
  have := congrFun (List.cons.inj heq).1 i
  simp only [update_self] at this
  exact ha this

omit [DecidableEq I] in
theorem osValue_nashReversion {g : I → ((i : I) → A i) → ℝ} {δ M : ℝ} (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1) (hg : ∀ i x, |g i x| ≤ M) (Q : ℕ → (i : I) → A i) (qs : (i : I) → A i)
    (i : I) (h : OSHist A) :
    osValue (stageU g) δ (nashReversion Q qs) h i = nashReversionValue g δ Q qs i h := by
  classical
  have hM : 0 ≤ M := (abs_nonneg _).trans (hg i qs)
  refine osValue_eq_of_rec hδ0 hδ1 (stageU_bound hg) _ i _ (B := M / (1 - δ)) (fun h => ?_)
    (fun h => ?_) h
  · unfold nashReversionValue
    split_ifs
    · exact pathValue_abs_le hδ0 hδ1 hg Q _ i
    · rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < 1 - δ)]
      exact div_le_div_of_nonneg_right (hg i qs) (by linarith)
  · by_cases hh : h = pathHist Q h.length
    · set t := h.length
      rw [hh, osPlay_nashReversion_on, nashReversionValue_on, pathHist_succ_eq,
        nashReversionValue_on]
      exact pathValue_succ hδ0 hδ1 hg Q t i
    · rw [osPlay_nashReversion_off hh, nashReversionValue_off g δ qs i hh,
        nashReversionValue_off g δ qs i (not_pathHist_cons hh qs)]
      simp only [stageU]
      have : (1 - δ) ≠ 0 := by linarith
      field_simp
      ring

/-- **Lemma 12.AA.1, corrected** (MWG, p. 418). Let `q*` be a stage Nash equilibrium and payoffs
be bounded. The Nash reversion profile for `Q` is an SPNE if and only if, for every period `t`,
player `i`, and action `a ≠ q_{it}`,
`π_i(a, q_{-i,t}) + δπ_i(q*)/(1 − δ) ≤ v_i(Q, t)`.
(MWG's condition (12.AA.1) uses the best-response payoff `br_i(q_{jt})`, which also counts
`a = q_{it}`; see `counterexample_12_AA`.) -/
theorem nashReversion_spne_iff {g : I → ((i : I) → A i) → ℝ} {δ M : ℝ} (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1) (hg : ∀ i x, |g i x| ≤ M) (Q : ℕ → (i : I) → A i) {qs : (i : I) → A i}
    (hqs : IsStageNash g qs) :
    IsRepeatedSPNE g δ (nashReversion Q qs) ↔
      ∀ t i (a : A i), a ≠ Q t i →
        g i (update (Q t) i a) + δ * (g i qs / (1 - δ)) ≤ pathValue g δ Q t i := by
  classical
  have h1δ : (0 : ℝ) < 1 - δ := by linarith
  have hval := osValue_nashReversion hδ0 hδ1 hg Q qs
  rw [IsRepeatedSPNE, oneShot_deviation_principle_discounted_iff hδ0 hδ1 (stageU_bound hg)]
  simp only [hval, stageU]
  constructor
  · intro hos t i a ha
    have := hos i (pathHist Q t) a
    rw [osPlay_nashReversion_on, nashReversionValue_off g δ qs i (update_cons_off ha),
      nashReversionValue_on] at this
    exact this
  · intro hcond i h a
    by_cases hh : h = pathHist Q h.length
    · set t := h.length
      rw [hh, osPlay_nashReversion_on, nashReversionValue_on]
      by_cases ha : a = Q t i
      · subst ha
        rw [update_eq_self, pathHist_succ_eq, nashReversionValue_on,
          pathValue_succ hδ0 hδ1 hg Q t i]
      · rw [nashReversionValue_off g δ qs i (update_cons_off ha)]
        exact hcond t i a ha
    · rw [osPlay_nashReversion_off hh, nashReversionValue_off g δ qs i hh,
        nashReversionValue_off g δ qs i (not_pathHist_cons hh _)]
      have := hqs i a
      have hne : (1 - δ) ≠ 0 := by linarith
      have h2 : g i qs / (1 - δ) = g i qs + δ * (g i qs / (1 - δ)) := by field_simp; ring
      linarith

/-- **The stage Nash equilibrium repeated** (MWG, p. 418). Playing a stage Nash equilibrium `q*`
in every period regardless of history is an SPNE for every `δ ∈ [0, 1)`. -/
theorem stage_nash_spne {g : I → ((i : I) → A i) → ℝ} {δ M : ℝ} (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1) (hg : ∀ i x, |g i x| ≤ M) {qs : (i : I) → A i} (hqs : IsStageNash g qs) :
    IsRepeatedSPNE g δ (nashReversion (fun _ => qs) qs) := by
  rw [nashReversion_spne_iff hδ0 hδ1 hg _ hqs]
  intro t i a _
  rw [pathValue_const g hδ0 hδ1]
  have := hqs i a
  have hne : (1 - δ) ≠ 0 := by linarith
  have h2 : g i qs / (1 - δ) = g i qs + δ * (g i qs / (1 - δ)) := by
    field_simp; ring
  linarith

/-- The best-response payoff `br_i(q_{-i}) = sup_a π_i(a, q_{-i})` (MWG, p. 417). -/
noncomputable def bestReplyValue (g : I → ((i : I) → A i) → ℝ) (i : I) (x : (i : I) → A i) : ℝ :=
  ⨆ a : A i, g i (update x i a)

theorem le_bestReplyValue {g : I → ((i : I) → A i) → ℝ} {M : ℝ} (hg : ∀ i x, |g i x| ≤ M)
    (i : I) (x : (i : I) → A i) (a : A i) : g i (update x i a) ≤ bestReplyValue g i x :=
  le_ciSup (f := fun a => g i (update x i a)) ⟨M, fun _ ⟨_, hb⟩ => hb ▸ (le_abs_self _).trans
    (hg i _)⟩ a

/-- **Lemma 12.AA.1, the "if" part** (MWG, p. 418, condition (12.AA.1)). If
`br_i(q_{jt}) + δπ_i(q*)/(1 − δ) ≤ v_i(Q, t)` for all `t` and `i`, the Nash reversion profile for
`Q` is an SPNE. -/
theorem lemma_12_AA_1_if {g : I → ((i : I) → A i) → ℝ} {δ M : ℝ} (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1) (hg : ∀ i x, |g i x| ≤ M) (Q : ℕ → (i : I) → A i) {qs : (i : I) → A i}
    (hqs : IsStageNash g qs)
    (h12AA1 : ∀ t i, bestReplyValue g i (Q t) + δ / (1 - δ) * g i qs ≤ pathValue g δ Q t i) :
    IsRepeatedSPNE g δ (nashReversion Q qs) := by
  rw [nashReversion_spne_iff hδ0 hδ1 hg Q hqs]
  intro t i a _
  have h1 := le_bestReplyValue hg i (Q t) a
  have h2 := h12AA1 t i
  have : δ * (g i qs / (1 - δ)) = δ / (1 - δ) * g i qs := by ring
  linarith

omit [DecidableEq I] in
/-- **Condition (12.AA.2)** (MWG, p. 419): (12.AA.1) rewritten as
`br_i(q_{jt}) − π_i(q_t) ≤ δ(v_i(Q, t + 1) − π_i(q*)/(1 − δ))`. -/
theorem eq_12_AA_2 {g : I → ((i : I) → A i) → ℝ} {δ M : ℝ} (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1) (hg : ∀ i x, |g i x| ≤ M) (Q : ℕ → (i : I) → A i) (qs : (i : I) → A i)
    (t : ℕ) (i : I) (br : ℝ) :
    br + δ / (1 - δ) * g i qs ≤ pathValue g δ Q t i ↔
      br - g i (Q t) ≤ δ * (pathValue g δ Q (t + 1) i - g i qs / (1 - δ)) := by
  rw [pathValue_succ hδ0 hδ1 hg Q t i]
  have : δ / (1 - δ) * g i qs = δ * (g i qs / (1 - δ)) := by ring
  rw [this]
  constructor <;> intro h <;> linarith

omit [DecidableEq I] in
/-- **Condition (12.AA.3)** (MWG, p. 419): for a stationary path `q, q, …`, (12.AA.1) reads
`br_i(q_j) − π_i(q) ≤ δ/(1 − δ)[π_i(q) − π_i(q*)]`. -/
theorem eq_12_AA_3 (g : I → ((i : I) → A i) → ℝ) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1) (q qs : (i : I) → A i) (t : ℕ) (i : I) (br : ℝ) :
    br + δ / (1 - δ) * g i qs ≤ pathValue g δ (fun _ => q) t i ↔
      br - g i q ≤ δ / (1 - δ) * (g i q - g i qs) := by
  rw [pathValue_const g hδ0 hδ1]
  have h1δ : (0 : ℝ) < 1 - δ := by linarith
  have : g i q / (1 - δ) = g i q + δ / (1 - δ) * g i q := by field_simp; ring
  rw [this]
  constructor <;> intro h <;> linarith

end MWG.MarketPower
