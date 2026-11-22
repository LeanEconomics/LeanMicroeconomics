/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGDynamicGames.Bargaining

/-!
# Bargaining with offer costs

MWG, Exercises 9.B.7 and 9.B.13 (pp. 302-303): the alternating-offer game of Example 9.AA.1
(Appendix A, pp. 296-297) without discounting, where making an offer costs the proposer
`c ∈ (0, v)`, incurred whether or not the offer is accepted.

The game reuses the histories and profiles of `MWGDynamicGames.Bargaining` (`BargainingProfile`,
the lists of rejected offers, `BargainingGame.path`, `BargainingGame.proposer`). Agreement in
period `t` on the offer `y` gives the responder `y` and the proposer `v − y`, minus each player's
total offer costs; without agreement each player loses her offer costs. The horizon `T : ℕ∞`
is the number of periods (`⊤`: Exercise 9.B.13). Payoffs are in `WithBot ℝ`: perpetual
disagreement in the infinite game means infinitely many offers, so payoff `⊥` (`−∞`).

* `firstStop`: the payoff of a stream of flows `f k` stopped at the first `k` with
  `c k = false` with terminal payoff `g k`; its recursion `firstStop_eq` and the one-stage
  bound `firstStop_le`.
* `OfferCostGame.threshold_isSPNE`: a threshold profile (the period-`n` proposer offers `a n`,
  the responder accepts exactly the offers `y ≥ a n`) is an SPNE when `a n` is the responder's
  value as the next proposer, `a n = v − c − a (n + 1)` (and `a n = 0` in the last period).
* `exercise_9_B_7`: with `T` periods the SPNE is unique; with `m` periods left the proposer
  offers `W (m − 1)`, the responder accepts exactly the offers `y ≥ W (m − 1)`, where
  `W k = v − c` for odd `k` and `0` for even `k`; player 1 gets `W T` and player 2 `W (T − 1)`:
  `(v − c, 0)` if `T` is odd and `(0, v − c)` if `T` is even. `exercise_9_B_7_limit`: the
  outcome has no limit as `T → ∞`.
* `exercise_9_B_13`: in the infinite game, every SPNE gives payoffs `a, b ≥ 0` with
  `a + b ≤ v − c` (in every subgame), and every split `(a, v − c − a)`, `a ∈ [0, v − c]`, is
  the payoff of an SPNE with immediate agreement; so the SPNE is not unique
  (`exercise_9_B_13_not_unique`), and player 1's set of SPNE payoffs is exactly `[0, v − c]`
  (`exercise_9_B_13_payoffs`). `exercise_9_B_13_delay`: if `v < 2c` agreement is immediate in
  every SPNE; if `v ≥ 2c` there is an SPNE in which the first offer is rejected
  (`delayProfile`, verified with the one-stage deviation principle `isSPNE_of_oneStage`).
-/

namespace MWG.DynamicGames

open Classical in
/-- The payoff of the flow stream `f` stopped at the first `k` with `c k = false`, with
terminal payoff `g k` there; `⊥` if the stream never stops. -/
noncomputable def firstStop (c : ℕ → Bool) (f : ℕ → ℝ) (g : ℕ → WithBot ℝ) : WithBot ℝ :=
  if hx : ∃ k, c k = false then
    (((∑ k ∈ Finset.range (Nat.find hx), f k : ℝ)) : WithBot ℝ) + g (Nat.find hx)
  else ⊥

open Classical in
theorem firstStop_of_exists {c : ℕ → Bool} (f : ℕ → ℝ) (g : ℕ → WithBot ℝ)
    (hx : ∃ k, c k = false) : firstStop c f g =
      (((∑ k ∈ Finset.range (Nat.find hx), f k : ℝ)) : WithBot ℝ) + g (Nat.find hx) := by
  unfold firstStop
  split_ifs
  rfl

theorem firstStop_of_not_exists {c : ℕ → Bool} (f : ℕ → ℝ) (g : ℕ → WithBot ℝ)
    (hx : ¬ ∃ k, c k = false) : firstStop c f g = ⊥ := by
  unfold firstStop
  split_ifs
  rfl

/-- The recursion of a stopped stream. -/
theorem firstStop_eq (c : ℕ → Bool) (f : ℕ → ℝ) (g : ℕ → WithBot ℝ) :
    firstStop c f g = if c 0 = true then ((f 0 : ℝ) : WithBot ℝ) +
      firstStop (fun k => c (k + 1)) (fun k => f (k + 1)) (fun k => g (k + 1)) else g 0 := by
  classical
  by_cases h0 : c 0 = true
  · simp only [h0, ↓reduceIte]
    by_cases hx' : ∃ k, c (k + 1) = false
    · have hx : ∃ k, c k = false := let ⟨k, hk⟩ := hx'; ⟨k + 1, hk⟩
      have hf : Nat.find hx = Nat.find hx' + 1 :=
        Nat.find_comp_succ hx hx' (by simp [h0])
      rw [firstStop_of_exists f g hx, firstStop_of_exists _ _ hx', hf,
        Finset.sum_range_succ', WithBot.coe_add, add_comm (((∑ k ∈ Finset.range _, _ : ℝ)) :
          WithBot ℝ), add_assoc]
    · have hx : ¬ ∃ k, c k = false := by
        rintro ⟨k, hk⟩
        cases k with
        | zero => simp [h0] at hk
        | succ k => exact hx' ⟨k, hk⟩
      rw [firstStop_of_not_exists f g hx, firstStop_of_not_exists _ _ hx', WithBot.add_bot]
  · have h0' : c 0 = false := by simpa using h0
    have hx : ∃ k, c k = false := ⟨0, h0'⟩
    have hf : Nat.find hx = 0 := (Nat.find_eq_zero hx).2 h0'
    rw [firstStop_of_exists f g hx, hf]
    simp [h0']

/-- **One-stage bound for stopped streams.** If `f k + b (k + 1) ≤ b k` whenever the stream
continues and `g k ≤ b k` where it stops, then `b 0` bounds the stopped payoff. -/
theorem firstStop_le {c : ℕ → Bool} {f : ℕ → ℝ} {g : ℕ → WithBot ℝ} (b : ℕ → ℝ)
    (hc : ∀ k, c k = true → f k + b (k + 1) ≤ b k)
    (hg : ∀ k, c k = false → g k ≤ b k) : firstStop c f g ≤ b 0 := by
  classical
  have key : ∀ K (c : ℕ → Bool) (f : ℕ → ℝ) (g : ℕ → WithBot ℝ) (b : ℕ → ℝ),
      (∀ k, c k = true → f k + b (k + 1) ≤ b k) → (∀ k, c k = false → g k ≤ b k) →
      (∀ j < K, c j = true) → c K = false →
      (((∑ k ∈ Finset.range K, f k : ℝ)) : WithBot ℝ) + g K ≤ b 0 := by
    intro K
    induction K with
    | zero =>
      intro c f g b _ hg _ hK
      simpa using hg 0 hK
    | succ K ih =>
      intro c f g b hc hg hj hK
      have h1 := ih (fun k => c (k + 1)) (fun k => f (k + 1)) (fun k => g (k + 1))
        (fun k => b (k + 1)) (fun k hk => hc (k + 1) hk) (fun k hk => hg (k + 1) hk)
        (fun j hj' => hj (j + 1) (by omega)) hK
      have h2 := hc 0 (hj 0 (by omega))
      rw [Finset.sum_range_succ', WithBot.coe_add, add_comm (((∑ k ∈ Finset.range _, _ : ℝ)) :
          WithBot ℝ), add_assoc]
      calc ((f 0 : ℝ) : WithBot ℝ) + ((((∑ k ∈ Finset.range K, f (k + 1) : ℝ)) : WithBot ℝ) +
            g (K + 1)) ≤ ((f 0 : ℝ) : WithBot ℝ) + ((b 1 : ℝ) : WithBot ℝ) := by
            gcongr
        _ ≤ b 0 := by
            rw [← WithBot.coe_add]
            exact WithBot.coe_le_coe.2 h2
  by_cases hx : ∃ k, c k = false
  · rw [firstStop_of_exists f g hx]
    exact key _ c f g b hc hg (fun j hj => by simpa using Nat.find_min hx hj) (Nat.find_spec hx)
  · rw [firstStop_of_not_exists f g hx]
    exact bot_le

/-- The sum of two stopped streams with the same stopping rule. -/
theorem firstStop_add (c : ℕ → Bool) (f f' : ℕ → ℝ) (g g' : ℕ → WithBot ℝ) :
    firstStop c f g + firstStop c f' g' = firstStop c (fun k => f k + f' k) (fun k => g k + g' k)
    := by
  classical
  by_cases hx : ∃ k, c k = false
  · rw [firstStop_of_exists f g hx, firstStop_of_exists f' g' hx, firstStop_of_exists _ _ hx,
      Finset.sum_add_distrib, WithBot.coe_add]
    abel
  · rw [firstStop_of_not_exists f g hx, firstStop_of_not_exists f' g' hx,
      firstStop_of_not_exists _ _ hx, WithBot.bot_add]

/-- The bargaining game with offer costs (MWG, Exercises 9.B.7 and 9.B.13, pp. 302-303): the
surplus `v`, the cost `c ∈ (0, v)` of making an offer and the horizon `T` (number of periods;
`⊤` for the infinite horizon). There is no discounting. -/
structure OfferCostGame where
  /-- The amount to be divided. -/
  v : ℝ
  /-- The cost of making an offer. -/
  c : ℝ
  /-- The horizon: the number of periods. -/
  T : ℕ∞
  c_pos : 0 < c
  c_lt_v : c < v

namespace OfferCostGame

open BargainingGame (proposer other other_ne ne_other other_other eq_or_eq_other proposer_succ
  path path_succ length_path setResp setProp IsDeviation setResp_isDeviation
  setProp_isDeviation)

variable (G : OfferCostGame)

/-- Period `n` is within the horizon. -/
def Live (n : ℕ) : Prop := (n : ℕ∞) < G.T

/-- Player `i`'s share (before costs) of an agreement on the offer `y` in period `n`. -/
def share (i : Fin 2) (n : ℕ) (y : ℝ) : ℝ := if proposer n = i then G.v - y else y

/-- Player `i`'s offer cost in period `n`: `c` if she is the proposer. -/
def offerCost (i : Fin 2) (n : ℕ) : ℝ := if proposer n = i then G.c else 0

theorem share_proposer (n : ℕ) (y : ℝ) : G.share (proposer n) n y = G.v - y := by
  simp [share]

theorem share_other (n : ℕ) (y : ℝ) : G.share (other (proposer n)) n y = y := by
  simp [share, ne_other]

theorem offerCost_proposer (n : ℕ) : G.offerCost (proposer n) n = G.c := by
  simp [offerCost]

theorem offerCost_other (n : ℕ) : G.offerCost (other (proposer n)) n = 0 := by
  simp [offerCost, ne_other]

open Classical in
/-- Player `i`'s payoff from the proposal node `h` under `σ`, counting the costs of the offers
made from `h` on: her share of the first agreement minus her offer costs, `−`(her offer costs)
if the horizon ends without agreement, and `⊥` under perpetual disagreement. -/
noncomputable def value (σ : BargainingProfile) (h : List ℝ) (i : Fin 2) : WithBot ℝ :=
  firstStop
    (fun k => decide (G.Live (h.length + k)) && !σ.resp (path σ h k) (σ.prop (path σ h k)))
    (fun k => -G.offerCost i (h.length + k))
    (fun k => if G.Live (h.length + k) then
      ((G.share i (h.length + k) (σ.prop (path σ h k)) - G.offerCost i (h.length + k) : ℝ) :
        WithBot ℝ) else 0)

open Classical in
/-- Player `i`'s payoff from the response node `(h, y)` (period `h.length` live). -/
noncomputable def respValue (σ : BargainingProfile) (h : List ℝ) (y : ℝ) (i : Fin 2) :
    WithBot ℝ :=
  if σ.resp h y = true then ((G.share i h.length y - G.offerCost i h.length : ℝ) : WithBot ℝ)
  else ((-G.offerCost i h.length : ℝ) : WithBot ℝ) + G.value σ (y :: h) i

/-- Beyond the horizon payoffs (from then on) are `0`. -/
theorem value_of_not_live {σ : BargainingProfile} {h : List ℝ} (hl : ¬ G.Live h.length)
    (i : Fin 2) : G.value σ h i = 0 := by
  unfold value
  rw [firstStop_eq]
  simp [hl]

/-- The value at a live proposal node is the value at the response node to the offer made. -/
theorem value_eq_respValue (σ : BargainingProfile) {h : List ℝ} (hl : G.Live h.length)
    (i : Fin 2) : G.value σ h i = G.respValue σ h (σ.prop h) i := by
  unfold value respValue
  rw [firstStop_eq]
  cases hr : σ.resp h (σ.prop h) with
  | true => simp [hl, path, hr]
  | false =>
    simp only [path, add_zero, hl, decide_true, hr, Bool.not_false, Bool.and_self,
      ↓reduceIte, Bool.false_eq_true]
    congr 1
    unfold value
    congr 1
    · funext k
      rw [← path_succ, List.length_cons, show h.length + 1 + k = h.length + (k + 1) by omega]
      rfl
    · funext k
      rw [List.length_cons, show h.length + 1 + k = h.length + (k + 1) by omega]
    · funext k
      rw [← path_succ, List.length_cons, show h.length + 1 + k = h.length + (k + 1) by omega]
      rfl

theorem respValue_accept {σ : BargainingProfile} {h : List ℝ} {y : ℝ} (hy : σ.resp h y = true)
    (i : Fin 2) : G.respValue σ h y i = ((G.share i h.length y - G.offerCost i h.length : ℝ) :
      WithBot ℝ) := by
  simp [respValue, hy]

theorem respValue_reject {σ : BargainingProfile} {h : List ℝ} {y : ℝ} (hy : σ.resp h y = false)
    (i : Fin 2) : G.respValue σ h y i =
      ((-G.offerCost i h.length : ℝ) : WithBot ℝ) + G.value σ (y :: h) i := by
  simp [respValue, hy]

/-- The value from `h` depends only on the moves at histories at least as long as `h`. -/
theorem value_congr {σ σ' : BargainingProfile} {h : List ℝ}
    (hp : ∀ h', h.length ≤ h'.length → σ.prop h' = σ'.prop h')
    (hr : ∀ h' y, h.length ≤ h'.length → σ.resp h' y = σ'.resp h' y) (i : Fin 2) :
    G.value σ h i = G.value σ' h i := by
  have hpath : ∀ t, path σ h t = path σ' h t := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih =>
      rw [path, path, ih, hp _ (by rw [length_path]; omega)]
  unfold value
  congr 1
  · funext k
    rw [hpath, hp _ (by rw [length_path]; omega), hr _ _ (by rw [length_path]; omega)]
  · funext k
    rw [hpath, hp _ (by rw [length_path]; omega)]

theorem setResp_value (σ : BargainingProfile) (h₀ : List ℝ) (y₀ : ℝ) (b : Bool) (i : Fin 2) :
    G.value (setResp σ h₀ y₀ b) (y₀ :: h₀) i = G.value σ (y₀ :: h₀) i := by
  refine G.value_congr (σ := setResp σ h₀ y₀ b) (σ' := σ) (fun _ _ => rfl) (fun h' y hl => ?_) i
  have : h' ≠ h₀ := fun he => by rw [he] at hl; simp at hl
  simp [setResp, this]

theorem setProp_value (σ : BargainingProfile) (h₀ : List ℝ) (y₀ y : ℝ) (i : Fin 2) :
    G.value (setProp σ h₀ y₀) (y :: h₀) i = G.value σ (y :: h₀) i := by
  refine G.value_congr (σ := setProp σ h₀ y₀) (σ' := σ) (fun h' hl => ?_) (fun _ _ _ => rfl) i
  have : h' ≠ h₀ := fun he => by rw [he] at hl; simp at hl
  simp [setProp, this]

/-- **One-stage deviation bound with offer costs.** If `bnd ≥ 0` beyond the horizon, `bnd h`
bounds player `i`'s payoff of an agreement at `h`, and `bnd` covers the offer cost plus `bnd`
at the next node after a rejection, then `bnd` bounds player `i`'s payoff from every node. -/
theorem value_le_of_bound {σ : BargainingProfile} {i : Fin 2} (bnd : List ℝ → ℝ)
    (hnl : ∀ h, ¬ G.Live h.length → 0 ≤ bnd h)
    (hacc : ∀ h, G.Live h.length → σ.resp h (σ.prop h) = true →
      G.share i h.length (σ.prop h) - G.offerCost i h.length ≤ bnd h)
    (hrej : ∀ h, G.Live h.length → σ.resp h (σ.prop h) = false →
      -G.offerCost i h.length + bnd (σ.prop h :: h) ≤ bnd h)
    (h : List ℝ) : G.value σ h i ≤ bnd h := by
  unfold value
  refine firstStop_le (fun k => bnd (path σ h k)) (fun k hk => ?_) (fun k hk => ?_)
  · simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true]
      at hk
    have := hrej (path σ h k) (by rw [length_path]; exact hk.1) hk.2
    rw [length_path] at this
    exact this
  · by_cases hl : G.Live (h.length + k)
    · have hr : σ.resp (path σ h k) (σ.prop (path σ h k)) = true := by
        simpa [hl] using hk
      have := hacc (path σ h k) (by rw [length_path]; exact hl) hr
      rw [length_path] at this
      simp only [hl, ↓reduceIte]
      exact WithBot.coe_le_coe.2 this
    · have := hnl (path σ h k) (by rw [length_path]; exact hl)
      simp only [hl, ↓reduceIte]
      exact WithBot.coe_le_coe.2 this

/-- Offers are feasible: `prop h ∈ [0, v]` at every history. -/
def Feasible (σ : BargainingProfile) : Prop := ∀ h, σ.prop h ∈ Set.Icc 0 G.v

/-- A history of feasible offers. -/
def ValidHist (h : List ℝ) : Prop := ∀ y ∈ h, y ∈ Set.Icc 0 G.v

theorem validHist_cons {h : List ℝ} (hh : G.ValidHist h) {y : ℝ} (hy : y ∈ Set.Icc 0 G.v) :
    G.ValidHist (y :: h) := by
  intro z hz
  rcases List.mem_cons.1 hz with rfl | hz
  · exact hy
  · exact hh z hz

/-- **Definition 9.B.2 for the bargaining game with offer costs** (MWG, pp. 275 and 302-303).
A subgame perfect Nash equilibrium: at every feasible proposal node `h` within the horizon and
at every response node `(h, y)` with `y ∈ [0, v]`, no player gains by deviating to any feasible
strategy. -/
def IsSPNE (σ : BargainingProfile) : Prop :=
  G.Feasible σ ∧ ∀ i σ', G.Feasible σ' → IsDeviation i σ σ' → ∀ h, G.ValidHist h →
    G.Live h.length → G.value σ' h i ≤ G.value σ h i ∧
      ∀ y ∈ Set.Icc 0 G.v, G.respValue σ' h y i ≤ G.respValue σ h y i

/-- In an SPNE the responder accepts an offer that beats her continuation payoff. -/
theorem accept_of_gt {σ : BargainingProfile} (hσ : G.IsSPNE σ) {h : List ℝ}
    (hv : G.ValidHist h) (hl : G.Live h.length) {y : ℝ} (hy : y ∈ Set.Icc 0 G.v)
    (hgt : G.value σ (y :: h) (other (proposer h.length)) < y) : σ.resp h y = true := by
  by_contra hrej
  have hrej' : σ.resp h y = false := by simpa using hrej
  have := (hσ.2 _ (setResp σ h y true) hσ.1 (setResp_isDeviation σ h y true) h hv hl).2 y hy
  rw [G.respValue_accept (by simp [setResp]), G.respValue_reject hrej', share_other,
    offerCost_other] at this
  simp only [sub_zero, neg_zero, WithBot.coe_zero, zero_add] at this
  exact absurd this (not_le.2 hgt)

/-- In an SPNE the responder rejects an offer below her continuation payoff. -/
theorem reject_of_lt {σ : BargainingProfile} (hσ : G.IsSPNE σ) {h : List ℝ}
    (hv : G.ValidHist h) (hl : G.Live h.length) {y : ℝ} (hy : y ∈ Set.Icc 0 G.v)
    (hlt : (y : WithBot ℝ) < G.value σ (y :: h) (other (proposer h.length))) :
    σ.resp h y = false := by
  by_contra hacc
  have hacc' : σ.resp h y = true := by simpa using hacc
  have := (hσ.2 _ (setResp σ h y false) hσ.1 (setResp_isDeviation σ h y false) h hv hl).2 y hy
  rw [G.respValue_reject (by simp [setResp]), G.setResp_value, G.respValue_accept hacc',
    share_other, offerCost_other] at this
  simp only [sub_zero, neg_zero, WithBot.coe_zero, zero_add] at this
  exact absurd this (not_le.2 hlt)

/-- In an SPNE the proposer does at least as well as with any other feasible offer. -/
theorem respValue_le_value {σ : BargainingProfile} (hσ : G.IsSPNE σ) {h : List ℝ}
    (hv : G.ValidHist h) (hl : G.Live h.length) {y : ℝ} (hy : y ∈ Set.Icc 0 G.v) :
    G.respValue σ h y (proposer h.length) ≤ G.value σ h (proposer h.length) := by
  have hf : G.Feasible (setProp σ h y) := by
    intro h'
    simp only [setProp]
    split_ifs
    · exact hy
    · exact hσ.1 h'
  have := (hσ.2 _ _ hf (setProp_isDeviation σ h y) h hv hl).1
  rw [G.value_eq_respValue _ hl] at this
  have hp : (setProp σ h y).prop h = y := by simp [setProp]
  rw [hp] at this
  unfold respValue at this ⊢
  rw [G.setProp_value] at this
  exact this

/-- The threshold profile: in period `n` the proposer offers `a n`; the responder accepts
exactly the offers `y ≥ a n`. -/
noncomputable def threshold (a : ℕ → ℝ) : BargainingProfile where
  prop h := a h.length
  resp h y := decide (a h.length ≤ y)

/-- Payoffs of a threshold profile from a live node: immediate agreement, the proposer gets
`v − c − a n` and the responder `a n`. -/
theorem value_threshold (a : ℕ → ℝ) {h : List ℝ} (hl : G.Live h.length) :
    G.value (threshold a) h (proposer h.length) = ((G.v - G.c - a h.length : ℝ) : WithBot ℝ) ∧
      G.value (threshold a) h (other (proposer h.length)) = ((a h.length : ℝ) : WithBot ℝ) := by
  have hacc : (threshold a).resp h ((threshold a).prop h) = true := by simp [threshold]
  rw [G.value_eq_respValue _ hl, G.value_eq_respValue _ hl, G.respValue_accept hacc,
    G.respValue_accept hacc, share_proposer, share_other, offerCost_proposer, offerCost_other]
  refine ⟨?_, ?_⟩
  · simp only [threshold]
    congr 1
    ring
  · simp [threshold]

/-- **Threshold profiles are SPNE** (MWG, pp. 302-303). If `a n ∈ [0, v]` for all `n`, and in
every live period `a n` is the responder's value as the next proposer (`a n = v − c − a (n + 1)`
if period `n + 1` is live, `a n = 0` in the last period), then `threshold a` is a subgame
perfect Nash equilibrium. -/
theorem threshold_isSPNE {a : ℕ → ℝ} (ha0 : ∀ n, a n ∈ Set.Icc 0 G.v)
    (ha1 : ∀ n, G.Live (n + 1) → a n = G.v - G.c - a (n + 1))
    (ha2 : ∀ n, G.Live n → ¬ G.Live (n + 1) → a n = 0) : G.IsSPNE (threshold a) := by
  classical
  refine ⟨fun h => ha0 h.length, fun i σ' hσ' hdev h hv hl => ?_⟩
  let bnd : List ℝ → ℝ := fun h => if G.Live h.length then
    (if proposer h.length = i then G.v - G.c - a h.length else a h.length) else 0
  have hbnd_val : ∀ h, G.value (threshold a) h i = bnd h := by
    intro h
    simp only [bnd]
    split_ifs with hl' hp
    · rw [← hp]; exact (G.value_threshold a hl').1
    · rcases eq_or_eq_other (proposer h.length) i with h1 | h1
      · exact absurd h1.symm hp
      · rw [h1]; exact (G.value_threshold a hl').2
    · rw [G.value_of_not_live hl']
      rfl
  -- the responder's continuation `bnd (y :: h)` as the next proposer is `a n`
  have hnext : ∀ h y, G.Live h.length → proposer h.length ≠ i → bnd (y :: h) = a h.length := by
    intro h y hl' hp
    have hi : proposer (y :: h).length = i := by
      rcases eq_or_eq_other (proposer h.length) i with h1 | h1
      · exact absurd h1.symm hp
      · rw [List.length_cons, proposer_succ, h1]
    simp only [bnd, hi, ↓reduceIte]
    split_ifs with hl2
    · exact (ha1 _ hl2).symm
    · exact (ha2 _ hl' hl2).symm
  have hnext' : ∀ h y, G.Live h.length → proposer h.length = i →
      bnd (y :: h) = if G.Live (h.length + 1) then a (h.length + 1) else 0 := by
    intro h y _ hp
    have hi : proposer (h.length + 1) ≠ i := by
      rw [proposer_succ, hp]
      exact other_ne i
    simp only [bnd, List.length_cons, hi, ↓reduceIte]
  have hbound : ∀ h, G.value σ' h i ≤ bnd h := by
    refine G.value_le_of_bound bnd (fun h hl' => by simp [bnd, hl']) (fun h' hl' hr => ?_)
      (fun h' hl' hr => ?_)
    · by_cases hp : proposer h'.length = i
      · have hr' := hdev.2 h' (σ'.prop h') hp
        rw [hr] at hr'
        have hle : a h'.length ≤ σ'.prop h' := by simpa [threshold] using hr'.symm
        subst hp
        rw [share_proposer, offerCost_proposer]
        simp only [bnd, hl', ↓reduceIte]
        linarith
      · have hpr := hdev.1 h' hp
        rcases eq_or_eq_other (proposer h'.length) i with h1 | h1
        · exact absurd h1.symm hp
        · subst h1
          rw [share_other, offerCost_other, hpr]
          simp only [bnd, hl', hp, ↓reduceIte, threshold]
          linarith
    · by_cases hp : proposer h'.length = i
      · rw [hnext' h' _ hl' hp]
        have hle := (ha0 h'.length).2
        subst hp
        rw [offerCost_proposer]
        simp only [bnd, hl', ↓reduceIte]
        have hc := G.c_pos
        split_ifs with hl2
        · rw [ha1 _ hl2]; linarith
        · linarith
      · rw [hnext h' _ hl' hp]
        rcases eq_or_eq_other (proposer h'.length) i with h1 | h1
        · exact absurd h1.symm hp
        · subst h1
          rw [offerCost_other]
          simp only [bnd, hl', hp, ↓reduceIte]
          linarith
  refine ⟨by rw [hbnd_val]; exact hbound h, fun y hy => ?_⟩
  by_cases hp : proposer h.length = i
  · have hr' := hdev.2 h y hp
    cases hry : (threshold a).resp h y with
    | true =>
      rw [G.respValue_accept hry, G.respValue_accept (hr'.trans hry)]
    | false =>
      rw [G.respValue_reject hry, G.respValue_reject (hr'.trans hry), hbnd_val]
      gcongr
      exact hbound _
  · have hB := hnext h y hl hp
    rcases eq_or_eq_other (proposer h.length) i with h1 | h1
    · exact absurd h1.symm hp
    · subst h1
      have hσ'v : G.value σ' (y :: h) (other (proposer h.length)) ≤ a h.length := by
        rw [← hB]; exact hbound _
      have hthr : (y : WithBot ℝ) ≤ G.respValue (threshold a) h y (other (proposer h.length)) ∧
          ((a h.length : ℝ) : WithBot ℝ) ≤
            G.respValue (threshold a) h y (other (proposer h.length)) := by
        cases hry : (threshold a).resp h y with
        | true =>
          rw [G.respValue_accept hry, share_other, offerCost_other, sub_zero]
          have : a h.length ≤ y := by simpa [threshold] using hry
          exact ⟨le_rfl, WithBot.coe_le_coe.2 this⟩
        | false =>
          rw [G.respValue_reject hry, offerCost_other, hbnd_val, hB, neg_zero, WithBot.coe_zero,
            zero_add]
          have : y < a h.length := by simpa [threshold] using hry
          exact ⟨WithBot.coe_le_coe.2 this.le, le_rfl⟩
      cases hry : σ'.resp h y with
      | true =>
        rw [G.respValue_accept hry, share_other, offerCost_other, sub_zero]
        exact hthr.1
      | false =>
        rw [G.respValue_reject hry, offerCost_other, neg_zero, WithBot.coe_zero, zero_add]
        exact hσ'v.trans hthr.2

/-- **SPNE strategies at a node are determined by the continuation values.** In an SPNE, if
after every feasible offer at the live node `h` the responder's continuation value (as the
next proposer) is `X ∈ [0, v]` and the proposer's is `Y ≥ 0`, with `X + Y < v`, then the
proposer offers exactly `X`, the responder accepts exactly the offers `y ≥ X` (indifference
included), and the payoffs from `h` are `v − c − X` and `X`. -/
theorem strategies_determined {σ : BargainingProfile} (hσ : G.IsSPNE σ) {h : List ℝ}
    (hv : G.ValidHist h) (hl : G.Live h.length) {X Y : ℝ} (hX : X ∈ Set.Icc 0 G.v)
    (hY : 0 ≤ Y) (hXY : X + Y < G.v)
    (hcr : ∀ y ∈ Set.Icc 0 G.v, G.value σ (y :: h) (other (proposer h.length)) = X)
    (hcp : ∀ y ∈ Set.Icc 0 G.v, G.value σ (y :: h) (proposer h.length) = Y) :
    σ.prop h = X ∧ (∀ y ∈ Set.Icc 0 G.v, σ.resp h y = decide (X ≤ y)) ∧
      G.value σ h (proposer h.length) = ((G.v - G.c - X : ℝ) : WithBot ℝ) ∧
      G.value σ h (other (proposer h.length)) = (X : WithBot ℝ) := by
  set p := proposer h.length
  set r := other p
  have hc := G.c_pos
  have hgt : ∀ y ∈ Set.Icc 0 G.v, X < y → σ.resp h y = true := fun y hy hxy =>
    G.accept_of_gt hσ hv hl hy (by rw [hcr y hy]; exact WithBot.coe_lt_coe.2 hxy)
  have hlt : ∀ y ∈ Set.Icc 0 G.v, y < X → σ.resp h y = false := fun y hy hxy =>
    G.reject_of_lt hσ hv hl hy (by rw [hcr y hy]; exact WithBot.coe_lt_coe.2 hxy)
  set y₀ := σ.prop h
  have hy₀ : y₀ ∈ Set.Icc 0 G.v := hσ.1 h
  -- the proposer's payoff is a real number `V`
  set V : ℝ := if σ.resp h y₀ = true then G.v - y₀ - G.c else Y - G.c with hVdef
  have hval : G.value σ h p = (V : WithBot ℝ) := by
    rw [G.value_eq_respValue σ hl]
    cases hr : σ.resp h y₀ with
    | true =>
      rw [G.respValue_accept hr, share_proposer, offerCost_proposer]
      simp only [hVdef, hr, ↓reduceIte]
    | false =>
      rw [G.respValue_reject hr, offerCost_proposer, hcp y₀ hy₀, ← WithBot.coe_add]
      simp only [hVdef, hr, Bool.false_eq_true, ↓reduceIte]
      congr 1
      ring
  have hdev : ∀ y ∈ Set.Icc 0 G.v, σ.resp h y = true → G.v - y - G.c ≤ V := by
    intro y hy hr
    have := G.respValue_le_value hσ hv hl hy
    rw [G.respValue_accept hr, share_proposer, offerCost_proposer, hval] at this
    exact WithBot.coe_le_coe.1 this
  have hVlow : X - G.v - G.c ≤ V := by
    simp only [hVdef]
    split_ifs <;> linarith [hX.1, hX.2, hy₀.1, hy₀.2]
  -- indifference: the responder accepts `X`
  have hXacc : σ.resp h X = true := by
    by_contra hrej
    have hrej' : σ.resp h X = false := by simpa using hrej
    have hVlt : V < G.v - G.c - X := by
      simp only [hVdef]
      split_ifs with hr
      · have hge : X ≤ y₀ := by
          by_contra hlt'
          rw [hlt y₀ hy₀ (not_le.1 hlt')] at hr
          exact Bool.noConfusion hr
        have hne : y₀ ≠ X := fun he => by rw [he, hrej'] at hr; exact Bool.noConfusion hr
        have := lt_of_le_of_ne hge (Ne.symm hne)
        linarith
      · linarith
    set y := X + (G.v - G.c - X - V) / 2
    have hy : y ∈ Set.Icc 0 G.v := ⟨by simp only [y]; linarith [hX.1],
      by simp only [y]; linarith [hX.2]⟩
    have := hdev y hy (hgt y hy (by simp only [y]; linarith))
    simp only [y] at this
    linarith
  have hXdev := hdev X hX hXacc
  have hprop : y₀ = X := by
    cases hr : σ.resp h y₀ with
    | true =>
      have hge : X ≤ y₀ := by
        by_contra hlt'
        rw [hlt y₀ hy₀ (not_le.1 hlt')] at hr
        exact Bool.noConfusion hr
      simp only [hVdef, hr, ↓reduceIte] at hXdev
      linarith
    | false =>
      simp only [hVdef, hr, Bool.false_eq_true, ↓reduceIte] at hXdev
      linarith
  refine ⟨hprop, fun y hy => ?_, ?_, ?_⟩
  · rcases lt_trichotomy y X with hyX | hyX | hyX
    · rw [hlt y hy hyX]; simp [not_le.2 hyX]
    · rw [hyX, hXacc]; simp
    · rw [hgt y hy hyX]; simp [hyX.le]
  · rw [G.value_eq_respValue σ hl, show σ.prop h = X from hprop, G.respValue_accept hXacc,
      share_proposer, offerCost_proposer]
    congr 1
    ring
  · rw [G.value_eq_respValue σ hl, show σ.prop h = X from hprop, G.respValue_accept hXacc,
      share_other, offerCost_other, sub_zero]

/-- The upper bounds on payoffs for any feasible profile: at most `v − c` for a player who
proposes at `h` and at most `v` for the responder. -/
theorem value_le_feasible {σ : BargainingProfile} (hσ : G.Feasible σ) (i : Fin 2)
    (h : List ℝ) : G.value σ h i ≤ ((if proposer h.length = i then G.v - G.c else G.v : ℝ) :
      WithBot ℝ) := by
  have hc := G.c_pos
  have hcv := G.c_lt_v
  refine G.value_le_of_bound (fun h => if proposer h.length = i then G.v - G.c else G.v)
    (fun h _ => by split_ifs <;> linarith) (fun h' _ _ => ?_) (fun h' _ _ => ?_) h
  · have hy := hσ h'
    by_cases hp : proposer h'.length = i
    · subst hp
      rw [share_proposer, offerCost_proposer]
      simp only [↓reduceIte]
      linarith [hy.1]
    · rcases eq_or_eq_other (proposer h'.length) i with h1 | h1
      · exact absurd h1.symm hp
      · subst h1
        rw [share_other, offerCost_other]
        simp only [hp, ↓reduceIte]
        linarith [hy.2]
  · by_cases hp : proposer h'.length = i
    · have hn : proposer (σ.prop h' :: h').length ≠ i := by
        rw [List.length_cons, proposer_succ, hp]; exact other_ne i
      subst hp
      rw [offerCost_proposer]
      simp only [hn, ↓reduceIte]
      linarith
    · have hn : proposer (σ.prop h' :: h').length = i := by
        rcases eq_or_eq_other (proposer h'.length) i with h1 | h1
        · exact absurd h1.symm hp
        · rw [List.length_cons, proposer_succ, h1]
      rcases eq_or_eq_other (proposer h'.length) i with h1 | h1
      · exact absurd h1.symm hp
      · rw [hn]
        subst h1
        rw [offerCost_other]
        simp only [hp, ↓reduceIte]
        linarith

theorem offerCost_add (n : ℕ) : G.offerCost 0 n + G.offerCost 1 n = G.c := by
  unfold offerCost
  rcases Fin.exists_fin_two.1 ⟨proposer n, rfl⟩ with h | h <;> simp [h]

theorem share_add (n : ℕ) (y : ℝ) : G.share 0 n y + G.share 1 n y = G.v := by
  unfold share
  rcases Fin.exists_fin_two.1 ⟨proposer n, rfl⟩ with h | h <;> simp [h]

/-- The two players' payoffs add up to at most `v − c`: an agreement divides `v`, and at least
one offer is made. -/
theorem value_add_le {σ : BargainingProfile} (h : List ℝ) :
    G.value σ h 0 + G.value σ h 1 ≤ ((G.v - G.c : ℝ) : WithBot ℝ) := by
  have hc := G.c_pos
  have hcv := G.c_lt_v
  unfold value
  rw [firstStop_add]
  refine firstStop_le (fun _ => G.v - G.c) (fun k _ => ?_) (fun k _ => ?_)
  · have := G.offerCost_add (h.length + k)
    linarith
  · split_ifs
    · rw [← WithBot.coe_add]
      refine WithBot.coe_le_coe.2 (le_of_eq ?_)
      have h1 := G.offerCost_add (h.length + k)
      have h2 := G.share_add (h.length + k) (σ.prop (path σ h k))
      linarith
    · simp only [add_zero]
      exact WithBot.coe_le_coe.2 (by linarith)

/-- **SPNE payoffs are nonnegative.** In an SPNE, at every live feasible node, the proposer's
and the responder's payoffs are real numbers `a, b ≥ 0` with `a + b ≤ v − c`. -/
theorem spne_bounds {σ : BargainingProfile} (hσ : G.IsSPNE σ) :
    ∀ h, G.ValidHist h → G.Live h.length → ∃ a b : ℝ,
      G.value σ h (proposer h.length) = a ∧ G.value σ h (other (proposer h.length)) = b ∧
        0 ≤ a ∧ 0 ≤ b ∧ a + b ≤ G.v - G.c := by
  have hc := G.c_pos
  have hcv := G.c_lt_v
  -- the proposer's payoff is at least `0`
  have hprop : ∀ h, G.ValidHist h → G.Live h.length →
      ∃ a : ℝ, G.value σ h (proposer h.length) = a ∧ 0 ≤ a := by
    intro h hv hl
    have hlow : ∀ y ∈ Set.Ioc (G.v - G.c) G.v,
        ((G.v - y - G.c : ℝ) : WithBot ℝ) ≤ G.value σ h (proposer h.length) := by
      intro y hy
      have hy' : y ∈ Set.Icc 0 G.v := ⟨by linarith [hy.1], hy.2⟩
      have hub := G.value_le_feasible hσ.1 (other (proposer h.length)) (y :: h)
      rw [List.length_cons, proposer_succ] at hub
      simp only [↓reduceIte] at hub
      have hacc := G.accept_of_gt hσ hv hl hy'
        (lt_of_le_of_lt hub (WithBot.coe_lt_coe.2 hy.1))
      have := G.respValue_le_value hσ hv hl hy'
      rw [G.respValue_accept hacc, share_proposer, offerCost_proposer] at this
      exact this
    have hne : G.value σ h (proposer h.length) ≠ ⊥ :=
      ne_bot_of_le_ne_bot (WithBot.coe_ne_bot) (hlow G.v ⟨by linarith, le_rfl⟩)
    obtain ⟨x, hx⟩ := WithBot.ne_bot_iff_exists.1 hne
    refine ⟨x, hx.symm, ?_⟩
    have hx1 := hlow G.v ⟨by linarith, le_rfl⟩
    rw [← hx] at hx1
    replace hx1 : G.v - G.v - G.c ≤ x := WithBot.coe_le_coe.1 hx1
    by_contra hneg
    push Not at hneg
    have := hlow (G.v - G.c - x / 2) ⟨by linarith, by linarith⟩
    rw [← hx] at this
    replace this : G.v - (G.v - G.c - x / 2) - G.c ≤ x := WithBot.coe_le_coe.1 this
    linarith
  intro h hv hl
  obtain ⟨a, ha, ha0⟩ := hprop h hv hl
  -- the responder's payoff is at least `0`
  have hresp : ∃ b : ℝ, G.value σ h (other (proposer h.length)) = b ∧ 0 ≤ b := by
    have hy₀ := hσ.1 h
    rw [G.value_eq_respValue σ hl]
    cases hr : σ.resp h (σ.prop h) with
    | true =>
      rw [G.respValue_accept hr, share_other, offerCost_other, sub_zero]
      exact ⟨_, rfl, hy₀.1⟩
    | false =>
      rw [G.respValue_reject hr, offerCost_other, neg_zero, WithBot.coe_zero, zero_add]
      by_cases hl2 : G.Live (σ.prop h :: h).length
      · obtain ⟨b, hb, hb0⟩ := hprop _ (G.validHist_cons hv hy₀) hl2
        rw [List.length_cons, proposer_succ] at hb
        exact ⟨b, hb, hb0⟩
      · exact ⟨0, G.value_of_not_live hl2 _, le_rfl⟩
  obtain ⟨b, hb, hb0⟩ := hresp
  refine ⟨a, b, ha, hb, ha0, hb0, ?_⟩
  have hsum := G.value_add_le (σ := σ) h
  rcases Fin.exists_fin_two.1 ⟨proposer h.length, rfl⟩ with hp | hp
  · have h1 : other (proposer h.length) = 1 := by rw [hp]; rfl
    rw [← hp, ha, ← h1, hb, ← WithBot.coe_add] at hsum
    exact WithBot.coe_le_coe.1 hsum
  · have h1 : other (proposer h.length) = 0 := by rw [hp]; rfl
    rw [← hp, ha, ← h1, hb, ← WithBot.coe_add, add_comm b a] at hsum
    · exact WithBot.coe_le_coe.1 hsum

/-- The proposer's SPNE payoff with `k` periods left in the finite game of Exercise 9.B.7:
`v − c` if `k` is odd and `0` if `k` is even. -/
def W (k : ℕ) : ℝ := if k % 2 = 1 then G.v - G.c else 0

theorem W_zero : G.W 0 = 0 := by simp [W]

theorem W_succ (k : ℕ) : G.W (k + 1) = G.v - G.c - G.W k := by
  unfold W
  rcases Nat.mod_two_eq_zero_or_one k with h | h
  · have : (k + 1) % 2 = 1 := by omega
    simp [h, this]
  · have : (k + 1) % 2 = 0 := by omega
    simp [h, this]

theorem W_mem (k : ℕ) : G.W k ∈ Set.Icc 0 G.v := by
  have hc := G.c_pos
  have hcv := G.c_lt_v
  unfold W
  split_ifs <;> constructor <;> linarith

theorem W_add_pred (k : ℕ) : G.W k + G.W (k - 1) ≤ G.v - G.c := by
  have hcv := G.c_lt_v
  cases k with
  | zero => rw [W_zero]; simp; linarith
  | succ k => rw [W_succ]; simp

theorem live_iff {N : ℕ} (hT : G.T = N) (n : ℕ) : G.Live n ↔ n < N := by
  simp [Live, hT]

/-- **Exercise 9.B.7: the SPNE payoffs** (MWG, p. 302). In every SPNE of the `N`-period game, at
every feasible node with `m` periods left, the proposer earns `W m` and the responder
`W (m − 1)`. -/
theorem exercise_9_B_7_values {N : ℕ} (hT : G.T = N) {σ : BargainingProfile}
    (hσ : G.IsSPNE σ) : ∀ m h, G.ValidHist h → h.length + m = N →
      G.value σ h (proposer h.length) = (G.W m : WithBot ℝ) ∧
        G.value σ h (other (proposer h.length)) = (G.W (m - 1) : WithBot ℝ) := by
  intro m
  induction m with
  | zero =>
    intro h _ hN
    have hl : ¬ G.Live h.length := by rw [G.live_iff hT]; omega
    rw [G.value_of_not_live hl, G.value_of_not_live hl, Nat.zero_sub, W_zero]
    simp
  | succ m ih =>
    intro h hv hN
    have hl : G.Live h.length := by rw [G.live_iff hT]; omega
    have hcont : ∀ y ∈ Set.Icc 0 G.v,
        G.value σ (y :: h) (other (proposer h.length)) = (G.W m : WithBot ℝ) ∧
          G.value σ (y :: h) (proposer h.length) = (G.W (m - 1) : WithBot ℝ) := by
      intro y hy
      have := ih (y :: h) (G.validHist_cons hv hy) (by simp; omega)
      rw [List.length_cons, proposer_succ, other_other] at this
      exact this
    have hcv := G.c_lt_v
    have hc := G.c_pos
    have hd := G.strategies_determined hσ hv hl (G.W_mem m) (G.W_mem (m - 1)).1
      (by linarith [G.W_add_pred m]) (fun y hy => (hcont y hy).1) (fun y hy => (hcont y hy).2)
    refine ⟨?_, ?_⟩
    · rw [hd.2.2.1, W_succ]
    · rw [hd.2.2.2, Nat.add_sub_cancel]

/-- **Exercise 9.B.7** (MWG, p. 302). The `N`-period alternating-offer game with offer cost
`c ∈ (0, v)` and no discounting has a unique SPNE: at every feasible node of period `n < N`
(so `m = N − n` periods are left) the proposer offers `W (m − 1)` and the responder accepts
exactly the offers `y ≥ W (m − 1)` (including at indifference), where `W k` is `v − c` for odd
`k` and `0` for even `k`. Agreement is immediate; player 1 (index `0`) earns `W N` and player
2 earns `W (N − 1)`. -/
theorem exercise_9_B_7 {N : ℕ} (hT : G.T = N) :
    G.IsSPNE (threshold (fun n => G.W (N - n - 1))) ∧
      ∀ σ, G.IsSPNE σ → (∀ h, G.ValidHist h → h.length < N →
        σ.prop h = G.W (N - h.length - 1) ∧
          ∀ y ∈ Set.Icc 0 G.v, σ.resp h y = decide (G.W (N - h.length - 1) ≤ y)) ∧
        G.value σ [] 0 = (G.W N : WithBot ℝ) ∧ G.value σ [] 1 = (G.W (N - 1) : WithBot ℝ) := by
  have hcv := G.c_lt_v
  refine ⟨G.threshold_isSPNE (fun n => G.W_mem _) (fun n hn => ?_) (fun n hn hn' => ?_),
    fun σ hσ => ⟨fun h hv hl => ?_, ?_⟩⟩
  · rw [G.live_iff hT] at hn
    rw [show N - n - 1 = (N - (n + 1) - 1) + 1 by omega, W_succ]
  · rw [G.live_iff hT] at hn hn'
    rw [show N - n - 1 = 0 by omega, W_zero]
  · have hl' : G.Live h.length := by rw [G.live_iff hT]; exact hl
    have hcont : ∀ y ∈ Set.Icc 0 G.v,
        G.value σ (y :: h) (other (proposer h.length)) = (G.W (N - h.length - 1) : WithBot ℝ) ∧
          G.value σ (y :: h) (proposer h.length) =
            (G.W (N - h.length - 1 - 1) : WithBot ℝ) := by
      intro y hy
      have := G.exercise_9_B_7_values hT hσ (N - h.length - 1) (y :: h)
        (G.validHist_cons hv hy) (by simp; omega)
      rw [List.length_cons, proposer_succ, other_other] at this
      exact this
    have hc := G.c_pos
    have hd := G.strategies_determined hσ hv hl' (G.W_mem _) (G.W_mem _).1
      (by linarith [G.W_add_pred (N - h.length - 1)]) (fun y hy => (hcont y hy).1)
      (fun y hy => (hcont y hy).2)
    exact ⟨hd.1, hd.2.1⟩
  · have := G.exercise_9_B_7_values hT hσ N [] (fun _ h => by simp at h) (by simp)
    exact this

/-- **Exercise 9.B.7: parity** (MWG, p. 302). With `N` periods, player 1's SPNE payoff is
`v − c` and player 2's is `0` if `N` is odd; if `N ≥ 2` is even they are `0` and `v − c`. -/
theorem exercise_9_B_7_parity {N : ℕ} (hT : G.T = N) {σ : BargainingProfile}
    (hσ : G.IsSPNE σ) :
    (N % 2 = 1 → G.value σ [] 0 = ((G.v - G.c : ℝ) : WithBot ℝ) ∧ G.value σ [] 1 = 0) ∧
      (N % 2 = 0 → 2 ≤ N →
        G.value σ [] 0 = 0 ∧ G.value σ [] 1 = ((G.v - G.c : ℝ) : WithBot ℝ)) := by
  have h := (G.exercise_9_B_7 hT).2 σ hσ
  refine ⟨fun hN => ?_, fun hN hN2 => ?_⟩
  · rw [h.2.1, h.2.2]
    have : (N - 1) % 2 = 0 := by omega
    simp [W, hN, this]
  · rw [h.2.1, h.2.2]
    have : (N - 1) % 2 = 1 := by omega
    simp [W, hN, this]

open Filter Topology in
/-- **Exercise 9.B.7: no limit as `T → ∞`** (MWG, p. 302). Player 1's SPNE payoff `W T`
alternates between `v − c` (odd `T`) and `0` (even `T`), so it has no limit. -/
theorem exercise_9_B_7_limit : ¬ ∃ L, Tendsto G.W atTop (𝓝 L) := by
  rintro ⟨L, hL⟩
  have hcv := G.c_lt_v
  have h2 : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨b, fun a ha => by omega⟩
  have h2' : Tendsto (fun n : ℕ => 2 * n + 1) atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨b, fun a ha => by omega⟩
  have he : (G.W ∘ fun n : ℕ => 2 * n) = fun _ => 0 := by
    funext n; simp [W]
  have ho : (G.W ∘ fun n : ℕ => 2 * n + 1) = fun _ => G.v - G.c := by
    funext n; simp [W, Nat.add_mod]
  have l0 := hL.comp h2
  have l1 := hL.comp h2'
  rw [he] at l0
  rw [ho] at l1
  have := tendsto_nhds_unique (tendsto_const_nhds (x := (0 : ℝ))) l0
  have := tendsto_nhds_unique (tendsto_const_nhds (x := G.v - G.c)) l1
  linarith

theorem live_top (hT : G.T = ⊤) (n : ℕ) : G.Live n := by
  simp [Live, hT]

/-- The stationary split profile of the infinite game: player 1 (index `0`, proposing in even
periods) offers `v − c − a`, player 2 offers `a`; each accepts exactly the offers of at least
her own value as the next proposer. -/
noncomputable def splitProfile (a : ℝ) : BargainingProfile :=
  threshold (fun n => if n % 2 = 0 then G.v - G.c - a else a)

/-- **Exercise 9.B.13: every split is an SPNE outcome** (MWG, p. 303). In the infinite game,
for every `a ∈ [0, v − c]` the split profile is an SPNE with immediate agreement, giving
player 1 the payoff `a` and player 2 the payoff `v − c − a`. -/
theorem splitProfile_isSPNE (hT : G.T = ⊤) {a : ℝ} (ha : a ∈ Set.Icc 0 (G.v - G.c)) :
    G.IsSPNE (G.splitProfile a) ∧ G.value (G.splitProfile a) [] 0 = (a : WithBot ℝ) ∧
      G.value (G.splitProfile a) [] 1 = ((G.v - G.c - a : ℝ) : WithBot ℝ) ∧
      (G.splitProfile a).resp [] ((G.splitProfile a).prop []) = true := by
  have hc := G.c_pos
  refine ⟨G.threshold_isSPNE (fun n => ?_) (fun n _ => ?_) (fun n _ hn => absurd (G.live_top hT
    (n + 1)) hn), ?_, ?_, ?_⟩
  · split_ifs <;> constructor <;> linarith [ha.1, ha.2]
  · rcases Nat.mod_two_eq_zero_or_one n with h | h
    · have : (n + 1) % 2 = 1 := by omega
      simp [h, this]
    · have : (n + 1) % 2 = 0 := by omega
      simp [h, this]
  · have := (G.value_threshold (fun n => if n % 2 = 0 then G.v - G.c - a else a)
      (h := []) (G.live_top hT 0)).1
    simp only [List.length_nil, Nat.zero_mod, ↓reduceIte, sub_sub_cancel] at this
    exact this
  · exact (G.value_threshold (fun n => if n % 2 = 0 then G.v - G.c - a else a)
      (h := []) (G.live_top hT 0)).2
  · simp [splitProfile, threshold]

/-- **Exercise 9.B.13** (MWG, p. 303). The infinite horizon game with offer cost `c ∈ (0, v)`
and no discounting. (1) In every SPNE the payoffs `a` of player 1 and `b` of player 2 are real
numbers with `a, b ≥ 0` and `a + b ≤ v − c` (`spne_bounds`: the same holds in every subgame).
(2) Conversely, for every `a ∈ [0, v − c]` there is an SPNE with immediate agreement and payoffs
`(a, v − c − a)` (`splitProfile_isSPNE`). -/
theorem exercise_9_B_13 (hT : G.T = ⊤) :
    (∀ σ, G.IsSPNE σ → ∃ a b : ℝ, G.value σ [] 0 = a ∧ G.value σ [] 1 = b ∧ 0 ≤ a ∧ 0 ≤ b ∧
      a + b ≤ G.v - G.c) ∧
    ∀ a ∈ Set.Icc 0 (G.v - G.c), ∃ σ, G.IsSPNE σ ∧ G.value σ [] 0 = (a : WithBot ℝ) ∧
      G.value σ [] 1 = ((G.v - G.c - a : ℝ) : WithBot ℝ) ∧ σ.resp [] (σ.prop []) = true := by
  refine ⟨fun σ hσ => ?_, fun a ha => ⟨_, G.splitProfile_isSPNE hT ha⟩⟩
  exact G.spne_bounds hσ [] (fun _ h => by simp at h) (G.live_top hT 0)

/-- **Exercise 9.B.13: player 1's SPNE payoffs** (MWG, p. 303). In the infinite game the set of
player 1's SPNE payoffs is exactly `[0, v − c]`; so is player 2's. -/
theorem exercise_9_B_13_payoffs (hT : G.T = ⊤) :
    {x : ℝ | ∃ σ, G.IsSPNE σ ∧ G.value σ [] 0 = (x : WithBot ℝ)} = Set.Icc 0 (G.v - G.c) ∧
      {x : ℝ | ∃ σ, G.IsSPNE σ ∧ G.value σ [] 1 = (x : WithBot ℝ)} =
        Set.Icc 0 (G.v - G.c) := by
  refine ⟨Set.ext fun x => ⟨fun ⟨σ, hσ, hx⟩ => ?_, fun hx => ?_⟩,
    Set.ext fun x => ⟨fun ⟨σ, hσ, hx⟩ => ?_, fun hx => ?_⟩⟩
  · obtain ⟨a, b, ha, _, ha0, hb0, hab⟩ := (G.exercise_9_B_13 hT).1 σ hσ
    rw [ha] at hx
    have := WithBot.coe_injective hx
    subst this
    exact ⟨ha0, by linarith⟩
  · exact ⟨_, (G.splitProfile_isSPNE hT hx).1, (G.splitProfile_isSPNE hT hx).2.1⟩
  · obtain ⟨a, b, _, hb, ha0, hb0, hab⟩ := (G.exercise_9_B_13 hT).1 σ hσ
    rw [hb] at hx
    have := WithBot.coe_injective hx
    subst this
    exact ⟨hb0, by linarith⟩
  · have hx' : G.v - G.c - x ∈ Set.Icc 0 (G.v - G.c) := ⟨by linarith [hx.2], by linarith [hx.1]⟩
    refine ⟨_, (G.splitProfile_isSPNE hT hx').1, ?_⟩
    rw [(G.splitProfile_isSPNE hT hx').2.2.1]
    congr 1
    ring

/-- **Exercise 9.B.13: the SPNE is not unique** (MWG, p. 303): in the infinite game there are
SPNE giving player 1 the payoffs `0` and `v − c > 0`. -/
theorem exercise_9_B_13_not_unique (hT : G.T = ⊤) :
    ∃ σ₁ σ₂, G.IsSPNE σ₁ ∧ G.IsSPNE σ₂ ∧ G.value σ₁ [] 0 ≠ G.value σ₂ [] 0 := by
  have hcv := G.c_lt_v
  have h0 := G.splitProfile_isSPNE hT (a := 0) ⟨le_rfl, by linarith⟩
  have h1 := G.splitProfile_isSPNE hT (a := G.v - G.c) ⟨by linarith, le_rfl⟩
  refine ⟨_, _, h0.1, h1.1, ?_⟩
  rw [h0.2.1, h1.2.1]
  intro he
  have := WithBot.coe_injective he
  linarith

/-- **Exercise 9.B.13: immediate agreement when `v < 2c`** (MWG, p. 303). If `v < 2c`, then in
every SPNE (of any horizon) the offer made at every live feasible node is accepted: after a
rejection the two payoffs add up to at most `v − c`, so the first proposer would get at most
`v − 2c < 0`. -/
theorem spne_immediate {σ : BargainingProfile} (hσ : G.IsSPNE σ) {h : List ℝ}
    (hv : G.ValidHist h) (hl : G.Live h.length) (hc2 : G.v < 2 * G.c) :
    σ.resp h (σ.prop h) = true := by
  by_contra hr
  have hr' : σ.resp h (σ.prop h) = false := by simpa using hr
  have hc := G.c_pos
  obtain ⟨a, b, ha, _, ha0, _, _⟩ := G.spne_bounds hσ h hv hl
  have h1 := G.value_eq_respValue σ hl (proposer h.length)
  rw [G.respValue_reject hr', offerCost_proposer, ha] at h1
  have hy₀ := hσ.1 h
  by_cases hl2 : G.Live (σ.prop h :: h).length
  · obtain ⟨a', b', _, hb', ha0', _, hab'⟩ :=
      G.spne_bounds hσ _ (G.validHist_cons hv hy₀) hl2
    rw [List.length_cons, proposer_succ, other_other] at hb'
    rw [hb', ← WithBot.coe_add] at h1
    have := WithBot.coe_injective h1
    linarith
  · rw [G.value_of_not_live hl2, ← WithBot.coe_zero, ← WithBot.coe_add] at h1
    have := WithBot.coe_injective h1
    linarith

/-- **One-stage deviation principle with offer costs.** A feasible profile `σ` is an SPNE if
its payoffs are given by real numbers `Vf h i` and at every live node no one-stage deviation
pays: the proposer cannot gain by any offer (given the responses and `Vf` afterwards), and the
responder accepts only offers of at least her `Vf` after rejection and rejects only offers of
at most it. -/
theorem isSPNE_of_oneStage {σ : BargainingProfile} (hF : G.Feasible σ)
    (Vf : List ℝ → Fin 2 → ℝ) (hval : ∀ h i, G.value σ h i = (Vf h i : WithBot ℝ))
    (hP : ∀ h, G.Live h.length → ∀ y ∈ Set.Icc 0 G.v,
      (if σ.resp h y = true then G.v - y - G.c else -G.c + Vf (y :: h) (proposer h.length)) ≤
        Vf h (proposer h.length))
    (hRa : ∀ h, G.Live h.length → ∀ y ∈ Set.Icc 0 G.v, σ.resp h y = true →
      Vf (y :: h) (other (proposer h.length)) ≤ y)
    (hRr : ∀ h, G.Live h.length → ∀ y ∈ Set.Icc 0 G.v, σ.resp h y = false →
      y ≤ Vf (y :: h) (other (proposer h.length))) : G.IsSPNE σ := by
  refine ⟨hF, fun i σ' hσ' hdev h _ hl => ?_⟩
  -- the responder's `Vf` dominates both the offer and the continuation
  have hresp : ∀ h, G.Live h.length → ∀ y ∈ Set.Icc 0 G.v,
      y ≤ (G.respValue σ h y (other (proposer h.length))) ∧
      (Vf (y :: h) (other (proposer h.length)) : WithBot ℝ) ≤
        G.respValue σ h y (other (proposer h.length)) := by
    intro h hl y hy
    cases hr : σ.resp h y with
    | true =>
      rw [G.respValue_accept hr, share_other, offerCost_other, sub_zero]
      exact ⟨le_rfl, WithBot.coe_le_coe.2 (hRa h hl y hy hr)⟩
    | false =>
      rw [G.respValue_reject hr, offerCost_other, neg_zero, WithBot.coe_zero, zero_add, hval]
      exact ⟨WithBot.coe_le_coe.2 (hRr h hl y hy hr), le_rfl⟩
  have hVr' : ∀ h, G.Live h.length →
      σ.prop h ≤ Vf h (other (proposer h.length)) ∧
        Vf (σ.prop h :: h) (other (proposer h.length)) ≤ Vf h (other (proposer h.length)) := by
    intro h hl
    have := hresp h hl (σ.prop h) (hF h)
    rw [← G.value_eq_respValue σ hl, hval] at this
    exact ⟨WithBot.coe_le_coe.1 this.1, WithBot.coe_le_coe.1 this.2⟩
  have hbound : ∀ h, G.value σ' h i ≤ (Vf h i : WithBot ℝ) := by
    refine G.value_le_of_bound (fun h => Vf h i) (fun h hl' => ?_) (fun h' hl' hr => ?_)
      (fun h' hl' hr => ?_)
    · have := hval h i
      rw [G.value_of_not_live hl'] at this
      exact (WithBot.coe_eq_zero.1 this.symm).ge
    · by_cases hp : proposer h'.length = i
      · have hr' : σ.resp h' (σ'.prop h') = true := (hdev.2 h' _ hp).symm.trans hr
        have := hP h' hl' _ (hσ' h')
        rw [hr'] at this
        subst hp
        rw [share_proposer, offerCost_proposer]
        simpa using this
      · rcases eq_or_eq_other (proposer h'.length) i with h1 | h1
        · exact absurd h1.symm hp
        · subst h1
          rw [share_other, offerCost_other, sub_zero, hdev.1 h' hp]
          exact (hVr' h' hl').1
    · by_cases hp : proposer h'.length = i
      · have hr' : σ.resp h' (σ'.prop h') = false := (hdev.2 h' _ hp).symm.trans hr
        have := hP h' hl' _ (hσ' h')
        rw [hr'] at this
        subst hp
        rw [offerCost_proposer]
        simpa using this
      · rcases eq_or_eq_other (proposer h'.length) i with h1 | h1
        · exact absurd h1.symm hp
        · subst h1
          rw [offerCost_other, neg_zero, zero_add, hdev.1 h' hp]
          exact (hVr' h' hl').2
  refine ⟨by rw [hval]; exact hbound h, fun y hy => ?_⟩
  by_cases hp : proposer h.length = i
  · have hr' := hdev.2 h y hp
    cases hry : σ.resp h y with
    | true =>
      rw [G.respValue_accept hry, G.respValue_accept (hr'.trans hry)]
    | false =>
      rw [G.respValue_reject hry, G.respValue_reject (hr'.trans hry), hval]
      gcongr
      exact hbound _
  · rcases eq_or_eq_other (proposer h.length) i with h1 | h1
    · exact absurd h1.symm hp
    · subst h1
      have := hresp h hl y hy
      cases hry : σ'.resp h y with
      | true =>
        rw [G.respValue_accept hry, share_other, offerCost_other, sub_zero]
        exact this.1
      | false =>
        rw [G.respValue_reject hry, offerCost_other, neg_zero, WithBot.coe_zero, zero_add]
        exact (hbound _).trans this.2

/-- The regime of the delay equilibrium after the first rejection: player 1 gets `v − c` if
the first offer was `0`, and `0` otherwise. -/
noncomputable def delayReg (h : List ℝ) : ℝ := if h.getLast? = some 0 then G.v - G.c else 0

/-- Payoffs in the delay equilibrium: at the root `(v − 2c, 0)`; after the first offer `y`
player 1 gets `delayReg` and player 2 gets the rest of `v − c`. -/
noncomputable def delayV (h : List ℝ) (i : Fin 2) : ℝ :=
  if h = [] then (if i = 0 then G.v - 2 * G.c else 0)
  else (if i = 0 then G.delayReg h else G.v - G.c - G.delayReg h)

/-- **An SPNE with delay** (Exercise 9.B.13, MWG, p. 303). Player 1 offers `0` and player 2
rejects it; after that, a stationary split profile is played in which player 1 gets `v − c` if
the first offer was `0` and `0` otherwise (and player 2 accepts a first offer `y ≠ 0` exactly
when `y ≥ v − c`). -/
noncomputable def delayProfile : BargainingProfile where
  prop h := if h = [] then 0 else G.delayV h (other (proposer h.length))
  resp h y := if h = [] then decide (y ≠ 0 ∧ G.v - G.c ≤ y)
    else decide (G.delayV h (other (proposer h.length)) ≤ y)

theorem delayV_cons {h : List ℝ} (hh : h ≠ []) (y : ℝ) (i : Fin 2) :
    G.delayV (y :: h) i = G.delayV h i := by
  obtain ⟨b, l, rfl⟩ := List.exists_cons_of_ne_nil hh
  simp [delayV, delayReg, List.getLast?_cons_cons]

theorem delayV_add {h : List ℝ} (hh : h ≠ []) (i : Fin 2) :
    G.delayV h i + G.delayV h (other i) = G.v - G.c := by
  rcases Fin.exists_fin_two.1 ⟨i, rfl⟩ with rfl | rfl
  · simp only [delayV, hh, ↓reduceIte, show other 0 = 1 from rfl, one_ne_zero]
    ring
  · simp only [delayV, hh, ↓reduceIte, show other 1 = 0 from rfl, one_ne_zero]
    ring

theorem delayV_nil_one : G.delayV [] 1 = 0 := by simp [delayV]

theorem delayReg_mem (h : List ℝ) : G.delayReg h ∈ Set.Icc 0 (G.v - G.c) := by
  have := G.c_lt_v
  unfold delayReg
  split_ifs <;> constructor <;> linarith

/-- **Exercise 9.B.13: agreement need not be immediate** (MWG, p. 303). If `v ≥ 2c`, the
infinite game has an SPNE in which player 1's first offer is rejected; player 1 then gets
`v − 2c` and player 2 gets `0`. -/
theorem delayProfile_isSPNE (hT : G.T = ⊤) (hc2 : 2 * G.c ≤ G.v) :
    G.IsSPNE G.delayProfile ∧ G.delayProfile.resp [] (G.delayProfile.prop []) = false ∧
      G.value G.delayProfile [] 0 = ((G.v - 2 * G.c : ℝ) : WithBot ℝ) ∧
      G.value G.delayProfile [] 1 = ((0 : ℝ) : WithBot ℝ) := by
  have hc := G.c_pos
  have hl : ∀ n, G.Live n := G.live_top hT
  have hp0 : proposer ([] : List ℝ).length = 0 := rfl
  have ho0 : other (0 : Fin 2) = 1 := rfl
  have hreg := G.delayReg_mem
  have hres0 : ∀ y, G.delayProfile.resp [] y = decide (y ≠ 0 ∧ G.v - G.c ≤ y) := fun y => by
    simp only [delayProfile, ↓reduceIte]
  have hresc : ∀ h, h ≠ [] → ∀ y, G.delayProfile.resp h y =
      decide (G.delayV h (other (proposer h.length)) ≤ y) := fun h hh y => by
    simp only [delayProfile, hh, ↓reduceIte]
  have hprop0 : G.delayProfile.prop [] = 0 := by simp only [delayProfile, ↓reduceIte]
  have hpropc : ∀ h, h ≠ [] → G.delayProfile.prop h = G.delayV h (other (proposer h.length)) :=
    fun h hh => by simp only [delayProfile, hh, ↓reduceIte]
  have hreg0 : G.delayReg [0] = G.v - G.c := by simp [delayReg]
  have hregy : ∀ y, y ≠ 0 → G.delayReg [y] = 0 := fun y hy => by simp [delayReg, hy]
  have hV1 : ∀ y, G.delayV [y] 1 = G.v - G.c - G.delayReg [y] := fun y => by simp [delayV]
  have hV0 : ∀ y, G.delayV [y] 0 = G.delayReg [y] := fun y => by simp [delayV]
  -- values at nodes after the first offer: immediate agreement
  have hvalc : ∀ h, h ≠ [] → ∀ i, G.value G.delayProfile h i = (G.delayV h i : WithBot ℝ) := by
    intro h hh i
    have hacc : G.delayProfile.resp h (G.delayProfile.prop h) = true := by
      rw [hresc h hh, hpropc h hh]; simp
    rw [G.value_eq_respValue _ (hl _), G.respValue_accept hacc, hpropc h hh]
    rcases eq_or_eq_other (proposer h.length) i with h1 | h1
    · subst h1
      rw [share_proposer, offerCost_proposer]
      have := G.delayV_add hh (proposer h.length)
      congr 1
      linarith
    · subst h1
      rw [share_other, offerCost_other, sub_zero]
  have hrej0 : G.delayProfile.resp [] (G.delayProfile.prop []) = false := by
    rw [hres0, hprop0]; simp
  have hval : ∀ h i, G.value G.delayProfile h i = (G.delayV h i : WithBot ℝ) := by
    intro h i
    by_cases hh : h = []
    · subst hh
      rw [G.value_eq_respValue _ (hl _), G.respValue_reject hrej0, hprop0,
        hvalc _ (List.cons_ne_nil _ _), ← WithBot.coe_add]
      congr 1
      rcases Fin.exists_fin_two.1 ⟨i, rfl⟩ with rfl | rfl
      · rw [← hp0, offerCost_proposer, hp0, hV0, hreg0]
        simp only [delayV, ↓reduceIte]
        ring
      · rw [show (1 : Fin 2) = other (proposer ([] : List ℝ).length) from rfl, offerCost_other,
          ← show (1 : Fin 2) = other (proposer ([] : List ℝ).length) from rfl, hV1, hreg0,
          delayV_nil_one]
        ring
    · exact hvalc h hh i
  refine ⟨G.isSPNE_of_oneStage (fun h => ?_) G.delayV hval (fun h _ y hy => ?_)
    (fun h _ y hy hr => ?_) (fun h _ y hy hr => ?_), hrej0, ?_, ?_⟩
  · by_cases hh : h = []
    · subst hh
      rw [hprop0]
      exact ⟨le_rfl, by linarith⟩
    · rw [hpropc h hh]
      have h1 := hreg h
      rcases Fin.exists_fin_two.1 ⟨other (proposer h.length), rfl⟩ with h2 | h2 <;>
        rw [h2] <;> simp only [delayV, hh, ↓reduceIte, one_ne_zero] <;> constructor <;>
        linarith [h1.1, h1.2]
  · by_cases hh : h = []
    · subst hh
      rw [hp0, hV0]
      have hy1 := hreg [y]
      by_cases hr : G.delayProfile.resp [] y = true
      · simp only [hr, ↓reduceIte]
        rw [hres0] at hr
        have := (of_decide_eq_true hr).2
        simp only [delayV, ↓reduceIte]
        linarith
      · simp only [hr, Bool.false_eq_true, ↓reduceIte]
        simp only [delayV, ↓reduceIte]
        linarith [hy1.2]
    · rw [G.delayV_cons hh]
      have hs := G.delayV_add hh (proposer h.length)
      by_cases hr : G.delayProfile.resp h y = true
      · simp only [hr, ↓reduceIte]
        rw [hresc h hh] at hr
        have := of_decide_eq_true hr
        linarith
      · simp only [hr, Bool.false_eq_true, ↓reduceIte]
        linarith
  · by_cases hh : h = []
    · subst hh
      rw [hres0] at hr
      have := of_decide_eq_true hr
      rw [hp0, ho0, hV1, hregy y this.1]
      linarith [this.2]
    · rw [G.delayV_cons hh]
      rw [hresc h hh] at hr
      exact of_decide_eq_true hr
  · by_cases hh : h = []
    · subst hh
      rw [hres0] at hr
      have := of_decide_eq_false hr
      rw [hp0, ho0, hV1]
      by_cases hy0 : y = 0
      · subst hy0
        rw [hreg0]
        simp
      · rw [hregy y hy0]
        push Not at this
        linarith [this hy0]
    · rw [G.delayV_cons hh]
      rw [hresc h hh] at hr
      have := of_decide_eq_false hr
      linarith
  · rw [hval]
    simp [delayV]
  · rw [hval, delayV_nil_one]

/-- **Exercise 9.B.13: delay** (MWG, p. 303). In the infinite game, if `v < 2c` every SPNE has
immediate agreement at every feasible node; if `v ≥ 2c` some SPNE has the first offer
rejected. -/
theorem exercise_9_B_13_delay (hT : G.T = ⊤) :
    (G.v < 2 * G.c → ∀ σ, G.IsSPNE σ → ∀ h, G.ValidHist h → σ.resp h (σ.prop h) = true) ∧
      (2 * G.c ≤ G.v → ∃ σ, G.IsSPNE σ ∧ σ.resp [] (σ.prop []) = false) :=
  ⟨fun hc2 _ hσ _ hv => G.spne_immediate hσ hv (G.live_top hT _) hc2,
    fun hc2 => ⟨_, (G.delayProfile_isSPNE hT hc2).1, (G.delayProfile_isSPNE hT hc2).2.1⟩⟩

end OfferCostGame

/-- **Exercise 9.B.13: an instance** (MWG, p. 303): `v = 2`, `c = 1`, infinite horizon; the
split profiles with `a = 0` and `a = 1` are both SPNE. -/
theorem exercise_9_B_13_instance :
    ∃ G : OfferCostGame, G.T = ⊤ ∧ G.IsSPNE (G.splitProfile 0) ∧ G.IsSPNE (G.splitProfile 1) :=
  ⟨⟨2, 1, ⊤, by norm_num, by norm_num⟩, rfl,
    (OfferCostGame.splitProfile_isSPNE _ rfl ⟨le_rfl, by norm_num⟩).1,
    (OfferCostGame.splitProfile_isSPNE _ rfl ⟨by norm_num, by norm_num⟩).1⟩

/-- **Exercise 9.B.13: instances of the delay dichotomy** (MWG, p. 303): with `v = 2`, `c = 1`
(so `v ≥ 2c`) the delay profile is an SPNE with the first offer rejected; with `v = 3/2`,
`c = 1` (so `v < 2c`) every SPNE agrees at once, and an SPNE exists. -/
theorem exercise_9_B_13_delay_instance :
    (∃ G : OfferCostGame, G.T = ⊤ ∧ 2 * G.c ≤ G.v ∧ G.IsSPNE G.delayProfile ∧
      G.delayProfile.resp [] (G.delayProfile.prop []) = false) ∧
    ∃ G : OfferCostGame, G.T = ⊤ ∧ G.v < 2 * G.c ∧ G.IsSPNE (G.splitProfile 0) ∧
      ∀ σ, G.IsSPNE σ → ∀ h, G.ValidHist h → σ.resp h (σ.prop h) = true := by
  refine ⟨⟨⟨2, 1, ⊤, by norm_num, by norm_num⟩, rfl, by norm_num, ?_, ?_⟩,
    ⟨⟨3 / 2, 1, ⊤, by norm_num, by norm_num⟩, rfl, by norm_num, ?_, ?_⟩⟩
  · exact (OfferCostGame.delayProfile_isSPNE _ rfl (by norm_num)).1
  · exact (OfferCostGame.delayProfile_isSPNE _ rfl (by norm_num)).2.1
  · exact (OfferCostGame.splitProfile_isSPNE _ rfl ⟨le_rfl, by norm_num⟩).1
  · exact (OfferCostGame.exercise_9_B_13_delay _ rfl).1 (by norm_num)

/-- **Exercise 9.B.7: an instance** (MWG, p. 302): `v = 2`, `c = 1`, three periods; the unique
SPNE gives player 1 the payoff `v − c = 1`. -/
theorem exercise_9_B_7_instance :
    ∃ G : OfferCostGame, G.T = 3 ∧ G.IsSPNE (OfferCostGame.threshold (fun n => G.W (3 - n - 1))) ∧
      ∀ σ, G.IsSPNE σ → G.value σ [] 0 = ((1 : ℝ) : WithBot ℝ) := by
  refine ⟨⟨2, 1, 3, by norm_num, by norm_num⟩, rfl, ?_, fun σ hσ => ?_⟩
  · exact (OfferCostGame.exercise_9_B_7 _ (N := 3) rfl).1
  · rw [((OfferCostGame.exercise_9_B_7 _ (N := 3) rfl).2 σ hσ).2.1]
    norm_num [OfferCostGame.W]

end MWG.DynamicGames
