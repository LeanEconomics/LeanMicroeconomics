/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import Mathlib.Data.ENat.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FinCases

/-!
# Finite and infinite horizon bilateral bargaining

MWG, Appendix A of Chapter 9, pp. 296-299 (Examples 9.AA.1 and 9.AA.2), and Exercise 9.B.12.

Two players (`0` is MWG's player 1) divide `v` dollars. In period `t = 0, 1, 2, …` (MWG's period
`t + 1`) the proposer, player `0` in even and player `1` in odd periods, offers the responder
an amount `y ∈ [0, v]`; the responder accepts or rejects. Agreement in period `t` on offer `y`
gives the proposer `δ_i^t (v − y)` and the responder `δ_j^t y`. The horizon `T : ℕ∞` is the
number of periods (`⊤`: Rubinstein's infinite horizon); without agreement both get `0`.

Histories at a proposal node are the lists of rejected offers (most recent first). A
`Profile` gives the offer `prop h` at every history and the response `resp h y` to every offer
at every history; player `i`'s strategy is its part at the nodes where `i` moves. Every
proposal node `h` and every response node `(h, y)` begins a subgame. `IsSPNE` is subgame
perfection: at every (feasible, live) node no player gains by any change of her strategy.
Values are measured in dollars of the period of the node.

* `value_le_of_bound`: a discounted one-shot bound (the infinite-horizon one-stage deviation
  argument used to verify that a profile is subgame perfect).
* `value_ge_of_isSPNE`, `value_le_of_isSPNE`: the Shaked-Sutton bounds `v − δ_j M_j` and
  `v − δ_j m_j` on the proposer's SPNE payoff.
* `example_9_AA_2` (Rubinstein, with `δ₁ = δ₂`) and `exercise_9_B_12` (different discount
  factors): the SPNE exists and is unique; player `i` proposing earns
  `v (1 − δ_j) / (1 − δ_i δ_j)`; agreement is immediate.
* `example_9_AA_1`: the finite horizon game has a unique SPNE; the first proposer earns
  `v (1 − (−δ)^T) / (1 + δ)`, which for odd `T` is `v [1 − δ + δ² − ⋯ + δ^{T−1}]` and for even
  `T` is `v − δ v₁*(T − 1)`, and tends to `v / (1 + δ)` (`example_9_AA_1_limit`).
-/

namespace MWG.DynamicGames

/-- The data of an alternating-offer bargaining game: the surplus `v > 0`, discount factors
`δ_i ∈ (0, 1)` and the horizon `T` (number of periods; `⊤` for the infinite horizon). -/
structure BargainingGame where
  /-- The amount to be divided. -/
  v : ℝ
  /-- The players' discount factors. -/
  δ : Fin 2 → ℝ
  /-- The horizon: the number of periods. -/
  T : ℕ∞
  v_pos : 0 < v
  δ_pos : ∀ i, 0 < δ i
  δ_lt_one : ∀ i, δ i < 1

/-- A strategy profile of the bargaining game: the offer at every history and the response to
every offer at every history (`true` = accept). -/
structure BargainingProfile where
  /-- The offer made to the responder at history `h`. -/
  prop : List ℝ → ℝ
  /-- The response at history `h` to offer `y`. -/
  resp : List ℝ → ℝ → Bool

namespace BargainingGame

/-- The proposer in period `t`: player `0` (MWG's player 1) in even periods. -/
def proposer (t : ℕ) : Fin 2 := if t % 2 = 0 then 0 else 1

/-- The other player. -/
def other (i : Fin 2) : Fin 2 := if i = 0 then 1 else 0

theorem other_ne (i : Fin 2) : other i ≠ i := by fin_cases i <;> decide

theorem ne_other (i : Fin 2) : i ≠ other i := (other_ne i).symm

theorem other_other (i : Fin 2) : other (other i) = i := by fin_cases i <;> decide

theorem eq_or_eq_other (i j : Fin 2) : j = i ∨ j = other i := by
  fin_cases i <;> fin_cases j <;> decide

theorem proposer_succ (t : ℕ) : proposer (t + 1) = other (proposer t) := by
  unfold proposer other
  rcases Nat.mod_two_eq_zero_or_one t with h | h
  · have : (t + 1) % 2 = 1 := by omega
    simp [h, this]
  · have : (t + 1) % 2 = 0 := by omega
    simp [h, this]

variable (B : BargainingGame)

/-- Player `i`'s share (undiscounted) of an agreement on offer `y` in period `t`. -/
def share (i : Fin 2) (t : ℕ) (y : ℝ) : ℝ := if proposer t = i then B.v - y else y

theorem share_proposer (t : ℕ) (y : ℝ) : B.share (proposer t) t y = B.v - y := by
  simp [share]

theorem share_other (t : ℕ) (y : ℝ) : B.share (other (proposer t)) t y = y := by
  simp [share, ne_other]

/-- Period `t` is within the horizon. -/
def Live (t : ℕ) : Prop := (t : ℕ∞) < B.T

theorem live_of_le {s t : ℕ} (ht : B.Live t) (hst : s ≤ t) : B.Live s :=
  lt_of_le_of_lt (Nat.cast_le.2 hst) ht

/-- The history after `t` further rejections, when offers follow `σ`. -/
def path (σ : BargainingProfile) (h : List ℝ) : ℕ → List ℝ
  | 0 => h
  | t + 1 => σ.prop (path σ h t) :: path σ h t

theorem length_path (σ : BargainingProfile) (h : List ℝ) (t : ℕ) :
    (path σ h t).length = h.length + t := by
  induction t with
  | zero => rfl
  | succ t ih => simp [path, ih]; omega

theorem path_succ (σ : BargainingProfile) (h : List ℝ) (t : ℕ) :
    path σ h (t + 1) = path σ (σ.prop h :: h) t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [path, ih, path]

/-- Agreement is reached `t` periods after history `h` (if the earlier offers were rejected). -/
def Agrees (σ : BargainingProfile) (h : List ℝ) (t : ℕ) : Prop :=
  B.Live (h.length + t) ∧ σ.resp (path σ h t) (σ.prop (path σ h t)) = true

open Classical in
/-- Player `i`'s payoff from the proposal node `h` under `σ`, in dollars of the period of `h`:
`δ_i^T × share` if the first agreement is `T` periods later, `0` without agreement. -/
noncomputable def value (σ : BargainingProfile) (h : List ℝ) (i : Fin 2) : ℝ :=
  if hx : ∃ t, B.Agrees σ h t then
    B.δ i ^ Nat.find hx * B.share i (h.length + Nat.find hx) (σ.prop (path σ h (Nat.find hx)))
  else 0

open Classical in
/-- Player `i`'s payoff from the response node `(h, y)`. -/
noncomputable def respValue (σ : BargainingProfile) (h : List ℝ) (y : ℝ) (i : Fin 2) : ℝ :=
  if B.Live h.length ∧ σ.resp h y = true then B.share i h.length y
  else B.δ i * B.value σ (y :: h) i

open Classical in
theorem value_of_exists {σ : BargainingProfile} {h : List ℝ} (hx : ∃ t, B.Agrees σ h t)
    (i : Fin 2) : B.value σ h i = B.δ i ^ Nat.find hx *
      B.share i (h.length + Nat.find hx) (σ.prop (path σ h (Nat.find hx))) := by
  unfold value
  split_ifs
  rfl

theorem value_of_not_exists {σ : BargainingProfile} {h : List ℝ} (hx : ¬ ∃ t, B.Agrees σ h t)
    (i : Fin 2) : B.value σ h i = 0 := by
  unfold value
  split_ifs
  rfl

theorem respValue_accept {σ : BargainingProfile} {h : List ℝ} {y : ℝ} (hl : B.Live h.length)
    (hy : σ.resp h y = true) (i : Fin 2) : B.respValue σ h y i = B.share i h.length y := by
  unfold respValue
  split_ifs with hc
  · rfl
  · exact absurd ⟨hl, hy⟩ hc

theorem respValue_reject {σ : BargainingProfile} {h : List ℝ} {y : ℝ}
    (hy : σ.resp h y = false) (i : Fin 2) : B.respValue σ h y i = B.δ i * B.value σ (y :: h) i := by
  unfold respValue
  split_ifs with hc
  · simp [hy] at hc
  · rfl

/-- Beyond the horizon nothing is agreed. -/
theorem value_of_not_live {σ : BargainingProfile} {h : List ℝ} (hl : ¬ B.Live h.length)
    (i : Fin 2) : B.value σ h i = 0 :=
  B.value_of_not_exists (fun ⟨t, ht⟩ => hl (B.live_of_le ht.1 (by omega))) i

/-- The value at a proposal node is the value at the response node to the offer made there. -/
theorem value_eq_respValue (σ : BargainingProfile) {h : List ℝ} (hl : B.Live h.length)
    (i : Fin 2) : B.value σ h i = B.respValue σ h (σ.prop h) i := by
  classical
  have hshift : ∀ t, B.Agrees σ h (t + 1) ↔ B.Agrees σ (σ.prop h :: h) t := by
    intro t
    simp only [Agrees, path_succ, List.length_cons,
      show h.length + (t + 1) = h.length + 1 + t by omega]
  by_cases h0 : σ.resp h (σ.prop h) = true
  · have hA : B.Agrees σ h 0 := ⟨by simpa using hl, by simpa [path] using h0⟩
    have hx : ∃ t, B.Agrees σ h t := ⟨0, hA⟩
    rw [B.value_of_exists hx, B.respValue_accept hl h0]
    have hf : Nat.find hx = 0 := (Nat.find_eq_zero hx).2 hA
    simp only [hf, pow_zero, one_mul, add_zero, path]
  · have h0' : σ.resp h (σ.prop h) = false := by simpa using h0
    rw [B.respValue_reject h0']
    have hA0 : ¬ B.Agrees σ h 0 := fun h' => h0 (by simpa [path] using h'.2)
    by_cases hx' : ∃ t, B.Agrees σ (σ.prop h :: h) t
    · have hx : ∃ t, B.Agrees σ h t := let ⟨t, ht⟩ := hx'; ⟨t + 1, (hshift t).2 ht⟩
      have hx2 : ∃ t, B.Agrees σ h (t + 1) := let ⟨t, ht⟩ := hx'; ⟨t, (hshift t).2 ht⟩
      have hf : Nat.find hx = Nat.find hx' + 1 := by
        rw [Nat.find_comp_succ hx hx2 hA0]
        congr 1
        exact Nat.find_congr' (hshift _)
      rw [B.value_of_exists hx, B.value_of_exists hx', hf, path_succ, pow_succ]
      simp only [List.length_cons, show h.length + (Nat.find hx' + 1) =
        h.length + 1 + Nat.find hx' by omega]
      ring
    · have hx : ¬ ∃ t, B.Agrees σ h t := by
        rintro ⟨t, ht⟩
        cases t with
        | zero => exact hA0 ht
        | succ t => exact hx' ⟨t, (hshift t).1 ht⟩
      rw [B.value_of_not_exists hx, B.value_of_not_exists hx', mul_zero]

/-- The value from `h` depends only on the moves at histories at least as long as `h`. -/
theorem value_congr {σ σ' : BargainingProfile} {h : List ℝ}
    (hp : ∀ h', h.length ≤ h'.length → σ.prop h' = σ'.prop h')
    (hr : ∀ h' y, h.length ≤ h'.length → σ.resp h' y = σ'.resp h' y) (i : Fin 2) :
    B.value σ h i = B.value σ' h i := by
  classical
  have hpath : ∀ t, path σ h t = path σ' h t := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih =>
      rw [path, path, ih, hp _ (by rw [length_path]; omega)]
  have hA : ∀ t, B.Agrees σ h t ↔ B.Agrees σ' h t := by
    intro t
    unfold Agrees
    rw [hpath, hp _ (by rw [length_path]; omega), hr _ _ (by rw [length_path]; omega)]
  by_cases hx : ∃ t, B.Agrees σ h t
  · have hx' : ∃ t, B.Agrees σ' h t := let ⟨t, ht⟩ := hx; ⟨t, (hA t).1 ht⟩
    rw [B.value_of_exists hx, B.value_of_exists hx']
    have hf : Nat.find hx = Nat.find hx' := Nat.find_congr' (hA _)
    rw [hf, hpath, hp _ (by rw [length_path]; omega)]
  · have hx' : ¬ ∃ t, B.Agrees σ' h t := fun ⟨t, ht⟩ => hx ⟨t, (hA t).2 ht⟩
    rw [B.value_of_not_exists hx, B.value_of_not_exists hx']

/-- Offers are feasible: `prop h ∈ [0, v]` at every history. -/
def Feasible (σ : BargainingProfile) : Prop := ∀ h, σ.prop h ∈ Set.Icc 0 B.v

/-- A history of feasible offers. -/
def ValidHist (h : List ℝ) : Prop := ∀ y ∈ h, y ∈ Set.Icc 0 B.v

theorem validHist_cons {h : List ℝ} (hh : B.ValidHist h) {y : ℝ} (hy : y ∈ Set.Icc 0 B.v) :
    B.ValidHist (y :: h) := by
  intro z hz
  rcases List.mem_cons.1 hz with rfl | hz
  · exact hy
  · exact hh z hz

/-- Shares of a feasible offer are in `[0, v]` and add up to `v`. -/
theorem share_mem (i : Fin 2) (t : ℕ) {y : ℝ} (hy : y ∈ Set.Icc 0 B.v) :
    0 ≤ B.share i t y ∧ B.share i t y ≤ B.v := by
  unfold share
  split_ifs <;> constructor <;> linarith [hy.1, hy.2]

theorem share_add (i : Fin 2) (t : ℕ) (y : ℝ) : B.share i t y + B.share (other i) t y = B.v := by
  unfold share
  rcases eq_or_eq_other i (proposer t) with h | h
  · rw [h]; simp [ne_other]
  · rw [h]; simp [other_ne]

/-- Payoffs are in `[0, v]` and the two players' payoffs add up to at most `v`. -/
theorem value_bounds {σ : BargainingProfile} (hσ : B.Feasible σ) (h : List ℝ) (i : Fin 2) :
    0 ≤ B.value σ h i ∧ B.value σ h i + B.value σ h (other i) ≤ B.v := by
  classical
  by_cases hx : ∃ t, B.Agrees σ h t
  · rw [B.value_of_exists hx, B.value_of_exists hx]
    set T := Nat.find hx
    set y := σ.prop (path σ h T)
    have hy := hσ (path σ h T)
    have h1 := B.share_mem i (h.length + T) hy
    have h2 := B.share_mem (other i) (h.length + T) hy
    have hadd := B.share_add i (h.length + T) y
    have hd1 : B.δ i ^ T ≤ 1 := pow_le_one₀ (B.δ_pos i).le (B.δ_lt_one i).le
    have hd2 : B.δ (other i) ^ T ≤ 1 := pow_le_one₀ (B.δ_pos _).le (B.δ_lt_one _).le
    have hp1 : 0 ≤ B.δ i ^ T := pow_nonneg (B.δ_pos i).le T
    have hp2 : 0 ≤ B.δ (other i) ^ T := pow_nonneg (B.δ_pos _).le T
    refine ⟨mul_nonneg hp1 h1.1, ?_⟩
    nlinarith [mul_le_of_le_one_left h1.1 hd1, mul_le_of_le_one_left h2.1 hd2]
  · rw [B.value_of_not_exists hx, B.value_of_not_exists hx]
    exact ⟨le_rfl, by linarith [B.v_pos]⟩

/-- Player `i`'s deviation from `σ` to `σ'`: `σ'` agrees with `σ` wherever `i` does not move. -/
def IsDeviation (i : Fin 2) (σ σ' : BargainingProfile) : Prop :=
  (∀ h, proposer h.length ≠ i → σ'.prop h = σ.prop h) ∧
    ∀ h y, proposer h.length = i → σ'.resp h y = σ.resp h y

/-- **Definition 9.B.2 for the bargaining game** (MWG, pp. 275 and 296-298). A subgame perfect
Nash equilibrium: at every feasible proposal node `h` within the horizon and at every response
node `(h, y)` with `y ∈ [0, v]`, no player gains by deviating to any feasible strategy. -/
def IsSPNE (σ : BargainingProfile) : Prop :=
  B.Feasible σ ∧ ∀ i σ', B.Feasible σ' → IsDeviation i σ σ' → ∀ h, B.ValidHist h →
    B.Live h.length → B.value σ' h i ≤ B.value σ h i ∧
      ∀ y ∈ Set.Icc 0 B.v, B.respValue σ' h y i ≤ B.respValue σ h y i

open Classical in
/-- Changing only the response at the node `(h₀, y₀)`. -/
noncomputable def setResp (σ : BargainingProfile) (h₀ : List ℝ) (y₀ : ℝ) (b : Bool) :
    BargainingProfile where
  prop := σ.prop
  resp h y := if h = h₀ ∧ y = y₀ then b else σ.resp h y

open Classical in
/-- Changing only the offer at the history `h₀`. -/
noncomputable def setProp (σ : BargainingProfile) (h₀ : List ℝ) (y₀ : ℝ) : BargainingProfile where
  prop h := if h = h₀ then y₀ else σ.prop h
  resp := σ.resp

theorem setResp_value (σ : BargainingProfile) (h₀ : List ℝ) (y₀ : ℝ) (b : Bool) (i : Fin 2) :
    B.value (setResp σ h₀ y₀ b) (y₀ :: h₀) i = B.value σ (y₀ :: h₀) i := by
  refine B.value_congr (σ := setResp σ h₀ y₀ b) (σ' := σ) (fun _ _ => rfl) (fun h' y hl => ?_) i
  have : h' ≠ h₀ := fun he => by rw [he] at hl; simp at hl
  simp [setResp, this]

theorem setProp_value (σ : BargainingProfile) (h₀ : List ℝ) (y₀ y : ℝ) (i : Fin 2) :
    B.value (setProp σ h₀ y₀) (y :: h₀) i = B.value σ (y :: h₀) i := by
  refine B.value_congr (σ := setProp σ h₀ y₀) (σ' := σ) (fun h' hl => ?_) (fun _ _ _ => rfl) i
  have : h' ≠ h₀ := fun he => by rw [he] at hl; simp at hl
  simp [setProp, this]

theorem setResp_isDeviation (σ : BargainingProfile) (h₀ : List ℝ) (y₀ : ℝ) (b : Bool) :
    IsDeviation (other (proposer h₀.length)) σ (setResp σ h₀ y₀ b) := by
  refine ⟨fun _ _ => rfl, fun h y hh => ?_⟩
  have : h ≠ h₀ := fun he => by rw [he] at hh; exact other_ne _ hh.symm
  simp [setResp, this]

theorem setProp_isDeviation (σ : BargainingProfile) (h₀ : List ℝ) (y₀ : ℝ) :
    IsDeviation (proposer h₀.length) σ (setProp σ h₀ y₀) := by
  refine ⟨fun h hh => ?_, fun _ _ _ => rfl⟩
  have : h ≠ h₀ := fun he => by rw [he] at hh; exact hh rfl
  simp [setProp, this]

theorem setResp_feasible {σ : BargainingProfile} (hσ : B.Feasible σ) (h₀ : List ℝ) (y₀ : ℝ)
    (b : Bool) : B.Feasible (setResp σ h₀ y₀ b) := hσ

theorem setProp_feasible {σ : BargainingProfile} (hσ : B.Feasible σ) (h₀ : List ℝ) {y₀ : ℝ}
    (hy : y₀ ∈ Set.Icc 0 B.v) : B.Feasible (setProp σ h₀ y₀) := by
  intro h
  simp only [setProp]
  split_ifs
  · exact hy
  · exact hσ h

/-- In an SPNE the responder accepts an offer that beats her continuation payoff. -/
theorem accept_of_gt {σ : BargainingProfile} (hσ : B.IsSPNE σ) {h : List ℝ} (hv : B.ValidHist h)
    (hl : B.Live h.length) {y : ℝ} (hy : y ∈ Set.Icc 0 B.v)
    (hgt : B.δ (other (proposer h.length)) * B.value σ (y :: h) (other (proposer h.length)) < y) :
    σ.resp h y = true := by
  by_contra hrej
  have hrej' : σ.resp h y = false := by simpa using hrej
  have := (hσ.2 _ _ (B.setResp_feasible hσ.1 h y true) (setResp_isDeviation σ h y true) h hv
    hl).2 y hy
  rw [B.respValue_accept hl (by simp [setResp]), B.respValue_reject hrej', share_other] at this
  linarith

/-- In an SPNE the responder rejects an offer below her continuation payoff. -/
theorem reject_of_lt {σ : BargainingProfile} (hσ : B.IsSPNE σ) {h : List ℝ} (hv : B.ValidHist h)
    (hl : B.Live h.length) {y : ℝ} (hy : y ∈ Set.Icc 0 B.v)
    (hlt : y < B.δ (other (proposer h.length)) * B.value σ (y :: h) (other (proposer h.length))) :
    σ.resp h y = false := by
  by_contra hacc
  have hacc' : σ.resp h y = true := by simpa using hacc
  have := (hσ.2 _ _ (B.setResp_feasible hσ.1 h y false) (setResp_isDeviation σ h y false) h hv
    hl).2 y hy
  rw [B.respValue_reject (by simp [setResp]), B.setResp_value, B.respValue_accept hl hacc',
    share_other] at this
  linarith

/-- In an SPNE the proposer does at least as well as with any other feasible offer. -/
theorem respValue_le_value {σ : BargainingProfile} (hσ : B.IsSPNE σ) {h : List ℝ}
    (hv : B.ValidHist h) (hl : B.Live h.length) {y : ℝ} (hy : y ∈ Set.Icc 0 B.v) :
    B.respValue σ h y (proposer h.length) ≤ B.value σ h (proposer h.length) := by
  have := (hσ.2 _ _ (B.setProp_feasible hσ.1 h hy) (setProp_isDeviation σ h y) h hv hl).1
  rw [B.value_eq_respValue _ hl] at this
  have hp : (setProp σ h y).prop h = y := by simp [setProp]
  rw [hp] at this
  unfold respValue at this ⊢
  rw [B.setProp_value] at this
  exact this

/-- **Shaked-Sutton lower bound** (MWG, p. 298). In an SPNE, if the responder can expect at
most `M` as the next proposer after any rejection, the proposer earns at least
`v − δ_j M`. -/
theorem value_ge_of_isSPNE {σ : BargainingProfile} (hσ : B.IsSPNE σ) {h : List ℝ}
    (hv : B.ValidHist h) (hl : B.Live h.length) {M : ℝ}
    (hM : ∀ y ∈ Set.Icc 0 B.v, B.value σ (y :: h) (other (proposer h.length)) ≤ M) :
    B.v - B.δ (other (proposer h.length)) * M ≤ B.value σ h (proposer h.length) := by
  set p := proposer h.length
  set r := other p
  have hM0 : 0 ≤ M := le_trans (B.value_bounds hσ.1 _ r).1 (hM 0 ⟨le_rfl, B.v_pos.le⟩)
  have hval0 := (B.value_bounds hσ.1 h p).1
  by_contra hlt
  push Not at hlt
  set ε := (B.v - B.δ r * M - B.value σ h p) / 2 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  set y := B.δ r * M + ε
  have hδr := B.δ_pos r
  have hy : y ∈ Set.Icc 0 B.v := ⟨by positivity, by simp only [y]; linarith⟩
  have hacc : σ.resp h y = true := by
    refine B.accept_of_gt hσ hv hl hy ?_
    have := hM y hy
    have : B.δ r * B.value σ (y :: h) r ≤ B.δ r * M := mul_le_mul_of_nonneg_left this hδr.le
    simp only [y]
    linarith
  have := B.respValue_le_value hσ hv hl hy
  rw [B.respValue_accept hl hacc, share_proposer] at this
  simp only [y] at this
  linarith

/-- **Shaked-Sutton upper bound** (MWG, p. 298). In an SPNE, if the responder can expect at
least `m ≥ 0` as the next proposer after any rejection, the proposer earns at most
`v − δ_j m`. -/
theorem value_le_of_isSPNE {σ : BargainingProfile} (hσ : B.IsSPNE σ) {h : List ℝ}
    (hv : B.ValidHist h) (hl : B.Live h.length) {m : ℝ} (hm0 : 0 ≤ m)
    (hm : ∀ y ∈ Set.Icc 0 B.v, m ≤ B.value σ (y :: h) (other (proposer h.length))) :
    B.value σ h (proposer h.length) ≤ B.v - B.δ (other (proposer h.length)) * m := by
  set p := proposer h.length
  set r := other p
  set y := σ.prop h
  have hy := hσ.1 h
  rw [B.value_eq_respValue σ hl]
  cases hacc : σ.resp h y with
  | true =>
    rw [B.respValue_accept hl hacc, share_proposer]
    have hge : B.δ r * B.value σ (y :: h) r ≤ y := by
      by_contra hlt
      push Not at hlt
      have := B.reject_of_lt hσ hv hl hy hlt
      rw [hacc] at this
      exact Bool.noConfusion this
    have := mul_le_mul_of_nonneg_left (hm y hy) (B.δ_pos r).le
    linarith
  | false =>
    rw [B.respValue_reject hacc]
    have hb := B.value_bounds hσ.1 (y :: h) p
    have hmv : m ≤ B.v := le_trans (hm y hy) (by linarith [(B.value_bounds hσ.1 (y :: h) r).1,
      (B.value_bounds hσ.1 (y :: h) r).2, other_other p ▸ hb.1])
    have h1 : B.value σ (y :: h) p ≤ B.v - m := by
      have := hm y hy
      linarith [hb.2]
    have hδp := B.δ_pos p
    have hδp1 := B.δ_lt_one p
    have hδr := B.δ_pos r
    have hδr1 := B.δ_lt_one r
    have : B.δ p * B.value σ (y :: h) p ≤ B.δ p * (B.v - m) :=
      mul_le_mul_of_nonneg_left h1 hδp.le
    nlinarith

/-- **Discounted one-stage deviation bound.** If `bnd ≥ 0` bounds player `i`'s payoff of an
immediate agreement at every live node, and `δ_i bnd(next) ≤ bnd` after every rejection, then
`bnd` bounds player `i`'s payoff from every node. -/
theorem value_le_of_bound {σ : BargainingProfile} {i : Fin 2} (bnd : List ℝ → ℝ)
    (h0 : ∀ h, 0 ≤ bnd h)
    (hacc : ∀ h, B.Live h.length → σ.resp h (σ.prop h) = true →
      B.share i h.length (σ.prop h) ≤ bnd h)
    (hrej : ∀ h, B.Live h.length → σ.resp h (σ.prop h) = false →
      B.δ i * bnd (σ.prop h :: h) ≤ bnd h)
    (h : List ℝ) : B.value σ h i ≤ bnd h := by
  classical
  have key : ∀ T h, (∀ s < T, ¬ B.Agrees σ h s) → B.Agrees σ h T →
      B.δ i ^ T * B.share i (h.length + T) (σ.prop (path σ h T)) ≤ bnd h := by
    intro T
    induction T with
    | zero =>
      intro h _ hA
      simpa [path] using hacc h (by simpa using hA.1) (by simpa [path] using hA.2)
    | succ T ih =>
      intro h hmin hA
      have hl : B.Live h.length := B.live_of_le hA.1 (by omega)
      have hrej0 : σ.resp h (σ.prop h) = false := by
        have := hmin 0 (by omega)
        by_contra hc
        exact this ⟨by simpa using hl, by simpa [path] using hc⟩
      have hshift : ∀ t, B.Agrees σ h (t + 1) ↔ B.Agrees σ (σ.prop h :: h) t := by
        intro t
        simp only [Agrees, path_succ, List.length_cons,
          show h.length + (t + 1) = h.length + 1 + t by omega]
      have := ih (σ.prop h :: h) (fun s hs h' => hmin (s + 1) (by omega) ((hshift s).2 h'))
        ((hshift T).1 hA)
      rw [path_succ, pow_succ, show h.length + (T + 1) = (σ.prop h :: h).length + T by
        simp; omega]
      have hδ := (B.δ_pos i).le
      calc B.δ i ^ T * B.δ i * B.share i ((σ.prop h :: h).length + T)
            (σ.prop (path σ (σ.prop h :: h) T))
          = B.δ i * (B.δ i ^ T * B.share i ((σ.prop h :: h).length + T)
            (σ.prop (path σ (σ.prop h :: h) T))) := by ring
        _ ≤ B.δ i * bnd (σ.prop h :: h) := mul_le_mul_of_nonneg_left this hδ
        _ ≤ bnd h := hrej h hl hrej0
  by_cases hx : ∃ t, B.Agrees σ h t
  · rw [B.value_of_exists hx]
    exact key _ h (fun s hs => Nat.find_min hx hs) (Nat.find_spec hx)
  · rw [B.value_of_not_exists hx]
    exact h0 h

/-- In an SPNE, if the responder's continuation value after rejecting is the same number `X`
for every offer, and the proposer earns `v − δ_j X` while a rejected offer would give her
less, then the SPNE strategies at `h` are determined: the proposer offers exactly `δ_j X` and
the responder accepts exactly the offers `y ≥ δ_j X`. -/
theorem strategies_determined {σ : BargainingProfile} (hσ : B.IsSPNE σ) {h : List ℝ}
    (hv : B.ValidHist h) (hl : B.Live h.length) {X : ℝ}
    (hX : ∀ y ∈ Set.Icc 0 B.v, B.value σ (y :: h) (other (proposer h.length)) = X)
    (hval : B.value σ h (proposer h.length) = B.v - B.δ (other (proposer h.length)) * X)
    (hrej : B.δ (proposer h.length) * (B.v - X) < B.v - B.δ (other (proposer h.length)) * X) :
    σ.prop h = B.δ (other (proposer h.length)) * X ∧
      ∀ y ∈ Set.Icc 0 B.v, σ.resp h y = true ↔ B.δ (other (proposer h.length)) * X ≤ y := by
  set p := proposer h.length
  set r := other p
  set y₀ := σ.prop h
  have hy₀ := hσ.1 h
  have hacc0 : σ.resp h y₀ = true := by
    by_contra hc
    have hc' : σ.resp h y₀ = false := by simpa using hc
    have h1 := B.value_eq_respValue σ hl p
    rw [B.respValue_reject hc', hval] at h1
    have hb := B.value_bounds hσ.1 (y₀ :: h) p
    have h2 : B.value σ (y₀ :: h) p ≤ B.v - X := by
      have := hX y₀ hy₀
      have h3 := hb.2
      rw [show other p = r from rfl, this] at h3
      linarith
    have := mul_le_mul_of_nonneg_left h2 (B.δ_pos p).le
    linarith
  have hprop : y₀ = B.δ r * X := by
    have h1 := B.value_eq_respValue σ hl p
    rw [B.respValue_accept hl hacc0, share_proposer, hval] at h1
    linarith
  refine ⟨hprop, fun y hy => ⟨fun hacc => ?_, fun hge => ?_⟩⟩
  · by_contra hlt
    push Not at hlt
    have := B.reject_of_lt hσ hv hl hy (by rw [hX y hy]; exact hlt)
    rw [hacc] at this
    exact Bool.noConfusion this
  · rcases hge.lt_or_eq with hgt | heq
    · exact B.accept_of_gt hσ hv hl hy (by rw [hX y hy]; exact hgt)
    · rw [← heq, ← hprop]
      exact hacc0

end BargainingGame

end MWG.DynamicGames
