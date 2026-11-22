/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGWelfareBargaining.RubinsteinConcave

/-!
# Rubinstein's alternating-offer game with utility payoffs

MWG, Exercise 22.E.11(c) (p. 854), building on Example 9.AA.2 (pp. 297-298) and the
alternating-offer game of `MWGDynamicGames.Bargaining` (imported).

We reuse the Chapter 9 game form: the data `BargainingGame` (amount `v = m`, discount factors,
horizon), the profiles `BargainingProfile` (offer `prop h` to the responder at every history,
response `resp h y`), the offer paths `path`, agreement times `Agrees`, proposers, shares,
deviations and feasibility. Only the payoffs change: player `i` (`0` is MWG's agent 1) values an
agreement in period `T` giving her the money share `s` at `δ_i^T uᵢ(s)` (`uValue`, `uRespValue`);
disagreement forever gives `0`. `UIsSPNE` is subgame perfection, exactly as `IsSPNE` of
Chapter 9 but with these payoffs.

* `uValue_le_of_bound`: the discounted one-stage deviation bound in utility terms.
* `uValue_ge_of_uIsSPNE`, `uValue_le_of_uIsSPNE`: the Shaked-Sutton bounds in utility space
  (the proposer gets at least `u_p(v - y)` for every offer `y` the responder must accept, and at
  most `u_p(v - q)` when `u_r(q)` is at most `δ` times the responder's worst continuation).
* `statProfile_isSPNE`: the stationary profile built from shares `s p` (proposer `p` offers
  `v - s p`; the responder accepts exactly the offers `y ≥ v - s p`, i.e. those with
  `u_r(y) ≥ δ u_r(s r)`) is an SPNE whenever the responder's stationary utility is `δ` times her
  proposer utility (`u_i(v - s_j) = δ_i u_i(s_i)`).
* `uSPNE_unique`: with a common discount factor and increasing, concave, continuous utilities,
  in every SPNE, at every feasible history, the proposer offers `v - s p`, the offer is accepted
  and both payoffs are the stationary ones. The proof is the Shaked-Sutton sup/inf argument in
  utility space: the shares `p⁺`, `p⁻` with `u₁(p⁺) = sup`, `u₁(p⁻) = inf` of agent 1's SPNE
  proposer payoffs satisfy `p⁺ ≤ T p⁺` and `T p⁻ ≤ p⁻` for the monotone map `T` whose fixed points
  are the stationary configurations; by the uniqueness of Exercise 22.E.11(a) (concavity) `T` has
  exactly one fixed point, so `p⁺ ≤ x ≤ p⁻ ≤ p⁺`.
* `exercise_22_E_11c`: every SPNE payoff configuration is the payoff configuration of the SPNE in
  stationary strategies, and that SPNE exists. `exercise_22_E_11c_instance`: linear utilities
  with `v = 1`, `δ = 1/2` (every SPNE gives agent 1 the utility `2/3` at the start).

Departure (as in `exercise_22_E_11a_exists`): the utilities are assumed continuous on `[0, m]`
(MWG assume differentiability, which implies it).
-/

namespace MWG.WelfareBargaining

open MWG.DynamicGames BargainingGame Classical in
/-- **Exercise 22.E.11(c)** (MWG, p. 854). Player `i`'s utility payoff from the proposal node `h`
under `σ`, in utils of the period of `h`: `δ_i^T uᵢ(share)` if the first agreement is `T` periods
later, `0` without agreement. -/
noncomputable def uValue (B : BargainingGame) (u : Fin 2 → ℝ → ℝ) (σ : BargainingProfile)
    (h : List ℝ) (i : Fin 2) : ℝ :=
  if hx : ∃ t, B.Agrees σ h t then
    B.δ i ^ Nat.find hx *
      u i (B.share i (h.length + Nat.find hx) (σ.prop (path σ h (Nat.find hx))))
  else 0

open MWG.DynamicGames BargainingGame Classical in
/-- **Exercise 22.E.11(c)** (MWG, p. 854). Player `i`'s utility payoff from the response node
`(h, y)`. -/
noncomputable def uRespValue (B : BargainingGame) (u : Fin 2 → ℝ → ℝ) (σ : BargainingProfile)
    (h : List ℝ) (y : ℝ) (i : Fin 2) : ℝ :=
  if B.Live h.length ∧ σ.resp h y = true then u i (B.share i h.length y)
  else B.δ i * uValue B u σ (y :: h) i

open MWG.DynamicGames BargainingGame in
/-- **Exercise 22.E.11(c)** (MWG, p. 854; Definition 9.B.2 for the bargaining game with utility
payoffs). A subgame perfect Nash equilibrium: at every feasible proposal node within the horizon
and at every response node to a feasible offer, no player gains (in utility) by deviating to any
feasible strategy. -/
def UIsSPNE (B : BargainingGame) (u : Fin 2 → ℝ → ℝ) (σ : BargainingProfile) : Prop :=
  B.Feasible σ ∧ ∀ i σ', B.Feasible σ' → IsDeviation i σ σ' → ∀ h, B.ValidHist h →
    B.Live h.length → uValue B u σ' h i ≤ uValue B u σ h i ∧
      ∀ y ∈ Set.Icc 0 B.v, uRespValue B u σ' h y i ≤ uRespValue B u σ h y i

open MWG.DynamicGames BargainingGame in
/-- **Exercise 22.E.11(c)** (MWG, p. 854). The stationary profile with proposer shares `s`: the
proposer `p` offers `v - s p`, the responder accepts exactly the offers `y ≥ v - s p`. -/
noncomputable def statProfile (B : BargainingGame) (s : Fin 2 → ℝ) : BargainingProfile :=
  threshold fun t => B.v - s (proposer t)

/-- **Exercise 22.E.11(c)** (MWG, p. 854). The proposer shares of the stationary configuration
`(x, w)`: agent 1 proposing keeps `x`, agent 2 proposing keeps `m - w`. -/
def stShares (B : MWG.DynamicGames.BargainingGame) (x w : ℝ) : Fin 2 → ℝ :=
  fun i => if i = 0 then x else B.v - w

open MWG.DynamicGames BargainingGame in
/-- **Exercise 22.E.11(c)** (MWG, p. 854). The utility payoffs of the proposer in SPNE, over all
SPNE and all feasible histories at which `i` proposes. -/
def uSpnePayoffs (B : BargainingGame) (u : Fin 2 → ℝ → ℝ) (i : Fin 2) : Set ℝ :=
  {z | ∃ σ, UIsSPNE B u σ ∧ ∃ h, B.ValidHist h ∧ proposer h.length = i ∧ z = uValue B u σ h i}

variable {B : MWG.DynamicGames.BargainingGame} (u : Fin 2 → ℝ → ℝ)

open MWG.DynamicGames BargainingGame Classical in
theorem uValue_of_exists {σ : BargainingProfile} {h : List ℝ} (hx : ∃ t, B.Agrees σ h t)
    (i : Fin 2) : uValue B u σ h i = B.δ i ^ Nat.find hx *
      u i (B.share i (h.length + Nat.find hx) (σ.prop (path σ h (Nat.find hx)))) := by
  unfold uValue
  split_ifs
  rfl

open MWG.DynamicGames BargainingGame in
theorem uValue_of_not_exists {σ : BargainingProfile} {h : List ℝ}
    (hx : ¬ ∃ t, B.Agrees σ h t) (i : Fin 2) : uValue B u σ h i = 0 := by
  unfold uValue
  split_ifs
  rfl

open MWG.DynamicGames BargainingGame in
theorem uRespValue_accept {σ : BargainingProfile} {h : List ℝ} {y : ℝ} (hl : B.Live h.length)
    (hy : σ.resp h y = true) (i : Fin 2) :
    uRespValue B u σ h y i = u i (B.share i h.length y) := by
  unfold uRespValue
  split_ifs with hc
  · rfl
  · exact absurd ⟨hl, hy⟩ hc

open MWG.DynamicGames BargainingGame in
theorem uRespValue_reject {σ : BargainingProfile} {h : List ℝ} {y : ℝ}
    (hy : σ.resp h y = false) (i : Fin 2) :
    uRespValue B u σ h y i = B.δ i * uValue B u σ (y :: h) i := by
  unfold uRespValue
  split_ifs with hc
  · simp [hy] at hc
  · rfl

open MWG.DynamicGames BargainingGame in
/-- The utility value at a proposal node is the value at the response node to the offer made
there. -/
theorem uValue_eq_uRespValue (σ : BargainingProfile) {h : List ℝ} (hl : B.Live h.length)
    (i : Fin 2) : uValue B u σ h i = uRespValue B u σ h (σ.prop h) i := by
  classical
  have hshift : ∀ t, B.Agrees σ h (t + 1) ↔ B.Agrees σ (σ.prop h :: h) t := by
    intro t
    simp only [Agrees, path_succ, List.length_cons,
      show h.length + (t + 1) = h.length + 1 + t by omega]
  by_cases h0 : σ.resp h (σ.prop h) = true
  · have hA : B.Agrees σ h 0 := ⟨by simpa using hl, by simpa [path] using h0⟩
    have hx : ∃ t, B.Agrees σ h t := ⟨0, hA⟩
    rw [uValue_of_exists u hx, uRespValue_accept u hl h0]
    have hf : Nat.find hx = 0 := (Nat.find_eq_zero hx).2 hA
    simp only [hf, pow_zero, one_mul, add_zero, path]
  · have h0' : σ.resp h (σ.prop h) = false := by simpa using h0
    rw [uRespValue_reject u h0']
    have hA0 : ¬ B.Agrees σ h 0 := fun h' => h0 (by simpa [path] using h'.2)
    by_cases hx' : ∃ t, B.Agrees σ (σ.prop h :: h) t
    · have hx : ∃ t, B.Agrees σ h t := let ⟨t, ht⟩ := hx'; ⟨t + 1, (hshift t).2 ht⟩
      have hx2 : ∃ t, B.Agrees σ h (t + 1) := let ⟨t, ht⟩ := hx'; ⟨t, (hshift t).2 ht⟩
      have hf : Nat.find hx = Nat.find hx' + 1 := by
        rw [Nat.find_comp_succ hx hx2 hA0]
        congr 1
        exact Nat.find_congr' (hshift _)
      rw [uValue_of_exists u hx, uValue_of_exists u hx', hf, path_succ, pow_succ]
      simp only [List.length_cons, show h.length + (Nat.find hx' + 1) =
        h.length + 1 + Nat.find hx' by omega]
      ring
    · have hx : ¬ ∃ t, B.Agrees σ h t := by
        rintro ⟨t, ht⟩
        cases t with
        | zero => exact hA0 ht
        | succ t => exact hx' ⟨t, (hshift t).1 ht⟩
      rw [uValue_of_not_exists u hx, uValue_of_not_exists u hx', mul_zero]

open MWG.DynamicGames BargainingGame in
/-- The utility value from `h` depends only on the moves at histories at least as long as `h`. -/
theorem uValue_congr {σ σ' : BargainingProfile} {h : List ℝ}
    (hp : ∀ h', h.length ≤ h'.length → σ.prop h' = σ'.prop h')
    (hr : ∀ h' y, h.length ≤ h'.length → σ.resp h' y = σ'.resp h' y) (i : Fin 2) :
    uValue B u σ h i = uValue B u σ' h i := by
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
    rw [uValue_of_exists u hx, uValue_of_exists u hx']
    have hf : Nat.find hx = Nat.find hx' := Nat.find_congr' (hA _)
    rw [hf, hpath, hp _ (by rw [length_path]; omega)]
  · have hx' : ¬ ∃ t, B.Agrees σ' h t := fun ⟨t, ht⟩ => hx ⟨t, (hA t).2 ht⟩
    rw [uValue_of_not_exists u hx, uValue_of_not_exists u hx']

open MWG.DynamicGames BargainingGame in
theorem setResp_uValue (σ : BargainingProfile) (h₀ : List ℝ) (y₀ : ℝ) (b : Bool) (i : Fin 2) :
    uValue B u (setResp σ h₀ y₀ b) (y₀ :: h₀) i = uValue B u σ (y₀ :: h₀) i := by
  refine uValue_congr u (σ := setResp σ h₀ y₀ b) (σ' := σ) (fun _ _ => rfl)
    (fun h' y hl => ?_) i
  have : h' ≠ h₀ := fun he => by rw [he] at hl; simp at hl
  simp [setResp, this]

open MWG.DynamicGames BargainingGame in
theorem setProp_uValue (σ : BargainingProfile) (h₀ : List ℝ) (y₀ y : ℝ) (i : Fin 2) :
    uValue B u (setProp σ h₀ y₀) (y :: h₀) i = uValue B u σ (y :: h₀) i := by
  refine uValue_congr u (σ := setProp σ h₀ y₀) (σ' := σ) (fun h' hl => ?_)
    (fun _ _ _ => rfl) i
  have : h' ≠ h₀ := fun he => by rw [he] at hl; simp at hl
  simp [setProp, this]

open MWG.DynamicGames BargainingGame in
theorem uShare_of_proposer {t : ℕ} {i : Fin 2} (hp : proposer t = i) (y : ℝ) :
    B.share i t y = B.v - y := by
  simp [BargainingGame.share, hp]

open MWG.DynamicGames BargainingGame in
theorem uShare_of_responder {t : ℕ} {i : Fin 2} (hp : proposer t ≠ i) (y : ℝ) :
    B.share i t y = y := by
  simp [BargainingGame.share, hp]

open MWG.DynamicGames BargainingGame Classical in
/-- Utility payoffs of a feasible profile are nonnegative when the utilities are nonnegative on
`[0, v]`. -/
theorem uValue_nonneg {σ : BargainingProfile} (hσ : B.Feasible σ)
    (hu : ∀ i, ∀ z ∈ Set.Icc 0 B.v, 0 ≤ u i z) (h : List ℝ) (i : Fin 2) :
    0 ≤ uValue B u σ h i := by
  by_cases hx : ∃ t, B.Agrees σ h t
  · rw [uValue_of_exists u hx]
    exact mul_nonneg (pow_nonneg (B.δ_pos i).le _) (hu i _ (B.share_mem i _ (hσ _)))
  · rw [uValue_of_not_exists u hx]

open MWG.DynamicGames BargainingGame Classical in
/-- Utility payoffs are at most `uᵢ(v)`. -/
theorem uValue_le_top {σ : BargainingProfile} (hσ : B.Feasible σ)
    (hu : ∀ i, ∀ z ∈ Set.Icc 0 B.v, 0 ≤ u i z) {i : Fin 2}
    (hmono : MonotoneOn (u i) (Set.Icc 0 B.v)) (h : List ℝ) :
    uValue B u σ h i ≤ u i B.v := by
  have hvv : B.v ∈ Set.Icc 0 B.v := ⟨B.v_pos.le, le_rfl⟩
  by_cases hx : ∃ t, B.Agrees σ h t
  · rw [uValue_of_exists u hx]
    have hs := B.share_mem i (h.length + Nat.find hx) (hσ (path σ h (Nat.find hx)))
    have h1 := hu i _ hs
    have h2 := hmono hs hvv hs.2
    have hd : B.δ i ^ Nat.find hx ≤ 1 := pow_le_one₀ (B.δ_pos i).le (B.δ_lt_one i).le
    exact (mul_le_of_le_one_left h1 hd).trans h2
  · rw [uValue_of_not_exists u hx]
    exact hu i _ hvv

open MWG.DynamicGames BargainingGame Classical in
/-- **The utility frontier.** If the other player gets at least `u_j(z)`, player `i` gets at most
`uᵢ(v - z)`. -/
theorem uValue_frontier {σ : BargainingProfile} (hσ : B.Feasible σ)
    (hu : ∀ i, ∀ z ∈ Set.Icc 0 B.v, 0 ≤ u i z) {i : Fin 2}
    (hmono : MonotoneOn (u i) (Set.Icc 0 B.v))
    (hstr : StrictMonoOn (u (other i)) (Set.Icc 0 B.v)) (h : List ℝ) {z : ℝ}
    (hz : z ∈ Set.Icc 0 B.v) (hle : u (other i) z ≤ uValue B u σ h (other i)) :
    uValue B u σ h i ≤ u i (B.v - z) := by
  have hvz : B.v - z ∈ Set.Icc 0 B.v := ⟨by linarith [hz.2], by linarith [hz.1]⟩
  by_cases hx : ∃ t, B.Agrees σ h t
  · rw [uValue_of_exists u hx] at hle ⊢
    set T := Nat.find hx
    set y := σ.prop (path σ h T)
    have hy := hσ (path σ h T)
    have hj := B.share_mem (other i) (h.length + T) hy
    have hi := B.share_mem i (h.length + T) hy
    have hadd := B.share_add i (h.length + T) y
    have hd1 : B.δ (other i) ^ T ≤ 1 := pow_le_one₀ (B.δ_pos _).le (B.δ_lt_one _).le
    have hd2 : B.δ i ^ T ≤ 1 := pow_le_one₀ (B.δ_pos _).le (B.δ_lt_one _).le
    have hu1 := hu (other i) _ hj
    have hu2 := hu i _ hi
    have hz1 : u (other i) z ≤ u (other i) (B.share (other i) (h.length + T) y) :=
      hle.trans (mul_le_of_le_one_left hu1 hd1)
    have hzs : z ≤ B.share (other i) (h.length + T) y := (hstr.le_iff_le hz hj).1 hz1
    have h3 : u i (B.share i (h.length + T) y) ≤ u i (B.v - z) :=
      hmono hi hvz (by linarith)
    exact (mul_le_of_le_one_left hu2 hd2).trans h3
  · rw [uValue_of_not_exists u hx]
    exact hu i _ hvz

open MWG.DynamicGames BargainingGame in
/-- In an SPNE the responder accepts an offer whose utility beats her discounted continuation. -/
theorem u_accept_of_gt {σ : BargainingProfile} (hσ : UIsSPNE B u σ) {h : List ℝ}
    (hvh : B.ValidHist h) (hl : B.Live h.length) {y : ℝ} (hy : y ∈ Set.Icc 0 B.v)
    (hgt : B.δ (other (proposer h.length)) *
      uValue B u σ (y :: h) (other (proposer h.length)) < u (other (proposer h.length)) y) :
    σ.resp h y = true := by
  by_contra hrej
  have hrej' : σ.resp h y = false := by simpa using hrej
  have := (hσ.2 _ _ (B.setResp_feasible hσ.1 h y true) (setResp_isDeviation σ h y true) h hvh
    hl).2 y hy
  rw [uRespValue_accept u hl (by simp [setResp]), uRespValue_reject u hrej',
    share_other] at this
  linarith

open MWG.DynamicGames BargainingGame in
/-- In an SPNE the responder rejects an offer below her discounted continuation. -/
theorem u_reject_of_lt {σ : BargainingProfile} (hσ : UIsSPNE B u σ) {h : List ℝ}
    (hvh : B.ValidHist h) (hl : B.Live h.length) {y : ℝ} (hy : y ∈ Set.Icc 0 B.v)
    (hlt : u (other (proposer h.length)) y < B.δ (other (proposer h.length)) *
      uValue B u σ (y :: h) (other (proposer h.length))) :
    σ.resp h y = false := by
  by_contra hacc
  have hacc' : σ.resp h y = true := by simpa using hacc
  have := (hσ.2 _ _ (B.setResp_feasible hσ.1 h y false) (setResp_isDeviation σ h y false) h hvh
    hl).2 y hy
  rw [uRespValue_reject u (by simp [setResp]), setResp_uValue, uRespValue_accept u hl hacc',
    share_other] at this
  linarith

open MWG.DynamicGames BargainingGame in
/-- In an SPNE the proposer does at least as well as with any other feasible offer. -/
theorem u_respValue_le_value {σ : BargainingProfile} (hσ : UIsSPNE B u σ) {h : List ℝ}
    (hvh : B.ValidHist h) (hl : B.Live h.length) {y : ℝ} (hy : y ∈ Set.Icc 0 B.v) :
    uRespValue B u σ h y (proposer h.length) ≤ uValue B u σ h (proposer h.length) := by
  have := (hσ.2 _ _ (B.setProp_feasible hσ.1 h hy) (setProp_isDeviation σ h y) h hvh hl).1
  rw [uValue_eq_uRespValue u _ hl] at this
  have hp : (setProp σ h y).prop h = y := by simp [setProp]
  rw [hp] at this
  unfold uRespValue at this ⊢
  rw [setProp_uValue] at this
  exact this

open MWG.DynamicGames BargainingGame in
/-- **Discounted one-stage deviation bound, utility payoffs.** If `bnd ≥ 0` bounds player `i`'s
utility of an immediate agreement at every live node, and `δ_i bnd(next) ≤ bnd` after every
rejection, then `bnd` bounds player `i`'s utility payoff from every node. -/
theorem uValue_le_of_bound {σ : BargainingProfile} {i : Fin 2} (bnd : List ℝ → ℝ)
    (h0 : ∀ h, 0 ≤ bnd h)
    (hacc : ∀ h, B.Live h.length → σ.resp h (σ.prop h) = true →
      u i (B.share i h.length (σ.prop h)) ≤ bnd h)
    (hrej : ∀ h, B.Live h.length → σ.resp h (σ.prop h) = false →
      B.δ i * bnd (σ.prop h :: h) ≤ bnd h)
    (h : List ℝ) : uValue B u σ h i ≤ bnd h := by
  classical
  have key : ∀ T h, (∀ s < T, ¬ B.Agrees σ h s) → B.Agrees σ h T →
      B.δ i ^ T * u i (B.share i (h.length + T) (σ.prop (path σ h T))) ≤ bnd h := by
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
      calc B.δ i ^ T * B.δ i * u i (B.share i ((σ.prop h :: h).length + T)
            (σ.prop (path σ (σ.prop h :: h) T)))
          = B.δ i * (B.δ i ^ T * u i (B.share i ((σ.prop h :: h).length + T)
            (σ.prop (path σ (σ.prop h :: h) T)))) := by ring
        _ ≤ B.δ i * bnd (σ.prop h :: h) := mul_le_mul_of_nonneg_left this hδ
        _ ≤ bnd h := hrej h hl hrej0
  by_cases hx : ∃ t, B.Agrees σ h t
  · rw [uValue_of_exists u hx]
    exact key _ h (fun s hs => Nat.find_min hx hs) (Nat.find_spec hx)
  · rw [uValue_of_not_exists u hx]
    exact h0 h

open MWG.DynamicGames BargainingGame in
/-- Payoffs of the stationary profile from a live node: immediate agreement on the offer
`v - s p`. -/
theorem statProfile_uValue (s : Fin 2 → ℝ) {h : List ℝ} (hl : B.Live h.length) (i : Fin 2) :
    uValue B u (statProfile B s) h i =
      u i (B.share i h.length (B.v - s (proposer h.length))) := by
  have hacc : (statProfile B s).resp h ((statProfile B s).prop h) = true := by
    simp [statProfile, threshold]
  rw [uValue_eq_uRespValue u _ hl, uRespValue_accept u hl hacc]
  rfl

open MWG.DynamicGames BargainingGame in
/-- **Exercise 22.E.11(c)**, stationary SPNE (MWG, p. 854). In the infinite horizon game, let
`s i ∈ [0, v]` be player `i`'s stationary proposer share, and suppose that each player's
stationary responder utility is `δ_i` times her proposer utility:
`uᵢ(v - s_j) = δ_i uᵢ(s_i)`. With utilities nonnegative and increasing on `[0, v]`, the stationary
profile (proposer `p` offers `v - s p`; the responder accepts exactly the offers `y ≥ v - s p`)
is a subgame perfect Nash equilibrium. -/
theorem statProfile_isSPNE (hT : B.T = ⊤) {s : Fin 2 → ℝ} (hs : ∀ i, s i ∈ Set.Icc 0 B.v)
    (hu : ∀ i, ∀ z ∈ Set.Icc 0 B.v, 0 ≤ u i z)
    (hmono : ∀ i, MonotoneOn (u i) (Set.Icc 0 B.v))
    (hrel : ∀ i, u i (B.v - s (other i)) = B.δ i * u i (s i)) :
    UIsSPNE B u (statProfile B s) := by
  classical
  have hc0 : ∀ t, B.v - s (proposer t) ∈ Set.Icc 0 B.v := fun t =>
    ⟨by linarith [(hs (proposer t)).2], by linarith [(hs (proposer t)).1]⟩
  refine ⟨fun h => hc0 h.length, fun i σ' hσ' hdev h hvh hl => ?_⟩
  let bnd : List ℝ → ℝ := fun h => u i (B.share i h.length (B.v - s (proposer h.length)))
  have hval : ∀ h, uValue B u (statProfile B s) h i = bnd h := fun h =>
    statProfile_uValue u s (B.live_of_top hT _) i
  have hbnd0 : ∀ h, 0 ≤ bnd h := fun h => hu i _ (B.share_mem i _ (hc0 h.length))
  have hδi := B.δ_pos i
  have hδi1 := B.δ_lt_one i
  have hsi := hu i _ (hs i)
  -- one period: the responder's stationary utility is `δ` times her proposer utility
  have hstep : ∀ t, B.δ i * u i (B.share i (t + 1) (B.v - s (proposer (t + 1)))) ≤
      u i (B.share i t (B.v - s (proposer t))) ∧
      (proposer t ≠ i → B.δ i * u i (B.share i (t + 1) (B.v - s (proposer (t + 1)))) =
        u i (B.share i t (B.v - s (proposer t)))) := by
    intro t
    have hsucc := proposer_succ t
    rcases eq_or_eq_other i (proposer t) with hp | hp
    · rw [uShare_of_proposer hp, uShare_of_responder (by rw [hsucc, hp]; exact other_ne i),
        hsucc, hp, hrel i, sub_sub_cancel]
      refine ⟨?_, fun h => absurd rfl h⟩
      have h2 := mul_le_of_le_one_left (mul_nonneg hδi.le hsi) hδi1.le
      linarith [mul_le_of_le_one_left hsi hδi1.le]
    · have h1 : proposer (t + 1) = i := by rw [hsucc, hp, other_other]
      rw [uShare_of_proposer h1, uShare_of_responder (by rw [hp]; exact other_ne i), h1, hp,
        sub_sub_cancel, hrel i]
      exact ⟨le_rfl, fun _ => rfl⟩
  -- the deviation's value is bounded by the stationary value
  have hle : ∀ h, uValue B u σ' h i ≤ bnd h := by
    refine uValue_le_of_bound u bnd hbnd0 (fun h hl hacc => ?_) (fun h _ _ => ?_)
    · by_cases hp : proposer h.length = i
      · have hr : σ'.resp h (σ'.prop h) = (statProfile B s).resp h (σ'.prop h) :=
          hdev.2 h _ hp
        rw [hacc] at hr
        have hr' : B.v - s (proposer h.length) ≤ σ'.prop h := by
          simpa [statProfile, threshold] using hr.symm
        have hy := hσ' h
        change u i (B.share i h.length (σ'.prop h)) ≤
          u i (B.share i h.length (B.v - s (proposer h.length)))
        rw [uShare_of_proposer hp, uShare_of_proposer hp]
        exact hmono i ⟨by linarith [hy.2], by linarith [hy.1]⟩
          ⟨by linarith [(hc0 h.length).2], by linarith [(hc0 h.length).1]⟩ (by linarith)
      · have hpr : σ'.prop h = (statProfile B s).prop h := hdev.1 h hp
        rw [hpr]
        exact le_rfl
    · exact (hstep h.length).1
  refine ⟨by rw [hval]; exact hle h, fun y hy => ?_⟩
  have hyh : uValue B u σ' (y :: h) i ≤ uValue B u (statProfile B s) (y :: h) i := by
    rw [hval]; exact hle _
  by_cases hp : proposer h.length = i
  · have hr : σ'.resp h y = (statProfile B s).resp h y := hdev.2 h y hp
    unfold uRespValue
    rw [hr]
    split_ifs
    · exact le_rfl
    · exact mul_le_mul_of_nonneg_left hyh hδi.le
  · have hcont : B.δ i * uValue B u (statProfile B s) (y :: h) i =
        u i (B.v - s (proposer h.length)) := by
      rw [hval]
      have := (hstep h.length).2 hp
      rw [uShare_of_responder hp] at this
      exact this
    have hthr : max (u i y) (u i (B.v - s (proposer h.length))) ≤
        uRespValue B u (statProfile B s) h y i := by
      by_cases hyc : B.v - s (proposer h.length) ≤ y
      · rw [uRespValue_accept u hl (by simp [statProfile, threshold]; linarith),
          uShare_of_responder hp]
        exact max_le le_rfl (hmono i (hc0 _) hy hyc)
      · rw [uRespValue_reject u (by simp [statProfile, threshold]; linarith [not_le.1 hyc]),
          hcont]
        exact max_le (hmono i hy (hc0 _) (le_of_lt (not_le.1 hyc))) le_rfl
    refine le_trans ?_ hthr
    unfold uRespValue
    split_ifs
    · rw [uShare_of_responder hp]
      exact le_max_left _ _
    · calc B.δ i * uValue B u σ' (y :: h) i
          ≤ B.δ i * uValue B u (statProfile B s) (y :: h) i :=
            mul_le_mul_of_nonneg_left hyh hδi.le
        _ = u i (B.v - s (proposer h.length)) := hcont
        _ ≤ _ := le_max_right _ _

open MWG.DynamicGames BargainingGame in
/-- **Shaked-Sutton lower bound in utility space** (MWG, p. 298, Exercise 22.E.11(c)). In an
SPNE, if the responder `r` expects at most `M` as the next proposer after any rejection, then
every offer `y` with `δ_r M < u_r(y)` is accepted, so the proposer `p` earns at least
`u_p(v - y)`. -/
theorem uValue_ge_of_uIsSPNE {σ : BargainingProfile} (hσ : UIsSPNE B u σ) {h : List ℝ}
    (hvh : B.ValidHist h) (hl : B.Live h.length) {M : ℝ}
    (hM : ∀ y ∈ Set.Icc 0 B.v, uValue B u σ (y :: h) (other (proposer h.length)) ≤ M)
    {y : ℝ} (hy : y ∈ Set.Icc 0 B.v)
    (hgt : B.δ (other (proposer h.length)) * M < u (other (proposer h.length)) y) :
    u (proposer h.length) (B.v - y) ≤ uValue B u σ h (proposer h.length) := by
  have hacc : σ.resp h y = true := by
    refine u_accept_of_gt u hσ hvh hl hy ?_
    have := mul_le_mul_of_nonneg_left (hM y hy) (B.δ_pos (other (proposer h.length))).le
    linarith
  have := u_respValue_le_value u hσ hvh hl hy
  rwa [uRespValue_accept u hl hacc, share_proposer] at this

open MWG.DynamicGames BargainingGame in
/-- **Shaked-Sutton upper bound in utility space** (MWG, p. 298, Exercise 22.E.11(c)). In an
SPNE, if the responder `r` expects at least `m` as the next proposer after any rejection, and
`u_r(q) ≤ δ_r m`, then the proposer `p` earns at most `u_p(v - q)`: an accepted offer `y` has
`u_r(y) ≥ δ_r m ≥ u_r(q)`, and after a rejection the utility frontier caps `p`'s payoff. -/
theorem uValue_le_of_uIsSPNE {σ : BargainingProfile} (hσ : UIsSPNE B u σ) {h : List ℝ}
    (hvh : B.ValidHist h) (hl : B.Live h.length) (hu : ∀ i, ∀ z ∈ Set.Icc 0 B.v, 0 ≤ u i z)
    (hmono : MonotoneOn (u (proposer h.length)) (Set.Icc 0 B.v))
    (hstr : StrictMonoOn (u (other (proposer h.length))) (Set.Icc 0 B.v)) {mm : ℝ}
    (hm : ∀ y ∈ Set.Icc 0 B.v, mm ≤ uValue B u σ (y :: h) (other (proposer h.length)))
    {q : ℝ} (hq : q ∈ Set.Icc 0 B.v)
    (hqm : u (other (proposer h.length)) q ≤ B.δ (other (proposer h.length)) * mm) :
    uValue B u σ h (proposer h.length) ≤ u (proposer h.length) (B.v - q) := by
  set p := proposer h.length
  set r := other p
  set y := σ.prop h
  have hy := hσ.1 h
  have hδr := B.δ_pos r
  have hδr1 := B.δ_lt_one r
  have hδp := B.δ_pos p
  have hδp1 := B.δ_lt_one p
  have hmm0 : 0 ≤ mm := by nlinarith [hu r q hq]
  have hvq : B.v - q ∈ Set.Icc 0 B.v := ⟨by linarith [hq.2], by linarith [hq.1]⟩
  rw [uValue_eq_uRespValue u σ hl]
  cases hacc : σ.resp h y with
  | true =>
    rw [uRespValue_accept u hl hacc, share_proposer]
    have hge : B.δ r * uValue B u σ (y :: h) r ≤ u r y := by
      by_contra hlt
      push Not at hlt
      have := u_reject_of_lt u hσ hvh hl hy hlt
      rw [hacc] at this
      exact Bool.noConfusion this
    have h1 := mul_le_mul_of_nonneg_left (hm y hy) hδr.le
    have hqy : q ≤ y := (hstr.le_iff_le hq hy).1 (by linarith)
    exact hmono ⟨by linarith [hy.2], by linarith [hy.1]⟩ hvq (by linarith)
  | false =>
    rw [uRespValue_reject u hacc]
    have hm' : u r q ≤ uValue B u σ (y :: h) r := by
      have := hm y hy
      nlinarith
    have hfr := uValue_frontier u hσ.1 hu hmono hstr (y :: h) hq hm'
    have h0 := uValue_nonneg u hσ.1 hu (y :: h) p
    nlinarith

/-- **Knaster-Tarski with a unique fixed point.** For `T` monotone on `[0, v]` (into `[0, v]`)
with a unique fixed point `xs`, every `x ≤ T x` lies below `xs` and every `T x ≤ x` above it. -/
theorem fixed_point_bounds {T : ℝ → ℝ} {v : ℝ} (hv0 : 0 ≤ v)
    (hTm : ∀ x ∈ Set.Icc 0 v, T x ∈ Set.Icc 0 v)
    (hmono : ∀ x ∈ Set.Icc 0 v, ∀ y ∈ Set.Icc 0 v, x ≤ y → T x ≤ T y)
    (huniq : ∀ x ∈ Set.Icc 0 v, ∀ y ∈ Set.Icc 0 v, T x = x → T y = y → x = y) {xs : ℝ}
    (hxs : xs ∈ Set.Icc 0 v) (hfix : T xs = xs) {x : ℝ} (hx : x ∈ Set.Icc 0 v) :
    (x ≤ T x → x ≤ xs) ∧ (T x ≤ x → xs ≤ x) := by
  have h0 : (0 : ℝ) ∈ Set.Icc 0 v := ⟨le_rfl, hv0⟩
  have hv : v ∈ Set.Icc 0 v := ⟨hv0, le_rfl⟩
  constructor
  · intro hle
    set S := {z | z ∈ Set.Icc 0 v ∧ z ≤ T z}
    have hS0 : (0 : ℝ) ∈ S := ⟨h0, (hTm 0 h0).1⟩
    have hSb : BddAbove S := ⟨v, fun z hz => hz.1.2⟩
    have hsm : sSup S ∈ Set.Icc 0 v := ⟨le_csSup hSb hS0, csSup_le ⟨0, hS0⟩ fun z hz => hz.1.2⟩
    have h1 : sSup S ≤ T (sSup S) := csSup_le ⟨0, hS0⟩ fun z hz =>
      hz.2.trans (hmono z hz.1 _ hsm (le_csSup hSb hz))
    have h2 : T (sSup S) ≤ sSup S := le_csSup hSb ⟨hTm _ hsm, hmono _ hsm _ (hTm _ hsm) h1⟩
    have := huniq _ hsm _ hxs (le_antisymm h2 h1) hfix
    rw [← this]
    exact le_csSup hSb ⟨hx, hle⟩
  · intro hle
    set S := {z | z ∈ Set.Icc 0 v ∧ T z ≤ z}
    have hSv : v ∈ S := ⟨hv, (hTm v hv).2⟩
    have hSb : BddBelow S := ⟨0, fun z hz => hz.1.1⟩
    have hsm : sInf S ∈ Set.Icc 0 v := ⟨le_csInf ⟨v, hSv⟩ fun z hz => hz.1.1, csInf_le hSb hSv⟩
    have h1 : T (sInf S) ≤ sInf S := le_csInf ⟨v, hSv⟩ fun z hz =>
      (hmono _ hsm z hz.1 (csInf_le hSb hz)).trans hz.2
    have h2 : sInf S ≤ T (sInf S) := csInf_le hSb ⟨hTm _ hsm, hmono _ (hTm _ hsm) _ hsm h1⟩
    have := huniq _ hsm _ hxs (le_antisymm h1 h2) hfix
    rw [← this]
    exact csInf_le hSb ⟨hx, hle⟩

open MWG.DynamicGames BargainingGame in
/-- **Exercise 22.E.11(c)** (MWG, p. 854). The stationary configuration `(x, w)` gives the shares
`s = stShares B x w` the stationary relations `uᵢ(v - s_j) = δ uᵢ(s_i)` (responder utility is `δ`
times proposer utility), and `0 < s i ≤ v`. -/
theorem stShares_spec (hδ : B.δ 0 = B.δ 1) (hD : RubinsteinData (u 0) (u 1) B.v (B.δ 0))
    {x w : ℝ} (hs : IsStationary (u 0) (u 1) B.v (B.δ 0) x w) :
    (∀ i, stShares B x w i ∈ Set.Icc 0 B.v ∧ 0 < stShares B x w i) ∧
      ∀ i, u i (B.v - stShares B x w (other i)) = B.δ i * u i (stShares B x w i) := by
  obtain ⟨hw0, hwx, hxm⟩ := stationary_interior hD hs
  have e0 : stShares B x w 0 = x := rfl
  have e1 : stShares B x w 1 = B.v - w := rfl
  have ho0 : other 0 = 1 := rfl
  have ho1 : other 1 = 0 := rfl
  refine ⟨Fin.forall_fin_two.2 ⟨?_, ?_⟩, Fin.forall_fin_two.2 ⟨?_, ?_⟩⟩
  · rw [e0]; exact ⟨⟨by linarith, by linarith⟩, by linarith⟩
  · rw [e1]; exact ⟨⟨by linarith, by linarith⟩, by linarith⟩
  · rw [ho0, e0, e1, sub_sub_cancel]; exact hs.2.2.2.2.2
  · rw [ho1, e0, e1, ← hδ]; exact hs.2.2.2.2.1

open MWG.DynamicGames BargainingGame in
/-- **Exercise 22.E.11(c)** (MWG, p. 854): every SPNE is stationary in outcome. With a common
discount factor `δ`, utilities `u₁ = u 0`, `u₂ = u 1` increasing, concave and continuous on
`[0, m]` with `uᵢ(0) = 0`, and `(x, w)` the stationary configuration, in every SPNE of the
infinite-horizon alternating-offer game, at every feasible history `h` with proposer `p`:
the proposer offers `v - s p`, it is accepted, the proposer's utility is `u_p(s p)` and the
responder's `u_r(v - s p)` (`s = stShares B x w`: agent 1 keeps `x`, agent 2 keeps `m - w`).

Shaked-Sutton in utility space: let `M i`, `m i` be the sup and inf of player `i`'s SPNE proposer
utilities and `p⁺`, `p⁻`, `r⁺`, `r⁻` the shares with these utilities. The bounds
`uValue_ge_of_uIsSPNE` (with continuity) and `uValue_le_of_uIsSPNE` give `p⁺ ≤ T p⁺` and
`T p⁻ ≤ p⁻` for the monotone map `T x = v - g₂(v - g₁ x)` (`uᵢ(gᵢ z) = δuᵢ(z)`), whose fixed
points are the stationary configurations; by `exercise_22_E_11a` it has the single fixed point
`x`, so `p⁺ ≤ x ≤ p⁻ ≤ p⁺` (`fixed_point_bounds`). -/
theorem uSPNE_unique (hT : B.T = ⊤) (hδ : B.δ 0 = B.δ 1)
    (hD : RubinsteinData (u 0) (u 1) B.v (B.δ 0)) (hc : ∀ k, ContinuousOn (u k) (Set.Icc 0 B.v))
    {x w : ℝ} (hs : IsStationary (u 0) (u 1) B.v (B.δ 0) x w) :
    ∀ σ, UIsSPNE B u σ → ∀ h, B.ValidHist h →
      σ.prop h = B.v - stShares B x w (proposer h.length) ∧ σ.resp h (σ.prop h) = true ∧
      uValue B u σ h (proposer h.length) =
        u (proposer h.length) (stShares B x w (proposer h.length)) ∧
      uValue B u σ h (other (proposer h.length)) =
        u (other (proposer h.length)) (B.v - stShares B x w (proposer h.length)) := by
  classical
  have hall : ∀ k, B.δ k = B.δ 0 := Fin.forall_fin_two.2 ⟨rfl, hδ.symm⟩
  have hvpos := B.v_pos
  have hδ0 := B.δ_pos 0
  have hδ1 := B.δ_lt_one 0
  obtain ⟨hw0, hwx, hxm⟩ := stationary_interior hD hs
  have hstr : ∀ k, StrictMonoOn (u k) (Set.Icc 0 B.v) := Fin.forall_fin_two.2 ⟨hD.mono₁, hD.mono₂⟩
  have hmono : ∀ k, MonotoneOn (u k) (Set.Icc 0 B.v) := fun k => (hstr k).monotoneOn
  have hzero : ∀ k, u k 0 = 0 := Fin.forall_fin_two.2 ⟨hD.zero₁, hD.zero₂⟩
  have hvI : B.v ∈ Set.Icc 0 B.v := ⟨hvpos.le, le_rfl⟩
  have h0I : (0 : ℝ) ∈ Set.Icc 0 B.v := ⟨le_rfl, hvpos.le⟩
  have hu : ∀ k, ∀ z ∈ Set.Icc 0 B.v, 0 ≤ u k z := fun k z hz => by
    have := hmono k h0I hz hz.1; rwa [hzero] at this
  have hupos : ∀ k, ∀ z, 0 < z → z ≤ B.v → 0 < u k z := fun k z hz hzv => by
    have := hstr k h0I ⟨hz.le, hzv⟩ hz; rwa [hzero] at this
  have hflip : ∀ z ∈ Set.Icc 0 B.v, B.v - z ∈ Set.Icc 0 B.v := fun z hz =>
    ⟨by linarith [hz.2], by linarith [hz.1]⟩
  set s := stShares B x w with hsdef
  obtain ⟨hs0, hrel⟩ := stShares_spec u hδ hD hs
  have ho0 : other 0 = 1 := rfl
  have ho1 : other 1 = 0 := rfl
  -- the stationary profile is an SPNE
  have hstat : UIsSPNE B u (statProfile B s) :=
    statProfile_isSPNE u hT (fun i => (hs0 i).1) hu hmono hrel
  -- the sets of SPNE proposer payoffs
  set S := uSpnePayoffs B u with hSdef
  have hbdd : ∀ k, BddAbove (S k) ∧ BddBelow (S k) := fun k =>
    ⟨⟨u k B.v, fun z ⟨σ, hσ, h, _, _, hz⟩ => by
      rw [hz]; exact uValue_le_top u hσ.1 hu (hmono k) h⟩,
    ⟨0, fun z ⟨σ, hσ, h, _, _, hz⟩ => by rw [hz]; exact uValue_nonneg u hσ.1 hu h k⟩⟩
  have hne : ∀ k, (S k).Nonempty := Fin.forall_fin_two.2
    ⟨⟨_, statProfile B s, hstat, [], fun _ h => absurd h List.not_mem_nil, rfl, rfl⟩,
     ⟨_, statProfile B s, hstat, [0], B.validHist_cons (fun _ h => absurd h List.not_mem_nil)
        h0I, rfl, rfl⟩⟩
  set M : Fin 2 → ℝ := fun k => sSup (S k) with hMdef
  set m : Fin 2 → ℝ := fun k => sInf (S k) with hmdef
  have hmM : ∀ k, m k ≤ M k := fun k => csInf_le_csSup (hne k) (hbdd k).2 (hbdd k).1
  have hm0 : ∀ k, 0 ≤ m k := fun k =>
    le_csInf (hne k) fun z ⟨σ, hσ, h, _, _, hz⟩ => by rw [hz]; exact uValue_nonneg u hσ.1 hu h k
  have hMtop : ∀ k, M k ≤ u k B.v := fun k =>
    csSup_le (hne k) fun z ⟨σ, hσ, h, _, _, hz⟩ => by
      rw [hz]; exact uValue_le_top u hσ.1 hu (hmono k) h
  have hnext : ∀ σ, UIsSPNE B u σ → ∀ h, B.ValidHist h → ∀ y ∈ Set.Icc 0 B.v,
      uValue B u σ (y :: h) (other (proposer h.length)) ∈ S (other (proposer h.length)) :=
    fun σ hσ h hvh y hy => ⟨σ, hσ, y :: h, B.validHist_cons hvh hy, proposer_succ _, rfl⟩
  -- Shaked-Sutton, lower bound (limit using continuity)
  have hA : ∀ k, ∀ q ∈ Set.Icc 0 B.v, u (other k) q = B.δ (other k) * M (other k) →
      u k (B.v - q) ≤ m k := by
    intro k q hq hqM
    have hfor : ∀ y ∈ Set.Ioc q B.v, u k (B.v - y) ≤ m k := by
      intro y hy
      have hyI : y ∈ Set.Icc 0 B.v := ⟨by linarith [hq.1, hy.1], hy.2⟩
      have hlt : B.δ (other k) * M (other k) < u (other k) y := by
        rw [← hqM]; exact hstr _ hq hyI hy.1
      refine le_csInf (hne k) fun z ⟨σ, hσ, h, hvh, hp, hz⟩ => ?_
      rw [hz]
      subst hp
      exact uValue_ge_of_uIsSPNE u hσ hvh (B.live_of_top hT _)
        (fun y' hy' => le_csSup (hbdd _).1 (hnext σ hσ h hvh y' hy')) hyI hlt
    have hqv : q < B.v := by
      have h1 : u (other k) q < u (other k) B.v := by
        rw [hqM]
        have := hupos (other k) B.v hvpos le_rfl
        have := hMtop (other k)
        have := B.δ_lt_one (other k)
        have := B.δ_pos (other k)
        nlinarith
      exact ((hstr _).lt_iff_lt hq hvI).1 h1
    have hcont : ContinuousOn (fun y => u k (B.v - y)) (Set.Icc 0 B.v) :=
      (hc k).comp (continuousOn_const.sub continuousOn_id) fun y hy => hflip y hy
    have hcw : ContinuousWithinAt (fun y => u k (B.v - y)) (Set.Ioc q B.v) q :=
      (hcont q hq).mono fun y hy => ⟨by linarith [hq.1, hy.1], hy.2⟩
    have := left_nhdsWithin_Ioc_neBot hqv
    exact le_of_tendsto hcw (eventually_nhdsWithin_of_forall hfor)
  -- Shaked-Sutton, upper bound
  have hB : ∀ k, ∀ q ∈ Set.Icc 0 B.v, u (other k) q ≤ B.δ (other k) * m (other k) →
      M k ≤ u k (B.v - q) := by
    intro k q hq hqm
    refine csSup_le (hne k) fun z ⟨σ, hσ, h, hvh, hp, hz⟩ => ?_
    rw [hz]
    subst hp
    exact uValue_le_of_uIsSPNE u hσ hvh (B.live_of_top hT _) hu (hmono _) (hstr _)
      (fun y hy => csInf_le (hbdd _).2 (hnext σ hσ h hvh y hy)) hq hqm
  -- shares with given utilities (intermediate value theorem)
  have hinv : ∀ k, ∀ t, 0 ≤ t → t ≤ u k B.v → ∃ z ∈ Set.Icc 0 B.v, u k z = t := by
    intro k t ht0 htv
    obtain ⟨z, hz, hzt⟩ := intermediate_value_Icc hvpos.le (hc k)
      (⟨by rw [hzero]; exact ht0, htv⟩ : t ∈ Set.Icc (u k 0) (u k B.v))
    exact ⟨z, hz, hzt⟩
  -- `g k z`: the share giving `k` the utility `δ u_k(z)`
  set g : Fin 2 → ℝ → ℝ := fun k z =>
    Classical.epsilon fun y => y ∈ Set.Icc 0 B.v ∧ u k y = B.δ 0 * u k z with hgdef
  have hg : ∀ k, ∀ z ∈ Set.Icc 0 B.v, g k z ∈ Set.Icc 0 B.v ∧ u k (g k z) = B.δ 0 * u k z := by
    intro k z hz
    have h1 := hu k z hz
    have h2 := hmono k hz hvI hz.2
    obtain ⟨y, hy, hy'⟩ := hinv k (B.δ 0 * u k z) (mul_nonneg hδ0.le h1) (by nlinarith)
    exact Classical.epsilon_spec (p := fun y => y ∈ Set.Icc 0 B.v ∧ u k y = B.δ 0 * u k z)
      ⟨y, hy, hy'⟩
  have hgm : ∀ k, ∀ z ∈ Set.Icc 0 B.v, ∀ z' ∈ Set.Icc 0 B.v, z ≤ z' → g k z ≤ g k z' := by
    intro k z hz z' hz' hzz
    rw [← (hstr k).le_iff_le (hg k z hz).1 (hg k z' hz').1, (hg k z hz).2, (hg k z' hz').2]
    exact mul_le_mul_of_nonneg_left (hmono k hz hz' hzz) hδ0.le
  set T : ℝ → ℝ := fun z => B.v - g 1 (B.v - g 0 z) with hTdef
  have hTm : ∀ z ∈ Set.Icc 0 B.v, T z ∈ Set.Icc 0 B.v := fun z hz =>
    hflip _ (hg 1 _ (hflip _ (hg 0 z hz).1)).1
  have hTmono : ∀ z ∈ Set.Icc 0 B.v, ∀ z' ∈ Set.Icc 0 B.v, z ≤ z' → T z ≤ T z' := by
    intro z hz z' hz' hzz
    have h1 := hgm 0 z hz z' hz' hzz
    have h2 := hgm 1 _ (hflip _ (hg 0 z' hz').1) _ (hflip _ (hg 0 z hz).1) (by linarith)
    simp only [hTdef]
    linarith
  -- fixed points of `T` are stationary configurations, hence unique
  have hTfix : ∀ z ∈ Set.Icc 0 B.v, T z = z → IsStationary (u 0) (u 1) B.v (B.δ 0) z (g 0 z) := by
    intro z hz hfix
    refine ⟨(hg 0 z hz).1.1, (hg 0 z hz).1.2, hz.1, hz.2, ?_, (hg 0 z hz).2⟩
    have : B.v - z = g 1 (B.v - g 0 z) := by simp only [hTdef] at hfix; linarith
    rw [this]
    exact (hg 1 _ (hflip _ (hg 0 z hz).1)).2
  have huniq : ∀ z ∈ Set.Icc 0 B.v, ∀ z' ∈ Set.Icc 0 B.v, T z = z → T z' = z' → z = z' :=
    fun z hz z' hz' h1 h2 => (exercise_22_E_11a hD (hTfix z hz h1) (hTfix z' hz' h2)).1
  have hxI : x ∈ Set.Icc 0 B.v := ⟨hs.2.2.1, hs.2.2.2.1⟩
  have hwI : w ∈ Set.Icc 0 B.v := ⟨hs.1, hs.2.1⟩
  have hxfix : T x = x := by
    have e1 : g 0 x = w := (hstr 0).injOn (hg 0 x hxI).1 hwI
      (by rw [(hg 0 x hxI).2, hs.2.2.2.2.2])
    have e2 : g 1 (B.v - w) = B.v - x := (hstr 1).injOn (hg 1 _ (hflip w hwI)).1 (hflip x hxI)
      (by rw [(hg 1 _ (hflip w hwI)).2, hs.2.2.2.2.1])
    simp only [hTdef]
    rw [e1, e2]
    ring
  have hfb := fun z hz => fixed_point_bounds hvpos.le hTm hTmono huniq hxI hxfix (x := z) hz
  -- the extreme shares of agent 1 and agent 2
  obtain ⟨pP, hpP, hpPu⟩ := hinv 0 (M 0) ((hm0 0).trans (hmM 0)) (hMtop 0)
  obtain ⟨pm, hpm, hpmu⟩ := hinv 0 (m 0) (hm0 0) ((hmM 0).trans (hMtop 0))
  obtain ⟨rP, hrP, hrPu⟩ := hinv 1 (M 1) ((hm0 1).trans (hmM 1)) (hMtop 1)
  obtain ⟨rm, hrm, hrmu⟩ := hinv 1 (m 1) (hm0 1) ((hmM 1).trans (hMtop 1))
  -- `p⁺ ≤ T p⁺`
  have hup : pP ≤ T pP := by
    have e1 : pP ≤ B.v - g 1 rm := by
      have := hB 0 (g 1 rm) (hg 1 rm hrm).1
        (by rw [ho0, (hg 1 rm hrm).2, hrmu, hall 1])
      rw [← hpPu] at this
      exact ((hstr 0).le_iff_le hpP (hflip _ (hg 1 rm hrm).1)).1 this
    have e2 : B.v - g 0 pP ≤ rm := by
      have := hA 1 (g 0 pP) (hg 0 pP hpP).1 (by rw [ho1, (hg 0 pP hpP).2, hpPu])
      rw [← hrmu] at this
      exact ((hstr 1).le_iff_le (hflip _ (hg 0 pP hpP).1) hrm).1 this
    have e3 := hgm 1 _ (hflip _ (hg 0 pP hpP).1) rm hrm e2
    simp only [hTdef]
    linarith
  -- `T p⁻ ≤ p⁻`
  have hdown : T pm ≤ pm := by
    have f1 : B.v - g 1 rP ≤ pm := by
      have := hA 0 (g 1 rP) (hg 1 rP hrP).1 (by rw [ho0, (hg 1 rP hrP).2, hrPu, hall 1])
      rw [← hpmu] at this
      exact ((hstr 0).le_iff_le (hflip _ (hg 1 rP hrP).1) hpm).1 this
    have f2 : rP ≤ B.v - g 0 pm := by
      have := hB 1 (g 0 pm) (hg 0 pm hpm).1 (by rw [ho1, (hg 0 pm hpm).2, hpmu])
      rw [← hrPu] at this
      exact ((hstr 1).le_iff_le hrP (hflip _ (hg 0 pm hpm).1)).1 this
    have f3 := hgm 1 rP hrP _ (hflip _ (hg 0 pm hpm).1) f2
    simp only [hTdef]
    linarith
  have h1 := (hfb pP hpP).1 hup
  have h2 := (hfb pm hpm).2 hdown
  have h3 : pm ≤ pP := ((hstr 0).le_iff_le hpm hpP).1 (by rw [hpmu, hpPu]; exact hmM 0)
  have hpPx : pP = x := by linarith
  have hpmx : pm = x := by linarith
  have hM0 : M 0 = u 0 x := by rw [← hpPu, hpPx]
  have hm0' : m 0 = u 0 x := by rw [← hpmu, hpmx]
  -- agent 2's proposer payoffs
  have hm1 : u 1 (B.v - w) ≤ m 1 := hA 1 w hwI (by rw [ho1, hs.2.2.2.2.2, hM0])
  have hM1 : M 1 ≤ u 1 (B.v - w) := hB 1 w hwI (by rw [ho1, hs.2.2.2.2.2, hm0'])
  have hMs : ∀ k, M k = u k (s k) ∧ m k = u k (s k) := Fin.forall_fin_two.2
    ⟨⟨hM0, hm0'⟩, ⟨le_antisymm hM1 (hm1.trans (hmM 1)), le_antisymm ((hmM 1).trans hM1) hm1⟩⟩
  -- every SPNE: the proposer gets the stationary utility
  have hprop : ∀ σ, UIsSPNE B u σ → ∀ h, B.ValidHist h →
      uValue B u σ h (proposer h.length) = u (proposer h.length) (s (proposer h.length)) := by
    intro σ hσ h hvh
    have hz : uValue B u σ h (proposer h.length) ∈ S (proposer h.length) :=
      ⟨σ, hσ, h, hvh, rfl, rfl⟩
    have e1 := le_csSup (hbdd _).1 hz
    have e2 := csInf_le (hbdd _).2 hz
    have := hMs (proposer h.length)
    linarith [this.1, this.2]
  -- the responder; agreement is immediate
  intro σ hσ h hvh
  set p := proposer h.length with hpdef
  have hl := B.live_of_top hT h.length
  have hvalp := hprop σ hσ h hvh
  set y := σ.prop h
  have hy := hσ.1 h
  have hsp := hupos p (s p) (hs0 p).2 (hs0 p).1.2
  have hacc : σ.resp h y = true := by
    by_contra hrej
    have hrej' : σ.resp h y = false := by simpa using hrej
    have e1 := uValue_eq_uRespValue u σ hl p
    rw [uRespValue_reject u hrej', hvalp] at e1
    have hnext := hprop σ hσ (y :: h) (B.validHist_cons hvh hy)
    rw [List.length_cons, proposer_succ] at hnext
    have hfr := uValue_frontier u hσ.1 hu (hmono p) (hstr (other p)) (y :: h) (hs0 (other p)).1
      hnext.ge
    rw [hrel p] at hfr
    have e2 := mul_le_mul_of_nonneg_left hfr (B.δ_pos p).le
    have hδp := B.δ_pos p
    have hδp1 := B.δ_lt_one p
    nlinarith [mul_pos (mul_pos (sub_pos.2 hδp1) (by linarith : (0 : ℝ) < 1 + B.δ p)) hsp]
  have e1 := uValue_eq_uRespValue u σ hl p
  rw [uRespValue_accept u hl hacc, share_proposer, hvalp] at e1
  have hyeq : B.v - y = s p := (hstr p).injOn (hflip y hy) (hs0 p).1 e1.symm
  refine ⟨by linarith, hacc, hvalp, ?_⟩
  have e2 := uValue_eq_uRespValue u σ hl (other p)
  rw [uRespValue_accept u hl hacc, share_other] at e2
  rw [e2, ← hyeq, sub_sub_cancel]

open MWG.DynamicGames BargainingGame in
/-- **Exercise 22.E.11(c)** (MWG, p. 854). In Rubinstein's infinite-horizon alternating-offer
game with common discount factor `δ` and utilities `u₁ = u 0`, `u₂ = u 1` for money that are
increasing, concave (possibly different) and continuous on `[0, m]` with `uᵢ(0) = 0`:
a stationary configuration `(x, w)` exists (Exercise 22.E.11(a)), its stationary profile is a
subgame perfect Nash equilibrium, and every SPNE has, at every feasible history, the same payoff
configuration as this stationary SPNE. So every SPNE payoff configuration is the payoff
configuration of an SPNE in stationary strategies, and the uniqueness of Example 9.AA.2 extends
to concave utilities (by Exercise 22.E.11(a) the stationary configuration is unique). -/
theorem exercise_22_E_11c (hT : B.T = ⊤) (hδ : B.δ 0 = B.δ 1)
    (hD : RubinsteinData (u 0) (u 1) B.v (B.δ 0))
    (hc : ∀ k, ContinuousOn (u k) (Set.Icc 0 B.v)) :
    (∃ x w, IsStationary (u 0) (u 1) B.v (B.δ 0) x w) ∧
    ∀ x w, IsStationary (u 0) (u 1) B.v (B.δ 0) x w →
      UIsSPNE B u (statProfile B (stShares B x w)) ∧
      ∀ σ, UIsSPNE B u σ → ∀ h, B.ValidHist h → ∀ i,
        uValue B u σ h i = uValue B u (statProfile B (stShares B x w)) h i := by
  refine ⟨exercise_22_E_11a_exists hD (hc 0) (hc 1), fun x w hs => ?_⟩
  have hstr : ∀ k, StrictMonoOn (u k) (Set.Icc 0 B.v) := Fin.forall_fin_two.2 ⟨hD.mono₁, hD.mono₂⟩
  have hzero : ∀ k, u k 0 = 0 := Fin.forall_fin_two.2 ⟨hD.zero₁, hD.zero₂⟩
  have hu : ∀ k, ∀ z ∈ Set.Icc 0 B.v, 0 ≤ u k z := fun k z hz => by
    have := (hstr k).monotoneOn ⟨le_rfl, B.v_pos.le⟩ hz hz.1; rwa [hzero] at this
  obtain ⟨hs0, hrel⟩ := stShares_spec u hδ hD hs
  refine ⟨statProfile_isSPNE u hT (fun i => (hs0 i).1) hu (fun k => (hstr k).monotoneOn) hrel,
    fun σ hσ h hvh i => ?_⟩
  obtain ⟨-, -, h1, h2⟩ := uSPNE_unique u hT hδ hD hc hs σ hσ h hvh
  rw [statProfile_uValue u _ (B.live_of_top hT h.length)]
  rcases eq_or_eq_other (proposer h.length) i with hi | hi
  · subst hi
    rw [h1, share_proposer, sub_sub_cancel]
  · subst hi
    rw [h2, share_other]

open MWG.DynamicGames BargainingGame in
/-- **Exercise 22.E.11(c)**, instance (MWG, p. 854). For `m = 1`, `δ = 1/2` and linear utilities
the hypotheses hold, the stationary configuration is `x = 2/3`, `w = 1/3`, and in every SPNE
agent 1 gets `2/3` at the start of the game (and agent 2 `1/3`). -/
theorem exercise_22_E_11c_instance :
    ∃ B : BargainingGame, B.T = ⊤ ∧ B.δ 0 = B.δ 1 ∧ B.v = 1 ∧ B.δ 0 = 1 / 2 ∧
      RubinsteinData id id B.v (B.δ 0) ∧
      IsStationary id id B.v (B.δ 0) (2 / 3) (1 / 3) ∧
      ∀ σ, UIsSPNE B (fun _ => id) σ →
        uValue B (fun _ => id) σ [] 0 = 2 / 3 ∧ uValue B (fun _ => id) σ [] 1 = 1 / 3 := by
  have hst := stationary_linear (m := 1) (δ := 1 / 2) one_pos (by norm_num) (by norm_num)
  have e1 : (1 : ℝ) / (1 + 1 / 2) = 2 / 3 := by norm_num
  have e2 : (1 / 2 : ℝ) * 1 / (1 + 1 / 2) = 1 / 3 := by norm_num
  rw [e1, e2] at hst
  refine ⟨⟨1, fun _ => 1 / 2, ⊤, one_pos, fun _ => by norm_num, fun _ => by norm_num⟩,
    rfl, rfl, rfl, rfl, hst.1, hst.2, fun σ hσ => ?_⟩
  obtain ⟨-, -, h1, h2⟩ := uSPNE_unique (fun _ => id) rfl rfl hst.1
    (fun _ => continuousOn_id) hst.2 σ hσ [] (fun _ h => absurd h List.not_mem_nil)
  have hp : proposer ([] : List ℝ).length = 0 := rfl
  rw [hp] at h1 h2
  rw [show other (0 : Fin 2) = 1 from rfl] at h2
  rw [h1, h2]
  norm_num [stShares]

end MWG.WelfareBargaining
