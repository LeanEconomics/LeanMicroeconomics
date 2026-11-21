/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGDynamicGames.Bargaining
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Uniqueness of the SPNE in the alternating-offer bargaining games

MWG, Appendix A of Chapter 9, pp. 296-299: Examples 9.AA.1 (Stahl's finite horizon game) and
9.AA.2 (Rubinstein's infinite horizon game), and Exercise 9.B.12 (different discount factors).

* `threshold c`: the profile in which the period-`t` proposer offers `c t` and the responder
  accepts exactly the offers `y ≥ c t`. `threshold_isSPNE`: if `c t` is the responder's
  discounted continuation value (`c t = δ_j (v − c (t+1))`, and `0` in the last period) the
  profile is an SPNE (proved with the discounted one-stage deviation bound).
* `exercise_9_B_12` (Rubinstein with discount factors `δ₁, δ₂`): there is a unique SPNE. In
  it the proposer `i` offers `δ_j x_j` and earns `x_i = v (1 − δ_j) / (1 − δ_i δ_j)`; the
  responder accepts exactly the offers of at least `δ_j x_j`; agreement is immediate.
  `example_9_AA_2` is the case `δ₁ = δ₂ = δ`: player 1 earns `v / (1 + δ)`, player 2
  `δ v / (1 + δ)`.
* `example_9_AA_1` (finite horizon `T`, common `δ`): unique SPNE; from a node with `n` periods
  left the proposer earns `P n = v (1 − (−δ)^n) / (1 + δ)`, with MWG's closed forms for odd and
  even `T` (`example_9_AA_1_odd`, `example_9_AA_1_even`) and limit `v / (1 + δ)` as
  `T → ∞` (`example_9_AA_1_limit`; the infinite-horizon outcome is the limit, p. 299).
-/

namespace MWG.DynamicGames

namespace BargainingGame

variable (B : BargainingGame)

/-- The threshold profile: in period `t` the proposer offers `c t`; the responder accepts
exactly the offers `y ≥ c t`. -/
noncomputable def threshold (c : ℕ → ℝ) : BargainingProfile where
  prop h := c h.length
  resp h y := decide (c h.length ≤ y)

/-- Payoffs of a threshold profile from a live node: the proposer gets `v − c t`, the
responder `c t` (immediate agreement). -/
theorem value_threshold (c : ℕ → ℝ) {h : List ℝ} (hl : B.Live h.length) :
    B.value (threshold c) h (proposer h.length) = B.v - c h.length ∧
      B.value (threshold c) h (other (proposer h.length)) = c h.length := by
  have hacc : (threshold c).resp h ((threshold c).prop h) = true := by simp [threshold]
  rw [B.value_eq_respValue _ hl, B.value_eq_respValue _ hl, B.respValue_accept hl hacc,
    B.respValue_accept hl hacc, share_proposer, share_other]
  exact ⟨rfl, rfl⟩

/-- **Threshold profiles are SPNE** (MWG, pp. 296-299). If `c t ∈ [0, v]` for all `t`, and in
every live period `c t` is the responder's discounted value as the next proposer
(`c t = δ_j (v − c (t + 1))` if period `t + 1` is live, `c t = 0` if `t` is the last period),
then `threshold c` is a subgame perfect Nash equilibrium. -/
theorem threshold_isSPNE {c : ℕ → ℝ} (hc0 : ∀ t, c t ∈ Set.Icc 0 B.v)
    (hc1 : ∀ t, B.Live (t + 1) → c t = B.δ (other (proposer t)) * (B.v - c (t + 1)))
    (hc2 : ∀ t, B.Live t → ¬ B.Live (t + 1) → c t = 0) : B.IsSPNE (threshold c) := by
  classical
  refine ⟨fun h => hc0 h.length, fun i σ' hσ' hdev h hv hl => ?_⟩
  -- the bound: the threshold profile's value
  let bnd : List ℝ → ℝ := fun h => if B.Live h.length then
    (if proposer h.length = i then B.v - c h.length else c h.length) else 0
  have hbnd_val : ∀ h, B.value (threshold c) h i = bnd h := by
    intro h
    simp only [bnd]
    split_ifs with hl' hp
    · rw [← hp]; exact (B.value_threshold c hl').1
    · rcases eq_or_eq_other (proposer h.length) i with h1 | h1
      · exact absurd h1.symm hp
      · rw [h1]; exact (B.value_threshold c hl').2
    · exact B.value_of_not_live hl' i
  have hbnd0 : ∀ h, 0 ≤ bnd h := by
    intro h
    simp only [bnd]
    split_ifs
    · linarith [(hc0 h.length).2]
    · exact (hc0 h.length).1
    · exact le_rfl
  have hδi := B.δ_pos i
  have hδi1 := B.δ_lt_one i
  -- the deviation's value is bounded by `bnd`
  have hle : ∀ h, B.value σ' h i ≤ bnd h := by
    refine B.value_le_of_bound bnd hbnd0 (fun h hl hacc => ?_) (fun h hl hrej => ?_)
    · simp only [bnd, hl, ite_true]
      split_ifs with hp
      · have hr : σ'.resp h (σ'.prop h) = (threshold c).resp h (σ'.prop h) := hdev.2 h _ hp
        rw [hacc] at hr
        have hr' : c h.length ≤ σ'.prop h := by simpa [threshold] using hr.symm
        rw [← hp, share_proposer]
        linarith
      · have hpr : σ'.prop h = c h.length := hdev.1 h hp
        rcases eq_or_eq_other (proposer h.length) i with h1 | h1
        · exact absurd h1.symm hp
        · rw [hpr, h1, share_other]
    · have hlen : (σ'.prop h :: h).length = h.length + 1 := rfl
      have hbl : bnd h = if proposer h.length = i then B.v - c h.length else c h.length := by
        simp only [bnd, hl, ite_true]
      rw [hbl]
      by_cases hl1 : B.Live (h.length + 1)
      · have hbn : bnd (σ'.prop h :: h) = if proposer (h.length + 1) = i then
            B.v - c (h.length + 1) else c (h.length + 1) := by
          simp only [bnd, hlen, hl1, ite_true]
        rw [hbn, proposer_succ]
        have h1 := hc1 h.length hl1
        have hc := hc0 (h.length + 1)
        rcases eq_or_eq_other i (proposer h.length) with hp | hp
        · rw [hp] at h1 ⊢
          simp only [other_ne, ite_false, ite_true]
          have hδo := B.δ_pos (other i)
          have hδo1 := B.δ_lt_one (other i)
          rw [h1]
          nlinarith [mul_nonneg (sub_nonneg.2 hc.2) (sub_nonneg.2 hδo1.le),
            mul_nonneg hc.1 (sub_nonneg.2 hδi1.le)]
        · rw [hp, other_other] at h1 ⊢
          simp only [other_ne, ite_false, ite_true]
          rw [h1]
      · have hbn : bnd (σ'.prop h :: h) = 0 := by simp only [bnd, hlen, hl1, ite_false]
        rw [hbn, mul_zero, ← hbl]
        exact hbnd0 h
  refine ⟨by rw [hbnd_val]; exact hle h, fun y hy => ?_⟩
  have hyh : B.value σ' (y :: h) i ≤ B.value (threshold c) (y :: h) i := by
    rw [hbnd_val]; exact hle _
  by_cases hp : proposer h.length = i
  · have hr : σ'.resp h y = (threshold c).resp h y := hdev.2 h y hp
    unfold respValue
    rw [hr]
    split_ifs
    · exact le_rfl
    · exact mul_le_mul_of_nonneg_left hyh hδi.le
  · have hi : other (proposer h.length) = i := by
      rcases eq_or_eq_other (proposer h.length) i with h2 | h2
      · exact absurd h2.symm hp
      · exact h2.symm
    -- the threshold responder's value is `max y (c t)`
    have hcont : B.δ i * B.value (threshold c) (y :: h) i = c h.length := by
      rw [hbnd_val]
      simp only [bnd, List.length_cons, proposer_succ, hi, ite_true]
      by_cases hl1 : B.Live (h.length + 1)
      · simp only [hl1, ite_true]
        have := hc1 h.length hl1
        rw [hi] at this
        rw [this]
      · simp only [hl1, ite_false, mul_zero]
        exact (hc2 h.length hl hl1).symm
    have hthr : max y (c h.length) ≤ B.respValue (threshold c) h y i := by
      by_cases hyc : c h.length ≤ y
      · rw [B.respValue_accept hl (by simp [threshold, hyc]), ← hi, share_other]
        exact max_le le_rfl hyc
      · rw [B.respValue_reject (by simp [threshold, hyc]), hcont]
        exact max_le (le_of_lt (not_le.1 hyc)) le_rfl
    refine le_trans ?_ hthr
    unfold respValue
    split_ifs with hacc
    · rw [← hi, share_other]
      exact le_max_left _ _
    · calc B.δ i * B.value σ' (y :: h) i ≤ B.δ i * B.value (threshold c) (y :: h) i :=
            mul_le_mul_of_nonneg_left hyh hδi.le
        _ = c h.length := hcont
        _ ≤ max y (c h.length) := le_max_right _ _

/-- Proposer `i`'s Rubinstein payoff `x_i = v (1 − δ_j) / (1 − δ_i δ_j)`. -/
noncomputable def xstar (i : Fin 2) : ℝ :=
  B.v * (1 - B.δ (other i)) / (1 - B.δ i * B.δ (other i))

theorem one_sub_mul_pos (i : Fin 2) : 0 < 1 - B.δ i * B.δ (other i) := by
  have := B.δ_lt_one i
  have := B.δ_lt_one (other i)
  have := B.δ_pos i
  have := B.δ_pos (other i)
  nlinarith

/-- `x_i + δ_j x_j = v`: the proposer's share plus the responder's discounted value. -/
theorem xstar_add (i : Fin 2) : B.xstar i + B.δ (other i) * B.xstar (other i) = B.v := by
  have h1 := B.one_sub_mul_pos i
  have h2 := B.one_sub_mul_pos (other i)
  unfold xstar
  rw [other_other]
  have hne : 1 - B.δ i * B.δ (other i) ≠ 0 := h1.ne'
  have hne' : 1 - B.δ (other i) * B.δ i ≠ 0 := by rw [mul_comm]; exact hne
  field_simp
  ring

theorem xstar_mem (i : Fin 2) : B.xstar i ∈ Set.Icc 0 B.v ∧ 0 < B.xstar i := by
  have h1 := B.one_sub_mul_pos i
  have hv := B.v_pos
  have hd := B.δ_lt_one (other i)
  have hd0 := B.δ_pos (other i)
  have hdi := B.δ_pos i
  have hdi1 := B.δ_lt_one i
  have hpos : 0 < B.xstar i := by unfold xstar; apply div_pos <;> nlinarith
  refine ⟨⟨hpos.le, ?_⟩, hpos⟩
  unfold xstar
  rw [div_le_iff₀ h1]
  nlinarith [mul_pos (mul_pos hv hd0) (sub_pos.2 hdi1)]

/-- The Rubinstein offer in period `t`: the responder's discounted value `δ_j x_j`. -/
noncomputable def rubOffer (t : ℕ) : ℝ := B.δ (other (proposer t)) * B.xstar (other (proposer t))

theorem rubOffer_mem (t : ℕ) : B.rubOffer t ∈ Set.Icc 0 B.v := by
  have h := B.xstar_mem (other (proposer t))
  have hd := B.δ_pos (other (proposer t))
  have hd1 := B.δ_lt_one (other (proposer t))
  unfold rubOffer
  constructor
  · exact mul_nonneg hd.le h.1.1
  · nlinarith [h.1.2]

/-- In the infinite horizon game every period is live. -/
theorem live_of_top (hT : B.T = ⊤) (t : ℕ) : B.Live t := by
  unfold Live
  rw [hT]
  exact ENat.natCast_lt_top t

/-- The stationary Rubinstein profile is an SPNE of the infinite horizon game. -/
theorem rubinstein_isSPNE (hT : B.T = ⊤) : B.IsSPNE (threshold B.rubOffer) := by
  refine B.threshold_isSPNE B.rubOffer_mem (fun t _ => ?_)
    (fun t _ h => absurd (B.live_of_top hT (t + 1)) h)
  unfold rubOffer
  rw [proposer_succ, other_other]
  have := B.xstar_add (other (proposer t))
  rw [other_other] at this
  rw [show B.v - B.δ (proposer t) * B.xstar (proposer t) = B.xstar (other (proposer t)) by
    linarith]

/-- SPNE payoffs of the proposer, over all SPNE and all feasible histories where `i` proposes. -/
def spnePayoffs (i : Fin 2) : Set ℝ :=
  {x | ∃ σ, B.IsSPNE σ ∧ ∃ h, B.ValidHist h ∧ proposer h.length = i ∧ x = B.value σ h i}

theorem validHist_nil : B.ValidHist [] := fun _ h => absurd h List.not_mem_nil

/-- **Rubinstein's theorem, payoffs** (MWG, Example 9.AA.2, p. 298; Exercise 9.B.12). In the
infinite horizon game, in every SPNE and at every feasible proposal node, the proposer `i`
earns exactly `x_i = v (1 − δ_j) / (1 − δ_i δ_j)`. -/
theorem rubinstein_value (hT : B.T = ⊤) {σ : BargainingProfile} (hσ : B.IsSPNE σ)
    {h : List ℝ} (hv : B.ValidHist h) :
    B.value σ h (proposer h.length) = B.xstar (proposer h.length) := by
  have hbdd : ∀ i, BddAbove (B.spnePayoffs i) ∧ BddBelow (B.spnePayoffs i) := fun i =>
    ⟨⟨B.v, fun x ⟨σ, hσ, h, _, _, hx⟩ => by
      rw [hx]
      have := B.value_bounds hσ.1 h i
      have := (B.value_bounds hσ.1 h (other i)).1
      linarith⟩,
    ⟨0, fun x ⟨σ, hσ, h, _, _, hx⟩ => by rw [hx]; exact (B.value_bounds hσ.1 h i).1⟩⟩
  have hne : ∀ i, (B.spnePayoffs i).Nonempty := by
    intro i
    rcases eq_or_eq_other 0 i with h0 | h1
    · exact ⟨_, threshold B.rubOffer, B.rubinstein_isSPNE hT, [], B.validHist_nil,
        by rw [h0]; rfl, rfl⟩
    · refine ⟨_, threshold B.rubOffer, B.rubinstein_isSPNE hT, [0],
        B.validHist_cons B.validHist_nil ⟨le_rfl, B.v_pos.le⟩, ?_, rfl⟩
      rw [h1]; rfl
  set M : Fin 2 → ℝ := fun i => sSup (B.spnePayoffs i)
  set m : Fin 2 → ℝ := fun i => sInf (B.spnePayoffs i)
  have hm0 : ∀ i, 0 ≤ m i := fun i =>
    le_csInf (hne i) fun x ⟨σ, hσ, h, _, _, hx⟩ => by rw [hx]; exact (B.value_bounds hσ.1 h i).1
  -- the two Shaked-Sutton bounds at any SPNE node
  have hnext : ∀ σ, B.IsSPNE σ → ∀ h, B.ValidHist h → ∀ y ∈ Set.Icc 0 B.v,
      B.value σ (y :: h) (other (proposer h.length)) ∈
        B.spnePayoffs (other (proposer h.length)) := fun σ hσ h hv y hy =>
    ⟨σ, hσ, y :: h, B.validHist_cons hv hy, proposer_succ _, rfl⟩
  have hlo : ∀ i, B.v - B.δ (other i) * M (other i) ≤ m i := by
    intro i
    refine le_csInf (hne i) fun x ⟨σ, hσ, h, hv, hp, hx⟩ => ?_
    rw [hx, ← hp]
    exact B.value_ge_of_isSPNE hσ hv (B.live_of_top hT _) fun y hy =>
      le_csSup (hbdd _).1 (hnext σ hσ h hv y hy)
  have hhi : ∀ i, M i ≤ B.v - B.δ (other i) * m (other i) := by
    intro i
    refine csSup_le (hne i) fun x ⟨σ, hσ, h, hv, hp, hx⟩ => ?_
    rw [hx, ← hp]
    exact B.value_le_of_isSPNE hσ hv (B.live_of_top hT _) (hm0 _) fun y hy =>
      csInf_le (hbdd _).2 (hnext σ hσ h hv y hy)
  have hsolve : ∀ i, M i ≤ B.xstar i ∧ B.xstar i ≤ m i := by
    intro i
    have h1 := hhi i
    have h2 := hlo (other i)
    have h3 := hlo i
    have h4 := hhi (other i)
    rw [other_other] at h2 h4
    have hd := B.δ_pos (other i)
    have hdi := B.δ_pos i
    have hD := B.one_sub_mul_pos i
    unfold xstar
    constructor
    · rw [le_div_iff₀ hD]
      have : B.δ (other i) * (B.v - B.δ i * M i) ≤ B.δ (other i) * m (other i) :=
        mul_le_mul_of_nonneg_left h2 hd.le
      nlinarith
    · rw [div_le_iff₀ hD]
      have : B.δ (other i) * M (other i) ≤ B.δ (other i) * (B.v - B.δ i * m i) :=
        mul_le_mul_of_nonneg_left h4 hd.le
      nlinarith
  set i := proposer h.length
  have hx : B.value σ h i ∈ B.spnePayoffs i := ⟨σ, hσ, h, hv, rfl, rfl⟩
  have h1 := le_csSup (hbdd i).1 hx
  have h2 := csInf_le (hbdd i).2 hx
  have := hsolve i
  linarith [this.1, this.2]

/-- **Exercise 9.B.12** (MWG, p. 303; Rubinstein 1982). The infinite horizon bargaining game
with discount factors `δ₁, δ₂ ∈ (0, 1)` has a unique SPNE (on feasible histories): the
proposer `i` offers `δ_j x_j` with `x_j = v (1 − δ_i) / (1 − δ_i δ_j)`, the responder `j`
accepts exactly the offers `y ≥ δ_j x_j`; agreement is immediate, player 1 earning
`x_1 = v (1 − δ₂) / (1 − δ₁ δ₂)` and player 2 earning `v − x_1`. -/
theorem exercise_9_B_12 (hT : B.T = ⊤) :
    B.IsSPNE (threshold B.rubOffer) ∧
    ∀ σ, B.IsSPNE σ → ∀ h, B.ValidHist h →
      σ.prop h = (threshold B.rubOffer).prop h ∧
      (∀ y ∈ Set.Icc 0 B.v, σ.resp h y = (threshold B.rubOffer).resp h y) ∧
      B.value σ h (proposer h.length) = B.xstar (proposer h.length) ∧
      B.value σ h (other (proposer h.length)) = B.v - B.xstar (proposer h.length) := by
  refine ⟨B.rubinstein_isSPNE hT, fun σ hσ h hv => ?_⟩
  set p := proposer h.length
  have hl := B.live_of_top hT h.length
  have hX : ∀ y ∈ Set.Icc 0 B.v, B.value σ (y :: h) (other p) = B.xstar (other p) :=
    fun y hy => by
      have := B.rubinstein_value hT hσ (B.validHist_cons hv hy)
      simpa [List.length_cons, proposer_succ] using this
  have hval : B.value σ h p = B.v - B.δ (other p) * B.xstar (other p) := by
    rw [B.rubinstein_value hT hσ hv]
    have := B.xstar_add p
    linarith
  have hrej : B.δ p * (B.v - B.xstar (other p)) < B.v - B.δ (other p) * B.xstar (other p) := by
    have h1 := B.xstar_add p
    have h2 := B.xstar_add (other p)
    rw [other_other] at h2
    have hx := (B.xstar_mem p).2
    have hd := B.δ_pos p
    have hd1 := B.δ_lt_one p
    rw [show B.v - B.xstar (other p) = B.δ p * B.xstar p by linarith,
      show B.v - B.δ (other p) * B.xstar (other p) = B.xstar p by linarith]
    have : 0 < B.xstar p * (1 - B.δ p) * (1 + B.δ p) :=
      mul_pos (mul_pos hx (sub_pos.2 hd1)) (by linarith)
    nlinarith
  obtain ⟨hprop, hresp⟩ := B.strategies_determined hσ hv hl hX hval hrej
  refine ⟨hprop, fun y hy => ?_, B.rubinstein_value hT hσ hv, ?_⟩
  · have := hresp y hy
    change σ.resp h y = decide (B.rubOffer h.length ≤ y)
    unfold rubOffer
    by_cases hc : B.δ (other p) * B.xstar (other p) ≤ y
    · rw [this.2 hc]
      exact (decide_eq_true hc).symm
    · rw [decide_eq_false hc]
      cases hb : σ.resp h y
      · rfl
      · exact absurd (this.1 hb) hc
  · -- the responder gets the agreed offer
    have hacc : σ.resp h (σ.prop h) = true := (hresp _ (hσ.1 h)).2 (by rw [hprop])
    rw [B.value_eq_respValue σ hl, B.respValue_accept hl hacc, share_other, hprop]
    have := B.xstar_add p
    linarith

/-- **Example 9.AA.2** (MWG, p. 298; Rubinstein 1982). With a common discount factor `δ`, the
infinite horizon alternating-offer game has a unique SPNE: a player who has just received an
offer accepts iff it gives her at least `δ v / (1 + δ)`, and a proposer offers exactly
`δ v / (1 + δ)`; agreement is immediate, with payoffs `v / (1 + δ)` and `δ v / (1 + δ)`. -/
theorem example_9_AA_2 (hT : B.T = ⊤) (hδ : B.δ 0 = B.δ 1) :
    B.IsSPNE (threshold B.rubOffer) ∧
    (∀ t, B.rubOffer t = B.δ 0 * B.v / (1 + B.δ 0)) ∧
    ∀ σ, B.IsSPNE σ → ∀ h, B.ValidHist h →
      σ.prop h = B.δ 0 * B.v / (1 + B.δ 0) ∧
      (∀ y ∈ Set.Icc 0 B.v, σ.resp h y = true ↔ B.δ 0 * B.v / (1 + B.δ 0) ≤ y) ∧
      B.value σ h (proposer h.length) = B.v / (1 + B.δ 0) ∧
      B.value σ h (other (proposer h.length)) = B.δ 0 * B.v / (1 + B.δ 0) := by
  have hall : ∀ i, B.δ i = B.δ 0 := fun i => by fin_cases i <;> simp [hδ]
  have hx : ∀ i, B.xstar i = B.v / (1 + B.δ 0) := by
    intro i
    unfold xstar
    rw [hall i, hall (other i)]
    have h1 : (1 : ℝ) + B.δ 0 ≠ 0 := by linarith [B.δ_pos 0]
    have h2 : (1 : ℝ) - B.δ 0 ≠ 0 := by linarith [B.δ_lt_one 0]
    have h3 : (1 : ℝ) - B.δ 0 * B.δ 0 = (1 - B.δ 0) * (1 + B.δ 0) := by ring
    rw [h3]
    field_simp
  have hoff : ∀ t, B.rubOffer t = B.δ 0 * B.v / (1 + B.δ 0) := by
    intro t
    unfold rubOffer
    rw [hx, hall]
    ring
  obtain ⟨hS, hU⟩ := B.exercise_9_B_12 hT
  refine ⟨hS, hoff, fun σ hσ h hv => ?_⟩
  obtain ⟨hp, hr, hv1, hv2⟩ := hU σ hσ h hv
  refine ⟨by rw [hp]; exact hoff _, fun y hy => ?_, by rw [hv1, hx], ?_⟩
  · rw [hr y hy]
    simp [threshold, hoff]
  · rw [hv2, hx]
    have h1 : (1 : ℝ) + B.δ 0 ≠ 0 := by linarith [B.δ_pos 0]
    field_simp
    ring

/-- The finite horizon proposer payoffs with `n` periods left: `P 0 = 0`,
`P (n + 1) = v − δ P n`. -/
noncomputable def finP (v δ : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => v - δ * finP v δ n

theorem finP_mem {v δ : ℝ} (hv : 0 < v) (hδ0 : 0 < δ) (hδ1 : δ < 1) (n : ℕ) :
    finP v δ n ∈ Set.Icc 0 v := by
  induction n with
  | zero => exact ⟨le_rfl, hv.le⟩
  | succ n ih =>
    simp only [finP]
    constructor <;> nlinarith [ih.1, ih.2]

/-- `P n = v (1 − (−δ)^n) / (1 + δ)`. -/
theorem finP_eq {v δ : ℝ} (hδ0 : 0 < δ) (n : ℕ) :
    finP v δ n = v * (1 - (-δ) ^ n) / (1 + δ) := by
  have h1 : (1 : ℝ) + δ ≠ 0 := by linarith
  induction n with
  | zero => simp [finP]
  | succ n ih =>
    simp only [finP, ih, pow_succ]
    field_simp
    ring

/-- **Example 9.AA.1** (MWG, pp. 296-297; Stahl 1972). In the `T`-period alternating-offer game
with common discount factor `δ`, there is a unique SPNE. From a node with `n ≥ 1` periods
left, the proposer offers `δ P (n − 1)` and earns `P n`, the responder accepts exactly the
offers `y ≥ δ P (n − 1)`; in particular player 1 earns `v₁*(T) = P T` and player 2
`v − v₁*(T)`, agreement being immediate. -/
theorem example_9_AA_1 (N : ℕ) (hT : B.T = N) (hδ : B.δ 0 = B.δ 1) :
    B.IsSPNE (threshold fun t => B.δ 0 * finP B.v (B.δ 0) (N - t - 1)) ∧
    ∀ σ, B.IsSPNE σ → ∀ h, B.ValidHist h → h.length < N →
      B.value σ h (proposer h.length) = finP B.v (B.δ 0) (N - h.length) ∧
      σ.prop h = B.δ 0 * finP B.v (B.δ 0) (N - h.length - 1) ∧
      ∀ y ∈ Set.Icc 0 B.v, σ.resp h y = true ↔ B.δ 0 * finP B.v (B.δ 0) (N - h.length - 1) ≤ y := by
  have hall : ∀ i, B.δ i = B.δ 0 := fun i => by fin_cases i <;> simp [hδ]
  set δ := B.δ 0
  have hδ0 : 0 < δ := B.δ_pos 0
  have hδ1 : δ < 1 := B.δ_lt_one 0
  have hlive : ∀ t, B.Live t ↔ t < N := fun t => by
    unfold Live
    rw [hT]
    exact Nat.cast_lt
  have hP := finP_mem B.v_pos hδ0 hδ1
  refine ⟨B.threshold_isSPNE (fun t => ?_) (fun t ht => ?_) (fun t ht ht1 => ?_), ?_⟩
  · have := hP (N - t - 1)
    exact ⟨mul_nonneg hδ0.le this.1, by nlinarith [this.1, this.2]⟩
  · rw [hlive] at ht
    show δ * finP B.v δ (N - t - 1) =
      B.δ (other (proposer t)) * (B.v - δ * finP B.v δ (N - (t + 1) - 1))
    rw [hall, show N - t - 1 = (N - (t + 1) - 1) + 1 by omega, finP]
  · rw [hlive] at ht ht1
    have : N - t - 1 = 0 := by omega
    simp only [this, finP, mul_zero]
  · intro σ hσ
    -- induction on the number of periods left
    have key : ∀ n, ∀ h, B.ValidHist h → h.length + n = N → 1 ≤ n →
        B.value σ h (proposer h.length) = finP B.v δ n := by
      intro n
      induction n with
      | zero => intro h _ _ hn; omega
      | succ n ih =>
        intro h hv hn _
        have hl : B.Live h.length := (hlive _).2 (by omega)
        have hnext : ∀ y ∈ Set.Icc 0 B.v,
            B.value σ (y :: h) (other (proposer h.length)) = finP B.v δ n := by
          intro y hy
          rcases Nat.eq_zero_or_pos n with h0 | h0
          · subst h0
            rw [B.value_of_not_live (by rw [hlive]; simp; omega)]
            rfl
          · have := ih (y :: h) (B.validHist_cons hv hy) (by simp; omega) h0
            simpa [proposer_succ] using this
        have hge := B.value_ge_of_isSPNE hσ hv hl (M := finP B.v δ n)
          fun y hy => (hnext y hy).le
        have hle := B.value_le_of_isSPNE hσ hv hl (hP n).1 fun y hy => (hnext y hy).ge
        rw [hall] at hge hle
        simp only [finP]
        linarith
    intro h hv hlt
    have hl : B.Live h.length := (hlive _).2 hlt
    have hval := key (N - h.length) h hv (by omega) (by omega)
    have hX : ∀ y ∈ Set.Icc 0 B.v,
        B.value σ (y :: h) (other (proposer h.length)) = finP B.v δ (N - h.length - 1) := by
      intro y hy
      by_cases hN : h.length + 1 < N
      · have := key (N - h.length - 1) (y :: h) (B.validHist_cons hv hy) (by simp; omega)
          (by omega)
        simpa [proposer_succ] using this
      · rw [B.value_of_not_live (by rw [hlive]; simp; omega),
          show N - h.length - 1 = 0 by omega]
        rfl
    have hval' : B.value σ h (proposer h.length) =
        B.v - B.δ (other (proposer h.length)) * finP B.v δ (N - h.length - 1) := by
      rw [hval, hall]
      obtain ⟨n, hn⟩ : ∃ n, N - h.length = n + 1 := ⟨N - h.length - 1, by omega⟩
      rw [hn, finP, Nat.add_sub_cancel]
    have hrej : B.δ (proposer h.length) * (B.v - finP B.v δ (N - h.length - 1)) <
        B.v - B.δ (other (proposer h.length)) * finP B.v δ (N - h.length - 1) := by
      rw [hall, hall]
      nlinarith [B.v_pos]
    obtain ⟨hp, hr⟩ := B.strategies_determined hσ hv hl hX hval' hrej
    rw [hall] at hp hr
    exact ⟨hval, hp, hr⟩

/-- **Example 9.AA.1** (MWG, p. 297). For odd `T`, player 1's SPNE payoff is
`v₁*(T) = v [1 − δ + δ² − ⋯ + δ^{T−1}] = v [(1 − δ)(1 − δ^{T−1}) / (1 − δ²) + δ^{T−1}]`. -/
theorem example_9_AA_1_odd {v δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) {T : ℕ} (hT : Odd T) :
    finP v δ T = v * ∑ k ∈ Finset.range T, (-δ) ^ k ∧
      finP v δ T = v * ((1 - δ) * (1 - δ ^ (T - 1)) / (1 - δ ^ 2) + δ ^ (T - 1)) := by
  have h1 : (1 : ℝ) + δ ≠ 0 := by linarith
  have h2 : (1 : ℝ) - δ ^ 2 ≠ 0 := by nlinarith
  have h3 : (-1 - δ : ℝ) ≠ 0 := fun h => by linarith
  have h4 : (-δ - 1 : ℝ) ≠ 0 := fun h => by linarith
  obtain ⟨k, rfl⟩ := hT
  constructor
  · rw [finP_eq hδ0, geom_sum_eq (by linarith : (-δ : ℝ) ≠ 1)]
    field_simp
    ring
  · rw [finP_eq hδ0, show 2 * k + 1 - 1 = 2 * k by omega, pow_succ, pow_mul, neg_sq]
    rw [pow_mul]
    field_simp
    ring

/-- **Example 9.AA.1** (MWG, p. 297). For even `T`, player 1 earns `v − δ v₁*(T − 1)`. -/
theorem example_9_AA_1_even {v δ : ℝ} {T : ℕ} (hT : Even T) (hT0 : 0 < T) :
    finP v δ T = v - δ * finP v δ (T - 1) := by
  obtain ⟨k, rfl⟩ := hT
  rw [show k + k = (k + k - 1) + 1 by omega, finP]
  rfl

/-- **Example 9.AA.1** (MWG, p. 297). As the horizon grows, player 1's payoff converges to
`v / (1 + δ)` and player 2's to `δ v / (1 + δ)`: the infinite-horizon payoffs. -/
theorem example_9_AA_1_limit {v δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    Filter.Tendsto (fun T => finP v δ T) Filter.atTop (nhds (v / (1 + δ))) ∧
      Filter.Tendsto (fun T => v - finP v δ T) Filter.atTop (nhds (δ * v / (1 + δ))) := by
  have hpow : Filter.Tendsto (fun n : ℕ => (-δ) ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by rw [abs_neg, abs_of_pos hδ0]; exact hδ1)
  have h1 : Filter.Tendsto (fun T => finP v δ T) Filter.atTop (nhds (v / (1 + δ))) := by
    simp_rw [finP_eq hδ0]
    have := ((tendsto_const_nhds (x := (1 : ℝ))).sub hpow).const_mul v |>.div_const (1 + δ)
    simpa using this
  refine ⟨h1, ?_⟩
  have := (tendsto_const_nhds (x := v)).sub h1
  convert this using 2
  have : (1 : ℝ) + δ ≠ 0 := by linarith
  field_simp
  ring

end BargainingGame

end MWG.DynamicGames
