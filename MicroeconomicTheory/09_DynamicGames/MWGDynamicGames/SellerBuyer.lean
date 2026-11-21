/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Two-period bargaining with a privately informed buyer

MWG, Exercise 9.C.3 (p. 304) and Exercise 9.C.6 for it. The seller (value `0`) names a
price in each of two periods; the buyer, whose value `v ∈ {vL, vH}` (`0 < vL < vH`,
`Prob(vH) = λ ∈ (0, 1)`) only she knows, accepts or rejects; payoffs in period 2 are discounted
by `δ ∈ (0, 1)`; the buyer accepts when indifferent.

The model (a direct description of the extensive form's pure strategies and of a weak PBE,
Definition 9.C.3). `SBProfile`: the seller's first price `p1`, the buyer's period-1 acceptance
rule `acc b p` (type `b`, `true` = high, at every price `p`), the seller's second price
`p2 p` after each rejected `p`, and the seller's belief `μ p` that `v = vH` there. In period 2 the
buyer accepts `q` iff `q ≤ v` (the unique sequentially rational move given the tie rule,
`sb_period2`). `IsSBWeakPBE`: the buyer is sequentially rational at every price, the seller is
sequentially rational after every rejected price given her belief, the belief is Bayes'
posterior after the equilibrium price whenever someone rejects it, and the seller's first price
is optimal against every deviation of her whole strategy (price `p` now, price `q` after a
rejection of `p`) given the buyer's strategy and the prior.

* `exercise_9_C_3a`: with `p̂ = (1 − δ) vH + δ vL` (the highest price the high type accepts when
  she expects `vL` next), `A = vL`, `B = λ p̂ + (1 − λ) δ vL`, `C = δ λ vH`, every pure weak PBE has
  one of three outcomes: (i) `p1 = vL`, both types buy at once (needs `B, C ≤ A`); (ii)
  `p1 = p̂`, the high type buys at once, the low type in period 2 at `vL` (needs `A, C ≤ B`);
  (iii) `p1 > vH`, both types reject and the seller charges `vH` in period 2 (needs
  `A, B ≤ C`). Each outcome is a weak PBE outcome exactly under its condition, the seller's
  payoff is `max {A, B, C}`, and a weak PBE always exists. Along the way: the seller's period-2
  price is always `vL` or `vH` (`sb_p2_mem`), the buyer's period-1 choice has a cutoff
  structure (the high type accepts whenever the low type does, `sb_acc_mono`).
* Exercise 9.C.6 (two types). Definition 9.C.4 is stated for finite games, so it is read here
  through its implication for these games (structural consistency, recorded in
  docs/corrections.md): after every price that some type rejects, the seller's belief is Bayes'
  posterior given the buyer's strategy (`IsSBConsistent`; `sbPost_tendsto` shows this is what
  limits of Bayes beliefs from trembles converging to the profile give). Then:
  `exercise_9_C_6_two_types_none` (if `λ vH > vL` there is no pure-strategy sequential
  equilibrium: after prices between `p̂` and `vH` no pure continuation is consistent) and
  `exercise_9_C_6_two_types` (if `λ vH ≤ vL`, the pure sequential equilibria have exactly the
  outcomes (i)-(ii) above under the same conditions, and one exists).
* Exercise 9.C.3(b), values uniform on `[0, 1]` (`v̲ = 0`, normalised `v̄ = 1`; the case `v̲ > 0` is
  in `SellerBuyerGeneral.lean`). `exercise_9_C_3b_cutoff`: for every expected second price the
  buyer's period-1 choice is a cutoff rule. In a reduced model (`IsSBUWeakPBE`: first price, second
  price after each rejected price, cutoff buyers, uniform prior through its distribution function)
  `exercise_9_C_3b` proves that the linear-cutoff profile (cutoff `2p/(2 − δ)`, second price half
  the cutoff, first price `(2 − δ)²/(2 (4 − 3δ))`) is a weak PBE and the unique one with consistent
  beliefs (`IsSBUConsistent`); `exercise_9_C_3b_not_unique` exhibits another weak PBE first price
  (off-path beliefs after the seller's own deviations).
-/

namespace MWG.DynamicGames

/-- The buyer's value: `vH` for the high type (`true`), `vL` for the low type (`false`). -/
def sbVal (vL vH : ℝ) (b : Bool) : ℝ := if b then vH else vL

/-- The prior probability of a type: `λ` for the high type, `1 − λ` for the low type. -/
def sbPrior (lam : ℝ) (b : Bool) : ℝ := if b then lam else 1 - lam

/-- A buyer with value `v` who rejects in period 1 and faces the price `q` in period 2 accepts iff
`q ≤ v`, and gets `δ (v − q)` or `0`. -/
noncomputable def sbCont (δ v q : ℝ) : ℝ := if q ≤ v then δ * (v - q) else 0

/-- The seller's undiscounted period-2 expected revenue at price `q` when she believes the
buyer is of the high type with probability `m`. -/
noncomputable def sbRev (vL vH m q : ℝ) : ℝ :=
  m * (if q ≤ vH then q else 0) + (1 - m) * (if q ≤ vL then q else 0)

/-- A pure strategy profile with beliefs: the seller's first price `p1`, the buyer's period-1
acceptance rule `acc b p`, the seller's second price `p2 p` after a rejection of `p`, and her
belief `μ p` that the buyer is of the high type there. -/
structure SBProfile where
  /-- The seller's first-period price. -/
  p1 : ℝ
  /-- Whether type `b` accepts the first-period price `p`. -/
  acc : Bool → ℝ → Bool
  /-- The seller's second-period price after the first-period price `p` was rejected. -/
  p2 : ℝ → ℝ
  /-- The seller's belief that `v = vH` after the first-period price `p` was rejected. -/
  μ : ℝ → ℝ

/-- The seller's expected payoff when she charges `p` and, after a rejection, `q`, against the
buyer's acceptance rule `acc`. -/
noncomputable def sbPay (vL vH lam δ : ℝ) (acc : Bool → ℝ → Bool) (p q : ℝ) : ℝ :=
  lam * (if acc true p then p else δ * (if q ≤ vH then q else 0)) +
    (1 - lam) * (if acc false p then p else δ * (if q ≤ vL then q else 0))

/-- Bayes' posterior on the high type after the price `p` is rejected. -/
noncomputable def sbPost (lam : ℝ) (acc : Bool → ℝ → Bool) (p : ℝ) : ℝ :=
  (if acc true p then 0 else lam) /
    ((if acc true p then 0 else lam) + (if acc false p then 0 else 1 - lam))

/-- **Exercise 9.C.3** (MWG, p. 304). A pure-strategy weak perfect Bayesian equilibrium of the
two-type bargaining game (Definition 9.C.3). -/
def IsSBWeakPBE (vL vH lam δ : ℝ) (P : SBProfile) : Prop :=
  (∀ b p, P.acc b p = true ↔ sbCont δ (sbVal vL vH b) (P.p2 p) ≤ sbVal vL vH b - p) ∧
  (∀ p, 0 ≤ P.μ p ∧ P.μ p ≤ 1) ∧
  (∀ p q, δ * sbRev vL vH (P.μ p) q ≤ δ * sbRev vL vH (P.μ p) (P.p2 p)) ∧
  ((P.acc true P.p1 = false ∨ P.acc false P.p1 = false) → P.μ P.p1 = sbPost lam P.acc P.p1) ∧
  ∀ p q, sbPay vL vH lam δ P.acc p q ≤ sbPay vL vH lam δ P.acc P.p1 (P.p2 P.p1)

/-- **Exercise 9.C.6** (MWG, p. 304), structural consistency: after every price that some type
rejects (on or off the equilibrium path), the seller's belief is Bayes' posterior. -/
def IsSBConsistent (lam : ℝ) (P : SBProfile) : Prop :=
  ∀ p, (P.acc true p = false ∨ P.acc false p = false) → P.μ p = sbPost lam P.acc p

/-- In period 2 the buyer is sequentially rational exactly when she accepts iff `q ≤ v`
(accepting gives `δ (v − q)`, rejecting `0`, and she accepts when indifferent). -/
theorem sb_period2 {δ v q : ℝ} (hd : 0 < δ) : 0 ≤ δ * (v - q) ↔ q ≤ v := by
  constructor
  · intro h
    by_contra hn
    push Not at hn
    nlinarith
  · intro h
    exact mul_nonneg hd.le (by linarith)

variable {vL vH lam δ : ℝ}

theorem sbRev_vL (hLH : vL < vH) (m : ℝ) : sbRev vL vH m vL = vL := by
  simp only [sbRev, hLH.le, le_refl, ↓reduceIte]
  ring

theorem sbRev_vH (hLH : vL < vH) (m : ℝ) : sbRev vL vH m vH = m * vH := by
  simp only [sbRev, le_refl, ↓reduceIte, not_le.2 hLH]
  ring

/-- The seller's period-2 revenue never exceeds the larger of `vL` (price `vL`, both types
buy) and `m vH` (price `vH`, only the high type buys). -/
theorem sbRev_le (hL : 0 < vL) (hLH : vL < vH) {m : ℝ} (hm : 0 ≤ m ∧ m ≤ 1) (q : ℝ) :
    sbRev vL vH m q ≤ vL ∨ sbRev vL vH m q ≤ m * vH := by
  unfold sbRev
  by_cases h1 : q ≤ vL
  · left
    simp only [h1, le_trans h1 hLH.le, ↓reduceIte]
    nlinarith
  · by_cases h2 : q ≤ vH
    · right
      simp only [h1, h2, ↓reduceIte]
      nlinarith
    · left
      simp only [h1, h2, ↓reduceIte]
      linarith

/-- With `0 < vL < vH`, the seller's optimal period-2 price is `vL` or `vH`, whatever her
belief. -/
theorem sb_p2_mem (hL : 0 < vL) (hLH : vL < vH) {m q : ℝ} (hm : 0 ≤ m ∧ m ≤ 1)
    (hq : ∀ q', sbRev vL vH m q' ≤ sbRev vL vH m q) : q = vL ∨ q = vH := by
  have h1 := hq vL
  have h2 := hq vH
  rw [sbRev_vL hLH] at h1
  rw [sbRev_vH hLH] at h2
  unfold sbRev at h1 h2
  by_cases a : q ≤ vL
  · left
    simp only [a, le_trans a hLH.le, ↓reduceIte] at h1
    linarith
  · by_cases b : q ≤ vH
    · right
      simp only [a, b, ↓reduceIte] at h1 h2
      have hm0 : 0 < m := by
        by_contra hn
        have : m = 0 := le_antisymm (not_lt.1 hn) hm.1
        rw [this] at h1
        linarith
      have : vH ≤ q := le_of_mul_le_mul_left (by linarith) hm0
      linarith
    · simp only [a, b, ↓reduceIte] at h1
      linarith

/-- The seller's period-2 price when one of the two prices is strictly better. -/
theorem sb_p2_of_lt (hLH : vL < vH) {m q : ℝ} (hq : ∀ q', sbRev vL vH m q' ≤ sbRev vL vH m q)
    (hq2 : q = vL ∨ q = vH) : (m * vH < vL → q = vL) ∧ (vL < m * vH → q = vH) := by
  have h1 := hq vL
  have h2 := hq vH
  rw [sbRev_vL hLH] at h1
  rw [sbRev_vH hLH] at h2
  constructor
  · intro h
    rcases hq2 with rfl | rfl
    · rfl
    · rw [sbRev_vH hLH] at h1
      linarith
  · intro h
    rcases hq2 with rfl | rfl
    · rw [sbRev_vL hLH] at h2
      linarith
    · rfl

/-- The highest first-period price that the high type accepts when she expects the price `vL`
in period 2: `p̂ = (1 − δ) vH + δ vL`. -/
def sbHat (vL vH δ : ℝ) : ℝ := (1 - δ) * vH + δ * vL

/-- The buyer's period-1 decision when the period-2 price is `vL` or `vH`: the low type accepts
`p` iff `p ≤ vL`; the high type accepts iff `p ≤ p̂` (period-2 price `vL`) or `p ≤ vH` (period-2
price `vH`). -/
theorem sb_buyer {acc : Bool → ℝ → Bool} {p2 : ℝ → ℝ} (hLH : vL < vH)
    (hacc : ∀ b p, acc b p = true ↔ sbCont δ (sbVal vL vH b) (p2 p) ≤ sbVal vL vH b - p)
    {p : ℝ} (hp2 : p2 p = vL ∨ p2 p = vH) :
    (acc false p = true ↔ p ≤ vL) ∧ (p2 p = vL → (acc true p = true ↔ p ≤ sbHat vL vH δ)) ∧
      (p2 p = vH → (acc true p = true ↔ p ≤ vH)) := by
  have hl := hacc false p
  have hh := hacc true p
  simp only [sbVal, Bool.false_eq_true, ↓reduceIte] at hl hh
  refine ⟨?_, fun h => ?_, fun h => ?_⟩
  · rcases hp2 with h | h <;> rw [h] at hl <;> rw [hl] <;>
      simp [sbCont, not_le.2 hLH]
  · rw [h] at hh
    rw [hh]
    simp only [sbCont, hLH.le, ↓reduceIte, sbHat]
    constructor <;> intro <;> linarith
  · rw [h] at hh
    rw [hh]
    simp only [sbCont, le_refl, ↓reduceIte, sub_self, mul_zero]
    constructor <;> intro <;> linarith

theorem sbHat_mem (hLH : vL < vH) (hd0 : 0 < δ) (hd1 : δ < 1) :
    vL < sbHat vL vH δ ∧ sbHat vL vH δ < vH := by
  unfold sbHat
  constructor <;> nlinarith

/-- An upper bound on the seller's payoff from any deviation, when her period-2 price is `vL`
after every price except possibly prices above `vH` (where it may be `vH`): at most the
largest of `vL`, `λ p̂ + (1 − λ) δ vL` and `δ λ vH`. -/
theorem sbPay_le (hL : 0 < vL) (hLH : vL < vH) (hl0 : 0 < lam) (hl1 : lam < 1) (hd0 : 0 < δ)
    (hd1 : δ < 1) {acc : Bool → ℝ → Bool} {p2 : ℝ → ℝ}
    (hacc : ∀ b p, acc b p = true ↔ sbCont δ (sbVal vL vH b) (p2 p) ≤ sbVal vL vH b - p)
    (hp2 : ∀ p, p2 p = vL ∨ (p2 p = vH ∧ vH < p)) {M : ℝ} (hA : vL ≤ M)
    (hB : lam * sbHat vL vH δ + (1 - lam) * (δ * vL) ≤ M) (hC : δ * (lam * vH) ≤ M)
    (p q : ℝ) : sbPay vL vH lam δ acc p q ≤ M := by
  obtain ⟨hh1, hh2⟩ := sbHat_mem hLH hd0 hd1
  have hp2' : p2 p = vL ∨ p2 p = vH := by rcases hp2 p with h | h; exacts [Or.inl h, Or.inr h.1]
  obtain ⟨bl, bh1, bh2⟩ := sb_buyer hLH hacc hp2'
  have hqL : (if q ≤ vL then q else 0) ≤ vL := by split_ifs <;> linarith
  unfold sbPay
  by_cases h1 : p ≤ vL
  · have hH : acc true p = true := by
      rcases hp2 p with h | h
      · exact (bh1 h).2 (by linarith)
      · linarith [h.2]
    rw [hH, bl.2 h1]
    simp only [↓reduceIte]
    nlinarith
  · have hLo : acc false p = false := by
      cases h : acc false p
      · rfl
      · exact absurd (bl.1 h) h1
    by_cases h2 : p ≤ sbHat vL vH δ
    · have hH : acc true p = true := by
        rcases hp2 p with h | h
        · exact (bh1 h).2 h2
        · linarith [h.2]
      rw [hH, hLo]
      simp only [↓reduceIte, Bool.false_eq_true]
      nlinarith [mul_le_mul_of_nonneg_left h2 hl0.le, mul_le_mul_of_nonneg_left hqL hd0.le]
    · have hH : acc true p = false := by
        cases h : acc true p
        · rfl
        · rcases hp2 p with h' | h'
          · exact absurd ((bh1 h').1 h) h2
          · exact absurd ((bh2 h'.1).1 h) (not_le.2 h'.2)
      rw [hH, hLo]
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hR := sbRev_le hL hLH ⟨hl0.le, hl1.le⟩ q
      unfold sbRev at hR
      rcases hR with hR | hR <;> nlinarith

/-- In a weak PBE the seller's period-2 price after any rejected price is optimal for her belief,
and it is `vL` or `vH`. -/
theorem sb_weakPBE_p2 (hL : 0 < vL) (hLH : vL < vH) (hd0 : 0 < δ) {P : SBProfile}
    (h : IsSBWeakPBE vL vH lam δ P) (p : ℝ) :
    (∀ q, sbRev vL vH (P.μ p) q ≤ sbRev vL vH (P.μ p) (P.p2 p)) ∧
      (P.p2 p = vL ∨ P.p2 p = vH) := by
  have hq : ∀ q, sbRev vL vH (P.μ p) q ≤ sbRev vL vH (P.μ p) (P.p2 p) :=
    fun q => le_of_mul_le_mul_left (h.2.2.1 p q) hd0
  exact ⟨hq, sb_p2_mem hL hLH (h.2.1 p) hq⟩

/-- **Exercise 9.C.3(a), cutoff structure** (MWG, p. 304). In a weak PBE, at every first-period
price the high type accepts whenever the low type does. -/
theorem sb_acc_mono (hL : 0 < vL) (hLH : vL < vH) (hd0 : 0 < δ) (hd1 : δ < 1)
    {P : SBProfile} (h : IsSBWeakPBE vL vH lam δ P) (p : ℝ) (hp : P.acc false p = true) :
    P.acc true p = true := by
  obtain ⟨-, hp2⟩ := sb_weakPBE_p2 hL hLH hd0 h p
  obtain ⟨bl, bh1, bh2⟩ := sb_buyer hLH h.1 hp2
  obtain ⟨hh1, -⟩ := sbHat_mem hLH hd0 hd1
  have := bl.1 hp
  rcases hp2 with h2 | h2
  · exact (bh1 h2).2 (by linarith)
  · exact (bh2 h2).2 (by linarith)

/-- **Exercise 9.C.3(a)** (MWG, p. 304), necessity. Every pure-strategy weak PBE has one of three
outcomes: (i) `p1 = vL` and both types buy at once, possible only if `vL ≥ λ p̂ + (1 − λ) δ vL`
and `vL ≥ δ λ vH`; (ii) `p1 = p̂`, the high type buys at once and the low type buys at `vL` in
period 2, possible only if `λ p̂ + (1 − λ) δ vL` is the largest of the three numbers; (iii)
`p1 > vH`, nobody buys in period 1 and the seller charges `vH` in period 2, possible only if
`δ λ vH` is the largest. In each case the seller's payoff is the largest of the three. -/
theorem sb_weakPBE_outcome (hL : 0 < vL) (hLH : vL < vH) (hl0 : 0 < lam) (hl1 : lam < 1)
    (hd0 : 0 < δ) (hd1 : δ < 1) {P : SBProfile} (h : IsSBWeakPBE vL vH lam δ P) :
    (P.p1 = vL ∧ P.acc true P.p1 = true ∧ P.acc false P.p1 = true ∧
        lam * sbHat vL vH δ + (1 - lam) * (δ * vL) ≤ vL ∧ δ * (lam * vH) ≤ vL ∧
        sbPay vL vH lam δ P.acc P.p1 (P.p2 P.p1) = vL) ∨
    (P.p1 = sbHat vL vH δ ∧ P.acc true P.p1 = true ∧ P.acc false P.p1 = false ∧
        P.p2 P.p1 = vL ∧ vL ≤ lam * sbHat vL vH δ + (1 - lam) * (δ * vL) ∧
        δ * (lam * vH) ≤ lam * sbHat vL vH δ + (1 - lam) * (δ * vL) ∧
        sbPay vL vH lam δ P.acc P.p1 (P.p2 P.p1) = lam * sbHat vL vH δ + (1 - lam) * (δ * vL)) ∨
    (vH < P.p1 ∧ P.acc true P.p1 = false ∧ P.acc false P.p1 = false ∧ P.p2 P.p1 = vH ∧
        vL ≤ δ * (lam * vH) ∧ lam * sbHat vL vH δ + (1 - lam) * (δ * vL) ≤ δ * (lam * vH) ∧
        sbPay vL vH lam δ P.acc P.p1 (P.p2 P.p1) = δ * (lam * vH)) := by
  obtain ⟨hh1, hh2⟩ := sbHat_mem hLH hd0 hd1
  have hroot := h.2.2.2.2
  have hB2 := fun p => sb_buyer hLH h.1 (sb_weakPBE_p2 hL hLH hd0 h p).2
  have hp2 := fun p => (sb_weakPBE_p2 hL hLH hd0 h p).2
  set S := sbPay vL vH lam δ P.acc P.p1 (P.p2 P.p1) with hS
  -- the three deviations
  have dA : vL ≤ S := by
    have hLo : P.acc false vL = true := (hB2 vL).1.2 le_rfl
    have hH : P.acc true vL = true := sb_acc_mono hL hLH hd0 hd1 h vL hLo
    have := hroot vL 0
    rw [sbPay, hH, hLo] at this
    simp only [↓reduceIte] at this
    linarith
  have dB : lam * sbHat vL vH δ + (1 - lam) * (δ * vL) ≤ S := by
    have hLo : P.acc false (sbHat vL vH δ) = false := by
      cases hc : P.acc false (sbHat vL vH δ)
      · rfl
      · exact absurd ((hB2 _).1.1 hc) (not_le.2 hh1)
    have hH : P.acc true (sbHat vL vH δ) = true := by
      rcases hp2 (sbHat vL vH δ) with h2 | h2
      · exact ((hB2 _).2.1 h2).2 le_rfl
      · exact ((hB2 _).2.2 h2).2 hh2.le
    have := hroot (sbHat vL vH δ) vL
    rw [sbPay, hH, hLo] at this
    simp only [↓reduceIte, Bool.false_eq_true, le_refl] at this
    linarith
  have dC : δ * (lam * vH) ≤ S := by
    have hLo : P.acc false (vH + 1) = false := by
      cases hc : P.acc false (vH + 1)
      · rfl
      · have := (hB2 _).1.1 hc; linarith
    have hH : P.acc true (vH + 1) = false := by
      cases hc : P.acc true (vH + 1)
      · rfl
      · rcases hp2 (vH + 1) with h2 | h2
        · have := ((hB2 _).2.1 h2).1 hc; linarith
        · have := ((hB2 _).2.2 h2).1 hc; linarith
    have := hroot (vH + 1) vH
    rw [sbPay, hH, hLo] at this
    simp only [↓reduceIte, Bool.false_eq_true, le_refl, not_le.2 hLH] at this
    linarith
  -- the equilibrium
  cases hLo : P.acc false P.p1
  · cases hH : P.acc true P.p1
    · -- both reject: the posterior is `λ`
      have hμ : P.μ P.p1 = lam := by
        rw [h.2.2.2.1 (Or.inl hH), sbPost, hH, hLo]
        simp
      obtain ⟨hq, -⟩ := sb_weakPBE_p2 hL hLH hd0 h P.p1
      rw [hμ] at hq
      have hS' : S = δ * sbRev vL vH lam (P.p2 P.p1) := by
        rw [hS, sbPay, hH, hLo, sbRev]
        simp only [Bool.false_eq_true, ↓reduceIte]
        ring
      rcases hp2 P.p1 with h2 | h2
      · rw [hS', h2, sbRev_vL hLH] at dA
        nlinarith
      · rw [hS', h2, sbRev_vH hLH] at dA dB
        have hgt : vH < P.p1 := by
          by_contra hn
          have := ((hB2 _).2.2 h2).2 (not_lt.1 hn)
          rw [hH] at this
          exact Bool.false_ne_true this
        right; right
        refine ⟨hgt, rfl, rfl, h2, by linarith, by linarith, ?_⟩
        rw [hS', h2, sbRev_vH hLH]
    · -- only the low type rejects: the posterior is `0`
      have hμ : P.μ P.p1 = 0 := by
        rw [h.2.2.2.1 (Or.inr hLo), sbPost, hH, hLo]
        simp
      obtain ⟨hq, -⟩ := sb_weakPBE_p2 hL hLH hd0 h P.p1
      rw [hμ] at hq
      have h2 : P.p2 P.p1 = vL :=
        (sb_p2_of_lt hLH hq (hp2 P.p1)).1 (by linarith)
      have hle : P.p1 ≤ sbHat vL vH δ := ((hB2 _).2.1 h2).1 hH
      have hS' : S = lam * P.p1 + (1 - lam) * (δ * vL) := by
        rw [hS, sbPay, hH, hLo, h2]
        simp only [Bool.false_eq_true, ↓reduceIte, le_refl]
      have heq : P.p1 = sbHat vL vH δ := by
        rw [hS'] at dB
        exact le_antisymm hle (le_of_mul_le_mul_left (by linarith) hl0)
      right; left
      have hSv : S = lam * sbHat vL vH δ + (1 - lam) * (δ * vL) := by rw [hS', heq]
      refine ⟨heq, rfl, rfl, h2, by linarith, by linarith, hSv⟩
  · have hH := sb_acc_mono hL hLH hd0 hd1 h P.p1 hLo
    have hle := (hB2 P.p1).1.1 hLo
    have hS' : S = P.p1 := by
      rw [hS, sbPay, hH, hLo]
      simp only [↓reduceIte]
      ring
    have heq : P.p1 = vL := le_antisymm hle (by linarith)
    left
    exact ⟨heq, hH, rfl, by linarith, by linarith, by rw [hS', heq]⟩

/-- The profile with first price `p1`, period-2 prices `p2`, beliefs `μ`, and the buyer's
sequentially rational period-1 acceptance rule. -/
noncomputable def sbBuild (vL vH δ p1 : ℝ) (p2 μ : ℝ → ℝ) : SBProfile where
  p1 := p1
  acc b p := decide (sbCont δ (sbVal vL vH b) (p2 p) ≤ sbVal vL vH b - p)
  p2 := p2
  μ := μ

theorem sbBuild_acc (p1 : ℝ) (p2 μ : ℝ → ℝ) (b : Bool) (p : ℝ) :
    (sbBuild vL vH δ p1 p2 μ).acc b p = true ↔
      sbCont δ (sbVal vL vH b) ((sbBuild vL vH δ p1 p2 μ).p2 p) ≤ sbVal vL vH b - p := by
  simp [sbBuild]

/-- A sufficient condition for `sbBuild` to be a weak PBE: beliefs in `[0, 1]`, period-2 prices
optimal for the beliefs and equal to `vL` except possibly above `vH`, Bayes' rule at `p1`, and a
payoff at `p1` at least the three benchmark payoffs. -/
theorem sbBuild_isWeakPBE (hL : 0 < vL) (hLH : vL < vH) (hl0 : 0 < lam) (hl1 : lam < 1)
    (hd0 : 0 < δ) (hd1 : δ < 1) {p1 : ℝ} {p2 μ : ℝ → ℝ} (hμ : ∀ p, 0 ≤ μ p ∧ μ p ≤ 1)
    (hopt : ∀ p q, sbRev vL vH (μ p) q ≤ sbRev vL vH (μ p) (p2 p))
    (hp2 : ∀ p, p2 p = vL ∨ (p2 p = vH ∧ vH < p))
    (hbayes : ((sbBuild vL vH δ p1 p2 μ).acc true p1 = false ∨
      (sbBuild vL vH δ p1 p2 μ).acc false p1 = false) →
      μ p1 = sbPost lam (sbBuild vL vH δ p1 p2 μ).acc p1)
    (hA : vL ≤ sbPay vL vH lam δ (sbBuild vL vH δ p1 p2 μ).acc p1 (p2 p1))
    (hB : lam * sbHat vL vH δ + (1 - lam) * (δ * vL) ≤
      sbPay vL vH lam δ (sbBuild vL vH δ p1 p2 μ).acc p1 (p2 p1))
    (hC : δ * (lam * vH) ≤ sbPay vL vH lam δ (sbBuild vL vH δ p1 p2 μ).acc p1 (p2 p1)) :
    IsSBWeakPBE vL vH lam δ (sbBuild vL vH δ p1 p2 μ) :=
  ⟨sbBuild_acc p1 p2 μ, hμ, fun p q => mul_le_mul_of_nonneg_left (hopt p q) hd0.le, hbayes,
    fun p q => sbPay_le hL hLH hl0 hl1 hd0 hd1 (sbBuild_acc p1 p2 μ) hp2 hA hB hC p q⟩

/-- The buyer's choices in `sbBuild` when the period-2 price is `vL` after `p`. -/
theorem sbBuild_acc_vL (hLH : vL < vH) {p1 p : ℝ} {p2 μ : ℝ → ℝ} (h2 : p2 p = vL) :
    ((sbBuild vL vH δ p1 p2 μ).acc false p = true ↔ p ≤ vL) ∧
      ((sbBuild vL vH δ p1 p2 μ).acc true p = true ↔ p ≤ sbHat vL vH δ) :=
  have h := sb_buyer (δ := δ) hLH (sbBuild_acc p1 p2 μ) (Or.inl h2)
  ⟨h.1, h.2.1 h2⟩

/-- The period-2 revenue is at most `vL` at any belief `m` with `m vH ≤ vL`. -/
theorem sbRev_le_vL (hL : 0 < vL) (hLH : vL < vH) {m : ℝ} (hm : 0 ≤ m ∧ m ≤ 1)
    (hmv : m * vH ≤ vL) (q : ℝ) : sbRev vL vH m q ≤ vL := by
  rcases sbRev_le hL hLH hm q with h | h <;> linarith

theorem bool_false_of_not {b : Bool} (h : ¬ b = true) : b = false := by
  cases b
  · rfl
  · exact absurd rfl h

/-- **Exercise 9.C.3(a)** (MWG, p. 304). Write `p̂ = (1 − δ) vH + δ vL`, `A = vL`,
`B = λ p̂ + (1 − λ) δ vL`, `C = δ λ vH`. Every pure-strategy weak PBE has outcome (i) `p1 = vL`,
immediate sale to both types, (ii) `p1 = p̂`, immediate sale to the high type and sale to the low
type at `vL` in period 2, or (iii) `p1 > vH`, no sale in period 1 and sale to the high type at
`vH` in period 2 (`sb_weakPBE_outcome`, which also gives the necessary conditions and the
seller's payoff `max {A, B, C}`); conversely each outcome is that of a weak PBE whenever its
benchmark is the largest of `A`, `B`, `C`. -/
theorem exercise_9_C_3a (hL : 0 < vL) (hLH : vL < vH) (hl0 : 0 < lam) (hl1 : lam < 1)
    (hd0 : 0 < δ) (hd1 : δ < 1) :
    (lam * sbHat vL vH δ + (1 - lam) * (δ * vL) ≤ vL → δ * (lam * vH) ≤ vL →
      ∃ P, IsSBWeakPBE vL vH lam δ P ∧ P.p1 = vL ∧ P.acc true P.p1 = true ∧
        P.acc false P.p1 = true) ∧
    (vL ≤ lam * sbHat vL vH δ + (1 - lam) * (δ * vL) →
      δ * (lam * vH) ≤ lam * sbHat vL vH δ + (1 - lam) * (δ * vL) →
      ∃ P, IsSBWeakPBE vL vH lam δ P ∧ P.p1 = sbHat vL vH δ ∧ P.acc true P.p1 = true ∧
        P.acc false P.p1 = false ∧ P.p2 P.p1 = vL) ∧
    (vL ≤ δ * (lam * vH) → lam * sbHat vL vH δ + (1 - lam) * (δ * vL) ≤ δ * (lam * vH) →
      ∃ P, IsSBWeakPBE vL vH lam δ P ∧ vH < P.p1 ∧ P.acc true P.p1 = false ∧
        P.acc false P.p1 = false ∧ P.p2 P.p1 = vH) := by
  obtain ⟨hh1, hh2⟩ := sbHat_mem hLH hd0 hd1
  have hμ0 : ∀ p : ℝ, 0 ≤ (fun _ => (0 : ℝ)) p ∧ (fun _ => (0 : ℝ)) p ≤ 1 :=
    fun _ => ⟨le_rfl, zero_le_one⟩
  have hopt0 : ∀ p q : ℝ, sbRev vL vH ((fun _ => (0 : ℝ)) p) q ≤
      sbRev vL vH ((fun _ => (0 : ℝ)) p) ((fun _ => vL) p) := fun p q => by
    rw [sbRev_vL hLH]
    exact sbRev_le_vL hL hLH ⟨le_rfl, zero_le_one⟩ (by simp [hL.le]) q
  refine ⟨fun hB hC => ?_, fun hA hC => ?_, fun hA hB => ?_⟩
  · -- (i)
    obtain ⟨bl, bh⟩ := sbBuild_acc_vL (δ := δ) (p1 := vL) (μ := fun _ => 0) hLH
      (p2 := fun _ => vL) (p := vL) rfl
    have hLo := bl.2 le_rfl
    have hH := bh.2 hh1.le
    have hpay : sbPay vL vH lam δ (sbBuild vL vH δ vL (fun _ => vL) fun _ => 0).acc vL vL =
        vL := by
      rw [sbPay, hH, hLo]
      simp only [↓reduceIte]
      ring
    refine ⟨_, sbBuild_isWeakPBE hL hLH hl0 hl1 hd0 hd1 hμ0 hopt0 (fun _ => Or.inl rfl)
      (fun h => ?_) (by rw [hpay]) (by rw [hpay]; exact hB) (by rw [hpay]; exact hC),
      rfl, hH, hLo⟩
    rcases h with h | h
    · rw [hH] at h; exact absurd h (by decide)
    · rw [hLo] at h; exact absurd h (by decide)
  · -- (ii)
    set P := sbBuild vL vH δ (sbHat vL vH δ) (fun _ => vL) fun _ => 0 with hP
    obtain ⟨bl, bh⟩ := sbBuild_acc_vL (δ := δ) (p1 := sbHat vL vH δ) (μ := fun _ => 0) hLH
      (p2 := fun _ => vL) (p := sbHat vL vH δ) rfl
    have hH : P.acc true (sbHat vL vH δ) = true := bh.2 le_rfl
    have hLo : P.acc false (sbHat vL vH δ) = false :=
      bool_false_of_not fun h => absurd (bl.1 h) (not_le.2 hh1)
    have hpay : sbPay vL vH lam δ P.acc (sbHat vL vH δ) vL =
        lam * sbHat vL vH δ + (1 - lam) * (δ * vL) := by
      rw [sbPay, hH, hLo]
      simp only [↓reduceIte, Bool.false_eq_true, le_refl]
    refine ⟨P, sbBuild_isWeakPBE hL hLH hl0 hl1 hd0 hd1 hμ0 hopt0 (fun _ => Or.inl rfl)
      (fun _ => ?_) (by rw [hpay]; exact hA) (by rw [hpay]) (by rw [hpay]; exact hC),
      rfl, hH, hLo, rfl⟩
    rw [sbPost, hH, hLo]
    simp
  · -- (iii)
    have hlv : vL ≤ lam * vH := by nlinarith
    set p2 : ℝ → ℝ := fun p => if p = vH + 1 then vH else vL with hp2
    set μ : ℝ → ℝ := fun p => if p = vH + 1 then lam else 0 with hμ
    set P := sbBuild vL vH δ (vH + 1) p2 μ with hP
    have h2 : p2 (vH + 1) = vH := by simp [hp2]
    obtain ⟨bl, -, bh⟩ := sb_buyer (δ := δ) hLH (sbBuild_acc (vH + 1) p2 μ)
      (p := vH + 1) (Or.inr h2)
    have hH : P.acc true (vH + 1) = false :=
      bool_false_of_not fun h => by have := (bh h2).1 h; linarith
    have hLo : P.acc false (vH + 1) = false :=
      bool_false_of_not fun h => by have := bl.1 h; linarith
    have hpay : sbPay vL vH lam δ P.acc (vH + 1) (p2 (vH + 1)) = δ * (lam * vH) := by
      rw [sbPay, hH, hLo, h2]
      simp only [Bool.false_eq_true, ↓reduceIte, le_refl, not_le.2 hLH]
      ring
    have hμ' : ∀ p, 0 ≤ μ p ∧ μ p ≤ 1 := fun p => by
      simp only [hμ]; split_ifs <;> constructor <;> linarith
    have hopt : ∀ p q, sbRev vL vH (μ p) q ≤ sbRev vL vH (μ p) (p2 p) := fun p q => by
      by_cases hp : p = vH + 1
      · simp only [hμ, hp2, hp, ↓reduceIte]
        rw [sbRev_vH hLH]
        rcases sbRev_le hL hLH ⟨hl0.le, hl1.le⟩ q with h | h <;> linarith
      · simp only [hμ, hp2, hp, ↓reduceIte]
        rw [sbRev_vL hLH]
        exact sbRev_le_vL hL hLH ⟨le_rfl, zero_le_one⟩ (by simp [hL.le]) q
    have hp2' : ∀ p, p2 p = vL ∨ (p2 p = vH ∧ vH < p) := fun p => by
      by_cases hp : p = vH + 1
      · right; simp only [hp2, hp, ↓reduceIte]; exact ⟨trivial, by linarith⟩
      · left; simp [hp2, hp]
    refine ⟨P, sbBuild_isWeakPBE hL hLH hl0 hl1 hd0 hd1 hμ' hopt hp2' (fun _ => ?_)
      (by rw [hpay]; exact hA) (by rw [hpay]; exact hB) (by rw [hpay]), by simp [hP, sbBuild],
      hH, hLo, h2⟩
    rw [sbPost, hH, hLo]
    simp [hμ]

/-- A weak PBE always exists in the two-type game (one of the three benchmarks is largest). -/
theorem exercise_9_C_3a_exists (hL : 0 < vL) (hLH : vL < vH) (hl0 : 0 < lam) (hl1 : lam < 1)
    (hd0 : 0 < δ) (hd1 : δ < 1) : ∃ P, IsSBWeakPBE vL vH lam δ P := by
  obtain ⟨h1, h2, h3⟩ := exercise_9_C_3a hL hLH hl0 hl1 hd0 hd1
  rcases le_total (lam * sbHat vL vH δ + (1 - lam) * (δ * vL)) vL with hB | hB
  · rcases le_total (δ * (lam * vH)) vL with hC | hC
    · obtain ⟨P, hP, -⟩ := h1 hB hC; exact ⟨P, hP⟩
    · obtain ⟨P, hP, -⟩ := h3 hC (by linarith); exact ⟨P, hP⟩
  · rcases le_total (δ * (lam * vH)) (lam * sbHat vL vH δ + (1 - lam) * (δ * vL)) with hC | hC
    · obtain ⟨P, hP, -⟩ := h2 hB hC; exact ⟨P, hP⟩
    · obtain ⟨P, hP, -⟩ := h3 (by linarith) hC; exact ⟨P, hP⟩

/-- **Exercise 9.C.3(a), examples** (MWG, p. 304). Each of the three outcomes occurs: with
`vL = 1`, `vH = 2`, `δ = 1/2`, outcome (i) for `λ = 1/10` and outcome (ii) for `λ = 9/10`; with
`vL = 1`, `vH = 10`, `λ = δ = 9/10`, outcome (iii). -/
theorem exercise_9_C_3a_examples :
    (∃ P, IsSBWeakPBE 1 2 (1 / 10) (1 / 2) P ∧ P.p1 = 1) ∧
    (∃ P, IsSBWeakPBE 1 2 (9 / 10) (1 / 2) P ∧ P.p1 = 3 / 2) ∧
    (∃ P, IsSBWeakPBE 1 10 (9 / 10) (9 / 10) P ∧ 10 < P.p1) := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨P, hP, h1, -⟩ := (exercise_9_C_3a (vL := 1) (vH := 2) (lam := 1 / 10)
      (δ := 1 / 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)).1 (by norm_num [sbHat]) (by norm_num)
    exact ⟨P, hP, h1⟩
  · obtain ⟨P, hP, h1, -⟩ := (exercise_9_C_3a (vL := 1) (vH := 2) (lam := 9 / 10)
      (δ := 1 / 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)).2.1 (by norm_num [sbHat]) (by norm_num [sbHat])
    exact ⟨P, hP, by rw [h1]; norm_num [sbHat]⟩
  · obtain ⟨P, hP, h1, -⟩ := (exercise_9_C_3a (vL := 1) (vH := 10) (lam := 9 / 10)
      (δ := 9 / 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)).2.2 (by norm_num) (by norm_num [sbHat])
    exact ⟨P, hP, h1⟩

/-- Bayes' posterior as a function of the two types' rejection probabilities. -/
theorem sbPost_eq (lam : ℝ) (acc : Bool → ℝ → Bool) (p : ℝ) :
    sbPost lam acc p = lam * (if acc true p then 0 else 1) /
      (lam * (if acc true p then 0 else 1) + (1 - lam) * (if acc false p then 0 else 1)) := by
  unfold sbPost
  split_ifs <;> simp

open Filter Topology in
/-- **Exercise 9.C.6, the consistency reading** (MWG, pp. 290 and 304). Suppose trembles give the
two types rejection probabilities `rH n → aH` and `rL n → aL` (and the seller's own trembles do
not depend on the buyer's type, so they cancel). If some type rejects in the limit
(`aH + aL > 0`), the Bayes beliefs converge to Bayes' posterior for the limit strategies. So in
the limit of totally mixed profiles, the seller's belief after a price that some type rejects
is `sbPost`; this is what `IsSBConsistent` imposes. -/
theorem sbPost_tendsto (hl0 : 0 < lam) (hl1 : lam < 1) {rH rL : ℕ → ℝ} {aH aL : ℝ}
    (hH : Tendsto rH atTop (𝓝 aH)) (hL : Tendsto rL atTop (𝓝 aL)) (haH : 0 ≤ aH)
    (haL : 0 ≤ aL) (hpos : 0 < aH + aL) :
    Tendsto (fun n => lam * rH n / (lam * rH n + (1 - lam) * rL n)) atTop
      (𝓝 (lam * aH / (lam * aH + (1 - lam) * aL))) := by
  have hne : lam * aH + (1 - lam) * aL ≠ 0 := by
    rcases haH.lt_or_eq with h | h
    · have : 0 < lam * aH := mul_pos hl0 h
      have : 0 ≤ (1 - lam) * aL := mul_nonneg (by linarith) haL
      linarith
    · have : 0 < (1 - lam) * aL := mul_pos (by linarith) (by linarith)
      rw [← h]
      linarith
  exact (hH.const_mul lam).div ((hH.const_mul lam).add (hL.const_mul (1 - lam))) hne

/-- **Exercise 9.C.6, two types, `λ vH > vL`** (MWG, p. 304). There is no pure-strategy
sequential equilibrium (no pure-strategy weak PBE whose beliefs are consistent after every
rejected price): after a first price strictly between `p̂` and `vH`, if the seller is expected to
charge `vL` both types reject, so she believes `λ` and must charge `vH`; if she is expected to
charge `vH` only the low type rejects, so she believes `0` and must charge `vL`. -/
theorem exercise_9_C_6_two_types_none (hL : 0 < vL) (hLH : vL < vH) (hd0 : 0 < δ) (hd1 : δ < 1)
    (hgt : vL < lam * vH) :
    ¬ ∃ P, IsSBWeakPBE vL vH lam δ P ∧ IsSBConsistent lam P := by
  rintro ⟨P, h, hc⟩
  obtain ⟨hh1, hh2⟩ := sbHat_mem hLH hd0 hd1
  set p := (sbHat vL vH δ + vH) / 2 with hp
  obtain ⟨hq, hp2⟩ := sb_weakPBE_p2 hL hLH hd0 h p
  obtain ⟨bl, bh1, bh2⟩ := sb_buyer hLH h.1 hp2
  have hLo : P.acc false p = false := bool_false_of_not fun h' => by have := bl.1 h'; linarith
  rcases hp2 with h2 | h2
  · have hH : P.acc true p = false :=
      bool_false_of_not fun h' => by have := (bh1 h2).1 h'; linarith
    have hμ : P.μ p = lam := by
      rw [hc p (Or.inl hH), sbPost, hH, hLo]
      simp
    rw [hμ] at hq
    have := (sb_p2_of_lt hLH hq (Or.inl h2)).2 hgt
    linarith
  · have hH : P.acc true p = true := (bh2 h2).2 (by linarith)
    have hμ : P.μ p = 0 := by
      rw [hc p (Or.inr hLo), sbPost, hH, hLo]
      simp
    rw [hμ] at hq
    have := (sb_p2_of_lt hLH hq (Or.inr h2)).1 (by linarith)
    linarith

/-- **Exercise 9.C.6, two types, `λ vH ≤ vL`** (MWG, p. 304). The pure-strategy sequential
equilibria (weak PBE with consistent beliefs after every rejected price) have outcome (i)
(`p1 = vL`) or (ii) (`p1 = p̂`) of `exercise_9_C_3a`, never (iii); and each of (i), (ii) is the
outcome of one whenever its benchmark is the larger. -/
theorem exercise_9_C_6_two_types (hL : 0 < vL) (hLH : vL < vH) (hl0 : 0 < lam) (hl1 : lam < 1)
    (hd0 : 0 < δ) (hd1 : δ < 1) (hle : lam * vH ≤ vL) :
    (∀ P, IsSBWeakPBE vL vH lam δ P → IsSBConsistent lam P →
      P.p1 = vL ∨ P.p1 = sbHat vL vH δ) ∧
    (lam * sbHat vL vH δ + (1 - lam) * (δ * vL) ≤ vL →
      ∃ P, IsSBWeakPBE vL vH lam δ P ∧ IsSBConsistent lam P ∧ P.p1 = vL) ∧
    (vL ≤ lam * sbHat vL vH δ + (1 - lam) * (δ * vL) →
      ∃ P, IsSBWeakPBE vL vH lam δ P ∧ IsSBConsistent lam P ∧ P.p1 = sbHat vL vH δ) := by
  obtain ⟨hh1, hh2⟩ := sbHat_mem hLH hd0 hd1
  have hC : δ * (lam * vH) < vL := by nlinarith
  set p2 : ℝ → ℝ := fun _ => vL with hp2
  set μ : ℝ → ℝ := fun p => if sbHat vL vH δ < p then lam else 0 with hμ
  have hμ' : ∀ p, 0 ≤ μ p ∧ μ p ≤ 1 := fun p => by
    simp only [hμ]; split_ifs <;> constructor <;> linarith
  have hopt : ∀ p q, sbRev vL vH (μ p) q ≤ sbRev vL vH (μ p) (p2 p) := fun p q => by
    simp only [hp2]
    rw [sbRev_vL hLH]
    refine sbRev_le_vL hL hLH (hμ' p) ?_ q
    simp only [hμ]
    split_ifs
    · exact hle
    · simp [hL.le]
  have hcons : ∀ p1, IsSBConsistent lam (sbBuild vL vH δ p1 p2 μ) := by
    intro p1 p hp
    obtain ⟨bl, bh⟩ := sbBuild_acc_vL (δ := δ) (p1 := p1) (μ := μ) hLH (p2 := p2) (p := p) rfl
    change μ p = _
    have hLo : (sbBuild vL vH δ p1 p2 μ).acc false p = false := by
      rcases hp with hp | hp
      · exact bool_false_of_not fun h' => by
          have h1 := bl.1 h'
          rw [bh.2 (by linarith)] at hp
          exact absurd hp (by decide)
      · exact hp
    by_cases hgt : sbHat vL vH δ < p
    · have hH : (sbBuild vL vH δ p1 p2 μ).acc true p = false :=
        bool_false_of_not fun h' => absurd (bh.1 h') (not_le.2 hgt)
      rw [sbPost, hH, hLo]
      simp [hμ, hgt]
    · have hH : (sbBuild vL vH δ p1 p2 μ).acc true p = true := bh.2 (not_lt.1 hgt)
      rw [sbPost, hH, hLo]
      simp [hμ, hgt]
  refine ⟨fun P h _ => ?_, fun hB => ?_, fun hB => ?_⟩
  · rcases sb_weakPBE_outcome hL hLH hl0 hl1 hd0 hd1 h with h1 | h1 | h1
    · exact Or.inl h1.1
    · exact Or.inr h1.1
    · linarith [h1.2.2.2.2.1]
  · obtain ⟨bl, bh⟩ := sbBuild_acc_vL (δ := δ) (p1 := vL) (μ := μ) hLH (p2 := p2) (p := vL) rfl
    have hLo := bl.2 le_rfl
    have hH := bh.2 hh1.le
    have hpay : sbPay vL vH lam δ (sbBuild vL vH δ vL p2 μ).acc vL (p2 vL) = vL := by
      rw [sbPay, hH, hLo]
      simp only [↓reduceIte]
      ring
    refine ⟨_, sbBuild_isWeakPBE hL hLH hl0 hl1 hd0 hd1 hμ' hopt (fun _ => Or.inl rfl)
      (fun h => hcons vL vL h) (by rw [hpay]) (by rw [hpay]; exact hB)
      (by rw [hpay]; exact hC.le), hcons vL, rfl⟩
  · set P := sbBuild vL vH δ (sbHat vL vH δ) p2 μ
    obtain ⟨bl, bh⟩ := sbBuild_acc_vL (δ := δ) (p1 := sbHat vL vH δ) (μ := μ) hLH (p2 := p2)
      (p := sbHat vL vH δ) rfl
    have hH : P.acc true (sbHat vL vH δ) = true := bh.2 le_rfl
    have hLo : P.acc false (sbHat vL vH δ) = false :=
      bool_false_of_not fun h => absurd (bl.1 h) (not_le.2 hh1)
    have hpay : sbPay vL vH lam δ P.acc (sbHat vL vH δ) (p2 (sbHat vL vH δ)) =
        lam * sbHat vL vH δ + (1 - lam) * (δ * vL) := by
      rw [sbPay, hH, hLo]
      simp only [↓reduceIte, Bool.false_eq_true, le_refl, hp2]
    refine ⟨P, sbBuild_isWeakPBE hL hLH hl0 hl1 hd0 hd1 hμ' hopt (fun _ => Or.inl rfl)
      (fun h => hcons _ _ h) (by rw [hpay]; exact hB) (by rw [hpay])
      (by rw [hpay]; linarith), hcons _, rfl⟩

/-! ### Exercise 9.C.3(b): values uniform on `[0, 1]` -/

/-- The cutoff type at the first price `p` when the second price is `r`: the buyer with value
`v` accepts `p` iff `κ ≤ v` (`exercise_9_C_3b_cutoff`). -/
noncomputable def sbKappa (δ p r : ℝ) : ℝ := if r ≤ p then (p - δ * r) / (1 - δ) else p

/-- **Exercise 9.C.3(b), cutoff structure** (MWG, p. 304). Whatever second price `r` the buyer
expects after rejecting `p`, she accepts `p` iff her value is at least `κ(p, r)`: her gain from
accepting, `v − p − δ (v − r)⁺`, is strictly increasing in `v`. -/
theorem exercise_9_C_3b_cutoff (hd1 : δ < 1) (v p r : ℝ) :
    sbCont δ v r ≤ v - p ↔ sbKappa δ p r ≤ v := by
  unfold sbCont sbKappa
  have h1 : 0 < 1 - δ := by linarith
  by_cases hrv : r ≤ v
  · simp only [hrv, ↓reduceIte]
    split_ifs with hrp
    · rw [div_le_iff₀ h1]
      constructor <;> intro <;> nlinarith
    · constructor <;> intro <;> nlinarith
  · simp only [hrv, ↓reduceIte]
    split_ifs with hrp
    · rw [div_le_iff₀ h1]
      constructor <;> intro <;> nlinarith
    · constructor <;> intro <;> linarith

/-- The mass of buyers who reject `p` (values in `[0, k)`, `k = κ` clamped to `[0, 1]`). -/
noncomputable def sbCut (δ p r : ℝ) : ℝ := max 0 (min (sbKappa δ p r) 1)

/-- The seller's expected payoff (values uniform on `[0, 1]`) from first price `p` and second
price `q`, when the buyer expects the second price `r`: the types `[k, 1]` buy at `p`, the types
in `[max q 0, k)` buy at `q` in period 2. -/
noncomputable def sbUPay (δ p r q : ℝ) : ℝ :=
  p * (1 - sbCut δ p r) + δ * q * max 0 (sbCut δ p r - max q 0)

/-- The seller's period-2 revenue at price `q` when her belief is uniform on `[0, k)` (the Bayes
posterior after the types below `k` reject): `q · Prob(v ≥ q)`. -/
noncomputable def sbURev (k q : ℝ) : ℝ := q * (max 0 (k - max q 0) / k)

/-- **Exercise 9.C.3(b)** (MWG, p. 304). A pure-strategy weak PBE of the uniform case, in reduced
form: the first price `p1` and the second price `r p` after each rejected price `p`; the buyer
uses the cutoff rule of `exercise_9_C_3b_cutoff`. Each `r p` is in `[0, 1]` (any such price is
optimal for some belief, `sb_point_mass_opt`); after `p1`, if some types reject, `r p1` is
optimal for the Bayes posterior (uniform on the rejecting types); `p1` is optimal against every
deviation `(p, q)`. -/
def IsSBUWeakPBE (δ p1 : ℝ) (r : ℝ → ℝ) : Prop :=
  (∀ p, 0 ≤ r p ∧ r p ≤ 1) ∧
  (0 < sbCut δ p1 (r p1) → ∀ q, sbURev (sbCut δ p1 (r p1)) q ≤
    sbURev (sbCut δ p1 (r p1)) (r p1)) ∧
  ∀ p q, sbUPay δ p (r p) q ≤ sbUPay δ p1 (r p1) (r p1)

/-- **Exercise 9.C.6 for 9.C.3(b)** (MWG, p. 304). Structural consistency: after every price that
a positive mass of types rejects, the second price is optimal for the Bayes posterior. -/
def IsSBUConsistent (δ : ℝ) (r : ℝ → ℝ) : Prop :=
  ∀ p, 0 < sbCut δ p (r p) → ∀ q, sbURev (sbCut δ p (r p)) q ≤ sbURev (sbCut δ p (r p)) (r p)

/-- Any price `r ∈ [0, 1]` is an optimal period-2 price for the belief that puts probability
one on the value `r`. -/
theorem sb_point_mass_opt {r : ℝ} (hr : 0 ≤ r) (q : ℝ) :
    q * (if q ≤ r then 1 else 0) ≤ r * (if r ≤ r then 1 else 0) := by
  split_ifs <;> linarith

/-- `q (k − q)⁺ ≤ k²/4`. -/
theorem sb_rev_bound {k : ℝ} (hk : 0 ≤ k) (q : ℝ) : q * max 0 (k - max q 0) ≤ k ^ 2 / 4 := by
  rcases le_total q 0 with hq | hq
  · rw [max_eq_right hq, sub_zero, max_eq_right hk]
    nlinarith
  · rw [max_eq_left hq]
    rcases le_total (k - q) 0 with h | h
    · rw [max_eq_left h]; nlinarith
    · rw [max_eq_right h]; nlinarith [sq_nonneg (q - k / 2)]

/-- **Exercise 9.C.3(b), the second price** (MWG, p. 304). With the posterior uniform on
`[0, k)`, `k > 0`, the unique optimal second price is `k/2`. -/
theorem sbURev_opt_iff {k : ℝ} (hk : 0 < k) (r : ℝ) :
    (∀ q, sbURev k q ≤ sbURev k r) ↔ r = k / 2 := by
  have hval : sbURev k (k / 2) = k / 4 := by
    unfold sbURev
    rw [max_eq_left (by linarith : (0 : ℝ) ≤ k / 2), max_eq_right (by linarith)]
    field_simp
    ring
  have hle : ∀ q, sbURev k q ≤ k / 4 := fun q => by
    unfold sbURev
    rw [← mul_div_assoc, div_le_iff₀ hk]
    nlinarith [sb_rev_bound hk.le q]
  constructor
  · intro h
    have h1 := h (k / 2)
    rw [hval] at h1
    have h2 : sbURev k r * k = r * max 0 (k - max r 0) := by
      unfold sbURev; field_simp
    have h3 : k ^ 2 / 4 ≤ r * max 0 (k - max r 0) := by nlinarith
    rcases le_total r 0 with hq | hq
    · rw [max_eq_right hq, sub_zero, max_eq_right hk.le] at h3
      nlinarith
    · rw [max_eq_left hq] at h3
      rcases le_total (k - r) 0 with h4 | h4
      · rw [max_eq_left h4] at h3; nlinarith
      · rw [max_eq_right h4] at h3; nlinarith [sq_nonneg (r - k / 2)]
  · rintro rfl q
    rw [hval]
    exact hle q

/-- The second price after `p > 0` in the consistent profile: half the cutoff
`min (2p/(2 − δ), 1)`. -/
noncomputable def sbRStar (δ p : ℝ) : ℝ := if 0 < p then min (2 * p / (2 - δ)) 1 / 2 else 0

/-- The equilibrium first price `p* = (2 − δ)² / (2 (4 − 3δ))`. -/
noncomputable def sbPStar (δ : ℝ) : ℝ := (2 - δ) ^ 2 / (2 * (4 - 3 * δ))

/-- **Exercise 9.C.3(b), the linear cutoff** (MWG, p. 304). If the second price after `p > 0` is
optimal for the Bayes posterior, then the cutoff is `κ = 2p/(2 − δ)` (capped at `1`) and the
second price is `κ/2`. -/
theorem sb_consistent_r (hd0 : 0 < δ) (hd1 : δ < 1) {r : ℝ → ℝ} (hc : IsSBUConsistent δ r)
    {p : ℝ} (hp : 0 < p) :
    r p = sbRStar δ p ∧ sbCut δ p (r p) = min (2 * p / (2 - δ)) 1 := by
  have h1 : 0 < 1 - δ := by linarith
  have h2 : 0 < 2 - δ := by linarith
  set κ := sbKappa δ p (r p) with hκ
  have hκpos : 0 < κ := by
    rw [hκ, sbKappa]
    split_ifs with h
    · rw [lt_div_iff₀ h1]; nlinarith [mul_le_mul_of_nonneg_left h hd0.le]
    · exact hp
  have hk : 0 < sbCut δ p (r p) := by
    unfold sbCut
    rw [← hκ]
    exact lt_max_of_lt_right (lt_min hκpos one_pos)
  have hr2 := (sbURev_opt_iff hk (r p)).1 (hc p hk)
  have hcut : sbCut δ p (r p) = min κ 1 := by
    unfold sbCut; rw [← hκ]; exact max_eq_right (le_min hκpos.le zero_le_one)
  rw [hcut] at hr2 ⊢
  have hRS : sbRStar δ p = min (2 * p / (2 - δ)) 1 / 2 := by simp [sbRStar, hp]
  rw [hRS]
  by_cases hrp : r p ≤ p
  · have hκeq : κ * (1 - δ) = p - δ * r p := by
      rw [hκ, sbKappa]
      simp only [hrp, ↓reduceIte]
      field_simp
    rcases le_total κ 1 with hk1 | hk1
    · rw [min_eq_left hk1] at hr2
      have : κ = 2 * p / (2 - δ) := by
        rw [eq_div_iff h2.ne']
        rw [hr2] at hκeq
        linarith
      rw [← this, min_eq_left hk1]
      exact ⟨hr2, rfl⟩
    · rw [min_eq_right hk1] at hr2
      have : 1 ≤ 2 * p / (2 - δ) := by
        rw [le_div_iff₀ h2]
        rw [hr2] at hκeq
        nlinarith
      rw [min_eq_right this, min_eq_right hk1]
      exact ⟨hr2, rfl⟩
  · exfalso
    have hκp : κ = p := by
      rw [hκ, sbKappa]
      simp only [hrp, ↓reduceIte]
    rw [hκp] at hr2
    have : min p 1 ≤ p := min_le_left _ _
    have : p < r p := not_le.1 hrp
    linarith

/-- At a first price `p ≤ 0` every type buys at once, and the seller earns `p ≤ 0`. -/
theorem sbUPay_nonpos (hd0 : 0 < δ) (hd1 : δ < 1) {p r : ℝ} (hp : p ≤ 0) (hr : 0 ≤ r)
    (q : ℝ) : sbUPay δ p r q ≤ 0 := by
  have hκ : sbKappa δ p r ≤ 0 := by
    unfold sbKappa
    split_ifs
    · exact div_nonpos_of_nonpos_of_nonneg (by nlinarith) (by linarith)
    · exact hp
  have hcut : sbCut δ p r = 0 := by
    unfold sbCut
    exact max_eq_left (le_trans (min_le_left _ _) hκ)
  unfold sbUPay
  rw [hcut]
  rcases le_total q 0 with hq | hq
  · rw [max_eq_right hq, sub_self, max_self, mul_zero, add_zero]; linarith
  · rw [max_eq_left hq, max_eq_left (by linarith : (0 : ℝ) - q ≤ 0)]; linarith

/-- The seller's payoff after `p > 0` when the cutoff is `k` and the second price is `k/2`: at
most `p (1 − k) + δ k²/4`, attained at `q = k/2`. -/
theorem sbUPay_value {p r k : ℝ} (hd0 : 0 < δ) (hk : 0 ≤ k) (hcut : sbCut δ p r = k)
    (q : ℝ) : sbUPay δ p r q ≤ p * (1 - k) + δ * k ^ 2 / 4 ∧
      sbUPay δ p r (k / 2) = p * (1 - k) + δ * k ^ 2 / 4 := by
  unfold sbUPay
  rw [hcut]
  constructor
  · nlinarith [sb_rev_bound hk q]
  · rw [max_eq_left (by linarith : (0 : ℝ) ≤ k / 2), max_eq_right (by linarith)]
    ring

/-- The seller's first-period problem: `p (1 − k) + δ k²/4` with `k = min (2p/(2 − δ), 1)` is at
most `(2 − δ)² / (4 (4 − 3δ))`, with equality only at `p* = (2 − δ)² / (2 (4 − 3δ))`. -/
theorem sbG_le (hd0 : 0 < δ) (hd1 : δ < 1) {p : ℝ} (hp : 0 < p) :
    p * (1 - min (2 * p / (2 - δ)) 1) + δ * (min (2 * p / (2 - δ)) 1) ^ 2 / 4 ≤
      (2 - δ) ^ 2 / (4 * (4 - 3 * δ)) ∧
    (p * (1 - min (2 * p / (2 - δ)) 1) + δ * (min (2 * p / (2 - δ)) 1) ^ 2 / 4 =
      (2 - δ) ^ 2 / (4 * (4 - 3 * δ)) → p = sbPStar δ) := by
  have h2 : 0 < 2 - δ := by linarith
  have h43 : 0 < 4 - 3 * δ := by linarith
  have h43' : 4 - 3 * δ ≠ 0 := h43.ne'
  have h2' : 2 - δ ≠ 0 := h2.ne'
  set k := 2 * p / (2 - δ) with hk
  have hpk : p = (2 - δ) * k / 2 := by rw [hk]; field_simp
  set c := (2 - δ) / (4 - 3 * δ) with hcdef
  have hc : c * (4 - 3 * δ) = 2 - δ := div_mul_cancel₀ _ h43'
  have hg : (2 - δ) ^ 2 / (4 * (4 - 3 * δ)) = c * (2 - δ) / 4 := by
    rw [hcdef]; field_simp
  have key : (2 - δ) ^ 2 / (4 * (4 - 3 * δ)) - (p * (1 - k) + δ * k ^ 2 / 4) =
      (4 - 3 * δ) / 4 * (k - c) ^ 2 := by
    rw [hg, hpk]
    linear_combination (k / 2 - c / 4) * hc
  rcases le_total k 1 with hk1 | hk1
  · rw [min_eq_left hk1]
    refine ⟨by nlinarith [sq_nonneg (k - c)], fun he => ?_⟩
    have hsq : (k - c) ^ 2 = 0 := by
      have : (4 - 3 * δ) / 4 * (k - c) ^ 2 = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h (by positivity)
      · exact h
    have hkk : k = c := sub_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 hsq)
    rw [hpk, hkk, hcdef, sbPStar]
    field_simp
  · rw [min_eq_right hk1]
    have hlt : δ * 1 ^ 2 / 4 < (2 - δ) ^ 2 / (4 * (4 - 3 * δ)) := by
      rw [lt_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (1 - δ), mul_pos hd0 h43]
    refine ⟨by nlinarith, fun he => ?_⟩
    exfalso
    have : p * (1 - 1) = 0 := by ring
    linarith

/-- The cutoff and second price of the consistent profile after `p > 0`. -/
theorem sbRStar_cut (hd0 : 0 < δ) (hd1 : δ < 1) {p : ℝ} (hp : 0 < p) :
    sbCut δ p (sbRStar δ p) = min (2 * p / (2 - δ)) 1 ∧
      sbRStar δ p = min (2 * p / (2 - δ)) 1 / 2 := by
  have h1 : 0 < 1 - δ := by linarith
  have h2 : 0 < 2 - δ := by linarith
  have hRS : sbRStar δ p = min (2 * p / (2 - δ)) 1 / 2 := by simp [sbRStar, hp]
  refine ⟨?_, hRS⟩
  set k := min (2 * p / (2 - δ)) 1 with hk
  have hkpos : 0 < k := lt_min (div_pos (by linarith) h2) one_pos
  have hkp : k / 2 ≤ p := by
    have : k ≤ 2 * p / (2 - δ) := min_le_left _ _
    rw [le_div_iff₀ h2] at this
    nlinarith
  unfold sbCut sbKappa
  rw [hRS]
  simp only [hkp, ↓reduceIte]
  rcases le_total (2 * p / (2 - δ)) 1 with hk1 | hk1
  · have hk' : k = 2 * p / (2 - δ) := min_eq_left hk1
    have : (p - δ * (k / 2)) / (1 - δ) = k := by
      rw [hk', div_eq_iff h1.ne']; field_simp; ring
    rw [this, min_eq_left (min_le_right _ _), max_eq_right hkpos.le]
  · have hk' : k = 1 := min_eq_right hk1
    have : 1 ≤ (p - δ * (k / 2)) / (1 - δ) := by
      rw [hk', le_div_iff₀ h1]
      rw [le_div_iff₀ h2] at hk1
      linarith
    rw [min_eq_right this, max_eq_right zero_le_one, hk']

/-- **Exercise 9.C.3(b)** (MWG, p. 304), values uniform on `[0, 1]`. The profile in which, after
every first price `p > 0`, the types with `v ≥ κ = 2p/(2 − δ)` (capped at `1`) buy at once and
the seller then charges `κ/2`, and the first price is `p* = (2 − δ)²/(2 (4 − 3δ))` (cutoff
`(2 − δ)/(4 − 3δ)`, second price `(2 − δ)/(2 (4 − 3δ))`), is a weak PBE with consistent beliefs;
and it is the only weak PBE whose beliefs are consistent after every rejected price
(the sequential-equilibrium reading of Exercise 9.C.6). -/
theorem exercise_9_C_3b (hd0 : 0 < δ) (hd1 : δ < 1) :
    IsSBUWeakPBE δ (sbPStar δ) (sbRStar δ) ∧ IsSBUConsistent δ (sbRStar δ) ∧
    sbCut δ (sbPStar δ) (sbRStar δ (sbPStar δ)) = (2 - δ) / (4 - 3 * δ) ∧
    sbRStar δ (sbPStar δ) = (2 - δ) / (2 * (4 - 3 * δ)) ∧
    ∀ p1 r, IsSBUWeakPBE δ p1 r → IsSBUConsistent δ r →
      p1 = sbPStar δ ∧ ∀ p, 0 < p → r p = sbRStar δ p := by
  have h2 : 0 < 2 - δ := by linarith
  have h43 : 0 < 4 - 3 * δ := by linarith
  have h43' : 4 - 3 * δ ≠ 0 := h43.ne'
  have h2' : 2 - δ ≠ 0 := h2.ne'
  have hps : 0 < sbPStar δ := by unfold sbPStar; positivity
  have hks : 2 * sbPStar δ / (2 - δ) = (2 - δ) / (4 - 3 * δ) := by
    unfold sbPStar; field_simp
  have hks1 : (2 - δ) / (4 - 3 * δ) ≤ 1 := by rw [div_le_one h43]; linarith
  obtain ⟨hc1, hc2⟩ := sbRStar_cut hd0 hd1 hps
  rw [hks, min_eq_left hks1] at hc1 hc2
  -- the value of the consistent profile
  have hval : ∀ p, 0 < p → ∀ q, sbUPay δ p (sbRStar δ p) q ≤
      (2 - δ) ^ 2 / (4 * (4 - 3 * δ)) := fun p hp q => by
    obtain ⟨c1, -⟩ := sbRStar_cut hd0 hd1 hp
    have := (sbUPay_value hd0 (le_min (div_pos (by linarith) h2).le zero_le_one) c1 q).1
    linarith [(sbG_le hd0 hd1 hp).1]
  have hstar : sbUPay δ (sbPStar δ) (sbRStar δ (sbPStar δ)) (sbRStar δ (sbPStar δ)) =
      (2 - δ) ^ 2 / (4 * (4 - 3 * δ)) := by
    have := (sbUPay_value hd0 (by positivity) hc1 0).2
    rw [hc2] at this ⊢
    rw [this]
    set c := (2 - δ) / (4 - 3 * δ) with hcdef
    have hc : c * (4 - 3 * δ) = 2 - δ := div_mul_cancel₀ _ h43'
    have hpc : sbPStar δ = (2 - δ) * c / 2 := by unfold sbPStar; rw [hcdef]; field_simp
    have hg : (2 - δ) ^ 2 / (4 * (4 - 3 * δ)) = c * (2 - δ) / 4 := by rw [hcdef]; field_simp
    rw [hpc, hg]
    linear_combination (-c / 4) * hc
  have hRnn : ∀ p, 0 ≤ sbRStar δ p ∧ sbRStar δ p ≤ 1 := fun p => by
    unfold sbRStar
    split_ifs with hp
    · constructor
      · exact div_nonneg (le_min (div_pos (by linarith) h2).le zero_le_one) zero_le_two
      · linarith [min_le_right (2 * p / (2 - δ)) 1]
    · exact ⟨le_rfl, zero_le_one⟩
  have hcons : IsSBUConsistent δ (sbRStar δ) := by
    intro p hpos q
    by_cases hp : 0 < p
    · obtain ⟨c1, c2⟩ := sbRStar_cut hd0 hd1 hp
      rw [c1] at hpos ⊢
      exact (sbURev_opt_iff hpos _).2 c2 q
    · exfalso
      have hκ : sbKappa δ p (sbRStar δ p) ≤ 0 := by
        have hr0 : sbRStar δ p = 0 := by simp [sbRStar, hp]
        rw [hr0, sbKappa]
        split_ifs
        · rw [mul_zero, sub_zero]
          exact div_nonpos_of_nonpos_of_nonneg (not_lt.1 hp) (by linarith)
        · exact not_lt.1 hp
      have : sbCut δ p (sbRStar δ p) = 0 := max_eq_left (le_trans (min_le_left _ _) hκ)
      linarith
  refine ⟨⟨hRnn, fun h => hcons _ h, fun p q => ?_⟩, hcons, hc1,
    by rw [hc2, div_div, mul_comm (4 - 3 * δ)], fun p1 r hW hC => ?_⟩
  · rw [hstar]
    by_cases hp : 0 < p
    · exact hval p hp q
    · exact le_trans (sbUPay_nonpos hd0 hd1 (not_lt.1 hp) (hRnn p).1 q) (by positivity)
  · obtain ⟨hr01, -, hroot⟩ := hW
    have hrs : ∀ p, 0 < p → r p = sbRStar δ p := fun p hp => (sb_consistent_r hd0 hd1 hC hp).1
    have hdev := hroot (sbPStar δ) (sbRStar δ (sbPStar δ))
    rw [hrs _ hps, hstar] at hdev
    have hp1 : 0 < p1 := by
      by_contra hn
      have := sbUPay_nonpos hd0 hd1 (not_lt.1 hn) (hr01 p1).1 (r p1)
      have : 0 < (2 - δ) ^ 2 / (4 * (4 - 3 * δ)) := by positivity
      linarith
    refine ⟨?_, hrs⟩
    obtain ⟨c1, c2⟩ := sb_consistent_r hd0 hd1 hC hp1
    obtain ⟨-, c3⟩ := sbRStar_cut hd0 hd1 hp1
    have hv := (sbUPay_value hd0 (le_min (div_pos (by linarith) h2).le zero_le_one) c2
      (r p1)).2
    rw [c1, c3] at hv
    rw [c1, c3, hv] at hdev
    exact (sbG_le hd0 hd1 hp1).2 (le_antisymm (sbG_le hd0 hd1 hp1).1 hdev)

/-- **Exercise 9.C.3(b): weak PBE are not unique** (MWG, p. 304). With `δ = 1/2` the
consistent price is `p* = 9/20`, but `p1 = 3/10` is also a weak PBE first price: after
`3/10` the cutoff is `2/5` and the seller charges `1/5`, earning `1/5`; after any other price
the seller (at an information set reached with probability zero, where any belief is allowed)
charges `0`, so the buyers' cutoff is `2p` and no deviation earns more than `1/6`. -/
theorem exercise_9_C_3b_not_unique :
    IsSBUWeakPBE (1 / 2) (3 / 10) (fun p => if p = 3 / 10 then 1 / 5 else 0) ∧
      (3 / 10 : ℝ) ≠ sbPStar (1 / 2) := by
  set r : ℝ → ℝ := fun p => if p = 3 / 10 then 1 / 5 else 0 with hr
  have hcut1 : sbCut (1 / 2) (3 / 10) (r (3 / 10)) = 2 / 5 := by
    simp only [hr, ↓reduceIte, sbCut, sbKappa]
    norm_num
  have hpay1 : sbUPay (1 / 2) (3 / 10) (r (3 / 10)) (r (3 / 10)) = 1 / 5 := by
    unfold sbUPay
    rw [hcut1]
    simp only [hr, ↓reduceIte]
    norm_num
  refine ⟨⟨fun p => ?_, fun _ q => ?_, fun p q => ?_⟩, by unfold sbPStar; norm_num⟩
  · simp only [hr]; split_ifs <;> norm_num
  · rw [hcut1]
    have : r (3 / 10) = 2 / 5 / 2 := by simp only [hr, ↓reduceIte]; norm_num
    rw [this]
    exact (sbURev_opt_iff (by norm_num) _).2 rfl q
  · rw [hpay1]
    by_cases hp : p = 3 / 10
    · subst hp
      unfold sbUPay
      rw [hcut1]
      nlinarith [sb_rev_bound (k := 2 / 5) (by norm_num) q]
    · have hr0 : r p = 0 := by simp [hr, hp]
      rw [hr0]
      by_cases hp0 : 0 < p
      · have hκ : sbKappa (1 / 2) p 0 = 2 * p := by
          simp only [sbKappa, hp0.le, ↓reduceIte]; ring
        unfold sbUPay sbCut
        rw [hκ]
        rcases le_total (2 * p) 1 with h1 | h1
        · rw [min_eq_left h1, max_eq_right (by linarith)]
          nlinarith [sb_rev_bound (k := 2 * p) (by linarith) q, sq_nonneg (p - 1 / 3)]
        · rw [min_eq_right h1, max_eq_right zero_le_one]
          nlinarith [sb_rev_bound (k := 1) zero_le_one q]
      · exact le_trans (sbUPay_nonpos (by norm_num) (by norm_num) (not_lt.1 hp0) le_rfl q)
          (by norm_num)

end MWG.DynamicGames
