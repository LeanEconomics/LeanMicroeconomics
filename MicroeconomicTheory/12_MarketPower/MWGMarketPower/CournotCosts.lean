/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGMarketPower.CournotExistence
import MWGMarketPower.CournotBestResponse
import MWGSimultaneousMoveGames.Cournot
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Cournot competition with different costs

MWG, Exercises 12.C.9(a)-(b), 12.C.10, 12.C.19 and 12.C.20, pp. 431-433.

* `exercise_12_C_9a`: the linear duopoly `p(q) = a − bq` with unit costs `c₁ > c₂`, `a > c₁`:
  if `a + c₂ > 2c₁` the unique Nash equilibrium is `qⱼ = (a − 2cⱼ + cₖ)/(3b)`; if
  `a + c₂ ≤ 2c₁` it is `q₁ = 0`, `q₂ = (a − c₂)/(2b)`: only the low-cost firm 2 produces.
* `exercise_12_C_9b`: in the interior case, `dq₁/dc₁ = −2/(3b) < 0`, `dq₂/dc₁ = 1/(3b) > 0`; the
  profits are `πⱼ = bqⱼ²`, with `dπ₁/dc₁ < 0 < dπ₂/dc₁`.
* `exercise_12_C_10a`: `J` firms with costs `αⱼc̃(q)`, `c̃` strictly increasing, convex and
  differentiable, the `αⱼ` distinct: if two firms produce positive output in a Nash equilibrium,
  moving output between them lowers total cost, so `Q*` is not produced efficiently.
* `exercise_12_C_10b`: the correct measure of welfare loss is `S(Q°) − W(q*)`, where
  `S(Q) = ∫₀^Q p − C(Q)` uses the efficient (minimum) cost `C(Q)` of producing `Q` and `Q°`
  maximizes `S`; it splits into the loss from the output level, `S(Q°) − S(Q*)`, and the
  production inefficiency `∑ⱼ cⱼ(qⱼ*) − C(Q*)`, both nonnegative; the second is positive when
  two firms produce (`exercise_12_C_10b_strict`).
* `exercise_12_C_10c`: in the model of Exercise 12.C.9 (`c̃(q) = q`, `αⱼ = cⱼ`), welfare at the
  Cournot equilibrium has derivative `(11c₁ − 4a − 7c₂)/(9b)` in `c₁`; with `a = 10`, `b = 1`,
  `c₂ = 1`, lowering `c₁` from `5` to `9/2` lowers welfare from `268/9` to `2123/72`.
* `exercise_12_C_19a`, `exercise_12_C_19b`: Exercise 8.B.5, proved in Chapter 8.
* `exercise_12_C_20`: Proposition 12.C.2 with a convex differentiable cost `c(q)`: in a Cournot
  duopoly equilibrium the price exceeds each firm's marginal cost and is below the monopoly
  price.

Departures: costs and inverse demand are differentiable on all of `ℝ` (as in
`MWGMarketPower.CournotBestResponse`); in 12.C.10(b) costs are nonnegative on `[0, ∞)`.
-/

namespace MWG.MarketPower

open Set Function Filter Topology

/-! ### Exercise 12.C.9 -/

/-- The cost functions `cⱼq` of the two firms of Exercise 12.C.9. -/
noncomputable def ccLinCost (c₁ c₂ : ℝ) : Fin 2 → ℝ → ℝ := ![fun z => c₁ * z, fun z => c₂ * z]

theorem ccLin_profit0 (a b c₁ c₂ : ℝ) (q : Fin 2 → ℝ) (y : ℝ) :
    cournotGenProfit (fun z => a - b * z) (ccLinCost c₁ c₂) (update q 0 y) 0 =
      (a - b * (y + q 1)) * y - c₁ * y := by
  simp [cournotGenProfit, ccLinCost, Fin.sum_univ_two]

theorem ccLin_profit1 (a b c₁ c₂ : ℝ) (q : Fin 2 → ℝ) (y : ℝ) :
    cournotGenProfit (fun z => a - b * z) (ccLinCost c₁ c₂) (update q 1 y) 1 =
      (a - b * (y + q 0)) * y - c₂ * y := by
  simp [cournotGenProfit, ccLinCost, Fin.sum_univ_two, add_comm]

/-- A best response in the linear model, in Kuhn-Tucker form: `q ≥ 0`, `A − br ≤ 2bq`, with
equality if `q > 0` (where `A = a − c`, `r` the rival's output). -/
theorem cc_br_kkt {A b r : ℝ} (hb : 0 < b) :
    0 ≤ max 0 ((A - b * r) / (2 * b)) ∧ A - b * r ≤ 2 * b * max 0 ((A - b * r) / (2 * b)) ∧
      (0 < max 0 ((A - b * r) / (2 * b)) → 2 * b * max 0 ((A - b * r) / (2 * b)) = A - b * r) := by
  rcases le_total ((A - b * r) / (2 * b)) 0 with h | h
  · rw [max_eq_left h]
    refine ⟨le_rfl, ?_, fun h' => absurd h' (lt_irrefl 0)⟩
    rw [div_nonpos_iff] at h
    rcases h with ⟨-, h2⟩ | ⟨h1, -⟩
    · linarith
    · linarith
  · rw [max_eq_right h]
    refine ⟨h, ?_, fun _ => ?_⟩
    · field_simp; exact le_rfl
    · field_simp

/-- The Nash equilibria of the linear duopoly with costs `c₁, c₂` are the mutual best responses
`qⱼ = max{0, (a − cⱼ − bqₖ)/(2b)}`. -/
theorem ccLin_ne_iff {a b c₁ c₂ : ℝ} (hb : 0 < b) (q : Fin 2 → ℝ) :
    IsCournotGenNE (fun z => a - b * z) (ccLinCost c₁ c₂) q ↔
      0 ≤ q 1 ∧ 0 ≤ q 0 ∧ q 0 = max 0 ((a - c₁ - b * q 1) / (2 * b)) ∧
        q 1 = max 0 ((a - c₂ - b * q 0) / (2 * b)) := by
  constructor
  · rintro ⟨hnn, hbr⟩
    refine ⟨hnn 1, hnn 0, ?_, ?_⟩
    · obtain ⟨-, huniq⟩ := example_12_C_1_br (a := a) (c := c₁) hb (hnn 1)
      by_contra hne
      have h1 := huniq (q 0) (hnn 0) hne
      have h2 := hbr 0 (max 0 ((a - c₁ - b * q 1) / (2 * b))) (le_max_left _ _)
      rw [ccLin_profit0] at h2
      have h3 : cournotGenProfit (fun z => a - b * z) (ccLinCost c₁ c₂) q 0 =
          (a - b * (q 0 + q 1)) * q 0 - c₁ * q 0 := by
        rw [← ccLin_profit0 a b c₁ c₂ q (q 0), update_eq_self]
      rw [h3] at h2
      linarith
    · obtain ⟨-, huniq⟩ := example_12_C_1_br (a := a) (c := c₂) hb (hnn 0)
      by_contra hne
      have h1 := huniq (q 1) (hnn 1) hne
      have h2 := hbr 1 (max 0 ((a - c₂ - b * q 0) / (2 * b))) (le_max_left _ _)
      rw [ccLin_profit1] at h2
      have h3 : cournotGenProfit (fun z => a - b * z) (ccLinCost c₁ c₂) q 1 =
          (a - b * (q 1 + q 0)) * q 1 - c₂ * q 1 := by
        rw [← ccLin_profit1 a b c₁ c₂ q (q 1), update_eq_self]
      rw [h3] at h2
      linarith
  · rintro ⟨h1, h0, e0, e1⟩
    refine ⟨fun j => by fin_cases j <;> assumption, fun j y hy => ?_⟩
    fin_cases j
    · simp only [Fin.zero_eta]
      rw [ccLin_profit0]
      have h3 : cournotGenProfit (fun z => a - b * z) (ccLinCost c₁ c₂) q 0 =
          (a - b * (q 0 + q 1)) * q 0 - c₁ * q 0 := by
        rw [← ccLin_profit0 a b c₁ c₂ q (q 0), update_eq_self]
      rw [h3]
      obtain ⟨-, huniq⟩ := example_12_C_1_br (a := a) (c := c₁) hb h1
      by_cases hy' : y = q 0
      · rw [hy']
      · rw [e0] at hy' ⊢
        exact (huniq y hy hy').le
    · simp only [Fin.mk_one]
      rw [ccLin_profit1]
      have h3 : cournotGenProfit (fun z => a - b * z) (ccLinCost c₁ c₂) q 1 =
          (a - b * (q 1 + q 0)) * q 1 - c₂ * q 1 := by
        rw [← ccLin_profit1 a b c₁ c₂ q (q 1), update_eq_self]
      rw [h3]
      obtain ⟨-, huniq⟩ := example_12_C_1_br (a := a) (c := c₂) hb h0
      by_cases hy' : y = q 1
      · rw [hy']
      · rw [e1] at hy' ⊢
        exact (huniq y hy hy').le

/-- **Exercise 12.C.9(a)** (MWG, p. 431). The linear Cournot duopoly with `p(q) = a − bq`,
`b > 0`, and unit costs `c₁ > c₂` with `a > c₁`. If `a + c₂ > 2c₁` the unique Nash equilibrium is
`q₁ = (a − 2c₁ + c₂)/(3b)`, `q₂ = (a − 2c₂ + c₁)/(3b)` (both positive); if `a + c₂ ≤ 2c₁` the
unique Nash equilibrium is `q₁ = 0`, `q₂ = (a − c₂)/(2b)`: only the low-cost firm 2 produces,
at its monopoly output. -/
theorem exercise_12_C_9a {a b c₁ c₂ : ℝ} (hb : 0 < b) (h21 : c₂ < c₁) (hca : c₁ < a) :
    (2 * c₁ < a + c₂ → ∀ q, IsCournotGenNE (fun z => a - b * z) (ccLinCost c₁ c₂) q ↔
      q = ![(a - 2 * c₁ + c₂) / (3 * b), (a - 2 * c₂ + c₁) / (3 * b)]) ∧
    (a + c₂ ≤ 2 * c₁ → ∀ q, IsCournotGenNE (fun z => a - b * z) (ccLinCost c₁ c₂) q ↔
      q = ![0, (a - c₂) / (2 * b)]) := by
  -- the mutual best responses, in Kuhn-Tucker form
  have hsolve : ∀ q : Fin 2 → ℝ, IsCournotGenNE (fun z => a - b * z) (ccLinCost c₁ c₂) q →
      0 ≤ q 0 ∧ 0 ≤ q 1 ∧ a - c₁ - b * q 1 ≤ 2 * b * q 0 ∧
        (0 < q 0 → 2 * b * q 0 = a - c₁ - b * q 1) ∧ a - c₂ - b * q 0 ≤ 2 * b * q 1 ∧
        (0 < q 1 → 2 * b * q 1 = a - c₂ - b * q 0) := by
    intro q hq
    obtain ⟨h1, h0, e0, e1⟩ := (ccLin_ne_iff hb q).1 hq
    obtain ⟨-, k0, k0'⟩ := cc_br_kkt (A := a - c₁) (r := q 1) hb
    obtain ⟨-, k1, k1'⟩ := cc_br_kkt (A := a - c₂) (r := q 0) hb
    rw [← e0] at k0 k0'
    rw [← e1] at k1 k1'
    exact ⟨h0, h1, k0, k0', k1, k1'⟩
  -- firm 2 always produces
  have hq1pos : ∀ q : Fin 2 → ℝ, IsCournotGenNE (fun z => a - b * z) (ccLinCost c₁ c₂) q →
      0 < q 1 := by
    intro q hq
    obtain ⟨h0, h1, k0, k0', k1, -⟩ := hsolve q hq
    by_contra h
    have hz : q 1 = 0 := le_antisymm (not_lt.1 h) h1
    rw [hz] at k0 k1
    have hq0 : 0 < q 0 := by nlinarith
    have := k0' hq0
    rw [hz] at this
    nlinarith
  constructor
  · intro hint q
    constructor
    · intro hq
      obtain ⟨h0, h1, k0, k0', k1, k1'⟩ := hsolve q hq
      have hp1 := hq1pos q hq
      have e1 := k1' hp1
      have hp0 : 0 < q 0 := by
        by_contra h
        have hz : q 0 = 0 := le_antisymm (not_lt.1 h) h0
        rw [hz] at e1 k0
        nlinarith
      have e0 := k0' hp0
      funext j
      fin_cases j
      · simp only [Fin.zero_eta, Matrix.cons_val_zero]
        field_simp; nlinarith
      · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
        field_simp; nlinarith
    · rintro rfl
      rw [ccLin_ne_iff hb]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      have hq0 : 0 < (a - 2 * c₁ + c₂) / (3 * b) := div_pos (by linarith) (by positivity)
      have hq1 : 0 < (a - 2 * c₂ + c₁) / (3 * b) := div_pos (by linarith) (by positivity)
      refine ⟨hq1.le, hq0.le, ?_, ?_⟩
      · rw [max_eq_right (by field_simp; linarith)]; field_simp; ring
      · rw [max_eq_right (by field_simp; linarith)]; field_simp; ring
  · intro hcorner q
    constructor
    · intro hq
      obtain ⟨h0, h1, k0, k0', k1, k1'⟩ := hsolve q hq
      have hp1 := hq1pos q hq
      have e1 := k1' hp1
      have hz : q 0 = 0 := by
        by_contra h
        have hp0 : 0 < q 0 := lt_of_le_of_ne h0 (Ne.symm h)
        have e0 := k0' hp0
        nlinarith
      funext j
      fin_cases j
      · simpa using hz
      · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
        rw [hz] at e1
        field_simp; linarith
    · rintro rfl
      rw [ccLin_ne_iff hb]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      have hq1 : 0 < (a - c₂) / (2 * b) := div_pos (by linarith) (by positivity)
      refine ⟨hq1.le, le_rfl, ?_, ?_⟩
      · rw [max_eq_left]
        rw [div_nonpos_iff]
        right
        refine ⟨?_, by positivity⟩
        field_simp
        linarith
      · rw [max_eq_right (by simpa using hq1.le)]
        field_simp
        ring

/-- **Exercise 12.C.9(b)** (MWG, p. 431). In the equilibrium with both firms producing
(`a − 2c₁ + c₂ > 0`, `a − 2c₂ + c₁ > 0`), firm `j`'s profit is `bqⱼ²`; as `c₁` rises, firm 1's
output `(a − 2c₁ + c₂)/(3b)` and profit `(a − 2c₁ + c₂)²/(9b)` fall (derivatives `−2/(3b)` and
`−4(a − 2c₁ + c₂)/(9b)`), while firm 2's output `(a − 2c₂ + c₁)/(3b)` and profit
`(a − 2c₂ + c₁)²/(9b)` rise (derivatives `1/(3b)` and `2(a − 2c₂ + c₁)/(9b)`). -/
theorem exercise_12_C_9b {a b c₂ : ℝ} (hb : 0 < b) (c₁ : ℝ) (h1 : 0 < a - 2 * c₁ + c₂)
    (h2 : 0 < a - 2 * c₂ + c₁) :
    (a - b * ((a - 2 * c₁ + c₂) / (3 * b) + (a - 2 * c₂ + c₁) / (3 * b)) - c₁) *
        ((a - 2 * c₁ + c₂) / (3 * b)) = (a - 2 * c₁ + c₂) ^ 2 / (9 * b) ∧
    (a - b * ((a - 2 * c₁ + c₂) / (3 * b) + (a - 2 * c₂ + c₁) / (3 * b)) - c₂) *
        ((a - 2 * c₂ + c₁) / (3 * b)) = (a - 2 * c₂ + c₁) ^ 2 / (9 * b) ∧
    HasDerivAt (fun c => (a - 2 * c + c₂) / (3 * b)) (-2 / (3 * b)) c₁ ∧ -2 / (3 * b) < 0 ∧
    HasDerivAt (fun c => (a - 2 * c₂ + c) / (3 * b)) (1 / (3 * b)) c₁ ∧ 0 < 1 / (3 * b) ∧
    HasDerivAt (fun c => (a - 2 * c + c₂) ^ 2 / (9 * b))
      (-4 * (a - 2 * c₁ + c₂) / (9 * b)) c₁ ∧ -4 * (a - 2 * c₁ + c₂) / (9 * b) < 0 ∧
    HasDerivAt (fun c => (a - 2 * c₂ + c) ^ 2 / (9 * b))
      (2 * (a - 2 * c₂ + c₁) / (9 * b)) c₁ ∧ 0 < 2 * (a - 2 * c₂ + c₁) / (9 * b) := by
  have hl1 : HasDerivAt (fun c => a - 2 * c + c₂) (-2) c₁ := by
    have := (((hasDerivAt_id c₁).const_mul 2).const_sub a).add_const c₂
    simpa using this
  have hl2 : HasDerivAt (fun c => a - 2 * c₂ + c) 1 c₁ := by
    simpa using (hasDerivAt_id c₁).const_add (a - 2 * c₂)
  refine ⟨by field_simp; ring, by field_simp; ring, ?_, ?_, ?_, by positivity, ?_, ?_, ?_, ?_⟩
  · simpa using hl1.div_const (3 * b)
  · exact div_neg_of_neg_of_pos (by norm_num) (by positivity)
  · simpa using hl2.div_const (3 * b)
  · convert (hl1.pow 2).div_const (9 * b) using 1; ring
  · exact div_neg_of_neg_of_pos (by nlinarith) (by positivity)
  · convert (hl2.pow 2).div_const (9 * b) using 1; ring
  · positivity

/-! ### Exercise 12.C.19 -/

/-- **Exercise 12.C.19(a)** (MWG, p. 433): Exercise 8.B.5(a), proved in Chapter 8 as
`MWG.SimultaneousMoveGames.exercise_8_B_5a`. With two firms, iterated deletion of strictly
dominated strategies in the linear Cournot model leaves exactly `(a − c)/(3b)` in the limit. -/
theorem exercise_12_C_19a {a b c : ℝ} (hb : 0 < b) (hA : 0 < a - c) :
    (∀ i, ⋂ n, MWG.SimultaneousMoveGames.sdIter
        (MWG.SimultaneousMoveGames.cournot (Fin 2) a b c) n i =
      {MWG.SimultaneousMoveGames.cournotStar a b c hb hA}) ∧
    ∀ n i, (MWG.SimultaneousMoveGames.sdIter
      (MWG.SimultaneousMoveGames.cournot (Fin 2) a b c) n i).Nontrivial :=
  MWG.SimultaneousMoveGames.exercise_8_B_5a hb hA

/-- **Exercise 12.C.19(b)** (MWG, p. 433): Exercise 8.B.5(b), proved in Chapter 8 as
`MWG.SimultaneousMoveGames.exercise_8_B_5b`. With three firms the deletion process stops after
one round at the interval `[0, (a − c)/(2b)]`. -/
theorem exercise_12_C_19b {a b c : ℝ} (hb : 0 < b) (hA : 0 < a - c) :
    (∀ n i, MWG.SimultaneousMoveGames.sdIter
        (MWG.SimultaneousMoveGames.cournot (Fin 3) a b c) (n + 1) i =
      MWG.SimultaneousMoveGames.qIval 0 ((a - c) / (2 * b))) ∧
    MWG.SimultaneousMoveGames.SDTerminal (MWG.SimultaneousMoveGames.cournot (Fin 3) a b c)
      (fun _ => MWG.SimultaneousMoveGames.qIval 0 ((a - c) / (2 * b))) ∧
    ∀ i, (⋂ n, MWG.SimultaneousMoveGames.sdIter
      (MWG.SimultaneousMoveGames.cournot (Fin 3) a b c) n i).Nontrivial :=
  MWG.SimultaneousMoveGames.exercise_8_B_5b hb hA

/-! ### Exercise 12.C.10 -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Moving output between two firms changes a separable sum only in two terms. -/
theorem cc_sum_update_two (F : ι → ℝ → ℝ) (q : ι → ℝ) {h l : ι} (hhl : h ≠ l) (a b : ℝ) :
    ∑ k, F k (update (update q h a) l b k) =
      ∑ k, F k (q k) - F h (q h) - F l (q l) + F h a + F l b := by
  have hl : l ∈ Finset.univ.erase h := Finset.mem_erase.2 ⟨hhl.symm, Finset.mem_univ l⟩
  have e1 := Finset.add_sum_erase Finset.univ (fun k => F k (update (update q h a) l b k))
    (Finset.mem_univ h)
  have e2 := Finset.add_sum_erase (Finset.univ.erase h)
    (fun k => F k (update (update q h a) l b k)) hl
  have e3 := Finset.add_sum_erase Finset.univ (fun k => F k (q k)) (Finset.mem_univ h)
  have e4 := Finset.add_sum_erase (Finset.univ.erase h) (fun k => F k (q k)) hl
  have e5 : ∑ k ∈ (Finset.univ.erase h).erase l, F k (update (update q h a) l b k) =
      ∑ k ∈ (Finset.univ.erase h).erase l, F k (q k) :=
    Finset.sum_congr rfl fun k hk => by
      obtain ⟨hkl, hk'⟩ := Finset.mem_erase.1 hk
      obtain ⟨hkh, -⟩ := Finset.mem_erase.1 hk'
      rw [update_of_ne hkl, update_of_ne hkh]
  simp only [update_self, update_of_ne hhl] at e1 e2
  linarith

/-- The first-order condition of a producing firm in a Cournot equilibrium with cost functions
`Cₖ`: `P'(Q)qₖ + P(Q) = Cₖ'(qₖ)`. -/
theorem cc_foc {P P' : ℝ → ℝ} {C C' : ι → ℝ → ℝ} (hP : ∀ Q, HasDerivAt P (P' Q) Q)
    (hC : ∀ k y, HasDerivAt (C k) (C' k y) y) {q : ι → ℝ} (hq : IsCournotGenNE P C q) {k : ι}
    (hk : 0 < q k) : P' (∑ j, q j) * q k + P (∑ j, q j) = C' k (q k) := by
  set R := ∑ j, q j - q k with hR
  have hQ : q k + R = ∑ j, q j := by rw [hR]; ring
  set f : ℝ → ℝ := fun y => P (y + R) * y - C k y with hf
  have hfeq : ∀ y, cournotGenProfit P C (update q k y) k = f y := by
    intro y
    simp only [cournotGenProfit, update_self, sum_update_eq, hf]
    rfl
  have hd : HasDerivAt f (P' (q k + R) * 1 * q k + P (q k + R) * 1 - C' k (q k)) (q k) := by
    have h1 : HasDerivAt (fun y => y + R) 1 (q k) := (hasDerivAt_id _).add_const R
    have h2 := (hP (q k + R)).comp (q k) h1
    exact (h2.mul (hasDerivAt_id _)).sub (hC k (q k))
  have hmax : IsLocalMax f (q k) := by
    filter_upwards [Ioi_mem_nhds hk] with y hy
    rw [← hfeq, ← hfeq, update_eq_self]
    exact hq.2 k y (le_of_lt hy)
  have := hmax.hasDerivAt_eq_zero hd
  rw [hQ] at this
  linarith

omit [DecidableEq ι] in
/-- If two producing firms' marginal costs differ, moving a little output from the firm with
the higher marginal cost to the other lowers total cost. -/
theorem cc_move {ct ct' : ℝ → ℝ} {α : ι → ℝ} (hct : ∀ y, HasDerivAt ct (ct' y) y)
    {q : ι → ℝ} (hq : ∀ k, 0 ≤ q k) {h l : ι} (hhl : h ≠ l) (hh : 0 < q h)
    (hmc : α l * ct' (q l) < α h * ct' (q h)) :
    ∃ q' : ι → ℝ, (∀ k, 0 ≤ q' k) ∧ ∑ k, q' k = ∑ k, q k ∧
      ∑ k, α k * ct (q' k) < ∑ k, α k * ct (q k) := by
  classical
  set φ : ℝ → ℝ := fun t => α l * ct (q l + t) + α h * ct (q h - t) with hφ
  have hd : HasDerivAt φ (α l * ct' (q l) - α h * ct' (q h)) 0 := by
    have h1 : HasDerivAt (fun t => ct (q l + t)) (ct' (q l)) 0 := by
      have := (hct (q l + 0)).comp_const_add (q l) 0
      rwa [add_zero] at this
    have h2 : HasDerivAt (fun t => ct (q h - t)) (-ct' (q h)) 0 := by
      have := (hct (q h - 0)).comp_const_sub (q h) 0
      rwa [sub_zero] at this
    have := (h1.const_mul (α l)).add (h2.const_mul (α h))
    convert this using 1
    ring
  have hT := hd.tendsto_slope_zero_right
  have hneg : ∀ᶠ t in 𝓝[>] (0 : ℝ), t⁻¹ • (φ (0 + t) - φ 0) < 0 :=
    (tendsto_order.1 hT).2 0 (by linarith)
  have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioo 0 (q h) := Ioo_mem_nhdsGT hh
  obtain ⟨t, ht1, ht2, ht3⟩ := (hneg.and hsmall).exists
  have hφt : φ t < φ 0 := by
    rw [smul_eq_mul, zero_add] at ht1
    by_contra hge
    push Not at hge
    have := mul_nonneg (inv_pos.2 ht2).le (sub_nonneg.2 hge)
    linarith
  refine ⟨update (update q h (q h - t)) l (q l + t), fun k => ?_, ?_, ?_⟩
  · by_cases hkl : k = l
    · subst hkl; simp only [update_self]; linarith [hq k]
    · rw [update_of_ne hkl]
      by_cases hkh : k = h
      · subst hkh; simp only [update_self]; linarith
      · rw [update_of_ne hkh]; exact hq k
  · rw [cc_sum_update_two (fun _ y => y) q hhl]
    ring
  · rw [cc_sum_update_two (fun k y => α k * ct y) q hhl]
    simp only [hφ, add_zero, sub_zero] at hφt
    linarith

/-- **Exercise 12.C.10(a)** (MWG, pp. 431-432). `J`-firm Cournot model with costs
`cⱼ(q) = αⱼc̃(q)`, `c̃` strictly increasing and convex on `[0, ∞)` (and differentiable), the
`αⱼ` distinct (`α₁ > ⋯ > α_J`), inverse demand differentiable with `P' < 0`. If two firms make
positive sales in a Nash equilibrium, the aggregate output `Q*` is produced inefficiently: some
reallocation of `Q*` among the firms has strictly lower total cost. -/
theorem exercise_12_C_10a {P P' ct ct' : ℝ → ℝ} {α : ι → ℝ} (hα : Injective α)
    (hP : ∀ Q, HasDerivAt P (P' Q) Q) (hP' : ∀ Q, 0 ≤ Q → P' Q < 0)
    (hct : ∀ y, HasDerivAt ct (ct' y) y) (hmono : StrictMonoOn ct (Ici 0))
    (hconv : ConvexOn ℝ (Ici 0) ct) {q : ι → ℝ}
    (hq : IsCournotGenNE P (fun k y => α k * ct y) q) {i j : ι} (hij : i ≠ j) (hi : 0 < q i)
    (hj : 0 < q j) :
    ∃ q' : ι → ℝ, (∀ k, 0 ≤ q' k) ∧ ∑ k, q' k = ∑ k, q k ∧
      ∑ k, α k * ct (q' k) < ∑ k, α k * ct (q k) := by
  -- marginal cost is positive at positive output
  have hct'pos : ∀ y, 0 < y → 0 < ct' y := by
    intro y hy
    have h1 := hconv.slope_le_deriv (x := 0) (y := y) (mem_Ici.2 le_rfl) (mem_Ici.2 hy.le) hy
      (hct y).differentiableAt
    rw [(hct y).deriv] at h1
    have h2 : 0 < slope ct 0 y := by
      rw [slope_def_field]
      exact div_pos (sub_pos.2 (hmono (mem_Ici.2 le_rfl) (mem_Ici.2 hy.le) hy)) (by linarith)
    linarith
  have hC : ∀ k y, HasDerivAt ((fun k y => α k * ct y) k) (α k * ct' y) y :=
    fun k y => (hct y).const_mul (α k)
  have hfi := cc_foc (C' := fun k y => α k * ct' y) hP hC hq hi
  have hfj := cc_foc (C' := fun k y => α k * ct' y) hP hC hq hj
  have hQ : 0 ≤ ∑ k, q k := Finset.sum_nonneg fun k _ => hq.1 k
  have hne : α i * ct' (q i) ≠ α j * ct' (q j) := by
    intro heq
    have hqq : q i = q j := by
      have : P' (∑ k, q k) * (q i - q j) = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h (hP' _ hQ).ne
      · linarith
    rw [hqq] at heq
    exact hij (hα (mul_right_cancel₀ (hct'pos _ hj).ne' heq))
  rcases lt_or_gt_of_ne hne with h | h
  · exact cc_move hct hq.1 hij.symm hj h
  · exact cc_move hct hq.1 hij hi h

/-- The minimum total cost of producing `Q ≥ 0` with the firms' cost functions `Cₖ`: the
aggregate cost function with efficient production (MWG, Section 10.E). -/
noncomputable def efficientCost (C : ι → ℝ → ℝ) (Q : ℝ) : ℝ :=
  sInf {s | ∃ q : ι → ℝ, (∀ k, 0 ≤ q k) ∧ ∑ k, q k = Q ∧ s = ∑ k, C k (q k)}

/-- Aggregate surplus of an allocation `q`: `∫₀^Q P(s) ds − ∑ₖ Cₖ(qₖ)` (MWG, Section 10.E). -/
noncomputable def allocWelfare (P : ℝ → ℝ) (C : ι → ℝ → ℝ) (q : ι → ℝ) : ℝ :=
  (∫ s in (0 : ℝ)..∑ k, q k, P s) - ∑ k, C k (q k)

/-- Aggregate surplus `S(Q) = ∫₀^Q P(s) ds − C(Q)` with efficient production. -/
noncomputable def efficientSurplus (P : ℝ → ℝ) (C : ι → ℝ → ℝ) (Q : ℝ) : ℝ :=
  (∫ s in (0 : ℝ)..Q, P s) - efficientCost C Q

omit [DecidableEq ι] in
theorem efficientCost_le {C : ι → ℝ → ℝ} (hC : ∀ k y, 0 ≤ y → 0 ≤ C k y) {q : ι → ℝ}
    (hq : ∀ k, 0 ≤ q k) : efficientCost C (∑ k, q k) ≤ ∑ k, C k (q k) := by
  refine csInf_le ⟨0, ?_⟩ ⟨q, hq, rfl, rfl⟩
  rintro s ⟨q', hq', -, rfl⟩
  exact Finset.sum_nonneg fun k _ => hC k _ (hq' k)

omit [DecidableEq ι] in
/-- **Exercise 12.C.10(b)** (MWG, p. 432). With nonnegative costs, let `Q°` maximize the
efficient surplus `S(Q) = ∫₀^Q p − C(Q)` over `Q ≥ 0`. Then `S(Q°)` bounds the surplus of every
allocation (it is the fully efficient outcome), and for the Cournot allocation `q*` the welfare
loss `S(Q°) − W(q*)` splits into `S(Q°) − S(Q*)`, the loss from the level of output valued with
efficient costs, plus `∑ⱼ cⱼ(qⱼ*) − C(Q*)`, the loss from inefficient production; both are
nonnegative. Measuring the loss only by the first term (the triangle under an efficient cost
curve) would omit the second. -/
theorem exercise_12_C_10b {P : ℝ → ℝ} {C : ι → ℝ → ℝ} (hC : ∀ k y, 0 ≤ y → 0 ≤ C k y)
    {Qo : ℝ} (hmax : ∀ Q, 0 ≤ Q → efficientSurplus P C Q ≤ efficientSurplus P C Qo)
    {q : ι → ℝ} (hq : ∀ k, 0 ≤ q k) :
    (∀ q' : ι → ℝ, (∀ k, 0 ≤ q' k) → allocWelfare P C q' ≤ efficientSurplus P C Qo) ∧
    efficientSurplus P C Qo - allocWelfare P C q =
      (efficientSurplus P C Qo - efficientSurplus P C (∑ k, q k)) +
        (∑ k, C k (q k) - efficientCost C (∑ k, q k)) ∧
    0 ≤ efficientSurplus P C Qo - efficientSurplus P C (∑ k, q k) ∧
    0 ≤ ∑ k, C k (q k) - efficientCost C (∑ k, q k) := by
  refine ⟨fun q' hq' => ?_, by unfold allocWelfare efficientSurplus; ring, ?_, ?_⟩
  · have h1 := efficientCost_le hC hq'
    have h2 := hmax _ (Finset.sum_nonneg (fun k _ => hq' k) : 0 ≤ ∑ k, q' k)
    unfold allocWelfare
    unfold efficientSurplus at h2 ⊢
    linarith
  · linarith [hmax _ (Finset.sum_nonneg (fun k _ => hq k) : 0 ≤ ∑ k, q k)]
  · linarith [efficientCost_le hC hq]

/-- **Exercise 12.C.10(b), strict loss** (MWG, p. 432). In the setting of
`exercise_12_C_10a`, with nonnegative costs, if two firms produce in a Nash equilibrium then
the production-inefficiency term `∑ⱼ cⱼ(qⱼ*) − C(Q*)` is strictly positive. -/
theorem exercise_12_C_10b_strict {P P' ct ct' : ℝ → ℝ} {α : ι → ℝ} (hα : Injective α)
    (hP : ∀ Q, HasDerivAt P (P' Q) Q) (hP' : ∀ Q, 0 ≤ Q → P' Q < 0)
    (hct : ∀ y, HasDerivAt ct (ct' y) y) (hmono : StrictMonoOn ct (Ici 0))
    (hconv : ConvexOn ℝ (Ici 0) ct) (hC : ∀ k y, 0 ≤ y → 0 ≤ α k * ct y) {q : ι → ℝ}
    (hq : IsCournotGenNE P (fun k y => α k * ct y) q) {i j : ι} (hij : i ≠ j) (hi : 0 < q i)
    (hj : 0 < q j) :
    0 < ∑ k, α k * ct (q k) - efficientCost (fun k y => α k * ct y) (∑ k, q k) := by
  obtain ⟨q', hq', hsum, hlt⟩ := exercise_12_C_10a hα hP hP' hct hmono hconv hq hij hi hj
  have := efficientCost_le (C := fun k y => α k * ct y) hC hq'
  rw [hsum] at this
  linarith

/-- **Exercise 12.C.10(a)-(b), instance** (MWG, pp. 431-432). With `P(Q) = 10 − Q`,
`c̃(q) = q`, `α = (2, 1)` the unique equilibrium `(7/3, 10/3)` has both firms producing, so its
output is produced inefficiently and the production-inefficiency loss is positive. -/
theorem exercise_12_C_10_instance :
    IsCournotGenNE (fun z => 10 - 1 * z) (fun k y => ![(2 : ℝ), 1] k * id y) ![7 / 3, 10 / 3] ∧
    0 < ∑ k, ![(2 : ℝ), 1] k * id (![(7 : ℝ) / 3, 10 / 3] k) -
      efficientCost (fun k y => ![(2 : ℝ), 1] k * id y) (∑ k, ![(7 : ℝ) / 3, 10 / 3] k) := by
  have hC : (fun k y => ![(2 : ℝ), 1] k * id y) = ccLinCost 2 1 := by
    funext k y; fin_cases k <;> simp [ccLinCost]
  have hne : IsCournotGenNE (fun z => 10 - 1 * z) (fun k y => ![(2 : ℝ), 1] k * id y)
      ![7 / 3, 10 / 3] := by
    rw [hC, ((exercise_12_C_9a (a := 10) (b := 1) (c₁ := 2) (c₂ := 1) (by norm_num) (by norm_num)
      (by norm_num)).1 (by norm_num) _)]
    funext j; fin_cases j <;> norm_num
  refine ⟨hne, exercise_12_C_10b_strict (P' := fun _ => -1) (ct' := fun _ => 1) ?_ ?_ ?_ ?_
    ?_ ?_ ?_ hne (i := 0) (j := 1) (by decide) (by norm_num) (by norm_num)⟩
  · intro i j h; fin_cases i <;> fin_cases j <;> simp_all
  · intro Q; simpa using ((hasDerivAt_id Q).const_mul 1).const_sub 10
  · intro Q _; norm_num
  · intro y; exact hasDerivAt_id y
  · exact strictMono_id.strictMonoOn _
  · exact convexOn_id (convex_Ici 0)
  · intro k y hy; fin_cases k <;> simp [hy]

/-- The surplus `∫₀^Q (a − bs) ds = aQ − bQ²/2`. -/
theorem cc_lin_integral (a b Q : ℝ) : ∫ s in (0 : ℝ)..Q, (a - b * s) = a * Q - b * Q ^ 2 / 2 := by
  have h : ∫ s in (0 : ℝ)..Q, (a - b * s) =
      (∫ _ in (0 : ℝ)..Q, a) - ∫ s in (0 : ℝ)..Q, b * s :=
    intervalIntegral.integral_sub intervalIntegrable_const
      ((continuous_const.mul continuous_id).intervalIntegrable _ _)
  rw [h, intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_id]
  simp only [smul_eq_mul, sub_zero]
  ring

/-- **Exercise 12.C.10(c)** (MWG, p. 432). In the model of Exercise 12.C.9 (`c̃(q) = q`,
`αⱼ = cⱼ`) with both firms producing, welfare at the Cournot equilibrium,
`aQ − bQ²/2 − c₁q₁ − c₂q₂`, has derivative `(11c₁ − 4a − 7c₂)/(9b)` in `c₁`, which is positive
when `11c₁ > 4a + 7c₂`: then a fall in the high-cost firm's `α₁ = c₁` lowers welfare. Example:
`a = 10`, `b = 1`, `c₂ = 1`; the unique equilibria at `c₁ = 5` and `c₁ = 9/2` are `(1/3, 13/3)`
and `(2/3, 25/6)`, and welfare falls from `268/9` to `2123/72`. (Output shifts towards the
inefficient firm 1, raising production costs by more than the gain in consumer surplus.) -/
theorem exercise_12_C_10c {a b c₂ : ℝ} (hb : 0 < b) (c₁ : ℝ) :
    HasDerivAt (fun c => a * ((2 * a - c - c₂) / (3 * b)) -
        b * ((2 * a - c - c₂) / (3 * b)) ^ 2 / 2 -
        c * ((a - 2 * c + c₂) / (3 * b)) - c₂ * ((a - 2 * c₂ + c) / (3 * b)))
      ((11 * c₁ - 4 * a - 7 * c₂) / (9 * b)) c₁ ∧
    (∀ q, IsCournotGenNE (fun z => 10 - 1 * z) (ccLinCost 5 1) q ↔ q = ![1 / 3, 13 / 3]) ∧
    (∀ q, IsCournotGenNE (fun z => 10 - 1 * z) (ccLinCost (9 / 2) 1) q ↔ q = ![2 / 3, 25 / 6]) ∧
    allocWelfare (fun z => 10 - 1 * z) (ccLinCost 5 1) ![1 / 3, 13 / 3] = 268 / 9 ∧
    allocWelfare (fun z => 10 - 1 * z) (ccLinCost (9 / 2) 1) ![2 / 3, 25 / 6] = 2123 / 72 ∧
    (2123 : ℝ) / 72 < 268 / 9 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, by norm_num⟩
  · have hQ : HasDerivAt (fun c => (2 * a - c - c₂) / (3 * b)) (-1 / (3 * b)) c₁ := by
      have := (((hasDerivAt_id c₁).const_sub (2 * a)).sub_const c₂).div_const (3 * b)
      simpa [neg_div] using this
    have hq1 : HasDerivAt (fun c => (a - 2 * c + c₂) / (3 * b)) (-2 / (3 * b)) c₁ := by
      have := ((((hasDerivAt_id c₁).const_mul 2).const_sub a).add_const c₂).div_const (3 * b)
      simpa [neg_div] using this
    have hq2 : HasDerivAt (fun c => (a - 2 * c₂ + c) / (3 * b)) (1 / (3 * b)) c₁ := by
      simpa using ((hasDerivAt_id c₁).const_add (a - 2 * c₂)).div_const (3 * b)
    have h := ((((hQ.const_mul a).sub ((hQ.pow 2).const_mul b |>.div_const 2)).sub
      ((hasDerivAt_id c₁).mul hq1)).sub (hq2.const_mul c₂))
    have hb' : b ≠ 0 := hb.ne'
    convert h using 1
    · funext c
      simp only [Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, id_eq]
    · simp only [id_eq, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
      field_simp
      ring
  · intro q
    have := (exercise_12_C_9a (a := 10) (b := 1) (c₁ := 5) (c₂ := 1) (by norm_num) (by norm_num)
      (by norm_num)).1 (by norm_num) q
    rw [this]; norm_num
  · intro q
    have := (exercise_12_C_9a (a := 10) (b := 1) (c₁ := 9 / 2) (c₂ := 1) (by norm_num)
      (by norm_num) (by norm_num)).1 (by norm_num) q
    rw [this]; norm_num
  · unfold allocWelfare
    rw [cc_lin_integral]
    simp [Fin.sum_univ_two, ccLinCost]
    norm_num
  · unfold allocWelfare
    rw [cc_lin_integral]
    simp [Fin.sum_univ_two, ccLinCost]
    norm_num

/-! ### Exercise 12.C.20 -/

/-- Increments of a convex differentiable function grow when shifted right. -/
theorem cc_convex_increment {c c' : ℝ → ℝ} (hc : ∀ y, HasDerivAt c (c' y) y)
    (hconv : ConvexOn ℝ (Ici 0) c) {s t d : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (hd : 0 ≤ d) :
    c t - c s ≤ c (t + d) - c (s + d) := by
  have hmono : MonotoneOn c' (Ici 0) := by
    have := hconv.monotoneOn_deriv (fun x _ => (hc x).differentiableAt)
    intro x hx y hy hxy
    have h := this hx hy hxy
    rwa [(hc x).deriv, (hc y).deriv] at h
  have hg : MonotoneOn (fun u => c (u + d) - c u) (Ici 0) := by
    have hderiv : ∀ u, HasDerivAt (fun u => c (u + d) - c u) (c' (u + d) - c' u) u := fun u =>
      ((hc (u + d)).comp_add_const u d).sub (hc u)
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun u _ => (hderiv u).continuousAt.continuousWithinAt)
      (fun u _ => (hderiv u).differentiableAt.differentiableWithinAt) fun u hu => ?_
    rw [(hderiv u).deriv]
    rw [interior_Ici] at hu
    have hu' : 0 ≤ u := le_of_lt hu
    have := hmono (mem_Ici.2 hu') (mem_Ici.2 (by linarith)) (by linarith : u ≤ u + d)
    linarith
  have := hg (mem_Ici.2 hs) (mem_Ici.2 (hs.trans hst)) hst
  simp only at this
  linarith

/-- **Exercise 12.C.20** (MWG, p. 433): Proposition 12.C.2 with a general convex cost `c(q)`.
Let `p` be differentiable with `p'(Q) < 0` for `Q ≥ 0`, let `c` be convex on `[0, ∞)` and
differentiable, and `p(0) > c'(0)`. In any Nash equilibrium `(q₁, q₂)` of the Cournot duopoly
(each `qⱼ ≥ 0` a best response to the other) the price exceeds each firm's marginal cost,
`c'(qⱼ) < p(q₁ + q₂)`, and is below the monopoly price `p(qᵐ)`, for any `qᵐ` solving the
monopoly problem with cost `c`. -/
theorem exercise_12_C_20 {P P' c c' : ℝ → ℝ} (hP : ∀ Q, HasDerivAt P (P' Q) Q)
    (hP' : ∀ Q, 0 ≤ Q → P' Q < 0) (hc : ∀ y, HasDerivAt c (c' y) y)
    (hconv : ConvexOn ℝ (Ici 0) c) (h0 : c' 0 < P 0) {q₁ q₂ : ℝ}
    (h1 : IsBROn P c (Ici 0) q₂ q₁) (h2 : IsBROn P c (Ici 0) q₁ q₂) {qm : ℝ}
    (hqm : IsMonopolyOptimum P c qm) :
    c' q₁ < P (q₁ + q₂) ∧ c' q₂ < P (q₁ + q₂) ∧ P (q₁ + q₂) < P qm := by
  have hmono : MonotoneOn c' (Ici 0) := by
    have := hconv.monotoneOn_deriv (fun x _ => (hc x).differentiableAt)
    intro x hx y hy hxy
    have h := this hx hy hxy
    rwa [(hc x).deriv, (hc y).deriv] at h
  have hq1 : 0 ≤ q₁ := h1.1
  have hq2 : 0 ≤ q₂ := h2.1
  obtain ⟨f1, f1'⟩ := cbr_foc hP hc h1
  obtain ⟨f2, f2'⟩ := cbr_foc hP hc h2
  rw [add_comm q₂ q₁] at f1 f1'
  have hQ : 0 ≤ q₁ + q₂ := by linarith
  -- both firms produce
  have hpos : ∀ y z, 0 ≤ y → 0 ≤ z → P (y + z) + y * P' (y + z) ≤ c' y →
      (0 < z → P (y + z) + z * P' (y + z) = c' z) → 0 < y := by
    intro y z hy hz fy fz
    by_contra hy0
    have hy0' : y = 0 := le_antisymm (not_lt.1 hy0) hy
    subst hy0'
    simp only [zero_add, zero_mul, add_zero] at fy fz
    rcases eq_or_lt_of_le hz with hz0 | hz0
    · subst hz0; linarith
    · have := fz hz0
      have hm := hmono (mem_Ici.2 le_rfl) (mem_Ici.2 hz) hz
      have := mul_neg_of_pos_of_neg hz0 (hP' z hz)
      linarith
  have hp1 : 0 < q₁ := hpos q₁ q₂ hq1 hq2 f1 f2'
  have hp2 : 0 < q₂ := hpos q₂ q₁ hq2 hq1 (by rw [add_comm q₂ q₁]; exact f2)
    (fun h => by rw [add_comm q₂ q₁]; exact f1' h)
  have e1 := f1' hp1
  have e2 := f2' hp2
  have hm1 : c' q₁ < P (q₁ + q₂) := by nlinarith [mul_neg_of_pos_of_neg hp1 (hP' _ hQ)]
  have hm2 : c' q₂ < P (q₁ + q₂) := by nlinarith [mul_neg_of_pos_of_neg hp2 (hP' _ hQ)]
  refine ⟨hm1, hm2, ?_⟩
  have hPd : ∀ z ∈ Ici (0 : ℝ), HasDerivWithinAt P (P' z) (Ici 0) z :=
    fun z _ => (hP z).hasDerivWithinAt
  have hanti := strictAntiOn_of_deriv_neg' hPd hP'
  -- the monopoly first-order condition
  obtain ⟨hqmpos, hfm⟩ := eq_12_B_4 (hP qm).hasDerivWithinAt (hc qm).hasDerivWithinAt hqm h0
  -- `Q* ≥ qᵐ`
  have hge : qm ≤ q₁ + q₂ := by
    by_contra hlt
    push Not at hlt
    have hdev := h1.2 (qm - q₂) (mem_Ici.2 (by linarith))
    unfold cbrProfit at hdev
    rw [show q₂ + (qm - q₂) = qm by ring, show q₂ + q₁ = q₁ + q₂ by ring] at hdev
    have hmon := hqm.2 (q₁ + q₂) hQ
    unfold monopolyProfit at hmon
    have hinc := cc_convex_increment hc hconv hq1 (show q₁ ≤ qm - q₂ by linarith) hq2
    rw [show qm - q₂ + q₂ = qm by ring] at hinc
    have hpl : P qm < P (q₁ + q₂) := hanti (mem_Ici.2 hQ) (mem_Ici.2 hqmpos.le) hlt
    nlinarith [mul_lt_mul_of_pos_right hpl hp2]
  rcases eq_or_lt_of_le hge with heq | hlt
  · exfalso
    rw [← heq] at e1
    have hm := hmono (mem_Ici.2 hq1) (mem_Ici.2 hqmpos.le) (by rw [heq]; linarith)
    have : P' qm * q₂ < 0 := mul_neg_of_neg_of_pos (hP' qm hqmpos.le) hp2
    have hsum : qm = q₁ + q₂ := heq
    nlinarith
  · exact hanti (mem_Ici.2 hqm.1) (mem_Ici.2 hQ) hlt

/-- **Exercise 12.C.20, instance** (MWG, p. 433). With `p(Q) = 10 − Q` and `c(q) = q²`, the
outputs `q₁ = q₂ = 2` are mutual best responses and `qᵐ = 5/2` is the monopoly output; the
equilibrium price `6` exceeds marginal cost `4` and is below the monopoly price `15/2`. -/
theorem exercise_12_C_20_instance :
    (2 * 2 : ℝ) < 10 - (2 + 2) ∧ (10 : ℝ) - (2 + 2) < 10 - 5 / 2 := by
  have hP : ∀ Q : ℝ, HasDerivAt (fun Q => 10 - Q) (-1) Q := fun Q => by
    simpa using (hasDerivAt_id Q).const_sub 10
  have hc : ∀ y : ℝ, HasDerivAt (fun y => y ^ 2) (2 * y) y := fun y => by
    simpa using hasDerivAt_pow 2 y
  have hconv : ConvexOn ℝ (Ici 0) (fun y : ℝ => y ^ 2) := (convexOn_pow 2).subset
    (subset_refl _) (convex_Ici 0)
  have hbr : IsBROn (fun Q => 10 - Q) (fun y => y ^ 2) (Ici 0) 2 2 := by
    refine ⟨mem_Ici.2 (by norm_num), fun y _ => ?_⟩
    unfold cbrProfit
    nlinarith [sq_nonneg (y - 2)]
  have hm : IsMonopolyOptimum (fun Q => 10 - Q) (fun y => y ^ 2) (5 / 2) := by
    refine ⟨by norm_num, fun q _ => ?_⟩
    unfold monopolyProfit
    nlinarith [sq_nonneg (q - 5 / 2)]
  obtain ⟨h1, -, h3⟩ := exercise_12_C_20 (P' := fun _ => -1) (c' := fun y => 2 * y) hP
    (fun _ _ => by norm_num) hc hconv (by norm_num) hbr hbr hm
  exact ⟨h1, h3⟩

end MWG.MarketPower
