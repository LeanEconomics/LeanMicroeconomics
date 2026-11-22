/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGMarketPower.Cournot
import MWGSimultaneousMoveGames.Existence

/-!
# Existence of Cournot equilibrium and quasiconcavity

MWG, Section 12.C, small type on p. 393.

The quantity game has firms `j ∈ ι`, inverse demand `p(·)` and cost functions `c_j(·)`; firm `j`
earns `p(∑ q_k)q_j − c_j(q_j)` (`cournotGenProfit`).

* `smallType_12_C_393`: "with quasiconcavity, we can use Proposition 8.D.3 to show that a pure
  strategy Nash equilibrium necessarily exists". Proposition 8.D.3 needs compact strategy sets,
  so quantities are taken in `[0, B]`; with `p` continuous on `[0, ∞)`, each `c_j` continuous and
  each profit quasiconcave in the firm's own quantity, an equilibrium of the game on `[0, B]`
  exists (Chapter 8's `nash_exists_of_quasiconcave`).
* `smallType_12_C_393_unbounded`: with constant marginal cost `c` and `p(Q) ≤ c` for `Q ≥ B`, the
  equilibrium of the truncated game is a Cournot equilibrium on `[0, ∞)` (`IsCournotNE`).
  `smallType_12_C_393_linear` instantiates it for `p(Q) = a − bQ`.
* `smallType_12_C_393_nonexistence`: "without quasiconcavity ... a pure strategy Nash
  equilibrium of this quantity game may not exist": a duopoly with a convex kinked inverse demand
  and costs that are zero (firm 1) or linear (firm 2) on two output levels and prohibitive
  elsewhere has no pure strategy equilibrium.

Departure: the existence statement adds the compact strategy set `[0, B]` that Proposition 8.D.3
requires (correction 25).
-/

namespace MWG.MarketPower

open Set Function

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Firm `j`'s profit `p(∑ q_k)q_j − c_j(q_j)` in the Cournot game with cost functions `c_j`
(problem (12.C.1), MWG, p. 390). -/
def cournotGenProfit (p : ℝ → ℝ) (C : ι → ℝ → ℝ) (q : ι → ℝ) (j : ι) : ℝ :=
  p (∑ k, q k) * q j - C j (q j)

/-- **Small type, p. 393** (MWG), via **Proposition 8.D.3**. If quantities lie in `[0, B]`, the
inverse demand is continuous on `[0, ∞)`, the costs are continuous on `[0, B]` and each firm's
profit is quasiconcave in its own quantity, a pure strategy Nash equilibrium exists. -/
theorem smallType_12_C_393 {p : ℝ → ℝ} {C : ι → ℝ → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hp : ContinuousOn p (Ici 0)) (hC : ∀ j, ContinuousOn (C j) (Icc 0 B))
    (hqc : ∀ j, ∀ q : ι → ℝ, (∀ k, q k ∈ Icc 0 B) →
      QuasiconcaveOn ℝ (Icc 0 B) fun y => cournotGenProfit p C (update q j y) j) :
    ∃ q : ι → ℝ, (∀ k, q k ∈ Icc 0 B) ∧
      ∀ j, ∀ y ∈ Icc 0 B, cournotGenProfit p C (update q j y) j ≤ cournotGenProfit p C q j := by
  have hmem : ∀ q : ι → ℝ, q ∈ Set.pi univ (fun _ : ι => Icc (0 : ℝ) B) ↔ ∀ k, q k ∈ Icc 0 B :=
    fun q => Set.mem_univ_pi
  have hcont : ∀ j, ContinuousOn (fun q : ι → ℝ => cournotGenProfit p C q j)
      (Set.pi univ fun _ : ι => Icc (0 : ℝ) B) := by
    intro j
    unfold cournotGenProfit
    have hsum : ContinuousOn (fun q : ι → ℝ => p (∑ k, q k))
        (Set.pi univ fun _ : ι => Icc (0 : ℝ) B) :=
      hp.comp (continuous_finsetSum _ fun k _ => continuous_apply k).continuousOn
        fun q hq => Finset.sum_nonneg fun k _ => ((hmem q).1 hq k).1
    have hc : ContinuousOn (fun q : ι → ℝ => C j (q j))
        (Set.pi univ fun _ : ι => Icc (0 : ℝ) B) :=
      (hC j).comp (continuous_apply j).continuousOn fun q hq => (hmem q).1 hq j
    exact (hsum.mul (continuous_apply j).continuousOn).sub hc
  obtain ⟨q, hq, hne⟩ := MWG.SimultaneousMoveGames.nash_exists_of_quasiconcave
    (E := fun _ : ι => ℝ) (u := fun j q => cournotGenProfit p C q j)
    (S := fun _ : ι => Icc (0 : ℝ) B) (fun _ => nonempty_Icc.2 hB) (fun _ => isCompact_Icc)
    (fun _ => convex_Icc 0 B) hcont (fun j s hs => hqc j s ((hmem s).1 hs))
  exact ⟨q, (hmem q).1 hq, hne⟩

/-- **Small type, p. 393** (MWG), on the book's strategy sets `[0, ∞)`: with constant marginal
cost `c`, if `p(Q) ≤ c` for `Q ≥ B` then the equilibrium of the game on `[0, B]` is a Cournot
equilibrium (no firm gains by any output `y ≥ 0`). -/
theorem smallType_12_C_393_unbounded {p : ℝ → ℝ} {c B : ℝ} (hB : 0 ≤ B)
    (hp : ContinuousOn p (Ici 0))
    (hqc : ∀ j, ∀ q : ι → ℝ, (∀ k, q k ∈ Icc 0 B) →
      QuasiconcaveOn ℝ (Icc 0 B) fun y => cournotProfit p c (update q j y) j)
    (hpB : ∀ Q, B ≤ Q → p Q ≤ c) : ∃ q : ι → ℝ, IsCournotNE p c q := by
  obtain ⟨q, hq, hne⟩ := smallType_12_C_393 (C := fun _ y => c * y) hB hp
    (fun _ => (continuous_const.mul continuous_id).continuousOn) hqc
  refine ⟨q, fun j => (hq j).1, fun j y hy => ?_⟩
  by_cases hyB : y ≤ B
  · exact hne j y ⟨hy, hyB⟩
  · push Not at hyB
    have h0 := hne j 0 ⟨le_rfl, hB⟩
    have hrest : 0 ≤ ∑ k, q k - q j := by
      have := Finset.sum_nonneg (s := Finset.univ) fun k (_ : k ∈ Finset.univ) =>
        (show 0 ≤ update q j 0 k by
          by_cases hk : k = j
          · rw [hk, update_self]
          · rw [update_of_ne hk]; exact (hq k).1)
      rw [sum_update_eq] at this
      linarith
    have hdev : cournotProfit p c (update q j y) j ≤ 0 := by
      unfold cournotProfit
      rw [sum_update_eq, update_self]
      have := hpB (y + (∑ k, q k - q j)) (by linarith)
      nlinarith
    have hzero : cournotGenProfit p (fun _ y => c * y) (update q j 0) j = 0 := by
      unfold cournotGenProfit; rw [update_self]; ring
    have : cournotGenProfit p (fun _ y => c * y) q j = cournotProfit p c q j := rfl
    linarith

/-- The hypotheses of `smallType_12_C_393_unbounded` hold for the linear model
`p(Q) = a − bQ` (`a > c`, `b > 0`) with `B = (a − c)/b`: each profit is concave in own output. -/
theorem smallType_12_C_393_linear {a b c : ℝ} (hac : c < a) (hb : 0 < b) :
    0 ≤ (a - c) / b ∧ ContinuousOn (fun Q => a - b * Q) (Ici 0) ∧
    (∀ j, ∀ q : ι → ℝ, (∀ k, q k ∈ Icc 0 ((a - c) / b)) →
      QuasiconcaveOn ℝ (Icc 0 ((a - c) / b)) fun y =>
        cournotProfit (fun Q => a - b * Q) c (update q j y) j) ∧
    (∀ Q, (a - c) / b ≤ Q → a - b * Q ≤ c) ∧ ∃ q : ι → ℝ, IsCournotNE (fun Q => a - b * Q) c q := by
  have hB : 0 ≤ (a - c) / b := div_nonneg (by linarith) hb.le
  have hcont : ContinuousOn (fun Q : ℝ => a - b * Q) (Ici 0) :=
    (continuous_const.sub (continuous_const.mul continuous_id)).continuousOn
  have hqc : ∀ j, ∀ q : ι → ℝ, (∀ k, q k ∈ Icc 0 ((a - c) / b)) →
      QuasiconcaveOn ℝ (Icc 0 ((a - c) / b)) fun y =>
        cournotProfit (fun Q => a - b * Q) c (update q j y) j := by
    intro j q _
    apply ConcaveOn.quasiconcaveOn
    refine ⟨convex_Icc _ _, fun u _ v _ α β hα hβ hαβ => ?_⟩
    simp only [cournotProfit, sum_update_eq, update_self, smul_eq_mul]
    obtain rfl : β = 1 - α := by linarith
    nlinarith [mul_nonneg (mul_nonneg hα hβ) (mul_nonneg hb.le (sq_nonneg (u - v)))]
  have hpB : ∀ Q, (a - c) / b ≤ Q → a - b * Q ≤ c := by
    intro Q hQ
    rw [div_le_iff₀ hb] at hQ
    linarith
  exact ⟨hB, hcont, hqc, hpB, smallType_12_C_393_unbounded hB hcont hqc hpB⟩

/-! ### Nonexistence without quasiconcavity -/

/-- A pure strategy Nash equilibrium of the Cournot game with cost functions `c_j` and
quantities in `[0, ∞)`. -/
def IsCournotGenNE (p : ℝ → ℝ) (C : ι → ℝ → ℝ) (q : ι → ℝ) : Prop :=
  (∀ j, 0 ≤ q j) ∧ ∀ j y, 0 ≤ y → cournotGenProfit p C (update q j y) j ≤ cournotGenProfit p C q j

/-- A convex, kinked, strictly decreasing (until it reaches zero) inverse demand. -/
noncomputable def cnxP (Q : ℝ) : ℝ := if Q ≤ 2 then 10 - 4 * Q else max 0 (3 - Q / 2)

/-- Costs: firm `0` produces `1` or `2` at no cost, firm `1` produces `0` or `1` at unit cost
`7/4`; any other output costs `100`. -/
noncomputable def cnxC (j : Fin 2) (y : ℝ) : ℝ :=
  if j = 0 then (if y = 1 ∨ y = 2 then 0 else 100) else (if y = 0 ∨ y = 1 then 7 / 4 * y else 100)

theorem cnxP_rev {y R : ℝ} (hy : 0 ≤ y) (hR : 0 ≤ R) : 0 ≤ cnxP (y + R) * y ∧
    cnxP (y + R) * y ≤ 60 := by
  unfold cnxP
  split_ifs with h
  · constructor <;> nlinarith
  · rcases le_total (3 - (y + R) / 2) 0 with h' | h'
    · rw [max_eq_left h']; simp
    · rw [max_eq_right h']; constructor <;> nlinarith

theorem cournotGenProfit_fin0 (p : ℝ → ℝ) (C : Fin 2 → ℝ → ℝ) (q : Fin 2 → ℝ) (y : ℝ) :
    cournotGenProfit p C (update q 0 y) 0 = p (y + q 1) * y - C 0 y := by
  simp [cournotGenProfit, Fin.sum_univ_two]

theorem cournotGenProfit_fin1 (p : ℝ → ℝ) (C : Fin 2 → ℝ → ℝ) (q : Fin 2 → ℝ) (y : ℝ) :
    cournotGenProfit p C (update q 1 y) 1 = p (q 0 + y) * y - C 1 y := by
  simp [cournotGenProfit, Fin.sum_univ_two]

/-- **Small type, p. 393** (MWG): "without quasiconcavity of these functions, however, a pure
strategy Nash equilibrium of this quantity game may not exist." With the inverse demand `cnxP`
and the costs `cnxC` (whose profits are not quasiconcave), the duopoly has no pure strategy Nash
equilibrium: the best responses cycle `(1, 0) → (1, 1) → (2, 1) → (2, 0) → (1, 0)`. -/
theorem smallType_12_C_393_nonexistence : ¬ ∃ q : Fin 2 → ℝ, IsCournotGenNE cnxP cnxC q := by
  rintro ⟨q, hq0, hne⟩
  have cur0 : cournotGenProfit cnxP cnxC q 0 = cnxP (q 0 + q 1) * q 0 - cnxC 0 (q 0) := by
    simp [cournotGenProfit, Fin.sum_univ_two]
  have cur1 : cournotGenProfit cnxP cnxC q 1 = cnxP (q 0 + q 1) * q 1 - cnxC 1 (q 1) := by
    simp [cournotGenProfit, Fin.sum_univ_two]
  have d0 := fun y hy => hne 0 y hy
  have d1 := fun y hy => hne 1 y hy
  simp only [cournotGenProfit_fin0, cournotGenProfit_fin1, cur0, cur1] at d0 d1
  -- firm 0 produces `1` or `2`
  have h0 : q 0 = 1 ∨ q 0 = 2 := by
    by_contra hn
    have hc : cnxC 0 (q 0) = 100 := by simp [cnxC, hn]
    have := d0 1 zero_le_one
    have hr := cnxP_rev (hq0 0) (hq0 1)
    have hr1 := cnxP_rev zero_le_one (hq0 1)
    have hc1 : cnxC 0 1 = 0 := by simp [cnxC]
    rw [hc, hc1] at this
    linarith [hr.2, hr1.1]
  -- firm 1 produces `0` or `1`
  have h1 : q 1 = 0 ∨ q 1 = 1 := by
    by_contra hn
    have hc : cnxC 1 (q 1) = 100 := by simp [cnxC, hn]
    have := d1 0 le_rfl
    have hr := cnxP_rev (hq0 1) (hq0 0)
    rw [add_comm (q 1)] at hr
    have hc0 : cnxC 1 0 = 0 := by simp [cnxC]
    rw [hc, hc0] at this
    simp only [mul_zero] at this
    linarith [hr.2]
  rcases h0 with e0 | e0 <;> rcases h1 with e1 | e1 <;> rw [e0, e1] at d0 d1
  · -- `(1, 0)`: firm 1 gains by producing `1`
    have := d1 1 zero_le_one
    norm_num [cnxP, cnxC] at this
  · -- `(1, 1)`: firm 0 gains by producing `2`
    have := d0 2 zero_le_two
    norm_num [cnxP, cnxC] at this
  · -- `(2, 0)`: firm 0 gains by producing `1`
    have := d0 1 zero_le_one
    norm_num [cnxP, cnxC] at this
  · -- `(2, 1)`: firm 1 gains by producing `0`
    have := d1 0 le_rfl
    norm_num [cnxP, cnxC] at this

end MWG.MarketPower
