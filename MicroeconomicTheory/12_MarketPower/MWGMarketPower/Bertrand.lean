/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGSimultaneousMoveGames.Dominance
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# The Bertrand model of price competition

MWG, Section 12.C, pp. 388-389, and Exercises 12.C.1 and 12.C.3.

Firms `j ∈ ι` name prices simultaneously; demand `x(·)` is continuous, nonnegative, strictly
decreasing where positive, zero above some `p̄`, with `x(c) > 0`; each firm has unit cost `c > 0`.
The lowest-priced firms share the market equally: a firm naming the lowest price `p` together
with `J̄ − 1` others sells `x(p)/J̄`; the others sell nothing (`bertrandSales`). For two firms this
is MWG's sales function `x_j(p_j, p_k)` (`bertrandSales_duopoly`). The game is a Chapter 8
`NormalForm` (`bertrandGame`), and equilibrium is Chapter 8's `IsNashEquilibrium`.

* `proposition_12_C_1`: the unique Nash equilibrium of the duopoly is `p₁ = p₂ = c`.
* `exercise_12_C_1`: with `J ≥ 2` firms the lowest price is `c` in every Nash equilibrium, so all
  sales take place at a price equal to cost.
* `exercise_12_C_3a`, `exercise_12_C_3b`: prices on a grid of size `Δ`.

MWG's proof of Proposition 12.C.1 deviates to `p_j − ε` and to `c + (p_k − c)/2`; these give
strictly positive profit only if demand is positive there. The proofs below deviate instead to a
price chosen with the continuity of `(p − c)x(p)` (`bertrand_deviation`), which covers prices
above `p̄`.
-/

namespace MWG.MarketPower

open MWG.NoncooperativeGames MWG.SimultaneousMoveGames Function Finset

/-- The demand assumptions of the Bertrand model (MWG, p. 388): `x` is continuous, nonnegative,
strictly decreasing at all `p` with `x(p) > 0`, and `x(p) = 0` for `p ≥ p̄`. -/
structure IsBertrandDemand (x : ℝ → ℝ) (pbar : ℝ) : Prop where
  cont : Continuous x
  nonneg : ∀ p, 0 ≤ x p
  strictAnti : ∀ p p', p < p' → 0 < x p' → x p' < x p
  zero : ∀ p, pbar ≤ p → x p = 0

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Sales of firm `j` at the price profile `p` (MWG, pp. 388-389): if `p j` is a lowest price it
sells `x(p j)/J̄`, where `J̄` is the number of firms naming that price; otherwise nothing. -/
noncomputable def bertrandSales (x : ℝ → ℝ) (p : ι → ℝ) (j : ι) : ℝ :=
  if ∀ k, p j ≤ p k then x (p j) / ((univ.filter fun k => p k = p j).card : ℝ) else 0

/-- Firm `j`'s profit `(p_j − c)x_j(p)`. -/
noncomputable def bertrandProfit (x : ℝ → ℝ) (c : ℝ) (p : ι → ℝ) (j : ι) : ℝ :=
  (p j - c) * bertrandSales x p j

/-- **The Bertrand game** (MWG, p. 388) as a game in normal form. -/
noncomputable def bertrandGame (ι : Type*) [Fintype ι] [DecidableEq ι] (x : ℝ → ℝ) (c : ℝ) :
    NormalForm ι (fun _ => ℝ) where
  payoff j p := bertrandProfit x c p j

/-- **The duopoly sales function** (MWG, p. 388): `x_j = x(p_j)` if `p_j < p_k`, `x(p_j)/2` if
`p_j = p_k`, and `0` if `p_j > p_k`. -/
theorem bertrandSales_duopoly (x : ℝ → ℝ) (p : Fin 2 → ℝ) :
    bertrandSales x p 0 = if p 0 < p 1 then x (p 0) else if p 0 = p 1 then x (p 0) / 2 else 0 := by
  unfold bertrandSales
  rcases lt_trichotomy (p 0) (p 1) with h | h | h
  · have hall : ∀ k, p 0 ≤ p k := by intro k; fin_cases k <;> simp [h.le]
    have hcard : (univ.filter fun k => p k = p 0) = {0} := by
      ext k; fin_cases k <;> simp [h.ne']
    simp only [hall, implies_true, ↓reduceIte]
    rw [hcard]
    simp [h]
  · have hall : ∀ k, p 0 ≤ p k := by intro k; fin_cases k <;> simp [h.le]
    have hcard : (univ.filter fun k => p k = p 0) = univ := by
      ext k; fin_cases k <;> simp [h]
    simp only [hall, implies_true, ↓reduceIte]
    rw [hcard]
    simp [h]
  · have hn : ¬ ∀ k, p 0 ≤ p k := fun hall => absurd (hall 1) (not_le.2 h)
    simp [hn, h.not_gt, h.ne']

omit [DecidableEq ι] in
theorem bertrandSales_nonneg {x : ℝ → ℝ} (hx : ∀ p, 0 ≤ x p) (p : ι → ℝ) (j : ι) :
    0 ≤ bertrandSales x p j := by
  unfold bertrandSales; split_ifs
  · exact div_nonneg (hx _) (Nat.cast_nonneg _)
  · exact le_rfl

omit [DecidableEq ι] in
theorem bertrandSales_le {x : ℝ → ℝ} (hx : ∀ p, 0 ≤ x p) (p : ι → ℝ) (j : ι) :
    bertrandSales x p j ≤ x (p j) := by
  unfold bertrandSales; split_ifs
  · have h1 : (1 : ℝ) ≤ ((univ.filter fun k => p k = p j).card : ℝ) := by
      exact_mod_cast Finset.card_pos.2 ⟨j, by simp⟩
    exact div_le_self (hx _) h1
  · exact hx _

omit [DecidableEq ι] in
/-- A firm naming a strictly lowest price sells the whole demand. -/
theorem bertrandSales_of_lt {x : ℝ → ℝ} {p : ι → ℝ} {j : ι} (h : ∀ k, k ≠ j → p j < p k) :
    bertrandSales x p j = x (p j) := by
  classical
  unfold bertrandSales
  have hall : ∀ k, p j ≤ p k := fun k => by
    by_cases hk : k = j
    · rw [hk]
    · exact (h k hk).le
  have hcard : (univ.filter fun k => p k = p j) = {j} := by
    ext k; simp only [mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · intro hk; by_contra hne; exact (h k hne).ne' hk
    · rintro rfl; rfl
  simp [hall, hcard]

omit [DecidableEq ι] in
/-- A firm whose price is not a lowest price sells nothing. -/
theorem bertrandSales_of_gt {x : ℝ → ℝ} {p : ι → ℝ} {j k : ι} (h : p k < p j) :
    bertrandSales x p j = 0 := by
  unfold bertrandSales
  have hn : ¬ ∀ k, p j ≤ p k := fun hall => absurd (hall k) (not_le.2 h)
  simp [hn]

/-- The key deviation: for `m > c` there is a price `p' ∈ (c, m)` with
`(p' − c)x(p') > (m − c)x(m)/2`. -/
theorem bertrand_deviation {x : ℝ → ℝ} {pbar c m : ℝ} (hx : IsBertrandDemand x pbar)
    (hxc : 0 < x c) (hm : c < m) :
    ∃ p', c < p' ∧ p' < m ∧ (m - c) * x m / 2 < (p' - c) * x p' := by
  have hg : Continuous fun p => (p - c) * x p := (continuous_id.sub continuous_const).mul hx.cont
  have hgm : 0 ≤ (m - c) * x m := mul_nonneg (by linarith) (hx.nonneg m)
  rcases eq_or_lt_of_le hgm with h0 | hpos
  · -- positive demand just above `c`
    have hev : ∀ᶠ p in nhds c, 0 < x p := hx.cont.continuousAt.eventually (lt_mem_nhds hxc)
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
    set p' := c + min δ (m - c) / 2 with hp'
    have hmin : 0 < min δ (m - c) := lt_min hδ (by linarith)
    have hp'c : c < p' := by rw [hp']; linarith
    have hp'm : p' < m := by rw [hp']; linarith [min_le_right δ (m - c)]
    have hxp : 0 < x p' := hball (by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith [min_le_left δ (m - c)])
    refine ⟨p', hp'c, hp'm, ?_⟩
    rw [← h0]; simp only [zero_div]
    exact mul_pos (by linarith) hxp
  · -- continuity at `m`
    have hev : ∀ᶠ p in nhds m, (m - c) * x m / 2 < (p - c) * x p :=
      hg.continuousAt.eventually (lt_mem_nhds (by linarith))
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
    set p' := max (m - δ / 2) ((c + m) / 2) with hp'
    have hp'c : c < p' := by rw [hp']; exact lt_of_lt_of_le (by linarith) (le_max_right _ _)
    have hp'm : p' < m := by rw [hp']; exact max_lt (by linarith) (by linarith)
    refine ⟨p', hp'c, hp'm, hball ?_⟩
    rw [Real.dist_eq, abs_lt]
    constructor
    · linarith [le_max_left (m - δ / 2) ((c + m) / 2)]
    · linarith

omit [DecidableEq ι] in
/-- In a Nash equilibrium no firm earns less than it would from the price `c`... more simply:
at any price at most `c` a firm earns at most `0`. -/
theorem bertrandProfit_le_zero {x : ℝ → ℝ} (hx : ∀ p, 0 ≤ x p) {c : ℝ} {p : ι → ℝ} {j : ι}
    (h : p j ≤ c) : bertrandProfit x c p j ≤ 0 :=
  mul_nonpos_of_nonpos_of_nonneg (by linarith) (bertrandSales_nonneg hx p j)

omit [DecidableEq ι] in
/-- Profits are nonnegative at prices at least `c`. -/
theorem bertrandProfit_nonneg {x : ℝ → ℝ} (hx : ∀ p, 0 ≤ x p) {c : ℝ} {p : ι → ℝ} {j : ι}
    (h : c ≤ p j) : 0 ≤ bertrandProfit x c p j :=
  mul_nonneg (by linarith) (bertrandSales_nonneg hx p j)

/-- **Exercise 12.C.1** (MWG, p. 389). In the Bertrand model with `J ≥ 2` firms, in any Nash
equilibrium the lowest price is `c`: all sales take place at a price equal to cost (the firms
naming `c` share `x(c) > 0`, the others sell nothing). -/
theorem exercise_12_C_1 {x : ℝ → ℝ} {pbar c : ℝ} (hx : IsBertrandDemand x pbar) (hc : 0 < c)
    (hxc : 0 < x c) (h2 : 2 ≤ Fintype.card ι) {p : ι → ℝ}
    (hne : IsNashEquilibrium (bertrandGame ι x c) p) :
    ∃ j, (∀ k, p j ≤ p k) ∧ p j = c := by
  have _ := hc
  have hnem : (univ : Finset ι).Nonempty := univ_nonempty_iff.2 (by
    rw [← Fintype.card_pos_iff]; omega)
  obtain ⟨j, -, hj⟩ := exists_min_image univ p hnem
  have hjmin : ∀ k, p j ≤ p k := fun k => hj k (mem_univ k)
  refine ⟨j, hjmin, ?_⟩
  set m := p j with hm
  rcases lt_trichotomy m c with hlt | heq | hgt
  · -- the lowest price is below cost: firm `j` sells at a loss
    exfalso
    have hxm : 0 < x m := by
      by_contra h0; push Not at h0
      have := hx.strictAnti m c hlt hxc; linarith [hx.nonneg m]
    have hsales : 0 < bertrandSales x p j := by
      unfold bertrandSales
      split_ifs with hcond
      · exact div_pos hxm (by exact_mod_cast Finset.card_pos.2 ⟨j, by simp⟩)
      · exact absurd hjmin hcond
    have hprof : bertrandProfit x c p j < 0 := mul_neg_of_neg_of_pos (by linarith) hsales
    have hdev := hne j c
    have : bertrandProfit x c (update p j c) j ≤ 0 :=
      bertrandProfit_le_zero hx.nonneg (by simp)
    have h0 : (bertrandGame ι x c).payoff j (update p j c) = bertrandProfit x c (update p j c) j :=
      rfl
    have h1 : (bertrandGame ι x c).payoff j p = bertrandProfit x c p j := rfl
    -- deviating to a price above `p̄` gives profit `0`
    have hdev2 := hne j (max pbar c + 1)
    have hz : bertrandProfit x c (update p j (max pbar c + 1)) j = 0 := by
      unfold bertrandProfit
      have : bertrandSales x (update p j (max pbar c + 1)) j = 0 := by
        have hle := bertrandSales_le hx.nonneg (update p j (max pbar c + 1)) j
        have hge := bertrandSales_nonneg hx.nonneg (update p j (max pbar c + 1)) j
        simp only [update_self] at hle
        rw [hx.zero _ (by linarith [le_max_left pbar c])] at hle
        linarith
      rw [this, mul_zero]
    change bertrandProfit x c (update p j (max pbar c + 1)) j ≤ bertrandProfit x c p j at hdev2
    linarith
  · exact heq
  · -- the lowest price exceeds cost: some firm earns at most half of `(m − c)x(m)`
    exfalso
    obtain ⟨p', hp'c, hp'm, hgain⟩ := bertrand_deviation hx hxc hgt
    -- a firm `k` earning at most `(m − c)x(m)/2`
    have hk : ∃ k, bertrandProfit x c p k ≤ (m - c) * x m / 2 := by
      by_cases hall : ∀ k, k ≠ j → p j < p k
      · -- `j` is the unique lowest; another firm earns nothing
        have hcard : 1 < Fintype.card ι := by omega
        obtain ⟨k, hkj⟩ := Fintype.exists_ne_of_one_lt_card hcard j
        refine ⟨k, ?_⟩
        unfold bertrandProfit
        rw [bertrandSales_of_gt (hall k hkj), mul_zero]
        exact div_nonneg (mul_nonneg (by linarith) (hx.nonneg m)) (by norm_num)
      · push Not at hall
        obtain ⟨k, hkj, hpk⟩ := hall
        have hpkm : p k = m := le_antisymm hpk (hjmin k)
        refine ⟨j, ?_⟩
        unfold bertrandProfit bertrandSales
        split_ifs with hcond
        swap
        · exact absurd hjmin hcond
        have h2le : (2 : ℝ) ≤ ((univ.filter fun l => p l = p j).card : ℝ) := by
          have : ({j, k} : Finset ι) ⊆ univ.filter fun l => p l = p j := by
            intro l hl
            simp only [mem_insert, mem_singleton] at hl
            rcases hl with rfl | rfl
            · simp
            · simp [hpkm, hm]
          have hc2 := Finset.card_le_card this
          rw [Finset.card_pair (Ne.symm hkj)] at hc2
          exact_mod_cast hc2
        rw [← hm, mul_div_assoc]
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        exact div_le_div_of_nonneg_left (hx.nonneg m) (by norm_num) h2le
    obtain ⟨k, hkle⟩ := hk
    have hdev := hne k p'
    change bertrandProfit x c (update p k p') k ≤ bertrandProfit x c p k at hdev
    have hlow : ∀ l, l ≠ k → (update p k p') k < (update p k p') l := by
      intro l hl
      simp only [update_self, update_of_ne hl]
      exact lt_of_lt_of_le hp'm (hjmin l)
    have hval : bertrandProfit x c (update p k p') k = (p' - c) * x p' := by
      unfold bertrandProfit
      rw [bertrandSales_of_lt hlow]
      simp
    linarith

/-- **Proposition 12.C.1** (MWG, p. 388). There is a unique Nash equilibrium `(p₁*, p₂*)` of the
Bertrand duopoly: `p₁* = p₂* = c`. -/
theorem proposition_12_C_1 {x : ℝ → ℝ} {pbar c : ℝ} (hx : IsBertrandDemand x pbar) (hc : 0 < c)
    (hxc : 0 < x c) :
    IsNashEquilibrium (bertrandGame (Fin 2) x c) (fun _ => c) ∧
    ∀ p, IsNashEquilibrium (bertrandGame (Fin 2) x c) p → p = fun _ => c := by
  constructor
  · intro j t
    change bertrandProfit x c (update (fun _ => c) j t) j ≤ bertrandProfit x c (fun _ => c) j
    have h0 : bertrandProfit x c (fun _ : Fin 2 => c) j = 0 := by simp [bertrandProfit]
    rw [h0]
    rcases le_or_gt t c with h | h
    · exact bertrandProfit_le_zero hx.nonneg (by simpa using h)
    · obtain ⟨k, hk⟩ : ∃ k, k ≠ j := ⟨j + 1, by fin_cases j <;> decide⟩
      unfold bertrandProfit
      rw [bertrandSales_of_gt (k := k) (by simpa [update_of_ne hk] using h), mul_zero]
  · intro p hne
    obtain ⟨j, hjmin, hj⟩ := exercise_12_C_1 hx hc hxc (by simp) hne
    -- the other firm also names `c`
    obtain ⟨k, hk⟩ : ∃ k, k ≠ j := ⟨j + 1, by fin_cases j <;> decide⟩
    have hall : ∀ l, l = j ∨ l = k := by
      intro l; fin_cases j <;> fin_cases k <;> fin_cases l <;> simp_all
    have hpk : p k = c := by
      by_contra hne'
      have hgt : c < p k := lt_of_le_of_ne (hj ▸ hjmin k) (Ne.symm hne')
      obtain ⟨p', hp'c, hp'k, hgain⟩ := bertrand_deviation hx hxc hgt
      have hdev := hne j p'
      change bertrandProfit x c (update p j p') j ≤ bertrandProfit x c p j at hdev
      have hlow : ∀ l, l ≠ j → (update p j p') j < (update p j p') l := by
        intro l hl
        rcases hall l with rfl | rfl
        · exact absurd rfl hl
        · simp [update_of_ne hl, hp'k]
      have hval : bertrandProfit x c (update p j p') j = (p' - c) * x p' := by
        unfold bertrandProfit; rw [bertrandSales_of_lt hlow]; simp
      have h0 : bertrandProfit x c p j = 0 := by simp [bertrandProfit, hj]
      have : 0 ≤ (p k - c) * x (p k) / 2 :=
        div_nonneg (mul_nonneg (by linarith) (hx.nonneg _)) (by norm_num)
      linarith
    funext l
    rcases hall l with rfl | rfl
    · exact hj
    · exact hpk

/-! ### Exercise 12.C.3: prices on a grid -/

/-- The smallest multiple of `Δ` strictly greater than `c`: `(⌊c/Δ⌋ + 1)Δ`. -/
noncomputable def gridPrice (Δ c : ℝ) : ℝ := (⌊c / Δ⌋ + 1) * Δ

theorem gridPrice_spec {Δ c : ℝ} (hΔ : 0 < Δ) : c < gridPrice Δ c ∧ gridPrice Δ c ≤ c + Δ ∧
    gridPrice Δ c - Δ ≤ c := by
  unfold gridPrice
  have h1 := Int.lt_floor_add_one (c / Δ)
  have h2 := Int.floor_le (c / Δ)
  rw [div_lt_iff₀ hΔ] at h1
  rw [le_div_iff₀ hΔ] at h2
  refine ⟨by linarith, by linarith, by linarith⟩

/-- The Bertrand duopoly with prices restricted to the multiples `nΔ`, `n ∈ ℤ`
(MWG, Exercise 12.C.3, p. 430). -/
noncomputable def gridBertrandGame (x : ℝ → ℝ) (c Δ : ℝ) : NormalForm (Fin 2) (fun _ => ℤ) where
  payoff j n := bertrandProfit x c (fun k => (n k : ℝ) * Δ) j

/-- **Exercise 12.C.3(a)** (MWG, p. 430). With prices on the grid `Δℤ`, both firms naming
`p̂ = (⌊c/Δ⌋ + 1)Δ`, the smallest multiple of `Δ` above `c`, is a pure strategy Nash
equilibrium. If `x(p̂) > 0`, this strategy is not weakly dominated: against any other grid price
`n'Δ` some rival price makes `p̂` strictly better. -/
theorem exercise_12_C_3a {x : ℝ → ℝ} {pbar c Δ : ℝ} (hx : IsBertrandDemand x pbar)
    (hΔ : 0 < Δ) :
    IsNashEquilibrium (gridBertrandGame x c Δ) (fun _ => ⌊c / Δ⌋ + 1) ∧
    (0 < x (gridPrice Δ c) → ∀ n' : ℤ, n' ≠ ⌊c / Δ⌋ + 1 → ∃ r : ℤ,
      bertrandProfit x c (fun k : Fin 2 => ((if k = 0 then n' else r : ℤ) : ℝ) * Δ) 0 <
      bertrandProfit x c
        (fun k : Fin 2 => ((if k = 0 then ⌊c / Δ⌋ + 1 else r : ℤ) : ℝ) * Δ) 0) := by
  obtain ⟨hgt, -, hle⟩ := gridPrice_spec (c := c) hΔ
  set N : ℤ := ⌊c / Δ⌋ + 1 with hN
  have hNΔ : (N : ℝ) * Δ = gridPrice Δ c := by rw [hN, gridPrice]; push_cast; ring
  constructor
  · intro j t
    change bertrandProfit x c (fun k => ((update (fun _ => N) j t k : ℤ) : ℝ) * Δ) j ≤
      bertrandProfit x c (fun k => ((N : ℤ) : ℝ) * Δ) j
    obtain ⟨k, hk⟩ : ∃ k, k ≠ j := ⟨j + 1, by fin_cases j <;> decide⟩
    have hr : bertrandProfit x c (fun _ : Fin 2 => (N : ℝ) * Δ) j =
        ((N : ℝ) * Δ - c) * (x ((N : ℝ) * Δ) / 2) := by
      unfold bertrandProfit; congr 1
      unfold bertrandSales
      simp
    rw [hr]
    have hR : 0 ≤ ((N : ℝ) * Δ - c) * (x ((N : ℝ) * Δ) / 2) :=
      mul_nonneg (by rw [hNΔ]; linarith) (div_nonneg (hx.nonneg _) (by norm_num))
    rcases lt_trichotomy t N with h | h | h
    · -- a lower grid price is at most `c`
      have ht : (t : ℝ) * Δ ≤ c := by
        have : (t : ℝ) ≤ N - 1 := by exact_mod_cast Int.le_sub_one_of_lt h
        have := mul_le_mul_of_nonneg_right this hΔ.le
        rw [hNΔ.symm] at hle
        nlinarith
      exact (bertrandProfit_le_zero hx.nonneg (by simpa using ht)).trans hR
    · have hu : update (fun _ : Fin 2 => N) j t = fun _ => N := by
        funext l; by_cases hl : l = j <;> simp [hl, h]
      rw [hu, ← hr]
    · have ht : (N : ℝ) * Δ < (t : ℝ) * Δ := by
        have : (N : ℝ) < t := by exact_mod_cast h
        nlinarith
      unfold bertrandProfit
      rw [bertrandSales_of_gt (k := k) (by simpa [update_of_ne hk] using ht), mul_zero]
      exact hR
  · intro hxp n' hn'
    rcases lt_or_gt_of_ne hn' with h | h
    · -- `n'Δ ≤ c`: against `p̂`, the price `p̂` earns half the positive profit
      refine ⟨N, ?_⟩
      have hl : bertrandProfit x c (fun k : Fin 2 => ((if k = 0 then n' else N : ℤ) : ℝ) * Δ) 0
          ≤ 0 := by
        apply bertrandProfit_le_zero hx.nonneg
        have : (n' : ℝ) ≤ N - 1 := by exact_mod_cast Int.le_sub_one_of_lt h
        have := mul_le_mul_of_nonneg_right this hΔ.le
        rw [hNΔ.symm] at hle
        simp only [ite_true]
        nlinarith
      have hr : bertrandProfit x c (fun k : Fin 2 => ((if k = 0 then N else N : ℤ) : ℝ) * Δ) 0 =
          (gridPrice Δ c - c) * (x (gridPrice Δ c) / 2) := by
        unfold bertrandProfit bertrandSales
        simp [hNΔ]
      have : 0 < (gridPrice Δ c - c) * (x (gridPrice Δ c) / 2) :=
        mul_pos (by linarith) (by positivity)
      linarith
    · -- `n'Δ > p̂`: against `p̂`, the higher price sells nothing
      refine ⟨N, ?_⟩
      have hl : bertrandProfit x c (fun k : Fin 2 => ((if k = 0 then n' else N : ℤ) : ℝ) * Δ) 0
          = 0 := by
        unfold bertrandProfit
        rw [bertrandSales_of_gt (k := 1)]
        · ring
        · simp only [ite_true, one_ne_zero, ite_false]
          have : (N : ℝ) < n' := by exact_mod_cast h
          nlinarith
      have hr : bertrandProfit x c (fun k : Fin 2 => ((if k = 0 then N else N : ℤ) : ℝ) * Δ) 0 =
          (gridPrice Δ c - c) * (x (gridPrice Δ c) / 2) := by
        unfold bertrandProfit bertrandSales
        simp [hNΔ]
      have : 0 < (gridPrice Δ c - c) * (x (gridPrice Δ c) / 2) :=
        mul_pos (by linarith) (by positivity)
      linarith

/-- **Exercise 12.C.3(b)** (MWG, p. 430). As `Δ → 0` the equilibrium price `p̂ ∈ (c, c + Δ]`
converges to `c`. -/
theorem exercise_12_C_3b (c : ℝ) :
    Filter.Tendsto (fun Δ => gridPrice Δ c) (nhdsWithin 0 (Set.Ioi 0)) (nhds c) := by
  have h1 : Filter.Tendsto (fun Δ : ℝ => c + Δ) (nhdsWithin 0 (Set.Ioi 0)) (nhds c) := by
    have := (tendsto_const_nhds (x := c) (f := nhdsWithin (0 : ℝ) (Set.Ioi 0))).add
      (tendsto_nhdsWithin_of_tendsto_nhds (s := Set.Ioi (0 : ℝ))
        (Filter.tendsto_id (x := nhds (0 : ℝ))))
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h1 ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with Δ hΔ using (gridPrice_spec hΔ).1.le
  · filter_upwards [self_mem_nhdsWithin] with Δ hΔ using (gridPrice_spec hΔ).2.1

end MWG.MarketPower
