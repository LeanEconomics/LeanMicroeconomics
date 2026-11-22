/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGSimultaneousMoveGames.Dominance
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# The Groves-Clarke mechanism (MWG Section 11.E, pp. 373-374; Exercises 11.E.3-11.E.6)

The revelation mechanism of p. 373 for the two-level externality: the firm (player `0`) announces
`b̂`, the consumer (player `1`) announces `ĉ`; `h = h̄` iff `b̂ > ĉ`, and then the firm pays `ĉ` and
the consumer receives `b̂`. We add the arbitrary payments of **Exercise 11.E.4**: the firm receives
`τ_f(ĉ)` and the consumer `τ_c(b̂)`. Strategic form and dominance are Chapter 8's
(`MWG.NoncooperativeGames.NormalForm`, `MWG.SimultaneousMoveGames.WeaklyDominant`,
Definition 8.B.3).

* Truth-telling is a weakly dominant strategy for both agents, whatever `τ_f, τ_c`
  (`gc_consumer_truth`, `gc_firm_truth`; Exercise 11.E.4: `exercise_11_E_4`), and the outcome is
  optimal for every `(b, c)` (`gc_optimal`).
* **Exercise 11.E.3**: truth-telling is the consumer's only weakly dominant strategy
  (`exercise_11_E_3`, via `weaklyDominant_unique`).
* Small type, p. 374: the government's deficit is `b - c` when `b > c` (`gc_deficit`), and no
  choice of the Exercise 11.E.4 payments balances the budget for every `(b, c)`
  (`gc_no_budget_balance`); eliminating the deficit everywhere creates a surplus somewhere.
* **Exercise 11.E.5**: the Groves-Clarke mechanism for a public project (truth weakly dominant,
  efficient decision) and expected budget balance by a lump-sum adjustment
  (`exercise_11_E_5_truth`, `exercise_11_E_5_strict`, `exercise_11_E_5_balance`).
* **Exercise 11.E.6**: `N` projects (any finite set of alternatives) (`exercise_11_E_6`).
-/

namespace MWG.ExternalitiesPublicGoods

open MWG.NoncooperativeGames MWG.SimultaneousMoveGames Function

/-! ## The two-agent mechanism -/

/-- The Groves-Clarke revelation game for true types `(b, c)` (MWG, p. 373), with the extra
payments `τ_f(ĉ)` to the firm and `τ_c(b̂)` to the consumer of Exercise 11.E.4. Player `0` is the
firm, player `1` the consumer; strategies are announcements in `ℝ`. -/
noncomputable def gcGame (b c : ℝ) (τf τc : ℝ → ℝ) : NormalForm (Fin 2) (fun _ => ℝ) where
  payoff i s := if i = 0 then (if s 1 < s 0 then b - s 1 else 0) + τf (s 1)
    else (if s 1 < s 0 then s 0 - c else 0) + τc (s 0)

theorem gc_payoff_consumer (b c : ℝ) (τf τc : ℝ → ℝ) (r : Fin 2 → ℝ) (x : ℝ) :
    (gcGame b c τf τc).payoff 1 (update r 1 x) =
      (if x < r 0 then r 0 - c else 0) + τc (r 0) := by
  simp [gcGame]

theorem gc_payoff_firm (b c : ℝ) (τf τc : ℝ → ℝ) (r : Fin 2 → ℝ) (x : ℝ) :
    (gcGame b c τf τc).payoff 0 (update r 0 x) =
      (if r 1 < x then b - r 1 else 0) + τf (r 1) := by
  simp [gcGame]

/-- **Truth-telling is weakly dominant for the consumer** (MWG, pp. 373-374; Definition 8.B.3):
announcing `ĉ = c` is at least as good as any other announcement against every `b̂`, and
strictly better against some. -/
theorem gc_consumer_truth (b c : ℝ) (τf τc : ℝ → ℝ) : WeaklyDominant (gcGame b c τf τc) 1 c := by
  intro x hx
  refine ⟨fun r => ?_, ?_⟩
  · rw [gc_payoff_consumer, gc_payoff_consumer]
    split_ifs with h1 h2 h2 <;> linarith
  · rcases lt_or_gt_of_ne hx with hlt | hgt
    · refine ⟨fun _ => (x + c) / 2, ?_⟩
      rw [gc_payoff_consumer, gc_payoff_consumer]
      have h1 : x < (x + c) / 2 := by linarith
      have h2 : ¬ c < (x + c) / 2 := by linarith
      simp only [h1, h2, ↓reduceIte]
      linarith
    · refine ⟨fun _ => (x + c) / 2, ?_⟩
      rw [gc_payoff_consumer, gc_payoff_consumer]
      have h1 : ¬ x < (x + c) / 2 := by linarith
      have h2 : c < (x + c) / 2 := by linarith
      simp only [h1, h2, ↓reduceIte]
      linarith

/-- **Truth-telling is weakly dominant for the firm** (MWG, p. 374: "a parallel analysis"). -/
theorem gc_firm_truth (b c : ℝ) (τf τc : ℝ → ℝ) : WeaklyDominant (gcGame b c τf τc) 0 b := by
  intro x hx
  refine ⟨fun r => ?_, ?_⟩
  · rw [gc_payoff_firm, gc_payoff_firm]
    split_ifs with h1 h2 h2 <;> linarith
  · rcases lt_or_gt_of_ne hx with hlt | hgt
    · refine ⟨fun _ => (x + b) / 2, ?_⟩
      rw [gc_payoff_firm, gc_payoff_firm]
      have h1 : ¬ (x + b) / 2 < x := by linarith
      have h2 : (x + b) / 2 < b := by linarith
      simp only [h1, h2, ↓reduceIte]
      linarith
    · refine ⟨fun _ => (x + b) / 2, ?_⟩
      rw [gc_payoff_firm, gc_payoff_firm]
      have h1 : (x + b) / 2 < x := by linarith
      have h2 : ¬ (x + b) / 2 < b := by linarith
      simp only [h1, h2, ↓reduceIte]
      linarith

/-- **Exercise 11.E.4** (MWG, p. 374). Adding to each agent a payment depending arbitrarily on the
other's announcement affects neither truth-telling nor the outcome: for all `τ_f, τ_c`, truth is
weakly dominant for both agents and the externality is allowed iff `b > c`. -/
theorem exercise_11_E_4 (b c : ℝ) (τf τc : ℝ → ℝ) :
    WeaklyDominant (gcGame b c τf τc) 0 b ∧ WeaklyDominant (gcGame b c τf τc) 1 c :=
  ⟨gc_firm_truth b c τf τc, gc_consumer_truth b c τf τc⟩

/-- **Optimality** (MWG, p. 373): under truthful announcements the externality is allowed iff
`b > c`, which maximizes aggregate surplus `(b - c)·1[h = h̄]` for every `(b, c)`. -/
theorem gc_optimal (b c : ℝ) :
    (if c < b then b - c else 0) = max (b - c) 0 := by
  split_ifs with h
  · rw [max_eq_left (by linarith)]
  · rw [max_eq_right (by linarith)]

/-- In any game a player has at most one weakly dominant strategy. -/
theorem weaklyDominant_unique {I : Type*} [DecidableEq I] {S : I → Type*} (N : NormalForm I S)
    (i : I) {s s' : S i} (hs : WeaklyDominant N i s) (hs' : WeaklyDominant N i s') : s = s' := by
  by_contra hne
  obtain ⟨-, r, hr⟩ := hs s' (Ne.symm hne)
  have := (hs' s hne).1 r
  linarith

/-- **Exercise 11.E.3** (MWG, p. 381). Truth-telling is the consumer's only weakly dominant
strategy in the Groves-Clarke mechanism. -/
theorem exercise_11_E_3 (b c : ℝ) (τf τc : ℝ → ℝ) (x : ℝ)
    (hx : WeaklyDominant (gcGame b c τf τc) 1 x) : x = c :=
  weaklyDominant_unique _ 1 hx (gc_consumer_truth b c τf τc)

/-- The government's net revenue at announcements `(b̂, ĉ)`: it collects `ĉ` from the firm and pays
`b̂` to the consumer when `h = h̄`, and pays the Exercise 11.E.4 payments. -/
noncomputable def gcRevenue (τf τc : ℝ → ℝ) (bh ch : ℝ) : ℝ :=
  (if ch < bh then ch - bh else 0) - τf ch - τc bh

/-- **The deficit** (MWG, small type, p. 374): without extra payments, the government's deficit
under truth-telling is `b - c` whenever `b > c`. -/
theorem gc_deficit {b c : ℝ} (h : c < b) : -gcRevenue (fun _ => 0) (fun _ => 0) b c = b - c := by
  simp [gcRevenue, h]

/-- **No budget balance** (MWG, small type, p. 374). No payments `τ_f, τ_c` of the Exercise 11.E.4
form balance the budget for every `(b, c)` with `b, c > 0`. -/
theorem gc_no_budget_balance (τf τc : ℝ → ℝ) :
    ¬ ∀ b c : ℝ, 0 < b → 0 < c → gcRevenue τf τc b c = 0 := by
  intro hbal
  have h1 := hbal 1 2 one_pos two_pos
  have h2 := hbal 1 3 one_pos (by norm_num)
  have h3 := hbal 3 2 (by norm_num) two_pos
  have h4 := hbal 3 3 (by norm_num) (by norm_num)
  simp only [gcRevenue] at h1 h2 h3 h4
  norm_num at h1 h2 h3 h4
  linarith

/-- **A surplus somewhere** (MWG, small type, p. 374): if the payments eliminate the deficit for
all `(b, c)`, the government runs a strict surplus for some `(b, c)`, so some numeraire is not
left with the agents (a Pareto inefficient outcome). -/
theorem gc_surplus_somewhere (τf τc : ℝ → ℝ)
    (hnd : ∀ b c : ℝ, 0 < b → 0 < c → 0 ≤ gcRevenue τf τc b c) :
    ∃ b c : ℝ, 0 < b ∧ 0 < c ∧ 0 < gcRevenue τf τc b c := by
  by_contra hno
  push Not at hno
  exact gc_no_budget_balance τf τc fun b c hb hc => le_antisymm (hno b c hb hc) (hnd b c hb hc)

/-! ## Exercise 11.E.5: a public project -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Exercise 11.E.5** (MWG, p. 381). The Groves-Clarke mechanism for a public project of cost
`K`: given announcements `b̂`, build iff `∑ b̂ᵢ ≥ K`; if built, individual `i` receives
`∑_{j ≠ i} b̂ⱼ - K`, and in any case `hᵢ(b̂₋ᵢ)` (any function of the others' announcements; the
`i`-th coordinate of its argument is ignored). Payoffs for true benefits `b`. -/
noncomputable def projGame (K : ℝ) (b : ι → ℝ) (hh : ι → (ι → ℝ) → ℝ) :
    NormalForm ι (fun _ => ℝ) where
  payoff i s := (if K ≤ ∑ j, s j then b i + (∑ j, s j - s i) - K else 0) + hh i (update s i 0)

theorem proj_payoff (K : ℝ) (b : ι → ℝ) (hh : ι → (ι → ℝ) → ℝ) (i : ι) (r : ι → ℝ) (x : ℝ) :
    (projGame K b hh).payoff i (update r i x) =
      (if K ≤ x + (∑ j, r j - r i) then b i + (∑ j, r j - r i) - K else 0) +
        hh i (update r i 0) := by
  have hs : ∑ j, update r i x j = x + (∑ j, r j - r i) := by
    rw [Finset.sum_update_of_mem (Finset.mem_univ i), ← Finset.add_sum_erase _ _
      (Finset.mem_univ i)]
    simp only [Finset.sdiff_singleton_eq_erase]
    ring
  simp only [projGame, hs, update_self, update_idem]
  congr 2
  ring

/-- **Exercise 11.E.5**: truth-telling is a dominant strategy (at least as good as any other
announcement whatever the others announce). -/
theorem exercise_11_E_5_truth (K : ℝ) (b : ι → ℝ) (hh : ι → (ι → ℝ) → ℝ) (i : ι) (r : ι → ℝ)
    (x : ℝ) : (projGame K b hh).payoff i (update r i x) ≤
      (projGame K b hh).payoff i (update r i (b i)) := by
  rw [proj_payoff, proj_payoff]
  split_ifs with h1 h2 h2 <;> linarith

/-- **Exercise 11.E.5**: with at least two individuals, truth-telling is weakly dominant in the
sense of Definition 8.B.3 (strictly better than each other announcement against some
announcements of the others). -/
theorem exercise_11_E_5_strict (K : ℝ) (b : ι → ℝ) (hh : ι → (ι → ℝ) → ℝ) (i : ι)
    (hI : ∃ j, j ≠ i) : WeaklyDominant (projGame K b hh) i (b i) := by
  obtain ⟨j, hj⟩ := hI
  intro x hx
  refine ⟨fun r => exercise_11_E_5_truth K b hh i r x, ?_⟩
  -- the others announce a total `K - (x + b i)/2`, carried by `j`
  set R := K - (x + b i) / 2
  refine ⟨update (fun _ => (0 : ℝ)) j R, ?_⟩
  have hR : ∑ k, update (fun _ => (0 : ℝ)) j R k - update (fun _ => (0 : ℝ)) j R i = R := by
    simp [Finset.sum_update_of_mem, update_of_ne hj.symm]
  rw [proj_payoff, proj_payoff, hR]
  rcases lt_or_gt_of_ne hx with hlt | hgt
  · have h1 : ¬ K ≤ x + R := by simp only [R]; linarith
    have h2 : K ≤ b i + R := by simp only [R]; linarith
    simp only [h1, h2, ↓reduceIte]
    simp only [R]
    linarith
  · have h1 : K ≤ x + R := by simp only [R]; linarith
    have h2 : ¬ K ≤ b i + R := by simp only [R]; linarith
    simp only [h1, h2, ↓reduceIte]
    simp only [R]
    linarith

omit [DecidableEq ι] in
/-- **Exercise 11.E.5**: under truth-telling the project is built iff `∑ bᵢ ≥ K`, which maximizes
aggregate surplus `(∑ bᵢ - K)·1[build]`. -/
theorem exercise_11_E_5_efficient (K : ℝ) (b : ι → ℝ) :
    (if K ≤ ∑ j, b j then ∑ j, b j - K else 0) = max (∑ j, b j - K) 0 := by
  split_ifs with h
  · rw [max_eq_left (by linarith)]
  · rw [max_eq_right (by linarith)]

/-- The government's budget under truthful announcements with `hᵢ = kᵢ` constants: it pays `K` if
the project is built, and the transfers. -/
noncomputable def projBudget (K : ℝ) (k : ι → ℝ) (b : ι → ℝ) : ℝ :=
  -(if K ≤ ∑ j, b j then K + ∑ i, (∑ j, b j - b i - K) else 0) - ∑ i, k i

omit [DecidableEq ι] in
open MeasureTheory in
/-- **Exercise 11.E.5: budget balance on average** (MWG, p. 381). For any probability
distribution `μ` of the benefit profiles under which the budget is integrable, lump-sum payments
`hᵢ = kᵢ` (which preserve truth-telling, `exercise_11_E_5_truth`) can be chosen so that the
government balances its budget in expectation. -/
theorem exercise_11_E_5_balance [MeasurableSpace (ι → ℝ)] (K : ℝ) (μ : Measure (ι → ℝ))
    [IsProbabilityMeasure μ] (i₀ : ι) (hint : Integrable (projBudget K (fun _ => 0)) μ) :
    ∃ k : ι → ℝ, ∫ b, projBudget K k b ∂μ = 0 := by
  classical
  refine ⟨Pi.single i₀ (∫ b, projBudget K (fun _ => 0) b ∂μ), ?_⟩
  have hk : ∀ b, projBudget K (Pi.single i₀ (∫ b, projBudget K (fun _ => 0) b ∂μ)) b =
      projBudget K (fun _ => 0) b - ∫ b, projBudget K (fun _ => 0) b ∂μ := fun b => by
    simp [projBudget]
  simp_rw [hk]
  rw [integral_sub hint (integrable_const _), integral_const, probReal_univ, one_smul, sub_self]

/-! ## Exercise 11.E.6: `N` projects -/

/-- **Exercise 11.E.6** (MWG, p. 381). With a finite set of alternatives `X` (the `N` projects,
costs `K(x)`), individual `i` announces a benefit function `b̂ᵢ : X → ℝ`; the mechanism chooses an
alternative `x*(b̂)` maximizing `∑ b̂ᵢ(x) - K(x)` (`hsel`) and pays `i` the amount
`∑_{j ≠ i} b̂ⱼ(x*) - K(x*) + hᵢ(b̂₋ᵢ)`. Truth-telling is a dominant strategy. -/
theorem exercise_11_E_6 {X : Type*} (K : X → ℝ) (sel : (ι → X → ℝ) → X)
    (hsel : ∀ bh : ι → X → ℝ, ∀ y, ∑ j, bh j y - K y ≤ ∑ j, bh j (sel bh) - K (sel bh))
    (hh : ι → (ι → X → ℝ) → ℝ) (b : ι → X → ℝ) (i : ι) (r : ι → X → ℝ) (x : X → ℝ) :
    let pay : (ι → X → ℝ) → ℝ := fun s =>
      b i (sel s) + (∑ j, s j (sel s) - s i (sel s)) - K (sel s) + hh i (update s i 0)
    pay (update r i x) ≤ pay (update r i (b i)) := by
  intro pay
  have hsum : ∀ (z : X → ℝ) (y : X), ∑ j, update r i z j y = z y + (∑ j, r j y - r i y) :=
    fun z y => by
      have : ∀ j, update r i z j y = update (fun j => r j y) i (z y) j := fun j => by
        rcases eq_or_ne j i with h | h
        · subst h; simp
        · simp [update_of_ne h]
      simp_rw [this]
      rw [Finset.sum_update_of_mem (Finset.mem_univ i), ← Finset.add_sum_erase _ _
        (Finset.mem_univ i)]
      simp only [Finset.sdiff_singleton_eq_erase]
      ring
  simp only [pay, update_self, update_idem]
  have key := hsel (update r i (b i)) (sel (update r i x))
  rw [hsum, hsum] at key
  rw [hsum, hsum]
  linarith

omit [Fintype ι] [DecidableEq ι] in
/-- A selection rule as required in `exercise_11_E_6` exists for any finite nonempty set of
alternatives. -/
theorem exercise_11_E_6_selector {X : Type*} [Finite X] [Nonempty X] (K : X → ℝ)
    [Fintype ι] : ∃ sel : (ι → X → ℝ) → X,
      ∀ bh : ι → X → ℝ, ∀ y, ∑ j, bh j y - K y ≤ ∑ j, bh j (sel bh) - K (sel bh) := by
  have := Fintype.ofFinite X
  refine ⟨fun bh => (Finset.univ.exists_max_image (fun y => ∑ j, bh j y - K y)
    Finset.univ_nonempty).choose, fun bh y => ?_⟩
  exact (Finset.univ.exists_max_image (fun y => ∑ j, bh j y - K y)
    Finset.univ_nonempty).choose_spec.2 y (Finset.mem_univ y)

open MeasureTheory in
/-- An instance of `exercise_11_E_5_balance`: the point mass at a benefit profile (any budget is
integrable for it). -/
theorem exercise_11_E_5_balance_instance (K : ℝ) (b₀ : Fin 2 → ℝ) :
    ∃ k : Fin 2 → ℝ, ∫ b, projBudget K k b ∂(Measure.dirac b₀) = 0 :=
  exercise_11_E_5_balance K (Measure.dirac b₀) 0
    ((integrable_const _).congr (ae_eq_dirac _).symm)

end MWG.ExternalitiesPublicGoods
