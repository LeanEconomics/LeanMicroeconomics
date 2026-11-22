/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGCoreFoundations.CoreWalras
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# The limits to redistribution (MWG Section 18.D, pp. 665-670)

The exchange economy of Section 18.D is a `CoreEconomy` (preferences `≿ᵢ` on `ℝ^L₊`,
endowments `ωᵢ`; feasibility with the technology `Y`, `Y = -ℝ^L₊` in the exchange case).

* **Definition 18.D.1** (`CoreEconomy.IsSelfSelectiveWith`, `CoreEconomy.IsSelfSelective`,
  `definition_18_D_1`).
* p. 666, corrected (`selfSelective_iff_netTrades`): a feasible allocation is self-selective iff
  it is self-selective with `B = {z*₁, ..., z*_I}` (the net trades) iff no consumer envies another
  consumer's net trade (`CoreEconomy.NoEnvyNetTrades`). The printed `B = {x*₁, ..., x*_I}` is a
  misprint: `selfSelective_consumptions_misprint`.
* p. 667 (`walras_isParetoOptimal_selfSelective`): with rational monotone preferences a
  Walrasian allocation with prices `p` is Pareto optimal (Proposition 16.C.1 through the
  Chapter 16 bridges) and self-selective with `B = {z : p·z = 0}` (budgets bind by
  monotonicity), and also with `B = {z : p·z ≤ 0}`.
* **Figures 18.D.2 and 18.D.3** (`figure_18_D_2`): with `u = √x₁ + √x₂`, `ω₁ = (9/2, 17)`,
  `ω₂ = (41/2, 8)`, the allocation `x*₁ = (9, 9)`, `x*₂ = (16, 16)` is Pareto optimal,
  self-selective and not Walrasian.
* **Exercise 18.D.1** (`exercise_18_D_1`, key step `pref_add_of_pref_endow`): in an Edgeworth
  box with rational strictly convex preferences, every feasible allocation weakly preferred by
  both consumers to their endowments is self-selective with `B = {z*₁, -z*₁}` (continuity and
  monotonicity are not needed).
* **Proposition 18.D.1** (p. 669), the parts that can be made rigorous: the equal-treatment step
  (`proposition_18_D_1_supported_eq`, `proposition_18_D_1_equal_treatment`), the single net
  trade step (`proposition_18_D_1_single_net_trade`), and a corrected main claim for a smooth
  continuum of types `t ∈ [0, 1]` (`proposition_18_D_1_smooth`, `proposition_18_D_1_walrasian`)
  under the regularity the book's proof assumes informally (net trades `z t` continuous on
  `[0, 1]` and differentiable inside, interior bundles, differentiable utilities with gradients
  proportional to the supporting price `p`, no envy among all types, and `0` a convex
  combination of net trades present), with a concrete instance
  (`proposition_18_D_1_instance`). A continuum form with a population measure, in which the
  continuity of `z(t)` is derived, is in `Closer18D` (`proposition_18_D_1_continuum`).

Verbal or graphical: Figure 18.D.1, footnotes 15-19, Figures 18.D.4-18.D.6 (Figure 18.D.4 is a
continuum example with kinked preferences; its finite counterpart is `figure_18_D_2`), and the
discussion of pp. 665-669.
-/

namespace MWG.CoreFoundations

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.Production MWG.WelfareTheorems
open Kreps.PreferenceProperties

variable {ι : Type*} {L : ℕ}

/-! ### Definition 18.D.1 -/

/-- **Definition 18.D.1** (MWG, p. 666). The allocation `x*` is self-selective with the
generalized budget set (tax system) `B ⊆ ℝ^L`: for every consumer `i`, the net trade
`z*ᵢ = x*ᵢ - ωᵢ` solves `max uᵢ(zᵢ + ωᵢ)` subject to `zᵢ ∈ B`, `zᵢ + ωᵢ ≥ 0`. -/
def CoreEconomy.IsSelfSelectiveWith (E : CoreEconomy ι L) (x : ι → Fin L → ℝ)
    (B : Set (Fin L → ℝ)) : Prop :=
  ∀ i, x i - E.ω i ∈ B ∧ ∀ z ∈ B, z + E.ω i ∈ nonnegOrthant L → E.pref i (x i) (z + E.ω i)

/-- **Definition 18.D.1** (MWG, p. 666). A feasible allocation is self-selective (anonymous,
envy-free in net trades) if it is self-selective with some generalized budget set `B`. -/
def CoreEconomy.IsSelfSelective [Fintype ι] (E : CoreEconomy ι L) (x : ι → Fin L → ℝ) :
    Prop :=
  E.IsFeasible x ∧ ∃ B, E.IsSelfSelectiveWith x B

/-- No consumer envies the net trade of another (whenever that net trade is feasible for her):
`x*ᵢ ≿ᵢ ωᵢ + z*ₖ` for all `i, k` with `ωᵢ + z*ₖ ≥ 0`. -/
def CoreEconomy.NoEnvyNetTrades (E : CoreEconomy ι L) (x : ι → Fin L → ℝ) : Prop :=
  ∀ i k, x k - E.ω k + E.ω i ∈ nonnegOrthant L → E.pref i (x i) (x k - E.ω k + E.ω i)

/-- **Definition 18.D.1** (MWG, p. 666), restated: `z*ᵢ + ωᵢ = x*ᵢ` is maximal for `≿ᵢ` among the
bundles `z + ωᵢ ≥ 0` with `z ∈ B`. -/
theorem definition_18_D_1 (E : CoreEconomy ι L) (x : ι → Fin L → ℝ) (B : Set (Fin L → ℝ))
    (hx : ∀ i, x i ∈ nonnegOrthant L) :
    E.IsSelfSelectiveWith x B ↔
      ∀ i, IsMaximalFor (E.pref i) {y | y ∈ nonnegOrthant L ∧ y - E.ω i ∈ B} (x i) := by
  constructor
  · intro h i
    refine ⟨⟨hx i, (h i).1⟩, fun y ⟨hy, hyB⟩ => ?_⟩
    have := (h i).2 _ hyB (by rwa [sub_add_cancel])
    rwa [sub_add_cancel] at this
  · intro h i
    refine ⟨(h i).1.2, fun z hz hzω => (h i).2 _ ⟨hzω, by rwa [add_sub_cancel_right]⟩⟩

/-- **Section 18.D** (MWG, p. 666), corrected. For a feasible allocation, being self-selective
is equivalent to being self-selective with `B = {z*₁, ..., z*_I}`, the set of the equilibrium
net trades, and to no consumer envying the net trade of another. (The book prints
`B = {x*₁, ..., x*_I}`; see `selfSelective_consumptions_misprint`.) -/
theorem selfSelective_iff_netTrades [Fintype ι] (E : CoreEconomy ι L) (x : ι → Fin L → ℝ)
    (hfe : E.IsFeasible x) :
    (E.IsSelfSelective x ↔ E.IsSelfSelectiveWith x (Set.range fun k => x k - E.ω k)) ∧
      (E.IsSelfSelective x ↔ E.NoEnvyNetTrades x) := by
  have h1 : E.IsSelfSelective x → E.NoEnvyNetTrades x := by
    rintro ⟨-, B, hB⟩ i k hik
    exact (hB i).2 _ (hB k).1 hik
  have h2 : E.NoEnvyNetTrades x → E.IsSelfSelectiveWith x (Set.range fun k => x k - E.ω k) := by
    intro h i
    refine ⟨⟨i, rfl⟩, ?_⟩
    rintro z ⟨k, rfl⟩ hz
    exact h i k hz
  have h3 : E.IsSelfSelectiveWith x (Set.range fun k => x k - E.ω k) → E.IsSelfSelective x :=
    fun h => ⟨hfe, _, h⟩
  exact ⟨⟨fun h => h2 (h1 h), h3⟩, ⟨h1, fun h => h3 (h2 h)⟩⟩

/-- The economy of the misprint counterexample: two consumers with utility `√x₁ + √x₂` and
endowments `(1, 1)`. -/
noncomputable def misprintEconomy : CoreEconomy (Fin 2) 2 := sqrtEconomy fun _ => ![1, 1]

/-- **Section 18.D** (MWG, p. 666), the misprint. "It is enough to take `B = {x*₁, ..., x*_I}`"
is false as printed: the no-trade allocation `x* = ω = ((1, 1), (1, 1))` of `misprintEconomy`
is self-selective (with `B = {0}`), but not with `B = {x*₁, x*₂} = {(1, 1)}`, which does not
contain the net trades `z*ᵢ = 0`. The set to take is the set of net trades
(`selfSelective_iff_netTrades`). -/
theorem selfSelective_consumptions_misprint :
    misprintEconomy.IsSelfSelective (fun _ => ![1, 1]) ∧
      ¬ misprintEconomy.IsSelfSelectiveWith (fun _ => ![1, 1])
        (Set.range fun _ : Fin 2 => (![1, 1] : Fin 2 → ℝ)) := by
  refine ⟨⟨⟨fun _ l => by fin_cases l <;> norm_num, 0, fun _ => le_rfl, by
    simp [misprintEconomy, sqrtEconomy]⟩, {0}, fun i => ⟨?_, ?_⟩⟩, ?_⟩
  · simp [misprintEconomy, sqrtEconomy]
  · rintro z rfl -
    simp [misprintEconomy, sqrtEconomy, utilityPref]
  · intro h
    obtain ⟨k, hk⟩ := (h 0).1
    have := congrFun hk 0
    simp [misprintEconomy, sqrtEconomy] at this

/-! ### Walrasian allocations (p. 667) -/

/-- **Section 18.D** (MWG, p. 667). A Walrasian allocation with price vector `p` of an economy
with rational, monotone preferences (Definition 3.B.2) and a constant returns technology (e.g.
the exchange case `Y = -ℝ^L₊`) is Pareto optimal (first welfare theorem, Proposition 16.C.1 via
the bridges of `CoreWalras`) and self-selective with `B = {z : p·z = 0}`, and also with
`B = {z : p·z ≤ 0}`: monotonicity makes every budget bind, `p·z*ᵢ = 0`. -/
theorem walras_isParetoOptimal_selfSelective [Fintype ι] [Nonempty ι] (E : CoreEconomy ι L)
    (hL : 0 < L) (hY : IsCRSTechnology E.Y)
    (hr : ∀ i, RationalOn (nonnegOrthant L) (E.pref i))
    (hm : ∀ i, PrefMonotone (nonnegOrthant L) (E.pref i)) {x : ι → Fin L → ℝ}
    {p : Fin L → ℝ} (h : E.IsWalrasEqm x p) :
    E.IsParetoOptimal x ∧ E.IsSelfSelectiveWith x {z | p ⬝ᵥ z = 0} ∧
      E.IsSelfSelectiveWith x {z | p ⬝ᵥ z ≤ 0} ∧ E.IsSelfSelective x := by
  have hlns : ∀ i, LocallyNonsatiated (nonnegOrthant L) (E.pref i) :=
    fun i => exercise_3_B_1b_orthant hL (hm i)
  -- Pareto optimality through Chapter 16
  set θ : ι → ℝ := fun _ => 1 / (Fintype.card ι : ℝ) with hθ
  obtain ⟨y, hy, hpriv⟩ := (isWalrasEqm_iff_toPriv E hY θ x p).mp h
  have hθ1 : ∀ j, ∑ i, (E.toPriv θ).θ i j = 1 := by
    intro j
    simp only [CoreEconomy.toPriv, hθ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
    field_simp
  have hpo := proposition_16_C_1_walras (E := E.toPriv θ) (fun i => hr i) (fun i => hlns i) hθ1
    hpriv
  have hPO : E.IsParetoOptimal x := (isParetoOptimal_iff_toPriv E θ x).mpr ⟨y, hpo⟩
  -- budgets bind
  have hbind : ∀ i, p ⬝ᵥ (x i - E.ω i) = 0 := by
    intro i
    have hxi := (h.2 i).1
    have hrefl : E.pref i (x i) (x i) := ((hr i).1 _ hxi.1 _ hxi.1).elim id id
    have hge := exercise_16_C_2 (hlns i) (hr i).2 (h.2 i) hxi.1 hrefl
    rw [dotProduct_sub]
    linarith [hxi.2]
  have hle : E.IsSelfSelectiveWith x {z | p ⬝ᵥ z ≤ 0} := by
    intro i
    refine ⟨le_of_eq (hbind i), fun z hz hzω => (h.2 i).2 _ ⟨hzω, ?_⟩⟩
    have : p ⬝ᵥ z ≤ 0 := hz
    rw [dotProduct_add]
    linarith
  refine ⟨hPO, fun i => ⟨hbind i, fun z hz hzω => (hle i).2 z (le_of_eq hz) hzω⟩, hle,
    hPO.1, _, hle⟩

/-! ### Figures 18.D.2 and 18.D.3: a Pareto optimal, self-selective, non-Walrasian allocation -/

/-- The endowments of the Edgeworth box of `figure_18_D_2`: `ω₁ = (9/2, 17)`, `ω₂ = (41/2, 8)`. -/
noncomputable def fig18D2Endow : Fin 2 → Fin 2 → ℝ := ![![9 / 2, 17], ![41 / 2, 8]]

/-- The allocation `x*₁ = (9, 9)`, `x*₂ = (16, 16)` of `figure_18_D_2`. -/
noncomputable def fig18D2Alloc : Fin 2 → Fin 2 → ℝ := fun i => ![![9, 16] i, ![9, 16] i]

/-- `√(n²) = n` for the small perfect squares used below. -/
theorem fig18D2_sqrt_sq {a : ℝ} (ha : 0 ≤ a) : Real.sqrt (a ^ 2) = a := Real.sqrt_sq ha

/-- **Figures 18.D.2 and 18.D.3** (MWG, p. 667). In the Edgeworth box with identical utilities
`√x₁ + √x₂` and endowments `ω₁ = (9/2, 17)`, `ω₂ = (41/2, 8)`, the allocation
`x*₁ = (9, 9)`, `x*₂ = (16, 16)` is Pareto optimal and self-selective (consumer 1 prefers her net
trade `z*₁` to `z*₂`: `ω₁ + z*₂ = (0, 25)` gives utility `5 < 6`; consumer 2 prefers `z*₂` to
`z*₁`: `ω₂ + z*₁ = (25, 0)` gives `5 < 8`), but it is not a Walrasian allocation for any price
vector (the budgets force `p₁ = 16p₂/9`, at which consumer 1 can afford `(81/16, 16)`, worth
`25/4 > 6`, or, if `p₂ ≤ 0`, `(10, 10)`). -/
theorem figure_18_D_2 :
    (sqrtEconomy fig18D2Endow).IsParetoOptimal fig18D2Alloc ∧
      (sqrtEconomy fig18D2Endow).IsSelfSelective fig18D2Alloc ∧
      ¬ (sqrtEconomy fig18D2Endow).IsWalrasAlloc fig18D2Alloc := by
  have hPO : (sqrtEconomy fig18D2Endow).IsParetoOptimal fig18D2Alloc :=
    sqrtEconomy_diag_isParetoOptimal (t := ![9, 16])
      (fun i => by fin_cases i <;> norm_num)
      (by simp [fig18D2Endow, Fin.sum_univ_two]; norm_num)
      (by simp [fig18D2Endow, Fin.sum_univ_two]; norm_num)
  have h3 : Real.sqrt 9 = 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num]
    exact fig18D2_sqrt_sq (by norm_num)
  have h4 : Real.sqrt 16 = 4 := by
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num]
    exact fig18D2_sqrt_sq (by norm_num)
  have h5 : Real.sqrt 25 = 5 := by
    rw [show (25 : ℝ) = 5 ^ 2 by norm_num]
    exact fig18D2_sqrt_sq (by norm_num)
  refine ⟨hPO, ?_, ?_⟩
  · refine ((selfSelective_iff_netTrades _ _ hPO.1).2).2 fun i k _ => ?_
    fin_cases i <;> fin_cases k
    · simp [sqrtEconomy, utilityPref]
    · change sqrtU (fig18D2Alloc 1 - fig18D2Endow 1 + fig18D2Endow 0) ≤ sqrtU (fig18D2Alloc 0)
      have e : fig18D2Alloc 1 - fig18D2Endow 1 + fig18D2Endow 0 = ![0, 25] := by
        funext l
        fin_cases l <;> simp [fig18D2Alloc, fig18D2Endow] <;> norm_num
      rw [e, sqrtU_two, sqrtU_two]
      simp [fig18D2Alloc, h3, h5]
      norm_num
    · change sqrtU (fig18D2Alloc 0 - fig18D2Endow 0 + fig18D2Endow 1) ≤ sqrtU (fig18D2Alloc 1)
      have e : fig18D2Alloc 0 - fig18D2Endow 0 + fig18D2Endow 1 = ![25, 0] := by
        funext l
        fin_cases l <;> simp [fig18D2Alloc, fig18D2Endow] <;> norm_num
      rw [e, sqrtU_two, sqrtU_two]
      simp [fig18D2Alloc, h4, h5]
      norm_num
    · simp [sqrtEconomy, utilityPref]
  · rintro ⟨p, -, hx⟩
    have b0 := (hx 0).1.2
    have b1 := (hx 1).1.2
    change p ⬝ᵥ ![9, 9] ≤ p ⬝ᵥ ![9 / 2, 17] at b0
    change p ⬝ᵥ ![16, 16] ≤ p ⬝ᵥ ![41 / 2, 8] at b1
    simp only [dot_two, Matrix.cons_val_zero, Matrix.cons_val_one] at b0 b1
    have hu : sqrtU (fig18D2Alloc 0) = 6 := by
      change sqrtU ![9, 9] = 6
      rw [sqrtU_vec, h3]
      norm_num
    rcases le_or_gt (p 1) 0 with hp | hp
    · have hb : (![10, 10] : Fin 2 → ℝ) ∈
          budgetSetOn (nonnegOrthant 2) p (p ⬝ᵥ (sqrtEconomy fig18D2Endow).ω 0) := by
        refine ⟨fun l => by fin_cases l <;> norm_num, ?_⟩
        change p ⬝ᵥ ![10, 10] ≤ p ⬝ᵥ ![9 / 2, 17]
        simp only [dot_two, Matrix.cons_val_zero, Matrix.cons_val_one]
        linarith
      have := (hx 0).2 _ hb
      change sqrtU ![10, 10] ≤ sqrtU (fig18D2Alloc 0) at this
      rw [hu, sqrtU_vec] at this
      have : (3 : ℝ) < Real.sqrt 10 := Real.lt_sqrt_of_sq_lt (by norm_num)
      linarith
    · have hb : (![81 / 16, 16] : Fin 2 → ℝ) ∈
          budgetSetOn (nonnegOrthant 2) p (p ⬝ᵥ (sqrtEconomy fig18D2Endow).ω 0) := by
        refine ⟨fun l => by fin_cases l <;> norm_num, ?_⟩
        change p ⬝ᵥ ![81 / 16, 16] ≤ p ⬝ᵥ ![9 / 2, 17]
        simp only [dot_two, Matrix.cons_val_zero, Matrix.cons_val_one]
        linarith
      have := (hx 0).2 _ hb
      change sqrtU ![81 / 16, 16] ≤ sqrtU (fig18D2Alloc 0) at this
      rw [hu, sqrtU_vec, h4] at this
      have h94 : Real.sqrt (81 / 16) = 9 / 4 := by
        rw [show (81 / 16 : ℝ) = (9 / 4) ^ 2 by norm_num]
        exact fig18D2_sqrt_sq (by norm_num)
      rw [h94] at this
      norm_num at this

/-! ### Exercise 18.D.1 -/

/-- The key step of Exercise 18.D.1: with rational, strictly convex preferences on `ℝ^L₊`, if
`ω + z ≿ ω` then `ω + z ≿ ω - z` (when `ω - z ≥ 0`). Otherwise `ω - z ≻ ω + z`, the two bundles
differ, and strict convexity gives `ω = ½(ω - z) + ½(ω + z) ≻ ω + z`, a contradiction. -/
theorem pref_add_of_pref_endow {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hr : RationalOn (nonnegOrthant L) r) (hsc : PrefStrictlyConvex (nonnegOrthant L) r)
    {ω z : Fin L → ℝ} (hp : ω + z ∈ nonnegOrthant L)
    (hm : ω - z ∈ nonnegOrthant L) (hir : r (ω + z) ω) : r (ω + z) (ω - z) := by
  by_contra hne
  have hrev : r (ω - z) (ω + z) := ((hr.1 _ hp _ hm).resolve_left hne)
  have hrefl : r (ω + z) (ω + z) := (hr.1 _ hp _ hp).elim id id
  have hdiff : ω - z ≠ ω + z := by
    intro h
    rw [h] at hne
    exact hne hrefl
  have := hsc _ hp _ hm _ hp hrev hrefl hdiff (1 / 2) (by norm_num) (by norm_num)
  have hmid : (1 / 2 : ℝ) • (ω - z) + (1 - 1 / 2 : ℝ) • (ω + z) = ω := by
    funext l
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  rw [hmid] at this
  exact this.2 hir

/-- **Exercise 18.D.1** (MWG, p. 685). In an Edgeworth box (two consumers, exact feasibility
`x₁ + x₂ = ω₁ + ω₂`) with rational, strictly convex preferences, every feasible allocation that
leaves both consumers at least as well off as at their endowments is self-selective, with the
generalized budget set `B = {z*₁, -z*₁} = {z*₁, z*₂}`. (Continuity and monotonicity, assumed in
the exercise, are not needed, nor is `ωᵢ ≥ 0`.) -/
theorem exercise_18_D_1 (E : CoreEconomy (Fin 2) L) (h0Y : (0 : Fin L → ℝ) ∈ E.Y)
    (hr : ∀ i, RationalOn (nonnegOrthant L) (E.pref i))
    (hsc : ∀ i, PrefStrictlyConvex (nonnegOrthant L) (E.pref i)) {x : Fin 2 → Fin L → ℝ}
    (hx : ∀ i, x i ∈ nonnegOrthant L) (hsum : x 0 + x 1 = E.ω 0 + E.ω 1)
    (hir : ∀ i, E.pref i (x i) (E.ω i)) :
    E.IsSelfSelectiveWith x {x 0 - E.ω 0, -(x 0 - E.ω 0)} ∧ E.IsSelfSelective x := by
  have hz1 : x 1 - E.ω 1 = -(x 0 - E.ω 0) := by
    funext l
    have := congrFun hsum l
    simp only [Pi.add_apply] at this
    simp only [Pi.sub_apply, Pi.neg_apply]
    linarith
  have hrefl : ∀ i, E.pref i (x i) (x i) := fun i => ((hr i).1 _ (hx i) _ (hx i)).elim id id
  have hB : E.IsSelfSelectiveWith x {x 0 - E.ω 0, -(x 0 - E.ω 0)} := by
    intro i
    fin_cases i
    · refine ⟨Set.mem_insert _ _, fun z hz hzω => ?_⟩
      rcases hz with rfl | hz
      · simpa using hrefl 0
      · rw [Set.mem_singleton_iff] at hz
        subst hz
        have hp : E.ω 0 + (x 0 - E.ω 0) ∈ nonnegOrthant L := by simpa using hx 0
        have hm : E.ω 0 - (x 0 - E.ω 0) ∈ nonnegOrthant L := by
          rwa [sub_eq_neg_add]
        have := pref_add_of_pref_endow (hr 0) (hsc 0) hp hm (by simpa using hir 0)
        simpa [sub_eq_neg_add] using this
    · refine ⟨by simp [hz1], fun z hz hzω => ?_⟩
      rcases hz with rfl | hz
      · have hm : E.ω 1 - (x 1 - E.ω 1) ∈ nonnegOrthant L := by
          rw [hz1, sub_neg_eq_add, add_comm]
          exact hzω
        have hp : E.ω 1 + (x 1 - E.ω 1) ∈ nonnegOrthant L := by simpa using hx 1
        have := pref_add_of_pref_endow (hr 1) (hsc 1) hp hm (by simpa using hir 1)
        simp only [add_sub_cancel] at this
        rw [hz1, sub_neg_eq_add, add_comm] at this
        exact this
      · rw [Set.mem_singleton_iff] at hz
        subst hz
        rw [← hz1]
        simpa using hrefl 1
  refine ⟨hB, ⟨hx, 0, h0Y, ?_⟩, _, hB⟩
  rw [zero_add, Fin.sum_univ_two, Fin.sum_univ_two, hsum]

/-! ### Proposition 18.D.1: the rigorous steps -/

/-- **Proposition 18.D.1**, proof, equal-treatment step (MWG, p. 669). With rational, strictly
convex preferences on `ℝ^L₊`, two bundles on the same indifference curve that are both
supported by the same price vector `p` (each maximal in its own budget `{y ≥ 0 : p·y ≤ p·x}`)
are equal: otherwise their midpoint is strictly preferred and affordable for one of them. -/
theorem proposition_18_D_1_supported_eq {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hr : RationalOn (nonnegOrthant L) r) (hsc : PrefStrictlyConvex (nonnegOrthant L) r)
    {p x x' : Fin L → ℝ} (hx : x ∈ nonnegOrthant L) (hx' : x' ∈ nonnegOrthant L)
    (hmax : IsMaximalFor r (budgetSetOn (nonnegOrthant L) p (p ⬝ᵥ x)) x)
    (hmax' : IsMaximalFor r (budgetSetOn (nonnegOrthant L) p (p ⬝ᵥ x')) x')
    (hxx' : r x x') (hx'x : r x' x) : x = x' := by
  by_contra hne
  have hrefl : r x x := (hr.1 _ hx _ hx).elim id id
  have hs := hsc _ hx _ hx _ hx' hrefl hx'x hne (1 / 2) (by norm_num) (by norm_num)
  set m := (1 / 2 : ℝ) • x + (1 - 1 / 2 : ℝ) • x' with hm
  have hmX : m ∈ nonnegOrthant L := fun l => by
    simp only [hm, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [hx l, hx' l]
  have hpm : p ⬝ᵥ m = (p ⬝ᵥ x + p ⬝ᵥ x') / 2 := by
    rw [hm, dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    ring
  rcases le_total (p ⬝ᵥ x) (p ⬝ᵥ x') with h | h
  · have := hmax'.2 m ⟨hmX, by rw [hpm]; linarith⟩
    exact hs.2 (hr.2 _ hx _ hx' _ hmX hxx' this)
  · exact hs.2 (hmax.2 m ⟨hmX, by rw [hpm]; linarith⟩)

/-- **Proposition 18.D.1**, proof, equal treatment (MWG, p. 669). If consumers `i` and `k` have
the same preferences and endowments, the allocation has no envy in net trades, and a common
price vector `p` supports every consumer's bundle (a price equilibrium with transfers), then
`x*ᵢ = x*ₖ`. -/
theorem proposition_18_D_1_equal_treatment (E : CoreEconomy ι L)
    (hr : ∀ i, RationalOn (nonnegOrthant L) (E.pref i))
    (hsc : ∀ i, PrefStrictlyConvex (nonnegOrthant L) (E.pref i)) {x : ι → Fin L → ℝ}
    (hx : ∀ i, x i ∈ nonnegOrthant L) (henvy : E.NoEnvyNetTrades x) {p : Fin L → ℝ}
    (hsupp : ∀ i, IsMaximalFor (E.pref i) (budgetSetOn (nonnegOrthant L) p (p ⬝ᵥ x i)) (x i))
    {i k : ι} (hpref : E.pref i = E.pref k) (hω : E.ω i = E.ω k) : x i = x k := by
  have h1 : E.pref i (x i) (x k) := by
    have := henvy i k (by rw [hω, sub_add_cancel]; exact hx k)
    rwa [hω, sub_add_cancel] at this
  have h2 : E.pref k (x k) (x i) := by
    have := henvy k i (by rw [← hω, sub_add_cancel]; exact hx i)
    rwa [← hω, sub_add_cancel] at this
  rw [← hpref] at h2
  have hsk := hsupp k
  rw [← hpref] at hsk
  exact proposition_18_D_1_supported_eq (hr i) (hsc i) (hx i) (hx k) (hsupp i) hsk h1 h2

/-- **Proposition 18.D.1**, proof (MWG, p. 669). If all consumers have the same net trade and
the net trades add up to zero (`∑ᵢ x*ᵢ = ∑ᵢ ωᵢ`), the common net trade is `0`. -/
theorem proposition_18_D_1_single_net_trade [Fintype ι] [Nonempty ι] {x ω : ι → Fin L → ℝ}
    (hsum : ∑ i, x i = ∑ i, ω i) (hz : ∀ i k, x i - ω i = x k - ω k) (i : ι) :
    x i - ω i = 0 := by
  have h : ∑ k, (x k - ω k) = (Fintype.card ι : ℝ) • (x i - ω i) := by
    rw [Finset.sum_congr rfl fun k _ => hz k i, Finset.sum_const, Finset.card_univ,
      Nat.cast_smul_eq_nsmul]
  rw [Finset.sum_sub_distrib, hsum, sub_self] at h
  have hc : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  exact (smul_eq_zero.mp h.symm).resolve_left hc

/-- **Proposition 18.D.1** (MWG, p. 669), a rigorous version of the main step for a smooth
continuum of types. Types are `t ∈ [0, 1]`, with utilities `u t`, endowments `ω t` and net trades
`z t`. Assume (the regularity the book's proof takes for granted) that `t ↦ z t` is continuous
on `[0, 1]` and differentiable on `(0, 1)`; that the allocation is interior and has no envy in
net trades (no type prefers another type's net trade); that every `u t` is differentiable at the
type's bundle with gradient proportional to `p` (`D t v = μ t (p·v)`, `μ t ≠ 0`); and that the
net trades add up to zero in the sense that `0` is a convex combination of net trades present in
the economy. Then `p·z t = 0` for every type: the first-order condition of no envy makes the
derivative of `t ↦ p·z t` vanish, so `p·z t` is constant, and aggregate feasibility makes the
constant zero. -/
theorem proposition_18_D_1_smooth {u : ℝ → (Fin L → ℝ) → ℝ} {ω z z' : ℝ → Fin L → ℝ}
    {p : Fin L → ℝ} {D : ℝ → (Fin L → ℝ) →L[ℝ] ℝ} {μ : ℝ → ℝ}
    (hzc : ContinuousOn z (Set.Icc 0 1)) (hzd : ∀ t ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt z (z' t) t)
    (hint : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ l, 0 < ω t l + z t l)
    (henvy : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1, ω t + z s ∈ nonnegOrthant L →
      u t (ω t + z s) ≤ u t (ω t + z t))
    (hD : ∀ t ∈ Set.Ioo (0 : ℝ) 1, HasFDerivAt (u t) (D t) (ω t + z t))
    (hgrad : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ v, D t v = μ t * (p ⬝ᵥ v))
    (hμ : ∀ t ∈ Set.Ioo (0 : ℝ) 1, μ t ≠ 0) {n : ℕ} {τ w : Fin n → ℝ}
    (hτ : ∀ k, τ k ∈ Set.Icc (0 : ℝ) 1) (hw1 : ∑ k, w k = 1)
    (hagg : ∑ k, w k • z (τ k) = 0) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, p ⬝ᵥ z t = 0 := by
  -- the first-order condition of no envy
  have hfoc : ∀ t ∈ Set.Ioo (0 : ℝ) 1, p ⬝ᵥ z' t = 0 := by
    intro t ht
    have htI : t ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self ht
    have hzt : ContinuousAt z t := (hzd t ht).continuousAt
    have hpos : ∀ l, ∀ᶠ s in nhds t, 0 < ω t l + z s l := by
      intro l
      have hcont : ContinuousAt (fun s => ω t l + z s l) t :=
        continuousAt_const.add ((continuous_apply l).continuousAt.comp hzt)
      exact continuousAt_const.eventually_lt hcont (hint t htI l)
    have hloc : IsLocalMax (fun s => u t (ω t + z s)) t := by
      filter_upwards [Filter.eventually_all.mpr hpos, isOpen_Ioo.mem_nhds ht] with s hs hsI
      exact henvy t htI s (Set.Ioo_subset_Icc_self hsI) fun l => (hs l).le
    have hder : HasDerivAt (fun s => u t (ω t + z s)) (D t (z' t)) t :=
      (hD t ht).comp_hasDerivAt (f := fun s => ω t + z s) t ((hzd t ht).const_add (ω t))
    have := hloc.hasDerivAt_eq_zero hder
    rw [hgrad t ht] at this
    exact (mul_eq_zero.mp this).resolve_left (hμ t ht)
  -- `t ↦ p·z t` has derivative `p·z' t` on `(0, 1)`
  have hderf : ∀ t ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt (fun s => p ⬝ᵥ z s) (p ⬝ᵥ z' t) t := by
    intro t ht
    have hl : ∀ l ∈ Finset.univ, HasDerivAt (fun s => p l * z s l) (p l * z' t l) t :=
      fun l _ => (hasDerivAt_pi.mp (hzd t ht) l).const_mul (p l)
    exact HasDerivAt.fun_sum hl
  have hcontf : ContinuousOn (fun s => p ⬝ᵥ z s) (Set.Icc 0 1) := by
    have : ∀ l ∈ Finset.univ, ContinuousOn (fun s => p l * z s l) (Set.Icc 0 1) :=
      fun l _ => continuousOn_const.mul ((continuous_apply l).comp_continuousOn hzc)
    exact continuousOn_finsetSum _ this
  -- hence `p·z t = p·z 0` on `[0, 1]`
  have hconst : ∀ t ∈ Set.Icc (0 : ℝ) 1, p ⬝ᵥ z t = p ⬝ᵥ z 0 := by
    intro t ht
    rcases ht.1.eq_or_lt with h0 | h0
    · rw [← h0]
    · obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope (fun s => p ⬝ᵥ z s)
        (fun s => p ⬝ᵥ z' s) h0 (hcontf.mono (Set.Icc_subset_Icc_right ht.2))
        fun s hs => hderf s ⟨hs.1, hs.2.trans_le ht.2⟩
      have hc0 : p ⬝ᵥ z' c = 0 := hfoc c ⟨hc.1, hc.2.trans_le ht.2⟩
      rw [hc0, eq_comm, div_eq_zero_iff] at hslope
      rcases hslope with h | h
      · linarith
      · linarith
  -- aggregate feasibility makes the constant zero
  have h0 : p ⬝ᵥ z 0 = 0 := by
    have := congrArg (fun v => p ⬝ᵥ v) hagg
    simp only [dotProduct_sum, dotProduct_smul, smul_eq_mul, dotProduct_zero] at this
    rw [Finset.sum_congr rfl fun k _ => by rw [hconst (τ k) (hτ k)], ← Finset.sum_mul,
      hw1, one_mul] at this
    exact this
  intro t ht
  rw [hconst t ht, h0]

/-- **Proposition 18.D.1** (MWG, p. 669), conclusion. Under the hypotheses of
`proposition_18_D_1_smooth`, if moreover `p` supports every type's bundle as a price equilibrium
with transfers (`x t = ω t + z t` is best among `y ≥ 0` with `p·y ≤ p·x t`, as `p` does for a
Pareto optimal allocation), then every type's bundle is her Walrasian demand at `p`: the
allocation is a Walrasian equilibrium allocation. -/
theorem proposition_18_D_1_walrasian {u : ℝ → (Fin L → ℝ) → ℝ} {ω z z' : ℝ → Fin L → ℝ}
    {p : Fin L → ℝ} {D : ℝ → (Fin L → ℝ) →L[ℝ] ℝ} {μ : ℝ → ℝ}
    (hzc : ContinuousOn z (Set.Icc 0 1)) (hzd : ∀ t ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt z (z' t) t)
    (hint : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ l, 0 < ω t l + z t l)
    (henvy : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1, ω t + z s ∈ nonnegOrthant L →
      u t (ω t + z s) ≤ u t (ω t + z t))
    (hD : ∀ t ∈ Set.Ioo (0 : ℝ) 1, HasFDerivAt (u t) (D t) (ω t + z t))
    (hgrad : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ v, D t v = μ t * (p ⬝ᵥ v))
    (hμ : ∀ t ∈ Set.Ioo (0 : ℝ) 1, μ t ≠ 0) {n : ℕ} {τ w : Fin n → ℝ}
    (hτ : ∀ k, τ k ∈ Set.Icc (0 : ℝ) 1) (hw1 : ∑ k, w k = 1)
    (hagg : ∑ k, w k • z (τ k) = 0)
    (hsupp : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ nonnegOrthant L, p ⬝ᵥ y ≤ p ⬝ᵥ (ω t + z t) →
      u t y ≤ u t (ω t + z t)) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, p ⬝ᵥ (ω t + z t) = p ⬝ᵥ ω t ∧
      ∀ y ∈ nonnegOrthant L, p ⬝ᵥ y ≤ p ⬝ᵥ ω t → u t y ≤ u t (ω t + z t) := by
  have h := proposition_18_D_1_smooth hzc hzd hint henvy hD hgrad hμ hτ hw1 hagg
  intro t ht
  have he : p ⬝ᵥ (ω t + z t) = p ⬝ᵥ ω t := by rw [dotProduct_add, h t ht, add_zero]
  exact ⟨he, fun y hy hpy => hsupp t ht y hy (he ▸ hpy)⟩

/-- The linear utility `x₁ + x₂` of the instance of Proposition 18.D.1, as a continuous linear
map. -/
noncomputable def prop18D1D : (Fin 2 → ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0 +
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1

/-- **Proposition 18.D.1**, a concrete instance of the hypotheses (MWG, Figure 18.D.6): types
`t ∈ [0, 1]` with utility `x₁ + x₂`, endowments `ω t = (2t, 2 - 2t)` and net trades
`z t = (1 - 2t, 2t - 1)` (every type consumes `(1, 1)`), `p = (1, 1)`, and aggregate net trade
`½ z 0 + ½ z 1 = 0`; all hypotheses of `proposition_18_D_1_walrasian` hold. -/
theorem proposition_18_D_1_instance :
    let u : ℝ → (Fin 2 → ℝ) → ℝ := fun _ => prop18D1D
    let ω : ℝ → Fin 2 → ℝ := fun t => ![2 * t, 2 - 2 * t]
    let z : ℝ → Fin 2 → ℝ := fun t => ![1 - 2 * t, 2 * t - 1]
    let p : Fin 2 → ℝ := ![1, 1]
    ContinuousOn z (Set.Icc 0 1) ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt z ![-2, 2] t) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ l, 0 < ω t l + z t l) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1, ω t + z s ∈ nonnegOrthant 2 →
        u t (ω t + z s) ≤ u t (ω t + z t)) ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) 1, HasFDerivAt (u t) prop18D1D (ω t + z t)) ∧
      (∀ v, prop18D1D v = 1 * (p ⬝ᵥ v)) ∧
      (∑ k : Fin 2, ![1 / 2, 1 / 2] k • z (![0, 1] k) = 0) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ nonnegOrthant 2, p ⬝ᵥ y ≤ p ⬝ᵥ (ω t + z t) →
        u t y ≤ u t (ω t + z t)) := by
  intro u ω z p
  have hD : ∀ v, prop18D1D v = v 0 + v 1 := fun v => by simp [prop18D1D]
  have hz : Continuous z := by
    refine continuous_pi fun l => ?_
    fin_cases l
    · exact continuous_const.sub (continuous_const.mul continuous_id)
    · exact (continuous_const.mul continuous_id).sub continuous_const
  refine ⟨hz.continuousOn, fun t _ => ?_, fun t _ l => ?_, fun t _ s _ _ => ?_,
    fun t _ => prop18D1D.hasFDerivAt, fun v => ?_, ?_, fun t _ y _ hy => ?_⟩
  · refine hasDerivAt_pi.mpr fun l => ?_
    fin_cases l
    · have := ((hasDerivAt_id t).const_mul 2).const_sub 1
      simpa [z] using this
    · have := ((hasDerivAt_id t).const_mul 2).sub_const 1
      simpa [z] using this
  · fin_cases l <;> simp [ω, z]
  · simp only [u, hD]
    simp [ω, z]
    linarith
  · rw [hD, dot_two]
    simp [p]
  · funext l
    fin_cases l <;> simp [z]
  · simp only [u, hD]
    rw [dot_two, dot_two] at hy
    simpa [p] using hy

end MWG.CoreFoundations
