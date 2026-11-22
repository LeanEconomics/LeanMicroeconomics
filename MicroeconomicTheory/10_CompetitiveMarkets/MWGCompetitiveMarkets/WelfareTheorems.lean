/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGCompetitiveMarkets.QuasilinearEquilibrium
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# The fundamental welfare theorems in a partial equilibrium context (MWG Section 10.D)

MWG, pp. 325-328, and Exercises 10.D.1-10.D.4 (p. 346). Pareto optimality is Definition 10.B.2
for the quasilinear economy of Section 10.C.

* (10.D.1) (p. 325): for fixed levels of good `ℓ`, the utility vectors attainable by
  distributing the numeraire are `{u : ∑ uᵢ ≤ ∑ φᵢ(x̄ᵢ) + ω_m - ∑ cⱼ(q̄ⱼ)}`: the boundary is a
  hyperplane with normal `(1, …, 1)` (`eq_10_D_1`).
* Pareto optimal allocations are exactly the feasible allocations whose levels of good `ℓ`
  maximize the Marshallian aggregate surplus `∑ φᵢ(xᵢ) - ∑ cⱼ(qⱼ)` subject to `∑ xᵢ = ∑ qⱼ`
  (problem (10.D.2)) and which waste no numeraire (`ql_pareto_iff`).
* (10.D.3)-(10.D.5) (p. 326): the first-order conditions of (10.D.2) are necessary
  (`optimalLevels_foc`) and sufficient (`IsQLEqm.isOptimalLevels`); they are (10.C.1)-(10.C.3)
  with `μ` in place of `p*`.
* **Proposition 10.D.1** (first welfare theorem) and **Proposition 10.D.2** (second welfare
  theorem, given that an equilibrium exists, which Section 10.C provides for strictly convex
  costs; correction 2).
* Footnote 15 and **Exercise 10.D.1**: uniqueness of optimal consumption levels, of aggregate
  output, and (with strictly convex costs) of individual outputs.
* Problem (10.D.6), **Exercise 10.D.3** and **Exercise 10.D.4** (p. 328).
-/

namespace MWG.CompetitiveMarkets

open Filter Topology MWG.ConsumerChoice

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **(10.D.2), (10.E.1)** (MWG, pp. 326, 329). The Marshallian aggregate surplus
`S(x, q) = ∑ᵢ φᵢ(xᵢ) - ∑ⱼ cⱼ(qⱼ)`. -/
def qlSurplus (φ : ι → ℝ → ℝ) (c : κ → ℝ → ℝ) (x : ι → ℝ) (q : κ → ℝ) : ℝ :=
  ∑ i, φ i (x i) - ∑ j, c j (q j)

/-- **Problem (10.D.2)** (MWG, p. 326). `(x, q)` are optimal consumption and production levels
of good `ℓ`: nonnegative, `∑ xᵢ = ∑ qⱼ`, and maximizing aggregate surplus among such levels. -/
def IsOptimalLevels (φ : ι → ℝ → ℝ) (c : κ → ℝ → ℝ) (x : ι → ℝ) (q : κ → ℝ) : Prop :=
  (∀ i, 0 ≤ x i) ∧ (∀ j, 0 ≤ q j) ∧ ∑ i, x i = ∑ j, q j ∧
    ∀ x' q', (∀ i, 0 ≤ x' i) → (∀ j, 0 ≤ q' j) → ∑ i, x' i = ∑ j, q' j →
      qlSurplus φ c x' q' ≤ qlSurplus φ c x q

/-- Feasibility (Definition 10.B.1) in the quasilinear economy, unfolded. -/
theorem ql_feasible_iff (φ : ι → ℝ → ℝ) (c : κ → ℝ → ℝ) (ωm : ι → ℝ) (θ : ι → κ → ℝ)
    (a : Allocation ι κ 2) :
    (qlEconomy φ c ωm θ).toEconomy.IsFeasible a ↔
      (∀ i, 0 ≤ a.x i 1) ∧ (∀ j, 0 ≤ a.y j 1 ∧ c j (a.y j 1) ≤ -a.y j 0) ∧
      ∑ i, a.x i 0 ≤ ∑ i, ωm i + ∑ j, a.y j 0 ∧ ∑ i, a.x i 1 ≤ ∑ j, a.y j 1 := by
  simp only [Economy.IsFeasible, Economy.IsAllocation, PrivEconomy.toEconomy, qlEconomy,
    Fin.forall_fin_two, Finset.sum_apply]
  simp only [Set.mem_ofPred_eq, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Finset.sum_const_zero, zero_add]
  tauto

omit [Fintype κ] in
/-- Utilities in the quasilinear economy: `uᵢ(m, x) = m + φᵢ(x)`. -/
theorem ql_utility (φ : ι → ℝ → ℝ) (c : κ → ℝ → ℝ) (ωm : ι → ℝ) (θ : ι → κ → ℝ) (i : ι)
    (v : Fin 2 → ℝ) : (qlEconomy φ c ωm θ).toEconomy.u i v = v 0 + φ i (v 1) := rfl

/-- In a feasible allocation, `∑ᵢ uᵢ ≤ ω_m + S(x, q)`. -/
theorem ql_sum_utility_le {φ : ι → ℝ → ℝ} {c : κ → ℝ → ℝ} {ωm : ι → ℝ} {θ : ι → κ → ℝ}
    {a : Allocation ι κ 2} (ha : (qlEconomy φ c ωm θ).toEconomy.IsFeasible a) :
    ∑ i, (qlEconomy φ c ωm θ).toEconomy.u i (a.x i) ≤
      ∑ i, ωm i + qlSurplus φ c (fun i => a.x i 1) (fun j => a.y j 1) := by
  rw [ql_feasible_iff] at ha
  simp only [ql_utility, Finset.sum_add_distrib, qlSurplus]
  have h1 := ha.2.2.1
  have h2 : ∑ j, a.y j 0 ≤ -∑ j, c j (a.y j 1) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum fun j _ => by linarith [(ha.2.1 j).2]
  linarith

/-- **(10.D.1)** (MWG, p. 325). With the levels of good `ℓ` fixed at `(x̄, q̄)`, the utility
vectors attainable by distributing the remaining numeraire `ω_m - ∑ cⱼ(q̄ⱼ)` are exactly
`{u : ∑ uᵢ ≤ ∑ φᵢ(x̄ᵢ) + ω_m - ∑ cⱼ(q̄ⱼ)}` (at least one consumer). -/
theorem eq_10_D_1 [Nonempty ι] (φ : ι → ℝ → ℝ) (c : κ → ℝ → ℝ) (ωm : ℝ) (x : ι → ℝ)
    (q : κ → ℝ) :
    {u : ι → ℝ | ∃ m : ι → ℝ, ∑ i, m i ≤ ωm - ∑ j, c j (q j) ∧ ∀ i, u i ≤ m i + φ i (x i)} =
      {u | ∑ i, u i ≤ ∑ i, φ i (x i) + ωm - ∑ j, c j (q j)} := by
  ext u
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨m, hm, hu⟩
    have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hu i
    rw [Finset.sum_add_distrib] at this
    linarith
  · intro hu
    obtain ⟨i₀⟩ := ‹Nonempty ι›
    classical
    set slack := ∑ i, φ i (x i) + ωm - ∑ j, c j (q j) - ∑ i, u i with hslack
    refine ⟨fun i => u i - φ i (x i) + if i = i₀ then slack else 0, ?_, fun i => ?_⟩
    · simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq',
        Finset.mem_univ, ↓reduceIte, hslack]
      linarith
    · have : (0 : ℝ) ≤ if i = i₀ then slack else 0 := by
        split_ifs
        · simp only [hslack]; linarith
        · exact le_rfl
      linarith

/-- A positive sum of reals has a positive term. -/
theorem exists_pos_of_sum_pos {α : Type*} [Fintype α] {f : α → ℝ} (h : 0 < ∑ i, f i) :
    ∃ i, 0 < f i := by
  obtain ⟨i, -, hi⟩ := Finset.exists_lt_of_sum_lt (s := Finset.univ) (f := fun _ => (0 : ℝ))
    (g := f) (by simpa using h)
  exact ⟨i, hi⟩

/-- Lowering production to match consumption: from nonnegative `q'` with `X ≤ ∑ q'ⱼ`, scale to
`q''` with `∑ q''ⱼ = X` and lower cost (strictly lower if `X < ∑ q'ⱼ` and costs are strictly
increasing). -/
theorem ql_reduce {c : κ → ℝ → ℝ} (hc : ∀ j, StrictMonoOn (c j) (Set.Ici 0)) {q' : κ → ℝ}
    (hq' : ∀ j, 0 ≤ q' j) {X : ℝ} (hX : 0 ≤ X) (hXq : X ≤ ∑ j, q' j) :
    ∃ q'' : κ → ℝ, (∀ j, 0 ≤ q'' j) ∧ ∑ j, q'' j = X ∧ ∑ j, c j (q'' j) ≤ ∑ j, c j (q' j) ∧
      (X < ∑ j, q' j → ∑ j, c j (q'' j) < ∑ j, c j (q' j)) := by
  rcases eq_or_lt_of_le (Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => hq' j) with h0 | hpos
  · have hX0 : X = 0 := le_antisymm (h0 ▸ hXq) hX
    refine ⟨q', hq', by rw [← h0, hX0], le_rfl, fun h => ?_⟩
    rw [← h0] at h; exact absurd h (by linarith)
  · set r := X / ∑ j, q' j with hr
    have hr0 : 0 ≤ r := div_nonneg hX hpos.le
    have hr1 : r ≤ 1 := (div_le_one hpos).2 hXq
    have hle : ∀ j, q' j * r ≤ q' j := fun j => mul_le_of_le_one_right (hq' j) hr1
    refine ⟨fun j => q' j * r, fun j => mul_nonneg (hq' j) hr0, ?_, ?_, fun hlt => ?_⟩
    · rw [← Finset.sum_mul, hr]; field_simp
    · exact Finset.sum_le_sum fun j _ =>
        (hc j).monotoneOn (mul_nonneg (hq' j) hr0) (hq' j) (hle j)
    · have hr1' : r < 1 := (div_lt_one hpos).2 hlt
      obtain ⟨j, hj⟩ := exists_pos_of_sum_pos hpos
      refine Finset.sum_lt_sum (fun k _ =>
        (hc k).monotoneOn (mul_nonneg (hq' k) hr0) (hq' k) (hle k)) ⟨j, Finset.mem_univ j, ?_⟩
      exact hc j (mul_nonneg (hq' j) hr0) (hq' j) (mul_lt_of_lt_one_right hj hr1')

/-- **Pareto optimality via aggregate surplus** (MWG, p. 325). A feasible allocation is Pareto
optimal iff the sum of utilities reaches `ω_m + S(x', q')` for all nonnegative levels with
`∑ x'ᵢ ≤ ∑ q'ⱼ`. -/
theorem ql_pareto_iff_le [Nonempty ι] (φ : ι → ℝ → ℝ) (c : κ → ℝ → ℝ) (ωm : ι → ℝ)
    (θ : ι → κ → ℝ) (a : Allocation ι κ 2) :
    (qlEconomy φ c ωm θ).toEconomy.IsParetoOptimal a ↔
      (qlEconomy φ c ωm θ).toEconomy.IsFeasible a ∧
      ∀ x' q', (∀ i, 0 ≤ x' i) → (∀ j, 0 ≤ q' j) → ∑ i, x' i ≤ ∑ j, q' j →
        ∑ i, ωm i + qlSurplus φ c x' q' ≤ ∑ i, (qlEconomy φ c ωm θ).toEconomy.u i (a.x i) := by
  classical
  constructor
  · rintro ⟨ha, hno⟩
    refine ⟨ha, fun x' q' hx' hq' hsum => not_lt.1 fun hlt => hno ?_⟩
    set n : ℝ := (Fintype.card ι : ℝ) with hn
    have hn0 : 0 < n := by rw [hn]; exact_mod_cast Fintype.card_pos
    set δ := ∑ i, ωm i + qlSurplus φ c x' q' -
      ∑ i, (qlEconomy φ c ωm θ).toEconomy.u i (a.x i) with hδ
    have hδ0 : 0 < δ := by rw [hδ]; linarith
    refine ⟨⟨fun i => ![(qlEconomy φ c ωm θ).toEconomy.u i (a.x i) - φ i (x' i) + δ / n, x' i],
      fun j => ![-c j (q' j), q' j]⟩, ?_, fun i => ?_, ?_⟩
    · rw [ql_feasible_iff]
      refine ⟨fun i => by simpa using hx' i, fun j => ⟨by simpa using hq' j, by simp⟩, ?_, ?_⟩
      · simp only [Matrix.cons_val_zero, Finset.sum_add_distrib, Finset.sum_sub_distrib,
          Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.sum_neg_distrib]
        have : (Fintype.card ι : ℝ) * (δ / n) = δ := by rw [← hn]; field_simp
        rw [this, hδ]
        simp only [qlSurplus]
        linarith
      · simpa using hsum
    · simp only [ql_utility, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      have : 0 < δ / n := div_pos hδ0 hn0
      linarith
    · obtain ⟨i⟩ := ‹Nonempty ι›
      refine ⟨i, ?_⟩
      simp only [ql_utility, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      have : 0 < δ / n := div_pos hδ0 hn0
      linarith
  · rintro ⟨ha, hmax⟩
    refine ⟨ha, fun ⟨a', ha', hle, i, hi⟩ => ?_⟩
    have h1 := ql_sum_utility_le ha'
    have hfa := (ql_feasible_iff φ c ωm θ a').1 ha'
    have h2 := hmax (fun i => a'.x i 1) (fun j => a'.y j 1) hfa.1 (fun j => (hfa.2.1 j).1)
      hfa.2.2.2
    have h3 : ∑ k, (qlEconomy φ c ωm θ).toEconomy.u k (a.x k) <
        ∑ k, (qlEconomy φ c ωm θ).toEconomy.u k (a'.x k) :=
      Finset.sum_lt_sum (fun k _ => hle k) ⟨i, Finset.mem_univ i, hi⟩
    linarith

/-- **Pareto optimal allocations** (MWG, pp. 325-326). With strictly increasing costs, a feasible
allocation is Pareto optimal iff its levels of good `ℓ` solve problem (10.D.2) and no numeraire
is wasted: `∑ᵢ uᵢ = ω_m + S(x, q)`. -/
theorem ql_pareto_iff [Nonempty ι] (φ : ι → ℝ → ℝ) (c : κ → ℝ → ℝ)
    (hc : ∀ j, StrictMonoOn (c j) (Set.Ici 0)) (ωm : ι → ℝ) (θ : ι → κ → ℝ)
    (a : Allocation ι κ 2) :
    (qlEconomy φ c ωm θ).toEconomy.IsParetoOptimal a ↔
      (qlEconomy φ c ωm θ).toEconomy.IsFeasible a ∧
      IsOptimalLevels φ c (fun i => a.x i 1) (fun j => a.y j 1) ∧
      ∑ i, (qlEconomy φ c ωm θ).toEconomy.u i (a.x i) =
        ∑ i, ωm i + qlSurplus φ c (fun i => a.x i 1) (fun j => a.y j 1) := by
  rw [ql_pareto_iff_le]
  constructor
  · rintro ⟨ha, hmax⟩
    have hf := (ql_feasible_iff φ c ωm θ a).1 ha
    have hup := ql_sum_utility_le ha
    have hself := hmax _ _ hf.1 (fun j => (hf.2.1 j).1) hf.2.2.2
    have hbal : ∑ i, a.x i 1 = ∑ j, a.y j 1 := by
      by_contra hne
      have hlt : ∑ i, a.x i 1 < ∑ j, a.y j 1 := lt_of_le_of_ne hf.2.2.2 hne
      obtain ⟨q'', hq'', hs'', -, hstrict⟩ := ql_reduce hc (fun j => (hf.2.1 j).1)
        (Finset.sum_nonneg fun i _ => hf.1 i) hf.2.2.2
      have := hmax (fun i => a.x i 1) q'' hf.1 hq'' hs''.symm.le
      have := hstrict hlt
      simp only [qlSurplus] at *
      linarith
    refine ⟨ha, ⟨hf.1, fun j => (hf.2.1 j).1, hbal, fun x' q' hx' hq' hs => ?_⟩, by linarith⟩
    have := hmax x' q' hx' hq' hs.le
    linarith
  · rintro ⟨ha, ⟨-, -, -, hopt⟩, heq⟩
    refine ⟨ha, fun x' q' hx' hq' hs => ?_⟩
    obtain ⟨q'', hq'', hs'', hle, -⟩ := ql_reduce hc hq' (Finset.sum_nonneg fun i _ => hx' i) hs
    have := hopt x' q'' hx' hq'' hs''.symm
    simp only [qlSurplus] at *
    linarith

/-! ## First-order conditions (10.D.3)-(10.D.5) -/

/-- **Sufficiency of (10.D.3)-(10.D.5)** (MWG, p. 326). Levels satisfying the conditions with
multiplier `μ` (which are (10.C.1)-(10.C.3) with `μ` for `p*`) solve problem (10.D.2). -/
theorem IsQLEqm.isOptimalLevels {C : ι → QLConsumer} {F : κ → QLFirm} {x : ι → ℝ}
    {q : κ → ℝ} {μ : ℝ} (h : IsQLEqm C F x q μ) :
    IsOptimalLevels (fun i => (C i).φ) (fun j => (F j).c) x q := by
  refine ⟨fun i => (h.2.1 i).1, fun j => (h.1 j).1, h.2.2, fun x' q' hx' hq' hs => ?_⟩
  have hcons : ∀ i, (C i).φ (x' i) - μ * x' i ≤ (C i).φ (x i) - μ * x i := fun i =>
    ((C i).max_iff (h.2.1 i).1).2 (h.2.1 i) _ (hx' i)
  have hfirm : ∀ j, μ * q' j - (F j).c (q' j) ≤ μ * q j - (F j).c (q j) := fun j =>
    ((F j).max_iff (h.1 j).1).2 (h.1 j).2 _ (hq' j)
  have e1 := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hcons i
  have e2 := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hfirm j
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at e1 e2
  simp only [qlSurplus]
  rw [hs] at e1
  rw [h.2.2] at e1
  linarith

/-- The value of a function after updating one coordinate of its argument. -/
theorem sum_update_apply [DecidableEq ι] (g : ι → ℝ → ℝ) (x : ι → ℝ) (i : ι) (v : ℝ) :
    ∑ k, g k (Function.update x i v k) = ∑ k, g k (x k) + (g i v - g i (x i)) := by
  have h : ∀ k, g k (Function.update x i v k) =
      g k (x k) + if k = i then g i v - g i (x i) else 0 := by
    intro k
    by_cases hk : k = i
    · subst hk; simp
    · simp [hk]
  simp only [h, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

theorem sum_update_id [DecidableEq ι] (x : ι → ℝ) (i : ι) (v : ℝ) :
    ∑ k, Function.update x i v k = ∑ k, x k + (v - x i) :=
  sum_update_apply (fun _ t => t) x i v

/-- Shifting a function's argument: `t ↦ f(a + t)` has derivative `f'(a)` within `[0, ∞)` at `0`
when `f` has it within `[0, ∞)` at `a ≥ 0`. -/
theorem hasDerivWithinAt_shift {f : ℝ → ℝ} {f'a a : ℝ}
    (hf : HasDerivWithinAt f f'a (Set.Ici 0) a) (ha : 0 ≤ a) :
    HasDerivWithinAt (fun t => f (a + t)) f'a (Set.Ici 0) 0 := by
  have hh : HasDerivWithinAt (fun t : ℝ => a + t) 1 (Set.Ici 0) 0 :=
    ((hasDerivAt_id 0).const_add a).hasDerivWithinAt
  have hmap : Set.MapsTo (fun t : ℝ => a + t) (Set.Ici 0) (Set.Ici 0) :=
    fun t ht => by simp only [Set.mem_Ici] at ht ⊢; linarith
  exact (show HasDerivWithinAt f f'a (Set.Ici 0) (a + 0) by simpa using hf).comp 0 hh hmap
    |>.congr_deriv (mul_one _)

/-- **Necessity of (10.D.3)-(10.D.5)** (MWG, p. 326). Optimal levels of good `ℓ` satisfy the
first-order conditions for some multiplier `μ`. -/
theorem optimalLevels_foc {C : ι → QLConsumer} {F : κ → QLFirm} {x : ι → ℝ} {q : κ → ℝ}
    (h : IsOptimalLevels (fun i => (C i).φ) (fun j => (F j).c) x q) :
    ∃ μ, IsQLEqm C F x q μ := by
  classical
  obtain ⟨hx, hq, hs, hopt⟩ := h
  -- perturbation: raise `xᵢ` and `qⱼ` together
  have hpert : ∀ i j (t : ℝ), 0 ≤ x i + t → 0 ≤ q j + t →
      (C i).φ (x i + t) - (F j).c (q j + t) ≤ (C i).φ (x i) - (F j).c (q j) := by
    intro i j t hxt hqt
    have := hopt (Function.update x i (x i + t)) (Function.update q j (q j + t))
      (fun k => by by_cases hk : k = i <;> simp [hk, hxt, hx k])
      (fun k => by by_cases hk : k = j <;> simp [hk, hqt, hq k])
      (by rw [sum_update_id, sum_update_id, hs]; ring)
    simp only [qlSurplus, sum_update_apply (fun k => (C k).φ),
      sum_update_apply (fun k => (F k).c)] at this
    linarith
  -- (A) `φᵢ'(xᵢ) ≤ cⱼ'(qⱼ)`
  have hA : ∀ i j, (C i).dφ (x i) ≤ (F j).dc (q j) := by
    intro i j
    have hd : HasDerivWithinAt (fun t => (C i).φ (x i + t) - (F j).c (q j + t))
        ((C i).dφ (x i) - (F j).dc (q j)) (Set.Ici 0) 0 :=
      (hasDerivWithinAt_shift ((C i).hasDeriv _ (hx i)) (hx i)).sub
        (hasDerivWithinAt_shift ((F j).hasDeriv _ (hq j)) (hq j))
    have := foc_local_necessary hd (by
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht' : 0 < t := ht
      simpa using hpert i j t (by linarith [hx i]) (by linarith [hq j]))
    linarith
  -- (B) at interior points `φᵢ'(xᵢ) = cⱼ'(qⱼ)`
  have hB : ∀ i j, 0 < x i → 0 < q j → (C i).dφ (x i) = (F j).dc (q j) := by
    intro i j hxi hqj
    have hd : HasDerivAt (fun t => (C i).φ (x i + t) - (F j).c (q j + t))
        ((C i).dφ (x i) - (F j).dc (q j)) 0 := by
      have h1 := HasDerivAt.comp_const_add (x i) 0
        (by simpa using foc_hasDerivAt (C i).hasDeriv hxi)
      have h2 := HasDerivAt.comp_const_add (q j) 0
        (by simpa using foc_hasDerivAt (F j).hasDeriv hqj)
      exact h1.sub h2
    have hmax : IsLocalMax (fun t => (C i).φ (x i + t) - (F j).c (q j + t)) 0 := by
      filter_upwards [Ioi_mem_nhds (neg_lt_zero.2 (lt_min hxi hqj))] with t ht
      have ht' : -min (x i) (q j) < t := ht
      have := hpert i j t (by linarith [min_le_left (x i) (q j)])
        (by linarith [min_le_right (x i) (q j)])
      simpa using this
    have := hmax.hasDerivAt_eq_zero hd
    linarith
  by_cases hagg : 0 < ∑ i, x i
  · obtain ⟨i₀, hi₀⟩ := exists_pos_of_sum_pos hagg
    obtain ⟨j₀, hj₀⟩ := exists_pos_of_sum_pos (hs ▸ hagg)
    refine ⟨(C i₀).dφ (x i₀), fun j => ⟨hq j, hA i₀ j, fun hj => (hB i₀ j hi₀ hj)⟩,
      fun i => ⟨hx i, ?_, fun hi => ?_⟩, hs⟩
    · rw [hB i₀ j₀ hi₀ hj₀]; exact hA i j₀
    · rw [hB i j₀ hi hj₀, hB i₀ j₀ hi₀ hj₀]
  · have hx0 : ∀ i, x i = 0 := fun i =>
      (Finset.sum_eq_zero_iff_of_nonneg fun k _ => hx k).1
        (le_antisymm (not_lt.1 hagg) (Finset.sum_nonneg fun k _ => hx k)) i (Finset.mem_univ i)
    have hq0 : ∀ j, q j = 0 := fun j =>
      (Finset.sum_eq_zero_iff_of_nonneg fun k _ => hq k).1
        (by rw [← hs]; exact Finset.sum_eq_zero fun i _ => hx0 i) j (Finset.mem_univ j)
    have hqn : ∀ j, ¬ 0 < q j := fun j => by rw [hq0 j]; exact lt_irrefl 0
    have hxn : ∀ i, ¬ 0 < x i := fun i => by rw [hx0 i]; exact lt_irrefl 0
    by_cases hne : Nonempty ι
    · obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image Finset.univ (fun i => (C i).dφ 0)
        (Finset.univ_nonempty_iff.2 hne)
      refine ⟨(C i₀).dφ 0, fun j => ⟨hq j, ?_, fun hj => absurd hj (hqn j)⟩,
        fun i => ⟨hx i, ?_, fun hi => absurd hi (hxn i)⟩, hs⟩
      · have := hA i₀ j; rw [hx0, hq0] at this; rw [hq0]; exact this
      · rw [hx0]; exact hi₀ i (Finset.mem_univ i)
    · exact ⟨0, fun j => ⟨hq j, ((F j).dc_pos _ (hq j)).le, fun hj => absurd hj (hqn j)⟩,
        fun i => absurd ⟨i⟩ hne, hs⟩

/-- **(10.D.3)-(10.D.5)** (MWG, p. 326). Given the convexity assumptions, levels of good `ℓ`
solve problem (10.D.2) iff they satisfy the first-order conditions for some `μ`. -/
theorem optimalLevels_iff_foc (C : ι → QLConsumer) (F : κ → QLFirm) (x : ι → ℝ) (q : κ → ℝ) :
    IsOptimalLevels (fun i => (C i).φ) (fun j => (F j).c) x q ↔ ∃ μ, IsQLEqm C F x q μ :=
  ⟨optimalLevels_foc, fun ⟨_, h⟩ => h.isOptimalLevels⟩

/-! ## The welfare theorems -/

/-- The sum of utilities at a competitive equilibrium of the quasilinear economy is
`ω_m + S(x*, q*)`: no numeraire is wasted. -/
theorem ql_eqm_sum_utility (C : ι → QLConsumer) (F : κ → QLFirm) (ωm : ι → ℝ)
    (θ : ι → κ → ℝ) (hθ : ∀ j, ∑ i, θ i j = 1) {x : ι → ℝ} {q : κ → ℝ} {p : ℝ}
    (hs : ∑ i, x i = ∑ j, q j) :
    ∑ i, (qlEconomyOf C F ωm θ).toEconomy.u i ((qlAllocation F ωm θ x q p).x i) =
      ∑ i, ωm i + qlSurplus (fun i => (C i).φ) (fun j => (F j).c) x q := by
  simp only [qlEconomyOf, ql_utility, qlAllocation, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, qlSurplus, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [Finset.sum_comm (f := fun i j => θ i j * (p * q j - (F j).c (q j)))]
  simp only [← Finset.sum_mul, hθ, one_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hs]
  ring

/-- **Proposition 10.D.1 (the first fundamental theorem of welfare economics)** (MWG, p. 326).
If the price `p*` and an allocation form a competitive equilibrium (Definition 10.B.3) of the
quasilinear economy, the allocation is Pareto optimal (Definition 10.B.2). -/
theorem proposition_10_D_1 [Nonempty ι] (C : ι → QLConsumer) (F : κ → QLFirm) (ωm : ι → ℝ)
    (θ : ι → κ → ℝ) (hθ : ∀ j, ∑ i, θ i j = 1) (a : Allocation ι κ 2) (p : ℝ)
    (h : (qlEconomyOf C F ωm θ).IsCompetitiveEqm a (qlPrice p)) :
    (qlEconomyOf C F ωm θ).toEconomy.IsParetoOptimal a := by
  have hfeas := h.isFeasible
  obtain ⟨hq, ha⟩ := (ql_isCompetitiveEqm_iff C F ωm θ hθ a p).1 h
  rw [qlEconomyOf, ql_pareto_iff _ _ (fun j => (F j).c_strictMono)]
  refine ⟨hfeas, hq.isOptimalLevels, ?_⟩
  have := ql_eqm_sum_utility C F ωm θ hθ (p := p) hq.2.2
  rw [← ha] at this
  exact this

/-- Two solutions of problem (10.D.2) have the same aggregate surplus. -/
theorem IsOptimalLevels.surplus_eq {φ : ι → ℝ → ℝ} {c : κ → ℝ → ℝ} {x x' : ι → ℝ}
    {q q' : κ → ℝ} (h : IsOptimalLevels φ c x q) (h' : IsOptimalLevels φ c x' q') :
    qlSurplus φ c x q = qlSurplus φ c x' q' :=
  le_antisymm (h'.2.2.2 x q h.1 h.2.1 h.2.2.1) (h.2.2.2 x' q' h'.1 h'.2.1 h'.2.2.1)

/-- **Proposition 10.D.2 (the second fundamental theorem of welfare economics)** (MWG, p. 327),
given that a competitive equilibrium exists (Section 10.C). For the utility levels `u*` of any
Pareto optimal allocation there are transfers `Tᵢ` of the numeraire with `∑ Tᵢ = 0` such that a
competitive equilibrium reached from the endowments `ω_{mi} + Tᵢ` yields exactly `u*`. -/
theorem proposition_10_D_2_of_exists [Nonempty ι] (C : ι → QLConsumer) (F : κ → QLFirm)
    (ωm : ι → ℝ) (θ : ι → κ → ℝ) (hθ : ∀ j, ∑ i, θ i j = 1) (a : Allocation ι κ 2)
    (hPO : (qlEconomyOf C F ωm θ).toEconomy.IsParetoOptimal a)
    (hex : ∃ x q p, IsQLEqm C F x q p) :
    ∃ T : ι → ℝ, ∑ i, T i = 0 ∧ ∃ (a' : Allocation ι κ 2) (p : ℝ),
      (qlEconomyOf C F (ωm + T) θ).IsCompetitiveEqm a' (qlPrice p) ∧
      ∀ i, (qlEconomyOf C F (ωm + T) θ).toEconomy.u i (a'.x i) =
        (qlEconomyOf C F ωm θ).toEconomy.u i (a.x i) := by
  obtain ⟨x, q, p, hq⟩ := hex
  rw [qlEconomyOf, ql_pareto_iff _ _ (fun j => (F j).c_strictMono)] at hPO
  obtain ⟨-, hopt, hsum⟩ := hPO
  set e := qlAllocation F ωm θ x q p with he
  set T : ι → ℝ := fun i => (qlEconomyOf C F ωm θ).toEconomy.u i (a.x i) -
    (qlEconomyOf C F ωm θ).toEconomy.u i (e.x i) with hT
  have hS := hq.isOptimalLevels.surplus_eq hopt
  have hsumT : ∑ i, T i = 0 := by
    simp only [hT, Finset.sum_sub_distrib]
    have := ql_eqm_sum_utility C F ωm θ hθ (p := p) hq.2.2
    rw [← he] at this
    rw [this]
    simp only [qlEconomyOf] at hsum ⊢
    rw [hsum, hS]
    ring
  refine ⟨T, hsumT, qlAllocation F (ωm + T) θ x q p, p,
    ql_isCompetitiveEqm_of_isQLEqm hq _ θ hθ, fun i => ?_⟩
  simp only [hT, he, qlEconomyOf, ql_utility, qlAllocation, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.add_apply]
  ring

/-- **Proposition 10.D.2** (MWG, p. 327) under the assumptions of Section 10.C that give
existence (strictly convex costs, `cⱼ' → ∞`, `maxᵢ φᵢ'(0) > minⱼ cⱼ'(0)`). -/
theorem proposition_10_D_2 [Nonempty ι] [Nonempty κ] (C : ι → QLConsumer)
    (F : κ → QLFirmStrict) (hgap : ∃ i j, (F j).dc 0 < (C i).dφ 0) (ωm : ι → ℝ)
    (θ : ι → κ → ℝ) (hθ : ∀ j, ∑ i, θ i j = 1) (a : Allocation ι κ 2)
    (hPO : (qlEconomyOf C (fun j => (F j).toQLFirm) ωm θ).toEconomy.IsParetoOptimal a) :
    ∃ T : ι → ℝ, ∑ i, T i = 0 ∧ ∃ (a' : Allocation ι κ 2) (p : ℝ),
      (qlEconomyOf C (fun j => (F j).toQLFirm) (ωm + T) θ).IsCompetitiveEqm a' (qlPrice p) ∧
      ∀ i, (qlEconomyOf C (fun j => (F j).toQLFirm) (ωm + T) θ).toEconomy.u i (a'.x i) =
        (qlEconomyOf C (fun j => (F j).toQLFirm) ωm θ).toEconomy.u i (a.x i) := by
  obtain ⟨p, -, -, -, -, hq⟩ := ql_eqm_exists C F hgap
  exact proposition_10_D_2_of_exists C _ ωm θ hθ a hPO ⟨_, _, p, hq⟩

/-! ## Footnote 15 and Exercise 10.D.1: uniqueness of optimal levels -/

/-- **Exercise 10.D.1** (MWG, p. 346; footnote 15, p. 325). If every `φᵢ` is strictly concave
and every `cⱼ` convex on `ℝ₊`, the optimal individual consumption levels in problem (10.D.2) are
unique, and hence so is the optimal aggregate production level. -/
theorem exercise_10_D_1 {φ : ι → ℝ → ℝ} {c : κ → ℝ → ℝ}
    (hφ : ∀ i, StrictConcaveOn ℝ (Set.Ici 0) (φ i)) (hc : ∀ j, ConvexOn ℝ (Set.Ici 0) (c j))
    {x x' : ι → ℝ} {q q' : κ → ℝ} (h : IsOptimalLevels φ c x q)
    (h' : IsOptimalLevels φ c x' q') : x = x' ∧ ∑ j, q j = ∑ j, q' j := by
  have hS := h.surplus_eq h'
  set xm : ι → ℝ := fun i => (1 / 2 : ℝ) • x i + (1 / 2 : ℝ) • x' i with hxm
  set qm : κ → ℝ := fun j => (1 / 2 : ℝ) • q j + (1 / 2 : ℝ) • q' j with hqm
  have hxm0 : ∀ i, 0 ≤ xm i := fun i => by
    simp only [hxm, smul_eq_mul]; linarith [h.1 i, h'.1 i]
  have hqm0 : ∀ j, 0 ≤ qm j := fun j => by
    simp only [hqm, smul_eq_mul]; linarith [h.2.1 j, h'.2.1 j]
  have hsm : ∑ i, xm i = ∑ j, qm j := by
    simp only [hxm, hqm, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum, h.2.2.1,
      h'.2.2.1]
  have hle := h.2.2.2 xm qm hxm0 hqm0 hsm
  have hcost : ∑ j, c j (qm j) ≤ ∑ j, ((1 / 2 : ℝ) * c j (q j) + (1 / 2 : ℝ) * c j (q' j)) :=
    Finset.sum_le_sum fun j _ => by
      simpa [smul_eq_mul, hqm] using (hc j).2 (Set.mem_Ici.2 (h.2.1 j)) (Set.mem_Ici.2 (h'.2.1 j))
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  have hben : ∀ i, (1 / 2 : ℝ) * φ i (x i) + (1 / 2 : ℝ) * φ i (x' i) ≤ φ i (xm i) := fun i => by
    simpa [smul_eq_mul, hxm] using (hφ i).concaveOn.2 (Set.mem_Ici.2 (h.1 i))
      (Set.mem_Ici.2 (h'.1 i))
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  have hxx : x = x' := by
    by_contra hne
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hne
    have hstrict : (1 / 2 : ℝ) * φ i (x i) + (1 / 2 : ℝ) * φ i (x' i) < φ i (xm i) := by
      simpa [smul_eq_mul, hxm] using (hφ i).2 (Set.mem_Ici.2 (h.1 i)) (Set.mem_Ici.2 (h'.1 i)) hi
        (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
    have hsumb : ∑ k, ((1 / 2 : ℝ) * φ k (x k) + (1 / 2 : ℝ) * φ k (x' k)) < ∑ k, φ k (xm k) :=
      Finset.sum_lt_sum (fun k _ => hben k) ⟨i, Finset.mem_univ i, hstrict⟩
    simp only [qlSurplus, Finset.sum_add_distrib, ← Finset.mul_sum] at hle hS hsumb hcost
    linarith
  exact ⟨hxx, by rw [← h.2.2.1, ← h'.2.2.1, hxx]⟩

/-- **Exercise 10.D.1** (MWG, p. 346), last part. If moreover every `cⱼ` is strictly convex,
the optimal individual production levels are unique too. -/
theorem exercise_10_D_1_strict {φ : ι → ℝ → ℝ} {c : κ → ℝ → ℝ}
    (hφ : ∀ i, StrictConcaveOn ℝ (Set.Ici 0) (φ i))
    (hc : ∀ j, StrictConvexOn ℝ (Set.Ici 0) (c j)) {x x' : ι → ℝ} {q q' : κ → ℝ}
    (h : IsOptimalLevels φ c x q) (h' : IsOptimalLevels φ c x' q') : x = x' ∧ q = q' := by
  obtain ⟨hxx, -⟩ := exercise_10_D_1 hφ (fun j => (hc j).convexOn) h h'
  subst hxx
  refine ⟨rfl, ?_⟩
  have hS := h.surplus_eq h'
  by_contra hne
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hne
  set qm : κ → ℝ := fun j => (1 / 2 : ℝ) • q j + (1 / 2 : ℝ) • q' j with hqm
  have hqm0 : ∀ j, 0 ≤ qm j := fun j => by
    simp only [hqm, smul_eq_mul]; linarith [h.2.1 j, h'.2.1 j]
  have hsm : ∑ i, x i = ∑ j, qm j := by
    simp only [hqm, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum, ← h.2.2.1,
      ← h'.2.2.1]
    ring
  have hle := h.2.2.2 x qm h.1 hqm0 hsm
  have hcost : ∑ k, c k (qm k) < ∑ k, ((1 / 2 : ℝ) * c k (q k) + (1 / 2 : ℝ) * c k (q' k)) :=
    Finset.sum_lt_sum (fun k _ => by
      simpa [smul_eq_mul, hqm] using (hc k).convexOn.2 (Set.mem_Ici.2 (h.2.1 k))
        (Set.mem_Ici.2 (h'.2.1 k)) (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
      ⟨j, Finset.mem_univ j, by
        simpa [smul_eq_mul, hqm] using (hc j).2 (Set.mem_Ici.2 (h.2.1 j))
          (Set.mem_Ici.2 (h'.2.1 j)) hj (by norm_num : (0 : ℝ) < 1 / 2)
          (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)⟩
  simp only [qlSurplus, Finset.sum_add_distrib, ← Finset.mul_sum] at hle hS hcost
  linarith

/-- **Footnote 15** (MWG, p. 325). Under the assumptions of Section 10.C, two Pareto optimal
allocations have the same consumption levels of good `ℓ` (and aggregate output): they differ
only in the distribution of the numeraire (and, without strict convexity, in the split of
production among firms). -/
theorem footnote_10_D_15 [Nonempty ι] (C : ι → QLConsumer) (F : κ → QLFirm) (ωm : ι → ℝ)
    (θ : ι → κ → ℝ) {a a' : Allocation ι κ 2}
    (h : (qlEconomyOf C F ωm θ).toEconomy.IsParetoOptimal a)
    (h' : (qlEconomyOf C F ωm θ).toEconomy.IsParetoOptimal a') :
    (∀ i, a.x i 1 = a'.x i 1) ∧ ∑ j, a.y j 1 = ∑ j, a'.y j 1 := by
  rw [qlEconomyOf, ql_pareto_iff _ _ (fun j => (F j).c_strictMono)] at h h'
  obtain ⟨hx, hq⟩ := exercise_10_D_1 (fun i => (C i).strictConcave) (fun j => (F j).convex)
    h.2.1 h'.2.1
  exact ⟨fun i => congrFun hx i, hq⟩

/-! ## Problem (10.D.6), Exercises 10.D.3 and 10.D.4 -/

/-- **Problem (10.D.6)** (MWG, p. 328). `a` maximizes the utility of consumer `i₁` among feasible
allocations giving every other consumer `i` at least `ūᵢ`. -/
def Economy.Solves10D6 {L : ℕ} (E : Economy ι κ L) (i₁ : ι) (ū : ι → ℝ)
    (a : Allocation ι κ L) : Prop :=
  E.IsFeasible a ∧ (∀ i, i ≠ i₁ → ū i ≤ E.u i (a.x i)) ∧
    ∀ a', E.IsFeasible a' → (∀ i, i ≠ i₁ → ū i ≤ E.u i (a'.x i)) →
      E.u i₁ (a'.x i₁) ≤ E.u i₁ (a.x i₁)

/-- **Exercise 10.D.3**, second part (MWG, p. 346). In any economy, a Pareto optimal allocation
solves problem (10.D.6) for the utility levels `ūᵢ = uᵢ(xᵢ)`. -/
theorem exercise_10_D_3_of_pareto {L : ℕ} (E : Economy ι κ L) (i₁ : ι) {a : Allocation ι κ L}
    (h : E.IsParetoOptimal a) : E.Solves10D6 i₁ (fun i => E.u i (a.x i)) a := by
  refine ⟨h.1, fun _ _ => le_rfl, fun a' ha' hcon => not_lt.1 fun hlt => h.2 ?_⟩
  refine ⟨a', ha', fun i => ?_, i₁, hlt⟩
  by_cases hi : i = i₁
  · subst hi; exact hlt.le
  · exact hcon i hi

/-- **Exercise 10.D.3**, first part (MWG, p. 346). In the quasilinear economy, any solution of
problem (10.D.6) is Pareto optimal (a surplus of another consumer could be transferred to
consumer `i₁` through the numeraire). -/
theorem exercise_10_D_3_pareto (φ : ι → ℝ → ℝ) (c : κ → ℝ → ℝ) (ωm : ι → ℝ) (θ : ι → κ → ℝ)
    (i₁ : ι) (ū : ι → ℝ) {a : Allocation ι κ 2}
    (h : (qlEconomy φ c ωm θ).toEconomy.Solves10D6 i₁ ū a) :
    (qlEconomy φ c ωm θ).toEconomy.IsParetoOptimal a := by
  classical
  obtain ⟨ha, hcon, hmax⟩ := h
  refine ⟨ha, fun ⟨a', ha', hle, k, hk⟩ => ?_⟩
  have hk1 : k ≠ i₁ := by
    rintro rfl
    have := hmax a' ha' fun i hi => (hcon i hi).trans (hle i)
    linarith
  set ε := (qlEconomy φ c ωm θ).toEconomy.u k (a'.x k) -
    (qlEconomy φ c ωm θ).toEconomy.u k (a.x k) with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  set coef : ι → ℝ := fun i => (if i = i₁ then ε else 0) - (if i = k then ε else 0) with hcoef
  set a'' : Allocation ι κ 2 := ⟨fun i => a'.x i + coef i • ![1, 0], a'.y⟩ with ha''
  have hx0 : ∀ i, a''.x i 0 = a'.x i 0 + coef i := fun i => by
    simp only [ha'', Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, mul_one]
  have hx1 : ∀ i, a''.x i 1 = a'.x i 1 := fun i => by
    simp only [ha'', Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, mul_zero, add_zero]
  have hu : ∀ i, (qlEconomy φ c ωm θ).toEconomy.u i (a''.x i) =
      (qlEconomy φ c ωm θ).toEconomy.u i (a'.x i) + coef i := by
    intro i
    rw [ql_utility, ql_utility, hx0, hx1]
    ring
  have hfeas : (qlEconomy φ c ωm θ).toEconomy.IsFeasible a'' := by
    rw [ql_feasible_iff] at ha' ⊢
    refine ⟨fun i => by rw [hx1]; exact ha'.1 i, ha'.2.1, ?_, ?_⟩
    · have hsc : ∑ i, coef i = 0 := by
        simp [hcoef, Finset.sum_sub_distrib, Finset.sum_ite_eq']
      have : ∑ i, a''.x i 0 = ∑ i, a'.x i 0 + ∑ i, coef i := by
        simp only [hx0, Finset.sum_add_distrib]
      rw [this, hsc, add_zero]
      exact ha'.2.2.1
    · simp only [hx1]; exact ha'.2.2.2
  have h1 := hmax a'' hfeas fun i hi => by
    rw [hu]
    by_cases hik : i = k
    · subst hik
      simp only [hcoef, hi, ↓reduceIte, zero_sub]
      have := hcon i hi
      rw [hε]
      linarith
    · simp only [hcoef, hi, hik, ↓reduceIte, sub_zero]
      linarith [hcon i hi, hle i]
  rw [hu] at h1
  simp only [hcoef, ↓reduceIte, Ne.symm hk1, sub_zero] at h1
  linarith [hle i₁]

/-- **Exercise 10.D.4** (MWG, p. 346). At any solution of problem (10.D.6) in the quasilinear
economy the levels of good `ℓ` satisfy (10.D.3)-(10.D.5) for some `μ` (the multipliers of the
utility constraints and of the numeraire constraint all equal `1`, and `μ` is the multiplier of
the constraint for good `ℓ`). -/
theorem exercise_10_D_4 [Nonempty ι] (C : ι → QLConsumer) (F : κ → QLFirm) (ωm : ι → ℝ)
    (θ : ι → κ → ℝ) (i₁ : ι) (ū : ι → ℝ) {a : Allocation ι κ 2}
    (h : (qlEconomyOf C F ωm θ).toEconomy.Solves10D6 i₁ ū a) :
    ∃ μ, IsQLEqm C F (fun i => a.x i 1) (fun j => a.y j 1) μ := by
  have hPO := exercise_10_D_3_pareto _ _ ωm θ i₁ ū h
  rw [ql_pareto_iff _ _ (fun j => (F j).c_strictMono)] at hPO
  exact optimalLevels_foc hPO.2.1

/-- **Exercise 10.D.4**, converse (MWG, p. 346). A feasible allocation without waste whose levels
of good `ℓ` satisfy (10.D.3)-(10.D.5) solves problem (10.D.6) for its own utility levels. -/
theorem exercise_10_D_4_converse [Nonempty ι] (C : ι → QLConsumer) (F : κ → QLFirm)
    (ωm : ι → ℝ) (θ : ι → κ → ℝ) (i₁ : ι) {a : Allocation ι κ 2} {μ : ℝ}
    (ha : (qlEconomyOf C F ωm θ).toEconomy.IsFeasible a)
    (hfoc : IsQLEqm C F (fun i => a.x i 1) (fun j => a.y j 1) μ)
    (hwaste : ∑ i, (qlEconomyOf C F ωm θ).toEconomy.u i (a.x i) =
      ∑ i, ωm i + qlSurplus (fun i => (C i).φ) (fun j => (F j).c) (fun i => a.x i 1)
        (fun j => a.y j 1)) :
    (qlEconomyOf C F ωm θ).toEconomy.Solves10D6 i₁
      (fun i => (qlEconomyOf C F ωm θ).toEconomy.u i (a.x i)) a := by
  refine exercise_10_D_3_of_pareto _ i₁ ?_
  rw [qlEconomyOf, ql_pareto_iff _ _ (fun j => (F j).c_strictMono)]
  exact ⟨ha, hfoc.isOptimalLevels, hwaste⟩

end MWG.CompetitiveMarkets
