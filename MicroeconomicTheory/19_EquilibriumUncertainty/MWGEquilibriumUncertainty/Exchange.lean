/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGEquilibriumUncertainty.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-!
# Exchange economies under uncertainty: welfare and first-order tools

Pure exchange economies with consumption sets `ℝ^{LS}_+` and utility functions, the setting of
Examples 19.C.1-19.C.2 and of Sections 19.D-19.F.

* Pareto optimality with the feasibility condition `∑ᵢ xᵢ ≤ ∑ᵢ ωᵢ` used on pp. 694 and 710
  (`IsParetoOptimalU`).
* With strongly monotone utilities, Arrow-Debreu equilibrium prices are nonnegative, budgets bind,
  and every Arrow-Debreu equilibrium allocation is Pareto optimal (`adEqmU_paretoOptimal`, the
  first welfare theorem in this setting).
* **pp. 709-710** (the argument of Example 19.F.1, used for Example 19.C.1): with common
  probabilities, state-independent strictly concave Bernoulli utilities and a state-independent
  aggregate endowment, every Pareto optimal allocation is state independent
  (`po_stateIndependent`).
* The one-good expected utility `eu1`, its directional derivatives, the Lagrange condition of
  an interior optimum (`foc_eu1`), and the Pareto tangency condition for two consumers and two
  states (`po_tangency`).
* `GoodBernoulli`: a strictly concave, strictly increasing, differentiable Bernoulli utility,
  with the instance `√·` (`goodBernoulli_sqrt`); its derivative is positive.
-/

namespace MWG.EquilibriumUncertainty

open Filter Topology

variable {S L : ℕ} {ι : Type*} [Fintype ι]

/-! ## Values, sums and cheap improvements -/

theorem cval_sum (p : CVec S L) (x : ι → CVec S L) :
    cval p (∑ i, x i) = ∑ i, cval p (x i) := by
  simp only [cval, Finset.sum_apply, dotProduct_sum]
  exact Finset.sum_comm

theorem cval_mono {p x y : CVec S L} (hp : ∀ s l, 0 ≤ p s l) (h : x ≤ y) :
    cval p x ≤ cval p y :=
  Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun l _ =>
    mul_le_mul_of_nonneg_left (h s l) (hp s l)

theorem cval_add (p x y : CVec S L) : cval p (x + y) = cval p x + cval p y := by
  simp [cval, dotProduct_add, Finset.sum_add_distrib]

theorem cval_sub (p x y : CVec S L) : cval p (x - y) = cval p x - cval p y := by
  simp [cval, dotProduct_sub, Finset.sum_sub_distrib]

theorem cval_smul (p x : CVec S L) (a : ℝ) : cval p (a • x) = a * cval p x := by
  simp [cval, dotProduct_smul, Finset.mul_sum]

theorem cval_unit (p : CVec S L) (l : Fin L) (s : Fin S) :
    cval p (contingentUnit l s) = p s l := by
  unfold cval contingentUnit
  rw [Finset.sum_eq_single s]
  · simp [dotProduct]
  · intro b _ hb; simp [dotProduct, hb]
  · simp

/-- Near any `x ≥ 0` there is a strictly larger bundle costing less than `p·x + g` (`g > 0`). -/
theorem exists_larger_cheap [NeZero S] [NeZero L] (p x : CVec S L) {g : ℝ} (hg : 0 < g) :
    ∃ x', x ≤ x' ∧ x ≠ x' ∧ cval p x' < cval p x + g := by
  set c := ∑ s, ∑ l, |p s l| + 1 with hc
  have hc0 : 0 < c := by
    have : 0 ≤ ∑ s, ∑ l, |p s l| :=
      Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun l _ => abs_nonneg _
    linarith
  set δ := g / c with hδ
  have hδ0 : 0 < δ := div_pos hg hc0
  refine ⟨x + fun _ _ => δ, fun s l => by simp [hδ0.le], fun h => ?_, ?_⟩
  · have := congrFun (congrFun h ⟨0, NeZero.pos S⟩) ⟨0, NeZero.pos L⟩
    simp at this; linarith
  · rw [cval_add]
    have h1 : cval p (fun _ _ => δ) ≤ δ * (∑ s, ∑ l, |p s l|) := by
      unfold cval
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun s _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun l _ => ?_
      rw [mul_comm δ]
      exact mul_le_mul_of_nonneg_right (le_abs_self _) hδ0.le
    have h2 : δ * (∑ s, ∑ l, |p s l|) < g := by
      have : δ * c = g := by rw [hδ]; field_simp
      nlinarith
    linarith

/-! ## Pareto optimality and the first welfare theorem -/

/-- **Pareto optimality** (Definition 16.B.2, with the feasibility `∑ᵢ xᵢ ≤ ∑ᵢ ωᵢ` of pp. 694 and
710): `x` is feasible and no feasible `x'` makes everyone at least as well off and someone
strictly better off. -/
def IsParetoOptimalU (U : ι → CVec S L → ℝ) (ω : ι → CVec S L) (x : ι → CVec S L) : Prop :=
  ((∀ i, NonnegC (x i)) ∧ ∑ i, x i ≤ ∑ i, ω i) ∧
    ¬ ∃ x' : ι → CVec S L, ((∀ i, NonnegC (x' i)) ∧ ∑ i, x' i ≤ ∑ i, ω i) ∧
      (∀ i, U i (x i) ≤ U i (x' i)) ∧ ∃ i, U i (x i) < U i (x' i)

/-- With strongly monotone utilities, Arrow-Debreu prices are nonnegative. -/
theorem adEqmU_price_nonneg {U : ι → CVec S L → ℝ} (hU : ∀ i, StronglyMonotoneC (U i))
    {ω x : ι → CVec S L} {p : CVec S L} (h : IsADEqmU U ω x p) (i : ι) :
    ∀ s l, 0 ≤ p s l := by
  intro s l
  by_contra hneg
  push Not at hneg
  have hx := (h.1 i).1.1
  have hle : x i ≤ x i + contingentUnit l s := fun s' l' => by
    simp only [Pi.add_apply, contingentUnit]; split_ifs <;> simp
  have hne : x i ≠ x i + contingentUnit l s := fun h' => by
    have := congrFun (congrFun h' s) l
    simp [contingentUnit] at this
  have hlt := hU i _ _ hx hle hne
  have hge := (h.1 i).2 (x i + contingentUnit l s) (fun s' l' => (hx s' l').trans (hle s' l'))
    (by rw [cval_add, cval_unit]; linarith [(h.1 i).1.2])
  linarith

/-- With strongly monotone utilities (and `S, L ≥ 1`), the budget constraint binds at an
Arrow-Debreu equilibrium. -/
theorem adEqmU_budget_binds [NeZero S] [NeZero L] {U : ι → CVec S L → ℝ}
    (hU : ∀ i, StronglyMonotoneC (U i)) {ω x : ι → CVec S L} {p : CVec S L}
    (h : IsADEqmU U ω x p) (i : ι) : cval p (x i) = cval p (ω i) := by
  refine le_antisymm (h.1 i).1.2 (not_lt.mp fun hlt => ?_)
  obtain ⟨x', hle, hne, hc⟩ := exists_larger_cheap p (x i) (sub_pos.mpr hlt)
  have hx := (h.1 i).1.1
  have := (h.1 i).2 x' (fun s l => (hx s l).trans (hle s l)) (by linarith)
  linarith [hU i _ _ hx hle hne]

/-- **First welfare theorem** for exchange economies under uncertainty (p. 692, Proposition
16.C.1 in this setting): with strongly monotone utilities on `ℝ^{LS}_+`, every Arrow-Debreu
equilibrium allocation is Pareto optimal. -/
theorem adEqmU_paretoOptimal [NeZero S] [NeZero L] {U : ι → CVec S L → ℝ}
    (hU : ∀ i, StronglyMonotoneC (U i)) {ω x : ι → CVec S L} {p : CVec S L}
    (h : IsADEqmU U ω x p) : IsParetoOptimalU U ω x := by
  refine ⟨⟨fun i => (h.1 i).1.1, h.2.le⟩, ?_⟩
  rintro ⟨x', ⟨hx', hfeas⟩, hge, k, hk⟩
  have hp := adEqmU_price_nonneg hU h k
  have hweak : ∀ i, cval p (ω i) ≤ cval p (x' i) := by
    intro i
    by_contra hlt
    push Not at hlt
    obtain ⟨x'', hle, hne, hc⟩ := exists_larger_cheap p (x' i) (sub_pos.mpr hlt)
    have h1 := hU i _ _ (hx' i) hle hne
    have h2 := (h.1 i).2 x'' (fun s l => (hx' i s l).trans (hle s l)) (by linarith)
    linarith [hge i]
  have hstrict : cval p (ω k) < cval p (x' k) := by
    by_contra hle
    push Not at hle
    linarith [(h.1 k).2 (x' k) (hx' k) hle]
  have hsum : ∑ i, cval p (ω i) < ∑ i, cval p (x' i) :=
    Finset.sum_lt_sum (fun i _ => hweak i) ⟨k, Finset.mem_univ _, hstrict⟩
  rw [← cval_sum, ← cval_sum] at hsum
  linarith [cval_mono hp hfeas]

/-! ## State independence of Pareto optima (pp. 709-710) -/

/-- The constant contingent vector delivering `a ∈ ℝ^L` in every state. -/
def constC (a : Fin L → ℝ) : CVec S L := fun _ => a

/-- **pp. 709-710** (the argument of Example 19.F.1, also behind Example 19.C.1(a)). Suppose the
probabilities `π ≫ 0` (with `∑_s π_s = 1`) are common, every consumer's Bernoulli utility `uᵢ` is
state independent and strictly concave on `ℝ^L_+`, and the aggregate endowment is the same in
every state. Then every Pareto optimal allocation is state independent: `x_{si} = x_{s'i}`. -/
theorem po_stateIndependent {π : Fin S → ℝ} (hπ : ∀ s, 0 < π s) (hπ1 : ∑ s, π s = 1)
    {u : ι → (Fin L → ℝ) → ℝ} (hu : ∀ i, StrictConcaveOn ℝ {a | ∀ l, 0 ≤ a l} (u i))
    {ω : ι → CVec S L} (hω : ∀ s s', ∑ i, ω i s = ∑ i, ω i s') {x : ι → CVec S L}
    (hpo : IsParetoOptimalU (fun i => expUtil π (fun _ => u i)) ω x) :
    ∀ i s s', x i s = x i s' := by
  obtain ⟨⟨hx, hfeas⟩, hno⟩ := hpo
  set xbar : ι → Fin L → ℝ := fun i => ∑ s, π s • x i s with hxbar
  have hxbar0 : ∀ i, ∀ l, 0 ≤ xbar i l := fun i l => by
    simp only [hxbar, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_nonneg fun s _ => mul_nonneg (hπ s).le (hx i s l)
  have hjensen : ∀ i, expUtil π (fun _ => u i) (x i) ≤ u i (xbar i) := by
    intro i
    have := (hu i).concaveOn.le_map_sum (t := Finset.univ) (w := π) (p := x i)
      (fun s _ => (hπ s).le) hπ1 (fun s _ => hx i s)
    simpa [expUtil, smul_eq_mul] using this
  have hconst : ∀ i, expUtil π (fun _ => u i) (constC (S := S) (xbar i)) = u i (xbar i) := by
    intro i
    simp [expUtil, constC, ← Finset.sum_mul, hπ1]
  have hfeas' : ∑ i, constC (S := S) (xbar i) ≤ ∑ i, ω i := by
    intro s l
    obtain ⟨s0⟩ : Nonempty (Fin S) := ⟨s⟩
    have h1 : (∑ i, constC (S := S) (xbar i)) s l = ∑ s', π s' * (∑ i, x i s' l) := by
      simp only [Finset.sum_apply, constC, hxbar, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_comm
    have h2 : ∀ s', ∑ i, x i s' l ≤ (∑ i, ω i) s l := by
      intro s'
      have := hfeas s' l
      simp only [Finset.sum_apply] at this ⊢
      have hω' := congrFun (hω s' s) l
      simp only [Finset.sum_apply] at hω'
      linarith
    rw [h1]
    calc ∑ s', π s' * (∑ i, x i s' l) ≤ ∑ s', π s' * (∑ i, ω i) s l :=
          Finset.sum_le_sum fun s' _ => mul_le_mul_of_nonneg_left (h2 s') (hπ s').le
      _ = (∑ i, ω i) s l := by rw [← Finset.sum_mul, hπ1, one_mul]
  have heq : ∀ i, expUtil π (fun _ => u i) (x i) = u i (xbar i) := by
    intro i
    refine le_antisymm (hjensen i) (not_lt.mp fun hlt => hno ⟨fun i => constC (xbar i),
      ⟨fun i s l => hxbar0 i l, hfeas'⟩, fun j => ?_, i, ?_⟩)
    · dsimp only; rw [hconst]; exact hjensen j
    · dsimp only; rw [hconst]; exact hlt
  intro i s s'
  by_contra hne
  have := (hu i).lt_map_sum (t := Finset.univ) (w := π) (p := x i) (fun s _ => hπ s) hπ1
    (fun s _ => hx i s) ⟨s, Finset.mem_univ _, s', Finset.mem_univ _, hne⟩
  have h2 := heq i
  simp only [expUtil, smul_eq_mul] at this h2
  linarith

/-! ## One good: expected utility and first-order conditions -/

/-- The one-good expected utility `∑_s π_s u_s(x_s)` on `ℝ^S_+` (contingent vectors with
`L = 1`). -/
def eu1 (π : Fin S → ℝ) (u : Fin S → ℝ → ℝ) (x : CVec S 1) : ℝ := ∑ s, π s * u s (x s 0)

theorem eu1_eq_expUtil (π : Fin S → ℝ) (u : Fin S → ℝ → ℝ) :
    eu1 π u = expUtil π (fun s v => u s (v 0)) := rfl

/-- One-good expected utility with `π ≫ 0` and strictly increasing `u_s` on `ℝ_+` is strongly
monotone. -/
theorem eu1_stronglyMonotone {π : Fin S → ℝ} (hπ : ∀ s, 0 < π s) {u : Fin S → ℝ → ℝ}
    (hu : ∀ s, StrictMonoOn (u s) (Set.Ici 0)) : StronglyMonotoneC (eu1 π u) := by
  rw [eu1_eq_expUtil]
  refine expUtil_stronglyMonotone hπ fun s a b ha hab hne => ?_
  have h0 : a 0 ≠ b 0 := fun h => hne (funext fun l => by rw [Subsingleton.elim l 0]; exact h)
  exact hu s (Set.mem_Ici.mpr (ha 0)) (Set.mem_Ici.mpr ((ha 0).trans (hab 0)))
    (lt_of_le_of_ne (hab 0) h0)

/-- The direction `d ∈ ℝ^S` as a one-good contingent vector. -/
def dirC (d : Fin S → ℝ) : CVec S 1 := fun s _ => d s

theorem cval_dirC (p : CVec S 1) (d : Fin S → ℝ) : cval p (dirC d) = ∑ s, p s 0 * d s := by
  simp [cval, dirC, dotProduct]

/-- The derivative of `t ↦ ∑_s π_s u_s(x_s + t d_s)` at `0` is `∑_s π_s u_s'(x_s) d_s`. -/
theorem hasDerivAt_eu1_dir {π : Fin S → ℝ} {u : Fin S → ℝ → ℝ} {x : CVec S 1}
    {D : Fin S → ℝ} (hd : ∀ s, HasDerivAt (u s) (D s) (x s 0)) (d : Fin S → ℝ) :
    HasDerivAt (fun t : ℝ => eu1 π u (x + t • dirC d)) (∑ s, π s * (D s * d s)) 0 := by
  have hfun : (fun t : ℝ => eu1 π u (x + t • dirC d)) =
      fun t => ∑ s, π s * u s (x s 0 + t * d s) := by
    funext t; simp [eu1, dirC]
  rw [hfun]
  refine HasDerivAt.fun_sum fun s _ => HasDerivAt.const_mul _ ?_
  have hin : HasDerivAt (fun t : ℝ => x s 0 + t * d s) (d s) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).mul_const (d s)).const_add (x s 0)
    simpa using this
  have hout : HasDerivAt (u s) (D s) (x s 0 + 0 * d s) := by simpa using hd s
  exact hout.comp (0 : ℝ) hin

/-- **Lagrange condition** for one good. If `x ≫ 0` maximizes `∑_s π_s u_s(x_s)` on
`{x ≥ 0 : p·x ≤ w}` and `u_s'(x_s) = D_s`, then `π_s D_s = λ p_s` for some `λ ≥ 0`. -/
theorem foc_eu1 {π : Fin S → ℝ} {u : Fin S → ℝ → ℝ} {p x : CVec S 1} {w : ℝ}
    (hx : ∀ s, 0 < x s 0) (hb : cval p x ≤ w)
    (hmax : ∀ x', NonnegC x' → cval p x' ≤ w → eu1 π u x' ≤ eu1 π u x) {D : Fin S → ℝ}
    (hd : ∀ s, HasDerivAt (u s) (D s) (x s 0)) :
    ∃ lam : ℝ, 0 ≤ lam ∧ ∀ s, π s * D s = lam * p s 0 := by
  have hx' : ∀ s l, 0 < x s l := fun s l => by rw [Subsingleton.elim l 0]; exact hx s
  obtain ⟨lam, hlam, heq⟩ := exists_nonneg_smul_of_dot_nonpos
    (a := fun s => π s * D s) (q := fun s => p s 0) (fun d hd' => by
      have hcd : cval p (dirC d) ≤ 0 := by rw [cval_dirC]; exact hd'
      have := foc_dir hx' hb hmax hcd (hasDerivAt_eu1_dir hd d)
      simpa [dotProduct, mul_assoc] using this)
  exact ⟨lam, hlam, fun s => by simpa using congrFun heq s⟩

/-- **Pareto optimality excludes improving directions** (two consumers, one good). At an interior
Pareto optimum no direction `d` raises consumer 0's utility at `x₀ + t d` and consumer 1's at
`x₁ - t d` at once (to first order). -/
theorem po_no_improving_dir {U : Fin 2 → CVec S 1 → ℝ} {ω x : Fin 2 → CVec S 1}
    (hpo : IsParetoOptimalU U ω x) (hx : ∀ i s, 0 < x i s 0) (d : Fin S → ℝ) {D₀ D₁ : ℝ}
    (h0 : HasDerivAt (fun t : ℝ => U 0 (x 0 + t • dirC d)) D₀ 0)
    (h1 : HasDerivAt (fun t : ℝ => U 1 (x 1 + t • dirC (-d))) D₁ 0) (hD₀ : 0 < D₀)
    (hD₁ : 0 < D₁) : False := by
  obtain ⟨⟨_, hfeas⟩, hno⟩ := hpo
  have hpos : ∀ i s, ∀ (e : Fin S → ℝ), ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 ≤ x i s 0 + t * e s := by
    intro i s e
    have hc : Tendsto (fun t : ℝ => x i s 0 + t * e s) (𝓝 0) (𝓝 (x i s 0 + 0 * e s)) :=
      tendsto_const_nhds.add (tendsto_id.mul tendsto_const_nhds)
    rw [zero_mul, add_zero] at hc
    exact (hc.eventually (lt_mem_nhds (hx i s))).filter_mono nhdsWithin_le_nhds |>.mono
      fun t ht => ht.le
  have hall : ∀ᶠ t in 𝓝[>] (0 : ℝ), (∀ s, 0 ≤ x 0 s 0 + t * d s) ∧
      ∀ s, 0 ≤ x 1 s 0 + t * (-d) s :=
    (eventually_all.2 fun s => hpos 0 s d).and (eventually_all.2 fun s => hpos 1 s (-d))
  obtain ⟨t, ⟨ht0, ht1⟩, hg0, hg1⟩ := (hall.and ((eventually_lt_of_hasDerivAt_pos h0 hD₀).and
    (eventually_lt_of_hasDerivAt_pos h1 hD₁))).exists
  simp only [zero_smul, add_zero] at hg0 hg1
  refine hno ⟨![x 0 + t • dirC d, x 1 + t • dirC (-d)], ⟨fun i => ?_, ?_⟩, fun i => ?_, 0, ?_⟩
  · fin_cases i
    · intro s l; rw [Subsingleton.elim l 0]; simpa [dirC] using ht0 s
    · intro s l; rw [Subsingleton.elim l 0]; simpa [dirC] using ht1 s
  · have : ∑ i, ![x 0 + t • dirC d, x 1 + t • dirC (-d)] i = ∑ i, x i := by
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      funext s l; simp [dirC]; ring
    rw [this]; exact hfeas
  · fin_cases i
    · exact hg0.le
    · exact hg1.le
  · exact hg0

/-- **Pareto tangency** (two consumers, two states, one good, common probabilities, state-
independent utilities): at an interior Pareto optimum the marginal rates of substitution
`π₁ u₁'(x₁ᵢ) / (π₂ u₂'(x₂ᵢ))` of the two consumers are equal (in cross-multiplied form). -/
theorem po_tangency {π : Fin 2 → ℝ} {u : Fin 2 → ℝ → ℝ} {du : Fin 2 → Fin 2 → ℝ}
    {ω x : Fin 2 → CVec 2 1} (hpo : IsParetoOptimalU (fun i => eu1 π fun _ => u i) ω x)
    (hx : ∀ i s, 0 < x i s 0) (hd : ∀ i s, HasDerivAt (u i) (du i s) (x i s 0)) :
    π 0 * du 0 0 * (π 1 * du 1 1) = π 0 * du 1 0 * (π 1 * du 0 1) := by
  have hder : ∀ i (e : Fin 2 → ℝ), HasDerivAt (fun t : ℝ => eu1 π (fun _ => u i) (x i + t • dirC e))
      (π 0 * (du i 0 * e 0) + π 1 * (du i 1 * e 1)) 0 := by
    intro i e
    simpa [Fin.sum_univ_two] using hasDerivAt_eu1_dir (π := π) (fun s => hd i s) e
  set v : Fin 2 → ℝ := ![π 1 * du 0 1 + π 1 * du 1 1, -(π 0 * du 0 0 + π 0 * du 1 0)] with hv
  have hv0 : v 0 = π 1 * du 0 1 + π 1 * du 1 1 := rfl
  have hv1 : v 1 = -(π 0 * du 0 0 + π 0 * du 1 0) := rfl
  rcases lt_trichotomy (π 0 * du 0 0 * (π 1 * du 1 1)) (π 0 * du 1 0 * (π 1 * du 0 1))
    with hlt | heq | hgt
  · exfalso
    refine po_no_improving_dir hpo hx (-v) (hder 0 _) (hder 1 _) ?_ ?_
    · simp only [Pi.neg_apply, hv0, hv1]; nlinarith
    · simp only [Pi.neg_apply, neg_neg, hv0, hv1]; nlinarith
  · exact heq
  · exfalso
    refine po_no_improving_dir hpo hx v (hder 0 _) (hder 1 _) ?_ ?_
    · simp only [hv0, hv1]; nlinarith
    · simp only [Pi.neg_apply, hv0, hv1]; nlinarith

/-! ## Good Bernoulli utilities -/

/-- A strictly concave, strictly increasing Bernoulli utility on `ℝ_+`, differentiable on `ℝ_{++}`
with derivative `u'` (the standing assumptions of Examples 19.C.1-19.C.2 and Exercise 19.C.4). -/
def GoodBernoulli (u u' : ℝ → ℝ) : Prop :=
  StrictConcaveOn ℝ (Set.Ici 0) u ∧ StrictMonoOn u (Set.Ici 0) ∧
    ∀ y, 0 < y → HasDerivAt u (u' y) y

/-- The derivative of a good Bernoulli utility is positive on `ℝ_{++}`. -/
theorem GoodBernoulli.deriv_pos {u u' : ℝ → ℝ} (h : GoodBernoulli u u') {y : ℝ} (hy : 0 < y) :
    0 < u' y := by
  have hnn : ∀ z, 0 < z → 0 ≤ u' z := by
    intro z hz
    have := hasDerivAt_nonpos_of_eventually_le (h.2.2 z hz).neg (Filter.eventually_of_mem
      self_mem_nhdsWithin fun t (ht : z < t) => by
        rw [Pi.neg_apply, Pi.neg_apply, neg_le_neg_iff]
        exact (h.2.1 (Set.mem_Ici.mpr hz.le) (Set.mem_Ici.mpr (hz.le.trans ht.le)) ht).le)
    linarith
  have hlt := hasDerivAt_lt_of_strictConcaveOn h.1 (Set.mem_Ici.mpr hy.le)
    (Set.mem_Ici.mpr (by linarith : (0 : ℝ) ≤ y + 1)) (by linarith) (h.2.2 y hy)
    (h.2.2 (y + 1) (by linarith))
  linarith [hnn (y + 1) (by linarith)]

/-- The derivative of a good Bernoulli utility is strictly decreasing. -/
theorem GoodBernoulli.deriv_lt {u u' : ℝ → ℝ} (h : GoodBernoulli u u') {y z : ℝ} (hy : 0 < y)
    (hyz : y < z) : u' z < u' y :=
  hasDerivAt_lt_of_strictConcaveOn h.1 (Set.mem_Ici.mpr hy.le)
    (Set.mem_Ici.mpr (hy.le.trans hyz.le)) hyz (h.2.2 y hy) (h.2.2 z (hy.trans hyz))

/-- `√·` is a good Bernoulli utility (an instance of the hypotheses). -/
theorem goodBernoulli_sqrt : GoodBernoulli Real.sqrt fun y => 1 / (2 * Real.sqrt y) :=
  ⟨Real.strictConcaveOn_sqrt, fun _ ha _ _ hab => Real.sqrt_lt_sqrt ha hab,
    fun _ hy => Real.hasDerivAt_sqrt hy.ne'⟩

end MWG.EquilibriumUncertainty
