import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Order.MonotoneConvergence
import MWGProduction.Efficiency
import MWGGeneralEquilibriumExamples.FactorMarkets
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Normed.Group.FunctionSeries
import MWGGeneralEquilibriumExamples.Tools
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import LeanEconomics.DynamicProgramming.Optimality
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Data.Matrix.Mul
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
set_option autoImplicit false

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Intertemporal utility (MWG Section 20.B)

MWG, Chapter 20, Section 20.B, pp. 733-736, and Exercises 20.B.1-20.B.5 (pp. 782-783).

Dates are `t : ℕ`, bundles are `ι → ℝ` with the coordinatewise order, and a consumption
stream is `c : ℕ → ι → ℝ`. The utility of a stream is the discounted sum (20.B.1)
`V(c) = ∑ δ^t u(c_t)` (`discountedUtility`), a `tsum`; `summable_discounted` and
`summable_discounted_of_monotoneOn` show it converges on bounded nonnegative streams when the
one-period utility is bounded on bounded bundles (footnote 2: completeness).

* Comment (1), time impatience: `exercise_20_B_1`.
* Comment (1), survival interpretation: `survival_interpretation`.
* Comment (2), stationarity: `exercise_20_B_2_stationary`, `exercise_20_B_2_violation`.
* Comment (3), additive separability: `exercise_20_B_3_future`, `exercise_20_B_3_past`.
* Comment (5), recursivity `V(c) = u(c₀) + δ V(c¹)`: `discountedUtility_recursive`.
* Comment (5), recursive utility with `G(u, V) = u^α + δ V^α`: Exercise 20.B.4
  (`exercise_20_B_4_bounded`, `exercise_20_B_4_limit`, `exercise_20_B_4_aggregator`).
* Comment (6), altruism: `altruism_dynasty`.
* Exercise 20.B.5: `exercise_20_B_5_concave`, `exercise_20_B_5_affine`,
  `exercise_20_B_5_ordinal_not_additive`.

Departures. The discount factor must be positive (`0 < δ`) for time impatience and
stationarity: with `δ = 0` both fail (`impatience_fails_at_zero_discount`,
`stationarity_fails_at_zero_discount`). The aside after (20.B.3), that the continuation value
`V(c^T)` may be given an arbitrary value, is false for `G(u, V) = u^α + δ V^α`: the zero stream
has two solutions of the aggregator equation (`recursive_aggregator_two_solutions`).
-/

open Filter Topology

namespace MWG.EquilibriumTime

variable {ι : Type*}

/-- A **bounded consumption stream** (MWG, p. 733): `sup_t ‖c_t‖ < ∞`, stated coordinatewise. -/
def BoundedStream (c : ℕ → ι → ℝ) : Prop := ∃ M : ℝ, ∀ t i, |c t i| ≤ M

/-- A **nonnegative stream**: `c_t ≥ 0` for every date. -/
def NonnegStream (c : ℕ → ι → ℝ) : Prop := ∀ t, 0 ≤ c t

/-- **(20.B.2)** (MWG, p. 734): the time-dependent additive utility `V(c) = ∑_t u_t(c_t)`. -/
noncomputable def timeAdditiveUtility (u : ℕ → (ι → ℝ) → ℝ) (c : ℕ → ι → ℝ) : ℝ :=
  ∑' t, u t (c t)

/-- **(20.B.1)** (MWG, p. 733): the discounted utility `V(c) = ∑_t δ^t u(c_t)`. -/
noncomputable def discountedUtility (δ : ℝ) (u : (ι → ℝ) → ℝ) (c : ℕ → ι → ℝ) : ℝ :=
  ∑' t, δ ^ t * u (c t)

/-- (20.B.1) is the special case `u_t = δ^t u` of (20.B.2) (MWG, p. 734). -/
theorem discountedUtility_eq_timeAdditive (δ : ℝ) (u : (ι → ℝ) → ℝ)
    (c : ℕ → ι → ℝ) :
    discountedUtility δ u c = timeAdditiveUtility (fun t x => δ ^ t * u x) c := rfl

/-- The `T`-period **backward shift** `c^T` of a stream (MWG, p. 733): `(c^T)_t = c_{t+T}`. -/
def backShift (c : ℕ → ι → ℝ) (T : ℕ) : ℕ → ι → ℝ := fun t => c (t + T)

/-- The **forward shift** `(0, c₀, c₁, ...)` of comment (1) (MWG, p. 733). -/
def forwardShift (c : ℕ → ι → ℝ) : ℕ → ι → ℝ
  | 0 => 0
  | t + 1 => c t

/-- The discounted series converges when the one-period utilities are bounded and
`0 ≤ δ < 1` (MWG, p. 734: discounting guarantees a finite utility value). -/
theorem summable_discounted {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) {a : ℕ → ℝ} {M : ℝ}
    (ha : ∀ t, |a t| ≤ M) : Summable fun t => δ ^ t * a t := by
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hδ0 hδ1).mul_right M) ?_
  intro t
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hδ0 t)]
  exact mul_le_mul_of_nonneg_left (ha t) (pow_nonneg hδ0 t)

/-- A one-period utility that is monotone on `ℝ^L_+` is bounded along a bounded nonnegative
stream: `u(0) ≤ u(c_t) ≤ u(M, ..., M)`. -/
theorem abs_utility_le_of_monotoneOn {u : (ι → ℝ) → ℝ}
    (hu : MonotoneOn u (Set.Ici 0)) {c : ℕ → ι → ℝ} (hc : NonnegStream c) {M : ℝ}
    (hM : ∀ t i, |c t i| ≤ M) (t : ℕ) :
    |u (c t)| ≤ max |u 0| |u (fun _ => M)| := by
  have h0 : (0 : ι → ℝ) ≤ c t := hc t
  have hMv : c t ≤ fun _ => M := fun i => (le_abs_self _).trans (hM t i)
  have hM0 : (0 : ι → ℝ) ≤ fun _ => M := h0.trans hMv
  have h1 : u 0 ≤ u (c t) := hu (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 h0) h0
  have h2 : u (c t) ≤ u (fun _ => M) := hu (Set.mem_Ici.2 h0) (Set.mem_Ici.2 hM0) hMv
  rw [abs_le]
  constructor
  · have := neg_abs_le (u 0)
    have := le_max_left |u 0| |u (fun _ => M)|
    linarith
  · have := le_abs_self (u (fun _ => M))
    have := le_max_right |u 0| |u (fun _ => M)|
    linarith

/-- **Footnote 2** (MWG, p. 734): for a monotone one-period utility, (20.B.1) converges on every
bounded nonnegative stream, so any two such streams can be compared. -/
theorem summable_discounted_of_monotoneOn {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    {u : (ι → ℝ) → ℝ} (hu : MonotoneOn u (Set.Ici 0)) {c : ℕ → ι → ℝ}
    (hc : NonnegStream c) (hb : BoundedStream c) :
    Summable fun t => δ ^ t * u (c t) := by
  obtain ⟨M, hM⟩ := hb
  exact summable_discounted hδ0 hδ1 (abs_utility_le_of_monotoneOn hu hc hM)

/-- **Footnote 2** (MWG, p. 734): the preference on bounded nonnegative streams induced by
(20.B.1) is complete (and, being represented by a real number, transitive). -/
theorem footnote_20_2 (δ : ℝ) (u : (ι → ℝ) → ℝ) (c c' : ℕ → ι → ℝ) :
    discountedUtility δ u c' ≤ discountedUtility δ u c ∨
      discountedUtility δ u c ≤ discountedUtility δ u c' :=
  le_total _ _

/-- Shifting a nonnegative stream is again nonnegative. -/
theorem NonnegStream.backShift {c : ℕ → ι → ℝ} (hc : NonnegStream c) (T : ℕ) :
    NonnegStream (backShift c T) := fun t => hc (t + T)

/-- Shifting a bounded stream is again bounded. -/
theorem BoundedStream.backShift {c : ℕ → ι → ℝ} (hc : BoundedStream c) (T : ℕ) :
    BoundedStream (backShift c T) := by
  obtain ⟨M, hM⟩ := hc
  exact ⟨M, fun t i => hM (t + T) i⟩

/-- Splitting (20.B.1) at a date `T`: `V(c) = ∑_{t<T} δ^t u(c_t) + δ^T V(c^T)`. -/
theorem discountedUtility_split {δ : ℝ} {u : (ι → ℝ) → ℝ} {c : ℕ → ι → ℝ}
    (hs : Summable fun t => δ ^ t * u (c t)) (T : ℕ) :
    discountedUtility δ u c = ∑ t ∈ Finset.range T, δ ^ t * u (c t)
      + δ ^ T * discountedUtility δ u (backShift c T) := by
  unfold discountedUtility backShift
  rw [← hs.sum_add_tsum_nat_add T, ← tsum_mul_left]
  congr 1
  refine tsum_congr fun t => ?_
  rw [pow_add]
  ring

/-- **Comment (5)** (MWG, p. 735): with (20.B.1), `V(c) = u(c₀) + δ V(c¹)`. -/
theorem discountedUtility_recursive {δ : ℝ} {u : (ι → ℝ) → ℝ} {c : ℕ → ι → ℝ}
    (hs : Summable fun t => δ ^ t * u (c t)) :
    discountedUtility δ u c = u (c 0) + δ * discountedUtility δ u (backShift c 1) := by
  rw [discountedUtility_split hs 1]
  simp

/-- The utility of the forward shift: `V(0, c₀, c₁, ...) = u(0) + δ V(c)`. -/
theorem discountedUtility_forwardShift {δ : ℝ} {u : (ι → ℝ) → ℝ} {c : ℕ → ι → ℝ}
    (hs : Summable fun t => δ ^ t * u (c t)) :
    discountedUtility δ u (forwardShift c) = u 0 + δ * discountedUtility δ u c := by
  have hs' : Summable fun t => δ ^ t * u (forwardShift c t) := by
    refine (summable_nat_add_iff 1).1 ?_
    have : (fun t => δ ^ (t + 1) * u (forwardShift c (t + 1)))
        = fun t => δ * (δ ^ t * u (c t)) := by
      funext t; simp only [forwardShift]; ring
    rw [this]; exact hs.mul_left δ
  rw [discountedUtility_recursive hs']
  simp only [forwardShift]
  congr 2

/-- **Exercise 20.B.1** (MWG, p. 782), time impatience (comment (1), p. 733): if `0 < δ < 1`
and `u` is strictly increasing on `ℝ^L_+`, then for every bounded nonnegative stream `c ≠ 0`
the forward shift `(0, c₀, c₁, ...)` is strictly worse than `c`. -/
theorem exercise_20_B_1 {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) {u : (ι → ℝ) → ℝ}
    (hu : StrictMonoOn u (Set.Ici 0)) {c : ℕ → ι → ℝ} (hc : NonnegStream c)
    (hb : BoundedStream c) (hne : c ≠ 0) :
    discountedUtility δ u (forwardShift c) < discountedUtility δ u c := by
  have hs := summable_discounted_of_monotoneOn hδ0.le hδ1 hu.monotoneOn hc hb
  rw [discountedUtility_forwardShift hs]
  obtain ⟨s, hs0⟩ : ∃ s, c s ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (funext h)
  have hgeom := summable_geometric_of_lt_one hδ0.le hδ1
  have hdiff : Summable fun t => δ ^ t * (u (c t) - u 0) := by
    have := hs.sub (hgeom.mul_right (u 0))
    refine this.congr fun t => ?_
    ring
  have hpos : 0 < ∑' t, δ ^ t * (u (c t) - u 0) := by
    refine hdiff.tsum_pos (fun t => ?_) s ?_
    · exact mul_nonneg (pow_nonneg hδ0.le t)
        (sub_nonneg.2 (hu.monotoneOn (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 (hc t)) (hc t)))
    · refine mul_pos (pow_pos hδ0 s) (sub_pos.2 ?_)
      exact hu (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 (hc s)) (lt_of_le_of_ne (hc s) hs0.symm)
  have hsplit : ∑' t, δ ^ t * (u (c t) - u 0)
      = discountedUtility δ u c - u 0 * (1 - δ)⁻¹ := by
    unfold discountedUtility
    rw [show (fun t => δ ^ t * (u (c t) - u 0)) = fun t => δ ^ t * u (c t) - δ ^ t * u 0 by
      funext t; ring, hs.tsum_sub (hgeom.mul_right (u 0)), tsum_mul_right,
      tsum_geometric_of_lt_one hδ0.le hδ1, mul_comm]
  have h1δ : 0 < 1 - δ := by linarith
  rw [hsplit] at hpos
  have key : u 0 < (1 - δ) * discountedUtility δ u c := by
    have := mul_lt_mul_of_pos_left hpos h1δ
    rw [mul_sub, mul_comm (u 0), ← mul_assoc, mul_inv_cancel₀ h1δ.ne', one_mul] at this
    linarith
  linarith

/-- With `δ = 0`, time impatience fails (correction to the implicit range of `δ`): the
stream `(0, 1, 0, ...)` and its forward shift both have utility `u(0) = 0`. -/
theorem impatience_fails_at_zero_discount :
    let c : ℕ → Fin 1 → ℝ := fun t => if t = 1 then 1 else 0
    c ≠ 0 ∧ NonnegStream c ∧ BoundedStream c ∧
      discountedUtility 0 (fun x => x 0) (forwardShift c) =
        discountedUtility 0 (fun x => x 0) c := by
  intro c
  refine ⟨fun h => ?_, fun t => ?_, ⟨1, fun t i => ?_⟩, ?_⟩
  · have := congrFun (congrFun h 1) 0
    simp [c] at this
  · intro i; simp only [c]; split_ifs <;> simp
  · simp only [c]; split_ifs <;> simp
  · unfold discountedUtility
    rw [tsum_eq_single 0 (fun t ht => by simp [ht]),
      tsum_eq_single 0 (fun t ht => by simp [ht])]
    simp [forwardShift, c]

/-- **Exercise 20.B.2**, first part (MWG, p. 782), stationarity (comment (2), p. 734): if `c`
and `c'` agree before `T`, then `V(c) ≥ V(c')` if and only if `V(c^T) ≥ V(c'^T)`. -/
theorem exercise_20_B_2_stationary {δ : ℝ} (hδ0 : 0 < δ) {u : (ι → ℝ) → ℝ}
    {c c' : ℕ → ι → ℝ} (hs : Summable fun t => δ ^ t * u (c t))
    (hs' : Summable fun t => δ ^ t * u (c' t)) (T : ℕ) (hagree : ∀ t < T, c t = c' t) :
    discountedUtility δ u c' ≤ discountedUtility δ u c ↔
      discountedUtility δ u (backShift c' T) ≤ discountedUtility δ u (backShift c T) := by
  rw [discountedUtility_split hs T, discountedUtility_split hs' T]
  have hsum : ∑ t ∈ Finset.range T, δ ^ t * u (c t)
      = ∑ t ∈ Finset.range T, δ ^ t * u (c' t) :=
    Finset.sum_congr rfl fun t ht => by rw [hagree t (Finset.mem_range.1 ht)]
  rw [hsum, add_le_add_iff_left]
  exact mul_le_mul_iff_of_pos_left (pow_pos hδ0 T)

/-- With `δ = 0` stationarity fails: `(0, 0, ...)` and `(0, 1, 0, ...)` agree at date `0` and
are indifferent at `t = 0`, but their one-period backward shifts are strictly ranked. -/
theorem stationarity_fails_at_zero_discount :
    let c : ℕ → Fin 1 → ℝ := fun t => if t = 1 then 1 else 0
    let c' : ℕ → Fin 1 → ℝ := fun _ => 0
    (∀ t < 1, c t = c' t) ∧
      discountedUtility 0 (fun x => x 0) c ≤ discountedUtility 0 (fun x => x 0) c' ∧
      ¬ discountedUtility 0 (fun x => x 0) (backShift c 1) ≤
        discountedUtility 0 (fun x => x 0) (backShift c' 1) := by
  intro c c'
  have hval : ∀ d : ℕ → Fin 1 → ℝ, discountedUtility 0 (fun x => x 0) d = d 0 0 := by
    intro d
    unfold discountedUtility
    rw [tsum_eq_single 0 (fun t ht => by simp [ht])]
    simp
  refine ⟨fun t ht => ?_, ?_, ?_⟩
  · have : t = 0 := by omega
    subst this; simp [c, c']
  · rw [hval, hval]; simp [c, c']
  · rw [hval, hval]; simp [backShift, c, c']

/-- The time-dependent discount factors `δ_0 = 1`, `δ_t = (1/2)(1/2)^t` for `t ≥ 1`
(quasi-hyperbolic discounting) used for the second part of Exercise 20.B.2. -/
noncomputable def quasiHyperbolic (t : ℕ) : ℝ := if t = 0 then 1 else (1 / 2) * (1 / 2) ^ t

/-- **Exercise 20.B.2**, second part (MWG, p. 782): with the time-dependent discount factors
`quasiHyperbolic` and `u(x) = x`, the streams `c = (0, 1, 0, ...)` and `c' = (0, 0, 3, 0, ...)`
agree at date `0` and `V(c) < V(c')`, while `V(c¹) > V(c'¹)`: stationarity is violated. -/
theorem exercise_20_B_2_violation :
    let c : ℕ → Fin 1 → ℝ := fun t => if t = 1 then 1 else 0
    let c' : ℕ → Fin 1 → ℝ := fun t => if t = 2 then 3 else 0
    let V := timeAdditiveUtility (fun t (x : Fin 1 → ℝ) => quasiHyperbolic t * x 0)
    (∀ t < 1, c t = c' t) ∧ V c < V c' ∧ V (backShift c' 1) < V (backShift c 1) := by
  intro c c' V
  have h1 : V c = 1 / 4 := by
    simp only [V, timeAdditiveUtility]
    rw [tsum_eq_single 1 (fun t ht => by simp [c, ht])]
    norm_num [c, quasiHyperbolic]
  have h2 : V c' = 3 / 8 := by
    simp only [V, timeAdditiveUtility]
    rw [tsum_eq_single 2 (fun t ht => by simp [c', ht])]
    norm_num [c', quasiHyperbolic]
  have h3 : V (backShift c 1) = 1 := by
    simp only [V, timeAdditiveUtility, backShift]
    rw [tsum_eq_single 0 (fun t ht => by simp [c, ht])]
    norm_num [c, quasiHyperbolic]
  have h4 : V (backShift c' 1) = 3 / 4 := by
    simp only [V, timeAdditiveUtility, backShift]
    rw [tsum_eq_single 1 (fun t ht => by
      have : t + 1 ≠ 2 := by omega
      simp [c', this])]
    norm_num [c', quasiHyperbolic]
  refine ⟨fun t ht => ?_, ?_, ?_⟩
  · have : t = 0 := by omega
    subst this; simp [c, c']
  · rw [h1, h2]; norm_num
  · rw [h3, h4]; norm_num

/-- **Footnote 4** (MWG, p. 734): "time consistency" is tautological for a fixed `V`: the
comparison of `c` and `c'` made at `t = 0` and at `T` is the same comparison. -/
theorem footnote_20_4 (V : (ℕ → ι → ℝ) → ℝ) (c c' : ℕ → ι → ℝ) :
    (V c' ≤ V c ↔ V c' ≤ V c) := Iff.rfl

/-- The stream that follows `a` up to date `T` and `b` afterwards: `c = (c', c'')` with
`c' = (a₀, ..., a_T)` and `c'' = (b_{T+1}, ...)` (Exercise 20.B.3, MWG, p. 783). -/
def splice (T : ℕ) (a b : ℕ → ι → ℝ) : ℕ → ι → ℝ := fun t => if t ≤ T then a t else b t

/-- (20.B.1) is additively separable across the split at `T`:
`V(c', c'') = ∑_{t ≤ T} δ^t u(c'_t) + δ^{T+1} V((c'')^{T+1})`. -/
theorem discountedUtility_splice {δ : ℝ} {u : (ι → ℝ) → ℝ} {T : ℕ}
    {a b : ℕ → ι → ℝ} (hs : Summable fun t => δ ^ t * u (splice T a b t)) :
    discountedUtility δ u (splice T a b) = ∑ t ∈ Finset.range (T + 1), δ ^ t * u (a t)
      + δ ^ (T + 1) * discountedUtility δ u (backShift b (T + 1)) := by
  rw [discountedUtility_split hs (T + 1)]
  congr 1
  · refine Finset.sum_congr rfl fun t ht => ?_
    have : t ≤ T := Nat.lt_succ_iff.1 (Finset.mem_range.1 ht)
    simp [splice, this]
  · congr 2
    funext t
    simp [backShift, splice, show ¬ (t + (T + 1) ≤ T) by omega]

/-- **Exercise 20.B.3**, first part (MWG, p. 783): with additively separable `V`, if
`V(ĉ', c'') ≥ V(ĉ', ĉ'')` for some `ĉ'`, then `V(c', c'') ≥ V(c', ĉ'')` for all `c'`: the
ordering of the future is independent of the past. -/
theorem exercise_20_B_3_future {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) {u : (ι → ℝ) → ℝ}
    {M : ℝ} (hM : ∀ x, |u x| ≤ M) (T : ℕ) (a₀ b b' : ℕ → ι → ℝ)
    (h : discountedUtility δ u (splice T a₀ b') ≤ discountedUtility δ u (splice T a₀ b))
    (a : ℕ → ι → ℝ) :
    discountedUtility δ u (splice T a b') ≤ discountedUtility δ u (splice T a b) := by
  have hs : ∀ d : ℕ → ι → ℝ, Summable fun t => δ ^ t * u (d t) :=
    fun d => summable_discounted hδ0.le hδ1 (fun t => hM (d t))
  rw [discountedUtility_splice (hs _), discountedUtility_splice (hs _)] at h ⊢
  have hp := pow_pos hδ0 (T + 1)
  have := le_of_mul_le_mul_left (by linarith : _) hp
  nlinarith

/-- **Exercise 20.B.3**, second part (MWG, p. 783): if `V(c', c̄'') ≥ V(ĉ', c̄'')` for some
`c̄''`, then `V(c', c'') ≥ V(ĉ', c'')` for all `c''`: the ordering of the present is
independent of the (fixed) future. -/
theorem exercise_20_B_3_past {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) {u : (ι → ℝ) → ℝ}
    {M : ℝ} (hM : ∀ x, |u x| ≤ M) (T : ℕ) (a a' b₀ : ℕ → ι → ℝ)
    (h : discountedUtility δ u (splice T a' b₀) ≤ discountedUtility δ u (splice T a b₀))
    (b : ℕ → ι → ℝ) :
    discountedUtility δ u (splice T a' b) ≤ discountedUtility δ u (splice T a b) := by
  have hs : ∀ d : ℕ → ι → ℝ, Summable fun t => δ ^ t * u (d t) :=
    fun d => summable_discounted hδ0.le hδ1 (fun t => hM (d t))
  rw [discountedUtility_splice (hs _), discountedUtility_splice (hs _)] at h ⊢
  linarith

/-- **Comment (1)**, survival interpretation (MWG, p. 734): if the consumer survives each
period with probability `δ`, so that life ends after date `n` with probability
`(1 - δ) δ^n`, then expected lifetime utility `∑_n (1 - δ) δ^n ∑_{t ≤ n} u(c_t)` equals
`V(c)`. Stated for bounded period utilities `a_t = u(c_t)`. -/
theorem survival_interpretation {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) {a : ℕ → ℝ} {M : ℝ}
    (ha : ∀ t, |a t| ≤ M) :
    HasSum (fun n => (1 - δ) * δ ^ n * ∑ t ∈ Finset.range (n + 1), a t)
      (∑' t, δ ^ t * a t) := by
  -- partial sums telescope: ∑_{n<N} (1-δ)δ^n S_n = ∑_{t<N} δ^t a_t - δ^N S_{N-1}
  set S : ℕ → ℝ := fun n => ∑ t ∈ Finset.range n, a t with hS
  have hpart : ∀ N, ∑ n ∈ Finset.range N, (1 - δ) * δ ^ n * S (n + 1)
      = ∑ t ∈ Finset.range N, δ ^ t * a t - δ ^ N * S N := by
    intro N
    induction N with
    | zero => simp [hS]
    | succ N ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
      simp only [hS, Finset.sum_range_succ]
      ring
  have hsum := summable_discounted hδ0 hδ1 ha
  have hSb : ∀ N, |S N| ≤ N * M := by
    intro N
    calc |S N| ≤ ∑ t ∈ Finset.range N, |a t| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _t ∈ Finset.range N, M := Finset.sum_le_sum fun t _ => ha t
      _ = N * M := by simp
  have htail : Tendsto (fun N : ℕ => δ ^ N * S N) atTop (𝓝 0) := by
    have hlim : Tendsto (fun N : ℕ => (N : ℝ) * δ ^ N) atTop (𝓝 0) := by
      have := tendsto_self_mul_const_pow_of_lt_one hδ0 hδ1
      exact this
    have hlim' : Tendsto (fun N : ℕ => (N : ℝ) * δ ^ N * M) atTop (𝓝 0) := by
      simpa using hlim.mul_const M
    refine squeeze_zero_norm (a := fun N : ℕ => |(N : ℝ) * δ ^ N * M|) (fun N => ?_)
      (by simpa using hlim'.abs)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hδ0 N)]
    calc δ ^ N * |S N| ≤ δ ^ N * (N * M) := mul_le_mul_of_nonneg_left (hSb N) (pow_nonneg hδ0 N)
      _ = (N : ℝ) * δ ^ N * M := by ring
      _ ≤ |(N : ℝ) * δ ^ N * M| := le_abs_self _
  have hconv : Tendsto (fun N => ∑ t ∈ Finset.range N, δ ^ t * a t - δ ^ N * S N) atTop
      (𝓝 (∑' t, δ ^ t * a t - 0)) :=
    (hsum.hasSum.tendsto_sum_nat).sub htail
  rw [sub_zero] at hconv
  -- the summand family converges absolutely
  have habs : Summable fun n => (1 - δ) * δ ^ n * S (n + 1) := by
    refine Summable.of_norm_bounded (g := fun n => (1 - δ) * ((n + 1 : ℝ) * δ ^ n) * |M|) ?_ ?_
    · refine Summable.mul_right _ (Summable.mul_left _ ?_)
      have h1 := (summable_pow_mul_geometric_of_norm_lt_one 1
        (by rw [Real.norm_eq_abs, abs_of_nonneg hδ0]; exact hδ1) : Summable fun n : ℕ =>
          ((n : ℝ) ^ 1 * δ ^ n))
      have h2 := summable_geometric_of_lt_one hδ0 hδ1
      refine (h1.add h2).congr fun n => ?_
      ring
    · intro n
      have h1δ : 0 ≤ 1 - δ := by linarith
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg h1δ, abs_of_nonneg (pow_nonneg hδ0 n)]
      have hb := hSb (n + 1)
      have hM : (↑(n + 1) : ℝ) * M ≤ ((n : ℝ) + 1) * |M| := by
        push_cast
        exact mul_le_mul_of_nonneg_left (le_abs_self M) (by positivity)
      calc (1 - δ) * δ ^ n * |S (n + 1)| ≤ (1 - δ) * δ ^ n * (((n : ℝ) + 1) * |M|) :=
            mul_le_mul_of_nonneg_left (hb.trans hM) (mul_nonneg h1δ (pow_nonneg hδ0 n))
        _ = (1 - δ) * (((n : ℝ) + 1) * δ ^ n) * |M| := by ring
  refine (habs.hasSum_iff_tendsto_nat).2 ?_
  exact hconv.congr fun N => (hpart N).symm

/-- **Comment (6)**, altruism (MWG, p. 736): if `W` is bounded on streams bounded by `M` and
satisfies the altruistic recursion `W(c) = u(c₀) + δ W(c¹)`, then by recursive substitution `W`
is the discounted utility (20.B.1) of the dynasty. -/
theorem altruism_dynasty {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) {u : (ι → ℝ) → ℝ}
    {M B : ℝ} (hu : ∀ x : ι → ℝ, (∀ i, |x i| ≤ M) → |u x| ≤ B)
    (W : (ℕ → ι → ℝ) → ℝ) {K : ℝ}
    (hW : ∀ c : ℕ → ι → ℝ, (∀ t i, |c t i| ≤ M) → |W c| ≤ K)
    (hrec : ∀ c : ℕ → ι → ℝ, (∀ t i, |c t i| ≤ M) → W c = u (c 0) + δ * W (backShift c 1))
    (c : ℕ → ι → ℝ) (hc : ∀ t i, |c t i| ≤ M) :
    W c = discountedUtility δ u c := by
  have hs : Summable fun t => δ ^ t * u (c t) :=
    summable_discounted hδ0 hδ1 (fun t => hu (c t) (hc t))
  have hshift : ∀ T, ∀ t i, |backShift c T t i| ≤ M := fun T t i => hc (t + T) i
  have hiter : ∀ T, W c = ∑ t ∈ Finset.range T, δ ^ t * u (c t)
      + δ ^ T * W (backShift c T) := by
    intro T
    induction T with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, zero_add, pow_zero, one_mul]
      rfl
    | succ T ih =>
      rw [ih, hrec _ (hshift T), Finset.sum_range_succ]
      have h1 : backShift (backShift c T) 1 = backShift c (T + 1) := by
        funext t; simp [backShift, add_assoc, add_comm 1 T]
      rw [h1]
      simp only [backShift, zero_add]
      ring
  have htail : Tendsto (fun T => δ ^ T * W (backShift c T)) atTop (𝓝 0) := by
    have hg := (tendsto_pow_atTop_nhds_zero_of_lt_one hδ0 hδ1).mul_const K
    rw [zero_mul] at hg
    refine squeeze_zero_norm (fun T => ?_) hg
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hδ0 T)]
    exact mul_le_mul_of_nonneg_left (hW _ (hshift T)) (pow_nonneg hδ0 T)
  have hconv := (hs.hasSum.tendsto_sum_nat).add htail
  rw [add_zero] at hconv
  exact tendsto_nhds_unique (tendsto_const_nhds.congr fun T => hiter T) hconv

/-! ### Recursive utility with the aggregator `G(u, V) = u^α + δ V^α` (Exercise 20.B.4) -/

/-- The aggregator `G(u, V) = u^α + δ V^α` of comment (5) (MWG, p. 736). -/
noncomputable def powAggregator (α δ : ℝ) (x v : ℝ) : ℝ := x ^ α + δ * v ^ α

/-- The utility (20.B.3) of a stream of current utilities `a_t = u(c_t)` truncated after `n`
periods, with continuation value `v` at the horizon. -/
noncomputable def recursiveTrunc (α δ v : ℝ) : ℕ → (ℕ → ℝ) → ℝ
  | 0, _ => v
  | n + 1, a => powAggregator α δ (a 0) (recursiveTrunc α δ v n (fun t => a (t + 1)))

/-- The truncated recursive utilities are nonnegative. -/
theorem recursiveTrunc_nonneg {α δ v : ℝ} (hδ : 0 ≤ δ) (hv : 0 ≤ v) (n : ℕ)
    (a : ℕ → ℝ) (ha : ∀ t, 0 ≤ a t) : 0 ≤ recursiveTrunc α δ v n a := by
  induction n generalizing a with
  | zero => exact hv
  | succ n ih =>
    simp only [recursiveTrunc, powAggregator]
    exact add_nonneg (Real.rpow_nonneg (ha 0) α) (mul_nonneg hδ (Real.rpow_nonneg
      (ih _ fun t => ha _) α))

/-- **Exercise 20.B.4**, boundedness step (MWG, p. 783): with `0 < α < 1`, `0 ≤ δ < 1` and
current utilities in `[0, U]`, every truncation of (20.B.3) with continuation value `0` lies in
`[0, B]` with `B = max 1 (U^α / (1 - δ))`. -/
theorem exercise_20_B_4_bounded {α δ U : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1) (a : ℕ → ℝ) (ha0 : ∀ t, 0 ≤ a t) (haU : ∀ t, a t ≤ U) (n : ℕ) :
    recursiveTrunc α δ 0 n a ≤ max 1 (U ^ α / (1 - δ)) := by
  set B := max 1 (U ^ α / (1 - δ))
  have hB1 : 1 ≤ B := le_max_left _ _
  have hBU : U ^ α ≤ (1 - δ) * B := by
    have h := le_max_right 1 (U ^ α / (1 - δ))
    have h1δ : 0 < 1 - δ := by linarith
    rw [div_le_iff₀ h1δ] at h
    linarith
  induction n generalizing a with
  | zero => simp only [recursiveTrunc]; linarith
  | succ n ih =>
    simp only [recursiveTrunc, powAggregator]
    have hW := ih (fun t => a (t + 1)) (fun t => ha0 _) (fun t => haU _)
    have hW0 := recursiveTrunc_nonneg (α := α) hδ0 le_rfl n (fun t => a (t + 1)) (fun t => ha0 _)
    have h1 : a 0 ^ α ≤ U ^ α :=
      Real.rpow_le_rpow (ha0 0) (haU 0) hα0.le
    have h2 : recursiveTrunc α δ 0 n (fun t => a (t + 1)) ^ α ≤ B := by
      calc recursiveTrunc α δ 0 n (fun t => a (t + 1)) ^ α ≤ B ^ α :=
            Real.rpow_le_rpow hW0 hW hα0.le
        _ ≤ B ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hB1 hα1.le
        _ = B := Real.rpow_one B
    nlinarith [mul_le_mul_of_nonneg_left h2 hδ0]

/-- The truncations of (20.B.3) with continuation value `0` increase with the horizon. -/
theorem recursiveTrunc_mono {α δ : ℝ} (hα0 : 0 < α) (hδ0 : 0 ≤ δ) (n : ℕ) (a : ℕ → ℝ)
    (ha0 : ∀ t, 0 ≤ a t) : recursiveTrunc α δ 0 n a ≤ recursiveTrunc α δ 0 (n + 1) a := by
  induction n generalizing a with
  | zero =>
    simp only [recursiveTrunc, powAggregator]
    exact add_nonneg (Real.rpow_nonneg (ha0 0) α) (mul_nonneg hδ0 (Real.rpow_nonneg le_rfl α))
  | succ n ih =>
    simp only [recursiveTrunc, powAggregator] at ih ⊢
    have h := ih (fun t => a (t + 1)) (fun t => ha0 _)
    have hW0 := recursiveTrunc_nonneg (α := α) hδ0 le_rfl n (fun t => a (t + 1)) (fun t => ha0 _)
    have hpow := Real.rpow_le_rpow hW0 h hα0.le
    nlinarith [mul_le_mul_of_nonneg_left hpow hδ0]

/-- The recursive utility of (20.B.3): the limit of the truncations with continuation
value `0`. -/
noncomputable def recursiveUtility (α δ : ℝ) (a : ℕ → ℝ) : ℝ :=
  ⨆ n, recursiveTrunc α δ 0 n a

/-- **Exercise 20.B.4**, limit step (MWG, p. 783): the truncated utilities converge as the
horizon grows. -/
theorem exercise_20_B_4_limit {α δ U : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1) (a : ℕ → ℝ) (ha0 : ∀ t, 0 ≤ a t) (haU : ∀ t, a t ≤ U) :
    Tendsto (fun n => recursiveTrunc α δ 0 n a) atTop (𝓝 (recursiveUtility α δ a)) :=
  tendsto_atTop_ciSup (monotone_nat_of_le_succ fun n => recursiveTrunc_mono hα0 hδ0 n a ha0)
    ⟨_, by rintro _ ⟨n, rfl⟩; exact exercise_20_B_4_bounded hα0 hα1 hδ0 hδ1 a ha0 haU n⟩

/-- **Exercise 20.B.4**, aggregator step (MWG, p. 783): the limit satisfies the aggregator
equation `V(c) = G(u(c₀), V(c¹))`. -/
theorem exercise_20_B_4_aggregator {α δ U : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1) (a : ℕ → ℝ) (ha0 : ∀ t, 0 ≤ a t) (haU : ∀ t, a t ≤ U) :
    recursiveUtility α δ a =
      powAggregator α δ (a 0) (recursiveUtility α δ (fun t => a (t + 1))) := by
  have h1 := exercise_20_B_4_limit hα0 hα1 hδ0 hδ1 a ha0 haU
  have h2 := exercise_20_B_4_limit hα0 hα1 hδ0 hδ1 (fun t => a (t + 1)) (fun t => ha0 _)
    (fun t => haU _)
  have hcont : Continuous fun v : ℝ => powAggregator α δ (a 0) v :=
    continuous_const.add (continuous_const.mul (Real.continuous_rpow_const hα0.le))
  have h3 := (hcont.tendsto _).comp h2
  have h4 : Tendsto (fun n => recursiveTrunc α δ 0 (n + 1) a) atTop
      (𝓝 (recursiveUtility α δ a)) := h1.comp (tendsto_add_atTop_nat 1)
  exact tendsto_nhds_unique h4 h3

/-- **Correction to the aside after (20.B.3)** (MWG, p. 736): for `G(u, V) = u^α + δ V^α` the
continuation value cannot be given an arbitrary value. For the zero stream of current
utilities both `V ≡ 0` and `V ≡ δ^{1/(1-α)} > 0` solve the aggregator equation, and the
truncations with continuation value `δ^{1/(1-α)}` stay there at every horizon. -/
theorem recursive_aggregator_two_solutions {α δ : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hδ0 : 0 < δ) :
    let vstar := δ ^ (1 / (1 - α))
    0 < vstar ∧ powAggregator α δ 0 vstar = vstar ∧
      (∀ n, recursiveTrunc α δ vstar n (fun _ => 0) = vstar) ∧
      powAggregator α δ 0 0 = 0 ∧ ∀ n, recursiveTrunc α δ 0 n (fun _ => 0) = 0 := by
  intro vstar
  have hpos : 0 < vstar := Real.rpow_pos_of_pos hδ0 _
  have h1α : 1 - α ≠ 0 := by linarith
  have hfix : powAggregator α δ 0 vstar = vstar := by
    simp only [powAggregator, vstar]
    rw [Real.zero_rpow hα0.ne', zero_add, ← Real.rpow_mul hδ0.le]
    nth_rewrite 1 [← Real.rpow_one δ]
    rw [← Real.rpow_add hδ0]
    congr 1
    field_simp
    ring
  refine ⟨hpos, hfix, fun n => ?_, ?_, fun n => ?_⟩
  · induction n with
    | zero => rfl
    | succ n ih =>
      simp only [recursiveTrunc]
      rw [ih]; exact hfix
  · simp [powAggregator, Real.zero_rpow hα0.ne']
  · induction n with
    | zero => rfl
    | succ n ih =>
      simp only [recursiveTrunc]
      rw [ih]; simp [powAggregator, Real.zero_rpow hα0.ne']

/-! ### Exercise 20.B.5 -/

/-- **Exercise 20.B.5**, first part (MWG, p. 783): if `u` is concave on `ℝ^L_+` and bounded on
the streams considered, then `V(c) = ∑ δ^t u(c_t)` is concave: for nonnegative streams with
summable utility series, `V(θ c + (1 - θ) c') ≥ θ V(c) + (1 - θ) V(c')`. -/
theorem exercise_20_B_5_concave {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) {u : (ι → ℝ) → ℝ}
    (hu : ConcaveOn ℝ (Set.Ici 0) u) {M : ℝ}
    (hM : ∀ x : ι → ℝ, 0 ≤ x → |u x| ≤ M) {c c' : ℕ → ι → ℝ} (hc : NonnegStream c)
    (hc' : NonnegStream c') {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    θ * discountedUtility δ u c + (1 - θ) * discountedUtility δ u c' ≤
      discountedUtility δ u (fun t => θ • c t + (1 - θ) • c' t) := by
  have hmix : ∀ t, 0 ≤ θ • c t + (1 - θ) • c' t := fun t =>
    add_nonneg (smul_nonneg hθ0 (hc t)) (smul_nonneg (by linarith) (hc' t))
  have hs1 := summable_discounted hδ0 hδ1 (fun t => hM (c t) (hc t))
  have hs2 := summable_discounted hδ0 hδ1 (fun t => hM (c' t) (hc' t))
  have hs3 := summable_discounted hδ0 hδ1 (fun t => hM _ (hmix t))
  unfold discountedUtility
  rw [← hs1.tsum_mul_left, ← hs2.tsum_mul_left, ← (hs1.mul_left θ).tsum_add (hs2.mul_left _)]
  refine Summable.tsum_le_tsum (fun t => ?_) ((hs1.mul_left θ).add (hs2.mul_left _)) hs3
  have := hu.2 (Set.mem_Ici.2 (hc t)) (Set.mem_Ici.2 (hc' t)) hθ0 (by linarith : 0 ≤ 1 - θ)
    (by ring)
  simp only [smul_eq_mul] at this
  have hp := pow_nonneg hδ0 t
  nlinarith [mul_le_mul_of_nonneg_left this hp]

/-- **Exercise 20.B.5**, second part, the transformations that preserve the form (MWG,
p. 783): replacing `u` by `a u + b` with `a > 0` gives an additively separable utility with the
same discount factor that ranks streams exactly as `V` does. -/
theorem exercise_20_B_5_affine {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) {u : (ι → ℝ) → ℝ}
    {a b : ℝ} (ha : 0 < a) {c c' : ℕ → ι → ℝ} (hs : Summable fun t => δ ^ t * u (c t))
    (hs' : Summable fun t => δ ^ t * u (c' t)) :
    discountedUtility δ (fun x => a * u x + b) c' ≤ discountedUtility δ (fun x => a * u x + b) c
      ↔ discountedUtility δ u c' ≤ discountedUtility δ u c := by
  have hg := summable_geometric_of_lt_one hδ0 hδ1
  have key : ∀ d : ℕ → ι → ℝ, Summable (fun t => δ ^ t * u (d t)) →
      discountedUtility δ (fun x => a * u x + b) d
        = a * discountedUtility δ u d + b * (1 - δ)⁻¹ := by
    intro d hd
    unfold discountedUtility
    rw [show (fun t => δ ^ t * (a * u (d t) + b)) = fun t => a * (δ ^ t * u (d t)) + b * δ ^ t
      by funext t; ring, (hd.mul_left a).tsum_add (hg.mul_left b), hd.tsum_mul_left,
      tsum_mul_left, tsum_geometric_of_lt_one hδ0 hδ1]
  rw [key c hs, key c' hs', add_le_add_iff_right]
  exact mul_le_mul_iff_of_pos_left ha

/-- **Exercise 20.B.5**, second part, the transformations that destroy the form (MWG,
p. 783): the ordinal transformation `exp ∘ V` of `V(c) = ∑ (1/2)^t c_t` (one good) is not
additively separable: on the streams `(x, y, 0, 0, ...)` every `∑ δ^t w(c_t)` has the form
`w(x) + δ w(y) + C`, whose mixed second difference vanishes, while that of `exp ∘ V` does not. -/
theorem exercise_20_B_5_ordinal_not_additive :
    ¬ ∃ (δ C : ℝ) (w : ℝ → ℝ), ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
      Real.exp (x + (1 / 2) * y) = w x + δ * w y + C := by
  rintro ⟨δ, C, w, h⟩
  have e00 := h 0 0 le_rfl le_rfl
  have e10 := h 1 0 zero_le_one le_rfl
  have e01 := h 0 1 le_rfl zero_le_one
  have e11 := h 1 1 zero_le_one zero_le_one
  have key : Real.exp (1 + 1 / 2 * 1) - Real.exp (1 + 1 / 2 * 0) - Real.exp (0 + 1 / 2 * 1)
      + Real.exp (0 + 1 / 2 * 0) = 0 := by
    rw [e00, e10, e01, e11]; ring
  have hfac : Real.exp (1 + 1 / 2 * 1) - Real.exp (1 + 1 / 2 * 0) - Real.exp (0 + 1 / 2 * 1)
      + Real.exp (0 + 1 / 2 * 0) = (Real.exp 1 - 1) * (Real.exp (1 / 2) - 1) := by
    simp only [mul_one, mul_zero, add_zero, zero_add, Real.exp_zero]
    rw [Real.exp_add]; ring
  rw [hfac] at key
  have h1 : 0 < Real.exp 1 - 1 := by
    have := Real.add_one_lt_exp (one_ne_zero); linarith
  have h2 : 0 < Real.exp (1 / 2) - 1 := by
    have := Real.add_one_lt_exp (by norm_num : (1 / 2 : ℝ) ≠ 0); linarith
  exact absurd key (mul_pos h1 h2).ne'

end MWG.EquilibriumTime

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Intertemporal production and efficiency (MWG Section 20.C)

MWG, Chapter 20, Section 20.C, pp. 736-743, Exercises 20.C.1-20.C.5(a) (p. 783).

Commodities are indexed by a finite type `ι` (MWG's `L` goods; `ι = Fin L`). A production
plan is a pair `y = (y_b, y_a) ∈ ℝ^L × ℝ^L` (`ProdPlan ι`), "before" and "after". A
production path is `y : ℕ → ProdPlan ι` with `y t ∈ Y`; its net input-output vector at `t` is
`y_{a,t-1} + y_{b,t}` with `y_{a,-1} = 0` (`netOutput`), and its profit at `t` for a price
sequence `p : ℕ → ι → ℝ` is `p_t · y_{bt} + p_{t+1} · y_{at}` (`periodProfit`).

* Assumptions (i)-(iv) on `Y` (`TechAssumptions`), with bridges to Chapter 5's no free lunch and
  free disposal (`noFreeLunch_iff_stack`, `freeDisposal_iff_stack`) and the remark that
  `y_a ≥ 0` makes truncation a consequence of free disposal (`truncation_of_nonneg_after`).
* Examples 20.C.1-20.C.4: `ramseySolowSet` (with `example_20_C_1`, a proved instance of
  `TechAssumptions`), `costAdjustmentSet`, `twoSectorSet`, `multiSectorSet`
  (`example_20_C_3_costAdjustment`, `example_20_C_3_ramseySolow`).
* Definitions 20.C.1-20.C.3: `IsProdPath`, `ProdEfficient`, `MyopicProfitMax`; the
  transversality condition `Transversality`.
* The rearrangement identity behind Proposition 20.C.1 and (20.D.1): `sum_value_netOutput`.
* Example 20.C.5 (storage): `example_20_C_5`.
* **Proposition 20.C.1**: `proposition_20_C_1`; efficient plans are on the boundary of `Y`
  (`prodEfficient_not_mem_interior`).
* Exercises 20.C.1 (`ownRate`), 20.C.2, 20.C.3, 20.C.4(a)-(b) and 20.C.5(a).
-/

open Filter Topology

namespace MWG.EquilibriumTime

variable {ι : Type*} [Fintype ι]

/-- A **production plan** `y = (y_b, y_a) ∈ ℝ^{2L}` (MWG, p. 737): `y.1 = y_b` is the plan for
the initial period and `y.2 = y_a` the plan for the last period. -/
abbrev ProdPlan (ι : Type*) := (ι → ℝ) × (ι → ℝ)

/-- A vector is **strictly positive** (`p ≫ 0`). -/
def StrictPos (v : ι → ℝ) : Prop := ∀ i, 0 < v i

/-- Strictly positive prices value a nonzero nonnegative vector strictly positively. -/
theorem dotProduct_pos_of_strictPos {p v : ι → ℝ} (hp : StrictPos p) (hv : 0 ≤ v)
    (hne : v ≠ 0) : 0 < p ⬝ᵥ v := by
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (funext h)
  refine Finset.sum_pos' (fun j _ => mul_nonneg (hp j).le (hv j)) ⟨i, Finset.mem_univ _, ?_⟩
  exact mul_pos (hp i) (lt_of_le_of_ne (hv i) (Ne.symm hi))

/-- **Assumptions (i)-(iv)** on the one-period technology `Y ⊆ ℝ^{2L}` (MWG, p. 737). -/
structure TechAssumptions (Y : Set (ProdPlan ι)) : Prop where
  /-- (i) `Y` is closed. -/
  isClosed : IsClosed Y
  /-- (i) `Y` is convex. -/
  convex : Convex ℝ Y
  /-- (ii) No free lunch, `Y ∩ ℝ^{2L}_+ = {0}`: the inclusion `⊇` (inaction is possible). -/
  zero_mem : (0 : ProdPlan ι) ∈ Y
  /-- (ii) No free lunch, `Y ∩ ℝ^{2L}_+ = {0}`: the inclusion `⊆`. -/
  noFreeLunch : ∀ y ∈ Y, 0 ≤ y → y = 0
  /-- (iii) Free disposal: `Y - ℝ^{2L}_+ ⊆ Y`. -/
  freeDisposal : ∀ y ∈ Y, ∀ y', y' ≤ y → y' ∈ Y
  /-- (iv) Possibility of truncation: `(y_b, y_a) ∈ Y` implies `(y_b, 0) ∈ Y`. -/
  truncation : ∀ y ∈ Y, (y.1, 0) ∈ Y

omit [Fintype ι] in
/-- **Remark on (iv)** (MWG, p. 737): when `y_a ≥ 0` for every `y ∈ Y`, truncation follows from
free disposal. -/
theorem truncation_of_nonneg_after {Y : Set (ProdPlan ι)}
    (hfd : ∀ y ∈ Y, ∀ y', y' ≤ y → y' ∈ Y) (hpos : ∀ y ∈ Y, 0 ≤ y.2) :
    ∀ y ∈ Y, (y.1, 0) ∈ Y :=
  fun y hy => hfd y hy _ ⟨le_rfl, hpos y hy⟩

/-! ### Bridge to Chapter 5 -/

/-- Stacking a plan `(y_b, y_a)` into one vector of `ℝ^{L+L}` (MWG, p. 737: `Y ⊂ ℝ^{2L}`). -/
def stackPlan {L : ℕ} (y : ProdPlan (Fin L)) : Fin (L + L) → ℝ := Fin.append y.1 y.2

theorem stackPlan_le_iff {L : ℕ} (y z : ProdPlan (Fin L)) :
    stackPlan y ≤ stackPlan z ↔ y ≤ z := by
  constructor
  · intro h
    refine ⟨fun i => ?_, fun i => ?_⟩
    · have := h (Fin.castAdd L i)
      simpa [stackPlan, Fin.append_left] using this
    · have := h (Fin.natAdd L i)
      simp only [stackPlan, Fin.append_right] at this
      exact this
  · rintro ⟨h1, h2⟩ i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa [stackPlan, Fin.append_left] using h1 j
    · simp only [stackPlan, Fin.append_right]
      exact h2 j

theorem stackPlan_zero {L : ℕ} : stackPlan (0 : ProdPlan (Fin L)) = 0 := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [stackPlan, Fin.append_left, Prod.fst_zero, Pi.zero_apply]
  · simp only [stackPlan, Fin.append_right, Prod.snd_zero, Pi.zero_apply]

theorem stackPlan_injective {L : ℕ} : Function.Injective (stackPlan (L := L)) := by
  intro y z h
  exact le_antisymm ((stackPlan_le_iff y z).1 h.le) ((stackPlan_le_iff z y).1 h.ge)

theorem stackPlan_surjective {L : ℕ} (v : Fin (L + L) → ℝ) :
    stackPlan (fun i => v (Fin.castAdd L i), fun i => v (Fin.natAdd L i)) = v :=
  Fin.append_castAdd_natAdd

/-- Assumption (ii) is Chapter 5's no-free-lunch property of the stacked set. -/
theorem noFreeLunch_iff_stack {L : ℕ} (Y : Set (ProdPlan (Fin L))) :
    (∀ y ∈ Y, 0 ≤ y → y = 0) ↔ MWG.Production.NoFreeLunch (stackPlan '' Y) := by
  constructor
  · rintro h _ ⟨y, hy, rfl⟩ h0
    rw [← stackPlan_zero] at h0 ⊢
    rw [h y hy ((stackPlan_le_iff _ _).1 h0)]
  · intro h y hy h0
    apply stackPlan_injective
    rw [stackPlan_zero]
    exact h _ ⟨y, hy, rfl⟩ (by rw [← stackPlan_zero]; exact (stackPlan_le_iff _ _).2 h0)

/-- Assumption (iii) is Chapter 5's free disposal of the stacked set. -/
theorem freeDisposal_iff_stack {L : ℕ} (Y : Set (ProdPlan (Fin L))) :
    (∀ y ∈ Y, ∀ y', y' ≤ y → y' ∈ Y) ↔ MWG.Production.FreeDisposal (stackPlan '' Y) := by
  constructor
  · rintro h _ ⟨y, hy, rfl⟩ v hv
    refine ⟨_, h y hy _ ?_, stackPlan_surjective v⟩
    rw [← stackPlan_le_iff, stackPlan_surjective]
    exact hv
  · intro h y hy y' hle
    obtain ⟨z, hz, hzy⟩ := h _ ⟨y, hy, rfl⟩ _ ((stackPlan_le_iff _ _).2 hle)
    rwa [stackPlan_injective hzy] at hz

/-! ### Examples 20.C.1-20.C.4 -/

/-- **Example 20.C.1** (MWG, p. 737), the Ramsey-Solow technology: goods `0` (consumption-
investment good) and `1` (labor), `Y = {(-k, -l, x, 0) : k, l ≥ 0, x ≤ F(k, l)} - ℝ^4_+`, with
the production function written `F ![k, l]`. -/
def ramseySolowSet (F : (Fin 2 → ℝ) → ℝ) : Set (ProdPlan (Fin 2)) :=
  {y | ∃ k l x : ℝ, 0 ≤ k ∧ 0 ≤ l ∧ x ≤ F ![k, l] ∧ y ≤ (![-k, -l], ![x, 0])}

/-- With a nondecreasing production function the Ramsey-Solow set is
`{y : y_b ≤ 0, y_{a,1} ≤ 0, y_{a,0} ≤ F(-y_b)}`. -/
theorem ramseySolowSet_eq {F : (Fin 2 → ℝ) → ℝ}
    (hmono : MonotoneOn F (Set.Ici 0)) :
    ramseySolowSet F = {y | y.1 ≤ 0 ∧ y.2 1 ≤ 0 ∧ y.2 0 ≤ F (-y.1)} := by
  ext ⟨yb, ya⟩
  simp only [ramseySolowSet]
  constructor
  · rintro ⟨k, l, x, hk, hl, hx, hb, ha⟩
    have hb0 : yb 0 ≤ -k := by simpa using hb 0
    have hb1 : yb 1 ≤ -l := by simpa using hb 1
    have ha0 : ya 0 ≤ x := by simpa using ha 0
    have ha1 : ya 1 ≤ 0 := by simpa using ha 1
    refine ⟨fun i => ?_, ha1, ?_⟩
    · fin_cases i
      · simp; linarith
      · simp; linarith
    · have hle : ![k, l] ≤ -yb := by
        intro i; fin_cases i
        · simp; linarith
        · simp; linarith
      have h0 : (0 : Fin 2 → ℝ) ≤ ![k, l] := by
        intro i; fin_cases i <;> simp [hk, hl]
      exact ha0.trans (hx.trans (hmono h0 (h0.trans hle) hle))
  · rintro ⟨hb, ha1, ha0⟩
    have hb0 : yb 0 ≤ 0 := hb 0
    have hb1 : yb 1 ≤ 0 := hb 1
    refine ⟨-yb 0, -yb 1, ya 0, by linarith, by linarith, ?_, fun i => ?_,
      fun i => ?_⟩
    · convert ha0 using 2
      funext i; fin_cases i <;> simp
    · fin_cases i <;> simp
    · fin_cases i
      · simp
      · simpa using ha1

/-- **Example 20.C.1** (MWG, p. 737): labor is a primary factor, it cannot be produced. -/
theorem ramseySolow_labor_primary {F : (Fin 2 → ℝ) → ℝ} :
    ∀ y ∈ ramseySolowSet F, y.1 1 ≤ 0 ∧ y.2 1 ≤ 0 := by
  rintro y ⟨k, l, x, hk, hl, -, hb, ha⟩
  have h1 : y.1 1 ≤ -l := by simpa using hb 1
  have h2 : y.2 1 ≤ 0 := by simpa using ha 1
  exact ⟨by linarith, h2⟩

/-- **Example 20.C.1** (MWG, p. 737): the Ramsey-Solow technology satisfies assumptions (i)-(iv)
when `F` is continuous, concave and nondecreasing on `ℝ²_+` with `F(0, 0) = 0`. -/
theorem example_20_C_1 {F : (Fin 2 → ℝ) → ℝ} (hcont : Continuous F)
    (hconc : ConcaveOn ℝ (Set.Ici 0) F) (hmono : MonotoneOn F (Set.Ici 0)) (h00 : F 0 = 0) :
    TechAssumptions (ramseySolowSet F) := by
  rw [ramseySolowSet_eq hmono]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine IsClosed.inter (isClosed_le continuous_fst continuous_const) ?_
    refine IsClosed.inter (isClosed_le ((continuous_apply 1).comp continuous_snd)
      continuous_const) ?_
    exact isClosed_le ((continuous_apply 0).comp continuous_snd)
      (hcont.comp continuous_fst.neg)
  · rintro ⟨yb, ya⟩ ⟨hb, ha1, ha0⟩ ⟨zb, za⟩ ⟨hb', ha1', ha0'⟩ a b ha hb'' hab
    refine ⟨?_, ?_, ?_⟩
    · intro i
      have h1 : yb i ≤ 0 := hb i
      have h2 : zb i ≤ 0 := hb' i
      simp only [Prod.smul_mk, Prod.mk_add_mk, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Pi.zero_apply]
      nlinarith
    · simp only [Prod.smul_mk, Prod.mk_add_mk, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      nlinarith
    · simp only [Prod.smul_mk, Prod.mk_add_mk, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have hyb : -yb ∈ Set.Ici (0 : Fin 2 → ℝ) := fun i => by simpa using hb i
      have hzb : -zb ∈ Set.Ici (0 : Fin 2 → ℝ) := fun i => by simpa using hb' i
      have := hconc.2 hyb hzb ha hb'' hab
      have heq : -(a • yb + b • zb) = a • -yb + b • -zb := by
        rw [neg_add, smul_neg, smul_neg]
      simp only [smul_eq_mul] at this
      rw [heq]
      nlinarith
  · refine ⟨le_rfl, le_rfl, ?_⟩
    simp [h00]
  · rintro ⟨yb, ya⟩ ⟨hb, ha1, ha0⟩ ⟨h0b, h0a⟩
    have hyb : yb = 0 := le_antisymm hb h0b
    subst hyb
    have : ya 0 ≤ 0 := by simpa [h00] using ha0
    refine Prod.ext rfl (funext fun i => ?_)
    fin_cases i
    · exact le_antisymm this (h0a 0)
    · exact le_antisymm ha1 (h0a 1)
  · rintro ⟨yb, ya⟩ ⟨hb, ha1, ha0⟩ ⟨zb, za⟩ ⟨hzb, hza⟩
    refine ⟨hzb.trans hb, (hza 1).trans ha1, (hza 0).trans (ha0.trans ?_)⟩
    have h0 : (0 : Fin 2 → ℝ) ≤ -yb := fun i => by simpa using hb i
    exact hmono h0 (h0.trans (neg_le_neg hzb)) (neg_le_neg hzb)
  · rintro ⟨yb, ya⟩ ⟨hb, ha1, ha0⟩
    refine ⟨hb, le_rfl, ?_⟩
    have h0 : (0 : Fin 2 → ℝ) ≤ -yb := fun i => by simpa using hb i
    simpa [h00] using hmono (le_refl (0 : Fin 2 → ℝ)) h0 h0

/-- **Example 20.C.3** (MWG, p. 738), the two-sector technology: goods `0` (capacity), `1`
(consumption) and `2` (labor), `Y = {(-k, 0, -l, k', x, 0) : k, l, k' ≥ 0, x ≤ G(k, l, k')}
- ℝ^6_+`. -/
def twoSectorSet (G : ℝ → ℝ → ℝ → ℝ) : Set (ProdPlan (Fin 3)) :=
  {y | ∃ k l k' x : ℝ, 0 ≤ k ∧ 0 ≤ l ∧ 0 ≤ k' ∧ x ≤ G k l k' ∧
    y ≤ (![-k, 0, -l], ![k', x, 0])}

/-- **Example 20.C.2** (MWG, p. 737), the cost-of-adjustment technology:
`Y = {(-k, 0, -l, k', x, 0) : k, l, k' ≥ 0, x ≤ F(k, l) - k' - γ(k' - k)} - ℝ^6_+`. -/
def costAdjustmentSet (F : ℝ → ℝ → ℝ) (γ : ℝ → ℝ) : Set (ProdPlan (Fin 3)) :=
  {y | ∃ k l k' x : ℝ, 0 ≤ k ∧ 0 ≤ l ∧ 0 ≤ k' ∧ x ≤ F k l - k' - γ (k' - k) ∧
    y ≤ (![-k, 0, -l], ![k', x, 0])}

/-- **Example 20.C.3** (MWG, p. 738): the cost-of-adjustment model is the two-sector model with
`G(k, l, k') = F(k, l) - k' - γ(k' - k)`. -/
theorem example_20_C_3_costAdjustment (F : ℝ → ℝ → ℝ) (γ : ℝ → ℝ) :
    costAdjustmentSet F γ = twoSectorSet (fun k l k' => F k l - k' - γ (k' - k)) := rfl

/-- Merging the capacity and consumption goods of the two-sector model into the single
consumption-investment good of the Ramsey-Solow model. -/
def mergeGoods (y : ProdPlan (Fin 3)) : ProdPlan (Fin 2) :=
  (![y.1 0 + y.1 1, y.1 2], ![y.2 0 + y.2 1, y.2 2])

/-- **Example 20.C.3** (MWG, p. 738): with `G(k, l, k') = F(k, l) - k'` (investment and
consumption goods perfect substitutes in production) the two-sector model is the Ramsey-Solow
model: merging the two goods maps the two-sector set exactly onto the Ramsey-Solow set. -/
theorem example_20_C_3_ramseySolow (F : (Fin 2 → ℝ) → ℝ) :
    mergeGoods '' twoSectorSet (fun k l k' => F ![k, l] - k') = ramseySolowSet F := by
  ext z
  constructor
  · rintro ⟨y, ⟨k, l, k', x, hk, hl, hk', hx, hb, ha⟩, rfl⟩
    refine ⟨k, l, x + k', hk, hl, by linarith, fun i => ?_, fun i => ?_⟩
    · have h0 := hb 0; have h1 := hb 1; have h2 := hb 2
      simp at h0 h1 h2
      fin_cases i <;> simp [mergeGoods] <;> linarith
    · have h0 := ha 0; have h1 := ha 1; have h2 := ha 2
      simp at h0 h1 h2
      fin_cases i <;> simp [mergeGoods] <;> linarith
  · rintro ⟨k, l, x, hk, hl, hx, hb, ha⟩
    refine ⟨(![z.1 0, 0, z.1 1], ![0, z.2 0, z.2 1]), ⟨k, l, 0, x, hk, hl, le_rfl,
      by simpa using hx, fun i => ?_, fun i => ?_⟩, ?_⟩
    · have h0 := hb 0; have h1 := hb 1
      simp at h0 h1
      fin_cases i <;> simp <;> linarith
    · have h0 := ha 0; have h1 := ha 1
      simp at h0 h1
      fin_cases i <;> simp <;> linarith
    · refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;>
        fin_cases i <;> simp [mergeGoods]

/-- **Example 20.C.4** (MWG, p. 738), the `(N + 1)`-sector technology: `N` capital goods
(`Sum.inl`), the consumption good (`Sum.inr 0`) and labor (`Sum.inr 1`);
`Y = {(-k, 0, -l, k', x, 0) : (k, l, k') ∈ A, x ≤ G(k, l, k')} - ℝ^{2(N+2)}_+` for an admissible
domain `A`. -/
def multiSectorSet (N : ℕ) (A : Set ((Fin N → ℝ) × ℝ × (Fin N → ℝ)))
    (G : (Fin N → ℝ) → ℝ → (Fin N → ℝ) → ℝ) : Set (ProdPlan (Fin N ⊕ Fin 2)) :=
  {y | ∃ k l k' x, (k, l, k') ∈ A ∧ x ≤ G k l k' ∧
    y ≤ (Sum.elim (fun n => -k n) ![0, -l], Sum.elim k' ![x, 0])}

/-! ### Production paths and prices -/

/-- **Definition 20.C.1** (MWG, p. 738): a production path is a sequence of plans in `Y`. -/
def IsProdPath (Y : Set (ProdPlan ι)) (y : ℕ → ProdPlan ι) : Prop := ∀ t, y t ∈ Y

/-- The net input-output vector `y_{a,t-1} + y_{b,t}` of a path at `t`, with `y_{a,-1} = 0`
(MWG, p. 738). -/
def netOutput (y : ℕ → ProdPlan ι) : ℕ → ι → ℝ
  | 0 => (y 0).1
  | t + 1 => (y t).2 + (y (t + 1)).1

/-- **Definition 20.C.2** (MWG, p. 739): a path is efficient if no other path has net outputs at
least as large at every date and different at some date. -/
def ProdEfficient (Y : Set (ProdPlan ι)) (y : ℕ → ProdPlan ι) : Prop :=
  IsProdPath Y y ∧ ¬ ∃ y', IsProdPath Y y' ∧ (∀ t, netOutput y t ≤ netOutput y' t) ∧
    netOutput y' ≠ netOutput y

/-- The value of a plan at the prices `(p_t, p_{t+1})`. -/
def planValue (pb pa : ι → ℝ) (z : ProdPlan ι) : ℝ := pb ⬝ᵥ z.1 + pa ⬝ᵥ z.2

/-- The profit `p_t · y_{bt} + p_{t+1} · y_{at}` of the plan at `t` (MWG, p. 739). -/
def periodProfit (p : ℕ → ι → ℝ) (y : ℕ → ProdPlan ι) (t : ℕ) : ℝ :=
  planValue (p t) (p (t + 1)) (y t)

/-- **Definition 20.C.3** (MWG, p. 739): `y` is myopically (short-run) profit maximizing for
`p` if every `y_t` maximizes `p_t · y_b + p_{t+1} · y_a` on `Y`; `p` is then a system of
**Malinvaud prices** for `y`. -/
def MyopicProfitMax (Y : Set (ProdPlan ι)) (p : ℕ → ι → ℝ) (y : ℕ → ProdPlan ι) : Prop :=
  IsProdPath Y y ∧ ∀ t, ∀ z ∈ Y, planValue (p t) (p (t + 1)) z ≤ periodProfit p y t

/-- The **transversality condition** `p_{t+1} · y_{at} → 0` (MWG, p. 740). -/
def Transversality (p : ℕ → ι → ℝ) (y : ℕ → ProdPlan ι) : Prop :=
  Tendsto (fun t => p (t + 1) ⬝ᵥ (y t).2) atTop (𝓝 0)

/-- **The rearrangement identity** (MWG, pp. 740 and 744): matching inputs and outputs per period
instead of per plan, `∑_{t ≤ T} p_t · (y_{a,t-1} + y_{bt}) = ∑_{t ≤ T} π_t - p_{T+1} · y_{aT}`. -/
theorem sum_value_netOutput (p : ℕ → ι → ℝ) (y : ℕ → ProdPlan ι) (T : ℕ) :
    ∑ t ∈ Finset.range (T + 1), p t ⬝ᵥ netOutput y t
      = ∑ t ∈ Finset.range (T + 1), periodProfit p y t - p (T + 1) ⬝ᵥ (y T).2 := by
  induction T with
  | zero => simp [netOutput, periodProfit, planValue]
  | succ T ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ (fun t => periodProfit p y t) (T + 1)]
    simp only [netOutput, periodProfit, planValue, dotProduct_add]
    ring

/-- The identity in the form "truncate the last plan":
`∑_{t ≤ T} p_t · n_t = ∑_{t < T} π_t + p_T · y_{bT}`. -/
theorem sum_value_netOutput' (p : ℕ → ι → ℝ) (y : ℕ → ProdPlan ι) (T : ℕ) :
    ∑ t ∈ Finset.range (T + 1), p t ⬝ᵥ netOutput y t
      = ∑ t ∈ Finset.range T, periodProfit p y t + p T ⬝ᵥ (y T).1 := by
  rw [sum_value_netOutput, Finset.sum_range_succ]
  simp only [periodProfit, planValue]
  ring

/-- **The key inequality** of the proof of Proposition 20.C.1 (MWG, p. 740): if `y` is myopically
profit maximizing and `Y` allows truncation, then for any path `y'` and any `T`,
`∑_{t ≤ T} p_t · n'_t ≤ ∑_{t ≤ T} p_t · n_t + p_{T+1} · y_{aT}`. -/
theorem sum_value_le_of_myopic {Y : Set (ProdPlan ι)} {p : ℕ → ι → ℝ}
    {y y' : ℕ → ProdPlan ι} (htr : ∀ z ∈ Y, (z.1, 0) ∈ Y) (hy : MyopicProfitMax Y p y)
    (hy' : IsProdPath Y y') (T : ℕ) :
    ∑ t ∈ Finset.range (T + 1), p t ⬝ᵥ netOutput y' t
      ≤ ∑ t ∈ Finset.range (T + 1), p t ⬝ᵥ netOutput y t + p (T + 1) ⬝ᵥ (y T).2 := by
  rw [sum_value_netOutput' p y', sum_value_netOutput p y, sub_add_cancel,
    Finset.sum_range_succ]
  have h1 : ∑ t ∈ Finset.range T, periodProfit p y' t ≤ ∑ t ∈ Finset.range T, periodProfit p y t :=
    Finset.sum_le_sum fun t _ => hy.2 t _ (hy' t)
  have h2 : p T ⬝ᵥ (y' T).1 ≤ periodProfit p y T := by
    have := hy.2 T _ (htr _ (hy' T))
    simpa [planValue] using this
  linarith

/-- The common core of Proposition 20.C.1 and Exercise 20.C.3: under myopic profit maximization,
truncation and the transversality condition, no path `y'` can have `p_t · n'_t ≥ p_t · n_t` at
every date with strict inequality at some date. -/
theorem no_value_improvement {Y : Set (ProdPlan ι)} {p : ℕ → ι → ℝ}
    {y y' : ℕ → ProdPlan ι} (htr : ∀ z ∈ Y, (z.1, 0) ∈ Y) (hy : MyopicProfitMax Y p y)
    (htc : Transversality p y) (hy' : IsProdPath Y y')
    (hge : ∀ t, p t ⬝ᵥ netOutput y t ≤ p t ⬝ᵥ netOutput y' t) {s : ℕ}
    (hs : p s ⬝ᵥ netOutput y s < p s ⬝ᵥ netOutput y' s) : False := by
  set ε := p s ⬝ᵥ netOutput y' s - p s ⬝ᵥ netOutput y s with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  have hgap : ∀ T, s ≤ T → ε ≤ p (T + 1) ⬝ᵥ (y T).2 := by
    intro T hT
    have hsum : ∑ t ∈ Finset.range (T + 1), p t ⬝ᵥ netOutput y t + ε
        ≤ ∑ t ∈ Finset.range (T + 1), p t ⬝ᵥ netOutput y' t := by
      have hmem : s ∈ Finset.range (T + 1) := Finset.mem_range.2 (Nat.lt_succ_of_le hT)
      rw [← sub_nonneg, ← sub_sub, ← Finset.sum_sub_distrib]
      have := Finset.single_le_sum (f := fun t => p t ⬝ᵥ netOutput y' t - p t ⬝ᵥ netOutput y t)
        (fun t _ => sub_nonneg.2 (hge t)) hmem
      linarith
    have := sum_value_le_of_myopic htr hy hy' T
    linarith
  have hev := (htc.eventually (gt_mem_nhds hεpos))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  have h1 := hN (max N s) (le_max_left _ _)
  have h2 := hgap (max N s) (le_max_right _ _)
  linarith

/-- **Proposition 20.C.1** (MWG, p. 740): a path that is myopically profit maximizing for a price
sequence `p ≫ 0` and satisfies the transversality condition is efficient. Truncation, assumption
(iv), is the only property of `Y` used. -/
theorem proposition_20_C_1 {Y : Set (ProdPlan ι)} {p : ℕ → ι → ℝ} {y : ℕ → ProdPlan ι}
    (htr : ∀ z ∈ Y, (z.1, 0) ∈ Y) (hp : ∀ t, StrictPos (p t)) (hy : MyopicProfitMax Y p y)
    (htc : Transversality p y) : ProdEfficient Y y := by
  refine ⟨hy.1, fun ⟨y', hy', hle, hne⟩ => ?_⟩
  obtain ⟨s, hs⟩ : ∃ s, netOutput y' s ≠ netOutput y s := by
    by_contra h
    push Not at h
    exact hne (funext h)
  refine no_value_improvement htr hy htc hy' (fun t => ?_) (s := s) ?_
  · exact dotProduct_le_dotProduct_of_nonneg_left (hle t) (fun i => (hp t i).le)
  · have := dotProduct_pos_of_strictPos (hp s) (sub_nonneg.2 (hle s)) (sub_ne_zero.2 hs)
    rw [dotProduct_sub] at this
    linarith

omit [Fintype ι] in
/-- Efficient plans lie on the boundary of `Y` (MWG, p. 742): no `y_t` of an efficient path is in
the interior of `Y` (otherwise the output `y_{a,t}` could be raised). -/
theorem prodEfficient_not_mem_interior [Finite ι] [Nonempty ι] {Y : Set (ProdPlan ι)}
    {y : ℕ → ProdPlan ι} (hy : ProdEfficient Y y) (t : ℕ) : y t ∉ interior Y := by
  have := Fintype.ofFinite ι
  intro hint
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior (y t) hint
  set e : ProdPlan ι := (0, fun _ => ε / 2) with he
  have hmem : y t + e ∈ Y := by
    apply interior_subset
    apply hball
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
    have hn : ‖e‖ ≤ ε / 2 := by
      rw [he, Prod.norm_def]
      refine max_le (by simp; linarith) ?_
      refine (pi_norm_le_iff_of_nonneg (by linarith)).2 fun i => ?_
      rw [Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith
  set y' : ℕ → ProdPlan ι := Function.update y t (y t + e) with hy'
  have hpath : IsProdPath Y y' := by
    intro s
    by_cases hs : s = t
    · subst hs; simp [hy', hmem]
    · simp [hy', hs, hy.1 s]
  refine hy.2 ⟨y', hpath, fun s => ?_, fun h => ?_⟩
  · cases s with
    | zero =>
      by_cases h0 : t = 0
      · subst h0; simp [netOutput, hy', he]
      · simp [netOutput, hy', Ne.symm h0]
    | succ s =>
      simp only [netOutput, hy']
      by_cases h1 : s = t
      · subst h1
        intro i
        simp [he]
        linarith
      · by_cases h2 : s + 1 = t
        · subst h2; simp [he]
        · simp [Function.update_of_ne h1, Function.update_of_ne h2]
  · have := congrFun (congrFun h (t + 1)) (Classical.arbitrary ι)
    have ht : t + 1 ≠ t := by omega
    simp [netOutput, hy', he] at this
    linarith

/-! ### Example 20.C.5: storage -/

/-- The storage technology of Example 20.C.5 (MWG, p. 740), `L = 1`:
`Y = {(-k, k') : k ≥ 0, k' ≤ k}`. -/
def storageSet : Set (ProdPlan (Fin 1)) :=
  {y | ∃ k k', 0 ≤ k ∧ k' ≤ k ∧ y = (fun _ => -k, fun _ => k')}

theorem storageSet_eq : storageSet = {y | y.1 0 ≤ 0 ∧ y.2 0 ≤ -y.1 0} := by
  ext ⟨yb, ya⟩
  constructor
  · rintro ⟨k, k', hk, hk', h⟩
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp; constructor <;> linarith
  · rintro ⟨h1, h2⟩
    refine ⟨-yb 0, ya 0, by linarith, by linarith, ?_⟩
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> fin_cases i <;> simp

/-- The storage technology satisfies assumptions (i)-(iv). -/
theorem storageSet_techAssumptions : TechAssumptions storageSet := by
  rw [storageSet_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact IsClosed.inter (isClosed_le ((continuous_apply 0).comp continuous_fst)
      continuous_const) (isClosed_le ((continuous_apply 0).comp continuous_snd)
      ((continuous_apply 0).comp continuous_fst).neg)
  · rintro ⟨yb, ya⟩ ⟨h1, h2⟩ ⟨zb, za⟩ ⟨h1', h2'⟩ a b ha hb hab
    dsimp only at h1 h2 h1' h2'
    refine ⟨?_, ?_⟩
    · change a * yb 0 + b * zb 0 ≤ 0
      nlinarith
    · change a * ya 0 + b * za 0 ≤ -(a * yb 0 + b * zb 0)
      nlinarith
  · exact ⟨le_rfl, by simp⟩
  · rintro ⟨yb, ya⟩ ⟨h1, h2⟩ ⟨h0b, h0a⟩
    have hb : yb 0 = 0 := le_antisymm h1 (h0b 0)
    have ha : ya 0 = 0 := le_antisymm (by linarith) (h0a 0)
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> fin_cases i <;> simp [hb, ha]
  · rintro ⟨yb, ya⟩ ⟨h1, h2⟩ ⟨zb, za⟩ ⟨hzb, hza⟩
    exact ⟨(hzb 0).trans h1, by linarith [hzb 0, hza 0]⟩
  · rintro ⟨yb, ya⟩ ⟨h1, h2⟩
    exact ⟨h1, by simp; linarith⟩

/-- The path of Example 20.C.5: carry one unit forward forever, `y_t = (-1, 1)`. -/
def storagePath : ℕ → ProdPlan (Fin 1) := fun _ => (fun _ => -1, fun _ => 1)

/-- **Example 20.C.5** (MWG, p. 740): the storage path `y_t = (-1, 1)` is a production path with
net outputs `-1` at `t = 0` and `0` afterwards; it is not efficient (the path `y'_t = 0`
dominates it); yet it is myopically profit maximizing for the constant prices `p_t = 1`, and the
transversality condition fails. -/
theorem example_20_C_5 :
    IsProdPath storageSet storagePath ∧
      netOutput storagePath 0 = (fun _ => -1) ∧ (∀ t, netOutput storagePath (t + 1) = 0) ∧
      ¬ ProdEfficient storageSet storagePath ∧
      MyopicProfitMax storageSet (fun _ _ => 1) storagePath ∧
      ¬ Transversality (fun _ _ => 1) storagePath := by
  have hpath : IsProdPath storageSet storagePath := fun t =>
    ⟨1, 1, zero_le_one, le_rfl, rfl⟩
  have h0 : netOutput storagePath 0 = fun _ => -1 := rfl
  have hs : ∀ t, netOutput storagePath (t + 1) = 0 := by
    intro t; funext i; simp [netOutput, storagePath]
  refine ⟨hpath, h0, hs, ?_, ⟨hpath, ?_⟩, ?_⟩
  · rintro ⟨-, hne⟩
    refine hne ⟨fun _ => 0, fun t => ⟨0, 0, le_rfl, le_rfl, by ext <;> simp⟩, fun t => ?_, ?_⟩
    · cases t with
      | zero => intro i; simp [netOutput, storagePath]
      | succ t => rw [hs t]; intro i; simp [netOutput]
    · intro h
      have := congrFun (congrFun h 0) 0
      simp [netOutput, storagePath] at this
  · rintro t z hz
    rw [storageSet_eq] at hz
    obtain ⟨h1, h2⟩ := hz
    simp [periodProfit, planValue, storagePath, dotProduct]
    linarith
  · intro h
    have : (fun t : ℕ => (fun _ : Fin 1 => (1 : ℝ)) ⬝ᵥ (storagePath t).2) = fun _ => 1 := by
      funext t; simp [storagePath, dotProduct]
    unfold Transversality at h
    rw [this] at h
    exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds h)

/-! ### Exercises 20.C.1-20.C.5(a) -/

/-- **Exercise 20.C.1** (MWG, p. 783): the own rate of interest of commodity `l` from `t` to
`t + 1`, defined by `p_{t,l} = (1 + r_{t,l}) p_{t+1,l}`. -/
noncomputable def ownRate (p : ℕ → ι → ℝ) (t : ℕ) (l : ι) : ℝ := p t l / p (t + 1) l - 1

omit [Fintype ι] in
/-- **Exercise 20.C.1** (MWG, p. 783): the own rate satisfies `p_{t,l} = (1 + r_{t,l})
p_{t+1,l}`, and is the unique number doing so. -/
theorem exercise_20_C_1 (p : ℕ → ι → ℝ) (t : ℕ) (l : ι) (hp : p (t + 1) l ≠ 0) :
    p t l = (1 + ownRate p t l) * p (t + 1) l ∧
      ∀ r, p t l = (1 + r) * p (t + 1) l → r = ownRate p t l := by
  refine ⟨by unfold ownRate; field_simp; ring, fun r hr => ?_⟩
  unfold ownRate
  rw [hr]
  field_simp
  ring

/-- **Exercise 20.C.2** (MWG, p. 783): a myopically profit maximizing path is also profit
maximizing over any finite horizon: for any `T`, no path changes the total profits of the first
`T` periods upward. -/
theorem exercise_20_C_2 {Y : Set (ProdPlan ι)} {p : ℕ → ι → ℝ} {y : ℕ → ProdPlan ι}
    (hy : MyopicProfitMax Y p y) {y' : ℕ → ProdPlan ι} (hy' : IsProdPath Y y') (T : ℕ) :
    ∑ t ∈ Finset.range T, periodProfit p y' t ≤ ∑ t ∈ Finset.range T, periodProfit p y t :=
  Finset.sum_le_sum fun t _ => hy.2 t _ (hy' t)

/-- **Exercise 20.C.3** (MWG, p. 783), weak efficiency: no path has net outputs strictly larger
in every commodity at every date. -/
def ProdWeaklyEfficient (Y : Set (ProdPlan ι)) (y : ℕ → ProdPlan ι) : Prop :=
  IsProdPath Y y ∧ ¬ ∃ y', IsProdPath Y y' ∧ ∀ t i, netOutput y t i < netOutput y' t i

/-- **Exercise 20.C.3** (MWG, p. 783): Proposition 20.C.1 with `p ≥ 0` having some nonzero entry
gives weak efficiency. -/
theorem exercise_20_C_3 {Y : Set (ProdPlan ι)} {p : ℕ → ι → ℝ} {y : ℕ → ProdPlan ι}
    (htr : ∀ z ∈ Y, (z.1, 0) ∈ Y) (hp : ∀ t, 0 ≤ p t) {s : ℕ} (hps : p s ≠ 0)
    (hy : MyopicProfitMax Y p y) (htc : Transversality p y) : ProdWeaklyEfficient Y y := by
  refine ⟨hy.1, fun ⟨y', hy', hlt⟩ => ?_⟩
  refine no_value_improvement htr hy htc hy' (fun t => ?_) (s := s) ?_
  · exact dotProduct_le_dotProduct_of_nonneg_left (fun i => (hlt t i).le) (hp t)
  · obtain ⟨i, hi⟩ : ∃ i, p s i ≠ 0 := by
      by_contra h
      push Not at h
      exact hps (funext h)
    have hpi : 0 < p s i := lt_of_le_of_ne (hp s i) (Ne.symm hi)
    have : 0 < p s ⬝ᵥ (netOutput y' s - netOutput y s) := by
      refine Finset.sum_pos' (fun j _ => mul_nonneg (hp s j) (sub_nonneg.2 (hlt s j).le))
        ⟨i, Finset.mem_univ _, mul_pos hpi (sub_pos.2 (hlt s i))⟩
    rw [dotProduct_sub] at this
    linarith

/-- A path is **bounded** (Exercise 20.C.4, MWG, p. 783): `|y_{t}| ≤ α` coordinatewise. -/
def BoundedPath (y : ℕ → ProdPlan ι) : Prop :=
  ∃ α : ℝ, ∀ t i, |(y t).1 i| ≤ α ∧ |(y t).2 i| ≤ α

/-- **Exercise 20.C.4** (MWG, p. 783): `y` is overall profit maximizing for `p` if its profit
series converges and no path with a convergent profit series has a larger total profit. -/
def OverallProfitMax (Y : Set (ProdPlan ι)) (p : ℕ → ι → ℝ) (y : ℕ → ProdPlan ι) : Prop :=
  IsProdPath Y y ∧ Summable (periodProfit p y) ∧
    ∀ y', IsProdPath Y y' → Summable (periodProfit p y') →
      ∑' t, periodProfit p y' t ≤ ∑' t, periodProfit p y t

/-- Summable nonnegative prices tend to zero against a bounded path. -/
theorem tendsto_value_of_bounded {p : ℕ → ι → ℝ} (hp0 : ∀ t, 0 ≤ p t)
    (hps : Summable fun t => ∑ i, p t i) {v : ℕ → ι → ℝ} {α : ℝ} (hv : ∀ t i, |v t i| ≤ α) :
    Tendsto (fun t => p t ⬝ᵥ v t) atTop (𝓝 0) := by
  have hlim := (hps.tendsto_atTop_zero).mul_const α
  rw [zero_mul] at hlim
  refine squeeze_zero_norm (fun t => ?_) hlim
  rw [Real.norm_eq_abs]
  calc |p t ⬝ᵥ v t| ≤ ∑ i, |p t i * v t i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, p t i * α := Finset.sum_le_sum fun i _ => by
        rw [abs_mul, abs_of_nonneg (hp0 t i)]
        exact mul_le_mul_of_nonneg_left (hv t i) (hp0 t i)
    _ = (∑ i, p t i) * α := by rw [Finset.sum_mul]

/-- The path that follows `y'` before `T`, the truncation `((y'_T)_b, 0)` at `T`, and `y` after
`T` (used in Exercise 20.C.4(a)). -/
def splicePath (y y' : ℕ → ProdPlan ι) (T : ℕ) : ℕ → ProdPlan ι :=
  fun t => if t < T then y' t else if t = T then ((y' T).1, 0) else y t

omit [Fintype ι] in
theorem splicePath_lt {y y' : ℕ → ProdPlan ι} {T t : ℕ} (h : t < T) :
    splicePath y y' T t = y' t := by
  simp [splicePath, h]

omit [Fintype ι] in
theorem splicePath_self {y y' : ℕ → ProdPlan ι} {T : ℕ} :
    splicePath y y' T T = ((y' T).1, 0) := by
  simp [splicePath]

omit [Fintype ι] in
theorem splicePath_gt {y y' : ℕ → ProdPlan ι} {T t : ℕ} (h : T < t) :
    splicePath y y' T t = y t := by
  simp [splicePath, show ¬ t < T by omega, show t ≠ T by omega]

/-- **Exercise 20.C.4(a)** (MWG, p. 783): a bounded path that is overall profit maximizing for
`p ≫ 0` with `∑_t p_t < ∞` is efficient (truncation, assumption (iv), is used). -/
theorem exercise_20_C_4a {Y : Set (ProdPlan ι)} {p : ℕ → ι → ℝ} {y : ℕ → ProdPlan ι}
    (htr : ∀ z ∈ Y, (z.1, 0) ∈ Y) (hp : ∀ t, StrictPos (p t))
    (hps : Summable fun t => ∑ i, p t i) (hb : BoundedPath y) (hy : OverallProfitMax Y p y) :
    ProdEfficient Y y := by
  obtain ⟨α, hα⟩ := hb
  refine ⟨hy.1, fun ⟨y', hy', hle, hne⟩ => ?_⟩
  obtain ⟨s, hs⟩ : ∃ s, netOutput y' s ≠ netOutput y s := by
    by_contra h
    push Not at h
    exact hne (funext h)
  have hp0 : ∀ t, 0 ≤ p t := fun t i => (hp t i).le
  set ε := p s ⬝ᵥ netOutput y' s - p s ⬝ᵥ netOutput y s with hε
  have hεpos : 0 < ε := by
    have := dotProduct_pos_of_strictPos (hp s) (sub_nonneg.2 (hle s)) (sub_ne_zero.2 hs)
    rw [dotProduct_sub] at this
    rw [hε]; linarith
  -- the spliced path: `y'` before `T`, the truncation of `y'_T` at `T`, `y` afterwards
  have hgap : ∀ T, s ≤ T → ε ≤ p (T + 1) ⬝ᵥ (y T).2 := by
    intro T hT
    set z := splicePath y y' T with hz
    have hzpath : IsProdPath Y z := by
      intro t
      rcases lt_trichotomy t T with h | rfl | h
      · rw [hz, splicePath_lt h]; exact hy' t
      · rw [hz, splicePath_self]; exact htr _ (hy' t)
      · rw [hz, splicePath_gt h]; exact hy.1 t
    have htail : ∀ t, periodProfit p z (t + (T + 1)) = periodProfit p y (t + (T + 1)) := by
      intro t
      simp only [periodProfit]
      rw [hz, splicePath_gt (by omega)]
    have hzs : Summable (periodProfit p z) := by
      refine (summable_nat_add_iff (T + 1)).1 ?_
      exact ((summable_nat_add_iff (T + 1)).2 hy.2.1).congr fun t => (htail t).symm
    have hle' := hy.2.2 z hzpath hzs
    have htail' : ∑' t, periodProfit p z (t + (T + 1)) = ∑' t, periodProfit p y (t + (T + 1)) :=
      tsum_congr htail
    rw [← hzs.sum_add_tsum_nat_add (T + 1), ← hy.2.1.sum_add_tsum_nat_add (T + 1),
      htail', add_le_add_iff_right] at hle'
    have hzsum : ∑ t ∈ Finset.range (T + 1), periodProfit p z t
        = ∑ t ∈ Finset.range (T + 1), p t ⬝ᵥ netOutput y' t := by
      rw [sum_value_netOutput' p y', Finset.sum_range_succ]
      congr 1
      · refine Finset.sum_congr rfl fun t ht => ?_
        simp only [periodProfit]
        rw [hz, splicePath_lt (Finset.mem_range.1 ht)]
      · simp only [periodProfit, planValue]
        rw [hz, splicePath_self, dotProduct_zero, add_zero]
    rw [hzsum] at hle'
    have hsum : ∑ t ∈ Finset.range (T + 1), p t ⬝ᵥ netOutput y t + ε
        ≤ ∑ t ∈ Finset.range (T + 1), p t ⬝ᵥ netOutput y' t := by
      have hmem : s ∈ Finset.range (T + 1) := Finset.mem_range.2 (Nat.lt_succ_of_le hT)
      rw [← sub_nonneg, ← sub_sub, ← Finset.sum_sub_distrib]
      have := Finset.single_le_sum (f := fun t => p t ⬝ᵥ netOutput y' t - p t ⬝ᵥ netOutput y t)
        (fun t _ => sub_nonneg.2 (dotProduct_le_dotProduct_of_nonneg_left (hle t) (hp0 t))) hmem
      linarith
    rw [sum_value_netOutput p y] at hsum
    linarith
  have hps1 : Summable fun t => ∑ i, p (t + 1) i :=
    (summable_nat_add_iff 1).2 hps
  have htc : Tendsto (fun t => p (t + 1) ⬝ᵥ (y t).2) atTop (𝓝 0) :=
    tendsto_value_of_bounded (p := fun t => p (t + 1)) (v := fun t => (y t).2)
      (fun t => hp0 (t + 1)) hps1 (fun t i => (hα t i).2)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (htc.eventually (gt_mem_nhds hεpos))
  have h1 := hN (max N s) (le_max_left _ _)
  have h2 := hgap (max N s) (le_max_right _ _)
  linarith

/-- **Exercise 20.C.4(b)** (MWG, p. 783): a bounded path that is myopically profit maximizing for
`p ≫ 0` with `∑_t p_t < ∞` is overall profit maximizing. -/
theorem exercise_20_C_4b {Y : Set (ProdPlan ι)} {p : ℕ → ι → ℝ} {y : ℕ → ProdPlan ι}
    (hp : ∀ t, StrictPos (p t)) (hps : Summable fun t => ∑ i, p t i) (hb : BoundedPath y)
    (hy : MyopicProfitMax Y p y) : OverallProfitMax Y p y := by
  obtain ⟨α, hα⟩ := hb
  have hp0 : ∀ t i, 0 ≤ p t i := fun t i => (hp t i).le
  have hsum : Summable (periodProfit p y) := by
    have hps1 : Summable fun t => ∑ i, p (t + 1) i := (summable_nat_add_iff 1).2 hps
    refine Summable.of_norm_bounded ((hps.add hps1).mul_right α) fun t => ?_
    rw [Real.norm_eq_abs]
    have hdot : ∀ (q v : ι → ℝ), 0 ≤ q → (∀ i, |v i| ≤ α) → |q ⬝ᵥ v| ≤ (∑ i, q i) * α := by
      intro q v hq hv
      calc |q ⬝ᵥ v| ≤ ∑ i, |q i * v i| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i, q i * α := Finset.sum_le_sum fun i _ => by
            rw [abs_mul, abs_of_nonneg (hq i)]
            exact mul_le_mul_of_nonneg_left (hv i) (hq i)
        _ = (∑ i, q i) * α := by rw [Finset.sum_mul]
    simp only [periodProfit, planValue]
    calc |p t ⬝ᵥ (y t).1 + p (t + 1) ⬝ᵥ (y t).2|
        ≤ |p t ⬝ᵥ (y t).1| + |p (t + 1) ⬝ᵥ (y t).2| := abs_add_le _ _
      _ ≤ (∑ i, p t i) * α + (∑ i, p (t + 1) i) * α :=
          add_le_add (hdot _ _ (hp0 t) fun i => (hα t i).1)
            (hdot _ _ (hp0 (t + 1)) fun i => (hα t i).2)
      _ = ((∑ i, p t i) + ∑ i, p (t + 1) i) * α := by ring
  exact ⟨hy.1, hsum, fun y' hy' hs' =>
    Summable.tsum_le_tsum (fun t => hy.2 t _ (hy' t)) hs' hsum⟩

/-- **Exercise 20.C.5** (MWG, p. 783): a path is `T`-efficient if no dominating path differs
from it at no more than `T` dates. -/
def TEfficient (Y : Set (ProdPlan ι)) (y : ℕ → ProdPlan ι) (T : ℕ) : Prop :=
  IsProdPath Y y ∧ ¬ ∃ y', IsProdPath Y y' ∧ (∀ t, netOutput y t ≤ netOutput y' t) ∧
    netOutput y' ≠ netOutput y ∧ {t | y' t ≠ y t}.Finite ∧ {t | y' t ≠ y t}.ncard ≤ T

/-- Myopic profit maximization for `p ≫ 0` rules out every dominating path that differs from
`y` at only finitely many dates (no transversality condition is needed). -/
theorem not_finite_change_of_myopic {Y : Set (ProdPlan ι)} {p : ℕ → ι → ℝ}
    {y y' : ℕ → ProdPlan ι} (hp : ∀ t, StrictPos (p t)) (hy : MyopicProfitMax Y p y)
    (hy' : IsProdPath Y y') (hle : ∀ t, netOutput y t ≤ netOutput y' t)
    (hne : netOutput y' ≠ netOutput y) : ¬ {t | y' t ≠ y t}.Finite := by
  intro hfin
  obtain ⟨M, hM⟩ : ∃ M, ∀ t, M ≤ t → y' t = y t := by
    obtain ⟨M, hM⟩ := hfin.bddAbove
    refine ⟨M + 1, fun t ht => ?_⟩
    by_contra h
    have := hM h
    omega
  have hlate : ∀ t, M < t → netOutput y' t = netOutput y t := by
    intro t ht
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    simp only [netOutput, hM s (by omega), hM (s + 1) (by omega)]
  obtain ⟨s, hs⟩ : ∃ s, netOutput y' s ≠ netOutput y s := by
    by_contra h
    push Not at h
    exact hne (funext h)
  have hsM : s ≤ M := by
    by_contra h
    exact hs (hlate s (by omega))
  have hsum : ∑ t ∈ Finset.range (M + 1), p t ⬝ᵥ netOutput y' t
      ≤ ∑ t ∈ Finset.range (M + 1), p t ⬝ᵥ netOutput y t := by
    rw [sum_value_netOutput' p y', sum_value_netOutput' p y, hM M le_rfl]
    have := Finset.sum_le_sum fun t (_ : t ∈ Finset.range M) => hy.2 t _ (hy' t)
    simp only [periodProfit] at this ⊢
    linarith
  have hpos : 0 < ∑ t ∈ Finset.range (M + 1), (p t ⬝ᵥ netOutput y' t - p t ⬝ᵥ netOutput y t) := by
    refine Finset.sum_pos' (fun t _ => ?_) ⟨s, Finset.mem_range.2 (by omega), ?_⟩
    · exact sub_nonneg.2 (dotProduct_le_dotProduct_of_nonneg_left (hle t)
        (fun i => (hp t i).le))
    · have := dotProduct_pos_of_strictPos (hp s) (sub_nonneg.2 (hle s)) (sub_ne_zero.2 hs)
      rwa [dotProduct_sub] at this
  rw [Finset.sum_sub_distrib] at hpos
  linarith

/-- **Exercise 20.C.5(a)** (MWG, p. 783): a path that is myopically profit maximizing for some
`p ≫ 0` is `T`-efficient for every `T < ∞`. -/
theorem exercise_20_C_5a {Y : Set (ProdPlan ι)} {p : ℕ → ι → ℝ} {y : ℕ → ProdPlan ι}
    (hp : ∀ t, StrictPos (p t)) (hy : MyopicProfitMax Y p y) (T : ℕ) : TEfficient Y y T :=
  ⟨hy.1, fun ⟨_, hy', hle, hne, hfin, _⟩ => not_finite_change_of_myopic hp hy hy' hle hne hfin⟩

end MWG.EquilibriumTime

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Chains of intermediate goods (MWG Exercise 20.C.5(c), p. 783)

MWG, Chapter 20, Exercise 20.C.5(c): for a general linear activity technology the conclusion of
Exercise 20.C.5(b) (2-efficiency implies `T`-efficiency for all `T`) fails.

The example (following the hint, a chain of intermediate goods): three goods, a final good `0`
and intermediate goods `1`, `2`, and the cone `chainSet` generated by four activities,
* storage: one unit of good `0` today gives one unit of good `0` tomorrow;
* `0 → 1` and `1 → 2`: one unit of the input today gives one unit of the output tomorrow;
* `2 → 0`: one unit of good `2` today gives two units of good `0` tomorrow.

The path that stores one unit of good `0` for ever (`chainStoragePath`) is 2-efficient: any
dominating path using the productive activity `2 → 0` must run the whole chain, which changes
the plan at three consecutive dates; without that activity every plan has zero value at the
prices `(1, 1, 1)`, and the finite-change argument of Exercise 20.C.5(a) applies
(`exercise_20_C_5c_twoEfficient`). Running the chain once at dates `0, 1, 2` instead of storing
gives one extra unit of good `0` at date `3`, so the path is not 3-efficient
(`exercise_20_C_5c_not_threeEfficient`).
-/

namespace MWG.EquilibriumTime

/-- The plan obtained by running the four activities of the chain technology at levels
`a 0` (storage), `a 1` (`0 → 1`), `a 2` (`1 → 2`), `a 3` (`2 → 0`, doubling). -/
def chainPlan (a : Fin 4 → ℝ) : ProdPlan (Fin 3) :=
  (![-(a 0) - a 1, -(a 2), -(a 3)], ![a 0 + 2 * a 3, a 1, a 2])

/-- **Exercise 20.C.5(c)** (MWG, p. 783): the linear activity technology of the example, the
cone generated by the four activities. -/
def chainSet : Set (ProdPlan (Fin 3)) := {z | ∃ a : Fin 4 → ℝ, 0 ≤ a ∧ z = chainPlan a}

/-- The subcone without the productive activity `2 → 0`. -/
def chainSetNoReturn : Set (ProdPlan (Fin 3)) :=
  {z | ∃ a : Fin 4 → ℝ, 0 ≤ a ∧ a 3 = 0 ∧ z = chainPlan a}

/-- The path that stores one unit of good `0` in every period. -/
def chainStoragePath : ℕ → ProdPlan (Fin 3) := fun _ => chainPlan ![1, 0, 0, 0]

/-- Every plan of the subcone without `2 → 0` has value zero at the prices `(1, 1, 1)`. -/
theorem chain_value_zero {a : Fin 4 → ℝ} (h3 : a 3 = 0) :
    planValue (fun _ => (1 : ℝ)) (fun _ => 1) (chainPlan a) = 0 := by
  simp [planValue, chainPlan, dotProduct, Fin.sum_univ_three, h3]
  ring

/-- The storage path is myopically profit maximizing at the constant prices `(1, 1, 1)` for
the technology without the productive activity `2 → 0`. -/
theorem chain_storage_myopic :
    MyopicProfitMax chainSetNoReturn (fun _ _ => (1 : ℝ)) chainStoragePath := by
  refine ⟨fun t => ⟨![1, 0, 0, 0], fun i => ?_, rfl, rfl⟩, fun t z ⟨a, _, h3, hz⟩ => ?_⟩
  · fin_cases i <;> simp
  · rw [hz, chain_value_zero h3]
    simp only [periodProfit, chainStoragePath]
    rw [chain_value_zero (by simp)]

/-- **Exercise 20.C.5(c)**, first half (MWG, p. 783): the storage path is 2-efficient for the
chain technology. -/
theorem exercise_20_C_5c_twoEfficient : TEfficient chainSet chainStoragePath 2 := by
  refine ⟨fun t => ⟨![1, 0, 0, 0], fun i => ?_, rfl⟩, ?_⟩
  · fin_cases i <;> simp
  rintro ⟨y', hy', hle, hne, hfin, hcard⟩
  choose a ha hya using hy'
  -- the dominance inequalities for the intermediate goods
  have g2zero : 0 ≤ -(a 0 3) := by
    have := hle 0 2
    simpa [netOutput, chainStoragePath, chainPlan, hya] using this
  have g2succ : ∀ s, a (s + 1) 3 ≤ a s 2 := fun s => by
    have := hle (s + 1) 2
    simp [netOutput, chainStoragePath, chainPlan, hya] at this
    linarith
  have g1zero : 0 ≤ -(a 0 2) := by
    have := hle 0 1
    simpa [netOutput, chainStoragePath, chainPlan, hya] using this
  have g1succ : ∀ s, a (s + 1) 2 ≤ a s 1 := fun s => by
    have := hle (s + 1) 1
    simp [netOutput, chainStoragePath, chainPlan, hya] at this
    linarith
  -- a date at which an intermediate activity runs is a date of change
  have hchg1 : ∀ s, 0 < a s 1 → y' s ≠ chainStoragePath s := fun s hs h => by
    have := congrArg (fun z : ProdPlan (Fin 3) => z.2 1) h
    simp [chainStoragePath, chainPlan, hya] at this
    linarith
  have hchg2 : ∀ s, 0 < a s 2 → y' s ≠ chainStoragePath s := fun s hs h => by
    have := congrArg (fun z : ProdPlan (Fin 3) => z.2 2) h
    simp [chainStoragePath, chainPlan, hya] at this
    linarith
  have hchg3 : ∀ s, 0 < a s 3 → y' s ≠ chainStoragePath s := fun s hs h => by
    have := congrArg (fun z : ProdPlan (Fin 3) => z.1 2) h
    simp [chainStoragePath, chainPlan, hya] at this
    linarith
  -- the activity `2 → 0` is never used
  have h3 : ∀ t, a t 3 = 0 := by
    intro t
    refine le_antisymm (not_lt.1 fun hpos => ?_) (ha t 3)
    rcases t with _ | s
    · linarith
    have h2 : 0 < a s 2 := lt_of_lt_of_le hpos (g2succ s)
    rcases s with _ | r
    · linarith
    have h1 : 0 < a r 1 := lt_of_lt_of_le h2 (g1succ r)
    have hsub : ({r, r + 1, r + 1 + 1} : Set ℕ) ⊆ {t | y' t ≠ chainStoragePath t} := by
      intro t ht
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
      rcases ht with rfl | rfl | rfl
      · exact hchg1 _ h1
      · exact hchg2 _ h2
      · exact hchg3 _ hpos
    have hc3 := Set.ncard_le_ncard hsub hfin
    rw [Set.ncard_insert_of_notMem
      (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; omega),
      Set.ncard_pair (by omega)] at hc3
    omega
  -- without `2 → 0`, the finite-change argument at prices `(1, 1, 1)` applies
  have hpath : IsProdPath chainSetNoReturn y' := fun t => ⟨a t, ha t, h3 t, hya t⟩
  exact not_finite_change_of_myopic (p := fun _ _ => (1 : ℝ)) (fun _ _ => one_pos)
    chain_storage_myopic hpath hle hne hfin

/-- The path that runs the chain once: at dates `0, 1, 2` it moves one unit of good `0` through
goods `1` and `2` and back into two units of good `0`; afterwards it stores. -/
def chainDetourPath : ℕ → ProdPlan (Fin 3)
  | 0 => chainPlan ![0, 1, 0, 0]
  | 1 => chainPlan ![0, 0, 1, 0]
  | 2 => chainPlan ![0, 0, 0, 1]
  | _ => chainPlan ![1, 0, 0, 0]

/-- **Exercise 20.C.5(c)**, second half (MWG, p. 783): the storage path is not 3-efficient: the
detour through the chain dominates it, gives one more unit of good `0` at date `3`, and differs
from it at three dates. Hence 2-efficiency does not imply `T`-efficiency for all `T`. -/
theorem exercise_20_C_5c_not_threeEfficient : ¬ TEfficient chainSet chainStoragePath 3 := by
  rintro ⟨-, hno⟩
  have hdiff : {t | chainDetourPath t ≠ chainStoragePath t} = {0, 1, 2} := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro h
      by_contra h'
      push Not at h'
      obtain ⟨h0, h1, h2⟩ := h'
      apply h
      match t, h0, h1, h2 with
      | n + 3, _, _, _ => rfl
    · rintro (rfl | rfl | rfl) h
      · have := congrArg (fun z : ProdPlan (Fin 3) => z.2 1) h
        simp [chainDetourPath, chainStoragePath, chainPlan] at this
      · have := congrArg (fun z : ProdPlan (Fin 3) => z.2 2) h
        simp [chainDetourPath, chainStoragePath, chainPlan] at this
      · have := congrArg (fun z : ProdPlan (Fin 3) => z.1 2) h
        simp [chainDetourPath, chainStoragePath, chainPlan] at this
  refine hno ⟨chainDetourPath, fun t => ?_, fun t i => ?_, fun h => ?_, ?_, ?_⟩
  · match t with
    | 0 => exact ⟨![0, 1, 0, 0], fun i => by fin_cases i <;> simp, rfl⟩
    | 1 => exact ⟨![0, 0, 1, 0], fun i => by fin_cases i <;> simp, rfl⟩
    | 2 => exact ⟨![0, 0, 0, 1], fun i => by fin_cases i <;> simp, rfl⟩
    | n + 3 => exact ⟨![1, 0, 0, 0], fun i => by fin_cases i <;> simp, rfl⟩
  · match t with
    | 0 => fin_cases i <;> simp [netOutput, chainDetourPath, chainStoragePath, chainPlan]
    | 1 => fin_cases i <;> simp [netOutput, chainDetourPath, chainStoragePath, chainPlan]
    | 2 => fin_cases i <;> simp [netOutput, chainDetourPath, chainStoragePath, chainPlan]
    | 3 => fin_cases i <;> norm_num [netOutput, chainDetourPath, chainStoragePath, chainPlan]
    | n + 4 => fin_cases i <;> simp [netOutput, chainDetourPath, chainStoragePath, chainPlan]
  · have := congrFun (congrFun h 3) 0
    norm_num [netOutput, chainDetourPath, chainStoragePath, chainPlan] at this
  · rw [hdiff]; exact Set.toFinite _
  · rw [hdiff, Set.ncard_insert_of_notMem (by simp), Set.ncard_pair (by omega)]

end MWG.EquilibriumTime

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Malinvaud prices in the smooth case (MWG Section 20.C, small type; Exercise 20.C.5(b))

MWG, Chapter 20, the small-type discussion at the end of Section 20.C, pp. 742-743, and
Exercise 20.C.5(b), p. 783.

A technology is smooth at `y ∈ Y` with normal `q` (`SmoothAt`) if `q` supports `Y` at `y` and every
supporting vector is a positive multiple of `q` (the marginal rates of transformation at `y` are
uniquely defined).

* The inductive construction of Malinvaud prices from normals satisfying
  `q_{a,t-1} = β_t q_{b,t}` (`malinvaud_of_proportional_normals`).
* MWG's claim that (short-run) efficiency forces `q_{a,t} ∝ q_{b,t+1}`, proved from
  `2`-efficiency (changes at two consecutive dates only) by the second fundamental theorem of
  Chapter 5 (`MWG.Production.proposition_5_F_2`) applied to the stacked two-date technology
  (`proportional_normals_of_twoEfficient`).
* **Exercise 20.C.5(b)**: with a smooth convex technology and strictly positive normals,
  `2`-efficiency implies `T`-efficiency for every `T` (`exercise_20_C_5b`), and in fact yields
  strictly positive Malinvaud prices (`malinvaud_of_twoEfficient`).
-/

open Filter Topology

namespace MWG.EquilibriumTime

variable {ι : Type*} [Fintype ι]

/-- `q ≠ 0` **supports** `Y` at `y`: `y` maximizes `q_b · z_b + q_a · z_a` over `Y`. -/
def SupportsAt (Y : Set (ProdPlan ι)) (y q : ProdPlan ι) : Prop :=
  q ≠ 0 ∧ ∀ z ∈ Y, planValue q.1 q.2 z ≤ planValue q.1 q.2 y

/-- **Smoothness** (MWG, p. 742): `Y` has a single outward normal `q` at `y`, up to positive
scaling. -/
def SmoothAt (Y : Set (ProdPlan ι)) (y q : ProdPlan ι) : Prop :=
  SupportsAt Y y q ∧ ∀ q', SupportsAt Y y q' → ∃ c : ℝ, 0 < c ∧ q' = c • q

theorem planValue_smul (c : ℝ) (a b : ι → ℝ) (z : ProdPlan ι) :
    planValue (c • a) (c • b) z = c * planValue a b z := by
  simp only [planValue, smul_dotProduct, smul_eq_mul]
  ring

/-- The cumulative scale factors `c_t = β_0 ⋯ β_{t-1}` of the construction (MWG, p. 743). -/
noncomputable def normalScale (β : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | t + 1 => normalScale β t * β t

theorem normalScale_pos {β : ℕ → ℝ} (hβ : ∀ t, 0 < β t) (t : ℕ) : 0 < normalScale β t := by
  induction t with
  | zero => exact one_pos
  | succ t ih => exact mul_pos ih (hβ t)

/-- The prices built from the normals: `p_t = c_t q_{b,t}` (MWG, p. 743, `p_0 = q_{b0}`). -/
noncomputable def normalPrices (β : ℕ → ℝ) (q : ℕ → ProdPlan ι) (t : ℕ) : ι → ℝ :=
  normalScale β t • (q t).1

/-- **The construction of Malinvaud prices** in the smooth case (MWG, pp. 742-743): if `q_t`
supports `Y` at `y_t` and `q_{a,t} = β_t q_{b,t+1}` with `β_t > 0`, then `p_t = c_t q_{b,t}` makes
the path myopically profit maximizing, because `(p_t, p_{t+1}) = c_t q_t`. -/
theorem malinvaud_of_proportional_normals {Y : Set (ProdPlan ι)} {y : ℕ → ProdPlan ι}
    (hpath : IsProdPath Y y) {q : ℕ → ProdPlan ι} (hq : ∀ t, SupportsAt Y (y t) (q t))
    {β : ℕ → ℝ} (hβ : ∀ t, 0 < β t) (hprop : ∀ t, (q t).2 = β t • (q (t + 1)).1) :
    MyopicProfitMax Y (normalPrices β q) y := by
  refine ⟨hpath, fun t z hz => ?_⟩
  have hpair : normalPrices β q (t + 1) = normalScale β t • (q t).2 := by
    rw [normalPrices, normalScale, hprop t, smul_smul]
  have h := (hq t).2 z hz
  simp only [periodProfit]
  rw [hpair, normalPrices, planValue_smul, planValue_smul]
  exact mul_le_mul_of_nonneg_left h (normalScale_pos hβ t).le

omit [Fintype ι] in
/-- The constructed prices are strictly positive when the normals' initial parts are. -/
theorem normalPrices_strictPos {β : ℕ → ℝ} (hβ : ∀ t, 0 < β t) {q : ℕ → ProdPlan ι}
    (hq : ∀ t, StrictPos (q t).1) (t : ℕ) : StrictPos (normalPrices β q t) := fun i => by
  simp only [normalPrices, Pi.smul_apply, smul_eq_mul]
  exact mul_pos (normalScale_pos hβ t) (hq t i)

/-! ### The stacked two-date technology -/

variable {L : ℕ}

/-- Stacking three blocks of `ℝ^L` into `ℝ^{3L}`. -/
def tripleVec (a b c : Fin L → ℝ) : Fin (L + L + L) → ℝ := Fin.append (Fin.append a b) c

theorem tripleVec_le_iff (a b c a' b' c' : Fin L → ℝ) :
    tripleVec a b c ≤ tripleVec a' b' c' ↔ a ≤ a' ∧ b ≤ b' ∧ c ≤ c' := by
  constructor
  · intro h
    refine ⟨fun i => ?_, fun i => ?_, fun i => ?_⟩
    · have := h (Fin.castAdd L (Fin.castAdd L i))
      simp only [tripleVec, Fin.append_left] at this
      exact this
    · have := h (Fin.castAdd L (Fin.natAdd L i))
      simp only [tripleVec, Fin.append_left, Fin.append_right] at this
      exact this
    · have := h (Fin.natAdd (L + L) i)
      simp only [tripleVec, Fin.append_right] at this
      exact this
  · rintro ⟨ha, hb, hc⟩ k
    refine Fin.addCases (fun j => ?_) (fun j => ?_) k
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simp only [tripleVec, Fin.append_left]; exact ha i
      · simp only [tripleVec, Fin.append_left, Fin.append_right]; exact hb i
    · simp only [tripleVec, Fin.append_right]; exact hc j

theorem tripleVec_injective {a b c a' b' c' : Fin L → ℝ}
    (h : tripleVec a b c = tripleVec a' b' c') : a = a' ∧ b = b' ∧ c = c' := by
  have h1 := (tripleVec_le_iff a b c a' b' c').1 h.le
  have h2 := (tripleVec_le_iff a' b' c' a b c).1 h.ge
  exact ⟨le_antisymm h1.1 h2.1, le_antisymm h1.2.1 h2.2.1, le_antisymm h1.2.2 h2.2.2⟩

theorem dotProduct_tripleVec (p : Fin (L + L + L) → ℝ) (a b c : Fin L → ℝ) :
    p ⬝ᵥ tripleVec a b c = (fun i => p (Fin.castAdd L (Fin.castAdd L i))) ⬝ᵥ a
      + (fun i => p (Fin.castAdd L (Fin.natAdd L i))) ⬝ᵥ b
      + (fun i => p (Fin.natAdd (L + L) i)) ⬝ᵥ c := by
  simp only [dotProduct, tripleVec]
  rw [Fin.sum_univ_add, Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]

/-- The two-date technology of dates `t, t+1`: the net vectors
`(z_b, z_a + z'_b, z'_a)` for `z, z' ∈ Y`, stacked in `ℝ^{3L}`. -/
def twoDateSet (Y : Set (ProdPlan (Fin L))) : Set (Fin (L + L + L) → ℝ) :=
  {v | ∃ z ∈ Y, ∃ z' ∈ Y, v = tripleVec z.1 (z.2 + z'.1) z'.2}

theorem convex_twoDateSet {Y : Set (ProdPlan (Fin L))} (hY : Convex ℝ Y) :
    Convex ℝ (twoDateSet Y) := by
  have hlin : IsLinearMap ℝ (fun w : ProdPlan (Fin L) × ProdPlan (Fin L) =>
      tripleVec w.1.1 (w.1.2 + w.2.1) w.2.2) := by
    constructor
    · intro w w'
      funext k
      refine Fin.addCases (fun j => ?_) (fun j => ?_) k
      · refine Fin.addCases (fun i => ?_) (fun i => ?_) j
        · simp only [tripleVec, Fin.append_left, Pi.add_apply, Prod.fst_add, Prod.snd_add]
        · simp only [tripleVec, Fin.append_left, Fin.append_right, Pi.add_apply, Prod.fst_add,
            Prod.snd_add]
          ring
      · simp only [tripleVec, Fin.append_right, Pi.add_apply, Prod.snd_add]
    · intro c w
      funext k
      refine Fin.addCases (fun j => ?_) (fun j => ?_) k
      · refine Fin.addCases (fun i => ?_) (fun i => ?_) j
        · simp only [tripleVec, Fin.append_left, Pi.smul_apply, Prod.smul_fst]
        · simp only [tripleVec, Fin.append_left, Fin.append_right, Pi.add_apply,
            Pi.smul_apply, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
          ring
      · simp only [tripleVec, Fin.append_right, Pi.smul_apply, Prod.smul_snd]
  have h := (hY.prod hY).is_linear_image hlin
  convert h using 1
  ext v
  constructor
  · rintro ⟨z, hz, z', hz', rfl⟩
    exact ⟨(z, z'), ⟨hz, hz'⟩, rfl⟩
  · rintro ⟨⟨z, z'⟩, ⟨hz, hz'⟩, rfl⟩
    exact ⟨z, hz, z', hz', rfl⟩

/-- Changing the plans of a path at the dates `t` and `t + 1`. -/
def updateTwo (y : ℕ → ProdPlan ι) (t : ℕ) (z z' : ProdPlan ι) : ℕ → ProdPlan ι :=
  fun s => if s = t then z else if s = t + 1 then z' else y s

omit [Fintype ι] in
theorem updateTwo_changes (y : ℕ → ProdPlan ι) (t : ℕ) (z z' : ProdPlan ι) :
    {s | updateTwo y t z z' s ≠ y s} ⊆ {t, t + 1} := by
  intro s hs
  by_contra h
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at h
  exact hs (by simp [updateTwo, h.1, h.2])

/-- Two-efficiency at the consecutive dates `t, t+1` makes the stacked point efficient in the
two-date technology. -/
theorem efficient_twoDateSet {Y : Set (ProdPlan (Fin L))} {y : ℕ → ProdPlan (Fin L)}
    (hy : TEfficient Y y 2) (t : ℕ) :
    MWG.Production.Efficient (twoDateSet Y)
      (tripleVec (y t).1 ((y t).2 + (y (t + 1)).1) (y (t + 1)).2) := by
  refine ⟨⟨y t, hy.1 t, y (t + 1), hy.1 (t + 1), rfl⟩, ?_⟩
  rintro ⟨v, ⟨z, hz, z', hz', rfl⟩, hle, hne⟩
  obtain ⟨h1, h2, h3⟩ := (tripleVec_le_iff _ _ _ _ _ _).1 hle
  set y' := updateTwo y t z z' with hy'
  have hpath : IsProdPath Y y' := by
    intro s
    simp only [hy', updateTwo]
    split_ifs
    · exact hz
    · exact hz'
    · exact hy.1 s
  have hfin : {s | y' s ≠ y s}.Finite :=
    (Set.toFinite {t, t + 1}).subset (updateTwo_changes _ _ _ _)
  have hcard : {s | y' s ≠ y s}.ncard ≤ 2 := by
    calc {s | y' s ≠ y s}.ncard ≤ ({t, t + 1} : Set ℕ).ncard :=
          Set.ncard_le_ncard (updateTwo_changes _ _ _ _) (Set.toFinite _)
      _ = 2 := Set.ncard_pair (by omega)
  have hnet : ∀ s, netOutput y s ≤ netOutput y' s := by
    intro s
    rcases s with _ | s
    · by_cases h0 : t = 0
      · subst h0; simpa [netOutput, hy', updateTwo] using h1
      · simp [netOutput, hy', updateTwo, Ne.symm h0]
    · simp only [netOutput, hy', updateTwo]
      by_cases ha : s = t
      · subst ha
        simp only [ite_true, show s + 1 ≠ s by omega]
        simpa using h2
      · by_cases hb : s = t + 1
        · subst hb
          simp only [show t + 1 ≠ t by omega, show t + 1 + 1 ≠ t by omega,
            show t + 1 + 1 ≠ t + 1 by omega]
          simp only [↓reduceIte]
          exact add_le_add h3 le_rfl
        · by_cases hc : s + 1 = t
          · subst hc
            simp only [ha, hb]
            simp only [↓reduceIte]
            exact add_le_add le_rfl h1
          · simp [ha, hb, hc]
  refine hy.2 ⟨y', hpath, hnet, fun heq => hne ?_, hfin, hcard⟩
  -- equal net outputs force equal stacked vectors
  have e1 := congrFun heq t
  have e2 := congrFun heq (t + 1)
  have e3 := congrFun heq (t + 2)
  have ht1 : t + 1 ≠ t := by omega
  have ht2 : t + 2 ≠ t := by omega
  have ht3 : t + 2 ≠ t + 1 := by omega
  have hb : z.1 = (y t).1 := by
    rcases t with _ | t
    · simpa [netOutput, hy', updateTwo] using e1
    · simp only [netOutput, hy', updateTwo, show t ≠ t + 1 by omega, ite_true,
        show t ≠ t + 1 + 1 by omega] at e1
      simpa using e1
  have hm : z.2 + z'.1 = (y t).2 + (y (t + 1)).1 := by
    simpa [netOutput, hy', updateTwo, ht1] using e2
  have ha : z'.2 = (y (t + 1)).2 := by
    have : z'.2 + (y (t + 2)).1 = (y (t + 1)).2 + (y (t + 2)).1 := by
      simpa [netOutput, hy', updateTwo, ht2, ht3, show t + 1 + 1 = t + 2 by omega] using e3
    exact add_right_cancel this
  rw [hb, hm, ha]

/-- Splitting a price vector of `ℝ^{3L}` into its three blocks. -/
def block1 (p : Fin (L + L + L) → ℝ) : Fin L → ℝ := fun i => p (Fin.castAdd L (Fin.castAdd L i))
/-- The middle block. -/
def block2 (p : Fin (L + L + L) → ℝ) : Fin L → ℝ := fun i => p (Fin.castAdd L (Fin.natAdd L i))
/-- The last block. -/
def block3 (p : Fin (L + L + L) → ℝ) : Fin L → ℝ := fun i => p (Fin.natAdd (L + L) i)

theorem tripleVec_blocks (p : Fin (L + L + L) → ℝ) :
    tripleVec (block1 p) (block2 p) (block3 p) = p := by
  funext k
  refine Fin.addCases (fun j => ?_) (fun j => ?_) k
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp [tripleVec, block1]
    · simp only [tripleVec, Fin.append_left, Fin.append_right, block2]
  · simp only [tripleVec, Fin.append_right, block3]

/-- **MWG's claim** (p. 742): in the smooth case, short-run efficiency forces the normals at
consecutive dates to be compatible: `q_{a,t} = β q_{b,t+1}` for some `β > 0`. Proved from
`2`-efficiency, convexity, smoothness at `y_t` and `y_{t+1}`, and nonzero `q_{a,t}`,
`q_{b,t+1}`, by the second fundamental theorem of Chapter 5 on the two-date technology. -/
theorem proportional_normals_of_twoEfficient (hL : 0 < L) {Y : Set (ProdPlan (Fin L))}
    (hY : Convex ℝ Y) {y : ℕ → ProdPlan (Fin L)} (hy : TEfficient Y y 2) {q : ℕ → ProdPlan (Fin L)}
    (t : ℕ) (hs0 : SmoothAt Y (y t) (q t)) (hs1 : SmoothAt Y (y (t + 1)) (q (t + 1)))
    (ha0 : (q t).2 ≠ 0) (hb1 : (q (t + 1)).1 ≠ 0) :
    ∃ β : ℝ, 0 < β ∧ (q t).2 = β • (q (t + 1)).1 := by
  obtain ⟨p, -, hp0, -, hmax⟩ := MWG.Production.proposition_5_F_2 (by omega)
    (convex_twoDateSet hY) (efficient_twoDateSet hy t)
  set p1 := block1 p
  set p2 := block2 p
  set p3 := block3 p
  have hval : ∀ a b c : Fin L → ℝ, p ⬝ᵥ tripleVec a b c = p1 ⬝ᵥ a + p2 ⬝ᵥ b + p3 ⬝ᵥ c :=
    fun a b c => dotProduct_tripleVec p a b c
  -- `(p1, p2)` supports `Y` at `y_t`, `(p2, p3)` supports `Y` at `y_{t+1}`
  have hsup0 : ∀ z ∈ Y, planValue p1 p2 z ≤ planValue p1 p2 (y t) := by
    intro z hz
    have := hmax _ ⟨z, hz, y (t + 1), hy.1 (t + 1), rfl⟩
    rw [hval, hval] at this
    simp only [planValue, dotProduct_add] at this ⊢
    linarith
  have hsup1 : ∀ z ∈ Y, planValue p2 p3 z ≤ planValue p2 p3 (y (t + 1)) := by
    intro z hz
    have := hmax _ ⟨y t, hy.1 t, z, hz, rfl⟩
    rw [hval, hval] at this
    simp only [planValue, dotProduct_add] at this ⊢
    linarith
  have hp : p = tripleVec p1 p2 p3 := (tripleVec_blocks p).symm
  have h12 : ((p1, p2) : ProdPlan (Fin L)) ≠ 0 := by
    intro h
    have hp1 : p1 = 0 := congrArg Prod.fst h
    have hp2 : p2 = 0 := congrArg Prod.snd h
    have hp3 : p3 ≠ 0 := by
      intro hp3
      apply hp0
      rw [hp, hp1, hp2, hp3]
      funext k
      refine Fin.addCases (fun j => ?_) (fun j => ?_) k
      · refine Fin.addCases (fun i => ?_) (fun i => ?_) j
        · simp [tripleVec]
        · simp only [tripleVec, Fin.append_left, Fin.append_right, Pi.zero_apply]
      · simp only [tripleVec, Fin.append_right, Pi.zero_apply]
    obtain ⟨c, hc, hceq⟩ := hs1.2 (p2, p3) ⟨by
      intro h0; exact hp3 (congrArg Prod.snd h0), hsup1⟩
    have := congrArg Prod.fst hceq
    simp only [Prod.smul_fst] at this
    rw [hp2] at this
    exact hb1 (smul_eq_zero.1 this.symm |>.resolve_left hc.ne')
  have h23 : ((p2, p3) : ProdPlan (Fin L)) ≠ 0 := by
    intro h
    have hp2 : p2 = 0 := congrArg Prod.fst h
    have hp3 : p3 = 0 := congrArg Prod.snd h
    have hp1 : p1 ≠ 0 := by
      intro hp1
      apply hp0
      rw [hp, hp1, hp2, hp3]
      funext k
      refine Fin.addCases (fun j => ?_) (fun j => ?_) k
      · refine Fin.addCases (fun i => ?_) (fun i => ?_) j
        · simp [tripleVec]
        · simp only [tripleVec, Fin.append_left, Fin.append_right, Pi.zero_apply]
      · simp only [tripleVec, Fin.append_right, Pi.zero_apply]
    obtain ⟨c, hc, hceq⟩ := hs0.2 (p1, p2) ⟨by
      intro h0; exact hp1 (congrArg Prod.fst h0), hsup0⟩
    have := congrArg Prod.snd hceq
    simp only [Prod.smul_snd] at this
    rw [hp2] at this
    exact ha0 (smul_eq_zero.1 this.symm |>.resolve_left hc.ne')
  obtain ⟨c0, hc0, hc0eq⟩ := hs0.2 (p1, p2) ⟨h12, hsup0⟩
  obtain ⟨c1, hc1, hc1eq⟩ := hs1.2 (p2, p3) ⟨h23, hsup1⟩
  have e0 : p2 = c0 • (q t).2 := by
    have := congrArg Prod.snd hc0eq; simpa using this
  have e1 : p2 = c1 • (q (t + 1)).1 := by
    have := congrArg Prod.fst hc1eq; simpa using this
  refine ⟨c1 / c0, div_pos hc1 hc0, ?_⟩
  have : c0 • (q t).2 = c1 • (q (t + 1)).1 := e0.symm.trans e1
  calc (q t).2 = c0⁻¹ • (c0 • (q t).2) := by rw [smul_smul, inv_mul_cancel₀ hc0.ne', one_smul]
    _ = c0⁻¹ • (c1 • (q (t + 1)).1) := by rw [this]
    _ = (c1 / c0) • (q (t + 1)).1 := by rw [smul_smul, div_eq_inv_mul]

/-- **Existence of Malinvaud prices** in the smooth case (MWG, pp. 742-743): a `2`-efficient path
of a convex technology that is smooth along the path with strictly positive normals has a
strictly positive system of Malinvaud prices. -/
theorem malinvaud_of_twoEfficient (hL : 0 < L) {Y : Set (ProdPlan (Fin L))} (hY : Convex ℝ Y)
    {y : ℕ → ProdPlan (Fin L)} (hy : TEfficient Y y 2) {q : ℕ → ProdPlan (Fin L)}
    (hs : ∀ t, SmoothAt Y (y t) (q t)) (hqb : ∀ t, StrictPos (q t).1)
    (hqa : ∀ t, StrictPos (q t).2) :
    ∃ p : ℕ → Fin L → ℝ, (∀ t, StrictPos (p t)) ∧ MyopicProfitMax Y p y := by
  have hne : ∀ v : Fin L → ℝ, StrictPos v → v ≠ 0 := by
    intro v hv h
    have := hv ⟨0, hL⟩
    rw [h] at this
    exact lt_irrefl _ this
  have hβ : ∀ t, ∃ β : ℝ, 0 < β ∧ (q t).2 = β • (q (t + 1)).1 := fun t =>
    proportional_normals_of_twoEfficient hL hY hy t (hs t) (hs (t + 1)) (hne _ (hqa t))
      (hne _ (hqb (t + 1)))
  choose β hβpos hβeq using hβ
  exact ⟨normalPrices β q, normalPrices_strictPos hβpos hqb,
    malinvaud_of_proportional_normals hy.1 (fun t => (hs t).1) hβpos hβeq⟩

/-- **Exercise 20.C.5(b)** (MWG, p. 783): for a convex technology that is smooth along the path
with strictly positive outward normals, `2`-efficiency implies `T`-efficiency for all `T < ∞`. -/
theorem exercise_20_C_5b (hL : 0 < L) {Y : Set (ProdPlan (Fin L))} (hY : Convex ℝ Y)
    {y : ℕ → ProdPlan (Fin L)} (hy : TEfficient Y y 2) {q : ℕ → ProdPlan (Fin L)}
    (hs : ∀ t, SmoothAt Y (y t) (q t)) (hqb : ∀ t, StrictPos (q t).1)
    (hqa : ∀ t, StrictPos (q t).2) (T : ℕ) : TEfficient Y y T := by
  obtain ⟨p, hp, hmyopic⟩ := malinvaud_of_twoEfficient hL hY hy hs hqb hqa
  exact exercise_20_C_5a hp hmyopic T

end MWG.EquilibriumTime

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Supporting prices in the Ramsey-Solow and cost-of-adjustment models (MWG Section 20.C)

MWG, Chapter 20, Examples 20.C.6-20.C.7, pp. 741-742, and Exercise 20.C.6, pp. 783-784.

The Ramsey-Solow production function is `F ![k, l]` on `ℝ²`; its partial derivatives at `x` are
`DF(e_k)` and `DF(e_l)` for the derivative `DF` (`HasFDerivAt F DF x`). Prices at `t` are
`p_t = ![q_t, w_t]` (output, wage). A capital-labor path `(k_t, l_t)` determines the plans
`y_t = (-k_t, -l_t, F(k_t, l_t), 0)` (`rsPlan`).

* **Example 20.C.6**: the first-order conditions `q_t / q_{t+1} = ∇₁F` and `w_t / q_{t+1} = ∇₂F`
  are necessary and sufficient for short-run profit maximization at an interior plan
  (`example_20_C_6`).
* **Exercise 20.C.6**: output prices with `q_t / q_{t+1} = ∇₁F(k_t, l_t)` and the wages
  `w_t = q_{t+1} ∇₂F(k_t, l_t)` support any capital path (`exercise_20_C_6`).
* **(20.C.1)-(20.C.2)**: with bounded production, these prices and `q_t → 0` give efficiency
  (`efficient_of_20_C_1_20_C_2`), by Proposition 20.C.1.
* **Example 20.C.7**: the first-order conditions (i)-(ii) of the cost-of-adjustment model and
  (20.C.3), which reduces to (20.C.1) without adjustment costs (`example_20_C_7`).

The gradient inequality for concave functions is Chapter 15's
`MWG.GeneralEquilibriumExamples.concave_le_fderiv`.
-/

open Filter Topology

namespace MWG.EquilibriumTime

/-- Every vector of `ℝ²` is `v₀ e_k + v₁ e_l`, so a linear functional is determined by the two
partial derivatives. -/
theorem clm_fin2_apply (D : (Fin 2 → ℝ) →L[ℝ] ℝ) (v : Fin 2 → ℝ) :
    D v = v 0 * D (Pi.single 0 1) + v 1 * D (Pi.single 1 1) := by
  have hv : v = v 0 • (Pi.single 0 1 : Fin 2 → ℝ) + v 1 • (Pi.single 1 1 : Fin 2 → ℝ) := by
    funext i; fin_cases i <;> simp
  conv_lhs => rw [hv]
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

/-- The Ramsey-Solow plan `(-k, -l, F(k, l), 0)` of a capital-labor pair. -/
def rsPlan (F : (Fin 2 → ℝ) → ℝ) (k l : ℝ) : ProdPlan (Fin 2) := (![-k, -l], ![F ![k, l], 0])

theorem rsPlan_mem {F : (Fin 2 → ℝ) → ℝ} {k l : ℝ} (hk : 0 ≤ k) (hl : 0 ≤ l) :
    rsPlan F k l ∈ ramseySolowSet F :=
  ⟨k, l, F ![k, l], hk, hl, le_rfl, le_rfl⟩

/-- The profit of the Ramsey-Solow plan at prices `(q, w)` today and `(q', w')` tomorrow:
`q' F(k, l) - q k - w l` (MWG, p. 741). -/
theorem planValue_rsPlan (F : (Fin 2 → ℝ) → ℝ) (k l q w q' w' : ℝ) :
    planValue ![q, w] ![q', w'] (rsPlan F k l) = q' * F ![k, l] - q * k - w * l := by
  simp [planValue, rsPlan, dotProduct, Fin.sum_univ_two]
  ring

/-- A concave function that is nondecreasing on `ℝ²_+` has nonnegative partial derivatives at
every point of `ℝ²_+` where it is differentiable. -/
theorem partial_nonneg_of_concave_mono {F : (Fin 2 → ℝ) → ℝ}
    (hconc : ConcaveOn ℝ (Set.Ici 0) F) (hmono : MonotoneOn F (Set.Ici 0))
    {x : Fin 2 → ℝ} (hx : 0 ≤ x) {DF : (Fin 2 → ℝ) →L[ℝ] ℝ} (hDF : HasFDerivAt F DF x)
    (i : Fin 2) : 0 ≤ DF (Pi.single i 1) := by
  have he : (0 : Fin 2 → ℝ) ≤ Pi.single i 1 := by
    intro j; by_cases h : j = i
    · subst h; simp
    · simp [h]
  have hxe : x ≤ x + Pi.single i 1 := le_add_of_nonneg_right he
  have h1 := MWG.GeneralEquilibriumExamples.concave_le_fderiv hconc (Set.mem_Ici.2 hx)
    (Set.mem_Ici.2 (hx.trans hxe)) hDF
  have h2 := hmono (Set.mem_Ici.2 hx) (Set.mem_Ici.2 (hx.trans hxe)) hxe
  rw [add_sub_cancel_left] at h1
  linarith

/-- The capital-labor path's plans. -/
def rsPath (F : (Fin 2 → ℝ) → ℝ) (k l : ℕ → ℝ) : ℕ → ProdPlan (Fin 2) :=
  fun t => rsPlan F (k t) (l t)

/-- The price sequence `p_t = (q_t, w_t)`. -/
def rsPrices (q w : ℕ → ℝ) : ℕ → Fin 2 → ℝ := fun t => ![q t, w t]

/-- **Example 20.C.6**, sufficiency (MWG, p. 741): if `F` is concave and nondecreasing on `ℝ²_+`,
differentiable at `(k, l) ≥ 0`, `q' > 0`, `w' ≥ 0`, `q = q' ∇₁F(k, l)` and `w = q' ∇₂F(k, l)`,
then the plan `(-k, -l, F(k, l), 0)` maximizes profit on the Ramsey-Solow technology at prices
`(q, w)` and `(q', w')`. -/
theorem rs_profitMax_of_foc {F : (Fin 2 → ℝ) → ℝ} (hconc : ConcaveOn ℝ (Set.Ici 0) F)
    (hmono : MonotoneOn F (Set.Ici 0)) {k l : ℝ} (hk : 0 ≤ k) (hl : 0 ≤ l)
    {DF : (Fin 2 → ℝ) →L[ℝ] ℝ} (hDF : HasFDerivAt F DF ![k, l]) {q w q' w' : ℝ}
    (hq' : 0 < q') (hw' : 0 ≤ w') (hq : q = q' * DF (Pi.single 0 1))
    (hw : w = q' * DF (Pi.single 1 1)) :
    ∀ z ∈ ramseySolowSet F, planValue ![q, w] ![q', w'] z ≤
      planValue ![q, w] ![q', w'] (rsPlan F k l) := by
  rintro z ⟨k', l', x, hk', hl', hx, hb, ha⟩
  have hb0 : z.1 0 ≤ -k' := by simpa using hb 0
  have hb1 : z.1 1 ≤ -l' := by simpa using hb 1
  have ha0 : z.2 0 ≤ x := by simpa using ha 0
  have ha1 : z.2 1 ≤ 0 := by simpa using ha 1
  have hx0 : (0 : Fin 2 → ℝ) ≤ ![k, l] := by intro i; fin_cases i <;> simp [hk, hl]
  have hx1 : (0 : Fin 2 → ℝ) ≤ ![k', l'] := by intro i; fin_cases i <;> simp [hk', hl']
  have hgrad := MWG.GeneralEquilibriumExamples.concave_le_fderiv hconc (Set.mem_Ici.2 hx0)
    (Set.mem_Ici.2 hx1) hDF
  rw [clm_fin2_apply DF] at hgrad
  simp only [Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    at hgrad
  rw [planValue_rsPlan]
  simp only [planValue, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  have hq0 : 0 ≤ q := by
    rw [hq]; exact mul_nonneg hq'.le (partial_nonneg_of_concave_mono hconc hmono hx0 hDF 0)
  have hw0 : 0 ≤ w := by
    rw [hw]; exact mul_nonneg hq'.le (partial_nonneg_of_concave_mono hconc hmono hx0 hDF 1)
  have e1 : q * z.1 0 ≤ q * -k' := mul_le_mul_of_nonneg_left hb0 hq0
  have e2 : w * z.1 1 ≤ w * -l' := mul_le_mul_of_nonneg_left hb1 hw0
  have e3 : q' * z.2 0 ≤ q' * F ![k', l'] := mul_le_mul_of_nonneg_left (ha0.trans hx) hq'.le
  have e4 : w' * z.2 1 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hw' ha1
  have e5 := mul_le_mul_of_nonneg_left hgrad hq'.le
  have e6 : q' * ((k' - k) * DF (Pi.single 0 1) + (l' - l) * DF (Pi.single 1 1))
      = (k' - k) * q + (l' - l) * w := by rw [hq, hw]; ring
  rw [mul_add, e6] at e5
  linarith

/-- **Example 20.C.6**, necessity (MWG, p. 741): at an interior plan (`k, l > 0`) that maximizes
profit on the Ramsey-Solow technology, `q = q' ∇₁F(k, l)` and `w = q' ∇₂F(k, l)`. -/
theorem rs_foc_of_profitMax {F : (Fin 2 → ℝ) → ℝ} {k l : ℝ} (hk : 0 < k) (hl : 0 < l)
    {DF : (Fin 2 → ℝ) →L[ℝ] ℝ} (hDF : HasFDerivAt F DF ![k, l]) {q w q' w' : ℝ}
    (hmax : ∀ z ∈ ramseySolowSet F, planValue ![q, w] ![q', w'] z ≤
      planValue ![q, w] ![q', w'] (rsPlan F k l)) :
    q = q' * DF (Pi.single 0 1) ∧ w = q' * DF (Pi.single 1 1) := by
  -- the profit along each coordinate line is maximized at the interior point
  have hline0 : HasDerivAt (fun s : ℝ => (![s, l] : Fin 2 → ℝ)) (Pi.single 0 1) k := by
    refine hasDerivAt_pi.2 fun i => ?_
    fin_cases i
    · simpa using hasDerivAt_id' k
    · simpa using hasDerivAt_const k l
  have hline1 : HasDerivAt (fun s : ℝ => (![k, s] : Fin 2 → ℝ)) (Pi.single 1 1) l := by
    refine hasDerivAt_pi.2 fun i => ?_
    fin_cases i
    · simpa using hasDerivAt_const l k
    · simpa using hasDerivAt_id' l
  have hd0 : HasDerivAt (fun s => q' * F ![s, l] - q * s - w * l)
      (q' * DF (Pi.single 0 1) - q * 1 - 0) k :=
    (((hDF.comp_hasDerivAt k hline0).const_mul q').sub ((hasDerivAt_id k).const_mul q)).sub
      (hasDerivAt_const k _)
  have hd1 : HasDerivAt (fun s => q' * F ![k, s] - q * k - w * s)
      (q' * DF (Pi.single 1 1) - 0 - w * 1) l :=
    (((hDF.comp_hasDerivAt l hline1).const_mul q').sub (hasDerivAt_const l _)).sub
      ((hasDerivAt_id l).const_mul w)
  have hmax0 : IsLocalMax (fun s => q' * F ![s, l] - q * s - w * l) k := by
    filter_upwards [Ioi_mem_nhds hk] with s hs
    have := hmax _ (rsPlan_mem (le_of_lt hs) hl.le)
    rwa [planValue_rsPlan, planValue_rsPlan] at this
  have hmax1 : IsLocalMax (fun s => q' * F ![k, s] - q * k - w * s) l := by
    filter_upwards [Ioi_mem_nhds hl] with s hs
    have := hmax _ (rsPlan_mem hk.le (le_of_lt hs))
    rwa [planValue_rsPlan, planValue_rsPlan] at this
  have e0 := hmax0.hasDerivAt_eq_zero hd0
  have e1 := hmax1.hasDerivAt_eq_zero hd1
  constructor <;> linarith

/-- **Example 20.C.6** (MWG, p. 741): for `F` concave and nondecreasing on `ℝ²_+`, an interior plan
`(-k, -l, F(k, l), 0)` maximizes short-run profit at `(q, w)`, `(q', w')` (`q' > 0`, `w' ≥ 0`) if
and only if `q / q' = ∇₁F(k, l)` and `w / q' = ∇₂F(k, l)`. -/
theorem example_20_C_6 {F : (Fin 2 → ℝ) → ℝ} (hconc : ConcaveOn ℝ (Set.Ici 0) F)
    (hmono : MonotoneOn F (Set.Ici 0)) {k l : ℝ} (hk : 0 < k) (hl : 0 < l)
    {DF : (Fin 2 → ℝ) →L[ℝ] ℝ} (hDF : HasFDerivAt F DF ![k, l]) {q w q' w' : ℝ}
    (hq' : 0 < q') (hw' : 0 ≤ w') :
    (∀ z ∈ ramseySolowSet F, planValue ![q, w] ![q', w'] z ≤
      planValue ![q, w] ![q', w'] (rsPlan F k l)) ↔
      q / q' = DF (Pi.single 0 1) ∧ w / q' = DF (Pi.single 1 1) := by
  constructor
  · intro h
    obtain ⟨h0, h1⟩ := rs_foc_of_profitMax hk hl hDF h
    refine ⟨?_, ?_⟩
    · rw [h0]; field_simp
    · rw [h1]; field_simp
  · rintro ⟨h0, h1⟩
    refine rs_profitMax_of_foc hconc hmono hk.le hl.le hDF hq' hw' ?_ ?_
    · rw [← h0]; field_simp
    · rw [← h1]; field_simp

/-- **Exercise 20.C.6** (MWG, pp. 783-784): for any capital path with exogenous labor
`(k_t, l_t) ≥ 0`, positive output prices with `q_t / q_{t+1} = ∇₁F(k_t, l_t)` and the wages
`w_t = q_{t+1} ∇₂F(k_t, l_t)` make the path myopically profit maximizing. -/
theorem exercise_20_C_6 {F : (Fin 2 → ℝ) → ℝ} (hconc : ConcaveOn ℝ (Set.Ici 0) F)
    (hmono : MonotoneOn F (Set.Ici 0)) {k l : ℕ → ℝ} (hk : ∀ t, 0 ≤ k t) (hl : ∀ t, 0 ≤ l t)
    {DF : ℕ → (Fin 2 → ℝ) →L[ℝ] ℝ} (hDF : ∀ t, HasFDerivAt F (DF t) ![k t, l t])
    {q : ℕ → ℝ} (hq : ∀ t, 0 < q t) (hfoc : ∀ t, q t / q (t + 1) = DF t (Pi.single 0 1)) :
    MyopicProfitMax (ramseySolowSet F)
      (rsPrices q (fun t => q (t + 1) * DF t (Pi.single 1 1))) (rsPath F k l) := by
  refine ⟨fun t => rsPlan_mem (hk t) (hl t), fun t z hz => ?_⟩
  have hx : ∀ t, (0 : Fin 2 → ℝ) ≤ ![k t, l t] := fun t i => by
    fin_cases i <;> simp [hk t, hl t]
  have hw' : 0 ≤ q (t + 1 + 1) * DF (t + 1) (Pi.single 1 1) :=
    mul_nonneg (hq _).le (partial_nonneg_of_concave_mono hconc hmono (hx (t + 1)) (hDF (t + 1)) 1)
  have := rs_profitMax_of_foc hconc hmono (hk t) (hl t) (hDF t) (hq (t + 1)) hw'
    (q := q t) (w := q (t + 1) * DF t (Pi.single 1 1))
    (by rw [← hfoc t]; field_simp [(hq (t + 1)).ne']) rfl z hz
  simpa [periodProfit, rsPrices, rsPath] using this

/-- **(20.C.1)-(20.C.2)** (MWG, p. 741): a feasible capital path with exogenous labor, bounded
production `F(k_t, l_t)`, output prices `q_t > 0` with `q_t / q_{t+1} = ∇₁F(k_t, l_t)` and
`q_t → 0` is efficient (positive marginal products of labor make the wages strictly positive). -/
theorem efficient_of_20_C_1_20_C_2 {F : (Fin 2 → ℝ) → ℝ} (hconc : ConcaveOn ℝ (Set.Ici 0) F)
    (hmono : MonotoneOn F (Set.Ici 0)) (h00 : F 0 = 0) {k l : ℕ → ℝ} (hk : ∀ t, 0 ≤ k t)
    (hl : ∀ t, 0 ≤ l t) {DF : ℕ → (Fin 2 → ℝ) →L[ℝ] ℝ}
    (hDF : ∀ t, HasFDerivAt F (DF t) ![k t, l t]) (hmpl : ∀ t, 0 < DF t (Pi.single 1 1))
    {B : ℝ} (hbdd : ∀ t, |F ![k t, l t]| ≤ B) {q : ℕ → ℝ} (hq : ∀ t, 0 < q t)
    (h20C1 : ∀ t, q t / q (t + 1) = DF t (Pi.single 0 1))
    (h20C2 : Tendsto q atTop (𝓝 0)) : ProdEfficient (ramseySolowSet F) (rsPath F k l) := by
  have htr : ∀ z ∈ ramseySolowSet F, (z.1, 0) ∈ ramseySolowSet F := by
    rintro z ⟨k', l', x, hk', hl', hx, hb, -⟩
    refine ⟨k', l', 0, hk', hl', ?_, hb, fun i => ?_⟩
    · have h0 : (0 : Fin 2 → ℝ) ≤ ![k', l'] := by intro i; fin_cases i <;> simp [hk', hl']
      rw [← h00]; exact hmono (le_refl (0 : Fin 2 → ℝ)) h0 h0
    · fin_cases i <;> simp
  refine proposition_20_C_1 htr (fun t i => ?_) (exercise_20_C_6 hconc hmono hk hl hDF hq h20C1)
    ?_
  · fin_cases i
    · simpa [rsPrices] using hq t
    · simpa [rsPrices] using mul_pos (hq (t + 1)) (hmpl t)
  · unfold Transversality
    have hlim : Tendsto (fun t => q (t + 1) * B) atTop (𝓝 0) := by
      simpa using (h20C2.comp (tendsto_add_atTop_nat 1)).mul_const B
    refine squeeze_zero_norm (fun t => ?_) hlim
    simp only [rsPrices, rsPath, rsPlan, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_zero, add_zero, Real.norm_eq_abs,
      abs_mul, abs_of_pos (hq (t + 1))]
    exact mul_le_mul_of_nonneg_left (hbdd t) (hq (t + 1)).le

/-- **Example 20.C.7** (MWG, p. 742), the cost-of-adjustment model with fixed labor: if
`(k₀, k₁) = (k_{t-1}, k_t)` maximizes, coordinate by coordinate, the profit
`s (F(k₀) - k₁ - γ(k₁ - k₀)) + q k₁ - q₀ k₀`, then (i) `q = s (1 + γ'(k₁ - k₀))` and
(ii) `q₀ = s (F'(k₀) + γ'(k₁ - k₀))`; hence (20.C.3)
`q₀ / q = (F'(k₀) + γ'(k₁ - k₀)) / (1 + γ'(k₁ - k₀))`, which is (20.C.1) when `γ ≡ 0`. -/
theorem example_20_C_7 {F γ : ℝ → ℝ} {k₀ k₁ s q q₀ F' γ' : ℝ} (hF : HasDerivAt F F' k₀)
    (hγ : HasDerivAt γ γ' (k₁ - k₀))
    (hmax₁ : IsLocalMax (fun b => s * (F k₀ - b - γ (b - k₀)) + q * b - q₀ * k₀) k₁)
    (hmax₀ : IsLocalMax (fun a => s * (F a - k₁ - γ (k₁ - a)) + q * k₁ - q₀ * a) k₀) :
    q = s * (1 + γ') ∧ q₀ = s * (F' + γ') ∧
      (q ≠ 0 → 1 + γ' ≠ 0 → q₀ / q = (F' + γ') / (1 + γ')) := by
  have hγ₁ : HasDerivAt (fun b => γ (b - k₀)) γ' k₁ := hγ.comp_sub_const k₁ k₀
  have hγ₀ : HasDerivAt (fun a => γ (k₁ - a)) (-γ') k₀ := by
    have h : HasDerivAt γ γ' (k₁ - k₀) := hγ
    exact h.comp_const_sub k₁ k₀
  have hd₁ : HasDerivAt (fun b => s * (F k₀ - b - γ (b - k₀)) + q * b - q₀ * k₀)
      (s * (0 - 1 - γ') + q * 1 - 0) k₁ :=
    ((((hasDerivAt_const k₁ (F k₀)).sub (hasDerivAt_id k₁)).sub hγ₁).const_mul s |>.add
      ((hasDerivAt_id k₁).const_mul q)).sub (hasDerivAt_const k₁ _)
  have hd₀ : HasDerivAt (fun a => s * (F a - k₁ - γ (k₁ - a)) + q * k₁ - q₀ * a)
      (s * (F' - 0 - -γ') + 0 - q₀ * 1) k₀ :=
    ((((hF.sub (hasDerivAt_const k₀ k₁)).sub hγ₀).const_mul s).add
      (hasDerivAt_const k₀ _)).sub ((hasDerivAt_id k₀).const_mul q₀)
  have e₁ := hmax₁.hasDerivAt_eq_zero hd₁
  have e₀ := hmax₀.hasDerivAt_eq_zero hd₀
  have hi : q = s * (1 + γ') := by linarith
  have hii : q₀ = s * (F' + γ') := by linarith
  refine ⟨hi, hii, fun hq hγ1 => ?_⟩
  have hs : s ≠ 0 := by rintro rfl; exact hq (by simpa using hi)
  rw [hi, hii]
  field_simp

/-- **Example 20.C.7** (MWG, p. 742): with no adjustment costs (`γ ≡ 0`, so `γ' = 0`), (20.C.3)
is precisely (20.C.1): `q₀ / q = F'(k₀)`. -/
theorem example_20_C_7_no_adjustment {F' q q₀ s : ℝ} (hi : q = s * (1 + 0))
    (hii : q₀ = s * (F' + 0)) (hq : q ≠ 0) : q₀ / q = F' := by
  have hs : s ≠ 0 := by rintro rfl; exact hq (by simpa using hi)
  rw [hi, hii]
  field_simp
  ring

end MWG.EquilibriumTime

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Equilibrium with one consumer (MWG Section 20.D, pp. 743-746)

MWG, Chapter 20, Section 20.D up to Proposition 20.D.2, pp. 743-746, with Exercises 20.D.1-20.D.4
(p. 784).

The consumer's consumption set is `X ⊆ ℝ^L` (`ℝ^L_+` in MWG; the positive orthant when the
one-period utility is logarithmic, footnote 10). The budget set at prices `p` and wealth `w` is
the set of bounded streams in `X` whose expenditure `∑_t p_t · c_t` does not exceed `w`, stated
through the partial sums (`InBudget`).

* The consumption stream of a path, `c_t = y_{a,t-1} + y_{bt} + ω_t` (`consumption`), and the
  identity **(20.D.1)** (`identity_20_D_1`).
* **Definition 20.D.1** (`WalrasEq`), with a proved instance (`example_20_D_1_ii`).
* Strict monotonicity makes the budget constraint bind (`budget_binds`).
* **Proposition 20.D.1** (`proposition_20_D_1`): equilibrium satisfies transversality.
* Condition (ii') and **Exercise 20.D.2** (`exercise_20_D_2_to`, `exercise_20_D_2_of`).
* **Definition 20.D.2** (`MyopicUtilityMax`), **Exercise 20.D.3** (`exercise_20_D_3`), the
  equivalence of (20.D.5) and (20.D.6) (`foc_20_D_5_iff_20_D_6`).
* **Proposition 20.D.2** (`proposition_20_D_2`).
* **Example 20.D.1** and **Exercise 20.D.4**: `example_20_D_1_foc`, `exercise_20_D_4`,
  `example_20_D_1_i`, `example_20_D_1_ii` (a full Walrasian equilibrium), and the correction of
  part (iii) (`example_20_D_1_iii_false`, `example_20_D_1_iii_corrected`).
* **Exercise 20.D.1**: the single budget constraint as a sequence of constraints
  (`exercise_20_D_1`).

Departures. Prices are required to be nonnegative and the wealth series to converge in
Definition 20.D.1 (MWG derives the finiteness of `w` from monotonicity). The claim in
Example 20.D.1(iii) that a fraction `δ` of wealth is invested is false for a general `F`.
-/

open Filter Topology

namespace MWG.EquilibriumTime

variable {L : ℕ}

/-- The consumption stream `c_t = y_{a,t-1} + y_{bt} + ω_t` of a path (MWG, p. 744). -/
def consumption (ω : ℕ → Fin L → ℝ) (y : ℕ → ProdPlan (Fin L)) (t : ℕ) : Fin L → ℝ :=
  netOutput y t + ω t

/-- **(20.D.1)** (MWG, p. 744): `∑_{t ≤ T} (π_t + p_t · ω_t) - ∑_{t ≤ T} p_t · c_t =
p_{T+1} · y_{aT}`. -/
theorem identity_20_D_1 (p : ℕ → Fin L → ℝ) (y : ℕ → ProdPlan (Fin L)) (ω : ℕ → Fin L → ℝ)
    (T : ℕ) :
    ∑ t ∈ Finset.range (T + 1), (periodProfit p y t + p t ⬝ᵥ ω t)
      - ∑ t ∈ Finset.range (T + 1), p t ⬝ᵥ consumption ω y t = p (T + 1) ⬝ᵥ (y T).2 := by
  have h := sum_value_netOutput p y T
  simp only [consumption, dotProduct_add, Finset.sum_add_distrib] at h ⊢
  linarith

/-- `c` lies in the budget set of prices `p` and wealth `w` (MWG, (20.D.4)): a bounded stream in
the consumption set `X` with `∑_{t < T} p_t · c_t ≤ w` for every `T`. -/
def InBudget (X : Set (Fin L → ℝ)) (p : ℕ → Fin L → ℝ) (w : ℝ) (c : ℕ → Fin L → ℝ) : Prop :=
  (∀ t, c t ∈ X) ∧ BoundedStream c ∧ ∀ T, ∑ t ∈ Finset.range T, p t ⬝ᵥ c t ≤ w

/-- `c` **maximizes utility** (20.B.1) in the budget set: it is in the budget set, its utility
series converges, and no budget-feasible stream with a convergent utility series is better. -/
def UtilityMax (X : Set (Fin L → ℝ)) (δ : ℝ) (u : (Fin L → ℝ) → ℝ) (p : ℕ → Fin L → ℝ)
    (w : ℝ) (c : ℕ → Fin L → ℝ) : Prop :=
  InBudget X p w c ∧ Summable (fun t => δ ^ t * u (c t)) ∧
    ∀ c', InBudget X p w c' → Summable (fun t => δ ^ t * u (c' t)) →
      discountedUtility δ u c' ≤ discountedUtility δ u c

/-- With nonnegative prices and consumption, the partial-sum budget constraint is the
constraint `∑_t p_t · c_t ≤ w`. -/
theorem expenditure_summable {p c : ℕ → Fin L → ℝ} (hp : ∀ t, 0 ≤ p t) (hc : ∀ t, 0 ≤ c t)
    {w : ℝ} (h : ∀ T, ∑ t ∈ Finset.range T, p t ⬝ᵥ c t ≤ w) :
    Summable (fun t => p t ⬝ᵥ c t) ∧ ∑' t, p t ⬝ᵥ c t ≤ w :=
  ⟨summable_of_sum_range_le (fun t => dotProduct_nonneg_of_nonneg (hp t) (hc t)) h,
    Real.tsum_le_of_sum_range_le (fun t => dotProduct_nonneg_of_nonneg (hp t) (hc t)) h⟩

/-- Two streams that differ only on a finite set of dates differ in utility by the finite sum
over those dates. -/
theorem discountedUtility_sub_of_finite {δ : ℝ} {u : (Fin L → ℝ) → ℝ} {c c' : ℕ → Fin L → ℝ}
    (s : Finset ℕ) (hs : ∀ t ∉ s, c' t = c t) (h : Summable fun t => δ ^ t * u (c t))
    (h' : Summable fun t => δ ^ t * u (c' t)) :
    discountedUtility δ u c' - discountedUtility δ u c
      = ∑ t ∈ s, δ ^ t * (u (c' t) - u (c t)) := by
  unfold discountedUtility
  rw [← h'.tsum_sub h]
  rw [tsum_eq_sum (s := s) (fun t ht => by rw [hs t ht]; ring)]
  exact Finset.sum_congr rfl fun t _ => by ring

/-- Changing a stream at finitely many dates keeps its utility series convergent. -/
theorem summable_of_finite_change {δ : ℝ} {u : (Fin L → ℝ) → ℝ} {c c' : ℕ → Fin L → ℝ}
    (s : Finset ℕ) (hs : ∀ t ∉ s, c' t = c t) (h : Summable fun t => δ ^ t * u (c t)) :
    Summable fun t => δ ^ t * u (c' t) := by
  have hfin : Summable fun t => if t ∈ s then δ ^ t * u (c' t) - δ ^ t * u (c t) else 0 :=
    summable_of_ne_finset_zero (s := s) (fun t ht => by simp [ht])
  refine (h.add hfin).congr fun t => ?_
  by_cases ht : t ∈ s
  · simp [ht]
  · simp [ht, hs t ht]

/-- A coordinate bump changes one coordinate by at most its size. -/
theorem abs_add_smul_single_le (x : Fin L → ℝ) (a : ℝ) (i j : Fin L) :
    |(x + a • (Pi.single i 1 : Fin L → ℝ)) j| ≤ |x j| + |a| := by
  by_cases h : j = i
  · subst h
    simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
    exact abs_add_le _ _
  · simp [h]

/-- A positive coordinate bump is a nonzero nonnegative vector. -/
theorem single_smul_pos {a : ℝ} (ha : 0 < a) (i : Fin L) :
    (0 : Fin L → ℝ) < a • Pi.single i 1 := by
  refine lt_of_le_of_ne (fun j => ?_) (fun h => ?_)
  · by_cases hj : j = i
    · subst hj; simp [ha.le]
    · simp [hj]
  · have := congrFun h i
    simp at this
    exact ha.ne' this.symm

/-- **Strict monotonicity makes the budget constraint bind** (MWG, p. 745): if `u` is strictly
increasing on an upward-closed consumption set and no budget-feasible change of `c` at date `0`
raises utility, then `∑_t p_t · c_t = w`. Prices are assumed nonnegative. -/
theorem budget_binds [NeZero L] {X : Set (Fin L → ℝ)} (hX0 : X ⊆ Set.Ici 0)
    (hXup : ∀ x ∈ X, ∀ x', x ≤ x' → x' ∈ X) {δ : ℝ} {u : (Fin L → ℝ) → ℝ}
    (hu : StrictMonoOn u X) {p : ℕ → Fin L → ℝ} (hp : ∀ t, 0 ≤ p t) {w : ℝ}
    {c : ℕ → Fin L → ℝ} (hc : InBudget X p w c) (hs : Summable fun t => δ ^ t * u (c t))
    (hmax : ∀ c', InBudget X p w c' → (∀ t, t ≠ 0 → c' t = c t) →
      discountedUtility δ u c' ≤ discountedUtility δ u c) :
    HasSum (fun t => p t ⬝ᵥ c t) w := by
  obtain ⟨hsum, hle⟩ := expenditure_summable hp (fun t => hX0 (hc.1 t)) hc.2.2
  refine (hsum.hasSum_iff).2 (le_antisymm hle ?_)
  by_contra hlt
  push Not at hlt
  set S := ∑' t, p t ⬝ᵥ c t
  set i : Fin L := 0
  set ε := (w - S) / (p 0 i + 1) with hε
  have hpi : 0 ≤ p 0 i := hp 0 i
  have hεpos : 0 < ε := div_pos (by linarith) (by linarith)
  have hεle : p 0 i * ε ≤ w - S := by
    rw [hε, mul_div_assoc']
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  set c' : ℕ → Fin L → ℝ := fun t => c t + if t = 0 then ε • Pi.single i 1 else 0 with hc'
  have hdiff : ∀ t, t ≠ 0 → c' t = c t := fun t ht => by simp [hc', ht]
  have hc'0 : c' 0 = c 0 + ε • Pi.single i 1 := by simp [hc']
  have hlt0 : c 0 < c' 0 := by
    rw [hc'0]
    exact lt_add_of_pos_right _ (single_smul_pos hεpos i)
  have hbud : InBudget X p w c' := by
    refine ⟨fun t => ?_, ?_, fun T => ?_⟩
    · rcases eq_or_ne t 0 with rfl | ht
      · exact hXup _ (hc.1 0) _ hlt0.le
      · rw [hdiff t ht]; exact hc.1 t
    · obtain ⟨M, hM⟩ := hc.2.1
      refine ⟨M + ε, fun t j => ?_⟩
      rcases eq_or_ne t 0 with rfl | ht
      · rw [hc'0]
        have := abs_add_smul_single_le (c 0) ε i j
        rw [abs_of_pos hεpos] at this
        linarith [hM 0 j]
      · rw [hdiff t ht]; linarith [hM t j]
    · have hpart : ∑ t ∈ Finset.range T, p t ⬝ᵥ c' t
          = ∑ t ∈ Finset.range T, p t ⬝ᵥ c t
            + ∑ t ∈ Finset.range T, if t = 0 then p 0 ⬝ᵥ (ε • Pi.single i 1) else 0 := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun t _ => ?_
        rcases eq_or_ne t 0 with rfl | ht
        · simp [hc', dotProduct_add]
        · simp [hc', ht]
      have hextra : (∑ t ∈ Finset.range T, if t = 0 then p 0 ⬝ᵥ (ε • Pi.single i 1) else 0)
          ≤ p 0 i * ε := by
        rw [Finset.sum_ite_eq' (Finset.range T) 0]
        split_ifs
        · simp [dotProduct_smul, dotProduct_single, mul_comm]
        · exact mul_nonneg hpi hεpos.le
      have hS : ∑ t ∈ Finset.range T, p t ⬝ᵥ c t ≤ S :=
        hsum.sum_le_tsum _ (fun t _ => dotProduct_nonneg_of_nonneg (hp t) (hX0 (hc.1 t)))
      linarith
  have hgt : discountedUtility δ u c < discountedUtility δ u c' := by
    have hs' := summable_of_finite_change {0} (fun t ht => hdiff t (by simpa using ht)) hs
    have := discountedUtility_sub_of_finite {0} (fun t ht => hdiff t (by simpa using ht)) hs hs'
    rw [Finset.sum_singleton, pow_zero, one_mul] at this
    have hu0 : u (c 0) < u (c' 0) := hu (hc.1 0) (hbud.1 0) hlt0
    linarith
  exact absurd (hmax c' hbud hdiff) (not_le.2 hgt)

variable (X : Set (Fin L → ℝ)) (Y : Set (ProdPlan (Fin L))) (δ : ℝ) (u : (Fin L → ℝ) → ℝ)
  (ω p : ℕ → Fin L → ℝ) (y : ℕ → ProdPlan (Fin L)) in
/-- **Definition 20.D.1** (MWG, p. 744): a bounded production path `y` and a bounded price
sequence `p` form a Walrasian equilibrium if (i) consumptions are feasible, (ii) the path is
myopically profit maximizing, and (iii) the consumption stream maximizes utility in the budget
set with wealth `w = ∑_t π_t + ∑_t p_t · ω_t`. Departures: prices are nonnegative and the wealth
series converges (MWG derive the finiteness of `w` from monotonicity, p. 745). -/
structure WalrasEq where
  /-- The production path is bounded. -/
  boundedPath : BoundedPath y
  /-- The price sequence is bounded. -/
  boundedPrices : ∃ B : ℝ, ∀ t i, |p t i| ≤ B
  /-- Prices are nonnegative. -/
  pricesNonneg : ∀ t, 0 ≤ p t
  /-- (i), (20.D.2): consumption is feasible. -/
  feasible : ∀ t, consumption ω y t ∈ X
  /-- (ii), (20.D.3): short-run profit maximization. -/
  myopic : MyopicProfitMax Y p y
  /-- Wealth is finite. -/
  wealthSummable : Summable fun t => periodProfit p y t + p t ⬝ᵥ ω t
  /-- (iii), (20.D.4): utility maximization in the budget set. -/
  utilityMax : UtilityMax X δ u p (∑' t, (periodProfit p y t + p t ⬝ᵥ ω t)) (consumption ω y)

/-- **Proposition 20.D.1** (MWG, p. 745): at a Walrasian equilibrium (with a strictly increasing
one-period utility on an upward-closed consumption set in `ℝ^L_+`), the transversality condition
`p_{t+1} · y_{at} → 0` holds. -/
theorem proposition_20_D_1 [NeZero L] {X : Set (Fin L → ℝ)} (hX0 : X ⊆ Set.Ici 0)
    (hXup : ∀ x ∈ X, ∀ x', x ≤ x' → x' ∈ X) {Y : Set (ProdPlan (Fin L))} {δ : ℝ}
    {u : (Fin L → ℝ) → ℝ} (hu : StrictMonoOn u X) {ω p : ℕ → Fin L → ℝ}
    {y : ℕ → ProdPlan (Fin L)} (he : WalrasEq X Y δ u ω p y) : Transversality p y := by
  set w := ∑' t, (periodProfit p y t + p t ⬝ᵥ ω t)
  have hexp : HasSum (fun t => p t ⬝ᵥ consumption ω y t) w :=
    budget_binds hX0 hXup hu he.pricesNonneg he.utilityMax.1 he.utilityMax.2.1
      fun c' hc' _ => he.utilityMax.2.2 c' hc'
        (summable_of_finite_change {0} (fun t ht => by simp_all) he.utilityMax.2.1)
  have h1 := he.wealthSummable.hasSum.tendsto_sum_nat
  have h2 := hexp.tendsto_sum_nat
  have h3 : Tendsto (fun T => ∑ t ∈ Finset.range (T + 1), (periodProfit p y t + p t ⬝ᵥ ω t)
      - ∑ t ∈ Finset.range (T + 1), p t ⬝ᵥ consumption ω y t) atTop (𝓝 (w - w)) :=
    (h1.comp (tendsto_add_atTop_nat 1)).sub (h2.comp (tendsto_add_atTop_nat 1))
  rw [sub_self] at h3
  unfold Transversality
  exact h3.congr fun T => identity_20_D_1 p y ω T

/-- **Condition (ii')** (MWG, p. 745): the path maximizes total profits: the profit series
converges and, for every path and every horizon `T`, the profits up to `T` do not exceed the
total profits of `y`. -/
def TotalProfitMax (Y : Set (ProdPlan (Fin L))) (p : ℕ → Fin L → ℝ) (y : ℕ → ProdPlan (Fin L)) :
    Prop :=
  IsProdPath Y y ∧ Summable (periodProfit p y) ∧
    ∀ y', IsProdPath Y y' → ∀ T, ∑ t ∈ Finset.range (T + 1), periodProfit p y' t ≤
      ∑' t, periodProfit p y t

/-- **Exercise 20.D.2**, first part (MWG, p. 784): condition (ii') implies condition (ii). -/
theorem exercise_20_D_2_to {Y : Set (ProdPlan (Fin L))} {p : ℕ → Fin L → ℝ}
    {y : ℕ → ProdPlan (Fin L)} (h : TotalProfitMax Y p y) : MyopicProfitMax Y p y := by
  refine ⟨h.1, fun t z hz => ?_⟩
  by_contra hlt
  push Not at hlt
  set y' := Function.update y t z with hy'
  have hpath : IsProdPath Y y' := fun s => by
    rcases eq_or_ne s t with rfl | hs
    · simpa [hy'] using hz
    · simpa [hy', hs] using h.1 s
  set g := planValue (p t) (p (t + 1)) z - periodProfit p y t with hg
  have hgpos : 0 < g := by rw [hg]; linarith
  have hsplit : ∀ T, t ≤ T → ∑ s ∈ Finset.range (T + 1), periodProfit p y' s
      = ∑ s ∈ Finset.range (T + 1), periodProfit p y s + g := by
    intro T hT
    rw [← Finset.sum_erase_add _ _ (Finset.mem_range.2 (Nat.lt_succ_of_le hT)),
      ← Finset.sum_erase_add (s := Finset.range (T + 1)) (f := periodProfit p y)
        (Finset.mem_range.2 (Nat.lt_succ_of_le hT))]
    have he : ∑ s ∈ (Finset.range (T + 1)).erase t, periodProfit p y' s
        = ∑ s ∈ (Finset.range (T + 1)).erase t, periodProfit p y s :=
      Finset.sum_congr rfl fun s hs => by
        simp [periodProfit, hy', Finset.ne_of_mem_erase hs]
    rw [he, hg]
    simp [periodProfit, hy']
  have hlim := (h.2.1.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)).add_const g
  have hbound : ∀ T, t ≤ T →
      ∑ s ∈ Finset.range (T + 1), periodProfit p y s + g ≤ ∑' s, periodProfit p y s :=
    fun T hT => (hsplit T hT) ▸ h.2.2 y' hpath T
  have := le_of_tendsto hlim (eventually_atTop.2 ⟨t, hbound⟩)
  linarith

/-- **Exercise 20.D.2**, second part (MWG, p. 784): condition (ii), with `0 ∈ Y` (assumption (ii)
of Section 20.C) and a convergent profit series (part of `w < ∞`), implies condition (ii'). -/
theorem exercise_20_D_2_of {Y : Set (ProdPlan (Fin L))} (h0 : (0 : ProdPlan (Fin L)) ∈ Y)
    {p : ℕ → Fin L → ℝ} {y : ℕ → ProdPlan (Fin L)} (h : MyopicProfitMax Y p y)
    (hs : Summable (periodProfit p y)) : TotalProfitMax Y p y := by
  refine ⟨h.1, hs, fun y' hy' T => ?_⟩
  have hnn : ∀ t, 0 ≤ periodProfit p y t := fun t => by
    have := h.2 t 0 h0
    simpa [planValue] using this
  calc ∑ t ∈ Finset.range (T + 1), periodProfit p y' t
      ≤ ∑ t ∈ Finset.range (T + 1), periodProfit p y t :=
        Finset.sum_le_sum fun t _ => h.2 t _ (hy' t)
    _ ≤ ∑' t, periodProfit p y t := hs.sum_le_tsum _ (fun t _ => hnn t)

/-- **Definition 20.D.2** (MWG, p. 745): `c` is myopically (short-run) utility maximizing in the
budget set of `p` and `w` if no budget-feasible stream differing from `c` only at two consecutive
dates `t, t+1` gives higher utility. -/
def MyopicUtilityMax (X : Set (Fin L → ℝ)) (δ : ℝ) (u : (Fin L → ℝ) → ℝ)
    (p : ℕ → Fin L → ℝ) (w : ℝ) (c : ℕ → Fin L → ℝ) : Prop :=
  InBudget X p w c ∧ Summable (fun t => δ ^ t * u (c t)) ∧
    ∀ t c', InBudget X p w c' → (∀ s, s ≠ t → s ≠ t + 1 → c' s = c s) →
      discountedUtility δ u c' ≤ discountedUtility δ u c

/-- A continuous linear functional on `ℝ^L` is the sum of its partial derivatives weighted by
the coordinates. -/
theorem clm_apply_eq_sum (D : (Fin L → ℝ) →L[ℝ] ℝ) (v : Fin L → ℝ) :
    D v = ∑ i, v i * D (Pi.single i 1) := by
  conv_lhs => rw [show v = ∑ i, v i • (Pi.single i 1 : Fin L → ℝ) by
    funext j; simp [Finset.sum_apply, Pi.single_apply]]
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul]

/-- The conditions **(20.D.5)** (MWG, p. 745): for every `t` there is `λ_t > 0` with
`λ_t p_t = ∇u(c_t)` and `λ_t p_{t+1} = δ ∇u(c_{t+1})`. -/
def Foc20D5 (δ : ℝ) (p : ℕ → Fin L → ℝ) (Du : ℕ → (Fin L → ℝ) →L[ℝ] ℝ) : Prop :=
  ∀ t, ∃ lam : ℝ, 0 < lam ∧ (∀ v, lam * (p t ⬝ᵥ v) = Du t v) ∧
    ∀ v, lam * (p (t + 1) ⬝ᵥ v) = δ * Du (t + 1) v

/-- The conditions **(20.D.6)** (MWG, p. 746): for some `λ > 0`, `λ p_t = δ^t ∇u(c_t)` for all
`t`. -/
def Foc20D6 (δ : ℝ) (p : ℕ → Fin L → ℝ) (Du : ℕ → (Fin L → ℝ) →L[ℝ] ℝ) : Prop :=
  ∃ lam : ℝ, 0 < lam ∧ ∀ t v, lam * (p t ⬝ᵥ v) = δ ^ t * Du t v

/-- **(20.D.5) is equivalent to (20.D.6)** (MWG, pp. 745-746), for `δ > 0` and nonzero prices:
`λ_{t-1} = δ λ_t`, so `λ = λ_0` works. -/
theorem foc_20_D_5_iff_20_D_6 {δ : ℝ} (hδ : 0 < δ) {p : ℕ → Fin L → ℝ}
    (hp : ∀ t, p t ≠ 0) {Du : ℕ → (Fin L → ℝ) →L[ℝ] ℝ} :
    Foc20D5 δ p Du ↔ Foc20D6 δ p Du := by
  constructor
  · intro h
    choose lam hlam h1 h2 using h
    -- `λ_t = δ λ_{t+1}`
    have hrec : ∀ t, lam t = δ * lam (t + 1) := by
      intro t
      obtain ⟨i, hi⟩ : ∃ i, p (t + 1) i ≠ 0 := by
        by_contra hc; push Not at hc; exact hp (t + 1) (funext hc)
      have e1 := h2 t (Pi.single i 1)
      have e2 := h1 (t + 1) (Pi.single i 1)
      simp only [dotProduct_single, mul_one] at e1 e2
      have : lam t * p (t + 1) i = δ * lam (t + 1) * p (t + 1) i := by rw [e1, ← e2]; ring
      exact mul_right_cancel₀ hi this
    have hpow : ∀ t, lam 0 = δ ^ t * lam t := by
      intro t
      induction t with
      | zero => simp
      | succ t ih => rw [ih, hrec t, pow_succ]; ring
    refine ⟨lam 0, hlam 0, fun t v => ?_⟩
    rw [hpow t, mul_assoc, h1 t v]
  · rintro ⟨lam, hlam, h⟩
    refine fun t => ⟨lam / δ ^ t, div_pos hlam (pow_pos hδ t), fun v => ?_, fun v => ?_⟩
    · rw [div_mul_eq_mul_div, h t v]
      field_simp
    · rw [div_mul_eq_mul_div, h (t + 1) v, pow_succ]
      field_simp

/-- **Exercise 20.D.3** (MWG, p. 745): a strictly positive bounded stream `c ≫ 0` is myopically
utility maximizing for `p` and `w` if and only if `∑_t p_t · c_t = w` and the first-order
conditions (20.D.5) hold. Here `u` is concave and strictly increasing on `ℝ^L_+`, differentiable
at every `c_t` with strictly positive marginal utilities, and `0 < δ`. -/
theorem exercise_20_D_3 [NeZero L] {δ : ℝ} (hδ : 0 < δ) {u : (Fin L → ℝ) → ℝ}
    (hconc : ConcaveOn ℝ (Set.Ici 0) u) (hmono : StrictMonoOn u (Set.Ici 0))
    {c : ℕ → Fin L → ℝ} (hc : ∀ t, StrictPos (c t)) (hb : BoundedStream c)
    (hs : Summable fun t => δ ^ t * u (c t)) {Du : ℕ → (Fin L → ℝ) →L[ℝ] ℝ}
    (hDu : ∀ t, HasFDerivAt u (Du t) (c t)) (hDpos : ∀ t i, 0 < Du t (Pi.single i 1))
    {p : ℕ → Fin L → ℝ} {w : ℝ} :
    MyopicUtilityMax (Set.Ici 0) δ u p w c ↔
      HasSum (fun t => p t ⬝ᵥ c t) w ∧ Foc20D5 δ p Du := by
  have hc0 : ∀ t, 0 ≤ c t := fun t i => (hc t i).le
  constructor
  · rintro ⟨hbud, -, hmax⟩
    -- prices are strictly positive
    have hppos : ∀ t i, 0 < p t i := by
      intro t i
      by_contra hneg
      push Not at hneg
      set c' : ℕ → Fin L → ℝ := fun s => c s + if s = t then (1 : ℝ) • Pi.single i 1 else 0
        with hc'
      have hdiff : ∀ s, s ≠ t → c' s = c s := fun s hs => by simp [hc', hs]
      have hc't : c' t = c t + (1 : ℝ) • Pi.single i 1 := by simp [hc']
      have hlt : c t < c' t := by
        rw [hc't]; exact lt_add_of_pos_right _ (single_smul_pos one_pos i)
      have hbud' : InBudget (Set.Ici 0) p w c' := by
        refine ⟨fun s => ?_, ?_, fun T => ?_⟩
        · rcases eq_or_ne s t with rfl | hs
          · exact Set.mem_Ici.2 ((hc0 s).trans hlt.le)
          · rw [hdiff s hs]; exact hc0 s
        · obtain ⟨M, hM⟩ := hb
          refine ⟨M + 1, fun s j => ?_⟩
          rcases eq_or_ne s t with rfl | hs
          · rw [hc't]
            have := abs_add_smul_single_le (c s) 1 i j
            rw [abs_one] at this
            linarith [hM s j]
          · rw [hdiff s hs]; linarith [hM s j]
        · have hle : ∑ s ∈ Finset.range T, p s ⬝ᵥ c' s ≤ ∑ s ∈ Finset.range T, p s ⬝ᵥ c s := by
            refine Finset.sum_le_sum fun s _ => ?_
            rcases eq_or_ne s t with rfl | hs
            · rw [hc't, dotProduct_add, dotProduct_smul, dotProduct_single, mul_one, one_smul]
              linarith
            · rw [hdiff s hs]
          exact hle.trans (hbud.2.2 T)
      have hs' := summable_of_finite_change {t} (fun s hst => hdiff s (by simpa using hst)) hs
      have hd := discountedUtility_sub_of_finite {t}
        (fun s hst => hdiff s (by simpa using hst)) hs hs'
      rw [Finset.sum_singleton] at hd
      have hu := hmono (Set.mem_Ici.2 (hc0 t)) (Set.mem_Ici.2 ((hc0 t).trans hlt.le)) hlt
      have := hmax t c' hbud' (fun s hs _ => hdiff s hs)
      have : 0 < δ ^ t * (u (c' t) - u (c t)) := mul_pos (pow_pos hδ t) (by linarith)
      linarith
    have hp0 : ∀ t, 0 ≤ p t := fun t i => (hppos t i).le
    have hbind : HasSum (fun t => p t ⬝ᵥ c t) w :=
      budget_binds (fun _ h => h) (fun x hx x' hxx' => Set.mem_Ici.2 ((Set.mem_Ici.1 hx).trans
        hxx')) hmono hp0 hbud hs
        (fun c' hc' hdiff => hmax 0 c' hc' (fun s hs _ => hdiff s hs))
    have hpos_open : IsOpen (Set.univ.pi fun _ : Fin L => Set.Ioi (0 : ℝ)) :=
      isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioi
    refine ⟨hbind, fun t => ?_⟩
    -- the cross-date first-order conditions
    have hcross : ∀ i j, p (t + 1) j * Du t (Pi.single i 1)
        = δ * p t i * Du (t + 1) (Pi.single j 1) := by
      intro i j
      set v : Fin L → ℝ := p (t + 1) j • Pi.single i 1 with hv
      set v' : Fin L → ℝ := -(p t i • Pi.single j 1) with hv'
      set φ : ℝ → ℝ := fun θ => δ ^ t * u (c t + θ • v) + δ ^ (t + 1) * u (c (t + 1) + θ • v')
        with hφdef
      have hφ : HasDerivAt φ (δ ^ t * Du t v + δ ^ (t + 1) * Du (t + 1) v') 0 := by
        have h1 : HasDerivAt (fun θ : ℝ => c t + θ • v) v 0 := by
          simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add (c t)
        have h2 : HasDerivAt (fun θ : ℝ => c (t + 1) + θ • v') v' 0 := by
          simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v').const_add (c (t + 1))
        have g1 := (hDu t).comp_hasDerivAt_of_eq (0 : ℝ) h1 (by simp)
        have g2 := (hDu (t + 1)).comp_hasDerivAt_of_eq (0 : ℝ) h2 (by simp)
        exact (g1.const_mul _).add (g2.const_mul _)
      have hloc : IsLocalMax φ 0 := by
        have hcont1 : Continuous fun θ : ℝ => c t + θ • v := by fun_prop
        have hcont2 : Continuous fun θ : ℝ => c (t + 1) + θ • v' := by fun_prop
        have hn1 : ∀ᶠ θ in 𝓝 (0 : ℝ), c t + θ • v ∈ Set.univ.pi fun _ => Set.Ioi 0 :=
          hcont1.continuousAt.preimage_mem_nhds (hpos_open.mem_nhds (by
            simp only [zero_smul, add_zero]
            exact Set.mem_univ_pi.2 fun k => Set.mem_Ioi.2 (hc t k)))
        have hn2 : ∀ᶠ θ in 𝓝 (0 : ℝ), c (t + 1) + θ • v' ∈ Set.univ.pi fun _ => Set.Ioi 0 :=
          hcont2.continuousAt.preimage_mem_nhds (hpos_open.mem_nhds (by
            simp only [zero_smul, add_zero]
            exact Set.mem_univ_pi.2 fun k => Set.mem_Ioi.2 (hc (t + 1) k)))
        filter_upwards [hn1, hn2] with θ hθ1 hθ2
        rw [Set.mem_univ_pi] at hθ1 hθ2
        set c' : ℕ → Fin L → ℝ := fun s => c s + (if s = t then θ • v else 0)
          + (if s = t + 1 then θ • v' else 0) with hc'
        have ht1 : t + 1 ≠ t := by omega
        have hc't : c' t = c t + θ • v := by simp [hc']
        have hc't1 : c' (t + 1) = c (t + 1) + θ • v' := by simp [hc']
        have hdiff : ∀ s, s ≠ t → s ≠ t + 1 → c' s = c s := fun s h1 h2 => by
          simp [hc', h1, h2]
        have hcnn : ∀ s, 0 ≤ c' s := fun s => by
          rcases eq_or_ne s t with rfl | h1
          · rw [hc't]; exact fun k => (hθ1 k).le
          rcases eq_or_ne s (t + 1) with rfl | h2
          · rw [hc't1]; exact fun k => (hθ2 k).le
          rw [hdiff s h1 h2]; exact hc0 s
        have hcost : p t ⬝ᵥ (θ • v) + p (t + 1) ⬝ᵥ (θ • v') = 0 := by
          simp only [hv, hv', dotProduct_smul, dotProduct_neg, dotProduct_single, smul_eq_mul,
            mul_one]
          ring
        have hbud' : InBudget (Set.Ici 0) p w c' := by
          refine ⟨hcnn, ?_, ?_⟩
          · obtain ⟨M, hM⟩ := hb
            refine ⟨M + |θ * p (t + 1) j| + |θ * -p t i|, fun s k => ?_⟩
            have hv1 : θ • v = (θ * p (t + 1) j) • (Pi.single i 1 : Fin L → ℝ) := by
              rw [hv, smul_smul]
            have hv2 : θ • v' = (θ * -p t i) • (Pi.single j 1 : Fin L → ℝ) := by
              rw [hv', smul_neg, smul_smul, ← neg_smul, mul_neg]
            rcases eq_or_ne s t with rfl | h1
            · rw [hc't, hv1]
              have := abs_add_smul_single_le (c s) (θ * p (s + 1) j) i k
              linarith [hM s k, abs_nonneg (θ * -p s i)]
            rcases eq_or_ne s (t + 1) with rfl | h2
            · rw [hc't1, hv2]
              have := abs_add_smul_single_le (c (t + 1)) (θ * -p t i) j k
              linarith [hM (t + 1) k, abs_nonneg (θ * p (t + 1) j)]
            rw [hdiff s h1 h2]
            linarith [hM s k, abs_nonneg (θ * p (t + 1) j), abs_nonneg (θ * -p t i)]
          · have hsum' : HasSum (fun s => p s ⬝ᵥ c' s) w := by
              have hfin : HasSum (fun s => (if s = t then p t ⬝ᵥ (θ • v) else 0)
                  + (if s = t + 1 then p (t + 1) ⬝ᵥ (θ • v') else 0)) 0 := by
                have := (hasSum_ite_eq t (p t ⬝ᵥ (θ • v))).add
                  (hasSum_ite_eq (t + 1) (p (t + 1) ⬝ᵥ (θ • v')))
                rwa [hcost] at this
              have := hbind.add hfin
              rw [add_zero] at this
              refine this.congr_fun fun s => ?_
              simp only [hc', dotProduct_add]
              split_ifs <;> simp_all
            intro T
            rw [← hsum'.tsum_eq]
            exact hsum'.summable.sum_le_tsum _
              (fun s _ => dotProduct_nonneg_of_nonneg (hp0 s) (hcnn s))
        have hfs : ∀ s ∉ ({t, t + 1} : Finset ℕ), c' s = c s := fun s hst => by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hst
          exact hdiff s hst.1 hst.2
        have hs' := summable_of_finite_change _ hfs hs
        have hd := discountedUtility_sub_of_finite _ hfs hs hs'
        rw [Finset.sum_pair (by omega), hc't, hc't1] at hd
        have hle := hmax t c' hbud' hdiff
        simp only [hφdef, zero_smul, add_zero]
        nlinarith
      have h0 := hloc.hasDerivAt_eq_zero hφ
      simp only [hv, hv', map_smul, map_neg, smul_eq_mul, pow_succ] at h0
      have hδt : 0 < δ ^ t := pow_pos hδ t
      have : δ ^ t * (p (t + 1) j * Du t (Pi.single i 1)
          - δ * (p t i * Du (t + 1) (Pi.single j 1))) = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h hδt.ne'
      · linarith
    obtain ⟨i₀⟩ : Nonempty (Fin L) := inferInstance
    have hratio : ∀ i, Du t (Pi.single i 1) * p t i₀ = p t i * Du t (Pi.single i₀ 1) := by
      intro i
      have h1 := hcross i₀ i₀
      have h2 := hcross i i₀
      have : p (t + 1) i₀ * (Du t (Pi.single i 1) * p t i₀)
          = p (t + 1) i₀ * (p t i * Du t (Pi.single i₀ 1)) := by
        linear_combination (p t i₀) * h2 - (p t i) * h1
      exact mul_left_cancel₀ (hppos (t + 1) i₀).ne' this
    have hp0' := (hppos t i₀).ne'
    refine ⟨Du t (Pi.single i₀ 1) / p t i₀, div_pos (hDpos t i₀) (hppos t i₀), fun v => ?_,
      fun v => ?_⟩
    · rw [clm_apply_eq_sum (Du t) v, dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [div_mul_eq_mul_div, div_eq_iff hp0']
      linear_combination (-(v i)) * hratio i
    · rw [clm_apply_eq_sum (Du (t + 1)) v, dotProduct, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [div_mul_eq_mul_div, div_eq_iff hp0']
      linear_combination (v j) * hcross i₀ j
  · rintro ⟨hbind, hfoc⟩
    have hppos : ∀ t i, 0 < p t i := by
      intro t i
      obtain ⟨lam, hlam, h1, -⟩ := hfoc t
      have := h1 (Pi.single i 1)
      rw [dotProduct_single, mul_one] at this
      have := hDpos t i
      nlinarith
    have hp0 : ∀ t, 0 ≤ p t := fun t i => (hppos t i).le
    have hbud : InBudget (Set.Ici 0) p w c := by
      refine ⟨fun t => hc0 t, hb, fun T => ?_⟩
      rw [← hbind.tsum_eq]
      exact hbind.summable.sum_le_tsum _
        (fun s _ => dotProduct_nonneg_of_nonneg (hp0 s) (hc0 s))
    refine ⟨hbud, hs, fun t c' hc' hdiff => ?_⟩
    obtain ⟨lam, hlam, h1, h2⟩ := hfoc t
    have hfinset : ∀ s ∉ ({t, t + 1} : Finset ℕ), c' s = c s := fun s hst => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hst
      exact hdiff s hst.1 hst.2
    have hs' := summable_of_finite_change _ hfinset hs
    have hd := discountedUtility_sub_of_finite _ hfinset hs hs'
    rw [Finset.sum_pair (by omega)] at hd
    -- the expenditure of `c'` is at most `w`
    obtain ⟨hsum', hle'⟩ := expenditure_summable hp0 (fun s => hc'.1 s) hc'.2.2
    have hcost : p t ⬝ᵥ (c' t - c t) + p (t + 1) ⬝ᵥ (c' (t + 1) - c (t + 1)) ≤ 0 := by
      have heq : ∑' s, p s ⬝ᵥ c' s - ∑' s, p s ⬝ᵥ c s
          = p t ⬝ᵥ (c' t - c t) + p (t + 1) ⬝ᵥ (c' (t + 1) - c (t + 1)) := by
        rw [← hsum'.tsum_sub hbind.summable,
          tsum_eq_sum (s := {t, t + 1}) (fun s hs => by rw [hfinset s hs, sub_self]),
          Finset.sum_pair (by omega), dotProduct_sub, dotProduct_sub]
      rw [← heq, hbind.tsum_eq]
      linarith
    have g1 := MWG.GeneralEquilibriumExamples.concave_le_fderiv hconc (Set.mem_Ici.2 (hc0 t))
      (hc'.1 t) (hDu t)
    have g2 := MWG.GeneralEquilibriumExamples.concave_le_fderiv hconc
      (Set.mem_Ici.2 (hc0 (t + 1))) (hc'.1 (t + 1)) (hDu (t + 1))
    rw [← h1] at g1
    have e2 := h2 (c' (t + 1) - c (t + 1))
    have hδt : 0 < δ ^ t := pow_pos hδ t
    have key : δ ^ t * (u (c' t) - u (c t)) + δ ^ (t + 1) * (u (c' (t + 1)) - u (c (t + 1)))
        ≤ δ ^ t * (lam * (p t ⬝ᵥ (c' t - c t) + p (t + 1) ⬝ᵥ (c' (t + 1) - c (t + 1)))) := by
      rw [pow_succ]
      have : δ * (u (c' (t + 1)) - u (c (t + 1))) ≤ lam * (p (t + 1) ⬝ᵥ (c' (t + 1) - c (t + 1)))
          := by rw [e2]; nlinarith
      nlinarith
    have : δ ^ t * (lam * (p t ⬝ᵥ (c' t - c t) + p (t + 1) ⬝ᵥ (c' (t + 1) - c (t + 1)))) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hδt.le (mul_nonpos_of_nonneg_of_nonpos hlam.le hcost)
    linarith

/-- **Proposition 20.D.2** (MWG, p. 746): if `∑_t p_t · c_t = w < ∞` and (20.D.6) holds, then `c`
maximizes utility in the budget set of `p` and `w`. Proved for a one-period utility concave on a
convex consumption set `X ⊆ ℝ^L_+` and differentiable at every `c_t`, with nonnegative prices. -/
theorem proposition_20_D_2 {X : Set (Fin L → ℝ)} (hX0 : X ⊆ Set.Ici 0) {δ : ℝ} (hδ : 0 ≤ δ)
    {u : (Fin L → ℝ) → ℝ} (hconc : ConcaveOn ℝ X u) {p : ℕ → Fin L → ℝ} (hp : ∀ t, 0 ≤ p t)
    {w : ℝ} {c : ℕ → Fin L → ℝ} (hcX : ∀ t, c t ∈ X) (hb : BoundedStream c)
    (hs : Summable fun t => δ ^ t * u (c t)) (hbind : HasSum (fun t => p t ⬝ᵥ c t) w)
    {Du : ℕ → (Fin L → ℝ) →L[ℝ] ℝ} (hDu : ∀ t, HasFDerivAt u (Du t) (c t)) {lam : ℝ}
    (hlam : 0 ≤ lam) (hfoc : ∀ t v, lam * (p t ⬝ᵥ v) = δ ^ t * Du t v) :
    UtilityMax X δ u p w c := by
  have hbud : InBudget X p w c := by
    refine ⟨hcX, hb, fun T => ?_⟩
    rw [← hbind.tsum_eq]
    exact hbind.summable.sum_le_tsum _
      (fun s _ => dotProduct_nonneg_of_nonneg (hp s) (hX0 (hcX s)))
  refine ⟨hbud, hs, fun c' hc' hs' => ?_⟩
  obtain ⟨hsum', hle'⟩ := expenditure_summable hp (fun s => hX0 (hc'.1 s)) hc'.2.2
  have hterm : ∀ t, δ ^ t * u (c' t) ≤ δ ^ t * u (c t) + lam * (p t ⬝ᵥ c' t - p t ⬝ᵥ c t) := by
    intro t
    have g := MWG.GeneralEquilibriumExamples.concave_le_fderiv hconc (hcX t) (hc'.1 t) (hDu t)
    have e := hfoc t (c' t - c t)
    rw [dotProduct_sub] at e
    have := mul_le_mul_of_nonneg_left g (pow_nonneg hδ t)
    nlinarith
  have hrhs : Summable fun t => δ ^ t * u (c t) + lam * (p t ⬝ᵥ c' t - p t ⬝ᵥ c t) :=
    hs.add ((hsum'.sub hbind.summable).mul_left lam)
  have := Summable.tsum_le_tsum hterm hs' hrhs
  rw [hs.tsum_add ((hsum'.sub hbind.summable).mul_left lam),
    (hsum'.sub hbind.summable).tsum_mul_left, hsum'.tsum_sub hbind.summable,
    hbind.tsum_eq] at this
  unfold discountedUtility
  nlinarith [mul_le_mul_of_nonneg_left (sub_nonpos.2 hle') hlam]

/-- **Exercise 20.D.1** (MWG, p. 784): with borrowing and lending at a zero nominal rate, the
single budget constraint is a sequence of budget constraints. The asset (money) holdings
`m_t = m_{t-1} + p_t · (ω_t - c_t)`, `m_{-1} = 0`, satisfy the period-`t` constraint
`p_t · c_t + m_t = p_t · ω_t + m_{t-1}`, and `∑ p_t · c_t ≤ ∑ p_t · ω_t` exactly when the limit
of the holdings is nonnegative (no debt is left at infinity). -/
theorem exercise_20_D_1 {p c ω : ℕ → Fin L → ℝ} (hc : Summable fun t => p t ⬝ᵥ c t)
    (hω : Summable fun t => p t ⬝ᵥ ω t) :
    let m : ℕ → ℝ := fun t => ∑ s ∈ Finset.range (t + 1), p s ⬝ᵥ (ω s - c s)
    (p 0 ⬝ᵥ c 0 + m 0 = p 0 ⬝ᵥ ω 0) ∧
      (∀ t, p (t + 1) ⬝ᵥ c (t + 1) + m (t + 1) = p (t + 1) ⬝ᵥ ω (t + 1) + m t) ∧
      Tendsto m atTop (𝓝 (∑' t, p t ⬝ᵥ ω t - ∑' t, p t ⬝ᵥ c t)) ∧
      (∑' t, p t ⬝ᵥ c t ≤ ∑' t, p t ⬝ᵥ ω t ↔ 0 ≤ ∑' t, p t ⬝ᵥ ω t - ∑' t, p t ⬝ᵥ c t) := by
  intro m
  refine ⟨by simp [m, dotProduct_sub], fun t => ?_, ?_, by constructor <;> intro h <;> linarith⟩
  · simp only [m, Finset.sum_range_succ _ (t + 1), dotProduct_sub]
    ring
  · have h := (hω.sub hc).hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
    rw [hω.tsum_sub hc] at h
    refine h.congr fun t => ?_
    simp [m, dotProduct_sub, Function.comp]

/-! ### Example 20.D.1: logarithmic utility -/

/-- **Example 20.D.1** (MWG, p. 746): with one good and `u = ln`, the first-order conditions
`λ p_t = δ^t / c_t` and `∑ p_t c_t = w` give `w = 1 / (λ (1 - δ))` and
`p_t c_t = δ^t (1 - δ) w`. -/
theorem example_20_D_1_foc {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) {p c : ℕ → ℝ} {lam w : ℝ}
    (hlam : 0 < lam) (hfoc : ∀ t, lam * p t * c t = δ ^ t)
    (hw : HasSum (fun t => p t * c t) w) :
    w = 1 / (lam * (1 - δ)) ∧ ∀ t, p t * c t = δ ^ t * (1 - δ) * w := by
  have hpc : ∀ t, p t * c t = δ ^ t / lam := fun t => by
    rw [← hfoc t]; field_simp
  have hg : HasSum (fun t => p t * c t) ((1 - δ)⁻¹ / lam) := by
    have := (hasSum_geometric_of_lt_one hδ0 hδ1).div_const lam
    exact this.congr_fun fun t => hpc t
  have hweq : w = 1 / (lam * (1 - δ)) := by
    rw [hw.unique hg]; field_simp
  refine ⟨hweq, fun t => ?_⟩
  rw [hpc t, hweq]
  have : (1 : ℝ) - δ ≠ 0 := by linarith
  field_simp

/-- **Exercise 20.D.4** (MWG, p. 784): with `p_t c_t = δ^t (1 - δ) w` and `w > 0`, the savings
rate is constant: `p_T c_T / ∑_{t ≥ T} p_t c_t = 1 - δ` for every `T`. -/
theorem exercise_20_D_4 {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) {p c : ℕ → ℝ} {w : ℝ}
    (hw : 0 < w) (h : ∀ t, p t * c t = δ ^ t * (1 - δ) * w) (T : ℕ) :
    p T * c T / ∑' t, p (t + T) * c (t + T) = 1 - δ := by
  have hsum : ∑' t, p (t + T) * c (t + T) = δ ^ T * w := by
    simp_rw [h, pow_add]
    rw [show (fun t => δ ^ t * δ ^ T * (1 - δ) * w) = fun t => δ ^ t * (δ ^ T * (1 - δ) * w)
      by funext t; ring, tsum_mul_right, tsum_geometric_of_lt_one hδ0.le hδ1]
    have : (1 : ℝ) - δ ≠ 0 := by linarith
    field_simp
  rw [hsum, h T]
  have : δ ^ T * w ≠ 0 := (mul_pos (pow_pos hδ0 T) hw).ne'
  field_simp

/-- **Example 20.D.1(i)** (MWG, p. 746): in the exchange economy with one good and log utility, the
equilibrium consumption is `c* = ω`; with the normalization `∑ p_t ω_t = 1` the first-order
conditions force `p_t = δ^t (1 - δ) / ω_t`, and these prices satisfy the normalization and the
conditions (20.D.6) with `λ = 1 / (1 - δ)`. -/
theorem example_20_D_1_i {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) {ω p : ℕ → ℝ}
    (hω : ∀ t, 0 < ω t) :
    ((∃ lam, 0 < lam ∧ (∀ t, lam * p t * ω t = δ ^ t) ∧ HasSum (fun t => p t * ω t) 1) →
      ∀ t, p t = δ ^ t * (1 - δ) / ω t) ∧
    (HasSum (fun t => δ ^ t * (1 - δ) / ω t * ω t) 1 ∧
      ∀ t, 1 / (1 - δ) * (δ ^ t * (1 - δ) / ω t) * ω t = δ ^ t) := by
  have h1δ : (1 : ℝ) - δ ≠ 0 := by linarith
  refine ⟨fun ⟨lam, hlam, hfoc, hw⟩ t => ?_, ?_, fun t => ?_⟩
  · obtain ⟨-, h⟩ := example_20_D_1_foc hδ0 hδ1 hlam hfoc hw
    have := h t
    field_simp [(hω t).ne'] at this ⊢
    linarith
  · have := (hasSum_geometric_of_lt_one hδ0 hδ1).mul_right (1 - δ)
    rw [inv_mul_cancel₀ h1δ] at this
    exact this.congr_fun fun t => by field_simp [(hω t).ne']
  · field_simp [(hω t).ne']

/-- The linear technology of Example 20.D.1(ii): `a` units of output at `t + 1` per unit of
input at `t`, `Y = {(-k, k') : k ≥ 0, k' ≤ a k}` (one good). -/
def linearTech (a : ℝ) : Set (ProdPlan (Fin 1)) :=
  {y | y.1 0 ≤ 0 ∧ y.2 0 ≤ -(a * y.1 0)}

/-- The strictly positive orthant of `ℝ¹`, the consumption set of the logarithmic utility. -/
def posOrthant1 : Set (Fin 1 → ℝ) := {x | 0 < x 0}

/-- The logarithmic one-period utility `u(x) = ln x₀`. -/
noncomputable def logUtil (x : Fin 1 → ℝ) : ℝ := Real.log (x 0)

theorem logUtil_concaveOn : ConcaveOn ℝ posOrthant1 logUtil := by
  refine ⟨?_, fun x hx y hy a b ha hb hab => ?_⟩
  · intro x hx y hy a b ha hb hab
    simp only [posOrthant1, Set.mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at *
    rcases eq_or_lt_of_le ha with rfl | ha'
    · have hb1 : b = 1 := by linarith
      subst hb1; simpa using hy
    · nlinarith [mul_pos ha' hx]
  · simp only [logUtil, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact (StrictConcaveOn.concaveOn strictConcaveOn_log_Ioi).2 hx hy ha hb hab

theorem logUtil_hasFDerivAt {x : Fin 1 → ℝ} (hx : 0 < x 0) :
    HasFDerivAt logUtil ((ContinuousLinearMap.toSpanSingleton ℝ (x 0)⁻¹).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0)) x :=
  (Real.hasDerivAt_log hx.ne').hasFDerivAt.comp x
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).hasFDerivAt

/-- **Example 20.D.1(ii)** (MWG, p. 747): one good, log utility, `ω₀ = 1`, `ω_t = 0` for `t > 0`,
and the linear technology `a`. With `1 ≤ a` and `a δ ≤ 1`, the prices `p_t = 1/a^t`, the
investments `k_t = δ (aδ)^t` and the consumptions `c_t = (aδ)^t (1 - δ)` form a Walrasian
equilibrium (Definition 20.D.1, with consumption set the positive reals). This is also a proved
instance of `WalrasEq`. -/
theorem example_20_D_1_ii {a δ : ℝ} (ha : 1 ≤ a) (hδ0 : 0 < δ) (hδ1 : δ < 1) (haδ : a * δ ≤ 1) :
    WalrasEq posOrthant1 (linearTech a) δ logUtil (fun t _ => if t = 0 then 1 else 0)
      (fun t _ => (a ^ t)⁻¹)
      (fun t => (fun _ => -(δ * (a * δ) ^ t), fun _ => a * (δ * (a * δ) ^ t))) := by
  set ω : ℕ → Fin 1 → ℝ := fun t _ => if t = 0 then 1 else 0 with hω
  set p : ℕ → Fin 1 → ℝ := fun t _ => (a ^ t)⁻¹ with hp
  set y : ℕ → ProdPlan (Fin 1) :=
    fun t => (fun _ => -(δ * (a * δ) ^ t), fun _ => a * (δ * (a * δ) ^ t)) with hy
  have ha0 : 0 < a := by linarith
  have haδ0 : 0 ≤ a * δ := by positivity
  have hpow : ∀ t, (a * δ) ^ t ≤ 1 := fun t => pow_le_one₀ haδ0 haδ
  -- consumption
  have hcons : ∀ t, consumption ω y t = fun _ => (a * δ) ^ t * (1 - δ) := by
    intro t
    funext i
    cases t with
    | zero => simp [consumption, netOutput, hy, hω]; ring
    | succ t => simp [consumption, netOutput, hy, hω, pow_succ]; ring
  have hprofit : ∀ t, periodProfit p y t = 0 := by
    intro t
    simp [periodProfit, planValue, dotProduct, hp, hy, pow_succ]
    field_simp
    ring
  have hwealth : HasSum (fun t => periodProfit p y t + p t ⬝ᵥ ω t) 1 := by
    have : (fun t => periodProfit p y t + p t ⬝ᵥ ω t) = fun t => if t = 0 then 1 else 0 := by
      funext t
      rw [hprofit t]
      rcases eq_or_ne t 0 with rfl | ht
      · simp [dotProduct, hp, hω]
      · simp [dotProduct, hp, hω, ht]
    rw [this]
    exact hasSum_ite_eq 0 1
  have hpc : ∀ t, p t ⬝ᵥ consumption ω y t = δ ^ t * (1 - δ) := by
    intro t
    rw [hcons t]
    simp [dotProduct, hp, mul_pow]
    field_simp
  refine ⟨⟨1, fun t i => ⟨?_, ?_⟩⟩, ⟨1, fun t i => ?_⟩, fun t i => ?_, fun t => ?_, ⟨fun t => ?_,
    fun t z hz => ?_⟩, hwealth.summable, ?_⟩
  · simp only [hy, abs_neg]
    rw [abs_of_nonneg (by positivity)]
    calc δ * (a * δ) ^ t ≤ 1 * 1 := mul_le_mul hδ1.le (hpow t) (by positivity) zero_le_one
      _ = 1 := one_mul 1
  · simp only [hy]
    rw [abs_of_nonneg (by positivity)]
    have : a * (δ * (a * δ) ^ t) = (a * δ) * (a * δ) ^ t := by ring
    rw [this]
    calc (a * δ) * (a * δ) ^ t ≤ 1 * 1 := mul_le_mul haδ (hpow t) (by positivity) zero_le_one
      _ = 1 := one_mul 1
  · simp only [hp]
    rw [abs_of_pos (by positivity)]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ ha)
  · simp only [hp]; positivity
  · rw [hcons t]; simp only [posOrthant1, Set.mem_ofPred_eq]
    exact mul_pos (pow_pos (by positivity) t) (by linarith)
  · simp only [linearTech, Set.mem_ofPred_eq, hy]
    constructor
    · have : 0 ≤ δ * (a * δ) ^ t := by positivity
      linarith
    · linarith
  · simp only [linearTech, Set.mem_ofPred_eq] at hz
    obtain ⟨h1, h2⟩ := hz
    rw [hprofit t]
    simp only [planValue, dotProduct, Finset.univ_unique, Fin.default_eq_zero,
      Finset.sum_singleton, hp]
    have hpt : 0 < (a ^ (t + 1))⁻¹ := by positivity
    have : (a ^ t)⁻¹ = a * (a ^ (t + 1))⁻¹ := by
      rw [pow_succ]; field_simp
    rw [this]
    nlinarith [mul_le_mul_of_nonneg_left h2 hpt.le]
  · rw [hwealth.tsum_eq]
    have hbind : HasSum (fun t => p t ⬝ᵥ consumption ω y t) 1 := by
      have := (hasSum_geometric_of_lt_one hδ0.le hδ1).mul_right (1 - δ)
      rw [inv_mul_cancel₀ (by linarith : (1 : ℝ) - δ ≠ 0)] at this
      exact this.congr_fun fun t => hpc t
    have hcpos : ∀ t, 0 < consumption ω y t 0 := fun t => by
      rw [hcons t]; exact mul_pos (pow_pos (by positivity) t) (by linarith)
    refine proposition_20_D_2 (fun x hx => fun i => ?_) hδ0.le logUtil_concaveOn
      (fun t i => by simp only [hp]; positivity) (fun t => hcpos t) ⟨1, fun t i => ?_⟩ ?_ hbind
      (fun t => logUtil_hasFDerivAt (hcpos t)) (lam := 1 / (1 - δ)) (by
        have : 0 < 1 - δ := by linarith
        positivity) (fun t v => ?_)
    · fin_cases i; exact (show 0 < x 0 from hx).le
    · rw [hcons t]
      simp only
      rw [abs_of_nonneg (by have := pow_nonneg haδ0 t; nlinarith)]
      nlinarith [hpow t]
    · -- the utility series converges: `δ^t (t ln(aδ) + ln(1 - δ))`
      have hc : ∀ t, logUtil (consumption ω y t) = t * Real.log (a * δ) + Real.log (1 - δ) := by
        intro t
        rw [hcons t]
        simp only [logUtil]
        rw [Real.log_mul (pow_pos (by positivity) t).ne' (by linarith), Real.log_pow]
      simp_rw [hc]
      have h1 : Summable fun t : ℕ => δ ^ t * (t * Real.log (a * δ)) := by
        have := (summable_pow_mul_geometric_of_norm_lt_one 1
          (by rw [Real.norm_eq_abs, abs_of_pos hδ0]; exact hδ1) : Summable fun n : ℕ =>
            ((n : ℝ) ^ 1 * δ ^ n)).mul_right (Real.log (a * δ))
        refine this.congr fun t => ?_
        ring
      have h2 := (summable_geometric_of_lt_one hδ0.le hδ1).mul_right (Real.log (1 - δ))
      refine (h1.add h2).congr fun t => ?_
      ring
    · rw [hcons t]
      simp only [dotProduct, Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, hp,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
        ContinuousLinearMap.proj_apply, smul_eq_mul]
      have : 0 < 1 - δ := by linarith
      field_simp
      rw [mul_pow]
      ring

/-- **Correction to Example 20.D.1(iii)** (MWG, p. 747): with `F(k) = k^α`, `0 < α < 1`, and log
utility, the rule "invest the fraction `δ` of wealth", `k_{t+1} = δ F(k_t)`, is incompatible with
the equilibrium conditions: the first-order conditions `λ p_t c_t = δ^t` (20.D.6) at `t = 1, 2`,
profit maximization `p_2 F'(k_1) = p_1`, and the resource constraints `c_{t+1} + k_{t+1} =
F(k_t)` with `k_{t+1} = δ F(k_t)` force `α = 1`. (The step `∑_{t ≥ T+1} p_t c_t = p_{T+1} F(k_T)`
fails because future profits are positive under decreasing returns.) -/
theorem example_20_D_1_iii_false {α δ lam : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    {k c p : ℕ → ℝ} (hk : ∀ t, 0 < k t) (hp : ∀ t, 0 < p t)
    (hfoc : ∀ t, lam * p t * c t = δ ^ t) (hprofit : p 2 * (α * k 1 ^ (α - 1)) = p 1)
    (hres : ∀ t, c (t + 1) + k (t + 1) = k t ^ α) (hrule : ∀ t, k (t + 1) = δ * k t ^ α) :
    α = 1 := by
  have hc1 : c 1 = (1 - δ) * k 0 ^ α := by have := hres 0; rw [hrule 0] at this; linarith
  have hc2 : c 2 = (1 - δ) * k 1 ^ α := by have := hres 1; rw [hrule 1] at this; linarith
  have hk0 : 0 < k 0 ^ α := Real.rpow_pos_of_pos (hk 0) α
  have hk1' : 0 < k 1 ^ α := Real.rpow_pos_of_pos (hk 1) α
  have h1δ : 0 < 1 - δ := by linarith
  have e1 := hfoc 1
  have e2 := hfoc 2
  -- `p_1 / p_2 = c_2 / (δ c_1)`
  have hlam : lam ≠ 0 := by
    rintro rfl; simp at e1; exact hδ0.ne' e1.symm
  have hratio : p 1 * δ * c 1 = p 2 * c 2 := by
    have : lam * (p 1 * δ * c 1) = lam * (p 2 * c 2) := by
      calc lam * (p 1 * δ * c 1) = δ * (lam * p 1 * c 1) := by ring
        _ = δ * δ ^ 1 := by rw [e1]
        _ = δ ^ 2 := by ring
        _ = lam * (p 2 * c 2) := by rw [← e2]; ring
    exact mul_left_cancel₀ hlam this
  rw [← hprofit, hc1, hc2] at hratio
  -- `α k_1^{α-1} k_1 = k_1^α`
  have hpow : k 1 ^ (α - 1) * k 1 = k 1 ^ α := by
    rw [← Real.rpow_add_one (hk 1).ne']; congr 1; ring
  have hk1 : δ * k 0 ^ α = k 1 := (hrule 0).symm
  have key : p 2 * (1 - δ) * k 1 ^ α * (α - 1) = 0 := by
    calc p 2 * (1 - δ) * k 1 ^ α * (α - 1)
        = p 2 * (α * k 1 ^ (α - 1)) * ((1 - δ) * (δ * k 0 ^ α))
          - p 2 * ((1 - δ) * k 1 ^ α) := by rw [hk1, ← hpow]; ring
      _ = 0 := by rw [sub_eq_zero, ← hratio]; ring
  have hne : p 2 * (1 - δ) * k 1 ^ α ≠ 0 := (mul_pos (mul_pos (hp 2) h1δ) hk1').ne'
  have := (mul_eq_zero.1 key).resolve_left hne
  linarith

/-- **Example 20.D.1(iii), corrected** (MWG, p. 747): with `F(k) = k^α` and log utility, the
investment rule `k_{t+1} = α δ F(k_t)` (with `c_{t+1} = (1 - αδ) F(k_t)`) satisfies, for every
`α` and `δ` (in particular `0 < α < 1`, `0 < δ < 1`), the Euler
equation `c_{t+1} / c_t = δ F'(k_t)`, i.e. the first-order conditions (20.D.6) with prices from
profit maximization `p_{t+1} F'(k_t) = p_t`. -/
theorem example_20_D_1_iii_corrected {α δ : ℝ} {k : ℕ → ℝ} (hk : ∀ t, 0 < k t)
    (hrule : ∀ t, k (t + 1) = α * δ * k t ^ α)
    (t : ℕ) :
    (1 - α * δ) * k (t + 1) ^ α = δ * (α * k (t + 1) ^ (α - 1)) * ((1 - α * δ) * k t ^ α) := by
  have hpow : k (t + 1) ^ (α - 1) * k (t + 1) = k (t + 1) ^ α := by
    rw [← Real.rpow_add_one (hk (t + 1)).ne']; congr 1; ring
  rw [← hpow]
  nth_rewrite 2 [hrule t]
  ring

end MWG.EquilibriumTime

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Equilibrium and the planning problem (MWG Section 20.D, pp. 747-749)

MWG, Chapter 20, Propositions 20.D.3-20.D.6, pp. 747-749.

The planning problem (20.D.7) maximizes `∑_t δ^t u(c_t)` over feasible bounded production paths
(`PlanOptimal`; MWG restrict all paths to be bounded, p. 744).

* **Proposition 20.D.3** (`proposition_20_D_3`): equilibrium paths solve the planning problem.
* **Proposition 20.D.4** (`proposition_20_D_4`): a planning solution with consumption bounded away
  from zero is an equilibrium for `p_t = δ^t ∇u(c_t)`, with a complete proof (MWG sketch it).
* **Proposition 20.D.5** (`proposition_20_D_5`): existence of a planning solution, by Tychonoff
  compactness of the space of paths and continuity of the discounted objective.
* **Proposition 20.D.6** (`proposition_20_D_6`): uniqueness of the planning consumption stream.

Departure. Proposition 20.D.5 assumes a uniform bound on all feasible production paths (the
alternative MWG offer on p. 744), not only on the consumption streams they generate.
-/

open Filter Topology

namespace MWG.EquilibriumTime

variable {L : ℕ}

/-- A production path is **feasible** for the endowments `ω` (MWG, p. 744): it is a path of `Y`
and sustains nonnegative consumption at every date. -/
def FeasiblePath (Y : Set (ProdPlan (Fin L))) (ω : ℕ → Fin L → ℝ) (y : ℕ → ProdPlan (Fin L)) :
    Prop :=
  IsProdPath Y y ∧ ∀ t, 0 ≤ consumption ω y t

/-- The **planning problem (20.D.7)** (MWG, p. 747): `y` is a feasible bounded path whose
consumption stream has the largest utility among all feasible bounded paths. -/
def PlanOptimal (Y : Set (ProdPlan (Fin L))) (δ : ℝ) (u : (Fin L → ℝ) → ℝ)
    (ω : ℕ → Fin L → ℝ) (y : ℕ → ProdPlan (Fin L)) : Prop :=
  FeasiblePath Y ω y ∧ BoundedPath y ∧ Summable (fun t => δ ^ t * u (consumption ω y t)) ∧
    ∀ y', FeasiblePath Y ω y' → BoundedPath y' →
      Summable (fun t => δ ^ t * u (consumption ω y' t)) →
      discountedUtility δ u (consumption ω y') ≤ discountedUtility δ u (consumption ω y)

/-- A bounded path with bounded endowments has a bounded consumption stream. -/
theorem boundedStream_consumption {ω : ℕ → Fin L → ℝ} {y : ℕ → ProdPlan (Fin L)}
    (hy : BoundedPath y) (hω : BoundedStream ω) : BoundedStream (consumption ω y) := by
  obtain ⟨α, hα⟩ := hy
  obtain ⟨M, hM⟩ := hω
  refine ⟨2 * α + M, fun t i => ?_⟩
  cases t with
  | zero =>
    simp only [consumption, netOutput, Pi.add_apply]
    have := abs_add_le ((y 0).1 i) (ω 0 i)
    linarith [(hα 0 i).1, (hα 0 i).2, hM 0 i, abs_nonneg ((y 0).2 i)]
  | succ t =>
    simp only [consumption, netOutput, Pi.add_apply]
    have h1 := abs_add_le ((y t).2 i + (y (t + 1)).1 i) (ω (t + 1) i)
    have h2 := abs_add_le ((y t).2 i) ((y (t + 1)).1 i)
    linarith [(hα t i).2, (hα (t + 1) i).1, hM (t + 1) i]

/-- **Proposition 20.D.3** (MWG, p. 747): a Walrasian equilibrium path solves the planning problem
(20.D.7). Uses inaction (`0 ∈ Y`), truncation, and nonnegative bounded endowments. -/
theorem proposition_20_D_3 {Y : Set (ProdPlan (Fin L))} (h0 : (0 : ProdPlan (Fin L)) ∈ Y)
    (htr : ∀ z ∈ Y, (z.1, 0) ∈ Y) {δ : ℝ} {u : (Fin L → ℝ) → ℝ} {ω p : ℕ → Fin L → ℝ}
    (hω0 : ∀ t, 0 ≤ ω t) (hωb : BoundedStream ω) {y : ℕ → ProdPlan (Fin L)}
    (he : WalrasEq (Set.Ici 0) Y δ u ω p y) : PlanOptimal Y δ u ω y := by
  set w := ∑' t, (periodProfit p y t + p t ⬝ᵥ ω t)
  have hnn : ∀ t, 0 ≤ periodProfit p y t + p t ⬝ᵥ ω t := by
    intro t
    have h1 : 0 ≤ periodProfit p y t := by
      have := he.myopic.2 t 0 h0
      simpa [planValue] using this
    exact add_nonneg h1 (dotProduct_nonneg_of_nonneg (he.pricesNonneg t) (hω0 t))
  refine ⟨⟨he.myopic.1, fun t => he.feasible t⟩, he.boundedPath, he.utilityMax.2.1,
    fun y' hy' hb' hs' => he.utilityMax.2.2 _ ⟨fun t => hy'.2 t,
      boundedStream_consumption hb' hωb, fun T => ?_⟩ hs'⟩
  rcases T with _ | T
  · simpa using tsum_nonneg hnn
  · -- the budget inequality, by the possibility of truncation and short-run profit maximization
    have h1 := sum_value_le_of_myopic htr he.myopic hy'.1 T
    have h2 := sum_value_netOutput p y T
    have h3 : ∑ t ∈ Finset.range (T + 1), (periodProfit p y t + p t ⬝ᵥ ω t) ≤ w :=
      he.wealthSummable.sum_le_tsum _ (fun t _ => hnn t)
    simp only [consumption, dotProduct_add, Finset.sum_add_distrib] at h3 ⊢
    linarith

/-! ### Proposition 20.D.4 -/

/-- Changing one plan of a bounded path keeps it bounded. -/
theorem BoundedPath.update {y : ℕ → ProdPlan (Fin L)} (hy : BoundedPath y) (T : ℕ)
    (z : ProdPlan (Fin L)) : BoundedPath (Function.update y T z) := by
  obtain ⟨α, hα⟩ := hy
  refine ⟨α + ‖z‖, fun t i => ?_⟩
  rcases eq_or_ne t T with rfl | ht
  · simp only [Function.update_self]
    have h1 : |z.1 i| ≤ ‖z‖ := by
      rw [← Real.norm_eq_abs]; exact (norm_le_pi_norm z.1 i).trans (norm_fst_le z)
    have h2 : |z.2 i| ≤ ‖z‖ := by
      rw [← Real.norm_eq_abs]; exact (norm_le_pi_norm z.2 i).trans (norm_snd_le z)
    have := (hα t i).1
    exact ⟨by linarith [abs_nonneg ((y t).1 i)], by linarith [abs_nonneg ((y t).1 i)]⟩
  · simp only [Function.update_of_ne ht]
    exact ⟨by linarith [(hα t i).1, norm_nonneg z], by linarith [(hα t i).2, norm_nonneg z]⟩

/-- A function with positive derivative at `0` and value `0` there is positive just to the right
of `0`. -/
theorem eventually_pos_of_hasDerivAt {g : ℝ → ℝ} {D : ℝ} (hg : HasDerivAt g D 0) (h0 : g 0 = 0)
    (hD : 0 < D) : ∀ᶠ θ in 𝓝[>] (0 : ℝ), 0 < g θ := by
  have hs := (hasDerivAt_iff_tendsto_slope.1 hg).mono_left (nhdsGT_le_nhdsNE 0)
  filter_upwards [hs.eventually (lt_mem_nhds hD), self_mem_nhdsWithin] with θ hθ hpos
  rw [slope_def_field, h0, sub_zero, sub_zero] at hθ
  exact (div_pos_iff_of_pos_right (Set.mem_Ioi.1 hpos)).1 hθ

/-- Bounds on the marginal utilities of a concave nondecreasing `u` at a point `x ≥ ε` of
`ℝ^L_+` below `(B, ..., B)`: `0 ≤ ∂_i u(x) ≤ (u(B, ..., B) - u(0)) / ε`. -/
theorem partial_bounds {u : (Fin L → ℝ) → ℝ} (hconc : ConcaveOn ℝ (Set.Ici 0) u)
    (hmono : MonotoneOn u (Set.Ici 0)) {x : Fin L → ℝ} {ε B : ℝ} (hε : 0 < ε)
    (hxε : ∀ i, ε ≤ x i) (hxB : ∀ i, x i ≤ B) {D : (Fin L → ℝ) →L[ℝ] ℝ}
    (hD : HasFDerivAt u D x) (i : Fin L) :
    0 ≤ D (Pi.single i 1) ∧ D (Pi.single i 1) ≤ (u (fun _ => B) - u 0) / ε := by
  have hx0 : (0 : Fin L → ℝ) ≤ x := fun j => hε.le.trans (hxε j)
  have he : (0 : Fin L → ℝ) ≤ Pi.single i 1 := by
    intro j; by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  constructor
  · have hxe : x ≤ x + Pi.single i 1 := le_add_of_nonneg_right he
    have g := MWG.GeneralEquilibriumExamples.concave_le_fderiv hconc (Set.mem_Ici.2 hx0)
      (Set.mem_Ici.2 (hx0.trans hxe)) hD
    have m := hmono (Set.mem_Ici.2 hx0) (Set.mem_Ici.2 (hx0.trans hxe)) hxe
    rw [add_sub_cancel_left] at g
    linarith
  · have hxm : (0 : Fin L → ℝ) ≤ x - ε • Pi.single i 1 := by
      intro j; by_cases hj : j = i
      · subst hj; simp [hxε j]
      · simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_apply, hj, ↓reduceIte, smul_eq_mul,
          mul_zero, sub_zero]
        exact hx0 j
    have g := MWG.GeneralEquilibriumExamples.concave_le_fderiv hconc (Set.mem_Ici.2 hx0)
      (Set.mem_Ici.2 hxm) hD
    rw [sub_sub_cancel_left, map_neg, map_smul, smul_eq_mul] at g
    have m1 := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hxm) hxm
    have hxB' : x ≤ fun _ => B := hxB
    have m2 := hmono (Set.mem_Ici.2 hx0) (Set.mem_Ici.2 (hx0.trans hxB')) hxB'
    rw [le_div_iff₀ hε]
    linarith

/-- **Proposition 20.D.4** (MWG, p. 748): a bounded solution of the planning problem (20.D.7) whose
consumption is bounded away from zero (`c_t ≥ ε` in every coordinate) is a Walrasian equilibrium
for the prices `p_t = δ^t ∇u(c_t)`. Here `Y` is convex, `u` is concave and nondecreasing on
`ℝ^L_+` and differentiable at every `c_t`, `0 < δ < 1`, and endowments are bounded. MWG sketch
the proof; it is given in full (prices are summable, which yields transversality, the budget
identity and, by Proposition 20.D.2, utility maximization; profit maximization follows from the
first-order term of a small convex perturbation of one plan). -/
theorem proposition_20_D_4 {Y : Set (ProdPlan (Fin L))} (hY : Convex ℝ Y) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1) {u : (Fin L → ℝ) → ℝ} (hconc : ConcaveOn ℝ (Set.Ici 0) u)
    (hmono : MonotoneOn u (Set.Ici 0)) {ω : ℕ → Fin L → ℝ} (hωb : BoundedStream ω)
    {y : ℕ → ProdPlan (Fin L)} (hopt : PlanOptimal Y δ u ω y) {ε : ℝ} (hε : 0 < ε)
    (hcε : ∀ t i, ε ≤ consumption ω y t i) {Du : ℕ → (Fin L → ℝ) →L[ℝ] ℝ}
    (hDu : ∀ t, HasFDerivAt u (Du t) (consumption ω y t)) :
    WalrasEq (Set.Ici 0) Y δ u ω (fun t i => δ ^ t * Du t (Pi.single i 1)) y := by
  set c := consumption ω y with hc
  set p : ℕ → Fin L → ℝ := fun t i => δ ^ t * Du t (Pi.single i 1) with hp
  obtain ⟨⟨hpath, hfeas⟩, hbdd, hsum, hmax⟩ := hopt
  obtain ⟨B, hB⟩ := boundedStream_consumption hbdd hωb
  set K := (u (fun _ => B) - u 0) / ε with hK
  have hpb : ∀ t i, 0 ≤ Du t (Pi.single i 1) ∧ Du t (Pi.single i 1) ≤ K := fun t i =>
    partial_bounds hconc hmono hε (hcε t) (fun j => (le_abs_self _).trans (hB t j)) (hDu t) i
  have hp0 : ∀ t, 0 ≤ p t := fun t i => mul_nonneg (pow_nonneg hδ0.le t) (hpb t i).1
  have hpsum : Summable fun t => ∑ i, p t i := by
    refine Summable.of_nonneg_of_le (fun t => Finset.sum_nonneg fun i _ => hp0 t i)
      (fun t => ?_) ((summable_geometric_of_lt_one hδ0.le hδ1).mul_right (Fintype.card (Fin L) * K))
    calc ∑ i, p t i ≤ ∑ _i : Fin L, δ ^ t * K :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hpb t i).2 (pow_nonneg hδ0.le t)
      _ = δ ^ t * (Fintype.card (Fin L) * K) := by simp; ring
  have hfoc : ∀ t v, 1 * (p t ⬝ᵥ v) = δ ^ t * Du t v := by
    intro t v
    rw [one_mul, clm_apply_eq_sum (Du t) v, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by simp only [hp]; ring
  have hpabs : ∀ t i, |p t i| ≤ K := fun t i => by
    simp only [hp]
    rw [abs_of_nonneg (mul_nonneg (pow_nonneg hδ0.le t) (hpb t i).1)]
    calc δ ^ t * Du t (Pi.single i 1) ≤ 1 * K :=
          mul_le_mul (pow_le_one₀ hδ0.le hδ1.le) (hpb t i).2 (hpb t i).1 zero_le_one
      _ = K := one_mul K
  clear_value p
  obtain ⟨α, hα⟩ := hbdd
  -- myopic profit maximization
  have hmyopic : MyopicProfitMax Y p y := by
    refine ⟨hpath, fun T z hz => ?_⟩
    by_contra hlt
    push Not at hlt
    set db := z.1 - (y T).1
    set da := z.2 - (y T).2
    set g : ℝ → ℝ := fun θ => δ ^ T * (u (c T + θ • db) - u (c T))
      + δ ^ (T + 1) * (u (c (T + 1) + θ • da) - u (c (T + 1))) with hg
    have hgd : HasDerivAt g (δ ^ T * Du T db + δ ^ (T + 1) * Du (T + 1) da) 0 := by
      have h1 : HasDerivAt (fun θ : ℝ => c T + θ • db) db 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const db).const_add (c T)
      have h2 : HasDerivAt (fun θ : ℝ => c (T + 1) + θ • da) da 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const da).const_add (c (T + 1))
      have g1 := (hDu T).comp_hasDerivAt_of_eq (0 : ℝ) h1 (by simp)
      have g2 := (hDu (T + 1)).comp_hasDerivAt_of_eq (0 : ℝ) h2 (by simp)
      have := ((g1.sub_const (u (c T))).const_mul (δ ^ T)).add
        ((g2.sub_const (u (c (T + 1)))).const_mul (δ ^ (T + 1)))
      exact this
    have hDpos : 0 < δ ^ T * Du T db + δ ^ (T + 1) * Du (T + 1) da := by
      rw [← hfoc T db, ← hfoc (T + 1) da]
      simp only [one_mul, db, da, dotProduct_sub, periodProfit, planValue] at hlt ⊢
      linarith
    have hev := eventually_pos_of_hasDerivAt hgd (by simp [hg]) hDpos
    -- small perturbations keep consumption nonnegative
    have hpos_open : IsOpen (Set.univ.pi fun _ : Fin L => Set.Ioi (0 : ℝ)) :=
      isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioi
    have hn : ∀ (x d : Fin L → ℝ), (∀ i, 0 < x i) →
        ∀ᶠ θ in 𝓝[>] (0 : ℝ), ∀ i, 0 < (x + θ • d) i := by
      intro x d hx
      have hcont : Continuous fun θ : ℝ => x + θ • d := by fun_prop
      have := hcont.continuousAt.preimage_mem_nhds (x := 0) (hpos_open.mem_nhds (by
        simp only [zero_smul, add_zero]
        exact Set.mem_univ_pi.2 fun k => Set.mem_Ioi.2 (hx k)))
      filter_upwards [nhdsWithin_le_nhds this] with θ hθ
      exact fun i => Set.mem_univ_pi.1 hθ i
    have hcpos : ∀ t i, 0 < c t i := fun t i => hε.trans_le (hcε t i)
    have hlt1 : ∀ᶠ θ in 𝓝[>] (0 : ℝ), θ < 1 :=
      nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)
    obtain ⟨θ, hgθ, hθ1, hθ2, hθlt, hθpos⟩ :=
      (hev.and ((hn _ db (hcpos T)).and ((hn _ da (hcpos (T + 1))).and
        (hlt1.and self_mem_nhdsWithin)))).exists
    have hθpos' : 0 < θ := hθpos
    -- the perturbed path
    set y' := Function.update y T ((1 - θ) • y T + θ • z) with hy'
    have hpath' : IsProdPath Y y' := fun t => by
      rcases eq_or_ne t T with rfl | ht
      · simp only [hy', Function.update_self]
        exact hY (hpath t) hz (by linarith) hθpos'.le (by ring)
      · simp only [hy', Function.update_of_ne ht]; exact hpath t
    have hc'T : consumption ω y' T = c T + θ • db := by
      funext i
      cases T with
      | zero => simp [consumption, netOutput, hy', c, db]; ring
      | succ T =>
        simp [consumption, netOutput, hy', c, db]
        ring
    have hc'T1 : consumption ω y' (T + 1) = c (T + 1) + θ • da := by
      funext i
      simp [consumption, netOutput, hy', c, da]
      ring
    have hc'other : ∀ t, t ≠ T → t ≠ T + 1 → consumption ω y' t = c t := by
      intro t h1 h2
      cases t with
      | zero => simp [consumption, netOutput, hy', c, Function.update_of_ne h1]
      | succ t =>
        have h3 : t ≠ T := fun h => h2 (by rw [h])
        simp [consumption, netOutput, hy', c, Function.update_of_ne h1, Function.update_of_ne h3]
    have hfin : ∀ t ∉ ({T, T + 1} : Finset ℕ), consumption ω y' t = c t := fun t ht => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht
      exact hc'other t ht.1 ht.2
    have hfeas' : FeasiblePath Y ω y' := by
      refine ⟨hpath', fun t => ?_⟩
      rcases eq_or_ne t T with rfl | h1
      · rw [hc'T]; exact fun i => (hθ1 i).le
      rcases eq_or_ne t (T + 1) with rfl | h2
      · rw [hc'T1]; exact fun i => (hθ2 i).le
      rw [hc'other t h1 h2]; exact hfeas t
    have hs' := summable_of_finite_change _ hfin hsum
    have hd := discountedUtility_sub_of_finite _ hfin hsum hs'
    rw [Finset.sum_pair (by omega), hc'T, hc'T1] at hd
    have := hmax y' hfeas' (BoundedPath.update ⟨α, hα⟩ T _) hs'
    simp only [hg] at hgθ
    linarith
  -- the wealth series
  have hwealth : Summable fun t => periodProfit p y t + p t ⬝ᵥ ω t := by
    obtain ⟨M, hM⟩ := hωb
    have hdot : ∀ (q v : Fin L → ℝ) (A : ℝ), 0 ≤ q → (∀ i, |v i| ≤ A) →
        |q ⬝ᵥ v| ≤ (∑ i, q i) * A := by
      intro q v A hq hv
      calc |q ⬝ᵥ v| ≤ ∑ i, |q i * v i| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i, q i * A := Finset.sum_le_sum fun i _ => by
            rw [abs_mul, abs_of_nonneg (hq i)]
            exact mul_le_mul_of_nonneg_left (hv i) (hq i)
        _ = (∑ i, q i) * A := by rw [Finset.sum_mul]
    have hps1 : Summable fun t => ∑ i, p (t + 1) i :=
      (summable_nat_add_iff (f := fun t => ∑ i, p t i) 1).2 hpsum
    refine Summable.of_norm_bounded ((hpsum.mul_right α).add ((hps1.mul_right α).add
      (hpsum.mul_right M))) fun t => ?_
    rw [Real.norm_eq_abs]
    simp only [periodProfit, planValue]
    have e1 := hdot (p t) (y t).1 α (hp0 t) fun i => (hα t i).1
    have e2 := hdot (p (t + 1)) (y t).2 α (hp0 (t + 1)) fun i => (hα t i).2
    have e3 := hdot (p t) (ω t) M (hp0 t) (hM t)
    calc |p t ⬝ᵥ (y t).1 + p (t + 1) ⬝ᵥ (y t).2 + p t ⬝ᵥ ω t|
        ≤ |p t ⬝ᵥ (y t).1| + |p (t + 1) ⬝ᵥ (y t).2| + |p t ⬝ᵥ ω t| := by
          have := abs_add_le (p t ⬝ᵥ (y t).1 + p (t + 1) ⬝ᵥ (y t).2) (p t ⬝ᵥ ω t)
          have := abs_add_le (p t ⬝ᵥ (y t).1) (p (t + 1) ⬝ᵥ (y t).2)
          linarith
      _ ≤ _ := by linarith
  -- transversality and the budget identity
  have htc : Tendsto (fun t => p (t + 1) ⬝ᵥ (y t).2) atTop (𝓝 0) :=
    tendsto_value_of_bounded (p := fun t => p (t + 1)) (v := fun t => (y t).2)
      (fun t => hp0 (t + 1)) ((summable_nat_add_iff (f := fun t => ∑ i, p t i) 1).2 hpsum)
      (fun t i => (hα t i).2)
  have hbind : HasSum (fun t => p t ⬝ᵥ c t) (∑' t, (periodProfit p y t + p t ⬝ᵥ ω t)) := by
    refine (hasSum_iff_tendsto_nat_of_nonneg
      (fun t => dotProduct_nonneg_of_nonneg (hp0 t) (hfeas t)) _).2 ?_
    have h1 := hwealth.hasSum.tendsto_sum_nat
    have h2 : Tendsto (fun T => ∑ t ∈ Finset.range (T + 1), (periodProfit p y t + p t ⬝ᵥ ω t)
        - p (T + 1) ⬝ᵥ (y T).2) atTop (𝓝 (∑' t, (periodProfit p y t + p t ⬝ᵥ ω t) - 0)) :=
      (h1.comp (tendsto_add_atTop_nat 1)).sub htc
    rw [sub_zero] at h2
    have h3 : Tendsto (fun T => ∑ t ∈ Finset.range (T + 1), p t ⬝ᵥ c t) atTop
        (𝓝 (∑' t, (periodProfit p y t + p t ⬝ᵥ ω t))) :=
      h2.congr fun T => by have := identity_20_D_1 p y ω T; simp only [c]; linarith
    exact (tendsto_add_atTop_iff_nat 1).1 h3
  refine ⟨⟨α, hα⟩, ⟨K, hpabs⟩, hp0, hfeas, hmyopic, hwealth, ?_⟩
  exact proposition_20_D_2 (fun _ h => h) hδ0.le hconc hp0 (fun t => hfeas t)
    (boundedStream_consumption ⟨α, hα⟩ hωb) hsum hbind hDu zero_le_one hfoc

/-! ### Propositions 20.D.5 and 20.D.6 -/

/-- A one-period utility continuous on `ℝ^L_+` has a convergent discounted series along every
bounded nonnegative stream. -/
theorem summable_of_continuousOn {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) {u : (Fin L → ℝ) → ℝ}
    (hu : ContinuousOn u (Set.Ici 0)) {c : ℕ → Fin L → ℝ} (hc : ∀ t, 0 ≤ c t)
    (hb : BoundedStream c) : Summable fun t => δ ^ t * u (c t) := by
  obtain ⟨M, hM⟩ := hb
  set R := max M 0
  have hK : IsCompact (Set.Ici (0 : Fin L → ℝ) ∩ Metric.closedBall 0 R) :=
    (isCompact_closedBall 0 R).inter_left isClosed_Ici
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hu.mono Set.inter_subset_left)
  refine summable_discounted hδ0 hδ1 (M := C) fun t => ?_
  have hmem : c t ∈ Set.Ici (0 : Fin L → ℝ) ∩ Metric.closedBall 0 R := by
    refine ⟨hc t, ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (pi_norm_le_iff_of_nonneg (le_max_right _ _)).2 fun i => by
      rw [Real.norm_eq_abs]; exact (hM t i).trans (le_max_left _ _)
  simpa [Real.norm_eq_abs] using hC _ hmem


/-- The consumption at a date depends continuously on the path (product topology). -/
theorem continuous_consumption (ω : ℕ → Fin L → ℝ) (t : ℕ) :
    Continuous fun y : ℕ → ProdPlan (Fin L) => consumption ω y t := by
  cases t with
  | zero =>
    simp only [consumption, netOutput]
    exact ((continuous_fst.comp (continuous_apply 0)).add continuous_const)
  | succ t =>
    simp only [consumption, netOutput]
    exact ((continuous_snd.comp (continuous_apply t)).add
      (continuous_fst.comp (continuous_apply (t + 1)))).add continuous_const

/-- The zero path consumes the endowments. -/
theorem consumption_zero (ω : ℕ → Fin L → ℝ) (t : ℕ) :
    consumption ω (fun _ => (0 : ProdPlan (Fin L))) t = ω t := by
  cases t <;> simp [consumption, netOutput]

/-- **Proposition 20.D.5** (MWG, p. 749): the planning problem (20.D.7) attains its maximum.
Hypotheses: `Y` closed with `0 ∈ Y`, endowments nonnegative and bounded, `u` continuous on
`ℝ^L_+`, `0 ≤ δ < 1`, and (departure) a uniform bound `‖y_t‖ ≤ B` on all feasible production
paths. The feasible paths form a compact set in the product topology (Tychonoff) and the
discounted objective is continuous on it (uniform convergence, by the Weierstrass M-test). -/
theorem proposition_20_D_5 {Y : Set (ProdPlan (Fin L))} (hYc : IsClosed Y)
    (h0 : (0 : ProdPlan (Fin L)) ∈ Y) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    {u : (Fin L → ℝ) → ℝ} (hu : ContinuousOn u (Set.Ici 0)) {ω : ℕ → Fin L → ℝ}
    (hω0 : ∀ t, 0 ≤ ω t) (hωb : BoundedStream ω) {B : ℝ}
    (hB : ∀ y, FeasiblePath Y ω y → ∀ t, ‖y t‖ ≤ B) :
    ∃ y, PlanOptimal Y δ u ω y := by
  set K := {y : ℕ → ProdPlan (Fin L) | FeasiblePath Y ω y} with hK
  have hclosed : IsClosed K := by
    have : K = ⋂ t, ({y : ℕ → ProdPlan (Fin L) | y t ∈ Y} ∩
        {y | 0 ≤ consumption ω y t}) := by
      ext y
      simp only [hK, FeasiblePath, IsProdPath, Set.mem_iInter, Set.mem_inter_iff]
      exact ⟨fun h t => ⟨h.1 t, h.2 t⟩, fun h => ⟨fun t => (h t).1, fun t => (h t).2⟩⟩
    rw [this]
    exact isClosed_iInter fun t => (hYc.preimage (continuous_apply t)).inter
      (isClosed_le continuous_const (continuous_consumption ω t))
  have hcompact : IsCompact K :=
    (isCompact_univ_pi fun _ => isCompact_closedBall (0 : ProdPlan (Fin L)) B).of_isClosed_subset
      hclosed fun y hy => Set.mem_univ_pi.2 fun t => by
        rw [Metric.mem_closedBall, dist_zero_right]; exact hB y hy t
  have hne : K.Nonempty := ⟨fun _ => 0, fun _ => h0, fun t => by
    rw [consumption_zero]; exact hω0 t⟩
  -- a bound on consumption, hence on utility, over `K`
  obtain ⟨M, hM⟩ := hωb
  set R := 2 * B + max M 0
  have hcR : ∀ y ∈ K, ∀ t, ‖consumption ω y t‖ ≤ R := by
    intro y hy t
    have hω : ‖ω t‖ ≤ max M 0 := (pi_norm_le_iff_of_nonneg (le_max_right _ _)).2 fun i => by
      rw [Real.norm_eq_abs]; exact (hM t i).trans (le_max_left _ _)
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB y hy 0)
    cases t with
    | zero =>
      simp only [consumption, netOutput]
      have := (norm_fst_le (y 0)).trans (hB y hy 0)
      linarith [norm_add_le (y 0).1 (ω 0)]
    | succ t =>
      simp only [consumption, netOutput]
      have h1 := (norm_snd_le (y t)).trans (hB y hy t)
      have h2 := (norm_fst_le (y (t + 1))).trans (hB y hy (t + 1))
      linarith [norm_add_le ((y t).2 + (y (t + 1)).1) (ω (t + 1)),
        norm_add_le (y t).2 (y (t + 1)).1]
  have hS : IsCompact (Set.Ici (0 : Fin L → ℝ) ∩ Metric.closedBall 0 R) :=
    (isCompact_closedBall 0 R).inter_left isClosed_Ici
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn (hu.mono Set.inter_subset_left)
  have hmemS : ∀ y ∈ K, ∀ t, consumption ω y t ∈ Set.Ici (0 : Fin L → ℝ) ∩
      Metric.closedBall 0 R := fun y hy t =>
    ⟨hy.2 t, by rw [Metric.mem_closedBall, dist_zero_right]; exact hcR y hy t⟩
  have hcont : ContinuousOn (fun y => ∑' t, δ ^ t * u (consumption ω y t)) K := by
    refine continuousOn_tsum (u := fun t => δ ^ t * C) (fun t => ?_)
      ((summable_geometric_of_lt_one hδ0 hδ1).mul_right C) (fun t y hy => ?_)
    · exact continuousOn_const.mul (hu.comp (continuous_consumption ω t).continuousOn
        fun y hy => hy.2 t)
    · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hδ0 t)]
      exact mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using hC _ (hmemS y hy t))
        (pow_nonneg hδ0 t)
  obtain ⟨y, hyK, hymax⟩ := hcompact.exists_isMaxOn hne hcont
  have hbdd : ∀ y' ∈ K, BoundedPath y' := fun y' hy' => ⟨B, fun t i => by
    constructor
    · rw [← Real.norm_eq_abs]
      exact ((norm_le_pi_norm (y' t).1 i).trans (norm_fst_le _)).trans (hB y' hy' t)
    · rw [← Real.norm_eq_abs]
      exact ((norm_le_pi_norm (y' t).2 i).trans (norm_snd_le _)).trans (hB y' hy' t)⟩
  refine ⟨y, hyK, hbdd y hyK, summable_discounted hδ0 hδ1 (M := C) fun t => ?_,
    fun y' hy' _ _ => hymax hy'⟩
  simpa [Real.norm_eq_abs] using hC _ (hmemS y hyK t)

/-- The consumption of a mixture of paths is the mixture of their consumptions. -/
theorem consumption_mix (ω : ℕ → Fin L → ℝ) (y y' : ℕ → ProdPlan (Fin L)) (t : ℕ) :
    consumption ω (fun s => (1 / 2 : ℝ) • y s + (1 / 2 : ℝ) • y' s) t
      = (1 / 2 : ℝ) • consumption ω y t + (1 / 2 : ℝ) • consumption ω y' t := by
  funext i
  cases t <;> simp [consumption, netOutput] <;> ring

/-- **Proposition 20.D.6** (MWG, p. 749): the planning problem (20.D.7) has at most one
consumption stream solution, for convex `Y`, `u` strictly concave and continuous on `ℝ^L_+`,
`0 < δ < 1` and bounded endowments. -/
theorem proposition_20_D_6 {Y : Set (ProdPlan (Fin L))} (hY : Convex ℝ Y) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1) {u : (Fin L → ℝ) → ℝ} (hu : StrictConcaveOn ℝ (Set.Ici 0) u)
    (hcont : ContinuousOn u (Set.Ici 0)) {ω : ℕ → Fin L → ℝ} (hωb : BoundedStream ω)
    {y y' : ℕ → ProdPlan (Fin L)} (h : PlanOptimal Y δ u ω y) (h' : PlanOptimal Y δ u ω y') :
    consumption ω y = consumption ω y' := by
  by_contra hne
  obtain ⟨t₀, ht₀⟩ : ∃ t, consumption ω y t ≠ consumption ω y' t := by
    by_contra hc; push Not at hc; exact hne (funext hc)
  set m : ℕ → ProdPlan (Fin L) := fun s => (1 / 2 : ℝ) • y s + (1 / 2 : ℝ) • y' s with hm
  have hcm : ∀ t, consumption ω m t
      = (1 / 2 : ℝ) • consumption ω y t + (1 / 2 : ℝ) • consumption ω y' t :=
    consumption_mix ω y y'
  have hmfeas : FeasiblePath Y ω m := by
    refine ⟨fun t => hY (h.1.1 t) (h'.1.1 t) (by norm_num) (by norm_num) (by norm_num),
      fun t => ?_⟩
    rw [hcm t]
    exact add_nonneg (smul_nonneg (by norm_num) (h.1.2 t)) (smul_nonneg (by norm_num) (h'.1.2 t))
  have hmb : BoundedPath m := by
    obtain ⟨α, hα⟩ := h.2.1
    obtain ⟨α', hα'⟩ := h'.2.1
    refine ⟨α + α', fun t i => ⟨?_, ?_⟩⟩
    · simp only [hm, Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have := abs_add_le (1 / 2 * (y t).1 i) (1 / 2 * (y' t).1 i)
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at this
      linarith [(hα t i).1, (hα' t i).1, abs_nonneg ((y t).1 i), abs_nonneg ((y' t).1 i)]
    · simp only [hm, Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have := abs_add_le (1 / 2 * (y t).2 i) (1 / 2 * (y' t).2 i)
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at this
      linarith [(hα t i).2, (hα' t i).2, abs_nonneg ((y t).2 i), abs_nonneg ((y' t).2 i)]
  have hms := summable_of_continuousOn hδ0.le hδ1 hcont hmfeas.2
    (boundedStream_consumption hmb hωb)
  have hle := h.2.2.2 m hmfeas hmb hms
  have heq : discountedUtility δ u (consumption ω y) = discountedUtility δ u (consumption ω y')
    := le_antisymm (h'.2.2.2 y h.1 h.2.1 h.2.2.1) (h.2.2.2 y' h'.1 h'.2.1 h'.2.2.1)
  have hs := h.2.2.1
  have hs' := h'.2.2.1
  have hlt : (1 / 2 : ℝ) * discountedUtility δ u (consumption ω y)
      + (1 / 2 : ℝ) * discountedUtility δ u (consumption ω y')
      < discountedUtility δ u (consumption ω m) := by
    unfold discountedUtility
    rw [← hs.tsum_mul_left, ← hs'.tsum_mul_left, ← (hs.mul_left _).tsum_add (hs'.mul_left _)]
    refine Summable.tsum_lt_tsum (i := t₀) (fun t => ?_) ?_ ((hs.mul_left _).add (hs'.mul_left _))
      hms
    · rw [hcm t]
      have hc := (StrictConcaveOn.concaveOn hu).2 (h.1.2 t) (h'.1.2 t)
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
      simp only [smul_eq_mul] at hc
      have hp := pow_nonneg hδ0.le t
      nlinarith [mul_le_mul_of_nonneg_left hc hp]
    · rw [hcm t₀]
      have hc := hu.2 (h.1.2 t₀) (h'.1.2 t₀) ht₀ (by norm_num : (0 : ℝ) < 1 / 2)
        (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
      simp only [smul_eq_mul] at hc
      have hp := pow_pos hδ0 t₀
      nlinarith [mul_lt_mul_of_pos_left hc hp]
  rw [heq] at hlt hle
  linarith

end MWG.EquilibriumTime

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Euler equations, the policy function and the value function (MWG Section 20.D, pp. 749-754)

MWG, Chapter 20, the computation of equilibrium in the `(N+1)`-sector model, pp. 749-754:
(20.D.8)-(20.D.12), Proposition 20.D.7, and Exercises 20.D.6, 20.D.8, 20.D.9 (p. 784).

The capital space is a real normed space `K` (`ℝ^N` in MWG), the admissible region is
`A ⊆ K × K`, `u : K × K → ℝ`, and a path `k : ℕ → K` is admissible from `k̄₀` if `k₀ = k̄₀` and
`(k_t, k_{t+1}) ∈ A` (`Admissible`). The objective used here is
`W(k) = ∑_{t ≥ 0} δ^t u(k_t, k_{t+1})` (`reducedObjective`); MWG's (20.D.8),
`∑_{t ≥ 1} δ^t u(k_{t-1}, k_t)`, is `δ W(k)` (`objective_20_D_8`), so the two problems have the same
solutions. The Euler equations (20.D.9) at the date `t + 1` read
`D₂u(k_t, k_{t+1}) + δ D₁u(k_{t+1}, k_{t+2}) = 0` (`EulerEq`).

* Necessity of the Euler equations at an interior optimum: `euler_of_optimal`.
* **Exercise 20.D.6**: for a concave `u` and an interior path, the Euler equations are necessary
  and sufficient for short-run optimality (`exercise_20_D_6`).
* **Proposition 20.D.7**: a bounded, strictly interior path satisfying the Euler equations is
  optimal (`proposition_20_D_7`).
* Uniqueness of the optimal path under strict concavity (`optimal_unique`).
* (20.D.10): tails of optimal paths are optimal and `k_{t+1} = ψ(k_t)` (`optimal_tail`,
  `policy_20_D_10`).
* (20.D.11): the Bellman equation for `V = sup W` (`bellman_20_D_11`); as printed, for the value
  of (20.D.8), it is off by the factor `δ` (`bellman_20_D_11_printed_false`).
* **Exercise 20.D.8** (`exercise_20_D_8_i`, `exercise_20_D_8_ii`) and **Exercise 20.D.9**
  (`exercise_20_D_9_first`, `exercise_20_D_9_second`).

The gradient inequality for concave functions on a normed space (`concave_le_fderiv_normed`)
reduces to Chapter 15's one-dimensional `MWG.GeneralEquilibriumExamples.concave_le_tangent`.
-/

open Filter Topology

namespace MWG.EquilibriumTime

/-- **The gradient inequality** for a concave function on a convex subset of a real normed
space: `f y ≤ f x + f'(y - x)`. -/
theorem concave_le_fderiv_normed {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set E} {f : E → ℝ} {f' : E →L[ℝ] ℝ} {x y : E} (hf : ConcaveOn ℝ S f) (hx : x ∈ S)
    (hy : y ∈ S) (hd : HasFDerivAt f f' x) : f y ≤ f x + f' (y - x) := by
  set g : ℝ → ℝ := fun s => f (AffineMap.lineMap x y s) with hg
  have hsub : Set.Icc (0 : ℝ) 1 ⊆ (AffineMap.lineMap x y) ⁻¹' S := fun s hs =>
    hf.1.lineMap_mem hx hy hs
  have hconc : ConcaveOn ℝ (Set.Icc 0 1) g :=
    (hf.comp_affineMap (AffineMap.lineMap x y)).subset hsub (convex_Icc 0 1)
  have hderiv : HasDerivAt g (f' (y - x)) 0 := by
    have h1 : HasDerivAt (AffineMap.lineMap x y : ℝ → E) (y - x) 0 :=
      AffineMap.hasDerivAt_lineMap
    have h2 : HasFDerivAt f f' (AffineMap.lineMap x y (0 : ℝ)) := by
      rw [AffineMap.lineMap_apply_zero]; exact hd
    exact h2.comp_hasDerivAt (0 : ℝ) h1
  have := MWG.GeneralEquilibriumExamples.concave_le_tangent hconc
    (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one) hderiv
  simpa [hg, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one] using this

/-- Changing a real sequence at finitely many indices preserves summability. -/
theorem summable_of_eq_off {a a' : ℕ → ℝ} (s : Finset ℕ) (h : ∀ t ∉ s, a' t = a t)
    (ha : Summable a) : Summable a' := by
  have hfin : Summable fun t => if t ∈ s then a' t - a t else 0 :=
    summable_of_ne_finset_zero (s := s) (fun t ht => by simp [ht])
  refine (ha.add hfin).congr fun t => ?_
  by_cases ht : t ∈ s
  · simp [ht]
  · simp [ht, h t ht]

/-- Changing a summable real sequence at finitely many indices changes its sum by the finite
sum of the changes. -/
theorem tsum_sub_eq_of_eq_off {a a' : ℕ → ℝ} (s : Finset ℕ) (h : ∀ t ∉ s, a' t = a t)
    (ha : Summable a) : ∑' t, a' t - ∑' t, a t = ∑ t ∈ s, (a' t - a t) := by
  rw [← (summable_of_eq_off s h ha).tsum_sub ha]
  exact tsum_eq_sum fun t ht => by rw [h t ht, sub_self]

variable {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]

/-- A capital path is **admissible** from `k̄₀` for the region `A` (MWG, (20.D.8)). -/
def Admissible (A : Set (K × K)) (k₀ : K) (k : ℕ → K) : Prop :=
  k 0 = k₀ ∧ ∀ t, (k t, k (t + 1)) ∈ A

/-- The objective `W(k) = ∑_{t ≥ 0} δ^t u(k_t, k_{t+1})`. -/
noncomputable def reducedObjective (δ : ℝ) (u : K × K → ℝ) (k : ℕ → K) : ℝ :=
  ∑' t, δ ^ t * u (k t, k (t + 1))

omit [NormedAddCommGroup K] [NormedSpace ℝ K] in
/-- MWG's objective (20.D.8), `∑_{t ≥ 1} δ^t u(k_{t-1}, k_t)` (with `u(k_{-1}, k₀) = 0`, footnote
12), is `δ W(k)`. -/
theorem objective_20_D_8 (δ : ℝ) (u : K × K → ℝ) (k : ℕ → K) :
    ∑' t, δ ^ (t + 1) * u (k t, k (t + 1)) = δ * reducedObjective δ u k := by
  unfold reducedObjective
  rw [← tsum_mul_left]
  exact tsum_congr fun t => by ring

/-- `k` **solves the planning problem (20.D.8)** from `k̄₀`: it is admissible with a convergent
objective, and no admissible path with a convergent objective does better. -/
def OptimalFrom (A : Set (K × K)) (δ : ℝ) (u : K × K → ℝ) (k₀ : K) (k : ℕ → K) : Prop :=
  Admissible A k₀ k ∧ Summable (fun t => δ ^ t * u (k t, k (t + 1))) ∧
    ∀ k', Admissible A k₀ k' → Summable (fun t => δ ^ t * u (k' t, k' (t + 1))) →
      reducedObjective δ u k' ≤ reducedObjective δ u k

/-- **The Euler equations (20.D.9)** (MWG, p. 750), with `Du t` the derivative of `u` at
`(k_t, k_{t+1})`: `D₂u(k_t, k_{t+1}) + δ D₁u(k_{t+1}, k_{t+2}) = 0` for every `t ≥ 0`. -/
def EulerEq (δ : ℝ) (Du : ℕ → K × K →L[ℝ] ℝ) : Prop :=
  ∀ t v, Du t (0, v) + δ * Du (t + 1) (v, 0) = 0

/-- **Necessity of the Euler equations** (MWG, p. 750), in the short-run form: if no admissible
path that differs from `k` at finitely many dates does better, `k` passes through the interior of
`A`, `δ > 0` and `u` is differentiable along `k`, then (20.D.9) holds. -/
theorem euler_of_shortRun {A : Set (K × K)} {δ : ℝ} (hδ : 0 < δ) {u : K × K → ℝ} {k₀ : K}
    {k : ℕ → K} (hadm : Admissible A k₀ k) (hsum0 : Summable fun t => δ ^ t * u (k t, k (t + 1)))
    (hshort : ∀ k', Admissible A k₀ k' → {t | k' t ≠ k t}.Finite →
      reducedObjective δ u k' ≤ reducedObjective δ u k)
    (hint : ∀ t, (k t, k (t + 1)) ∈ interior A)
    {Du : ℕ → K × K →L[ℝ] ℝ} (hDu : ∀ t, HasFDerivAt u (Du t) (k t, k (t + 1))) :
    EulerEq δ Du := by
  intro t v
  set φ : ℝ → ℝ := fun θ => δ ^ t * u (k t, k (t + 1) + θ • v)
    + δ ^ (t + 1) * u (k (t + 1) + θ • v, k (t + 2)) with hφ
  have hd : HasDerivAt φ (δ ^ t * Du t (0, v) + δ ^ (t + 1) * Du (t + 1) (v, 0)) 0 := by
    have h1 : HasDerivAt (fun θ : ℝ => (k t, k (t + 1) + θ • v)) ((0 : K), v) 0 := by
      refine HasDerivAt.prodMk (hasDerivAt_const _ _) ?_
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add (k (t + 1))
    have h2 : HasDerivAt (fun θ : ℝ => (k (t + 1) + θ • v, k (t + 2))) (v, (0 : K)) 0 := by
      refine HasDerivAt.prodMk ?_ (hasDerivAt_const _ _)
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add (k (t + 1))
    have g1 := (hDu t).comp_hasDerivAt_of_eq (0 : ℝ) h1 (by simp)
    have g2 := (hDu (t + 1)).comp_hasDerivAt_of_eq (0 : ℝ) h2 (by simp)
    exact (g1.const_mul _).add (g2.const_mul _)
  have hloc : IsLocalMax φ 0 := by
    have c1 : Continuous fun θ : ℝ => (k t, k (t + 1) + θ • v) := by fun_prop
    have c2 : Continuous fun θ : ℝ => (k (t + 1) + θ • v, k (t + 2)) := by fun_prop
    have n1 := c1.continuousAt.preimage_mem_nhds (x := 0) (isOpen_interior.mem_nhds (by
      simpa using hint t))
    have n2 := c2.continuousAt.preimage_mem_nhds (x := 0) (isOpen_interior.mem_nhds (by
      simpa using hint (t + 1)))
    filter_upwards [n1, n2] with θ h1 h2
    set k' : ℕ → K := Function.update k (t + 1) (k (t + 1) + θ • v) with hk'
    have hadm' : Admissible A k₀ k' := by
      refine ⟨by simp [hk', hadm.1], fun s => ?_⟩
      by_cases hs : s = t
      · subst hs; simpa [hk'] using interior_subset h1
      by_cases hs' : s = t + 1
      · subst hs'; simpa [hk', show t + 1 + 1 = t + 2 by omega] using interior_subset h2
      have : s + 1 ≠ t + 1 := fun h => hs (by omega)
      rw [hk', Function.update_of_ne hs', Function.update_of_ne this]
      exact hadm.2 s
    have hoff : ∀ s ∉ ({t, t + 1} : Finset ℕ), δ ^ s * u (k' s, k' (s + 1))
        = δ ^ s * u (k s, k (s + 1)) := by
      intro s hs
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hs
      have h1' : s ≠ t + 1 := hs.2
      have h2' : s + 1 ≠ t + 1 := fun h => hs.1 (by omega)
      rw [hk', Function.update_of_ne h1', Function.update_of_ne h2']
    have hdiff := tsum_sub_eq_of_eq_off _ hoff hsum0
    rw [Finset.sum_pair (by omega)] at hdiff
    have hfin : {s | k' s ≠ k s}.Finite := (Set.finite_singleton (t + 1)).subset fun s hs => by
      by_contra h
      exact hs (by simp [hk', show s ≠ t + 1 from h])
    have hle := hshort k' hadm' hfin
    unfold reducedObjective at hle
    simp only [hk', Function.update_self, Function.update_of_ne (show t ≠ t + 1 by omega),
      Function.update_of_ne (show t + 1 + 1 ≠ t + 1 by omega)] at hdiff
    simp only [hφ, zero_smul, add_zero, show t + 1 + 1 = t + 2 by omega] at hdiff ⊢
    linarith
  have h0 := hloc.hasDerivAt_eq_zero hd
  have hδt : 0 < δ ^ t := pow_pos hδ t
  have : δ ^ t * (Du t (0, v) + δ * Du (t + 1) (v, 0)) = 0 := by rw [pow_succ] at h0; linarith
  exact (mul_eq_zero.1 this).resolve_left hδt.ne'

/-- **Necessity of the Euler equations** (MWG, p. 750): an optimal path through the interior of
`A` (with `δ > 0` and `u` differentiable along it) satisfies (20.D.9). -/
theorem euler_of_optimal {A : Set (K × K)} {δ : ℝ} (hδ : 0 < δ) {u : K × K → ℝ} {k₀ : K}
    {k : ℕ → K} (hopt : OptimalFrom A δ u k₀ k) (hint : ∀ t, (k t, k (t + 1)) ∈ interior A)
    {Du : ℕ → K × K →L[ℝ] ℝ} (hDu : ∀ t, HasFDerivAt u (Du t) (k t, k (t + 1))) :
    EulerEq δ Du := by
  refine euler_of_shortRun hδ hopt.1 hopt.2.1 (fun k' hk' hfin => ?_) hint hDu
  obtain ⟨M, hM⟩ := hfin.bddAbove
  have hoff : ∀ s ∉ Finset.range (M + 1), δ ^ s * u (k' s, k' (s + 1))
      = δ ^ s * u (k s, k (s + 1)) := by
    intro s hs
    rw [Finset.mem_range, not_lt] at hs
    have e1 : k' s = k s := by by_contra h; have := hM h; omega
    have e2 : k' (s + 1) = k (s + 1) := by by_contra h; have := hM h; omega
    rw [e1, e2]
  exact hopt.2.2 k' hk' (summable_of_eq_off _ hoff hopt.2.1)

/-- The **telescoping identity** behind the sufficiency of the Euler equations:
`∑_{t ≤ T} δ^t Du_t(d_t, d_{t+1}) = Du_0(d_0, 0) + ∑_{t < T} δ^{t+1} (Euler expression at
t + 1, applied to d_{t+1}) + δ^T Du_T(0, d_{T+1})`. -/
theorem euler_telescope (δ : ℝ) (Du : ℕ → K × K →L[ℝ] ℝ) (d : ℕ → K) (T : ℕ) :
    ∑ t ∈ Finset.range (T + 1), δ ^ t * Du t (d t, d (t + 1))
      = Du 0 (d 0, 0) + ∑ t ∈ Finset.range T,
          δ ^ t * (Du t (0, d (t + 1)) + δ * Du (t + 1) (d (t + 1), 0))
        + δ ^ T * Du T (0, d (T + 1)) := by
  have hsplit : ∀ t (a b : K), Du t (a, b) = Du t (a, 0) + Du t (0, b) := by
    intro t a b
    rw [← map_add, Prod.mk_add_mk, add_zero, zero_add]
  induction T with
  | zero => simp [hsplit 0 (d 0) (d 1)]
  | succ T ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ, hsplit (T + 1) (d (T + 1))]
    ring

/-- **Exercise 20.D.6** (MWG, p. 784): for `u` concave on a convex `A`, an interior admissible
path along which `u` is differentiable, and `δ > 0`, the Euler equations hold if and only if no
admissible path that differs from `k` at finitely many dates does better (short-run
optimality). -/
theorem exercise_20_D_6 {A : Set (K × K)} {δ : ℝ} (hδ : 0 < δ) {u : K × K → ℝ}
    (hconc : ConcaveOn ℝ A u) {k₀ : K} {k : ℕ → K} (hadm : Admissible A k₀ k)
    (hsum : Summable fun t => δ ^ t * u (k t, k (t + 1)))
    (hint : ∀ t, (k t, k (t + 1)) ∈ interior A) {Du : ℕ → K × K →L[ℝ] ℝ}
    (hDu : ∀ t, HasFDerivAt u (Du t) (k t, k (t + 1))) :
    EulerEq δ Du ↔ ∀ k', Admissible A k₀ k' → {t | k' t ≠ k t}.Finite →
      reducedObjective δ u k' ≤ reducedObjective δ u k := by
  constructor
  · intro heul k' hk' hfin
    obtain ⟨M, hM⟩ : ∃ M, ∀ t, M ≤ t → k' t = k t := by
      obtain ⟨M, hM⟩ := hfin.bddAbove
      exact ⟨M + 1, fun t ht => by by_contra h; have := hM h; omega⟩
    have hoff : ∀ s ∉ Finset.range (M + 1), δ ^ s * u (k' s, k' (s + 1))
        = δ ^ s * u (k s, k (s + 1)) := by
      intro s hs
      rw [Finset.mem_range, not_lt] at hs
      rw [hM s (by omega), hM (s + 1) (by omega)]
    have hdiff := tsum_sub_eq_of_eq_off _ hoff hsum
    -- termwise gradient inequality, then the telescoping identity
    set d : ℕ → K := fun t => k' t - k t
    have hterm : ∀ t, δ ^ t * u (k' t, k' (t + 1)) - δ ^ t * u (k t, k (t + 1))
        ≤ δ ^ t * Du t (d t, d (t + 1)) := by
      intro t
      have g := concave_le_fderiv_normed hconc (hadm.2 t) (hk'.2 t) (hDu t)
      have : (k' t, k' (t + 1)) - (k t, k (t + 1)) = (d t, d (t + 1)) := rfl
      rw [this] at g
      have hp := pow_nonneg hδ.le t
      nlinarith [mul_le_mul_of_nonneg_left g hp]
    have htel := euler_telescope δ Du d M
    have hd0 : d 0 = 0 := by simp [d, hk'.1, hadm.1]
    have hdM : d (M + 1) = 0 := by simp [d, hM (M + 1) (by omega)]
    have hmid : ∑ t ∈ Finset.range M,
        δ ^ t * (Du t (0, d (t + 1)) + δ * Du (t + 1) (d (t + 1), 0)) = 0 :=
      Finset.sum_eq_zero fun t _ => by rw [heul t (d (t + 1)), mul_zero]
    rw [hd0, hdM, hmid] at htel
    simp only [Prod.mk_zero_zero, map_zero, mul_zero, add_zero] at htel
    unfold reducedObjective
    have := Finset.sum_le_sum fun t (_ : t ∈ Finset.range (M + 1)) => hterm t
    rw [Finset.sum_sub_distrib] at hdiff
    rw [Finset.sum_sub_distrib, htel] at this
    linarith
  · intro h
    exact euler_of_shortRun hδ hadm hsum h hint hDu

/-- A concave function bounded by `C` on the closed ball of radius `r` around `x`, and
differentiable at `x`, has derivative bounded by `2C / r` in operator norm. -/
theorem abs_fderiv_le_of_concave {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set E} {f : E → ℝ} (hf : ConcaveOn ℝ S f) {x : E} {r C : ℝ} (hr : 0 < r)
    (hball : Metric.closedBall x r ⊆ S) (hC : ∀ z ∈ Metric.closedBall x r, |f z| ≤ C)
    {f' : E →L[ℝ] ℝ} (hd : HasFDerivAt f f' x) (v : E) : |f' v| ≤ 2 * C / r * ‖v‖ := by
  have hx : x ∈ S := hball (Metric.mem_closedBall_self hr.le)
  -- first on the sphere of radius `r`
  have hw : ∀ w : E, ‖w‖ ≤ r → |f' w| ≤ 2 * C := by
    intro w hw
    have h1 : x + w ∈ Metric.closedBall x r := by
      rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left]; exact hw
    have h2 : x - w ∈ Metric.closedBall x r := by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg]; exact hw
    have g1 := concave_le_fderiv_normed hf hx (hball h1) hd
    have g2 := concave_le_fderiv_normed hf hx (hball h2) hd
    rw [add_sub_cancel_left] at g1
    rw [sub_sub_cancel_left, map_neg] at g2
    have c0 := hC x (Metric.mem_closedBall_self hr.le)
    have c1 := hC _ h1
    have c2 := hC _ h2
    rw [abs_le] at c0 c1 c2 ⊢
    constructor <;> linarith
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  · have hvn : 0 < ‖v‖ := norm_pos_iff.2 hv
    have := hw ((r / ‖v‖) • v) (by rw [norm_smul, Real.norm_eq_abs,
      abs_of_pos (div_pos hr hvn), div_mul_cancel₀ _ hvn.ne'])
    rw [map_smul, smul_eq_mul, abs_mul, abs_of_pos (div_pos hr hvn)] at this
    rw [div_mul_eq_mul_div, le_div_iff₀ hr]
    calc |f' v| * r = r / ‖v‖ * |f' v| * ‖v‖ := by field_simp
      _ ≤ 2 * C * ‖v‖ := mul_le_mul_of_nonneg_right this hvn.le

/-- **Proposition 20.D.7** (MWG, p. 751): a bounded, strictly interior admissible path satisfying
the Euler equations solves (20.D.8) among bounded admissible paths (all paths are bounded in MWG,
p. 744). Here `K` is finite-dimensional, `u` is concave on the convex region `A`, `0 < δ < 1`,
and strict interiority means `ball((k_t, k_{t+1}), ε) ⊆ A` for a fixed `ε > 0`. The proof uses
the gradient inequality and the telescoping identity: the gain of any competitor over the first
`T + 1` dates is at most `δ^T Du_T(0, k'_{T+1} - k_{T+1})`, which tends to `0` because strict
interiority bounds the derivatives (concave functions are continuous, hence bounded, on compact
subsets of the interior). -/
theorem proposition_20_D_7 [FiniteDimensional ℝ K] {A : Set (K × K)} {δ : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ < 1) {u : K × K → ℝ} (hconc : ConcaveOn ℝ A u) {k₀ : K} {k : ℕ → K}
    (hadm : Admissible A k₀ k) (hsum : Summable fun t => δ ^ t * u (k t, k (t + 1)))
    {R : ℝ} (hbdd : ∀ t, ‖k t‖ ≤ R) {ε : ℝ} (hε : 0 < ε)
    (hball : ∀ t, Metric.ball (k t, k (t + 1)) ε ⊆ A) {Du : ℕ → K × K →L[ℝ] ℝ}
    (hDu : ∀ t, HasFDerivAt u (Du t) (k t, k (t + 1))) (heul : EulerEq δ Du)
    (k' : ℕ → K) (hk' : Admissible A k₀ k') {R' : ℝ} (hbdd' : ∀ t, ‖k' t‖ ≤ R')
    (hsum' : Summable fun t => δ ^ t * u (k' t, k' (t + 1))) :
    reducedObjective δ u k' ≤ reducedObjective δ u k := by
  set x : ℕ → K × K := fun t => (k t, k (t + 1)) with hx
  set U := ⋃ t, Metric.closedBall (x t) (ε / 2) with hU
  set S := closure U with hS
  have hR0 : 0 ≤ R := (norm_nonneg _).trans (hbdd 0)
  have hxR : ∀ t, ‖x t‖ ≤ R := fun t => by
    rw [hx, Prod.norm_def]; exact max_le (hbdd t) (hbdd (t + 1))
  have hSsub : S ⊆ interior A := by
    intro z hz
    obtain ⟨w, hw, hzw⟩ := Metric.mem_closure_iff.1 hz (ε / 2) (by linarith)
    obtain ⟨t, ht⟩ := Set.mem_iUnion.1 hw
    have hzt : z ∈ Metric.ball (x t) ε := by
      rw [Metric.mem_ball]
      have := dist_triangle z w (x t)
      rw [Metric.mem_closedBall] at ht
      linarith
    exact (Metric.isOpen_ball.subset_interior_iff.2 (hball t)) hzt
  have hScpt : IsCompact S := by
    refine Metric.isCompact_of_isClosed_isBounded isClosed_closure ?_
    refine (Metric.isBounded_closedBall (x := (0 : K × K)) (r := R + ε / 2)).subset ?_
    refine closure_minimal (fun z hz => ?_) Metric.isClosed_closedBall
    obtain ⟨t, ht⟩ := Set.mem_iUnion.1 hz
    rw [Metric.mem_closedBall, dist_eq_norm] at ht
    rw [Metric.mem_closedBall, dist_zero_right]
    have := norm_le_insert' z (x t)
    linarith [hxR t]
  obtain ⟨C, hC⟩ := hScpt.exists_bound_of_continuousOn
    (hconc.continuousOn_interior.mono hSsub)
  have hballS : ∀ t, Metric.closedBall (x t) (ε / 2) ⊆ S := fun t =>
    (Set.subset_iUnion (fun t => Metric.closedBall (x t) (ε / 2)) t).trans subset_closure
  have hDbound : ∀ t v, |Du t v| ≤ 2 * C / (ε / 2) * ‖v‖ := fun t v =>
    abs_fderiv_le_of_concave hconc (by linarith) ((hballS t).trans (hSsub.trans interior_subset))
      (fun z hz => by simpa [Real.norm_eq_abs] using hC z (hballS t hz)) (hDu t) v
  -- the gain over the first `T + 1` dates
  set d : ℕ → K := fun t => k' t - k t with hd
  have hdb : ∀ t, ‖d t‖ ≤ R' + R := fun t => by
    simp only [hd]; exact (norm_sub_le _ _).trans (add_le_add (hbdd' t) (hbdd t))
  have hgain : ∀ T, ∑ t ∈ Finset.range (T + 1),
      (δ ^ t * u (k' t, k' (t + 1)) - δ ^ t * u (k t, k (t + 1)))
        ≤ δ ^ T * (2 * C / (ε / 2) * (R' + R)) := by
    intro T
    have hterm : ∀ t, δ ^ t * u (k' t, k' (t + 1)) - δ ^ t * u (k t, k (t + 1))
        ≤ δ ^ t * Du t (d t, d (t + 1)) := by
      intro t
      have g := concave_le_fderiv_normed hconc (hadm.2 t) (hk'.2 t) (hDu t)
      have : (k' t, k' (t + 1)) - (k t, k (t + 1)) = (d t, d (t + 1)) := rfl
      rw [this] at g
      have hp := pow_nonneg hδ0.le t
      nlinarith [mul_le_mul_of_nonneg_left g hp]
    have htel := euler_telescope δ Du d T
    have hd0 : d 0 = 0 := by simp [hd, hk'.1, hadm.1]
    have hmid : ∑ t ∈ Finset.range T,
        δ ^ t * (Du t (0, d (t + 1)) + δ * Du (t + 1) (d (t + 1), 0)) = 0 :=
      Finset.sum_eq_zero fun t _ => by rw [heul t (d (t + 1)), mul_zero]
    rw [hd0, hmid] at htel
    simp only [Prod.mk_zero_zero, map_zero, zero_add] at htel
    have hlast : δ ^ T * Du T (0, d (T + 1)) ≤ δ ^ T * (2 * C / (ε / 2) * (R' + R)) := by
      refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hδ0.le T)
      refine (le_abs_self _).trans ((hDbound T _).trans ?_)
      have hC0 : 0 ≤ 2 * C / (ε / 2) := by
        have := hC _ (hballS 0 (Metric.mem_closedBall_self (by linarith)))
        exact div_nonneg (by linarith [norm_nonneg (u (x 0))]) (by linarith)
      refine mul_le_mul_of_nonneg_left ?_ hC0
      rw [Prod.norm_def, norm_zero]
      exact max_le (by linarith [hdb 0, norm_nonneg (d 0)]) (hdb (T + 1))
    calc ∑ t ∈ Finset.range (T + 1), (δ ^ t * u (k' t, k' (t + 1)) - δ ^ t * u (k t, k (t + 1)))
        ≤ ∑ t ∈ Finset.range (T + 1), δ ^ t * Du t (d t, d (t + 1)) :=
          Finset.sum_le_sum fun t _ => hterm t
      _ = δ ^ T * Du T (0, d (T + 1)) := htel
      _ ≤ _ := hlast
  have hlim1 : Tendsto (fun T => ∑ t ∈ Finset.range (T + 1),
      (δ ^ t * u (k' t, k' (t + 1)) - δ ^ t * u (k t, k (t + 1)))) atTop
      (𝓝 (reducedObjective δ u k' - reducedObjective δ u k)) := by
    have := ((hsum'.sub hsum).hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
    rw [hsum'.tsum_sub hsum] at this
    exact this
  have hlim2 : Tendsto (fun T : ℕ => δ ^ T * (2 * C / (ε / 2) * (R' + R))) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hδ0.le hδ1).mul_const
      (2 * C / (ε / 2) * (R' + R))
  have := le_of_tendsto_of_tendsto hlim1 hlim2 (Eventually.of_forall hgain)
  linarith

/-! ### The policy function and the value function -/

omit [NormedAddCommGroup K] [NormedSpace ℝ K] in
/-- The objective splits off its first term: `W(k) = u(k₀, k₁) + δ W(k¹)`. -/
theorem reducedObjective_succ {δ : ℝ} {u : K × K → ℝ} {k : ℕ → K}
    (hs : Summable fun t => δ ^ t * u (k t, k (t + 1))) :
    reducedObjective δ u k = u (k 0, k 1) + δ * reducedObjective δ u (fun t => k (t + 1)) := by
  unfold reducedObjective
  rw [hs.tsum_eq_zero_add, ← tsum_mul_left]
  simp only [pow_zero, one_mul, zero_add]
  congr 1
  exact tsum_congr fun t => by ring

/-- Prepending an initial capital stock to a path. -/
def consPath (a : K) (k : ℕ → K) : ℕ → K
  | 0 => a
  | t + 1 => k t

omit [NormedAddCommGroup K] [NormedSpace ℝ K] in
@[simp] theorem consPath_zero (a : K) (k : ℕ → K) : consPath a k 0 = a := rfl

omit [NormedAddCommGroup K] [NormedSpace ℝ K] in
@[simp] theorem consPath_succ (a : K) (k : ℕ → K) (t : ℕ) : consPath a k (t + 1) = k t := rfl

omit [NormedAddCommGroup K] [NormedSpace ℝ K] in
/-- The objective of a prepended path: `W(a, k) = u(a, k₀) + δ W(k)`. -/
theorem reducedObjective_consPath {δ : ℝ} {u : K × K → ℝ} (a : K) {k : ℕ → K}
    (hs : Summable fun t => δ ^ t * u (k t, k (t + 1))) :
    Summable (fun t => δ ^ t * u (consPath a k t, consPath a k (t + 1))) ∧
      reducedObjective δ u (consPath a k) = u (a, k 0) + δ * reducedObjective δ u k := by
  have hs' : Summable (fun t => δ ^ t * u (consPath a k t, consPath a k (t + 1))) := by
    refine (summable_nat_add_iff 1).1 ?_
    refine (hs.mul_left δ).congr fun t => ?_
    simp only [consPath_succ]; ring
  refine ⟨hs', ?_⟩
  rw [reducedObjective_succ hs']
  rfl

omit [NormedAddCommGroup K] [NormedSpace ℝ K] in
/-- **The principle of optimality** behind (20.D.10) (MWG, p. 752): if `k` solves (20.D.8) from
`k̄₀` and `δ > 0`, the tail `(k₁, k₂, ...)` solves it from `k₁`. -/
theorem optimal_tail {A : Set (K × K)} {δ : ℝ} (hδ : 0 < δ) {u : K × K → ℝ} {k₀ : K}
    {k : ℕ → K} (hopt : OptimalFrom A δ u k₀ k) :
    OptimalFrom A δ u (k 1) (fun t => k (t + 1)) := by
  obtain ⟨hadm, hs, hmax⟩ := hopt
  have hstail : Summable fun t => δ ^ t * u (k (t + 1), k (t + 1 + 1)) :=
    (((summable_nat_add_iff 1).2 hs).mul_left δ⁻¹).congr fun t => by
      rw [pow_succ]; field_simp
  refine ⟨⟨rfl, fun t => hadm.2 (t + 1)⟩, hstail, fun k' hk' hs' => ?_⟩
  obtain ⟨hs'', heq⟩ := reducedObjective_consPath (u := u) k₀ hs'
  have hadm'' : Admissible A k₀ (consPath k₀ k') := by
    refine ⟨rfl, fun t => ?_⟩
    cases t with
    | zero => simp only [consPath_zero, consPath_succ, hk'.1]; rw [← hadm.1]; exact hadm.2 0
    | succ t => exact hk'.2 t
  have h1 := hmax _ hadm'' hs''
  rw [heq, reducedObjective_succ hs, hk'.1, hadm.1] at h1
  have := le_of_mul_le_mul_left (by linarith : δ * reducedObjective δ u k'
    ≤ δ * reducedObjective δ u (fun t => k (t + 1))) hδ
  exact this

omit [NormedAddCommGroup K] [NormedSpace ℝ K] in
/-- **(20.D.10)** (MWG, p. 752): along an optimal path, `k_{t+1} = ψ(k_t)` for the policy
function `ψ`, the first-period choice of the optimal path from each initial condition. -/
theorem policy_20_D_10 {A : Set (K × K)} {δ : ℝ} (hδ : 0 < δ) {u : K × K → ℝ} {k₀ : K}
    {k : ℕ → K} (hopt : OptimalFrom A δ u k₀ k) {ψ : K → K}
    (hψ : ∀ a k', OptimalFrom A δ u a k' → k' 1 = ψ a) (t : ℕ) : k (t + 1) = ψ (k t) := by
  have htail : ∀ t, OptimalFrom A δ u (k t) (fun s => k (s + t)) := by
    intro t
    induction t with
    | zero => simpa [hopt.1.1] using hopt
    | succ t ih =>
      have := optimal_tail hδ ih
      simpa [add_assoc, add_comm 1 t] using this
  have := hψ _ _ (htail t)
  simpa [add_comm 1 t] using this

/-- **Uniqueness** of the solution of (20.D.8) (MWG, p. 750): if `A` is convex and `u` is strictly
concave and bounded above on `A`, and `0 < δ < 1`, two optimal paths from the same `k̄₀`
coincide. -/
theorem optimal_unique {A : Set (K × K)} (hA : Convex ℝ A) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    {u : K × K → ℝ} (hu : StrictConcaveOn ℝ A u) {M : ℝ} (hM : ∀ x ∈ A, u x ≤ M) {k₀ : K}
    {k k' : ℕ → K} (h : OptimalFrom A δ u k₀ k) (h' : OptimalFrom A δ u k₀ k') : k = k' := by
  by_contra hne
  obtain ⟨t₀, ht₀⟩ : ∃ t, k t ≠ k' t := by
    by_contra hc; push Not at hc; exact hne (funext hc)
  set m : ℕ → K := fun t => (1 / 2 : ℝ) • k t + (1 / 2 : ℝ) • k' t with hm
  have hpair : ∀ t, (m t, m (t + 1))
      = (1 / 2 : ℝ) • (k t, k (t + 1)) + (1 / 2 : ℝ) • (k' t, k' (t + 1)) := fun t => rfl
  have hadm : Admissible A k₀ m := by
    refine ⟨by simp [hm, h.1.1, h'.1.1, ← add_smul]; norm_num, fun t => ?_⟩
    rw [hpair]
    exact hA (h.1.2 t) (h'.1.2 t) (by norm_num) (by norm_num) (by norm_num)
  have hs := h.2.1
  have hs' := h'.2.1
  have hlow : ∀ t, (1 / 2 : ℝ) * (δ ^ t * u (k t, k (t + 1)))
      + (1 / 2 : ℝ) * (δ ^ t * u (k' t, k' (t + 1))) ≤ δ ^ t * u (m t, m (t + 1)) := by
    intro t
    have hc := (StrictConcaveOn.concaveOn hu).2 (h.1.2 t) (h'.1.2 t)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    rw [← hpair] at hc
    simp only [smul_eq_mul] at hc
    nlinarith [mul_le_mul_of_nonneg_left hc (pow_nonneg hδ0.le t)]
  have hms : Summable fun t => δ ^ t * u (m t, m (t + 1)) := by
    have hlowsum := (hs.mul_left (1 / 2 : ℝ)).add (hs'.mul_left (1 / 2 : ℝ))
    have hg := (summable_geometric_of_lt_one hδ0.le hδ1).mul_right M
    have hup : ∀ t, δ ^ t * u (m t, m (t + 1)) ≤ δ ^ t * M := fun t =>
      mul_le_mul_of_nonneg_left (hM _ (hadm.2 t)) (pow_nonneg hδ0.le t)
    have hdiff : Summable fun t => δ ^ t * u (m t, m (t + 1))
        - ((1 / 2 : ℝ) * (δ ^ t * u (k t, k (t + 1)))
          + (1 / 2 : ℝ) * (δ ^ t * u (k' t, k' (t + 1)))) :=
      Summable.of_nonneg_of_le (fun t => sub_nonneg.2 (hlow t))
        (fun t => by have := hup t; linarith [hlow t])
        (hg.sub hlowsum)
    exact (hdiff.add hlowsum).congr fun t => by ring
  have hle := h.2.2 m hadm hms
  have heq : reducedObjective δ u k = reducedObjective δ u k' :=
    le_antisymm (h'.2.2 k h.1 hs) (h.2.2 k' h'.1 hs')
  -- strict inequality at a date where the pairs differ
  have hpair_ne : (k t₀, k (t₀ + 1)) ≠ (k' t₀, k' (t₀ + 1)) := fun he =>
    ht₀ (congrArg Prod.fst he)
  have hlt : (1 / 2 : ℝ) * reducedObjective δ u k + (1 / 2 : ℝ) * reducedObjective δ u k'
      < reducedObjective δ u m := by
    unfold reducedObjective
    rw [← hs.tsum_mul_left, ← hs'.tsum_mul_left, ← (hs.mul_left _).tsum_add (hs'.mul_left _)]
    refine Summable.tsum_lt_tsum (i := t₀) hlow ?_ ((hs.mul_left _).add (hs'.mul_left _)) hms
    have hc := hu.2 (h.1.2 t₀) (h'.1.2 t₀) hpair_ne (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
    rw [← hpair] at hc
    simp only [smul_eq_mul] at hc
    nlinarith [mul_lt_mul_of_pos_left hc (pow_pos hδ0 t₀)]
  rw [heq] at hlt hle
  linarith

/-- `V` is the **value function** of (20.D.8) on a set `D` of initial conditions: from every
`k̄ ∈ D` an optimal path exists and `V(k̄)` is its value `W`. -/
def IsValueFn (A : Set (K × K)) (δ : ℝ) (u : K × K → ℝ) (D : Set K) (V : K → ℝ) : Prop :=
  ∀ a ∈ D, ∃ k, OptimalFrom A δ u a k ∧ reducedObjective δ u k = V a

omit [NormedAddCommGroup K] [NormedSpace ℝ K] in
/-- **(20.D.11)** (MWG, p. 753), the Bellman equation: if `V` is the value function on `D`, the
region keeps the capital stocks in `D` (`A ⊆ D × D`) and `δ > 0`, then for every `k ∈ D`,
`V(k) = max_{k' : (k, k') ∈ A} u(k, k') + δ V(k')`, attained at the first-period choice of the
optimal path. -/
theorem bellman_20_D_11 {A : Set (K × K)} {δ : ℝ} (hδ : 0 < δ) {u : K × K → ℝ} {D : Set K}
    (hAD : ∀ a b, (a, b) ∈ A → a ∈ D ∧ b ∈ D) {V : K → ℝ} (hV : IsValueFn A δ u D V)
    {a : K} (ha : a ∈ D) :
    IsGreatest {r | ∃ b, (a, b) ∈ A ∧ r = u (a, b) + δ * V b} (V a) := by
  obtain ⟨k, hk, hkV⟩ := hV a ha
  constructor
  · refine ⟨k 1, by simpa [hk.1.1] using hk.1.2 0, ?_⟩
    have htail := optimal_tail hδ hk
    obtain ⟨k', hk', hk'V⟩ := hV (k 1) (hAD _ _ (by simpa [hk.1.1] using hk.1.2 0)).2
    have hval : reducedObjective δ u (fun t => k (t + 1)) = V (k 1) := by
      rw [← hk'V]
      exact le_antisymm (hk'.2.2 _ htail.1 htail.2.1) (htail.2.2 _ hk'.1 hk'.2.1)
    rw [← hkV, reducedObjective_succ hk.2.1, hval, hk.1.1]
  · rintro r ⟨b, hab, rfl⟩
    obtain ⟨k', hk', hk'V⟩ := hV b (hAD _ _ hab).2
    obtain ⟨hs'', heq⟩ := reducedObjective_consPath (u := u) a hk'.2.1
    have hadm : Admissible A a (consPath a k') := by
      refine ⟨rfl, fun t => ?_⟩
      cases t with
      | zero => simpa [hk'.1.1] using hab
      | succ t => exact hk'.1.2 t
    have := hk.2.2 _ hadm hs''
    rw [heq, hk'.1.1, hk'V, hkV] at this
    exact this

/-- **Correction to (20.D.11)** (MWG, p. 753): for the value `V₈` of the objective (20.D.8) as
printed, `∑_{t ≥ 1} δ^t u(k_{t-1}, k_t)`, the printed equation `V₈ = max u + δ V₈` fails: with
`u ≡ 1` and `0 < δ < 1` every path has `V₈ = δ / (1 - δ)`, while `1 + δ V₈ ≠ V₈`; the normalized
value `V₈ / δ` does satisfy it. -/
theorem bellman_20_D_11_printed_false {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    let V₈ := ∑' t : ℕ, δ ^ (t + 1) * (1 : ℝ)
    V₈ = δ / (1 - δ) ∧ V₈ ≠ 1 + δ * V₈ ∧ V₈ / δ = 1 + δ * (V₈ / δ) := by
  intro V₈
  have h1δ : (1 : ℝ) - δ ≠ 0 := by linarith
  have hV : V₈ = δ / (1 - δ) := by
    simp only [V₈, mul_one, pow_succ]
    rw [tsum_mul_right, tsum_geometric_of_lt_one hδ0.le hδ1]
    field_simp
  refine ⟨hV, fun h => ?_, ?_⟩
  · rw [hV] at h
    field_simp at h
    nlinarith
  · rw [hV]
    field_simp
    ring

/-- **Exercise 20.D.8(i)** (MWG, p. 784): the value function is concave, for `A` convex, `u`
concave and bounded above on `A`, `0 ≤ δ < 1`, and `D` convex. -/
theorem exercise_20_D_8_i {A : Set (K × K)} (hA : Convex ℝ A) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1) {u : K × K → ℝ} (hu : ConcaveOn ℝ A u) {M : ℝ} (hM : ∀ x ∈ A, u x ≤ M)
    {D : Set K} (hD : Convex ℝ D) {V : K → ℝ} (hV : IsValueFn A δ u D V) :
    ConcaveOn ℝ D V := by
  refine ⟨hD, fun a ha b hb θ φ hθ hφ hθφ => ?_⟩
  obtain ⟨k, hk, hkV⟩ := hV a ha
  obtain ⟨k', hk', hk'V⟩ := hV b hb
  obtain ⟨k'', hk'', hk''V⟩ := hV _ (hD ha hb hθ hφ hθφ)
  set m : ℕ → K := fun t => θ • k t + φ • k' t with hm
  have hpair : ∀ t, (m t, m (t + 1)) = θ • (k t, k (t + 1)) + φ • (k' t, k' (t + 1)) :=
    fun t => rfl
  have hadm : Admissible A (θ • a + φ • b) m :=
    ⟨by simp [hm, hk.1.1, hk'.1.1], fun t => by
      rw [hpair]; exact hA (hk.1.2 t) (hk'.1.2 t) hθ hφ hθφ⟩
  have hs := hk.2.1
  have hs' := hk'.2.1
  have hlow : ∀ t, θ * (δ ^ t * u (k t, k (t + 1))) + φ * (δ ^ t * u (k' t, k' (t + 1)))
      ≤ δ ^ t * u (m t, m (t + 1)) := by
    intro t
    have hc := hu.2 (hk.1.2 t) (hk'.1.2 t) hθ hφ hθφ
    rw [← hpair] at hc
    simp only [smul_eq_mul] at hc
    nlinarith [mul_le_mul_of_nonneg_left hc (pow_nonneg hδ0 t)]
  have hlowsum := (hs.mul_left θ).add (hs'.mul_left φ)
  have hms : Summable fun t => δ ^ t * u (m t, m (t + 1)) := by
    have hg := (summable_geometric_of_lt_one hδ0 hδ1).mul_right M
    have hdiff : Summable fun t => δ ^ t * u (m t, m (t + 1))
        - (θ * (δ ^ t * u (k t, k (t + 1))) + φ * (δ ^ t * u (k' t, k' (t + 1)))) :=
      Summable.of_nonneg_of_le (fun t => sub_nonneg.2 (hlow t))
        (fun t => by
          have := mul_le_mul_of_nonneg_left (hM _ (hadm.2 t)) (pow_nonneg hδ0 t)
          linarith [hlow t])
        (hg.sub hlowsum)
    exact (hdiff.add hlowsum).congr fun t => by ring
  have h1 := hk''.2.2 m hadm hms
  have h2 : θ * reducedObjective δ u k + φ * reducedObjective δ u k' ≤ reducedObjective δ u m := by
    unfold reducedObjective
    rw [← hs.tsum_mul_left, ← hs'.tsum_mul_left, ← (hs.mul_left _).tsum_add (hs'.mul_left _)]
    exact Summable.tsum_le_tsum hlow hlowsum hms
  rw [hkV, hk'V] at h2
  rw [hk''V] at h1
  simp only [smul_eq_mul]
  linarith

omit [NormedSpace ℝ K] in
/-- **Exercise 20.D.8(ii)** (MWG, p. 784), (20.D.12): for every perturbation `z` with
`(k + z, ψ(k)) ∈ A`, `V(k + z) ≥ u(k + z, ψ(k)) + δ V(ψ(k))`, with equality at `z = 0`. -/
theorem exercise_20_D_8_ii {A : Set (K × K)} {δ : ℝ} (hδ : 0 < δ) {u : K × K → ℝ}
    {D : Set K} (hAD : ∀ a b, (a, b) ∈ A → a ∈ D ∧ b ∈ D) {V : K → ℝ}
    (hV : IsValueFn A δ u D V) {ψ : K → K} (hψ : ∀ a k', OptimalFrom A δ u a k' → k' 1 = ψ a)
    {a : K} (ha : a ∈ D) :
    (∀ z, (a + z, ψ a) ∈ A → u (a + z, ψ a) + δ * V (ψ a) ≤ V (a + z)) ∧
      V a = u (a, ψ a) + δ * V (ψ a) := by
  refine ⟨fun z hz => (bellman_20_D_11 hδ hAD hV (hAD _ _ hz).1).2 ⟨ψ a, hz, rfl⟩, ?_⟩
  obtain ⟨k, hk, hkV⟩ := hV a ha
  have h1 := hψ a k hk
  -- the Bellman maximum is attained at `ψ a`
  have htail := optimal_tail hδ hk
  obtain ⟨k', hk', hk'V⟩ := hV (k 1) (hAD _ _ (by simpa [hk.1.1] using hk.1.2 0)).2
  have hval : reducedObjective δ u (fun t => k (t + 1)) = V (k 1) := by
    rw [← hk'V]
    exact le_antisymm (hk'.2.2 _ htail.1 htail.2.1) (htail.2.2 _ hk'.1 hk'.2.1)
  rw [← hkV, reducedObjective_succ hk.2.1, hval, h1, hk.1.1]

/-- A **second-order condition at a local minimum**: if `g` has a local minimum at `a`, is
differentiable near `a` with derivative `g'`, and `g'` has derivative `D` at `a`, then `D ≥ 0`. -/
theorem second_deriv_nonneg_of_isLocalMin {g g' : ℝ → ℝ} {a D : ℝ} (hmin : IsLocalMin g a)
    (hd : ∀ᶠ x in 𝓝 a, HasDerivAt g (g' x) x) (hd2 : HasDerivAt g' D a) : 0 ≤ D := by
  by_contra hneg
  push Not at hneg
  have hg'a : g' a = 0 := hmin.hasDerivAt_eq_zero hd.self_of_nhds
  -- `g' < 0` just to the right of `a`
  have hs := (hasDerivAt_iff_tendsto_slope.1 hd2).mono_left (nhdsGT_le_nhdsNE a)
  have hneg' : ∀ᶠ x in 𝓝[>] a, g' x < 0 := by
    filter_upwards [hs.eventually (gt_mem_nhds hneg), self_mem_nhdsWithin] with x hx hxa
    rw [slope_def_field, hg'a, sub_zero] at hx
    have hxa' : 0 < x - a := sub_pos.2 hxa
    exact (div_neg_iff.1 hx).elim (fun h => absurd h.2 (not_lt.2 hxa'.le)) (fun h => h.1)
  have h1 : ∀ᶠ x in 𝓝[>] a, HasDerivAt g (g' x) x := nhdsWithin_le_nhds hd
  have h2 : ∀ᶠ x in 𝓝[>] a, g a ≤ g x := nhdsWithin_le_nhds hmin
  have hall : ∀ᶠ x in 𝓝[>] a, g' x < 0 ∧ HasDerivAt g (g' x) x ∧ g a ≤ g x :=
    hneg'.and (h1.and h2)
  obtain ⟨b, hb, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hall
  have hab : a < b := hb
  set x := (a + b) / 2
  have hax : a < x := by simp only [x]; linarith
  have hxb : x < b := by simp only [x]; linarith
  have hcont : ContinuousOn g (Set.Icc a x) := by
    intro y hy
    rcases eq_or_lt_of_le hy.1 with rfl | hy1
    · exact hd.self_of_nhds.continuousAt.continuousWithinAt
    · exact (hsub ⟨hy1, hy.2.trans_lt hxb⟩).2.1.continuousAt.continuousWithinAt
  obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope g g' hax hcont
    (fun y hy => (hsub ⟨hy.1, hy.2.trans hxb⟩).2.1)
  have hξneg := (hsub ⟨hξ.1, hξ.2.trans hxb⟩).1
  have hgx := (hsub ⟨hax, hxb⟩).2.2
  rw [hξeq] at hξneg
  have : g x - g a < 0 := by
    have := (div_neg_iff.1 hξneg).elim (fun h => absurd h.2 (not_lt.2 (sub_pos.2 hax).le))
      (fun h => h.1)
    exact this
  linarith

/-- **Exercise 20.D.9**, first consequence (MWG, p. 784): with one capital good, if `(k, ψ(k))` is
interior to `A`, `V` is differentiable at `k` and `u(·, ψ(k))` is differentiable at `k`, then
`V'(k) = ∇₁u(k, ψ(k))`. -/
theorem exercise_20_D_9_first {A : Set (ℝ × ℝ)} {δ : ℝ} (hδ : 0 < δ) {u : ℝ × ℝ → ℝ}
    {D : Set ℝ} (hAD : ∀ a b, (a, b) ∈ A → a ∈ D ∧ b ∈ D) {V : ℝ → ℝ}
    (hV : IsValueFn A δ u D V) {ψ : ℝ → ℝ} (hψ : ∀ a k', OptimalFrom A δ u a k' → k' 1 = ψ a)
    {a : ℝ} (ha : a ∈ D) (hint : (a, ψ a) ∈ interior A) {V1 u1 : ℝ}
    (hV1 : HasDerivAt V V1 a) (hu1 : HasDerivAt (fun x => u (x, ψ a)) u1 a) : V1 = u1 := by
  obtain ⟨hge, heq⟩ := exercise_20_D_8_ii hδ hAD hV hψ ha
  have hmin : IsLocalMin (fun x => V x - u (x, ψ a) - δ * V (ψ a)) a := by
    have hc : Continuous fun x : ℝ => (x, ψ a) := by fun_prop
    filter_upwards [hc.continuousAt.preimage_mem_nhds (isOpen_interior.mem_nhds hint)] with x hx
    have := hge (x - a) (by simpa using interior_subset hx)
    simp only [add_sub_cancel] at this
    linarith
  have := hmin.hasDerivAt_eq_zero ((hV1.sub hu1).sub_const _)
  linarith

/-- **Exercise 20.D.9**, second consequence (MWG, p. 784): with one capital good, `(k, ψ(k))`
interior to `A`, and `V`, `u(·, ψ(k))` twice differentiable at `k`, `V''(k) ≥ ∇²₁₁u(k, ψ(k))`. -/
theorem exercise_20_D_9_second {A : Set (ℝ × ℝ)} {δ : ℝ} (hδ : 0 < δ) {u : ℝ × ℝ → ℝ}
    {D : Set ℝ} (hAD : ∀ a b, (a, b) ∈ A → a ∈ D ∧ b ∈ D) {V : ℝ → ℝ}
    (hV : IsValueFn A δ u D V) {ψ : ℝ → ℝ} (hψ : ∀ a k', OptimalFrom A δ u a k' → k' 1 = ψ a)
    {a : ℝ} (ha : a ∈ D) (hint : (a, ψ a) ∈ interior A) {V' u' : ℝ → ℝ} {V2 u11 : ℝ}
    (hV' : ∀ᶠ x in 𝓝 a, HasDerivAt V (V' x) x)
    (hu' : ∀ᶠ x in 𝓝 a, HasDerivAt (fun y => u (y, ψ a)) (u' x) x)
    (hV2 : HasDerivAt V' V2 a) (hu2 : HasDerivAt u' u11 a) : u11 ≤ V2 := by
  obtain ⟨hge, heq⟩ := exercise_20_D_8_ii hδ hAD hV hψ ha
  have hmin : IsLocalMin (fun x => V x - u (x, ψ a) - δ * V (ψ a)) a := by
    have hc : Continuous fun x : ℝ => (x, ψ a) := by fun_prop
    filter_upwards [hc.continuousAt.preimage_mem_nhds (isOpen_interior.mem_nhds hint)] with x hx
    have := hge (x - a) (by simpa using interior_subset hx)
    simp only [add_sub_cancel] at this
    linarith
  have := second_deriv_nonneg_of_isLocalMin (g' := fun x => V' x - u' x) hmin
    (by filter_upwards [hV', hu'] with x h1 h2; exact (h1.sub h2).sub_const _) (hV2.sub hu2)
  linarith

end MWG.EquilibriumTime

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Examples of Euler equations (MWG Examples 20.D.2-20.D.4, Exercises 20.D.5 and 20.D.7)

MWG, Chapter 20, pp. 750-753, Exercises 20.D.5 and 20.D.7 (p. 784), footnote 17. One capital
good: `K = ℝ`.

* **Example 20.D.2** (Ramsey-Solow, `u(k, k') = û(F(k) - k')`): the derivative of `u`
  (`example_20_D_2_deriv`) and the Euler equations `û'(c_t) / (δ û'(c_{t+1})) = F'(k_t)`
  (`example_20_D_2`, `example_20_D_2_ratio`).
* **Example 20.D.3** (cost of adjustment): the Euler equations (`example_20_D_3`) and, iterating,
  `1 + γ'(k₁ - k₀) = ∑_{t ≥ 1} δ^t (F'(k_t) - 1)` (`example_20_D_3_iterated`).
* **Exercise 20.D.5**: `F(k) = k^α`, `γ(x) = (max x 0)^β`; the derivatives
  (`exercise_20_D_5_gamma_deriv_*`, `exercise_20_D_5_F_deriv`) and the steady state
  `k* = (αδ)^{1/(1-α)}` (`exercise_20_D_5_steady_state`).
* **Example 20.D.4** and **Exercise 20.D.7** (`u = ln(2k - k')`, `δ = 1/2`): the Euler equations
  are `k_{t+1} = 3k_t - 2k_{t-1}` (`exercise_20_D_7_euler`), solved by
  `k_t = k₀ + (k₁ - k₀)(2^t - 1)` (`exercise_20_D_7_solution`, `exercise_20_D_7_unique`); the
  claims about `k₁ < k₀`, `k₁ > k₀`, constant consumption and non-optimality
  (`example_20_D_4_*`), optimality of `k₁ = k₀` by Proposition 20.D.7
  (`example_20_D_4_optimal`), and footnote 17 (`footnote_20_17`).

Correction: for `k₁ ≥ 2k₀` the path of Example 20.D.4 is not feasible (consumption
`2k₀ - k₁ ≤ 0`), so "if `k₁ ≥ k₀` the path is feasible" holds only for `k₀ ≤ k₁ < 2k₀`
(`example_20_D_4_infeasible`).
-/

open Filter Topology

namespace MWG.EquilibriumTime

/-! ### Example 20.D.2 -/

/-- **Example 20.D.2** (MWG, p. 750): `u(k, k') = û(F(k) - k')` has derivative
`(v, w) ↦ û'(F(k) - k') (F'(k) v - w)`. -/
theorem example_20_D_2_deriv {uh F : ℝ → ℝ} {a b uh' F' : ℝ}
    (huh : HasDerivAt uh uh' (F a - b)) (hF : HasDerivAt F F' a) :
    ∃ D : ℝ × ℝ →L[ℝ] ℝ, HasFDerivAt (fun p : ℝ × ℝ => uh (F p.1 - p.2)) D (a, b) ∧
      ∀ v w, D (v, w) = uh' * (F' * v - w) := by
  have h1 : HasFDerivAt (fun p : ℝ × ℝ => F p.1 - p.2)
      ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) F').comp (ContinuousLinearMap.fst ℝ ℝ ℝ)
        - ContinuousLinearMap.snd ℝ ℝ ℝ) (a, b) :=
    (hF.hasFDerivAt.comp (a, b) hasFDerivAt_fst).sub hasFDerivAt_snd
  refine ⟨_, huh.hasFDerivAt.comp (a, b) h1, fun v w => ?_⟩
  simp
  ring

/-- **Example 20.D.2** (MWG, p. 750): with `Du_t(v, w) = û'(c_{t+1}) (F'(k_t) v - w)`, where
`c_{t+1} = F(k_t) - k_{t+1}`, the Euler equations are `û'(c_{t+1}) = δ û'(c_{t+2}) F'(k_{t+1})`. -/
theorem example_20_D_2 {δ : ℝ} {uh' F' : ℝ → ℝ} {k : ℕ → ℝ} {F : ℝ → ℝ}
    {Du : ℕ → ℝ × ℝ →L[ℝ] ℝ}
    (hDu : ∀ t v w, Du t (v, w) = uh' (F (k t) - k (t + 1)) * (F' (k t) * v - w)) :
    EulerEq δ Du ↔ ∀ t, uh' (F (k t) - k (t + 1))
      = δ * uh' (F (k (t + 1)) - k (t + 2)) * F' (k (t + 1)) := by
  constructor
  · intro h t
    have := h t 1
    rw [hDu, hDu] at this
    linarith
  · intro h t v
    rw [hDu, hDu, h t]
    ring

/-- **Example 20.D.2** (MWG, p. 750), ratio form: `û'(c_t) / (δ û'(c_{t+1})) = F'(k_t)` (marginal
utilities of consuming or investing are equal), when `δ û'(c_{t+1}) ≠ 0`. -/
theorem example_20_D_2_ratio {δ uc uc' F' : ℝ} (h : δ * uc' ≠ 0) :
    uc = δ * uc' * F' ↔ uc / (δ * uc') = F' := by
  rw [div_eq_iff h]; constructor <;> intro e <;> linarith

/-! ### Example 20.D.3 -/

/-- **Example 20.D.3** (MWG, p. 750): `u(k, k') = F(k) - k' - γ(k' - k)` has derivative
`(v, w) ↦ F'(k) v - w - γ'(k' - k)(w - v)`. -/
theorem example_20_D_3_deriv {F γ : ℝ → ℝ} {a b F' γ' : ℝ} (hF : HasDerivAt F F' a)
    (hγ : HasDerivAt γ γ' (b - a)) :
    ∃ D : ℝ × ℝ →L[ℝ] ℝ, HasFDerivAt (fun p : ℝ × ℝ => F p.1 - p.2 - γ (p.2 - p.1)) D (a, b) ∧
      ∀ v w, D (v, w) = F' * v - w - γ' * (w - v) := by
  have h1 := hF.hasFDerivAt.comp (a, b) (hasFDerivAt_fst (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := (a, b)))
  have h2 : HasFDerivAt (fun p : ℝ × ℝ => p.2 - p.1)
      (ContinuousLinearMap.snd ℝ ℝ ℝ - ContinuousLinearMap.fst ℝ ℝ ℝ) (a, b) :=
    hasFDerivAt_snd.sub hasFDerivAt_fst
  have h3 := hγ.hasFDerivAt.comp (a, b) h2
  refine ⟨_, (h1.sub hasFDerivAt_snd).sub h3, fun v w => ?_⟩
  simp
  ring

/-- **Example 20.D.3** (MWG, p. 751): the Euler equations of the cost-of-adjustment problem,
`-1 - γ'(k_t - k_{t-1}) + δ [F'(k_t) + γ'(k_{t+1} - k_t)] = 0`. -/
theorem example_20_D_3 {δ : ℝ} {F' γ' : ℝ → ℝ} {k : ℕ → ℝ} {Du : ℕ → ℝ × ℝ →L[ℝ] ℝ}
    (hDu : ∀ t v w, Du t (v, w) = F' (k t) * v - w - γ' (k (t + 1) - k t) * (w - v)) :
    EulerEq δ Du ↔ ∀ t, -1 - γ' (k (t + 1) - k t)
      + δ * (F' (k (t + 1)) + γ' (k (t + 2) - k (t + 1))) = 0 := by
  constructor
  · intro h t
    have := h t 1
    rw [hDu, hDu] at this
    linarith
  · intro h t v
    rw [hDu, hDu]
    have := h t
    linear_combination v * this

/-- Iterating a first-order recursion `x_t = δ (f_t + x_{t+1})` with bounded `x` and `0 ≤ δ < 1`
gives `x_0 = ∑_{t ≥ 0} δ^{t+1} f_t`. -/
theorem hasSum_of_recursion {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) {x f : ℕ → ℝ} {B : ℝ}
    (hx : ∀ t, |x t| ≤ B) (hrec : ∀ t, x t = δ * (f t + x (t + 1))) :
    HasSum (fun t => δ ^ (t + 1) * f t) (x 0) := by
  have hpart : ∀ T, x 0 = ∑ t ∈ Finset.range T, δ ^ (t + 1) * f t + δ ^ T * x T := by
    intro T
    induction T with
    | zero => simp
    | succ T ih => rw [ih, Finset.sum_range_succ, hrec T]; ring
  have htail : Tendsto (fun T => δ ^ T * x T) atTop (𝓝 0) := by
    have hg := (tendsto_pow_atTop_nhds_zero_of_lt_one hδ0 hδ1).mul_const B
    rw [zero_mul] at hg
    refine squeeze_zero_norm (fun T => ?_) hg
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hδ0 T)]
    exact mul_le_mul_of_nonneg_left (hx T) (pow_nonneg hδ0 T)
  have hsum : Tendsto (fun T => ∑ t ∈ Finset.range T, δ ^ (t + 1) * f t) atTop (𝓝 (x 0)) := by
    have : Tendsto (fun T => x 0 - δ ^ T * x T) atTop (𝓝 (x 0 - 0)) :=
      tendsto_const_nhds.sub htail
    rw [sub_zero] at this
    exact this.congr fun T => by rw [hpart T]; ring
  -- absolute summability from the bounded recursion
  have habs : Summable fun t => δ ^ (t + 1) * f t := by
    have hf : ∀ t, |δ * f t| ≤ |x t| + δ * |x (t + 1)| := by
      intro t
      have : δ * f t = x t - δ * x (t + 1) := by rw [hrec t]; ring
      rw [this]
      calc |x t - δ * x (t + 1)| ≤ |x t| + |δ * x (t + 1)| := abs_sub _ _
        _ = |x t| + δ * |x (t + 1)| := by rw [abs_mul, abs_of_nonneg hδ0]
    refine Summable.of_norm_bounded
      ((summable_geometric_of_lt_one hδ0 hδ1).mul_right (B + δ * B)) fun t => ?_
    rw [Real.norm_eq_abs, pow_succ, mul_assoc, abs_mul, abs_of_nonneg (pow_nonneg hδ0 t)]
    refine mul_le_mul_of_nonneg_left ((hf t).trans ?_) (pow_nonneg hδ0 t)
    linarith [hx t, mul_le_mul_of_nonneg_left (hx (t + 1)) hδ0]
  exact (habs.hasSum_iff_tendsto_nat).2 hsum

/-- **Example 20.D.3** (MWG, p. 751): iterating the Euler equations from `t = 1`,
`1 + γ'(k₁ - k₀) = ∑_{t ≥ 1} δ^t (F'(k_t) - 1)`: the cost of an extra unit of capacity at `t = 1`
equals the discounted marginal products of a maintained unit of capacity. Valid when the marginal
adjustment costs `γ'(k_{t+1} - k_t)` along the path are bounded and `0 ≤ δ < 1`. -/
theorem example_20_D_3_iterated {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) {F' γ' : ℝ → ℝ}
    {k : ℕ → ℝ} (heul : ∀ t, -1 - γ' (k (t + 1) - k t)
      + δ * (F' (k (t + 1)) + γ' (k (t + 2) - k (t + 1))) = 0)
    {B : ℝ} (hγb : ∀ t, |γ' (k (t + 1) - k t)| ≤ B) :
    HasSum (fun t => δ ^ (t + 1) * (F' (k (t + 1)) - 1)) (1 + γ' (k 1 - k 0)) := by
  have := hasSum_of_recursion (x := fun t => 1 + γ' (k (t + 1) - k t))
    (f := fun t => F' (k (t + 1)) - 1) hδ0 hδ1 (B := 1 + B)
    (fun t => (abs_add_le _ _).trans (by rw [abs_one]; linarith [hγb t]))
    (fun t => by have := heul t; simp only [show t + 1 + 1 = t + 2 by omega]; linarith)
  simpa using this

/-! ### Exercise 20.D.5 -/

/-- The adjustment cost of Exercise 20.D.5: `γ(x) = x^β` for `x ≥ 0` and `0` for `x ≤ 0`. -/
noncomputable def powCost (β : ℝ) (x : ℝ) : ℝ := (max x 0) ^ β

/-- **Exercise 20.D.5** (MWG, p. 784): for `β > 1`, `γ'(0) = 0`. -/
theorem exercise_20_D_5_gamma_deriv_zero {β : ℝ} (hβ : 1 < β) : HasDerivAt (powCost β) 0 0 := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hc : Continuous fun x : ℝ => |x| ^ (β - 1) :=
    continuous_abs.rpow_const fun _ => Or.inr (by linarith)
  have hlim : Tendsto (fun x : ℝ => |x| ^ (β - 1)) (𝓝[≠] 0) (𝓝 0) := by
    have := hc.tendsto 0
    rw [abs_zero, Real.zero_rpow (by linarith)] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := hx
  have hβ0 : β ≠ 0 := by linarith
  have h0 : powCost β 0 = 0 := by simp [powCost, Real.zero_rpow hβ0]
  rw [slope_def_field, h0, sub_zero, sub_zero, Real.norm_eq_abs]
  rcases lt_or_gt_of_ne hx0 with hneg | hpos
  · have : powCost β x = 0 := by simp [powCost, max_eq_right hneg.le, Real.zero_rpow hβ0]
    rw [this, zero_div, abs_zero]
    exact Real.rpow_nonneg (abs_nonneg x) _
  · have : powCost β x = x ^ β := by simp [powCost, max_eq_left hpos.le]
    rw [this, abs_div, abs_of_pos hpos, abs_of_pos (Real.rpow_pos_of_pos hpos β),
      Real.rpow_sub hpos, Real.rpow_one]

/-- **Exercise 20.D.5** (MWG, p. 784): `γ'(x) = β x^{β-1}` for `x > 0`. -/
theorem exercise_20_D_5_gamma_deriv_pos {β x : ℝ} (hx : 0 < x) :
    HasDerivAt (powCost β) (β * x ^ (β - 1)) x := by
  have h := Real.hasDerivAt_rpow_const (x := x) (p := β) (Or.inl hx.ne')
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hx] with y hy
  simp [powCost, max_eq_left (le_of_lt (Set.mem_Ioi.1 hy))]

/-- **Exercise 20.D.5** (MWG, p. 784): `γ'(x) = 0` for `x < 0`. -/
theorem exercise_20_D_5_gamma_deriv_neg {β x : ℝ} (hx : x < 0) :
    HasDerivAt (powCost β) 0 x := by
  refine (hasDerivAt_const x ((0 : ℝ) ^ β)).congr_of_eventuallyEq ?_
  filter_upwards [Iio_mem_nhds hx] with y hy
  simp [powCost, max_eq_right (le_of_lt (Set.mem_Iio.1 hy))]

/-- **Exercise 20.D.5** (MWG, p. 784): `F(k) = k^α` has `F'(k) = α k^{α-1}` for `k > 0`. -/
theorem exercise_20_D_5_F_deriv {α k : ℝ} (hk : 0 < k) :
    HasDerivAt (fun x : ℝ => x ^ α) (α * k ^ (α - 1)) k :=
  Real.hasDerivAt_rpow_const (Or.inl hk.ne')

/-- **Exercise 20.D.5** (MWG, p. 784), the steady state: a constant path `k_t = k > 0` satisfies
the Euler equations of Example 20.D.3 with `F(k) = k^α` and `γ'(0) = 0` if and only if
`k = (αδ)^{1/(1-α)}` (for `0 < α < 1`, `0 < δ`). -/
theorem exercise_20_D_5_steady_state {α δ k : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hδ : 0 < δ)
    (hk : 0 < k) :
    (-1 - 0 + δ * (α * k ^ (α - 1) + 0) = 0) ↔ k = (α * δ) ^ (1 / (1 - α)) := by
  have hαδ : 0 < α * δ := mul_pos hα0 hδ
  have h1α : (1 : ℝ) - α ≠ 0 := by linarith
  constructor
  · intro h
    have hk' : k ^ (α - 1) = (α * δ)⁻¹ := by
      field_simp; linarith
    have hk2 : k ^ (1 - α) = α * δ := by
      rw [show (1 : ℝ) - α = -(α - 1) by ring, Real.rpow_neg hk.le, hk', inv_inv]
    rw [← hk2, ← Real.rpow_mul hk.le, mul_one_div_cancel h1α, Real.rpow_one]
  · intro h
    rw [h, ← Real.rpow_mul hαδ.le]
    have : 1 / (1 - α) * (α - 1) = -1 := by field_simp; ring
    rw [this, Real.rpow_neg_one]
    field_simp
    ring

/-! ### Example 20.D.4 and Exercise 20.D.7 -/

/-- **Exercise 20.D.7** (MWG, p. 784): with `u(k, k') = ln(2k - k')` and `δ = 1/2`, for
`Du_t(v, w) = (2v - w) / c_t` with `c_t = 2k_t - k_{t+1} > 0`, the Euler equations (20.D.9) are
`k_{t+2} = 3k_{t+1} - 2k_t` (MWG's `k_{t+1} = 3k_t - 2k_{t-1}`). -/
theorem exercise_20_D_7_euler {k : ℕ → ℝ} (hc : ∀ t, 0 < 2 * k t - k (t + 1))
    {Du : ℕ → ℝ × ℝ →L[ℝ] ℝ} (hDu : ∀ t v w, Du t (v, w) = (2 * v - w) / (2 * k t - k (t + 1))) :
    EulerEq (1 / 2) Du ↔ ∀ t, k (t + 2) = 3 * k (t + 1) - 2 * k t := by
  constructor
  · intro h t
    have := h t 1
    rw [hDu, hDu] at this
    have h0 := (hc t).ne'
    have h1 := (hc (t + 1)).ne'
    field_simp at this
    simp only [show t + 1 + 1 = t + 2 by omega] at this
    linarith
  · intro h t v
    rw [hDu, hDu, show t + 1 + 1 = t + 2 by omega, h t]
    have h0 := (hc t).ne'
    have : 2 * k (t + 1) - (3 * k (t + 1) - 2 * k t) = 2 * k t - k (t + 1) := by ring
    rw [this]
    field_simp
    ring

/-- The derivative of `u(k, k') = ln(2k - k')` at a point with `2k - k' > 0` (Example 20.D.4). -/
theorem example_20_D_4_deriv {a b : ℝ} (hab : 0 < 2 * a - b) :
    ∃ D : ℝ × ℝ →L[ℝ] ℝ, HasFDerivAt (fun p : ℝ × ℝ => Real.log (2 * p.1 - p.2)) D (a, b) ∧
      ∀ v w, D (v, w) = (2 * v - w) / (2 * a - b) := by
  have h1 : HasFDerivAt (fun p : ℝ × ℝ => 2 * p.1 - p.2)
      ((2 : ℝ) • ContinuousLinearMap.fst ℝ ℝ ℝ - ContinuousLinearMap.snd ℝ ℝ ℝ) (a, b) :=
    (hasFDerivAt_fst.const_mul (2 : ℝ)).sub hasFDerivAt_snd
  have h2 := (Real.hasDerivAt_log hab.ne').comp_hasFDerivAt (a, b) h1
  refine ⟨_, (h2 : HasFDerivAt (fun p : ℝ × ℝ => Real.log (2 * p.1 - p.2)) _ (a, b)),
    fun v w => ?_⟩
  simp
  field_simp

/-- **Exercise 20.D.7** (MWG, p. 784): `k_t = k₀ + (k₁ - k₀)(2^t - 1)` solves
`k_{t+2} = 3k_{t+1} - 2k_t`. -/
theorem exercise_20_D_7_solution (k₀ k₁ : ℝ) (t : ℕ) :
    let k : ℕ → ℝ := fun t => k₀ + (k₁ - k₀) * (2 ^ t - 1)
    k (t + 2) = 3 * k (t + 1) - 2 * k t ∧ k 0 = k₀ ∧ k 1 = k₁ := by
  intro k
  refine ⟨by simp only [k, pow_succ]; ring, by simp [k], by simp only [k]; ring⟩

/-- **Exercise 20.D.7** (MWG, p. 784): every solution of the difference equation is of this
form. -/
theorem exercise_20_D_7_unique {k : ℕ → ℝ} (h : ∀ t, k (t + 2) = 3 * k (t + 1) - 2 * k t)
    (t : ℕ) : k t = k 0 + (k 1 - k 0) * (2 ^ t - 1) := by
  have key : ∀ t, k t = k 0 + (k 1 - k 0) * (2 ^ t - 1) ∧
      k (t + 1) = k 0 + (k 1 - k 0) * (2 ^ (t + 1) - 1) := by
    intro t
    induction t with
    | zero => exact ⟨by simp, by simp; ring⟩
    | succ t ih =>
      refine ⟨ih.2, ?_⟩
      rw [show t + 1 + 1 = t + 2 by omega, h t, ih.1, ih.2, pow_succ, pow_succ]
      ring
  exact (key t).1

/-- **Example 20.D.4** (MWG, p. 753): along a solution, consumption `c_t = 2k_t - k_{t+1}` is
constant, equal to `2k₀ - k₁`. -/
theorem example_20_D_4_consumption (k₀ k₁ : ℝ) (t : ℕ) :
    let k : ℕ → ℝ := fun t => k₀ + (k₁ - k₀) * (2 ^ t - 1)
    2 * k t - k (t + 1) = 2 * k₀ - k₁ := by
  intro k
  simp only [k, pow_succ]
  ring

/-- **Example 20.D.4** (MWG, p. 753): if `k₁ < k₀`, `k_t` eventually becomes negative. -/
theorem example_20_D_4_negative {k₀ k₁ : ℝ} (h : k₁ < k₀) :
    ∃ t : ℕ, k₀ + (k₁ - k₀) * (2 ^ t - 1) < 0 := by
  obtain ⟨t, ht⟩ := pow_unbounded_of_one_lt (k₀ / (k₀ - k₁) + 1) (by norm_num : (1 : ℝ) < 2)
  refine ⟨t, ?_⟩
  have hd : 0 < k₀ - k₁ := by linarith
  have : k₀ < (k₀ - k₁) * (2 ^ t - 1) := by
    rw [div_add_one hd.ne', div_lt_iff₀ hd] at ht
    nlinarith
  nlinarith

/-- **Example 20.D.4** (MWG, p. 753): if `k₁ > k₀`, `k_t` is unbounded. -/
theorem example_20_D_4_unbounded {k₀ k₁ : ℝ} (h : k₀ < k₁) (B : ℝ) :
    ∃ t : ℕ, B < k₀ + (k₁ - k₀) * (2 ^ t - 1) := by
  have hd : 0 < k₁ - k₀ := by linarith
  obtain ⟨t, ht⟩ := pow_unbounded_of_one_lt ((B - k₀) / (k₁ - k₀) + 1) (by norm_num : (1 : ℝ) < 2)
  refine ⟨t, ?_⟩
  rw [div_add_one hd.ne', div_lt_iff₀ hd] at ht
  nlinarith

/-- **Example 20.D.4** (MWG, p. 753): `k₁ = k₀` is the only choice generating a bounded
solution, so `ψ(k₀) = k₀`. -/
theorem example_20_D_4_bounded_iff {k₀ k₁ : ℝ} :
    (∃ B, ∀ t : ℕ, |k₀ + (k₁ - k₀) * (2 ^ t - 1)| ≤ B) ↔ k₁ = k₀ := by
  constructor
  · rintro ⟨B, hB⟩
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · obtain ⟨t, ht⟩ := example_20_D_4_unbounded (k₀ := k₁) (k₁ := k₀) h 0
      -- symmetric bound: use the explicit growth of `|k_t|`
      have hd : 0 < k₀ - k₁ := by linarith
      obtain ⟨s, hs⟩ := pow_unbounded_of_one_lt ((B + |k₀|) / (k₀ - k₁) + 1)
        (by norm_num : (1 : ℝ) < 2)
      rw [div_add_one hd.ne', div_lt_iff₀ hd] at hs
      have := hB s
      have h2 := neg_abs_le (k₀ + (k₁ - k₀) * (2 ^ s - 1))
      have h3 := le_abs_self k₀
      nlinarith
    · obtain ⟨t, ht⟩ := example_20_D_4_unbounded h B
      have := (le_abs_self _).trans (hB t)
      linarith
  · intro h
    rw [h]
    exact ⟨|k₀|, fun t => by simp⟩

/-- **Example 20.D.4** (MWG, p. 753): for `k₀ < k₁ < 2k₀` the Euler path is feasible with constant
consumption `2k₀ - k₁ > 0`, but it is not optimal: the stationary path `k₁ = k₀` has the strictly
higher constant consumption `k₀`, hence strictly higher utility `∑ (1/2)^t ln c`. -/
theorem example_20_D_4_not_optimal {k₀ k₁ : ℝ} (h1 : k₀ < k₁) (h2 : k₁ < 2 * k₀) :
    0 < 2 * k₀ - k₁ ∧
      ∑' t : ℕ, (1 / 2 : ℝ) ^ t * Real.log (2 * k₀ - k₁)
        < ∑' t : ℕ, (1 / 2 : ℝ) ^ t * Real.log k₀ := by
  have hc : 0 < 2 * k₀ - k₁ := by linarith
  refine ⟨hc, ?_⟩
  rw [tsum_mul_right, tsum_mul_right]
  have hg : 0 < ∑' t : ℕ, (1 / 2 : ℝ) ^ t := by
    rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; norm_num
  exact mul_lt_mul_of_pos_left (Real.log_lt_log hc (by linarith)) hg

/-- **Correction to Example 20.D.4** (MWG, p. 753): for `k₁ ≥ 2k₀` the Euler path is not feasible,
since consumption `2k₀ - k₁` is not positive. -/
theorem example_20_D_4_infeasible {k₀ k₁ : ℝ} (h : 2 * k₀ ≤ k₁) (t : ℕ) :
    ¬ 0 < 2 * (k₀ + (k₁ - k₀) * (2 ^ t - 1)) - (k₀ + (k₁ - k₀) * (2 ^ (t + 1) - 1)) := by
  rw [example_20_D_4_consumption k₀ k₁ t]
  linarith

/-- **Footnote 17** (MWG, p. 753): when `k₁ > k₀`, the supporting prices read off the Euler
equations, `p_t = (1/2)^t / c` with constant consumption `c = 2k₀ - k₁`, violate the
transversality condition: the value `p_{t+1} F(k_t) = p_{t+1} 2k_t` of the output tends to
`(k₁ - k₀)/c ≠ 0`. -/
theorem footnote_20_17 {k₀ k₁ : ℝ} (h1 : k₀ < k₁) (h2 : k₁ < 2 * k₀) :
    let k : ℕ → ℝ := fun t => k₀ + (k₁ - k₀) * (2 ^ t - 1)
    let c := 2 * k₀ - k₁
    Tendsto (fun t : ℕ => (1 / 2 : ℝ) ^ (t + 1) / c * (2 * k t)) atTop (𝓝 ((k₁ - k₀) / c)) ∧
      (k₁ - k₀) / c ≠ 0 := by
  intro k c
  have hc : 0 < c := by simp only [c]; linarith
  refine ⟨?_, div_ne_zero (by linarith) hc.ne'⟩
  have hform : ∀ t : ℕ, (1 / 2 : ℝ) ^ (t + 1) / c * (2 * k t)
      = ((k₁ - k₀) + (2 * k₀ - k₁) * (1 / 2 : ℝ) ^ t) / c := by
    intro t
    have h2t : (1 / 2 : ℝ) ^ t * 2 ^ t = 1 := by rw [← mul_pow]; norm_num
    calc (1 / 2 : ℝ) ^ (t + 1) / c * (2 * k t) = ((1 / 2 : ℝ) ^ t * k t) / c := by
          rw [pow_succ]; ring
      _ = _ := by
          congr 1
          simp only [k]
          linear_combination (k₁ - k₀) * h2t
  have hlim : Tendsto (fun t : ℕ => ((k₁ - k₀) + (2 * k₀ - k₁) * (1 / 2 : ℝ) ^ t) / c) atTop
      (𝓝 (((k₁ - k₀) + (2 * k₀ - k₁) * 0) / c)) :=
    ((tendsto_const_nhds.add (tendsto_const_nhds.mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)))).div_const c)
  rw [mul_zero, add_zero] at hlim
  exact hlim.congr fun t => (hform t).symm

/-- The admissible region of Example 20.D.4: positive consumption `2k - k' > 0`. -/
def logRegion : Set (ℝ × ℝ) := {p | 0 < 2 * p.1 - p.2}

/-- **Example 20.D.4** (MWG, p. 753): by Proposition 20.D.7, the stationary path `k_t = k₀ > 0`
solves (20.D.8) among bounded admissible paths (so `ψ(k₀) = k₀`). -/
theorem example_20_D_4_optimal {k₀ : ℝ} (hk₀ : 0 < k₀) (k' : ℕ → ℝ)
    (hk' : Admissible logRegion k₀ k') {R' : ℝ} (hbdd' : ∀ t, ‖k' t‖ ≤ R')
    (hsum' : Summable fun t => (1 / 2 : ℝ) ^ t * Real.log (2 * k' t - k' (t + 1))) :
    reducedObjective (1 / 2) (fun p => Real.log (2 * p.1 - p.2)) k'
      ≤ reducedObjective (1 / 2) (fun p => Real.log (2 * p.1 - p.2)) (fun _ => k₀) := by
  have hconv : Convex ℝ logRegion := by
    intro x hx y hy a b ha hb hab
    simp only [logRegion, Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul] at *
    rcases eq_or_lt_of_le ha with h | h
    · have hb1 : b = 1 := by linarith
      rw [← h, hb1]; linarith
    · nlinarith [mul_pos h hx, mul_nonneg hb hy.le]
  have hconc : ConcaveOn ℝ logRegion (fun p : ℝ × ℝ => Real.log (2 * p.1 - p.2)) := by
    refine ⟨hconv, fun x hx y hy a b ha hb hab => ?_⟩
    have h := (StrictConcaveOn.concaveOn strictConcaveOn_log_Ioi).2 (Set.mem_Ioi.2 hx)
      (Set.mem_Ioi.2 hy) ha hb hab
    simp only [smul_eq_mul, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd] at h ⊢
    convert h using 2
    ring
  have hD : ∃ D : ℝ × ℝ →L[ℝ] ℝ, HasFDerivAt (fun p : ℝ × ℝ => Real.log (2 * p.1 - p.2)) D
      (k₀, k₀) ∧ ∀ v w, D (v, w) = (2 * v - w) / (2 * k₀ - k₀) :=
    example_20_D_4_deriv (by linarith)
  obtain ⟨D, hDd, hDf⟩ := hD
  refine proposition_20_D_7 (K := ℝ) (by norm_num) (by norm_num) hconc
    ⟨rfl, fun t => by simp only [logRegion, Set.mem_ofPred_eq]; linarith⟩ ?_
    (R := |k₀|) (fun t => by simp [Real.norm_eq_abs]) (ε := k₀ / 3) (by linarith)
    (fun t => ?_) (Du := fun _ => D) (fun t => hDd) ?_ k' hk' hbdd' hsum'
  · simp only [mul_comm]
    exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_right _
  · intro p hp
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq] at hp
    simp only [logRegion, Set.mem_ofPred_eq]
    have h1 := abs_lt.1 hp.1
    have h2 := abs_lt.1 hp.2
    linarith [h1.1, h2.2]
  · intro t v
    rw [hDf, hDf]
    field_simp
    ring

end MWG.EquilibriumTime

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Stationary paths, interest rates and golden rules (MWG Section 20.E, pp. 754-756)

MWG, Chapter 20, Section 20.E: Definitions 20.E.1-20.E.2, Propositions 20.E.1-20.E.2, and
Exercises 20.E.1, 20.E.2 and 20.E.9 (pp. 784-785).

* **Definition 20.E.1** (`IsStationary`); proportional price sequences `p_t = α^t p₀`
  (`propPrices`) and the implicit rate of interest `r = (1 - α)/α` (`exercise_20_E_1`).
* **Proposition 20.E.1** in the smooth case MWG treat: an efficient stationary path is supported
  by proportional prices (`proposition_20_E_1`), and every supporting sequence is proportional
  (`supporting_prices_proportional`). The nonsmooth case is OPEN (MWG: "too delicate").
* **Proposition 20.E.2**: efficiency for `r > 0` (`proposition_20_E_2_pos`) and inefficiency
  for `r < 0` in the smooth case (`proposition_20_E_2_neg`), via the fact that a direction below
  the tangent hyperplane of a smooth convex body points into it (`exists_mem_of_smooth_neg`).
* **Definition 20.E.2** (`IsModifiedGoldenRule`, `IsGoldenRule`); a stationary interior
  equilibrium is a modified golden rule (`stationary_equilibrium_modified_golden_rule`).
* **Exercise 20.E.2** (proportional paths under constant returns): (a)
  `exercise_20_E_2a`, (b) `exercise_20_E_2b_pos`, `exercise_20_E_2b_neg`.
* **Exercise 20.E.9**: the golden rule is not a stationary equilibrium (`exercise_20_E_9`).
-/

open Filter Topology

namespace MWG.EquilibriumTime

variable {ι : Type*} [Fintype ι]

/-- **Definition 20.E.1** (MWG, p. 754): a path is stationary (a steady state) if `y_t = ȳ` for
all `t`, for some `ȳ ∈ Y`. -/
def IsStationary (Y : Set (ProdPlan ι)) (y : ℕ → ProdPlan ι) : Prop :=
  ∃ yb ∈ Y, ∀ t, y t = yb

/-- The proportional price sequence `(p₀, α p₀, α² p₀, ...)` (MWG, p. 754). -/
def propPrices (α : ℝ) (p₀ : ι → ℝ) : ℕ → ι → ℝ := fun t => α ^ t • p₀

omit [Fintype ι] in
/-- **Exercise 20.E.1** (MWG, p. 784): with `r = (1 - α)/α`, the proportional prices satisfy
`p_t = (1 + r) p_{t+1}`, so `r` is the own rate of interest of every commodity (Exercise 20.C.1)
at every date. -/
theorem exercise_20_E_1 {α : ℝ} (hα : 0 < α) (p₀ : ι → ℝ) (t : ℕ) :
    propPrices α p₀ t = (1 + (1 - α) / α) • propPrices α p₀ (t + 1) ∧
      ∀ l, p₀ l ≠ 0 → ownRate (propPrices α p₀) t l = (1 - α) / α := by
  constructor
  · funext l
    simp only [propPrices, Pi.smul_apply, smul_eq_mul, pow_succ]
    field_simp
    ring
  · intro l hl
    simp only [ownRate, propPrices, Pi.smul_apply, smul_eq_mul, pow_succ]
    have : α ^ t ≠ 0 := pow_ne_zero t hα.ne'
    field_simp

/-- A continuous linear functional on `ℝ^L × ℝ^L` is the value function of its coefficient
vectors. -/
theorem clm_prod_eq_planValue [DecidableEq ι] (f : ProdPlan ι →L[ℝ] ℝ) (z : ProdPlan ι) :
    f z = planValue (fun i => f (Pi.single i 1, 0)) (fun i => f (0, Pi.single i 1)) z := by
  have h1 : z.1 = ∑ i, z.1 i • (Pi.single i 1 : ι → ℝ) := by
    funext j; simp [Finset.sum_apply, Pi.single_apply]
  have h2 : z.2 = ∑ i, z.2 i • (Pi.single i 1 : ι → ℝ) := by
    funext j; simp [Finset.sum_apply, Pi.single_apply]
  have hz : z = ∑ i, z.1 i • ((Pi.single i 1 : ι → ℝ), (0 : ι → ℝ))
      + ∑ i, z.2 i • ((0 : ι → ℝ), (Pi.single i 1 : ι → ℝ)) := by
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add, Prod.fst_sum, Prod.smul_fst, smul_zero, Finset.sum_const_zero,
        add_zero]
      exact h1
    · simp only [Prod.snd_add, Prod.snd_sum, Prod.smul_snd, smul_zero, Finset.sum_const_zero,
        zero_add]
      exact h2
  conv_lhs => rw [hz]
  simp only [map_add, map_sum, map_smul, smul_eq_mul, planValue, dotProduct]
  congr 1 <;> exact Finset.sum_congr rfl fun i _ => by ring

/-- **A direction below the tangent hyperplane points into a smooth convex body** (the test used
in the proof of Proposition 20.E.2, MWG, p. 755): if `Y` is convex with nonempty interior and
smooth at `ȳ ∈ Y` with normal `q`, and `q · d < 0`, then `ȳ + ε d ∈ Y` for some `ε > 0`. -/
theorem exists_mem_of_smooth_neg {Y : Set (ProdPlan ι)} (hY : Convex ℝ Y)
    (hint : (interior Y).Nonempty) {yb q d : ProdPlan ι} (hyb : yb ∈ Y) (hs : SmoothAt Y yb q)
    (hd : planValue q.1 q.2 d < 0) : ∃ ε : ℝ, 0 < ε ∧ yb + ε • d ∈ Y := by
  classical
  by_contra hno
  push Not at hno
  set ray : Set (ProdPlan ι) := {z | ∃ ε : ℝ, 0 < ε ∧ z = yb + ε • d} with hray
  have hrayc : Convex ℝ ray := by
    rintro _ ⟨ε₁, h₁, rfl⟩ _ ⟨ε₂, h₂, rfl⟩ a b ha hb hab
    refine ⟨a * ε₁ + b * ε₂, ?_, ?_⟩
    · rcases eq_or_lt_of_le ha with rfl | ha'
      · have hb1 : b = 1 := by linarith
        subst hb1; simpa using h₂
      · nlinarith [mul_pos ha' h₁, mul_nonneg hb h₂.le]
    · rw [smul_add, smul_add, smul_smul, smul_smul, add_add_add_comm, ← add_smul, hab,
        one_smul, ← add_smul]
  have hdisj : Disjoint (interior Y) ray := by
    rw [Set.disjoint_left]
    rintro z hz ⟨ε, hε, rfl⟩
    exact hno ε hε (interior_subset hz)
  obtain ⟨f, u, hfs, hft⟩ := geometric_hahn_banach_open hY.interior isOpen_interior
    hrayc hdisj
  -- `f ≤ u` on `Y`, and `f ȳ ≥ u`
  have hclos : Y ⊆ {z | f z ≤ u} := by
    intro z hz
    have hz' : z ∈ closure (interior Y) := by
      rw [hY.closure_interior_eq_closure_of_nonempty_interior hint]; exact subset_closure hz
    exact closure_lt_subset_le f.continuous continuous_const
      (closure_mono (fun w hw => hfs w hw) hz')
  have hfyb : u ≤ f yb := by
    by_contra hlt
    push Not at hlt
    -- choose `ε` small so that `f (ȳ + ε d) < u`
    have hcont : Tendsto (fun ε : ℝ => f (yb + ε • d)) (𝓝 0) (𝓝 (f yb)) := by
      have : Continuous fun ε : ℝ => f (yb + ε • d) := by fun_prop
      simpa using this.tendsto 0
    have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), f (yb + ε • d) < u :=
      (hcont.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds hlt)
    obtain ⟨ε, hεlt, hε⟩ := (hev.and self_mem_nhdsWithin).exists
    exact absurd (hft _ ⟨ε, hε, rfl⟩) (not_le.2 hεlt)
  -- `f` supports `Y` at `ȳ`, so it is a positive multiple of `q`
  set qf : ProdPlan ι := (fun i => f (Pi.single i 1, 0), fun i => f (0, Pi.single i 1))
  have hfeq : ∀ z, f z = planValue qf.1 qf.2 z := clm_prod_eq_planValue f
  have hqf0 : qf ≠ 0 := by
    intro h0
    obtain ⟨z, hz⟩ := hint
    have h1 := hfs z hz
    have h2 := hft (yb + (1 : ℝ) • d) ⟨1, one_pos, rfl⟩
    rw [hfeq z, h0] at h1
    rw [hfeq, h0] at h2
    simp [planValue] at h1 h2
    linarith
  obtain ⟨c, hc, hceq⟩ := hs.2 qf ⟨hqf0, fun z hz => by
    rw [← hfeq, ← hfeq]; exact (hclos hz).trans hfyb⟩
  have h1 := hft (yb + (1 : ℝ) • d) ⟨1, one_pos, rfl⟩
  have h2 : f yb ≤ u := hclos hyb
  rw [hfeq] at h1 h2
  rw [hceq] at h1 h2
  simp only [Prod.smul_fst, Prod.smul_snd] at h1 h2
  rw [planValue_smul] at h1 h2
  simp only [planValue, Prod.fst_add, Prod.snd_add, one_smul, dotProduct_add] at h1 h2 hd
  nlinarith [mul_neg_of_pos_of_neg hc hd]

/-- **Every supporting price sequence of a smooth stationary path is proportional** (MWG, p. 754,
proof of Proposition 20.E.1): if `Y` is smooth at `ȳ` with normal `q`, `q_b ≠ 0`, and `p` is a
Malinvaud price sequence for the stationary path with `(p_t, p_{t+1}) ≠ 0` for all `t`, then
`p_t = α^t p₀` for some `α > 0`. -/
theorem supporting_prices_proportional {Y : Set (ProdPlan ι)} {yb q : ProdPlan ι}
    (hs : SmoothAt Y yb q) (hqb : q.1 ≠ 0) {p : ℕ → ι → ℝ}
    (hmy : MyopicProfitMax Y p (fun _ => yb)) (hp : ∀ t, ((p t, p (t + 1)) : ProdPlan ι) ≠ 0) :
    ∃ α : ℝ, 0 < α ∧ ∀ t, p t = α ^ t • p 0 := by
  have hlam : ∀ t, ∃ c : ℝ, 0 < c ∧ ((p t, p (t + 1)) : ProdPlan ι) = c • q := fun t =>
    hs.2 _ ⟨hp t, fun z hz => hmy.2 t z hz⟩
  choose c hc hceq using hlam
  have hb : ∀ t, p t = c t • q.1 := fun t => by
    have := congrArg Prod.fst (hceq t); simpa using this
  have ha : ∀ t, p (t + 1) = c t • q.2 := fun t => by
    have := congrArg Prod.snd (hceq t); simpa using this
  -- `q_a = (c_{t+1} / c_t) q_b` for every `t`, so the ratio is constant
  have hratio : ∀ t, c (t + 1) = (c 1 / c 0) * c t := by
    intro t
    obtain ⟨i, hi⟩ : ∃ i, q.1 i ≠ 0 := by
      by_contra h; push Not at h; exact hqb (funext h)
    have e1 : c t * q.2 i = c (t + 1) * q.1 i := by
      have := congrFun ((ha t).symm.trans (hb (t + 1))) i; simpa using this
    have e0 : c 0 * q.2 i = c 1 * q.1 i := by
      have := congrFun ((ha 0).symm.trans (hb 1)) i; simpa using this
    have hc0 := (hc 0).ne'
    have hct := (hc t).ne'
    field_simp
    have : c (t + 1) * q.1 i * c 0 = c 1 * q.1 i * c t := by
      rw [← e1, ← e0]; ring
    exact mul_right_cancel₀ hi (by linarith [this])
  refine ⟨c 1 / c 0, div_pos (hc 1) (hc 0), fun t => ?_⟩
  have hct : ∀ t, c t = (c 1 / c 0) ^ t * c 0 := by
    intro t
    induction t with
    | zero => simp
    | succ t ih => rw [hratio t, ih, pow_succ]; ring
  rw [hb t, hb 0, hct t, smul_smul]

/-- **Proposition 20.E.1** (MWG, p. 754), the smooth case: an efficient stationary path of a
convex technology that is smooth at `ȳ` with normal `q`, `q_b ≫ 0`, `q_a ≫ 0`, is myopically
profit maximizing for a proportional price sequence `(p₀, α p₀, α² p₀, ...)` with `α > 0` and
`p₀ ≫ 0`. -/
theorem proposition_20_E_1 {L : ℕ} (hL : 0 < L) {Y : Set (ProdPlan (Fin L))} (hY : Convex ℝ Y)
    {yb q : ProdPlan (Fin L)} (hs : SmoothAt Y yb q) (hqb : StrictPos q.1) (hqa : StrictPos q.2)
    (heff : ProdEfficient Y (fun _ => yb)) :
    ∃ α : ℝ, 0 < α ∧ StrictPos q.1 ∧ MyopicProfitMax Y (propPrices α q.1) (fun _ => yb) := by
  have h2 : TEfficient Y (fun _ => yb) 2 :=
    ⟨heff.1, fun ⟨y', hy', hle, hne, _, _⟩ => heff.2 ⟨y', hy', hle, hne⟩⟩
  have hne : ∀ v : Fin L → ℝ, StrictPos v → v ≠ 0 := fun v hv h => by
    have := hv ⟨0, hL⟩; rw [h] at this; exact lt_irrefl _ this
  obtain ⟨β, hβ, hβeq⟩ := proportional_normals_of_twoEfficient (q := fun _ => q) hL hY h2 0 hs hs
    (hne _ hqa) (hne _ hqb)
  refine ⟨β, hβ, hqb, heff.1, fun t z hz => ?_⟩
  have hpair : ((propPrices β q.1 t, propPrices β q.1 (t + 1)) : ProdPlan (Fin L))
      = β ^ t • q := by
    refine Prod.ext ?_ ?_
    · simp [propPrices]
    · simp only [propPrices, Prod.smul_snd, pow_succ, mul_smul]
      exact congrArg _ hβeq.symm
  simp only [periodProfit]
  have hval : ∀ w, planValue (propPrices β q.1 t) (propPrices β q.1 (t + 1)) w
      = β ^ t * planValue q.1 q.2 w := by
    intro w
    have e1 := congrArg Prod.fst hpair
    have e2 := congrArg Prod.snd hpair
    simp only [Prod.smul_fst, Prod.smul_snd] at e1 e2
    rw [e1, e2, planValue_smul]
  rw [hval, hval]
  exact mul_le_mul_of_nonneg_left (hs.1.2 z hz) (pow_nonneg hβ.le t)

/-- **Proposition 20.E.2**, first part (MWG, p. 755): a stationary path supported by
proportional prices with `p₀ ≫ 0` and rate of interest `r > 0` (that is, `0 < α < 1`) satisfies
the transversality condition and is therefore efficient (Proposition 20.C.1). -/
theorem proposition_20_E_2_pos {Y : Set (ProdPlan ι)} (htr : ∀ z ∈ Y, (z.1, 0) ∈ Y)
    {yb : ProdPlan ι} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {p₀ : ι → ℝ} (hp₀ : StrictPos p₀)
    (hmy : MyopicProfitMax Y (propPrices α p₀) (fun _ => yb)) : ProdEfficient Y (fun _ => yb) := by
  refine proposition_20_C_1 htr (fun t i => ?_) hmy ?_
  · simp only [propPrices, Pi.smul_apply, smul_eq_mul]
    exact mul_pos (pow_pos hα0 t) (hp₀ i)
  · unfold Transversality
    simp only [propPrices, smul_dotProduct, smul_eq_mul]
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one hα0.le hα1).comp (tendsto_add_atTop_nat 1)
    simpa using this.mul_const (p₀ ⬝ᵥ yb.2)

/-- **Proposition 20.E.2**, second part (MWG, p. 755): in the smooth case (convex `Y` with
nonempty interior, smooth at `ȳ`), a stationary path supported by proportional prices with
`p₀ ≥ 0`, `p₀ ≠ 0`, and rate of interest `r < 0` (`α > 1`) is inefficient: for small `ε > 0` the
stationary path `ȳ + ε (e, -e)` dominates it (it overaccumulates). -/
theorem proposition_20_E_2_neg [Nonempty ι] {Y : Set (ProdPlan ι)} (hY : Convex ℝ Y)
    (hint : (interior Y).Nonempty) {yb q : ProdPlan ι} (hyb : yb ∈ Y) (hs : SmoothAt Y yb q)
    {α : ℝ} (hα : 1 < α) {p₀ : ι → ℝ} (hp₀ : 0 ≤ p₀) (hp₀ne : p₀ ≠ 0)
    (hmy : MyopicProfitMax Y (propPrices α p₀) (fun _ => yb)) :
    ¬ ProdEfficient Y (fun _ => yb) := by
  set e : ι → ℝ := fun _ => 1
  set d : ProdPlan ι := (e, -e)
  -- the supporting functional at date 0 is a positive multiple of `q`
  have hsup : SupportsAt Y yb (p₀, α • p₀) := by
    refine ⟨fun h => hp₀ne (congrArg Prod.fst h), fun z hz => ?_⟩
    have := hmy.2 0 z hz
    simpa [periodProfit, propPrices] using this
  obtain ⟨c, hc, hceq⟩ := hs.2 _ hsup
  have hpe : 0 < p₀ ⬝ᵥ e := by
    obtain ⟨i, hi⟩ : ∃ i, p₀ i ≠ 0 := by
      by_contra h; push Not at h; exact hp₀ne (funext h)
    refine Finset.sum_pos' (fun j _ => by simpa [e] using hp₀ j) ⟨i, Finset.mem_univ _, ?_⟩
    simpa [e] using lt_of_le_of_ne (hp₀ i) (Ne.symm hi)
  have hqd : planValue q.1 q.2 d < 0 := by
    have hv : planValue p₀ (α • p₀) d = c * planValue q.1 q.2 d := by
      have e1 := congrArg Prod.fst hceq
      have e2 := congrArg Prod.snd hceq
      simp only [Prod.smul_fst, Prod.smul_snd] at e1 e2
      rw [e2, e1, planValue_smul]
    have : planValue p₀ (α • p₀) d = (1 - α) * (p₀ ⬝ᵥ e) := by
      simp only [planValue, d, smul_dotProduct, dotProduct_neg, smul_eq_mul]; ring
    have hneg : planValue p₀ (α • p₀) d < 0 := by
      rw [this]; exact mul_neg_of_neg_of_pos (by linarith) hpe
    rw [hv] at hneg
    by_contra hge
    push Not at hge
    exact absurd hneg (not_lt.2 (mul_nonneg hc.le hge))
  obtain ⟨ε, hε, hmem⟩ := exists_mem_of_smooth_neg hY hint hyb hs hqd
  rintro ⟨-, hno⟩
  refine hno ⟨fun _ => yb + ε • d, fun _ => hmem, fun t => ?_, ?_⟩
  · cases t with
    | zero =>
      intro i
      simp [netOutput, d, e, hε.le]
    | succ t =>
      intro i
      simp only [netOutput, d, e, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, mul_one, mul_neg]
      linarith
  · intro h
    have := congrFun (congrFun h 0) (Classical.arbitrary ι)
    exact hε.ne' (by simpa [netOutput, d, e] using this)

/-- **Definition 20.E.2** (MWG, p. 755): a stationary path is a **modified golden rule path** if it
is myopically supported by proportional prices `p_t = δ^t p₀`. -/
def IsModifiedGoldenRule (Y : Set (ProdPlan ι)) (δ : ℝ) (yb : ProdPlan ι) : Prop :=
  yb ∈ Y ∧ ∃ p₀ : ι → ℝ, p₀ ≠ 0 ∧ MyopicProfitMax Y (propPrices δ p₀) (fun _ => yb)

/-- **Definition 20.E.2** (MWG, p. 755): a stationary path is a **golden rule path** if it is
myopically supported by constant prices `p_t = p₀`. -/
def IsGoldenRule (Y : Set (ProdPlan ι)) (yb : ProdPlan ι) : Prop :=
  IsModifiedGoldenRule Y 1 yb

/-- **A stationary equilibrium is a modified golden rule** (MWG, p. 755): at a Walrasian
equilibrium whose path is stationary with constant strictly positive consumption `c̄ ≫ 0`, with
`u` concave and strictly increasing on `ℝ^L_+`, differentiable at `c̄` with strictly positive
marginal utilities, and `0 < δ`, the prices are `p_t = δ^t p₀` (by Exercise 20.D.3 and (20.D.6)),
so the path is a modified golden rule path for `δ`. In particular, the candidates for stationary
equilibria depend only on the technology and `δ`, not on `u`. -/
theorem stationary_equilibrium_modified_golden_rule {L : ℕ} [NeZero L]
    {Y : Set (ProdPlan (Fin L))} {δ : ℝ} (hδ : 0 < δ) {u : (Fin L → ℝ) → ℝ}
    (hconc : ConcaveOn ℝ (Set.Ici 0) u) (hmono : StrictMonoOn u (Set.Ici 0))
    {ω p : ℕ → Fin L → ℝ} {yb : ProdPlan (Fin L)}
    (he : WalrasEq (Set.Ici 0) Y δ u ω p (fun _ => yb)) {cb : Fin L → ℝ}
    (hcb : ∀ t, consumption ω (fun _ => yb) t = cb) (hcpos : StrictPos cb)
    {Du : (Fin L → ℝ) →L[ℝ] ℝ} (hDu : HasFDerivAt u Du cb)
    (hDpos : ∀ i, 0 < Du (Pi.single i 1)) :
    ∃ p₀ : Fin L → ℝ, StrictPos p₀ ∧ p = propPrices δ p₀ ∧ IsModifiedGoldenRule Y δ yb := by
  obtain ⟨hbud, hs, hmax⟩ := he.utilityMax
  set c := consumption ω (fun _ => yb) with hc
  have hmyo : MyopicUtilityMax (Set.Ici 0) δ u p
      (∑' t, (periodProfit p (fun _ => yb) t + p t ⬝ᵥ ω t)) c := by
    refine ⟨hbud, hs, fun t c' hc' hdiff => hmax c' hc' ?_⟩
    exact summable_of_finite_change {t, t + 1} (fun s hst => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hst
      exact hdiff s hst.1 hst.2) hs
  have hcpos' : ∀ t, StrictPos (c t) := fun t => by rw [hcb t]; exact hcpos
  obtain ⟨-, hfoc⟩ := (exercise_20_D_3 hδ hconc hmono hcpos' hbud.2.1 hs
    (fun t => by rw [hcb t]; exact hDu) (fun t i => hDpos i)).1 hmyo
  -- prices are strictly positive
  have hppos : ∀ t, StrictPos (p t) := by
    intro t i
    obtain ⟨lam, hlam, h1, -⟩ := hfoc t
    have := h1 (Pi.single i 1)
    rw [dotProduct_single, mul_one] at this
    have := hDpos i
    nlinarith
  have hpne : ∀ t, p t ≠ 0 := fun t h => by
    have := hppos t ⟨0, Nat.pos_of_ne_zero (NeZero.ne L)⟩
    rw [h] at this; exact lt_irrefl _ this
  obtain ⟨lam, hlam, h6⟩ := (foc_20_D_5_iff_20_D_6 hδ hpne).1 hfoc
  have hprop : p = propPrices δ (p 0) := by
    funext t i
    have e1 := h6 t (Pi.single i 1)
    have e0 := h6 0 (Pi.single i 1)
    simp only [dotProduct_single, mul_one, pow_zero, one_mul] at e1 e0
    simp only [propPrices, Pi.smul_apply, smul_eq_mul]
    rw [← e0] at e1
    have : lam * p t i = lam * (δ ^ t * p 0 i) := by rw [e1]; ring
    exact mul_left_cancel₀ hlam.ne' this
  refine ⟨p 0, hppos 0, hprop, he.myopic.1 0, p 0, hpne 0, ?_⟩
  rw [← hprop]
  exact he.myopic

/-! ### Proportional paths (Exercise 20.E.2) and the golden rule (Exercise 20.E.9) -/

/-- A technology is a **cone** (constant returns): `y ∈ Y` and `λ ≥ 0` imply `λ y ∈ Y`. -/
def IsConeTech (Y : Set (ProdPlan ι)) : Prop := ∀ y ∈ Y, ∀ c : ℝ, 0 ≤ c → c • y ∈ Y

/-- Under constant returns, a normal at `ȳ` is a normal at every `λ ȳ`, `λ > 0`, and smoothness is
inherited. -/
theorem smoothAt_smul_of_cone {Y : Set (ProdPlan ι)} (hc : IsConeTech Y) {yb q : ProdPlan ι}
    (hyb : yb ∈ Y) (hs : SmoothAt Y yb q) {c : ℝ} (hc0 : 0 < c) : SmoothAt Y (c • yb) q := by
  -- every supporting functional vanishes at `ȳ`
  have hzero : ∀ q', SupportsAt Y yb q' → planValue q'.1 q'.2 yb = 0 := by
    intro q' hq'
    have h0 := hq'.2 _ (hc yb hyb 0 le_rfl)
    have h2 := hq'.2 _ (hc yb hyb 2 (by norm_num))
    simp only [planValue, zero_smul, Prod.smul_fst, Prod.smul_snd, Prod.fst_zero,
      Prod.snd_zero, dotProduct_zero, dotProduct_smul, smul_eq_mul, add_zero] at h0 h2
    simp only [planValue]
    linarith
  have hval : ∀ q' : ProdPlan ι, planValue q'.1 q'.2 (c • yb) = c * planValue q'.1 q'.2 yb := by
    intro q'; simp only [planValue, Prod.smul_fst, Prod.smul_snd, dotProduct_smul, smul_eq_mul]
    ring
  refine ⟨⟨hs.1.1, fun z hz => ?_⟩, fun q' hq' => hs.2 q' ⟨hq'.1, fun z hz => ?_⟩⟩
  · rw [hval, hzero q hs.1, mul_zero, ← hzero q hs.1]; exact hs.1.2 z hz
  · -- `q'` supports at `c ȳ`, hence vanishes there and supports at `ȳ`
    have h0 := hq'.2 _ (hc _ (hc yb hyb c hc0.le) 0 le_rfl)
    simp only [zero_smul] at h0
    simp only [planValue, Prod.fst_zero, Prod.snd_zero, dotProduct_zero, add_zero] at h0
    have h2 := hq'.2 _ (hc _ (hc yb hyb c hc0.le) 2 (by norm_num))
    have hc' := hq'.2 z hz
    rw [hval] at hc'
    simp only [planValue, Prod.smul_fst, Prod.smul_snd, dotProduct_smul, smul_eq_mul] at h0 h2 hc' ⊢
    nlinarith

/-- Malinvaud prices from a **common smooth normal**: if a `2`-efficient path of a convex
technology is smooth at every `y_t` with the same normal `q` (`q_b, q_a ≫ 0`), it is myopically
profit maximizing for a proportional sequence `p_t = β^t q_b`. -/
theorem malinvaud_prop_of_common_normal {L : ℕ} (hL : 0 < L) {Y : Set (ProdPlan (Fin L))}
    (hY : Convex ℝ Y) {y : ℕ → ProdPlan (Fin L)} (h2 : TEfficient Y y 2) {q : ProdPlan (Fin L)}
    (hs : ∀ t, SmoothAt Y (y t) q) (hqb : StrictPos q.1) (hqa : StrictPos q.2) :
    ∃ β : ℝ, 0 < β ∧ MyopicProfitMax Y (propPrices β q.1) y := by
  have hne : ∀ v : Fin L → ℝ, StrictPos v → v ≠ 0 := fun v hv h => by
    have := hv ⟨0, hL⟩; rw [h] at this; exact lt_irrefl _ this
  obtain ⟨β, hβ, hβeq⟩ := proportional_normals_of_twoEfficient (q := fun _ => q) hL hY h2 0
    (hs 0) (hs 1) (hne _ hqa) (hne _ hqb)
  refine ⟨β, hβ, h2.1, fun t z hz => ?_⟩
  have hval : ∀ w, planValue (propPrices β q.1 t) (propPrices β q.1 (t + 1)) w
      = β ^ t * planValue q.1 q.2 w := by
    intro w
    simp only [propPrices, pow_succ, mul_smul]
    rw [← hβeq, planValue_smul]
  simp only [periodProfit]
  rw [hval, hval]
  exact mul_le_mul_of_nonneg_left ((hs t).1.2 z hz) (pow_nonneg hβ.le t)

/-- **Exercise 20.E.2(a)** (MWG, p. 784): under constant returns, Proposition 20.E.1 holds for
proportional paths `y_t = (1 + n)^t ȳ` (`n > -1`): an efficient proportional path of a convex cone
technology that is smooth at `ȳ` (normal parts `≫ 0`) is supported by proportional prices. -/
theorem exercise_20_E_2a {L : ℕ} (hL : 0 < L) {Y : Set (ProdPlan (Fin L))} (hY : Convex ℝ Y)
    (hcone : IsConeTech Y) {yb q : ProdPlan (Fin L)} (hyb : yb ∈ Y) (hs : SmoothAt Y yb q)
    (hqb : StrictPos q.1) (hqa : StrictPos q.2) {n : ℝ} (hn : -1 < n)
    (heff : ProdEfficient Y (fun t => (1 + n) ^ t • yb)) :
    ∃ β : ℝ, 0 < β ∧ MyopicProfitMax Y (propPrices β q.1) (fun t => (1 + n) ^ t • yb) :=
  malinvaud_prop_of_common_normal hL hY ⟨heff.1, fun ⟨y', hy', hle, hne, _, _⟩ =>
    heff.2 ⟨y', hy', hle, hne⟩⟩
    (fun t => smoothAt_smul_of_cone hcone hyb hs (pow_pos (by linarith) t)) hqb hqa

/-- **Exercise 20.E.2(b)**, efficiency (MWG, p. 784): a proportional path `y_t = (1+n)^t ȳ`
supported by `p_t = α^t p₀` (`p₀ ≫ 0`) with `α (1 + n) < 1` (rate of interest `r > n`) satisfies
transversality and is efficient. -/
theorem exercise_20_E_2b_pos {Y : Set (ProdPlan ι)} (htr : ∀ z ∈ Y, (z.1, 0) ∈ Y)
    {yb : ProdPlan ι} {α n : ℝ} (hα0 : 0 < α) (hn : -1 < n) (hαn : α * (1 + n) < 1)
    {p₀ : ι → ℝ} (hp₀ : StrictPos p₀)
    (hmy : MyopicProfitMax Y (propPrices α p₀) (fun t => (1 + n) ^ t • yb)) :
    ProdEfficient Y (fun t => (1 + n) ^ t • yb) := by
  refine proposition_20_C_1 htr (fun t i => ?_) hmy ?_
  · simp only [propPrices, Pi.smul_apply, smul_eq_mul]
    exact mul_pos (pow_pos hα0 t) (hp₀ i)
  · unfold Transversality
    have hn0 : 0 ≤ α * (1 + n) := mul_nonneg hα0.le (by linarith)
    have hlim := (tendsto_pow_atTop_nhds_zero_of_lt_one hn0 hαn).mul_const (α * (p₀ ⬝ᵥ yb.2))
    rw [zero_mul] at hlim
    refine hlim.congr fun t => ?_
    simp only [propPrices, Prod.smul_snd, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      mul_pow, pow_succ]
    ring

/-- **Exercise 20.E.2(b)**, inefficiency (MWG, p. 784): in the smooth constant-returns case, a
proportional path supported by `p_t = α^t p₀` (`p₀ ≥ 0`, `p₀ ≠ 0`) with `α (1 + n) > 1` (rate of
interest `r < n`) is inefficient: `(1+n)^t (ȳ + ε(e, -(1+n) e))` dominates it. -/
theorem exercise_20_E_2b_neg [Nonempty ι] {Y : Set (ProdPlan ι)} (hY : Convex ℝ Y)
    (hcone : IsConeTech Y) (hint : (interior Y).Nonempty) {yb q : ProdPlan ι} (hyb : yb ∈ Y)
    (hs : SmoothAt Y yb q) {α n : ℝ} (hn : -1 < n) (hαn : 1 < α * (1 + n)) {p₀ : ι → ℝ}
    (hp₀ : 0 ≤ p₀) (hp₀ne : p₀ ≠ 0)
    (hmy : MyopicProfitMax Y (propPrices α p₀) (fun t => (1 + n) ^ t • yb)) :
    ¬ ProdEfficient Y (fun t => (1 + n) ^ t • yb) := by
  set e : ι → ℝ := fun _ => 1
  set d : ProdPlan ι := (e, -((1 + n) • e))
  have hsup : SupportsAt Y yb (p₀, α • p₀) := by
    refine ⟨fun h => hp₀ne (congrArg Prod.fst h), fun z hz => ?_⟩
    have := hmy.2 0 z hz
    simpa [periodProfit, propPrices] using this
  obtain ⟨c, hc, hceq⟩ := hs.2 _ hsup
  have hpe : 0 < p₀ ⬝ᵥ e := by
    obtain ⟨i, hi⟩ : ∃ i, p₀ i ≠ 0 := by
      by_contra h; push Not at h; exact hp₀ne (funext h)
    refine Finset.sum_pos' (fun j _ => by simpa [e] using hp₀ j) ⟨i, Finset.mem_univ _, ?_⟩
    simpa [e] using lt_of_le_of_ne (hp₀ i) (Ne.symm hi)
  have hqd : planValue q.1 q.2 d < 0 := by
    have hv : planValue p₀ (α • p₀) d = c * planValue q.1 q.2 d := by
      have e1 := congrArg Prod.fst hceq
      have e2 := congrArg Prod.snd hceq
      simp only [Prod.smul_fst, Prod.smul_snd] at e1 e2
      rw [e2, e1, planValue_smul]
    have : planValue p₀ (α • p₀) d = (1 - α * (1 + n)) * (p₀ ⬝ᵥ e) := by
      simp only [planValue, d, smul_dotProduct, dotProduct_neg, dotProduct_smul, smul_eq_mul]
      ring
    have hneg : planValue p₀ (α • p₀) d < 0 := by
      rw [this]; exact mul_neg_of_neg_of_pos (by linarith) hpe
    rw [hv] at hneg
    by_contra hge
    push Not at hge
    exact absurd hneg (not_lt.2 (mul_nonneg hc.le hge))
  obtain ⟨ε, hε, hmem⟩ := exists_mem_of_smooth_neg hY hint hyb hs hqd
  rintro ⟨-, hno⟩
  have h1n : 0 < 1 + n := by linarith
  refine hno ⟨fun t => (1 + n) ^ t • (yb + ε • d),
    fun t => hcone _ hmem _ (pow_nonneg h1n.le t), fun t => ?_, ?_⟩
  · cases t with
    | zero =>
      intro i
      simp [netOutput, d, e, hε.le]
    | succ t =>
      intro i
      simp only [netOutput, d, e, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, mul_one, mul_neg, pow_succ]
      nlinarith [pow_pos h1n t]
  · intro h
    have := congrFun (congrFun h 0) (Classical.arbitrary ι)
    exact hε.ne' (by simpa [netOutput, d, e] using this)

/-- **Exercise 20.E.9** (MWG, p. 785): in the one-consumer model with `δ < 1`, a stationary
equilibrium path (interior, as in `stationary_equilibrium_modified_golden_rule`) of a technology
that is smooth at `ȳ` with `q_b ≠ 0` is not a golden rule path: the golden rule needs constant
supporting prices, the equilibrium needs prices declining at the rate `δ`, and smoothness allows
only one proportionality factor. -/
theorem exercise_20_E_9 {L : ℕ} [NeZero L] {Y : Set (ProdPlan (Fin L))} {δ : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ < 1) {u : (Fin L → ℝ) → ℝ} (hconc : ConcaveOn ℝ (Set.Ici 0) u)
    (hmono : StrictMonoOn u (Set.Ici 0)) {ω p : ℕ → Fin L → ℝ} {yb q : ProdPlan (Fin L)}
    (he : WalrasEq (Set.Ici 0) Y δ u ω p (fun _ => yb)) {cb : Fin L → ℝ}
    (hcb : ∀ t, consumption ω (fun _ => yb) t = cb) (hcpos : StrictPos cb)
    {Du : (Fin L → ℝ) →L[ℝ] ℝ} (hDu : HasFDerivAt u Du cb)
    (hDpos : ∀ i, 0 < Du (Pi.single i 1)) (hs : SmoothAt Y yb q) :
    ¬ IsGoldenRule Y yb := by
  rintro ⟨-, p', hp'ne, hmy'⟩
  obtain ⟨p₀, hp₀, -, hmgr⟩ := stationary_equilibrium_modified_golden_rule hδ0 hconc hmono he hcb
    hcpos hDu hDpos
  obtain ⟨-, p₀', hp₀'ne, hmy⟩ := hmgr
  -- both `(p', p')` and `(p₀', δ p₀')` are positive multiples of `q`
  obtain ⟨c, hc, hceq⟩ := hs.2 (p', (1 : ℝ) • p') ⟨fun h => hp'ne (congrArg Prod.fst h),
    fun z hz => by simpa [periodProfit, propPrices] using hmy'.2 0 z hz⟩
  obtain ⟨c', hc', hc'eq⟩ := hs.2 (p₀', δ • p₀') ⟨fun h => hp₀'ne (congrArg Prod.fst h),
    fun z hz => by simpa [periodProfit, propPrices] using hmy.2 0 z hz⟩
  have h1 : p' = c • q.1 := by have := congrArg Prod.fst hceq; simpa using this
  have h2 : p' = c • q.2 := by have := congrArg Prod.snd hceq; simpa using this
  have h3 : p₀' = c' • q.1 := by have := congrArg Prod.fst hc'eq; simpa using this
  have h4 : δ • p₀' = c' • q.2 := by have := congrArg Prod.snd hc'eq; simpa using this
  have hq : q.1 = q.2 := by
    have := h1.symm.trans h2
    have := congrArg (fun v => c⁻¹ • v) this
    simpa [smul_smul, inv_mul_cancel₀ hc.ne'] using this
  have : δ • p₀' = p₀' := by rw [h4, ← hq, ← h3]
  have : (δ - 1) • p₀' = 0 := by rw [sub_smul, this, one_smul, sub_self]
  rcases smul_eq_zero.1 this with h | h
  · linarith
  · exact hp₀'ne h

end MWG.EquilibriumTime

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Steady states of the Ramsey-Solow model and golden rules (MWG Section 20.E, pp. 756-759)

MWG, Chapter 20, Section 20.E from p. 756, with Exercises 20.E.3-20.E.8 (pp. 784-785).

Labor is fixed at one unit per period; `f(k) = F(k, 1)` (`F ![k, 1]`). A steady state `k` has
surplus `c(k) = f(k) - k` and rate of interest `r(k) = f'(k) - 1`; the golden rule `k̂` maximizes
`c`, i.e. `f'(k̂) = 1` (`golden_rule_iff`), and the modified golden rule has
`r(k_δ) = (1 - δ)/δ`.

* The interest rate implicit in Malinvaud prices: `q_{t+1}(1 + r_t) = q_t`
  (`rs_interest_rate`); the steady-state supporting prices (`rs_steady_prices`).
* Below the golden rule `r > 0`, above it `r < 0` (`rate_pos_below_golden`,
  `rate_neg_above_golden`); steady states above the golden rule are inefficient
  (`inefficient_above_golden`); **the golden rule is efficient** (`golden_rule_efficient`, from
  the capital-depletion argument `golden_rule_capital`).
* **Exercise 20.E.3**: every path with `k_t ≤ k̂ - ε` is efficient (`exercise_20_E_3`).
* **Exercise 20.E.4**, the neoclassical properties (`exercise_20_E_4_i_mono`,
  `exercise_20_E_4_i_anti`, `exercise_20_E_4_ii`, `exercise_20_E_4_iii`), with Euler's theorem
  for constant returns (`euler_homogeneous`).
* **(20.E.1)** and **Exercises 20.E.5-20.E.7** for the multisector model, and **Exercise
  20.E.8** (growth golden rule `r = n`).

Not formalised: the possibility of several modified golden rules in the two-sector model
(Figure 20.E.3, a graphical claim without explicit data), and the efficiency of the golden rule in
the general `(N+1)`-sector model (asserted without proof, "we could also prove").
-/

open Filter Topology

namespace MWG.EquilibriumTime

/-! ### Concavity tools on the real line -/

/-- The three-chord inequality for a concave function: for `a ≤ b < c` in `S`,
`(f c - f b)/(c - b) ≤ (f c - f a)/(c - a)`. -/
theorem chord_right_le {S : Set ℝ} {f : ℝ → ℝ} (hf : ConcaveOn ℝ S f) {a b c : ℝ} (ha : a ∈ S)
    (hc : c ∈ S) (hab : a ≤ b) (hbc : b < c) :
    (f c - f b) / (c - b) ≤ (f c - f a) / (c - a) := by
  rcases eq_or_lt_of_le hab with rfl | hab'
  · exact le_rfl
  have hca : 0 < c - a := by linarith
  have hcb : 0 < c - b := by linarith
  set lam := (c - b) / (c - a) with hlam
  have hl0 : 0 ≤ lam := div_nonneg hcb.le hca.le
  have hl1 : 0 ≤ 1 - lam := by
    rw [hlam, sub_nonneg, div_le_one hca]; linarith
  have hb : lam • a + (1 - lam) • c = b := by
    simp only [smul_eq_mul, hlam]; field_simp; ring
  have := hf.2 ha hc hl0 hl1 (by ring)
  rw [hb] at this
  simp only [smul_eq_mul] at this
  rw [div_le_div_iff₀ hcb hca]
  have e : (c - b) = lam * (c - a) := by rw [hlam]; field_simp
  rw [e]
  nlinarith

/-- A strictly concave function with derivative `1` at `k̂` lies strictly below its tangent:
`f(k̂ - d) < f(k̂) - d` for `0 < d` with `k̂ - d ∈ S`. -/
theorem strict_tangent_below {S : Set ℝ} {f : ℝ → ℝ} (hf : StrictConcaveOn ℝ S f) {kh d : ℝ}
    (hkh : kh ∈ S) (hd : 0 < d) (hmem : kh - d ∈ S) (hder : HasDerivAt f 1 kh) :
    f (kh - d) < f kh - d := by
  have := hf.lt_slope_of_hasDerivAt hmem hkh (by linarith) hder
  rw [slope_def_field, lt_div_iff₀ (by linarith)] at this
  linarith

/-- A strictly concave function is strictly increasing to the left of a maximizer. -/
theorem strictMonoOn_left_of_max {S : Set ℝ} {g : ℝ → ℝ} (hg : StrictConcaveOn ℝ S g) {m : ℝ}
    (hm : m ∈ S) (hmax : ∀ x ∈ S, g x ≤ g m) :
    StrictMonoOn g (S ∩ Set.Iic m) := by
  intro a ha b hb hab
  rcases eq_or_lt_of_le (Set.mem_Iic.1 hb.2) with rfl | hbm
  · -- `a < m`: the midpoint beats `a`, so `g a < g m`
    have hmid := hg.2 ha.1 hm (ne_of_lt hab) (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
    have hmS : (1 / 2 : ℝ) • a + (1 / 2 : ℝ) • b ∈ S :=
      hg.1 ha.1 hm (by norm_num) (by norm_num) (by norm_num)
    have := hmax _ hmS
    simp only [smul_eq_mul] at hmid this
    linarith
  · have hma : 0 < m - a := by linarith
    set lam := (m - b) / (m - a) with hlam
    have hl0 : 0 < lam := div_pos (by linarith) hma
    have hl1 : 0 < 1 - lam := by rw [hlam, sub_pos, div_lt_one hma]; linarith
    have hcomb : lam • a + (1 - lam) • m = b := by
      simp only [smul_eq_mul, hlam]; field_simp; ring
    have := hg.2 ha.1 hm (ne_of_lt (lt_trans hab hbm)) hl0 hl1 (by ring)
    rw [hcomb] at this
    simp only [smul_eq_mul] at this
    have := hmax a ha.1
    nlinarith

/-- A strictly concave function is strictly decreasing to the right of a maximizer. -/
theorem strictAntiOn_right_of_max {S : Set ℝ} {g : ℝ → ℝ} (hg : StrictConcaveOn ℝ S g) {m : ℝ}
    (hm : m ∈ S) (hmax : ∀ x ∈ S, g x ≤ g m) :
    StrictAntiOn g (S ∩ Set.Ici m) := by
  intro a ha b hb hab
  rcases eq_or_lt_of_le (Set.mem_Ici.1 ha.2) with rfl | ham
  · have hmid := hg.2 hm hb.1 (ne_of_lt hab) (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
    have hmS : (1 / 2 : ℝ) • m + (1 / 2 : ℝ) • b ∈ S :=
      hg.1 hm hb.1 (by norm_num) (by norm_num) (by norm_num)
    have := hmax _ hmS
    simp only [smul_eq_mul] at hmid this
    linarith
  · have hbm : 0 < b - m := by linarith
    set lam := (b - a) / (b - m) with hlam
    have hl0 : 0 < lam := div_pos (by linarith) hbm
    have hl1 : 0 < 1 - lam := by rw [hlam, sub_pos, div_lt_one hbm]; linarith
    have hcomb : lam • m + (1 - lam) • b = a := by
      simp only [smul_eq_mul, hlam]; field_simp; ring
    have := hg.2 hm hb.1 (ne_of_lt (lt_trans ham hab)) hl0 hl1 (by ring)
    rw [hcomb] at this
    simp only [smul_eq_mul] at this
    have := hmax b hb.1
    nlinarith

/-! ### Steady states of the Ramsey-Solow model -/

/-- The capital derivative of `F(·, 1)` is the partial derivative `∇₁F`. -/
theorem hasDerivAt_capital {F : (Fin 2 → ℝ) → ℝ} {k l : ℝ} {DF : (Fin 2 → ℝ) →L[ℝ] ℝ}
    (hDF : HasFDerivAt F DF ![k, l]) :
    HasDerivAt (fun s => F ![s, l]) (DF (Pi.single 0 1)) k := by
  have hline : HasDerivAt (fun s : ℝ => (![s, l] : Fin 2 → ℝ)) (Pi.single 0 1) k := by
    refine hasDerivAt_pi.2 fun i => ?_
    fin_cases i
    · simpa using hasDerivAt_id' k
    · simpa using hasDerivAt_const k l
  exact hDF.comp_hasDerivAt k hline

/-- **The rate of interest is the net marginal productivity of capital** (MWG, p. 756): at an
interior plan `(k_t, 1)` supported by Malinvaud prices, `q_{t+1}(1 + r_t) = q_t` with
`r_t = ∇₁F(k_t, 1) - 1`. -/
theorem rs_interest_rate {F : (Fin 2 → ℝ) → ℝ} {k : ℝ} (hk : 0 < k)
    {DF : (Fin 2 → ℝ) →L[ℝ] ℝ} (hDF : HasFDerivAt F DF ![k, 1]) {q w q' w' : ℝ}
    (hmax : ∀ z ∈ ramseySolowSet F, planValue ![q, w] ![q', w'] z ≤
      planValue ![q, w] ![q', w'] (rsPlan F k 1)) :
    q' * (1 + (DF (Pi.single 0 1) - 1)) = q := by
  obtain ⟨h, -⟩ := rs_foc_of_profitMax hk one_pos hDF hmax
  rw [h]; ring

/-- **The steady-state supporting prices** (MWG, p. 756): for a steady state `k ≥ 0` with
`r = ∇₁F(k, 1) - 1 > -1` and `∇₂F ≥ 0`, the sequence `(q_t, w_t) = (1/(1 + r))^t (q₀, w₀)` with
`w₀ / q₀ = ∇₂F / ∇₁F` (here `q₀ = 1`) myopically supports the stationary path. -/
theorem rs_steady_prices {F : (Fin 2 → ℝ) → ℝ} (hconc : ConcaveOn ℝ (Set.Ici 0) F)
    (hmono : MonotoneOn F (Set.Ici 0)) {k : ℝ} (hk : 0 ≤ k) {DF : (Fin 2 → ℝ) →L[ℝ] ℝ}
    (hDF : HasFDerivAt F DF ![k, 1]) (hpos : 0 < DF (Pi.single 0 1)) :
    MyopicProfitMax (ramseySolowSet F)
      (fun t => ((1 / DF (Pi.single 0 1)) ^ t) • ![1, DF (Pi.single 1 1) / DF (Pi.single 0 1)])
      (fun _ => rsPlan F k 1) := by
  have h := exercise_20_C_6 hconc hmono (k := fun _ => k) (l := fun _ => 1) (fun _ => hk)
    (fun _ => zero_le_one) (DF := fun _ => DF) (fun _ => hDF)
    (q := fun t => (1 / DF (Pi.single 0 1)) ^ t)
    (fun t => pow_pos (by positivity) t) (fun t => by
      rw [pow_succ]; field_simp)
  convert h using 1
  · funext t i
    fin_cases i
    · simp [rsPrices]
    · simp only [rsPrices, Pi.smul_apply, smul_eq_mul, Fin.mk_one, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, pow_succ]
      field_simp
  · rfl

/-- **The golden rule** (MWG, p. 756): for `f` concave on `ℝ_+` and differentiable at `k̂ > 0`,
`k̂` maximizes the steady-state surplus `c(k) = f(k) - k` if and only if
`r(k̂) = f'(k̂) - 1 = 0`. -/
theorem golden_rule_iff {f : ℝ → ℝ} (hf : ConcaveOn ℝ (Set.Ici 0) f) {kh f' : ℝ}
    (hkh : 0 < kh) (hder : HasDerivAt f f' kh) :
    (∀ k, 0 ≤ k → f k - k ≤ f kh - kh) ↔ f' - 1 = 0 := by
  constructor
  · intro h
    have hloc : IsLocalMax (fun k => f k - k) kh := by
      filter_upwards [Ioi_mem_nhds hkh] with k hk using h k (le_of_lt hk)
    have := hloc.hasDerivAt_eq_zero (hder.sub (hasDerivAt_id kh))
    linarith
  · intro h k hk
    have := MWG.GeneralEquilibriumExamples.concave_le_tangent hf (Set.mem_Ici.2 hkh.le)
      (Set.mem_Ici.2 hk) hder
    have hf1 : f' = 1 := by linarith
    rw [hf1] at this
    linarith

/-- **The modified golden rule** (MWG, p. 756): `r(k_δ) = (1 - δ)/δ` exactly when `f'(k_δ) = 1/δ`,
the factor of the proportional prices `δ^t`. -/
theorem modified_golden_rule_iff {δ f' : ℝ} (hδ : δ ≠ 0) : f' - 1 = (1 - δ) / δ ↔ f' = 1 / δ := by
  constructor <;> intro h
  · field_simp at h ⊢; linarith
  · rw [h]; field_simp

/-- **Below the golden rule the rate of interest is positive** (MWG, p. 756): for `f` strictly
concave and `0 ≤ k < k̂`, `f'(k) > f'(k̂) = 1`. -/
theorem rate_pos_below_golden {f : ℝ → ℝ} (hf : StrictConcaveOn ℝ (Set.Ici 0) f) {k kh fk : ℝ}
    (hk : 0 ≤ k) (hkkh : k < kh) (hdk : HasDerivAt f fk k) (hdkh : HasDerivAt f 1 kh) :
    0 < fk - 1 := by
  have h1 := hf.slope_lt_of_hasDerivAt (Set.mem_Ici.2 hk) (Set.mem_Ici.2 (hk.trans hkkh.le))
    hkkh hdk
  have h2 := hf.lt_slope_of_hasDerivAt (Set.mem_Ici.2 hk) (Set.mem_Ici.2 (hk.trans hkkh.le))
    hkkh hdkh
  linarith

/-- **Above the golden rule the rate of interest is negative** (MWG, p. 756). -/
theorem rate_neg_above_golden {f : ℝ → ℝ} (hf : StrictConcaveOn ℝ (Set.Ici 0) f) {k kh fk : ℝ}
    (hkh : 0 ≤ kh) (hkkh : kh < k) (hdk : HasDerivAt f fk k) (hdkh : HasDerivAt f 1 kh) :
    fk - 1 < 0 := by
  have h1 := hf.slope_lt_of_hasDerivAt (Set.mem_Ici.2 hkh) (Set.mem_Ici.2 (hkh.trans hkkh.le))
    hkkh hdkh
  have h2 := hf.lt_slope_of_hasDerivAt (Set.mem_Ici.2 hkh) (Set.mem_Ici.2 (hkh.trans hkkh.le))
    hkkh hdk
  linarith

/-- **Steady states above the golden rule are inefficient** (MWG, p. 756): if `k̂ < k` and `k̂`
maximizes the surplus `F(k, 1) - k` over `k ≥ 0`, the stationary path at `k̂` dominates the
stationary path at `k` (less capital at `t = 0`, at least as much surplus afterwards). -/
theorem inefficient_above_golden {F : (Fin 2 → ℝ) → ℝ} {k kh : ℝ} (hkh : 0 ≤ kh)
    (hkkh : kh < k) (hmax : ∀ x, 0 ≤ x → F ![x, 1] - x ≤ F ![kh, 1] - kh) :
    ¬ ProdEfficient (ramseySolowSet F) (fun _ => rsPlan F k 1) := by
  rintro ⟨-, hno⟩
  refine hno ⟨fun _ => rsPlan F kh 1, fun _ => rsPlan_mem hkh zero_le_one, fun t => ?_, ?_⟩
  · intro i
    cases t with
    | zero =>
      fin_cases i
      · simp [netOutput, rsPlan]; linarith
      · simp [netOutput, rsPlan]
    | succ t =>
      have := hmax k (hkh.trans hkkh.le)
      fin_cases i
      · simp [netOutput, rsPlan]; linarith
      · simp [netOutput, rsPlan]
  · intro h
    have := congrFun (congrFun h 0) 0
    simp [netOutput, rsPlan] at this
    linarith

/-- **The capital-depletion argument** for the golden rule (MWG, pp. 756-757, Figure 20.E.2): if
`f` is strictly concave on `ℝ_+` with `f'(k̂) = 1`, a nonnegative capital path with `k'₀ ≤ k̂` and
surplus `f(k'_t) - k'_{t+1}` at least the golden-rule surplus `f(k̂) - k̂` at every date must stay
at `k̂`: any attempt to use less capital leads to capital depletion in finite time. -/
theorem golden_rule_capital {f : ℝ → ℝ} (hf : StrictConcaveOn ℝ (Set.Ici 0) f) {kh : ℝ}
    (hkh : 0 < kh) (hder : HasDerivAt f 1 kh) {k : ℕ → ℝ} (hk0 : ∀ t, 0 ≤ k t)
    (hstart : k 0 ≤ kh) (hsurplus : ∀ t, f kh - kh ≤ f (k t) - k (t + 1)) (t : ℕ) :
    k t = kh := by
  have hcv := hf.concaveOn
  have htan : ∀ x, 0 ≤ x → f x ≤ f kh + (x - kh) := fun x hx => by
    have := MWG.GeneralEquilibriumExamples.concave_le_tangent hcv (Set.mem_Ici.2 hkh.le)
      (Set.mem_Ici.2 hx) hder
    linarith
  set d : ℕ → ℝ := fun t => kh - k t with hd
  have hstep : ∀ t, f kh - f (k t) ≤ d (t + 1) := fun t => by
    have := hsurplus t; simp only [hd]; linarith
  have hd0 : ∀ t, 0 ≤ d t := by
    intro t
    induction t with
    | zero => simp only [hd]; linarith
    | succ t ih =>
      have h1 := hstep t
      have h2 := htan (k t) (hk0 t)
      simp only [hd] at ih ⊢ h1
      linarith
  have hdle : ∀ t, d t ≤ kh := fun t => by simp only [hd]; linarith [hk0 t]
  by_contra hne
  have hds : 0 < d t := lt_of_le_of_ne (hd0 t) (fun h => hne (by simp only [hd] at h; linarith))
  set g := f kh - f (kh - d t) - d t with hg
  have hgpos : 0 < g := by
    have := strict_tangent_below hf (Set.mem_Ici.2 hkh.le) hds (Set.mem_Ici.2 (by
      simp only [hd]; linarith [hk0 t])) hder
    simp only [hg]; linarith
  -- once the deficit is at least `d_t`, it grows by at least `g` per period
  have hgrow : ∀ D, d t ≤ D → D ≤ kh → D + g ≤ f kh - f (kh - D) := by
    intro D hD hDk
    have hD0 : 0 < D := lt_of_lt_of_le hds hD
    have := chord_right_le hcv (Set.mem_Ici.2 (by linarith : (0 : ℝ) ≤ kh - D))
      (Set.mem_Ici.2 hkh.le) (by linarith : kh - D ≤ kh - d t) (by linarith : kh - d t < kh)
    rw [show kh - (kh - d t) = d t by ring, show kh - (kh - D) = D by ring,
      div_le_div_iff₀ hds hD0] at this
    have hgd : f kh - f (kh - d t) = d t + g := by simp only [hg]; ring
    rw [hgd] at this
    nlinarith
  have hlin : ∀ m : ℕ, d t + m * g ≤ d (t + m) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have h1 := hstep (t + m)
      have h2 := hgrow (d (t + m)) (by nlinarith [hgpos]) (hdle _)
      have hkd : k (t + m) = kh - d (t + m) := by simp only [hd]; ring
      rw [hkd] at h1
      rw [show t + (m + 1) = t + m + 1 by ring]
      push_cast
      linarith
  obtain ⟨m, hm⟩ := exists_nat_gt (kh / g)
  have := hlin m
  have := hdle (t + m)
  rw [div_lt_iff₀ hgpos] at hm
  nlinarith

/-- **The golden rule steady state is efficient** (MWG, pp. 756-757). Hypotheses: `F` is
nondecreasing on `ℝ²_+`, `f = F(·, 1)` is strictly concave on `ℝ_+` with `f'(k̂) = 1`, `k̂ > 0`, and
output at `k̂` strictly increases with labor up to `1` (so that saving labor costs output). -/
theorem golden_rule_efficient {F : (Fin 2 → ℝ) → ℝ} (hmono : MonotoneOn F (Set.Ici 0))
    (hf : StrictConcaveOn ℝ (Set.Ici 0) (fun k => F ![k, 1])) {kh : ℝ} (hkh : 0 < kh)
    (hder : HasDerivAt (fun k => F ![k, 1]) 1 kh)
    (hlab : ∀ l, 0 ≤ l → l < 1 → F ![kh, l] < F ![kh, 1]) :
    ProdEfficient (ramseySolowSet F) (fun _ => rsPlan F kh 1) := by
  refine ⟨fun _ => rsPlan_mem hkh.le zero_le_one, fun ⟨y', hy', hle, hne⟩ => hne ?_⟩
  rw [ramseySolowSet_eq hmono] at hy'
  set k : ℕ → ℝ := fun t => -(y' t).1 0 with hk
  set l : ℕ → ℝ := fun t => -(y' t).1 1 with hl
  have hk0 : ∀ t, 0 ≤ k t := fun t => by have := (hy' t).1 0; simp only [hk]; simp at this; linarith
  have hl0 : ∀ t, 0 ≤ l t := fun t => by have := (hy' t).1 1; simp only [hl]; simp at this; linarith
  have hneg : ∀ t, -(y' t).1 = ![k t, l t] := fun t => by
    funext i; fin_cases i <;> simp [hk, hl]
  -- labor input is at most one
  have hl1 : ∀ t, l t ≤ 1 := by
    intro t
    cases t with
    | zero => have := hle 0 1; simp [netOutput, rsPlan] at this; simp only [hl]; linarith
    | succ t =>
      have := hle (t + 1) 1
      have ha := (hy' t).2.1
      simp [netOutput, rsPlan] at this
      simp only [hl]; linarith
  -- output is at most `f(k_t)`
  have hout : ∀ t, (y' t).2 0 ≤ F ![k t, 1] := by
    intro t
    have h1 := (hy' t).2.2
    rw [hneg] at h1
    have hle' : ![k t, l t] ≤ ![k t, 1] := by
      intro i; fin_cases i <;> simp [hl1 t]
    have h0 : (0 : Fin 2 → ℝ) ≤ ![k t, l t] := by
      intro i; fin_cases i <;> simp [hk0 t, hl0 t]
    exact h1.trans (hmono h0 (h0.trans hle') hle')
  have hsurplus : ∀ t, F ![kh, 1] - kh ≤ F ![k t, 1] - k (t + 1) := by
    intro t
    have := hle (t + 1) 0
    simp [netOutput, rsPlan] at this
    have := hout t
    simp only [hk]; linarith
  have hstart : k 0 ≤ kh := by
    have := hle 0 0; simp [netOutput, rsPlan] at this; simp only [hk]; linarith
  have hkeq : ∀ t, k t = kh :=
    golden_rule_capital (f := fun k => F ![k, 1]) hf hkh hder hk0 hstart hsurplus
  -- output equals `f(k̂)` at every date
  have hx : ∀ t, (y' t).2 0 = F ![kh, 1] := by
    intro t
    refine le_antisymm (by rw [← hkeq t]; exact hout t) ?_
    have := hle (t + 1) 0
    simp [netOutput, rsPlan] at this
    have h2 := hkeq (t + 1)
    simp only [hk] at h2
    linarith
  -- labor input is exactly one
  have hlab1 : ∀ t, l t = 1 := by
    intro t
    by_contra hne1
    have hlt : l t < 1 := lt_of_le_of_ne (hl1 t) hne1
    have h1 := (hy' t).2.2
    rw [hneg, hkeq t] at h1
    have := hlab (l t) (hl0 t) hlt
    linarith [hx t]
  -- hence the net outputs coincide
  have ha1 : ∀ t, (y' t).2 1 = 0 := by
    intro t
    have := hle (t + 1) 1
    have h2 := hlab1 (t + 1)
    simp [netOutput, rsPlan] at this
    simp only [hl] at h2
    linarith [(hy' t).2.1]
  funext t i
  cases t with
  | zero =>
    fin_cases i
    · have := hkeq 0; simp only [hk] at this; simp [netOutput, rsPlan]; linarith
    · have := hlab1 0; simp only [hl] at this; simp [netOutput, rsPlan]; linarith
  | succ t =>
    fin_cases i
    · have := hkeq (t + 1); simp only [hk] at this; simp [netOutput, rsPlan, hx t]; linarith
    · have := hlab1 (t + 1); simp only [hl] at this; simp [netOutput, rsPlan, ha1 t]; linarith

/-! ### Exercises 20.E.3, 20.E.4 and 20.E.8 -/

/-- **Exercise 20.E.3** (MWG, p. 784): in the Ramsey-Solow model with `f = F(·, 1)` strictly concave
and `f'(k̂) = 1`, every capital path with `0 ≤ k_t ≤ k̂ - ε` (`ε > 0`) is efficient. The prices with
`q_t / q_{t+1} = f'(k_t)` fall geometrically, since `f'(k_t) ≥ (f(k̂) - f(k̂ - ε))/ε > 1`, so the
transversality condition holds (hint of the exercise; (20.C.1)-(20.C.2)). Hypotheses: `F` concave
and nondecreasing on `ℝ²_+`, `F(0) = 0`, differentiable along the path with positive marginal
product of labor. -/
theorem exercise_20_E_3 {F : (Fin 2 → ℝ) → ℝ} (hconc : ConcaveOn ℝ (Set.Ici 0) F)
    (hmono : MonotoneOn F (Set.Ici 0)) (h00 : F 0 = 0)
    (hf : StrictConcaveOn ℝ (Set.Ici 0) (fun k => F ![k, 1])) {kh : ℝ} (hkh : 0 < kh)
    (hder : HasDerivAt (fun k => F ![k, 1]) 1 kh) {ε : ℝ} (hε : 0 < ε) (hεk : ε ≤ kh)
    {k : ℕ → ℝ} (hk0 : ∀ t, 0 ≤ k t) (hkε : ∀ t, k t ≤ kh - ε) {DF : ℕ → (Fin 2 → ℝ) →L[ℝ] ℝ}
    (hDF : ∀ t, HasFDerivAt F (DF t) ![k t, 1]) (hmpl : ∀ t, 0 < DF t (Pi.single 1 1)) :
    ProdEfficient (ramseySolowSet F) (rsPath F k fun _ => 1) := by
  set f : ℝ → ℝ := fun k => F ![k, 1] with hfdef
  set ρ := (f kh - f (kh - ε)) / ε with hρ
  have hρ1 : 1 < ρ := by
    have := strict_tangent_below hf (Set.mem_Ici.2 hkh.le) hε (Set.mem_Ici.2 (by linarith)) hder
    rw [hρ, lt_div_iff₀ hε]; linarith
  -- the marginal product of capital along the path is at least `ρ`
  have hmpk : ∀ t, ρ ≤ DF t (Pi.single 0 1) := by
    intro t
    have hd := hasDerivAt_capital (hDF t)
    have h1 := hf.concaveOn.slope_le_of_hasDerivAt (Set.mem_Ici.2 (hk0 t))
      (Set.mem_Ici.2 hkh.le) (by linarith [hkε t]) hd
    have h2 := chord_right_le hf.concaveOn (Set.mem_Ici.2 (hk0 t)) (Set.mem_Ici.2 hkh.le)
      (hkε t) (by linarith)
    rw [show kh - (kh - ε) = ε by ring] at h2
    rw [slope_def_field] at h1
    exact h2.trans h1
  have hDpos : ∀ t, 0 < DF t (Pi.single 0 1) := fun t => by linarith [hmpk t]
  -- output prices
  set q : ℕ → ℝ := fun t => ∏ s ∈ Finset.range t, (DF s (Pi.single 0 1))⁻¹ with hq
  have hqpos : ∀ t, 0 < q t := fun t => Finset.prod_pos fun s _ => inv_pos.2 (hDpos s)
  have hqrec : ∀ t, q t / q (t + 1) = DF t (Pi.single 0 1) := by
    intro t
    have hq1 : q (t + 1) = q t * (DF t (Pi.single 0 1))⁻¹ := by
      simp only [hq, Finset.prod_range_succ]
    rw [hq1, div_mul_eq_div_div, div_self (hqpos t).ne', one_div, inv_inv]
  have hqle : ∀ t, q t ≤ (ρ⁻¹) ^ t := by
    intro t
    induction t with
    | zero => simp [hq]
    | succ t ih =>
      simp only [hq, Finset.prod_range_succ, pow_succ] at ih ⊢
      exact mul_le_mul ih (inv_anti₀ (by linarith) (hmpk t)) (inv_pos.2 (hDpos t)).le
        (pow_nonneg (inv_pos.2 (by linarith)).le t)
  have hqlim : Tendsto q atTop (𝓝 0) := by
    refine squeeze_zero (fun t => (hqpos t).le) hqle ?_
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (inv_pos.2 (by linarith)).le
      (inv_lt_one_of_one_lt₀ hρ1)
  refine efficient_of_20_C_1_20_C_2 hconc hmono h00 hk0 (fun _ => zero_le_one) hDF hmpl
    (B := F ![kh, 1]) (fun t => ?_) hqpos hqrec hqlim
  have h0 : (0 : Fin 2 → ℝ) ≤ ![k t, 1] := by
    intro i; fin_cases i <;> simp [hk0 t]
  have hle : ![k t, (1 : ℝ)] ≤ ![kh, 1] := by
    intro i; fin_cases i <;> simp; linarith [hkε t]
  have hlo := hmono (le_refl (0 : Fin 2 → ℝ)) h0 h0
  have hhi := hmono h0 (h0.trans hle) hle
  rw [h00] at hlo
  rw [abs_of_nonneg hlo]
  exact hhi

/-- **The modified golden rule is efficient** (MWG, p. 756): with `f'(k_δ) = 1/δ > 1` it lies below
the golden rule, so (Exercise 20.E.3) its stationary path is efficient. -/
theorem modified_golden_rule_below {f : ℝ → ℝ} (hf : StrictConcaveOn ℝ (Set.Ici 0) f)
    {kd kh δ : ℝ} (hkd : 0 ≤ kd) (hkh : 0 ≤ kh) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hdd : HasDerivAt f (1 / δ) kd) (hdh : HasDerivAt f 1 kh) : kd < kh := by
  by_contra hle
  push Not at hle
  rcases eq_or_lt_of_le hle with rfl | hlt
  · have := hdd.unique hdh
    rw [div_eq_one_iff_eq hδ0.ne'] at this
    linarith
  · have := rate_neg_above_golden hf hkh hlt hdd hdh
    have : 1 < 1 / δ := by rw [lt_div_iff₀ hδ0]; linarith
    linarith

/-- **Exercise 20.E.4(i)** (MWG, p. 784): the steady-state surplus `c(k) = f(k) - k` increases
strictly up to the golden rule. -/
theorem exercise_20_E_4_i_mono {f : ℝ → ℝ} (hf : StrictConcaveOn ℝ (Set.Ici 0) f) {kh : ℝ}
    (hkh : 0 < kh) (hder : HasDerivAt f 1 kh) :
    StrictMonoOn (fun k => f k - k) (Set.Ici 0 ∩ Set.Iic kh) := by
  have hg : StrictConcaveOn ℝ (Set.Ici 0) (fun k => f k - k) := by
    have hneg : ConcaveOn ℝ (Set.Ici (0 : ℝ)) (fun k => -k) :=
      ⟨convex_Ici 0, fun x _ y _ a b _ _ _ => by simp only [smul_eq_mul]; nlinarith⟩
    convert hf.add_concaveOn hneg using 1
  refine strictMonoOn_left_of_max hg (Set.mem_Ici.2 hkh.le) fun x hx => ?_
  exact (golden_rule_iff hf.concaveOn hkh hder).2 (by ring) x hx

/-- **Exercise 20.E.4(i)** (MWG, p. 784): beyond the golden rule the surplus decreases strictly. -/
theorem exercise_20_E_4_i_anti {f : ℝ → ℝ} (hf : StrictConcaveOn ℝ (Set.Ici 0) f) {kh : ℝ}
    (hkh : 0 < kh) (hder : HasDerivAt f 1 kh) :
    StrictAntiOn (fun k => f k - k) (Set.Ici 0 ∩ Set.Ici kh) := by
  have hg : StrictConcaveOn ℝ (Set.Ici 0) (fun k => f k - k) := by
    have hneg : ConcaveOn ℝ (Set.Ici (0 : ℝ)) (fun k => -k) :=
      ⟨convex_Ici 0, fun x _ y _ a b _ _ _ => by simp only [smul_eq_mul]; nlinarith⟩
    convert hf.add_concaveOn hneg using 1
  refine strictAntiOn_right_of_max hg (Set.mem_Ici.2 hkh.le) fun x hx => ?_
  exact (golden_rule_iff hf.concaveOn hkh hder).2 (by ring) x hx

/-- **Exercise 20.E.4(ii)** (MWG, p. 784): the rate of interest `r(k) = f'(k) - 1` decreases
strictly with the level of capital. -/
theorem exercise_20_E_4_ii {f : ℝ → ℝ} (hf : StrictConcaveOn ℝ (Set.Ici 0) f) {k₁ k₂ d₁ d₂ : ℝ}
    (h₁ : 0 ≤ k₁) (h₁₂ : k₁ < k₂) (hd₁ : HasDerivAt f d₁ k₁) (hd₂ : HasDerivAt f d₂ k₂) :
    d₂ - 1 < d₁ - 1 := by
  have a := hf.slope_lt_of_hasDerivAt (Set.mem_Ici.2 h₁) (Set.mem_Ici.2 (h₁.trans h₁₂.le)) h₁₂
    hd₁
  have b := hf.lt_slope_of_hasDerivAt (Set.mem_Ici.2 h₁) (Set.mem_Ici.2 (h₁.trans h₁₂.le)) h₁₂
    hd₂
  linarith

/-- **Euler's theorem** for a production function homogeneous of degree one (used in Exercise
20.E.4(iii)): `∇F(x) · x = F(x)`. -/
theorem euler_homogeneous {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : E → ℝ}
    (hhom : ∀ c : ℝ, 0 < c → ∀ x, F (c • x) = c * F x) {x : E} {DF : E →L[ℝ] ℝ}
    (hDF : HasFDerivAt F DF x) : DF x = F x := by
  have h1 : HasDerivAt (fun c : ℝ => F (c • x)) (DF x) 1 := by
    have hl : HasDerivAt (fun c : ℝ => c • x) x 1 := by
      simpa using (hasDerivAt_id (1 : ℝ)).smul_const x
    exact hDF.comp_hasDerivAt_of_eq (1 : ℝ) hl (by simp)
  have h2 : HasDerivAt (fun c : ℝ => F (c • x)) (F x) 1 := by
    have : HasDerivAt (fun c : ℝ => c * F x) (F x) 1 := by
      simpa using (hasDerivAt_id (1 : ℝ)).mul_const (F x)
    refine this.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds (one_pos : (0 : ℝ) < 1)] with c hc using hhom c hc x
  exact h1.unique h2

/-- **Exercise 20.E.4(iii)** (MWG, p. 784): with constant returns, the real wage
`w(k) = ∇₂F(k, 1)/∇₁F(k, 1) = (f(k) - k f'(k))/f'(k)` increases strictly with capital (for `f`
strictly concave, nonnegative, with positive marginal product). First, Euler's theorem gives the
wage formula. -/
theorem exercise_20_E_4_iii_wage {F : (Fin 2 → ℝ) → ℝ}
    (hhom : ∀ c : ℝ, 0 < c → ∀ x, F (c • x) = c * F x) {k : ℝ} {DF : (Fin 2 → ℝ) →L[ℝ] ℝ}
    (hDF : HasFDerivAt F DF ![k, 1]) :
    DF (Pi.single 1 1) = F ![k, 1] - k * DF (Pi.single 0 1) := by
  have h := euler_homogeneous hhom hDF
  rw [clm_fin2_apply DF] at h
  simp at h
  linarith

/-- **Exercise 20.E.4(iii)** (MWG, p. 784): the wage-rental expression `f(k)/f'(k) - k` increases
strictly with `k` for `f` strictly concave and nonnegative on `ℝ_+` with positive derivatives. -/
theorem exercise_20_E_4_iii {f : ℝ → ℝ} (hf : StrictConcaveOn ℝ (Set.Ici 0) f)
    (hf0 : ∀ k, 0 ≤ k → 0 ≤ f k) {k₁ k₂ d₁ d₂ : ℝ} (h₁ : 0 ≤ k₁) (h₁₂ : k₁ < k₂)
    (hd₁ : HasDerivAt f d₁ k₁) (hd₂ : HasDerivAt f d₂ k₂) (hpos : 0 < d₂) :
    (f k₁ - k₁ * d₁) / d₁ < (f k₂ - k₂ * d₂) / d₂ := by
  have hd12 : d₂ < d₁ := by
    have := exercise_20_E_4_ii hf h₁ h₁₂ hd₁ hd₂; linarith
  have hd1 : 0 < d₁ := hpos.trans hd12
  -- the strict tangent inequality at `k₂`
  have htan : f k₁ < f k₂ + d₂ * (k₁ - k₂) := by
    have := hf.lt_slope_of_hasDerivAt (Set.mem_Ici.2 h₁) (Set.mem_Ici.2 (h₁.trans h₁₂.le)) h₁₂
      hd₂
    rw [slope_def_field, lt_div_iff₀ (by linarith)] at this
    linarith
  have hfk1 := hf0 k₁ h₁
  rw [div_lt_div_iff₀ hd1 hpos]
  nlinarith [mul_le_mul_of_nonneg_left hd12.le hfk1]

/-- **Exercise 20.E.8** (MWG, p. 785): with constant returns and labor growing at `n`, the
proportional path `k_t = (1 + n)^t k`, `l_t = (1 + n)^t` has surplus
`F(k_t, l_t) - k_{t+1} = (1 + n)^t (f(k) - (1 + n) k)`. -/
theorem exercise_20_E_8_surplus {F : (Fin 2 → ℝ) → ℝ}
    (hhom : ∀ c : ℝ, 0 < c → ∀ x, F (c • x) = c * F x) {n : ℝ} (hn : -1 < n) (k : ℝ) (t : ℕ) :
    F ![(1 + n) ^ t * k, (1 + n) ^ t] - (1 + n) ^ (t + 1) * k
      = (1 + n) ^ t * (F ![k, 1] - (1 + n) * k) := by
  have h : (![(1 + n) ^ t * k, (1 + n) ^ t] : Fin 2 → ℝ) = (1 + n) ^ t • ![k, 1] := by
    funext i; fin_cases i <;> simp
  rw [h, hhom _ (pow_pos (by linarith) t), pow_succ]
  ring

/-- **Exercise 20.E.8** (MWG, p. 785): among the proportional paths with growth `n`, the one
maximizing (normalized) surplus `f(k) - (1 + n) k` is characterized by `r = f'(k) - 1 = n` (the
golden rule with growth), for `f` concave and differentiable at an interior `k*`. -/
theorem exercise_20_E_8 {f : ℝ → ℝ} (hf : ConcaveOn ℝ (Set.Ici 0) f) {n ks f' : ℝ}
    (hks : 0 < ks) (hder : HasDerivAt f f' ks) :
    (∀ k, 0 ≤ k → f k - (1 + n) * k ≤ f ks - (1 + n) * ks) ↔ f' - 1 = n := by
  constructor
  · intro h
    have hloc : IsLocalMax (fun k => f k - (1 + n) * k) ks := by
      filter_upwards [Ioi_mem_nhds hks] with k hk using h k (le_of_lt hk)
    have := hloc.hasDerivAt_eq_zero (hder.sub ((hasDerivAt_id ks).const_mul (1 + n)))
    linarith
  · intro h k hk
    have := MWG.GeneralEquilibriumExamples.concave_le_tangent hf (Set.mem_Ici.2 hks.le)
      (Set.mem_Ici.2 hk) hder
    have hf1 : f' = 1 + n := by linarith
    rw [hf1] at this
    linarith

/-! ### The multisector model: (20.E.1) and Exercises 20.E.5-20.E.7 -/

/-- **(20.E.1)**, **Exercise 20.E.5** (MWG, p. 758): at a steady state `(k, k)` that maximizes the
short-run profit `s G(k_{t-1}, k_t) + q_t(k_t) - q_{t-1}(k_{t-1})` (consumption price `s`, capital
prices `q_{t-1}, q_t` as linear functionals), `∇₁G(k, k) = q_{t-1}/s` and
`∇₂G(k, k) = -q_t/s`. -/
theorem eq_20_E_1 {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K] {G : K × K → ℝ}
    {k : K} {DG : K × K →L[ℝ] ℝ} (hDG : HasFDerivAt G DG (k, k)) {s : ℝ}
    {q₀ q : K →L[ℝ] ℝ}
    (hmax : IsLocalMax (fun p : K × K => s * G p + q p.2 - q₀ p.1) (k, k)) :
    (∀ v, s * DG (v, 0) = q₀ v) ∧ (∀ v, s * DG (0, v) = -q v) := by
  have hd : HasFDerivAt (fun p : K × K => s * G p + q p.2 - q₀ p.1)
      (s • DG + q.comp (ContinuousLinearMap.snd ℝ K K) - q₀.comp (ContinuousLinearMap.fst ℝ K K))
      (k, k) :=
    ((hDG.const_mul s).add (q.hasFDerivAt.comp _ hasFDerivAt_snd)).sub
      (q₀.hasFDerivAt.comp _ hasFDerivAt_fst)
  have h0 := hmax.hasFDerivAt_eq_zero hd
  constructor
  · intro v
    have := congrArg (fun L => L (v, 0)) h0
    simp at this
    linarith
  · intro v
    have := congrArg (fun L => L (0, v)) h0
    simp at this
    linarith

/-- **(20.E.1) continued** (MWG, p. 758): with proportional prices `q_{t-1} = (1 + r) q_t`, the
marginal product of a permanent increase of capital is `∇Ĝ(k) = (r/s) q_t`, where
`Ĝ(k) = G(k, k)`; hence the steady state maximizes consumption (`∇Ĝ = 0`) if and only if `r = 0`
(for `s ≠ 0`, `q_t ≠ 0`): the golden rule property. -/
theorem golden_rule_multisector {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]
    {DG : K × K →L[ℝ] ℝ} {s r : ℝ} (hs : s ≠ 0) {q : K →L[ℝ] ℝ}
    (h1 : ∀ v, s * DG (v, 0) = (1 + r) * q v) (h2 : ∀ v, s * DG (0, v) = -q v) :
    (∀ v, DG (v, v) = r / s * q v) ∧ ((∀ v, DG (v, v) = 0) ↔ (q = 0 ∨ r = 0)) := by
  have hdiag : ∀ v, DG (v, v) = r / s * q v := by
    intro v
    have hsplit : DG (v, v) = DG (v, 0) + DG (0, v) := by
      rw [← map_add, Prod.mk_add_mk, add_zero, zero_add]
    rw [hsplit]
    have e1 := h1 v
    have e2 := h2 v
    field_simp
    linarith
  refine ⟨hdiag, ⟨fun h => ?_, fun h => ?_⟩⟩
  · by_contra hc
    push Not at hc
    obtain ⟨hq, hr⟩ := hc
    obtain ⟨v, hv⟩ : ∃ v, q v ≠ 0 := by
      by_contra h'; push Not at h'; exact hq (ContinuousLinearMap.ext h')
    have := h v
    rw [hdiag v] at this
    rcases mul_eq_zero.1 this with h' | h'
    · exact hr (by rcases div_eq_zero_iff.1 h' with h'' | h'' <;> [exact h''; exact absurd h'' hs])
    · exact hv h'
  · intro v
    rw [hdiag v]
    rcases h with rfl | rfl <;> simp

/-- **Exercise 20.E.6** (MWG, p. 785): in the two-sector model (one capital good), at a supported
steady state the slope `-∇₁G/∇₂G` of the level curve of `G` through `(k, k)` equals
`q_{t-1}/q_t = 1 + r(k)`. -/
theorem exercise_20_E_6 {G1 G2 s q₀ q : ℝ} (hs : s ≠ 0) (hq : q ≠ 0) (h1 : s * G1 = q₀)
    (h2 : s * G2 = -q) : -G1 / G2 = q₀ / q := by
  have hG2 : G2 ≠ 0 := by intro h; rw [h, mul_zero] at h2; exact hq (by linarith)
  rw [div_eq_div_iff hG2 hq]
  have : G1 = q₀ / s := by field_simp; linarith
  have : G2 = -q / s := by field_simp; linarith
  subst_vars
  field_simp

/-- **Exercise 20.E.7** (MWG, p. 785): if consumption and investment goods are perfect substitutes
in production, `G(k, k' + a) = G(k, k') - a`, then `G(k, k') = H(k) - k'` with `H(k) = G(k, 0)`,
the interest rate of a steady state is `r(k) = H'(k) - 1`, and for `H` strictly concave two
different steady states have different rates of interest. -/
theorem exercise_20_E_7 {G : ℝ → ℝ → ℝ} (hsub : ∀ k k' a, G k (k' + a) = G k k' - a)
    (hH : StrictConcaveOn ℝ (Set.Ici 0) (fun k => G k 0)) {k₁ k₂ d₁ d₂ : ℝ} (h₁ : 0 ≤ k₁)
    (h₂ : 0 ≤ k₂) (hne : k₁ ≠ k₂) (hd₁ : HasDerivAt (fun k => G k 0) d₁ k₁)
    (hd₂ : HasDerivAt (fun k => G k 0) d₂ k₂) :
    (∀ k k', G k k' = G k 0 - k') ∧ d₁ - 1 ≠ d₂ - 1 := by
  refine ⟨fun k k' => by simpa using hsub k 0 k', fun h => ?_⟩
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have := exercise_20_E_4_ii hH h₁ hlt hd₁ hd₂; linarith
  · have := exercise_20_E_4_ii hH h₂ hgt hd₂ hd₁; linarith

end MWG.EquilibriumTime

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Efficiency of the golden rule in the multisector model (MWG Section 20.E, p. 758)

MWG, Chapter 20, p. 758: in the `(N + 1)`-sector technology of Example 20.C.4, consumption
`G(k, k')` from capital `k ∈ ℝ^N` and investment `k'`, "we could also prove that the golden
rule path is efficient". At the golden rule `k̂` the interest rate is zero, so the supporting
prices of capital are constant: `∇₁G(k̂, k̂) = q = -∇₂G(k̂, k̂)` (`golden_rule_multisector`,
(20.E.1)).

`golden_rule_multisector_efficient`: if `G` lies below its tangent plane at `(k̂, k̂)` with this
zero-interest gradient `(q, -q)` by a quadratic margin `μ ‖k - k̂‖²` (strong concavity in the
current capital stock), then no bounded feasible capital path starting at `k̂` gives consumption
at least `Ĝ = G(k̂, k̂)` in every period and more in some period: the golden rule path is
efficient. Telescoping the tangent-plane inequality gives
`∑_{t < T} (c_t - Ĝ) + μ ∑_{t < T} ‖k_t - k̂‖² ≤ q · (k̂ - k_T)`; a gain `ε > 0` forces
`‖k_T - k̂‖² ≥ ε² / (q · q)` for all later `T`, so the left side grows without bound while the
right side stays bounded.

Some strict concavity is needed: for a linear `G` the golden rule is inefficient
(`golden_rule_linear_inefficient`). A proved instance of the hypotheses:
`golden_rule_quadratic_instance`.
-/

namespace MWG.EquilibriumTime

variable {N : ℕ}

/-- **The golden rule is efficient in the multisector model** (MWG, p. 758). Let `G` be the
consumption available from capital `k` and investment `k'` on a set `A` of feasible pairs, and
let `k̂` be a golden rule with zero-interest supporting gradient `(q, -q)` and a quadratic
margin: `G(k, k') ≤ G(k̂, k̂) + q · (k - k') - μ ‖k - k̂‖²` on `A`, `μ > 0`. If a bounded capital
path with `k_0 = k̂` and `(k_t, k_{t+1}) ∈ A` gives consumption `G(k_t, k_{t+1}) ≥ G(k̂, k̂)` in
every period, then it gives exactly `G(k̂, k̂)` in every period. -/
theorem golden_rule_multisector_efficient {G : (Fin N → ℝ) → (Fin N → ℝ) → ℝ}
    {A : Set ((Fin N → ℝ) × (Fin N → ℝ))} {khat q : Fin N → ℝ} {μ B : ℝ} (hμ : 0 < μ)
    (hsupp : ∀ x ∈ A, G x.1 x.2 ≤ G khat khat + q ⬝ᵥ (x.1 - x.2)
      - μ * ((x.1 - khat) ⬝ᵥ (x.1 - khat)))
    {k : ℕ → Fin N → ℝ} (hk0 : k 0 = khat) (hA : ∀ t, (k t, k (t + 1)) ∈ A)
    (hB : ∀ t i, |k t i| ≤ B) (hge : ∀ t, G khat khat ≤ G (k t) (k (t + 1))) :
    ∀ t, G (k t) (k (t + 1)) = G khat khat := by
  by_contra hne
  push Not at hne
  obtain ⟨s, hs⟩ := hne
  set ε := G (k s) (k (s + 1)) - G khat khat with hε
  have hεpos : 0 < ε := by have := hge s; rw [hε]; exact sub_pos.2 (lt_of_le_of_ne this hs.symm)
  set d : ℕ → ℝ := fun t => (k t - khat) ⬝ᵥ (k t - khat) with hd
  have hd0 : ∀ t, 0 ≤ d t := fun t => by
    simp only [hd, dotProduct, ← sq]; exact Finset.sum_nonneg fun i _ => sq_nonneg _
  -- telescoping
  have htel : ∀ T, ∑ t ∈ Finset.range T, (G (k t) (k (t + 1)) - G khat khat)
      + μ * ∑ t ∈ Finset.range T, d t ≤ q ⬝ᵥ (khat - k T) := by
    intro T
    induction T with
    | zero => simp [hk0]
    | succ T ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, mul_add]
      have h := hsupp _ (hA T)
      simp only at h
      have e : q ⬝ᵥ (khat - k (T + 1)) = q ⬝ᵥ (khat - k T) + q ⬝ᵥ (k T - k (T + 1)) := by
        rw [← dotProduct_add]; congr 1; abel
      rw [e]
      simp only [hd] at ih ⊢
      linarith
  -- the gain forces the capital stock to stay away from `k̂`
  have hgain : ∀ T, s < T → ε ≤ q ⬝ᵥ (khat - k T) - μ * ∑ t ∈ Finset.range T, d t := by
    intro T hT
    have h := htel T
    have hsum : ε ≤ ∑ t ∈ Finset.range T, (G (k t) (k (t + 1)) - G khat khat) := by
      rw [hε]
      exact Finset.single_le_sum (f := fun t => G (k t) (k (t + 1)) - G khat khat)
        (fun t _ => sub_nonneg.2 (hge t)) (Finset.mem_range.2 hT)
    linarith
  have hqq : 0 < q ⬝ᵥ q := by
    have h := hgain (s + 1) (by omega)
    have hS : 0 ≤ μ * ∑ t ∈ Finset.range (s + 1), d t :=
      mul_nonneg hμ.le (Finset.sum_nonneg fun t _ => hd0 t)
    by_contra hle
    push Not at hle
    have hq0 : q = 0 := by
      funext i
      have : q i ^ 2 ≤ q ⬝ᵥ q := by
        simp only [dotProduct, ← sq]
        exact Finset.single_le_sum (fun j _ => sq_nonneg (q j)) (Finset.mem_univ i)
      have : q i ^ 2 = 0 := le_antisymm (by linarith) (sq_nonneg _)
      simpa using this
    rw [hq0, zero_dotProduct] at h
    linarith
  set a := ε ^ 2 / (q ⬝ᵥ q) with ha
  have hapos : 0 < a := by rw [ha]; positivity
  have hdlow : ∀ T, s < T → a ≤ d T := by
    intro T hT
    have h1 : ε ≤ q ⬝ᵥ (khat - k T) := by
      have := hgain T hT
      have : 0 ≤ μ * ∑ t ∈ Finset.range T, d t :=
        mul_nonneg hμ.le (Finset.sum_nonneg fun t _ => hd0 t)
      linarith
    -- Cauchy-Schwarz: `(q · v)² ≤ (q · q)(v · v)` with `v = k̂ - k_T`
    have hcs : (q ⬝ᵥ (khat - k T)) ^ 2 ≤ (q ⬝ᵥ q) * d T := by
      have e : d T = (khat - k T) ⬝ᵥ (khat - k T) := by
        simp only [hd, dotProduct, Pi.sub_apply]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [e]
      have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ q (khat - k T)
      simpa only [dotProduct, ← sq] using this
    rw [ha, div_le_iff₀ hqq]
    nlinarith
  -- the right side is bounded
  set C := ∑ i, |q i| * (|khat i| + B) with hC
  have hbd : ∀ T, q ⬝ᵥ (khat - k T) ≤ C := by
    intro T
    simp only [dotProduct, hC, Pi.sub_apply]
    refine Finset.sum_le_sum fun i _ => ?_
    calc q i * (khat i - k T i) ≤ |q i * (khat i - k T i)| := le_abs_self _
      _ = |q i| * |khat i - k T i| := abs_mul _ _
      _ ≤ |q i| * (|khat i| + B) := mul_le_mul_of_nonneg_left
          ((abs_sub _ _).trans (by linarith [hB T i])) (abs_nonneg _)
  -- the sum of the `d_t` grows without bound
  obtain ⟨n, hn⟩ := exists_nat_gt (C / (μ * a))
  have hgrow : ∀ m : ℕ, (m : ℝ) * a ≤ ∑ t ∈ Finset.range (s + 1 + m), d t := by
    intro m
    induction m with
    | zero =>
      rw [Nat.cast_zero, zero_mul, add_zero]
      exact Finset.sum_nonneg fun t _ => hd0 t
    | succ m ih =>
      rw [show s + 1 + (m + 1) = s + 1 + m + 1 by omega, Finset.sum_range_succ]
      have := hdlow (s + 1 + m) (by omega)
      push_cast
      linarith
  have h := hgain (s + 1 + n) (by omega)
  have hb := hbd (s + 1 + n)
  have hg := hgrow n
  have : C < μ * ((n : ℝ) * a) := by
    rw [div_lt_iff₀ (mul_pos hμ hapos)] at hn
    nlinarith
  nlinarith

/-- Some strict concavity is needed (MWG, p. 758): for the linear technology
`G(k, k') = k - k'` (one capital good) the golden rule `k̂ = 1` is inefficient: investing `1/2`
less in period 0 gives consumption `1/2` instead of `0` then and `0` afterwards. -/
theorem golden_rule_linear_inefficient :
    let k : ℕ → ℝ := fun t => if t = 0 then 1 else 1 / 2
    k 0 = 1 ∧ (∀ t, (1 : ℝ) - 1 ≤ k t - k (t + 1)) ∧ (1 : ℝ) - 1 < k 0 - k 1 := by
  intro k
  refine ⟨rfl, fun t => ?_, by simp [k]; norm_num⟩
  rcases t with _ | t
  · simp [k]; norm_num
  · simp [k]

/-- A proved instance of the hypotheses of `golden_rule_multisector_efficient`:
`G(k, k') = 1 · (k - k') - ‖k - 1‖²` with golden rule `k̂ = 1`, `q = 1`, `μ = 1`. -/
theorem golden_rule_quadratic_instance :
    ∀ x ∈ (Set.univ : Set ((Fin N → ℝ) × (Fin N → ℝ))),
      (fun k k' : Fin N → ℝ => (fun _ => (1 : ℝ)) ⬝ᵥ (k - k') - (k - fun _ => 1) ⬝ᵥ
          (k - fun _ => 1)) x.1 x.2
        ≤ (fun k k' : Fin N → ℝ => (fun _ => (1 : ℝ)) ⬝ᵥ (k - k') - (k - fun _ => 1) ⬝ᵥ
          (k - fun _ => 1)) (fun _ => 1) (fun _ => 1)
          + (fun _ => (1 : ℝ)) ⬝ᵥ (x.1 - x.2) - 1 * ((x.1 - fun _ => 1) ⬝ᵥ (x.1 - fun _ => 1)) :=
  fun x _ => by simp

end MWG.EquilibriumTime

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Dynamics (MWG Section 20.F, pp. 759-765)

MWG, Chapter 20, Section 20.F and Exercises 20.F.1-20.F.5 (p. 785). One capital good.

* Steady states are the fixed points of the policy function (`steady_state_iff_fixed`).
* Figures 20.F.1-20.F.2: an increasing continuous policy function on an interval drives every path
  to a steady state, and to the unique one if it is unique (`monotone_policy_converges`,
  `monotone_policy_converges_unique`); Figure 20.F.3, a two-cycle (`two_cycle_example`);
  Figure 20.F.4, a three-cycle (`three_cycle_example`).
* Low discount of time: the derivative of the policy function (`policy_deriv`), and the
  correction that the printed bound on `|ψ'|` goes the other way
  (`policy_deriv_bound_printed_false`, `policy_deriv_lower_bound`); **Exercise 20.F.2**
  (`exercise_20_F_2`, true on `ℝ_+`, false on `ℝ_{++}`: `exercise_20_F_2_false`); footnote 26
  (`footnote_20_26`); the turnpike intuition that a cycle is beaten by its mean
  (`cycle_beaten_by_mean`).
* Cross derivatives of uniform sign: increasing differences make the policy increasing
  (`policy_mono_of_increasing_differences`, `increasing_differences_of_cross_pos`) and decreasing
  for the opposite sign (`policy_anti_of_decreasing_differences`); **Exercise 20.F.3**
  (`exercise_20_F_3_rs`, `exercise_20_F_3_adjustment`).
* **Example 20.F.1** and **Exercises 20.F.4-20.F.5** (`example_20_F_1`, `exercise_20_F_4`,
  `exercise_20_F_5`).
* **Exercise 20.F.1**: the Engel-curve property of the hinted utility (`exercise_20_F_1_engel`).

OPEN: the period-three-implies-chaos theorem, the Boldrin-Montrucchio theorem and the turnpike
theorem (cited, not stated precisely in MWG), and the monotonicity and concavity parts of
Exercise 20.F.1.
-/

open Filter Topology

namespace MWG.EquilibriumTime

/-! ### Steady states and monotone dynamics -/

/-- **Steady states are fixed points of the policy function** (MWG, p. 760): if `ψ` is the policy
function (the first-period choice of every optimal path) and an optimal path from `k` exists, the
constant path at `k` is optimal if and only if `ψ(k) = k`. -/
theorem steady_state_iff_fixed {A : Set (ℝ × ℝ)} {δ : ℝ} (hδ : 0 < δ) {u : ℝ × ℝ → ℝ} {ψ : ℝ → ℝ}
    (hψ : ∀ a k', OptimalFrom A δ u a k' → k' 1 = ψ a) {k : ℝ} {kp : ℕ → ℝ}
    (hopt : OptimalFrom A δ u k kp) :
    OptimalFrom A δ u k (fun _ => k) ↔ ψ k = k := by
  constructor
  · intro h; exact (hψ k _ h).symm
  · intro hfix
    have hpath : ∀ t, kp t = k := by
      intro t
      induction t with
      | zero => exact hopt.1.1
      | succ t ih => rw [policy_20_D_10 hδ hopt hψ t, ih, hfix]
    have : kp = fun _ => k := funext hpath
    rw [← this]; exact hopt

/-- **Figure 20.F.2** (MWG, p. 760): if the policy function is nondecreasing and continuous and
maps `[a, b]` into itself, the path `k_{t+1} = ψ(k_t)` from any `k₀ ∈ [a, b]` converges
(monotonically) to a steady state. -/
theorem monotone_policy_converges {ψ : ℝ → ℝ} {a b : ℝ} (hmono : MonotoneOn ψ (Set.Icc a b))
    (hcont : ContinuousOn ψ (Set.Icc a b)) (hmaps : Set.MapsTo ψ (Set.Icc a b) (Set.Icc a b))
    {k₀ : ℝ} (hk₀ : k₀ ∈ Set.Icc a b) :
    ∃ ks ∈ Set.Icc a b, ψ ks = ks ∧ Tendsto (fun t => ψ^[t] k₀) atTop (𝓝 ks) := by
  set k : ℕ → ℝ := fun t => ψ^[t] k₀ with hk
  have hmem : ∀ t, k t ∈ Set.Icc a b := by
    intro t
    induction t with
    | zero => exact hk₀
    | succ t ih =>
      simp only [hk, Function.iterate_succ_apply'] at ih ⊢
      exact hmaps ih
  have hsucc : ∀ t, k (t + 1) = ψ (k t) := fun t => by
    simp only [hk, Function.iterate_succ_apply']
  -- the path is monotone
  have hlim : ∃ ks, Tendsto k atTop (𝓝 ks) := by
    rcases le_total (k 0) (k 1) with h01 | h10
    · have hm : Monotone k := by
        refine monotone_nat_of_le_succ fun t => ?_
        induction t with
        | zero => exact h01
        | succ t ih =>
          calc k (t + 1) = ψ (k t) := hsucc t
            _ ≤ ψ (k (t + 1)) := hmono (hmem t) (hmem (t + 1)) ih
            _ = k (t + 1 + 1) := (hsucc (t + 1)).symm
      exact ⟨_, tendsto_atTop_ciSup hm ⟨b, by rintro _ ⟨t, rfl⟩; exact (hmem t).2⟩⟩
    · have ha : Antitone k := by
        refine antitone_nat_of_succ_le fun t => ?_
        induction t with
        | zero => exact h10
        | succ t ih =>
          calc k (t + 1 + 1) = ψ (k (t + 1)) := hsucc (t + 1)
            _ ≤ ψ (k t) := hmono (hmem (t + 1)) (hmem t) ih
            _ = k (t + 1) := (hsucc t).symm
      exact ⟨_, tendsto_atTop_ciInf ha ⟨a, by rintro _ ⟨t, rfl⟩; exact (hmem t).1⟩⟩
  obtain ⟨ks, hks⟩ := hlim
  have hksmem : ks ∈ Set.Icc a b :=
    isClosed_Icc.mem_of_tendsto hks (Eventually.of_forall hmem)
  refine ⟨ks, hksmem, ?_, hks⟩
  have h1 : Tendsto (fun t => k (t + 1)) atTop (𝓝 ks) := hks.comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun t => ψ (k t)) atTop (𝓝 (ψ ks)) :=
    ((hcont ks hksmem).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hks, Eventually.of_forall hmem⟩))
  exact (tendsto_nhds_unique (h1.congr hsucc) h2).symm

/-- **Figure 20.F.1** (MWG, p. 760): with a single steady state, it is globally stable. -/
theorem monotone_policy_converges_unique {ψ : ℝ → ℝ} {a b ks : ℝ}
    (hmono : MonotoneOn ψ (Set.Icc a b)) (hcont : ContinuousOn ψ (Set.Icc a b))
    (hmaps : Set.MapsTo ψ (Set.Icc a b) (Set.Icc a b))
    (huniq : ∀ x ∈ Set.Icc a b, ψ x = x → x = ks) {k₀ : ℝ} (hk₀ : k₀ ∈ Set.Icc a b) :
    Tendsto (fun t => ψ^[t] k₀) atTop (𝓝 ks) := by
  obtain ⟨k', hk', hfix, hlim⟩ := monotone_policy_converges hmono hcont hmaps hk₀
  rwa [huniq k' hk' hfix] at hlim

/-- **Figure 20.F.3** (MWG, p. 760): a decreasing policy function with a single steady state and a
cycle of period two: `ψ(k) = 1 - k` on `[0, 1]`, steady state `1/2`, cycle `0 → 1 → 0`. -/
theorem two_cycle_example :
    let ψ : ℝ → ℝ := fun k => 1 - k
    (∀ k, ψ k = k ↔ k = 1 / 2) ∧ ψ 0 = 1 ∧ ψ 1 = 0 := by
  intro ψ
  refine ⟨fun k => ⟨fun h => by simp only [ψ] at h; linarith, fun h => by
    simp only [ψ, h]; norm_num⟩, by simp [ψ], by simp [ψ]⟩

/-- **Figure 20.F.4** (MWG, p. 760): a continuous policy function with a cycle of period three:
`ψ(k) = 1 + k` on `[0, 1]`, `ψ(k) = 4 - 2k` on `[1, 2]`, with `0 → 1 → 2 → 0`. (That a cycle of
period three implies chaos is a cited theorem, OPEN here.) -/
theorem three_cycle_example :
    let ψ : ℝ → ℝ := fun k => if k ≤ 1 then 1 + k else 4 - 2 * k
    Continuous ψ ∧ ψ 0 = 1 ∧ ψ 1 = 2 ∧ ψ 2 = 0 := by
  intro ψ
  refine ⟨?_, by norm_num [ψ], by norm_num [ψ], by norm_num [ψ]⟩
  exact Continuous.if_le (by fun_prop) (by fun_prop) continuous_id continuous_const
    (fun x hx => by rw [hx]; norm_num)

/-! ### Low discount of time -/

/-- **The derivative of the policy function** (MWG, p. 762): differentiating the first-order
condition (20.F.3) `∇₂u(k, ψ(k)) + δ V'(ψ(k)) = 0`: if `∇₂u(k, ψ(k)) + δ V'(ψ(k))` vanishes
identically near `k` and its total derivative is `∇²₂₁u + (∇²₂₂u + δ V'') ψ'(k)`, then
`ψ'(k) = -∇²₂₁u / (∇²₂₂u + δ V'')`. -/
theorem policy_deriv {u21 u22 V2 δ dψ : ℝ} (hden : u22 + δ * V2 ≠ 0)
    (hfoc : u21 + (u22 + δ * V2) * dψ = 0) : dψ = -u21 / (u22 + δ * V2) := by
  field_simp; linarith

/-- **Correction to the bound on `|ψ'|`** (MWG, p. 762): from `∇²₂₂u ≤ 0` and
`δ ∇²₁₁u ≤ δ V'' ≤ 0` it does **not** follow that `|ψ'| ≤ |∇²₂₁u / (∇²₂₂u + δ∇²₁₁u)|`: with
`∇²₂₁u = 1`, `∇²₂₂u = -1`, `∇²₁₁u = -4` (so that `(∇²₂₁u)² ≤ ∇²₁₁u ∇²₂₂u`), `V'' = 0` and
`δ = 1/2`, `ψ' = 1` while the printed bound is `1/3`. -/
theorem policy_deriv_bound_printed_false :
    let u21 : ℝ := 1
    let u22 : ℝ := -1
    let u11 : ℝ := -4
    let V2 : ℝ := 0
    let δ : ℝ := 1 / 2
    u22 ≤ 0 ∧ δ * u11 ≤ δ * V2 ∧ δ * V2 ≤ 0 ∧ u21 ^ 2 ≤ u11 * u22 ∧
      ¬ |-u21 / (u22 + δ * V2)| ≤ |u21 / (u22 + δ * u11)| := by
  intro u21 u22 u11 V2 δ
  norm_num [u21, u22, u11, V2, δ, abs_of_pos, abs_of_neg]

/-- **The correct direction** (MWG, p. 762): under `∇²₂₂u ≤ 0` and `δ∇²₁₁u ≤ δ V'' ≤ 0` (with
nonzero denominators), `|ψ'| ≥ |∇²₂₁u / (∇²₂₂u + δ∇²₁₁u)|`, and `|ψ'| ≤ |∇²₂₁u / ∇²₂₂u|`. -/
theorem policy_deriv_lower_bound {u21 u22 u11 V2 δ : ℝ} (h22 : u22 < 0) (h1 : δ * u11 ≤ δ * V2)
    (h2 : δ * V2 ≤ 0) :
    |u21 / (u22 + δ * u11)| ≤ |-u21 / (u22 + δ * V2)| ∧
      |-u21 / (u22 + δ * V2)| ≤ |u21 / u22| := by
  have hd1 : u22 + δ * u11 < 0 := by linarith
  have hd2 : u22 + δ * V2 < 0 := by linarith
  rw [abs_div, abs_div, abs_div, abs_neg, abs_of_neg hd1, abs_of_neg hd2, abs_of_neg h22]
  constructor
  · exact div_le_div_of_nonneg_left (abs_nonneg _) (by linarith) (by linarith)
  · exact div_le_div_of_nonneg_left (abs_nonneg _) (by linarith) (by linarith)

/-- **Exercise 20.F.2** (MWG, p. 785), on `ℝ_+`: a contraction `ψ : ℝ_+ → ℝ_+` has a unique steady
state, and every path `k_{t+1} = ψ(k_t)` converges to it (global stability). -/
theorem exercise_20_F_2 {ψ : ℝ → ℝ} (hmaps : ∀ k, 0 ≤ k → 0 ≤ ψ k) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1) (hlip : ∀ x y, 0 ≤ x → 0 ≤ y → |ψ x - ψ y| ≤ θ * |x - y|) :
    ∃ ks, 0 ≤ ks ∧ ψ ks = ks ∧ (∀ x, 0 ≤ x → ψ x = x → x = ks) ∧
      ∀ k₀, 0 ≤ k₀ → Tendsto (fun t => ψ^[t] k₀) atTop (𝓝 ks) := by
  -- the restriction to the complete space `ℝ_+`
  set g : Set.Ici (0 : ℝ) → Set.Ici (0 : ℝ) := fun x => ⟨ψ x, hmaps x x.2⟩ with hg
  have hcon : ContractingWith ⟨θ, hθ0⟩ g := by
    refine ⟨by exact_mod_cast hθ1, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
    simp only [hg, Subtype.dist_eq, Real.dist_eq]
    exact hlip x y x.2 y.2
  have : CompleteSpace (Set.Ici (0 : ℝ)) := isClosed_Ici.completeSpace_coe
  set ks := ContractingWith.fixedPoint g hcon with hks
  have hfix : g ks = ks := ContractingWith.fixedPoint_isFixedPt hcon
  refine ⟨ks, ks.2, congrArg Subtype.val hfix, fun x hx hxfix => ?_, fun k₀ hk₀ => ?_⟩
  · have : g ⟨x, hx⟩ = ⟨x, hx⟩ := Subtype.ext hxfix
    exact congrArg Subtype.val (ContractingWith.fixedPoint_unique hcon this)
  · have h := ContractingWith.tendsto_iterate_fixedPoint hcon ⟨k₀, hk₀⟩
    have hiter : ∀ t, ((g^[t] ⟨k₀, hk₀⟩ : Set.Ici (0 : ℝ)) : ℝ) = ψ^[t] k₀ := by
      intro t
      induction t with
      | zero => rfl
      | succ t ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
    have := (continuous_subtype_val.tendsto _).comp h
    exact this.congr fun t => hiter t

/-- **Correction to Exercise 20.F.2** (MWG, p. 785): on `ℝ_{++}` a contraction need not have a
steady state: `ψ(k) = k/2` maps `(0, ∞)` into itself with Lipschitz constant `1/2` and has no
fixed point there. -/
theorem exercise_20_F_2_false :
    (∀ k : ℝ, 0 < k → 0 < k / 2) ∧ (∀ x y : ℝ, |x / 2 - y / 2| ≤ 1 / 2 * |x - y|) ∧
      ∀ k : ℝ, 0 < k → k / 2 ≠ k := by
  refine ⟨fun k hk => by positivity, fun x y => ?_, fun k hk h => by linarith⟩
  rw [← sub_div, abs_div, abs_two]; linarith [abs_nonneg (x - y)]

/-- **Footnote 26** (MWG, p. 763): a contraction need not be monotone and convergence may be
cyclical: `ψ(k) = 1 - k/2` on `[0, 2]` is decreasing with Lipschitz constant `1/2`; the deviations
from the steady state `2/3` alternate in sign and dampen. -/
theorem footnote_20_26 (k : ℝ) (t : ℕ) :
    (fun x : ℝ => 1 - x / 2)^[t] k - 2 / 3 = (-1 / 2) ^ t * (k - 2 / 3) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply', pow_succ]
    have : (fun x : ℝ => 1 - x / 2)^[t] k = (-1 / 2) ^ t * (k - 2 / 3) + 2 / 3 := by linarith
    rw [this]
    ring

/-- **The turnpike intuition** (MWG, p. 763): for a strictly concave `u` on a convex `A`, a
nonconstant cyclical path of period `P` has average utility over the cycle strictly below
`u(k̄, k̄)`, where `k̄` is the mean capital over the cycle. -/
theorem cycle_beaten_by_mean {A : Set (ℝ × ℝ)} {u : ℝ × ℝ → ℝ} (hu : StrictConcaveOn ℝ A u)
    {P : ℕ} (hP : 0 < P) {k : ℕ → ℝ} (hper : k P = k 0) (hA : ∀ t < P, (k t, k (t + 1)) ∈ A)
    (hnc : ∃ s < P, ∃ r < P, (k s, k (s + 1)) ≠ (k r, k (r + 1))) :
    (1 / P : ℝ) * ∑ t ∈ Finset.range P, u (k t, k (t + 1))
      < u ((1 / P : ℝ) * ∑ t ∈ Finset.range P, k t, (1 / P : ℝ) * ∑ t ∈ Finset.range P, k t) := by
  have hPr : (0 : ℝ) < P := by exact_mod_cast hP
  have hshift : ∑ t ∈ Finset.range P, k (t + 1) = ∑ t ∈ Finset.range P, k t := by
    obtain ⟨P', rfl⟩ : ∃ P', P = P' + 1 := ⟨P - 1, by omega⟩
    rw [Finset.sum_range_succ, Finset.sum_range_succ' (fun t => k t), hper]
  have hj := hu.lt_map_sum (t := Finset.range P) (w := fun _ => (1 / P : ℝ))
    (p := fun t => (k t, k (t + 1))) (fun _ _ => by positivity)
    (by simp; field_simp) (fun t ht => hA t (Finset.mem_range.1 ht))
    (by obtain ⟨s, hs, r, hr, hne⟩ := hnc
        exact ⟨s, Finset.mem_range.2 hs, r, Finset.mem_range.2 hr, hne⟩)
  have hsum : ∑ t ∈ Finset.range P, (1 / P : ℝ) • (k t, k (t + 1))
      = ((1 / P : ℝ) * ∑ t ∈ Finset.range P, k t, (1 / P : ℝ) * ∑ t ∈ Finset.range P, k t) := by
    rw [← Finset.smul_sum]
    refine Prod.ext ?_ ?_
    · simp only [Prod.smul_fst, Prod.fst_sum, smul_eq_mul]
    · simp only [Prod.smul_snd, Prod.snd_sum, smul_eq_mul, hshift]
  rw [hsum] at hj
  simpa [Finset.mul_sum, smul_eq_mul] using hj

/-! ### Cross derivatives of uniform sign -/

/-- `u` has **strictly increasing differences**: `u(k₂, ·) - u(k₁, ·)` is strictly increasing for
`k₁ < k₂` (the integrated form of `∇²₁₂u > 0`). -/
def StrictIncDiff (u : ℝ → ℝ → ℝ) : Prop :=
  ∀ k₁ k₂ a₁ a₂, k₁ < k₂ → a₁ < a₂ → u k₂ a₁ - u k₁ a₁ < u k₂ a₂ - u k₁ a₂

/-- **The cross-derivative condition implies increasing differences**: if `∇₂u(k, k')` exists
everywhere and `k ↦ ∇₂u(k, k')` has derivative `∇²₁₂u(k, k') > 0`, then `u` has strictly
increasing differences. -/
theorem increasing_differences_of_cross_pos {u u2 u12 : ℝ → ℝ → ℝ}
    (h2 : ∀ k a, HasDerivAt (fun a' => u k a') (u2 k a) a)
    (h12 : ∀ k a, HasDerivAt (fun k' => u2 k' a) (u12 k a) k) (hpos : ∀ k a, 0 < u12 k a) :
    StrictIncDiff u := by
  intro k₁ k₂ a₁ a₂ hk ha
  -- `a ↦ u k₂ a - u k₁ a` has derivative `u2 k₂ a - u2 k₁ a > 0`
  have hder : ∀ a, 0 < u2 k₂ a - u2 k₁ a := by
    intro a
    obtain ⟨c, _, hc⟩ := exists_hasDerivAt_eq_slope (fun k' => u2 k' a) (fun k' => u12 k' a) hk
      (fun x _ => (h12 x a).continuousAt.continuousWithinAt) (fun x _ => h12 x a)
    have := hpos c a
    rw [hc] at this
    exact (div_pos_iff_of_pos_right (by linarith)).1 this |> fun h => by linarith
  obtain ⟨c, _, hc⟩ := exists_hasDerivAt_eq_slope (fun a => u k₂ a - u k₁ a)
    (fun a => u2 k₂ a - u2 k₁ a) ha
    (fun x _ => ((h2 k₂ x).sub (h2 k₁ x)).continuousAt.continuousWithinAt)
    (fun x _ => (h2 k₂ x).sub (h2 k₁ x))
  have := hder c
  rw [hc] at this
  have h' := (div_pos_iff_of_pos_right (by linarith : (0 : ℝ) < a₂ - a₁)).1 this
  linarith

/-- **Under strictly increasing differences the policy function is increasing** (MWG, pp. 763-764,
Figure 20.F.6): if `ψ(k)` maximizes `u(k, k') + δ V(k')` over a common feasible set, then
`k₁ < k₂` implies `ψ(k₁) ≤ ψ(k₂)`. -/
theorem policy_mono_of_increasing_differences {u : ℝ → ℝ → ℝ} (hu : StrictIncDiff u)
    {δ : ℝ} {V : ℝ → ℝ} {S : Set ℝ} {ψ : ℝ → ℝ}
    (hψ : ∀ k, ψ k ∈ S ∧ ∀ a ∈ S, u k a + δ * V a ≤ u k (ψ k) + δ * V (ψ k))
    {k₁ k₂ : ℝ} (hk : k₁ < k₂) : ψ k₁ ≤ ψ k₂ := by
  by_contra hlt
  push Not at hlt
  have h1 := (hψ k₁).2 (ψ k₂) (hψ k₂).1
  have h2 := (hψ k₂).2 (ψ k₁) (hψ k₁).1
  have := hu k₁ k₂ (ψ k₂) (ψ k₁) hk hlt
  linarith

/-- **Cross derivative of uniform negative sign** (MWG, p. 764): with strictly decreasing
differences the policy function is decreasing. -/
theorem policy_anti_of_decreasing_differences {u : ℝ → ℝ → ℝ}
    (hu : StrictIncDiff (fun k a => -u k a)) {δ : ℝ} {V : ℝ → ℝ} {S : Set ℝ} {ψ : ℝ → ℝ}
    (hψ : ∀ k, ψ k ∈ S ∧ ∀ a ∈ S, u k a + δ * V a ≤ u k (ψ k) + δ * V (ψ k))
    {k₁ k₂ : ℝ} (hk : k₁ < k₂) : ψ k₂ ≤ ψ k₁ := by
  by_contra hlt
  push Not at hlt
  have h1 := (hψ k₁).2 (ψ k₂) (hψ k₂).1
  have h2 := (hψ k₂).2 (ψ k₁) (hψ k₁).1
  have := hu k₁ k₂ (ψ k₁) (ψ k₂) hk hlt
  simp only at this
  linarith

/-- **Exercise 20.F.3**, Ramsey-Solow (MWG, p. 785): for `u(k, k') = û(F(k) - k')`,
`∇₂u = -û'(c)` and `∇²₁₂u = -û''(c) F'(k) > 0` when `û'' < 0 < F'`. -/
theorem exercise_20_F_3_rs {uh' uh'' F F' : ℝ → ℝ} {k a : ℝ}
    (huh : HasDerivAt uh' (uh'' (F k - a)) (F k - a)) (hF : HasDerivAt F (F' k) k)
    (hneg : uh'' (F k - a) < 0) (hpos : 0 < F' k) :
    HasDerivAt (fun k' => -uh' (F k' - a)) (-(uh'' (F k - a) * F' k)) k ∧
      0 < -(uh'' (F k - a) * F' k) := by
  refine ⟨?_, by nlinarith⟩
  exact (huh.comp k (hF.sub_const a)).neg

/-- **Exercise 20.F.3**, cost of adjustment (MWG, p. 785): for
`u(k, k') = û(F(k) - k' - γ(k' - k))`, `∇₂u = -û'(c)(1 + γ'(k' - k))` and
`∇²₁₂u = -û''(c)(F'(k) + γ'(k' - k))(1 + γ'(k' - k)) + û'(c) γ''(k' - k) > 0` when `û'' < 0 < û'`,
`F' + γ' > 0`, `1 + γ' > 0` and `γ'' ≥ 0`. -/
theorem exercise_20_F_3_adjustment {uh' uh'' F F' γ γ' γ'' : ℝ → ℝ} {k a : ℝ}
    (huh : HasDerivAt uh' (uh'' (F k - a - γ (a - k))) (F k - a - γ (a - k)))
    (hF : HasDerivAt F (F' k) k) (hγ : HasDerivAt γ (γ' (a - k)) (a - k))
    (hγ' : HasDerivAt γ' (γ'' (a - k)) (a - k))
    (hneg : uh'' (F k - a - γ (a - k)) < 0) (hpos : 0 < uh' (F k - a - γ (a - k)))
    (h1 : 0 < F' k + γ' (a - k)) (h2 : 0 < 1 + γ' (a - k)) (h3 : 0 ≤ γ'' (a - k)) :
    HasDerivAt (fun k' => -uh' (F k' - a - γ (a - k')) * (1 + γ' (a - k')))
      (-(uh'' (F k - a - γ (a - k)) * (F' k + γ' (a - k))) * (1 + γ' (a - k))
        + uh' (F k - a - γ (a - k)) * γ'' (a - k)) k ∧
      0 < -(uh'' (F k - a - γ (a - k)) * (F' k + γ' (a - k))) * (1 + γ' (a - k))
        + uh' (F k - a - γ (a - k)) * γ'' (a - k) := by
  refine ⟨?_, by nlinarith [mul_nonneg hpos.le h3, mul_pos (mul_pos (neg_pos.2 hneg) h1) h2]⟩
  have hc : HasDerivAt (fun k' => F k' - a - γ (a - k')) (F' k + γ' (a - k)) k := by
    have := (hF.sub_const a).sub (hγ.comp_const_sub a k)
    convert this using 1
    ring
  have hd1 : HasDerivAt (fun k' => -uh' (F k' - a - γ (a - k')))
      (-(uh'' (F k - a - γ (a - k)) * (F' k + γ' (a - k)))) k := (huh.comp k hc).neg
  have hd2 : HasDerivAt (fun k' => 1 + γ' (a - k')) (-γ'' (a - k)) k := by
    have := (hγ'.comp_const_sub a k).const_add 1
    simpa using this
  convert hd1.mul hd2 using 1
  ring

/-! ### Example 20.F.1 and Exercises 20.F.4-20.F.5 -/

/-- **Example 20.F.1** (MWG, p. 765): with separable utility `u(k, k') = g(k) + h(k')` the
maximizer of `u(k, k') + δ V(k')` does not depend on `k` (the policy function is constant), and
any value function satisfying the Bellman equation is `g` plus a constant. -/
theorem example_20_F_1 {g h V : ℝ → ℝ} {δ : ℝ} {S : Set ℝ} {kb : ℝ}
    (hmax : ∀ a ∈ S, h a + δ * V a ≤ h kb + δ * V kb) :
    (∀ k, ∀ a ∈ S, g k + h a + δ * V a ≤ g k + h kb + δ * V kb) ∧
      ((∀ k, V k = g k + h kb + δ * V kb) → ∀ k, V k = g k + (h kb + δ * V kb)) := by
  refine ⟨fun k a ha => by linarith [hmax a ha], fun hV k => by rw [hV k]; ring⟩

/-- **Exercise 20.F.4** (MWG, p. 785), a transitory shock: with the old continuation value `V`,
the new choice `k₁` maximizes `h(k', θ) + δ V(k')`; if `h` has strictly increasing differences in
`(k', θ)` (the sign of `∂²h/∂k'∂θ` is positive), then `k₁ ≥ k̄` for `θ > 0`; with strictly
decreasing differences `k₁ ≤ k̄`. -/
theorem exercise_20_F_4 {h : ℝ → ℝ → ℝ} {V : ℝ → ℝ} {δ θ kb k₁ : ℝ} {S : Set ℝ} (hθ : 0 < θ)
    (hkb : kb ∈ S) (hk₁ : k₁ ∈ S)
    (hmax0 : ∀ a ∈ S, h a 0 + δ * V a ≤ h kb 0 + δ * V kb)
    (hmaxθ : ∀ a ∈ S, h a θ + δ * V a ≤ h k₁ θ + δ * V k₁) :
    (StrictIncDiff (fun θ' a => h a θ') → kb ≤ k₁) ∧
      (StrictIncDiff (fun θ' a => -h a θ') → k₁ ≤ kb) := by
  constructor
  · intro hd
    by_contra hlt; push Not at hlt
    have e1 := hmax0 k₁ hk₁
    have e2 := hmaxθ kb hkb
    have := hd 0 θ k₁ kb hθ hlt
    linarith
  · intro hd
    by_contra hlt; push Not at hlt
    have e1 := hmax0 k₁ hk₁
    have e2 := hmaxθ kb hkb
    have := hd 0 θ kb k₁ hθ hlt
    simp only at this
    linarith

/-- **Exercise 20.F.5** (MWG, p. 785), a permanent shock: the new value function is
`V_θ(k) = g(k, θ) + C_θ` (Example 20.F.1). If `g` has strictly increasing differences in
`(k, θ)`, then `V_θ - V` is strictly increasing, so (by increasing differences in the
continuation value) the choice under the permanent shock `k₁ᴾ` is at least the choice under the
transitory shock `k₁ᵀ`. Together with Exercise 20.F.4, `k₁ᴾ ≥ k₁ᵀ ≥ k̄`. -/
theorem exercise_20_F_5 {g h : ℝ → ℝ → ℝ} {δ θ Cθ C₀ kT kP : ℝ} (hδ : 0 < δ) (hθ : 0 < θ)
    {S : Set ℝ} (hkT : kT ∈ S) (hkP : kP ∈ S) (hg : StrictIncDiff (fun θ' k => g k θ'))
    (hmaxT : ∀ a ∈ S, h a θ + δ * (g a 0 + C₀) ≤ h kT θ + δ * (g kT 0 + C₀))
    (hmaxP : ∀ a ∈ S, h a θ + δ * (g a θ + Cθ) ≤ h kP θ + δ * (g kP θ + Cθ)) :
    kT ≤ kP := by
  by_contra hlt; push Not at hlt
  have e1 := hmaxT kP hkP
  have e2 := hmaxP kT hkT
  have := hg 0 θ kP kT hθ hlt
  nlinarith

/-! ### Exercise 20.F.1 -/

/-- **Exercise 20.F.1** (MWG, p. 785), the Engel-curve part: for
`u(x₁, x₂) = (x₁ + x₂)^{1/2} - ε[(x₁ - γ₁(x₁ + x₂))² + (x₂ - γ₂(x₁ + x₂))²]` with
`γ₁(w) + γ₂(w) = w` and `ε > 0`, on the budget line `x₁ + x₂ = w` the unique maximizer of `u` is
`(γ₁(w), γ₂(w))`. (Monotonicity and concavity for small `ε` are OPEN.) -/
theorem exercise_20_F_1_engel {γ₁ γ₂ : ℝ → ℝ} {w ε : ℝ} (hε : 0 < ε)
    (hγ : γ₁ w + γ₂ w = w) {x₁ x₂ : ℝ} (hx : x₁ + x₂ = w) :
    let u : ℝ → ℝ → ℝ := fun x₁ x₂ => Real.sqrt (x₁ + x₂)
      - ε * ((x₁ - γ₁ (x₁ + x₂)) ^ 2 + (x₂ - γ₂ (x₁ + x₂)) ^ 2)
    u x₁ x₂ ≤ u (γ₁ w) (γ₂ w) ∧ (u x₁ x₂ = u (γ₁ w) (γ₂ w) → x₁ = γ₁ w ∧ x₂ = γ₂ w) := by
  intro u
  simp only [u, hx, hγ, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    add_zero, mul_zero, sub_zero]
  refine ⟨by nlinarith [sq_nonneg (x₁ - γ₁ w), sq_nonneg (x₂ - γ₂ w)], fun h => ?_⟩
  have h0 : (x₁ - γ₁ w) ^ 2 + (x₂ - γ₂ w) ^ 2 = 0 := by
    have : ε * ((x₁ - γ₁ w) ^ 2 + (x₂ - γ₂ w) ^ 2) = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_left hε.ne'
  have h1 : (x₁ - γ₁ w) ^ 2 = 0 := by nlinarith [sq_nonneg (x₁ - γ₁ w), sq_nonneg (x₂ - γ₂ w)]
  have h2 : (x₂ - γ₂ w) ^ 2 = 0 := by nlinarith [sq_nonneg (x₁ - γ₁ w), sq_nonneg (x₂ - γ₂ w)]
  exact ⟨by nlinarith [pow_eq_zero_iff (n := 2) (two_ne_zero) |>.1 h1],
    by nlinarith [pow_eq_zero_iff (n := 2) (two_ne_zero) |>.1 h2]⟩

end MWG.EquilibriumTime

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Equilibrium with several consumers (MWG Section 20.G, pp. 765-769)

MWG, Chapter 20, Section 20.G and Exercises 20.G.1, 20.G.4, 20.G.5 (pp. 785-786).

Consumers `i : ι` (a finite type) have one-period utilities `u i`, a common discount factor `δ`,
endowment streams `ω i` and shares `θ i t ≥ 0` of period-`t` profits (`∑_i θ_{it} = 1`).

* **Definition 20.G.1** (`WalrasEqI`), with a proved instance (`walrasEqI_example`).
* **Proposition 20.G.1** (first welfare theorem, `proposition_20_G_1`).
* **Proposition 20.G.2** (the representative consumer of a Walrasian equilibrium with Negishi
  weights `η_i = 1/λ_i`, `proposition_20_G_2`), with a complete proof for interior equilibria of
  differentiable concave utilities (MWG give an intuitive argument).
* **Exercise 20.G.1** (`exercise_20_G_1`): with one good, two consumers and constant aggregate
  endowment, equilibrium consumption is stationary, prices are proportional with rate of interest
  `(1 - δ)/δ`, and each consumer consumes `(1 - δ) ∑_t δ^t ω_{it}`.
* **(20.G.6)** (`eq_20_G_6`), **Exercise 20.G.5** (`exercise_20_G_5`), and the dampening criterion
  `|dk_{t+1}/dk_t|, |dk_{t+1}/dk_{t-1}| < 1/2` (`dampening_of_small_coefficients`).

OPEN: Exercise 20.G.2 (Pareto optima equalize the marginal utilities of wealth across periods),
Exercise 20.G.3 (the Negishi equation and generic finiteness, Kehoe-Levine), Exercise 20.G.4 and
footnote 32, and the existence of robust continua of equilibria with externalities (no explicit
example is given in MWG).
-/

open Filter Topology

namespace MWG.EquilibriumTime

variable {L : ℕ} {ι : Type*} [Fintype ι]

variable (X : Set (Fin L → ℝ)) (Y : Set (ProdPlan (Fin L))) (δ : ℝ) (u : ι → (Fin L → ℝ) → ℝ)
  (ω : ι → ℕ → Fin L → ℝ) (θ : ι → ℕ → ℝ) (p : ℕ → Fin L → ℝ) (y : ℕ → ProdPlan (Fin L))
  (c : ι → ℕ → Fin L → ℝ) in
/-- **Definition 20.G.1** (MWG, pp. 765-766): a bounded production path `y`, a bounded nonnegative
price sequence `p` and consumption streams `c i` form a Walrasian equilibrium if (i) aggregate
consumption is feasible, (20.G.1), (ii) the path is myopically profit maximizing, (20.G.2), and
(iii) every consumer maximizes utility subject to the single budget constraint with wealth
`w_i = ∑_t θ_{it} π_t + ∑_t p_t · ω_{it}`, (20.G.3). (As in Definition 20.D.1, the profit and
endowment series are required to converge.) -/
structure WalrasEqI where
  /-- The production path is bounded. -/
  boundedPath : BoundedPath y
  /-- The price sequence is bounded. -/
  boundedPrices : ∃ B : ℝ, ∀ t i, |p t i| ≤ B
  /-- Prices are nonnegative. -/
  pricesNonneg : ∀ t, 0 ≤ p t
  /-- (i), (20.G.1): feasibility. -/
  feasible : ∀ t, ∑ i, c i t = netOutput y t + ∑ i, ω i t
  /-- (ii), (20.G.2): short-run profit maximization. -/
  myopic : MyopicProfitMax Y p y
  /-- Profits converge. -/
  profitSummable : Summable (periodProfit p y)
  /-- Every consumer's endowment has finite value. -/
  endowSummable : ∀ i, Summable fun t => p t ⬝ᵥ ω i t
  /-- (iii), (20.G.3): utility maximization. -/
  utilityMax : ∀ i, UtilityMax X δ (u i) p
    (∑' t, θ i t * periodProfit p y t + ∑' t, p t ⬝ᵥ ω i t) (c i)

/-- The wealth of consumer `i`. -/
noncomputable def wealthI (θ : ι → ℕ → ℝ) (p : ℕ → Fin L → ℝ) (y : ℕ → ProdPlan (Fin L))
    (ω : ι → ℕ → Fin L → ℝ) (i : ι) : ℝ :=
  ∑' t, θ i t * periodProfit p y t + ∑' t, p t ⬝ᵥ ω i t

/-- A **feasible allocation**: a production path and consumption streams in `X` with
`∑_i c'_{it} ≤ y'_{a,t-1} + y'_{bt} + ∑_i ω_{it}` (MWG, p. 766). -/
def FeasibleAlloc (X : Set (Fin L → ℝ)) (Y : Set (ProdPlan (Fin L))) (ω : ι → ℕ → Fin L → ℝ)
    (y : ℕ → ProdPlan (Fin L)) (c : ι → ℕ → Fin L → ℝ) : Prop :=
  IsProdPath Y y ∧ (∀ i t, c i t ∈ X) ∧ ∀ t, ∑ i, c i t ≤ netOutput y t + ∑ i, ω i t

/-- A stream with expenditure strictly below `w` can be improved within the budget set (strict
monotonicity, upward-closed `X ⊆ ℝ^L_+`). -/
theorem exists_better_of_slack [NeZero L] {X : Set (Fin L → ℝ)} (hX0 : X ⊆ Set.Ici 0)
    (hXup : ∀ x ∈ X, ∀ x', x ≤ x' → x' ∈ X)
    {δ : ℝ} {v : (Fin L → ℝ) → ℝ} (hv : StrictMonoOn v X) {p : ℕ → Fin L → ℝ}
    (hp : ∀ t, 0 ≤ p t) {w : ℝ} {c : ℕ → Fin L → ℝ} (hcX : ∀ t, c t ∈ X) (hb : BoundedStream c)
    (hsum : Summable fun t => p t ⬝ᵥ c t) (hlt : ∑' t, p t ⬝ᵥ c t < w)
    (hs : Summable fun t => δ ^ t * v (c t)) :
    ∃ c', InBudget X p w c' ∧ Summable (fun t => δ ^ t * v (c' t)) ∧
      discountedUtility δ v c < discountedUtility δ v c' := by
  set S := ∑' t, p t ⬝ᵥ c t
  set i : Fin L := 0
  set ε := (w - S) / (p 0 i + 1) with hε
  have hpi : 0 ≤ p 0 i := hp 0 i
  have hεpos : 0 < ε := div_pos (by linarith) (by linarith)
  have hεle : p 0 i * ε ≤ w - S := by
    rw [hε, mul_div_assoc', div_le_iff₀ (by linarith)]
    nlinarith
  set c' : ℕ → Fin L → ℝ := fun t => c t + if t = 0 then ε • Pi.single i 1 else 0 with hc'
  have hdiff : ∀ t, t ≠ 0 → c' t = c t := fun t ht => by simp [hc', ht]
  have hc'0 : c' 0 = c 0 + ε • Pi.single i 1 := by simp [hc']
  have hlt0 : c 0 < c' 0 := by rw [hc'0]; exact lt_add_of_pos_right _ (single_smul_pos hεpos i)
  have hfs : ∀ t ∉ ({0} : Finset ℕ), c' t = c t := fun t ht => hdiff t (by simpa using ht)
  refine ⟨c', ⟨fun t => ?_, ?_, fun T => ?_⟩, summable_of_finite_change _ hfs hs, ?_⟩
  · rcases eq_or_ne t 0 with rfl | ht
    · exact hXup _ (hcX 0) _ hlt0.le
    · rw [hdiff t ht]; exact hcX t
  · obtain ⟨M, hM⟩ := hb
    refine ⟨M + ε, fun t j => ?_⟩
    rcases eq_or_ne t 0 with rfl | ht
    · rw [hc'0]
      have := abs_add_smul_single_le (c 0) ε i j
      rw [abs_of_pos hεpos] at this
      linarith [hM 0 j]
    · rw [hdiff t ht]; linarith [hM t j]
  · have hpart : ∑ t ∈ Finset.range T, p t ⬝ᵥ c' t
        = ∑ t ∈ Finset.range T, p t ⬝ᵥ c t
          + ∑ t ∈ Finset.range T, if t = 0 then p 0 ⬝ᵥ (ε • Pi.single i 1) else 0 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun t _ => ?_
      rcases eq_or_ne t 0 with rfl | ht
      · simp [hc', dotProduct_add]
      · simp [hc', ht]
    have hextra : (∑ t ∈ Finset.range T, if t = 0 then p 0 ⬝ᵥ (ε • Pi.single i 1) else 0)
        ≤ p 0 i * ε := by
      rw [Finset.sum_ite_eq' (Finset.range T) 0]
      split_ifs
      · simp [dotProduct_smul, dotProduct_single, mul_comm]
      · exact mul_nonneg hpi hεpos.le
    have hS : ∑ t ∈ Finset.range T, p t ⬝ᵥ c t ≤ S :=
      hsum.sum_le_tsum _ (fun t _ => dotProduct_nonneg_of_nonneg (hp t) (hX0 (hcX t)))
    linarith
  · have hs' := summable_of_finite_change _ hfs hs
    have := discountedUtility_sub_of_finite _ hfs hs hs'
    rw [Finset.sum_singleton, pow_zero, one_mul] at this
    have hu0 : v (c 0) < v (c' 0) := hv (hcX 0) (hXup _ (hcX 0) _ hlt0.le) hlt0
    linarith

/-- **Aggregate wealth** (MWG, p. 766): with shares `θ_{it} ≥ 0` summing to one, the wealths add up
to `∑_t π_t + ∑_t p_t · ∑_i ω_{it}`. -/
theorem sum_wealthI {θ : ι → ℕ → ℝ} (hθ0 : ∀ i t, 0 ≤ θ i t) (hθ1 : ∀ t, ∑ i, θ i t = 1)
    {p : ℕ → Fin L → ℝ} {y : ℕ → ProdPlan (Fin L)} {ω : ι → ℕ → Fin L → ℝ}
    (hπ : Summable (periodProfit p y)) (hω : ∀ i, Summable fun t => p t ⬝ᵥ ω i t) :
    Summable (fun t => periodProfit p y t + p t ⬝ᵥ ∑ i, ω i t) ∧
      ∑ i, wealthI θ p y ω i = ∑' t, (periodProfit p y t + p t ⬝ᵥ ∑ i, ω i t) := by
  have hθle : ∀ i t, θ i t ≤ 1 := fun i t => by
    rw [← hθ1 t]
    exact Finset.single_le_sum (fun j _ => hθ0 j t) (Finset.mem_univ i)
  have hθπ : ∀ i, Summable fun t => θ i t * periodProfit p y t := fun i =>
    Summable.of_norm_bounded hπ.abs fun t => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hθ0 i t)]
      exact mul_le_of_le_one_left (abs_nonneg _) (hθle i t)
  have hωsum : Summable fun t => p t ⬝ᵥ ∑ i, ω i t := by
    simp_rw [dotProduct_sum]
    exact summable_sum fun i _ => hω i
  refine ⟨hπ.add hωsum, ?_⟩
  simp only [wealthI, Finset.sum_add_distrib]
  rw [← Summable.tsum_finsetSum (fun i _ => hθπ i), ← Summable.tsum_finsetSum (fun i _ => hω i),
    hπ.tsum_add hωsum]
  congr 1
  · refine tsum_congr fun t => ?_
    rw [← Finset.sum_mul, hθ1 t, one_mul]
  · refine tsum_congr fun t => ?_
    rw [dotProduct_sum]

/-- **Proposition 20.G.1** (MWG, p. 766), the first welfare theorem: a Walrasian equilibrium
allocation is Pareto optimal. No feasible allocation (with bounded consumption streams whose
utility series converge) makes every consumer at least as well off and one strictly better off.
Hypotheses: `X ⊆ ℝ^L_+` upward closed, strictly increasing one-period utilities, `0 ∈ Y`,
truncation, nonnegative endowments, and nonnegative shares summing to one. -/
theorem proposition_20_G_1 [NeZero L] {X : Set (Fin L → ℝ)} (hX0 : X ⊆ Set.Ici 0)
    (hXup : ∀ x ∈ X, ∀ x', x ≤ x' → x' ∈ X) {Y : Set (ProdPlan (Fin L))}
    (h0 : (0 : ProdPlan (Fin L)) ∈ Y) (htr : ∀ z ∈ Y, (z.1, 0) ∈ Y) {δ : ℝ}
    {u : ι → (Fin L → ℝ) → ℝ} (hu : ∀ i, StrictMonoOn (u i) X) {ω : ι → ℕ → Fin L → ℝ}
    (hω0 : ∀ i t, 0 ≤ ω i t) {θ : ι → ℕ → ℝ} (hθ0 : ∀ i t, 0 ≤ θ i t)
    (hθ1 : ∀ t, ∑ i, θ i t = 1) {p : ℕ → Fin L → ℝ} {y : ℕ → ProdPlan (Fin L)}
    {c : ι → ℕ → Fin L → ℝ} (he : WalrasEqI X Y δ u ω θ p y c) :
    ¬ ∃ y' c', FeasibleAlloc X Y ω y' c' ∧ (∀ i, BoundedStream (c' i)) ∧
      (∀ i, Summable fun t => δ ^ t * u i (c' i t)) ∧
      (∀ i, discountedUtility δ (u i) (c i) ≤ discountedUtility δ (u i) (c' i)) ∧
      ∃ j, discountedUtility δ (u j) (c j) < discountedUtility δ (u j) (c' j) := by
  rintro ⟨y', c', ⟨hpath', hcX', hfeas'⟩, hb', hs', hge, j, hj⟩
  obtain ⟨hWs, hW⟩ := sum_wealthI hθ0 hθ1 he.profitSummable he.endowSummable
  set W := ∑' t, (periodProfit p y t + p t ⬝ᵥ ∑ i, ω i t)
  have hp := he.pricesNonneg
  have hπ0 : ∀ t, 0 ≤ periodProfit p y t := fun t => by
    have := he.myopic.2 t 0 h0; simpa [planValue] using this
  have hnn : ∀ t, 0 ≤ periodProfit p y t + p t ⬝ᵥ ∑ i, ω i t := fun t =>
    add_nonneg (hπ0 t) (dotProduct_nonneg_of_nonneg (hp t)
      (Finset.sum_nonneg fun i _ => hω0 i t))
  -- the aggregate value of the new consumptions is at most `W` at every horizon
  have hagg : ∀ T, ∑ t ∈ Finset.range T, ∑ i, p t ⬝ᵥ c' i t ≤ W := by
    intro T
    rcases T with _ | T
    · simpa using tsum_nonneg hnn
    have h1 := sum_value_le_of_myopic htr he.myopic hpath' T
    have h2 := sum_value_netOutput p y T
    have h3 : ∑ t ∈ Finset.range (T + 1), (periodProfit p y t + p t ⬝ᵥ ∑ i, ω i t) ≤ W :=
      hWs.sum_le_tsum _ (fun t _ => hnn t)
    have h4 : ∀ t, ∑ i, p t ⬝ᵥ c' i t ≤ p t ⬝ᵥ netOutput y' t + p t ⬝ᵥ ∑ i, ω i t := by
      intro t
      rw [← dotProduct_sum, ← dotProduct_add]
      exact dotProduct_le_dotProduct_of_nonneg_left (hfeas' t) (hp t)
    have h5 := Finset.sum_le_sum fun t (_ : t ∈ Finset.range (T + 1)) => h4 t
    rw [Finset.sum_add_distrib] at h5
    rw [Finset.sum_add_distrib] at h3
    linarith
  have hci0 : ∀ i t, 0 ≤ p t ⬝ᵥ c' i t := fun i t =>
    dotProduct_nonneg_of_nonneg (hp t) (hX0 (hcX' i t))
  -- every consumer's expenditure series converges
  have hpart : ∀ i T, ∑ t ∈ Finset.range T, p t ⬝ᵥ c' i t ≤ W := by
    intro i T
    refine le_trans (Finset.sum_le_sum fun t _ => ?_) (hagg T)
    exact Finset.single_le_sum (f := fun k => p t ⬝ᵥ c' k t) (fun k _ => hci0 k t)
      (Finset.mem_univ i)
  have hsumi : ∀ i, Summable fun t => p t ⬝ᵥ c' i t := fun i =>
    summable_of_sum_range_le (hci0 i) (hpart i)
  -- the new streams cost at least the wealth, strictly so for `j`
  have hcost : ∀ i, wealthI θ p y ω i ≤ ∑' t, p t ⬝ᵥ c' i t := by
    intro i
    by_contra hlt
    push Not at hlt
    obtain ⟨c'', hbud, hs'', hbetter⟩ := exists_better_of_slack hX0 hXup (hu i) hp (hcX' i)
      (hb' i) (hsumi i) hlt (hs' i)
    have := (he.utilityMax i).2.2 c'' hbud hs''
    linarith [hge i]
  have hcostj : wealthI θ p y ω j < ∑' t, p t ⬝ᵥ c' j t := by
    by_contra hle
    push Not at hle
    have hbud : InBudget X p (wealthI θ p y ω j) (c' j) := ⟨hcX' j, hb' j, fun T =>
      ((hsumi j).sum_le_tsum _ (fun t _ => hci0 j t)).trans hle⟩
    have := (he.utilityMax j).2.2 (c' j) hbud (hs' j)
    exact absurd this (not_le.2 hj)
  have htot : ∑ i, ∑' t, p t ⬝ᵥ c' i t ≤ W := by
    rw [← Summable.tsum_finsetSum (fun i _ => hsumi i)]
    exact Real.tsum_le_of_sum_range_le (fun t => Finset.sum_nonneg fun i _ => hci0 i t)
      (fun T => by rw [Finset.sum_comm]; exact hagg T |>.trans_eq' (Finset.sum_comm))
  have hlt : ∑ i, wealthI θ p y ω i < ∑ i, ∑' t, p t ⬝ᵥ c' i t :=
    Finset.sum_lt_sum (fun i _ => hcost i) ⟨j, Finset.mem_univ _, hcostj⟩
  rw [hW] at hlt
  linarith

/-- An instance of `WalrasEqI`: two consumers with linear utility `u(x) = x₀`, one good,
`δ = 1/2`, endowments `1/2` each, the technology `{y ≤ 0}` used at inaction, prices
`p_t = (1/2)^t`, and consumption equal to the endowments. -/
theorem walrasEqI_example :
    WalrasEqI (Set.Ici 0) {y : ProdPlan (Fin 1) | y ≤ 0} (1 / 2) (fun (_ : Fin 2) x => x 0)
      (fun _ _ _ => 1 / 2) (fun _ _ => 1 / 2) (fun t _ => (1 / 2) ^ t) (fun _ => 0)
      (fun _ _ _ => 1 / 2) := by
  have hπ : ∀ t, periodProfit (fun t (_ : Fin 1) => ((1 : ℝ) / 2) ^ t)
      (fun _ => (0 : ProdPlan (Fin 1))) t = 0 := fun t => by simp [periodProfit, planValue]
  have hg := summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  refine ⟨⟨0, fun t i => by simp⟩, ⟨1, fun t i => ?_⟩, fun t i => by positivity, fun t => ?_,
    ⟨fun t => show (0 : ProdPlan (Fin 1)) ≤ 0 from le_refl _, fun t z hz => ?_⟩,
    summable_zero.congr fun t => (hπ t).symm,
    fun i => ?_, fun i => ?_⟩
  · rw [abs_of_nonneg (by positivity)]; exact pow_le_one₀ (by norm_num) (by norm_num)
  · funext k
    cases t <;> simp [netOutput]
  · rw [hπ]
    simp only [planValue, dotProduct, Finset.univ_unique, Fin.default_eq_zero,
      Finset.sum_singleton]
    have h1 : z.1 0 ≤ 0 := hz.1 0
    have h2 : z.2 0 ≤ 0 := hz.2 0
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) t,
      pow_pos (by norm_num : (0 : ℝ) < 1 / 2) (t + 1)]
  · refine (hg.mul_right (1 / 2)).congr fun t => ?_
    simp [dotProduct]
  · simp_rw [hπ, mul_zero, tsum_zero, zero_add]
    refine ⟨⟨fun t _ => by norm_num, ⟨1, fun t k => by norm_num⟩, fun T => ?_⟩, ?_,
      fun c' hc' hs' => ?_⟩
    · have hnn : ∀ t, 0 ≤ (fun t (_ : Fin 1) => ((1 : ℝ) / 2) ^ t) t ⬝ᵥ fun _ => (1 : ℝ) / 2 :=
        fun t => by simp [dotProduct]
      exact (hg.mul_right (1 / 2) |>.congr (fun t => by simp [dotProduct])).sum_le_tsum _
        (fun t _ => hnn t)
    · exact (hg.mul_right (1 / 2)).congr fun t => by simp
    · -- linear utility: the utility of a budget-feasible stream is its expenditure
      obtain ⟨hsum, hle⟩ := expenditure_summable (fun t i => by simp)
        (fun t => hc'.1 t) hc'.2.2
      unfold discountedUtility
      have e1 : ∑' t, ((1 : ℝ) / 2) ^ t * c' t 0
          = ∑' t, (fun t (_ : Fin 1) => ((1 : ℝ) / 2) ^ t) t ⬝ᵥ c' t :=
        tsum_congr fun t => by simp [dotProduct]
      have e2 : ∑' t, ((1 : ℝ) / 2) ^ t * (fun (_ : Fin 1) => (1 : ℝ) / 2) 0
          = ∑' t, (fun t (_ : Fin 1) => ((1 : ℝ) / 2) ^ t) t ⬝ᵥ fun _ => (1 : ℝ) / 2 :=
        tsum_congr fun t => by simp [dotProduct]
      rw [e1, e2]
      exact hle

/-! ### Proposition 20.G.2: the representative consumer -/

/-- The **representative one-period utility** of Proposition 20.G.2 (MWG, p. 767):
`u(x) = max ∑_i η_i u_i(x_i)` subject to `∑_i x_i ≤ x`, `x_i ≥ 0` (a supremum). -/
noncomputable def negishiUtility (η : ι → ℝ) (u : ι → (Fin L → ℝ) → ℝ) (x : Fin L → ℝ) : ℝ :=
  sSup {r | ∃ z : ι → Fin L → ℝ, (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ x ∧ r = ∑ i, η i * u i (z i)}

/-- The weighted utilities have a common supergradient `q` at an allocation where the weighted
marginal utilities `η_i ∇u_i(z⁰_i)` all equal `q`. -/
theorem weighted_supergradient {η : ι → ℝ} (hη : ∀ i, 0 < η i) {u : ι → (Fin L → ℝ) → ℝ}
    (hconc : ∀ i, ConcaveOn ℝ (Set.Ici 0) (u i)) {z0 : ι → Fin L → ℝ} (hz0 : ∀ i, 0 ≤ z0 i)
    {D : ι → (Fin L → ℝ) →L[ℝ] ℝ} (hD : ∀ i, HasFDerivAt (u i) (D i) (z0 i)) {q : Fin L → ℝ}
    (hq : ∀ i v, η i * D i v = q ⬝ᵥ v) {z : ι → Fin L → ℝ} (hz : ∀ i, 0 ≤ z i) :
    ∑ i, η i * u i (z i) ≤ ∑ i, η i * u i (z0 i) + q ⬝ᵥ (∑ i, z i - ∑ i, z0 i) := by
  have h : ∀ i, η i * u i (z i) ≤ η i * u i (z0 i) + q ⬝ᵥ (z i - z0 i) := by
    intro i
    have g := MWG.GeneralEquilibriumExamples.concave_le_fderiv (hconc i) (Set.mem_Ici.2 (hz0 i))
      (Set.mem_Ici.2 (hz i)) (hD i)
    rw [← hq i]
    nlinarith [mul_le_mul_of_nonneg_left g (hη i).le]
  calc ∑ i, η i * u i (z i) ≤ ∑ i, (η i * u i (z0 i) + q ⬝ᵥ (z i - z0 i)) :=
        Finset.sum_le_sum fun i _ => h i
    _ = _ := by
        rw [Finset.sum_add_distrib, ← dotProduct_sum, Finset.sum_sub_distrib]

/-- The representative utility at the equilibrium aggregate is the weighted sum of the
individual utilities, and it has supergradient `q` there. -/
theorem negishiUtility_props {η : ι → ℝ} (hη : ∀ i, 0 < η i) {u : ι → (Fin L → ℝ) → ℝ}
    (hconc : ∀ i, ConcaveOn ℝ (Set.Ici 0) (u i)) {z0 : ι → Fin L → ℝ} (hz0 : ∀ i, 0 ≤ z0 i)
    {D : ι → (Fin L → ℝ) →L[ℝ] ℝ} (hD : ∀ i, HasFDerivAt (u i) (D i) (z0 i)) {q : Fin L → ℝ}
    (hq0 : 0 ≤ q) (hq : ∀ i v, η i * D i v = q ⬝ᵥ v) :
    negishiUtility η u (∑ i, z0 i) = ∑ i, η i * u i (z0 i) ∧
      ∀ x, 0 ≤ x → negishiUtility η u x ≤ ∑ i, η i * u i (z0 i) + q ⬝ᵥ (x - ∑ i, z0 i) := by
  have hbound : ∀ x, ∀ r ∈ {r | ∃ z : ι → Fin L → ℝ, (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ x ∧
      r = ∑ i, η i * u i (z i)}, r ≤ ∑ i, η i * u i (z0 i) + q ⬝ᵥ (x - ∑ i, z0 i) := by
    rintro x r ⟨z, hz, hzx, rfl⟩
    have := weighted_supergradient hη hconc hz0 hD hq hz
    have hmono : q ⬝ᵥ (∑ i, z i - ∑ i, z0 i) ≤ q ⬝ᵥ (x - ∑ i, z0 i) :=
      dotProduct_le_dotProduct_of_nonneg_left (sub_le_sub_right hzx _) hq0
    linarith
  have hne : ∀ x : Fin L → ℝ, 0 ≤ x → ({r | ∃ z : ι → Fin L → ℝ, (∀ i, 0 ≤ z i) ∧
      ∑ i, z i ≤ x ∧ r = ∑ i, η i * u i (z i)} : Set ℝ).Nonempty :=
    fun x hx => ⟨_, fun _ => 0, fun _ => le_rfl, by simpa using hx, rfl⟩
  refine ⟨le_antisymm ?_ ?_, fun x hx => csSup_le (hne x hx) (hbound x)⟩
  · have := csSup_le (hne _ (Finset.sum_nonneg fun i _ => hz0 i)) (hbound (∑ i, z0 i))
    rw [sub_self, dotProduct_zero, add_zero] at this
    exact this
  · exact le_csSup ⟨_, hbound (∑ i, z0 i)⟩ ⟨z0, hz0, le_rfl, rfl⟩

/-- **Proposition 20.G.2** (MWG, p. 767): at a Walrasian equilibrium of an economy with several
consumers (common discount factor `0 < δ`), with strictly positive bounded consumption streams and
one-period utilities that are concave and strictly increasing on `ℝ^L_+`, differentiable along the
equilibrium with strictly positive marginal utilities, there are weights `η_i > 0` (the
reciprocals of the marginal utilities of wealth) such that the production path and prices form a
Walrasian equilibrium of the one-consumer economy with utility `∑ δ^t u(c_t)`, where
`u(c) = max {∑_i η_i u_i(c_i) : ∑_i c_i ≤ c}`, and aggregate endowments. Hypotheses on the
economy: nonnegative shares summing to one. -/
theorem proposition_20_G_2 [NeZero L] {Y : Set (ProdPlan (Fin L))}
    {δ : ℝ} (hδ : 0 < δ) {u : ι → (Fin L → ℝ) → ℝ}
    (hconc : ∀ i, ConcaveOn ℝ (Set.Ici 0) (u i)) (hmono : ∀ i, StrictMonoOn (u i) (Set.Ici 0))
    {ω : ι → ℕ → Fin L → ℝ} {θ : ι → ℕ → ℝ}
    (hθ0 : ∀ i t, 0 ≤ θ i t) (hθ1 : ∀ t, ∑ i, θ i t = 1) {p : ℕ → Fin L → ℝ}
    {y : ℕ → ProdPlan (Fin L)} {c : ι → ℕ → Fin L → ℝ}
    (he : WalrasEqI (Set.Ici 0) Y δ u ω θ p y c) (hcpos : ∀ i t, StrictPos (c i t))
    {D : ι → ℕ → (Fin L → ℝ) →L[ℝ] ℝ} (hD : ∀ i t, HasFDerivAt (u i) (D i t) (c i t))
    (hDpos : ∀ i t k, 0 < D i t (Pi.single k 1)) :
    ∃ η : ι → ℝ, (∀ i, 0 < η i) ∧
      (∀ t, consumption (fun t => ∑ i, ω i t) y t = ∑ i, c i t) ∧
      (∀ t, negishiUtility η u (∑ i, c i t) = ∑ i, η i * u i (c i t)) ∧
      WalrasEq (Set.Ici 0) Y δ (negishiUtility η u) (fun t => ∑ i, ω i t) p y := by
  have hc0 : ∀ i t, 0 ≤ c i t := fun i t k => (hcpos i t k).le
  -- each consumer's first-order conditions (20.D.6)
  have hfoc : ∀ i, ∃ lam : ℝ, 0 < lam ∧ ∀ t v, lam * (p t ⬝ᵥ v) = δ ^ t * D i t v := by
    intro i
    obtain ⟨hbud, hs, hmax⟩ := he.utilityMax i
    have hmyo : MyopicUtilityMax (Set.Ici 0) δ (u i) p (wealthI θ p y ω i) (c i) := by
      refine ⟨hbud, hs, fun t c' hc' hdiff => hmax c' hc' ?_⟩
      exact summable_of_finite_change {t, t + 1} (fun s hst => by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hst
        exact hdiff s hst.1 hst.2) hs
    obtain ⟨-, h5⟩ := (exercise_20_D_3 hδ (hconc i) (hmono i) (hcpos i) hbud.2.1 hs (hD i)
      (hDpos i)).1 hmyo
    have hpne : ∀ t, p t ≠ 0 := by
      intro t hpt
      obtain ⟨lam, hlam, h1, -⟩ := h5 t
      have := h1 (Pi.single 0 1)
      rw [hpt, zero_dotProduct, mul_zero] at this
      exact (hDpos i t 0).ne' this.symm
    exact (foc_20_D_5_iff_20_D_6 hδ hpne).1 h5
  choose lam hlam hlamfoc using hfoc
  set η : ι → ℝ := fun i => (lam i)⁻¹ with hη
  have hηpos : ∀ i, 0 < η i := fun i => inv_pos.2 (hlam i)
  set q : ℕ → Fin L → ℝ := fun t => (δ ^ t)⁻¹ • p t with hq
  have hqfoc : ∀ t i v, η i * D i t v = q t ⬝ᵥ v := by
    intro t i v
    have := hlamfoc i t v
    simp only [hη, hq, smul_dotProduct, smul_eq_mul]
    have hδt : δ ^ t ≠ 0 := pow_ne_zero t hδ.ne'
    field_simp
    rw [div_eq_iff (hlam i).ne']
    linarith
  have hq0 : ∀ t, 0 ≤ q t := fun t k => by
    simp only [hq, Pi.smul_apply, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.2 (pow_nonneg hδ.le t)) (he.pricesNonneg t k)
  have hprops : ∀ t, negishiUtility η u (∑ i, c i t) = ∑ i, η i * u i (c i t) ∧
      ∀ x, 0 ≤ x → negishiUtility η u x ≤ ∑ i, η i * u i (c i t)
        + q t ⬝ᵥ (x - ∑ i, c i t) := fun t =>
    negishiUtility_props hηpos hconc (fun i => hc0 i t) (fun i => hD i t) (hq0 t)
      (fun i v => hqfoc t i v)
  have hcons : ∀ t, consumption (fun t => ∑ i, ω i t) y t = ∑ i, c i t := fun t => by
    rw [he.feasible t]; rfl
  obtain ⟨hWs, hW⟩ := sum_wealthI hθ0 hθ1 he.profitSummable he.endowSummable
  -- every consumer's budget binds
  have hbind : ∀ i, HasSum (fun t => p t ⬝ᵥ c i t) (wealthI θ p y ω i) := fun i =>
    budget_binds (fun _ h => h) (fun x hx x' hxx' => Set.mem_Ici.2 ((Set.mem_Ici.1 hx).trans
      hxx')) (hmono i) he.pricesNonneg (he.utilityMax i).1 (he.utilityMax i).2.1
      (fun c' hc' hdiff => (he.utilityMax i).2.2 c' hc'
        (summable_of_finite_change {0} (fun t ht => hdiff t (by simpa using ht))
          (he.utilityMax i).2.1))
  have hbindT : HasSum (fun t => p t ⬝ᵥ ∑ i, c i t)
      (∑' t, (periodProfit p y t + p t ⬝ᵥ ∑ i, ω i t)) := by
    rw [← hW]
    have := hasSum_sum (s := Finset.univ) fun i _ => hbind i
    exact this.congr_fun fun t => by rw [dotProduct_sum]
  have hsumU : Summable fun t => δ ^ t * negishiUtility η u (∑ i, c i t) := by
    have := summable_sum (s := Finset.univ) fun i _ => ((he.utilityMax i).2.1.mul_left (η i))
    refine this.congr fun t => ?_
    rw [(hprops t).1, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  refine ⟨η, hηpos, hcons, fun t => (hprops t).1, he.boundedPath, he.boundedPrices,
    he.pricesNonneg, fun t => ?_, he.myopic, hWs, ?_⟩
  · rw [hcons t]; exact Finset.sum_nonneg fun i _ => hc0 i t
  · refine ⟨⟨fun t => ?_, ?_, fun T => ?_⟩, ?_, fun C' hC' hsC' => ?_⟩
    · rw [hcons t]; exact Finset.sum_nonneg fun i _ => hc0 i t
    · choose Mi hMi using fun i => (he.utilityMax i).1.2.1
      refine ⟨∑ i, Mi i, fun t k => ?_⟩
      rw [hcons t, Finset.sum_apply]
      exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => hMi i t k)
    · have hnn : ∀ t, 0 ≤ p t ⬝ᵥ consumption (fun t => ∑ i, ω i t) y t := fun t => by
        rw [hcons t]
        exact dotProduct_nonneg_of_nonneg (he.pricesNonneg t)
          (Finset.sum_nonneg fun i _ => hc0 i t)
      have hb' : HasSum (fun t => p t ⬝ᵥ consumption (fun t => ∑ i, ω i t) y t)
          (∑' t, (periodProfit p y t + p t ⬝ᵥ ∑ i, ω i t)) :=
        hbindT.congr_fun fun t => by rw [hcons t]
      rw [← hb'.tsum_eq]
      exact hb'.summable.sum_le_tsum _ (fun t _ => hnn t)
    · simpa [hcons] using hsumU
    · -- the supergradient inequality, summed over dates
      obtain ⟨hsum', hle'⟩ := expenditure_summable he.pricesNonneg (fun t => hC'.1 t) hC'.2.2
      have hterm : ∀ t, δ ^ t * negishiUtility η u (C' t) ≤
          δ ^ t * negishiUtility η u (∑ i, c i t) + (p t ⬝ᵥ C' t - p t ⬝ᵥ ∑ i, c i t) := by
        intro t
        have h1 := (hprops t).2 (C' t) (hC'.1 t)
        rw [← (hprops t).1] at h1
        have hδt : 0 < δ ^ t := pow_pos hδ t
        have hpq : δ ^ t * (q t ⬝ᵥ (C' t - ∑ i, c i t)) = p t ⬝ᵥ C' t - p t ⬝ᵥ ∑ i, c i t := by
          simp only [hq, smul_dotProduct, smul_eq_mul, dotProduct_sub]
          field_simp
        nlinarith [mul_le_mul_of_nonneg_left h1 hδt.le]
      have hrhs : Summable fun t => δ ^ t * negishiUtility η u (∑ i, c i t)
          + (p t ⬝ᵥ C' t - p t ⬝ᵥ ∑ i, c i t) :=
        hsumU.add (hsum'.sub hbindT.summable)
      have := Summable.tsum_le_tsum hterm hsC' hrhs
      rw [hsumU.tsum_add (hsum'.sub hbindT.summable), hsum'.tsum_sub hbindT.summable,
        hbindT.tsum_eq] at this
      unfold discountedUtility
      have hC : consumption (fun t => ∑ i, ω i t) y = fun t => ∑ i, c i t := funext hcons
      rw [hC]
      linarith

/-! ### Exercise 20.G.1 -/

/-- **Exercise 20.G.1** (MWG, p. 785): one good, two consumers with a common discount factor
`0 < δ < 1` and aggregate endowment `ω₁ₜ + ω₂ₜ = 1`. At an interior equilibrium the first-order
conditions `λ_i p_t = δ^t u_i'(c_{it})` hold (Exercise 20.D.3, (20.D.6)) and each budget binds
(Proposition 20.D.1's argument). With strictly decreasing marginal utilities it follows that
consumption is stationary, prices are proportional `p_t = δ^t p₀` (rate of interest
`(1 - δ)/δ`), and consumer 1's consumption is uniquely `(1 - δ) ∑_t δ^t ω₁ₜ`. -/
theorem exercise_20_G_1 {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) {u1' u2' : ℝ → ℝ}
    (h1 : StrictAntiOn u1' (Set.Ioo 0 1)) (h2 : StrictAntiOn u2' (Set.Ioo 0 1))
    {c p ω : ℕ → ℝ} (hc : ∀ t, c t ∈ Set.Ioo 0 1) (hp : ∀ t, 0 < p t) {lam₁ lam₂ : ℝ}
    (hl₁ : 0 < lam₁) (hl₂ : 0 < lam₂) (hfoc₁ : ∀ t, lam₁ * p t = δ ^ t * u1' (c t))
    (hfoc₂ : ∀ t, lam₂ * p t = δ ^ t * u2' (1 - c t))
    (hbud : HasSum (fun t => p t * c t) (∑' t, p t * ω t)) :
    (∀ t, c t = c 0) ∧ (∀ t, p t = δ ^ t * p 0) ∧
      (∀ t, p t = (1 + (1 - δ) / δ) * p (t + 1)) ∧
      c 0 = (1 - δ) * ∑' t, δ ^ t * ω t := by
  -- `λ₂ u₁'(c_t) = λ₁ u₂'(1 - c_t)` and the left side minus the right is strictly decreasing
  have hkey : ∀ t, lam₂ * u1' (c t) - lam₁ * u2' (1 - c t) = 0 := by
    intro t
    have := pow_pos hδ0 t
    have e : δ ^ t * (lam₂ * u1' (c t) - lam₁ * u2' (1 - c t)) = 0 := by
      have a1 := hfoc₁ t
      have a2 := hfoc₂ t
      nlinarith
    exact (mul_eq_zero.1 e).resolve_left this.ne'
  have hmono : StrictAntiOn (fun x => lam₂ * u1' x - lam₁ * u2' (1 - x)) (Set.Ioo 0 1) := by
    intro x hx z hz hxz
    have a := h1 hx hz hxz
    have hx' : 1 - x ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [hx.2], by linarith [hx.1]⟩
    have hz' : 1 - z ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [hz.2], by linarith [hz.1]⟩
    have b := h2 hz' hx' (by linarith)
    simp only
    nlinarith
  have hconst : ∀ t, c t = c 0 := fun t =>
    hmono.injOn (hc t) (hc 0) ((hkey t).trans (hkey 0).symm)
  have hprop : ∀ t, p t = δ ^ t * p 0 := by
    intro t
    have a := hfoc₁ t
    have b := hfoc₁ 0
    rw [hconst t] at a
    simp only [pow_zero, one_mul] at b
    have : lam₁ * p t = lam₁ * (δ ^ t * p 0) := by rw [a, ← b]; ring
    exact mul_left_cancel₀ hl₁.ne' this
  refine ⟨hconst, hprop, fun t => ?_, ?_⟩
  · rw [hprop t, hprop (t + 1), pow_succ]; field_simp; ring
  · have hg := hasSum_geometric_of_lt_one hδ0.le hδ1
    have h1' : HasSum (fun t => p t * c t) (p 0 * c 0 * (1 - δ)⁻¹) := by
      have := (hg.mul_left (p 0 * c 0))
      exact this.congr_fun fun t => by rw [hprop t, hconst t]; ring
    have h2' : ∑' t, p t * ω t = p 0 * ∑' t, δ ^ t * ω t := by
      rw [← tsum_mul_left]; exact tsum_congr fun t => by rw [hprop t]; ring
    have := hbud.unique h1'
    rw [h2'] at this
    have hp0 := hp 0
    have h1δ : (1 : ℝ) - δ ≠ 0 := by linarith
    field_simp at this
    nlinarith

/-! ### Externalities: (20.G.5)-(20.G.6) and Exercise 20.G.5 -/

/-- **(20.G.6)** (MWG, p. 769): differentiating the equilibrium condition (20.G.5)
`∇₂u(k_{t-1}, k_t, k_t) + δ ∇₁u(k_t, k_{t+1}, k_{t+1}) = 0` along a solution `k_{t+1} = φ(k_t)`
(implicit function theorem) gives
`dk_{t+1}/dk_t = -(∇²₂₂u + ∇²₂₃u + δ∇²₁₁u) / (δ(∇²₁₂u + ∇²₁₃u))`. -/
theorem eq_20_G_6 {u22 u23 u11 u12 u13 δ dφ : ℝ} (hden : δ * (u12 + u13) ≠ 0)
    (htotal : (u22 + u23 + δ * u11) + δ * (u12 + u13) * dφ = 0) :
    dφ = -(u22 + u23 + δ * u11) / (δ * (u12 + u13)) := by
  rw [eq_div_iff hden]; linarith

/-- **Exercise 20.G.5** (MWG, p. 786): without externalities (`∇²₂₃u = ∇²₁₃u = 0`), concavity
(`∇²₁₁u ≤ 0`, `∇²₂₂u ≤ 0`, `(∇²₁₂u)² ≤ ∇²₁₁u ∇²₂₂u`), `∇²₁₂u ≠ 0` and `0 < δ < 1` make
(20.G.6) larger than one in absolute value. -/
theorem exercise_20_G_5 {u11 u22 u12 δ : ℝ} (h11 : u11 ≤ 0) (h22 : u22 ≤ 0)
    (hconc : u12 ^ 2 ≤ u11 * u22) (h12 : u12 ≠ 0) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    1 < |-(u22 + 0 + δ * u11) / (δ * (u12 + 0))| := by
  rw [add_zero, add_zero, abs_div, abs_neg, abs_mul, abs_of_pos hδ0,
    one_lt_div (mul_pos hδ0 (abs_pos.2 h12))]
  have hsum : |u22 + δ * u11| = -u22 + δ * -u11 := by
    rw [abs_of_nonpos (by nlinarith)]; ring
  rw [hsum]
  have hu12 : 0 < |u12| := abs_pos.2 h12
  have hsq : |u12| ^ 2 ≤ (-u11) * (-u22) := by rw [sq_abs]; linarith
  -- `(a + δb)² ≥ 4δab ≥ 4δ u12² > δ² u12²`
  have hs0 : 0 ≤ -u22 + δ * -u11 := by nlinarith
  have hsq2 : (δ * |u12|) ^ 2 < (-u22 + δ * -u11) ^ 2 := by
    have e1 : 4 * δ * ((-u11) * (-u22)) ≤ (-u22 + δ * -u11) ^ 2 := by
      nlinarith [sq_nonneg (-u22 - δ * -u11)]
    have e2 : 4 * δ * |u12| ^ 2 ≤ 4 * δ * ((-u11) * (-u22)) :=
      mul_le_mul_of_nonneg_left hsq (by linarith)
    have e3 : (δ * |u12|) ^ 2 < 4 * δ * |u12| ^ 2 := by
      have : 0 < δ * (4 - δ) * |u12| ^ 2 := by
        have := pow_pos hu12 2
        have h4 : 0 < 4 - δ := by linarith
        positivity
      nlinarith
    linarith
  exact lt_of_pow_lt_pow_left₀ 2 hs0 hsq2

/-- **The dampening criterion** (MWG, p. 769): if the linearized dynamics are
`x_{t+2} = a x_{t+1} + b x_t` with `|a| < 1/2` and `|b| < 1/2`, every perturbation dies out,
`x_t → 0`. -/
theorem dampening_of_small_coefficients {a b : ℝ} (ha : |a| < 1 / 2) (hb : |b| < 1 / 2)
    {x : ℕ → ℝ} (hrec : ∀ t, x (t + 2) = a * x (t + 1) + b * x t) :
    Tendsto x atTop (𝓝 0) := by
  set ρ := |a| + |b| with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ < 1 := by linarith
  set m : ℕ → ℝ := fun t => max |x t| |x (t + 1)| with hm
  have hstep : ∀ t, |x (t + 2)| ≤ ρ * m t := by
    intro t
    rw [hrec t]
    calc |a * x (t + 1) + b * x t| ≤ |a| * |x (t + 1)| + |b| * |x t| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ |a| * m t + |b| * m t := add_le_add
          (mul_le_mul_of_nonneg_left (le_max_right _ _) (abs_nonneg _))
          (mul_le_mul_of_nonneg_left (le_max_left _ _) (abs_nonneg _))
      _ = ρ * m t := by ring
  have hm0 : ∀ t, 0 ≤ m t := fun t => (abs_nonneg _).trans (le_max_left _ _)
  have hmono : ∀ t, m (t + 1) ≤ m t := by
    intro t
    refine max_le (le_max_right _ _) ?_
    exact (hstep t).trans ((mul_le_of_le_one_left (hm0 t) hρ1.le))
  have hdec : ∀ n, m (2 * n) ≤ ρ ^ n * m 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h1 : m (2 * (n + 1)) ≤ ρ * m (2 * n) := by
        rw [show 2 * (n + 1) = 2 * n + 2 by ring]
        refine max_le (hstep (2 * n)) ?_
        exact (hstep (2 * n + 1)).trans (mul_le_mul_of_nonneg_left (hmono _) hρ0)
      calc m (2 * (n + 1)) ≤ ρ * m (2 * n) := h1
        _ ≤ ρ * (ρ ^ n * m 0) := mul_le_mul_of_nonneg_left ih hρ0
        _ = ρ ^ (n + 1) * m 0 := by ring
  have hanti : Antitone m := antitone_nat_of_succ_le hmono
  have hbound : ∀ t, |x t| ≤ ρ ^ (t / 2) * m 0 := by
    intro t
    calc |x t| ≤ m t := le_max_left _ _
      _ ≤ m (2 * (t / 2)) := hanti (Nat.mul_div_le t 2)
      _ ≤ ρ ^ (t / 2) * m 0 := hdec _
  have hlim : Tendsto (fun t : ℕ => ρ ^ (t / 2) * m 0) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).comp
      (Nat.tendsto_div_const_atTop (by norm_num : (2 : ℕ) ≠ 0))
    simpa using this.mul_const (m 0)
  exact squeeze_zero_norm (fun t => by rw [Real.norm_eq_abs]; exact hbound t) hlim

end MWG.EquilibriumTime

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Several consumers: Pareto optima and marginal utilities of wealth (MWG Section 20.G)

MWG, Chapter 20, Exercise 20.G.2 (p. 785), footnote 32 (p. 768) and Exercise 20.G.4 (p. 786).

An exchange economy with consumers `i ∈ ι`, `L` goods per period, a common discount factor and
utilities `∑_t δ^t u_i(c_{it})`. A feasible allocation is Pareto optimal
(`ParetoOptimalExchange`) if no feasible allocation with convergent utility series makes every
consumer at least as well off and one strictly better off.

* **Exercise 20.G.2** (`exercise_20_G_2`): at an interior Pareto optimum with differentiable
  one-period utilities, for any two consumers `i ≠ j` the ratio
  `∂_ℓ u_i(c_{it}) / ∂_ℓ u_j(c_{jt})` is the same for every period `t` and every good `ℓ`
  (cross-multiplied). With strictly positive marginal utilities (`exercise_20_G_2_ratio`)
  there is `κ > 0` with
  `∇u_i(c_{it}) = κ ∇u_j(c_{jt})` for all `t`: measured in any common unit of account the
  in-period marginal utilities of wealth stand in a ratio independent of the period, so with the
  supporting prices `p_t = δ^t ∇u_j(c_{jt})` each consumer's in-period marginal utility of wealth
  is the same in every period. The proof is the perturbation argument: if the ratios differed,
  a two-date transfer between `i` and `j` would improve both to the first order.
* A proved instance of the Pareto optimality hypothesis (`paretoOptimalExchange_linear`): linear
  utilities with a common gradient, at any allocation exhausting the endowments.
* **Footnote 32 / Exercise 20.G.4**: with constant endowments, a common discount factor and no
  production, the intertemporal equilibria are exactly the constant repetitions of the static
  Walrasian equilibria (`StaticWalrasEq`, instance `staticWalrasEq_noTrade`), with price
  sequences `p_t = δ^t p̄`. The repetition of an interior static equilibrium is an equilibrium
  in the sense of Definition 20.G.1 (`exercise_20_G_4_repetition`, using the static first-order
  conditions `static_foc`); conversely, with strictly concave utilities every equilibrium
  satisfying the first-order conditions (20.D.6) with binding budgets has constant consumption,
  prices `δ^t p_0` and a static equilibrium at date 0 (`exercise_20_G_4_static`, via the strict
  gradient inequality `strictConcave_lt_fderiv`). The footnote's `L = 2`, `I = 2` is the special
  case `Fin 2`, `ι = Fin 2`.
-/

open Filter Topology

namespace MWG.EquilibriumTime

variable {L : ℕ} {ι : Type*} [Fintype ι]

/-- A **Pareto optimal** allocation of the exchange economy with aggregate endowments `ω`
(MWG, Section 20.G, Exercise 20.G.2): nonnegative, feasible, and not Pareto dominated by any
nonnegative feasible allocation whose utility series converge. -/
def ParetoOptimalExchange (δ : ℝ) (u : ι → (Fin L → ℝ) → ℝ) (ω : ℕ → Fin L → ℝ)
    (c : ι → ℕ → Fin L → ℝ) : Prop :=
  (∀ i t, 0 ≤ c i t) ∧ (∀ t, ∑ i, c i t ≤ ω t) ∧
    ¬ ∃ c' : ι → ℕ → Fin L → ℝ, (∀ i t, 0 ≤ c' i t) ∧ (∀ t, ∑ i, c' i t ≤ ω t) ∧
      (∀ i, Summable fun t => δ ^ t * u i (c' i t)) ∧
      (∀ i, discountedUtility δ (u i) (c i) ≤ discountedUtility δ (u i) (c' i)) ∧
      ∃ j, discountedUtility δ (u j) (c j) < discountedUtility δ (u j) (c' j)

/-- Changing a stream at finitely many dates changes discounted utility by the finite sum of
the discounted one-period changes. -/
theorem discountedUtility_finite_change {δ : ℝ} {u : (Fin L → ℝ) → ℝ} {c c' : ℕ → Fin L → ℝ}
    {N : ℕ} (hcc : ∀ τ, N ≤ τ → c' τ = c τ) (hs : Summable fun t => δ ^ t * u (c t)) :
    Summable (fun t => δ ^ t * u (c' t)) ∧ discountedUtility δ u c' =
      discountedUtility δ u c + ∑ τ ∈ Finset.range N, δ ^ τ * (u (c' τ) - u (c τ)) := by
  set h : ℕ → ℝ := fun τ => δ ^ τ * (u (c' τ) - u (c τ)) with hh
  have hzero : ∀ τ ∉ Finset.range N, h τ = 0 := fun τ hτ => by
    simp only [Finset.mem_range, not_lt] at hτ
    simp [hh, hcc τ hτ]
  have hsh : Summable h := summable_of_ne_finset_zero hzero
  have heq : (fun t => δ ^ t * u (c' t)) = fun t => δ ^ t * u (c t) + h t := by
    funext t; simp only [hh]; ring
  refine ⟨heq ▸ hs.add hsh, ?_⟩
  unfold discountedUtility
  rw [heq, hs.tsum_add hsh, tsum_eq_sum hzero]

/-- The core of Exercise 20.G.2: at an interior Pareto optimum,
`∂_ℓ u_j(c_{jt}) ∂_{ℓ'} u_i(c_{it'}) ≥ ∂_ℓ u_i(c_{it}) ∂_{ℓ'} u_j(c_{jt'})` fails to be strict
in the other direction: otherwise a transfer from `j` to `i` of good `ℓ` at `t` against good `ℓ'`
at `t'` raises both utilities. -/
theorem pareto_ratio_core {δ : ℝ} (hδ : 0 < δ) {u : ι → (Fin L → ℝ) → ℝ}
    {ω : ℕ → Fin L → ℝ} {c : ι → ℕ → Fin L → ℝ} (hpo : ParetoOptimalExchange δ u ω c)
    (hs : ∀ i, Summable fun t => δ ^ t * u i (c i t)) (hint : ∀ i t l, 0 < c i t l)
    {D : ι → ℕ → (Fin L → ℝ) →L[ℝ] ℝ} (hD : ∀ i t, HasFDerivAt (u i) (D i t) (c i t))
    {i j : ι} (hij : i ≠ j) (t t' : ℕ) (l l' : Fin L) :
    ¬ D j t (Pi.single l 1) * D i t' (Pi.single l' 1)
      < D i t (Pi.single l 1) * D j t' (Pi.single l' 1) := by
  classical
  intro hlt
  obtain ⟨hc0, hfeas, hno⟩ := hpo
  set ai := δ ^ t * D i t (Pi.single l 1) with hai
  set aj := δ ^ t * D j t (Pi.single l 1) with haj
  set bi := δ ^ t' * D i t' (Pi.single l' 1) with hbi
  set bj := δ ^ t' * D j t' (Pi.single l' 1) with hbj
  have hgap : 0 < ai * bj - aj * bi := by
    have : ai * bj - aj * bi = δ ^ t * δ ^ t' * (D i t (Pi.single l 1) * D j t' (Pi.single l' 1)
        - D j t (Pi.single l 1) * D i t' (Pi.single l' 1)) := by
      simp only [hai, haj, hbi, hbj]; ring
    rw [this]
    exact mul_pos (mul_pos (pow_pos hδ t) (pow_pos hδ t')) (by linarith)
  set x := bi + bj with hx
  set y := ai + aj with hy
  -- the transfer: consumer `i` gains `x` of good `l` at `t` and loses `y` of good `l'` at `t'`
  set v : ℕ → Fin L → ℝ := fun τ =>
    (if τ = t then x • Pi.single l 1 else 0) - (if τ = t' then y • Pi.single l' 1 else 0) with hv
  set κ : ι → ℝ := Pi.single i 1 - Pi.single j 1 with hκ
  have hκsum : ∑ k, κ k = 0 := by simp [hκ, Finset.sum_sub_distrib]
  have hκi : κ i = 1 := by simp [hκ, hij]
  have hκj : κ j = -1 := by simp [hκ, Ne.symm hij]
  set N := max t t' + 1 with hN
  have htN : t ∈ Finset.range N := Finset.mem_range.2 (by omega)
  have ht'N : t' ∈ Finset.range N := Finset.mem_range.2 (by omega)
  have hvN : ∀ τ, N ≤ τ → v τ = 0 := fun τ hτ => by
    simp [hv, show τ ≠ t by omega, show τ ≠ t' by omega]
  -- the utility gain of consumer `k` as a function of the size `s` of the transfer
  set φ : ι → ℝ → ℝ := fun k s =>
    ∑ τ ∈ Finset.range N, δ ^ τ * (u k (c k τ + (s * κ k) • v τ) - u k (c k τ)) with hφ
  have hderiv : ∀ k, HasDerivAt (φ k)
      (∑ τ ∈ Finset.range N, δ ^ τ * D k τ (κ k • v τ)) 0 := by
    intro k
    have hterm : ∀ τ ∈ Finset.range N, HasDerivAt
        (fun s : ℝ => δ ^ τ * (u k (c k τ + (s * κ k) • v τ) - u k (c k τ)))
        (δ ^ τ * D k τ (κ k • v τ)) 0 := fun τ _ => by
      have hline : HasDerivAt (fun s : ℝ => c k τ + (s * κ k) • v τ) (κ k • v τ) 0 := by
        have := ((hasDerivAt_id (0 : ℝ)).mul_const (κ k)).smul_const (v τ)
        simpa using this.const_add (c k τ)
      have hc := (hD k τ).comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
      exact (hc.sub_const (u k (c k τ))).const_mul (δ ^ τ)
    convert HasDerivAt.sum hterm using 1
    funext s
    simp only [hφ, Finset.sum_apply]
  have hDv : ∀ k, ∑ τ ∈ Finset.range N, δ ^ τ * D k τ (κ k • v τ)
      = κ k * (x * (δ ^ t * D k t (Pi.single l 1)) - y * (δ ^ t' * D k t' (Pi.single l' 1))) := by
    intro k
    have e : ∀ τ, δ ^ τ * D k τ (κ k • v τ) =
        κ k * ((if τ = t then x * (δ ^ t * D k t (Pi.single l 1)) else 0) -
          (if τ = t' then y * (δ ^ t' * D k t' (Pi.single l' 1)) else 0)) := fun τ => by
      simp only [hv, map_smul, map_sub, smul_eq_mul]
      split_ifs with h1 h2 h2 <;> subst_vars <;> simp <;> ring
    rw [Finset.sum_congr rfl fun τ _ => e τ, ← Finset.mul_sum, Finset.sum_sub_distrib,
      Finset.sum_ite_eq' _ _ _, Finset.sum_ite_eq' _ _ _]
    simp only [htN, ht'N, ↓reduceIte]
  have hφ0 : ∀ k, φ k 0 = 0 := fun k => by simp [hφ]
  -- both `i` and `j` gain to the first order
  have hdi : 0 < ∑ τ ∈ Finset.range N, δ ^ τ * D i τ (κ i • v τ) := by
    rw [hDv i, hκi, one_mul, ← hai, ← hbi, hx, hy]; nlinarith
  have hdj : 0 < ∑ τ ∈ Finset.range N, δ ^ τ * D j τ (κ j • v τ) := by
    rw [hDv j, hκj, ← haj, ← hbj, hx, hy]; nlinarith
  have hevi := eventually_pos_of_hasDerivAt (hderiv i) (hφ0 i) hdi
  have hevj := eventually_pos_of_hasDerivAt (hderiv j) (hφ0 j) hdj
  -- the perturbed allocation stays nonnegative for small `s`
  have hnn : ∀ τ, ∀ᶠ s in 𝓝 (0 : ℝ), ∀ k l₀, 0 ≤ c k τ l₀ + (s * κ k) * v τ l₀ := by
    intro τ
    rw [eventually_all]; intro k
    rw [eventually_all]; intro l₀
    have hcont : Continuous fun s : ℝ => c k τ l₀ + (s * κ k) * v τ l₀ := by fun_prop
    exact (hcont.continuousAt.eventually (lt_mem_nhds (by simpa using hint k τ l₀))).mono
      fun _ h => h.le
  have hnn' : ∀ᶠ s in 𝓝[>] (0 : ℝ), (∀ k l₀, 0 ≤ c k t l₀ + (s * κ k) * v t l₀) ∧
      ∀ k l₀, 0 ≤ c k t' l₀ + (s * κ k) * v t' l₀ :=
    nhdsWithin_le_nhds ((hnn t).and (hnn t'))
  obtain ⟨s, ⟨hφi, hφj⟩, hnt, hnt'⟩ := ((hevi.and hevj).and hnn').exists
  set c' : ι → ℕ → Fin L → ℝ := fun k τ => c k τ + (s * κ k) • v τ with hc'
  have hchg : ∀ k τ, N ≤ τ → c' k τ = c k τ := fun k τ hτ => by simp [hc', hvN τ hτ]
  have hfc : ∀ k, Summable (fun τ => δ ^ τ * u k (c' k τ)) ∧ discountedUtility δ (u k) (c' k) =
      discountedUtility δ (u k) (c k) + φ k s := fun k =>
    discountedUtility_finite_change (hchg k) (hs k)
  refine hno ⟨c', fun k τ l₀ => ?_, fun τ => ?_, fun k => (hfc k).1, fun k => ?_, i, ?_⟩
  · simp only [hc', Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    by_cases h1 : τ = t
    · subst h1; exact hnt k l₀
    by_cases h2 : τ = t'
    · subst h2; exact hnt' k l₀
    simp only [hv, h1, h2, ↓reduceIte, sub_self, Pi.zero_apply, mul_zero, add_zero]
    exact hc0 k τ l₀
  · have : ∑ k, c' k τ = ∑ k, c k τ := by
      simp only [hc', Finset.sum_add_distrib, mul_smul]
      simp [← Finset.sum_smul, ← smul_assoc, hκsum, ← Finset.mul_sum]
    rw [this]; exact hfeas τ
  · rw [(hfc k).2]
    by_cases hk1 : k = i
    · subst hk1; linarith
    by_cases hk2 : k = j
    · subst hk2; linarith
    have : κ k = 0 := by simp [hκ, hk1, hk2]
    have : φ k s = 0 := by simp [hφ, this]
    linarith
  · rw [(hfc i).2]; linarith

/-- **Exercise 20.G.2** (MWG, p. 785): at an interior Pareto optimum of the exchange economy
(common discount factor `0 < δ`, differentiable one-period utilities, convergent utility
series), for any two consumers `i ≠ j`, all periods
`t, t'` and goods `ℓ, ℓ'`,
`∂_ℓ u_i(c_{it}) ∂_{ℓ'} u_j(c_{jt'}) = ∂_ℓ u_j(c_{jt}) ∂_{ℓ'} u_i(c_{it'})`. -/
theorem exercise_20_G_2 {δ : ℝ} (hδ : 0 < δ) {u : ι → (Fin L → ℝ) → ℝ}
    {ω : ℕ → Fin L → ℝ} {c : ι → ℕ → Fin L → ℝ} (hpo : ParetoOptimalExchange δ u ω c)
    (hs : ∀ i, Summable fun t => δ ^ t * u i (c i t)) (hint : ∀ i t l, 0 < c i t l)
    {D : ι → ℕ → (Fin L → ℝ) →L[ℝ] ℝ} (hD : ∀ i t, HasFDerivAt (u i) (D i t) (c i t))
    {i j : ι} (hij : i ≠ j) (t t' : ℕ) (l l' : Fin L) :
    D i t (Pi.single l 1) * D j t' (Pi.single l' 1)
      = D j t (Pi.single l 1) * D i t' (Pi.single l' 1) := by
  rcases lt_trichotomy (D j t (Pi.single l 1) * D i t' (Pi.single l' 1))
    (D i t (Pi.single l 1) * D j t' (Pi.single l' 1)) with h | h | h
  · exact absurd h (pareto_ratio_core hδ hpo hs hint hD hij t t' l l')
  · exact h.symm
  · exact absurd h (pareto_ratio_core hδ hpo hs hint hD (Ne.symm hij) t t' l l')

/-- **Exercise 20.G.2**, ratio form (MWG, p. 785): with `L ≥ 1`, there is `κ > 0` such that
`∇u_i(c_{it}) = κ ∇u_j(c_{jt})` in every period `t`. With the supporting prices
`p_t = δ^t ∇u_j(c_{jt})` the first-order conditions `δ^t ∇u_i(c_{it}) = λ_{it} p_t` hold with
`λ_{it} = κ` and `λ_{jt} = 1` for all `t`: each consumer's in-period marginal utility of wealth is
the same in every period. -/
theorem exercise_20_G_2_ratio [NeZero L] {δ : ℝ} (hδ : 0 < δ)
    {u : ι → (Fin L → ℝ) → ℝ} {ω : ℕ → Fin L → ℝ} {c : ι → ℕ → Fin L → ℝ}
    (hpo : ParetoOptimalExchange δ u ω c) (hs : ∀ i, Summable fun t => δ ^ t * u i (c i t))
    (hint : ∀ i t l, 0 < c i t l) {D : ι → ℕ → (Fin L → ℝ) →L[ℝ] ℝ}
    (hD : ∀ i t, HasFDerivAt (u i) (D i t) (c i t)) (hpos : ∀ i t l, 0 < D i t (Pi.single l 1))
    {i j : ι} (hij : i ≠ j) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ t, D i t = κ • D j t := by
  set κ := D i 0 (Pi.single 0 1) / D j 0 (Pi.single 0 1) with hκ
  refine ⟨κ, div_pos (hpos i 0 0) (hpos j 0 0), fun t => ?_⟩
  refine ContinuousLinearMap.ext fun z => ?_
  change D i t z = κ • D j t z
  have hz : z = ∑ l, z l • (Pi.single l (1 : ℝ) : Fin L → ℝ) := by
    funext m; simp [Finset.sum_apply, Pi.single_apply]
  rw [hz]
  simp only [map_sum, map_smul, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  have e := exercise_20_G_2 hδ hpo hs hint hD hij t 0 l 0
  have hj0 := hpos j 0 0
  rw [hκ, div_mul_eq_mul_div, eq_div_iff hj0.ne']
  linear_combination (z l) * e

/-- A proved instance of `ParetoOptimalExchange`: if every consumer has the linear one-period
utility `u_i(x) = ∑_ℓ x_ℓ`, `0 ≤ δ < 1` and the aggregate endowment is bounded, any nonnegative
allocation with `∑_i c_{it} = ω_t` is Pareto optimal. -/
theorem paretoOptimalExchange_linear {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    {ω : ℕ → Fin L → ℝ} {B : ℝ} (hωB : ∀ t l, ω t l ≤ B) {c : ι → ℕ → Fin L → ℝ}
    (hc0 : ∀ i t, 0 ≤ c i t) (hcω : ∀ t, ∑ i, c i t = ω t) :
    ParetoOptimalExchange δ (fun _ x => ∑ l, x l) ω c := by
  refine ⟨hc0, fun t => (hcω t).le, ?_⟩
  rintro ⟨c', hc'0, hfeas', hs', hge, j, hj⟩
  -- total utility is bounded by the discounted value of the endowments
  have hbd : ∀ (d : ι → ℕ → Fin L → ℝ), (∀ i t, 0 ≤ d i t) → (∀ t, ∑ i, d i t ≤ ω t) →
      ∀ i t, |δ ^ t * ∑ l, d i t l| ≤ δ ^ t * (Fintype.card (Fin L) * B) := by
    intro d hd hdω i t
    have hδt := pow_nonneg hδ0 t
    rw [abs_mul, abs_of_nonneg hδt]
    refine mul_le_mul_of_nonneg_left ?_ hδt
    rw [abs_of_nonneg (Finset.sum_nonneg fun l _ => hd i t l)]
    calc ∑ l, d i t l ≤ ∑ l, ω t l := Finset.sum_le_sum fun l _ =>
            (Finset.single_le_sum (fun k _ => hd k t l) (Finset.mem_univ i)).trans
              (by simpa [Finset.sum_apply] using hdω t l)
      _ ≤ ∑ _l : Fin L, B := Finset.sum_le_sum fun l _ => hωB t l
      _ = Fintype.card (Fin L) * B := by simp
  have hgeo : Summable fun t => δ ^ t * (Fintype.card (Fin L) * B) :=
    (summable_geometric_of_lt_one hδ0 hδ1).mul_right _
  have hsc : ∀ i, Summable fun t => δ ^ t * ∑ l, c i t l := fun i =>
    Summable.of_norm_bounded hgeo fun t =>
      hbd c hc0 (fun t => (hcω t).le) i t
  -- the sums over consumers
  have htot : ∑ i, discountedUtility δ (fun x => ∑ l, x l) (c' i)
      ≤ ∑ i, discountedUtility δ (fun x => ∑ l, x l) (c i) := by
    unfold discountedUtility
    rw [← Summable.tsum_finsetSum fun i _ => hs' i, ← Summable.tsum_finsetSum fun i _ => hsc i]
    refine Summable.tsum_le_tsum (fun t => ?_) (summable_sum fun i _ => hs' i)
      (summable_sum fun i _ => hsc i)
    simp only [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hδ0 t)
    rw [Finset.sum_comm, Finset.sum_comm (f := fun i l => c i t l)]
    refine Finset.sum_le_sum fun l _ => ?_
    have h1 := hfeas' t l
    have h2 := congrFun (hcω t) l
    simp only [Finset.sum_apply] at h1 h2
    linarith
  have hlt : ∑ i, discountedUtility δ (fun x => ∑ l, x l) (c i)
      < ∑ i, discountedUtility δ (fun x => ∑ l, x l) (c' i) :=
    Finset.sum_lt_sum (fun i _ => hge i) ⟨j, Finset.mem_univ j, hj⟩
  linarith

/-! ### Footnote 32 and Exercise 20.G.4: repetitions of static equilibria -/

/-- The **strict gradient inequality**: for `u` strictly concave on a convex set `S` and
differentiable at `x ∈ S`, `u(y) < u(x) + Du(x)(y - x)` for every `y ∈ S`, `y ≠ x`. -/
theorem strictConcave_lt_fderiv {S : Set (Fin L → ℝ)} {f : (Fin L → ℝ) → ℝ}
    {f' : (Fin L → ℝ) →L[ℝ] ℝ} {x y : Fin L → ℝ} (hfc : StrictConcaveOn ℝ S f) (hx : x ∈ S)
    (hy : y ∈ S) (hxy : x ≠ y) (hf : HasFDerivAt f f' x) : f y < f x + f' (y - x) := by
  set m : Fin L → ℝ := (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y with hm
  have hmS : m ∈ S := hfc.1 hx hy (by norm_num) (by norm_num) (by norm_num)
  have hlt := hfc.2 hx hy hxy (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num)
  have hle := MWG.GeneralEquilibriumExamples.concave_le_fderiv hfc.concaveOn hx hmS hf
  have hmx : m - x = (1 / 2 : ℝ) • (y - x) := by
    simp only [hm, smul_sub]; module
  rw [hmx, map_smul, smul_eq_mul] at hle
  simp only [smul_eq_mul] at hlt
  linarith

/-- A **static (one-period) Walrasian equilibrium** of the exchange economy with endowments
`ω_i` (MWG, footnote 32): consumption bundles `x_i ≥ 0` in the budget sets of the prices `p̄`,
maximizing `u_i` there, and clearing the markets. -/
def StaticWalrasEq (u : ι → (Fin L → ℝ) → ℝ) (ω : ι → Fin L → ℝ) (pbar : Fin L → ℝ)
    (x : ι → Fin L → ℝ) : Prop :=
  (∀ i, 0 ≤ x i) ∧ (∀ i, pbar ⬝ᵥ x i ≤ pbar ⬝ᵥ ω i) ∧
    (∀ i z, 0 ≤ z → pbar ⬝ᵥ z ≤ pbar ⬝ᵥ ω i → u i z ≤ u i (x i)) ∧ ∑ i, x i = ∑ i, ω i

/-- A proved instance of `StaticWalrasEq`: one good, utilities `u_i(z) = z`, price `1`, no
trade. -/
theorem staticWalrasEq_noTrade (ω : ι → Fin 1 → ℝ) (hω : ∀ i, 0 ≤ ω i) :
    StaticWalrasEq (fun _ z => z 0) ω (fun _ => 1) ω := by
  refine ⟨hω, fun i => le_rfl, fun i z _ hz => ?_, rfl⟩
  simpa [dotProduct] using hz

/-- **First-order conditions of a static optimum**: if an interior bundle `x ≫ 0` maximizes `u`
on `{z ≥ 0 : p̄ · z ≤ p̄ · ω}` with `p̄ ≫ 0` and `u` is differentiable at `x`, then
`Du(x) = λ p̄` with `λ = ∂_0 u(x) / p̄_0`; if moreover `∂_0 u(x) > 0`, the budget binds. -/
theorem static_foc [NeZero L] {u : (Fin L → ℝ) → ℝ} {pbar ω x : Fin L → ℝ}
    (hp : ∀ l, 0 < pbar l) (hx : ∀ l, 0 < x l) (hxb : pbar ⬝ᵥ x ≤ pbar ⬝ᵥ ω)
    (hmax : ∀ z, 0 ≤ z → pbar ⬝ᵥ z ≤ pbar ⬝ᵥ ω → u z ≤ u x) {D : (Fin L → ℝ) →L[ℝ] ℝ}
    (hD : HasFDerivAt u D x) :
    (∀ v, D v = D (Pi.single 0 1) / pbar 0 * (pbar ⬝ᵥ v)) ∧
      (0 < D (Pi.single 0 1) → pbar ⬝ᵥ x = pbar ⬝ᵥ ω) := by
  have hcomp : ∀ l, D (Pi.single l 1) * pbar 0 = pbar l * D (Pi.single 0 1) := by
    intro l
    set v : Fin L → ℝ := pbar 0 • Pi.single l 1 - pbar l • Pi.single 0 1 with hv
    have hpv : pbar ⬝ᵥ v = 0 := by
      simp only [hv, dotProduct_sub, dotProduct_smul, smul_eq_mul]
      simp [dotProduct, Pi.single_apply]
      ring
    have hline : HasDerivAt (fun s : ℝ => x + s • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
    have hd := hD.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
    have hloc : IsLocalMax (fun s : ℝ => u (x + s • v)) 0 := by
      have hnn : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ k, 0 ≤ x k + s * v k := by
        rw [eventually_all]; intro k
        have hcont : Continuous fun s : ℝ => x k + s * v k := by fun_prop
        exact (hcont.continuousAt.eventually (lt_mem_nhds (by simpa using hx k))).mono
          fun _ h => h.le
      filter_upwards [hnn] with s hs
      simp only [zero_smul, add_zero]
      refine hmax (x + s • v) (fun k => by simpa using hs k) ?_
      simpa [dotProduct_add, dotProduct_smul, hpv] using hxb
    have := hloc.hasDerivAt_eq_zero hd
    simp only [hv, map_sub, map_smul, smul_eq_mul] at this
    linarith
  refine ⟨fun v => ?_, fun hD0 => ?_⟩
  · rw [clm_apply_eq_sum D v]
    simp only [dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    have := hcomp l
    have hp0 := hp 0
    field_simp
    linear_combination (v l) * this
  · refine le_antisymm hxb (not_lt.1 fun hlt => ?_)
    have hline : HasDerivAt (fun s : ℝ => x + s • Pi.single 0 1) (Pi.single 0 1) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single 0 (1 : ℝ))).const_add x
    have hd := (hD.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)).sub_const (u x)
    have hev := eventually_pos_of_hasDerivAt hd (by simp) hD0
    have hsmall : ∀ᶠ s in 𝓝[>] (0 : ℝ), s * pbar 0 < pbar ⬝ᵥ ω - pbar ⬝ᵥ x :=
      nhdsWithin_le_nhds ((continuous_id.mul continuous_const).continuousAt.eventually
        (gt_mem_nhds (by simpa using sub_pos.2 hlt)))
    obtain ⟨s, hs1, hs2, hs3⟩ := (hev.and (hsmall.and self_mem_nhdsWithin)).exists
    have hz : 0 ≤ x + s • Pi.single 0 (1 : ℝ) := fun k => by
      have := hx k
      have : 0 ≤ s * (Pi.single 0 (1 : ℝ) : Fin L → ℝ) k := by
        rw [Pi.single_apply]; split_ifs <;> simp [hs3.le]
      simpa using by linarith
    have hb : pbar ⬝ᵥ (x + s • Pi.single 0 1) ≤ pbar ⬝ᵥ ω := by
      simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, dotProduct_single, mul_one]
      linarith
    have := hmax _ hz hb
    simp only [Function.comp_apply] at hs1
    linarith

/-- **Footnote 32 and Exercise 20.G.4**, from static to intertemporal (MWG, p. 768, p. 786):
in an exchange economy with constant endowments `ω_i`, common discount factor `0 < δ < 1` and
concave utilities, the infinite constant repetition of an interior static Walrasian
equilibrium `(p̄, x)` (with `p̄ ≫ 0`, differentiable `u_i` and `∂_0 u_i(x_i) > 0`) is a Walrasian
equilibrium (Definition 20.G.1, with the null technology `Y = {0}` and any shares) with price
sequence `p_t = δ^t p̄`. -/
theorem exercise_20_G_4_repetition [NeZero L] {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    {u : ι → (Fin L → ℝ) → ℝ} (hconc : ∀ i, ConcaveOn ℝ (Set.Ici 0) (u i))
    {ω : ι → Fin L → ℝ} (hω : ∀ i, 0 ≤ ω i) {pbar : Fin L → ℝ} {x : ι → Fin L → ℝ}
    (he : StaticWalrasEq u ω pbar x) (hp : ∀ l, 0 < pbar l) (hx : ∀ i l, 0 < x i l)
    {D : ι → (Fin L → ℝ) →L[ℝ] ℝ} (hD : ∀ i, HasFDerivAt (u i) (D i) (x i))
    (hD0 : ∀ i, 0 < D i (Pi.single 0 1)) (θ : ι → ℕ → ℝ) :
    WalrasEqI (Set.Ici 0) {0} δ u (fun i _ => ω i) θ (fun t => δ ^ t • pbar) (fun _ => 0)
      (fun i _ => x i) := by
  obtain ⟨hx0, hbx, hmax, hclear⟩ := he
  have hδt : ∀ t, 0 ≤ δ ^ t := fun t => pow_nonneg hδ0.le t
  have hgeo := summable_geometric_of_lt_one hδ0.le hδ1
  have hpω : ∀ i, 0 ≤ pbar ⬝ᵥ ω i := fun i =>
    dotProduct_nonneg_of_nonneg (fun l => (hp l).le) (hω i)
  refine ⟨⟨0, fun t l => by simp⟩, ⟨∑ l, |pbar l|, fun t l => ?_⟩, fun t l => ?_, fun t => ?_,
    ⟨fun t => rfl, fun t z hz => ?_⟩, ?_, fun i => ?_, fun i => ?_⟩
  · rw [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg (hδt t)]
    calc δ ^ t * |pbar l| ≤ 1 * |pbar l| :=
          mul_le_mul_of_nonneg_right (pow_le_one₀ hδ0.le hδ1.le) (abs_nonneg _)
      _ ≤ ∑ l, |pbar l| := by
          rw [one_mul]
          exact Finset.single_le_sum (fun k _ => abs_nonneg (pbar k)) (Finset.mem_univ l)
  · simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    exact mul_nonneg (hδt t) (hp l).le
  · rcases t with _ | t <;> simp [netOutput, hclear]
  · rw [Set.mem_singleton_iff.1 hz]; simp [planValue, periodProfit]
  · have : periodProfit (fun t => δ ^ t • pbar) (fun _ => (0 : ProdPlan (Fin L))) = fun _ => 0 :=
      funext fun t => by simp [periodProfit, planValue]
    rw [this]; exact summable_zero
  · simpa [smul_dotProduct, smul_eq_mul] using hgeo.mul_right (pbar ⬝ᵥ ω i)
  -- utility maximization
  obtain ⟨hlamD, hbind⟩ := static_foc hp (hx i) (hbx i) (hmax i) (hD i)
  have hbx' := hbind (hD0 i)
  set lam := D i (Pi.single 0 1) / pbar 0 with hlam
  have hlam0 : 0 < lam := div_pos (hD0 i) (hp 0)
  have hW : (∑' t, θ i t * periodProfit (fun t => δ ^ t • pbar) (fun _ => 0) t
      + ∑' t, (δ ^ t • pbar) ⬝ᵥ ω i) = ∑' t, δ ^ t * (pbar ⬝ᵥ x i) := by
    simp [periodProfit, planValue, smul_dotProduct, hbx']
  rw [hW]
  have hsx : Summable fun t => δ ^ t * (pbar ⬝ᵥ x i) := hgeo.mul_right _
  refine ⟨⟨fun t => hx0 i, ⟨∑ l, |x i l|, fun t l =>
    Finset.single_le_sum (fun k _ => abs_nonneg (x i k)) (Finset.mem_univ l)⟩, fun T => ?_⟩,
    hgeo.mul_right _, fun c' hc' hs' => ?_⟩
  · simp only [smul_dotProduct, smul_eq_mul]
    exact hsx.sum_le_tsum _ fun t _ =>
      mul_nonneg (hδt t) (dotProduct_nonneg_of_nonneg (fun l => (hp l).le) (hx0 i))
  obtain ⟨hcs, hcle⟩ := expenditure_summable (p := fun t => δ ^ t • pbar)
    (fun t l => mul_nonneg (hδt t) (hp l).le) (fun t => hc'.1 t) hc'.2.2
  have hpt : ∀ t, δ ^ t * u i (c' t) ≤ δ ^ t * u i (x i)
      + lam * ((δ ^ t • pbar) ⬝ᵥ c' t) - lam * (δ ^ t * (pbar ⬝ᵥ x i)) := by
    intro t
    have g := MWG.GeneralEquilibriumExamples.concave_le_fderiv (hconc i)
      (show x i ∈ Set.Ici 0 from hx0 i) (hc'.1 t) (hD i)
    rw [hlamD, dotProduct_sub] at g
    rw [smul_dotProduct, smul_eq_mul]
    nlinarith [hδt t]
  have hsR : Summable fun t => δ ^ t * u i (x i)
      + lam * ((δ ^ t • pbar) ⬝ᵥ c' t) - lam * (δ ^ t * (pbar ⬝ᵥ x i)) :=
    ((hgeo.mul_right _).add (hcs.mul_left lam)).sub (hsx.mul_left lam)
  unfold discountedUtility
  calc ∑' t, δ ^ t * u i (c' t) ≤ ∑' t, (δ ^ t * u i (x i)
        + lam * ((δ ^ t • pbar) ⬝ᵥ c' t) - lam * (δ ^ t * (pbar ⬝ᵥ x i))) :=
        Summable.tsum_le_tsum hpt hs' hsR
    _ = ∑' t, δ ^ t * u i (x i) + lam * ∑' t, (δ ^ t • pbar) ⬝ᵥ c' t
        - lam * ∑' t, δ ^ t * (pbar ⬝ᵥ x i) := by
        rw [((hgeo.mul_right _).add (hcs.mul_left lam)).tsum_sub (hsx.mul_left lam),
          (hgeo.mul_right _).tsum_add (hcs.mul_left lam), tsum_mul_left, tsum_mul_left]
    _ ≤ ∑' t, δ ^ t * u i (x i) := by nlinarith

/-- **Footnote 32 and Exercise 20.G.4**, from intertemporal to static (MWG, p. 768, p. 786):
in an exchange economy with constant endowments `ω_i`, common discount factor `0 < δ < 1` and
strictly concave differentiable utilities, at an equilibrium whose consumptions satisfy the
first-order conditions (20.D.6) `λ_i p_t = δ^t ∇u_i(c_{it})` (Exercise 20.D.3) and exhaust the
budgets, consumption is constant over time, the price sequence is `p_t = δ^t p_0` (the rate of
interest is `(1 - δ)/δ` in every period), and `(p_0, (c_{i0})_i)` is a static Walrasian
equilibrium. Constancy: `∑_i λ_i⁻¹ (∇u_i(c_{it}) - ∇u_i(c_{i0})) · (c_{i0} - c_{it})` vanishes by
market clearing, while each term is positive unless `c_{it} = c_{i0}`. -/
theorem exercise_20_G_4_static [Nonempty ι] {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    {u : ι → (Fin L → ℝ) → ℝ} (hconc : ∀ i, StrictConcaveOn ℝ (Set.Ici 0) (u i))
    {ω : ι → Fin L → ℝ} {c : ι → ℕ → Fin L → ℝ} (hc0 : ∀ i t, 0 ≤ c i t)
    {D : ι → ℕ → (Fin L → ℝ) →L[ℝ] ℝ} (hD : ∀ i t, HasFDerivAt (u i) (D i t) (c i t))
    {p : ℕ → Fin L → ℝ} (hfoc : ∀ i, Foc20D6 δ p (D i))
    (hfeas : ∀ t, ∑ i, c i t = ∑ i, ω i)
    (hbud : ∀ i, HasSum (fun t => p t ⬝ᵥ c i t) (∑' t, p t ⬝ᵥ ω i)) :
    (∀ i t, c i t = c i 0) ∧ (∀ t, p t = δ ^ t • p 0) ∧
      StaticWalrasEq u ω (p 0) (fun i => c i 0) := by
  choose lam hlam hlamD using hfoc
  have hδt : ∀ t, 0 < δ ^ t := fun t => pow_pos hδ0 t
  have hDp : ∀ i t v, D i t v = lam i * (p t ⬝ᵥ v) / δ ^ t := fun i t v => by
    rw [hlamD i t v]; field_simp
  -- constancy of consumption
  have hconst : ∀ i t, c i t = c i 0 := by
    intro i₀ t
    set g : ι → ℝ := fun i => (lam i)⁻¹ * (D i t (c i 0 - c i t) + D i 0 (c i t - c i 0))
      with hg
    have hgnn : ∀ i, 0 ≤ g i ∧ (c i t ≠ c i 0 → 0 < g i) := by
      intro i
      have hpos : c i t ≠ c i 0 → 0 < D i t (c i 0 - c i t) + D i 0 (c i t - c i 0) := by
        intro hne
        have h1 := strictConcave_lt_fderiv (hconc i) (show c i t ∈ Set.Ici 0 from hc0 i t)
          (show c i 0 ∈ Set.Ici 0 from hc0 i 0) hne (hD i t)
        have h2 := strictConcave_lt_fderiv (hconc i) (show c i 0 ∈ Set.Ici 0 from hc0 i 0)
          (show c i t ∈ Set.Ici 0 from hc0 i t) (Ne.symm hne) (hD i 0)
        linarith
      have hli := inv_pos.2 (hlam i)
      refine ⟨?_, fun hne => mul_pos hli (hpos hne)⟩
      by_cases hne : c i t = c i 0
      · simp [hg, hne]
      · exact (mul_pos hli (hpos hne)).le
    have hsum : ∑ i, g i = 0 := by
      have e : ∀ i, g i = (p t ⬝ᵥ (c i 0 - c i t)) / δ ^ t + p 0 ⬝ᵥ (c i t - c i 0) := by
        intro i
        simp only [hg, hDp, pow_zero, div_one]
        field_simp [(hlam i).ne']
      simp only [e, Finset.sum_add_distrib, ← Finset.sum_div, ← dotProduct_sum,
        Finset.sum_sub_distrib, hfeas, sub_self, dotProduct_zero, zero_div, add_zero]
    have hall := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => (hgnn i).1).1 hsum i₀
      (Finset.mem_univ _)
    by_contra hne
    exact (hgnn i₀).2 hne |>.ne' hall
  -- proportional prices
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hDconst : ∀ i t, D i t = D i 0 := fun i t =>
    (hD i t).unique (by rw [hconst i t]; exact hD i 0)
  have hprice : ∀ t, p t = δ ^ t • p 0 := by
    intro t
    funext l
    have a := hlamD i₀ t (Pi.single l 1)
    have b := hlamD i₀ 0 (Pi.single l 1)
    rw [hDconst i₀ t] at a
    simp only [dotProduct_single, mul_one, pow_zero, one_mul] at a b
    simp only [Pi.smul_apply, smul_eq_mul]
    have : lam i₀ * p t l = lam i₀ * (δ ^ t * p 0 l) := by rw [a, ← b]; ring
    exact mul_left_cancel₀ (hlam i₀).ne' this
  refine ⟨hconst, hprice, fun i => hc0 i 0, fun i => ?_, fun i z hz hzb => ?_, hfeas 0⟩
  -- the static budget binds
  · have hgeo := hasSum_geometric_of_lt_one hδ0.le hδ1
    have h1 : HasSum (fun t => p t ⬝ᵥ c i t) (p 0 ⬝ᵥ c i 0 * (1 - δ)⁻¹) :=
      (hgeo.mul_left (p 0 ⬝ᵥ c i 0)).congr_fun fun t => by
        rw [hprice t, hconst i t, smul_dotProduct, smul_eq_mul]; ring
    have h2 : ∑' t, p t ⬝ᵥ ω i = p 0 ⬝ᵥ ω i * (1 - δ)⁻¹ :=
      ((hgeo.mul_left (p 0 ⬝ᵥ ω i)).congr_fun fun t => by
        rw [hprice t, smul_dotProduct, smul_eq_mul]; ring).tsum_eq
    have := (hbud i).unique h1
    rw [h2] at this
    have hinv : 0 < (1 - δ)⁻¹ := inv_pos.2 (by linarith)
    have := mul_right_cancel₀ hinv.ne' this
    exact this.symm.le
  -- static optimality
  · have g := MWG.GeneralEquilibriumExamples.concave_le_fderiv (hconc i).concaveOn
      (show c i 0 ∈ Set.Ici 0 from hc0 i 0) (show z ∈ Set.Ici 0 from hz) (hD i 0)
    have hb : p 0 ⬝ᵥ c i 0 = p 0 ⬝ᵥ ω i := by
      have hgeo := hasSum_geometric_of_lt_one hδ0.le hδ1
      have h1 : HasSum (fun t => p t ⬝ᵥ c i t) (p 0 ⬝ᵥ c i 0 * (1 - δ)⁻¹) :=
        (hgeo.mul_left (p 0 ⬝ᵥ c i 0)).congr_fun fun t => by
          rw [hprice t, hconst i t, smul_dotProduct, smul_eq_mul]; ring
      have h2 : ∑' t, p t ⬝ᵥ ω i = p 0 ⬝ᵥ ω i * (1 - δ)⁻¹ :=
        ((hgeo.mul_left (p 0 ⬝ᵥ ω i)).congr_fun fun t => by
          rw [hprice t, smul_dotProduct, smul_eq_mul]; ring).tsum_eq
      have := (hbud i).unique h1
      rw [h2] at this
      have hinv : 0 < (1 - δ)⁻¹ := inv_pos.2 (by linarith)
      exact (mul_right_cancel₀ hinv.ne' this).symm
    rw [hDp, pow_zero, div_one, dotProduct_sub] at g
    have := hlam i
    simp only
    nlinarith

/-! ### Exercise 20.G.3: the Negishi parametrization -/

/-- **Exercise 20.G.3(a)** (MWG, p. 786): the Pareto frontier of the two-consumer exchange
economy of Exercise 20.G.2 is parametrized by the ratio `r` of marginal utilities of wealth. An
interior allocation exhausting the aggregate endowment (`c_{0t} + c_{1t} = ω_t`), with concave
differentiable utilities and strictly positive marginal utilities, is Pareto optimal if and only
if `∇u_0(c_{0t}) = r ∇u_1(c_{1t})` in every period for some `r > 0`. -/
theorem exercise_20_G_3a [NeZero L] {δ : ℝ} (hδ : 0 < δ) {u : Fin 2 → (Fin L → ℝ) → ℝ}
    (hconc : ∀ i, ConcaveOn ℝ (Set.Ici 0) (u i)) {ω : ℕ → Fin L → ℝ}
    {c : Fin 2 → ℕ → Fin L → ℝ} (hint : ∀ i t l, 0 < c i t l) (hω : ∀ t, ∑ i, c i t = ω t)
    (hs : ∀ i, Summable fun t => δ ^ t * u i (c i t)) {D : Fin 2 → ℕ → (Fin L → ℝ) →L[ℝ] ℝ}
    (hD : ∀ i t, HasFDerivAt (u i) (D i t) (c i t)) (hpos : ∀ i t l, 0 < D i t (Pi.single l 1)) :
    ParetoOptimalExchange δ u ω c ↔ ∃ r : ℝ, 0 < r ∧ ∀ t, D 0 t = r • D 1 t := by
  constructor
  · intro hpo
    exact exercise_20_G_2_ratio hδ hpo hs hint hD hpos (by decide)
  rintro ⟨r, hr, hDr⟩
  have hc0 : ∀ i t, 0 ≤ c i t := fun i t l => (hint i t l).le
  refine ⟨hc0, fun t => (hω t).le, ?_⟩
  rintro ⟨c', hc'0, hfeas', hs', hge, j, hj⟩
  -- the weighted utility gain is pointwise nonpositive
  have hpt : ∀ t, δ ^ t * (u 0 (c' 0 t) - u 0 (c 0 t)) + r * (δ ^ t * (u 1 (c' 1 t) - u 1 (c 1 t)))
      ≤ 0 := by
    intro t
    have g0 := MWG.GeneralEquilibriumExamples.concave_le_fderiv (hconc 0)
      (show c 0 t ∈ Set.Ici 0 from hc0 0 t) (show c' 0 t ∈ Set.Ici 0 from hc'0 0 t) (hD 0 t)
    have g1 := MWG.GeneralEquilibriumExamples.concave_le_fderiv (hconc 1)
      (show c 1 t ∈ Set.Ici 0 from hc0 1 t) (show c' 1 t ∈ Set.Ici 0 from hc'0 1 t) (hD 1 t)
    have hsum : D 0 t (c' 0 t - c 0 t) + r * D 1 t (c' 1 t - c 1 t) ≤ 0 := by
      have e : D 0 t (c' 0 t - c 0 t) + r * D 1 t (c' 1 t - c 1 t)
          = D 0 t (c' 0 t + c' 1 t - ω t) := by
        rw [← hω t, Fin.sum_univ_two, hDr t]
        simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, map_sub,
          map_add]
        ring
      rw [e, clm_apply_eq_sum]
      refine Finset.sum_nonpos fun l _ => mul_nonpos_of_nonpos_of_nonneg ?_
        (hpos 0 t l).le
      have := hfeas' t l
      simp only [Fin.sum_univ_two, Pi.add_apply] at this
      simp only [Pi.sub_apply, Pi.add_apply]
      linarith
    have hδt := pow_pos hδ t
    have hA : (u 0 (c' 0 t) - u 0 (c 0 t)) + r * (u 1 (c' 1 t) - u 1 (c 1 t)) ≤ 0 := by
      have := mul_le_mul_of_nonneg_left (show u 1 (c' 1 t) - u 1 (c 1 t)
        ≤ D 1 t (c' 1 t - c 1 t) by linarith) hr.le
      linarith
    calc δ ^ t * (u 0 (c' 0 t) - u 0 (c 0 t)) + r * (δ ^ t * (u 1 (c' 1 t) - u 1 (c 1 t)))
        = δ ^ t * ((u 0 (c' 0 t) - u 0 (c 0 t)) + r * (u 1 (c' 1 t) - u 1 (c 1 t))) := by ring
      _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hδt.le hA
  have hsum0 := Summable.tsum_le_tsum hpt
    ((((hs' 0).sub (hs 0)).congr fun t => by ring).add
      ((((hs' 1).sub (hs 1)).congr fun t => by ring).mul_left r)) summable_zero
  rw [tsum_zero, ((((hs' 0).sub (hs 0)).congr fun t => by ring)).tsum_add
      ((((hs' 1).sub (hs 1)).congr fun t => by ring).mul_left r), tsum_mul_left] at hsum0
  have e0 : ∑' t, δ ^ t * (u 0 (c' 0 t) - u 0 (c 0 t))
      = discountedUtility δ (u 0) (c' 0) - discountedUtility δ (u 0) (c 0) := by
    unfold discountedUtility
    rw [← (hs' 0).tsum_sub (hs 0)]; exact tsum_congr fun t => by ring
  have e1 : ∑' t, δ ^ t * (u 1 (c' 1 t) - u 1 (c 1 t))
      = discountedUtility δ (u 1) (c' 1) - discountedUtility δ (u 1) (c 1) := by
    unfold discountedUtility
    rw [← (hs' 1).tsum_sub (hs 1)]; exact tsum_congr fun t => by ring
  rw [e0, e1] at hsum0
  have h0 := hge 0
  have h1 := hge 1
  fin_cases j
  · simp only [Fin.zero_eta, Fin.isValue] at hj
    nlinarith
  · simp only [Fin.mk_one, Fin.isValue] at hj
    nlinarith

/-- The **Negishi prices** of a point of the Pareto frontier: `p_t = δ^t ∇u_0(c_{0t})`. -/
def negishiPrice (δ : ℝ) (D0 : ℕ → (Fin L → ℝ) →L[ℝ] ℝ) (t : ℕ) : Fin L → ℝ :=
  fun l => δ ^ t * D0 t (Pi.single l 1)

/-- **Exercise 20.G.3(b)** (MWG, p. 786), the Negishi equation: let `c` be a point of the Pareto
frontier with parameter `r > 0` (`∇u_0(c_{0t}) = r ∇u_1(c_{1t})`, Exercise 20.G.3(a)), exhausting
the endowments `ω_0 + ω_1`, with bounded consumptions, endowments and marginal utilities,
`0 < δ < 1`, and Negishi prices `p_t = δ^t ∇u_0(c_{0t})`. Then `(p, c)` is a Walrasian
equilibrium (every consumer maximizes utility on the budget set with wealth `∑_t p_t · ω_{it}`)
if and only if the one equation in the one unknown `r`,
`∑_t p_t · c_{0t} - ∑_t p_t · ω_{0t} = 0` (consumer 0's wealth gap), holds. -/
theorem exercise_20_G_3b {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) {u : Fin 2 → (Fin L → ℝ) → ℝ}
    (hconc : ∀ i, ConcaveOn ℝ (Set.Ici 0) (u i)) {ω c : Fin 2 → ℕ → Fin L → ℝ} {B G r : ℝ}
    (hc0 : ∀ i t, 0 ≤ c i t) (hcB : ∀ i t l, c i t l ≤ B) (hω0 : ∀ i t, 0 ≤ ω i t)
    (hωB : ∀ i t l, ω i t l ≤ B) (hclear : ∀ t, c 0 t + c 1 t = ω 0 t + ω 1 t)
    (hs : ∀ i, Summable fun t => δ ^ t * u i (c i t)) {D : Fin 2 → ℕ → (Fin L → ℝ) →L[ℝ] ℝ}
    (hD : ∀ i t, HasFDerivAt (u i) (D i t) (c i t)) (hpos : ∀ t l, 0 ≤ D 0 t (Pi.single l 1))
    (hG : ∀ t l, D 0 t (Pi.single l 1) ≤ G) (hr : 0 < r) (hDr : ∀ t, D 0 t = r • D 1 t) :
    (∀ i, UtilityMax (Set.Ici 0) δ (u i) (negishiPrice δ (D 0))
        (∑' t, negishiPrice δ (D 0) t ⬝ᵥ ω i t) (c i)) ↔
      ∑' t, negishiPrice δ (D 0) t ⬝ᵥ c 0 t - ∑' t, negishiPrice δ (D 0) t ⬝ᵥ ω 0 t = 0 := by
  set p := negishiPrice δ (D 0) with hp
  have hδt : ∀ t, 0 ≤ δ ^ t := fun t => pow_nonneg hδ0.le t
  have hp0 : ∀ t, 0 ≤ p t := fun t l => mul_nonneg (hδt t) (hpos t l)
  -- value series of bounded nonnegative streams converge
  have hsumm : ∀ v : ℕ → Fin L → ℝ, (∀ t, 0 ≤ v t) → (∀ t l, v t l ≤ B) →
      Summable fun t => p t ⬝ᵥ v t := by
    intro v hv0 hvB
    refine Summable.of_nonneg_of_le (fun t => dotProduct_nonneg_of_nonneg (hp0 t) (hv0 t))
      (fun t => ?_) ((summable_geometric_of_lt_one hδ0.le hδ1).mul_right
        (Fintype.card (Fin L) * (G * B)))
    simp only [dotProduct]
    calc ∑ l, p t l * v t l ≤ ∑ _l : Fin L, δ ^ t * (G * B) := Finset.sum_le_sum fun l _ => by
          simp only [hp, negishiPrice]
          have := hpos t l
          have := hG t l
          have h3 : 0 ≤ v t l := hv0 t l
          have := hvB t l
          have := hδt t
          have hGB : D 0 t (Pi.single l 1) * v t l ≤ G * B := by nlinarith
          nlinarith
      _ = δ ^ t * (Fintype.card (Fin L) * (G * B)) := by simp; ring
  have hsc : ∀ i, Summable fun t => p t ⬝ᵥ c i t := fun i => hsumm _ (hc0 i) (hcB i)
  have hsω : ∀ i, Summable fun t => p t ⬝ᵥ ω i t := fun i => hsumm _ (hω0 i) (hωB i)
  -- total value identity
  have htot : ∑' t, p t ⬝ᵥ c 0 t + ∑' t, p t ⬝ᵥ c 1 t
      = ∑' t, p t ⬝ᵥ ω 0 t + ∑' t, p t ⬝ᵥ ω 1 t := by
    rw [← (hsc 0).tsum_add (hsc 1), ← (hsω 0).tsum_add (hsω 1)]
    exact tsum_congr fun t => by rw [← dotProduct_add, ← dotProduct_add, hclear t]
  -- the first-order identities `δ^t ∇u_0 = p_t`, `δ^t ∇u_1 = p_t / r`
  have hfoc0 : ∀ t v, δ ^ t * D 0 t v = p t ⬝ᵥ v := fun t v => by
    rw [clm_apply_eq_sum, Finset.mul_sum]
    simp only [hp, negishiPrice, dotProduct]
    exact Finset.sum_congr rfl fun l _ => by ring
  have hfoc1 : ∀ t v, δ ^ t * D 1 t v = r⁻¹ * (p t ⬝ᵥ v) := fun t v => by
    rw [← hfoc0, hDr t]
    simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
    field_simp
  constructor
  · intro hmax
    have h0 := (expenditure_summable hp0 (fun t => (hmax 0).1.1 t) (hmax 0).1.2.2).2
    have h1 := (expenditure_summable hp0 (fun t => (hmax 1).1.1 t) (hmax 1).1.2.2).2
    linarith
  intro hgap
  -- generic optimality from the gradient inequality, for a weight `κ > 0` with
  -- `δ^t ∇u_i = κ p_t` and binding budget
  have hopt : ∀ i (κ : ℝ), 0 < κ → (∀ t v, δ ^ t * D i t v = κ * (p t ⬝ᵥ v)) →
      ∑' t, p t ⬝ᵥ c i t = ∑' t, p t ⬝ᵥ ω i t →
      UtilityMax (Set.Ici 0) δ (u i) p (∑' t, p t ⬝ᵥ ω i t) (c i) := by
    intro i κ hκ hfi hbi
    refine ⟨⟨fun t => hc0 i t, ⟨max B 0, fun t l => ?_⟩, fun T => ?_⟩, hs i,
      fun c' hc' hs' => ?_⟩
    · rw [abs_of_nonneg (hc0 i t l)]; exact (hcB i t l).trans (le_max_left _ _)
    · rw [← hbi]
      exact (hsc i).sum_le_tsum _ fun t _ => dotProduct_nonneg_of_nonneg (hp0 t) (hc0 i t)
    obtain ⟨hcs, hcle⟩ := expenditure_summable hp0 (fun t => hc'.1 t) hc'.2.2
    have hpt : ∀ t, δ ^ t * u i (c' t)
        ≤ δ ^ t * u i (c i t) + κ * (p t ⬝ᵥ c' t) - κ * (p t ⬝ᵥ c i t) := by
      intro t
      have g := MWG.GeneralEquilibriumExamples.concave_le_fderiv (hconc i)
        (show c i t ∈ Set.Ici 0 from hc0 i t) (hc'.1 t) (hD i t)
      have e := hfi t (c' t - c i t)
      rw [dotProduct_sub] at e
      nlinarith [hδt t]
    have hsR : Summable fun t => δ ^ t * u i (c i t) + κ * (p t ⬝ᵥ c' t)
        - κ * (p t ⬝ᵥ c i t) := (((hs i).add (hcs.mul_left κ))).sub ((hsc i).mul_left κ)
    unfold discountedUtility
    calc ∑' t, δ ^ t * u i (c' t) ≤ ∑' t, (δ ^ t * u i (c i t) + κ * (p t ⬝ᵥ c' t)
          - κ * (p t ⬝ᵥ c i t)) := Summable.tsum_le_tsum hpt hs' hsR
      _ = ∑' t, δ ^ t * u i (c i t) + κ * ∑' t, p t ⬝ᵥ c' t
          - κ * ∑' t, p t ⬝ᵥ c i t := by
          rw [((hs i).add (hcs.mul_left κ)).tsum_sub ((hsc i).mul_left κ),
            (hs i).tsum_add (hcs.mul_left κ), tsum_mul_left, tsum_mul_left]
      _ ≤ ∑' t, δ ^ t * u i (c i t) := by rw [hbi] at *; nlinarith
  intro i
  fin_cases i
  · exact hopt 0 1 one_pos (fun t v => by rw [hfoc0, one_mul]) (by linarith)
  · exact hopt 1 r⁻¹ (inv_pos.2 hr) hfoc1 (by linarith)

end MWG.EquilibriumTime

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The additive form is cardinal: uniqueness (MWG Exercise 20.B.5, p. 783)

MWG, Chapter 20, Exercise 20.B.5: "Show also that the additively separable form of `V(·)` is a
cardinal property." The module `Utility` proves that positive affine transformations of `u`
preserve the form and that an ordinal transformation can destroy it. Here is the uniqueness
half: if `V(c) = ∑_t δ^t u(c_t)` and `W(c) = ∑_t δ^t w(c_t)` (one good, the same discount
factor `0 < δ < 1`, `u` and `w` continuous on `ℝ_+`, `u` strictly increasing) rank nonnegative
bounded streams in the same way, then `w = α u + β` on `ℝ_+` with `α > 0`
(`exercise_20_B_5_unique`).

Proof. Streams `(x, y, 0, 0, ...)` and `(z, z, 0, 0, ...)` are indifferent under `V` exactly when
`(1 + δ) u(z) = u(x) + δ u(y)`; so under `W` too, and `w` satisfies the weighted Jensen equation
with weight `λ = 1/(1 + δ)` in the `u`-scale (`additive_jensen`). A continuous solution of that
equation is affine in `u` on every interval: the set where `w` agrees with the affine
interpolation is closed, and the intermediate value theorem puts a point of it into every gap
(`affine_of_weighted_jensen`).
-/

namespace MWG.EquilibriumTime

/-- The one-good stream `(x, y, 0, 0, ...)`. -/
def twoDateStream (x y : ℝ) : ℕ → Fin 1 → ℝ :=
  fun t => if t = 0 then fun _ => x else if t = 1 then fun _ => y else 0

/-- Discounted utility of `(x, y, 0, 0, ...)`: that of the zero stream `(0, 0, 0, ...)` plus
`(u(x) - u(0)) + δ (u(y) - u(0))`. -/
theorem twoDate_value {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (u : ℝ → ℝ) (x y : ℝ) :
    discountedUtility δ (fun z => u (z 0)) (twoDateStream x y)
      = discountedUtility δ (fun z => u (z 0)) (twoDateStream 0 0) + (u x - u 0)
        + δ * (u y - u 0) := by
  have hs : Summable fun t => δ ^ t * (fun z : Fin 1 → ℝ => u (z 0)) (twoDateStream 0 0 t) :=
    ((summable_geometric_of_lt_one hδ0 hδ1).mul_right (u 0)).congr fun t => by
      simp only [twoDateStream]
      split_ifs <;> simp
  have hcc : ∀ τ, 2 ≤ τ → twoDateStream x y τ = twoDateStream 0 0 τ := fun τ hτ => by
    simp only [twoDateStream, show τ ≠ 0 by omega, show τ ≠ 1 by omega, ↓reduceIte]
  have := (discountedUtility_finite_change (u := fun z : Fin 1 → ℝ => u (z 0)) hcc hs).2
  have hsum : ∑ τ ∈ Finset.range 2, δ ^ τ * ((fun z : Fin 1 → ℝ => u (z 0))
      (twoDateStream x y τ) - (fun z : Fin 1 → ℝ => u (z 0)) (twoDateStream 0 0 τ))
      = (u x - u 0) + δ * (u y - u 0) := by
    simp [Finset.sum_range_succ, twoDateStream]
  rw [this, hsum]
  ring

/-- The two-date streams are nonnegative and bounded. -/
theorem twoDate_props {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    NonnegStream (twoDateStream x y) ∧ BoundedStream (twoDateStream x y) := by
  refine ⟨fun t i => ?_, ⟨max x y, fun t i => ?_⟩⟩
  · simp only [twoDateStream, Pi.zero_apply]
    split_ifs <;> simp [hx, hy]
  · simp only [twoDateStream]
    split_ifs
    · rw [abs_of_nonneg hx]; exact le_max_left _ _
    · rw [abs_of_nonneg hy]; exact le_max_right _ _
    · simp [le_max_of_le_left hx]

/-- Two additive utilities `V`, `W` with the same discount factor that rank nonnegative bounded
one-good streams alike. -/
def SameRanking (δ : ℝ) (u w : ℝ → ℝ) : Prop :=
  ∀ c c' : ℕ → Fin 1 → ℝ, NonnegStream c → NonnegStream c' → BoundedStream c →
    BoundedStream c' →
    (discountedUtility δ (fun z => u (z 0)) c ≤ discountedUtility δ (fun z => u (z 0)) c' ↔
      discountedUtility δ (fun z => w (z 0)) c ≤ discountedUtility δ (fun z => w (z 0)) c')

/-- A proved instance of `SameRanking`: `w = 2u + 3`. -/
theorem sameRanking_affine {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) {u : ℝ → ℝ} {M : ℝ}
    (hM : ∀ x, 0 ≤ x → |u x| ≤ M) : SameRanking δ u (fun x => 2 * u x + 3) := by
  intro c c' hc hc' _ _
  have hs : ∀ d : ℕ → Fin 1 → ℝ, NonnegStream d →
      Summable fun t => δ ^ t * (fun z : Fin 1 → ℝ => u (z 0)) (d t) :=
    fun d hd => summable_discounted hδ0 hδ1 (fun t => hM _ (hd t 0))
  exact (exercise_20_B_5_affine (u := fun z : Fin 1 → ℝ => u (z 0)) (a := 2) (b := 3) hδ0 hδ1
    two_pos (hs c' hc') (hs c hc)).symm

/-- Indifference transfers: if `(1 + δ) u(z) = u(x) + δ u(y)` then
`(1 + δ) w(z) = w(x) + δ w(y)`, for `x, y, z ≥ 0`. -/
theorem additive_jensen {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) {u w : ℝ → ℝ}
    (hrep : SameRanking δ u w) {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (h : (1 + δ) * u z = u x + δ * u y) : (1 + δ) * w z = w x + δ * w y := by
  obtain ⟨n1, b1⟩ := twoDate_props hx hy
  obtain ⟨n2, b2⟩ := twoDate_props hz hz
  have hV : discountedUtility δ (fun z => u (z 0)) (twoDateStream x y)
      = discountedUtility δ (fun z => u (z 0)) (twoDateStream z z) := by
    rw [twoDate_value hδ0 hδ1 u x y, twoDate_value hδ0 hδ1 u z z]; linarith
  have h1 := (hrep _ _ n1 n2 b1 b2).1 hV.le
  have h2 := (hrep _ _ n2 n1 b2 b1).1 hV.ge
  rw [twoDate_value hδ0 hδ1 w x y, twoDate_value hδ0 hδ1 w z z] at h1 h2
  linarith

/-- A function `w` that is continuous on `[a, b]` and satisfies the weighted Jensen equation in
the scale of a continuous strictly increasing `u` (`u(z) = λ u(x) + (1 - λ) u(y)` implies
`w(z) = λ w(x) + (1 - λ) w(y)`, `0 < λ < 1`) is affine in `u` on `[a, b]`. -/
theorem affine_of_weighted_jensen {u w : ℝ → ℝ} {a b lam : ℝ} (hab : a < b) (hlam0 : 0 < lam)
    (hlam1 : lam < 1) (hu : ContinuousOn u (Set.Icc a b)) (hw : ContinuousOn w (Set.Icc a b))
    (hmono : StrictMonoOn u (Set.Icc a b))
    (hj : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, ∀ z ∈ Set.Icc a b,
      u z = lam * u x + (1 - lam) * u y → w z = lam * w x + (1 - lam) * w y) :
    ∀ x ∈ Set.Icc a b, w x = w a + (w b - w a) / (u b - u a) * (u x - u a) := by
  have hua : u a < u b := hmono (Set.left_mem_Icc.2 hab.le) (Set.right_mem_Icc.2 hab.le) hab
  set K := (w b - w a) / (u b - u a) with hK
  set f : ℝ → ℝ := fun x => w x - (w a + K * (u x - u a)) with hf
  have hfc : ContinuousOn f (Set.Icc a b) :=
    hw.sub (continuousOn_const.add (continuousOn_const.mul (hu.sub continuousOn_const)))
  have hfa : f a = 0 := by simp [hf]
  have hfb : f b = 0 := by
    simp only [hf, hK]
    rw [div_mul_cancel₀ _ (sub_ne_zero.2 hua.ne')]
    ring
  have hfj : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, ∀ z ∈ Set.Icc a b,
      u z = lam * u x + (1 - lam) * u y → f z = lam * f x + (1 - lam) * f y := by
    intro x hx y hy z hz huz
    simp only [hf]
    rw [hj x hx y hy z hz huz, huz]
    ring
  intro z0 hz0
  by_contra hne
  have hne' : f z0 ≠ 0 := fun h => hne (by simp only [hf] at h; linarith)
  -- the last zero of `f` below `z0` and the first one above
  set S1 := Set.Icc a z0 ∩ f ⁻¹' {0} with hS1
  set S2 := Set.Icc z0 b ∩ f ⁻¹' {0} with hS2
  have hS1c : IsClosed S1 :=
    (hfc.mono (Set.Icc_subset_Icc le_rfl hz0.2)).preimage_isClosed_of_isClosed
      isClosed_Icc isClosed_singleton
  have hS2c : IsClosed S2 :=
    (hfc.mono (Set.Icc_subset_Icc hz0.1 le_rfl)).preimage_isClosed_of_isClosed
      isClosed_Icc isClosed_singleton
  have hS1n : S1.Nonempty := ⟨a, ⟨le_rfl, hz0.1⟩, hfa⟩
  have hS2n : S2.Nonempty := ⟨b, ⟨hz0.2, le_rfl⟩, hfb⟩
  have hS1b : BddAbove S1 := ⟨z0, fun x hx => hx.1.2⟩
  have hS2b : BddBelow S2 := ⟨z0, fun x hx => hx.1.1⟩
  set c := sSup S1 with hc
  set d := sInf S2 with hd
  have hcS : c ∈ S1 := hS1c.csSup_mem hS1n hS1b
  have hdS : d ∈ S2 := hS2c.csInf_mem hS2n hS2b
  have hcz : c < z0 := lt_of_le_of_ne hcS.1.2 fun h => hne' (h ▸ hcS.2)
  have hzd : z0 < d := lt_of_le_of_ne hdS.1.1 fun h => hne' (h.symm ▸ hdS.2)
  have hcab : c ∈ Set.Icc a b := ⟨hcS.1.1, hcS.1.2.trans hz0.2⟩
  have hdab : d ∈ Set.Icc a b := ⟨hz0.1.trans hdS.1.1, hdS.1.2⟩
  have hucd : u c < u d := hmono hcab hdab (hcz.trans hzd)
  -- a point of the gap where `f` vanishes
  have hsub : Set.Icc c d ⊆ Set.Icc a b := Set.Icc_subset_Icc hcab.1 hdab.2
  obtain ⟨m, hm, hum⟩ := intermediate_value_Icc (hcz.trans hzd).le (hu.mono hsub)
    (show lam * u c + (1 - lam) * u d ∈ Set.Icc (u c) (u d) by
      constructor <;> nlinarith)
  have hmc : c < m := lt_of_le_of_ne hm.1 fun h => by
    rw [← h] at hum; nlinarith
  have hmd : m < d := lt_of_le_of_ne hm.2 fun h => by
    rw [h] at hum; nlinarith
  have hfm : f m = 0 := by
    rw [hfj c hcab d hdab m (hsub hm) hum, hcS.2, hdS.2]; ring
  rcases le_total m z0 with hmz | hmz
  · have : m ≤ c := le_csSup hS1b ⟨⟨(hsub hm).1, hmz⟩, hfm⟩
    linarith
  · have : d ≤ m := csInf_le hS2b ⟨⟨hmz, (hsub hm).2⟩, hfm⟩
    linarith

/-- **Exercise 20.B.5**, uniqueness (MWG, p. 783): the additive form is cardinal. If
`V(c) = ∑_t δ^t u(c_t)` and `W(c) = ∑_t δ^t w(c_t)` rank nonnegative bounded one-good streams
alike, with `0 < δ < 1`, `u` and `w` continuous on `ℝ_+` and `u` strictly increasing, then
`w = α u + β` on `ℝ_+` for some `α > 0`. -/
theorem exercise_20_B_5_unique {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) {u w : ℝ → ℝ}
    (hu : ContinuousOn u (Set.Ici 0)) (hw : ContinuousOn w (Set.Ici 0))
    (hmono : StrictMonoOn u (Set.Ici 0)) (hrep : SameRanking δ u w) :
    ∃ α : ℝ, 0 < α ∧ ∃ β : ℝ, ∀ x, 0 ≤ x → w x = α * u x + β := by
  set lam := 1 / (1 + δ) with hlam
  have hlam0 : 0 < lam := by rw [hlam]; positivity
  have hlam1 : lam < 1 := by rw [hlam, div_lt_one (by linarith)]; linarith
  have hj : ∀ x, 0 ≤ x → ∀ y, 0 ≤ y → ∀ z, 0 ≤ z →
      u z = lam * u x + (1 - lam) * u y → w z = lam * w x + (1 - lam) * w y := by
    intro x hx y hy z hz h
    have h' : (1 + δ) * u z = u x + δ * u y := by
      rw [h, hlam]; field_simp; ring
    have := additive_jensen hδ0.le hδ1 hrep hx hy hz h'
    rw [hlam]; field_simp; linarith
  have hu01 : u 0 < u 1 := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 zero_le_one) one_pos
  -- `w` is strictly increasing between `0` and `1`
  have hw01 : w 0 < w 1 := by
    obtain ⟨n0, b0⟩ := twoDate_props (le_refl (0 : ℝ)) (le_refl (0 : ℝ))
    obtain ⟨n1, b1⟩ := twoDate_props zero_le_one (le_refl (0 : ℝ))
    have hV : ¬ discountedUtility δ (fun z => u (z 0)) (twoDateStream 1 0)
        ≤ discountedUtility δ (fun z => u (z 0)) (twoDateStream 0 0) := by
      rw [twoDate_value hδ0.le hδ1 u 1 0]; linarith
    have hW := mt (hrep _ _ n1 n0 b1 b0).2 hV
    rw [twoDate_value hδ0.le hδ1 w 1 0] at hW
    linarith
  set α := (w 1 - w 0) / (u 1 - u 0) with hα
  refine ⟨α, div_pos (by linarith) (by linarith), w 0 - α * u 0, fun x hx => ?_⟩
  set b := max x 1 with hb
  have hb1 : 1 ≤ b := le_max_right _ _
  have hsub : Set.Icc 0 b ⊆ Set.Ici 0 := fun z hz => Set.mem_Ici.2 hz.1
  have haff := affine_of_weighted_jensen (by linarith : (0 : ℝ) < b) hlam0 hlam1 (hu.mono hsub)
    (hw.mono hsub) (hmono.mono hsub) (fun x hx y hy z hz => hj x hx.1 y hy.1 z hz.1)
  have h1 := haff 1 ⟨zero_le_one, hb1⟩
  have hx' := haff x ⟨hx, le_max_left _ _⟩
  set K := (w b - w 0) / (u b - u 0) with hK
  have hKα : K = α := by
    rw [hα, eq_div_iff (by linarith)]; linarith
  rw [hx', hKα]; ring

end MWG.EquilibriumTime

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Overlapping generations (MWG Section 20.H, pp. 769-777)

MWG, Chapter 20, Section 20.H and Exercise 20.H.1 (p. 786). One good per period; generation `t`
lives at `t` (young, consumption `c_{bt}`) and `t + 1` (old, `c_{at}`) with utility
`u(c_b, c_a)` (a function on `ℝ × ℝ`), is endowed with `1 - ε` when young, and generation `0` owns
the asset paying `ε` per period plus a bubble `M ≥ 0`.

* The budget constraints (20.H.1)-(20.H.2) (`olgWealth`) and **Definition 20.H.1** (`OLGEq`), with
  a proved instance (`olg_autarky_linear`).
* The fundamental value of the asset is a lower bound for its no-arbitrage price
  (`fundamental_value_bound`, footnote 34).
* The steady state of Figure 20.H.1: `α = (1 - ε - γ)/(1 - γ) < 1` (`olg_steady_alpha`).
* **Proposition 20.H.1** (`proposition_20_H_1`) and **Proposition 20.H.2** (`proposition_20_H_2`).
* The nominal case: `p_{t+1} c_{at} = M` (`olg_nominal_identity`), so `M = 0` exactly at the
  no-trade equilibrium (`olg_bubble_zero_iff_autarky`); autarky is an equilibrium
  (`olg_autarky_equilibrium`) and, when the marginal rate of substitution at `(1, 0)` is below
  one, it is strictly Pareto dominated (`olg_autarky_dominated`).
* **Exercise 20.H.1**: no bubbles with finitely many consumers (`exercise_20_H_1`).
* The backward shift: a linear onto map of sequences with a nonzero kernel (`backward_shift`).
* Correction: in the monetary steady state the price sequence is constant only from `t = 1`
  (generation 0's choice fixes `p_1/p_0`; `monetary_steady_state_prices_log`).

The module `Closer20H` proves the optimality of the monetary steady state, the bubble
characterization of optimal nominal equilibria and Exercise 20.H.2(b) in the `√b + √a` economy,
and the cycles of Figures 20.H.5-20.H.6. OPEN: existence of equilibrium (Wilson 1981), the
general determinacy analysis (20.H.3) and Exercise 20.H.2(a), (c), (d).
-/

open Filter Topology

namespace MWG.EquilibriumTime

/-- The wealth of generation `t` (MWG, (20.H.1)-(20.H.2)): `(1 - ε) p_t` for `t > 0`, and for
generation `0` also the asset at its fundamental value `ε ∑_t p_t` plus the bubble `M`. -/
noncomputable def olgWealth (ε M : ℝ) (p : ℕ → ℝ) (t : ℕ) : ℝ :=
  if t = 0 then (1 - ε) * p 0 + ε * ∑' s, p s + M else (1 - ε) * p t

/-- **Definition 20.H.1** (MWG, p. 771): positive prices `p`, a bubble `M ≥ 0` and consumptions
`(c_{bt}, c_{at})` form a Walrasian equilibrium if every generation maximizes `u` on its budget set
and `c_{a,t-1} + c_{bt} = 1` (with `c_{a,-1} = 0`). Departures: prices are positive, and for a
real asset (`ε > 0`) the value `∑_t p_t` is finite (MWG, p. 773: otherwise generation 0 cannot be
in equilibrium). -/
structure OLGEq (u : ℝ × ℝ → ℝ) (ε : ℝ) (p : ℕ → ℝ) (M : ℝ) (cb ca : ℕ → ℝ) : Prop where
  /-- Prices are positive. -/
  pricesPos : ∀ t, 0 < p t
  /-- The bubble is nonnegative. -/
  bubble_nonneg : 0 ≤ M
  /-- A real asset has finite value. -/
  assetFinite : 0 < ε → Summable p
  /-- Consumption is nonnegative. -/
  cons_nonneg : ∀ t, 0 ≤ cb t ∧ 0 ≤ ca t
  /-- The budget constraint holds. -/
  budget : ∀ t, p t * cb t + p (t + 1) * ca t ≤ olgWealth ε M p t
  /-- Utility maximization. -/
  optimal : ∀ t b a, 0 ≤ b → 0 ≤ a → p t * b + p (t + 1) * a ≤ olgWealth ε M p t →
    u (b, a) ≤ u (cb t, ca t)
  /-- Feasibility at `t = 0`. -/
  feasible_zero : cb 0 = 1
  /-- Feasibility at `t + 1`. -/
  feasible : ∀ t, ca t + cb (t + 1) = 1

/-- **Footnote 34** (MWG, p. 771): if the asset's prices `A_t` (paid by the young at `t`) admit no
arbitrage, `A_t ≥ ε p_{t+1} + A_{t+1}` and `A ≥ 0`, then `A_0 ≥ ε (p_1 + ... + p_n)` for every
`n`; hence the value `ε p_0 + A_0` to generation 0 is at least the fundamental value `ε ∑_t p_t`. -/
theorem fundamental_value_bound {ε : ℝ} (hε : 0 ≤ ε) {p A : ℕ → ℝ} (hp : ∀ t, 0 ≤ p t)
    (hA : ∀ t, 0 ≤ A t) (hnoarb : ∀ t, ε * p (t + 1) + A (t + 1) ≤ A t) :
    (∀ n, ε * ∑ s ∈ Finset.range n, p (s + 1) ≤ A 0) ∧
      (Summable p → ε * ∑' s, p s ≤ ε * p 0 + A 0) := by
  have hgen : ∀ n t, ε * ∑ s ∈ Finset.range n, p (t + s + 1) + A (t + n) ≤ A t := by
    intro n
    induction n with
    | zero => intro t; simp
    | succ n ih =>
      intro t
      have h1 := ih (t + 1)
      have h2 := hnoarb t
      rw [Finset.sum_range_succ']
      simp only [show ∀ s, t + 1 + s + 1 = t + (s + 1) + 1 by omega,
        show t + 1 + n = t + (n + 1) by omega] at h1
      simp only [add_zero]
      nlinarith
  have hfin : ∀ n, ε * ∑ s ∈ Finset.range n, p (s + 1) ≤ A 0 := fun n => by
    have := hgen n 0
    simp only [zero_add] at this
    linarith [hA n]
  refine ⟨hfin, fun hs => ?_⟩
  have hs1 : Summable fun s => p (s + 1) := (summable_nat_add_iff 1).2 hs
  have hle : ∑' s, p (s + 1) ≤ A 0 / ε ∨ ε = 0 := by
    rcases eq_or_lt_of_le hε with h | h
    · exact Or.inr h.symm
    · left
      exact Real.tsum_le_of_sum_range_le (fun s => hp (s + 1)) fun n => by
        rw [le_div_iff₀ h]; linarith [hfin n]
  rw [hs.tsum_eq_zero_add]
  rcases hle with h | h
  · rcases eq_or_lt_of_le hε with h0 | h0
    · subst h0; simpa using hA 0
    · rw [le_div_iff₀ h0] at h; nlinarith
  · subst h; simpa using hA 0

/-- **The steady state of Figure 20.H.1** (MWG, p. 772): generations `t ≥ 1` consuming `(γ, 1 - γ)`
at prices `p_t = α^t` exhaust their budgets `(1 - ε) p_t` exactly when
`α = (1 - ε - γ)/(1 - γ)`, and `α < 1` when `ε > 0`. -/
theorem olg_steady_alpha {ε γ α : ℝ} (hγ : γ < 1) (t : ℕ) (hαpos : 0 < α) :
    (α ^ t * γ + α ^ (t + 1) * (1 - γ) = (1 - ε) * α ^ t ↔ α = (1 - ε - γ) / (1 - γ)) ∧
      (0 < ε → (1 - ε - γ) / (1 - γ) < 1) := by
  have h1γ : (1 : ℝ) - γ ≠ 0 := by linarith
  have hαt : 0 < α ^ t := pow_pos hαpos t
  constructor
  · rw [eq_div_iff h1γ, pow_succ]
    constructor
    · intro h
      have : α ^ t * (γ + α * (1 - γ) - (1 - ε)) = 0 := by linarith
      have := (mul_eq_zero.1 this).resolve_left hαt.ne'
      linarith
    · intro h
      have : α * (1 - γ) = 1 - ε - γ := h
      nlinarith
  · intro hε
    rw [div_lt_one (by linarith)]
    linarith

/-- The budget of an OLG generation binds when `u` is strictly increasing in first-period
consumption. -/
theorem olg_budget_binds {u : ℝ × ℝ → ℝ} (hmono : ∀ b b' a, 0 ≤ b → b < b' → u (b, a) < u (b', a))
    {ε : ℝ} {p : ℕ → ℝ} {M : ℝ} {cb ca : ℕ → ℝ} (he : OLGEq u ε p M cb ca) (t : ℕ) :
    p t * cb t + p (t + 1) * ca t = olgWealth ε M p t := by
  refine le_antisymm (he.budget t) ?_
  by_contra hlt
  push Not at hlt
  set gap := olgWealth ε M p t - (p t * cb t + p (t + 1) * ca t)
  have hgap : 0 < gap := by simp only [gap]; linarith
  have hpt := he.pricesPos t
  have := he.optimal t (cb t + gap / p t) (ca t) (by
    have := (he.cons_nonneg t).1; have := div_pos hgap hpt; linarith) (he.cons_nonneg t).2 (by
    rw [mul_add, mul_div_cancel₀ _ hpt.ne']; simp only [gap]; linarith)
  have hlt' := hmono (cb t) (cb t + gap / p t) (ca t) (he.cons_nonneg t).1
    (by have := div_pos hgap hpt; linarith)
  linarith

/-- A bundle that is at least as good as the optimum costs at least the wealth (local
nonsatiation in first-period consumption). -/
theorem olg_cost_ge {u : ℝ × ℝ → ℝ} (hmono : ∀ b b' a, 0 ≤ b → b < b' → u (b, a) < u (b', a))
    {ε : ℝ} {p : ℕ → ℝ} {M : ℝ} {cb ca : ℕ → ℝ} (he : OLGEq u ε p M cb ca) (t : ℕ) {b a : ℝ}
    (hb : 0 ≤ b) (ha : 0 ≤ a) (hge : u (cb t, ca t) ≤ u (b, a)) :
    olgWealth ε M p t ≤ p t * b + p (t + 1) * a := by
  by_contra hlt
  push Not at hlt
  set gap := olgWealth ε M p t - (p t * b + p (t + 1) * a)
  have hgap : 0 < gap := by simp only [gap]; linarith
  have hpt := he.pricesPos t
  have := he.optimal t (b + gap / p t) a (by have := div_pos hgap hpt; linarith) ha (by
    rw [mul_add, mul_div_cancel₀ _ hpt.ne']; simp only [gap]; linarith)
  have := hmono b (b + gap / p t) a hb (by have := div_pos hgap hpt; linarith)
  linarith

/-- A strictly better bundle costs strictly more than the wealth. -/
theorem olg_cost_gt {u : ℝ × ℝ → ℝ} {ε : ℝ} {p : ℕ → ℝ} {M : ℝ} {cb ca : ℕ → ℝ}
    (he : OLGEq u ε p M cb ca) (t : ℕ) {b a : ℝ} (hb : 0 ≤ b) (ha : 0 ≤ a)
    (hgt : u (cb t, ca t) < u (b, a)) : olgWealth ε M p t < p t * b + p (t + 1) * a := by
  by_contra hle
  push Not at hle
  exact absurd (he.optimal t b a hb ha hle) (not_le.2 hgt)

/-- The total wealth of all generations is `∑_t p_t + M` when `∑_t p_t < ∞`. -/
theorem olg_total_wealth {ε M : ℝ} {p : ℕ → ℝ} (hs : Summable p) :
    HasSum (olgWealth ε M p) (∑' t, p t + M) := by
  have hsum : Summable fun t => (1 - ε) * p t := hs.mul_left _
  have h := hsum.hasSum.add (hasSum_ite_eq 0 (ε * ∑' s, p s + M))
  have heq : (1 - ε) * ∑' t, p t + (ε * ∑' s, p s + M) = ∑' t, p t + M := by ring
  rw [tsum_mul_left, heq] at h
  refine h.congr_fun fun t => ?_
  rcases eq_or_ne t 0 with rfl | ht
  · simp [olgWealth]; ring
  · simp [olgWealth, ht]

/-- **Proposition 20.H.1** (MWG, p. 773): an equilibrium with `∑_t p_t < ∞` is Pareto optimal: no
feasible consumptions (`c'_{b0} ≤ 1`, `c'_{at} + c'_{b,t+1} ≤ 1`) make every generation at least as
well off and one strictly better off. `u` is strictly increasing in first-period consumption. -/
theorem proposition_20_H_1 {u : ℝ × ℝ → ℝ}
    (hmono : ∀ b b' a, 0 ≤ b → b < b' → u (b, a) < u (b', a)) {ε : ℝ} {p : ℕ → ℝ} {M : ℝ}
    {cb ca : ℕ → ℝ} (he : OLGEq u ε p M cb ca) (hs : Summable p) :
    ¬ ∃ cb' ca' : ℕ → ℝ, (∀ t, 0 ≤ cb' t ∧ 0 ≤ ca' t) ∧ cb' 0 ≤ 1 ∧
      (∀ t, ca' t + cb' (t + 1) ≤ 1) ∧ (∀ t, u (cb t, ca t) ≤ u (cb' t, ca' t)) ∧
      ∃ s, u (cb s, ca s) < u (cb' s, ca' s) := by
  rintro ⟨cb', ca', hnn, h0, hfeas, hge, s, hs'⟩
  have hp := he.pricesPos
  -- the costs `p_t c'_{bt} + p_{t+1} c'_{at}`
  set cost : ℕ → ℝ := fun t => p t * cb' t + p (t + 1) * ca' t with hcost
  have hcost0 : ∀ t, 0 ≤ cost t := fun t =>
    add_nonneg (mul_nonneg (hp t).le (hnn t).1) (mul_nonneg (hp (t + 1)).le (hnn t).2)
  -- partial sums of the costs are bounded by `∑ p`
  have hpart : ∀ T, ∑ t ∈ Finset.range T, cost t ≤ ∑' t, p t := by
    intro T
    have hle : ∀ T, ∑ t ∈ Finset.range T, cost t
        ≤ ∑ t ∈ Finset.range (T + 1), p t - p T * cb' T := by
      intro T
      induction T with
      | zero => simp; nlinarith [hp 0, h0]
      | succ T ih =>
        rw [Finset.sum_range_succ, Finset.sum_range_succ (fun t => p t) (T + 1)]
        have := hfeas T
        have hpT1 := hp (T + 1)
        simp only [hcost]
        nlinarith [mul_le_mul_of_nonneg_left this hpT1.le, (hnn (T + 1)).1]
    calc ∑ t ∈ Finset.range T, cost t ≤ ∑ t ∈ Finset.range (T + 1), p t - p T * cb' T := hle T
      _ ≤ ∑ t ∈ Finset.range (T + 1), p t := by
          linarith [mul_nonneg (hp T).le (hnn T).1]
      _ ≤ ∑' t, p t := hs.sum_le_tsum _ (fun t _ => (hp t).le)
  have hcs : Summable cost := summable_of_sum_range_le hcost0 hpart
  have hcle : ∑' t, cost t ≤ ∑' t, p t := Real.tsum_le_of_sum_range_le hcost0 hpart
  -- costs are at least the wealths, strictly for `s`
  have hw := olg_total_wealth (ε := ε) (M := M) hs
  have hge' : ∀ t, olgWealth ε M p t ≤ cost t := fun t =>
    olg_cost_ge hmono he t (hnn t).1 (hnn t).2 (hge t)
  have hgt' : olgWealth ε M p s < cost s := olg_cost_gt he s (hnn s).1 (hnn s).2 hs'
  have := hasSum_lt hge' hgt' hw hcs.hasSum
  linarith [he.bubble_nonneg]

/-- The value of total consumption up to `T`: `∑_{t ≤ T} (p_t c_{bt} + p_{t+1} c_{at}) =
∑_{t ≤ T} p_t + p_{T+1} c_{aT}`, by feasibility. -/
theorem olg_consumption_value {p cb ca : ℕ → ℝ} (h0 : cb 0 = 1) (hf : ∀ t, ca t + cb (t + 1) = 1)
    (T : ℕ) :
    ∑ t ∈ Finset.range (T + 1), (p t * cb t + p (t + 1) * ca t)
      = ∑ t ∈ Finset.range (T + 1), p t + p (T + 1) * ca T := by
  induction T with
  | zero => simp [h0]
  | succ T ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ (fun t => p t) (T + 1)]
    have := hf T
    have e : cb (T + 1) = 1 - ca T := by linarith
    rw [e]
    ring

/-- **Proposition 20.H.2** (MWG, p. 775): at an equilibrium with `∑_t p_t < ∞` there is no
bubble, `M = 0`: total wealth `∑ p_t + M` is spent, and total consumption is worth `∑ p_t`. -/
theorem proposition_20_H_2 {u : ℝ × ℝ → ℝ}
    (hmono : ∀ b b' a, 0 ≤ b → b < b' → u (b, a) < u (b', a)) {ε : ℝ} {p : ℕ → ℝ} {M : ℝ}
    {cb ca : ℕ → ℝ} (he : OLGEq u ε p M cb ca) (hs : Summable p) : M = 0 := by
  have hbind := olg_budget_binds hmono he
  have hw := olg_total_wealth (ε := ε) (M := M) hs
  have hp := he.pricesPos
  have hca1 : ∀ t, ca t ≤ 1 := fun t => by
    have := he.feasible t; linarith [(he.cons_nonneg (t + 1)).1]
  have hcons : HasSum (fun t => p t * cb t + p (t + 1) * ca t) (∑' t, p t) := by
    refine (hasSum_iff_tendsto_nat_of_nonneg (fun t => add_nonneg
      (mul_nonneg (hp t).le (he.cons_nonneg t).1) (mul_nonneg (hp (t + 1)).le
        (he.cons_nonneg t).2)) _).2 ?_
    refine (tendsto_add_atTop_iff_nat 1).1 ?_
    have h1 := (hs.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
    have h2 : Tendsto (fun T => p (T + 1) * ca T) atTop (𝓝 0) := by
      have hp0 := ((summable_nat_add_iff 1).2 hs).tendsto_atTop_zero
      refine squeeze_zero_norm (fun T => ?_) hp0
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (hp (T + 1)), abs_of_nonneg (he.cons_nonneg T).2]
      exact mul_le_of_le_one_right (hp (T + 1)).le (hca1 T)
    have := h1.add h2
    rw [add_zero] at this
    exact this.congr fun T => (olg_consumption_value he.feasible_zero he.feasible T).symm
  have := hw.unique (hcons.congr_fun fun t => (hbind t).symm)
  linarith

/-! ### The purely nominal asset -/

/-- **The nominal identity** (MWG, p. 774): with a purely nominal asset (`ε = 0`) and binding
budgets, `p_{t+1} c_{at} = p_t (1 - c_{bt}) = p_t c_{a,t-1} = ⋯ = M` for every `t`. -/
theorem olg_nominal_identity {u : ℝ × ℝ → ℝ}
    (hmono : ∀ b b' a, 0 ≤ b → b < b' → u (b, a) < u (b', a)) {p : ℕ → ℝ} {M : ℝ}
    {cb ca : ℕ → ℝ} (he : OLGEq u 0 p M cb ca) (t : ℕ) : p (t + 1) * ca t = M := by
  have hbind := olg_budget_binds hmono he
  induction t with
  | zero =>
    have := hbind 0
    simp [olgWealth, he.feasible_zero] at this
    linarith
  | succ t ih =>
    have := hbind (t + 1)
    simp only [olgWealth, show t + 1 ≠ 0 by omega, ↓reduceIte, sub_zero, one_mul] at this
    have hf := he.feasible t
    have e : cb (t + 1) = 1 - ca t := by linarith
    rw [e] at this
    nlinarith

/-- **`M = 0` only at the no-trade equilibrium** (MWG, p. 774): in the nominal case, the bubble
vanishes if and only if no generation consumes when old (and every generation consumes its
endowment `1` when young). -/
theorem olg_bubble_zero_iff_autarky {u : ℝ × ℝ → ℝ}
    (hmono : ∀ b b' a, 0 ≤ b → b < b' → u (b, a) < u (b', a)) {p : ℕ → ℝ} {M : ℝ}
    {cb ca : ℕ → ℝ} (he : OLGEq u 0 p M cb ca) :
    M = 0 ↔ (∀ t, ca t = 0) ∧ ∀ t, cb t = 1 := by
  have hid := olg_nominal_identity hmono he
  constructor
  · intro hM
    have hca : ∀ t, ca t = 0 := fun t => by
      have := hid t
      rw [hM] at this
      exact (mul_eq_zero.1 this).resolve_left (he.pricesPos (t + 1)).ne'
    refine ⟨hca, fun t => ?_⟩
    cases t with
    | zero => exact he.feasible_zero
    | succ t => have := he.feasible t; rw [hca t] at this; linarith
  · rintro ⟨hca, -⟩
    have := hid 0
    rw [hca 0, mul_zero] at this
    exact this.symm

/-- **The no-trade (nonmonetary) steady state is an equilibrium** (MWG, p. 773): if `u` is concave
on `ℝ²_+`, differentiable at `(1, 0)` with marginal utilities `u_b, u_a > 0`, and `β = u_b/u_a`
is the marginal rate of substitution there, then `M = 0`, the prices `p_t = β^{-t}` (so
`p_t / p_{t+1} = β`) and autarky `(1, 0)` form an equilibrium with a purely nominal asset. -/
theorem olg_autarky_equilibrium {u : ℝ × ℝ → ℝ}
    (hconc : ConcaveOn ℝ {x : ℝ × ℝ | 0 ≤ x.1 ∧ 0 ≤ x.2} u) {D : ℝ × ℝ →L[ℝ] ℝ}
    (hD : HasFDerivAt u D (1, 0)) {ub ua : ℝ} (hub : 0 < ub) (hua : 0 < ua)
    (hDf : ∀ v w, D (v, w) = ub * v + ua * w) :
    OLGEq u 0 (fun t => (ub / ua)⁻¹ ^ t) 0 (fun _ => 1) (fun _ => 0) := by
  have hβ : 0 < ub / ua := div_pos hub hua
  refine ⟨fun t => pow_pos (inv_pos.2 hβ) t, le_rfl, fun h => absurd h (lt_irrefl 0),
    fun t => ⟨zero_le_one, le_rfl⟩, fun t => ?_, fun t b a hb ha hbud => ?_, rfl,
    fun t => by norm_num⟩
  · rcases eq_or_ne t 0 with rfl | ht <;> simp [olgWealth, *]
  · have hw : olgWealth 0 0 (fun t => (ub / ua)⁻¹ ^ t) t = (ub / ua)⁻¹ ^ t := by
      rcases eq_or_ne t 0 with rfl | ht <;> simp [olgWealth, *]
    rw [hw] at hbud
    have hpt : 0 < (ub / ua)⁻¹ ^ t := pow_pos (inv_pos.2 hβ) t
    -- the budget is `b + (ua/ub) a ≤ 1`
    have hbud' : b + ua / ub * a ≤ 1 := by
      have : (ub / ua)⁻¹ ^ t * (b + ua / ub * a) ≤ (ub / ua)⁻¹ ^ t * 1 := by
        rw [pow_succ] at hbud
        have : (ub / ua)⁻¹ = ua / ub := inv_div ub ua
        rw [this] at hbud ⊢
        nlinarith
      exact le_of_mul_le_mul_left this hpt
    have g := concave_le_fderiv_normed hconc (by simp) (show (b, a) ∈ _ from ⟨hb, ha⟩) hD
    rw [Prod.mk_sub_mk, hDf] at g
    have : ub * (b - 1) + ua * (a - 0) ≤ 0 := by
      have h' : ua * a = ub * (ua / ub * a) := by field_simp
      nlinarith
    simpa using g.trans (by linarith)

/-- A proved instance of `OLGEq`: `u(b, a) = b + 2a`, autarky at prices `p_t = 2^t`. -/
theorem olg_autarky_linear :
    OLGEq (fun x => x.1 + 2 * x.2) 0 (fun t => (1 / 2 : ℝ)⁻¹ ^ t) 0 (fun _ => 1) (fun _ => 0) := by
  have hD : HasFDerivAt (fun x : ℝ × ℝ => x.1 + 2 * x.2)
      (ContinuousLinearMap.fst ℝ ℝ ℝ + (2 : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ) (1, 0) :=
    hasFDerivAt_fst.add (hasFDerivAt_snd.const_mul 2)
  have h := olg_autarky_equilibrium (u := fun x : ℝ × ℝ => x.1 + 2 * x.2)
    ((LinearMap.fst ℝ ℝ ℝ + (2 : ℝ) • LinearMap.snd ℝ ℝ ℝ).concaveOn
      (by
        intro x hx y hy a b ha hb hab
        simp only [Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
          Prod.smul_snd, smul_eq_mul] at *
        constructor <;> nlinarith [hx.1, hx.2, hy.1, hy.2]))
    hD one_pos two_pos (fun v w => by simp)
  simpa using h

/-- **Autarky is Pareto dominated when `β < 1`** (MWG, p. 773, Figure 20.H.2): if `u` is strictly
increasing in second-period consumption and differentiable at `(1, 0)` with `u_a > u_b`, then for
some `x ∈ (0, 1)` the feasible allocation in which generation 0 consumes `(1, x)` and every other
generation `(1 - x, x)` makes every generation strictly better off than autarky. -/
theorem olg_autarky_dominated {u : ℝ × ℝ → ℝ}
    (hmono_a : ∀ b a a', 0 ≤ a → a < a' → u (b, a) < u (b, a')) {D : ℝ × ℝ →L[ℝ] ℝ}
    (hD : HasFDerivAt u D (1, 0)) {ub ua : ℝ} (hDf : ∀ v w, D (v, w) = ub * v + ua * w)
    (hβ : ub < ua) :
    ∃ x : ℝ, 0 < x ∧ x < 1 ∧ u (1, 0) < u (1, x) ∧ u (1, 0) < u (1 - x, x) := by
  have hline : HasDerivAt (fun x : ℝ => ((1 - x, x) : ℝ × ℝ)) (-1, 1) 0 :=
    ((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub (hasDerivAt_id 0)).prodMk (hasDerivAt_id 0)
      |>.congr_deriv (by simp)
  have hd : HasDerivAt (fun x => u (1 - x, x) - u (1, 0)) (ua - ub) 0 := by
    have := (hD.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)).sub_const (u (1, 0))
    rw [hDf] at this
    exact this.congr_deriv (by ring)
  have hev := eventually_pos_of_hasDerivAt hd (by simp) (by linarith)
  have hlt1 : ∀ᶠ x in 𝓝[>] (0 : ℝ), x < 1 := nhdsWithin_le_nhds (Iio_mem_nhds one_pos)
  obtain ⟨x, hx, hx1, hxpos⟩ := (hev.and (hlt1.and self_mem_nhdsWithin)).exists
  refine ⟨x, hxpos, hx1, hmono_a 1 0 x le_rfl hxpos, ?_⟩
  linarith

/-- **Correction on the monetary steady state** (MWG, p. 774): with `u(b, a) = ln b + ln a` the
monetary steady state has generations `t ≥ 1` consuming `(1/2, 1/2)` at constant prices, but
generation 0 must consume `(1, 1/2)`, and its optimality forces `p₁ = 2 p₀`: the price sequence is
constant only from `t = 1` on. Precisely, if `(1, 1/2)` maximizes `ln b + ln a` on
`{b, a > 0 : p₀ b + p₁ a ≤ p₀ + p₁/2}`, then `p₁ = 2 p₀`. -/
theorem monetary_steady_state_prices_log {p₀ p₁ : ℝ}
    (hopt : ∀ b a, 0 < b → 0 < a → p₀ * b + p₁ * a ≤ p₀ * 1 + p₁ * (1 / 2) →
      Real.log b + Real.log a ≤ Real.log 1 + Real.log (1 / 2)) : p₁ = 2 * p₀ := by
  -- move along the budget line `b = 1 + s p₁`, `a = 1/2 - s p₀`
  have h1 : HasDerivAt (fun s : ℝ => 1 + s * p₁) p₁ 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).mul_const p₁).const_add 1
    simp only [id, one_mul] at this
    exact this
  have h2 : HasDerivAt (fun s : ℝ => 1 / 2 - s * p₀) (-p₀) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).mul_const p₀).const_sub (1 / 2)
    simp only [id, one_mul] at this
    exact this
  have hd : HasDerivAt (fun s => Real.log (1 + s * p₁) + Real.log (1 / 2 - s * p₀))
      (p₁ - 2 * p₀) 0 := by
    have := ((Real.hasDerivAt_log (by norm_num : (1 + 0 * p₁ : ℝ) ≠ 0)).comp 0 h1).add
      ((Real.hasDerivAt_log (by norm_num : (1 / 2 - 0 * p₀ : ℝ) ≠ 0)).comp 0 h2)
    exact this.congr_deriv (by norm_num; ring)
  set φ : ℝ → ℝ := fun s => Real.log (1 + s * p₁) + Real.log (1 / 2 - s * p₀) with hφ
  have hloc : IsLocalMax φ 0 := by
    have c1 : ∀ᶠ s in 𝓝 (0 : ℝ), 0 < 1 + s * p₁ :=
      (continuous_const.add (continuous_id.mul continuous_const)).continuousAt.eventually
        (lt_mem_nhds (by norm_num))
    have c2 : ∀ᶠ s in 𝓝 (0 : ℝ), 0 < 1 / 2 - s * p₀ :=
      (continuous_const.sub (continuous_id.mul continuous_const)).continuousAt.eventually
        (lt_mem_nhds (by norm_num))
    filter_upwards [c1, c2] with s h1 h2
    have := hopt _ _ h1 h2 (by nlinarith)
    simpa [hφ] using this
  have := hloc.hasDerivAt_eq_zero hd
  linarith

/-- **The backward shift** (MWG, p. 777): `f(x)_t = x_{t+1}` is linear and maps bounded sequences
onto bounded sequences, yet `f(x) = 0` has the nonzero bounded solution `(1, 0, 0, ...)`: an onto
linear map of an infinite-dimensional space need not be injective. -/
theorem backward_shift :
    let f : (ℕ → ℝ) → ℕ → ℝ := fun x t => x (t + 1)
    IsLinearMap ℝ f ∧
      (∀ y : ℕ → ℝ, (∃ B, ∀ t, |y t| ≤ B) → ∃ x : ℕ → ℝ, (∃ B, ∀ t, |x t| ≤ B) ∧ f x = y) ∧
      ∃ x : ℕ → ℝ, x ≠ 0 ∧ (∃ B, ∀ t, |x t| ≤ B) ∧ f x = 0 := by
  intro f
  refine ⟨⟨fun x y => rfl, fun c x => rfl⟩, fun y ⟨B, hB⟩ => ?_, ?_⟩
  · refine ⟨fun t => if t = 0 then 0 else y (t - 1), ⟨max B 0, fun t => ?_⟩, ?_⟩
    · change |(if t = 0 then 0 else y (t - 1))| ≤ max B 0
      split_ifs
      · simp
      · exact (hB _).trans (le_max_left _ _)
    · funext t; simp [f]
  · refine ⟨fun t => if t = 0 then 1 else 0, fun h => ?_, ⟨1, fun t => ?_⟩, ?_⟩
    · have := congrFun h 0; simp at this
    · change |(if t = 0 then (1 : ℝ) else 0)| ≤ 1
      split_ifs <;> simp
    · funext t; simp [f]

/-- **Exercise 20.H.1** (MWG, p. 786): with finitely many consumers there are no bubbles. If the
consumers of Section 20.G had extra wealth `M_i ≥ 0` (all budgets binding:
`∑_t p_t · c_{it} = w_i + M_i`), feasibility, short-run profit maximization and truncation force
`M_i = 0` for every consumer. -/
theorem exercise_20_H_1 {L : ℕ} {ι : Type*} [Fintype ι] {Y : Set (ProdPlan (Fin L))}
    (htr : ∀ z ∈ Y, (z.1, 0) ∈ Y) {p : ℕ → Fin L → ℝ} {y : ℕ → ProdPlan (Fin L)}
    (hmy : MyopicProfitMax Y p y) {ω c : ι → ℕ → Fin L → ℝ} {θ : ι → ℕ → ℝ}
    (hθ0 : ∀ i t, 0 ≤ θ i t) (hθ1 : ∀ t, ∑ i, θ i t = 1)
    (hπ : Summable (periodProfit p y)) (hω : ∀ i, Summable fun t => p t ⬝ᵥ ω i t)
    (hfeas : ∀ t, ∑ i, c i t = netOutput y t + ∑ i, ω i t) {Mb : ι → ℝ} (hM : ∀ i, 0 ≤ Mb i)
    (hbind : ∀ i, HasSum (fun t => p t ⬝ᵥ c i t) (wealthI θ p y ω i + Mb i)) :
    ∀ i, Mb i = 0 := by
  obtain ⟨hWs, hW⟩ := sum_wealthI hθ0 hθ1 hπ hω
  have htot : HasSum (fun t => p t ⬝ᵥ ∑ i, c i t) (∑ i, (wealthI θ p y ω i + Mb i)) := by
    have := hasSum_sum (s := Finset.univ) fun i _ => hbind i
    exact this.congr_fun fun t => by rw [dotProduct_sum]
  -- partial sums of the value of consumption are below those of wealth
  have hpart : ∀ T, ∑ t ∈ Finset.range (T + 1), p t ⬝ᵥ ∑ i, c i t
      ≤ ∑ t ∈ Finset.range (T + 1), (periodProfit p y t + p t ⬝ᵥ ∑ i, ω i t) := by
    intro T
    have h1 := sum_value_netOutput p y T
    have h2 : 0 ≤ p (T + 1) ⬝ᵥ (y T).2 := by
      have := hmy.2 T _ (htr _ (hmy.1 T))
      simp [periodProfit, planValue] at this
      linarith
    simp only [hfeas, dotProduct_add, Finset.sum_add_distrib] at h1 ⊢
    linarith
  have hle := le_of_tendsto_of_tendsto
    ((htot.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1))
    ((hWs.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)) (Eventually.of_forall hpart)
  rw [← hW, Finset.sum_add_distrib] at hle
  have hsum0 : ∑ i, Mb i ≤ 0 := by linarith
  intro i
  have := Finset.single_le_sum (fun j _ => hM j) (Finset.mem_univ i)
  linarith [hM i]

end MWG.EquilibriumTime

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Overlapping generations: optimality, bubbles and cycles (MWG Section 20.H)

MWG, Chapter 20, Section 20.H, p. 774 and Figure 20.H.3 ("the monetary steady state is Pareto
optimal. We will not give a rigorous proof of this").

The monetary steady state of the purely nominal economy (generation 0 consumes `(1, 1 - γ)`,
every later generation `(γ, 1 - γ)`) is Pareto optimal (`monetary_steady_state_optimal`) when
`u` is continuous on `ℝ²_+`, nondecreasing in first-period and strictly increasing in
second-period consumption, and `(γ, 1 - γ)` is the unique maximizer of `u` on
`{b + a ≤ 1}` (the budget set of a generation `t ≥ 1` at the constant steady-state prices,
which is the equilibrium condition of the steady state plus strict quasiconcavity).

The proof makes Figure 20.H.3's "unfeasible chain of compensations" precise. With
`d_t = c'_{at} - (1 - γ)` the extra old-age consumption of generation `t`, feasibility and
the uniqueness of the maximizer give `0 ≤ d_0 ≤ d_1 ≤ ⋯ ≤ γ`, and a strict improvement for some
generation makes some `d_s > 0`. The limit `D > 0` of `d_t` then gives, by continuity,
`u(γ - D, 1 - γ + D) ≥ u(γ, 1 - γ)` on the line `b + a = 1`, a contradiction.

A proved instance: `u(b, a) = √b + √a` with `γ = 1/2` (`sqrt_utility_unique_max`,
`monetary_steady_state_optimal_sqrt`).

**Optimal nominal equilibria and the bubble** (p. 774, "which we leave without proof"): in the
stationary economy `u(b, a) = √b + √a` with a purely nominal asset, an equilibrium is Pareto
optimal (`OLGParetoOptimal`) if and only if its real bubble `M/p_{t+1}` is bounded away from zero
(`olg_sqrt_optimal_iff_bubble`). Every equilibrium is either the monetary steady state or has
relative prices `r_k = p_{k+2}/p_{k+1}` with `r_{k+1} = r_k² + r_k - 1`, `r_0 > 1`, a vanishing real
bubble, and is Pareto dominated by the steady state (`olg_sqrt_classification`; demand:
`sqrt_demand`, `olg_sqrt_demand`). This economy satisfies the determinacy condition (20.H.3)
(`sqrt_determinacy_condition`), and its monetary steady state is the only Pareto optimal
nominal equilibrium: Exercise 20.H.2(b) for this economy (`exercise_20_H_2b_sqrt`).

**Cycles** (Figures 20.H.5-20.H.6, p. 777): explicit period-2 and period-3 equilibrium paths of the
nominal economy with concave, increasing, piecewise linear utilities
(`figure_20_H_5_period_two`, `figure_20_H_6_period_three`).
-/

open Filter Topology

namespace MWG.EquilibriumTime

/-- First-period consumption in the monetary steady state: `1` for generation 0, `γ` after. -/
noncomputable def monetaryCb (γ : ℝ) (t : ℕ) : ℝ := if t = 0 then 1 else γ

/-- **The monetary steady state is Pareto optimal** (MWG, p. 774, Figure 20.H.3). Let `u` be
continuous on `ℝ²_+`, nondecreasing in first-period consumption, strictly increasing in
second-period consumption, and let `(γ, 1 - γ)` be the unique maximizer of `u` on
`{(b, a) ≥ 0 : b + a ≤ 1}`. Then no feasible allocation (`c'_{b0} ≤ 1`,
`c'_{at} + c'_{b,t+1} ≤ 1`) makes every generation at least as well off as in the monetary
steady state (generation 0 at `(1, 1 - γ)`, generation `t ≥ 1` at `(γ, 1 - γ)`) and some
generation strictly better off. -/
theorem monetary_steady_state_optimal {u : ℝ × ℝ → ℝ} {γ : ℝ}
    (hcont : ContinuousOn u {x | 0 ≤ x.1 ∧ 0 ≤ x.2})
    (hmono_b : ∀ b b' a, 0 ≤ b → b ≤ b' → 0 ≤ a → u (b, a) ≤ u (b', a))
    (hmono_a : ∀ b a a', 0 ≤ b → 0 ≤ a → a < a' → u (b, a) < u (b, a'))
    (hmax : ∀ b a, 0 ≤ b → 0 ≤ a → b + a ≤ 1 → (b, a) ≠ (γ, 1 - γ) → u (b, a) < u (γ, 1 - γ)) :
    ¬ ∃ cb' ca' : ℕ → ℝ, (∀ t, 0 ≤ cb' t ∧ 0 ≤ ca' t) ∧ cb' 0 ≤ 1 ∧
      (∀ t, ca' t + cb' (t + 1) ≤ 1) ∧
      (∀ t, u (monetaryCb γ t, 1 - γ) ≤ u (cb' t, ca' t)) ∧
      ∃ s, u (monetaryCb γ s, 1 - γ) < u (cb' s, ca' s) := by
  rintro ⟨cb', ca', hnn, h0, hfeas, hge, s, hs⟩
  -- a later generation at least as well off consumes at least `1` in total
  have hsum : ∀ t, u (γ, 1 - γ) ≤ u (cb' (t + 1), ca' (t + 1)) →
      1 ≤ cb' (t + 1) + ca' (t + 1) := fun t h => by
    by_contra hlt
    push Not at hlt
    have hne : (cb' (t + 1), ca' (t + 1)) ≠ (γ, 1 - γ) := fun he => by
      simp only [Prod.mk.injEq] at he
      linarith [he.1, he.2]
    linarith [hmax _ _ (hnn _).1 (hnn _).2 hlt.le hne]
  have hgeS : ∀ t, u (γ, 1 - γ) ≤ u (cb' (t + 1), ca' (t + 1)) := fun t => by
    simpa [monetaryCb] using hge (t + 1)
  -- generation 0 cannot lose old-age consumption
  have hca0 : 1 - γ ≤ ca' 0 := by
    by_contra hlt
    push Not at hlt
    have h1 := hmono_b _ _ _ (hnn 0).1 h0 (hnn 0).2
    have h2 := hmono_a 1 _ _ zero_le_one (hnn 0).2 hlt
    have h3 := hge 0
    simp only [monetaryCb, ↓reduceIte] at h3
    linarith
  -- the extra old-age consumption `d_t` is nondecreasing
  set d : ℕ → ℝ := fun t => ca' t - (1 - γ) with hd
  have hstep : ∀ t, d t ≤ d (t + 1) := fun t => by
    have := hsum t (hgeS t)
    have := hfeas t
    simp only [hd]
    linarith
  have hmono : Monotone d := monotone_nat_of_le_succ hstep
  have hd0 : 0 ≤ d 0 := by simp only [hd]; linarith
  have hdγ : ∀ t, d t ≤ γ - cb' (t + 1) := fun t => by
    have := hfeas t
    simp only [hd]
    linarith
  have hdle : ∀ t, d t ≤ γ := fun t => by linarith [hdγ t, (hnn (t + 1)).1]
  -- some `d_s` is positive
  have hpos : ∃ s, 0 < d s := by
    rcases s with _ | r
    · refine ⟨0, ?_⟩
      by_contra hle
      push Not at hle
      have hca : ca' 0 ≤ 1 - γ := by simp only [hd] at hle; linarith
      have h1 := hmono_b _ _ _ (hnn 0).1 h0 (hnn 0).2
      have h2 : u (1, ca' 0) ≤ u (1, 1 - γ) := by
        rcases eq_or_lt_of_le hca with h | h
        · rw [h]
        · exact (hmono_a 1 _ _ zero_le_one (hnn 0).2 h).le
      simp only [monetaryCb, ↓reduceIte] at hs
      linarith
    · refine ⟨r + 1, ?_⟩
      have hs' : u (γ, 1 - γ) < u (cb' (r + 1), ca' (r + 1)) := by
        simpa [monetaryCb] using hs
      have hgt : 1 < cb' (r + 1) + ca' (r + 1) := by
        by_contra hle
        push Not at hle
        rcases eq_or_ne (cb' (r + 1), ca' (r + 1)) (γ, 1 - γ) with he | hne
        · rw [he] at hs'; exact lt_irrefl _ hs'
        · linarith [hmax _ _ (hnn _).1 (hnn _).2 hle hne]
      have := hfeas r
      have := hmono (Nat.zero_le r)
      simp only [hd] at this ⊢
      linarith
  obtain ⟨s, hds⟩ := hpos
  -- the limit `D` of `d_t`
  have hbdd : BddAbove (Set.range d) := ⟨γ, by rintro _ ⟨t, rfl⟩; exact hdle t⟩
  set D := ⨆ t, d t with hD
  have hlim : Tendsto d atTop (𝓝 D) := tendsto_atTop_ciSup hmono hbdd
  have hDpos : 0 < D := lt_of_lt_of_le hds (le_ciSup hbdd s)
  have hDle : D ≤ γ := ciSup_le hdle
  -- every generation `t + 1` is at least as well off at `(γ - d_t, 1 - γ + d_{t+1})`
  have hpt : ∀ t, u (γ, 1 - γ) ≤ u (γ - d t, 1 - γ + d (t + 1)) := fun t => by
    have e : ca' (t + 1) = 1 - γ + d (t + 1) := by simp only [hd]; ring
    have h1 := hmono_b (cb' (t + 1)) (γ - d t) (ca' (t + 1)) (hnn _).1 (by linarith [hdγ t])
      (hnn _).2
    calc u (γ, 1 - γ) ≤ u (cb' (t + 1), ca' (t + 1)) := hgeS t
      _ ≤ u (γ - d t, ca' (t + 1)) := h1
      _ = u (γ - d t, 1 - γ + d (t + 1)) := by rw [e]
  -- pass to the limit
  have hseq : Tendsto (fun t => ((γ - d t, 1 - γ + d (t + 1)) : ℝ × ℝ)) atTop
      (𝓝 (γ - D, 1 - γ + D)) :=
    (tendsto_const_nhds.sub hlim).prodMk_nhds
      (tendsto_const_nhds.add (hlim.comp (tendsto_add_atTop_nat 1)))
  have hmem : ∀ t, ((γ - d t, 1 - γ + d (t + 1)) : ℝ × ℝ) ∈ {x : ℝ × ℝ | 0 ≤ x.1 ∧ 0 ≤ x.2} :=
    fun t => ⟨by linarith [hdγ t, (hnn (t + 1)).1], by
      have := (hnn (t + 1)).2; simp only [hd] at this ⊢; linarith⟩
  have hDmem : ((γ - D, 1 - γ + D) : ℝ × ℝ) ∈ {x : ℝ × ℝ | 0 ≤ x.1 ∧ 0 ≤ x.2} :=
    ⟨by simp only; linarith, by
      have h1 : d 0 ≤ D := le_ciSup hbdd 0
      have h2 : d 0 = ca' 0 - (1 - γ) := rfl
      simp only
      linarith [(hnn 0).2]⟩
  have hu : Tendsto (fun t => u (γ - d t, 1 - γ + d (t + 1))) atTop (𝓝 (u (γ - D, 1 - γ + D))) :=
    (hcont _ hDmem).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hseq, Eventually.of_forall hmem⟩)
  have hlimge : u (γ, 1 - γ) ≤ u (γ - D, 1 - γ + D) :=
    ge_of_tendsto hu (Eventually.of_forall hpt)
  have hne : ((γ - D, 1 - γ + D) : ℝ × ℝ) ≠ (γ, 1 - γ) := fun he => by
    simp only [Prod.mk.injEq] at he
    linarith [he.1]
  have := hmax _ _ hDmem.1 hDmem.2 (by linarith) hne
  linarith

/-- The instance `u(b, a) = √b + √a`: on `{(b, a) ≥ 0 : b + a ≤ 1}` it has the unique maximizer
`(1/2, 1/2)`. -/
theorem sqrt_utility_unique_max (b a : ℝ) (hb : 0 ≤ b) (ha : 0 ≤ a) (hba : b + a ≤ 1)
    (hne : (b, a) ≠ (1 / 2, 1 - 1 / 2)) :
    Real.sqrt b + Real.sqrt a < Real.sqrt (1 / 2) + Real.sqrt (1 - 1 / 2) := by
  have sb := Real.sq_sqrt hb
  have sa := Real.sq_sqrt ha
  have s2 : Real.sqrt (1 / 2) ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)
  have hpos2 : 0 < Real.sqrt (1 / 2) := Real.sqrt_pos.2 (by norm_num)
  have e : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  rw [e] at hne ⊢
  -- `(√b + √a)² ≤ 2(b + a) ≤ 2`, with equality only at `b = a = 1/2`
  have hx := Real.sqrt_nonneg b
  have hy := Real.sqrt_nonneg a
  by_contra hge
  push Not at hge
  have hsq : 2 ≤ (Real.sqrt b + Real.sqrt a) ^ 2 := by nlinarith
  have heq : Real.sqrt b = Real.sqrt a := by nlinarith [sq_nonneg (Real.sqrt b - Real.sqrt a)]
  have hb2 : b = 1 / 2 := by nlinarith
  have ha2 : a = 1 / 2 := by nlinarith
  exact hne (by rw [hb2, ha2])

/-- **The monetary steady state is Pareto optimal**, proved instance (MWG, p. 774):
`u(b, a) = √b + √a`, `γ = 1/2`. -/
theorem monetary_steady_state_optimal_sqrt :
    ¬ ∃ cb' ca' : ℕ → ℝ, (∀ t, 0 ≤ cb' t ∧ 0 ≤ ca' t) ∧ cb' 0 ≤ 1 ∧
      (∀ t, ca' t + cb' (t + 1) ≤ 1) ∧
      (∀ t, Real.sqrt (monetaryCb (1 / 2) t) + Real.sqrt (1 - 1 / 2)
        ≤ Real.sqrt (cb' t) + Real.sqrt (ca' t)) ∧
      ∃ s, Real.sqrt (monetaryCb (1 / 2) s) + Real.sqrt (1 - 1 / 2)
        < Real.sqrt (cb' s) + Real.sqrt (ca' s) :=
  monetary_steady_state_optimal (u := fun x => Real.sqrt x.1 + Real.sqrt x.2)
    ((Real.continuous_sqrt.comp continuous_fst).add
      (Real.continuous_sqrt.comp continuous_snd)).continuousOn
    (fun b b' a _ hbb' _ => by
      simp only
      linarith [Real.sqrt_le_sqrt hbb'])
    (fun b a a' _ ha haa' => by
      simp only
      linarith [Real.sqrt_lt_sqrt ha haa'])
    (fun b a hb ha hba hne => sqrt_utility_unique_max b a hb ha hba hne)

/-! ### A period-2 equilibrium path (Figure 20.H.5) -/

/-- The utility of the period-2 example: `u(b, a) = min(b + 2a, 2b + a - 1/4)`, concave,
piecewise linear and increasing (complementary consumptions, no inferior goods). Its kink line
`b = a + 1/4` is the offer curve for relative prices `p_{t+1}/p_t ∈ [1/2, 2]`. -/
noncomputable def cycleU (x : ℝ × ℝ) : ℝ := min (x.1 + 2 * x.2) (2 * x.1 + x.2 - 1 / 4)

/-- Old-age consumption on the period-2 path: `1/3` for even `t`, `5/12` for odd `t`. -/
noncomputable def cycleCa (t : ℕ) : ℝ := if t % 2 = 0 then 1 / 3 else 5 / 12

/-- Young-age consumption on the period-2 path: `1` for generation 0, then `1 - c_{a,t-1}`. -/
noncomputable def cycleCb (t : ℕ) : ℝ := if t = 0 then 1 else 1 - cycleCa (t - 1)

/-- The prices of the period-2 path: `1, 2, 8/5, 2, 8/5, ...`. -/
noncomputable def cyclePrice (t : ℕ) : ℝ := if t = 0 then 1 else if t % 2 = 0 then 8 / 5 else 2

/-- **Figure 20.H.5** (MWG, p. 777): a period-2 equilibrium path with complementary
consumptions, in the purely nominal case. With `u(b, a) = min(b + 2a, 2b + a - 1/4)`, the
prices `1, 2, 8/5, 2, 8/5, ...`, the bubble `M = 2/3` and generations alternating between
`(2/3, 5/12)` (odd `t`) and `(7/12, 1/3)` (even `t ≥ 2`) form an equilibrium (Definition 20.H.1)
whose allocation has period exactly 2. -/
theorem figure_20_H_5_period_two :
    OLGEq cycleU 0 cyclePrice (2 / 3) cycleCb cycleCa ∧
      (∀ t, 1 ≤ t → cycleCb (t + 2) = cycleCb t ∧ cycleCa (t + 2) = cycleCa t) ∧
      (cycleCb 1, cycleCa 1) ≠ (cycleCb 2, cycleCa 2) := by
  have hpar : ∀ t : ℕ, (t + 2) % 2 = t % 2 := fun t => by omega
  refine ⟨⟨fun t => ?_, by norm_num, fun h => absurd h (lt_irrefl 0), fun t => ?_,
    fun t => ?_, fun t b a hb ha hbud => ?_, by simp [cycleCb], fun t => ?_⟩, fun t ht => ?_, ?_⟩
  · unfold cyclePrice; split_ifs <;> norm_num
  · unfold cycleCb cycleCa; split_ifs <;> norm_num
  · rcases t with _ | t
    · simp [olgWealth, cyclePrice, cycleCb, cycleCa]; norm_num
    rcases Nat.even_or_odd' t with ⟨k, rfl | rfl⟩
    · have h1 : (2 * k + 1) % 2 = 1 := by omega
      have h2 : (2 * k + 1 + 1) % 2 = 0 := by omega
      have h3 : (2 * k) % 2 = 0 := by omega
      simp [olgWealth, cyclePrice, cycleCb, cycleCa, h1, h2, h3]; norm_num
    · have h1 : (2 * k + 1 + 1) % 2 = 0 := by omega
      have h2 : (2 * k + 1 + 1 + 1) % 2 = 1 := by omega
      have h3 : (2 * k + 1) % 2 = 1 := by omega
      simp [olgWealth, cyclePrice, cycleCb, cycleCa, h1, h2, h3]; norm_num
  · have hu1 : cycleU (b, a) ≤ b + 2 * a := min_le_left _ _
    have hu2 : cycleU (b, a) ≤ 2 * b + a - 1 / 4 := min_le_right _ _
    rcases t with _ | t
    · simp [olgWealth, cyclePrice] at hbud
      have : cycleU (cycleCb 0, cycleCa 0) = 5 / 3 := by
        simp [cycleU, cycleCb, cycleCa]; norm_num
      rw [this]; linarith
    rcases Nat.even_or_odd' t with ⟨k, rfl | rfl⟩
    · have h1 : (2 * k + 1) % 2 = 1 := by omega
      have h2 : (2 * k + 1 + 1) % 2 = 0 := by omega
      have h3 : (2 * k) % 2 = 0 := by omega
      have hw : olgWealth 0 (2 / 3) cyclePrice (2 * k + 1) = 2 := by
        simp [olgWealth, cyclePrice, h1]
      have hp1 : cyclePrice (2 * k + 1) = 2 := by simp [cyclePrice, h1]
      have hp2 : cyclePrice (2 * k + 1 + 1) = 8 / 5 := by simp [cyclePrice, h2]
      rw [hw, hp1, hp2] at hbud
      have : cycleU (cycleCb (2 * k + 1), cycleCa (2 * k + 1)) = 3 / 2 := by
        simp [cycleU, cycleCb, cycleCa, h1, h3]; norm_num
      rw [this]; linarith
    · have h1 : (2 * k + 1 + 1) % 2 = 0 := by omega
      have h2 : (2 * k + 1 + 1 + 1) % 2 = 1 := by omega
      have h3 : (2 * k + 1) % 2 = 1 := by omega
      have hw : olgWealth 0 (2 / 3) cyclePrice (2 * k + 1 + 1) = 8 / 5 := by
        simp [olgWealth, cyclePrice, h1]
      have hp1 : cyclePrice (2 * k + 1 + 1) = 8 / 5 := by simp [cyclePrice, h1]
      have hp2 : cyclePrice (2 * k + 1 + 1 + 1) = 2 := by simp [cyclePrice, h2]
      rw [hw, hp1, hp2] at hbud
      have : cycleU (cycleCb (2 * k + 1 + 1), cycleCa (2 * k + 1 + 1)) = 5 / 4 := by
        simp [cycleU, cycleCb, cycleCa, h1, h3]; norm_num
      rw [this]; linarith
  · simp [cycleCb]
  · obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    have e1 : (s + 1 + 2) % 2 = (s + 1) % 2 := by omega
    have e2 : (s + 2) % 2 = s % 2 := by omega
    simp only [cycleCb, cycleCa, show s + 1 + 2 ≠ 0 by omega, show s + 1 ≠ 0 by omega,
      ↓reduceIte, show s + 1 + 2 - 1 = s + 2 by omega, show s + 1 - 1 = s by omega, e1, e2,
      and_self]
  · simp [cycleCb, cycleCa]
    norm_num

/-! ### A period-3 equilibrium path (Figure 20.H.6) -/

/-- The utility of the period-3 example: the minimum of four affine functions (concave,
piecewise linear and increasing), built by Afriat's construction from the four consumption
points of the path and their budget lines. -/
noncomputable def cycle3U (x : ℝ × ℝ) : ℝ :=
  min (min (min (24 * x.1 + 12 * x.2 - 27) (96 * x.1 + 288 * x.2 - 129))
    (48 * x.1 + 24 * x.2 - 51)) (144 * x.1 + 96 * x.2 - 149)

/-- Old-age consumption on the period-3 path: `1/4, 1/12, 1/6` according to `t mod 3`. -/
noncomputable def cycle3Ca (t : ℕ) : ℝ :=
  if t % 3 = 0 then 1 / 4 else if t % 3 = 1 then 1 / 12 else 1 / 6

/-- Young-age consumption on the period-3 path: `1` for generation 0, then `1 - c_{a,t-1}`. -/
noncomputable def cycle3Cb (t : ℕ) : ℝ := if t = 0 then 1 else 1 - cycle3Ca (t - 1)

/-- The prices of the period-3 path: `2`, then `1, 3, 3/2` according to `t mod 3 = 1, 2, 0`. -/
noncomputable def cycle3Price (t : ℕ) : ℝ :=
  if t = 0 then 2 else if t % 3 = 1 then 1 else if t % 3 = 2 then 3 else 3 / 2

/-- **Figure 20.H.6** (MWG, p. 777): a period-3 equilibrium path with complementary
consumptions, in the purely nominal case ("chaos rears its head"). With the piecewise linear
concave utility `cycle3U`, the bubble `M = 1/4` and the prices `2, 1, 3, 3/2, 1, 3, 3/2, ...`,
generations `t ≥ 1` cycle through `(3/4, 1/12)`, `(11/12, 1/6)`, `(5/6, 1/4)`: an equilibrium
(Definition 20.H.1) whose allocation has period exactly 3. -/
theorem figure_20_H_6_period_three :
    OLGEq cycle3U 0 cycle3Price (1 / 4) cycle3Cb cycle3Ca ∧
      (∀ t, 1 ≤ t → cycle3Cb (t + 3) = cycle3Cb t ∧ cycle3Ca (t + 3) = cycle3Ca t) ∧
      (cycle3Cb 1, cycle3Ca 1) ≠ (cycle3Cb 2, cycle3Ca 2) ∧
      (cycle3Cb 2, cycle3Ca 2) ≠ (cycle3Cb 3, cycle3Ca 3) ∧
      (cycle3Cb 1, cycle3Ca 1) ≠ (cycle3Cb 3, cycle3Ca 3) := by
  refine ⟨⟨fun t => ?_, by norm_num, fun h => absurd h (lt_irrefl 0), fun t => ?_,
    fun t => ?_, fun t b a hb ha hbud => ?_, by simp [cycle3Cb], fun t => ?_⟩, fun t ht => ?_,
    ?_, ?_, ?_⟩
  · unfold cycle3Price; split_ifs <;> norm_num
  · unfold cycle3Cb cycle3Ca; split_ifs <;> norm_num
  · rcases t with _ | t
    · simp [olgWealth, cycle3Price, cycle3Cb, cycle3Ca]
    have hc : (t + 1) % 3 = 0 ∨ (t + 1) % 3 = 1 ∨ (t + 1) % 3 = 2 := by omega
    rcases hc with h | h | h
    · have h1 : (t + 1 + 1) % 3 = 1 := by omega
      have h2 : t % 3 = 2 := by omega
      simp [olgWealth, cycle3Price, cycle3Cb, cycle3Ca, h, h1, h2]; norm_num
    · have h1 : (t + 1 + 1) % 3 = 2 := by omega
      have h2 : t % 3 = 0 := by omega
      simp [olgWealth, cycle3Price, cycle3Cb, cycle3Ca, h, h1, h2]; norm_num
    · have h1 : (t + 1 + 1) % 3 = 0 := by omega
      have h2 : t % 3 = 1 := by omega
      simp [olgWealth, cycle3Price, cycle3Cb, cycle3Ca, h, h1, h2]; norm_num
  · have hu0 : cycle3U (b, a) ≤ 24 * b + 12 * a - 27 :=
      (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
    have hu1 : cycle3U (b, a) ≤ 96 * b + 288 * a - 129 :=
      (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
    have hu2 : cycle3U (b, a) ≤ 48 * b + 24 * a - 51 :=
      (min_le_left _ _).trans (min_le_right _ _)
    have hu3 : cycle3U (b, a) ≤ 144 * b + 96 * a - 149 := min_le_right _ _
    rcases t with _ | t
    · have hw : olgWealth 0 (1 / 4) cycle3Price 0 = 9 / 4 := by
        simp [olgWealth, cycle3Price]; norm_num
      have hp1 : cycle3Price 0 = 2 := by simp [cycle3Price]
      have hp2 : cycle3Price (0 + 1) = 1 := by simp [cycle3Price]
      rw [hw, hp1, hp2] at hbud
      have : cycle3U (cycle3Cb 0, cycle3Ca 0) = 0 := by
        simp [cycle3U, cycle3Cb, cycle3Ca]; norm_num
      rw [this]; linarith
    have hc : (t + 1) % 3 = 0 ∨ (t + 1) % 3 = 1 ∨ (t + 1) % 3 = 2 := by omega
    rcases hc with h | h | h
    · have h1 : (t + 1 + 1) % 3 = 1 := by omega
      have h2 : t % 3 = 2 := by omega
      have hw : olgWealth 0 (1 / 4) cycle3Price (t + 1) = 3 / 2 := by
        simp [olgWealth, cycle3Price, h]
      have hp1 : cycle3Price (t + 1) = 3 / 2 := by simp [cycle3Price, h]
      have hp2 : cycle3Price (t + 1 + 1) = 1 := by simp [cycle3Price, h1]
      rw [hw, hp1, hp2] at hbud
      have : cycle3U (cycle3Cb (t + 1), cycle3Ca (t + 1)) = -5 := by
        simp [cycle3U, cycle3Cb, cycle3Ca, h, h2]; norm_num
      rw [this]; linarith
    · have h1 : (t + 1 + 1) % 3 = 2 := by omega
      have h2 : t % 3 = 0 := by omega
      have hw : olgWealth 0 (1 / 4) cycle3Price (t + 1) = 1 := by
        simp [olgWealth, cycle3Price, h]
      have hp1 : cycle3Price (t + 1) = 1 := by simp [cycle3Price, h]
      have hp2 : cycle3Price (t + 1 + 1) = 3 := by simp [cycle3Price, h1]
      rw [hw, hp1, hp2] at hbud
      have : cycle3U (cycle3Cb (t + 1), cycle3Ca (t + 1)) = -33 := by
        simp [cycle3U, cycle3Cb, cycle3Ca, h, h2]; norm_num
      rw [this]; linarith
    · have h1 : (t + 1 + 1) % 3 = 0 := by omega
      have h2 : t % 3 = 1 := by omega
      have hw : olgWealth 0 (1 / 4) cycle3Price (t + 1) = 3 := by
        simp [olgWealth, cycle3Price, h]
      have hp1 : cycle3Price (t + 1) = 3 := by simp [cycle3Price, h]
      have hp2 : cycle3Price (t + 1 + 1) = 3 / 2 := by simp [cycle3Price, h1]
      rw [hw, hp1, hp2] at hbud
      have : cycle3U (cycle3Cb (t + 1), cycle3Ca (t + 1)) = -3 := by
        simp [cycle3U, cycle3Cb, cycle3Ca, h, h2]; norm_num
      rw [this]; linarith
  · simp [cycle3Cb]
  · obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    have e1 : (s + 1 + 3) % 3 = (s + 1) % 3 := by omega
    have e2 : (s + 3) % 3 = s % 3 := by omega
    simp only [cycle3Cb, cycle3Ca, show s + 1 + 3 ≠ 0 by omega, show s + 1 ≠ 0 by omega,
      ↓reduceIte, show s + 1 + 3 - 1 = s + 3 by omega, show s + 1 - 1 = s by omega, e1, e2,
      and_self]
  · simp [cycle3Cb, cycle3Ca]
  · simp [cycle3Cb, cycle3Ca]
  · simp [cycle3Cb, cycle3Ca]

/-! ### Optimal nominal equilibria have a bubble bounded away from zero -/

/-- Pareto optimality of an OLG allocation (as in Proposition 20.H.1): no feasible allocation
makes every generation at least as well off and one strictly better off. -/
def OLGParetoOptimal (u : ℝ × ℝ → ℝ) (cb ca : ℕ → ℝ) : Prop :=
  ¬ ∃ cb' ca' : ℕ → ℝ, (∀ t, 0 ≤ cb' t ∧ 0 ≤ ca' t) ∧ cb' 0 ≤ 1 ∧
    (∀ t, ca' t + cb' (t + 1) ≤ 1) ∧ (∀ t, u (cb t, ca t) ≤ u (cb' t, ca' t)) ∧
    ∃ s, u (cb s, ca s) < u (cb' s, ca' s)

/-- The utility `u(b, a) = √b + √a` of the stationary example. -/
noncomputable def sqrtU (x : ℝ × ℝ) : ℝ := Real.sqrt x.1 + Real.sqrt x.2

/-- A proved instance of `OLGParetoOptimal`: the monetary steady state of `sqrtU`. -/
theorem olgParetoOptimal_monetary :
    OLGParetoOptimal sqrtU (monetaryCb (1 / 2)) (fun _ => 1 - 1 / 2) :=
  monetary_steady_state_optimal_sqrt

/-- The demand of `√b + √a` on the budget `b + r a ≤ 1`: the unique maximizer is
`(r/(1 + r), 1/(r(1 + r)))`. -/
theorem sqrt_demand {r b a : ℝ} (hr : 0 < r) (hb : 0 ≤ b) (ha : 0 ≤ a) (hbud : b + r * a ≤ 1)
    (hopt : ∀ b' a', 0 ≤ b' → 0 ≤ a' → b' + r * a' ≤ 1 →
      Real.sqrt b' + Real.sqrt a' ≤ Real.sqrt b + Real.sqrt a) :
    b = r / (1 + r) ∧ a = 1 / (r * (1 + r)) := by
  have h1r : 0 < 1 + r := by linarith
  set as := 1 / (r * (1 + r)) with has
  have has0 : 0 < as := by rw [has]; positivity
  have hbs : r / (1 + r) = r ^ 2 * as := by rw [has]; field_simp
  have hsum : r ^ 2 * as + r * as = 1 := by rw [has]; field_simp; ring
  have hys := Real.sq_sqrt has0.le
  have hxs : Real.sqrt (r ^ 2 * as) = r * Real.sqrt as := by
    rw [Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hr.le]
  have hval := hopt (r ^ 2 * as) as (by positivity) has0.le (by linarith)
  rw [hxs] at hval
  set x := Real.sqrt b with hx
  set y := Real.sqrt a with hy
  set ys := Real.sqrt as with hysd
  have hx2 : x ^ 2 = b := Real.sq_sqrt hb
  have hy2 : y ^ 2 = a := Real.sq_sqrt ha
  have hx0 : 0 ≤ x := Real.sqrt_nonneg b
  have hy0 : 0 ≤ y := Real.sqrt_nonneg a
  have hys0 : 0 ≤ ys := Real.sqrt_nonneg as
  -- `(1 + r) ≤ r (x + y)²` from optimality, `r (x + y)² + (x - r y)² ≤ 1 + r` from the budget
  have hlow : (1 + r) ≤ r * (x + y) ^ 2 := by
    have hsq : ((1 + r) * ys) ^ 2 ≤ (x + y) ^ 2 := by
      have : (1 + r) * ys ≤ x + y := by linarith
      exact pow_le_pow_left₀ (by positivity) this 2
    have : ((1 + r) * ys) ^ 2 = (1 + r) ^ 2 * as := by rw [mul_pow, hys]
    rw [this] at hsq
    have e : r * ((1 + r) ^ 2 * as) = 1 + r := by rw [has]; field_simp
    nlinarith
  have hident : r * (x + y) ^ 2 + (x - r * y) ^ 2 = (1 + r) * (x ^ 2 + r * y ^ 2) := by ring
  have hxy : x = r * y := by
    have : (x - r * y) ^ 2 ≤ 0 := by rw [hx2, hy2] at hident; nlinarith
    nlinarith [sq_nonneg (x - r * y)]
  have hbind : b + r * a = 1 := by
    rw [hx2, hy2] at hident
    have : (x - r * y) ^ 2 = 0 := by rw [hxy]; ring
    nlinarith
  have hba : b = r ^ 2 * a := by rw [← hx2, ← hy2, hxy]; ring
  have haeq : a = as := by
    have : (r ^ 2 + r) * a = (r ^ 2 + r) * as := by nlinarith
    exact mul_left_cancel₀ (by positivity) this
  refine ⟨by rw [hba, haeq, hbs], haeq⟩

/-- In a nominal equilibrium of the `√b + √a` economy, every generation `t ≥ 1` consumes its
demand at the relative price `r_t = p_{t+1}/p_t`. -/
theorem olg_sqrt_demand {p : ℕ → ℝ} {M : ℝ} {cb ca : ℕ → ℝ} (he : OLGEq sqrtU 0 p M cb ca)
    {t : ℕ} (ht : t ≠ 0) :
    cb t = p (t + 1) / p t / (1 + p (t + 1) / p t) ∧
      ca t = 1 / (p (t + 1) / p t * (1 + p (t + 1) / p t)) := by
  have hpt := he.pricesPos t
  have hpt1 := he.pricesPos (t + 1)
  have hw : olgWealth 0 M p t = p t := by simp [olgWealth, ht]
  have hr : 0 < p (t + 1) / p t := div_pos hpt1 hpt
  have hscale : ∀ b a, p t * b + p (t + 1) * a = p t * (b + p (t + 1) / p t * a) := by
    intro b a; field_simp
  refine sqrt_demand hr (he.cons_nonneg t).1 (he.cons_nonneg t).2 ?_ fun b' a' hb' ha' hbud => ?_
  · have := he.budget t
    rw [hw, hscale] at this
    nlinarith
  · have := he.optimal t b' a' hb' ha' (by rw [hw, hscale]; nlinarith)
    simpa [sqrtU] using this

/-- **Classification of the nominal equilibria of the `√b + √a` economy** (MWG, p. 774, Figures
20.H.2-20.H.3). With `r_k = p_{k+2}/p_{k+1}`, market clearing gives `r_{k+1} = r_k² + r_k - 1`;
positivity forces `r_k ≥ 1`. If `r_0 = 1` the equilibrium is the monetary steady state; if
`r_0 > 1`, `r_k ≥ 1 + (k + 1)(r_0 - 1)`, the real bubble `M/p_{t+1} = c_{at}` is not bounded away
from zero, and the monetary steady state Pareto dominates the equilibrium. -/
theorem olg_sqrt_classification {p : ℕ → ℝ} {M : ℝ} {cb ca : ℕ → ℝ}
    (he : OLGEq sqrtU 0 p M cb ca) :
    ((∀ t, cb t = monetaryCb (1 / 2) t) ∧ ∀ t, ca t = 1 - 1 / 2) ∨
      (¬ OLGParetoOptimal sqrtU cb ca ∧ ¬ ∃ η : ℝ, 0 < η ∧ ∀ t, η ≤ M / p (t + 1)):= by
  have hmono : ∀ b b' a, 0 ≤ b → b < b' → sqrtU (b, a) < sqrtU (b', a) := fun b b' a hb hbb' => by
    simp only [sqrtU]; linarith [Real.sqrt_lt_sqrt hb hbb']
  have hid := olg_nominal_identity hmono he
  have hreal : ∀ t, M / p (t + 1) = ca t := fun t => by
    rw [← hid t]; field_simp [(he.pricesPos (t + 1)).ne']
  simp only [hreal]
  set R : ℕ → ℝ := fun k => p (k + 2) / p (k + 1) with hR
  have hRpos : ∀ k, 0 < R k := fun k => div_pos (he.pricesPos _) (he.pricesPos _)
  have hdem : ∀ k, cb (k + 1) = R k / (1 + R k) ∧ ca (k + 1) = 1 / (R k * (1 + R k)) :=
    fun k => olg_sqrt_demand he (t := k + 1) (by omega)
  have hrec : ∀ k, R (k + 1) = R k ^ 2 + R k - 1 := by
    intro k
    have hf := he.feasible (k + 1)
    rw [(hdem k).2, (hdem (k + 1)).1] at hf
    have h1 := hRpos k
    have h2 := hRpos (k + 1)
    field_simp at hf
    nlinarith
  -- `r_k ≥ 1`
  have hge1 : ∀ k, 1 ≤ R k := by
    intro k
    by_contra hlt
    push Not at hlt
    have hneg : ∀ n, R (k + n) - 1 ≤ 2 ^ n * (R k - 1) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [← add_assoc, hrec]
        have hp := hRpos (k + n)
        have hle1 : R (k + n) - 1 ≤ 0 := by
          have : 2 ^ n * (R k - 1) ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
          linarith
        have : R (k + n) ^ 2 + R (k + n) - 1 - 1 ≤ 2 * (R (k + n) - 1) := by
          nlinarith [mul_nonpos_of_nonneg_of_nonpos hp.le hle1]
        have e : (2 : ℝ) ^ (n + 1) * (R k - 1) = 2 * (2 ^ n * (R k - 1)) := by ring
        linarith
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / (1 - R k))
    have h2n : (n : ℝ) ≤ 2 ^ n := by
      have := Nat.lt_two_pow_self (n := n)
      exact_mod_cast this.le
    have hpos := hRpos (k + n)
    have := hneg n
    have hd : 0 < 1 - R k := by linarith
    have : (n : ℝ) * (1 - R k) > 1 := by
      rw [div_lt_iff₀ hd] at hn; linarith
    nlinarith
  -- steady state or exploding prices
  rcases eq_or_lt_of_le (hge1 0) with h0 | h0
  · -- `r_0 = 1`: the monetary steady state
    have hR1 : ∀ k, R k = 1 := by
      intro k
      induction k with
      | zero => exact h0.symm
      | succ k ih => rw [hrec, ih]; norm_num
    have hcb : ∀ t, cb t = monetaryCb (1 / 2) t := by
      intro t
      rcases t with _ | k
      · simp [monetaryCb, he.feasible_zero]
      · rw [(hdem k).1, hR1]; simp [monetaryCb]; norm_num
    have hca : ∀ t, ca t = 1 - 1 / 2 := by
      intro t
      have := he.feasible t
      rw [hcb (t + 1)] at this
      simp [monetaryCb] at this
      linarith
    exact Or.inl ⟨hcb, hca⟩
  · -- `r_0 > 1`: the bubble vanishes and the steady state dominates
    have hgrow : ∀ n, 1 + (n + 1) * (R 0 - 1) ≤ R n := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [hrec]
        push_cast
        have := hge1 n
        nlinarith
    right
    constructor
    · intro hpo
      apply hpo
      refine ⟨monetaryCb (1 / 2), fun _ => 1 - 1 / 2, fun t => ⟨?_, by norm_num⟩,
        by simp [monetaryCb], fun t => by simp [monetaryCb], fun t => ?_, 0, ?_⟩
      · unfold monetaryCb; split_ifs <;> norm_num
      · rcases t with _ | k
        · -- generation 0 consumes `(1, 1/(1 + r_0)) ≤ (1, 1/2)`
          have hca0 : ca 0 = 1 / (1 + R 0) := by
            have hfe := he.feasible 0
            rw [(hdem 0).1] at hfe
            have h1 : R 0 / (1 + R 0) = 1 - 1 / (1 + R 0) := by
              rw [eq_sub_iff_add_eq, ← add_div, add_comm,
                div_self (by linarith [hRpos 0])]
            linarith
          simp only [sqrtU, he.feasible_zero, monetaryCb, ↓reduceIte, hca0]
          have : 1 / (1 + R 0) ≤ 1 - 1 / 2 := by
            rw [div_le_iff₀ (by linarith)]; linarith
          linarith [Real.sqrt_le_sqrt this]
        · -- generation `k + 1` has utility `√(1 + 1/r_k) ≤ √2`
          rw [(hdem k).1, (hdem k).2]
          simp only [sqrtU, monetaryCb, show k + 1 ≠ 0 by omega, ↓reduceIte]
          have hr := hRpos k
          have hr1 := hge1 k
          set x := Real.sqrt (R k / (1 + R k)) with hx
          set y := Real.sqrt (1 / (R k * (1 + R k))) with hy
          have hx2 : x ^ 2 = R k / (1 + R k) := Real.sq_sqrt (by positivity)
          have hy2 : y ^ 2 = 1 / (R k * (1 + R k)) := Real.sq_sqrt (by positivity)
          have hx0 : 0 ≤ x := Real.sqrt_nonneg _
          have hy0 : 0 ≤ y := Real.sqrt_nonneg _
          have hxy : x = R k * y := by
            have e : R k / (1 + R k) = R k ^ 2 * (1 / (R k * (1 + R k))) := by field_simp
            rw [hx, e, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hr.le]
          have hs : Real.sqrt (1 / 2) ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)
          have hs0 : 0 ≤ Real.sqrt (1 / 2) := Real.sqrt_nonneg _
          have e : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
          rw [e]
          -- `(x + y)² = 1 + 1/r_k ≤ 2`
          have hsq : (x + y) ^ 2 ≤ (Real.sqrt (1 / 2) + Real.sqrt (1 / 2)) ^ 2 := by
            have h1 : (x + y) ^ 2 = (R k + 1) ^ 2 * y ^ 2 := by rw [hxy]; ring
            rw [h1, hy2]
            have : (R k + 1) ^ 2 * (1 / (R k * (1 + R k))) = 1 + 1 / R k := by
              field_simp; ring
            rw [this]
            have : 1 / R k ≤ 1 := by rw [div_le_one hr]; exact hr1
            nlinarith
          nlinarith [sq_nonneg (x + y - (Real.sqrt (1 / 2) + Real.sqrt (1 / 2)))]
      · -- strictly better for generation 0
        have hca0 : ca 0 = 1 / (1 + R 0) := by
          have hfe := he.feasible 0
          rw [(hdem 0).1] at hfe
          have h1 : R 0 / (1 + R 0) = 1 - 1 / (1 + R 0) := by
            rw [eq_sub_iff_add_eq, ← add_div, add_comm,
              div_self (by linarith [hRpos 0])]
          linarith
        simp only [sqrtU, he.feasible_zero, monetaryCb, ↓reduceIte, hca0]
        have : 1 / (1 + R 0) < 1 - 1 / 2 := by
          rw [div_lt_iff₀ (by linarith)]; linarith
        linarith [Real.sqrt_lt_sqrt (by positivity) this]
    · rintro ⟨η, hη, hb⟩
      obtain ⟨n, hn⟩ := exists_nat_gt (1 / (η * (R 0 - 1)))
      have hd : 0 < R 0 - 1 := by linarith
      have hg := hgrow n
      have hca := hb (n + 1)
      rw [(hdem n).2] at hca
      have hRn := hRpos n
      have hbig : 1 / η < R n := by
        have : 1 / (η * (R 0 - 1)) * (η * (R 0 - 1)) = 1 := by field_simp
        have h1 : (1 / η) = 1 / (η * (R 0 - 1)) * (R 0 - 1) := by field_simp
        rw [h1]
        nlinarith
      have : 1 / (R n * (1 + R n)) < η := by
        rw [div_lt_iff₀ (by positivity)]
        rw [div_lt_iff₀ hη] at hbig
        nlinarith
      linarith

/-- **Optimal nominal equilibria are those, and only those, whose bubble is bounded away from
zero** (MWG, p. 774, a claim "we leave without proof"), in the stationary economy
`u(b, a) = √b + √a` with a purely nominal asset. -/
theorem olg_sqrt_optimal_iff_bubble {p : ℕ → ℝ} {M : ℝ} {cb ca : ℕ → ℝ}
    (he : OLGEq sqrtU 0 p M cb ca) :
    OLGParetoOptimal sqrtU cb ca ↔ ∃ η : ℝ, 0 < η ∧ ∀ t, η ≤ M / p (t + 1) := by
  have hmono : ∀ b b' a, 0 ≤ b → b < b' → sqrtU (b, a) < sqrtU (b', a) := fun b b' a hb hbb' => by
    simp only [sqrtU]; linarith [Real.sqrt_lt_sqrt hb hbb']
  have hid := olg_nominal_identity hmono he
  rcases olg_sqrt_classification he with ⟨hcb, hca⟩ | ⟨hnpo, hnb⟩
  · constructor
    · intro _
      refine ⟨1 / 2, by norm_num, fun t => ?_⟩
      rw [← hid t, hca t, mul_div_assoc, mul_div_cancel₀ _ (he.pricesPos (t + 1)).ne']
      norm_num
    · intro _
      rw [show cb = monetaryCb (1 / 2) from funext hcb, show ca = (fun _ => 1 - 1 / 2) from
        funext hca]
      exact olgParetoOptimal_monetary
  · exact ⟨fun h => absurd h hnpo, fun h => absurd h hnb⟩

/-- **Exercise 20.H.2(b)** for the `√b + √a` economy (MWG, p. 786): its excess demand satisfies
the determinacy condition (20.H.3) (`sqrt_determinacy_condition`), and the monetary steady state
is the only nominal equilibrium that is a Pareto optimum. -/
theorem exercise_20_H_2b_sqrt {p : ℕ → ℝ} {M : ℝ} {cb ca : ℕ → ℝ}
    (he : OLGEq sqrtU 0 p M cb ca) (hpo : OLGParetoOptimal sqrtU cb ca) :
    (∀ t, cb t = monetaryCb (1 / 2) t) ∧ ∀ t, ca t = 1 - 1 / 2 := by
  rcases olg_sqrt_classification he with h | ⟨hnpo, _⟩
  · exact h
  · exact absurd hpo hnpo

/-- **The determinacy condition (20.H.3) for `√b + √a`** (MWG, p. 776): with endowment `(1, 0)`
the excess demands are `z_b(p_b, p_a) = p_a/(p_b + p_a) - 1` and
`z_a(p_b, p_a) = p_b²/(p_a (p_b + p_a))`, and `∇₁z_b(p_b, p_a) < ∇₁z_a(p_b, p_a)` at all
positive prices (`z_b` decreases and `z_a` increases in `p_b`). -/
theorem sqrt_determinacy_condition {pb pa : ℝ} (hb : 0 < pb) (ha : 0 < pa) :
    HasDerivAt (fun x => pa / (x + pa) - 1) (-pa / (pb + pa) ^ 2) pb ∧
      HasDerivAt (fun x => x ^ 2 / (pa * (x + pa)))
        (pb * (pb + 2 * pa) / (pa * (pb + pa) ^ 2)) pb ∧
      -pa / (pb + pa) ^ 2 < pb * (pb + 2 * pa) / (pa * (pb + pa) ^ 2) := by
  have hs : pb + pa ≠ 0 := by positivity
  have hlin : HasDerivAt (fun x : ℝ => x + pa) 1 pb := (hasDerivAt_id pb).add_const pa
  refine ⟨?_, ?_, ?_⟩
  · have := ((hasDerivAt_const pb pa).div hlin hs).sub_const 1
    convert this using 1
    field_simp
    ring
  · have h2 : HasDerivAt (fun x : ℝ => pa * (x + pa)) pa pb := by
      simpa using hlin.const_mul pa
    have := (hasDerivAt_pow 2 pb).div h2 (by positivity)
    convert this using 1
    field_simp
    ring
  · have h1 : -pa / (pb + pa) ^ 2 < 0 := div_neg_of_neg_of_pos (by linarith) (by positivity)
    have h2 : 0 < pb * (pb + 2 * pa) / (pa * (pb + pa) ^ 2) := by positivity
    linarith

end MWG.EquilibriumTime

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Dynamic programming (MWG Mathematical Appendix, Section M.N, pp. 968-970)

The problem (M.N.1): `max ∑_t δ^t u(x_t, x_{t+1})` over sequences in a nonempty compact
`A ⊆ ℝ^N` with `x₀ = z`, for `u` continuous on `A × A` and `0 < δ < 1`. Here `A` is a set
`K ⊆ Fin N → ℝ` with `CompactSpace K` and `Nonempty K`.

The problem is LeanEconomics' `DynamicProgram` with states and actions in `K`, the constant
feasible set `K` and the law of motion `(z, z') ↦ z'` (`mnProgram`); its value function is
`LeanEconomics.DynamicProgram.valueFunction`.

* The value function is attained by a maximizing sequence and is the value of (M.N.1)
  (`value_attained_M_N`); it is continuous (`value_continuous_M_N`) and concave when `A` is convex
  and `u` concave (`value_concave_M_N`).
* The Bellman equation (`bellman_M_N`).
* **Theorem M.N.1** (`theorem_M_N_1`): a continuous solution of the Bellman equation (M.N.2) is the
  value function.
* Value function iteration converges (`value_iteration_M_N`, pointwise
  `value_iteration_pointwise_M_N`).
* The Euler equations (M.N.4) at an interior optimum (`euler_M_N_4`).
-/

open Filter Topology BoundedContinuousFunction
open scoped NNReal

namespace MWG.EquilibriumTime

variable {N : ℕ} {K : Set (Fin N → ℝ)} [CompactSpace K] [Nonempty K]

/-- The reward `u` restricted to `K × K` as a bounded continuous function. -/
noncomputable def mnReward (u : (Fin N → ℝ) × (Fin N → ℝ) → ℝ) (hu : ContinuousOn u (K ×ˢ K)) :
    (K × K) →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun x => u (x.1.1, x.2.1), hu.comp_continuous (by fun_prop) fun x => ⟨x.1.2, x.2.2⟩⟩

/-- **The dynamic program of (M.N.1)** (MWG, p. 968), as a LeanEconomics `DynamicProgram`: state
`z ∈ K`, action `z' ∈ K` (the whole of `K` is feasible), reward `u(z, z')`, next state `z'`. -/
noncomputable def mnProgram (u : (Fin N → ℝ) × (Fin N → ℝ) → ℝ) (hu : ContinuousOn u (K ×ˢ K))
    (δ : ℝ≥0) (hδ : δ < 1) : LeanEconomics.DynamicProgram K K where
  feasible _ := Set.univ
  isCompact_feasible _ := isCompact_univ
  feasible_nonempty _ := Set.univ_nonempty
  upperHemicontinuous_feasible := LeanEconomics.upperHemicontinuous_const Set.univ
  lowerHemicontinuous_feasible := LeanEconomics.lowerHemicontinuous_const Set.univ
  reward := mnReward u hu
  transition := ⟨Prod.snd, continuous_snd⟩
  discount := δ
  discount_lt_one := hδ

/-- The objective of (M.N.1) along a sequence in `K`. -/
noncomputable def mnObjective (u : (Fin N → ℝ) × (Fin N → ℝ) → ℝ) (δ : ℝ) (x : ℕ → K) : ℝ :=
  ∑' t, δ ^ t * u ((x t : Fin N → ℝ), (x (t + 1) : Fin N → ℝ))

variable {u : (Fin N → ℝ) × (Fin N → ℝ) → ℝ} {hu : ContinuousOn u (K ×ˢ K)} {δ : ℝ≥0}
  {hδ : δ < 1}

/-- A sequence of `K` as a plan of the dynamic program. -/
def mnPlan (x : ℕ → K) : (mnProgram u hu δ hδ).Plan (x 0) where
  state := x
  action := fun t => x (t + 1)
  state_zero := rfl
  action_mem := fun _ => Set.mem_univ _
  state_succ := fun _ => rfl

theorem mnPlan_value (x : ℕ → K) :
    (mnPlan (u := u) (hu := hu) (δ := δ) (hδ := hδ) x).value = mnObjective u δ x := rfl

/-- Every plan is the plan of its state sequence. -/
theorem plan_value_eq {z : K} (p : (mnProgram u hu δ hδ).Plan z) :
    p.value = mnObjective u δ p.state := by
  unfold LeanEconomics.DynamicProgram.Plan.value LeanEconomics.DynamicProgram.Plan.payoff
    mnObjective
  refine tsum_congr fun t => ?_
  have h := p.state_succ t
  simp only [mnProgram] at h
  rw [h]
  rfl

/-- **The value of (M.N.1) is attained** (MWG, p. 968): there is a maximizing sequence from `z`,
and the value function of the dynamic program is the maximum value `v(z)`. -/
theorem value_attained_M_N (z : K) :
    ∃ x : ℕ → K, x 0 = z ∧ mnObjective u δ x = (mnProgram u hu δ hδ).valueFunction z ∧
      ∀ x' : ℕ → K, x' 0 = z → mnObjective u δ x' ≤ (mnProgram u hu δ hδ).valueFunction z := by
  obtain ⟨⟨p, hp⟩, hmax⟩ := (mnProgram u hu δ hδ).isGreatest_planValue z
  refine ⟨p.state, p.state_zero, by rw [← plan_value_eq, hp], fun x' hx' => ?_⟩
  subst hx'
  exact hmax ⟨mnPlan x', rfl⟩

/-- **The value function is continuous** (MWG, p. 968). -/
theorem value_continuous_M_N : Continuous ((mnProgram u hu δ hδ).valueFunction) :=
  (mnProgram u hu δ hδ).valueFunction.continuous

/-- **The Bellman equation** (MWG, p. 969): `v(z) = max_{z' ∈ A} u(z, z') + δ v(z')`. -/
theorem bellman_M_N (z : K) :
    IsGreatest {r | ∃ z' : K, r = u ((z : Fin N → ℝ), (z' : Fin N → ℝ))
      + δ * (mnProgram u hu δ hδ).valueFunction z'}
      ((mnProgram u hu δ hδ).valueFunction z) := by
  set D := mnProgram u hu δ hδ
  obtain ⟨a, -, ha⟩ := D.exists_optimal_policy z
  refine ⟨⟨a, by rw [ha]; rfl⟩, ?_⟩
  rintro r ⟨z', rfl⟩
  have h := D.le_bellmanFn (s := z) (a := z') D.valueFunction (Set.mem_univ _)
  have hfix : D.bellmanFn D.valueFunction z = D.valueFunction z := by
    conv_rhs => rw [← D.bellman_valueFunction]
    rfl
  rw [hfix] at h
  exact h

/-- **Theorem M.N.1** (MWG, p. 969): if `f : A → ℝ` is continuous and satisfies the Bellman
equation (M.N.2), `f(z) = max_{z' ∈ A} u(z, z') + δ f(z')` for every `z ∈ A`, then `f` is the value
function of (M.N.1). -/
theorem theorem_M_N_1 {f : K → ℝ} (hf : Continuous f)
    (hbell : ∀ z : K, IsGreatest {r | ∃ z' : K, r = u ((z : Fin N → ℝ), (z' : Fin N → ℝ))
      + δ * f z'} (f z)) :
    ∀ z, f z = (mnProgram u hu δ hδ).valueFunction z := by
  set D := mnProgram u hu δ hδ
  set g : K →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact ⟨f, hf⟩
  have hfix : D.bellman g = g := by
    ext z
    rw [D.bellman_apply, LeanEconomics.maxValue]
    have : D.objective g z '' D.feasible z
        = {r | ∃ z' : K, r = u ((z : Fin N → ℝ), (z' : Fin N → ℝ)) + δ * f z'} := by
      ext r
      constructor
      · rintro ⟨z', -, rfl⟩; exact ⟨z', rfl⟩
      · rintro ⟨z', rfl⟩; exact ⟨z', Set.mem_univ _, rfl⟩
    rw [this, (hbell z).csSup_eq]
    rfl
  intro z
  have := D.eq_valueFunction hfix
  exact congrFun (congrArg DFunLike.coe this) z

/-- **Value function iteration** (MWG, p. 969): from any continuous `f₀`, the iterates
`f_{r+1}(z) = max_{z'} u(z, z') + δ f_r(z')` converge (uniformly) to the value function. -/
theorem value_iteration_M_N (f₀ : K →ᵇ ℝ) :
    Tendsto (fun r => (mnProgram u hu δ hδ).bellman^[r] f₀) atTop
      (𝓝 (mnProgram u hu δ hδ).valueFunction) :=
  (mnProgram u hu δ hδ).tendsto_iterate_valueFunction f₀

/-- **Value function iteration**, pointwise form (MWG, p. 969): `f_r(z) → v(z)` for every `z`. -/
theorem value_iteration_pointwise_M_N (f₀ : K →ᵇ ℝ) (z : K) :
    Tendsto (fun r => ((mnProgram u hu δ hδ).bellman^[r] f₀) z) atTop
      (𝓝 ((mnProgram u hu δ hδ).valueFunction z)) := by
  have h := value_iteration_M_N (u := u) (hu := hu) (δ := δ) (hδ := hδ) f₀
  rw [tendsto_iff_dist_tendsto_zero] at h ⊢
  exact squeeze_zero (fun r => dist_nonneg)
    (fun r => BoundedContinuousFunction.dist_coe_le_dist z) h

omit [Nonempty K] in
include hu in
/-- A bounded reward makes the objective summable. -/
theorem summable_mnObjective (x : ℕ → K) (hδ0 : (δ : ℝ) < 1) :
    Summable fun t => (δ : ℝ) ^ t * u ((x t : Fin N → ℝ), (x (t + 1) : Fin N → ℝ)) := by
  refine summable_discounted δ.coe_nonneg hδ0 (M := ‖mnReward u hu‖) fun t => ?_
  have := (mnReward u hu).norm_coe_le_norm (x t, x (t + 1))
  simpa [mnReward, Real.norm_eq_abs] using this

/-- **The value function is concave** (MWG, p. 968) when `A` is convex and `u` is concave on
`A × A`. -/
theorem value_concave_M_N (hKc : Convex ℝ K) (hconc : ConcaveOn ℝ (K ×ˢ K) u) {z₁ z₂ : K}
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    θ * (mnProgram u hu δ hδ).valueFunction z₁ + (1 - θ) * (mnProgram u hu δ hδ).valueFunction z₂
      ≤ (mnProgram u hu δ hδ).valueFunction
        ⟨θ • (z₁ : Fin N → ℝ) + (1 - θ) • (z₂ : Fin N → ℝ),
          hKc z₁.2 z₂.2 hθ0 (by linarith) (by ring)⟩ := by
  obtain ⟨x₁, hx₁, hv₁, -⟩ := value_attained_M_N (u := u) (hu := hu) (δ := δ) (hδ := hδ) z₁
  obtain ⟨x₂, hx₂, hv₂, -⟩ := value_attained_M_N (u := u) (hu := hu) (δ := δ) (hδ := hδ) z₂
  have hδ1 : (δ : ℝ) < 1 := by exact_mod_cast hδ
  set m : ℕ → K := fun t => ⟨θ • (x₁ t : Fin N → ℝ) + (1 - θ) • (x₂ t : Fin N → ℝ),
    hKc (x₁ t).2 (x₂ t).2 hθ0 (by linarith) (by ring)⟩ with hm
  obtain ⟨_, _, _, hmax⟩ := value_attained_M_N (u := u) (hu := hu) (δ := δ) (hδ := hδ)
    ⟨θ • (z₁ : Fin N → ℝ) + (1 - θ) • (z₂ : Fin N → ℝ),
      hKc z₁.2 z₂.2 hθ0 (by linarith) (by ring)⟩
  have hm0 : m 0 = ⟨θ • (z₁ : Fin N → ℝ) + (1 - θ) • (z₂ : Fin N → ℝ),
      hKc z₁.2 z₂.2 hθ0 (by linarith) (by ring)⟩ := by
    simp [hm, hx₁, hx₂]
  have hle := hmax m hm0
  have hs₁ := summable_mnObjective (u := u) (hu := hu) x₁ hδ1
  have hs₂ := summable_mnObjective (u := u) (hu := hu) x₂ hδ1
  have hsm := summable_mnObjective (u := u) (hu := hu) m hδ1
  have hterm : ∀ t, θ * ((δ : ℝ) ^ t * u ((x₁ t : Fin N → ℝ), (x₁ (t + 1) : Fin N → ℝ)))
      + (1 - θ) * ((δ : ℝ) ^ t * u ((x₂ t : Fin N → ℝ), (x₂ (t + 1) : Fin N → ℝ)))
      ≤ (δ : ℝ) ^ t * u ((m t : Fin N → ℝ), (m (t + 1) : Fin N → ℝ)) := by
    intro t
    have hc := hconc.2 (⟨(x₁ t).2, (x₁ (t + 1)).2⟩ : ((x₁ t : Fin N → ℝ),
      (x₁ (t + 1) : Fin N → ℝ)) ∈ K ×ˢ K) (⟨(x₂ t).2, (x₂ (t + 1)).2⟩ :
      ((x₂ t : Fin N → ℝ), (x₂ (t + 1) : Fin N → ℝ)) ∈ K ×ˢ K) hθ0 (by linarith : 0 ≤ 1 - θ)
      (by ring)
    simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at hc
    have hp := pow_nonneg δ.coe_nonneg t
    simp only [hm]
    nlinarith [mul_le_mul_of_nonneg_left hc hp]
  have hsum := Summable.tsum_le_tsum hterm ((hs₁.mul_left θ).add (hs₂.mul_left (1 - θ))) hsm
  rw [(hs₁.mul_left θ).tsum_add (hs₂.mul_left (1 - θ)), hs₁.tsum_mul_left,
    hs₂.tsum_mul_left] at hsum
  unfold mnObjective at hv₁ hv₂ hle
  rw [← hv₁, ← hv₂]
  exact hsum.trans hle

/-- **The Euler equations (M.N.4)** (MWG, p. 969): along a maximizing sequence of (M.N.1) whose
pairs `(x_t, x_{t+1})` are interior to `A × A`, with `u` differentiable there (derivative `Du t`),
`∇₂u(x_t, x_{t+1}) + δ ∇₁u(x_{t+1}, x_{t+2}) = 0` for all `t` (MWG's `t ≥ 1` with
`x_{t-1}, x_t`). -/
theorem euler_M_N_4 (hδ0 : 0 < (δ : ℝ)) {z : K} {x : ℕ → K} (hx0 : x 0 = z)
    (hopt : mnObjective u δ x = (mnProgram u hu δ hδ).valueFunction z)
    (hint : ∀ t, ((x t : Fin N → ℝ), (x (t + 1) : Fin N → ℝ)) ∈ interior (K ×ˢ K))
    {Du : ℕ → (Fin N → ℝ) × (Fin N → ℝ) →L[ℝ] ℝ}
    (hDu : ∀ t, HasFDerivAt u (Du t) ((x t : Fin N → ℝ), (x (t + 1) : Fin N → ℝ))) :
    EulerEq (δ : ℝ) Du := by
  have hδ1 : (δ : ℝ) < 1 := by exact_mod_cast hδ
  -- the sequence is optimal among admissible ambient paths
  have hopt' : OptimalFrom (K ×ˢ K) (δ : ℝ) u (z : Fin N → ℝ) (fun t => (x t : Fin N → ℝ)) := by
    refine ⟨⟨congrArg Subtype.val hx0, fun t => ⟨(x t).2, (x (t + 1)).2⟩⟩,
      summable_mnObjective (u := u) (hu := hu) x hδ1, fun k' hk' _ => ?_⟩
    -- a competitor stays in `K`
    have hkK : ∀ t, k' t ∈ K := fun t => (hk'.2 t).1
    set x' : ℕ → K := fun t => ⟨k' t, hkK t⟩
    have hx'0 : x' 0 = z := Subtype.ext hk'.1
    obtain ⟨_, _, _, hmax⟩ := value_attained_M_N (u := u) (hu := hu) (δ := δ) (hδ := hδ) z
    have := hmax x' hx'0
    rw [← hopt] at this
    exact this
  exact euler_of_optimal hδ0 hopt' hint hDu

end MWG.EquilibriumTime

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Remarks on nonequilibrium dynamics (MWG Section 20.I, pp. 778-781)

MWG, Chapter 20, Section 20.I and Exercise 20.I.1 (p. 786).

* **Short-run equilibrium and permanent income**: with the marginal utilities of wealth `λ_i`
  fixed, (20.I.1) `δ^t ∇u_i(c_{it}) = λ_i p_t` defines short-run demands whose price derivative is
  `λ_i [D²u_i]⁻¹` (`shortRun_demand_derivative`), negative definite (`shortRun_negDef`), and so is
  the aggregate (`shortRun_aggregate_negDef`); an excess demand with negative definite derivative
  has at most one zero, so the short-run equilibrium is unique (`unique_zero_of_negDef`).
* **Exercise 20.I.1** (`exercise_20_I_1`): the identity relating the single-market law of demand
  in the overlapping generations model to the determinacy condition (20.H.3).
* **Learning**: by Walras' law (20.I.2) is (20.I.3) (`learning_walras`), and the adaptive dynamics
  reverse the equilibrium dynamics (`learning_reverses`, footnote 44).

OPEN: global tâtonnement stability of the short-run equilibrium, the effect of patience on `λ_i`
(heuristic), and the stability-determinacy correspondences (stated with "we neglect borderline
cases").
-/

open Filter Topology

namespace MWG.EquilibriumTime

variable {L : ℕ}

/-- **The short-run price effects** (MWG, p. 778): if `C` is the derivative of the short-run
demand `c₀(p₀, λ)` defined by `∇u(c₀) = λ p₀` and `H = D²u(c₀)` is invertible, differentiating
gives `H C = λ I`, hence `C = λ H⁻¹`. -/
theorem shortRun_demand_derivative {H C : Matrix (Fin L) (Fin L) ℝ} {lam : ℝ}
    (hH : IsUnit H.det) (hdiff : H * C = lam • (1 : Matrix (Fin L) (Fin L) ℝ)) :
    C = lam • H⁻¹ := by
  have := congrArg (fun M => H⁻¹ * M) hdiff
  simp only [Matrix.nonsing_inv_mul_cancel_left _ _ hH, Matrix.mul_smul, Matrix.mul_one] at this
  exact this

/-- **The short-run price effects are negative definite** (MWG, p. 778): if `D²u` is negative
definite and `λ > 0`, then `λ (D²u)⁻¹` is negative definite. -/
theorem shortRun_negDef {H : Matrix (Fin L) (Fin L) ℝ} (hH : (-H).PosDef) {lam : ℝ}
    (hlam : 0 < lam) : (-(lam • H⁻¹)).PosDef := by
  have hu : IsUnit H.det := by
    have := hH.isUnit
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_neg] at this
    exact (IsUnit.mul_iff.1 this).2
  have hinv : (-H)⁻¹ = -H⁻¹ := by
    refine Matrix.inv_eq_right_inv ?_
    rw [neg_mul_neg, Matrix.mul_nonsing_inv _ hu]
  have := hH.inv.smul hlam
  rw [hinv] at this
  rwa [smul_neg] at this

/-- **The aggregate short-run price effects are negative definite** (MWG, p. 778). -/
theorem shortRun_aggregate_negDef {ι : Type*} [Fintype ι] [Nonempty ι]
    {H : ι → Matrix (Fin L) (Fin L) ℝ} (hH : ∀ i, (-H i).PosDef) {lam : ι → ℝ}
    (hlam : ∀ i, 0 < lam i) : (-(∑ i, lam i • (H i)⁻¹)).PosDef := by
  classical
  rw [← Finset.sum_neg_distrib]
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
  have h0 := shortRun_negDef (hH i₀) (hlam i₀)
  refine Finset.induction_on (Finset.univ.erase i₀) (by simpa using h0) ?_
  intro j s hj ih
  rw [Finset.sum_insert hj, ← add_assoc, add_comm (-(lam i₀ • (H i₀)⁻¹)), add_assoc]
  exact (shortRun_negDef (hH j) (hlam j)).add ih

/-- **Uniqueness of the short-run equilibrium** (MWG, p. 778): an excess demand function whose
derivative is negative definite on a convex set (`v · Dz(p) v < 0` for `v ≠ 0`) has at most one
zero there; indeed `(p - p') · (z(p) - z(p')) < 0` for `p ≠ p'`. -/
theorem unique_zero_of_negDef {S : Set (Fin L → ℝ)} (hS : Convex ℝ S)
    {z : (Fin L → ℝ) → Fin L → ℝ} {Dz : (Fin L → ℝ) → (Fin L → ℝ) →L[ℝ] (Fin L → ℝ)}
    (hDz : ∀ x ∈ S, HasFDerivAt z (Dz x) x) (hneg : ∀ x ∈ S, ∀ v, v ≠ 0 → v ⬝ᵥ Dz x v < 0)
    {p p' : Fin L → ℝ} (hp : p ∈ S) (hp' : p' ∈ S) (hne : p ≠ p') :
    (p - p') ⬝ᵥ (z p - z p') < 0 := by
  set v := p - p' with hv
  have hv0 : v ≠ 0 := sub_ne_zero.2 hne
  set g : ℝ → ℝ := fun s => v ⬝ᵥ z (p' + s • v) with hg
  have hseg : ∀ s ∈ Set.Icc (0 : ℝ) 1, p' + s • v ∈ S := by
    intro s hs
    have := hS hp' hp (by linarith [hs.2] : 0 ≤ 1 - s) hs.1 (by ring)
    convert this using 1
    simp only [hv]
    module
  have hgd : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivAt g (v ⬝ᵥ Dz (p' + s • v) v) s := by
    intro s hs
    have hl : HasDerivAt (fun s : ℝ => p' + s • v) v s := by
      simpa using ((hasDerivAt_id s).smul_const v).const_add p'
    have h1 := (hDz _ (hseg s hs)).comp_hasDerivAt s hl
    have hcomp : ∀ i, HasDerivAt (fun s : ℝ => z (p' + s • v) i) ((Dz (p' + s • v) v) i) s :=
      fun i => hasDerivAt_pi.1 h1 i
    have := HasDerivAt.sum (u := Finset.univ) (fun i _ => (hcomp i).const_mul (v i))
    simp only [hg, dotProduct]
    convert this using 1
    funext s; simp
  obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope g (fun s => v ⬝ᵥ Dz (p' + s • v) v)
    (zero_lt_one) (fun s hs => (hgd s hs).continuousAt.continuousWithinAt)
    (fun s hs => hgd s (Set.Ioo_subset_Icc_self hs))
  have hlt := hneg _ (hseg c (Set.Ioo_subset_Icc_self hc)) v hv0
  rw [hceq] at hlt
  simp only [hg, zero_smul, add_zero, one_smul, hv, add_sub_cancel] at hlt
  rw [dotProduct_sub]
  linarith

/-- **Exercise 20.I.1** (MWG, p. 786): if the excess demands `z_b`, `z_a` of a generation are
homogeneous of degree zero in `(p_b, p_a)` and differentiable, then (with `∇₁`, `∇₂` the partial
derivatives)
`∇₂z_a(1/p, 1) + ∇₁z_b(1, p) = p ∇₂z_a(1, p) + ∇₁z_b(1, p) = -∇₁z_a(1, p) + ∇₁z_b(1, p)`. -/
theorem exercise_20_I_1 {za : ℝ × ℝ → ℝ} (hhom : ∀ c : ℝ, 0 < c → ∀ x, za (c • x) = za x)
    {p : ℝ} (hp : 0 < p) {D D' : ℝ × ℝ →L[ℝ] ℝ} (hD : HasFDerivAt za D (1, p))
    (hD' : HasFDerivAt za D' (1 / p, 1)) (zb1 : ℝ) :
    D' (0, 1) + zb1 = p * D (0, 1) + zb1 ∧ p * D (0, 1) + zb1 = -D (1, 0) + zb1 := by
  -- degree `-1` homogeneity of the derivative: `za(x) = za((1/p) • x)` near `(1, p)`
  have hscale : (1 / p) • ((1 : ℝ), p) = (1 / p, 1) := by
    ext <;> simp [hp.ne']
  have h1 : HasFDerivAt (fun x : ℝ × ℝ => za ((1 / p) • x))
      (D'.comp ((1 / p) • ContinuousLinearMap.id ℝ (ℝ × ℝ))) (1, p) := by
    have hl : HasFDerivAt (fun x : ℝ × ℝ => (1 / p) • x)
        ((1 / p) • ContinuousLinearMap.id ℝ (ℝ × ℝ)) (1, p) :=
      (hasFDerivAt_id _).const_smul (1 / p)
    rw [← hscale] at hD'
    exact hD'.comp _ hl
  have h2 : HasFDerivAt (fun x : ℝ × ℝ => za ((1 / p) • x)) D (1, p) := by
    refine hD.congr_of_eventuallyEq (Eventually.of_forall fun x => hhom (1 / p) (by positivity) x)
  have hEq := h2.unique h1
  have e1 : D (0, 1) = (1 / p) * D' (0, 1) := by
    rw [hEq]; simp
  -- Euler's theorem for degree zero: `D(1, p) = 0`
  have h3 : HasDerivAt (fun c : ℝ => za (c • ((1 : ℝ), p))) (D (1, p)) 1 := by
    have hl : HasDerivAt (fun c : ℝ => c • ((1 : ℝ), p)) ((1 : ℝ), p) 1 := by
      simpa using (hasDerivAt_id (1 : ℝ)).smul_const ((1 : ℝ), p)
    exact hD.comp_hasDerivAt_of_eq (1 : ℝ) hl (by simp)
  have h4 : HasDerivAt (fun c : ℝ => za (c • ((1 : ℝ), p))) 0 1 := by
    refine (hasDerivAt_const (1 : ℝ) (za ((1 : ℝ), p))).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds (zero_lt_one : (0 : ℝ) < 1)] with c hc
    exact hhom c hc _
  have hEuler := h3.unique h4
  have hsplit : D (1, p) = D (1, 0) + p * D (0, 1) := by
    rw [show ((1 : ℝ), p) = (1, 0) + p • ((0 : ℝ), (1 : ℝ)) by ext <;> simp, map_add, map_smul,
      smul_eq_mul]
  refine ⟨?_, ?_⟩
  · rw [e1]; field_simp
  · linarith

/-- **(20.I.2) is (20.I.3)** (MWG, p. 780): by Walras' law for the young,
`p_t z_b + p^e z_a = 0` with expected price `p^e = p_{t-1}`, the condition `z_b = -M/p_t` is
equivalent to `z_a = M/p_{t-1}`. -/
theorem learning_walras {pt pe zb za M : ℝ} (hpt : 0 < pt) (hpe : 0 < pe)
    (hW : pt * zb + pe * za = 0) : zb = -(M / pt) ↔ za = M / pe := by
  constructor
  · intro h
    rw [h] at hW
    field_simp at hW ⊢
    linarith
  · intro h
    rw [h] at hW
    field_simp at hW ⊢
    linarith

/-- **Footnote 44** (MWG, p. 781): the learning dynamics exactly reverse the equilibrium
dynamics. If the realizations `p_t` satisfy the adaptive rule `z_b(p_t, p_{t-1}) = -M/p_t`
(20.I.2) for `1 ≤ t ≤ T`, then `p'_s = p_{T-s}` satisfies the perfect-foresight equilibrium
condition `z_b(p'_s, p'_{s+1}) = -M/p'_s` for `s < T`. -/
theorem learning_reverses {zb : ℝ → ℝ → ℝ} {M : ℝ} {p : ℕ → ℝ} {T : ℕ}
    (hlearn : ∀ t, 1 ≤ t → t ≤ T → zb (p t) (p (t - 1)) = -(M / p t)) :
    ∀ s, s < T → zb (p (T - s)) (p (T - (s + 1))) = -(M / p (T - s)) := by
  intro s hs
  have := hlearn (T - s) (by omega) (by omega)
  rwa [show T - s - 1 = T - (s + 1) by omega] at this

end MWG.EquilibriumTime

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Global tâtonnement stability of the short-run equilibrium (MWG Section 20.I, p. 778)

MWG, Chapter 20, Section 20.I, p. 778: with the marginal utilities of wealth `λ_i` fixed, the
matrix of short-run price effects is negative definite, so "the short-run equilibrium is unique
and globally tâtonnement stable". Uniqueness is `unique_zero_of_negDef` (module
`Nonequilibrium`). Here is global stability for the tâtonnement `dp/dt = z(p)` of Section 17.H.

* `tatonnement_global_stable`: if `z` is continuous, `z(p*) = 0` and
  `(p - p*) · z(p) < 0` for every `p ≠ p*`, every solution of `dp/dt = z(p)` converges to `p*`
  as `t → ∞`. The Lyapunov function `V(t) = ‖p(t) - p*‖²` is nonincreasing; if its limit were
  positive, the trajectory would stay in a compact shell on which `(p - p*) · z(p)` is bounded
  away from zero, and `V` would decrease without bound.
* `tatonnement_global_stable_negDef`: the hypothesis of the book, a differentiable excess demand
  with negative definite derivative everywhere, implies the sign condition (by
  `unique_zero_of_negDef`), hence global stability.
* A proved instance: `z(p) = p* - p` with its explicit trajectories
  (`tatonnement_linear_instance`).
-/

open Filter Topology

namespace MWG.EquilibriumTime

variable {L : ℕ}

/-- The squared Euclidean distance as a dot product. -/
theorem sq_le_dotProduct_self (v : Fin L → ℝ) (l : Fin L) : v l ^ 2 ≤ v ⬝ᵥ v := by
  simp only [dotProduct, ← sq]
  exact Finset.single_le_sum (fun k _ => sq_nonneg (v k)) (Finset.mem_univ l)

/-- **Global tâtonnement stability** (MWG, p. 778, with Section 17.H): for a continuous excess
demand `z` with `z(p*) = 0` and `(p - p*) · z(p) < 0` for every `p ≠ p*`, every solution of the
tâtonnement `dp/dt = z(p)` converges to `p*`. -/
theorem tatonnement_global_stable {z : (Fin L → ℝ) → Fin L → ℝ} (hz : Continuous z)
    {pstar : Fin L → ℝ} (hsign : ∀ p, p ≠ pstar → (p - pstar) ⬝ᵥ z p < 0)
    {P : ℝ → Fin L → ℝ} (hP : ∀ t, HasDerivAt P (z (P t)) t) :
    Tendsto P atTop (𝓝 pstar) := by
  set V : ℝ → ℝ := fun t => (P t - pstar) ⬝ᵥ (P t - pstar) with hV
  have hV0 : ∀ t, 0 ≤ V t := fun t => by
    simp only [hV, dotProduct, ← sq]; exact Finset.sum_nonneg fun l _ => sq_nonneg _
  have hVd : ∀ t, HasDerivAt V (2 * ((P t - pstar) ⬝ᵥ z (P t))) t := by
    intro t
    have hc := hasDerivAt_pi.1 (hP t)
    have : HasDerivAt V (∑ l, 2 * ((P t l - pstar l) * z (P t) l)) t := by
      simp only [hV, dotProduct, Pi.sub_apply]
      refine HasDerivAt.fun_sum fun l _ => ?_
      have h1 := (hc l).sub_const (pstar l)
      convert h1.mul h1 using 1
      ring
    convert this using 1
    simp only [dotProduct, Pi.sub_apply, Finset.mul_sum]
  have hdiff : Differentiable ℝ V := fun t => (hVd t).differentiableAt
  have hanti : Antitone V := antitone_of_deriv_nonpos hdiff fun t => by
    rw [(hVd t).deriv]
    by_cases h : P t = pstar
    · simp [h]
    · linarith [hsign _ h]
  have hbdd : BddBelow (Set.range V) := ⟨0, by rintro _ ⟨t, rfl⟩; exact hV0 t⟩
  set Vinf := ⨅ t, V t with hVinf
  have hlim : Tendsto V atTop (𝓝 Vinf) := tendsto_atTop_ciInf hanti hbdd
  have hVinf0 : 0 ≤ Vinf := le_ciInf hV0
  have hle : ∀ t, Vinf ≤ V t := fun t => ciInf_le hbdd t
  -- the limit is zero
  have hzero : Vinf = 0 := by
    by_contra hne
    have hpos : 0 < Vinf := lt_of_le_of_ne hVinf0 (Ne.symm hne)
    -- the compact shell `Vinf ≤ ‖p - p*‖² ≤ V 0`
    set g : (Fin L → ℝ) → ℝ := fun p => (p - pstar) ⬝ᵥ (p - pstar) with hg
    have hgc : Continuous g := by
      simp only [hg, dotProduct]; fun_prop
    set K := g ⁻¹' Set.Icc Vinf (V 0) with hK
    set c := V 0 + 1 with hc
    have hKbox : K ⊆ Set.Icc (pstar - fun _ => c) (pstar + fun _ => c) := by
      intro p hp
      have hp2 : g p ≤ V 0 := hp.2
      have hb : ∀ l, |p l - pstar l| ≤ c := fun l => by
        have h1 := sq_le_dotProduct_self (p - pstar) l
        simp only [Pi.sub_apply] at h1
        have h2 : (p l - pstar l) ^ 2 ≤ V 0 := h1.trans hp2
        rcases le_or_gt |p l - pstar l| 1 with h | h
        · linarith [hV0 0]
        · have : |p l - pstar l| ≤ (p l - pstar l) ^ 2 := by
            rw [← sq_abs]; nlinarith [abs_nonneg (p l - pstar l)]
          linarith
      exact ⟨fun l => by have := (abs_le.1 (hb l)).1; simp only [Pi.sub_apply]; linarith,
        fun l => by have := (abs_le.1 (hb l)).2; simp only [Pi.add_apply]; linarith⟩
    have hKc : IsCompact K :=
      isCompact_Icc.of_isClosed_subset (isClosed_Icc.preimage hgc) hKbox
    have hKn : K.Nonempty := ⟨P 0, hle 0, le_rfl⟩
    set h : (Fin L → ℝ) → ℝ := fun p => (p - pstar) ⬝ᵥ z p with hh
    have hhc : Continuous h := by
      simp only [hh, dotProduct]; fun_prop
    obtain ⟨q, hqK, hqmax⟩ := hKc.exists_isMaxOn hKn hhc.continuousOn
    have hq : h q < 0 := by
      refine hsign q fun hqe => ?_
      have := hqK.1
      simp only [hg, hqe, sub_self, dotProduct_zero] at this
      linarith
    -- along the trajectory `V' ≤ 2 h(q) < 0`
    have hmem : ∀ t, 0 ≤ t → P t ∈ K := fun t ht => ⟨hle t, hanti ht⟩
    set m := h q with hm
    have hW : ∀ t, 0 ≤ t → V t ≤ V 0 + 2 * m * t := by
      have hd : ∀ t, HasDerivAt (fun t => V t - 2 * m * t) (2 * h (P t) - 2 * m) t :=
        fun t => by
          have := (hVd t).sub ((hasDerivAt_id' t).const_mul (2 * m))
          rw [mul_one] at this
          exact this
      have hWanti : AntitoneOn (fun t => V t - 2 * m * t) (Set.Ici 0) := by
        refine antitoneOn_of_deriv_nonpos (convex_Ici 0)
          (fun t _ => (hd t).continuousAt.continuousWithinAt)
          (fun t _ => (hd t).differentiableAt.differentiableWithinAt) fun t ht => ?_
        rw [interior_Ici] at ht
        rw [(hd t).deriv]
        have := hqmax (hmem t (le_of_lt ht))
        simp only [Set.mem_ofPred_eq] at this
        linarith
      intro t ht
      have := hWanti (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 ht) ht
      simp only [mul_zero, sub_zero] at this
      linarith
    have ht := hW (-(V 0 + 1) / (2 * m))
      (div_nonneg_of_nonpos (by linarith [hV0 0]) (by linarith))
    have hm0 : m ≠ 0 := ne_of_lt hq
    have : 2 * m * (-(V 0 + 1) / (2 * m)) = -(V 0 + 1) := by
      field_simp
    linarith [hV0 (-(V 0 + 1) / (2 * m))]
  -- conclude coordinatewise
  rw [hzero] at hlim
  refine tendsto_pi_nhds.2 fun l => ?_
  have hsq : Tendsto (fun t => Real.sqrt (V t)) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hlim
    rw [Real.sqrt_zero] at this
    exact this
  refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun _ => norm_nonneg _)
    (fun t => ?_) hsq)
  rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
  have := sq_le_dotProduct_self (P t - pstar) l
  simp only [Pi.sub_apply] at this
  exact Real.sqrt_le_sqrt this

/-- **Global tâtonnement stability, the book's hypothesis** (MWG, p. 778): if the short-run
excess demand `z` is differentiable with a negative definite derivative everywhere and
`z(p*) = 0`, every solution of `dp/dt = z(p)` converges to `p*`. -/
theorem tatonnement_global_stable_negDef {z : (Fin L → ℝ) → Fin L → ℝ}
    {Dz : (Fin L → ℝ) → (Fin L → ℝ) →L[ℝ] (Fin L → ℝ)} (hDz : ∀ x, HasFDerivAt z (Dz x) x)
    (hneg : ∀ x v, v ≠ 0 → v ⬝ᵥ Dz x v < 0) {pstar : Fin L → ℝ} (hzero : z pstar = 0)
    {P : ℝ → Fin L → ℝ} (hP : ∀ t, HasDerivAt P (z (P t)) t) :
    Tendsto P atTop (𝓝 pstar) := by
  refine tatonnement_global_stable (continuous_iff_continuousAt.2 fun x =>
    (hDz x).continuousAt) (fun p hp => ?_) hP
  have := unique_zero_of_negDef convex_univ (fun x _ => hDz x) (fun x _ => hneg x)
    (Set.mem_univ p) (Set.mem_univ pstar) hp
  rwa [hzero, sub_zero] at this

/-- A proved instance: the linear excess demand `z(p) = p* - p`, whose derivative `-I` is
negative definite, and its trajectories `p(t) = p* + e^{-t} (p₀ - p*)`, which converge to `p*`. -/
theorem tatonnement_linear_instance (pstar p₀ : Fin L → ℝ) :
    (∀ t, HasDerivAt (fun s => pstar + Real.exp (-s) • (p₀ - pstar))
      (pstar - (pstar + Real.exp (-t) • (p₀ - pstar))) t) ∧
      Tendsto (fun s => pstar + Real.exp (-s) • (p₀ - pstar)) atTop (𝓝 pstar) := by
  refine ⟨fun t => ?_, ?_⟩
  · have h := ((Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t)).smul_const (p₀ - pstar)
    have := h.const_add pstar
    exact this.congr_deriv (by rw [mul_neg_one, neg_smul]; abel)
  · have := tatonnement_global_stable_negDef (z := fun p => pstar - p)
      (Dz := fun _ => -ContinuousLinearMap.id ℝ (Fin L → ℝ))
      (fun x => (hasFDerivAt_id x).const_sub pstar)
      (fun x v hv => by
        change v ⬝ᵥ (-v) < 0
        rw [dotProduct_neg, neg_lt_zero]
        obtain ⟨l, hl⟩ := Function.ne_iff.1 hv
        exact lt_of_lt_of_le (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hl)))
          (sq_le_dotProduct_self v l))
      (sub_self pstar) (P := fun s => pstar + Real.exp (-s) • (p₀ - pstar)) (fun t => ?_)
    · exact this
    · have h := ((Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t)).smul_const (p₀ - pstar)
      have := h.const_add pstar
      exact this.congr_deriv (by rw [mul_neg_one, neg_smul]; abel)

end MWG.EquilibriumTime

set_option linter.style.longLine false
#print axioms MWG.EquilibriumTime.BoundedStream
#print axioms MWG.EquilibriumTime.NonnegStream
#print axioms MWG.EquilibriumTime.timeAdditiveUtility
#print axioms MWG.EquilibriumTime.discountedUtility
#print axioms MWG.EquilibriumTime.discountedUtility_eq_timeAdditive
#print axioms MWG.EquilibriumTime.backShift
#print axioms MWG.EquilibriumTime.forwardShift
#print axioms MWG.EquilibriumTime.summable_discounted
#print axioms MWG.EquilibriumTime.abs_utility_le_of_monotoneOn
#print axioms MWG.EquilibriumTime.summable_discounted_of_monotoneOn
#print axioms MWG.EquilibriumTime.footnote_20_2
#print axioms MWG.EquilibriumTime.NonnegStream.backShift
#print axioms MWG.EquilibriumTime.BoundedStream.backShift
#print axioms MWG.EquilibriumTime.discountedUtility_split
#print axioms MWG.EquilibriumTime.discountedUtility_recursive
#print axioms MWG.EquilibriumTime.discountedUtility_forwardShift
#print axioms MWG.EquilibriumTime.exercise_20_B_1
#print axioms MWG.EquilibriumTime.impatience_fails_at_zero_discount
#print axioms MWG.EquilibriumTime.exercise_20_B_2_stationary
#print axioms MWG.EquilibriumTime.stationarity_fails_at_zero_discount
#print axioms MWG.EquilibriumTime.quasiHyperbolic
#print axioms MWG.EquilibriumTime.exercise_20_B_2_violation
#print axioms MWG.EquilibriumTime.footnote_20_4
#print axioms MWG.EquilibriumTime.splice
#print axioms MWG.EquilibriumTime.discountedUtility_splice
#print axioms MWG.EquilibriumTime.exercise_20_B_3_future
#print axioms MWG.EquilibriumTime.exercise_20_B_3_past
#print axioms MWG.EquilibriumTime.survival_interpretation
#print axioms MWG.EquilibriumTime.altruism_dynasty
#print axioms MWG.EquilibriumTime.powAggregator
#print axioms MWG.EquilibriumTime.recursiveTrunc
#print axioms MWG.EquilibriumTime.recursiveTrunc_nonneg
#print axioms MWG.EquilibriumTime.exercise_20_B_4_bounded
#print axioms MWG.EquilibriumTime.recursiveTrunc_mono
#print axioms MWG.EquilibriumTime.recursiveUtility
#print axioms MWG.EquilibriumTime.exercise_20_B_4_limit
#print axioms MWG.EquilibriumTime.exercise_20_B_4_aggregator
#print axioms MWG.EquilibriumTime.recursive_aggregator_two_solutions
#print axioms MWG.EquilibriumTime.exercise_20_B_5_concave
#print axioms MWG.EquilibriumTime.exercise_20_B_5_affine
#print axioms MWG.EquilibriumTime.exercise_20_B_5_ordinal_not_additive
#print axioms MWG.EquilibriumTime.ProdPlan
#print axioms MWG.EquilibriumTime.StrictPos
#print axioms MWG.EquilibriumTime.dotProduct_pos_of_strictPos
#print axioms MWG.EquilibriumTime.TechAssumptions
#print axioms MWG.EquilibriumTime.TechAssumptions.mk
#print axioms MWG.EquilibriumTime.TechAssumptions.isClosed
#print axioms MWG.EquilibriumTime.TechAssumptions.convex
#print axioms MWG.EquilibriumTime.TechAssumptions.zero_mem
#print axioms MWG.EquilibriumTime.TechAssumptions.noFreeLunch
#print axioms MWG.EquilibriumTime.TechAssumptions.freeDisposal
#print axioms MWG.EquilibriumTime.TechAssumptions.truncation
#print axioms MWG.EquilibriumTime.truncation_of_nonneg_after
#print axioms MWG.EquilibriumTime.stackPlan
#print axioms MWG.EquilibriumTime.stackPlan_le_iff
#print axioms MWG.EquilibriumTime.stackPlan_zero
#print axioms MWG.EquilibriumTime.stackPlan_injective
#print axioms MWG.EquilibriumTime.stackPlan_surjective
#print axioms MWG.EquilibriumTime.noFreeLunch_iff_stack
#print axioms MWG.EquilibriumTime.freeDisposal_iff_stack
#print axioms MWG.EquilibriumTime.ramseySolowSet
#print axioms MWG.EquilibriumTime.ramseySolowSet_eq
#print axioms MWG.EquilibriumTime.ramseySolow_labor_primary
#print axioms MWG.EquilibriumTime.example_20_C_1
#print axioms MWG.EquilibriumTime.twoSectorSet
#print axioms MWG.EquilibriumTime.costAdjustmentSet
#print axioms MWG.EquilibriumTime.example_20_C_3_costAdjustment
#print axioms MWG.EquilibriumTime.mergeGoods
#print axioms MWG.EquilibriumTime.example_20_C_3_ramseySolow
#print axioms MWG.EquilibriumTime.multiSectorSet
#print axioms MWG.EquilibriumTime.IsProdPath
#print axioms MWG.EquilibriumTime.netOutput
#print axioms MWG.EquilibriumTime.ProdEfficient
#print axioms MWG.EquilibriumTime.planValue
#print axioms MWG.EquilibriumTime.periodProfit
#print axioms MWG.EquilibriumTime.MyopicProfitMax
#print axioms MWG.EquilibriumTime.Transversality
#print axioms MWG.EquilibriumTime.sum_value_netOutput
#print axioms MWG.EquilibriumTime.sum_value_netOutput'
#print axioms MWG.EquilibriumTime.sum_value_le_of_myopic
#print axioms MWG.EquilibriumTime.no_value_improvement
#print axioms MWG.EquilibriumTime.proposition_20_C_1
#print axioms MWG.EquilibriumTime.prodEfficient_not_mem_interior
#print axioms MWG.EquilibriumTime.storageSet
#print axioms MWG.EquilibriumTime.storageSet_eq
#print axioms MWG.EquilibriumTime.storageSet_techAssumptions
#print axioms MWG.EquilibriumTime.storagePath
#print axioms MWG.EquilibriumTime.example_20_C_5
#print axioms MWG.EquilibriumTime.ownRate
#print axioms MWG.EquilibriumTime.exercise_20_C_1
#print axioms MWG.EquilibriumTime.exercise_20_C_2
#print axioms MWG.EquilibriumTime.ProdWeaklyEfficient
#print axioms MWG.EquilibriumTime.exercise_20_C_3
#print axioms MWG.EquilibriumTime.BoundedPath
#print axioms MWG.EquilibriumTime.OverallProfitMax
#print axioms MWG.EquilibriumTime.tendsto_value_of_bounded
#print axioms MWG.EquilibriumTime.splicePath
#print axioms MWG.EquilibriumTime.splicePath_lt
#print axioms MWG.EquilibriumTime.splicePath_self
#print axioms MWG.EquilibriumTime.splicePath_gt
#print axioms MWG.EquilibriumTime.exercise_20_C_4a
#print axioms MWG.EquilibriumTime.exercise_20_C_4b
#print axioms MWG.EquilibriumTime.TEfficient
#print axioms MWG.EquilibriumTime.not_finite_change_of_myopic
#print axioms MWG.EquilibriumTime.exercise_20_C_5a
#print axioms MWG.EquilibriumTime.chainPlan
#print axioms MWG.EquilibriumTime.chainSet
#print axioms MWG.EquilibriumTime.chainSetNoReturn
#print axioms MWG.EquilibriumTime.chainStoragePath
#print axioms MWG.EquilibriumTime.chain_value_zero
#print axioms MWG.EquilibriumTime.chain_storage_myopic
#print axioms MWG.EquilibriumTime.exercise_20_C_5c_twoEfficient
#print axioms MWG.EquilibriumTime.chainDetourPath
#print axioms MWG.EquilibriumTime.exercise_20_C_5c_not_threeEfficient
#print axioms MWG.EquilibriumTime.SupportsAt
#print axioms MWG.EquilibriumTime.SmoothAt
#print axioms MWG.EquilibriumTime.planValue_smul
#print axioms MWG.EquilibriumTime.normalScale
#print axioms MWG.EquilibriumTime.normalScale_pos
#print axioms MWG.EquilibriumTime.normalPrices
#print axioms MWG.EquilibriumTime.malinvaud_of_proportional_normals
#print axioms MWG.EquilibriumTime.normalPrices_strictPos
#print axioms MWG.EquilibriumTime.tripleVec
#print axioms MWG.EquilibriumTime.tripleVec_le_iff
#print axioms MWG.EquilibriumTime.tripleVec_injective
#print axioms MWG.EquilibriumTime.dotProduct_tripleVec
#print axioms MWG.EquilibriumTime.twoDateSet
#print axioms MWG.EquilibriumTime.convex_twoDateSet
#print axioms MWG.EquilibriumTime.updateTwo
#print axioms MWG.EquilibriumTime.updateTwo_changes
#print axioms MWG.EquilibriumTime.efficient_twoDateSet
#print axioms MWG.EquilibriumTime.block1
#print axioms MWG.EquilibriumTime.block2
#print axioms MWG.EquilibriumTime.block3
#print axioms MWG.EquilibriumTime.tripleVec_blocks
#print axioms MWG.EquilibriumTime.proportional_normals_of_twoEfficient
#print axioms MWG.EquilibriumTime.malinvaud_of_twoEfficient
#print axioms MWG.EquilibriumTime.exercise_20_C_5b
#print axioms MWG.EquilibriumTime.clm_fin2_apply
#print axioms MWG.EquilibriumTime.rsPlan
#print axioms MWG.EquilibriumTime.rsPlan_mem
#print axioms MWG.EquilibriumTime.planValue_rsPlan
#print axioms MWG.EquilibriumTime.partial_nonneg_of_concave_mono
#print axioms MWG.EquilibriumTime.rsPath
#print axioms MWG.EquilibriumTime.rsPrices
#print axioms MWG.EquilibriumTime.rs_profitMax_of_foc
#print axioms MWG.EquilibriumTime.rs_foc_of_profitMax
#print axioms MWG.EquilibriumTime.example_20_C_6
#print axioms MWG.EquilibriumTime.exercise_20_C_6
#print axioms MWG.EquilibriumTime.efficient_of_20_C_1_20_C_2
#print axioms MWG.EquilibriumTime.example_20_C_7
#print axioms MWG.EquilibriumTime.example_20_C_7_no_adjustment
#print axioms MWG.EquilibriumTime.consumption
#print axioms MWG.EquilibriumTime.identity_20_D_1
#print axioms MWG.EquilibriumTime.InBudget
#print axioms MWG.EquilibriumTime.UtilityMax
#print axioms MWG.EquilibriumTime.expenditure_summable
#print axioms MWG.EquilibriumTime.discountedUtility_sub_of_finite
#print axioms MWG.EquilibriumTime.summable_of_finite_change
#print axioms MWG.EquilibriumTime.abs_add_smul_single_le
#print axioms MWG.EquilibriumTime.single_smul_pos
#print axioms MWG.EquilibriumTime.budget_binds
#print axioms MWG.EquilibriumTime.WalrasEq
#print axioms MWG.EquilibriumTime.WalrasEq.mk
#print axioms MWG.EquilibriumTime.WalrasEq.boundedPath
#print axioms MWG.EquilibriumTime.WalrasEq.boundedPrices
#print axioms MWG.EquilibriumTime.WalrasEq.pricesNonneg
#print axioms MWG.EquilibriumTime.WalrasEq.feasible
#print axioms MWG.EquilibriumTime.WalrasEq.myopic
#print axioms MWG.EquilibriumTime.WalrasEq.wealthSummable
#print axioms MWG.EquilibriumTime.WalrasEq.utilityMax
#print axioms MWG.EquilibriumTime.proposition_20_D_1
#print axioms MWG.EquilibriumTime.TotalProfitMax
#print axioms MWG.EquilibriumTime.exercise_20_D_2_to
#print axioms MWG.EquilibriumTime.exercise_20_D_2_of
#print axioms MWG.EquilibriumTime.MyopicUtilityMax
#print axioms MWG.EquilibriumTime.clm_apply_eq_sum
#print axioms MWG.EquilibriumTime.Foc20D5
#print axioms MWG.EquilibriumTime.Foc20D6
#print axioms MWG.EquilibriumTime.foc_20_D_5_iff_20_D_6
#print axioms MWG.EquilibriumTime.exercise_20_D_3
#print axioms MWG.EquilibriumTime.proposition_20_D_2
#print axioms MWG.EquilibriumTime.exercise_20_D_1
#print axioms MWG.EquilibriumTime.example_20_D_1_foc
#print axioms MWG.EquilibriumTime.exercise_20_D_4
#print axioms MWG.EquilibriumTime.example_20_D_1_i
#print axioms MWG.EquilibriumTime.linearTech
#print axioms MWG.EquilibriumTime.posOrthant1
#print axioms MWG.EquilibriumTime.logUtil
#print axioms MWG.EquilibriumTime.logUtil_concaveOn
#print axioms MWG.EquilibriumTime.logUtil_hasFDerivAt
#print axioms MWG.EquilibriumTime.example_20_D_1_ii
#print axioms MWG.EquilibriumTime.example_20_D_1_iii_false
#print axioms MWG.EquilibriumTime.example_20_D_1_iii_corrected
#print axioms MWG.EquilibriumTime.FeasiblePath
#print axioms MWG.EquilibriumTime.PlanOptimal
#print axioms MWG.EquilibriumTime.boundedStream_consumption
#print axioms MWG.EquilibriumTime.proposition_20_D_3
#print axioms MWG.EquilibriumTime.BoundedPath.update
#print axioms MWG.EquilibriumTime.eventually_pos_of_hasDerivAt
#print axioms MWG.EquilibriumTime.partial_bounds
#print axioms MWG.EquilibriumTime.proposition_20_D_4
#print axioms MWG.EquilibriumTime.summable_of_continuousOn
#print axioms MWG.EquilibriumTime.continuous_consumption
#print axioms MWG.EquilibriumTime.consumption_zero
#print axioms MWG.EquilibriumTime.proposition_20_D_5
#print axioms MWG.EquilibriumTime.consumption_mix
#print axioms MWG.EquilibriumTime.proposition_20_D_6
#print axioms MWG.EquilibriumTime.concave_le_fderiv_normed
#print axioms MWG.EquilibriumTime.summable_of_eq_off
#print axioms MWG.EquilibriumTime.tsum_sub_eq_of_eq_off
#print axioms MWG.EquilibriumTime.Admissible
#print axioms MWG.EquilibriumTime.reducedObjective
#print axioms MWG.EquilibriumTime.objective_20_D_8
#print axioms MWG.EquilibriumTime.OptimalFrom
#print axioms MWG.EquilibriumTime.EulerEq
#print axioms MWG.EquilibriumTime.euler_of_shortRun
#print axioms MWG.EquilibriumTime.euler_of_optimal
#print axioms MWG.EquilibriumTime.euler_telescope
#print axioms MWG.EquilibriumTime.exercise_20_D_6
#print axioms MWG.EquilibriumTime.abs_fderiv_le_of_concave
#print axioms MWG.EquilibriumTime.proposition_20_D_7
#print axioms MWG.EquilibriumTime.reducedObjective_succ
#print axioms MWG.EquilibriumTime.consPath
#print axioms MWG.EquilibriumTime.consPath_zero
#print axioms MWG.EquilibriumTime.consPath_succ
#print axioms MWG.EquilibriumTime.reducedObjective_consPath
#print axioms MWG.EquilibriumTime.optimal_tail
#print axioms MWG.EquilibriumTime.policy_20_D_10
#print axioms MWG.EquilibriumTime.optimal_unique
#print axioms MWG.EquilibriumTime.IsValueFn
#print axioms MWG.EquilibriumTime.bellman_20_D_11
#print axioms MWG.EquilibriumTime.bellman_20_D_11_printed_false
#print axioms MWG.EquilibriumTime.exercise_20_D_8_i
#print axioms MWG.EquilibriumTime.exercise_20_D_8_ii
#print axioms MWG.EquilibriumTime.second_deriv_nonneg_of_isLocalMin
#print axioms MWG.EquilibriumTime.exercise_20_D_9_first
#print axioms MWG.EquilibriumTime.exercise_20_D_9_second
#print axioms MWG.EquilibriumTime.example_20_D_2_deriv
#print axioms MWG.EquilibriumTime.example_20_D_2
#print axioms MWG.EquilibriumTime.example_20_D_2_ratio
#print axioms MWG.EquilibriumTime.example_20_D_3_deriv
#print axioms MWG.EquilibriumTime.example_20_D_3
#print axioms MWG.EquilibriumTime.hasSum_of_recursion
#print axioms MWG.EquilibriumTime.example_20_D_3_iterated
#print axioms MWG.EquilibriumTime.powCost
#print axioms MWG.EquilibriumTime.exercise_20_D_5_gamma_deriv_zero
#print axioms MWG.EquilibriumTime.exercise_20_D_5_gamma_deriv_pos
#print axioms MWG.EquilibriumTime.exercise_20_D_5_gamma_deriv_neg
#print axioms MWG.EquilibriumTime.exercise_20_D_5_F_deriv
#print axioms MWG.EquilibriumTime.exercise_20_D_5_steady_state
#print axioms MWG.EquilibriumTime.exercise_20_D_7_euler
#print axioms MWG.EquilibriumTime.example_20_D_4_deriv
#print axioms MWG.EquilibriumTime.exercise_20_D_7_solution
#print axioms MWG.EquilibriumTime.exercise_20_D_7_unique
#print axioms MWG.EquilibriumTime.example_20_D_4_consumption
#print axioms MWG.EquilibriumTime.example_20_D_4_negative
#print axioms MWG.EquilibriumTime.example_20_D_4_unbounded
#print axioms MWG.EquilibriumTime.example_20_D_4_bounded_iff
#print axioms MWG.EquilibriumTime.example_20_D_4_not_optimal
#print axioms MWG.EquilibriumTime.example_20_D_4_infeasible
#print axioms MWG.EquilibriumTime.footnote_20_17
#print axioms MWG.EquilibriumTime.logRegion
#print axioms MWG.EquilibriumTime.example_20_D_4_optimal
#print axioms MWG.EquilibriumTime.IsStationary
#print axioms MWG.EquilibriumTime.propPrices
#print axioms MWG.EquilibriumTime.exercise_20_E_1
#print axioms MWG.EquilibriumTime.clm_prod_eq_planValue
#print axioms MWG.EquilibriumTime.exists_mem_of_smooth_neg
#print axioms MWG.EquilibriumTime.supporting_prices_proportional
#print axioms MWG.EquilibriumTime.proposition_20_E_1
#print axioms MWG.EquilibriumTime.proposition_20_E_2_pos
#print axioms MWG.EquilibriumTime.proposition_20_E_2_neg
#print axioms MWG.EquilibriumTime.IsModifiedGoldenRule
#print axioms MWG.EquilibriumTime.IsGoldenRule
#print axioms MWG.EquilibriumTime.stationary_equilibrium_modified_golden_rule
#print axioms MWG.EquilibriumTime.IsConeTech
#print axioms MWG.EquilibriumTime.smoothAt_smul_of_cone
#print axioms MWG.EquilibriumTime.malinvaud_prop_of_common_normal
#print axioms MWG.EquilibriumTime.exercise_20_E_2a
#print axioms MWG.EquilibriumTime.exercise_20_E_2b_pos
#print axioms MWG.EquilibriumTime.exercise_20_E_2b_neg
#print axioms MWG.EquilibriumTime.exercise_20_E_9
#print axioms MWG.EquilibriumTime.chord_right_le
#print axioms MWG.EquilibriumTime.strict_tangent_below
#print axioms MWG.EquilibriumTime.strictMonoOn_left_of_max
#print axioms MWG.EquilibriumTime.strictAntiOn_right_of_max
#print axioms MWG.EquilibriumTime.hasDerivAt_capital
#print axioms MWG.EquilibriumTime.rs_interest_rate
#print axioms MWG.EquilibriumTime.rs_steady_prices
#print axioms MWG.EquilibriumTime.golden_rule_iff
#print axioms MWG.EquilibriumTime.modified_golden_rule_iff
#print axioms MWG.EquilibriumTime.rate_pos_below_golden
#print axioms MWG.EquilibriumTime.rate_neg_above_golden
#print axioms MWG.EquilibriumTime.inefficient_above_golden
#print axioms MWG.EquilibriumTime.golden_rule_capital
#print axioms MWG.EquilibriumTime.golden_rule_efficient
#print axioms MWG.EquilibriumTime.exercise_20_E_3
#print axioms MWG.EquilibriumTime.modified_golden_rule_below
#print axioms MWG.EquilibriumTime.exercise_20_E_4_i_mono
#print axioms MWG.EquilibriumTime.exercise_20_E_4_i_anti
#print axioms MWG.EquilibriumTime.exercise_20_E_4_ii
#print axioms MWG.EquilibriumTime.euler_homogeneous
#print axioms MWG.EquilibriumTime.exercise_20_E_4_iii_wage
#print axioms MWG.EquilibriumTime.exercise_20_E_4_iii
#print axioms MWG.EquilibriumTime.exercise_20_E_8_surplus
#print axioms MWG.EquilibriumTime.exercise_20_E_8
#print axioms MWG.EquilibriumTime.eq_20_E_1
#print axioms MWG.EquilibriumTime.golden_rule_multisector
#print axioms MWG.EquilibriumTime.exercise_20_E_6
#print axioms MWG.EquilibriumTime.exercise_20_E_7
#print axioms MWG.EquilibriumTime.golden_rule_multisector_efficient
#print axioms MWG.EquilibriumTime.golden_rule_linear_inefficient
#print axioms MWG.EquilibriumTime.golden_rule_quadratic_instance
#print axioms MWG.EquilibriumTime.steady_state_iff_fixed
#print axioms MWG.EquilibriumTime.monotone_policy_converges
#print axioms MWG.EquilibriumTime.monotone_policy_converges_unique
#print axioms MWG.EquilibriumTime.two_cycle_example
#print axioms MWG.EquilibriumTime.three_cycle_example
#print axioms MWG.EquilibriumTime.policy_deriv
#print axioms MWG.EquilibriumTime.policy_deriv_bound_printed_false
#print axioms MWG.EquilibriumTime.policy_deriv_lower_bound
#print axioms MWG.EquilibriumTime.exercise_20_F_2
#print axioms MWG.EquilibriumTime.exercise_20_F_2_false
#print axioms MWG.EquilibriumTime.footnote_20_26
#print axioms MWG.EquilibriumTime.cycle_beaten_by_mean
#print axioms MWG.EquilibriumTime.StrictIncDiff
#print axioms MWG.EquilibriumTime.increasing_differences_of_cross_pos
#print axioms MWG.EquilibriumTime.policy_mono_of_increasing_differences
#print axioms MWG.EquilibriumTime.policy_anti_of_decreasing_differences
#print axioms MWG.EquilibriumTime.exercise_20_F_3_rs
#print axioms MWG.EquilibriumTime.exercise_20_F_3_adjustment
#print axioms MWG.EquilibriumTime.example_20_F_1
#print axioms MWG.EquilibriumTime.exercise_20_F_4
#print axioms MWG.EquilibriumTime.exercise_20_F_5
#print axioms MWG.EquilibriumTime.exercise_20_F_1_engel
#print axioms MWG.EquilibriumTime.WalrasEqI
#print axioms MWG.EquilibriumTime.WalrasEqI.mk
#print axioms MWG.EquilibriumTime.WalrasEqI.boundedPath
#print axioms MWG.EquilibriumTime.WalrasEqI.boundedPrices
#print axioms MWG.EquilibriumTime.WalrasEqI.pricesNonneg
#print axioms MWG.EquilibriumTime.WalrasEqI.feasible
#print axioms MWG.EquilibriumTime.WalrasEqI.myopic
#print axioms MWG.EquilibriumTime.WalrasEqI.profitSummable
#print axioms MWG.EquilibriumTime.WalrasEqI.endowSummable
#print axioms MWG.EquilibriumTime.WalrasEqI.utilityMax
#print axioms MWG.EquilibriumTime.wealthI
#print axioms MWG.EquilibriumTime.FeasibleAlloc
#print axioms MWG.EquilibriumTime.exists_better_of_slack
#print axioms MWG.EquilibriumTime.sum_wealthI
#print axioms MWG.EquilibriumTime.proposition_20_G_1
#print axioms MWG.EquilibriumTime.walrasEqI_example
#print axioms MWG.EquilibriumTime.negishiUtility
#print axioms MWG.EquilibriumTime.weighted_supergradient
#print axioms MWG.EquilibriumTime.negishiUtility_props
#print axioms MWG.EquilibriumTime.proposition_20_G_2
#print axioms MWG.EquilibriumTime.exercise_20_G_1
#print axioms MWG.EquilibriumTime.eq_20_G_6
#print axioms MWG.EquilibriumTime.exercise_20_G_5
#print axioms MWG.EquilibriumTime.dampening_of_small_coefficients
#print axioms MWG.EquilibriumTime.ParetoOptimalExchange
#print axioms MWG.EquilibriumTime.discountedUtility_finite_change
#print axioms MWG.EquilibriumTime.pareto_ratio_core
#print axioms MWG.EquilibriumTime.exercise_20_G_2
#print axioms MWG.EquilibriumTime.exercise_20_G_2_ratio
#print axioms MWG.EquilibriumTime.paretoOptimalExchange_linear
#print axioms MWG.EquilibriumTime.strictConcave_lt_fderiv
#print axioms MWG.EquilibriumTime.StaticWalrasEq
#print axioms MWG.EquilibriumTime.staticWalrasEq_noTrade
#print axioms MWG.EquilibriumTime.static_foc
#print axioms MWG.EquilibriumTime.exercise_20_G_4_repetition
#print axioms MWG.EquilibriumTime.exercise_20_G_4_static
#print axioms MWG.EquilibriumTime.exercise_20_G_3a
#print axioms MWG.EquilibriumTime.negishiPrice
#print axioms MWG.EquilibriumTime.exercise_20_G_3b
#print axioms MWG.EquilibriumTime.twoDateStream
#print axioms MWG.EquilibriumTime.twoDate_value
#print axioms MWG.EquilibriumTime.twoDate_props
#print axioms MWG.EquilibriumTime.SameRanking
#print axioms MWG.EquilibriumTime.sameRanking_affine
#print axioms MWG.EquilibriumTime.additive_jensen
#print axioms MWG.EquilibriumTime.affine_of_weighted_jensen
#print axioms MWG.EquilibriumTime.exercise_20_B_5_unique
#print axioms MWG.EquilibriumTime.olgWealth
#print axioms MWG.EquilibriumTime.OLGEq
#print axioms MWG.EquilibriumTime.OLGEq.mk
#print axioms MWG.EquilibriumTime.OLGEq.pricesPos
#print axioms MWG.EquilibriumTime.OLGEq.bubble_nonneg
#print axioms MWG.EquilibriumTime.OLGEq.assetFinite
#print axioms MWG.EquilibriumTime.OLGEq.cons_nonneg
#print axioms MWG.EquilibriumTime.OLGEq.budget
#print axioms MWG.EquilibriumTime.OLGEq.optimal
#print axioms MWG.EquilibriumTime.OLGEq.feasible_zero
#print axioms MWG.EquilibriumTime.OLGEq.feasible
#print axioms MWG.EquilibriumTime.fundamental_value_bound
#print axioms MWG.EquilibriumTime.olg_steady_alpha
#print axioms MWG.EquilibriumTime.olg_budget_binds
#print axioms MWG.EquilibriumTime.olg_cost_ge
#print axioms MWG.EquilibriumTime.olg_cost_gt
#print axioms MWG.EquilibriumTime.olg_total_wealth
#print axioms MWG.EquilibriumTime.proposition_20_H_1
#print axioms MWG.EquilibriumTime.olg_consumption_value
#print axioms MWG.EquilibriumTime.proposition_20_H_2
#print axioms MWG.EquilibriumTime.olg_nominal_identity
#print axioms MWG.EquilibriumTime.olg_bubble_zero_iff_autarky
#print axioms MWG.EquilibriumTime.olg_autarky_equilibrium
#print axioms MWG.EquilibriumTime.olg_autarky_linear
#print axioms MWG.EquilibriumTime.olg_autarky_dominated
#print axioms MWG.EquilibriumTime.monetary_steady_state_prices_log
#print axioms MWG.EquilibriumTime.backward_shift
#print axioms MWG.EquilibriumTime.exercise_20_H_1
#print axioms MWG.EquilibriumTime.monetaryCb
#print axioms MWG.EquilibriumTime.monetary_steady_state_optimal
#print axioms MWG.EquilibriumTime.sqrt_utility_unique_max
#print axioms MWG.EquilibriumTime.monetary_steady_state_optimal_sqrt
#print axioms MWG.EquilibriumTime.cycleU
#print axioms MWG.EquilibriumTime.cycleCa
#print axioms MWG.EquilibriumTime.cycleCb
#print axioms MWG.EquilibriumTime.cyclePrice
#print axioms MWG.EquilibriumTime.figure_20_H_5_period_two
#print axioms MWG.EquilibriumTime.cycle3U
#print axioms MWG.EquilibriumTime.cycle3Ca
#print axioms MWG.EquilibriumTime.cycle3Cb
#print axioms MWG.EquilibriumTime.cycle3Price
#print axioms MWG.EquilibriumTime.figure_20_H_6_period_three
#print axioms MWG.EquilibriumTime.OLGParetoOptimal
#print axioms MWG.EquilibriumTime.sqrtU
#print axioms MWG.EquilibriumTime.olgParetoOptimal_monetary
#print axioms MWG.EquilibriumTime.sqrt_demand
#print axioms MWG.EquilibriumTime.olg_sqrt_demand
#print axioms MWG.EquilibriumTime.olg_sqrt_classification
#print axioms MWG.EquilibriumTime.olg_sqrt_optimal_iff_bubble
#print axioms MWG.EquilibriumTime.exercise_20_H_2b_sqrt
#print axioms MWG.EquilibriumTime.sqrt_determinacy_condition
#print axioms MWG.EquilibriumTime.mnReward
#print axioms MWG.EquilibriumTime.mnProgram
#print axioms MWG.EquilibriumTime.mnObjective
#print axioms MWG.EquilibriumTime.mnPlan
#print axioms MWG.EquilibriumTime.mnPlan_value
#print axioms MWG.EquilibriumTime.plan_value_eq
#print axioms MWG.EquilibriumTime.value_attained_M_N
#print axioms MWG.EquilibriumTime.value_continuous_M_N
#print axioms MWG.EquilibriumTime.bellman_M_N
#print axioms MWG.EquilibriumTime.theorem_M_N_1
#print axioms MWG.EquilibriumTime.value_iteration_M_N
#print axioms MWG.EquilibriumTime.value_iteration_pointwise_M_N
#print axioms MWG.EquilibriumTime.summable_mnObjective
#print axioms MWG.EquilibriumTime.value_concave_M_N
#print axioms MWG.EquilibriumTime.euler_M_N_4
#print axioms MWG.EquilibriumTime.shortRun_demand_derivative
#print axioms MWG.EquilibriumTime.shortRun_negDef
#print axioms MWG.EquilibriumTime.shortRun_aggregate_negDef
#print axioms MWG.EquilibriumTime.unique_zero_of_negDef
#print axioms MWG.EquilibriumTime.exercise_20_I_1
#print axioms MWG.EquilibriumTime.learning_walras
#print axioms MWG.EquilibriumTime.learning_reverses
#print axioms MWG.EquilibriumTime.sq_le_dotProduct_self
#print axioms MWG.EquilibriumTime.tatonnement_global_stable
#print axioms MWG.EquilibriumTime.tatonnement_global_stable_negDef
#print axioms MWG.EquilibriumTime.tatonnement_linear_instance
