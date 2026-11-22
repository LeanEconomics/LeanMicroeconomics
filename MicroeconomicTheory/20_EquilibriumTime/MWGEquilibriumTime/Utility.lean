/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Order.MonotoneConvergence

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
