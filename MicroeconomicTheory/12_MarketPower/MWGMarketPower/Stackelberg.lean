/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGMarketPower.CournotBestResponse

/-!
# Slopes of best responses and the Stackelberg model

MWG, Exercises 12.C.12 and 12.C.18, pp. 432-433.

* `sc_strictMonoOn_diff`, `sc_topkis`: if a player's marginal profit is strictly increasing in
  the rival's choice, the profit has strictly increasing differences and every selection of
  maximizers is nondecreasing (a revealed-preference argument).
* (12.C.12(a)) `exercise_12_C_12a`: for profits `πⱼ(qⱼ, qₖ)` differentiable on `[0, q̄]`, the
  best response is nondecreasing if `∂²πⱼ/∂qⱼ∂qₖ > 0` and nonincreasing if
  `∂²πⱼ/∂qⱼ∂qₖ < 0`, strictly so where it is interior; `exercise_12_C_12a_unique`: strict
  concavity makes the best response unique.
* (12.C.12(b)) `exercise_12_C_12b`: in the Cournot model `πⱼ = p(qⱼ + qₖ)qⱼ − cⱼ(qⱼ)` the cross
  partial is `p'(Q) + p''(Q)qⱼ`; when it is negative best responses slope down.
  `exercise_12_C_12b_normal`: it is negative whenever `p' < 0` and `p'(Q) + p''(Q)Q < 0` (in
  particular for concave demand), which is why downward-sloping best responses are the normal
  case; `exercise_12_C_12b_instance`: linear demand.
* (12.C.18(a)) `exercise_12_C_18a`: with `p' < 0`, `p'(q) + p''(q)q < 0` for `q ≥ 0`, constant
  unit cost `c < p(0)`, a Cournot equilibrium, a follower best-response function and a leader
  optimum (existence is assumed explicitly): the leader produces more than its Cournot output and
  earns strictly more, aggregate output is larger and the follower earns strictly less.
  `exercise_12_C_18a_instance`: linear demand `p(q) = 1 − q`, `c = 0`.
  (12.C.18(b) is graphical.)

The leader's strict gain is proved by parametrizing the follower's reaction by aggregate output
`Q`: the follower's first-order condition gives `y(Q) = (p(Q) − c)/(−p'(Q))`, the leader output
`r(Q) = Q − y(Q)` and the leader profit `Π(Q) = (p(Q) − c)r(Q)`, whose derivative at the Cournot
output is `−q̂(p' + q̂p'') > 0`.

Departures: `p` is twice differentiable on `ℝ`; MWG's hypotheses are completed by `p(0) > c`
(otherwise nothing is produced) and the existence of the equilibria compared.
-/

namespace MWG.MarketPower

open Set Filter Topology

/-- Increasing differences from a marginal-profit comparison: if `∂π/∂u(u, r) < ∂π/∂u(u, r')`
on the interior of the convex set `S`, then `u ↦ π(u, r') − π(u, r)` is strictly increasing
on `S`. -/
theorem sc_strictMonoOn_diff {π D : ℝ → ℝ → ℝ} {S : Set ℝ} (hS : Convex ℝ S) {r r' : ℝ}
    (hπr : ∀ y ∈ S, HasDerivWithinAt (fun u => π u r) (D y r) S y)
    (hπr' : ∀ y ∈ S, HasDerivWithinAt (fun u => π u r') (D y r') S y)
    (hlt : ∀ y ∈ interior S, D y r < D y r') :
    StrictMonoOn (fun u => π u r' - π u r) S := by
  refine strictMonoOn_of_hasDerivWithinAt_pos (f' := fun y => D y r' - D y r) hS
    (fun y hy => ((hπr' y hy).sub (hπr y hy)).continuousWithinAt) (fun y hy => ?_)
    (fun y hy => sub_pos.2 (hlt y hy))
  exact ((hπr' y (interior_subset hy)).sub (hπr y (interior_subset hy))).mono interior_subset

/-- **Monotone comparative statics** (revealed preference). If `π(u, r') − π(u, r)` is strictly
increasing in `u` on `S`, `y` maximizes `π(·, r)` and `y'` maximizes `π(·, r')` on `S`, then
`y ≤ y'`. -/
theorem sc_topkis {π : ℝ → ℝ → ℝ} {S : Set ℝ} {r r' y y' : ℝ}
    (hID : StrictMonoOn (fun u => π u r' - π u r) S) (hy : y ∈ S) (hy' : y' ∈ S)
    (hmax : ∀ u ∈ S, π u r ≤ π y r) (hmax' : ∀ u ∈ S, π u r' ≤ π y' r') : y ≤ y' := by
  by_contra hlt
  push Not at hlt
  have h1 := hID hy' hy hlt
  have h2 := hmax y' hy'
  have h3 := hmax' y hy
  simp only at h1
  linarith

/-- A maximizer in the interior of `[0, q̄]` satisfies the first-order condition. -/
theorem sc_foc_interior {f : ℝ → ℝ} {d qbar y : ℝ} (hd : HasDerivWithinAt f d (Icc 0 qbar) y)
    (hy : y ∈ Ioo 0 qbar) (hmax : ∀ u ∈ Icc 0 qbar, f u ≤ f y) : d = 0 := by
  have hmem : Icc 0 qbar ∈ 𝓝 y := Icc_mem_nhds hy.1 hy.2
  have hloc : IsLocalMax f y := Filter.eventually_of_mem hmem hmax
  exact hloc.hasDerivAt_eq_zero (hd.hasDerivAt hmem)

/-- **Exercise 12.C.12(a)** (MWG, p. 432). Let `π(qⱼ, qₖ)` be firm `j`'s profit on
`[0, q̄]²`, differentiable in `qⱼ` with partial derivative `D(qⱼ, qₖ)`, itself differentiable in
`qₖ` with partial derivative `D₂(qⱼ, qₖ) = ∂²π/∂qⱼ∂qₖ`, and let `b(qₖ)` maximize `π(·, qₖ)` on
`[0, q̄]`. If `∂²π/∂qⱼ∂qₖ > 0` the best response is nondecreasing, and strictly increasing
from any interior point; if `∂²π/∂qⱼ∂qₖ < 0` it is nonincreasing, and strictly decreasing from
any interior point. -/
theorem exercise_12_C_12a {π D D₂ : ℝ → ℝ → ℝ} {qbar : ℝ}
    (hπ : ∀ r ∈ Icc 0 qbar, ∀ y ∈ Icc 0 qbar,
      HasDerivWithinAt (fun u => π u r) (D y r) (Icc 0 qbar) y)
    (hD : ∀ y ∈ Icc 0 qbar, ∀ r ∈ Icc 0 qbar, HasDerivWithinAt (D y) (D₂ y r) (Icc 0 qbar) r)
    {b : ℝ → ℝ}
    (hb : ∀ r ∈ Icc 0 qbar, b r ∈ Icc 0 qbar ∧ ∀ u ∈ Icc 0 qbar, π u r ≤ π (b r) r) :
    ((∀ y ∈ Icc 0 qbar, ∀ r ∈ Icc 0 qbar, 0 < D₂ y r) →
      MonotoneOn b (Icc 0 qbar) ∧
        ∀ r ∈ Icc 0 qbar, ∀ r' ∈ Icc 0 qbar, r < r' → b r ∈ Ioo 0 qbar → b r < b r') ∧
    ((∀ y ∈ Icc 0 qbar, ∀ r ∈ Icc 0 qbar, D₂ y r < 0) →
      AntitoneOn b (Icc 0 qbar) ∧
        ∀ r ∈ Icc 0 qbar, ∀ r' ∈ Icc 0 qbar, r < r' → b r ∈ Ioo 0 qbar → b r' < b r) := by
  have hcont : ∀ y ∈ Icc 0 qbar, ContinuousOn (D y) (Icc 0 qbar) := fun y hy r hr =>
    (hD y hy r hr).continuousWithinAt
  have hint : ∀ y ∈ Icc 0 qbar, ∀ r ∈ interior (Icc (0 : ℝ) qbar),
      HasDerivWithinAt (D y) (D₂ y r) (interior (Icc 0 qbar)) r := fun y hy r hr =>
    (hD y hy r (interior_subset hr)).mono interior_subset
  -- the first-order condition at an interior best response
  have hfoc : ∀ r ∈ Icc 0 qbar, b r ∈ Ioo 0 qbar → D (b r) r = 0 := fun r hr hbr =>
    sc_foc_interior (hπ r hr (b r) (hb r hr).1) hbr (hb r hr).2
  constructor
  · intro hpos
    have hmono : ∀ y ∈ Icc 0 qbar, StrictMonoOn (D y) (Icc 0 qbar) := fun y hy =>
      strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc 0 qbar) (hcont y hy) (hint y hy)
        fun r hr => hpos y hy r (interior_subset hr)
    have hle : MonotoneOn b (Icc 0 qbar) := by
      intro r hr r' hr' hrr
      rcases eq_or_lt_of_le hrr with h | h
      · rw [h]
      have hID := sc_strictMonoOn_diff (π := π) (D := D) (convex_Icc 0 qbar)
        (fun y hy => hπ r hr y hy) (fun y hy => hπ r' hr' y hy)
        (fun y hy => hmono y (interior_subset hy) hr hr' h)
      exact sc_topkis hID (hb r hr).1 (hb r' hr').1 (hb r hr).2 (hb r' hr').2
    refine ⟨hle, fun r hr r' hr' hrr hbr => lt_of_le_of_ne (hle hr hr' hrr.le) fun heq => ?_⟩
    have h0 := hfoc r hr hbr
    have h1 : D (b r) r' = 0 := by
      have := sc_foc_interior (hπ r' hr' (b r) (hb r hr).1) hbr (by
        rw [heq]; exact (hb r' hr').2)
      exact this
    have := hmono (b r) (hb r hr).1 hr hr' hrr
    linarith
  · intro hneg
    have hanti : ∀ y ∈ Icc 0 qbar, StrictAntiOn (D y) (Icc 0 qbar) := fun y hy =>
      strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc 0 qbar) (hcont y hy) (hint y hy)
        fun r hr => hneg y hy r (interior_subset hr)
    have hle : AntitoneOn b (Icc 0 qbar) := by
      intro r hr r' hr' hrr
      rcases eq_or_lt_of_le hrr with h | h
      · rw [h]
      have hID := sc_strictMonoOn_diff (π := π) (D := D) (convex_Icc 0 qbar)
        (fun y hy => hπ r' hr' y hy) (fun y hy => hπ r hr y hy)
        (fun y hy => hanti y (interior_subset hy) hr hr' h)
      exact sc_topkis hID (hb r' hr').1 (hb r hr).1 (hb r' hr').2 (hb r hr).2
    refine ⟨hle, fun r hr r' hr' hrr hbr =>
      lt_of_le_of_ne (hle hr hr' hrr.le) fun heq => ?_⟩
    have h0 := hfoc r hr hbr
    have h1 : D (b r) r' = 0 :=
      sc_foc_interior (hπ r' hr' (b r) (hb r hr).1) hbr (by rw [← heq]; exact (hb r' hr').2)
    have := hanti (b r) (hb r hr).1 hr hr' hrr
    linarith

/-- **Exercise 12.C.12(a), uniqueness** (MWG, p. 432). If `π(·, qₖ)` is strictly concave on
`[0, q̄]`, it has at most one maximizer there, so the best response is a function. -/
theorem exercise_12_C_12a_unique {f : ℝ → ℝ} {qbar : ℝ} (hconc : StrictConcaveOn ℝ (Icc 0 qbar) f)
    {y y' : ℝ} (hy : y ∈ Icc 0 qbar) (hy' : y' ∈ Icc 0 qbar) (hmax : ∀ u ∈ Icc 0 qbar, f u ≤ f y)
    (hmax' : ∀ u ∈ Icc 0 qbar, f u ≤ f y') : y = y' := by
  by_contra hne
  have h := hconc.2 hy hy' hne (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num)
  have hmid : (1 / 2 : ℝ) • y + (1 / 2 : ℝ) • y' ∈ Icc 0 qbar :=
    (convex_Icc 0 qbar) hy hy' (by norm_num) (by norm_num) (by norm_num)
  have h1 := hmax _ hmid
  have h2 := hmax y' hy'
  have h3 := hmax' y hy
  simp only [smul_eq_mul] at h h1
  linarith

/-- The cross partial of the Cournot profit is negative when `p' < 0` and marginal revenue
falls with output: `p'(Q) + p''(Q)y < 0` for `0 ≤ y ≤ Q`. -/
theorem exercise_12_C_12b_normal {p' p'' : ℝ → ℝ} (hneg : ∀ Q, 0 ≤ Q → p' Q < 0)
    (hmr : ∀ Q, 0 ≤ Q → p' Q + p'' Q * Q < 0) {Q y : ℝ} (hy : 0 ≤ y) (hyQ : y ≤ Q) :
    p' Q + p'' Q * y < 0 := by
  rcases le_total 0 (p'' Q) with h | h
  · nlinarith [hmr Q (hy.trans hyQ)]
  · nlinarith [hneg Q (hy.trans hyQ)]

/-- **Exercise 12.C.12(b)** (MWG, p. 432). In the Cournot model, firm `j`'s profit
`p(qⱼ + qₖ)qⱼ − c(qⱼ)` has cross partial `p'(Q) + p''(Q)qⱼ`. If this is negative on `[0, q̄]²`
(e.g. under `exercise_12_C_12b_normal`), any best-response function on `[0, q̄]` is
nonincreasing, and strictly decreasing from an interior point. -/
theorem exercise_12_C_12b {p p' p'' c c' : ℝ → ℝ} {qbar : ℝ} (hp : ∀ Q, HasDerivAt p (p' Q) Q)
    (hp' : ∀ Q, HasDerivAt p' (p'' Q) Q) (hc : ∀ y, HasDerivAt c (c' y) y)
    (hcross : ∀ y ∈ Icc 0 qbar, ∀ r ∈ Icc 0 qbar, p' (y + r) + p'' (y + r) * y < 0)
    {b : ℝ → ℝ} (hb : ∀ r ∈ Icc 0 qbar, b r ∈ Icc 0 qbar ∧
      ∀ u ∈ Icc 0 qbar, p (u + r) * u - c u ≤ p (b r + r) * b r - c (b r)) :
    AntitoneOn b (Icc 0 qbar) ∧
      ∀ r ∈ Icc 0 qbar, ∀ r' ∈ Icc 0 qbar, r < r' → b r ∈ Ioo 0 qbar → b r' < b r := by
  have hπ : ∀ r ∈ Icc (0 : ℝ) qbar, ∀ y ∈ Icc (0 : ℝ) qbar,
      HasDerivWithinAt (fun u => p (u + r) * u - c u) (p' (y + r) * y + p (y + r) - c' y)
        (Icc 0 qbar) y := by
    intro r _ y _
    have h1 : HasDerivAt (fun u => p (u + r)) (p' (y + r)) y := (hp (y + r)).comp_add_const y r
    have := (h1.mul (hasDerivAt_id y)).sub (hc y)
    refine (this.congr_deriv ?_).hasDerivWithinAt
    simp only [id]; ring
  have hD : ∀ y ∈ Icc (0 : ℝ) qbar, ∀ r ∈ Icc (0 : ℝ) qbar,
      HasDerivWithinAt (fun r => p' (y + r) * y + p (y + r) - c' y)
        (p'' (y + r) * y + p' (y + r)) (Icc 0 qbar) r := by
    intro y _ r _
    have h1 : HasDerivAt (fun r => p' (y + r)) (p'' (y + r)) r := (hp' (y + r)).comp_const_add y r
    have h2 : HasDerivAt (fun r => p (y + r)) (p' (y + r)) r := (hp (y + r)).comp_const_add y r
    exact (((h1.mul_const y).add h2).sub_const (c' y)).hasDerivWithinAt
  exact (exercise_12_C_12a (π := fun u r => p (u + r) * u - c u)
    (D := fun y r => p' (y + r) * y + p (y + r) - c' y)
    (D₂ := fun y r => p'' (y + r) * y + p' (y + r)) hπ hD hb).2
    (fun y hy r hr => by have := hcross y hy r hr; linarith)

/-- **Exercise 12.C.12(b), instance** (MWG, p. 432). With linear demand `p(Q) = 1 − Q` and
`c = 0`, the cross partial is `−1 < 0`, so the hypotheses of `exercise_12_C_12b` hold on any
`[0, q̄]`. -/
theorem exercise_12_C_12b_instance (qbar : ℝ) :
    (∀ Q : ℝ, HasDerivAt (fun Q => 1 - Q) (-1) Q) ∧ (∀ Q : ℝ, HasDerivAt (fun _ => (-1 : ℝ)) 0 Q) ∧
    ∀ y ∈ Icc (0 : ℝ) qbar, ∀ r ∈ Icc (0 : ℝ) qbar,
      (fun _ => (-1 : ℝ)) (y + r) + (fun _ => (0 : ℝ)) (y + r) * y < 0 := by
  refine ⟨fun Q => by simpa using (hasDerivAt_id Q).const_sub 1, fun Q => hasDerivAt_const Q _,
    fun y _ r _ => by norm_num⟩

/-! ### Exercise 12.C.18: the Stackelberg model -/

/-- The follower's marginal profit `p(r + y) + yp'(r + y) − c`. -/
theorem sb_hasDerivAt {p p' : ℝ → ℝ} (hp : ∀ Q, HasDerivAt p (p' Q) Q) (c r y : ℝ) :
    HasDerivAt (fun u => cbrProfit p (fun y => c * y) r u) (p (r + y) + y * p' (r + y) - c) y := by
  have h1 : HasDerivAt (fun u => p (r + u)) (p' (r + y)) y := (hp (r + y)).comp_const_add r y
  have h2 : HasDerivAt (fun u => p (r + u) * u - c * u)
      (p' (r + y) * y + p (r + y) * 1 - c * 1) y :=
    (h1.mul (hasDerivAt_id' y)).sub ((hasDerivAt_id' y).const_mul c)
  unfold cbrProfit
  exact h2.congr_deriv (by ring)

/-- The marginal profit is strictly decreasing in own output. -/
theorem sb_anti_own {p p' p'' : ℝ → ℝ} (hp : ∀ Q, HasDerivAt p (p' Q) Q)
    (hp' : ∀ Q, HasDerivAt p' (p'' Q) Q) (hneg : ∀ Q, 0 ≤ Q → p' Q < 0)
    (hmr : ∀ Q, 0 ≤ Q → p' Q + p'' Q * Q < 0) (c : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    StrictAntiOn (fun u => p (r + u) + u * p' (r + u) - c) (Ici 0) := by
  have hd : ∀ u, HasDerivAt (fun u => p (r + u) + u * p' (r + u) - c)
      (p' (r + u) + (1 * p' (r + u) + u * p'' (r + u))) u := by
    intro u
    have h1 : HasDerivAt (fun u => p (r + u)) (p' (r + u)) u := (hp (r + u)).comp_const_add r u
    have h2 : HasDerivAt (fun u => p' (r + u)) (p'' (r + u)) u := (hp' (r + u)).comp_const_add r u
    exact (h1.add ((hasDerivAt_id u).mul h2)).sub_const c
  refine strictAntiOn_of_hasDerivWithinAt_neg (convex_Ici 0)
    (fun u _ => (hd u).continuousAt.continuousWithinAt) (fun u _ => (hd u).hasDerivWithinAt)
    fun u hu => ?_
  rw [interior_Ici] at hu
  have hu' : (0 : ℝ) < u := hu
  have h1 := hneg (r + u) (by linarith)
  have h2 := exercise_12_C_12b_normal hneg hmr hu'.le (show u ≤ r + u by linarith)
  linarith

/-- The marginal profit is strictly decreasing in the rival's output. -/
theorem sb_anti_rival {p p' p'' : ℝ → ℝ} (hp : ∀ Q, HasDerivAt p (p' Q) Q)
    (hp' : ∀ Q, HasDerivAt p' (p'' Q) Q) (hneg : ∀ Q, 0 ≤ Q → p' Q < 0)
    (hmr : ∀ Q, 0 ≤ Q → p' Q + p'' Q * Q < 0) (c : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    StrictAntiOn (fun r => p (r + u) + u * p' (r + u) - c) (Ici 0) := by
  have hd : ∀ r, HasDerivAt (fun r => p (r + u) + u * p' (r + u) - c)
      (p' (r + u) + u * p'' (r + u)) r := by
    intro r
    have h1 : HasDerivAt (fun r => p (r + u)) (p' (r + u)) r := (hp (r + u)).comp_add_const r u
    have h2 : HasDerivAt (fun r => p' (r + u)) (p'' (r + u)) r := (hp' (r + u)).comp_add_const r u
    exact (h1.add (h2.const_mul u)).sub_const c
  refine strictAntiOn_of_hasDerivWithinAt_neg (convex_Ici 0)
    (fun r _ => (hd r).continuousAt.continuousWithinAt) (fun r _ => (hd r).hasDerivWithinAt)
    fun r hr => ?_
  rw [interior_Ici] at hr
  have hr' : (0 : ℝ) < r := hr
  have := exercise_12_C_12b_normal hneg hmr hu (show u ≤ r + u by linarith)
  linarith

/-- The follower's best response to `r ≥ 0` is unique. -/
theorem sb_br_unique {p p' p'' : ℝ → ℝ} (hp : ∀ Q, HasDerivAt p (p' Q) Q)
    (hp' : ∀ Q, HasDerivAt p' (p'' Q) Q) (hneg : ∀ Q, 0 ≤ Q → p' Q < 0)
    (hmr : ∀ Q, 0 ≤ Q → p' Q + p'' Q * Q < 0) {c r y₁ y₂ : ℝ} (hr : 0 ≤ r)
    (h1 : IsBROn p (fun y => c * y) (Ici 0) r y₁) (h2 : IsBROn p (fun y => c * y) (Ici 0) r y₂) :
    y₁ = y₂ := by
  have hC : ∀ y, HasDerivAt (fun y => c * y) ((fun _ => c) y) y := fun y => by
    simpa using (hasDerivAt_id y).const_mul c
  obtain ⟨f1, f1'⟩ := cbr_foc hp hC h1
  obtain ⟨f2, f2'⟩ := cbr_foc hp hC h2
  have hanti := sb_anti_own hp hp' hneg hmr c hr
  have hy1 : (0 : ℝ) ≤ y₁ := h1.1
  have hy2 : (0 : ℝ) ≤ y₂ := h2.1
  rcases lt_trichotomy y₁ y₂ with h | h | h
  · have := hanti (mem_Ici.2 hy1) (mem_Ici.2 hy2) h
    have := f2' (by linarith)
    simp only at *
    linarith
  · exact h
  · have := hanti (mem_Ici.2 hy2) (mem_Ici.2 hy1) h
    have := f1' (by linarith)
    simp only at *
    linarith

/-- The first-order condition is sufficient for the follower's best response. -/
theorem sb_br_of_foc {p p' p'' : ℝ → ℝ} (hp : ∀ Q, HasDerivAt p (p' Q) Q)
    (hp' : ∀ Q, HasDerivAt p' (p'' Q) Q) (hneg : ∀ Q, 0 ≤ Q → p' Q < 0)
    (hmr : ∀ Q, 0 ≤ Q → p' Q + p'' Q * Q < 0) {c r y : ℝ} (hr : 0 ≤ r) (hy : 0 ≤ y)
    (hfoc : p (r + y) + y * p' (r + y) - c = 0) : IsBROn p (fun y => c * y) (Ici 0) r y := by
  have hanti := sb_anti_own hp hp' hneg hmr c hr
  have hd := sb_hasDerivAt hp c r
  refine ⟨mem_Ici.2 hy, fun u hu => ?_⟩
  have hu' : (0 : ℝ) ≤ u := hu
  rcases lt_trichotomy u y with h | h | h
  · have hmono : StrictMonoOn (fun u => cbrProfit p (fun y => c * y) r u) (Icc 0 y) := by
      refine strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc 0 y)
        (fun x _ => (hd x).continuousAt.continuousWithinAt) (fun x _ => (hd x).hasDerivWithinAt)
        fun x hx => ?_
      rw [interior_Icc] at hx
      have := hanti (mem_Ici.2 hx.1.le) (mem_Ici.2 hy) hx.2
      simp only at this
      linarith
    exact (hmono ⟨hu', h.le⟩ ⟨hy, le_rfl⟩ h).le
  · rw [h]
  · have hanti' : StrictAntiOn (fun u => cbrProfit p (fun y => c * y) r u) (Ici y) := by
      refine strictAntiOn_of_hasDerivWithinAt_neg (convex_Ici y)
        (fun x _ => (hd x).continuousAt.continuousWithinAt) (fun x _ => (hd x).hasDerivWithinAt)
        fun x hx => ?_
      rw [interior_Ici] at hx
      have hx' : y < x := hx
      have := hanti (mem_Ici.2 hy) (mem_Ici.2 (by linarith)) hx'
      simp only at this
      linarith
    exact (hanti' (mem_Ici.2 le_rfl) (mem_Ici.2 h.le) h).le

/-- The follower's best response is nonincreasing in the leader's output. -/
theorem sb_br_anti {p p' p'' : ℝ → ℝ} (hp : ∀ Q, HasDerivAt p (p' Q) Q)
    (hp' : ∀ Q, HasDerivAt p' (p'' Q) Q) (hneg : ∀ Q, 0 ≤ Q → p' Q < 0)
    (hmr : ∀ Q, 0 ≤ Q → p' Q + p'' Q * Q < 0) {c r r' y y' : ℝ} (hr : 0 ≤ r) (hrr : r < r')
    (hy : IsBROn p (fun y => c * y) (Ici 0) r y) (hy' : IsBROn p (fun y => c * y) (Ici 0) r' y') :
    y' ≤ y := by
  have hID := sc_strictMonoOn_diff (π := fun u s => cbrProfit p (fun y => c * y) s u)
    (D := fun u s => p (s + u) + u * p' (s + u) - c) (r := r') (r' := r) (convex_Ici 0)
    (fun u _ => (sb_hasDerivAt hp c r' u).hasDerivWithinAt)
    (fun u _ => (sb_hasDerivAt hp c r u).hasDerivWithinAt) (fun u hu => by
      rw [interior_Ici] at hu
      exact sb_anti_rival hp hp' hneg hmr c (le_of_lt hu) (mem_Ici.2 hr)
        (mem_Ici.2 (by linarith)) hrr)
  exact sc_topkis (π := fun u s => cbrProfit p (fun y => c * y) s u) hID hy'.1 hy.1
    (fun u hu => hy'.2 u hu) (fun u hu => hy.2 u hu)

/-- **Exercise 12.C.18(a)** (MWG, p. 433), the Stackelberg leadership model. Inverse demand
`p` is twice differentiable with `p'(q) < 0` and `p'(q) + p''(q)q < 0` for `q ≥ 0`; both firms
have unit cost `c < p(0)`. Let `(q₁ᶜ, q₂ᶜ)` be a Cournot equilibrium, `b` the follower's
best-response function and `q₁ˢ` an optimal output of the leader, who anticipates `b`. Then
`q₁ˢ > q₁ᶜ`, the leader's profit is strictly larger than in the Cournot equilibrium, aggregate
output `q₁ˢ + b(q₁ˢ)` is strictly larger, and the follower's profit is strictly smaller. -/
theorem exercise_12_C_18a {p p' p'' : ℝ → ℝ} {c : ℝ} (hp : ∀ Q, HasDerivAt p (p' Q) Q)
    (hp' : ∀ Q, HasDerivAt p' (p'' Q) Q) (hneg : ∀ Q, 0 ≤ Q → p' Q < 0)
    (hmr : ∀ Q, 0 ≤ Q → p' Q + p'' Q * Q < 0) (hc0 : c < p 0) {q1c q2c : ℝ}
    (hc1 : IsBROn p (fun y => c * y) (Ici 0) q2c q1c)
    (hc2 : IsBROn p (fun y => c * y) (Ici 0) q1c q2c) {b : ℝ → ℝ}
    (hb : ∀ r, 0 ≤ r → IsBROn p (fun y => c * y) (Ici 0) r (b r)) {q1s : ℝ} (hq1s : 0 ≤ q1s)
    (hlead : ∀ r, 0 ≤ r → cbrProfit p (fun y => c * y) (b r) r ≤
      cbrProfit p (fun y => c * y) (b q1s) q1s) :
    q1c < q1s ∧
    cbrProfit p (fun y => c * y) q2c q1c < cbrProfit p (fun y => c * y) (b q1s) q1s ∧
    q1c + q2c < q1s + b q1s ∧
    cbrProfit p (fun y => c * y) q1s (b q1s) < cbrProfit p (fun y => c * y) q1c q2c := by
  have hC : ∀ y, HasDerivAt (fun y => c * y) ((fun _ => c) y) y := fun y => by
    simpa using (hasDerivAt_id y).const_mul c
  have hanti : StrictAntiOn p (Ici 0) := strictAntiOn_of_deriv_neg'
    (fun z _ => (hp z).hasDerivWithinAt) hneg
  have h1 : (0 : ℝ) ≤ q1c := hc1.1
  have h2 : (0 : ℝ) ≤ q2c := hc2.1
  obtain ⟨f1, f1'⟩ := cbr_foc hp hC hc1
  obtain ⟨f2, f2'⟩ := cbr_foc hp hC hc2
  rw [add_comm q2c q1c] at f1 f1'
  -- both Cournot firms produce
  have hpos : ∀ y z, 0 ≤ y → 0 ≤ z → p (y + z) + y * p' (y + z) ≤ c →
      (0 < z → p (y + z) + z * p' (y + z) = c) → 0 < y := by
    intro y z hy hz fy fz
    by_contra hy0
    have hy0' : y = 0 := le_antisymm (not_lt.1 hy0) hy
    subst hy0'
    simp only [zero_add, zero_mul, add_zero] at fy fz
    rcases eq_or_lt_of_le hz with hz0 | hz0
    · subst hz0; linarith
    · have := fz hz0
      have := mul_neg_of_pos_of_neg hz0 (hneg z hz)
      linarith
  have hq1 : 0 < q1c := hpos q1c q2c h1 h2 f1 f2'
  have hq2 : 0 < q2c := hpos q2c q1c h2 h1 (by rw [add_comm q2c q1c]; exact f2)
    (fun h => by rw [add_comm q2c q1c]; exact f1' h)
  set Qc := q1c + q2c with hQcdef
  have hQc : 0 < Qc := by linarith
  have hd1 : p' Qc < 0 := hneg Qc hQc.le
  have e1 := f1' hq1
  have e2 := f2' hq2
  have hsym : q1c = q2c := by
    have : p' Qc * (q1c - q2c) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · linarith
  have hbc : b q1c = q2c := sb_br_unique hp hp' hneg hmr h1 (hb q1c h1) hc2
  have hstrict1 : ∀ r, 0 ≤ r → r ≠ q1c →
      cbrProfit p (fun y => c * y) q2c r < cbrProfit p (fun y => c * y) q2c q1c := by
    intro r hr hne
    by_contra hle
    push Not at hle
    have hbr : IsBROn p (fun y => c * y) (Ici 0) q2c r := ⟨mem_Ici.2 hr, fun u hu =>
      (hc1.2 u hu).trans hle⟩
    exact hne (sb_br_unique hp hp' hneg hmr h2 hbr hc1)
  -- the leader never produces less than its Cournot output
  have hge : q1c ≤ q1s := by
    by_contra hlt
    push Not at hlt
    have hbs : q2c ≤ b q1s := by
      rw [← hbc]; exact sb_br_anti hp hp' hneg hmr hq1s hlt (hb q1s hq1s) (hb q1c h1)
    have hbs0 : (0 : ℝ) ≤ b q1s := (hb q1s hq1s).1
    have hL1 : cbrProfit p (fun y => c * y) (b q1s) q1s ≤ cbrProfit p (fun y => c * y) q2c q1s := by
      unfold cbrProfit
      have : p (b q1s + q1s) ≤ p (q2c + q1s) :=
        hanti.antitoneOn (mem_Ici.2 (by linarith)) (mem_Ici.2 (by linarith)) (by linarith)
      nlinarith [mul_le_mul_of_nonneg_right this hq1s]
    have h3 := hstrict1 q1s hq1s (ne_of_lt hlt)
    have h4 := hlead q1c h1
    rw [hbc] at h4
    linarith
  -- the leader can strictly improve on its Cournot profit
  have himp : ∃ r, 0 ≤ r ∧
      cbrProfit p (fun y => c * y) q2c q1c < cbrProfit p (fun y => c * y) (b r) r := by
    set y : ℝ → ℝ := fun Q => (p Q - c) / (-p' Q) with hy
    set rr : ℝ → ℝ := fun Q => Q - y Q with hrr
    set Lf : ℝ → ℝ := fun Q => (p Q - c) * rr Q with hLf
    have hne : -p' Qc ≠ 0 := by linarith
    have hne1 : p' Qc ≠ 0 := hd1.ne
    have hyd : HasDerivAt y ((p' Qc * -p' Qc - (p Qc - c) * -p'' Qc) / (-p' Qc) ^ 2) Qc :=
      ((hp Qc).sub_const c).div (hp' Qc).neg hne
    have hrd : HasDerivAt rr (1 - (p' Qc * -p' Qc - (p Qc - c) * -p'' Qc) / (-p' Qc) ^ 2) Qc :=
      (hasDerivAt_id Qc).sub hyd
    have hLd := ((hp Qc).sub_const c).mul hrd
    have hpc : p Qc - c = -p' Qc * q2c := by linarith
    have hyc : y Qc = q2c := by
      simp only [hy]; rw [hpc]; field_simp
    have hrc : rr Qc = q1c := by
      simp only [hrr]; rw [hyc, hQcdef]; ring
    have hnorm := exercise_12_C_12b_normal hneg hmr h2 (show q2c ≤ Qc by linarith)
    have hdpos : 0 < p' Qc * rr Qc + (p Qc - c) *
        (1 - (p' Qc * -p' Qc - (p Qc - c) * -p'' Qc) / (-p' Qc) ^ 2) := by
      rw [hrc, hpc, hsym]
      have key : p' Qc * q2c + -p' Qc * q2c *
          (1 - (p' Qc * -p' Qc - -p' Qc * q2c * -p'' Qc) / (-p' Qc) ^ 2) =
          -q2c * (p' Qc + p'' Qc * q2c) := by
        field_simp
        ring
      rw [key]
      nlinarith
    have hT := hLd.tendsto_slope_zero_right
    have hev1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t⁻¹ • (Lf (Qc + t) - Lf Qc) :=
      (tendsto_order.1 hT).1 0 hdpos
    have hshift : Tendsto (fun t : ℝ => Qc + t) (𝓝 0) (𝓝 Qc) := by
      have := (tendsto_const_nhds (x := Qc)).add (tendsto_id (x := 𝓝 (0 : ℝ)))
      simpa using this
    have hev2 : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < y (Qc + t) ∧ 0 < rr (Qc + t) ∧ 0 < Qc + t :=
      ((hyd.continuousAt.tendsto.comp hshift).eventually (lt_mem_nhds (by rw [hyc]; exact hq2))).and
        (((hrd.continuousAt.tendsto.comp hshift).eventually
          (lt_mem_nhds (by rw [hrc]; exact hq1))).and
          (hshift.eventually (lt_mem_nhds hQc)))
    have hev3 : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
    obtain ⟨t, ht1, ⟨hyt, hrt, hQt⟩, ht⟩ :=
      (hev1.and ((hev2.filter_mono nhdsWithin_le_nhds).and hev3)).exists
    have hsum : rr (Qc + t) + y (Qc + t) = Qc + t := by simp only [hrr]; ring
    have hfoc : p (rr (Qc + t) + y (Qc + t)) + y (Qc + t) * p' (rr (Qc + t) + y (Qc + t)) - c
        = 0 := by
      rw [hsum]
      have hne' : p' (Qc + t) ≠ 0 := (hneg _ hQt.le).ne
      simp only [hy]
      field_simp
      ring
    have hbr := sb_br_of_foc hp hp' hneg hmr hrt.le hyt.le hfoc
    have hbQ : b (rr (Qc + t)) = y (Qc + t) :=
      sb_br_unique hp hp' hneg hmr hrt.le (hb _ hrt.le) hbr
    refine ⟨rr (Qc + t), hrt.le, ?_⟩
    have hLQ : cbrProfit p (fun y => c * y) (b (rr (Qc + t))) (rr (Qc + t)) = Lf (Qc + t) := by
      rw [hbQ]
      unfold cbrProfit
      simp only [hLf]
      rw [add_comm (y (Qc + t)), hsum]
      ring
    have hLc : cbrProfit p (fun y => c * y) q2c q1c = Lf Qc := by
      unfold cbrProfit
      simp only [hLf]
      rw [hrc, add_comm q2c q1c]
      ring
    rw [hLQ, hLc]
    rw [smul_eq_mul] at ht1
    by_contra hle
    push Not at hle
    have := mul_nonpos_of_nonneg_of_nonpos (inv_pos.2 ht).le (sub_nonpos.2 hle)
    linarith
  obtain ⟨r, hr, hrL⟩ := himp
  have hprofit : cbrProfit p (fun y => c * y) q2c q1c < cbrProfit p (fun y => c * y) (b q1s) q1s :=
    lt_of_lt_of_le hrL (hlead r hr)
  have hlt : q1c < q1s := lt_of_le_of_ne hge fun h => by
    rw [← h, hbc] at hprofit; exact lt_irrefl _ hprofit
  have hbs0 : (0 : ℝ) ≤ b q1s := (hb q1s hq1s).1
  -- aggregate output rises
  have hagg : q1c + q2c < q1s + b q1s := by
    have hconv : ConvexOn ℝ (Ici 0) (fun y : ℝ => c * y) := by
      refine ⟨convex_Ici 0, fun x _ y _ a b _ _ _ => le_of_eq ?_⟩
      simp only [smul_eq_mul]
      ring
    have hw := exercise_12_C_8c (P := p) (c := fun y => c * y) (S := Ici 0) hanti hconv
      ordConnected_Ici (subset_refl _) h1 hlt hc2 (hb q1s hq1s)
    rcases eq_or_lt_of_le hw with heq | hlt'
    · exfalso
      obtain ⟨g, g'⟩ := cbr_foc hp hC (hb q1s hq1s)
      have hQ : q1s + b q1s = Qc := by rw [hQcdef]; linarith
      rw [hQ] at g g'
      rcases eq_or_lt_of_le hbs0 with h0 | h0
      · rw [← h0] at g
        simp only [zero_mul, add_zero] at g
        nlinarith [mul_neg_of_pos_of_neg hq2 hd1]
      · have := g' h0
        have hbs : b q1s < q2c := by linarith
        have : p' Qc * (b q1s - q2c) = 0 := by linarith
        rcases mul_eq_zero.1 this with h | h <;> linarith
    · linarith
  refine ⟨hlt, hprofit, hagg, ?_⟩
  -- the follower's profit falls
  rcases eq_or_lt_of_le hbs0 with h0 | h0
  · rw [← h0]
    unfold cbrProfit
    simp only [mul_zero, sub_zero]
    have hpc : p Qc - c = -p' Qc * q2c := by linarith
    nlinarith [mul_pos (neg_pos.2 hd1) (mul_pos hq2 hq2)]
  · have hlt2 : p (q1s + b q1s) < p (q1c + b q1s) :=
      hanti (mem_Ici.2 (by linarith)) (mem_Ici.2 (by linarith)) (by linarith)
    have h3 := hc2.2 (b q1s) (mem_Ici.2 hbs0)
    unfold cbrProfit at h3 ⊢
    nlinarith [mul_lt_mul_of_pos_right hlt2 h0]

/-- **Exercise 12.C.18(a), instance** (MWG, p. 433). With `p(q) = 1 − q` (`p' = −1`,
`p'' = 0`) and `c = 0`: the Cournot outputs are `1/3`, the follower's best response is
`b(r) = max{0, (1 − r)/2}`, and the leader's optimum is `1/2`; the leader produces more
(`1/2 > 1/3`) and earns more (`1/8 > 1/9`), total output rises to `3/4 > 2/3`, and the follower
earns less (`1/16 < 1/9`). -/
theorem exercise_12_C_18a_instance :
    (1 : ℝ) / 3 < 1 / 2 ∧
    cbrProfit (fun Q => 1 - Q) (fun y => 0 * y) (1 / 3) (1 / 3) <
      cbrProfit (fun Q => 1 - Q) (fun y => 0 * y) (max 0 ((1 - 1 / 2) / 2)) (1 / 2) ∧
    (1 : ℝ) / 3 + 1 / 3 < 1 / 2 + max 0 ((1 - 1 / 2) / 2) ∧
    cbrProfit (fun Q => 1 - Q) (fun y => 0 * y) (1 / 2) (max 0 ((1 - 1 / 2) / 2)) <
      cbrProfit (fun Q => 1 - Q) (fun y => 0 * y) (1 / 3) (1 / 3) := by
  have hp : ∀ Q : ℝ, HasDerivAt (fun Q => 1 - Q) ((fun _ => (-1 : ℝ)) Q) Q := fun Q => by
    simpa using (hasDerivAt_id Q).const_sub 1
  have hp' : ∀ Q : ℝ, HasDerivAt (fun _ : ℝ => (-1 : ℝ)) ((fun _ => (0 : ℝ)) Q) Q :=
    fun Q => hasDerivAt_const Q _
  have hbr : ∀ r : ℝ, 0 ≤ r → IsBROn (fun Q => 1 - Q) (fun y => 0 * y) (Ici 0) r
      (max 0 ((1 - r) / 2)) := by
    intro r hr
    obtain ⟨h0, huniq⟩ := example_12_C_1_br (a := 1) (b := 1) (c := 0) (qk := r) one_pos hr
    have e : max 0 ((1 - 0 - 1 * r) / (2 * 1)) = max 0 ((1 - r) / 2) := by ring_nf
    rw [e] at h0 huniq
    refine ⟨mem_Ici.2 h0, fun u hu => ?_⟩
    by_cases hu' : u = max 0 ((1 - r) / 2)
    · rw [hu']
    · have := huniq u hu hu'
      unfold cbrProfit
      nlinarith
  have hlead : ∀ r : ℝ, 0 ≤ r →
      cbrProfit (fun Q => 1 - Q) (fun y => 0 * y) (max 0 ((1 - r) / 2)) r ≤
      cbrProfit (fun Q => 1 - Q) (fun y => 0 * y) (max 0 ((1 - 1 / 2) / 2)) (1 / 2) := by
    intro r hr
    unfold cbrProfit
    rw [max_eq_right (by norm_num : (0 : ℝ) ≤ (1 - 1 / 2) / 2)]
    rcases le_total ((1 - r) / 2) 0 with h | h
    · rw [max_eq_left h]; nlinarith
    · rw [max_eq_right h]; nlinarith [sq_nonneg (r - 1 / 2)]
  have hc1 : IsBROn (fun Q => 1 - Q) (fun y => 0 * y) (Ici 0) (1 / 3) (1 / 3) := by
    have := hbr (1 / 3) (by norm_num)
    rwa [show max 0 ((1 - (1 : ℝ) / 3) / 2) = 1 / 3 by norm_num] at this
  have h := exercise_12_C_18a (p := fun Q => 1 - Q) (p' := fun _ => -1) (p'' := fun _ => 0)
    (c := 0) hp hp' (fun _ _ => by norm_num) (fun _ _ => by norm_num) (by norm_num) hc1 hc1
    (b := fun r => max 0 ((1 - r) / 2)) hbr (q1s := 1 / 2) (by norm_num) hlead
  exact h

end MWG.MarketPower
