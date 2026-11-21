/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGMarketPower.CournotBestResponse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# The competitive limit

MWG, Section 12.F, pp. 411-413 (Proposition 12.F.1, its small-type argument and footnote 29),
and Exercise 12.F.1, p. 435.

Market demand is `αx(p)`; with `p(·)` the inverse of `x(·)` the inverse demand at market size
`α` is `p_α(Q) = p(Q/α)` (`sizedDemand`). Potential firms are indexed by `ℕ` (infinitely many);
each has cost `c` and entry cost `K`. `c̄ = min_{q>0} (K + c(q))/q` is minimum average cost,
reached at the efficient scale `q̄ > 0`, and `X = x(c̄) > 0` (so `p(X) = c̄`).

**The SPNE.** In the two-stage Cournot entry game a pure strategy profile consists of stage-1
entry decisions, which we record as the finite set `E` of entrants, and stage-2 output rules: for
every set `F` of entrants (every stage-1 history), the output profile `σ F`. Subgame perfection
requires (i) `σ F` to be a Cournot equilibrium among the firms of `F`, for every `F` (every
stage-2 subgame), and (ii) no firm to gain by changing its stage-1 decision given the continuation
`σ`: an entrant earns at least `0` net of `K`, and an outsider `j` who entered would earn at most
`0` in the continuation equilibrium `σ (insert j E)` that the profile specifies. (A firm changing
both decisions gains nothing more, since `σ F` is an equilibrium of each subgame.) This is
`IsCournotEntrySPNE`. Only the subgames after `E` and after single-firm entry deviations are
used in the proof.

* `entry_incumbents_no_expand`: the small-type paragraph of p. 413. If best responses are unique
  and weakly decreasing, the incumbents' aggregate output cannot rise when a firm enters (via
  `exercise_12_C_8c`).
* `entry_step_ii`: step (ii) of the proof, in the form: if an entrant producing `q₀` at average
  output `s₀ = Q/α` would earn more than `K`, then `Q_α + q₀ ≥ αs₀`.
* `competitive_limit`: every SPNE price tends to `c̄` when `c̄` is only an infimum of average
  cost; `proposition_12_F_1` (minimum attained at `q̄`) and `footnote_12_29` (constant marginal
  cost `c`, `c̄ = c` the limit of average cost) are corollaries.
* Exercise 12.F.1 as printed is false: `exercise_12_F_1_counterexample`,
  `exercise_12_F_1_false` (inverse demand `1 + e^{−(s+1)²}`, cost `q²`: for every `α ≥ 4` best
  responses are unique but increase between `Q₋ⱼ = 2α²` and `2α² + 1`). Corrected:
  `exercise_12_F_1_core`, `exercise_12_F_1` (`p'' ≤ L(−p')`, best responses bounded by `B`,
  `α > LB`).
* `entry_spne_instance`: an explicit SPNE (linear demand, zero cost), so the SPNE hypotheses of
  the lemmas above are satisfiable.
* `proposition_12_F_1_of_exercise_12_F_1`: Proposition 12.F.1 with the decreasing best response
  derived from the Exercise 12.F.1 condition; `proposition_12_F_1_instance` (linear demand,
  quadratic cost) and `footnote_12_29_instance` verify every hypothesis.

Departures: the inverse demand `p` is primitive (continuous at `X`, strictly decreasing on
`[0, ∞)`); the proof uses convexity of `c` only (MWG assume strict convexity); the book's standing
assumption that the best response is unique is part of `BRDecreasing`.
-/

namespace MWG.MarketPower

open Set Filter Topology

/-- Inverse demand at market size `α`: `p_α(Q) = p(Q/α)` (MWG, p. 412). -/
noncomputable def sizedDemand (p : ℝ → ℝ) (α : ℝ) : ℝ → ℝ := fun Q => p (Q / α)

/-- `p_α` inherits strict decrease on `[0, ∞)` from `p` when `α > 0`. -/
theorem sizedDemand_strictAntiOn {p : ℝ → ℝ} (hp : StrictAntiOn p (Ici 0)) {α : ℝ}
    (hα : 0 < α) : StrictAntiOn (sizedDemand p α) (Ici 0) := fun _ hx _ hy h =>
  hp (mem_Ici.2 (div_nonneg hx hα.le)) (mem_Ici.2 (div_nonneg hy hα.le))
    (div_lt_div_of_pos_right h hα)

/-- Net profit of firm `j` among the entrants `E` at the output profile `q`, market size `α`:
`p_α(∑_{k∈E} q_k)qⱼ − c(qⱼ) − K`. -/
noncomputable def entryNetProfit (p c : ℝ → ℝ) (K α : ℝ) (E : Finset ℕ) (q : ℕ → ℝ) (j : ℕ) : ℝ :=
  p ((∑ k ∈ E, q k) / α) * q j - c (q j) - K

/-- A pure-strategy subgame perfect Nash equilibrium of the two-stage Cournot entry model with
market size `α` (MWG, p. 412): entrants `E`, stage-2 output rules `σ` (see the module docstring).
-/
def IsCournotEntrySPNE (p c : ℝ → ℝ) (K α : ℝ) (E : Finset ℕ) (σ : Finset ℕ → ℕ → ℝ) : Prop :=
  (∀ F : Finset ℕ, IsCournotEqm (sizedDemand p α) c (Ici 0) F (σ F)) ∧
  (∀ j ∈ E, 0 ≤ entryNetProfit p c K α E (σ E) j) ∧
  ∀ j ∉ E, entryNetProfit p c K α (insert j E) (σ (insert j E)) j ≤ 0

/-- The best response `b(Q₋ⱼ)` is unique and weakly decreasing on `Q₋ⱼ ≥ 0` (MWG, p. 412 and
step (i) of the proof of Proposition 12.F.1). -/
def BRDecreasing (P c : ℝ → ℝ) : Prop :=
  (∀ R, 0 ≤ R → ∀ y y', IsBROn P c (Ici 0) R y → IsBROn P c (Ici 0) R y' → y = y') ∧
  ∀ R R', 0 ≤ R → R < R' → ∀ y y', IsBROn P c (Ici 0) R y → IsBROn P c (Ici 0) R' y' → y' ≤ y

/-- **Proposition 12.F.1, small-type argument** (MWG, pp. 412-413). If `P` is strictly decreasing,
`c` convex and the best response unique and decreasing, then when firm `j ∉ E` enters, the
aggregate output of the original entrants cannot increase: `Q̃ ≤ Q`. -/
theorem entry_incumbents_no_expand {P c : ℝ → ℝ} (hP : StrictAntiOn P (Ici 0))
    (hc : ConvexOn ℝ (Ici 0) c) (hdec : BRDecreasing P c) {E : Finset ℕ} {j : ℕ} (hj : j ∉ E)
    {q q' : ℕ → ℝ} (hq : IsCournotEqm P c (Ici 0) E q)
    (hq' : IsCournotEqm P c (Ici 0) (insert j E) q') : ∑ k ∈ E, q' k ≤ ∑ k ∈ E, q k := by
  by_contra hlt
  push Not at hlt
  obtain ⟨k, hk, hkk⟩ := Finset.exists_lt_of_sum_lt hlt
  have hkF : k ∈ insert j E := Finset.mem_insert_of_mem hk
  have hR0 : 0 ≤ ∑ l ∈ E.erase k, q l :=
    Finset.sum_nonneg fun l hl => (hq l (Finset.mem_of_mem_erase hl)).1
  have hR'0 : 0 ≤ ∑ l ∈ (insert j E).erase k, q' l :=
    Finset.sum_nonneg fun l hl => (hq' l (Finset.mem_of_mem_erase hl)).1
  rcases lt_or_ge (∑ l ∈ (insert j E).erase k, q' l) (∑ l ∈ E.erase k, q l) with hlt' | hge
  · have key := exercise_12_C_8c hP hc ordConnected_Ici subset_rfl hR'0 hlt' (hq' k hkF)
      (hq k hk)
    have e1 := Finset.add_sum_erase E q hk
    have e2 := Finset.add_sum_erase _ q' hkF
    rw [Finset.sum_insert hj] at e2
    have hj0 : 0 ≤ q' j := (hq' j (Finset.mem_insert_self j E)).1
    linarith
  · rcases eq_or_lt_of_le hge with heq | hgt
    · have h' := hq' k hkF
      rw [← heq] at h'
      have := hdec.1 _ hR0 (q k) (q' k) (hq k hk) h'
      linarith
    · have := hdec.2 _ _ hR0 hgt (q k) (q' k) (hq k hk) (hq' k hkF)
      linarith

/-- **Proposition 12.F.1, step (ii)** (MWG, p. 412). In any SPNE with market size `α`, if a firm
producing `q₀ > 0` at the average output `s₀` would earn more than its entry cost
(`K + c(q₀) < p(s₀)q₀`), then `Q_α + q₀ ≥ αs₀`. (The book takes `q₀ = q̄`, `s₀ = x(c̄)`.) -/
theorem entry_step_ii {p c : ℝ → ℝ} {K α : ℝ} (hα : 0 < α) (hp : StrictAntiOn p (Ici 0))
    (hc : ConvexOn ℝ (Ici 0) c) (hdec : BRDecreasing (sizedDemand p α) c)
    {E : Finset ℕ} {σ : Finset ℕ → ℕ → ℝ} (hE : IsCournotEntrySPNE p c K α E σ)
    {q₀ s₀ : ℝ} (hq₀ : 0 < q₀) (hprof : K + c q₀ < p s₀ * q₀) :
    α * s₀ ≤ ∑ k ∈ E, σ E k + q₀ := by
  by_contra hlt
  push Not at hlt
  obtain ⟨j, hj⟩ := Infinite.exists_notMem_finset E
  have hNE := hE.1 E
  have hNF := hE.1 (insert j E)
  have hsmall := entry_incumbents_no_expand (sizedDemand_strictAntiOn hp hα) hc hdec hj hNE hNF
  have hQ'0 : 0 ≤ ∑ k ∈ E, σ (insert j E) k :=
    Finset.sum_nonneg fun k hk => (hNF k (Finset.mem_insert_of_mem hk)).1
  have hbr := hNF j (Finset.mem_insert_self j E)
  rw [Finset.erase_insert hj] at hbr
  have hdev := hbr.2 q₀ (mem_Ici.2 hq₀.le)
  have hout := hE.2.2 j hj
  unfold entryNetProfit at hout
  rw [Finset.sum_insert hj] at hout
  unfold cbrProfit sizedDemand at hdev
  have hlt2 : (∑ k ∈ E, σ (insert j E) k + q₀) / α < s₀ := by
    rw [div_lt_iff₀ hα]; linarith
  have hpr1 : p s₀ < p ((∑ k ∈ E, σ (insert j E) k + q₀) / α) :=
    hp (mem_Ici.2 (by positivity)) (mem_Ici.2 (le_trans (by positivity) hlt2.le)) hlt2
  have hpr2 := mul_lt_mul_of_pos_right hpr1 hq₀
  rw [add_comm (σ (insert j E) j)] at hout
  linarith

/-- In any SPNE with positive aggregate output, the price is at least minimum average cost: some
entrant produces `qₖ > 0` and earns `p qₖ ≥ K + c(qₖ) ≥ c̄ qₖ` (MWG, p. 412). -/
theorem entry_price_ge {p c : ℝ → ℝ} {K α cbar : ℝ} {E : Finset ℕ} {σ : Finset ℕ → ℕ → ℝ}
    (hE : IsCournotEntrySPNE p c K α E σ) (hlow : ∀ q, 0 < q → cbar * q ≤ K + c q)
    (hQ : 0 < ∑ k ∈ E, σ E k) : cbar ≤ p ((∑ k ∈ E, σ E k) / α) := by
  obtain ⟨k, hk, hpos⟩ := Finset.exists_lt_of_sum_lt (f := fun _ => (0 : ℝ))
    (by simpa using hQ)
  have h1 := hE.2.1 k hk
  unfold entryNetProfit at h1
  have h2 := hlow _ hpos
  by_contra h
  push Not at h
  nlinarith [mul_lt_mul_of_pos_right h hpos]

/-- **Proposition 12.F.1, general form** (MWG, pp. 412-413, with footnote 29). Let `p` be
strictly decreasing on `[0, ∞)` and continuous at `X > 0` with `p(X) = c̄`, `c` convex, `c̄` the
infimum of average cost (`c̄q ≤ K + c(q)` for `q > 0`, and average cost comes arbitrarily close
to `c̄`), and best responses unique and decreasing for all large `α`. Then for every `ε > 0` there
is `A` such that every SPNE price at every market size `α ≥ A` lies within `ε` of `c̄`, i.e.
`max_{p_α ∈ P_α} |p_α − c̄| → 0`. -/
theorem competitive_limit {p c : ℝ → ℝ} {K cbar X : ℝ} (hp : StrictAntiOn p (Ici 0))
    (hpc : ContinuousAt p X) (hX : 0 < X) (hpX : p X = cbar) (hc : ConvexOn ℝ (Ici 0) c)
    (hlow : ∀ q, 0 < q → cbar * q ≤ K + c q)
    (hinf : ∀ η, 0 < η → ∃ q₀, 0 < q₀ ∧ K + c q₀ < (cbar + η) * q₀)
    (hdec : ∃ A₀, ∀ α, A₀ ≤ α → BRDecreasing (sizedDemand p α) c) :
    ∀ ε, 0 < ε → ∃ A, ∀ α, A ≤ α → ∀ (E : Finset ℕ) (σ : Finset ℕ → ℕ → ℝ),
      IsCournotEntrySPNE p c K α E σ → |p ((∑ k ∈ E, σ E k) / α) - cbar| < ε := by
  intro ε hε
  obtain ⟨A₀, hA₀⟩ := hdec
  obtain ⟨δ, hδ, hδp⟩ := Metric.continuousAt_iff.1 hpc ε hε
  set d := min δ X with hd
  have hd0 : 0 < d := lt_min hδ hX
  have hdδ : d ≤ δ := min_le_left _ _
  have hdX : d ≤ X := min_le_right _ _
  have hs₀ : cbar < p (X - d / 3) :=
    hpX ▸ hp (mem_Ici.2 (by linarith)) (mem_Ici.2 hX.le) (by linarith)
  obtain ⟨q₀, hq₀, hK⟩ := hinf (p (X - d / 3) - cbar) (by linarith)
  refine ⟨max (max A₀ 1) (3 * q₀ / d), fun α hα E σ hE => ?_⟩
  have hα1 : 1 ≤ α := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hα)
  have hα0 : 0 < α := by linarith
  have hαA : A₀ ≤ α := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hα)
  have hαq : 3 * q₀ / d ≤ α := le_trans (le_max_right _ _) hα
  have hq₀α : q₀ / α ≤ d / 3 := by
    rw [div_le_iff₀ hd0] at hαq
    rw [div_le_iff₀ hα0]; linarith
  have hii := entry_step_ii hα0 hp hc (hA₀ α hαA) hE hq₀
    (show K + c q₀ < p (X - d / 3) * q₀ by linarith)
  set Q := ∑ k ∈ E, σ E k with hQ
  have hQα : X - 2 * d / 3 ≤ Q / α := by
    have h1 : X - d / 3 ≤ (Q + q₀) / α := by rw [le_div_iff₀ hα0]; linarith
    rw [add_div] at h1
    linarith
  have hQpos : 0 < Q := by
    have : 0 < Q / α := by linarith
    exact (div_pos_iff_of_pos_right hα0).1 this
  have hge := entry_price_ge hE hlow hQpos
  rw [abs_lt]
  refine ⟨by linarith, ?_⟩
  rcases le_or_gt X (Q / α) with h | h
  · have := hp.antitoneOn (mem_Ici.2 hX.le) (mem_Ici.2 (hX.le.trans h)) h
    linarith
  · have hdist : dist (Q / α) X < δ := by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith
    have := hδp hdist
    rw [Real.dist_eq, abs_lt, hpX] at this
    linarith

/-- **Proposition 12.F.1** (MWG, p. 412). Market demand `αx(p)` with inverse `p` (strictly
decreasing, continuous at `X = x(c̄) > 0`), convex cost `c`, entry cost `K`, minimum average cost
`c̄ = min_{q>0}(K + c(q))/q` attained at the efficient scale `q̄ > 0`, and best responses unique
and weakly decreasing for large `α` (Exercise 12.F.1). Then the price in any SPNE of the
two-stage Cournot entry model converges to `c̄` uniformly: `max_{p_α ∈ P_α} |p_α − c̄| → 0`. -/
theorem proposition_12_F_1 {p c : ℝ → ℝ} {K cbar qbar X : ℝ} (hp : StrictAntiOn p (Ici 0))
    (hpc : ContinuousAt p X) (hX : 0 < X) (hpX : p X = cbar) (hc : ConvexOn ℝ (Ici 0) c)
    (hqbar : 0 < qbar) (hmin : ∀ q, 0 < q → cbar * q ≤ K + c q)
    (hatt : cbar * qbar = K + c qbar)
    (hdec : ∃ A₀, ∀ α, A₀ ≤ α → BRDecreasing (sizedDemand p α) c) :
    ∀ ε, 0 < ε → ∃ A, ∀ α, A ≤ α → ∀ (E : Finset ℕ) (σ : Finset ℕ → ℕ → ℝ),
      IsCournotEntrySPNE p c K α E σ → |p ((∑ k ∈ E, σ E k) / α) - cbar| < ε :=
  competitive_limit hp hpc hX hpX hc hmin
    (fun η hη => ⟨qbar, hqbar, by nlinarith [mul_pos hη hqbar]⟩) hdec

/-- **Footnote 29** (MWG, p. 413). With constant marginal cost, `c(q) = c₀q` and entry cost
`K ≥ 0` (the cost of Example 12.E.2), average cost `c₀ + K/q` has no minimum, but Proposition
12.F.1 still holds with `c̄ = c₀`, the limit of average cost. -/
theorem footnote_12_29 {p : ℝ → ℝ} {K c₀ X : ℝ} (hK : 0 ≤ K) (hp : StrictAntiOn p (Ici 0))
    (hpc : ContinuousAt p X) (hX : 0 < X) (hpX : p X = c₀)
    (hdec : ∃ A₀, ∀ α, A₀ ≤ α → BRDecreasing (sizedDemand p α) (fun q => c₀ * q)) :
    ∀ ε, 0 < ε → ∃ A, ∀ α, A ≤ α → ∀ (E : Finset ℕ) (σ : Finset ℕ → ℕ → ℝ),
      IsCournotEntrySPNE p (fun q => c₀ * q) K α E σ →
        |p ((∑ k ∈ E, σ E k) / α) - c₀| < ε := by
  have hlin : ConvexOn ℝ (Ici 0) (fun q : ℝ => c₀ * q) :=
    ⟨convex_Ici 0, fun x _ y _ a b _ _ _ => le_of_eq (by simp only [smul_eq_mul]; ring)⟩
  refine competitive_limit hp hpc hX hpX hlin (fun q _ => by linarith) (fun η hη => ?_) hdec
  refine ⟨K / η + 1, by positivity, ?_⟩
  have : (c₀ + η) * (K / η + 1) = c₀ * (K / η + 1) + K + η := by field_simp; ring
  linarith

/-! ### Exercise 12.F.1: decreasing best responses -/

/-- **Exercise 12.F.1, core step** (MWG, p. 435). Let `p` be twice differentiable with `p' < 0`
and `p'' ≤ L(−p')` on `[0, ∞)` (`L ≥ 0`). At market size `α > 0`, if `0 ≤ Q₋ⱼ < Q̂₋ⱼ`,
`q ∈ b(Q₋ⱼ)`, `q̂ ∈ b(Q̂₋ⱼ)` and `Lq̂ < α`, then `q̂ ≤ q`: the cross partial
`p'(s)/α + q p''(s)/α²` is negative where `Lq < α`, so profit has strictly decreasing differences
and revealed preference applies. No assumption on `c` is needed. -/
theorem exercise_12_F_1_core {p p' p'' c : ℝ → ℝ} {L α : ℝ} (hp : ∀ s, HasDerivAt p (p' s) s)
    (hp' : ∀ s, HasDerivAt p' (p'' s) s) (hneg : ∀ s, 0 ≤ s → p' s < 0)
    (hL : ∀ s, 0 ≤ s → p'' s ≤ L * -p' s) (hL0 : 0 ≤ L) (hα : 0 < α)
    {R R' y y' : ℝ} (hR : 0 ≤ R) (hRR : R < R')
    (hy : IsBROn (sizedDemand p α) c (Ici 0) R y) (hy' : IsBROn (sizedDemand p α) c (Ici 0) R' y')
    (hLy : L * y' < α) : y' ≤ y := by
  by_contra hlt
  push Not at hlt
  have hy0 : (0 : ℝ) ≤ y := hy.1
  have hφ : ∀ r, 0 ≤ r → p' ((r + y') / α) * y' < p' ((r + y) / α) * y := by
    intro r hr
    have hderiv : ∀ t, HasDerivAt (fun t => p' ((r + t) / α) * t)
        (p'' ((r + t) / α) * (1 / α) * t + p' ((r + t) / α)) t := by
      intro t
      have h1 : HasDerivAt (fun t => (r + t) / α) (1 / α) t := by
        simpa using ((hasDerivAt_id' t).const_add r).div_const α
      have h2 : HasDerivAt (fun t => p' ((r + t) / α)) (p'' ((r + t) / α) * (1 / α)) t :=
        (hp' ((r + t) / α)).comp t h1
      convert h2.mul (hasDerivAt_id' t) using 1
      ring
    have hanti : StrictAntiOn (fun t => p' ((r + t) / α) * t) (Icc y y') := by
      apply strictAntiOn_of_deriv_neg (convex_Icc y y')
      · exact fun t _ => (hderiv t).continuousAt.continuousWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        rw [(hderiv t).deriv]
        have ht0 : 0 ≤ t := by linarith [ht.1]
        have hs : 0 ≤ (r + t) / α := div_nonneg (by linarith) hα.le
        have h1 := mul_le_mul_of_nonneg_right (hL _ hs) ht0
        have h2 := hneg _ hs
        have hLt : L * t < α := lt_of_le_of_lt (mul_le_mul_of_nonneg_left ht.2.le hL0) hLy
        have e : p'' ((r + t) / α) * (1 / α) * t + p' ((r + t) / α) =
            (p'' ((r + t) / α) * t + α * p' ((r + t) / α)) / α := by
          field_simp
        rw [e]
        apply div_neg_of_neg_of_pos _ hα
        nlinarith [mul_neg_of_neg_of_pos h2 (sub_pos.2 hLt)]
    exact hanti ⟨le_rfl, hlt.le⟩ ⟨hlt.le, le_rfl⟩ hlt
  set D : ℝ → ℝ := fun r => (p ((r + y') / α) * y' - c y') - (p ((r + y) / α) * y - c y)
    with hD
  have hA : ∀ z r, HasDerivAt (fun r => p ((r + z) / α)) (p' ((r + z) / α) * (1 / α)) r := by
    intro z r
    have h1 : HasDerivAt (fun r => (r + z) / α) (1 / α) r := by
      simpa using ((hasDerivAt_id' r).add_const z).div_const α
    exact (hp _).comp r h1
  have hDd : ∀ r, HasDerivAt D ((p' ((r + y') / α) * y' - p' ((r + y) / α) * y) / α) r := by
    intro r
    have := (((hA y' r).mul_const y').sub_const (c y')).sub (((hA y r).mul_const y).sub_const (c y))
    convert this using 1
    field_simp
  have hDanti : StrictAntiOn D (Icc R R') := by
    apply strictAntiOn_of_deriv_neg (convex_Icc R R')
    · exact fun r _ => (hDd r).continuousAt.continuousWithinAt
    · intro r hr
      rw [interior_Icc] at hr
      rw [(hDd r).deriv]
      exact div_neg_of_neg_of_pos (by linarith [hφ r (by linarith [hr.1])]) hα
  have hlt2 := hDanti ⟨le_rfl, hRR.le⟩ ⟨hRR.le, le_rfl⟩ hRR
  have h1 := hy.2 y' hy'.1
  have h2 := hy'.2 y hy.1
  unfold cbrProfit sizedDemand at h1 h2
  simp only [hD] at hlt2
  linarith

/-- If `p` is nonincreasing on `[0, ∞)` and `c(q) − c(0) > p(0)q` for `q > B`, every best response
(at any market size `α > 0`, rivals' output `R ≥ 0`) is at most `B`. -/
theorem sized_br_le {p c : ℝ → ℝ} {B α R y : ℝ} (hp : AntitoneOn p (Ici 0))
    (hcB : ∀ y, B < y → p 0 * y < c y - c 0) (hα : 0 < α) (hR : 0 ≤ R)
    (hy : IsBROn (sizedDemand p α) c (Ici 0) R y) : y ≤ B := by
  by_contra h
  push Not at h
  have hy0 : (0 : ℝ) ≤ y := hy.1
  have h0 := hy.2 0 (mem_Ici.2 le_rfl)
  unfold cbrProfit sizedDemand at h0
  have hpy : p ((R + y) / α) ≤ p 0 :=
    hp (mem_Ici.2 le_rfl) (mem_Ici.2 (div_nonneg (by linarith) hα.le))
      (div_nonneg (by linarith) hα.le)
  have := mul_le_mul_of_nonneg_right hpy hy0
  have := hcB y h
  simp only [mul_zero, zero_sub] at h0
  linarith

/-- **Exercise 12.F.1** (MWG, p. 435), under a sufficient condition. Suppose `p` is twice
differentiable with `p' < 0` and `p'' ≤ L(−p')` on `[0, ∞)` (`L ≥ 0`), and costs grow fast enough
that best responses are bounded: `c(q) − c(0) > p(0)q` for `q > B`. Then for every market size
`α > LB` the best-response correspondence is weakly decreasing: `0 ≤ Q₋ⱼ < Q̂₋ⱼ`, `q ∈ b(Q₋ⱼ)`,
`q̂ ∈ b(Q̂₋ⱼ)` imply `q̂ ≤ q`. -/
theorem exercise_12_F_1 {p p' p'' c : ℝ → ℝ} {L B α : ℝ} (hp : ∀ s, HasDerivAt p (p' s) s)
    (hp' : ∀ s, HasDerivAt p' (p'' s) s) (hneg : ∀ s, 0 ≤ s → p' s < 0)
    (hL : ∀ s, 0 ≤ s → p'' s ≤ L * -p' s) (hL0 : 0 ≤ L)
    (hcB : ∀ y, B < y → p 0 * y < c y - c 0) (hα : 0 < α) (hαL : L * B < α) :
    ∀ R R', 0 ≤ R → R < R' → ∀ y y', IsBROn (sizedDemand p α) c (Ici 0) R y →
      IsBROn (sizedDemand p α) c (Ici 0) R' y' → y' ≤ y := by
  have hpanti : StrictAntiOn p (Ici 0) := by
    apply strictAntiOn_of_deriv_neg (convex_Ici 0)
    · exact fun s _ => (hp s).continuousAt.continuousWithinAt
    · intro s hs
      rw [interior_Ici] at hs
      rw [(hp s).deriv]
      exact hneg s (le_of_lt hs)
  intro R R' hR hRR y y' hy hy'
  have hyB := sized_br_le hpanti.antitoneOn hcB hα (by linarith) hy'
  exact exercise_12_F_1_core hp hp' hneg hL hL0 hα hR hRR hy hy'
    (lt_of_le_of_lt (mul_le_mul_of_nonneg_left hyB hL0) hαL)

/-- **Proposition 12.F.1 from Exercise 12.F.1** (MWG, pp. 412 and 435). Proposition 12.F.1 with
the decreasing best response derived from the sufficient condition of `exercise_12_F_1`, plus the
book's standing assumption that best responses are unique. -/
theorem proposition_12_F_1_of_exercise_12_F_1 {p p' p'' c : ℝ → ℝ} {K cbar qbar X L B : ℝ}
    (hp : ∀ s, HasDerivAt p (p' s) s) (hp' : ∀ s, HasDerivAt p' (p'' s) s)
    (hneg : ∀ s, 0 ≤ s → p' s < 0) (hL : ∀ s, 0 ≤ s → p'' s ≤ L * -p' s) (hL0 : 0 ≤ L)
    (hB : 0 ≤ B) (hcB : ∀ y, B < y → p 0 * y < c y - c 0)
    (huniq : ∀ α, 0 < α → ∀ R, 0 ≤ R → ∀ y y', IsBROn (sizedDemand p α) c (Ici 0) R y →
      IsBROn (sizedDemand p α) c (Ici 0) R y' → y = y')
    (hX : 0 < X) (hpX : p X = cbar) (hc : ConvexOn ℝ (Ici 0) c) (hqbar : 0 < qbar)
    (hmin : ∀ q, 0 < q → cbar * q ≤ K + c q) (hatt : cbar * qbar = K + c qbar) :
    ∀ ε, 0 < ε → ∃ A, ∀ α, A ≤ α → ∀ (E : Finset ℕ) (σ : Finset ℕ → ℕ → ℝ),
      IsCournotEntrySPNE p c K α E σ → |p ((∑ k ∈ E, σ E k) / α) - cbar| < ε := by
  have hpanti : StrictAntiOn p (Ici 0) := by
    apply strictAntiOn_of_deriv_neg (convex_Ici 0)
    · exact fun s _ => (hp s).continuousAt.continuousWithinAt
    · intro s hs
      rw [interior_Ici] at hs
      rw [(hp s).deriv]
      exact hneg s (le_of_lt hs)
  refine proposition_12_F_1 hpanti (hp X).continuousAt hX hpX hc hqbar hmin hatt
    ⟨L * B + 1, fun α hα => ?_⟩
  have hLB : 0 ≤ L * B := mul_nonneg hL0 hB
  have hα0 : 0 < α := by linarith
  exact ⟨huniq α hα0, exercise_12_F_1 hp hp' hneg hL hL0 hcB hα0 (by linarith)⟩

/-! ### Exercise 12.F.1 as printed is false -/

/-- The inverse demand of the counterexample to Exercise 12.F.1: `p(s) = 1 + e^{−(s+1)²}`. -/
noncomputable def gaussDemand (s : ℝ) : ℝ := 1 + Real.exp (-(s + 1) ^ 2)

/-- `p'(s) = −2(s + 1)e^{−(s+1)²}`. -/
noncomputable def gaussDemand' (s : ℝ) : ℝ := -2 * (s + 1) * Real.exp (-(s + 1) ^ 2)

/-- `p''(s) = (4(s + 1)² − 2)e^{−(s+1)²}`. -/
noncomputable def gaussDemand'' (s : ℝ) : ℝ := (4 * (s + 1) ^ 2 - 2) * Real.exp (-(s + 1) ^ 2)

/-- `p'` is the derivative of `gaussDemand`. -/
theorem gaussDemand_hasDerivAt (s : ℝ) : HasDerivAt gaussDemand (gaussDemand' s) s := by
  have h : HasDerivAt (fun s : ℝ => -(s + 1) ^ 2) (-(2 * (s + 1))) s := by
    convert (((hasDerivAt_id' s).add_const 1).pow 2).neg using 1
    norm_num
  unfold gaussDemand gaussDemand'
  convert h.exp.const_add 1 using 1
  ring

/-- `p''` is the derivative of `gaussDemand'`. -/
theorem gaussDemand'_hasDerivAt (s : ℝ) : HasDerivAt gaussDemand' (gaussDemand'' s) s := by
  have h : HasDerivAt (fun s : ℝ => -(s + 1) ^ 2) (-(2 * (s + 1))) s := by
    convert (((hasDerivAt_id' s).add_const 1).pow 2).neg using 1
    norm_num
  have h2 : HasDerivAt (fun s : ℝ => -2 * (s + 1)) (-2) s := by
    convert ((hasDerivAt_id' s).add_const 1).const_mul (-2) using 1
    ring
  unfold gaussDemand' gaussDemand''
  convert h2.mul h.exp using 1
  ring

/-- Bounds on `[0, ∞)`: `1 < p ≤ 2`, `−1 ≤ p' < 0`, `p'' < 4`. -/
theorem gaussDemand_bounds {s : ℝ} (hs : 0 ≤ s) :
    1 < gaussDemand s ∧ gaussDemand s ≤ 2 ∧ gaussDemand' s < 0 ∧ -1 ≤ gaussDemand' s ∧
      gaussDemand'' s < 4 := by
  unfold gaussDemand gaussDemand' gaussDemand''
  set u := s + 1 with hu
  have hu1 : 1 ≤ u := by linarith
  set E := Real.exp (-u ^ 2) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hE1 : E ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have hEu : E * (u ^ 2 + 1) ≤ 1 := by
    have h1 := Real.add_one_le_exp (u ^ 2)
    have h2 : E * Real.exp (u ^ 2) = 1 := by rw [hE, ← Real.exp_add]; simp
    nlinarith
  refine ⟨by linarith, by linarith, by nlinarith, ?_, ?_⟩
  · nlinarith [sq_nonneg (u - 1)]
  · nlinarith

/-- The model of the counterexample satisfies the Section 12.F assumptions: `p` is differentiable
with `p' < 0` on `[0, ∞)` (so `x = p⁻¹` is differentiable with `x' < 0`) and `c(q) = q²` is
strictly convex. -/
theorem gaussDemand_model :
    (∀ s, HasDerivAt gaussDemand (gaussDemand' s) s) ∧ (∀ s, 0 ≤ s → gaussDemand' s < 0) ∧
    StrictConvexOn ℝ (Ici 0) (fun q : ℝ => q ^ 2) :=
  ⟨gaussDemand_hasDerivAt, fun _ hs => (gaussDemand_bounds hs).2.2.1, strictConvexOn_pow le_rfl⟩

/-- The first-order expression `F(R, y) = p(s) + y p'(s)/α − 2y`, `s = (R + y)/α`, for the
counterexample (`c(q) = q²`). -/
noncomputable def gaussFOC (α R y : ℝ) : ℝ :=
  gaussDemand ((R + y) / α) + y * (gaussDemand' ((R + y) / α) * (1 / α)) - 2 * y

/-- At a best response, `F(R, y) = 0` and `3/8 ≤ y ≤ 1` (for `α ≥ 4`). -/
theorem gauss_br_foc {α R y : ℝ} (hα : 4 ≤ α) (hR : 0 ≤ R)
    (hy : IsBROn (sizedDemand gaussDemand α) (fun q => q ^ 2) (Ici 0) R y) :
    gaussFOC α R y = 0 ∧ 3 / 8 ≤ y ∧ y ≤ 1 := by
  have hα0 : 0 < α := by linarith
  have hP : ∀ Q, HasDerivAt (sizedDemand gaussDemand α)
      ((fun Q => gaussDemand' (Q / α) * (1 / α)) Q) Q := by
    intro Q
    have h1 : HasDerivAt (fun Q : ℝ => Q / α) (1 / α) Q := by
      simpa using (hasDerivAt_id' Q).div_const α
    exact (gaussDemand_hasDerivAt (Q / α)).comp Q h1
  have hc : ∀ y : ℝ, HasDerivAt (fun q : ℝ => q ^ 2) ((fun q => 2 * q) y) y := fun y => by
    simpa using hasDerivAt_pow 2 y
  have hfoc := cbr_foc hP hc hy
  have hy0 : (0 : ℝ) ≤ y := hy.1
  have hs : 0 ≤ (R + y) / α := div_nonneg (by linarith) hα0.le
  obtain ⟨hb1, hb2, hb3, hb4, -⟩ := gaussDemand_bounds hs
  unfold sizedDemand at hfoc
  have hpos : 0 < y := by
    rcases eq_or_lt_of_le hy0 with h | h
    · subst h
      simp only [zero_mul, add_zero, mul_zero] at hfoc hb1
      linarith [hfoc.1]
    · exact h
  have hF := hfoc.2 hpos
  have hF' : gaussFOC α R y = 0 := by unfold gaussFOC; linarith
  have hinv : 0 < 1 / α := by positivity
  have hinv4 : 1 / α ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hα
  have hy1 : y ≤ 1 := by nlinarith [mul_pos hpos hinv]
  refine ⟨hF', ?_, hy1⟩
  nlinarith [mul_le_mul_of_nonneg_left hb4 (mul_nonneg hy0 hinv.le)]

/-- `F(R, ·)` is strictly decreasing on `[0, 1]` (for `α ≥ 4`, `R ≥ 0`). -/
theorem gaussFOC_anti {α R : ℝ} (hα : 4 ≤ α) (hR : 0 ≤ R) :
    StrictAntiOn (gaussFOC α R) (Icc 0 1) := by
  have hα0 : 0 < α := by linarith
  have h1 : ∀ y, HasDerivAt (fun y : ℝ => (R + y) / α) (1 / α) y := fun y => by
    simpa using ((hasDerivAt_id' y).const_add R).div_const α
  have hd : ∀ y, HasDerivAt (gaussFOC α R)
      (gaussDemand' ((R + y) / α) * (1 / α) + (1 * (gaussDemand' ((R + y) / α) * (1 / α)) +
        y * (gaussDemand'' ((R + y) / α) * (1 / α) * (1 / α))) - 2 * 1) y := by
    intro y
    have hA : HasDerivAt (fun y => gaussDemand ((R + y) / α))
        (gaussDemand' ((R + y) / α) * (1 / α)) y := (gaussDemand_hasDerivAt _).comp y (h1 y)
    have hB : HasDerivAt (fun y => gaussDemand' ((R + y) / α))
        (gaussDemand'' ((R + y) / α) * (1 / α)) y := (gaussDemand'_hasDerivAt _).comp y (h1 y)
    exact (hA.add ((hasDerivAt_id' y).mul (hB.mul_const (1 / α)))).sub
      ((hasDerivAt_id' y).const_mul 2)
  apply strictAntiOn_of_deriv_neg (convex_Icc 0 1)
  · exact fun y _ => (hd y).continuousAt.continuousWithinAt
  · intro y hy
    rw [interior_Icc] at hy
    rw [(hd y).deriv]
    have hs : 0 ≤ (R + y) / α := div_nonneg (by linarith [hy.1]) hα0.le
    obtain ⟨-, -, hb3, -, hb5⟩ := gaussDemand_bounds hs
    have hinv : 0 < 1 / α := by positivity
    have hinv4 : 1 / α ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hα
    have hq : y * gaussDemand'' ((R + y) / α) ≤ 4 :=
      by nlinarith [mul_le_mul_of_nonneg_left hb5.le hy.1.le, hy.2]
    have : y * (gaussDemand'' ((R + y) / α) * (1 / α) * (1 / α)) ≤ 4 * (1 / α) * (1 / α) := by
      have := mul_le_mul_of_nonneg_right hq (mul_nonneg hinv.le hinv.le)
      linarith
    nlinarith [mul_neg_of_neg_of_pos hb3 hinv, mul_le_mul hinv4 hinv4 hinv.le (by norm_num)]

/-- For `y ∈ [3/8, 1]`, `F(·, y)` is strictly increasing on `R ≥ 2α²` (strategic
complements: `p' + (y/α)p'' > 0` far out in the tail of `p`). -/
theorem gaussFOC_mono {α y : ℝ} (hα : 4 ≤ α) (hy1 : 3 / 8 ≤ y) (hy2 : y ≤ 1) :
    StrictMonoOn (fun R => gaussFOC α R y) (Ici (2 * α ^ 2)) := by
  have hα0 : 0 < α := by linarith
  have h1 : ∀ R, HasDerivAt (fun R : ℝ => (R + y) / α) (1 / α) R := fun R => by
    simpa using ((hasDerivAt_id' R).add_const y).div_const α
  have hd : ∀ R, HasDerivAt (fun R => gaussFOC α R y)
      (gaussDemand' ((R + y) / α) * (1 / α) +
        y * (gaussDemand'' ((R + y) / α) * (1 / α) * (1 / α))) R := by
    intro R
    have hA : HasDerivAt (fun R => gaussDemand ((R + y) / α))
        (gaussDemand' ((R + y) / α) * (1 / α)) R := (gaussDemand_hasDerivAt _).comp R (h1 R)
    have hB : HasDerivAt (fun R => gaussDemand' ((R + y) / α))
        (gaussDemand'' ((R + y) / α) * (1 / α)) R := (gaussDemand'_hasDerivAt _).comp R (h1 R)
    have := (hA.add ((hB.mul_const (1 / α)).const_mul y)).sub_const (2 * y)
    exact this
  apply strictMonoOn_of_deriv_pos (convex_Ici _)
  · exact fun R _ => (hd R).continuousAt.continuousWithinAt
  · intro R hR
    rw [interior_Ici] at hR
    rw [(hd R).deriv]
    have hR' : 2 * α ^ 2 < R := hR
    set u := (R + y) / α + 1 with hu
    have hu2 : 2 * α + 1 ≤ u := by
      rw [hu]
      have : 2 * α ≤ (R + y) / α := by rw [le_div_iff₀ hα0]; nlinarith
      linarith
    unfold gaussDemand' gaussDemand''
    rw [← hu]
    set E := Real.exp (-u ^ 2)
    have hE : 0 < E := Real.exp_pos _
    have key : 0 < -2 * u * α + y * (4 * u ^ 2 - 2) := by nlinarith
    have e : -2 * u * E * (1 / α) + y * ((4 * u ^ 2 - 2) * E * (1 / α) * (1 / α)) =
        E * (-2 * u * α + y * (4 * u ^ 2 - 2)) / α ^ 2 := by
      field_simp
    rw [e]
    positivity

/-- **Exercise 12.F.1, the printed claim is false** (MWG, p. 435). For the inverse demand
`p(s) = 1 + e^{−(s+1)²}` (differentiable, `p' < 0` on `[0, ∞)`) and the strictly convex cost
`c(q) = q²`, at every market size `α ≥ 4` best responses exist and are unique, but the best
response is strictly increasing somewhere: at `Q₋ⱼ = 2α²` and `2α² + 1`. So there is no `α̂` such
that `b(·)` is weakly decreasing for all `α ≥ α̂`. (The ratio `p''/(−p')` is unbounded, so the
sufficient condition of `exercise_12_F_1` fails.) -/
theorem exercise_12_F_1_counterexample {α : ℝ} (hα : 4 ≤ α) :
    (∀ R, 0 ≤ R → ∃ y, IsBROn (sizedDemand gaussDemand α) (fun q => q ^ 2) (Ici 0) R y) ∧
    (∀ R, 0 ≤ R → ∀ y y', IsBROn (sizedDemand gaussDemand α) (fun q => q ^ 2) (Ici 0) R y →
      IsBROn (sizedDemand gaussDemand α) (fun q => q ^ 2) (Ici 0) R y' → y = y') ∧
    ∃ y y', IsBROn (sizedDemand gaussDemand α) (fun q => q ^ 2) (Ici 0) (2 * α ^ 2) y ∧
      IsBROn (sizedDemand gaussDemand α) (fun q => q ^ 2) (Ici 0) (2 * α ^ 2 + 1) y' ∧ y < y' := by
  have hα0 : 0 < α := by linarith
  have hex : ∀ R, 0 ≤ R → ∃ y, IsBROn (sizedDemand gaussDemand α) (fun q => q ^ 2) (Ici 0) R y := by
    intro R hR
    obtain ⟨y, hy⟩ := cbr_exists_Icc (P := sizedDemand gaussDemand α) (c := fun q => q ^ 2)
      (B := 2) (by norm_num) (by unfold sizedDemand gaussDemand; fun_prop) (by fun_prop) R
    refine ⟨y, hy.1.1, fun y' hy' => ?_⟩
    rcases le_or_gt y' 2 with h | h
    · exact hy.2 y' ⟨hy', h⟩
    · have h0 := hy.2 0 ⟨le_rfl, by norm_num⟩
      have hp2 : sizedDemand gaussDemand α (R + y') ≤ 2 := by
        unfold sizedDemand gaussDemand
        have : Real.exp (-((R + y') / α + 1) ^ 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
        linarith
      unfold cbrProfit at h0 ⊢
      have hy'0 : (0 : ℝ) ≤ y' := by linarith
      nlinarith [mul_le_mul_of_nonneg_right hp2 hy'0]
  have huniq : ∀ R, 0 ≤ R → ∀ y y',
      IsBROn (sizedDemand gaussDemand α) (fun q => q ^ 2) (Ici 0) R y →
      IsBROn (sizedDemand gaussDemand α) (fun q => q ^ 2) (Ici 0) R y' → y = y' := by
    intro R hR y y' hy hy'
    obtain ⟨h1, h2, h3⟩ := gauss_br_foc hα hR hy
    obtain ⟨h1', h2', h3'⟩ := gauss_br_foc hα hR hy'
    exact (gaussFOC_anti hα hR).injOn ⟨by linarith, h3⟩ ⟨by linarith, h3'⟩ (h1.trans h1'.symm)
  refine ⟨hex, huniq, ?_⟩
  have hR1 : (0 : ℝ) ≤ 2 * α ^ 2 := by positivity
  obtain ⟨y, hy⟩ := hex _ hR1
  obtain ⟨y', hy'⟩ := hex (2 * α ^ 2 + 1) (by positivity)
  refine ⟨y, y', hy, hy', ?_⟩
  obtain ⟨f1, l1, u1⟩ := gauss_br_foc hα hR1 hy
  obtain ⟨f2, l2, u2⟩ := gauss_br_foc hα (by positivity) hy'
  by_contra hle
  push Not at hle
  have hA := (gaussFOC_anti hα (show (0 : ℝ) ≤ 2 * α ^ 2 + 1 by positivity)).antitoneOn
    ⟨by linarith, u2⟩ ⟨by linarith, u1⟩ hle
  have hM := gaussFOC_mono hα l1 u1 (mem_Ici.2 le_rfl) (mem_Ici.2 (by linarith))
    (show 2 * α ^ 2 < 2 * α ^ 2 + 1 by linarith)
  simp only at hM
  linarith

/-- **Exercise 12.F.1, the printed claim refuted** (MWG, p. 435): for the model of
`exercise_12_F_1_counterexample` there is no market size beyond which best responses are unique
and weakly decreasing. -/
theorem exercise_12_F_1_false :
    ¬ ∃ A, ∀ α, A ≤ α → BRDecreasing (sizedDemand gaussDemand α) (fun q => q ^ 2) := by
  rintro ⟨A, hA⟩
  set α := max A 4
  obtain ⟨-, -, y, y', hy, hy', hlt⟩ := exercise_12_F_1_counterexample (le_max_right A 4)
  have := (hA α (le_max_left A 4)).2 _ _ (by positivity) (by linarith) y y' hy hy'
  linarith

/-- With linear demand `p(s) = a − s` and any convex cost, best responses are unique: profit is
strictly concave in own output. -/
theorem linear_br_unique {a α : ℝ} (hα : 0 < α) {c : ℝ → ℝ} (hc : ConvexOn ℝ (Ici 0) c)
    {R y y' : ℝ} (hy : IsBROn (sizedDemand (fun s => a - s) α) c (Ici 0) R y)
    (hy' : IsBROn (sizedDemand (fun s => a - s) α) c (Ici 0) R y') : y = y' := by
  by_contra hne
  have hy0 : (0 : ℝ) ≤ y := hy.1
  have hy'0 : (0 : ℝ) ≤ y' := hy'.1
  have hm : (y + y') / 2 ∈ Ici (0 : ℝ) := mem_Ici.2 (by linarith)
  have h1 := hy.2 _ hm
  have h2 := hy'.2 y hy.1
  have h3 := hy.2 y' hy'.1
  have hcv := hc.2 (mem_Ici.2 hy0) (mem_Ici.2 hy'0) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num)
  simp only [smul_eq_mul] at hcv
  rw [show 1 / 2 * y + 1 / 2 * y' = (y + y') / 2 by ring] at hcv
  unfold cbrProfit sizedDemand at h1 h2 h3
  have hsq : 0 < (y - y') ^ 2 := by
    have : y - y' ≠ 0 := sub_ne_zero.2 hne
    positivity
  have e : (a - (R + (y + y') / 2) / α) * ((y + y') / 2) -
      ((a - (R + y) / α) * y + (a - (R + y') / α) * y') / 2 = (y - y') ^ 2 / (4 * α) := by
    field_simp
    ring
  have : 0 < (y - y') ^ 2 / (4 * α) := by positivity
  linarith

/-- With linear demand `p(s) = a − s` and convex cost, the best response is unique and weakly
decreasing at every market size `α > 0` (Exercise 12.F.1 with `L = 0`). -/
theorem linear_brDecreasing {a α : ℝ} (hα : 0 < α) {c : ℝ → ℝ} (hc : ConvexOn ℝ (Ici 0) c) :
    BRDecreasing (sizedDemand (fun s => a - s) α) c := by
  have hp : ∀ s : ℝ, HasDerivAt (fun s : ℝ => a - s) ((fun _ => (-1 : ℝ)) s) s := fun s => by
    simpa using (hasDerivAt_id s).const_sub a
  have hp' : ∀ s : ℝ, HasDerivAt (fun _ : ℝ => (-1 : ℝ)) ((fun _ => (0 : ℝ)) s) s :=
    fun s => hasDerivAt_const s _
  refine ⟨fun R _ y y' hy hy' => linear_br_unique hα hc hy hy', fun R R' hR hRR y y' hy hy' =>
    exercise_12_F_1_core (L := 0) hp hp' (fun _ _ => by norm_num) (fun _ _ => by norm_num) le_rfl
      hα hR hRR hy hy' (by simpa using hα)⟩

/-- **Instance for Proposition 12.F.1** (MWG, p. 412). Inverse demand `p(s) = 3 − s`, cost
`c(q) = q²`, entry cost `K = 1`: average cost `1/q + q` is minimized at `q̄ = 1` with `c̄ = 2`,
`x(c̄) = 1`; every hypothesis of `proposition_12_F_1_of_exercise_12_F_1` holds (`L = 0`,
`B = 3`, unique best responses), so SPNE prices converge to `2`. -/
theorem proposition_12_F_1_instance :
    ∀ ε, 0 < ε → ∃ A, ∀ α, A ≤ α → ∀ (E : Finset ℕ) (σ : Finset ℕ → ℕ → ℝ),
      IsCournotEntrySPNE (fun s => 3 - s) (fun q => q ^ 2) 1 α E σ →
        |(fun s : ℝ => 3 - s) ((∑ k ∈ E, σ E k) / α) - 2| < ε := by
  have hp : ∀ s : ℝ, HasDerivAt (fun s : ℝ => 3 - s) ((fun _ => (-1 : ℝ)) s) s := fun s => by
    simpa using (hasDerivAt_id s).const_sub 3
  have hp' : ∀ s : ℝ, HasDerivAt (fun _ : ℝ => (-1 : ℝ)) ((fun _ => (0 : ℝ)) s) s :=
    fun s => hasDerivAt_const s _
  exact proposition_12_F_1_of_exercise_12_F_1 (L := 0) (B := 3) (qbar := 1) (X := 1) hp hp'
    (fun _ _ => by norm_num) (fun _ _ => by norm_num) le_rfl (by norm_num)
    (fun y hy => by norm_num; nlinarith)
    (fun α hα R _ y y' hy hy' => linear_br_unique hα (convexOn_pow 2) hy hy')
    one_pos (by norm_num) (convexOn_pow 2) one_pos (fun q _ => by nlinarith [sq_nonneg (q - 1)])
    (by norm_num)

/-- **Instance for footnote 29** (MWG, p. 413). Inverse demand `p(s) = 2 − s`, constant marginal
cost `c(q) = q` and entry cost `K = 1`: every hypothesis of `footnote_12_29` holds, so SPNE prices
converge to `c̄ = 1`. -/
theorem footnote_12_29_instance :
    ∀ ε, 0 < ε → ∃ A, ∀ α, A ≤ α → ∀ (E : Finset ℕ) (σ : Finset ℕ → ℕ → ℝ),
      IsCournotEntrySPNE (fun s => 2 - s) (fun q => 1 * q) 1 α E σ →
        |(fun s : ℝ => 2 - s) ((∑ k ∈ E, σ E k) / α) - 1| < ε := by
  have hlin : ConvexOn ℝ (Ici 0) (fun q : ℝ => 1 * q) :=
    ⟨convex_Ici 0, fun x _ y _ a b _ _ _ => le_of_eq (by simp only [smul_eq_mul]; ring)⟩
  exact footnote_12_29 zero_le_one (fun _ _ _ _ h => sub_lt_sub_left h 2)
    (by fun_prop : Continuous fun s : ℝ => 2 - s).continuousAt one_pos (by norm_num)
    ⟨1, fun α hα => linear_brDecreasing (by linarith) hlin⟩

/-- **Instance for Exercise 12.F.1** (MWG, p. 435). `p(s) = 3 − s` (`p' = −1`, `p'' = 0`,
`L = 0`) and `c(q) = q²` (`B = 3`) satisfy every hypothesis of `exercise_12_F_1` at `α = 1`. -/
theorem exercise_12_F_1_instance :
    ∀ R R', 0 ≤ R → R < R' → ∀ y y', IsBROn (sizedDemand (fun s => 3 - s) 1) (fun q => q ^ 2)
      (Ici 0) R y → IsBROn (sizedDemand (fun s => 3 - s) 1) (fun q => q ^ 2) (Ici 0) R' y' →
        y' ≤ y := by
  have hp : ∀ s : ℝ, HasDerivAt (fun s : ℝ => 3 - s) ((fun _ => (-1 : ℝ)) s) s := fun s => by
    simpa using (hasDerivAt_id s).const_sub 3
  have hp' : ∀ s : ℝ, HasDerivAt (fun _ : ℝ => (-1 : ℝ)) ((fun _ => (0 : ℝ)) s) s :=
    fun s => hasDerivAt_const s _
  exact exercise_12_F_1 (L := 0) (B := 3) hp hp' (fun _ _ => by norm_num)
    (fun _ _ => by norm_num) le_rfl (fun y hy => by norm_num; nlinarith) one_pos (by norm_num)

/-! ### An explicit SPNE -/

/-- **An SPNE of the two-stage Cournot entry model** (MWG, p. 412), showing that the hypotheses of
`entry_incumbents_no_expand`, `entry_step_ii` and `entry_price_ge` are met. With `p(s) = 2 − s`,
`α = 1`, zero production cost and `K = 1`, the rule "`n` entrants each produce `2/(n + 1)`" is a
Cournot equilibrium after every entry set, and one entrant (`E = {0}`) is an SPNE: the entrant
earns `0`, a second entrant would earn `4/9 − 1 < 0`. -/
theorem entry_spne_instance :
    IsCournotEntrySPNE (fun s => 2 - s) (fun _ => 0) 1 1 {0}
      (fun F _ => 2 / ((F.card : ℝ) + 1)) ∧
    BRDecreasing (sizedDemand (fun s => 2 - s) 1) (fun _ => 0) ∧
    ∑ k ∈ ({0} : Finset ℕ), (fun (F : Finset ℕ) (_ : ℕ) => 2 / ((F.card : ℝ) + 1)) {1, 0} k ≤
      ∑ k ∈ ({0} : Finset ℕ), (fun (F : Finset ℕ) (_ : ℕ) => 2 / ((F.card : ℝ) + 1)) {0} k ∧
    1 * 0 ≤ ∑ k ∈ ({0} : Finset ℕ), (fun (F : Finset ℕ) (_ : ℕ) => 2 / ((F.card : ℝ) + 1)) {0} k
      + 1 ∧
    0 ≤ (fun s : ℝ => 2 - s) ((∑ k ∈ ({0} : Finset ℕ),
      (fun (F : Finset ℕ) (_ : ℕ) => 2 / ((F.card : ℝ) + 1)) {0} k) / 1) := by
  have hc0 : ConvexOn ℝ (Ici 0) (fun _ : ℝ => (0 : ℝ)) := convexOn_const 0 (convex_Ici 0)
  have hdec := linear_brDecreasing (a := 2) one_pos hc0
  have hp : StrictAntiOn (fun s : ℝ => 2 - s) (Ici 0) := fun _ _ _ _ h => sub_lt_sub_left h 2
  have hspne : IsCournotEntrySPNE (fun s => 2 - s) (fun _ => 0) 1 1 {0}
      (fun F _ => 2 / ((F.card : ℝ) + 1)) := by
    refine ⟨fun F j hj => ?_, fun j hj => ?_, fun j hj => ?_⟩
    · have h1 : 1 ≤ F.card := Nat.succ_le_of_lt (Finset.card_pos.2 ⟨j, hj⟩)
      have hsum : ∑ k ∈ F.erase j, (fun (_ : ℕ) => 2 / ((F.card : ℝ) + 1)) k =
          ((F.card : ℝ) - 1) * (2 / ((F.card : ℝ) + 1)) := by
        rw [Finset.sum_const, Finset.card_erase_of_mem hj, nsmul_eq_mul, Nat.cast_sub h1,
          Nat.cast_one]
      have hn : (0 : ℝ) < (F.card : ℝ) + 1 := by positivity
      refine ⟨mem_Ici.2 (by positivity), fun y' hy' => ?_⟩
      unfold cbrProfit sizedDemand
      rw [hsum]
      have hy2 : ((F.card : ℝ) + 1) * (2 / ((F.card : ℝ) + 1)) = 2 := by field_simp
      simp only [div_one, sub_zero]
      generalize 2 / ((F.card : ℝ) + 1) = Y at hy2 ⊢
      generalize (F.card : ℝ) = n at hy2 ⊢
      have e : (2 - ((n - 1) * Y + y')) * y' = (2 - ((n - 1) * Y + Y)) * Y - (y' - Y) ^ 2 := by
        linear_combination (Y - y') * hy2
      rw [e]
      nlinarith [sq_nonneg (y' - Y)]
    · rw [Finset.mem_singleton] at hj
      subst hj
      unfold entryNetProfit
      norm_num
    · rw [Finset.mem_singleton] at hj
      unfold entryNetProfit
      rw [Finset.sum_const, Finset.card_pair hj]
      norm_num [Finset.card_pair hj]
  have hNE := hspne.1 {0}
  have hNF := hspne.1 (insert 1 {0})
  refine ⟨hspne, hdec, ?_, ?_, ?_⟩
  · exact entry_incumbents_no_expand (sizedDemand_strictAntiOn hp one_pos) hc0 hdec
      (by simp) hNE hNF
  · exact entry_step_ii one_pos hp hc0 hdec hspne one_pos (by norm_num)
  · refine le_trans (le_of_eq (zero_mul (2 : ℝ)).symm) ?_
    have h0 : (0 : ℝ) * 2 ≤ 2 := by norm_num
    have := entry_price_ge (cbar := 0) hspne (fun q _ => by norm_num) (by norm_num)
    simpa using this

end MWG.MarketPower
