/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGProduction.CostFOC

/-!
# The geometry of cost and supply in the single-output case (MWG Section 5.D, pp. 143-147)

With input prices fixed, `C(q) = c(w̄, q)`, `AC(q) = C(q)/q` and the supply locus
`q(p) = argmax_{q ≥ 0} pq - C(q)`.

* (5.D.1) and its sufficiency for convex `C` are `foc_5_C_6` and `foc_5_C_6_sufficient`.
* The nonconvex case (Figure 5.D.3, p. 145): with `C(0) = 0`, `q = 0` is the unique optimum for
  `p < min AC`, the optimal set at `p = AC(q̄)` is `{0} ∪ {q > 0 : AC(q) = AC(q̄)}`, and for
  `p > AC(q̄)` every optimum is positive and earns positive profits (`supply_nonconvex`).
* **Exercise 5.D.1**: `AC(q̄) = C'(q̄)` at the efficient scale, using differentiability only at
  `q̄`; without it only `C'₋(q̄) ≤ AC(q̄) ≤ C'₊(q̄)` holds (`exercise_5_D_1_onesided`,
  `exercise_5_D_1_kink`).
* Setup costs (Figures 5.D.4-5.D.6): nonsunk fixed cost with linear variable cost, sunk costs,
  and **Exercise 5.D.2** (partially sunk).
* Short-run and long-run costs (pp. 146-147): `C(q|z̄) ≥ C(q)`, equality at the long-run input
  level, lower envelope and equality of marginal costs.

Departure: "p = C_v'(q) implies pq > C_v(q)" (p. 146) needs strict convexity; for convex `C_v`
only `pq ≥ C_v(q)` holds (`sunk_cost_covers_variable`, `sunk_cost_strict_fails`).
-/

namespace MWG.Production

open MWG.ClassicalDemand MWG.ConsumerChoice Filter Topology

/-- The optimal output set of `max_{q ≥ 0} pq - C(q)`. -/
def outputSupply (C : ℝ → ℝ) (p : ℝ) : Set ℝ :=
  {q | 0 ≤ q ∧ ∀ q', 0 ≤ q' → p * q' - C q' ≤ p * q - C q}

/-- **Section 5.D** (MWG, p. 145, Figure 5.D.3). Let `C(0) = 0` and `q̄ > 0` minimize average cost
over `q > 0` (the efficient scale). (a) If `p < AC(q̄)`, then `q = 0` is the unique optimum.
(b) If `p = AC(q̄)`, the optimal set is `{0} ∪ {q > 0 : AC(q) = AC(q̄)}`. (c) If `p > AC(q̄)`, every
optimum is positive and earns strictly positive profit, so `p > AC(q*)`. -/
theorem supply_nonconvex {C : ℝ → ℝ} (h0 : C 0 = 0) {qb : ℝ} (hqb : 0 < qb)
    (hmin : ∀ q, 0 < q → C qb / qb ≤ C q / q) (p : ℝ) :
    (p < C qb / qb → outputSupply C p = {0}) ∧
      (p = C qb / qb → outputSupply C p = {q | q = 0 ∨ (0 < q ∧ C q / q = C qb / qb)}) ∧
      (C qb / qb < p → ∀ q ∈ outputSupply C p, 0 < q ∧ 0 < p * q - C q ∧ C q / q < p) := by
  have hprof : ∀ q, 0 < q → p * q - C q = q * (p - C q / q) := fun q hq => by
    field_simp
  refine ⟨fun hp => ?_, fun hp => ?_, fun hp q hq => ?_⟩
  · ext q
    simp only [outputSupply, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hq0, hopt⟩
      by_contra hne
      have hpos : 0 < q := lt_of_le_of_ne hq0 (Ne.symm hne)
      have := hopt 0 le_rfl
      rw [h0, hprof q hpos] at this
      have : p - C q / q < 0 := by linarith [hmin q hpos]
      nlinarith
    · rintro rfl
      refine ⟨le_rfl, fun q' hq' => ?_⟩
      rw [h0]
      rcases hq'.lt_or_eq with hpos | rfl
      · rw [hprof q' hpos]
        nlinarith [hmin q' hpos]
      · simp [h0]
  · ext q
    simp only [outputSupply, Set.mem_ofPred_eq]
    have hopt0 : ∀ q', 0 ≤ q' → p * q' - C q' ≤ 0 := by
      intro q' hq'
      rcases hq'.lt_or_eq with hpos | rfl
      · rw [hprof q' hpos, hp]
        nlinarith [hmin q' hpos]
      · simp [h0]
    constructor
    · rintro ⟨hq0, hopt⟩
      rcases hq0.lt_or_eq with hpos | rfl
      · right
        refine ⟨hpos, le_antisymm ?_ (hmin q hpos)⟩
        have h1 := hopt qb hqb.le
        have h2 : p * qb - C qb = 0 := by rw [hp]; field_simp; ring
        rw [hprof q hpos] at h1
        rw [h2] at h1
        rw [← hp]
        by_contra hlt
        rw [not_le] at hlt
        nlinarith
      · left; rfl
    · rintro (rfl | ⟨hpos, hav⟩)
      · exact ⟨le_rfl, fun q' hq' => by rw [h0]; simpa using hopt0 q' hq'⟩
      · refine ⟨hpos.le, fun q' hq' => ?_⟩
        rw [hprof q hpos, hav, ← hp, sub_self, mul_zero]
        exact hopt0 q' hq'
  · obtain ⟨hq0, hopt⟩ := hq
    have hbig : 0 < p * qb - C qb := by
      rw [hprof qb hqb]
      exact mul_pos hqb (by linarith)
    have h1 := hopt qb hqb.le
    have hposprof : 0 < p * q - C q := by linarith
    have hqpos : 0 < q := by
      rcases hq0.lt_or_eq with h | h
      · exact h
      · rw [← h, h0] at hposprof; simp at hposprof
    refine ⟨hqpos, hposprof, ?_⟩
    rw [hprof q hqpos] at hposprof
    have := (mul_pos_iff_of_pos_left hqpos).mp hposprof
    linarith

/-- **Exercise 5.D.1** (MWG, p. 144). If `q̄ > 0` minimizes `AC(q) = C(q)/q` over `q > 0` and `C` is
differentiable at `q̄`, then `AC(q̄) = C'(q̄)`. Only differentiability at `q̄` is used. -/
theorem exercise_5_D_1 {C : ℝ → ℝ} {qb d : ℝ} (hqb : 0 < qb)
    (hmin : ∀ q, 0 < q → C qb / qb ≤ C q / q) (hd : HasDerivAt C d qb) : C qb / qb = d := by
  have hAC : HasDerivAt (fun q => C q / q) ((d * qb - C qb * 1) / qb ^ 2) qb :=
    hd.div (hasDerivAt_id qb) hqb.ne'
  have hloc : IsLocalMin (fun q => C q / q) qb := by
    filter_upwards [eventually_gt_nhds hqb] with q hq
    exact hmin q hq
  have h0 := hloc.hasDerivAt_eq_zero hAC
  have h1 : d * qb - C qb = 0 := by
    rw [mul_one, div_eq_zero_iff] at h0
    rcases h0 with h | h
    · exact h
    · exact absurd h (pow_ne_zero 2 hqb.ne')
  field_simp
  linarith

/-- **Exercise 5.D.1** (MWG, p. 144), second question: without differentiability at `q̄`, only
`C'₋(q̄) ≤ AC(q̄) ≤ C'₊(q̄)` holds (one-sided derivatives). -/
theorem exercise_5_D_1_onesided {C : ℝ → ℝ} {qb dl dr : ℝ} (hqb : 0 < qb)
    (hmin : ∀ q, 0 < q → C qb / qb ≤ C q / q)
    (hdr : HasDerivWithinAt C dr (Set.Ici qb) qb) (hdl : HasDerivWithinAt C dl (Set.Iic qb) qb) :
    dl ≤ C qb / qb ∧ C qb / qb ≤ dr := by
  -- `C(q) ≥ AC(q̄) q` for `q > 0`, with equality at `q̄`
  have hge : ∀ q, 0 < q → C qb / qb * q ≤ C q := fun q hq => by
    have := hmin q hq
    rwa [le_div_iff₀ hq] at this
  have heq : C qb / qb * qb = C qb := by field_simp
  constructor
  · have hs := hasDerivWithinAt_iff_tendsto_slope.mp hdl
    rw [Set.Iic_sdiff_right] at hs
    apply le_of_tendsto hs
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (eventually_gt_nhds hqb)] with q hq hq0
    have hq' : q < qb := hq
    rw [slope_def_field, div_le_iff_of_neg (by linarith)]
    nlinarith [hge q hq0]
  · have hs := hasDerivWithinAt_iff_tendsto_slope.mp hdr
    rw [Set.Ici_sdiff_left] at hs
    apply ge_of_tendsto hs
    filter_upwards [self_mem_nhdsWithin] with q hq
    have hq' : qb < q := hq
    rw [slope_def_field, le_div_iff₀ (by linarith)]
    nlinarith [hge q (by linarith)]

/-- **Exercise 5.D.1** (MWG, p. 144): the equality can fail at a kink. For
`C(q) = max{1, q²}`, `q̄ = 1` minimizes `AC` with `AC(1) = 1`, but `C'₋(1) = 0` and `C'₊(1) = 2`. -/
theorem exercise_5_D_1_kink :
    (∀ q : ℝ, 0 < q → max 1 (1 ^ 2) / 1 ≤ max 1 (q ^ 2) / q) ∧
      HasDerivWithinAt (fun q : ℝ => max 1 (q ^ 2)) 2 (Set.Ici 1) 1 ∧
      HasDerivWithinAt (fun q : ℝ => max 1 (q ^ 2)) 0 (Set.Iic 1) 1 := by
  refine ⟨fun q hq => ?_, ?_, ?_⟩
  · rw [le_div_iff₀ hq]
    norm_num
    rcases le_total q 1 with h | h
    · exact Or.inl h
    · exact Or.inr (by nlinarith)
  · have h1 : HasDerivWithinAt (fun q : ℝ => q ^ 2) 2 (Set.Ici 1) 1 := by
      have := (hasDerivAt_pow 2 (1 : ℝ)).hasDerivWithinAt (s := Set.Ici 1)
      simpa using this
    apply h1.congr_of_mem (fun q hq => ?_) (Set.mem_Ici.mpr le_rfl)
    exact max_eq_right (by nlinarith [Set.mem_Ici.mp hq])
  · have h1 : HasDerivWithinAt (fun _ : ℝ => (1 : ℝ)) 0 (Set.Iic 1) 1 :=
      hasDerivWithinAt_const _ _ _
    apply h1.congr_of_eventuallyEq _ (by norm_num)
    filter_upwards [nhdsWithin_le_nhds (eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)),
      self_mem_nhdsWithin] with q hq0 hq
    have hq1 : q ≤ 1 := hq
    exact max_eq_left (by nlinarith)

/-- **Figure 5.D.5** (MWG, p. 145). Constant returns variable cost with a nonsunk setup cost:
`C(0) = 0`, `C(q) = K + cq` for `q > 0` (`K > 0`). For `p ≤ c` the unique optimum is `q = 0`;
for `p > c` profits are unbounded and no optimum exists ("infinite supply"). -/
theorem figure_5_D_5 {K c p : ℝ} (hK : 0 < K) :
    let C : ℝ → ℝ := fun q => if q = 0 then 0 else K + c * q
    (p ≤ c → outputSupply C p = {0}) ∧ (c < p → outputSupply C p = ∅) := by
  intro C
  constructor
  · intro hp
    ext q
    simp only [outputSupply, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hq0, hopt⟩
      by_contra hne
      have := hopt 0 le_rfl
      simp only [C, hne, ↓reduceIte, mul_zero, sub_zero] at this
      nlinarith
    · rintro rfl
      refine ⟨le_rfl, fun q' hq' => ?_⟩
      by_cases h : q' = 0
      · simp [C, h]
      · simp only [C, h, ↓reduceIte, mul_zero, sub_zero]
        nlinarith
  · intro hp
    ext q
    simp only [outputSupply, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hq0 hopt
    set q' := q + (K + |p * q - C q| + 1) / (p - c) with hq'
    have hpc : 0 < p - c := by linarith
    have hq'pos : 0 < q' := by
      have : 0 < (K + |p * q - C q| + 1) / (p - c) := by positivity
      linarith
    have := hopt q' hq'pos.le
    simp only [C, hq'pos.ne', ↓reduceIte] at this
    have h2 : (p - c) * ((K + |p * q - C q| + 1) / (p - c)) = K + |p * q - C q| + 1 := by
      field_simp
    have h3 : p * q' - (K + c * q') = (p - c) * q + (K + |p * q - C q| + 1) - K := by
      rw [hq']; nlinarith
    have h4 : (p - c) * q ≥ 0 := mul_nonneg hpc.le hq0
    linarith [le_abs_self (p * q - C q)]

/-- **Section 5.D** (MWG, p. 146). With a sunk cost, `C(q) = C_v(q) + K` for all `q ≥ 0`, the
supply is the same as without `K`. -/
theorem sunk_cost_supply (Cv : ℝ → ℝ) (K p : ℝ) :
    outputSupply (fun q => Cv q + K) p = outputSupply Cv p := by
  ext q
  simp only [outputSupply, Set.mem_ofPred_eq]
  constructor <;> rintro ⟨hq, h⟩ <;> exact ⟨hq, fun q' hq' => by linarith [h q' hq']⟩

/-- **Section 5.D** (MWG, p. 146). If `C_v` is convex on `[0, ∞)` with `C_v(0) = 0` and
`p = C_v'(q)`, then `pq ≥ C_v(q)`: the firm covers its variable costs. -/
theorem sunk_cost_covers_variable {Cv : ℝ → ℝ} (hc : ConvexOn ℝ (Set.Ici 0) Cv) (h0 : Cv 0 = 0)
    {q p : ℝ} (hq : 0 ≤ q) (hd : HasDerivAt Cv p q) : Cv q ≤ p * q := by
  have := convex_tangent_le hc (Set.mem_Ici.mpr hq) (Set.mem_Ici.mpr le_rfl) hd
  rw [h0] at this
  linarith

/-- The strict inequality `pq > C_v(q)` printed on p. 146 fails for linear `C_v` (correction):
`C_v(q) = q` is convex, `C_v(0) = 0`, `C_v'(1) = 1` and `1·1 = C_v(1)`. -/
theorem sunk_cost_strict_fails :
    ConvexOn ℝ (Set.Ici 0) (fun q : ℝ => q) ∧ HasDerivAt (fun q : ℝ => q) 1 1 ∧
      ¬ ((fun q : ℝ => q) 1 < 1 * 1) :=
  ⟨convexOn_id (convex_Ici 0), hasDerivAt_id 1, by norm_num⟩

/-- **Exercise 5.D.2** (MWG, p. 146), partially sunk costs: `C(0) = K₀`, `C(q) = K + C_v(q)` for
`q > 0`, `0 < K₀ < K`. Producing some `q > 0` is optimal over shutting down iff
`pq - C_v(q) ≥ K - K₀`: only the nonsunk part `K - K₀` of the fixed cost matters. (The graph of
the supply locus is a figure.) -/
theorem exercise_5_D_2 (Cv : ℝ → ℝ) {K K₀ p q : ℝ} (hq : 0 < q) :
    let C : ℝ → ℝ := fun q => if q = 0 then K₀ else K + Cv q
    (p * 0 - C 0 ≤ p * q - C q ↔ K - K₀ ≤ p * q - Cv q) := by
  intro C
  simp only [C, hq.ne', ↓reduceIte, mul_zero, zero_sub]
  constructor <;> intro h <;> linarith

/-! ### Short-run and long-run costs -/

/-- The short-run input requirement set with input `k` fixed at `z̄`. -/
def shortRunReq {n : ℕ} (V : Set (Fin n → ℝ)) (k : Fin n) (zb : ℝ) : Set (Fin n → ℝ) :=
  {z | z ∈ V ∧ z k = zb}

/-- **Section 5.D** (MWG, p. 146). Short-run costs are at least long-run costs:
`C(q|z̄) ≥ C(q)` (`w ≥ 0`, the short-run problem feasible). -/
theorem shortRun_ge_longRun {n : ℕ} {V : Set (Fin n → ℝ)} (hV : V ⊆ {z | 0 ≤ z}) {w : Fin n → ℝ}
    (hw : 0 ≤ w) (k : Fin n) {zb : ℝ} (hne : (shortRunReq V k zb).Nonempty) :
    supportFn V w ≤ supportFn (shortRunReq V k zb) w :=
  vcost_mono hV (fun _ hz => hz.1) hne hw

/-- **Section 5.D** (MWG, pp. 146-147). If a long-run cost-minimizing input vector has `z_k = z̄`,
short-run and long-run costs coincide: `C(q|z_k(w, q)) = C(q)`. -/
theorem shortRun_eq_longRun {n : ℕ} {V : Set (Fin n → ℝ)} {w z : Fin n → ℝ} (k : Fin n)
    (hz : z ∈ supportArgmin V w) :
    supportFn (shortRunReq V k (z k)) w = supportFn V w := by
  have hz' : z ∈ supportArgmin (shortRunReq V k (z k)) w := ⟨⟨hz.1, rfl⟩, fun y hy => hz.2 y hy.1⟩
  rw [supportFn_eq_of_mem_argmin hz', supportFn_eq_of_mem_argmin hz]

/-- **Section 5.D** (MWG, p. 147). The long-run cost function is the lower envelope of the
short-run cost functions: `C(q) = min_{z̄} C(q|z̄)` (attained at `z̄ = z_k(w, q)`). -/
theorem longRun_lower_envelope {n : ℕ} {V : Set (Fin n → ℝ)} (hV : V ⊆ {z | 0 ≤ z})
    {w z : Fin n → ℝ} (hw : 0 ≤ w) (k : Fin n) (hz : z ∈ supportArgmin V w) :
    IsLeast {c | ∃ zb, (shortRunReq V k zb).Nonempty ∧ c = supportFn (shortRunReq V k zb) w}
      (supportFn V w) :=
  ⟨⟨z k, ⟨z, hz.1, rfl⟩, (shortRun_eq_longRun k hz).symm⟩,
    by rintro _ ⟨zb, hne, rfl⟩; exact shortRun_ge_longRun hV hw k hne⟩

/-- **Section 5.D** (MWG, p. 147). If the short-run cost `C(·|z̄)` with `z̄ = z_k(w, q̄)` and the
long-run cost `C(·)` are both differentiable at `q̄`, the marginal costs are equal:
`C'(q̄) = C'(q̄|z̄)` (tangency of the envelope). -/
theorem shortRun_marginal_eq {Clr Csr : ℝ → ℝ} {qb d dsr : ℝ}
    (hge : ∀ q, Clr q ≤ Csr q) (heq : Csr qb = Clr qb) (hd : HasDerivAt Clr d qb)
    (hdsr : HasDerivAt Csr dsr qb) : d = dsr := by
  have hmin : IsLocalMin (fun q => Csr q - Clr q) qb :=
    Eventually.of_forall fun q => by simp only; linarith [hge q, heq]
  have := hmin.hasDerivAt_eq_zero (hdsr.sub hd)
  linarith

end MWG.Production
