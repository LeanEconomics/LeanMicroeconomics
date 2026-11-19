/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGChoiceUnderUncertainty.SecondOrderDominance

/-!
# The integral condition implies second-order dominance

MWG, Proposition 6.D.2, (iii) ⇒ (i), p. 199 (stated without proof; footnote 21 sketches a
double integration by parts for differentiable `u`). We prove it for every nondecreasing
concave `u` on `ℝ₊`: on a grid of mesh `h = x̄/n` the piecewise-linear interpolation
`uₙ(t) = u(0) + ∑_j s_j (min(t, x_{j+1}) - min(t, x_j))` is a nonnegative combination of the
utilities `min(t, x)` with antitone nonnegative slopes, so (iii) and an Abel summation give
`∫ uₙ dG ≤ ∫ uₙ dF`; `uₙ → u` on `(0, x̄]` and dominated convergence finishes. Equal means are
not needed for this direction.
-/

namespace MWG.ChoiceUnderUncertainty

open MeasureTheory ProbabilityTheory Filter Topology Set

/-- Summation by parts. -/
theorem sum_by_parts (a D : ℕ → ℝ) (n : ℕ) :
    ∑ j ∈ Finset.range n, a j * (D (j + 1) - D j) =
      ∑ j ∈ Finset.range n, (a j - a (j + 1)) * D (j + 1) + a n * D n - a 0 * D 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]; ring

/-- The grid points `x_j = j h`. -/
noncomputable def gridPt (h : ℝ) (j : ℕ) : ℝ := j * h

/-- The interpolation of `u` on the grid of mesh `h` with `n` cells. -/
noncomputable def gridInterp (u : ℝ → ℝ) (h : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  u 0 + ∑ j ∈ Finset.range n, (u (gridPt h (j + 1)) - u (gridPt h j)) / h *
    (min t (gridPt h (j + 1)) - min t (gridPt h j))

/-- On the cell `[x_k, x_{k+1}]`, the interpolation is `u(x_k) + s_k (t - x_k)`. -/
theorem gridInterp_cell (u : ℝ → ℝ) {h : ℝ} (hh : 0 < h) {n k : ℕ} (hk : k < n) {t : ℝ}
    (ht1 : gridPt h k ≤ t) (ht2 : t ≤ gridPt h (k + 1)) :
    gridInterp u h n t = u (gridPt h k) +
      (u (gridPt h (k + 1)) - u (gridPt h k)) / h * (t - gridPt h k) := by
  unfold gridInterp
  rw [← Finset.sum_range_add_sum_Ico _ (show k + 1 ≤ n by omega), Finset.sum_range_succ]
  have hlow : ∀ j ∈ Finset.range k, (u (gridPt h (j + 1)) - u (gridPt h j)) / h *
      (min t (gridPt h (j + 1)) - min t (gridPt h j)) = u (gridPt h (j + 1)) - u (gridPt h j) := by
    intro j hj
    have hj' : j + 1 ≤ k := Finset.mem_range.mp hj
    have hle1 : gridPt h (j + 1) ≤ gridPt h k := by
      unfold gridPt
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hj') hh.le
    have h1 : gridPt h (j + 1) ≤ t := hle1.trans ht1
    have hle2 : gridPt h j ≤ gridPt h (j + 1) := by unfold gridPt; push_cast; nlinarith
    have h2 : gridPt h j ≤ t := hle2.trans h1
    rw [min_eq_right h1, min_eq_right h2]
    have : gridPt h (j + 1) - gridPt h j = h := by unfold gridPt; push_cast; ring
    rw [this]; field_simp
  have hhigh : ∀ j ∈ Finset.Ico (k + 1) n, (u (gridPt h (j + 1)) - u (gridPt h j)) / h *
      (min t (gridPt h (j + 1)) - min t (gridPt h j)) = 0 := by
    intro j hj
    have hj' : k + 1 ≤ j := (Finset.mem_Ico.mp hj).1
    have hle1 : gridPt h (k + 1) ≤ gridPt h j := by
      unfold gridPt
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hj') hh.le
    have h1 : t ≤ gridPt h j := ht2.trans hle1
    have hle2 : gridPt h j ≤ gridPt h (j + 1) := by unfold gridPt; push_cast; nlinarith
    have h2 : t ≤ gridPt h (j + 1) := h1.trans hle2
    rw [min_eq_left h1, min_eq_left h2]; ring
  rw [Finset.sum_congr rfl hlow, Finset.sum_congr rfl hhigh, Finset.sum_range_sub
    (fun j => u (gridPt h j)), min_eq_left ht2, min_eq_right ht1]
  have : gridPt h 0 = 0 := by simp [gridPt]
  rw [this, Finset.sum_const_zero]; ring

/-- The interpolation is continuous. -/
theorem gridInterp_continuous (u : ℝ → ℝ) (h : ℝ) (n : ℕ) : Continuous (gridInterp u h n) := by
  unfold gridInterp; fun_prop

/-- The cell index of `t ∈ (0, n h]`: `k = ⌈t/h⌉ - 1`. -/
theorem exists_cell {h : ℝ} (hh : 0 < h) {n : ℕ} {t : ℝ} (ht0 : 0 < t)
    (htn : t ≤ n * h) : ∃ k < n, gridPt h k < t ∧ t ≤ gridPt h (k + 1) := by
  set c := Nat.ceil (t / h)
  have hc1 : 1 ≤ c := Nat.one_le_iff_ne_zero.mpr (by
    intro h0; rw [Nat.ceil_eq_zero] at h0
    exact absurd h0 (not_le.mpr (div_pos ht0 hh)))
  have hcn : c ≤ n := Nat.ceil_le.mpr (by rw [div_le_iff₀ hh]; exact htn)
  refine ⟨c - 1, by omega, ?_, ?_⟩
  · have := Nat.ceil_lt_add_one (div_pos ht0 hh).le
    unfold gridPt
    rw [Nat.cast_sub hc1, Nat.cast_one]
    have : (c : ℝ) - 1 < t / h := by linarith
    calc ((c : ℝ) - 1) * h < t / h * h := mul_lt_mul_of_pos_right this hh
      _ = t := by field_simp
  · unfold gridPt
    rw [Nat.sub_add_cancel hc1]
    have := Nat.le_ceil (t / h)
    calc t = t / h * h := by field_simp
      _ ≤ c * h := mul_le_mul_of_nonneg_right this hh.le

/-- The interpolation lies between `u(x_k)` and `u(x_{k+1})` on a cell. -/
theorem gridInterp_between (u : ℝ → ℝ) {h : ℝ} (hh : 0 < h) {n k : ℕ} (hk : k < n) {t : ℝ}
    (ht1 : gridPt h k ≤ t) (ht2 : t ≤ gridPt h (k + 1))
    (hmono : u (gridPt h k) ≤ u (gridPt h (k + 1))) :
    u (gridPt h k) ≤ gridInterp u h n t ∧ gridInterp u h n t ≤ u (gridPt h (k + 1)) := by
  rw [gridInterp_cell u hh hk ht1 ht2]
  have hlen : gridPt h (k + 1) - gridPt h k = h := by unfold gridPt; push_cast; ring
  have hθ0 : 0 ≤ (t - gridPt h k) / h := div_nonneg (by linarith) hh.le
  have hθ1 : (t - gridPt h k) / h ≤ 1 := by rw [div_le_one hh]; linarith
  have e : (u (gridPt h (k + 1)) - u (gridPt h k)) / h * (t - gridPt h k) =
      (u (gridPt h (k + 1)) - u (gridPt h k)) * ((t - gridPt h k) / h) := by ring
  rw [e]
  constructor <;> nlinarith

/-- **Proposition 6.D.2**, (iii) ⇒ (i) (MWG, p. 199). For MWG distributions, the integral
condition (6.D.2) implies second-order stochastic dominance. -/
theorem sosd_of_integralCondition {μ ν : Measure ℝ} (hμ : IsMWGDist μ) (hν : IsMWGDist ν)
    (h : IntegralCondition μ ν) : SOSD μ ν := by
  intro u hm hc
  have := hμ.1
  have := hν.1
  obtain ⟨M₁, hM₁, hae₁⟩ := hμ.ae_mem
  obtain ⟨M₂, hM₂, hae₂⟩ := hν.ae_mem
  set M := max M₁ M₂
  have hM : 0 < M := lt_max_of_lt_left hM₁
  have hμM : ∀ᵐ t ∂μ, t ∈ Ioc 0 M := hae₁.mono fun t ht => ⟨ht.1, ht.2.trans (le_max_left _ _)⟩
  have hνM : ∀ᵐ t ∂ν, t ∈ Ioc 0 M := hae₂.mono fun t ht => ⟨ht.1, ht.2.trans (le_max_right _ _)⟩
  -- the approximants, with `n + 1` cells
  set hN : ℕ → ℝ := fun n => M / (n + 1)
  have hNpos (n : ℕ) : 0 < hN n := by simp only [hN]; positivity
  set U : ℕ → ℝ → ℝ := fun n => gridInterp u (hN n) (n + 1)
  have hgrid (n j : ℕ) (hj : j ≤ n + 1) : gridPt (hN n) j ∈ Icc 0 M := by
    unfold gridPt
    constructor
    · exact mul_nonneg (Nat.cast_nonneg _) (hNpos n).le
    · simp only [hN]
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      have : (j : ℝ) ≤ n + 1 := by exact_mod_cast hj
      nlinarith
  have hcellval (n : ℕ) (t : ℝ) (ht : t ∈ Ioc 0 M) : ∃ k < n + 1,
      gridPt (hN n) k < t ∧ t ≤ gridPt (hN n) (k + 1) := by
    apply exists_cell (hNpos n) ht.1
    simp only [hN]; push_cast; field_simp; exact ht.2
  -- bounds
  have hbound (n : ℕ) (t : ℝ) (ht : t ∈ Ioc 0 M) : |U n t| ≤ |u 0| + |u M| := by
    obtain ⟨k, hk, h1, h2⟩ := hcellval n t ht
    have hg1 := hgrid n k (by omega)
    have hg2 := hgrid n (k + 1) (by omega)
    have hb := gridInterp_between u (hNpos n) hk h1.le h2
      (hm hg1.1 hg2.1 (by unfold gridPt; push_cast; nlinarith [hNpos n]))
    have l1 := hm (mem_Ici.mpr le_rfl) hg1.1 hg1.1
    have l2 := hm hg2.1 (mem_Ici.mpr hM.le) hg2.2
    rw [abs_le]
    constructor <;> [linarith [neg_abs_le (u 0), abs_nonneg (u M), hb.1];
      linarith [le_abs_self (u M), abs_nonneg (u 0), hb.2]]
  -- pointwise convergence on `(0, M]`
  have hcont : ∀ t ∈ Ioi (0 : ℝ), ContinuousAt u t := by
    have := hc.continuousOn_interior
    rw [interior_Ici] at this
    exact fun t ht => this.continuousAt (isOpen_Ioi.mem_nhds ht)
  have hconv (t : ℝ) (ht : t ∈ Ioc 0 M) : Tendsto (fun n => U n t) atTop (𝓝 (u t)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.mp (hcont t ht.1) ε hε
    obtain ⟨N, hN'⟩ := exists_nat_gt (M / δ)
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨k, hk, h1, h2⟩ := hcellval n t ht
    have hg1 := hgrid n k (by omega)
    have hg2 := hgrid n (k + 1) (by omega)
    have hlen : gridPt (hN n) (k + 1) - gridPt (hN n) k = hN n := by
      unfold gridPt; push_cast; ring
    have hsmall : hN n < δ := by
      simp only [hN]
      rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ hδ] at hN'
      have : (N : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith
    have d1 : dist (gridPt (hN n) k) t < δ := by
      rw [Real.dist_eq, abs_of_neg (by linarith)]; linarith
    have d2 : dist (gridPt (hN n) (k + 1)) t < δ := by
      rw [Real.dist_eq, abs_of_nonneg (by linarith)]; linarith
    have e1 := hball d1
    have e2 := hball d2
    rw [Real.dist_eq] at e1 e2 ⊢
    have hb := gridInterp_between u (hNpos n) hk h1.le h2
      (hm hg1.1 hg2.1 (by linarith))
    rw [abs_lt] at e1 e2 ⊢
    simp only [U]
    constructor <;> linarith [hb.1, hb.2]
  -- dominated convergence for both laws
  have hUmeas (n : ℕ) : Measurable (U n) := (gridInterp_continuous _ _ _).measurable
  have hlim (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (hρ : ∀ᵐ t ∂ρ, t ∈ Ioc 0 M) :
      Tendsto (fun n => ∫ t, U n t ∂ρ) atTop (𝓝 (∫ t, u t ∂ρ)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => |u 0| + |u M|)
      (fun n => (hUmeas n).aestronglyMeasurable) (integrable_const _)
    · intro n
      filter_upwards [hρ] with t ht
      rw [Real.norm_eq_abs]; exact hbound n t ht
    · filter_upwards [hρ] with t ht using hconv t ht
  -- the comparison for each approximant
  have hcomp (n : ℕ) : ∫ t, U n t ∂ν ≤ ∫ t, U n t ∂μ := by
    set a : ℕ → ℝ := fun j => if j < n + 1 then
      (u (gridPt (hN n) (j + 1)) - u (gridPt (hN n) j)) / hN n else 0
    have hmin (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (hρ : ∀ᵐ t ∂ρ, t ∈ Ioc 0 M) (x : ℝ) :
        Integrable (fun t => min t x) ρ :=
      IsMoneyLottery.integrable (S := univ) ⟨inferInstance, 0, M, subset_univ _,
        measure_eq_zero_iff_ae_notMem.mpr (hρ.mono fun t ht => by
          simpa using (⟨ht.1.le, ht.2⟩ : 0 ≤ t ∧ t ≤ M))⟩ (by fun_prop)
    have hU (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (hρ : ∀ᵐ t ∂ρ, t ∈ Ioc 0 M) :
        ∫ t, U n t ∂ρ = u 0 + ∑ j ∈ Finset.range (n + 1), a j *
          (∫ t, min t (gridPt (hN n) (j + 1)) ∂ρ - ∫ t, min t (gridPt (hN n) j) ∂ρ) := by
      simp only [U, gridInterp]
      rw [integral_add (integrable_const _), integral_const, probReal_univ, one_smul,
        integral_finsetSum]
      · congr 1
        refine Finset.sum_congr rfl fun j hj => ?_
        have hj' : j < n + 1 := Finset.mem_range.mp hj
        simp only [a, hj', ↓reduceIte]
        rw [integral_const_mul, integral_sub (hmin ρ hρ _) (hmin ρ hρ _)]
      · intro j _
        exact ((hmin ρ hρ _).sub (hmin ρ hρ _)).const_mul _
      · exact integrable_finsetSum _ fun j _ => ((hmin ρ hρ _).sub (hmin ρ hρ _)).const_mul _
    set D : ℕ → ℝ := fun j => ∫ t, min t (gridPt (hN n) j) ∂μ -
      ∫ t, min t (gridPt (hN n) j) ∂ν
    have hD (j : ℕ) : 0 ≤ D j := by
      have hx : 0 ≤ gridPt (hN n) j := mul_nonneg (Nat.cast_nonneg _) (hNpos n).le
      simp only [D]
      rw [integral_min_eq hμ hx, integral_min_eq hν hx]
      linarith [h _ hx]
    have hD0 : D 0 = 0 := by
      simp only [D, gridPt, Nat.cast_zero, zero_mul]
      rw [integral_min_eq hμ le_rfl, integral_min_eq hν le_rfl]
      simp
    have hdiff : ∫ t, U n t ∂μ - ∫ t, U n t ∂ν =
        ∑ j ∈ Finset.range (n + 1), a j * (D (j + 1) - D j) := by
      rw [hU μ hμM, hU ν hνM]
      simp only [D]
      rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    have ha_anti (j : ℕ) (hj : j < n + 1) : 0 ≤ a j - a (j + 1) := by
      have hg0 := hgrid n j (by omega)
      have hg1 := hgrid n (j + 1) (by omega)
      by_cases hj2 : j + 1 < n + 1
      · have hg2 := hgrid n (j + 2) (by omega)
        simp only [a, hj, hj2, ↓reduceIte]
        have hs := hc.slope_anti_adjacent hg0.1 hg2.1
          (show gridPt (hN n) j < gridPt (hN n) (j + 1) by
            unfold gridPt; push_cast; nlinarith [hNpos n])
          (show gridPt (hN n) (j + 1) < gridPt (hN n) (j + 1 + 1) by
            unfold gridPt; push_cast; nlinarith [hNpos n])
        have l1 : gridPt (hN n) (j + 1) - gridPt (hN n) j = hN n := by
          unfold gridPt; push_cast; ring
        have l2 : gridPt (hN n) (j + 1 + 1) - gridPt (hN n) (j + 1) = hN n := by
          unfold gridPt; push_cast; ring
        rw [l1, l2] at hs
        linarith
      · simp only [a, hj, hj2, ↓reduceIte, ↓reduceIte, sub_zero]
        exact div_nonneg (sub_nonneg.mpr (hm hg0.1 hg1.1 (by
          unfold gridPt; push_cast; nlinarith [hNpos n]))) (hNpos n).le
    have : 0 ≤ ∑ j ∈ Finset.range (n + 1), a j * (D (j + 1) - D j) := by
      rw [sum_by_parts, hD0, mul_zero, sub_zero]
      have hlast : a (n + 1) = 0 := by simp [a]
      rw [hlast, zero_mul, add_zero]
      exact Finset.sum_nonneg fun j hj =>
        mul_nonneg (ha_anti j (Finset.mem_range.mp hj)) (hD (j + 1))
    linarith
  exact le_of_tendsto_of_tendsto' (hlim ν hνM) (hlim μ hμM) hcomp

/-- **Proposition 6.D.2**, (i) ⇔ (iii) (MWG, p. 199). For MWG distributions, second-order
stochastic dominance is equivalent to the integral condition (6.D.2). -/
theorem proposition_6_D_2_i_iii {μ ν : Measure ℝ} (hμ : IsMWGDist μ) (hν : IsMWGDist ν) :
    SOSD μ ν ↔ IntegralCondition μ ν :=
  ⟨sosd_integralCondition hμ hν, sosd_of_integralCondition hμ hν⟩

/-- **Footnote 21 and p. 198** (single crossing). If `F` and `G` have the same mean and the graph
of `G` is first above and then permanently below that of `F` (crossing at `c`), condition
(6.D.2) holds, so `G` is riskier than `F`. -/
theorem integralCondition_of_single_crossing {μ ν : Measure ℝ} (hμ : IsMWGDist μ)
    (hν : IsMWGDist ν) (hmean : ∫ x, x ∂μ = ∫ x, x ∂ν) {c : ℝ}
    (h1 : ∀ t ≤ c, cdf μ t ≤ cdf ν t) (h2 : ∀ t, c ≤ t → cdf ν t ≤ cdf μ t) :
    IntegralCondition μ ν := by
  have := hμ.1
  have := hν.1
  obtain ⟨M₁, -, hae₁⟩ := hμ.ae_mem
  obtain ⟨M₂, -, hae₂⟩ := hν.ae_mem
  set M := max (max M₁ M₂) (max c 0)
  have hone (ρ : Measure ℝ) [IsProbabilityMeasure ρ] {K : ℝ} (hρ : ∀ᵐ t ∂ρ, t ∈ Ioc 0 K)
      (t : ℝ) (ht : K ≤ t) : cdf ρ t = 1 := by
    rw [cdf_eq_real, measureReal_def]
    have : ρ (Iic t) = 1 := by
      rw [← prob_compl_eq_zero_iff measurableSet_Iic, measure_eq_zero_iff_ae_notMem]
      filter_upwards [hρ] with s hs
      simpa using hs.2.trans ht
    rw [this]; simp
  have hμ1 : ∀ t, M ≤ t → cdf μ t = 1 := fun t ht => hone μ hae₁ t
    ((le_max_left _ _).trans ((le_max_left _ _).trans ht))
  have hν1 : ∀ t, M ≤ t → cdf ν t = 1 := fun t ht => hone ν hae₂ t
    ((le_max_right _ _).trans ((le_max_left _ _).trans ht))
  have hM0 : 0 ≤ M := (le_max_right _ _).trans (le_max_right _ _)
  have hcM : c ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  have harea := equal_areas hμ hν hM0 (hμ1 M le_rfl) (hν1 M le_rfl) hmean
  have hI (a b : ℝ) : IntervalIntegrable (fun t => cdf ν t - cdf μ t) volume a b :=
    ((monotone_cdf ν).intervalIntegrable).sub ((monotone_cdf μ).intervalIntegrable)
  have hzero : ∫ t in (0)..M, (cdf ν t - cdf μ t) = 0 := by
    have : (fun t => cdf ν t - cdf μ t) = fun t => -(cdf μ t - cdf ν t) := by
      funext t; ring
    rw [this, intervalIntegral.integral_neg, harea, neg_zero]
  intro x hx
  rw [← sub_nonneg, ← intervalIntegral.integral_sub ((monotone_cdf ν).intervalIntegrable)
    ((monotone_cdf μ).intervalIntegrable)]
  by_cases hxc : x ≤ c
  · exact intervalIntegral.integral_nonneg hx fun t ht => sub_nonneg.mpr (h1 t (ht.2.trans hxc))
  · have hxc' : c < x := lt_of_not_ge hxc
    rw [← intervalIntegral.integral_add_adjacent_intervals (hI 0 M) (hI M x), hzero, zero_add]
    rcases le_total M x with hMx | hxM
    · apply intervalIntegral.integral_nonneg hMx
      intro t ht
      rw [hμ1 t ht.1, hν1 t ht.1]; simp
    · rw [intervalIntegral.integral_symm, neg_nonneg]
      have : ∫ t in x..M, (cdf ν t - cdf μ t) = -∫ t in x..M, (cdf μ t - cdf ν t) := by
        rw [← intervalIntegral.integral_neg]; congr 1; funext t; ring
      rw [this, neg_nonpos]
      exact intervalIntegral.integral_nonneg hxM fun t ht =>
        sub_nonneg.mpr (h2 t (hxc'.le.trans ht.1))

end MWG.ChoiceUnderUncertainty
