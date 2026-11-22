/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGChoiceUnderUncertainty.SOSDApprox

/-!
# Hat-function discretizations of a distribution

Preparation for Proposition 6.D.2, (i) ⇒ (ii) (MWG, p. 199). On the grid `x_j = j h`,
`j = 0, …, N`, of mesh `h = x̄/N`, the hat functions `λ_j(t) = max(0, 1 - |t - x_j|/h)` form a
partition of unity on `(0, x̄]` with `∑_j λ_j(t) x_j = t`. They give two finite
discretizations of a distribution `F` concentrated on `(0, x̄]`:

* the *dilation* `∑_j w_j δ_{x_j}`, `w_j = ∫ λ_j dF`, which moves the mass at `t` to the two
  neighbouring grid points keeping its mean (an elementary increase in risk, Example 6.D.3), so
  `∫ u dF` dominates it for every concave `u`;
* the *contraction* `∑_j m_j δ_{c_j}`, `m_j = ∫ λ_j dF`, `c_j` the `λ_j`-weighted mean of `F`,
  which `F` is a mean-preserving spread of, so it dominates `∫ u dF` for every concave `u`.

Both have the mean of `F`, and as `h → 0` their expectations of a continuous function converge
to the expectation under `F`. The discretizations are also written as Kreps simple lotteries.
-/

namespace MWG.ChoiceUnderUncertainty

open MeasureTheory ProbabilityTheory Filter Topology Set

/-- The hat function of half-width `h` centred at `x`. -/
noncomputable def hatFn (h x t : ℝ) : ℝ := max 0 (1 - |t - x| / h)

theorem hatFn_nonneg (h x t : ℝ) : 0 ≤ hatFn h x t := le_max_left _ _

theorem continuous_hatFn (h x : ℝ) : Continuous (hatFn h x) := by
  unfold hatFn; fun_prop

theorem hatFn_le_one {h : ℝ} (hh : 0 < h) (x t : ℝ) : hatFn h x t ≤ 1 := by
  unfold hatFn
  refine max_le zero_le_one ?_
  have : 0 ≤ |t - x| / h := div_nonneg (abs_nonneg _) hh.le
  linarith

/-- The hat function vanishes at distance at least `h` from its centre. -/
theorem hatFn_eq_zero {h x t : ℝ} (hh : 0 < h) (hd : h ≤ |t - x|) : hatFn h x t = 0 := by
  unfold hatFn
  apply max_eq_left
  rw [sub_nonpos, le_div_iff₀ hh]
  linarith

/-- Where the hat function is positive, `t` is within `h` of the centre. -/
theorem abs_sub_lt_of_hatFn_pos {h x t : ℝ} (hh : 0 < h) (hp : 0 < hatFn h x t) :
    |t - x| < h := by
  by_contra hc
  rw [hatFn_eq_zero hh (not_lt.mp hc)] at hp
  exact lt_irrefl _ hp

/-- On the cell `[x_k, x_{k+1}]` only the hats at `x_k` and `x_{k+1}` are active, with weights
`1 - θ` and `θ`, `θ = (t - x_k)/h`. -/
theorem hatFn_grid_sum {h : ℝ} (hh : 0 < h) {N k : ℕ} (hk : k < N) {t : ℝ}
    (h1 : gridPt h k ≤ t) (h2 : t ≤ gridPt h (k + 1)) (f : ℕ → ℝ) :
    ∑ j ∈ Finset.range (N + 1), hatFn h (gridPt h j) t * f j =
      (1 - (t - gridPt h k) / h) * f k + (t - gridPt h k) / h * f (k + 1) := by
  have hx : gridPt h (k + 1) = gridPt h k + h := by unfold gridPt; push_cast; ring
  have hθ1 : (t - gridPt h k) / h ≤ 1 := by rw [div_le_one hh]; linarith
  rw [Finset.sum_eq_add k (k + 1) (by omega)]
  · congr 1
    · congr 1
      unfold hatFn
      rw [abs_of_nonneg (by linarith), max_eq_right (by linarith)]
    · congr 1
      unfold hatFn
      rw [abs_of_nonpos (by linarith), max_eq_right]
      · rw [hx]; field_simp; ring
      · have : 0 ≤ (t - gridPt h k) / h := div_nonneg (by linarith) hh.le
        rw [hx]
        have e : 1 - |t - (gridPt h k + h)| / h = (t - gridPt h k) / h := by
          rw [abs_of_nonpos (by linarith)]; field_simp; ring
        rw [← abs_of_nonpos (show t - (gridPt h k + h) ≤ 0 by linarith), e]
        exact this
  · intro j _ hj
    rw [hatFn_eq_zero hh, zero_mul]
    rcases lt_or_gt_of_ne hj.1 with hlt | hgt
    · have hc : (j : ℝ) + 1 ≤ k := by exact_mod_cast hlt
      have : gridPt h j + h ≤ gridPt h k := by unfold gridPt; nlinarith
      rw [abs_of_nonneg (by linarith)]; linarith
    · have hc : (k : ℝ) + 2 ≤ j := by
        have : k + 2 ≤ j := by omega
        exact_mod_cast this
      have : gridPt h (k + 1) + h ≤ gridPt h j := by unfold gridPt; push_cast; nlinarith
      rw [abs_of_nonpos (by linarith)]; linarith
  · intro hn; exact absurd (Finset.mem_range.mpr (by omega)) hn
  · intro hn; exact absurd (Finset.mem_range.mpr (by omega)) hn

/-- The hats at the grid points sum to one on `(0, N h]`. -/
theorem hatFn_sum_one {h : ℝ} (hh : 0 < h) {N : ℕ} {t : ℝ} (ht0 : 0 < t) (htN : t ≤ N * h) :
    ∑ j ∈ Finset.range (N + 1), hatFn h (gridPt h j) t = 1 := by
  obtain ⟨k, hk, h1, h2⟩ := exists_cell hh ht0 htN
  have := hatFn_grid_sum hh hk h1.le h2 (fun _ => 1)
  simp only [mul_one] at this
  rw [this]; ring

/-- The hats reproduce the identity on `(0, N h]`: `∑_j λ_j(t) x_j = t`. -/
theorem hatFn_sum_id {h : ℝ} (hh : 0 < h) {N : ℕ} {t : ℝ} (ht0 : 0 < t) (htN : t ≤ N * h) :
    ∑ j ∈ Finset.range (N + 1), hatFn h (gridPt h j) t * gridPt h j = t := by
  obtain ⟨k, hk, h1, h2⟩ := exists_cell hh ht0 htN
  rw [hatFn_grid_sum hh hk h1.le h2]
  have hx : gridPt h (k + 1) = gridPt h k + h := by unfold gridPt; push_cast; ring
  rw [hx]; field_simp; ring

/-- The piecewise-linear interpolation of a concave function lies below it. -/
theorem hatFn_sum_concave {h : ℝ} (hh : 0 < h) {N : ℕ} {t : ℝ} (ht0 : 0 < t) (htN : t ≤ N * h)
    {U : ℝ → ℝ} (hU : ConcaveOn ℝ univ U) :
    ∑ j ∈ Finset.range (N + 1), hatFn h (gridPt h j) t * U (gridPt h j) ≤ U t := by
  obtain ⟨k, hk, h1, h2⟩ := exists_cell hh ht0 htN
  rw [hatFn_grid_sum hh hk h1.le h2]
  have hx : gridPt h (k + 1) = gridPt h k + h := by unfold gridPt; push_cast; ring
  have hθ0 : 0 ≤ (t - gridPt h k) / h := div_nonneg (by linarith) hh.le
  have hθ1 : (t - gridPt h k) / h ≤ 1 := by rw [div_le_one hh]; linarith
  have := hU.2 (mem_univ (gridPt h k)) (mem_univ (gridPt h (k + 1)))
    (show 0 ≤ 1 - (t - gridPt h k) / h by linarith) hθ0 (by ring)
  simp only [smul_eq_mul] at this
  have e : (1 - (t - gridPt h k) / h) * gridPt h k + (t - gridPt h k) / h * gridPt h (k + 1)
      = t := by rw [hx]; field_simp; ring
  rw [e] at this
  exact this

/-- If every active hat at `t` has `|g(y_j) - g(t)| ≤ ε`, the hat-weighted average of the
`g(y_j)` is within `ε` of `g(t)`. -/
theorem hatFn_sum_approx {h : ℝ} (hh : 0 < h) {N : ℕ} {t : ℝ} (ht0 : 0 < t) (htN : t ≤ N * h)
    (g : ℝ → ℝ) (y : ℕ → ℝ) {ε : ℝ}
    (hg : ∀ j ∈ Finset.range (N + 1), 0 < hatFn h (gridPt h j) t → |g (y j) - g t| ≤ ε) :
    |∑ j ∈ Finset.range (N + 1), hatFn h (gridPt h j) t * g (y j) - g t| ≤ ε := by
  have h1 := hatFn_sum_one hh ht0 htN
  have e : ∑ j ∈ Finset.range (N + 1), hatFn h (gridPt h j) t * g (y j) - g t =
      ∑ j ∈ Finset.range (N + 1), hatFn h (gridPt h j) t * (g (y j) - g t) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, h1, one_mul]
  rw [e]
  calc |∑ j ∈ Finset.range (N + 1), hatFn h (gridPt h j) t * (g (y j) - g t)|
      ≤ ∑ j ∈ Finset.range (N + 1), |hatFn h (gridPt h j) t * (g (y j) - g t)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range (N + 1), hatFn h (gridPt h j) t * ε := by
        refine Finset.sum_le_sum fun j hj => ?_
        rw [abs_mul, abs_of_nonneg (hatFn_nonneg _ _ _)]
        rcases (hatFn_nonneg h (gridPt h j) t).lt_or_eq with hp | hp
        · exact mul_le_mul_of_nonneg_left (hg j hj hp) hp.le
        · rw [← hp]; simp
    _ = ε := by rw [← Finset.sum_mul, h1, one_mul]

/-- A continuous function is integrable for a finite measure concentrated on `(a, b]`. -/
theorem integrable_of_continuous_ae_Ioc {μ : Measure ℝ} [IsFiniteMeasure μ] {a b : ℝ}
    (hae : ∀ᵐ t ∂μ, t ∈ Ioc a b) {f : ℝ → ℝ} (hf : Continuous f) : Integrable f μ := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    hf.continuousOn
  refine Integrable.of_bound hf.aestronglyMeasurable C ?_
  filter_upwards [hae] with t ht
  exact hC t ⟨ht.1.le, ht.2⟩

/-- The grid mass `∫ λ_j dF`. -/
noncomputable def gridMass (μ : Measure ℝ) (h : ℝ) (j : ℕ) : ℝ :=
  ∫ t, hatFn h (gridPt h j) t ∂μ

/-- The `λ_j`-weighted mean `c_j` of `F` (equal to `x_j` when `m_j = 0`). -/
noncomputable def gridCtr (μ : Measure ℝ) (h : ℝ) (j : ℕ) : ℝ :=
  gridPt h j + (∫ t, hatFn h (gridPt h j) t * (t - gridPt h j) ∂μ) / gridMass μ h j

theorem gridMass_nonneg (μ : Measure ℝ) (h : ℝ) (j : ℕ) : 0 ≤ gridMass μ h j :=
  integral_nonneg fun _ => hatFn_nonneg _ _ _

/-- The grid masses sum to one. -/
theorem gridMass_sum {μ : Measure ℝ} [IsProbabilityMeasure μ] {h : ℝ} (hh : 0 < h) {N : ℕ}
    (hae : ∀ᵐ t ∂μ, t ∈ Ioc 0 (N * h)) :
    ∑ j ∈ Finset.range (N + 1), gridMass μ h j = 1 := by
  unfold gridMass
  rw [← integral_finsetSum _ fun j _ =>
    integrable_of_continuous_ae_Ioc hae (continuous_hatFn _ _)]
  rw [integral_congr_ae (g := fun _ => (1 : ℝ)) ?_]
  · simp
  · filter_upwards [hae] with t ht
    exact hatFn_sum_one hh ht.1 ht.2

/-- `|∫ λ_j(t)(t - x_j) dF| ≤ h m_j`. -/
theorem abs_integral_hat_sub_le {μ : Measure ℝ} [IsProbabilityMeasure μ] {h : ℝ} (hh : 0 < h)
    {N : ℕ} (hae : ∀ᵐ t ∂μ, t ∈ Ioc 0 (N * h)) (j : ℕ) :
    |∫ t, hatFn h (gridPt h j) t * (t - gridPt h j) ∂μ| ≤ h * gridMass μ h j := by
  unfold gridMass
  rw [← integral_const_mul]
  calc |∫ t, hatFn h (gridPt h j) t * (t - gridPt h j) ∂μ|
      ≤ ∫ t, |hatFn h (gridPt h j) t * (t - gridPt h j)| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ t, h * hatFn h (gridPt h j) t ∂μ := by
        refine integral_mono (integrable_of_continuous_ae_Ioc hae (by
          have := continuous_hatFn h (gridPt h j); fun_prop)).abs
          ((integrable_of_continuous_ae_Ioc hae (continuous_hatFn _ _)).const_mul h) fun t => ?_
        rw [abs_mul, abs_of_nonneg (hatFn_nonneg _ _ _)]
        rcases (hatFn_nonneg h (gridPt h j) t).lt_or_eq with hp | hp
        · rw [mul_comm]
          exact mul_le_mul_of_nonneg_right (abs_sub_lt_of_hatFn_pos hh hp).le hp.le
        · rw [← hp]; simp

/-- `m_j c_j = ∫ λ_j(t) t dF`. -/
theorem gridMass_mul_ctr {μ : Measure ℝ} [IsProbabilityMeasure μ] {h : ℝ} (hh : 0 < h)
    {N : ℕ} (hae : ∀ᵐ t ∂μ, t ∈ Ioc 0 (N * h)) (j : ℕ) :
    gridMass μ h j * gridCtr μ h j = ∫ t, hatFn h (gridPt h j) t * t ∂μ := by
  have hb := abs_integral_hat_sub_le hh hae j
  have hi1 : Integrable (fun t => hatFn h (gridPt h j) t * t) μ :=
    integrable_of_continuous_ae_Ioc hae (by have := continuous_hatFn h (gridPt h j); fun_prop)
  have hi2 : Integrable (fun t => hatFn h (gridPt h j) t) μ :=
    integrable_of_continuous_ae_Ioc hae (continuous_hatFn _ _)
  have e : ∫ t, hatFn h (gridPt h j) t * (t - gridPt h j) ∂μ =
      ∫ t, hatFn h (gridPt h j) t * t ∂μ - gridMass μ h j * gridPt h j := by
    unfold gridMass
    rw [← integral_mul_const, ← integral_sub hi1 (hi2.mul_const _)]
    congr 1; funext t; ring
  unfold gridCtr
  rcases (gridMass_nonneg μ h j).lt_or_eq with hm | hm
  · rw [e]; field_simp; ring
  · rw [← hm] at hb ⊢
    rw [mul_zero, abs_nonpos_iff] at hb
    rw [e, ← hm] at hb
    simp only [zero_mul, sub_zero] at hb
    rw [hb, zero_mul]

/-- The weighted mean `c_j` is within `h` of the grid point `x_j`. -/
theorem abs_gridCtr_sub_le {μ : Measure ℝ} [IsProbabilityMeasure μ] {h : ℝ} (hh : 0 < h)
    {N : ℕ} (hae : ∀ᵐ t ∂μ, t ∈ Ioc 0 (N * h)) (j : ℕ) :
    |gridCtr μ h j - gridPt h j| ≤ h := by
  have hb := abs_integral_hat_sub_le hh hae j
  unfold gridCtr
  rw [add_sub_cancel_left, abs_div, abs_of_nonneg (gridMass_nonneg μ h j)]
  rcases (gridMass_nonneg μ h j).lt_or_eq with hm | hm
  · rw [div_le_iff₀ hm]; exact hb
  · rw [← hm, div_zero]; exact hh.le

/-- Expectation under the dilation, as an integral. -/
theorem sum_gridMass_mul {μ : Measure ℝ} [IsProbabilityMeasure μ] {h : ℝ} {N : ℕ}
    (hae : ∀ᵐ t ∂μ, t ∈ Ioc 0 (N * h)) (y : ℕ → ℝ) (g : ℝ → ℝ) :
    ∑ j ∈ Finset.range (N + 1), gridMass μ h j * g (y j) =
      ∫ t, ∑ j ∈ Finset.range (N + 1), hatFn h (gridPt h j) t * g (y j) ∂μ := by
  rw [integral_finsetSum _ fun j _ =>
    (integrable_of_continuous_ae_Ioc hae (continuous_hatFn _ _)).mul_const _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_mul_const]; rfl

/-- **Dilation dominated** (Example 6.D.3, p. 198). For concave `u`, `∑_j w_j u(x_j) ≤ ∫ u dF`. -/
theorem dilation_le {μ : Measure ℝ} [IsProbabilityMeasure μ] {h : ℝ} (hh : 0 < h) {N : ℕ}
    (hae : ∀ᵐ t ∂μ, t ∈ Ioc 0 (N * h)) {U : ℝ → ℝ} (hU : ConcaveOn ℝ univ U) :
    ∑ j ∈ Finset.range (N + 1), gridMass μ h j * U (gridPt h j) ≤ ∫ t, U t ∂μ := by
  have hUc : Continuous U := by
    have := hU.continuousOn_interior
    rw [interior_univ] at this
    exact continuousOn_univ.mp this
  rw [sum_gridMass_mul hae]
  refine integral_mono_ae ?_ (integrable_of_continuous_ae_Ioc hae hUc) ?_
  · exact integrable_finsetSum _ fun j _ =>
      (integrable_of_continuous_ae_Ioc hae (continuous_hatFn _ _)).mul_const _
  · filter_upwards [hae] with t ht
    exact hatFn_sum_concave hh ht.1 ht.2 hU

/-- The dilation keeps the mean: `∑_j w_j x_j = ∫ t dF`. -/
theorem dilation_mean {μ : Measure ℝ} [IsProbabilityMeasure μ] {h : ℝ} (hh : 0 < h) {N : ℕ}
    (hae : ∀ᵐ t ∂μ, t ∈ Ioc 0 (N * h)) :
    ∑ j ∈ Finset.range (N + 1), gridMass μ h j * gridPt h j = ∫ t, t ∂μ := by
  rw [sum_gridMass_mul hae (gridPt h) (fun x => x)]
  apply integral_congr_ae
  filter_upwards [hae] with t ht
  exact hatFn_sum_id hh ht.1 ht.2

/-- **Contraction dominates** (Jensen cell by cell). For nondecreasing concave `u`,
`∫ u dF ≤ ∑_j m_j u(c_j)`. -/
theorem le_contraction {μ : Measure ℝ} [IsProbabilityMeasure μ] {h : ℝ} (hh : 0 < h) {N : ℕ}
    (hae : ∀ᵐ t ∂μ, t ∈ Ioc 0 (N * h)) {U : ℝ → ℝ} (hm : Monotone U)
    (hU : ConcaveOn ℝ univ U) :
    ∫ t, U t ∂μ ≤ ∑ j ∈ Finset.range (N + 1), gridMass μ h j * U (gridCtr μ h j) := by
  have hUc : Continuous U := by
    have := hU.continuousOn_interior
    rw [interior_univ] at this
    exact continuousOn_univ.mp this
  have hsplit : ∫ t, U t ∂μ =
      ∑ j ∈ Finset.range (N + 1), ∫ t, hatFn h (gridPt h j) t * U t ∂μ := by
    rw [← integral_finsetSum _ fun j _ =>
      integrable_of_continuous_ae_Ioc hae (by have := continuous_hatFn h (gridPt h j); fun_prop)]
    apply integral_congr_ae
    filter_upwards [hae] with t ht
    rw [← Finset.sum_mul, hatFn_sum_one hh ht.1 ht.2, one_mul]
  rw [hsplit]
  refine Finset.sum_le_sum fun j _ => ?_
  set c := gridCtr μ h j
  obtain ⟨κ, -, hκ⟩ := concave_supergradient hU (hm.monotoneOn univ)
    (show c ∈ interior univ by rw [interior_univ]; exact mem_univ c)
  have hsup (b : ℝ) : U b ≤ U c + κ * (b - c) := by
    rcases le_total c b with hcb | hcb
    · have := hκ c (mem_univ _) b (mem_univ _) (Or.inl ⟨le_rfl, hcb⟩); linarith
    · have := hκ c (mem_univ _) b (mem_univ _) (Or.inr ⟨hcb, le_rfl⟩); linarith
  have hi1 : Integrable (fun t => hatFn h (gridPt h j) t * t) μ :=
    integrable_of_continuous_ae_Ioc hae (by have := continuous_hatFn h (gridPt h j); fun_prop)
  have hi2 : Integrable (fun t => hatFn h (gridPt h j) t) μ :=
    integrable_of_continuous_ae_Ioc hae (continuous_hatFn _ _)
  calc ∫ t, hatFn h (gridPt h j) t * U t ∂μ
      ≤ ∫ t, (U c - κ * c) * hatFn h (gridPt h j) t + κ * (hatFn h (gridPt h j) t * t) ∂μ := by
        refine integral_mono (integrable_of_continuous_ae_Ioc hae
          (by have := continuous_hatFn h (gridPt h j); fun_prop))
          ((hi2.const_mul _).add (hi1.const_mul _)) fun t => ?_
        have := mul_le_mul_of_nonneg_left (hsup t) (hatFn_nonneg h (gridPt h j) t)
        simp only
        linarith
    _ = gridMass μ h j * U c := by
        rw [integral_add (hi2.const_mul _) (hi1.const_mul _), integral_const_mul,
          integral_const_mul, ← gridMass_mul_ctr hh hae j]
        unfold gridMass
        ring

/-- The contraction keeps the mean: `∑_j m_j c_j = ∫ t dF`. -/
theorem contraction_mean {μ : Measure ℝ} [IsProbabilityMeasure μ] {h : ℝ} (hh : 0 < h) {N : ℕ}
    (hae : ∀ᵐ t ∂μ, t ∈ Ioc 0 (N * h)) :
    ∑ j ∈ Finset.range (N + 1), gridMass μ h j * gridCtr μ h j = ∫ t, t ∂μ := by
  simp only [gridMass_mul_ctr hh hae]
  rw [← integral_finsetSum _ fun j _ =>
    integrable_of_continuous_ae_Ioc hae (by have := continuous_hatFn h (gridPt h j); fun_prop)]
  apply integral_congr_ae
  filter_upwards [hae] with t ht
  rw [← Finset.sum_mul, hatFn_sum_one hh ht.1 ht.2, one_mul]

end MWG.ChoiceUnderUncertainty
