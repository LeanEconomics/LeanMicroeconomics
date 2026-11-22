/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGEquilibriumTime.Production
import MWGGeneralEquilibriumExamples.FactorMarkets

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
