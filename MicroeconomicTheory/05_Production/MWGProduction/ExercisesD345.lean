/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGProduction.ExercisesDE
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.Quasiconvex
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Exercises 5.D.3, 5.D.4(b)-(c) and 5.D.5(a) (MWG, pp. 162-163)

* **Exercise 5.D.3** (Le Chatelier): with long-run cost `c(q)` and short-run cost `c_s(q)`
  (input 1 fixed at its long-run optimal level for `q̄`), `c_s ≥ c` with equality at `q̄`. Then
  the long-run supply response `dq/dp` is at least the short-run one (`exercise_5_D_3`). The
  proof compares the long-run and short-run profit functions: their difference is minimized at
  `p̄`, its derivative is `q(p) - q_s(p)` by Hotelling's lemma (`hotelling_1d`), and a
  second-order necessary condition (`second_order_nonneg`) gives `q'(p̄) - q_s'(p̄) ≥ 0`. The
  inequality is weak in general (`exercise_5_D_3_equal`); `exercise_5_D_3_instance` is a strict
  example.
* **Exercise 5.D.4(b)**: decreasing ray average cost does not imply subadditivity:
  `C(q) = √q₁ + √q₂ + √(√q₁√q₂)` (`exercise_5_D_4b`).
* **Exercise 5.D.4(c)**: decreasing ray average cost and quasiconvexity (with `C` nondecreasing,
  `C(0) = 0`) imply subadditivity (`exercise_5_D_4c`; continuity is not needed); instance
  `C(q) = √(q₁ + q₂)` (`exercise_5_D_4c_instance`).
* **Exercise 5.D.5(a)**: increasing returns imply a nondecreasing average product
  (`exercise_5_D_5a_average`), but not a nondecreasing marginal product: `f(z) = z(1 - e^{-z})`
  (`exercise_5_D_5a_marginal`).
-/

namespace MWG.Production

open MWG.ClassicalDemand MWG.ConsumerChoice Filter Topology

/-! ### Exercise 5.D.3 -/

/-- Hotelling's lemma in one dimension: if `q(p')` maximizes `p'q - c(q)` over `q ≥ 0` for `p'`
near `p` and `q(·)` is continuous at `p`, then the profit `π(p') = p'q(p') - c(q(p'))` has
derivative `q(p)` at `p`. -/
theorem hotelling_1d {c qs : ℝ → ℝ} {p : ℝ}
    (hopt : ∀ᶠ p' in 𝓝 p, 0 ≤ qs p' ∧ ∀ q, 0 ≤ q → p' * q - c q ≤ p' * qs p' - c (qs p'))
    (hc : ContinuousAt qs p) :
    HasDerivAt (fun p' => p' * qs p' - c (qs p')) (qs p) p := by
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  have hp := hopt.self_of_nhds
  have hcl : ∀ᶠ p' in 𝓝 p, |qs p' - qs p| ≤ ε := by
    have := Metric.tendsto_nhds.mp hc.tendsto ε hε
    filter_upwards [this] with p' hp'
    rw [Real.dist_eq] at hp'
    exact hp'.le
  filter_upwards [hopt, hcl] with p' hp' hcl'
  have h1 := hp'.2 (qs p) hp.1
  have h2 := hp.2 (qs p') hp'.1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, smul_eq_mul, abs_le]
  have hab : |(p' - p) * (qs p' - qs p)| ≤ ε * |p' - p| := by
    rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right hcl' (abs_nonneg _)
  rw [abs_le] at hab
  constructor <;> nlinarith [abs_nonneg (p' - p)]

/-- A second-order necessary condition: if `g` has a local minimum at `x₀`, has derivative
`g'(x)` near `x₀`, `g'(x₀) = 0` and `g'` has derivative `d` at `x₀`, then `d ≥ 0`. -/
theorem second_order_nonneg {g g' : ℝ → ℝ} {x₀ d : ℝ} (hmin : ∀ᶠ x in 𝓝 x₀, g x₀ ≤ g x)
    (hg : ∀ᶠ x in 𝓝 x₀, HasDerivAt g (g' x) x) (hg0 : g' x₀ = 0) (hd : HasDerivAt g' d x₀) :
    0 ≤ d := by
  by_contra hneg
  push Not at hneg
  have hsl := hd.tendsto_slope_zero_right
  have hshift : Tendsto (fun t : ℝ => x₀ + t) (𝓝[>] 0) (𝓝 x₀) := by
    have : Tendsto (fun t : ℝ => x₀ + t) (𝓝 0) (𝓝 (x₀ + 0)) :=
      tendsto_const_nhds.add tendsto_id
    rw [add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), t⁻¹ • (g' (x₀ + t) - g' x₀) < 0 ∧
      HasDerivAt g (g' (x₀ + t)) (x₀ + t) ∧ g x₀ ≤ g (x₀ + t) :=
    (hsl.eventually (gt_mem_nhds hneg)).and ((hshift.eventually hg).and (hshift.eventually hmin))
  obtain ⟨ε, hε, hall⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.mp hev
  set b := ε / 2 with hb
  have hb0 : 0 < b := by positivity
  have hbε : b ∈ Set.Ioo 0 ε := ⟨hb0, by linarith⟩
  have hcont : ContinuousOn g (Set.Icc x₀ (x₀ + b)) := by
    intro x hx
    rcases eq_or_lt_of_le hx.1 with h | h
    · rw [← h]; exact hg.self_of_nhds.continuousAt.continuousWithinAt
    · have ht : x - x₀ ∈ Set.Ioo 0 ε := ⟨by linarith, by linarith [hx.2]⟩
      have := (hall ht).2.1
      rw [add_sub_cancel] at this
      exact this.continuousAt.continuousWithinAt
  have hderiv : ∀ x ∈ Set.Ioo x₀ (x₀ + b), HasDerivAt g (g' x) x := by
    intro x hx
    have ht : x - x₀ ∈ Set.Ioo 0 ε := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have := (hall ht).2.1
    rwa [add_sub_cancel] at this
  obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope g g' (by linarith) hcont hderiv
  have hξt : ξ - x₀ ∈ Set.Ioo 0 ε := ⟨by linarith [hξ.1], by linarith [hξ.2]⟩
  have hneg' := (hall hξt).1
  rw [add_sub_cancel, hg0, sub_zero, smul_eq_mul] at hneg'
  have hgξ : g' ξ < 0 := by
    have hpos : 0 < (ξ - x₀)⁻¹ := inv_pos.mpr hξt.1
    by_contra h
    push Not at h
    have := mul_nonneg hpos.le h
    linarith
  have hgb := (hall hbε).2.2
  rw [hξeq, add_sub_cancel_left] at hgξ
  have : g (x₀ + b) - g x₀ < 0 := by
    rw [div_neg_iff] at hgξ
    rcases hgξ with h | h
    · linarith [h.2]
    · linarith [h.1]
  linarith

/-- **Exercise 5.D.3** (MWG, p. 162), Le Chatelier. Let `c(q)` be the long-run cost and `c_s(q)`
the short-run cost with input 1 fixed at its long-run level for `q̄ = q(p̄)`, so that
`c_s ≥ c` on `q ≥ 0` with equality at `q̄` (`shortRun_ge_longRun`, `shortRun_eq_longRun`). If
the long-run and short-run supplies `q(p)`, `q_s(p)` maximize profits near `p̄`, coincide at
`p̄`, are continuous near `p̄` and differentiable at `p̄`, then `q_s'(p̄) ≤ q'(p̄)`: output
responds at least as much in the long run as in the short run. -/
theorem exercise_5_D_3 {c cs qL qS : ℝ → ℝ} {p dL dS : ℝ}
    (hle : ∀ q, 0 ≤ q → c q ≤ cs q) (heq : cs (qL p) = c (qL p)) (hsame : qS p = qL p)
    (hL : ∀ᶠ p' in 𝓝 p, 0 ≤ qL p' ∧ ∀ q, 0 ≤ q → p' * q - c q ≤ p' * qL p' - c (qL p'))
    (hS : ∀ᶠ p' in 𝓝 p, 0 ≤ qS p' ∧ ∀ q, 0 ≤ q → p' * q - cs q ≤ p' * qS p' - cs (qS p'))
    (hcL : ∀ᶠ p' in 𝓝 p, ContinuousAt qL p') (hcS : ∀ᶠ p' in 𝓝 p, ContinuousAt qS p')
    (hdL : HasDerivAt qL dL p) (hdS : HasDerivAt qS dS p) : dS ≤ dL := by
  set φ : ℝ → ℝ := fun p' => (p' * qL p' - c (qL p')) - (p' * qS p' - cs (qS p')) with hφ
  have hmin : ∀ᶠ x in 𝓝 p, φ p ≤ φ x := by
    filter_upwards [hL, hS] with x hx hx'
    have hφp : φ p = 0 := by simp only [hφ, hsame, heq]; ring
    rw [hφp]
    have h1 := hx.2 (qS x) hx'.1
    have h2 := hle (qS x) hx'.1
    simp only [hφ]
    linarith
  have hgrad : ∀ᶠ x in 𝓝 p, HasDerivAt φ (qL x - qS x) x := by
    filter_upwards [hL.eventually_nhds, hS.eventually_nhds, hcL, hcS] with x hx hx' hcx hcx'
    exact (hotelling_1d hx hcx).sub (hotelling_1d hx' hcx')
  have := second_order_nonneg hmin hgrad (by rw [hsame, sub_self]) (hdL.sub hdS)
  linarith

/-- **Exercise 5.D.3** (MWG, p. 162): a strict instance. With `c(q) = q²` and
`c_s(q) = q² + (q - 1)²` (`c_s ≥ c`, equal at `q̄ = 1`), at `p̄ = 2` the supplies are
`q(p) = p/2` and `q_s(p) = (p + 2)/4`, and `q_s' = 1/4 < 1/2 = q'`. -/
theorem exercise_5_D_3_instance :
    (∀ q : ℝ, 0 ≤ q → q ^ 2 ≤ q ^ 2 + (q - 1) ^ 2) ∧
      (∀ᶠ p' in 𝓝 (2 : ℝ), 0 ≤ p' / 2 ∧
        ∀ q : ℝ, 0 ≤ q → p' * q - q ^ 2 ≤ p' * (p' / 2) - (p' / 2) ^ 2) ∧
      (∀ᶠ p' in 𝓝 (2 : ℝ), 0 ≤ (p' + 2) / 4 ∧ ∀ q : ℝ, 0 ≤ q →
        p' * q - (q ^ 2 + (q - 1) ^ 2) ≤
          p' * ((p' + 2) / 4) - (((p' + 2) / 4) ^ 2 + ((p' + 2) / 4 - 1) ^ 2)) ∧
      HasDerivAt (fun p' : ℝ => p' / 2) (1 / 2) 2 ∧
      HasDerivAt (fun p' : ℝ => (p' + 2) / 4) (1 / 4) 2 ∧ (1 / 4 : ℝ) < 1 / 2 := by
  have hpos : ∀ᶠ p' in 𝓝 (2 : ℝ), 0 < p' := lt_mem_nhds (by norm_num)
  refine ⟨fun q _ => by nlinarith [sq_nonneg (q - 1)], ?_, ?_, ?_, ?_, by norm_num⟩
  · filter_upwards [hpos] with p' hp'
    exact ⟨by positivity, fun q _ => by nlinarith [sq_nonneg (q - p' / 2)]⟩
  · filter_upwards [hpos] with p' hp'
    exact ⟨by positivity, fun q _ => by nlinarith [sq_nonneg (q - (p' + 2) / 4)]⟩
  · simpa using (hasDerivAt_id (2 : ℝ)).div_const 2
  · simpa using ((hasDerivAt_id (2 : ℝ)).add_const 2).div_const 4

/-- **Exercise 5.D.3** (MWG, p. 162): the response is only weakly larger in general. If fixing
input 1 does not raise costs (`c_s = c`, e.g. when input 1 is not used), the short-run and
long-run supplies coincide: for `c(q) = q²`, both are `p/2`, with equal derivatives. -/
theorem exercise_5_D_3_equal :
    (∀ᶠ p' in 𝓝 (2 : ℝ), 0 ≤ p' / 2 ∧
        ∀ q : ℝ, 0 ≤ q → p' * q - q ^ 2 ≤ p' * (p' / 2) - (p' / 2) ^ 2) ∧
      HasDerivAt (fun p' : ℝ => p' / 2) (1 / 2) 2 := by
  have hpos : ∀ᶠ p' in 𝓝 (2 : ℝ), 0 < p' := lt_mem_nhds (by norm_num)
  refine ⟨?_, by simpa using (hasDerivAt_id (2 : ℝ)).div_const 2⟩
  filter_upwards [hpos] with p' hp'
  exact ⟨by positivity, fun q _ => by nlinarith [sq_nonneg (q - p' / 2)]⟩

/-! ### Exercise 5.D.4(b)-(c) -/

variable {M : ℕ}

/-- **Exercise 5.D.4** (MWG, p. 163). `C` is subadditive: no split of `q = Σ_j q_j` among
`J ≥ 1` firms has `Σ_j C(q_j) < C(q)`. -/
def Subadditive (C : (Fin M → ℝ) → ℝ) : Prop :=
  ∀ (J : ℕ), 0 < J → ∀ qs : Fin J → Fin M → ℝ, (∀ j, 0 ≤ qs j) → C (∑ j, qs j) ≤ ∑ j, C (qs j)

/-- **Exercise 5.D.4(b)** (MWG, p. 163). Decreasing ray average cost: `C(q) > C(kq)/k` for all
`k > 1` and `q ∈ ℝ^M_+`, `q ≠ 0` (at `q = 0` the condition would need `C(0) > 0`, against
`C(0) = 0` in (c)). -/
def DecreasingRayAC (C : (Fin M → ℝ) → ℝ) : Prop :=
  ∀ q : Fin M → ℝ, 0 ≤ q → q ≠ 0 → ∀ k : ℝ, 1 < k → C (k • q) / k < C q

/-- The cost function `C(q) = √q₁ + √q₂ + √(√q₁ √q₂)` of Exercise 5.D.4(b). -/
noncomputable def cost4b (q : Fin 2 → ℝ) : ℝ :=
  Real.sqrt (q 0) + Real.sqrt (q 1) + Real.sqrt (Real.sqrt (q 0) * Real.sqrt (q 1))

/-- **Exercise 5.D.4(b)** (MWG, p. 163). `C(q) = √q₁ + √q₂ + √(√q₁√q₂)` is continuous,
nondecreasing, has `C(0) = 0` and decreasing ray average cost (it is homogeneous of degree
`1/2`), but is not subadditive: producing `(1, 0)` and `(0, 1)` in separate firms costs
`2 < 3 = C(1, 1)`. -/
theorem exercise_5_D_4b :
    Continuous cost4b ∧ (∀ x y : Fin 2 → ℝ, x ≤ y → cost4b x ≤ cost4b y) ∧ cost4b 0 = 0 ∧
      DecreasingRayAC cost4b ∧ ¬ Subadditive cost4b := by
  refine ⟨by unfold cost4b; fun_prop, fun x y hxy => ?_, by simp [cost4b], ?_, ?_⟩
  · have h0 := Real.sqrt_le_sqrt (hxy 0)
    have h1 := Real.sqrt_le_sqrt (hxy 1)
    have h2 : Real.sqrt (x 0) * Real.sqrt (x 1) ≤ Real.sqrt (y 0) * Real.sqrt (y 1) :=
      mul_le_mul h0 h1 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    unfold cost4b
    linarith [Real.sqrt_le_sqrt h2]
  · intro q hq hq0 k hk
    have hk0 : 0 < k := by linarith
    have hsk : Real.sqrt (k * q 0) = Real.sqrt k * Real.sqrt (q 0) := Real.sqrt_mul hk0.le _
    have hsk1 : Real.sqrt (k * q 1) = Real.sqrt k * Real.sqrt (q 1) := Real.sqrt_mul hk0.le _
    have hkk : Real.sqrt k * Real.sqrt k = k := Real.mul_self_sqrt hk0.le
    have hs3 : Real.sqrt (Real.sqrt k * Real.sqrt (q 0) * (Real.sqrt k * Real.sqrt (q 1))) =
        Real.sqrt k * Real.sqrt (Real.sqrt (q 0) * Real.sqrt (q 1)) := by
      rw [show Real.sqrt k * Real.sqrt (q 0) * (Real.sqrt k * Real.sqrt (q 1)) =
        k * (Real.sqrt (q 0) * Real.sqrt (q 1)) by
          linear_combination (Real.sqrt (q 0) * Real.sqrt (q 1)) * hkk]
      exact Real.sqrt_mul hk0.le _
    have hC : cost4b (k • q) = Real.sqrt k * cost4b q := by
      simp only [cost4b, Pi.smul_apply, smul_eq_mul, hsk, hsk1, hs3]
      ring
    have hpos : 0 < cost4b q := by
      have : q 0 ≠ 0 ∨ q 1 ≠ 0 := by
        by_contra h
        push Not at h
        exact hq0 (funext fun i => by fin_cases i <;> simp [h.1, h.2])
      have n0 := Real.sqrt_nonneg (q 0)
      have n1 := Real.sqrt_nonneg (q 1)
      have n2 := Real.sqrt_nonneg (Real.sqrt (q 0) * Real.sqrt (q 1))
      unfold cost4b
      rcases this with h | h
      · have := Real.sqrt_pos.mpr (lt_of_le_of_ne (hq 0) (Ne.symm h)); linarith
      · have := Real.sqrt_pos.mpr (lt_of_le_of_ne (hq 1) (Ne.symm h)); linarith
    have hsk1' : 1 < Real.sqrt k := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_lt_sqrt zero_le_one hk
    rw [hC, div_lt_iff₀ hk0]
    have : 0 < Real.sqrt k := by linarith
    have h1 := mul_lt_mul_of_pos_left hsk1' (mul_pos this hpos)
    have h2 : Real.sqrt k * cost4b q * Real.sqrt k = cost4b q * k := by
      linear_combination cost4b q * hkk
    linarith
  · intro hsub
    have h := hsub 2 (by norm_num) ![![1, 0], ![0, 1]] (fun j => by
      fin_cases j <;> intro i <;> fin_cases i <;> simp)
    have hsum : (∑ j, (![![1, 0], ![0, 1]] : Fin 2 → Fin 2 → ℝ) j) = ![1, 1] := by
      funext i; fin_cases i <;> simp [Fin.sum_univ_two]
    rw [hsum, Fin.sum_univ_two] at h
    simp [cost4b] at h
    norm_num at h

/-- **Exercise 5.D.4(c)** (MWG, p. 163). If `C` is nondecreasing on `ℝ^M_+`, `C(0) = 0`, and `C`
has decreasing ray average cost and is quasiconvex on `ℝ^M_+`, then `C` is subadditive. (The
book's continuity hypothesis is not needed.) Proof: with `S = Σ_j C(q_j)`,
`q = Σ_j (C(q_j)/S)·(S/C(q_j)) q_j` is a convex combination of points of the sublevel set
`{C ≤ S}` (by decreasing ray average cost), which is convex. -/
theorem exercise_5_D_4c {C : (Fin M → ℝ) → ℝ}
    (hmono : ∀ x y : Fin M → ℝ, 0 ≤ x → x ≤ y → C x ≤ C y) (h0 : C 0 = 0)
    (hqc : QuasiconvexOn ℝ {x : Fin M → ℝ | 0 ≤ x} C) (hdrac : DecreasingRayAC C) :
    Subadditive C := by
  intro J hJ qs hqs
  have hCnn : ∀ x : Fin M → ℝ, 0 ≤ x → 0 ≤ C x := fun x hx => h0 ▸ hmono 0 x le_rfl hx
  have hCpos : ∀ x : Fin M → ℝ, 0 ≤ x → x ≠ 0 → 0 < C x := by
    intro x hx hx0
    have h2 := hdrac x hx hx0 2 one_lt_two
    have : 0 ≤ C ((2 : ℝ) • x) / 2 := div_nonneg (hCnn _ (smul_nonneg zero_le_two hx))
      zero_le_two
    linarith
  set S := ∑ j, C (qs j) with hS
  have hSnn : 0 ≤ S := Finset.sum_nonneg fun j _ => hCnn _ (hqs j)
  have hqnn : 0 ≤ ∑ j, qs j := Finset.sum_nonneg fun j _ => hqs j
  rcases hSnn.lt_or_eq with hSpos | hS0
  · -- the convex combination
    set lam : Fin J → ℝ := fun j => C (qs j) / S with hlam
    set x : Fin J → Fin M → ℝ := fun j => (S / C (qs j)) • qs j with hx
    have hlam0 : ∀ j ∈ Finset.univ, 0 ≤ lam j := fun j _ => div_nonneg (hCnn _ (hqs j)) hSpos.le
    have hlam1 : ∑ j ∈ Finset.univ, lam j = 1 := by
      rw [hlam, ← Finset.sum_div, ← hS, div_self hSpos.ne']
    have hcomb : ∑ j ∈ Finset.univ, lam j • x j = ∑ j, qs j := by
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hj : qs j = 0
      · simp [hlam, hx, hj]
      · have hc := hCpos _ (hqs j) hj
        simp only [hlam, hx, smul_smul]
        rw [show C (qs j) / S * (S / C (qs j)) = 1 by field_simp, one_smul]
    have hmem : ∀ j ∈ Finset.univ, x j ∈ {y | y ∈ {x : Fin M → ℝ | 0 ≤ x} ∧ C y ≤ S} := by
      intro j _
      by_cases hj : qs j = 0
      · refine ⟨by simp [hx, hj], ?_⟩
        simp only [hx, hj, smul_zero, h0]
        exact hSnn
      · have hc := hCpos _ (hqs j) hj
        have hle : C (qs j) ≤ S :=
          Finset.single_le_sum (fun i _ => hCnn _ (hqs i)) (Finset.mem_univ j)
        have hk : 1 ≤ S / C (qs j) := by rw [le_div_iff₀ hc]; linarith
        refine ⟨smul_nonneg (by linarith) (hqs j), ?_⟩
        rcases hk.lt_or_eq with hk1 | hk1
        · have := hdrac (qs j) (hqs j) hj _ hk1
          rw [div_lt_iff₀ (by linarith)] at this
          have e : C (qs j) * (S / C (qs j)) = S := by field_simp
          simp only [hx]
          linarith
        · simp only [hx, ← hk1, one_smul]
          exact hle
    have := (hqc S).sum_mem hlam0 hlam1 hmem
    rw [hcomb] at this
    exact this.2
  · -- all costs zero: then all `q_j = 0`
    have hall : ∀ j, qs j = 0 := by
      intro j
      by_contra hj
      have hc := hCpos _ (hqs j) hj
      have hle : C (qs j) ≤ S :=
        Finset.single_le_sum (fun i _ => hCnn _ (hqs i)) (Finset.mem_univ j)
      linarith
    have : ∑ j, qs j = 0 := Finset.sum_eq_zero fun j _ => hall j
    rw [this, h0]
    exact hSnn

/-- **Exercise 5.D.4(c)** (MWG, p. 163): the hypotheses are met by `C(q) = √(q₁ + q₂)`. -/
theorem exercise_5_D_4c_instance :
    let C : (Fin 2 → ℝ) → ℝ := fun q => Real.sqrt (q 0 + q 1)
    (∀ x y : Fin 2 → ℝ, 0 ≤ x → x ≤ y → C x ≤ C y) ∧ C 0 = 0 ∧
      QuasiconvexOn ℝ {x : Fin 2 → ℝ | 0 ≤ x} C ∧ DecreasingRayAC C ∧ Subadditive C := by
  intro C
  have hmono : ∀ x y : Fin 2 → ℝ, 0 ≤ x → x ≤ y → C x ≤ C y :=
    fun x y _ hxy => Real.sqrt_le_sqrt (add_le_add (hxy 0) (hxy 1))
  have h0 : C 0 = 0 := by simp [C]
  have hqc : QuasiconvexOn ℝ {x : Fin 2 → ℝ | 0 ≤ x} C := by
    intro r
    rintro x ⟨hx, hxr⟩ y ⟨hy, hyr⟩ a b ha hb hab
    refine ⟨fun i => ?_, ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      exact add_nonneg (mul_nonneg ha (hx i)) (mul_nonneg hb (hy i))
    · simp only [C, Real.sqrt_le_iff] at hxr hyr ⊢
      refine ⟨hxr.1, ?_⟩
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      nlinarith [hxr.2, hyr.2]
  have hdrac : DecreasingRayAC C := by
    intro q hq hq0 k hk
    have hk0 : 0 < k := by linarith
    have q0 : 0 ≤ q 0 := hq 0
    have q1 : 0 ≤ q 1 := hq 1
    have hs : 0 < q 0 + q 1 := by
      rcases (add_nonneg q0 q1).lt_or_eq with h | h
      · exact h
      · exfalso
        have a0 : q 0 = 0 := by linarith
        have a1 : q 1 = 0 := by linarith
        exact hq0 (funext fun i => by fin_cases i <;> simp [a0, a1])
    have e : C (k • q) = Real.sqrt k * C q := by
      simp only [C, Pi.smul_apply, smul_eq_mul, ← mul_add]
      exact Real.sqrt_mul hk0.le _
    have hkk : Real.sqrt k * Real.sqrt k = k := Real.mul_self_sqrt hk0.le
    have hsk1 : 1 < Real.sqrt k := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_lt_sqrt zero_le_one hk
    have hC : 0 < C q := Real.sqrt_pos.mpr hs
    rw [e, div_lt_iff₀ hk0]
    have h1 := mul_lt_mul_of_pos_left hsk1 (mul_pos (by linarith : 0 < Real.sqrt k) hC)
    have h2 : Real.sqrt k * C q * Real.sqrt k = C q * k := by
      linear_combination C q * hkk
    linarith
  exact ⟨hmono, h0, hqc, hdrac, exercise_5_D_4c hmono h0 hqc hdrac⟩

/-! ### Exercise 5.D.5(a) -/

/-- **Exercise 5.D.5(a)** (MWG, p. 163), average product. If `f` has increasing returns to
scale (`f(αz) ≥ αf(z)` for `α ≥ 1`, `z ≥ 0`), the average product `f(z)/z` is nondecreasing on
`z > 0`. (Differentiability is not needed.) -/
theorem exercise_5_D_5a_average {f : ℝ → ℝ}
    (hirs : ∀ z, 0 ≤ z → ∀ α : ℝ, 1 ≤ α → α * f z ≤ f (α * z)) {z z' : ℝ} (hz : 0 < z)
    (hzz : z ≤ z') : f z / z ≤ f z' / z' := by
  have hz' : 0 < z' := lt_of_lt_of_le hz hzz
  have h := hirs z hz.le (z' / z) (by rw [le_div_iff₀ hz]; linarith)
  rw [div_mul_cancel₀ _ hz.ne'] at h
  rw [div_le_div_iff₀ hz hz']
  have : z' / z * f z * z = z' * f z := by field_simp
  nlinarith

/-- The production function `f(z) = z(1 - e^{-z})` of Exercise 5.D.5(a). -/
noncomputable def prod5a (z : ℝ) : ℝ := z * (1 - Real.exp (-z))

/-- **Exercise 5.D.5(a)** (MWG, p. 163), marginal product. `f(z) = z(1 - e^{-z})` is
differentiable with `f'(z) = 1 - e^{-z} + ze^{-z}` and has (strictly) increasing returns to
scale, but its marginal product falls between `z = 2` and `z = 3`:
`f'(3) = 1 + 2e^{-3} < 1 + e^{-2} = f'(2)`. -/
theorem exercise_5_D_5a_marginal :
    (∀ z : ℝ, HasDerivAt prod5a (1 - Real.exp (-z) + z * Real.exp (-z)) z) ∧
      (∀ z, 0 ≤ z → ∀ α : ℝ, 1 ≤ α → α * prod5a z ≤ prod5a (α * z)) ∧
      (∀ z, 0 < z → ∀ α : ℝ, 1 < α → α * prod5a z < prod5a (α * z)) ∧
      1 - Real.exp (-3) + 3 * Real.exp (-3) < 1 - Real.exp (-2) + 2 * Real.exp (-2) := by
  refine ⟨fun z => ?_, fun z hz α hα => ?_, fun z hz α hα => ?_, ?_⟩
  · have h := (hasDerivAt_id z).mul (((hasDerivAt_id z).neg.exp).const_sub 1)
    convert h using 1
    · funext x; simp [prod5a]
    · simp
  · have : Real.exp (-(α * z)) ≤ Real.exp (-z) :=
      Real.exp_le_exp.mpr (by nlinarith)
    unfold prod5a
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ α) hz]
  · have : Real.exp (-(α * z)) < Real.exp (-z) :=
      Real.exp_lt_exp.mpr (by nlinarith)
    unfold prod5a
    nlinarith [mul_pos (by linarith : (0 : ℝ) < α) hz]
  · have he : 2 < Real.exp 1 := by
      have := Real.add_one_lt_exp (one_ne_zero : (1 : ℝ) ≠ 0)
      linarith
    have h2 : Real.exp (-2) = Real.exp 1 * Real.exp (-3) := by
      rw [← Real.exp_add]; norm_num
    have h3 := Real.exp_pos (-3)
    rw [h2]
    nlinarith

end MWG.Production
