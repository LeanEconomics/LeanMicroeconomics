/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGChoiceUnderUncertainty.WealthEffects
import MWGChoiceUnderUncertainty.InsuranceAssets
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Comparative statics of the demand for a risky asset

MWG, Section 6.C, pp. 192-194: "more risk averse than" is a partial ordering that is far from
complete, Example 6.C.2 continued (a more risk-averse investor invests less in the risky
asset), and Exercises 6.C.8 (under decreasing absolute risk aversion the risky asset is a
normal good) and 6.C.11 (relative risk aversion and the proportion invested).

MWG's argument differentiates under the integral and compares first-order conditions at an
interior optimum. We prove the comparison without differentiability or interiority: if
`u₂ = ψ ∘ u₁` with `ψ` concave and increasing and `α₁*` is optimal for `u₁`, then `u₂` never
gains by investing more than `α₁*` (`invest_compare`); with a unique optimum for `u₂` this
gives `α₂* ≤ α₁*`. The key step is a supergradient `κ ≥ 0` of `ψ` at `u₁(w)`.
-/

namespace MWG.ChoiceUnderUncertainty

open MeasureTheory Filter Topology Set

/-- A concave, nondecreasing `ψ` has a supergradient `κ ≥ 0` at an interior point `m`, and the
increments of `ψ` moving away from `m` are at most `κ` times the increments of the argument. -/
theorem concave_supergradient {ψ : ℝ → ℝ} {J : Set ℝ} (hψ : ConcaveOn ℝ J ψ)
    (hmono : MonotoneOn ψ J) {m : ℝ} (hmi : m ∈ interior J) :
    ∃ κ, 0 ≤ κ ∧ ∀ a ∈ J, ∀ b ∈ J, ((m ≤ a ∧ a ≤ b) ∨ (b ≤ a ∧ a ≤ m)) →
      ψ b - ψ a ≤ κ * (b - a) := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior m hmi
  have hin (y : ℝ) (hy : |y - m| < ε) : y ∈ J :=
    interior_subset (hball (by rw [Metric.mem_ball, Real.dist_eq]; exact hy))
  have hmJ : m ∈ J := interior_subset hmi
  set yR := m + ε / 2
  set yL := m - ε / 2
  have hyR : yR ∈ J := by
    apply hin
    simp only [yR]
    rw [show m + ε / 2 - m = ε / 2 by ring, abs_of_pos (by linarith)]
    linarith
  have hyL : yL ∈ J := by
    apply hin
    simp only [yL]
    rw [show m - ε / 2 - m = -(ε / 2) by ring, abs_neg, abs_of_pos (by linarith)]
    linarith
  set R := {s | ∃ y ∈ J, m < y ∧ s = (ψ y - ψ m) / (y - m)}
  have hRne : R.Nonempty := ⟨_, yR, hyR, by simp only [yR]; linarith, rfl⟩
  have hRbdd : BddAbove R := by
    refine ⟨(ψ m - ψ yL) / (m - yL), ?_⟩
    rintro s ⟨y, hy, hmy, rfl⟩
    exact hψ.slope_anti_adjacent hyL hy (by simp only [yL]; linarith) hmy
  set κ := sSup R
  have hκ0 : 0 ≤ κ := by
    have h1 : (ψ yR - ψ m) / (yR - m) ∈ R := ⟨yR, hyR, by simp only [yR]; linarith, rfl⟩
    refine le_trans ?_ (le_csSup hRbdd h1)
    exact div_nonneg (sub_nonneg.mpr (hmono hmJ hyR (by simp only [yR]; linarith)))
      (by simp only [yR]; linarith)
  have hsup (y : ℝ) (hy : y ∈ J) : ψ y ≤ ψ m + κ * (y - m) := by
    rcases lt_trichotomy m y with hmy | rfl | hym
    · have : (ψ y - ψ m) / (y - m) ≤ κ := le_csSup hRbdd ⟨y, hy, hmy, rfl⟩
      rw [div_le_iff₀ (by linarith)] at this
      linarith
    · simp
    · have : κ ≤ (ψ m - ψ y) / (m - y) := by
        apply csSup_le hRne
        rintro s ⟨y', hy', hmy', rfl⟩
        exact hψ.slope_anti_adjacent hy hy' hym hmy'
      rw [le_div_iff₀ (by linarith)] at this
      linarith
  refine ⟨κ, hκ0, fun a ha b hb hab => ?_⟩
  have key : ψ b - ψ a ≤ κ * (b - a) := by
    by_cases hbm : b = m
    · have : a = m := by
        rcases hab with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
      subst this; rw [hbm]; simp
    · set lam := (b - a) / (b - m)
      have hlam0 : 0 ≤ lam := by
        rcases hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact div_nonneg (by linarith) (by
            rcases eq_or_lt_of_le (h1.trans h2) with h | h
            · exact absurd h.symm hbm
            · linarith)
        · exact div_nonneg_of_nonpos (by linarith) (by linarith)
      have hlam1 : lam ≤ 1 := by
        rcases hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · have hbm' : 0 < b - m := lt_of_le_of_ne (by linarith) (fun h => hbm (by linarith))
          rw [div_le_one hbm']; linarith
        · have hbm' : b - m < 0 := lt_of_le_of_ne (by linarith) (fun h => hbm (by linarith))
          rw [div_le_one_of_neg hbm']; linarith
      have hbm' : b - m ≠ 0 := sub_ne_zero.mpr hbm
      have hcomb : lam • m + (1 - lam) • b = a := by
        simp only [smul_eq_mul, lam]; field_simp; ring
      have hc := hψ.2 hmJ hb hlam0 (sub_nonneg.mpr hlam1) (by ring)
      rw [hcomb] at hc
      simp only [smul_eq_mul] at hc
      have h1 : ψ b - ψ a ≤ lam * (ψ b - ψ m) := by linarith
      have h2 : lam * (ψ b - ψ m) ≤ lam * (κ * (b - m)) :=
        mul_le_mul_of_nonneg_left (by linarith [hsup b hb]) hlam0
      have h3 : lam * (κ * (b - m)) = κ * (b - a) := by
        simp only [lam]; field_simp
      linarith
  exact key

/-- `u₁(w)` lies in the interior of `u₁(S)` for an open interval `S ∋ w`. -/
theorem mem_interior_image {S : Set ℝ} (hS : Convex ℝ S) (ho : IsOpen S) {u : ℝ → ℝ}
    (hc : ContinuousOn u S) (hi : StrictMonoOn u S) {w : ℝ} (hw : w ∈ S) :
    u w ∈ interior (u '' S) := by
  obtain ⟨a', b', -, -, -, himg, hlo, hhi⟩ :=
    exists_Icc_image_nhds hS ho hc hi (a := w) (b := w) (by simpa using hw) le_rfl
  exact interior_mono himg (by rw [interior_Icc]; exact ⟨hlo, hhi⟩)

/-- **Example 6.C.2 continued** (MWG, p. 192), the comparison step. If `u₂ = ψ ∘ u₁` with `ψ`
concave and increasing, and `α₁ ≥ 0` maximizes `∫ u₁(w + α(z - 1)) dF` on a set containing
`[α₁, β]`, then `∫ u₂(w + α(z - 1)) dF ≤ ∫ u₂(w + α₁(z - 1)) dF` for all `α ∈ [α₁, β]`. -/
theorem invest_compare {S : Set ℝ} (hS : Convex ℝ S) (ho : IsOpen S) {u₁ u₂ : ℝ → ℝ}
    (c1 : ContinuousOn u₁ S) (c2 : ContinuousOn u₂ S) (h1 : StrictMonoOn u₁ S)
    (h : MoreRiskAverseII S u₁ u₂) {T : Set ℝ} {μ : Measure ℝ} (hμ : IsMoneyLottery T μ)
    {w α₁ β : ℝ} (hw : w ∈ S) (hα0 : 0 ≤ α₁)
    (hdom : ∀ z ∈ T, ∀ γ ∈ Icc α₁ β, w + γ * (z - 1) ∈ S)
    (hopt : ∀ γ ∈ Icc α₁ β, assetEU u₁ w μ γ ≤ assetEU u₁ w μ α₁) :
    ∀ γ ∈ Icc α₁ β, assetEU u₂ w μ γ ≤ assetEU u₂ w μ α₁ := by
  obtain ⟨ψ, hψi, hψ, he⟩ := h
  obtain ⟨κ, hκ, hstep⟩ := concave_supergradient hψ hψi.monotoneOn
    (mem_interior_image hS ho c1 h1 hw)
  intro γ hγ
  have hα1 : α₁ ∈ Icc α₁ β := ⟨le_rfl, hγ.1.trans hγ.2⟩
  have hint (u : ℝ → ℝ) (hu : ContinuousOn u S) (g : ℝ) (hg : g ∈ Icc α₁ β) :
      Integrable (fun z => u (w + g * (z - 1))) μ :=
    hμ.integrable (u := fun z => u (w + g * (z - 1)))
      (hu.comp (by fun_prop) fun z hz => hdom z hz g hg)
  obtain ⟨a, b, hab, hae⟩ := hμ.ae_mem
  have hpt : ∀ᵐ z ∂μ, u₂ (w + γ * (z - 1)) - u₂ (w + α₁ * (z - 1)) ≤
      κ * (u₁ (w + γ * (z - 1)) - u₁ (w + α₁ * (z - 1))) := by
    filter_upwards [hae] with z hz
    have hzT := hab hz
    have hS1 := hdom z hzT α₁ hα1
    have hSγ := hdom z hzT γ hγ
    rw [he _ hS1, he _ hSγ]
    apply hstep _ (mem_image_of_mem _ hS1) _ (mem_image_of_mem _ hSγ)
    rcases le_total 1 z with hz1 | hz1
    · left
      constructor
      · exact h1.monotoneOn hw hS1 (by nlinarith)
      · exact h1.monotoneOn hS1 hSγ (by nlinarith [hγ.1])
    · right
      constructor
      · exact h1.monotoneOn hSγ hS1 (by nlinarith [hγ.1])
      · exact h1.monotoneOn hS1 hw (by nlinarith)
  have hI : ∫ z, (u₂ (w + γ * (z - 1)) - u₂ (w + α₁ * (z - 1))) ∂μ ≤
      ∫ z, κ * (u₁ (w + γ * (z - 1)) - u₁ (w + α₁ * (z - 1))) ∂μ :=
    integral_mono_ae ((hint u₂ c2 γ hγ).sub (hint u₂ c2 α₁ hα1))
    (((hint u₁ c1 γ hγ).sub (hint u₁ c1 α₁ hα1)).const_mul κ) hpt
  rw [integral_sub (hint u₂ c2 γ hγ) (hint u₂ c2 α₁ hα1), integral_const_mul,
    integral_sub (hint u₁ c1 γ hγ) (hint u₁ c1 α₁ hα1)] at hI
  have hle := hopt γ hγ
  unfold assetEU at hle ⊢
  nlinarith

/-- **Example 6.C.2 continued** (MWG, p. 192). If `u₂` is more risk averse than `u₁` (a concave
transformation, condition (ii) of Proposition 6.C.2), `α₁*` is optimal for `u₁` and `α₂*` is
the unique optimum for `u₂` on `[0, w]`, then `α₂* ≤ α₁*`. -/
theorem example_6_C_2_continued {S : Set ℝ} (hS : Convex ℝ S) (ho : IsOpen S)
    {u₁ u₂ : ℝ → ℝ} (c1 : ContinuousOn u₁ S) (c2 : ContinuousOn u₂ S)
    (h1 : StrictMonoOn u₁ S) (h : MoreRiskAverseII S u₁ u₂) {T : Set ℝ} {μ : Measure ℝ}
    (hμ : IsMoneyLottery T μ) {w α₁ α₂ : ℝ} (hw : w ∈ S)
    (hdom : ∀ z ∈ T, ∀ γ ∈ Icc 0 w, w + γ * (z - 1) ∈ S) (hα₁ : α₁ ∈ Icc 0 w)
    (hopt₁ : ∀ γ ∈ Icc 0 w, assetEU u₁ w μ γ ≤ assetEU u₁ w μ α₁) (hα₂ : α₂ ∈ Icc 0 w)
    (hopt₂ : ∀ γ ∈ Icc 0 w, assetEU u₂ w μ γ ≤ assetEU u₂ w μ α₂)
    (huniq : ∀ γ ∈ Icc 0 w, assetEU u₂ w μ γ = assetEU u₂ w μ α₂ → γ = α₂) : α₂ ≤ α₁ := by
  by_contra hlt
  have hlt : α₁ < α₂ := lt_of_not_ge hlt
  have hsub : Icc α₁ w ⊆ Icc 0 w := Icc_subset_Icc_left hα₁.1
  have := invest_compare hS ho c1 c2 h1 h hμ hw hα₁.1
    (fun z hz γ hγ => hdom z hz γ (hsub hγ)) (fun γ hγ => hopt₁ γ (hsub hγ)) α₂
    ⟨hlt.le, hα₂.2⟩
  have heq := le_antisymm (hopt₂ α₁ hα₁) this
  exact absurd (huniq α₁ hα₁ heq) hlt.ne

/-- **p. 192**. "More risk averse than" (condition (i)) is transitive. -/
theorem moreRiskAverseI_trans {S : Set ℝ} {u₁ u₂ u₃ : ℝ → ℝ} (h12 : MoreRiskAverseI S u₁ u₂)
    (h23 : MoreRiskAverseI S u₂ u₃) : MoreRiskAverseI S u₁ u₃ :=
  fun x hx => (h12 x hx).trans (h23 x hx)

/-- The Arrow-Pratt coefficient of `ln` is `1/x` on `x > 0`. -/
theorem arrowPratt_log {x : ℝ} (hx : 0 < x) : arrowPratt Real.log x = 1 / x := by
  unfold arrowPratt
  rw [Real.deriv_log', deriv_inv]
  field_simp

/-- **p. 192**. The ordering is far from complete: on `x > 0`, `u₁(x) = -e^{-x}` (with
`r_A = 1`) and `u₂ = ln` (with `r_A = 1/x`) are not comparable in either direction. -/
theorem moreRiskAverse_not_complete :
    ¬MoreRiskAverseI (Ioi 0) (Kreps.UtilityForMoney.ExponentialUtility 1) Real.log ∧
      ¬MoreRiskAverseI (Ioi 0) Real.log (Kreps.UtilityForMoney.ExponentialUtility 1) := by
  have he (x : ℝ) : arrowPratt (Kreps.UtilityForMoney.ExponentialUtility 1) x = 1 := by
    rw [arrowPratt_eq_kreps, Kreps.UtilityForMoney.absoluteRiskAversion_exponential one_ne_zero]
  constructor
  · intro h
    have := h 2 (by norm_num)
    rw [he, arrowPratt_log (by norm_num)] at this
    norm_num at this
  · intro h
    have := h (1 / 2) (by norm_num)
    rw [he, arrowPratt_log (by norm_num)] at this
    norm_num at this

/-- The asset objective at wealth `w` is the objective of the shifted utility at zero. -/
theorem assetEU_shiftU (u : ℝ → ℝ) (w : ℝ) (μ : Measure ℝ) (γ : ℝ) :
    assetEU u w μ γ = assetEU (shiftU u w) 0 μ γ := by
  simp [assetEU, shiftU]

/-- **Exercise 6.C.8** (MWG, p. 193). Under decreasing absolute risk aversion the risky asset is
a normal good: if `w < w'`, `a` is the unique optimal investment at wealth `w` and `a'` an
optimal investment at `w'`, then `a ≤ a'`. -/
theorem exercise_6_C_8 {u : ℝ → ℝ} (hd : ∀ x, ContDiffAt ℝ 2 u x) (hp : ∀ x, 0 < deriv u x)
    (hdara : DecreasingAbsoluteRiskAversion u) {μ : Measure ℝ} (hμ : IsMoneyLottery univ μ)
    {w w' a a' : ℝ} (hww : w < w') (ha : a ∈ Icc 0 w)
    (hopt : ∀ γ ∈ Icc 0 w, assetEU u w μ γ ≤ assetEU u w μ a)
    (huniq : ∀ γ ∈ Icc 0 w, assetEU u w μ γ = assetEU u w μ a → γ = a) (ha' : a' ∈ Icc 0 w')
    (hopt' : ∀ γ ∈ Icc 0 w', assetEU u w' μ γ ≤ assetEU u w' μ a') : a ≤ a' := by
  have h12 : DecreasingAbsoluteRiskAversion u →
      ∀ x₂ x₁, x₂ < x₁ → MoreRiskAverseII univ (shiftU u x₁) (shiftU u x₂) :=
    ((proposition_6_C_3 hd hp).out 1 2).mp
  have hII : MoreRiskAverseII univ (shiftU u w') (shiftU u w) := h12 hdara w w' hww
  have hc : Continuous u := continuous_iff_continuousAt.mpr fun x => (hd x).continuousAt
  have hcs (x : ℝ) : ContinuousOn (shiftU u x) univ :=
    (show Continuous (shiftU u x) from by unfold shiftU; fun_prop).continuousOn
  have hmono : StrictMonoOn (shiftU u w') univ := by
    have := strictMono_of_deriv_pos (f := shiftU u w') fun z => by
      rw [deriv_shiftU]; exact hp _
    exact this.strictMonoOn _
  rcases le_or_gt w a' with hwa | hwa
  · exact ha.2.trans hwa
  · by_contra hlt
    have hlt : a' < a := lt_of_not_ge hlt
    have hcomp := invest_compare convex_univ isOpen_univ (hcs w') (hcs w) hmono hII hμ
      (w := 0) (α₁ := a') (β := w) (mem_univ 0) ha'.1 (fun _ _ _ _ => mem_univ _)
      (fun γ hγ => by
        rw [← assetEU_shiftU, ← assetEU_shiftU]
        exact hopt' γ ⟨ha'.1.trans hγ.1, hγ.2.trans hww.le⟩) a ⟨hlt.le, ha.2⟩
    rw [← assetEU_shiftU, ← assetEU_shiftU] at hcomp
    have ha'w : a' ∈ Icc 0 w := ⟨ha'.1, hwa.le⟩
    have heq := le_antisymm (hopt a' ha'w) hcomp
    exact absurd (huniq a' ha'w heq) hlt.ne

/-- The proportion problem: investing the fraction `γ` of wealth `w` gives final wealth
`w + γw(z - 1) = w(1 + γ(z - 1))`. -/
theorem proportion_objective (u : ℝ → ℝ) (w : ℝ) (μ : Measure ℝ) (γ : ℝ) :
    assetEU u w μ (γ * w) = assetEU (scaleU u w) 1 μ γ := by
  simp only [assetEU, scaleU]
  congr 1; ext z; congr 1; ring

/-- **Exercise 6.C.11** (MWG, p. 211). In the asset model with returns `z > 0`, if `r_R(x, u)`
is increasing in `x` then the optimal proportion `γ = α/w` invested in the risky asset is
decreasing in `w`, and if `r_R` is decreasing then `γ` is increasing. Here `g`, `g'` are the
optimal proportions at wealth `w < w'`, assumed unique where the comparison needs it. -/
theorem exercise_6_C_11 {u : ℝ → ℝ} (hd : ∀ x > 0, ContDiffAt ℝ 2 u x)
    (hp : ∀ x > 0, 0 < deriv u x) {μ : Measure ℝ} (hμ : IsMoneyLottery (Ioi 0) μ)
    {w w' g g' : ℝ} (hw : 0 < w) (hww : w < w') (hg : g ∈ Icc 0 1) (hg' : g' ∈ Icc 0 1)
    (hopt : ∀ γ ∈ Icc 0 1, assetEU (scaleU u w) 1 μ γ ≤ assetEU (scaleU u w) 1 μ g)
    (hopt' : ∀ γ ∈ Icc 0 1, assetEU (scaleU u w') 1 μ γ ≤ assetEU (scaleU u w') 1 μ g') :
    (MonotoneOn (relativeRiskAversion u) (Ioi 0) →
      (∀ γ ∈ Icc 0 1, assetEU (scaleU u w') 1 μ γ = assetEU (scaleU u w') 1 μ g' → γ = g') →
      g' ≤ g) ∧
    (AntitoneOn (relativeRiskAversion u) (Ioi 0) →
      (∀ γ ∈ Icc 0 1, assetEU (scaleU u w) 1 μ γ = assetEU (scaleU u w) 1 μ g → γ = g) →
      g ≤ g') := by
  have hw' : 0 < w' := hw.trans hww
  have hd2 (y : ℝ) (hy : 0 < y) : DifferentiableAt ℝ (deriv u) y :=
    ((hd y hy).derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hcs (x : ℝ) (hx : 0 < x) : ContinuousOn (scaleU u x) (Ioi 0) := fun t ht =>
    ((hd (x * t) (mul_pos hx ht)).continuousAt.comp
      (continuous_const.mul continuous_id).continuousAt).continuousWithinAt
  have hsm (x : ℝ) (hx : 0 < x) : StrictMonoOn (scaleU u x) (Ioi 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioi 0) (hcs x hx)
    rw [interior_Ioi]
    intro t ht
    rw [deriv_scaleU]; exact mul_pos (hp _ (mul_pos hx ht)) hx
  have hdom : ∀ z ∈ Ioi (0 : ℝ), ∀ γ ∈ Icc (0 : ℝ) 1, 1 + γ * (z - 1) ∈ Ioi (0 : ℝ) := by
    intro z hz γ hγ
    have hz' : (0 : ℝ) < z := hz
    change 0 < 1 + γ * (z - 1)
    rcases eq_or_lt_of_le hγ.2 with h1 | h1
    · rw [h1]; linarith
    · nlinarith [hγ.1]
  have hAP (x t : ℝ) (hx : 0 < x) (ht : 0 < t) :
      arrowPratt (scaleU u x) t = relativeRiskAversion u (x * t) / t :=
    arrowPratt_scaleU hx ht (hd2 _ (mul_pos hx ht))
  -- the generic comparison applied to the proportion problem
  have compare (x₁ x₂ a₁ a₂ : ℝ) (h₁ : 0 < x₁) (h₂ : 0 < x₂)
      (hI : MoreRiskAverseI (Ioi 0) (scaleU u x₁) (scaleU u x₂)) (ha₁ : a₁ ∈ Icc 0 1)
      (ho₁ : ∀ γ ∈ Icc 0 1, assetEU (scaleU u x₁) 1 μ γ ≤ assetEU (scaleU u x₁) 1 μ a₁)
      (ha₂ : a₂ ∈ Icc 0 1)
      (ho₂ : ∀ γ ∈ Icc 0 1, assetEU (scaleU u x₂) 1 μ γ ≤ assetEU (scaleU u x₂) 1 μ a₂)
      (hu₂ : ∀ γ ∈ Icc 0 1, assetEU (scaleU u x₂) 1 μ γ = assetEU (scaleU u x₂) 1 μ a₂ →
        γ = a₂) : a₂ ≤ a₁ := by
    have h12 : MoreRiskAverseI (Ioi 0) (scaleU u x₁) (scaleU u x₂) →
        MoreRiskAverseII (Ioi 0) (scaleU u x₁) (scaleU u x₂) :=
      ((scale_tfae hd hp h₁ h₂).out 1 2).mp
    have hII := h12 hI
    exact example_6_C_2_continued (convex_Ioi 0) isOpen_Ioi (hcs x₁ h₁) (hcs x₂ h₂)
      (hsm x₁ h₁) hII hμ (w := 1) (mem_Ioi.mpr one_pos) hdom ha₁ ho₁ ha₂ ho₂ hu₂
  constructor
  · intro hR hu'
    apply compare w w' g g' hw hw' _ hg hopt hg' hopt' hu'
    intro t ht
    have ht' : (0 : ℝ) < t := ht
    rw [hAP w t hw ht', hAP w' t hw' ht']
    apply div_le_div_of_nonneg_right _ ht'.le
    exact hR (mul_pos hw ht') (mul_pos hw' ht') (mul_le_mul_of_nonneg_right hww.le ht'.le)
  · intro hR hu
    apply compare w' w g' g hw' hw _ hg' hopt' hg hopt hu
    intro t ht
    have ht' : (0 : ℝ) < t := ht
    rw [hAP w t hw ht', hAP w' t hw' ht']
    apply div_le_div_of_nonneg_right _ ht'.le
    exact hR (mul_pos hw ht') (mul_pos hw' ht') (mul_le_mul_of_nonneg_right hww.le ht'.le)

end MWG.ChoiceUnderUncertainty
