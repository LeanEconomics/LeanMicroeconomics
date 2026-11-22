/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGChoiceUnderUncertainty.MoreRiskAverse
import UtilityForMoney.RelativeRisk

/-!
# Comparisons of risk aversion across wealth levels

MWG, Section 6.C, pp. 192-194: Definition 6.C.4 (decreasing absolute risk aversion),
Proposition 6.C.3 with Exercise 6.C.10, Definition 6.C.5 (relative risk aversion),
`r_R = x r_A`, decreasing relative implies decreasing absolute risk aversion (and not
conversely), and Proposition 6.C.4.

MWG's "decreasing" is read as nonincreasing (`Antitone`): with the strict reading condition
(iii) of Proposition 6.C.3 fails for every degenerate risk, for which `x - c_x` is constant.
Proposition 6.C.3 is proved, as Exercise 6.C.10 suggests, by applying Proposition 6.C.2 to the
shifted utilities `z ↦ u(x + z)`, and Proposition 6.C.4 (all three equivalences, not only the
implication proved in the text) by applying it to the scaled utilities `t ↦ u(tx)` on
`t > 0`.
-/

namespace MWG.ChoiceUnderUncertainty

open MeasureTheory Filter Topology Set

/-- The utility of increments `z` to the wealth level `x`, `z ↦ u(x + z)`. -/
def shiftU (u : ℝ → ℝ) (x : ℝ) : ℝ → ℝ := fun z => u (x + z)

theorem deriv_shiftU (u : ℝ → ℝ) (x z : ℝ) : deriv (shiftU u x) z = deriv u (x + z) :=
  deriv_comp_const_add u x z

theorem arrowPratt_shiftU (u : ℝ → ℝ) (x z : ℝ) :
    arrowPratt (shiftU u x) z = arrowPratt u (x + z) := by
  have h1 : deriv (shiftU u x) = fun z => deriv u (x + z) := funext fun z => deriv_shiftU u x z
  have h2 : deriv (deriv (shiftU u x)) z = deriv (deriv u) (x + z) := by
    rw [h1]; exact deriv_comp_const_add (deriv u) x z
  unfold arrowPratt
  rw [h2, deriv_shiftU]

theorem probPremium_shiftU (u : ℝ → ℝ) (x y ε : ℝ) :
    probPremium (shiftU u x) y ε = probPremium u (x + y) ε := by
  unfold probPremium shiftU
  rw [show x + (y + ε) = x + y + ε by ring, show x + (y - ε) = x + y - ε by ring]

theorem contDiffAt_shiftU {u : ℝ → ℝ} (hd : ∀ x, ContDiffAt ℝ 2 u x) (x z : ℝ) :
    ContDiffAt ℝ 2 (shiftU u x) z :=
  (hd (x + z)).comp z (contDiffAt_const.add contDiffAt_id)

/-- A translate of a money lottery on `ℝ` is a money lottery on `ℝ`. -/
theorem isMoneyLottery_map_add {μ : Measure ℝ} (hμ : IsMoneyLottery univ μ) (c : ℝ) :
    IsMoneyLottery univ (μ.map (fun z => z + c)) := by
  have := hμ.1
  obtain ⟨a, b, -, h0⟩ := hμ.2
  refine ⟨inferInstance, a + c, b + c, subset_univ _, ?_⟩
  rw [Measure.map_apply (by fun_prop) measurableSet_Icc.compl]
  apply measure_mono_null _ h0
  intro z hz hz'
  exact hz ⟨by linarith [hz'.1], by linarith [hz'.2]⟩

/-- **Definition 6.C.4** (MWG, p. 193). Decreasing absolute risk aversion: `r_A(x, u)` is a
(nonincreasing) decreasing function of `x`. -/
def DecreasingAbsoluteRiskAversion (u : ℝ → ℝ) : Prop := Antitone (arrowPratt u)

/-- Proposition 6.C.2 for the shifted pair `(u(x₁ + ·), u(x₂ + ·))`. -/
theorem shift_tfae {u : ℝ → ℝ} (hd : ∀ x, ContDiffAt ℝ 2 u x) (hp : ∀ x, 0 < deriv u x)
    (x₁ x₂ : ℝ) :
    List.TFAE [MoreRiskAverseI univ (shiftU u x₁) (shiftU u x₂),
      MoreRiskAverseII univ (shiftU u x₁) (shiftU u x₂),
      MoreRiskAverseIII univ (shiftU u x₁) (shiftU u x₂),
      MoreRiskAverseIV univ (shiftU u x₁) (shiftU u x₂),
      MoreRiskAverseV univ (shiftU u x₁) (shiftU u x₂)] :=
  proposition_6_C_2 convex_univ isOpen_univ univ_nonempty
    (fun z _ => contDiffAt_shiftU hd x₁ z) (fun z _ => contDiffAt_shiftU hd x₂ z)
    (fun z _ => by rw [deriv_shiftU]; exact hp _) (fun z _ => by rw [deriv_shiftU]; exact hp _)

/-- **Proposition 6.C.3** (MWG, p. 193) and **Exercise 6.C.10** (p. 211). For a twice
continuously differentiable Bernoulli utility with `u' > 0`, the following are equivalent:
(i) decreasing absolute risk aversion; (ii) for `x₂ < x₁`, `u(x₂ + ·)` is a concave
transformation of `u(x₁ + ·)`; (iii) for every risk `F`, `x - c_x` is decreasing, where
`u(c_x) = ∫ u(x + z) dF(z)`; (iv) `π(x, ε, u)` is decreasing in `x`; (v) if
`∫ u(x₂ + z) dF ≥ u(x₂)` and `x₂ < x₁` then `∫ u(x₁ + z) dF ≥ u(x₁)`. -/
theorem proposition_6_C_3 {u : ℝ → ℝ} (hd : ∀ x, ContDiffAt ℝ 2 u x)
    (hp : ∀ x, 0 < deriv u x) :
    List.TFAE [DecreasingAbsoluteRiskAversion u,
      ∀ x₂ x₁, x₂ < x₁ → MoreRiskAverseII univ (shiftU u x₁) (shiftU u x₂),
      ∀ μ x₁ x₂ c₁ c₂, IsMoneyLottery univ μ → x₂ < x₁ → u c₁ = ∫ z, u (x₁ + z) ∂μ →
        u c₂ = ∫ z, u (x₂ + z) ∂μ → x₁ - c₁ ≤ x₂ - c₂,
      ∀ ε, 0 < ε → Antitone fun x => probPremium u x ε,
      ∀ μ x₁ x₂, IsMoneyLottery univ μ → x₂ < x₁ → u x₂ ≤ ∫ z, u (x₂ + z) ∂μ →
        u x₁ ≤ ∫ z, u (x₁ + z) ∂μ] := by
  have T (x₁ x₂ : ℝ) := shift_tfae hd hp x₁ x₂
  -- each condition is the pairwise counterpart of Proposition 6.C.2
  have e1 : DecreasingAbsoluteRiskAversion u ↔
      ∀ x₂ x₁, x₂ < x₁ → MoreRiskAverseI univ (shiftU u x₁) (shiftU u x₂) := by
    constructor
    · intro h x₂ x₁ hlt z _
      rw [arrowPratt_shiftU, arrowPratt_shiftU]
      exact h (by linarith)
    · intro h a b hab
      rcases eq_or_lt_of_le hab with he | hlt
      · rw [he]
      · have := h a b hlt 0 (mem_univ _)
        rwa [arrowPratt_shiftU, arrowPratt_shiftU, add_zero, add_zero] at this
  have e3 : (∀ μ x₁ x₂ c₁ c₂, IsMoneyLottery univ μ → x₂ < x₁ → u c₁ = ∫ z, u (x₁ + z) ∂μ →
        u c₂ = ∫ z, u (x₂ + z) ∂μ → x₁ - c₁ ≤ x₂ - c₂) ↔
      ∀ x₂ x₁, x₂ < x₁ → MoreRiskAverseIII univ (shiftU u x₁) (shiftU u x₂) := by
    constructor
    · intro h x₂ x₁ hlt μ k₁ k₂ hμ hk1 hk2
      have := h μ x₁ x₂ (x₁ + k₁) (x₂ + k₂) hμ hlt hk1.2 hk2.2
      linarith
    · intro h μ x₁ x₂ c₁ c₂ hμ hlt hc1 hc2
      have := h x₂ x₁ hlt μ (c₁ - x₁) (c₂ - x₂) hμ
        ⟨mem_univ _, by simp only [shiftU, add_sub_cancel]; exact hc1⟩
        ⟨mem_univ _, by simp only [shiftU, add_sub_cancel]; exact hc2⟩
      linarith
  have e4 : (∀ ε, 0 < ε → Antitone fun x => probPremium u x ε) ↔
      ∀ x₂ x₁, x₂ < x₁ → MoreRiskAverseIV univ (shiftU u x₁) (shiftU u x₂) := by
    constructor
    · intro h x₂ x₁ hlt y ε hε _ _
      rw [probPremium_shiftU, probPremium_shiftU]
      exact h ε hε (by linarith)
    · intro h ε hε a b hab
      rcases eq_or_lt_of_le hab with he | hlt
      · rw [he]
      · have := h a b hlt 0 ε hε (mem_univ _) (mem_univ _)
        rwa [probPremium_shiftU, probPremium_shiftU, add_zero, add_zero] at this
  have e5 : (∀ μ x₁ x₂, IsMoneyLottery univ μ → x₂ < x₁ → u x₂ ≤ ∫ z, u (x₂ + z) ∂μ →
        u x₁ ≤ ∫ z, u (x₁ + z) ∂μ) ↔
      ∀ x₂ x₁, x₂ < x₁ → MoreRiskAverseV univ (shiftU u x₁) (shiftU u x₂) := by
    constructor
    · intro h x₂ x₁ hlt μ y hμ _ hle
      have hμ' := isMoneyLottery_map_add hμ (-y)
      have hmap (x : ℝ) : ∫ z, u (x + y + z) ∂(μ.map fun z => z + -y) = ∫ z, u (x + z) ∂μ := by
        rw [integral_map (by fun_prop) (by
          exact (hμ'.integrable (S := univ) (u := fun z => u (x + y + z))
            (by
              have hc : Continuous u := continuous_iff_continuousAt.mpr fun z =>
                (hd z).continuousAt
              fun_prop)).aestronglyMeasurable)]
        congr 1; ext z; congr 1; ring
      have := h _ (x₁ + y) (x₂ + y) hμ' (by linarith) (by rw [hmap]; exact hle)
      rw [hmap] at this
      exact this
    · intro h μ x₁ x₂ hμ hlt hle
      have := h x₂ x₁ hlt μ 0 hμ (mem_univ _) (by simpa [shiftU] using hle)
      simpa [shiftU] using this
  have e2 : (∀ x₂ x₁, x₂ < x₁ → MoreRiskAverseII univ (shiftU u x₁) (shiftU u x₂)) ↔
      ∀ x₂ x₁, x₂ < x₁ → MoreRiskAverseI univ (shiftU u x₁) (shiftU u x₂) :=
    forall₂_congr fun x₂ x₁ => imp_congr_right fun _ => (T x₁ x₂).out 2 1
  have e3' : (∀ x₂ x₁, x₂ < x₁ → MoreRiskAverseIII univ (shiftU u x₁) (shiftU u x₂)) ↔
      ∀ x₂ x₁, x₂ < x₁ → MoreRiskAverseI univ (shiftU u x₁) (shiftU u x₂) :=
    forall₂_congr fun x₂ x₁ => imp_congr_right fun _ => (T x₁ x₂).out 3 1
  have e4' : (∀ x₂ x₁, x₂ < x₁ → MoreRiskAverseIV univ (shiftU u x₁) (shiftU u x₂)) ↔
      ∀ x₂ x₁, x₂ < x₁ → MoreRiskAverseI univ (shiftU u x₁) (shiftU u x₂) :=
    forall₂_congr fun x₂ x₁ => imp_congr_right fun _ => (T x₁ x₂).out 4 1
  have e5' : (∀ x₂ x₁, x₂ < x₁ → MoreRiskAverseV univ (shiftU u x₁) (shiftU u x₂)) ↔
      ∀ x₂ x₁, x₂ < x₁ → MoreRiskAverseI univ (shiftU u x₁) (shiftU u x₂) :=
    forall₂_congr fun x₂ x₁ => imp_congr_right fun _ => (T x₁ x₂).out 5 1
  tfae_have 1 ↔ 2 := e1.trans e2.symm
  tfae_have 1 ↔ 3 := e1.trans (e3.trans e3').symm
  tfae_have 1 ↔ 4 := e1.trans (e4.trans e4').symm
  tfae_have 1 ↔ 5 := e1.trans (e5.trans e5').symm
  tfae_finish

/-- **Definition 6.C.5** (MWG, p. 194). The coefficient of relative risk aversion
`r_R(x, u) = -x u''(x)/u'(x)`; it is Kreps's `RelativeRiskAversion`. -/
noncomputable def relativeRiskAversion (u : ℝ → ℝ) (x : ℝ) : ℝ := x * arrowPratt u x

theorem relativeRiskAversion_eq_kreps (u : ℝ → ℝ) (x : ℝ) :
    relativeRiskAversion u x = Kreps.UtilityForMoney.RelativeRiskAversion u x := rfl

/-- **p. 194**. `r_R(x, u) = -x u''(x)/u'(x)`, the Arrow-Pratt coefficient of `t ↦ u(tx)` at
`t = 1`: `-ũ''(1)/ũ'(1) = -x u''(x)/u'(x)`. -/
theorem relativeRiskAversion_eq (u : ℝ → ℝ) (x : ℝ) :
    relativeRiskAversion u x = -x * deriv (deriv u) x / deriv u x := by
  unfold relativeRiskAversion arrowPratt; ring

/-- **p. 194**. A risk-averse individual (`r_A ≥ 0`) on `x > 0` with decreasing relative risk
aversion has decreasing absolute risk aversion, since `r_A = r_R/x`. -/
theorem decreasingAbsolute_of_decreasingRelative {u : ℝ → ℝ}
    (hra : ∀ x > 0, 0 ≤ arrowPratt u x)
    (h : AntitoneOn (relativeRiskAversion u) (Ioi 0)) : AntitoneOn (arrowPratt u) (Ioi 0) := by
  intro x hx y hy hxy
  have hx' : (0 : ℝ) < x := hx
  have hy' : (0 : ℝ) < y := hy
  have hR := h hx hy hxy
  unfold relativeRiskAversion at hR
  have h1 : arrowPratt u y ≤ x * arrowPratt u x / y := by
    rw [le_div_iff₀ hy']; linarith
  calc arrowPratt u y ≤ x * arrowPratt u x / y := h1
    _ ≤ y * arrowPratt u x / y := by
        apply div_le_div_of_nonneg_right _ hy'.le
        exact mul_le_mul_of_nonneg_right hxy (hra x hx')
    _ = arrowPratt u x := by field_simp

/-- **p. 194**. The converse fails: `u(x) = -e^{-x}` has constant (so decreasing) absolute risk
aversion, but `r_R(x, u) = x` is not decreasing. -/
theorem decreasingRelative_not_of_decreasingAbsolute :
    Antitone (arrowPratt (Kreps.UtilityForMoney.ExponentialUtility 1)) ∧
      ¬AntitoneOn (relativeRiskAversion (Kreps.UtilityForMoney.ExponentialUtility 1))
        (Ioi 0) := by
  refine ⟨fun x y _ => ?_, Kreps.UtilityForMoney.relativeRisk_printed_counterexample.2⟩
  rw [arrowPratt_eq_kreps, arrowPratt_eq_kreps,
    Kreps.UtilityForMoney.absoluteRiskAversion_exponential one_ne_zero,
    Kreps.UtilityForMoney.absoluteRiskAversion_exponential one_ne_zero]

/-- The utility of proportional risks at wealth `x`, `t ↦ u(xt)` (MWG, p. 193). -/
def scaleU (u : ℝ → ℝ) (x : ℝ) : ℝ → ℝ := fun t => u (x * t)

theorem deriv_scaleU (u : ℝ → ℝ) (x t : ℝ) : deriv (scaleU u x) t = deriv u (x * t) * x :=
  Kreps.UtilityForMoney.deriv_scaled_wealth u x t

theorem arrowPratt_scaleU {u : ℝ → ℝ} {x t : ℝ} (hx : 0 < x) (ht : 0 < t)
    (h₂ : DifferentiableAt ℝ (deriv u) (x * t)) :
    arrowPratt (scaleU u x) t = relativeRiskAversion u (x * t) / t :=
  Kreps.UtilityForMoney.absoluteRiskAversion_scaled hx ht h₂

/-- Proposition 6.C.2 on `t > 0` for the scaled pair `(u(x₁ ·), u(x₂ ·))`. -/
theorem scale_tfae {u : ℝ → ℝ} (hd : ∀ x > 0, ContDiffAt ℝ 2 u x)
    (hp : ∀ x > 0, 0 < deriv u x) {x₁ x₂ : ℝ} (h1 : 0 < x₁) (h2 : 0 < x₂) :
    List.TFAE [MoreRiskAverseI (Ioi 0) (scaleU u x₁) (scaleU u x₂),
      MoreRiskAverseII (Ioi 0) (scaleU u x₁) (scaleU u x₂),
      MoreRiskAverseIII (Ioi 0) (scaleU u x₁) (scaleU u x₂),
      MoreRiskAverseIV (Ioi 0) (scaleU u x₁) (scaleU u x₂),
      MoreRiskAverseV (Ioi 0) (scaleU u x₁) (scaleU u x₂)] := by
  have hc (x : ℝ) (hx : 0 < x) (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) : ContDiffAt ℝ 2 (scaleU u x) t :=
    (hd (x * t) (mul_pos hx ht)).comp t (contDiffAt_const.mul contDiffAt_id)
  have hq (x : ℝ) (hx : 0 < x) (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) : 0 < deriv (scaleU u x) t := by
    rw [deriv_scaleU]; exact mul_pos (hp _ (mul_pos hx ht)) hx
  exact proposition_6_C_2 (convex_Ioi 0) isOpen_Ioi ⟨1, mem_Ioi.mpr one_pos⟩ (hc x₁ h1) (hc x₂ h2)
    (hq x₁ h1) (hq x₂ h2)

/-- **Proposition 6.C.4** (MWG, p. 194). For a Bernoulli utility on `x > 0`, twice
continuously differentiable with `u' > 0`, the following are equivalent: (i) `r_R(x, u)` is
decreasing in `x`; (ii) for `x₂ < x₁`, `t ↦ u(t x₂)` is a concave transformation of
`t ↦ u(t x₁)`; (iii) for every risk `F` on `t > 0`, the certainty equivalent `ĉ_x` with
`u(ĉ_x) = ∫ u(tx) dF(t)` makes `x/ĉ_x` decreasing in `x`. -/
theorem proposition_6_C_4 {u : ℝ → ℝ} (hd : ∀ x > 0, ContDiffAt ℝ 2 u x)
    (hp : ∀ x > 0, 0 < deriv u x) :
    List.TFAE [AntitoneOn (relativeRiskAversion u) (Ioi 0),
      ∀ x₂ x₁, 0 < x₂ → x₂ < x₁ → MoreRiskAverseII (Ioi 0) (scaleU u x₁) (scaleU u x₂),
      ∀ μ x₁ x₂ c₁ c₂, IsMoneyLottery (Ioi 0) μ → 0 < x₂ → x₂ < x₁ → 0 < c₁ → 0 < c₂ →
        u c₁ = ∫ t, u (x₁ * t) ∂μ → u c₂ = ∫ t, u (x₂ * t) ∂μ → x₁ / c₁ ≤ x₂ / c₂] := by
  have hd2 (y : ℝ) (hy : 0 < y) : DifferentiableAt ℝ (deriv u) y := by
    exact ((hd y hy).derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have e1 : AntitoneOn (relativeRiskAversion u) (Ioi 0) ↔
      ∀ x₂ x₁, 0 < x₂ → x₂ < x₁ → MoreRiskAverseI (Ioi 0) (scaleU u x₁) (scaleU u x₂) := by
    constructor
    · intro h x₂ x₁ h2 hlt t ht
      have ht' : (0 : ℝ) < t := ht
      rw [arrowPratt_scaleU (h2.trans hlt) ht' (hd2 _ (mul_pos (h2.trans hlt) ht')),
        arrowPratt_scaleU h2 ht' (hd2 _ (mul_pos h2 ht'))]
      apply div_le_div_of_nonneg_right _ ht'.le
      exact h (show (0 : ℝ) < x₂ * t from mul_pos h2 ht')
        (show (0 : ℝ) < x₁ * t from mul_pos (h2.trans hlt) ht')
        (mul_le_mul_of_nonneg_right hlt.le ht'.le)
    · intro h a ha b hb hab
      rcases eq_or_lt_of_le hab with he | hlt
      · rw [he]
      · have ha' : (0 : ℝ) < a := ha
        have hb' : (0 : ℝ) < b := hb
        have := h a b ha' hlt 1 (mem_Ioi.mpr one_pos)
        rwa [arrowPratt_scaleU hb' one_pos (hd2 _ (by simpa using hb')),
          arrowPratt_scaleU ha' one_pos (hd2 _ (by simpa using ha')), mul_one, mul_one,
          div_one, div_one] at this
  have e3 : (∀ μ x₁ x₂ c₁ c₂, IsMoneyLottery (Ioi 0) μ → 0 < x₂ → x₂ < x₁ → 0 < c₁ → 0 < c₂ →
        u c₁ = ∫ t, u (x₁ * t) ∂μ → u c₂ = ∫ t, u (x₂ * t) ∂μ → x₁ / c₁ ≤ x₂ / c₂) ↔
      ∀ x₂ x₁, 0 < x₂ → x₂ < x₁ → MoreRiskAverseIII (Ioi 0) (scaleU u x₁) (scaleU u x₂) := by
    constructor
    · intro h x₂ x₁ h2 hlt μ k₁ k₂ hμ hk1 hk2
      have h1 : 0 < x₁ := h2.trans hlt
      have hk1' : (0 : ℝ) < k₁ := hk1.1
      have hk2' : (0 : ℝ) < k₂ := hk2.1
      have := h μ x₁ x₂ (x₁ * k₁) (x₂ * k₂) hμ h2 hlt (mul_pos h1 hk1') (mul_pos h2 hk2')
        hk1.2 hk2.2
      rw [div_le_div_iff₀ (mul_pos h1 hk1') (mul_pos h2 hk2')] at this
      have : x₁ * x₂ * k₂ ≤ x₁ * x₂ * k₁ := by nlinarith
      exact le_of_mul_le_mul_left this (mul_pos h1 h2)
    · intro h μ x₁ x₂ c₁ c₂ hμ h2 hlt hc1 hc2 he1 he2
      have h1 : 0 < x₁ := h2.trans hlt
      have := h x₂ x₁ h2 hlt μ (c₁ / x₁) (c₂ / x₂) hμ
        ⟨div_pos hc1 h1, by simp only [scaleU]; rw [mul_div_cancel₀ _ h1.ne']; exact he1⟩
        ⟨div_pos hc2 h2, by simp only [scaleU]; rw [mul_div_cancel₀ _ h2.ne']; exact he2⟩
      rw [div_le_div_iff₀ h2 h1] at this
      rw [div_le_div_iff₀ hc1 hc2]
      nlinarith
  have e2' : (∀ x₂ x₁, 0 < x₂ → x₂ < x₁ → MoreRiskAverseII (Ioi 0) (scaleU u x₁) (scaleU u x₂))
      ↔ ∀ x₂ x₁, 0 < x₂ → x₂ < x₁ → MoreRiskAverseI (Ioi 0) (scaleU u x₁) (scaleU u x₂) :=
    forall₂_congr fun x₂ x₁ => forall_congr' fun h2 => imp_congr_right fun hlt =>
      (scale_tfae hd hp (h2.trans hlt) h2).out 2 1
  have e3' : (∀ x₂ x₁, 0 < x₂ → x₂ < x₁ →
        MoreRiskAverseIII (Ioi 0) (scaleU u x₁) (scaleU u x₂)) ↔
      ∀ x₂ x₁, 0 < x₂ → x₂ < x₁ → MoreRiskAverseI (Ioi 0) (scaleU u x₁) (scaleU u x₂) :=
    forall₂_congr fun x₂ x₁ => forall_congr' fun h2 => imp_congr_right fun hlt =>
      (scale_tfae hd hp (h2.trans hlt) h2).out 3 1
  tfae_have 1 ↔ 2 := e1.trans e2'.symm
  tfae_have 1 ↔ 3 := e1.trans (e3.trans e3').symm
  tfae_finish

end MWG.ChoiceUnderUncertainty
