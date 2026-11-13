/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGClassicalDemand.EconWelfare
import MWGClassicalDemand.ExpCobbDouglas
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The area variation and the deadweight loss (Figure 3.I.8, footnote 29)

MWG, Section 3.I, p. 90, Figure 3.I.8 and footnote 29. The book: "the approximation error may be
quite large as a fraction of the deadweight loss ... The percentage difference between these two
areas need not grow small as the price change grows small."

Precise statement proved here. Cobb-Douglas utility `x₁^α x₂^{1-α}`, `α ∈ (0, 1)`, prices
`p⁰ ≫ 0`, wealth `w > 0`; a tax raises the price of good 1 from `a = p⁰₁` to `s`
(`p¹ = (s, p⁰₂)`, `τ = s - a`). The book's deadweight losses are
* (3.I.5), measured at `u¹`: `DWL_EV(s) = -τ x₁(p¹, w) - EV(p⁰, p¹, w)`;
* (3.I.6), measured at `u⁰`: `DWL_CV(s) = -CV(p⁰, p¹, w) - τ h₁(p¹, u⁰)`;
and the deadweight loss computed from the Walrasian demand curve replaces the welfare change by
the area variation: `DWL_AV(s) = -AV(p⁰, p¹, w) - τ x₁(p¹, w)`. All three are computed in closed
form from the project's `expenditure`, `indirectUtility`, `equivalentVariation`,
`compensatingVariation`, `hicksianOf` and `areaVariation` (`last_cd_dwl_ev_eq`,
`last_cd_dwl_cv_eq`, `last_cd_dwl_av_eq`). Their second-order expansions at `s = a` are
`DWL_EV, DWL_CV ≈ α(1-α)w(s-a)²/(2a²)` and `DWL_AV ≈ αw(s-a)²/(2a²)`, so

`(DWL_AV - DWL)/DWL → α/(1-α) ≠ 0` as `s → a`, for both book measures
(`figure_3_I_8_ev`, `figure_3_I_8_cv`, summary `figure_3_I_8`).

By contrast the relative error of `AV` against the welfare change itself tends to `0`
(`welfare_av_relative_error`, p. 89).

The computation in `docs/source-map-F2.md` (limit `-α/(α+1)`) uses the mixed measure
`-CV(p⁰, p¹, w) - τ x₁(p¹, w)` (the compensating variation minus the revenue actually collected,
rather than (3.I.6)'s compensated revenue `τ h₁(p¹, u⁰)`): that limit is proved as well
(`footnote_3_I_29_mixed`); it is not one of the book's two deadweight-loss measures
(correction G-2). The footnote's own claim (misranking of two equal-revenue taxes) needs two
taxed goods with different wealth effects and is not covered here (see `docs/source-map-G.md`).
-/

namespace MWG.ClassicalDemand

open MWG.ConsumerChoice Kreps.PreferenceProperties Filter Topology Asymptotics

/-- The relative price factor `q(s) = (s/a)^α`. -/
noncomputable def lastQ (a α s : ℝ) : ℝ := (s / a) ^ α

/-- `q(s) > 0` for `a, s > 0`. -/
theorem lastQ_pos {a α s : ℝ} (ha : 0 < a) (hs : 0 < s) : 0 < lastQ a α s :=
  Real.rpow_pos_of_pos (div_pos hs ha) _

/-- `q(a) = 1`. -/
theorem lastQ_self {a : ℝ} (ha : 0 < a) (α : ℝ) : lastQ a α a = 1 := by
  simp [lastQ, div_self ha.ne']

/-- `q'(s) = α q(s)/s`. -/
theorem lastQ_hasDerivAt {a α s : ℝ} (ha : 0 < a) (hs : 0 < s) :
    HasDerivAt (lastQ a α) (α * lastQ a α s / s) s := by
  have h : HasDerivAt (lastQ a α) _ s := ((hasDerivAt_id' s).div_const a).rpow_const (p := α)
    (Or.inl (div_pos hs ha).ne')
  convert h using 1
  rw [Real.rpow_sub_one (div_pos hs ha).ne', lastQ]
  field_simp

/-- A function vanishing to first order at `a` with second derivative `σ` there:
`F(s) = (σ/2)(s - a)² + o((s - a)²)`. -/
theorem last_quadratic_of_deriv {F H : ℝ → ℝ} {a σ : ℝ}
    (hF : ∀ᶠ t in 𝓝 a, HasDerivAt F (H t) t) (hH : HasDerivAt H σ a) (hF0 : F a = 0)
    (hH0 : H a = 0) :
    (fun s => F s - σ / 2 * (s - a) ^ 2) =o[𝓝 a] fun s => (s - a) ^ 2 := by
  have h := econ_second_order_taylor hF hH
  simpa [hF0, hH0] using h

/-- If `F ≈ c(s - a)²` with `c ≠ 0` and `G ≈ d(s - a)²`, then `(G - F)/F → (d - c)/c`. -/
theorem last_ratio_limit {F G : ℝ → ℝ} {a c d : ℝ} (hc : c ≠ 0)
    (hF : (fun s => F s - c * (s - a) ^ 2) =o[𝓝 a] fun s => (s - a) ^ 2)
    (hG : (fun s => G s - d * (s - a) ^ 2) =o[𝓝 a] fun s => (s - a) ^ 2) :
    Tendsto (fun s => (G s - F s) / F s) (𝓝[≠] a) (𝓝 ((d - c) / c)) := by
  have h1 := (hF.mono (nhdsWithin_le_nhds (s := {a}ᶜ))).tendsto_div_nhds_zero
  have h2 := (hG.mono (nhdsWithin_le_nhds (s := {a}ᶜ))).tendsto_div_nhds_zero
  have hF' : Tendsto (fun s => F s / (s - a) ^ 2) (𝓝[≠] a) (𝓝 c) := by
    have := h1.add_const c
    rw [zero_add] at this
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have : (s - a) ^ 2 ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hs)
    rw [sub_div, mul_div_assoc, div_self this, mul_one, sub_add_cancel]
  have hG' : Tendsto (fun s => G s / (s - a) ^ 2) (𝓝[≠] a) (𝓝 d) := by
    have := h2.add_const d
    rw [zero_add] at this
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have : (s - a) ^ 2 ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hs)
    rw [sub_div, mul_div_assoc, div_self this, mul_one, sub_add_cancel]
  refine ((hG'.sub hF').div hF' hc).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have : (s - a) ^ 2 ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hs)
  change (G s / (s - a) ^ 2 - F s / (s - a) ^ 2) / (F s / (s - a) ^ 2) = _
  rw [← sub_div, div_div_div_cancel_right₀ this]

/-- The closed form of `DWL_EV(s) = -τ x₁(p¹, w) - EV` for Cobb-Douglas. -/
noncomputable def lastDwlEV (a α w s : ℝ) : ℝ :=
  -((s - a) * (α * w / s)) - (w / lastQ a α s - w)

/-- The closed form of `DWL_CV(s) = -CV - τ h₁(p¹, u⁰)` for Cobb-Douglas. -/
noncomputable def lastDwlCV (a α w s : ℝ) : ℝ :=
  -(w - w * lastQ a α s) - (s - a) * (α * (w * lastQ a α s) / s)

/-- The closed form of `DWL_AV(s) = -AV - τ x₁(p¹, w)` for Cobb-Douglas. -/
noncomputable def lastDwlAV (a α w s : ℝ) : ℝ :=
  -(α * w * Real.log (a / s)) - (s - a) * (α * w / s)

/-- The closed form of the mixed measure `-CV - τ x₁(p¹, w)` for Cobb-Douglas. -/
noncomputable def lastDwlMixed (a α w s : ℝ) : ℝ :=
  -(w - w * lastQ a α s) - (s - a) * (α * w / s)

/-- `d/ds [(s - a)(c/s)] = c a/s²`. -/
theorem last_revenue_hasDerivAt (a c : ℝ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun s => (s - a) * (c / s)) (c * a / s ^ 2) s := by
  have h : HasDerivAt (fun s => (s - a) * (c / s)) _ s := ((hasDerivAt_id' s).sub_const a).mul
    ((hasDerivAt_const s c).div (hasDerivAt_id' s) hs.ne')
  convert h using 1
  field_simp
  ring

/-- `d/ds [c a/s²]` at `s`. -/
theorem last_inv_sq_hasDerivAt (c : ℝ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun s => c / s ^ 2) (-(2 * c) / s ^ 3) s := by
  have h : HasDerivAt (fun s => c / s ^ 2) _ s :=
    (hasDerivAt_const s c).div ((hasDerivAt_id' s).pow 2) (pow_ne_zero 2 hs.ne')
  convert h using 1
  field_simp
  ring

/-- Expansion of `DWL_EV`: `≈ α(1-α)w(s-a)²/(2a²)`. -/
theorem lastDwlEV_expansion {a α w : ℝ} (ha : 0 < a) :
    (fun s => lastDwlEV a α w s - α * (1 - α) * w / a ^ 2 / 2 * (s - a) ^ 2) =o[𝓝 a]
      fun s => (s - a) ^ 2 := by
  set H : ℝ → ℝ := fun s => -(α * w * a / s ^ 2) + α * w / (s * lastQ a α s) with hH
  have hD : ∀ᶠ t in 𝓝 a, HasDerivAt (lastDwlEV a α w) (H t) t := by
    filter_upwards [lt_mem_nhds ha] with t ht
    have hq := lastQ_hasDerivAt (α := α) ha ht
    have hqne := (lastQ_pos (α := α) ha ht).ne'
    have h : HasDerivAt (lastDwlEV a α w) _ t := ((last_revenue_hasDerivAt a (α * w) ht).neg).sub
      (((hasDerivAt_const t w).div hq hqne).sub_const w)
    convert h using 1
    simp only [hH]
    field_simp
    ring
  have hH' : HasDerivAt H (α * (1 - α) * w / a ^ 2) a := by
    have hq := lastQ_hasDerivAt (α := α) ha ha
    have hqne := (lastQ_pos (α := α) ha ha).ne'
    have h : HasDerivAt H _ a := (last_inv_sq_hasDerivAt (α * w * a) ha).neg.add
      ((hasDerivAt_const a (α * w)).div ((hasDerivAt_id' a).mul hq)
        (mul_ne_zero ha.ne' hqne))
    convert h using 1
    simp only [lastQ_self ha]
    field_simp
    ring
  have h := last_quadratic_of_deriv hD hH' (by simp [lastDwlEV, lastQ_self ha])
    (by simp only [hH, lastQ_self ha]; field_simp; ring)
  exact h

/-- Expansion of `DWL_CV`: `≈ α(1-α)w(s-a)²/(2a²)`. -/
theorem lastDwlCV_expansion {a α w : ℝ} (ha : 0 < a) :
    (fun s => lastDwlCV a α w s - α * (1 - α) * w / a ^ 2 / 2 * (s - a) ^ 2) =o[𝓝 a]
      fun s => (s - a) ^ 2 := by
  set H : ℝ → ℝ := fun s => α * (1 - α) * w * ((s - a) * (lastQ a α s / s ^ 2)) with hH
  have hD : ∀ᶠ t in 𝓝 a, HasDerivAt (lastDwlCV a α w) (H t) t := by
    filter_upwards [lt_mem_nhds ha] with t ht
    have hq := lastQ_hasDerivAt (α := α) ha ht
    have h : HasDerivAt (lastDwlCV a α w) _ t :=
      (((hasDerivAt_const t w).sub ((hasDerivAt_const t w).mul hq)).neg).sub
      (((hasDerivAt_id' t).sub_const a).mul
        (((hasDerivAt_const t α).mul ((hasDerivAt_const t w).mul hq)).div
          (hasDerivAt_id' t) ht.ne'))
    convert h using 1
    simp only [hH, Pi.mul_apply]
    field_simp
    ring
  have hH' : HasDerivAt H (α * (1 - α) * w / a ^ 2) a := by
    have hq := lastQ_hasDerivAt (α := α) ha ha
    have h : HasDerivAt H _ a := (((hasDerivAt_id' a).sub_const a).mul
      (hq.div ((hasDerivAt_id' a).pow 2) (pow_ne_zero 2 ha.ne'))).const_mul (α * (1 - α) * w)
    convert h using 1
    simp only [Pi.div_apply, Pi.pow_apply, lastQ_self ha]
    field_simp
    ring
  exact last_quadratic_of_deriv hD hH' (by simp [lastDwlCV, lastQ_self ha])
    (by simp [hH])

/-- Expansion of `DWL_AV`: `≈ αw(s-a)²/(2a²)`. -/
theorem lastDwlAV_expansion {a α w : ℝ} (ha : 0 < a) :
    (fun s => lastDwlAV a α w s - α * w / a ^ 2 / 2 * (s - a) ^ 2) =o[𝓝 a]
      fun s => (s - a) ^ 2 := by
  set H : ℝ → ℝ := fun s => α * w * ((s - a) / s ^ 2) with hH
  have hD : ∀ᶠ t in 𝓝 a, HasDerivAt (lastDwlAV a α w) (H t) t := by
    filter_upwards [lt_mem_nhds ha] with t ht
    have hlog : HasDerivAt (fun s => Real.log (a / s)) (-(1 / t)) t := by
      have h : HasDerivAt (fun s => Real.log (a / s)) _ t :=
        ((hasDerivAt_const t a).div (hasDerivAt_id' t) ht.ne').log (div_pos ha ht).ne'
      convert h using 1
      simp only [Pi.div_apply]
      field_simp
      ring
    have h : HasDerivAt (lastDwlAV a α w) _ t :=
      ((hlog.const_mul (α * w)).neg).sub (last_revenue_hasDerivAt a (α * w) ht)
    convert h using 1
    simp only [hH]
    field_simp
  have hH' : HasDerivAt H (α * w / a ^ 2) a := by
    have h : HasDerivAt H _ a := (((hasDerivAt_id' a).sub_const a).div ((hasDerivAt_id' a).pow 2)
      (pow_ne_zero 2 ha.ne')).const_mul (α * w)
    convert h using 1
    simp only [Pi.pow_apply]
    field_simp
    ring
  exact last_quadratic_of_deriv hD hH' (by simp [lastDwlAV, div_self ha.ne'])
    (by simp [hH])

/-- Expansion of the mixed measure: `≈ α(1+α)w(s-a)²/(2a²)`. -/
theorem lastDwlMixed_expansion {a α w : ℝ} (ha : 0 < a) :
    (fun s => lastDwlMixed a α w s - α * (1 + α) * w / a ^ 2 / 2 * (s - a) ^ 2) =o[𝓝 a]
      fun s => (s - a) ^ 2 := by
  set H : ℝ → ℝ := fun s => w * (α * lastQ a α s / s) - α * w * a / s ^ 2 with hH
  have hD : ∀ᶠ t in 𝓝 a, HasDerivAt (lastDwlMixed a α w) (H t) t := by
    filter_upwards [lt_mem_nhds ha] with t ht
    have hq := lastQ_hasDerivAt (α := α) ha ht
    have h : HasDerivAt (lastDwlMixed a α w) _ t :=
      (((hasDerivAt_const t w).sub ((hasDerivAt_const t w).mul hq)).neg).sub
      (last_revenue_hasDerivAt a (α * w) ht)
    convert h using 1
    simp only [hH]
    ring
  have hH' : HasDerivAt H (α * (1 + α) * w / a ^ 2) a := by
    have hq := lastQ_hasDerivAt (α := α) ha ha
    have h : HasDerivAt H _ a :=
      (((hasDerivAt_const a α).mul hq).div (hasDerivAt_id' a) ha.ne').const_mul w |>.sub
      (last_inv_sq_hasDerivAt (α * w * a) ha)
    convert h using 1
    simp only [Pi.mul_apply, lastQ_self ha]
    field_simp
    ring
  exact last_quadratic_of_deriv hD hH' (by simp [lastDwlMixed, lastQ_self ha])
    (by simp only [hH, lastQ_self ha]; field_simp; ring)

/-- The price vector `p¹ = (s, p⁰₂)`: its first coordinate. -/
theorem last_priceLine_zero (p₀ : Fin 2 → ℝ) (s : ℝ) : priceLine p₀ 0 s 0 = s := by
  simp [priceLine]

/-- The price vector `p¹ = (s, p⁰₂)`: its second coordinate. -/
theorem last_priceLine_one (p₀ : Fin 2 → ℝ) (s : ℝ) : priceLine p₀ 0 s 1 = p₀ 1 := by
  simp [priceLine]

/-- For Cobb-Douglas, `e(p, v(p', w)) = w C(p')/C(p)`. -/
theorem last_cd_expenditure_indirect {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {p p' : Fin 2 → ℝ} (hp : StrictlyPositive p) (hp' : StrictlyPositive p') {w : ℝ}
    (hw : 0 < w) :
    expenditure (cobbDouglasUtility 1 α) p (indirectUtility (cobbDouglasUtility 1 α) p' w) =
      w * cdConst α p' / cdConst α p := by
  rw [example_3_D_2 hα0 hα1 hp' hw.le, cobbDouglasIndirect_eq hα0 hα1 hp' hw,
    (example_3_E_1 hα0 hα1 hp (mul_pos hw (cdConst_pos hα0 hα1 hp'))).1, cdExpenditure]

/-- `C(p⁰) = C(p¹) q(s)` for `p¹ = (s, p⁰₂)`. -/
theorem last_cdConst_priceLine {α : ℝ} (hα0 : 0 < α) {p₀ : Fin 2 → ℝ}
    (hp₀ : StrictlyPositive p₀) {s : ℝ} (hs : 0 < s) :
    cdConst α p₀ = cdConst α (priceLine p₀ 0 s) * lastQ (p₀ 0) α s := by
  unfold cdConst lastQ
  rw [last_priceLine_zero, last_priceLine_one]
  have h : (α / p₀ 0) ^ α = (α / s) ^ α * (s / p₀ 0) ^ α := by
    rw [← Real.mul_rpow (div_pos hα0 hs).le (div_pos hs (hp₀ 0)).le]
    congr 1
    field_simp
  rw [h]
  ring

/-- **Equation (3.I.5)** (MWG, p. 84) for Cobb-Douglas: `-τ x₁(p¹, w) - EV(p⁰, p¹, w)` in closed
form, `p¹ = (s, p⁰₂)`, `τ = s - p⁰₁`. -/
theorem last_cd_dwl_ev_eq {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {p₀ : Fin 2 → ℝ}
    (hp₀ : StrictlyPositive p₀) {s w : ℝ} (hs : 0 < s) (hw : 0 < w) :
    -((s - p₀ 0) * cobbDouglasDemand α (priceLine p₀ 0 s) w 0) -
        equivalentVariation (cobbDouglasUtility 1 α) p₀ (priceLine p₀ 0 s) w =
      lastDwlEV (p₀ 0) α w s := by
  have hp₁ := priceLine_pos hp₀ 0 hs
  have hC₀ := (cdConst_pos hα0 hα1 hp₀).ne'
  have hC₁ := (cdConst_pos hα0 hα1 hp₁).ne'
  have hq := (lastQ_pos (α := α) (hp₀ 0) hs).ne'
  unfold equivalentVariation lastDwlEV
  rw [last_cd_expenditure_indirect hα0 hα1 hp₀ hp₁ hw,
    last_cd_expenditure_indirect hα0 hα1 hp₀ hp₀ hw, last_cdConst_priceLine hα0 hp₀ hs]
  simp only [cobbDouglasDemand, Matrix.cons_val_zero, last_priceLine_zero]
  field_simp

/-- **Equation (3.I.6)** (MWG, p. 85) for Cobb-Douglas: `-CV(p⁰, p¹, w) - τ h₁(p¹, u⁰)` in
closed form. -/
theorem last_cd_dwl_cv_eq {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {p₀ : Fin 2 → ℝ}
    (hp₀ : StrictlyPositive p₀) {s w : ℝ} (hs : 0 < s) (hw : 0 < w) :
    -compensatingVariation (cobbDouglasUtility 1 α) p₀ (priceLine p₀ 0 s) w -
        (s - p₀ 0) * hicksianOf (cobbDouglasUtility 1 α) (cobbDouglasDemand α)
          (priceLine p₀ 0 s) (indirectUtility (cobbDouglasUtility 1 α) p₀ w) 0 =
      lastDwlCV (p₀ 0) α w s := by
  have hp₁ := priceLine_pos hp₀ 0 hs
  have hC₁ := (cdConst_pos hα0 hα1 hp₁).ne'
  unfold compensatingVariation lastDwlCV hicksianOf
  rw [last_cd_expenditure_indirect hα0 hα1 hp₁ hp₁ hw,
    last_cd_expenditure_indirect hα0 hα1 hp₁ hp₀ hw, last_cdConst_priceLine hα0 hp₀ hs]
  simp only [cobbDouglasDemand, Matrix.cons_val_zero, last_priceLine_zero]
  field_simp

/-- The mixed measure `-CV(p⁰, p¹, w) - τ x₁(p¹, w)` in closed form. -/
theorem last_cd_dwl_mixed_eq {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {p₀ : Fin 2 → ℝ}
    (hp₀ : StrictlyPositive p₀) {s w : ℝ} (hs : 0 < s) (hw : 0 < w) :
    -compensatingVariation (cobbDouglasUtility 1 α) p₀ (priceLine p₀ 0 s) w -
        (s - p₀ 0) * cobbDouglasDemand α (priceLine p₀ 0 s) w 0 =
      lastDwlMixed (p₀ 0) α w s := by
  have hp₁ := priceLine_pos hp₀ 0 hs
  have hC₁ := (cdConst_pos hα0 hα1 hp₁).ne'
  unfold compensatingVariation lastDwlMixed
  rw [last_cd_expenditure_indirect hα0 hα1 hp₁ hp₁ hw,
    last_cd_expenditure_indirect hα0 hα1 hp₁ hp₀ hw, last_cdConst_priceLine hα0 hp₀ hs]
  simp only [cobbDouglasDemand, Matrix.cons_val_zero, last_priceLine_zero]
  field_simp

/-- **Equation (3.I.8)** (MWG, p. 89) for Cobb-Douglas: the deadweight loss computed with the
area variation, `-AV(p⁰, p¹, w) - τ x₁(p¹, w)`, in closed form
(`AV = ∫_s^a αw/t dt = αw log(a/s)`). -/
theorem last_cd_dwl_av_eq (α : ℝ) {p₀ : Fin 2 → ℝ} (hp₀ : StrictlyPositive p₀) {s : ℝ}
    (hs : 0 < s) (w : ℝ) :
    -areaVariation (cobbDouglasDemand α) p₀ 0 (p₀ 0) s w -
        (s - p₀ 0) * cobbDouglasDemand α (priceLine p₀ 0 s) w 0 =
      lastDwlAV (p₀ 0) α w s := by
  have hAV : areaVariation (cobbDouglasDemand α) p₀ 0 (p₀ 0) s w =
      α * w * Real.log (p₀ 0 / s) := by
    unfold areaVariation
    have : (fun t => cobbDouglasDemand α (priceLine p₀ 0 t) w 0) = fun t => α * w * t⁻¹ := by
      funext t
      simp only [cobbDouglasDemand, Matrix.cons_val_zero, last_priceLine_zero]
      rw [div_eq_mul_inv]
    rw [this, intervalIntegral.integral_const_mul, integral_inv_of_pos hs (hp₀ 0)]
  unfold lastDwlAV
  rw [hAV]
  simp only [cobbDouglasDemand, Matrix.cons_val_zero, last_priceLine_zero]

/-- **Section 3.I** (MWG, p. 90, Figure 3.I.8), measure (3.I.5). For Cobb-Douglas utility and a
tax on good 1 raising its price from `a = p⁰₁` to `s`, the relative error of the deadweight loss
computed from the Walrasian demand curve, `(DWL_AV - DWL_EV)/DWL_EV`, tends to `α/(1-α) ≠ 0`
as `s → a`: it does not grow small with the price change. -/
theorem figure_3_I_8_ev {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {p₀ : Fin 2 → ℝ}
    (hp₀ : StrictlyPositive p₀) {w : ℝ} (hw : 0 < w) :
    Tendsto (fun s =>
      ((-areaVariation (cobbDouglasDemand α) p₀ 0 (p₀ 0) s w -
          (s - p₀ 0) * cobbDouglasDemand α (priceLine p₀ 0 s) w 0) -
        (-((s - p₀ 0) * cobbDouglasDemand α (priceLine p₀ 0 s) w 0) -
          equivalentVariation (cobbDouglasUtility 1 α) p₀ (priceLine p₀ 0 s) w)) /
        (-((s - p₀ 0) * cobbDouglasDemand α (priceLine p₀ 0 s) w 0) -
          equivalentVariation (cobbDouglasUtility 1 α) p₀ (priceLine p₀ 0 s) w))
      (𝓝[≠] (p₀ 0)) (𝓝 (α / (1 - α))) := by
  have ha := hp₀ 0
  have hc : α * (1 - α) * w / p₀ 0 ^ 2 / 2 ≠ 0 := by
    have : 0 < 1 - α := by linarith
    positivity
  have h := last_ratio_limit hc (lastDwlEV_expansion ha) (lastDwlAV_expansion (α := α) (w := w) ha)
  have hval : (α * w / p₀ 0 ^ 2 / 2 - α * (1 - α) * w / p₀ 0 ^ 2 / 2) /
      (α * (1 - α) * w / p₀ 0 ^ 2 / 2) = α / (1 - α) := by
    have : (1 - α) ≠ 0 := by linarith
    field_simp
    ring
  rw [hval] at h
  refine h.congr' ?_
  filter_upwards [nhdsWithin_le_nhds (lt_mem_nhds ha)] with s hs
  rw [last_cd_dwl_ev_eq hα0 hα1 hp₀ hs hw, last_cd_dwl_av_eq α hp₀ hs w]

/-- **Section 3.I** (MWG, p. 90, Figure 3.I.8), measure (3.I.6) (the figure's Hicksian demand
is at `u⁰`). For Cobb-Douglas utility, `(DWL_AV - DWL_CV)/DWL_CV → α/(1-α) ≠ 0` as `s → a`. -/
theorem figure_3_I_8_cv {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {p₀ : Fin 2 → ℝ}
    (hp₀ : StrictlyPositive p₀) {w : ℝ} (hw : 0 < w) :
    Tendsto (fun s =>
      ((-areaVariation (cobbDouglasDemand α) p₀ 0 (p₀ 0) s w -
          (s - p₀ 0) * cobbDouglasDemand α (priceLine p₀ 0 s) w 0) -
        (-compensatingVariation (cobbDouglasUtility 1 α) p₀ (priceLine p₀ 0 s) w -
          (s - p₀ 0) * hicksianOf (cobbDouglasUtility 1 α) (cobbDouglasDemand α)
            (priceLine p₀ 0 s) (indirectUtility (cobbDouglasUtility 1 α) p₀ w) 0)) /
        (-compensatingVariation (cobbDouglasUtility 1 α) p₀ (priceLine p₀ 0 s) w -
          (s - p₀ 0) * hicksianOf (cobbDouglasUtility 1 α) (cobbDouglasDemand α)
            (priceLine p₀ 0 s) (indirectUtility (cobbDouglasUtility 1 α) p₀ w) 0))
      (𝓝[≠] (p₀ 0)) (𝓝 (α / (1 - α))) := by
  have ha := hp₀ 0
  have hc : α * (1 - α) * w / p₀ 0 ^ 2 / 2 ≠ 0 := by
    have : 0 < 1 - α := by linarith
    positivity
  have h := last_ratio_limit hc (lastDwlCV_expansion ha) (lastDwlAV_expansion (α := α) (w := w) ha)
  have hval : (α * w / p₀ 0 ^ 2 / 2 - α * (1 - α) * w / p₀ 0 ^ 2 / 2) /
      (α * (1 - α) * w / p₀ 0 ^ 2 / 2) = α / (1 - α) := by
    have : (1 - α) ≠ 0 := by linarith
    field_simp
    ring
  rw [hval] at h
  refine h.congr' ?_
  filter_upwards [nhdsWithin_le_nhds (lt_mem_nhds ha)] with s hs
  rw [last_cd_dwl_cv_eq hα0 hα1 hp₀ hs hw, last_cd_dwl_av_eq α hp₀ hs w]

/-- **Section 3.I** (MWG, p. 90, Figure 3.I.8). "The percentage difference between these two
areas need not grow small as the price change grows small": there is a utility (Cobb-Douglas,
continuous, locally nonsatiated, strictly quasiconcave on the interior) for which the relative
error of the area-variation deadweight loss against the deadweight loss (3.I.6) has a nonzero
limit, while (p. 89) the area variation itself has vanishing relative error against the welfare
change (`welfare_av_relative_error`). -/
theorem figure_3_I_8 {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {p₀ : Fin 2 → ℝ}
    (hp₀ : StrictlyPositive p₀) {w : ℝ} (hw : 0 < w) :
    α / (1 - α) ≠ 0 ∧
      ¬ Tendsto (fun s =>
        ((-areaVariation (cobbDouglasDemand α) p₀ 0 (p₀ 0) s w -
            (s - p₀ 0) * cobbDouglasDemand α (priceLine p₀ 0 s) w 0) -
          (-compensatingVariation (cobbDouglasUtility 1 α) p₀ (priceLine p₀ 0 s) w -
            (s - p₀ 0) * hicksianOf (cobbDouglasUtility 1 α) (cobbDouglasDemand α)
              (priceLine p₀ 0 s) (indirectUtility (cobbDouglasUtility 1 α) p₀ w) 0)) /
          (-compensatingVariation (cobbDouglasUtility 1 α) p₀ (priceLine p₀ 0 s) w -
            (s - p₀ 0) * hicksianOf (cobbDouglasUtility 1 α) (cobbDouglasDemand α)
              (priceLine p₀ 0 s) (indirectUtility (cobbDouglasUtility 1 α) p₀ w) 0))
        (𝓝[≠] (p₀ 0)) (𝓝 0) := by
  have hne : α / (1 - α) ≠ 0 := by
    have : 0 < 1 - α := by linarith
    positivity
  refine ⟨hne, fun h0 => hne ?_⟩
  exact tendsto_nhds_unique (figure_3_I_8_cv hα0 hα1 hp₀ hw) h0

/-- **Footnote 29** (MWG, p. 90), the Cobb-Douglas computation of `docs/source-map-F2.md`. With
the mixed measure `M(s) = -CV(p⁰, p¹, w) - τ x₁(p¹, w)` (compensating variation minus the revenue
collected), `(DWL_AV - M)/M → -α/(α+1)` as `s → a`. (This is not one of the book's measures
(3.I.5)-(3.I.6), for which the limit is `α/(1-α)`; correction G-2.) -/
theorem footnote_3_I_29_mixed {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {p₀ : Fin 2 → ℝ}
    (hp₀ : StrictlyPositive p₀) {w : ℝ} (hw : 0 < w) :
    Tendsto (fun s =>
      ((-areaVariation (cobbDouglasDemand α) p₀ 0 (p₀ 0) s w -
          (s - p₀ 0) * cobbDouglasDemand α (priceLine p₀ 0 s) w 0) -
        (-compensatingVariation (cobbDouglasUtility 1 α) p₀ (priceLine p₀ 0 s) w -
          (s - p₀ 0) * cobbDouglasDemand α (priceLine p₀ 0 s) w 0)) /
        (-compensatingVariation (cobbDouglasUtility 1 α) p₀ (priceLine p₀ 0 s) w -
          (s - p₀ 0) * cobbDouglasDemand α (priceLine p₀ 0 s) w 0))
      (𝓝[≠] (p₀ 0)) (𝓝 (-α / (α + 1))) := by
  have ha := hp₀ 0
  have hc : α * (1 + α) * w / p₀ 0 ^ 2 / 2 ≠ 0 := by positivity
  have h := last_ratio_limit hc (lastDwlMixed_expansion ha)
    (lastDwlAV_expansion (α := α) (w := w) ha)
  have hval : (α * w / p₀ 0 ^ 2 / 2 - α * (1 + α) * w / p₀ 0 ^ 2 / 2) /
      (α * (1 + α) * w / p₀ 0 ^ 2 / 2) = -α / (α + 1) := by
    have : (α + 1) ≠ 0 := by linarith
    field_simp
    ring
  rw [hval] at h
  refine h.congr' ?_
  filter_upwards [nhdsWithin_le_nhds (lt_mem_nhds ha)] with s hs
  rw [last_cd_dwl_mixed_eq hα0 hα1 hp₀ hs hw, last_cd_dwl_av_eq α hp₀ hs w]

end MWG.ClassicalDemand
