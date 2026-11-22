/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPositiveEquilibriumTheory.NegishiLogEconomy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Exercise 17.AA.2: the sufficient condition for `g(s)` to be a function (MWG, p. 649)

The parenthesis of Exercise 17.AA.2: "a sufficient condition for this is that preferences be
representable by differentiable utility functions and that at every Pareto optimal allocation
at least one consumer gets a strictly positive consumption of every good".

* `aa2_support_pos`, `aa2_support_ker`: if `p` supports the upper contour set of `u` at an
  interior bundle `x ≫ 0` (`u(y) > u(x) ⟹ p·y > p·x` on `ℝ^L₊`) and `u` has derivative `D ≠ 0`
  at `x`, then `p·v > 0` whenever `Dv > 0`, and `p·v = 0` whenever `Dv = 0`.
* `aa2_support_unique`: hence `p` is a multiple of the gradient of `u` at `x`, and two such
  prices in the simplex coincide.
* `exercise_17_AA_2_sufficient`: with `Xᵢ = ℝ^L₊`, continuous strongly monotone utilities,
  `uᵢ(0) = 0`, `ωᵢ ≥ 0`, utilities differentiable with nonzero derivative at strictly positive
  bundles, and some consumer with a strictly positive bundle at every Pareto optimum, the
  normalized supporting price of `x(s)` is unique for every `s ∈ Δ` (the field `price_unique`
  of `NegishiHyp`). Instance: `logEconomy` (`exercise_17_AA_2_sufficient_instance`).

Departure: "differentiable" is read as differentiable with a nonzero derivative at the strictly
positive bundle (a differentiable utility with zero derivative there, such as `(v(x) - v(x̄))³`
for a `v` with a kinked indifference curve through `x̄`, does not determine the supporting
price).
-/

namespace MWG.PositiveEquilibriumTheory

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.GeneralEquilibriumExamples MWG.WelfareTheorems
open Filter Topology

variable {L : ℕ}

/-- A supporting price at an interior bundle `x ≫ 0` of a utility with derivative `D` at `x`
makes `p·v > 0` for every direction `v` with `Dv > 0`. -/
theorem aa2_support_pos {u : (Fin L → ℝ) → ℝ} {x p : Fin L → ℝ}
    {D : (Fin L → ℝ) →L[ℝ] ℝ} (hx : ∀ l, 0 < x l) (hD : HasFDerivAt u D x)
    (hsup : ∀ y ∈ nonnegOrthant L, u x < u y → p ⬝ᵥ x < p ⬝ᵥ y) {v : Fin L → ℝ}
    (hv : 0 < D v) : 0 < p ⬝ᵥ v := by
  -- `t ↦ u(x + t v)` has derivative `D v > 0` at `0`
  have hline : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hcomp : HasDerivAt (fun t : ℝ => u (x + t • v)) (D v) 0 := by
    have hD' : HasFDerivAt u D (x + (0 : ℝ) • v) := by simpa using hD
    exact hD'.comp_hasDerivAt (0 : ℝ) hline
  have hslope := (hasDerivAt_iff_tendsto_slope.1 hcomp).mono_left
    (nhdsWithin_mono _ fun t (ht : 0 < t) => (ne_of_gt ht : t ≠ 0))
  have hev1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < slope (fun t : ℝ => u (x + t • v)) 0 t :=
    hslope.eventually (lt_mem_nhds hv)
  -- `x + t v ≫ 0` for small `t`
  have hcont : Continuous fun t : ℝ => x + t • v := by fun_prop
  have hev2 : ∀ᶠ t in 𝓝 (0 : ℝ), x + t • v ∈ posOrthant L := by
    have hopen : IsOpen (posOrthant L) := by
      have : posOrthant L = ⋂ l, {q : Fin L → ℝ | 0 < q l} := by ext q; simp [posOrthant,
        StrictlyPositive]
      rw [this]
      exact isOpen_iInter_of_finite fun l => isOpen_lt continuous_const (continuous_apply l)
    exact hcont.continuousAt.preimage_mem_nhds (by simpa using hopen.mem_nhds hx)
  obtain ⟨t, h1, h2, h3⟩ := (hev1.and ((hev2.filter_mono nhdsWithin_le_nhds).and
    self_mem_nhdsWithin)).exists
  have ht : (0 : ℝ) < t := h3
  rw [slope_def_field] at h1
  simp only [zero_smul, add_zero, sub_zero] at h1
  have hlt : u x < u (x + t • v) := by
    have := (div_pos_iff_of_pos_right ht).1 h1
    linarith
  have := hsup _ (fun l => (h2 l).le) hlt
  rw [dotProduct_add, dotProduct_smul, smul_eq_mul] at this
  have : 0 < t * (p ⬝ᵥ v) := by linarith
  exact (pos_iff_pos_of_mul_pos this).1 ht

/-- A supporting price at an interior bundle `x ≫ 0` of a utility with derivative `D ≠ 0` at `x`
annihilates the kernel of `D`. -/
theorem aa2_support_ker {u : (Fin L → ℝ) → ℝ} {x p : Fin L → ℝ}
    {D : (Fin L → ℝ) →L[ℝ] ℝ} (hx : ∀ l, 0 < x l) (hD : HasFDerivAt u D x) (hD0 : D ≠ 0)
    (hsup : ∀ y ∈ nonnegOrthant L, u x < u y → p ⬝ᵥ x < p ⬝ᵥ y) {v : Fin L → ℝ}
    (hv : D v = 0) : p ⬝ᵥ v = 0 := by
  obtain ⟨w0, hw0⟩ : ∃ w, D w ≠ 0 := by
    by_contra h
    push Not at h
    exact hD0 (ContinuousLinearMap.ext h)
  obtain ⟨w, hw⟩ : ∃ w, 0 < D w := by
    rcases lt_or_gt_of_ne hw0 with h | h
    · exact ⟨-w0, by rw [map_neg]; linarith⟩
    · exact ⟨w0, h⟩
  have hpw := aa2_support_pos hx hD hsup hw
  -- `p·v ≥ 0` for every `v` in the kernel, applied to `v` and `-v`
  have hge : ∀ v, D v = 0 → 0 ≤ p ⬝ᵥ v := by
    intro v hv
    by_contra hneg
    push Not at hneg
    set ε := -(p ⬝ᵥ v) / (2 * (p ⬝ᵥ w)) with hε
    have hεpos : 0 < ε := div_pos (by linarith) (by linarith)
    have hD' : 0 < D (v + ε • w) := by
      rw [map_add, map_smul, hv, smul_eq_mul, zero_add]
      exact mul_pos hεpos hw
    have := aa2_support_pos hx hD hsup hD'
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul, hε] at this
    have e : -(p ⬝ᵥ v) / (2 * (p ⬝ᵥ w)) * (p ⬝ᵥ w) = -(p ⬝ᵥ v) / 2 := by
      field_simp
    linarith
  have h1 := hge v hv
  have h2 := hge (-v) (by rw [map_neg, hv, neg_zero])
  rw [dotProduct_neg] at h2
  linarith

/-- The derivative of `u` at `x` in coordinates: `Dv = g·v` with `gₗ = D eₗ`. -/
theorem aa2_grad (D : (Fin L → ℝ) →L[ℝ] ℝ) (v : Fin L → ℝ) :
    D v = (fun l => D (Pi.single l 1)) ⬝ᵥ v := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum, dotProduct]
  refine Finset.sum_congr rfl fun l _ => ?_
  have : (Pi.single l (v l) : Fin L → ℝ) = v l • (Pi.single l 1 : Fin L → ℝ) := by
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  rw [this, map_smul, smul_eq_mul, mul_comm]

/-- **Exercise 17.AA.2** (MWG, p. 649), the mechanism of the sufficient condition: at an interior
bundle where `u` has a nonzero derivative, a supporting price is a multiple of the gradient, so
there is only one supporting price in the simplex. -/
theorem aa2_support_unique {u : (Fin L → ℝ) → ℝ} {x p q : Fin L → ℝ}
    {D : (Fin L → ℝ) →L[ℝ] ℝ} (hx : ∀ l, 0 < x l) (hD : HasFDerivAt u D x) (hD0 : D ≠ 0)
    (hp : p ∈ priceSimplex L) (hq : q ∈ priceSimplex L)
    (hsp : ∀ y ∈ nonnegOrthant L, u x < u y → p ⬝ᵥ x < p ⬝ᵥ y)
    (hsq : ∀ y ∈ nonnegOrthant L, u x < u y → q ⬝ᵥ x < q ⬝ᵥ y) : p = q := by
  set g : Fin L → ℝ := fun l => D (Pi.single l 1) with hg
  have hDg : ∀ v, D v = g ⬝ᵥ v := aa2_grad D
  have hg0 : g ⬝ᵥ g ≠ 0 := by
    intro h
    apply hD0
    refine ContinuousLinearMap.ext fun v => ?_
    rw [hDg, dotProduct_self_eq_zero.1 h, zero_dotProduct]
    rfl
  -- every supporting price in the simplex is `(r·g / g·g) g`
  have hmul : ∀ r : Fin L → ℝ, (∀ y ∈ nonnegOrthant L, u x < u y → r ⬝ᵥ x < r ⬝ᵥ y) →
      r = ((r ⬝ᵥ g) / (g ⬝ᵥ g)) • g := by
    intro r hr
    set w := r - ((r ⬝ᵥ g) / (g ⬝ᵥ g)) • g with hw
    have hgw : g ⬝ᵥ w = 0 := by
      rw [hw, dotProduct_sub, dotProduct_smul, smul_eq_mul, dotProduct_comm g r]
      field_simp
      ring
    have hrw : r ⬝ᵥ w = 0 := aa2_support_ker hx hD hD0 hr (by rw [hDg, hgw])
    have hww : w ⬝ᵥ w = 0 := by
      have : w ⬝ᵥ w = r ⬝ᵥ w - ((r ⬝ᵥ g) / (g ⬝ᵥ g)) * (g ⬝ᵥ w) := by
        conv_lhs => rw [hw]
        rw [sub_dotProduct, smul_dotProduct, smul_eq_mul]
      rw [this, hrw, hgw, mul_zero, sub_zero]
    have := dotProduct_self_eq_zero.1 hww
    rw [hw] at this
    exact sub_eq_zero.1 this
  have ep := hmul p hsp
  have eq := hmul q hsq
  set a := (p ⬝ᵥ g) / (g ⬝ᵥ g)
  set b := (q ⬝ᵥ g) / (g ⬝ᵥ g)
  have hsa : a * ∑ l, g l = 1 := by
    have := hp.2
    rw [ep] at this
    simpa [Finset.mul_sum] using this
  have hsb : b * ∑ l, g l = 1 := by
    have := hq.2
    rw [eq] at this
    simpa [Finset.mul_sum] using this
  have hab : a = b := by
    have hS : ∑ l, g l ≠ 0 := fun h => by rw [h, mul_zero] at hsa; exact zero_ne_one hsa
    exact mul_right_cancel₀ hS (hsa.trans hsb.symm)
  rw [ep, eq, hab]

variable {I : ℕ}

/-- **Exercise 17.AA.2** (MWG, p. 649), the parenthetical sufficient condition. Let `Xᵢ = ℝ^L₊`,
utilities continuous and strongly monotone with `uᵢ(0) = 0`, `ωᵢ ≥ 0`. Suppose every `uᵢ` is
differentiable with a nonzero derivative at every strictly positive bundle, and at every Pareto
optimal allocation some consumer consumes a strictly positive amount of every good. Then for
every `s ∈ Δ` the supporting price of `x(s)` in `Δ` is unique: `g(s)` is a function. -/
theorem exercise_17_AA_2_sufficient {E : ExchangeEconomy (Fin I) L}
    (hX : ∀ i, E.X i = nonnegOrthant L) (hc : ∀ i, ContinuousOn (E.u i) (nonnegOrthant L))
    (hm : ∀ i, UtilityStronglyMonotone (E.u i)) (hu0 : ∀ i, E.u i 0 = 0)
    (hω : ∀ i, E.ω i ∈ nonnegOrthant L)
    (hdiff : ∀ i, ∀ y : Fin L → ℝ, (∀ l, 0 < y l) →
      ∃ D : (Fin L → ℝ) →L[ℝ] ℝ, HasFDerivAt (E.u i) D y ∧ D ≠ 0)
    (hint : ∀ x, E.IsParetoOptimal x → ∃ i, ∀ l, 0 < x i l) :
    ∀ s ∈ priceSimplex I, ∀ p q, p ∈ priceSimplex L → q ∈ priceSimplex L →
      IsSupportingPrice E (negishiAlloc E s) p → IsSupportingPrice E (negishiAlloc E s) q →
        p = q := by
  intro s hs p q hp hq hsp hsq
  obtain ⟨i, hi⟩ := hint _ (negishiAlloc_spec hX hc hm hu0 hω hs).1
  obtain ⟨D, hD, hD0⟩ := hdiff i _ hi
  exact aa2_support_unique hi hD hD0 hp hq (fun y hy hlt => hsp i y (by rw [hX i]; exact hy) hlt)
    (fun y hy hlt => hsq i y (by rw [hX i]; exact hy) hlt)

/-- `logU` has a nonzero derivative at every strictly positive bundle. -/
theorem logU_hasFDerivAt {y : Fin 2 → ℝ} (hy : ∀ l, 0 < y l) :
    ∃ D : (Fin 2 → ℝ) →L[ℝ] ℝ, HasFDerivAt logU D y ∧ D ≠ 0 := by
  have h0 : (1 + y 0) ≠ 0 := by linarith [hy 0]
  have h1 : (1 + y 1) ≠ 0 := by linarith [hy 1]
  have hd0 := ((hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) y).const_add 1).log h0
  have hd1 := ((hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) y).const_add 1).log h1
  refine ⟨_, hd0.add hd1, fun hD => ?_⟩
  have := congrArg (fun D : (Fin 2 → ℝ) →L[ℝ] ℝ => D (Pi.single 0 1)) hD
  exact h0 (by simpa using this)

/-- **Exercise 17.AA.2** (MWG, p. 649), instance of the sufficient condition: in `logEconomy`
(utilities `log(1 + x₁) + log(1 + x₂)`) the hypotheses of `exercise_17_AA_2_sufficient` hold
(every Pareto optimum is `x₁ = (a, a)`, `x₂ = (2 - a, 2 - a)`, so one consumer has `≥ (1, 1)`). -/
theorem exercise_17_AA_2_sufficient_instance :
    ∀ s ∈ priceSimplex 2, ∀ p q, p ∈ priceSimplex 2 → q ∈ priceSimplex 2 →
      IsSupportingPrice logEconomy (negishiAlloc logEconomy s) p →
        IsSupportingPrice logEconomy (negishiAlloc logEconomy s) q → p = q := by
  have h := logEconomy_negishiHyp
  refine exercise_17_AA_2_sufficient h.X_eq (fun i => (h.standard i).1)
    (fun i => (h.standard i).2.2) h.u_zero h.ω_mem (fun _ y hy => logU_hasFDerivAt hy) ?_
  intro x hpo
  obtain ⟨h01, h10, h11, -⟩ := logEconomy_diag hpo
  rcases le_or_gt 1 (x 0 0) with ha | ha
  · refine ⟨0, fun l => ?_⟩
    fin_cases l
    · change 0 < x 0 0; linarith
    · change 0 < x 0 1; linarith
  · refine ⟨1, fun l => ?_⟩
    fin_cases l
    · change 0 < x 1 0; linarith
    · change 0 < x 1 1; linarith

end MWG.PositiveEquilibriumTheory
