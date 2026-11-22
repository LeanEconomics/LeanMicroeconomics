/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGMechanismDesign.OptimalAuction
import MWGMechanismDesign.DanaSpier

/-!
# Completing a monotone allocation rule by envelope transfers

MWG, Section 23.D, Proposition 23.D.2 (p. 888), sufficiency half, used in Example 23.F.2
(p. 905): "the optimal transfer functions can then be set as `tᵢ(θ) = Uᵢ(θᵢ) - θᵢȳᵢ(θᵢ)`, where
`Uᵢ(θᵢ)` is calculated from constraint (iii)".

* `ecTransfer`: given an allocation rule `y` with independent types with densities, the
  envelope transfers `tᵢ(θ) = cᵢ + ∫_{θ̲ᵢ}^{θᵢ} ȳᵢ - θᵢȳᵢ(θᵢ)`.
* `ec_mechanism`: if every `yᵢ` is measurable, bounded by `1` in absolute value and
  nondecreasing in the agent's own type (for every profile of the others), then `(y, t)` is
  Bayesian incentive compatible, the expectations exist, and `Uᵢ(θᵢ) = cᵢ + ∫_{θ̲ᵢ}^{θᵢ} ȳᵢ`.
* **Example 23.F.2** for general densities (`example_23_F_2_general`): with every virtual
  valuation `Jᵢ` nondecreasing on `[θ̲ᵢ, θ̄ᵢ]` (MWG's assumption), the rule `oaRule` (the good
  goes to the bidder with the largest positive `Jᵢ(θᵢ)`, ties to the lowest index) solves the
  relaxed problem (23.F.8) at every profile, has `yᵢ` nondecreasing in `θᵢ`, and with the
  envelope transfers (`cᵢ = 0`, so `Uᵢ(θ̲ᵢ) = 0`) is a feasible mechanism that maximises the
  seller's expected revenue among all feasible social choice functions. Instance: two bidders
  uniform on `[0, 1]` and `[0, 2]` (`example_23_F_2_general_instance`).

Departure: MWG leave ties `Jᵢ = max{0, maxₖ≠ᵢ Jₖ}` free, saying they have probability zero;
that is not true when some `Jᵢ` is constant on an interval, so the rule breaks ties by a fixed
order of the bidders, which keeps `yᵢ` nondecreasing in `θᵢ`.
-/

namespace MWG.MechanismDesign

open MeasureTheory Function

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Example 23.F.2** (MWG, p. 905) and Proposition 23.D.2: the envelope transfers
`tᵢ(θ) = cᵢ + ∫_{θ̲ᵢ}^{θᵢ} ȳᵢ(s) ds - θᵢȳᵢ(θᵢ)` completing an allocation rule `y`. -/
noncomputable def ecTransfer (D : ι → TypeDensity) (y : (ι → ℝ) → ι → ℝ) (c : ι → ℝ) :
    (ι → ℝ) → ι → ℝ :=
  fun θ i => c i + (∫ s in (D i).lo..(θ i),
      interimBenefit (Measure.pi fun j => (D j).measure) allocV y i s) -
    θ i * interimBenefit (Measure.pi fun j => (D j).measure) allocV y i (θ i)

/-- With `yᵢ` measurable and `|yᵢ| ≤ 1`, `yᵢ(a, θ₋ᵢ)` is integrable for every announcement. -/
theorem ec_integrable_update (D : ι → TypeDensity) {y : (ι → ℝ) → ι → ℝ}
    (hym : ∀ i, Measurable fun θ => y θ i) (hyb : ∀ θ i, |y θ i| ≤ 1) (i : ι) (a : ℝ) :
    Integrable (fun θ' => y (update θ' i a) i) (Measure.pi fun j => (D j).measure) := by
  have : ∀ j, IsProbabilityMeasure (D j).measure := fun j => (D j).isProbabilityMeasure
  exact Integrable.of_bound ((hym i).comp measurable_update_left).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun θ' => by rw [Real.norm_eq_abs]; exact hyb _ i)

/-- `|ȳᵢ| ≤ 1` when `|yᵢ| ≤ 1`. -/
theorem ec_interimBenefit_abs_le (D : ι → TypeDensity) {y : (ι → ℝ) → ι → ℝ}
    (hyb : ∀ θ i, |y θ i| ≤ 1) (i : ι) (a : ℝ) :
    |interimBenefit (Measure.pi fun j => (D j).measure) allocV y i a| ≤ 1 := by
  have : ∀ j, IsProbabilityMeasure (D j).measure := fun j => (D j).isProbabilityMeasure
  have h := norm_integral_le_of_norm_le_const (μ := Measure.pi fun j => (D j).measure)
    (f := fun θ' => y (update θ' i a) i) (C := 1)
    (Filter.Eventually.of_forall fun θ' => by rw [Real.norm_eq_abs]; exact hyb _ i)
  rw [probReal_univ, mul_one, Real.norm_eq_abs] at h
  exact h

/-- If `yᵢ` is nondecreasing in the agent's own type for every `θ₋ᵢ`, so is `ȳᵢ`. -/
theorem ec_interimBenefit_mono (D : ι → TypeDensity) {y : (ι → ℝ) → ι → ℝ}
    (hym : ∀ i, Measurable fun θ => y θ i) (hyb : ∀ θ i, |y θ i| ≤ 1)
    (hmono : ∀ i θ', ∀ a ∈ Set.Icc (D i).lo (D i).hi, ∀ b ∈ Set.Icc (D i).lo (D i).hi, a ≤ b →
      y (update θ' i a) i ≤ y (update θ' i b) i) (i : ι) :
    MonotoneOn (interimBenefit (Measure.pi fun j => (D j).measure) allocV y i)
      (Set.Icc (D i).lo (D i).hi) := fun a ha b hb hab =>
  integral_mono (ec_integrable_update D hym hyb i a) (ec_integrable_update D hym hyb i b)
    fun θ' => hmono i θ' a ha b hb hab

/-- **Proposition 23.D.2** (MWG, p. 888), sufficiency half, as used in Example 23.F.2 (p. 905):
an allocation rule `y` that is measurable, bounded (`|yᵢ| ≤ 1`) and nondecreasing in each
agent's own type, completed by the envelope transfers `ecTransfer`, is Bayesian incentive
compatible, its expectations exist, and `Uᵢ(θᵢ) = cᵢ + ∫_{θ̲ᵢ}^{θᵢ} ȳᵢ`. -/
theorem ec_mechanism (D : ι → TypeDensity) {y : (ι → ℝ) → ι → ℝ}
    (hym : ∀ i, Measurable fun θ => y θ i) (hyb : ∀ θ i, |y θ i| ≤ 1)
    (hmono : ∀ i θ', ∀ a ∈ Set.Icc (D i).lo (D i).hi, ∀ b ∈ Set.Icc (D i).lo (D i).hi, a ≤ b →
      y (update θ' i a) i ≤ y (update θ' i b) i) (c : ι → ℝ) :
    InterimIntegrable (Measure.pi fun j => (D j).measure) allocV y (ecTransfer D y c)
        (fun i => (D i).lo) (fun i => (D i).hi) ∧
      BayesianICOn (Measure.pi fun j => (D j).measure) allocV y (ecTransfer D y c)
        (fun i => (D i).lo) (fun i => (D i).hi) ∧
      (∀ i, Integrable (fun θ => ecTransfer D y c θ i) (Measure.pi fun j => (D j).measure)) ∧
      ∀ i a, interimU (Measure.pi fun j => (D j).measure) allocV y (ecTransfer D y c) i a =
        c i + ∫ s in (D i).lo..a, interimBenefit (Measure.pi fun j => (D j).measure) allocV y i s
  := by
  have : ∀ j, IsProbabilityMeasure (D j).measure := fun j => (D j).isProbabilityMeasure
  set P := Measure.pi fun j => (D j).measure with hP
  have hmon := ec_interimBenefit_mono D hym hyb hmono
  have hU : ∀ i a, interimU P allocV y (ecTransfer D y c) i a =
      c i + ∫ s in (D i).lo..a, interimBenefit P allocV y i s := by
    intro i a
    simp only [interimU, interimTransfer, ecTransfer, update_self, integral_const, probReal_univ,
      one_smul]
    ring
  have hint : InterimIntegrable P allocV y (ecTransfer D y c) (fun i => (D i).lo)
      (fun i => (D i).hi) := by
    intro i a _
    refine ⟨ec_integrable_update D hym hyb i a, ?_⟩
    simp only [ecTransfer, update_self]
    exact integrable_const _
  refine ⟨hint, (proposition_23_D_2 hint).2 fun i => ⟨hmon i, fun θ _ => ?_⟩, fun i => ?_, hU⟩
  · rw [hU, hU, intervalIntegral.integral_same, add_zero]
  · -- the transfer is a bounded, a.e. strongly measurable function of `θᵢ`
    set E := D i with hE
    have hle : E.lo ≤ E.hi := E.lo_lt_hi.le
    have hprim : ContinuousOn (fun x => ∫ s in E.lo..x, interimBenefit P allocV y i s)
        (Set.Icc E.lo E.hi) := by
      rw [← Set.uIcc_of_le hle]
      refine intervalIntegral.continuousOn_primitive_interval ?_
      rw [Set.uIcc_of_le hle]
      exact (hmon i).integrableOn_isCompact isCompact_Icc
    have hG : AEStronglyMeasurable (fun x => c i + (∫ s in E.lo..x,
        interimBenefit P allocV y i s) - x * interimBenefit P allocV y i x) E.measure :=
      (aestronglyMeasurable_const.add ((hprim.aestronglyMeasurable measurableSet_Icc).mono_ac
        E.absolutelyContinuous)).sub
        (continuous_id.aestronglyMeasurable.mul (E.aestronglyMeasurable_of_monotoneOn (hmon i)))
    have hGi : Integrable (fun x => c i + (∫ s in E.lo..x,
        interimBenefit P allocV y i s) - x * interimBenefit P allocV y i x) E.measure := by
      refine Integrable.of_bound hG (|c i| + (E.hi - E.lo) + (|E.lo| + |E.hi|)) ?_
      filter_upwards [mem_ae_iff.2 E.measure_compl_Icc] with x hx
      have h1 : |∫ s in E.lo..x, interimBenefit P allocV y i s| ≤ 1 * |x - E.lo| := by
        have := intervalIntegral.norm_integral_le_of_norm_le_const (a := E.lo) (b := x)
          (C := 1) (f := interimBenefit P allocV y i) fun s _ => by
            rw [Real.norm_eq_abs]; exact ec_interimBenefit_abs_le D hyb i s
        rwa [Real.norm_eq_abs] at this
      have h2 : |x * interimBenefit P allocV y i x| ≤ |x| * 1 := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (ec_interimBenefit_abs_le D hyb i x) (abs_nonneg x)
      have h3 : |x - E.lo| ≤ E.hi - E.lo := by
        rw [abs_of_nonneg (by linarith [hx.1])]; linarith [hx.2]
      have h4 : |x| ≤ |E.lo| + |E.hi| := re_abs_le_of_mem hx
      rw [Real.norm_eq_abs]
      calc |c i + (∫ s in E.lo..x, interimBenefit P allocV y i s) -
            x * interimBenefit P allocV y i x|
          ≤ |c i| + |∫ s in E.lo..x, interimBenefit P allocV y i s| +
            |x * interimBenefit P allocV y i x| := by
            refine (abs_sub _ _).trans ?_
            exact add_le_add (abs_add_le _ _) le_rfl
        _ ≤ |c i| + (E.hi - E.lo) + (|E.lo| + |E.hi|) := by nlinarith
    exact integrable_comp_eval (μ := fun j => (D j).measure) (i := i) hGi

/-! ### Example 23.F.2 for general densities -/

/-- **Example 23.F.2** (MWG, p. 905): bidder `i` wins under the (23.F.9) rule at virtual
valuations `J`: `Jᵢ(θᵢ) > 0` and `Jᵢ(θᵢ)` is the largest virtual valuation, ties going to the
lowest index. -/
def oaWins {n : ℕ} (J : Fin n → ℝ → ℝ) (θ : Fin n → ℝ) (i : Fin n) : Prop :=
  0 < J i (θ i) ∧ ∀ k, J k (θ k) < J i (θ i) ∨ (J k (θ k) = J i (θ i) ∧ i ≤ k)

open Classical in
/-- **Example 23.F.2** (MWG, p. 905), the pointwise rule (23.F.9) with a fixed tie-break: the
good goes to the bidder with the largest positive virtual valuation `Jᵢ(θᵢ)` (lowest index on a
tie) and is kept if all `Jᵢ(θᵢ) ≤ 0`. -/
noncomputable def oaRule {n : ℕ} (D : Fin n → TypeDensity) : (Fin n → ℝ) → Fin n → ℝ :=
  fun θ i => if oaWins (fun k => (D k).virtualValue) θ i then 1 else 0

/-- At most one bidder wins. -/
theorem oa_wins_unique {n : ℕ} {J : Fin n → ℝ → ℝ} {θ : Fin n → ℝ} {i j : Fin n}
    (hi : oaWins J θ i) (hj : oaWins J θ j) : i = j := by
  rcases hi.2 j with h1 | ⟨h1, h1'⟩ <;> rcases hj.2 i with h2 | ⟨h2, h2'⟩
  · linarith
  · linarith
  · linarith
  · exact le_antisymm h1' h2'

/-- If some virtual valuation is positive, some bidder wins. -/
theorem oa_exists_wins {n : ℕ} {J : Fin n → ℝ → ℝ} {θ : Fin n → ℝ} {k : Fin n}
    (hk : 0 < J k (θ k)) : ∃ i, oaWins J θ i := by
  obtain ⟨m, -, hm⟩ := Finset.exists_max_image Finset.univ (fun l => J l (θ l))
    ⟨k, Finset.mem_univ k⟩
  set S := Finset.univ.filter fun l => J l (θ l) = J m (θ m) with hS
  have hSne : S.Nonempty := ⟨m, by simp [hS]⟩
  set i := S.min' hSne with hi
  have hiS : i ∈ S := S.min'_mem hSne
  have hJi : J i (θ i) = J m (θ m) := (Finset.mem_filter.1 hiS).2
  refine ⟨i, ⟨?_, fun l => ?_⟩⟩
  · rw [hJi]; exact lt_of_lt_of_le hk (hm k (Finset.mem_univ k))
  · rcases lt_or_eq_of_le (hm l (Finset.mem_univ l)) with h | h
    · left; rw [hJi]; exact h
    · right
      refine ⟨by rw [hJi, h], S.min'_le l ?_⟩
      simp [hS, h]

/-- The rule gives a feasible allocation and solves the relaxed problem (23.F.8) at every
profile (for any virtual valuations). -/
theorem oaRule_pointwiseOpt {n : ℕ} (D : Fin n → TypeDensity) (θ : Fin n → ℝ) :
    PointwiseOptAlloc (fun i => (D i).virtualValue (θ i)) (oaRule D θ) := by
  classical
  set J : Fin n → ℝ → ℝ := fun k => (D k).virtualValue with hJ
  have hy : ∀ i, oaRule D θ i = if oaWins J θ i then 1 else 0 := fun i => by
    simp only [oaRule, hJ]
  have hsum : ∀ w : Fin n → ℝ, ∀ i, oaWins J θ i →
      ∑ k, oaRule D θ k * w k = w i := by
    intro w i hi
    rw [Finset.sum_eq_single i (fun k _ hk => by
      have hk' : ¬oaWins J θ k := fun hk' => hk (oa_wins_unique hk' hi)
      simp [hy, hk'])
      (fun h => absurd (Finset.mem_univ i) h)]
    simp [hy, hi]
  have hfeas : FeasAlloc (oaRule D θ) := by
    refine ⟨fun i => by rw [hy]; split_ifs <;> norm_num, ?_⟩
    by_cases hw : ∃ i, oaWins J θ i
    · obtain ⟨i, hi⟩ := hw
      have := hsum (fun _ => 1) i hi
      simp only [mul_one] at this
      rw [this]
    · push Not at hw
      simp [hy, hw]
  refine ⟨hfeas, fun w' ⟨hw0, hw1⟩ => ?_⟩
  by_cases hw : ∃ i, oaWins J θ i
  · obtain ⟨i, hi⟩ := hw
    have h1 := hsum (fun k => J k (θ k)) i hi
    simp only [hJ] at h1
    rw [h1]
    have hle : ∀ k, J k (θ k) ≤ J i (θ i) := fun k => by
      rcases hi.2 k with h | ⟨h, -⟩
      · exact h.le
      · exact h.le
    calc ∑ k, w' k * (D k).virtualValue (θ k) ≤ ∑ k, w' k * J i (θ i) :=
          Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hle k) (hw0 k)
      _ = (∑ k, w' k) * J i (θ i) := by rw [Finset.sum_mul]
      _ ≤ 1 * J i (θ i) := mul_le_mul_of_nonneg_right hw1 hi.1.le
      _ = (D i).virtualValue (θ i) := by rw [one_mul]
  · push Not at hw
    have hneg : ∀ k, J k (θ k) ≤ 0 := fun k => by
      by_contra h
      obtain ⟨i, hi⟩ := oa_exists_wins (J := J) (θ := θ) (not_le.1 h)
      exact hw i hi
    have h0 : ∑ k, oaRule D θ k * (D k).virtualValue (θ k) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [hy, hw k]
    rw [h0]
    exact Finset.sum_nonpos fun k _ => mul_nonpos_of_nonneg_of_nonpos (hw0 k) (hneg k)

/-- **Example 23.F.2** (MWG, p. 905): with `Jᵢ` nondecreasing, the rule's `yᵢ` is
nondecreasing in `θᵢ` for every profile of the other bidders' types. -/
theorem oaRule_mono {n : ℕ} (D : Fin n → TypeDensity)
    (hJ : ∀ i, MonotoneOn (D i).virtualValue (Set.Icc (D i).lo (D i).hi)) (i : Fin n)
    (θ' : Fin n → ℝ) {a b : ℝ} (ha : a ∈ Set.Icc (D i).lo (D i).hi)
    (hb : b ∈ Set.Icc (D i).lo (D i).hi) (hab : a ≤ b) :
    oaRule D (update θ' i a) i ≤ oaRule D (update θ' i b) i := by
  classical
  have hJab := hJ i ha hb hab
  simp only [oaRule]
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exfalso
    apply h2
    simp only [oaWins, update_self] at h1 ⊢
    refine ⟨lt_of_lt_of_le h1.1 hJab, fun k => ?_⟩
    by_cases hk : k = i
    · subst hk; right; simp
    · rcases h1.2 k with h | ⟨h, h'⟩
      · left; rw [update_of_ne hk] at h ⊢; linarith
      · rw [update_of_ne hk] at h ⊢
        rcases lt_or_eq_of_le hJab with hlt | heq
        · left; linarith
        · right; exact ⟨by rw [h, heq], h'⟩
  · norm_num
  · exact le_rfl

/-- The virtual valuation is measurable. -/
theorem oa_measurable_virtualValue (D : TypeDensity) : Measurable D.virtualValue :=
  measurable_id.sub (((continuous_const.sub D.continuous_cdf).measurable).div D.measurable_dens)

/-- The virtual valuation has an expectation: `Jφ = θφ - (1 - Φ)` on `[θ̲, θ̄]`. -/
theorem oa_integrable_virtualValue (D : TypeDensity) : Integrable D.virtualValue D.measure :=
  mss_integrable_of_mul_dens D (h := fun x => x * D.dens x - (1 - D.cdf x))
    ((mss_ii_mul_dens D continuous_id _ _).sub
      ((continuous_const.sub D.continuous_cdf).intervalIntegrable _ _)) fun x hx => by
      have := (D.dens_pos x hx).ne'
      simp only [TypeDensity.virtualValue]
      rw [sub_mul, div_mul_cancel₀ _ this]

/-- The rule is measurable. -/
theorem oaRule_measurable {n : ℕ} (D : Fin n → TypeDensity) (i : Fin n) :
    Measurable fun θ => oaRule D θ i := by
  classical
  have hJ : ∀ k, Measurable fun θ : Fin n → ℝ => (D k).virtualValue (θ k) := fun k =>
    (oa_measurable_virtualValue (D k)).comp (measurable_pi_apply k)
  refine Measurable.ite ?_ measurable_const measurable_const
  refine measurableSet_setOfPred.2 (Measurable.and (measurableSet_setOfPred.1
    (measurableSet_lt measurable_const (hJ i))) (Measurable.forall fun k => Measurable.or
      (measurableSet_setOfPred.1 (measurableSet_lt (hJ k) (hJ i)))
      (Measurable.and (measurableSet_setOfPred.1 (measurableSet_eq_fun (hJ k) (hJ i)))
        measurable_const)))

/-- **Example 23.F.2** (MWG, pp. 904-905) for general densities: suppose every virtual valuation
`Jᵢ(θᵢ) = θᵢ - (1 - Φᵢ(θᵢ))/φᵢ(θᵢ)` is nondecreasing on `[θ̲ᵢ, θ̄ᵢ]`. Then the rule (23.F.9)
(`oaRule`, ties to the lowest index) completed by the transfers
`tᵢ(θ) = Uᵢ(θᵢ) - θᵢȳᵢ(θᵢ)`, `Uᵢ(θᵢ) = ∫_{θ̲ᵢ}^{θᵢ} ȳᵢ` (constraint (iii) with `Uᵢ(θ̲ᵢ) = 0`), is
a feasible mechanism (constraints (i)-(iv)), it solves the relaxed problem (23.F.8) at every
profile, and it maximises the seller's expected revenue among all feasible social choice
functions. -/
theorem example_23_F_2_general {n : ℕ} (D : Fin n → TypeDensity)
    (hJ : ∀ i, MonotoneOn (D i).virtualValue (Set.Icc (D i).lo (D i).hi)) :
    OptAuctionFeasible D (oaRule D) (ecTransfer D (oaRule D) 0) ∧
      (∀ i, interimU (Measure.pi fun j => (D j).measure) allocV (oaRule D)
        (ecTransfer D (oaRule D) 0) i (D i).lo = 0) ∧
      (∀ θ, PointwiseOptAlloc (fun i => (D i).virtualValue (θ i)) (oaRule D θ)) ∧
      ∀ y t, OptAuctionFeasible D y t →
        auctionRevenue D t ≤ auctionRevenue D (ecTransfer D (oaRule D) 0) := by
  have : ∀ j, IsProbabilityMeasure (D j).measure := fun j => (D j).isProbabilityMeasure
  have hy01 : ∀ θ i, 0 ≤ oaRule D θ i ∧ oaRule D θ i ≤ 1 := fun θ i => by
    simp only [oaRule]; split_ifs <;> norm_num
  have hyb : ∀ θ i, |oaRule D θ i| ≤ 1 := fun θ i => by
    rw [abs_le]; constructor <;> linarith [hy01 θ i]
  obtain ⟨hint, hbic, ht, hU⟩ := ec_mechanism D (oaRule_measurable D) hyb
    (fun i θ' a ha b hb hab => oaRule_mono D hJ i θ' ha hb hab) 0
  have hU0 : ∀ i, interimU (Measure.pi fun j => (D j).measure) allocV (oaRule D)
      (ecTransfer D (oaRule D) 0) i (D i).lo = 0 := fun i => by
    rw [hU, intervalIntegral.integral_same, Pi.zero_apply, add_zero]
  have hfeas : OptAuctionFeasible D (oaRule D) (ecTransfer D (oaRule D) 0) := by
    refine ⟨fun θ _ => (oaRule_pointwiseOpt D θ).1, hint, hbic, ht, fun i => ?_,
      fun i x hx => ?_⟩
    · refine (integrable_comp_eval (μ := fun j => (D j).measure) (i := i)
        (oa_integrable_virtualValue (D i))).bdd_mul (c := 1)
        (oaRule_measurable D i).aestronglyMeasurable
        (Filter.Eventually.of_forall fun θ => ?_)
      rw [Real.norm_eq_abs]; exact hyb θ i
    · rw [hU, Pi.zero_apply, zero_add]
      exact intervalIntegral.integral_nonneg hx.1 fun s _ =>
        integral_nonneg fun θ' => (hy01 _ i).1
  exact ⟨hfeas, hU0, oaRule_pointwiseOpt D, fun y t h =>
    example_23_F_2 D hfeas hU0 (fun θ _ => oaRule_pointwiseOpt D θ) h⟩

/-- **Example 23.F.2**, non-vacuity of `example_23_F_2_general`: two bidders uniform on `[0, 1]`
and `[0, 2]` (`J₁(θ) = 2θ - 1`, `J₂(θ) = 2θ - 2`, both nondecreasing): the completed rule is an
optimal auction. -/
theorem example_23_F_2_general_instance :
    let D : Fin 2 → TypeDensity := ![uniformDensity 0 1 zero_lt_one,
      uniformDensity 0 2 zero_lt_two]
    OptAuctionFeasible D (oaRule D) (ecTransfer D (oaRule D) 0) ∧
      ∀ y t, OptAuctionFeasible D y t →
        auctionRevenue D t ≤ auctionRevenue D (ecTransfer D (oaRule D) 0) := by
  intro D
  have hJ : ∀ i, MonotoneOn (D i).virtualValue (Set.Icc (D i).lo (D i).hi) := by
    intro i
    fin_cases i
    · intro a ha b hb hab
      have ha' : a ∈ Set.Icc (0 : ℝ) 1 := ha
      have hb' : b ∈ Set.Icc (0 : ℝ) 1 := hb
      change (uniformDensity 0 1 zero_lt_one).virtualValue a ≤
        (uniformDensity 0 1 zero_lt_one).virtualValue b
      rw [oa_uniform_virtualValue _ ha', oa_uniform_virtualValue _ hb']; linarith
    · intro a ha b hb hab
      have ha' : a ∈ Set.Icc (0 : ℝ) 2 := ha
      have hb' : b ∈ Set.Icc (0 : ℝ) 2 := hb
      change (uniformDensity 0 2 zero_lt_two).virtualValue a ≤
        (uniformDensity 0 2 zero_lt_two).virtualValue b
      rw [oa_uniform_virtualValue _ ha', oa_uniform_virtualValue _ hb']; linarith
  obtain ⟨h1, -, -, h4⟩ := example_23_F_2_general D hJ
  exact ⟨h1, h4⟩

/-! ### Exercise 23.F.7: completing the virtual-welfare rule -/

/-- Exercise 23.F.7: the virtual welfare of market structure `y` at cost profile `θ`. -/
noncomputable def dsVW (D : Bool → TypeDensity) (c lam : ℝ) (θ : Bool → ℝ) (y : Bool × Bool) :
    ℝ :=
  dsVirtualWelfare c lam (fun j => dsVirtualCost (D j) lam (θ j)) y

open Classical in
/-- **Exercise 23.F.7** (MWG, p. 924): the pointwise virtual-welfare rule, a maximiser of the
virtual welfare over the four market structures, ties broken in the fixed order duopoly,
monopoly of `false`, monopoly of `true`, no production. -/
noncomputable def dsRule (D : Bool → TypeDensity) (c lam : ℝ) (θ : Bool → ℝ) : Bool × Bool :=
  if ∀ y, dsVW D c lam θ y ≤ dsVW D c lam θ (true, true) then (true, true)
  else if ∀ y, dsVW D c lam θ y ≤ dsVW D c lam θ (true, false) then (true, false)
  else if ∀ y, dsVW D c lam θ y ≤ dsVW D c lam θ (false, true) then (false, true)
  else (false, false)

/-- The rule maximises virtual welfare at every profile. -/
theorem dsRule_max (D : Bool → TypeDensity) (c lam : ℝ) (θ : Bool → ℝ) (y : Bool × Bool) :
    dsVW D c lam θ y ≤ dsVW D c lam θ (dsRule D c lam θ) := by
  classical
  obtain ⟨m, hm⟩ := Finite.exists_max (dsVW D c lam θ)
  unfold dsRule
  split_ifs with h1 h2 h3
  · exact h1 y
  · exact h2 y
  · exact h3 y
  · rcases m with ⟨_ | _, _ | _⟩
    · exact hm y
    · exact absurd hm h3
    · exact absurd hm h2
    · exact absurd hm h1

/-- The virtual cost is measurable. -/
theorem ds_measurable_virtualCost (D : TypeDensity) (lam : ℝ) :
    Measurable (dsVirtualCost D lam) :=
  (measurable_const.mul measurable_id).add
    (measurable_const.mul (D.continuous_cdf.measurable.div D.measurable_dens))

/-- The rule is measurable. -/
theorem dsRule_measurable (D : Bool → TypeDensity) (c lam : ℝ) :
    Measurable (dsRule D c lam) := by
  classical
  have hvc : ∀ j, Measurable fun θ : Bool → ℝ => dsVirtualCost (D j) lam (θ j) := fun j =>
    (ds_measurable_virtualCost (D j) lam).comp (measurable_pi_apply j)
  have hV : ∀ y, Measurable fun θ => dsVW D c lam θ y := by
    intro y
    have hf := hvc false
    have ht := hvc true
    rcases y with ⟨_ | _, _ | _⟩ <;>
      simp only [dsVW, dsVirtualWelfare, dsProduces, Bool.false_eq_true, ↓reduceIte] <;>
      fun_prop
  have hS : ∀ y0, MeasurableSet {θ : Bool → ℝ | ∀ y, dsVW D c lam θ y ≤ dsVW D c lam θ y0} :=
    fun y0 => measurableSet_setOfPred.2 (Measurable.forall fun y =>
      measurableSet_setOfPred.1 (measurableSet_le (hV y) (hV y0)))
  exact Measurable.ite (hS _) measurable_const (Measurable.ite (hS _) measurable_const
    (Measurable.ite (hS _) measurable_const measurable_const))

/-- Lowering firm `j`'s virtual cost (the other's unchanged) raises the virtual welfare of every
structure in which `j` produces by the difference, and leaves the others unchanged. -/
theorem ds_vw_shift (c lam : ℝ) {vc vc' : Bool → ℝ} {j : Bool} (hother : vc' (!j) = vc (!j))
    (y : Bool × Bool) :
    dsVirtualWelfare c lam vc' y =
      dsVirtualWelfare c lam vc y + if dsProduces y j then vc j - vc' j else 0 := by
  cases j <;> simp only [Bool.not_false, Bool.not_true] at hother <;>
    rcases y with ⟨_ | _, _ | _⟩ <;>
    simp [dsVirtualWelfare, dsProduces, hother] <;> ring

/-- **Exercise 23.F.7** (MWG, p. 924): with `λ > 1` and `Φⱼ/φⱼ` nondecreasing, the rule awards
production rights to firm `j` at cost `a` whenever it does at a higher cost `b ≥ a` (the other
firm's cost unchanged): `xⱼ` is nonincreasing in `θⱼ`. -/
theorem dsRule_mono (D : Bool → TypeDensity) (c : ℝ) {lam : ℝ} (hlam : 1 < lam)
    (hΦ : ∀ j, MonotoneOn (fun θ => (D j).cdf θ / (D j).dens θ)
      (Set.Icc (D j).lo (D j).hi)) (j : Bool) (θ' : Bool → ℝ) {a b : ℝ}
    (ha : a ∈ Set.Icc (D j).lo (D j).hi) (hb : b ∈ Set.Icc (D j).lo (D j).hi) (hab : a ≤ b) :
    dsX (dsRule D c lam (update θ' j b)) j ≤ dsX (dsRule D c lam (update θ' j a)) j := by
  rcases lt_or_eq_of_le hab with hlt | heq
  · set yA := dsRule D c lam (update θ' j a)
    set yB := dsRule D c lam (update θ' j b)
    have hvc := dsVirtualCost_strictMono (D j) hlam (hΦ j) ha hb hlt
    have hother : (fun k => dsVirtualCost (D k) lam (update θ' j a k)) (!j) =
        (fun k => dsVirtualCost (D k) lam (update θ' j b k)) (!j) := by
      have hne : (!j) ≠ j := by cases j <;> simp
      simp only [update_of_ne hne]
    have hsh := fun y => ds_vw_shift c lam (vc := fun k => dsVirtualCost (D k) lam
      (update θ' j b k)) (vc' := fun k => dsVirtualCost (D k) lam (update θ' j a k)) hother y
    simp only [update_self] at hsh
    have hA : dsVW D c lam (update θ' j a) yB ≤ dsVW D c lam (update θ' j a) yA :=
      dsRule_max D c lam (update θ' j a) yB
    have hB : dsVW D c lam (update θ' j b) yA ≤ dsVW D c lam (update θ' j b) yB :=
      dsRule_max D c lam (update θ' j b) yA
    simp only [dsVW] at hA hB
    rw [hsh yA, hsh yB] at hA
    simp only [dsX]
    by_cases h1 : dsProduces yB j = true
    · by_cases h2 : dsProduces yA j = true
      · simp [h1, h2]
      · exfalso
        have h2' : dsProduces yA j = false := by simpa using h2
        rw [h1, h2'] at hA
        simp only [ite_true, Bool.false_eq_true, ite_false, add_zero] at hA
        linarith
    · simp only [h1, Bool.false_eq_true, ↓reduceIte]
      split_ifs <;> norm_num
  · rw [heq]

/-- **Exercise 23.F.7** (MWG, p. 924): the transfers from the firms completing `dsRule`,
`tⱼ(θ) = πᶜⱼ - τⱼ(θⱼ)` with `τⱼ` the envelope transfers normalised so that `Uⱼ(θ̄ⱼ) = 0`. -/
noncomputable def dsRuleT (D : Bool → TypeDensity) (c lam : ℝ) : (Bool → ℝ) → Bool → ℝ :=
  fun θ j => dsGross c (dsRule D c lam θ) j -
    ecTransfer D (dsAlloc (dsRule D c lam)) (fun i => -∫ s in (D i).lo..(D i).hi,
      interimBenefit (Measure.pi fun l => (D l).measure) allocV (dsAlloc (dsRule D c lam)) i s)
      θ j

/-- **Exercise 23.F.7** (MWG, p. 924), the optimal auction of production rights for general
densities. Let `λ > 1` and `Φⱼ/φⱼ` be nondecreasing for both firms (MWG: increasing). The
pointwise virtual-welfare rule `dsRule` completed by the envelope transfers `dsRuleT` is a
feasible mechanism (Bayesian incentive compatible, interim individually rational, expectations
existing), leaves each firm's highest-cost type with `Uⱼ(θ̄ⱼ) = 0`, and maximises the planner's
expected welfare `E[∑ⱼ πⱼ + S + (λ - 1)∑ⱼ tⱼ]` among all feasible mechanisms. -/
theorem exercise_23_F_7_general (D : Bool → TypeDensity) (c : ℝ) {lam : ℝ} (hlam : 1 < lam)
    (hΦ : ∀ j, MonotoneOn (fun θ => (D j).cdf θ / (D j).dens θ)
      (Set.Icc (D j).lo (D j).hi)) :
    DSFeasible D c (dsRule D c lam) (dsRuleT D c lam) ∧
      (∀ j, interimU (Measure.pi fun i => (D i).measure) allocV (dsAlloc (dsRule D c lam))
        (dsTau c (dsRule D c lam) (dsRuleT D c lam)) j (D j).hi = 0) ∧
      ∀ k t, DSFeasible D c k t →
        ∫ θ, dsWelfare c lam (k θ) θ (t θ) ∂Measure.pi (fun i => (D i).measure) ≤
          ∫ θ, dsWelfare c lam (dsRule D c lam θ) θ (dsRuleT D c lam θ)
            ∂Measure.pi (fun i => (D i).measure) := by
  have : ∀ j, IsProbabilityMeasure (D j).measure := fun j => (D j).isProbabilityMeasure
  set P := Measure.pi fun i => (D i).measure with hP
  set ks := dsRule D c lam with hks
  set y := dsAlloc ks with hy
  set cst : Bool → ℝ := fun i => -∫ s in (D i).lo..(D i).hi, interimBenefit P allocV y i s
    with hcst
  have hkm : Measurable ks := dsRule_measurable D c lam
  have hym : ∀ j, Measurable fun θ => y θ j := fun j =>
    ((measurable_of_finite fun z => dsX z j).comp hkm).neg
  have hyb : ∀ θ j, |y θ j| ≤ 1 := fun θ j => by
    simp only [hy, dsAlloc, abs_neg]
    rw [abs_le]; constructor <;> linarith [ds_x_mem (ks θ) j]
  have hmono : ∀ j θ', ∀ a ∈ Set.Icc (D j).lo (D j).hi, ∀ b ∈ Set.Icc (D j).lo (D j).hi,
      a ≤ b → y (update θ' j a) j ≤ y (update θ' j b) j := fun j θ' a ha b hb hab => by
    simp only [hy, dsAlloc, neg_le_neg_iff]
    exact dsRule_mono D c hlam hΦ j θ' ha hb hab
  obtain ⟨hint, hbic, ht, hU⟩ := ec_mechanism D hym hyb hmono cst
  have htau : dsTau c ks (dsRuleT D c lam) = ecTransfer D y cst := by
    funext θ j
    simp only [dsTau, dsRuleT, hks, hy, hcst, hP]
    ring
  have hmon := ec_interimBenefit_mono D hym hyb hmono
  have hii : ∀ j, ∀ a ∈ Set.Icc (D j).lo (D j).hi, ∀ b ∈ Set.Icc (D j).lo (D j).hi,
      IntervalIntegrable (interimBenefit P allocV y j) volume a b := fun j a ha b hb =>
    ((hmon j).mono (Set.uIcc_subset_Icc ha hb)).intervalIntegrable
  have hUx : ∀ j x, x ∈ Set.Icc (D j).lo (D j).hi →
      interimU P allocV y (ecTransfer D y cst) j x =
        -∫ s in x..(D j).hi, interimBenefit P allocV y j s := by
    intro j x hx
    have hlo : (D j).lo ∈ Set.Icc (D j).lo (D j).hi := ⟨le_rfl, (D j).lo_lt_hi.le⟩
    have hhi : (D j).hi ∈ Set.Icc (D j).lo (D j).hi := ⟨(D j).lo_lt_hi.le, le_rfl⟩
    rw [hU]
    change -(∫ s in (D j).lo..(D j).hi, interimBenefit P allocV y j s) +
      (∫ s in (D j).lo..x, interimBenefit P allocV y j s) = _
    rw [← intervalIntegral.integral_add_adjacent_intervals (hii j _ hlo _ hx)
      (hii j _ hx _ hhi)]
    ring
  have hy0 : ∀ j s, interimBenefit P allocV y j s ≤ 0 := fun j s =>
    integral_nonpos fun θ' => by
      simp only [allocV, hy, dsAlloc, Pi.zero_apply]
      linarith [(ds_x_mem (ks (update θ' j s)) j).1]
  have hfeas : DSFeasible D c ks (dsRuleT D c lam) := by
    refine ⟨hkm, fun j => ?_, ?_, ?_, fun j x hx => ?_⟩
    · exact ((ds_integrable_comp D hkm fun z => dsGross c z j).sub (ht j)).congr
        (Filter.Eventually.of_forall fun θ => rfl)
    · rw [htau]; exact hint
    · rw [htau]; exact hbic
    · rw [htau, hUx j x hx, neg_nonneg]
      have := intervalIntegral.integral_nonneg (μ := volume) hx.2 fun s _ =>
        neg_nonneg.2 (hy0 j s)
      rw [intervalIntegral.integral_neg] at this
      linarith
  have hUhi : ∀ j, interimU P allocV (dsAlloc ks) (dsTau c ks (dsRuleT D c lam)) j
      (D j).hi = 0 := fun j => by
    rw [htau, hUx j _ ⟨(D j).lo_lt_hi.le, le_rfl⟩, intervalIntegral.integral_same, neg_zero]
  exact ⟨hfeas, hUhi, fun k t h => exercise_23_F_7_optimal D c hlam hfeas hUhi
    (fun θ _ y' => dsRule_max D c lam θ y') h⟩

/-- **Exercise 23.F.7**, non-vacuity of `exercise_23_F_7_general`: fixed costs uniform on
`[0, 1/100]` have `Φ/φ = θ`, nondecreasing; with `c = 0`, `λ = 2` the completed rule is optimal. -/
theorem exercise_23_F_7_general_instance :
    DSFeasible (fun _ => dsUnif) 0 (dsRule (fun _ => dsUnif) 0 2)
        (dsRuleT (fun _ => dsUnif) 0 2) ∧
      ∀ k t, DSFeasible (fun _ => dsUnif) 0 k t →
        ∫ θ, dsWelfare 0 2 (k θ) θ (t θ) ∂Measure.pi (fun _ : Bool => dsUnif.measure) ≤
          ∫ θ, dsWelfare 0 2 (dsRule (fun _ => dsUnif) 0 2 θ) θ
            (dsRuleT (fun _ => dsUnif) 0 2 θ) ∂Measure.pi (fun _ : Bool => dsUnif.measure) := by
  have hΦ : ∀ j : Bool, MonotoneOn (fun θ => ((fun _ => dsUnif) j).cdf θ /
      ((fun _ => dsUnif) j).dens θ) (Set.Icc ((fun _ => dsUnif) j).lo
        ((fun _ => dsUnif) j).hi) := by
    intro j
    have hr : ∀ x ∈ Set.Icc dsUnif.lo dsUnif.hi, dsUnif.cdf x / dsUnif.dens x = x := by
      intro x hx
      have hd : dsUnif.dens x = (1 / 100 - 0 : ℝ)⁻¹ := by
        change (Set.Icc (0 : ℝ) (1 / 100)).indicator (fun _ => (1 / 100 - 0 : ℝ)⁻¹) x = _
        exact Set.indicator_of_mem hx _
      have hc : dsUnif.cdf x = (x - 0) / (1 / 100 - 0) := oa_uniform_cdf (by norm_num) hx
      rw [hd, hc]
      field_simp
      ring
    intro a ha b hb hab
    simp only at ha hb ⊢
    rw [hr a ha, hr b hb]
    exact hab
  obtain ⟨h1, -, h3⟩ := exercise_23_F_7_general (fun _ => dsUnif) 0 (by norm_num : (1 : ℝ) < 2)
    hΦ
  exact ⟨h1, h3⟩

end MWG.MechanismDesign
