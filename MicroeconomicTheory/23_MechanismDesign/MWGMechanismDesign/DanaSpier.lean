/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGMechanismDesign.MyersonSatterthwaiteSteps
import MWGMechanismDesign.RegulationExercises

/-!
# Exercise 23.F.7 (Dana-Spier): the reduction to virtual welfare

MWG, Exercise 23.F.7 (p. 924). Two firms `j ∈ {false, true}` with private fixed costs `θⱼ`,
independent with densities `φⱼ > 0` on `[θ̲ⱼ, θ̄ⱼ]`; demand `p = 1 - x`, marginal cost `c`;
the planner chooses a market structure `k(θ)` (neither, one, or both firms licensed; Cournot
competition when both) and transfers `tⱼ(θ)` from firm `j`, maximising
`E[W]`, `W = ∑ⱼ πⱼ + S + (λ - 1)∑ⱼ tⱼ` (`dsWelfare`), over Bayesian incentive compatible,
interim individually rational mechanisms (`DSFeasible`). In the linear form of Section 23.D
firm `j` has utility `θⱼvⱼ + τⱼ` with `vⱼ = -xⱼ` (`dsAlloc`) and `τⱼ = πᶜⱼ - tⱼ` (`dsTau`),
so Proposition 23.D.2 and the revenue formulas apply.

* `exercise_23_F_7_reduction`, the missing step (the two-firm analogue of (23.F.4)):
  `E[W] = E[S + ∑ⱼ xⱼ(λπᶜⱼ - λθⱼ - (λ - 1)Φⱼ(θⱼ)/φⱼ(θⱼ))] - (λ - 1)∑ⱼ Uⱼ(θ̄ⱼ)`, the
  virtual welfare being `dsVirtualWelfare` with virtual costs `dsVirtualCost` (from
  `RegulationExercises`).
* `exercise_23_F_7_optimal`: for `λ > 1`, a feasible mechanism with `Uⱼ(θ̄ⱼ) = 0` that maximises
  virtual welfare at every cost profile is optimal; with `Φ/φ` increasing this pointwise rule has
  the monotonicity incentive compatibility needs (`exercise_23_F_7`, `dsVirtualCost_strictMono`).
* `exercise_23_F_7_instance`: costs uniform on `[0, 1/100]`, `c = 0`, `λ = 2`: licensing both
  firms and charging each `1/9 - 1/100` is optimal.

**Departures.** Participation is interim (`Uⱼ(θⱼ) ≥ 0`); market structures are deterministic;
the reduction holds for any `λ` and for different densities of the two firms. That for every
`(c, λ > 1, φ)` with `Φ/φ` nondecreasing the pointwise virtual-welfare rule can be completed by
transfers into a feasible mechanism is `exercise_23_F_7_general` (`EnvelopeCompletion`).
-/

namespace MWG.MechanismDesign

open MeasureTheory Function

/-- Exercise 23.F.7: `xⱼ(y) = 1` if firm `j` is awarded production rights in market structure
`y`, `0` otherwise. -/
noncomputable def dsX (y : Bool × Bool) (j : Bool) : ℝ := if dsProduces y j then 1 else 0

/-- Exercise 23.F.7 in the linear form of Section 23.D: firm `j` of fixed cost `θⱼ` has utility
`θⱼvⱼ + τⱼ` with `vⱼ = -xⱼ(k(θ))` (the fixed cost is paid only when producing). -/
noncomputable def dsAlloc (k : (Bool → ℝ) → Bool × Bool) : (Bool → ℝ) → Bool → ℝ :=
  fun θ j => -dsX (k θ) j

/-- Exercise 23.F.7 in the linear form: firm `j`'s type-independent payoff
`τⱼ = (Cournot profit before fixed cost) - tⱼ`, `tⱼ` the transfer from firm `j` to the
planner. -/
noncomputable def dsTau (c : ℝ) (k : (Bool → ℝ) → Bool × Bool) (t : (Bool → ℝ) → Bool → ℝ) :
    (Bool → ℝ) → Bool → ℝ :=
  fun θ j => dsGross c (k θ) j - t θ j

/-- Exercise 23.F.7: firm `j`'s gross (pretransfer) profit `πⱼ = Cournot profit - θⱼxⱼ`. -/
noncomputable def dsProfit (c : ℝ) (y : Bool × Bool) (θ : Bool → ℝ) (j : Bool) : ℝ :=
  dsGross c y j - θ j * dsX y j

/-- **Exercise 23.F.7** (MWG, p. 924): social welfare `W = ∑ⱼ πⱼ + S + (λ - 1)∑ⱼ tⱼ` in
market structure `y` with fixed costs `θ` and transfers `t` to the planner. -/
noncomputable def dsWelfare (c lam : ℝ) (y : Bool × Bool) (θ : Bool → ℝ) (t : Bool → ℝ) : ℝ :=
  ∑ j, dsProfit c y θ j + dsSurplus c y + (lam - 1) * ∑ j, t j

/-- Exercise 23.F.7: firm `j`'s utility in the linear form is its profit net of the transfer,
`θⱼvⱼ + τⱼ = πⱼ - tⱼ`. -/
theorem ds_linU (c : ℝ) (k : (Bool → ℝ) → Bool × Bool) (t : (Bool → ℝ) → Bool → ℝ)
    (θ : Bool → ℝ) (j : Bool) :
    linU allocV j (dsAlloc k θ, dsTau c k t θ) (θ j) = dsProfit c (k θ) θ j - t θ j := by
  simp only [linU, allocV, dsAlloc, dsTau, dsProfit]
  ring

/-- **Exercise 23.F.7** (MWG, p. 924): the mechanisms the planner may use. The types
`θ = (θ_false, θ_true)` (fixed costs) are independent with densities `φⱼ > 0` on `[θ̲ⱼ, θ̄ⱼ]`;
`k` (measurable) chooses the market structure and `t` the transfers; the induced social choice
function is Bayesian incentive compatible and interim individually rational (`Uⱼ(θⱼ) ≥ 0`), and
the expectations involved exist. -/
def DSFeasible (D : Bool → TypeDensity) (c : ℝ) (k : (Bool → ℝ) → Bool × Bool)
    (t : (Bool → ℝ) → Bool → ℝ) : Prop :=
  Measurable k ∧ (∀ j, Integrable (fun θ => t θ j) (Measure.pi fun i => (D i).measure)) ∧
    InterimIntegrable (Measure.pi fun i => (D i).measure) allocV (dsAlloc k) (dsTau c k t)
      (fun i => (D i).lo) (fun i => (D i).hi) ∧
    BayesianICOn (Measure.pi fun i => (D i).measure) allocV (dsAlloc k) (dsTau c k t)
      (fun i => (D i).lo) (fun i => (D i).hi) ∧
    ∀ j, ∀ x ∈ Set.Icc (D j).lo (D j).hi,
      0 ≤ interimU (Measure.pi fun i => (D i).measure) allocV (dsAlloc k) (dsTau c k t) j x

/-- A function of the market structure is integrable. -/
theorem ds_integrable_comp (D : Bool → TypeDensity) {k : (Bool → ℝ) → Bool × Bool}
    (hk : Measurable k) (f : Bool × Bool → ℝ) :
    Integrable (fun θ => f (k θ)) (Measure.pi fun i => (D i).measure) := by
  have : ∀ j, IsProbabilityMeasure (D j).measure := fun j => (D j).isProbabilityMeasure
  refine Integrable.of_bound ((measurable_of_finite f).comp hk).aestronglyMeasurable
    (∑ y, |f y|) (Filter.Eventually.of_forall fun θ => ?_)
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (f := fun y => |f y|) (fun y _ => abs_nonneg _)
    (Finset.mem_univ (k θ))

/-- `0 ≤ xⱼ ≤ 1`. -/
theorem ds_x_mem (y : Bool × Bool) (j : Bool) : 0 ≤ dsX y j ∧ dsX y j ≤ 1 := by
  simp only [dsX]; split_ifs <;> norm_num

/-- `xⱼ(k(θ))g(θⱼ)` is integrable when `g` is integrable for `μⱼ`. -/
theorem ds_integrable_x_mul (D : Bool → TypeDensity) {k : (Bool → ℝ) → Bool × Bool}
    (hk : Measurable k) (j : Bool) {g : ℝ → ℝ} (hg : Integrable g (D j).measure) :
    Integrable (fun θ => dsX (k θ) j * g (θ j)) (Measure.pi fun i => (D i).measure) := by
  have : ∀ i, IsProbabilityMeasure (D i).measure := fun i => (D i).isProbabilityMeasure
  refine (integrable_comp_eval hg).bdd_mul (c := 1)
    ((measurable_of_finite fun y => dsX y j).comp hk).aestronglyMeasurable
    (Filter.Eventually.of_forall fun θ => ?_)
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [ds_x_mem (k θ) j]

/-- The identity function has an expectation under a type distribution. -/
theorem ds_integrable_id (E : TypeDensity) : Integrable (fun x => x) E.measure :=
  mss_integrable_of_mul_dens E (mss_ii_mul_dens E continuous_id _ _) fun _ _ => rfl

/-- Gross Cournot profits vanish for firms without production rights: `πᶜⱼ = xⱼπᶜⱼ`. -/
theorem ds_gross_eq (c : ℝ) (y : Bool × Bool) (j : Bool) :
    dsGross c y j = dsX y j * dsGross c y j := by
  simp only [dsX, dsGross]; split_ifs <;> ring

/-- `dsVirtualWelfare` as a sum over firms: `S + ∑ⱼ xⱼ(λπᶜⱼ - vcⱼ)`. -/
theorem ds_virtualWelfare_eq (c lam : ℝ) (vc : Bool → ℝ) (y : Bool × Bool) :
    dsVirtualWelfare c lam vc y = dsSurplus c y + ∑ j, dsX y j * (lam * dsGross c y j - vc j) := by
  simp only [dsVirtualWelfare, Fintype.sum_bool, dsX]
  split_ifs <;> ring

/-- **Exercise 23.F.7** (MWG, p. 924), the missing step: the planner's expected welfare is
expected VIRTUAL welfare (the two-firm analogue of (23.F.4)). For every feasible mechanism
`(k, t)`,
`E[∑ⱼ πⱼ + S + (λ - 1)∑ⱼ tⱼ] = E[S(k(θ)) + ∑ⱼ xⱼ(λπᶜⱼ - λθⱼ - (λ - 1)Φⱼ(θⱼ)/φⱼ(θⱼ))]
  - (λ - 1)∑ⱼ Uⱼ(θ̄ⱼ)`,
where `πᶜⱼ` is the Cournot profit before the fixed cost; the virtual welfare is
`dsVirtualWelfare` with virtual costs `dsVirtualCost` (and it has an expectation). This holds
for any `λ` and any (possibly different) type densities. -/
theorem exercise_23_F_7_reduction (D : Bool → TypeDensity) (c lam : ℝ)
    {k : (Bool → ℝ) → Bool × Bool} {t : (Bool → ℝ) → Bool → ℝ} (h : DSFeasible D c k t) :
    Integrable (fun θ => dsVirtualWelfare c lam (fun j => dsVirtualCost (D j) lam (θ j)) (k θ))
        (Measure.pi fun i => (D i).measure) ∧
      ∫ θ, dsWelfare c lam (k θ) θ (t θ) ∂Measure.pi (fun i => (D i).measure) =
        ∫ θ, dsVirtualWelfare c lam (fun j => dsVirtualCost (D j) lam (θ j)) (k θ)
          ∂Measure.pi (fun i => (D i).measure) -
        (lam - 1) * ∑ j, interimU (Measure.pi fun i => (D i).measure) allocV (dsAlloc k)
          (dsTau c k t) j (D j).hi := by
  have : ∀ j, IsProbabilityMeasure (D j).measure := fun j => (D j).isProbabilityMeasure
  obtain ⟨hk, ht, hint, hbic, -⟩ := h
  set P := Measure.pi fun i => (D i).measure with hP
  -- integrability of the pieces
  have iG : ∀ j, Integrable (fun θ => dsGross c (k θ) j) P := fun j =>
    ds_integrable_comp D hk fun y => dsGross c y j
  have iS : Integrable (fun θ => dsSurplus c (k θ)) P := ds_integrable_comp D hk _
  have iXK : ∀ j, Integrable (fun θ => dsX (k θ) j * (D j).virtualCost (θ j)) P := fun j =>
    ds_integrable_x_mul D hk j (mss_integrable_virtualCost (D j))
  have iXT : ∀ j, Integrable (fun θ => θ j * dsX (k θ) j) P := fun j =>
    (ds_integrable_x_mul D hk j (ds_integrable_id (D j))).congr
      (Filter.Eventually.of_forall fun θ => by simp only [mul_comm])
  have iTau : ∀ j, Integrable (fun θ => dsTau c k t θ j) P := fun j => (iG j).sub (ht j)
  -- the expected transfer of each firm
  have hT : ∀ j, ∫ θ, t θ j ∂P = ∫ θ, dsGross c (k θ) j ∂P -
      ∫ θ, dsX (k θ) j * (D j).virtualCost (θ j) ∂P -
      interimU P allocV (dsAlloc k) (dsTau c k t) j (D j).hi := by
    intro j
    have e1 := mss_expected_transfer D hint hbic j (iTau j)
    have hyK : Integrable (fun θ => dsAlloc k θ j * (D j).virtualCost (θ j)) P :=
      ((iXK j).neg).congr (Filter.Eventually.of_forall fun θ => by
        simp only [dsAlloc, Pi.neg_apply]; ring)
    have e2 := mss_payment_from_top D hint hbic j
    have e3 := mss_expect_mul D hint hbic j (mss_measurable_virtualCost (D j)) hyK
    rw [← e3, ← e1] at e2
    have e4 : ∫ θ, dsAlloc k θ j * (D j).virtualCost (θ j) ∂P =
        -∫ θ, dsX (k θ) j * (D j).virtualCost (θ j) ∂P := by
      rw [← integral_neg]; congr 1; funext θ; simp only [dsAlloc]; ring
    have e5 : ∫ θ, -dsTau c k t θ j ∂P = -(∫ θ, dsGross c (k θ) j ∂P - ∫ θ, t θ j ∂P) := by
      rw [integral_neg]; congr 1; exact integral_sub (iG j) (ht j)
    rw [e4, e5] at e2
    linarith
  -- the pointwise identity
  set A : (Bool → ℝ) → ℝ := fun θ => dsWelfare c lam (k θ) θ (t θ) with hA
  set B : (Bool → ℝ) → ℝ := fun θ => ∑ j, (t θ j - dsGross c (k θ) j +
    dsX (k θ) j * (D j).virtualCost (θ j)) with hB
  have hpt : ∀ θ, dsVirtualWelfare c lam (fun j => dsVirtualCost (D j) lam (θ j)) (k θ) =
      A θ - (lam - 1) * B θ := by
    intro θ
    rw [ds_virtualWelfare_eq]
    simp only [hA, hB, dsWelfare, dsProfit, Fintype.sum_bool, dsVirtualCost,
      TypeDensity.virtualCost]
    linear_combination (-lam) * ds_gross_eq c (k θ) true + (-lam) * ds_gross_eq c (k θ) false
  have iB : Integrable B P := by
    simp only [hB, Fintype.sum_bool]
    exact (((ht true).sub (iG true)).add (iXK true)).add (((ht false).sub (iG false)).add
      (iXK false))
  have iA : Integrable A P := by
    simp only [hA, dsWelfare, dsProfit, Fintype.sum_bool]
    exact ((((iG true).sub (iXT true)).add ((iG false).sub (iXT false))).add iS).add
      (((ht true).add (ht false)).const_mul (lam - 1))
  have iV : Integrable (fun θ => dsVirtualWelfare c lam
      (fun j => dsVirtualCost (D j) lam (θ j)) (k θ)) P := by
    simp only [hpt]; exact iA.sub (iB.const_mul (lam - 1))
  refine ⟨iV, ?_⟩
  have hBj : ∀ j, ∫ θ, (t θ j - dsGross c (k θ) j + dsX (k θ) j * (D j).virtualCost (θ j)) ∂P =
      -interimU P allocV (dsAlloc k) (dsTau c k t) j (D j).hi := by
    intro j
    rw [integral_add (f := fun θ => t θ j - dsGross c (k θ) j)
      (g := fun θ => dsX (k θ) j * (D j).virtualCost (θ j)) ((ht j).sub (iG j)) (iXK j),
      integral_sub (ht j) (iG j), hT j]
    ring
  have hBE : ∫ θ, B θ ∂P = -∑ j, interimU P allocV (dsAlloc k) (dsTau c k t) j (D j).hi := by
    simp only [hB, Fintype.sum_bool]
    rw [integral_add (f := fun θ => t θ true - dsGross c (k θ) true +
        dsX (k θ) true * (D true).virtualCost (θ true))
      (g := fun θ => t θ false - dsGross c (k θ) false +
        dsX (k θ) false * (D false).virtualCost (θ false))
      (((ht true).sub (iG true)).add (iXK true)) (((ht false).sub (iG false)).add (iXK false)),
      hBj true, hBj false]
    ring
  simp only [hpt]
  rw [integral_sub iA (iB.const_mul (lam - 1)), integral_const_mul, hBE]
  ring

/-- **Exercise 23.F.7** (MWG, p. 924), the optimal auction of production rights. Let `λ > 1`.
If a feasible mechanism `(k*, t*)` leaves the highest-cost type of each firm with
`Uⱼ(θ̄ⱼ) = 0` and, at every cost profile `θ ∈ Θ`, chooses a market structure maximising the
virtual welfare `S(y) + ∑_{j producing}(λπᶜⱼ(y) - λθⱼ - (λ - 1)Φⱼ(θⱼ)/φⱼ(θⱼ))`, then it
maximises the planner's expected welfare `E[∑ⱼ πⱼ + S + (λ - 1)∑ⱼ tⱼ]` among all feasible
mechanisms. (`exercise_23_F_7` shows that this pointwise rule has the monotonicity Bayesian
incentive compatibility requires.) -/
theorem exercise_23_F_7_optimal (D : Bool → TypeDensity) (c : ℝ) {lam : ℝ} (hlam : 1 < lam)
    {ks : (Bool → ℝ) → Bool × Bool} {ts : (Bool → ℝ) → Bool → ℝ} (hs : DSFeasible D c ks ts)
    (hU : ∀ j, interimU (Measure.pi fun i => (D i).measure) allocV (dsAlloc ks)
      (dsTau c ks ts) j (D j).hi = 0)
    (hopt : ∀ θ, (∀ j, θ j ∈ Set.Icc (D j).lo (D j).hi) → ∀ y,
      dsVirtualWelfare c lam (fun j => dsVirtualCost (D j) lam (θ j)) y ≤
        dsVirtualWelfare c lam (fun j => dsVirtualCost (D j) lam (θ j)) (ks θ))
    {k : (Bool → ℝ) → Bool × Bool} {t : (Bool → ℝ) → Bool → ℝ} (h : DSFeasible D c k t) :
    ∫ θ, dsWelfare c lam (k θ) θ (t θ) ∂Measure.pi (fun i => (D i).measure) ≤
      ∫ θ, dsWelfare c lam (ks θ) θ (ts θ) ∂Measure.pi (fun i => (D i).measure) := by
  have : ∀ j, IsProbabilityMeasure (D j).measure := fun j => (D j).isProbabilityMeasure
  obtain ⟨iV, hW⟩ := exercise_23_F_7_reduction D c lam h
  obtain ⟨iVs, hWs⟩ := exercise_23_F_7_reduction D c lam hs
  rw [hW, hWs]
  simp only [hU, Finset.sum_const_zero, mul_zero, sub_zero]
  have hIR : 0 ≤ ∑ j, interimU (Measure.pi fun i => (D i).measure) allocV (dsAlloc k)
      (dsTau c k t) j (D j).hi :=
    Finset.sum_nonneg fun j _ => h.2.2.2.2 j _ ⟨(D j).lo_lt_hi.le, le_rfl⟩
  have hle : ∫ θ, dsVirtualWelfare c lam (fun j => dsVirtualCost (D j) lam (θ j)) (k θ)
      ∂Measure.pi (fun i => (D i).measure) ≤
      ∫ θ, dsVirtualWelfare c lam (fun j => dsVirtualCost (D j) lam (θ j)) (ks θ)
      ∂Measure.pi (fun i => (D i).measure) := by
    refine integral_mono_ae iV iVs ?_
    filter_upwards [re_ae_mem (fun j => (D j).measure) fun j => (D j).measure_compl_Icc]
      with θ hθ using hopt θ hθ (k θ)
  nlinarith

/-- Fixed costs uniform on `[0, 1/100]` (the instance of Exercise 23.F.7 below). -/
noncomputable def dsUnif : TypeDensity := uniformDensity 0 (1 / 100) (by norm_num)

/-- For costs uniform on `[0, 1/100]` and `λ = 2`, the virtual cost is `3θ`. -/
theorem ds_unif_virtualCost {x : ℝ} (hx : x ∈ Set.Icc dsUnif.lo dsUnif.hi) :
    dsVirtualCost dsUnif 2 x = 3 * x := by
  have hd : dsUnif.dens x = (1 / 100 - 0 : ℝ)⁻¹ := by
    change (Set.Icc (0 : ℝ) (1 / 100)).indicator (fun _ => (1 / 100 - 0 : ℝ)⁻¹) x = _
    exact Set.indicator_of_mem hx _
  have hc : dsUnif.cdf x = (x - 0) / (1 / 100 - 0) := oa_uniform_cdf (by norm_num) hx
  rw [dsVirtualCost, hd, hc]
  field_simp
  ring

/-- **Exercise 23.F.7** (MWG, p. 924), a solved instance (non-vacuity of
`exercise_23_F_7_optimal`): with fixed costs independent and uniform on `[0, 1/100]`, `c = 0`
and `λ = 2`, licensing both firms (Cournot duopoly) and charging each firm `1/9 - 1/100`
(so the highest-cost type just breaks even) is feasible and maximises the planner's expected
welfare among all feasible mechanisms. -/
theorem exercise_23_F_7_instance {k : (Bool → ℝ) → Bool × Bool} {t : (Bool → ℝ) → Bool → ℝ}
    (h : DSFeasible (fun _ => dsUnif) 0 k t) :
    DSFeasible (fun _ => dsUnif) 0 (fun _ => (true, true)) (fun _ _ => 1 / 9 - 1 / 100) ∧
    ∫ θ, dsWelfare 0 2 (k θ) θ (t θ) ∂Measure.pi (fun _ : Bool => dsUnif.measure) ≤
      ∫ θ, dsWelfare 0 2 (true, true) θ (fun _ => 1 / 9 - 1 / 100)
        ∂Measure.pi (fun _ : Bool => dsUnif.measure) := by
  have := dsUnif.isProbabilityMeasure
  have hA : ∀ θ j, dsAlloc (fun _ => (true, true)) θ j = -1 := fun θ j => by
    cases j <;> simp [dsAlloc, dsX, dsProduces]
  have hT : ∀ θ j, dsTau 0 (fun _ => (true, true)) (fun _ _ => 1 / 9 - 1 / 100) θ j = 1 / 100 :=
    fun θ j => by cases j <;> simp [dsTau, dsGross, dsProduces]
  have hB : ∀ j a, interimBenefit (Measure.pi fun _ : Bool => dsUnif.measure) allocV
      (dsAlloc fun _ => (true, true)) j a = -1 := fun j a => by
    simp [interimBenefit, allocV, hA]
  have hTr : ∀ j a, interimTransfer (Measure.pi fun _ : Bool => dsUnif.measure)
      (dsTau 0 (fun _ => (true, true)) (fun _ _ => 1 / 9 - 1 / 100)) j a = 1 / 100 :=
    fun j a => by simp only [interimTransfer, hT]; simp
  have hF : DSFeasible (fun _ => dsUnif) 0 (fun _ => (true, true))
      (fun _ _ => 1 / 9 - 1 / 100) := by
    refine ⟨measurable_const, fun j => integrable_const _, fun j a _ => ?_, ?_, ?_⟩
    · simp only [allocV, hA, hT]; exact ⟨integrable_const _, integrable_const _⟩
    · intro j x _ a _
      simp only [linU, allocV, hA, hT, le_refl]
    · intro j x hx
      simp only [interimU, hB, hTr]
      have : x ≤ 1 / 100 := hx.2
      linarith
  refine ⟨hF, exercise_23_F_7_optimal (fun _ => dsUnif) 0 (by norm_num : (1 : ℝ) < 2) hF
    (fun j => ?_) (fun θ hθ y => ?_) h⟩
  · simp only [interimU, hB, hTr]
    change (1 / 100 : ℝ) * -1 + 1 / 100 = 0
    norm_num
  · have hv : (fun j => dsVirtualCost ((fun _ => dsUnif) j) 2 (θ j)) = fun j => 3 * θ j :=
      funext fun j => ds_unif_virtualCost (hθ j)
    have b0 : θ false ≤ 1 / 100 := (hθ false).2
    have b1 : θ true ≤ 1 / 100 := (hθ true).2
    have c0 : 0 ≤ θ false := (hθ false).1
    have c1 : 0 ≤ θ true := (hθ true).1
    rw [hv]
    rcases y with ⟨_ | _, _ | _⟩ <;>
      simp [dsVirtualWelfare, dsSurplus, dsGross, dsProduces] <;> norm_num <;> linarith

end MWG.MechanismDesign
