import ChoiceUnderUncertainty.MixtureRepresentation
import ChoiceUnderUncertainty.AffineUniqueness
import ChoiceUnderUncertainty.SegmentOrder
import MWGPreferenceChoice.PreferenceRelations
import ChoiceUnderUncertainty.LotteryEvaluation
import Mathlib.Probability.CDF
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import UtilityForMoney.EqualProbabilityRisk
import Mathlib.Analysis.Convex.Deriv
import UtilityForMoney.Insurance
import Mathlib.Analysis.Convex.Continuous
import UtilityForMoney.LocalRiskPremium
import UtilityForMoney.ConstantAbsoluteRisk
import UtilityForMoney.ArrowPrattTheorem
import UtilityForMoney.ComparativeRisk
import UtilityForMoney.RelativeRisk
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import UtilityForMoney.IncomeChoice
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Probability.Distributions.Gaussian.Real
import UtilityForMoney.GeneralQuantile
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.MeasureTheory.Integral.Layercake
import UtilityForMoney.SupermartingaleCoupling
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import ChoiceUnderUncertainty.AnscombeAumann
import MWGClassicalDemand.CloserSeparable
import MWGClassicalDemand.UtilityRepresentation
import PreferenceProperties.PrimitiveAdditiveExistence
set_option autoImplicit false

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Simple and compound lotteries

MWG, Section 6.B, pp. 168-170: Definitions 6.B.1 and 6.B.2, the reduced lottery, footnote 4
and Figures 6.B.2-6.B.3.

A simple lottery over a finite outcome set `C` is Kreps's `SimpleLottery C`
(`Kreps.ChoiceUnderUncertainty`, Mathlib's `StdSimplex ℝ C`): on a finite type a finitely
supported probability vector is exactly MWG's list `(p₁, …, p_N)` with `p_n ≥ 0` and
`∑ p_n = 1` (`definition_6_B_1`). Binary mixtures `αL + (1 - α)L'` are Kreps's `Mix`. The
reduced lottery of a compound lottery `(L₁, …, L_K; α₁, …, α_K)` is `reducedLottery`, whose
`n`-th probability is `∑_k α_k p_n^k`. The rationality notion of this chapter is Kreps's,
which is MWG's Definition 1.B.1 (`rational_iff_mwg`).
-/

namespace MWG.ChoiceUnderUncertainty

open Kreps.ChoiceUnderUncertainty Convexity

variable {C : Type*} [Fintype C]

/-- The rationality notion used with lotteries (Kreps Chapter 5's copy) is MWG's
Definition 1.B.1. -/
theorem rational_iff_mwg {X : Type*} (r : X → X → Prop) :
    Rational r ↔ Kreps.ChoicePreferenceUtility.Rational r :=
  Iff.rfl

/-- The simple lottery with a given probability vector. -/
noncomputable def lotteryOfVec (p : C → ℝ) (h0 : ∀ n, 0 ≤ p n) (h1 : ∑ n, p n = 1) :
    SimpleLottery C where
  weights := Finsupp.equivFunOnFinite.symm p
  nonneg := fun n => h0 n
  total := by
    rw [Finsupp.sum_fintype _ _ (by simp)]
    simpa using h1

/-- The probabilities of `lotteryOfVec` are the given vector. -/
@[simp] theorem lotteryOfVec_weights (p : C → ℝ) (h0 : ∀ n, 0 ≤ p n) (h1 : ∑ n, p n = 1)
    (n : C) : (lotteryOfVec p h0 h1).weights n = p n := rfl

/-- **Definition 6.B.1** (MWG, p. 168). A simple lottery is a list `(p₁, …, p_N)` with
`p_n ≥ 0` and `∑ p_n = 1`: the probability vector of a `SimpleLottery C` lies in the simplex,
every vector of the simplex is one, and the vector determines the lottery. -/
theorem definition_6_B_1 :
    (∀ L : SimpleLottery C, (∀ n, 0 ≤ L.weights n) ∧ ∑ n, L.weights n = 1) ∧
    (∀ p : C → ℝ, (∀ n, 0 ≤ p n) → ∑ n, p n = 1 → ∃ L : SimpleLottery C, ⇑L.weights = p) ∧
    (∀ L L' : SimpleLottery C, ⇑L.weights = ⇑L'.weights → L = L') := by
  refine ⟨fun L => ⟨fun n => L.weights_nonneg n, L.total_of_fintype⟩,
    fun p h0 h1 => ⟨lotteryOfVec p h0 h1, rfl⟩, fun L L' h => ?_⟩
  exact StdSimplex.ext (Finsupp.ext (congrFun h))

/-- **p. 169**. The simplex `Δ = {p ∈ ℝ^N_+ : ∑ p_n = 1}` is the set of probability vectors of
simple lotteries. -/
theorem lottery_vectors_eq_simplex :
    Set.range (fun L : SimpleLottery C => ⇑L.weights) =
      {p : C → ℝ | (∀ n, 0 ≤ p n) ∧ ∑ n, p n = 1} := by
  ext p
  constructor
  · rintro ⟨L, rfl⟩
    exact ⟨fun n => L.weights_nonneg n, L.total_of_fintype⟩
  · rintro ⟨h0, h1⟩
    exact ⟨lotteryOfVec p h0 h1, rfl⟩

omit [Fintype C] in
/-- **p. 169**. Each vertex of the simplex is the degenerate lottery giving one outcome for
sure. -/
theorem degenerate_lottery_weights [DecidableEq C] (n m : C) :
    (PureLottery n : SimpleLottery C).weights m = if m = n then 1 else 0 := by
  simp [PureLottery, StdSimplex.single, Finsupp.single_apply, eq_comm]

/-- The reduced probability vector `p_n = α₁ p_n^1 + ⋯ + α_K p_n^K`. -/
noncomputable def reducedVec {K : Type*} [Fintype K] (L : K → SimpleLottery C) (α : K → ℝ)
    (n : C) : ℝ :=
  ∑ k, α k * (L k).weights n

/-- **Footnote 4** (MWG, p. 170). The reduced probabilities are nonnegative and sum to one:
`∑_n p_n = ∑_k α_k (∑_n p_n^k) = ∑_k α_k = 1`. -/
theorem footnote_6_4 {K : Type*} [Fintype K] (L : K → SimpleLottery C) (α : K → ℝ)
    (hα : ∀ k, 0 ≤ α k) (h1 : ∑ k, α k = 1) :
    (∀ n, 0 ≤ reducedVec L α n) ∧ ∑ n, reducedVec L α n = 1 := by
  refine ⟨fun n => Finset.sum_nonneg fun k _ => mul_nonneg (hα k) ((L k).weights_nonneg n), ?_⟩
  unfold reducedVec
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, StdSimplex.total_of_fintype, mul_one, h1]

/-- **Definition 6.B.2** (MWG, p. 169). The reduced lottery of the compound lottery
`(L₁, …, L_K; α₁, …, α_K)`. -/
noncomputable def reducedLottery {K : Type*} [Fintype K] (L : K → SimpleLottery C) (α : K → ℝ)
    (hα : ∀ k, 0 ≤ α k) (h1 : ∑ k, α k = 1) : SimpleLottery C :=
  lotteryOfVec (reducedVec L α) (footnote_6_4 L α hα h1).1 (footnote_6_4 L α hα h1).2

/-- **p. 169**. The `n`-th probability of the reduced lottery. -/
@[simp] theorem reducedLottery_weights {K : Type*} [Fintype K] (L : K → SimpleLottery C)
    (α : K → ℝ) (hα : ∀ k, 0 ≤ α k) (h1 : ∑ k, α k = 1) (n : C) :
    (reducedLottery L α hα h1).weights n = ∑ k, α k * (L k).weights n := rfl

/-- **p. 170**. For two lotteries the reduced lottery is the binary mixture
`αL₁ + (1 - α)L₂`, the point on the segment between `L₁` and `L₂`. -/
theorem reducedLottery_two (L : Fin 2 → SimpleLottery C) (a : Weight) :
    reducedLottery L ![a.val, 1 - a.val]
      (by intro k; fin_cases k <;> simp [a.property.1, a.property.2]) (by simp) =
      Mix a (L 0) (L 1) := by
  apply StdSimplex.ext
  ext n
  simp [lottery_mix_weight]

omit [Fintype C] in
/-- **Figure 6.B.2** (MWG, p. 170). The reduced lottery of `(L₁, L₂; 1/2, 1/2)` is the
midpoint `(1/2)L₁ + (1/2)L₂`. -/
theorem figure_6_B_2 (L₁ L₂ : SimpleLottery C) (n : C) :
    (Mix ⟨1 / 2, by norm_num, by norm_num⟩ L₁ L₂).weights n =
      (L₁.weights n + L₂.weights n) / 2 := by
  rw [lottery_mix_weight]
  ring

/-- **Figure 6.B.3** (MWG, p. 170). The compound lottery giving `(1,0,0)`,
`(1/4,3/8,3/8)`, `(1/4,3/8,3/8)` with probability `1/3` each, and the one giving
`(1/2,1/2,0)`, `(1/2,0,1/2)` with probability `1/2` each, both reduce to `(1/2,1/4,1/4)`. -/
theorem figure_6_B_3 :
    (fun n : Fin 3 => ∑ k : Fin 3, (1 / 3 : ℝ) * (![![1, 0, 0], ![1 / 4, 3 / 8, 3 / 8],
      ![1 / 4, 3 / 8, 3 / 8]] k n)) = ![1 / 2, 1 / 4, 1 / 4] ∧
    (fun n : Fin 3 => ∑ k : Fin 2, (1 / 2 : ℝ) * (![![1 / 2, 1 / 2, 0], ![1 / 2, 0, 1 / 2]] k n))
      = ![1 / 2, 1 / 4, 1 / 4] := by
  constructor <;> ext n <;> fin_cases n <;> simp [Fin.sum_univ_succ] <;> norm_num

/-- **Footnote 2** (MWG, p. 169, Figure 6.B.1(b)). In the equilateral triangle of altitude `1`
with vertices `v₁ = (-1/√3, 0)`, `v₂ = (1/√3, 0)`, `v₃ = (0, 1)`, the point
`p₁v₁ + p₂v₂ + p₃v₃` of a lottery has perpendicular distance `p_n` to the side opposite
`v_n` (distances to the lines `(√3/2)x + y/2 = 1/2`, `-(√3/2)x + y/2 = 1/2` and `y = 0`, written
with unit normals); in particular the three distances sum to the altitude `1`. -/
theorem footnote_6_2 {p₁ p₂ p₃ : ℝ} (h1 : 0 ≤ p₁) (h2 : 0 ≤ p₂) (h3 : 0 ≤ p₃)
    (hs : p₁ + p₂ + p₃ = 1) :
    let X := p₁ * (-1 / Real.sqrt 3) + p₂ * (1 / Real.sqrt 3) + p₃ * 0
    let Y := p₁ * 0 + p₂ * 0 + p₃ * 1
    |Real.sqrt 3 / 2 * X + 1 / 2 * Y - 1 / 2| = p₁ ∧
      |-(Real.sqrt 3 / 2) * X + 1 / 2 * Y - 1 / 2| = p₂ ∧ |Y| = p₃ ∧
      (Real.sqrt 3 / 2) ^ 2 + (1 / 2) ^ 2 = 1 := by
  intro X Y
  have h3' : Real.sqrt 3 ≠ 0 := by positivity
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have eX : Real.sqrt 3 / 2 * X = (p₂ - p₁) / 2 := by
    simp only [X]; field_simp; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [eX, show (p₂ - p₁) / 2 + 1 / 2 * Y - 1 / 2 = -p₁ by simp only [Y]; linarith, abs_neg,
      abs_of_nonneg h1]
  · rw [neg_mul, eX, show -((p₂ - p₁) / 2) + 1 / 2 * Y - 1 / 2 = -p₂ by simp only [Y]; linarith,
      abs_neg, abs_of_nonneg h2]
  · simp only [Y]; rw [abs_of_nonneg (by linarith)]; ring
  · rw [div_pow, hsq]; norm_num

end MWG.ChoiceUnderUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The continuity and independence axioms and the expected utility theorem

MWG, Section 6.B, pp. 171-178: Definitions 6.B.3-6.B.5, Exercises 6.B.1-6.B.3,
Propositions 6.B.1-6.B.3 (the expected utility theorem) with Steps 1-3 of its proof and
footnotes 6-7.

MWG's continuity axiom (closed sets of mixture weights) and independence axiom (weak
comparisons at interior weights) are stated on an arbitrary mixture space (`ConvexSpace ℝ Z`,
with Kreps's binary `Mix`). Together with rationality they imply Kreps's mixture axioms
(`mixtureAxioms_of_mwg`), so Proposition 6.B.3 follows from Kreps's Proposition 5.3, and the
uniqueness Proposition 6.B.2 from Kreps's uniqueness theorem. Exercise 6.B.3 (best and worst
lotteries exist under independence alone) is proved by showing that the set of lotteries
dominated by the best sure outcome is convex.
-/

universe u

namespace MWG.ChoiceUnderUncertainty

open Kreps.ChoiceUnderUncertainty Convexity

/-- **Definition 6.B.3** (MWG, p. 171). Continuity: for all `L, L', L''` the sets
`{α ∈ [0,1] : αL + (1 - α)L' ≿ L''}` and `{α ∈ [0,1] : L'' ≿ αL + (1 - α)L'}` are closed. -/
def MixContinuous {Z : Type*} [ConvexSpace ℝ Z] (r : Z → Z → Prop) : Prop :=
  ∀ L L' L'' : Z, IsClosed {a : Weight | r (Mix a L L') L''} ∧
    IsClosed {a : Weight | r L'' (Mix a L L')}

/-- **Definition 6.B.4** (MWG, p. 171). The independence axiom: for all `L, L', L''` and
`α ∈ (0,1)`, `L ≿ L'` iff `αL + (1 - α)L'' ≿ αL' + (1 - α)L''`. -/
def Independence {Z : Type*} [ConvexSpace ℝ Z] (r : Z → Z → Prop) : Prop :=
  ∀ (L L' L'' : Z) (a : Weight), 0 < a.val → a.val < 1 →
    (r L L' ↔ r (Mix a L L'') (Mix a L' L''))

variable {Z : Type*} [ConvexSpace ℝ Z] {r : Z → Z → Prop}

/-- **Exercise 6.B.1**, first claim (MWG, p. 172). Under independence, `L ≻ L'` iff
`αL + (1 - α)L'' ≻ αL' + (1 - α)L''`. -/
theorem exercise_6_B_1_strict (hi : Independence r) (L L' L'' : Z) (a : Weight)
    (ha0 : 0 < a.val) (ha1 : a.val < 1) :
    Strict r L L' ↔ Strict r (Mix a L L'') (Mix a L' L'') := by
  rw [Strict, Strict, hi L L' L'' a ha0 ha1, hi L' L L'' a ha0 ha1]

/-- **Exercise 6.B.1**, second claim (MWG, p. 172). Under independence, `L ∼ L'` iff
`αL + (1 - α)L'' ∼ αL' + (1 - α)L''`. -/
theorem exercise_6_B_1_indifferent (hi : Independence r) (L L' L'' : Z) (a : Weight)
    (ha0 : 0 < a.val) (ha1 : a.val < 1) :
    Indifferent r L L' ↔ Indifferent r (Mix a L L'') (Mix a L' L'') := by
  rw [Indifferent, Indifferent, hi L L' L'' a ha0 ha1, hi L' L L'' a ha0 ha1]

/-- Independence with the common lottery in the first position. -/
theorem independence_left (hi : Independence r) (L L' L'' : Z) (a : Weight)
    (ha0 : 0 < a.val) (ha1 : a.val < 1) :
    r L L' ↔ r (Mix a L'' L) (Mix a L'' L') := by
  rw [mix_swap a L'' L, mix_swap a L'' L']
  exact hi L L' L'' (Kreps.ChoiceUnderUncertainty.Complement a)
    (by change 0 < 1 - a.val; linarith) (by change 1 - a.val < 1; linarith)

/-- **Exercise 6.B.1**, third claim (MWG, p. 172). For rational preferences satisfying
independence, `L ≻ L'` and `L'' ≻ L'''` imply `αL + (1 - α)L'' ≻ αL' + (1 - α)L'''`. -/
theorem exercise_6_B_1_both (hr : Rational r) (hi : Independence r) {L L' L'' L''' : Z}
    (h : Strict r L L') (h' : Strict r L'' L''') (a : Weight) (ha0 : 0 < a.val)
    (ha1 : a.val < 1) : Strict r (Mix a L L'') (Mix a L' L''') := by
  have h1 := (exercise_6_B_1_strict hi L L' L'' a ha0 ha1).mp h
  have h2 : r (Mix a L' L'') (Mix a L' L''') := (independence_left hi L'' L''' L' a ha0 ha1).mp h'.1
  exact strict_weak_trans hr.2 h1 h2

/-- MWG's continuity, independence and rationality imply Kreps's mixture axioms (strict
background independence at all weights and strict comparisons near weight one). -/
theorem mixtureAxioms_of_mwg (hr : Rational r) (hc : MixContinuous r) (hi : Independence r) :
    MixtureAxioms r := by
  refine ⟨hr, ?_, ?_⟩
  · intro a x y z w
    rcases eq_or_lt_of_le a.property.1 with h0 | h0
    · have ha : a = 0 := Subtype.ext h0.symm
      subst ha
      simp only [mix_zero]
      exact ⟨fun h => absurd h.1 h.2, fun h => absurd h.1 h.2⟩
    rcases eq_or_lt_of_le a.property.2 with h1 | h1
    · have ha : a = 1 := Subtype.ext h1
      subst ha
      simp only [mix_one]
    rw [← exercise_6_B_1_strict hi x y z a h0 h1, ← exercise_6_B_1_strict hi x y w a h0 h1]
  · intro x y hxy z
    have hA := (hc x z y).2
    have hB := (hc y z x).1
    have hO : IsOpen ({a : Weight | r y (Mix a x z)}ᶜ ∩ {a : Weight | r (Mix a y z) x}ᶜ) :=
      hA.isOpen_compl.inter hB.isOpen_compl
    have h1 : (1 : Weight) ∈ {a : Weight | r y (Mix a x z)}ᶜ ∩ {a : Weight | r (Mix a y z) x}ᶜ := by
      simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_ofPred_eq, mix_one]
      exact ⟨hxy.2, hxy.2⟩
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hO 1 h1
    refine ⟨max (1 - ε / 2) (1 / 2), ⟨lt_max_of_lt_right (by norm_num),
      max_lt (by linarith) (by norm_num)⟩, fun a ha => ?_⟩
    have hmem : a ∈ Metric.ball (1 : Weight) ε := by
      rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq]
      have : (1 : Weight).val = 1 := rfl
      rw [this, abs_of_nonpos (by linarith [a.property.2])]
      linarith [le_max_left (1 - ε / 2) (1 / 2)]
    obtain ⟨hA', hB'⟩ := hball hmem
    exact ⟨(proposition_1_9a hr.1 _ _).mpr hA', (proposition_1_9a hr.1 _ _).mpr hB'⟩

/-- A mixture-affine representation gives MWG's continuity axiom. -/
theorem mixContinuous_of_affine {U : Z → ℝ} (hU : Represents U r) (ha : AffineInMix U) :
    MixContinuous r := by
  have hcont (L L' : Z) : Continuous fun a : Weight => U (Mix a L L') := by
    have : (fun a : Weight => U (Mix a L L')) = fun a : Weight => a.val * U L + (1 - a.val) * U L'
      := funext fun a => ha a L L'
    rw [this]
    fun_prop
  intro L L' L''
  have e1 : {a : Weight | r (Mix a L L') L''} = {a : Weight | U L'' ≤ U (Mix a L L')} := by
    ext a; exact hU _ _
  have e2 : {a : Weight | r L'' (Mix a L L')} = {a : Weight | U (Mix a L L') ≤ U L''} := by
    ext a; exact hU _ _
  rw [e1, e2]
  exact ⟨isClosed_le continuous_const (hcont L L'), isClosed_le (hcont L L') continuous_const⟩

/-- A mixture-affine representation gives MWG's independence axiom. -/
theorem independence_of_affine {U : Z → ℝ} (hU : Represents U r) (ha : AffineInMix U) :
    Independence r := by
  intro L L' L'' a ha0 _
  rw [hU, hU, ha, ha]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- **Step 1 of the proof of Proposition 6.B.3** (MWG, p. 176). If `L ≻ L'` and
`α ∈ (0,1)`, then `L ≻ αL + (1 - α)L' ≻ L'`. -/
theorem proposition_6_B_3_step1 (hr : Rational r) (hc : MixContinuous r) (hi : Independence r)
    {L L' : Z} (h : Strict r L L') (a : Weight) (ha0 : 0 < a.val) (ha1 : a.val < 1) :
    Strict r L (Mix a L L') ∧ Strict r (Mix a L L') L' := by
  have hm := mixtureAxioms_of_mwg hr hc hi
  refine ⟨?_, segment_base_strict hm h a ha0⟩
  simpa only [mix_one] using lemma_5_7_strict hm h (s := a) (t := 1) ha1

/-- **Step 2 of the proof of Proposition 6.B.3** (MWG, p. 176). If `L̄ ≻ L̲`, then
`βL̄ + (1 - β)L̲ ≻ αL̄ + (1 - α)L̲` iff `β > α`. -/
theorem proposition_6_B_3_step2 (hr : Rational r) (hc : MixContinuous r) (hi : Independence r)
    {Lb Lw : Z} (h : Strict r Lb Lw) (a b : Weight) :
    Strict r (Mix b Lb Lw) (Mix a Lb Lw) ↔ a.val < b.val := by
  have hm := mixtureAxioms_of_mwg hr hc hi
  refine ⟨fun hs => lt_of_not_ge fun hab => ?_, fun hab => lemma_5_7_strict hm h hab⟩
  rcases eq_or_lt_of_le hab with he | hlt
  · have : b = a := Subtype.ext he
    subst this
    exact hs.2 hs.1
  · exact hs.2 (lemma_5_7_strict hm h hlt).1

/-- **Linear utility** (MWG, Proposition 6.B.1, p. 173): `U` satisfies (6.B.1),
`U(∑ α_k L_k) = ∑ α_k U(L_k)`, for every finite family of lotteries. -/
def IsLinearUtility {C : Type u} [Fintype C] (U : SimpleLottery C → ℝ) : Prop :=
  ∀ (K : Type u) [Fintype K] (L : K → SimpleLottery C) (α : K → ℝ) (hα : ∀ k, 0 ≤ α k)
    (h1 : ∑ k, α k = 1), U (reducedLottery L α hα h1) = ∑ k, α k * U (L k)

/-- **Definition 6.B.5** (MWG, p. 173). `U` has the expected utility form if there are numbers
`u₁, …, u_N` with `U(L) = u₁p₁ + ⋯ + u_N p_N` for every simple lottery. -/
def HasExpectedUtilityForm {C : Type*} [Fintype C] (U : SimpleLottery C → ℝ) : Prop :=
  ∃ u : C → ℝ, ∀ L : SimpleLottery C, U L = ∑ n, u n * L.weights n

variable {C : Type u} [Fintype C]

/-- **p. 173**. With the expected utility form, the utility of the degenerate lottery `Lⁿ` is
`u_n`. -/
theorem expectedUtilityForm_degenerate (u : C → ℝ) (n : C) :
    ∑ m, u m * (PureLottery n : SimpleLottery C).weights m = u n := by
  classical
  simp [degenerate_lottery_weights]

/-- Every lottery is the reduced lottery of the degenerate lotteries with weights
`(p₁, …, p_N)`: `L = ∑ p_n Lⁿ`. -/
theorem reducedLottery_degenerate (L : SimpleLottery C) :
    reducedLottery (fun n => PureLottery n) (fun n => L.weights n) (fun n => L.weights_nonneg n)
      L.total_of_fintype = L := by
  classical
  apply StdSimplex.ext
  ext m
  simp [degenerate_lottery_weights]

/-- **Proposition 6.B.1** (MWG, p. 173). `U` has an expected utility form iff it is linear. -/
theorem proposition_6_B_1 (U : SimpleLottery C → ℝ) :
    HasExpectedUtilityForm U ↔ IsLinearUtility U := by
  constructor
  · rintro ⟨u, hu⟩ K _ L α hα h1
    rw [hu]
    simp only [reducedLottery_weights, hu, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun n _ => by ring
  · intro h
    refine ⟨fun n => U (PureLottery n), fun L => ?_⟩
    have := h C (fun n => PureLottery n) (fun n => L.weights n) (fun n => L.weights_nonneg n)
      L.total_of_fintype
    rw [reducedLottery_degenerate] at this
    rw [this]
    exact Finset.sum_congr rfl fun n _ => mul_comm _ _

/-- The expected utility form is Kreps's `ExpectedUtility`. -/
theorem hasExpectedUtilityForm_iff (U : SimpleLottery C → ℝ) :
    HasExpectedUtilityForm U ↔ ∃ u : C → ℝ, U = ExpectedUtility u := by
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨u, funext fun L => by rw [hu, expectedUtility_eq_sum]; simp only [mul_comm]⟩
  · rintro ⟨u, rfl⟩
    exact ⟨u, fun L => by rw [expectedUtility_eq_sum]; simp only [mul_comm]⟩

/-- A utility function of expected utility form is affine in binary mixtures. -/
theorem affineInMix_of_expectedUtilityForm {U : SimpleLottery C → ℝ}
    (hU : HasExpectedUtilityForm U) : AffineInMix U := by
  obtain ⟨u, rfl⟩ := (hasExpectedUtilityForm_iff U).mp hU
  exact expectedUtility_affine u

/-- **Proposition 6.B.2** (MWG, p. 173). If `U` is a v.N-M expected utility function for `≿`,
then `Ũ` is another one iff `Ũ = βU + γ` for some `β > 0` and `γ`. -/
theorem proposition_6_B_2 {r : SimpleLottery C → SimpleLottery C → Prop}
    {U : SimpleLottery C → ℝ} (hU : HasExpectedUtilityForm U) (hr : Represents U r)
    (V : SimpleLottery C → ℝ) :
    (HasExpectedUtilityForm V ∧ Represents V r) ↔
      ∃ β > 0, ∃ γ : ℝ, ∀ L, V L = β * U L + γ := by
  constructor
  · rintro ⟨hV, hvr⟩
    exact proposition_5_4_unique hr hvr (affineInMix_of_expectedUtilityForm hU)
      (affineInMix_of_expectedUtilityForm hV)
  · rintro ⟨β, hβ, γ, hV⟩
    obtain ⟨u, hu⟩ := hU
    refine ⟨⟨fun n => β * u n + γ, fun L => ?_⟩, fun L L' => ?_⟩
    · rw [hV, hu]
      simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
      have hγ : ∑ x, γ * L.weights x = γ := by
        rw [← Finset.mul_sum, L.total_of_fintype, mul_one]
      rw [hγ]
    · rw [hr, hV, hV]
      constructor
      · intro h; nlinarith
      · intro h; nlinarith

/-- **Footnote 6** (MWG, p. 173). For a utility function of expected utility form there are
best and worst lotteries (degenerate lotteries at a best and a worst outcome). -/
theorem footnote_6_6 [Nonempty C] {U : SimpleLottery C → ℝ} (hU : HasExpectedUtilityForm U) :
    ∃ Lb Lw : SimpleLottery C, ∀ L, U Lw ≤ U L ∧ U L ≤ U Lb := by
  obtain ⟨u, hu⟩ := hU
  obtain ⟨nb, -, hnb⟩ := Finset.exists_max_image Finset.univ u Finset.univ_nonempty
  obtain ⟨nw, -, hnw⟩ := Finset.exists_min_image Finset.univ u Finset.univ_nonempty
  refine ⟨PureLottery nb, PureLottery nw, fun L => ?_⟩
  simp only [hu, expectedUtilityForm_degenerate]
  constructor
  · calc u nw = ∑ n, u nw * L.weights n := by rw [← Finset.mul_sum, L.total_of_fintype, mul_one]
      _ ≤ _ := Finset.sum_le_sum fun n _ =>
          mul_le_mul_of_nonneg_right (hnw n (Finset.mem_univ _)) (L.weights_nonneg n)
  · calc ∑ n, u n * L.weights n ≤ ∑ n, u nb * L.weights n := Finset.sum_le_sum fun n _ =>
          mul_le_mul_of_nonneg_right (hnb n (Finset.mem_univ _)) (L.weights_nonneg n)
      _ = u nb := by rw [← Finset.mul_sum, L.total_of_fintype, mul_one]

/-- **p. 175**. A preference represented by a utility function of expected utility form is
continuous (Definition 6.B.3). -/
theorem continuous_of_expectedUtilityForm {r : SimpleLottery C → SimpleLottery C → Prop}
    {U : SimpleLottery C → ℝ} (hU : HasExpectedUtilityForm U) (hr : Represents U r) :
    MixContinuous r :=
  mixContinuous_of_affine hr (affineInMix_of_expectedUtilityForm hU)

/-- **Exercise 6.B.2** (MWG, p. 175). A preference represented by a utility function of
expected utility form satisfies the independence axiom. -/
theorem exercise_6_B_2 {r : SimpleLottery C → SimpleLottery C → Prop}
    {U : SimpleLottery C → ℝ} (hU : HasExpectedUtilityForm U) (hr : Represents U r) :
    Independence r :=
  independence_of_affine hr (affineInMix_of_expectedUtilityForm hU)

/-- **Proposition 6.B.3** (MWG, p. 176), the expected utility theorem: a rational preference
on the simple lotteries satisfying continuity and independence has a representation of the
expected utility form, `L ≿ L'` iff `∑ u_n p_n ≥ ∑ u_n p'_n`. -/
theorem proposition_6_B_3 {r : SimpleLottery C → SimpleLottery C → Prop} (hr : Rational r)
    (hc : MixContinuous r) (hi : Independence r) :
    ∃ u : C → ℝ, ∀ L L' : SimpleLottery C,
      r L L' ↔ ∑ n, u n * L'.weights n ≤ ∑ n, u n * L.weights n := by
  obtain ⟨u, hu⟩ := proposition_5_3.mp (mixtureAxioms_of_mwg hr hc hi)
  refine ⟨u, fun L L' => ?_⟩
  rw [hu, expectedUtility_eq_sum, expectedUtility_eq_sum]
  simp only [mul_comm]

/-- The converse of Proposition 6.B.3 (MWG, p. 175): a preference with an expected utility
representation is rational, continuous and satisfies independence. -/
theorem proposition_6_B_3_converse {r : SimpleLottery C → SimpleLottery C → Prop} (u : C → ℝ)
    (h : ∀ L L' : SimpleLottery C, r L L' ↔ ∑ n, u n * L'.weights n ≤ ∑ n, u n * L.weights n) :
    Rational r ∧ MixContinuous r ∧ Independence r := by
  have hU : HasExpectedUtilityForm (fun L : SimpleLottery C => ∑ n, u n * L.weights n) :=
    ⟨u, fun _ => rfl⟩
  have hrep : Represents (fun L : SimpleLottery C => ∑ n, u n * L.weights n) r := h
  refine ⟨⟨fun x y => ?_, fun x y z hxy hyz => ?_⟩, continuous_of_expectedUtilityForm hU hrep,
    exercise_6_B_2 hU hrep⟩
  · rw [h, h]; exact le_total _ _
  · rw [h] at *; exact hyz.trans hxy

/-- **Step 3 of the proof of Proposition 6.B.3** (MWG, p. 177). If `L̄ ≻ L̲` are best and
worst lotteries, every lottery is indifferent to `α_L L̄ + (1 - α_L) L̲` for a unique
`α_L ∈ [0,1]`. -/
theorem proposition_6_B_3_step3 {r : Z → Z → Prop} (hr : Rational r) (hc : MixContinuous r)
    (hi : Independence r) {Lb Lw : Z} (h : Strict r Lb Lw) (hb : ∀ L, r Lb L)
    (hw : ∀ L, r L Lw) (L : Z) : ∃! a : Weight, Indifferent r (Mix a Lb Lw) L := by
  obtain ⟨U, hU, ha⟩ := proposition_5_4.mp (mixtureAxioms_of_mwg hr hc hi)
  have hlt : U Lw < U Lb := by
    rw [Strict, hU, hU] at h
    exact lt_of_not_ge h.2
  have hL1 : U L ≤ U Lb := (hU _ _).mp (hb L)
  have hL2 : U Lw ≤ U L := (hU _ _).mp (hw L)
  have hd : 0 < U Lb - U Lw := sub_pos.mpr hlt
  let a : Weight := ⟨(U L - U Lw) / (U Lb - U Lw), div_nonneg (by linarith) hd.le,
    (div_le_one hd).mpr (by linarith)⟩
  have hval (b : Weight) : Indifferent r (Mix b Lb Lw) L ↔ b.val = a.val := by
    rw [Indifferent, hU, hU, ha]
    change _ ↔ b.val = (U L - U Lw) / (U Lb - U Lw)
    rw [eq_div_iff hd.ne']
    constructor
    · rintro ⟨h1, h2⟩; nlinarith
    · intro h; constructor <;> nlinarith
  exact ⟨a, (hval a).mpr rfl, fun b hb => Subtype.ext ((hval b).mp hb)⟩

/-- The set of lotteries no better than a given one is convex under independence (MWG,
p. 181: independence implies convexity of the not-better-than sets). -/
theorem noBetter_isConvexSet (hr : Rational r) (hi : Independence r) (L : Z) :
    IsConvexSet ℝ {M : Z | r L M} := by
  apply IsConvexSet.of_convexCombPair_mem
  intro a b ha hb hab x hx y hy
  have he : b = 1 - a := by linarith
  subst b
  let t : Weight := ⟨a, ha, by linarith⟩
  change r L (Mix t x y)
  rcases eq_or_lt_of_le ha with h0 | h0
  · have : t = 0 := Subtype.ext h0.symm
    rw [this, mix_zero]; exact hy
  rcases eq_or_lt_of_le t.property.2 with h1 | h1
  · have : t = 1 := Subtype.ext h1
    rw [this, mix_one]; exact hx
  have h1' : r (Mix t L y) (Mix t x y) := (hi L x y t h0 h1).mp hx
  have h2' : r (Mix t L L) (Mix t L y) := (independence_left hi L y L t h0 h1).mp hy
  rw [mix_self] at h2'
  exact hr.2 _ _ _ h2' h1'

/-- The set of lotteries at least as good as a given one is convex under independence. -/
theorem noWorse_isConvexSet (hr : Rational r) (hi : Independence r) (L : Z) :
    IsConvexSet ℝ {M : Z | r M L} := by
  apply IsConvexSet.of_convexCombPair_mem
  intro a b ha hb hab x hx y hy
  have he : b = 1 - a := by linarith
  subst b
  let t : Weight := ⟨a, ha, by linarith⟩
  change r (Mix t x y) L
  rcases eq_or_lt_of_le ha with h0 | h0
  · have : t = 0 := Subtype.ext h0.symm
    rw [this, mix_zero]; exact hy
  rcases eq_or_lt_of_le t.property.2 with h1 | h1
  · have : t = 1 := Subtype.ext h1
    rw [this, mix_one]; exact hx
  have h1' : r (Mix t x y) (Mix t L y) := (hi x L y t h0 h1).mp hx
  have h2' : r (Mix t L y) (Mix t L L) := (independence_left hi y L L t h0 h1).mp hy
  rw [mix_self] at h2'
  exact hr.2 _ _ _ h1' h2'

omit [Fintype C] in
/-- **Exercise 6.B.3** (MWG, p. 208) and **footnote 7** (p. 176). With finitely many outcomes,
a rational preference satisfying the independence axiom has a best and a worst lottery
(no continuity is needed). -/
theorem exercise_6_B_3 [Finite C] [Nonempty C] {r : SimpleLottery C → SimpleLottery C → Prop}
    (hr : Rational r) (hi : Independence r) :
    ∃ Lb Lw : SimpleLottery C, ∀ L, r Lb L ∧ r L Lw := by
  let _ : Fintype C := Fintype.ofFinite C
  let q : C → C → Prop := fun n m => r (PureLottery n) (PureLottery m)
  have hq : Kreps.ChoicePreferenceUtility.Rational q :=
    ⟨fun n m => hr.1 _ _, fun n m k => hr.2 _ _ _⟩
  have hrep := Kreps.ChoicePreferenceUtility.proposition_1_8 hq
  let v := Kreps.ChoicePreferenceUtility.FiniteUtility q
  obtain ⟨nb, -, hnb⟩ := Finset.exists_max_image Finset.univ v Finset.univ_nonempty
  obtain ⟨nw, -, hnw⟩ := Finset.exists_min_image Finset.univ v Finset.univ_nonempty
  refine ⟨PureLottery nb, PureLottery nw, fun L => ⟨?_, ?_⟩⟩
  · have hs := noBetter_isConvexSet hr hi (PureLottery nb)
    have hp : L.iConvexComb (fun x => PureLottery x) ∈ {M | r (PureLottery nb) M} :=
      hs.iConvexComb_mem fun n _ => (hrep nb n).mpr (hnb n (Finset.mem_univ _))
    simpa only [PureLottery, StdSimplex.iConvexComb_single, Set.mem_ofPred_eq] using hp
  · have hs := noWorse_isConvexSet hr hi (PureLottery nw)
    have hp : L.iConvexComb (fun x => PureLottery x) ∈ {M | r M (PureLottery nw)} :=
      hs.iConvexComb_mem fun n _ => (hrep n nw).mpr (hnw n (Finset.mem_univ _))
    simpa only [PureLottery, StdSimplex.iConvexComb_single, Set.mem_ofPred_eq] using hp

end MWG.ChoiceUnderUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Uses and critiques of expected utility

MWG, Section 6.B, pp. 174-183, and Exercises 6.B.4-6.B.7, pp. 208-209: utility differences,
straight parallel indifference lines (Figure 6.B.5), Example 6.B.1 (expected utility as a
guide to introspection), the Allais paradox (Example 6.B.2, Figure 6.B.7), Machina's paradox
(Example 6.B.3), the Dutch book remark (independence implies convex not-better-than sets, a
strictly weaker property), induced preferences (Example 6.B.4, footnote 9, Exercise 6.B.6),
and Exercises 6.B.4 (flood evacuation), 6.B.5 (the betweenness axiom) and 6.B.7.

`eu u L = ∑ u_n p_n` is the expected utility of `L` for outcome utilities `u`.
-/

namespace MWG.ChoiceUnderUncertainty

open Kreps.ChoiceUnderUncertainty Convexity

/-- The expected utility `∑ u_n p_n` of a simple lottery. -/
noncomputable def eu {C : Type*} [Fintype C] (u : C → ℝ) (L : SimpleLottery C) : ℝ :=
  ∑ n, u n * L.weights n

/-- Expected utility is affine in binary mixtures. -/
theorem eu_mix {C : Type*} [Fintype C] (u : C → ℝ) (a : Weight) (L L' : SimpleLottery C) :
    eu u (Mix a L L') = a.val * eu u L + (1 - a.val) * eu u L' := by
  simp only [eu, lottery_mix_weight, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1 <;> exact Finset.sum_congr rfl fun n _ => by ring

/-- A three-outcome lottery from its probability vector. -/
noncomputable def lot3 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : a + b + c = 1) : SimpleLottery (Fin 3) :=
  lotteryOfVec ![a, b, c] (by intro n; fin_cases n <;> simpa)
    (by simp [Fin.sum_univ_succ]; linarith)

/-- Expected utility of a three-outcome lottery. -/
theorem eu_lot3 (u : Fin 3 → ℝ) (a b c : ℝ) (ha hb hc h) :
    eu u (lot3 a b c ha hb hc h) = u 0 * a + u 1 * b + u 2 * c := by
  simp [eu, lot3, Fin.sum_univ_succ]
  ring

/-- **p. 174**. With four outcomes and an expected utility representation, `u₁ - u₂ > u₃ - u₄`
iff the lottery `L = (1/2, 0, 0, 1/2)` is strictly preferred to `L' = (0, 1/2, 1/2, 0)`. -/
theorem utility_differences_meaning (u : Fin 4 → ℝ) :
    u 0 - u 1 > u 2 - u 3 ↔
      eu u (lotteryOfVec ![1 / 2, 0, 0, 1 / 2] (by intro n; fin_cases n <;> norm_num)
        (by simp [Fin.sum_univ_succ]; norm_num)) >
      eu u (lotteryOfVec ![0, 1 / 2, 1 / 2, 0] (by intro n; fin_cases n <;> norm_num)
        (by simp [Fin.sum_univ_succ]; norm_num)) := by
  simp only [Fin.isValue, gt_iff_lt, eu, one_div, lotteryOfVec_weights, Fin.sum_univ_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.succ_zero_eq_one, mul_zero,
    Fin.succ_one_eq_two, Finset.univ_unique, Fin.default_eq_zero, Matrix.cons_val_fin_one,
    Finset.sum_singleton, Fin.reduceSucc, zero_add, Finset.sum_const_zero, add_zero]
  constructor <;> intro h <;> linarith

/-- **p. 174**. The ranking of utility differences is preserved by every positive linear
transformation `ũ_n = βu_n + γ`. -/
theorem utility_differences_invariant (u : Fin 4 → ℝ) {β : ℝ} (hβ : 0 < β) (γ : ℝ) :
    (β * u 0 + γ) - (β * u 1 + γ) > (β * u 2 + γ) - (β * u 3 + γ) ↔ u 0 - u 1 > u 2 - u 3 := by
  constructor <;> intro h <;> nlinarith

/-- **p. 175, Figure 6.B.5(a)**. Under an expected utility representation the indifference set
through `L` is the intersection of the simplex with the hyperplane `∑ u_n p'_n = ∑ u_n p_n`;
all indifference sets are level sets of one linear function (straight parallel lines). -/
theorem indifference_set_hyperplane {C : Type*} [Fintype C] (u : C → ℝ)
    {r : SimpleLottery C → SimpleLottery C → Prop} (hr : Represents (eu u) r)
    (L : SimpleLottery C) :
    {M | Indifferent r M L} = {M | ∑ n, u n * (M.weights n - L.weights n) = 0} := by
  ext M
  rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, Indifferent, hr, hr]
  simp only [mul_sub, Finset.sum_sub_distrib]
  unfold eu
  constructor
  · rintro ⟨h1, h2⟩; linarith
  · intro h; constructor <;> linarith

/-- **p. 175, Figure 6.B.5(b)**. Indifference curves are straight: under independence,
`L ∼ L'` implies `αL + (1 - α)L' ∼ L` for every `α ∈ [0,1]`. -/
theorem indifference_straight {Z : Type*} [ConvexSpace ℝ Z] {r : Z → Z → Prop}
    (hr : Rational r) (hi : Independence r) {L L' : Z} (h : Indifferent r L L') (a : Weight) :
    Indifferent r (Mix a L L') L := by
  rcases eq_or_lt_of_le a.property.1 with h0 | h0
  · have : a = 0 := Subtype.ext h0.symm
    rw [this, mix_zero]; exact ⟨h.2, h.1⟩
  rcases eq_or_lt_of_le a.property.2 with h1 | h1
  · have : a = 1 := Subtype.ext h1
    rw [this, mix_one]; exact ⟨complete_refl hr.1 L, complete_refl hr.1 L⟩
  have e := (independence_left hi L' L L a h0 h1)
  rw [mix_self] at e
  exact ⟨e.mp h.2, (independence_left hi L L' L a h0 h1).mp h.1 |> fun h' => by
    rw [mix_self] at h'; exact h'⟩

/-- **p. 176, Figure 6.B.5(c)**. Indifference curves are parallel: under independence, if
`L ∼ L'` then `αL + (1 - α)L'' ∼ αL' + (1 - α)L''` for every `L''`. -/
theorem indifference_parallel {Z : Type*} [ConvexSpace ℝ Z] {r : Z → Z → Prop}
    (hi : Independence r) {L L' : Z} (h : Indifferent r L L') (L'' : Z) (a : Weight)
    (ha0 : 0 < a.val) (ha1 : a.val < 1) :
    Indifferent r (Mix a L L'') (Mix a L' L'') :=
  (exercise_6_B_1_indifferent hi L L' L'' a ha0 ha1).mp h

/-- **Example 6.B.1** (MWG, p. 178). If `L'` lies on the segment from `L` to `L''` (so
`L' = αL'' + (1 - α)L` with `α ∈ (0,1]`) and `L'' ≻ L`, then `L' ≻ L`, for every rational,
continuous preference satisfying independence. -/
theorem example_6_B_1 {Z : Type*} [ConvexSpace ℝ Z] {r : Z → Z → Prop} (hr : Rational r)
    (hc : MixContinuous r) (hi : Independence r) {L L'' : Z} (h : Strict r L'' L)
    (a : Weight) (ha : 0 < a.val) : Strict r (Mix a L'' L) L :=
  segment_base_strict (mixtureAxioms_of_mwg hr hc hi) h a ha

/-- **Example 6.B.1** (MWG, p. 179). Without the expected utility hypotheses the inference
fails: for the continuous utility `V(p) = (p₁ - 1/2)²` on three outcomes, `L'' = (1,0,0) ≻
L = (1/4,3/4,0)` but `L ≻ L' = (1/2,1/2,0)`, which lies between `L` and `L''`. -/
theorem example_6_B_1_general_map_fails :
    let V : SimpleLottery (Fin 3) → ℝ := fun p => (p.weights 0 - 1 / 2) ^ 2
    let L := lot3 (1 / 4) (3 / 4) 0 (by norm_num) (by norm_num) le_rfl (by norm_num)
    let L' := lot3 (1 / 2) (1 / 2) 0 (by norm_num) (by norm_num) le_rfl (by norm_num)
    let L'' := lot3 1 0 0 zero_le_one le_rfl le_rfl (by norm_num)
    L' = Mix ⟨1 / 3, by norm_num, by norm_num⟩ L'' L ∧ V L < V L'' ∧ V L' < V L := by
  intro V L L' L''
  refine ⟨?_, ?_, ?_⟩
  · apply StdSimplex.ext; ext n
    rw [lottery_mix_weight]
    fin_cases n <;> simp [L, L', L'', lot3] <;> norm_num
  · simp [V, L, L'', lot3]; norm_num
  · simp [V, L, L', lot3]; norm_num

/-- The Allais lotteries `L₁ = (0,1,0)`, `L₁' = (.10,.89,.01)`, `L₂ = (0,.11,.89)`,
`L₂' = (.10,0,.90)` (outcomes 2 500 000, 500 000 and 0 dollars). -/
noncomputable def allaisL1 : SimpleLottery (Fin 3) :=
  lot3 0 1 0 le_rfl zero_le_one le_rfl (by norm_num)

/-- `L₁' = (.10, .89, .01)`. -/
noncomputable def allaisL1' : SimpleLottery (Fin 3) :=
  lot3 (1 / 10) (89 / 100) (1 / 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- `L₂ = (0, .11, .89)`. -/
noncomputable def allaisL2 : SimpleLottery (Fin 3) :=
  lot3 0 (11 / 100) (89 / 100) le_rfl (by norm_num) (by norm_num) (by norm_num)

/-- `L₂' = (.10, 0, .90)`. -/
noncomputable def allaisL2' : SimpleLottery (Fin 3) :=
  lot3 (1 / 10) 0 (9 / 10) (by norm_num) le_rfl (by norm_num) (by norm_num)

/-- **Figure 6.B.7** (MWG, p. 179). `L₁' = L₁ + (.10, -.11, .01)` and
`L₂' = L₂ + (.10, -.11, .01)`: the segments `L₁L₁'` and `L₂L₂'` are parallel. -/
theorem figure_6_B_7 (n : Fin 3) :
    allaisL1'.weights n - allaisL1.weights n = ![1 / 10, -(11 / 100), 1 / 100] n ∧
    allaisL2'.weights n - allaisL2.weights n = ![1 / 10, -(11 / 100), 1 / 100] n := by
  fin_cases n <;> simp [allaisL1, allaisL1', allaisL2, allaisL2', lot3] <;> norm_num

/-- **Example 6.B.2** (MWG, p. 180), the Allais paradox: no expected utility function has
`L₁ ≻ L₁'` and `L₂' ≻ L₂`; indeed `L₁ ≻ L₁'` forces `L₂ ≻ L₂'`. -/
theorem example_6_B_2 (u : Fin 3 → ℝ) (h : eu u allaisL1' < eu u allaisL1) :
    eu u allaisL2' < eu u allaisL2 := by
  simp only [allaisL1, allaisL1', allaisL2, allaisL2', eu_lot3] at *
  linarith

/-- **Example 6.B.2** (MWG, p. 180). No rational, continuous preference satisfying the
independence axiom displays the Allais choices `L₁ ≻ L₁'` and `L₂' ≻ L₂`. -/
theorem example_6_B_2_axioms {r : SimpleLottery (Fin 3) → SimpleLottery (Fin 3) → Prop}
    (hr : Rational r) (hc : MixContinuous r) (hi : Independence r) :
    ¬(Strict r allaisL1 allaisL1' ∧ Strict r allaisL2' allaisL2) := by
  rintro ⟨h1, h2⟩
  obtain ⟨u, hu⟩ := proposition_6_B_3 hr hc hi
  have hs (L M) : Strict r L M ↔ eu u M < eu u L := by
    rw [Strict, hu, hu, not_le]; exact ⟨And.right, fun h => ⟨h.le, h⟩⟩
  rw [hs] at h1 h2
  exact absurd (example_6_B_2 u h1) (not_lt.mpr h2.le)

/-- **Example 6.B.3** (MWG, pp. 180-181), Machina's paradox: if "movie" is strictly preferred
to "home", independence forces `.999·Venice + .001·movie ≻ .999·Venice + .001·home`. -/
theorem example_6_B_3 {Z : Type*} [ConvexSpace ℝ Z] {r : Z → Z → Prop} (hi : Independence r)
    {venice movie home : Z} (h : Strict r movie home) :
    Strict r (Mix ⟨999 / 1000, by norm_num, by norm_num⟩ venice movie)
      (Mix ⟨999 / 1000, by norm_num, by norm_num⟩ venice home) := by
  have hl := independence_left hi movie home venice ⟨999 / 1000, by norm_num, by norm_num⟩
    (by norm_num) (by norm_num)
  have hl' := independence_left hi home movie venice ⟨999 / 1000, by norm_num, by norm_num⟩
    (by norm_num) (by norm_num)
  exact ⟨hl.mp h.1, fun h' => h.2 (hl'.mpr h')⟩

/-- **p. 181** (Dutch books). Independence implies the convexity of the not-better-than sets:
`L ≿ L'` and `L ≿ L''` imply `L ≿ αL' + (1 - α)L''`. -/
theorem dutchBook_convexity {Z : Type*} [ConvexSpace ℝ Z] {r : Z → Z → Prop}
    (hr : Rational r) (hi : Independence r) {L L' L'' : Z} (h' : r L L') (h'' : r L L'')
    (a : Weight) : r L (Mix a L' L'') := by
  have hs := noBetter_isConvexSet hr hi L
  exact hs.convexCombPair_mem h' h'' a.property.1 (sub_nonneg.mpr a.property.2) (by ring)

/-- The weighted utility `V(p) = ∑ w_n u_n p_n / ∑ w_n p_n` with `w = (1,1,10)` and
`u = (1, 3/5, 0)`, a betweenness preference that is not an expected utility. -/
noncomputable def weightedV (p : SimpleLottery (Fin 3)) : ℝ :=
  (p.weights 0 + 3 / 5 * p.weights 1) / (p.weights 0 + p.weights 1 + 10 * p.weights 2)

/-- The denominator of `weightedV` is positive. -/
theorem weightedV_den_pos (p : SimpleLottery (Fin 3)) :
    0 < p.weights 0 + p.weights 1 + 10 * p.weights 2 := by
  have h : p.weights 0 + p.weights 1 + p.weights 2 = 1 := by
    have := p.total_of_fintype
    rw [Fin.sum_univ_three] at this
    exact this
  have h0 := p.weights_nonneg 0
  have h1 := p.weights_nonneg 1
  have h2 := p.weights_nonneg 2
  linarith

/-- The preference represented by the weighted utility. -/
def weightedPref (p q : SimpleLottery (Fin 3)) : Prop := weightedV q ≤ weightedV p

/-- `weightedV` is a continuous function of the mixture weight. -/
theorem weightedV_mix_continuous (L L' : SimpleLottery (Fin 3)) :
    Continuous fun a : Weight => weightedV (Mix a L L') := by
  have hden (a : Weight) : (Mix a L L').weights 0 + (Mix a L L').weights 1 +
      10 * (Mix a L L').weights 2 ≠ 0 := (weightedV_den_pos _).ne'
  unfold weightedV
  simp only [lottery_mix_weight] at hden ⊢
  exact Continuous.div (by fun_prop) (by fun_prop) hden

/-- The weighted-utility preference is rational and continuous. -/
theorem weightedPref_rational_continuous : Rational weightedPref ∧ MixContinuous weightedPref := by
  refine ⟨⟨fun p q => le_total _ _, fun p q s h1 h2 => h2.trans h1⟩, fun L L' L'' => ?_⟩
  exact ⟨isClosed_le continuous_const (weightedV_mix_continuous L L'),
    isClosed_le (weightedV_mix_continuous L L') continuous_const⟩

/-- **Exercise 6.B.5(a)** (MWG, p. 209). The betweenness axiom: `L ∼ L'` and `λ ∈ (0,1)`
imply `λL + (1 - λ)L' ∼ L`. -/
def Betweenness {Z : Type*} [ConvexSpace ℝ Z] (r : Z → Z → Prop) : Prop :=
  ∀ (L L' : Z) (a : Weight), 0 < a.val → a.val < 1 → Indifferent r L L' →
    Indifferent r (Mix a L L') L

/-- **Exercise 6.B.5(a)** (MWG, p. 209). Independence implies betweenness. -/
theorem exercise_6_B_5a {Z : Type*} [ConvexSpace ℝ Z] {r : Z → Z → Prop} (hr : Rational r)
    (hi : Independence r) : Betweenness r :=
  fun _ _ a _ _ h => indifference_straight hr hi h a

/-- **Exercise 6.B.5(b)** (MWG, p. 209). For a rational preference, betweenness holds iff every
indifference set is closed under mixtures (the indifference curves are straight). -/
theorem exercise_6_B_5b {Z : Type*} [ConvexSpace ℝ Z] {r : Z → Z → Prop} (hr : Rational r) :
    Betweenness r ↔ ∀ L : Z, ∀ M M', Indifferent r M L → Indifferent r M' L →
      ∀ a : Weight, Indifferent r (Mix a M M') L := by
  constructor
  · intro hb L M M' hM hM' a
    rcases eq_or_lt_of_le a.property.1 with h0 | h0
    · have : a = 0 := Subtype.ext h0.symm
      rw [this, mix_zero]; exact hM'
    rcases eq_or_lt_of_le a.property.2 with h1 | h1
    · have : a = 1 := Subtype.ext h1
      rw [this, mix_one]; exact hM
    have hMM : Indifferent r M M' := ⟨hr.2 _ _ _ hM.1 hM'.2, hr.2 _ _ _ hM'.1 hM.2⟩
    have := hb M M' a h0 h1 hMM
    exact ⟨hr.2 _ _ _ this.1 hM.1, hr.2 _ _ _ hM.2 this.2⟩
  · intro h L L' a _ _ hLL
    exact h L L L' ⟨complete_refl hr.1 L, complete_refl hr.1 L⟩ ⟨hLL.2, hLL.1⟩ a

/-- The weighted-utility preference satisfies betweenness. -/
theorem weightedPref_betweenness : Betweenness weightedPref := by
  intro L L' a _ _ h
  have he : weightedV L = weightedV L' := le_antisymm h.2 h.1
  have hd := weightedV_den_pos L
  have hd' := weightedV_den_pos L'
  have hdm := weightedV_den_pos (Mix a L L')
  have hv : weightedV (Mix a L L') = weightedV L := by
    unfold weightedV at he ⊢
    rw [div_eq_div_iff hd.ne' hd'.ne'] at he
    rw [div_eq_div_iff hdm.ne' hd.ne']
    simp only [lottery_mix_weight]
    linear_combination (a.val - 1) * he
  exact ⟨hv.ge, hv.le⟩

/-- **Exercise 6.B.5(d)** (MWG, p. 209). The weighted-utility indifference map satisfies
betweenness and yields the Allais choices `L₁ ≻ L₁'` and `L₂' ≻ L₂`. -/
theorem exercise_6_B_5d :
    Betweenness weightedPref ∧ Strict weightedPref allaisL1 allaisL1' ∧
      Strict weightedPref allaisL2' allaisL2 := by
  have hs (L M) : Strict weightedPref L M ↔ weightedV M < weightedV L := by
    rw [Strict, weightedPref, weightedPref, not_le]; exact ⟨And.right, fun h => ⟨h.le, h⟩⟩
  refine ⟨weightedPref_betweenness, (hs _ _).mpr ?_, (hs _ _).mpr ?_⟩ <;>
    simp [weightedV, allaisL1, allaisL1', allaisL2, allaisL2', lot3] <;> norm_num

/-- **Exercise 6.B.5(b)-(c)** (MWG, p. 209). Betweenness is strictly weaker than independence:
the weighted-utility preference is rational, continuous and satisfies betweenness but not
independence, so its straight indifference lines are not parallel. -/
theorem exercise_6_B_5c : Rational weightedPref ∧ MixContinuous weightedPref ∧
    Betweenness weightedPref ∧ ¬Independence weightedPref := by
  obtain ⟨hr, hc⟩ := weightedPref_rational_continuous
  refine ⟨hr, hc, weightedPref_betweenness, fun hi => ?_⟩
  obtain ⟨-, h1, h2⟩ := exercise_6_B_5d
  exact example_6_B_2_axioms hr hc hi ⟨h1, h2⟩

/-- **p. 181**. Convexity of the not-better-than sets is weaker than independence: the
weighted-utility preference has convex not-better-than sets but violates independence. -/
theorem dutchBook_convexity_weaker :
    (∀ (L L' L'' : SimpleLottery (Fin 3)) (a : Weight), weightedPref L L' →
      weightedPref L L'' → weightedPref L (Mix a L' L'')) ∧ ¬Independence weightedPref := by
  refine ⟨fun L L' L'' a h' h'' => ?_, exercise_6_B_5c.2.2.2⟩
  unfold weightedPref weightedV at *
  have hd := weightedV_den_pos L
  have hd' := weightedV_den_pos L'
  have hd'' := weightedV_den_pos L''
  have hdm := weightedV_den_pos (Mix a L' L'')
  rw [div_le_div_iff₀ hd' hd] at h'
  rw [div_le_div_iff₀ hd'' hd] at h''
  rw [div_le_div_iff₀ hdm hd]
  simp only [lottery_mix_weight]
  nlinarith [a.property.1, a.property.2]

/-- **Exercise 6.B.4(a)** (MWG, p. 208). With `u(A) = 1`, `u(D) = 0`, `u(B) = p` and
`u(C) = qp` (outcomes indexed `A, B, C, D`), the indifferences `B ∼ pA + (1-p)D` and
`C ∼ qB + (1-q)D` hold. -/
theorem exercise_6_B_4a (p q : ℝ) :
    let u : Fin 4 → ℝ := ![1, p, q * p, 0]
    u 1 = p * u 0 + (1 - p) * u 3 ∧ u 2 = q * u 1 + (1 - q) * u 3 ∧ u 3 < u 0 := by
  simp

/-- **Exercise 6.B.4(b)** (MWG, p. 208). With flooding probability `1/100`, Criterion 1 gives
`(A,B,C,D) = (.891, .099, .009, .001)` and Criterion 2 gives `(.9405, .0495, .0095, .0005)`;
for all `p, q ∈ (0,1)` the agency strictly prefers Criterion 2. -/
theorem exercise_6_B_4b (p q : ℝ) (hp : p < 1) (hq : 0 < q) (hp0 : 0 < p) :
    let crit1 : Fin 4 → ℝ := ![99 / 100 * (9 / 10), 99 / 100 * (1 / 10), 1 / 100 * (9 / 10),
      1 / 100 * (1 / 10)]
    let crit2 : Fin 4 → ℝ := ![99 / 100 * (95 / 100), 99 / 100 * (5 / 100),
      1 / 100 * (95 / 100), 1 / 100 * (5 / 100)]
    let u : Fin 4 → ℝ := ![1, p, q * p, 0]
    crit1 = ![891 / 1000, 99 / 1000, 9 / 1000, 1 / 1000] ∧
      crit2 = ![9405 / 10000, 495 / 10000, 95 / 10000, 5 / 10000] ∧
      ∑ n, u n * crit1 n < ∑ n, u n * crit2 n := by
  intro crit1 crit2 u
  refine ⟨?_, ?_, ?_⟩
  · ext n; fin_cases n <;> simp [crit1] <;> norm_num
  · ext n; fin_cases n <;> simp [crit2] <;> norm_num
  · simp [crit1, crit2, u, Fin.sum_univ_succ]
    nlinarith [mul_pos hq hp0]

/-- **Exercise 6.B.6** (MWG, p. 209, and p. 182). The induced utility
`U(L) = max_{a ∈ A} ∑ p_n u_n(a)` over a finite nonempty action set is convex. -/
theorem exercise_6_B_6_convex {C A : Type*} [Fintype C] [Fintype A] [Nonempty A]
    (u : C → A → ℝ) (L L' : SimpleLottery C) (t : Weight) :
    Finset.univ.sup' Finset.univ_nonempty (fun a => ∑ n, (Mix t L L').weights n * u n a) ≤
      t.val * Finset.univ.sup' Finset.univ_nonempty (fun a => ∑ n, L.weights n * u n a) +
      (1 - t.val) * Finset.univ.sup' Finset.univ_nonempty
        (fun a => ∑ n, L'.weights n * u n a) := by
  apply Finset.sup'_le
  intro a _
  have e : ∑ n, (Mix t L L').weights n * u n a =
      t.val * ∑ n, L.weights n * u n a + (1 - t.val) * ∑ n, L'.weights n * u n a := by
    simp only [lottery_mix_weight, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
  rw [e]
  have h1 := Finset.le_sup' (fun a => ∑ n, L.weights n * u n a) (Finset.mem_univ a)
  have h2 := Finset.le_sup' (fun a => ∑ n, L'.weights n * u n a) (Finset.mem_univ a)
  have ht := t.property
  nlinarith [mul_le_mul_of_nonneg_left h1 ht.1,
    mul_le_mul_of_nonneg_left h2 (sub_nonneg.mpr ht.2)]

/-- A supremum over two actions is the larger of the two values. -/
theorem sup'_fin_two (f : Fin 2 → ℝ) :
    Finset.univ.sup' Finset.univ_nonempty f = max (f 0) (f 1) := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro a _
    fin_cases a
    · exact le_max_left _ _
    · exact le_max_right _ _
  · exact max_le (Finset.le_sup' f (Finset.mem_univ 0)) (Finset.le_sup' f (Finset.mem_univ 1))

/-- **Example 6.B.4 and Exercise 6.B.6** (MWG, pp. 181-182, 209). Induced preferences need not
be linear: with outcomes fish (`0`) and meat (`1`), actions white (`0`) and red (`1`) wine,
and `u_F(white) = u_M(red) = 1`, `u_F(red) = u_M(white) = 0`, the induced utility is `1` for
each sure outcome but `1/2` for the half-half lottery. -/
theorem example_6_B_4 :
    let u : Fin 2 → Fin 2 → ℝ := fun n a => if n = a then 1 else 0
    let U : SimpleLottery (Fin 2) → ℝ := fun L =>
      Finset.univ.sup' Finset.univ_nonempty (fun a => ∑ n, L.weights n * u n a)
    let half := lotteryOfVec ![1 / 2, 1 / 2] (by intro n; fin_cases n <;> norm_num)
      (by simp [Fin.sum_univ_succ]; norm_num)
    U (PureLottery 0) = 1 ∧ U (PureLottery 1) = 1 ∧ U half = 1 / 2 := by
  intro u U half
  classical
  refine ⟨?_, ?_, ?_⟩ <;> simp only [U, sup'_fin_two] <;>
    simp [u, half, degenerate_lottery_weights]

/-- **Example 6.B.4** (MWG, p. 182). With the ex ante action folded into the outcomes
("meat & red", "meat & white", "fish & red", "fish & white"), expected utility with
`u = (1, 0, 0, 1)` is indifferent among all lotteries between "meat & red" and
"fish & white", as the independence axiom requires. -/
theorem example_6_B_4_outcomes (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    eu ![1, 0, 0, 1] (lotteryOfVec ![a, 0, 0, 1 - a]
      (by intro n; fin_cases n <;> simp [ha0, ha1]) (by simp [Fin.sum_univ_succ])) = 1 := by
  simp [eu, Fin.sum_univ_succ]

/-- **Footnote 9** (MWG, p. 182). Actions taken after the uncertainty is resolved create no
problem: evaluating each outcome by its best ex post action, `u_n = max_{a ∈ A_n} u_n(a)`,
gives a utility of the expected utility form. -/
theorem footnote_6_9 {C A : Type*} [Fintype C] [Fintype A] [Nonempty A] (v : C → A → ℝ) :
    HasExpectedUtilityForm (fun L : SimpleLottery C =>
      ∑ n, L.weights n * Finset.univ.sup' Finset.univ_nonempty (v n)) :=
  ⟨fun n => Finset.univ.sup' Finset.univ_nonempty (v n), fun _ =>
    Finset.sum_congr rfl fun _ _ => mul_comm _ _⟩

/-- **Exercise 6.B.7** (MWG, p. 209). If preferences are transitive, `L ∼ x_L` and `L' ∼ x_{L'}`
for sure amounts, and larger sure amounts are strictly preferred (monotonicity), then `L ≻ L'`
iff `x_L > x_{L'}`. -/
theorem exercise_6_B_7 {Z : Type*} {r : Z → Z → Prop} (ht : TransitivePref r)
    (sure : ℝ → Z) (hmono : ∀ x y, y < x → Strict r (sure x) (sure y)) {L L' : Z} {xL xL' : ℝ}
    (hL : Indifferent r L (sure xL)) (hL' : Indifferent r L' (sure xL')) :
    Strict r L L' ↔ xL' < xL := by
  constructor
  · intro h
    by_contra hle
    rcases eq_or_lt_of_le (not_lt.mp hle) with he | hlt
    · subst he
      exact h.2 (ht _ _ _ hL'.1 hL.2)
    · have := hmono _ _ hlt
      exact h.2 (ht _ _ _ hL'.1 (strict_weak_trans ht this hL.2).1)
  · intro h
    have := hmono _ _ h
    exact weak_strict_trans ht hL.1 (strict_weak_trans ht this hL'.2)

end MWG.ChoiceUnderUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Lotteries over monetary outcomes

MWG, Section 6.C, pp. 183-185: money lotteries as distribution functions, the linear structure
of distribution functions, Figure 6.C.1, the expected utility form (6.C.1), the
St. Petersburg-Menger paradox and footnote 14.

A money lottery on a set `S ⊆ ℝ` of monetary amounts is a Borel probability measure `μ` on `ℝ`
concentrated on a compact interval `[a, b] ⊆ S` (`IsMoneyLottery`); its distribution function
is Mathlib's `cdf μ`, `F(x) = μ(-∞, x]`. MWG leaves the integrability of `u` and of `x`
unspecified; concentration on a compact interval guarantees that every expectation
`∫ u dF` of a continuous `u` exists (Section 6.D imposes exactly this, `F(0) = 0` and
`F(x̄) = 1`). The text's statement that the expected utility theorem yields (6.C.1),
`U(F) = ∫ u dF`, on all distributions is false under MWG's axioms: `atomicMass`, the total mass
of the atoms, is affine, so its preference is rational, continuous and satisfies independence,
but it has no Bernoulli utility (`expectedUtility_6_C_1_counterexample`).
-/

namespace MWG.ChoiceUnderUncertainty

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

/-- A money lottery on `S`: a probability measure on `ℝ` concentrated on a compact interval
contained in `S`. -/
def IsMoneyLottery (S : Set ℝ) (μ : Measure ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ ∃ a b, Icc a b ⊆ S ∧ μ (Icc a b)ᶜ = 0

/-- A money lottery is concentrated on its interval almost surely. -/
theorem IsMoneyLottery.ae_mem {S : Set ℝ} {μ : Measure ℝ} (h : IsMoneyLottery S μ) :
    ∃ a b, Icc a b ⊆ S ∧ ∀ᵐ x ∂μ, x ∈ Icc a b := by
  obtain ⟨-, a, b, hS, h0⟩ := h
  exact ⟨a, b, hS, measure_eq_zero_iff_ae_notMem.mp h0 |>.mono fun x hx => by simpa using hx⟩

/-- A function continuous on `S` is integrable for every money lottery on `S`. -/
theorem IsMoneyLottery.integrable {S : Set ℝ} {μ : Measure ℝ} (h : IsMoneyLottery S μ)
    {u : ℝ → ℝ} (hu : ContinuousOn u S) : Integrable u μ := by
  have := h.1
  obtain ⟨a, b, hS, h0⟩ := h.2
  have hr : μ.restrict (Icc a b) = μ := Measure.restrict_eq_self_of_ae_mem
    (measure_eq_zero_iff_ae_notMem.mp h0 |>.mono fun x hx => by simpa using hx)
  have hi : IntegrableOn u (Icc a b) μ := (hu.mono hS).integrableOn_compact isCompact_Icc
  rw [IntegrableOn, hr] at hi
  exact hi

/-- The identity (the monetary amount) is integrable for every money lottery. -/
theorem IsMoneyLottery.integrable_id {S : Set ℝ} {μ : Measure ℝ} (h : IsMoneyLottery S μ) :
    Integrable (fun x : ℝ => x) μ := by
  obtain ⟨hp, a, b, -, h0⟩ := h
  exact IsMoneyLottery.integrable (S := Icc a b) ⟨hp, a, b, le_rfl, h0⟩ continuousOn_id

/-- The mean of a money lottery lies in its interval, hence in `S`. -/
theorem IsMoneyLottery.mean_mem {S : Set ℝ} {μ : Measure ℝ} (h : IsMoneyLottery S μ) :
    ∃ a b, Icc a b ⊆ S ∧ (∀ᵐ x ∂μ, x ∈ Icc a b) ∧ ∫ x, x ∂μ ∈ Icc a b := by
  have := h.1
  obtain ⟨a, b, hS, hae⟩ := h.ae_mem
  refine ⟨a, b, hS, hae, ?_, ?_⟩
  · calc a = ∫ _, a ∂μ := by simp
      _ ≤ ∫ x, x ∂μ := integral_mono_ae (integrable_const a) h.integrable_id
          (hae.mono fun x hx => hx.1)
  · calc ∫ x, x ∂μ ≤ ∫ _, b ∂μ := integral_mono_ae h.integrable_id (integrable_const b)
          (hae.mono fun x hx => hx.2)
      _ = b := by simp

/-- The mean of a money lottery on `S` lies in `S`. -/
theorem IsMoneyLottery.mean_mem_S {S : Set ℝ} {μ : Measure ℝ} (h : IsMoneyLottery S μ) :
    ∫ x, x ∂μ ∈ S := by
  obtain ⟨a, b, hS, -, hm⟩ := h.mean_mem
  exact hS hm

/-- The binary lottery paying `x` with probability `p` and `y` with probability `1 - p`. -/
noncomputable def binLot (p x y : ℝ) : Measure ℝ :=
  ENNReal.ofReal p • Measure.dirac x + ENNReal.ofReal (1 - p) • Measure.dirac y

/-- Expectations under a binary lottery. -/
theorem integral_binLot (p x y : ℝ) (f : ℝ → ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∫ z, f z ∂(binLot p x y) = p * f x + (1 - p) * f y := by
  unfold binLot
  rw [integral_add_measure, integral_smul_measure, integral_smul_measure, integral_dirac,
    integral_dirac, ENNReal.toReal_ofReal hp0, ENNReal.toReal_ofReal (by linarith)]
  · simp [smul_eq_mul]
  · exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  · exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

/-- A binary lottery is a probability measure. -/
theorem binLot_isProbabilityMeasure (p x y : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsProbabilityMeasure (binLot p x y) := by
  constructor
  simp only [binLot, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add hp0 (by linarith)]
  simp

/-- A binary lottery with prizes in a convex `S` is a money lottery on `S`. -/
theorem binLot_isMoneyLottery {S : Set ℝ} (hS : Convex ℝ S) {x y : ℝ} (hx : x ∈ S) (hy : y ∈ S)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : IsMoneyLottery S (binLot p x y) := by
  refine ⟨binLot_isProbabilityMeasure p x y hp0 hp1, min x y, max x y,
    hS.ordConnected.uIcc_subset hx hy, ?_⟩
  simp only [binLot, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  rw [Measure.dirac_apply' _ (measurableSet_Icc.compl),
    Measure.dirac_apply' _ (measurableSet_Icc.compl)]
  simp

/-- The degenerate lottery at `x` is a money lottery on any `S ∋ x`. -/
theorem dirac_isMoneyLottery {S : Set ℝ} {x : ℝ} (hx : x ∈ S) :
    IsMoneyLottery S (Measure.dirac x) := by
  refine ⟨inferInstance, x, x, by simpa using hx, ?_⟩
  rw [Measure.dirac_apply' _ (measurableSet_Icc.compl)]
  simp

/-- The mixture `αF + (1 - α)G` of two lotteries. -/
noncomputable def mixM (a : ℝ) (μ ν : Measure ℝ) : Measure ℝ :=
  ENNReal.ofReal a • μ + ENNReal.ofReal (1 - a) • ν

/-- A mixture of probability measures is a probability measure. -/
theorem mixM_isProbabilityMeasure {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) {μ ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] : IsProbabilityMeasure (mixM a μ ν) := by
  constructor
  simp only [mixM, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add ha0 (by linarith)]
  simp

/-- The measure of a set under a mixture of probability measures. -/
theorem mixM_real {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) {μ ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (s : Set ℝ) :
    (mixM a μ ν).real s = a * μ.real s + (1 - a) * ν.real s := by
  simp only [mixM, measureReal_def, Measure.coe_add, Measure.coe_smul, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)), ENNReal.toReal_mul,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal ha0, ENNReal.toReal_ofReal (by linarith)]

/-- **p. 183**. Distribution functions preserve the linear structure of lotteries: the
distribution of the mixture `αF + (1 - α)G` is `αF(x) + (1 - α)G(x)`. -/
theorem cdf_mixM {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) {μ ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (x : ℝ) :
    cdf (mixM a μ ν) x = a * cdf μ x + (1 - a) * cdf ν x := by
  have := mixM_isProbabilityMeasure ha0 ha1 (μ := μ) (ν := ν)
  rw [cdf_eq_real, cdf_eq_real, cdf_eq_real, mixM_real ha0 ha1]

/-- The lottery of Figure 6.C.1: `1`, `4`, `6` dollars with probabilities `1/4`, `1/2`,
`1/4`. -/
noncomputable def figure_6_C_1_lottery : Measure ℝ :=
  ENNReal.ofReal (1 / 4) • Measure.dirac 1 + ENNReal.ofReal (1 / 2) • Measure.dirac 4 +
    ENNReal.ofReal (1 / 4) • Measure.dirac 6

/-- **Figure 6.C.1** (MWG, p. 184). The distribution function of the lottery is `0` on
`x < 1`, `1/4` on `[1,4)`, `3/4` on `[4,6)` and `1` on `x ≥ 6`. -/
theorem figure_6_C_1 (x : ℝ) :
    figure_6_C_1_lottery.real (Iic x) =
      if x < 1 then 0 else if x < 4 then 1 / 4 else if x < 6 then 3 / 4 else 1 := by
  have hd (c : ℝ) : (Measure.dirac c) (Iic x) = if c ≤ x then 1 else 0 := by
    rw [Measure.dirac_apply' _ measurableSet_Iic]
    by_cases h : c ≤ x <;> simp [h]
  simp only [figure_6_C_1_lottery, measureReal_def, Measure.coe_add, Measure.coe_smul,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, hd]
  split_ifs <;> first
    | (exfalso; linarith)
    | (simp only [mul_one, mul_zero, add_zero]
       rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
       try rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
       rw [ENNReal.toReal_ofReal (by norm_num)]; norm_num)
    | simp

/-- **p. 185** (St. Petersburg-Menger paradox). If `u(x_m) > 2^m` for every `m`, the lottery
paying `x_m` with probability `1/2^m` (`m ≥ 1`) has infinite expected utility: the partial sums
`∑_{m=1}^{N} u(x_m)/2^m` tend to `+∞`. -/
theorem stPetersburg (u : ℝ → ℝ) (x : ℕ → ℝ) (hx : ∀ m, (2 : ℝ) ^ m < u (x m)) :
    Tendsto (fun N => ∑ m ∈ Finset.Icc 1 N, u (x m) * (1 / 2) ^ m) atTop atTop := by
  have hterm (m : ℕ) : 1 < u (x m) * (1 / 2) ^ m := by
    have h2 : (0 : ℝ) < (1 / 2) ^ m := by positivity
    have : (2 : ℝ) ^ m * (1 / 2) ^ m = 1 := by rw [← mul_pow]; norm_num
    nlinarith [hx m]
  refine tendsto_atTop_mono (f := fun N : ℕ => (N : ℝ)) (fun N => ?_) tendsto_natCast_atTop_atTop
  calc (N : ℝ) = ∑ m ∈ Finset.Icc 1 N, (1 : ℝ) := by simp
    _ ≤ _ := Finset.sum_le_sum fun m _ => (hterm m).le

/-- **p. 185**. The St. Petersburg probabilities `1/2^m`, `m ≥ 1`, sum to one. -/
theorem stPetersburg_probabilities : HasSum (fun m : ℕ => (1 / 2 : ℝ) ^ (m + 1)) 1 := by
  have := hasSum_geometric_two' (1 : ℝ)
  convert this using 1
  ext m
  rw [pow_succ]
  field_simp
  rw [← mul_pow]
  norm_num

/-- For a concave function on the line that is bounded below, `u x ≤ u y` for all `x, y`. -/
theorem concave_bddBelow_le {u : ℝ → ℝ} (hc : ConcaveOn ℝ univ u) {m : ℝ}
    (hlow : ∀ z, m ≤ u z) (x y : ℝ) : u x ≤ u y := by
  by_contra hlt
  have hlt : u y < u x := lt_of_not_ge hlt
  have hd : 0 < u x - u y := by linarith
  obtain ⟨t, ht0, ht⟩ : ∃ t : ℝ, 0 < t ∧ u y - t * (u x - u y) < m := by
    refine ⟨(u y - m + 1) / (u x - u y) + 1, ?_, ?_⟩
    · have : 0 ≤ (u y - m + 1) / (u x - u y) :=
        div_nonneg (by linarith [hlow y]) hd.le
      linarith
    · rw [add_mul, div_mul_cancel₀ _ hd.ne']
      linarith
  have h1t : (1 : ℝ) + t ≠ 0 := by linarith
  have h1t' : (0 : ℝ) < 1 + t := by linarith
  set z := y + t * (y - x)
  have hy : (t / (1 + t)) • x + (1 / (1 + t)) • z = y := by
    simp only [smul_eq_mul, z]; field_simp; ring
  have hconc := hc.2 (mem_univ x) (mem_univ z) (show 0 ≤ t / (1 + t) by positivity)
    (show 0 ≤ 1 / (1 + t) by positivity)
    (by rw [← add_div, div_eq_one_iff_eq h1t]; ring)
  rw [hy] at hconc
  simp only [smul_eq_mul] at hconc
  have h1 : u z ≤ u y - t * (u x - u y) := by
    field_simp at hconc
    nlinarith
  linarith [hlow z]

/-- **Footnote 14** (MWG, p. 185). A concave function on `(-∞, ∞)` that is bounded below is
constant; so a nonconstant Bernoulli utility on the whole line cannot be both concave and
bounded (above and below). -/
theorem footnote_6_14 {u : ℝ → ℝ} (hc : ConcaveOn ℝ univ u) (hb : BddBelow (range u)) :
    ∀ x y, u x = u y := by
  obtain ⟨m, hm⟩ := hb
  have hlow (z : ℝ) : m ≤ u z := hm ⟨z, rfl⟩
  exact fun x y => le_antisymm (concave_bddBelow_le hc hlow x y) (concave_bddBelow_le hc hlow y x)

/-- MWG's continuity axiom (Definition 6.B.3) for a preference on the money lotteries on `S`:
`{α ∈ [0,1] : αF + (1 - α)G ≿ H}` and `{α ∈ [0,1] : H ≿ αF + (1 - α)G}` are closed. -/
def MoneyContinuous (S : Set ℝ) (r : Measure ℝ → Measure ℝ → Prop) : Prop :=
  ∀ μ ν η, IsMoneyLottery S μ → IsMoneyLottery S ν → IsMoneyLottery S η →
    IsClosed {a : Kreps.ChoiceUnderUncertainty.Weight | r (mixM a.val μ ν) η} ∧
    IsClosed {a : Kreps.ChoiceUnderUncertainty.Weight | r η (mixM a.val μ ν)}

/-- MWG's independence axiom (Definition 6.B.4) for a preference on the money lotteries on
`S`. -/
def MoneyIndependence (S : Set ℝ) (r : Measure ℝ → Measure ℝ → Prop) : Prop :=
  ∀ μ ν η, IsMoneyLottery S μ → IsMoneyLottery S ν → IsMoneyLottery S η →
    ∀ a : ℝ, 0 < a → a < 1 → (r μ ν ↔ r (mixM a μ η) (mixM a ν η))

/-- Completeness and transitivity on the money lotteries on `S`. -/
def MoneyRational (S : Set ℝ) (r : Measure ℝ → Measure ℝ → Prop) : Prop :=
  (∀ μ ν, IsMoneyLottery S μ → IsMoneyLottery S ν → r μ ν ∨ r ν μ) ∧
  ∀ μ ν η, IsMoneyLottery S μ → IsMoneyLottery S ν → IsMoneyLottery S η →
    r μ ν → r ν η → r μ η

/-- The total mass `∑_x F({x})` of the atoms of a lottery. -/
noncomputable def atomicMass (μ : Measure ℝ) : ℝ := (∑' x : ℝ, μ {x}).toReal

/-- The atoms of a probability measure have total mass at most one. -/
theorem tsum_atoms_le_one (μ : Measure ℝ) [IsProbabilityMeasure μ] : ∑' x : ℝ, μ {x} ≤ 1 :=
  (tsum_meas_le_meas_iUnion_of_disjoint μ (fun x => measurableSet_singleton x)
    (fun _ _ hxy => Set.disjoint_singleton.mpr hxy)).trans prob_le_one

/-- The atomic mass is affine in mixtures. -/
theorem atomicMass_mixM {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    atomicMass (mixM a μ ν) = a * atomicMass μ + (1 - a) * atomicMass ν := by
  have h1 := tsum_atoms_le_one μ
  have h2 := tsum_atoms_le_one ν
  have hμ : ∑' x : ℝ, μ {x} ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top h1
  have hν : ∑' x : ℝ, ν {x} ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top h2
  unfold atomicMass mixM
  simp only [Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left,
    ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hμ)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hν),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal ha0,
    ENNReal.toReal_ofReal (by linarith)]

/-- A degenerate lottery has atomic mass one. -/
theorem atomicMass_dirac (x : ℝ) : atomicMass (Measure.dirac x) = 1 := by
  unfold atomicMass
  have : (fun y : ℝ => Measure.dirac x {y}) = fun y => if y = x then 1 else 0 := by
    ext y
    rw [Measure.dirac_apply' _ (measurableSet_singleton y)]
    by_cases h : y = x
    · simp [h]
    · simp [h, Ne.symm h]
  rw [this, tsum_ite_eq]
  simp

/-- The uniform lottery on `[0,1]`. -/
noncomputable def uniform01 : Measure ℝ := volume.restrict (Icc 0 1)

/-- The uniform lottery on `[0,1]` is a money lottery on every `S ⊇ [0,1]`. -/
theorem uniform01_isMoneyLottery {S : Set ℝ} (hS : Icc 0 1 ⊆ S) :
    IsMoneyLottery S uniform01 := by
  refine ⟨⟨by simp [uniform01]⟩, 0, 1, hS, ?_⟩
  rw [uniform01, Measure.restrict_apply measurableSet_Icc.compl]
  simp

/-- The uniform lottery has no atoms. -/
theorem atomicMass_uniform01 : atomicMass uniform01 = 0 := by
  unfold atomicMass
  have : (fun y : ℝ => uniform01 {y}) = fun _ => 0 := by
    ext y
    exact le_antisymm ((Measure.restrict_apply_le _ _).trans_eq Real.volume_singleton) bot_le
  rw [this]
  simp

/-- **p. 184, (6.C.1)**: correction. MWG's axioms on general distributions do not yield the
integral form `U(F) = ∫ u dF`. The preference ranking lotteries by the total mass of their
atoms is rational, continuous and satisfies independence on all money lotteries, yet no
Bernoulli utility `u` represents it by `∫ u dF`. -/
theorem expectedUtility_6_C_1_counterexample :
    let r : Measure ℝ → Measure ℝ → Prop := fun μ ν => atomicMass ν ≤ atomicMass μ
    MoneyRational univ r ∧ MoneyContinuous univ r ∧ MoneyIndependence univ r ∧
      ¬∃ u : ℝ → ℝ, ∀ μ ν, IsMoneyLottery univ μ → IsMoneyLottery univ ν →
        (r μ ν ↔ ∫ x, u x ∂ν ≤ ∫ x, u x ∂μ) := by
  intro r
  refine ⟨⟨fun μ ν _ _ => le_total _ _, fun μ ν η _ _ _ h1 h2 => h2.trans h1⟩, ?_, ?_, ?_⟩
  · intro μ ν η hμ hν _
    have := hμ.1; have := hν.1
    have hc : Continuous fun a : Kreps.ChoiceUnderUncertainty.Weight =>
        atomicMass (mixM a.val μ ν) := by
      have : (fun a : Kreps.ChoiceUnderUncertainty.Weight => atomicMass (mixM a.val μ ν)) =
          fun a => a.val * atomicMass μ + (1 - a.val) * atomicMass ν :=
        funext fun a => atomicMass_mixM a.property.1 a.property.2 μ ν
      rw [this]; fun_prop
    exact ⟨isClosed_le continuous_const hc, isClosed_le hc continuous_const⟩
  · intro μ ν η hμ hν hη a ha0 ha1
    have := hμ.1; have := hν.1; have := hη.1
    change atomicMass ν ≤ atomicMass μ ↔ atomicMass (mixM a ν η) ≤ atomicMass (mixM a μ η)
    rw [atomicMass_mixM ha0.le ha1.le, atomicMass_mixM ha0.le ha1.le]
    constructor
    · intro h; nlinarith
    · intro h; nlinarith
  · rintro ⟨u, hu⟩
    have hconst (x y : ℝ) : u x = u y := by
      have h := hu (Measure.dirac x) (Measure.dirac y) (dirac_isMoneyLottery (mem_univ x))
        (dirac_isMoneyLottery (mem_univ y))
      have h' := hu (Measure.dirac y) (Measure.dirac x) (dirac_isMoneyLottery (mem_univ y))
        (dirac_isMoneyLottery (mem_univ x))
      simp only [r, atomicMass_dirac, le_refl, true_iff, integral_dirac] at h h'
      exact le_antisymm h' h
    have h := hu uniform01 (Measure.dirac 0) (uniform01_isMoneyLottery (subset_univ _))
      (dirac_isMoneyLottery (mem_univ 0))
    have hint : ∫ x, u x ∂uniform01 = u 0 := by
      have : IsProbabilityMeasure uniform01 := (uniform01_isMoneyLottery (subset_univ _)).1
      rw [show (fun x => u x) = fun _ => u 0 from funext fun x => hconst x 0]
      simp
    simp only [r, atomicMass_dirac, atomicMass_uniform01, integral_dirac, hint, le_refl,
      iff_true] at h
    norm_num at h

end MWG.ChoiceUnderUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Risk aversion, certainty equivalents and probability premia

MWG, Section 6.C, pp. 185-187: Definition 6.C.1 (risk aversion, risk neutrality, strict risk
aversion), Jensen's inequality (6.C.2), Definition 6.C.2 (certainty equivalent `c(F, u)` and
probability premium `π(x, ε, u)`), Figures 6.C.2-6.C.3, Proposition 6.C.1, footnote 16 and
Exercise 6.C.3.

Lotteries are the money lotteries of `MoneyLotteries` on a convex set `S` of monetary amounts.
The expected-utility preference of a Bernoulli utility `u` is `euPref u`. Throughout, `u` is
continuous on `S` and increasing (strictly, `StrictMonoOn`), MWG's maintained assumptions
(p. 185). The probability premium is the explicit solution `probPremium u x ε` of (6.C.4).
For (iv) ⇒ (ii) of Proposition 6.C.1 the midpoint inequality is upgraded to concavity by
continuity (Kreps's `midpoint_gap_nonneg`).
-/

namespace MWG.ChoiceUnderUncertainty

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

/-- The expected-utility preference of a Bernoulli utility `u`: `F ≿ G` iff
`∫ u dF ≥ ∫ u dG`. -/
def euPref (u : ℝ → ℝ) (μ ν : Measure ℝ) : Prop := ∫ x, u x ∂ν ≤ ∫ x, u x ∂μ

/-- **Definition 6.C.1** (MWG, p. 185). A decision maker is a risk averter if for every
lottery `F` the degenerate lottery at `∫ x dF` is at least as good as `F`. -/
def RiskAverter (S : Set ℝ) (r : Measure ℝ → Measure ℝ → Prop) : Prop :=
  ∀ μ, IsMoneyLottery S μ → r (Measure.dirac (∫ x, x ∂μ)) μ

/-- **Definition 6.C.1** (MWG, p. 185). Risk neutrality: always indifferent between `F` and
the degenerate lottery at its mean. -/
def RiskNeutral (S : Set ℝ) (r : Measure ℝ → Measure ℝ → Prop) : Prop :=
  ∀ μ, IsMoneyLottery S μ → r (Measure.dirac (∫ x, x ∂μ)) μ ∧ r μ (Measure.dirac (∫ x, x ∂μ))

/-- **Definition 6.C.1** (MWG, p. 185). Strict risk aversion: risk aversion, with indifference
only when `F` is degenerate. -/
def StrictlyRiskAverse (S : Set ℝ) (r : Measure ℝ → Measure ℝ → Prop) : Prop :=
  RiskAverter S r ∧ ∀ μ, IsMoneyLottery S μ → r μ (Measure.dirac (∫ x, x ∂μ)) →
    μ = Measure.dirac (∫ x, x ∂μ)

/-- **(6.C.2)** (MWG, p. 185). An expected utility maximizer is risk averse iff Jensen's
inequality `∫ u dF ≤ u(∫ x dF)` holds for all `F`. -/
theorem riskAverter_iff_jensen (S : Set ℝ) (u : ℝ → ℝ) :
    RiskAverter S (euPref u) ↔ ∀ μ, IsMoneyLottery S μ → ∫ x, u x ∂μ ≤ u (∫ x, x ∂μ) := by
  simp only [RiskAverter, euPref, integral_dirac]

/-- Jensen's inequality for a money lottery and a concave, continuous Bernoulli utility. -/
theorem jensen_moneyLottery {S : Set ℝ} {u : ℝ → ℝ} (hc : ConcaveOn ℝ S u)
    (hu : ContinuousOn u S) {μ : Measure ℝ} (hμ : IsMoneyLottery S μ) :
    ∫ x, u x ∂μ ≤ u (∫ x, x ∂μ) := by
  have := hμ.1
  obtain ⟨a, b, hS, hae⟩ := hμ.ae_mem
  exact (hc.subset hS (convex_Icc a b)).le_map_integral (hu.mono hS) isClosed_Icc hae
    hμ.integrable_id (hμ.integrable hu)

/-- The mean of the binary lottery `p x + (1 - p) y`. -/
theorem mean_binLot (p x y : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∫ z, z ∂(binLot p x y) = p * x + (1 - p) * y :=
  integral_binLot p x y id hp0 hp1

/-- **Proposition 6.C.1**, (i) ⇔ (ii) (MWG, p. 187). For a continuous Bernoulli utility on a
convex `S`, the expected utility maximizer is risk averse iff `u` is concave. -/
theorem proposition_6_C_1_i_ii {S : Set ℝ} (hS : Convex ℝ S) {u : ℝ → ℝ}
    (hu : ContinuousOn u S) : RiskAverter S (euPref u) ↔ ConcaveOn ℝ S u := by
  rw [riskAverter_iff_jensen]
  refine ⟨fun h => ⟨hS, fun x hx y hy a b ha hb hab => ?_⟩,
    fun hc μ hμ => jensen_moneyLottery hc hu hμ⟩
  have hb' : b = 1 - a := by linarith
  subst hb'
  have := h _ (binLot_isMoneyLottery hS hx hy a ha (by linarith))
  rw [integral_binLot _ _ _ _ ha (by linarith), mean_binLot _ _ _ ha (by linarith)] at this
  simpa only [smul_eq_mul] using this

/-- **Definition 6.C.2(i)** (MWG, p. 186). `c` is the certainty equivalent of `F`:
`u(c) = ∫ u dF` (6.C.3). -/
def IsCertaintyEquivalent (S : Set ℝ) (u : ℝ → ℝ) (μ : Measure ℝ) (c : ℝ) : Prop :=
  c ∈ S ∧ u c = ∫ x, u x ∂μ

/-- **Definition 6.C.2(i)** (MWG, p. 186). A continuous Bernoulli utility gives every money
lottery a certainty equivalent. -/
theorem certaintyEquivalent_exists {S : Set ℝ} {u : ℝ → ℝ} (hu : ContinuousOn u S)
    {μ : Measure ℝ} (hμ : IsMoneyLottery S μ) : ∃ c, IsCertaintyEquivalent S u μ c := by
  have := hμ.1
  obtain ⟨a, b, hS, hae, hm⟩ := hμ.mean_mem
  have hne : (Icc a b).Nonempty := ⟨_, hm⟩
  obtain ⟨p, hp, hpmin⟩ := isCompact_Icc.exists_isMinOn hne (hu.mono hS)
  obtain ⟨q, hq, hqmax⟩ := isCompact_Icc.exists_isMaxOn hne (hu.mono hS)
  have hlo : u p ≤ ∫ x, u x ∂μ := by
    calc u p = ∫ _, u p ∂μ := by simp
      _ ≤ ∫ x, u x ∂μ := integral_mono_ae (integrable_const _) (hμ.integrable hu)
          (hae.mono fun x hx => hpmin hx)
  have hhi : ∫ x, u x ∂μ ≤ u q := by
    calc ∫ x, u x ∂μ ≤ ∫ _, u q ∂μ := integral_mono_ae (hμ.integrable hu) (integrable_const _)
          (hae.mono fun x hx => hqmax hx)
      _ = u q := by simp
  have hsub : uIcc p q ⊆ Icc a b := (ordConnected_Icc).uIcc_subset hp hq
  obtain ⟨c, hc, hce⟩ := intermediate_value_uIcc ((hu.mono hS).mono hsub)
    ⟨(min_le_left _ _).trans hlo, hhi.trans (le_max_right _ _)⟩
  exact ⟨c, hS (hsub hc), hce⟩

/-- **Definition 6.C.2(i)** (MWG, p. 186). For an increasing Bernoulli utility the certainty
equivalent is unique. -/
theorem certaintyEquivalent_unique {S : Set ℝ} {u : ℝ → ℝ} (hi : StrictMonoOn u S)
    {μ : Measure ℝ} {c d : ℝ} (hc : IsCertaintyEquivalent S u μ c)
    (hd : IsCertaintyEquivalent S u μ d) : c = d :=
  hi.injOn hc.1 hd.1 (hc.2.trans hd.2.symm)

/-- **Definition 6.C.2(ii)** (MWG, p. 186). The probability premium `π(x, ε, u)`, the excess
winning probability over fair odds solving (6.C.4). -/
noncomputable def probPremium (u : ℝ → ℝ) (x ε : ℝ) : ℝ :=
  (2 * u x - u (x + ε) - u (x - ε)) / (2 * (u (x + ε) - u (x - ε)))

/-- **(6.C.4)** (MWG, p. 186). `u(x) = (1/2 + π) u(x + ε) + (1/2 - π) u(x - ε)`, and `π` is the
unique such number. -/
theorem probPremium_spec (u : ℝ → ℝ) (x ε : ℝ) (h : u (x - ε) < u (x + ε)) :
    u x = (1 / 2 + probPremium u x ε) * u (x + ε) + (1 / 2 - probPremium u x ε) * u (x - ε) ∧
    ∀ q, u x = (1 / 2 + q) * u (x + ε) + (1 / 2 - q) * u (x - ε) → q = probPremium u x ε := by
  have hd : 2 * (u (x + ε) - u (x - ε)) ≠ 0 := by linarith
  have hd' : u (x + ε) - u (x - ε) ≠ 0 := by linarith
  constructor
  · unfold probPremium
    field_simp
    ring
  · intro q hq
    unfold probPremium
    rw [eq_div_iff hd]
    linarith

/-- **Figure 6.C.3(b)** (MWG, p. 187). The mean of the premium gamble is
`(1/2 + π)(x + ε) + (1/2 - π)(x - ε) = x + 2επ`. -/
theorem figure_6_C_3b (x ε q : ℝ) :
    (1 / 2 + q) * (x + ε) + (1 / 2 - q) * (x - ε) = x + 2 * ε * q := by ring

/-- **Figure 6.C.2(a)** (MWG, p. 186). For a strictly concave `u` the gamble between `1` and `3`
dollars has utility `u(1)/2 + u(3)/2 < u(2)`. -/
theorem figure_6_C_2a {u : ℝ → ℝ} {S : Set ℝ} (hc : StrictConcaveOn ℝ S u) (h1 : (1 : ℝ) ∈ S)
    (h3 : (3 : ℝ) ∈ S) : u 1 / 2 + u 3 / 2 < u 2 := by
  have := hc.2 h1 h3 (by norm_num : (1 : ℝ) ≠ 3) (show (0 : ℝ) < 1 / 2 by norm_num)
    (show (0 : ℝ) < 1 / 2 by norm_num) (by norm_num)
  norm_num at this
  linarith

/-- **Figure 6.C.2(b)** (MWG, p. 186). For a linear (affine) `u`, `u(1)/2 + u(3)/2 = u(2)`. -/
theorem figure_6_C_2b (α β : ℝ) :
    (fun x : ℝ => α * x + β) 1 / 2 + (fun x : ℝ => α * x + β) 3 / 2 = (fun x => α * x + β) 2 :=
  by ring

/-- **Proposition 6.C.1**, (ii) ⇔ (iii) (MWG, p. 187). For a continuous, increasing Bernoulli
utility, `u` is concave iff `c(F, u) ≤ ∫ x dF` for every `F`. -/
theorem proposition_6_C_1_ii_iii {S : Set ℝ} (hS : Convex ℝ S) {u : ℝ → ℝ}
    (hu : ContinuousOn u S) (hi : StrictMonoOn u S) :
    ConcaveOn ℝ S u ↔ ∀ μ c, IsMoneyLottery S μ → IsCertaintyEquivalent S u μ c →
      c ≤ ∫ x, x ∂μ := by
  constructor
  · intro hc μ c hμ hce
    have hj := jensen_moneyLottery hc hu hμ
    rw [← hce.2] at hj
    exact (hi.le_iff_le hce.1 hμ.mean_mem_S).mp hj
  · intro h
    rw [← proposition_6_C_1_i_ii hS hu, riskAverter_iff_jensen]
    intro μ hμ
    obtain ⟨c, hce⟩ := certaintyEquivalent_exists hu hμ
    rw [← hce.2]
    exact (hi.le_iff_le hce.1 hμ.mean_mem_S).mpr (h μ c hμ hce)

/-- **(iii)** and the chain on p. 187: `c(F, u) ≤ ∫ x dF` iff `u(c(F, u)) ≤ u(∫ x dF)` iff
`∫ u dF ≤ u(∫ x dF)`. -/
theorem certaintyEquivalent_le_mean_iff {S : Set ℝ} {u : ℝ → ℝ} (hi : StrictMonoOn u S)
    {μ : Measure ℝ} (hμ : IsMoneyLottery S μ) {c : ℝ} (hce : IsCertaintyEquivalent S u μ c) :
    c ≤ ∫ x, x ∂μ ↔ ∫ x, u x ∂μ ≤ u (∫ x, x ∂μ) := by
  rw [← hce.2]
  exact (hi.le_iff_le hce.1 hμ.mean_mem_S).symm

/-- Midpoint concavity and continuity on a convex set give concavity. -/
theorem concaveOn_of_midpoint {S : Set ℝ} (hS : Convex ℝ S) {u : ℝ → ℝ}
    (hu : ContinuousOn u S) (hm : ∀ x ∈ S, ∀ y ∈ S, (u x + u y) / 2 ≤ u ((x + y) / 2)) :
    ConcaveOn ℝ S u := by
  refine ⟨hS, fun x hx y hy a b ha hb hab => ?_⟩
  -- the gap along the segment from `y` (t = 0) to `x` (t = 1)
  let p : ℝ → ℝ := fun t => t * x + (1 - t) * y
  have hp (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : p t ∈ S := by
    have := hS hx hy ht.1 (sub_nonneg.mpr ht.2) (by ring)
    simpa [p, smul_eq_mul] using this
  let f : ℝ → ℝ := fun t => u (p t) - (t * u x + (1 - t) * u y)
  have hfc : ContinuousOn f (Icc 0 1) := by
    have hpc : ContinuousOn p (Icc 0 1) := by fun_prop
    exact (hu.comp hpc fun t ht => hp t ht).sub (by fun_prop)
  have hfm : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, (f s + f t) / 2 ≤ f ((s + t) / 2) := by
    intro s hs t ht
    have hmid := hm (p s) (hp s hs) (p t) (hp t ht)
    have he : (p s + p t) / 2 = p ((s + t) / 2) := by simp only [p]; ring
    rw [he] at hmid
    simp only [f]
    linarith
  have h0 : f 0 = 0 := by simp [f, p]
  have h1 : f 1 = 0 := by simp [f, p]
  have := Kreps.UtilityForMoney.midpoint_gap_nonneg f hfc hfm h0 h1 a ⟨ha, by linarith⟩
  have hb' : b = 1 - a := by linarith
  subst hb'
  simp only [f, p, smul_eq_mul] at this ⊢
  linarith

/-- **Proposition 6.C.1**, (ii) ⇔ (iv) (MWG, p. 187; Exercise 6.C.3, p. 210). For a
continuous, increasing Bernoulli utility, `u` is concave iff `π(x, ε, u) ≥ 0` for all `x` and
`ε > 0` (with `x ± ε ∈ S`). -/
theorem proposition_6_C_1_ii_iv {S : Set ℝ} (hS : Convex ℝ S) {u : ℝ → ℝ}
    (hu : ContinuousOn u S) (hi : StrictMonoOn u S) :
    ConcaveOn ℝ S u ↔ ∀ x ε, 0 < ε → x - ε ∈ S → x + ε ∈ S → 0 ≤ probPremium u x ε := by
  constructor
  · intro hc x ε hε h1 h2
    have hlt : u (x - ε) < u (x + ε) := hi h1 h2 (by linarith)
    have hmid := hc.2 h2 h1 (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      (by norm_num)
    simp only [smul_eq_mul] at hmid
    have he : 1 / 2 * (x + ε) + 1 / 2 * (x - ε) = x := by ring
    rw [he] at hmid
    unfold probPremium
    apply div_nonneg <;> linarith
  · intro h
    apply concaveOn_of_midpoint hS hu
    intro x hx y hy
    rcases lt_trichotomy x y with hxy | hxy | hxy
    · have hε : 0 < (y - x) / 2 := by linarith
      have h1 : (x + y) / 2 - (y - x) / 2 = x := by ring
      have h2 : (x + y) / 2 + (y - x) / 2 = y := by ring
      have hp := h ((x + y) / 2) ((y - x) / 2) hε (by rw [h1]; exact hx) (by rw [h2]; exact hy)
      unfold probPremium at hp
      rw [h1, h2] at hp
      have hlt : u x < u y := hi hx hy hxy
      have := (div_nonneg_iff.mp hp)
      rcases this with ⟨hn, _⟩ | ⟨_, hd⟩
      · linarith
      · linarith
    · subst hxy; simp
    · have hε : 0 < (x - y) / 2 := by linarith
      have h1 : (x + y) / 2 - (x - y) / 2 = y := by ring
      have h2 : (x + y) / 2 + (x - y) / 2 = x := by ring
      have hp := h ((x + y) / 2) ((x - y) / 2) hε (by rw [h1]; exact hy) (by rw [h2]; exact hx)
      unfold probPremium at hp
      rw [h1, h2] at hp
      have hlt : u y < u x := hi hy hx hxy
      rcases div_nonneg_iff.mp hp with ⟨hn, _⟩ | ⟨_, hd⟩
      · linarith
      · linarith

/-- **Proposition 6.C.1** (MWG, p. 187). For an expected utility maximizer with a continuous,
increasing Bernoulli utility on a convex set of monetary amounts, the following are
equivalent: (i) risk aversion; (ii) concavity of `u`; (iii) `c(F, u) ≤ ∫ x dF` for all `F`;
(iv) `π(x, ε, u) ≥ 0` for all `x, ε`. -/
theorem proposition_6_C_1 {S : Set ℝ} (hS : Convex ℝ S) {u : ℝ → ℝ} (hu : ContinuousOn u S)
    (hi : StrictMonoOn u S) :
    List.TFAE [RiskAverter S (euPref u), ConcaveOn ℝ S u,
      ∀ μ c, IsMoneyLottery S μ → IsCertaintyEquivalent S u μ c → c ≤ ∫ x, x ∂μ,
      ∀ x ε, 0 < ε → x - ε ∈ S → x + ε ∈ S → 0 ≤ probPremium u x ε] := by
  tfae_have 1 ↔ 2 := proposition_6_C_1_i_ii hS hu
  tfae_have 2 ↔ 3 := proposition_6_C_1_ii_iii hS hu hi
  tfae_have 2 ↔ 4 := proposition_6_C_1_ii_iv hS hu hi
  tfae_finish

/-- **Exercise 6.C.3** (MWG, p. 210). The four conditions of Proposition 6.C.1 are equivalent;
in particular (iv) gives `u(x/2 + y/2) ≥ u(x)/2 + u(y)/2`, which with continuity is
sufficient for concavity. -/
theorem exercise_6_C_3 {S : Set ℝ} (hS : Convex ℝ S) {u : ℝ → ℝ} (hu : ContinuousOn u S)
    (hi : StrictMonoOn u S) :
    (RiskAverter S (euPref u) → ∀ x ε, 0 < ε → x - ε ∈ S → x + ε ∈ S →
      0 ≤ probPremium u x ε) ∧
    ((∀ x ε, 0 < ε → x - ε ∈ S → x + ε ∈ S → 0 ≤ probPremium u x ε) →
      ∀ x ∈ S, ∀ y ∈ S, (u x + u y) / 2 ≤ u ((x + y) / 2)) := by
  constructor
  · intro h
    exact (proposition_6_C_1_ii_iv hS hu hi).mp ((proposition_6_C_1_i_ii hS hu).mp h)
  · intro h x hx y hy
    have hc := (proposition_6_C_1_ii_iv hS hu hi).mpr h
    have := hc.2 hx hy (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      (by norm_num)
    simp only [smul_eq_mul] at this
    have e : 1 / 2 * x + 1 / 2 * y = (x + y) / 2 := by ring
    rw [e] at this
    linarith

/-- A probability measure under which the identity is almost surely constant is degenerate. -/
theorem eq_dirac_of_ae_eq_const {μ : Measure ℝ} [IsProbabilityMeasure μ] {c : ℝ}
    (h : (fun x : ℝ => x) =ᵐ[μ] fun _ => c) : μ = Measure.dirac c := by
  have hne : μ {x | x ≠ c} = 0 := by
    have := h
    rw [Filter.EventuallyEq, ae_iff] at this
    simpa using this
  ext s hs
  rw [Measure.dirac_apply' _ hs]
  by_cases hc : c ∈ s
  · rw [indicator_of_mem hc]
    apply le_antisymm prob_le_one
    have hsub : sᶜ ⊆ {x | x ≠ c} := fun x hx hxc => hx (hxc ▸ hc)
    have h0 : μ sᶜ = 0 := measure_mono_null hsub hne
    rw [prob_compl_eq_zero_iff hs] at h0
    rw [h0]
  · rw [indicator_of_notMem hc]
    exact measure_mono_null (fun x hx => show x ≠ c from fun hxc => hc (hxc ▸ hx)) hne

/-- **p. 186**. Strict risk aversion is equivalent to strict concavity of `u`. -/
theorem strictlyRiskAverse_iff {S : Set ℝ} (hS : Convex ℝ S) {u : ℝ → ℝ}
    (hu : ContinuousOn u S) : StrictlyRiskAverse S (euPref u) ↔ StrictConcaveOn ℝ S u := by
  constructor
  · rintro ⟨hra, hstr⟩
    have hc := (proposition_6_C_1_i_ii hS hu).mp hra
    refine ⟨hS, fun x hx y hy hxy a b ha hb hab => ?_⟩
    have hb' : b = 1 - a := by linarith
    subst hb'
    have hμ := binLot_isMoneyLottery hS hx hy a ha.le (by linarith)
    have hle := hc.2 hx hy ha.le hb.le hab
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact hlt
    · exfalso
      have hind : euPref u (binLot a x y) (Measure.dirac (∫ z, z ∂(binLot a x y))) := by
        simp only [euPref, integral_dirac, integral_binLot _ _ _ _ ha.le (by linarith : a ≤ 1)]
        simp only [smul_eq_mul] at heq
        exact heq.ge
      have hdeg := hstr _ hμ hind
      rw [mean_binLot _ _ _ ha.le (by linarith)] at hdeg
      have hval : binLot a x y {x} = Measure.dirac (a * x + (1 - a) * y) {x} := by rw [← hdeg]
      have hL : binLot a x y {x} = ENNReal.ofReal a := by
        simp [binLot, Measure.dirac_apply' _ (measurableSet_singleton x), Ne.symm hxy]
      rw [hL, Measure.dirac_apply' _ (measurableSet_singleton x)] at hval
      by_cases hm : a * x + (1 - a) * y = x
      · have : (1 - a) * (y - x) = 0 := by linarith
        rcases mul_eq_zero.mp this with h | h
        · linarith
        · exact hxy (by linarith)
      · rw [indicator_of_notMem (by simpa using hm)] at hval
        rw [ENNReal.ofReal_eq_zero] at hval
        linarith
  · intro hsc
    have hc := hsc.concaveOn
    refine ⟨(proposition_6_C_1_i_ii hS hu).mpr hc, fun μ hμ hind => ?_⟩
    have := hμ.1
    obtain ⟨a, b, hSab, hae⟩ := hμ.ae_mem
    have hstrict := (hsc.subset hSab (convex_Icc a b)).ae_eq_const_or_lt_map_average
      (hu.mono hSab) isClosed_Icc hae hμ.integrable_id (hμ.integrable hu)
    simp only [average_eq_integral] at hstrict
    rcases hstrict with hconst | hlt
    · exact eq_dirac_of_ae_eq_const hconst
    · exfalso
      simp only [euPref, integral_dirac] at hind
      exact absurd hind (not_le.mpr hlt)

/-- **p. 186**. Risk neutrality is equivalent to `u` being linear (affine) on `S`. -/
theorem riskNeutral_iff_affine {S : Set ℝ} (hS : Convex ℝ S) {u : ℝ → ℝ}
    (hu : ContinuousOn u S) :
    RiskNeutral S (euPref u) ↔ ConcaveOn ℝ S u ∧ ConvexOn ℝ S u := by
  constructor
  · intro h
    refine ⟨(proposition_6_C_1_i_ii hS hu).mp fun μ hμ => (h μ hμ).1,
      ⟨hS, fun x hx y hy a b ha hb hab => ?_⟩⟩
    have hb' : b = 1 - a := by linarith
    subst hb'
    have := (h _ (binLot_isMoneyLottery hS hx hy a ha (by linarith))).2
    simp only [euPref, integral_dirac, integral_binLot _ _ _ _ ha (by linarith : a ≤ 1)] at this
    simpa only [smul_eq_mul] using this
  · rintro ⟨hc, hv⟩ μ hμ
    have := hμ.1
    obtain ⟨a, b, hSab, hae⟩ := hμ.ae_mem
    refine ⟨(proposition_6_C_1_i_ii hS hu).mpr hc μ hμ, ?_⟩
    simp only [euPref, integral_dirac]
    exact (hv.subset hSab (convex_Icc a b)).map_integral_le (hu.mono hSab) isClosed_Icc hae
      hμ.integrable_id (hμ.integrable hu)

/-- **Footnote 16** (MWG, p. 187). For a twice differentiable `u` on an open convex set,
concavity is equivalent to `u''(x) ≤ 0` for all `x`. -/
theorem footnote_6_16 {S : Set ℝ} (hS : Convex ℝ S) (ho : IsOpen S) {u : ℝ → ℝ}
    (h1 : ∀ x ∈ S, DifferentiableAt ℝ u x) (h2 : ∀ x ∈ S, DifferentiableAt ℝ (deriv u) x) :
    ConcaveOn ℝ S u ↔ ∀ x ∈ S, deriv (deriv u) x ≤ 0 := by
  constructor
  · intro hc x hx
    have hant := hc.antitoneOn_deriv h1
    have := hant.derivWithin_nonpos (x := x)
    rwa [derivWithin_of_isOpen ho hx] at this
  · intro h
    have hint : interior S = S := ho.interior_eq
    apply concaveOn_of_deriv2_nonpos hS
      (fun x hx => (h1 x hx).continuousAt.continuousWithinAt)
    · rw [hint]; exact fun x hx => (h1 x hx).differentiableWithinAt
    · rw [hint]; exact fun x hx => (h2 x hx).differentiableWithinAt
    · rw [hint]; intro x hx
      simpa only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply,
        Function.id_comp] using h x hx

end MWG.ChoiceUnderUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Insurance and the demand for risky assets

MWG, Section 6.C, pp. 187-189: Example 6.C.1 (insurance; full insurance at actuarially fair
prices), Exercise 6.C.1 (incomplete insurance at unfair prices), Example 6.C.2 (a risk averter
always holds some of an actuarially favorable asset) with footnote 17, and Example 6.C.3 with
Exercise 6.C.4 (the portfolio utility `U(α) = ∫ u(α · z) dF(z)` is increasing, concave and
continuous).

The insurance objective is `(1 - π) u(w - αq) + π u(w - αq - D + α)` over `α ≥ 0` (MWG's
domain, not Kreps's unrestricted coverage). Bernoulli utilities are defined on the whole line,
so wealth levels need not be restricted. Asset returns have a distribution with compact support
(the convention of `MoneyLotteries`).
-/

namespace MWG.ChoiceUnderUncertainty

open MeasureTheory Filter Topology Set

/-- Expected utility of buying `α` units of insurance (MWG, p. 188). -/
def insuranceEU (u : ℝ → ℝ) (w D π q α : ℝ) : ℝ :=
  (1 - π) * u (w - α * q) + π * u (w - α * q - D + α)

/-- **Example 6.C.1** (MWG, p. 187). Expected wealth with `α` units of insurance is
`w - πD + α(π - q)`. -/
theorem example_6_C_1_expected_wealth (w D π q α : ℝ) :
    (1 - π) * (w - α * q) + π * (w - α * q - D + α) = w - π * D + α * (π - q) := by ring

/-- A first-order necessary condition at a maximum over `[x, ∞)`: the derivative is `≤ 0`. -/
theorem deriv_nonpos_of_max_Ici {f : ℝ → ℝ} {f' x : ℝ} (hf : HasDerivAt f f' x)
    (hmax : ∀ y, x ≤ y → f y ≤ f x) : f' ≤ 0 := by
  by_contra hpos
  have hpos : 0 < f' := lt_of_not_ge hpos
  have hev := hf.tendsto_slope_zero_right.eventually (lt_mem_nhds hpos)
  obtain ⟨t, ht, ht0⟩ := (hev.and self_mem_nhdsWithin).exists
  have ht0' : (0 : ℝ) < t := ht0
  have := hmax (x + t) (by linarith)
  rw [smul_eq_mul] at ht
  have : t⁻¹ * (f (x + t) - f x) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr ht0'.le) (by linarith)
  linarith

/-- The derivative of the insurance objective in `α`. -/
theorem insuranceEU_hasDerivAt {u : ℝ → ℝ} (w D π q α : ℝ)
    (h1 : DifferentiableAt ℝ u (w - α * q)) (h2 : DifferentiableAt ℝ u (w - D + α * (1 - q))) :
    HasDerivAt (insuranceEU u w D π q)
      (-q * (1 - π) * deriv u (w - α * q) + π * (1 - q) * deriv u (w - D + α * (1 - q))) α := by
  have ha : HasDerivAt (fun a : ℝ => w - a * q) (-q) α := by
    simpa using ((hasDerivAt_id' α).mul_const q).const_sub w
  have hb : HasDerivAt (fun a : ℝ => w - D + a * (1 - q)) (1 - q) α := by
    simpa using ((hasDerivAt_id' α).mul_const (1 - q)).const_add (w - D)
  have hu1 : HasDerivAt (fun a => u (w - a * q)) (deriv u (w - α * q) * -q) α :=
    h1.hasDerivAt.comp α ha
  have hu2 : HasDerivAt (fun a => u (w - D + a * (1 - q)))
      (deriv u (w - D + α * (1 - q)) * (1 - q)) α := h2.hasDerivAt.comp α hb
  have hfun : insuranceEU u w D π q =
      fun a => (1 - π) * u (w - a * q) + π * u (w - D + a * (1 - q)) := by
    funext a
    unfold insuranceEU
    rw [show w - a * q - D + a = w - D + a * (1 - q) by ring]
  rw [hfun]
  convert (hu1.const_mul (1 - π)).add (hu2.const_mul π) using 1
  ring

/-- **Example 6.C.1** (MWG, p. 188), the first-order condition: at an optimum `α* ≥ 0`,
`-q(1 - π)u'(w - α*q) + π(1 - q)u'(w - D + α*(1 - q)) ≤ 0`, with equality if `α* > 0`. -/
theorem example_6_C_1_foc {u : ℝ → ℝ} {w D π q a : ℝ} (ha : 0 ≤ a)
    (hopt : ∀ b, 0 ≤ b → insuranceEU u w D π q b ≤ insuranceEU u w D π q a)
    (h1 : DifferentiableAt ℝ u (w - a * q)) (h2 : DifferentiableAt ℝ u (w - D + a * (1 - q))) :
    -q * (1 - π) * deriv u (w - a * q) + π * (1 - q) * deriv u (w - D + a * (1 - q)) ≤ 0 ∧
    (0 < a →
      -q * (1 - π) * deriv u (w - a * q) + π * (1 - q) * deriv u (w - D + a * (1 - q)) = 0) := by
  have hd := insuranceEU_hasDerivAt w D π q a h1 h2
  refine ⟨deriv_nonpos_of_max_Ici hd fun b hb => hopt b (ha.trans hb), fun hpos => ?_⟩
  have hloc : IsLocalMax (insuranceEU u w D π q) a := by
    filter_upwards [lt_mem_nhds hpos] with b hb
    exact hopt b hb.le
  exact hloc.hasDerivAt_eq_zero hd

/-- **Example 6.C.1** (MWG, pp. 188-189). With actuarially fair insurance (`q = π`) a strictly
risk-averse decision maker insures completely: `α = D` is the unique optimum, giving final
wealth `w - πD` in both states. -/
theorem example_6_C_1 {u : ℝ → ℝ} (hc : StrictConcaveOn ℝ univ u) {π : ℝ} (h0 : 0 < π)
    (h1 : π < 1) (w D : ℝ) :
    (∀ α, insuranceEU u w D π π α ≤ insuranceEU u w D π π D) ∧
    (∀ α, insuranceEU u w D π π α = insuranceEU u w D π π D → α = D) ∧
    insuranceEU u w D π π D = u (w - π * D) := by
  have hD : insuranceEU u w D π π D = u (w - π * D) := by
    unfold insuranceEU
    rw [show w - D * π - D + D = w - π * D by ring, show w - D * π = w - π * D by ring]
    ring
  have key (α : ℝ) (hα : α ≠ D) : insuranceEU u w D π π α < u (w - π * D) := by
    have hne : w - α * π ≠ w - α * π - D + α := by
      intro h; exact hα (by linarith)
    have := hc.2 (mem_univ (w - α * π)) (mem_univ (w - α * π - D + α)) hne
      (show 0 < 1 - π by linarith) h0 (by ring)
    simp only [smul_eq_mul] at this
    rw [show (1 - π) * (w - α * π) + π * (w - α * π - D + α) = w - π * D by ring] at this
    exact this
  refine ⟨fun α => ?_, fun α hα => ?_, hD⟩
  · by_cases hα : α = D
    · rw [hα]
    · rw [hD]; exact (key α hα).le
  · by_contra hne
    have := key α hne
    rw [hα, hD] at this
    exact lt_irrefl _ this

/-- **Exercise 6.C.1** (MWG, p. 209). If insurance is not actuarially fair (`q > π`), a
strictly increasing, concave, differentiable Bernoulli utility never insures completely: every
optimum over `α ≥ 0` has `α < D`. -/
theorem exercise_6_C_1 {u : ℝ → ℝ} (hc : ConcaveOn ℝ univ u) (hi : StrictMono u)
    (hd : Differentiable ℝ u) {w D π q a : ℝ} (hD : 0 < D) (h0 : 0 ≤ π) (h1 : π ≤ 1)
    (hq : π < q)
    (hopt : ∀ b, 0 ≤ b → insuranceEU u w D π q b ≤ insuranceEU u w D π q a) : a < D := by
  have hfull : insuranceEU u w D π q D = u (w - D * q) := by
    unfold insuranceEU
    rw [show w - D * q - D + D = w - D * q by ring]
    ring
  rcases lt_trichotomy a D with hlt | heq | hgt
  · exact hlt
  · exfalso
    subst heq
    have hloc : IsLocalMax (insuranceEU u w a π q) a := by
      filter_upwards [lt_mem_nhds hD] with b hb
      exact hopt b hb.le
    have hder := insuranceEU_hasDerivAt (u := u) w a π q a (hd _) (hd _)
    have hz := hloc.hasDerivAt_eq_zero hder
    rw [show w - a + a * (1 - q) = w - a * q by ring] at hz
    have hpos := Kreps.UtilityForMoney.deriv_pos_of_concave_strictMono hc hi (hd (w - a * q))
    have : (π - q) * deriv u (w - a * q) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · linarith
  · exfalso
    have hmean := hc.2 (mem_univ (w - a * q)) (mem_univ (w - a * q - D + a))
      (sub_nonneg.mpr h1) h0 (by ring)
    simp only [smul_eq_mul] at hmean
    rw [show (1 - π) * (w - a * q) + π * (w - a * q - D + a) = w - π * D + a * (π - q) by ring]
      at hmean
    have hlt : w - π * D + a * (π - q) < w - D * q := by nlinarith
    have := hi hlt
    have hopt' := hopt D hD.le
    rw [hfull] at hopt'
    change (1 - π) * u (w - a * q) + π * u (w - a * q - D + a) ≥ u (w - D * q) at hopt'
    linarith

/-- Expected utility from investing `α` in the risky asset with return distribution `F`
(MWG, Example 6.C.2, p. 188): `∫ u(w + α(z - 1)) dF(z)`. -/
noncomputable def assetEU (u : ℝ → ℝ) (w : ℝ) (μ : Measure ℝ) (α : ℝ) : ℝ :=
  ∫ z, u (w + α * (z - 1)) ∂μ

/-- Integrability of the asset objective for a continuous Bernoulli utility. -/
theorem assetEU_integrable {u : ℝ → ℝ} (hu : Continuous u) {μ : Measure ℝ}
    (hμ : IsMoneyLottery univ μ) (w α : ℝ) : Integrable (fun z => u (w + α * (z - 1))) μ :=
  hμ.integrable (S := univ) (u := fun z => u (w + α * (z - 1))) (by fun_prop)

/-- **Footnote 17** (MWG, p. 189). For a concave Bernoulli utility the asset objective is
concave in `α`. -/
theorem footnote_6_17 {u : ℝ → ℝ} (hc : ConcaveOn ℝ univ u) {μ : Measure ℝ}
    (hμ : IsMoneyLottery univ μ) (w : ℝ) : ConcaveOn ℝ univ (assetEU u w μ) := by
  have hcont : Continuous u := by
    have := hc.continuousOn_interior
    rw [interior_univ] at this
    exact continuousOn_univ.mp this
  have := hμ.1
  refine ⟨convex_univ, fun a _ b _ s t hs ht hst => ?_⟩
  simp only [assetEU, smul_eq_mul]
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add
    ((assetEU_integrable hcont hμ w a).const_mul s) ((assetEU_integrable hcont hμ w b).const_mul t)]
  apply integral_mono ((assetEU_integrable hcont hμ w a).const_mul s |>.add
    ((assetEU_integrable hcont hμ w b).const_mul t)) (assetEU_integrable hcont hμ w _)
  intro z
  have := hc.2 (mem_univ (w + a * (z - 1))) (mem_univ (w + b * (z - 1))) hs ht hst
  simp only [smul_eq_mul] at this
  convert this using 2
  have : s * (w + a * (z - 1)) + t * (w + b * (z - 1)) = (s + t) * w + (s * a + t * b) * (z - 1)
    := by ring
  rw [this, hst, one_mul]

/-- **Example 6.C.2** (MWG, p. 189). If the risky asset's mean return exceeds the safe return,
`∫ z dF > 1`, a strictly increasing, concave Bernoulli utility differentiable at `w > 0` gains
from investing a small amount: some `α ∈ (0, w]` gives strictly higher expected utility than
`α = 0`. Hence every optimal portfolio has `α* > 0`. -/
theorem example_6_C_2 {u : ℝ → ℝ} (hc : ConcaveOn ℝ univ u) (hi : StrictMono u)
    {w : ℝ} (hw : 0 < w) (hdw : DifferentiableAt ℝ u w) {μ : Measure ℝ}
    (hμ : IsMoneyLottery univ μ) (hmean : 1 < ∫ z, z ∂μ) :
    ∃ α ∈ Ioc 0 w, assetEU u w μ 0 < assetEU u w μ α := by
  have := hμ.1
  have hcont : Continuous u := by
    have := hc.continuousOn_interior
    rw [interior_univ] at this
    exact continuousOn_univ.mp this
  obtain ⟨a, b, -, hae⟩ := hμ.ae_mem
  set d := deriv u w
  have hd : 0 < d := Kreps.UtilityForMoney.deriv_pos_of_concave_strictMono hc hi hdw
  set m := ∫ z, z ∂μ - 1
  have hm : 0 < m := by simp only [m]; linarith
  set K := |a - 1| + |b - 1| + 1
  have hK : 0 < K := by positivity
  set ε := d * m / (2 * K)
  have hε : 0 < ε := by positivity
  have hlo := hdw.hasDerivAt.isLittleO.bound hε
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hlo
  set α := min w (δ / (2 * K))
  have hα : 0 < α := lt_min hw (by positivity)
  refine ⟨α, ⟨hα, min_le_left _ _⟩, ?_⟩
  have hbnd : ∀ z ∈ Icc a b, |z - 1| ≤ K := by
    intro z hz
    rcases le_total 1 z with h | h
    · rw [abs_of_nonneg (by linarith)]
      have : z - 1 ≤ |b - 1| := (by linarith [hz.2] : z - 1 ≤ b - 1).trans (le_abs_self _)
      linarith [abs_nonneg (a - 1)]
    · rw [abs_of_nonpos (by linarith)]
      have : 1 - z ≤ |a - 1| := (by linarith [hz.1] : 1 - z ≤ 1 - a).trans
        (by rw [abs_sub_comm]; exact le_abs_self _)
      linarith [abs_nonneg (b - 1)]
  have hpt : ∀ z ∈ Icc a b, u w + d * (α * (z - 1)) - ε * (α * K) ≤ u (w + α * (z - 1)) := by
    intro z hz
    have hz1 := hbnd z hz
    have hsmall : dist (w + α * (z - 1)) w < δ := by
      rw [Real.dist_eq, show w + α * (z - 1) - w = α * (z - 1) by ring, abs_mul,
        abs_of_pos hα]
      calc α * |z - 1| ≤ α * K := mul_le_mul_of_nonneg_left hz1 hα.le
        _ ≤ δ / (2 * K) * K := mul_le_mul_of_nonneg_right (min_le_right _ _) hK.le
        _ < δ := by field_simp; linarith
    have hb := hball hsmall
    rw [Real.norm_eq_abs, Real.norm_eq_abs, show w + α * (z - 1) - w = α * (z - 1) by ring,
      smul_eq_mul] at hb
    have h2 : |α * (z - 1)| ≤ α * K := by
      rw [abs_mul, abs_of_pos hα]; exact mul_le_mul_of_nonneg_left hz1 hα.le
    have h3 := neg_abs_le (u (w + α * (z - 1)) - u w - α * (z - 1) * d)
    nlinarith [mul_le_mul_of_nonneg_left h2 hε.le]
  have hint : ∫ z, (u w + d * (α * (z - 1)) - ε * (α * K)) ∂μ ≤
      ∫ z, u (w + α * (z - 1)) ∂μ := integral_mono_ae (μ := μ)
    (((integrable_const (u w)).add ((hμ.integrable_id.sub (integrable_const 1)).const_mul α
      |>.const_mul d)).sub (integrable_const (ε * (α * K))))
    (assetEU_integrable hcont hμ w α) (hae.mono fun z hz => hpt z hz)
  have hcalc : ∫ z, (u w + d * (α * (z - 1)) - ε * (α * K)) ∂μ =
      u w + d * α * m - ε * (α * K) := by
    rw [integral_sub, integral_add, integral_const_mul, integral_const_mul, integral_sub]
    · simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, m]; ring
    all_goals first
      | exact integrable_const _
      | exact hμ.integrable_id
      | exact (hμ.integrable_id.sub (integrable_const 1)).const_mul α
      | exact ((hμ.integrable_id.sub (integrable_const 1)).const_mul α).const_mul d
      | exact (integrable_const _).add (((hμ.integrable_id.sub (integrable_const 1)).const_mul
          α).const_mul d)
  rw [hcalc] at hint
  have h0 : assetEU u w μ 0 = u w := by simp [assetEU]
  rw [h0]
  have hεK : ε * K = d * m / 2 := by simp only [ε]; field_simp
  have : u w < u w + d * α * m - ε * (α * K) := by
    have : ε * (α * K) = α * (d * m / 2) := by rw [← hεK]; ring
    rw [this]; nlinarith [mul_pos hd hm]
  exact this.trans_le hint

/-- The utility of a portfolio `α ∈ ℝ^N_+` of risky assets with jointly distributed returns
(MWG, Example 6.C.3, p. 189, and Exercise 6.C.4, p. 210): `U(α) = ∫ u(α₁z₁ + ⋯ + α_N z_N) dF`. -/
noncomputable def portfolioU {N : ℕ} (u : ℝ → ℝ) (μ : Measure (Fin N → ℝ)) (α : Fin N → ℝ) :
    ℝ :=
  ∫ z, u (∑ n, α n * z n) ∂μ

variable {N : ℕ} {u : ℝ → ℝ} {μ : Measure (Fin N → ℝ)} {K : Set (Fin N → ℝ)}

/-- The portfolio payoff is nonnegative for nonnegative holdings and returns. -/
theorem portfolio_payoff_nonneg {α z : Fin N → ℝ} (hα : 0 ≤ α) (hz : 0 ≤ z) :
    0 ≤ ∑ n, α n * z n :=
  Finset.sum_nonneg fun n _ => mul_nonneg (hα n) (hz n)

/-- The portfolio integrand is integrable when returns are supported in a compact set of
nonnegative vectors. -/
theorem portfolio_integrable [IsProbabilityMeasure μ] (hu : ContinuousOn u (Ici 0))
    (hK : IsCompact K) (hKn : ∀ z ∈ K, 0 ≤ z) (hμK : μ Kᶜ = 0) {α : Fin N → ℝ} (hα : 0 ≤ α) :
    Integrable (fun z => u (∑ n, α n * z n)) μ := by
  have hr : μ.restrict K = μ := Measure.restrict_eq_self_of_ae_mem
    (measure_eq_zero_iff_ae_notMem.mp hμK |>.mono fun x hx => by simpa using hx)
  have hc : ContinuousOn (fun z : Fin N → ℝ => u (∑ n, α n * z n)) K :=
    hu.comp (by fun_prop) fun z hz => portfolio_payoff_nonneg hα (hKn z hz)
  have := hc.integrableOn_compact (μ := μ) hK
  rwa [IntegrableOn, hr] at this

/-- **Exercise 6.C.4(a)** (MWG, p. 210). For a nondecreasing `u`, the portfolio utility is
nondecreasing in the holdings. -/
theorem exercise_6_C_4a [IsProbabilityMeasure μ] (hu : ContinuousOn u (Ici 0))
    (hm : MonotoneOn u (Ici 0)) (hK : IsCompact K) (hKn : ∀ z ∈ K, 0 ≤ z) (hμK : μ Kᶜ = 0)
    {α β : Fin N → ℝ} (hα : 0 ≤ α) (hαβ : α ≤ β) : portfolioU u μ α ≤ portfolioU u μ β := by
  have hβ : 0 ≤ β := hα.trans hαβ
  apply integral_mono_ae (portfolio_integrable hu hK hKn hμK hα)
    (portfolio_integrable hu hK hKn hμK hβ)
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hμK] with z hz
  have hz' : 0 ≤ z := hKn z (by simpa using hz)
  exact hm (portfolio_payoff_nonneg hα hz') (portfolio_payoff_nonneg hβ hz')
    (Finset.sum_le_sum fun n _ => mul_le_mul_of_nonneg_right (hαβ n) (hz' n))

/-- **Exercise 6.C.4(b)** (MWG, p. 210). For a concave `u`, the portfolio utility is concave on
`ℝ^N_+`. -/
theorem exercise_6_C_4b [IsProbabilityMeasure μ] (hu : ContinuousOn u (Ici 0))
    (hc : ConcaveOn ℝ (Ici 0) u) (hK : IsCompact K) (hKn : ∀ z ∈ K, 0 ≤ z) (hμK : μ Kᶜ = 0) :
    ConcaveOn ℝ (Ici 0) (portfolioU u μ) := by
  refine ⟨convex_Ici 0, fun α hα β hβ s t hs ht hst => ?_⟩
  have hα' : 0 ≤ α := hα
  have hβ' : 0 ≤ β := hβ
  have hIα := portfolio_integrable hu hK hKn hμK hα'
  have hIβ := portfolio_integrable hu hK hKn hμK hβ'
  have hγ : 0 ≤ s • α + t • β := add_nonneg (smul_nonneg hs hα') (smul_nonneg ht hβ')
  simp only [portfolioU, smul_eq_mul]
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hIα.const_mul s)
    (hIβ.const_mul t)]
  apply integral_mono_ae ((hIα.const_mul s).add (hIβ.const_mul t))
    (portfolio_integrable hu hK hKn hμK hγ)
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hμK] with z hz
  have hz' : 0 ≤ z := hKn z (by simpa using hz)
  have := hc.2 (show ∑ n, α n * z n ∈ Ici (0 : ℝ) from portfolio_payoff_nonneg hα' hz')
    (show ∑ n, β n * z n ∈ Ici (0 : ℝ) from portfolio_payoff_nonneg hβ' hz') hs ht hst
  simp only [smul_eq_mul] at this
  convert this using 2
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
    Finset.mul_sum, mul_assoc]

/-- **Exercise 6.C.4(c)** (MWG, p. 210). For a continuous `u`, the portfolio utility is
continuous on `ℝ^N_+`. -/
theorem exercise_6_C_4c [IsProbabilityMeasure μ] (hu : ContinuousOn u (Ici 0))
    (hK : IsCompact K) (hKn : ∀ z ∈ K, 0 ≤ z) (hμK : μ Kᶜ = 0) :
    ContinuousOn (portfolioU u μ) (Ici 0) := by
  intro α0 hα0
  obtain ⟨C, hC⟩ := hK.isBounded.exists_norm_le
  set A := ‖α0‖ + 1
  set R := N * A * |C|
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := R)).exists_bound_of_continuousOn
    (hu.mono Icc_subset_Ici_self)
  set s' : Set (Fin N → ℝ) := Ici 0 ∩ Metric.closedBall α0 1
  have hs' : s' ∈ 𝓝[Ici 0] α0 := inter_mem_nhdsWithin _ (Metric.closedBall_mem_nhds α0 one_pos)
  have hae : ∀ᵐ z ∂μ, z ∈ K := measure_eq_zero_iff_ae_notMem.mp hμK |>.mono fun x hx => by
    simpa using hx
  have hcont : ContinuousOn (portfolioU u μ) s' := by
    apply continuousOn_of_dominated (bound := fun _ => M)
    · intro α hα
      exact (portfolio_integrable hu hK hKn hμK hα.1).aestronglyMeasurable
    · intro α hα
      filter_upwards [hae] with z hz
      apply hM
      refine ⟨portfolio_payoff_nonneg hα.1 (hKn z hz), ?_⟩
      have hαn : ‖α‖ ≤ A := by
        have := Metric.mem_closedBall.mp hα.2
        calc ‖α‖ ≤ ‖α - α0‖ + ‖α0‖ := norm_le_norm_sub_add α α0
          _ ≤ 1 + ‖α0‖ := by rw [← dist_eq_norm]; linarith
          _ = A := by ring
      calc ∑ n, α n * z n ≤ ∑ _n : Fin N, A * |C| := by
            apply Finset.sum_le_sum
            intro n _
            calc α n * z n ≤ |α n * z n| := le_abs_self _
              _ = |α n| * |z n| := abs_mul _ _
              _ ≤ A * |C| := by
                apply mul_le_mul _ _ (abs_nonneg _) (by positivity)
                · exact (norm_le_pi_norm α n).trans hαn
                · exact ((norm_le_pi_norm z n).trans (hC z hz)).trans (le_abs_self C)
        _ = R := by simp [R]; ring
    · exact integrable_const M
    · filter_upwards [hae] with z hz
      exact hu.comp (by fun_prop) fun α hα => portfolio_payoff_nonneg hα.1 (hKn z hz)
  exact (hcont α0 ⟨hα0, Metric.mem_closedBall_self zero_le_one⟩).mono_of_mem_nhdsWithin hs'

end MWG.ChoiceUnderUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The Arrow-Pratt coefficient of absolute risk aversion

MWG, Section 6.C, pp. 190-191: Definition 6.C.3, invariance under positive linear
transformations, the probability-premium characterization `r_A(x) = 4π'(0)`, recovery of `u`
from `r_A` up to two constants, and Example 6.C.4 (constant absolute risk aversion).

`arrowPratt u x = -u''(x)/u'(x)` is Kreps's `AbsoluteRiskAversion`. MWG obtains
`r_A(x) = 4π'(0)` by differentiating (6.C.4) twice under the assumption that `π` is
differentiable; we prove the limit form `π(x, ε, u)/ε → r_A(x)/4` as `ε ↓ 0` for every `u`
twice continuously differentiable at `x` with `u'(x) > 0`, without assuming anything about
`π` (and `π(x, 0, u) = 0`, so this is the right derivative of `π` at `0`).
-/

namespace MWG.ChoiceUnderUncertainty

open Filter Topology Set

/-- **Definition 6.C.3** (MWG, p. 190). The Arrow-Pratt coefficient of absolute risk aversion
`r_A(x, u) = -u''(x)/u'(x)`. -/
noncomputable def arrowPratt (u : ℝ → ℝ) (x : ℝ) : ℝ := -(deriv (deriv u) x) / deriv u x

/-- MWG's coefficient is Kreps's `AbsoluteRiskAversion`. -/
theorem arrowPratt_eq_kreps (u : ℝ → ℝ) (x : ℝ) :
    arrowPratt u x = Kreps.UtilityForMoney.AbsoluteRiskAversion u x := rfl

/-- **p. 190**. The Arrow-Pratt coefficient is invariant under positive (indeed nonzero) linear
transformations `βu + γ` of the Bernoulli utility. -/
theorem arrowPratt_affine_invariant (u : ℝ → ℝ) {β : ℝ} (hβ : β ≠ 0) (γ x : ℝ) :
    arrowPratt (fun y => β * u y + γ) x = arrowPratt u x := by
  have h1 : deriv (fun y => β * u y + γ) = fun y => β * deriv u y := by
    funext y
    rw [deriv_add_const, deriv_const_mul_field]
  have h2 : deriv (fun y => β * deriv u y) x = β * deriv (deriv u) x := deriv_const_mul_field _
  unfold arrowPratt
  rw [h1, h2]
  by_cases hd : deriv u x = 0
  · simp [hd]
  · field_simp

/-- **p. 190**. The second derivative alone is not invariant: `(2u)'' = 2u''`. -/
theorem second_derivative_not_invariant (u : ℝ → ℝ) (x : ℝ) :
    deriv (deriv (fun y => 2 * u y)) x = 2 * deriv (deriv u) x := by
  have h1 : deriv (fun y => 2 * u y) = fun y => 2 * deriv u y := by
    funext y; exact deriv_const_mul_field _
  rw [h1]
  exact deriv_const_mul_field _

/-- **p. 190**. `r_A(x, u) = 4π'(0)`: the probability premium of a small symmetric risk divided
by its size tends to `r_A(x, u)/4`. -/
theorem arrowPratt_eq_four_probPremium_slope {u : ℝ → ℝ} {x : ℝ} (hu : ContDiffAt ℝ 2 u x)
    (hp : 0 < deriv u x) :
    Tendsto (fun ε => probPremium u x ε / ε) (𝓝[>] 0) (𝓝 (arrowPratt u x / 4)) := by
  have hq := (Kreps.UtilityForMoney.symmetricUtility_quotient hu).mono_left
    (nhdsGT_le_nhdsNE (0 : ℝ))
  have hd : HasDerivAt u (deriv u x) x :=
    (hu.differentiableAt (by norm_num)).hasDerivAt
  -- the symmetric difference quotient `(u(x+ε) - u(x-ε)) / ε → 2u'(x)`
  have hsym : Tendsto (fun ε : ℝ => (u (x + ε) - u (x - ε)) / ε) (𝓝[>] 0)
      (𝓝 (2 * deriv u x)) := by
    have h1 := hd.tendsto_slope_zero_right
    have h2 := hd.tendsto_slope_zero_left
    have h2' : Tendsto (fun ε : ℝ => ε⁻¹ * (u x - u (x - ε))) (𝓝[>] 0) (𝓝 (deriv u x)) := by
      have hneg : Tendsto (fun ε : ℝ => -ε) (𝓝[>] 0) (𝓝[<] 0) := by
        have := (continuous_neg.tendsto' (0 : ℝ) 0 neg_zero)
        exact tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
          (this.mono_left nhdsWithin_le_nhds)
          (eventually_nhdsWithin_of_forall fun ε (hε : 0 < ε) => by simpa using hε)
      have := h2.comp hneg
      refine this.congr' (Eventually.of_forall fun ε => ?_)
      simp only [Function.comp_apply, smul_eq_mul, inv_neg, ← sub_eq_add_neg]
      ring
    have := (h1.add h2')
    simp only [smul_eq_mul] at this
    refine (this.congr' ?_).trans (by rw [two_mul])
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε' : ε ≠ 0 := (ne_of_gt hε)
    field_simp
    ring
  have hlim := (hq.neg).div hsym (by positivity)
  have hfin : arrowPratt u x / 4 = -(deriv (deriv u) x / 2) / (2 * deriv u x) := by
    unfold arrowPratt; field_simp; ring
  rw [hfin]
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε' : ε ≠ 0 := ne_of_gt hε
  simp only [Pi.div_apply]
  unfold probPremium Kreps.UtilityForMoney.SymmetricUtility
  by_cases hden : u (x + ε) - u (x - ε) = 0
  · simp [hden]
  · field_simp
    ring

/-- **p. 191**. The Bernoulli utility is recovered from `r_A` up to two integration constants:
two utilities with positive marginal utility and the same Arrow-Pratt coefficient on an open
interval differ by a positive linear transformation there. -/
theorem utility_determined_by_arrowPratt {S : Set ℝ} (hS : Convex ℝ S)
    {u v : ℝ → ℝ} (hu1 : ∀ x ∈ S, DifferentiableAt ℝ u x) (hv1 : ∀ x ∈ S, DifferentiableAt ℝ v x)
    (hu2 : ∀ x ∈ S, DifferentiableAt ℝ (deriv u) x) (hv2 : ∀ x ∈ S, DifferentiableAt ℝ (deriv v) x)
    (hup : ∀ x ∈ S, 0 < deriv u x) (hvp : ∀ x ∈ S, 0 < deriv v x)
    (h : ∀ x ∈ S, arrowPratt u x = arrowPratt v x) {x₀ : ℝ} (hx₀ : x₀ ∈ S) :
    ∃ β > 0, ∃ γ : ℝ, ∀ x ∈ S, v x = β * u x + γ := by
  -- the ratio of marginal utilities is constant
  have hratio (x : ℝ) (hx : x ∈ S) : HasDerivAt (fun y => deriv v y / deriv u y) 0 x := by
    have hd := (hv2 x hx).hasDerivAt.div (hu2 x hx).hasDerivAt (hup x hx).ne'
    convert hd using 1
    have hh := h x hx
    unfold arrowPratt at hh
    rw [div_eq_div_iff (hup x hx).ne' (hvp x hx).ne'] at hh
    have : deriv (deriv v) x * deriv u x - deriv v x * deriv (deriv u) x = 0 := by linarith
    rw [this, zero_div]
  set β := deriv v x₀ / deriv u x₀
  have hβ : 0 < β := div_pos (hvp x₀ hx₀) (hup x₀ hx₀)
  have hconst (x : ℝ) (hx : x ∈ S) : deriv v x = β * deriv u x := by
    have := Kreps.UtilityForMoney.eq_on_interval_of_deriv_zero hS hratio hx hx₀
    change deriv v x = deriv v x₀ / deriv u x₀ * deriv u x
    rw [← this]
    field_simp [(hup x hx).ne']
  have hdiff (x : ℝ) (hx : x ∈ S) : HasDerivAt (fun y => v y - β * u y) 0 x := by
    convert (hv1 x hx).hasDerivAt.sub ((hu1 x hx).hasDerivAt.const_mul β) using 1
    rw [hconst x hx]; ring
  refine ⟨β, hβ, v x₀ - β * u x₀, fun x hx => ?_⟩
  have := Kreps.UtilityForMoney.eq_on_interval_of_deriv_zero hS hdiff hx hx₀
  linarith

/-- **Example 6.C.4** (MWG, p. 191). For `u(x) = -e^{-ax}`, `r_A(x, u) = a` at every `x`. -/
theorem example_6_C_4 {a : ℝ} (ha : a ≠ 0) (x : ℝ) :
    arrowPratt (fun y => -Real.exp (-a * y)) x = a :=
  Kreps.UtilityForMoney.absoluteRiskAversion_exponential ha x

/-- **Example 6.C.4** (MWG, p. 191). A Bernoulli utility with constant `r_A = a > 0` on an open
interval has the form `u(x) = -αe^{-ax} + β` with `α > 0`. -/
theorem example_6_C_4_general {S : Set ℝ} (hS : Convex ℝ S) (hne : S.Nonempty) {u : ℝ → ℝ}
    (h₁ : ∀ x ∈ S, DifferentiableAt ℝ u x) (h₂ : ∀ x ∈ S, DifferentiableAt ℝ (deriv u) x)
    (hp : ∀ x ∈ S, 0 < deriv u x) {a : ℝ} (ha : 0 < a) (hc : ∀ x ∈ S, arrowPratt u x = a) :
    ∃ α > 0, ∃ β : ℝ, ∀ x ∈ S, u x = -α * Real.exp (-a * x) + β := by
  obtain ⟨A, B, hB, h⟩ := Kreps.UtilityForMoney.proposition_6_12_exponential hS hne h₁ h₂ hp ha hc
  refine ⟨B, hB, A, fun x hx => ?_⟩
  rw [h x hx, Kreps.UtilityForMoney.ExponentialUtility]
  ring

end MWG.ChoiceUnderUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Comparisons of risk aversion across individuals

MWG, Section 6.C, pp. 191-192: the five definitions (i)-(v) of "`u₂` is more risk averse than
`u₁`", Proposition 6.C.2 (their equivalence) with the differentiable proof of (i) ⇔ (ii), and
Exercises 6.C.6 and 6.C.7.

Conditions (iii) and (v) range over all money lotteries (compactly supported distributions,
see `MoneyLotteries`). The utilities are twice continuously differentiable with positive
marginal utility on an open interval `S`. The equivalence (i) ⇔ (ii) is Kreps's
Proposition 6.8 (Arrow-Pratt comparison iff the finite-lottery comparison) combined with
Kreps's Proposition 6.7 (the finite-lottery comparison iff concavity of `u₂ ∘ u₁⁻¹`); (ii) ⇒
(iii) is Jensen's inequality for `ψ` on arbitrary distributions; (iv) ⇒ (i) uses
`r_A = 4 lim π(ε)/ε`.
-/

namespace MWG.ChoiceUnderUncertainty

open MeasureTheory Filter Topology Set
open scoped ENNReal

/-- A finite-support lottery over amounts in `S` (Kreps's `SimpleLottery S`) as a measure. -/
noncomputable def simpleMeasure {S : Set ℝ} (p : Kreps.UtilityForMoney.SimpleLottery S) :
    Measure ℝ :=
  ∑ x ∈ p.weights.support, ENNReal.ofReal (p.weights x) • Measure.dirac (x : ℝ)

/-- Expectations under `simpleMeasure p` are Kreps's expected utilities. -/
theorem integral_simpleMeasure {S : Set ℝ} (p : Kreps.UtilityForMoney.SimpleLottery S)
    (f : ℝ → ℝ) :
    ∫ z, f z ∂(simpleMeasure p) =
      Kreps.UtilityForMoney.ExpectedUtility (fun y : S => f y) p := by
  unfold simpleMeasure Kreps.UtilityForMoney.ExpectedUtility
  rw [integral_finsetSum_measure]
  · rw [Finsupp.sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (p.weights_nonneg x),
      smul_eq_mul]
  · intro x _
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

/-- A finite-support lottery over a convex `S` is a money lottery on `S`. -/
theorem simpleMeasure_isMoneyLottery {S : Set ℝ} (hS : Convex ℝ S)
    (p : Kreps.UtilityForMoney.SimpleLottery S) : IsMoneyLottery S (simpleMeasure p) := by
  classical
  have hne := p.support_weights_nonempty
  set T := p.weights.support.image (fun x : S => (x : ℝ))
  have hT : T.Nonempty := hne.image _
  refine ⟨⟨?_⟩, T.min' hT, T.max' hT, ?_, ?_⟩
  · simp only [simpleMeasure, Measure.coe_finsetSum, Finset.sum_apply, Measure.coe_smul,
      Pi.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => p.weights_nonneg x)]
    have := p.total
    rw [Finsupp.sum] at this
    rw [this, ENNReal.ofReal_one]
  · obtain ⟨a, ha, ha'⟩ := Finset.mem_image.mp (T.min'_mem hT)
    obtain ⟨b, hb, hb'⟩ := Finset.mem_image.mp (T.max'_mem hT)
    rw [← ha', ← hb']
    exact hS.ordConnected.out a.property b.property
  · simp only [simpleMeasure, Measure.coe_finsetSum, Finset.sum_apply, Measure.coe_smul,
      Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_eq_zero
    intro x hx
    rw [Measure.dirac_apply' _ measurableSet_Icc.compl, indicator_of_notMem, mul_zero]
    simp only [mem_compl_iff, not_not]
    have hxT : (x : ℝ) ∈ T := Finset.mem_image_of_mem _ hx
    exact ⟨T.min'_le _ hxT, T.le_max' _ hxT⟩

/-- **Proposition 6.C.2(i)** (MWG, p. 191). `r_A(x, u₂) ≥ r_A(x, u₁)` for every `x`. -/
def MoreRiskAverseI (S : Set ℝ) (u₁ u₂ : ℝ → ℝ) : Prop :=
  ∀ x ∈ S, arrowPratt u₁ x ≤ arrowPratt u₂ x

/-- **Proposition 6.C.2(ii)** (MWG, p. 191). `u₂ = ψ ∘ u₁` for an increasing concave `ψ`. -/
def MoreRiskAverseII (S : Set ℝ) (u₁ u₂ : ℝ → ℝ) : Prop :=
  ∃ ψ : ℝ → ℝ, StrictMonoOn ψ (u₁ '' S) ∧ ConcaveOn ℝ (u₁ '' S) ψ ∧ ∀ x ∈ S, u₂ x = ψ (u₁ x)

/-- **Proposition 6.C.2(iii)** (MWG, p. 191). `c(F, u₂) ≤ c(F, u₁)` for every `F`. -/
def MoreRiskAverseIII (S : Set ℝ) (u₁ u₂ : ℝ → ℝ) : Prop :=
  ∀ μ c₁ c₂, IsMoneyLottery S μ → IsCertaintyEquivalent S u₁ μ c₁ →
    IsCertaintyEquivalent S u₂ μ c₂ → c₂ ≤ c₁

/-- **Proposition 6.C.2(iv)** (MWG, p. 191). `π(x, ε, u₂) ≥ π(x, ε, u₁)` for all `x` and
`ε > 0`. -/
def MoreRiskAverseIV (S : Set ℝ) (u₁ u₂ : ℝ → ℝ) : Prop :=
  ∀ x ε, 0 < ε → x - ε ∈ S → x + ε ∈ S → probPremium u₁ x ε ≤ probPremium u₂ x ε

/-- **Proposition 6.C.2(v)** (MWG, p. 191). If `u₂` finds `F` at least as good as the riskless
`x̄`, so does `u₁`. -/
def MoreRiskAverseV (S : Set ℝ) (u₁ u₂ : ℝ → ℝ) : Prop :=
  ∀ μ x, IsMoneyLottery S μ → x ∈ S → u₂ x ≤ ∫ z, u₂ z ∂μ → u₁ x ≤ ∫ z, u₁ z ∂μ

/-- Condition (v) restricted to finite-support lotteries is Kreps's `MoreRiskAverse`. -/
theorem kreps_of_moreRiskAverseV {S : Set ℝ} (hS : Convex ℝ S) {u₁ u₂ : ℝ → ℝ}
    (h : MoreRiskAverseV S u₁ u₂) : Kreps.UtilityForMoney.MoreRiskAverse S u₂ u₁ := by
  intro p x hx
  have := h (simpleMeasure p) x (simpleMeasure_isMoneyLottery hS p) x.property
  simp only [integral_simpleMeasure] at this
  exact this hx

/-- Kreps's finite-lottery comparison gives the concave transformation (ii). -/
theorem moreRiskAverseII_of_kreps {S : Set ℝ} (hS : Convex ℝ S) {u₁ u₂ : ℝ → ℝ}
    (h1 : StrictMonoOn u₁ S) (h2 : StrictMonoOn u₂ S) (c1 : ContinuousOn u₁ S)
    (c2 : ContinuousOn u₂ S) (h : Kreps.UtilityForMoney.MoreRiskAverse S u₂ u₁) :
    MoreRiskAverseII S u₁ u₂ :=
  ⟨Kreps.UtilityForMoney.UtilityTransform S u₂ u₁,
    Kreps.UtilityForMoney.utilityTransform_strictMonoOn h1 h2,
    (Kreps.UtilityForMoney.proposition_6_7 hS h2 h1 c2 c1).mp h,
    fun _ hx => (Kreps.UtilityForMoney.utilityTransform_apply u₂ h1 hx).symm⟩

/-- A concave transformation (ii) gives Kreps's finite-lottery comparison. -/
theorem kreps_of_moreRiskAverseII {S : Set ℝ} (hS : Convex ℝ S) {u₁ u₂ : ℝ → ℝ}
    (h1 : StrictMonoOn u₁ S) (h2 : StrictMonoOn u₂ S) (c1 : ContinuousOn u₁ S)
    (c2 : ContinuousOn u₂ S) (h : MoreRiskAverseII S u₁ u₂) :
    Kreps.UtilityForMoney.MoreRiskAverse S u₂ u₁ := by
  obtain ⟨ψ, -, hψ, he⟩ := h
  apply (Kreps.UtilityForMoney.proposition_6_7 hS h2 h1 c2 c1).mpr
  refine ⟨hψ.1, fun a ha b hb s t hs ht hst => ?_⟩
  have heq : ∀ y ∈ u₁ '' S, Kreps.UtilityForMoney.UtilityTransform S u₂ u₁ y = ψ y := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Kreps.UtilityForMoney.utilityTransform_apply u₂ h1 hx, he x hx]
  rw [heq a ha, heq b hb, heq _ (hψ.1 ha hb hs ht hst)]
  exact hψ.2 ha hb hs ht hst

/-- An open interval image: for `[a, b] ⊆ S` with `S` open, the values `u([a, b])` lie in the
interior of a closed interval contained in `u(S)`. -/
theorem exists_Icc_image_nhds {S : Set ℝ} (hS : Convex ℝ S) (ho : IsOpen S) {u : ℝ → ℝ}
    (hc : ContinuousOn u S) (hi : StrictMonoOn u S) {a b : ℝ} (hab : Icc a b ⊆ S)
    (hle : a ≤ b) : ∃ a' b', a' < a ∧ b < b' ∧ Icc a' b' ⊆ S ∧
      Icc (u a') (u b') ⊆ u '' S ∧ u a' < u a ∧ u b < u b' := by
  have ha : a ∈ S := hab ⟨le_rfl, hle⟩
  have hb : b ∈ S := hab ⟨hle, le_rfl⟩
  obtain ⟨ε, hε, hεa⟩ := Metric.isOpen_iff.mp ho a ha
  obtain ⟨δ, hδ, hδb⟩ := Metric.isOpen_iff.mp ho b hb
  have ha' : a - ε / 2 ∈ S := by
    apply hεa
    rw [Metric.mem_ball, Real.dist_eq, show a - ε / 2 - a = -(ε / 2) by ring, abs_neg,
      abs_of_pos (by linarith)]
    linarith
  have hb' : b + δ / 2 ∈ S := by
    apply hδb
    rw [Metric.mem_ball, Real.dist_eq, show b + δ / 2 - b = δ / 2 by ring,
      abs_of_pos (by linarith)]
    linarith
  have hsub : Icc (a - ε / 2) (b + δ / 2) ⊆ S := hS.ordConnected.out ha' hb'
  refine ⟨a - ε / 2, b + δ / 2, by linarith, by linarith, hsub, ?_, hi ha' ha (by linarith),
    hi hb hb' (by linarith)⟩
  intro y hy
  obtain ⟨c, hc', hce⟩ := intermediate_value_Icc (by linarith) (hc.mono hsub) hy
  exact ⟨c, hsub hc', hce⟩

/-- **Proposition 6.C.2**, (ii) ⇒ (iii) (MWG, p. 191; Exercise 6.C.6(a), p. 210). By Jensen's
inequality for `ψ`, a concave transformation has smaller certainty equivalents. -/
theorem moreRiskAverse_ii_iii {S : Set ℝ} (hS : Convex ℝ S) (ho : IsOpen S) {u₁ u₂ : ℝ → ℝ}
    (c1 : ContinuousOn u₁ S) (c2 : ContinuousOn u₂ S) (h1 : StrictMonoOn u₁ S)
    (h2 : StrictMonoOn u₂ S) (h : MoreRiskAverseII S u₁ u₂) : MoreRiskAverseIII S u₁ u₂ := by
  obtain ⟨ψ, -, hψ, he⟩ := h
  intro μ k₁ k₂ hμ hk1 hk2
  have := hμ.1
  obtain ⟨a, b, hab, hae⟩ := hμ.ae_mem
  have hle : a ≤ b := by
    have : (ae μ).NeBot := ae_neBot.mpr (NeZero.ne μ)
    obtain ⟨z, hz⟩ := hae.exists
    exact hz.1.trans hz.2
  obtain ⟨a', b', -, -, hsub', himg, hlo, hhi⟩ := exists_Icc_image_nhds hS ho c1 h1 hab hle
  -- `ψ` is continuous on `[u₁ a, u₁ b]`, inside the interior of `[u₁ a', u₁ b']`
  have hψI : ConcaveOn ℝ (Icc (u₁ a') (u₁ b')) ψ := hψ.subset himg (convex_Icc _ _)
  have hψc : ContinuousOn ψ (Icc (u₁ a) (u₁ b)) := by
    have := hψI.continuousOn_interior
    rw [interior_Icc] at this
    exact this.mono fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hsubψ : Icc (u₁ a) (u₁ b) ⊆ Icc (u₁ a') (u₁ b') :=
    fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hval : ∀ᵐ z ∂μ, u₁ z ∈ Icc (u₁ a) (u₁ b) := hae.mono fun z hz =>
    ⟨h1.monotoneOn (hab ⟨le_rfl, hle⟩) (hab hz) hz.1,
      h1.monotoneOn (hab hz) (hab ⟨hle, le_rfl⟩) hz.2⟩
  have hint2 : ∫ z, u₂ z ∂μ = ∫ z, ψ (u₁ z) ∂μ :=
    integral_congr_ae (hae.mono fun z hz => he z (hab hz))
  have hInt : Integrable (fun z => ψ (u₁ z)) μ :=
    (hμ.integrable c2).congr (hae.mono fun z hz => he z (hab hz))
  have hj := (hψI.subset hsubψ (convex_Icc _ _)).le_map_integral hψc isClosed_Icc hval
    (hμ.integrable c1) hInt
  rw [← hint2, ← hk1.2, ← hk2.2, ← he k₁ hk1.1] at hj
  exact (h2.le_iff_le hk2.1 hk1.1).mp hj

/-- **Proposition 6.C.2**, (iii) ⇒ (v) (MWG, p. 191; Exercise 6.C.6(b), p. 210). -/
theorem moreRiskAverse_iii_v {S : Set ℝ} {u₁ u₂ : ℝ → ℝ} (c1 : ContinuousOn u₁ S)
    (c2 : ContinuousOn u₂ S) (h1 : StrictMonoOn u₁ S) (h2 : StrictMonoOn u₂ S)
    (h : MoreRiskAverseIII S u₁ u₂) : MoreRiskAverseV S u₁ u₂ := by
  intro μ x hμ hx hle
  obtain ⟨k₁, hk1⟩ := certaintyEquivalent_exists c1 hμ
  obtain ⟨k₂, hk2⟩ := certaintyEquivalent_exists c2 hμ
  have hk := h μ k₁ k₂ hμ hk1 hk2
  rw [← hk2.2] at hle
  have hxk : x ≤ k₂ := (h2.le_iff_le hx hk2.1).mp hle
  rw [← hk1.2]
  exact h1.monotoneOn hx hk1.1 (hxk.trans hk)

/-- **Proposition 6.C.2**, (v) ⇒ (iii) (MWG, p. 191; Exercise 6.C.6(b), p. 210). -/
theorem moreRiskAverse_v_iii {S : Set ℝ} {u₁ u₂ : ℝ → ℝ} (h1 : StrictMonoOn u₁ S)
    (h : MoreRiskAverseV S u₁ u₂) : MoreRiskAverseIII S u₁ u₂ := by
  intro μ k₁ k₂ hμ hk1 hk2
  have := h μ k₂ hμ hk2.1 hk2.2.le
  rw [← hk1.2] at this
  exact (h1.le_iff_le hk2.1 hk1.1).mp this

/-- **Proposition 6.C.2**, (iii) ⇒ (iv) (MWG, p. 191; Exercise 6.C.7, p. 210). -/
theorem moreRiskAverse_iii_iv {S : Set ℝ} (hS : Convex ℝ S) {u₁ u₂ : ℝ → ℝ}
    (c2 : ContinuousOn u₂ S) (h1 : StrictMonoOn u₁ S) (h2 : StrictMonoOn u₂ S)
    (h : MoreRiskAverseIII S u₁ u₂) : MoreRiskAverseIV S u₁ u₂ := by
  intro x ε hε hm hp
  have hx : x ∈ S := hS.ordConnected.out hm hp ⟨by linarith, by linarith⟩
  have l1 : u₁ (x - ε) < u₁ x := h1 hm hx (by linarith)
  have l2 : u₁ x < u₁ (x + ε) := h1 hx hp (by linarith)
  have m2 : u₂ (x - ε) < u₂ (x + ε) := h2 hm hp (by linarith)
  set π₁ := probPremium u₁ x ε
  have hs1 := (probPremium_spec u₁ x ε (l1.trans l2)).1
  have hs2 := (probPremium_spec u₂ x ε m2).1
  -- `π₁ ∈ (-1/2, 1/2)`, so the premium gamble is a lottery
  have hb1 : -(1 / 2) < π₁ := by
    by_contra hn
    have : (1 / 2 + π₁) * u₁ (x + ε) + (1 / 2 - π₁) * u₁ (x - ε) ≤ u₁ (x - ε) := by nlinarith
    linarith
  have hb2 : π₁ < 1 / 2 := by
    by_contra hn
    have : u₁ (x + ε) ≤ (1 / 2 + π₁) * u₁ (x + ε) + (1 / 2 - π₁) * u₁ (x - ε) := by nlinarith
    linarith
  set p := 1 / 2 + π₁
  have hp0 : 0 ≤ p := by simp only [p]; linarith
  have hp1 : p ≤ 1 := by simp only [p]; linarith
  have hG := binLot_isMoneyLottery hS hp hm p hp0 hp1
  have hce1 : IsCertaintyEquivalent S u₁ (binLot p (x + ε) (x - ε)) x := by
    refine ⟨hx, ?_⟩
    rw [integral_binLot _ _ _ _ hp0 hp1, hs1]
    simp only [p]; ring
  obtain ⟨k₂, hk2⟩ := certaintyEquivalent_exists c2 hG
  have hk := h _ x k₂ hG hce1 hk2
  have hu2 : ∫ z, u₂ z ∂(binLot p (x + ε) (x - ε)) ≤ u₂ x := by
    rw [← hk2.2]; exact h2.monotoneOn hk2.1 hx hk
  rw [integral_binLot _ _ _ _ hp0 hp1] at hu2
  rw [hs2] at hu2
  simp only [p] at hu2
  nlinarith

/-- **Proposition 6.C.2**, (iv) ⇒ (i) (MWG, p. 191; Exercise 6.C.7, p. 210), via
`r_A(x) = 4 lim_{ε ↓ 0} π(x, ε)/ε`. -/
theorem moreRiskAverse_iv_i {S : Set ℝ} (ho : IsOpen S) {u₁ u₂ : ℝ → ℝ}
    (d1 : ∀ x ∈ S, ContDiffAt ℝ 2 u₁ x) (d2 : ∀ x ∈ S, ContDiffAt ℝ 2 u₂ x)
    (p1 : ∀ x ∈ S, 0 < deriv u₁ x) (p2 : ∀ x ∈ S, 0 < deriv u₂ x)
    (h : MoreRiskAverseIV S u₁ u₂) : MoreRiskAverseI S u₁ u₂ := by
  intro x hx
  have t1 := arrowPratt_eq_four_probPremium_slope (d1 x hx) (p1 x hx)
  have t2 := arrowPratt_eq_four_probPremium_slope (d2 x hx) (p2 x hx)
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp ho x hx
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), probPremium u₁ x ε / ε ≤ probPremium u₂ x ε / ε := by
    filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT hδ] with ε hε hεδ
    have hε0 : (0 : ℝ) < ε := hε
    apply div_le_div_of_nonneg_right _ hε0.le
    apply h x ε hε0
    · apply hball; rw [Metric.mem_ball, Real.dist_eq]
      rw [show x - ε - x = -ε by ring, abs_neg, abs_of_pos hε0]; exact hεδ.2
    · apply hball; rw [Metric.mem_ball, Real.dist_eq]
      rw [show x + ε - x = ε by ring, abs_of_pos hε0]; exact hεδ.2
  have := le_of_tendsto_of_tendsto t1 t2 hev
  linarith

/-- **Proposition 6.C.2** (MWG, p. 191). For utilities twice continuously differentiable with
positive marginal utility on an open interval, the five definitions of "`u₂` is more risk
averse than `u₁`" are equivalent. -/
theorem proposition_6_C_2 {S : Set ℝ} (hS : Convex ℝ S) (ho : IsOpen S) (hne : S.Nonempty)
    {u₁ u₂ : ℝ → ℝ} (d1 : ∀ x ∈ S, ContDiffAt ℝ 2 u₁ x) (d2 : ∀ x ∈ S, ContDiffAt ℝ 2 u₂ x)
    (p1 : ∀ x ∈ S, 0 < deriv u₁ x) (p2 : ∀ x ∈ S, 0 < deriv u₂ x) :
    List.TFAE [MoreRiskAverseI S u₁ u₂, MoreRiskAverseII S u₁ u₂, MoreRiskAverseIII S u₁ u₂,
      MoreRiskAverseIV S u₁ u₂, MoreRiskAverseV S u₁ u₂] := by
  have c1 : ContinuousOn u₁ S := fun x hx => (d1 x hx).continuousAt.continuousWithinAt
  have c2 : ContinuousOn u₂ S := fun x hx => (d2 x hx).continuousAt.continuousWithinAt
  have hint : interior S = S := ho.interior_eq
  have h1 : StrictMonoOn u₁ S := strictMonoOn_of_deriv_pos hS c1 (by
    rw [hint]; exact p1)
  have h2 : StrictMonoOn u₂ S := strictMonoOn_of_deriv_pos hS c2 (by
    rw [hint]; exact p2)
  have hI : (interior S).Nonempty := by rw [hint]; exact hne
  tfae_have 1 → 2 := fun h => moreRiskAverseII_of_kreps hS h1 h2 c1 c2
    ((Kreps.UtilityForMoney.proposition_6_8 hS hI d2 d1 h1 p2 p1).mpr h)
  tfae_have 2 → 3 := moreRiskAverse_ii_iii hS ho c1 c2 h1 h2
  tfae_have 3 → 5 := moreRiskAverse_iii_v c1 c2 h1 h2
  tfae_have 5 → 3 := moreRiskAverse_v_iii h1
  tfae_have 3 → 4 := moreRiskAverse_iii_iv hS c2 h1 h2
  tfae_have 4 → 1 := moreRiskAverse_iv_i ho d1 d2 p1 p2
  tfae_finish

end MWG.ChoiceUnderUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

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

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

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

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercises 6.C.2, 6.C.5, 6.C.12, 6.C.13, 6.C.14, 6.C.16 and 6.C.18

MWG, pp. 209-212. Quadratic and mean-variance utility (6.C.2), risk aversion over commodity
bundles and the derived Bernoulli utility of wealth (6.C.5, using Kreps's Proposition 6.16(c)),
constant relative risk aversion (6.C.12), the risk-neutral firm facing price uncertainty
(6.C.13), "strongly more risk averse" (6.C.14), buying and selling prices of a lottery
(6.C.16) and the square-root utility calculations (6.C.18).

Corrections: in 6.C.12(a) the printed form `βx^{1-ρ} + γ` with `β > 0` is decreasing for
`ρ > 1`; the strictly increasing CRRA utilities are `βx^{1-ρ}/(1-ρ) + γ`, `β > 0`. In
6.C.12(c) the printed limit `x^{1-ρ}/(1-ρ) → ln x` fails (at `x = 1` the expression is
`1/(1-ρ)`); the correct limit is `(x^{1-ρ} - 1)/(1-ρ) → ln x`.
-/

namespace MWG.ChoiceUnderUncertainty

open MeasureTheory Filter Topology Set

/-- **Exercise 6.C.2(a)** (MWG, p. 209). With `u(x) = βx² + γx`, expected utility is
`β(σ² + m²) + γm`, a function of the mean `m` and variance `σ²` alone. -/
theorem exercise_6_C_2a (β γ : ℝ) {μ : Measure ℝ} (hμ : IsMoneyLottery univ μ) :
    ∫ x, (β * x ^ 2 + γ * x) ∂μ =
      β * ((∫ x, x ^ 2 ∂μ - (∫ x, x ∂μ) ^ 2) + (∫ x, x ∂μ) ^ 2) + γ * ∫ x, x ∂μ := by
  have h2 : Integrable (fun x : ℝ => x ^ 2) μ := hμ.integrable (by fun_prop)
  rw [integral_add (h2.const_mul β) (hμ.integrable_id.const_mul γ), integral_const_mul,
    integral_const_mul]
  ring

/-- **Exercise 6.C.2(a)** (MWG, p. 209). Two lotteries with the same mean and variance have the
same quadratic expected utility. -/
theorem exercise_6_C_2a_moments (β γ : ℝ) {μ ν : Measure ℝ} (hμ : IsMoneyLottery univ μ)
    (hν : IsMoneyLottery univ ν) (hm : ∫ x, x ∂μ = ∫ x, x ∂ν)
    (hs : ∫ x, x ^ 2 ∂μ = ∫ x, x ^ 2 ∂ν) :
    ∫ x, (β * x ^ 2 + γ * x) ∂μ = ∫ x, (β * x ^ 2 + γ * x) ∂ν := by
  rw [exercise_6_C_2a β γ hμ, exercise_6_C_2a β γ hν, hm, hs]

/-- **Exercise 6.C.2(a)**, note (MWG, p. 209). For `β < 0` the quadratic is concave, and it is
decreasing for `x > -γ/(2β)`. -/
theorem exercise_6_C_2a_note {β γ : ℝ} (hβ : β < 0) :
    ConcaveOn ℝ univ (fun x : ℝ => β * x ^ 2 + γ * x) ∧
      StrictAntiOn (fun x : ℝ => β * x ^ 2 + γ * x) (Ici (-γ / (2 * β))) := by
  constructor
  · refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    simp only [smul_eq_mul]
    have hb' : b = 1 - a := by linarith
    subst hb'
    nlinarith [mul_nonneg ha hb, sq_nonneg (x - y),
      mul_nonneg (mul_nonneg ha hb) (sq_nonneg (x - y))]
  · intro x hx y hy hxy
    simp only [mem_Ici] at hx hy
    have h1 : -γ / (2 * β) * (2 * β) = -γ := div_mul_cancel₀ _ (by linarith)
    have h2 : 2 * (-γ / (2 * β)) < x + y := by linarith
    have h3 : β * (x + y) < β * (2 * (-γ / (2 * β))) := mul_lt_mul_of_neg_left h2 hβ
    have h4 : β * (x + y) + γ < 0 := by linarith
    have he : (β * y ^ 2 + γ * y) - (β * x ^ 2 + γ * x) = (y - x) * (β * (x + y) + γ) := by
      ring
    change β * y ^ 2 + γ * y < β * x ^ 2 + γ * x
    nlinarith [mul_neg_of_pos_of_neg (sub_pos.mpr hxy) h4]

/-- The mean-variance utility `U(F) = mean - r · variance` of a money lottery. -/
noncomputable def meanVarianceU (r : ℝ) (μ : Measure ℝ) : ℝ :=
  ∫ x, x ∂μ - r * (∫ x, x ^ 2 ∂μ - (∫ x, x ∂μ) ^ 2)

/-- Mean-variance utility of the two-point lottery `0` / `2/r` with probability `p` on `2/r`
is `(2/r)(2p² - p)`. -/
theorem meanVarianceU_binLot {r : ℝ} (hr : 0 < r) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    meanVarianceU r (binLot p (2 / r) 0) = 2 / r * (2 * p ^ 2 - p) := by
  unfold meanVarianceU
  rw [integral_binLot _ _ _ _ hp0 hp1, integral_binLot _ _ _ (fun x => x ^ 2) hp0 hp1]
  field_simp
  ring

/-- **Exercise 6.C.2(b)** (MWG, p. 209). For every `r > 0` the mean-variance utility is not
compatible with any Bernoulli utility: on the lotteries over `x' = 0 < x'' = 2/r`, the lottery
`L` giving `x''` with probability `1/4` is ranked strictly below the lottery `L'` giving `x''`
with probability `0`, and no `u` represents the ranking by expected utility. -/
theorem exercise_6_C_2b {r : ℝ} (hr : 0 < r) :
    meanVarianceU r (binLot (1 / 4) (2 / r) 0) < meanVarianceU r (binLot 0 (2 / r) 0) ∧
    ¬∃ u : ℝ → ℝ, ∀ p q : ℝ, p ∈ Icc (0 : ℝ) 1 → q ∈ Icc (0 : ℝ) 1 →
      (meanVarianceU r (binLot p (2 / r) 0) ≤ meanVarianceU r (binLot q (2 / r) 0) ↔
        ∫ x, u x ∂(binLot p (2 / r) 0) ≤ ∫ x, u x ∂(binLot q (2 / r) 0)) := by
  have hU (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) := meanVarianceU_binLot hr hp.1 hp.2
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h4 : (1 / 4 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have h2 : (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  constructor
  · rw [hU _ h4, hU _ h0]
    have : (0 : ℝ) < 2 / r := by positivity
    nlinarith
  · rintro ⟨u, hu⟩
    have hEU (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) :
        ∫ x, u x ∂(binLot p (2 / r) 0) = p * u (2 / r) + (1 - p) * u 0 :=
      integral_binLot _ _ _ _ hp.1 hp.2
    have e1 := (hu 0 (1 / 2) h0 h2).mp (by rw [hU _ h0, hU _ h2]; norm_num)
    have e2 := (hu (1 / 2) 0 h2 h0).mp (by rw [hU _ h0, hU _ h2]; norm_num)
    rw [hEU _ h0, hEU _ h2] at e1 e2
    have e3 := (hu 0 (1 / 4) h0 h4).mpr (by rw [hEU _ h0, hEU _ h4]; nlinarith)
    rw [hU _ h0, hU _ h4] at e3
    have : (0 : ℝ) < 2 / r := by positivity
    nlinarith

/-- **Exercise 6.C.5(a)** (MWG, p. 210). For a utility function on commodity bundles in a convex
set `K` (e.g. `ℝ^L_+`), concavity is equivalent to risk aversion over every finite lottery
whose outcomes are bundles: `∑ w_i u(x_i) ≤ u(∑ w_i x_i)`. -/
theorem exercise_6_C_5a {L : ℕ} {K : Set (Fin L → ℝ)} (hK : Convex ℝ K)
    (u : (Fin L → ℝ) → ℝ) :
    ConcaveOn ℝ K u ↔ ∀ (n : ℕ) (w : Fin n → ℝ) (x : Fin n → Fin L → ℝ), (∀ i, 0 ≤ w i) →
      ∑ i, w i = 1 → (∀ i, x i ∈ K) → ∑ i, w i * u (x i) ≤ u (∑ i, w i • x i) := by
  constructor
  · intro hc n w x hw h1 hx
    simpa only [smul_eq_mul] using hc.le_map_sum (t := Finset.univ) (fun i _ => hw i) h1
      (fun i _ => hx i)
  · intro h
    refine ⟨hK, fun x hx y hy a b ha hb hab => ?_⟩
    have := h 2 ![a, b] ![x, y] (by intro i; fin_cases i <;> simp [ha, hb]) (by simp [hab])
      (by intro i; fin_cases i <;> simp [hx, hy])
    simpa [Fin.sum_univ_two, smul_eq_mul] using this

/-- **Exercise 6.C.5(b)** (MWG, p. 210). At fixed strictly positive prices, if the utility over
commodity bundles is continuous and concave (risk averse), the derived Bernoulli utility of
wealth `v(w) = max {u(x) : p · x ≤ w}` is concave (risk averse); Kreps's Proposition 6.16(c). -/
theorem exercise_6_C_5b {L : ℕ} {u : (Fin L → ℝ) → ℝ} (hu : Continuous u)
    (hc : ConcaveOn ℝ (Ici 0) u) (p : Kreps.UtilityForMoney.Demand.PositivePrices L) :
    ConcaveOn ℝ (Ici 0) (fun w : ℝ => Kreps.UtilityForMoney.Demand.IndirectUtility
      (fun x : Kreps.UtilityForMoney.Demand.NonnegativeOrthant L => u x.val) p w.toNNReal) := by
  apply Kreps.UtilityForMoney.proposition_6_16c (hu.comp continuous_subtype_val)
  intro x y a ha
  change a * u x.val + (1 - a) * u y.val ≤ u (a • x.val + (1 - a) • y.val)
  have := hc.2 x.property y.property ha.1 (sub_nonneg.mpr ha.2) (by ring)
  simpa only [smul_eq_mul] using this

/-- The nonconcave utility of Exercise 6.C.5(c): `x₁ + x₂` minus a bump at `(1,1)`. -/
noncomputable def bumpUtility (x : Kreps.UtilityForMoney.Demand.NonnegativeOrthant 2) : ℝ :=
  x.val 0 + x.val 1 - max 0 (1 / 2 - |x.val 0 - 1| - |x.val 1 - 1|)

/-- **Exercise 6.C.5(c)** (MWG, p. 210). The converse of (b) fails: `bumpUtility` is not
concave, yet for every price vector its derived utility of wealth is `w / min(p₁, p₂)`,
linear and hence concave (risk averse). -/
theorem exercise_6_C_5c :
    ¬Kreps.UtilityForMoney.Demand.ConcaveUtility (convex_Ici (𝕜 := ℝ) (0 : Fin 2 → ℝ))
      bumpUtility ∧
    ∀ (p : Kreps.UtilityForMoney.Demand.PositivePrices 2) (w : NNReal),
      Kreps.UtilityForMoney.Demand.IndirectUtility bumpUtility p w =
        w / min (p.val 0) (p.val 1) := by
  constructor
  · intro hc
    let x : Kreps.UtilityForMoney.Demand.NonnegativeOrthant 2 := ⟨![1 / 2, 1], by
      intro i; fin_cases i <;> norm_num⟩
    let y : Kreps.UtilityForMoney.Demand.NonnegativeOrthant 2 := ⟨![3 / 2, 1], by
      intro i; fin_cases i <;> norm_num⟩
    have := hc x y (1 / 2) ⟨by norm_num, by norm_num⟩
    simp only [bumpUtility, Kreps.UtilityForMoney.Demand.Mix, x, y] at this
    norm_num at this
  · intro p w
    have hp0 := p.property 0
    have hp1 := p.property 1
    set m := min (p.val 0) (p.val 1)
    have hm : 0 < m := lt_min hp0 hp1
    have hbound (x : Kreps.UtilityForMoney.Demand.NonnegativeOrthant 2)
        (hx : x ∈ Kreps.UtilityForMoney.Demand.BudgetSet p w) : bumpUtility x ≤ w / m := by
      have hx0 : 0 ≤ x.val 0 := x.property 0
      have hx1 : 0 ≤ x.val 1 := x.property 1
      have hb : p.val 0 * x.val 0 + p.val 1 * x.val 1 ≤ w := by
        have := hx
        simpa [Kreps.UtilityForMoney.Demand.BudgetSet, Kreps.UtilityForMoney.Demand.Expenditure,
          Fin.sum_univ_two] using this
      have h1 : m * (x.val 0 + x.val 1) ≤ w := by
        have a1 := mul_le_mul_of_nonneg_right (min_le_left (p.val 0) (p.val 1)) hx0
        have a2 := mul_le_mul_of_nonneg_right (min_le_right (p.val 0) (p.val 1)) hx1
        nlinarith
      rw [le_div_iff₀ hm]
      unfold bumpUtility
      nlinarith [le_max_left 0 (1 / 2 - |x.val 0 - 1| - |x.val 1 - 1|)]
    -- a corner bundle buying only the cheaper good attains the bound
    have hwm : 0 ≤ (w : ℝ) / m := by positivity
    obtain ⟨c, hcB, hcv⟩ : ∃ c : Kreps.UtilityForMoney.Demand.NonnegativeOrthant 2,
        c ∈ Kreps.UtilityForMoney.Demand.BudgetSet p w ∧ bumpUtility c = w / m := by
      by_cases h : p.val 0 ≤ p.val 1
      · have hm' : m = p.val 0 := min_eq_left h
        refine ⟨⟨![w / m, 0], by intro j; fin_cases j <;> simp [hwm]⟩, ?_, ?_⟩
        · simp only [Kreps.UtilityForMoney.Demand.BudgetSet,
            Kreps.UtilityForMoney.Demand.Expenditure, Set.mem_ofPred_eq, Fin.sum_univ_two]
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, add_zero]
          rw [← hm']; field_simp; exact le_rfl
        · simp only [bumpUtility, Matrix.cons_val_zero, Matrix.cons_val_one, zero_sub, abs_neg,
            abs_one]
          rw [max_eq_left (by linarith [abs_nonneg ((w : ℝ) / m - 1)])]
          ring
      · have hm' : m = p.val 1 := min_eq_right (le_of_not_ge h)
        refine ⟨⟨![0, w / m], by intro j; fin_cases j <;> simp [hwm]⟩, ?_, ?_⟩
        · simp only [Kreps.UtilityForMoney.Demand.BudgetSet,
            Kreps.UtilityForMoney.Demand.Expenditure, Set.mem_ofPred_eq, Fin.sum_univ_two]
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, zero_add]
          rw [← hm']; field_simp; exact le_rfl
        · simp only [bumpUtility, Matrix.cons_val_zero, Matrix.cons_val_one, zero_sub, abs_neg,
            abs_one]
          rw [max_eq_left (by linarith [abs_nonneg ((w : ℝ) / m - 1)])]
          ring
    unfold Kreps.UtilityForMoney.Demand.IndirectUtility
    apply le_antisymm
    · apply csSup_le (Set.Nonempty.image _ ⟨c, hcB⟩)
      rintro _ ⟨x, hx, rfl⟩
      exact hbound x hx
    · rw [← hcv]
      apply le_csSup _ (Set.mem_image_of_mem _ hcB)
      refine ⟨(w : ℝ) / m, ?_⟩
      rintro _ ⟨x, hx, rfl⟩
      exact hbound x hx

end MWG.ChoiceUnderUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercises 6.C.12 and 6.C.18: constant relative risk aversion and square-root utility

MWG, pp. 211-212. Exercise 6.C.12 characterizes constant relative risk aversion on `x > 0`;
two printed statements are corrected (see `ExercisesC` and `docs/corrections.md`): the
strictly increasing CRRA utilities are `βx^{1-ρ}/(1-ρ) + γ` with `β > 0`, and the limit in (c)
holds for `(x^{1-ρ} - 1)/(1-ρ)`. Exercise 6.C.18 computes the Arrow-Pratt coefficients,
certainty equivalents and probability premia of `u(x) = √x`.
-/

namespace MWG.ChoiceUnderUncertainty

open Filter Topology Set

/-- Second derivatives on `x > 0` only depend on the values there. -/
theorem deriv2_congr_Ioi {u v : ℝ → ℝ} (h : ∀ x > 0, u x = v x) {x : ℝ} (hx : 0 < x) :
    deriv u x = deriv v x ∧ deriv (deriv u) x = deriv (deriv v) x := by
  have he : u =ᶠ[𝓝 x] v := by
    filter_upwards [lt_mem_nhds hx] with y hy using h y hy
  have hd : deriv u =ᶠ[𝓝 x] deriv v := by
    filter_upwards [lt_mem_nhds hx] with y hy
    have he' : u =ᶠ[𝓝 y] v := by
      filter_upwards [lt_mem_nhds hy] with z hz using h z hz
    exact he'.deriv_eq
  exact ⟨he.deriv_eq, hd.deriv_eq⟩

/-- The relative risk aversion of `βx^{1-ρ}/(1-ρ) + γ` is `ρ` on `x > 0`. -/
theorem relativeRiskAversion_crra {ρ β γ : ℝ} (hρ : ρ ≠ 1) (hβ : 0 < β) {x : ℝ} (hx : 0 < x) :
    relativeRiskAversion (fun y => β * y ^ (1 - ρ) / (1 - ρ) + γ) x = ρ := by
  have h1ρ : (1 : ℝ) - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ)
  have hd1 : deriv (fun y => β * y ^ (1 - ρ) / (1 - ρ) + γ) = fun y => β * y ^ (-ρ) := by
    funext y
    rw [deriv_add_const, deriv_div_const, deriv_const_mul_field, Real.deriv_rpow_const]
    rw [show 1 - ρ - 1 = -ρ by ring]
    field_simp
  have hd2 : deriv (fun y => β * y ^ (-ρ)) x = β * (-ρ * x ^ (-ρ - 1)) := by
    rw [deriv_const_mul_field, Real.deriv_rpow_const]
  rw [relativeRiskAversion_eq, hd1, hd2]
  have hp : 0 < x ^ (-ρ) := Real.rpow_pos_of_pos hx _
  have he : x ^ (-ρ - 1) = x ^ (-ρ) / x := by
    rw [Real.rpow_sub hx, Real.rpow_one]
  rw [he]
  field_simp

/-- The relative risk aversion of `β ln x + γ` is `1` on `x > 0`. -/
theorem relativeRiskAversion_log {β γ : ℝ} (hβ : 0 < β) {x : ℝ} (hx : 0 < x) :
    relativeRiskAversion (fun y => β * Real.log y + γ) x = 1 := by
  have hd1 : deriv (fun y => β * Real.log y + γ) = fun y => β * y⁻¹ := by
    funext y
    rw [deriv_add_const, deriv_const_mul_field, Real.deriv_log]
  rw [relativeRiskAversion_eq, hd1, deriv_const_mul_field, deriv_inv]
  field_simp

/-- Marginal utility with constant relative risk aversion `ρ` is `c x^{-ρ}`, `c > 0`. -/
theorem marginal_of_constant_relative {u : ℝ → ℝ} (hd : ∀ x > 0, ContDiffAt ℝ 2 u x)
    (hp : ∀ x > 0, 0 < deriv u x) {ρ : ℝ} (hc : ∀ x > 0, relativeRiskAversion u x = ρ) :
    ∃ c > 0, ∀ x > 0, deriv u x = c * x ^ (-ρ) := by
  have hd2 (y : ℝ) (hy : 0 < y) : DifferentiableAt ℝ (deriv u) y :=
    ((hd y hy).derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
  let F := fun x : ℝ => deriv u x * x ^ ρ
  have hF (x : ℝ) (hx : x ∈ Ioi (0 : ℝ)) : HasDerivAt F 0 x := by
    have hx' : (0 : ℝ) < x := hx
    have h := (hd2 x hx').hasDerivAt.mul (Real.hasDerivAt_rpow_const (p := ρ) (Or.inl hx'.ne'))
    convert h using 1
    have hr := hc x hx'
    rw [relativeRiskAversion_eq, div_eq_iff (hp x hx').ne'] at hr
    have he : x ^ (ρ - 1) = x ^ ρ / x := by rw [Real.rpow_sub hx', Real.rpow_one]
    rw [he]
    field_simp
    linear_combination (x ^ ρ) * hr
  refine ⟨deriv u 1, hp 1 one_pos, fun x hx => ?_⟩
  have := Kreps.UtilityForMoney.eq_on_interval_of_deriv_zero (convex_Ioi 0) hF
    (mem_Ioi.mpr hx) (mem_Ioi.mpr one_pos)
  simp only [F] at this
  have hp' : 0 < x ^ ρ := Real.rpow_pos_of_pos hx _
  rw [Real.one_rpow, mul_one] at this
  rw [Real.rpow_neg hx.le, ← this]
  field_simp

/-- **Exercise 6.C.12(a)** (MWG, p. 211), corrected. A strictly increasing (`u' > 0`), twice
continuously differentiable `u` on `x > 0` has constant relative risk aversion `ρ ≠ 1` iff
`u(x) = βx^{1-ρ}/(1-ρ) + γ` with `β > 0`. -/
theorem exercise_6_C_12a {u : ℝ → ℝ} (hd : ∀ x > 0, ContDiffAt ℝ 2 u x)
    (hp : ∀ x > 0, 0 < deriv u x) {ρ : ℝ} (hρ : ρ ≠ 1) :
    (∀ x > 0, relativeRiskAversion u x = ρ) ↔
      ∃ β > 0, ∃ γ : ℝ, ∀ x > 0, u x = β * x ^ (1 - ρ) / (1 - ρ) + γ := by
  have h1ρ : (1 : ℝ) - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ)
  constructor
  · intro hc
    obtain ⟨c, hc0, hu'⟩ := marginal_of_constant_relative hd hp hc
    let G := fun x : ℝ => u x - c * x ^ (1 - ρ) / (1 - ρ)
    have hG (x : ℝ) (hx : x ∈ Ioi (0 : ℝ)) : HasDerivAt G 0 x := by
      have hx' : (0 : ℝ) < x := hx
      have h1 : HasDerivAt u (c * x ^ (-ρ)) x := by
        rw [← hu' x hx']
        exact ((hd x hx').differentiableAt (by norm_num)).hasDerivAt
      have h2 := ((Real.hasDerivAt_rpow_const (p := 1 - ρ) (Or.inl hx'.ne')).const_mul c).div_const
        (1 - ρ)
      convert h1.sub h2 using 1
      rw [show 1 - ρ - 1 = -ρ by ring]
      field_simp
      ring
    refine ⟨c, hc0, G 1, fun x hx => ?_⟩
    have := Kreps.UtilityForMoney.eq_on_interval_of_deriv_zero (convex_Ioi 0) hG
      (mem_Ioi.mpr hx) (mem_Ioi.mpr one_pos)
    simp only [G] at this
    linarith
  · rintro ⟨β, hβ, γ, he⟩ x hx
    have hcg := deriv2_congr_Ioi he hx
    rw [relativeRiskAversion_eq, hcg.1, hcg.2, ← relativeRiskAversion_eq]
    exact relativeRiskAversion_crra hρ hβ hx

/-- **Exercise 6.C.12(a)**: the printed form fails for `ρ > 1`. Every `βx^{1-ρ} + γ` with
`β > 0` and `ρ > 1` is strictly decreasing on `x > 0`, while `u(x) = -1/x` is strictly
increasing with constant relative risk aversion `2`. -/
theorem exercise_6_C_12a_printed_counterexample :
    (∀ ρ : ℝ, 1 < ρ → ∀ β : ℝ, 0 < β → ∀ γ : ℝ,
      StrictAntiOn (fun x : ℝ => β * x ^ (1 - ρ) + γ) (Ioi 0)) ∧
    StrictMonoOn (fun x : ℝ => -x⁻¹) (Ioi 0) ∧
    ∀ x : ℝ, 0 < x → relativeRiskAversion (fun y : ℝ => -y⁻¹) x = 2 := by
  refine ⟨fun ρ hρ β hβ γ x hx y hy hxy => ?_, fun x hx y hy hxy => ?_, fun x hx => ?_⟩
  · have := Real.rpow_lt_rpow_of_neg hx hxy (show 1 - ρ < 0 by linarith)
    simp only
    nlinarith
  · simp only [neg_lt_neg_iff]
    exact (inv_lt_inv₀ hy hx).mpr hxy
  · have he : ∀ y : ℝ, y > 0 → -y⁻¹ = 1 * y ^ (1 - 2 : ℝ) / (1 - 2) + 0 := by
      intro y hy
      rw [show (1 : ℝ) - 2 = -1 by norm_num, Real.rpow_neg_one]
      ring
    have hcg := deriv2_congr_Ioi he hx
    rw [relativeRiskAversion_eq, hcg.1, hcg.2, ← relativeRiskAversion_eq]
    exact relativeRiskAversion_crra (by norm_num) one_pos hx

/-- **Exercise 6.C.12(b)** (MWG, p. 211). A strictly increasing, twice continuously
differentiable `u` on `x > 0` has constant relative risk aversion `1` iff
`u(x) = β ln x + γ` with `β > 0`. -/
theorem exercise_6_C_12b {u : ℝ → ℝ} (hd : ∀ x > 0, ContDiffAt ℝ 2 u x)
    (hp : ∀ x > 0, 0 < deriv u x) :
    (∀ x > 0, relativeRiskAversion u x = 1) ↔
      ∃ β > 0, ∃ γ : ℝ, ∀ x > 0, u x = β * Real.log x + γ := by
  constructor
  · intro hc
    obtain ⟨c, hc0, hu'⟩ := marginal_of_constant_relative hd hp hc
    let G := fun x : ℝ => u x - c * Real.log x
    have hG (x : ℝ) (hx : x ∈ Ioi (0 : ℝ)) : HasDerivAt G 0 x := by
      have hx' : (0 : ℝ) < x := hx
      have h1 : HasDerivAt u (c * x ^ (-1 : ℝ)) x := by
        rw [← hu' x hx']
        exact ((hd x hx').differentiableAt (by norm_num)).hasDerivAt
      convert h1.sub ((Real.hasDerivAt_log hx'.ne').const_mul c) using 1
      rw [Real.rpow_neg_one]; ring
    refine ⟨c, hc0, u 1, fun x hx => ?_⟩
    have := Kreps.UtilityForMoney.eq_on_interval_of_deriv_zero (convex_Ioi 0) hG
      (mem_Ioi.mpr hx) (mem_Ioi.mpr one_pos)
    simp only [G, Real.log_one, mul_zero, sub_zero] at this
    linarith
  · rintro ⟨β, hβ, γ, he⟩ x hx
    have hcg := deriv2_congr_Ioi he hx
    rw [relativeRiskAversion_eq, hcg.1, hcg.2, ← relativeRiskAversion_eq]
    exact relativeRiskAversion_log hβ hx

/-- **Exercise 6.C.12(c)** (MWG, p. 211), corrected: `(x^{1-ρ} - 1)/(1-ρ) → ln x` as
`ρ → 1`, for every `x > 0`. -/
theorem exercise_6_C_12c {x : ℝ} (hx : 0 < x) :
    Tendsto (fun ρ : ℝ => (x ^ (1 - ρ) - 1) / (1 - ρ)) (𝓝[≠] 1) (𝓝 (Real.log x)) := by
  have hd := (Real.hasStrictDerivAt_const_rpow hx 0).hasDerivAt.tendsto_slope_zero
  simp only [zero_add, Real.rpow_zero, one_mul, smul_eq_mul] at hd
  have hmap : Tendsto (fun ρ : ℝ => 1 - ρ) (𝓝[≠] 1) (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have : Tendsto (fun ρ : ℝ => 1 - ρ) (𝓝 1) (𝓝 (1 - 1)) :=
        (continuous_const.sub continuous_id).tendsto 1
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ρ hρ
      exact sub_ne_zero.mpr (Ne.symm hρ)
  refine (hd.comp hmap).congr' (Eventually.of_forall fun ρ => ?_)
  simp only [Function.comp_apply]
  rw [div_eq_inv_mul]

/-- **Exercise 6.C.12(c)**: the printed limit fails; at `x = 1`, `x^{1-ρ}/(1-ρ) = 1/(1-ρ)` does
not tend to `ln 1 = 0`. -/
theorem exercise_6_C_12c_printed_counterexample :
    ¬Tendsto (fun ρ : ℝ => (1 : ℝ) ^ (1 - ρ) / (1 - ρ)) (𝓝[≠] 1) (𝓝 (Real.log 1)) := by
  intro h
  rw [Real.log_one] at h
  have h1 := h.eventually (Metric.ball_mem_nhds (0 : ℝ) one_pos)
  have h2a : Metric.ball (1 : ℝ) 1 ∈ 𝓝[≠] (1 : ℝ) :=
    nhdsWithin_le_nhds (Metric.ball_mem_nhds _ one_pos)
  have h2 : ∀ᶠ ρ in 𝓝[≠] (1 : ℝ), ρ ∈ Metric.ball (1 : ℝ) 1 := h2a
  have h3 : ∀ᶠ ρ in 𝓝[≠] (1 : ℝ), ρ ≠ 1 := self_mem_nhdsWithin
  obtain ⟨ρ, hρ1, hρ2, hρ3⟩ := (h1.and (h2.and h3)).exists
  rw [Metric.mem_ball, Real.dist_eq] at hρ2
  simp only [Real.dist_eq] at hρ1
  simp only [Real.one_rpow, sub_zero] at hρ1
  have hne : (1 : ℝ) - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ3)
  have hlt : |1 - ρ| < 1 := by rw [abs_sub_comm]; exact hρ2
  rw [abs_div, abs_one, div_lt_one (abs_pos.mpr hne)] at hρ1
  linarith

end MWG.ChoiceUnderUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercises 6.C.13, 6.C.14, 6.C.16 and 6.C.18

MWG, pp. 211-212. The risk-neutral firm prefers random prices (6.C.13); "strongly more risk
averse" implies the Arrow-Pratt comparison and is strictly stronger (6.C.14); selling and
buying prices of a lottery (6.C.16); square-root utility (6.C.18).

In 6.C.14 the Bernoulli utilities are defined on the line and compared pointwise; part (b)
works on `[0, ∞)` as the hint says. In 6.C.16 the lottery pays `G` with probability `p` and
`B` otherwise, and the probability in part (d) is left general by the book; we give the
selling price for every `p` and both prices at `p = 1/2`.
-/

namespace MWG.ChoiceUnderUncertainty

open Filter Topology Set

/-- The maximal profit `π(p) = max_{y ∈ Y} p · y`. -/
noncomputable def maxProfit {L : ℕ} (Y : Set (Fin L → ℝ)) (p : Fin L → ℝ) : ℝ :=
  sSup ((fun y => ∑ l, p l * y l) '' Y)

/-- **Exercise 6.C.13** (MWG, p. 211). If production decisions are made after uncertain prices
are revealed, a risk-neutral firm weakly prefers the random prices to their expected value:
`π(∑ q_i P_i) ≤ ∑ q_i π(P_i)` (the profit function is convex). -/
theorem exercise_6_C_13 {L n : ℕ} (Y : Set (Fin L → ℝ)) (hY : Y.Nonempty)
    (hb : ∀ p : Fin L → ℝ, BddAbove ((fun y => ∑ l, p l * y l) '' Y)) (q : Fin n → ℝ)
    (P : Fin n → Fin L → ℝ) (hq : ∀ i, 0 ≤ q i) :
    maxProfit Y (∑ i, q i • P i) ≤ ∑ i, q i * maxProfit Y (P i) := by
  apply csSup_le (hY.image _)
  rintro _ ⟨y, hy, rfl⟩
  have e : ∑ l, (∑ i, q i • P i) l * y l = ∑ i, q i * ∑ l, P i l * y l := by
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring
  dsimp only
  rw [e]
  exact Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_left (le_csSup (hb (P i)) ⟨y, hy, rfl⟩) (hq i)

/-- **Exercise 6.C.14(a)** (MWG, p. 211). If `u* = ku + v` with `k > 0` and `v` nonincreasing
and concave, then `u*` is more risk averse than `u` in the Arrow-Pratt sense at every `x`
where `u' > 0`, `u'' ≤ 0` and `u*' > 0`. -/
theorem exercise_6_C_14a {u v : ℝ → ℝ} {k : ℝ} (hu1 : Differentiable ℝ u)
    (hv1 : Differentiable ℝ v) (hv : Antitone v) (hvc : ConcaveOn ℝ univ v) {x : ℝ}
    (hu2 : DifferentiableAt ℝ (deriv u) x) (hv2 : ∀ y, DifferentiableAt ℝ (deriv v) y)
    (hup : 0 < deriv u x) (huc : deriv (deriv u) x ≤ 0)
    (hpos : 0 < k * deriv u x + deriv v x) :
    arrowPratt u x ≤ arrowPratt (fun y => k * u y + v y) x := by
  have hvd : deriv v x ≤ 0 := hv.deriv_nonpos
  have hvcc : deriv (deriv v) x ≤ 0 :=
    (footnote_6_16 convex_univ isOpen_univ (fun y _ => hv1 y) (fun y _ => hv2 y)).mp hvc x
      (mem_univ x)
  have hd : deriv (fun y => k * u y + v y) = fun y => k * deriv u y + deriv v y := by
    funext y
    exact (((hu1 y).hasDerivAt.const_mul k).add (hv1 y).hasDerivAt).deriv
  have hd2 : deriv (fun y => k * deriv u y + deriv v y) x =
      k * deriv (deriv u) x + deriv (deriv v) x := by
    exact ((hu2.hasDerivAt.const_mul k).add (hv2 x).hasDerivAt).deriv
  unfold arrowPratt
  rw [hd, hd2, div_le_div_iff₀ hup hpos]
  nlinarith [mul_nonneg (neg_nonneg.mpr huc) (neg_nonneg.mpr hvd), mul_nonneg
    (neg_nonneg.mpr hvcc) hup.le]

/-- **Exercise 6.C.14(b)** (MWG, p. 211). If `u` is bounded on `[0, ∞)` and `u* = ku + v` is
increasing there with `v` nonincreasing and concave, then `v` is constant: the only strongly
more risk-averse utilities are `ku + c`. -/
theorem exercise_6_C_14b {u ustar v : ℝ → ℝ} {k : ℝ} (hk : 0 < k) {B : ℝ}
    (hbd : ∀ x ≥ 0, |u x| ≤ B) (hmono : MonotoneOn ustar (Ici 0)) (hv : AntitoneOn v (Ici 0))
    (hvc : ConcaveOn ℝ (Ici 0) v) (he : ∀ x ≥ 0, ustar x = k * u x + v x) :
    ∀ x ≥ 0, v x = v 0 := by
  intro x hx
  rcases eq_or_lt_of_le hx with h0 | hxpos
  · rw [← h0]
  by_contra hne
  have hlt : v x < v 0 := lt_of_le_of_ne (hv (mem_Ici.mpr le_rfl) (mem_Ici.mpr hx) hx) hne
  set s := (v x - v 0) / (x - 0)
  have hs : s < 0 := div_neg_of_neg_of_pos (by linarith) (by linarith)
  set T := (2 * k * B + |v x| + |v 0| + 1) / (-s)
  have hB : 0 ≤ B := (abs_nonneg _).trans (hbd 0 le_rfl)
  have hT : 0 < T := div_pos (by positivity) (by linarith)
  set t := x + T
  have hslope := hvc.slope_anti_adjacent (mem_Ici.mpr le_rfl) (mem_Ici.mpr (by linarith))
    hxpos (show x < t by simp only [t]; linarith)
  have hvt : v t ≤ v x + s * T := by
    rw [div_le_iff₀ (show (0 : ℝ) < t - x by simp only [t]; linarith)] at hslope
    simp only [t] at hslope ⊢
    have : x + T - x = T := by ring
    rw [this] at hslope
    linarith
  have hs0 : s ≠ 0 := hs.ne
  have hsT : s * T = -(2 * k * B + |v x| + |v 0| + 1) := by
    simp only [T]; field_simp
  have hmt := hmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr (by simp only [t]; linarith))
    (show (0 : ℝ) ≤ t by simp only [t]; linarith)
  rw [he 0 le_rfl, he t (by simp only [t]; linarith)] at hmt
  have h1 := abs_le.mp (hbd 0 le_rfl)
  have h2 := abs_le.mp (hbd t (by simp only [t]; linarith))
  have h3 := le_abs_self (v x)
  have h4 := neg_abs_le (v 0)
  nlinarith

/-- **Exercise 6.C.14(c)** (MWG, p. 211). Being strongly more risk averse is strictly stronger
than the Arrow-Pratt comparison: `u* = -e^{-2x}` has `r_A = 2 > 1 = r_A(-e^{-x})` everywhere,
yet it is not of the form `k(-e^{-x}) + v` with `k > 0` and `v` nonincreasing and concave on
`[0, ∞)`. -/
theorem exercise_6_C_14c :
    (∀ x, arrowPratt (Kreps.UtilityForMoney.ExponentialUtility 1) x <
      arrowPratt (Kreps.UtilityForMoney.ExponentialUtility 2) x) ∧
    ¬∃ k > 0, ∃ v : ℝ → ℝ, AntitoneOn v (Ici 0) ∧ ConcaveOn ℝ (Ici 0) v ∧
      ∀ x ≥ 0, Kreps.UtilityForMoney.ExponentialUtility 2 x =
        k * Kreps.UtilityForMoney.ExponentialUtility 1 x + v x := by
  constructor
  · intro x
    rw [arrowPratt_eq_kreps, arrowPratt_eq_kreps,
      Kreps.UtilityForMoney.absoluteRiskAversion_exponential one_ne_zero,
      Kreps.UtilityForMoney.absoluteRiskAversion_exponential two_ne_zero]
    norm_num
  · rintro ⟨k, hk, v, hv, hvc, he⟩
    have hbd : ∀ x ≥ 0, |Kreps.UtilityForMoney.ExponentialUtility 1 x| ≤ 1 := by
      intro x hx
      simp only [Kreps.UtilityForMoney.ExponentialUtility, abs_neg, neg_mul, one_mul,
        abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (by linarith)
    have hconst := exercise_6_C_14b hk hbd
      ((Kreps.UtilityForMoney.exponentialUtility_strictMono two_pos).monotone.monotoneOn _)
      hv hvc he
    have hval (x : ℝ) (hx : 0 ≤ x) : -Real.exp (-2 * x) = -k * Real.exp (-x) + v 0 := by
      have := he x hx
      rw [hconst x hx] at this
      simp only [Kreps.UtilityForMoney.ExponentialUtility] at this
      rw [this]; ring_nf
    have hl2 : Real.exp (-Real.log 2) = 1 / 2 := by
      rw [Real.exp_neg, Real.exp_log two_pos, one_div]
    have hsq (t : ℝ) : Real.exp (-2 * t) = Real.exp (-t) * Real.exp (-t) := by
      rw [← Real.exp_add]; ring_nf
    have e0 := hval 0 le_rfl
    have e1 := hval (Real.log 2) (Real.log_nonneg (by norm_num))
    have e2 := hval (2 * Real.log 2) (by positivity)
    rw [hsq, hl2] at e1
    rw [hsq, show -(2 * Real.log 2) = -Real.log 2 + -Real.log 2 by ring, Real.exp_add, hl2]
      at e2
    simp only [mul_zero, Real.exp_zero, neg_zero] at e0
    nlinarith

/-- **Exercise 6.C.16(a)** (MWG, p. 212). The minimum selling price `s` of the lottery
(`G` with probability `p`, `B` otherwise) owned at wealth `w`: `u(w + s) = E u(w + L)`. -/
def IsSellingPrice (u : ℝ → ℝ) (w G B p s : ℝ) : Prop :=
  u (w + s) = p * u (w + G) + (1 - p) * u (w + B)

/-- **Exercise 6.C.16(b)** (MWG, p. 212). The maximum buying price `b`:
`E u(w - b + L) = u(w)`. -/
def IsBuyingPrice (u : ℝ → ℝ) (w G B p b : ℝ) : Prop :=
  p * u (w - b + G) + (1 - p) * u (w - b + B) = u w

/-- **Exercise 6.C.16(a)** (MWG, p. 212). A continuous, strictly increasing Bernoulli utility
has a unique selling price. -/
theorem exercise_6_C_16a {u : ℝ → ℝ} (hc : Continuous u) (hi : StrictMono u) (w G B p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : ∃! s, IsSellingPrice u w G B p s := by
  have hlo : u (w + min G B) ≤ p * u (w + G) + (1 - p) * u (w + B) := by
    have h1 := hi.monotone (show w + min G B ≤ w + G by linarith [min_le_left G B])
    have h2 := hi.monotone (show w + min G B ≤ w + B by linarith [min_le_right G B])
    nlinarith
  have hhi : p * u (w + G) + (1 - p) * u (w + B) ≤ u (w + max G B) := by
    have h1 := hi.monotone (show w + G ≤ w + max G B by linarith [le_max_left G B])
    have h2 := hi.monotone (show w + B ≤ w + max G B by linarith [le_max_right G B])
    nlinarith
  obtain ⟨s, -, hs⟩ := intermediate_value_Icc (min_le_max) (f := fun s => u (w + s))
    (by fun_prop : Continuous fun s => u (w + s)).continuousOn ⟨hlo, hhi⟩
  refine ⟨s, hs, fun t ht => ?_⟩
  have := hi.injective (ht.trans hs.symm)
  linarith

/-- **Exercise 6.C.16(b)** (MWG, p. 212). A continuous, strictly increasing Bernoulli utility
has a unique buying price. -/
theorem exercise_6_C_16b {u : ℝ → ℝ} (hc : Continuous u) (hi : StrictMono u) (w G B p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : ∃! b, IsBuyingPrice u w G B p b := by
  let g := fun b : ℝ => p * u (w - b + G) + (1 - p) * u (w - b + B)
  have hg : Continuous g := by simp only [g]; fun_prop
  have hanti : StrictAnti g := by
    intro b b' hbb
    simp only [g]
    have h1 := hi (show w - b' + G < w - b + G by linarith)
    have h2 := hi (show w - b' + B < w - b + B by linarith)
    rcases eq_or_lt_of_le hp0 with h | h
    · subst h; nlinarith
    · nlinarith
  have hlo : g (max G B) ≤ u w := by
    simp only [g]
    have h1 := hi.monotone (show w - max G B + G ≤ w by linarith [le_max_left G B])
    have h2 := hi.monotone (show w - max G B + B ≤ w by linarith [le_max_right G B])
    nlinarith
  have hhi : u w ≤ g (min G B) := by
    simp only [g]
    have h1 := hi.monotone (show w ≤ w - min G B + G by linarith [min_le_left G B])
    have h2 := hi.monotone (show w ≤ w - min G B + B by linarith [min_le_right G B])
    nlinarith
  obtain ⟨b, -, hb⟩ := intermediate_value_Icc' min_le_max hg.continuousOn ⟨hlo, hhi⟩
  exact ⟨b, hb, fun t ht => hanti.injective (ht.trans hb.symm)⟩

/-- **Exercise 6.C.16(c)** (MWG, p. 212). Buying and selling prices coincide under constant
absolute risk aversion `u(x) = -e^{-ax}`, `a > 0` (no wealth effect on risk attitudes). -/
theorem exercise_6_C_16c_cara {a : ℝ} (ha : 0 < a) {w G B p s b : ℝ}
    (hs : IsSellingPrice (Kreps.UtilityForMoney.ExponentialUtility a) w G B p s)
    (hb : IsBuyingPrice (Kreps.UtilityForMoney.ExponentialUtility a) w G B p b) : s = b := by
  unfold IsSellingPrice IsBuyingPrice Kreps.UtilityForMoney.ExponentialUtility at *
  set M := p * Real.exp (-a * G) + (1 - p) * Real.exp (-a * B)
  have k0 (t : ℝ) : Real.exp (-a * (w + t)) = Real.exp (-a * w) * Real.exp (-a * t) := by
    rw [← Real.exp_add]; ring_nf
  have k1 (t : ℝ) : Real.exp (-a * (w - b + t)) =
      Real.exp (-a * w) * (Real.exp (a * b) * Real.exp (-a * t)) := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  rw [k0, k0, k0] at hs
  rw [k1, k1] at hb
  have hw := (Real.exp_pos (-a * w)).ne'
  have h1 : Real.exp (-a * w) * (Real.exp (-a * s) - M) = 0 := by
    simp only [M]; linear_combination (-1 : ℝ) * hs
  have h2 : Real.exp (-a * w) * (Real.exp (a * b) * M - 1) = 0 := by
    simp only [M]; linear_combination (-1 : ℝ) * hb
  have hsM : Real.exp (-a * s) = M := by
    have := (mul_eq_zero.mp h1).resolve_left hw; linarith
  have hbM : Real.exp (a * b) * M = 1 := by
    have := (mul_eq_zero.mp h2).resolve_left hw; linarith
  rw [← hsM, ← Real.exp_add, Real.exp_eq_one_iff] at hbM
  have : a * (b - s) = 0 := by linarith
  rcases mul_eq_zero.mp this with h | h
  · linarith
  · linarith

/-- **Exercise 6.C.16(c)** (MWG, p. 212). For a riskless lottery (`G = B`) buying and selling
prices coincide (both equal `G`) for every strictly increasing `u`. -/
theorem exercise_6_C_16c_riskless {u : ℝ → ℝ} (hi : StrictMono u) {w G p s b : ℝ}
    (hs : IsSellingPrice u w G G p s) (hb : IsBuyingPrice u w G G p b) : s = G ∧ b = G := by
  unfold IsSellingPrice IsBuyingPrice at *
  constructor
  · have : u (w + s) = u (w + G) := by rw [hs]; ring
    have := hi.injective this; linarith
  · have : u (w - b + G) = u w := by rw [← hb]; ring
    have := hi.injective this; linarith

/-- Square-root facts used in Exercises 6.C.16(d) and 6.C.18. -/
theorem sqrt_of_sq {a b : ℝ} (hb : 0 ≤ b) (h : a = b ^ 2) : Real.sqrt a = b := by
  rw [h, Real.sqrt_sq hb]

/-- **Exercise 6.C.16(d)** (MWG, p. 212). With `G = 10`, `B = 5`, `w = 10`, `u(x) = √x`, the
selling price is `s = (p√20 + (1 - p)√15)² - 10` for every `p ∈ [0,1]`; at `p = 1/2` it is
`5√3 - 5/4`, the buying price is `235/32`, and the buying price is strictly lower. -/
theorem exercise_6_C_16d :
    (∀ p : ℝ, 0 ≤ p → p ≤ 1 → IsSellingPrice Real.sqrt 10 10 5 p
      ((p * Real.sqrt 20 + (1 - p) * Real.sqrt 15) ^ 2 - 10)) ∧
    IsSellingPrice Real.sqrt 10 10 5 (1 / 2) (5 * Real.sqrt 3 - 5 / 4) ∧
    IsBuyingPrice Real.sqrt 10 10 5 (1 / 2) (235 / 32) ∧
    (235 / 32 : ℝ) < 5 * Real.sqrt 3 - 5 / 4 := by
  have h20 := Real.sqrt_nonneg 20
  have h15 := Real.sqrt_nonneg 15
  have h3 := Real.sqrt_nonneg 3
  have s20 := Real.sq_sqrt (show (0 : ℝ) ≤ 20 by norm_num)
  have s15 := Real.sq_sqrt (show (0 : ℝ) ≤ 15 by norm_num)
  have s3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hprod : Real.sqrt 20 * Real.sqrt 15 = 10 * Real.sqrt 3 := by
    rw [← Real.sqrt_mul (by norm_num)]
    exact sqrt_of_sq (by positivity) (by nlinarith)
  refine ⟨fun p hp0 hp1 => ?_, ?_, ?_, ?_⟩
  · unfold IsSellingPrice
    rw [show (10 : ℝ) + ((p * Real.sqrt 20 + (1 - p) * Real.sqrt 15) ^ 2 - 10) =
      (p * Real.sqrt 20 + (1 - p) * Real.sqrt 15) ^ 2 by ring,
      Real.sqrt_sq (by nlinarith)]
    norm_num
  · unfold IsSellingPrice
    rw [sqrt_of_sq (b := (Real.sqrt 20 + Real.sqrt 15) / 2) (by positivity) (by nlinarith)]
    norm_num; ring
  · unfold IsBuyingPrice
    have h10 := Real.sqrt_nonneg 10
    have s10 := Real.sq_sqrt (show (0 : ℝ) ≤ 10 by norm_num)
    have h405 : Real.sqrt (10 - 235 / 32 + 10) = 9 * Real.sqrt 10 / 8 :=
      sqrt_of_sq (by positivity) (by nlinarith)
    have h245 : Real.sqrt (10 - 235 / 32 + 5) = 7 * Real.sqrt 10 / 8 :=
      sqrt_of_sq (by positivity) (by nlinarith)
    rw [h405, h245]
    ring
  · nlinarith [Real.sqrt_nonneg 3, sq_nonneg (Real.sqrt 3 - 1.71875)]

/-- The Arrow-Pratt coefficient of `√x` is `1/(2x)` on `x > 0`. -/
theorem arrowPratt_sqrt {x : ℝ} (hx : 0 < x) : arrowPratt Real.sqrt x = 1 / (2 * x) := by
  have hd : deriv Real.sqrt =ᶠ[𝓝 x] fun y => 1 / (2 * Real.sqrt y) := by
    filter_upwards [lt_mem_nhds hx] with y hy
    exact (Real.hasDerivAt_sqrt hy.ne').deriv
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have h2 : HasDerivAt (fun y => 1 / (2 * Real.sqrt y))
      ((0 * (2 * Real.sqrt x) - 1 * (2 * (1 / (2 * Real.sqrt x)))) / (2 * Real.sqrt x) ^ 2) x :=
    (hasDerivAt_const x (1 : ℝ)).div ((Real.hasDerivAt_sqrt hx.ne').const_mul 2) (by positivity)
  unfold arrowPratt
  rw [hd.deriv_eq, h2.deriv, (Real.hasDerivAt_sqrt hx.ne').deriv]
  have := Real.sq_sqrt hx.le
  field_simp
  nlinarith

/-- **Exercise 6.C.18(a)** (MWG, p. 212). For `u(x) = √x` at wealth `5`, `r_A = 1/10` and
`r_R = 1/2`. -/
theorem exercise_6_C_18a :
    arrowPratt Real.sqrt 5 = 1 / 10 ∧ relativeRiskAversion Real.sqrt 5 = 1 / 2 := by
  have h := arrowPratt_sqrt (show (0 : ℝ) < 5 by norm_num)
  refine ⟨by rw [h]; norm_num, by rw [relativeRiskAversion, h]; norm_num⟩

/-- **Exercise 6.C.18(b)** (MWG, p. 212). For the gamble `(16, 4; 1/2, 1/2)`: the certainty
equivalent is `9` and the probability premium at the mean `10` is `(√10 - 3)/2`. -/
theorem exercise_6_C_18b :
    Real.sqrt 9 = (Real.sqrt 16 + Real.sqrt 4) / 2 ∧
      probPremium Real.sqrt 10 6 = (Real.sqrt 10 - 3) / 2 := by
  have e9 : Real.sqrt 9 = 3 := sqrt_of_sq (by norm_num) (by norm_num)
  have e16 : Real.sqrt 16 = 4 := sqrt_of_sq (by norm_num) (by norm_num)
  have e4 : Real.sqrt 4 = 2 := sqrt_of_sq (by norm_num) (by norm_num)
  refine ⟨by rw [e9, e16, e4]; norm_num, ?_⟩
  unfold probPremium
  rw [show (10 : ℝ) + 6 = 16 by norm_num, show (10 : ℝ) - 6 = 4 by norm_num, e16, e4]
  ring

/-- **Exercise 6.C.18(c)** (MWG, p. 212). For `(36, 16; 1/2, 1/2)`: the certainty equivalent is
`25` and the probability premium is `(√26 - 5)/2`. Compared with (b), the risk premium
(mean minus certainty equivalent) is `1` in both, while the probability premium is smaller at
the higher wealth (decreasing absolute risk aversion). -/
theorem exercise_6_C_18c :
    Real.sqrt 25 = (Real.sqrt 36 + Real.sqrt 16) / 2 ∧
      probPremium Real.sqrt 26 10 = (Real.sqrt 26 - 5) / 2 ∧
      (10 : ℝ) - 9 = 26 - 25 ∧ (Real.sqrt 26 - 5) / 2 < (Real.sqrt 10 - 3) / 2 := by
  have e25 : Real.sqrt 25 = 5 := sqrt_of_sq (by norm_num) (by norm_num)
  have e36 : Real.sqrt 36 = 6 := sqrt_of_sq (by norm_num) (by norm_num)
  have e16 : Real.sqrt 16 = 4 := sqrt_of_sq (by norm_num) (by norm_num)
  refine ⟨by rw [e25, e36, e16]; norm_num, ?_, by norm_num, ?_⟩
  · unfold probPremium
    rw [show (26 : ℝ) + 10 = 36 by norm_num, show (26 : ℝ) - 10 = 16 by norm_num, e36, e16]
    ring
  · have h26 := Real.sq_sqrt (show (0 : ℝ) ≤ 26 by norm_num)
    have h10 := Real.sq_sqrt (show (0 : ℝ) ≤ 10 by norm_num)
    nlinarith [Real.sqrt_nonneg 26, Real.sqrt_nonneg 10, sq_nonneg (Real.sqrt 26 - 5.1),
      sq_nonneg (Real.sqrt 10 - 3.16)]

end MWG.ChoiceUnderUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercises 6.C.9 (precautionary saving) and 6.C.20

MWG, pp. 210-213. Exercise 6.C.9 (Kimball): uncertainty about second-period income and
precautionary saving, absolute prudence `-v'''/v''`, and its relation to decreasing absolute
risk aversion. Exercise 6.C.20: the second derivative of the certainty equivalent of the
symmetric gamble `x ± ε` tends to `-r_A(x)`.

Corrections: in 6.C.9(c) the strict inequality needs a nondegenerate `y` (for `y ≡ 0` it is an
equality); in 6.C.9(d), with "decreasing" read as nonincreasing (as throughout Section 6.C), the
conclusion is `-v'''/v'' ≥ -v''/v'`, with equality for constant absolute risk aversion; it is
strict where `r_A' < 0`. The expectation of second-period utility is over a compactly supported
distribution of `y` (the convention of `MoneyLotteries`).
-/

namespace MWG.ChoiceUnderUncertainty

open MeasureTheory Filter Topology Set

/-- The tangent line of a concave differentiable function lies above it. -/
theorem concave_le_tangent {f : ℝ → ℝ} (hc : ConcaveOn ℝ univ f) {z₀ : ℝ}
    (hd : DifferentiableAt ℝ f z₀) (z : ℝ) : f z ≤ f z₀ + deriv f z₀ * (z - z₀) := by
  rcases lt_trichotomy z₀ z with h | rfl | h
  · have := hc.slope_le_deriv (mem_univ z₀) (mem_univ z) h hd
    rw [slope_def_field, div_le_iff₀ (by linarith)] at this
    linarith
  · simp
  · have := hc.deriv_le_slope (mem_univ z) (mem_univ z₀) h hd
    rw [slope_def_field, le_div_iff₀ (by linarith)] at this
    linarith

/-- Expected second-period utility `E v(x + y)` is differentiable in `x` with derivative
`E v'(x + y)` when `v'` is continuous and `y` has compact support. -/
theorem hasDerivAt_expected {v : ℝ → ℝ} (hd : Differentiable ℝ v) (hc' : Continuous (deriv v))
    {μ : Measure ℝ} (hμ : IsMoneyLottery univ μ) (x₀ : ℝ) :
    HasDerivAt (fun x => ∫ y, v (x + y) ∂μ) (∫ y, deriv v (x₀ + y) ∂μ) x₀ := by
  have := hμ.1
  obtain ⟨a, b, -, hae⟩ := hμ.ae_mem
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := x₀ - 1 + a) (b := x₀ + 1 + b)).exists_bound_of_continuousOn
    hc'.continuousOn
  have hcv : Continuous v := hd.continuous
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := fun _ => C)
    (F := fun x y => v (x + y)) (F' := fun x y => deriv v (x + y))
    (Metric.ball_mem_nhds x₀ one_pos)
    (Eventually.of_forall fun x => (hμ.integrable (S := univ) (u := fun y => v (x + y))
      (by fun_prop)).aestronglyMeasurable)
    (hμ.integrable (S := univ) (u := fun y => v (x₀ + y)) (by fun_prop))
    (hμ.integrable (S := univ) (u := fun y => deriv v (x₀ + y)) (by fun_prop)).aestronglyMeasurable
    ?_ (integrable_const C) ?_).2
  · filter_upwards [hae] with y hy x hx
    apply hC
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hx
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  · exact Eventually.of_forall fun y x _ => ((hd (x + y)).hasDerivAt.comp_add_const x y)

/-- **Exercise 6.C.9(a)** (MWG, p. 211). Let `x₀` maximize `u(w - x) + v(x)` and `x*` maximize
`u(w - x) + E[v(x + y)]`, with `u, v` concave and differentiable (`v'` continuous). If
`E[v'(x₀ + y)] > v'(x₀)`, then `x* > x₀`. -/
theorem exercise_6_C_9a {u v : ℝ → ℝ} (hu : ConcaveOn ℝ univ u) (hv : ConcaveOn ℝ univ v)
    (hud : Differentiable ℝ u) (hvd : Differentiable ℝ v) (hv' : Continuous (deriv v))
    {μ : Measure ℝ} (hμ : IsMoneyLottery univ μ) {w x₀ xs : ℝ}
    (h₀ : ∀ x, u (w - x) + v x ≤ u (w - x₀) + v x₀)
    (hs : ∀ x, u (w - x) + ∫ y, v (x + y) ∂μ ≤ u (w - xs) + ∫ y, v (xs + y) ∂μ)
    (hprec : deriv v x₀ < ∫ y, deriv v (x₀ + y) ∂μ) : x₀ < xs := by
  have := hμ.1
  have hcv : Continuous v := hvd.continuous
  have hdu (x : ℝ) : HasDerivAt (fun x => u (w - x)) (-deriv u (w - x)) x := by
    exact (hud (w - x)).hasDerivAt.comp_const_sub w x
  -- first-order condition at the certainty optimum
  have hfoc : deriv u (w - x₀) = deriv v x₀ := by
    have hloc : IsLocalMax (fun x => u (w - x) + v x) x₀ := Eventually.of_forall h₀
    have := hloc.hasDerivAt_eq_zero ((hdu x₀).add (hvd x₀).hasDerivAt)
    linarith
  set G := fun x => u (w - x) + ∫ y, v (x + y) ∂μ
  have hGd : HasDerivAt G (-deriv u (w - x₀) + ∫ y, deriv v (x₀ + y) ∂μ) x₀ :=
    (hdu x₀).add (hasDerivAt_expected hvd hv' hμ x₀)
  -- below `x₀`, `G` is strictly smaller than `G x₀`
  have hbelow (x : ℝ) (hx : x < x₀) : G x < G x₀ := by
    have h1 := concave_le_tangent hu (hud (w - x₀)) (w - x)
    have h2 : ∫ y, v (x + y) ∂μ ≤ ∫ y, (v (x₀ + y) + deriv v (x₀ + y) * (x - x₀)) ∂μ :=
      integral_mono (hμ.integrable (S := univ) (u := fun y => v (x + y)) (by fun_prop))
        ((hμ.integrable (S := univ) (u := fun y => v (x₀ + y)) (by fun_prop)).add
          ((hμ.integrable (S := univ) (u := fun y => deriv v (x₀ + y)) (by fun_prop)).mul_const _))
        fun y => by
          have := concave_le_tangent hv (hvd (x₀ + y)) (x + y)
          rw [show x + y - (x₀ + y) = x - x₀ by ring] at this
          exact this
    rw [integral_add (hμ.integrable (S := univ) (u := fun y => v (x₀ + y)) (by fun_prop))
      ((hμ.integrable (S := univ) (u := fun y => deriv v (x₀ + y)) (by fun_prop)).mul_const _),
      integral_mul_const] at h2
    simp only [G]
    rw [show w - x - (w - x₀) = -(x - x₀) by ring] at h1
    nlinarith [mul_pos (sub_pos.mpr hprec) (sub_pos.mpr hx)]
  rcases lt_trichotomy x₀ xs with h | h | h
  · exact h
  · exfalso
    subst h
    have hloc : IsLocalMax G x₀ := Eventually.of_forall hs
    have := hloc.hasDerivAt_eq_zero hGd
    linarith
  · exfalso
    have := hbelow xs h
    linarith [hs x₀]

/-- The coefficient of absolute prudence `-v'''(x)/v''(x)` (MWG, Exercise 6.C.9(b), p. 211). -/
noncomputable def prudence (v : ℝ → ℝ) (x : ℝ) : ℝ :=
  -deriv (deriv (deriv v)) x / deriv (deriv v) x

/-- Absolute prudence of `v` is the Arrow-Pratt coefficient of `-v'`. -/
theorem prudence_eq_arrowPratt (v : ℝ → ℝ) (x : ℝ) :
    prudence v x = arrowPratt (fun t => -deriv v t) x := by
  have h1 : deriv (fun t => -deriv v t) = fun t => -deriv (deriv v) t :=
    funext fun t => deriv.fun_neg
  have h2 : deriv (fun t => -deriv (deriv v) t) x = -deriv (deriv (deriv v)) x := deriv.fun_neg
  unfold prudence arrowPratt
  rw [h1, h2]
  by_cases h : deriv (deriv v) x = 0
  · simp [h]
  · field_simp

/-- **Exercise 6.C.9(b)** (MWG, p. 211). If the absolute prudence of `v₁` is nowhere larger than
that of `v₂`, then `E[v₁'(x₀ + y)] > v₁'(x₀)` implies `E[v₂'(x₀ + y)] > v₂'(x₀)` (stated for
the distribution `F` of final wealth `x₀ + y`). Here `v_i'` is twice continuously
differentiable with `v_i'' < 0`. -/
theorem exercise_6_C_9b {v₁ v₂ : ℝ → ℝ} (d1 : ∀ x, ContDiffAt ℝ 2 (fun t => -deriv v₁ t) x)
    (d2 : ∀ x, ContDiffAt ℝ 2 (fun t => -deriv v₂ t) x) (n1 : ∀ x, deriv (deriv v₁) x < 0)
    (n2 : ∀ x, deriv (deriv v₂) x < 0) (hP : ∀ x, prudence v₁ x ≤ prudence v₂ x)
    {ν : Measure ℝ} (hν : IsMoneyLottery univ ν) (x₀ : ℝ)
    (h1 : deriv v₁ x₀ < ∫ t, deriv v₁ t ∂ν) : deriv v₂ x₀ < ∫ t, deriv v₂ t ∂ν := by
  have hpos (v : ℝ → ℝ) (n : ∀ x, deriv (deriv v) x < 0) (x : ℝ) (_ : x ∈ univ) :
      0 < deriv (fun t => -deriv v t) x := by
    rw [deriv.fun_neg]; linarith [n x]
  have T := proposition_6_C_2 convex_univ isOpen_univ univ_nonempty (fun x _ => d1 x)
    (fun x _ => d2 x) (hpos v₁ n1) (hpos v₂ n2)
  have hV : MoreRiskAverseV univ (fun t => -deriv v₁ t) (fun t => -deriv v₂ t) :=
    (T.out 1 5).mp fun x _ => by rw [← prudence_eq_arrowPratt, ← prudence_eq_arrowPratt]; exact hP x
  by_contra hcon
  have hle : -deriv v₂ x₀ ≤ ∫ t, -deriv v₂ t ∂ν := by
    rw [integral_neg]; linarith [not_lt.mp hcon]
  have := hV ν x₀ hν (mem_univ _) hle
  rw [integral_neg] at this
  linarith

/-- **Exercise 6.C.9(c)** (MWG, p. 211), corrected. If `v''' > 0` and `E[y] = 0` with `y` not
identically zero, then `E[v'(x + y)] > v'(x)` for every `x`. -/
theorem exercise_6_C_9c {v : ℝ → ℝ} (hd2 : Differentiable ℝ (deriv v))
    (h3 : ∀ x, 0 < deriv (deriv (deriv v)) x)
    {μ : Measure ℝ} (hμ : IsMoneyLottery univ μ) (hmean : ∫ y, y ∂μ = 0)
    (hnd : μ ≠ Measure.dirac 0) (x : ℝ) : deriv v x < ∫ y, deriv v (x + y) ∂μ := by
  have := hμ.1
  have hsc : StrictConvexOn ℝ univ (deriv v) :=
    (strictMono_of_deriv_pos h3).strictConvexOn_univ_of_deriv hd2.continuous
  have hcont : Continuous (deriv v) := hd2.continuous
  have hj := hsc.ae_eq_const_or_map_average_lt hcont.continuousOn isClosed_univ
    (Eventually.of_forall fun y => mem_univ (x + y))
    (hμ.integrable (S := univ) (u := fun y => x + y) (by fun_prop))
    (hμ.integrable (S := univ) (u := fun y => deriv v (x + y)) (by fun_prop))
  simp only [average_eq_integral] at hj
  rw [integral_add (integrable_const x) hμ.integrable_id, hmean, integral_const] at hj
  simp only [probReal_univ, one_smul, add_zero] at hj
  rcases hj with hconst | hlt
  · exfalso
    apply hnd
    apply eq_dirac_of_ae_eq_const
    filter_upwards [hconst] with y hy
    simp only [Function.const_apply] at hy
    linarith
  · exact hlt

/-- **Exercise 6.C.9(c)**: the strict inequality fails for the degenerate `y ≡ 0`. -/
theorem exercise_6_C_9c_degenerate (v : ℝ → ℝ) (x : ℝ) :
    ∫ y, deriv v (x + y) ∂(Measure.dirac (0 : ℝ)) = deriv v x := by
  rw [integral_dirac, add_zero]

/-- **Exercise 6.C.9(d)** (MWG, p. 211), corrected. If `r_A = -v''/v'` is (weakly) decreasing,
`v' > 0` and `v'' < 0`, then `-v'''/v'' ≥ -v''/v'` and hence `v''' > 0`; the first inequality is
strict where `r_A' < 0`. -/
theorem exercise_6_C_9d {v : ℝ → ℝ} (hd1 : Differentiable ℝ (deriv v))
    (hd2 : Differentiable ℝ (deriv (deriv v))) (hp : ∀ x, 0 < deriv v x)
    (hn : ∀ x, deriv (deriv v) x < 0) (x : ℝ) :
    (deriv (arrowPratt v) x ≤ 0 → arrowPratt v x ≤ prudence v x ∧
      0 < deriv (deriv (deriv v)) x) ∧
    (deriv (arrowPratt v) x < 0 → arrowPratt v x < prudence v x) := by
  have hr : HasDerivAt (arrowPratt v)
      (-(deriv (deriv (deriv v)) x * deriv v x - deriv (deriv v) x * deriv (deriv v) x) /
        deriv v x ^ 2) x := by
    have := ((hd2 x).hasDerivAt.neg).div (hd1 x).hasDerivAt (hp x).ne'
    convert this using 1
    · funext t; simp only [arrowPratt, Pi.div_apply, Pi.neg_apply]
    · rw [Pi.neg_apply]; ring
  rw [hr.deriv]
  set A := deriv v x
  set B := deriv (deriv v) x
  set C := deriv (deriv (deriv v)) x
  have hA : 0 < A := hp x
  have hB : B < 0 := hn x
  have hB2 : 0 < B * B := mul_pos_of_neg_of_neg hB hB
  have hA2 : 0 < A ^ 2 := by positivity
  have hgoal : arrowPratt v x = -B / A := rfl
  have hpr : prudence v x = C / -B := by
    change -C / B = C / -B
    rw [neg_div, div_neg]
  rw [hgoal, hpr]
  constructor
  · intro h
    have key : B * B ≤ C * A := by
      by_contra hk
      have : 0 < -(C * A - B * B) / A ^ 2 := div_pos (by linarith) hA2
      linarith
    refine ⟨?_, ?_⟩
    · rw [div_le_div_iff₀ hA (by linarith)]; nlinarith
    · by_contra hc
      have : C * A ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hc) hA.le
      linarith
  · intro h
    have key : B * B < C * A := by
      by_contra hk
      have : 0 ≤ -(C * A - B * B) / A ^ 2 := div_nonneg (by linarith) hA2.le
      linarith
    rw [div_lt_div_iff₀ hA (by linarith)]; nlinarith

/-- **Exercise 6.C.9(d)**: with constant absolute risk aversion (`v = -e^{-x}`) the two sides
are equal, so the printed strict inequality fails under weakly decreasing `r_A`. -/
theorem exercise_6_C_9d_cara (x : ℝ) :
    prudence (Kreps.UtilityForMoney.ExponentialUtility 1) x =
      arrowPratt (Kreps.UtilityForMoney.ExponentialUtility 1) x := by
  have h1 : deriv (Kreps.UtilityForMoney.ExponentialUtility 1) = fun t => Real.exp (-t) := by
    funext t
    simpa using (Kreps.UtilityForMoney.exponentialUtility_hasDerivAt 1 t).deriv
  have h2 : deriv (fun t => Real.exp (-t)) = fun t => -Real.exp (-t) := by
    funext t
    simpa using ((hasDerivAt_neg t).exp).deriv
  have h3 : deriv (fun t => -Real.exp (-t)) = fun t => Real.exp (-t) := by
    funext t; rw [deriv.fun_neg, h2]; ring
  unfold prudence arrowPratt
  rw [h1, h2, h3]
  field_simp

/-- **Exercise 6.C.20** (MWG, p. 213). Let `c(ε)` be the certainty equivalent of the gamble
paying `x + ε` or `x - ε` with probability `1/2` each (`u(c(ε)) = (u(x+ε) + u(x-ε))/2` near
`ε = 0`), twice continuously differentiable at `0`. For `u` twice continuously differentiable
and strictly increasing with `u'(x) > 0`, `c''(ε) → -r_A(x)` as `ε → 0`. -/
theorem exercise_6_C_20 {u c : ℝ → ℝ} {x : ℝ} (hu : ContDiff ℝ 2 u) (hi : StrictMono u)
    (hp : 0 < deriv u x) (hc : ContDiffAt ℝ 2 c 0)
    (he : ∀ᶠ ε in 𝓝 0, u (c ε) = (u (x + ε) + u (x - ε)) / 2) :
    Tendsto (fun ε => deriv (deriv c) ε) (𝓝 0) (𝓝 (-arrowPratt u x)) := by
  have hc0 : c 0 = x := by
    have h0 := he.self_of_nhds
    simp only [add_zero, sub_zero] at h0
    have : u (c 0) = u x := by rw [h0]; ring
    exact hi.injective this
  have hu1 : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hu2 : Differentiable ℝ (deriv u) := hu.differentiable_deriv_two
  have hc1 : ContDiffAt ℝ 1 (deriv c) 0 := hc.derivWithin (m := 1) (by norm_num)
  have hc2 : ContinuousAt (deriv (deriv c)) 0 :=
    (hc1.derivWithin (m := 0) (by norm_num)).continuousAt
  have hcd : ∀ᶠ ε in 𝓝 (0 : ℝ), DifferentiableAt ℝ c ε :=
    (hc.eventually (by simp)).mono fun ε h => h.differentiableAt (by norm_num)
  set S := fun ε : ℝ => (u (x + ε) + u (x - ε)) / 2
  have hS1 : deriv S = fun ε => (deriv u (x + ε) - deriv u (x - ε)) / 2 := by
    funext ε
    have h1 := (hu1 (x + ε)).hasDerivAt.comp_const_add x ε
    have h2 := (hu1 (x - ε)).hasDerivAt.comp_const_sub x ε
    exact ((h1.add h2).div_const 2).deriv.trans (by ring)
  have hS2 : deriv (deriv S) 0 = deriv (deriv u) x := by
    rw [hS1]
    have h1 := (hu2 (x + 0)).hasDerivAt.comp_const_add x 0
    have h2 := (hu2 (x - 0)).hasDerivAt.comp_const_sub x 0
    have h3 : HasDerivAt (fun ε => (deriv u (x + ε) - deriv u (x - ε)) / 2)
        ((deriv (deriv u) (x + 0) - -deriv (deriv u) (x - 0)) / 2) 0 := (h1.sub h2).div_const 2
    rw [h3.deriv]
    simp only [add_zero, sub_zero]; ring
  -- derivatives of `u ∘ c` near `0`
  have hg1 : ∀ᶠ ε in 𝓝 (0 : ℝ), deriv (fun e => u (c e)) ε = deriv u (c ε) * deriv c ε := by
    filter_upwards [hcd] with ε hε
    exact ((hu1 (c ε)).hasDerivAt.comp ε hε.hasDerivAt).deriv
  have hgS : deriv (fun e => u (c e)) =ᶠ[𝓝 0] deriv S :=
    Filter.EventuallyEq.deriv (show (fun e => u (c e)) =ᶠ[𝓝 0] S from he)
  have hfirst : deriv u x * deriv c 0 = 0 := by
    have := hgS.self_of_nhds
    rw [hg1.self_of_nhds, hc0, hS1] at this
    simpa using this
  have hc'0 : deriv c 0 = 0 := by
    rcases mul_eq_zero.mp hfirst with h | h
    · linarith
    · exact h
  have hsecond : deriv (fun ε => deriv u (c ε) * deriv c ε) 0 = deriv (deriv u) x * deriv c 0 *
      deriv c 0 + deriv u x * deriv (deriv c) 0 := by
    have hcd0 : DifferentiableAt ℝ c 0 := hc.differentiableAt (by norm_num)
    have h1 : HasDerivAt (fun ε => deriv u (c ε)) (deriv (deriv u) (c 0) * deriv c 0) 0 :=
      (hu2 (c 0)).hasDerivAt.comp 0 hcd0.hasDerivAt
    have h2 : HasDerivAt (deriv c) (deriv (deriv c) 0) 0 :=
      (hc1.differentiableAt (by norm_num)).hasDerivAt
    have h3 : HasDerivAt (fun ε => deriv u (c ε) * deriv c ε)
        (deriv (deriv u) (c 0) * deriv c 0 * deriv c 0 + deriv u (c 0) * deriv (deriv c) 0) 0 :=
      h1.mul h2
    rw [h3.deriv, hc0]
  have hval : deriv (deriv c) 0 = -arrowPratt u x := by
    have hcomb : (fun ε => deriv u (c ε) * deriv c ε) =ᶠ[𝓝 0] deriv S :=
      (show deriv (fun e => u (c e)) =ᶠ[𝓝 0] fun ε => deriv u (c ε) * deriv c ε from
        hg1).symm.trans hgS
    have h := hcomb.deriv_eq
    rw [hsecond, hS2, hc'0] at h
    unfold arrowPratt
    field_simp
    linarith
  rw [← hval]
  exact hc2.tendsto

/-- A concrete instance of Exercise 6.C.20: for `u(x) = -e^{-x}`, `c(ε) = x - ln cosh ε` is the
certainty equivalent of `x ± ε`, twice continuously differentiable. -/
theorem exercise_6_C_20_instance (x : ℝ) :
    ContDiffAt ℝ 2 (fun ε => x - Real.log (Real.cosh ε)) 0 ∧
      ∀ ε, Kreps.UtilityForMoney.ExponentialUtility 1 (x - Real.log (Real.cosh ε)) =
        (Kreps.UtilityForMoney.ExponentialUtility 1 (x + ε) +
          Kreps.UtilityForMoney.ExponentialUtility 1 (x - ε)) / 2 := by
  constructor
  · apply contDiffAt_const.sub
    exact (Real.contDiffAt_log.mpr (Real.cosh_pos 0).ne').comp 0 Real.contDiff_cosh.contDiffAt
  · intro ε
    simp only [Kreps.UtilityForMoney.ExponentialUtility, neg_mul, one_mul]
    rw [show -(x - Real.log (Real.cosh ε)) = -x + Real.log (Real.cosh ε) by ring, Real.exp_add,
      Real.exp_log (Real.cosh_pos ε), Real.cosh_eq, show -(x + ε) = -x + -ε by ring,
      show -(x - ε) = -x + ε by ring, Real.exp_add, Real.exp_add]
    ring

end MWG.ChoiceUnderUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercise 6.C.15: a riskless and a risky asset

MWG, p. 212. Wealth `1` is split between a riskless asset paying `1` and a risky asset paying
`a` with probability `π` and `b` with probability `1 - π`; with `x₂` in the risky asset, final
wealth is `1 + x₂(a - 1)` or `1 + x₂(b - 1)`. Parts (a)-(b) give necessary conditions for
positive demands, (c) the first-order condition, (d) `dx₁/da ≤ 0` (indeed `< 0`) when `a < 1`,
and (e)-(f) the conjecture `dx₁/dπ ≥ 0` (indeed `> 0`) and its proof, by implicit
differentiation of the first-order condition along a differentiable demand.
-/

namespace MWG.ChoiceUnderUncertainty

open Filter Topology Set

/-- Expected utility from holding `x₂` of the risky asset (and `1 - x₂` of the riskless one). -/
def twoAssetEU (u : ℝ → ℝ) (π a b x₂ : ℝ) : ℝ :=
  π * u (1 + x₂ * (a - 1)) + (1 - π) * u (1 + x₂ * (b - 1))

/-- **Exercise 6.C.15(a)** (MWG, p. 212). If the demand for the riskless asset is strictly
positive (`x₂ < 1`) at an optimum of a strictly increasing utility, then `a < 1` or `b < 1`
(or both returns equal `1`). -/
theorem exercise_6_C_15a {u : ℝ → ℝ} (hi : StrictMono u) {π a b x₂ : ℝ} (hπ : π ∈ Ioo 0 1)
    (hx : x₂ ∈ Ico 0 1) (hopt : ∀ y ∈ Icc (0 : ℝ) 1, twoAssetEU u π a b y ≤ twoAssetEU u π a b x₂) :
    a < 1 ∨ b < 1 ∨ (a = 1 ∧ b = 1) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨ha, hb, hab⟩ := hcon
  have h1 := hopt 1 ⟨zero_le_one, le_rfl⟩
  unfold twoAssetEU at h1
  have hx1 : 0 < 1 - x₂ := by linarith [hx.2]
  have ea : u (1 + x₂ * (a - 1)) ≤ u (1 + 1 * (a - 1)) := hi.monotone (by nlinarith)
  have eb : u (1 + x₂ * (b - 1)) ≤ u (1 + 1 * (b - 1)) := hi.monotone (by nlinarith)
  rcases lt_or_eq_of_le ha with ha' | ha'
  · have : u (1 + x₂ * (a - 1)) < u (1 + 1 * (a - 1)) := hi (by nlinarith)
    nlinarith [hπ.1, hπ.2]
  · have hb' : 1 < b := lt_of_le_of_ne hb (fun h => hab ha'.symm h.symm)
    have : u (1 + x₂ * (b - 1)) < u (1 + 1 * (b - 1)) := hi (by nlinarith)
    nlinarith [hπ.1, hπ.2]

/-- **Exercise 6.C.15(b)** (MWG, p. 212). For a strictly risk-averse, increasing utility and
`a ≠ b`, a strictly positive demand for the risky asset requires `πa + (1 - π)b > 1`. -/
theorem exercise_6_C_15b {u : ℝ → ℝ} (hc : StrictConcaveOn ℝ univ u) (hm : Monotone u)
    {π a b x₂ : ℝ} (hπ : π ∈ Ioo 0 1) (hab : a ≠ b) (hx : x₂ ∈ Ioc 0 1)
    (hopt : ∀ y ∈ Icc (0 : ℝ) 1, twoAssetEU u π a b y ≤ twoAssetEU u π a b x₂) :
    1 < π * a + (1 - π) * b := by
  by_contra hle
  have hle : π * a + (1 - π) * b ≤ 1 := not_lt.mp hle
  have hne : 1 + x₂ * (a - 1) ≠ 1 + x₂ * (b - 1) := by
    intro h; apply hab
    have : x₂ * (a - b) = 0 := by linarith
    rcases mul_eq_zero.mp this with h0 | h0
    · linarith [hx.1]
    · linarith
  have hs := hc.2 (mem_univ _) (mem_univ _) hne hπ.1 (show 0 < 1 - π by linarith [hπ.2])
    (by ring)
  simp only [smul_eq_mul] at hs
  have hmean : π * (1 + x₂ * (a - 1)) + (1 - π) * (1 + x₂ * (b - 1)) ≤ 1 := by nlinarith [hx.1]
  have := hopt 0 ⟨le_rfl, zero_le_one⟩
  unfold twoAssetEU at this
  simp only [zero_mul, add_zero] at this
  have hu1 := hm hmean
  have h1 : π * u 1 + (1 - π) * u 1 = u 1 := by ring
  linarith

/-- The marginal expected utility `φ(x₂) = π(a-1)u'(1 + x₂(a-1)) + (1-π)(b-1)u'(1 + x₂(b-1))`. -/
noncomputable def twoAssetFOC (u : ℝ → ℝ) (π a b x₂ : ℝ) : ℝ :=
  π * (a - 1) * deriv u (1 + x₂ * (a - 1)) + (1 - π) * (b - 1) * deriv u (1 + x₂ * (b - 1))

/-- **Exercise 6.C.15(c)** (MWG, p. 212). At an interior optimum `0 < x₂ < 1` the first-order
condition `φ(x₂) = 0` holds. -/
theorem exercise_6_C_15c {u : ℝ → ℝ} (hd : Differentiable ℝ u) {π a b x₂ : ℝ}
    (hx : x₂ ∈ Ioo 0 1)
    (hopt : ∀ y ∈ Icc (0 : ℝ) 1, twoAssetEU u π a b y ≤ twoAssetEU u π a b x₂) :
    twoAssetFOC u π a b x₂ = 0 := by
  have h1 : HasDerivAt (fun y => u (1 + y * (a - 1))) (deriv u (1 + x₂ * (a - 1)) * (a - 1)) x₂ :=
    (hd _).hasDerivAt.comp x₂ (by simpa using ((hasDerivAt_id x₂).mul_const (a - 1)).const_add 1)
  have h2 : HasDerivAt (fun y => u (1 + y * (b - 1))) (deriv u (1 + x₂ * (b - 1)) * (b - 1)) x₂ :=
    (hd _).hasDerivAt.comp x₂ (by simpa using ((hasDerivAt_id x₂).mul_const (b - 1)).const_add 1)
  have hD : HasDerivAt (twoAssetEU u π a b) (twoAssetFOC u π a b x₂) x₂ := by
    convert (h1.const_mul π).add (h2.const_mul (1 - π)) using 1
    · funext y; rfl
    · unfold twoAssetFOC; ring
  have hloc : IsLocalMax (twoAssetEU u π a b) x₂ := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy using hopt y ⟨hy.1.le, hy.2.le⟩
  exact hloc.hasDerivAt_eq_zero hD

/-- The derivative of the first-order condition along a demand `x₂ = X(a)`. -/
theorem foc_along_a {u : ℝ → ℝ} (hd2 : Differentiable ℝ (deriv u))
    (π b : ℝ) {X : ℝ → ℝ} {X' a₀ : ℝ} (hX : HasDerivAt X X' a₀) :
    HasDerivAt (fun a => twoAssetFOC u π a b (X a))
      (X' * (π * (a₀ - 1) ^ 2 * deriv (deriv u) (1 + X a₀ * (a₀ - 1)) +
          (1 - π) * (b - 1) ^ 2 * deriv (deriv u) (1 + X a₀ * (b - 1))) +
        (π * deriv u (1 + X a₀ * (a₀ - 1)) +
          π * (a₀ - 1) * X a₀ * deriv (deriv u) (1 + X a₀ * (a₀ - 1)))) a₀ := by
  have hWa : HasDerivAt (fun a => 1 + X a * (a - 1)) (X' * (a₀ - 1) + X a₀ * 1) a₀ := by
    simpa using (hX.mul ((hasDerivAt_id a₀).sub_const 1)).const_add 1
  have hWb : HasDerivAt (fun a => 1 + X a * (b - 1)) (X' * (b - 1)) a₀ := by
    simpa using (hX.mul_const (b - 1)).const_add 1
  have t1 := ((hasDerivAt_id a₀).sub_const 1).const_mul π |>.mul
    ((hd2 _).hasDerivAt.comp a₀ hWa)
  have t2 := ((hd2 _).hasDerivAt.comp a₀ hWb).const_mul ((1 - π) * (b - 1))
  unfold twoAssetFOC
  convert t1.add t2 using 1
  · funext a; simp only [Pi.add_apply, Pi.mul_apply, Function.comp_apply, id]
  · simp only [Function.comp_apply, id]; ring

/-- **Exercise 6.C.15(d)** (MWG, p. 212). With `a < 1`, implicit differentiation of the
first-order condition along a differentiable demand `x₂(a) ≥ 0` (for a strictly increasing,
strictly concave `u`) gives `dx₂/da > 0`, i.e. `dx₁/da = -dx₂/da < 0`. -/
theorem exercise_6_C_15d {u : ℝ → ℝ} (hd2 : Differentiable ℝ (deriv u))
    (hpos : ∀ t, 0 < deriv u t) (hneg : ∀ t, deriv (deriv u) t < 0) {π b a₀ : ℝ}
    (hπ : π ∈ Ioo 0 1) (ha : a₀ < 1) {X : ℝ → ℝ} {X' : ℝ} (hX : HasDerivAt X X' a₀)
    (hX0 : 0 ≤ X a₀) (hfoc : ∀ᶠ a in 𝓝 a₀, twoAssetFOC u π a b (X a) = 0) :
    -X' < 0 := by
  have hD := foc_along_a hd2 π b hX
  have hzero : HasDerivAt (fun a => twoAssetFOC u π a b (X a)) 0 a₀ :=
    (hasDerivAt_const a₀ (0 : ℝ)).congr_of_eventuallyEq hfoc
  have he := hD.unique hzero
  set Pa := deriv (deriv u) (1 + X a₀ * (a₀ - 1))
  set Pb := deriv (deriv u) (1 + X a₀ * (b - 1))
  have hPa : Pa < 0 := hneg _
  have hPb : Pb < 0 := hneg _
  have hφx : π * (a₀ - 1) ^ 2 * Pa + (1 - π) * (b - 1) ^ 2 * Pb < 0 := by
    have h1 : 0 < π * (a₀ - 1) ^ 2 := mul_pos hπ.1 (by nlinarith)
    have h2 : 0 ≤ (1 - π) * (b - 1) ^ 2 := mul_nonneg (by linarith [hπ.2]) (sq_nonneg _)
    nlinarith [mul_nonpos_of_nonneg_of_nonpos h2 hPb.le]
  have hφa : 0 < π * deriv u (1 + X a₀ * (a₀ - 1)) + π * (a₀ - 1) * X a₀ * Pa := by
    have h1 := mul_pos hπ.1 (hpos (1 + X a₀ * (a₀ - 1)))
    have h2 : 0 ≤ π * (a₀ - 1) * X a₀ * Pa := by
      have : π * (a₀ - 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hπ.1.le (by linarith)
      have : π * (a₀ - 1) * X a₀ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg this hX0
      nlinarith
    linarith
  nlinarith

/-- The derivative of the first-order condition along a demand `x₂ = X(π)`. -/
theorem foc_along_π {u : ℝ → ℝ} (hd2 : Differentiable ℝ (deriv u)) (a b : ℝ) {X : ℝ → ℝ}
    {X' π₀ : ℝ} (hX : HasDerivAt X X' π₀) :
    HasDerivAt (fun π => twoAssetFOC u π a b (X π))
      (X' * (π₀ * (a - 1) ^ 2 * deriv (deriv u) (1 + X π₀ * (a - 1)) +
          (1 - π₀) * (b - 1) ^ 2 * deriv (deriv u) (1 + X π₀ * (b - 1))) +
        ((a - 1) * deriv u (1 + X π₀ * (a - 1)) - (b - 1) * deriv u (1 + X π₀ * (b - 1)))) π₀ := by
  have hWa : HasDerivAt (fun π => 1 + X π * (a - 1)) (X' * (a - 1)) π₀ := by
    simpa using (hX.mul_const (a - 1)).const_add 1
  have hWb : HasDerivAt (fun π => 1 + X π * (b - 1)) (X' * (b - 1)) π₀ := by
    simpa using (hX.mul_const (b - 1)).const_add 1
  have ga := (hd2 _).hasDerivAt.comp π₀ hWa
  have gb := (hd2 _).hasDerivAt.comp π₀ hWb
  have t1 := ((hasDerivAt_id π₀).mul_const (a - 1)).mul ga
  have t2 := (((hasDerivAt_const π₀ (1 : ℝ)).sub (hasDerivAt_id π₀)).mul_const (b - 1)).mul gb
  unfold twoAssetFOC
  convert t1.add t2 using 1
  · funext π; simp only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply, Function.comp_apply, id]
  · simp only [Function.comp_apply, id, Pi.sub_apply]; ring

/-- **Exercise 6.C.15(e)-(f)** (MWG, p. 212). Conjecture and proof: when `a < 1 < b`, a higher
probability `π` of the low return lowers the demand for the risky asset, `dx₂/dπ < 0`, so
`dx₁/dπ > 0` (by implicit differentiation of the first-order condition). -/
theorem exercise_6_C_15f {u : ℝ → ℝ} (hd2 : Differentiable ℝ (deriv u))
    (hpos : ∀ t, 0 < deriv u t) (hneg : ∀ t, deriv (deriv u) t < 0) {a b π₀ : ℝ}
    (hπ : π₀ ∈ Ioo 0 1) (ha : a < 1) (hb : 1 < b) {X : ℝ → ℝ} {X' : ℝ}
    (hX : HasDerivAt X X' π₀) (hfoc : ∀ᶠ π in 𝓝 π₀, twoAssetFOC u π a b (X π) = 0) :
    0 < -X' := by
  have hD := foc_along_π hd2 a b hX
  have hzero : HasDerivAt (fun π => twoAssetFOC u π a b (X π)) 0 π₀ :=
    (hasDerivAt_const π₀ (0 : ℝ)).congr_of_eventuallyEq hfoc
  have he := hD.unique hzero
  have hPa := hneg (1 + X π₀ * (a - 1))
  have hPb := hneg (1 + X π₀ * (b - 1))
  have hφx : π₀ * (a - 1) ^ 2 * deriv (deriv u) (1 + X π₀ * (a - 1)) +
      (1 - π₀) * (b - 1) ^ 2 * deriv (deriv u) (1 + X π₀ * (b - 1)) < 0 := by
    have h1 : 0 < π₀ * (a - 1) ^ 2 := mul_pos hπ.1 (by nlinarith)
    have h2 : 0 < (1 - π₀) * (b - 1) ^ 2 := mul_pos (by linarith [hπ.2]) (by nlinarith)
    nlinarith
  have hφπ : (a - 1) * deriv u (1 + X π₀ * (a - 1)) -
      (b - 1) * deriv u (1 + X π₀ * (b - 1)) < 0 := by
    have h1 := hpos (1 + X π₀ * (a - 1))
    have h2 := hpos (1 + X π₀ * (b - 1))
    nlinarith
  nlinarith

end MWG.ChoiceUnderUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercises 6.C.17 (myopic portfolio choice) and 6.C.19 (CARA and normal returns)

MWG, pp. 212-213.

Exercise 6.C.17: with returns taking finitely many positive values, safe gross return `R > 0`,
and the fraction `α ∈ [0,1]` in the risky asset, wealth evolves as
`w_t = ((1 - α_{t-1})R + α_{t-1}x_t) w_{t-1}`. Under constant relative risk aversion
(`u(w) = w^{1-ρ}/(1-ρ)`, `ρ ≠ 1`, or `u = ln`) the period-1 problem at any wealth and the
period-0 problem (against the optimal period-1 value) have exactly the optimal fractions of
the one-period problem, so `α₀ = α₁` is optimal. Under constant absolute risk aversion the
optimal amount invested does not depend on wealth, so the optimal fraction does, and
`α₀ = α₁` fails whenever `w₁ ≠ w₀`.

Exercise 6.C.19: jointly normal returns are given through their moment generating function
`E[e^{t·z}] = e^{t·μ + t'Vt/2}` (which characterizes the multivariate normal law; a concrete
instance with Mathlib's `gaussianReal` is proved). The demand for the risky assets is
`α* = V⁻¹(μ - r1)/a`, the unique maximizer, and `w - ∑ α*` is held in the riskless asset.
-/

namespace MWG.ChoiceUnderUncertainty

open MeasureTheory ProbabilityTheory Filter Topology Set

variable {m : ℕ}

/-- The gross portfolio return `(1 - α)R + αx_i`. -/
def grossReturn (R : ℝ) (x : Fin m → ℝ) (α : ℝ) (i : Fin m) : ℝ := (1 - α) * R + α * x i

theorem grossReturn_pos {R : ℝ} (hR : 0 < R) {x : Fin m → ℝ} (hx : ∀ i, 0 < x i) {α : ℝ}
    (hα : α ∈ Icc (0 : ℝ) 1) (i : Fin m) : 0 < grossReturn R x α i := by
  unfold grossReturn
  rcases eq_or_lt_of_le hα.2 with h | h
  · rw [h]; simpa using hx i
  · have := hx i; nlinarith [hα.1]

/-- The CRRA utility `w^{1-ρ}/(1-ρ)`. -/
noncomputable def crra (ρ w : ℝ) : ℝ := w ^ (1 - ρ) / (1 - ρ)

/-- Expected CRRA utility of investing the fraction `α` of wealth `w`. -/
noncomputable def crraObjective (ρ : ℝ) (q : Fin m → ℝ) (R : ℝ) (x : Fin m → ℝ) (w α : ℝ) :
    ℝ :=
  ∑ i, q i * crra ρ (w * grossReturn R x α i)

/-- Homogeneity: `E u(w G) = w^{1-ρ} E u(G)`. -/
theorem crraObjective_homog {ρ : ℝ} (q : Fin m → ℝ) {R : ℝ} (hR : 0 < R) {x : Fin m → ℝ}
    (hx : ∀ i, 0 < x i) {w : ℝ} (hw : 0 < w) {α : ℝ} (hα : α ∈ Icc (0 : ℝ) 1) :
    crraObjective ρ q R x w α = w ^ (1 - ρ) * crraObjective ρ q R x 1 α := by
  unfold crraObjective crra
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.mul_rpow hw.le (grossReturn_pos hR hx hα i).le, one_mul]
  ring

/-- Scaling an objective by a positive constant preserves its maximizers. -/
theorem isMaxOn_const_mul_iff {f g : ℝ → ℝ} {S : Set ℝ} {c : ℝ} (hc : 0 < c)
    (h : ∀ β ∈ S, f β = c * g β) {α : ℝ} (hα : α ∈ S) : IsMaxOn f S α ↔ IsMaxOn g S α := by
  constructor
  · intro hm β hβ
    have := hm hβ
    simp only [mem_ofPred_eq, h β hβ, h α hα] at this
    exact le_of_mul_le_mul_left this hc
  · intro hm β hβ
    have := hm hβ
    simp only [mem_ofPred_eq] at this ⊢
    rw [h β hβ, h α hα]
    exact mul_le_mul_of_nonneg_left this hc.le

/-- **Exercise 6.C.17** (MWG, p. 212), period 1. Under CRRA the optimal fractions at any wealth
`w₁ > 0` are those of the one-period problem at unit wealth. -/
theorem exercise_6_C_17_period1 {ρ : ℝ} (q : Fin m → ℝ) {R : ℝ} (hR : 0 < R) {x : Fin m → ℝ}
    (hx : ∀ i, 0 < x i) {w : ℝ} (hw : 0 < w) {α : ℝ} (hα : α ∈ Icc (0 : ℝ) 1) :
    IsMaxOn (crraObjective ρ q R x w) (Icc 0 1) α ↔
      IsMaxOn (crraObjective ρ q R x 1) (Icc 0 1) α :=
  isMaxOn_const_mul_iff (Real.rpow_pos_of_pos hw _)
    (fun _ hβ => crraObjective_homog q hR hx hw hβ) hα

/-- The one-period CRRA objective is continuous on `[0, 1]`. -/
theorem crraObjective_continuousOn (ρ : ℝ) (q : Fin m → ℝ) {R : ℝ} (hR : 0 < R)
    {x : Fin m → ℝ} (hx : ∀ i, 0 < x i) : ContinuousOn (crraObjective ρ q R x 1) (Icc 0 1) := by
  unfold crraObjective crra
  apply continuousOn_finsetSum
  intro i _
  apply ContinuousOn.mul continuousOn_const
  apply ContinuousOn.div_const
  apply ContinuousOn.rpow_const (by unfold grossReturn; fun_prop)
  intro α hα
  left
  rw [one_mul]
  exact (grossReturn_pos hR hx hα i).ne'

/-- The optimal period-1 value `V₁(w) = max_α E u(w G_α)`. -/
noncomputable def crraValue (ρ : ℝ) (q : Fin m → ℝ) (R : ℝ) (x : Fin m → ℝ) (w : ℝ) : ℝ :=
  sSup (crraObjective ρ q R x w '' Icc 0 1)

/-- **Exercise 6.C.17** (MWG, p. 212), period 0. Under CRRA (`ρ ≠ 1`), with probabilities
`q_i ≥ 0` summing to one, the fraction `α₀` maximizes the period-0 objective
`E[V₁((1 - α₀)R + α₀x₁) w₀]` iff it maximizes the one-period problem; together with
`exercise_6_C_17_period1`, the individual optimally sets `α₀ = α₁`. -/
theorem exercise_6_C_17_period0 {ρ : ℝ} (hρ : ρ ≠ 1) {q : Fin m → ℝ} (hq : ∀ i, 0 ≤ q i)
    (hq1 : ∑ i, q i = 1) {R : ℝ} (hR : 0 < R) {x : Fin m → ℝ} (hx : ∀ i, 0 < x i) {w₀ : ℝ}
    (hw₀ : 0 < w₀) {α : ℝ} (hα : α ∈ Icc (0 : ℝ) 1) :
    IsMaxOn (fun a => ∑ i, q i * crraValue ρ q R x (w₀ * grossReturn R x a i)) (Icc 0 1) α ↔
      IsMaxOn (crraObjective ρ q R x 1) (Icc 0 1) α := by
  have h1ρ : (1 : ℝ) - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ)
  obtain ⟨αs, hαs, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨0, le_rfl, zero_le_one⟩
    (crraObjective_continuousOn ρ q hR hx)
  set J := crraObjective ρ q R x 1
  -- `V₁(w) = w^{1-ρ} J(αs)`
  have hV (w : ℝ) (hw : 0 < w) : crraValue ρ q R x w = w ^ (1 - ρ) * J αs := by
    apply IsGreatest.csSup_eq
    refine ⟨⟨αs, hαs, crraObjective_homog q hR hx hw hαs⟩, ?_⟩
    rintro _ ⟨β, hβ, rfl⟩
    rw [crraObjective_homog q hR hx hw hβ]
    exact mul_le_mul_of_nonneg_left (hmax hβ) (Real.rpow_nonneg hw.le _)
  -- `(1 - ρ) J(β) > 0`
  have hpos (β : ℝ) (hβ : β ∈ Icc (0 : ℝ) 1) : 0 < (1 - ρ) * J β := by
    simp only [J, crraObjective, crra, one_mul, Finset.mul_sum]
    have hterm (i : Fin m) : (1 - ρ) * (q i * (grossReturn R x β i ^ (1 - ρ) / (1 - ρ))) =
        q i * grossReturn R x β i ^ (1 - ρ) := by field_simp
    simp only [hterm]
    obtain ⟨i, hi⟩ : ∃ i, 0 < q i := by
      by_contra hcon
      push Not at hcon
      have : ∑ i, q i ≤ 0 := Finset.sum_nonpos fun i _ => hcon i
      linarith
    exact lt_of_lt_of_le (mul_pos hi (Real.rpow_pos_of_pos (grossReturn_pos hR hx hβ i) _))
      (Finset.single_le_sum (fun j _ => mul_nonneg (hq j)
        (Real.rpow_nonneg (grossReturn_pos hR hx hβ j).le _)) (Finset.mem_univ i))
  set K := (1 - ρ) * J αs * w₀ ^ (1 - ρ)
  have hK : 0 < K := mul_pos (hpos αs hαs) (Real.rpow_pos_of_pos hw₀ _)
  apply isMaxOn_const_mul_iff hK _ hα
  intro β hβ
  have hG (i : Fin m) := grossReturn_pos hR hx hβ i
  simp only [J]
  rw [show ∑ i, q i * crraValue ρ q R x (w₀ * grossReturn R x β i) =
      ∑ i, q i * ((w₀ * grossReturn R x β i) ^ (1 - ρ) * J αs) from
    Finset.sum_congr rfl fun i _ => by rw [hV _ (mul_pos hw₀ (hG i))]]
  simp only [K, crraObjective, crra, one_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.mul_rpow hw₀.le (hG i).le]
  field_simp

/-- Expected CARA utility of investing the fraction `α` of wealth `w`. -/
noncomputable def caraObjective (k : ℝ) (q : Fin m → ℝ) (R : ℝ) (x : Fin m → ℝ) (w α : ℝ) : ℝ :=
  ∑ i, q i * -Real.exp (-k * (w * grossReturn R x α i))

/-- Expected CARA utility of investing the amount `A`, net of the safe wealth. -/
noncomputable def caraAmount (k : ℝ) (q : Fin m → ℝ) (R : ℝ) (x : Fin m → ℝ) (A : ℝ) : ℝ :=
  ∑ i, q i * -Real.exp (-k * (A * (x i - R)))

/-- Under CARA, `E u(w G_α) = e^{-kwR} E u(αw(x - R))`: the problem in amounts does not depend
on wealth. -/
theorem caraObjective_eq (k : ℝ) (q : Fin m → ℝ) (R : ℝ) (x : Fin m → ℝ) (w α : ℝ) :
    caraObjective k q R x w α = Real.exp (-k * w * R) * caraAmount k q R x (α * w) := by
  unfold caraObjective caraAmount grossReturn
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show -k * (w * ((1 - α) * R + α * x i)) = -k * w * R + -k * (α * w * (x i - R)) by ring,
    Real.exp_add]
  ring

/-- **Exercise 6.C.17** (MWG, p. 212), CARA. Myopia fails: if the amount problem has a unique
maximizer `A₀ > 0` on `[0, W]` with `A₀ ≤ min(w, w')` and `max(w, w') ≤ W`, then the optimal
fractions at two different wealth levels `w ≠ w'` differ (they are `A₀/w` and `A₀/w'`). -/
theorem exercise_6_C_17_cara {k : ℝ} (q : Fin m → ℝ) (R : ℝ) (x : Fin m → ℝ) {A₀ W w w' α α' : ℝ}
    (hA : 0 < A₀) (hw : A₀ ≤ w) (hw' : A₀ ≤ w') (hW : w ≤ W) (hW' : w' ≤ W)
    (huniq : ∀ A ∈ Icc 0 W, caraAmount k q R x A ≤ caraAmount k q R x A₀ ∧
      (caraAmount k q R x A = caraAmount k q R x A₀ → A = A₀))
    (hα : α ∈ Icc (0 : ℝ) 1) (hα' : α' ∈ Icc (0 : ℝ) 1)
    (hopt : IsMaxOn (caraObjective k q R x w) (Icc 0 1) α)
    (hopt' : IsMaxOn (caraObjective k q R x w') (Icc 0 1) α') (hne : w ≠ w') : α ≠ α' := by
  have hw0 : 0 < w := hA.trans_le hw
  have hw0' : 0 < w' := hA.trans_le hw'
  have amount (v a : ℝ) (hv : 0 < v) (hvA : A₀ ≤ v) (hvW : v ≤ W) (ha : a ∈ Icc (0 : ℝ) 1)
      (ho : IsMaxOn (caraObjective k q R x v) (Icc 0 1) a) : a * v = A₀ := by
    have hA0 : A₀ / v ∈ Icc (0 : ℝ) 1 := ⟨by positivity, (div_le_one hv).mpr hvA⟩
    have := ho hA0
    simp only [mem_ofPred_eq, caraObjective_eq] at this
    rw [div_mul_cancel₀ _ hv.ne'] at this
    have h1 := le_of_mul_le_mul_left this (Real.exp_pos _)
    have haW : a * v ∈ Icc 0 W := ⟨mul_nonneg ha.1 hv.le,
      (mul_le_of_le_one_left hv.le ha.2).trans hvW⟩
    exact (huniq _ haW).2 (le_antisymm (huniq _ haW).1 h1)
  have e1 := amount w α hw0 hw hW hα hopt
  have e2 := amount w' α' hw0' hw' hW' hα' hopt'
  intro heq
  rw [heq] at e1
  apply hne
  have : α' * (w - w') = 0 := by linarith
  rcases mul_eq_zero.mp this with h | h
  · rw [h, zero_mul] at e2; linarith
  · linarith

/-- Adding a constant preserves maximizers. -/
theorem isMaxOn_add_const_iff {f g : ℝ → ℝ} {S : Set ℝ} {c : ℝ} (h : ∀ β ∈ S, f β = c + g β)
    {α : ℝ} (hα : α ∈ S) : IsMaxOn f S α ↔ IsMaxOn g S α := by
  constructor
  · intro hm β hβ
    have := hm hβ
    simp only [mem_ofPred_eq, h β hβ, h α hα] at this ⊢
    linarith
  · intro hm β hβ
    have := hm hβ
    simp only [mem_ofPred_eq] at this ⊢
    rw [h β hβ, h α hα]
    linarith

/-- Expected logarithmic utility (constant relative risk aversion `1`). -/
noncomputable def logObjective (q : Fin m → ℝ) (R : ℝ) (x : Fin m → ℝ) (w α : ℝ) : ℝ :=
  ∑ i, q i * Real.log (w * grossReturn R x α i)

theorem logObjective_shift {q : Fin m → ℝ} (hq1 : ∑ i, q i = 1) {R : ℝ} (hR : 0 < R)
    {x : Fin m → ℝ} (hx : ∀ i, 0 < x i) {w : ℝ} (hw : 0 < w) {α : ℝ} (hα : α ∈ Icc (0 : ℝ) 1) :
    logObjective q R x w α = Real.log w + logObjective q R x 1 α := by
  unfold logObjective
  have e (i : Fin m) : q i * Real.log (w * grossReturn R x α i) =
      q i * Real.log w + q i * Real.log (1 * grossReturn R x α i) := by
    rw [Real.log_mul hw.ne' (grossReturn_pos hR hx hα i).ne', one_mul]; ring
  simp only [e, Finset.sum_add_distrib, ← Finset.sum_mul, hq1, one_mul]

/-- **Exercise 6.C.17** (MWG, p. 212), logarithmic utility. With `u = ln` the optimal fractions
in period 1 at any wealth, and in period 0 against the optimal period-1 value, are those of
the one-period problem. -/
theorem exercise_6_C_17_log {q : Fin m → ℝ} (hq1 : ∑ i, q i = 1) {R : ℝ} (hR : 0 < R)
    {x : Fin m → ℝ} (hx : ∀ i, 0 < x i) {w₀ : ℝ} (hw₀ : 0 < w₀) {α : ℝ}
    (hα : α ∈ Icc (0 : ℝ) 1) (hcont : ContinuousOn (logObjective q R x 1) (Icc 0 1)) :
    (∀ w > 0, IsMaxOn (logObjective q R x w) (Icc 0 1) α ↔
      IsMaxOn (logObjective q R x 1) (Icc 0 1) α) ∧
    (IsMaxOn (fun a => ∑ i, q i * sSup (logObjective q R x (w₀ * grossReturn R x a i) ''
      Icc 0 1)) (Icc 0 1) α ↔ IsMaxOn (logObjective q R x 1) (Icc 0 1) α) := by
  refine ⟨fun w hw => isMaxOn_add_const_iff (fun β hβ => logObjective_shift hq1 hR hx hw hβ) hα,
    ?_⟩
  obtain ⟨αs, hαs, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨0, le_rfl, zero_le_one⟩ hcont
  have hV (w : ℝ) (hw : 0 < w) : sSup (logObjective q R x w '' Icc 0 1) =
      Real.log w + logObjective q R x 1 αs := by
    apply IsGreatest.csSup_eq
    refine ⟨⟨αs, hαs, logObjective_shift hq1 hR hx hw hαs⟩, ?_⟩
    rintro _ ⟨β, hβ, rfl⟩
    rw [logObjective_shift hq1 hR hx hw hβ]
    have := hmax hβ
    simp only [mem_ofPred_eq] at this
    linarith
  apply isMaxOn_add_const_iff (c := Real.log w₀ + logObjective q R x 1 αs) _ hα
  intro β hβ
  have hG (i : Fin m) := grossReturn_pos hR hx hβ i
  rw [show ∑ i, q i * sSup (logObjective q R x (w₀ * grossReturn R x β i) '' Icc 0 1) =
      ∑ i, q i * (Real.log (w₀ * grossReturn R x β i) + logObjective q R x 1 αs) from
    Finset.sum_congr rfl fun i _ => by rw [hV _ (mul_pos hw₀ (hG i))]]
  have e (i : Fin m) : q i * (Real.log (w₀ * grossReturn R x β i) + logObjective q R x 1 αs) =
      q i * (Real.log w₀ + logObjective q R x 1 αs) +
        q i * Real.log (1 * grossReturn R x β i) := by
    rw [Real.log_mul hw₀.ne' (hG i).ne', one_mul]; ring
  simp only [e, Finset.sum_add_distrib, ← Finset.sum_mul, hq1, one_mul]
  simp only [logObjective, one_mul]

/-- The expected CARA utility of holding `α` (amounts) in risky assets with returns `z` and
`w - ∑ α` in the riskless asset with return `r`. -/
noncomputable def caraPortfolioEU {N : ℕ} (a w r : ℝ) (ρ : Measure (Fin N → ℝ))
    (α : Fin N → ℝ) : ℝ :=
  ∫ z, -Real.exp (-a * ((w - ∑ n, α n) * r + α ⬝ᵥ z)) ∂ρ

/-- The certainty-equivalent index `wr + α · (μ - r1) - (a/2) α'Vα`. -/
noncomputable def caraCE {N : ℕ} (a w r : ℝ) (μ : Fin N → ℝ) (V : Matrix (Fin N) (Fin N) ℝ)
    (α : Fin N → ℝ) : ℝ :=
  w * r + α ⬝ᵥ (μ - fun _ => r) - a / 2 * (α ⬝ᵥ (V.mulVec α))

/-- With normal returns (given by their moment generating function), expected CARA utility is
`-exp(-a · CE(α))`. -/
theorem caraPortfolioEU_eq {N : ℕ} {a w r : ℝ} {ρ : Measure (Fin N → ℝ)} {μ : Fin N → ℝ}
    {V : Matrix (Fin N) (Fin N) ℝ}
    (hmgf : ∀ t : Fin N → ℝ, ∫ z, Real.exp (t ⬝ᵥ z) ∂ρ = Real.exp (t ⬝ᵥ μ + t ⬝ᵥ (V.mulVec t) / 2))
    (α : Fin N → ℝ) : caraPortfolioEU a w r ρ α = -Real.exp (-a * caraCE a w r μ V α) := by
  unfold caraPortfolioEU caraCE
  have e (z : Fin N → ℝ) : -Real.exp (-a * ((w - ∑ n, α n) * r + α ⬝ᵥ z)) =
      -Real.exp (-a * ((w - ∑ n, α n) * r)) * Real.exp ((-a • α) ⬝ᵥ z) := by
    rw [show -a * ((w - ∑ n, α n) * r + α ⬝ᵥ z) = -a * ((w - ∑ n, α n) * r) + (-a • α) ⬝ᵥ z by
      rw [smul_dotProduct, smul_eq_mul]; ring, Real.exp_add]
    ring
  simp only [e]
  rw [integral_const_mul, hmgf, neg_mul, ← Real.exp_add]
  congr 2
  simp only [smul_dotProduct, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, dotProduct_sub]
  have hs : α ⬝ᵥ (fun _ => r) = (∑ n, α n) * r := by
    simp [dotProduct, Finset.sum_mul]
  rw [hs]
  ring

/-- **Exercise 6.C.19** (MWG, pp. 212-213). With `u(x) = -e^{-ax}`, `a > 0`, riskless return
`r` and jointly normal risky returns with mean `μ` and positive definite covariance `V`, the
risky demand `α*` solving `aVα* = μ - r1` (i.e. `α* = V⁻¹(μ - r1)/a`) is the unique optimal
portfolio; the riskless demand is `w - ∑ α*`. -/
theorem exercise_6_C_19 {N : ℕ} {a w r : ℝ} (ha : 0 < a) {ρ : Measure (Fin N → ℝ)}
    {μ : Fin N → ℝ} {V : Matrix (Fin N) (Fin N) ℝ} (hV : V.PosDef)
    (hmgf : ∀ t : Fin N → ℝ, ∫ z, Real.exp (t ⬝ᵥ z) ∂ρ = Real.exp (t ⬝ᵥ μ + t ⬝ᵥ (V.mulVec t) / 2))
    {αs : Fin N → ℝ} (hαs : a • (V.mulVec αs) = μ - fun _ => r) :
    ∀ α, caraPortfolioEU a w r ρ α ≤ caraPortfolioEU a w r ρ αs ∧
      (caraPortfolioEU a w r ρ α = caraPortfolioEU a w r ρ αs → α = αs) := by
  have hsym (x y : Fin N → ℝ) : x ⬝ᵥ (V.mulVec y) = y ⬝ᵥ (V.mulVec x) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm]
    congr 2
    have := hV.1
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
    exact this
  have key (α : Fin N → ℝ) : caraCE a w r μ V αs - caraCE a w r μ V α =
      a / 2 * ((α - αs) ⬝ᵥ (V.mulVec (α - αs))) := by
    unfold caraCE
    rw [← hαs]
    simp only [dotProduct_smul, smul_eq_mul, Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct,
      hsym αs α]
    ring
  intro α
  rw [caraPortfolioEU_eq hmgf, caraPortfolioEU_eq hmgf]
  have hq : 0 ≤ (α - αs) ⬝ᵥ (V.mulVec (α - αs)) := by
    by_cases h : α - αs = 0
    · rw [h]; simp
    · exact (hV.dotProduct_mulVec_pos h).le
  constructor
  · have : caraCE a w r μ V α ≤ caraCE a w r μ V αs := by
      have := key α; nlinarith
    simp only [neg_le_neg_iff, Real.exp_le_exp]
    nlinarith
  · intro heq
    have h1 : caraCE a w r μ V α = caraCE a w r μ V αs := by
      have := Real.exp_injective (neg_injective heq)
      have := mul_left_cancel₀ (neg_ne_zero.mpr ha.ne') this
      exact this
    by_contra hne
    have hpos := hV.dotProduct_mulVec_pos (sub_ne_zero.mpr hne)
    simp only [star_trivial] at hpos
    have := key α
    rw [h1, sub_self] at this
    nlinarith

/-- **Exercise 6.C.19**: existence and uniqueness of the solution `α* = V⁻¹(μ - r1)/a`. -/
theorem exercise_6_C_19_exists {N : ℕ} {a r : ℝ} (ha : 0 < a) {μ : Fin N → ℝ}
    {V : Matrix (Fin N) (Fin N) ℝ} (hV : V.PosDef) :
    ∃! αs : Fin N → ℝ, a • (V.mulVec αs) = μ - fun _ => r := by
  have hu : IsUnit V := hV.isUnit
  refine ⟨a⁻¹ • (V⁻¹.mulVec (μ - fun _ => r)), ?_, fun β hβ => ?_⟩
  · change a • V.mulVec (a⁻¹ • V⁻¹.mulVec (μ - fun _ => r)) = μ - fun _ => r
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
      ((Matrix.isUnit_iff_isUnit_det V).mp hu), Matrix.one_mulVec, smul_smul,
      mul_inv_cancel₀ ha.ne', one_smul]
  · have hinj := Matrix.mulVec_injective_iff_isUnit.mpr hu
    apply hinj
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
      ((Matrix.isUnit_iff_isUnit_det V).mp hu), Matrix.one_mulVec, ← hβ, smul_smul,
      inv_mul_cancel₀ ha.ne', one_smul]

/-- A concrete instance of the normality hypothesis of Exercise 6.C.19: one risky asset with a
Gaussian return of mean `m` and variance `v > 0`. -/
theorem exercise_6_C_19_instance (m : ℝ) (v : NNReal) :
    ∀ t : Fin 1 → ℝ, ∫ z, Real.exp (t ⬝ᵥ z) ∂((gaussianReal m v).map fun x => fun _ => x) =
      Real.exp (t ⬝ᵥ (fun _ => m) + t ⬝ᵥ ((Matrix.of fun _ _ => (v : ℝ)).mulVec t) / 2) := by
  intro t
  rw [integral_map (by fun_prop) (by fun_prop)]
  have h := congrFun (mgf_id_gaussianReal (μ := m) (v := v)) (t 0)
  simp only [mgf, id] at h
  simp only [dotProduct, Fin.sum_univ_one, Matrix.mulVec, Matrix.of_apply]
  rw [show (fun x : ℝ => Real.exp (t 0 * x)) = fun x => Real.exp (t 0 * x) from rfl, h]
  congr 1
  ring

end MWG.ChoiceUnderUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# First-order stochastic dominance

MWG, Section 6.D, pp. 194-197: the standing restriction to distributions with `F(0) = 0` and
`F(x̄) = 1`, Definition 6.D.1, Proposition 6.D.1 in full generality for distribution
functions (both directions), Example 6.D.1 (an upward probabilistic shift produces a
first-order dominating distribution; Figure 6.D.2), and Exercise 6.D.2.

The "if" direction of Proposition 6.D.1 is proved without MWG's integration by parts (which
needs differentiable `u`): writing both laws as images of a uniform draw under their
generalized inverses (Kreps's `generalQuantile_uniform_law`), `F ≤ G` makes the quantile of
`F` pointwise larger, and a nondecreasing `u` preserves the order.
-/

namespace MWG.ChoiceUnderUncertainty

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

/-- **p. 195**. MWG's distributions in Section 6.D: probability measures with `F(0) = 0` and
`F(x̄) = 1` for some `x̄`. -/
def IsMWGDist (μ : Measure ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ cdf μ 0 = 0 ∧ ∃ M, cdf μ M = 1

/-- Such a distribution is concentrated on some `(0, x̄]`. -/
theorem IsMWGDist.ae_mem {μ : Measure ℝ} (h : IsMWGDist μ) :
    ∃ M, 0 < M ∧ ∀ᵐ x ∂μ, x ∈ Ioc 0 M := by
  obtain ⟨hp, h0, M, hM⟩ := h
  have hle : μ (Iic 0) = 0 := by rw [← ofReal_cdf, h0, ENNReal.ofReal_zero]
  have hgt : μ (Ioi M) = 0 := by
    rw [← compl_Iic, prob_compl_eq_zero_iff measurableSet_Iic, ← ofReal_cdf, hM,
      ENNReal.ofReal_one]
  have hM0 : 0 < M := by
    by_contra hn
    have := monotone_cdf μ (not_lt.mp hn)
    rw [hM, h0] at this
    norm_num at this
  refine ⟨M, hM0, ?_⟩
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hle, measure_eq_zero_iff_ae_notMem.mp hgt]
    with x h1 h2
  exact ⟨lt_of_not_ge h1, le_of_not_gt h2⟩

/-- An MWG distribution is a money lottery on `[0, ∞)`. -/
theorem IsMWGDist.isMoneyLottery {μ : Measure ℝ} (h : IsMWGDist μ) :
    IsMoneyLottery (Ici 0) μ := by
  obtain ⟨M, -, hae⟩ := h.ae_mem
  refine ⟨h.1, 0, M, Icc_subset_Ici_self, ?_⟩
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [hae] with x hx
  simpa using (⟨hx.1.le, hx.2⟩ : 0 ≤ x ∧ x ≤ M)

/-- A nondecreasing utility is integrable for an MWG distribution. -/
theorem IsMWGDist.integrable_monotone {μ : Measure ℝ} (h : IsMWGDist μ) {u : ℝ → ℝ}
    (hu : Monotone u) : Integrable u μ := by
  have := h.1
  obtain ⟨M, -, hae⟩ := h.ae_mem
  refine Integrable.of_bound hu.measurable.aestronglyMeasurable (|u 0| + |u M|) ?_
  filter_upwards [hae] with x hx
  rw [Real.norm_eq_abs, abs_le]
  have h1 := hu hx.1.le
  have h2 := hu hx.2
  constructor
  · linarith [neg_abs_le (u 0), abs_nonneg (u M)]
  · linarith [le_abs_self (u M), abs_nonneg (u 0)]

/-- **Definition 6.D.1** (MWG, p. 195). `F` first-order stochastically dominates `G` if
`∫ u dF ≥ ∫ u dG` for every nondecreasing `u : ℝ → ℝ`. -/
def FOSD (μ ν : Measure ℝ) : Prop :=
  ∀ u : ℝ → ℝ, Monotone u → ∫ x, u x ∂ν ≤ ∫ x, u x ∂μ

/-- The step utility `1_{x > c}` is nondecreasing. -/
theorem monotone_step (c : ℝ) : Monotone fun x : ℝ => (Ioi c).indicator (1 : ℝ → ℝ) x := by
  intro x y hxy
  by_cases hx : c < x
  · have hy : c < y := hx.trans_le hxy
    simp [indicator, hx, hy]
  · by_cases hy : c < y <;> simp [indicator, hx, hy]

/-- The expected value of the step utility is `1 - F(c)`. -/
theorem integral_step {μ : Measure ℝ} [IsProbabilityMeasure μ] (c : ℝ) :
    ∫ x, (Ioi c).indicator (1 : ℝ → ℝ) x ∂μ = 1 - cdf μ c := by
  rw [integral_indicator_one measurableSet_Ioi, cdf_eq_real, ← compl_Iic,
    measureReal_compl measurableSet_Iic, probReal_univ]

/-- **Proposition 6.D.1** (MWG, p. 195). For MWG distributions, `F` first-order
stochastically dominates `G` iff `F(x) ≤ G(x)` for every `x`. -/
theorem proposition_6_D_1 {μ ν : Measure ℝ} (hμ : IsMWGDist μ) (hν : IsMWGDist ν) :
    FOSD μ ν ↔ ∀ x, cdf μ x ≤ cdf ν x := by
  have := hμ.1
  have := hν.1
  constructor
  · intro h x
    have := h _ (monotone_step x)
    rw [integral_step, integral_step] at this
    linarith
  · intro hle u hu
    set lam : Measure ℝ := volume.restrict (Ioo (0 : ℝ) 1)
    have hlam : IsProbabilityMeasure lam := ⟨by simp [lam, Real.volume_Ioo]⟩
    have hQμ := Kreps.UtilityForMoney.generalQuantile_measurable μ
    have hQν := Kreps.UtilityForMoney.generalQuantile_measurable ν
    have eμ : ∫ x, u x ∂μ = ∫ t, u (Kreps.UtilityForMoney.GeneralQuantile μ t) ∂lam := by
      conv_lhs => rw [← Kreps.UtilityForMoney.generalQuantile_uniform_law μ]
      exact integral_map hQμ.aemeasurable hu.measurable.aestronglyMeasurable
    have eν : ∫ x, u x ∂ν = ∫ t, u (Kreps.UtilityForMoney.GeneralQuantile ν t) ∂lam := by
      conv_lhs => rw [← Kreps.UtilityForMoney.generalQuantile_uniform_law ν]
      exact integral_map hQν.aemeasurable hu.measurable.aestronglyMeasurable
    rw [eμ, eν]
    have hint (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (hρ : IsMWGDist ρ) :
        Integrable (fun t => u (Kreps.UtilityForMoney.GeneralQuantile ρ t)) lam := by
      have h1 := hρ.integrable_monotone hu
      rw [← Kreps.UtilityForMoney.generalQuantile_uniform_law ρ] at h1
      exact (integrable_map_measure hu.measurable.aestronglyMeasurable
        (Kreps.UtilityForMoney.generalQuantile_measurable ρ).aemeasurable).mp h1
    apply integral_mono_ae (hint ν hν) (hint μ hμ)
    have hae : ∀ᵐ t ∂lam, t ∈ Ioo (0 : ℝ) 1 := ae_restrict_mem measurableSet_Ioo
    filter_upwards [hae] with t ht
    apply hu
    rw [Kreps.UtilityForMoney.generalQuantile_le_iff ν ht]
    exact ((Kreps.UtilityForMoney.generalQuantile_le_iff μ ht _).mp le_rfl).trans (hle _)

/-- **Exercise 6.D.2** (MWG, p. 213), first part. First-order dominance implies a weakly
higher mean. -/
theorem exercise_6_D_2_mean {μ ν : Measure ℝ} (h : FOSD μ ν) :
    ∫ x, x ∂ν ≤ ∫ x, x ∂μ :=
  h id monotone_id

/-- **Exercise 6.D.2** (MWG, p. 213), second part. `F = (1/2)δ₁ + (1/2)δ₅` has a higher mean
(`3`) than `G = δ₂` (`2`) but does not first-order dominate it. -/
theorem exercise_6_D_2_example :
    ∫ x, x ∂(Measure.dirac (2 : ℝ)) < ∫ x, x ∂(binLot (1 / 2) 1 5) ∧
      ¬FOSD (binLot (1 / 2) 1 5) (Measure.dirac 2) := by
  constructor
  · rw [integral_dirac, integral_binLot _ _ _ _ (by norm_num) (by norm_num)]; norm_num
  · intro h
    have := h _ (monotone_step 1)
    rw [integral_dirac, integral_binLot _ _ _ _ (by norm_num) (by norm_num)] at this
    simp [indicator] at this
    norm_num at this

/-- **Example 6.D.1** (MWG, p. 196). An upward probabilistic shift: if the second stage adds
`z ≥ 0` drawn from `H_x` (bounded), the reduced distribution `F` first-order stochastically
dominates `G`. -/
theorem example_6_D_1 {μ : Measure ℝ} (hμ : IsMWGDist μ) (κ : Kernel ℝ ℝ) [IsMarkovKernel κ]
    {B : ℝ} (hκ : ∀ x, ∀ᵐ z ∂(κ x), z ∈ Icc 0 B) :
    FOSD ((μ ⊗ₘ κ).map fun p => p.1 + p.2) μ := by
  have := hμ.1
  obtain ⟨M, -, hae⟩ := hμ.ae_mem
  intro u hu
  have hmeas : Measurable fun p : ℝ × ℝ => p.1 + p.2 := by fun_prop
  rw [integral_map hmeas.aemeasurable hu.measurable.aestronglyMeasurable]
  have hjoint : ∀ᵐ p ∂(μ ⊗ₘ κ), p.1 ∈ Ioc 0 M ∧ p.2 ∈ Icc 0 B := by
    apply Measure.ae_compProd_of_ae_ae
    · exact (measurable_fst measurableSet_Ioc).inter (measurable_snd measurableSet_Icc)
    · filter_upwards [hae] with x hx
      filter_upwards [hκ x] with z hz using ⟨hx, hz⟩
  have hint : Integrable (fun p : ℝ × ℝ => u (p.1 + p.2)) (μ ⊗ₘ κ) := by
    refine Integrable.of_bound (hu.measurable.comp hmeas).aestronglyMeasurable
      (|u 0| + |u (M + B)|) ?_
    filter_upwards [hjoint] with p hp
    rw [Real.norm_eq_abs, abs_le]
    have h1 := hu (show 0 ≤ p.1 + p.2 by linarith [hp.1.1, hp.2.1])
    have h2 := hu (show p.1 + p.2 ≤ M + B by linarith [hp.1.2, hp.2.2])
    constructor
    · linarith [neg_abs_le (u 0), abs_nonneg (u (M + B))]
    · linarith [le_abs_self (u (M + B)), abs_nonneg (u 0)]
  rw [Measure.integral_compProd hint]
  apply integral_mono_ae (hμ.integrable_monotone hu) hint.integral_compProd
  filter_upwards [hint.ae_of_compProd] with x hx
  calc u x = ∫ _, u x ∂(κ x) := by simp
    _ ≤ ∫ z, u (x + z) ∂(κ x) := integral_mono_ae (integrable_const _) hx
        ((hκ x).mono fun z hz => hu (by linarith [hz.1]))

/-- Integrals against a weighted Dirac mass. -/
theorem integral_smul_dirac {a : ℝ} (ha : 0 ≤ a) (x : ℝ) (f : ℝ → ℝ) :
    ∫ z, f z ∂(ENNReal.ofReal a • Measure.dirac x) = a * f x := by
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal ha, smul_eq_mul]

/-- A weighted Dirac mass integrates every function. -/
theorem integrable_smul_dirac (a x : ℝ) (f : ℝ → ℝ) :
    Integrable f (ENNReal.ofReal a • Measure.dirac x) :=
  (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

/-- The three-atom lottery `a δ_x + b δ_y + c δ_z`. -/
noncomputable def lot3M (a b c x y z : ℝ) : Measure ℝ :=
  ENNReal.ofReal a • Measure.dirac x + ENNReal.ofReal b • Measure.dirac y +
    ENNReal.ofReal c • Measure.dirac z

/-- Integrals against a three-atom lottery. -/
theorem integral_lot3M {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (x y z : ℝ)
    (f : ℝ → ℝ) : ∫ t, f t ∂(lot3M a b c x y z) = a * f x + b * f y + c * f z := by
  unfold lot3M
  rw [integral_add_measure ((integrable_smul_dirac a x f).add_measure
    (integrable_smul_dirac b y f)) (integrable_smul_dirac c z f),
    integral_add_measure (integrable_smul_dirac a x f) (integrable_smul_dirac b y f),
    integral_smul_dirac ha, integral_smul_dirac hb, integral_smul_dirac hc]

/-- **Figure 6.D.2** (MWG, p. 196). `G` is the even randomization between `1` and `4`; the
outcome `1` is shifted to an even chance of `2` or `3` and `4` to `5`. The resulting
`F = (1/4)δ₂ + (1/4)δ₃ + (1/2)δ₅` first-order dominates `G`. -/
theorem figure_6_D_2 : FOSD (lot3M (1 / 4) (1 / 4) (1 / 2) 2 3 5) (binLot (1 / 2) 1 4) := by
  intro u hu
  rw [integral_binLot _ _ _ _ (by norm_num) (by norm_num),
    integral_lot3M (by norm_num) (by norm_num) (by norm_num)]
  have h1 := hu (show (1 : ℝ) ≤ 2 by norm_num)
  have h2 := hu (show (1 : ℝ) ≤ 3 by norm_num)
  have h3 := hu (show (4 : ℝ) ≤ 5 by norm_num)
  linarith

end MWG.ChoiceUnderUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# First-order dominance as an upward probabilistic shift

MWG, Example 6.D.1, p. 197: "whenever `F` first-order stochastically dominates `G`, it is
possible to generate `F` from `G`" by an upward probabilistic shift. The two distributions are
coupled through their quantile functions applied to one uniform draw (Kreps's
`generalQuantile_uniform_law`); the shift kernel `H_x` is the conditional law of the increment
given the first stage (Mathlib's disintegration `condKernel`), modified on a `G`-null set so
that `H_x` is concentrated on `[0, ∞)` for every `x`.
-/

namespace MWG.ChoiceUnderUncertainty

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

/-- **Example 6.D.1** (MWG, p. 197), the reverse direction. If `F` first-order stochastically
dominates `G` (MWG distributions), there is a Markov kernel `H_x` with `H_x(z < 0) = 0` for
every `x` such that `F` is the law of `x + z` when `x ~ G` and `z ~ H_x`. -/
theorem example_6_D_1_converse {μ ν : Measure ℝ} (hμ : IsMWGDist μ) (hν : IsMWGDist ν)
    (h : FOSD μ ν) : ∃ κ : Kernel ℝ ℝ, IsMarkovKernel κ ∧ (∀ x, κ x (Iio 0) = 0) ∧
      μ = (ν ⊗ₘ κ).map fun p => p.1 + p.2 := by
  have := hμ.1
  have := hν.1
  have hle := (proposition_6_D_1 hμ hν).mp h
  set lam : Measure ℝ := volume.restrict (Ioo (0 : ℝ) 1)
  have hlam : IsProbabilityMeasure lam := ⟨by simp [lam, Real.volume_Ioo]⟩
  set Qμ := Kreps.UtilityForMoney.GeneralQuantile μ
  set Qν := Kreps.UtilityForMoney.GeneralQuantile ν
  have mQμ : Measurable Qμ := Kreps.UtilityForMoney.generalQuantile_measurable μ
  have mQν : Measurable Qν := Kreps.UtilityForMoney.generalQuantile_measurable ν
  set f : ℝ → ℝ × ℝ := fun t => (Qν t, Qμ t - Qν t)
  have mf : Measurable f := mQν.prodMk (mQμ.sub mQν)
  set ρ : Measure (ℝ × ℝ) := lam.map f
  have hρ : IsProbabilityMeasure ρ := inferInstance
  have hfst : ρ.fst = ν := by
    rw [Measure.fst, Measure.map_map measurable_fst mf]
    exact Kreps.UtilityForMoney.generalQuantile_uniform_law ν
  have hsum : ρ.map (fun p => p.1 + p.2) = μ := by
    rw [Measure.map_map (by fun_prop) mf]
    convert Kreps.UtilityForMoney.generalQuantile_uniform_law μ using 2
    funext t; simp [f, Qμ]
  -- the increment is nonnegative almost surely
  have hpos : ∀ᵐ p ∂ρ, 0 ≤ p.2 := by
    rw [ae_map_iff mf.aemeasurable (measurableSet_le measurable_const measurable_snd)]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    simp only [f, sub_nonneg]
    rw [Kreps.UtilityForMoney.generalQuantile_le_iff ν ht]
    exact ((Kreps.UtilityForMoney.generalQuantile_le_iff μ ht _).mp le_rfl).trans (hle _)
  set κ₀ := ρ.condKernel
  have hdis : ρ.fst ⊗ₘ κ₀ = ρ := ρ.disintegrate κ₀
  have hκ₀ : ∀ᵐ x ∂ρ.fst, κ₀ x (Iio 0) = 0 := by
    have := Measure.ae_ae_of_ae_compProd (μ := ρ.fst) (κ := κ₀)
      (p := fun p : ℝ × ℝ => 0 ≤ p.2) (by rw [hdis]; exact hpos)
    filter_upwards [this] with x hx
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hx] with z hz
    simpa using hz
  have hs : MeasurableSet {x : ℝ | κ₀ x (Iio 0) = 0} :=
    (Kernel.measurable_coe κ₀ measurableSet_Iio) (measurableSet_singleton 0)
  set κ := Kernel.piecewise hs κ₀ (Kernel.const ℝ (Measure.dirac 0))
  refine ⟨κ, inferInstance, fun x => ?_, ?_⟩
  · rw [Kernel.piecewise_apply]
    split_ifs with hx
    · exact hx
    · simp [Kernel.const_apply]
  · have hae : κ =ᵐ[ν] κ₀ := by
      rw [← hfst]
      filter_upwards [hκ₀] with x hx
      rw [Kernel.piecewise_apply]
      exact ite_eq_left_iff.mpr fun hn => absurd (show x ∈ {x | κ₀ x (Iio 0) = 0} from hx) hn
    rw [Measure.compProd_congr hae, ← hfst, hdis, hsum]

end MWG.ChoiceUnderUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Second-order stochastic dominance

MWG, Section 6.D, pp. 197-199: Definition 6.D.2, mean-preserving spreads (Example 6.D.2),
the integral condition (6.D.2), equality of the areas (6.D.1), and the implications of
Proposition 6.D.2 among (i) second-order dominance, (ii) mean-preserving spread and (iii)
condition (6.D.2).

A mean-preserving spread is MWG's compound lottery: a Markov kernel `H_x` with mean zero for
every `x`, and `G` the law of `x + z` when `x ~ F` and `z ~ H_x`. The utility functions of
Definition 6.D.2 are nondecreasing and concave on `ℝ₊`; such a function may jump at `0`, which
carries no mass under MWG's distributions (`F(0) = 0`). The key identity is
`∫ min(t, x) dF(t) = x - ∫₀ˣ F(s) ds` (layer-cake formula).
-/

namespace MWG.ChoiceUnderUncertainty

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

/-- **Definition 6.D.2** (MWG, p. 197). `F` second-order stochastically dominates `G` if
`∫ u dF ≥ ∫ u dG` for every nondecreasing concave `u : ℝ₊ → ℝ` (MWG compares distributions
with the same mean, which the theorems below assume). -/
def SOSD (μ ν : Measure ℝ) : Prop :=
  ∀ u : ℝ → ℝ, MonotoneOn u (Ici 0) → ConcaveOn ℝ (Ici 0) u → ∫ x, u x ∂ν ≤ ∫ x, u x ∂μ

/-- A nondecreasing concave utility on `ℝ₊` is integrable for an MWG distribution. -/
theorem IsMWGDist.integrable_concave {μ : Measure ℝ} (h : IsMWGDist μ) {u : ℝ → ℝ}
    (hm : MonotoneOn u (Ici 0)) (hc : ConcaveOn ℝ (Ici 0) u) : Integrable u μ := by
  have := h.1
  obtain ⟨M, hM, hae⟩ := h.ae_mem
  have hcont : ContinuousOn u (Ioi 0) := by
    have := hc.continuousOn_interior
    rwa [interior_Ici] at this
  have hr : μ.restrict (Ioi 0) = μ := Measure.restrict_eq_self_of_ae_mem
    (hae.mono fun x hx => hx.1)
  have hmeas : AEStronglyMeasurable u μ := by
    have := hcont.aestronglyMeasurable (μ := μ) measurableSet_Ioi
    rwa [hr] at this
  refine Integrable.of_bound hmeas (|u 0| + |u M|) ?_
  filter_upwards [hae] with x hx
  rw [Real.norm_eq_abs, abs_le]
  have h1 := hm (mem_Ici.mpr le_rfl) (mem_Ici.mpr hx.1.le) hx.1.le
  have h2 := hm (mem_Ici.mpr hx.1.le) (mem_Ici.mpr hM.le) hx.2
  constructor
  · linarith [neg_abs_le (u 0), abs_nonneg (u M)]
  · linarith [le_abs_self (u M), abs_nonneg (u 0)]

/-- `t ↦ min(t, x)` is nondecreasing and concave on `ℝ₊`. -/
theorem min_utility_props (x : ℝ) :
    MonotoneOn (fun t : ℝ => min t x) (Ici 0) ∧ ConcaveOn ℝ (Ici 0) (fun t : ℝ => min t x) := by
  refine ⟨fun a _ b _ hab => min_le_min_right x hab, convex_Ici 0, ?_⟩
  intro a _ b _ s t hs ht hst
  simp only [smul_eq_mul]
  apply le_min
  · nlinarith [min_le_left a x, min_le_left b x]
  · have h1 := mul_le_mul_of_nonneg_left (min_le_right a x) hs
    have h2 := mul_le_mul_of_nonneg_left (min_le_right b x) ht
    have h3 : s * x + t * x = x := by rw [← add_mul, hst, one_mul]
    linarith

/-- **p. 198**. `∫ min(t, x) dF(t) = x - ∫₀ˣ F(s) ds` for an MWG distribution and `x ≥ 0`. -/
theorem integral_min_eq {μ : Measure ℝ} (h : IsMWGDist μ) {x : ℝ} (hx : 0 ≤ x) :
    ∫ t, min t x ∂μ = x - ∫ s in (0)..x, cdf μ s := by
  have := h.1
  obtain ⟨M, -, hae⟩ := h.ae_mem
  have hint : Integrable (fun t : ℝ => min t x) μ := by
    refine Integrable.of_bound (by fun_prop) x ?_
    filter_upwards [hae] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min ht.1.le hx)]
    exact min_le_right _ _
  rw [hint.integral_eq_integral_meas_lt (hae.mono fun t ht => le_min ht.1.le hx)]
  have key : ∀ s ∈ Ioi (0 : ℝ), μ.real {t | s < min t x} =
      (Iio x).indicator (fun s => 1 - cdf μ s) s := by
    intro s _
    by_cases hs : s < x
    · have : {t | s < min t x} = Ioi s := by
        ext t; simp only [mem_ofPred_eq, lt_min_iff, mem_Ioi, hs, and_true]
      rw [this, indicator_of_mem (mem_Iio.mpr hs), cdf_eq_real, ← compl_Iic,
        measureReal_compl measurableSet_Iic, probReal_univ]
    · have : {t | s < min t x} = ∅ := by
        ext t; simp only [mem_ofPred_eq, lt_min_iff, mem_empty_iff_false, iff_false, not_and]
        exact fun _ => hs
      rw [this, indicator_of_notMem (by simpa using hs)]; simp
  rw [setIntegral_congr_fun measurableSet_Ioi key, integral_indicator measurableSet_Iio,
    Measure.restrict_restrict measurableSet_Iio, inter_comm, Ioi_inter_Iio,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hx,
    intervalIntegral.integral_sub intervalIntegrable_const
      ((monotone_cdf μ).intervalIntegrable)]
  simp

/-- **(6.D.2)** (MWG, p. 198). The integral condition: `∫₀ˣ G(t) dt ≥ ∫₀ˣ F(t) dt` for all
`x ≥ 0`. -/
def IntegralCondition (μ ν : Measure ℝ) : Prop :=
  ∀ x, 0 ≤ x → ∫ t in (0)..x, cdf μ t ≤ ∫ t in (0)..x, cdf ν t

/-- **(6.D.1)** (MWG, p. 198). With equal means, the areas below the two distribution
functions over `[0, x̄]` coincide: `∫₀^x̄ (F - G) = 0` (for `x̄` with `F(x̄) = G(x̄) = 1`). -/
theorem equal_areas {μ ν : Measure ℝ} (hμ : IsMWGDist μ) (hν : IsMWGDist ν) {M : ℝ}
    (hM : 0 ≤ M) (hμM : cdf μ M = 1) (hνM : cdf ν M = 1)
    (hmean : ∫ x, x ∂μ = ∫ x, x ∂ν) :
    ∫ t in (0)..M, (cdf μ t - cdf ν t) = 0 := by
  have := hμ.1
  have := hν.1
  have hmin (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (hρ : IsMWGDist ρ) (hρM : cdf ρ M = 1) :
      ∫ t, min t M ∂ρ = ∫ t, t ∂ρ := by
    apply integral_congr_ae
    have hgt : ρ (Ioi M) = 0 := by
      rw [← compl_Iic, prob_compl_eq_zero_iff measurableSet_Iic, ← ofReal_cdf, hρM,
        ENNReal.ofReal_one]
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hgt] with t ht
    exact min_eq_left (le_of_not_gt ht)
  have e1 := integral_min_eq hμ hM
  have e2 := integral_min_eq hν hM
  rw [hmin μ hμ hμM] at e1
  rw [hmin ν hν hνM] at e2
  rw [intervalIntegral.integral_sub ((monotone_cdf μ).intervalIntegrable)
    ((monotone_cdf ν).intervalIntegrable)]
  linarith

/-- **Proposition 6.D.2**, (i) ⇒ (iii) (MWG, p. 199). Second-order dominance implies the
integral condition (6.D.2), using the utilities `min(t, x)`. -/
theorem sosd_integralCondition {μ ν : Measure ℝ} (hμ : IsMWGDist μ) (hν : IsMWGDist ν)
    (h : SOSD μ ν) : IntegralCondition μ ν := by
  intro x hx
  obtain ⟨hm, hc⟩ := min_utility_props x
  have := h _ hm hc
  rw [integral_min_eq hμ hx, integral_min_eq hν hx] at this
  linarith

/-- **Example 6.D.2** (MWG, p. 197). A mean-preserving spread: a Markov kernel `H_x` with mean
zero for every `x`, and `G` the law of `x + z`. -/
def IsMeanPreservingSpread (μ ν : Measure ℝ) : Prop :=
  ∃ κ : Kernel ℝ ℝ, IsMarkovKernel κ ∧ (∀ x, Integrable (fun z => z) (κ x) ∧
    ∫ z, z ∂(κ x) = 0) ∧ ν = (μ ⊗ₘ κ).map fun p => p.1 + p.2

/-- **Example 6.D.2** (MWG, pp. 197-198) and **Proposition 6.D.2**, (ii) ⇒ (i). If `G` is a
mean-preserving spread of `F` (both MWG distributions), `F` second-order stochastically
dominates `G` and the means agree. -/
theorem sosd_of_meanPreservingSpread {μ ν : Measure ℝ} (hμ : IsMWGDist μ) (hν : IsMWGDist ν)
    (h : IsMeanPreservingSpread μ ν) : SOSD μ ν ∧ ∫ x, x ∂μ = ∫ x, x ∂ν := by
  obtain ⟨κ, hκ, hmean, rfl⟩ := h
  have := hμ.1
  obtain ⟨M, hM, hae⟩ := hμ.ae_mem
  obtain ⟨N, hN, haeν⟩ := hν.ae_mem
  have hmeas : Measurable fun p : ℝ × ℝ => p.1 + p.2 := by fun_prop
  have hsum : ∀ᵐ p ∂(μ ⊗ₘ κ), p.1 + p.2 ∈ Ioc 0 N :=
    ae_of_ae_map hmeas.aemeasurable haeν
  have hfst : ∀ᵐ p ∂(μ ⊗ₘ κ), p.1 ∈ Ioc 0 M := by
    apply Measure.ae_compProd_of_ae_ae (measurable_fst measurableSet_Ioc)
    filter_upwards [hae] with x hx using Eventually.of_forall fun _ => hx
  have hboth := Measure.ae_ae_of_ae_compProd (hsum.and hfst)
  -- a general integrand bounded on the relevant region
  have key (u : ℝ → ℝ) (hu : Integrable u ((μ ⊗ₘ κ).map fun p => p.1 + p.2))
      (hstep : ∀ x ∈ Ioc 0 M, ∀ f : ℝ → ℝ, Integrable (fun z => u (x + z)) (κ x) →
        (∀ᵐ z ∂(κ x), x + z ∈ Ioc 0 N) → ∫ z, u (x + z) ∂(κ x) ≤ u x)
      (hu' : Integrable u μ) :
      ∫ x, u x ∂((μ ⊗ₘ κ).map fun p => p.1 + p.2) ≤ ∫ x, u x ∂μ := by
    rw [integral_map hmeas.aemeasurable hu.aestronglyMeasurable]
    have hint : Integrable (fun p : ℝ × ℝ => u (p.1 + p.2)) (μ ⊗ₘ κ) :=
      (integrable_map_measure hu.aestronglyMeasurable hmeas.aemeasurable).mp hu
    rw [Measure.integral_compProd hint]
    apply integral_mono_ae hint.integral_compProd hu'
    filter_upwards [hint.ae_of_compProd, hboth, hae] with x hx hb hxM
    exact hstep x hxM u hx (hb.mono fun z hz => hz.1)
  constructor
  · intro u hm hc
    have hiν := hν.integrable_concave hm hc
    refine key u hiν (fun x hx _ hxi hpos => ?_) (hμ.integrable_concave hm hc)
    obtain ⟨c, -, hstep⟩ := concave_supergradient hc hm
      (show x ∈ interior (Ici (0 : ℝ)) by rw [interior_Ici]; exact hx.1)
    have hbound : ∀ᵐ z ∂(κ x), u (x + z) ≤ u x + c * z := by
      filter_upwards [hpos] with z hz
      have hz' : x + z ∈ Ici (0 : ℝ) := mem_Ici.mpr hz.1.le
      have := hstep x (mem_Ici.mpr hx.1.le) (x + z) hz'
        (by rcases le_total 0 z with h0 | h0
            · exact Or.inl ⟨le_rfl, by linarith⟩
            · exact Or.inr ⟨by linarith, le_rfl⟩)
      linarith
    calc ∫ z, u (x + z) ∂(κ x) ≤ ∫ z, (u x + c * z) ∂(κ x) :=
          integral_mono_ae hxi ((integrable_const _).add ((hmean x).1.const_mul c)) hbound
      _ = u x := by
          rw [integral_add (integrable_const _) ((hmean x).1.const_mul c), integral_const_mul,
            (hmean x).2]
          simp
  · have hiν : Integrable (fun x : ℝ => x) ((μ ⊗ₘ κ).map fun p => p.1 + p.2) :=
      hν.isMoneyLottery.integrable_id
    rw [integral_map hmeas.aemeasurable hiν.aestronglyMeasurable]
    have hint : Integrable (fun p : ℝ × ℝ => p.1 + p.2) (μ ⊗ₘ κ) :=
      (integrable_map_measure hiν.aestronglyMeasurable hmeas.aemeasurable).mp hiν
    rw [Measure.integral_compProd hint]
    apply integral_congr_ae
    filter_upwards [hint.ae_of_compProd] with x hx
    rw [integral_add (integrable_const x) (hmean x).1, (hmean x).2]
    simp

end MWG.ChoiceUnderUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

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

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Examples and exercises on stochastic dominance

MWG, Section 6.D, pp. 197-198 and Exercises 6.D.1, 6.D.3 and 6.D.4, p. 213: the
mean-preserving spread of Example 6.D.2 (Figure 6.D.3), the elementary increase in risk of
Example 6.D.3 (Exercise 6.D.3), and the regions of the three-outcome simplex (outcomes `1`, `2`,
`3` dollars) for first-order dominance, equal means, second-order dominance and condition
(6.D.2).
-/

namespace MWG.ChoiceUnderUncertainty

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

/-- A three-atom lottery integrates every function. -/
theorem integrable_lot3M (a b c x y z : ℝ) (f : ℝ → ℝ) : Integrable f (lot3M a b c x y z) :=
  ((integrable_smul_dirac a x f).add_measure (integrable_smul_dirac b y f)).add_measure
    (integrable_smul_dirac c z f)

/-- The measure of a set under a three-atom lottery. -/
theorem lot3M_apply (a b c x y z : ℝ) {s : Set ℝ} (hs : MeasurableSet s) :
    lot3M a b c x y z s = ENNReal.ofReal a * s.indicator 1 x + ENNReal.ofReal b *
      s.indicator 1 y + ENNReal.ofReal c * s.indicator 1 z := by
  simp only [lot3M, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, Measure.dirac_apply' _ hs]

/-- The three-outcome lottery `(p₁, p₂, p₃)` over `1`, `2`, `3` dollars is an MWG
distribution. -/
theorem lot3M_isMWGDist {p₁ p₂ p₃ : ℝ} (h1 : 0 ≤ p₁) (h2 : 0 ≤ p₂) (h3 : 0 ≤ p₃)
    (hs : p₁ + p₂ + p₃ = 1) : IsMWGDist (lot3M p₁ p₂ p₃ 1 2 3) := by
  have hP : IsProbabilityMeasure (lot3M p₁ p₂ p₃ 1 2 3) := by
    constructor
    rw [lot3M_apply _ _ _ _ _ _ MeasurableSet.univ]
    simp only [indicator_univ, Pi.one_apply, mul_one]
    rw [← ENNReal.ofReal_add h1 h2, ← ENNReal.ofReal_add (by linarith) h3, hs,
      ENNReal.ofReal_one]
  refine ⟨hP, ?_, 3, ?_⟩
  · rw [cdf_eq_real, measureReal_def, lot3M_apply _ _ _ _ _ _ measurableSet_Iic]
    simp only [indicator, mem_Iic, Pi.one_apply]
    norm_num
  · rw [cdf_eq_real, measureReal_def, lot3M_apply _ _ _ _ _ _ measurableSet_Iic]
    simp only [indicator, mem_Iic, Pi.one_apply]
    norm_num
    rw [← ENNReal.ofReal_add h1 h2, ← ENNReal.ofReal_add (by linarith) h3, hs]
    simp

/-- **Exercise 6.D.1(a)** (MWG, p. 213). In the simplex over `1`, `2`, `3` dollars, `L' = q`
first-order stochastically dominates `L = p` iff `q₁ ≤ p₁` and `q₃ ≥ p₃`. -/
theorem exercise_6_D_1a {p₁ p₂ p₃ q₁ q₂ q₃ : ℝ} (hp : p₁ + p₂ + p₃ = 1)
    (hq : q₁ + q₂ + q₃ = 1) (hp1 : 0 ≤ p₁) (hp2 : 0 ≤ p₂) (hp3 : 0 ≤ p₃) (hq1 : 0 ≤ q₁)
    (hq2 : 0 ≤ q₂) (hq3 : 0 ≤ q₃) :
    FOSD (lot3M q₁ q₂ q₃ 1 2 3) (lot3M p₁ p₂ p₃ 1 2 3) ↔ q₁ ≤ p₁ ∧ p₃ ≤ q₃ := by
  constructor
  · intro h
    have s1 := h _ (monotone_step 1)
    have s2 := h _ (monotone_step 2)
    simp only [integral_lot3M hp1 hp2 hp3, integral_lot3M hq1 hq2 hq3, indicator, mem_Ioi,
      Pi.one_apply] at s1 s2
    norm_num at s1 s2
    constructor <;> linarith
  · rintro ⟨h1, h3⟩ u hu
    rw [integral_lot3M hp1 hp2 hp3, integral_lot3M hq1 hq2 hq3]
    have a1 := hu (show (1 : ℝ) ≤ 2 by norm_num)
    have a2 := hu (show (2 : ℝ) ≤ 3 by norm_num)
    have e : q₁ * u 1 + q₂ * u 2 + q₃ * u 3 - (p₁ * u 1 + p₂ * u 2 + p₃ * u 3) =
        (q₃ - p₃) * (u 3 - u 2) + (p₁ - q₁) * (u 2 - u 1) := by
      have : q₂ = 1 - q₁ - q₃ := by linarith
      have : p₂ = 1 - p₁ - p₃ := by linarith
      subst_vars; ring
    nlinarith [mul_nonneg (sub_nonneg.mpr h3) (sub_nonneg.mpr a2),
      mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr a1)]

/-- **Exercise 6.D.1(b)** (MWG, p. 213). The region where `F ≤ G` everywhere is the same:
`q₁ ≤ p₁` and `q₃ ≥ p₃`. -/
theorem exercise_6_D_1b {p₁ p₂ p₃ q₁ q₂ q₃ : ℝ} (hp : p₁ + p₂ + p₃ = 1)
    (hq : q₁ + q₂ + q₃ = 1) (hp1 : 0 ≤ p₁) (hp2 : 0 ≤ p₂) (hp3 : 0 ≤ p₃) (hq1 : 0 ≤ q₁)
    (hq2 : 0 ≤ q₂) (hq3 : 0 ≤ q₃) :
    (∀ x, cdf (lot3M q₁ q₂ q₃ 1 2 3) x ≤ cdf (lot3M p₁ p₂ p₃ 1 2 3) x) ↔
      q₁ ≤ p₁ ∧ p₃ ≤ q₃ := by
  rw [← proposition_6_D_1 (lot3M_isMWGDist hq1 hq2 hq3 hq) (lot3M_isMWGDist hp1 hp2 hp3 hp)]
  exact exercise_6_D_1a hp hq hp1 hp2 hp3 hq1 hq2 hq3

/-- **Exercise 6.D.4(a)** (MWG, p. 213). Two lotteries over `1`, `2`, `3` dollars have the same
mean iff `q₃ - q₁ = p₃ - p₁`: they lie on a line of slope one in the simplex. -/
theorem exercise_6_D_4a {p₁ p₂ p₃ q₁ q₂ q₃ : ℝ} (hp : p₁ + p₂ + p₃ = 1)
    (hq : q₁ + q₂ + q₃ = 1) (hp1 : 0 ≤ p₁) (hp2 : 0 ≤ p₂) (hp3 : 0 ≤ p₃) (hq1 : 0 ≤ q₁)
    (hq2 : 0 ≤ q₂) (hq3 : 0 ≤ q₃) :
    ∫ x, x ∂(lot3M q₁ q₂ q₃ 1 2 3) = ∫ x, x ∂(lot3M p₁ p₂ p₃ 1 2 3) ↔ q₃ - q₁ = p₃ - p₁ := by
  rw [integral_lot3M hp1 hp2 hp3, integral_lot3M hq1 hq2 hq3]
  constructor <;> intro h <;> linarith

/-- **Exercise 6.D.4(b)** (MWG, p. 213). With equal means, `L = p` second-order stochastically
dominates `L' = q` iff `q₁ ≥ p₁`. -/
theorem exercise_6_D_4b {p₁ p₂ p₃ q₁ q₂ q₃ : ℝ} (hp : p₁ + p₂ + p₃ = 1)
    (hq : q₁ + q₂ + q₃ = 1) (hp1 : 0 ≤ p₁) (hp2 : 0 ≤ p₂) (hp3 : 0 ≤ p₃) (hq1 : 0 ≤ q₁)
    (hq2 : 0 ≤ q₂) (hq3 : 0 ≤ q₃) (hmean : q₃ - q₁ = p₃ - p₁) :
    SOSD (lot3M p₁ p₂ p₃ 1 2 3) (lot3M q₁ q₂ q₃ 1 2 3) ↔ p₁ ≤ q₁ := by
  constructor
  · intro h
    obtain ⟨hm, hc⟩ := min_utility_props 2
    have := h _ hm hc
    rw [integral_lot3M hp1 hp2 hp3, integral_lot3M hq1 hq2 hq3] at this
    norm_num at this
    linarith
  · intro h u _ hc
    rw [integral_lot3M hp1 hp2 hp3, integral_lot3M hq1 hq2 hq3]
    have hmid := hc.2 (show (1 : ℝ) ∈ Ici 0 by norm_num) (show (3 : ℝ) ∈ Ici 0 by norm_num)
      (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num)
    norm_num at hmid
    have e : p₁ * u 1 + p₂ * u 2 + p₃ * u 3 - (q₁ * u 1 + q₂ * u 2 + q₃ * u 3) =
        (q₁ - p₁) * (2 * u 2 - u 1 - u 3) := by
      have : q₂ = 1 - q₁ - q₃ := by linarith
      have : p₂ = 1 - p₁ - p₃ := by linarith
      have : q₃ = p₃ - p₁ + q₁ := by linarith
      subst_vars; ring
    nlinarith [mul_nonneg (sub_nonneg.mpr h) (show (0 : ℝ) ≤ 2 * u 2 - u 1 - u 3 by linarith)]

/-- **Exercise 6.D.4(d)** (MWG, p. 213). With equal means, condition (6.D.2) between `p` and `q`
holds iff `q₁ ≥ p₁`: the same region as in (b). -/
theorem exercise_6_D_4d {p₁ p₂ p₃ q₁ q₂ q₃ : ℝ} (hp : p₁ + p₂ + p₃ = 1)
    (hq : q₁ + q₂ + q₃ = 1) (hp1 : 0 ≤ p₁) (hp2 : 0 ≤ p₂) (hp3 : 0 ≤ p₃) (hq1 : 0 ≤ q₁)
    (hq2 : 0 ≤ q₂) (hq3 : 0 ≤ q₃) (hmean : q₃ - q₁ = p₃ - p₁) :
    IntegralCondition (lot3M p₁ p₂ p₃ 1 2 3) (lot3M q₁ q₂ q₃ 1 2 3) ↔ p₁ ≤ q₁ := by
  rw [← proposition_6_D_2_i_iii (lot3M_isMWGDist hp1 hp2 hp3 hp)
    (lot3M_isMWGDist hq1 hq2 hq3 hq)]
  exact exercise_6_D_4b hp hq hp1 hp2 hp3 hq1 hq2 hq3 hmean

/-- **Example 6.D.2** (MWG, p. 197, Figure 6.D.3). `F` gives `2` or `3` dollars with even
probability; spreading `2` to an even chance of `1` or `3` and `3` to `2` or `4` gives the
uniform `G` on `{1, 2, 3, 4}` (represented as `(1/4, 1/4, 1/4)` on `1, 2, 3` plus `1/4` on
`4`). The means agree (`5/2`) and `F` second-order stochastically dominates `G`. -/
theorem example_6_D_2 :
    let G := lot3M (1 / 4) (1 / 4) (1 / 4) 1 2 3 + ENNReal.ofReal (1 / 4) • Measure.dirac 4
    ∫ x, x ∂(binLot (1 / 2) 2 3) = ∫ x, x ∂G ∧ SOSD (binLot (1 / 2) 2 3) G := by
  intro G
  have hG (f : ℝ → ℝ) : ∫ x, f x ∂G = (f 1 + f 2 + f 3 + f 4) / 4 := by
    simp only [G]
    rw [integral_add_measure (integrable_lot3M _ _ _ _ _ _ f) (integrable_smul_dirac _ _ f),
      integral_lot3M (by norm_num) (by norm_num) (by norm_num),
      integral_smul_dirac (by norm_num)]
    ring
  refine ⟨?_, fun u _ hc => ?_⟩
  · rw [hG, integral_binLot _ _ _ _ (by norm_num) (by norm_num)]; norm_num
  · rw [hG, integral_binLot _ _ _ _ (by norm_num) (by norm_num)]
    have m1 := hc.2 (show (1 : ℝ) ∈ Ici 0 by norm_num) (show (3 : ℝ) ∈ Ici 0 by norm_num)
      (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num)
    have m2 := hc.2 (show (2 : ℝ) ∈ Ici 0 by norm_num) (show (4 : ℝ) ∈ Ici 0 by norm_num)
      (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num)
    norm_num at m1 m2
    linarith

/-- **Example 6.D.3** (MWG, p. 198). The elementary increase in risk: the mass that `F` assigns
to `[x', x'']` is moved to the endpoints, with weights `p' = ∫_{[x',x'']} (x'' - t)/(x'' - x')`
and `p'' = ∫_{[x',x'']} (t - x')/(x'' - x')` so that the mean is preserved. -/
noncomputable def elementaryIncrease (μ : Measure ℝ) (a b : ℝ) : Measure ℝ :=
  μ.restrict (Icc a b)ᶜ +
    ENNReal.ofReal (∫ t in Icc a b, (b - t) / (b - a) ∂μ) • Measure.dirac a +
    ENNReal.ofReal (∫ t in Icc a b, (t - a) / (b - a) ∂μ) • Measure.dirac b

/-- Integrals against an elementary increase in risk. -/
theorem integral_elementaryIncrease {μ : Measure ℝ} [IsFiniteMeasure μ] {a b : ℝ} (hab : a < b)
    {f : ℝ → ℝ} (hf : Integrable f μ) :
    ∫ t, f t ∂(elementaryIncrease μ a b) = ∫ t in (Icc a b)ᶜ, f t ∂μ +
      (∫ t in Icc a b, (b - t) / (b - a) ∂μ) * f a +
      (∫ t in Icc a b, (t - a) / (b - a) ∂μ) * f b := by
  have hw1 : 0 ≤ ∫ t in Icc a b, (b - t) / (b - a) ∂μ :=
    setIntegral_nonneg measurableSet_Icc fun t ht => div_nonneg (by linarith [ht.2])
      (by linarith)
  have hw2 : 0 ≤ ∫ t in Icc a b, (t - a) / (b - a) ∂μ :=
    setIntegral_nonneg measurableSet_Icc fun t ht => div_nonneg (by linarith [ht.1])
      (by linarith)
  unfold elementaryIncrease
  rw [integral_add_measure (hf.restrict.add_measure (integrable_smul_dirac _ _ f))
    (integrable_smul_dirac _ _ f), integral_add_measure hf.restrict
    (integrable_smul_dirac _ _ f), integral_smul_dirac hw1, integral_smul_dirac hw2]

/-- **Exercise 6.D.3** (MWG, p. 213) and **Example 6.D.3** (p. 198). An elementary increase in
risk preserves the mean, and `F` second-order stochastically dominates it (for
`0 ≤ x' < x''`). -/
theorem exercise_6_D_3 {μ : Measure ℝ} (hμ : IsMWGDist μ) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a < b) :
    ∫ t, t ∂(elementaryIncrease μ a b) = ∫ t, t ∂μ ∧ SOSD μ (elementaryIncrease μ a b) := by
  have := hμ.1
  have hba : 0 < b - a := by linarith
  have hlin : Integrable (fun t : ℝ => t) μ := hμ.isMoneyLottery.integrable_id
  have hchord_int (c d : ℝ) : Integrable (fun t : ℝ => c * ((b - t) / (b - a)) +
      d * ((t - a) / (b - a))) μ := by
    have h1 : Integrable (fun t : ℝ => (b - t) / (b - a)) μ :=
      ((integrable_const b).sub hlin).div_const _
    have h2 : Integrable (fun t : ℝ => (t - a) / (b - a)) μ :=
      (hlin.sub (integrable_const a)).div_const _
    exact (h1.const_mul c).add (h2.const_mul d)
  have hchord (c d : ℝ) : ∫ t in Icc a b, (c * ((b - t) / (b - a)) + d * ((t - a) / (b - a))) ∂μ
      = (∫ t in Icc a b, (b - t) / (b - a) ∂μ) * c +
        (∫ t in Icc a b, (t - a) / (b - a) ∂μ) * d := by
    rw [integral_add, integral_const_mul, integral_const_mul]
    · ring
    · exact (((integrable_const b).sub hlin).div_const _).restrict.const_mul c
    · exact ((hlin.sub (integrable_const a)).div_const _).restrict.const_mul d
  constructor
  · rw [integral_elementaryIncrease hab hlin,
      ← integral_add_compl (s := Icc a b) measurableSet_Icc hlin]
    have := hchord a b
    have e : ∫ t in Icc a b, (a * ((b - t) / (b - a)) + b * ((t - a) / (b - a))) ∂μ =
        ∫ t in Icc a b, t ∂μ := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro t _; field_simp; ring
    linarith
  · intro u hm hc
    have hu := hμ.integrable_concave hm hc
    rw [integral_elementaryIncrease hab hu,
      ← integral_add_compl (s := Icc a b) measurableSet_Icc hu]
    have hch := hchord (u a) (u b)
    have : ∫ t in Icc a b, (u a * ((b - t) / (b - a)) + u b * ((t - a) / (b - a))) ∂μ ≤
        ∫ t in Icc a b, u t ∂μ := by
      apply setIntegral_mono_on (hchord_int _ _).restrict hu.restrict measurableSet_Icc
      intro t ht
      have hc' := hc.2 (show a ∈ Ici (0 : ℝ) from ha) (show b ∈ Ici (0 : ℝ) by
        exact mem_Ici.mpr (by linarith)) (show 0 ≤ (b - t) / (b - a) from
          div_nonneg (by linarith [ht.2]) hba.le)
        (show 0 ≤ (t - a) / (b - a) from div_nonneg (by linarith [ht.1]) hba.le)
        (by field_simp; ring)
      simp only [smul_eq_mul] at hc'
      have e : (b - t) / (b - a) * a + (t - a) / (b - a) * b = t := by field_simp; ring
      rw [e] at hc'
      linarith
    linarith

/-- The second stage of a compound lottery started at a sure `x`: `(δ_x ⊗ H).map(+)` is `H_x`
shifted by `x`. -/
theorem dirac_compProd_map_add (κ : Kernel ℝ ℝ) [IsMarkovKernel κ] (x : ℝ) :
    ((Measure.dirac x) ⊗ₘ κ).map (fun p => p.1 + p.2) = (κ x).map (fun z => x + z) := by
  ext s hs
  rw [Measure.map_apply (by fun_prop) hs, Measure.map_apply (by fun_prop) hs,
    Measure.dirac_compProd_apply ((by fun_prop : Measurable fun p : ℝ × ℝ => p.1 + p.2) hs)]
  rfl

/-- Real masses of the binary lottery. -/
theorem binLot_real {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x y : ℝ) {s : Set ℝ}
    (hs : MeasurableSet s) :
    (binLot p x y).real s = p * s.indicator 1 x + (1 - p) * s.indicator 1 y := by
  rw [measureReal_def]
  simp only [binLot, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ hs]
  rw [ENNReal.toReal_add (by simp [indicator]; split_ifs <;> simp)
    (by simp [indicator]; split_ifs <;> simp), ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hp0, ENNReal.toReal_ofReal (by linarith)]
  simp only [indicator]
  split_ifs <;> simp

/-- **Example 6.D.2** (MWG, p. 197, Figure 6.D.3). `G` (uniform on `{1, 2, 3, 4}`) is a
mean-preserving spread of `F` (even chance of `2` or `3`): spreading each outcome by `±1` with
even probability (a mean-zero `H_x`). -/
theorem example_6_D_2_spread :
    IsMeanPreservingSpread (binLot (1 / 2) 2 3)
      (lot3M (1 / 4) (1 / 4) (1 / 4) 1 2 3 + ENNReal.ofReal (1 / 4) • Measure.dirac 4) := by
  have hP : IsProbabilityMeasure (binLot (1 / 2) (-1 : ℝ) 1) :=
    binLot_isProbabilityMeasure _ _ _ (by norm_num) (by norm_num)
  refine ⟨Kernel.const ℝ (binLot (1 / 2) (-1) 1), inferInstance, fun x => ⟨?_, ?_⟩, ?_⟩
  · simp only [Kernel.const_apply]
    exact (binLot_isMoneyLottery (S := univ) convex_univ (mem_univ _) (mem_univ _) (1 / 2)
      (by norm_num) (by norm_num)).integrable_id
  · simp only [Kernel.const_apply]
    rw [mean_binLot _ _ _ (by norm_num) (by norm_num)]; norm_num
  · have hF : binLot (1 / 2) (2 : ℝ) 3 = ENNReal.ofReal (1 / 2) • Measure.dirac 2 +
        ENNReal.ofReal (1 - 1 / 2) • Measure.dirac 3 := rfl
    rw [hF, Measure.compProd_add_left, Measure.compProd_smul_left, Measure.compProd_smul_left,
      Measure.map_add _ _ (by fun_prop), Measure.map_smul, Measure.map_smul,
      dirac_compProd_map_add, dirac_compProd_map_add]
    all_goals try fun_prop
    simp only [Kernel.const_apply]
    ext s hs
    have h2 : MeasurableSet ((fun z : ℝ => 2 + z) ⁻¹' s) := (by fun_prop : Measurable _) hs
    have h3 : MeasurableSet ((fun z : ℝ => 3 + z) ⁻¹' s) := (by fun_prop : Measurable _) hs
    simp only [lot3M, binLot, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, Measure.map_apply (by fun_prop : Measurable fun z : ℝ => 2 + z) hs,
      Measure.map_apply (by fun_prop : Measurable fun z : ℝ => 3 + z) hs,
      Measure.dirac_apply' _ hs, Measure.dirac_apply' _ h2, Measure.dirac_apply' _ h3]
    have e1 : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
    have e2 : ENNReal.ofReal (1 / 2) * ENNReal.ofReal (1 / 2) = ENNReal.ofReal (1 / 4) := by
      rw [← ENNReal.ofReal_mul (by norm_num)]; norm_num
    simp only [e1, indicator, mem_preimage, Pi.one_apply]
    norm_num
    have p1 : ((-1 : ℝ) ∈ (fun z : ℝ => 2 + z) ⁻¹' s) = ((1 : ℝ) ∈ s) := by
      simp only [mem_preimage]; norm_num
    have p2 : ((1 : ℝ) ∈ (fun z : ℝ => 2 + z) ⁻¹' s) = ((3 : ℝ) ∈ s) := by
      simp only [mem_preimage]; norm_num
    have p3 : ((-1 : ℝ) ∈ (fun z : ℝ => 3 + z) ⁻¹' s) = ((2 : ℝ) ∈ s) := by
      simp only [mem_preimage]; norm_num
    have p4 : ((1 : ℝ) ∈ (fun z : ℝ => 3 + z) ⁻¹' s) = ((4 : ℝ) ∈ s) := by
      simp only [mem_preimage]; norm_num
    simp only [p1, p2, p3, p4, mul_add]
    rw [← e2]
    split_ifs <;> first | (exfalso; simp_all; done) | ring

/-- **Exercise 6.D.4(c)** (MWG, p. 213). Every mean-preserving spread `q` of `p` (lotteries over
`1`, `2`, `3` dollars) lies in the region of (b): same mean and `q₁ ≥ p₁`. -/
theorem exercise_6_D_4c {p₁ p₂ p₃ q₁ q₂ q₃ : ℝ} (hp : p₁ + p₂ + p₃ = 1)
    (hq : q₁ + q₂ + q₃ = 1) (hp1 : 0 ≤ p₁) (hp2 : 0 ≤ p₂) (hp3 : 0 ≤ p₃) (hq1 : 0 ≤ q₁)
    (hq2 : 0 ≤ q₂) (hq3 : 0 ≤ q₃)
    (h : IsMeanPreservingSpread (lot3M p₁ p₂ p₃ 1 2 3) (lot3M q₁ q₂ q₃ 1 2 3)) :
    q₃ - q₁ = p₃ - p₁ ∧ p₁ ≤ q₁ := by
  obtain ⟨hs, hm⟩ := sosd_of_meanPreservingSpread (lot3M_isMWGDist hp1 hp2 hp3 hp)
    (lot3M_isMWGDist hq1 hq2 hq3 hq) h
  have hmean := (exercise_6_D_4a hp hq hp1 hp2 hp3 hq1 hq2 hq3).mp hm.symm
  exact ⟨hmean, (exercise_6_D_4b hp hq hp1 hp2 hp3 hq1 hq2 hq3 hmean).mp hs⟩

end MWG.ChoiceUnderUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

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

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Martingale couplings of the discretizations

Preparation for Proposition 6.D.2, (i) ⇒ (ii) (MWG, p. 199). If `F` dominates `G` for every
nondecreasing concave utility and the means agree, then on every grid the contraction of `F`
dominates the dilation of `G` in Kreps's finite sense (`SecondOrderDominates`), with equal
means. Kreps's finite theorem `supermartingaleCoupling_of_dominance` (Kreps I, Problem 6.6)
gives a joint table with nonpositive conditional drift; equal means force every row's drift to
vanish, so the table is a martingale coupling. We record it as a finite Borel probability
measure `π` on `ℝ²` with first marginal the contraction, second marginal the dilation and
`∫ φ(x)(y - x) dπ = 0` for every `φ`.
-/

namespace MWG.ChoiceUnderUncertainty

open MeasureTheory ProbabilityTheory Filter Topology Set

/-- The simple lottery `∑_{j<n} m_j δ_{c_j}` (Kreps's `SimpleLottery`). -/
noncomputable def atomLottery (n : ℕ) (c m : ℕ → ℝ) (hm : ∀ j, 0 ≤ m j)
    (hs : ∑ j ∈ Finset.range n, m j = 1) : Kreps.UtilityForMoney.SimpleLottery ℝ where
  weights := ∑ j ∈ Finset.range n, Finsupp.single (c j) (m j)
  nonneg := by
    intro x
    simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.coe_finsetSum, Finset.sum_apply]
    refine Finset.sum_nonneg fun j _ => ?_
    rw [Finsupp.single_apply]
    split_ifs
    · exact hm j
    · exact le_rfl
  total := by
    rw [← Finsupp.sum_finsetSum_index (fun _ => rfl) (fun _ _ _ => rfl)]
    simp only [Finsupp.sum_single_index, hs]

/-- Expected utility of `∑_j m_j δ_{c_j}` is `∑_j m_j u(c_j)`. -/
theorem expectedUtility_atomLottery (n : ℕ) (c m : ℕ → ℝ) (hm : ∀ j, 0 ≤ m j)
    (hs : ∑ j ∈ Finset.range n, m j = 1) (U : ℝ → ℝ) :
    Kreps.UtilityForMoney.ExpectedUtility U (atomLottery n c m hm hs) =
      ∑ j ∈ Finset.range n, m j * U (c j) := by
  unfold Kreps.UtilityForMoney.ExpectedUtility atomLottery
  rw [← Finsupp.sum_finsetSum_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finsupp.sum_single_index (zero_mul _)]

/-- Every support point of `∑_j m_j δ_{c_j}` is one of the `c_j`. -/
theorem mem_support_atomLottery {n : ℕ} {c m : ℕ → ℝ} {hm : ∀ j, 0 ≤ m j}
    {hs : ∑ j ∈ Finset.range n, m j = 1} {x : ℝ}
    (hx : x ∈ (atomLottery n c m hm hs).weights.support) :
    ∃ j ∈ Finset.range n, c j = x := by
  classical
  have := Finsupp.support_finsetSum hx
  rw [Finset.mem_biUnion] at this
  obtain ⟨j, hj, hx'⟩ := this
  exact ⟨j, hj, (Finset.mem_singleton.mp (Finsupp.support_single_subset hx')).symm⟩

/-- Integration against a finite combination of point masses. -/
theorem integral_sum_dirac {ι : Type*} (s : Finset ι) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (a : ι → ℝ × ℝ) (F : ℝ × ℝ → ℝ) :
    ∫ p, F p ∂(∑ i ∈ s, ENNReal.ofReal (w i) • Measure.dirac (a i)) = ∑ i ∈ s, w i * F (a i) := by
  rw [integral_finsetSum_measure fun i _ =>
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hw i), smul_eq_mul]

/-- **Finite martingale coupling of the discretizations.** If `F` (`μ`) dominates `G` (`ν`) for
every nondecreasing concave utility on `ℝ`, with equal means, both concentrated on `(0, N h]`,
there is a finite probability measure on `ℝ²`, concentrated on `[-h, N h + h]²`, whose first
marginal is the contraction of `F`, whose second marginal is the dilation of `G`, and with
`∫ φ(x)(y - x) dπ = 0` for every `φ`. -/
theorem exists_grid_martingale_coupling {μ ν : Measure ℝ} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {h : ℝ} (hh : 0 < h) {N : ℕ}
    (hμ : ∀ᵐ t ∂μ, t ∈ Ioc 0 (N * h)) (hν : ∀ᵐ t ∂ν, t ∈ Ioc 0 (N * h))
    (hdom : ∀ U : ℝ → ℝ, Monotone U → ConcaveOn ℝ univ U → ∫ t, U t ∂ν ≤ ∫ t, U t ∂μ)
    (hmean : ∫ t, t ∂μ = ∫ t, t ∂ν) :
    ∃ π : Measure (ℝ × ℝ), IsProbabilityMeasure π ∧
      (∀ᵐ p ∂π, p.1 ∈ Icc (-h) (N * h + h) ∧ p.2 ∈ Icc (-h) (N * h + h)) ∧
      (∀ g : ℝ → ℝ, ∫ p, g p.1 ∂π =
        ∑ j ∈ Finset.range (N + 1), gridMass μ h j * g (gridCtr μ h j)) ∧
      (∀ g : ℝ → ℝ, ∫ p, g p.2 ∂π =
        ∑ j ∈ Finset.range (N + 1), gridMass ν h j * g (gridPt h j)) ∧
      ∀ φ : ℝ → ℝ, ∫ p, φ p.1 * (p.2 - p.1) ∂π = 0 := by
  classical
  set p := atomLottery (N + 1) (gridCtr μ h) (gridMass μ h) (gridMass_nonneg μ h)
    (gridMass_sum hh hμ) with hp
  set q := atomLottery (N + 1) (gridPt h) (gridMass ν h) (gridMass_nonneg ν h)
    (gridMass_sum hh hν) with hq
  have hdomK : Kreps.UtilityForMoney.SecondOrderDominates p q := by
    intro U hm hc
    rw [hp, hq, expectedUtility_atomLottery, expectedUtility_atomLottery]
    calc _ ≤ ∫ t, U t ∂ν := dilation_le hh hν hc
      _ ≤ ∫ t, U t ∂μ := hdom U hm hc
      _ ≤ _ := le_contraction hh hμ hm hc
  obtain ⟨C, hC⟩ := Kreps.UtilityForMoney.supermartingaleCoupling_of_dominance hdomK
  -- row and column expectations
  have hrow (g : ℝ → ℝ) : ∑ i : p.weights.support, ∑ j : q.weights.support,
      C.mass i j * g i.val = ∑ j ∈ Finset.range (N + 1), gridMass μ h j * g (gridCtr μ h j) := by
    simp only [← Finset.sum_mul, C.row_sum]
    rw [Kreps.UtilityForMoney.sum_support_utility, hp, expectedUtility_atomLottery]
  have hcol (g : ℝ → ℝ) : ∑ i : p.weights.support, ∑ j : q.weights.support,
      C.mass i j * g j.val = ∑ j ∈ Finset.range (N + 1), gridMass ν h j * g (gridPt h j) := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, C.col_sum]
    rw [Kreps.UtilityForMoney.sum_support_utility, hq, expectedUtility_atomLottery]
  -- every row has zero drift
  have hzero : ∀ i : p.weights.support,
      ∑ j : q.weights.support, C.mass i j * (j.val - i.val) = 0 := by
    have htot : ∑ i : p.weights.support,
        ∑ j : q.weights.support, C.mass i j * (j.val - i.val) = 0 := by
      simp only [mul_sub, Finset.sum_sub_distrib]
      rw [hcol (fun x => x), hrow (fun x => x), dilation_mean hh hν, contraction_mean hh hμ,
        hmean, sub_self]
    exact fun i => (Finset.sum_eq_zero_iff_of_nonpos fun i _ => hC i).mp htot i
      (Finset.mem_univ i)
  set π : Measure (ℝ × ℝ) := ∑ ij : p.weights.support × q.weights.support,
    ENNReal.ofReal (C.mass ij.1 ij.2) • Measure.dirac ((ij.1 : ℝ), (ij.2 : ℝ)) with hπ
  have hint (F : ℝ × ℝ → ℝ) : ∫ x, F x ∂π = ∑ i : p.weights.support, ∑ j : q.weights.support,
      C.mass i j * F (i.val, j.val) := by
    rw [hπ, integral_sum_dirac _ (fun ij : p.weights.support × q.weights.support =>
      C.mass ij.1 ij.2) (fun ij => C.nonneg ij.1 ij.2), Fintype.sum_prod_type]
  have hbox (N' : ℕ) (hN' : N' ≤ N) (y : ℝ) (hy : |y - gridPt h N'| ≤ h) :
      y ∈ Icc (-h) (N * h + h) := by
    have h0 : 0 ≤ gridPt h N' := by unfold gridPt; positivity
    have h1 : gridPt h N' ≤ N * h := by
      unfold gridPt
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hN') hh.le
    rw [abs_le] at hy
    exact ⟨by linarith, by linarith⟩
  refine ⟨π, ⟨?_⟩, ?_, fun g => ?_, fun g => ?_, fun φ => ?_⟩
  · rw [hπ, Measure.coe_finsetSum, Finset.sum_apply]
    simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg fun ij _ => C.nonneg ij.1 ij.2, Fintype.sum_prod_type]
    simp only [C.row_sum]
    rw [Kreps.UtilityForMoney.support_mass_sum, ENNReal.ofReal_one]
  · rw [ae_iff, hπ, Measure.coe_finsetSum, Finset.sum_apply]
    refine Finset.sum_eq_zero fun ij _ => ?_
    rw [Measure.smul_apply, smul_eq_mul]
    convert mul_zero _
    rw [dirac_eq_zero_iff_not_mem (by measurability)]
    simp only [mem_ofPred_eq, not_not]
    obtain ⟨k, hk, hck⟩ := mem_support_atomLottery ij.1.property
    obtain ⟨l, hl, hcl⟩ := mem_support_atomLottery ij.2.property
    have hk' : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hl' : l ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
    refine ⟨?_, ?_⟩
    · rw [← hck]; exact hbox k hk' _ (abs_gridCtr_sub_le hh hμ k)
    · rw [← hcl]; exact hbox l hl' _ (by simp [hh.le])
  · rw [hint (fun x => g x.1)]; exact hrow g
  · rw [hint (fun x => g x.2)]; exact hcol g
  · rw [hint (fun x => φ x.1 * (x.2 - x.1))]
    refine Finset.sum_eq_zero fun i _ => ?_
    have e : ∀ j : q.weights.support, C.mass i j * (φ i.val * (j.val - i.val)) =
        φ i.val * (C.mass i j * (j.val - i.val)) := fun j => by ring
    rw [Finset.sum_congr rfl fun j _ => e j, ← Finset.mul_sum, hzero i, mul_zero]

end MWG.ChoiceUnderUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# A martingale coupling as a weak limit

Preparation for Proposition 6.D.2, (i) ⇒ (ii) (MWG, p. 199). For the grids of mesh
`x̄/(n+1)`, the finite martingale couplings of `StrassenFinite` all live on the compact square
`[-x̄, 2x̄]²`. By Prokhorov's theorem (Mathlib: probability measures giving zero mass outside a
fixed compact set form a compact set for the weak topology) the sequence has a cluster point
`π`. Expectations of bounded continuous functions are continuous in the weak topology, and
along the sequence the marginal expectations converge to those under `F` and `G` (uniform
continuity on the square), while the martingale expectations `∫ φ(x)(y - x)` vanish
identically. Hence `π` has marginals `F` and `G` and `∫ φ(x)(y - x) dπ = 0` for every bounded
continuous `φ`.
-/

namespace MWG.ChoiceUnderUncertainty

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal BoundedContinuousFunction

/-- A cluster point of a sequence whose image under a continuous map converges is sent to the
limit. -/
theorem eq_of_mapClusterPt_of_tendsto {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space Y] {P : ℕ → X} {Q : X} (hQ : MapClusterPt Q atTop P) {Φ : X → Y}
    (hΦ : Continuous Φ) {c : Y} (hc : Tendsto (Φ ∘ P) atTop (𝓝 c)) : Φ Q = c := by
  have h1 : MapClusterPt (Φ Q) atTop (Φ ∘ P) := hQ.continuousAt_comp hΦ.continuousAt
  exact eq_of_nhds_neBot (h1.neBot.mono (inf_le_inf_left _ hc))

/-- The hat-weighted averages of `g` at points within `h` of the grid points converge to
`∫ g dF` as the mesh `x̄/(n+1)` goes to zero. -/
theorem tendsto_hat_average {μ : Measure ℝ} [IsProbabilityMeasure μ] {M : ℝ} (hM : 0 < M)
    (hae : ∀ᵐ t ∂μ, t ∈ Ioc 0 M) {g : ℝ → ℝ} (hg : Continuous g) (y : ℕ → ℕ → ℝ)
    (hy : ∀ n j, |y n j - gridPt (M / (n + 1)) j| ≤ M / (n + 1)) :
    Tendsto (fun n : ℕ => ∫ t, ∑ j ∈ Finset.range (n + 1 + 1),
      hatFn (M / (n + 1)) (gridPt (M / (n + 1)) j) t * g (y n j) ∂μ) atTop
      (𝓝 (∫ t, g t ∂μ)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have huc := (isCompact_Icc (a := -M) (b := 2 * M)).uniformContinuousOn_of_continuous
    hg.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, hδg⟩ := huc (ε / 2) (by linarith)
  obtain ⟨n0, hn0⟩ := exists_nat_gt (2 * M / δ)
  refine ⟨n0, fun n hn => ?_⟩
  set h := M / (n + 1) with hh_def
  have hn1 : (0 : ℝ) < n + 1 := by positivity
  have hh : 0 < h := div_pos hM hn1
  have hhM : h ≤ M := div_le_self hM.le (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  have hNh : ((n + 1 : ℕ) : ℝ) * h = M := by rw [hh_def]; push_cast; field_simp
  have h2h : 2 * h < δ := by
    have hn' : (n0 : ℝ) ≤ n := by exact_mod_cast hn
    rw [div_lt_iff₀ hδ] at hn0
    rw [hh_def, ← mul_div_assoc, div_lt_iff₀ hn1]
    nlinarith
  have hae' : ∀ᵐ t ∂μ, t ∈ Ioc 0 (((n + 1 : ℕ) : ℝ) * h) := by rwa [hNh]
  have hint : Integrable (fun t => ∑ j ∈ Finset.range (n + 1 + 1),
      hatFn h (gridPt h j) t * g (y n j)) μ :=
    integrable_finsetSum _ fun j _ =>
      (integrable_of_continuous_ae_Ioc hae (continuous_hatFn _ _)).mul_const _
  rw [Real.dist_eq, ← integral_sub hint (integrable_of_continuous_ae_Ioc hae hg)]
  have hbound : ∀ᵐ t ∂μ, ‖∑ j ∈ Finset.range (n + 1 + 1),
      hatFn h (gridPt h j) t * g (y n j) - g t‖ ≤ ε / 2 := by
    filter_upwards [hae'] with t ht
    rw [Real.norm_eq_abs]
    refine hatFn_sum_approx hh ht.1 ht.2 g (y n) fun j hj hp => ?_
    have hjN : (j : ℝ) ≤ n + 1 := by
      have := Finset.mem_range.mp hj
      exact_mod_cast Nat.lt_succ_iff.mp this
    have hx0 : 0 ≤ gridPt h j := by unfold gridPt; positivity
    have hxM : gridPt h j ≤ M := by
      rw [← hNh]; unfold gridPt; push_cast
      exact mul_le_mul_of_nonneg_right hjN hh.le
    have h1 := abs_sub_lt_of_hatFn_pos hh hp
    have h2 := hy n j
    rw [abs_lt] at h1
    rw [abs_le] at h2
    have hmemy : y n j ∈ Icc (-M) (2 * M) := ⟨by linarith, by linarith⟩
    have hmemt : t ∈ Icc (-M) (2 * M) := ⟨by linarith [ht.1], by linarith [ht.2, hNh]⟩
    have hd : dist (y n j) t < δ := by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith
    have := hδg _ hmemy _ hmemt hd
    rw [Real.dist_eq] at this
    exact this.le
  have := norm_integral_le_of_norm_le_const hbound
  rw [probReal_univ, mul_one, Real.norm_eq_abs] at this
  linarith

/-- The truncation `max(-c, min(z, c))`. -/
noncomputable def truncAt (c z : ℝ) : ℝ := max (-c) (min z c)

theorem continuous_truncAt (c : ℝ) : Continuous (truncAt c) := by
  unfold truncAt; fun_prop

theorem abs_truncAt_le {c : ℝ} (hc : 0 ≤ c) (z : ℝ) : |truncAt c z| ≤ c := by
  unfold truncAt
  rw [abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_right _ _)

theorem truncAt_eq {c z : ℝ} (h : |z| ≤ c) : truncAt c z = z := by
  unfold truncAt
  rw [abs_le] at h
  rw [min_eq_left h.2, max_eq_right h.1]

/-- **Existence of a martingale coupling.** If `F` (`μ`) dominates `G` (`ν`) for every
nondecreasing concave utility on `ℝ`, with equal means, both concentrated on `(0, x̄]`, there
is a Borel probability measure `π` on `ℝ²` concentrated on `[-x̄, 2x̄]²` with marginals `F` and
`G` and `∫ φ(x)(y - x) dπ = 0` for every bounded continuous `φ`. -/
theorem exists_martingale_coupling {μ ν : Measure ℝ} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {M : ℝ} (hM : 0 < M)
    (hμ : ∀ᵐ t ∂μ, t ∈ Ioc 0 M) (hν : ∀ᵐ t ∂ν, t ∈ Ioc 0 M)
    (hdom : ∀ U : ℝ → ℝ, Monotone U → ConcaveOn ℝ univ U → ∫ t, U t ∂ν ≤ ∫ t, U t ∂μ)
    (hmean : ∫ t, t ∂μ = ∫ t, t ∂ν) :
    ∃ π : Measure (ℝ × ℝ), IsProbabilityMeasure π ∧
      (∀ᵐ p ∂π, p.1 ∈ Icc (-M) (2 * M) ∧ p.2 ∈ Icc (-M) (2 * M)) ∧
      π.map Prod.fst = μ ∧ π.map Prod.snd = ν ∧
      ∀ φ : ℝ →ᵇ ℝ, ∫ p, φ p.1 * (p.2 - p.1) ∂π = 0 := by
  set K : Set (ℝ × ℝ) := Icc (-M) (2 * M) ×ˢ Icc (-M) (2 * M) with hK
  have hKc : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hfin (n : ℕ) := exists_grid_martingale_coupling (μ := μ) (ν := ν)
    (h := M / (n + 1)) (div_pos hM (by positivity)) (N := n + 1)
    (by
      have : ((n + 1 : ℕ) : ℝ) * (M / (n + 1)) = M := by push_cast; field_simp
      rwa [this])
    (by
      have : ((n + 1 : ℕ) : ℝ) * (M / (n + 1)) = M := by push_cast; field_simp
      rwa [this])
    hdom hmean
  choose π hprob hsupp hfst hsnd hmart using hfin
  have hMn (n : ℕ) : M / (n + 1) ≤ M :=
    div_le_self hM.le (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  have hNh (n : ℕ) : ((n + 1 : ℕ) : ℝ) * (M / (n + 1)) = M := by push_cast; field_simp
  have hπK (n : ℕ) : ∀ᵐ p ∂(π n), p ∈ K := by
    filter_upwards [hsupp n] with p hp
    rw [hNh] at hp
    have := hMn n
    have h0 : 0 ≤ M / (n + 1) := div_nonneg hM.le (by positivity)
    exact ⟨⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩,
      ⟨by linarith [hp.2.1], by linarith [hp.2.2]⟩⟩
  let P : ℕ → ProbabilityMeasure (ℝ × ℝ) := fun n => ⟨π n, hprob n⟩
  set S : Set (ProbabilityMeasure (ℝ × ℝ)) := {R | ∀ _ : ℕ, R Kᶜ ≤ (fun _ : ℕ => (0 : ℝ≥0)) 0}
  have hS : IsCompact S :=
    isCompact_setOfPred_probabilityMeasure_mass_eq_compl_isCompact_le (u := fun _ => 0)
      (K := fun _ => K) tendsto_const_nhds (fun _ => hKc) (Or.inr monotone_const)
  have hPS (n : ℕ) : P n ∈ S := by
    intro _
    rw [nonpos_iff_eq_zero, ProbabilityMeasure.null_iff_toMeasure_null]
    exact measure_eq_zero_iff_ae_notMem.mpr ((hπK n).mono fun p hp hn => hn hp)
  obtain ⟨Q, hQS, hQ⟩ := hS.exists_mapClusterPt (f := atTop) (u := P)
    (tendsto_principal.mpr (Eventually.of_forall hPS))
  have hQK : ∀ᵐ p ∂(Q : Measure (ℝ × ℝ)), p ∈ K := by
    have := hQS 0
    rw [nonpos_iff_eq_zero, ProbabilityMeasure.null_iff_toMeasure_null] at this
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp this] with p hp
    exact not_not.mp hp
  -- passing a bounded continuous test function to the limit
  have hlim (F : ℝ × ℝ →ᵇ ℝ) (c : ℝ)
      (hc : Tendsto (fun n => ∫ p, F p ∂(π n)) atTop (𝓝 c)) :
      ∫ p, F p ∂(Q : Measure (ℝ × ℝ)) = c :=
    eq_of_mapClusterPt_of_tendsto hQ
      (ProbabilityMeasure.continuous_integral_boundedContinuousFunction F) hc
  have hQprob : IsProbabilityMeasure (Q : Measure (ℝ × ℝ)) := inferInstance
  refine ⟨Q, hQprob, hQK.mono fun p hp => hp, ?_, ?_, fun φ => ?_⟩
  · apply ext_of_forall_integral_eq_of_IsFiniteMeasure
    intro f
    rw [integral_map measurable_fst.aemeasurable f.continuous.aestronglyMeasurable]
    refine hlim (f.compContinuous ⟨Prod.fst, continuous_fst⟩) _ ?_
    simp only [BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mk]
    have e : (fun n => ∫ p, f p.1 ∂(π n)) = fun n => ∫ t, ∑ j ∈ Finset.range (n + 1 + 1),
        hatFn (M / (n + 1)) (gridPt (M / (n + 1)) j) t * f (gridCtr μ (M / (n + 1)) j) ∂μ :=
      funext fun n => by rw [hfst n f, sum_gridMass_mul (by rw [hNh]; exact hμ)]
    rw [e]
    exact tendsto_hat_average hM hμ f.continuous (fun n j => gridCtr μ (M / (n + 1)) j)
      fun n j => abs_gridCtr_sub_le (div_pos hM (by positivity)) (N := n + 1)
        (by rw [hNh]; exact hμ) j
  · apply ext_of_forall_integral_eq_of_IsFiniteMeasure
    intro f
    rw [integral_map measurable_snd.aemeasurable f.continuous.aestronglyMeasurable]
    refine hlim (f.compContinuous ⟨Prod.snd, continuous_snd⟩) _ ?_
    simp only [BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mk]
    have e : (fun n => ∫ p, f p.2 ∂(π n)) = fun n => ∫ t, ∑ j ∈ Finset.range (n + 1 + 1),
        hatFn (M / (n + 1)) (gridPt (M / (n + 1)) j) t * f (gridPt (M / (n + 1)) j) ∂ν :=
      funext fun n => by rw [hsnd n f, sum_gridMass_mul (by rw [hNh]; exact hν)]
    rw [e]
    exact tendsto_hat_average hM hν f.continuous (fun n j => gridPt (M / (n + 1)) j)
      fun n j => by simp [div_nonneg hM.le (by positivity : (0 : ℝ) ≤ n + 1)]
  · -- the truncated martingale test function
    set c := 3 * M
    let G : ℝ × ℝ →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
      (fun p => φ p.1 * truncAt c (p.2 - p.1))
      ((φ.continuous.comp continuous_fst).mul ((continuous_truncAt c).comp
        (continuous_snd.sub continuous_fst))) (‖φ‖ * c) (fun p => by
          rw [norm_mul]
          exact mul_le_mul (φ.norm_coe_le_norm _) (by
            rw [Real.norm_eq_abs]; exact abs_truncAt_le (by linarith) _)
            (norm_nonneg _) (norm_nonneg _))
    have hGeq (R : Measure (ℝ × ℝ)) (hR : ∀ᵐ p ∂R, p ∈ K) :
        ∫ p, G p ∂R = ∫ p, φ p.1 * (p.2 - p.1) ∂R := by
      apply integral_congr_ae
      filter_upwards [hR] with p hp
      change φ p.1 * truncAt c (p.2 - p.1) = _
      rw [truncAt_eq]
      rw [abs_le]
      obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hp
      constructor <;> linarith
    rw [← hGeq _ hQK]
    refine hlim G 0 ?_
    simp_rw [hGeq _ (hπK _), hmart]
    exact tendsto_const_nhds

end MWG.ChoiceUnderUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Second-order dominance implies a mean-preserving spread

MWG, Section 6.D, pp. 198-199: Proposition 6.D.2, (i) ⇒ (ii), stated in the book without
proof (the Rothschild-Stiglitz / Strassen theorem), the converse claim of Example 6.D.2, and
the remaining inclusion of Exercise 6.D.4(c). With these, Proposition 6.D.2 is proved in full:
for MWG distributions with the same mean, (i) second-order dominance, (ii) mean-preserving
spread and (iii) the integral condition (6.D.2) are equivalent.

Proof of (i) ⇒ (ii). `StrassenLimit` gives a probability measure `π` on `ℝ²` with marginals `F`
and `G`, concentrated on a compact square, with `∫ φ(x)(y - x) dπ = 0` for every bounded
continuous `φ`. Writing `π` in the coordinates `(x, z) = (x, y - x)` and disintegrating with
respect to `x` (Mathlib's conditional kernel on the standard Borel space `ℝ`) gives a Markov
kernel `H_x`; the identity with smooth compactly supported `φ` shows that `x ↦ ∫ z dH_x(z)`
vanishes `F`-almost everywhere (Mathlib's `ae_eq_zero_of_integral_contDiff_smul_eq_zero`).
Replacing `H_x` by `δ₀` on the null set where this fails gives MWG's compound lottery: `G` is the
law of `x + z` with `x ~ F` and `z ~ H_x`, `E[z | x] = 0` for every `x`.
-/

namespace MWG.ChoiceUnderUncertainty

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BoundedContinuousFunction ContDiff

/-- **Proposition 6.D.2**, (i) ⇒ (ii) (MWG, p. 199), and the converse claim of **Example
6.D.2** (p. 198). If `F` second-order stochastically dominates `G` and the means agree, then `G`
is a mean-preserving spread of `F`: there is a Markov kernel `H_x` with `∫ z dH_x(z) = 0` for
every `x` such that `G` is the law of `x + z` when `x ~ F` and `z ~ H_x`. -/
theorem proposition_6_D_2_i_ii {μ ν : Measure ℝ} (hμ : IsMWGDist μ) (hν : IsMWGDist ν)
    (hmean : ∫ x, x ∂μ = ∫ x, x ∂ν) (h : SOSD μ ν) : IsMeanPreservingSpread μ ν := by
  have := hμ.1
  have := hν.1
  obtain ⟨M₁, hM₁, hae₁⟩ := hμ.ae_mem
  obtain ⟨M₂, -, hae₂⟩ := hν.ae_mem
  set M := max M₁ M₂
  have hM : 0 < M := lt_of_lt_of_le hM₁ (le_max_left _ _)
  have hμM : ∀ᵐ t ∂μ, t ∈ Ioc 0 M :=
    hae₁.mono fun t ht => ⟨ht.1, ht.2.trans (le_max_left _ _)⟩
  have hνM : ∀ᵐ t ∂ν, t ∈ Ioc 0 M :=
    hae₂.mono fun t ht => ⟨ht.1, ht.2.trans (le_max_right _ _)⟩
  have hdom : ∀ U : ℝ → ℝ, Monotone U → ConcaveOn ℝ univ U → ∫ t, U t ∂ν ≤ ∫ t, U t ∂μ :=
    fun U hm hc => h U (hm.monotoneOn _) (hc.subset (subset_univ _) (convex_Ici 0))
  obtain ⟨π, hπ, hπK, hπ1, hπ2, hπm⟩ := exists_martingale_coupling hM hμM hνM hdom hmean
  -- the coupling in the coordinates `(x, y - x)`
  set f : ℝ × ℝ → ℝ × ℝ := fun p => (p.1, p.2 - p.1) with hf
  have mf : Measurable f := by fun_prop
  set ρ : Measure (ℝ × ℝ) := π.map f
  have hρ : IsProbabilityMeasure ρ := inferInstance
  have hρfst : ρ.fst = μ := by
    rw [Measure.fst, Measure.map_map measurable_fst mf]
    exact hπ1
  have hρsum : ρ.map (fun p => p.1 + p.2) = ν := by
    rw [Measure.map_map (by fun_prop) mf, ← hπ2]
    congr 1
    funext p
    simp [f]
  have hρK : ∀ᵐ p ∂ρ, p.2 ∈ Icc (-(3 * M)) (3 * M) := by
    rw [ae_map_iff mf.aemeasurable (measurableSet_Icc.preimage measurable_snd)]
    filter_upwards [hπK] with p hp
    obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hp
    exact ⟨by simp only [f]; linarith, by simp only [f]; linarith⟩
  have hρm (φ : ℝ →ᵇ ℝ) : ∫ p, φ p.1 * p.2 ∂ρ = 0 := by
    rw [integral_map mf.aemeasurable (by fun_prop)]
    exact hπm φ
  set κ₀ := ρ.condKernel
  have hdis : ρ.fst ⊗ₘ κ₀ = ρ := ρ.disintegrate κ₀
  rw [hρfst] at hdis
  -- the conditional laws are concentrated on a bounded interval
  have hbd : ∀ᵐ x ∂μ, κ₀ x (Icc (-(3 * M)) (3 * M))ᶜ = 0 := by
    have := Measure.ae_ae_of_ae_compProd (μ := μ) (κ := κ₀)
      (p := fun p : ℝ × ℝ => p.2 ∈ Icc (-(3 * M)) (3 * M)) (by rw [hdis]; exact hρK)
    filter_upwards [this] with x hx
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hx] with z hz
    exact fun hn => hn hz
  have hint_of (x : ℝ) (hx : κ₀ x (Icc (-(3 * M)) (3 * M))ᶜ = 0) :
      Integrable (fun z : ℝ => z) (κ₀ x) := by
    refine Integrable.of_bound measurable_id.aestronglyMeasurable (3 * M) ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hx] with z hz
    rw [Real.norm_eq_abs, abs_le]
    exact not_not.mp hz
  -- the conditional mean
  set m : ℝ → ℝ := fun x => ∫ z, z ∂(κ₀ x) with hm
  have mm : Measurable m := (stronglyMeasurable_id.integral_kernel (κ := κ₀)).measurable
  have hmb : ∀ᵐ x ∂μ, |m x| ≤ 3 * M := by
    filter_upwards [hbd] with x hx
    have hb : ∀ᵐ z ∂(κ₀ x), ‖z‖ ≤ 3 * M := by
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp hx] with z hz
      rw [Real.norm_eq_abs, abs_le]
      exact not_not.mp hz
    have := norm_integral_le_of_norm_le_const hb
    rw [probReal_univ, mul_one, Real.norm_eq_abs] at this
    exact this
  have hmi : Integrable m μ :=
    Integrable.of_bound mm.aestronglyMeasurable (3 * M) (hmb.mono fun x hx => by
      rw [Real.norm_eq_abs]; exact hx)
  have hm0 : ∀ᵐ x ∂μ, m x = 0 := by
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hmi.locallyIntegrable fun g hg hgs => ?_
    obtain ⟨C, hC⟩ := hg.continuous.bounded_above_of_compact_support hgs
    set φ : ℝ →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup g hg.continuous C hC
    have hφ : ∀ x, φ x = g x := fun _ => rfl
    have hgi : Integrable (fun p : ℝ × ℝ => g p.1 * p.2) (μ ⊗ₘ κ₀) := by
      rw [hdis]
      refine Integrable.of_bound (by fun_prop) (C * (3 * M)) ?_
      filter_upwards [hρK] with p hp
      rw [norm_mul]
      exact mul_le_mul (hC _) (by rw [Real.norm_eq_abs, abs_le]; exact hp) (norm_nonneg _)
        ((norm_nonneg _).trans (hC 0))
    have := hρm φ
    simp only [hφ] at this
    rw [← hdis, Measure.integral_compProd hgi] at this
    rw [← this]
    refine integral_congr_ae ?_
    filter_upwards [hbd] with x hx
    rw [smul_eq_mul, hm, ← integral_const_mul]
  -- the spread kernel
  set G := {x : ℝ | κ₀ x (Icc (-(3 * M)) (3 * M))ᶜ = 0} ∩ {x | m x = 0}
  have hG : MeasurableSet G :=
    ((Kernel.measurable_coe κ₀ measurableSet_Icc.compl) (measurableSet_singleton 0)).inter
      (mm (measurableSet_singleton 0))
  set κ := Kernel.piecewise hG κ₀ (Kernel.const ℝ (Measure.dirac 0))
  refine ⟨κ, inferInstance, fun x => ?_, ?_⟩
  · rw [Kernel.piecewise_apply]
    split_ifs with hx
    · exact ⟨hint_of x hx.1, hx.2⟩
    · simp only [Kernel.const_apply]
      exact ⟨integrable_dirac (by simp), by simp⟩
  · have hae : κ =ᵐ[μ] κ₀ := by
      filter_upwards [hbd, hm0] with x h1 h2
      rw [Kernel.piecewise_apply]
      exact ite_eq_left_iff.mpr fun hn => absurd (show x ∈ G from ⟨h1, h2⟩) hn
    rw [Measure.compProd_congr hae, hdis, hρsum]

/-- **Proposition 6.D.2** (MWG, p. 199), in full. For MWG distributions `F` and `G` with the
same mean, (i) `F` second-order stochastically dominates `G`, (ii) `G` is a mean-preserving
spread of `F`, and (iii) the integral condition (6.D.2) holds, are equivalent. -/
theorem proposition_6_D_2 {μ ν : Measure ℝ} (hμ : IsMWGDist μ) (hν : IsMWGDist ν)
    (hmean : ∫ x, x ∂μ = ∫ x, x ∂ν) :
    (SOSD μ ν ↔ IsMeanPreservingSpread μ ν) ∧ (SOSD μ ν ↔ IntegralCondition μ ν) :=
  ⟨⟨proposition_6_D_2_i_ii hμ hν hmean, fun h => (sosd_of_meanPreservingSpread hμ hν h).1⟩,
    proposition_6_D_2_i_iii hμ hν⟩

/-- **Example 6.D.2** (MWG, p. 198), "saying that `G` is a mean-preserving spread of `F` is
equivalent to saying that `F` second-order stochastically dominates `G`" (distributions with the
same mean, as throughout Definition 6.D.2). -/
theorem example_6_D_2_equivalence {μ ν : Measure ℝ} (hμ : IsMWGDist μ) (hν : IsMWGDist ν)
    (hmean : ∫ x, x ∂μ = ∫ x, x ∂ν) : IsMeanPreservingSpread μ ν ↔ SOSD μ ν :=
  (proposition_6_D_2 hμ hν hmean).1.symm

/-- **Exercise 6.D.4(c)** (MWG, p. 213), the other inclusion: every lottery `q` over `1`, `2`, `3`
dollars in the region of (b) (same mean as `p`, `q₁ ≥ p₁`) is a mean-preserving spread of `p`.
With `exercise_6_D_4c`, the mean-preserving spreads of `p` are exactly that region. -/
theorem exercise_6_D_4c_converse {p₁ p₂ p₃ q₁ q₂ q₃ : ℝ} (hp : p₁ + p₂ + p₃ = 1)
    (hq : q₁ + q₂ + q₃ = 1) (hp1 : 0 ≤ p₁) (hp2 : 0 ≤ p₂) (hp3 : 0 ≤ p₃) (hq1 : 0 ≤ q₁)
    (hq2 : 0 ≤ q₂) (hq3 : 0 ≤ q₃) (hmean : q₃ - q₁ = p₃ - p₁) (h1 : p₁ ≤ q₁) :
    IsMeanPreservingSpread (lot3M p₁ p₂ p₃ 1 2 3) (lot3M q₁ q₂ q₃ 1 2 3) := by
  have hF := lot3M_isMWGDist hp1 hp2 hp3 hp
  have hG := lot3M_isMWGDist hq1 hq2 hq3 hq
  have hm := (exercise_6_D_4a hp hq hp1 hp2 hp3 hq1 hq2 hq3).mpr hmean
  exact proposition_6_D_2_i_ii hF hG hm.symm
    ((exercise_6_D_4b hp hq hp1 hp2 hp3 hq1 hq2 hq3 hmean).mpr h1)

/-- **Exercise 6.D.4(c)** (MWG, p. 213), both inclusions: the mean-preserving spreads of `p` in
the simplex over `1`, `2`, `3` dollars are exactly the region of (b). -/
theorem exercise_6_D_4c_iff {p₁ p₂ p₃ q₁ q₂ q₃ : ℝ} (hp : p₁ + p₂ + p₃ = 1)
    (hq : q₁ + q₂ + q₃ = 1) (hp1 : 0 ≤ p₁) (hp2 : 0 ≤ p₂) (hp3 : 0 ≤ p₃) (hq1 : 0 ≤ q₁)
    (hq2 : 0 ≤ q₂) (hq3 : 0 ≤ q₃) :
    IsMeanPreservingSpread (lot3M p₁ p₂ p₃ 1 2 3) (lot3M q₁ q₂ q₃ 1 2 3) ↔
      q₃ - q₁ = p₃ - p₁ ∧ p₁ ≤ q₁ :=
  ⟨exercise_6_D_4c hp hq hp1 hp2 hp3 hq1 hq2 hq3, fun h =>
    exercise_6_D_4c_converse hp hq hp1 hp2 hp3 hq1 hq2 hq3 h.1 h.2⟩

/-- A concrete instance of Proposition 6.D.2, (i) ⇒ (ii), with a distribution that is not of
the explicit form of Example 6.D.2: `q = (1/2, 0, 1/2)` is a mean-preserving spread of the sure
`2` dollars `p = (0, 1, 0)`. -/
theorem exercise_6_D_4c_instance :
    IsMeanPreservingSpread (lot3M 0 1 0 1 2 3) (lot3M (1 / 2) 0 (1 / 2) 1 2 3) :=
  exercise_6_D_4c_converse (by norm_num) (by norm_num) le_rfl zero_le_one le_rfl
    (by norm_num) le_rfl (by norm_num) (by norm_num) (by norm_num)

end MWG.ChoiceUnderUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# State-dependent utility

MWG, Section 6.E, pp. 199-204, and Exercises 6.E.1-6.E.3, pp. 213-214: random variables and
their distributions (Definition 6.E.1), the extended expected utility representation
(Definition 6.E.2), the marginal rate of substitution on the certainty line, Example 6.E.1
(insurance with state-dependent utility), the extended independence axiom (Definition 6.E.3),
Proposition 6.E.1, the sure-thing axiom (Definition 6.E.4), and risk aversion as concavity of
every `u_s`.

Lotteries `L = (F₁, …, F_S)` are Kreps's horse lotteries `S → SimpleLottery X` (state-contingent
simple lotteries over an arbitrary prize set, the setting of MWG's proof), and Proposition 6.E.1
follows from Kreps's Proposition 5.12 through `mixtureAxioms_of_mwg`. As printed, for arbitrary
distribution functions in each state, Proposition 6.E.1 contains the case `S = 1`, i.e. the claim
(6.C.1), which fails (`expectedUtility_6_C_1_counterexample`). Proposition 6.E.2 (sure-thing
axiom and continuity with at least three states imply an additively separable representation)
is Debreu's additive representation theorem; it is proved, with the needed correction (three
*essential* states), in `DebreuAdditive`.
-/

namespace MWG.ChoiceUnderUncertainty

open MeasureTheory ProbabilityTheory Filter Topology Set Kreps.ChoiceUnderUncertainty
open scoped ENNReal

/-- **Definition 6.E.1** (MWG, p. 200). The money lottery induced by a random variable
`g : S → ℝ₊` with state probabilities `π`: `∑_s π_s δ_{g(s)}`. -/
noncomputable def inducedLaw {S : Type*} [Fintype S] (π : S → ℝ) (g : S → ℝ) : Measure ℝ :=
  ∑ s, ENNReal.ofReal (π s) • Measure.dirac (g s)

/-- **p. 200**. The distribution function of the induced lottery is
`F(x) = ∑_{s : g(s) ≤ x} π_s`. -/
theorem inducedLaw_cdf {S : Type*} [Fintype S] {π : S → ℝ} (hπ : ∀ s, 0 ≤ π s) (g : S → ℝ)
    (x : ℝ) :
    (inducedLaw π g).real (Iic x) = ∑ s ∈ Finset.univ.filter (fun s => g s ≤ x), π s := by
  rw [measureReal_def]
  simp only [inducedLaw, Measure.coe_finsetSum, Finset.sum_apply, Measure.coe_smul,
    Pi.smul_apply, smul_eq_mul, Measure.dirac_apply' _ measurableSet_Iic]
  rw [ENNReal.toReal_sum (fun s _ => by
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by simp [indicator]; split_ifs <;> simp))]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases h : g s ≤ x <;> simp [indicator, h, hπ s]

/-- Expectations under the induced lottery: `∫ u dF = ∑_s π_s u(g(s))` (footnote 24). -/
theorem integral_inducedLaw {S : Type*} [Fintype S] {π : S → ℝ} (hπ : ∀ s, 0 ≤ π s)
    (g : S → ℝ) (u : ℝ → ℝ) : ∫ x, u x ∂(inducedLaw π g) = ∑ s, π s * u (g s) := by
  unfold inducedLaw
  rw [integral_finsetSum_measure (fun s _ => integrable_smul_dirac _ _ u)]
  exact Finset.sum_congr rfl fun s _ => integral_smul_dirac (hπ s) _ u

/-- **Definition 6.E.2** (MWG, p. 201). `≿` on `ℝ^S_+` has an extended expected utility
representation with state probabilities `π`. -/
def HasExtendedEU {S : Type*} [Fintype S] (π : S → ℝ) (r : (S → ℝ) → (S → ℝ) → Prop) : Prop :=
  ∃ u : S → ℝ → ℝ, ∀ x x', (∀ s, 0 ≤ x s) → (∀ s, 0 ≤ x' s) →
    (r x x' ↔ ∑ s, π s * u s (x' s) ≤ ∑ s, π s * u s (x s))

/-- **Footnote 24** (MWG, p. 201). With a state-uniform `u`, `∑ π_s u(x_s)` is the expected
utility of the money lottery induced by `(x₁, …, x_S)`. -/
theorem footnote_6_24 {S : Type*} [Fintype S] {π : S → ℝ} (hπ : ∀ s, 0 ≤ π s) (u : ℝ → ℝ)
    (x : S → ℝ) : ∑ s, π s * u (x s) = ∫ t, u t ∂(inducedLaw π x) :=
  (integral_inducedLaw hπ x u).symm

/-- **p. 202**. Since `π_s > 0`, the probabilities can be absorbed into the state utilities:
an additively separable `∑_s u_s(x_s)` is an extended expected utility with `ũ_s = u_s/π_s`. -/
theorem absorb_probabilities {S : Type*} [Fintype S] {π : S → ℝ} (hπ : ∀ s, 0 < π s)
    (u : S → ℝ → ℝ) (x : S → ℝ) : ∑ s, π s * ((1 / π s) * u s (x s)) = ∑ s, u s (x s) :=
  Finset.sum_congr rfl fun s _ => by
    rw [one_div, ← mul_assoc, mul_inv_cancel₀ (hπ s).ne', one_mul]

/-- **p. 201, Figure 6.E.1**. On the certainty line `x₁ = x₂ = x̄`, the gradient of
`π₁u₁(x₁) + π₂u₂(x₂)` is `(π₁u₁'(x̄), π₂u₂'(x̄))`, so the indifference curve has slope
`-π₁u₁'(x̄)/(π₂u₂'(x̄))`; with state-uniform utility the slope is `-π₁/π₂` at every point. -/
theorem certainty_line_mrs {π₁ π₂ : ℝ} {u₁ u₂ : ℝ → ℝ} {x : ℝ} (h1 : DifferentiableAt ℝ u₁ x)
    (h2 : DifferentiableAt ℝ u₂ x) :
    deriv (fun y => π₁ * u₁ y + π₂ * u₂ x) x = π₁ * deriv u₁ x ∧
      deriv (fun y => π₁ * u₁ x + π₂ * u₂ y) x = π₂ * deriv u₂ x ∧
      (u₁ = u₂ → deriv u₂ x ≠ 0 → π₂ ≠ 0 →
        π₁ * deriv u₁ x / (π₂ * deriv u₂ x) = π₁ / π₂) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [deriv_add_const, deriv_const_mul _ h1]
  · rw [deriv_const_add, deriv_const_mul _ h2]
  · rintro rfl hd hπ
    field_simp

/-- **Example 6.E.1** (MWG, pp. 201-202), state-uniform case. A risk-averse expected utility
maximizer with state-uniform utility insures completely when any actuarially fair contract
`π₁z₁ + π₂z₂ = 0` is available: the certain wealth `w - π₂D` is optimal. -/
theorem example_6_E_1_uniform {u : ℝ → ℝ} (hc : ConcaveOn ℝ univ u) {π₁ π₂ : ℝ}
    (h1 : 0 ≤ π₁) (h2 : 0 ≤ π₂) (hs : π₁ + π₂ = 1) (w D z₁ z₂ : ℝ)
    (hfair : π₁ * z₁ + π₂ * z₂ = 0) :
    π₁ * u (w + z₁) + π₂ * u (w - D + z₂) ≤ π₁ * u (w - π₂ * D) + π₂ * u (w - π₂ * D) := by
  have := hc.2 (mem_univ (w + z₁)) (mem_univ (w - D + z₂)) h1 h2 hs
  simp only [smul_eq_mul] at this
  have e : π₁ * (w + z₁) + π₂ * (w - D + z₂) = w - π₂ * D := by
    have : π₁ * w + π₂ * w = w := by rw [← add_mul, hs, one_mul]
    linear_combination this + hfair
  rw [e] at this
  rw [← add_mul, hs, one_mul]
  exact this

/-- **Example 6.E.1** (MWG, p. 202, Figure 6.E.2(b)), state-dependent case. With `π₁ = π₂ = 1/2`,
`u₁(x) = 2√x` and `u₂(x) = √x`, the fair contract `(0.6, -0.6)` from the certain point
`(1, 1)` is strictly preferred to full insurance: more wealth in the state where marginal
utility is higher. -/
theorem example_6_E_1_dependent :
    1 / 2 * (2 * Real.sqrt 1) + 1 / 2 * Real.sqrt 1 <
      1 / 2 * (2 * Real.sqrt (1 + 3 / 5)) + 1 / 2 * Real.sqrt (1 - 3 / 5) := by
  have a : (1.26 : ℝ) < Real.sqrt (1 + 3 / 5) := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have b : (0.63 : ℝ) < Real.sqrt (1 - 3 / 5) := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  rw [Real.sqrt_one]
  linarith

/-- **Definition 6.E.3** (MWG, p. 203). The extended independence axiom is the independence
axiom on the mixture space of state-contingent lotteries `L = (F₁, …, F_S)`, mixed state by
state. -/
abbrev ExtendedIndependence {S X : Type*} (r : HorseLottery S X → HorseLottery S X → Prop) :
    Prop :=
  Independence r

/-- **Proposition 6.E.1** (MWG, p. 203), the extended expected utility theorem: a rational,
continuous preference on state-contingent lotteries satisfying the extended independence
axiom is represented by `∑_s ∫ u_s dF_s` for state utility functions `u_s`. -/
theorem proposition_6_E_1 {S X : Type*} [Fintype S]
    {r : HorseLottery S X → HorseLottery S X → Prop} (hr : Rational r) (hc : MixContinuous r)
    (hi : ExtendedIndependence r) :
    ∃ u : S → X → ℝ, ∀ L L', r L L' ↔ HorseValue u L' ≤ HorseValue u L := by
  obtain ⟨U, hU⟩ := proposition_5_12.mp (mixtureAxioms_of_mwg hr hc hi)
  exact ⟨U, hU⟩

/-- The converse of Proposition 6.E.1: such a representation satisfies the three axioms. -/
theorem proposition_6_E_1_converse {S X : Type*} [Fintype S] (u : S → X → ℝ) :
    Rational (UtilityPref (HorseValue u)) ∧ MixContinuous (UtilityPref (HorseValue u)) ∧
      ExtendedIndependence (UtilityPref (HorseValue u)) := by
  have hrep : Represents (HorseValue u) (UtilityPref (HorseValue u)) := fun _ _ => Iff.rfl
  exact ⟨⟨fun x y => le_total _ _, fun x y z h1 h2 => h2.trans h1⟩,
    mixContinuous_of_affine hrep (horseValue_affine u),
    independence_of_affine hrep (horseValue_affine u)⟩

/-- **Definition 6.E.4** (MWG, p. 204). The sure-thing axiom: if `x, x'` and `x̄, x̄'` agree
outside an event `E`, and `x = x̄`, `x' = x̄'` on `E`, then `x ≿ x'` iff `x̄ ≿ x̄'`. -/
def SureThing {S : Type*} (r : (S → ℝ) → (S → ℝ) → Prop) : Prop :=
  ∀ (E : Set S) (x x' y y' : S → ℝ), (∀ s ∉ E, x s = x' s ∧ y s = y' s) →
    (∀ s ∈ E, x s = y s ∧ x' s = y' s) → (r x x' ↔ r y y')

/-- **p. 204**. An additively separable (extended expected utility) representation satisfies
the sure-thing axiom: terms with `x_s = x'_s` cancel. -/
theorem sureThing_of_additive {S : Type*} [Fintype S] (u : S → ℝ → ℝ) :
    SureThing (fun x x' : S → ℝ => ∑ s, u s (x' s) ≤ ∑ s, u s (x s)) := by
  classical
  intro E x x' y y' hout hin
  change (∑ s, u s (x' s) ≤ ∑ s, u s (x s)) ↔ (∑ s, u s (y' s) ≤ ∑ s, u s (y s))
  have key (a b : S → ℝ) : ∑ s, u s (b s) ≤ ∑ s, u s (a s) ↔
      0 ≤ ∑ s, (u s (a s) - u s (b s)) := by
    rw [Finset.sum_sub_distrib, sub_nonneg]
  rw [key, key]
  have e : ∑ s, (u s (x s) - u s (x' s)) = ∑ s, (u s (y s) - u s (y' s)) := by
    refine Finset.sum_congr rfl fun s _ => ?_
    by_cases hs : s ∈ E
    · rw [(hin s hs).1, (hin s hs).2]
    · rw [(hout s hs).1, (hout s hs).2]; ring
  rw [e]

/-- **p. 204**. With an extended expected utility representation on state-contingent money
lotteries, risk aversion (each state's sure mean at least as good as the state's lottery,
for every profile) is equivalent to the concavity of every `u_s`. -/
theorem riskAversion_iff_concave_states {S : Type*} [Fintype S] (u : S → ℝ → ℝ) :
    (∀ L : HorseLottery S ℝ, HorseValue u L ≤
      HorseValue u (fun s => PureLottery (ExpectedUtility id (L s)))) ↔
      ∀ s, ConcaveOn ℝ univ (u s) := by
  classical
  constructor
  · intro h s
    refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    let q : SimpleLottery ℝ := Kreps.UtilityForMoney.BinaryLottery x y a ⟨ha, by linarith⟩
    let L : HorseLottery S ℝ := fun t => if t = s then q else PureLottery 0
    have hL := h L
    simp only [HorseValue, StateAdditiveValue] at hL
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ s),
      ← Finset.add_sum_erase _ _ (Finset.mem_univ s)] at hL
    have hrest : ∑ t ∈ Finset.univ.erase s, ExpectedUtility (u t) (L t) =
        ∑ t ∈ Finset.univ.erase s, ExpectedUtility (u t)
          (PureLottery (ExpectedUtility id (L t))) := by
      refine Finset.sum_congr rfl fun t ht => ?_
      have hts : t ≠ s := Finset.ne_of_mem_erase ht
      simp only [L, hts, ↓reduceIte, expectedUtility_pure]
      rfl
    rw [hrest] at hL
    have hq := Kreps.UtilityForMoney.expectedUtility_binary (u s) x y a ⟨ha, by linarith⟩
    have hm := Kreps.UtilityForMoney.expectedUtility_binary id x y a ⟨ha, by linarith⟩
    simp only [L, ↓reduceIte, expectedUtility_pure] at hL
    have hL' : ExpectedUtility (u s) q ≤ u s (ExpectedUtility id q) := by linarith
    have hb' : b = 1 - a := by linarith
    subst hb'
    change Kreps.UtilityForMoney.ExpectedUtility (u s) q ≤
      u s (Kreps.UtilityForMoney.ExpectedUtility id q) at hL'
    rw [hq, hm] at hL'
    simpa only [smul_eq_mul, id] using hL'
  · intro h L
    simp only [HorseValue, StateAdditiveValue, expectedUtility_pure]
    exact Finset.sum_le_sum fun s _ =>
      Kreps.UtilityForMoney.expectedUtility_jensen (h s) id (fun _ => mem_univ _) (L s)

/-- The regret of `x` relative to `x'`, `∑_s π_s h(max{0, x'_s - x_s})` (MWG, Exercise 6.E.1,
p. 213). -/
noncomputable def regret {S : Type*} [Fintype S] (π : S → ℝ) (h : ℝ → ℝ) (x x' : S → ℝ) : ℝ :=
  ∑ s, π s * h (max 0 (x' s - x s))

/-- **Exercise 6.E.1** (MWG, pp. 213-214). With three equally likely states and
`h(x) = √x`, the regret ordering over `x = (0,-2,1)`, `x' = (0,2,-2)`, `x'' = (2,-3,-1)` is
not transitive: `x' ≻ x`, `x'' ≻ x'` and `x ≻ x''`. -/
theorem exercise_6_E_1 :
    let R := regret (fun _ : Fin 3 => (1 / 3 : ℝ)) Real.sqrt
    let x : Fin 3 → ℝ := ![0, -2, 1]
    let x' : Fin 3 → ℝ := ![0, 2, -2]
    let x'' : Fin 3 → ℝ := ![2, -3, -1]
    R x' x < R x x' ∧ R x'' x' < R x' x'' ∧ R x x'' < R x'' x := by
  intro R x x' x''
  have s4 : Real.sqrt 4 = 2 := sqrt_of_sq (by norm_num) (by norm_num)
  have s1 : Real.sqrt 1 = 1 := Real.sqrt_one
  have h3 : Real.sqrt 3 < 2 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have h5 : Real.sqrt 5 < Real.sqrt 2 + 1 := by
    have : (1.4 : ℝ) < Real.sqrt 2 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
    have : Real.sqrt 5 < 2.4 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
    linarith
  have h2 := Real.sqrt_nonneg 2
  simp only [R, x, x', x'', regret, Fin.sum_univ_three]
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [s4, s1] <;> linarith

/-- **Exercise 6.E.2(a)** (MWG, p. 214). With state-independent concave `u`, the preference
`π₁u(x₁) + π₂u(x₂)` on contingent commodities is convex (its utility is concave, hence
quasiconcave). -/
theorem exercise_6_E_2a {u : ℝ → ℝ} (hc : ConcaveOn ℝ (Ici 0) u) {π₁ π₂ : ℝ} (h1 : 0 ≤ π₁)
    (h2 : 0 ≤ π₂) :
    ConcaveOn ℝ {x : Fin 2 → ℝ | 0 ≤ x} (fun x => π₁ * u (x 0) + π₂ * u (x 1)) := by
  refine ⟨fun x hx y hy a b ha hb hab => show 0 ≤ a • x + b • y from
    add_nonneg (smul_nonneg ha (show 0 ≤ x from hx)) (smul_nonneg hb (show 0 ≤ y from hy)),
    fun x hx y hy a b ha hb hab => ?_⟩
  have c0 := hc.2 (mem_Ici.mpr (hx 0)) (mem_Ici.mpr (hy 0)) ha hb hab
  have c1 := hc.2 (mem_Ici.mpr (hx 1)) (mem_Ici.mpr (hy 1)) ha hb hab
  simp only [smul_eq_mul, Pi.add_apply, Pi.smul_apply] at c0 c1 ⊢
  nlinarith [mul_le_mul_of_nonneg_left c0 h1, mul_le_mul_of_nonneg_left c1 h2]

/-- **Exercise 6.E.2(b)** (MWG, p. 214). The decision maker is also risk averse over lotteries
whose outcomes are contingent-commodity vectors: Jensen's inequality for the concave
`π₁u(x₁) + π₂u(x₂)` (Exercise 6.C.5(a)). -/
theorem exercise_6_E_2b {u : ℝ → ℝ} (hc : ConcaveOn ℝ (Ici 0) u) {π₁ π₂ : ℝ} (h1 : 0 ≤ π₁)
    (h2 : 0 ≤ π₂) (n : ℕ) (w : Fin n → ℝ) (x : Fin n → Fin 2 → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hs : ∑ i, w i = 1) (hx : ∀ i, 0 ≤ x i) :
    ∑ i, w i * (π₁ * u (x i 0) + π₂ * u (x i 1)) ≤
      π₁ * u ((∑ i, w i • x i) 0) + π₂ * u ((∑ i, w i • x i) 1) :=
  (exercise_6_C_5a (convex_Ici (0 : Fin 2 → ℝ)) _).mp (exercise_6_E_2a hc h1 h2) n w x hw hs
    (fun i => hx i)

/-- **Exercise 6.E.2(c)** (MWG, p. 214). The Walrasian demands for the two contingent
commodities are normal: at interior optima with strictly decreasing marginal utility
(`π_l u'(x_l) = λ p_l`), higher wealth raises the demand for both (MWG's Exercise 3.G.4(c) for
the additively separable utility `π₁u(x₁) + π₂u(x₂)`). -/
theorem exercise_6_E_2c {du : ℝ → ℝ} (hdu : StrictAntiOn du (Ioi 0)) {π : Fin 2 → ℝ}
    (hπ : ∀ l, 0 < π l) {p x x' : Fin 2 → ℝ} (hp : ∀ l, 0 < p l) (hx : ∀ l, 0 < x l)
    (hx' : ∀ l, 0 < x' l) {lam lam' w w' : ℝ} (hfoc : ∀ l, π l * du (x l) = lam * p l)
    (hfoc' : ∀ l, π l * du (x' l) = lam' * p l) (hw : p ⬝ᵥ x = w) (hw' : p ⬝ᵥ x' = w')
    (hww : w < w') : ∀ l, x l < x' l := by
  apply MWG.ClassicalDemand.exercise_3_G_4c (du := fun l t => π l * du t) _ hp hx hx' hfoc
    hfoc' hw hw' hww
  intro l a ha b hb hab
  exact mul_lt_mul_of_pos_left (hdu ha hb hab) (hπ l)

/-- **Exercise 6.E.3** (MWG, p. 214). If `E(g) = 1` and `g* = αg + (1 - α)`, then the
distribution of `g*` second-order stochastically dominates that of `g`: for every concave `u`
on `ℝ₊`, `∑ π_s u(g*(s)) ≥ ∑ π_s u(g(s))`, and the means agree. -/
theorem exercise_6_E_3 {S : Type*} [Fintype S] {π : S → ℝ} (hπ : ∀ s, 0 ≤ π s)
    (hs : ∑ s, π s = 1) {g : S → ℝ} (hg : ∀ s, 0 ≤ g s) (hmean : ∑ s, π s * g s = 1)
    {α : ℝ} (ha0 : 0 < α) (ha1 : α < 1) :
    ∑ s, π s * (α * g s + (1 - α)) = ∑ s, π s * g s ∧
      ∀ u : ℝ → ℝ, ConcaveOn ℝ (Ici 0) u →
        ∑ s, π s * u (g s) ≤ ∑ s, π s * u (α * g s + (1 - α)) := by
  have hsum (A B : S → ℝ) (c d : ℝ) :
      ∑ s, π s * (c * A s + d * B s) = c * ∑ s, π s * A s + d * ∑ s, π s * B s := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring
  have hconst : ∑ s, π s * (1 : ℝ) = 1 := by simp [hs]
  constructor
  · have := hsum g (fun _ => 1) α (1 - α)
    simp only [mul_one] at this
    rw [show (∑ s, π s * (α * g s + (1 - α))) = ∑ s, π s * (α * g s + (1 - α) * 1) by
      simp only [mul_one], hsum g (fun _ => 1) α (1 - α), hmean, hconst]
    ring
  · intro u hc
    have hjensen : ∑ s, π s * u (g s) ≤ u 1 := by
      have := hc.le_map_sum (t := Finset.univ) (fun s _ => hπ s) hs (fun s _ => hg s)
      simpa [smul_eq_mul, hmean] using this
    have hpt (s : S) : α * u (g s) + (1 - α) * u 1 ≤ u (α * g s + (1 - α)) := by
      have := hc.2 (mem_Ici.mpr (hg s)) (show (1 : ℝ) ∈ Ici 0 by norm_num)
        (show (0 : ℝ) ≤ α from ha0.le) (show (0 : ℝ) ≤ 1 - α by linarith) (by ring)
      simpa [smul_eq_mul] using this
    have e : ∑ s, π s * (α * u (g s) + (1 - α) * u 1) =
        α * ∑ s, π s * u (g s) + (1 - α) * u 1 := by
      rw [hsum (fun s => u (g s)) (fun _ => u 1) α (1 - α)]
      rw [← Finset.sum_mul, hs, one_mul]
    calc ∑ s, π s * u (g s)
        ≤ α * ∑ s, π s * u (g s) + (1 - α) * u 1 := by nlinarith
      _ = ∑ s, π s * (α * u (g s) + (1 - α) * u 1) := e.symm
      _ ≤ ∑ s, π s * u (α * g s + (1 - α)) :=
          Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hpt s) (hπ s)

end MWG.ChoiceUnderUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The sure-thing axiom and additive representations

MWG, Section 6.E, p. 204: Proposition 6.E.2 (stated in the book without proof: "a complete
proof is too advanced"). A continuous rational preference on state-contingent money outcomes
`ℝ^S_+` satisfying the sure-thing axiom (Definition 6.E.4) has an additively separable
(extended expected utility) representation `∑_s u_s(x_s)`.

As printed the proposition is false: "at least three states" must be "at least three
*essential* states". If only two states matter, the sure-thing axiom reduces to the
independence of each state's ranking from the other, which does not give an additive
representation (the Thomsen condition fails). `proposition_6_E_2_false` gives a continuous
rational preference on `ℝ³_+` (and on `ℝ^S_+` for every `S ≥ 2`) satisfying the sure-thing
axiom, with utility `x₁ + x₂ + min(x₁, x₂)`, and with no representation `∑_s u_s(x_s)`.

The corrected statement (`proposition_6_E_2`) is Debreu's (1960) additive representation
theorem. It is derived from Kreps's Proposition 2.14 (`proposition_2_14_exists`, Kreps I,
p. 42, proved in the `PreferenceProperties` dependency by the local cardinal scales and
global continuation described in its construction guide), applied to the blocks
`B_s = ℝ₊`: MWG's continuity (Definition 3.C.1) is Kreps's open strict-preference graph
(`prefContinuous_iff_continuousPreference`), the sure-thing axiom is Kreps's strong
separability, and essential states are nontrivial blocks. The state utilities are moreover
continuous on `ℝ₊`.
-/

namespace MWG.ChoiceUnderUncertainty

open Set MWG.ConsumerChoice MWG.ClassicalDemand

/-- **Definition 6.E.4** (MWG, p. 204) on a domain `X` of outcome vectors (MWG: `X = ℝ^S_+`):
the sure-thing axiom for vectors of `X`. -/
def SureThingOn {S : Type*} (X : Set (S → ℝ)) (r : (S → ℝ) → (S → ℝ) → Prop) : Prop :=
  ∀ (E : Set S) (x x' y y' : S → ℝ), x ∈ X → x' ∈ X → y ∈ X → y' ∈ X →
    (∀ s ∉ E, x s = x' s ∧ y s = y' s) → (∀ s ∈ E, x s = y s ∧ x' s = y' s) →
      (r x x' ↔ r y y')

/-- The sure-thing axiom on all of `ℝ^S` gives it on every domain. -/
theorem SureThing.sureThingOn {S : Type*} {r : (S → ℝ) → (S → ℝ) → Prop} (h : SureThing r)
    (X : Set (S → ℝ)) : SureThingOn X r :=
  fun E x x' y y' _ _ _ _ hout hin => h E x x' y y' hout hin

/-- State `s` is essential (non-null) on `X`: two outcome vectors of `X` that differ only in
state `s` are strictly ranked. -/
def EssentialState {n : ℕ} (X : Set (Fin n → ℝ)) (r : (Fin n → ℝ) → (Fin n → ℝ) → Prop)
    (s : Fin n) : Prop :=
  ∃ x ∈ X, ∃ y ∈ X, (∀ t, t ≠ s → x t = y t) ∧ r x y ∧ ¬ r y x

/-- **Proposition 6.E.2** (MWG, p. 204), corrected (Debreu 1960). If `≿` on `ℝ^S_+` is
rational, continuous (Definition 3.C.1) and satisfies the sure-thing axiom, and at least three
states are essential, then `≿` has an additively separable representation
`x ≿ x' ⟺ ∑_s u_s(x'_s) ≤ ∑_s u_s(x_s)`, with every `u_s` continuous on `ℝ₊`. The book asks
for at least three states; `proposition_6_E_2_false` shows that three essential states are
needed. -/
theorem proposition_6_E_2 {n : ℕ} {r : (Fin n → ℝ) → (Fin n → ℝ) → Prop}
    (hr : RationalOn (nonnegOrthant n) r) (hc : PrefContinuous (nonnegOrthant n) r)
    (hs : SureThingOn (nonnegOrthant n) r)
    (h3 : ∃ s₁ s₂ s₃, s₁ ≠ s₂ ∧ s₁ ≠ s₃ ∧ s₂ ≠ s₃ ∧ EssentialState (nonnegOrthant n) r s₁ ∧
      EssentialState (nonnegOrthant n) r s₂ ∧ EssentialState (nonnegOrthant n) r s₃) :
    ∃ u : Fin n → ℝ → ℝ, (∀ s, ContinuousOn (u s) (Ici 0)) ∧
      ∀ x ∈ nonnegOrthant n, ∀ y ∈ nonnegOrthant n,
        (r x y ↔ ∑ s, u s (y s) ≤ ∑ s, u s (x s)) := by
  classical
  let emb : (∀ _ : Fin n, Ici (0 : ℝ)) → Fin n → ℝ := fun a i => (a i : ℝ)
  have hemb (a : ∀ _ : Fin n, Ici (0 : ℝ)) : emb a ∈ nonnegOrthant n := fun i => (a i).2
  let r' : (∀ _ : Fin n, Ici (0 : ℝ)) → (∀ _ : Fin n, Ici (0 : ℝ)) → Prop :=
    fun a b => r (emb a) (emb b)
  have hrat : Kreps.PreferenceProperties.Rational r' :=
    ⟨fun a b => hr.1 _ (hemb a) _ (hemb b),
      fun a b c h1 h2 => hr.2 _ (hemb a) _ (hemb b) _ (hemb c) h1 h2⟩
  have hcont : Kreps.PreferenceProperties.ContinuousPreference r' := by
    have ho := (prefContinuous_iff_continuousPreference hr).mp hc
    let e : (∀ _ : Fin n, Ici (0 : ℝ)) → nonnegOrthant n := fun a => ⟨emb a, hemb a⟩
    have he : Continuous e :=
      Continuous.subtype_mk (continuous_pi fun i => continuous_subtype_val.comp
        (continuous_apply i)) _
    exact ho.preimage ((he.comp continuous_fst).prodMk (he.comp continuous_snd))
  have hsep : Kreps.PreferenceProperties.StronglySeparable r' := by
    intro S a b z t
    refine hs (↑S) _ _ _ _ (hemb _) (hemb _) (hemb _) (hemb _) (fun s hsS => ?_)
      (fun s hsS => ?_)
    · have hsS' : s ∉ S := hsS
      simp only [emb, Finset.piecewise_eq_of_notMem _ _ _ hsS', and_self]
    · have hsS' : s ∈ S := hsS
      simp only [emb, Finset.piecewise_eq_of_mem _ _ _ hsS', and_self]
  have hnt (s : Fin n) (h : EssentialState (nonnegOrthant n) r s) :
      Kreps.PreferenceProperties.NontrivialBlock r' s := by
    obtain ⟨x, hx, y, hy, hxy, h1, h2⟩ := h
    let z : ∀ _ : Fin n, Ici (0 : ℝ) := fun i => ⟨x i, hx i⟩
    refine ⟨⟨x s, hx s⟩, ⟨y s, hy s⟩, z, ?_⟩
    have ex : emb (Function.update z s ⟨x s, hx s⟩) = x := by
      funext t
      by_cases hts : t = s
      · subst hts; simp [emb]
      · simp [emb, z]
    have ey : emb (Function.update z s ⟨y s, hy s⟩) = y := by
      funext t
      by_cases hts : t = s
      · subst hts; simp [emb]
      · simp [emb, Function.update_of_ne hts, z, hxy t hts]
    exact ⟨by change r _ _; rw [ex, ey]; exact h1, by change ¬ r _ _; rw [ex, ey]; exact h2⟩
  have hthree : Kreps.PreferenceProperties.ThreeNontrivialBlocks r' := by
    obtain ⟨s₁, s₂, s₃, h12, h13, h23, e1, e2, e3⟩ := h3
    exact ⟨s₁, s₂, s₃, h12, h13, h23, hnt s₁ e1, hnt s₂ e2, hnt s₃ e3⟩
  have hpc : PreconnectedSpace (Ici (0 : ℝ)) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Ici
  obtain ⟨w, hwc, hwr⟩ := Kreps.PreferenceProperties.proposition_2_14_exists
    (B := fun _ : Fin n => Ici (0 : ℝ)) hrat hcont hsep hthree
  refine ⟨fun s t => if h : 0 ≤ t then w s ⟨t, h⟩ else 0, fun s => ?_, fun x hx y hy => ?_⟩
  · have hproj : Continuous (Set.projIci (0 : ℝ)) :=
      (continuous_const.max continuous_id).subtype_mk _
    refine ((hwc s).comp hproj).continuousOn.congr fun t ht => ?_
    have ht' : (0 : ℝ) ≤ t := ht
    simp [ht', Set.projIci_of_mem ht]
  · have := hwr (fun i => ⟨x i, hx i⟩) (fun i => ⟨y i, hy i⟩)
    have hx' : ∀ s, 0 ≤ x s := hx
    have hy' : ∀ s, 0 ≤ y s := hy
    simp only [Kreps.PreferenceProperties.AdditiveUtility] at this
    simp only [hx', hy', ↓reduceDIte]
    exact this

/-- The utility `V(x) = x₀ + x₁ + min(x₀, x₁)` of the counterexample to Proposition 6.E.2 as
printed: only the first two states matter. -/
noncomputable def thomsenV {k : ℕ} (x : Fin (k + 2) → ℝ) : ℝ := x 0 + x 1 + min (x 0) (x 1)

/-- The preference represented by `thomsenV`. -/
def thomsenPref {k : ℕ} (x y : Fin (k + 2) → ℝ) : Prop := thomsenV y ≤ thomsenV x

theorem thomsen_mono_left (a b c : ℝ) : a + c + min a c ≤ b + c + min b c ↔ a ≤ b := by
  constructor
  · intro h
    by_contra hn
    push Not at hn
    have : min b c ≤ min a c := min_le_min_right c hn.le
    linarith
  · intro h
    have : min a c ≤ min b c := min_le_min_right c h
    linarith

theorem thomsen_mono_right (a b c : ℝ) : c + a + min c a ≤ c + b + min c b ↔ a ≤ b := by
  rw [min_comm c a, min_comm c b, add_comm c a, add_comm c b]
  exact thomsen_mono_left a b c

/-- The counterexample preference is rational on `ℝ^S_+`. -/
theorem thomsenPref_rational (k : ℕ) : RationalOn (nonnegOrthant (k + 2)) thomsenPref :=
  ⟨fun _ _ _ _ => le_total _ _, fun _ _ _ _ _ _ h1 h2 => h2.trans h1⟩

/-- The counterexample preference is continuous (Definition 3.C.1). -/
theorem thomsenPref_continuous (k : ℕ) : PrefContinuous (nonnegOrthant (k + 2)) thomsenPref := by
  intro xs ys x y _ _ _ _ h hx hy
  have hV : Continuous (thomsenV (k := k)) := by unfold thomsenV; fun_prop
  exact le_of_tendsto_of_tendsto' ((hV.tendsto y).comp hy) ((hV.tendsto x).comp hx) h

/-- The counterexample preference satisfies the sure-thing axiom (on all of `ℝ^S`). -/
theorem thomsenPref_sureThing (k : ℕ) : SureThing (thomsenPref (k := k)) := by
  intro E x x' y y' hout hin
  unfold thomsenPref thomsenV
  by_cases h0 : (0 : Fin (k + 2)) ∈ E <;> by_cases h1 : (1 : Fin (k + 2)) ∈ E
  · rw [(hin 0 h0).1, (hin 0 h0).2, (hin 1 h1).1, (hin 1 h1).2]
  · rw [(hin 0 h0).1, (hin 0 h0).2, (hout 1 h1).1, (hout 1 h1).2, thomsen_mono_left,
      thomsen_mono_left]
  · rw [(hin 1 h1).1, (hin 1 h1).2, (hout 0 h0).1, (hout 0 h0).2, thomsen_mono_right,
      thomsen_mono_right]
  · rw [(hout 0 h0).1, (hout 0 h0).2, (hout 1 h1).1, (hout 1 h1).2]
    simp

/-- The outcome vector paying `a` in state `0`, `b` in state `1` and `0` elsewhere. -/
noncomputable def twoStateVec {k : ℕ} (a b : ℝ) : Fin (k + 2) → ℝ :=
  fun s => if s = 0 then a else if s = 1 then b else 0

theorem twoStateVec_zero {k : ℕ} (a b : ℝ) : twoStateVec (k := k) a b 0 = a := by
  simp [twoStateVec]

theorem twoStateVec_one {k : ℕ} (a b : ℝ) : twoStateVec (k := k) a b 1 = b := by
  have : (1 : Fin (k + 2)) ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp at this
  simp [twoStateVec, this]

theorem twoStateVec_mem {k : ℕ} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    twoStateVec (k := k) a b ∈ nonnegOrthant (k + 2) := by
  intro s
  unfold twoStateVec
  split_ifs
  · exact ha
  · exact hb
  · exact le_rfl

theorem thomsenV_twoStateVec {k : ℕ} (a b : ℝ) :
    thomsenV (twoStateVec (k := k) a b) = a + b + min a b := by
  unfold thomsenV; rw [twoStateVec_zero, twoStateVec_one]

/-- The counterexample preference has no additively separable representation on `ℝ^S_+`: the
Thomsen condition fails, `(0,4) ∼ (2,1)` and `(2,2) ∼ (1,4)` but `(0,2) ≺ (1,1)`, whereas any
`f(x₀) + g(x₁)` would give `(0,2) ∼ (1,1)`. -/
theorem thomsenPref_not_additive (k : ℕ) : ¬ ∃ u : Fin (k + 2) → ℝ → ℝ,
    ∀ x ∈ nonnegOrthant (k + 2), ∀ y ∈ nonnegOrthant (k + 2),
      (thomsenPref x y ↔ ∑ s, u s (y s) ≤ ∑ s, u s (x s)) := by
  rintro ⟨u, hu⟩
  set T : ℝ → ℝ → ℝ := fun a b => ∑ s, u s (twoStateVec (k := k) a b s) with hT
  have hrect (a b c d : ℝ) : T a b + T c d = T a d + T c b := by
    simp only [hT, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    unfold twoStateVec
    split_ifs <;> ring
  have hrep {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
      (c + d + min c d ≤ a + b + min a b ↔ T c d ≤ T a b) := by
    have := hu _ (twoStateVec_mem (k := k) ha hb) _ (twoStateVec_mem (k := k) hc hd)
    simp only [thomsenPref, thomsenV_twoStateVec] at this
    exact this
  have e1 : T 0 4 = T 2 1 := le_antisymm
    ((hrep (by norm_num) (by norm_num) (by norm_num) (by norm_num)).mp (by norm_num))
    ((hrep (by norm_num) (by norm_num) (by norm_num) (by norm_num)).mp (by norm_num))
  have e2 : T 2 2 = T 1 4 := le_antisymm
    ((hrep (by norm_num) (by norm_num) (by norm_num) (by norm_num)).mp (by norm_num))
    ((hrep (by norm_num) (by norm_num) (by norm_num) (by norm_num)).mp (by norm_num))
  have r1 := hrect 0 4 2 2
  have r2 := hrect 2 1 1 4
  have hlt : ¬ (1 + 1 + min (1 : ℝ) 1 ≤ 0 + 2 + min 0 2) := by norm_num
  rw [hrep (by norm_num) (by norm_num) (by norm_num) (by norm_num)] at hlt
  linarith

/-- **Proposition 6.E.2** (MWG, p. 204) as printed is false, for every number `S ≥ 2` of states
(in particular `S = 3`): the counterexample preference is rational, continuous and satisfies
the sure-thing axiom on `ℝ^S_+`, but has no additively separable representation. Only two of
its states are essential (`thomsenPref_essential`). -/
theorem proposition_6_E_2_false (k : ℕ) : ¬ ∀ r : (Fin (k + 2) → ℝ) → (Fin (k + 2) → ℝ) → Prop,
    RationalOn (nonnegOrthant (k + 2)) r → PrefContinuous (nonnegOrthant (k + 2)) r →
      SureThingOn (nonnegOrthant (k + 2)) r → ∃ u : Fin (k + 2) → ℝ → ℝ,
        ∀ x ∈ nonnegOrthant (k + 2), ∀ y ∈ nonnegOrthant (k + 2),
          (r x y ↔ ∑ s, u s (y s) ≤ ∑ s, u s (x s)) :=
  fun h => thomsenPref_not_additive k (h _ (thomsenPref_rational k) (thomsenPref_continuous k)
    ((thomsenPref_sureThing k).sureThingOn _))

/-- In the counterexample, states `0` and `1` are essential and every other state is not, so
it has exactly two essential states. -/
theorem thomsenPref_essential (k : ℕ) :
    EssentialState (nonnegOrthant (k + 2)) thomsenPref 0 ∧
      EssentialState (nonnegOrthant (k + 2)) thomsenPref 1 ∧
      ∀ s, s ≠ 0 → s ≠ 1 → ¬ EssentialState (nonnegOrthant (k + 2)) thomsenPref s := by
  refine ⟨⟨twoStateVec 1 0, twoStateVec_mem (by norm_num) le_rfl, twoStateVec 0 0,
    twoStateVec_mem le_rfl le_rfl, fun t ht => ?_, ?_, ?_⟩,
    ⟨twoStateVec 0 1, twoStateVec_mem le_rfl (by norm_num), twoStateVec 0 0,
    twoStateVec_mem le_rfl le_rfl, fun t ht => ?_, ?_, ?_⟩, ?_⟩
  · simp [twoStateVec, ht]
  · simp only [thomsenPref, thomsenV_twoStateVec]; norm_num
  · simp only [thomsenPref, thomsenV_twoStateVec]; norm_num
  · unfold twoStateVec; split_ifs <;> simp_all
  · simp only [thomsenPref, thomsenV_twoStateVec]; norm_num
  · simp only [thomsenPref, thomsenV_twoStateVec]; norm_num
  · rintro s h0 h1 ⟨x, -, y, -, hxy, -, h2⟩
    apply h2
    unfold thomsenPref thomsenV
    rw [hxy 0 (Ne.symm h0), hxy 1 (Ne.symm h1)]

/-- A concrete instance of the hypotheses of the corrected Proposition 6.E.2: the risk-neutral
preference `∑_s x_s` on `ℝ³_+` is rational, continuous, satisfies the sure-thing axiom, and all
three states are essential. -/
theorem proposition_6_E_2_instance :
    let r : (Fin 3 → ℝ) → (Fin 3 → ℝ) → Prop := fun x y => ∑ s, y s ≤ ∑ s, x s
    RationalOn (nonnegOrthant 3) r ∧ PrefContinuous (nonnegOrthant 3) r ∧
      SureThingOn (nonnegOrthant 3) r ∧ ∀ s, EssentialState (nonnegOrthant 3) r s := by
  intro r
  refine ⟨⟨fun x _ y _ => le_total _ _, fun _ _ _ _ _ _ h1 h2 => h2.trans h1⟩, ?_, ?_, ?_⟩
  · intro xs ys x y _ _ _ _ h hx hy
    have hV : Continuous fun z : Fin 3 → ℝ => ∑ s, z s := by fun_prop
    exact le_of_tendsto_of_tendsto' ((hV.tendsto y).comp hy) ((hV.tendsto x).comp hx) h
  · exact (sureThing_of_additive (fun _ t => t)).sureThingOn _
  · intro s
    refine ⟨Pi.single s 1, fun t => ?_, 0, fun _ => le_rfl, fun t ht => ?_, ?_, ?_⟩
    · by_cases h : t = s
      · subst h; simp
      · simp [h]
    · simp [ht]
    · simp only [r]; simp
    · simp only [r]; simp

end MWG.ChoiceUnderUncertainty

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Subjective probability theory

MWG, Section 6.F, pp. 204-206, and Exercises 6.F.1-6.F.2, pp. 214-215: state preferences,
Definition 6.F.1 (state uniformity), the affine relation `u_s = π_s u + β_s`, Proposition 6.F.1
(the subjective expected utility theorem, in the Anscombe-Aumann setting with state-contingent
lotteries), its uniqueness part (Exercise 6.F.1), the Ellsberg variation (Example 6.F.1) and the
Gilboa-Schmeidler multiple-priors explanation (Exercise 6.F.2).

Correction: the probabilities are unique only when the utility on money is nonconstant (not all
lotteries indifferent); otherwise every probability vector represents the preference
(`exercise_6_F_1_probabilities_not_unique`).
-/

namespace MWG.ChoiceUnderUncertainty

open Kreps.ChoiceUnderUncertainty

variable {S X : Type*} [Fintype S]

/-- **p. 206**. The state-`s` preference on money lotteries derived from the state utility
`u_s`: `F ≿_s F'` iff `∫ u_s dF ≥ ∫ u_s dF'`. -/
def statePref (U : S → X → ℝ) (s : S) (F F' : SimpleLottery X) : Prop :=
  ExpectedUtility (U s) F' ≤ ExpectedUtility (U s) F

/-- **Definition 6.F.1** (MWG, p. 206). The state preferences are state uniform if
`≿_s = ≿_{s'}` for all `s, s'`. -/
def StateUniform (U : S → X → ℝ) : Prop := ∀ s s', statePref U s = statePref U s'

omit [Fintype S] in
/-- **p. 206**. With state uniformity, `u_s = α_s u + β_s` with `α_s > 0` for a common `u`
(here `u = u_{s₀}`). -/
theorem stateUniform_affine {U : S → X → ℝ} (h : StateUniform U) (s₀ s : S) :
    ∃ A > 0, ∃ B : ℝ, ∀ x, U s x = A * U s₀ x + B := by
  have h0 : Represents (ExpectedUtility (U s₀)) (statePref U s₀) := fun _ _ => Iff.rfl
  have h1 : Represents (ExpectedUtility (U s)) (statePref U s₀) := by
    rw [h s₀ s]; exact fun _ _ => Iff.rfl
  exact proposition_5_3_unique h0 h1

/-- **Proposition 6.F.1** (MWG, p. 206), the subjective expected utility theorem: if the
preference on state-contingent lotteries is rational, continuous, satisfies the extended
independence axiom, and the derived state preferences are state uniform, there are
probabilities `π_s > 0` summing to one and a utility `u` with
`L ≿ L'` iff `∑ π_s ∫ u dF_s ≥ ∑ π_s ∫ u dF'_s`. -/
theorem proposition_6_F_1 [Nonempty S] {r : HorseLottery S X → HorseLottery S X → Prop}
    (hr : Rational r) (hc : MixContinuous r) (hi : ExtendedIndependence r)
    (huni : ∀ U : S → X → ℝ, Represents (HorseValue U) r → StateUniform U) :
    ∃ (π : S → ℝ) (u : X → ℝ), (∀ s, 0 < π s) ∧ ∑ s, π s = 1 ∧
      Represents (SubjectiveHorseValue π u) r := by
  classical
  obtain ⟨U, hU⟩ := proposition_6_E_1 hr hc hi
  obtain ⟨s₀⟩ := ‹Nonempty S›
  have hu := huni U hU
  choose A hA B hB using stateUniform_affine hu s₀
  set T := ∑ s, A s
  have hT : 0 < T := Finset.sum_pos (fun s _ => hA s) Finset.univ_nonempty
  refine ⟨fun s => A s / T, U s₀, fun s => div_pos (hA s) hT, ?_, fun L L' => ?_⟩
  · rw [← Finset.sum_div, div_self hT.ne']
  · have hval (M : HorseLottery S X) : HorseValue U M =
        T * SubjectiveHorseValue (fun s => A s / T) (U s₀) M + ∑ s, B s := by
      simp only [HorseValue, StateAdditiveValue, SubjectiveHorseValue, SubjectiveActValue]
      have he (s : S) : ExpectedUtility (U s) (M s) =
          A s * ExpectedUtility (U s₀) (M s) + B s := by
        rw [show U s = fun x => A s * U s₀ x + B s from funext (hB s),
          expectedUtility_affine_transform]
      simp only [he, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun s _ => by field_simp
    rw [hU, hval, hval]
    constructor
    · intro h; nlinarith
    · intro h; nlinarith

/-- **Proposition 6.F.1** (MWG, p. 206) for sure money payoffs `(x₁, …, x_S)`:
`x ≿ x'` iff `∑ π_s u(x_s) ≥ ∑ π_s u(x'_s)`. -/
theorem proposition_6_F_1_sure [Nonempty S] {r : HorseLottery S X → HorseLottery S X → Prop}
    (hr : Rational r) (hc : MixContinuous r) (hi : ExtendedIndependence r)
    (huni : ∀ U : S → X → ℝ, Represents (HorseValue U) r → StateUniform U) :
    ∃ (π : S → ℝ) (u : X → ℝ), (∀ s, 0 < π s) ∧ ∑ s, π s = 1 ∧ ∀ x x' : S → X,
      r (fun s => PureLottery (x s)) (fun s => PureLottery (x' s)) ↔
        ∑ s, π s * u (x' s) ≤ ∑ s, π s * u (x s) := by
  obtain ⟨π, u, hπ, h1, hrep⟩ := proposition_6_F_1 hr hc hi huni
  refine ⟨π, u, hπ, h1, fun x x' => ?_⟩
  rw [hrep]
  simp only [SubjectiveHorseValue, SubjectiveActValue, expectedUtility_pure]

/-- **Exercise 6.F.1** (MWG, p. 214), utility. In the subjective expected utility theorem the
utility on money is unique up to origin and scale. -/
theorem exercise_6_F_1_utility {π π' : S → ℝ} (hπ : ∑ s, π s = 1) (hπ' : ∑ s, π' s = 1)
    {u u' : X → ℝ} {r : HorseLottery S X → HorseLottery S X → Prop}
    (h : Represents (SubjectiveHorseValue π u) r) (h' : Represents (SubjectiveHorseValue π' u') r) :
    ∃ β > 0, ∃ γ : ℝ, ∀ x, u' x = β * u x + γ :=
  subjective_prize_utility_unique π π' hπ hπ' u u' h h'

/-- **Exercise 6.F.1** (MWG, p. 214), probabilities. When the utility on money is nonconstant,
the subjective probabilities are uniquely determined. -/
theorem exercise_6_F_1_probabilities {π π' : S → ℝ} (hπ : ∑ s, π s = 1)
    (hπ' : ∑ s, π' s = 1) {u u' : X → ℝ} {r : HorseLottery S X → HorseLottery S X → Prop}
    (h : Represents (SubjectiveHorseValue π u) r) (h' : Represents (SubjectiveHorseValue π' u') r)
    {x y : X} (hne : u x ≠ u y) : π' = π :=
  subjective_probabilities_unique π π' hπ hπ' u u' h h' hne

/-- **Exercise 6.F.1**: correction. Without a nonconstant utility the probabilities are not
unique: for the total-indifference preference, `u = 0` with `π = (1/2, 1/2)` and with
`π = (1/3, 2/3)` both represent it. -/
theorem exercise_6_F_1_probabilities_not_unique :
    let r : HorseLottery (Fin 2) Bool → HorseLottery (Fin 2) Bool → Prop := fun _ _ => True
    Represents (SubjectiveHorseValue ![1 / 2, 1 / 2] (fun _ => 0)) r ∧
      Represents (SubjectiveHorseValue ![1 / 3, 2 / 3] (fun _ => 0)) r ∧
      (![1 / 2, 1 / 2] : Fin 2 → ℝ) ≠ ![1 / 3, 2 / 3] := by
  intro r
  have h0 (p : Fin 2 → ℝ) (M : HorseLottery (Fin 2) Bool) :
      SubjectiveHorseValue p (fun _ => (0 : ℝ)) M = 0 := by
    simp [SubjectiveHorseValue, SubjectiveActValue, ExpectedUtility]
  refine ⟨fun L L' => ?_, fun L L' => ?_, fun h => ?_⟩
  · simp [r, h0]
  · simp [r, h0]
  · have := congrFun h 0
    norm_num at this

/-- **Example 6.F.1** (MWG, p. 206), a variation of the Ellsberg paradox. Urn `R` has `49` white
and `51` black balls; urn `H` an unknown mixture. With any subjective probability `q` that the
`H`-ball is white, strictly preferring the `R`-ball when black wins (`0.51 > 1 - q`) forces
strictly preferring the `H`-ball when white wins (`q > 0.49`): choosing `R` in both situations
is inconsistent with subjective expected utility. -/
theorem example_6_F_1 (q : ℝ) :
    (51 / 100 : ℝ) > 1 - q → q > 49 / 100 := by intro h; linarith

/-- **Exercise 6.F.2** (MWG, pp. 214-215). Gilboa-Schmeidler utilities with a set of beliefs `P`
on the `H`-ball being white, `u(0) = 0`, `u(1000) = 1`. -/
noncomputable def gsUtilityW (P : Set ℝ) : ℝ := sInf P

/-- The worst-case probability of black. -/
noncomputable def gsUtilityB (P : Set ℝ) : ℝ := sInf ((fun q => 1 - q) '' P)

/-- **Exercise 6.F.2(a)** (MWG, p. 215). With a single belief `P = {q}`, the utilities are
expected utilities (`U_W(H) = q`, `U_B(H) = 1 - q`), and `U_W(R) > U_W(H)` iff
`U_B(R) < U_B(H)`. -/
theorem exercise_6_F_2a (q : ℝ) :
    gsUtilityW {q} = q ∧ gsUtilityB {q} = 1 - q ∧
      ((49 / 100 : ℝ) > gsUtilityW {q} ↔ (51 / 100 : ℝ) < gsUtilityB {q}) := by
  have h1 : gsUtilityW {q} = q := csInf_singleton q
  have h2 : gsUtilityB {q} = 1 - q := by
    simp [gsUtilityB, Set.image_singleton, csInf_singleton]
  refine ⟨h1, h2, ?_⟩
  rw [h1, h2]
  constructor <;> intro h <;> linarith

/-- **Exercise 6.F.2(b)** (MWG, p. 215). With `P = [0.4, 0.6]` the decision maker strictly
prefers the `R`-ball in both choice situations: `U_W(R) = 0.49 > 0.4 = U_W(H)` and
`U_B(R) = 0.51 > 0.4 = U_B(H)`. -/
theorem exercise_6_F_2b :
    gsUtilityW (Set.Icc (2 / 5) (3 / 5)) = 2 / 5 ∧ gsUtilityB (Set.Icc (2 / 5) (3 / 5)) = 2 / 5 ∧
      (49 / 100 : ℝ) > gsUtilityW (Set.Icc (2 / 5) (3 / 5)) ∧
      (51 / 100 : ℝ) > gsUtilityB (Set.Icc (2 / 5) (3 / 5)) := by
  have h1 : gsUtilityW (Set.Icc (2 / 5) (3 / 5)) = 2 / 5 := csInf_Icc (by norm_num)
  have himg : (fun q : ℝ => 1 - q) '' Set.Icc (2 / 5) (3 / 5) = Set.Icc (2 / 5) (3 / 5) := by
    ext y
    constructor
    · rintro ⟨q, hq, rfl⟩; exact ⟨by linarith [hq.2], by linarith [hq.1]⟩
    · intro hy; exact ⟨1 - y, ⟨by linarith [hy.2], by linarith [hy.1]⟩, by ring⟩
  have h2 : gsUtilityB (Set.Icc (2 / 5) (3 / 5)) = 2 / 5 := by
    rw [gsUtilityB, himg]; exact csInf_Icc (by norm_num)
  refine ⟨h1, h2, ?_, ?_⟩
  · rw [h1]; norm_num
  · rw [h2]; norm_num

end MWG.ChoiceUnderUncertainty

set_option linter.style.longLine false
#print axioms MWG.ChoiceUnderUncertainty.rational_iff_mwg
#print axioms MWG.ChoiceUnderUncertainty.lotteryOfVec
#print axioms MWG.ChoiceUnderUncertainty.lotteryOfVec_weights
#print axioms MWG.ChoiceUnderUncertainty.definition_6_B_1
#print axioms MWG.ChoiceUnderUncertainty.lottery_vectors_eq_simplex
#print axioms MWG.ChoiceUnderUncertainty.degenerate_lottery_weights
#print axioms MWG.ChoiceUnderUncertainty.reducedVec
#print axioms MWG.ChoiceUnderUncertainty.footnote_6_4
#print axioms MWG.ChoiceUnderUncertainty.reducedLottery
#print axioms MWG.ChoiceUnderUncertainty.reducedLottery_weights
#print axioms MWG.ChoiceUnderUncertainty.reducedLottery_two
#print axioms MWG.ChoiceUnderUncertainty.figure_6_B_2
#print axioms MWG.ChoiceUnderUncertainty.figure_6_B_3
#print axioms MWG.ChoiceUnderUncertainty.footnote_6_2
#print axioms MWG.ChoiceUnderUncertainty.MixContinuous
#print axioms MWG.ChoiceUnderUncertainty.Independence
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_B_1_strict
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_B_1_indifferent
#print axioms MWG.ChoiceUnderUncertainty.independence_left
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_B_1_both
#print axioms MWG.ChoiceUnderUncertainty.mixtureAxioms_of_mwg
#print axioms MWG.ChoiceUnderUncertainty.mixContinuous_of_affine
#print axioms MWG.ChoiceUnderUncertainty.independence_of_affine
#print axioms MWG.ChoiceUnderUncertainty.proposition_6_B_3_step1
#print axioms MWG.ChoiceUnderUncertainty.proposition_6_B_3_step2
#print axioms MWG.ChoiceUnderUncertainty.IsLinearUtility
#print axioms MWG.ChoiceUnderUncertainty.HasExpectedUtilityForm
#print axioms MWG.ChoiceUnderUncertainty.expectedUtilityForm_degenerate
#print axioms MWG.ChoiceUnderUncertainty.reducedLottery_degenerate
#print axioms MWG.ChoiceUnderUncertainty.proposition_6_B_1
#print axioms MWG.ChoiceUnderUncertainty.hasExpectedUtilityForm_iff
#print axioms MWG.ChoiceUnderUncertainty.affineInMix_of_expectedUtilityForm
#print axioms MWG.ChoiceUnderUncertainty.proposition_6_B_2
#print axioms MWG.ChoiceUnderUncertainty.footnote_6_6
#print axioms MWG.ChoiceUnderUncertainty.continuous_of_expectedUtilityForm
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_B_2
#print axioms MWG.ChoiceUnderUncertainty.proposition_6_B_3
#print axioms MWG.ChoiceUnderUncertainty.proposition_6_B_3_converse
#print axioms MWG.ChoiceUnderUncertainty.proposition_6_B_3_step3
#print axioms MWG.ChoiceUnderUncertainty.noBetter_isConvexSet
#print axioms MWG.ChoiceUnderUncertainty.noWorse_isConvexSet
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_B_3
#print axioms MWG.ChoiceUnderUncertainty.eu
#print axioms MWG.ChoiceUnderUncertainty.eu_mix
#print axioms MWG.ChoiceUnderUncertainty.lot3
#print axioms MWG.ChoiceUnderUncertainty.eu_lot3
#print axioms MWG.ChoiceUnderUncertainty.utility_differences_meaning
#print axioms MWG.ChoiceUnderUncertainty.utility_differences_invariant
#print axioms MWG.ChoiceUnderUncertainty.indifference_set_hyperplane
#print axioms MWG.ChoiceUnderUncertainty.indifference_straight
#print axioms MWG.ChoiceUnderUncertainty.indifference_parallel
#print axioms MWG.ChoiceUnderUncertainty.example_6_B_1
#print axioms MWG.ChoiceUnderUncertainty.example_6_B_1_general_map_fails
#print axioms MWG.ChoiceUnderUncertainty.allaisL1
#print axioms MWG.ChoiceUnderUncertainty.allaisL1'
#print axioms MWG.ChoiceUnderUncertainty.allaisL2
#print axioms MWG.ChoiceUnderUncertainty.allaisL2'
#print axioms MWG.ChoiceUnderUncertainty.figure_6_B_7
#print axioms MWG.ChoiceUnderUncertainty.example_6_B_2
#print axioms MWG.ChoiceUnderUncertainty.example_6_B_2_axioms
#print axioms MWG.ChoiceUnderUncertainty.example_6_B_3
#print axioms MWG.ChoiceUnderUncertainty.dutchBook_convexity
#print axioms MWG.ChoiceUnderUncertainty.weightedV
#print axioms MWG.ChoiceUnderUncertainty.weightedV_den_pos
#print axioms MWG.ChoiceUnderUncertainty.weightedPref
#print axioms MWG.ChoiceUnderUncertainty.weightedV_mix_continuous
#print axioms MWG.ChoiceUnderUncertainty.weightedPref_rational_continuous
#print axioms MWG.ChoiceUnderUncertainty.Betweenness
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_B_5a
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_B_5b
#print axioms MWG.ChoiceUnderUncertainty.weightedPref_betweenness
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_B_5d
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_B_5c
#print axioms MWG.ChoiceUnderUncertainty.dutchBook_convexity_weaker
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_B_4a
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_B_4b
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_B_6_convex
#print axioms MWG.ChoiceUnderUncertainty.sup'_fin_two
#print axioms MWG.ChoiceUnderUncertainty.example_6_B_4
#print axioms MWG.ChoiceUnderUncertainty.example_6_B_4_outcomes
#print axioms MWG.ChoiceUnderUncertainty.footnote_6_9
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_B_7
#print axioms MWG.ChoiceUnderUncertainty.IsMoneyLottery
#print axioms MWG.ChoiceUnderUncertainty.IsMoneyLottery.ae_mem
#print axioms MWG.ChoiceUnderUncertainty.IsMoneyLottery.integrable
#print axioms MWG.ChoiceUnderUncertainty.IsMoneyLottery.integrable_id
#print axioms MWG.ChoiceUnderUncertainty.IsMoneyLottery.mean_mem
#print axioms MWG.ChoiceUnderUncertainty.IsMoneyLottery.mean_mem_S
#print axioms MWG.ChoiceUnderUncertainty.binLot
#print axioms MWG.ChoiceUnderUncertainty.integral_binLot
#print axioms MWG.ChoiceUnderUncertainty.binLot_isProbabilityMeasure
#print axioms MWG.ChoiceUnderUncertainty.binLot_isMoneyLottery
#print axioms MWG.ChoiceUnderUncertainty.dirac_isMoneyLottery
#print axioms MWG.ChoiceUnderUncertainty.mixM
#print axioms MWG.ChoiceUnderUncertainty.mixM_isProbabilityMeasure
#print axioms MWG.ChoiceUnderUncertainty.mixM_real
#print axioms MWG.ChoiceUnderUncertainty.cdf_mixM
#print axioms MWG.ChoiceUnderUncertainty.figure_6_C_1_lottery
#print axioms MWG.ChoiceUnderUncertainty.figure_6_C_1
#print axioms MWG.ChoiceUnderUncertainty.stPetersburg
#print axioms MWG.ChoiceUnderUncertainty.stPetersburg_probabilities
#print axioms MWG.ChoiceUnderUncertainty.concave_bddBelow_le
#print axioms MWG.ChoiceUnderUncertainty.footnote_6_14
#print axioms MWG.ChoiceUnderUncertainty.MoneyContinuous
#print axioms MWG.ChoiceUnderUncertainty.MoneyIndependence
#print axioms MWG.ChoiceUnderUncertainty.MoneyRational
#print axioms MWG.ChoiceUnderUncertainty.atomicMass
#print axioms MWG.ChoiceUnderUncertainty.tsum_atoms_le_one
#print axioms MWG.ChoiceUnderUncertainty.atomicMass_mixM
#print axioms MWG.ChoiceUnderUncertainty.atomicMass_dirac
#print axioms MWG.ChoiceUnderUncertainty.uniform01
#print axioms MWG.ChoiceUnderUncertainty.uniform01_isMoneyLottery
#print axioms MWG.ChoiceUnderUncertainty.atomicMass_uniform01
#print axioms MWG.ChoiceUnderUncertainty.expectedUtility_6_C_1_counterexample
#print axioms MWG.ChoiceUnderUncertainty.euPref
#print axioms MWG.ChoiceUnderUncertainty.RiskAverter
#print axioms MWG.ChoiceUnderUncertainty.RiskNeutral
#print axioms MWG.ChoiceUnderUncertainty.StrictlyRiskAverse
#print axioms MWG.ChoiceUnderUncertainty.riskAverter_iff_jensen
#print axioms MWG.ChoiceUnderUncertainty.jensen_moneyLottery
#print axioms MWG.ChoiceUnderUncertainty.mean_binLot
#print axioms MWG.ChoiceUnderUncertainty.proposition_6_C_1_i_ii
#print axioms MWG.ChoiceUnderUncertainty.IsCertaintyEquivalent
#print axioms MWG.ChoiceUnderUncertainty.certaintyEquivalent_exists
#print axioms MWG.ChoiceUnderUncertainty.certaintyEquivalent_unique
#print axioms MWG.ChoiceUnderUncertainty.probPremium
#print axioms MWG.ChoiceUnderUncertainty.probPremium_spec
#print axioms MWG.ChoiceUnderUncertainty.figure_6_C_3b
#print axioms MWG.ChoiceUnderUncertainty.figure_6_C_2a
#print axioms MWG.ChoiceUnderUncertainty.figure_6_C_2b
#print axioms MWG.ChoiceUnderUncertainty.proposition_6_C_1_ii_iii
#print axioms MWG.ChoiceUnderUncertainty.certaintyEquivalent_le_mean_iff
#print axioms MWG.ChoiceUnderUncertainty.concaveOn_of_midpoint
#print axioms MWG.ChoiceUnderUncertainty.proposition_6_C_1_ii_iv
#print axioms MWG.ChoiceUnderUncertainty.proposition_6_C_1
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_C_3
#print axioms MWG.ChoiceUnderUncertainty.eq_dirac_of_ae_eq_const
#print axioms MWG.ChoiceUnderUncertainty.strictlyRiskAverse_iff
#print axioms MWG.ChoiceUnderUncertainty.riskNeutral_iff_affine
#print axioms MWG.ChoiceUnderUncertainty.footnote_6_16
#print axioms MWG.ChoiceUnderUncertainty.insuranceEU
#print axioms MWG.ChoiceUnderUncertainty.example_6_C_1_expected_wealth
#print axioms MWG.ChoiceUnderUncertainty.deriv_nonpos_of_max_Ici
#print axioms MWG.ChoiceUnderUncertainty.insuranceEU_hasDerivAt
#print axioms MWG.ChoiceUnderUncertainty.example_6_C_1_foc
#print axioms MWG.ChoiceUnderUncertainty.example_6_C_1
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_C_1
#print axioms MWG.ChoiceUnderUncertainty.assetEU
#print axioms MWG.ChoiceUnderUncertainty.assetEU_integrable
#print axioms MWG.ChoiceUnderUncertainty.footnote_6_17
#print axioms MWG.ChoiceUnderUncertainty.example_6_C_2
#print axioms MWG.ChoiceUnderUncertainty.portfolioU
#print axioms MWG.ChoiceUnderUncertainty.portfolio_payoff_nonneg
#print axioms MWG.ChoiceUnderUncertainty.portfolio_integrable
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_C_4a
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_C_4b
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_C_4c
#print axioms MWG.ChoiceUnderUncertainty.arrowPratt
#print axioms MWG.ChoiceUnderUncertainty.arrowPratt_eq_kreps
#print axioms MWG.ChoiceUnderUncertainty.arrowPratt_affine_invariant
#print axioms MWG.ChoiceUnderUncertainty.second_derivative_not_invariant
#print axioms MWG.ChoiceUnderUncertainty.arrowPratt_eq_four_probPremium_slope
#print axioms MWG.ChoiceUnderUncertainty.utility_determined_by_arrowPratt
#print axioms MWG.ChoiceUnderUncertainty.example_6_C_4
#print axioms MWG.ChoiceUnderUncertainty.example_6_C_4_general
#print axioms MWG.ChoiceUnderUncertainty.simpleMeasure
#print axioms MWG.ChoiceUnderUncertainty.integral_simpleMeasure
#print axioms MWG.ChoiceUnderUncertainty.simpleMeasure_isMoneyLottery
#print axioms MWG.ChoiceUnderUncertainty.MoreRiskAverseI
#print axioms MWG.ChoiceUnderUncertainty.MoreRiskAverseII
#print axioms MWG.ChoiceUnderUncertainty.MoreRiskAverseIII
#print axioms MWG.ChoiceUnderUncertainty.MoreRiskAverseIV
#print axioms MWG.ChoiceUnderUncertainty.MoreRiskAverseV
#print axioms MWG.ChoiceUnderUncertainty.kreps_of_moreRiskAverseV
#print axioms MWG.ChoiceUnderUncertainty.moreRiskAverseII_of_kreps
#print axioms MWG.ChoiceUnderUncertainty.kreps_of_moreRiskAverseII
#print axioms MWG.ChoiceUnderUncertainty.exists_Icc_image_nhds
#print axioms MWG.ChoiceUnderUncertainty.moreRiskAverse_ii_iii
#print axioms MWG.ChoiceUnderUncertainty.moreRiskAverse_iii_v
#print axioms MWG.ChoiceUnderUncertainty.moreRiskAverse_v_iii
#print axioms MWG.ChoiceUnderUncertainty.moreRiskAverse_iii_iv
#print axioms MWG.ChoiceUnderUncertainty.moreRiskAverse_iv_i
#print axioms MWG.ChoiceUnderUncertainty.proposition_6_C_2
#print axioms MWG.ChoiceUnderUncertainty.shiftU
#print axioms MWG.ChoiceUnderUncertainty.deriv_shiftU
#print axioms MWG.ChoiceUnderUncertainty.arrowPratt_shiftU
#print axioms MWG.ChoiceUnderUncertainty.probPremium_shiftU
#print axioms MWG.ChoiceUnderUncertainty.contDiffAt_shiftU
#print axioms MWG.ChoiceUnderUncertainty.isMoneyLottery_map_add
#print axioms MWG.ChoiceUnderUncertainty.DecreasingAbsoluteRiskAversion
#print axioms MWG.ChoiceUnderUncertainty.shift_tfae
#print axioms MWG.ChoiceUnderUncertainty.proposition_6_C_3
#print axioms MWG.ChoiceUnderUncertainty.relativeRiskAversion
#print axioms MWG.ChoiceUnderUncertainty.relativeRiskAversion_eq_kreps
#print axioms MWG.ChoiceUnderUncertainty.relativeRiskAversion_eq
#print axioms MWG.ChoiceUnderUncertainty.decreasingAbsolute_of_decreasingRelative
#print axioms MWG.ChoiceUnderUncertainty.decreasingRelative_not_of_decreasingAbsolute
#print axioms MWG.ChoiceUnderUncertainty.scaleU
#print axioms MWG.ChoiceUnderUncertainty.deriv_scaleU
#print axioms MWG.ChoiceUnderUncertainty.arrowPratt_scaleU
#print axioms MWG.ChoiceUnderUncertainty.scale_tfae
#print axioms MWG.ChoiceUnderUncertainty.proposition_6_C_4
#print axioms MWG.ChoiceUnderUncertainty.concave_supergradient
#print axioms MWG.ChoiceUnderUncertainty.mem_interior_image
#print axioms MWG.ChoiceUnderUncertainty.invest_compare
#print axioms MWG.ChoiceUnderUncertainty.example_6_C_2_continued
#print axioms MWG.ChoiceUnderUncertainty.moreRiskAverseI_trans
#print axioms MWG.ChoiceUnderUncertainty.arrowPratt_log
#print axioms MWG.ChoiceUnderUncertainty.moreRiskAverse_not_complete
#print axioms MWG.ChoiceUnderUncertainty.assetEU_shiftU
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_C_8
#print axioms MWG.ChoiceUnderUncertainty.proportion_objective
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_C_11
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_C_2a
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_C_2a_moments
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_C_2a_note
#print axioms MWG.ChoiceUnderUncertainty.meanVarianceU
#print axioms MWG.ChoiceUnderUncertainty.meanVarianceU_binLot
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_C_2b
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_C_5a
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_C_5b
#print axioms MWG.ChoiceUnderUncertainty.bumpUtility
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_C_5c
#print axioms MWG.ChoiceUnderUncertainty.deriv2_congr_Ioi
#print axioms MWG.ChoiceUnderUncertainty.relativeRiskAversion_crra
#print axioms MWG.ChoiceUnderUncertainty.relativeRiskAversion_log
#print axioms MWG.ChoiceUnderUncertainty.marginal_of_constant_relative
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_C_12a
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_C_12a_printed_counterexample
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_C_12b
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_C_12c
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_C_12c_printed_counterexample
#print axioms MWG.ChoiceUnderUncertainty.maxProfit
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_C_13
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_C_14a
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_C_14b
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_C_14c
#print axioms MWG.ChoiceUnderUncertainty.IsSellingPrice
#print axioms MWG.ChoiceUnderUncertainty.IsBuyingPrice
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_C_16a
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_C_16b
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_C_16c_cara
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_C_16c_riskless
#print axioms MWG.ChoiceUnderUncertainty.sqrt_of_sq
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_C_16d
#print axioms MWG.ChoiceUnderUncertainty.arrowPratt_sqrt
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_C_18a
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_C_18b
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_C_18c
#print axioms MWG.ChoiceUnderUncertainty.concave_le_tangent
#print axioms MWG.ChoiceUnderUncertainty.hasDerivAt_expected
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_C_9a
#print axioms MWG.ChoiceUnderUncertainty.prudence
#print axioms MWG.ChoiceUnderUncertainty.prudence_eq_arrowPratt
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_C_9b
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_C_9c
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_C_9c_degenerate
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_C_9d
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_C_9d_cara
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_C_20
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_C_20_instance
#print axioms MWG.ChoiceUnderUncertainty.twoAssetEU
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_C_15a
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_C_15b
#print axioms MWG.ChoiceUnderUncertainty.twoAssetFOC
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_C_15c
#print axioms MWG.ChoiceUnderUncertainty.foc_along_a
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_C_15d
#print axioms MWG.ChoiceUnderUncertainty.foc_along_π
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_C_15f
#print axioms MWG.ChoiceUnderUncertainty.grossReturn
#print axioms MWG.ChoiceUnderUncertainty.grossReturn_pos
#print axioms MWG.ChoiceUnderUncertainty.crra
#print axioms MWG.ChoiceUnderUncertainty.crraObjective
#print axioms MWG.ChoiceUnderUncertainty.crraObjective_homog
#print axioms MWG.ChoiceUnderUncertainty.isMaxOn_const_mul_iff
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_C_17_period1
#print axioms MWG.ChoiceUnderUncertainty.crraObjective_continuousOn
#print axioms MWG.ChoiceUnderUncertainty.crraValue
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_C_17_period0
#print axioms MWG.ChoiceUnderUncertainty.caraObjective
#print axioms MWG.ChoiceUnderUncertainty.caraAmount
#print axioms MWG.ChoiceUnderUncertainty.caraObjective_eq
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_C_17_cara
#print axioms MWG.ChoiceUnderUncertainty.isMaxOn_add_const_iff
#print axioms MWG.ChoiceUnderUncertainty.logObjective
#print axioms MWG.ChoiceUnderUncertainty.logObjective_shift
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_C_17_log
#print axioms MWG.ChoiceUnderUncertainty.caraPortfolioEU
#print axioms MWG.ChoiceUnderUncertainty.caraCE
#print axioms MWG.ChoiceUnderUncertainty.caraPortfolioEU_eq
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_C_19
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_C_19_exists
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_C_19_instance
#print axioms MWG.ChoiceUnderUncertainty.IsMWGDist
#print axioms MWG.ChoiceUnderUncertainty.IsMWGDist.ae_mem
#print axioms MWG.ChoiceUnderUncertainty.IsMWGDist.isMoneyLottery
#print axioms MWG.ChoiceUnderUncertainty.IsMWGDist.integrable_monotone
#print axioms MWG.ChoiceUnderUncertainty.FOSD
#print axioms MWG.ChoiceUnderUncertainty.monotone_step
#print axioms MWG.ChoiceUnderUncertainty.integral_step
#print axioms MWG.ChoiceUnderUncertainty.proposition_6_D_1
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_D_2_mean
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_D_2_example
#print axioms MWG.ChoiceUnderUncertainty.example_6_D_1
#print axioms MWG.ChoiceUnderUncertainty.integral_smul_dirac
#print axioms MWG.ChoiceUnderUncertainty.integrable_smul_dirac
#print axioms MWG.ChoiceUnderUncertainty.lot3M
#print axioms MWG.ChoiceUnderUncertainty.integral_lot3M
#print axioms MWG.ChoiceUnderUncertainty.figure_6_D_2
#print axioms MWG.ChoiceUnderUncertainty.example_6_D_1_converse
#print axioms MWG.ChoiceUnderUncertainty.SOSD
#print axioms MWG.ChoiceUnderUncertainty.IsMWGDist.integrable_concave
#print axioms MWG.ChoiceUnderUncertainty.min_utility_props
#print axioms MWG.ChoiceUnderUncertainty.integral_min_eq
#print axioms MWG.ChoiceUnderUncertainty.IntegralCondition
#print axioms MWG.ChoiceUnderUncertainty.equal_areas
#print axioms MWG.ChoiceUnderUncertainty.sosd_integralCondition
#print axioms MWG.ChoiceUnderUncertainty.IsMeanPreservingSpread
#print axioms MWG.ChoiceUnderUncertainty.sosd_of_meanPreservingSpread
#print axioms MWG.ChoiceUnderUncertainty.sum_by_parts
#print axioms MWG.ChoiceUnderUncertainty.gridPt
#print axioms MWG.ChoiceUnderUncertainty.gridInterp
#print axioms MWG.ChoiceUnderUncertainty.gridInterp_cell
#print axioms MWG.ChoiceUnderUncertainty.gridInterp_continuous
#print axioms MWG.ChoiceUnderUncertainty.exists_cell
#print axioms MWG.ChoiceUnderUncertainty.gridInterp_between
#print axioms MWG.ChoiceUnderUncertainty.sosd_of_integralCondition
#print axioms MWG.ChoiceUnderUncertainty.proposition_6_D_2_i_iii
#print axioms MWG.ChoiceUnderUncertainty.integralCondition_of_single_crossing
#print axioms MWG.ChoiceUnderUncertainty.integrable_lot3M
#print axioms MWG.ChoiceUnderUncertainty.lot3M_apply
#print axioms MWG.ChoiceUnderUncertainty.lot3M_isMWGDist
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_D_1a
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_D_1b
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_D_4a
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_D_4b
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_D_4d
#print axioms MWG.ChoiceUnderUncertainty.example_6_D_2
#print axioms MWG.ChoiceUnderUncertainty.elementaryIncrease
#print axioms MWG.ChoiceUnderUncertainty.integral_elementaryIncrease
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_D_3
#print axioms MWG.ChoiceUnderUncertainty.dirac_compProd_map_add
#print axioms MWG.ChoiceUnderUncertainty.binLot_real
#print axioms MWG.ChoiceUnderUncertainty.example_6_D_2_spread
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_D_4c
#print axioms MWG.ChoiceUnderUncertainty.hatFn
#print axioms MWG.ChoiceUnderUncertainty.hatFn_nonneg
#print axioms MWG.ChoiceUnderUncertainty.continuous_hatFn
#print axioms MWG.ChoiceUnderUncertainty.hatFn_le_one
#print axioms MWG.ChoiceUnderUncertainty.hatFn_eq_zero
#print axioms MWG.ChoiceUnderUncertainty.abs_sub_lt_of_hatFn_pos
#print axioms MWG.ChoiceUnderUncertainty.hatFn_grid_sum
#print axioms MWG.ChoiceUnderUncertainty.hatFn_sum_one
#print axioms MWG.ChoiceUnderUncertainty.hatFn_sum_id
#print axioms MWG.ChoiceUnderUncertainty.hatFn_sum_concave
#print axioms MWG.ChoiceUnderUncertainty.hatFn_sum_approx
#print axioms MWG.ChoiceUnderUncertainty.integrable_of_continuous_ae_Ioc
#print axioms MWG.ChoiceUnderUncertainty.gridMass
#print axioms MWG.ChoiceUnderUncertainty.gridCtr
#print axioms MWG.ChoiceUnderUncertainty.gridMass_nonneg
#print axioms MWG.ChoiceUnderUncertainty.gridMass_sum
#print axioms MWG.ChoiceUnderUncertainty.abs_integral_hat_sub_le
#print axioms MWG.ChoiceUnderUncertainty.gridMass_mul_ctr
#print axioms MWG.ChoiceUnderUncertainty.abs_gridCtr_sub_le
#print axioms MWG.ChoiceUnderUncertainty.sum_gridMass_mul
#print axioms MWG.ChoiceUnderUncertainty.dilation_le
#print axioms MWG.ChoiceUnderUncertainty.dilation_mean
#print axioms MWG.ChoiceUnderUncertainty.le_contraction
#print axioms MWG.ChoiceUnderUncertainty.contraction_mean
#print axioms MWG.ChoiceUnderUncertainty.atomLottery
#print axioms MWG.ChoiceUnderUncertainty.expectedUtility_atomLottery
#print axioms MWG.ChoiceUnderUncertainty.mem_support_atomLottery
#print axioms MWG.ChoiceUnderUncertainty.integral_sum_dirac
#print axioms MWG.ChoiceUnderUncertainty.exists_grid_martingale_coupling
#print axioms MWG.ChoiceUnderUncertainty.eq_of_mapClusterPt_of_tendsto
#print axioms MWG.ChoiceUnderUncertainty.tendsto_hat_average
#print axioms MWG.ChoiceUnderUncertainty.truncAt
#print axioms MWG.ChoiceUnderUncertainty.continuous_truncAt
#print axioms MWG.ChoiceUnderUncertainty.abs_truncAt_le
#print axioms MWG.ChoiceUnderUncertainty.truncAt_eq
#print axioms MWG.ChoiceUnderUncertainty.exists_martingale_coupling
#print axioms MWG.ChoiceUnderUncertainty.proposition_6_D_2_i_ii
#print axioms MWG.ChoiceUnderUncertainty.proposition_6_D_2
#print axioms MWG.ChoiceUnderUncertainty.example_6_D_2_equivalence
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_D_4c_converse
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_D_4c_iff
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_D_4c_instance
#print axioms MWG.ChoiceUnderUncertainty.inducedLaw
#print axioms MWG.ChoiceUnderUncertainty.inducedLaw_cdf
#print axioms MWG.ChoiceUnderUncertainty.integral_inducedLaw
#print axioms MWG.ChoiceUnderUncertainty.HasExtendedEU
#print axioms MWG.ChoiceUnderUncertainty.footnote_6_24
#print axioms MWG.ChoiceUnderUncertainty.absorb_probabilities
#print axioms MWG.ChoiceUnderUncertainty.certainty_line_mrs
#print axioms MWG.ChoiceUnderUncertainty.example_6_E_1_uniform
#print axioms MWG.ChoiceUnderUncertainty.example_6_E_1_dependent
#print axioms MWG.ChoiceUnderUncertainty.ExtendedIndependence
#print axioms MWG.ChoiceUnderUncertainty.proposition_6_E_1
#print axioms MWG.ChoiceUnderUncertainty.proposition_6_E_1_converse
#print axioms MWG.ChoiceUnderUncertainty.SureThing
#print axioms MWG.ChoiceUnderUncertainty.sureThing_of_additive
#print axioms MWG.ChoiceUnderUncertainty.riskAversion_iff_concave_states
#print axioms MWG.ChoiceUnderUncertainty.regret
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_E_1
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_E_2a
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_E_2b
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_E_2c
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_E_3
#print axioms MWG.ChoiceUnderUncertainty.SureThingOn
#print axioms MWG.ChoiceUnderUncertainty.SureThing.sureThingOn
#print axioms MWG.ChoiceUnderUncertainty.EssentialState
#print axioms MWG.ChoiceUnderUncertainty.proposition_6_E_2
#print axioms MWG.ChoiceUnderUncertainty.thomsenV
#print axioms MWG.ChoiceUnderUncertainty.thomsenPref
#print axioms MWG.ChoiceUnderUncertainty.thomsen_mono_left
#print axioms MWG.ChoiceUnderUncertainty.thomsen_mono_right
#print axioms MWG.ChoiceUnderUncertainty.thomsenPref_rational
#print axioms MWG.ChoiceUnderUncertainty.thomsenPref_continuous
#print axioms MWG.ChoiceUnderUncertainty.thomsenPref_sureThing
#print axioms MWG.ChoiceUnderUncertainty.twoStateVec
#print axioms MWG.ChoiceUnderUncertainty.twoStateVec_zero
#print axioms MWG.ChoiceUnderUncertainty.twoStateVec_one
#print axioms MWG.ChoiceUnderUncertainty.twoStateVec_mem
#print axioms MWG.ChoiceUnderUncertainty.thomsenV_twoStateVec
#print axioms MWG.ChoiceUnderUncertainty.thomsenPref_not_additive
#print axioms MWG.ChoiceUnderUncertainty.proposition_6_E_2_false
#print axioms MWG.ChoiceUnderUncertainty.thomsenPref_essential
#print axioms MWG.ChoiceUnderUncertainty.proposition_6_E_2_instance
#print axioms MWG.ChoiceUnderUncertainty.statePref
#print axioms MWG.ChoiceUnderUncertainty.StateUniform
#print axioms MWG.ChoiceUnderUncertainty.stateUniform_affine
#print axioms MWG.ChoiceUnderUncertainty.proposition_6_F_1
#print axioms MWG.ChoiceUnderUncertainty.proposition_6_F_1_sure
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_F_1_utility
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_F_1_probabilities
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_F_1_probabilities_not_unique
#print axioms MWG.ChoiceUnderUncertainty.example_6_F_1
#print axioms MWG.ChoiceUnderUncertainty.gsUtilityW
#print axioms MWG.ChoiceUnderUncertainty.gsUtilityB
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_F_2a
#print axioms MWG.ChoiceUnderUncertainty.exercise_6_F_2b
