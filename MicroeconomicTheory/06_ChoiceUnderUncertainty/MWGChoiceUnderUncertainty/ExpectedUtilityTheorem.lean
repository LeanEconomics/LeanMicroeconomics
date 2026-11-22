/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGChoiceUnderUncertainty.Lotteries
import ChoiceUnderUncertainty.LotteryEvaluation

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
