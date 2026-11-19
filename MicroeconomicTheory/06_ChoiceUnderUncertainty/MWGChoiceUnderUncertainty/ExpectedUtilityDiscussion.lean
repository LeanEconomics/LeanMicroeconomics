/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGChoiceUnderUncertainty.ExpectedUtilityTheorem

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
