/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGChoiceUnderUncertainty.DominanceExamples
import MWGChoiceUnderUncertainty.ExpectedUtilityDiscussion
import MWGChoiceUnderUncertainty.ExercisesC3
import ChoiceUnderUncertainty.AnscombeAumann
import MWGClassicalDemand.CloserSeparable

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
