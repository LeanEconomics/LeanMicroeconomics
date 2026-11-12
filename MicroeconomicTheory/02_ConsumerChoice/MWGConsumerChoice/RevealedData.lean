/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGConsumerChoice.WeakAxiom
import MWGConsumerChoice.DemandCalculus
import MWGConsumerChoice.Aggregation
import ChoicePreferenceUtility.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Revealed preference from finitely many observations

MWG, Section 2.F: Figure 2.F.5 (p. 33), Example 2.F.1 (p. 35) with Exercise 2.F.2, and
Exercises 2.F.3 and 2.F.4 (pp. 37–38).

An observation is a price vector, a wealth level and the chosen bundle. Bundle `x` chosen at
`(p, w)` is directly revealed preferred to `y ≠ x` when `y` was affordable, `p·y ≤ w`. Two
observations are consistent with the weak axiom when neither is revealed preferred to the
other while the other is revealed preferred to it.
-/

namespace MWG.ConsumerChoice

/-- **Section 2.F** (MWG, p. 29). Bundle `x`, chosen at `(p, w)`, is directly revealed
preferred to `y`: `y` was affordable and not chosen. -/
def RevealedPreferred {L : ℕ} (p : Fin L → ℝ) (w : ℝ) (x y : Fin L → ℝ) : Prop :=
  p ⬝ᵥ y ≤ w ∧ y ≠ x

/-- **Definition 2.F.1** (MWG, p. 29) for two observations `(p, w, x)` and `(p', w', x')`. -/
def PairWeakAxiom {L : ℕ} (p : Fin L → ℝ) (w : ℝ) (x : Fin L → ℝ) (p' : Fin L → ℝ) (w' : ℝ)
    (x' : Fin L → ℝ) : Prop :=
  (RevealedPreferred p w x x' → w' < p' ⬝ᵥ x) ∧ (RevealedPreferred p' w' x' x → w < p ⬝ᵥ x')

/-- A demand function satisfying the weak axiom satisfies it on any two of its observations. -/
theorem pairWeakAxiom_of_weakAxiom {L : ℕ} {x : DemandFunction L} (hWA : WeakAxiom x)
    {p p' : Fin L → ℝ} {w w' : ℝ} (hd : PWDomain p w) (hd' : PWDomain p' w') :
    PairWeakAxiom p w (x p w) p' w' (x p' w') :=
  ⟨fun h => hWA p w p' w' hd hd' h.1 h.2, fun h => hWA p' w' p w hd' hd h.1 h.2⟩

/-- **Figure 2.F.5** (MWG, p. 33). The weak axiom does not give the law of demand for
uncompensated price changes. Prices fall from `p = (2, 1)` to `p' = (1, 1)` at wealth `w = 2`;
the bundles `x = (1/2, 1)` and `x' = (1/4, 7/4)` exhaust the budgets and satisfy the weak
axiom, yet demand for good 1 falls from `1/2` to `1/4`. -/
theorem figure_2_F_5 :
    PairWeakAxiom ![2, 1] 2 ![1 / 2, 1] ![1, 1] 2 ![1 / 4, 7 / 4] ∧
      ![(2 : ℝ), 1] ⬝ᵥ ![1 / 2, 1] = 2 ∧ ![(1 : ℝ), 1] ⬝ᵥ ![1 / 4, 7 / 4] = 2 ∧
      (![1 / 4, 7 / 4] : Fin 2 → ℝ) 0 < (![1 / 2, 1] : Fin 2 → ℝ) 0 := by
  refine ⟨⟨fun h => ?_, fun _ => ?_⟩, ?_, ?_, ?_⟩ <;>
    simp [RevealedPreferred, dotProduct, Fin.sum_univ_two] at * <;> norm_num at *

/-! ### Example 2.F.1 and Exercise 2.F.2 -/

/-- **Example 2.F.1** (MWG, p. 35). The price vectors `p¹ = (2,1,2)`, `p² = (2,2,1)`,
`p³ = (1,2,2)`. -/
def example_2_F_1_prices : Fin 3 → Fin 3 → ℝ := ![![2, 1, 2], ![2, 2, 1], ![1, 2, 2]]

/-- **Example 2.F.1** (MWG, p. 35). The choices `x¹ = (1,2,2)`, `x² = (2,1,2)`,
`x³ = (2,2,1)`. -/
def example_2_F_1_choices : Fin 3 → Fin 3 → ℝ := ![![1, 2, 2], ![2, 1, 2], ![2, 2, 1]]

/-- **Example 2.F.1** (MWG, p. 35). Each choice exhausts the common wealth 8. -/
theorem example_2_F_1_walras (i : Fin 3) :
    example_2_F_1_prices i ⬝ᵥ example_2_F_1_choices i = 8 := by
  fin_cases i <;>
    simp [example_2_F_1_prices, example_2_F_1_choices, dotProduct, Fin.sum_univ_three] <;>
    norm_num

/-- **Exercise 2.F.2** (MWG, p. 37), first claim. Any two of the three observations satisfy
the weak axiom. -/
theorem exercise_2_F_2_pairs (i j : Fin 3) :
    PairWeakAxiom (example_2_F_1_prices i) 8 (example_2_F_1_choices i)
      (example_2_F_1_prices j) 8 (example_2_F_1_choices j) := by
  fin_cases i <;> fin_cases j <;>
    simp [PairWeakAxiom, RevealedPreferred, example_2_F_1_prices, example_2_F_1_choices,
      dotProduct, Fin.sum_univ_three] <;> norm_num

/-- **Exercise 2.F.2** (MWG, p. 37), second claim. `x³` is revealed preferred to `x²`, `x²` to
`x¹`, and `x¹` to `x³` (indices `0, 1, 2` for observations 1, 2, 3). -/
theorem exercise_2_F_2_cycle :
    RevealedPreferred (example_2_F_1_prices 2) 8 (example_2_F_1_choices 2)
        (example_2_F_1_choices 1) ∧
      RevealedPreferred (example_2_F_1_prices 1) 8 (example_2_F_1_choices 1)
        (example_2_F_1_choices 0) ∧
      RevealedPreferred (example_2_F_1_prices 0) 8 (example_2_F_1_choices 0)
        (example_2_F_1_choices 2) := by
  refine ⟨⟨?_, fun h => ?_⟩, ⟨?_, fun h => ?_⟩, ⟨?_, fun h => ?_⟩⟩ <;>
    first
    | (simp [example_2_F_1_prices, example_2_F_1_choices, dotProduct, Fin.sum_univ_three];
        norm_num)
    | (have := congrFun h 0
       simp [example_2_F_1_choices] at this
       done)
    | (have := congrFun h 1
       simp [example_2_F_1_choices] at this)

/-- **Example 2.F.1** (MWG, p. 35). The data are incompatible with rational preferences: no
complete and transitive `≿` has `x^i` as the unique best bundle of each budget
`B_{p^i, 8}`. -/
theorem example_2_F_1_not_rationalizable :
    ¬ ∃ r : (Fin 3 → ℝ) → (Fin 3 → ℝ) → Prop, Kreps.ChoicePreferenceUtility.Rational r ∧
      ∀ i, Kreps.ChoicePreferenceUtility.PrefChoice r
        (budgetSet (example_2_F_1_prices i) 8) = {example_2_F_1_choices i} := by
  rintro ⟨r, hr, hgen⟩
  have hbest : ∀ i, example_2_F_1_choices i ∈
      Kreps.ChoicePreferenceUtility.PrefChoice r (budgetSet (example_2_F_1_prices i) 8) := by
    intro i; rw [hgen i]; rfl
  have hnn : ∀ i, example_2_F_1_choices i ∈ nonnegOrthant 3 := fun i => (hbest i).1.1
  obtain ⟨⟨h21, _⟩, ⟨h10, _⟩, ⟨h02, _⟩⟩ := exercise_2_F_2_cycle
  -- x¹ ≿ x³, x³ ≿ x², x² ≿ x¹
  have r02 : r (example_2_F_1_choices 0) (example_2_F_1_choices 2) := (hbest 0).2 _ ⟨hnn 2, h02⟩
  have r21 : r (example_2_F_1_choices 2) (example_2_F_1_choices 1) := (hbest 2).2 _ ⟨hnn 1, h21⟩
  have r10 : r (example_2_F_1_choices 1) (example_2_F_1_choices 0) := (hbest 1).2 _ ⟨hnn 0, h10⟩
  -- so x³ is also best in B¹, contradicting uniqueness
  have r20 : r (example_2_F_1_choices 2) (example_2_F_1_choices 0) := hr.2 _ _ _ r21 r10
  have hin : example_2_F_1_choices 2 ∈
      Kreps.ChoicePreferenceUtility.PrefChoice r (budgetSet (example_2_F_1_prices 0) 8) :=
    ⟨⟨hnn 2, h02⟩, fun y hy => hr.2 _ _ _ r20 ((hbest 0).2 y hy)⟩
  rw [hgen 0, Set.mem_singleton_iff] at hin
  have := congrFun hin 0
  simp [example_2_F_1_choices] at this

/-! ### Exercise 2.F.3 -/

/-- **Exercise 2.F.3** (MWG, p. 37). Year 1: prices `(100, 100)`, quantities `(100, 100)`,
wealth 20000. -/
def exercise_2_F_3_p1 : Fin 2 → ℝ := ![100, 100]

/-- Year-1 quantities. -/
def exercise_2_F_3_x1 : Fin 2 → ℝ := ![100, 100]

/-- Year 2: prices `(100, 80)`. -/
def exercise_2_F_3_p2 : Fin 2 → ℝ := ![100, 80]

/-- Year-2 quantities `(120, y)`. -/
def exercise_2_F_3_x2 (y : ℝ) : Fin 2 → ℝ := ![120, y]

/-- Year-2 wealth (Walras' law): `w² = 12000 + 80 y`. -/
def exercise_2_F_3_w2 (y : ℝ) : ℝ := 12000 + 80 * y

/-- Year 1 is revealed preferred to year 2 exactly when `y ≤ 80`. -/
theorem exercise_2_F_3_rp12 (y : ℝ) :
    RevealedPreferred exercise_2_F_3_p1 20000 exercise_2_F_3_x1 (exercise_2_F_3_x2 y) ↔
      y ≤ 80 := by
  simp only [RevealedPreferred, exercise_2_F_3_p1, exercise_2_F_3_x1, exercise_2_F_3_x2,
    dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor
  · rintro ⟨h, _⟩
    linarith
  · intro h
    refine ⟨by linarith, fun he => ?_⟩
    have := congrFun he 0
    norm_num at this

/-- Year 2 is revealed preferred to year 1 exactly when `y ≥ 75`. -/
theorem exercise_2_F_3_rp21 (y : ℝ) :
    RevealedPreferred exercise_2_F_3_p2 (exercise_2_F_3_w2 y) (exercise_2_F_3_x2 y)
      exercise_2_F_3_x1 ↔ 75 ≤ y := by
  simp only [RevealedPreferred, exercise_2_F_3_p2, exercise_2_F_3_x1, exercise_2_F_3_x2,
    exercise_2_F_3_w2, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor
  · rintro ⟨h, _⟩
    linarith
  · intro h
    refine ⟨by linarith, fun he => ?_⟩
    have := congrFun he 0
    norm_num at this

/-- **Exercise 2.F.3(a)** (MWG, p. 37). The two years are inconsistent with the weak axiom
exactly when `75 ≤ y ≤ 80`. -/
theorem exercise_2_F_3a (y : ℝ) :
    ¬ PairWeakAxiom exercise_2_F_3_p1 20000 exercise_2_F_3_x1 exercise_2_F_3_p2
      (exercise_2_F_3_w2 y) (exercise_2_F_3_x2 y) ↔ 75 ≤ y ∧ y ≤ 80 := by
  have e1 : exercise_2_F_3_p2 ⬝ᵥ exercise_2_F_3_x1 = 18000 := by
    simp [exercise_2_F_3_p2, exercise_2_F_3_x1, dotProduct, Fin.sum_univ_two]; norm_num
  have e2 : exercise_2_F_3_p1 ⬝ᵥ exercise_2_F_3_x2 y = 12000 + 100 * y := by
    simp [exercise_2_F_3_p1, exercise_2_F_3_x2, dotProduct, Fin.sum_univ_two]; ring
  simp only [PairWeakAxiom, exercise_2_F_3_rp12, exercise_2_F_3_rp21, e1, e2]
  simp only [exercise_2_F_3_w2]
  constructor
  · intro h
    by_contra hc
    apply h
    refine ⟨fun h' => ?_, fun h' => ?_⟩
    · by_contra h''
      exact hc ⟨by linarith, h'⟩
    · by_contra h''
      exact hc ⟨h', by linarith⟩
  · rintro ⟨h1, h2⟩ ⟨k1, _⟩
    have := k1 h2
    linarith

/-- **Exercise 2.F.3(b)** (MWG, p. 37). Year 1 is revealed preferred to year 2 iff `y ≤ 80`;
among data consistent with the weak axiom, iff `y < 75`. -/
theorem exercise_2_F_3b (y : ℝ) :
    (RevealedPreferred exercise_2_F_3_p1 20000 exercise_2_F_3_x1 (exercise_2_F_3_x2 y) ↔
      y ≤ 80) ∧
    (RevealedPreferred exercise_2_F_3_p1 20000 exercise_2_F_3_x1 (exercise_2_F_3_x2 y) ∧
      PairWeakAxiom exercise_2_F_3_p1 20000 exercise_2_F_3_x1 exercise_2_F_3_p2
        (exercise_2_F_3_w2 y) (exercise_2_F_3_x2 y) ↔ y < 75) := by
  refine ⟨exercise_2_F_3_rp12 y, ?_⟩
  rw [exercise_2_F_3_rp12]
  have ha := exercise_2_F_3a y
  constructor
  · rintro ⟨h1, h2⟩
    by_contra hc
    push Not at hc
    exact ha.mpr ⟨hc, h1⟩ h2
  · intro h
    refine ⟨by linarith, ?_⟩
    by_contra hc
    have := ha.mp hc
    linarith [this.1]

/-- **Exercise 2.F.3(c)** (MWG, p. 37). Year 2 is revealed preferred to year 1 iff `y ≥ 75`;
among data consistent with the weak axiom, iff `y > 80`. -/
theorem exercise_2_F_3c (y : ℝ) :
    (RevealedPreferred exercise_2_F_3_p2 (exercise_2_F_3_w2 y) (exercise_2_F_3_x2 y)
      exercise_2_F_3_x1 ↔ 75 ≤ y) ∧
    (RevealedPreferred exercise_2_F_3_p2 (exercise_2_F_3_w2 y) (exercise_2_F_3_x2 y)
      exercise_2_F_3_x1 ∧
      PairWeakAxiom exercise_2_F_3_p1 20000 exercise_2_F_3_x1 exercise_2_F_3_p2
        (exercise_2_F_3_w2 y) (exercise_2_F_3_x2 y) ↔ 80 < y) := by
  refine ⟨exercise_2_F_3_rp21 y, ?_⟩
  rw [exercise_2_F_3_rp21]
  have ha := exercise_2_F_3a y
  constructor
  · rintro ⟨h1, h2⟩
    by_contra hc
    push Not at hc
    exact ha.mpr ⟨h1, hc⟩ h2
  · intro h
    refine ⟨by linarith, ?_⟩
    by_contra hc
    have := ha.mp hc
    linarith [this.2]

/-- **Exercise 2.F.3(d)** (MWG, p. 37). There is no `y` for which the information is
insufficient: for every `y`, one of (a), (b) or (c) holds. -/
theorem exercise_2_F_3d (y : ℝ) :
    (75 ≤ y ∧ y ≤ 80) ∨
      RevealedPreferred exercise_2_F_3_p1 20000 exercise_2_F_3_x1 (exercise_2_F_3_x2 y) ∨
      RevealedPreferred exercise_2_F_3_p2 (exercise_2_F_3_w2 y) (exercise_2_F_3_x2 y)
        exercise_2_F_3_x1 := by
  rw [exercise_2_F_3_rp12, exercise_2_F_3_rp21]
  rcases le_or_gt y 80 with h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (by linarith))

/-- **Exercise 2.F.3(e)-(f)** (MWG, p. 37), the vacuous range. For `75 ≤ y ≤ 80` no demand
function satisfying the weak axiom produces both observations, so under the exercise's
assumption every conclusion (in particular inferiority of either good) holds vacuously. -/
theorem exercise_2_F_3_inconsistent {x : DemandFunction 2} (hWA : WeakAxiom x) {y : ℝ}
    (hy1 : 75 ≤ y) (hy2 : y ≤ 80) (h1 : x exercise_2_F_3_p1 20000 = exercise_2_F_3_x1)
    (h2 : x exercise_2_F_3_p2 (exercise_2_F_3_w2 y) = exercise_2_F_3_x2 y) : False := by
  have hd1 : PWDomain exercise_2_F_3_p1 20000 :=
    ⟨fun l => by fin_cases l <;> simp [exercise_2_F_3_p1], by norm_num⟩
  have hd2 : PWDomain exercise_2_F_3_p2 (exercise_2_F_3_w2 y) :=
    ⟨fun l => by fin_cases l <;> simp [exercise_2_F_3_p2],
      by simp only [exercise_2_F_3_w2]; linarith⟩
  have h := pairWeakAxiom_of_weakAxiom hWA hd1 hd2
  rw [h1, h2] at h
  exact (exercise_2_F_3a y).mpr ⟨hy1, hy2⟩ h

/-- A demand that falls with wealth somewhere has an inferior good at some intermediate
wealth, given differentiability (mean value theorem). -/
theorem exists_inferiorAt_of_decrease {L : ℕ} {x : DemandFunction L}
    (hdiff : ∀ p w, PWDomain p w → DifferentiableAt ℝ (Function.uncurry x) (p, w))
    {p : Fin L → ℝ} (hp : StrictlyPositive p) {wa wb : ℝ} (hwa : 0 < wa) (hab : wa < wb)
    (l : Fin L) (hdec : x p wb l < x p wa l) :
    ∃ w ∈ Set.Ioo wa wb, InferiorAt x p w l := by
  have hder : ∀ t, 0 < t → HasDerivAt (fun s => x p s l)
      (wealthEffect (fderiv ℝ (Function.uncurry x) (p, t)) l) t := by
    intro t ht
    have hD := (hdiff p t ⟨hp, ht⟩).hasFDerivAt
    have h := hasDerivAt_pi.mp (hasDerivAt_line (x := x) (p := p) (v := 0) (w := 0) (c := 1)
      (t₀ := t) (by simpa using hD)) l
    simpa [wealthEffect] using h
  have hcont : ContinuousOn (fun s => x p s l) (Set.Icc wa wb) :=
    fun t ht => (hder t (by linarith [ht.1])).continuousAt.continuousWithinAt
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope (fun s => x p s l)
    (fun t => wealthEffect (fderiv ℝ (Function.uncurry x) (p, t)) l) hab hcont
    (fun t ht => hder t (by linarith [ht.1]))
  refine ⟨c, hc, ?_⟩
  change wealthEffect (fderiv ℝ (Function.uncurry x) (p, c)) l < 0
  rw [hslope]
  exact div_neg_of_neg_of_pos (by linarith) (by linarith)

/-- The wealth-compensated year-2 demand `x̂ = x(p², 18000)`: by the compensated law of
demand, `x̂₂ ≥ 100`, and by Walras' law `x̂₁ = 180 - (4/5) x̂₂ ≤ 100`. -/
theorem exercise_2_F_3_compensated {x : DemandFunction 2} (hW : WalrasLaw x)
    (hWA : WeakAxiom x) (h1 : x exercise_2_F_3_p1 20000 = exercise_2_F_3_x1) :
    100 ≤ x exercise_2_F_3_p2 18000 1 ∧ x exercise_2_F_3_p2 18000 0 ≤ 100 := by
  have hd1 : PWDomain exercise_2_F_3_p1 20000 :=
    ⟨fun l => by fin_cases l <;> simp [exercise_2_F_3_p1], by norm_num⟩
  have hp2 : StrictlyPositive exercise_2_F_3_p2 := fun l => by
    fin_cases l <;> simp [exercise_2_F_3_p2]
  have hcw : compensatedWealth x exercise_2_F_3_p1 20000 exercise_2_F_3_p2 = 18000 := by
    simp [compensatedWealth, h1, exercise_2_F_3_p2, exercise_2_F_3_x1, dotProduct,
      Fin.sum_univ_two]
    norm_num
  obtain ⟨hc, _⟩ := proposition_2_F_1_i hW hWA _ _ _ hd1 hp2 (by rw [hcw]; norm_num)
  rw [hcw, h1] at hc
  have hw := hW exercise_2_F_3_p2 18000 ⟨hp2, by norm_num⟩
  simp [exercise_2_F_3_p1, exercise_2_F_3_p2, exercise_2_F_3_x1, dotProduct,
    Fin.sum_univ_two] at hc hw ⊢
  constructor <;> nlinarith

/-- **Exercise 2.F.3(e)** (MWG, p. 37). Suppose the data come from a demand function
satisfying the weak axiom and Walras' law. If `y < 75`, good 1 is inferior at some price:
its demand at prices `p²` falls as wealth rises from `w² = 12000 + 80y` to 18000. If demand
is differentiable, there is a wealth level at which `∂x₁/∂w < 0`. -/
theorem exercise_2_F_3e {x : DemandFunction 2} (hW : WalrasLaw x) (hWA : WeakAxiom x)
    {y : ℝ} (hy0 : 0 ≤ y) (hy : y < 75) (h1 : x exercise_2_F_3_p1 20000 = exercise_2_F_3_x1)
    (h2 : x exercise_2_F_3_p2 (exercise_2_F_3_w2 y) = exercise_2_F_3_x2 y) :
    exercise_2_F_3_w2 y < 18000 ∧
      x exercise_2_F_3_p2 18000 0 < x exercise_2_F_3_p2 (exercise_2_F_3_w2 y) 0 ∧
      ((∀ p w, PWDomain p w → DifferentiableAt ℝ (Function.uncurry x) (p, w)) →
        ∃ w ∈ Set.Ioo (exercise_2_F_3_w2 y) 18000, InferiorAt x exercise_2_F_3_p2 w 0) := by
  obtain ⟨_, hb⟩ := exercise_2_F_3_compensated hW hWA h1
  have hlt : exercise_2_F_3_w2 y < 18000 := by simp only [exercise_2_F_3_w2]; linarith
  have hdec : x exercise_2_F_3_p2 18000 0 < x exercise_2_F_3_p2 (exercise_2_F_3_w2 y) 0 := by
    rw [h2]
    simp only [exercise_2_F_3_x2, Matrix.cons_val_zero]
    linarith
  refine ⟨hlt, hdec, fun hdiff => ?_⟩
  have hp2 : StrictlyPositive exercise_2_F_3_p2 := fun l => by
    fin_cases l <;> simp [exercise_2_F_3_p2]
  exact exists_inferiorAt_of_decrease hdiff hp2 (by simp only [exercise_2_F_3_w2]; linarith)
    hlt 0 hdec

/-- **Exercise 2.F.3(f)** (MWG, p. 37). Under the weak axiom and Walras' law, if
`75 < y < 100`, good 2 is inferior at some price: its demand at `p²` falls from at least 100
to `y` as wealth rises from 18000 to `w²`. (For `75 < y ≤ 80` the data already violate the
weak axiom, so the hypotheses cannot hold.) -/
theorem exercise_2_F_3f {x : DemandFunction 2} (hW : WalrasLaw x) (hWA : WeakAxiom x)
    {y : ℝ} (hy0 : 75 < y) (hy : y < 100) (h1 : x exercise_2_F_3_p1 20000 = exercise_2_F_3_x1)
    (h2 : x exercise_2_F_3_p2 (exercise_2_F_3_w2 y) = exercise_2_F_3_x2 y) :
    18000 < exercise_2_F_3_w2 y ∧
      x exercise_2_F_3_p2 (exercise_2_F_3_w2 y) 1 < x exercise_2_F_3_p2 18000 1 ∧
      ((∀ p w, PWDomain p w → DifferentiableAt ℝ (Function.uncurry x) (p, w)) →
        ∃ w ∈ Set.Ioo 18000 (exercise_2_F_3_w2 y), InferiorAt x exercise_2_F_3_p2 w 1) := by
  obtain ⟨ha, _⟩ := exercise_2_F_3_compensated hW hWA h1
  have hlt : 18000 < exercise_2_F_3_w2 y := by simp only [exercise_2_F_3_w2]; linarith
  have hdec : x exercise_2_F_3_p2 (exercise_2_F_3_w2 y) 1 < x exercise_2_F_3_p2 18000 1 := by
    rw [h2]
    simp only [exercise_2_F_3_x2, Matrix.cons_val_one, Matrix.cons_val_zero]
    linarith
  refine ⟨hlt, hdec, fun hdiff => ?_⟩
  have hp2 : StrictlyPositive exercise_2_F_3_p2 := fun l => by
    fin_cases l <;> simp [exercise_2_F_3_p2]
  exact exists_inferiorAt_of_decrease hdiff hp2 (by norm_num) hlt 1 hdec

/-- **Exercise 2.F.3** (MWG, p. 37), limits of homothetic constructions. A demand function that
satisfies the weak axiom and Walras' law, is homogeneous of degree one in wealth (so no good is
ever inferior) and produces both observations must have `y ≥ 120`. Hence for `80 < y < 120`
no homothetic demand can witness that the data do not force inferiority. -/
theorem exercise_2_F_3_homothetic_bound {x : DemandFunction 2} (hW : WalrasLaw x)
    (hWA : WeakAxiom x) (h1w : HomogeneousOneInWealth x) {y : ℝ} (hy : 0 ≤ y)
    (h1 : x exercise_2_F_3_p1 20000 = exercise_2_F_3_x1)
    (h2 : x exercise_2_F_3_p2 (exercise_2_F_3_w2 y) = exercise_2_F_3_x2 y) : 120 ≤ y := by
  obtain ⟨hb, _⟩ := exercise_2_F_3_compensated hW hWA h1
  have hp2 : StrictlyPositive exercise_2_F_3_p2 := fun l => by
    fin_cases l <;> simp [exercise_2_F_3_p2]
  have hw2 : 0 < exercise_2_F_3_w2 y := by simp only [exercise_2_F_3_w2]; linarith
  set a := 18000 / exercise_2_F_3_w2 y
  have ha : 0 < a := div_pos (by norm_num) hw2
  have e := h1w exercise_2_F_3_p2 (exercise_2_F_3_w2 y) a ⟨hp2, hw2⟩ ha
  have ea : a * exercise_2_F_3_w2 y = 18000 := by simp only [a]; field_simp
  rw [ea, h2] at e
  have := congrFun e 1
  simp only [Pi.smul_apply, smul_eq_mul, exercise_2_F_3_x2, Matrix.cons_val_one,
    Matrix.cons_val_zero] at this
  rw [this] at hb
  simp only [a, exercise_2_F_3_w2] at hb
  rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)] at hb
  linarith

/-! ### Exercise 2.F.4 -/

/-- **Exercise 2.F.4** (MWG, p. 37). The Laspeyres quantity index `L_Q = (p⁰·x¹)/(p⁰·x⁰)`. -/
noncomputable def laspeyresQuantity {L : ℕ} (p0 x0 x1 : Fin L → ℝ) : ℝ :=
  (p0 ⬝ᵥ x1) / (p0 ⬝ᵥ x0)

/-- **Exercise 2.F.4** (MWG, p. 37). The Paasche quantity index `P_Q = (p¹·x¹)/(p¹·x⁰)`. -/
noncomputable def paascheQuantity {L : ℕ} (p1 x0 x1 : Fin L → ℝ) : ℝ :=
  (p1 ⬝ᵥ x1) / (p1 ⬝ᵥ x0)

/-- **Exercise 2.F.4** (MWG, p. 37). The expenditure index `E_Q = (p¹·x¹)/(p⁰·x⁰)`. -/
noncomputable def expenditureIndex {L : ℕ} (p0 p1 x0 x1 : Fin L → ℝ) : ℝ :=
  (p1 ⬝ᵥ x1) / (p0 ⬝ᵥ x0)

/-- **Exercise 2.F.4(a)** (MWG, p. 38). If `L_Q < 1` (with `p⁰·x⁰ = w₀ > 0`), the consumer
reveals a preference for `x⁰` over `x¹`. -/
theorem exercise_2_F_4a {L : ℕ} {p0 x0 x1 : Fin L → ℝ} {w0 : ℝ} (hw0 : 0 < w0)
    (hW0 : p0 ⬝ᵥ x0 = w0) (h : laspeyresQuantity p0 x0 x1 < 1) :
    RevealedPreferred p0 w0 x0 x1 := by
  unfold laspeyresQuantity at h
  rw [hW0, div_lt_one hw0] at h
  refine ⟨h.le, fun he => ?_⟩
  rw [he, hW0] at h
  exact lt_irrefl _ h

/-- **Exercise 2.F.4(b)** (MWG, p. 38). If `P_Q > 1` (with `p¹ ≫ 0`, `x⁰ ≥ 0` and
`p¹·x¹ = w₁`), the consumer reveals a preference for `x¹` over `x⁰`. -/
theorem exercise_2_F_4b {L : ℕ} {p1 x0 x1 : Fin L → ℝ} {w1 : ℝ} (hp1 : StrictlyPositive p1)
    (hx0 : x0 ∈ nonnegOrthant L) (hW1 : p1 ⬝ᵥ x1 = w1) (h : 1 < paascheQuantity p1 x0 x1) :
    RevealedPreferred p1 w1 x1 x0 := by
  unfold paascheQuantity at h
  have hnn : 0 ≤ p1 ⬝ᵥ x0 :=
    Finset.sum_nonneg fun l _ => mul_nonneg (hp1 l).le (hx0 l)
  rcases eq_or_lt_of_le hnn with h0 | hpos
  · rw [← h0, div_zero] at h
    exact absurd h (by norm_num)
  rw [one_lt_div hpos, hW1] at h
  refine ⟨h.le, fun he => ?_⟩
  rw [he, hW1] at h
  exact lt_irrefl _ h

/-- **Exercise 2.F.4(c)** (MWG, p. 38). Neither `E_Q > 1` nor `E_Q < 1` implies any revealed
preference: with `x⁰ = (1, 0)`, `x¹ = (0, 1)`, `p⁰ = (1, 2)` (`w₀ = 1`), the period-1 prices
`(4, 2)` give `E_Q = 2` and the prices `(1, 1/2)` give `E_Q = 1/2`, and in both cases neither
bundle is revealed preferred to the other. -/
theorem exercise_2_F_4c :
    expenditureIndex ![1, 2] ![4, 2] ![1, 0] ![0, 1] = 2 ∧
      ¬ RevealedPreferred ![1, 2] 1 ![1, 0] ![0, 1] ∧
      ¬ RevealedPreferred ![4, 2] 2 ![0, 1] ![1, 0] ∧
      expenditureIndex ![1, 2] ![1, 1 / 2] ![1, 0] ![0, 1] = 1 / 2 ∧
      ¬ RevealedPreferred ![1, 1 / 2] (1 / 2) ![0, 1] ![1, 0] := by
  refine ⟨?_, fun h => ?_, fun h => ?_, ?_, fun h => ?_⟩ <;>
    simp [expenditureIndex, RevealedPreferred, dotProduct, Fin.sum_univ_two] at * <;>
    norm_num at *

end MWG.ConsumerChoice
