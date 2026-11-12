import ConsumerDemand.BudgetSets
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Data.Set.Card
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import ChoicePreferenceUtility.Basic
import MWGPreferenceChoice.ChoiceRules
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Topology.Order.Monotone
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.LinearAlgebra.Matrix.RowCol
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.Basic.Complex.BigOperators
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Data.Finset.Sort
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.Finite
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.Data.Finset.Sum
set_option autoImplicit false

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Commodities and consumption sets

MWG, Sections 2.B and 2.C, pp. 17–20. A commodity vector is a point of `ℝ^L`, encoded as
`Fin L → ℝ`. The standard consumption set is the nonnegative orthant `ℝ^L_+`; it is convex
(p. 19). The six consumption sets drawn in Figures 2.C.1–2.C.6 are defined for `L = 2`
(good `0` is the horizontal axis, good `1` the vertical axis), and the text's claims on
p. 20 are proved: the sets of Figures 2.C.1, 2.C.4, 2.C.5 and 2.C.6 are convex, and those of
Figures 2.C.2 and 2.C.3 are not.

The orthant is bridged to Kreps' `NonnegativeOrthant` subtype (Kreps I, Chapter 3).
-/

namespace MWG.ConsumerChoice

/-- **Section 2.C** (MWG, p. 19). The consumption set `ℝ^L_+ = {x ∈ ℝ^L : x_ℓ ≥ 0}`. -/
def nonnegOrthant (L : ℕ) : Set (Fin L → ℝ) := {x | ∀ l, 0 ≤ x l}

/-- Membership in `ℝ^L_+` is the pointwise order `0 ≤ x`. -/
theorem mem_nonnegOrthant_iff {L : ℕ} (x : Fin L → ℝ) : x ∈ nonnegOrthant L ↔ 0 ≤ x :=
  Iff.rfl

/-- Bridge: MWG's `ℝ^L_+` is exactly the carrier of Kreps' `NonnegativeOrthant L`. -/
theorem range_val_nonnegativeOrthant (L : ℕ) :
    Set.range (Subtype.val : Kreps.ConsumerDemand.NonnegativeOrthant L → Fin L → ℝ) =
      nonnegOrthant L := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact y.property
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

/-- **Footnote 2** (MWG, p. 19). The `ℓ`th entry of `αx + (1-α)x'` is `αx_ℓ + (1-α)x'_ℓ`. -/
theorem convexCombination_apply {L : ℕ} (x x' : Fin L → ℝ) (a : ℝ) (l : Fin L) :
    (a • x + (1 - a) • x') l = a * x l + (1 - a) * x' l := by
  simp [smul_eq_mul]

/-- **Section 2.C** (MWG, p. 19). The consumption set `ℝ^L_+` is convex. -/
theorem convex_nonnegOrthant (L : ℕ) : Convex ℝ (nonnegOrthant L) := by
  intro x hx y hy a b ha hb _ l
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  exact add_nonneg (mul_nonneg ha (hx l)) (mul_nonneg hb (hy l))

/-- **Figure 2.C.1** (MWG, p. 19). Bread (good `0`) and leisure (good `1`): both nonnegative
and at most 24 hours of leisure. -/
def figure_2_C_1_set : Set (Fin 2 → ℝ) := {x | 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 1 ≤ 24}

/-- **Figure 2.C.2** (MWG, p. 19). Good `0` divisible, good `1` in nonnegative integer
amounts. -/
def figure_2_C_2_set : Set (Fin 2 → ℝ) := {x | 0 ≤ x 0 ∧ ∃ n : ℕ, x 1 = n}

/-- **Figure 2.C.3** (MWG, p. 19). Bread in Washington or bread in New York at noon, but not
both: one of the two coordinates is zero. -/
def figure_2_C_3_set : Set (Fin 2 → ℝ) := {x | 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ (x 0 = 0 ∨ x 1 = 0)}

/-- **Figure 2.C.4** (MWG, p. 19). Survival needs: at least four slices of bread in total. -/
def figure_2_C_4_set : Set (Fin 2 → ℝ) := {x | 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ 4 ≤ x 0 + x 1}

/-- **Figure 2.C.5** (MWG, p. 20). At most 16 hours of work, so leisure lies in `[8, 24]`. -/
def figure_2_C_5_set : Set (Fin 2 → ℝ) := {x | 0 ≤ x 0 ∧ 8 ≤ x 1 ∧ x 1 ≤ 24}

/-- **Figure 2.C.6** (MWG, p. 20). The consumption set `ℝ²_+`. -/
def figure_2_C_6_set : Set (Fin 2 → ℝ) := nonnegOrthant 2

/-- **Section 2.C** (MWG, p. 20). The consumption set of Figure 2.C.1 is convex. -/
theorem convex_figure_2_C_1 : Convex ℝ figure_2_C_1_set := by
  intro x hx y hy a b ha hb hab
  simp only [figure_2_C_1_set, Set.mem_ofPred_eq, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul] at hx hy ⊢
  refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

/-- **Section 2.C** (MWG, p. 20). The consumption set of Figure 2.C.4 is convex. -/
theorem convex_figure_2_C_4 : Convex ℝ figure_2_C_4_set := by
  intro x hx y hy a b ha hb hab
  simp only [figure_2_C_4_set, Set.mem_ofPred_eq, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul] at hx hy ⊢
  refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

/-- **Section 2.C** (MWG, p. 20). The consumption set of Figure 2.C.5 is convex. -/
theorem convex_figure_2_C_5 : Convex ℝ figure_2_C_5_set := by
  intro x hx y hy a b ha hb hab
  simp only [figure_2_C_5_set, Set.mem_ofPred_eq, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul] at hx hy ⊢
  refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

/-- **Section 2.C** (MWG, p. 20). The consumption set of Figure 2.C.6 is convex. -/
theorem convex_figure_2_C_6 : Convex ℝ figure_2_C_6_set := convex_nonnegOrthant 2

/-- **Section 2.C** (MWG, p. 20). The consumption set of Figure 2.C.2 is not convex: the
midpoint of `(0,0)` and `(0,1)` has half a unit of the indivisible good. -/
theorem not_convex_figure_2_C_2 : ¬ Convex ℝ figure_2_C_2_set := by
  intro h
  have h0 : (![0, 0] : Fin 2 → ℝ) ∈ figure_2_C_2_set := ⟨le_rfl, 0, by simp⟩
  have h1 : (![0, 1] : Fin 2 → ℝ) ∈ figure_2_C_2_set := ⟨le_rfl, 1, by simp⟩
  have hm := h h0 h1 (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)
  obtain ⟨_, n, hn⟩ := hm
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_one,
    Matrix.cons_val_zero] at hn
  norm_num at hn
  rcases Nat.lt_or_ge n 1 with h' | h'
  · have : n = 0 := by omega
    subst this
    norm_num at hn
  · have : (1 : ℝ) ≤ n := by exact_mod_cast h'
    linarith

/-- **Section 2.C** (MWG, p. 20). The consumption set of Figure 2.C.3 is not convex: the
midpoint of `(1,0)` and `(0,1)` consumes both goods. -/
theorem not_convex_figure_2_C_3 : ¬ Convex ℝ figure_2_C_3_set := by
  intro h
  have h0 : (![1, 0] : Fin 2 → ℝ) ∈ figure_2_C_3_set := by
    refine ⟨by simp, by simp, Or.inr (by simp)⟩
  have h1 : (![0, 1] : Fin 2 → ℝ) ∈ figure_2_C_3_set := by
    refine ⟨by simp, by simp, Or.inl (by simp)⟩
  have hm := h h0 h1 (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)
  obtain ⟨_, _, hm⟩ := hm
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_one,
    Matrix.cons_val_zero] at hm
  norm_num at hm

end MWG.ConsumerChoice

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Competitive budgets

MWG, Section 2.D, pp. 20–23, and Exercises 2.D.1–2.D.4 (p. 36). The Walrasian budget set
`B_{p,w} = {x ∈ ℝ^L_+ : p·x ≤ w}` (Definition 2.D.1), the budget hyperplane and its
orthogonality to `p` (Figure 2.D.3), the effect of a price fall (Figure 2.D.2), the
degenerate zero-wealth budget, and convexity of `B_{p,w}`. The budget set over a general
consumption set `X` is convex when `X` is (Exercise 2.D.3(b)) and need not be otherwise
(Exercise 2.D.3(a)); the overtime-and-tax budget set of Figure 2.D.4 is not convex
(Exercise 2.D.4). The lifetime budget of Exercise 2.D.1 and the consumption–leisure budget
of Exercise 2.D.2 are shown to be Walrasian budget sets.

Prices are strictly positive (`p ≫ 0`, p. 20) whenever a result needs it. The set is bridged
to Kreps' `BudgetSet` at positive prices.
-/

namespace MWG.ConsumerChoice

/-- **Section 2.D** (MWG, p. 20). A price vector is strictly positive, `p ≫ 0`. -/
def StrictlyPositive {L : ℕ} (p : Fin L → ℝ) : Prop := ∀ l, 0 < p l

/-- **Definition 2.D.1** (MWG, p. 21). The Walrasian (competitive) budget set
`B_{p,w} = {x ∈ ℝ^L_+ : p·x ≤ w}`. -/
def budgetSet {L : ℕ} (p : Fin L → ℝ) (w : ℝ) : Set (Fin L → ℝ) :=
  {x | x ∈ nonnegOrthant L ∧ p ⬝ᵥ x ≤ w}

/-- **Definition 2.D.1** (MWG, p. 21), unfolded. -/
theorem definition_2_D_1 {L : ℕ} (p : Fin L → ℝ) (w : ℝ) (x : Fin L → ℝ) :
    x ∈ budgetSet p w ↔ (∀ l, 0 ≤ x l) ∧ ∑ l, p l * x l ≤ w := Iff.rfl

/-- **Section 2.D** (MWG, p. 21). The budget hyperplane `{x ∈ ℝ^L : p·x = w}`. -/
def budgetHyperplane {L : ℕ} (p : Fin L → ℝ) (w : ℝ) : Set (Fin L → ℝ) := {x | p ⬝ᵥ x = w}

/-- Bridge to Kreps I, Chapter 3: at strictly positive prices and nonnegative income, the
carrier of Kreps' `BudgetSet` is MWG's Walrasian budget set. -/
theorem image_val_krepsBudgetSet {L : ℕ} (p : Kreps.ConsumerDemand.PositivePrices L)
    (y : NNReal) :
    Subtype.val '' Kreps.ConsumerDemand.BudgetSet p y = budgetSet p.val (y : ℝ) := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z.property, hz⟩
  · rintro ⟨hx, hb⟩
    exact ⟨⟨x, hx⟩, hb, rfl⟩

/-- **Section 2.D** (MWG, p. 21). With `w = 0` and `p ≫ 0` the consumer can afford only
`x = 0`. -/
theorem budgetSet_zero_wealth {L : ℕ} {p : Fin L → ℝ} (hp : StrictlyPositive p) :
    budgetSet p 0 = {0} := by
  ext x
  constructor
  · rintro ⟨hx, hb⟩
    have hsum : ∀ l ∈ Finset.univ, 0 ≤ p l * x l := fun l _ => mul_nonneg (hp l).le (hx l)
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hsum).mp
      (le_antisymm hb (Finset.sum_nonneg hsum))
    funext l
    have := hz l (Finset.mem_univ l)
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (hp l).ne'
    · simpa using h
  · intro hx
    rw [Set.mem_singleton_iff.mp hx]
    exact ⟨fun _ => le_rfl, by simp⟩

/-- **Figure 2.D.3** (MWG, p. 22). The price vector is orthogonal to every displacement
`Δx = x' - x̄` within the budget hyperplane: `p·Δx = 0`. -/
theorem budgetHyperplane_orthogonal {L : ℕ} {p : Fin L → ℝ} {w : ℝ} {x x' : Fin L → ℝ}
    (hx : x ∈ budgetHyperplane p w) (hx' : x' ∈ budgetHyperplane p w) :
    p ⬝ᵥ (x' - x) = 0 := by
  have h1 : p ⬝ᵥ x = w := hx
  have h2 : p ⬝ᵥ x' = w := hx'
  rw [dotProduct_sub, h1, h2, sub_self]

/-- **Figure 2.D.1** (MWG, p. 21). For `L = 2` the budget line is
`x₂ = w/p₂ - (p₁/p₂) x₁`, with slope `-(p₁/p₂)`. -/
theorem budgetLine_two_goods {p : Fin 2 → ℝ} (hp : StrictlyPositive p) (w : ℝ)
    (x : Fin 2 → ℝ) :
    x ∈ budgetHyperplane p w ↔ x 1 = w / p 1 - (p 0 / p 1) * x 0 := by
  have h1 := (hp 1).ne'
  change p ⬝ᵥ x = w ↔ _
  simp only [dotProduct, Fin.sum_univ_two]
  constructor
  · intro h
    field_simp
    linarith
  · intro h
    rw [h]
    field_simp
    ring

/-- **Figure 2.D.2** (MWG, p. 21). A fall in the price of good 2 (with `p₁` and `w` fixed)
enlarges the budget set. -/
theorem budgetSet_subset_of_price_fall {p : Fin 2 → ℝ} {w q : ℝ} (hq : q ≤ p 1) :
    budgetSet p w ⊆ budgetSet ![p 0, q] w := by
  rintro x ⟨hx, hb⟩
  refine ⟨hx, ?_⟩
  simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hb ⊢
  nlinarith [hx 1]

/-- **Figure 2.D.2** (MWG, p. 21). With `w > 0` and a strict fall `p̄₂ < p₂`, the budget set
grows strictly: the new vertex `(0, w/p̄₂)` was not affordable before. -/
theorem budgetSet_ssubset_of_price_fall {p : Fin 2 → ℝ} {w q : ℝ} (hw : 0 < w) (hq0 : 0 < q)
    (hq : q < p 1) : budgetSet p w ⊂ budgetSet ![p 0, q] w := by
  refine ⟨budgetSet_subset_of_price_fall hq.le, fun hsub => ?_⟩
  have hmem : (![0, w / q] : Fin 2 → ℝ) ∈ budgetSet ![p 0, q] w := by
    refine ⟨fun l => ?_, ?_⟩
    · fin_cases l
      · simp
      · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
        positivity
    · simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      field_simp
      simp
  obtain ⟨_, hb⟩ := hsub hmem
  simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    mul_zero, zero_add] at hb
  have : q * w < p 1 * w := mul_lt_mul_of_pos_right hq hw
  rw [mul_div_assoc', div_le_iff₀ hq0] at hb
  linarith

/-- **Figure 2.D.2** (MWG, p. 21). The new budget line is steeper: `p₁/p₂ < p₁/p̄₂`. -/
theorem budgetLine_steeper {p : Fin 2 → ℝ} (hp : StrictlyPositive p) {q : ℝ} (hq0 : 0 < q)
    (hq : q < p 1) : p 0 / p 1 < p 0 / q :=
  div_lt_div_of_pos_left (hp 0) hq0 hq

/-- **Section 2.D** (MWG, p. 22). The Walrasian budget set is convex (for every `p`, `w`). -/
theorem convex_budgetSet {L : ℕ} (p : Fin L → ℝ) (w : ℝ) : Convex ℝ (budgetSet p w) := by
  intro x hx y hy a b ha hb hab
  refine ⟨convex_nonnegOrthant L hx.1 hy.1 ha hb hab, ?_⟩
  rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  have h1 := mul_le_mul_of_nonneg_left hx.2 ha
  have h2 := mul_le_mul_of_nonneg_left hy.2 hb
  calc a * (p ⬝ᵥ x) + b * (p ⬝ᵥ y) ≤ a * w + b * w := add_le_add h1 h2
    _ = w := by rw [← add_mul, hab, one_mul]

/-- **Exercise 2.D.3** (MWG, p. 36). The budget set over a general consumption set `X`,
`B_{p,w} = {x ∈ X : p·x ≤ w}`. -/
def budgetSetOn {L : ℕ} (X : Set (Fin L → ℝ)) (p : Fin L → ℝ) (w : ℝ) : Set (Fin L → ℝ) :=
  {x | x ∈ X ∧ p ⬝ᵥ x ≤ w}

/-- With `X = ℝ^L_+`, the general budget set is the Walrasian budget set. -/
theorem budgetSetOn_nonnegOrthant {L : ℕ} (p : Fin L → ℝ) (w : ℝ) :
    budgetSetOn (nonnegOrthant L) p w = budgetSet p w := rfl

/-- **Exercise 2.D.3(b)** (MWG, p. 36). If the consumption set `X` is convex, so is
`B_{p,w}`. -/
theorem exercise_2_D_3b {L : ℕ} {X : Set (Fin L → ℝ)} (hX : Convex ℝ X) (p : Fin L → ℝ)
    (w : ℝ) : Convex ℝ (budgetSetOn X p w) := by
  intro x hx y hy a b ha hb hab
  refine ⟨hX hx.1 hy.1 ha hb hab, ?_⟩
  rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  have h1 := mul_le_mul_of_nonneg_left hx.2 ha
  have h2 := mul_le_mul_of_nonneg_left hy.2 hb
  calc a * (p ⬝ᵥ x) + b * (p ⬝ᵥ y) ≤ a * w + b * w := add_le_add h1 h2
    _ = w := by rw [← add_mul, hab, one_mul]

/-- **Exercise 2.D.3(a)** (MWG, p. 36). With the consumption set of Figure 2.C.3 and
`(p, w) ≫ 0`, the budget set is not convex. -/
theorem exercise_2_D_3a {p : Fin 2 → ℝ} (hp : StrictlyPositive p) {w : ℝ} (hw : 0 < w) :
    ¬ Convex ℝ (budgetSetOn figure_2_C_3_set p w) := by
  intro h
  have h0 := (hp 0).ne'
  have h1 := (hp 1).ne'
  have hA : (![w / p 0, 0] : Fin 2 → ℝ) ∈ budgetSetOn figure_2_C_3_set p w := by
    refine ⟨⟨by simp only [Matrix.cons_val_zero]; exact div_nonneg hw.le (hp 0).le,
      by simp, Or.inr (by simp)⟩, ?_⟩
    simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp
    simp
  have hB : (![0, w / p 1] : Fin 2 → ℝ) ∈ budgetSetOn figure_2_C_3_set p w := by
    refine ⟨⟨by simp, by simp only [Matrix.cons_val_one]; exact div_nonneg hw.le (hp 1).le,
      Or.inl (by simp)⟩, ?_⟩
    simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp
    simp
  obtain ⟨⟨_, _, hm⟩, _⟩ := h hA hB (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_one,
    Matrix.cons_val_zero] at hm
  rcases hm with hm | hm
  · have : 0 < w / p 0 := div_pos hw (hp 0)
    linarith
  · have : 0 < w / p 1 := div_pos hw (hp 1)
    linarith

/-- **Figure 2.D.4** (MWG, p. 22). Pre-tax labour income with `ℓ` hours of leisure: wage `s`
for the first 8 hours of work and overtime wage `s'` beyond. -/
noncomputable def figure_2_D_4_income (s s' leisure : ℝ) : ℝ :=
  if 16 ≤ leisure then s * (24 - leisure) else 8 * s + s' * (16 - leisure)

/-- **Figure 2.D.4** (MWG, p. 22). Affordable consumption (price 1): labour income above
`M` is taxed at rate `t`. -/
noncomputable def figure_2_D_4_consumption (s s' t M leisure : ℝ) : ℝ :=
  min (figure_2_D_4_income s s' leisure)
    (M + (1 - t) * (figure_2_D_4_income s s' leisure - M))

/-- **Figure 2.D.4** (MWG, p. 22). The budget set in (consumption, leisure) space:
coordinate `0` is consumption, coordinate `1` is leisure hours. -/
def figure_2_D_4_set (s s' t M : ℝ) : Set (Fin 2 → ℝ) :=
  {x | 0 ≤ x 0 ∧ x 0 ≤ figure_2_D_4_consumption s s' t M (x 1) ∧ 0 ≤ x 1 ∧ x 1 ≤ 24}

/-- **Exercise 2.D.4** (MWG, p. 36). The budget set of Figure 2.D.4 (wages `0 < s < s'`, a
tax rate `t ≥ 0` on labour income above `M > 8s`) is not convex: the overtime kink at
16 hours of leisure is convex toward the origin. -/
theorem exercise_2_D_4 {s s' t M : ℝ} (hs : 0 < s) (hss : s < s') (ht0 : 0 ≤ t)
    (hM : 8 * s < M) : ¬ Convex ℝ (figure_2_D_4_set s s' t M) := by
  intro h
  have hs' : 0 < s' := hs.trans hss
  set e : ℝ := min 1 ((M - 8 * s) / s') with he
  have he0 : 0 < e := lt_min one_pos (div_pos (by linarith) hs')
  have he1 : e ≤ 1 := min_le_left _ _
  have heM : s' * e ≤ M - 8 * s := by
    have : e ≤ (M - 8 * s) / s' := min_le_right _ _
    rw [le_div_iff₀ hs'] at this
    linarith
  -- the corner with no work
  have hA : (![0, 24] : Fin 2 → ℝ) ∈ figure_2_D_4_set s s' t M := by
    refine ⟨by simp, ?_, by simp, by simp⟩
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, figure_2_D_4_consumption,
      figure_2_D_4_income]
    norm_num
    nlinarith
  -- a point with a little overtime and untaxed income
  have hyB : figure_2_D_4_income s s' (16 - e) = 8 * s + s' * e := by
    simp only [figure_2_D_4_income]
    split_ifs with hc
    · linarith
    · ring
  have hcB : figure_2_D_4_consumption s s' t M (16 - e) = 8 * s + s' * e := by
    simp only [figure_2_D_4_consumption, hyB]
    apply min_eq_left
    nlinarith
  have hB : (![8 * s + s' * e, 16 - e] : Fin 2 → ℝ) ∈ figure_2_D_4_set s s' t M := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hcB] <;> nlinarith
  obtain ⟨_, hm, _, _⟩ := h hA hB (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_one,
    Matrix.cons_val_zero] at hm
  have hle : figure_2_D_4_consumption s s' t M (1 / 2 * 24 + 1 / 2 * (16 - e)) ≤
      s * (24 - (1 / 2 * 24 + 1 / 2 * (16 - e))) := by
    simp only [figure_2_D_4_consumption, figure_2_D_4_income]
    split_ifs with hc
    · exact min_le_left _ _
    · exfalso
      apply hc
      linarith
  nlinarith

/-- **Exercise 2.D.1** (MWG, p. 36). A consumer living two periods, with wealth `w` at
birth, who can save or borrow `σ` at interest rate `r > -1`: the lifetime budget set is the
Walrasian budget set at present-value prices `(p₁, p₂/(1+r))`. -/
theorem exercise_2_D_1 {p : Fin 2 → ℝ} {r w : ℝ} (hr : -1 < r) :
    {x : Fin 2 → ℝ | x ∈ nonnegOrthant 2 ∧ ∃ σ : ℝ, p 0 * x 0 + σ = w ∧
      p 1 * x 1 ≤ (1 + r) * σ} = budgetSet ![p 0, p 1 / (1 + r)] w := by
  have hr' : 0 < 1 + r := by linarith
  ext x
  simp only [budgetSet, Set.mem_ofPred_eq, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  constructor
  · rintro ⟨hx, σ, h1, h2⟩
    refine ⟨hx, ?_⟩
    have : p 1 * x 1 / (1 + r) ≤ σ := by rw [div_le_iff₀ hr']; linarith
    have h3 : p 1 / (1 + r) * x 1 = p 1 * x 1 / (1 + r) := by ring
    linarith
  · rintro ⟨hx, hb⟩
    refine ⟨hx, w - p 0 * x 0, by ring, ?_⟩
    have h3 : p 1 / (1 + r) * x 1 = p 1 * x 1 / (1 + r) := by ring
    rw [h3] at hb
    have : p 1 * x 1 / (1 + r) ≤ w - p 0 * x 0 := by linarith
    rw [div_le_iff₀ hr'] at this
    linarith

/-- **Exercise 2.D.2** (MWG, p. 36). Consumption good `x` at price `p` and leisure `h`, with
wage `s = 1`, 24 hours and no other wealth: `p·x ≤ 1·(24 - h)`, `0 ≤ h ≤ 24`. This is the
Walrasian budget set at prices `(p, 1)` and wealth 24 (the bound `h ≤ 24` is implied). -/
theorem exercise_2_D_2 {p : ℝ} (hp : 0 < p) :
    {x : Fin 2 → ℝ | x ∈ nonnegOrthant 2 ∧ x 1 ≤ 24 ∧ p * x 0 ≤ 1 * (24 - x 1)} =
      budgetSet ![p, 1] 24 := by
  ext x
  simp only [budgetSet, Set.mem_ofPred_eq, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  constructor
  · rintro ⟨hx, _, hb⟩
    exact ⟨hx, by linarith⟩
  · rintro ⟨hx, hb⟩
    have := mul_nonneg hp.le (hx 0)
    exact ⟨hx, by linarith, by linarith⟩

end MWG.ConsumerChoice

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Walrasian demand: homogeneity, Walras' law and comparative-statics notation

MWG, Section 2.E, pp. 23–26, and Exercises 2.E.1 (p. 23) and 2.E.7 (p. 37).

* Walrasian demand correspondences and functions on the domain `p ≫ 0`, `w > 0`;
  homogeneity of degree zero (Definition 2.E.1) and Walras' law (Definition 2.E.2), with the
  single-valued case bridged to the singleton correspondence.
* `B_{αp,αw} = B_{p,w}` (p. 23); Walrasian budget sets determine `(p, w)` up to scale, so a
  homogeneous demand depends only on the budget set (the choice-structure remark, p. 24); no
  finite set (in particular no two- or three-element set) is a Walrasian budget set.
* Normalisations `p_ℓ = 1` and `w = 1` (p. 24).
* Notation for derivatives: a derivative `D` of `(p, w) ↦ x(p, w)` at `(p, w)` is a
  continuous linear map; `∂x_ℓ/∂p_k` and `∂x_ℓ/∂w` are its values at coordinate directions,
  `D_p x` and `D_w x` collect them (pp. 25–26), and `D(v, c) = D_p x · v + c D_w x`.
* Engel functions, wealth expansion paths, normal, inferior and Giffen goods (pp. 24–26).
* Exercise 2.E.1: the given demand is homogeneous of degree zero for every `β`, and satisfies
  Walras' law if and only if `β = 1`. Exercise 2.E.7.
-/

namespace MWG.ConsumerChoice

/-- **Section 2.D–2.E** (MWG, pp. 21, 23). The price–wealth domain `p ≫ 0`, `w > 0`. -/
def PWDomain {L : ℕ} (p : Fin L → ℝ) (w : ℝ) : Prop := StrictlyPositive p ∧ 0 < w

/-- **Section 2.E** (MWG, p. 23). A Walrasian demand correspondence `x(p, w)`. -/
abbrev DemandCorrespondence (L : ℕ) := (Fin L → ℝ) → ℝ → Set (Fin L → ℝ)

/-- **Section 2.E** (MWG, p. 23). A single-valued Walrasian demand function `x(p, w)`. -/
abbrev DemandFunction (L : ℕ) := (Fin L → ℝ) → ℝ → Fin L → ℝ

/-- **Definition 2.E.1** (MWG, p. 23). The demand correspondence is homogeneous of degree zero:
`x(αp, αw) = x(p, w)` for all `p ≫ 0`, `w > 0`, `α > 0`. -/
def HomogeneousZeroCorr {L : ℕ} (x : DemandCorrespondence L) : Prop :=
  ∀ p w α, PWDomain p w → 0 < α → x (α • p) (α * w) = x p w

/-- **Definition 2.E.2** (MWG, p. 23). Walras' law: `p·x = w` for every `x ∈ x(p, w)`,
`p ≫ 0`, `w > 0`. -/
def WalrasLawCorr {L : ℕ} (x : DemandCorrespondence L) : Prop :=
  ∀ p w, PWDomain p w → ∀ y ∈ x p w, p ⬝ᵥ y = w

/-- **Definition 2.E.1** (MWG, p. 23) for a demand function. -/
def HomogeneousZero {L : ℕ} (x : DemandFunction L) : Prop :=
  ∀ p w α, PWDomain p w → 0 < α → x (α • p) (α * w) = x p w

/-- **Definition 2.E.2** (MWG, p. 23) for a demand function. -/
def WalrasLaw {L : ℕ} (x : DemandFunction L) : Prop := ∀ p w, PWDomain p w → p ⬝ᵥ x p w = w

/-- The singleton correspondence of a demand function. -/
def toCorrespondence {L : ℕ} (x : DemandFunction L) : DemandCorrespondence L :=
  fun p w => {x p w}

/-- Homogeneity of a demand function is homogeneity of its singleton correspondence. -/
theorem homogeneousZero_iff_corr {L : ℕ} (x : DemandFunction L) :
    HomogeneousZero x ↔ HomogeneousZeroCorr (toCorrespondence x) := by
  constructor
  · intro h p w α hd ha
    simp only [toCorrespondence, h p w α hd ha]
  · intro h p w α hd ha
    have := h p w α hd ha
    simpa [toCorrespondence] using this

/-- Walras' law for a demand function is Walras' law for its singleton correspondence. -/
theorem walrasLaw_iff_corr {L : ℕ} (x : DemandFunction L) :
    WalrasLaw x ↔ WalrasLawCorr (toCorrespondence x) := by
  constructor
  · intro h p w hd y hy
    rw [Set.mem_singleton_iff.mp hy]
    exact h p w hd
  · intro h p w hd
    exact h p w hd _ rfl

/-- Scaling preserves the domain. -/
theorem pwDomain_smul {L : ℕ} {p : Fin L → ℝ} {w α : ℝ} (hd : PWDomain p w) (ha : 0 < α) :
    PWDomain (α • p) (α * w) :=
  ⟨fun l => by simpa using mul_pos ha (hd.1 l), mul_pos ha hd.2⟩

/-- **Section 2.E** (MWG, p. 23). A proportional change in prices and wealth leaves the budget
set unchanged: `B_{αp,αw} = B_{p,w}` for `α > 0`. -/
theorem budgetSet_smul {L : ℕ} (p : Fin L → ℝ) (w : ℝ) {α : ℝ} (ha : 0 < α) :
    budgetSet (α • p) (α * w) = budgetSet p w := by
  ext y
  simp only [budgetSet, Set.mem_ofPred_eq, smul_dotProduct, smul_eq_mul]
  constructor
  · rintro ⟨hy, hb⟩
    exact ⟨hy, le_of_mul_le_mul_left hb ha⟩
  · rintro ⟨hy, hb⟩
    exact ⟨hy, mul_le_mul_of_nonneg_left hb ha.le⟩

/-- The vertex `(w/p_ℓ) e_ℓ` is a budget point. -/
theorem vertex_mem_budgetSet {L : ℕ} {p : Fin L → ℝ} {w : ℝ} (hd : PWDomain p w) (l : Fin L) :
    Pi.single l (w / p l) ∈ budgetSet p w := by
  refine ⟨fun k => ?_, ?_⟩
  · by_cases hk : k = l
    · subst hk
      simpa using div_nonneg hd.2.le (hd.1 k).le
    · simp [hk]
  · rw [dotProduct_single, mul_div_cancel₀ _ (hd.1 l).ne']

/-- Walrasian budget sets determine price–wealth pairs up to scale: `B_{p,w} = B_{p',w'}`
forces `(p', w') = (w'/w)(p, w)`. -/
theorem budgetSet_eq_imp_proportional {L : ℕ} {p p' : Fin L → ℝ} {w w' : ℝ}
    (hd : PWDomain p w) (hd' : PWDomain p' w') (h : budgetSet p w = budgetSet p' w') :
    p' = (w' / w) • p := by
  funext l
  have h1 : Pi.single l (w / p l) ∈ budgetSet p' w' := h ▸ vertex_mem_budgetSet hd l
  have h2 : Pi.single l (w' / p' l) ∈ budgetSet p w := h ▸ vertex_mem_budgetSet hd' l
  have b1 := h1.2
  have b2 := h2.2
  rw [dotProduct_single] at b1 b2
  have hp := hd.1 l
  have hp' := hd'.1 l
  have hw := hd.2
  have hw' := hd'.2
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [mul_div_assoc', div_le_iff₀ hp] at b1
  rw [mul_div_assoc', div_le_iff₀ hp'] at b2
  field_simp
  linarith

/-- **Section 2.E** (MWG, p. 24). Under homogeneity of degree zero, demand depends only on the
budget set: `B_{p,w} = B_{p',w'}` implies `x(p, w) = x(p', w')`. Hence `(𝓑^W, x(·))` is a
choice structure. -/
theorem demand_depends_only_on_budget {L : ℕ} {x : DemandFunction L} (hx : HomogeneousZero x)
    {p p' : Fin L → ℝ} {w w' : ℝ} (hd : PWDomain p w) (hd' : PWDomain p' w')
    (h : budgetSet p w = budgetSet p' w') : x p w = x p' w' := by
  have hp := budgetSet_eq_imp_proportional hd hd' h
  have ha : 0 < w' / w := div_pos hd'.2 hd.2
  have hw : w' = (w' / w) * w := by field_simp [hd.2.ne']
  calc x p w = x ((w' / w) • p) ((w' / w) * w) := (hx p w _ hd ha).symm
    _ = x p' w' := by rw [← hp, ← hw]

/-- **Section 2.E** (MWG, p. 24). The family of Walrasian budget sets
`𝓑^W = {B_{p,w} : p ≫ 0, w > 0}`. -/
def walrasianBudgetFamily (L : ℕ) : Set (Set (Fin L → ℝ)) :=
  {B | ∃ p w, PWDomain p w ∧ B = budgetSet p w}

/-- With at least one good, every Walrasian budget set is infinite. -/
theorem budgetSet_infinite {L : ℕ} {p : Fin L → ℝ} {w : ℝ} (hd : PWDomain p w) (l : Fin L) :
    (budgetSet p w).Infinite := by
  have hpos : 0 < w / p l := div_pos hd.2 (hd.1 l)
  let f : ℕ → Fin L → ℝ := fun n => Pi.single l ((1 / ((n : ℝ) + 1)) * (w / p l))
  have hinj : Function.Injective f := by
    intro a b hab
    have := congrFun hab l
    simp only [f, Pi.single_eq_same] at this
    have h2 := mul_right_cancel₀ hpos.ne' this
    have ha : (0 : ℝ) < (a : ℝ) + 1 := by positivity
    have hb : (0 : ℝ) < (b : ℝ) + 1 := by positivity
    field_simp at h2
    exact_mod_cast (by linarith : (a : ℝ) = b)
  have hmem : ∀ n, f n ∈ budgetSet p w := by
    intro n
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have ht0 : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity
    have ht1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one hn]
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    refine ⟨fun k => ?_, ?_⟩
    · by_cases hk : k = l
      · subst hk
        simpa [f] using mul_nonneg ht0 hpos.le
      · simp [f, hk]
    · simp only [f]
      rw [dotProduct_single]
      have : p l * (1 / ((n : ℝ) + 1) * (w / p l)) = 1 / ((n : ℝ) + 1) * w := by
        field_simp [(hd.1 l).ne']
      rw [this]
      nlinarith [hd.2]
  exact Set.infinite_of_injective_forall_mem hinj hmem

/-- **Section 2.E** (MWG, p. 24). With at least one good, `𝓑^W` contains no finite set; in
particular no two- or three-element subset of `X` is a Walrasian budget set. -/
theorem finite_not_mem_walrasianBudgetFamily {L : ℕ} (l : Fin L) {B : Set (Fin L → ℝ)}
    (hB : B.Finite) : B ∉ walrasianBudgetFamily L := by
  rintro ⟨p, w, hd, rfl⟩
  exact budgetSet_infinite hd l hB

/-- **Section 2.E** (MWG, p. 24). Normalisation `p_ℓ = 1`: under homogeneity of degree zero,
`x(p, w) = x(p/p_ℓ, w/p_ℓ)`. -/
theorem normalize_price {L : ℕ} {x : DemandFunction L} (hx : HomogeneousZero x)
    {p : Fin L → ℝ} {w : ℝ} (hd : PWDomain p w) (l : Fin L) :
    x ((p l)⁻¹ • p) (w / p l) = x p w ∧ ((p l)⁻¹ • p) l = 1 := by
  have hp := hd.1 l
  refine ⟨?_, by simp [hp.ne']⟩
  rw [div_eq_inv_mul]
  exact hx p w _ hd (inv_pos.mpr hp)

/-- **Section 2.E** (MWG, p. 24). Normalisation `w = 1`: `x(p, w) = x(p/w, 1)`. -/
theorem normalize_wealth {L : ℕ} {x : DemandFunction L} (hx : HomogeneousZero x)
    {p : Fin L → ℝ} {w : ℝ} (hd : PWDomain p w) : x (w⁻¹ • p) 1 = x p w := by
  have := hx p w w⁻¹ hd (inv_pos.mpr hd.2)
  rwa [inv_mul_cancel₀ hd.2.ne'] at this

/-! ### Derivative notation -/

/-- **Section 2.E** (MWG, p. 26). The price effect `∂x_ℓ/∂p_k` read off a derivative `D` of
`(p, w) ↦ x(p, w)`. -/
def priceEffect {L : ℕ} (D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)) (l k : Fin L) : ℝ :=
  D (Pi.single k 1, 0) l

/-- **Section 2.E** (MWG, p. 24). The wealth effect `∂x_ℓ/∂w` read off a derivative `D`. -/
def wealthEffect {L : ℕ} (D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)) (l : Fin L) : ℝ :=
  D (0, 1) l

/-- **Section 2.E** (MWG, p. 26). The matrix `D_p x(p, w)` of price effects. -/
def priceJacobian {L : ℕ} (D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)) :
    Matrix (Fin L) (Fin L) ℝ :=
  Matrix.of fun l k => priceEffect D l k

/-- **Section 2.E** (MWG, p. 25). The vector `D_w x(p, w)` of wealth effects. -/
def wealthJacobian {L : ℕ} (D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)) : Fin L → ℝ :=
  fun l => wealthEffect D l

/-- A direction `(v, c)` decomposes along the coordinate directions. -/
theorem prod_eq_sum_single {L : ℕ} (v : Fin L → ℝ) (c : ℝ) :
    ((v, c) : (Fin L → ℝ) × ℝ) =
      ∑ k, v k • ((Pi.single k 1, 0) : (Fin L → ℝ) × ℝ) + c • ((0, 1) : (Fin L → ℝ) × ℝ) := by
  ext
  · simp only [Prod.fst_add, Prod.fst_sum, Prod.smul_mk, smul_zero, add_zero]
    rw [Finset.sum_apply]
    simp [Pi.single_apply]
  · simp [Prod.snd_sum]

/-- The derivative in direction `(v, c)` is `D_p x · v + c · D_w x`, componentwise
`∑_k (∂x_ℓ/∂p_k) v_k + (∂x_ℓ/∂w) c`. -/
theorem deriv_apply_eq {L : ℕ} (D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)) (v : Fin L → ℝ)
    (c : ℝ) (l : Fin L) :
    D (v, c) l = ∑ k, priceEffect D l k * v k + wealthEffect D l * c := by
  rw [prod_eq_sum_single v c, map_add, map_sum]
  simp only [map_smul, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    priceEffect, wealthEffect]
  congr 1
  · exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  · ring

/-- Matrix form: `D(v, c) = D_p x · v + c · D_w x`. -/
theorem deriv_apply_eq_mulVec {L : ℕ} (D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ))
    (v : Fin L → ℝ) (c : ℝ) : D (v, c) = Matrix.mulVec (priceJacobian D) v + c • wealthJacobian D
 := by
  funext l
  rw [deriv_apply_eq]
  simp [Matrix.mulVec, dotProduct, priceJacobian, wealthJacobian, mul_comm]

/-! ### Comparative statics vocabulary -/

/-- **Section 2.E** (MWG, p. 24). The Engel function `w ↦ x(p̄, w)` at fixed prices. -/
def engelFunction {L : ℕ} (x : DemandFunction L) (p : Fin L → ℝ) : ℝ → Fin L → ℝ :=
  fun w => x p w

/-- **Section 2.E** (MWG, p. 24). The wealth expansion path `E_p̄ = {x(p̄, w) : w > 0}`. -/
def wealthExpansionPath {L : ℕ} (x : DemandFunction L) (p : Fin L → ℝ) : Set (Fin L → ℝ) :=
  {y | ∃ w, 0 < w ∧ y = x p w}

/-- **Section 2.E** (MWG, p. 25). Good `ℓ` is normal at `(p, w)`: `∂x_ℓ/∂w ≥ 0`. -/
def NormalAt {L : ℕ} (x : DemandFunction L) (p : Fin L → ℝ) (w : ℝ) (l : Fin L) : Prop :=
  0 ≤ wealthEffect (fderiv ℝ (Function.uncurry x) (p, w)) l

/-- **Section 2.E** (MWG, p. 25). Good `ℓ` is inferior at `(p, w)`: `∂x_ℓ/∂w < 0`. -/
def InferiorAt {L : ℕ} (x : DemandFunction L) (p : Fin L → ℝ) (w : ℝ) (l : Fin L) : Prop :=
  wealthEffect (fderiv ℝ (Function.uncurry x) (p, w)) l < 0

/-- **Section 2.E** (MWG, p. 25). Demand is normal: every good is normal at every `(p, w)`. -/
def NormalDemand {L : ℕ} (x : DemandFunction L) : Prop :=
  ∀ p w, PWDomain p w → ∀ l, NormalAt x p w l

/-- **Section 2.E** (MWG, p. 26). Good `ℓ` is a Giffen good at `(p, w)`: `∂x_ℓ/∂p_ℓ > 0`. -/
def GiffenAt {L : ℕ} (x : DemandFunction L) (p : Fin L → ℝ) (w : ℝ) (l : Fin L) : Prop :=
  0 < priceEffect (fderiv ℝ (Function.uncurry x) (p, w)) l l

/-- A good is inferior exactly when it is not normal. -/
theorem inferiorAt_iff_not_normalAt {L : ℕ} (x : DemandFunction L) (p : Fin L → ℝ) (w : ℝ)
    (l : Fin L) : InferiorAt x p w l ↔ ¬ NormalAt x p w l := not_le.symm

/-- Reading the effects off a known derivative. -/
theorem priceEffect_fderiv {L : ℕ} {x : DemandFunction L} {p : Fin L → ℝ} {w : ℝ}
    {D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)} (hD : HasFDerivAt (Function.uncurry x) D (p, w)) :
    fderiv ℝ (Function.uncurry x) (p, w) = D := hD.fderiv

/-! ### Exercises -/

/-- **Exercise 2.E.1** (MWG, p. 23). The three-good demand function
`x₁ = p₂/(p₁+p₂+p₃) · w/p₁`, `x₂ = p₃/(p₁+p₂+p₃) · w/p₂`,
`x₃ = βp₁/(p₁+p₂+p₃) · w/p₃` (goods indexed `0, 1, 2`). -/
noncomputable def demand_2_E_1 (β : ℝ) : DemandFunction 3 := fun p w =>
  ![p 1 / (p 0 + p 1 + p 2) * (w / p 0), p 2 / (p 0 + p 1 + p 2) * (w / p 1),
    β * p 0 / (p 0 + p 1 + p 2) * (w / p 2)]

/-- **Exercise 2.E.1** (MWG, p. 23). The demand is homogeneous of degree zero for every `β`
(in particular for `β = 1` and for `β ∈ (0, 1)`). -/
theorem exercise_2_E_1_homogeneous (β : ℝ) : HomogeneousZero (demand_2_E_1 β) := by
  intro p w α hd ha
  have h0 := (hd.1 0).ne'
  have h1 := (hd.1 1).ne'
  have h2 := (hd.1 2).ne'
  have hP : p 0 + p 1 + p 2 ≠ 0 := by have := hd.1 0; have := hd.1 1; have := hd.1 2; positivity
  have hα := ha.ne'
  funext l
  fin_cases l <;> simp [demand_2_E_1] <;> field_simp

/-- Expenditure on the Exercise 2.E.1 demand: `p·x = w(p₂ + p₃ + βp₁)/(p₁+p₂+p₃)`. -/
theorem demand_2_E_1_expenditure (β : ℝ) {p : Fin 3 → ℝ} {w : ℝ} (hd : PWDomain p w) :
    p ⬝ᵥ demand_2_E_1 β p w = w * (p 1 + p 2 + β * p 0) / (p 0 + p 1 + p 2) := by
  have h0 := (hd.1 0).ne'
  have h1 := (hd.1 1).ne'
  have h2 := (hd.1 2).ne'
  have hP : p 0 + p 1 + p 2 ≠ 0 := by have := hd.1 0; have := hd.1 1; have := hd.1 2; positivity
  simp [dotProduct, Fin.sum_univ_three, demand_2_E_1]
  field_simp

/-- **Exercise 2.E.1** (MWG, p. 23). The demand satisfies Walras' law if and only if `β = 1`;
so it does for `β = 1` and does not for any `β ∈ (0, 1)`. -/
theorem exercise_2_E_1_walras_iff (β : ℝ) : WalrasLaw (demand_2_E_1 β) ↔ β = 1 := by
  constructor
  · intro h
    have hd : PWDomain (fun _ : Fin 3 => (1 : ℝ)) 1 := ⟨fun _ => one_pos, one_pos⟩
    have := h _ _ hd
    rw [demand_2_E_1_expenditure β hd] at this
    norm_num at this
    linarith
  · rintro rfl p w hd
    rw [demand_2_E_1_expenditure 1 hd]
    have hP : p 0 + p 1 + p 2 ≠ 0 := by
      have := hd.1 0; have := hd.1 1; have := hd.1 2; positivity
    field_simp
    ring

/-- **Exercise 2.E.7** (MWG, p. 37). In a two-good economy, Walras' law and
`x₁(p, w) = αw/p₁` force `x₂(p, w) = (1 - α)w/p₂`, and the demand is homogeneous of degree
zero. -/
theorem exercise_2_E_7 {x : DemandFunction 2} {α : ℝ} (hW : WalrasLaw x)
    (h1 : ∀ p w, PWDomain p w → x p w 0 = α * w / p 0) :
    (∀ p w, PWDomain p w → x p w 1 = (1 - α) * w / p 1) ∧ HomogeneousZero x := by
  have h2 : ∀ p w, PWDomain p w → x p w 1 = (1 - α) * w / p 1 := by
    intro p w hd
    have hw := hW p w hd
    simp only [dotProduct, Fin.sum_univ_two] at hw
    rw [h1 p w hd] at hw
    have hp0 := (hd.1 0).ne'
    have hp1 := (hd.1 1).ne'
    field_simp
    field_simp at hw
    linarith
  refine ⟨h2, fun p w a hd ha => ?_⟩
  have hd' := pwDomain_smul hd ha
  funext l
  fin_cases l
  · simp only [Fin.zero_eta]
    rw [h1 _ _ hd', h1 _ _ hd]
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp [ha.ne', (hd.1 0).ne']
  · simp only [Fin.mk_one]
    rw [h2 _ _ hd', h2 _ _ hd]
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp [ha.ne', (hd.1 1).ne']

end MWG.ConsumerChoice

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Calculus along price–wealth lines

Supporting lemmas for the differential results of MWG, Sections 2.E–2.F (pp. 27–35). The
book differentiates identities such as `x(αp, αw) - x(p, w) = 0` or `p·x(p, w) = w` "with
respect to" a parameter. Here this is made rigorous: if `(p, w) ↦ x(p, w)` has Fréchet
derivative `D` at `(p, w)`, then along the line `t ↦ (p + t v, w + t c)` the demand has
derivative `D(v, c)`; and an identity holding on the open domain `p ≫ 0, w > 0` holds for all
`t` near `0`, so its derivative vanishes.
-/

namespace MWG.ConsumerChoice

open Filter Topology

/-- Demand along a line `t ↦ (p + t v, w + t c)` has derivative `D(v, c)` at `t₀`, when `D`
is the derivative of `x` at the point `(p + t₀ v, w + t₀ c)`. -/
theorem hasDerivAt_line {L : ℕ} {x : DemandFunction L} {p v : Fin L → ℝ} {w c t₀ : ℝ}
    {D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)}
    (hD : HasFDerivAt (Function.uncurry x) D (p + t₀ • v, w + t₀ * c)) :
    HasDerivAt (fun t : ℝ => x (p + t • v) (w + t * c)) (D (v, c)) t₀ := by
  have hγ : HasDerivAt (fun t : ℝ => ((p, w) : (Fin L → ℝ) × ℝ) + t • (v, c)) (v, c) t₀ := by
    simpa using ((hasDerivAt_id t₀).smul_const ((v, c) : (Fin L → ℝ) × ℝ)).const_add
      ((p, w) : (Fin L → ℝ) × ℝ)
  have hy : ((p + t₀ • v, w + t₀ * c) : (Fin L → ℝ) × ℝ) = (p, w) + t₀ • (v, c) := by
    simp [smul_eq_mul]
  have := hD.comp_hasDerivAt_of_eq t₀ hγ hy
  convert this using 1
  funext t
  simp [Function.uncurry, smul_eq_mul]


/-- The case `t₀ = 0`: the derivative of demand in direction `(v, c)` at `(p, w)`. -/
theorem hasDerivAt_path {L : ℕ} {x : DemandFunction L} {p : Fin L → ℝ} {w : ℝ}
    {D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)} (hD : HasFDerivAt (Function.uncurry x) D (p, w))
    (v : Fin L → ℝ) (c : ℝ) :
    HasDerivAt (fun t : ℝ => x (p + t • v) (w + t * c)) (D (v, c)) 0 :=
  hasDerivAt_line (by simpa using hD)

/-- Componentwise form of `hasDerivAt_path`. -/
theorem hasDerivAt_path_apply {L : ℕ} {x : DemandFunction L} {p : Fin L → ℝ} {w : ℝ}
    {D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)} (hD : HasFDerivAt (Function.uncurry x) D (p, w))
    (v : Fin L → ℝ) (c : ℝ) (l : Fin L) :
    HasDerivAt (fun t : ℝ => x (p + t • v) (w + t * c) l) (D (v, c) l) 0 :=
  hasDerivAt_pi.mp (hasDerivAt_path hD v c) l

/-- A line through a domain point stays in the domain for `t` near `0`. -/
theorem eventually_pwDomain {L : ℕ} {p : Fin L → ℝ} {w : ℝ} (hd : PWDomain p w)
    (v : Fin L → ℝ) (c : ℝ) : ∀ᶠ t in 𝓝 (0 : ℝ), PWDomain (p + t • v) (w + t * c) := by
  have hcont : ∀ a b : ℝ, Tendsto (fun t : ℝ => a + t * b) (𝓝 0) (𝓝 a) := by
    intro a b
    have : Continuous (fun t : ℝ => a + t * b) := by fun_prop
    simpa using this.tendsto 0
  have hp : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ l, 0 < (p + t • v) l := by
    rw [Filter.eventually_all]
    intro l
    simpa [smul_eq_mul] using (hcont (p l) (v l)).eventually_const_lt (hd.1 l)
  have hw : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < w + t * c := (hcont w c).eventually_const_lt hd.2
  filter_upwards [hp, hw] with t h1 h2
  exact ⟨h1, h2⟩

/-- A function with a derivative at `a` that is eventually constant near `a` has zero
derivative. -/
theorem hasDerivAt_eq_zero_of_eventually_const {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℝ → E} {f' : E} {a : ℝ} (hf : HasDerivAt f f' a) (c : E)
    (h : ∀ᶠ t in 𝓝 a, f t = c) : f' = 0 :=
  hf.unique ((hasDerivAt_const a c).congr_of_eventuallyEq h)

/-- If `x` satisfies Walras' law and has derivative `D` at a domain point, then for every
direction `(v, c)`: `v·x(p, w) + p·D(v, c) = c`. This is the derivative of
`p·x(p, w) = w` along `(v, c)`. -/
theorem walras_deriv_identity {L : ℕ} {x : DemandFunction L} (hW : WalrasLaw x)
    {p : Fin L → ℝ} {w : ℝ} (hd : PWDomain p w) {D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)}
    (hD : HasFDerivAt (Function.uncurry x) D (p, w)) (v : Fin L → ℝ) (c : ℝ) :
    v ⬝ᵥ x p w + p ⬝ᵥ D (v, c) = c := by
  have hterm : ∀ l ∈ (Finset.univ : Finset (Fin L)),
      HasDerivAt (fun t : ℝ => (p l + t * v l) * x (p + t • v) (w + t * c) l)
        (v l * x p w l + p l * D (v, c) l) 0 := by
    intro l _
    have h1 : HasDerivAt (fun t : ℝ => p l + t * v l) (v l) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v l)).const_add (p l)
    have h2 := hasDerivAt_path_apply hD v c l
    have := h1.fun_mul h2
    simpa using this
  have hsum := HasDerivAt.fun_sum hterm
  have hc : HasDerivAt (fun t : ℝ => w + t * c) c 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const c).const_add w
  have hg := hsum.sub hc
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ),
      (∑ l, (p l + t * v l) * x (p + t • v) (w + t * c) l) - (w + t * c) = 0 := by
    filter_upwards [eventually_pwDomain hd v c] with t ht
    have := hW _ _ ht
    simp only [dotProduct, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    rw [this, sub_self]
  have h0 := hasDerivAt_eq_zero_of_eventually_const hg 0 hev
  rw [Finset.sum_add_distrib, sub_eq_zero] at h0
  simpa [dotProduct] using h0

/-- If `x` is homogeneous of degree zero and has derivative `D` at a domain point `(p, w)`,
then `D(p, w) = 0`: the derivative of `α ↦ x(αp, αw)` at `α = 1`. -/
theorem homogeneous_deriv_identity {L : ℕ} {x : DemandFunction L} (hH : HomogeneousZero x)
    {p : Fin L → ℝ} {w : ℝ} (hd : PWDomain p w) {D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)}
    (hD : HasFDerivAt (Function.uncurry x) D (p, w)) : D (p, w) = 0 := by
  have h := hasDerivAt_path hD p w
  apply hasDerivAt_eq_zero_of_eventually_const h (x p w)
  have hpos : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < 1 + t := by
    have : Tendsto (fun t : ℝ => 1 + t) (𝓝 0) (𝓝 1) := by
      have hc : Continuous (fun t : ℝ => 1 + t) := by fun_prop
      simpa using hc.tendsto (0 : ℝ)
    exact this.eventually_const_lt one_pos
  filter_upwards [hpos] with t ht
  have e1 : p + t • p = (1 + t) • p := by rw [add_smul, one_smul]
  have e2 : w + t * w = (1 + t) * w := by ring
  rw [e1, e2]
  exact hH p w _ hd ht

end MWG.ConsumerChoice

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Implications of homogeneity and Walras' law for price and wealth effects

MWG, Section 2.E, pp. 27–28: Propositions 2.E.1–2.E.3 (equations (2.E.1)–(2.E.7)), the
elasticity forms, and Exercise 2.E.2 (p. 28). Demand is differentiable at the point in
question, in the Fréchet sense (`HasFDerivAt` of `(p, w) ↦ x(p, w)`), at an interior point
`p ≫ 0`, `w > 0`. Elasticities are taken where `x_ℓ(p, w) ≠ 0`, where they are defined.
-/

namespace MWG.ConsumerChoice

/-- **Section 2.E** (MWG, p. 27). The price elasticity `ε_ℓk = (∂x_ℓ/∂p_k)(p_k/x_ℓ)`. -/
noncomputable def priceElasticity {L : ℕ} (D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ))
    (p xv : Fin L → ℝ) (l k : Fin L) : ℝ :=
  priceEffect D l k * (p k / xv l)

/-- **Section 2.E** (MWG, p. 27). The wealth elasticity `ε_ℓw = (∂x_ℓ/∂w)(w/x_ℓ)`. -/
noncomputable def wealthElasticity {L : ℕ} (D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ))
    (w : ℝ) (xv : Fin L → ℝ) (l : Fin L) : ℝ :=
  wealthEffect D l * (w / xv l)

/-- **Exercise 2.E.2** (MWG, p. 28). The budget share `b_ℓ = p_ℓ x_ℓ / w`. -/
noncomputable def budgetShare {L : ℕ} (p xv : Fin L → ℝ) (w : ℝ) (l : Fin L) : ℝ :=
  p l * xv l / w

/-- **Proposition 2.E.1** (MWG, p. 27), equation (2.E.1). If `x` is homogeneous of degree zero
and differentiable at `(p, w)`, then `∑_k (∂x_ℓ/∂p_k) p_k + (∂x_ℓ/∂w) w = 0` for every `ℓ`. -/
theorem proposition_2_E_1 {L : ℕ} {x : DemandFunction L} (hH : HomogeneousZero x)
    {p : Fin L → ℝ} {w : ℝ} (hd : PWDomain p w) {D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)}
    (hD : HasFDerivAt (Function.uncurry x) D (p, w)) (l : Fin L) :
    ∑ k, priceEffect D l k * p k + wealthEffect D l * w = 0 := by
  rw [← deriv_apply_eq, homogeneous_deriv_identity hH hd hD]
  rfl

/-- **Proposition 2.E.1** (MWG, p. 27), matrix form (2.E.2): `D_p x(p, w) p + D_w x(p, w) w = 0`.
-/
theorem proposition_2_E_1_matrix {L : ℕ} {x : DemandFunction L} (hH : HomogeneousZero x)
    {p : Fin L → ℝ} {w : ℝ} (hd : PWDomain p w) {D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)}
    (hD : HasFDerivAt (Function.uncurry x) D (p, w)) :
    Matrix.mulVec (priceJacobian D) p + w • wealthJacobian D = 0 := by
  rw [← deriv_apply_eq_mulVec, homogeneous_deriv_identity hH hd hD]

/-- **Proposition 2.E.1** (MWG, p. 27), elasticity form (2.E.3):
`∑_k ε_ℓk(p, w) + ε_ℓw(p, w) = 0` (elasticities are meaningful where `x_ℓ(p, w) ≠ 0`; where
`x_ℓ(p, w) = 0` Lean's convention `a/0 = 0` makes both sides zero, so no hypothesis is needed).
-/
theorem proposition_2_E_1_elasticity {L : ℕ} {x : DemandFunction L} (hH : HomogeneousZero x)
    {p : Fin L → ℝ} {w : ℝ} (hd : PWDomain p w) {D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)}
    (hD : HasFDerivAt (Function.uncurry x) D (p, w)) (l : Fin L) :
    ∑ k, priceElasticity D p (x p w) l k + wealthElasticity D w (x p w) l = 0 := by
  have h := proposition_2_E_1 hH hd hD l
  simp only [priceElasticity, wealthElasticity, mul_div_assoc']
  rw [← Finset.sum_div, ← add_div, h, zero_div]

/-- **Proposition 2.E.2** (MWG, p. 28), equation (2.E.4) (Cournot aggregation). If `x`
satisfies Walras' law and is differentiable at `(p, w)`, then
`∑_ℓ p_ℓ (∂x_ℓ/∂p_k) + x_k(p, w) = 0` for every `k`. -/
theorem proposition_2_E_2 {L : ℕ} {x : DemandFunction L} (hW : WalrasLaw x)
    {p : Fin L → ℝ} {w : ℝ} (hd : PWDomain p w) {D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)}
    (hD : HasFDerivAt (Function.uncurry x) D (p, w)) (k : Fin L) :
    ∑ l, p l * priceEffect D l k + x p w k = 0 := by
  have h := walras_deriv_identity hW hd hD (Pi.single k 1) 0
  rw [single_dotProduct, one_mul] at h
  simpa [dotProduct, priceEffect, add_comm] using h

/-- **Proposition 2.E.2** (MWG, p. 28), matrix form (2.E.5): `p·D_p x(p, w) + x(p, w)ᵀ = 0ᵀ`.
-/
theorem proposition_2_E_2_matrix {L : ℕ} {x : DemandFunction L} (hW : WalrasLaw x)
    {p : Fin L → ℝ} {w : ℝ} (hd : PWDomain p w) {D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)}
    (hD : HasFDerivAt (Function.uncurry x) D (p, w)) :
    Matrix.vecMul p (priceJacobian D) + x p w = 0 := by
  funext k
  simpa [Matrix.vecMul, dotProduct, priceJacobian] using proposition_2_E_2 hW hd hD k

/-- **Proposition 2.E.3** (MWG, p. 28), equation (2.E.6) (Engel aggregation). If `x` satisfies
Walras' law and is differentiable at `(p, w)`, then `∑_ℓ p_ℓ (∂x_ℓ/∂w) = 1`. -/
theorem proposition_2_E_3 {L : ℕ} {x : DemandFunction L} (hW : WalrasLaw x)
    {p : Fin L → ℝ} {w : ℝ} (hd : PWDomain p w) {D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)}
    (hD : HasFDerivAt (Function.uncurry x) D (p, w)) :
    ∑ l, p l * wealthEffect D l = 1 := by
  have h := walras_deriv_identity hW hd hD 0 1
  simpa [dotProduct, wealthEffect] using h

/-- **Proposition 2.E.3** (MWG, p. 28), matrix form (2.E.7): `p·D_w x(p, w) = 1`. -/
theorem proposition_2_E_3_matrix {L : ℕ} {x : DemandFunction L} (hW : WalrasLaw x)
    {p : Fin L → ℝ} {w : ℝ} (hd : PWDomain p w) {D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)}
    (hD : HasFDerivAt (Function.uncurry x) D (p, w)) : p ⬝ᵥ wealthJacobian D = 1 :=
  proposition_2_E_3 hW hd hD

/-- **Exercise 2.E.2** (MWG, p. 28), first formula. With Walras' law and every
`x_ℓ(p, w) ≠ 0`: `∑_ℓ b_ℓ ε_ℓk + b_k = 0`. -/
theorem exercise_2_E_2_price {L : ℕ} {x : DemandFunction L} (hW : WalrasLaw x)
    {p : Fin L → ℝ} {w : ℝ} (hd : PWDomain p w) {D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)}
    (hD : HasFDerivAt (Function.uncurry x) D (p, w)) (hx : ∀ l, x p w l ≠ 0) (k : Fin L) :
    ∑ l, budgetShare p (x p w) w l * priceElasticity D p (x p w) l k +
      budgetShare p (x p w) w k = 0 := by
  have h := proposition_2_E_2 hW hd hD k
  have hw := hd.2.ne'
  have hterm : ∀ l, budgetShare p (x p w) w l * priceElasticity D p (x p w) l k =
      p k / w * (p l * priceEffect D l k) := by
    intro l
    simp only [budgetShare, priceElasticity]
    field_simp [hx l]
  rw [Finset.sum_congr rfl (fun l _ => hterm l), ← Finset.mul_sum]
  simp only [budgetShare]
  calc p k / w * ∑ l, p l * priceEffect D l k + p k * x p w k / w
      = p k / w * (∑ l, p l * priceEffect D l k + x p w k) := by ring
    _ = 0 := by rw [h, mul_zero]

/-- **Exercise 2.E.2** (MWG, p. 28), second formula. With Walras' law and every
`x_ℓ(p, w) ≠ 0`: `∑_ℓ b_ℓ ε_ℓw = 1`. -/
theorem exercise_2_E_2_wealth {L : ℕ} {x : DemandFunction L} (hW : WalrasLaw x)
    {p : Fin L → ℝ} {w : ℝ} (hd : PWDomain p w) {D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)}
    (hD : HasFDerivAt (Function.uncurry x) D (p, w)) (hx : ∀ l, x p w l ≠ 0) :
    ∑ l, budgetShare p (x p w) w l * wealthElasticity D w (x p w) l = 1 := by
  have h := proposition_2_E_3 hW hd hD
  have hw := hd.2.ne'
  have hterm : ∀ l, budgetShare p (x p w) w l * wealthElasticity D w (x p w) l =
      p l * wealthEffect D l := by
    intro l
    simp only [budgetShare, wealthElasticity]
    field_simp [hx l]
  simp only [hterm, h]

/-- **Exercise 2.E.3** (MWG, p. 36). With Walras' law, `p·D_p x(p, w) p = -w`: a proportional
rise in all prices at constant wealth lowers real expenditure capacity one-for-one. (Only
Walras' law, through Proposition 2.E.2, is used.) -/
theorem exercise_2_E_3 {L : ℕ} {x : DemandFunction L} (hW : WalrasLaw x)
    {p : Fin L → ℝ} {w : ℝ} (hd : PWDomain p w) {D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)}
    (hD : HasFDerivAt (Function.uncurry x) D (p, w)) :
    p ⬝ᵥ Matrix.mulVec (priceJacobian D) p = -w := by
  rw [Matrix.dotProduct_mulVec]
  have h := proposition_2_E_2_matrix hW hd hD
  rw [eq_neg_of_add_eq_zero_left h, neg_dotProduct, dotProduct_comm, hW p w hd]

/-- **Exercise 2.E.3** (MWG, p. 36), by the route the hint suggests: Proposition 2.E.1 gives
`D_p x p = -w D_w x`, and Proposition 2.E.3 gives `p·D_w x = 1`. -/
theorem exercise_2_E_3_via_homogeneity {L : ℕ} {x : DemandFunction L} (hH : HomogeneousZero x)
    (hW : WalrasLaw x) {p : Fin L → ℝ} {w : ℝ} (hd : PWDomain p w)
    {D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)} (hD : HasFDerivAt (Function.uncurry x) D (p, w)) :
    p ⬝ᵥ Matrix.mulVec (priceJacobian D) p = -w := by
  have h := proposition_2_E_1_matrix hH hd hD
  rw [eq_neg_of_add_eq_zero_left h, dotProduct_neg, dotProduct_smul,
    proposition_2_E_3_matrix hW hd hD, smul_eq_mul, mul_one]

/-! ### Exercise 2.E.4 -/

/-- **Exercise 2.E.4** (MWG, p. 36). Demand is homogeneous of degree one in wealth:
`x(p, αw) = αx(p, w)` for `α > 0`. -/
def HomogeneousOneInWealth {L : ℕ} (x : DemandFunction L) : Prop :=
  ∀ p w α, PWDomain p w → 0 < α → x p (α * w) = α • x p w

/-- **Exercise 2.E.4** (MWG, p. 36). Under homogeneity of degree one in wealth,
`D_w x(p, w) = (1/w) x(p, w)`. -/
theorem exercise_2_E_4_wealthJacobian {L : ℕ} {x : DemandFunction L}
    (h1 : HomogeneousOneInWealth x) {p : Fin L → ℝ} {w : ℝ} (hd : PWDomain p w)
    {D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)} (hD : HasFDerivAt (Function.uncurry x) D (p, w)) :
    wealthJacobian D = w⁻¹ • x p w := by
  have hpath := hasDerivAt_path hD 0 1
  have hw := hd.2
  have hlin : HasDerivAt (fun t : ℝ => (1 + t * w⁻¹) • x p w) (w⁻¹ • x p w) 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).mul_const w⁻¹).const_add 1).smul_const (x p w)
  have hev : (fun t : ℝ => x (p + t • 0) (w + t * 1)) =ᶠ[nhds 0]
      (fun t : ℝ => (1 + t * w⁻¹) • x p w) := by
    have hpos : ∀ᶠ t in nhds (0 : ℝ), 0 < 1 + t * w⁻¹ := by
      have hc : Continuous (fun t : ℝ => 1 + t * w⁻¹) := by fun_prop
      have := hc.tendsto (0 : ℝ)
      simp only [zero_mul, add_zero] at this
      exact this.eventually_const_lt one_pos
    filter_upwards [hpos] with t ht
    simp only [smul_zero, add_zero, mul_one]
    rw [← h1 p w _ hd ht]
    congr 1
    field_simp
  have := hpath.unique (hlin.congr_of_eventuallyEq hev)
  funext l
  have := congrFun this l
  simpa [wealthJacobian, wealthEffect] using this

/-- **Exercise 2.E.4** (MWG, p. 36). Under homogeneity of degree one in wealth,
`ε_ℓw(p, w) = 1` for every good with `x_ℓ(p, w) ≠ 0`. -/
theorem exercise_2_E_4 {L : ℕ} {x : DemandFunction L} (h1 : HomogeneousOneInWealth x)
    {p : Fin L → ℝ} {w : ℝ} (hd : PWDomain p w) {D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)}
    (hD : HasFDerivAt (Function.uncurry x) D (p, w)) (l : Fin L) (hx : x p w l ≠ 0) :
    wealthElasticity D w (x p w) l = 1 := by
  have h := congrFun (exercise_2_E_4_wealthJacobian h1 hd hD) l
  simp only [wealthJacobian, Pi.smul_apply, smul_eq_mul] at h
  simp only [wealthElasticity, h]
  field_simp [hd.2.ne', hx]

/-- **Exercise 2.E.4** (MWG, p. 36). Under homogeneity of degree one in wealth the Engel
function is linear, `x(p, w) = w x(p, 1)`, so the wealth expansion path is the open ray
through `x(p, 1)`. -/
theorem exercise_2_E_4_engel {L : ℕ} {x : DemandFunction L} (h1 : HomogeneousOneInWealth x)
    {p : Fin L → ℝ} (hp : StrictlyPositive p) :
    (∀ w, 0 < w → engelFunction x p w = w • x p 1) ∧
      wealthExpansionPath x p = {y | ∃ t : ℝ, 0 < t ∧ y = t • x p 1} := by
  have he : ∀ w, 0 < w → engelFunction x p w = w • x p 1 := by
    intro w hw
    have := h1 p 1 w ⟨hp, one_pos⟩ hw
    rwa [mul_one] at this
  refine ⟨he, ?_⟩
  ext y
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, hw, he w hw⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, ht, (he t ht).symm⟩

end MWG.ConsumerChoice

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercises 2.E.5, 2.E.6 and 2.E.8

MWG, Exercises 2.E.5, 2.E.6 and 2.E.8 (p. 37).

* Exercise 2.E.5: homogeneity of degree one in wealth, Walras' law, homogeneity of degree
  zero and zero cross-price effects force `x_ℓ(p, w) = α_ℓ w / p_ℓ`. The constants satisfy
  `α_ℓ ≥ 0` and `∑ α_ℓ = 1`; the printed `α_ℓ > 0` does not follow (counterexample
  `x(p, w) = (w/p₁, 0)`). Differentiability of demand on the domain is assumed, since
  "cross-price effects" are derivatives.
* Exercise 2.E.6: the demand of Exercise 2.E.1 with `β = 1` is differentiable on the domain,
  so Propositions 2.E.1–2.E.3 apply to it.
* Exercise 2.E.8: elasticities are logarithmic derivatives, and the coefficients of a
  log-linear demand equation are the elasticities.
-/

namespace MWG.ConsumerChoice

open Filter Topology

/-- Under zero cross-price effects, `x_ℓ(p, w)` depends on `p` only through `p_ℓ`. -/
theorem demand_eq_of_own_price_eq {L : ℕ} {x : DemandFunction L}
    (hdiff : ∀ p w, PWDomain p w → DifferentiableAt ℝ (Function.uncurry x) (p, w))
    (hcross : ∀ p w, PWDomain p w → ∀ l k, k ≠ l →
      priceEffect (fderiv ℝ (Function.uncurry x) (p, w)) l k = 0)
    {p p' : Fin L → ℝ} (hp : StrictlyPositive p) (hp' : StrictlyPositive p') {w : ℝ}
    (hw : 0 < w) (l : Fin L) (hl : p l = p' l) : x p w l = x p' w l := by
  set v := p' - p with hv
  let f : ℝ → ℝ := fun t => x (p + t • v) (w + t * 0) l
  have hdom : ∀ t ∈ Set.Icc (0 : ℝ) 1, PWDomain (p + t • v) (w + t * 0) := by
    intro t ht
    refine ⟨fun k => ?_, by simpa using hw⟩
    have h1 := hp k
    have h2 := hp' k
    simp only [hv, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rcases eq_or_lt_of_le ht.2 with h | h
    · rw [h]
      linarith
    · nlinarith [mul_nonneg ht.1 h2.le, mul_pos (sub_pos.mpr h) h1]
  have hder : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt f 0 t := by
    intro t ht
    have hD := (hdiff _ _ (hdom t ht)).hasFDerivAt
    have h := hasDerivAt_pi.mp (hasDerivAt_line (x := x) (p := p) (v := v) (w := w) (c := 0)
      (t₀ := t) hD) l
    convert h using 1
    rw [deriv_apply_eq]
    simp only [mul_zero, add_zero]
    symm
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : k = l
    · subst hk
      simp [hv, hl]
    · have hdom' : PWDomain (p + t • v) w := by simpa using hdom t ht
      rw [hcross _ _ hdom' l k hk, zero_mul]
  have hcont : ContinuousOn f (Set.Icc 0 1) :=
    fun t ht => (hder t ht).continuousAt.continuousWithinAt
  have hconst := constant_of_has_deriv_right_zero hcont
    (fun t ht => (hder t (Set.Ico_subset_Icc_self ht)).hasDerivWithinAt) 1
    (Set.right_mem_Icc.mpr zero_le_one)
  simpa [f, hv] using hconst.symm

/-- **Exercise 2.E.5** (MWG, p. 37), corrected. If `x` is homogeneous of degree one in `w`,
satisfies Walras' law and homogeneity of degree zero, takes values in `ℝ^L_+`, is
differentiable on the domain and has zero cross-price effects, then there are constants
`α_ℓ ≥ 0` with `∑ α_ℓ = 1` and `x_ℓ(p, w) = α_ℓ w / p_ℓ`. -/
theorem exercise_2_E_5 {L : ℕ} {x : DemandFunction L} (hH : HomogeneousZero x)
    (hW : WalrasLaw x) (h1 : HomogeneousOneInWealth x)
    (hX : ∀ p w, PWDomain p w → ∀ l, 0 ≤ x p w l)
    (hdiff : ∀ p w, PWDomain p w → DifferentiableAt ℝ (Function.uncurry x) (p, w))
    (hcross : ∀ p w, PWDomain p w → ∀ l k, k ≠ l →
      priceEffect (fderiv ℝ (Function.uncurry x) (p, w)) l k = 0) :
    ∃ α : Fin L → ℝ, (∀ l, 0 ≤ α l) ∧ ∑ l, α l = 1 ∧
      ∀ p w, PWDomain p w → ∀ l, x p w l = α l * w / p l := by
  have hone : StrictlyPositive (fun _ : Fin L => (1 : ℝ)) := fun _ => one_pos
  refine ⟨x (fun _ => 1) 1, fun l => hX _ _ ⟨hone, one_pos⟩ l, ?_, ?_⟩
  · have := hW _ _ ⟨hone, one_pos⟩
    simpa [dotProduct] using this
  · intro p w hd l
    have hpl := hd.1 l
    set a := (p l)⁻¹ with ha
    have ha0 : 0 < a := inv_pos.mpr hpl
    have hq : StrictlyPositive (a • p) := (pwDomain_smul hd ha0).1
    have e1 : x p w = w • x p 1 := by
      have := h1 p 1 w ⟨hd.1, one_pos⟩ hd.2
      rwa [mul_one] at this
    have e2 : x p 1 = x (a • p) a := by
      have := hH p 1 a ⟨hd.1, one_pos⟩ ha0
      rw [mul_one] at this
      exact this.symm
    have e3 : x (a • p) a = a • x (a • p) 1 := by
      have := h1 (a • p) 1 a ⟨hq, one_pos⟩ ha0
      rwa [mul_one] at this
    have e4 : x (a • p) 1 l = x (fun _ => 1) 1 l :=
      demand_eq_of_own_price_eq hdiff hcross hq hone one_pos l (by simp [ha, hpl.ne'])
    rw [e1, e2, e3]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [e4, ha]
    field_simp

/-- **Exercise 2.E.5** (MWG, p. 37): the counterexample demand `x(p, w) = (w/p₁, 0)`. -/
noncomputable def demand_2_E_5_counterexample : DemandFunction 2 := fun p w => ![w / p 0, 0]

/-- The counterexample demand is differentiable on the domain. -/
theorem demand_2_E_5_counterexample_differentiableAt {p : Fin 2 → ℝ} {w : ℝ}
    (hd : PWDomain p w) :
    DifferentiableAt ℝ (Function.uncurry demand_2_E_5_counterexample) (p, w) := by
  rw [differentiableAt_pi]
  intro i
  fin_cases i
  · have h0 := (hd.1 0).ne'
    simp only [Fin.zero_eta, demand_2_E_5_counterexample, Function.uncurry_def,
      Matrix.cons_val_zero, div_eq_mul_inv]
    fun_prop (disch := assumption)
  · simp only [Fin.mk_one, demand_2_E_5_counterexample, Function.uncurry_def,
      Matrix.cons_val_one, Matrix.cons_val_zero]
    exact differentiableAt_const _

/-- **Exercise 2.E.5** (MWG, p. 37). The printed conclusion `α_ℓ > 0` is false: the demand
`x(p, w) = (w/p₁, 0)` satisfies every hypothesis of the exercise, but no representation
`x_ℓ = α_ℓ w/p_ℓ` has all `α_ℓ > 0`. -/
theorem exercise_2_E_5_alpha_pos_counterexample :
    HomogeneousZero demand_2_E_5_counterexample ∧ WalrasLaw demand_2_E_5_counterexample ∧
      HomogeneousOneInWealth demand_2_E_5_counterexample ∧
      (∀ p w, PWDomain p w → ∀ l, 0 ≤ demand_2_E_5_counterexample p w l) ∧
      (∀ p w, PWDomain p w →
        DifferentiableAt ℝ (Function.uncurry demand_2_E_5_counterexample) (p, w)) ∧
      (∀ p w, PWDomain p w → ∀ l k, k ≠ l →
        priceEffect (fderiv ℝ (Function.uncurry demand_2_E_5_counterexample) (p, w)) l k = 0) ∧
      ¬ ∃ α : Fin 2 → ℝ, (∀ l, 0 < α l) ∧ ∀ p w, PWDomain p w → ∀ l,
        demand_2_E_5_counterexample p w l = α l * w / p l := by
  refine ⟨?_, ?_, ?_, ?_, fun p w hd => demand_2_E_5_counterexample_differentiableAt hd, ?_, ?_⟩
  · intro p w a hd ha
    funext l
    fin_cases l
    · simp only [demand_2_E_5_counterexample, Fin.zero_eta, Matrix.cons_val_zero,
        Pi.smul_apply, smul_eq_mul]
      field_simp [ha.ne', (hd.1 0).ne']
    · simp [demand_2_E_5_counterexample]
  · intro p w hd
    simp only [demand_2_E_5_counterexample, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, mul_zero, add_zero]
    field_simp [(hd.1 0).ne']
  · intro p w a hd ha
    funext l
    fin_cases l
    · simp only [demand_2_E_5_counterexample, Fin.zero_eta, Matrix.cons_val_zero,
        Pi.smul_apply, smul_eq_mul]
      ring
    · simp [demand_2_E_5_counterexample]
  · intro p w hd l
    fin_cases l
    · simpa [demand_2_E_5_counterexample] using div_nonneg hd.2.le (hd.1 0).le
    · simp [demand_2_E_5_counterexample]
  · intro p w hd l k hkl
    have hD := (demand_2_E_5_counterexample_differentiableAt hd).hasFDerivAt
    have h := hasDerivAt_path_apply hD (Pi.single k 1) 0 l
    apply hasDerivAt_eq_zero_of_eventually_const h (demand_2_E_5_counterexample p w l)
    refine Filter.Eventually.of_forall fun t => ?_
    fin_cases l <;> fin_cases k
    · exact absurd rfl hkl
    · simp [demand_2_E_5_counterexample]
    · simp [demand_2_E_5_counterexample]
    · exact absurd rfl hkl
  · rintro ⟨α, hα, hrep⟩
    have hd : PWDomain (fun _ : Fin 2 => (1 : ℝ)) 1 := ⟨fun _ => one_pos, one_pos⟩
    have := hrep _ _ hd 1
    simp [demand_2_E_5_counterexample] at this
    linarith [hα 1]

/-- The Exercise 2.E.1 demand (any `β`) is differentiable at every domain point. -/
theorem demand_2_E_1_differentiableAt (β : ℝ) {p : Fin 3 → ℝ} {w : ℝ} (hd : PWDomain p w) :
    DifferentiableAt ℝ (Function.uncurry (demand_2_E_1 β)) (p, w) := by
  have h0 := (hd.1 0).ne'
  have h1 := (hd.1 1).ne'
  have h2 := (hd.1 2).ne'
  have hP : p 0 + p 1 + p 2 ≠ 0 := by have := hd.1 0; have := hd.1 1; have := hd.1 2; positivity
  rw [differentiableAt_pi]
  intro i
  fin_cases i <;>
    simp only [demand_2_E_1, Function.uncurry_def, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons, div_eq_mul_inv] <;>
    fun_prop (disch := assumption)

/-- **Exercise 2.E.6** (MWG, p. 37). For the demand of Exercise 2.E.1 with `β = 1`, the
conclusions of Propositions 2.E.1, 2.E.2 and 2.E.3 hold at every `(p, w)`. -/
theorem exercise_2_E_6 {p : Fin 3 → ℝ} {w : ℝ} (hd : PWDomain p w) :
    (∀ l, ∑ k, priceEffect (fderiv ℝ (Function.uncurry (demand_2_E_1 1)) (p, w)) l k * p k +
        wealthEffect (fderiv ℝ (Function.uncurry (demand_2_E_1 1)) (p, w)) l * w = 0) ∧
      (∀ k, ∑ l, p l * priceEffect (fderiv ℝ (Function.uncurry (demand_2_E_1 1)) (p, w)) l k +
        demand_2_E_1 1 p w k = 0) ∧
      ∑ l, p l * wealthEffect (fderiv ℝ (Function.uncurry (demand_2_E_1 1)) (p, w)) l = 1 := by
  have hD := (demand_2_E_1_differentiableAt 1 hd).hasFDerivAt
  have hW := (exercise_2_E_1_walras_iff 1).mpr rfl
  exact ⟨proposition_2_E_1 (exercise_2_E_1_homogeneous 1) hd hD,
    proposition_2_E_2 hW hd hD, proposition_2_E_3 hW hd hD⟩

/-! ### Exercise 2.E.8 -/

/-- The curve `s ↦ (p + (e^s - p_k) e_k, w)` passes through `(p, w)` at `s = ln p_k` with
velocity `(p_k e_k, 0)`. -/
theorem hasDerivAt_exp_price_curve {L : ℕ} {p : Fin L → ℝ} (w : ℝ) (k : Fin L)
    (hk : 0 < p k) :
    HasDerivAt (fun s : ℝ => ((p + (Real.exp s - p k) • Pi.single k 1, w) :
      (Fin L → ℝ) × ℝ)) (p k • ((Pi.single k 1, 0) : (Fin L → ℝ) × ℝ)) (Real.log (p k)) := by
  have he : HasDerivAt (fun s : ℝ => Real.exp s - p k) (p k) (Real.log (p k)) := by
    have := (Real.hasDerivAt_exp (Real.log (p k))).sub_const (p k)
    rwa [Real.exp_log hk] at this
  have := (he.smul_const ((Pi.single k 1, 0) : (Fin L → ℝ) × ℝ)).const_add
    ((p, w) : (Fin L → ℝ) × ℝ)
  convert this using 1
  funext s
  simp

/-- **Exercise 2.E.8** (MWG, p. 37). The price elasticity is a logarithmic derivative:
`ε_ℓk(p, w) = d ln x_ℓ / d ln p_k`, i.e. the derivative of
`s ↦ ln x_ℓ(p with p_k = e^s, w)` at `s = ln p_k` (for `x_ℓ(p, w) > 0`). -/
theorem exercise_2_E_8_price {L : ℕ} {x : DemandFunction L} {p : Fin L → ℝ} {w : ℝ}
    (hd : PWDomain p w) {D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)}
    (hD : HasFDerivAt (Function.uncurry x) D (p, w)) (l k : Fin L) (hx : 0 < x p w l) :
    HasDerivAt (fun s => Real.log (x (p + (Real.exp s - p k) • Pi.single k 1) w l))
      (priceElasticity D p (x p w) l k) (Real.log (p k)) := by
  have hk := hd.1 k
  have hy : ((p, w) : (Fin L → ℝ) × ℝ) =
      (p + (Real.exp (Real.log (p k)) - p k) • Pi.single k 1, w) := by
    simp [Real.exp_log hk]
  have hc := hD.comp_hasDerivAt_of_eq (Real.log (p k)) (hasDerivAt_exp_price_curve w k hk) hy
  have hl := (hasDerivAt_pi.mp hc l).log (by simpa [Real.exp_log hk] using hx.ne')
  have hval : (Function.uncurry x ∘ fun s => (p + (Real.exp s - p k) • Pi.single k 1, w))
      (Real.log (p k)) = x p w := by simp [Real.exp_log hk]
  rw [hval, map_smul] at hl
  convert hl using 1
  · rfl
  · simp only [Pi.smul_apply, smul_eq_mul, priceElasticity, priceEffect]
    field_simp

/-- **Exercise 2.E.8** (MWG, p. 37). The wealth elasticity is `d ln x_ℓ / d ln w`. -/
theorem exercise_2_E_8_wealth {L : ℕ} {x : DemandFunction L} {p : Fin L → ℝ} {w : ℝ}
    (hd : PWDomain p w) {D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)}
    (hD : HasFDerivAt (Function.uncurry x) D (p, w)) (l : Fin L) (hx : 0 < x p w l) :
    HasDerivAt (fun s => Real.log (x p (Real.exp s) l)) (wealthElasticity D w (x p w) l)
      (Real.log w) := by
  have hw := hd.2
  have hγ : HasDerivAt (fun s : ℝ => ((p, Real.exp s) : (Fin L → ℝ) × ℝ))
      (w • ((0, 1) : (Fin L → ℝ) × ℝ)) (Real.log w) := by
    have he := Real.hasDerivAt_exp (Real.log w)
    rw [Real.exp_log hw] at he
    have := (he.smul_const ((0, 1) : (Fin L → ℝ) × ℝ)).const_add ((p, 0) : (Fin L → ℝ) × ℝ)
    convert this using 1
    funext s
    simp
  have hy : ((p, w) : (Fin L → ℝ) × ℝ) = (p, Real.exp (Real.log w)) := by
    simp [Real.exp_log hw]
  have hc := hD.comp_hasDerivAt_of_eq (Real.log w) hγ hy
  have hl := (hasDerivAt_pi.mp hc l).log (by simpa [Real.exp_log hw] using hx.ne')
  have hval : (Function.uncurry x ∘ fun s => ((p, Real.exp s) : (Fin L → ℝ) × ℝ))
      (Real.log w) = x p w := by simp [Real.exp_log hw]
  rw [hval, map_smul] at hl
  convert hl using 1
  · rfl
  · simp only [Pi.smul_apply, smul_eq_mul, wealthElasticity, wealthEffect]
    field_simp

/-- **Exercise 2.E.8** (MWG, p. 37). If, for `L = 2`,
`ln x_ℓ(p, w) = α₀ + α₁ ln p₁ + α₂ ln p₂ + γ ln w` on the whole domain, then the parameters
are the elasticities: `ε_ℓ1 = α₁`, `ε_ℓ2 = α₂` and `ε_ℓw = γ` (goods indexed `0, 1`). -/
theorem exercise_2_E_8_loglinear {x : DemandFunction 2} {l : Fin 2} {a0 a1 a2 γ : ℝ}
    (hpos : ∀ p w, PWDomain p w → 0 < x p w l)
    (hlog : ∀ p w, PWDomain p w → Real.log (x p w l) =
      a0 + a1 * Real.log (p 0) + a2 * Real.log (p 1) + γ * Real.log w)
    {p : Fin 2 → ℝ} {w : ℝ} (hd : PWDomain p w) {D : ((Fin 2 → ℝ) × ℝ) →L[ℝ] (Fin 2 → ℝ)}
    (hD : HasFDerivAt (Function.uncurry x) D (p, w)) :
    priceElasticity D p (x p w) l 0 = a1 ∧ priceElasticity D p (x p w) l 1 = a2 ∧
      wealthElasticity D w (x p w) l = γ := by
  have hx := hpos p w hd
  have hupd : ∀ (k : Fin 2) (s : ℝ),
      PWDomain (p + (Real.exp s - p k) • Pi.single k 1) w := by
    intro k s
    refine ⟨fun j => ?_, hd.2⟩
    by_cases hj : j = k
    · subst hj
      simpa using Real.exp_pos s
    · simpa [Pi.single_apply, hj] using hd.1 j
  refine ⟨?_, ?_, ?_⟩
  · have h := exercise_2_E_8_price hd hD l 0 hx
    have hlin : HasDerivAt (fun s => Real.log (x (p + (Real.exp s - p 0) • Pi.single 0 1) w l))
        a1 (Real.log (p 0)) := by
      have : (fun s => Real.log (x (p + (Real.exp s - p 0) • Pi.single 0 1) w l)) =
          fun s => a0 + a1 * s + a2 * Real.log (p 1) + γ * Real.log w := by
        funext s
        rw [hlog _ _ (hupd 0 s)]
        simp [Real.log_exp]
      rw [this]
      have := (((hasDerivAt_id (Real.log (p 0))).const_mul a1).const_add a0).add_const
        (a2 * Real.log (p 1) + γ * Real.log w)
      convert this using 1
      · funext s
        simp only [id]
        ring
      · simp
    exact h.unique hlin
  · have h := exercise_2_E_8_price hd hD l 1 hx
    have hlin : HasDerivAt (fun s => Real.log (x (p + (Real.exp s - p 1) • Pi.single 1 1) w l))
        a2 (Real.log (p 1)) := by
      have : (fun s => Real.log (x (p + (Real.exp s - p 1) • Pi.single 1 1) w l)) =
          fun s => a0 + a1 * Real.log (p 0) + a2 * s + γ * Real.log w := by
        funext s
        rw [hlog _ _ (hupd 1 s)]
        simp [Real.log_exp]
      rw [this]
      simpa using ((((hasDerivAt_id _).const_mul a2).const_add
        (a0 + a1 * Real.log (p 0))).add_const (γ * Real.log w))
    exact h.unique hlin
  · have h := exercise_2_E_8_wealth hd hD l hx
    have hlin : HasDerivAt (fun s => Real.log (x p (Real.exp s) l)) γ (Real.log w) := by
      have : (fun s => Real.log (x p (Real.exp s) l)) =
          fun s => a0 + a1 * Real.log (p 0) + a2 * Real.log (p 1) + γ * s := by
        funext s
        rw [hlog _ _ ⟨hd.1, Real.exp_pos s⟩, Real.log_exp]
      rw [this]
      simpa using ((hasDerivAt_id _).const_mul γ).const_add
        (a0 + a1 * Real.log (p 0) + a2 * Real.log (p 1))
    exact h.unique hlin

end MWG.ConsumerChoice

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The weak axiom of revealed preference and the compensated law of demand

MWG, Section 2.F, pp. 28–33.

* Definition 2.F.1 (the weak axiom for Walrasian demand functions) and Slutsky compensated
  price changes (p. 30).
* The fact used in the proof of Proposition 2.F.1(ii) (small type, pp. 31–32): with Walras'
  law, the weak axiom holds if and only if it holds for all compensated price changes.
* Proposition 2.F.1 (p. 30–31): with Walras' law, the weak axiom is equivalent to the
  compensated law of demand (2.F.1). Direction (i) uses only Walras' law; direction (ii) also
  uses that demand lies in `ℝ^L_+` (the book's consumption set). Homogeneity of degree zero,
  assumed in the book, is not needed.
* The own-price consequence (p. 32): a compensated rise in `p_ℓ` gives `Δx_ℓ ≤ 0`, with
  `Δx_ℓ < 0` when demand changes. The book's unqualified `Δx_ℓ < 0` fails when demand does not
  move: Leontief demand is a counterexample.
* Figure 2.F.4 (compensated price fall) and Figure 2.F.5 (the weak axiom does not give the law
  of demand for uncompensated changes: a two-observation witness).
-/

namespace MWG.ConsumerChoice

/-- **Definition 2.F.1** (MWG, p. 29). The weak axiom of revealed preference for a Walrasian
demand function: if `p·x(p', w') ≤ w` and `x(p', w') ≠ x(p, w)` then `p'·x(p, w) > w'`. -/
def WeakAxiom {L : ℕ} (x : DemandFunction L) : Prop :=
  ∀ p w p' w', PWDomain p w → PWDomain p' w' → p ⬝ᵥ x p' w' ≤ w → x p' w' ≠ x p w →
    w' < p' ⬝ᵥ x p w

/-- **Section 2.D–2.E** (MWG, pp. 21, 23). Demand takes values in the consumption set
`ℝ^L_+`. -/
def ValuesInOrthant {L : ℕ} (x : DemandFunction L) : Prop :=
  ∀ p w, PWDomain p w → x p w ∈ nonnegOrthant L

/-- **Section 2.F** (MWG, p. 30). Slutsky wealth compensation: the new wealth
`w' = p'·x(p, w)` that keeps the old bundle just affordable. -/
def compensatedWealth {L : ℕ} (x : DemandFunction L) (p : Fin L → ℝ) (w : ℝ)
    (p' : Fin L → ℝ) : ℝ :=
  p' ⬝ᵥ x p w

/-- **Proposition 2.F.1** (MWG, p. 31), property (2.F.1): the compensated law of demand. For
every compensated price change from `(p, w)` to `(p', p'·x(p, w))` in the domain,
`(p' - p)·[x(p', w') - x(p, w)] ≤ 0`, strictly when `x(p', w') ≠ x(p, w)`. -/
def CompensatedLawOfDemand {L : ℕ} (x : DemandFunction L) : Prop :=
  ∀ p w p', PWDomain p w → StrictlyPositive p' → 0 < compensatedWealth x p w p' →
    (p' - p) ⬝ᵥ (x p' (compensatedWealth x p w p') - x p w) ≤ 0 ∧
      (x p w ≠ x p' (compensatedWealth x p w p') →
        (p' - p) ⬝ᵥ (x p' (compensatedWealth x p w p') - x p w) < 0)

/-- With Walras' law and values in `ℝ^L_+`, compensated wealth is positive at any `p' ≫ 0`,
so every compensated price change stays in the domain. -/
theorem compensatedWealth_pos {L : ℕ} {x : DemandFunction L} (hW : WalrasLaw x)
    (hX : ValuesInOrthant x) {p : Fin L → ℝ} {w : ℝ} (hd : PWDomain p w) {p' : Fin L → ℝ}
    (hp' : StrictlyPositive p') : 0 < compensatedWealth x p w p' := by
  have hx := hX p w hd
  have hw := hW p w hd
  by_contra hneg
  push Not at hneg
  have hzero : ∀ l, x p w l = 0 := by
    have hsum : ∀ l ∈ Finset.univ, 0 ≤ p' l * x p w l :=
      fun l _ => mul_nonneg (hp' l).le (hx l)
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg hsum).mp
      (le_antisymm hneg (Finset.sum_nonneg hsum))
    intro l
    rcases mul_eq_zero.mp (h0 l (Finset.mem_univ l)) with h | h
    · exact absurd h (hp' l).ne'
    · exact h
  have : p ⬝ᵥ x p w = 0 := by simp [dotProduct, hzero]
  linarith [hd.2]

/-- **Section 2.F** (MWG, pp. 31–32, small type). With Walras' law (and demand in `ℝ^L_+`),
the weak axiom holds if and only if it holds for all compensated price changes: whenever
`p·x(p', w') = w` and `x(p', w') ≠ x(p, w)`, then `p'·x(p, w) > w'`. -/
theorem weakAxiom_iff_compensated {L : ℕ} {x : DemandFunction L} (hW : WalrasLaw x)
    (hX : ValuesInOrthant x) :
    WeakAxiom x ↔ ∀ p w p' w', PWDomain p w → PWDomain p' w' → p ⬝ᵥ x p' w' = w →
      x p' w' ≠ x p w → w' < p' ⬝ᵥ x p w := by
  constructor
  · intro h p w p' w' hd hd' heq hne
    exact h p w p' w' hd hd' heq.le hne
  · intro h p w p' w' hd hd' hle hne
    by_contra hcon
    push Not at hcon
    rcases eq_or_lt_of_le hle with heq | hlt
    · exact absurd (h p w p' w' hd hd' heq hne) (not_lt.mpr hcon)
    rcases eq_or_lt_of_le hcon with heq' | hlt'
    · have := h p' w' p w hd' hd heq' (Ne.symm hne)
      linarith
    -- both inequalities strict: interpolate the prices
    set xv := x p w
    set xv' := x p' w'
    have hWp : p ⬝ᵥ xv = w := hW p w hd
    have hWp' : p' ⬝ᵥ xv' = w' := hW p' w' hd'
    set a := p ⬝ᵥ (xv' - xv) with ha
    set b := p' ⬝ᵥ (xv' - xv) with hb
    have ha0 : a < 0 := by rw [ha, dotProduct_sub]; linarith
    have hb0 : 0 < b := by rw [hb, dotProduct_sub]; linarith
    set α := b / (b - a) with hα
    have hba : 0 < b - a := by linarith
    have hα0 : 0 < α := div_pos hb0 hba
    have hα1 : α < 1 := (div_lt_one hba).mpr (by linarith)
    set q := α • p + (1 - α) • p' with hq
    have hqpos : StrictlyPositive q := fun l => by
      simp only [hq, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have := hd.1 l
      have := hd'.1 l
      nlinarith
    have hqeq : q ⬝ᵥ xv' = q ⬝ᵥ xv := by
      have : q ⬝ᵥ (xv' - xv) = 0 := by
        rw [hq, add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul,
          ← ha, ← hb, hα]
        field_simp
        ring
      rw [dotProduct_sub, sub_eq_zero] at this
      exact this
    set wq := q ⬝ᵥ xv with hwq
    have hwq0 : 0 < wq := compensatedWealth_pos hW hX hd hqpos
    have hdq : PWDomain q wq := ⟨hqpos, hwq0⟩
    set xq := x q wq
    have hWq : q ⬝ᵥ xq = wq := hW q wq hdq
    have hsplit : α * (p ⬝ᵥ xq) + (1 - α) * (p' ⬝ᵥ xq) = wq := by
      rw [← hWq, hq, add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul]
    have hlt2 : wq < α * w + (1 - α) * w' := by
      have e : wq = α * (p ⬝ᵥ xv') + (1 - α) * (p' ⬝ᵥ xv') := by
        rw [← hqeq, hq, add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul,
          smul_eq_mul]
      rw [e]
      have h1 := mul_lt_mul_of_pos_left hlt hα0
      have h2 : (1 - α) * (p' ⬝ᵥ xv') = (1 - α) * w' := by rw [hWp']
      linarith
    by_cases hc : p ⬝ᵥ xq < w
    · -- compensated change from (q, wq) to (p, w), using x(p, w)
      have hne' : xq ≠ xv := by
        intro h'
        rw [h'] at hc
        linarith
      have := h q wq p w hdq hd hwq.symm (Ne.symm hne')
      linarith
    · push Not at hc
      have hc' : p' ⬝ᵥ xq < w' := by
        by_contra hc'
        push Not at hc'
        have := mul_le_mul_of_nonneg_left hc hα0.le
        have := mul_le_mul_of_nonneg_left hc' (by linarith : (0 : ℝ) ≤ 1 - α)
        linarith
      have hne' : xq ≠ xv' := by
        intro h'
        rw [h'] at hc'
        linarith
      have := h q wq p' w' hdq hd' (by rw [hqeq]) (Ne.symm hne')
      linarith

/-- **Proposition 2.F.1(i)** (MWG, p. 31). With Walras' law, the weak axiom implies the
compensated law of demand (2.F.1), strictly when demand changes. -/
theorem proposition_2_F_1_i {L : ℕ} {x : DemandFunction L} (hW : WalrasLaw x)
    (hWA : WeakAxiom x) : CompensatedLawOfDemand x := by
  intro p w p' hd hp' hw'
  set w' := compensatedWealth x p w p' with hw'def
  have hd' : PWDomain p' w' := ⟨hp', hw'⟩
  have h1 : p' ⬝ᵥ (x p' w' - x p w) = 0 := by
    rw [dotProduct_sub, hW p' w' hd', hw'def, compensatedWealth, sub_self]
  have hsplit : (p' - p) ⬝ᵥ (x p' w' - x p w) = -(p ⬝ᵥ (x p' w' - x p w)) := by
    rw [sub_dotProduct, h1, zero_sub]
  by_cases hne : x p w = x p' w'
  · refine ⟨by rw [hne, sub_self, dotProduct_zero], fun h => absurd hne h⟩
  · have hgt : w < p ⬝ᵥ x p' w' := by
      by_contra hle
      push Not at hle
      have := hWA p w p' w' hd hd' hle (Ne.symm hne)
      rw [hw'def, compensatedWealth] at this
      exact lt_irrefl _ this
    have hpos : 0 < p ⬝ᵥ (x p' w' - x p w) := by
      rw [dotProduct_sub, hW p w hd]
      linarith
    have hneg : (p' - p) ⬝ᵥ (x p' w' - x p w) < 0 := by rw [hsplit]; linarith
    exact ⟨hneg.le, fun _ => hneg⟩

/-- **Proposition 2.F.1(ii)** (MWG, pp. 31–32). With Walras' law and demand in `ℝ^L_+`, the
compensated law of demand (with its strict part) implies the weak axiom. -/
theorem proposition_2_F_1_ii {L : ℕ} {x : DemandFunction L} (hW : WalrasLaw x)
    (hX : ValuesInOrthant x) (hC : CompensatedLawOfDemand x) : WeakAxiom x := by
  rw [weakAxiom_iff_compensated hW hX]
  intro p w p' w' hd hd' heq hne
  by_contra hle
  push Not at hle
  -- compensated change from (p', w') to (p, p·x(p', w')) = (p, w)
  have hcw : compensatedWealth x p' w' p = w := heq
  have hpos : 0 < compensatedWealth x p' w' p := by rw [hcw]; exact hd.2
  obtain ⟨_, hstrict⟩ := hC p' w' p hd' hd.1 hpos
  rw [hcw] at hstrict
  have hlt := hstrict hne
  have e1 : p ⬝ᵥ (x p w - x p' w') = 0 := by rw [dotProduct_sub, hW p w hd, heq, sub_self]
  have e2 : 0 ≤ p' ⬝ᵥ (x p' w' - x p w) := by rw [dotProduct_sub, hW p' w' hd']; linarith
  have : (p - p') ⬝ᵥ (x p w - x p' w') = p' ⬝ᵥ (x p' w' - x p w) := by
    rw [sub_dotProduct, e1, zero_sub, ← neg_sub (x p' w') (x p w), dotProduct_neg, neg_neg]
  linarith

/-- **Proposition 2.F.1** (MWG, pp. 30–31). Suppose `x` satisfies Walras' law and takes values
in `ℝ^L_+`. Then `x` satisfies the weak axiom if and only if the compensated law of demand
(2.F.1) holds, strictly whenever demand changes. (The book also assumes homogeneity of degree
zero; it is not needed.) This is also summary conclusion (i) on p. 36. -/
theorem proposition_2_F_1 {L : ℕ} {x : DemandFunction L} (hW : WalrasLaw x)
    (hX : ValuesInOrthant x) : WeakAxiom x ↔ CompensatedLawOfDemand x :=
  ⟨proposition_2_F_1_i hW, proposition_2_F_1_ii hW hX⟩

/-- **Section 2.F** (MWG, p. 32), corrected. For a compensated change in the own price only,
`Δp = Δp_ℓ e_ℓ`, the weak axiom gives `Δp_ℓ Δx_ℓ ≤ 0`, strictly when demand changes. Hence
`Δp_ℓ > 0` implies `Δx_ℓ ≤ 0` (and `Δx_ℓ < 0` if `x(p', w') ≠ x(p, w)`). -/
theorem own_price_compensated_law {L : ℕ} {x : DemandFunction L} (hW : WalrasLaw x)
    (hWA : WeakAxiom x) {p : Fin L → ℝ} {w : ℝ} (hd : PWDomain p w) (l : Fin L) {δ : ℝ}
    (hp' : StrictlyPositive (p + Pi.single l δ))
    (hw' : 0 < compensatedWealth x p w (p + Pi.single l δ)) :
    δ * (x (p + Pi.single l δ) (compensatedWealth x p w (p + Pi.single l δ)) l - x p w l) ≤ 0 ∧
      (x p w ≠ x (p + Pi.single l δ) (compensatedWealth x p w (p + Pi.single l δ)) →
        δ * (x (p + Pi.single l δ) (compensatedWealth x p w (p + Pi.single l δ)) l -
          x p w l) < 0) := by
  obtain ⟨h1, h2⟩ := proposition_2_F_1_i hW hWA p w _ hd hp' hw'
  simp only [add_sub_cancel_left, single_dotProduct, Pi.sub_apply] at h1 h2
  exact ⟨h1, h2⟩

/-- **Figure 2.F.4** (MWG, p. 33). A compensated fall in the price of good `ℓ` cannot lower the
demand for good `ℓ`. -/
theorem figure_2_F_4 {L : ℕ} {x : DemandFunction L} (hW : WalrasLaw x) (hWA : WeakAxiom x)
    {p : Fin L → ℝ} {w : ℝ} (hd : PWDomain p w) (l : Fin L) {δ : ℝ} (hδ : δ < 0)
    (hp' : StrictlyPositive (p + Pi.single l δ))
    (hw' : 0 < compensatedWealth x p w (p + Pi.single l δ)) :
    x p w l ≤ x (p + Pi.single l δ) (compensatedWealth x p w (p + Pi.single l δ)) l := by
  have := (own_price_compensated_law hW hWA hd l hp' hw').1
  nlinarith

/-! ### The book's strict own-price claim fails without a change in demand -/

/-- Leontief demand for two goods, `x(p, w) = (w/(p₁+p₂), w/(p₁+p₂))`. -/
noncomputable def leontiefDemand : DemandFunction 2 := fun p w _ => w / (p 0 + p 1)

/-- Leontief demand satisfies Walras' law. -/
theorem leontiefDemand_walras : WalrasLaw leontiefDemand := by
  intro p w hd
  have : p 0 + p 1 ≠ 0 := by have := hd.1 0; have := hd.1 1; positivity
  simp only [leontiefDemand, dotProduct, Fin.sum_univ_two]
  field_simp

/-- Leontief demand is homogeneous of degree zero. -/
theorem leontiefDemand_homogeneous : HomogeneousZero leontiefDemand := by
  intro p w a hd ha
  have : p 0 + p 1 ≠ 0 := by have := hd.1 0; have := hd.1 1; positivity
  funext l
  simp only [leontiefDemand, Pi.smul_apply, smul_eq_mul]
  rw [← mul_add, mul_div_mul_left _ _ ha.ne']

/-- Leontief demand takes values in `ℝ²_+`. -/
theorem leontiefDemand_orthant : ValuesInOrthant leontiefDemand := by
  intro p w hd l
  have := hd.1 0
  have := hd.1 1
  exact div_nonneg hd.2.le (by positivity)

/-- Leontief demand satisfies the weak axiom. -/
theorem leontiefDemand_weakAxiom : WeakAxiom leontiefDemand := by
  intro p w p' w' hd hd' hle hne
  have hs : 0 < p 0 + p 1 := by have := hd.1 0; have := hd.1 1; positivity
  have hs' : 0 < p' 0 + p' 1 := by have := hd'.1 0; have := hd'.1 1; positivity
  simp only [leontiefDemand, dotProduct, Fin.sum_univ_two] at hle ⊢
  have hne' : w' / (p' 0 + p' 1) ≠ w / (p 0 + p 1) := by
    intro h
    apply hne
    funext l
    simp [leontiefDemand, h]
  have hle' : w' / (p' 0 + p' 1) ≤ w / (p 0 + p 1) := by
    rw [← add_mul, ← le_div_iff₀' hs] at hle
    exact hle
  have hlt := lt_of_le_of_ne hle' hne'
  rw [div_lt_div_iff₀ hs' hs] at hlt
  rw [← add_mul, mul_div_assoc', lt_div_iff₀ hs]
  linarith

/-- **Section 2.F** (MWG, p. 32), counterexample. The book states that a compensated rise in
the own price `p_ℓ` gives `Δx_ℓ < 0`. For Leontief demand (which satisfies the weak axiom,
Walras' law and homogeneity) at `p = (1, 1)`, `w = 2`, a compensated rise of `p₁` to 2 leaves
demand unchanged, so `Δx₁ = 0`. -/
theorem own_price_strict_counterexample :
    WeakAxiom leontiefDemand ∧ WalrasLaw leontiefDemand ∧ HomogeneousZero leontiefDemand ∧
      leontiefDemand (![1, 1] + Pi.single 0 1)
          (compensatedWealth leontiefDemand ![1, 1] 2 (![1, 1] + Pi.single 0 1)) 0 =
        leontiefDemand ![1, 1] 2 0 := by
  refine ⟨leontiefDemand_weakAxiom, leontiefDemand_walras, leontiefDemand_homogeneous, ?_⟩
  simp [leontiefDemand, compensatedWealth, dotProduct, Fin.sum_univ_two]
  norm_num

end MWG.ConsumerChoice

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The weak axiom: Figure 2.F.5 and Exercises 2.F.1, 2.F.6, 2.F.12–2.F.14

MWG, Section 2.F (p. 33) and Exercises 2.F.1, 2.F.6, 2.F.12, 2.F.13 and 2.F.14
(pp. 37–39).

MWG's choice structures and weak axiom (Definition 1.C.1) are imported from MWG Chapter 1
(`MWG.PreferenceChoice.ChoiceStructure`, `MWG.PreferenceChoice.WeakAxiom`); the Walrasian
budget family with the demand's choice rule is shown to be such a choice structure
(`walrasianChoiceStructure`, `walrasianCorrStructure`). Exercise 2.F.12
uses Kreps' rational preferences (`Kreps.ChoicePreferenceUtility.Rational`, complete and
transitive) and Kreps' set of best elements `PrefChoice`, which is MWG's `C*(B, ≿)`.
-/

namespace MWG.ConsumerChoice

/-- **Section 2.E** (MWG, p. 24). The choice rule of a demand function on Walrasian budgets:
`C(B) = {x(p, w) : B = B_{p,w}}`. -/
def walrasianChoiceRule {L : ℕ} (x : DemandFunction L) (B : Set (Fin L → ℝ)) :
    Set (Fin L → ℝ) :=
  {y | ∃ p w, PWDomain p w ∧ B = budgetSet p w ∧ y = x p w}

/-- The zero bundle lies in every Walrasian budget set with `w ≥ 0`. -/
theorem zero_mem_budgetSet {L : ℕ} {p : Fin L → ℝ} {w : ℝ} (hw : 0 ≤ w) :
    (0 : Fin L → ℝ) ∈ budgetSet p w :=
  ⟨fun _ => le_rfl, by simpa using hw⟩

/-- **Section 2.E** (MWG, p. 24). A Walrasian demand function with values in the budget sets
makes `(𝓑^W, x(·))` a choice structure in the sense of MWG Chapter 1. -/
def walrasianChoiceStructure {L : ℕ} (x : DemandFunction L)
    (hB : ∀ p w, PWDomain p w → x p w ∈ budgetSet p w) :
    MWG.PreferenceChoice.ChoiceStructure (Fin L → ℝ) :=
  ⟨walrasianBudgetFamily L, walrasianChoiceRule x,
    by rintro _ ⟨p, w, hd, rfl⟩; exact ⟨0, zero_mem_budgetSet hd.2.le⟩,
    by
      rintro _ ⟨p, w, hd, rfl⟩ y ⟨p', w', hd', hBB, rfl⟩
      rw [hBB]
      exact hB _ _ hd',
    by rintro _ ⟨p, w, hd, rfl⟩; exact ⟨x p w, p, w, hd, rfl, rfl⟩⟩

/-- Under homogeneity of degree zero, `C(B_{p,w}) = {x(p, w)}`. -/
theorem walrasianChoiceRule_budgetSet {L : ℕ} {x : DemandFunction L} (hH : HomogeneousZero x)
    {p : Fin L → ℝ} {w : ℝ} (hd : PWDomain p w) :
    walrasianChoiceRule x (budgetSet p w) = {x p w} := by
  ext y
  constructor
  · rintro ⟨p', w', hd', hB, rfl⟩
    exact Set.mem_singleton_iff.mpr (demand_depends_only_on_budget hH hd' hd hB.symm)
  · intro hy
    exact ⟨p, w, hd, rfl, hy⟩

/-- **Exercise 2.F.1** (MWG, p. 37). For a Walrasian demand function (values in `B_{p,w}`,
homogeneous of degree zero, so that `(𝓑^W, x(·))` is a choice structure), Definition 2.F.1
coincides with Definition 1.C.1. -/
theorem exercise_2_F_1 {L : ℕ} {x : DemandFunction L} (hH : HomogeneousZero x)
    (hB : ∀ p w, PWDomain p w → x p w ∈ budgetSet p w) :
    WeakAxiom x ↔ MWG.PreferenceChoice.WeakAxiom (walrasianChoiceStructure x hB) := by
  constructor
  · rintro hWA B ⟨p, w, hd, rfl⟩ B' ⟨p', w', hd', rfl⟩ a y _ hy ha ha' _ hy'
    change a ∈ walrasianChoiceRule x (budgetSet p w) at ha
    change y ∈ walrasianChoiceRule x (budgetSet p' w') at hy'
    change a ∈ walrasianChoiceRule x (budgetSet p' w')
    rw [walrasianChoiceRule_budgetSet hH hd] at ha
    rw [walrasianChoiceRule_budgetSet hH hd'] at hy' ⊢
    rw [Set.mem_singleton_iff] at ha hy' ⊢
    subst ha hy'
    by_contra hne
    have := hWA p w p' w' hd hd' hy.2 (Ne.symm hne)
    linarith [ha'.2]
  · intro hC p w p' w' hd hd' hle hne
    by_contra hcon
    push Not at hcon
    have hx := hB p w hd
    have hx' := hB p' w' hd'
    have hmem := hC (budgetSet p w) ⟨p, w, hd, rfl⟩ (budgetSet p' w') ⟨p', w', hd', rfl⟩
      (x p w) (x p' w') hx ⟨hx'.1, hle⟩
      (show x p w ∈ walrasianChoiceRule x (budgetSet p w) from ⟨p, w, hd, rfl, rfl⟩)
      ⟨hx.1, hcon⟩ hx'
      (show x p' w' ∈ walrasianChoiceRule x (budgetSet p' w') from ⟨p', w', hd', rfl, rfl⟩)
    change x p w ∈ walrasianChoiceRule x (budgetSet p' w') at hmem
    rw [walrasianChoiceRule_budgetSet hH hd', Set.mem_singleton_iff] at hmem
    exact hne hmem.symm

/-- **Exercise 2.F.6** (MWG, p. 38). For a demand function homogeneous of degree zero, the
weak axiom holds if and only if, for some `w > 0` and all `p, p' ≫ 0`, `p·x(p', w) ≤ w` and
`x(p', w) ≠ x(p, w)` imply `p'·x(p, w) > w`. -/
theorem exercise_2_F_6 {L : ℕ} {x : DemandFunction L} (hH : HomogeneousZero x) :
    WeakAxiom x ↔ ∃ w, 0 < w ∧ ∀ p p', StrictlyPositive p → StrictlyPositive p' →
      p ⬝ᵥ x p' w ≤ w → x p' w ≠ x p w → w < p' ⬝ᵥ x p w := by
  constructor
  · intro h
    exact ⟨1, one_pos, fun p p' hp hp' => h p 1 p' 1 ⟨hp, one_pos⟩ ⟨hp', one_pos⟩⟩
  · rintro ⟨v, hv, h⟩ p w p' w' hd hd' hle hne
    set a := v / w with ha
    set a' := v / w' with ha'
    have ha0 : 0 < a := div_pos hv hd.2
    have ha0' : 0 < a' := div_pos hv hd'.2
    have e : x (a • p) v = x p w := by
      have := hH p w a hd ha0
      rwa [ha, div_mul_cancel₀ _ hd.2.ne'] at this
    have e' : x (a' • p') v = x p' w' := by
      have := hH p' w' a' hd' ha0'
      rwa [ha', div_mul_cancel₀ _ hd'.2.ne'] at this
    have key := h (a • p) (a' • p') (pwDomain_smul hd ha0).1 (pwDomain_smul hd' ha0').1
      (by
        rw [e', smul_dotProduct, smul_eq_mul, ha]
        rw [div_mul_eq_mul_div, div_le_iff₀ hd.2]
        nlinarith)
      (by rw [e, e']; exact hne)
    rw [e, smul_dotProduct, smul_eq_mul, ha', div_mul_eq_mul_div, lt_div_iff₀ hd'.2] at key
    nlinarith

/-- **Exercise 2.F.12** (MWG, p. 38). A Walrasian demand function generated by a rational
preference relation `≿` (for every `(p, w)`, `x(p, w)` is the unique `≿`-best bundle of
`B_{p,w}`) satisfies the weak axiom. Kreps' `Rational` (complete and transitive) is MWG's
rationality, and Kreps' `PrefChoice` is MWG's `C*(B, ≿)`. -/
theorem exercise_2_F_12 {L : ℕ} {x : DemandFunction L}
    {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop} (hr : Kreps.ChoicePreferenceUtility.Rational r)
    (hgen : ∀ p w, PWDomain p w →
      Kreps.ChoicePreferenceUtility.PrefChoice r (budgetSet p w) = {x p w}) :
    WeakAxiom x := by
  intro p w p' w' hd hd' hle hne
  by_contra hcon
  push Not at hcon
  have hbest : x p w ∈ Kreps.ChoicePreferenceUtility.PrefChoice r (budgetSet p w) := by
    rw [hgen p w hd]; rfl
  have hbest' : x p' w' ∈ Kreps.ChoicePreferenceUtility.PrefChoice r (budgetSet p' w') := by
    rw [hgen p' w' hd']; rfl
  have hxB' : x p w ∈ budgetSet p' w' := ⟨hbest.1.1, hcon⟩
  have hx'B : x p' w' ∈ budgetSet p w := ⟨hbest'.1.1, hle⟩
  have h1 : r (x p w) (x p' w') := hbest.2 _ hx'B
  have hin : x p w ∈ Kreps.ChoicePreferenceUtility.PrefChoice r (budgetSet p' w') :=
    ⟨hxB', fun y hy => hr.2 _ _ _ h1 (hbest'.2 y hy)⟩
  rw [hgen p' w' hd', Set.mem_singleton_iff] at hin
  exact hne hin.symm

/-- **Exercise 2.F.14** (MWG, p. 39). A Walrasian demand function (values in `B_{p,w}`) that
satisfies the weak axiom is homogeneous of degree zero. -/
theorem exercise_2_F_14 {L : ℕ} {x : DemandFunction L} (hWA : WeakAxiom x)
    (hB : ∀ p w, PWDomain p w → x p w ∈ budgetSet p w) : HomogeneousZero x := by
  intro p w a hd ha
  have hd' := pwDomain_smul hd ha
  by_contra hne
  have hmem : x (a • p) (a * w) ∈ budgetSet p w := by
    rw [← budgetSet_smul p w ha]
    exact hB _ _ hd'
  have := hWA p w (a • p) (a * w) hd hd' hmem.2 hne
  rw [smul_dotProduct, smul_eq_mul] at this
  have hle := (hB p w hd).2
  nlinarith

/-! ### Exercise 2.F.13: multivalued demand -/

/-- **Exercise 2.F.13(a)** (MWG, p. 38). The weak axiom for Walrasian demand correspondences:
if `x ∈ x(p, w)`, `x' ∈ x(p', w')`, `x' ∈ B_{p,w}` and `x ∈ B_{p',w'}`, then
`x ∈ x(p', w')`. -/
def GeneralizedWeakAxiom {L : ℕ} (x : DemandCorrespondence L) : Prop :=
  ∀ p w p' w', PWDomain p w → PWDomain p' w' → ∀ y ∈ x p w, ∀ y' ∈ x p' w',
    y' ∈ budgetSet p w → y ∈ budgetSet p' w' → y ∈ x p' w'

/-- **Exercise 2.F.13(a)** (MWG, p. 38). A Walrasian demand correspondence with nonempty
values in the budget sets makes `(𝓑^W, x(·))` a choice structure (MWG Chapter 1). -/
def walrasianCorrStructure {L : ℕ} (x : DemandCorrespondence L)
    (hB : ∀ p w, PWDomain p w → x p w ⊆ budgetSet p w)
    (hne : ∀ p w, PWDomain p w → (x p w).Nonempty) :
    MWG.PreferenceChoice.ChoiceStructure (Fin L → ℝ) :=
  ⟨walrasianBudgetFamily L, fun B => {y | ∃ p w, PWDomain p w ∧ B = budgetSet p w ∧ y ∈ x p w},
    by rintro _ ⟨p, w, hd, rfl⟩; exact ⟨0, zero_mem_budgetSet hd.2.le⟩,
    by
      rintro _ ⟨p, w, hd, rfl⟩ y ⟨p', w', hd', hBB, hy⟩
      rw [hBB]
      exact hB _ _ hd' hy,
    by
      rintro _ ⟨p, w, hd, rfl⟩
      obtain ⟨y, hy⟩ := hne p w hd
      exact ⟨y, p, w, hd, rfl, hy⟩⟩

/-- **Exercise 2.F.13(a)** (MWG, p. 38). The generalisation is Definition 1.C.1 specialised to
Walrasian budgets: for a homogeneous correspondence with nonempty values in the budget sets,
with `C(B_{p,w}) = x(p, w)`. -/
theorem exercise_2_F_13a {L : ℕ} {x : DemandCorrespondence L} (hH : HomogeneousZeroCorr x)
    (hB : ∀ p w, PWDomain p w → x p w ⊆ budgetSet p w)
    (hne : ∀ p w, PWDomain p w → (x p w).Nonempty) :
    GeneralizedWeakAxiom x ↔ MWG.PreferenceChoice.WeakAxiom (walrasianCorrStructure x hB hne)
    := by
  have hC : ∀ p w, PWDomain p w →
      {y | ∃ p' w', PWDomain p' w' ∧ budgetSet p w = budgetSet p' w' ∧ y ∈ x p' w'} =
        x p w := by
    intro p w hd
    ext y
    constructor
    · rintro ⟨p', w', hd', hBB, hy⟩
      have hp := budgetSet_eq_imp_proportional hd hd' hBB
      have hw : w' = (w' / w) * w := by field_simp [hd.2.ne']
      have e : x p' w' = x p w := by
        calc x p' w' = x ((w' / w) • p) ((w' / w) * w) := by rw [← hp, ← hw]
          _ = x p w := hH p w _ hd (div_pos hd'.2 hd.2)
      rwa [e] at hy
    · intro hy
      exact ⟨p, w, hd, rfl, hy⟩
  constructor
  · rintro h B ⟨p, w, hd, rfl⟩ B' ⟨p', w', hd', rfl⟩ a y _ hy ha ha' _ hy'
    change a ∈ {y | ∃ p' w', PWDomain p' w' ∧ budgetSet p w = budgetSet p' w' ∧ y ∈ x p' w'}
      at ha
    change y ∈ {y | ∃ p'' w'', PWDomain p'' w'' ∧ budgetSet p' w' = budgetSet p'' w'' ∧
      y ∈ x p'' w''} at hy'
    change a ∈ {y | ∃ p'' w'', PWDomain p'' w'' ∧ budgetSet p' w' = budgetSet p'' w'' ∧
      y ∈ x p'' w''}
    rw [hC p w hd] at ha
    rw [hC p' w' hd'] at hy' ⊢
    exact h p w p' w' hd hd' a ha y hy' hy ha'
  · intro h p w p' w' hd hd' y hy y' hy' hy'B hyB
    have hres := h (budgetSet p w) ⟨p, w, hd, rfl⟩ (budgetSet p' w') ⟨p', w', hd', rfl⟩ y y'
      (hB p w hd hy) hy'B (show y ∈ {z | ∃ p'' w'', PWDomain p'' w'' ∧
        budgetSet p w = budgetSet p'' w'' ∧ z ∈ x p'' w''} from ⟨p, w, hd, rfl, hy⟩)
      hyB (hB p' w' hd' hy') (show y' ∈ {z | ∃ p'' w'', PWDomain p'' w'' ∧
        budgetSet p' w' = budgetSet p'' w'' ∧ z ∈ x p'' w''} from ⟨p', w', hd', rfl, hy'⟩)
    change y ∈ {z | ∃ p'' w'', PWDomain p'' w'' ∧
        budgetSet p' w' = budgetSet p'' w'' ∧ z ∈ x p'' w''} at hres
    rwa [hC p' w' hd'] at hres

/-- For a single-valued demand with values in `ℝ^L_+`, the generalised weak axiom of its
singleton correspondence is Definition 2.F.1. -/
theorem generalizedWeakAxiom_toCorrespondence_iff {L : ℕ} {x : DemandFunction L}
    (hX : ValuesInOrthant x) :
    GeneralizedWeakAxiom (toCorrespondence x) ↔ WeakAxiom x := by
  constructor
  · intro h p w p' w' hd hd' hle hne
    by_contra hcon
    push Not at hcon
    have := h p w p' w' hd hd' (x p w) rfl (x p' w') rfl ⟨hX p' w' hd', hle⟩ ⟨hX p w hd, hcon⟩
    exact hne (Set.mem_singleton_iff.mp this).symm
  · intro h p w p' w' hd hd' y hy y' hy' hy'B hyB
    simp only [toCorrespondence, Set.mem_singleton_iff] at hy hy' ⊢
    subst hy hy'
    by_contra hne
    have := h p w p' w' hd hd' hy'B.2 (Ne.symm hne)
    linarith [hyB.2]

/-- A nonnegative bundle with positive value at some prices has positive value at every
strictly positive price vector. -/
theorem dotProduct_pos_of_nonneg {L : ℕ} {y p p' : Fin L → ℝ} (hy : y ∈ nonnegOrthant L)
    (h : 0 < p ⬝ᵥ y) (hp' : StrictlyPositive p') : 0 < p' ⬝ᵥ y := by
  by_contra hneg
  push Not at hneg
  have hsum : ∀ l ∈ Finset.univ, 0 ≤ p' l * y l := fun l _ => mul_nonneg (hp' l).le (hy l)
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg hsum).mp
    (le_antisymm hneg (Finset.sum_nonneg hsum))
  have hz : ∀ l, y l = 0 := by
    intro l
    rcases mul_eq_zero.mp (h0 l (Finset.mem_univ l)) with h' | h'
    · exact absurd h' (hp' l).ne'
    · exact h'
  have : p ⬝ᵥ y = 0 := by simp [dotProduct, hz]
  linarith

/-- **Exercise 2.F.13(b)** (MWG, p. 38). The generalised weak axiom and Walras' law imply
property (*): for `y ∈ x(p, w)` and `y' ∈ x(p', w')`, if `p·y' < w` then `p'·y > w'`. -/
theorem exercise_2_F_13b {L : ℕ} {x : DemandCorrespondence L} (hG : GeneralizedWeakAxiom x)
    (hW : WalrasLawCorr x) (hB : ∀ p w, PWDomain p w → x p w ⊆ budgetSet p w) :
    ∀ p w p' w', PWDomain p w → PWDomain p' w' → ∀ y ∈ x p w, ∀ y' ∈ x p' w',
      p ⬝ᵥ y' < w → w' < p' ⬝ᵥ y := by
  intro p w p' w' hd hd' y hy y' hy' hlt
  by_contra hcon
  push Not at hcon
  have hmem := hG p' w' p w hd' hd y' hy' y hy ⟨(hB p w hd hy).1, hcon⟩
    ⟨(hB p' w' hd' hy').1, hlt.le⟩
  have := hW p w hd y' hmem
  linarith

/-- **Exercise 2.F.13(c)** (MWG, p. 39). The generalised compensated law of demand: from
`(p, w)` with `y ∈ x(p, w)`, for a compensated change to `(p', p'·y)`, every
`y' ∈ x(p', p'·y)` has `(p' - p)·(y' - y) ≤ 0`, strictly if `y' ∉ x(p, w)`. -/
def GeneralizedCompensatedLaw {L : ℕ} (x : DemandCorrespondence L) : Prop :=
  ∀ p w, PWDomain p w → ∀ y ∈ x p w, ∀ p', StrictlyPositive p' → 0 < p' ⬝ᵥ y →
    ∀ y' ∈ x p' (p' ⬝ᵥ y),
      (p' - p) ⬝ᵥ (y' - y) ≤ 0 ∧ (y' ∉ x p w → (p' - p) ⬝ᵥ (y' - y) < 0)

/-- **Exercise 2.F.13(c)** (MWG, p. 39). The generalised weak axiom and Walras' law imply the
generalised compensated law of demand. -/
theorem exercise_2_F_13c {L : ℕ} {x : DemandCorrespondence L} (hG : GeneralizedWeakAxiom x)
    (hW : WalrasLawCorr x) (hB : ∀ p w, PWDomain p w → x p w ⊆ budgetSet p w) :
    GeneralizedCompensatedLaw x := by
  intro p w hd y hy p' hp' hw' y' hy'
  set w' := p' ⬝ᵥ y with hw'def
  have hd' : PWDomain p' w' := ⟨hp', hw'⟩
  have hWy := hW p w hd y hy
  have hWy' := hW p' w' hd' y' hy'
  have hexp : (p' - p) ⬝ᵥ (y' - y) = w - p ⬝ᵥ y' := by
    rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, hWy, hWy', ← hw'def]
    ring
  have hge : w ≤ p ⬝ᵥ y' := by
    by_contra hlt
    push Not at hlt
    have := exercise_2_F_13b hG hW hB p w p' w' hd hd' y hy y' hy' hlt
    linarith
  refine ⟨by rw [hexp]; linarith, fun hnot => ?_⟩
  rw [hexp]
  rcases eq_or_lt_of_le hge with heq | hlt
  · exfalso
    apply hnot
    exact hG p' w' p w hd' hd y' hy' y hy ⟨(hB p w hd hy).1, le_of_eq hw'def.symm⟩
      ⟨(hB p' w' hd' hy').1, heq.symm.le⟩
  · linarith

/-- **Exercise 2.F.13(d)** (MWG, p. 39). Walras' law and the generalised compensated law of
demand imply the generalised weak axiom (for a demand correspondence with nonempty values in
the budget sets). -/
theorem exercise_2_F_13d {L : ℕ} {x : DemandCorrespondence L} (hW : WalrasLawCorr x)
    (hC : GeneralizedCompensatedLaw x) (hB : ∀ p w, PWDomain p w → x p w ⊆ budgetSet p w)
    (hne : ∀ p w, PWDomain p w → (x p w).Nonempty) : GeneralizedWeakAxiom x := by
  intro p w p' w' hd hd' y hy y' hy' hy'B hyB
  have hWy := hW p w hd y hy
  have hWy' := hW p' w' hd' y' hy'
  have hyO := (hB p w hd hy).1
  have hy'O := (hB p' w' hd' hy').1
  -- (p - p')·(y - y') = (w - p·y') + (w' - p'·y)
  have hsum : (p - p') ⬝ᵥ (y - y') = (w - p ⬝ᵥ y') + (w' - p' ⬝ᵥ y) := by
    rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, hWy, hWy']
    ring
  have hA := hy'B.2
  have hBn := hyB.2
  rcases eq_or_lt_of_le hBn with heq' | hlt'
  · -- the change to (p', w') is compensated for y
    have hpos : 0 < p' ⬝ᵥ y := by rw [heq']; exact hd'.2
    have hy'' : y' ∈ x p' (p' ⬝ᵥ y) := by rw [heq']; exact hy'
    obtain ⟨h1, _⟩ := hC p w hd y hy p' hd'.1 hpos y' hy''
    have e1 : (p' - p) ⬝ᵥ (y' - y) = w - p ⬝ᵥ y' := by
      rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, hWy, hWy', heq']
      ring
    have hpy' : p ⬝ᵥ y' = w := by linarith
    have hpos2 : 0 < p ⬝ᵥ y' := by rw [hpy']; exact hd.2
    have hy2 : y ∈ x p (p ⬝ᵥ y') := by rw [hpy']; exact hy
    obtain ⟨_, h2⟩ := hC p' w' hd' y' hy' p hd.1 hpos2 y hy2
    by_contra hnot
    have := h2 hnot
    rw [hsum, hpy', heq'] at this
    linarith
  · rcases eq_or_lt_of_le hA with heq | hlt
    · exfalso
      have hpos : 0 < p ⬝ᵥ y' := by rw [heq]; exact hd.2
      have hy2 : y ∈ x p (p ⬝ᵥ y') := by rw [heq]; exact hy
      obtain ⟨h1, _⟩ := hC p' w' hd' y' hy' p hd.1 hpos y hy2
      rw [hsum, heq] at h1
      linarith
    · exfalso
      set a := p ⬝ᵥ (y' - y) with ha
      set b := p' ⬝ᵥ (y' - y) with hb
      have ha0 : a < 0 := by rw [ha, dotProduct_sub]; linarith
      have hb0 : 0 < b := by rw [hb, dotProduct_sub]; linarith
      set α := b / (b - a) with hα
      have hba : 0 < b - a := by linarith
      have hα0 : 0 < α := div_pos hb0 hba
      have hα1 : α < 1 := (div_lt_one hba).mpr (by linarith)
      set q := α • p + (1 - α) • p' with hq
      have hqpos : StrictlyPositive q := fun l => by
        simp only [hq, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        have := hd.1 l
        have := hd'.1 l
        nlinarith
      have hqeq : q ⬝ᵥ y' = q ⬝ᵥ y := by
        have : q ⬝ᵥ (y' - y) = 0 := by
          rw [hq, add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul,
            ← ha, ← hb, hα]
          field_simp
          ring
        rw [dotProduct_sub, sub_eq_zero] at this
        exact this
      have hwq : 0 < q ⬝ᵥ y := dotProduct_pos_of_nonneg hyO (by rw [hWy]; exact hd.2) hqpos
      have hwq' : 0 < q ⬝ᵥ y' := by rw [hqeq]; exact hwq
      obtain ⟨yq, hyq⟩ := hne q (q ⬝ᵥ y) ⟨hqpos, hwq⟩
      have hyq' : yq ∈ x q (q ⬝ᵥ y') := by rw [hqeq]; exact hyq
      obtain ⟨c1, _⟩ := hC p w hd y hy q hqpos hwq yq hyq
      obtain ⟨c2, _⟩ := hC p' w' hd' y' hy' q hqpos hwq' yq hyq'
      have e1 : q - p = (1 - α) • (p' - p) := by
        rw [hq]; funext l; simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
        ring
      have e2 : q - p' = α • (p - p') := by
        rw [hq]; funext l; simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
        ring
      rw [e1, smul_dotProduct, smul_eq_mul] at c1
      rw [e2, smul_dotProduct, smul_eq_mul] at c2
      have d1 : (p' - p) ⬝ᵥ (yq - y) ≤ 0 := by
        by_contra hc; push Not at hc; nlinarith
      have d2 : (p - p') ⬝ᵥ (yq - y') ≤ 0 := by
        by_contra hc; push Not at hc; nlinarith
      have e3 : (p' - p) ⬝ᵥ (y' - y) = b - a := by
        rw [ha, hb, sub_dotProduct]
      have e4 : (p' - p) ⬝ᵥ (y' - y) = (p' - p) ⬝ᵥ (yq - y) + (p - p') ⬝ᵥ (yq - y') := by
        have : (p - p') = -(p' - p) := by rw [neg_sub]
        rw [this, neg_dotProduct, dotProduct_sub, dotProduct_sub, dotProduct_sub]
        ring
      linarith

end MWG.ConsumerChoice

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

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

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Negative and positive (semi)definite matrices

MWG, Mathematical Appendix, Definition M.D.1 (p. 935), and footnote 11 of Chapter 2 (p. 34):
definiteness does not presuppose symmetry. A real square matrix `M` is negative semidefinite
if `z·Mz ≤ 0` for all `z`, negative definite if `z·Mz < 0` for all `z ≠ 0`, and positive
(semi)definite with the inequalities reversed. `M` is positive (semi)definite iff `-M` is
negative (semi)definite (p. 935). For symmetric matrices the notions agree with Mathlib's
`Matrix.PosDef` and `Matrix.PosSemidef` (bridges below).
-/

namespace MWG.ConsumerChoice

variable {n : Type*} [Fintype n]

/-- **Definition M.D.1** (MWG, p. 935). `M` is negative semidefinite: `z·Mz ≤ 0` for all `z`.
-/
def NegSemidef (M : Matrix n n ℝ) : Prop := ∀ z : n → ℝ, z ⬝ᵥ M.mulVec z ≤ 0

/-- **Definition M.D.1** (MWG, p. 935). `M` is negative definite: `z·Mz < 0` for all `z ≠ 0`.
-/
def NegDef (M : Matrix n n ℝ) : Prop := ∀ z : n → ℝ, z ≠ 0 → z ⬝ᵥ M.mulVec z < 0

/-- **Definition M.D.1** (MWG, p. 935). `M` is positive semidefinite: `z·Mz ≥ 0` for all `z`.
-/
def PosSemidefMWG (M : Matrix n n ℝ) : Prop := ∀ z : n → ℝ, 0 ≤ z ⬝ᵥ M.mulVec z

/-- **Definition M.D.1** (MWG, p. 935). `M` is positive definite: `z·Mz > 0` for all `z ≠ 0`.
-/
def PosDefMWG (M : Matrix n n ℝ) : Prop := ∀ z : n → ℝ, z ≠ 0 → 0 < z ⬝ᵥ M.mulVec z

/-- **Section M.D** (MWG, p. 935). `M` is positive semidefinite iff `-M` is negative
semidefinite. -/
theorem posSemidefMWG_iff_neg (M : Matrix n n ℝ) : PosSemidefMWG M ↔ NegSemidef (-M) := by
  simp only [PosSemidefMWG, NegSemidef, Matrix.neg_mulVec, dotProduct_neg, neg_nonpos]

/-- **Section M.D** (MWG, p. 935). `M` is positive definite iff `-M` is negative definite. -/
theorem posDefMWG_iff_neg (M : Matrix n n ℝ) : PosDefMWG M ↔ NegDef (-M) := by
  simp only [PosDefMWG, NegDef, Matrix.neg_mulVec, dotProduct_neg, neg_neg_iff_pos]

/-- Negative definite matrices are negative semidefinite. -/
theorem NegDef.negSemidef {M : Matrix n n ℝ} (h : NegDef M) : NegSemidef M := by
  intro z
  by_cases hz : z = 0
  · simp [hz]
  · exact (h z hz).le

/-- Bridge to Mathlib: a symmetric matrix is positive semidefinite in MWG's sense iff it is
`Matrix.PosSemidef`. -/
theorem posSemidefMWG_iff_posSemidef {M : Matrix n n ℝ} (hM : M.IsSymm) :
    PosSemidefMWG M ↔ M.PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  have hH : M.IsHermitian := by simpa [Matrix.IsHermitian] using hM.eq
  simp only [PosSemidefMWG, star_trivial]
  exact ⟨fun h => ⟨hH, h⟩, fun h => h.2⟩

/-- Bridge to Mathlib: a symmetric matrix is positive definite in MWG's sense iff it is
`Matrix.PosDef`. -/
theorem posDefMWG_iff_posDef {M : Matrix n n ℝ} (hM : M.IsSymm) :
    PosDefMWG M ↔ M.PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  have hH : M.IsHermitian := by simpa [Matrix.IsHermitian] using hM.eq
  simp only [PosDefMWG, star_trivial]
  exact ⟨fun h => ⟨hH, h⟩, fun h => h.2⟩

end MWG.ConsumerChoice

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The Slutsky substitution matrix

MWG, Section 2.F, pp. 33–35, and Exercises 2.F.5, 2.F.7, 2.F.8, 2.F.9(b) and 2.F.11
(pp. 38–39).

* The Slutsky matrix `S(p, w)` with entries
  `s_ℓk = ∂x_ℓ/∂p_k + (∂x_ℓ/∂w) x_k` (2.F.10); `S v = D(v, v·x)` is the derivative of demand
  along a compensated price path (2.F.6)–(2.F.8).
* Proposition 2.F.2: under Walras' law and the weak axiom, `S(p, w)` is negative
  semidefinite. The book's differential argument ((2.F.5)–(2.F.9)) is made rigorous with the
  compensated path `t ↦ (p + t v, p·x(p,w) + t v·x(p, w))` and one-sided difference quotients.
  Homogeneity, assumed in the book, is not used. Consequences: `s_ℓℓ ≤ 0`, and a Giffen good
  is inferior (p. 34).
* Proposition 2.F.3 (= Exercise 2.F.7): `p·S(p, w) = 0` and `S(p, w) p = 0`; hence `S` is
  singular and not negative definite (p. 35).
* Exercise 2.F.11 and the remark on p. 34: for `L = 2` the Slutsky matrix is symmetric.
* Exercise 2.F.9(b): for `L = 2` and `S` of rank 1, negative semidefiniteness is equivalent to
  a negative diagonal entry.
* Exercise 2.F.5: homogeneity of degree one in wealth gives the law of demand for
  uncompensated price changes (both the finite and the infinitesimal versions).
* Exercise 2.F.8: substitution terms in elasticity form.
-/

namespace MWG.ConsumerChoice

open Filter Topology

/-- **Section 2.F** (MWG, p. 34), equation (2.F.10). The Slutsky (substitution) matrix
`s_ℓk = ∂x_ℓ/∂p_k + (∂x_ℓ/∂w) x_k`, from a derivative `D` and the bundle `x(p, w)`. -/
def slutskyMatrix {L : ℕ} (D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)) (xv : Fin L → ℝ) :
    Matrix (Fin L) (Fin L) ℝ :=
  Matrix.of fun l k => priceEffect D l k + wealthEffect D l * xv k

/-- Equation (2.F.8) (MWG, p. 33): `S = D_p x + D_w x xᵀ`. -/
theorem slutskyMatrix_eq {L : ℕ} (D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)) (xv : Fin L → ℝ) :
    slutskyMatrix D xv = priceJacobian D + Matrix.vecMulVec (wealthJacobian D) xv := by
  ext l k
  simp [slutskyMatrix, priceJacobian, wealthJacobian, Matrix.vecMulVec]

/-- Equations (2.F.6)–(2.F.8) (MWG, p. 33): `S v = D(v, v·x)`, the derivative of demand in the
compensated direction `dp = v`, `dw = x·dp`. -/
theorem slutskyMatrix_mulVec {L : ℕ} (D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ))
    (xv v : Fin L → ℝ) : Matrix.mulVec (slutskyMatrix D xv) v = D (v, v ⬝ᵥ xv) := by
  funext l
  rw [deriv_apply_eq]
  simp only [Matrix.mulVec, dotProduct, slutskyMatrix, Matrix.of_apply]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- A real function with derivative `g'` at `0` that does not exceed `g 0` immediately to the
right of `0` has `g' ≤ 0`. -/
theorem hasDerivAt_nonpos_of_right_le {g : ℝ → ℝ} {g' : ℝ} (hg : HasDerivAt g g' 0)
    (h : ∀ᶠ t in 𝓝[>] (0 : ℝ), g t ≤ g 0) : g' ≤ 0 := by
  have hs := hasDerivAt_iff_tendsto_slope.mp hg
  have hs' : Tendsto (slope g 0) (𝓝[>] 0) (𝓝 g') :=
    hs.mono_left (nhdsWithin_mono _ fun t ht => ne_of_gt ht)
  apply le_of_tendsto hs'
  filter_upwards [h, self_mem_nhdsWithin] with t ht htpos
  rw [slope_def_field]
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by simp only [sub_zero]; exact htpos.le)

/-- **Proposition 2.F.2** (MWG, p. 34). If a differentiable Walrasian demand function satisfies
Walras' law and the weak axiom, then at any `(p, w)` the Slutsky matrix is negative
semidefinite: `v·S(p, w) v ≤ 0` for all `v ∈ ℝ^L`. (The book also assumes homogeneity of
degree zero; it is not needed.) -/
theorem proposition_2_F_2 {L : ℕ} {x : DemandFunction L} (hW : WalrasLaw x)
    (hWA : WeakAxiom x) {p : Fin L → ℝ} {w : ℝ} (hd : PWDomain p w)
    {D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)} (hD : HasFDerivAt (Function.uncurry x) D (p, w))
    (v : Fin L → ℝ) : v ⬝ᵥ Matrix.mulVec (slutskyMatrix D (x p w)) v ≤ 0 := by
  rw [slutskyMatrix_mulVec]
  set c := v ⬝ᵥ x p w with hc
  have hpath := hasDerivAt_path hD v c
  have hg : HasDerivAt (fun t : ℝ => v ⬝ᵥ x (p + t • v) (w + t * c)) (v ⬝ᵥ D (v, c)) 0 := by
    have := HasDerivAt.fun_sum (u := Finset.univ) (fun l _ =>
      (hasDerivAt_pi.mp hpath l).const_mul (v l))
    simpa [dotProduct] using this
  apply hasDerivAt_nonpos_of_right_le hg
  have hdom := eventually_pwDomain hd v c
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds hdom, self_mem_nhdsWithin]
    with t ht htpos
  have hpt : StrictlyPositive (p + t • v) := ht.1
  have hcw : compensatedWealth x p w (p + t • v) = w + t * c := by
    simp only [compensatedWealth, add_dotProduct, smul_dotProduct, smul_eq_mul, hW p w hd, hc]
  obtain ⟨hle, _⟩ := proposition_2_F_1_i hW hWA p w (p + t • v) hd hpt (by rw [hcw]; exact ht.2)
  rw [hcw, add_sub_cancel_left, smul_dotProduct, smul_eq_mul] at hle
  have hle' : v ⬝ᵥ (x (p + t • v) (w + t * c) - x p w) ≤ 0 := by
    by_contra hcon
    push Not at hcon
    have := mul_pos (show (0 : ℝ) < t from htpos) hcon
    linarith
  simp only [zero_smul, add_zero, zero_mul]
  rw [dotProduct_sub, sub_nonpos] at hle'
  exact hle'

/-- **Section 2.F** (MWG, p. 34). Under the hypotheses of Proposition 2.F.2, the substitution
effect of good `ℓ` with respect to its own price is nonpositive: `s_ℓℓ(p, w) ≤ 0`. -/
theorem slutsky_diag_nonpos {L : ℕ} {x : DemandFunction L} (hW : WalrasLaw x)
    (hWA : WeakAxiom x) {p : Fin L → ℝ} {w : ℝ} (hd : PWDomain p w)
    {D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)} (hD : HasFDerivAt (Function.uncurry x) D (p, w))
    (l : Fin L) : slutskyMatrix D (x p w) l l ≤ 0 := by
  have h := proposition_2_F_2 hW hWA hd hD (Pi.single l 1)
  simpa [Matrix.mulVec_single, single_dotProduct] using h

/-- **Section 2.F** (MWG, p. 34). A good can be a Giffen good at `(p, w)` only if it is
inferior there: if `∂x_ℓ/∂p_ℓ > 0` then `∂x_ℓ/∂w < 0` (demand in `ℝ^L_+`). -/
theorem giffen_imp_inferior {L : ℕ} {x : DemandFunction L} (hW : WalrasLaw x)
    (hWA : WeakAxiom x) (hX : ValuesInOrthant x) {p : Fin L → ℝ} {w : ℝ} (hd : PWDomain p w)
    {D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)} (hD : HasFDerivAt (Function.uncurry x) D (p, w))
    (l : Fin L) (hG : 0 < priceEffect D l l) : wealthEffect D l < 0 := by
  have h := slutsky_diag_nonpos hW hWA hd hD l
  simp only [slutskyMatrix, Matrix.of_apply] at h
  have hx := hX p w hd l
  by_contra hcon
  push Not at hcon
  nlinarith [mul_nonneg hcon hx]

/-- **Proposition 2.F.3** (MWG, p. 35). If a differentiable demand function is homogeneous of
degree zero and satisfies Walras' law, then `p·S(p, w) = 0` and `S(p, w) p = 0`. -/
theorem proposition_2_F_3 {L : ℕ} {x : DemandFunction L} (hH : HomogeneousZero x)
    (hW : WalrasLaw x) {p : Fin L → ℝ} {w : ℝ} (hd : PWDomain p w)
    {D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)} (hD : HasFDerivAt (Function.uncurry x) D (p, w)) :
    Matrix.vecMul p (slutskyMatrix D (x p w)) = 0 ∧
      Matrix.mulVec (slutskyMatrix D (x p w)) p = 0 := by
  constructor
  · funext k
    have h2 := proposition_2_E_2 hW hd hD k
    have h3 := proposition_2_E_3 hW hd hD
    simp only [Matrix.vecMul, dotProduct, slutskyMatrix, Matrix.of_apply, Pi.zero_apply,
      mul_add, Finset.sum_add_distrib]
    have : ∑ l, p l * (wealthEffect D l * x p w k) =
        (∑ l, p l * wealthEffect D l) * x p w k := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun l _ => by ring
    rw [this, h3, one_mul]
    linarith
  · rw [slutskyMatrix_mulVec, hW p w hd, homogeneous_deriv_identity hH hd hD]

/-- **Exercise 2.F.7** (MWG, p. 35): proof of Proposition 2.F.3 from Propositions 2.E.1–2.E.3.
-/
theorem exercise_2_F_7 {L : ℕ} {x : DemandFunction L} (hH : HomogeneousZero x)
    (hW : WalrasLaw x) {p : Fin L → ℝ} {w : ℝ} (hd : PWDomain p w)
    {D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)} (hD : HasFDerivAt (Function.uncurry x) D (p, w)) :
    Matrix.vecMul p (slutskyMatrix D (x p w)) = 0 ∧
      Matrix.mulVec (slutskyMatrix D (x p w)) p = 0 :=
  proposition_2_F_3 hH hW hd hD

/-- **Section 2.F** (MWG, p. 35). Under the hypotheses of Proposition 2.F.3 (with at least one
good), `S(p, w)` is singular. -/
theorem slutsky_det_eq_zero {L : ℕ} {x : DemandFunction L} (hH : HomogeneousZero x)
    (hW : WalrasLaw x) {p : Fin L → ℝ} {w : ℝ} (hd : PWDomain p w)
    {D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)} (hD : HasFDerivAt (Function.uncurry x) D (p, w))
    (l : Fin L) : (slutskyMatrix D (x p w)).det = 0 := by
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨p, fun h => ?_, (proposition_2_F_3 hH hW hd hD).2⟩
  have := hd.1 l
  rw [h] at this
  exact lt_irrefl _ this

/-- **Section 2.F** (MWG, p. 35). Under the hypotheses of Proposition 2.F.3 (with at least one
good), `S(p, w)` is not negative definite: `p·S(p, w) p = 0` with `p ≠ 0`. -/
theorem slutsky_not_negDef {L : ℕ} {x : DemandFunction L} (hH : HomogeneousZero x)
    (hW : WalrasLaw x) {p : Fin L → ℝ} {w : ℝ} (hd : PWDomain p w)
    {D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)} (hD : HasFDerivAt (Function.uncurry x) D (p, w))
    (l : Fin L) : ¬ NegDef (slutskyMatrix D (x p w)) := by
  intro h
  have hp : p ≠ 0 := fun h0 => by have := hd.1 l; rw [h0] at this; exact lt_irrefl _ this
  have := h p hp
  rw [(proposition_2_F_3 hH hW hd hD).2, dotProduct_zero] at this
  exact lt_irrefl _ this

/-- **Exercise 2.F.11** (MWG, p. 38), matrix form. A `2 × 2` matrix with `S p = 0` and
`p·S = 0` for some `p` with `p₂ ≠ 0` is symmetric. -/
theorem symmetric_of_two_by_two {S : Matrix (Fin 2) (Fin 2) ℝ} {p : Fin 2 → ℝ} (hp : p 1 ≠ 0)
    (h1 : Matrix.vecMul p S = 0) (h2 : Matrix.mulVec S p = 0) : S.IsSymm := by
  have a := congrFun h1 0
  have b := congrFun h2 0
  simp only [Matrix.vecMul, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.zero_apply] at a b
  have h01 : S 0 1 = S 1 0 := by
    have : p 1 * (S 0 1 - S 1 0) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hp
    · linarith
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply, h01]

/-- **Exercise 2.F.11** (MWG, p. 38) and the remark on p. 34. For `L = 2`, under the
hypotheses of Proposition 2.F.3, `S(p, w)` is symmetric. -/
theorem exercise_2_F_11 {x : DemandFunction 2} (hH : HomogeneousZero x) (hW : WalrasLaw x)
    {p : Fin 2 → ℝ} {w : ℝ} (hd : PWDomain p w) {D : ((Fin 2 → ℝ) × ℝ) →L[ℝ] (Fin 2 → ℝ)}
    (hD : HasFDerivAt (Function.uncurry x) D (p, w)) : (slutskyMatrix D (x p w)).IsSymm :=
  symmetric_of_two_by_two (hd.1 1).ne' (proposition_2_F_3 hH hW hd hD).1
    (proposition_2_F_3 hH hW hd hD).2

/-- **Exercise 2.F.9(b)** (MWG, p. 38). For `L = 2`, a matrix `S` with `S p = 0` and `p·S = 0`
for some `p ≫ 0` (as the Slutsky matrix, by Proposition 2.F.3) and of rank 1 is negative
semidefinite iff any diagonal entry is negative. -/
theorem exercise_2_F_9b {S : Matrix (Fin 2) (Fin 2) ℝ} {p : Fin 2 → ℝ}
    (hp : StrictlyPositive p) (h1 : Matrix.vecMul p S = 0) (h2 : Matrix.mulVec S p = 0)
    (hrank : S.rank = 1) :
    (NegSemidef S ↔ S 0 0 < 0) ∧ (NegSemidef S ↔ S 1 1 < 0) := by
  have hp0 := hp 0
  have hp1 := hp 1
  have a0 := congrFun h1 0
  have a1 := congrFun h1 1
  have b0 := congrFun h2 0
  have b1 := congrFun h2 1
  simp only [Matrix.vecMul, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.zero_apply]
    at a0 a1 b0 b1
  -- all entries are determined by `S 0 0`
  have e01 : S 0 1 = -(p 0 / p 1) * S 0 0 := by field_simp; linarith
  have e10 : S 1 0 = -(p 0 / p 1) * S 0 0 := by field_simp; linarith
  have e11 : S 1 1 = (p 0 / p 1) ^ 2 * S 0 0 := by
    field_simp
    have : p 1 * S 1 1 = -(p 0 * S 1 0) := by linarith
    rw [e10] at this
    field_simp at this
    nlinarith
  have hS0 : S 0 0 ≠ 0 := by
    intro h0
    have hz : S = 0 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h0, e01, e10, e11]
    rw [hz, Matrix.rank_zero] at hrank
    exact zero_ne_one hrank
  have hq : ∀ z : Fin 2 → ℝ, z ⬝ᵥ S.mulVec z = S 0 0 * (z 0 - (p 0 / p 1) * z 1) ^ 2 := by
    intro z
    simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_two, e01, e10, e11]
    ring
  have hns : NegSemidef S ↔ S 0 0 < 0 := by
    constructor
    · intro h
      have := h ![1, 0]
      have e : ((![1, 0] : Fin 2 → ℝ) 0 - p 0 / p 1 * (![1, 0] : Fin 2 → ℝ) 1) ^ 2 = 1 := by
        simp
      rw [hq, e, mul_one] at this
      exact lt_of_le_of_ne this hS0
    · intro h z
      rw [hq]
      exact mul_nonpos_of_nonpos_of_nonneg h.le (sq_nonneg _)
  refine ⟨hns, hns.trans ?_⟩
  rw [e11]
  have : 0 < (p 0 / p 1) ^ 2 := by positivity
  constructor
  · intro h; nlinarith
  · intro h
    by_contra hc
    push Not at hc
    nlinarith

/-- **Exercise 2.F.8** (MWG, p. 38). Substitution terms in elasticity form:
`s̃_ℓk = (p_k/x_ℓ) s_ℓk = ε_ℓk + ε_ℓw b_k`. -/
theorem exercise_2_F_8 {L : ℕ} (D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)) (p xv : Fin L → ℝ)
    {w : ℝ} (hw : w ≠ 0) (l k : Fin L) :
    p k / xv l * slutskyMatrix D xv l k =
      priceElasticity D p xv l k + wealthElasticity D w xv l * budgetShare p xv w k := by
  simp only [slutskyMatrix, Matrix.of_apply, priceElasticity, wealthElasticity, budgetShare]
  field_simp

/-- **Exercise 2.F.5** (MWG, p. 38). If a demand function satisfying the weak axiom, Walras'
law (with values in `ℝ^L_+`) is homogeneous of degree one in wealth, then the law of demand
holds for uncompensated price changes: `(p' - p)·[x(p', w) - x(p, w)] ≤ 0`. -/
theorem exercise_2_F_5 {L : ℕ} {x : DemandFunction L} (hW : WalrasLaw x) (hWA : WeakAxiom x)
    (hX : ValuesInOrthant x) (h1 : HomogeneousOneInWealth x) {p p' : Fin L → ℝ} {w : ℝ}
    (hd : PWDomain p w) (hp' : StrictlyPositive p') :
    (p' - p) ⬝ᵥ (x p' w - x p w) ≤ 0 := by
  have hw := hd.2
  have hd' : PWDomain p' w := ⟨hp', hw⟩
  have hcw : 0 < compensatedWealth x p w p' := compensatedWealth_pos hW hX hd hp'
  set a := compensatedWealth x p w p' / w with ha
  have ha0 : 0 < a := div_pos hcw hw
  have hcwa : compensatedWealth x p w p' = a * w := by rw [ha]; field_simp
  obtain ⟨hc, _⟩ := proposition_2_F_1_i hW hWA p w p' hd hp' hcw
  rw [hcwa, h1 p' w a hd' ha0] at hc
  have hWp := hW p w hd
  have hWp' := hW p' w hd'
  set b := p ⬝ᵥ x p' w / w with hb
  have hpx' : p ⬝ᵥ x p' w = b * w := by rw [hb]; field_simp
  have hp'x : p' ⬝ᵥ x p w = a * w := hcwa
  -- the compensated law gives `1 ≤ a b`
  have hab : w * (1 - a * b) ≤ 0 := by
    have : (p' - p) ⬝ᵥ (a • x p' w - x p w) = w * (1 - a * b) := by
      rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, dotProduct_smul, dotProduct_smul,
        smul_eq_mul, smul_eq_mul, hWp', hp'x, hpx', hWp]
      ring
    linarith
  have hab' : 1 ≤ a * b := by nlinarith
  have hb0 : 0 < b := by
    by_contra hb0
    push Not at hb0
    nlinarith
  have hexp : (p' - p) ⬝ᵥ (x p' w - x p w) = w * (2 - a - b) := by
    rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, hWp', hp'x, hpx', hWp]
    ring
  rw [hexp]
  have : 2 ≤ a + b := by nlinarith [sq_nonneg (a - b)]
  nlinarith

/-- **Exercise 2.F.5** (MWG, p. 38), infinitesimal version: under the same hypotheses and
differentiability, `dp·D_p x(p, w) dp ≤ 0` for every `dp`. -/
theorem exercise_2_F_5_infinitesimal {L : ℕ} {x : DemandFunction L} (hW : WalrasLaw x)
    (hWA : WeakAxiom x) (h1 : HomogeneousOneInWealth x) {p : Fin L → ℝ} {w : ℝ}
    (hd : PWDomain p w) {D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)}
    (hD : HasFDerivAt (Function.uncurry x) D (p, w)) (v : Fin L → ℝ) :
    v ⬝ᵥ Matrix.mulVec (priceJacobian D) v ≤ 0 := by
  have hS := proposition_2_F_2 hW hWA hd hD v
  have hDw := exercise_2_E_4_wealthJacobian h1 hd hD
  rw [slutskyMatrix_mulVec, deriv_apply_eq_mulVec, dotProduct_add, dotProduct_smul, hDw,
    dotProduct_smul, smul_eq_mul, smul_eq_mul] at hS
  have hw := hd.2
  have : 0 ≤ (v ⬝ᵥ x p w) * (w⁻¹ * (v ⬝ᵥ x p w)) := by
    rw [mul_left_comm]
    exact mul_nonneg (inv_nonneg.mpr hw.le) (mul_self_nonneg _)
  linarith

end MWG.ConsumerChoice

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Slutsky matrices of explicit demand functions

MWG, Exercises 2.F.10, 2.F.15, 2.F.16 and 2.F.17 (pp. 38–39).

The Slutsky matrix is computed from its characterisation `S v = D(v, v·x)` as the derivative
of demand along the compensated path `t ↦ (p + t v, w + t v·x(p, w))`
(`slutsky_mulVec_of_hasDerivAt`), which only needs one-variable derivatives.

* Exercise 2.F.10: the demand of Exercise 2.E.1 with `β = 1`; at `p = (1,1,1)`, `w = 1`, the
  Slutsky matrix is `(1/3)[[-1,1,0],[0,-1,1],[1,0,-1]]`, negative semidefinite but not
  symmetric; at `p = (1, 1, ε)` with `0 < ε < 1/22` it is not negative semidefinite, so the
  demand violates the weak axiom (Proposition 2.F.2).
* Exercise 2.F.15 (consumption set `ℝ³`): the demand is determined by the stated data; it
  satisfies the weak axiom (proved directly), `v·S v < 0` for `v` not proportional to `p`, and
  `S` is not symmetric.
* Exercise 2.F.16 (consumption set `ℝ³`): homogeneous, Walras' law, violates the weak axiom,
  and `v·S v = 0` for all `v`.
* Exercise 2.F.17: `x_k = w / ∑ p_ℓ` is homogeneous, satisfies Walras' law and the weak axiom,
  and its Slutsky matrix is zero: negative semidefinite, symmetric, not negative definite.
-/

namespace MWG.ConsumerChoice

/-- The Slutsky matrix applied to `v` is the derivative of demand along the compensated path;
it can be read off from one-variable derivatives of the components. -/
theorem slutsky_mulVec_of_hasDerivAt {L : ℕ} {x : DemandFunction L} {p : Fin L → ℝ} {w : ℝ}
    {D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)} (hD : HasFDerivAt (Function.uncurry x) D (p, w))
    (v d : Fin L → ℝ)
    (h : ∀ l, HasDerivAt (fun t : ℝ => x (p + t • v) (w + t * (v ⬝ᵥ x p w)) l) (d l) 0) :
    Matrix.mulVec (slutskyMatrix D (x p w)) v = d := by
  rw [slutskyMatrix_mulVec]
  funext l
  exact (hasDerivAt_path_apply hD v _ l).unique (h l)

/-- An affine function of `t` has derivative its slope. -/
theorem hasDerivAt_affine (a b : ℝ) : HasDerivAt (fun t : ℝ => a + t * b) b 0 := by
  simpa using ((hasDerivAt_id (0 : ℝ)).mul_const b).const_add a

/-! ### Exercise 2.F.10 -/

/-- Derivative of a typical component `(a + t a')/(P + t P') · (w + t c)/(b + t b')` of the
Exercise 2.E.1 demand along a line. -/
theorem hasDerivAt_share_term (a a' P P' w c b b' : ℝ) (hP : P ≠ 0) (hb : b ≠ 0) :
    HasDerivAt (fun t : ℝ => (a + t * a') / (P + t * P') * ((w + t * c) / (b + t * b')))
      ((a' * P - a * P') / P ^ 2 * (w / b) + a / P * ((c * b - w * b') / b ^ 2)) 0 := by
  have h1 := (hasDerivAt_affine a a').div (hasDerivAt_affine P P') (by simpa using hP)
  have h2 := (hasDerivAt_affine w c).div (hasDerivAt_affine b b') (by simpa using hb)
  convert h1.mul h2 using 1
  simp only [Pi.div_apply, zero_mul, add_zero]

/-- **Exercise 2.F.10** (MWG, p. 38). The compensated derivative `S v` of the Exercise 2.E.1
demand (`β = 1`) at any `(p, w)`, with `P = p₁ + p₂ + p₃`, `V = v₁ + v₂ + v₃`, `c = v·x`. -/
theorem slutsky_2_E_1_mulVec {p : Fin 3 → ℝ} {w : ℝ} (hd : PWDomain p w) (v : Fin 3 → ℝ) :
    Matrix.mulVec (slutskyMatrix (fderiv ℝ (Function.uncurry (demand_2_E_1 1)) (p, w))
      (demand_2_E_1 1 p w)) v =
    let P := p 0 + p 1 + p 2
    let V := v 0 + v 1 + v 2
    let c := v ⬝ᵥ demand_2_E_1 1 p w
    ![(v 1 * P - p 1 * V) / P ^ 2 * (w / p 0) + p 1 / P * ((c * p 0 - w * v 0) / p 0 ^ 2),
      (v 2 * P - p 2 * V) / P ^ 2 * (w / p 1) + p 2 / P * ((c * p 1 - w * v 1) / p 1 ^ 2),
      (v 0 * P - p 0 * V) / P ^ 2 * (w / p 2) + p 0 / P * ((c * p 2 - w * v 2) / p 2 ^ 2)] := by
  have hD := (demand_2_E_1_differentiableAt 1 hd).hasFDerivAt
  have h0 := (hd.1 0).ne'
  have h1 := (hd.1 1).ne'
  have h2 := (hd.1 2).ne'
  have hP : p 0 + p 1 + p 2 ≠ 0 := by have := hd.1 0; have := hd.1 1; have := hd.1 2; positivity
  apply slutsky_mulVec_of_hasDerivAt hD
  intro l
  fin_cases l
  · convert hasDerivAt_share_term (p 1) (v 1) (p 0 + p 1 + p 2) (v 0 + v 1 + v 2) w
      (v ⬝ᵥ demand_2_E_1 1 p w) (p 0) (v 0) hP h0 using 1
    · funext t
      simp only [demand_2_E_1, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.zero_eta,
        Matrix.cons_val_zero]
      ring
    · rfl
  · convert hasDerivAt_share_term (p 2) (v 2) (p 0 + p 1 + p 2) (v 0 + v 1 + v 2) w
      (v ⬝ᵥ demand_2_E_1 1 p w) (p 1) (v 1) hP h1 using 1
    · funext t
      simp only [demand_2_E_1, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.mk_one,
        Matrix.cons_val_one, Matrix.cons_val_zero]
      ring
    · rfl
  · convert hasDerivAt_share_term (p 0) (v 0) (p 0 + p 1 + p 2) (v 0 + v 1 + v 2) w
      (v ⬝ᵥ demand_2_E_1 1 p w) (p 2) (v 2) hP h2 using 1
    · funext t
      simp only [demand_2_E_1, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.reduceFinMk,
        Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
      ring
    · rfl

/-- **Exercise 2.F.10(a)** (MWG, p. 38). At `p = (1,1,1)`, `w = 1`, the Slutsky matrix of the
Exercise 2.E.1 demand with `β = 1` is `(1/3)[[-1,1,0],[0,-1,1],[1,0,-1]]`. -/
theorem exercise_2_F_10a_matrix :
    slutskyMatrix (fderiv ℝ (Function.uncurry (demand_2_E_1 1)) (fun _ => 1, 1))
      (demand_2_E_1 1 (fun _ => 1) 1) =
    !![-1 / 3, 1 / 3, 0; 0, -1 / 3, 1 / 3; 1 / 3, 0, -1 / 3] := by
  have hd : PWDomain (fun _ : Fin 3 => (1 : ℝ)) 1 := ⟨fun _ => one_pos, one_pos⟩
  ext l k
  have h := congrFun (slutsky_2_E_1_mulVec hd (Pi.single k 1)) l
  rw [Matrix.mulVec_single_one] at h
  simp only [Matrix.col_apply] at h
  rw [h]
  fin_cases l <;> fin_cases k <;>
    simp [demand_2_E_1, dotProduct, Pi.single_apply] <;> norm_num

/-- **Exercise 2.F.10(a)** (MWG, p. 38). At `p = (1,1,1)`, `w = 1`, the Slutsky matrix is
negative semidefinite but not symmetric. -/
theorem exercise_2_F_10a :
    NegSemidef (slutskyMatrix (fderiv ℝ (Function.uncurry (demand_2_E_1 1)) (fun _ => 1, 1))
      (demand_2_E_1 1 (fun _ => 1) 1)) ∧
    ¬ (slutskyMatrix (fderiv ℝ (Function.uncurry (demand_2_E_1 1)) (fun _ => 1, 1))
      (demand_2_E_1 1 (fun _ => 1) 1)).IsSymm := by
  rw [exercise_2_F_10a_matrix]
  constructor
  · intro z
    simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
    nlinarith [sq_nonneg (z 0 - z 1), sq_nonneg (z 1 - z 2), sq_nonneg (z 2 - z 0)]
  · intro h
    have := congrFun (congrFun h.eq 0) 1
    simp at this

/-- **Exercise 2.F.10(b)** (MWG, p. 38). At `p = (1, 1, ε)`, `w = 1`, with `0 < ε < 1/22`,
the direction `v = (1, 0, 3ε/2)` gives `v·S v = (1 - 22ε)/(4(2+ε)²) > 0`: the Slutsky matrix is
not negative semidefinite. -/
theorem exercise_2_F_10b_quadratic {ε : ℝ} (hε : 0 < ε) :
    let S := slutskyMatrix (fderiv ℝ (Function.uncurry (demand_2_E_1 1)) (![1, 1, ε], 1))
      (demand_2_E_1 1 ![1, 1, ε] 1)
    ![1, 0, 3 * ε / 2] ⬝ᵥ Matrix.mulVec S ![1, 0, 3 * ε / 2] = (1 - 22 * ε) / (4 * (2 + ε) ^ 2)
    := by
  have hd : PWDomain (![1, 1, ε] : Fin 3 → ℝ) 1 := by
    refine ⟨fun l => ?_, one_pos⟩
    fin_cases l <;> simp [hε]
  intro S
  rw [slutsky_2_E_1_mulVec hd]
  have h2 : (2 + ε) ≠ 0 := by positivity
  simp [demand_2_E_1, dotProduct, Fin.sum_univ_three]
  field_simp
  ring

/-- **Exercise 2.F.10(b)** (MWG, p. 38). The demand of Exercise 2.E.1 with `β = 1` violates the
weak axiom: otherwise Proposition 2.F.2 would make `S(p, w)` negative semidefinite at
`p = (1, 1, 1/44)`, `w = 1`. -/
theorem exercise_2_F_10b : ¬ WeakAxiom (demand_2_E_1 1) := by
  intro hWA
  set ε : ℝ := 1 / 44
  have hε : 0 < ε := by norm_num
  have hd : PWDomain (![1, 1, ε] : Fin 3 → ℝ) 1 := by
    refine ⟨fun l => ?_, one_pos⟩
    fin_cases l <;> simp [hε]
  have hD := (demand_2_E_1_differentiableAt 1 hd).hasFDerivAt
  have hW := (exercise_2_E_1_walras_iff 1).mpr rfl
  have hns := proposition_2_F_2 hW hWA hd hD ![1, 0, 3 * ε / 2]
  have hq := exercise_2_F_10b_quadratic hε
  simp only at hq
  rw [hq] at hns
  have : 0 < (1 - 22 * ε) / (4 * (2 + ε) ^ 2) := by
    apply div_pos <;> norm_num [ε]
  linarith

/-! ### Exercise 2.F.16 -/

/-- **Exercise 2.F.16** (MWG, p. 39). The demand `x₁ = p₂/p₃`, `x₂ = -p₁/p₃`, `x₃ = w/p₃` on
the consumption set `ℝ³` (goods indexed `0, 1, 2`). -/
noncomputable def demand_2_F_16 : DemandFunction 3 := fun p w => ![p 1 / p 2, -(p 0 / p 2), w / p 2]

/-- **Exercise 2.F.16(a)** (MWG, p. 39). The demand is homogeneous of degree zero and satisfies
Walras' law. -/
theorem exercise_2_F_16a : HomogeneousZero demand_2_F_16 ∧ WalrasLaw demand_2_F_16 := by
  constructor
  · intro p w a hd ha
    have := (hd.1 2).ne'
    funext l
    fin_cases l <;> simp [demand_2_F_16] <;> field_simp
  · intro p w hd
    have := (hd.1 2).ne'
    simp [demand_2_F_16, dotProduct, Fin.sum_univ_three]
    field_simp
    ring

/-- **Exercise 2.F.16(b)** (MWG, p. 39). The demand violates the weak axiom: at `p = (1,1,1)`,
`w = 2` and `p' = (1,2,1)`, `w' = 1`, each bundle is affordable in the other situation. -/
theorem exercise_2_F_16b : ¬ WeakAxiom demand_2_F_16 := by
  intro h
  have hd : PWDomain (![1, 1, 1] : Fin 3 → ℝ) 2 :=
    ⟨fun l => by fin_cases l <;> simp, by norm_num⟩
  have hd' : PWDomain (![1, 2, 1] : Fin 3 → ℝ) 1 :=
    ⟨fun l => by fin_cases l <;> simp, by norm_num⟩
  have := h _ _ _ _ hd hd' (by simp [demand_2_F_16, dotProduct, Fin.sum_univ_three])
    (by
      intro he
      have := congrFun he 0
      simp [demand_2_F_16] at this)
  simp [demand_2_F_16, dotProduct, Fin.sum_univ_three] at this

/-- The Exercise 2.F.16 demand is differentiable at every domain point. -/
theorem demand_2_F_16_differentiableAt {p : Fin 3 → ℝ} {w : ℝ} (hd : PWDomain p w) :
    DifferentiableAt ℝ (Function.uncurry demand_2_F_16) (p, w) := by
  have h2 := (hd.1 2).ne'
  rw [differentiableAt_pi]
  intro i
  fin_cases i <;>
    simp only [demand_2_F_16, Function.uncurry_def, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons, div_eq_mul_inv] <;>
    fun_prop (disch := assumption)

/-- **Exercise 2.F.16(c)** (MWG, p. 39). `v·S(p, w) v = 0` for all `v ∈ ℝ³`. -/
theorem exercise_2_F_16c {p : Fin 3 → ℝ} {w : ℝ} (hd : PWDomain p w) (v : Fin 3 → ℝ) :
    v ⬝ᵥ Matrix.mulVec (slutskyMatrix (fderiv ℝ (Function.uncurry demand_2_F_16) (p, w))
      (demand_2_F_16 p w)) v = 0 := by
  have hD := (demand_2_F_16_differentiableAt hd).hasFDerivAt
  have h2 := (hd.1 2).ne'
  set c := v ⬝ᵥ demand_2_F_16 p w with hc
  have hS := slutsky_mulVec_of_hasDerivAt hD v
    ![(v 1 * p 2 - p 1 * v 2) / p 2 ^ 2, -((v 0 * p 2 - p 0 * v 2) / p 2 ^ 2),
      (c * p 2 - w * v 2) / p 2 ^ 2] (by
    intro l
    fin_cases l
    · convert (hasDerivAt_affine (p 1) (v 1)).div (hasDerivAt_affine (p 2) (v 2))
        (by simpa using h2) using 1
      · funext t
        simp [demand_2_F_16]
      · simp
    · convert ((hasDerivAt_affine (p 0) (v 0)).div (hasDerivAt_affine (p 2) (v 2))
        (by simpa using h2)).neg using 1
      · funext t
        simp [demand_2_F_16]
      · simp
    · convert (hasDerivAt_affine w c).div (hasDerivAt_affine (p 2) (v 2))
        (by simpa using h2) using 1
      · funext t
        simp [demand_2_F_16, hc]
      · simp)
  rw [hS]
  simp only [hc, demand_2_F_16, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  field_simp
  ring

/-! ### Exercise 2.F.15 -/

/-- **Exercise 2.F.15** (MWG, p. 39). The demand on the consumption set `ℝ³` that is
homogeneous of degree zero, satisfies Walras' law and, at `p₃ = 1`, has `x₁ = -p₁ + p₂` and
`x₂ = -p₂` (goods indexed `0, 1, 2`):
`x = ((p₂ - p₁)/p₃, -p₂/p₃, w/p₃ + (p₁² - p₁p₂ + p₂²)/p₃²)`. -/
noncomputable def demand_2_F_15 : DemandFunction 3 := fun p w =>
  ![(p 1 - p 0) / p 2, -(p 1 / p 2), w / p 2 + (p 0 ^ 2 - p 0 * p 1 + p 1 ^ 2) / p 2 ^ 2]

/-- The quadratic form `Q(a, b) = a² - ab + b²`, positive definite. -/
theorem quadForm_pos {a b : ℝ} (h : a ≠ 0 ∨ b ≠ 0) : 0 < a ^ 2 - a * b + b ^ 2 := by
  rcases h with h | h
  · have := pow_pos (abs_pos.mpr h) 2
    nlinarith [sq_nonneg (b - a / 2), sq_abs a]
  · have := pow_pos (abs_pos.mpr h) 2
    nlinarith [sq_nonneg (a - b / 2), sq_abs b]

/-- **Exercise 2.F.15** (MWG, p. 39). The demand is homogeneous of degree zero, satisfies
Walras' law, and has the stated first two components at `p₃ = 1`. -/
theorem exercise_2_F_15_basic :
    HomogeneousZero demand_2_F_15 ∧ WalrasLaw demand_2_F_15 ∧
      ∀ p w, p 2 = 1 → demand_2_F_15 p w 0 = -p 0 + p 1 ∧ demand_2_F_15 p w 1 = -p 1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro p w a hd ha
    have := (hd.1 2).ne'
    funext l
    fin_cases l <;> simp [demand_2_F_15] <;> field_simp
  · intro p w hd
    have := (hd.1 2).ne'
    simp [demand_2_F_15, dotProduct, Fin.sum_univ_three]
    field_simp
    ring
  · intro p w h
    simp [demand_2_F_15, h]
    ring

/-- **Exercise 2.F.15** (MWG, p. 39). The data determine the demand: any demand function that
is homogeneous of degree zero, satisfies Walras' law and has `x₁ = -p₁ + p₂`, `x₂ = -p₂` at
`p₃ = 1` coincides with `demand_2_F_15` on the domain. -/
theorem exercise_2_F_15_unique {x : DemandFunction 3} (hH : HomogeneousZero x)
    (hW : WalrasLaw x) (h0 : ∀ p w, PWDomain p w → p 2 = 1 → x p w 0 = -p 0 + p 1)
    (h1 : ∀ p w, PWDomain p w → p 2 = 1 → x p w 1 = -p 1) :
    ∀ p w, PWDomain p w → x p w = demand_2_F_15 p w := by
  intro p w hd
  have hc := hd.1 2
  set a := (p 2)⁻¹ with ha
  have ha0 : 0 < a := inv_pos.mpr hc
  have hd' := pwDomain_smul hd ha0
  have hq2 : (a • p) 2 = 1 := by simp [ha, hc.ne']
  have e := hH p w a hd ha0
  rw [← e]
  have hw := hW _ _ hd'
  simp only [dotProduct, Fin.sum_univ_three, h0 _ _ hd' hq2, h1 _ _ hd' hq2, hq2,
    one_mul] at hw
  funext l
  fin_cases l
  · change x (a • p) (a * w) 0 = demand_2_F_15 p w 0
    rw [h0 _ _ hd' hq2]
    simp only [demand_2_F_15, Matrix.cons_val_zero, Pi.smul_apply, smul_eq_mul, ha]
    field_simp
    ring
  · change x (a • p) (a * w) 1 = demand_2_F_15 p w 1
    rw [h1 _ _ hd' hq2]
    simp only [demand_2_F_15, Matrix.cons_val_one, Matrix.cons_val_zero, Pi.smul_apply,
      smul_eq_mul, ha]
    field_simp
  · simp only [Fin.reduceFinMk, demand_2_F_15, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons]
    have : x (a • p) (a * w) 2 = a * w - (a • p) 0 * (-(a • p) 0 + (a • p) 1) -
        (a • p) 1 * -(a • p) 1 := by linarith
    rw [this]
    simp only [Pi.smul_apply, smul_eq_mul, ha]
    field_simp
    ring

/-- **Exercise 2.F.15** (MWG, p. 39). The demand satisfies the weak axiom (proved directly). -/
theorem exercise_2_F_15_weakAxiom : WeakAxiom demand_2_F_15 := by
  intro p w p' w' hd hd' hle hne
  have hc := hd.1 2
  have hc' := hd'.1 2
  -- normalised prices and wealth
  set q0 := p 0 / p 2
  set q1 := p 1 / p 2
  set u := w / p 2
  set r0 := p' 0 / p' 2
  set r1 := p' 1 / p' 2
  set u' := w' / p' 2
  have hx : demand_2_F_15 p w = ![q1 - q0, -q1, u + (q0 ^ 2 - q0 * q1 + q1 ^ 2)] := by
    funext l
    fin_cases l <;> simp [demand_2_F_15, q0, q1, u] <;> field_simp
  have hx' : demand_2_F_15 p' w' = ![r1 - r0, -r1, u' + (r0 ^ 2 - r0 * r1 + r1 ^ 2)] := by
    funext l
    fin_cases l <;> simp [demand_2_F_15, r0, r1, u'] <;> field_simp
  have hdot : ∀ (z : Fin 3 → ℝ), p ⬝ᵥ z = p 2 * (q0 * z 0 + q1 * z 1 + z 2) := by
    intro z
    simp only [dotProduct, Fin.sum_univ_three, q0, q1]
    field_simp
  have hdot' : ∀ (z : Fin 3 → ℝ), p' ⬝ᵥ z = p' 2 * (r0 * z 0 + r1 * z 1 + z 2) := by
    intro z
    simp only [dotProduct, Fin.sum_univ_three, r0, r1]
    field_simp
  have hw : w = p 2 * u := by simp only [u]; field_simp
  have hw' : w' = p' 2 * u' := by simp only [u']; field_simp
  rw [hdot, hx', hw] at hle
  rw [hdot', hx, hw']
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons] at hle ⊢
  have hle' : q0 * (r1 - r0) + q1 * -r1 + (u' + (r0 ^ 2 - r0 * r1 + r1 ^ 2)) ≤ u :=
    le_of_mul_le_mul_left hle hc
  apply mul_lt_mul_of_pos_left _ hc'
  by_cases hq : q0 = r0 ∧ q1 = r1
  · obtain ⟨e0, e1⟩ := hq
    have hu : u ≠ u' := by
      intro hu
      apply hne
      rw [hx, hx', e0, e1, hu]
    rw [← e0, ← e1] at hle' ⊢
    have : u' ≤ u := by nlinarith
    have : u' < u := lt_of_le_of_ne this (Ne.symm hu)
    nlinarith
  · have hpos : 0 < (q0 - r0) ^ 2 - (q0 - r0) * (q1 - r1) + (q1 - r1) ^ 2 := by
      apply quadForm_pos
      by_contra hc0
      push Not at hc0
      exact hq ⟨by linarith [hc0.1], by linarith [hc0.2]⟩
    nlinarith

/-- **Exercise 2.F.15** (MWG, p. 39). The Exercise 2.F.15 demand is differentiable at every
domain point. -/
theorem demand_2_F_15_differentiableAt {p : Fin 3 → ℝ} {w : ℝ} (hd : PWDomain p w) :
    DifferentiableAt ℝ (Function.uncurry demand_2_F_15) (p, w) := by
  have h2 := (hd.1 2).ne'
  have h2' : p 2 ^ 2 ≠ 0 := pow_ne_zero 2 h2
  rw [differentiableAt_pi]
  intro i
  fin_cases i <;>
    simp only [demand_2_F_15, Function.uncurry_def, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons, div_eq_mul_inv] <;>
    fun_prop (disch := assumption)

/-- **Exercise 2.F.15** (MWG, p. 39). The compensated derivative `S v` of the demand. -/
theorem slutsky_2_F_15_mulVec {p : Fin 3 → ℝ} {w : ℝ} (hd : PWDomain p w) (v : Fin 3 → ℝ) :
    Matrix.mulVec (slutskyMatrix (fderiv ℝ (Function.uncurry demand_2_F_15) (p, w))
      (demand_2_F_15 p w)) v =
    ![((v 1 - v 0) * p 2 - (p 1 - p 0) * v 2) / p 2 ^ 2, -((v 1 * p 2 - p 1 * v 2) / p 2 ^ 2),
      (p 0 * v 0 - p 0 * v 1 + p 1 * v 1) / p 2 ^ 2 -
        (p 0 ^ 2 - p 0 * p 1 + p 1 ^ 2) * v 2 / p 2 ^ 3] := by
  have hD := (demand_2_F_15_differentiableAt hd).hasFDerivAt
  have h2 := (hd.1 2).ne'
  have h2' : p 2 + 0 * v 2 ≠ 0 := by simpa using h2
  apply slutsky_mulVec_of_hasDerivAt hD
  intro l
  fin_cases l
  · convert ((hasDerivAt_affine (p 1) (v 1)).sub (hasDerivAt_affine (p 0) (v 0))).div
      (hasDerivAt_affine (p 2) (v 2)) h2' using 1
    · funext t
      simp [demand_2_F_15]
    · simp
  · convert ((hasDerivAt_affine (p 1) (v 1)).div (hasDerivAt_affine (p 2) (v 2)) h2').neg
      using 1
    · funext t
      simp [demand_2_F_15]
    · simp
  · set c := v ⬝ᵥ demand_2_F_15 p w with hc
    have hA := hasDerivAt_affine (p 0) (v 0)
    have hB := hasDerivAt_affine (p 1) (v 1)
    have hC := hasDerivAt_affine (p 2) (v 2)
    have hnum := ((hA.pow 2).sub (hA.mul hB)).add (hB.pow 2)
    have hden := hC.pow 2
    have hq := hnum.div hden (by simpa using pow_ne_zero 2 h2)
    have hw := (hasDerivAt_affine w c).div hC h2'
    convert hw.add hq using 1
    · funext t
      simp [demand_2_F_15]
    · rw [hc]
      simp [demand_2_F_15, dotProduct, Fin.sum_univ_three]
      field_simp
      ring

/-- **Exercise 2.F.15** (MWG, p. 39). The Slutsky quadratic form is
`v·S v = -Q(p₃v₁ - v₃p₁, p₃v₂ - v₃p₂)/p₃³` with `Q(a, b) = a² - ab + b²`. -/
theorem exercise_2_F_15_quadratic {p : Fin 3 → ℝ} {w : ℝ} (hd : PWDomain p w)
    (v : Fin 3 → ℝ) :
    v ⬝ᵥ Matrix.mulVec (slutskyMatrix (fderiv ℝ (Function.uncurry demand_2_F_15) (p, w))
      (demand_2_F_15 p w)) v =
    -(((p 2 * v 0 - v 2 * p 0) ^ 2 - (p 2 * v 0 - v 2 * p 0) * (p 2 * v 1 - v 2 * p 1) +
      (p 2 * v 1 - v 2 * p 1) ^ 2) / p 2 ^ 3) := by
  rw [slutsky_2_F_15_mulVec hd]
  have h2 := (hd.1 2).ne'
  simp only [dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  field_simp
  ring

/-- **Exercise 2.F.15** (MWG, p. 39). `v·S(p, w) v < 0` for every `v` that is not a multiple of
`p`. -/
theorem exercise_2_F_15_negDef_off_p {p : Fin 3 → ℝ} {w : ℝ} (hd : PWDomain p w)
    (v : Fin 3 → ℝ) (hv : ∀ α : ℝ, v ≠ α • p) :
    v ⬝ᵥ Matrix.mulVec (slutskyMatrix (fderiv ℝ (Function.uncurry demand_2_F_15) (p, w))
      (demand_2_F_15 p w)) v < 0 := by
  rw [exercise_2_F_15_quadratic hd]
  have hc := hd.1 2
  rw [neg_neg_iff_pos]
  apply div_pos _ (pow_pos hc 3)
  apply quadForm_pos
  by_contra h
  push Not at h
  apply hv (v 2 / p 2)
  funext l
  fin_cases l
  · simp only [Fin.zero_eta, Pi.smul_apply, smul_eq_mul]
    field_simp
    linarith [h.1]
  · simp only [Fin.mk_one, Pi.smul_apply, smul_eq_mul]
    field_simp
    linarith [h.2]
  · simp only [Fin.reduceFinMk, Pi.smul_apply, smul_eq_mul]
    field_simp

/-- **Exercise 2.F.15** (MWG, p. 39). The Slutsky matrix is not symmetric: `s₁₂ = 1/p₃` while
`s₂₁ = 0`. -/
theorem exercise_2_F_15_not_symm {p : Fin 3 → ℝ} {w : ℝ} (hd : PWDomain p w) :
    ¬ (slutskyMatrix (fderiv ℝ (Function.uncurry demand_2_F_15) (p, w))
      (demand_2_F_15 p w)).IsSymm := by
  intro h
  have e01 := congrFun (slutsky_2_F_15_mulVec hd (Pi.single 1 1)) 0
  have e10 := congrFun (slutsky_2_F_15_mulVec hd (Pi.single 0 1)) 1
  rw [Matrix.mulVec_single_one] at e01 e10
  have hs := congrFun (congrFun h.eq 0) 1
  simp only [Matrix.transpose_apply] at hs
  simp only [Matrix.col_apply] at e01 e10
  rw [← hs, e10] at e01
  have h2 := (hd.1 2).ne'
  have key : p 2 / p 2 ^ 2 = 0 := by simpa using e01.symm
  exact div_ne_zero h2 (pow_ne_zero 2 h2) key

/-! ### Exercise 2.F.17 -/

/-- **Exercise 2.F.17** (MWG, p. 39). The demand `x_k(p, w) = w / ∑_ℓ p_ℓ`. -/
noncomputable def demand_2_F_17 (L : ℕ) : DemandFunction L := fun p w _ => w / ∑ l, p l

/-- **Exercise 2.F.17(a)** (MWG, p. 39). The demand is homogeneous of degree zero. -/
theorem exercise_2_F_17a (L : ℕ) : HomogeneousZero (demand_2_F_17 L) := by
  intro p w a hd ha
  funext k
  simp only [demand_2_F_17, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  rw [mul_div_mul_left _ _ ha.ne']

/-- With at least one good, the price sum is positive. -/
theorem sum_prices_pos {L : ℕ} {p : Fin L → ℝ} (hp : StrictlyPositive p) (l : Fin L) :
    0 < ∑ k, p k :=
  Finset.sum_pos (fun k _ => hp k) ⟨l, Finset.mem_univ l⟩

/-- **Exercise 2.F.17(b)** (MWG, p. 39). The demand satisfies Walras' law (for `L ≥ 1`). -/
theorem exercise_2_F_17b (L : ℕ) [NeZero L] : WalrasLaw (demand_2_F_17 L) := by
  intro p w hd
  have := (sum_prices_pos hd.1 0).ne'
  simp only [demand_2_F_17, dotProduct, ← Finset.sum_mul]
  field_simp

/-- **Exercise 2.F.17(c)** (MWG, p. 39). The demand satisfies the weak axiom. -/
theorem exercise_2_F_17c (L : ℕ) : WeakAxiom (demand_2_F_17 L) := by
  intro p w p' w' hd hd' hle hne
  rcases isEmpty_or_nonempty (Fin L) with hL | ⟨⟨l⟩⟩
  · exact absurd (funext fun i => (hL.false i).elim) hne
  have hs := sum_prices_pos hd.1 l
  have hs' := sum_prices_pos hd'.1 l
  simp only [demand_2_F_17, dotProduct, ← Finset.sum_mul] at hle ⊢
  have hne' : w' / ∑ k, p' k ≠ w / ∑ k, p k := fun h => hne (funext fun _ => h)
  have hle' : w' / ∑ k, p' k ≤ w / ∑ k, p k := by
    rw [le_div_iff₀ hs]
    linarith
  have hlt := lt_of_le_of_ne hle' hne'
  rw [div_lt_div_iff₀ hs' hs] at hlt
  rw [mul_div_assoc', lt_div_iff₀ hs]
  linarith

/-- The Exercise 2.F.17 demand is differentiable at every domain point. -/
theorem demand_2_F_17_differentiableAt {L : ℕ} {p : Fin L → ℝ} {w : ℝ} (hd : PWDomain p w)
    (l : Fin L) : DifferentiableAt ℝ (Function.uncurry (demand_2_F_17 L)) (p, w) := by
  have hs := (sum_prices_pos hd.1 l).ne'
  rw [differentiableAt_pi]
  intro i
  simp only [demand_2_F_17, Function.uncurry_def, div_eq_mul_inv]
  fun_prop (disch := assumption)

/-- **Exercise 2.F.17(d)** (MWG, p. 39). The Slutsky matrix is zero at every `(p, w)`. -/
theorem exercise_2_F_17d_zero {L : ℕ} {p : Fin L → ℝ} {w : ℝ} (hd : PWDomain p w)
    (l : Fin L) :
    slutskyMatrix (fderiv ℝ (Function.uncurry (demand_2_F_17 L)) (p, w)) (demand_2_F_17 L p w)
      = 0 := by
  have hD := (demand_2_F_17_differentiableAt hd l).hasFDerivAt
  have hs := (sum_prices_pos hd.1 l).ne'
  have hcol : ∀ v, Matrix.mulVec (slutskyMatrix (fderiv ℝ (Function.uncurry (demand_2_F_17 L))
      (p, w)) (demand_2_F_17 L p w)) v = 0 := by
    intro v
    apply slutsky_mulVec_of_hasDerivAt hD
    intro k
    set c := v ⬝ᵥ demand_2_F_17 L p w with hc
    have h := (hasDerivAt_affine w c).div (hasDerivAt_affine (∑ l, p l) (∑ l, v l))
      (by simpa using hs)
    convert h using 1
    · funext t
      simp [demand_2_F_17, Finset.sum_add_distrib, Finset.mul_sum]
    · rw [hc]
      simp only [demand_2_F_17, dotProduct, ← Finset.sum_mul, Pi.zero_apply]
      field_simp
      ring
  ext i k
  have := congrFun (hcol (Pi.single k 1)) i
  rw [Matrix.mulVec_single_one] at this
  simpa using this

/-- **Exercise 2.F.17(d)** (MWG, p. 39). The Slutsky matrix is negative semidefinite,
symmetric, and (with at least one good) not negative definite. -/
theorem exercise_2_F_17d {L : ℕ} {p : Fin L → ℝ} {w : ℝ} (hd : PWDomain p w) (l : Fin L) :
    NegSemidef (slutskyMatrix (fderiv ℝ (Function.uncurry (demand_2_F_17 L)) (p, w))
        (demand_2_F_17 L p w)) ∧
      (slutskyMatrix (fderiv ℝ (Function.uncurry (demand_2_F_17 L)) (p, w))
        (demand_2_F_17 L p w)).IsSymm ∧
      ¬ NegDef (slutskyMatrix (fderiv ℝ (Function.uncurry (demand_2_F_17 L)) (p, w))
        (demand_2_F_17 L p w)) := by
  rw [exercise_2_F_17d_zero hd l]
  refine ⟨fun z => by simp, Matrix.isSymm_zero, fun h => ?_⟩
  have := h (Pi.single l 1) (by simp)
  simp at this

end MWG.ConsumerChoice

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Negative definiteness off the price ray implies the weak axiom

MWG, Section 2.F, p. 35 (small type), citing Samuelson (1947) and Kihlstrom, Mas-Colell and
Sonnenschein (1976): if a demand function satisfying Walras' law and homogeneity of degree zero
has `v·S(p, w)v < 0` whenever `v ≠ αp`, then it satisfies the weak axiom.

Precise form proved here: demand is differentiable at every `p ≫ 0`, `w > 0`, takes values in
`ℝ^L_+`, and the condition holds at every `(p, w)`. Proof: for a compensated change from
`(p, w)` to `p'` (not proportional to `p`), put `Δ = p' - p`, `x̄ = x(p, w)` and
`φ(t) = Δ·[x(p + tΔ, w + tΔ·x̄) - x̄]`. Then `φ(0) = 0` and
`φ'(t) = Δ·S(t)Δ - (Δ·D_w x(t)) φ(t)`, so `φ' < 0` wherever `φ = 0`; hence `φ(1) < 0`, which is
the strict compensated law of demand, and Proposition 2.F.1 gives the weak axiom.
-/

namespace MWG.ConsumerChoice

open Filter Topology Set

/-- A function on `[0, 1]` that vanishes at `0` and has negative derivative at each of its zeros
is negative at `1`. -/
theorem neg_at_one_of_deriv_neg_at_zeros {φ : ℝ → ℝ} (h0 : φ 0 = 0)
    (hd : ∀ t ∈ Icc (0 : ℝ) 1, ∃ d, HasDerivAt φ d t ∧ (φ t = 0 → d < 0)) : φ 1 < 0 := by
  have hcont : ContinuousOn φ (Icc 0 1) :=
    fun t ht => (hd t ht).choose_spec.1.continuousAt.continuousWithinAt
  -- negative just to the right of `0`
  obtain ⟨d0, hd0, hd0neg⟩ := hd 0 ⟨le_rfl, zero_le_one⟩
  have hd0' := hd0neg h0
  have hslope := (hasDerivAt_iff_tendsto_slope.mp hd0).mono_left
    (nhdsWithin_mono _ fun t (ht : 0 < t) => ne_of_gt ht)
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), φ t < 0 := by
    filter_upwards [hslope.eventually (gt_mem_nhds hd0'), self_mem_nhdsWithin] with t ht htpos
    rw [slope_def_field, h0, sub_zero, sub_zero] at ht
    have ht' : (0 : ℝ) < t := htpos
    by_contra hc
    push Not at hc
    have := div_nonneg hc ht'.le
    linarith
  obtain ⟨ε, hε, hεsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  have hε' : (0 : ℝ) < ε := hε
  by_contra hcon
  push Not at hcon
  set δ := min (ε / 2) 1 with hδ
  have hδpos : 0 < δ := lt_min (by linarith) one_pos
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hδε : δ < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  set T := Icc δ 1 ∩ φ ⁻¹' Ici 0 with hT
  have hTclosed : IsClosed T :=
    (hcont.mono (Icc_subset_Icc hδpos.le le_rfl)).preimage_isClosed_of_isClosed isClosed_Icc
      isClosed_Ici
  have hTne : T.Nonempty := ⟨1, ⟨hδ1, le_rfl⟩, hcon⟩
  have hTbdd : BddBelow T := ⟨δ, fun t ht => ht.1.1⟩
  set t0 := sInf T
  have ht0 : t0 ∈ T := hTclosed.csInf_mem hTne hTbdd
  have ht0pos : 0 < t0 := lt_of_lt_of_le hδpos ht0.1.1
  -- `φ < 0` on `(0, t0)`
  have hneg : ∀ t ∈ Ioo 0 t0, φ t < 0 := by
    intro t ht
    by_cases htε : t < ε
    · exact hεsub ⟨ht.1, htε⟩
    · by_contra hc
      push Not at hc
      have hmem : t ∈ T := ⟨⟨by linarith, ht.2.le.trans ht0.1.2⟩, hc⟩
      exact absurd (csInf_le hTbdd hmem) (not_le.mpr ht.2)
  obtain ⟨d, hdt, hdneg⟩ := hd t0 ⟨ht0pos.le, ht0.1.2⟩
  have hleft : ∀ᶠ t in 𝓝[<] t0, t ∈ Ioo 0 t0 := Ioo_mem_nhdsLT ht0pos
  have hφ0 : φ t0 = 0 := by
    apply le_antisymm _ ht0.2
    apply le_of_tendsto (hdt.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio t0)))
    filter_upwards [hleft] with t ht
    exact (hneg t ht).le
  have hdlt := hdneg hφ0
  have hsl := (hasDerivAt_iff_tendsto_slope.mp hdt).mono_left
    (nhdsWithin_mono (s := Iio t0) _ fun t (ht : t < t0) => ne_of_lt ht)
  have : 0 ≤ d := by
    apply ge_of_tendsto hsl
    filter_upwards [hleft] with t ht
    rw [slope_def_field, hφ0, sub_zero]
    exact (div_pos_of_neg_of_neg (hneg t ht) (by linarith [ht.2])).le
  linarith

/-- **Section 2.F** (MWG, p. 35, small type; Samuelson 1947, Kihlstrom, Mas-Colell and
Sonnenschein 1976). Let `x` be homogeneous of degree zero, satisfy Walras' law, take values in
`ℝ^L_+` and be differentiable at every `p ≫ 0`, `w > 0`. If `v·S(p, w)v < 0` for every `(p, w)`
and every `v` not proportional to `p`, then `x` satisfies the weak axiom. -/
theorem samuelson_sufficiency {L : ℕ} {x : DemandFunction L} (hH : HomogeneousZero x)
    (hW : WalrasLaw x) (hX : ValuesInOrthant x)
    (hdiff : ∀ p w, PWDomain p w → DifferentiableAt ℝ (Function.uncurry x) (p, w))
    (hS : ∀ p w, PWDomain p w → ∀ v : Fin L → ℝ, (∀ α : ℝ, v ≠ α • p) →
      v ⬝ᵥ Matrix.mulVec (slutskyMatrix (fderiv ℝ (Function.uncurry x) (p, w)) (x p w)) v < 0) :
    WeakAxiom x := by
  apply proposition_2_F_1_ii hW hX
  intro p w p' hd hp' hw'
  set xb := x p w with hxb
  have hWx : p ⬝ᵥ xb = w := hW p w hd
  by_cases hprop : ∃ α : ℝ, p' = α • p
  · -- proportional prices: demand does not change
    obtain ⟨α, rfl⟩ := hprop
    obtain ⟨l⟩ : Nonempty (Fin L) := by
      by_contra hL
      rw [not_nonempty_iff] at hL
      have : p ⬝ᵥ x p w = 0 := by simp [dotProduct]
      linarith [hW p w hd, hd.2]
    have hα : 0 < α := by
      have := hp' l
      simp only [Pi.smul_apply, smul_eq_mul] at this
      exact pos_of_mul_pos_left this (hd.1 l).le
    have hcw : compensatedWealth x p w (α • p) = α * w := by
      simp [compensatedWealth, smul_dotProduct, hW p w hd]
    rw [hcw, hH p w α hd hα, sub_self, dotProduct_zero]
    exact ⟨le_rfl, fun h => absurd rfl h⟩
  push Not at hprop
  set Δ := p' - p with hΔ
  set c := Δ ⬝ᵥ xb with hc
  have hdomt : ∀ t ∈ Icc (0 : ℝ) 1, PWDomain (p + t • Δ) (w + t * c) := by
    intro t ht
    refine ⟨fun l => ?_, ?_⟩
    · have h1 := hd.1 l
      have h2 := hp' l
      simp only [hΔ, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      rcases eq_or_lt_of_le ht.2 with h | h
      · rw [h]; linarith
      · nlinarith [mul_nonneg ht.1 h2.le, mul_pos (sub_pos.mpr h) h1]
    · have e1 : w + 1 * c = compensatedWealth x p w p' := by
        simp only [compensatedWealth, hc, hΔ, sub_dotProduct, hWx]
        ring
      have : w + t * c = (1 - t) * w + t * (w + 1 * c) := by ring
      rw [this, e1]
      rcases eq_or_lt_of_le ht.2 with h | h
      · rw [h]; simpa using hw'
      · nlinarith [mul_nonneg ht.1 hw'.le, mul_pos (sub_pos.mpr h) hd.2]
  -- `Δ` is never proportional to the current prices
  have hnp : ∀ t ∈ Icc (0 : ℝ) 1, ∀ β : ℝ, Δ ≠ β • (p + t • Δ) := by
    intro t _ β hβ
    have hne : 1 - β * t ≠ 0 := by
      intro h0
      have : β • p = 0 := by
        have e : (1 - β * t) • Δ = β • p := by
          rw [sub_smul, one_smul, mul_smul]
          nth_rewrite 1 [hβ]
          rw [smul_add]
          abel
        rw [h0, zero_smul] at e
        exact e.symm
      have hβ0 : β = 0 := by
        rcases smul_eq_zero.mp this with h | h
        · exact h
        · exfalso
          obtain ⟨l⟩ : Nonempty (Fin L) := by
            by_contra hL
            rw [not_nonempty_iff] at hL
            exact hprop 1 (funext fun i => (hL.false i).elim)
          have := hd.1 l
          rw [h] at this
          exact lt_irrefl _ this
      rw [hβ0, zero_mul, sub_zero] at h0
      exact one_ne_zero h0
    apply hprop (1 + β / (1 - β * t))
    have e : (1 - β * t) • Δ = β • p := by
      rw [sub_smul, one_smul, mul_smul]
      nth_rewrite 1 [hβ]
      rw [smul_add]
      abel
    have hΔ' : Δ = (β / (1 - β * t)) • p := by
      rw [div_eq_inv_mul, mul_smul, ← e, smul_smul, inv_mul_cancel₀ hne, one_smul]
    rw [add_smul, one_smul, ← hΔ', hΔ, add_sub_cancel]
  -- the function `φ`
  set φ : ℝ → ℝ := fun t => Δ ⬝ᵥ (x (p + t • Δ) (w + t * c) - xb) with hφ
  have hφ0 : φ 0 = 0 := by simp [hφ, hxb]
  have hderiv : ∀ t ∈ Icc (0 : ℝ) 1, ∃ d, HasDerivAt φ d t ∧ (φ t = 0 → d < 0) := by
    intro t ht
    set D := fderiv ℝ (Function.uncurry x) (p + t • Δ, w + t * c)
    have hD : HasFDerivAt (Function.uncurry x) D (p + t • Δ, w + t * c) :=
      (hdiff _ _ (hdomt t ht)).hasFDerivAt
    have hline := hasDerivAt_pi.mp (hasDerivAt_line (x := x) (p := p) (v := Δ) (w := w)
      (c := c) (t₀ := t) hD)
    have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun l _ => (hline l).const_mul (Δ l))
    refine ⟨Δ ⬝ᵥ D (Δ, c), ?_, fun hzero => ?_⟩
    · have := hsum.sub_const (Δ ⬝ᵥ xb)
      convert this using 1
      · funext s
        simp only [hφ, dotProduct_sub]
        rfl
      · simp [dotProduct]
    · -- at a zero of `φ`, the derivative is `Δ·SΔ`
      have hxt : Δ ⬝ᵥ x (p + t • Δ) (w + t * c) = c := by
        have := hzero
        simp only [hφ, dotProduct_sub] at this
        linarith
      have hSΔ := hS _ _ (hdomt t ht) Δ (hnp t ht)
      rw [slutskyMatrix_mulVec, hxt] at hSΔ
      exact hSΔ
  have hneg := neg_at_one_of_deriv_neg_at_zeros hφ0 hderiv
  have hp1 : p + (1 : ℝ) • Δ = p' := by rw [one_smul, hΔ, add_sub_cancel]
  have hw1 : w + 1 * c = compensatedWealth x p w p' := by
    simp only [compensatedWealth, hc, hΔ, sub_dotProduct, hWx]
    ring
  simp only [hφ, hp1, hw1] at hneg
  exact ⟨hneg.le, fun _ => hneg⟩

end MWG.ConsumerChoice

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Matrix notation for derivatives

MWG, Mathematical Appendix, Section M.A, pp. 926–927.

Vectors of `ℝ^N` are columns (`Fin N → ℝ`); the inner product is `x·y = ∑ xₙyₙ = xᵀy`, and
`x·A` means `xᵀA`. For a differentiable `f : ℝ^N → ℝ^M` the derivative at `x` is a continuous
linear map `f'`; its matrix `Df(x)` has `mn` entry `∂fₘ/∂xₙ` (`jacobian`). For `M = 1` the
gradient is `∇f(x) = [Df(x)]ᵀ`. Partial derivative matrices `D_x f(x, y)` restrict the
derivative to the `x`-variables. The Hessian is the derivative matrix of the gradient.

Proved: the chain rule (M.A.1) in matrix form, and the product rules (M.A.2)–(M.A.5), including
that (M.A.4) is a special case of (M.A.5) and that `g(x) Dh(x)` has rank at most one.
-/

namespace MWG.ConsumerChoice

/-- **Section M.A** (MWG, p. 926). The inner product is `x·y = xᵀy`, the single entry of the
`1 × 1` matrix `xᵀ y`. -/
theorem dotProduct_eq_transpose_mul {N : ℕ} (x y : Fin N → ℝ) :
    x ⬝ᵥ y =
      (Matrix.transpose (Matrix.replicateCol Unit x) * Matrix.replicateCol Unit y) () () := by
  simp [Matrix.mul_apply, dotProduct]

/-- **Section M.A** (MWG, p. 926). `x·A` is `xᵀA`. -/
theorem vecMul_eq_transpose_mul {N M : ℕ} (x : Fin N → ℝ) (A : Matrix (Fin N) (Fin M) ℝ) :
    Matrix.vecMul x A = fun m => (Matrix.transpose (Matrix.replicateCol Unit x) * A) () m := by
  funext m
  simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]

/-- **Section M.A** (MWG, p. 926). The derivative matrix `Df(x)` of a linear map `f'`: the
`mn` entry is `∂fₘ/∂xₙ = f'(eₙ)ₘ`. -/
def jacobian {N M : ℕ} (f' : (Fin N → ℝ) →L[ℝ] (Fin M → ℝ)) : Matrix (Fin M) (Fin N) ℝ :=
  Matrix.of fun m n => f' (Pi.single n 1) m

/-- The derivative acts on a direction by multiplication with its matrix:
`f'(v) = Df(x) v`. -/
theorem jacobian_mulVec {N M : ℕ} (f' : (Fin N → ℝ) →L[ℝ] (Fin M → ℝ)) (v : Fin N → ℝ) :
    Matrix.mulVec (jacobian f') v = f' v := by
  conv_rhs => rw [← Finset.univ_sum_single v]
  funext m
  simp only [map_sum, Finset.sum_apply, jacobian, Matrix.mulVec, dotProduct, Matrix.of_apply]
  refine Finset.sum_congr rfl fun n _ => ?_
  have : Pi.single n (v n) = v n • (Pi.single n (1 : ℝ) : Fin N → ℝ) := by
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  rw [this, map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]

/-- **Section M.A** (MWG, pp. 926–927). The gradient `∇f(x) ∈ ℝ^N` of a real-valued function,
the vector of partial derivatives `∂f/∂xₙ = f'(eₙ)`. -/
def gradientVec {N : ℕ} (f' : (Fin N → ℝ) →L[ℝ] ℝ) : Fin N → ℝ := fun n => f' (Pi.single n 1)

/-- **Section M.A** (MWG, p. 927). For `M = 1`, `∇f(x) = [Df(x)]ᵀ`: the `1 × N` derivative
matrix of `x ↦ (f x)` is the transpose of the gradient column. -/
theorem gradient_eq_transpose_jacobian {N : ℕ} (f' : (Fin N → ℝ) →L[ℝ] ℝ) :
    Matrix.replicateCol (Fin 1) (gradientVec f') =
      Matrix.transpose (jacobian (ContinuousLinearMap.pi fun _ : Fin 1 => f')) := by
  ext n u
  simp [gradientVec, jacobian]

/-- The gradient represents the derivative: `f'(v) = ∇f(x)·v`. -/
theorem fderiv_apply_eq_gradient_dot {N : ℕ} (f' : (Fin N → ℝ) →L[ℝ] ℝ) (v : Fin N → ℝ) :
    f' v = gradientVec f' ⬝ᵥ v := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  simp only [map_sum, gradientVec, dotProduct]
  refine Finset.sum_congr rfl fun n _ => ?_
  have : Pi.single n (v n) = v n • (Pi.single n (1 : ℝ) : Fin N → ℝ) := by
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  rw [this, map_smul, smul_eq_mul, mul_comm]

/-- **Section M.A** (MWG, p. 927). For `f : ℝ^{N+K} → ℝ^M`, the partial derivative matrix
`D_x f(x, y)`: the `M × N` matrix of `∂fₘ/∂xₙ`. -/
def partialJacobianFst {N K M : ℕ} (f' : ((Fin N → ℝ) × (Fin K → ℝ)) →L[ℝ] (Fin M → ℝ)) :
    Matrix (Fin M) (Fin N) ℝ :=
  jacobian (f'.comp (ContinuousLinearMap.inl ℝ (Fin N → ℝ) (Fin K → ℝ)))

/-- `D_x f(x, y)` has `mn` entry `∂fₘ(x, y)/∂xₙ`: the derivative in direction `(eₙ, 0)`. -/
theorem partialJacobianFst_apply {N K M : ℕ}
    (f' : ((Fin N → ℝ) × (Fin K → ℝ)) →L[ℝ] (Fin M → ℝ)) (m : Fin M) (n : Fin N) :
    partialJacobianFst f' m n = f' (Pi.single n 1, 0) m := rfl

/-- **Section M.A** (MWG, p. 927). The Hessian `D²f(x) = D[∇f(x)]`: the derivative matrix of the
gradient map `y ↦ ∇f(y)`. -/
noncomputable def hessianMatrix {N : ℕ} (f : (Fin N → ℝ) → ℝ) (x : Fin N → ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  jacobian (fderiv ℝ (fun y => gradientVec (fderiv ℝ f y)) x)

/-- **Equation (M.A.1)** (MWG, p. 927), the chain rule: if `g : ℝ^S → ℝ^N` is differentiable at
`x` and `f : ℝ^N → ℝ^M` at `g(x)`, then `f ∘ g` is differentiable at `x` and
`D_x f(g(x)) = Df(g(x)) Dg(x)`. -/
theorem equation_M_A_1 {S N M : ℕ} {g : (Fin S → ℝ) → (Fin N → ℝ)}
    {f : (Fin N → ℝ) → (Fin M → ℝ)} {x : Fin S → ℝ} {g' : (Fin S → ℝ) →L[ℝ] (Fin N → ℝ)}
    {f' : (Fin N → ℝ) →L[ℝ] (Fin M → ℝ)} (hg : HasFDerivAt g g' x) (hf : HasFDerivAt f f' (g x)) :
    HasFDerivAt (f ∘ g) (f'.comp g') x ∧ jacobian (f'.comp g') = jacobian f' * jacobian g' := by
  refine ⟨hf.comp x hg, ?_⟩
  ext m s
  rw [Matrix.mul_apply]
  have := congrFun (jacobian_mulVec f' (g' (Pi.single s 1))) m
  simp only [jacobian, Matrix.of_apply, ContinuousLinearMap.coe_comp, Function.comp_apply]
    at this ⊢
  rw [← this]
  simp [Matrix.mulVec, dotProduct]

/-- **Equation (M.A.2)** (MWG, p. 927), the product rule for `f = g h` with `g, h : ℝ^N → ℝ`:
`Df(x) = g(x) Dh(x) + h(x) Dg(x)`, equivalently `∇f(x) = g(x)∇h(x) + h(x)∇g(x)`. -/
theorem equation_M_A_2 {N : ℕ} {g h : (Fin N → ℝ) → ℝ} {x : Fin N → ℝ}
    {g' h' : (Fin N → ℝ) →L[ℝ] ℝ} (hg : HasFDerivAt g g' x) (hh : HasFDerivAt h h' x) :
    HasFDerivAt (fun y => g y * h y) (g x • h' + h x • g') x ∧
      gradientVec (g x • h' + h x • g') = g x • gradientVec h' + h x • gradientVec g' := by
  refine ⟨hg.fun_mul hh, ?_⟩
  funext n
  simp [gradientVec]

/-- **Equation (M.A.3)** (MWG, p. 927), the product rule for the inner product `f = g·h` of
`g, h : ℝ^N → ℝ^M`: `Df(x) = g(x)·Dh(x) + h(x)·Dg(x)`, where `h(x)·Dg(x) = [h(x)]ᵀDg(x)`. -/
theorem equation_M_A_3 {N M : ℕ} {g h : (Fin N → ℝ) → (Fin M → ℝ)} {x : Fin N → ℝ}
    {g' h' : (Fin N → ℝ) →L[ℝ] (Fin M → ℝ)} (hg : HasFDerivAt g g' x)
    (hh : HasFDerivAt h h' x) :
    ∃ f' : (Fin N → ℝ) →L[ℝ] ℝ, HasFDerivAt (fun y => g y ⬝ᵥ h y) f' x ∧
      gradientVec f' = Matrix.vecMul (g x) (jacobian h') + Matrix.vecMul (h x) (jacobian g') := by
  have hterm : ∀ m ∈ (Finset.univ : Finset (Fin M)),
      HasFDerivAt (fun y => g y m * h y m)
        (g x m • (ContinuousLinearMap.proj m).comp h' +
          h x m • (ContinuousLinearMap.proj m).comp g') x := by
    intro m _
    exact (hasFDerivAt_pi'.mp hg m).fun_mul (hasFDerivAt_pi'.mp hh m)
  refine ⟨_, HasFDerivAt.fun_sum hterm, ?_⟩
  funext n
  simp [gradientVec, Matrix.vecMul, dotProduct, jacobian, Finset.sum_add_distrib]

/-- **Equation (M.A.5)** (MWG, p. 927), the product rule for `f = h g` with `h : ℝ^N → ℝ` and
`g : ℝ^N → ℝ^M`: `Df(x) = h(x) Dg(x) + g(x) Dh(x)`, where `g(x) Dh(x)` is the `M × N` outer
product. -/
theorem equation_M_A_5 {N M : ℕ} {h : (Fin N → ℝ) → ℝ} {g : (Fin N → ℝ) → (Fin M → ℝ)}
    {x : Fin N → ℝ} {h' : (Fin N → ℝ) →L[ℝ] ℝ} {g' : (Fin N → ℝ) →L[ℝ] (Fin M → ℝ)}
    (hh : HasFDerivAt h h' x) (hg : HasFDerivAt g g' x) :
    HasFDerivAt (fun y => h y • g y) (h x • g' + h'.smulRight (g x)) x ∧
      jacobian (h x • g' + h'.smulRight (g x)) =
        h x • jacobian g' + Matrix.vecMulVec (g x) (gradientVec h') := by
  refine ⟨hh.fun_smul hg, ?_⟩
  ext m n
  simp [jacobian, gradientVec, Matrix.vecMulVec, mul_comm]

/-- **Section M.A** (MWG, p. 927). The outer product `g(x) Dh(x)` has rank at most one. -/
theorem rank_vecMulVec_le_one {N M : ℕ} (a : Fin M → ℝ) (b : Fin N → ℝ) :
    Matrix.rank (Matrix.vecMulVec a b) ≤ 1 := by
  rw [Matrix.vecMulVec_eq (Fin 1)]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_width _)

/-- **Equation (M.A.4)** (MWG, p. 927), the product rule for `f = α g` with `α : ℝ → ℝ` and
`g : ℝ → ℝ^M`: `Df(x) = α(x) Dg(x) + α'(x) g(x)`. It is the special case `N = 1` of (M.A.5). -/
theorem equation_M_A_4 {M : ℕ} {α : ℝ → ℝ} {g : ℝ → (Fin M → ℝ)} {x α' : ℝ}
    {g' : Fin M → ℝ} (hα : HasDerivAt α α' x) (hg : HasDerivAt g g' x) :
    HasDerivAt (fun y => α y • g y) (α x • g' + α' • g x) x :=
  hα.smul hg

end MWG.ConsumerChoice

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Homogeneous functions and Euler's formula

MWG, Mathematical Appendix, Section M.B, pp. 928–929.

Functions are defined on the nonnegative orthant `ℝ^N_+` (encoded as functions on `ℝ^N` whose
homogeneity is required only on `ℝ^N_+`). Proved:

* Definition M.B.1 and its two examples (`x₁/x₂` of degree zero, `(x₁x₂)^{1/2}` of degree
  one), and the normalisations `f(1, x₂/x₁, …) = f(x)` (degree zero) and
  `f(1, x₂/x₁, …) = f(x)/x₁` (degree one).
* Theorem M.B.1: the partial derivatives of a degree-`r` homogeneous function are homogeneous
  of degree `r - 1`. The proof holds at every point of `ℝ^N_+`, including boundary points, by
  uniqueness of derivatives within the convex orthant (which has nonempty interior). The
  example `∂(x₁x₂)^{1/2}/∂x₁ = ½(x₂/x₁)^{1/2}` is checked.
* Radial expansions of level sets are level sets; slopes of level sets are constant along rays;
  homothetic functions `h ∘ f` (with `h` strictly increasing) have the same level sets as `f`.
* Theorem M.B.2 (Euler's formula) `∇f(x̄)·x̄ = r f(x̄)`, and its degree-zero case.
-/

namespace MWG.ConsumerChoice

open Filter Topology

/-- **Definition M.B.1** (MWG, p. 928). `f` is homogeneous of degree `r ∈ ℤ` on `ℝ^N_+`:
`f(tx) = t^r f(x)` for every `x ≥ 0` and `t > 0`. -/
def HomogeneousOfDegree {N : ℕ} (f : (Fin N → ℝ) → ℝ) (r : ℤ) : Prop :=
  ∀ x ∈ nonnegOrthant N, ∀ t : ℝ, 0 < t → f (t • x) = t ^ r * f x

/-- **Section M.B** (MWG, p. 928). `f(x₁, x₂) = x₁/x₂` is homogeneous of degree zero. -/
theorem example_M_B_quotient : HomogeneousOfDegree (fun x : Fin 2 → ℝ => x 0 / x 1) 0 := by
  intro x _ t ht
  simp only [Pi.smul_apply, smul_eq_mul, zpow_zero, one_mul]
  rw [mul_div_mul_left _ _ ht.ne']

/-- **Section M.B** (MWG, p. 928). `f(x₁, x₂) = (x₁x₂)^{1/2}` is homogeneous of degree one. -/
theorem example_M_B_sqrt :
    HomogeneousOfDegree (fun x : Fin 2 → ℝ => Real.sqrt (x 0 * x 1)) 1 := by
  intro x hx t ht
  simp only [Pi.smul_apply, smul_eq_mul, zpow_one]
  have : t * x 0 * (t * x 1) = t ^ 2 * (x 0 * x 1) := by ring
  rw [this, Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht.le]

/-- **Section M.B** (MWG, p. 928). If `f` is homogeneous of degree zero and `x₁ > 0`, then
`f(1, x₂/x₁, …, x_N/x₁) = f(x)`. -/
theorem homogeneous_zero_normalize {N : ℕ} {f : (Fin N → ℝ) → ℝ}
    (hf : HomogeneousOfDegree f 0) {x : Fin N → ℝ} (hx : x ∈ nonnegOrthant N) (i : Fin N)
    (hxi : 0 < x i) : f ((x i)⁻¹ • x) = f x ∧ ((x i)⁻¹ • x) i = 1 := by
  refine ⟨?_, by simp [hxi.ne']⟩
  rw [hf x hx _ (inv_pos.mpr hxi), zpow_zero, one_mul]

/-- **Section M.B** (MWG, p. 928). If `f` is homogeneous of degree one and `x₁ > 0`, then
`f(1, x₂/x₁, …, x_N/x₁) = (1/x₁) f(x)`. -/
theorem homogeneous_one_normalize {N : ℕ} {f : (Fin N → ℝ) → ℝ}
    (hf : HomogeneousOfDegree f 1) {x : Fin N → ℝ} (hx : x ∈ nonnegOrthant N) (i : Fin N)
    (hxi : 0 < x i) : f ((x i)⁻¹ • x) = (x i)⁻¹ * f x := by
  rw [hf x hx _ (inv_pos.mpr hxi), zpow_one]

/-- The strictly positive orthant lies in the interior of `ℝ^N_+`, which is therefore
nonempty. -/
theorem interior_nonnegOrthant_nonempty (N : ℕ) : (interior (nonnegOrthant N)).Nonempty := by
  refine ⟨fun _ => 1, ?_⟩
  have hopen : IsOpen (Set.pi Set.univ fun _ : Fin N => Set.Ioi (0 : ℝ)) :=
    isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioi
  apply interior_maximal _ hopen
  · simp
  · intro y hy l
    exact (hy l (Set.mem_univ l)).le

/-- **Theorem M.B.1** (MWG, p. 928). If `f` is homogeneous of degree `r` and differentiable at
`x ∈ ℝ^N_+` and at `tx` (`t > 0`), then its derivative at `tx` is `t^{r-1}` times its derivative
at `x`; in particular every partial derivative `∂f/∂xₙ` is homogeneous of degree `r - 1`. -/
theorem theorem_M_B_1 {N : ℕ} {f : (Fin N → ℝ) → ℝ} {r : ℤ} (hf : HomogeneousOfDegree f r)
    {x : Fin N → ℝ} (hx : x ∈ nonnegOrthant N) {t : ℝ} (ht : 0 < t)
    {f₁ f₂ : (Fin N → ℝ) →L[ℝ] ℝ} (h₁ : HasFDerivAt f f₁ x) (h₂ : HasFDerivAt f f₂ (t • x)) :
    f₂ = t ^ (r - 1) • f₁ := by
  set S := nonnegOrthant N
  have hS : UniqueDiffOn ℝ S :=
    uniqueDiffOn_convex (convex_nonnegOrthant N) (interior_nonnegOrthant_nonempty N)
  -- `y ↦ f(t y)` has derivative `t f₂` at `x`
  have hscale : HasFDerivAt (fun y : Fin N → ℝ => t • y) (t • ContinuousLinearMap.id ℝ _) x :=
    (hasFDerivAt_id x).const_smul t
  have hg : HasFDerivAt (fun y => f (t • y)) (f₂.comp (t • ContinuousLinearMap.id ℝ _)) x :=
    h₂.comp x hscale
  -- `y ↦ t^r f(y)` has derivative `t^r f₁` at `x`, and agrees with `f(t ·)` on `ℝ^N_+`
  have hh : HasFDerivAt (fun y => t ^ r * f y) (t ^ r • f₁) x := h₁.const_mul _
  have hg' : HasFDerivWithinAt (fun y => t ^ r * f y)
      (f₂.comp (t • ContinuousLinearMap.id ℝ _)) S x :=
    hg.hasFDerivWithinAt.congr (fun y hy => (hf y hy t ht).symm) (hf x hx t ht).symm
  have heq := (hS x hx).eq hg' hh.hasFDerivWithinAt
  ext v
  have := congrArg (fun L : (Fin N → ℝ) →L[ℝ] ℝ => L v) heq
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.coe_id', id_eq,
    map_smul, smul_eq_mul] at this
  simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  have htr : t ^ r = t * t ^ (r - 1) := by
    rw [← zpow_one_add₀ ht.ne', add_sub_cancel]
  rw [htr] at this
  have := mul_left_cancel₀ ht.ne' (this.trans (mul_assoc _ _ _))
  exact this

/-- **Theorem M.B.1** (MWG, p. 928), partial-derivative form:
`∂f(tx)/∂xₙ = t^{r-1} ∂f(x)/∂xₙ`. -/
theorem theorem_M_B_1_partial {N : ℕ} {f : (Fin N → ℝ) → ℝ} {r : ℤ}
    (hf : HomogeneousOfDegree f r) {x : Fin N → ℝ} (hx : x ∈ nonnegOrthant N) {t : ℝ}
    (ht : 0 < t) {f₁ f₂ : (Fin N → ℝ) →L[ℝ] ℝ} (h₁ : HasFDerivAt f f₁ x)
    (h₂ : HasFDerivAt f f₂ (t • x)) (n : Fin N) :
    f₂ (Pi.single n 1) = t ^ (r - 1) * f₁ (Pi.single n 1) := by
  rw [theorem_M_B_1 hf hx ht h₁ h₂]
  rfl

/-- **Section M.B** (MWG, p. 928), example of Theorem M.B.1: for `f = (x₁x₂)^{1/2}` at
`x ≫ 0`, `∂f/∂x₁ = ½ (x₂/x₁)^{1/2}`, which is homogeneous of degree zero. -/
theorem example_M_B_sqrt_partial {x : Fin 2 → ℝ} (h0 : 0 < x 0) (h1 : 0 < x 1) :
    HasDerivAt (fun s => Real.sqrt ((x 0 + s) * x 1)) (1 / 2 * Real.sqrt (x 1 / x 0)) 0 ∧
      ∀ t : ℝ, 0 < t → 1 / 2 * Real.sqrt (t * x 1 / (t * x 0)) =
        1 / 2 * Real.sqrt (x 1 / x 0) := by
  constructor
  · have hin : HasDerivAt (fun s => (x 0 + s) * x 1) (x 1) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_add (x 0)).mul_const (x 1)
    have hpos : (x 0 + 0) * x 1 ≠ 0 := by simp only [add_zero]; positivity
    convert hin.sqrt hpos using 1
    simp only [add_zero]
    rw [Real.sqrt_mul h0.le, Real.sqrt_div h1.le]
    have hs0 := Real.sqrt_pos.mpr h0
    have hs1 := Real.sqrt_pos.mpr h1
    field_simp
    rw [Real.sq_sqrt h1.le]
  · intro t ht
    rw [mul_div_mul_left _ _ ht.ne']

/-- **Section M.B** (MWG, p. 928). A radial expansion of a level set of a homogeneous function
is a level set: `f(x) = f(x')` implies `f(tx) = f(tx')` for `t > 0`. -/
theorem level_set_radial {N : ℕ} {f : (Fin N → ℝ) → ℝ} {r : ℤ} (hf : HomogeneousOfDegree f r)
    {x x' : Fin N → ℝ} (hx : x ∈ nonnegOrthant N) (hx' : x' ∈ nonnegOrthant N) {t : ℝ}
    (ht : 0 < t) (h : f x = f x') : f (t • x) = f (t • x') := by
  rw [hf x hx t ht, hf x' hx' t ht, h]

/-- **Section M.B** (MWG, pp. 928–929, Figure M.B.1). For `N = 2`, the slope
`-(∂f/∂x₁)/(∂f/∂x₂)` of the level set of a homogeneous function is the same at `x̄` and at
`tx̄`. -/
theorem level_set_slope_radial {f : (Fin 2 → ℝ) → ℝ} {r : ℤ} (hf : HomogeneousOfDegree f r)
    {x : Fin 2 → ℝ} (hx : x ∈ nonnegOrthant 2) {t : ℝ} (ht : 0 < t)
    {f₁ f₂ : (Fin 2 → ℝ) →L[ℝ] ℝ} (h₁ : HasFDerivAt f f₁ x) (h₂ : HasFDerivAt f f₂ (t • x)) :
    f₂ (Pi.single 0 1) / f₂ (Pi.single 1 1) = f₁ (Pi.single 0 1) / f₁ (Pi.single 1 1) := by
  rw [theorem_M_B_1_partial hf hx ht h₁ h₂, theorem_M_B_1_partial hf hx ht h₁ h₂]
  have : t ^ (r - 1) ≠ 0 := zpow_ne_zero _ ht.ne'
  rw [mul_div_mul_left _ _ this]

/-- **Section M.B** (MWG, p. 929). For a homothetic function `h ∘ f` with `h` strictly
increasing, the level sets of `h ∘ f` coincide with those of `f`. -/
theorem homothetic_level_sets {N : ℕ} {f : (Fin N → ℝ) → ℝ} {h : ℝ → ℝ} (hh : StrictMono h)
    (x : Fin N → ℝ) : {y | h (f y) = h (f x)} = {y | f y = f x} := by
  ext y
  exact hh.injective.eq_iff

/-- **Section M.B** (MWG, p. 929). For a homothetic function `h ∘ f` (`f` homogeneous, `h`
with nonzero derivative), the level-set slopes are also unchanged along rays. -/
theorem homothetic_slope_radial {f : (Fin 2 → ℝ) → ℝ} {r : ℤ} (hf : HomogeneousOfDegree f r)
    {h : ℝ → ℝ} {x : Fin 2 → ℝ} (hx : x ∈ nonnegOrthant 2) {t : ℝ} (ht : 0 < t)
    {f₁ f₂ : (Fin 2 → ℝ) →L[ℝ] ℝ} (h₁ : HasFDerivAt f f₁ x) (h₂ : HasFDerivAt f f₂ (t • x))
    {a b : ℝ} (ha : HasDerivAt h a (f x)) (hb : HasDerivAt h b (f (t • x))) (ha0 : a ≠ 0)
    (hb0 : b ≠ 0) :
    HasFDerivAt (h ∘ f) (a • f₁) x ∧ HasFDerivAt (h ∘ f) (b • f₂) (t • x) ∧
      (b • f₂) (Pi.single 0 1) / (b • f₂) (Pi.single 1 1) =
        (a • f₁) (Pi.single 0 1) / (a • f₁) (Pi.single 1 1) := by
  refine ⟨ha.comp_hasFDerivAt x h₁, hb.comp_hasFDerivAt (t • x) h₂, ?_⟩
  simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  rw [mul_div_mul_left _ _ hb0, mul_div_mul_left _ _ ha0]
  exact level_set_slope_radial hf hx ht h₁ h₂

/-- **Theorem M.B.2** (MWG, p. 929), Euler's formula. If `f` is homogeneous of degree `r` and
differentiable at `x̄ ∈ ℝ^N_+` with derivative `f'`, then `∑ₙ (∂f(x̄)/∂xₙ) x̄ₙ = r f(x̄)`, i.e.
`∇f(x̄)·x̄ = r f(x̄)`. -/
theorem theorem_M_B_2 {N : ℕ} {f : (Fin N → ℝ) → ℝ} {r : ℤ} (hf : HomogeneousOfDegree f r)
    {x : Fin N → ℝ} (hx : x ∈ nonnegOrthant N) {f' : (Fin N → ℝ) →L[ℝ] ℝ}
    (h : HasFDerivAt f f' x) : f' x = r * f x := by
  have hγ : HasDerivAt (fun t : ℝ => t • x) x 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).smul_const x
  have hc := h.comp_hasDerivAt_of_eq (1 : ℝ) hγ (one_smul ℝ x).symm
  have hz : HasDerivAt (fun t : ℝ => t ^ r * f x) ((r : ℝ) * 1 ^ (r - 1) * f x) 1 :=
    (hasDerivAt_zpow r 1 (Or.inl one_ne_zero)).mul_const (f x)
  have hev : (fun t : ℝ => t ^ r * f x) =ᶠ[𝓝 1] (f ∘ fun t : ℝ => t • x) := by
    filter_upwards [lt_mem_nhds one_pos] with t ht
    exact (hf x hx t ht).symm
  have := hc.unique (hz.congr_of_eventuallyEq hev.symm)
  rw [this, one_zpow, mul_one]

/-- **Section M.B** (MWG, p. 929). For a function homogeneous of degree zero, Euler's formula
reads `∑ₙ (∂f(x)/∂xₙ) xₙ = 0`. -/
theorem euler_degree_zero {N : ℕ} {f : (Fin N → ℝ) → ℝ} (hf : HomogeneousOfDegree f 0)
    {x : Fin N → ℝ} (hx : x ∈ nonnegOrthant N) {f' : (Fin N → ℝ) →L[ℝ] ℝ}
    (h : HasFDerivAt f f' x) : f' x = 0 := by
  rw [theorem_M_B_2 hf hx h]
  simp

end MWG.ConsumerChoice

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Negative definite matrices: Theorem M.D.1, dominant diagonals, Theorem M.D.5(i)–(iv)

MWG, Mathematical Appendix, Section M.D, pp. 935–940.

* Characteristic values (roots of `|M - λI| = 0`, complex in general); those of a symmetric
  matrix are real (p. 935).
* Theorem M.D.1: (i) `M` is negative definite iff `M + Mᵀ` is (also for semidefiniteness);
  (ii) a symmetric `M` is negative definite iff all its characteristic values are negative;
  (iii) `M` is negative definite iff `M⁻¹` is; (iv) if `M` is negative definite and `K` is
  diagonal with positive entries, `KM` is stable (every characteristic value has negative real
  part). The book proves (iv) through a cited Lyapunov criterion; here it is proved directly.
* Footnote 9 (p. 938): `|-ₜMₜ| = (-1)^r |ₜMₜ|`.
* Example M.D.1 (p. 937), as statements about `2 × 2` symmetric matrices.
* Definitions M.D.2 (dominant diagonal) and M.D.3 (gross substitute sign pattern) and
  Theorem M.D.5(i)–(iv) (pp. 939–940).
-/

namespace MWG.ConsumerChoice

open Matrix

variable {n : Type*} [Fintype n]

/-- A nonzero real vector has positive squared length. -/
theorem dotProduct_self_pos_of_ne_zero {v : n → ℝ} (hv : v ≠ 0) : 0 < v ⬝ᵥ v := by
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hv (funext hc)
  apply lt_of_lt_of_le (mul_self_pos.mpr hi)
  exact Finset.single_le_sum (f := fun j => v j * v j) (fun j _ => mul_self_nonneg (v j))
    (Finset.mem_univ i)

/-- The quadratic forms of `M` and `Mᵀ` agree: `z·Mᵀz = z·Mz`. -/
theorem dotProduct_transpose_mulVec (M : Matrix n n ℝ) (z : n → ℝ) :
    z ⬝ᵥ Mᵀ.mulVec z = z ⬝ᵥ M.mulVec z := by
  rw [mulVec_transpose, dotProduct_comm, ← dotProduct_mulVec]

/-- **Theorem M.D.1(i)** (MWG, p. 936). `M` is negative definite iff the symmetric matrix
`M + Mᵀ` is negative definite. -/
theorem theorem_M_D_1_i (M : Matrix n n ℝ) : NegDef M ↔ NegDef (M + Mᵀ) := by
  have h : ∀ z : n → ℝ, z ⬝ᵥ (M + Mᵀ).mulVec z = 2 * (z ⬝ᵥ M.mulVec z) := by
    intro z
    rw [add_mulVec, dotProduct_add, dotProduct_transpose_mulVec]
    ring
  constructor
  · intro hM z hz
    rw [h]
    linarith [hM z hz]
  · intro hM z hz
    have := hM z hz
    rw [h] at this
    linarith

/-- **Theorem M.D.1(i)** (MWG, p. 936), semidefinite version (used in Exercise 2.F.9(a)). -/
theorem theorem_M_D_1_i_semidef (M : Matrix n n ℝ) : NegSemidef M ↔ NegSemidef (M + Mᵀ) := by
  have h : ∀ z : n → ℝ, z ⬝ᵥ (M + Mᵀ).mulVec z = 2 * (z ⬝ᵥ M.mulVec z) := by
    intro z
    rw [add_mulVec, dotProduct_add, dotProduct_transpose_mulVec]
    ring
  constructor
  · intro hM z
    rw [h]
    linarith [hM z]
  · intro hM z
    have := hM z
    rw [h] at this
    linarith

/-- **Section M.D** (MWG, p. 935). `μ ∈ ℂ` is a characteristic value (eigenvalue) of the real
matrix `M`: `|M - μI| = 0`. -/
def IsCharacteristicValue [DecidableEq n] (M : Matrix n n ℝ) (μ : ℂ) : Prop :=
  (M.map Complex.ofReal - μ • (1 : Matrix n n ℂ)).det = 0

/-- A real number is a characteristic value iff `|M - μI| = 0` over `ℝ`. -/
theorem isCharacteristicValue_ofReal_iff [DecidableEq n] (M : Matrix n n ℝ) (μ : ℝ) :
    IsCharacteristicValue M μ ↔ (M - μ • (1 : Matrix n n ℝ)).det = 0 := by
  have : M.map Complex.ofReal - (μ : ℂ) • (1 : Matrix n n ℂ) =
      (M - μ • (1 : Matrix n n ℝ)).map Complex.ofReal := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  rw [IsCharacteristicValue, this]
  rw [show ((M - μ • (1 : Matrix n n ℝ)).map Complex.ofReal).det =
    Complex.ofRealHom (M - μ • (1 : Matrix n n ℝ)).det from
      (RingHom.map_det Complex.ofRealHom _).symm]
  simp

/-- **Section M.D** (MWG, p. 935). The characteristic values of a symmetric real matrix are
real. -/
theorem isCharacteristicValue_real [DecidableEq n] {M : Matrix n n ℝ} (hM : M.IsSymm) {μ : ℂ}
    (hμ : IsCharacteristicValue M μ) : μ.im = 0 := by
  obtain ⟨z, hz, hzero⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hμ
  set A := M.map Complex.ofReal with hA
  have hH : A.IsHermitian := by
    ext i j
    simp [hA, Matrix.conjTranspose_apply, hM.apply i j]
  have heig : A *ᵥ z = μ • z := by
    rw [sub_mulVec, sub_eq_zero, smul_mulVec, one_mulVec] at hzero
    exact hzero
  have h1 : star z ⬝ᵥ A *ᵥ z = μ * (star z ⬝ᵥ z) := by
    rw [heig, dotProduct_smul, smul_eq_mul]
  have h2 := hH.star_dotProduct_mulVec_comm z z
  rw [h1, star_mul', star_dotProduct, star_star] at h2
  have hne : star z ⬝ᵥ z ≠ 0 := by
    have hre : (star z ⬝ᵥ z).re = ∑ i, Complex.normSq (z i) := by
      simp only [dotProduct, Complex.re_sum, Pi.star_apply, RCLike.star_def, Complex.mul_re,
        Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
      exact Finset.sum_congr rfl fun i _ => by ring
    obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hz (funext hc)
    have hpos : 0 < ∑ i, Complex.normSq (z i) :=
      lt_of_lt_of_le (Complex.normSq_pos.mpr hi) (Finset.single_le_sum
        (f := fun j => Complex.normSq (z j)) (fun j _ => Complex.normSq_nonneg _)
        (Finset.mem_univ i))
    intro h0
    rw [h0, Complex.zero_re] at hre
    linarith
  have hreal : star (star z ⬝ᵥ z) = star z ⬝ᵥ z := by
    simp only [dotProduct, star_sum, star_mul', Pi.star_apply, star_star]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have h3 : (star μ - μ) * (star z ⬝ᵥ z) = 0 := by
    rw [sub_mul, h2, hreal, sub_self]
  rcases mul_eq_zero.mp h3 with h | h
  · have := congrArg Complex.im h
    simp at this
    linarith
  · exact absurd h hne

/-- **Theorem M.D.1(ii)** (MWG, p. 936). A symmetric matrix is negative definite iff all of its
(real) characteristic values are negative. -/
theorem theorem_M_D_1_ii [DecidableEq n] {M : Matrix n n ℝ} (hM : M.IsSymm) :
    NegDef M ↔ ∀ μ : ℝ, (M - μ • (1 : Matrix n n ℝ)).det = 0 → μ < 0 := by
  constructor
  · intro h μ hμ
    obtain ⟨v, hv, hzero⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hμ
    rw [sub_mulVec, sub_eq_zero, smul_mulVec, one_mulVec] at hzero
    have := h v hv
    rw [hzero, dotProduct_smul, smul_eq_mul] at this
    have hpos : 0 < v ⬝ᵥ v := dotProduct_self_pos_of_ne_zero hv
    nlinarith
  · intro h
    have hneg : (-M).IsHermitian := by
      ext i j
      simp [Matrix.conjTranspose_apply, hM.apply i j]
    have hpd : (-M).PosDef := by
      rw [hneg.posDef_iff_eigenvalues_pos]
      intro i
      set v := hneg.eigenvectorBasis i
      have hv := hneg.mulVec_eigenvectorBasis i
      have hv0 : (⇑v : n → ℝ) ≠ 0 := by
        intro h0
        have := (hneg.eigenvectorBasis).orthonormal.ne_zero i
        apply this
        ext j
        simpa using congrFun h0 j
      have hdet : (M - (-hneg.eigenvalues i) • (1 : Matrix n n ℝ)).det = 0 := by
        rw [← Matrix.exists_mulVec_eq_zero_iff]
        refine ⟨⇑v, hv0, ?_⟩
        rw [sub_mulVec, smul_mulVec, one_mulVec]
        rw [neg_mulVec] at hv
        have : M *ᵥ ⇑v = -(hneg.eigenvalues i • ⇑v) := by rw [← hv, neg_neg]
        rw [this, neg_smul, sub_neg_eq_add, neg_add_cancel]
      have := h _ hdet
      linarith
    have hsymm : (-M).IsSymm := by
      ext i j
      simp [hM.apply i j]
    rw [← (posDefMWG_iff_posDef hsymm)] at hpd
    have := (posDefMWG_iff_neg (-M)).mp hpd
    rwa [neg_neg] at this

/-- **Theorem M.D.1(ii)** (MWG, p. 936), with characteristic values as complex roots: a
symmetric matrix is negative definite iff every characteristic value has negative real part
(all of them being real). -/
theorem theorem_M_D_1_ii_complex [DecidableEq n] {M : Matrix n n ℝ} (hM : M.IsSymm) :
    NegDef M ↔ ∀ μ : ℂ, IsCharacteristicValue M μ → μ.re < 0 := by
  rw [theorem_M_D_1_ii hM]
  constructor
  · intro h μ hμ
    have him := isCharacteristicValue_real hM hμ
    have hμ' : μ = (μ.re : ℂ) := Complex.ext rfl (by simp [him])
    rw [hμ', isCharacteristicValue_ofReal_iff] at hμ
    exact h _ hμ
  · intro h μ hμ
    have := h μ ((isCharacteristicValue_ofReal_iff M μ).mpr hμ)
    simpa using this

/-- A negative definite matrix is nonsingular. -/
theorem NegDef.det_ne_zero [DecidableEq n] {M : Matrix n n ℝ} (h : NegDef M) : M.det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hzero⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have := h v hv
  rw [hzero, dotProduct_zero] at this
  exact lt_irrefl _ this

/-- The forward half of Theorem M.D.1(iii). -/
theorem NegDef.inv [DecidableEq n] {M : Matrix n n ℝ} (h : NegDef M) : NegDef M⁻¹ := by
  have hdet := h.det_ne_zero
  have hU : IsUnit M.det := isUnit_iff_ne_zero.mpr hdet
  intro z hz
  set y := M⁻¹ *ᵥ z with hy
  have hz' : M *ᵥ y = z := by rw [hy, mulVec_mulVec, mul_nonsing_inv _ hU, one_mulVec]
  have hy0 : y ≠ 0 := by
    intro h0
    rw [h0, mulVec_zero] at hz'
    exact hz hz'.symm
  calc z ⬝ᵥ y = (M *ᵥ y) ⬝ᵥ y := by rw [hz']
    _ = y ⬝ᵥ M *ᵥ y := dotProduct_comm _ _
    _ < 0 := h y hy0

/-- **Theorem M.D.1(iii)** (MWG, p. 936). `M` is negative definite iff `M⁻¹` is. -/
theorem theorem_M_D_1_iii [DecidableEq n] (M : Matrix n n ℝ) : NegDef M ↔ NegDef M⁻¹ := by
  refine ⟨NegDef.inv, fun h => ?_⟩
  have h1 := h.det_ne_zero
  rw [Matrix.det_nonsing_inv] at h1
  have hU : IsUnit M.det := isUnit_iff_ne_zero.mpr (by
    intro h0
    rw [h0, Ring.inverse_zero] at h1
    exact h1 rfl)
  have := h.inv
  rwa [Matrix.nonsing_inv_nonsing_inv _ hU] at this

/-- **Section M.D** (MWG, p. 936, footnote 7). A real matrix is stable if all its
characteristic values have negative real parts. -/
def Stable [DecidableEq n] (A : Matrix n n ℝ) : Prop :=
  ∀ μ : ℂ, IsCharacteristicValue A μ → μ.re < 0

/-- **Theorem M.D.1(iv)** (MWG, p. 936). If `M` is negative definite, then for every diagonal
matrix `K` with positive diagonal entries, `KM` is stable. -/
theorem theorem_M_D_1_iv [DecidableEq n] {M : Matrix n n ℝ} (hM : NegDef M) (k : n → ℝ)
    (hk : ∀ i, 0 < k i) : Stable (Matrix.diagonal k * M) := by
  intro μ hμ
  obtain ⟨z, hz, hzero⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hμ
  have heig : (Matrix.diagonal k * M).map Complex.ofReal *ᵥ z = μ • z := by
    rw [sub_mulVec, sub_eq_zero, smul_mulVec, one_mulVec] at hzero
    exact hzero
  have hrow : ∀ i, ∑ j, (M i j : ℂ) * z j = μ * z i / k i := by
    intro i
    have := congrFun heig i
    simp only [mulVec, dotProduct, Matrix.map_apply, Matrix.diagonal_mul, Complex.ofReal_mul,
      Pi.smul_apply, smul_eq_mul] at this
    have hki : (k i : ℂ) ≠ 0 := by exact_mod_cast (hk i).ne'
    rw [eq_div_iff hki, ← this, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  set a : n → ℝ := fun i => (z i).re
  set b : n → ℝ := fun i => (z i).im
  have hab : a ≠ 0 ∨ b ≠ 0 := by
    by_contra hc
    push Not at hc
    apply hz
    funext i
    apply Complex.ext
    · simpa [a] using congrFun hc.1 i
    · simpa [b] using congrFun hc.2 i
  -- the real part of `z̄·Mz` is `a·Ma + b·Mb < 0`
  have hre : (∑ i, star (z i) * ∑ j, (M i j : ℂ) * z j).re =
      a ⬝ᵥ M *ᵥ a + b ⬝ᵥ M *ᵥ b := by
    simp only [Complex.re_sum, Finset.mul_sum, dotProduct, mulVec, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp [a, b, Complex.mul_re, Complex.mul_im]
  have hneg : a ⬝ᵥ M *ᵥ a + b ⬝ᵥ M *ᵥ b < 0 := by
    rcases hab with h | h
    · linarith [hM a h, hM.negSemidef b]
    · linarith [hM.negSemidef a, hM b h]
  -- and it equals `Re μ · ∑ |zᵢ|²/kᵢ`
  have hT : (∑ i, star (z i) * ∑ j, (M i j : ℂ) * z j) =
      μ * ((∑ i, Complex.normSq (z i) / k i : ℝ) : ℂ) := by
    simp only [hrow, Complex.ofReal_sum, Complex.ofReal_div, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.normSq_eq_conj_mul_self]
    simp only [RCLike.star_def]
    have hki : (k i : ℂ) ≠ 0 := by exact_mod_cast (hk i).ne'
    field_simp
  have hTpos : 0 < ∑ i, Complex.normSq (z i) / k i := by
    obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hz (funext hc)
    apply lt_of_lt_of_le (div_pos (Complex.normSq_pos.mpr hi) (hk i))
    exact Finset.single_le_sum (f := fun i => Complex.normSq (z i) / k i)
      (fun j _ => div_nonneg (Complex.normSq_nonneg _) (hk j).le) (Finset.mem_univ i)
  rw [hT, Complex.re_mul_ofReal] at hre
  rw [← hre] at hneg
  by_contra hc
  push Not at hc
  have := mul_nonneg hc hTpos.le
  linarith

/-- **Footnote 9** (MWG, p. 938). `|-A| = (-1)^r |A|` for an `r × r` matrix `A`. -/
theorem det_neg_eq_pow (r : ℕ) (A : Matrix (Fin r) (Fin r) ℝ) : (-A).det = (-1) ^ r * A.det := by
  rw [Matrix.det_neg, Fintype.card_fin]

/-! ### Example M.D.1: `2 × 2` symmetric matrices -/

/-- The quadratic form of a symmetric `2 × 2` matrix. -/
theorem quadratic_two_by_two (f11 f12 f22 : ℝ) (z : Fin 2 → ℝ) :
    z ⬝ᵥ (!![f11, f12; f12, f22]).mulVec z = f11 * z 0 ^ 2 + 2 * f12 * z 0 * z 1 + f22 * z 1 ^ 2
    := by
  simp [dotProduct, mulVec, Fin.sum_univ_two]
  ring

/-- **Example M.D.1** (MWG, p. 937). A symmetric `2 × 2` matrix `[f₁₁ f₁₂; f₁₂ f₂₂]` is negative
definite iff `f₁₁ < 0` and `f₁₁f₂₂ - f₁₂² > 0`. -/
theorem example_M_D_1_negDef (f11 f12 f22 : ℝ) :
    NegDef !![f11, f12; f12, f22] ↔ f11 < 0 ∧ 0 < f11 * f22 - f12 ^ 2 := by
  constructor
  · intro h
    have h1 := h ![1, 0] (by intro h0; simpa using congrFun h0 0)
    have h2 := h ![-f12, f11] (by
      intro h0
      have e1 := congrFun h0 1
      simp at e1
      have : f11 < 0 := by
        have := h1
        rw [quadratic_two_by_two] at this
        simpa using this
      linarith)
    rw [quadratic_two_by_two] at h1 h2
    norm_num at h1 h2
    refine ⟨h1, ?_⟩
    nlinarith
  · rintro ⟨h1, h2⟩ z hz
    rw [quadratic_two_by_two]
    have hz' : z 0 ≠ 0 ∨ z 1 ≠ 0 := by
      by_contra hc
      push Not at hc
      apply hz
      funext i
      fin_cases i
      · exact hc.1
      · exact hc.2
    -- f11 * Q = (f11 z0 + f12 z1)² + (f11 f22 - f12²) z1²
    have key : f11 * (f11 * z 0 ^ 2 + 2 * f12 * z 0 * z 1 + f22 * z 1 ^ 2) =
        (f11 * z 0 + f12 * z 1) ^ 2 + (f11 * f22 - f12 ^ 2) * z 1 ^ 2 := by ring
    have hpos : 0 < (f11 * z 0 + f12 * z 1) ^ 2 + (f11 * f22 - f12 ^ 2) * z 1 ^ 2 := by
      rcases hz' with h | h
      · by_cases h1' : z 1 = 0
        · rw [h1']
          have : f11 * z 0 ≠ 0 := mul_ne_zero h1.ne h
          simp only [mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
            zero_pow, mul_zero, add_zero]
          positivity
        · have := pow_pos (abs_pos.mpr h1') 2
          rw [sq_abs] at this
          nlinarith [sq_nonneg (f11 * z 0 + f12 * z 1)]
      · have := pow_pos (abs_pos.mpr h) 2
        rw [sq_abs] at this
        nlinarith [sq_nonneg (f11 * z 0 + f12 * z 1)]
    nlinarith

/-- **Example M.D.1** (MWG, p. 937). A symmetric `2 × 2` matrix is negative semidefinite iff
`f₁₁ ≤ 0`, `f₂₂ ≤ 0` and `f₁₁f₂₂ - f₁₂² ≥ 0`. -/
theorem example_M_D_1_negSemidef (f11 f12 f22 : ℝ) :
    NegSemidef !![f11, f12; f12, f22] ↔ f11 ≤ 0 ∧ f22 ≤ 0 ∧ 0 ≤ f11 * f22 - f12 ^ 2 := by
  constructor
  · intro h
    have h1 := h ![1, 0]
    have h2 := h ![0, 1]
    rw [quadratic_two_by_two] at h1 h2
    norm_num at h1 h2
    refine ⟨h1, h2, ?_⟩
    by_contra hc
    push Not at hc
    rcases lt_or_eq_of_le h1 with h1' | h1'
    · have h3 := h ![-f12, f11]
      rw [quadratic_two_by_two] at h3
      simp at h3
      nlinarith
    · rw [h1'] at hc
      have hf : f12 ≠ 0 := by
        intro h0
        rw [h0] at hc
        simp at hc
      have h3 := h ![(1 - f22) / (2 * f12), 1]
      rw [quadratic_two_by_two, h1'] at h3
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h3
      have e : 2 * f12 * ((1 - f22) / (2 * f12)) * 1 = 1 - f22 := by field_simp
      nlinarith
  · rintro ⟨h1, h2, h3⟩ z
    rw [quadratic_two_by_two]
    rcases lt_or_eq_of_le h1 with h1' | h1'
    · have key : f11 * (f11 * z 0 ^ 2 + 2 * f12 * z 0 * z 1 + f22 * z 1 ^ 2) =
          (f11 * z 0 + f12 * z 1) ^ 2 + (f11 * f22 - f12 ^ 2) * z 1 ^ 2 := by ring
      have : 0 ≤ f11 * (f11 * z 0 ^ 2 + 2 * f12 * z 0 * z 1 + f22 * z 1 ^ 2) := by
        rw [key]; positivity
      nlinarith
    · have hf : f12 = 0 := by
        rw [h1'] at h3
        nlinarith [sq_nonneg f12]
      rw [h1', hf]
      nlinarith [sq_nonneg (z 1)]

/-! ### Dominant diagonals and gross substitutes -/

/-- **Definition M.D.2** (MWG, p. 939). `M` has a dominant diagonal: there is `p ≫ 0` with
`|pᵢaᵢᵢ| > ∑_{j ≠ i} |pⱼaᵢⱼ|` for every `i`. -/
def DominantDiagonal [DecidableEq n] (M : Matrix n n ℝ) : Prop :=
  ∃ p : n → ℝ, (∀ i, 0 < p i) ∧
    ∀ i, ∑ j ∈ Finset.univ.erase i, |p j * M i j| < |p i * M i i|

/-- **Definition M.D.3** (MWG, p. 939). `M` has the gross substitute sign pattern: every
off-diagonal entry is positive. -/
def GrossSubstituteSign (M : Matrix n n ℝ) : Prop := ∀ i j, i ≠ j → 0 < M i j

/-- **Theorem M.D.5(i)** (MWG, p. 939). A matrix with a dominant diagonal is nonsingular. -/
theorem theorem_M_D_5_i [DecidableEq n] {M : Matrix n n ℝ} (h : DominantDiagonal M) :
    M.det ≠ 0 := by
  obtain ⟨p, hp, hdom⟩ := h
  have hD : (M * Matrix.diagonal p).det ≠ 0 := by
    apply det_ne_zero_of_sum_row_lt_diag
    intro k
    simp only [Matrix.mul_diagonal, Real.norm_eq_abs]
    have := hdom k
    simpa [mul_comm] using this
  rw [Matrix.det_mul, Matrix.det_diagonal] at hD
  exact left_ne_zero_of_mul hD

/-- **Theorem M.D.5(ii)** (MWG, p. 939). A symmetric matrix with a negative and dominant
diagonal is negative definite. -/
theorem theorem_M_D_5_ii [DecidableEq n] {M : Matrix n n ℝ} (hM : M.IsSymm)
    (hneg : ∀ i, M i i < 0) (hdom : DominantDiagonal M) : NegDef M := by
  rw [theorem_M_D_1_ii hM]
  intro μ hμ
  by_contra hc
  push Not at hc
  apply theorem_M_D_5_i (M := M - μ • 1) _ hμ
  obtain ⟨p, hp, hd⟩ := hdom
  refine ⟨p, hp, fun i => ?_⟩
  have hoff : ∀ j ∈ Finset.univ.erase i, (M - μ • (1 : Matrix n n ℝ)) i j = M i j := by
    intro j hj
    have : i ≠ j := fun h => (Finset.mem_erase.mp hj).1 h.symm
    simp [this]
  rw [Finset.sum_congr rfl fun j hj => by rw [hoff j hj]]
  have hii : (M - μ • (1 : Matrix n n ℝ)) i i = M i i - μ := by simp
  rw [hii]
  calc ∑ j ∈ Finset.univ.erase i, |p j * M i j| < |p i * M i i| := hd i
    _ ≤ |p i * (M i i - μ)| := by
      rw [abs_mul, abs_mul, abs_of_pos (hp i), abs_of_neg (hneg i),
        abs_of_neg (by linarith [hneg i])]
      nlinarith [hp i]

/-- **Theorem M.D.5(iii)** (MWG, p. 940). If `M` has the gross substitute sign pattern and
`Mp ≪ 0`, `Mᵀp ≪ 0` for some `p ≫ 0`, then `M` is negative definite. -/
theorem theorem_M_D_5_iii {M : Matrix n n ℝ} (hgs : GrossSubstituteSign M)
    {p : n → ℝ} (hp : ∀ i, 0 < p i) (h1 : ∀ i, (M *ᵥ p) i < 0) (h2 : ∀ i, (Mᵀ *ᵥ p) i < 0) :
    NegDef M := by
  classical
  rw [theorem_M_D_1_i]
  have hsplit : ∀ (f : n → ℝ) i, ∑ j, f j = f i + ∑ j ∈ Finset.univ.erase i, f j := by
    intro f i
    rw [Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have hdiag : ∀ i, M i i < 0 := by
    intro i
    have := h1 i
    simp only [mulVec, dotProduct] at this
    rw [hsplit _ i] at this
    have : 0 ≤ ∑ j ∈ Finset.univ.erase i, M i j * p j :=
      Finset.sum_nonneg fun j hj => mul_nonneg
        (hgs i j (fun h => (Finset.mem_erase.mp hj).1 h.symm)).le (hp j).le
    nlinarith [hp i]
  apply theorem_M_D_5_ii
  · ext i j
    simp [add_comm]
  · intro i
    simp only [Matrix.add_apply, Matrix.transpose_apply]
    linarith [hdiag i]
  · refine ⟨p, hp, fun i => ?_⟩
    have e1 := h1 i
    have e2 := h2 i
    simp only [mulVec, dotProduct, Matrix.transpose_apply] at e1 e2
    rw [hsplit _ i] at e1 e2
    have hoff : ∀ j ∈ Finset.univ.erase i, |p j * (M + Mᵀ) i j| = M i j * p j + M j i * p j := by
      intro j hj
      have hij : i ≠ j := fun h => (Finset.mem_erase.mp hj).1 h.symm
      simp only [Matrix.add_apply, Matrix.transpose_apply]
      rw [abs_of_pos (mul_pos (hp j) (add_pos (hgs i j hij) (hgs j i (Ne.symm hij))))]
      ring
    rw [Finset.sum_congr rfl hoff, Finset.sum_add_distrib]
    simp only [Matrix.add_apply, Matrix.transpose_apply]
    rw [abs_of_neg (mul_neg_of_pos_of_neg (hp i) (by linarith [hdiag i]))]
    linarith

/-- **Theorem M.D.5(iv)** (MWG, p. 940). If `M` has the gross substitute sign pattern and
`Mp = Mᵀp = 0` for some `p ≫ 0`, then deleting any row and the corresponding column gives a
negative definite matrix `M̂`. -/
theorem theorem_M_D_5_iv {N : ℕ} {M : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hgs : GrossSubstituteSign M) {p : Fin (N + 1) → ℝ} (hp : ∀ i, 0 < p i)
    (h1 : M *ᵥ p = 0) (h2 : Mᵀ *ᵥ p = 0) (k : Fin (N + 1)) :
    NegDef (M.submatrix k.succAbove k.succAbove) := by
  apply theorem_M_D_5_iii (p := fun i => p (k.succAbove i))
  · intro i j hij
    exact hgs _ _ (fun h => hij (Fin.succAbove_right_injective h))
  · exact fun i => hp _
  · intro i
    have := congrFun h1 (k.succAbove i)
    simp only [mulVec, dotProduct, Pi.zero_apply] at this
    rw [Fin.sum_univ_succAbove _ k] at this
    simp only [mulVec, dotProduct, Matrix.submatrix_apply]
    have hpos := mul_pos (hgs (k.succAbove i) k (Fin.succAbove_ne k i)) (hp k)
    linarith
  · intro i
    have := congrFun h2 (k.succAbove i)
    simp only [mulVec, dotProduct, Pi.zero_apply, Matrix.transpose_apply] at this
    rw [Fin.sum_univ_succAbove _ k] at this
    simp only [mulVec, dotProduct, Matrix.transpose_apply, Matrix.submatrix_apply]
    have hpos := mul_pos (hgs k (k.succAbove i) (Fin.succAbove_ne k i).symm) (hp k)
    linarith

end MWG.ConsumerChoice

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Determinantal tests for negative (semi)definiteness

MWG, Mathematical Appendix, Theorem M.D.2 (p. 936) with footnote 8, and Exercise 2.F.9(a)
(p. 38).

For an `N × N` matrix `M`, `ₜMₜ` is the leading `r × r` submatrix (first `r` rows and
columns), and `M^π` is `M` with rows and columns permuted by `π`.

* Principal submatrices of negative (semi)definite matrices are negative (semi)definite.
* A (possibly nonsymmetric) positive definite matrix has positive determinant (proved by
  deforming it to the identity through positive definite matrices).
* Theorem M.D.2(iii): a negative definite matrix has `(-1)^r |ₜM^πₜ| > 0` for every `r` and
  every permutation `π`; equivalently `-M` is a P-matrix (footnote 8).
* Theorem M.D.2(i) (Sylvester's criterion): a symmetric `M` is negative definite iff
  `(-1)^r |ₜMₜ| > 0` for `r = 1, …, N`. The book does not carry out the sufficiency proof; it is
  proved here by induction with the Schur complement.
* Exercise 2.F.9(a): definiteness of `A` and of `A + Aᵀ` agree, the leading-minor condition is
  necessary in the nonsymmetric case, and it is not sufficient (`A = [[-1, 4], [0, -1]]`).
-/

namespace MWG.ConsumerChoice

open Matrix

/-- Summing `y·g` for the extension by zero `y` of `z` along an injection `e` gives `∑ zᵢ g(eᵢ)`.
-/
theorem sum_extend_mul {m n : Type*} [Fintype m] [Fintype n] {e : m → n}
    (he : Function.Injective e) (z : m → ℝ) (g : n → ℝ) :
    ∑ j, Function.extend e z 0 j * g j = ∑ i, z i * g (e i) := by
  classical
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image e)) (fun j _ hj => ?_)]
  · rw [Finset.sum_image fun a _ b _ h => he h]
    exact Finset.sum_congr rfl fun i _ => by rw [he.extend_apply]
  · have : ¬ ∃ a, e a = j := fun ⟨a, ha⟩ => hj (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, ha⟩)
    rw [Function.extend_apply' _ _ _ this, Pi.zero_apply, zero_mul]

/-- The quadratic form of a principal submatrix is the quadratic form of `M` at the extension by
zero. -/
theorem quadratic_submatrix {m n : Type*} [Fintype m] [Fintype n]
    (M : Matrix n n ℝ) {e : m → n} (he : Function.Injective e) (z : m → ℝ) :
    z ⬝ᵥ (M.submatrix e e).mulVec z =
      Function.extend e z 0 ⬝ᵥ M.mulVec (Function.extend e z 0) := by
  simp only [dotProduct, mulVec]
  rw [sum_extend_mul he]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  rw [show (∑ x, M (e i) x * Function.extend e z 0 x) =
      ∑ x, Function.extend e z 0 x * M (e i) x from
    Finset.sum_congr rfl fun _ _ => mul_comm _ _, sum_extend_mul he]
  exact Finset.sum_congr rfl fun k _ => by simp [submatrix_apply, mul_comm]

/-- **Section M.D** (MWG, p. 937). Principal submatrices of a negative definite matrix are
negative definite. -/
theorem NegDef.submatrix {m n : Type*} [Fintype m] [Fintype n] {M : Matrix n n ℝ}
    (h : NegDef M) {e : m → n} (he : Function.Injective e) : NegDef (M.submatrix e e) := by
  classical
  intro z hz
  rw [quadratic_submatrix M he]
  apply h
  intro h0
  apply hz
  funext i
  have := congrFun h0 (e i)
  rwa [he.extend_apply] at this

/-- Principal submatrices of a negative semidefinite matrix are negative semidefinite. -/
theorem NegSemidef.submatrix {m n : Type*} [Fintype m] [Fintype n] {M : Matrix n n ℝ}
    (h : NegSemidef M) {e : m → n} (he : Function.Injective e) :
    NegSemidef (M.submatrix e e) := by
  classical
  intro z
  rw [quadratic_submatrix M he]
  exact h _

/-- A matrix positive definite in MWG's sense is nonsingular. -/
theorem PosDefMWG.det_ne_zero {n : Type*} [Fintype n] [DecidableEq n] {B : Matrix n n ℝ}
    (h : PosDefMWG B) : B.det ≠ 0 := by
  have := ((posDefMWG_iff_neg B).mp h).det_ne_zero
  rw [Matrix.det_neg] at this
  intro h0
  rw [h0, mul_zero] at this
  exact this rfl

/-- **Section M.D** (MWG, p. 937). A (possibly nonsymmetric) positive definite matrix has
positive determinant: the path `t ↦ (1 - t)I + tB` stays positive definite, hence nonsingular,
and starts at `det I = 1`. -/
theorem PosDefMWG.det_pos {n : Type*} [Fintype n] [DecidableEq n] {B : Matrix n n ℝ}
    (h : PosDefMWG B) : 0 < B.det := by
  set f : ℝ → ℝ := fun t => ((1 - t) • (1 : Matrix n n ℝ) + t • B).det with hf
  have hcont : Continuous f := by
    apply Continuous.matrix_det
    exact ((continuous_const.sub continuous_id).smul continuous_const).add
      (continuous_id.smul continuous_const)
  have hne : ∀ t ∈ Set.Icc (0 : ℝ) 1, f t ≠ 0 := by
    intro t ht
    apply PosDefMWG.det_ne_zero
    intro z hz
    rw [add_mulVec, smul_mulVec, smul_mulVec, one_mulVec, dotProduct_add, dotProduct_smul,
      dotProduct_smul, smul_eq_mul, smul_eq_mul]
    have hzz := dotProduct_self_pos_of_ne_zero hz
    have hzB := h z hz
    rcases eq_or_lt_of_le ht.1 with h0 | h0
    · rw [← h0]; simp [hzz]
    · nlinarith [ht.2, mul_pos h0 hzB]
  have h0 : f 0 = 1 := by simp [hf]
  have h1 : f 1 = B.det := by simp [hf]
  by_contra hc
  push Not at hc
  have hmem : (0 : ℝ) ∈ Set.Icc (f 1) (f 0) := ⟨by rw [h1]; exact hc, by rw [h0]; norm_num⟩
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc' zero_le_one hcont.continuousOn hmem
  exact hne t ht hft

/-- **Section M.D** (MWG, p. 936). The leading principal `r × r` submatrix `ₜMₜ`. -/
def leadingMinorMatrix {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ) (r : ℕ) (h : r ≤ N) :
    Matrix (Fin r) (Fin r) ℝ :=
  M.submatrix (Fin.castLE h) (Fin.castLE h)

/-- **Section M.D** (MWG, p. 936). `M^π`: rows and columns permuted by `π`. -/
def permuteMatrix {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ) (π : Equiv.Perm (Fin N)) :
    Matrix (Fin N) (Fin N) ℝ :=
  M.submatrix π π

/-- **Theorem M.D.2(iii)** (MWG, p. 936). If `M` is negative definite (not necessarily
symmetric), then `(-1)^r |ₜM^πₜ| > 0` for every `r = 1, …, N` and every permutation `π`. -/
theorem theorem_M_D_2_iii {N : ℕ} {M : Matrix (Fin N) (Fin N) ℝ} (hM : NegDef M) (r : ℕ)
    (h : r ≤ N) (π : Equiv.Perm (Fin N)) :
    0 < (-1) ^ r * (leadingMinorMatrix (permuteMatrix M π) r h).det := by
  have hsub : NegDef (leadingMinorMatrix (permuteMatrix M π) r h) :=
    hM.submatrix (e := π ∘ Fin.castLE h) (π.injective.comp (Fin.castLE_injective h))
  have hpos := ((posDefMWG_iff_neg _).mpr (by rwa [neg_neg])).det_pos
  rw [det_neg_eq_pow] at hpos
  exact hpos

/-- **Footnote 8** (MWG, p. 936). A P-matrix: every principal minor `|ₜM^πₜ|` is positive. -/
def IsPMatrix {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ) : Prop :=
  ∀ r (h : r ≤ N) (π : Equiv.Perm (Fin N)), 1 ≤ r →
    0 < (leadingMinorMatrix (permuteMatrix M π) r h).det

/-- **Footnote 8** (MWG, p. 936). If `M` is negative definite, `-M` is a P-matrix. -/
theorem negDef_neg_isPMatrix {N : ℕ} {M : Matrix (Fin N) (Fin N) ℝ} (hM : NegDef M) :
    IsPMatrix (-M) := by
  intro r h π _
  have := theorem_M_D_2_iii hM r h π
  have e : leadingMinorMatrix (permuteMatrix (-M) π) r h =
      -leadingMinorMatrix (permuteMatrix M π) r h := rfl
  rw [e, det_neg_eq_pow]
  exact this

/-! ### Sylvester's criterion -/

/-- The leading minors of the top-left `N × N` block are leading minors of `A`. -/
theorem leadingMinorMatrix_castSucc {N : ℕ} (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (r : ℕ)
    (h : r ≤ N) :
    leadingMinorMatrix (A.submatrix Fin.castSucc Fin.castSucc) r h =
      leadingMinorMatrix A r (h.trans (Nat.le_succ N)) := rfl

/-- Splitting the quadratic form of a symmetric `(N+1) × (N+1)` matrix along the last
coordinate: `z·Az = y·A'y + 2s (b·y) + c s²`. -/
theorem quadratic_castSucc_split {N : ℕ} (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hA : A.IsSymm) (z : Fin (N + 1) → ℝ) :
    z ⬝ᵥ A *ᵥ z = (fun i : Fin N => z i.castSucc) ⬝ᵥ
        (A.submatrix Fin.castSucc Fin.castSucc) *ᵥ (fun i : Fin N => z i.castSucc) +
      2 * z (Fin.last N) *
        ((fun i : Fin N => A i.castSucc (Fin.last N)) ⬝ᵥ (fun i : Fin N => z i.castSucc)) +
      A (Fin.last N) (Fin.last N) * z (Fin.last N) ^ 2 := by
  have hsym : ∀ i : Fin N, A (Fin.last N) i.castSucc = A i.castSucc (Fin.last N) :=
    fun i => hA.apply i.castSucc (Fin.last N)
  simp only [dotProduct, mulVec, Fin.sum_univ_castSucc, submatrix_apply, mul_add,
    Finset.sum_add_distrib, hsym]
  have h2 : ∑ i : Fin N, z i.castSucc * (A i.castSucc (Fin.last N) * z (Fin.last N)) =
      z (Fin.last N) * ∑ i : Fin N, A i.castSucc (Fin.last N) * z i.castSucc := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [h2]
  ring

/-- Sylvester's criterion (positive definite form): a symmetric matrix whose leading principal
minors are all positive is positive definite. -/
theorem sylvester_posDef : ∀ {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ}, A.IsSymm →
    (∀ r (h : r ≤ N), 1 ≤ r → 0 < (leadingMinorMatrix A r h).det) → PosDefMWG A
  | 0, A, _, _ => fun z hz => absurd (Subsingleton.elim z 0) hz
  | N + 1, A, hA, hmin => by
    set A' := A.submatrix Fin.castSucc Fin.castSucc with hA'
    have hA'symm : A'.IsSymm := by
      ext i j
      simp only [transpose_apply, hA', submatrix_apply]
      exact hA.apply _ _
    have hA'pd : PosDefMWG A' := sylvester_posDef hA'symm (fun r h hr => by
      rw [leadingMinorMatrix_castSucc]
      exact hmin r _ hr)
    have hdetA' : A'.det ≠ 0 := hA'pd.det_ne_zero
    have hUA' : IsUnit A'.det := isUnit_iff_ne_zero.mpr hdetA'
    set b : Fin N → ℝ := fun i => A i.castSucc (Fin.last N) with hb
    set c : ℝ := A (Fin.last N) (Fin.last N) with hc
    set u : Fin N → ℝ := A'⁻¹ *ᵥ b with hu
    have hA'u : A' *ᵥ u = b := by rw [hu, mulVec_mulVec, mul_nonsing_inv _ hUA', one_mulVec]
    -- the determinant factorises through the Schur complement
    have hdet : A.det = A'.det * (c - b ⬝ᵥ u) := by
      let _inst : Invertible A' := A'.invertibleOfIsUnitDet hUA'
      have h11 : (A.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁ = A' := by
        ext i j
        rfl
      rw [← det_submatrix_equiv_self finSumFinEquiv A,
        ← fromBlocks_toBlocks (A.submatrix finSumFinEquiv finSumFinEquiv), h11,
        det_fromBlocks₁₁, invOf_eq_nonsing_inv]
      congr 1
      rw [det_unique]
      have hl : Fin.natAdd N (default : Fin 1) = Fin.last N := by ext; simp
      simp only [toBlocks₂₂, toBlocks₂₁, toBlocks₁₂, Matrix.sub_apply, Matrix.mul_apply,
        of_apply, submatrix_apply, finSumFinEquiv_apply_right, finSumFinEquiv_apply_left, hl]
      rw [hu]
      simp only [dotProduct, mulVec, Finset.mul_sum, Finset.sum_mul]
      congr 1
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      have e1 : A (Fin.last N) (Fin.castAdd 1 i) = b i := hA.apply _ _
      have e2 : A (Fin.castAdd 1 j) (Fin.last N) = b j := rfl
      rw [e1, e2]
      ring
    have hschur : 0 < c - b ⬝ᵥ u := by
      have hApos := hmin (N + 1) le_rfl (Nat.le_add_left 1 N)
      have hA'pos : 0 < A'.det := by
        have := hmin N (Nat.le_succ N)
        rcases Nat.eq_zero_or_pos N with h0 | h0
        · subst h0
          simp
        · exact this h0
      have e : leadingMinorMatrix A (N + 1) le_rfl = A := by
        ext i j
        rfl
      rw [e, hdet] at hApos
      exact pos_of_mul_pos_right hApos hA'pos.le
    -- the quadratic form splits as `(y + s u)·A'(y + s u) + s²(c - b·u)`
    intro z hz
    set y : Fin N → ℝ := fun i => z i.castSucc with hy
    set s : ℝ := z (Fin.last N) with hs
    have hquad : z ⬝ᵥ A *ᵥ z = y ⬝ᵥ A' *ᵥ y + 2 * s * (b ⬝ᵥ y) + c * s ^ 2 :=
      quadratic_castSucc_split A hA z
    have hsplit : z ⬝ᵥ A *ᵥ z =
        (y + s • u) ⬝ᵥ A' *ᵥ (y + s • u) + s ^ 2 * (c - b ⬝ᵥ u) := by
      have hA'sym : ∀ v w : Fin N → ℝ, v ⬝ᵥ A' *ᵥ w = w ⬝ᵥ A' *ᵥ v := by
        intro v w
        rw [dotProduct_mulVec, ← mulVec_transpose, hA'symm.eq, dotProduct_comm]
      have e1 : (y + s • u) ⬝ᵥ A' *ᵥ (y + s • u) =
          y ⬝ᵥ A' *ᵥ y + 2 * s * (b ⬝ᵥ y) + s ^ 2 * (b ⬝ᵥ u) := by
        rw [mulVec_add, mulVec_smul, hA'u, add_dotProduct, dotProduct_add, dotProduct_add,
          smul_dotProduct, smul_dotProduct, dotProduct_smul, dotProduct_smul, hA'sym u y, hA'u]
        simp only [smul_eq_mul]
        rw [dotProduct_comm y b, dotProduct_comm u b]
        ring
      rw [hquad, e1]
      ring
    rw [hsplit]
    by_cases hs0 : s = 0
    · have hy0 : y ≠ 0 := by
        intro h0
        apply hz
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · exact hs0
        · exact congrFun h0 j
      rw [hs0, zero_smul, add_zero]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, add_zero]
      exact hA'pd y hy0
    · have h1 : 0 ≤ (y + s • u) ⬝ᵥ A' *ᵥ (y + s • u) := by
        by_cases hv : y + s • u = 0
        · rw [hv, mulVec_zero, dotProduct_zero]
        · exact (hA'pd _ hv).le
      have h2 : 0 < s ^ 2 * (c - b ⬝ᵥ u) := mul_pos (pow_pos (abs_pos.mpr hs0) 2 |>.trans_eq
        (sq_abs s)) hschur
      linarith

/-- **Theorem M.D.2(i)** (MWG, p. 936), Sylvester's criterion. A symmetric `N × N` matrix is
negative definite iff `(-1)^r |ₜMₜ| > 0` for every `r = 1, …, N`. -/
theorem theorem_M_D_2_i {N : ℕ} {M : Matrix (Fin N) (Fin N) ℝ} (hM : M.IsSymm) :
    NegDef M ↔ ∀ r (h : r ≤ N), 1 ≤ r → 0 < (-1) ^ r * (leadingMinorMatrix M r h).det := by
  constructor
  · intro hND r h _
    have := theorem_M_D_2_iii hND r h 1
    simpa [permuteMatrix] using this
  · intro h
    have hneg : (-M).IsSymm := by
      ext i j
      simp [hM.apply i j]
    have hpd := sylvester_posDef hneg (fun r hr h1 => by
      have e : leadingMinorMatrix (-M) r hr = -leadingMinorMatrix M r hr := rfl
      rw [e, det_neg_eq_pow]
      exact h r hr h1)
    have := (posDefMWG_iff_neg (-M)).mp hpd
    rwa [neg_neg] at this

/-! ### Exercise 2.F.9(a) -/

/-- **Exercise 2.F.9(a)** (MWG, p. 38). An arbitrary matrix `A` is negative definite
(semidefinite) iff `A + Aᵀ` is; the leading-minor condition `(-1)^k |A_kk| > 0` is necessary
for negative definiteness of `A`; and it is not sufficient: `A = [[-1, 4], [0, -1]]` satisfies
it but `(1, 1)·A(1, 1) = 2 > 0`. -/
theorem exercise_2_F_9a :
    (∀ {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ), (NegDef A ↔ NegDef (A + Aᵀ)) ∧
      (NegSemidef A ↔ NegSemidef (A + Aᵀ)) ∧
      (NegDef A → ∀ k (h : k ≤ N), 1 ≤ k → 0 < (-1) ^ k * (leadingMinorMatrix A k h).det)) ∧
    (∀ k (h : k ≤ 2), 1 ≤ k →
      0 < (-1) ^ k * (leadingMinorMatrix !![-1, 4; 0, -1] k h).det) ∧
    ¬ NegDef !![(-1 : ℝ), 4; 0, -1] := by
  refine ⟨fun A => ⟨theorem_M_D_1_i A, theorem_M_D_1_i_semidef A, fun hA k h _ => ?_⟩,
    fun k h hk => ?_, fun hA => ?_⟩
  · simpa [permuteMatrix] using theorem_M_D_2_iii hA k h 1
  · interval_cases k
    · simp [leadingMinorMatrix]
    · simp [leadingMinorMatrix, Matrix.det_fin_two]
  · have := hA ![1, 1] (by intro h0; simpa using congrFun h0 0)
    simp [dotProduct, mulVec, Fin.sum_univ_two] at this
    norm_num at this

end MWG.ConsumerChoice

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The determinantal test for negative semidefiniteness

MWG, Mathematical Appendix, Theorem M.D.2(ii) (p. 936) and its discussion (p. 937).

A symmetric `M` is negative semidefinite iff `(-1)^r |ₜM^πₜ| ≥ 0` for every `r = 1, …, N` and
every permutation `π`. The book does not prove sufficiency; here every principal minor of
`-M` is obtained as a permuted leading minor, the coefficients of `det(I + t(-M))` are sums of
principal minors (Mathlib's `coeff_det_one_add_X_smul_eq_sum_minors`), so this determinant is
at least 1 for `t ≥ 0`, which rules out a negative eigenvalue of `-M`.

The book's example (p. 937) that permutations are needed: `[[0, 0], [0, 1]]` satisfies the
leading-minor conditions but is not negative semidefinite.
-/

namespace MWG.ConsumerChoice

open Matrix Polynomial

/-- Every injection `Fin r → Fin N` is the restriction of a permutation to the first `r`
indices. -/
theorem exists_perm_extend {N r : ℕ} (h : r ≤ N) (f : Fin r → Fin N)
    (hf : Function.Injective f) : ∃ π : Equiv.Perm (Fin N), ∀ i, π (Fin.castLE h i) = f i := by
  classical
  let e : {x // x ∈ Set.range (Fin.castLE h)} ≃ {x // x ∈ Set.range f} :=
    (Equiv.ofInjective _ (Fin.castLE_injective h)).symm.trans (Equiv.ofInjective f hf)
  refine ⟨e.extendSubtype, fun i => ?_⟩
  rw [Equiv.extendSubtype_apply_of_mem e _ ⟨i, rfl⟩]
  simp only [e, Equiv.trans_apply]
  have : (Equiv.ofInjective _ (Fin.castLE_injective h)).symm ⟨Fin.castLE h i, ⟨i, rfl⟩⟩ = i :=
    Equiv.ofInjective_symm_apply (Fin.castLE_injective h) i
  rw [this]
  rfl

/-- Each principal minor (indexed by a set of rows and columns) is a permuted leading minor. -/
theorem principalMinor_eq_permuted {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ) (s : Finset (Fin N)) :
    ∃ π : Equiv.Perm (Fin N),
      (M.submatrix (Subtype.val : s → Fin N) Subtype.val).det =
        (leadingMinorMatrix (permuteMatrix M π) s.card (Finset.card_le_univ s |>.trans
          (by simp))).det := by
  have hr : s.card ≤ N := (Finset.card_le_univ s).trans (by simp)
  obtain ⟨π, hπ⟩ := exists_perm_extend hr (s.orderEmbOfFin rfl)
    (s.orderEmbOfFin rfl).injective
  refine ⟨π, ?_⟩
  have e1 : leadingMinorMatrix (permuteMatrix M π) s.card hr =
      (M.submatrix (Subtype.val : s → Fin N) Subtype.val).submatrix
        (s.orderIsoOfFin rfl).toEquiv (s.orderIsoOfFin rfl).toEquiv := by
    ext i j
    simp only [leadingMinorMatrix, permuteMatrix, submatrix_apply, hπ,
      RelIso.coe_fn_toEquiv, Finset.coe_orderIsoOfFin_apply]
  rw [e1, det_submatrix_equiv_self]

/-- A symmetric real matrix all of whose principal minors are nonnegative is positive
semidefinite. -/
theorem posSemidef_of_principal_minors {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsSymm)
    (hmin : ∀ s : Finset n, 0 ≤ (A.submatrix (Subtype.val : s → n) Subtype.val).det) :
    PosSemidefMWG A := by
  have hH : A.IsHermitian := by
    ext i j
    simp [Matrix.conjTranspose_apply, hA.apply i j]
  rw [posSemidefMWG_iff_posSemidef hA, hH.posSemidef_iff_eigenvalues_nonneg]
  intro i
  by_contra hneg
  push Not at hneg
  have hneg' : hH.eigenvalues i < 0 := hneg
  set μ := hH.eigenvalues i
  set v := hH.eigenvectorBasis i
  have hv := hH.mulVec_eigenvectorBasis i
  have hv0 : (⇑v : n → ℝ) ≠ 0 := by
    intro h0
    have := (hH.eigenvectorBasis).orthonormal.ne_zero i
    apply this
    ext j
    simpa using congrFun h0 j
  set t : ℝ := -μ⁻¹
  have ht : 0 < t := by simp only [t]; exact neg_pos.mpr (inv_lt_zero.mpr hneg')
  have hμ : μ ≠ 0 := hneg'.ne
  -- `I + tA` is singular
  have hsing : (1 + t • A).det = 0 := by
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    refine ⟨⇑v, hv0, ?_⟩
    rw [add_mulVec, one_mulVec, smul_mulVec, hv, smul_smul]
    have : t * μ = -1 := by simp only [t]; rw [neg_mul, inv_mul_cancel₀ hμ]
    rw [this, neg_one_smul, add_neg_cancel]
  -- but `det(I + tA) ≥ 1`
  set P : ℝ[X] := det (1 + (X : ℝ[X]) • A.map C) with hP
  have heval : P.eval t = (1 + t • A).det := by
    rw [hP, ← Polynomial.coe_evalRingHom, RingHom.map_det]
    congr 1
    ext a b
    by_cases hab : a = b
    · subst hab
      simp
      ring
    · simp [hab]
      ring
  have hcoeff : ∀ k, 0 ≤ P.coeff k := by
    intro k
    rw [hP, coeff_det_one_add_X_smul_eq_sum_minors]
    exact Finset.sum_nonneg fun s _ => hmin s
  have hcoeff0 : P.coeff 0 = 1 := by
    rw [hP, coeff_det_one_add_X_smul_eq_sum_minors, Finset.powersetCard_zero]
    simp only [Finset.sum_singleton]
    have : IsEmpty ((∅ : Finset n) : Set n) := by simp
    exact det_isEmpty
  have hge : 1 ≤ P.eval t := by
    rw [eval_eq_sum_range]
    calc (1 : ℝ) = P.coeff 0 * t ^ 0 := by rw [hcoeff0]; simp
      _ ≤ ∑ k ∈ Finset.range (P.natDegree + 1), P.coeff k * t ^ k :=
        Finset.single_le_sum (f := fun k => P.coeff k * t ^ k)
          (fun k _ => mul_nonneg (hcoeff k) (pow_nonneg ht.le k))
          (Finset.mem_range.mpr (Nat.succ_pos _))
  rw [heval, hsing] at hge
  linarith

/-- **Theorem M.D.2(ii)** (MWG, p. 936). A symmetric `N × N` matrix is negative semidefinite
iff `(-1)^r |ₜM^πₜ| ≥ 0` for every `r = 1, …, N` and every permutation `π`. -/
theorem theorem_M_D_2_ii {N : ℕ} {M : Matrix (Fin N) (Fin N) ℝ} (hM : M.IsSymm) :
    NegSemidef M ↔ ∀ r (h : r ≤ N) (π : Equiv.Perm (Fin N)), 1 ≤ r →
      0 ≤ (-1) ^ r * (leadingMinorMatrix (permuteMatrix M π) r h).det := by
  constructor
  · intro hND r h π _
    set S := leadingMinorMatrix (permuteMatrix M π) r h
    have hS : NegSemidef S :=
      hND.submatrix (e := π ∘ Fin.castLE h) (π.injective.comp (Fin.castLE_injective h))
    have hSsymm : (-S).IsSymm := by
      ext i j
      simp [S, leadingMinorMatrix, permuteMatrix, hM.apply]
    have hpsd : PosSemidefMWG (-S) := by
      rw [posSemidefMWG_iff_neg, neg_neg]
      exact hS
    rw [posSemidefMWG_iff_posSemidef hSsymm] at hpsd
    have := hpsd.det_nonneg
    rwa [det_neg_eq_pow] at this
  · intro h
    have hneg : (-M).IsSymm := by
      ext i j
      simp [hM.apply i j]
    have hpsd := posSemidef_of_principal_minors hneg (fun s => by
      obtain ⟨π, hπ⟩ := principalMinor_eq_permuted (-M) s
      rw [hπ]
      rcases Nat.eq_zero_or_pos s.card with h0 | h0
      · have : IsEmpty (Fin s.card) := by rw [h0]; infer_instance
        rw [det_isEmpty]
        exact zero_le_one
      · have e : leadingMinorMatrix (permuteMatrix (-M) π) s.card
            ((Finset.card_le_univ s).trans (by simp)) =
            -leadingMinorMatrix (permuteMatrix M π) s.card
              ((Finset.card_le_univ s).trans (by simp)) := rfl
        rw [e, det_neg_eq_pow]
        exact h _ _ π h0)
    rw [posSemidefMWG_iff_neg, neg_neg] at hpsd
    exact hpsd

/-- **Section M.D** (MWG, p. 937). Permutations are needed in Theorem M.D.2(ii): the matrix
`[[0, 0], [0, 1]]` satisfies `(-1)^r |ₜMₜ| ≥ 0` for `r = 1, 2` but is not negative
semidefinite. -/
theorem theorem_M_D_2_ii_permutations_needed :
    (∀ r (h : r ≤ 2), 1 ≤ r →
      0 ≤ (-1) ^ r * (leadingMinorMatrix !![(0 : ℝ), 0; 0, 1] r h).det) ∧
    ¬ NegSemidef !![(0 : ℝ), 0; 0, 1] := by
  refine ⟨fun r h hr => ?_, fun hns => ?_⟩
  · interval_cases r
    · simp [leadingMinorMatrix]
    · simp [leadingMinorMatrix, Matrix.det_fin_two]
  · have := hns ![0, 1]
    simp [dotProduct, mulVec, Fin.sum_univ_two] at this
    linarith

end MWG.ConsumerChoice

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Definiteness on the hyperplane orthogonal to a positive vector

MWG, Mathematical Appendix, Theorem M.D.4 (p. 939). Let `M` be `N × N` with `Mp = 0` and
`Mᵀp = 0` for some `p ≫ 0`; `T_p = {z : p·z = 0}`; `M̂` deletes row and column `k`.

* (i) If `rank M = N - 1` then `rank M̂ = N - 1`.
* (ii) If `M` is negative definite on `T_p`, then `z·Mz < 0` for every `z` not proportional
  to `p`.
* (iii) `M` is negative definite on `T_p` iff `M̂` is negative definite.

Here `N = n + 1` and the deleted index is `k : Fin (n + 1)`, with `M̂ = M.submatrix k.succAbove
k.succAbove`. In (ii) only `p ≠ 0` is used.
-/

namespace MWG.ConsumerChoice

open Matrix

/-- Removing a multiple of `p` does not change the quadratic form when `Mp = 0` and
`Mᵀp = 0`. -/
theorem quadratic_sub_smul {n : Type*} [Fintype n] {M : Matrix n n ℝ} {p : n → ℝ}
    (h1 : M *ᵥ p = 0) (h2 : Mᵀ *ᵥ p = 0) (z : n → ℝ) (α : ℝ) :
    (z - α • p) ⬝ᵥ M *ᵥ (z - α • p) = z ⬝ᵥ M *ᵥ z := by
  have h2' : p ⬝ᵥ M *ᵥ z = 0 := by
    rw [dotProduct_mulVec, ← mulVec_transpose, h2, zero_dotProduct]
  rw [mulVec_sub, mulVec_smul, h1, smul_zero, sub_zero, sub_dotProduct, smul_dotProduct, h2',
    smul_zero, sub_zero]

/-- **Theorem M.D.4(ii)** (MWG, p. 939). If `Mp = Mᵀp = 0` (`p ≠ 0`) and `z·Mz < 0` for all
nonzero `z ∈ T_p`, then `z·Mz < 0` for every `z` not proportional to `p`. -/
theorem theorem_M_D_4_ii {n : Type*} [Fintype n] {M : Matrix n n ℝ} {p : n → ℝ} (hp : p ≠ 0)
    (h1 : M *ᵥ p = 0) (h2 : Mᵀ *ᵥ p = 0)
    (hT : ∀ z : n → ℝ, p ⬝ᵥ z = 0 → z ≠ 0 → z ⬝ᵥ M *ᵥ z < 0) (z : n → ℝ)
    (hz : ∀ α : ℝ, z ≠ α • p) : z ⬝ᵥ M *ᵥ z < 0 := by
  have hpp := dotProduct_self_pos_of_ne_zero hp
  set α := (p ⬝ᵥ z) / (p ⬝ᵥ p)
  rw [← quadratic_sub_smul h1 h2 z α]
  apply hT
  · rw [dotProduct_sub, dotProduct_smul, smul_eq_mul]
    simp only [α]
    field_simp
    ring
  · intro h0
    exact hz α (sub_eq_zero.mp h0)

/-- Extension by zero along `succAbove k` vanishes at `k`. -/
theorem extend_succAbove_self {n : ℕ} (k : Fin (n + 1)) (y : Fin n → ℝ) :
    Function.extend k.succAbove y 0 k = 0 := by
  rw [Function.extend_apply']
  · rfl
  · rintro ⟨i, hi⟩
    exact Fin.succAbove_ne k i hi

/-- A vector vanishing at `k` is the extension by zero of its restriction. -/
theorem extend_succAbove_restrict {n : ℕ} (k : Fin (n + 1)) {z : Fin (n + 1) → ℝ}
    (hz : z k = 0) : Function.extend k.succAbove (fun i => z (k.succAbove i)) 0 = z := by
  funext j
  rcases Fin.eq_self_or_eq_succAbove k j with h | ⟨i, rfl⟩
  · rw [h, extend_succAbove_self, hz]
  · rw [(Fin.succAbove_right_injective).extend_apply]

/-- **Theorem M.D.4(iii)** (MWG, p. 939). With `p ≫ 0`, `Mp = 0` and `Mᵀp = 0`, `M` is negative
definite on `T_p` iff `M̂` (delete row and column `k`) is negative definite. -/
theorem theorem_M_D_4_iii {n : ℕ} {M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {p : Fin (n + 1) → ℝ} (hp : ∀ i, 0 < p i) (h1 : M *ᵥ p = 0) (h2 : Mᵀ *ᵥ p = 0)
    (k : Fin (n + 1)) :
    (∀ z : Fin (n + 1) → ℝ, p ⬝ᵥ z = 0 → z ≠ 0 → z ⬝ᵥ M *ᵥ z < 0) ↔
      NegDef (M.submatrix k.succAbove k.succAbove) := by
  have hp0 : p ≠ 0 := fun h => by have := hp k; rw [h] at this; exact lt_irrefl _ this
  constructor
  · intro hT y hy
    rw [quadratic_submatrix M Fin.succAbove_right_injective]
    apply theorem_M_D_4_ii hp0 h1 h2 hT
    intro α hα
    have hk := congrFun hα k
    rw [extend_succAbove_self, Pi.smul_apply, smul_eq_mul] at hk
    have hα0 : α = 0 := by
      rcases mul_eq_zero.mp hk.symm with h | h
      · exact h
      · exact absurd h (hp k).ne'
    apply hy
    funext i
    have := congrFun hα (k.succAbove i)
    rwa [Fin.succAbove_right_injective.extend_apply, hα0, zero_smul] at this
  · intro hND z' hpz hz'
    set α := z' k / p k
    set z := z' - α • p with hzdef
    have hzk : z k = 0 := by
      simp only [hzdef, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, α]
      field_simp [(hp k).ne']
      ring
    have hz0 : (fun i => z (k.succAbove i)) ≠ 0 := by
      intro h0
      have hz : z = 0 := by
        rw [← extend_succAbove_restrict k hzk, h0]
        funext j
        rcases Fin.eq_self_or_eq_succAbove k j with h | ⟨i, rfl⟩
        · rw [h, extend_succAbove_self]
          rfl
        · rw [Fin.succAbove_right_injective.extend_apply]
          rfl
      have hz'eq : z' = α • p := sub_eq_zero.mp hz
      have hpp := dotProduct_self_pos_of_ne_zero hp0
      rw [hz'eq, dotProduct_smul, smul_eq_mul] at hpz
      have hα : α = 0 := by
        rcases mul_eq_zero.mp hpz with h | h
        · exact h
        · linarith
      apply hz'
      rw [hz'eq, hα, zero_smul]
    have := hND _ hz0
    rw [quadratic_submatrix M Fin.succAbove_right_injective, extend_succAbove_restrict k hzk,
      hzdef, quadratic_sub_smul h1 h2] at this
    exact this

/-- The rank of a square matrix with two linearly independent kernel vectors is at most its size
minus two. -/
theorem rank_le_of_two_kernel_vectors {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ) {u v : Fin N → ℝ}
    (hu : M *ᵥ u = 0) (hv : M *ᵥ v = 0) (hind : LinearIndependent ℝ ![u, v]) :
    M.rank + 2 ≤ N := by
  have hrn := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  rw [Module.finrank_fin_fun] at hrn
  have hspan : Submodule.span ℝ (Set.range ![u, v]) ≤ LinearMap.ker M.mulVecLin := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · simpa using hu
    · simpa using hv
  have h2 := Submodule.finrank_mono hspan
  rw [finrank_span_eq_card hind, Fintype.card_fin] at h2
  rw [Matrix.rank]
  omega

/-- **Theorem M.D.4(i)** (MWG, p. 939). With `p ≫ 0`, `Mp = 0` and `Mᵀp = 0`: if
`rank M = N - 1`, then `rank M̂ = N - 1`. -/
theorem theorem_M_D_4_i {n : ℕ} {M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {p : Fin (n + 1) → ℝ} (hp : ∀ i, 0 < p i) (h1 : M *ᵥ p = 0) (h2 : Mᵀ *ᵥ p = 0)
    (hrank : M.rank = n) (k : Fin (n + 1)) :
    (M.submatrix k.succAbove k.succAbove).rank = n := by
  set Mh := M.submatrix k.succAbove k.succAbove
  have hdet : Mh.det ≠ 0 := by
    intro hdet
    obtain ⟨y, hy, hMy⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    set z := Function.extend k.succAbove y 0 with hz
    have hzk : z k = 0 := extend_succAbove_self k y
    have hzsA : ∀ i, z (k.succAbove i) = y i := fun i =>
      Fin.succAbove_right_injective.extend_apply _ _ _
    -- rows other than `k`
    have hrows : ∀ i, (M *ᵥ z) (k.succAbove i) = 0 := by
      intro i
      have := congrFun hMy i
      simp only [mulVec, dotProduct, Pi.zero_apply, Mh, submatrix_apply] at this ⊢
      rw [Fin.sum_univ_succAbove _ k, hzk, mul_zero, zero_add]
      simpa only [hzsA] using this
    -- row `k`, from `pᵀM = 0`
    have hrowk : (M *ᵥ z) k = 0 := by
      have hpz : p ⬝ᵥ M *ᵥ z = 0 := by
        rw [dotProduct_mulVec, ← mulVec_transpose, h2, zero_dotProduct]
      rw [dotProduct, Fin.sum_univ_succAbove _ k] at hpz
      simp only [hrows, mul_zero, Finset.sum_const_zero, add_zero] at hpz
      rcases mul_eq_zero.mp hpz with h | h
      · exact absurd h (hp k).ne'
      · exact h
    have hMz : M *ᵥ z = 0 := by
      funext j
      rcases Fin.eq_self_or_eq_succAbove k j with h | ⟨i, rfl⟩
      · rw [h]; exact hrowk
      · exact hrows i
    have hind : LinearIndependent ℝ ![z, p] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      have hk := congrFun hst k
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hzk, mul_zero, zero_add,
        Pi.zero_apply] at hk
      have ht : t = 0 := by
        rcases mul_eq_zero.mp hk with h | h
        · exact h
        · exact absurd h (hp k).ne'
      refine ⟨?_, ht⟩
      rw [ht, zero_smul, add_zero] at hst
      obtain ⟨i, hi⟩ : ∃ i, y i ≠ 0 := by
        by_contra hc
        push Not at hc
        exact hy (funext hc)
      have := congrFun hst (k.succAbove i)
      rw [Pi.smul_apply, hzsA, smul_eq_mul, Pi.zero_apply] at this
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · exact absurd h hi
    have := rank_le_of_two_kernel_vectors M hMz h1 hind
    omega
  have hU : IsUnit Mh := (Matrix.isUnit_iff_isUnit_det Mh).mpr (isUnit_iff_ne_zero.mpr hdet)
  rw [Matrix.rank_of_isUnit Mh hU, Fintype.card_fin]

end MWG.ConsumerChoice

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Productive input–output matrices

MWG, Mathematical Appendix, Theorem M.D.5(v) (p. 940). If all entries of `M` are nonnegative
and `Mz ≪ z` for some `z ≫ 0`, then `(I - M)⁻¹` exists and equals `∑_{k=0}^∞ Mᵏ`.

The book refers to the Appendix of Chapter 5 for the proof. Here: with `θ = maxᵢ (Mz)ᵢ/zᵢ < 1`,
`Mᵏz ≤ θᵏz`, so each entry of `Mᵏ` is bounded by a geometric sequence and `∑ Mᵏ` converges
entrywise to some `T`; telescoping gives `(I - M)T = T(I - M) = I`.
-/

namespace MWG.ConsumerChoice

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Powers of an entrywise nonnegative matrix are entrywise nonnegative. -/
theorem pow_entry_nonneg {M : Matrix n n ℝ} (hM : ∀ i j, 0 ≤ M i j) (k : ℕ) (i j : n) :
    0 ≤ (M ^ k) i j := by
  induction k generalizing i j with
  | zero => simp [Matrix.one_apply]; split_ifs <;> norm_num
  | succ k ih =>
    rw [pow_succ', Matrix.mul_apply]
    exact Finset.sum_nonneg fun l _ => mul_nonneg (hM i l) (ih l j)

/-- **Theorem M.D.5(v)** (MWG, p. 940). If `M` has nonnegative entries and `Mz ≪ z` for some
`z ≫ 0`, then `∑ₖ Mᵏ` converges, `I - M` is invertible, and `(I - M)⁻¹ = ∑ₖ Mᵏ`. -/
theorem theorem_M_D_5_v {M : Matrix n n ℝ} (hM : ∀ i j, 0 ≤ M i j) {z : n → ℝ}
    (hz : ∀ i, 0 < z i) (hMz : ∀ i, (M *ᵥ z) i < z i) :
    Summable (fun k : ℕ => M ^ k) ∧ IsUnit (1 - M) ∧ (1 - M)⁻¹ = ∑' k : ℕ, M ^ k := by
  -- a uniform contraction factor
  obtain ⟨θ, hθ0, hθ1, hθ⟩ : ∃ θ : ℝ, 0 ≤ θ ∧ θ < 1 ∧ ∀ i, (M *ᵥ z) i ≤ θ * z i := by
    rcases isEmpty_or_nonempty n with hn | hn
    · exact ⟨0, le_rfl, one_pos, fun i => (hn.false i).elim⟩
    obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image Finset.univ
      (fun i => (M *ᵥ z) i / z i) Finset.univ_nonempty
    refine ⟨(M *ᵥ z) i₀ / z i₀, ?_, ?_, fun i => ?_⟩
    · apply div_nonneg _ (hz i₀).le
      exact Finset.sum_nonneg fun j _ => mul_nonneg (hM i₀ j) (hz j).le
    · rw [div_lt_one (hz i₀)]; exact hMz i₀
    · have := hi₀ i (Finset.mem_univ i)
      rw [div_le_iff₀ (hz i)] at this
      exact this
  -- `Mᵏ z ≤ θᵏ z`
  have hpow : ∀ k : ℕ, ∀ i, (M ^ k *ᵥ z) i ≤ θ ^ k * z i := by
    intro k
    induction k with
    | zero => intro i; simp
    | succ k ih =>
      intro i
      rw [pow_succ', ← mulVec_mulVec]
      calc (M *ᵥ (M ^ k *ᵥ z)) i ≤ (M *ᵥ (θ ^ k • z)) i := by
            simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
            exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (ih j) (hM i j)
        _ = θ ^ k * (M *ᵥ z) i := by rw [mulVec_smul, Pi.smul_apply, smul_eq_mul]
        _ ≤ θ ^ k * (θ * z i) := mul_le_mul_of_nonneg_left (hθ i) (pow_nonneg hθ0 k)
        _ = θ ^ (k + 1) * z i := by ring
  -- entrywise geometric bounds
  have hentry : ∀ k : ℕ, ∀ i j, (M ^ k) i j ≤ z i / z j * θ ^ k := by
    intro k i j
    have h1 : (M ^ k) i j * z j ≤ (M ^ k *ᵥ z) i :=
      Finset.single_le_sum (f := fun l => (M ^ k) i l * z l)
        (fun l _ => mul_nonneg (pow_entry_nonneg hM k i l) (hz l).le) (Finset.mem_univ j)
    have h2 := (h1.trans (hpow k i))
    rw [div_mul_eq_mul_div, le_div_iff₀ (hz j)]
    linarith
  have hsum : Summable (fun k : ℕ => M ^ k) := by
    exact Pi.summable.mpr fun i => Pi.summable.mpr fun j =>
      Summable.of_nonneg_of_le (fun k => pow_entry_nonneg hM k i j) (fun k => hentry k i j)
        ((summable_geometric_of_lt_one hθ0 hθ1).mul_left _)
  set T := ∑' k : ℕ, M ^ k with hT
  have hT' : HasSum (fun k : ℕ => M ^ k) T := hsum.hasSum
  have hshift : HasSum (fun k : ℕ => M ^ (k + 1)) (T - 1) := by
    have := (hasSum_nat_add_iff' 1).mpr hT'
    simpa using this
  have htel : HasSum (fun k : ℕ => M ^ k - M ^ (k + 1)) 1 := by
    have := hT'.sub hshift
    simpa using this
  have hleft : (1 - M) * T = 1 := by
    have h := hT'.mul_left (1 - M)
    have e : (fun k : ℕ => (1 - M) * M ^ k) = fun k => M ^ k - M ^ (k + 1) := by
      funext k
      rw [sub_mul, one_mul, pow_succ']
    rw [e] at h
    exact h.unique htel
  have hright : T * (1 - M) = 1 := by
    have h := hT'.mul_right (1 - M)
    have e : (fun k : ℕ => M ^ k * (1 - M)) = fun k => M ^ k - M ^ (k + 1) := by
      funext k
      rw [mul_sub, mul_one, pow_succ]
    rw [e] at h
    exact h.unique htel
  refine ⟨hsum, ?_, Matrix.inv_eq_right_inv hleft⟩
  exact (Matrix.isUnit_iff_isUnit_det _).mpr
    (Matrix.isUnit_det_of_right_inverse hleft)

end MWG.ConsumerChoice

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Bordered matrices: Theorem M.D.3 and Example M.D.2

MWG, Mathematical Appendix, Theorem M.D.3 and Example M.D.2 (p. 938–939).

The book's subspace `{z ∈ ℝ^N : Bz = 0}` does not typecheck for an `N × S` matrix `B`; the
intended subspace (as in Example M.D.2, where `B = ∇f(x)`) is `{z : Bᵀz = 0}`. The bordered
matrix of order `r` is `[[ₜMₜ, ₜB], [(ₜB)ᵀ, 0]]`, with `ₜB` the first `r` rows of `B`.

* Theorem M.D.3(i) is false as printed (rank `B = S` is not enough): with `N = 3`, `S = 1`,
  `M = -I` and `B = e₃`, `M` is negative definite on `{z₃ = 0}` but the bordered determinant of
  order `r = 2` vanishes. The corrected statement (top `S × S` block of
  `B` nonsingular) is `theorem_M_D_3_i` in `AppendixMDBorderedTests`.
* Example M.D.2 (`N = 2`, `S = 1`, `B = ∇f`): the bordered determinant equals
  `2f₁f₂f₁₂ - f₁²f₂₂ - f₂²f₁₁` (also after permuting), and for `∇f ≠ 0` the Hessian is negative
  definite (semidefinite) on `{z : ∇f·z = 0}` iff it is `> 0` (`≥ 0`). For `f = x₁x₂` it is
  `2x₁x₂`.
-/

namespace MWG.ConsumerChoice

open Matrix

/-- **Theorem M.D.3** (MWG, p. 938). The bordered matrix of order `r`:
`[[ₜMₜ, ₜB], [(ₜB)ᵀ, 0]]`. -/
def borderedMatrix {N S : ℕ} (M : Matrix (Fin N) (Fin N) ℝ) (B : Matrix (Fin N) (Fin S) ℝ)
    (r : ℕ) (h : r ≤ N) : Matrix (Fin r ⊕ Fin S) (Fin r ⊕ Fin S) ℝ :=
  Matrix.fromBlocks (leadingMinorMatrix M r h) (B.submatrix (Fin.castLE h) id)
    (B.submatrix (Fin.castLE h) id)ᵀ 0

/-- **Theorem M.D.3(i)** (MWG, p. 938), counterexample to the printed statement. For `N = 3`,
`S = 1`, `M = -I` and `B = (0, 0, 1)ᵀ` (rank 1), `M` is negative definite on `{z : Bᵀz = 0}`, but
`(-1)^r |bordered_r| > 0` fails at `r = 2` (the determinant is `0`). -/
theorem theorem_M_D_3_i_counterexample :
    Matrix.rank (!![0; 0; 1] : Matrix (Fin 3) (Fin 1) ℝ) = 1 ∧
      (∀ z : Fin 3 → ℝ, (!![0; 0; 1] : Matrix (Fin 3) (Fin 1) ℝ)ᵀ *ᵥ z = 0 → z ≠ 0 →
        z ⬝ᵥ (-(1 : Matrix (Fin 3) (Fin 3) ℝ)) *ᵥ z < 0) ∧
      ¬ ∀ r (h : r ≤ 3), 2 ≤ r →
        0 < (-1) ^ r * (borderedMatrix (-(1 : Matrix (Fin 3) (Fin 3) ℝ))
          (!![0; 0; 1] : Matrix (Fin 3) (Fin 1) ℝ) r h).det := by
  refine ⟨?_, fun z _ hz => ?_, fun h => ?_⟩
  · apply le_antisymm ((Matrix.rank_le_width _).trans (by norm_num))
    rw [Nat.one_le_iff_ne_zero]
    intro h0
    rw [Matrix.rank, Submodule.finrank_eq_zero] at h0
    have hmem := LinearMap.mem_range_self
      (!![0; 0; 1] : Matrix (Fin 3) (Fin 1) ℝ).mulVecLin (fun _ => 1)
    rw [h0, Submodule.mem_bot] at hmem
    have := congrFun hmem 2
    simp [mulVec, dotProduct] at this
  · rw [neg_mulVec, one_mulVec, dotProduct_neg, neg_neg_iff_pos]
    exact dotProduct_self_pos_of_ne_zero hz
  · have h2 := h 2 (by norm_num) le_rfl
    have hC : ((!![0; 0; 1] : Matrix (Fin 3) (Fin 1) ℝ).submatrix (Fin.castLE
        (by norm_num : 2 ≤ 3)) id)ᵀ = 0 := by
      ext i j
      fin_cases i; fin_cases j <;> rfl
    rw [borderedMatrix, hC, det_fromBlocks_zero₂₁] at h2
    simp at h2

/-- **Example M.D.2** (MWG, p. 938). The `3 × 3` bordered Hessian
`[[f₁₁, f₁₂, f₁], [f₁₂, f₂₂, f₂], [f₁, f₂, 0]]` has determinant
`2f₁f₂f₁₂ - f₁²f₂₂ - f₂²f₁₁`; so does its permutation (p. 939). -/
theorem example_M_D_2_det (f1 f2 f11 f12 f22 : ℝ) :
    (!![f11, f12, f1; f12, f22, f2; f1, f2, 0] : Matrix (Fin 3) (Fin 3) ℝ).det =
        2 * f1 * f2 * f12 - f1 ^ 2 * f22 - f2 ^ 2 * f11 ∧
      (!![f22, f12, f2; f12, f11, f1; f2, f1, 0] : Matrix (Fin 3) (Fin 3) ℝ).det =
        2 * f1 * f2 * f12 - f1 ^ 2 * f22 - f2 ^ 2 * f11 := by
  constructor <;> rw [det_fin_three] <;> simp <;> ring

/-- On the line `{z : f₁z₁ + f₂z₂ = 0}` (with `∇f ≠ 0`) every vector is a multiple of
`(f₂, -f₁)`, and the Hessian form there is `-t² · (bordered determinant)`. -/
theorem example_M_D_2_line {f1 f2 f11 f12 f22 : ℝ} (hf : f1 ≠ 0 ∨ f2 ≠ 0) (z : Fin 2 → ℝ)
    (hz : f1 * z 0 + f2 * z 1 = 0) :
    ∃ t : ℝ, z = t • ![f2, -f1] ∧
      z ⬝ᵥ (!![f11, f12; f12, f22]).mulVec z =
        -(t ^ 2 * (2 * f1 * f2 * f12 - f1 ^ 2 * f22 - f2 ^ 2 * f11)) := by
  have hn : 0 < f1 ^ 2 + f2 ^ 2 := by
    rcases hf with h | h
    · have := pow_pos (abs_pos.mpr h) 2; rw [sq_abs] at this; nlinarith [sq_nonneg f2]
    · have := pow_pos (abs_pos.mpr h) 2; rw [sq_abs] at this; nlinarith [sq_nonneg f1]
  set t := (f2 * z 0 - f1 * z 1) / (f1 ^ 2 + f2 ^ 2)
  have hzt : z = t • ![f2, -f1] := by
    funext i
    fin_cases i
    · simp only [Fin.zero_eta, Pi.smul_apply, Matrix.cons_val_zero, smul_eq_mul, t]
      field_simp
      linear_combination f1 * hz
    · simp only [Fin.mk_one, Pi.smul_apply, Matrix.cons_val_one, Matrix.cons_val_zero,
        smul_eq_mul, t]
      field_simp
      linear_combination f2 * hz
  refine ⟨t, hzt, ?_⟩
  rw [hzt, quadratic_two_by_two]
  simp only [Pi.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul]
  ring

/-- **Example M.D.2** (MWG, p. 938). With `∇f ≠ 0`, the Hessian is negative definite on
`{z ∈ ℝ² : ∇f·z = 0}` iff `2f₁f₂f₁₂ - f₁²f₂₂ - f₂²f₁₁ > 0`. -/
theorem example_M_D_2_negDef {f1 f2 f11 f12 f22 : ℝ} (hf : f1 ≠ 0 ∨ f2 ≠ 0) :
    (∀ z : Fin 2 → ℝ, f1 * z 0 + f2 * z 1 = 0 → z ≠ 0 →
        z ⬝ᵥ (!![f11, f12; f12, f22]).mulVec z < 0) ↔
      0 < 2 * f1 * f2 * f12 - f1 ^ 2 * f22 - f2 ^ 2 * f11 := by
  constructor
  · intro h
    have hw : f1 * f2 + f2 * -f1 = 0 := by ring
    have hne : (![f2, -f1] : Fin 2 → ℝ) ≠ 0 := by
      intro h0
      have e0 := congrFun h0 0
      have e1 := congrFun h0 1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply, neg_eq_zero]
        at e0 e1
      rcases hf with h' | h'
      · exact h' e1
      · exact h' e0
    have := h ![f2, -f1] (by simpa using hw) hne
    obtain ⟨t, ht, hq⟩ := example_M_D_2_line hf ![f2, -f1] (by simpa using hw)
    rw [hq] at this
    have ht1 : t = 1 := by
      have e := congrFun ht 0
      have e' := congrFun ht 1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.smul_apply, smul_eq_mul]
        at e e'
      rcases hf with h' | h'
      · have : f1 * (1 - t) = 0 := by linarith
        rcases mul_eq_zero.mp this with h'' | h''
        · exact absurd h'' h'
        · linarith
      · have : f2 * (1 - t) = 0 := by linarith
        rcases mul_eq_zero.mp this with h'' | h''
        · exact absurd h'' h'
        · linarith
    rw [ht1] at this
    linarith
  · intro hd z hz hz0
    obtain ⟨t, ht, hq⟩ := example_M_D_2_line hf z hz
    rw [hq]
    have ht0 : t ≠ 0 := by
      intro h0
      rw [h0, zero_smul] at ht
      exact hz0 ht
    have := pow_pos (abs_pos.mpr ht0) 2
    rw [sq_abs] at this
    nlinarith

/-- **Example M.D.2** (MWG, p. 939). With `∇f ≠ 0`, the Hessian is negative semidefinite on
`{z : ∇f·z = 0}` iff `2f₁f₂f₁₂ - f₁²f₂₂ - f₂²f₁₁ ≥ 0`. -/
theorem example_M_D_2_negSemidef {f1 f2 f11 f12 f22 : ℝ} (hf : f1 ≠ 0 ∨ f2 ≠ 0) :
    (∀ z : Fin 2 → ℝ, f1 * z 0 + f2 * z 1 = 0 →
        z ⬝ᵥ (!![f11, f12; f12, f22]).mulVec z ≤ 0) ↔
      0 ≤ 2 * f1 * f2 * f12 - f1 ^ 2 * f22 - f2 ^ 2 * f11 := by
  constructor
  · intro h
    have hw : f1 * f2 + f2 * -f1 = 0 := by ring
    have := h ![f2, -f1] (by simpa using hw)
    obtain ⟨t, ht, hq⟩ := example_M_D_2_line hf ![f2, -f1] (by simpa using hw)
    rw [hq] at this
    have ht1 : t = 1 := by
      have e := congrFun ht 0
      have e' := congrFun ht 1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.smul_apply, smul_eq_mul]
        at e e'
      rcases hf with h' | h'
      · have : f1 * (1 - t) = 0 := by linarith
        rcases mul_eq_zero.mp this with h'' | h''
        · exact absurd h'' h'
        · linarith
      · have : f2 * (1 - t) = 0 := by linarith
        rcases mul_eq_zero.mp this with h'' | h''
        · exact absurd h'' h'
        · linarith
    rw [ht1] at this
    linarith
  · intro hd z hz
    obtain ⟨t, -, hq⟩ := example_M_D_2_line hf z hz
    rw [hq]
    nlinarith [sq_nonneg t]

/-- **Example M.D.2** (MWG, p. 938). For `f(x₁, x₂) = x₁x₂` (`f₁ = x₂`, `f₂ = x₁`, `f₁₁ = f₂₂ = 0`,
`f₁₂ = 1`) the bordered determinant is `2x₁x₂`, positive on `ℝ²₊₊`. -/
theorem example_M_D_2_product (x1 x2 : ℝ) (h1 : 0 < x1) (h2 : 0 < x2) :
    (!![0, 1, x2; 1, 0, x1; x2, x1, 0] : Matrix (Fin 3) (Fin 3) ℝ).det = 2 * x1 * x2 ∧
      0 < 2 * x1 * x2 := by
  refine ⟨?_, by positivity⟩
  rw [det_fin_three]
  simp
  ring

end MWG.ConsumerChoice

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Bordered determinantal tests (Theorem M.D.3, corrected)

MWG, Mathematical Appendix, Theorem M.D.3 (p. 938), with the subspace `{z : Bᵀz = 0}`.

* `bordered_det_ne_zero`, `bordered_sign_pos`: if `A` is negative definite on `{z : Cᵀz = 0}`
  and `C` has full column rank, the bordered matrix `[[A, C], [Cᵀ, 0]]` is nonsingular and
  `(-1)^n |·| > 0` (`n` the size of `A`). The sign is found by deforming `A` to `-I` through
  matrices negative definite on the subspace; at `-I` the determinant is `(-1)^n |CᵀC|`.
* `bordered_det_eq`: `|[[A, C], [Cᵀ, εI]]| = ε^S |A - ε⁻¹CCᵀ|` for `ε ≠ 0`.
* `theorem_M_D_3_i` (corrected): if the top `S × S` block of `B` is nonsingular, `M` is negative
  definite on `{z : Bᵀz = 0}` iff `(-1)^r |bordered_r| > 0` for `r = S+1, …, N`. Sufficiency:
  for large `λ` every leading minor of `M - λBBᵀ` has sign `(-1)^r` (by the identity above for
  `r > S`, and by `|λ⁻¹ₜMₜ - ₜB ₜBᵀ| → (-1)^r |ₜB ₜBᵀ|` for `r ≤ S`), so `M - λBBᵀ` is negative
  definite by Sylvester's criterion.
* `theorem_M_D_3_ii_forward`: the necessity half of Theorem M.D.3(ii) as printed (all `r > S`
  and all permutations), with no rank hypothesis.
-/

namespace MWG.ConsumerChoice

open Matrix Filter Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ℕ}

/-- The bordered matrix `[[A, C], [Cᵀ, 0]]`. -/
def bordered (A : Matrix ι ι ℝ) (C : Matrix ι (Fin S) ℝ) : Matrix (ι ⊕ Fin S) (ι ⊕ Fin S) ℝ :=
  fromBlocks A C Cᵀ 0

/-- A bordered matrix whose border has a nonzero kernel vector is singular. -/
theorem bordered_det_eq_zero_of_not_injective {A : Matrix ι ι ℝ} {C : Matrix ι (Fin S) ℝ}
    (hC : ¬ ∀ μ, C *ᵥ μ = 0 → μ = 0) : (bordered A C).det = 0 := by
  push Not at hC
  obtain ⟨μ, hμ, hμ0⟩ := hC
  rw [← exists_mulVec_eq_zero_iff]
  refine ⟨Sum.elim 0 μ, fun h => hμ0 (funext fun j => by simpa using congrFun h (Sum.inr j)),
    ?_⟩
  funext k
  rcases k with i | j
  · have := congrFun hμ i
    simpa [bordered, mulVec, dotProduct, Fintype.sum_sum_type] using this
  · simp [bordered, mulVec, dotProduct, Fintype.sum_sum_type]

/-- If `A` is negative definite on `{z : Cᵀz = 0}` and `C` is injective, the bordered matrix is
nonsingular. -/
theorem bordered_det_ne_zero {A : Matrix ι ι ℝ} {C : Matrix ι (Fin S) ℝ}
    (hA : ∀ z, Cᵀ *ᵥ z = 0 → z ≠ 0 → z ⬝ᵥ A *ᵥ z < 0) (hC : ∀ μ, C *ᵥ μ = 0 → μ = 0) :
    (bordered A C).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, h0⟩ := exists_mulVec_eq_zero_iff.mpr hdet
  set z : ι → ℝ := fun i => v (Sum.inl i)
  set μ : Fin S → ℝ := fun j => v (Sum.inr j)
  have h1 : A *ᵥ z + C *ᵥ μ = 0 := by
    funext i
    have := congrFun h0 (Sum.inl i)
    simpa [bordered, mulVec, dotProduct, Fintype.sum_sum_type, z, μ] using this
  have h2 : Cᵀ *ᵥ z = 0 := by
    funext j
    have := congrFun h0 (Sum.inr j)
    simpa [bordered, mulVec, dotProduct, Fintype.sum_sum_type, z, μ] using this
  have hz : z = 0 := by
    by_contra hz
    have hlt := hA z h2 hz
    have : z ⬝ᵥ A *ᵥ z = 0 := by
      rw [eq_neg_of_add_eq_zero_left h1, dotProduct_neg, dotProduct_mulVec, ← mulVec_transpose,
        h2, zero_dotProduct, neg_zero]
    linarith
  have hμ : μ = 0 := hC μ (by rw [hz, mulVec_zero, zero_add] at h1; exact h1)
  apply hv
  funext k
  rcases k with i | j
  · exact congrFun hz i
  · exact congrFun hμ j

omit [DecidableEq ι] in
/-- `CᵀC` is positive definite when `C` is injective. -/
theorem posDefMWG_transpose_mul {C : Matrix ι (Fin S) ℝ} (hC : ∀ μ, C *ᵥ μ = 0 → μ = 0) :
    PosDefMWG (Cᵀ * C) := by
  intro μ hμ
  rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
  exact dotProduct_self_pos_of_ne_zero (fun h => hμ (hC μ h))

omit [DecidableEq ι] in
/-- `CCᵀ` is positive definite when `Cᵀ` is injective. -/
theorem posDefMWG_mul_transpose {C : Matrix ι (Fin S) ℝ} (hC : ∀ y, Cᵀ *ᵥ y = 0 → y = 0) :
    PosDefMWG (C * Cᵀ) := by
  intro y hy
  rw [← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose]
  exact dotProduct_self_pos_of_ne_zero (fun h => hy (hC y h))

/-- **Theorem M.D.3** (sign of the bordered determinant). If `A` (`n × n`) is negative definite on
`{z : Cᵀz = 0}` and `C` is injective, then `(-1)^n |[[A, C], [Cᵀ, 0]]| > 0`. -/
theorem bordered_sign_pos {A : Matrix ι ι ℝ} {C : Matrix ι (Fin S) ℝ}
    (hA : ∀ z, Cᵀ *ᵥ z = 0 → z ≠ 0 → z ⬝ᵥ A *ᵥ z < 0) (hC : ∀ μ, C *ᵥ μ = 0 → μ = 0) :
    0 < (-1) ^ Fintype.card ι * (bordered A C).det := by
  set f : ℝ → ℝ := fun s =>
    (-1) ^ Fintype.card ι * (bordered ((1 - s) • A - s • (1 : Matrix ι ι ℝ)) C).det with hf
  have hcont : Continuous f := by
    apply continuous_const.mul
    apply Continuous.matrix_det
    exact Continuous.matrix_fromBlocks
      (((continuous_const.sub continuous_id).smul continuous_const).sub
        (continuous_id.smul continuous_const)) continuous_const continuous_const continuous_const
  have hne : ∀ s ∈ Set.Icc (0 : ℝ) 1, f s ≠ 0 := by
    intro s hs
    have hdet := bordered_det_ne_zero (A := (1 - s) • A - s • (1 : Matrix ι ι ℝ)) (C := C)
      (fun z hz hz0 => by
        rw [sub_mulVec, smul_mulVec, smul_mulVec, one_mulVec, dotProduct_sub, dotProduct_smul,
          dotProduct_smul, smul_eq_mul, smul_eq_mul]
        have h1 := hA z hz hz0
        have h2 := dotProduct_self_pos_of_ne_zero hz0
        rcases eq_or_lt_of_le hs.2 with h | h
        · rw [h]; simp; linarith
        · nlinarith [mul_nonneg hs.1 h2.le, mul_pos (sub_pos.mpr h) (neg_pos.mpr h1)]) hC
    simp only [hf]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hdet
  have h1 : 0 < f 1 := by
    have hU : IsUnit (-(1 : Matrix ι ι ℝ)).det := by
      rw [det_neg, det_one, mul_one]
      exact (isUnit_neg_one (α := ℝ)).pow _
    let _inst : Invertible (-(1 : Matrix ι ι ℝ)) := (-(1 : Matrix ι ι ℝ)).invertibleOfIsUnitDet hU
    have hinv : ⅟(-(1 : Matrix ι ι ℝ)) = -1 := by
      rw [invOf_eq_nonsing_inv]
      apply Matrix.inv_eq_right_inv
      rw [neg_mul_neg, Matrix.one_mul]
    simp only [hf, sub_self, zero_smul, one_smul, zero_sub, bordered]
    rw [det_fromBlocks₁₁, hinv, det_neg, det_one, mul_one]
    have e : (0 : Matrix (Fin S) (Fin S) ℝ) - Cᵀ * (-1 : Matrix ι ι ℝ) * C = Cᵀ * C := by
      rw [Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, sub_neg_eq_add, zero_add]
    rw [e, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
    norm_num
    exact (posDefMWG_transpose_mul hC).det_pos
  have h0 : f 0 = (-1) ^ Fintype.card ι * (bordered A C).det := by simp [hf]
  rw [← h0]
  by_contra hc
  push Not at hc
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc zero_le_one hcont.continuousOn
    (show (0 : ℝ) ∈ Set.Icc (f 0) (f 1) from ⟨hc, h1.le⟩)
  exact hne t ht hft

/-- `|[[A, C], [Cᵀ, εI]]| = ε^S |A - ε⁻¹CCᵀ|` for `ε ≠ 0`. -/
theorem bordered_det_eq {A : Matrix ι ι ℝ} {C : Matrix ι (Fin S) ℝ} {ε : ℝ} (hε : ε ≠ 0) :
    (fromBlocks A C Cᵀ (ε • (1 : Matrix (Fin S) (Fin S) ℝ))).det =
      ε ^ S * (A - ε⁻¹ • (C * Cᵀ)).det := by
  have hU : IsUnit (ε • (1 : Matrix (Fin S) (Fin S) ℝ)).det := by
    rw [det_smul, det_one, mul_one, Fintype.card_fin]
    exact isUnit_iff_ne_zero.mpr (pow_ne_zero _ hε)
  let _inst := (ε • (1 : Matrix (Fin S) (Fin S) ℝ)).invertibleOfIsUnitDet hU
  have hinv : ⅟(ε • (1 : Matrix (Fin S) (Fin S) ℝ)) = ε⁻¹ • 1 := by
    rw [invOf_eq_nonsing_inv]
    apply Matrix.inv_eq_right_inv
    rw [smul_mul_smul_comm, mul_inv_cancel₀ hε, one_mul, one_smul]
  rw [det_fromBlocks₂₂, hinv, det_smul, det_one, mul_one, Fintype.card_fin]
  congr 2
  rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]

/-- Extension by zero commutes with the border: `Bᵀẑ = (B_e)ᵀz`. -/
theorem transpose_mulVec_extend {m n : Type*} [Fintype m] [Fintype n] (B : Matrix n (Fin S) ℝ)
    {e : m → n} (he : Function.Injective e) (z : m → ℝ) :
    Bᵀ *ᵥ Function.extend e z 0 = (B.submatrix e id)ᵀ *ᵥ z := by
  funext j
  simp only [mulVec, dotProduct, transpose_apply, submatrix_apply, id]
  rw [show (∑ x, B x j * Function.extend e z 0 x) = ∑ x, Function.extend e z 0 x * B x j from
    Finset.sum_congr rfl fun _ _ => mul_comm _ _, sum_extend_mul he]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

/-- Restricting a quadratic form that is negative definite on `{z : Bᵀz = 0}` to a set of
coordinates gives a form negative definite on the corresponding subspace. -/
theorem negDef_on_ker_submatrix {m n : Type*} [Fintype m] [Fintype n] {M : Matrix n n ℝ}
    {B : Matrix n (Fin S) ℝ} (hM : ∀ z, Bᵀ *ᵥ z = 0 → z ≠ 0 → z ⬝ᵥ M *ᵥ z < 0)
    {e : m → n} (he : Function.Injective e) :
    ∀ z, (B.submatrix e id)ᵀ *ᵥ z = 0 → z ≠ 0 → z ⬝ᵥ (M.submatrix e e) *ᵥ z < 0 := by
  classical
  intro z hz hz0
  rw [quadratic_submatrix M he]
  apply hM
  · rw [transpose_mulVec_extend B he]; exact hz
  · intro h0
    apply hz0
    funext i
    have := congrFun h0 (e i)
    rwa [he.extend_apply] at this

/-- The leading rows of `B` from row `r ≥ S` contain the top block `B₁`: if `B₁` is nonsingular
the leading `r` rows have full column rank. -/
theorem leadingRows_injective {N r : ℕ} {B : Matrix (Fin N) (Fin S) ℝ} (hSN : S ≤ N)
    (hB : (B.submatrix (Fin.castLE hSN) id).det ≠ 0) (hrN : r ≤ N) (hSr : S ≤ r) :
    ∀ μ, (B.submatrix (Fin.castLE hrN) id) *ᵥ μ = 0 → μ = 0 := by
  intro μ hμ
  by_contra hne
  apply hB
  rw [← exists_mulVec_eq_zero_iff]
  refine ⟨μ, hne, funext fun i => ?_⟩
  have := congrFun hμ (Fin.castLE hSr i)
  simpa [mulVec, dotProduct] using this

/-- For `r ≤ S`, the leading `r` rows of `B` have full row rank when `B₁` is nonsingular. -/
theorem leadingRows_transpose_injective {N r : ℕ} {B : Matrix (Fin N) (Fin S) ℝ} (hSN : S ≤ N)
    (hB : (B.submatrix (Fin.castLE hSN) id).det ≠ 0) (hrN : r ≤ N) (hrS : r ≤ S) :
    ∀ y, (B.submatrix (Fin.castLE hrN) id)ᵀ *ᵥ y = 0 → y = 0 := by
  classical
  intro y hy
  have he : Function.Injective (Fin.castLE hrS) := Fin.castLE_injective hrS
  have hT : (B.submatrix (Fin.castLE hSN) id)ᵀ *ᵥ Function.extend (Fin.castLE hrS) y 0 = 0 := by
    rw [transpose_mulVec_extend _ he]
    exact hy
  have hdetT : ((B.submatrix (Fin.castLE hSN) id)ᵀ).det ≠ 0 := by rwa [det_transpose]
  by_contra hne
  apply hdetT
  rw [← exists_mulVec_eq_zero_iff]
  refine ⟨_, fun h0 => hne (funext fun i => ?_), hT⟩
  have := congrFun h0 (Fin.castLE hrS i)
  rwa [he.extend_apply] at this

/-- **Theorem M.D.3(i)** (MWG, p. 938), corrected. Let `M` be symmetric `N × N` and `B` an
`N × S` matrix whose top `S × S` block is nonsingular. Then `M` is negative definite on
`{z : Bᵀz = 0}` iff `(-1)^r |[[ₜMₜ, ₜB], [(ₜB)ᵀ, 0]]| > 0` for `r = S+1, …, N`. -/
theorem theorem_M_D_3_i {N : ℕ} {M : Matrix (Fin N) (Fin N) ℝ} (hM : M.IsSymm)
    (B : Matrix (Fin N) (Fin S) ℝ) (hSN : S ≤ N)
    (hB : (B.submatrix (Fin.castLE hSN) id).det ≠ 0) :
    (∀ z, Bᵀ *ᵥ z = 0 → z ≠ 0 → z ⬝ᵥ M *ᵥ z < 0) ↔
      ∀ r (h : r ≤ N), S < r → 0 < (-1) ^ r * (borderedMatrix M B r h).det := by
  constructor
  · intro hND r h hr
    have := bordered_sign_pos (A := leadingMinorMatrix M r h) (C := B.submatrix (Fin.castLE h) id)
      (negDef_on_ker_submatrix hND (Fin.castLE_injective h))
      (leadingRows_injective hSN hB h hr.le)
    simpa [bordered, borderedMatrix] using this
  · intro hsign
    -- every leading minor of `M - λBBᵀ` eventually has sign `(-1)^r`
    have hev : ∀ r ∈ Finset.Icc 1 N, ∀ᶠ lam : ℝ in atTop, ∀ h : r ≤ N,
        0 < (-1) ^ r * (leadingMinorMatrix (M - lam • (B * Bᵀ)) r h).det := by
      intro r hr
      have hrN : r ≤ N := (Finset.mem_Icc.mp hr).2
      set A := leadingMinorMatrix M r hrN
      set C := B.submatrix (Fin.castLE hrN) id
      have hsub : ∀ lam : ℝ,
          leadingMinorMatrix (M - lam • (B * Bᵀ)) r hrN = A - lam • (C * Cᵀ) := by
        intro lam
        ext i j
        simp [A, C, leadingMinorMatrix, Matrix.mul_apply]
      have hpos : ∀ᶠ lam : ℝ in atTop, 0 < lam := eventually_gt_atTop 0
      have hinv := tendsto_inv_atTop_zero (𝕜 := ℝ)
      rcases le_or_gt r S with hrS | hrS
      · set g : ℝ → ℝ := fun ε => (-1) ^ r * (ε • A - C * Cᵀ).det with hg
        have hgc : Continuous g := continuous_const.mul
          ((continuous_id.smul continuous_const).sub continuous_const).matrix_det
        have hg0 : 0 < g 0 := by
          simp only [hg, zero_smul, zero_sub, det_neg, Fintype.card_fin, ← mul_assoc, ← pow_add,
            ← two_mul, pow_mul]
          norm_num
          exact (posDefMWG_mul_transpose
            (leadingRows_transpose_injective hSN hB hrN hrS)).det_pos
        filter_upwards [hpos, hinv.eventually (hgc.continuousAt.eventually (lt_mem_nhds hg0))]
          with lam hlam hglam _
        rw [hsub]
        have e : A - lam • (C * Cᵀ) = lam • (lam⁻¹ • A - C * Cᵀ) := by
          rw [smul_sub, smul_smul, mul_inv_cancel₀ hlam.ne', one_smul]
        rw [e, det_smul, Fintype.card_fin]
        have : 0 < lam ^ r * g lam⁻¹ := mul_pos (pow_pos hlam r) hglam
        simp only [hg] at this
        linarith [show (-1) ^ r * (lam ^ r * (lam⁻¹ • A - C * Cᵀ).det) =
          lam ^ r * ((-1) ^ r * (lam⁻¹ • A - C * Cᵀ).det) by ring]
      · set k : ℝ → ℝ := fun ε =>
          (-1) ^ r * (fromBlocks A C Cᵀ (ε • (1 : Matrix (Fin S) (Fin S) ℝ))).det with hk
        have hkc : Continuous k := continuous_const.mul
          (Continuous.matrix_fromBlocks continuous_const continuous_const continuous_const
            (continuous_id.smul continuous_const)).matrix_det
        have hk0 : 0 < k 0 := by
          simpa [hk, borderedMatrix, A, C] using hsign r hrN hrS
        filter_upwards [hpos, hinv.eventually (hkc.continuousAt.eventually (lt_mem_nhds hk0))]
          with lam hlam hklam _
        rw [hsub]
        have e := bordered_det_eq (A := A) (C := C) (inv_ne_zero hlam.ne')
        rw [inv_inv] at e
        have hdet : (A - lam • (C * Cᵀ)).det =
            (fromBlocks A C Cᵀ (lam⁻¹ • (1 : Matrix (Fin S) (Fin S) ℝ))).det / lam⁻¹ ^ S := by
          rw [e]
          field_simp
        rw [hdet, mul_div_assoc']
        exact div_pos hklam (pow_pos (inv_pos.mpr hlam) S)
    obtain ⟨lam, hlam⟩ := ((eventually_all_finset _).mpr hev).exists
    have hsymm : (M - lam • (B * Bᵀ)).IsSymm := by
      ext i j
      simp [hM.apply i j, Matrix.mul_apply, mul_comm]
    have hND := (theorem_M_D_2_i hsymm).mpr (fun r h hr => hlam r (Finset.mem_Icc.mpr ⟨hr, h⟩) h)
    intro z hz hz0
    have := hND z hz0
    rwa [sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul, ← mulVec_mulVec, hz,
      mulVec_zero, dotProduct_zero, smul_zero, sub_zero] at this

/-- **Theorem M.D.3(ii)** (MWG, p. 938), necessity. If the symmetric `M` is negative
semidefinite on `{z : Bᵀz = 0}`, then `(-1)^r |[[ₜM^πₜ, ₜB^π], [(ₜB^π)ᵀ, 0]]| ≥ 0` for every
`r > S` and every permutation `π` (rows and columns of `M`, rows of `B`). -/
theorem theorem_M_D_3_ii_forward {N : ℕ} {M : Matrix (Fin N) (Fin N) ℝ}
    (B : Matrix (Fin N) (Fin S) ℝ) (hNSD : ∀ z, Bᵀ *ᵥ z = 0 → z ⬝ᵥ M *ᵥ z ≤ 0)
    (r : ℕ) (h : r ≤ N) (π : Equiv.Perm (Fin N)) :
    0 ≤ (-1) ^ r * (borderedMatrix (permuteMatrix M π) (B.submatrix π id) r h).det := by
  classical
  set e : Fin r → Fin N := π ∘ Fin.castLE h
  have he : Function.Injective e := π.injective.comp (Fin.castLE_injective h)
  set A := M.submatrix e e
  set C := B.submatrix e id
  have hbm : ∀ ε : ℝ, borderedMatrix (permuteMatrix M π) (B.submatrix π id) r h =
      bordered A C := fun _ => rfl
  rw [hbm 0]
  by_cases hC : ∀ μ, C *ᵥ μ = 0 → μ = 0
  · set k : ℝ → ℝ := fun ε => (-1) ^ r * (bordered (A - ε • (1 : Matrix (Fin r) (Fin r) ℝ)) C).det
      with hk
    have hkc : Continuous k := continuous_const.mul
      (Continuous.matrix_fromBlocks (continuous_const.sub (continuous_id.smul continuous_const))
        continuous_const continuous_const continuous_const).matrix_det
    have hkpos : ∀ ε : ℝ, 0 < ε → 0 < k ε := by
      intro ε hε
      have := bordered_sign_pos (A := A - ε • (1 : Matrix (Fin r) (Fin r) ℝ)) (C := C)
        (fun z hz hz0 => by
          rw [sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul]
          have h1 : z ⬝ᵥ A *ᵥ z ≤ 0 := by
            rw [quadratic_submatrix M he]
            apply hNSD
            rw [transpose_mulVec_extend B he]
            exact hz
          nlinarith [dotProduct_self_pos_of_ne_zero hz0]) hC
      simpa [hk] using this
    have hk0 : k 0 = (-1) ^ r * (bordered A C).det := by simp [hk]
    rw [← hk0]
    apply ge_of_tendsto (hkc.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0)))
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (hkpos ε hε).le
  · rw [bordered_det_eq_zero_of_not_injective hC, mul_zero]

end MWG.ConsumerChoice

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The semidefinite bordered test (Theorem M.D.3(ii), sufficiency)

MWG, Mathematical Appendix, Theorem M.D.3(ii) (p. 938). With `{z : Bᵀz = 0}` for the printed
`{z : Bz = 0}`, and `B` of rank `S` in the form "some `S` rows of `B` are linearly independent":
if `(-1)^r |[[ₜM^πₜ, ₜB^π], [(ₜB^π)ᵀ, 0]]| ≥ 0` for every `r = S+1, …, N` and every permutation
`π`, then the symmetric `M` is negative semidefinite on `{z : Bᵀz = 0}`.

* `det_add_diagonal_expansion`: `|H + diag d| = ∑_W (∏_{i ∉ W} dᵢ) |H_W|` (all `dᵢ ≠ 0`), from
  Mathlib's expansion of `det (1 + X • K)` in principal minors.
* `bordered_perturbation_expansion`: `(-1)^n |[[A - εI, C], [Cᵀ, 0]]| =
  ∑_U ε^{n-|U|} (-1)^{|U|} |[[A_U, C_U], [C_Uᵀ, 0]]|`, by letting the border diagonal tend to 0.
* With the rows reordered so that the first `S` rows of `B` are independent, every term is
  `≥ 0` and the term of those `S` rows is `> 0`, so corrected Theorem M.D.3(i) applies to
  `M - εI` for every `ε > 0`.
-/

namespace MWG.ConsumerChoice

open Matrix Polynomial Filter Topology

/-- The sum of all principal minors: `|I + K| = ∑_W |K_W|`. -/
theorem det_one_add_eq_sum_minors {n : Type*} [Fintype n] [DecidableEq n] (K : Matrix n n ℝ) :
    (1 + K).det = ∑ W : Finset n, (K.submatrix (Subtype.val : W → n) Subtype.val).det := by
  set P : ℝ[X] := det (1 + (X : ℝ[X]) • K.map C) with hP
  have heval : P.eval 1 = (1 + K).det := by
    rw [hP, ← Polynomial.coe_evalRingHom, RingHom.map_det]
    congr 1
    ext a b
    by_cases hab : a = b
    · subst hab
      simp
    · simp [hab]
  have hdeg : P.natDegree < Fintype.card n + 1 := by
    have := natDegree_det_X_add_C_le K (1 : Matrix n n ℝ)
    rw [Matrix.map_one _ (map_zero C) (map_one C), add_comm] at this
    exact Nat.lt_succ_of_le this
  rw [← heval, eval_eq_sum_range' hdeg]
  simp only [one_pow, mul_one]
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (g := Finset.card)
    (t := Finset.range (Fintype.card n + 1))
    (fun W _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.card_le_univ W)))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hP, coeff_det_one_add_X_smul_eq_sum_minors, Finset.powersetCard_eq_filter,
    Finset.powerset_univ]

/-- **Expansion of a diagonally perturbed determinant.** For `dᵢ ≠ 0`,
`|H + diag d| = ∑_W (∏_{i ∉ W} dᵢ) |H_W|`. -/
theorem det_add_diagonal_expansion {n : Type*} [Fintype n] [DecidableEq n] (H : Matrix n n ℝ)
    {d : n → ℝ} (hd : ∀ i, d i ≠ 0) :
    (H + diagonal d).det =
      ∑ W : Finset n, (∏ i ∈ Wᶜ, d i) * (H.submatrix (Subtype.val : W → n) Subtype.val).det := by
  have hfac : H + diagonal d = diagonal d * (1 + diagonal (fun i => (d i)⁻¹) * H) := by
    rw [Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, diagonal_mul_diagonal]
    have : (fun i => d i * (d i)⁻¹) = fun _ => (1 : ℝ) := funext fun i => mul_inv_cancel₀ (hd i)
    rw [this, diagonal_one, Matrix.one_mul, add_comm]
  rw [hfac, det_mul, det_diagonal, det_one_add_eq_sum_minors, Finset.mul_sum]
  refine Finset.sum_congr rfl fun W _ => ?_
  have hsub : (diagonal (fun i => (d i)⁻¹) * H).submatrix (Subtype.val : W → n) Subtype.val =
      diagonal (fun i : W => (d i)⁻¹) * H.submatrix Subtype.val Subtype.val := by
    ext a b
    simp [diagonal_mul]
  rw [hsub, det_mul, det_diagonal, ← Finset.prod_mul_prod_compl W d, ← mul_assoc]
  congr 1
  rw [mul_comm (∏ i ∈ W, d i), mul_assoc]
  have : (∏ i ∈ W, d i) * ∏ i : W, (d i)⁻¹ = 1 := by
    rw [← Finset.prod_coe_sort W d, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun i _ => mul_inv_cancel₀ (hd i)
  rw [this, mul_one]

/-- The principal submatrix of a bordered matrix on `U ⊔ (all border indices)` is the bordered
matrix of the principal submatrix on `U`. -/
theorem det_bordered_submatrix_disjSum {ι : Type*} [DecidableEq ι] {S : ℕ}
    (A : Matrix ι ι ℝ) (C : Matrix ι (Fin S) ℝ) (U : Finset ι) :
    ((bordered A C).submatrix
      (Subtype.val : ↥(U.disjSum (Finset.univ : Finset (Fin S))) → ι ⊕ Fin S)
      Subtype.val).det =
      (bordered (A.submatrix (Subtype.val : U → ι) Subtype.val)
        (C.submatrix Subtype.val id)).det := by
  let f : U ⊕ Fin S → ↥(U.disjSum (Finset.univ : Finset (Fin S))) :=
    Sum.elim (fun u => ⟨Sum.inl u.1, Finset.inl_mem_disjSum.mpr u.2⟩)
      (fun j => ⟨Sum.inr j, Finset.inr_mem_disjSum.mpr (Finset.mem_univ j)⟩)
  have hf : Function.Bijective f := by
    constructor
    · rintro (a | a) (b | b) h <;> have h' := congrArg Subtype.val h
      · simp only [f, Sum.elim_inl, Sum.inl.injEq] at h'
        exact congrArg Sum.inl (Subtype.ext h')
      · simp [f] at h'
      · simp [f] at h'
      · simp only [f, Sum.elim_inr, Sum.inr.injEq] at h'
        rw [h']
    · rintro ⟨x | j, hx⟩
      · exact ⟨Sum.inl ⟨x, Finset.inl_mem_disjSum.mp hx⟩, rfl⟩
      · exact ⟨Sum.inr j, rfl⟩
  rw [← det_submatrix_equiv_self (Equiv.ofBijective f hf)]
  congr 1
  ext a b
  rcases a with a | a <;> rcases b with b | b <;> rfl

/-- **Expansion of the perturbed bordered determinant.** For `ε ≠ 0`,
`|[[A - εI, C], [Cᵀ, 0]]| = ∑_U (-ε)^{n-|U|} |[[A_U, C_U], [C_Uᵀ, 0]]|`. -/
theorem bordered_perturbation_expansion {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ℕ}
    (A : Matrix ι ι ℝ) (C : Matrix ι (Fin S) ℝ) {ε : ℝ} (hε : ε ≠ 0) :
    (bordered (A - ε • (1 : Matrix ι ι ℝ)) C).det =
      ∑ U : Finset ι, (-ε) ^ (Fintype.card ι - U.card) *
        (bordered (A.submatrix (Subtype.val : U → ι) Subtype.val)
          (C.submatrix Subtype.val id)).det := by
  set H := bordered A C
  set d : ℝ → ι ⊕ Fin S → ℝ := fun δ => Sum.elim (fun _ => -ε) (fun _ => -δ) with hd
  have hdc : Continuous d := by
    apply continuous_pi
    rintro (i | j)
    · exact continuous_const
    · exact continuous_neg
  set F : ℝ → ℝ := fun δ => (H + diagonal (d δ)).det
  set G : ℝ → ℝ := fun δ => ∑ W : Finset (ι ⊕ Fin S),
    (∏ i ∈ Wᶜ, d δ i) * (H.submatrix (Subtype.val : W → _) Subtype.val).det
  have hFc : Continuous F := (continuous_const.add (Continuous.matrix_diagonal hdc)).matrix_det
  have hGc : Continuous G := continuous_finsetSum _ fun W _ =>
    (continuous_finsetProd _ fun i _ => (continuous_apply i).comp hdc).mul continuous_const
  have hFG : F = G := by
    apply Continuous.ext_on (dense_compl_singleton (0 : ℝ)) hFc hGc
    intro δ hδ
    apply det_add_diagonal_expansion
    rintro (i | j)
    · simpa [hd] using hε
    · simpa [hd] using hδ
  have hF0 : F 0 = (bordered (A - ε • (1 : Matrix ι ι ℝ)) C).det := by
    simp only [F]
    congr 1
    ext a b
    rcases a with a | a <;> rcases b with b | b <;>
      simp [H, hd, bordered, Matrix.one_apply, diagonal_apply, sub_eq_add_neg]
    split_ifs <;> simp_all
  rw [← hF0, hFG]
  simp only [G]
  -- only `W` containing every border index survive
  have hzero : ∀ W : Finset (ι ⊕ Fin S), W ∉ Finset.univ.image
      (fun U : Finset ι => U.disjSum (Finset.univ : Finset (Fin S))) →
      (∏ i ∈ Wᶜ, d 0 i) * (H.submatrix (Subtype.val : W → _) Subtype.val).det = 0 := by
    intro W hW
    have : ∃ j, Sum.inr j ∉ W := by
      by_contra hc
      push Not at hc
      apply hW
      refine Finset.mem_image.mpr ⟨Finset.univ.filter (fun a => Sum.inl a ∈ W),
        Finset.mem_univ _, ?_⟩
      ext x
      rcases x with a | j
      · simp
      · simp [hc j]
    obtain ⟨j, hj⟩ := this
    rw [Finset.prod_eq_zero (i := Sum.inr j) (Finset.mem_compl.mpr hj) (by simp [hd]), zero_mul]
  rw [← Finset.sum_subset (Finset.subset_univ _) (fun W _ hW => hzero W hW),
    Finset.sum_image (fun U _ V _ h => by
      ext a
      have := congrArg (fun W : Finset (ι ⊕ Fin S) => Sum.inl a ∈ W) h
      simpa using this)]
  refine Finset.sum_congr rfl fun U _ => ?_
  rw [det_bordered_submatrix_disjSum]
  congr 1
  have hc : (U.disjSum (Finset.univ : Finset (Fin S)))ᶜ = Uᶜ.map Function.Embedding.inl := by
    ext x
    rcases x with a | j <;> simp
  rw [hc, Finset.prod_map]
  simp [hd, Finset.card_compl]

/-- An injective `U × S` matrix has `S ≤ |U|`. -/
theorem card_le_of_mulVec_injective {U : Type*} [Fintype U] {S : ℕ} {C : Matrix U (Fin S) ℝ}
    (h : ∀ μ, C *ᵥ μ = 0 → μ = 0) : S ≤ Fintype.card U := by
  have hinj : Function.Injective C.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    exact fun μ hμ => h μ hμ
  have := LinearMap.finrank_le_finrank_of_injective hinj
  simpa using this

/-- A square (`|U| = S`) injective matrix has injective transpose. -/
theorem transpose_injective_of_card_eq {U : Type*} [Fintype U] {S : ℕ}
    {C : Matrix U (Fin S) ℝ} (h : ∀ μ, C *ᵥ μ = 0 → μ = 0) (hc : Fintype.card U = S) :
    ∀ y, Cᵀ *ᵥ y = 0 → y = 0 := by
  classical
  have hinj : Function.Injective C.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    exact fun μ hμ => h μ hμ
  have hsurj : Function.Surjective C.mulVecLin :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [hc])).mp hinj
  have hrank : C.rank = Fintype.card U := by
    rw [Matrix.rank, LinearMap.range_eq_top.mpr hsurj, finrank_top,
      Module.finrank_fintype_fun_eq_card]
  have hrankT : Cᵀ.rank = Fintype.card U := by rw [Matrix.rank_transpose, hrank]
  have hrn := LinearMap.finrank_range_add_finrank_ker Cᵀ.mulVecLin
  rw [← Matrix.rank, hrankT, Module.finrank_fintype_fun_eq_card] at hrn
  have hker : LinearMap.ker Cᵀ.mulVecLin = ⊥ :=
    Submodule.finrank_eq_zero.mp (by omega)
  intro y hy
  have : y ∈ LinearMap.ker Cᵀ.mulVecLin := hy
  rw [hker] at this
  exact this

/-- For a square injective border the bordered determinant has sign `(-1)^{|U|}`, whatever `A`. -/
theorem bordered_sign_pos_square {U : Type*} [Fintype U] [DecidableEq U] {S : ℕ}
    (A : Matrix U U ℝ) {C : Matrix U (Fin S) ℝ} (h : ∀ μ, C *ᵥ μ = 0 → μ = 0)
    (hc : Fintype.card U = S) : 0 < (-1) ^ Fintype.card U * (bordered A C).det :=
  bordered_sign_pos (fun z hz hz0 => absurd (transpose_injective_of_card_eq h hc z hz) hz0) h

/-- Reindexing the first block of a bordered matrix leaves its determinant unchanged. -/
theorem det_bordered_reindex {U V : Type*} [Fintype U] [DecidableEq U] [Fintype V]
    [DecidableEq V] {S : ℕ} (σ : V ≃ U) (A : Matrix U U ℝ) (C : Matrix U (Fin S) ℝ) :
    (bordered (A.submatrix σ σ) (C.submatrix σ id)).det = (bordered A C).det := by
  rw [← det_submatrix_equiv_self (Equiv.sumCongr σ (Equiv.refl (Fin S))) (bordered A C)]
  congr 1
  ext a b
  rcases a with a | a <;> rcases b with b | b <;> rfl

/-- The printed hypothesis of Theorem M.D.3(ii) gives the sign of the bordered determinant for
every injective choice of rows `g`, indexed by any finite type. -/
theorem bordered_sign_of_printed {N S : ℕ} {M : Matrix (Fin N) (Fin N) ℝ}
    {B : Matrix (Fin N) (Fin S) ℝ}
    (hP : ∀ r (h : r ≤ N) (π : Equiv.Perm (Fin N)), S < r →
      0 ≤ (-1) ^ r * (borderedMatrix (permuteMatrix M π) (B.submatrix π id) r h).det)
    {U : Type*} [Fintype U] [DecidableEq U] {g : U → Fin N} (hg : Function.Injective g)
    (hU : S < Fintype.card U) :
    0 ≤ (-1) ^ Fintype.card U * (bordered (M.submatrix g g) (B.submatrix g id)).det := by
  set k := Fintype.card U
  set σ : Fin k ≃ U := (Fintype.equivFin U).symm
  have hk : k ≤ N := by simpa [k] using Fintype.card_le_of_injective g hg
  have hf : Function.Injective (g ∘ σ) := hg.comp σ.injective
  obtain ⟨π, hπ⟩ := exists_perm_extend hk (g ∘ σ) hf
  have := hP k hk π hU
  have e : borderedMatrix (permuteMatrix M π) (B.submatrix π id) k hk =
      bordered ((M.submatrix g g).submatrix σ σ) ((B.submatrix g id).submatrix σ id) := by
    ext a b
    rcases a with a | a <;> rcases b with b | b <;>
      simp [borderedMatrix, bordered, leadingMinorMatrix, permuteMatrix, hπ]
  rw [e, det_bordered_reindex] at this
  exact this

/-- **Theorem M.D.3(ii)** (MWG, p. 938), with `{z : Bᵀz = 0}`. Let `M` be symmetric and suppose
some `S` rows of `B` are linearly independent (`B` has rank `S`). Then `M` is negative
semidefinite on `{z : Bᵀz = 0}` iff `(-1)^r |[[ₜM^πₜ, ₜB^π], [(ₜB^π)ᵀ, 0]]| ≥ 0` for every
`r = S+1, …, N` and every permutation `π`. -/
theorem theorem_M_D_3_ii {N S : ℕ} {M : Matrix (Fin N) (Fin N) ℝ} (hM : M.IsSymm)
    (B : Matrix (Fin N) (Fin S) ℝ) {e₀ : Fin S → Fin N} (he₀ : Function.Injective e₀)
    (hB : (B.submatrix e₀ id).det ≠ 0) :
    (∀ z, Bᵀ *ᵥ z = 0 → z ⬝ᵥ M *ᵥ z ≤ 0) ↔
      ∀ r (h : r ≤ N) (π : Equiv.Perm (Fin N)), S < r →
        0 ≤ (-1) ^ r * (borderedMatrix (permuteMatrix M π) (B.submatrix π id) r h).det := by
  refine ⟨fun hNSD r h π _ => theorem_M_D_3_ii_forward B hNSD r h π, fun hP => ?_⟩
  have hSN : S ≤ N := by simpa using Fintype.card_le_of_injective e₀ he₀
  obtain ⟨π₀, hπ₀⟩ := exists_perm_extend hSN e₀ he₀
  set M' := permuteMatrix M π₀
  set B' := B.submatrix π₀ id
  have hB' : (B'.submatrix (Fin.castLE hSN) id).det ≠ 0 := by
    have e : B'.submatrix (Fin.castLE hSN) id = B.submatrix e₀ id := by
      ext i j
      simp [B', hπ₀]
    rwa [e]
  -- for every `ε > 0`, `M' - εI` is negative definite on `{z : B'ᵀz = 0}`
  have hND : ∀ ε : ℝ, 0 < ε → ∀ z, B'ᵀ *ᵥ z = 0 → z ≠ 0 →
      z ⬝ᵥ (M' - ε • (1 : Matrix (Fin N) (Fin N) ℝ)) *ᵥ z < 0 := by
    intro ε hε
    have hsymm : (M' - ε • (1 : Matrix (Fin N) (Fin N) ℝ)).IsSymm := by
      ext i j
      by_cases hij : i = j
      · subst hij; rfl
      · simp [M', permuteMatrix, hij, Ne.symm hij, hM.apply]
    apply (theorem_M_D_3_i hsymm B' hSN hB').mpr
    intro r h hr
    set e : Fin r → Fin N := π₀ ∘ Fin.castLE h
    have he : Function.Injective e := π₀.injective.comp (Fin.castLE_injective h)
    set A := M.submatrix e e
    set C := B.submatrix e id
    have hbm : borderedMatrix (M' - ε • (1 : Matrix (Fin N) (Fin N) ℝ)) B' r h =
        bordered (A - ε • (1 : Matrix (Fin r) (Fin r) ℝ)) C := by
      ext a b
      rcases a with a | a <;> rcases b with b | b <;>
        simp [borderedMatrix, bordered, leadingMinorMatrix, M', B', A, C, e, permuteMatrix,
          Matrix.one_apply, Fin.castLE_inj]
    rw [hbm, bordered_perturbation_expansion A C hε.ne', Finset.mul_sum]
    -- each term is `ε^{r-|U|} (-1)^{|U|} |bordered_U| ≥ 0`
    have hterm : ∀ U : Finset (Fin r),
        (-1) ^ r * ((-ε) ^ (Fintype.card (Fin r) - U.card) *
          (bordered (A.submatrix (Subtype.val : U → Fin r) Subtype.val)
            (C.submatrix Subtype.val id)).det) =
        ε ^ (r - U.card) * ((-1) ^ U.card *
          (bordered (A.submatrix (Subtype.val : U → Fin r) Subtype.val)
            (C.submatrix Subtype.val id)).det) := by
      intro U
      have hU : U.card ≤ r := by simpa using Finset.card_le_univ U
      rw [Fintype.card_fin, neg_pow]
      have : (-1 : ℝ) ^ r = (-1) ^ U.card * (-1) ^ (r - U.card) := by
        rw [← pow_add, Nat.add_sub_cancel' hU]
      rw [this]
      have h2 : ((-1 : ℝ) ^ (r - U.card)) * (-1) ^ (r - U.card) = 1 := by
        rw [← mul_pow]; norm_num
      linear_combination (ε ^ (r - U.card) * ((-1) ^ U.card *
        (bordered (A.submatrix (Subtype.val : U → Fin r) Subtype.val)
          (C.submatrix Subtype.val id)).det)) * h2
    simp only [hterm]
    have hnonneg : ∀ U : Finset (Fin r), 0 ≤ (-1) ^ U.card *
        (bordered (A.submatrix (Subtype.val : U → Fin r) Subtype.val)
          (C.submatrix Subtype.val id)).det := by
      intro U
      by_cases hinj : ∀ μ, (C.submatrix (Subtype.val : U → Fin r) id) *ᵥ μ = 0 → μ = 0
      · have hcard := card_le_of_mulVec_injective hinj
        rw [Fintype.card_coe] at hcard
        rcases eq_or_lt_of_le hcard with heq | hlt
        · have := bordered_sign_pos_square (A.submatrix (Subtype.val : U → Fin r) Subtype.val)
            hinj (by rw [Fintype.card_coe]; exact heq.symm)
          rw [Fintype.card_coe] at this
          exact this.le
        · have := bordered_sign_of_printed hP (g := e ∘ Subtype.val)
            (he.comp Subtype.val_injective) (by rw [Fintype.card_coe]; exact hlt)
          rw [Fintype.card_coe] at this
          exact this
      · rw [bordered_det_eq_zero_of_not_injective hinj, mul_zero]
    -- the term of the first `S` rows is positive
    set U₀ : Finset (Fin r) := Finset.univ.map (Fin.castLEEmb hr.le)
    have hU₀card : U₀.card = S := by simp [U₀]
    have hU₀inj : ∀ μ, (C.submatrix (Subtype.val : U₀ → Fin r) id) *ᵥ μ = 0 → μ = 0 := by
      intro μ hμ
      by_contra hne
      apply hB
      rw [← exists_mulVec_eq_zero_iff]
      refine ⟨μ, hne, funext fun i => ?_⟩
      have hmem : Fin.castLE hr.le i ∈ U₀ := Finset.mem_map_of_mem _ (Finset.mem_univ i)
      have := congrFun hμ ⟨Fin.castLE hr.le i, hmem⟩
      simpa [C, e, mulVec, dotProduct, hπ₀] using this
    have hU₀pos := bordered_sign_pos_square (A.submatrix (Subtype.val : U₀ → Fin r) Subtype.val)
      hU₀inj (by rw [Fintype.card_coe]; exact hU₀card)
    rw [Fintype.card_coe] at hU₀pos
    apply lt_of_lt_of_le (mul_pos (pow_pos hε (r - U₀.card)) hU₀pos)
    exact Finset.single_le_sum (f := fun U : Finset (Fin r) => ε ^ (r - U.card) *
      ((-1) ^ U.card * (bordered (A.submatrix (Subtype.val : U → Fin r) Subtype.val)
        (C.submatrix Subtype.val id)).det))
      (fun U _ => mul_nonneg (pow_nonneg hε.le _) (hnonneg U)) (Finset.mem_univ U₀)
  -- transfer back to `M`
  intro z hz
  set z' : Fin N → ℝ := fun i => z (π₀ i)
  have hz' : B'ᵀ *ᵥ z' = 0 := by
    funext j
    have := congrFun hz j
    simp only [mulVec, dotProduct, transpose_apply, Pi.zero_apply] at this ⊢
    rw [← this]
    exact Equiv.sum_comp π₀ (fun i => B i j * z i)
  have hq : z' ⬝ᵥ M' *ᵥ z' = z ⬝ᵥ M *ᵥ z := by
    simp only [dotProduct, mulVec, M', permuteMatrix, submatrix_apply, z']
    rw [← Equiv.sum_comp π₀ (fun i => z i * ∑ j, M i j * z j)]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    exact Equiv.sum_comp π₀ (fun j => M (π₀ i) j * z j)
  have hzz : z' ⬝ᵥ z' = z ⬝ᵥ z := by
    simp only [dotProduct, z']
    exact Equiv.sum_comp π₀ (fun i => z i * z i)
  by_cases hz0 : z' = 0
  · have : z = 0 := by
      funext i
      have := congrFun hz0 (π₀.symm i)
      simpa [z'] using this
    rw [this, mulVec_zero, dotProduct_zero]
  by_contra hc
  push Not at hc
  have hpos := dotProduct_self_pos_of_ne_zero hz0
  set ε := (z ⬝ᵥ M *ᵥ z) / (2 * (z' ⬝ᵥ z'))
  have hε : 0 < ε := div_pos hc (by linarith)
  have := hND ε hε z' hz' hz0
  rw [sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul, hq] at this
  have e2 : ε * (z' ⬝ᵥ z') = (z ⬝ᵥ M *ᵥ z) / 2 := by
    simp only [ε]
    field_simp
  linarith

end MWG.ConsumerChoice

set_option linter.style.longLine false
#print axioms MWG.ConsumerChoice.nonnegOrthant
#print axioms MWG.ConsumerChoice.mem_nonnegOrthant_iff
#print axioms MWG.ConsumerChoice.range_val_nonnegativeOrthant
#print axioms MWG.ConsumerChoice.convexCombination_apply
#print axioms MWG.ConsumerChoice.convex_nonnegOrthant
#print axioms MWG.ConsumerChoice.figure_2_C_1_set
#print axioms MWG.ConsumerChoice.figure_2_C_2_set
#print axioms MWG.ConsumerChoice.figure_2_C_3_set
#print axioms MWG.ConsumerChoice.figure_2_C_4_set
#print axioms MWG.ConsumerChoice.figure_2_C_5_set
#print axioms MWG.ConsumerChoice.figure_2_C_6_set
#print axioms MWG.ConsumerChoice.convex_figure_2_C_1
#print axioms MWG.ConsumerChoice.convex_figure_2_C_4
#print axioms MWG.ConsumerChoice.convex_figure_2_C_5
#print axioms MWG.ConsumerChoice.convex_figure_2_C_6
#print axioms MWG.ConsumerChoice.not_convex_figure_2_C_2
#print axioms MWG.ConsumerChoice.not_convex_figure_2_C_3
#print axioms MWG.ConsumerChoice.StrictlyPositive
#print axioms MWG.ConsumerChoice.budgetSet
#print axioms MWG.ConsumerChoice.definition_2_D_1
#print axioms MWG.ConsumerChoice.budgetHyperplane
#print axioms MWG.ConsumerChoice.image_val_krepsBudgetSet
#print axioms MWG.ConsumerChoice.budgetSet_zero_wealth
#print axioms MWG.ConsumerChoice.budgetHyperplane_orthogonal
#print axioms MWG.ConsumerChoice.budgetLine_two_goods
#print axioms MWG.ConsumerChoice.budgetSet_subset_of_price_fall
#print axioms MWG.ConsumerChoice.budgetSet_ssubset_of_price_fall
#print axioms MWG.ConsumerChoice.budgetLine_steeper
#print axioms MWG.ConsumerChoice.convex_budgetSet
#print axioms MWG.ConsumerChoice.budgetSetOn
#print axioms MWG.ConsumerChoice.budgetSetOn_nonnegOrthant
#print axioms MWG.ConsumerChoice.exercise_2_D_3b
#print axioms MWG.ConsumerChoice.exercise_2_D_3a
#print axioms MWG.ConsumerChoice.figure_2_D_4_income
#print axioms MWG.ConsumerChoice.figure_2_D_4_consumption
#print axioms MWG.ConsumerChoice.figure_2_D_4_set
#print axioms MWG.ConsumerChoice.exercise_2_D_4
#print axioms MWG.ConsumerChoice.exercise_2_D_1
#print axioms MWG.ConsumerChoice.exercise_2_D_2
#print axioms MWG.ConsumerChoice.PWDomain
#print axioms MWG.ConsumerChoice.DemandCorrespondence
#print axioms MWG.ConsumerChoice.DemandFunction
#print axioms MWG.ConsumerChoice.HomogeneousZeroCorr
#print axioms MWG.ConsumerChoice.WalrasLawCorr
#print axioms MWG.ConsumerChoice.HomogeneousZero
#print axioms MWG.ConsumerChoice.WalrasLaw
#print axioms MWG.ConsumerChoice.toCorrespondence
#print axioms MWG.ConsumerChoice.homogeneousZero_iff_corr
#print axioms MWG.ConsumerChoice.walrasLaw_iff_corr
#print axioms MWG.ConsumerChoice.pwDomain_smul
#print axioms MWG.ConsumerChoice.budgetSet_smul
#print axioms MWG.ConsumerChoice.vertex_mem_budgetSet
#print axioms MWG.ConsumerChoice.budgetSet_eq_imp_proportional
#print axioms MWG.ConsumerChoice.demand_depends_only_on_budget
#print axioms MWG.ConsumerChoice.walrasianBudgetFamily
#print axioms MWG.ConsumerChoice.budgetSet_infinite
#print axioms MWG.ConsumerChoice.finite_not_mem_walrasianBudgetFamily
#print axioms MWG.ConsumerChoice.normalize_price
#print axioms MWG.ConsumerChoice.normalize_wealth
#print axioms MWG.ConsumerChoice.priceEffect
#print axioms MWG.ConsumerChoice.wealthEffect
#print axioms MWG.ConsumerChoice.priceJacobian
#print axioms MWG.ConsumerChoice.wealthJacobian
#print axioms MWG.ConsumerChoice.prod_eq_sum_single
#print axioms MWG.ConsumerChoice.deriv_apply_eq
#print axioms MWG.ConsumerChoice.deriv_apply_eq_mulVec
#print axioms MWG.ConsumerChoice.engelFunction
#print axioms MWG.ConsumerChoice.wealthExpansionPath
#print axioms MWG.ConsumerChoice.NormalAt
#print axioms MWG.ConsumerChoice.InferiorAt
#print axioms MWG.ConsumerChoice.NormalDemand
#print axioms MWG.ConsumerChoice.GiffenAt
#print axioms MWG.ConsumerChoice.inferiorAt_iff_not_normalAt
#print axioms MWG.ConsumerChoice.priceEffect_fderiv
#print axioms MWG.ConsumerChoice.demand_2_E_1
#print axioms MWG.ConsumerChoice.exercise_2_E_1_homogeneous
#print axioms MWG.ConsumerChoice.demand_2_E_1_expenditure
#print axioms MWG.ConsumerChoice.exercise_2_E_1_walras_iff
#print axioms MWG.ConsumerChoice.exercise_2_E_7
#print axioms MWG.ConsumerChoice.hasDerivAt_line
#print axioms MWG.ConsumerChoice.hasDerivAt_path
#print axioms MWG.ConsumerChoice.hasDerivAt_path_apply
#print axioms MWG.ConsumerChoice.eventually_pwDomain
#print axioms MWG.ConsumerChoice.hasDerivAt_eq_zero_of_eventually_const
#print axioms MWG.ConsumerChoice.walras_deriv_identity
#print axioms MWG.ConsumerChoice.homogeneous_deriv_identity
#print axioms MWG.ConsumerChoice.priceElasticity
#print axioms MWG.ConsumerChoice.wealthElasticity
#print axioms MWG.ConsumerChoice.budgetShare
#print axioms MWG.ConsumerChoice.proposition_2_E_1
#print axioms MWG.ConsumerChoice.proposition_2_E_1_matrix
#print axioms MWG.ConsumerChoice.proposition_2_E_1_elasticity
#print axioms MWG.ConsumerChoice.proposition_2_E_2
#print axioms MWG.ConsumerChoice.proposition_2_E_2_matrix
#print axioms MWG.ConsumerChoice.proposition_2_E_3
#print axioms MWG.ConsumerChoice.proposition_2_E_3_matrix
#print axioms MWG.ConsumerChoice.exercise_2_E_2_price
#print axioms MWG.ConsumerChoice.exercise_2_E_2_wealth
#print axioms MWG.ConsumerChoice.exercise_2_E_3
#print axioms MWG.ConsumerChoice.exercise_2_E_3_via_homogeneity
#print axioms MWG.ConsumerChoice.HomogeneousOneInWealth
#print axioms MWG.ConsumerChoice.exercise_2_E_4_wealthJacobian
#print axioms MWG.ConsumerChoice.exercise_2_E_4
#print axioms MWG.ConsumerChoice.exercise_2_E_4_engel
#print axioms MWG.ConsumerChoice.demand_eq_of_own_price_eq
#print axioms MWG.ConsumerChoice.exercise_2_E_5
#print axioms MWG.ConsumerChoice.demand_2_E_5_counterexample
#print axioms MWG.ConsumerChoice.demand_2_E_5_counterexample_differentiableAt
#print axioms MWG.ConsumerChoice.exercise_2_E_5_alpha_pos_counterexample
#print axioms MWG.ConsumerChoice.demand_2_E_1_differentiableAt
#print axioms MWG.ConsumerChoice.exercise_2_E_6
#print axioms MWG.ConsumerChoice.hasDerivAt_exp_price_curve
#print axioms MWG.ConsumerChoice.exercise_2_E_8_price
#print axioms MWG.ConsumerChoice.exercise_2_E_8_wealth
#print axioms MWG.ConsumerChoice.exercise_2_E_8_loglinear
#print axioms MWG.ConsumerChoice.WeakAxiom
#print axioms MWG.ConsumerChoice.ValuesInOrthant
#print axioms MWG.ConsumerChoice.compensatedWealth
#print axioms MWG.ConsumerChoice.CompensatedLawOfDemand
#print axioms MWG.ConsumerChoice.compensatedWealth_pos
#print axioms MWG.ConsumerChoice.weakAxiom_iff_compensated
#print axioms MWG.ConsumerChoice.proposition_2_F_1_i
#print axioms MWG.ConsumerChoice.proposition_2_F_1_ii
#print axioms MWG.ConsumerChoice.proposition_2_F_1
#print axioms MWG.ConsumerChoice.own_price_compensated_law
#print axioms MWG.ConsumerChoice.figure_2_F_4
#print axioms MWG.ConsumerChoice.leontiefDemand
#print axioms MWG.ConsumerChoice.leontiefDemand_walras
#print axioms MWG.ConsumerChoice.leontiefDemand_homogeneous
#print axioms MWG.ConsumerChoice.leontiefDemand_orthant
#print axioms MWG.ConsumerChoice.leontiefDemand_weakAxiom
#print axioms MWG.ConsumerChoice.own_price_strict_counterexample
#print axioms MWG.ConsumerChoice.walrasianChoiceRule
#print axioms MWG.ConsumerChoice.zero_mem_budgetSet
#print axioms MWG.ConsumerChoice.walrasianChoiceStructure
#print axioms MWG.ConsumerChoice.walrasianChoiceRule_budgetSet
#print axioms MWG.ConsumerChoice.exercise_2_F_1
#print axioms MWG.ConsumerChoice.exercise_2_F_6
#print axioms MWG.ConsumerChoice.exercise_2_F_12
#print axioms MWG.ConsumerChoice.exercise_2_F_14
#print axioms MWG.ConsumerChoice.GeneralizedWeakAxiom
#print axioms MWG.ConsumerChoice.walrasianCorrStructure
#print axioms MWG.ConsumerChoice.exercise_2_F_13a
#print axioms MWG.ConsumerChoice.generalizedWeakAxiom_toCorrespondence_iff
#print axioms MWG.ConsumerChoice.dotProduct_pos_of_nonneg
#print axioms MWG.ConsumerChoice.exercise_2_F_13b
#print axioms MWG.ConsumerChoice.GeneralizedCompensatedLaw
#print axioms MWG.ConsumerChoice.exercise_2_F_13c
#print axioms MWG.ConsumerChoice.exercise_2_F_13d
#print axioms MWG.ConsumerChoice.RevealedPreferred
#print axioms MWG.ConsumerChoice.PairWeakAxiom
#print axioms MWG.ConsumerChoice.pairWeakAxiom_of_weakAxiom
#print axioms MWG.ConsumerChoice.figure_2_F_5
#print axioms MWG.ConsumerChoice.example_2_F_1_prices
#print axioms MWG.ConsumerChoice.example_2_F_1_choices
#print axioms MWG.ConsumerChoice.example_2_F_1_walras
#print axioms MWG.ConsumerChoice.exercise_2_F_2_pairs
#print axioms MWG.ConsumerChoice.exercise_2_F_2_cycle
#print axioms MWG.ConsumerChoice.example_2_F_1_not_rationalizable
#print axioms MWG.ConsumerChoice.exercise_2_F_3_p1
#print axioms MWG.ConsumerChoice.exercise_2_F_3_x1
#print axioms MWG.ConsumerChoice.exercise_2_F_3_p2
#print axioms MWG.ConsumerChoice.exercise_2_F_3_x2
#print axioms MWG.ConsumerChoice.exercise_2_F_3_w2
#print axioms MWG.ConsumerChoice.exercise_2_F_3_rp12
#print axioms MWG.ConsumerChoice.exercise_2_F_3_rp21
#print axioms MWG.ConsumerChoice.exercise_2_F_3a
#print axioms MWG.ConsumerChoice.exercise_2_F_3b
#print axioms MWG.ConsumerChoice.exercise_2_F_3c
#print axioms MWG.ConsumerChoice.exercise_2_F_3d
#print axioms MWG.ConsumerChoice.exercise_2_F_3_inconsistent
#print axioms MWG.ConsumerChoice.exists_inferiorAt_of_decrease
#print axioms MWG.ConsumerChoice.exercise_2_F_3_compensated
#print axioms MWG.ConsumerChoice.exercise_2_F_3e
#print axioms MWG.ConsumerChoice.exercise_2_F_3f
#print axioms MWG.ConsumerChoice.exercise_2_F_3_homothetic_bound
#print axioms MWG.ConsumerChoice.laspeyresQuantity
#print axioms MWG.ConsumerChoice.paascheQuantity
#print axioms MWG.ConsumerChoice.expenditureIndex
#print axioms MWG.ConsumerChoice.exercise_2_F_4a
#print axioms MWG.ConsumerChoice.exercise_2_F_4b
#print axioms MWG.ConsumerChoice.exercise_2_F_4c
#print axioms MWG.ConsumerChoice.NegSemidef
#print axioms MWG.ConsumerChoice.NegDef
#print axioms MWG.ConsumerChoice.PosSemidefMWG
#print axioms MWG.ConsumerChoice.PosDefMWG
#print axioms MWG.ConsumerChoice.posSemidefMWG_iff_neg
#print axioms MWG.ConsumerChoice.posDefMWG_iff_neg
#print axioms MWG.ConsumerChoice.NegDef.negSemidef
#print axioms MWG.ConsumerChoice.posSemidefMWG_iff_posSemidef
#print axioms MWG.ConsumerChoice.posDefMWG_iff_posDef
#print axioms MWG.ConsumerChoice.slutskyMatrix
#print axioms MWG.ConsumerChoice.slutskyMatrix_eq
#print axioms MWG.ConsumerChoice.slutskyMatrix_mulVec
#print axioms MWG.ConsumerChoice.hasDerivAt_nonpos_of_right_le
#print axioms MWG.ConsumerChoice.proposition_2_F_2
#print axioms MWG.ConsumerChoice.slutsky_diag_nonpos
#print axioms MWG.ConsumerChoice.giffen_imp_inferior
#print axioms MWG.ConsumerChoice.proposition_2_F_3
#print axioms MWG.ConsumerChoice.exercise_2_F_7
#print axioms MWG.ConsumerChoice.slutsky_det_eq_zero
#print axioms MWG.ConsumerChoice.slutsky_not_negDef
#print axioms MWG.ConsumerChoice.symmetric_of_two_by_two
#print axioms MWG.ConsumerChoice.exercise_2_F_11
#print axioms MWG.ConsumerChoice.exercise_2_F_9b
#print axioms MWG.ConsumerChoice.exercise_2_F_8
#print axioms MWG.ConsumerChoice.exercise_2_F_5
#print axioms MWG.ConsumerChoice.exercise_2_F_5_infinitesimal
#print axioms MWG.ConsumerChoice.slutsky_mulVec_of_hasDerivAt
#print axioms MWG.ConsumerChoice.hasDerivAt_affine
#print axioms MWG.ConsumerChoice.hasDerivAt_share_term
#print axioms MWG.ConsumerChoice.slutsky_2_E_1_mulVec
#print axioms MWG.ConsumerChoice.exercise_2_F_10a_matrix
#print axioms MWG.ConsumerChoice.exercise_2_F_10a
#print axioms MWG.ConsumerChoice.exercise_2_F_10b_quadratic
#print axioms MWG.ConsumerChoice.exercise_2_F_10b
#print axioms MWG.ConsumerChoice.demand_2_F_16
#print axioms MWG.ConsumerChoice.exercise_2_F_16a
#print axioms MWG.ConsumerChoice.exercise_2_F_16b
#print axioms MWG.ConsumerChoice.demand_2_F_16_differentiableAt
#print axioms MWG.ConsumerChoice.exercise_2_F_16c
#print axioms MWG.ConsumerChoice.demand_2_F_15
#print axioms MWG.ConsumerChoice.quadForm_pos
#print axioms MWG.ConsumerChoice.exercise_2_F_15_basic
#print axioms MWG.ConsumerChoice.exercise_2_F_15_unique
#print axioms MWG.ConsumerChoice.exercise_2_F_15_weakAxiom
#print axioms MWG.ConsumerChoice.demand_2_F_15_differentiableAt
#print axioms MWG.ConsumerChoice.slutsky_2_F_15_mulVec
#print axioms MWG.ConsumerChoice.exercise_2_F_15_quadratic
#print axioms MWG.ConsumerChoice.exercise_2_F_15_negDef_off_p
#print axioms MWG.ConsumerChoice.exercise_2_F_15_not_symm
#print axioms MWG.ConsumerChoice.demand_2_F_17
#print axioms MWG.ConsumerChoice.exercise_2_F_17a
#print axioms MWG.ConsumerChoice.sum_prices_pos
#print axioms MWG.ConsumerChoice.exercise_2_F_17b
#print axioms MWG.ConsumerChoice.exercise_2_F_17c
#print axioms MWG.ConsumerChoice.demand_2_F_17_differentiableAt
#print axioms MWG.ConsumerChoice.exercise_2_F_17d_zero
#print axioms MWG.ConsumerChoice.exercise_2_F_17d
#print axioms MWG.ConsumerChoice.neg_at_one_of_deriv_neg_at_zeros
#print axioms MWG.ConsumerChoice.samuelson_sufficiency
#print axioms MWG.ConsumerChoice.dotProduct_eq_transpose_mul
#print axioms MWG.ConsumerChoice.vecMul_eq_transpose_mul
#print axioms MWG.ConsumerChoice.jacobian
#print axioms MWG.ConsumerChoice.jacobian_mulVec
#print axioms MWG.ConsumerChoice.gradientVec
#print axioms MWG.ConsumerChoice.gradient_eq_transpose_jacobian
#print axioms MWG.ConsumerChoice.fderiv_apply_eq_gradient_dot
#print axioms MWG.ConsumerChoice.partialJacobianFst
#print axioms MWG.ConsumerChoice.partialJacobianFst_apply
#print axioms MWG.ConsumerChoice.hessianMatrix
#print axioms MWG.ConsumerChoice.equation_M_A_1
#print axioms MWG.ConsumerChoice.equation_M_A_2
#print axioms MWG.ConsumerChoice.equation_M_A_3
#print axioms MWG.ConsumerChoice.equation_M_A_5
#print axioms MWG.ConsumerChoice.rank_vecMulVec_le_one
#print axioms MWG.ConsumerChoice.equation_M_A_4
#print axioms MWG.ConsumerChoice.HomogeneousOfDegree
#print axioms MWG.ConsumerChoice.example_M_B_quotient
#print axioms MWG.ConsumerChoice.example_M_B_sqrt
#print axioms MWG.ConsumerChoice.homogeneous_zero_normalize
#print axioms MWG.ConsumerChoice.homogeneous_one_normalize
#print axioms MWG.ConsumerChoice.interior_nonnegOrthant_nonempty
#print axioms MWG.ConsumerChoice.theorem_M_B_1
#print axioms MWG.ConsumerChoice.theorem_M_B_1_partial
#print axioms MWG.ConsumerChoice.example_M_B_sqrt_partial
#print axioms MWG.ConsumerChoice.level_set_radial
#print axioms MWG.ConsumerChoice.level_set_slope_radial
#print axioms MWG.ConsumerChoice.homothetic_level_sets
#print axioms MWG.ConsumerChoice.homothetic_slope_radial
#print axioms MWG.ConsumerChoice.theorem_M_B_2
#print axioms MWG.ConsumerChoice.euler_degree_zero
#print axioms MWG.ConsumerChoice.dotProduct_self_pos_of_ne_zero
#print axioms MWG.ConsumerChoice.dotProduct_transpose_mulVec
#print axioms MWG.ConsumerChoice.theorem_M_D_1_i
#print axioms MWG.ConsumerChoice.theorem_M_D_1_i_semidef
#print axioms MWG.ConsumerChoice.IsCharacteristicValue
#print axioms MWG.ConsumerChoice.isCharacteristicValue_ofReal_iff
#print axioms MWG.ConsumerChoice.isCharacteristicValue_real
#print axioms MWG.ConsumerChoice.theorem_M_D_1_ii
#print axioms MWG.ConsumerChoice.theorem_M_D_1_ii_complex
#print axioms MWG.ConsumerChoice.NegDef.det_ne_zero
#print axioms MWG.ConsumerChoice.NegDef.inv
#print axioms MWG.ConsumerChoice.theorem_M_D_1_iii
#print axioms MWG.ConsumerChoice.Stable
#print axioms MWG.ConsumerChoice.theorem_M_D_1_iv
#print axioms MWG.ConsumerChoice.det_neg_eq_pow
#print axioms MWG.ConsumerChoice.quadratic_two_by_two
#print axioms MWG.ConsumerChoice.example_M_D_1_negDef
#print axioms MWG.ConsumerChoice.example_M_D_1_negSemidef
#print axioms MWG.ConsumerChoice.DominantDiagonal
#print axioms MWG.ConsumerChoice.GrossSubstituteSign
#print axioms MWG.ConsumerChoice.theorem_M_D_5_i
#print axioms MWG.ConsumerChoice.theorem_M_D_5_ii
#print axioms MWG.ConsumerChoice.theorem_M_D_5_iii
#print axioms MWG.ConsumerChoice.theorem_M_D_5_iv
#print axioms MWG.ConsumerChoice.sum_extend_mul
#print axioms MWG.ConsumerChoice.quadratic_submatrix
#print axioms MWG.ConsumerChoice.NegDef.submatrix
#print axioms MWG.ConsumerChoice.NegSemidef.submatrix
#print axioms MWG.ConsumerChoice.PosDefMWG.det_ne_zero
#print axioms MWG.ConsumerChoice.PosDefMWG.det_pos
#print axioms MWG.ConsumerChoice.leadingMinorMatrix
#print axioms MWG.ConsumerChoice.permuteMatrix
#print axioms MWG.ConsumerChoice.theorem_M_D_2_iii
#print axioms MWG.ConsumerChoice.IsPMatrix
#print axioms MWG.ConsumerChoice.negDef_neg_isPMatrix
#print axioms MWG.ConsumerChoice.leadingMinorMatrix_castSucc
#print axioms MWG.ConsumerChoice.quadratic_castSucc_split
#print axioms MWG.ConsumerChoice.sylvester_posDef
#print axioms MWG.ConsumerChoice.theorem_M_D_2_i
#print axioms MWG.ConsumerChoice.exercise_2_F_9a
#print axioms MWG.ConsumerChoice.exists_perm_extend
#print axioms MWG.ConsumerChoice.principalMinor_eq_permuted
#print axioms MWG.ConsumerChoice.posSemidef_of_principal_minors
#print axioms MWG.ConsumerChoice.theorem_M_D_2_ii
#print axioms MWG.ConsumerChoice.theorem_M_D_2_ii_permutations_needed
#print axioms MWG.ConsumerChoice.quadratic_sub_smul
#print axioms MWG.ConsumerChoice.theorem_M_D_4_ii
#print axioms MWG.ConsumerChoice.extend_succAbove_self
#print axioms MWG.ConsumerChoice.extend_succAbove_restrict
#print axioms MWG.ConsumerChoice.theorem_M_D_4_iii
#print axioms MWG.ConsumerChoice.rank_le_of_two_kernel_vectors
#print axioms MWG.ConsumerChoice.theorem_M_D_4_i
#print axioms MWG.ConsumerChoice.pow_entry_nonneg
#print axioms MWG.ConsumerChoice.theorem_M_D_5_v
#print axioms MWG.ConsumerChoice.borderedMatrix
#print axioms MWG.ConsumerChoice.theorem_M_D_3_i_counterexample
#print axioms MWG.ConsumerChoice.example_M_D_2_det
#print axioms MWG.ConsumerChoice.example_M_D_2_line
#print axioms MWG.ConsumerChoice.example_M_D_2_negDef
#print axioms MWG.ConsumerChoice.example_M_D_2_negSemidef
#print axioms MWG.ConsumerChoice.example_M_D_2_product
#print axioms MWG.ConsumerChoice.bordered
#print axioms MWG.ConsumerChoice.bordered_det_eq_zero_of_not_injective
#print axioms MWG.ConsumerChoice.bordered_det_ne_zero
#print axioms MWG.ConsumerChoice.posDefMWG_transpose_mul
#print axioms MWG.ConsumerChoice.posDefMWG_mul_transpose
#print axioms MWG.ConsumerChoice.bordered_sign_pos
#print axioms MWG.ConsumerChoice.bordered_det_eq
#print axioms MWG.ConsumerChoice.transpose_mulVec_extend
#print axioms MWG.ConsumerChoice.negDef_on_ker_submatrix
#print axioms MWG.ConsumerChoice.leadingRows_injective
#print axioms MWG.ConsumerChoice.leadingRows_transpose_injective
#print axioms MWG.ConsumerChoice.theorem_M_D_3_i
#print axioms MWG.ConsumerChoice.theorem_M_D_3_ii_forward
#print axioms MWG.ConsumerChoice.det_one_add_eq_sum_minors
#print axioms MWG.ConsumerChoice.det_add_diagonal_expansion
#print axioms MWG.ConsumerChoice.det_bordered_submatrix_disjSum
#print axioms MWG.ConsumerChoice.bordered_perturbation_expansion
#print axioms MWG.ConsumerChoice.card_le_of_mulVec_injective
#print axioms MWG.ConsumerChoice.transpose_injective_of_card_eq
#print axioms MWG.ConsumerChoice.bordered_sign_pos_square
#print axioms MWG.ConsumerChoice.det_bordered_reindex
#print axioms MWG.ConsumerChoice.bordered_sign_of_printed
#print axioms MWG.ConsumerChoice.theorem_M_D_3_ii
