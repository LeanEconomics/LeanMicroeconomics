/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGConsumerChoice.Commodities

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
