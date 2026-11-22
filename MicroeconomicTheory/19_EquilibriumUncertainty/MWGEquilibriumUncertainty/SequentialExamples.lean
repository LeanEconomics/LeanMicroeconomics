/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGEquilibriumUncertainty.Sequential

/-!
# Sequential trade: Example 19.D.1 and Exercises 19.D.2-19.D.4 (MWG pp. 697-699, 726-727)

* **Example 19.D.1**: two equally likely states, two goods, two consumers with the same
  state-independent concave Bernoulli utility; consumer 1 owns the aggregate endowment `ω̄` in
  state 1, consumer 2 in state 2. If `ω̄/2` is demanded at spot prices `p̂` with wealth `p̂·ω̄/2`
  (a symmetric spot equilibrium, as with `u = min`), giving everybody `ω̄/2` in each state is an
  Arrow-Debreu equilibrium with the same spot prices in both states (`example_19_D_1`), with an
  instance (`example_19_D_1_instance`); with a strictly concave, strongly monotone `u` every
  Arrow-Debreu equilibrium allocation is state independent (`example_19_D_1_stateIndependent`).
* **Exercise 19.D.2**: the contingent trades reaching it: consumer 1 sells `α` units of good 1
  contingent on state 1 and buys `β = α` contingent on state 2 (`exercise_19_D_2`).
* **Exercise 19.D.3**: with consumption at `t = 0`, the budget sets of the two formulations
  coincide in both directions (`exercise_19_D_3_i`, `exercise_19_D_3_ii`).
* **Exercise 19.D.4**: three dates and a binary tree: (a) the Arrow-Debreu budget constraint,
  (b) the Radner budget constraints with contingent trade in good `g` at `t = 0` and `t = 1`,
  (c) the budget sets coincide in both directions (`exercise_19_D_4c_i`, `exercise_19_D_4c_ii`).
-/

namespace MWG.EquilibriumUncertainty

open Matrix

/-! ## Example 19.D.1 and Exercise 19.D.2 -/

/-- The endowments of Example 19.D.1: consumer 1 owns `ω̄` in state 1, consumer 2 in state 2. -/
def omega19D1 (ωbar : Fin 2 → ℝ) : Fin 2 → CVec 2 2 :=
  fun i s => if i = s then ωbar else 0

/-- **Example 19.D.1** (MWG, pp. 697-698). Equal probabilities, a common state-independent Bernoulli
utility `u` concave on `ℝ²_+`. If `ω̄/2` maximizes `u` on `{y ≥ 0 : p̂·y ≤ p̂·ω̄/2}`, then giving
each consumer half of the aggregate endowment in each state is an Arrow-Debreu equilibrium at the
contingent prices `(p̂, p̂)`: the spot prices are the same in the two states. -/
theorem example_19_D_1 {u : (Fin 2 → ℝ) → ℝ} (hu : ConcaveOn ℝ {a | ∀ l, 0 ≤ a l} u)
    {ωbar phat : Fin 2 → ℝ} (hω : ∀ l, 0 ≤ ωbar l)
    (hmax : ∀ y : Fin 2 → ℝ, (∀ l, 0 ≤ y l) → phat ⬝ᵥ y ≤ phat ⬝ᵥ ((1 / 2 : ℝ) • ωbar) →
      u y ≤ u ((1 / 2 : ℝ) • ωbar)) :
    IsADEqmU (fun _ => expUtil (fun _ => 1 / 2) fun _ => u) (omega19D1 ωbar)
      (fun _ _ => (1 / 2 : ℝ) • ωbar) (fun _ => phat) := by
  have hval : ∀ i : Fin 2, cval (fun _ => phat) (omega19D1 ωbar i) = phat ⬝ᵥ ωbar := by
    intro i; fin_cases i <;> simp [cval, omega19D1, Fin.sum_univ_two]
  have hstar : cval (fun _ : Fin 2 => phat) (fun _ => (1 / 2 : ℝ) • ωbar) = phat ⬝ᵥ ωbar := by
    simp [cval]
  refine ⟨fun i => ⟨⟨fun s l => by simp; linarith [hω l], by rw [hstar, hval]⟩,
    fun x' hx' hb => ?_⟩, ?_⟩
  · rw [hval] at hb
    have hjen := hu.2 (hx' 0) (hx' 1) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    have hbud : phat ⬝ᵥ ((1 / 2 : ℝ) • x' 0 + (1 / 2 : ℝ) • x' 1) ≤
        phat ⬝ᵥ ((1 / 2 : ℝ) • ωbar) := by
      simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]
      simp only [cval, Fin.sum_univ_two] at hb
      linarith
    have hm := hmax _ (fun l => by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      nlinarith [hx' 0 l, hx' 1 l]) hbud
    simp only [expUtil, Fin.sum_univ_two, smul_eq_mul] at hjen ⊢
    linarith
  · funext s l
    fin_cases s <;> simp [omega19D1, Fin.sum_univ_two]

/-- **Example 19.D.1**, an instance: `u(y) = min(y₁, y₂)` (concave), `ω̄ = (1, 1)`,
`p̂ = (1, 1)`. -/
theorem example_19_D_1_instance :
    IsADEqmU (fun _ => expUtil (fun _ => 1 / 2) fun _ (y : Fin 2 → ℝ) => min (y 0) (y 1))
      (omega19D1 fun _ => 1) (fun _ _ => (1 / 2 : ℝ) • fun _ => 1) (fun _ _ => 1) := by
  refine example_19_D_1 ⟨?_, ?_⟩ (fun _ => zero_le_one) ?_
  · intro a ha b hb α β hα hβ _ l
    have := ha l; have := hb l
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; positivity
  · intro a _ b _ α β hα hβ _
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    refine le_min ?_ ?_
    · nlinarith [min_le_left (a 0) (a 1), min_le_left (b 0) (b 1)]
    · nlinarith [min_le_right (a 0) (a 1), min_le_right (b 0) (b 1)]
  · intro y _ hb
    have h1 : y 0 + y 1 ≤ 1 := by simpa [dotProduct, Fin.sum_univ_two] using hb
    simp only [Pi.smul_apply, smul_eq_mul, mul_one, min_self]
    rcases le_or_gt (y 0) (1 / 2) with h | h
    · exact (min_le_left _ _).trans h
    · exact (min_le_right _ _).trans (by linarith)

/-- **Example 19.D.1** (MWG, p. 698): with a strictly concave, strongly monotone `u`, every
Arrow-Debreu equilibrium allocation is state independent (the aggregate endowment is the same in
both states). -/
theorem example_19_D_1_stateIndependent {u : (Fin 2 → ℝ) → ℝ}
    (hc : StrictConcaveOn ℝ {a | ∀ l, 0 ≤ a l} u) (hm : StronglyMonotoneL u)
    {ωbar : Fin 2 → ℝ} {x : Fin 2 → CVec 2 2} {p : CVec 2 2}
    (h : IsADEqmU (fun _ => expUtil (fun _ => 1 / 2) fun _ => u) (omega19D1 ωbar) x p) :
    ∀ i, x i 0 = x i 1 := by
  have hpo := adEqmU_paretoOptimal (fun _ => expUtil_stronglyMonotone (fun _ => by norm_num)
    fun _ => hm) h
  have := po_stateIndependent (u := fun _ => u) (fun _ => by norm_num)
    (by simp) (fun _ => hc) (ω := omega19D1 ωbar)
    (fun s s' => by fin_cases s <;> fin_cases s' <;> simp [omega19D1]) hpo
  exact fun i => this i 0 1

/-- **Exercise 19.D.2** (MWG, p. 726), for Example 19.D.1. At the equilibrium of
`example_19_D_1` (with `p̂₁ > 0`), the contingent trades in good 1 of Proposition 19.D.1(i) are:
consumer 1 sells `α = p̂·ω̄ / (2 p̂₁)` units contingent on state 1 and buys `β = α` units contingent
on state 2; consumer 2 does the opposite; together with the common spot prices `p̂` they form a
Radner equilibrium. -/
theorem exercise_19_D_2 {u : (Fin 2 → ℝ) → ℝ} (hu : ConcaveOn ℝ {a | ∀ l, 0 ≤ a l} u)
    {ωbar phat : Fin 2 → ℝ} (hω : ∀ l, 0 ≤ ωbar l) (hp : 0 < phat 0)
    (hmax : ∀ y : Fin 2 → ℝ, (∀ l, 0 ≤ y l) → phat ⬝ᵥ y ≤ phat ⬝ᵥ ((1 / 2 : ℝ) • ωbar) →
      u y ≤ u ((1 / 2 : ℝ) • ωbar)) :
    let α := phat ⬝ᵥ ωbar / (2 * phat 0)
    let z : Fin 2 → Fin 2 → ℝ := fun i s =>
      (fun _ => phat) s ⬝ᵥ ((1 / 2 : ℝ) • ωbar - omega19D1 ωbar i s) / phat 0
    IsRadnerEqmD 0 (fun _ => expUtil (fun _ => 1 / 2) fun _ => u) (omega19D1 ωbar)
        (fun _ => phat 0) (fun _ => phat) (fun _ _ => (1 / 2 : ℝ) • ωbar) z ∧
      z 0 0 = -α ∧ z 0 1 = α ∧ z 1 0 = α ∧ z 1 1 = -α := by
  intro α z
  refine ⟨proposition_19_D_1_i 0 (fun _ => hp) (example_19_D_1 hu hω hmax), ?_⟩
  simp only [z, α, omega19D1, dotProduct_sub, dotProduct_smul, smul_eq_mul]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp <;> field_simp <;> ring

/-! ## Exercise 19.D.3: consumption at `t = 0` -/

variable {S L : ℕ}

/-- **Exercise 19.D.3** (MWG, p. 727). The Arrow-Debreu budget set with date-0 consumption
`x₀ ∈ ℝ^L_+` at prices `p₀`: `p₀·(x₀ - ω₀) + ∑_s p_s·(x_s - ω_s) ≤ 0`. -/
def adBudget0 (p₀ : Fin L → ℝ) (p : CVec S L) (ω₀ : Fin L → ℝ) (ω : CVec S L)
    (x₀ : Fin L → ℝ) (x : CVec S L) : Prop :=
  (∀ l, 0 ≤ x₀ l) ∧ NonnegC x ∧ p₀ ⬝ᵥ x₀ + cval p x ≤ p₀ ⬝ᵥ ω₀ + cval p ω

/-- **Exercise 19.D.3** (MWG, p. 727). The Radner budget set with a date-0 spot market:
`p₀·(x₀ - ω₀) + ∑_s q_s z_s ≤ 0` and `p_s·x_s ≤ p_s·ω_s + p_{gs} z_s`. -/
def radnerBudget0 (g : Fin L) (q : Fin S → ℝ) (p₀ : Fin L → ℝ) (p : CVec S L)
    (ω₀ : Fin L → ℝ) (ω : CVec S L) (x₀ : Fin L → ℝ) (x : CVec S L) : Prop :=
  (∀ l, 0 ≤ x₀ l) ∧ NonnegC x ∧ ∃ z : Fin S → ℝ, p₀ ⬝ᵥ x₀ + q ⬝ᵥ z ≤ p₀ ⬝ᵥ ω₀ ∧
    ∀ s, p s ⬝ᵥ x s ≤ p s ⬝ᵥ ω s + p s g * z s

/-- **Exercise 19.D.3** (MWG, p. 727), Proposition 19.D.1(i) remains valid: with `q_s = p_{gs} > 0`
(and the same date-0 prices) the two budget sets coincide, so Arrow-Debreu demands are Radner
demands; the contingent trades `z_s = p_s·(x_s - ω_s) / p_{gs}` clear when consumption does. -/
theorem exercise_19_D_3_i (g : Fin L) {p : CVec S L} (hp : ∀ s, 0 < p s g) (p₀ : Fin L → ℝ)
    (ω₀ : Fin L → ℝ) (ω : CVec S L) (x₀ : Fin L → ℝ) (x : CVec S L) :
    adBudget0 p₀ p ω₀ ω x₀ x ↔ radnerBudget0 g (fun s => p s g) p₀ p ω₀ ω x₀ x := by
  have key : ∀ y : CVec S L, (fun s => p s g) ⬝ᵥ (fun s => p s ⬝ᵥ y s / p s g) = cval p y := by
    intro y
    simp only [dotProduct, cval]
    exact Finset.sum_congr rfl fun s _ => by field_simp [(hp s).ne']
  constructor
  · rintro ⟨h0, hx, hb⟩
    refine ⟨h0, hx, fun s => p s ⬝ᵥ (x s - ω s) / p s g, ?_, fun s => ?_⟩
    · have := key (x - ω)
      simp only [Pi.sub_apply] at this
      rw [this, cval_sub]; linarith
    · rw [mul_div_cancel₀ _ (hp s).ne', dotProduct_sub]; linarith
  · rintro ⟨h0, hx, z, hz0, hzs⟩
    refine ⟨h0, hx, ?_⟩
    have h1 : ∑ s, (p s ⬝ᵥ x s - p s ⬝ᵥ ω s) ≤ ∑ s, p s g * z s :=
      Finset.sum_le_sum fun s _ => by linarith [hzs s]
    rw [Finset.sum_sub_distrib] at h1
    simp only [dotProduct] at hz0
    unfold cval
    simp only [dotProduct] at h1 ⊢
    linarith

/-- **Exercise 19.D.3** (MWG, p. 727), Proposition 19.D.1(ii) remains valid: with `q ≥ 0`,
`p_{gs} > 0` and `μ_s = q_s / p_{gs}`, the Radner budget set equals the Arrow-Debreu budget set
at the prices `(p₀, μ₁ p₁, …, μ_S p_S)`. -/
theorem exercise_19_D_3_ii (g : Fin L) {q : Fin S → ℝ} (hq : ∀ s, 0 ≤ q s) {p : CVec S L}
    (hp : ∀ s, 0 < p s g) (p₀ : Fin L → ℝ) (ω₀ : Fin L → ℝ) (ω : CVec S L) (x₀ : Fin L → ℝ)
    (x : CVec S L) :
    radnerBudget0 g q p₀ p ω₀ ω x₀ x ↔
      adBudget0 p₀ (fun s => (q s / p s g) • p s) ω₀ ω x₀ x := by
  constructor
  · rintro ⟨h0, hx, z, hz0, hzs⟩
    refine ⟨h0, hx, ?_⟩
    simp only [cval, smul_dotProduct, smul_eq_mul]
    have h1 : ∀ s, q s / p s g * (p s ⬝ᵥ x s) ≤ q s / p s g * (p s ⬝ᵥ ω s) + q s * z s := by
      intro s
      have := mul_le_mul_of_nonneg_left (hzs s) (div_nonneg (hq s) (hp s).le)
      rwa [mul_add, ← mul_assoc, div_mul_cancel₀ _ (hp s).ne'] at this
    have h2 := Finset.sum_le_sum fun s (_ : s ∈ Finset.univ) => h1 s
    rw [Finset.sum_add_distrib] at h2
    have hqz : q ⬝ᵥ z = ∑ s, q s * z s := rfl
    rw [hqz] at hz0
    linarith
  · rintro ⟨h0, hx, hb⟩
    refine ⟨h0, hx, fun s => p s ⬝ᵥ (x s - ω s) / p s g, ?_, fun s => ?_⟩
    · simp only [cval, smul_dotProduct, smul_eq_mul] at hb
      have e : q ⬝ᵥ (fun s => p s ⬝ᵥ (x s - ω s) / p s g) =
          ∑ s, q s / p s g * (p s ⬝ᵥ x s) - ∑ s, q s / p s g * (p s ⬝ᵥ ω s) := by
        simp only [dotProduct_sub]
        rw [dotProduct, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun s _ => by field_simp
      rw [e]; linarith
    · rw [mul_div_cancel₀ _ (hp s).ne', dotProduct_sub]; linarith

/-! ## Exercise 19.D.4: three dates, a binary tree -/

variable {H : ℕ}

/-- **Exercise 19.D.4(a)** (MWG, p. 727). The Arrow-Debreu budget constraint for the tree with
`t = 0, 1, 2`, two branches at each node and `H` goods consumed at every date: date-0 prices `p₀`,
node prices `p₁ b` at `t = 1` and `p₂ b c` at `t = 2`. -/
def adBudgetTree (p₀ : Fin H → ℝ) (p₁ : Fin 2 → Fin H → ℝ) (p₂ : Fin 2 → Fin 2 → Fin H → ℝ)
    (ω₀ x₀ : Fin H → ℝ) (ω₁ x₁ : Fin 2 → Fin H → ℝ) (ω₂ x₂ : Fin 2 → Fin 2 → Fin H → ℝ) :
    Prop :=
  p₀ ⬝ᵥ (x₀ - ω₀) + ∑ b, p₁ b ⬝ᵥ (x₁ b - ω₁ b) + ∑ b, ∑ c, p₂ b c ⬝ᵥ (x₂ b c - ω₂ b c) ≤ 0

/-- **Exercise 19.D.4(b)** (MWG, p. 727). The Radner budget constraints: at `t = 0` spot trade
and contingent trade `z₀ b` in good `g` deliverable at node `b` (prices `q₀ b`); at node `b` spot
trade at `P₁ b` and contingent trade `z₁ b c` in good `g` deliverable at `(b, c)` (prices
`q₁ b c`), financed by the delivery `P₁ b g · z₀ b`; at `(b, c)` spot trade financed by
`P₂ b c g · z₁ b c`. -/
def radnerBudgetTree (g : Fin H) (q₀ : Fin 2 → ℝ) (q₁ : Fin 2 → Fin 2 → ℝ) (p₀ : Fin H → ℝ)
    (P₁ : Fin 2 → Fin H → ℝ) (P₂ : Fin 2 → Fin 2 → Fin H → ℝ) (ω₀ x₀ : Fin H → ℝ)
    (ω₁ x₁ : Fin 2 → Fin H → ℝ) (ω₂ x₂ : Fin 2 → Fin 2 → Fin H → ℝ) : Prop :=
  ∃ (z₀ : Fin 2 → ℝ) (z₁ : Fin 2 → Fin 2 → ℝ), p₀ ⬝ᵥ (x₀ - ω₀) + ∑ b, q₀ b * z₀ b ≤ 0 ∧
    (∀ b, P₁ b ⬝ᵥ (x₁ b - ω₁ b) + ∑ c, q₁ b c * z₁ b c ≤ P₁ b g * z₀ b) ∧
    ∀ b c, P₂ b c ⬝ᵥ (x₂ b c - ω₂ b c) ≤ P₂ b c g * z₁ b c

/-- **Exercise 19.D.4(c)** (MWG, p. 727), the direction of Proposition 19.D.1(i). Given
Arrow-Debreu prices with `p₁ b g > 0` and `p₂ b c g > 0`, use them as spot prices and price the
contingent claims at `q₀ b = p₁ b g`, `q₁ b c = p₂ b c g`. Then the two budget sets coincide. -/
theorem exercise_19_D_4c_i (g : Fin H) (p₀ : Fin H → ℝ) {p₁ : Fin 2 → Fin H → ℝ}
    {p₂ : Fin 2 → Fin 2 → Fin H → ℝ} (h1 : ∀ b, 0 < p₁ b g) (h2 : ∀ b c, 0 < p₂ b c g)
    (ω₀ x₀ : Fin H → ℝ) (ω₁ x₁ : Fin 2 → Fin H → ℝ) (ω₂ x₂ : Fin 2 → Fin 2 → Fin H → ℝ) :
    adBudgetTree p₀ p₁ p₂ ω₀ x₀ ω₁ x₁ ω₂ x₂ ↔
      radnerBudgetTree g (fun b => p₁ b g) (fun b c => p₂ b c g) p₀ p₁ p₂ ω₀ x₀ ω₁ x₁ ω₂ x₂ := by
  constructor
  · intro h
    set z₁ : Fin 2 → Fin 2 → ℝ := fun b c => p₂ b c ⬝ᵥ (x₂ b c - ω₂ b c) / p₂ b c g with hz₁
    set z₀ : Fin 2 → ℝ := fun b =>
      (p₁ b ⬝ᵥ (x₁ b - ω₁ b) + ∑ c, p₂ b c g * z₁ b c) / p₁ b g with hz₀
    have e1 : ∀ b c, p₂ b c g * z₁ b c = p₂ b c ⬝ᵥ (x₂ b c - ω₂ b c) := fun b c => by
      rw [hz₁]; field_simp [(h2 b c).ne']
    have e0 : ∀ b, p₁ b g * z₀ b = p₁ b ⬝ᵥ (x₁ b - ω₁ b) + ∑ c, p₂ b c g * z₁ b c := fun b => by
      rw [hz₀]; field_simp [(h1 b).ne']
    refine ⟨z₀, z₁, ?_, fun b => (e0 b).ge, fun b c => (e1 b c).ge⟩
    simp only [e0, e1]
    unfold adBudgetTree at h
    rw [Finset.sum_add_distrib]
    linarith
  · rintro ⟨z₀, z₁, hr, hb, hbc⟩
    unfold adBudgetTree
    have k1 : ∀ b, p₁ b ⬝ᵥ (x₁ b - ω₁ b) + ∑ c, p₂ b c ⬝ᵥ (x₂ b c - ω₂ b c) ≤ p₁ b g * z₀ b :=
      fun b => by
        have := Finset.sum_le_sum fun c (_ : c ∈ Finset.univ) => hbc b c
        linarith [hb b]
    have := Finset.sum_le_sum fun b (_ : b ∈ Finset.univ) => k1 b
    rw [Finset.sum_add_distrib] at this
    linarith

/-- **Exercise 19.D.4(c)** (MWG, p. 727), the direction of Proposition 19.D.1(ii). Given Radner
prices with `q₀, q₁ ≥ 0` and positive spot prices of good `g`, the multipliers
`μ₁ b = q₀ b / P₁ b g` and `μ₂ b c = μ₁ b q₁ b c / P₂ b c g` turn the Radner budget set into the
Arrow-Debreu budget set at the prices `(p₀, μ₁ b P₁ b, μ₂ b c P₂ b c)`. -/
theorem exercise_19_D_4c_ii (g : Fin H) {q₀ : Fin 2 → ℝ} {q₁ : Fin 2 → Fin 2 → ℝ}
    (hq₀ : ∀ b, 0 ≤ q₀ b) (hq₁ : ∀ b c, 0 ≤ q₁ b c) (p₀ : Fin H → ℝ)
    {P₁ : Fin 2 → Fin H → ℝ} {P₂ : Fin 2 → Fin 2 → Fin H → ℝ} (h1 : ∀ b, 0 < P₁ b g)
    (h2 : ∀ b c, 0 < P₂ b c g) (ω₀ x₀ : Fin H → ℝ) (ω₁ x₁ : Fin 2 → Fin H → ℝ)
    (ω₂ x₂ : Fin 2 → Fin 2 → Fin H → ℝ) :
    radnerBudgetTree g q₀ q₁ p₀ P₁ P₂ ω₀ x₀ ω₁ x₁ ω₂ x₂ ↔
      adBudgetTree p₀ (fun b => (q₀ b / P₁ b g) • P₁ b)
        (fun b c => (q₀ b / P₁ b g * q₁ b c / P₂ b c g) • P₂ b c) ω₀ x₀ ω₁ x₁ ω₂ x₂ := by
  have hμ1 : ∀ b, 0 ≤ q₀ b / P₁ b g := fun b => div_nonneg (hq₀ b) (h1 b).le
  constructor
  · rintro ⟨z₀, z₁, hr, hb, hbc⟩
    unfold adBudgetTree
    simp only [smul_dotProduct, smul_eq_mul]
    have k2 : ∀ b c, q₀ b / P₁ b g * q₁ b c / P₂ b c g * (P₂ b c ⬝ᵥ (x₂ b c - ω₂ b c)) ≤
        q₀ b / P₁ b g * (q₁ b c * z₁ b c) := by
      intro b c
      have := mul_le_mul_of_nonneg_left (hbc b c)
        (div_nonneg (mul_nonneg (hμ1 b) (hq₁ b c)) (h2 b c).le)
      calc q₀ b / P₁ b g * q₁ b c / P₂ b c g * (P₂ b c ⬝ᵥ (x₂ b c - ω₂ b c))
          ≤ q₀ b / P₁ b g * q₁ b c / P₂ b c g * (P₂ b c g * z₁ b c) := this
        _ = q₀ b / P₁ b g * (q₁ b c * z₁ b c) := by field_simp [(h2 b c).ne']
    have k1 : ∀ b, q₀ b / P₁ b g * (P₁ b ⬝ᵥ (x₁ b - ω₁ b)) +
        ∑ c, q₀ b / P₁ b g * q₁ b c / P₂ b c g * (P₂ b c ⬝ᵥ (x₂ b c - ω₂ b c)) ≤ q₀ b * z₀ b := by
      intro b
      have hs := Finset.sum_le_sum fun c (_ : c ∈ Finset.univ) => k2 b c
      rw [← Finset.mul_sum] at hs
      have := mul_le_mul_of_nonneg_left (hb b) (hμ1 b)
      rw [mul_add] at this
      have e : q₀ b / P₁ b g * (P₁ b g * z₀ b) = q₀ b * z₀ b := by field_simp [(h1 b).ne']
      linarith
    have := Finset.sum_le_sum fun b (_ : b ∈ Finset.univ) => k1 b
    rw [Finset.sum_add_distrib] at this
    linarith
  · intro h
    unfold adBudgetTree at h
    simp only [smul_dotProduct, smul_eq_mul] at h
    set z₁ : Fin 2 → Fin 2 → ℝ := fun b c => P₂ b c ⬝ᵥ (x₂ b c - ω₂ b c) / P₂ b c g with hz₁
    set z₀ : Fin 2 → ℝ := fun b =>
      (P₁ b ⬝ᵥ (x₁ b - ω₁ b) + ∑ c, q₁ b c * z₁ b c) / P₁ b g with hz₀
    have e1 : ∀ b c, P₂ b c g * z₁ b c = P₂ b c ⬝ᵥ (x₂ b c - ω₂ b c) := fun b c => by
      rw [hz₁]; field_simp [(h2 b c).ne']
    have e0 : ∀ b, P₁ b g * z₀ b = P₁ b ⬝ᵥ (x₁ b - ω₁ b) + ∑ c, q₁ b c * z₁ b c := fun b => by
      rw [hz₀]; field_simp [(h1 b).ne']
    refine ⟨z₀, z₁, ?_, fun b => (e0 b).ge, fun b c => (e1 b c).ge⟩
    have e2 : ∀ b, q₀ b * z₀ b = q₀ b / P₁ b g * (P₁ b ⬝ᵥ (x₁ b - ω₁ b)) +
        ∑ c, q₀ b / P₁ b g * q₁ b c / P₂ b c g * (P₂ b c ⬝ᵥ (x₂ b c - ω₂ b c)) := by
      intro b
      have : q₀ b * z₀ b = q₀ b / P₁ b g * (P₁ b ⬝ᵥ (x₁ b - ω₁ b) + ∑ c, q₁ b c * z₁ b c) := by
        rw [hz₀]; field_simp
      rw [this, mul_add, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun c _ => by rw [hz₁]; ring
    simp only [e2, Finset.sum_add_distrib]
    linarith

end MWG.EquilibriumUncertainty
