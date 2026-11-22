/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGProduction.Profit

/-!
# Remarks on the objectives of the firm (MWG Section 5.G, pp. 152-154)

Section 5.G has no numbered proposition; its mathematical content is the unanimity argument.

* Unanimity (pp. 152-153): with fixed prices, owner `i` (share `θ_i ≥ 0`, nonprofit wealth
  `w_i`) has budget set `{x ≥ 0 : p·x ≤ w_i + θ_i p·y}`. A plan with higher profit enlarges every
  owner's budget set (`unanimity_budget`), so every owner's maximal utility weakly increases
  (`unanimity_value`); with `θ_i > 0` and a strongly monotone utility, every bundle affordable
  before is strictly beaten (`unanimity_strict`). Hence all owners agree that the manager should
  maximize profits (`unanimity_profit_max`).
* (i) When prices depend on the firm's output, owners' objectives differ: the example on p. 153
  with `f(z) = z` and `p(q) = 2 - q` (`price_dependence_example`).
* **Exercise 5.G.1** (p. 164): (a) at a unanimously chosen interior plan consumption shares equal
  ownership shares (`exercise_5_G_1a`), (b) with equal shares unanimity forces equal consumption
  (`exercise_5_G_1b`), (c) with identical preferences and shares all owners have the same
  objective (`exercise_5_G_1c`); that common objective is not profit maximization in general
  (`exercise_5_G_1c_not_profit`, correction).
-/

namespace MWG.Production

open MWG.ClassicalDemand MWG.ConsumerChoice Filter Topology

variable {L : ℕ}

/-- **Section 5.G** (MWG, p. 152). Owner `i`'s budget set when the firm chooses `y`:
`{x ≥ 0 : p·x ≤ w_i + θ_i p·y}`. -/
def ownerBudget (p : Fin L → ℝ) (w θ : ℝ) (y : Fin L → ℝ) : Set (Fin L → ℝ) :=
  {x | 0 ≤ x ∧ p ⬝ᵥ x ≤ w + θ * (p ⬝ᵥ y)}

/-- **Section 5.G** (MWG, p. 152). Higher profit expands every owner's budget set. -/
theorem unanimity_budget (p : Fin L → ℝ) (w : ℝ) {θ : ℝ} (hθ : 0 ≤ θ) {y y' : Fin L → ℝ}
    (h : p ⬝ᵥ y ≤ p ⬝ᵥ y') : ownerBudget p w θ y ⊆ ownerBudget p w θ y' :=
  fun _ hx => ⟨hx.1, hx.2.trans (by nlinarith)⟩

/-- **Section 5.G** (MWG, pp. 152-153). Whatever her utility function, each owner's maximal
utility is at least as high under the plan with higher profit. -/
theorem unanimity_value (u : (Fin L → ℝ) → ℝ) (p : Fin L → ℝ) (w : ℝ) {θ : ℝ} (hθ : 0 ≤ θ)
    {y y' : Fin L → ℝ} (h : p ⬝ᵥ y ≤ p ⬝ᵥ y') {v v' : ℝ}
    (hv : IsGreatest (u '' ownerBudget p w θ y) v)
    (hv' : IsGreatest (u '' ownerBudget p w θ y') v') : v ≤ v' := by
  obtain ⟨⟨x, hx, rfl⟩, -⟩ := hv
  exact hv'.2 ⟨x, unanimity_budget p w hθ h hx, rfl⟩

/-- **Section 5.G** (MWG, p. 152). With `θ_i > 0`, `p ≫ 0` and a strongly monotone utility, a
plan with strictly higher profit is strictly better for owner `i`: every bundle affordable under
`y` is beaten by one affordable under `y'`. -/
theorem unanimity_strict (hL : 0 < L) (u : (Fin L → ℝ) → ℝ)
    (hu : ∀ x x', x ≤ x' → x ≠ x' → u x < u x') {p : Fin L → ℝ} (hp : StrictlyPositive p)
    (w : ℝ) {θ : ℝ} (hθ : 0 < θ) {y y' : Fin L → ℝ} (h : p ⬝ᵥ y < p ⬝ᵥ y') {x : Fin L → ℝ}
    (hx : x ∈ ownerBudget p w θ y) : ∃ x' ∈ ownerBudget p w θ y', u x < u x' := by
  set l : Fin L := ⟨0, hL⟩
  set t := θ * (p ⬝ᵥ y' - p ⬝ᵥ y) / p l with ht
  have htpos : 0 < t := div_pos (mul_pos hθ (by linarith)) (hp l)
  refine ⟨x + t • Pi.single l 1, ⟨?_, ?_⟩, hu _ _ ?_ ?_⟩
  · exact add_nonneg hx.1 (smul_nonneg htpos.le (Pi.single_nonneg.mpr zero_le_one))
  · rw [dotProduct_add, dotProduct_smul, dotProduct_single, mul_one, smul_eq_mul, ht,
      div_mul_cancel₀ _ (hp l).ne']
    have := hx.2
    nlinarith
  · exact le_add_of_nonneg_right (smul_nonneg htpos.le (Pi.single_nonneg.mpr zero_le_one))
  · intro he
    have := congrFun he l
    simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at this
    linarith

/-- **Section 5.G** (MWG, p. 153). All owners agree on profit maximization: if `y* ∈ y(p)`, then for
every feasible `y` and every owner, the budget set under `y` is contained in that under `y*`. -/
theorem unanimity_profit_max {Y : Set (Fin L → ℝ)} {p ys : Fin L → ℝ} (hys : ys ∈ supply Y p)
    {y : Fin L → ℝ} (hy : y ∈ Y) (w : ℝ) {θ : ℝ} (hθ : 0 ≤ θ) :
    ownerBudget p w θ y ⊆ ownerBudget p w θ ys :=
  unanimity_budget p w hθ (hys.2 y hy)

/-- **Section 5.G** (MWG, p. 153), remark (i). With `w_i = 0`, `f(z) = z` and the price of good 1
`p(q) = 2 - q` (good 2 the numeraire), owners who consume only good 2 maximize
`A(z) = p(f(z))f(z) - z = z - z²`, whose unique maximizer is `z = 1/2`; owners who consume only
good 1 maximize `B(z) = f(z) - z/p(f(z)) = z - z/(2 - z)`, and strictly prefer `z = 3/5` to
`z = 1/2`. The two problems have different solutions. -/
theorem price_dependence_example :
    (∀ z : ℝ, z ≠ 1 / 2 → (2 - z) * z - z < (2 - 1 / 2) * (1 / 2) - 1 / 2) ∧
      (1 / 2 : ℝ) - (1 / 2) / (2 - 1 / 2) < (3 / 5 : ℝ) - (3 / 5) / (2 - 3 / 5) := by
  refine ⟨fun z hz => ?_, by norm_num⟩
  have : 0 < (z - 1 / 2) ^ 2 := by
    have : z - 1 / 2 ≠ 0 := sub_ne_zero.mpr hz
    positivity
  nlinarith

/-- **Exercise 5.G.1(a)** (MWG, p. 164). Owners `i` have quasilinear utility in the input
(numeraire), so owner `i`'s welfare from plan `z` is `W_i(z) = v_i(p(z)) + θ_i π(z)`, with
`v_i'(p) = -x_i(p)` (envelope). If `z̄` is a local maximum of every `W_i` (unanimity),
`p'(z̄) ≠ 0`, the output market clears (`Σ_i x_i = f(z̄)`) and `Σ_i θ_i = 1`, then consumption
shares equal ownership shares: `x_i = θ_i f(z̄)`. -/
theorem exercise_5_G_1a {I : ℕ} {v : Fin I → ℝ → ℝ} {pr π : ℝ → ℝ} {θ x : Fin I → ℝ}
    {z q p' π' : ℝ} (hv : ∀ i, HasDerivAt (v i) (-x i) (pr z)) (hp : HasDerivAt pr p' z)
    (hπ : HasDerivAt π π' z) (hp' : p' ≠ 0)
    (hmax : ∀ i, IsLocalMax (fun t => v i (pr t) + θ i * π t) z)
    (hclear : ∑ i, x i = q) (hθ : ∑ i, θ i = 1) : ∀ i, x i = θ i * q := by
  have hfoc : ∀ i, -x i * p' + θ i * π' = 0 := by
    intro i
    have hd := ((hv i).comp z hp).add (hπ.const_mul (θ i))
    exact (hmax i).hasDerivAt_eq_zero hd
  have hsum : -q * p' + π' = 0 := by
    have := Finset.sum_eq_zero (s := Finset.univ) fun i (_ : i ∈ Finset.univ) => hfoc i
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, Finset.sum_neg_distrib,
      hclear, hθ, one_mul] at this
    exact this
  intro i
  have h1 := hfoc i
  have h2 : π' = q * p' := by linarith
  rw [h2] at h1
  have h3 : (θ i * q - x i) * p' = 0 := by linarith
  rcases mul_eq_zero.mp h3 with h | h
  · linarith
  · exact absurd h hp'

/-- **Exercise 5.G.1(b)** (MWG, p. 164). With identical ownership shares `θ_i = 1/I`, unanimity at
an interior plan forces all owners to consume the same amount of output; owners whose tastes lead to
different consumption at `p(z̄)` give conflicting instructions. -/
theorem exercise_5_G_1b {I : ℕ} {v : Fin I → ℝ → ℝ} {pr π : ℝ → ℝ} {x : Fin I → ℝ}
    {z q p' π' : ℝ} (hI : 0 < I) (hv : ∀ i, HasDerivAt (v i) (-x i) (pr z))
    (hp : HasDerivAt pr p' z) (hπ : HasDerivAt π π' z) (hp' : p' ≠ 0)
    (hmax : ∀ i, IsLocalMax (fun t => v i (pr t) + (1 / I : ℝ) * π t) z)
    (hclear : ∑ i, x i = q) : ∀ i j, x i = x j := by
  have hθ : ∑ _i : Fin I, (1 / I : ℝ) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have := exercise_5_G_1a (θ := fun _ => 1 / I) hv hp hπ hp' hmax hclear hθ
  intro i j
  rw [this i, this j]

/-- **Exercise 5.G.1(c)** (MWG, p. 164). With identical preferences and ownership shares, all owners
have the same objective `W(z) = v(p(z)) + θ π(z)`, so they agree on the plan. -/
theorem exercise_5_G_1c {I : ℕ} (v : ℝ → ℝ) (pr π : ℝ → ℝ) (θ : ℝ) (i j : Fin I) :
    (fun (_ : Fin I) (t : ℝ) => v (pr t) + θ * π t) i =
      (fun (_ : Fin I) (t : ℝ) => v (pr t) + θ * π t) j :=
  rfl

/-- **Exercise 5.G.1(c)** (MWG, p. 164): the common objective is not profit maximization
(correction). One owner (`θ = 1`) with utility `2√x - z` for output `x` and input `z`, `f(z) = z`:
the inverse demand is `p(q) = 1/√q`, the owner's welfare is `W(z) = 2√z - z`, maximized at
`z = 1`, while profit `π(z) = p(z)z - z = √z - z` is maximized at `z = 1/4`. -/
theorem exercise_5_G_1c_not_profit :
    (∀ z : ℝ, 0 ≤ z → 2 * Real.sqrt z - z ≤ 2 * Real.sqrt 1 - 1) ∧
      (∀ z : ℝ, 0 ≤ z → Real.sqrt z - z ≤ Real.sqrt (1 / 4) - 1 / 4) ∧
      Real.sqrt 1 - 1 < Real.sqrt (1 / 4) - 1 / 4 := by
  have h14 : Real.sqrt (1 / 4) = 1 / 2 := by
    rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  refine ⟨fun z hz => ?_, fun z hz => ?_, ?_⟩
  · have hs := Real.sq_sqrt hz
    rw [Real.sqrt_one]
    nlinarith [sq_nonneg (Real.sqrt z - 1)]
  · have hs := Real.sq_sqrt hz
    rw [h14]
    nlinarith [sq_nonneg (Real.sqrt z - 1 / 2)]
  · rw [h14, Real.sqrt_one]
    norm_num

end MWG.Production
