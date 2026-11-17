/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGProduction.ExercisesC
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Exercise 5.C.7: the explicit counterexample and the `n`-input correction (MWG, p. 161)

`ExercisesC` refutes Exercise 5.C.7 at the level of the first-order conditions. Here:

* **The counterexample realized.** For `f(z) = -e^{-z₁} - e^{-z₂} - e^{-z₁-z₂}` (increasing,
  strictly concave, `∂²f/∂z₁∂z₂ = -e^{-z₁-z₂} < 0`; `c7f_technology`) the profit-maximizing input
  demand has the closed form `z_ℓ(p, w) = -ln u_ℓ`, where, with `r = w/p` and `d = r₁ - r₂`,
  `u₁ = (d - 1 + √((1-d)² + 4r₁))/2` and `u₂ = u₁ - d` (`c7demand`). It is the unique
  maximizer of `p f(z) - w·z` for every `p > 0`, `w ≫ 0` (`exercise_5_C_7_demand`); at `p = 1`,
  `w = (3/4, 3/4)` it is `(ln 2, ln 2)` and `∂z₁/∂w₂ = 1/2 > 0`
  (`exercise_5_C_7_explicit_counterexample`), against the printed claim `∂z₁/∂w₂ < 0`.
* **The corrected statement for `n` inputs** (`exercise_5_C_7_corrected_n`): if `D²f(z)` is
  negative definite with all cross partials `∂²f/∂z_ℓ∂z_k > 0` (complementary inputs), then
  every input demand falls with every input price (`∂z_ℓ/∂w_k < 0`, all `ℓ, k`) and rises with
  the output price when `∇f ≥ 0`, `∇f ≠ 0`. The key fact (`negDef_offdiag_pos_solution_pos`) is
  that `-D²f` is a nonsingular M-matrix with a strictly positive inverse.
-/

namespace MWG.Production

open MWG.ClassicalDemand MWG.ConsumerChoice Filter Topology

/-! ### The `n`-input corrected statement -/

/-- If `H` is negative definite with positive off-diagonal entries and `p > 0`, the solution of
`pHx = -b` with `b ≥ 0`, `b ≠ 0` is strictly positive (`-pH` is a nonsingular M-matrix). -/
theorem negDef_offdiag_pos_solution_pos {n : ℕ} {H : Matrix (Fin n) (Fin n) ℝ}
    (hneg : NegDef H) (hoff : ∀ i j, i ≠ j → 0 < H i j) {p : ℝ} (hp : 0 < p)
    {x b : Fin n → ℝ} (hx : Matrix.mulVec (p • H) x = -b) (hb : 0 ≤ b) (hb0 : b ≠ 0) :
    ∀ i, 0 < x i := by
  have hrow : ∀ i, p * ∑ j, H i j * x j = -b i := by
    intro i
    have := congrFun hx i
    simpa [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc] using this
  have hrow' : ∀ i, ∑ j, H i j * x j ≤ 0 := by
    intro i
    have h := hrow i
    have := hb i
    by_contra hc
    push Not at hc
    have : 0 < p * ∑ j, H i j * x j := mul_pos hp hc
    simp only [Pi.zero_apply] at *
    linarith
  -- step 1: `x ≥ 0`
  set m : Fin n → ℝ := fun i => max (-x i) 0 with hm
  set xp : Fin n → ℝ := fun i => max (x i) 0 with hxp
  have hx_eq : ∀ j, x j = xp j - m j := by
    intro j
    simp only [hm, hxp]
    rcases le_total 0 (x j) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  have hm0 : ∀ j, 0 ≤ m j := fun j => le_max_right _ _
  have hxp0 : ∀ j, 0 ≤ xp j := fun j => le_max_right _ _
  have hmxp : ∀ j, m j * xp j = 0 := by
    intro j
    simp only [hm, hxp]
    rcases le_total 0 (x j) with h | h
    · rw [max_eq_right (by linarith)]; ring
    · rw [max_eq_right h]; ring
  have hcross : 0 ≤ ∑ i, m i * ∑ j, H i j * xp j := by
    refine Finset.sum_nonneg fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_nonneg fun j _ => ?_
    by_cases hij : i = j
    · subst hij
      rw [show m i * (H i i * xp i) = H i i * (m i * xp i) by ring, hmxp, mul_zero]
    · exact mul_nonneg (hm0 i) (mul_nonneg (hoff i j hij).le (hxp0 j))
  have hmx : ∑ i, m i * ∑ j, H i j * x j ≤ 0 :=
    Finset.sum_nonpos fun i _ => mul_nonpos_of_nonneg_of_nonpos (hm0 i) (hrow' i)
  have hsplit : ∑ i, m i * ∑ j, H i j * x j =
      ∑ i, m i * ∑ j, H i j * xp j - ∑ i, m i * ∑ j, H i j * m j := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hx_eq j]; ring
  have hmm : 0 ≤ m ⬝ᵥ H.mulVec m := by
    have : m ⬝ᵥ H.mulVec m = ∑ i, m i * ∑ j, H i j * m j := by
      simp [dotProduct, Matrix.mulVec]
    rw [this]
    linarith
  have hmz : m = 0 := by
    by_contra hne
    have := hneg m hne
    linarith
  have hxnn : ∀ j, 0 ≤ x j := by
    intro j
    have := congrFun hmz j
    simp only [hm, Pi.zero_apply] at this
    have h2 : -x j ≤ 0 := by rw [← this]; exact le_max_left _ _
    linarith
  -- step 2: strict positivity
  intro i
  rcases (hxnn i).lt_or_eq with h | h
  · exact h
  · exfalso
    have hterms : ∀ j ∈ Finset.univ, 0 ≤ H i j * x j := by
      intro j _
      by_cases hij : i = j
      · subst hij; rw [← h, mul_zero]
      · exact mul_nonneg (hoff i j hij).le (hxnn j)
    have hsum0 : ∑ j, H i j * x j = 0 :=
      le_antisymm (hrow' i) (Finset.sum_nonneg hterms)
    have hall := (Finset.sum_eq_zero_iff_of_nonneg hterms).mp hsum0
    have hx0 : x = 0 := by
      funext j
      by_cases hij : i = j
      · subst hij; exact h.symm
      · have := hall j (Finset.mem_univ j)
        rcases mul_eq_zero.mp this with h1 | h1
        · exact absurd h1 (hoff i j hij).ne'
        · exact h1
    apply hb0
    funext k
    have := hrow k
    simp only [hx0, Pi.zero_apply, mul_zero, Finset.sum_const_zero] at this
    simp only [Pi.zero_apply]
    linarith

/-- **Exercise 5.C.7** (MWG, p. 161), corrected, for `n` inputs. Let `H = D²f(z)` be negative
definite with all cross partials positive (`∂²f/∂z_ℓ∂z_k > 0`, complementary inputs) and
`p > 0`. Differentiating the first-order conditions `p∇f(z(p, w)) = w`, the derivative `v` of the
demands in `w_k` solves `pHv = e_k` and is strictly negative in every component
(`∂z_ℓ/∂w_k < 0` for all `ℓ`, `k`); the derivative in `p` solves `pHv = -∇f` and is strictly
positive when `∇f ≥ 0`, `∇f ≠ 0`. -/
theorem exercise_5_C_7_corrected_n {n : ℕ} {H : Matrix (Fin n) (Fin n) ℝ} (hneg : NegDef H)
    (hoff : ∀ i j, i ≠ j → 0 < H i j) {p : ℝ} (hp : 0 < p) :
    (∀ (k : Fin n) (v : Fin n → ℝ), Matrix.mulVec (p • H) v = Pi.single k 1 → ∀ l, v l < 0) ∧
      (∀ g v : Fin n → ℝ, 0 ≤ g → g ≠ 0 → Matrix.mulVec (p • H) v = -g → ∀ l, 0 < v l) := by
  refine ⟨fun k v hv l => ?_, fun g v hg hg0 hv l =>
    negDef_offdiag_pos_solution_pos hneg hoff hp hv hg hg0 l⟩
  have hv' : Matrix.mulVec (p • H) (-v) = -Pi.single k 1 := by
    rw [Matrix.mulVec_neg, hv]
  have hs : (0 : Fin n → ℝ) ≤ Pi.single k 1 := Pi.single_nonneg.mpr zero_le_one
  have hs0 : (Pi.single k 1 : Fin n → ℝ) ≠ 0 := by
    intro h
    have := congrFun h k
    simp at this
  have := negDef_offdiag_pos_solution_pos hneg hoff hp hv' hs hs0 l
  simp only [Pi.neg_apply] at this
  linarith

/-- The matrix `[[-3, 1, 1], [1, -3, 1], [1, 1, -3]]`, the Hessian of the concave quadratic
`f(z) = c·z - (3/2)Σz_ℓ² + Σ_{ℓ<k} z_ℓ z_k`. -/
def c7H3 : Matrix (Fin 3) (Fin 3) ℝ := !![-3, 1, 1; 1, -3, 1; 1, 1, -3]

/-- The matrix `c7H3` satisfies the hypotheses of `exercise_5_C_7_corrected_n`. -/
theorem exercise_5_C_7_corrected_n_instance :
    NegDef c7H3 ∧ ∀ i j : Fin 3, i ≠ j → 0 < c7H3 i j := by
  refine ⟨fun z hz => ?_, fun i j hij => ?_⟩
  · have hform : z ⬝ᵥ Matrix.mulVec c7H3 z =
        -(z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2) - ((z 0 - z 1) ^ 2 + (z 0 - z 2) ^ 2 + (z 1 - z 2) ^ 2) := by
      simp [c7H3, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
      ring
    rw [hform]
    have : z 0 ≠ 0 ∨ z 1 ≠ 0 ∨ z 2 ≠ 0 := by
      by_contra h
      push Not at h
      exact hz (funext fun i => by fin_cases i <;> simp [h.1, h.2.1, h.2.2])
    rcases this with h | h | h
    · have := sq_pos_of_ne_zero h
      nlinarith [sq_nonneg (z 1), sq_nonneg (z 2), sq_nonneg (z 0 - z 1), sq_nonneg (z 0 - z 2),
        sq_nonneg (z 1 - z 2)]
    · have := sq_pos_of_ne_zero h
      nlinarith [sq_nonneg (z 0), sq_nonneg (z 2), sq_nonneg (z 0 - z 1), sq_nonneg (z 0 - z 2),
        sq_nonneg (z 1 - z 2)]
    · have := sq_pos_of_ne_zero h
      nlinarith [sq_nonneg (z 0), sq_nonneg (z 1), sq_nonneg (z 0 - z 1), sq_nonneg (z 0 - z 2),
        sq_nonneg (z 1 - z 2)]
  · fin_cases i <;> fin_cases j <;> simp_all [c7H3]

/-! ### The counterexample with an explicit demand function -/

/-- The technology `f(z) = -e^{-z₁} - e^{-z₂} - e^{-z₁-z₂}`. -/
noncomputable def c7f (z : Fin 2 → ℝ) : ℝ :=
  -(Real.exp (-z 0) + Real.exp (-z 1) + Real.exp (-z 0 - z 1))

/-- `u₁ = e^{-z₁}` at the optimum, as a function of the real input prices `r = w/p`. -/
noncomputable def c7u (r₀ r₁ : ℝ) : ℝ :=
  (r₀ - r₁ - 1 + Real.sqrt ((1 - r₀ + r₁) ^ 2 + 4 * r₀)) / 2

/-- `u₂ = e^{-z₂} = u₁ - (r₁ - r₂)` at the optimum. -/
noncomputable def c7v (r₀ r₁ : ℝ) : ℝ := c7u r₀ r₁ - (r₀ - r₁)

/-- The closed-form input demand `z(p, w) = (-ln u₁, -ln u₂)` for `f = c7f`. -/
noncomputable def c7demand (p : ℝ) (w : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![-Real.log (c7u (w 0 / p) (w 1 / p)), -Real.log (c7v (w 0 / p) (w 1 / p))]

/-- **Exercise 5.C.7** (MWG, p. 161): `c7f` meets the exercise's hypotheses. It is strictly
increasing in each input (`∂f/∂z₁ = e^{-z₁} + e^{-z₁-z₂} > 0`), strictly concave, and its cross
partial is `∂²f/∂z₂∂z₁ = -e^{-z₁-z₂} < 0`. -/
theorem c7f_technology (s t : ℝ) :
    HasDerivAt (fun x => c7f ![x, t]) (Real.exp (-s) + Real.exp (-s - t)) s ∧
      0 < Real.exp (-s) + Real.exp (-s - t) ∧
      HasDerivAt (fun y => Real.exp (-s) + Real.exp (-s - y)) (-Real.exp (-s - t)) t ∧
      -Real.exp (-s - t) < 0 ∧ StrictConcaveOn ℝ Set.univ c7f := by
  refine ⟨?_, by positivity, ?_, by simp [Real.exp_pos], ?_⟩
  · have h1 := ((hasDerivAt_id s).neg).exp
    have h2 := ((hasDerivAt_id s).neg.sub_const t).exp
    have h := ((h1.add_const (Real.exp (-t))).add h2).neg
    convert h using 1
    · funext x; simp [c7f]
    · simp; ring
  · have h := (((hasDerivAt_id t).const_sub (-s)).exp).const_add (Real.exp (-s))
    convert h using 1
    · funext y; simp [sub_eq_add_neg]
    · simp
  · refine ⟨convex_univ, fun x _ y _ hxy a b ha hb hab => ?_⟩
    have hcv : ∀ u v : ℝ, Real.exp (a * u + b * v) ≤ a * Real.exp u + b * Real.exp v :=
      fun u v => by
        simpa [smul_eq_mul] using convexOn_exp.2 (Set.mem_univ u) (Set.mem_univ v) ha.le hb.le hab
    have hst : ∀ u v : ℝ, u ≠ v → Real.exp (a * u + b * v) < a * Real.exp u + b * Real.exp v :=
      fun u v huv => by
        simpa [smul_eq_mul] using
          strictConvexOn_exp.2 (Set.mem_univ u) (Set.mem_univ v) huv ha hb hab
    have hc0 : (a • x + b • y) 0 = a * x 0 + b * y 0 := by simp
    have hc1 : (a • x + b • y) 1 = a * x 1 + b * y 1 := by simp
    change a * c7f x + b * c7f y < c7f (a • x + b • y)
    have e0 : -(a * x 0 + b * y 0) = a * -x 0 + b * -y 0 := by ring
    have e1 : -(a * x 1 + b * y 1) = a * -x 1 + b * -y 1 := by ring
    have e2 : -(a * x 0 + b * y 0) - (a * x 1 + b * y 1) =
        a * (-x 0 - x 1) + b * (-y 0 - y 1) := by ring
    have hmid : c7f (a • x + b • y) = -(Real.exp (a * -x 0 + b * -y 0) +
        Real.exp (a * -x 1 + b * -y 1) + Real.exp (a * (-x 0 - x 1) + b * (-y 0 - y 1))) := by
      unfold c7f; rw [hc0, hc1, e2, e0, e1]
    rw [hmid]
    unfold c7f
    have : x 0 ≠ y 0 ∨ x 1 ≠ y 1 := by
      by_contra h
      push Not at h
      exact hxy (funext fun i => by fin_cases i <;> simp [h.1, h.2])
    rcases this with h | h
    · have := hst (-x 0) (-y 0) (by intro e; exact h (by linarith))
      have := hcv (-x 1) (-y 1)
      have := hcv (-x 0 - x 1) (-y 0 - y 1)
      nlinarith
    · have := hcv (-x 0) (-y 0)
      have := hst (-x 1) (-y 1) (by intro e; exact h (by linarith))
      have := hcv (-x 0 - x 1) (-y 0 - y 1)
      nlinarith

/-- The optimality conditions solved by `c7u`, `c7v`: for `r ≫ 0`, `u₁, u₂ > 0`,
`u₁ + u₁u₂ = r₁` and `u₂ + u₁u₂ = r₂`. -/
theorem c7_foc {r₀ r₁ : ℝ} (h₀ : 0 < r₀) (h₁ : 0 < r₁) :
    0 < c7u r₀ r₁ ∧ 0 < c7v r₀ r₁ ∧ c7u r₀ r₁ + c7u r₀ r₁ * c7v r₀ r₁ = r₀ ∧
      c7v r₀ r₁ + c7u r₀ r₁ * c7v r₀ r₁ = r₁ := by
  set S := Real.sqrt ((1 - r₀ + r₁) ^ 2 + 4 * r₀) with hS
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hS2 : S ^ 2 = (1 - r₀ + r₁) ^ 2 + 4 * r₀ := Real.sq_sqrt (by positivity)
  have hu : c7u r₀ r₁ = (r₀ - r₁ - 1 + S) / 2 := rfl
  have hv : c7v r₀ r₁ = (r₀ - r₁ - 1 + S) / 2 - (r₀ - r₁) := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hu]
    have : 1 - r₀ + r₁ < S := by
      rcases lt_or_ge (1 - r₀ + r₁) 0 with h | h
      · linarith
      · rw [hS, Real.lt_sqrt h]; linarith
    linarith
  · rw [hv]
    have : 1 + r₀ - r₁ < S := by
      rcases lt_or_ge (1 + r₀ - r₁) 0 with h | h
      · linarith
      · rw [hS, Real.lt_sqrt h]; nlinarith
    linarith
  · rw [hu, hv]; linear_combination hS2 / 4
  · rw [hu, hv]; linear_combination hS2 / 4

/-- **Exercise 5.C.7** (MWG, p. 161), the counterexample realized: for `f = c7f`, every `p > 0`
and `w ≫ 0`, the closed-form `c7demand p w` is the unique maximizer of `p f(z) - w·z` over
`z ∈ ℝ²` (hence the profit-maximizing input demand). -/
theorem exercise_5_C_7_demand {p : ℝ} (hp : 0 < p) {w : Fin 2 → ℝ} (hw : StrictlyPositive w)
    (z : Fin 2 → ℝ) :
    p * c7f z - w ⬝ᵥ z ≤ p * c7f (c7demand p w) - w ⬝ᵥ c7demand p w ∧
      (z ≠ c7demand p w → p * c7f z - w ⬝ᵥ z < p * c7f (c7demand p w) - w ⬝ᵥ c7demand p w) := by
  obtain ⟨hu, hv, hf0, hf1⟩ := c7_foc (div_pos (hw 0) hp) (div_pos (hw 1) hp)
  set u := c7u (w 0 / p) (w 1 / p)
  set v := c7v (w 0 / p) (w 1 / p)
  set zs := c7demand p w with hzs
  have hz0 : zs 0 = -Real.log u := rfl
  have hz1 : zs 1 = -Real.log v := rfl
  have heu : Real.exp (-zs 0) = u := by rw [hz0, neg_neg, Real.exp_log hu]
  have hev : Real.exp (-zs 1) = v := by rw [hz1, neg_neg, Real.exp_log hv]
  have heuv : Real.exp (-zs 0 - zs 1) = u * v := by
    rw [sub_eq_add_neg, Real.exp_add, heu, hev]
  have hw0 : w 0 = p * (u + u * v) := by rw [hf0]; field_simp
  have hw1 : w 1 = p * (v + u * v) := by rw [hf1]; field_simp
  -- tangent inequalities `e^x ≥ e^{x₀}(1 + x - x₀)`
  have tang : ∀ x x₀ : ℝ, Real.exp x₀ * (1 + (x - x₀)) ≤ Real.exp x := by
    intro x x₀
    have := Real.add_one_le_exp (x - x₀)
    have e : Real.exp x = Real.exp x₀ * Real.exp (x - x₀) := by
      rw [← Real.exp_add]; ring_nf
    rw [e]
    nlinarith [Real.exp_pos x₀]
  have tang' : ∀ x x₀ : ℝ, x ≠ x₀ → Real.exp x₀ * (1 + (x - x₀)) < Real.exp x := by
    intro x x₀ hne
    have := Real.add_one_lt_exp (sub_ne_zero.mpr hne)
    have e : Real.exp x = Real.exp x₀ * Real.exp (x - x₀) := by
      rw [← Real.exp_add]; ring_nf
    rw [e]
    nlinarith [Real.exp_pos x₀]
  have t0 := tang (-z 0) (-zs 0)
  have t1 := tang (-z 1) (-zs 1)
  have t2 := tang (-z 0 - z 1) (-zs 0 - zs 1)
  rw [heu] at t0
  rw [hev] at t1
  rw [heuv] at t2
  have hdot : ∀ x : Fin 2 → ℝ, w ⬝ᵥ x = w 0 * x 0 + w 1 * x 1 := fun x => by
    simp [dotProduct, Fin.sum_univ_two]
  simp only [c7f, hdot, heu, hev, heuv]
  rw [hw0, hw1]
  refine ⟨by nlinarith, fun hne => ?_⟩
  have : z 0 ≠ zs 0 ∨ z 1 ≠ zs 1 := by
    by_contra h
    push Not at h
    exact hne (funext fun i => by fin_cases i <;> simp [h.1, h.2])
  rcases this with h | h
  · have s0 := tang' (-z 0) (-zs 0) (by intro e; exact h (by linarith))
    rw [heu] at s0
    nlinarith
  · have s1 := tang' (-z 1) (-zs 1) (by intro e; exact h (by linarith))
    rw [hev] at s1
    nlinarith

/-- **Exercise 5.C.7** (MWG, p. 161) is false, with an explicit demand function: for
`f = c7f` (increasing, strictly concave, `∂²f/∂z₁∂z₂ < 0`, `c7f_technology`), at `p = 1` and
`w = (3/4, 3/4)` the profit-maximizing demand is `(ln 2, ln 2)`, and
`∂z₁/∂w₂ = 1/2 > 0`, contradicting `∂z_ℓ/∂w_k < 0`. -/
theorem exercise_5_C_7_explicit_counterexample :
    c7demand 1 ![3 / 4, 3 / 4] = ![Real.log 2, Real.log 2] ∧
      HasDerivAt (fun t => c7demand 1 ![3 / 4, t] 0) (1 / 2) (3 / 4) ∧ (0 : ℝ) < 1 / 2 := by
  have hsq : Real.sqrt ((1 - 3 / 4 + 3 / 4 : ℝ) ^ 2 + 4 * (3 / 4)) = 2 := by
    rw [show ((1 - 3 / 4 + 3 / 4 : ℝ) ^ 2 + 4 * (3 / 4)) = 2 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  have hu : c7u (3 / 4) (3 / 4) = 1 / 2 := by
    rw [c7u, hsq]; norm_num
  have hv : c7v (3 / 4) (3 / 4) = 1 / 2 := by
    rw [c7v, hu]; norm_num
  refine ⟨?_, ?_, by norm_num⟩
  · funext i
    fin_cases i
    · simp [c7demand, hu, Real.log_inv]
    · simp [c7demand, hv, Real.log_inv]
  · -- `t ↦ -ln((3/4 - t - 1 + √((1 - 3/4 + t)² + 3))/2)`
    have hg : HasDerivAt (fun t : ℝ => (1 - 3 / 4 + t) ^ 2 + 4 * (3 / 4)) 2 (3 / 4) := by
      have h := (((hasDerivAt_id (3 / 4 : ℝ)).const_add (1 - 3 / 4)).pow 2).add_const
        (4 * (3 / 4 : ℝ))
      convert h using 1 <;> norm_num [id]
    have hgpos : ((1 - 3 / 4 + 3 / 4 : ℝ) ^ 2 + 4 * (3 / 4)) ≠ 0 := by norm_num
    have hsqrt := hg.sqrt hgpos
    rw [hsq] at hsqrt
    have hu' : HasDerivAt (fun t : ℝ => c7u (3 / 4) t) (-1 / 4) (3 / 4) := by
      have h := ((((hasDerivAt_id (3 / 4 : ℝ)).const_sub (3 / 4 - 1)).add hsqrt).div_const 2)
      convert h using 1
      · funext t; simp only [c7u, id, Pi.add_apply]; ring
      · norm_num
    have hlog := hu'.log (by rw [hu]; norm_num)
    rw [hu] at hlog
    have h := hlog.neg
    convert h using 1
    · funext t
      simp [c7demand]
    · norm_num

end MWG.Production
