/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGClassicalDemand.RelationsExercises

/-!
# Section 3.G exercises left open: 3.G.6(c)(e), 3.G.9, 3.G.10, 3.G.12, 3.G.18

MWG, Exercises 3.G.6, 3.G.9, 3.G.10, 3.G.12 and 3.G.18, pp. 100-102.

* **3.G.18** (chains of substitutes): for any negative semidefinite `S` with `S p = 0`,
  `p ≫ 0`, every nonempty proper set of goods has a good inside with a weak substitute outside
  (`closer_substitute_across`); hence any two goods are linked by a chain of weak substitutes
  (`closer_substitute_chain`), and so for the Hicksian derivative matrix of Proposition 3.G.2
  (`exercise_3_G_18`). The proof is the book's hint: a block of goods all of whose outside
  cross-effects are negative would make `p_A' S_AA p_A > 0`.
* **3.G.10**: for `v(p, w) = a(p) + b(p) w`, homogeneity of degree zero holds iff `a` is
  homogeneous of degree `0` and `b` of degree `-1`; `v` is strictly increasing in `w` iff
  `b > 0`; `v` is nonincreasing in `p` iff `a` and `b` are; continuity of `v` gives continuity
  of `a` and `b` (`exercise_3_G_10_*`).
* **3.G.12**: in Gorman form, demand is homothetic (`x(p, w) = w x(p, 1)`) iff `∇a(p) = 0`, and
  the demand for good `l` is independent of wealth iff `∂b/∂p_l = 0` (the quasilinear case for
  goods `l ≠ 1`, `p₁ = 1`) (`exercise_3_G_12_*`).
* **3.G.9**: the Slutsky matrix from the indirect utility function: with
  `x_l = -v_{p_l}/v_w` (Roy's identity),
  `s_lk = [-v_{p_l p_k} v_w² + v_{p_l} v_{w p_k} v_w + v_{p_l w} v_{p_k} v_w`
  `- v_{p_l} v_{p_k} v_{ww}] / v_w³` (`exercise_3_G_9`).
* **3.G.6(c)** (Fisher): Slutsky symmetry `s₁₂ = s₂₁` at all `(p, w)` holds iff `α = 100` and
  `β = γ = -5`; **(e)** then `x₁ ≡ x₂`: goods 1 and 2 are always consumed in equal amounts
  (perfect complements).
-/

namespace MWG.ClassicalDemand

open MWG.ConsumerChoice Kreps.PreferenceProperties Filter Topology

variable {L : ℕ}

/-- **Exercise 3.G.18** (MWG, p. 102), the key step. Let `S` be negative semidefinite with
`S p = 0` for some `p ≫ 0`. Then for every set `A` of goods that is nonempty and misses some
good, there are `l ∈ A` and `k ∉ A` with `s_lk ≥ 0`. -/
theorem closer_substitute_across {S : Matrix (Fin L) (Fin L) ℝ} (hS : NegSemidef S)
    {p : Fin L → ℝ} (hp : StrictlyPositive p) (hSp : S.mulVec p = 0) (A : Finset (Fin L))
    (hA : A.Nonempty) (hAc : ∃ k, k ∉ A) : ∃ l ∈ A, ∃ k ∉ A, 0 ≤ S l k := by
  by_contra hcon
  push Not at hcon
  set z : Fin L → ℝ := fun l => if l ∈ A then p l else 0 with hz
  have hcomp : (Aᶜ).Nonempty := by
    obtain ⟨k, hk⟩ := hAc
    exact ⟨k, Finset.mem_compl.2 hk⟩
  have hrow : ∀ l ∈ A, 0 < S.mulVec z l := by
    intro l hl
    have h0 : ∑ k, S l k * p k = 0 := by
      have := congrFun hSp l
      simpa [Matrix.mulVec, dotProduct] using this
    rw [← Finset.sum_add_sum_compl A] at h0
    have hneg : ∑ k ∈ Aᶜ, S l k * p k < 0 :=
      Finset.sum_neg (fun k hk => mul_neg_of_neg_of_pos
        (hcon l hl k (Finset.mem_compl.1 hk)) (hp k)) hcomp
    have : S.mulVec z l = ∑ k ∈ A, S l k * p k := by
      simp only [Matrix.mulVec, dotProduct, hz, mul_ite, mul_zero]
      rw [Finset.sum_ite_mem, Finset.univ_inter]
    rw [this]
    linarith
  have hpos : 0 < z ⬝ᵥ S.mulVec z := by
    simp only [dotProduct, hz, ite_mul, zero_mul]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
    exact Finset.sum_pos (fun l hl => mul_pos (hp l) (hrow l hl)) hA
  exact absurd (hS z) (not_le.2 hpos)

/-- **Exercise 3.G.18** (MWG, p. 102). If `S` is negative semidefinite with `S p = 0`, `p ≫ 0`,
then every good is related to every other good by a chain of weak substitutes: the relation
`s_lk ≥ 0` connects any `l` to any `k` in finitely many steps. -/
theorem closer_substitute_chain {S : Matrix (Fin L) (Fin L) ℝ} (hS : NegSemidef S)
    {p : Fin L → ℝ} (hp : StrictlyPositive p) (hSp : S.mulVec p = 0) (l k : Fin L) :
    Relation.ReflTransGen (fun i j => 0 ≤ S i j) l k := by
  classical
  set A := Finset.univ.filter fun j => Relation.ReflTransGen (fun i j => 0 ≤ S i j) l j
  by_contra hk
  have hkA : k ∉ A := by simp [A, hk]
  have hlA : l ∈ A := by simp [A, Relation.ReflTransGen.refl]
  obtain ⟨i, hi, j, hj, hij⟩ := closer_substitute_across hS hp hSp A ⟨l, hlA⟩ ⟨k, hkA⟩
  have hi' : Relation.ReflTransGen (fun i j => 0 ≤ S i j) l i := by simpa [A] using hi
  exact hj (by simpa [A] using hi'.tail hij)

/-- **Exercise 3.G.18** (MWG, p. 102), for Hicksian demand. Under the hypotheses of Proposition
3.G.2 (`u` continuous and strictly quasiconcave, `hf` a Hicksian demand function differentiable
at `p̄ ≫ 0`), any goods `l`, `k` are linked by a chain `l = r₀, r₁, …, r_n = k` with
`∂h_{r_i}/∂p_{r_{i+1}} ≥ 0`. -/
theorem exercise_3_G_18 {u : (Fin L → ℝ) → ℝ} (hu : ContinuousOn u (nonnegOrthant L))
    (hq : StrictlyQuasiconcaveOn (nonnegOrthant L) u) {ub : ℝ}
    {hf : (Fin L → ℝ) → (Fin L → ℝ)} (hhf : ∀ q, StrictlyPositive q → hf q ∈ hicksianDemand u q ub)
    {p : Fin L → ℝ} (hp : StrictlyPositive p) {D : (Fin L → ℝ) →L[ℝ] (Fin L → ℝ)}
    (hD : HasFDerivAt hf D p) (l k : Fin L) :
    Relation.ReflTransGen (fun i j => 0 ≤ jacobian D i j) l k := by
  have hnsd := proposition_3_G_2_ii u hhf hp hD
  have hDp := proposition_3_G_2_iv hu hq hhf hp hD
  exact closer_substitute_chain hnsd hp (by rw [jacobian_mulVec, hDp]) l k

/-- **Exercise 3.G.10** (MWG, p. 100), homogeneity. `v(p, w) = a(p) + b(p) w` is homogeneous of
degree zero in `(p, w)` for `p ≫ 0` iff `a` is homogeneous of degree zero and `b` of degree
`-1`. -/
theorem exercise_3_G_10_homogeneous (a b : (Fin L → ℝ) → ℝ) :
    (∀ p, StrictlyPositive p → ∀ w t : ℝ, 0 < t →
        a (t • p) + b (t • p) * (t * w) = a p + b p * w) ↔
      ∀ p, StrictlyPositive p → ∀ t : ℝ, 0 < t → a (t • p) = a p ∧ b (t • p) = b p / t := by
  constructor
  · intro h p hp t ht
    have h0 := h p hp 0 t ht
    have h1 := h p hp 1 t ht
    simp only [mul_zero, add_zero, mul_one] at h0 h1
    refine ⟨h0, ?_⟩
    rw [eq_div_iff ht.ne']
    linarith
  · intro h p hp w t ht
    obtain ⟨h1, h2⟩ := h p hp t ht
    rw [h1, h2]
    field_simp

/-- **Exercise 3.G.10** (MWG, p. 100), monotonicity in wealth. `a(p) + b(p) w` is strictly
increasing in `w` iff `b(p) > 0`. -/
theorem exercise_3_G_10_wealth (a b : (Fin L → ℝ) → ℝ) (p : Fin L → ℝ) :
    (∀ w w' : ℝ, w < w' → a p + b p * w < a p + b p * w') ↔ 0 < b p := by
  constructor
  · intro h
    have := h 0 1 one_pos
    linarith
  · intro hb w w' hww
    nlinarith

/-- **Exercise 3.G.10** (MWG, p. 100), monotonicity in prices. For `p ≤ p'`,
`a(p') + b(p') w ≤ a(p) + b(p) w` for every `w > 0` iff `a(p') ≤ a(p)` and `b(p') ≤ b(p)`. -/
theorem exercise_3_G_10_prices (a b : (Fin L → ℝ) → ℝ) (p p' : Fin L → ℝ) :
    (∀ w : ℝ, 0 < w → a p' + b p' * w ≤ a p + b p * w) ↔ a p' ≤ a p ∧ b p' ≤ b p := by
  constructor
  · intro h
    constructor
    · -- let `w → 0⁺`
      by_contra hcon
      push Not at hcon
      set ε := a p' - a p with hε
      have hε0 : 0 < ε := by linarith
      set w := ε / (2 * (|b p - b p'| + 1)) with hw
      have hw0 : 0 < w := by positivity
      have h1 := h w hw0
      have h2 : (b p - b p') * w ≤ |b p - b p'| * w :=
        mul_le_mul_of_nonneg_right (le_abs_self _) hw0.le
      have h3 : |b p - b p'| * w < ε := by
        rw [hw]
        have : 0 < |b p - b p'| + 1 := by positivity
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith [abs_nonneg (b p - b p')]
      nlinarith
    · by_contra hcon
      push Not at hcon
      have hpos : 0 < b p' - b p := by linarith
      set w := (|a p' - a p| + 1) / (b p' - b p) with hw
      have hw0 : 0 < w := by positivity
      have h1 := h w hw0
      have : (b p' - b p) * w = |a p' - a p| + 1 := by rw [hw]; field_simp
      have h3 : b p' * w - b p * w = |a p' - a p| + 1 := by rw [← sub_mul]; exact this
      linarith [neg_le_abs (a p' - a p)]
  · rintro ⟨ha, hb⟩ w hw
    nlinarith

/-- **Exercise 3.G.10** (MWG, p. 100), continuity. If `v(p, w) = a(p) + b(p) w` is continuous in
`p` at `w = 1` and `w = 2`, then `a` and `b` are continuous:
`b = v(·, 2) - v(·, 1)`, `a = 2 v(·, 1) - v(·, 2)`. -/
theorem exercise_3_G_10_continuous {a b : (Fin L → ℝ) → ℝ} {s : Set (Fin L → ℝ)}
    (hv : ∀ w : ℝ, 0 < w → ContinuousOn (fun p => a p + b p * w) s) :
    ContinuousOn a s ∧ ContinuousOn b s := by
  have h1 := hv 1 one_pos
  have h2 := hv 2 two_pos
  refine ⟨(((h1.const_smul (2 : ℝ)).sub h2).congr fun p _ => ?_),
    ((h2.sub h1).congr fun p _ => ?_)⟩
  · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · simp only [Pi.sub_apply]
    ring

/-- **Exercise 3.G.12** (MWG, p. 101), homothetic case. With Gorman-form demand
`x(p, w) = -(∇a(p) + w ∇b(p))/b(p)` (Exercise 3.G.11), demand is homothetic,
`x(p, w) = w x(p, 1)` for all `w > 0`, iff `∇a(p) = 0` (`a` locally constant: `v = a + b(p) w`
with `a` constant, an increasing transformation of `b(p) w`). -/
theorem exercise_3_G_12_homothetic {ga gb : Fin L → ℝ} {bp : ℝ} (hb : bp ≠ 0) :
    (∀ w : ℝ, 0 < w → -(1 / bp) • (ga + w • gb) = w • (-(1 / bp) • (ga + (1 : ℝ) • gb))) ↔
      ga = 0 := by
  constructor
  · intro h
    have h2 := h 2 two_pos
    funext l
    have := congrFun h2 l
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, one_mul] at this
    field_simp at this
    simp only [Pi.zero_apply]
    linarith
  · rintro rfl w _
    funext l
    simp only [Pi.smul_apply, smul_eq_mul, zero_add, one_mul]
    ring

/-- **Exercise 3.G.12** (MWG, p. 101), quasilinear case. With Gorman-form demand
`x(p, w) = -(∇a(p) + w ∇b(p))/b(p)`, the demand for good `l` does not depend on `w` iff
`∂b/∂p_l = 0`: for preferences quasilinear in good 1 (`p₁ = 1`), `∇b = 0` in the prices of
goods `2, …, L`, i.e. `b` is a constant and `v(p, w) = a(p) + b w`. -/
theorem exercise_3_G_12_quasilinear {ga gb : Fin L → ℝ} {bp : ℝ} (hb : bp ≠ 0) (l : Fin L) :
    (∀ w w' : ℝ, (-(1 / bp) • (ga + w • gb)) l = (-(1 / bp) • (ga + w' • gb)) l) ↔
      gb l = 0 := by
  constructor
  · intro h
    have := h 0 1
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, zero_mul, add_zero, one_mul] at this
    field_simp at this
    linarith
  · intro h w w'
    simp [h]

/-- **Exercise 3.G.9** (MWG, p. 100), the quotient-rule step: if `x = -f/g` with `f`, `g`
differentiable at `t` and `g(t) ≠ 0`, then `x' = -(f' g - f g')/g²`. -/
theorem closer_neg_div_hasDerivAt {f g : ℝ → ℝ} {f' g' t : ℝ} (hf : HasDerivAt f f' t)
    (hg : HasDerivAt g g' t) (hg0 : g t ≠ 0) :
    HasDerivAt (fun s => -(f s / g s)) (-((f' * g t - f t * g') / g t ^ 2)) t :=
  (hf.div hg hg0).neg

/-- **Exercise 3.G.9** (MWG, p. 100). The Slutsky matrix from the indirect utility function.
Let `x_l(p, w) = -v_{p_l}(p, w)/v_w(p, w)` (Roy's identity), and suppose that along `p_k` the
functions `v_{p_l}`, `v_w` have derivatives `v_lk`, `v_wk`, and along `w` they have derivatives
`v_lw`, `v_ww`; write `x_k = -v_k/v_w`. Then `∂x_l/∂p_k` and `∂x_l/∂w` are as computed, and
`s_lk = ∂x_l/∂p_k + (∂x_l/∂w) x_k
= (-v_lk v_w² + v_l v_wk v_w + v_lw v_k v_w - v_l v_k v_ww)/v_w³`. -/
theorem exercise_3_G_9 {Vl Vw : ℝ → ℝ} {Wl Ww : ℝ → ℝ} {pk w : ℝ} {vlk vwk vlw vww vk : ℝ}
    (hVl : HasDerivAt Vl vlk pk) (hVw : HasDerivAt Vw vwk pk)
    (hWl : HasDerivAt Wl vlw w) (hWw : HasDerivAt Ww vww w)
    (hl : Vl pk = Wl w) (hw : Vw pk = Ww w) (hw0 : Ww w ≠ 0) :
    HasDerivAt (fun s => -(Vl s / Vw s)) (-((vlk * Vw pk - Vl pk * vwk) / Vw pk ^ 2)) pk ∧
      HasDerivAt (fun s => -(Wl s / Ww s)) (-((vlw * Ww w - Wl w * vww) / Ww w ^ 2)) w ∧
      -((vlk * Vw pk - Vl pk * vwk) / Vw pk ^ 2) +
          -((vlw * Ww w - Wl w * vww) / Ww w ^ 2) * (-(vk / Ww w)) =
        (-vlk * Ww w ^ 2 + Wl w * vwk * Ww w + vlw * vk * Ww w - Wl w * vk * vww) /
          Ww w ^ 3 := by
  refine ⟨closer_neg_div_hasDerivAt hVl hVw (hw ▸ hw0), closer_neg_div_hasDerivAt hWl hWw hw0,
    ?_⟩
  rw [hl, hw]
  field_simp
  ring

/-- **Exercise 3.G.6(c)** (MWG, p. 100), the Slutsky terms of Fisher's demand system: along
`p₂`, `∂x₁/∂p₂ = β/p₃`; along `p₁`, `∂x₂/∂p₁ = β/p₃`; along `w`, `∂x₁/∂w = ∂x₂/∂w = δ/p₃`. -/
theorem exercise_3_G_6c_derivatives (α β γ δ : ℝ) {p : Fin 3 → ℝ} (hp : p 2 ≠ 0) (w : ℝ) :
    HasDerivAt (fun t => exercise_3_G_6_x1 β δ (Function.update p 1 t) w) (β / p 2) (p 1) ∧
      HasDerivAt (fun t => exercise_3_G_6_x2 α β γ δ (Function.update p 0 t) w) (β / p 2)
        (p 0) ∧
      HasDerivAt (fun w => exercise_3_G_6_x1 β δ p w) (δ / p 2) w ∧
      HasDerivAt (fun w => exercise_3_G_6_x2 α β γ δ p w) (δ / p 2) w := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := (((hasDerivAt_id (p 1)).div_const (p 2)).const_mul β).const_add
      (100 - 5 * (p 0 / p 2)) |>.add_const (δ * (w / p 2))
    refine h.congr_deriv (by field_simp) |>.congr_of_eventuallyEq ?_
    filter_upwards with t
    simp [exercise_3_G_6_x1]
  · have h := (((hasDerivAt_id (p 0)).div_const (p 2)).const_mul β).const_add α
      |>.add_const (γ * (p 1 / p 2) + δ * (w / p 2))
    refine h.congr_deriv (by field_simp) |>.congr_of_eventuallyEq ?_
    filter_upwards with t
    simp [exercise_3_G_6_x2]
    ring
  · have h := (((hasDerivAt_id w).div_const (p 2)).const_mul δ).const_add
      (100 - 5 * (p 0 / p 2) + β * (p 1 / p 2))
    exact h.congr_deriv (by field_simp)
  · have h := (((hasDerivAt_id w).div_const (p 2)).const_mul δ).const_add
      (α + β * (p 0 / p 2) + γ * (p 1 / p 2))
    exact h.congr_deriv (by field_simp)

/-- **Exercise 3.G.6(c)** (MWG, p. 100). With `δ ≠ 0`, the Slutsky symmetry condition
`s₁₂ = ∂x₁/∂p₂ + (∂x₁/∂w) x₂ = ∂x₂/∂p₁ + (∂x₂/∂w) x₁ = s₂₁`, required by utility maximization
(Proposition 3.G.2), holds at every `(p, w)` with `p ≫ 0`, `w > 0` iff `α = 100` and
`β = γ = -5`. -/
theorem exercise_3_G_6c (α β γ δ : ℝ) (hδ : δ ≠ 0) :
    (∀ p : Fin 3 → ℝ, StrictlyPositive p → ∀ w : ℝ, 0 < w →
        β / p 2 + δ / p 2 * exercise_3_G_6_x2 α β γ δ p w =
          β / p 2 + δ / p 2 * exercise_3_G_6_x1 β δ p w) ↔
      α = 100 ∧ β = -5 ∧ γ = -5 := by
  constructor
  · intro h
    have key : ∀ p : Fin 3 → ℝ, StrictlyPositive p → ∀ w : ℝ, 0 < w →
        exercise_3_G_6_x2 α β γ δ p w = exercise_3_G_6_x1 β δ p w := by
      intro p hp w hw
      have := h p hp w hw
      have hp2 := (hp 2).ne'
      have : δ / p 2 * exercise_3_G_6_x2 α β γ δ p w = δ / p 2 * exercise_3_G_6_x1 β δ p w := by
        linarith
      exact mul_left_cancel₀ (div_ne_zero hδ hp2) this
    have e1 := key ![1, 1, 1] (fun l => by fin_cases l <;> simp) 1 one_pos
    have e2 := key ![2, 1, 1] (fun l => by fin_cases l <;> simp) 1 one_pos
    have e3 := key ![1, 2, 1] (fun l => by fin_cases l <;> simp) 1 one_pos
    simp [exercise_3_G_6_x1, exercise_3_G_6_x2] at e1 e2 e3
    refine ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨rfl, rfl, rfl⟩ p _ w _
    simp only [exercise_3_G_6_x1, exercise_3_G_6_x2]
    ring

/-- **Exercise 3.G.6(e)** (MWG, p. 100). Under the restrictions of (c) the consumer always buys
equal amounts of goods 1 and 2: `x₁(p, w) = x₂(p, w)` for all `(p, w)`, so in the
`(x₁, x₂)` plane the goods are perfect complements and `u` has the form
`u(x) = U(min {x₁, x₂}, x₃)` on the demanded bundles (the indifference curves of (d) are
right angles on the diagonal). -/
theorem exercise_3_G_6e (δ : ℝ) (p : Fin 3 → ℝ) (w : ℝ) :
    exercise_3_G_6_x1 (-5) δ p w = exercise_3_G_6_x2 100 (-5) (-5) δ p w := by
  simp only [exercise_3_G_6_x1, exercise_3_G_6_x2]
  ring

end MWG.ClassicalDemand
