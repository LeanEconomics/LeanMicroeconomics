/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGMarketPower.Cournot
import Mathlib.Analysis.Convex.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# The representative-consumer model and monopolistic competition

MWG, Section 12.C, pp. 399-400, and footnotes 15-18.

The representative consumer has quasilinear utility `u(m, x₁, …, x_J) = G(∑_j f(x_j)) + m`, with
`G` and `f` concave. With the price of the numeraire normalized to `1` and wealth `w`, the
budget gives `m = w − ∑ p_j x_j`, so the consumer maximizes
`W(x) = G(∑_j f(x_j)) − ∑_j p_j x_j` (`repWelfare`, `repUtility_budget`).

* `eq_12_C_13`: at an interior optimum the first-order conditions (12.C.13)
  `G'(∑ f(x_j))f'(x_j) = p_j` hold.
* `eq_12_C_13_sufficient`: conversely, with `G` and `f` concave and `G' ≥ 0` at the point, a
  bundle satisfying (12.C.13) maximizes `W` over `x ≥ 0`; `eq_12_C_13_unique`: with `f` strictly
  concave and `G' > 0` it is the only maximizer, so (12.C.13) can be inverted to give demand
  functions. `eq_12_C_13_instance` verifies the hypotheses for `G(X) = X`, `f(x) = x − x²/2`.
* Monopolistic competition (p. 400): `monComp_demand`: with `ψ = f'⁻¹` and `G'(x̄) ≠ 0`, firm
  `j`'s first-order condition holds iff `x_j = ψ(p_j/G'(x̄))`; `monComp_index_update`: in the
  continuum model a single firm's quantity does not affect the index `x̄ = ∫₀¹ f(x_j) dj`, so no
  firm's choice affects any other firm's payoff (`monComp_no_interaction`; footnote 18's contrast
  is verbal). `IsMonCompEqm` is a symmetric equilibrium `x̄* = ∫₀¹ f(x_j(p*(x̄*), x̄*)) dj`;
  `monComp_example` exhibits one (`G = log`, `f(x) = 2√x`: `p* = 2c`, `x̄* = 1/√c`).

Departure: the sufficiency of (12.C.13) uses `G'(∑ f(x_j)) ≥ 0`, which MWG leaves implicit.
-/

namespace MWG.MarketPower

open Function MeasureTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The representative consumer's objective after substituting the budget constraint:
`G(∑_j f(x_j)) − ∑_j p_j x_j`. -/
noncomputable def repWelfare (G f : ℝ → ℝ) (p x : ι → ℝ) : ℝ :=
  G (∑ j, f (x j)) - ∑ j, p j * x j

omit [DecidableEq ι] in
/-- **The representative consumer** (MWG, p. 399). With `m = w − ∑ p_j x_j`,
`u(m, x) = G(∑ f(x_j)) + m = w + repWelfare`. -/
theorem repUtility_budget (G f : ℝ → ℝ) (p x : ι → ℝ) (w : ℝ) :
    G (∑ j, f (x j)) + (w - ∑ j, p j * x j) = w + repWelfare G f p x := by
  unfold repWelfare; ring

/-- The representative consumer's objective as a function of `x_j` alone. -/
theorem repWelfare_update (G f : ℝ → ℝ) (p x : ι → ℝ) (j : ι) (y : ℝ) :
    repWelfare G f p (update x j y) =
      G (f y + (∑ k, f (x k) - f (x j))) - (p j * y + (∑ k, p k * x k - p j * x j)) := by
  unfold repWelfare
  have h1 : ∑ k, f (update x j y k) = f y + (∑ k, f (x k) - f (x j)) := by
    simp_rw [apply_update (fun _ => f) x j y]
    exact sum_update_eq (fun k => f (x k)) j (f y)
  have h2 : ∑ k, p k * update x j y k = p j * y + (∑ k, p k * x k - p j * x j) := by
    have : ∀ k, p k * update x j y k = update (fun k => p k * x k) j (p j * y) k := by
      intro k
      by_cases hk : k = j
      · subst hk; simp
      · simp [update_of_ne hk]
    simp_rw [this]
    exact sum_update_eq (fun k => p k * x k) j (p j * y)
  rw [h1, h2]

omit [DecidableEq ι] in
/-- **Condition (12.C.13)** (MWG, p. 399). If `x` (with every `x_j > 0`) maximizes the
representative consumer's utility over positive bundles, and `G`, `f` are differentiable there,
then `G'(∑ f(x_j))f'(x_j) = p_j` for every `j`. -/
theorem eq_12_C_13 {G f f' : ℝ → ℝ} {G'S : ℝ} {p x : ι → ℝ} (hx : ∀ j, 0 < x j)
    (hG : HasDerivAt G G'S (∑ j, f (x j))) (hf : ∀ j, HasDerivAt f (f' (x j)) (x j))
    (hmax : ∀ y : ι → ℝ, (∀ j, 0 < y j) → repWelfare G f p y ≤ repWelfare G f p x) (j : ι) :
    G'S * f' (x j) = p j := by
  classical
  set g : ℝ → ℝ := fun y => repWelfare G f p (update x j y) with hg
  have hgx : g (x j) = repWelfare G f p x := by simp [hg]
  have hloc : IsLocalMax g (x j) := by
    filter_upwards [Ioi_mem_nhds (hx j)] with y hy
    rw [hgx]
    apply hmax
    intro k
    by_cases hk : k = j
    · rw [hk, update_self]; exact hy
    · rw [update_of_ne hk]; exact hx k
  have hd : HasDerivAt g (G'S * f' (x j) - p j) (x j) := by
    have e : g = fun y => G (f y + (∑ k, f (x k) - f (x j))) -
        (p j * y + (∑ k, p k * x k - p j * x j)) := by
      funext y; simp only [hg]; exact repWelfare_update G f p x j y
    rw [e]
    have hin : HasDerivAt (fun y => f y + (∑ k, f (x k) - f (x j))) (f' (x j)) (x j) :=
      (hf j).add_const _
    have hG' : HasDerivAt G G'S (f (x j) + (∑ k, f (x k) - f (x j))) := by
      rw [add_sub_cancel]; exact hG
    have h1 := hG'.comp (x j) hin
    have h2 : HasDerivAt (fun y => p j * y + (∑ k, p k * x k - p j * x j)) (p j) (x j) := by
      simpa using ((hasDerivAt_id (x j)).const_mul (p j)).add_const (∑ k, p k * x k - p j * x j)
    exact h1.sub h2
  have := hloc.hasDerivAt_eq_zero hd
  linarith

/-- The tangent-line inequality for a concave function: `f(y) ≤ f(x) + f'(x)(y − x)`. -/
theorem repTangent {f : ℝ → ℝ} {S : Set ℝ} {x y d : ℝ} (hf : ConcaveOn ℝ S f) (hx : x ∈ S)
    (hy : y ∈ S) (hd : HasDerivAt f d x) : f y ≤ f x + d * (y - x) := by
  rcases lt_trichotomy x y with h | h | h
  · have := hf.slope_le_of_hasDerivAt hx hy h hd
    rw [slope_def_field, div_le_iff₀ (by linarith)] at this
    linarith
  · rw [h]; simp
  · have := hf.le_slope_of_hasDerivAt hy hx h hd
    rw [slope_def_field, le_div_iff₀ (by linarith)] at this
    linarith

/-- The strict tangent-line inequality for a strictly concave function. -/
theorem repTangent_strict {f : ℝ → ℝ} {S : Set ℝ} {x y d : ℝ} (hf : StrictConcaveOn ℝ S f)
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y) (hd : HasDerivAt f d x) :
    f y < f x + d * (y - x) := by
  rcases lt_or_gt_of_ne hxy with h | h
  · have := hf.slope_lt_of_hasDerivAt hx hy h hd
    rw [slope_def_field, div_lt_iff₀ (by linarith)] at this
    linarith
  · have := hf.lt_slope_of_hasDerivAt hy hx h hd
    rw [slope_def_field, lt_div_iff₀ (by linarith)] at this
    linarith

omit [DecidableEq ι] in
/-- **Condition (12.C.13) is sufficient** (MWG, p. 399). If `f` is concave on `[0, ∞)`, `G` is
concave, both are differentiable at the bundle `x ≥ 0`, `G'(∑ f(x_j)) ≥ 0`, and (12.C.13) holds,
then `x` maximizes the representative consumer's utility over all bundles `y ≥ 0`. -/
theorem eq_12_C_13_sufficient {G f f' : ℝ → ℝ} {G'S : ℝ} {p x : ι → ℝ} (hx : ∀ j, 0 ≤ x j)
    (hfc : ConcaveOn ℝ (Set.Ici 0) f) (hGc : ConcaveOn ℝ Set.univ G)
    (hG : HasDerivAt G G'S (∑ j, f (x j))) (hf : ∀ j, HasDerivAt f (f' (x j)) (x j))
    (hG0 : 0 ≤ G'S) (hfoc : ∀ j, G'S * f' (x j) = p j) :
    ∀ y : ι → ℝ, (∀ j, 0 ≤ y j) → repWelfare G f p y ≤ repWelfare G f p x := by
  intro y hy
  unfold repWelfare
  have hT := repTangent hGc (Set.mem_univ _) (Set.mem_univ (∑ j, f (y j))) hG
  have hsum : ∑ j, f (y j) - ∑ j, f (x j) ≤ ∑ j, f' (x j) * (y j - x j) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum fun j _ => by
      have := repTangent hfc (hx j) (hy j) (hf j); linarith
  have hmul : G'S * (∑ j, f (y j) - ∑ j, f (x j)) ≤ ∑ j, p j * (y j - x j) := by
    calc G'S * (∑ j, f (y j) - ∑ j, f (x j)) ≤ G'S * ∑ j, f' (x j) * (y j - x j) :=
          mul_le_mul_of_nonneg_left hsum hG0
      _ = ∑ j, p j * (y j - x j) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by rw [← hfoc j]; ring
  have e : ∑ j, p j * (y j - x j) = ∑ j, p j * y j - ∑ j, p j * x j := by
    rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun j _ => by ring
  linarith

omit [DecidableEq ι] in
/-- **Inverting (12.C.13)** (MWG, p. 399). If moreover `f` is strictly concave on `[0, ∞)` and
`G'(∑ f(x_j)) > 0`, the bundle satisfying (12.C.13) is the unique maximizer over `y ≥ 0`: the
first-order conditions determine the demands `x_j(p₁, …, p_J)`. -/
theorem eq_12_C_13_unique {G f f' : ℝ → ℝ} {G'S : ℝ} {p x : ι → ℝ} (hx : ∀ j, 0 ≤ x j)
    (hfc : StrictConcaveOn ℝ (Set.Ici 0) f) (hGc : ConcaveOn ℝ Set.univ G)
    (hG : HasDerivAt G G'S (∑ j, f (x j))) (hf : ∀ j, HasDerivAt f (f' (x j)) (x j))
    (hG0 : 0 < G'S) (hfoc : ∀ j, G'S * f' (x j) = p j) :
    ∀ y : ι → ℝ, (∀ j, 0 ≤ y j) → y ≠ x → repWelfare G f p y < repWelfare G f p x := by
  intro y hy hne
  unfold repWelfare
  have hT := repTangent hGc (Set.mem_univ _) (Set.mem_univ (∑ j, f (y j))) hG
  obtain ⟨j0, hj0⟩ : ∃ j, y j ≠ x j := by
    by_contra h; push Not at h; exact hne (funext h)
  have hsum : ∑ j, f (y j) - ∑ j, f (x j) < ∑ j, f' (x j) * (y j - x j) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_lt_sum
    · intro j _
      have := repTangent hfc.concaveOn (hx j) (hy j) (hf j); linarith
    · refine ⟨j0, Finset.mem_univ _, ?_⟩
      have := repTangent_strict hfc (hx j0) (hy j0) (Ne.symm hj0) (hf j0); linarith
  have hmul : G'S * (∑ j, f (y j) - ∑ j, f (x j)) < ∑ j, p j * (y j - x j) := by
    calc G'S * (∑ j, f (y j) - ∑ j, f (x j)) < G'S * ∑ j, f' (x j) * (y j - x j) :=
          mul_lt_mul_of_pos_left hsum hG0
      _ = ∑ j, p j * (y j - x j) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by rw [← hfoc j]; ring
  have e : ∑ j, p j * (y j - x j) = ∑ j, p j * y j - ∑ j, p j * x j := by
    rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun j _ => by ring
  linarith

/-- The hypotheses of `eq_12_C_13_unique` are satisfiable: `G(X) = X`, `f(x) = x − x²/2`
(`f'(x) = 1 − x`), prices `(1/2, 1/4)`, demands `x_j = 1 − p_j = (1/2, 3/4)`. -/
theorem eq_12_C_13_instance :
    StrictConcaveOn ℝ (Set.Ici 0) (fun x : ℝ => x - x ^ 2 / 2) ∧
    ConcaveOn ℝ Set.univ (fun X : ℝ => X) ∧
    (∀ z : ℝ, HasDerivAt (fun x : ℝ => x - x ^ 2 / 2) (1 - z) z) ∧
    (∀ S : ℝ, HasDerivAt (fun X : ℝ => X) 1 S) ∧
    ∀ j : Fin 2, (1 : ℝ) * (1 - ![1 / 2, 3 / 4] j) = ![1 / 2, 1 / 4] j := by
  refine ⟨⟨convex_Ici 0, fun a _ b _ hab u v hu hv huv => ?_⟩, concaveOn_id convex_univ,
    fun z => ?_, fun S => hasDerivAt_id S, fun j => by fin_cases j <;> norm_num⟩
  · simp only [smul_eq_mul]
    obtain rfl : v = 1 - u := by linarith
    have : 0 < (a - b) ^ 2 := by have : a - b ≠ 0 := sub_ne_zero.2 hab; positivity
    nlinarith [mul_pos hu hv]
  · have h : HasDerivAt (fun x : ℝ => x - x ^ 2 / 2) (1 - ((2 : ℕ) : ℝ) * z ^ (2 - 1) / 2) z :=
      (hasDerivAt_id' z).sub ((hasDerivAt_pow 2 z).div_const 2)
    convert h using 1
    norm_num

/-! ### Monopolistic competition (p. 400) -/

/-- **Monopolistic competition: demand** (MWG, p. 400). If `ψ` inverts `f'` (`ψ(f'(y)) = y` and
`f'(ψ(r)) = r` at `r = p/G'(x̄)`) and `G'(x̄) ≠ 0`, the consumer's first-order condition
`G'(x̄)f'(x_j) = p_j` holds iff `x_j = ψ(p_j/G'(x̄))`. -/
theorem monComp_demand {f' ψ : ℝ → ℝ} {Gx p y : ℝ} (hG : Gx ≠ 0) (hleft : ψ (f' y) = y)
    (hright : f' (ψ (p / Gx)) = p / Gx) : Gx * f' y = p ↔ y = ψ (p / Gx) := by
  constructor
  · intro h
    rw [← hleft, show f' y = p / Gx by rw [← h]; field_simp]
  · intro h
    rw [h, hright]; field_simp

/-- **Monopolistic competition: the index** (MWG, p. 400). In the continuum model a single firm
`j₀` changing its quantity does not change the index of aggregate output `x̄ = ∫₀¹ f(x_j) dj`. -/
theorem monComp_index_update (f : ℝ → ℝ) (x : ℝ → ℝ) (j0 y : ℝ) :
    ∫ j in (0 : ℝ)..1, f (update x j0 y j) = ∫ j in (0 : ℝ)..1, f (x j) := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards [Measure.ae_ne volume j0] with j hj _
  rw [update_of_ne hj]

/-- **Monopolistic competition: no strategic interaction** (MWG, p. 400). If firm `k`'s payoff
depends only on its own quantity and the index, `Φ(x_k, ∫₀¹ f(x_j) dj)`, then a change in the
quantity of any other firm `j₀ ≠ k` leaves firm `k`'s payoff unchanged. -/
theorem monComp_no_interaction (f : ℝ → ℝ) (Φ : ℝ → ℝ → ℝ) (x : ℝ → ℝ) {j0 k : ℝ} (hk : k ≠ j0)
    (y : ℝ) :
    Φ (update x j0 y k) (∫ j in (0 : ℝ)..1, f (update x j0 y j)) =
      Φ (x k) (∫ j in (0 : ℝ)..1, f (x j)) := by
  rw [monComp_index_update, update_of_ne hk]

/-- A symmetric equilibrium of the monopolistic competition model (MWG, p. 400): every firm
charges `p* > 0`, which maximizes `(p − c)ψ(p/G'(x̄*))` over `p > 0` given the index, and the index
is `x̄* = ∫₀¹ f(x_j(p*, x̄*)) dj` with `x_j(p, x̄) = ψ(p/G'(x̄))`. -/
def IsMonCompEqm (f G' ψ : ℝ → ℝ) (c X ps : ℝ) : Prop :=
  0 < ps ∧ (∀ p, 0 < p → (p - c) * ψ (p / G' X) ≤ (ps - c) * ψ (ps / G' X)) ∧
    X = ∫ _j in (0 : ℝ)..1, f (ψ (ps / G' X))

/-- **Monopolistic competition: an example** (MWG, p. 400). With `G(X) = log X` (`G'(X) = 1/X`),
`f(x) = 2√x` (`f'(x) = 1/√x`, inverted by `ψ(r) = 1/r²`) and cost `c > 0`, the price `p* = 2c` and
index `x̄* = 1/√c` form a symmetric equilibrium. -/
theorem monComp_example {c : ℝ} (hc : 0 < c) :
    (∀ x : ℝ, 0 < x → HasDerivAt (fun x => 2 * √x) (1 / √x) x) ∧
    (∀ x : ℝ, 0 < x → (fun r : ℝ => 1 / r ^ 2) (1 / √x) = x) ∧
    IsMonCompEqm (fun x => 2 * √x) (fun X => 1 / X) (fun r => 1 / r ^ 2) c (1 / √c) (2 * c) := by
  have hsc : 0 < √c := Real.sqrt_pos.2 hc
  have hcc : √c * √c = c := Real.mul_self_sqrt hc.le
  refine ⟨fun x hx => ?_, fun x hx => ?_, by linarith, fun p hp => ?_, ?_⟩
  · have := (Real.hasDerivAt_sqrt hx.ne').const_mul 2
    convert this using 1
    have : 0 < √x := Real.sqrt_pos.2 hx
    field_simp
  · have : √x ^ 2 = x := Real.sq_sqrt hx.le
    simp only [one_div, inv_pow, inv_inv, this]
  · have e1 : 1 / (p / (1 / (1 / √c))) ^ 2 = c / p ^ 2 := by
      rw [one_div_one_div, div_pow, Real.sq_sqrt hc.le]; field_simp
    have e2 : 1 / (2 * c / (1 / (1 / √c))) ^ 2 = 1 / (4 * c) := by
      rw [one_div_one_div, div_pow, Real.sq_sqrt hc.le]; field_simp; ring
    beta_reduce
    rw [e1, e2]
    rw [show (p - c) * (c / p ^ 2) = c * (p - c) / p ^ 2 by ring,
      show (2 * c - c) * (1 / (4 * c)) = 1 / 4 by field_simp; ring,
      div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg (p - 2 * c)]
  · rw [intervalIntegral.integral_const, sub_zero, one_smul]
    have e : 1 / (2 * c / (1 / (1 / √c))) ^ 2 = (1 / (2 * √c)) ^ 2 := by
      have r : (1 / (2 * √c)) ^ 2 = 1 / (4 * c) := by
        rw [div_pow, mul_pow, Real.sq_sqrt hc.le]; ring
      rw [r, one_div_one_div, div_pow, Real.sq_sqrt hc.le]; field_simp; ring
    beta_reduce
    rw [e, Real.sqrt_sq (by positivity)]
    field_simp

end MWG.MarketPower
