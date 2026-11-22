/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGWelfareBargaining.Shapley
import Mathlib.Analysis.Calculus.LagrangeMultipliers
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.Deriv

/-!
# The regulated firm and cost allocation

MWG, Exercises 22.F.6 and 22.F.7 (p. 856), and the cost-allocation discussion of pp. 848-849.

* `exercise_22_F_6a_loss`: with strictly concave costs marginal-cost pricing does not cover
  costs; `exercise_22_F_6a_ac`: average-cost pricing `p(q) = c(q)/q = S'(q)` is not first best.
* `exercise_22_F_6b`: the second-best problem (break-even constraint `S'(q)q ≥ c(q)`) for
  `S(q) = 2q - q²/2`, `c(q) = q - q²/8 + 1/8`: the solution is `q = 1`, the largest output
  with `S'(q) = c(q)/q`, below the first best `q = 4/3`.
* `shapley_typeGame`: the Shapley value of the cost game `v(S) = C(|S ∩ T|)` gives each project
  in `T` the average cost `C(|T|)/|T|` and every other project `0`.
  `exercise_22_F_6c`: with `v(S) = c(|S|)` each unit of output is charged the average cost;
  `exercise_22_F_7b`: with separable costs each project is charged the average cost of its
  type (exactly; the approximation of the hint is not needed).
* `separable_kkt` (Mathlib's Lagrange multiplier theorem plus a sign argument) and
  `exercise_22_F_7a`: Boiteux's first-order conditions
  `(pₗ - c'ₗ)/pₗ = (μ/(1+μ))(-P'ₗqₗ/pₗ)`, a Ramsey formula; `exercise_22_F_7a_instance`.
* `exercise_22_F_7c`: type-by-type average-cost prices (the Shapley unit costs) are in general
  neither first best nor second best: an explicit two-type example.
-/

namespace MWG.WelfareBargaining


/-! ### Exercise 22.F.6 -/

/-- **Exercise 22.F.6(a)** (MWG, p. 856). If `c` is strictly concave on `[0, ∞)` with
`c(0) ≥ 0`, then at any `q > 0` the marginal-cost revenue `c'(q)q` falls short of `c(q)`. -/
theorem exercise_22_F_6a_loss {c : ℝ → ℝ} {m q : ℝ} (hc : StrictConcaveOn ℝ (Set.Ici 0) c)
    (hq : 0 < q) (hd : HasDerivAt c m q) (h0 : 0 ≤ c 0) : m * q < c q := by
  have := hc.lt_slope_of_hasDerivAt (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hq.le) hq hd
  rw [slope_def_field, sub_zero, lt_div_iff₀ hq] at this
  linarith

/-- **Exercise 22.F.6(a)** (MWG, p. 856). If the price is set at average cost,
`S'(q) = c(q)/q`, and marginal cost is below average cost, the output `q` is not first best:
the total surplus `S - c` has derivative `S'(q) - c'(q) > 0` there. -/
theorem exercise_22_F_6a_ac {S c : ℝ → ℝ} {p m q : ℝ} (hq : 0 < q) (hS : HasDerivAt S p q)
    (hc : HasDerivAt c m q) (hac : p = c q / q) (hmc : m * q < c q) :
    ¬IsLocalMax (fun x => S x - c x) q := by
  intro hmax
  have := hmax.hasDerivAt_eq_zero (hS.sub hc)
  rw [hac] at this
  have : m = c q / q := by linarith
  rw [this, div_mul_cancel₀ _ hq.ne'] at hmc
  exact lt_irrefl _ hmc

/-- The cost function of the example: `c(q) = q - q²/8 + 1/8`. -/
noncomputable def costEx (q : ℝ) : ℝ := q - q ^ 2 / 8 + 1 / 8

/-- **Exercise 22.F.6(a)**, instance (MWG, p. 856): `c(q) = q - q²/8 + 1/8` is strictly concave
with `c(0) > 0`; with `S(q) = 2q - q²/2`, at `q = 1` the price `S'(1) = 1` equals average cost
`c(1)/1 = 1` while marginal cost is `3/4`. -/
theorem exercise_22_F_6a_instance :
    StrictConcaveOn ℝ (Set.Ici 0) costEx ∧ 0 ≤ costEx 0 ∧
      HasDerivAt (fun q : ℝ => 2 * q - q ^ 2 / 2) 1 1 ∧ HasDerivAt costEx (3 / 4) 1 ∧
      (1 : ℝ) = costEx 1 / 1 := by
  refine ⟨⟨convex_Ici 0, fun x _ y _ hxy a b ha hb hab => ?_⟩, by norm_num [costEx], ?_, ?_,
    by norm_num [costEx]⟩
  · simp only [costEx, smul_eq_mul]
    have hb' : b = 1 - a := by linarith
    subst hb'
    have : 0 < (x - y) ^ 2 := by positivity
    nlinarith [mul_pos (mul_pos ha hb) this]
  · have := ((hasDerivAt_id (1 : ℝ)).const_mul 2).sub ((hasDerivAt_pow 2 (1 : ℝ)).div_const 2)
    convert this using 1
    · funext q; simp
    · norm_num
  · have := ((hasDerivAt_id (1 : ℝ)).sub ((hasDerivAt_pow 2 (1 : ℝ)).div_const 8)).add_const
      (1 / 8 : ℝ)
    convert this using 1
    · funext q; simp [costEx]
    · norm_num

/-- **Exercise 22.F.6(b)** (MWG, p. 856). The second-best problem `max S(q) - c(q)` subject to
`S'(q)q ≥ c(q)` for `S(q) = 2q - q²/2`, `c(q) = q - q²/8 + 1/8`: the constraint holds exactly
on `[1/7, 1]`, the solution is `q = 1` (where `S'(q) = c(q)/q`), and the first best `q = 4/3`
(where `S'(q) = c'(q)`) violates the constraint. -/
theorem exercise_22_F_6b :
    (∀ q : ℝ, ((2 - q) * q ≥ costEx q ↔ 1 / 7 ≤ q ∧ q ≤ 1)) ∧
      (∀ q : ℝ, (2 - q) * q ≥ costEx q →
        2 * q - q ^ 2 / 2 - costEx q ≤ 2 * 1 - 1 ^ 2 / 2 - costEx 1) ∧
      (2 - 1 : ℝ) * 1 = costEx 1 ∧ (2 - 4 / 3 : ℝ) = 1 - (4 / 3) / 4 ∧
      (2 - 4 / 3 : ℝ) * (4 / 3) < costEx (4 / 3) := by
  refine ⟨fun q => ?_, fun q hq => ?_, by norm_num [costEx], by norm_num, by norm_num [costEx]⟩
  · simp only [costEx, ge_iff_le]
    constructor
    · intro h
      constructor <;> nlinarith [sq_nonneg (q - 1), sq_nonneg (q - 1 / 7)]
    · rintro ⟨h1, h2⟩
      nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)]
  · simp only [costEx, ge_iff_le] at hq ⊢
    have h2 : q ≤ 1 := by nlinarith [sq_nonneg (q - 1)]
    nlinarith [sq_nonneg (q - 1)]

/-! ### Shapley cost allocation by project types -/

/-- The cost game of a type `T` of projects: `v(S) = C(|S ∩ T|)`. -/
def typeGame {n : ℕ} (T : Finset (Fin n)) (C : ℕ → ℝ) : Game n := fun S => C (S ∩ T).card

/-- **Section 22.F, cost allocation** (MWG, pp. 848-849). The Shapley value of
`v(S) = C(|S ∩ T|)` (`C(0) = 0`) charges each project in `T` the average cost `C(|T|)/|T|`
(symmetry and Pareto) and the others nothing (dummy axiom). -/
theorem shapley_typeGame {n : ℕ} (T : Finset (Fin n)) (C : ℕ → ℝ) (hC : C 0 = 0) (i : Fin n) :
    shapley (typeGame T C) i = if i ∈ T then C T.card / T.card else 0 := by
  classical
  have hv0 : typeGame T C ∅ = 0 := by simp [typeGame, hC]
  have hdummy : ∀ k ∉ T, shapley (typeGame T C) k = 0 := fun k hk =>
    shapley_dummy _ k hv0 fun S => by simp [typeGame, Finset.insert_inter_of_notMem hk]
  -- all projects of `T` are treated alike
  have hsymm : ∀ j ∈ T, ∀ k ∈ T, shapley (typeGame T C) j = shapley (typeGame T C) k := by
    intro j hj k hk
    set σ := Equiv.swap j k
    have hT : T.map σ.toEmbedding = T := by
      ext x
      rw [Finset.mem_map_equiv, Equiv.symm_swap]
      by_cases hxj : x = j
      · subst hxj; simp [hk, hj]
      by_cases hxk : x = k
      · subst hxk; simp [hj, hk]
      · simp [Equiv.swap_apply_of_ne_of_ne hxj hxk]
    have hinv : (fun S => typeGame T C (S.map σ.toEmbedding)) = typeGame T C := by
      funext S
      simp only [typeGame]
      congr 1
      conv_lhs => rw [← hT]
      rw [← Finset.map_inter, Finset.card_map]
    have := shapley_symmetric (typeGame T C) σ hv0 j
    rw [hinv] at this
    rw [this]; simp [σ]
  by_cases hi : i ∈ T
  · simp only [hi, ↓reduceIte]
    have hpar := shapley_pareto (typeGame T C) hv0
    have hsum : ∑ k, shapley (typeGame T C) k = T.card * shapley (typeGame T C) i := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ T)]
      rw [Finset.sum_congr rfl fun k hk => hsymm k (Finset.mem_filter.1 hk).2 i hi,
        Finset.sum_congr rfl fun k hk => hdummy k (Finset.mem_filter.1 hk).2]
      simp
    have hcard : (0 : ℝ) < T.card := by exact_mod_cast Finset.card_pos.2 ⟨i, hi⟩
    rw [hsum] at hpar
    simp only [typeGame, Finset.univ_inter] at hpar
    field_simp
    linarith
  · simp only [hi, ↓reduceIte]; exact hdummy i hi

/-- **Exercise 22.F.6(c)** (MWG, p. 856). With `q` units of output viewed as projects and cost
`c(|S|)` for `S ≠ ∅`, the Shapley value charges every unit the average cost `c(q)/q`. -/
theorem exercise_22_F_6c {q : ℕ} (c : ℕ → ℝ) (i : Fin q) :
    shapley (fun S : Finset (Fin q) => if S.card = 0 then 0 else c S.card) i = c q / q := by
  have h := shapley_typeGame (Finset.univ : Finset (Fin q))
    (fun k => if k = 0 then 0 else c k) (by simp) i
  have hq : q ≠ 0 := by rintro rfl; exact i.elim0
  simp only [Finset.mem_univ, ↓reduceIte, Finset.card_univ, Fintype.card_fin, hq] at h
  rw [← h]
  congr 1
  funext S
  simp [typeGame]

/-- **Exercise 22.F.7(b)** (MWG, p. 856). With separable costs `c₁(n₁(S)) + c₂(n₂(S))` (`nₗ(S)`
the number of projects of type `l` in `S`, `cₗ(0) = 0`), the Shapley value charges each project
the average cost `cₗ(qₗ)/qₗ` of its type. -/
theorem exercise_22_F_7b {n : ℕ} (T : Finset (Fin n)) (c₁ c₂ : ℕ → ℝ) (h₁ : c₁ 0 = 0)
    (h₂ : c₂ 0 = 0) (i : Fin n) :
    shapley (fun S => c₁ (S ∩ T).card + c₂ (S ∩ Tᶜ).card) i =
      if i ∈ T then c₁ T.card / T.card else c₂ Tᶜ.card / Tᶜ.card := by
  have := exercise_22_F_3a (typeGame T c₁) (typeGame Tᶜ c₂)
  have e : (fun S => c₁ (S ∩ T).card + c₂ (S ∩ Tᶜ).card) =
      typeGame T c₁ + typeGame Tᶜ c₂ := rfl
  rw [e, this, Pi.add_apply, shapley_typeGame T c₁ h₁, shapley_typeGame Tᶜ c₂ h₂]
  by_cases hi : i ∈ T
  · simp [hi]
  · simp [hi, Finset.mem_compl]

/-! ### Exercise 22.F.7(a): Boiteux's first-order conditions -/

open Filter Topology in
/-- Lagrange multipliers with a sign, for a separable objective `A₁(q₁) + A₂(q₂)` and a
separable inequality constraint `B₁(q₁) + B₂(q₂) ≥ R` that binds at a local maximum: there is
`μ ≥ 0` with `Aₗ' + μBₗ' = 0`, provided `(B₁', B₂') ≠ 0`. The multiplier comes from Mathlib's
`IsLocalExtrOn.exists_multipliers_of_hasStrictFDerivAt_1d`; its sign from moving along
`(B₁', B₂')`, which keeps the constraint and would raise the objective if `μ < 0`. -/
theorem separable_kkt {A₁ A₂ B₁ B₂ : ℝ → ℝ} {q₁ q₂ a₁ a₂ b₁ b₂ R : ℝ}
    (hA₁ : HasStrictDerivAt A₁ a₁ q₁) (hA₂ : HasStrictDerivAt A₂ a₂ q₂)
    (hB₁ : HasStrictDerivAt B₁ b₁ q₁) (hB₂ : HasStrictDerivAt B₂ b₂ q₂)
    (hmax : IsLocalMaxOn (fun q : ℝ × ℝ => A₁ q.1 + A₂ q.2) {q | R ≤ B₁ q.1 + B₂ q.2} (q₁, q₂))
    (hbind : B₁ q₁ + B₂ q₂ = R) (hCQ : b₁ ≠ 0 ∨ b₂ ≠ 0) :
    ∃ μ : ℝ, 0 ≤ μ ∧ a₁ + μ * b₁ = 0 ∧ a₂ + μ * b₂ = 0 := by
  set v : ℝ × ℝ → ℝ := fun q => A₁ q.1 + A₂ q.2 with hv
  set g : ℝ × ℝ → ℝ := fun q => B₁ q.1 + B₂ q.2 with hg
  have hc₁ : HasStrictFDerivAt (fun q : ℝ × ℝ => B₁ q.1) (b₁ • ContinuousLinearMap.fst ℝ ℝ ℝ)
      (q₁, q₂) := by
    have h := HasStrictDerivAt.comp_hasStrictFDerivAt (𝕜 := ℝ) (𝕜' := ℝ) (q₁, q₂) hB₁
      (hasStrictFDerivAt_fst (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := (q₁, q₂)))
    exact h
  have hc₂ : HasStrictFDerivAt (fun q : ℝ × ℝ => B₂ q.2) (b₂ • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (q₁, q₂) := by
    have h := HasStrictDerivAt.comp_hasStrictFDerivAt (𝕜 := ℝ) (𝕜' := ℝ) (q₁, q₂) hB₂
      (hasStrictFDerivAt_snd (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := (q₁, q₂)))
    exact h
  have hd₁ : HasStrictFDerivAt (fun q : ℝ × ℝ => A₁ q.1) (a₁ • ContinuousLinearMap.fst ℝ ℝ ℝ)
      (q₁, q₂) := by
    have h := HasStrictDerivAt.comp_hasStrictFDerivAt (𝕜 := ℝ) (𝕜' := ℝ) (q₁, q₂) hA₁
      (hasStrictFDerivAt_fst (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := (q₁, q₂)))
    exact h
  have hd₂ : HasStrictFDerivAt (fun q : ℝ × ℝ => A₂ q.2) (a₂ • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (q₁, q₂) := by
    have h := HasStrictDerivAt.comp_hasStrictFDerivAt (𝕜 := ℝ) (𝕜' := ℝ) (q₁, q₂) hA₂
      (hasStrictFDerivAt_snd (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := (q₁, q₂)))
    exact h
  have hgd := hc₁.add hc₂
  have hvd := hd₁.add hd₂
  have hext : IsLocalExtrOn v {p | g p = g (q₁, q₂)} (q₁, q₂) :=
    Or.inr (hmax.mono fun p (hp : g p = g (q₁, q₂)) => by
      change R ≤ g p
      rw [hp]
      exact hbind.ge)
  obtain ⟨a, b, hab, hlin⟩ := hext.exists_multipliers_of_hasStrictFDerivAt_1d hgd hvd
  have e1 := congrArg (fun L => L (1, 0)) hlin
  have e2 := congrArg (fun L => L (0, 1)) hlin
  simp only [add_apply, smul_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    smul_eq_mul, zero_apply] at e1 e2
  have hb : b ≠ 0 := by
    rintro rfl
    have ha : a ≠ 0 := fun ha => hab (by simp [ha])
    rcases hCQ with h | h
    · exact h ((mul_eq_zero.1 (by linarith : a * b₁ = 0)).resolve_left ha)
    · exact h ((mul_eq_zero.1 (by linarith : a * b₂ = 0)).resolve_left ha)
  set μ := a / b with hμ
  have h₁ : a₁ + μ * b₁ = 0 := by rw [hμ]; field_simp; linarith
  have h₂ : a₂ + μ * b₂ = 0 := by rw [hμ]; field_simp; linarith
  refine ⟨μ, ?_, h₁, h₂⟩
  by_contra hneg
  have hneg : μ < 0 := not_le.1 hneg
  have hGpos : 0 < b₁ ^ 2 + b₂ ^ 2 := by
    rcases hCQ with h | h
    · have := pow_pos (abs_pos.2 h) 2; rw [sq_abs] at this; positivity
    · have := pow_pos (abs_pos.2 h) 2; rw [sq_abs] at this; positivity
  set L : ℝ → ℝ × ℝ := fun t => (q₁, q₂) + t • (b₁, b₂) with hL
  have hLd : HasDerivAt L (b₁, b₂) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const (b₁, b₂)).const_add (q₁, q₂)
    simpa [hL] using this
  have hL0 : L 0 = (q₁, q₂) := by simp [hL]
  have hφ : HasDerivAt (v ∘ L) (-(μ * (b₁ ^ 2 + b₂ ^ 2))) 0 := by
    have := (hL0 ▸ hvd.hasFDerivAt).comp_hasDerivAt (0 : ℝ) hLd
    convert this using 1
    simp only [add_apply, smul_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', smul_eq_mul]
    linear_combination (-b₁) * h₁ - b₂ * h₂
  have hψ : HasDerivAt (g ∘ L) (b₁ ^ 2 + b₂ ^ 2) 0 := by
    have := (hL0 ▸ hgd.hasFDerivAt).comp_hasDerivAt (0 : ℝ) hLd
    convert this using 1
    simp only [add_apply, smul_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', smul_eq_mul]
    ring
  have hφpos : 0 < -(μ * (b₁ ^ 2 + b₂ ^ 2)) := by nlinarith
  have t1 := (hφ.tendsto_slope_zero_right).eventually (lt_mem_nhds hφpos)
  have t2 := (hψ.tendsto_slope_zero_right).eventually (lt_mem_nhds hGpos)
  have hLc : Tendsto L (𝓝[>] (0 : ℝ)) (𝓝 (q₁, q₂)) :=
    hL0 ▸ (hLd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have t3 := hLc.eventually (eventually_nhdsWithin_iff.1 hmax)
  obtain ⟨t, ⟨h1, h2, h3⟩, ht⟩ := ((t1.and (t2.and t3)).and self_mem_nhdsWithin).exists
  have ht' : (0 : ℝ) < t := ht
  simp only [zero_add, smul_eq_mul, Function.comp] at h1 h2
  rw [hL0] at h1 h2
  have hti : 0 < t⁻¹ := inv_pos.2 ht'
  have hv' : v (q₁, q₂) < v (L t) := by
    have := pos_of_mul_pos_right h1 hti.le; linarith
  have hg' : R < g (L t) := by
    have := pos_of_mul_pos_right h2 hti.le
    have hg0 : g (q₁, q₂) = R := hbind
    linarith
  exact absurd (h3 hg'.le) (not_le.2 hv')

/-- **Exercise 22.F.7(a)** (MWG, p. 856), Boiteux's problem. Let `Pₗ = Sₗ'` be the inverse
demands (`Pₗ'(qₗ) = dₗ`), `cₗ` the costs (`cₗ' = mₗ`), and let `(q₁, q₂)` maximize
`S₁ + S₂ - c₁ - c₂` locally subject to `P₁q₁ + P₂q₂ ≥ c₁ + c₂`, binding, with nonzero constraint
gradient. Then there is `μ ≥ 0` with `(pₗ - mₗ) + μ(pₗ + dₗqₗ - mₗ) = 0`, and, when
`pₗ > 0`, the Ramsey-type formula `(pₗ - mₗ)/pₗ = (μ/(1+μ))(-dₗqₗ/pₗ)`. -/
theorem exercise_22_F_7a {S₁ S₂ P₁ P₂ c₁ c₂ : ℝ → ℝ} {q₁ q₂ d₁ d₂ m₁ m₂ : ℝ}
    (hS₁ : HasStrictDerivAt S₁ (P₁ q₁) q₁) (hS₂ : HasStrictDerivAt S₂ (P₂ q₂) q₂)
    (hP₁ : HasStrictDerivAt P₁ d₁ q₁) (hP₂ : HasStrictDerivAt P₂ d₂ q₂)
    (hc₁ : HasStrictDerivAt c₁ m₁ q₁) (hc₂ : HasStrictDerivAt c₂ m₂ q₂)
    (hmax : IsLocalMaxOn (fun q : ℝ × ℝ => (S₁ q.1 - c₁ q.1) + (S₂ q.2 - c₂ q.2))
      {q | 0 ≤ (P₁ q.1 * q.1 - c₁ q.1) + (P₂ q.2 * q.2 - c₂ q.2)} (q₁, q₂))
    (hbind : (P₁ q₁ * q₁ - c₁ q₁) + (P₂ q₂ * q₂ - c₂ q₂) = 0)
    (hCQ : P₁ q₁ + d₁ * q₁ - m₁ ≠ 0 ∨ P₂ q₂ + d₂ * q₂ - m₂ ≠ 0) :
    ∃ μ : ℝ, 0 ≤ μ ∧ (P₁ q₁ - m₁) + μ * (P₁ q₁ + d₁ * q₁ - m₁) = 0 ∧
      (P₂ q₂ - m₂) + μ * (P₂ q₂ + d₂ * q₂ - m₂) = 0 ∧
      (0 < P₁ q₁ → (P₁ q₁ - m₁) / P₁ q₁ = μ / (1 + μ) * (-(d₁ * q₁) / P₁ q₁)) ∧
      (0 < P₂ q₂ → (P₂ q₂ - m₂) / P₂ q₂ = μ / (1 + μ) * (-(d₂ * q₂) / P₂ q₂)) := by
  have hR₁ : HasStrictDerivAt (fun q => P₁ q * q - c₁ q) (P₁ q₁ + d₁ * q₁ - m₁) q₁ := by
    have h := (hP₁.fun_mul (hasStrictDerivAt_id q₁)).fun_sub hc₁
    simp only [id, mul_one] at h
    convert h using 1; ring
  have hR₂ : HasStrictDerivAt (fun q => P₂ q * q - c₂ q) (P₂ q₂ + d₂ * q₂ - m₂) q₂ := by
    have h := (hP₂.fun_mul (hasStrictDerivAt_id q₂)).fun_sub hc₂
    simp only [id, mul_one] at h
    convert h using 1; ring
  obtain ⟨μ, hμ, h₁, h₂⟩ := separable_kkt (hS₁.sub hc₁) (hS₂.sub hc₂) hR₁ hR₂ hmax hbind hCQ
  refine ⟨μ, hμ, h₁, h₂, fun hp => ?_, fun hp => ?_⟩
  · have h1μ : (1 + μ) ≠ 0 := by linarith
    rw [div_mul_div_comm, div_eq_div_iff hp.ne' (mul_ne_zero h1μ hp.ne')]
    linear_combination P₁ q₁ * h₁
  · have h1μ : (1 + μ) ≠ 0 := by linarith
    rw [div_mul_div_comm, div_eq_div_iff hp.ne' (mul_ne_zero h1μ hp.ne')]
    linear_combination P₂ q₂ * h₂

/-- **Exercise 22.F.7(a)**, instance (MWG, p. 856): two identical types with `Pₗ(q) = 2 - q`,
`cₗ(q) = q - q²/8 + 1/8`. Under the break-even constraint the surplus is maximized at
`q = (1, 1)` (the Lagrangian with `μ = 1/3` is maximized there). -/
theorem exercise_22_F_7a_instance :
    ∀ q : ℝ × ℝ, 0 ≤ ((2 - q.1) * q.1 - costEx q.1) + ((2 - q.2) * q.2 - costEx q.2) →
      (2 * q.1 - q.1 ^ 2 / 2 - costEx q.1) + (2 * q.2 - q.2 ^ 2 / 2 - costEx q.2) ≤
        (2 * 1 - 1 ^ 2 / 2 - costEx 1) + (2 * 1 - 1 ^ 2 / 2 - costEx 1) := by
  intro q hq
  simp only [costEx] at hq ⊢
  nlinarith [sq_nonneg (q.1 - 1), sq_nonneg (q.2 - 1)]

/-- The second type of `exercise_22_F_7c`: `c₂(q) = q - q²/8 + 5/2`. -/
noncomputable def costEx₂ (q : ℝ) : ℝ := q - q ^ 2 / 8 + 5 / 2

/-- **Exercise 22.F.7(c)** (MWG, p. 856). Type 1: `P₁(q) = 2 - q`, `c₁ = costEx`; type 2:
`P₂(q) = 4 - q`, `c₂ = costEx₂`. At `(q̄₁, q̄₂) = (1, 2)` each price equals the Shapley unit
cost `cₗ(q̄ₗ)/q̄ₗ` (`1` and `2`), so every type breaks even; yet this is not second best
(`(9/10, 21/10)` also covers total cost and gives more surplus) and not first best (the
surplus at `(4/3, 4)`, where prices equal marginal costs, is larger still). -/
theorem exercise_22_F_7c :
    (2 - 1 : ℝ) = costEx 1 / 1 ∧ (4 - 2 : ℝ) = costEx₂ 2 / 2 ∧
      (0 : ℝ) ≤ ((2 - 9 / 10) * (9 / 10) - costEx (9 / 10)) +
        ((4 - 21 / 10) * (21 / 10) - costEx₂ (21 / 10)) ∧
      (2 * 1 - 1 ^ 2 / 2 - costEx 1) + (4 * 2 - 2 ^ 2 / 2 - costEx₂ 2) <
        (2 * (9 / 10) - (9 / 10) ^ 2 / 2 - costEx (9 / 10)) +
          (4 * (21 / 10) - (21 / 10) ^ 2 / 2 - costEx₂ (21 / 10)) ∧
      (2 - 4 / 3 : ℝ) = 1 - (4 / 3) / 4 ∧ (4 - 4 : ℝ) = 1 - 4 / 4 ∧
      (2 * 1 - 1 ^ 2 / 2 - costEx 1) + (4 * 2 - 2 ^ 2 / 2 - costEx₂ 2) <
        (2 * (4 / 3) - (4 / 3) ^ 2 / 2 - costEx (4 / 3)) +
          (4 * 4 - 4 ^ 2 / 2 - costEx₂ 4) := by
  norm_num [costEx, costEx₂]

end MWG.WelfareBargaining
