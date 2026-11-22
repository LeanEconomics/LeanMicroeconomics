/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGClassicalDemand.LastComposite
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-!
# Exercise 3.G.5(b)-(c): demand and Hicksian demand for the composite commodity

MWG, Exercise 3.G.5(b)-(c), p. 100. Standing assumptions (as in `LastComposite`): `q₀ ≫ 0`;
`u` continuous on `ℝ^A_+ × ℝ^B_+`, strictly increasing in the `y` goods ("desirable"), and
strictly quasiconcave on `ℝ^{A+B}_+`. The composite utility `ũ` on `ℝ^{A+1}_+` is then continuous,
locally nonsatiated and strictly quasiconcave (`last_composite_continuousOn`,
`last_composite_lns`, `last_composite_strictlyQuasiconcave`), so the project's general results
apply to it with `L = A + 1`. Composite prices are `(p, α) = Fin.snoc p α`.

* **(b)** `x(p, α, w)` and `z(p, α, w)`: homogeneity of degree zero, Walras' law
  `p·x + αz = w`, existence and uniqueness (Proposition 3.D.2, `exercise_3_G_5b`); they are the
  consumer's actual `x` and `z = q₀·y` (`exercise_3_G_5b_actual`, from Exercise 3.G.5(a));
  Roy's identity (Proposition 3.G.4, `exercise_3_G_5b_roy`).
* **(c)** The Hicksian demand of `ũ`: Proposition 3.E.3 (`exercise_3_G_5c_E3`), Shephard's lemma
  (Proposition 3.G.1, `exercise_3_G_5c_G1`), the properties of `D_p h` (Proposition 3.G.2,
  `exercise_3_G_5c_G2`) and the Slutsky equation (Proposition 3.G.3, `exercise_3_G_5c_G3`).
-/

namespace MWG.ClassicalDemand

open MWG.ConsumerChoice Kreps.PreferenceProperties Filter Topology

variable {A B : ℕ}

/-- The standing assumptions give `ũ` the hypotheses of Sections 3.D-3.G on `ℝ^{A+1}_+`:
continuity, local nonsatiation, strict quasiconcavity and strict convexity of its preference. -/
theorem last_composite_hyps {u : (Fin A → ℝ) → (Fin B → ℝ) → ℝ} {q0 : Fin B → ℝ}
    (hq0 : StrictlyPositive q0)
    (hu : ContinuousOn (Function.uncurry u) (nonnegOrthant A ×ˢ nonnegOrthant B))
    (hmono : ∀ x ∈ nonnegOrthant A, ∀ y ∈ nonnegOrthant B, ∀ y' : Fin B → ℝ,
      (∀ j, y j < y' j) → u x y < u x y')
    (hsq : ∀ x ∈ nonnegOrthant A, ∀ x' ∈ nonnegOrthant A, ∀ y ∈ nonnegOrthant B,
      ∀ y' ∈ nonnegOrthant B, (x, y) ≠ (x', y') → ∀ a : ℝ, 0 < a → a < 1 →
        min (u x y) (u x' y') < u (a • x + (1 - a) • x') (a • y + (1 - a) • y')) :
    ContinuousOn (lastCompositeVec u q0) (nonnegOrthant (A + 1)) ∧
      LocallyNonsatiated (nonnegOrthant (A + 1)) (utilityPref (lastCompositeVec u q0)) ∧
      StrictlyQuasiconcaveOn (nonnegOrthant (A + 1)) (lastCompositeVec u q0) ∧
      PrefStrictlyConvex (nonnegOrthant (A + 1)) (utilityPref (lastCompositeVec u q0)) := by
  have hS := last_composite_strictlyQuasiconcave hq0 hu hmono hsq
  exact ⟨last_composite_continuousOn hq0 hu, last_composite_lns hq0 hu hmono, hS,
    (prefStrictlyConvex_iff_strictlyQuasiconcaveOn (convex_nonnegOrthant (A + 1))
      (representsOn_utilityPref _ _)).mpr hS⟩

/-- **Exercise 3.G.5(b)** (MWG, p. 100), Proposition 3.D.2 for the composite demand
`(x, z)(p, α, w)`: (i) homogeneous of degree zero in `(p, α, w)`; (ii) Walras' law
`p·x + αz = w`; (iii) single-valued (it exists and is unique). -/
theorem exercise_3_G_5b {u : (Fin A → ℝ) → (Fin B → ℝ) → ℝ} {q0 : Fin B → ℝ}
    (hq0 : StrictlyPositive q0)
    (hu : ContinuousOn (Function.uncurry u) (nonnegOrthant A ×ˢ nonnegOrthant B))
    (hmono : ∀ x ∈ nonnegOrthant A, ∀ y ∈ nonnegOrthant B, ∀ y' : Fin B → ℝ,
      (∀ j, y j < y' j) → u x y < u x y')
    (hsq : ∀ x ∈ nonnegOrthant A, ∀ x' ∈ nonnegOrthant A, ∀ y ∈ nonnegOrthant B,
      ∀ y' ∈ nonnegOrthant B, (x, y) ≠ (x', y') → ∀ a : ℝ, 0 < a → a < 1 →
        min (u x y) (u x' y') < u (a • x + (1 - a) • x') (a • y + (1 - a) • y'))
    {p : Fin A → ℝ} (hp : StrictlyPositive p) {α w : ℝ} (hα : 0 < α) (hw : 0 ≤ w) :
    (∀ t : ℝ, 0 < t → walrasianDemand (lastCompositeVec u q0) (t • lastSnoc p α) (t * w) =
      walrasianDemand (lastCompositeVec u q0) (lastSnoc p α) w) ∧
    (∀ v ∈ walrasianDemand (lastCompositeVec u q0) (lastSnoc p α) w,
      p ⬝ᵥ Fin.init v + α * v (Fin.last A) = w) ∧
    ∃ v, walrasianDemand (lastCompositeVec u q0) (lastSnoc p α) w = {v} := by
  obtain ⟨hc, hl, hs, -⟩ := last_composite_hyps hq0 hu hmono hsq
  have hP : StrictlyPositive (lastSnoc p α) := (last_snoc_pos p α).mpr ⟨hp, hα⟩
  refine ⟨fun t ht => proposition_3_D_2_i _ _ _ ht, fun v hv => ?_, ?_⟩
  · have h := proposition_3_D_2_ii (representsOn_utilityPref _ _) hl hv
    rwa [← lastSnoc_init v, last_snoc_dot] at h
  · obtain ⟨v, hv⟩ := proposition_3_D_1 hc hP hw
    exact ⟨v, Set.eq_singleton_iff_unique_mem.mpr
      ⟨hv, fun v' hv' => proposition_3_D_2_iii_unique hs _ _ hv' hv⟩⟩

/-- **Exercise 3.G.5(b)** (MWG, p. 100), with (a): if `(x*, y*)` solves the consumer's UMP at
prices `(p, αq₀)` and wealth `w`, the composite demand is `{(x*, q₀·y*)}`, so
`x(p, α, w) = x*` and `z(p, α, w) = q₀·y*` are the consumer's actual levels. -/
theorem exercise_3_G_5b_actual {u : (Fin A → ℝ) → (Fin B → ℝ) → ℝ} {q0 : Fin B → ℝ}
    (hq0 : StrictlyPositive q0)
    (hu : ContinuousOn (Function.uncurry u) (nonnegOrthant A ×ˢ nonnegOrthant B))
    (hmono : ∀ x ∈ nonnegOrthant A, ∀ y ∈ nonnegOrthant B, ∀ y' : Fin B → ℝ,
      (∀ j, y j < y' j) → u x y < u x y')
    (hsq : ∀ x ∈ nonnegOrthant A, ∀ x' ∈ nonnegOrthant A, ∀ y ∈ nonnegOrthant B,
      ∀ y' ∈ nonnegOrthant B, (x, y) ≠ (x', y') → ∀ a : ℝ, 0 < a → a < 1 →
        min (u x y) (u x' y') < u (a • x + (1 - a) • x') (a • y + (1 - a) • y'))
    {p : Fin A → ℝ} {α w : ℝ} (hα : 0 < α) {xs : Fin A → ℝ} {ys : Fin B → ℝ}
    (hfeas : xs ∈ nonnegOrthant A ∧ ys ∈ nonnegOrthant B ∧ p ⬝ᵥ xs + (α • q0) ⬝ᵥ ys ≤ w)
    (hopt : ∀ x y, x ∈ nonnegOrthant A → y ∈ nonnegOrthant B →
      p ⬝ᵥ x + (α • q0) ⬝ᵥ y ≤ w → u x y ≤ u xs ys) :
    walrasianDemand (lastCompositeVec u q0) (lastSnoc p α) w = {lastSnoc xs (q0 ⬝ᵥ ys)} := by
  obtain ⟨-, -, hs, -⟩ := last_composite_hyps hq0 hu hmono hsq
  obtain ⟨hval, ⟨hx, hz, hb⟩, hbest⟩ := exercise_3_G_5a hq0 hα hfeas hopt
  have hmem : lastSnoc xs (q0 ⬝ᵥ ys) ∈
      walrasianDemand (lastCompositeVec u q0) (lastSnoc p α) w := by
    refine ⟨⟨(last_snoc_mem _ _).mpr ⟨hx, hz⟩, by rw [last_snoc_dot]; exact hb⟩, fun v hv => ?_⟩
    have hv' := hv
    rw [← lastSnoc_init v] at hv'
    obtain ⟨hvm, hvb⟩ := hv'
    rw [last_snoc_mem] at hvm
    rw [last_snoc_dot] at hvb
    rw [← lastSnoc_init v, lastCompositeVec_snoc, lastCompositeVec_snoc]
    exact hbest _ _ hvm.1 hvm.2 hvb
  exact Set.eq_singleton_iff_unique_mem.mpr
    ⟨hmem, fun v hv => proposition_3_D_2_iii_unique hs _ _ hv hmem⟩

/-- **Exercise 3.G.5(b)** (MWG, p. 100), Proposition 3.G.4 (Roy's identity) for the composite
demand: wherever the composite indirect utility `ṽ` is differentiable at `((p, α), w)`, `w > 0`,
`∂ṽ/∂p_l + (∂ṽ/∂w) x_l = 0` for every composite good (the `x` goods and `z`), and
`x_l = -(∂ṽ/∂p_l)/(∂ṽ/∂w)` when `∂ṽ/∂w ≠ 0`. -/
theorem exercise_3_G_5b_roy {u : (Fin A → ℝ) → (Fin B → ℝ) → ℝ} {q0 : Fin B → ℝ}
    (hq0 : StrictlyPositive q0)
    (hu : ContinuousOn (Function.uncurry u) (nonnegOrthant A ×ˢ nonnegOrthant B))
    (hmono : ∀ x ∈ nonnegOrthant A, ∀ y ∈ nonnegOrthant B, ∀ y' : Fin B → ℝ,
      (∀ j, y j < y' j) → u x y < u x y')
    (hsq : ∀ x ∈ nonnegOrthant A, ∀ x' ∈ nonnegOrthant A, ∀ y ∈ nonnegOrthant B,
      ∀ y' ∈ nonnegOrthant B, (x, y) ≠ (x', y') → ∀ a : ℝ, 0 < a → a < 1 →
        min (u x y) (u x' y') < u (a • x + (1 - a) • x') (a • y + (1 - a) • y'))
    {p : Fin A → ℝ} (hp : StrictlyPositive p) {α w : ℝ} (hα : 0 < α) (hw : 0 < w)
    {Dv : ((Fin (A + 1) → ℝ) × ℝ) →L[ℝ] ℝ}
    (hD : HasFDerivAt (fun q : (Fin (A + 1) → ℝ) × ℝ =>
      indirectUtility (lastCompositeVec u q0) q.1 q.2) Dv (lastSnoc p α, w))
    {v : Fin (A + 1) → ℝ} (hv : v ∈ walrasianDemand (lastCompositeVec u q0) (lastSnoc p α) w) :
    (∀ l, Dv (Pi.single l 1, 0) + Dv (0, 1) * v l = 0) ∧
      (Dv (0, 1) ≠ 0 → ∀ l, v l = -(Dv (Pi.single l 1, 0) / Dv (0, 1))) := by
  obtain ⟨hc, hl, -, hsc⟩ := last_composite_hyps hq0 hu hmono hsq
  exact proposition_3_G_4 (representsOn_utilityPref _ _) hc hl hsc
    ⟨(last_snoc_pos p α).mpr ⟨hp, hα⟩, hw⟩ hD hv

/-- **Exercise 3.G.5(c)** (MWG, p. 100), Proposition 3.E.3 for the Hicksian demand of `ũ` at
composite prices `P ≫ 0` and an attainable level `ū ≥ ũ(0)`: (i) homogeneous of degree zero in
`P`; (ii) no excess utility; (iii) single-valued. -/
theorem exercise_3_G_5c_E3 {u : (Fin A → ℝ) → (Fin B → ℝ) → ℝ} {q0 : Fin B → ℝ}
    (hq0 : StrictlyPositive q0)
    (hu : ContinuousOn (Function.uncurry u) (nonnegOrthant A ×ˢ nonnegOrthant B))
    (hmono : ∀ x ∈ nonnegOrthant A, ∀ y ∈ nonnegOrthant B, ∀ y' : Fin B → ℝ,
      (∀ j, y j < y' j) → u x y < u x y')
    (hsq : ∀ x ∈ nonnegOrthant A, ∀ x' ∈ nonnegOrthant A, ∀ y ∈ nonnegOrthant B,
      ∀ y' ∈ nonnegOrthant B, (x, y) ≠ (x', y') → ∀ a : ℝ, 0 < a → a < 1 →
        min (u x y) (u x' y') < u (a • x + (1 - a) • x') (a • y + (1 - a) • y'))
    {P : Fin (A + 1) → ℝ} (hP : StrictlyPositive P) {ub : ℝ}
    (hub : lastCompositeVec u q0 0 ≤ ub)
    (hne : ∃ v ∈ nonnegOrthant (A + 1), ub ≤ lastCompositeVec u q0 v) :
    (∀ t : ℝ, 0 < t → hicksianDemand (lastCompositeVec u q0) (t • P) ub =
      hicksianDemand (lastCompositeVec u q0) P ub) ∧
    (∀ v ∈ hicksianDemand (lastCompositeVec u q0) P ub, lastCompositeVec u q0 v = ub) ∧
    ∃ v, hicksianDemand (lastCompositeVec u q0) P ub = {v} := by
  obtain ⟨hc, -, -, hsc⟩ := last_composite_hyps hq0 hu hmono hsq
  refine ⟨fun t ht => proposition_3_E_3_i _ _ _ ht,
    fun v hv => proposition_3_E_3_ii hc hP hub hv, ?_⟩
  obtain ⟨v, hv⟩ := exercise_3_E_3 hc hP hne
  exact ⟨v, Set.eq_singleton_iff_unique_mem.mpr ⟨hv, fun v' hv' =>
    (proposition_3_E_3_iii (representsOn_utilityPref _ _) hc hP ub).2 hsc hv' hv⟩⟩

/-- **Exercise 3.G.5(c)** (MWG, p. 100), Proposition 3.G.1 (Shephard's lemma) for `ũ`: the
Hicksian demand `h̃(P, ū)` is the gradient of the composite expenditure function `ẽ(·, ū)`. -/
theorem exercise_3_G_5c_G1 {u : (Fin A → ℝ) → (Fin B → ℝ) → ℝ} {q0 : Fin B → ℝ}
    (hq0 : StrictlyPositive q0)
    (hu : ContinuousOn (Function.uncurry u) (nonnegOrthant A ×ˢ nonnegOrthant B))
    (hmono : ∀ x ∈ nonnegOrthant A, ∀ y ∈ nonnegOrthant B, ∀ y' : Fin B → ℝ,
      (∀ j, y j < y' j) → u x y < u x y')
    (hsq : ∀ x ∈ nonnegOrthant A, ∀ x' ∈ nonnegOrthant A, ∀ y ∈ nonnegOrthant B,
      ∀ y' ∈ nonnegOrthant B, (x, y) ≠ (x', y') → ∀ a : ℝ, 0 < a → a < 1 →
        min (u x y) (u x' y') < u (a • x + (1 - a) • x') (a • y + (1 - a) • y'))
    {P : Fin (A + 1) → ℝ} (hP : StrictlyPositive P) {ub : ℝ}
    (hne : ∃ v ∈ nonnegOrthant (A + 1), ub ≤ lastCompositeVec u q0 v) :
    ∃ v, hicksianDemand (lastCompositeVec u q0) P ub = {v} ∧
      HasFDerivAt (fun Q => expenditure (lastCompositeVec u q0) Q ub) (dualityDotCLM v) P ∧
      ∀ l, v l =
        gradientVec (fderiv ℝ (fun Q => expenditure (lastCompositeVec u q0) Q ub) P) l := by
  obtain ⟨hc, -, -, hsc⟩ := last_composite_hyps hq0 hu hmono hsq
  exact proposition_3_G_1 (representsOn_utilityPref _ _) hc hsc hP hne

/-- **Exercise 3.G.5(c)** (MWG, p. 100), Proposition 3.G.2 for `ũ`: if a Hicksian demand
function `h̃(·, ū)` of `ũ` is differentiable at `P ≫ 0` with derivative `D`, then
(i) `D = D²_P ẽ(P, ū)`, (ii) `D` is negative semidefinite, (iii) symmetric, (iv) `D P = 0`. -/
theorem exercise_3_G_5c_G2 {u : (Fin A → ℝ) → (Fin B → ℝ) → ℝ} {q0 : Fin B → ℝ}
    (hq0 : StrictlyPositive q0)
    (hu : ContinuousOn (Function.uncurry u) (nonnegOrthant A ×ˢ nonnegOrthant B))
    (hmono : ∀ x ∈ nonnegOrthant A, ∀ y ∈ nonnegOrthant B, ∀ y' : Fin B → ℝ,
      (∀ j, y j < y' j) → u x y < u x y')
    (hsq : ∀ x ∈ nonnegOrthant A, ∀ x' ∈ nonnegOrthant A, ∀ y ∈ nonnegOrthant B,
      ∀ y' ∈ nonnegOrthant B, (x, y) ≠ (x', y') → ∀ a : ℝ, 0 < a → a < 1 →
        min (u x y) (u x' y') < u (a • x + (1 - a) • x') (a • y + (1 - a) • y'))
    {ub : ℝ} {hf : (Fin (A + 1) → ℝ) → (Fin (A + 1) → ℝ)}
    (hhf : ∀ Q, StrictlyPositive Q → hf Q ∈ hicksianDemand (lastCompositeVec u q0) Q ub)
    {P : Fin (A + 1) → ℝ} (hP : StrictlyPositive P)
    {D : (Fin (A + 1) → ℝ) →L[ℝ] (Fin (A + 1) → ℝ)} (hD : HasFDerivAt hf D P) :
    MWG.ConsumerChoice.hessianMatrix (fun Q => expenditure (lastCompositeVec u q0) Q ub) P =
        jacobian D ∧
      NegSemidef (jacobian D) ∧ (∀ i j, jacobian D i j = jacobian D j i) ∧ D P = 0 := by
  obtain ⟨hc, -, hs, -⟩ := last_composite_hyps hq0 hu hmono hsq
  exact ⟨proposition_3_G_2_i hc hs hhf hP hD, proposition_3_G_2_ii _ hhf hP hD,
    proposition_3_G_2_iii hc hs hhf hP hD, proposition_3_G_2_iv hc hs hhf hP hD⟩

/-- **Exercise 3.G.5(c)** (MWG, p. 100), Proposition 3.G.3 (the Slutsky equation) for `ũ`: if
the composite Walrasian demand function is differentiable at `(P, w)`, the Hicksian demand at
`ū = ṽ(P, w)` has derivative `D_P x̃ + D_w x̃ x̃ᵀ`, whose matrix is the Slutsky matrix. -/
theorem exercise_3_G_5c_G3 {u : (Fin A → ℝ) → (Fin B → ℝ) → ℝ} {q0 : Fin B → ℝ}
    (hq0 : StrictlyPositive q0)
    (hu : ContinuousOn (Function.uncurry u) (nonnegOrthant A ×ˢ nonnegOrthant B))
    (hmono : ∀ x ∈ nonnegOrthant A, ∀ y ∈ nonnegOrthant B, ∀ y' : Fin B → ℝ,
      (∀ j, y j < y' j) → u x y < u x y')
    (hsq : ∀ x ∈ nonnegOrthant A, ∀ x' ∈ nonnegOrthant A, ∀ y ∈ nonnegOrthant B,
      ∀ y' ∈ nonnegOrthant B, (x, y) ≠ (x', y') → ∀ a : ℝ, 0 < a → a < 1 →
        min (u x y) (u x' y') < u (a • x + (1 - a) • x') (a • y + (1 - a) • y'))
    {xf : DemandFunction (A + 1)}
    (hxf : ∀ P w, PWDomain P w → xf P w ∈ walrasianDemand (lastCompositeVec u q0) P w)
    {P₀ : Fin (A + 1) → ℝ} {w₀ : ℝ} (hpw : PWDomain P₀ w₀)
    {Dx : ((Fin (A + 1) → ℝ) × ℝ) →L[ℝ] (Fin (A + 1) → ℝ)}
    (hD : HasFDerivAt (Function.uncurry xf) Dx (P₀, w₀))
    {hf : (Fin (A + 1) → ℝ) → (Fin (A + 1) → ℝ)}
    (hhf : ∀ Q, StrictlyPositive Q → hf Q ∈
      hicksianDemand (lastCompositeVec u q0) Q (indirectUtility (lastCompositeVec u q0) P₀ w₀)) :
    HasFDerivAt hf
        (Dx.comp ((ContinuousLinearMap.id ℝ (Fin (A + 1) → ℝ)).prod
          (dualityDotCLM (xf P₀ w₀)))) P₀ ∧
      jacobian (Dx.comp ((ContinuousLinearMap.id ℝ (Fin (A + 1) → ℝ)).prod
        (dualityDotCLM (xf P₀ w₀)))) = slutskyMatrix Dx (xf P₀ w₀) := by
  obtain ⟨hc, hl, -, hsc⟩ := last_composite_hyps hq0 hu hmono hsq
  exact proposition_3_G_3 (representsOn_utilityPref _ _) hc hl hsc hxf hpw hD hhf

/-- The standing assumptions of Exercise 3.G.5(b)-(c) are consistent: with one good of each kind,
`u(x, y) = √x + √y` and `q₀ = 1` satisfy all of them. -/
theorem last_composite_instance :
    StrictlyPositive (fun _ => (1 : ℝ) : Fin 1 → ℝ) ∧
    ContinuousOn (Function.uncurry fun (x : Fin 1 → ℝ) (y : Fin 1 → ℝ) =>
      Real.sqrt (x 0) + Real.sqrt (y 0)) (nonnegOrthant 1 ×ˢ nonnegOrthant 1) ∧
    (∀ x ∈ nonnegOrthant 1, ∀ y ∈ nonnegOrthant 1, ∀ y' : Fin 1 → ℝ, (∀ j, y j < y' j) →
      Real.sqrt (x 0) + Real.sqrt (y 0) < Real.sqrt (x 0) + Real.sqrt (y' 0)) ∧
    (∀ x ∈ nonnegOrthant 1, ∀ x' ∈ nonnegOrthant 1, ∀ y ∈ nonnegOrthant 1,
      ∀ y' ∈ nonnegOrthant 1, (x, y) ≠ (x', y') → ∀ a : ℝ, 0 < a → a < 1 →
        min (Real.sqrt (x 0) + Real.sqrt (y 0)) (Real.sqrt (x' 0) + Real.sqrt (y' 0)) <
          Real.sqrt ((a • x + (1 - a) • x') 0) + Real.sqrt ((a • y + (1 - a) • y') 0)) := by
  refine ⟨fun _ => one_pos, ?_, fun x _ y hy y' hyy => ?_, ?_⟩
  · exact Continuous.continuousOn (by fun_prop)
  · have := Real.sqrt_lt_sqrt (hy 0) (hyy 0)
    linarith
  · intro x hx x' hx' y hy y' hy' hne a ha0 ha1
    have hb : 0 < 1 - a := by linarith
    have hS := Real.strictConcaveOn_sqrt
    have hC := hS.concaveOn
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hx0 : x 0 ∈ Set.Ici (0 : ℝ) := hx 0
    have hx0' : x' 0 ∈ Set.Ici (0 : ℝ) := hx' 0
    have hy0 : y 0 ∈ Set.Ici (0 : ℝ) := hy 0
    have hy0' : y' 0 ∈ Set.Ici (0 : ℝ) := hy' 0
    have hcx := hC.2 hx0 hx0' ha0.le hb.le (by ring)
    have hcy := hC.2 hy0 hy0' ha0.le hb.le (by ring)
    simp only [smul_eq_mul] at hcx hcy
    have hstrict : a * Real.sqrt (x 0) + (1 - a) * Real.sqrt (x' 0) +
        (a * Real.sqrt (y 0) + (1 - a) * Real.sqrt (y' 0)) <
        Real.sqrt (a * x 0 + (1 - a) * x' 0) + Real.sqrt (a * y 0 + (1 - a) * y' 0) := by
      by_cases hxx : x 0 = x' 0
      · have hyy : y 0 ≠ y' 0 := by
          intro h
          apply hne
          have e1 : x = x' := funext fun i => by fin_cases i; exact hxx
          have e2 : y = y' := funext fun i => by fin_cases i; exact h
          rw [e1, e2]
        have := hS.2 hy0 hy0' hyy ha0 hb (by ring)
        simp only [smul_eq_mul] at this
        linarith
      · have := hS.2 hx0 hx0' hxx ha0 hb (by ring)
        simp only [smul_eq_mul] at this
        linarith
    have hmin : min (Real.sqrt (x 0) + Real.sqrt (y 0)) (Real.sqrt (x' 0) + Real.sqrt (y' 0)) ≤
        a * (Real.sqrt (x 0) + Real.sqrt (y 0)) +
          (1 - a) * (Real.sqrt (x' 0) + Real.sqrt (y' 0)) := by
      rcases le_total (Real.sqrt (x 0) + Real.sqrt (y 0)) (Real.sqrt (x' 0) + Real.sqrt (y' 0))
        with h | h
      · rw [min_eq_left h]; nlinarith
      · rw [min_eq_right h]; nlinarith
    linarith

end MWG.ClassicalDemand
