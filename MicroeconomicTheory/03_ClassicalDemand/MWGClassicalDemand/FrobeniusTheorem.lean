/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGClassicalDemand.FrobeniusDependence
import MWGClassicalDemand.HardIntegrability
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Frobenius' theorem for one unknown function, by integration along rays

MWG, Section 3.H, p. 80: "A basic result of the theory of partial differential equations (called
Frobenius' theorem) tells us that the symmetry of the `L × L` derivative matrix of (3.H.2) at all
points of its domain is the necessary and sufficient condition for the existence of a solution to
(3.H.2)." This module proves the sufficiency half for a system `∂Z/∂q = f(q, Z)` on all of
`ℝ^L × ℝ`, which is the form (3.H.2) takes in logarithmic coordinates (`FrobeniusIntegrability`).

Hypotheses on `f : ℝ^L × ℝ → ℝ^L`: `f` is `C¹`; `|v·f(q, z)| ≤ ‖v‖` (sup norm), which rules out
blow-up; and the integrability condition
`h·D f(q, z)(v, v·f(q, z)) = v·D f(q, z)(h, h·f(q, z))`, i.e. symmetry of the matrix
`A = D_q f + D_z f fᵀ` (for (3.H.2) this is the symmetry of the Slutsky matrix).

Construction (the route of the source map F1): `Z(q)` is the value at `s = 1` of the solution of the
scalar equation `y'(s) = (q - q₀)·f(q₀ + s(q - q₀), y)`, `y(0) = u`, along the segment from `q₀`
(`frobRayField`). Global existence: Picard-Lindelöf with the bound on `f` (`frob_ray_exists`).
Differentiability: `D(s)k = s k·f(q₀ + s(q - q₀), y(s))` solves the variational equation exactly,
because the defect is `s (k·A v - v·A k) = 0` by the integrability condition; then
`frob_hasFDerivAt_endpoint` gives `∇Z(q) = f(q, Z(q))` (`frobenius_ray_family`).

The family indexed by the initial value `u` is strictly increasing, onto and continuous in `u`
at every `q`, as needed by `integrability_of_pde`.
-/

namespace MWG.ClassicalDemand

open MWG.ConsumerChoice Filter Topology

variable {L : ℕ}

/-- Product rule for the dot product of two curves in `ℝ^L`. -/
theorem frob_hasDerivAt_dotProduct {a b : ℝ → Fin L → ℝ} {a' b' : Fin L → ℝ} {t : ℝ}
    (ha : HasDerivAt a a' t) (hb : HasDerivAt b b' t) :
    HasDerivAt (fun τ => a τ ⬝ᵥ b τ) (a' ⬝ᵥ b t + a t ⬝ᵥ b') t := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
    (hasDerivAt_pi.mp ha i).mul (hasDerivAt_pi.mp hb i)
  unfold dotProduct
  convert h using 1
  rw [← Finset.sum_add_distrib]

/-- The field of the scalar equation along the segment from `q₀` to `q`:
`G(s, q, y) = (q - q₀)·f(q₀ + s(q - q₀), y)`. -/
def frobRayField (f : (Fin L → ℝ) × ℝ → Fin L → ℝ) (q₀ : Fin L → ℝ)
    (X : ℝ × (Fin L → ℝ) × ℝ) : ℝ :=
  (X.2.1 - q₀) ⬝ᵥ f (q₀ + X.1 • (X.2.1 - q₀), X.2.2)

/-- The ray field is `C¹` when `f` is. -/
theorem frobRayField_contDiff {f : (Fin L → ℝ) × ℝ → Fin L → ℝ} (hf : ContDiff ℝ 1 f)
    (q₀ : Fin L → ℝ) : ContDiff ℝ 1 (frobRayField f q₀) := by
  have hin : ContDiff ℝ 1
      (fun X : ℝ × (Fin L → ℝ) × ℝ => (q₀ + X.1 • (X.2.1 - q₀), X.2.2)) := by fun_prop
  have hc := hf.comp hin
  unfold frobRayField dotProduct
  refine ContDiff.sum fun i _ => ContDiff.mul ?_ (contDiff_pi.mp hc i)
  fun_prop

/-- The ray field is bounded by `‖q - q₀‖` when `|v·f| ≤ ‖v‖`. -/
theorem frobRayField_abs_le {f : (Fin L → ℝ) × ℝ → Fin L → ℝ}
    (hbd : ∀ X v, |v ⬝ᵥ f X| ≤ ‖v‖) (q₀ : Fin L → ℝ) (s : ℝ) (q : Fin L → ℝ) (y : ℝ) :
    |frobRayField f q₀ (s, q, y)| ≤ ‖q - q₀‖ :=
  hbd _ _

/-- The derivative of the ray field in the direction `(0, k, u)`:
`k·f(γ, y) + (q - q₀)·D f(γ, y)(s k, u)` with `γ = q₀ + s(q - q₀)`. -/
theorem frobRayField_fderiv_apply {f : (Fin L → ℝ) × ℝ → Fin L → ℝ} (hf : ContDiff ℝ 1 f)
    (q₀ : Fin L → ℝ) (s : ℝ) (q : Fin L → ℝ) (y : ℝ) (k : Fin L → ℝ) (u : ℝ) :
    fderiv ℝ (frobRayField f q₀) (s, q, y) (0, k, u) =
      k ⬝ᵥ f (q₀ + s • (q - q₀), y) +
        (q - q₀) ⬝ᵥ fderiv ℝ f (q₀ + s • (q - q₀), y) (s • k, u) := by
  set ℓ : ℝ → ℝ × (Fin L → ℝ) × ℝ := fun τ => (s, q + τ • k, y + τ * u) with hℓdef
  have hℓ : HasDerivAt ℓ (0, k, u) 0 := by
    refine (hasDerivAt_const _ _).prodMk
      ((?_ : HasDerivAt (fun τ : ℝ => q + τ • k) k 0).prodMk ?_)
    · simpa using ((hasDerivAt_id (0 : ℝ)).smul_const k).const_add q
    · simpa using ((hasDerivAt_id (0 : ℝ)).mul_const u).const_add y
  have hℓ0 : ℓ 0 = (s, q, y) := by simp [hℓdef]
  have h1 := ((frobRayField_contDiff hf q₀).differentiable one_ne_zero
    (ℓ 0)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hℓ
  rw [hℓ0] at h1
  have ha : HasDerivAt (fun τ : ℝ => q + τ • k - q₀) k 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).smul_const k).const_add q).sub_const q₀
  have hp : HasDerivAt (fun τ : ℝ => (q₀ + s • (q + τ • k - q₀), y + τ * u)) (s • k, u) 0 := by
    refine HasDerivAt.prodMk ?_ ?_
    · simpa using (ha.const_smul s).const_add q₀
    · simpa using ((hasDerivAt_id (0 : ℝ)).mul_const u).const_add y
  have hb := ((hf.differentiable one_ne_zero _).hasFDerivAt).comp_hasDerivAt (0 : ℝ) hp
  have h2 := frob_hasDerivAt_dotProduct ha hb
  have h3 := h1.unique h2
  simp only [zero_smul, add_zero, zero_mul, Function.comp_apply] at h3
  exact h3

/-- Global existence along a ray: through every `(t₀, y₀)` the equation
`y' = (q - q₀)·f(q₀ + t(q - q₀), y)` has a solution defined on all of `ℝ`. -/
theorem frob_ray_exists {f : (Fin L → ℝ) × ℝ → Fin L → ℝ} (hf : ContDiff ℝ 1 f)
    (hbd : ∀ X v, |v ⬝ᵥ f X| ≤ ‖v‖) (q₀ q : Fin L → ℝ) (t₀ y₀ : ℝ) :
    ∃ α : ℝ → ℝ, α t₀ = y₀ ∧ ∀ t, HasDerivAt α (frobRayField f q₀ (t, q, α t)) t := by
  set c := ‖q - q₀‖ + 1 with hcdef
  have hc : 0 < c := by positivity
  set V : ℝ → ℝ → ℝ := fun t y => frobRayField f q₀ (t, q, c * y) / c with hVdef
  have hV : ContDiff ℝ 1 (fun z : ℝ × ℝ => V z.1 z.2) :=
    ((frobRayField_contDiff hf q₀).comp
      (by fun_prop : ContDiff ℝ 1 (fun z : ℝ × ℝ => (z.1, q, c * z.2)))).div_const c
  have hb : ∀ t y, |V t y| ≤ 1 := by
    intro t y
    simp only [hVdef, abs_div, abs_of_pos hc]
    rw [div_le_one hc]
    linarith [frobRayField_abs_le hbd q₀ t q (c * y)]
  obtain ⟨β, hβ0, hβ⟩ := hardInt_exists_global hV hb t₀ (y₀ / c)
  refine ⟨fun t => c * β t, by simp only [hβ0]; field_simp, fun t => ?_⟩
  have := (hβ t).const_mul c
  convert this using 1
  simp only [hVdef]
  field_simp

/-- Uniqueness along a ray: two global solutions that agree at one time agree everywhere. -/
theorem frob_ray_unique {f : (Fin L → ℝ) × ℝ → Fin L → ℝ} (hf : ContDiff ℝ 1 f)
    (q₀ q : Fin L → ℝ) {α β : ℝ → ℝ} (hα : ∀ t, HasDerivAt α (frobRayField f q₀ (t, q, α t)) t)
    (hβ : ∀ t, HasDerivAt β (frobRayField f q₀ (t, q, β t)) t) {t₀ : ℝ} (h0 : α t₀ = β t₀) :
    α = β :=
  hardInt_unique (V := fun t y => frobRayField f q₀ (t, q, y))
    ((frobRayField_contDiff hf q₀).comp
      (by fun_prop : ContDiff ℝ 1 (fun z : ℝ × ℝ => (z.1, q, z.2)))) hα hβ h0

/-- Solutions along a ray that are ordered at one time are strictly ordered at every time. -/
theorem frob_ray_strict_order {f : (Fin L → ℝ) × ℝ → Fin L → ℝ} (hf : ContDiff ℝ 1 f)
    (q₀ q : Fin L → ℝ) {α β : ℝ → ℝ} (hα : ∀ t, HasDerivAt α (frobRayField f q₀ (t, q, α t)) t)
    (hβ : ∀ t, HasDerivAt β (frobRayField f q₀ (t, q, β t)) t) {t₀ : ℝ} (h0 : α t₀ < β t₀)
    (t : ℝ) : α t < β t :=
  hardInt_strict_order (V := fun t y => frobRayField f q₀ (t, q, y))
    ((frobRayField_contDiff hf q₀).comp
      (by fun_prop : ContDiff ℝ 1 (fun z : ℝ × ℝ => (z.1, q, z.2)))) hα hβ h0 t

/-- **Frobenius' theorem** (MWG, p. 80), sufficiency, for `∂Z/∂q = f(q, Z)` on `ℝ^L × ℝ`. Let `f`
be `C¹` with `|v·f(q, z)| ≤ ‖v‖` and satisfy the integrability condition
`h·D f(q, z)(v, v·f) = v·D f(q, z)(h, h·f)`. Then for every `q₀` there is a family `Z u` of
solutions on all of `ℝ^L`, `∇Z u (q) = f(q, Z u (q))`, with `Z u (q₀) = u`; at every `q`,
`u ↦ Z u (q)` is strictly increasing, onto `ℝ` and continuous. -/
theorem frobenius_ray_family {f : (Fin L → ℝ) × ℝ → Fin L → ℝ} (hf : ContDiff ℝ 1 f)
    (hbd : ∀ X v, |v ⬝ᵥ f X| ≤ ‖v‖)
    (hsym : ∀ X h v, h ⬝ᵥ fderiv ℝ f X (v, v ⬝ᵥ f X) = v ⬝ᵥ fderiv ℝ f X (h, h ⬝ᵥ f X))
    (q₀ : Fin L → ℝ) :
    ∃ Z : ℝ → (Fin L → ℝ) → ℝ, (∀ u, Z u q₀ = u) ∧
      (∀ u q, HasFDerivAt (Z u) (dualityDotCLM (f (q, Z u q))) q) ∧
      (∀ q, StrictMono fun u => Z u q) ∧ (∀ q z, ∃ u, Z u q = z) ∧
      ∀ q, Continuous fun u => Z u q := by
  choose α hα0 hα using fun q u => frob_ray_exists hf hbd q₀ q 0 u
  have hsm : ∀ q, StrictMono fun u => α q u 1 := fun q u u' huu' =>
    frob_ray_strict_order hf q₀ q (hα q u) (hα q u') (t₀ := 0)
      (by rw [hα0, hα0]; exact huu') 1
  have hsurj : ∀ q z, ∃ u, α q u 1 = z := by
    intro q z
    obtain ⟨β, hβ1, hβ⟩ := frob_ray_exists hf hbd q₀ q 1 z
    refine ⟨β 0, ?_⟩
    rw [frob_ray_unique hf q₀ q (hα q (β 0)) hβ (t₀ := 0) (hα0 q (β 0)), hβ1]
  refine ⟨fun u q => α q u 1, fun u => ?_, fun u q₁ => ?_, hsm, hsurj,
    fun q => (hsm q).monotone.continuous_of_surjective (hsurj q)⟩
  · -- along the trivial ray the solution is constant
    have hconst : ∀ t, HasDerivAt (fun _ : ℝ => u) (frobRayField f q₀ (t, q₀, u)) t := by
      intro t
      simp only [frobRayField, sub_self, zero_dotProduct]
      exact hasDerivAt_const t u
    have := frob_ray_unique hf q₀ q₀ (hα q₀ u) hconst (t₀ := 0) (hα0 q₀ u)
    simp only [this]
  · -- differentiability via the variational equation
    set v := q₁ - q₀ with hv
    set P : ℝ → (Fin L → ℝ) × ℝ := fun s => (q₀ + s • v, α q₁ u s) with hPdef
    set D : ℝ → (Fin L → ℝ) →L[ℝ] ℝ := fun s => s • dualityDotCLM (f (P s)) with hDdef
    have hDk : ∀ s k, D s k = s * (k ⬝ᵥ f (P s)) := fun s k => by
      simp only [hDdef, smul_apply, dualityDotCLM_apply, smul_eq_mul,
        dotProduct_comm]
    have hB : ∀ q ∈ Metric.closedBall q₁ 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
        |α q u s| ≤ |u| + (‖q₁ - q₀‖ + 1) := by
      intro q hq s hs
      have h1 := norm_image_sub_le_of_norm_deriv_le_segment' (f := α q u) (C := ‖q - q₀‖)
        (fun x _ => (hα q u x).hasDerivWithinAt)
        (fun x _ => by rw [Real.norm_eq_abs]; exact frobRayField_abs_le hbd q₀ x q _) s hs
      rw [hα0, Real.norm_eq_abs, sub_zero] at h1
      have h2 : ‖q - q₀‖ ≤ ‖q₁ - q₀‖ + 1 := by
        have := norm_sub_le_norm_sub_add_norm_sub q q₁ q₀
        rw [Metric.mem_closedBall, dist_eq_norm] at hq
        linarith
      have h3 : ‖q - q₀‖ * s ≤ ‖q - q₀‖ := by
        nlinarith [norm_nonneg (q - q₀), hs.1, hs.2]
      have h4 := abs_sub_abs_le_abs_sub (α q u s) u
      linarith
    have hD : ∀ k, ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (fun t => D t k)
        (fderiv ℝ (frobRayField f q₀) (s, q₁, α q₁ u s) (0, k, D s k)) s := by
      intro k s _
      have hP : HasDerivAt P (v, frobRayField f q₀ (s, q₁, α q₁ u s)) s := by
        refine HasDerivAt.prodMk ?_ (hα q₁ u s)
        simpa using ((hasDerivAt_id s).smul_const v).const_add q₀
      have hfP := ((hf.differentiable one_ne_zero (P s)).hasFDerivAt).comp_hasDerivAt s hP
      have hdot := frob_hasDerivAt_dotProduct (hasDerivAt_const s k) hfP
      have hmul := (hasDerivAt_id s).mul hdot
      have hfun : (fun t => D t k) = fun t => id t * (k ⬝ᵥ (f ∘ P) t) := by
        funext t
        rw [hDk]
        rfl
      rw [hfun, frobRayField_fderiv_apply hf, hDk]
      convert hmul using 1
      have hsm2 : (s • k, s * (k ⬝ᵥ f (P s))) = s • (k, k ⬝ᵥ f (P s)) := by
        simp only [Prod.smul_mk, smul_eq_mul]
      have hG : frobRayField f q₀ (s, q₁, α q₁ u s) = v ⬝ᵥ f (P s) := rfl
      rw [hsm2, map_smul, dotProduct_smul, ← hsym (P s) k v, hG]
      simp only [id, Function.comp_apply, zero_dotProduct, zero_add, one_mul, smul_eq_mul]
      rfl
    have hfd := frob_hasFDerivAt_endpoint (frobRayField_contDiff hf q₀) (Y := fun q => α q u)
      (q₁ := q₁) (fun q s _ => hα q u s) (fun q => by rw [hα0, hα0]) hB
      (by simp only [hDdef, zero_smul]) hD
    have hD1 : D 1 = dualityDotCLM (f (q₁, α q₁ u 1)) := by
      simp only [hDdef, hPdef, hv, one_smul, add_sub_cancel]
    rw [hD1] at hfd
    exact hfd

end MWG.ClassicalDemand
