/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGClassicalDemand.FrobeniusTheorem

/-!
# Integrability for `L` goods: existence of solutions of (3.H.2)

MWG, Section 3.H, pp. 79-80. For a demand function `x(p, w)` that is `C¹` on `p ≫ 0, w > 0`,
nonnegative, satisfies Walras' law and has a symmetric Slutsky matrix, the system (3.H.2)
`∂e(p)/∂p_l = x_l(p, e(p))` has a solution through every initial condition `(p⁰, w⁰) ≫ 0`, defined
on all of `p ≫ 0` (`frob_3_H_2_exists`). With a negative semidefinite Slutsky matrix the solutions
rationalize `x` (`integrability_general`): **the integrability theorem for any number of goods,
from primitive hypotheses**. Homogeneity of degree zero is not used (see `docs/corrections-F3.md`).

Method: in logarithmic coordinates `q = log p`, `z = log w` the system becomes
`∂z/∂q_k = f_k(q, z) = p_k x_k(p, w) / w` (`frobLogField`), defined and `C¹` on all of
`ℝ^L × ℝ` (`frobLogField_contDiff`). Walras' law and `x ≥ 0` give `f ≥ 0`, `Σ f_k = 1`, hence
`|v·f| ≤ ‖v‖` (`frobLogField_abs_dot_le`). The derivative of `f` (`frobLogField_fderiv_apply`)
gives `v·D f(h, h·f) = Σ v_k h_k f_k + (p∘v)·S(p, w)(p∘h)/w - (v·f)(h·f)`
(`frobLogField_dot_fderiv`), so symmetry of `S` is exactly the integrability condition of
`frobenius_ray_family` (`frobLogField_symm`). The solutions are `E(p, u) = exp Z_u(log p)`.
-/

namespace MWG.ClassicalDemand

open MWG.ConsumerChoice Kreps.PreferenceProperties Filter Topology

variable {L : ℕ}

/-- Equation (3.H.2) in logarithmic coordinates: `f_k(q, z) = p_k x_k(p, w) / w` with
`p = exp q` (componentwise) and `w = exp z`. -/
noncomputable def frobLogField (x : DemandFunction L) (X : (Fin L → ℝ) × ℝ) : Fin L → ℝ :=
  fun k => Real.exp (X.1 k) * x (fun j => Real.exp (X.1 j)) (Real.exp X.2) k / Real.exp X.2

/-- The Slutsky matrix acting on a vector: `S u = D_p x u + D_w x (x·u)`. -/
theorem frob_slutsky_mulVec (D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)) (xv u : Fin L → ℝ) :
    (slutskyMatrix D xv).mulVec u = D (u, xv ⬝ᵥ u) := by
  rw [← pde_jacobian_eq_slutsky, jacobian_mulVec]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, dualityDotCLM_apply]

/-- The point `(exp q, exp z)` lies in the domain `p ≫ 0, w > 0`. -/
theorem frob_exp_mem_domain (q : Fin L → ℝ) (z : ℝ) :
    ((fun j => Real.exp (q j)), Real.exp z) ∈ demandDomain L :=
  ⟨fun _ => Real.exp_pos _, Real.exp_pos _⟩

/-- If demand is `C¹` on `p ≫ 0, w > 0`, the logarithmic field is `C¹` on `ℝ^L × ℝ`. -/
theorem frobLogField_contDiff {x : DemandFunction L}
    (hx : ContDiffOn ℝ 1 (Function.uncurry x) (demandDomain L)) :
    ContDiff ℝ 1 (frobLogField x) := by
  have hg : ContDiff ℝ 1
      (fun X : (Fin L → ℝ) × ℝ => ((fun j => Real.exp (X.1 j)), Real.exp X.2)) := by
    refine ContDiff.prodMk (contDiff_pi.mpr fun j => ?_) (Real.contDiff_exp.comp contDiff_snd)
    exact Real.contDiff_exp.comp ((contDiff_apply ℝ ℝ j).comp contDiff_fst)
  have hc := hx.comp_contDiff hg fun X => frob_exp_mem_domain X.1 X.2
  refine contDiff_pi.mpr fun k => ?_
  have h0 : ContDiff ℝ 1 (fun X : (Fin L → ℝ) × ℝ =>
      x (fun j => Real.exp (X.1 j)) (Real.exp X.2) k) := contDiff_pi.mp hc k
  exact ((Real.contDiff_exp.comp ((contDiff_apply ℝ ℝ k).comp contDiff_fst)).mul h0).div
    (Real.contDiff_exp.comp contDiff_snd) fun X => (Real.exp_pos _).ne'

/-- By Walras' law and `x ≥ 0`, the logarithmic field satisfies `|v·f(q, z)| ≤ ‖v‖`. -/
theorem frobLogField_abs_dot_le {x : DemandFunction L} (hW : WalrasLaw x)
    (hnn : ∀ q w, StrictlyPositive q → 0 < w → x q w ∈ nonnegOrthant L)
    (X : (Fin L → ℝ) × ℝ) (v : Fin L → ℝ) : |v ⬝ᵥ frobLogField x X| ≤ ‖v‖ := by
  set P : Fin L → ℝ := fun j => Real.exp (X.1 j) with hP
  have hPpos : StrictlyPositive P := fun j => Real.exp_pos _
  have hw := Real.exp_pos X.2
  have hwal := hW P (Real.exp X.2) ⟨hPpos, hw⟩
  have hn := hnn P (Real.exp X.2) hPpos hw
  have hf0 : ∀ k, 0 ≤ frobLogField x X k := fun k =>
    div_nonneg (mul_nonneg (Real.exp_pos _).le (hn k)) hw.le
  have hsum : ∑ k, frobLogField x X k = 1 := by
    simp only [frobLogField, ← Finset.sum_div]
    rw [div_eq_one_iff_eq hw.ne']
    exact hwal
  calc |v ⬝ᵥ frobLogField x X| ≤ ∑ k, |v k * frobLogField x X k| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, ‖v‖ * frobLogField x X k := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [abs_mul, abs_of_nonneg (hf0 k)]
        have := norm_le_pi_norm v k
        rw [Real.norm_eq_abs] at this
        exact mul_le_mul_of_nonneg_right this (hf0 k)
    _ = ‖v‖ := by rw [← Finset.mul_sum, hsum, mul_one]

/-- The derivative of the logarithmic field: with `p = exp q`, `w = exp z`,
`D f(q, z)(h, c)_k = h_k f_k + p_k D x(p, w)(p∘h, w c)_k / w - f_k c`. -/
theorem frobLogField_fderiv_apply {x : DemandFunction L}
    (hx : ContDiffOn ℝ 1 (Function.uncurry x) (demandDomain L)) (q : Fin L → ℝ) (z : ℝ)
    (h : Fin L → ℝ) (c : ℝ) :
    fderiv ℝ (frobLogField x) (q, z) (h, c) = fun k =>
      h k * frobLogField x (q, z) k +
        Real.exp (q k) * fderiv ℝ (Function.uncurry x) ((fun j => Real.exp (q j)), Real.exp z)
          ((fun j => Real.exp (q j) * h j), Real.exp z * c) k / Real.exp z -
        frobLogField x (q, z) k * c := by
  set ℓ : ℝ → (Fin L → ℝ) × ℝ := fun τ => (q + τ • h, z + τ * c) with hℓdef
  have hℓ : HasDerivAt ℓ (h, c) 0 := by
    refine HasDerivAt.prodMk ?_ ?_
    · simpa using ((hasDerivAt_id (0 : ℝ)).smul_const h).const_add q
    · simpa using ((hasDerivAt_id (0 : ℝ)).mul_const c).const_add z
  have hℓ0 : ℓ 0 = (q, z) := by simp [hℓdef]
  have h1 := ((frobLogField_contDiff hx).differentiable one_ne_zero
    (ℓ 0)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hℓ
  rw [hℓ0] at h1
  -- the same derivative computed by hand
  set P : Fin L → ℝ := fun j => Real.exp (q j) with hPdef
  set w := Real.exp z with hwdef
  have hdom : (P, w) ∈ demandDomain L := frob_exp_mem_domain q z
  have hDx : HasFDerivAt (Function.uncurry x) (fderiv ℝ (Function.uncurry x) (P, w)) (P, w) :=
    ((hx.differentiableOn one_ne_zero (P, w) hdom).differentiableAt
      ((isOpen_demandDomain L).mem_nhds hdom)).hasFDerivAt
  have hPτ : HasDerivAt (fun τ : ℝ => fun j => Real.exp (q j + τ * h j))
      (fun j => Real.exp (q j) * h j) 0 := by
    rw [hasDerivAt_pi]
    intro j
    simpa using (((hasDerivAt_id (0 : ℝ)).mul_const (h j)).const_add (q j)).exp
  have hWτ : HasDerivAt (fun τ : ℝ => Real.exp (z + τ * c)) (w * c) 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).mul_const c).const_add z).exp
  have hX := hDx.comp_hasDerivAt_of_eq 0 (hPτ.prodMk hWτ) (by simp [hPdef, hwdef])
  have hman : HasDerivAt (fun τ => frobLogField x (ℓ τ)) (fun k =>
      h k * frobLogField x (q, z) k +
        Real.exp (q k) * fderiv ℝ (Function.uncurry x) (P, w)
          ((fun j => Real.exp (q j) * h j), w * c) k / w -
        frobLogField x (q, z) k * c) 0 := by
    rw [hasDerivAt_pi]
    intro k
    have hEk : HasDerivAt (fun τ : ℝ => Real.exp (q k + τ * h k)) (Real.exp (q k) * h k) 0 := by
      simpa using (((hasDerivAt_id (0 : ℝ)).mul_const (h k)).const_add (q k)).exp
    have hXk := hasDerivAt_pi.mp hX k
    have hq := ((hEk.mul hXk).div hWτ (by simp only [zero_mul, add_zero]; exact
      (Real.exp_pos z).ne'))
    convert hq using 1
    · funext τ
      simp only [frobLogField, hℓdef, Function.comp_apply, Function.uncurry_apply_pair,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.mul_apply, Pi.div_apply]
    · simp only [frobLogField, Function.comp_apply, Function.uncurry_apply_pair, zero_mul,
        add_zero, hPdef, hwdef, Pi.mul_apply]
      field_simp
  exact h1.unique hman

/-- The integrability form of the derivative of the logarithmic field:
`v·D f(h, h·f) = Σ v_k h_k f_k + (p∘v)·S(p, w)(p∘h)/w - (v·f)(h·f)`. -/
theorem frobLogField_dot_fderiv {x : DemandFunction L}
    (hx : ContDiffOn ℝ 1 (Function.uncurry x) (demandDomain L)) (q : Fin L → ℝ) (z : ℝ)
    (h v : Fin L → ℝ) :
    v ⬝ᵥ fderiv ℝ (frobLogField x) (q, z) (h, h ⬝ᵥ frobLogField x (q, z)) =
      ∑ k, v k * h k * frobLogField x (q, z) k +
        (fun j => Real.exp (q j) * v j) ⬝ᵥ
          (slutskyMatrix (fderiv ℝ (Function.uncurry x) ((fun j => Real.exp (q j)), Real.exp z))
            (x (fun j => Real.exp (q j)) (Real.exp z))).mulVec
            (fun j => Real.exp (q j) * h j) / Real.exp z -
        (v ⬝ᵥ frobLogField x (q, z)) * (h ⬝ᵥ frobLogField x (q, z)) := by
  have hw := Real.exp_pos z
  have hc : Real.exp z * (h ⬝ᵥ frobLogField x (q, z)) =
      x (fun j => Real.exp (q j)) (Real.exp z) ⬝ᵥ (fun j => Real.exp (q j) * h j) := by
    simp only [dotProduct, frobLogField, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    field_simp
  rw [frobLogField_fderiv_apply hx, hc, frob_slutsky_mulVec]
  simp only [dotProduct, Finset.sum_div, Finset.sum_mul]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- Symmetry of the Slutsky matrix is the integrability condition of the logarithmic field. -/
theorem frobLogField_symm {x : DemandFunction L}
    (hx : ContDiffOn ℝ 1 (Function.uncurry x) (demandDomain L))
    (hS : ∀ p w, StrictlyPositive p → 0 < w → ∀ i j,
      slutskyMatrix (fderiv ℝ (Function.uncurry x) (p, w)) (x p w) i j =
        slutskyMatrix (fderiv ℝ (Function.uncurry x) (p, w)) (x p w) j i)
    (X : (Fin L → ℝ) × ℝ) (h v : Fin L → ℝ) :
    h ⬝ᵥ fderiv ℝ (frobLogField x) X (v, v ⬝ᵥ frobLogField x X) =
      v ⬝ᵥ fderiv ℝ (frobLogField x) X (h, h ⬝ᵥ frobLogField x X) := by
  obtain ⟨q, z⟩ := X
  rw [frobLogField_dot_fderiv hx, frobLogField_dot_fderiv hx]
  set S := slutskyMatrix (fderiv ℝ (Function.uncurry x) ((fun j => Real.exp (q j)), Real.exp z))
    (x (fun j => Real.exp (q j)) (Real.exp z)) with hSdef
  have hT : S.transpose = S := by
    ext i j
    exact hS _ _ (fun j => Real.exp_pos _) (Real.exp_pos _) j i
  have hmid : ∀ a b : Fin L → ℝ, a ⬝ᵥ S.mulVec b = b ⬝ᵥ S.mulVec a := by
    intro a b
    rw [Matrix.dotProduct_mulVec, ← hT, Matrix.vecMul_transpose, dotProduct_comm, hT]
  rw [hmid]
  have hs : ∑ k, h k * v k * frobLogField x (q, z) k =
      ∑ k, v k * h k * frobLogField x (q, z) k :=
    Finset.sum_congr rfl fun k _ => by ring
  rw [hs]
  ring

/-- The componentwise logarithm has derivative `h ↦ (h_j / p_j)_j` at `p ≫ 0`. -/
theorem frob_hasFDerivAt_log {p : Fin L → ℝ} (hp : StrictlyPositive p) :
    HasFDerivAt (fun q : Fin L → ℝ => fun j => Real.log (q j))
      (ContinuousLinearMap.pi fun j : Fin L =>
        (p j)⁻¹ • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin L => ℝ) j) p :=
  hasFDerivAt_pi.mpr fun j =>
    (Real.hasDerivAt_log (hp j).ne').comp_hasFDerivAt (f := fun q : Fin L → ℝ => q j) p
      (hasFDerivAt_apply (𝕜 := ℝ) j p)

/-- From the logarithmic system back to (3.H.2): if `∇Z(q) = f(q, Z(q))` on `ℝ^L`, then
`E(p) = exp Z(log p)` solves (3.H.2) on `p ≫ 0`. -/
theorem frob_solvesPDE_of_log {x : DemandFunction L} {Z : (Fin L → ℝ) → ℝ}
    (hZ : ∀ q, HasFDerivAt Z (dualityDotCLM (frobLogField x (q, Z q))) q) :
    SolvesPDE x fun p => Real.exp (Z fun j => Real.log (p j)) := by
  intro p hp
  have hd := ((hZ _).comp p (frob_hasFDerivAt_log hp)).exp
  refine hd.congr_fderiv ?_
  ext1 h
  have hel : ∀ j, Real.exp (Real.log (p j)) = p j := fun j => Real.exp_log (hp j)
  simp only [FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.comp_apply,
    dualityDotCLM_apply, ContinuousLinearMap.pi_apply, ContinuousLinearMap.proj_apply,
    frobLogField, hel, smul_eq_mul, dotProduct, Finset.mul_sum, Function.comp_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  have := hp k
  have := Real.exp_pos (Z fun j => Real.log (p j))
  field_simp

/-- **Equation (3.H.2)** (MWG, pp. 79-80): existence of solutions for `L` goods. Let `x(p, w)`
be `C¹` on `p ≫ 0, w > 0`, nonnegative, with Walras' law and a symmetric Slutsky matrix. Then
there is a family `E(·, u)` of positive solutions of (3.H.2) on all of `p ≫ 0`, with
`E(p⁰, u) = exp u`; at every `p ≫ 0`, `u ↦ E(p, u)` is strictly increasing, continuous and onto
`(0, ∞)`. -/
theorem frob_expenditure_family {x : DemandFunction L} (hW : WalrasLaw x)
    (hnn : ∀ q w, StrictlyPositive q → 0 < w → x q w ∈ nonnegOrthant L)
    (hx : ContDiffOn ℝ 1 (Function.uncurry x) (demandDomain L))
    (hS : ∀ p w, StrictlyPositive p → 0 < w → ∀ i j,
      slutskyMatrix (fderiv ℝ (Function.uncurry x) (p, w)) (x p w) i j =
        slutskyMatrix (fderiv ℝ (Function.uncurry x) (p, w)) (x p w) j i)
    (p₀ : Fin L → ℝ) :
    ∃ E : (Fin L → ℝ) → ℝ → ℝ, (∀ u, SolvesPDE x fun q => E q u) ∧
      (∀ q u, 0 < E q u) ∧ (∀ p, StrictMono (E p)) ∧ (∀ p, Continuous (E p)) ∧
      (∀ p w, 0 < w → ∃ u, E p u = w) ∧ ∀ u, E p₀ u = Real.exp u := by
  obtain ⟨Z, hZ0, hZ, hsm, hsurj, hcont⟩ := frobenius_ray_family (frobLogField_contDiff hx)
    (frobLogField_abs_dot_le hW hnn) (frobLogField_symm hx hS) (fun j => Real.log (p₀ j))
  refine ⟨fun p u => Real.exp (Z u fun j => Real.log (p j)),
    fun u => frob_solvesPDE_of_log (hZ u), fun _ _ => Real.exp_pos _,
    fun p => Real.exp_strictMono.comp (hsm _), fun p => Real.continuous_exp.comp (hcont _),
    fun p w hw => ?_, fun u => by simp only [hZ0]⟩
  obtain ⟨u, hu⟩ := hsurj (fun j => Real.log (p j)) (Real.log w)
  exact ⟨u, by simp only [hu, Real.exp_log hw]⟩

/-- **Equation (3.H.2)** (MWG, p. 79), existence through a given initial condition: with the
hypotheses of `frob_expenditure_family`, for every `p⁰` and `w⁰ > 0` there is a solution `e` of
(3.H.2) on all of `p ≫ 0`, positive, with `e(p⁰) = w⁰`. -/
theorem frob_3_H_2_exists {x : DemandFunction L} (hW : WalrasLaw x)
    (hnn : ∀ q w, StrictlyPositive q → 0 < w → x q w ∈ nonnegOrthant L)
    (hx : ContDiffOn ℝ 1 (Function.uncurry x) (demandDomain L))
    (hS : ∀ p w, StrictlyPositive p → 0 < w → ∀ i j,
      slutskyMatrix (fderiv ℝ (Function.uncurry x) (p, w)) (x p w) i j =
        slutskyMatrix (fderiv ℝ (Function.uncurry x) (p, w)) (x p w) j i)
    (p₀ : Fin L → ℝ) {w₀ : ℝ} (hw₀ : 0 < w₀) :
    ∃ e : (Fin L → ℝ) → ℝ, e p₀ = w₀ ∧ (∀ q, 0 < e q) ∧ SolvesPDE x e := by
  obtain ⟨E, hE, hpos, -, -, -, hE0⟩ := frob_expenditure_family hW hnn hx hS p₀
  exact ⟨fun q => E q (Real.log w₀), by simp only [hE0, Real.exp_log hw₀],
    fun q => hpos q _, hE _⟩

/-- **The integrability theorem** (MWG, Section 3.H, p. 80), for any number of goods, from
primitive hypotheses. Let `x(p, w)` be a nonnegative demand function, continuously
differentiable on `p ≫ 0, w > 0`, satisfying Walras' law, with a symmetric and negative
semidefinite Slutsky matrix. Then there is a family `E(·, u)` of solutions of (3.H.2), and the
preference recovered from these expenditure functions rationalizes `x`: its Walrasian demand at
every `(p, w) ≫ 0` is `{x(p, w)}`. -/
theorem integrability_general {x : DemandFunction L} (hW : WalrasLaw x)
    (hnn : ∀ q w, StrictlyPositive q → 0 < w → x q w ∈ nonnegOrthant L)
    (hx : ContDiffOn ℝ 1 (Function.uncurry x) (demandDomain L))
    (hS : ∀ p w, StrictlyPositive p → 0 < w → ∀ i j,
      slutskyMatrix (fderiv ℝ (Function.uncurry x) (p, w)) (x p w) i j =
        slutskyMatrix (fderiv ℝ (Function.uncurry x) (p, w)) (x p w) j i)
    (hnsd : ∀ p w, StrictlyPositive p → 0 < w →
      NegSemidef (slutskyMatrix (fderiv ℝ (Function.uncurry x) (p, w)) (x p w))) :
    ∃ E : (Fin L → ℝ) → ℝ → ℝ, (∀ u, SolvesPDE x fun q => E q u) ∧
      ∀ p w, StrictlyPositive p → 0 < w →
        walrasianDemandPref (recoveredPref E) p w = {x p w} := by
  obtain ⟨E, hE, hpos, hmono, hcont, hsurj, -⟩ :=
    frob_expenditure_family hW hnn hx hS (fun _ => 1)
  refine ⟨E, hE, fun p w hp hw => ?_⟩
  have hD : ∀ q w, StrictlyPositive q → 0 < w → HasFDerivAt (Function.uncurry x)
      (fderiv ℝ (Function.uncurry x) (q, w)) (q, w) := fun q w hq hw =>
    ((hx.differentiableOn one_ne_zero (q, w) ⟨hq, hw⟩).differentiableAt
      ((isOpen_demandDomain L).mem_nhds ⟨hq, hw⟩)).hasFDerivAt
  exact integrability_of_pde hnn hW hD hnsd hE (fun q u _ => hpos q u)
    (fun p _ => hmono p) (fun p _ => hcont p) (fun p _ w hw => hsurj p w hw) hp hw

end MWG.ClassicalDemand
