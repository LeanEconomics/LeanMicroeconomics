/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGClassicalDemand.AppendixMJ
import Mathlib.Analysis.Calculus.LagrangeMultipliers
import Mathlib.Analysis.Calculus.Implicit
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Mathematical Appendix M.K: constrained maximization (equality constraints)

MWG, Section M.K, pp. 956-958. The objective and constraints are functions on `ℝ^N`; the
equality-constrained problem (M.K.1) is `max f(x)` subject to `g_m(x) = b̄_m`, `m = 1, ..., M`.

* The constraint set and local constrained maximizers (Mathlib's `IsLocalMaxOn`).
* Theorem M.K.1 (Lagrange): at a local constrained maximizer where the constraint gradients
  are linearly independent (the constraint qualification, rank `M`), `∇f(x̄) = ∑ λ_m ∇g_m(x̄)`.
  We assume strict differentiability at `x̄` (implied by continuous differentiability), as
  Mathlib's Lagrange multiplier theorem does; the book assumes differentiability only, and the
  merely-differentiable case (Halkin 1974) is left open.
* Figure M.K.1: the constraint qualification is indispensable.
* The Lagrangian and its first-order conditions (p. 958).
-/

namespace MWG.ClassicalDemand

open Filter Topology MWG.ConsumerChoice

variable {N M : ℕ}

/-- **Section M.K** (MWG, p. 956). The constraint set `C = {x : g_m(x) = b̄_m, m = 1..M}`. -/
def eqConstraintSet (g : Fin M → (Fin N → ℝ) → ℝ) (b : Fin M → ℝ) : Set (Fin N → ℝ) :=
  {x | ∀ m, g m x = b m}

/-- **Section M.K** (MWG, p. 956). `x̄ ∈ C` is a local constrained maximizer iff there is an
open neighborhood `A` of `x̄` with `f(x̄) ≥ f(x)` for all `x ∈ A ∩ C` (Mathlib's
`IsLocalMaxOn`). -/
theorem local_constrained_maximizer_iff (f : (Fin N → ℝ) → ℝ) (C : Set (Fin N → ℝ))
    (x : Fin N → ℝ) :
    IsLocalMaxOn f C x ↔ ∃ A : Set (Fin N → ℝ), IsOpen A ∧ x ∈ A ∧ ∀ y ∈ A ∩ C, f y ≤ f x := by
  constructor
  · intro h
    obtain ⟨A, hAo, hxA, hAC⟩ := mem_nhdsWithin.mp h
    exact ⟨A, hAo, hxA, fun y hy => hAC hy⟩
  · rintro ⟨A, hAo, hxA, h⟩
    exact mem_nhdsWithin.mpr ⟨A, hAo, hxA, fun y hy => h y hy⟩

/-- **Theorem M.K.1** (MWG, p. 956), Lagrange multipliers. Let `x̄ ∈ C` be a local constrained
maximizer of (M.K.1) where `f` and all `g_m` are strictly differentiable, and suppose the
constraint qualification holds: the derivatives `∇g_m(x̄)` are linearly independent. Then
there are multipliers `λ_m` with `∇f(x̄) = ∑ λ_m ∇g_m(x̄)` (M.K.3). -/
theorem theorem_M_K_1 {f : (Fin N → ℝ) → ℝ} {f' : (Fin N → ℝ) →L[ℝ] ℝ}
    {g : Fin M → (Fin N → ℝ) → ℝ} {g' : Fin M → (Fin N → ℝ) →L[ℝ] ℝ} {b : Fin M → ℝ}
    {x : Fin N → ℝ} (hx : x ∈ eqConstraintSet g b) (hmax : IsLocalMaxOn f (eqConstraintSet g b) x)
    (hf : HasStrictFDerivAt f f' x) (hg : ∀ m, HasStrictFDerivAt (g m) (g' m) x)
    (hCQ : LinearIndependent ℝ g') : ∃ lam : Fin M → ℝ, f' = ∑ m, lam m • g' m := by
  have hset : eqConstraintSet g b = {y | ∀ m, g m y = g m x} := by
    ext y
    simp only [eqConstraintSet, Set.mem_ofPred_eq, hx _]
  rw [hset] at hmax
  obtain ⟨Λ, Λ₀, hne, hsum⟩ :=
    IsLocalExtrOn.exists_multipliers_of_hasStrictFDerivAt (Or.inr hmax) hg hf
  have hΛ₀ : Λ₀ ≠ 0 := by
    intro h0
    rw [h0, zero_smul, add_zero] at hsum
    have hΛ : Λ = 0 := funext fun m =>
      (Fintype.linearIndependent_iff.mp hCQ) Λ hsum m
    exact hne (by rw [hΛ, h0]; rfl)
  refine ⟨fun m => -(Λ m / Λ₀), ?_⟩
  have : Λ₀ • f' = -∑ m, Λ m • g' m := eq_neg_of_add_eq_zero_right hsum
  have hf' : f' = Λ₀⁻¹ • -∑ m, Λ m • g' m := by
    rw [← this, smul_smul, inv_mul_cancel₀ hΛ₀, one_smul]
  rw [hf', smul_neg, Finset.smul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [smul_smul]
  change _ = (-(Λ m / Λ₀)) • g' m
  rw [div_eq_inv_mul]
  exact (neg_smul _ _).symm

/-- **Equation (M.K.2)** (MWG, p. 956). In partial derivatives:
`∂f(x̄)/∂x_n = ∑ λ_m ∂g_m(x̄)/∂x_n` for every `n`. -/
theorem equation_M_K_2 {f' : (Fin N → ℝ) →L[ℝ] ℝ} {g' : Fin M → (Fin N → ℝ) →L[ℝ] ℝ}
    {lam : Fin M → ℝ} (h : f' = ∑ m, lam m • g' m) (n : Fin N) :
    gradientVec f' n = ∑ m, lam m * gradientVec (g' m) n := by
  simp [gradientVec, h]

/-- **Figure M.K.1** (MWG, p. 957). The constraint qualification is indispensable. With
`g₁(x) = x₂ - x₁²`, `g₂(x) = -x₂ - x₁²` and `b̄ = 0`, the constraint set is `{0}`, so `0` is a
global constrained maximizer of the linear `f(x) = x₁`; but `∇g₁(0) = -∇g₂(0)` and `∇f(0)` is
not a combination of the constraint gradients. -/
theorem figure_M_K_1 :
    eqConstraintSet ![fun x : Fin 2 → ℝ => x 1 - x 0 * x 0, fun x => -x 1 - x 0 * x 0] 0 =
        {0} ∧
      HasStrictFDerivAt (fun x : Fin 2 → ℝ => x 1 - x 0 * x 0)
        (ContinuousLinearMap.proj 1 : (Fin 2 → ℝ) →L[ℝ] ℝ) 0 ∧
      HasStrictFDerivAt (fun x : Fin 2 → ℝ => -x 1 - x 0 * x 0)
        (-ContinuousLinearMap.proj 1 : (Fin 2 → ℝ) →L[ℝ] ℝ) 0 ∧
      HasStrictFDerivAt (fun x : Fin 2 → ℝ => x 0)
        (ContinuousLinearMap.proj 0 : (Fin 2 → ℝ) →L[ℝ] ℝ) 0 ∧
      ¬ ∃ lam : Fin 2 → ℝ, (ContinuousLinearMap.proj 0 : (Fin 2 → ℝ) →L[ℝ] ℝ) =
        lam 0 • (ContinuousLinearMap.proj 1 : (Fin 2 → ℝ) →L[ℝ] ℝ) +
          lam 1 • -(ContinuousLinearMap.proj 1 : (Fin 2 → ℝ) →L[ℝ] ℝ) := by
  have h0 := hasStrictFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) (0 : Fin 2 → ℝ)
  have h1 := hasStrictFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) (0 : Fin 2 → ℝ)
  refine ⟨?_, ?_, ?_, h0, ?_⟩
  · ext x
    simp only [eqConstraintSet, Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Pi.zero_apply, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨e1, e2⟩
      have hx0 : x 0 = 0 := by nlinarith [mul_self_nonneg (x 0)]
      have hx1 : x 1 = 0 := by rw [hx0] at e1; linarith
      funext i
      fin_cases i
      · exact hx0
      · exact hx1
    · rintro rfl
      simp
  · refine HasStrictFDerivAt.congr_fderiv (h1.sub (h0.mul h0)) ?_
    ext v
    simp
  · refine HasStrictFDerivAt.congr_fderiv (h1.neg.sub (h0.mul h0)) ?_
    ext v
    simp
  · rintro ⟨lam, hlam⟩
    have := congrArg (fun φ : (Fin 2 → ℝ) →L[ℝ] ℝ => φ (Pi.single 0 1)) hlam
    simp at this

/-- **Section M.K** (MWG, p. 958). The Lagrangian `L(x, λ) = f(x) - ∑ λ_m (g_m(x) - b̄_m)`. -/
def lagrangian (f : (Fin N → ℝ) → ℝ) (g : Fin M → (Fin N → ℝ) → ℝ) (b : Fin M → ℝ)
    (x : Fin N → ℝ) (lam : Fin M → ℝ) : ℝ :=
  f x - ∑ m, lam m * (g m x - b m)

/-- **Section M.K** (MWG, p. 958). The first-order conditions (M.K.3) are the stationarity of
the Lagrangian in `x`: its derivative in `x` at `x̄` is `∇f(x̄) - ∑ λ_m ∇g_m(x̄)`. -/
theorem lagrangian_hasFDerivAt_x {f : (Fin N → ℝ) → ℝ} {f' : (Fin N → ℝ) →L[ℝ] ℝ}
    {g : Fin M → (Fin N → ℝ) → ℝ} {g' : Fin M → (Fin N → ℝ) →L[ℝ] ℝ} (b : Fin M → ℝ)
    {x : Fin N → ℝ} (hf : HasFDerivAt f f' x) (hg : ∀ m, HasFDerivAt (g m) (g' m) x)
    (lam : Fin M → ℝ) :
    HasFDerivAt (fun y => lagrangian f g b y lam) (f' - ∑ m, lam m • g' m) x := by
  unfold lagrangian
  refine hf.sub ?_
  have := HasFDerivAt.fun_sum (u := Finset.univ) fun m _ =>
    ((hg m).sub_const (b m)).const_mul (lam m)
  simpa using this

/-- **Section M.K** (MWG, p. 958). The derivative of the Lagrangian in `λ_m` is
`-(g_m(x) - b̄_m)`, so its stationarity in `λ` is the constraint `g_m(x) = b̄_m`. -/
theorem lagrangian_hasDerivAt_lam (f : (Fin N → ℝ) → ℝ) (g : Fin M → (Fin N → ℝ) → ℝ)
    (b : Fin M → ℝ) (x : Fin N → ℝ) (lam : Fin M → ℝ) (m : Fin M) :
    HasDerivAt (fun t : ℝ => lagrangian f g b x (Function.update lam m t))
      (-(g m x - b m)) (lam m) := by
  unfold lagrangian
  have hsplit : ∀ t : ℝ, ∑ k, Function.update lam m t k * (g k x - b k) =
      t * (g m x - b m) + ∑ k ∈ Finset.univ.erase m, lam k * (g k x - b k) := by
    intro t
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ m), Function.update_self]
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  simp_rw [hsplit]
  have := ((hasDerivAt_id (lam m)).mul_const (g m x - b m)).add_const
    (∑ k ∈ Finset.univ.erase m, lam k * (g k x - b k))
  have := this.const_sub (f x)
  simpa using this

/-- **Section M.K** (MWG, p. 958). All partial derivatives of the Lagrangian vanish at
`(x̄, λ)` iff (M.K.3) and the constraints hold. -/
theorem lagrangian_stationary_iff {f' : (Fin N → ℝ) →L[ℝ] ℝ}
    {g : Fin M → (Fin N → ℝ) → ℝ} {g' : Fin M → (Fin N → ℝ) →L[ℝ] ℝ} {b : Fin M → ℝ}
    {x : Fin N → ℝ} {lam : Fin M → ℝ} :
    (f' - ∑ m, lam m • g' m = 0 ∧ ∀ m, -(g m x - b m) = 0) ↔
      (f' = ∑ m, lam m • g' m ∧ x ∈ eqConstraintSet g b) := by
  simp only [sub_eq_zero, neg_eq_zero, eqConstraintSet, Set.mem_ofPred_eq]

/-- Linearly independent functionals give a surjective joint map `x ↦ (φ_i(x))_i`. -/
theorem mk_range_pi_eq_top {ι : Type*} [Finite ι]
    {φ : ι → (Fin N → ℝ) →L[ℝ] ℝ} (hφ : LinearIndependent ℝ φ) :
    (ContinuousLinearMap.pi φ).range = ⊤ := by
  classical
  have := Fintype.ofFinite ι
  by_contra hne
  obtain ⟨ψ, hψ, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
  have hdecomp : ∀ y : ι → ℝ, ψ y = ∑ i, y i * ψ (Pi.single i 1) := by
    intro y
    conv_lhs => rw [← Finset.univ_sum_single y]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← smul_eq_mul, ← map_smul, ← Pi.single_smul, smul_eq_mul, mul_one]
  have hcomb : ∑ i, ψ (Pi.single i 1) • φ i = 0 := by
    ext v
    have := hle ⟨v, rfl⟩
    rw [LinearMap.mem_ker, hdecomp] at this
    simpa [mul_comm] using this
  have hzero := (Fintype.linearIndependent_iff.mp hφ) _ hcomb
  apply hψ
  refine LinearMap.ext fun y => ?_
  rw [hdecomp]
  simp [hzero]

/-- **Lemma for Theorem M.K.2.** If `Φ : ℝ^N → ℝ^ι` is strictly differentiable at `a` with
surjective derivative, then for every direction `z` there is a curve `X` through `a` with
velocity `z` along which `Φ` moves exactly linearly: `Φ(X(s)) = Φ(a) + T(s)·DΦ(a)z` near
`s = 0`, with `T(0) = 0` and `T'(0) = 1` (implicit function theorem). -/
theorem mk_curve {ι : Type*} [Finite ι] {Φ : (Fin N → ℝ) → ι → ℝ}
    {Φ' : (Fin N → ℝ) →L[ℝ] (ι → ℝ)} {a : Fin N → ℝ} (hΦ : HasStrictFDerivAt Φ Φ' a)
    (hsurj : Φ'.range = ⊤) (z : Fin N → ℝ) :
    ∃ X : ℝ → Fin N → ℝ, ∃ T : ℝ → ℝ, X 0 = a ∧ T 0 = 0 ∧ HasDerivAt X z 0 ∧
      HasDerivAt T 1 0 ∧ ∀ᶠ s in 𝓝 (0 : ℝ), Φ (X s) = Φ a + T s • Φ' z := by
  have := Fintype.ofFinite ι
  set w := Φ' z with hw
  set Ψ : (Fin N → ℝ) × ℝ → ι → ℝ := fun p => Φ p.1 - p.2 • w with hΨdef
  set Ψ' : ((Fin N → ℝ) × ℝ) →L[ℝ] (ι → ℝ) :=
    Φ'.comp (ContinuousLinearMap.fst ℝ _ _) - (ContinuousLinearMap.snd ℝ _ _).smulRight w
    with hΨ'def
  have hΨ : HasStrictFDerivAt Ψ Ψ' (a, 0) := by
    have h1 : HasStrictFDerivAt (fun p : (Fin N → ℝ) × ℝ => Φ p.1)
        (Φ'.comp (ContinuousLinearMap.fst ℝ _ _)) (a, 0) :=
      hΦ.comp (a, 0) hasStrictFDerivAt_fst
    have h2 : HasStrictFDerivAt (fun p : (Fin N → ℝ) × ℝ => p.2 • w)
        ((ContinuousLinearMap.snd ℝ _ _).smulRight w) (a, 0) :=
      hasStrictFDerivAt_snd.smul_const w
    exact h1.sub h2
  have hrange : Ψ'.range = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro y
    obtain ⟨v, hv⟩ := LinearMap.range_eq_top.mp hsurj y
    refine ⟨(v, 0), ?_⟩
    change Φ' v - (0 : ℝ) • w = y
    rw [zero_smul, sub_zero]
    exact hv
  have hker : ((z, 1) : (Fin N → ℝ) × ℝ) ∈ Ψ'.ker := by
    simp [hΨ'def, hw]
  set kz : Ψ'.ker := ⟨(z, 1), hker⟩ with hkz
  set κ : ℝ → (Fin N → ℝ) × ℝ := fun s => hΨ.implicitFunction Ψ Ψ' hrange (Ψ (a, 0)) (s • kz)
    with hκ
  have hκd : HasDerivAt κ (z, 1) 0 := by
    have hinner : HasDerivAt (fun s : ℝ => s • kz) kz 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const kz
    have houter := (hΨ.to_implicitFunction hrange).hasFDerivAt
    have hzero : (0 : ℝ) • kz = 0 := zero_smul _ _
    rw [← hzero] at houter
    exact houter.comp_hasDerivAt (0 : ℝ) hinner
  have hκ0 : κ 0 = (a, 0) := by
    simp only [hκ, zero_smul]
    exact hΨ.implicitFunction_apply_image hrange
  have hev : ∀ᶠ s in 𝓝 (0 : ℝ), Ψ (κ s) = Ψ (a, 0) := by
    have hmap := hΨ.map_implicitFunction_eq hrange
    have ht : Tendsto (fun s : ℝ => (Ψ (a, 0), s • kz)) (𝓝 0) (𝓝 (Ψ (a, 0), 0)) := by
      refine tendsto_const_nhds.prodMk_nhds ?_
      have : Continuous (fun s : ℝ => s • kz) := continuous_id.smul continuous_const
      simpa using this.tendsto 0
    exact ht.eventually hmap
  refine ⟨fun s => (κ s).1, fun s => (κ s).2, by simp only [hκ0], by simp only [hκ0], ?_, ?_, ?_⟩
  · exact (hasFDerivAt_fst (𝕜 := ℝ) (p := κ 0)).comp_hasDerivAt (0 : ℝ) hκd
  · exact (hasFDerivAt_snd (𝕜 := ℝ) (p := κ 0)).comp_hasDerivAt (0 : ℝ) hκd
  · filter_upwards [hev] with s hs
    simp only [hΨdef, zero_smul, sub_zero] at hs
    rw [← hs]
    abel

/-- **Section M.K** (MWG, p. 958). The constraint set of problem (M.K.4):
`g_m(x) = b̄_m` for all `m` and `h_k(x) ≤ c̄_k` for all `k`. -/
def kktConstraintSet {K : ℕ} (g : Fin M → (Fin N → ℝ) → ℝ) (b : Fin M → ℝ)
    (h : Fin K → (Fin N → ℝ) → ℝ) (c : Fin K → ℝ) : Set (Fin N → ℝ) :=
  {x | (∀ m, g m x = b m) ∧ ∀ k, h k x ≤ c k}

/-- A strictly positive right derivative at `0` makes the function exceed its value at `0` for
all small `s > 0`. -/
theorem mk_eventually_gt_of_deriv_pos {φ : ℝ → ℝ} {d : ℝ} (hφ : HasDerivAt φ d 0)
    (hd : 0 < d) : ∀ᶠ s in 𝓝[>] (0 : ℝ), φ 0 < φ s := by
  filter_upwards [hφ.tendsto_slope_zero_right.eventually (lt_mem_nhds hd), self_mem_nhdsWithin]
    with s hs hs0
  rw [zero_add, smul_eq_mul] at hs
  have := (mul_pos_iff_of_pos_left (inv_pos.mpr hs0)).mp hs
  linarith

/-- **Theorem M.K.2** (MWG, p. 959), the Kuhn-Tucker conditions. Let `x̄ ∈ C` be a local
constrained maximizer of problem (M.K.4), with `f`, every `g_m` and every `h_k` strictly
differentiable at `x̄`, and suppose the constraint qualification holds: the gradients of the
equality constraints and of the binding inequality constraints are linearly independent. Then
there are `λ_m ∈ ℝ` and `λ_k ≥ 0` with `∇f(x̄) = ∑ λ_m ∇g_m(x̄) + ∑ λ_k ∇h_k(x̄)` (M.K.6) and
`λ_k (h_k(x̄) - c̄_k) = 0` (M.K.7). The book proves only the case `M = 0` and assumes that the
constraint qualification makes `x̄` a maximizer of the linearized problem; here that step is
proved with the implicit function theorem (`mk_curve`). -/
theorem theorem_M_K_2 {K : ℕ} {f : (Fin N → ℝ) → ℝ} {f' : (Fin N → ℝ) →L[ℝ] ℝ}
    {g : Fin M → (Fin N → ℝ) → ℝ} {g' : Fin M → (Fin N → ℝ) →L[ℝ] ℝ} {b : Fin M → ℝ}
    {h : Fin K → (Fin N → ℝ) → ℝ} {h' : Fin K → (Fin N → ℝ) →L[ℝ] ℝ} {c : Fin K → ℝ}
    {x : Fin N → ℝ} (hx : x ∈ kktConstraintSet g b h c)
    (hmax : IsLocalMaxOn f (kktConstraintSet g b h c) x) (hf : HasStrictFDerivAt f f' x)
    (hg : ∀ m, HasStrictFDerivAt (g m) (g' m) x) (hh : ∀ k, HasStrictFDerivAt (h k) (h' k) x)
    (hCQ : LinearIndependent ℝ (Sum.elim g' fun k : {k // h k x = c k} => h' k.1)) :
    ∃ lam : Fin M → ℝ, ∃ mu : Fin K → ℝ, (∀ k, 0 ≤ mu k) ∧
      f' = ∑ m, lam m • g' m + ∑ k, mu k • h' k ∧ ∀ k, mu k * (h k x - c k) = 0 := by
  classical
  set ι := Fin M ⊕ {k // h k x = c k}
  set φ : ι → (Fin N → ℝ) →L[ℝ] ℝ := Sum.elim g' fun k => h' k.1 with hφ
  set F : ι → (Fin N → ℝ) → ℝ := Sum.elim g fun k => h k.1 with hF
  have hFd : ∀ i, HasStrictFDerivAt (F i) (φ i) x := by
    rintro (m | k)
    · exact hg m
    · exact hh k.1
  -- inactive constraints stay slack near `x̄`
  have hslack : ∀ᶠ y in 𝓝 x, ∀ k, h k x < c k → h k y < c k := by
    rw [eventually_all]
    intro k
    by_cases hk : h k x < c k
    · exact ((hh k).continuousAt.eventually (gt_mem_nhds hk)).mono fun y hy _ => hy
    · exact Eventually.of_forall fun y hk' => absurd hk' hk
  -- membership of points that solve the active constraints
  have hmemC : ∀ y, (∀ m, g m y = b m) → (∀ k : {k // h k x = c k}, h k.1 y ≤ c k.1) →
      (∀ k, h k x < c k → h k y < c k) → y ∈ kktConstraintSet g b h c := by
    intro y hgy hay hiy
    refine ⟨hgy, fun k => ?_⟩
    rcases (hx.2 k).lt_or_eq with hk | hk
    · exact (hiy k hk).le
    · exact hay ⟨k, hk⟩
  -- Step 1: `x̄` is a local maximizer on the active-equality set; Lagrange multipliers
  have hloc : IsLocalMaxOn f {y | ∀ i, F i y = F i x} x := by
    obtain ⟨U, hUo, hxU, hUC⟩ := mem_nhdsWithin.mp hmax
    obtain ⟨V, hV, hVs⟩ := hslack.exists_mem
    refine mem_nhdsWithin.mpr ⟨interior (U ∩ V), isOpen_interior, ?_, fun y hy => ?_⟩
    · exact mem_interior_iff_mem_nhds.mpr (inter_mem (hUo.mem_nhds hxU) hV)
    · have hyUV := interior_subset hy.1
      apply hUC
      refine ⟨hyUV.1, hmemC y (fun m => ?_) (fun k => ?_) (hVs y hyUV.2)⟩
      · have := hy.2 (Sum.inl m)
        simp only [hF, Sum.elim_inl] at this
        rw [this, hx.1 m]
      · have := hy.2 (Sum.inr k)
        simp only [hF, Sum.elim_inr] at this
        rw [this, k.2]
  obtain ⟨Λ, Λ₀, hne, hsum⟩ :=
    IsLocalExtrOn.exists_multipliers_of_hasStrictFDerivAt (Or.inr hloc) hFd hf
  have hΛ₀ : Λ₀ ≠ 0 := by
    intro h0
    rw [h0, zero_smul, add_zero] at hsum
    have hΛ : Λ = 0 := funext fun i => (Fintype.linearIndependent_iff.mp hCQ) Λ hsum i
    exact hne (by rw [hΛ, h0]; rfl)
  set ν : ι → ℝ := fun i => -(Λ i / Λ₀) with hν
  have hfν : f' = ∑ i, ν i • φ i := by
    have h1 : Λ₀ • f' = -∑ i, Λ i • φ i := eq_neg_of_add_eq_zero_right hsum
    have h2 : f' = Λ₀⁻¹ • -∑ i, Λ i • φ i := by
      rw [← h1, smul_smul, inv_mul_cancel₀ hΛ₀, one_smul]
    rw [h2, smul_neg, Finset.smul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul]
    change _ = (-(Λ i / Λ₀)) • φ i
    rw [div_eq_inv_mul]
    exact (neg_smul _ _).symm
  set lam : Fin M → ℝ := fun m => ν (Sum.inl m) with hlam
  set mu : Fin K → ℝ := fun k => if hk : h k x = c k then ν (Sum.inr ⟨k, hk⟩) else 0 with hmu
  have hmu_sum : ∑ k, mu k • h' k = ∑ k : {k // h k x = c k}, ν (Sum.inr k) • h' k.1 := by
    rw [← Finset.sum_filter_of_ne (p := fun k => h k x = c k) (fun k _ hk => by
      by_contra hc
      simp [hmu, hc] at hk)]
    rw [Finset.sum_subtype (p := fun k => h k x = c k) (Finset.univ.filter fun k => h k x = c k)
      (fun k => by simp)]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [hmu, k.2]
  have hsplit : f' = ∑ m, lam m • g' m + ∑ k, mu k • h' k := by
    rw [hfν, Fintype.sum_sum_type, hmu_sum]
    rfl
  -- Step 2: signs of the inequality multipliers
  have hsurj := mk_range_pi_eq_top hCQ
  have hΦ : HasStrictFDerivAt (fun y i => F i y) (ContinuousLinearMap.pi φ) x :=
    hasStrictFDerivAt_pi.mpr hFd
  have hsign : ∀ k (hk : h k x = c k), 0 ≤ ν (Sum.inr ⟨k, hk⟩) := by
    intro k hk
    by_contra hneg
    push Not at hneg
    set j : ι := Sum.inr ⟨k, hk⟩ with hj
    obtain ⟨z, hz⟩ := LinearMap.range_eq_top.mp hsurj (Pi.single j (-1))
    have hzi : ∀ i, φ i z = (Pi.single j (-1 : ℝ) : ι → ℝ) i := fun i => congrFun hz i
    have hfz : 0 < f' z := by
      rw [hfν]
      simp only [FunLike.coe_sum, Finset.sum_apply,
        FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, hzi]
      rw [Finset.sum_eq_single j (fun i _ hij => by simp [hij])
        (fun hj' => absurd (Finset.mem_univ j) hj')]
      simp only [Pi.single_eq_same]
      linarith
    obtain ⟨X, T, hX0, hT0, hXd, hTd, hXΦ⟩ := mk_curve hΦ hsurj z
    have hXc : Tendsto X (𝓝[>] (0 : ℝ)) (𝓝 x) := by
      have := hXd.continuousAt.tendsto
      rw [hX0] at this
      exact this.mono_left nhdsWithin_le_nhds
    have hTpos := mk_eventually_gt_of_deriv_pos hTd one_pos
    have hfX : HasFDerivAt f f' (X 0) := by rw [hX0]; exact hf.hasFDerivAt
    have hfpos := mk_eventually_gt_of_deriv_pos
      (hfX.comp_hasDerivAt 0 hXd : HasDerivAt (f ∘ X) (f' z) 0) hfz
    -- feasibility of the curve
    have hfeas : ∀ᶠ s in 𝓝[>] (0 : ℝ), X s ∈ kktConstraintSet g b h c := by
      filter_upwards [hTpos, (hXΦ.filter_mono nhdsWithin_le_nhds), hXc.eventually hslack]
        with s hTs hΦs hsl
      rw [hT0] at hTs
      refine hmemC (X s) (fun m => ?_) (fun k' => ?_) hsl
      · have := congrFun hΦs (Sum.inl m)
        simp only [hF, Sum.elim_inl, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          ContinuousLinearMap.pi_apply] at this
        rw [this, hzi, Pi.single_eq_of_ne (by simp [hj]), mul_zero, add_zero, hx.1 m]
      · have := congrFun hΦs (Sum.inr k')
        simp only [hF, Sum.elim_inr, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          ContinuousLinearMap.pi_apply] at this
        rw [this, hzi, k'.2]
        rw [Pi.single_apply]
        split_ifs <;> nlinarith
    have hmaxc : ∀ᶠ s in 𝓝[>] (0 : ℝ), f (X s) ≤ f x := by
      have hin : Tendsto X (𝓝[>] (0 : ℝ)) (𝓝[kktConstraintSet g b h c] x) :=
        tendsto_nhdsWithin_iff.mpr ⟨hXc, hfeas⟩
      exact hin.eventually hmax
    obtain ⟨s, hs1, hs2⟩ := (hfpos.and hmaxc).exists
    simp only [Function.comp_apply, hX0] at hs1
    linarith
  refine ⟨lam, mu, fun k => ?_, hsplit, fun k => ?_⟩
  · simp only [hmu]
    split_ifs with hk
    · exact hsign k hk
    · exact le_rfl
  · simp only [hmu]
    split_ifs with hk
    · rw [hk, sub_self, mul_zero]
    · rw [zero_mul]

end MWG.ClassicalDemand
