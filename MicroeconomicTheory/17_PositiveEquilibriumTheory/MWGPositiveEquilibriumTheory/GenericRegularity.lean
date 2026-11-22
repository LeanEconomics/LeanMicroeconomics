/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPositiveEquilibriumTheory.CobbDouglasEconomy
import MWGClassicalDemand.HardSard
import Mathlib.Analysis.Calculus.Implicit

/-!
# Genericity analysis: transversality and generic regularity (MWG Section 17.D, pp. 593-597)

* **Definition 17.D.3** (`RegularEqSystem`): `f(v) = 0` (`M` equations, `N` unknowns) is regular
  if `rank Df(v) = M` (i.e. `Df(v)` is onto `ℝ^M`) whenever `f(v) = 0`.
* **Proposition 17.D.3 (transversality theorem)**, for `M = N` (`proposition_17_D_3`, a bridge
  to Chapter 3's `theorem_M_E_2`, Sard in equal dimension) and for `M > N`
  (`proposition_17_D_3_over`: generically the system has no solution, by padding the unknowns
  and applying the square case). The case `M < N` is OPEN (it needs Sard's theorem for `C^k`
  maps from higher to lower dimension, not in Mathlib).
* **Exercise 17.D.2** (`exercise_17_D_2`): near a regular solution the solution set is
  parametrized by `N - M` parameters (Mathlib's implicit function theorem for maps with onto
  derivative).
* **Proposition 17.D.4** (`proposition_17_D_4`): `rank D_ω ẑ(p; ω) = L - 1`. A perturbation
  `dω₁` of consumer 1's endowment with `p·dω₁ = 0` leaves his wealth, hence demand, unchanged and
  moves excess demand by exactly `-dω₁` (`genSystem_shift`); **Exercise 17.D.3**
  (`exercise_17_D_3`) carries out the computation `D_{ω₁}ẑ = D_w x̂₁ pᵀ - [I | 0]`.
* **Proposition 17.D.5 (Debreu)** (`proposition_17_D_5`): if every consumer's demand `xᵢ(p, w)`
  is `C¹` on `{p ≫ 0} × (0, ∞)`, then the set of endowment vectors `ω ∈ ℝ^{LI}_{++}` for which
  the economy is not regular has Lebesgue measure zero (footnote 21). Instance: Cobb-Douglas
  economies (`proposition_17_D_5_cobbDouglas`), whose excess demand is the chapter's
  `excessDemand` of the exchange economy.

The endowment vector is `ω = (ω₁₁, …, ω_{L1}, …, ω_{LI}) ∈ ℝ^{LI}`, consumer `i`'s endowment
being `endowOf ω i` (coordinates `finProdFinEquiv (i, ℓ)`).
-/

namespace MWG.PositiveEquilibriumTheory

open Filter Topology MeasureTheory MWG.ClassicalDemand

/-! ### Definition 17.D.3 and the transversality theorem -/

/-- **Definition 17.D.3** (MWG, p. 594). The system of `M` equations in `N` unknowns `f(v) = 0` is
regular if `rank Df(v) = M` (`Df(v)` is onto `ℝ^M`) whenever `f(v) = 0`. -/
def RegularEqSystem {N M : ℕ} (f : (Fin N → ℝ) → Fin M → ℝ) : Prop :=
  ∀ v, f v = 0 → (fderiv ℝ f v).range = ⊤

/-- **Section 17.D** (MWG, p. 594). If `M > N`, `rank Df(v) ≤ N < M`, so the system is regular iff
it has no solution. -/
theorem regularEqSystem_iff_of_lt {N M : ℕ} (h : N < M) (f : (Fin N → ℝ) → Fin M → ℝ) :
    RegularEqSystem f ↔ ∀ v, f v ≠ 0 := by
  constructor
  · intro hreg v hv
    have hr := hreg v hv
    have h1 := LinearMap.finrank_range_le (fderiv ℝ f v : (Fin N → ℝ) →ₗ[ℝ] (Fin M → ℝ))
    have h2 : Module.finrank ℝ (LinearMap.range
        (fderiv ℝ f v : (Fin N → ℝ) →ₗ[ℝ] (Fin M → ℝ))) = M := by
      rw [show LinearMap.range (fderiv ℝ f v : (Fin N → ℝ) →ₗ[ℝ] (Fin M → ℝ)) = ⊤ from hr,
        finrank_top, Module.finrank_fin_fun]
    rw [Module.finrank_fin_fun] at h1
    omega
  · intro h v hv
    exact absurd hv (h v)

/-- The partial derivative of a differentiable `f(v; q)` in `v` is `Df ∘ inl`. -/
theorem fderiv_partial_left {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : E × F → G} {v : E} {q : F} (hf : DifferentiableAt ℝ f (v, q)) :
    HasFDerivAt (fun v' => f (v', q)) ((fderiv ℝ f (v, q)).comp
      (ContinuousLinearMap.inl ℝ E F)) v :=
  hf.hasFDerivAt.comp v (hasFDerivAt_prodMk_left v q)

/-- **Proposition 17.D.3 (the transversality theorem)** (MWG, p. 595), `M = N`. If
`f : ℝ^N × ℝ^S → ℝ^N` is `C¹` and the `N × (N + S)` matrix `Df(v; q)` has rank `N` whenever
`f(v; q) = 0`, then for almost every `q` the system `f(·; q) = 0` is regular. (Chapter 3,
`theorem_M_E_2_regular`.) -/
theorem proposition_17_D_3 {N S : ℕ} {f : (Fin N → ℝ) × (Fin S → ℝ) → Fin N → ℝ}
    (hf : ContDiff ℝ 1 f) (hrank : ∀ p, f p = 0 → (fderiv ℝ f p).range = ⊤) :
    ∀ᵐ q, RegularEqSystem fun v => f (v, q) := by
  filter_upwards [theorem_M_E_2_regular hf hrank] with q hq
  intro v hv
  have hd := fderiv_partial_left (q := q) (hf.differentiable one_ne_zero (v, q))
  rw [hd.fderiv]
  obtain ⟨e, he⟩ := hq v hv
  rw [← he]
  exact LinearMap.range_eq_top.2 e.surjective

/-- **Proposition 17.D.3** (MWG, p. 595), `M > N` (more equations than unknowns): under the
hypotheses of the transversality theorem, for almost every `q` the system `f(·; q) = 0` has no
solution (so it is regular, `regularEqSystem_iff_of_lt`). Proof: pad the unknowns to `ℝ^M` and
apply the square case; the padded partial derivative kills the dummy directions. -/
theorem proposition_17_D_3_over {N M S : ℕ} (hNM : N < M)
    {f : (Fin N → ℝ) × (Fin S → ℝ) → Fin M → ℝ}
    (hf : ContDiff ℝ 1 f) (hrank : ∀ p, f p = 0 → (fderiv ℝ f p).range = ⊤) :
    ∀ᵐ q, RegularEqSystem fun v => f (v, q) := by
  set π : (Fin M → ℝ) →L[ℝ] (Fin N → ℝ) :=
    ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (Fin.castLE hNM.le j)
  set P : (Fin M → ℝ) × (Fin S → ℝ) →L[ℝ] (Fin N → ℝ) × (Fin S → ℝ) :=
    π.prodMap (ContinuousLinearMap.id ℝ _)
  set F : (Fin M → ℝ) × (Fin S → ℝ) → Fin M → ℝ := fun u => f (P u)
  have hP : ∀ u, HasFDerivAt F ((fderiv ℝ f (P u)).comp P) u := fun u =>
    (hf.differentiable one_ne_zero (P u)).hasFDerivAt.comp u P.hasFDerivAt
  have hPsurj : LinearMap.range
      (P : (Fin M → ℝ) × (Fin S → ℝ) →ₗ[ℝ] (Fin N → ℝ) × (Fin S → ℝ)) = ⊤ := by
    refine LinearMap.range_eq_top.2 fun w => ⟨(fun k => if h : (k : ℕ) < N then w.1 ⟨k, h⟩
      else 0, w.2), ?_⟩
    ext j
    · simp [P, π]
    · simp [P]
  have hF : ContDiff ℝ 1 F := hf.comp P.contDiff
  have hFrank : ∀ u, F u = 0 → (fderiv ℝ F u).range = ⊤ := by
    intro u hu
    rw [(hP u).fderiv]
    change LinearMap.range ((fderiv ℝ f (P u) : (Fin N → ℝ) × (Fin S → ℝ) →ₗ[ℝ] (Fin M → ℝ)).comp
      (P : (Fin M → ℝ) × (Fin S → ℝ) →ₗ[ℝ] (Fin N → ℝ) × (Fin S → ℝ))) = ⊤
    rw [LinearMap.range_comp_of_range_eq_top _ hPsurj]
    exact hrank _ hu
  filter_upwards [theorem_M_E_2_regular hF hFrank] with q hq
  refine (regularEqSystem_iff_of_lt hNM _).2 fun v hv => ?_
  set u : Fin M → ℝ := fun k => if h : (k : ℕ) < N then v ⟨k, h⟩ else 0
  have hPu : P (u, q) = (v, q) := by
    ext j
    · simp [P, π, u]
    · simp [P]
  obtain ⟨e, he⟩ := hq u (by simp only [F, hPu]; exact hv)
  -- the dummy direction `e_N` is killed by `D_u F`
  have hker : ((fderiv ℝ F (u, q)).comp (ContinuousLinearMap.inl ℝ _ _))
      (Pi.single ⟨N, hNM⟩ 1) = 0 := by
    rw [(hP (u, q)).fderiv]
    have : P ((ContinuousLinearMap.inl ℝ (Fin M → ℝ) (Fin S → ℝ)) (Pi.single ⟨N, hNM⟩ 1)) = 0 := by
      ext j
      · change (Pi.single (⟨N, hNM⟩ : Fin M) (1 : ℝ) : Fin M → ℝ) (Fin.castLE hNM.le j) = 0
        rw [Pi.single_apply]
        split_ifs with h
        · have := congrArg Fin.val h
          simp only [Fin.val_castLE] at this
          omega
        · rfl
      · rfl
    simp only [ContinuousLinearMap.comp_apply, this, map_zero]
  rw [← he] at hker
  have h0 : (Pi.single ⟨N, hNM⟩ (1 : ℝ) : Fin M → ℝ) = 0 :=
    e.injective (by rw [map_zero]; exact hker)
  have := congrFun h0 ⟨N, hNM⟩
  simp at this

/-! ### Exercise 17.D.2 -/

/-- **Exercise 17.D.2** (MWG, p. 644). If `f(v̄) = 0` for a `C¹` system of `M` equations in `N`
unknowns and `rank Df(v̄) = M`, then near `v̄` the solution set of `f = 0` is parametrized by
`N - M` parameters: there is `φ : ℝ^{N-M} → ℝ^N`, `φ(0) = v̄`, strictly differentiable at `0`
with injective derivative, with `f(φ(k)) = 0` for `k` near `0`, and every solution near `v̄` is
`φ(k)` for some `k` in any prescribed neighbourhood of `0`. -/
theorem exercise_17_D_2 {N M : ℕ} {f : (Fin N → ℝ) → Fin M → ℝ} {v₀ : Fin N → ℝ}
    (hf : ContDiffAt ℝ 1 f v₀) (h0 : f v₀ = 0) (hrank : (fderiv ℝ f v₀).range = ⊤) :
    ∃ φ : (Fin (N - M) → ℝ) → Fin N → ℝ, φ 0 = v₀ ∧
      (∃ φ' : (Fin (N - M) → ℝ) →L[ℝ] (Fin N → ℝ), HasStrictFDerivAt φ φ' 0 ∧
        Function.Injective φ') ∧
      (∀ᶠ k in 𝓝 0, f (φ k) = 0) ∧
      ∀ U ∈ 𝓝 (0 : Fin (N - M) → ℝ), ∀ᶠ v in 𝓝 v₀, f v = 0 → ∃ k ∈ U, φ k = v := by
  have hs : HasStrictFDerivAt f (fderiv ℝ f v₀) v₀ := hf.hasStrictFDerivAt one_ne_zero
  have h := LinearMap.finrank_range_add_finrank_ker
    (fderiv ℝ f v₀ : (Fin N → ℝ) →ₗ[ℝ] (Fin M → ℝ))
  rw [show LinearMap.range (fderiv ℝ f v₀ : (Fin N → ℝ) →ₗ[ℝ] (Fin M → ℝ)) = ⊤ from hrank,
    finrank_top, Module.finrank_fin_fun, Module.finrank_fin_fun] at h
  have hdim : Module.finrank ℝ (Fin (N - M) → ℝ) =
      Module.finrank ℝ (LinearMap.ker (fderiv ℝ f v₀ : (Fin N → ℝ) →ₗ[ℝ] (Fin M → ℝ))) := by
    rw [Module.finrank_fin_fun]
    omega
  set K := LinearMap.ker (fderiv ℝ f v₀ : (Fin N → ℝ) →ₗ[ℝ] (Fin M → ℝ))
  set eL : (Fin (N - M) → ℝ) ≃ₗ[ℝ] K := LinearEquiv.ofFinrankEq _ _ hdim
  set e : (Fin (N - M) → ℝ) ≃L[ℝ] K := eL.toContinuousLinearEquiv
  set g := hs.implicitFunction f (fderiv ℝ f v₀) hrank
  set φ : (Fin (N - M) → ℝ) → Fin N → ℝ := fun k => g (f v₀) (e k)
  refine ⟨φ, ?_, ?_, ?_, ?_⟩
  · simp only [φ, map_zero, g]
    exact hs.implicitFunction_apply_image hrank
  · refine ⟨K.subtypeL.comp (e : (Fin (N - M) → ℝ) →L[ℝ] K), ?_, ?_⟩
    · have h1 := hs.to_implicitFunction hrank
      have h2 : HasStrictFDerivAt (fun k => e k) (e : (Fin (N - M) → ℝ) →L[ℝ] K) 0 :=
        e.hasStrictFDerivAt
      have h1' : HasStrictFDerivAt (g (f v₀)) K.subtypeL (e 0) := by
        rw [map_zero]; exact h1
      exact h1'.comp (0 : Fin (N - M) → ℝ) h2
    · intro k k' h
      apply e.injective
      exact Subtype.ext h
  · have hmap := hs.map_implicitFunction_eq hrank
    have ht : Tendsto (fun k : Fin (N - M) → ℝ => (f v₀, e k)) (𝓝 0) (𝓝 (f v₀, 0)) := by
      refine tendsto_const_nhds.prodMk_nhds ?_
      simpa using e.continuous.tendsto 0
    filter_upwards [ht.eventually hmap] with k hk
    simp only [φ, g]
    rw [hk, h0]
  · intro U hU
    set H := hs.implicitToOpenPartialHomeomorph f (fderiv ℝ f v₀) hrank
    have hcont : ContinuousAt (fun v => e.symm (H v).2) v₀ := by
      refine e.symm.continuous.continuousAt.comp (continuous_snd.continuousAt.comp ?_)
      exact H.continuousAt (hs.mem_implicitToOpenPartialHomeomorph_source hrank)
    have hH0 : e.symm (H v₀).2 = 0 := by
      simp [H]
    have hU' : ∀ᶠ v in 𝓝 v₀, e.symm (H v).2 ∈ U :=
      hcont.eventually (show U ∈ 𝓝 (e.symm (H v₀).2) by rw [hH0]; exact hU)
    filter_upwards [hs.eq_implicitFunction hrank, hU'] with v hv hvU hfv
    refine ⟨e.symm (H v).2, hvU, ?_⟩
    simp only [φ, g, ContinuousLinearEquiv.apply_symm_apply]
    rw [h0, ← hfv]
    exact hv

/-! ### The excess demand equations with endowments as parameters -/

variable {n I : ℕ}

/-- Consumer `i`'s endowment in the vector `ω = (ω₁₁, …, ω_{LI}) ∈ ℝ^{LI}` (MWG p. 596). -/
def endowOf (ω : Fin (I * (n + 1)) → ℝ) (i : Fin I) : Fin (n + 1) → ℝ :=
  fun l => ω (finProdFinEquiv (i, l))

/-- `ẑ(p̂; ω)`: the normalized excess demand as a function of prices and endowments (p. 596). -/
noncomputable def genSystem (x : Fin I → (Fin (n + 1) → ℝ) → ℝ → Fin (n + 1) → ℝ)
    (v : (Fin n → ℝ) × (Fin (I * (n + 1)) → ℝ)) : Fin n → ℝ :=
  normED (demandED x (endowOf v.2)) v.1

/-- The endowment perturbation of the proof of Proposition 17.D.4: consumer `i₀` receives
`dω = (-y, p̂·y)`, which has value zero at `p = (p̂, 1)`. -/
noncomputable def endowPerturb (i₀ : Fin I) (q y : Fin n → ℝ) : Fin (I * (n + 1)) → ℝ :=
  fun k => if (finProdFinEquiv.symm k).1 = i₀ then
    Fin.snoc (α := fun _ => ℝ) (-y) (q ⬝ᵥ y) (finProdFinEquiv.symm k).2 else 0

theorem endowOf_add_smul (ω ω' : Fin (I * (n + 1)) → ℝ) (s : ℝ) (i : Fin I) :
    endowOf (ω + s • ω') i = endowOf ω i + s • endowOf ω' i := by
  funext l
  simp [endowOf]

theorem endowOf_endowPerturb (i₀ : Fin I) (q y : Fin n → ℝ) (i : Fin I) :
    endowOf (endowPerturb i₀ q y) i =
      if i = i₀ then Fin.snoc (α := fun _ => ℝ) (-y) (q ⬝ᵥ y) else 0 := by
  funext l
  by_cases h : i = i₀ <;> simp [endowOf, endowPerturb, h]

/-- The perturbation has zero value: `(p̂, 1)·(-y, p̂·y) = 0`. -/
theorem normPrice_dotProduct_snoc (q y : Fin n → ℝ) :
    normPrice q ⬝ᵥ Fin.snoc (α := fun _ => ℝ) (-y) (q ⬝ᵥ y) = 0 := by
  rw [dotProduct, Fin.sum_univ_castSucc]
  simp [dotProduct, Finset.sum_neg_distrib]

/-- **Proof of Proposition 17.D.4** (MWG, p. 596). Perturbing consumer `i₀`'s endowment by
`s·(-y, p̂·y)` leaves his wealth at `p = (p̂, 1)` unchanged and moves `ẑ` by exactly `s y`. -/
theorem genSystem_shift (x : Fin I → (Fin (n + 1) → ℝ) → ℝ → Fin (n + 1) → ℝ)
    (i₀ : Fin I) (q y : Fin n → ℝ) (ω : Fin (I * (n + 1)) → ℝ) (s : ℝ) :
    genSystem x (q, ω + s • endowPerturb i₀ q y) = genSystem x (q, ω) + s • y := by
  funext l
  simp only [genSystem, normED, truncExcessDemand, demandED, endowOf_add_smul,
    endowOf_endowPerturb, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hw : ∀ i, normPrice q ⬝ᵥ (endowOf ω i + s • (if i = i₀ then
      Fin.snoc (α := fun _ => ℝ) (-y) (q ⬝ᵥ y) else 0)) = normPrice q ⬝ᵥ endowOf ω i := by
    intro i
    rw [dotProduct_add, dotProduct_smul]
    split_ifs
    · rw [normPrice_dotProduct_snoc, smul_zero, add_zero]
    · simp
  simp only [hw, Finset.sum_apply, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hsum : ∑ i : Fin I, s * (if i = i₀ then Fin.snoc (α := fun _ => ℝ) (-y) (q ⬝ᵥ y)
      else (0 : Fin (n + 1) → ℝ)) (Fin.castSucc l) = -(s * y l) := by
    rw [Finset.sum_eq_single i₀]
    · simp
    · intro i _ hi; simp [hi]
    · simp
  rw [hsum]
  ring

/-- **Proposition 17.D.4** (MWG, p. 596). If `ẑ(·; ·)` is differentiable at `(p̂, ω)` (and there
is at least one consumer), then `D_ω ẑ(p̂; ω)` has rank `L - 1`: it is onto `ℝ^{L-1}`. Hence the
full matrix `Dẑ(p̂; ω)` has rank `L - 1` as well. -/
theorem proposition_17_D_4 (hI : 0 < I) (x : Fin I → (Fin (n + 1) → ℝ) → ℝ → Fin (n + 1) → ℝ)
    {q : Fin n → ℝ} {ω : Fin (I * (n + 1)) → ℝ}
    (hd : DifferentiableAt ℝ (genSystem x) (q, ω)) :
    ((fderiv ℝ (genSystem x) (q, ω)).comp (ContinuousLinearMap.inr ℝ _ _)).range = ⊤ ∧
      (fderiv ℝ (genSystem x) (q, ω)).range = ⊤ := by
  have hpartial : ((fderiv ℝ (genSystem x) (q, ω)).comp
      (ContinuousLinearMap.inr ℝ _ _)).range = ⊤ := by
    refine LinearMap.range_eq_top.2 fun y => ⟨endowPerturb ⟨0, hI⟩ q y, ?_⟩
    have hline : HasDerivAt (fun s : ℝ => (q, ω + s • endowPerturb ⟨0, hI⟩ q y))
        ((0 : Fin n → ℝ), endowPerturb ⟨0, hI⟩ q y) 0 := by
      refine (hasDerivAt_const (0 : ℝ) q).prodMk ?_
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (endowPerturb ⟨0, hI⟩ q y)).const_add ω
    have h1 := hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
    have h2 : HasDerivAt (fun s : ℝ => genSystem x (q, ω + s • endowPerturb ⟨0, hI⟩ q y)) y 0 := by
      simp only [genSystem_shift]
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const y).const_add (genSystem x (q, ω))
    have := h1.unique h2
    simpa using this
  refine ⟨hpartial, ?_⟩
  rw [eq_top_iff, ← hpartial]
  rintro w ⟨v, rfl⟩
  exact ⟨_, rfl⟩

/-- **Exercise 17.D.3** (MWG, p. 644): the explicit computation behind Proposition 17.D.4. If
consumer `i₀`'s demand is differentiable in wealth at `w = p·ω_{i₀}` with derivative `D_w x`,
then changing his endowment in the direction `v` changes `ẑ` at rate
`(p·v) D_w x̂ - v̂` (`D_{ω_{i₀}}ẑ = D_w x̂ pᵀ - [I_{L-1} | 0]`). For `v = (-y, p̂·y)` this is `y`,
so the rank is `L - 1`. -/
theorem exercise_17_D_3 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → (Fin (n + 1) → ℝ) → ℝ → Fin (n + 1) → ℝ) (ω : ι → Fin (n + 1) → ℝ) (i₀ : ι)
    (q : Fin n → ℝ) {dx : Fin (n + 1) → ℝ}
    (hdx : HasDerivAt (fun w => x i₀ (normPrice q) w) dx (normPrice q ⬝ᵥ ω i₀))
    (v : Fin (n + 1) → ℝ) :
    HasDerivAt (fun s : ℝ => normED (demandED x (Function.update ω i₀ (ω i₀ + s • v))) q)
      ((normPrice q ⬝ᵥ v) • (fun l => dx (Fin.castSucc l)) - fun l => v (Fin.castSucc l)) 0 := by
  set p := normPrice q
  have hsplit : ∀ s : ℝ, normED (demandED x (Function.update ω i₀ (ω i₀ + s • v))) q =
      (fun l => (∑ i ∈ Finset.univ.erase i₀, (x i p (p ⬝ᵥ ω i) - ω i)) (Fin.castSucc l)) +
      fun l => (x i₀ p (p ⬝ᵥ ω i₀ + s * (p ⬝ᵥ v)) - (ω i₀ + s • v)) (Fin.castSucc l) := by
    intro s
    funext l
    simp only [normED, truncExcessDemand, demandED, Pi.add_apply]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
    have : ∑ i ∈ Finset.univ.erase i₀, (x i p (p ⬝ᵥ Function.update ω i₀ (ω i₀ + s • v) i) -
        Function.update ω i₀ (ω i₀ + s • v) i) =
        ∑ i ∈ Finset.univ.erase i₀, (x i p (p ⬝ᵥ ω i) - ω i) :=
      Finset.sum_congr rfl fun i hi => by
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
    rw [this, Function.update_self, dotProduct_add, dotProduct_smul, smul_eq_mul]
    simp only [Finset.sum_apply, Pi.add_apply]
    ring
  simp only [hsplit]
  have hw : HasDerivAt (fun s : ℝ => p ⬝ᵥ ω i₀ + s * (p ⬝ᵥ v)) (p ⬝ᵥ v) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (p ⬝ᵥ v)).const_add (p ⬝ᵥ ω i₀)
  have hx : HasDerivAt (fun s : ℝ => x i₀ p (p ⬝ᵥ ω i₀ + s * (p ⬝ᵥ v))) ((p ⬝ᵥ v) • dx) 0 := by
    have hdx' : HasDerivAt (fun w => x i₀ p w) dx (p ⬝ᵥ ω i₀ + 0 * (p ⬝ᵥ v)) := by
      simpa using hdx
    have := hdx'.scomp (0 : ℝ) hw
    simpa [Function.comp_def] using this
  have hz : HasDerivAt (fun s : ℝ => x i₀ p (p ⬝ᵥ ω i₀ + s * (p ⬝ᵥ v)) - (ω i₀ + s • v))
      ((p ⬝ᵥ v) • dx - v) 0 := by
    refine hx.sub ?_
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add (ω i₀)
  have htr := (truncCLM n).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hz
  have hconst := hasDerivAt_const (0 : ℝ)
    (fun l : Fin n => (∑ i ∈ Finset.univ.erase i₀, (x i p (p ⬝ᵥ ω i) - ω i)) (Fin.castSucc l))
  convert hconst.add htr using 1
  · funext l
    rfl
  · funext l
    simp [truncCLM]

/-! ### Proposition 17.D.5: generic regularity -/

/-- `p̂ ↦ (p̂, 1)` is smooth (affine). -/
theorem contDiff_normPrice : ContDiff ℝ 1 (normPrice (n := n)) := by
  have heq : (normPrice : (Fin n → ℝ) → Fin (n + 1) → ℝ) =
      fun q => inclCLM n q + Pi.single (Fin.last n) 1 := by
    funext q k
    refine Fin.lastCases ?_ (fun l => ?_) k
    · simp
    · simp [Fin.castSucc_ne_last]
  rw [heq]
  exact (inclCLM n).contDiff.add contDiff_const

/-- **Proposition 17.D.5**, differentiability: with `C¹` demand functions, `ẑ(p̂; ω)` is `C¹` on
`{p̂ ≫ 0} × ℝ^{LI}_{++}`. -/
theorem contDiffOn_genSystem {x : Fin I → (Fin (n + 1) → ℝ) → ℝ → Fin (n + 1) → ℝ}
    (hx : ∀ i, ContDiffOn ℝ 1 (fun r : (Fin (n + 1) → ℝ) × ℝ => x i r.1 r.2)
      (posOrthant (n + 1) ×ˢ Set.Ioi 0)) :
    ContDiffOn ℝ 1 (genSystem x) (posOrthant n ×ˢ posOrthant (I * (n + 1))) := by
  have hinner : ∀ i, ContDiff ℝ 1 fun v : (Fin n → ℝ) × (Fin (I * (n + 1)) → ℝ) =>
      (normPrice v.1, normPrice v.1 ⬝ᵥ endowOf v.2 i) := by
    intro i
    refine (contDiff_normPrice.comp contDiff_fst).prodMk ?_
    simp only [dotProduct, endowOf]
    refine ContDiff.sum fun l _ => ?_
    exact ((contDiff_apply ℝ ℝ l).comp (contDiff_normPrice.comp contDiff_fst)).mul
      ((contDiff_apply ℝ ℝ _).comp contDiff_snd)
  have hmaps : ∀ i, Set.MapsTo (fun v : (Fin n → ℝ) × (Fin (I * (n + 1)) → ℝ) =>
      (normPrice v.1, normPrice v.1 ⬝ᵥ endowOf v.2 i))
      (posOrthant n ×ˢ posOrthant (I * (n + 1))) (posOrthant (n + 1) ×ˢ Set.Ioi 0) := by
    intro i v hv
    have hp := normPrice_mem_posOrthant.2 hv.1
    refine ⟨hp, ?_⟩
    change 0 < normPrice v.1 ⬝ᵥ endowOf v.2 i
    exact Finset.sum_pos (fun l _ => mul_pos (hp l) (hv.2 _)) Finset.univ_nonempty
  refine contDiffOn_pi.2 fun l => ?_
  simp only [genSystem, normED, truncExcessDemand, demandED, Finset.sum_apply, Pi.sub_apply]
  refine ContDiffOn.sum fun i _ => ContDiffOn.sub ?_ ?_
  · exact (contDiffOn_pi.1 (hx i) (Fin.castSucc l)).comp (hinner i).contDiffOn (hmaps i)
  · exact ((contDiff_apply ℝ ℝ _).comp contDiff_snd).contDiffOn

/-- **Proposition 17.D.5** (MWG, p. 596; Debreu 1970). Suppose every consumer `i` (`I ≥ 1`) has a
demand function `xᵢ(p, w)` that is `C¹` on `{p ≫ 0} × (0, ∞)` (the differentiability assumption
of the section). Then for almost every vector of initial endowments `(ω₁, …, ω_I) ∈ ℝ^{LI}_{++}`
the economy is regular: the set of endowments yielding nonregular economies has `LI`-dimensional
Lebesgue measure zero (footnote 21). Proof: Proposition 17.D.4 and the transversality theorem. -/
theorem proposition_17_D_5 (hI : 0 < I) {x : Fin I → (Fin (n + 1) → ℝ) → ℝ → Fin (n + 1) → ℝ}
    (hx : ∀ i, ContDiffOn ℝ 1 (fun r : (Fin (n + 1) → ℝ) × ℝ => x i r.1 r.2)
      (posOrthant (n + 1) ×ˢ Set.Ioi 0)) :
    volume {ω : Fin (I * (n + 1)) → ℝ | ω ∈ posOrthant (I * (n + 1)) ∧
      ¬ IsRegularEconomy (demandED x (endowOf ω))} = 0 := by
  have hA := isOpen_posOrthant n
  have hB := isOpen_posOrthant (I * (n + 1))
  have hf := contDiffOn_genSystem hx
  have hdiff : ∀ p ∈ posOrthant n ×ˢ posOrthant (I * (n + 1)),
      DifferentiableAt ℝ (genSystem x) p := fun p hp =>
    ((hf.contDiffAt ((hA.prod hB).mem_nhds hp)).differentiableAt one_ne_zero)
  refine measure_mono_null (fun ω hω => ?_) (theorem_M_E_2 hA hB hf fun p hp _ =>
    (proposition_17_D_4 hI x (hdiff p hp)).2)
  obtain ⟨hωB, hnot⟩ := hω
  simp only [IsRegularEconomy, not_forall] at hnot
  obtain ⟨q, hq, hnreg⟩ := hnot
  have hqA : q ∈ posOrthant n := normPrice_mem_posOrthant.1 hq.1
  have hd := hdiff (q, ω) ⟨hqA, hωB⟩
  have hpart := fderiv_partial_left hd
  refine ⟨hωB, q, hqA, hq.normED_eq_zero, fun hinv => hnreg ⟨hq, hpart.differentiableAt, ?_⟩⟩
  have : fderiv ℝ (normED (demandED x (endowOf ω))) q =
      (fderiv ℝ (genSystem x) (q, ω)).comp (ContinuousLinearMap.inl ℝ _ _) := hpart.fderiv
  rw [this]
  exact (isInvertible_iff_det_ne_zero _).1 hinv

/-- Regularity only depends on `z` near the positive orthant. -/
theorem isRegularEconomy_congr {z z' : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ}
    (h : Set.EqOn z z' (posOrthant (n + 1))) (hz : IsRegularEconomy z) :
    IsRegularEconomy z' := by
  have hev : ∀ q ∈ posOrthant n, normED z =ᶠ[𝓝 q] normED z' := by
    intro q hq
    filter_upwards [(isOpen_posOrthant n).mem_nhds hq] with q' hq'
    change truncExcessDemand z (normPrice q') = truncExcessDemand z' (normPrice q')
    unfold truncExcessDemand
    rw [h (normPrice_mem_posOrthant.2 hq')]
  have heqm : ∀ q, IsNormEqm z q ↔ IsNormEqm z' q := fun q =>
    ⟨fun hq => ⟨hq.1, by rw [← h hq.1]; exact hq.2⟩,
      fun hq => ⟨hq.1, by rw [h hq.1]; exact hq.2⟩⟩
  intro q hq
  have hq' := (heqm q).2 hq
  obtain ⟨-, hd, hdet⟩ := hz q hq'
  have hqA := normPrice_mem_posOrthant.1 hq.1
  refine ⟨hq, (hev q hqA).differentiableAt_iff.1 hd, ?_⟩
  rwa [← (hev q hqA).fderiv_eq]

/-- **Proposition 17.D.5**, instance: in Cobb-Douglas exchange economies (exponents `aᵢ ≫ 0`)
almost every endowment vector `ω ∈ ℝ^{LI}_{++}` gives a regular economy. -/
theorem proposition_17_D_5_cobbDouglas (hI : 0 < I) {a : Fin I → Fin (n + 1) → ℝ}
    (ha : ∀ i l, 0 < a i l) :
    volume {ω : Fin (I * (n + 1)) → ℝ | ω ∈ posOrthant (I * (n + 1)) ∧
      ¬ IsRegularEconomy (excessDemand (cdEconomy a (endowOf ω)))} = 0 := by
  refine measure_mono_null ?_
    (proposition_17_D_5 hI (x := fun i => cdDemand (a i)) fun i => contDiffOn_cdDemand (a i))
  intro ω hω
  obtain ⟨hωB, hnot⟩ := hω
  refine ⟨hωB, fun hreg => hnot ?_⟩
  refine isRegularEconomy_congr (fun p hp => ?_) hreg
  exact (excessDemand_cdEconomy ha (fun i l => (hωB _).le) hp).symm

end MWG.PositiveEquilibriumTheory
