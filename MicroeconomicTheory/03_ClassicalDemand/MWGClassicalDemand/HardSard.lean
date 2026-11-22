/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGClassicalDemand.AppendixME
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.Normed.Operator.Prod

/-!
# The transversality theorem (Theorem M.E.2)

MWG, Section M.E, p. 943: if `f : A × B → ℝ^N` (`A ⊆ ℝ^N`, `B ⊆ ℝ^M` open) is continuously
differentiable and `Df(x; q)` has rank `N` whenever `f(x; q) = 0`, then `f(·; q) = 0` is regular
for almost every `q ∈ B`.

No Sard theorem in unequal dimensions is needed: Mathlib's Sard lemma in equal dimension
(`addHaar_image_eq_zero_of_det_fderivWithin_eq_zero`, for differentiable maps `ℝ^M → ℝ^M`)
suffices, applied in charts of the zero set.

* `hardSard_local`: near a point `p` where `Df(p)` is onto, choose `Λ : ℝ^N × ℝ^M → ℝ^M`
  injective on `ker Df(p)` (`hardSard_exists_complement_map`), so that `φ = (f, Λ)` has an
  invertible derivative at `p`; the inverse function theorem gives a chart `Φ` of `ℝ^{N+M}`
  in which the zero set of `f` is `{Φ⁻¹(0, k)}`. The bad parameters near `p` are images of
  `k ↦ (Φ⁻¹(0, k))_q`, a differentiable map `ℝ^M → ℝ^M` whose derivative is singular wherever
  `D_x f` is singular (`hardSard_det_eq_zero`): if `D_x f ξ = 0` then `κ = Λ(ξ, 0) ≠ 0` and the
  derivative kills `κ`. Sard's lemma gives measure zero.
* `theorem_M_E_2`: the bad set `{q ∈ B : ∃ x ∈ A, f(x; q) = 0, D_x f(x; q) singular}` has
  Lebesgue measure zero (countably many charts cover the zero set, second countability);
  `theorem_M_E_2_ae`: equivalently, for almost every `q ∈ B` the system is regular on `A`;
  `theorem_M_E_2_regular`: with `A = ℝ^N`, `B = ℝ^M`, `RegularSystemAt f q` for a.e. `q`.
-/

namespace MWG.ClassicalDemand

open Filter Topology MeasureTheory

/-- For a surjective linear map `D : ℝ^N × ℝ^M → ℝ^N` there is a linear `Λ : ℝ^N × ℝ^M → ℝ^M`
that is injective on `ker D`, so that `(D, Λ)` is injective. -/
theorem hardSard_exists_complement_map {N M : ℕ}
    (D : (Fin N → ℝ) × (Fin M → ℝ) →L[ℝ] (Fin N → ℝ)) (hD : D.range = ⊤) :
    ∃ Λ : (Fin N → ℝ) × (Fin M → ℝ) →L[ℝ] (Fin M → ℝ),
      ∀ w, D w = 0 → Λ w = 0 → w = 0 := by
  set K := LinearMap.ker (D : (Fin N → ℝ) × (Fin M → ℝ) →ₗ[ℝ] (Fin N → ℝ)) with hK
  have hrk := LinearMap.finrank_range_add_finrank_ker
    (D : (Fin N → ℝ) × (Fin M → ℝ) →ₗ[ℝ] (Fin N → ℝ))
  have hrange : LinearMap.range (D : (Fin N → ℝ) × (Fin M → ℝ) →ₗ[ℝ] (Fin N → ℝ)) = ⊤ := hD
  rw [hrange, finrank_top, Module.finrank_prod, Module.finrank_fin_fun,
    Module.finrank_fin_fun] at hrk
  have hKdim : Module.finrank ℝ K = Module.finrank ℝ (Fin M → ℝ) := by
    rw [Module.finrank_fin_fun]
    change N + Module.finrank ℝ K = N + M at hrk
    omega
  obtain ⟨g, hg⟩ := K.subtype.exists_leftInverse_of_injective K.ker_subtype
  set e := LinearEquiv.ofFinrankEq K (Fin M → ℝ) hKdim with he
  refine ⟨LinearMap.toContinuousLinearMap (e.toLinearMap ∘ₗ g), fun w hw hΛ => ?_⟩
  have hwK : w ∈ K := hw
  have hgw : g w = ⟨w, hwK⟩ := by
    have := congrArg (fun T : K →ₗ[ℝ] K => T ⟨w, hwK⟩) hg
    simpa using this
  have : e (g w) = 0 := hΛ
  rw [hgw, LinearEquiv.map_eq_zero_iff] at this
  exact congrArg Subtype.val this

/-- An injective endomorphism of `ℝ^N` is invertible. -/
theorem hardSard_isInvertible_of_injective {N : ℕ} (T : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ))
    (hT : Function.Injective T) : T.IsInvertible :=
  ⟨(LinearEquiv.ofInjectiveEndo (T : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ)) hT).toContinuousLinearEquiv,
    by ext v; rfl⟩

/-- **Theorem M.E.2**, local step. Let `f` be `C¹` on an open `U ⊆ ℝ^N × ℝ^M` and `Df(p)` onto
at `p ∈ U`. Then `p` has an open neighbourhood `S` such that the set of parameters `q` for which
some `(x, q) ∈ S ∩ U` solves `f(x; q) = 0` with `D_x f(x; q)` singular has measure zero. -/
theorem hardSard_local {N M : ℕ} {U : Set ((Fin N → ℝ) × (Fin M → ℝ))} (hU : IsOpen U)
    {f : (Fin N → ℝ) × (Fin M → ℝ) → (Fin N → ℝ)} (hf : ContDiffOn ℝ 1 f U)
    {p : (Fin N → ℝ) × (Fin M → ℝ)} (hpU : p ∈ U) (hsurj : (fderiv ℝ f p).range = ⊤) :
    ∃ S : Set ((Fin N → ℝ) × (Fin M → ℝ)), IsOpen S ∧ p ∈ S ∧
      volume {q | ∃ x, (x, q) ∈ S ∧ (x, q) ∈ U ∧ f (x, q) = 0 ∧
        ¬ ((fderiv ℝ f (x, q)).comp (ContinuousLinearMap.inl ℝ _ _)).IsInvertible} = 0 := by
  obtain ⟨Λ, hΛ⟩ := hardSard_exists_complement_map (fderiv ℝ f p) hsurj
  set φ : (Fin N → ℝ) × (Fin M → ℝ) → (Fin N → ℝ) × (Fin M → ℝ) := fun w => (f w, Λ w) with hφ
  set Dφ : (Fin N → ℝ) × (Fin M → ℝ) → ((Fin N → ℝ) × (Fin M → ℝ) →L[ℝ]
    (Fin N → ℝ) × (Fin M → ℝ)) := fun w => (fderiv ℝ f w).prod Λ with hDφ
  have hfd : ∀ w ∈ U, HasFDerivAt f (fderiv ℝ f w) w := fun w hw =>
    ((hf.differentiableOn one_ne_zero w hw).differentiableAt (hU.mem_nhds hw)).hasFDerivAt
  have hφd : ∀ w ∈ U, HasFDerivAt φ (Dφ w) w := fun w hw =>
    (hfd w hw).prodMk Λ.hasFDerivAt
  -- the derivative of `φ` at `p` is invertible
  have hinj : Function.Injective (Dφ p).toLinearMap := by
    refine (injective_iff_map_eq_zero _).mpr fun w hw => ?_
    have h1 : fderiv ℝ f p w = 0 := congrArg Prod.fst hw
    have h2 : Λ w = 0 := congrArg Prod.snd hw
    exact hΛ w h1 h2
  set E₀ := (LinearEquiv.ofInjectiveEndo (Dφ p).toLinearMap hinj
    ).toContinuousLinearEquiv with hE₀
  have hE₀c : (E₀ : (Fin N → ℝ) × (Fin M → ℝ) →L[ℝ] (Fin N → ℝ) × (Fin M → ℝ)) = Dφ p := by
    ext v <;> rfl
  have hfs : HasStrictFDerivAt f (fderiv ℝ f p) p :=
    (hf.contDiffAt (hU.mem_nhds hpU)).hasStrictFDerivAt one_ne_zero
  have hφs : HasStrictFDerivAt φ (E₀ : (Fin N → ℝ) × (Fin M → ℝ) →L[ℝ] _) p := by
    rw [hE₀c]
    exact hfs.prodMk Λ.hasStrictFDerivAt
  set Φ := hφs.toOpenPartialHomeomorph φ with hΦ
  have hΦc : (Φ : (Fin N → ℝ) × (Fin M → ℝ) → (Fin N → ℝ) × (Fin M → ℝ)) = φ := rfl
  -- the set where `Dφ` is invertible is open
  have hDc : ContinuousOn Dφ U := by
    have := hf.continuousOn_fderiv_of_isOpen hU le_rfl
    exact (ContinuousLinearMap.prodₗᵢ ℝ).continuous.comp_continuousOn
      (this.prodMk continuousOn_const)
  have hO : IsOpen (U ∩ Dφ ⁻¹' {T | IsUnit T}) := hDc.isOpen_inter_preimage hU Units.isOpen
  set S := Φ.source ∩ (U ∩ Dφ ⁻¹' {T | IsUnit T}) with hS
  have hpS : p ∈ S := ⟨hφs.mem_toOpenPartialHomeomorph_source, hpU, by
    change IsUnit (Dφ p)
    rw [← hE₀c]
    exact (ContinuousLinearEquiv.unitsEquiv ℝ _).symm E₀ |>.isUnit⟩
  refine ⟨S, Φ.open_source.inter hO, hpS, ?_⟩
  -- the parametrization of the zero set and the bad parameters
  set h : (Fin M → ℝ) → (Fin M → ℝ) := fun k => (Φ.symm (0, k)).2 with hh
  set s : Set (Fin M → ℝ) := {k | ((0 : Fin N → ℝ), k) ∈ Φ.target ∧ Φ.symm (0, k) ∈ S ∧
    ¬ ((fderiv ℝ f (Φ.symm (0, k))).comp (ContinuousLinearMap.inl ℝ _ _)).IsInvertible} with hs
  have hsub : {q | ∃ x, (x, q) ∈ S ∧ (x, q) ∈ U ∧ f (x, q) = 0 ∧
      ¬ ((fderiv ℝ f (x, q)).comp (ContinuousLinearMap.inl ℝ _ _)).IsInvertible} ⊆ h '' s := by
    rintro q ⟨x, hxS, -, hf0, hbad⟩
    have hmap : Φ (x, q) = (0, Λ (x, q)) := by rw [hΦc, hφ]; simp only [hf0]
    have htgt : ((0 : Fin N → ℝ), Λ (x, q)) ∈ Φ.target := hmap ▸ Φ.map_source hxS.1
    have hinv : Φ.symm (0, Λ (x, q)) = (x, q) := by rw [← hmap]; exact Φ.left_inv hxS.1
    refine ⟨Λ (x, q), ⟨htgt, by rw [hinv]; exact hxS, by rw [hinv]; exact hbad⟩, ?_⟩
    simp only [hh, hinv]
  refine measure_mono_null hsub ?_
  -- derivative of the parametrization and its singularity
  have hderiv : ∀ k ∈ s, ∃ D : (Fin M → ℝ) →L[ℝ] (Fin M → ℝ), HasFDerivAt h D k ∧ D.det = 0 := by
    intro k hk
    obtain ⟨htgt, hwS, hbad⟩ := hk
    set w := Φ.symm (0, k) with hw
    have hu : IsUnit (Dφ w) := hwS.2.2
    set Ew := ContinuousLinearEquiv.unitsEquiv ℝ _ hu.unit with hEw
    have hEwc : (Ew : (Fin N → ℝ) × (Fin M → ℝ) →L[ℝ] _) = Dφ w := rfl
    have hφw : HasFDerivAt Φ (Ew : (Fin N → ℝ) × (Fin M → ℝ) →L[ℝ] _) (Φ.symm (0, k)) := by
      rw [hEwc, hΦc]
      exact hφd w hwS.2.1
    have hψ := Φ.hasFDerivAt_symm htgt hφw
    have hin : HasFDerivAt (fun k' : Fin M → ℝ => ((0 : Fin N → ℝ), k'))
        ((0 : (Fin M → ℝ) →L[ℝ] (Fin N → ℝ)).prod (ContinuousLinearMap.id ℝ _)) k :=
      (hasFDerivAt_const _ k).prodMk (hasFDerivAt_id k)
    have hcomp := hasFDerivAt_snd.comp k (hψ.comp k hin)
    set Dk : (Fin M → ℝ) →L[ℝ] (Fin M → ℝ) :=
      (ContinuousLinearMap.snd ℝ (Fin N → ℝ) (Fin M → ℝ)).comp
        ((Ew.symm : ((Fin N → ℝ) × (Fin M → ℝ)) →L[ℝ] ((Fin N → ℝ) × (Fin M → ℝ))).comp
          ((0 : (Fin M → ℝ) →L[ℝ] (Fin N → ℝ)).prod (ContinuousLinearMap.id ℝ (Fin M → ℝ))))
      with hDk
    refine ⟨Dk, hcomp, ?_⟩
    -- a nonzero vector in the kernel
    have hni : ¬ Function.Injective
        ((fderiv ℝ f w).comp (ContinuousLinearMap.inl ℝ (Fin N → ℝ) (Fin M → ℝ))) :=
      fun hi => hbad (hardSard_isInvertible_of_injective _ hi)
    obtain ⟨ξ, hξ, hξ0⟩ : ∃ ξ, (fderiv ℝ f w) (ξ, 0) = 0 ∧ ξ ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hni
      refine (injective_iff_map_eq_zero _).mpr fun ξ' hξ' => ?_
      by_contra hne
      exact hne (hcon ξ' hξ')
    set κ := Λ (ξ, 0) with hκ
    have hEξ : Ew (ξ, 0) = (0, κ) := by
      change Dφ w (ξ, 0) = (0, κ)
      simp only [hDφ, ContinuousLinearMap.prod_apply, hξ, hκ]
    have hκ0 : κ ≠ 0 := by
      intro h0
      rw [h0] at hEξ
      have : ((ξ, 0) : (Fin N → ℝ) × (Fin M → ℝ)) = 0 :=
        Ew.injective (hEξ.trans (by rw [map_zero]; rfl))
      exact hξ0 (congrArg Prod.fst this)
    have hker : Dk κ = 0 := by
      have : Ew.symm (0, κ) = (ξ, 0) := by rw [← hEξ, ContinuousLinearEquiv.symm_apply_apply]
      simp only [hDk, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
        zero_apply, ContinuousLinearMap.id_apply,
        ContinuousLinearEquiv.coe_coe, this, ContinuousLinearMap.coe_snd']
    rw [ContinuousLinearMap.det, LinearMap.det_eq_zero_iff_ker_ne_bot]
    intro hbot
    apply hκ0
    have hmem : κ ∈ LinearMap.ker Dk.toLinearMap := hker
    rw [hbot] at hmem
    exact hmem
  choose! D hD hdet using hderiv
  exact addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume
    (fun k hk => (hD k hk).hasFDerivWithinAt) hdet

/-- **Theorem M.E.2 (transversality theorem)** (MWG, p. 943). Let `A ⊆ ℝ^N` and `B ⊆ ℝ^M` be open
and `f : A × B → ℝ^N` continuously differentiable, with `Df(x; q)` of rank `N` (onto `ℝ^N`)
whenever `f(x; q) = 0`. Then the set of `q ∈ B` at which `f(·; q) = 0` is not regular (some
`x ∈ A` solves it with `D_x f(x; q)` singular) has Lebesgue measure zero. -/
theorem theorem_M_E_2 {N M : ℕ} {A : Set (Fin N → ℝ)} {B : Set (Fin M → ℝ)} (hA : IsOpen A)
    (hB : IsOpen B) {f : (Fin N → ℝ) × (Fin M → ℝ) → (Fin N → ℝ)}
    (hf : ContDiffOn ℝ 1 f (A ×ˢ B))
    (hrank : ∀ p ∈ A ×ˢ B, f p = 0 → (fderiv ℝ f p).range = ⊤) :
    volume {q | q ∈ B ∧ ∃ x ∈ A, f (x, q) = 0 ∧
      ¬ ((fderiv ℝ f (x, q)).comp (ContinuousLinearMap.inl ℝ _ _)).IsInvertible} = 0 := by
  have hU : IsOpen (A ×ˢ B) := hA.prod hB
  choose S hSo hpS hnull using fun z : {p : (Fin N → ℝ) × (Fin M → ℝ) // p ∈ A ×ˢ B ∧ f p = 0} =>
    hardSard_local hU hf z.2.1 (hrank z.1 z.2.1 z.2.2)
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable S hSo
  refine measure_mono_null (fun q hq => ?_) ((measure_biUnion_null_iff hTc).mpr fun z _ => hnull z)
  obtain ⟨hqB, x, hxA, hf0, hbad⟩ := hq
  have hz : (x, q) ∈ ⋃ z, S z := Set.mem_iUnion.mpr ⟨⟨(x, q), ⟨hxA, hqB⟩, hf0⟩, hpS _⟩
  rw [← hTU] at hz
  obtain ⟨z, hzT, hxz⟩ := Set.mem_iUnion₂.mp hz
  exact Set.mem_iUnion₂.mpr ⟨z, hzT, x, hxz, ⟨hxA, hqB⟩, hf0, hbad⟩

/-- **Theorem M.E.2** (MWG, p. 943), "almost every" form: under the hypotheses of
`theorem_M_E_2`, for almost every `q`, if `q ∈ B` then every solution `x ∈ A` of `f(x; q) = 0`
has `D_x f(x; q)` invertible. -/
theorem theorem_M_E_2_ae {N M : ℕ} {A : Set (Fin N → ℝ)} {B : Set (Fin M → ℝ)} (hA : IsOpen A)
    (hB : IsOpen B) {f : (Fin N → ℝ) × (Fin M → ℝ) → (Fin N → ℝ)}
    (hf : ContDiffOn ℝ 1 f (A ×ˢ B))
    (hrank : ∀ p ∈ A ×ˢ B, f p = 0 → (fderiv ℝ f p).range = ⊤) :
    ∀ᵐ q, q ∈ B → ∀ x ∈ A, f (x, q) = 0 →
      ((fderiv ℝ f (x, q)).comp (ContinuousLinearMap.inl ℝ _ _)).IsInvertible := by
  rw [ae_iff]
  refine measure_mono_null (fun q hq => ?_) (theorem_M_E_2 hA hB hf hrank)
  change ¬ (q ∈ B → ∀ x ∈ A, f (x, q) = 0 → _) at hq
  push Not at hq
  exact hq

/-- **Theorem M.E.2** (MWG, p. 943) with `A = ℝ^N`, `B = ℝ^M`, in terms of Definition M.E.2: if
`f` is `C¹` and `Df(x; q)` is onto whenever `f(x; q) = 0`, then `f(·; q) = 0` is regular
(`RegularSystemAt`) for almost every `q`. -/
theorem theorem_M_E_2_regular {N M : ℕ} {f : (Fin N → ℝ) × (Fin M → ℝ) → (Fin N → ℝ)}
    (hf : ContDiff ℝ 1 f) (hrank : ∀ p, f p = 0 → (fderiv ℝ f p).range = ⊤) :
    ∀ᵐ q, RegularSystemAt f q := by
  filter_upwards [theorem_M_E_2_ae isOpen_univ isOpen_univ hf.contDiffOn
    (fun p _ hp => hrank p hp)] with q hq
  exact fun x hx => hq trivial x trivial hx

end MWG.ClassicalDemand
