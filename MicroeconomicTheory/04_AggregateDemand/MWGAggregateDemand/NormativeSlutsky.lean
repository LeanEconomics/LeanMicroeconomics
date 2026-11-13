/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGAggregateDemand.Representative
import MWGClassicalDemand.AppendixMJ

/-!
# The necessary condition `A ⊆ B` and the Slutsky matrices

MWG, Section 4.D, pp. 120-121, and Exercise 4.D.9 (p. 126).

`exercise_4_D_9`: if the at-least-as-good set `B` of a (positive) representative consumer
contains the Scitovsky set `A = {∑ᵢ xᵢ : uᵢ(xᵢ) ≥ uᵢ(x̄ᵢ)}` at `x̄ = x(p̄, w̄) = ∑ᵢ x̄ᵢ`, then
`S(p̄, w̄) - ∑ᵢ Sᵢ(p̄, w̄ᵢ)` is negative semidefinite: the function
`g(p) = e(p, u(x̄)) - ∑ᵢ eᵢ(p, uᵢ(x̄ᵢ))` is `≤ 0` with `g(p̄) = 0`, so its Hessian
`S - ∑ᵢ Sᵢ` (Shephard's lemma and the Slutsky equation, MWG Chapter 3) is negative
semidefinite at the maximum (Theorem M.J.2). Equivalently `C(p̄, w̄)` is positive semidefinite
(p. 121): a necessary condition for a normative representative consumer.
-/

namespace MWG.AggregateDemand

open MWG.ConsumerChoice MWG.ClassicalDemand Filter Topology

variable {L I : ℕ}

/-- A Hicksian demand selection at every `q ≫ 0` for an attainable utility level. -/
theorem exists_hicksian_selection {u : (Fin L → ℝ) → ℝ} (hu : ContinuousOn u (nonnegOrthant L))
    {ub : ℝ} (hne : ∃ x ∈ nonnegOrthant L, ub ≤ u x) :
    ∃ hf : (Fin L → ℝ) → (Fin L → ℝ), ∀ q, StrictlyPositive q → hf q ∈ hicksianDemand u q ub := by
  have hsel : ∀ q, ∃ y, StrictlyPositive q → y ∈ hicksianDemand u q ub := by
    intro q
    by_cases hq : StrictlyPositive q
    · obtain ⟨y, hy⟩ := exercise_3_E_3 hu hq hne
      exact ⟨y, fun _ => hy⟩
    · exact ⟨0, fun h => absurd h hq⟩
  choose hf hhf using hsel
  exact ⟨hf, hhf⟩

/-- **Exercise 4.D.9** (MWG, p. 126; claim on p. 121). Let the representative utility `u` and the
individual utilities `uᵢ` be continuous on `ℝ^L_+`, representing locally nonsatiated, strictly
convex preferences, with demand functions `x_R`, `xᵢ` differentiable at `(p̄, w̄)`,
`(p̄, w̄ᵢ)` and `∑ᵢ w̄ᵢ = w̄` (in the book `x_R(p̄, w̄) = ∑ᵢ xᵢ(p̄, w̄ᵢ)`; the proof does not
need it). If `A ⊆ B`, i.e. every
`∑ᵢ yᵢ` with `yᵢ ≥ 0`, `uᵢ(yᵢ) ≥ uᵢ(x̄ᵢ)` has `u(∑ᵢ yᵢ) ≥ u(x̄)`, then
`S(p̄, w̄) - ∑ᵢ Sᵢ(p̄, w̄ᵢ)` is negative semidefinite. -/
theorem exercise_4_D_9 {u : (Fin L → ℝ) → ℝ} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hrep : RepresentsOn (nonnegOrthant L) u r) (hu : ContinuousOn u (nonnegOrthant L))
    (hlns : LocallyNonsatiated (nonnegOrthant L) r) (hsc : PrefStrictlyConvex (nonnegOrthant L) r)
    {us : Fin I → (Fin L → ℝ) → ℝ} {rs : Fin I → (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hrepi : ∀ i, RepresentsOn (nonnegOrthant L) (us i) (rs i))
    (hui : ∀ i, ContinuousOn (us i) (nonnegOrthant L))
    (hlnsi : ∀ i, LocallyNonsatiated (nonnegOrthant L) (rs i))
    (hsci : ∀ i, PrefStrictlyConvex (nonnegOrthant L) (rs i)) {xR : DemandFunction L}
    (hxR : ∀ p w, PWDomain p w → xR p w ∈ walrasianDemand u p w)
    {xs : Fin I → DemandFunction L}
    (hxs : ∀ i p w, PWDomain p w → xs i p w ∈ walrasianDemand (us i) p w) {pb : Fin L → ℝ}
    {wb : ℝ} {wbs : Fin I → ℝ} (hd : PWDomain pb wb) (hwi : ∀ i, 0 < wbs i)
    (hsum : ∑ i, wbs i = wb)
    (hAB : ∀ ys : Fin I → Fin L → ℝ, (∀ i, ys i ∈ nonnegOrthant L) →
      (∀ i, us i (xs i pb (wbs i)) ≤ us i (ys i)) → u (xR pb wb) ≤ u (∑ i, ys i))
    {DR : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)}
    (hDR : HasFDerivAt (Function.uncurry xR) DR (pb, wb))
    {D : Fin I → ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)}
    (hD : ∀ i, HasFDerivAt (Function.uncurry (xs i)) (D i) (pb, wbs i)) :
    NegSemidef (slutskyMatrix DR (xR pb wb) - ∑ i, slutskyMatrix (D i) (xs i pb (wbs i))) := by
  have hdi : ∀ i, PWDomain pb (wbs i) := fun i => ⟨hd.1, hwi i⟩
  set ub := indirectUtility u pb wb with hub
  set ubs : Fin I → ℝ := fun i => indirectUtility (us i) pb (wbs i) with hubs
  have hq := (prefStrictlyConvex_iff_strictlyQuasiconcaveOn (convex_nonnegOrthant L) hrep).mp hsc
  have hqi : ∀ i, StrictlyQuasiconcaveOn (nonnegOrthant L) (us i) := fun i =>
    (prefStrictlyConvex_iff_strictlyQuasiconcaveOn (convex_nonnegOrthant L) (hrepi i)).mp (hsci i)
  have hubx : ub = u (xR pb wb) := indirectUtility_eq_of_mem (hxR pb wb hd)
  have hubxi : ∀ i, ubs i = us i (xs i pb (wbs i)) :=
    fun i => indirectUtility_eq_of_mem (hxs i pb _ (hdi i))
  have hne : ∃ x ∈ nonnegOrthant L, ub ≤ u x := ⟨xR pb wb, (hxR pb wb hd).1.1, hubx.le⟩
  have hnei : ∀ i, ∃ x ∈ nonnegOrthant L, ubs i ≤ us i x :=
    fun i => ⟨xs i pb (wbs i), (hxs i pb _ (hdi i)).1.1, (hubxi i).le⟩
  obtain ⟨hf, hhf⟩ := exists_hicksian_selection hu hne
  have hsel := fun i => exists_hicksian_selection (hui i) (hnei i)
  choose hfi hhfi using hsel
  -- derivatives of the Hicksian demands: the Slutsky matrices (Proposition 3.G.3)
  obtain ⟨hHR, hjR⟩ := proposition_3_G_3 hrep hu hlns hsc hxR hd hDR hhf
  have hHi := fun i => proposition_3_G_3 (hrepi i) (hui i) (hlnsi i) (hsci i) (hxs i) (hdi i)
    (hD i) (hhfi i)
  set H : (Fin L → ℝ) → (Fin L → ℝ) := fun q => hf q - ∑ i, hfi i q with hH
  set DRc := DR.comp ((ContinuousLinearMap.id ℝ (Fin L → ℝ)).prod (dualityDotCLM (xR pb wb)))
  set Dic : Fin I → (Fin L → ℝ) →L[ℝ] (Fin L → ℝ) := fun i => (D i).comp
    ((ContinuousLinearMap.id ℝ (Fin L → ℝ)).prod (dualityDotCLM (xs i pb (wbs i))))
  have hHd : HasFDerivAt H (DRc - ∑ i, Dic i) pb := by
    have hs := HasFDerivAt.sum (u := Finset.univ) fun i _ => (hHi i).1
    convert hHR.sub hs using 1
    funext q
    simp [H, Finset.sum_apply]
  -- `g(q) = e(q, ū) - ∑ᵢ eᵢ(q, ūᵢ)`
  set g : (Fin L → ℝ) → ℝ := fun q => expenditure u q ub - ∑ i, expenditure (us i) q (ubs i)
  have hgd : ∀ q, StrictlyPositive q → HasFDerivAt g (dualityDotCLM (H q)) q := by
    intro q hq'
    have h1 := shephard_lemma hu hq hq' (hhf q hq')
    have h2 := HasFDerivAt.sum (u := Finset.univ) fun i _ =>
      shephard_lemma (hui i) (hqi i) hq' (hhfi i q hq')
    have := h1.sub h2
    convert this using 1
    · funext q
      simp [g, Finset.sum_apply]
    · ext z
      simp [H, dualityDotCLM_apply, sub_dotProduct, sum_dotProduct]
  have hev : ∀ᶠ q in 𝓝 pb, StrictlyPositive q := relations_eventually_strictlyPositive hd.1
  have hdiff : ∀ᶠ q in 𝓝 pb, DifferentiableAt ℝ g q := by
    filter_upwards [hev] with q hq'
    exact (hgd q hq').differentiableAt
  have h2 : HasFDerivAt (fderiv ℝ g) (dualityDotLin.comp (DRc - ∑ i, Dic i)) pb := by
    have := dualityDotLin.hasFDerivAt.comp pb hHd
    apply this.congr_of_eventuallyEq
    filter_upwards [hev] with q hq'
    rw [(hgd q hq').fderiv]
    simp [dualityDotLin_apply]
  -- `g ≤ 0` near `p̄` and `g(p̄) = 0`
  have hgle : ∀ q, StrictlyPositive q → g q ≤ 0 := by
    intro q hq'
    have hmem : ∑ i, hfi i q ∈ empConstraintSet u ub := by
      have hys : ∀ i, hfi i q ∈ nonnegOrthant L := fun i => (hhfi i q hq').1.1
      refine ⟨fun l => ?_, ?_⟩
      · simp only [Finset.sum_apply]
        exact Finset.sum_nonneg fun i _ => hys i l
      · rw [hubx]
        exact hAB _ hys fun i => (hubxi i) ▸ (hhfi i q hq').1.2
    have hle : expenditure u q ub ≤ q ⬝ᵥ ∑ i, hfi i q := by
      have := supportFn_le (exp_bddBelow hq' ub) hmem
      exact this
    have hsumE : q ⬝ᵥ ∑ i, hfi i q = ∑ i, expenditure (us i) q (ubs i) := by
      rw [dotProduct_sum]
      exact Finset.sum_congr rfl fun i _ => (expenditure_eq_of_mem (hhfi i q hq')).symm
    simp only [g]
    linarith
  have hg0 : g pb = 0 := by
    simp only [g]
    rw [hub, equation_3_E_1_left hrep hu hlns hd.1 hd.2.le]
    rw [Finset.sum_congr rfl fun i _ =>
      equation_3_E_1_left (hrepi i) (hui i) (hlnsi i) hd.1 (hwi i).le, hsum, sub_self]
  have hmax : IsLocalMax g pb := by
    filter_upwards [hev] with q hq'
    rw [hg0]
    exact hgle q hq'
  have hnsd := theorem_M_J_2_i hmax hdiff h2
  intro z
  have hz := hnsd z
  rw [hessianMatrix_quad] at hz
  simp only [ContinuousLinearMap.comp_apply, dualityDotLin_apply, dualityDotCLM_apply] at hz
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.sum_mulVec, dotProduct_sum, ← hjR,
    jacobian_mulVec, Finset.sum_congr rfl fun i _ => by rw [← (hHi i).2, jacobian_mulVec]]
  simp only [sub_apply, FunLike.coe_sum, Finset.sum_apply,
    sub_dotProduct, sum_dotProduct] at hz
  rw [dotProduct_comm z (DRc z)]
  simp only [dotProduct_comm z] at *
  linarith

end MWG.AggregateDemand
