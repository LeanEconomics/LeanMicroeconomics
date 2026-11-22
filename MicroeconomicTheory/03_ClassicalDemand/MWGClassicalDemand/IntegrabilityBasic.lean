/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGClassicalDemand.RelationsBasic
import MWGClassicalDemand.AppendixMC
import MWGClassicalDemand.ExpContinuity

/-!
# Integrability: recovering preferences from the expenditure function

MWG, Section 3.H, pp. 75-78 ("Recovering Preferences from the Expenditure Function").

* `recoveredSet E` is the book's at-least-as-good set `V_u = {x ∈ ℝ^L_+ : p·x ≥ e(p, u) for all
  p ≫ 0}` for the function `E = e(·, u)`.
* Proposition 3.H.1: if `E` is concave, homogeneous of degree one and nondecreasing on `p ≫ 0`
  and differentiable at `p̄ ≫ 0`, then `∇E(p̄) ∈ V_u` and `E(p̄) = p̄·∇E(p̄) = min {p̄·x : x ∈ V_u}`
  (`proposition_3_H_1`). Strict monotonicity in `u` and continuity are not needed.
* The small-type remark on p. 78 (the proposition holds without differentiability) is proved for
  `E` continuous on `p ≫ 0` through a supergradient (`integ_exists_supergradient`,
  `proposition_3_H_1_general`), and `V_u` generates the expenditure function of any continuous
  utility (`recoveredSet_generates_expenditure`).
* The claims after the proposition (p. 77): `V_u` is closed, convex and bounded below, and
  `V_{u'} ⊊ V_u` for `u' > u`.

The recovered utility (Exercise 3.H.1) is in `IntegrabilityUtility`; the closed-convex-hull remark
of p. 78 and Exercise 3.H.2 are in `IntegrabilityExercises`.
-/

namespace MWG.ClassicalDemand

open MWG.ConsumerChoice Kreps.PreferenceProperties Filter Topology

variable {L : ℕ}

/-- **Section 3.H** (MWG, p. 77). The at-least-as-good set recovered from `E = e(·, u)`:
`V_u = {x ∈ ℝ^L_+ : p·x ≥ e(p, u) for all p ≫ 0}`. -/
def recoveredSet (E : (Fin L → ℝ) → ℝ) : Set (Fin L → ℝ) :=
  {x | x ∈ nonnegOrthant L ∧ ∀ p, StrictlyPositive p → E p ≤ p ⬝ᵥ x}

/-- Homogeneity of degree one on `p ≫ 0`: `E(αp) = αE(p)` for `α > 0`. -/
def HD1OnPos (E : (Fin L → ℝ) → ℝ) : Prop :=
  ∀ p, StrictlyPositive p → ∀ α : ℝ, 0 < α → E (α • p) = α * E p

/-- `E` is nondecreasing on `p ≫ 0`: `p ≤ q` implies `E(p) ≤ E(q)`. -/
def MonotoneOnPos (E : (Fin L → ℝ) → ℝ) : Prop :=
  ∀ p q, StrictlyPositive p → p ≤ q → E p ≤ E q

/-- The set `{p : p ≫ 0}` of strictly positive price vectors. -/
def posPrices (L : ℕ) : Set (Fin L → ℝ) := {p | StrictlyPositive p}

/-- A vector `≥` a strictly positive one is strictly positive. -/
theorem integ_strictlyPositive_of_le {p q : Fin L → ℝ} (hp : StrictlyPositive p) (h : p ≤ q) :
    StrictlyPositive q := fun l => (hp l).trans_le (h l)

/-- A linear functional applied to a vector is the dot product with its gradient. -/
theorem integ_apply_eq_dot (f : (Fin L → ℝ) →L[ℝ] ℝ) (z : Fin L → ℝ) :
    f z = gradientVec f ⬝ᵥ z := by
  conv_lhs => rw [← dualityDotCLM_gradientVec f]
  rw [dualityDotCLM_apply]

/-- **Section M.C** (MWG, p. 931), the pointwise form of Theorem M.C.1 used in the proof of
Proposition 3.H.1: a concave `E` on a convex set `A`, differentiable at `p ∈ A`, satisfies
`E(p') ≤ E(p) + ∇E(p)·(p' - p)` for every `p' ∈ A`. -/
theorem integ_concave_le_tangent {A : Set (Fin L → ℝ)} {E : (Fin L → ℝ) → ℝ}
    {E' : (Fin L → ℝ) →L[ℝ] ℝ} (hc : ConcaveOn ℝ A E) {p p' : Fin L → ℝ} (hp : p ∈ A)
    (hp' : p' ∈ A) (hd : HasFDerivAt E E' p) : E p' ≤ E p + E' (p' - p) := by
  have hdl := mc_line_hasDerivAt hd (p' - p)
  have key : E p' - E p ≤ E' (p' - p) := by
    apply mc_le_deriv_of_slope hdl
    intro t ht0 ht1
    have hconc := hc.2 hp' hp ht0.le (by linarith : (0 : ℝ) ≤ 1 - t) (by ring)
    have heq : t • p' + (1 - t) • p = p + t • (p' - p) := by module
    rw [heq, smul_eq_mul, smul_eq_mul] at hconc
    simp only [zero_smul, add_zero]
    rw [le_div_iff₀ ht0]
    linarith
  linarith

/-- **Euler's formula** (MWG, p. 77, proof of Proposition 3.H.1). If `E` is homogeneous of
degree one on `p ≫ 0` and differentiable at `p ≫ 0`, then `∇E(p)·p = E(p)`. -/
theorem integ_euler {E : (Fin L → ℝ) → ℝ} {E' : (Fin L → ℝ) →L[ℝ] ℝ} (hh : HD1OnPos E)
    {p : Fin L → ℝ} (hp : StrictlyPositive p) (hd : HasFDerivAt E E' p) : E' p = E p := by
  have h1 : HasDerivAt (fun t : ℝ => E (t • p)) (E' p) 1 := by
    have hl : HasDerivAt (fun t : ℝ => t • p) p 1 := by
      simpa using (hasDerivAt_id (1 : ℝ)).smul_const p
    have hd' : HasFDerivAt E E' ((1 : ℝ) • p) := by simpa using hd
    exact hd'.comp_hasDerivAt (1 : ℝ) hl
  have h2 : HasDerivAt (fun t : ℝ => t * E p) (E p) 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).mul_const (E p)
  have heq : (fun t : ℝ => E (t • p)) =ᶠ[𝓝 1] fun t => t * E p := by
    filter_upwards [lt_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with t ht
    exact hh p hp t ht
  exact (h1.congr_of_eventuallyEq heq.symm).unique h2

/-- **Section 3.H** (MWG, p. 77). A nondecreasing `E`, differentiable at `p ≫ 0`, has a
nonnegative gradient there. -/
theorem integ_gradient_nonneg {E : (Fin L → ℝ) → ℝ} {E' : (Fin L → ℝ) →L[ℝ] ℝ}
    (hm : MonotoneOnPos E) {p : Fin L → ℝ} (hp : StrictlyPositive p) (hd : HasFDerivAt E E' p)
    (l : Fin L) : 0 ≤ gradientVec E' l := by
  have hdl := mc_line_hasDerivAt hd (Pi.single l 1)
  apply mc_le_deriv_of_slope hdl
  intro t ht0 _
  have hle : p ≤ p + t • (Pi.single l 1 : Fin L → ℝ) := by
    intro k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have : 0 ≤ (Pi.single l (1 : ℝ) : Fin L → ℝ) k := by
      rw [Pi.single_apply]; split_ifs <;> norm_num
    nlinarith
  have := hm p _ hp hle
  simp only [zero_smul, add_zero]
  exact div_nonneg (by linarith) ht0.le

/-- The supergradient step of the proof of Proposition 3.H.1 (MWG, p. 77). If `g` is a
supergradient of `E` at `p ≫ 0` (on `p ≫ 0`), and `E` is homogeneous of degree one and
nondecreasing, then `g ∈ V_u` and `p·g = E(p)`. -/
theorem integ_supergradient_mem {E : (Fin L → ℝ) → ℝ} (hh : HD1OnPos E) (hm : MonotoneOnPos E)
    {p g : Fin L → ℝ} (hp : StrictlyPositive p)
    (hg : ∀ q, StrictlyPositive q → E q ≤ E p + g ⬝ᵥ (q - p)) :
    g ∈ recoveredSet E ∧ p ⬝ᵥ g = E p := by
  have h2 := hg ((2 : ℝ) • p) (fun l => by
    simp only [Pi.smul_apply, smul_eq_mul]; nlinarith [hp l])
  have hh2 := hh p hp 2 (by norm_num)
  have hhalf := hg ((1 / 2 : ℝ) • p) (fun l => by
    simp only [Pi.smul_apply, smul_eq_mul]; nlinarith [hp l])
  have hhh := hh p hp (1 / 2) (by norm_num)
  rw [hh2, dotProduct_sub, dotProduct_smul, smul_eq_mul] at h2
  rw [hhh, dotProduct_sub, dotProduct_smul, smul_eq_mul] at hhalf
  have hpg : p ⬝ᵥ g = E p := by
    rw [dotProduct_comm]
    linarith
  refine ⟨⟨fun l => ?_, fun q hq => ?_⟩, hpg⟩
  · have hle : p ≤ p + Pi.single l 1 := by
      intro k
      simp only [Pi.add_apply]
      have : 0 ≤ (Pi.single l (1 : ℝ) : Fin L → ℝ) k := by
        rw [Pi.single_apply]; split_ifs <;> norm_num
      linarith
    have h1 := hm p _ hp hle
    have h3 := hg _ (integ_strictlyPositive_of_le hp hle)
    rw [add_sub_cancel_left] at h3
    have : g ⬝ᵥ Pi.single l 1 = g l := by simp
    linarith
  · have := hg q hq
    rw [dotProduct_sub] at this
    rw [dotProduct_comm] at hpg
    rw [dotProduct_comm]
    linarith

/-- **Proposition 3.H.1** (MWG, p. 77). Let `E = e(·, u)` be concave, homogeneous of degree one
and nondecreasing on `p ≫ 0`, and differentiable at `p ≫ 0`. Then `∇E(p) ∈ V_u` and
`E(p) = p·∇E(p) = min {p·x : x ∈ V_u}`. (Differentiability is used only at `p`; strict
monotonicity in `u` and continuity are not needed.) -/
theorem proposition_3_H_1 {E : (Fin L → ℝ) → ℝ} {E' : (Fin L → ℝ) →L[ℝ] ℝ}
    (hc : ConcaveOn ℝ (posPrices L) E) (hh : HD1OnPos E) (hm : MonotoneOnPos E)
    {p : Fin L → ℝ} (hp : StrictlyPositive p) (hd : HasFDerivAt E E' p) :
    gradientVec E' ∈ supportArgmin (recoveredSet E) p ∧
      E p = p ⬝ᵥ gradientVec E' ∧ supportFn (recoveredSet E) p = E p := by
  have hg : ∀ q, StrictlyPositive q → E q ≤ E p + gradientVec E' ⬝ᵥ (q - p) := by
    intro q hq
    have := integ_concave_le_tangent hc hp hq hd
    rwa [integ_apply_eq_dot] at this
  obtain ⟨hmem, hpg⟩ := integ_supergradient_mem hh hm hp hg
  have hargmin : gradientVec E' ∈ supportArgmin (recoveredSet E) p :=
    ⟨hmem, fun y hy => hpg ▸ hy.2 p hp⟩
  exact ⟨hargmin, hpg.symm, (supportFn_eq_of_mem_argmin hargmin).trans hpg⟩

/-- A concave function that is continuous on `p ≫ 0` has a supergradient at every `p ≫ 0`
(via the Hahn-Banach separation of `(p, E(p))` from the open strict hypograph). -/
theorem integ_exists_supergradient {E : (Fin L → ℝ) → ℝ} (hc : ConcaveOn ℝ (posPrices L) E)
    (hcont : ContinuousOn E (posPrices L)) {p : Fin L → ℝ} (hp : StrictlyPositive p) :
    ∃ g : Fin L → ℝ, ∀ q, StrictlyPositive q → E q ≤ E p + g ⬝ᵥ (q - p) := by
  set S : Set ((Fin L → ℝ) × ℝ) := {z | StrictlyPositive z.1 ∧ z.2 < E z.1} with hS
  have hSc : Convex ℝ S := by
    intro z hz z' hz' a b ha hb hab
    refine ⟨exp_convex_strictlyPositive L hz.1 hz'.1 ha hb hab, ?_⟩
    have hconc := hc.2 hz.1 hz'.1 ha hb hab
    simp only [Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, smul_eq_mul] at hconc ⊢
    rcases ha.lt_or_eq with ha' | ha'
    · nlinarith [hz.2, hz'.2, mul_lt_mul_of_pos_left hz.2 ha',
        mul_le_mul_of_nonneg_left hz'.2.le hb]
    · subst ha'
      have hb1 : b = 1 := by linarith
      subst hb1
      simp only [zero_mul, zero_add, one_mul] at hconc ⊢
      simp only [zero_smul, one_smul, zero_add] at hconc ⊢
      exact hz'.2
  have hPo : IsOpen {z : (Fin L → ℝ) × ℝ | StrictlyPositive z.1} :=
    (relations_isOpen_strictlyPositive L).preimage continuous_fst
  have hgc : ContinuousOn (fun z : (Fin L → ℝ) × ℝ => E z.1 - z.2)
      {z : (Fin L → ℝ) × ℝ | StrictlyPositive z.1} :=
    (hcont.comp continuousOn_fst fun z hz => hz).sub continuousOn_snd
  have hSo : IsOpen S := by
    have := hgc.isOpen_inter_preimage hPo (isOpen_Ioi (a := (0 : ℝ)))
    convert this using 1
    ext z
    simp [hS, sub_pos]
  have hpS : ((p, E p) : (Fin L → ℝ) × ℝ) ∉ S := fun h => lt_irrefl _ h.2
  obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hSc hSo hpS
  have hsplit : ∀ q : Fin L → ℝ, ∀ t : ℝ, f (q, t) = f (q, 0) + t * f (0, 1) := by
    intro q t
    have : ((q, t) : (Fin L → ℝ) × ℝ) = (q, 0) + t • ((0 : Fin L → ℝ), (1 : ℝ)) := by
      ext <;> simp
    rw [this, map_add, map_smul, smul_eq_mul]
  set c := f (0, 1) with hcdef
  have hc0 : 0 < c := by
    have := hf (p, E p - 1) ⟨hp, by linarith⟩
    rw [hsplit, hsplit p (E p)] at this
    nlinarith
  set a : (Fin L → ℝ) →L[ℝ] ℝ := f.comp (ContinuousLinearMap.inl ℝ (Fin L → ℝ) ℝ) with ha
  have haq : ∀ q, a q = f (q, 0) := fun q => rfl
  refine ⟨-(1 / c) • gradientVec a, fun q hq => ?_⟩
  have key : E q ≤ (f (p, 0) + E p * c - f (q, 0)) / c := by
    apply le_of_forall_lt
    intro t ht
    have := hf (q, t) ⟨hq, ht⟩
    rw [hsplit, hsplit p (E p)] at this
    rw [lt_div_iff₀ hc0]
    linarith
  have hdot : (-(1 / c) • gradientVec a) ⬝ᵥ (q - p) = (f (p, 0) - f (q, 0)) / c := by
    rw [smul_dotProduct, ← integ_apply_eq_dot, map_sub, haq, haq, smul_eq_mul]
    field_simp
    ring
  rw [hdot]
  have : (f (p, 0) + E p * c - f (q, 0)) / c = E p + (f (p, 0) - f (q, 0)) / c := by
    field_simp
    ring
  linarith

/-- **Proposition 3.H.1 without differentiability** (MWG, p. 78, small type). If `E = e(·, u)`
is continuous, concave, homogeneous of degree one and nondecreasing on `p ≫ 0`, then for every
`p ≫ 0` the minimum of `p·x` over `V_u` exists and equals `E(p)`. -/
theorem proposition_3_H_1_general {E : (Fin L → ℝ) → ℝ} (hc : ConcaveOn ℝ (posPrices L) E)
    (hcont : ContinuousOn E (posPrices L)) (hh : HD1OnPos E) (hm : MonotoneOnPos E)
    {p : Fin L → ℝ} (hp : StrictlyPositive p) :
    (supportArgmin (recoveredSet E) p).Nonempty ∧ supportFn (recoveredSet E) p = E p := by
  obtain ⟨g, hg⟩ := integ_exists_supergradient hc hcont hp
  obtain ⟨hmem, hpg⟩ := integ_supergradient_mem hh hm hp hg
  have hargmin : g ∈ supportArgmin (recoveredSet E) p := ⟨hmem, fun y hy => hpg ▸ hy.2 p hp⟩
  exact ⟨⟨g, hargmin⟩, (supportFn_eq_of_mem_argmin hargmin).trans hpg⟩

/-- **Section 3.H** (MWG, p. 77). `V_u` is closed. -/
theorem isClosed_recoveredSet (E : (Fin L → ℝ) → ℝ) : IsClosed (recoveredSet E) := by
  have : recoveredSet E = nonnegOrthant L ∩
      ⋂ p ∈ posPrices L, {x : Fin L → ℝ | E p ≤ p ⬝ᵥ x} := by
    ext x
    simp [recoveredSet, posPrices]
  rw [this]
  refine (exp_isClosed_nonnegOrthant L).inter (isClosed_biInter fun p _ => ?_)
  exact isClosed_le continuous_const (by fun_prop)

/-- **Section 3.H** (MWG, p. 77). `V_u` is convex. -/
theorem convex_recoveredSet (E : (Fin L → ℝ) → ℝ) : Convex ℝ (recoveredSet E) := by
  intro x hx y hy a b ha hb hab
  refine ⟨convex_nonnegOrthant L hx.1 hy.1 ha hb hab, fun p hp => ?_⟩
  rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  have h1 := hx.2 p hp
  have h2 := hy.2 p hp
  have h3 : a * E p + b * E p = E p := by rw [← add_mul, hab, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]

/-- **Section 3.H** (MWG, p. 77). `V_u` is bounded below (it lies in `ℝ^L_+`). -/
theorem recoveredSet_subset_orthant (E : (Fin L → ℝ) → ℝ) :
    recoveredSet E ⊆ nonnegOrthant L := fun _ hx => hx.1

/-- `V_u` is closed upward in `ℝ^L_+`: `x ∈ V_u` and `y ≥ x` give `y ∈ V_u`. -/
theorem recoveredSet_upward {E : (Fin L → ℝ) → ℝ} {x y : Fin L → ℝ} (hx : x ∈ recoveredSet E)
    (hxy : x ≤ y) : y ∈ recoveredSet E :=
  ⟨fun l => (hx.1 l).trans (hxy l), fun p hp =>
    (hx.2 p hp).trans (dotProduct_le_dotProduct_of_nonneg_left hxy fun l => (hp l).le)⟩

/-- **Section 3.H** (MWG, p. 77). If `e` is nondecreasing in `u`, then `u ≤ u'` gives
`V_{u'} ⊆ V_u`. -/
theorem recoveredSet_antitone {E : (Fin L → ℝ) → ℝ → ℝ} {u u' : ℝ}
    (hmono : ∀ p, StrictlyPositive p → E p u ≤ E p u') :
    recoveredSet (fun p => E p u') ⊆ recoveredSet (fun p => E p u) :=
  fun _ hx => ⟨hx.1, fun p hp => (hmono p hp).trans (hx.2 p hp)⟩

/-- **Section 3.H** (MWG, p. 77). If `e` is strictly increasing in `u` and `e(·, u)` has the
properties of Proposition 3.H.1 and is differentiable at some `p ≫ 0`, then `u < u'` gives
`V_{u'} ⊊ V_u`. -/
theorem recoveredSet_ssubset {E : (Fin L → ℝ) → ℝ → ℝ} {u u' : ℝ}
    (hmono : ∀ p, StrictlyPositive p → E p u < E p u')
    (hc : ConcaveOn ℝ (posPrices L) fun p => E p u) (hh : HD1OnPos fun p => E p u)
    (hm : MonotoneOnPos fun p => E p u) {p : Fin L → ℝ} (hp : StrictlyPositive p)
    {E' : (Fin L → ℝ) →L[ℝ] ℝ} (hd : HasFDerivAt (fun q => E q u) E' p) :
    recoveredSet (fun p => E p u') ⊂ recoveredSet (fun p => E p u) := by
  refine ⟨recoveredSet_antitone fun q hq => (hmono q hq).le, fun hsub => ?_⟩
  obtain ⟨hargmin, hval, -⟩ := proposition_3_H_1 hc hh hm hp hd
  have := (hsub hargmin.1).2 p hp
  have h2 := hmono p hp
  simp only at hval this
  linarith

/-- **Section 3.H** (MWG, pp. 77-78, Figure 3.H.1). If `x` lies in an expenditure-minimizing
set `K ⊆ ℝ^L_+` whose support function is `E`, then `x ∈ V_u`: the actual at-least-as-good set is
contained in `V_u`. -/
theorem subset_recoveredSet {K : Set (Fin L → ℝ)} (hK : K ⊆ nonnegOrthant L) :
    K ⊆ recoveredSet (supportFn K) := by
  intro x hx
  refine ⟨hK hx, fun p hp => supportFn_le ?_ hx⟩
  refine ⟨0, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  exact Finset.sum_nonneg fun l _ => mul_nonneg (hp l).le (hK hy l)

/-- **Section 3.H** (MWG, p. 78, small type). The expenditure function of any utility `u`
continuous on `ℝ^L_+` is generated by the convex set `V_u` as well: `V_u` contains the actual
at-least-as-good set `{x ≥ 0 : u(x) ≥ ū}`, and `min {p·x : x ∈ V_u} = e(p, ū)` for `p ≫ 0`
(for `ū` attainable, so that Proposition 3.E.2 applies). -/
theorem recoveredSet_generates_expenditure {u : (Fin L → ℝ) → ℝ}
    {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hrep : RepresentsOn (nonnegOrthant L) u r) (hu : ContinuousOn u (nonnegOrthant L))
    (hlns : LocallyNonsatiated (nonnegOrthant L) r) {ub : ℝ}
    (hne : ∃ x ∈ nonnegOrthant L, ub ≤ u x) {p : Fin L → ℝ} (hp : StrictlyPositive p) :
    empConstraintSet u ub ⊆ recoveredSet (fun q => expenditure u q ub) ∧
      (supportArgmin (recoveredSet fun q => expenditure u q ub) p).Nonempty ∧
      supportFn (recoveredSet fun q => expenditure u q ub) p = expenditure u p ub := by
  refine ⟨subset_recoveredSet fun _ hx => hx.1, ?_⟩
  have hcont : ContinuousOn (fun q => expenditure u q ub) (posPrices L) := by
    intro q hq
    have h := proposition_3_E_2_iv hrep hu hlns (q, ub) ⟨hq, hne⟩
    have hmap : Set.MapsTo (fun q : Fin L → ℝ => (q, ub)) (posPrices L) (expDomain u) :=
      fun q' hq' => ⟨hq', hne⟩
    exact ContinuousWithinAt.comp (g := fun z : (Fin L → ℝ) × ℝ => expenditure u z.1 z.2)
      (f := fun q : Fin L → ℝ => (q, ub)) h
      (continuous_id.prodMk continuous_const).continuousWithinAt hmap
  exact proposition_3_H_1_general (proposition_3_E_2_iii u ub) hcont
    (fun q _ α hα => proposition_3_E_2_i u q ub hα)
    (fun q q' hq hqq => proposition_3_E_2_ii_prices u hq hqq ub) hp

end MWG.ClassicalDemand
