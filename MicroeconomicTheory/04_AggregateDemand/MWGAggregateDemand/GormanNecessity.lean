/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGAggregateDemand.AggregateWealth
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Proposition 4.B.1: necessity of the Gorman form

MWG, Section 4.B, Proposition 4.B.1 (p. 107). The book proves only sufficiency (Exercise 4.B.1)
and tells the reader not to attempt necessity, citing Deaton and Muellbauer (1980). Here
necessity is proved for consumers with continuous, locally nonsatiated, strictly convex
preferences on `ℝ^L_+`.

If `xᵢ(p, w) = αᵢ(p) + w β(p)` for every `p ≫ 0`, `w > 0` (straight parallel expansion paths),
Shephard's lemma gives `∇ₚ eᵢ(p, u) = αᵢ(p) + eᵢ(p, u) β(p)`. Differences of expenditure
functions then satisfy `∇D = D β`, so every ratio of two of them has zero gradient on the open
convex set `ℝ^L_{++}` and is constant. Hence `eᵢ(p, u) - eᵢ(p, u⁰) = κᵢ(u) cᵢ(p)` with
`cᵢ = eᵢ(·, u¹) - eᵢ(·, u⁰) > 0`, and `κᵢ(vᵢ(p, w)) = (w - eᵢ(p, u⁰))/cᵢ(p)`: a Gorman form,
with `κᵢ` strictly increasing. Finally `cᵢ/c₁` is constant too, so after rescaling all
consumers share the coefficient `b(p) = 1/c₁(p)` of wealth.

* `ratio_const_of_grad`: two positive-orthant functions with gradients `f β` and `g β` have
  constant ratio.
* `expenditure_hasFDerivAt_linear_engel`: Shephard's lemma with linear Engel curves.
* `proposition_4_B_1_necessity`.
-/

namespace MWG.AggregateDemand

open MWG.ConsumerChoice MWG.ClassicalDemand Filter Topology

variable {L I : ℕ}

/-- The set of strictly positive price vectors is convex. -/
theorem convex_strictlyPositive (L : ℕ) : Convex ℝ {p : Fin L → ℝ | StrictlyPositive p} := by
  intro p hp q hq a b ha hb hab l
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rcases eq_or_lt_of_le ha with h | h
  · rw [← h] at hab ⊢
    simp only [zero_add] at hab
    rw [hab]
    simpa using hq l
  · exact add_pos_of_pos_of_nonneg (mul_pos h (hp l)) (mul_nonneg hb (hq l).le)

/-- **Proposition 4.B.1, necessity** (MWG, p. 107), the key lemma. If on `ℝ^L_{++}` the
functions `f` and `g` have gradients `f(q) β(q)` and `g(q) β(q)` and `g ≠ 0`, then `f/g` is
constant on `ℝ^L_{++}`. -/
theorem ratio_const_of_grad {f g : (Fin L → ℝ) → ℝ} {β : (Fin L → ℝ) → Fin L → ℝ}
    (hf : ∀ q, StrictlyPositive q → HasFDerivAt f (dualityDotCLM (f q • β q)) q)
    (hg : ∀ q, StrictlyPositive q → HasFDerivAt g (dualityDotCLM (g q • β q)) q)
    (hg0 : ∀ q, StrictlyPositive q → g q ≠ 0) {q q' : Fin L → ℝ} (hq : StrictlyPositive q)
    (hq' : StrictlyPositive q') : f q / g q = f q' / g q' := by
  have hderiv : ∀ r, StrictlyPositive r →
      HasFDerivAt (fun r => f r / g r) (0 : (Fin L → ℝ) →L[ℝ] ℝ) r := by
    intro r hr
    have hinv : HasFDerivAt (fun r => (g r)⁻¹)
        ((-(g r ^ 2)⁻¹) • dualityDotCLM (g r • β r)) r :=
      (hasDerivAt_inv (hg0 r hr)).comp_hasFDerivAt (f := g) r (hg r hr)
    have hm := (hf r hr).mul hinv
    convert hm using 1
    · funext r
      rw [div_eq_mul_inv, Pi.mul_apply]
    ext z
    have := hg0 r hr
    simp only [zero_apply, add_apply, smul_apply, dualityDotCLM_apply, smul_dotProduct,
      smul_eq_mul]
    field_simp
    ring
  have hopen := relations_isOpen_strictlyPositive L
  exact hopen.is_const_of_fderiv_eq_zero (convex_strictlyPositive L).isPreconnected
    (fun r hr => (hderiv r hr).differentiableAt.differentiableWithinAt)
    (fun r hr => (hderiv r hr).fderiv) hq hq'

/-- **Proposition 4.B.1, necessity** (MWG, p. 107), Shephard's lemma with straight expansion
paths. If demand is `x(p, w) = α(p) + w β(p)` on the domain, then for every utility level
`ū > u(0)` that some bundle attains, `∇ₚ e(p, ū) = α(p) + e(p, ū) β(p)` at every `p ≫ 0`. -/
theorem expenditure_hasFDerivAt_linear_engel {u : (Fin L → ℝ) → ℝ}
    {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop} (hrep : RepresentsOn (nonnegOrthant L) u r)
    (hu : ContinuousOn u (nonnegOrthant L)) (hlns : LocallyNonsatiated (nonnegOrthant L) r)
    (hsc : PrefStrictlyConvex (nonnegOrthant L) r) {xf : DemandFunction L}
    (hxf : ∀ p w, PWDomain p w → xf p w ∈ walrasianDemand u p w)
    {α β : (Fin L → ℝ) → Fin L → ℝ} (hlin : ∀ p w, PWDomain p w → xf p w = α p + w • β p)
    {ub : ℝ} (hub : u 0 < ub) (hne : ∃ x ∈ nonnegOrthant L, ub ≤ u x) {q : Fin L → ℝ}
    (hq : StrictlyPositive q) :
    HasFDerivAt (fun q => expenditure u q ub)
      (dualityDotCLM (α q + expenditure u q ub • β q)) q := by
  have hqc := (prefStrictlyConvex_iff_strictlyQuasiconcaveOn (convex_nonnegOrthant L) hrep).mp hsc
  have he := expenditure_pos_of_attainable hu hq hub hne
  have hmem : xf q (expenditure u q ub) ∈ hicksianDemand u q ub := by
    rw [equation_3_E_4_left hrep hu hlns hq hub hne]
    exact hxf q _ ⟨hq, he⟩
  have := shephard_lemma hu hqc hq hmem
  rwa [hlin q _ ⟨hq, he⟩] at this

/-- **Proposition 4.B.1, necessity** (MWG, p. 107). Suppose each consumer `i` has a utility `uᵢ`,
continuous on `ℝ^L_+`, representing a locally nonsatiated, strictly convex preference, and a
demand function `xᵢ` generated by it. If the consumers exhibit straight, parallel wealth
expansion paths at every `p ≫ 0` (`xᵢ(p, w) = aᵢ(p) + w b(p)`), then their preferences admit
indirect utility functions of the Gorman form with a common coefficient on wealth: there are
`Aᵢ` and `B > 0` such that `Aᵢ(p) + B(p) w` orders price-wealth pairs exactly as `vᵢ(p, w)`. -/
theorem proposition_4_B_1_necessity {us : Fin I → (Fin L → ℝ) → ℝ}
    {rs : Fin I → (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hrep : ∀ i, RepresentsOn (nonnegOrthant L) (us i) (rs i))
    (hu : ∀ i, ContinuousOn (us i) (nonnegOrthant L))
    (hlns : ∀ i, LocallyNonsatiated (nonnegOrthant L) (rs i))
    (hsc : ∀ i, PrefStrictlyConvex (nonnegOrthant L) (rs i)) {xs : Fin I → DemandFunction L}
    (hxs : ∀ i p w, PWDomain p w → xs i p w ∈ walrasianDemand (us i) p w)
    (hpar : ParallelLinearEngel xs) :
    ∃ (A : Fin I → (Fin L → ℝ) → ℝ) (B : (Fin L → ℝ) → ℝ), (∀ p, StrictlyPositive p → 0 < B p) ∧
      ∀ i p w p' w', PWDomain p w → PWDomain p' w' →
        (indirectUtility (us i) p w ≤ indirectUtility (us i) p' w' ↔
          A i p + B p * w ≤ A i p' + B p' * w') := by
  classical
  -- choose the expansion-path coefficients as functions
  have hex : ∀ p, ∃ a : Fin I → Fin L → ℝ, ∃ b : Fin L → ℝ,
      StrictlyPositive p → ∀ i w, 0 < w → xs i p w = a i + w • b := by
    intro p
    by_cases hp : StrictlyPositive p
    · obtain ⟨a, b, h⟩ := hpar p hp
      exact ⟨a, b, fun _ => h⟩
    · exact ⟨0, 0, fun h => absurd h hp⟩
  choose α β hαβ using hex
  have hlin : ∀ i p w, PWDomain p w → xs i p w = α p i + w • β p :=
    fun i p w hd => hαβ p hd.1 i w hd.2
  set pb : Fin L → ℝ := fun _ => 1 with hpb
  have hpbpos : StrictlyPositive pb := fun _ => one_pos
  -- reference utility levels `u⁰ = vᵢ(p̄, 1) < u¹ = vᵢ(p̄, 2)`
  set u0 : Fin I → ℝ := fun i => indirectUtility (us i) pb 1
  set u1 : Fin I → ℝ := fun i => indirectUtility (us i) pb 2
  have hatt : ∀ i p w, PWDomain p w → ∃ x ∈ nonnegOrthant L, indirectUtility (us i) p w ≤ us i x :=
    fun i p w hd => ⟨xs i p w, (hxs i p w hd).1.1, (indirectUtility_eq_of_mem (hxs i p w hd)).le⟩
  have hgt0 : ∀ i p w, PWDomain p w → us i 0 < indirectUtility (us i) p w :=
    fun i p w hd => relations_indirectUtility_gt_zero (hrep i) (hu i) (hlns i) hd.1 hd.2
  have hu01 : ∀ i, u0 i < u1 i := fun i =>
    proposition_3_D_3_ii_wealth (hrep i) (hu i) (hlns i) hpbpos zero_le_one one_lt_two
  set E : Fin I → ℝ → (Fin L → ℝ) → ℝ := fun i ub q => expenditure (us i) q ub
  have hgradE : ∀ i p w, PWDomain p w → ∀ q, StrictlyPositive q →
      HasFDerivAt (E i (indirectUtility (us i) p w))
        (dualityDotCLM (α q i + E i (indirectUtility (us i) p w) q • β q)) q :=
    fun i p w hd q hq => expenditure_hasFDerivAt_linear_engel (hrep i) (hu i) (hlns i) (hsc i)
      (hxs i) (α := fun q => α q i) (fun p w hd => hlin i p w hd) (hgt0 i p w hd) (hatt i p w hd) hq
  -- differences of expenditure functions have gradient `D β`
  have hgradD : ∀ i p w p' w', PWDomain p w → PWDomain p' w' → ∀ q, StrictlyPositive q →
      HasFDerivAt
        (fun q => E i (indirectUtility (us i) p w) q - E i (indirectUtility (us i) p' w') q)
        (dualityDotCLM ((E i (indirectUtility (us i) p w) q -
          E i (indirectUtility (us i) p' w') q) • β q)) q := by
    intro i p w p' w' hd hd' q hq
    have := (hgradE i p w hd q hq).sub (hgradE i p' w' hd' q hq)
    convert this using 1
    ext z
    simp [dualityDotCLM_apply, sub_smul, sub_dotProduct]
  have hd1 : PWDomain pb 1 := ⟨hpbpos, one_pos⟩
  have hd2 : PWDomain pb 2 := ⟨hpbpos, two_pos⟩
  -- `cᵢ = eᵢ(·, u¹) - eᵢ(·, u⁰) > 0`
  set c : Fin I → (Fin L → ℝ) → ℝ := fun i q => E i (u1 i) q - E i (u0 i) q with hc
  have hcpos : ∀ i q, StrictlyPositive q → 0 < c i q := by
    intro i q hq
    simp only [c, E, sub_pos]
    exact proposition_3_E_2_ii_utility (hu i) hq (hgt0 i pb 1 hd1) (hu01 i) (hatt i pb 2 hd2)
  have hgradc : ∀ i q, StrictlyPositive q → HasFDerivAt (c i) (dualityDotCLM (c i q • β q)) q :=
    fun i q hq => hgradD i pb 2 pb 1 hd2 hd1 q hq
  -- the wealth equation `eᵢ(p, vᵢ(p, w)) = w`
  have hEv : ∀ i p w, PWDomain p w → E i (indirectUtility (us i) p w) p = w :=
    fun i p w hd => equation_3_E_1_left (hrep i) (hu i) (hlns i) hd.1 hd.2.le
  -- `κᵢ(ū) = (eᵢ(p̄, ū) - eᵢ(p̄, u⁰))/cᵢ(p̄)`, and `(w - eᵢ(p, u⁰))/cᵢ(p) = κᵢ(vᵢ(p, w))`
  set κ : Fin I → ℝ → ℝ := fun i ub => (E i ub pb - E i (u0 i) pb) / c i pb with hκ
  have hkey : ∀ i p w, PWDomain p w →
      (w - E i (u0 i) p) / c i p = κ i (indirectUtility (us i) p w) := by
    intro i p w hd
    have := ratio_const_of_grad (hgradD i p w pb 1 hd hd1) (hgradc i)
      (fun q hq => (hcpos i q hq).ne') hd.1 hpbpos
    simp only [hEv i p w hd] at this
    exact this
  have hκmono : ∀ i p w p' w', PWDomain p w → PWDomain p' w' →
      (indirectUtility (us i) p w ≤ indirectUtility (us i) p' w' ↔
        κ i (indirectUtility (us i) p w) ≤ κ i (indirectUtility (us i) p' w')) := by
    intro i p w p' w' hd hd'
    have hcp := hcpos i pb hpbpos
    have hstrict : ∀ a b : ℝ, (∃ q v, PWDomain q v ∧ a = indirectUtility (us i) q v) →
        (∃ q v, PWDomain q v ∧ b = indirectUtility (us i) q v) → a < b → κ i a < κ i b := by
      rintro a b ⟨q, v, hqv, rfl⟩ ⟨q', v', hqv', rfl⟩ hab
      simp only [κ]
      apply div_lt_div_of_pos_right _ hcp
      simp only [E]
      linarith [proposition_3_E_2_ii_utility (hu i) hpbpos (hgt0 i q v hqv) hab
        (hatt i q' v' hqv')]
    constructor
    · intro h
      rcases h.lt_or_eq with h | h
      · exact (hstrict _ _ ⟨p, w, hd, rfl⟩ ⟨p', w', hd', rfl⟩ h).le
      · rw [h]
    · intro h
      by_contra hc
      push Not at hc
      exact absurd h (not_le.mpr (hstrict _ _ ⟨p', w', hd', rfl⟩ ⟨p, w, hd, rfl⟩ hc))
  -- common coefficient: `cᵢ = Kᵢ c₁`
  rcases Nat.eq_zero_or_pos I with hI | hI
  · subst hI
    exact ⟨fun _ _ => 0, fun _ => 1, fun _ _ => one_pos, fun i => i.elim0⟩
  set i0 : Fin I := ⟨0, hI⟩
  set K : Fin I → ℝ := fun i => c i pb / c i0 pb with hK
  have hKpos : ∀ i, 0 < K i := fun i => div_pos (hcpos i pb hpbpos) (hcpos i0 pb hpbpos)
  have hci : ∀ i q, StrictlyPositive q → c i q = K i * c i0 q := by
    intro i q hq
    have := ratio_const_of_grad (hgradc i) (hgradc i0) (fun q hq => (hcpos i0 q hq).ne') hq
      hpbpos
    have h0 := (hcpos i0 q hq).ne'
    rw [hK]
    field_simp at this ⊢
    linarith
  refine ⟨fun i p => -(E i (u0 i) p) / c i0 p, fun p => 1 / c i0 p,
    fun p hp => one_div_pos.mpr (hcpos i0 p hp), fun i p w p' w' hd hd' => ?_⟩
  -- `Aᵢ(p) + B(p) w = Kᵢ κᵢ(vᵢ(p, w))`
  have hG : ∀ q v, PWDomain q v → -(E i (u0 i) q) / c i0 q + 1 / c i0 q * v =
      K i * κ i (indirectUtility (us i) q v) := by
    intro q v hqv
    rw [← hkey i q v hqv, hci i q hqv.1]
    have h0 := (hcpos i0 q hqv.1).ne'
    have hK0 := (hKpos i).ne'
    field_simp
    ring
  rw [hG p w hd, hG p' w' hd', mul_le_mul_iff_of_pos_left (hKpos i)]
  exact hκmono i p w p' w' hd hd'

end MWG.AggregateDemand
