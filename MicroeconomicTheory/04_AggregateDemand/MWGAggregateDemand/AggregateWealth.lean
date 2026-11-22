/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGAggregateDemand.Basic
import MWGClassicalDemand.RelationsBasic
import MWGClassicalDemand.UMPExercises
import MWGConsumerChoice.AppendixMA
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Basic.Real.Pointwise

/-!
# Aggregate demand and aggregate wealth

MWG, Section 4.B, pp. 106-109, and Exercises 4.B.1-4.B.2 (pp. 123-124).

* `invariant_transfer`: invariance to redistribution means a transfer `t` from consumer `j`
  to consumer `i` leaves `xᵢ + xⱼ` unchanged.
* `equation_4_B_1` (p. 107): if aggregate demand is invariant to redistribution and demands are
  differentiable in wealth, then `∂xᵢ/∂wᵢ = ∂xⱼ/∂wⱼ` for any two consumers and any wealth
  levels; `footnote_4_B_3`: hence `∂xᵢ(p, wᵢ)/∂wᵢ` does not depend on `wᵢ`.
* `invariant_iff_parallel` (p. 107, Figure 4.B.1): with at least two consumers and demands
  differentiable in wealth, invariance holds iff the wealth expansion paths are straight
  parallel lines, `xᵢ(p, w) = aᵢ(p) + w b(p)`.
* `roy_gorman`, `proposition_4_B_1_sufficiency` (p. 107, Exercise 4.B.1): Gorman-form indirect
  utilities `vᵢ(p, w) = aᵢ(p) + b(p) w` with a common `b` give straight parallel expansion
  paths (via Roy's identity, MWG Chapter 3's `proposition_3_G_4`), hence invariance. The
  necessity direction is in `MWGAggregateDemand.GormanNecessity`.
* `exercise_4_B_1_expenditure`: Gorman form gives `eᵢ(p, u) = c(p) u + dᵢ(p)`.
* `footnote_4_B_4`: a quasilinear utility (numeraire `k`) has `v(p, w) = v(p, 0) + w/p_k`;
  `indirectUtility_homothetic`: a degree-one homogeneous utility has `v(p, w) = w v(p, 1)`.
  Both are Gorman forms (p. 107).
* `exercise_4_B_2a`, `exercise_4_B_2b`: family-size heterogeneity.

Throughout, wealth levels are positive (the domain `w > 0` of MWG Chapter 2); the book
neglects boundary constraints (footnote 2), and the differential statements here are exactly
the local statements it makes.
-/

namespace MWG.AggregateDemand

open MWG.ConsumerChoice MWG.ClassicalDemand Filter Topology
open scoped Pointwise

variable {L I : ℕ}

/-- Splitting a sum over `Fin I` at two distinct indices. -/
theorem sum_split_pair {M : Type*} [AddCommMonoid M] (f : Fin I → M) {i j : Fin I}
    (hij : i ≠ j) :
    ∑ k, f k = f i + f j + ∑ k ∈ (Finset.univ.erase i).erase j, f k := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
    ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩), add_assoc]

/-- **Section 4.B** (MWG, p. 106). Under invariance to redistribution, transferring `t` from
consumer `j` to consumer `i ≠ j` leaves their joint demand unchanged:
`xᵢ(p, a + t) + xⱼ(p, b - t) = xᵢ(p, a) + xⱼ(p, b)`. -/
theorem invariant_transfer {xs : Fin I → DemandFunction L} (hinv : RedistributionInvariant xs)
    {p : Fin L → ℝ} (hp : StrictlyPositive p) {i j : Fin I} (hij : i ≠ j) {a b t : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hat : 0 < a + t) (hbt : 0 < b - t) :
    xs i p (a + t) + xs j p (b - t) = xs i p a + xs j p b := by
  classical
  set ws : Fin I → ℝ := fun k => if k = i then a else if k = j then b else 1 with hws
  set ws' : Fin I → ℝ := fun k => if k = i then a + t else if k = j then b - t else 1 with hws'
  have hrest : ∀ k ∈ (Finset.univ.erase i).erase j, ws k = ws' k := by
    intro k hk
    obtain ⟨hkj, hk'⟩ := Finset.mem_erase.mp hk
    have hki := (Finset.mem_erase.mp hk').1
    simp [ws, ws', hki, hkj]
  have hpos : ∀ k, 0 < ws k := by
    intro k
    simp only [ws]
    split_ifs <;> linarith
  have hpos' : ∀ k, 0 < ws' k := by
    intro k
    simp only [ws']
    split_ifs <;> linarith
  have hwi : ws i = a := by simp [ws]
  have hwj : ws j = b := by simp [ws, hij.symm]
  have hwi' : ws' i = a + t := by simp [ws']
  have hwj' : ws' j = b - t := by simp [ws', hij.symm]
  have hsum : ∑ k, ws k = ∑ k, ws' k := by
    rw [sum_split_pair ws hij, sum_split_pair ws' hij, Finset.sum_congr rfl hrest, hwi, hwj,
      hwi', hwj']
    ring
  have h := hinv p hp ws ws' hpos hpos' hsum
  unfold aggDemand at h
  rw [sum_split_pair (fun k => xs k p (ws k)) hij, sum_split_pair (fun k => xs k p (ws' k)) hij,
    Finset.sum_congr rfl (fun k hk => by rw [hrest k hk])] at h
  simp only [hwi, hwj, hwi', hwj'] at h
  exact (add_right_cancel h).symm

/-- **Equation (4.B.1)** (MWG, p. 107). If aggregate demand is invariant to redistributions of
wealth, then at any `p ≫ 0` the wealth effects of any two consumers coincide:
`∂xᵢ(p, wᵢ)/∂wᵢ = ∂xⱼ(p, wⱼ)/∂wⱼ` for all `wᵢ, wⱼ > 0`. -/
theorem equation_4_B_1 {xs : Fin I → DemandFunction L} (hinv : RedistributionInvariant xs)
    {p : Fin L → ℝ} (hp : StrictlyPositive p) {i j : Fin I} (hij : i ≠ j) {wi wj : ℝ}
    (hwi : 0 < wi) (hwj : 0 < wj) {di dj : Fin L → ℝ} (hdi : HasDerivAt (xs i p) di wi)
    (hdj : HasDerivAt (xs j p) dj wj) : di = dj := by
  have h1 : HasDerivAt (fun t => xs i p (wi + t) + xs j p (wj - t)) (di + -dj) 0 :=
    (HasDerivAt.comp_const_add wi 0 (by simpa using hdi)).add
      (HasDerivAt.comp_const_sub wj 0 (by simpa using hdj))
  have hev : (fun t => xs i p (wi + t) + xs j p (wj - t)) =ᶠ[𝓝 0]
      fun _ => xs i p wi + xs j p wj := by
    have : ∀ᶠ t in 𝓝 (0 : ℝ), t ∈ Set.Ioo (-wi) wj := Ioo_mem_nhds (by linarith) hwj
    filter_upwards [this] with t ht
    exact invariant_transfer hinv hp hij hwi hwj (by linarith [ht.1]) (by linarith [ht.2])
  have h2 : HasDerivAt (fun t => xs i p (wi + t) + xs j p (wj - t)) 0 0 :=
    (hasDerivAt_const (0 : ℝ) (xs i p wi + xs j p wj)).congr_of_eventuallyEq hev
  have h3 := h1.unique h2
  rw [← sub_eq_zero, sub_eq_add_neg]
  exact h3

/-- **Footnote 3** (MWG, p. 107). Under invariance, a consumer's wealth effect does not depend
on his wealth level: `∂xᵢ(p, wᵢ)/∂wᵢ = ∂xᵢ(p, w'ᵢ)/∂wᵢ` (compare both with a second consumer
`j ≠ i`). -/
theorem footnote_4_B_3 {xs : Fin I → DemandFunction L} (hinv : RedistributionInvariant xs)
    {p : Fin L → ℝ} (hp : StrictlyPositive p) {i j : Fin I} (hij : i ≠ j) {w w' wj : ℝ}
    (hw : 0 < w) (hw' : 0 < w') (hwj : 0 < wj) {d d' dj : Fin L → ℝ}
    (hd : HasDerivAt (xs i p) d w) (hd' : HasDerivAt (xs i p) d' w')
    (hdj : HasDerivAt (xs j p) dj wj) : d = d' :=
  (equation_4_B_1 hinv hp hij hw hwj hd hdj).trans
    (equation_4_B_1 hinv hp hij hw' hwj hd' hdj).symm

/-- **Section 4.B** (MWG, p. 107). Straight parallel wealth expansion paths give invariance to
redistribution (no differentiability needed). -/
theorem invariant_of_parallel {xs : Fin I → DemandFunction L} (h : ParallelLinearEngel xs) :
    RedistributionInvariant xs := by
  intro p hp ws ws' hws hws' hsum
  obtain ⟨a, b, hab⟩ := h p hp
  rw [aggDemand_of_linear hab hws, aggDemand_of_linear hab hws', hsum]

/-- **Section 4.B** (MWG, p. 107; Figure 4.B.1). With at least two consumers whose demands are
differentiable in wealth, invariance to redistribution implies that wealth expansion paths are
straight lines with a common direction: `xᵢ(p, w) = aᵢ(p) + w b(p)`. -/
theorem parallel_of_invariant (hI : 2 ≤ I) {xs : Fin I → DemandFunction L}
    (hdiff : ∀ i p, StrictlyPositive p → ∀ w, 0 < w → DifferentiableAt ℝ (xs i p) w)
    (hinv : RedistributionInvariant xs) : ParallelLinearEngel xs := by
  have hnt : Nontrivial (Fin I) := Fin.nontrivial_iff_two_le.mpr hI
  intro p hp
  set i0 : Fin I := ⟨0, by omega⟩
  set b := deriv (xs i0 p) 1
  have hder : ∀ i w, 0 < w → deriv (xs i p) w = b := by
    intro i w hw
    by_cases hi : i = i0
    · subst hi
      obtain ⟨j, hj⟩ := exists_ne i0
      have e1 := equation_4_B_1 hinv hp hj.symm hw one_pos (hdiff i0 p hp w hw).hasDerivAt
        (hdiff j p hp 1 one_pos).hasDerivAt
      have e2 := equation_4_B_1 hinv hp hj.symm one_pos one_pos
        (hdiff i0 p hp 1 one_pos).hasDerivAt (hdiff j p hp 1 one_pos).hasDerivAt
      rw [e1, ← e2]
    · exact equation_4_B_1 hinv hp hi hw one_pos (hdiff i p hp w hw).hasDerivAt
        (hdiff i0 p hp 1 one_pos).hasDerivAt
  have hlin : ∀ w : ℝ, HasDerivAt (fun v : ℝ => v • b) b w := by
    intro w
    simpa using (hasDerivAt_id w).smul_const b
  have hex : ∀ i, ∃ a : Fin L → ℝ, ∀ w, 0 < w → xs i p w = a + w • b := by
    intro i
    obtain ⟨a, ha⟩ := IsOpen.exists_eq_add_of_deriv_eq (s := Set.Ioi (0 : ℝ)) isOpen_Ioi
      (convex_Ioi 0).isPreconnected
      (fun w hw => (hdiff i p hp w hw).differentiableWithinAt)
      (fun w _ => (hlin w).differentiableAt.differentiableWithinAt)
      (fun w hw => by rw [hder i w hw, (hlin w).deriv])
    exact ⟨a, fun w hw => by rw [ha hw, add_comm]⟩
  choose a ha using hex
  exact ⟨a, b, ha⟩

/-- **Section 4.B** (MWG, pp. 106-107). With at least two consumers whose demands are
differentiable in wealth, aggregate demand can be written as a function of aggregate wealth
for every distribution of wealth if and only if the wealth expansion paths are straight
parallel lines. -/
theorem invariant_iff_parallel (hI : 2 ≤ I) {xs : Fin I → DemandFunction L}
    (hdiff : ∀ i p, StrictlyPositive p → ∀ w, 0 < w → DifferentiableAt ℝ (xs i p) w) :
    RedistributionInvariant xs ↔ ParallelLinearEngel xs :=
  ⟨parallel_of_invariant hI hdiff, invariant_of_parallel⟩

/-! ### Gorman form -/

/-- **Proposition 4.B.1** (MWG, p. 107). An indirect utility function `v` has the Gorman form
`v(p, w) = a(p) + b(p) w` on the domain `p ≫ 0`, `w > 0`. -/
def GormanForm (v : (Fin L → ℝ) → ℝ → ℝ) (a b : (Fin L → ℝ) → ℝ) : Prop :=
  ∀ p w, PWDomain p w → v p w = a p + b p * w

/-- The price-wealth domain is open. -/
theorem isOpen_pwDomain (L : ℕ) : IsOpen {q : (Fin L → ℝ) × ℝ | PWDomain q.1 q.2} :=
  ((relations_isOpen_strictlyPositive L).preimage continuous_fst).inter
    (isOpen_Ioi.preimage continuous_snd)

/-- **Exercise 4.B.1** (MWG, p. 123), the Roy's identity step. If `u` (continuous on `ℝ^L_+`,
representing a locally nonsatiated strictly convex `≿`) has a Gorman-form indirect utility
`v(p, w) = a(p) + b(p) w` with `a`, `b` differentiable at `p₀ ≫ 0` and `b(p₀) ≠ 0`, then the
demand at `(p₀, w₀)` is `x = -(1/b(p₀)) (∇a(p₀) + w₀ ∇b(p₀))`: affine in wealth, with slope
`-∇b(p₀)/b(p₀)`. -/
theorem roy_gorman {u : (Fin L → ℝ) → ℝ} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hrep : RepresentsOn (nonnegOrthant L) u r) (hu : ContinuousOn u (nonnegOrthant L))
    (hlns : LocallyNonsatiated (nonnegOrthant L) r) (hsc : PrefStrictlyConvex (nonnegOrthant L) r)
    {a b : (Fin L → ℝ) → ℝ} (hG : GormanForm (indirectUtility u) a b) {p₀ : Fin L → ℝ}
    {w₀ : ℝ} (hpw : PWDomain p₀ w₀) {a' b' : (Fin L → ℝ) →L[ℝ] ℝ} (ha : HasFDerivAt a a' p₀)
    (hb : HasFDerivAt b b' p₀) (hb0 : b p₀ ≠ 0) {x : Fin L → ℝ}
    (hx : x ∈ walrasianDemand u p₀ w₀) :
    x = -(b p₀)⁻¹ • (gradientVec a' + w₀ • gradientVec b') := by
  have hG' := (ha.comp (p₀, w₀) (hasFDerivAt_fst (𝕜 := ℝ) (p := (p₀, w₀)))).add
    ((hb.comp (p₀, w₀) (hasFDerivAt_fst (𝕜 := ℝ) (p := (p₀, w₀)))).mul
      (hasFDerivAt_snd (𝕜 := ℝ) (p := (p₀, w₀))))
  have hev : (fun q : (Fin L → ℝ) × ℝ => indirectUtility u q.1 q.2) =ᶠ[𝓝 (p₀, w₀)]
      fun q => a q.1 + b q.1 * q.2 := by
    filter_upwards [(isOpen_pwDomain L).mem_nhds hpw] with q hq
    exact hG q.1 q.2 hq
  have hD := hG'.congr_of_eventuallyEq hev
  obtain ⟨-, hroy⟩ := proposition_3_G_4 hrep hu hlns hsc hpw hD hx
  have hroy' := hroy (by
    convert hb0 using 1
    simp)
  funext l
  rw [hroy' l]
  simp [gradientVec]
  field_simp

/-- **Proposition 4.B.1, sufficiency** (MWG, p. 107; Exercise 4.B.1, p. 123). Suppose each
consumer `i` has a utility `uᵢ` (continuous on `ℝ^L_+`, representing a locally nonsatiated,
strictly convex preference) whose indirect utility has the Gorman form
`vᵢ(p, w) = aᵢ(p) + b(p) w` with the same `b`, `aᵢ` and `b` differentiable at every `p ≫ 0`
and `b(p) ≠ 0`. Then the consumers' wealth expansion paths are straight parallel lines, and
aggregate demand is invariant to redistribution. -/
theorem proposition_4_B_1_sufficiency {us : Fin I → (Fin L → ℝ) → ℝ}
    {rs : Fin I → (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hrep : ∀ i, RepresentsOn (nonnegOrthant L) (us i) (rs i))
    (hu : ∀ i, ContinuousOn (us i) (nonnegOrthant L))
    (hlns : ∀ i, LocallyNonsatiated (nonnegOrthant L) (rs i))
    (hsc : ∀ i, PrefStrictlyConvex (nonnegOrthant L) (rs i))
    {a : Fin I → (Fin L → ℝ) → ℝ} {b : (Fin L → ℝ) → ℝ}
    (hG : ∀ i, GormanForm (indirectUtility (us i)) (a i) b)
    (ha : ∀ i p, StrictlyPositive p → DifferentiableAt ℝ (a i) p)
    (hb : ∀ p, StrictlyPositive p → DifferentiableAt ℝ b p) (hb0 : ∀ p, b p ≠ 0)
    {xs : Fin I → DemandFunction L}
    (hxs : ∀ i p w, PWDomain p w → xs i p w ∈ walrasianDemand (us i) p w) :
    ParallelLinearEngel xs ∧ RedistributionInvariant xs := by
  have hpar : ParallelLinearEngel xs := by
    intro p hp
    refine ⟨fun i => -(b p)⁻¹ • gradientVec (fderiv ℝ (a i) p),
      -(b p)⁻¹ • gradientVec (fderiv ℝ b p), fun i w hw => ?_⟩
    rw [roy_gorman (hrep i) (hu i) (hlns i) (hsc i) (hG i) ⟨hp, hw⟩ (ha i p hp).hasFDerivAt
      (hb p hp).hasFDerivAt (hb0 p) (hxs i p w ⟨hp, hw⟩), smul_add, smul_comm]
  exact ⟨hpar, invariant_of_parallel hpar⟩

/-- The expenditure at a utility level above `u(0)` that some bundle attains is positive. -/
theorem expenditure_pos_of_attainable {u : (Fin L → ℝ) → ℝ}
    (hu : ContinuousOn u (nonnegOrthant L)) {p : Fin L → ℝ} (hp : StrictlyPositive p) {ub : ℝ}
    (hub : u 0 < ub) (hne : ∃ x ∈ nonnegOrthant L, ub ≤ u x) : 0 < expenditure u p ub := by
  obtain ⟨y, hy⟩ := exercise_3_E_3 hu hp hne
  have hy0 : y ≠ 0 := by
    rintro rfl
    linarith [hy.1.2]
  rw [expenditure_eq_of_mem hy]
  exact exp_dotProduct_pos hp hy.1.1 hy0

/-- **Exercise 4.B.1** (MWG, p. 123), second part. If consumer `i`'s indirect utility has the
Gorman form `aᵢ(p) + b(p) w` (with `b(p) ≠ 0`), then the expenditure function has the form
`eᵢ(p, u) = c(p) u + dᵢ(p)` with `c = 1/b` (common to all consumers sharing `b`) and
`dᵢ = -aᵢ/b`, at every utility level `u > uᵢ(0)` that is attainable. -/
theorem exercise_4_B_1_expenditure {u : (Fin L → ℝ) → ℝ} (hu : ContinuousOn u (nonnegOrthant L))
    {a b : (Fin L → ℝ) → ℝ} (hG : GormanForm (indirectUtility u) a b) {p : Fin L → ℝ}
    (hp : StrictlyPositive p) (hb0 : b p ≠ 0) {ub : ℝ} (hub : u 0 < ub)
    (hne : ∃ x ∈ nonnegOrthant L, ub ≤ u x) :
    expenditure u p ub = (b p)⁻¹ * ub + -(a p) / b p := by
  have he := expenditure_pos_of_attainable hu hp hub hne
  have hv := equation_3_E_1_right hu hp hub hne
  rw [hG p _ ⟨hp, he⟩] at hv
  field_simp
  linarith

/-- **Footnote 4** (MWG, p. 108). If `u(x + t e_k) = u(x) + t` (quasilinear with respect to
good `k`, on the consumption set `(-∞, ∞) × ℝ^{L-1}_+`) and the UMP at zero wealth is bounded,
then the indirect utility is `v(p, w) = v(p, 0) + w/p_k`: a Gorman form with `b(p) = 1/p_k`,
the same for every consumer quasilinear in the same good. -/
theorem footnote_4_B_4 {k : Fin L} {u : (Fin L → ℝ) → ℝ}
    (hql : ∀ x : Fin L → ℝ, ∀ t : ℝ, u (x + t • unitVec k) = u x + t) {p : Fin L → ℝ}
    (hpk : 0 < p k) (hbdd : BddAbove (u '' budgetSetOn (quasilinearDomain k) p 0)) (w : ℝ) :
    indirectUtilityOn (quasilinearDomain k) u p w =
      indirectUtilityOn (quasilinearDomain k) u p 0 + w / p k := by
  set t := w / p k with ht
  have hpe : p ⬝ᵥ unitVec k = p k := by simp [unitVec]
  have hdom : ∀ x : Fin L → ℝ, ∀ s : ℝ, x ∈ quasilinearDomain k →
      x + s • unitVec k ∈ quasilinearDomain k := by
    intro x s hx l hl
    simpa [unitVec, hl] using hx l hl
  have himg : u '' budgetSetOn (quasilinearDomain k) p w =
      (fun y => y + t) '' (u '' budgetSetOn (quasilinearDomain k) p 0) := by
    ext v
    constructor
    · rintro ⟨x, ⟨hxX, hxb⟩, rfl⟩
      refine ⟨u (x + (-t) • unitVec k), ⟨x + (-t) • unitVec k, ⟨hdom x _ hxX, ?_⟩, rfl⟩, ?_⟩
      · rw [dotProduct_add, dotProduct_smul, hpe, smul_eq_mul, ht]
        field_simp
        linarith
      · simp only
        rw [hql]
        ring
    · rintro ⟨_, ⟨y, ⟨hyX, hyb⟩, rfl⟩, rfl⟩
      refine ⟨y + t • unitVec k, ⟨hdom y _ hyX, ?_⟩, hql y t⟩
      rw [dotProduct_add, dotProduct_smul, hpe, smul_eq_mul, ht]
      field_simp
      linarith
  have hne : (u '' budgetSetOn (quasilinearDomain k) p 0).Nonempty :=
    ⟨u 0, 0, ⟨fun l _ => le_rfl, by simp⟩, rfl⟩
  unfold indirectUtilityOn
  rw [himg]
  exact ((OrderIso.addRight t).map_csSup' hne hbdd).symm

/-- **Section 4.B** (MWG, p. 107). If `u` is homogeneous of degree one on `ℝ^L_+`, then
`v(p, w) = w v(p, 1)` for `w > 0`: a Gorman form with `a = 0` and `b(p) = v(p, 1)`, the same
for consumers with identical homothetic preferences. -/
theorem indirectUtility_homothetic {u : (Fin L → ℝ) → ℝ} (hu : HomogeneousOneOn u)
    (p : Fin L → ℝ) {w : ℝ} (hw : 0 < w) :
    indirectUtility u p w = w * indirectUtility u p 1 := by
  have himg : u '' budgetSet p w = w • (u '' budgetSet p 1) := by
    ext v
    constructor
    · rintro ⟨x, ⟨hx0, hxb⟩, rfl⟩
      have hy0 : w⁻¹ • x ∈ nonnegOrthant L :=
        fun l => by simpa using mul_nonneg (inv_pos.mpr hw).le (hx0 l)
      refine ⟨u (w⁻¹ • x), ⟨w⁻¹ • x, ⟨hy0, ?_⟩, rfl⟩, ?_⟩
      · rw [dotProduct_smul, smul_eq_mul]
        rw [inv_mul_le_iff₀ hw]
        linarith
      · simp only [smul_eq_mul]
        rw [← hu _ hy0 w hw, smul_smul, mul_inv_cancel₀ hw.ne', one_smul]
    · rintro ⟨_, ⟨y, ⟨hy0, hyb⟩, rfl⟩, rfl⟩
      refine ⟨w • y, ⟨fun l => by simpa using mul_nonneg hw.le (hy0 l), ?_⟩, ?_⟩
      · rw [dotProduct_smul, smul_eq_mul]
        nlinarith
      · rw [hu y hy0 w hw]
        rfl
  unfold indirectUtility indirectUtilityOn
  rw [budgetSetOn_nonnegOrthant, budgetSetOn_nonnegOrthant, himg,
    Real.sSup_smul_of_nonneg hw.le, smul_eq_mul]

/-- **Section 4.B** (MWG, p. 107). Identical homothetic preferences (a common utility
homogeneous of degree one) give Gorman-form indirect utilities with the same `b(p) = v(p, 1)`
and `aᵢ = 0`. -/
theorem gorman_of_homothetic {u : (Fin L → ℝ) → ℝ} (hu : HomogeneousOneOn u) :
    GormanForm (indirectUtility u) (fun _ => 0) (fun p => indirectUtility u p 1) := by
  intro p w hd
  rw [indirectUtility_homothetic hu p hd.2, zero_add, mul_comm]

/-! ### Exercise 4.B.2: family size -/

/-- **Exercise 4.B.2(a)** (MWG, pp. 123-124). Fix the family sizes, so that consumer `i` has the
demand function `xs i = x(·, ·, sᵢ)`. If every consumer's demand is homogeneous of degree one
in wealth (homothetic preferences, see `demand_hd1_of_homogeneousOne`) and aggregate demand is
invariant to redistribution, then all consumers have the same demand function:
`x(p, w, sᵢ) = x(p, w, sⱼ)`, so demand does not depend on family size. -/
theorem exercise_4_B_2a {xs : Fin I → DemandFunction L}
    (hhd : ∀ i p w t, StrictlyPositive p → 0 < w → 0 < t → xs i p (t * w) = t • xs i p w)
    (hinv : RedistributionInvariant xs) {p : Fin L → ℝ} (hp : StrictlyPositive p) (i j : Fin I)
    {w : ℝ} (hw : 0 < w) : xs i p w = xs j p w := by
  have hlin : ∀ k v, 0 < v → xs k p v = v • xs k p 1 := by
    intro k v hv
    have := hhd k p 1 v hp one_pos hv
    rwa [mul_one] at this
  by_cases hij : i = j
  · rw [hij]
  have htr := invariant_transfer hinv hp hij one_pos one_pos (by norm_num : (0 : ℝ) < 1 + 1 / 2)
    (by norm_num : (0 : ℝ) < 1 - 1 / 2)
  rw [hlin i _ (by norm_num), hlin j _ (by norm_num)] at htr
  have hc : xs i p 1 = xs j p 1 := by
    have h2 : ((1 : ℝ) / 2) • (xs i p 1 - xs j p 1) = 0 := by
      rw [smul_sub]
      have e1 : (1 + 1 / 2 : ℝ) • xs i p 1 = xs i p 1 + (1 / 2 : ℝ) • xs i p 1 := by
        rw [add_smul, one_smul]
      have e2 : (1 - 1 / 2 : ℝ) • xs j p 1 = xs j p 1 - (1 / 2 : ℝ) • xs j p 1 := by
        rw [sub_smul, one_smul]
      rw [e1, e2] at htr
      have := congrArg (fun z => z - (xs i p 1 + xs j p 1)) htr
      simp only [sub_self] at this
      rw [← this]
      abel
    rw [smul_eq_zero] at h2
    rcases h2 with h2 | h2
    · norm_num at h2
    · exact sub_eq_zero.mp h2
  rw [hlin i w hw, hlin j w hw, hc]

/-- **Exercise 4.B.2(a)** (MWG, p. 124), the homothetic step. If `u` is homogeneous of degree
one on `ℝ^L_+` and its demand is single-valued (as for a strictly convex preference), the
demand function is homogeneous of degree one in wealth: `x(p, t w) = t x(p, w)`. -/
theorem demand_hd1_of_homogeneousOne {u : (Fin L → ℝ) → ℝ} (hu : HomogeneousOneOn u)
    (huniq : ∀ p w, (walrasianDemand u p w).Subsingleton) {xf : DemandFunction L}
    (hxf : ∀ p w, PWDomain p w → xf p w ∈ walrasianDemand u p w) {p : Fin L → ℝ}
    (hp : StrictlyPositive p) {w t : ℝ} (hw : 0 < w) (ht : 0 < t) :
    xf p (t * w) = t • xf p w := by
  obtain ⟨⟨hx0, hxb⟩, hmax⟩ := hxf p w ⟨hp, hw⟩
  have hmem : t • xf p w ∈ walrasianDemand u p (t * w) := by
    refine ⟨⟨fun l => by simpa using mul_nonneg ht.le (hx0 l), ?_⟩, fun y hy => ?_⟩
    · rw [dotProduct_smul, smul_eq_mul]
      exact mul_le_mul_of_nonneg_left hxb ht.le
    · have hy' : t⁻¹ • y ∈ budgetSet p w := by
        refine ⟨fun l => by simpa using mul_nonneg (inv_pos.mpr ht).le (hy.1 l), ?_⟩
        rw [dotProduct_smul, smul_eq_mul, inv_mul_le_iff₀ ht]
        exact hy.2
      have h1 := hmax _ hy'
      have h2 := hu (t⁻¹ • y) hy'.1 t ht
      rw [smul_smul, mul_inv_cancel₀ ht.ne', one_smul] at h2
      rw [h2, hu _ hx0 t ht]
      exact mul_le_mul_of_nonneg_left h1 ht.le
  exact huniq p (t * w) (hxf p (t * w) ⟨hp, mul_pos ht hw⟩) hmem

/-- **Exercise 4.B.2(b)** (MWG, p. 124). A sufficient condition for aggregate demand to depend
only on aggregate wealth and aggregate family size: demand is affine in `(w, s)` with
coefficients common to all consumers, `x(p, w, s) = a(p) + w b(p) + s c(p)`. Then
`∑ᵢ x(p, wᵢ, sᵢ) = I a(p) + (∑ᵢ wᵢ) b(p) + (∑ᵢ sᵢ) c(p)`. -/
theorem exercise_4_B_2b {x : ℝ → DemandFunction L} {a b c : (Fin L → ℝ) → Fin L → ℝ}
    (hx : ∀ s p w, x s p w = a p + w • b p + s • c p) (p : Fin L → ℝ) (ws ss : Fin I → ℝ) :
    ∑ i, x (ss i) p (ws i) = (I : ℝ) • a p + (∑ i, ws i) • b p + (∑ i, ss i) • c p := by
  simp only [hx, Finset.sum_add_distrib, Finset.sum_smul, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, Nat.cast_smul_eq_nsmul]

/-- **Exercise 4.B.2(b)** (MWG, p. 124), at the level of indirect utility. If the indirect
utility of a consumer with family size `s` has the form `v(p, w, s) = a(p) + d(p) s + b(p) w`
(common `a`, `d`, `b`, differentiable, `b ≠ 0`), then demand has the affine form
`x(p, w, s) = α(p) + w β(p) + s γ(p)` of `exercise_4_B_2b`, by Roy's identity. -/
theorem exercise_4_B_2b_gorman {u : ℝ → (Fin L → ℝ) → ℝ}
    {r : ℝ → (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hrep : ∀ s, RepresentsOn (nonnegOrthant L) (u s) (r s))
    (hu : ∀ s, ContinuousOn (u s) (nonnegOrthant L))
    (hlns : ∀ s, LocallyNonsatiated (nonnegOrthant L) (r s))
    (hsc : ∀ s, PrefStrictlyConvex (nonnegOrthant L) (r s)) {a d b : (Fin L → ℝ) → ℝ}
    (hG : ∀ s, GormanForm (indirectUtility (u s)) (fun p => a p + d p * s) b) {p : Fin L → ℝ}
    (hp : StrictlyPositive p) (ha : DifferentiableAt ℝ a p) (hd : DifferentiableAt ℝ d p)
    (hb : DifferentiableAt ℝ b p) (hb0 : b p ≠ 0) {x : ℝ → DemandFunction L}
    (hx : ∀ s w, 0 < w → x s p w ∈ walrasianDemand (u s) p w) (s w : ℝ) (hw : 0 < w) :
    x s p w = -(b p)⁻¹ • gradientVec (fderiv ℝ a p) +
      w • (-(b p)⁻¹ • gradientVec (fderiv ℝ b p)) +
      s • (-(b p)⁻¹ • gradientVec (fderiv ℝ d p)) := by
  have has : HasFDerivAt (fun q => a q + d q * s) (fderiv ℝ a p + s • fderiv ℝ d p) p := by
    exact ha.hasFDerivAt.add (hd.hasFDerivAt.mul_const s)
  rw [roy_gorman (hrep s) (hu s) (hlns s) (hsc s) (hG s) ⟨hp, hw⟩ has hb.hasFDerivAt hb0
    (hx s w hw)]
  funext l
  simp [gradientVec]
  ring

end MWG.AggregateDemand
