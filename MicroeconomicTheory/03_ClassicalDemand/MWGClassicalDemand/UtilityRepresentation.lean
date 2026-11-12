/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGClassicalDemand.PrefProperties
import MWGClassicalDemand.AppendixMC
import PreferenceProperties.GeneralContinuousRepresentation
import PreferenceProperties.DiagonalRepresentation
import PreferenceProperties.Lexicographic

/-!
# Preference and utility

MWG, Section 3.C, pp. 46-50, and Exercises 3.C.1-3.C.4 (p. 96).

* Definition 3.C.1 (sequential continuity on `X`) is equivalent, for rational preferences,
  to Kreps's continuity (an open strict-preference graph on `X`); continuity implies closed
  contour sets (p. 47), and Exercise 3.C.3 is the converse for rational preferences. Without
  rationality Exercise 3.C.3 is false (`exercise_3_C_3_needs_rationality`).
* Example 3.C.1 and Exercise 3.C.1: the lexicographic order on `ℝ²_+` is complete,
  transitive, strongly monotone and strictly convex, has no utility representation (through
  Kreps's Problem 1.10) and is not continuous.
* Proposition 3.C.1: on `ℝ^L_+` (and on every convex consumption set) a continuous rational
  preference has a continuous utility representation (Kreps's Proposition 2.9, Debreu's
  theorem); with monotonicity, the book's own construction `u(x) = α(x)`, `α(x)e ∼ x`
  (Kreps's diagonal utility). The general (disconnected) `X` is open.
* Exercise 3.C.2 and the remarks on p. 49-50: transformations, discontinuous
  representations, Leontief preferences have no utility differentiable on `ℝ²_{++}`,
  monotonicity and (strict) convexity correspond to increasing and (strictly) quasiconcave
  utilities, and a convex preference with no concave utility. Exercise 3.C.4.
-/

namespace MWG.ClassicalDemand

open MWG.ConsumerChoice Kreps.PreferenceProperties Filter Topology

variable {L : ℕ}

/-- A rational relation on `X` is reflexive on `X`. -/
theorem RationalOn.refl {X : Set (Fin L → ℝ)} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hr : RationalOn X r) {x : Fin L → ℝ} (hx : x ∈ X) : r x x :=
  (hr.1 x hx x hx).elim id id

/-- For a complete relation, `¬ x ≿ y` means `y ≻ x`. -/
theorem RationalOn.strict_of_not {X : Set (Fin L → ℝ)} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hr : RationalOn X r) {x y : Fin L → ℝ} (hx : x ∈ X) (hy : y ∈ X) (h : ¬ r x y) :
    Strict r y x :=
  ⟨(hr.1 x hx y hy).resolve_left h, h⟩

/-- **Definition 3.C.1** (MWG, p. 46). For a rational preference relation, MWG's sequential
continuity on `X` is Kreps's continuity: the strict-preference graph is open in `X × X`. -/
theorem prefContinuous_iff_continuousPreference {X : Set (Fin L → ℝ)}
    {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop} (hr : RationalOn X r) :
    PrefContinuous X r ↔ ContinuousPreference (restrictPref X r) := by
  have hr' := (rationalOn_iff_rational X r).mp hr
  constructor
  · intro hc
    apply (proposition_1_14a hr').mpr
    intro u x y hu
    have hu' : Tendsto (fun n => (u n : Fin L → ℝ)) atTop (𝓝 (x : Fin L → ℝ)) :=
      (continuous_subtype_val.tendsto x).comp hu
    refine ⟨fun hn => ?_, fun hn => ?_⟩
    · exact hc (fun n => u n) (fun _ => y) x y (fun n => (u n).2) (fun _ => y.2) x.2 y.2 hn hu'
        tendsto_const_nhds
    · exact hc (fun _ => y) (fun n => u n) y x (fun _ => y.2) (fun n => (u n).2) y.2 x.2 hn
        tendsto_const_nhds hu'
  · intro hc xs ys x y hxs hys hx hy hn hxt hyt
    by_contra hxy
    have hstrict : Strict (restrictPref X r) ⟨y, hy⟩ ⟨x, hx⟩ := hr.strict_of_not hx hy hxy
    have hpair : Tendsto (fun n => ((⟨ys n, hys n⟩ : X), (⟨xs n, hxs n⟩ : X))) atTop
        (𝓝 ((⟨y, hy⟩ : X), (⟨x, hx⟩ : X))) := by
      refine Tendsto.prodMk_nhds ?_ ?_
      · exact tendsto_subtype_rng.mpr hyt
      · exact tendsto_subtype_rng.mpr hxt
    obtain ⟨n, hnn⟩ := (hpair.eventually (hc.mem_nhds hstrict)).exists
    exact hnn.2 (hn n)

/-- **Section 3.C** (MWG, p. 47). If `≿` is continuous on a closed consumption set `X`, its
upper and lower contour sets are closed. -/
theorem PrefContinuous.isClosed_contours {X : Set (Fin L → ℝ)} (hX : IsClosed X)
    {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop} (hc : PrefContinuous X r) {x : Fin L → ℝ}
    (hx : x ∈ X) : IsClosed (upperContour X r x) ∧ IsClosed (lowerContour X r x) := by
  constructor
  · apply isSeqClosed_iff_isClosed.mp
    intro u y hu hut
    have hy : y ∈ X := hX.mem_of_tendsto hut (Eventually.of_forall fun n => (hu n).1)
    exact ⟨hy, hc u (fun _ => x) y x (fun n => (hu n).1) (fun _ => hx) hy hx
      (fun n => (hu n).2) hut tendsto_const_nhds⟩
  · apply isSeqClosed_iff_isClosed.mp
    intro u y hu hut
    have hy : y ∈ X := hX.mem_of_tendsto hut (Eventually.of_forall fun n => (hu n).1)
    exact ⟨hy, hc (fun _ => x) u x y (fun _ => hx) (fun n => (hu n).1) hx hy
      (fun n => (hu n).2) tendsto_const_nhds hut⟩

/-- **Exercise 3.C.3** (MWG, p. 96). If `≿` is rational on `X` and all its upper and lower
contour sets are closed, then `≿` is continuous in the sense of Definition 3.C.1. -/
theorem exercise_3_C_3 {X : Set (Fin L → ℝ)} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hr : RationalOn X r)
    (hcl : ∀ x ∈ X, IsClosed (upperContour X r x) ∧ IsClosed (lowerContour X r x)) :
    PrefContinuous X r := by
  rw [prefContinuous_iff_continuousPreference hr,
    proposition_1_14c ((rationalOn_iff_rational X r).mp hr)]
  intro x
  constructor
  · have h := (hcl x x.2).2.preimage (continuous_subtype_val (p := (· ∈ X)))
    convert h using 1
    ext y
    exact ⟨fun h => ⟨y.2, h⟩, fun h => h.2⟩
  · have h := (hcl x x.2).1.preimage (continuous_subtype_val (p := (· ∈ X)))
    convert h using 1
    ext y
    exact ⟨fun h => ⟨y.2, h⟩, fun h => h.2⟩

/-- The relation of `exercise_3_C_3_needs_rationality`: only the bundles `1/(n+1)` (in `ℝ¹`)
are related, each to itself. -/
def exercise_3_C_3_relation (x y : Fin 1 → ℝ) : Prop :=
  ∃ n : ℕ, x = (fun _ => 1 / ((n : ℝ) + 1)) ∧ y = fun _ => 1 / ((n : ℝ) + 1)

/-- **Exercise 3.C.3** (MWG, p. 96) needs rationality: a relation on `ℝ¹_+` whose upper and
lower contour sets are all closed (singletons or empty) but which is not continuous. -/
theorem exercise_3_C_3_needs_rationality :
    (∀ x ∈ nonnegOrthant 1, IsClosed (upperContour (nonnegOrthant 1) exercise_3_C_3_relation x)
      ∧ IsClosed (lowerContour (nonnegOrthant 1) exercise_3_C_3_relation x)) ∧
      ¬ PrefContinuous (nonnegOrthant 1) exercise_3_C_3_relation := by
  have hsub : ∀ x, upperContour (nonnegOrthant 1) exercise_3_C_3_relation x ⊆ {x} ∧
      lowerContour (nonnegOrthant 1) exercise_3_C_3_relation x ⊆ {x} := by
    intro x
    constructor
    · rintro y ⟨-, n, hy, hx⟩
      rw [Set.mem_singleton_iff, hy, hx]
    · rintro y ⟨-, n, hx, hy⟩
      rw [Set.mem_singleton_iff, hy, hx]
  refine ⟨fun x _ => ⟨(Set.subsingleton_singleton.anti (hsub x).1).isClosed,
    (Set.subsingleton_singleton.anti (hsub x).2).isClosed⟩, fun hc => ?_⟩
  have hmem : ∀ n : ℕ, (fun _ => 1 / ((n : ℝ) + 1) : Fin 1 → ℝ) ∈ nonnegOrthant 1 :=
    fun n _ => by positivity
  have hlim : Tendsto (fun n : ℕ => (fun _ => 1 / ((n : ℝ) + 1) : Fin 1 → ℝ)) atTop
      (𝓝 (0 : Fin 1 → ℝ)) := by
    rw [tendsto_pi_nhds]
    intro _
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨n, hn, -⟩ := hc _ _ 0 0 hmem hmem (fun _ => le_rfl) (fun _ => le_rfl)
    (fun n => ⟨n, rfl, rfl⟩) hlim hlim
  have := congrFun hn 0
  simp only [Pi.zero_apply] at this
  have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  linarith

/-- **Exercise 3.C.2** (MWG, p. 96). If a utility function continuous on `X` represents `≿`
on `X`, then `≿` is continuous on `X`. -/
theorem exercise_3_C_2 {X : Set (Fin L → ℝ)} {u : (Fin L → ℝ) → ℝ}
    {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop} (hu : RepresentsOn X u r)
    (hcont : ContinuousOn u X) : PrefContinuous X r := by
  intro xs ys x y hxs hys hx hy hn hxt hyt
  have hx' : Tendsto (fun n => u (xs n)) atTop (𝓝 (u x)) :=
    (hcont x hx).tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨hxt, Eventually.of_forall hxs⟩)
  have hy' : Tendsto (fun n => u (ys n)) atTop (𝓝 (u y)) :=
    (hcont y hy).tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨hyt, Eventually.of_forall hys⟩)
  exact (hu x hx y hy).mpr
    (le_of_tendsto_of_tendsto' hy' hx' fun n => (hu (xs n) (hxs n) (ys n) (hys n)).mp (hn n))

/-- **Example 3.C.1** (MWG, p. 46). The lexicographic preference relation on `ℝ²`:
`x ≿ y` iff `x₁ > y₁`, or `x₁ = y₁` and `x₂ ≥ y₂`. -/
def lexPref (x y : Fin 2 → ℝ) : Prop := y 0 < x 0 ∨ (x 0 = y 0 ∧ y 1 ≤ x 1)

/-- **Exercise 3.C.1** (MWG, pp. 46, 96). The lexicographic ordering is complete and
transitive. -/
theorem exercise_3_C_1_rational : RationalOn (nonnegOrthant 2) lexPref := by
  refine ⟨fun x _ y _ => ?_, fun x _ y _ z _ hxy hyz => ?_⟩
  · rcases lt_trichotomy (x 0) (y 0) with h | h | h
    · exact Or.inr (Or.inl h)
    · rcases le_total (y 1) (x 1) with h' | h'
      · exact Or.inl (Or.inr ⟨h, h'⟩)
      · exact Or.inr (Or.inr ⟨h.symm, h'⟩)
    · exact Or.inl (Or.inl h)
  · rcases hxy with h1 | ⟨h1, h1'⟩ <;> rcases hyz with h2 | ⟨h2, h2'⟩
    · exact Or.inl (h2.trans h1)
    · left; linarith
    · left; linarith
    · exact Or.inr ⟨h1.trans h2, h2'.trans h1'⟩

/-- **Exercise 3.C.1** (MWG, p. 96). The lexicographic ordering is strongly monotone. -/
theorem exercise_3_C_1_stronglyMonotone : PrefStronglyMonotone (nonnegOrthant 2) lexPref := by
  intro x _ y _ hxy hne
  rcases (hxy 0).lt_or_eq with h0 | h0
  · exact ⟨Or.inl h0, fun h => by rcases h with h | ⟨h, -⟩ <;> linarith⟩
  · have h1 : x 1 < y 1 := by
      rcases (hxy 1).lt_or_eq with h1 | h1
      · exact h1
      · exfalso
        apply hne
        funext l
        fin_cases l
        · exact h0.symm
        · exact h1.symm
    exact ⟨Or.inr ⟨h0.symm, h1.le⟩, fun h => by rcases h with h | ⟨-, h⟩ <;> linarith⟩

/-- **Exercise 3.C.1** (MWG, p. 96). The lexicographic ordering is strictly convex. -/
theorem exercise_3_C_1_strictlyConvex : PrefStrictlyConvex (nonnegOrthant 2) lexPref := by
  intro x _ y _ z _ hyx hzx hyz α h0 h1
  simp only [Strict, lexPref, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hyx hzx ⊢
  have h1' : 0 < 1 - α := by linarith
  rcases hyx with hy | ⟨hy, hy'⟩
  · have : x 0 < α * y 0 + (1 - α) * z 0 := by
      rcases hzx with hz | ⟨hz, -⟩ <;> nlinarith
    exact ⟨Or.inl this, fun h => by rcases h with h | ⟨h, -⟩ <;> linarith⟩
  · rcases hzx with hz | ⟨hz, hz'⟩
    · have : x 0 < α * y 0 + (1 - α) * z 0 := by nlinarith
      exact ⟨Or.inl this, fun h => by rcases h with h | ⟨h, -⟩ <;> linarith⟩
    · have hne : y 1 ≠ z 1 := by
        intro h
        apply hyz
        funext l
        fin_cases l
        · simp only [Fin.zero_eta, Fin.isValue]; linarith
        · exact h
      have hlt : x 1 < α * y 1 + (1 - α) * z 1 := by
        rcases lt_or_gt_of_ne hne with h | h <;> nlinarith
      have heq : α * y 0 + (1 - α) * z 0 = x 0 := by rw [hy, hz]; ring
      exact ⟨Or.inr ⟨heq, hlt.le⟩, fun h => by rcases h with h | ⟨-, h⟩ <;> linarith⟩

/-- **Example 3.C.1** (MWG, p. 46). No utility function represents the lexicographic ordering
on `ℝ²_+`. The book's small-type argument (a rational between `u(x₁, 1)` and `u(x₁, 2)` for
each `x₁` injects an uncountable set into `ℚ`) is Kreps's Problem 1.10, which we apply to the
restriction to the unit square. -/
theorem example_3_C_1_not_representable :
    ¬ ∃ u : (Fin 2 → ℝ) → ℝ, RepresentsOn (nonnegOrthant 2) u lexPref := by
  rintro ⟨u, hu⟩
  apply lexicographic_not_representable
  refine ⟨fun p => u ![p.1.val, p.2.val], fun p q => ?_⟩
  have hp : ![p.1.val, p.2.val] ∈ nonnegOrthant 2 := by
    intro l
    fin_cases l
    · exact p.1.2.1
    · exact p.2.2.1
  have hq : ![q.1.val, q.2.val] ∈ nonnegOrthant 2 := by
    intro l
    fin_cases l
    · exact q.1.2.1
    · exact q.2.2.1
  rw [← hu _ hp _ hq]
  simp only [LexicographicPreference, lexPref, Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor
  · rintro (h | ⟨h, h'⟩)
    · exact Or.inl h
    · exact Or.inr ⟨h.symm, h'⟩
  · rintro (h | ⟨h, h'⟩)
    · exact Or.inl h
    · exact Or.inr ⟨h.symm, h'⟩

/-- **Example 3.C.1 continued** (MWG, p. 47). Lexicographic preferences are not continuous:
`xⁿ = (1/n, 0) ≻ yⁿ = (0, 1)` for every `n`, but `(0, 1) ≻ (0, 0)` in the limit. -/
theorem example_3_C_1_not_continuous : ¬ PrefContinuous (nonnegOrthant 2) lexPref := by
  intro hc
  have hxs : ∀ n : ℕ, (![1 / ((n : ℝ) + 1), 0] : Fin 2 → ℝ) ∈ nonnegOrthant 2 := by
    intro n l
    fin_cases l
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      positivity
    · simp
  have hy : (![0, 1] : Fin 2 → ℝ) ∈ nonnegOrthant 2 := by
    intro l
    fin_cases l <;> norm_num
  have h0 : (![0, 0] : Fin 2 → ℝ) ∈ nonnegOrthant 2 := by
    intro l
    fin_cases l <;> norm_num
  have hlim : Tendsto (fun n : ℕ => (![1 / ((n : ℝ) + 1), 0] : Fin 2 → ℝ)) atTop
      (𝓝 ![0, 0]) := by
    rw [tendsto_pi_nhds]
    intro l
    fin_cases l
    · simpa using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    · simp
  have := hc _ (fun _ => ![0, 1]) _ _ hxs (fun _ => hy) h0 hy
    (fun n => Or.inl (by simp only [Matrix.cons_val_zero]; positivity)) hlim tendsto_const_nhds
  rcases this with h | ⟨-, h⟩ <;> norm_num at h

/-- The ambient extension of a utility on Kreps's orthant subtype, constant along `x ↦ x ⊔ 0`. -/
noncomputable def extendOrthant (v : Kreps.PreferenceProperties.NonnegativeOrthant L → ℝ)
    (x : Fin L → ℝ) : ℝ := v ⟨x ⊔ 0, le_sup_right⟩

/-- On `ℝ^L_+` the extension agrees with the subtype utility. -/
theorem extendOrthant_apply (v : Kreps.PreferenceProperties.NonnegativeOrthant L → ℝ)
    {x : Fin L → ℝ} (hx : x ∈ nonnegOrthant L) : extendOrthant v x = v ⟨x, hx⟩ := by
  unfold extendOrthant
  congr
  exact sup_eq_left.mpr hx

/-- The extension of a continuous subtype utility is continuous on all of `ℝ^L`. -/
theorem extendOrthant_continuous {v : Kreps.PreferenceProperties.NonnegativeOrthant L → ℝ}
    (hv : Continuous v) : Continuous (extendOrthant v) :=
  hv.comp ((continuous_pi fun l => (continuous_apply l).max continuous_const).subtype_mk _)

/-- A representation on Kreps's orthant subtype extends to a representation on `ℝ^L_+`. -/
theorem representsOn_extendOrthant {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    {v : Kreps.PreferenceProperties.NonnegativeOrthant L → ℝ}
    (hv : Represents v (restrictPref (nonnegOrthant L) r)) :
    RepresentsOn (nonnegOrthant L) (extendOrthant v) r := by
  intro x hx y hy
  rw [extendOrthant_apply v hx, extendOrthant_apply v hy]
  exact hv ⟨x, hx⟩ ⟨y, hy⟩

/-- **Proposition 3.C.1** (MWG, p. 47) on `X = ℝ^L_+`. A continuous rational preference relation
has a continuous utility representation (Debreu's theorem; Kreps's Proposition 2.9, no
monotonicity needed). The utility is continuous on all of `ℝ^L`. -/
theorem proposition_3_C_1 {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hr : RationalOn (nonnegOrthant L) r) (hc : PrefContinuous (nonnegOrthant L) r) :
    ∃ u : (Fin L → ℝ) → ℝ, Continuous u ∧ RepresentsOn (nonnegOrthant L) u r := by
  have hr' := (rationalOn_iff_rational _ r).mp hr
  have hc' := (prefContinuous_iff_continuousPreference hr).mp hc
  obtain ⟨v, hv, hvc⟩ := (proposition_2_9 L hr').mp hc'
  exact ⟨extendOrthant v, extendOrthant_continuous hvc, representsOn_extendOrthant hv⟩

/-- **Proposition 3.C.1** (MWG, p. 47) on any convex consumption set `X` (connected and
separable, as Kreps's general Debreu theorem requires): a continuous rational `≿` on `X` has a
utility representation continuous on `X`. -/
theorem proposition_3_C_1_convex {X : Set (Fin L → ℝ)} (hX : Convex ℝ X)
    {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop} (hr : RationalOn X r) (hc : PrefContinuous X r) :
    ∃ u : (Fin L → ℝ) → ℝ, ContinuousOn u X ∧ RepresentsOn X u r := by
  classical
  have hr' := (rationalOn_iff_rational X r).mp hr
  have hc' := (prefContinuous_iff_continuousPreference hr).mp hc
  have : PreconnectedSpace X := isPreconnected_iff_preconnectedSpace.mp hX.isPreconnected
  obtain ⟨v, hv, hvc, -⟩ := continuous_represents_of_continuous_connected hr' hc'
  refine ⟨fun x => if h : x ∈ X then v ⟨x, h⟩ else 0, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    convert hvc using 1
    funext x
    simp [x.2]
  · intro x hx y hy
    simp only [hx, hy, ↓reduceDIte]
    exact hv ⟨x, hx⟩ ⟨y, hy⟩

/-- **Proposition 3.C.1, the book's proof** (MWG, pp. 47-49). For a continuous, rational and
monotone `≿` on `ℝ^L_+` (`L ≥ 1`), the diagonal utility `u(x) = α(x)`, where `α(x) ≥ 0` and
`α(x)e ∼ x`, is a continuous representation. Kreps's diagonal construction (Steps 2-5, pp.
37-38) carries out exactly the book's argument. -/
theorem proposition_3_C_1_monotone (hL : 0 < L) {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hr : RationalOn (nonnegOrthant L) r) (hc : PrefContinuous (nonnegOrthant L) r)
    (hm : PrefMonotone (nonnegOrthant L) r) :
    ∃ u : (Fin L → ℝ) → ℝ, Continuous u ∧ RepresentsOn (nonnegOrthant L) u r ∧
      ∀ x ∈ nonnegOrthant L, 0 ≤ u x ∧ Indifferent r (fun _ => u x) x := by
  have hr' := (rationalOn_iff_rational _ r).mp hr
  have hc' := (prefContinuous_iff_continuousPreference hr).mp hc
  have hs : StrictAllIncreasePreference (restrictPref (nonnegOrthant L) r) :=
    fun x y hxy => hm y.1 y.2 x.1 x.2 hxy
  have hw := continuous_strictAllIncrease_monotone hr' hc' hs
  refine ⟨extendOrthant (DiagonalUtility hL hr' hc' hw),
    extendOrthant_continuous (diagonalUtility_continuous hL hr' hc' hw hs),
    representsOn_extendOrthant (diagonalUtility_represents hL hr' hc' hw hs), ?_⟩
  intro x hx
  rw [extendOrthant_apply _ hx]
  exact ⟨diagonalUtility_nonneg hL hr' hc' hw ⟨x, hx⟩,
    diagonalCoordinate_spec hL hr' hc' hw ⟨x, hx⟩⟩

/-- **Section 3.C** (MWG, p. 49). Any strictly increasing transformation `f ∘ u` of a utility
function representing `≿` also represents `≿`. -/
theorem representsOn_comp_strictMono {X : Set (Fin L → ℝ)} {u : (Fin L → ℝ) → ℝ}
    {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop} (hu : RepresentsOn X u r) {f : ℝ → ℝ}
    (hf : StrictMono f) : RepresentsOn X (f ∘ u) r := by
  intro x hx y hy
  rw [hu x hx y hy, Function.comp_apply, Function.comp_apply, hf.le_iff_le]

/-- The strictly increasing but discontinuous transformation `t ↦ t + [t > 1]`. -/
noncomputable def jumpTransform (t : ℝ) : ℝ := t + if 1 < t then 1 else 0

/-- **Section 3.C** (MWG, p. 49). Not every utility representing a continuous `≿` is
continuous: on `ℝ¹_+`, `u(x) = x` and its discontinuous strictly increasing transformation
`x + [x > 1]` both represent the same continuous preference. -/
theorem discontinuous_representation :
    RepresentsOn (nonnegOrthant 1) (fun x => x 0) (utilityPref fun x => x 0) ∧
      RepresentsOn (nonnegOrthant 1) (jumpTransform ∘ fun x => x 0)
        (utilityPref fun x => x 0) ∧
      ¬ Continuous (jumpTransform ∘ fun x : Fin 1 → ℝ => x 0) := by
  have hmono : StrictMono jumpTransform := by
    intro a b hab
    unfold jumpTransform
    split_ifs <;> linarith
  refine ⟨representsOn_utilityPref _ _, representsOn_comp_strictMono
    (representsOn_utilityPref _ _) hmono, fun hcont => ?_⟩
  have hcont' : Continuous jumpTransform := by
    have : jumpTransform = (jumpTransform ∘ fun x : Fin 1 → ℝ => x 0) ∘ fun t => fun _ => t := by
      funext t
      rfl
    rw [this]
    exact hcont.comp (continuous_pi fun _ => continuous_id :
      Continuous fun t : ℝ => (fun _ : Fin 1 => t))
  have hlim : Tendsto jumpTransform (𝓝[>] 1) (𝓝 (jumpTransform 1)) :=
    hcont'.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hlim2 : Tendsto jumpTransform (𝓝[>] 1) (𝓝 (1 + 1)) := by
    have : Tendsto (fun t : ℝ => t + 1) (𝓝[>] 1) (𝓝 (1 + 1)) :=
      ((continuous_id.add continuous_const).tendsto 1).mono_left nhdsWithin_le_nhds
    apply this.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp [jumpTransform, Set.mem_Ioi.mp ht]
  have := tendsto_nhds_unique hlim hlim2
  simp [jumpTransform] at this

/-- **Section 3.C** (MWG, p. 49). Monotonicity makes every representing utility increasing:
`u(x) > u(y)` whenever `x ≫ y`. -/
theorem utility_strict_of_monotone {X : Set (Fin L → ℝ)} {u : (Fin L → ℝ) → ℝ}
    {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop} (hu : RepresentsOn X u r)
    (hm : PrefMonotone X r) {x y : Fin L → ℝ} (hx : x ∈ X) (hy : y ∈ X)
    (hxy : ∀ l, y l < x l) : u y < u x :=
  (hu.strict_iff hx hy).mp (hm y hy x hx hxy)

/-- **Section 3.C** (MWG, p. 49). On a convex consumption set, `≿` is convex iff any utility
representing it is quasiconcave. -/
theorem prefConvex_iff_quasiconcaveOn {X : Set (Fin L → ℝ)} (hX : Convex ℝ X)
    {u : (Fin L → ℝ) → ℝ} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop} (hu : RepresentsOn X u r) :
    PrefConvex X r ↔ QuasiconcaveOn ℝ X u := by
  rw [prefConvex_iff_of_convex hX, definition_M_C_3 hX]
  constructor
  · intro h t x hx x' hx' htx htx' α h0 h1
    rcases le_total (u x) (u x') with hle | hle
    · have := h x hx x hx x' hx' ((hu x hx x hx).mpr le_rfl) ((hu x' hx' x hx).mpr hle) α h0 h1
      exact htx.trans ((hu _ (hX hx hx' h0
        (show (0 : ℝ) ≤ 1 - α by linarith) (by ring)) x hx).mp this)
    · have := h x' hx' x hx x' hx' ((hu x hx x' hx').mpr hle) ((hu x' hx' x' hx').mpr le_rfl)
        α h0 h1
      exact htx'.trans ((hu _ (hX hx hx' h0
        (show (0 : ℝ) ≤ 1 - α by linarith) (by ring)) x' hx').mp this)
  · intro h x hx y hy z hz hyx hzx α h0 h1
    exact (hu _ (hX hy hz h0 (show (0 : ℝ) ≤ 1 - α by linarith) (by ring)) x hx).mpr
      (h (u x) y hy z hz ((hu y hy x hx).mp hyx) ((hu z hz x hx).mp hzx) α h0 h1)

/-- **Section 3.C** (MWG, p. 49). On a convex consumption set, `≿` is strictly convex iff any
utility representing it is strictly quasiconcave. -/
theorem prefStrictlyConvex_iff_strictlyQuasiconcaveOn {X : Set (Fin L → ℝ)} (hX : Convex ℝ X)
    {u : (Fin L → ℝ) → ℝ} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop} (hu : RepresentsOn X u r) :
    PrefStrictlyConvex X r ↔ StrictlyQuasiconcaveOn X u := by
  constructor
  · intro h
    refine ⟨hX, fun x hx x' hx' hne α h0 h1 t ht ht' => ?_⟩
    have hmem := hX hx hx' h0.le (show (0 : ℝ) ≤ 1 - α by linarith) (by ring)
    rcases le_total (u x) (u x') with hle | hle
    · have := h x hx x hx x' hx' ((hu x hx x hx).mpr le_rfl) ((hu x' hx' x hx).mpr hle) hne α
        h0 h1
      exact ht.trans_lt ((hu.strict_iff hmem hx).mp this)
    · have := h x' hx' x hx x' hx' ((hu x hx x' hx').mpr hle) ((hu x' hx' x' hx').mpr le_rfl)
        hne α h0 h1
      exact ht'.trans_lt ((hu.strict_iff hmem hx').mp this)
  · rintro ⟨-, h⟩ x hx y hy z hz hyx hzx hne α h0 h1
    exact (hu.strict_iff (hX hy hz h0.le (show (0 : ℝ) ≤ 1 - α by linarith) (by ring)) hx).mpr
      (h y hy z hz hne α h0 h1 (u x) ((hu y hy x hx).mp hyx) ((hu z hz x hx).mp hzx))

/-- The utility `g(x) = min(x, 1) + max(x - 2, 0)`, flat on `[1, 2]`. -/
noncomputable def flatUtility (x : Fin 1 → ℝ) : ℝ := min (x 0) 1 + max (x 0 - 2) 0

/-- **Section 3.C** (MWG, p. 50). A convex preference relation may have no concave utility
representation at all: the preference on `ℝ¹_+` represented by `min(x, 1) + max(x - 2, 0)`
(indifferent on `[1, 2]`, increasing elsewhere) is convex, but no utility representing it is
concave on `ℝ¹_+`. -/
theorem convex_pref_no_concave_utility :
    PrefConvex (nonnegOrthant 1) (utilityPref flatUtility) ∧
      ¬ ∃ v : (Fin 1 → ℝ) → ℝ, RepresentsOn (nonnegOrthant 1) v (utilityPref flatUtility) ∧
        ConcaveOn ℝ (nonnegOrthant 1) v := by
  have hmono : Monotone flatUtility := by
    intro x y hxy
    unfold flatUtility
    have := hxy 0
    exact add_le_add (min_le_min_right _ this) (max_le_max_right _ (by linarith))
  constructor
  · rw [prefConvex_iff_quasiconcaveOn (convex_nonnegOrthant 1)
      (representsOn_utilityPref _ flatUtility)]
    rw [equation_M_C_7 (convex_nonnegOrthant 1)]
    intro x _ x' _ α h0 h1
    rcases le_total (x 0) (x' 0) with h | h
    · refine (min_le_left _ _).trans (hmono fun l => ?_)
      fin_cases l
      simp only [Fin.zero_eta, Fin.isValue, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      nlinarith
    · refine (min_le_right _ _).trans (hmono fun l => ?_)
      fin_cases l
      simp only [Fin.zero_eta, Fin.isValue, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      nlinarith
  · rintro ⟨v, hv, hconc⟩
    have hp : ∀ c : ℝ, 0 ≤ c → (fun _ => c : Fin 1 → ℝ) ∈ nonnegOrthant 1 := fun c hc _ => hc
    have h12 : v (fun _ => 2) = v (fun _ => 1) :=
      (hv.indifferent_iff (hp 2 (by norm_num)) (hp 1 (by norm_num))).mp
        (by simp [Indifferent, utilityPref, flatUtility])
    have h23 : v (fun _ => 2) < v (fun _ => 3) :=
      (hv.strict_iff (hp 3 (by norm_num)) (hp 2 (by norm_num))).mp
        (by simp [Strict, utilityPref, flatUtility]; norm_num)
    have := hconc.2 (hp 1 (by norm_num)) (hp 3 (by norm_num))
      (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num)
    have hmid : ((1 / 2 : ℝ) • (fun _ => (1 : ℝ)) + (1 / 2 : ℝ) • fun _ => (3 : ℝ) :
        Fin 1 → ℝ) = fun _ => 2 := by
      funext _
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      norm_num
    rw [hmid, smul_eq_mul, smul_eq_mul] at this
    linarith

/-- **Exercise 3.C.4** (MWG, p. 96). A preference relation that is representable by a utility
function but not continuous: on `ℝ¹_+`, the one represented by `u(x) = [x > 0]`. -/
theorem exercise_3_C_4 :
    RepresentsOn (nonnegOrthant 1) (fun x => if 0 < x 0 then (1 : ℝ) else 0)
        (utilityPref fun x => if 0 < x 0 then (1 : ℝ) else 0) ∧
      ¬ PrefContinuous (nonnegOrthant 1)
        (utilityPref fun x => if 0 < x 0 then (1 : ℝ) else 0) := by
  refine ⟨representsOn_utilityPref _ _, fun hc => ?_⟩
  have hxs : ∀ n : ℕ, (fun _ => 1 / ((n : ℝ) + 1) : Fin 1 → ℝ) ∈ nonnegOrthant 1 :=
    fun n _ => by positivity
  have hy : (fun _ => 1 : Fin 1 → ℝ) ∈ nonnegOrthant 1 := fun _ => zero_le_one
  have hlim : Tendsto (fun n : ℕ => (fun _ => 1 / ((n : ℝ) + 1) : Fin 1 → ℝ)) atTop
      (𝓝 (0 : Fin 1 → ℝ)) := by
    rw [tendsto_pi_nhds]
    intro _
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have := hc _ (fun _ => fun _ => 1) 0 _ hxs (fun _ => hy) (fun _ => le_rfl) hy
    (fun n => by
      simp only [utilityPref, show (0 : ℝ) < 1 / ((n : ℝ) + 1) by positivity, ↓reduceIte,
        zero_lt_one, le_refl]) hlim tendsto_const_nhds
  simp only [utilityPref, Pi.zero_apply, lt_irrefl, ↓reduceIte, zero_lt_one] at this
  linarith

end MWG.ClassicalDemand
