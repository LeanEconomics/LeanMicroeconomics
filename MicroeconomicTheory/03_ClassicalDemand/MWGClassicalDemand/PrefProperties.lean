/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGClassicalDemand.Basic

/-!
# Preference relations: basic properties

MWG, Section 3.B, pp. 41-45, and Exercises 3.B.1-3.B.3 (pp. 43, 96).

* Exercise 3.B.1: strong monotonicity implies monotonicity, and monotonicity (with free
  disposal) implies local nonsatiation. Both need at least one commodity (`0 < L`): on
  `ℝ^0_+ = {0}` the indifferent relation is strongly monotone but neither monotone nor locally
  nonsatiated (`exercise_3_B_1_needs_commodity`).
* Local nonsatiation rules out thick indifference sets and, on `ℝ^L_+`, preferences for which
  every commodity is a bad (p. 43).
* Definition 3.B.4 in its pointwise form; the small-type remark that convexity forces a
  convex consumption set (true for complete preferences); strict convexity implies convexity;
  the half-half mixture of indifferent bundles is no worse than either (p. 44); Figure 3.B.4.
* Exercise 3.B.2: on `ℝ^L_+`, transitive, locally nonsatiated, weakly monotone preferences
  are monotone.
* Exercise 3.B.3: a convex, locally nonsatiated, non-monotone preference.
-/

namespace MWG.ClassicalDemand

open MWG.ConsumerChoice Kreps.PreferenceProperties

variable {L : ℕ}

/-- A relation with `y ≿ z` and `z ≻ x` has `y ≻ x`, when it is transitive on the bundles. -/
theorem prefs_strict_of_weak_strict {X : Set (Fin L → ℝ)}
    {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (ht : ∀ x ∈ X, ∀ y ∈ X, ∀ z ∈ X, r x y → r y z → r x z) {x y z : Fin L → ℝ}
    (hx : x ∈ X) (hy : y ∈ X) (hz : z ∈ X) (hyz : r y z) (hzx : Strict r z x) :
    Strict r y x :=
  ⟨ht y hy z hz x hx hyz hzx.1, fun hxy => hzx.2 (ht x hx y hy z hz hxy hyz)⟩

/-- **Exercise 3.B.1(a)** (MWG, pp. 43, 96). With at least one commodity, a strongly
monotone preference relation is monotone. -/
theorem exercise_3_B_1a (hL : 0 < L) {X : Set (Fin L → ℝ)}
    {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop} (h : PrefStronglyMonotone X r) :
    PrefMonotone X r := by
  intro x hx y hy hxy
  refine h x hx y hy (fun l => (hxy l).le) ?_
  intro he
  have := hxy ⟨0, hL⟩
  rw [he] at this
  exact lt_irrefl _ this

/-- **Exercise 3.B.1(b)** (MWG, pp. 43, 96). With at least one commodity and a consumption set
closed under increases (the free-disposal assumption made for Definition 3.B.2), a monotone
preference relation is locally nonsatiated. -/
theorem exercise_3_B_1b (hL : 0 < L) {X : Set (Fin L → ℝ)}
    (hX : ∀ x ∈ X, ∀ y, x ≤ y → y ∈ X) {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (h : PrefMonotone X r) : LocallyNonsatiated X r := by
  intro x hx ε hε
  have hL' : (0 : ℝ) < Real.sqrt L := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hL)
  set c := ε / Real.sqrt L with hc
  have hc0 : 0 < c := div_pos hε hL'
  have hmem : (x + fun _ => c) ∈ X := hX x hx _ fun l => by simp [hc0.le]
  refine ⟨x + fun _ => c, hmem, ?_, h x hx _ hmem fun l => by simp [hc0]⟩
  rw [euclidDist_add_const, abs_of_pos hc0, hc, mul_div_cancel₀ _ hL'.ne']

/-- `ℝ^L_+` is closed under increases. -/
theorem nonnegOrthant_upward {x : Fin L → ℝ} (hx : x ∈ nonnegOrthant L) {y : Fin L → ℝ}
    (hxy : x ≤ y) : y ∈ nonnegOrthant L := fun l => (hx l).trans (hxy l)

/-- **Exercise 3.B.1(b)** on `X = ℝ^L_+`. -/
theorem exercise_3_B_1b_orthant (hL : 0 < L) {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (h : PrefMonotone (nonnegOrthant L) r) : LocallyNonsatiated (nonnegOrthant L) r :=
  exercise_3_B_1b hL (fun _ hx _ hxy => nonnegOrthant_upward hx hxy) h

/-- **Exercise 3.B.1** (MWG, p. 43): the hypothesis `0 < L` cannot be dropped. With no
commodities, the relation that ranks everything indifferent is strongly monotone on
`ℝ^0_+`, but it is neither monotone nor locally nonsatiated. -/
theorem exercise_3_B_1_needs_commodity :
    PrefStronglyMonotone (nonnegOrthant 0) (fun _ _ => True) ∧
      ¬ PrefMonotone (nonnegOrthant 0) (fun _ _ => True) ∧
      ¬ LocallyNonsatiated (nonnegOrthant 0) (fun _ _ => True) := by
  have h0 : (0 : Fin 0 → ℝ) ∈ nonnegOrthant 0 := fun l => l.elim0
  refine ⟨fun x _ y _ _ hne => absurd (funext fun l => l.elim0) hne, fun h => ?_, fun h => ?_⟩
  · exact (h 0 h0 0 h0 fun l => l.elim0).2 trivial
  · obtain ⟨y, -, -, hy⟩ := h 0 h0 1 one_pos
    exact hy.2 trivial

/-- **Section 3.B** (MWG, p. 43). Local nonsatiation rules out "thick" indifference sets: no
indifference set contains all bundles of `X` within some positive distance of one of its
points (Figure 3.B.2(a)). -/
theorem locallyNonsatiated_no_thick_indifference {X : Set (Fin L → ℝ)}
    {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop} (h : LocallyNonsatiated X r) {x : Fin L → ℝ}
    (hx : x ∈ X) {ε : ℝ} (hε : 0 < ε) :
    ¬ ∀ y ∈ X, euclidDist y x ≤ ε → y ∈ indifferenceSet X r x := by
  intro hthick
  obtain ⟨y, hy, hd, hs⟩ := h x hx ε hε
  exact hs.2 (hthick y hy hd).2.2

/-- **Section 3.B** (MWG, p. 43). On `X = ℝ^L_+`, local nonsatiation rules out preferences
for which all commodities are bads (less is weakly better), since then `0` would be a
satiation point. -/
theorem locallyNonsatiated_not_all_bads {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (h : LocallyNonsatiated (nonnegOrthant L) r)
    (hbad : ∀ x ∈ nonnegOrthant L, ∀ y ∈ nonnegOrthant L, x ≤ y → r x y) : False := by
  have h0 : (0 : Fin L → ℝ) ∈ nonnegOrthant L := fun _ => le_rfl
  obtain ⟨y, hy, -, hs⟩ := h 0 h0 1 one_pos
  exact hs.2 (hbad 0 h0 y hy hy)

/-- **Definition 3.B.4** (MWG, p. 44), pointwise form: `≿` is convex on `X` if and only if
`y ≿ x` and `z ≿ x` (all in `X`) imply that `αy + (1 - α)z` lies in `X` and `≿ x`, for
`α ∈ [0, 1]`. -/
theorem definition_3_B_4 (X : Set (Fin L → ℝ)) (r : (Fin L → ℝ) → (Fin L → ℝ) → Prop) :
    PrefConvex X r ↔ ∀ x ∈ X, ∀ y ∈ X, ∀ z ∈ X, r y x → r z x → ∀ α : ℝ, 0 ≤ α → α ≤ 1 →
      α • y + (1 - α) • z ∈ X ∧ r (α • y + (1 - α) • z) x := by
  constructor
  · intro h x hx y hy z hz hyx hzx α h0 h1
    exact h x hx ⟨hy, hyx⟩ ⟨hz, hzx⟩ h0 (by linarith) (by ring)
  · intro h x hx y hyx z hzx a b ha hb hab
    have hb' : b = 1 - a := by linarith
    rw [hb']
    exact h x hx y hyx.1 z hzx.1 hyx.2 hzx.2 a ha (by linarith)

/-- **Definition 3.B.4** on a convex consumption set: membership of the mixture is automatic. -/
theorem prefConvex_iff_of_convex {X : Set (Fin L → ℝ)} (hX : Convex ℝ X)
    (r : (Fin L → ℝ) → (Fin L → ℝ) → Prop) :
    PrefConvex X r ↔ ∀ x ∈ X, ∀ y ∈ X, ∀ z ∈ X, r y x → r z x → ∀ α : ℝ, 0 ≤ α → α ≤ 1 →
      r (α • y + (1 - α) • z) x := by
  rw [definition_3_B_4]
  constructor
  · intro h x hx y hy z hz hyx hzx α h0 h1
    exact (h x hx y hy z hz hyx hzx α h0 h1).2
  · intro h x hx y hy z hz hyx hzx α h0 h1
    exact ⟨hX hy hz h0 (by linarith) (by ring), h x hx y hy z hz hyx hzx α h0 h1⟩

/-- **Section 3.B, small type** (MWG, p. 44). "The convexity assumption can hold only if `X`
is convex": a complete preference relation that is convex on `X` forces `X` to be convex. -/
theorem convex_of_prefConvex {X : Set (Fin L → ℝ)} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hc : ∀ x ∈ X, ∀ y ∈ X, r x y ∨ r y x) (h : PrefConvex X r) : Convex ℝ X := by
  intro y hy z hz a b ha hb hab
  have hrefl : ∀ v ∈ X, r v v := fun v hv => (hc v hv v hv).elim id id
  rcases hc y hy z hz with hyz | hzy
  · exact (h z hz ⟨hy, hyz⟩ ⟨hz, hrefl z hz⟩ ha hb hab).1
  · exact (h y hy ⟨hy, hrefl y hy⟩ ⟨hz, hzy⟩ ha hb hab).1

/-- **Section 3.B** (MWG, p. 44). Under convexity, if `x ∼ y` then the half-half mixture
`½x + ½y` is at least as good as `x` and as `y`. -/
theorem half_mixture_of_prefConvex {X : Set (Fin L → ℝ)}
    {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop} (hc : ∀ x ∈ X, ∀ y ∈ X, r x y ∨ r y x)
    (h : PrefConvex X r) {x y : Fin L → ℝ} (hx : x ∈ X) (hy : y ∈ X)
    (hxy : Indifferent r x y) :
    r ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) x ∧ r ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) y := by
  have hrefl : ∀ v ∈ X, r v v := fun v hv => (hc v hv v hv).elim id id
  have hhalf : (1 / 2 : ℝ) + 1 / 2 = 1 := by norm_num
  exact ⟨(h x hx ⟨hx, hrefl x hx⟩ ⟨hy, hxy.2⟩ (by norm_num) (by norm_num) hhalf).2,
    (h y hy ⟨hx, hxy.1⟩ ⟨hy, hrefl y hy⟩ (by norm_num) (by norm_num) hhalf).2⟩

/-- **Definition 3.B.5** (MWG, p. 44): strict convexity strengthens convexity. On a convex
consumption set, a complete, strictly convex preference relation is convex. -/
theorem PrefStrictlyConvex.prefConvex {X : Set (Fin L → ℝ)} (hX : Convex ℝ X)
    {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop} (h : PrefStrictlyConvex X r) : PrefConvex X r := by
  rw [prefConvex_iff_of_convex hX]
  intro x hx y hy z hz hyx hzx α h0 h1
  rcases eq_or_ne y z with rfl | hne
  · rw [← add_smul, add_sub_cancel, one_smul]
    exact hyx
  rcases h0.lt_or_eq with h0 | rfl
  · rcases h1.lt_or_eq with h1 | rfl
    · exact (h x hx y hy z hz hyx hzx hne α h0 h1).1
    · simpa using hyx
  · simpa using hzx

/-- **Exercise 3.B.2** (MWG, p. 96). On `X = ℝ^L_+`, a transitive, locally nonsatiated and
weakly monotone (`x ≥ y ⟹ x ≿ y`) preference relation is monotone. -/
theorem exercise_3_B_2 {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (ht : ∀ x ∈ nonnegOrthant L, ∀ y ∈ nonnegOrthant L, ∀ z ∈ nonnegOrthant L,
      r x y → r y z → r x z)
    (hlns : LocallyNonsatiated (nonnegOrthant L) r)
    (hweak : ∀ x ∈ nonnegOrthant L, ∀ y ∈ nonnegOrthant L, y ≤ x → r x y) :
    PrefMonotone (nonnegOrthant L) r := by
  intro x hx y hy hxy
  obtain ⟨ε, hε, hεle⟩ := exists_pos_le_of_pos (fun l => y l - x l) fun l => by
    simp only [sub_pos]
    exact hxy l
  obtain ⟨z, hz, hzd, hzs⟩ := hlns x hx ε hε
  have hzy : z ≤ y := by
    intro l
    have h1 := (abs_le.mp ((abs_sub_le_euclidDist z x l).trans hzd)).2
    have h2 := hεle l
    linarith
  exact prefs_strict_of_weak_strict ht hx hy hz (hweak y hy z hz hzy) hzs

/-- The utility `u(x) = x₁ - x₂` of Exercise 3.B.3 (good 2 is a bad). -/
def exercise_3_B_3_utility (x : Fin 2 → ℝ) : ℝ := x 0 - x 1

/-- **Exercise 3.B.3** (MWG, p. 96). A preference relation on `ℝ²_+` that is convex and locally
nonsatiated but not monotone: the one represented by `u(x) = x₁ - x₂`. -/
theorem exercise_3_B_3 :
    PrefConvex (nonnegOrthant 2) (utilityPref exercise_3_B_3_utility) ∧
      LocallyNonsatiated (nonnegOrthant 2) (utilityPref exercise_3_B_3_utility) ∧
      ¬ PrefMonotone (nonnegOrthant 2) (utilityPref exercise_3_B_3_utility) := by
  have hrep := representsOn_utilityPref (nonnegOrthant 2) exercise_3_B_3_utility
  refine ⟨?_, ?_, ?_⟩
  · rw [prefConvex_iff_of_convex (convex_nonnegOrthant 2)]
    intro x _ y _ z _ hyx hzx α h0 h1
    simp only [utilityPref, exercise_3_B_3_utility, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul] at *
    nlinarith
  · intro x hx ε hε
    refine ⟨x + Pi.single 0 ε, ?_, ?_, ?_⟩
    · intro l
      fin_cases l <;> simp [hx 0, hx 1, hε.le, add_nonneg]
    · calc euclidDist (x + Pi.single 0 ε) x ≤ Real.sqrt (ε ^ 2) :=
            Real.sqrt_le_sqrt (by simp [Fin.sum_univ_two])
        _ = ε := Real.sqrt_sq hε.le
    · rw [hrep.strict_iff (fun l => by fin_cases l <;> simp [hx 0, hx 1, hε.le, add_nonneg])
        hx]
      simp [exercise_3_B_3_utility, hε]
  · intro h
    have h0 : (0 : Fin 2 → ℝ) ∈ nonnegOrthant 2 := fun _ => le_rfl
    have hy : (![1, 3] : Fin 2 → ℝ) ∈ nonnegOrthant 2 := by
      intro l
      fin_cases l <;> norm_num
    have := (h 0 h0 ![1, 3] hy fun l => by fin_cases l <;> norm_num).1
    simp [utilityPref, exercise_3_B_3_utility] at this

/-- The linear utility `u(x) = x₁ + x₂` of Figure 3.B.4. -/
def figure_3_B_4_utility (x : Fin 2 → ℝ) : ℝ := x 0 + x 1

/-- **Figure 3.B.4** (MWG, p. 45). A convex but not strictly convex preference relation on
`ℝ²_+`: the one represented by `u(x) = x₁ + x₂` (its indifference sets are line segments). -/
theorem figure_3_B_4 :
    PrefConvex (nonnegOrthant 2) (utilityPref figure_3_B_4_utility) ∧
      ¬ PrefStrictlyConvex (nonnegOrthant 2) (utilityPref figure_3_B_4_utility) := by
  refine ⟨?_, fun h => ?_⟩
  · rw [prefConvex_iff_of_convex (convex_nonnegOrthant 2)]
    intro x _ y _ z _ hyx hzx α h0 h1
    simp only [utilityPref, figure_3_B_4_utility, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul] at *
    nlinarith
  · have hy : (![1, 0] : Fin 2 → ℝ) ∈ nonnegOrthant 2 := by
      intro l
      fin_cases l <;> norm_num
    have hz : (![0, 1] : Fin 2 → ℝ) ∈ nonnegOrthant 2 := by
      intro l
      fin_cases l <;> norm_num
    have hne : (![1, 0] : Fin 2 → ℝ) ≠ ![0, 1] := by
      intro he
      have := congrFun he 0
      norm_num at this
    have := (h _ hy _ hy _ hz (by simp [utilityPref]) (by simp [utilityPref, figure_3_B_4_utility])
      hne (1 / 2) (by norm_num) (by norm_num)).2
    apply this
    simp [utilityPref, figure_3_B_4_utility]

end MWG.ClassicalDemand
