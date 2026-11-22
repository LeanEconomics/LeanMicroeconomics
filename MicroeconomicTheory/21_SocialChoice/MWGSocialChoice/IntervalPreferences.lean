/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGSocialChoice.SinglePeaked
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Quasiconvex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Single-peaked preferences on an interval

MWG, Section 21.D, p. 801 (Example 21.D.4) and Exercises 21.D.4 and 21.D.10, pp. 813-814.

On `X = [a, b] ⊆ ℝ` with its natural order, a continuous rational preference is single peaked
iff it is strictly convex: `αy + (1 - α)z ≻ w` whenever `y ≿ w`, `z ≿ w`, `y ≠ z` and
`α ∈ (0, 1)` (Example 21.D.4). Necessity (Exercise 21.D.4) needs neither continuity nor
compactness. Sufficiency uses a maximal element, which exists by continuity and compactness.

Exercise 21.D.10 (majority voting over a proportional tax rate `t ∈ [0, 1]`, odd number of
agents, positive wealths, increasing utilities of wealth).

**Corrections.**
1. Example 21.D.4 needs `X = [a, b]` nonempty (`a ≤ b`): for `a > b` every relation is
   strictly convex but none is single peaked.
2. Exercise 21.D.10(b): an agent whose wealth equals the mean `w̄` is indifferent between all
   tax rates, so her preference is not single peaked (`exercise_21_D_10b_mean_agent`); all other
   agents are single peaked. The Condorcet-winner claims hold as stated.
3. Exercise 21.D.10(d) is false: with the deadweight loss `(1 - t²)wᵢ`, every agent's
   preference over tax rates is still single peaked (`exercise_21_D_10d`), because ex post
   wealth `(1 - t²)((1 - t)wᵢ + t w̄)` is a product of positive affine functions, hence strictly
   log-concave on `[0, 1)`.
-/

namespace MWG.SocialChoice

open Kreps.ChoicePreferenceUtility Finset

variable {a b : ℝ}

/-- The convex combination `αy + (1 - α)z` of two points of `[a, b]`, for `α ∈ [0, 1]`. -/
def iccComb (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (y z : Set.Icc a b) : Set.Icc a b :=
  ⟨α * y + (1 - α) * z, by
    have h := (convex_Icc a b) y.2 z.2 hα.1 (sub_nonneg.2 hα.2) (add_sub_cancel α 1)
    simpa [smul_eq_mul] using h⟩

/-- **Example 21.D.4** (MWG, p. 801). A preference on `[a, b]` is strictly convex:
`αy + (1 - α)z ≻ w` whenever `y ≿ w`, `z ≿ w`, `y ≠ z` and `α ∈ (0, 1)`. -/
def StrictlyConvexPref (r : Set.Icc a b → Set.Icc a b → Prop) : Prop :=
  ∀ w y z : Set.Icc a b, ∀ α (hα : α ∈ Set.Ioo (0 : ℝ) 1), r y w → r z w → y ≠ z →
    Strict r (iccComb α (Set.Ioo_subset_Icc_self hα) y z) w

/-- A preference on `[a, b]` is continuous: its graph is closed (MWG, Definition 3.C.1). -/
def ContinuousPref (r : Set.Icc a b → Set.Icc a b → Prop) : Prop :=
  IsClosed {q : Set.Icc a b × Set.Icc a b | r q.1 q.2}

/-- **Exercise 21.D.4** (MWG, p. 813). A single-peaked preference on `[a, b]` is strictly
convex. (Continuity is not needed.) -/
theorem exercise_21_D_4 {r : Set.Icc a b → Set.Icc a b → Prop} (hr : SinglePeaked r) :
    StrictlyConvexPref r := by
  obtain ⟨hrat, x, hx⟩ := hr
  intro w y z α hα hyw hzw hyz
  set m := iccComb α (Set.Ioo_subset_Icc_self hα) y z with hm
  have hm' : (m : ℝ) = α * y + (1 - α) * z := rfl
  have h1 := hα.1
  have h2 := hα.2
  have hyz' : (y : ℝ) ≠ z := fun e => hyz (Subtype.ext e)
  rcases lt_or_gt_of_ne hyz' with hlt | hgt
  · have hym : y < m := by
      rw [← Subtype.coe_lt_coe, hm']
      nlinarith
    have hmz : m < z := by
      rw [← Subtype.coe_lt_coe, hm']
      nlinarith
    by_cases hmx : m ≤ x
    · exact MWG.PreferenceChoice.proposition_1_B_1_iii hrat ((hx y m).1 hmx hym) hyw
    · push Not at hmx
      exact MWG.PreferenceChoice.proposition_1_B_1_iii hrat ((hx z m).2 hmx.le hmz) hzw
  · have hzm : z < m := by
      rw [← Subtype.coe_lt_coe, hm']
      nlinarith
    have hmy : m < y := by
      rw [← Subtype.coe_lt_coe, hm']
      nlinarith
    by_cases hmx : m ≤ x
    · exact MWG.PreferenceChoice.proposition_1_B_1_iii hrat ((hx z m).1 hmx hzm) hzw
    · push Not at hmx
      exact MWG.PreferenceChoice.proposition_1_B_1_iii hrat ((hx y m).2 hmx.le hmy) hyw

/-- A continuous rational preference on a nonempty compact interval has a maximal element. -/
theorem exists_max_of_continuousPref (hab : a ≤ b) {r : Set.Icc a b → Set.Icc a b → Prop}
    (hr : Rational r) (hc : ContinuousPref r) : ∃ x, ∀ y, r x y := by
  have hne : Nonempty (Set.Icc a b) := ⟨⟨a, le_rfl, hab⟩⟩
  have hclosed : ∀ y : Set.Icc a b, IsClosed {x | r x y} := fun y =>
    hc.preimage (Continuous.prodMk continuous_id continuous_const)
  obtain ⟨x, hx⟩ := isCompact_univ.inter_iInter_nonempty (fun y => {x | r x y}) hclosed
    fun u => by
      classical
      rcases u.eq_empty_or_nonempty with hu | hu
      · obtain ⟨x⟩ := hne
        exact ⟨x, by simp [hu]⟩
      · obtain ⟨m, -, hm⟩ := rational_acyclic hr u hu
        exact ⟨m, Set.mem_univ m, Set.mem_iInter₂.2 fun y hy => hm y hy⟩
  exact ⟨x, fun y => Set.mem_iInter.1 hx.2 y⟩

/-- **Example 21.D.4** (MWG, p. 801), sufficiency. A continuous, rational, strictly convex
preference on a nonempty interval `[a, b]` is single peaked, with peak its maximal element. -/
theorem example_21_D_4_sufficiency (hab : a ≤ b) {r : Set.Icc a b → Set.Icc a b → Prop}
    (hr : Rational r) (hc : ContinuousPref r) (hsc : StrictlyConvexPref r) : SinglePeaked r := by
  obtain ⟨x, hx⟩ := exists_max_of_continuousPref hab hr hc
  have best : ∀ y, y ≠ x → Strict r x y := by
    intro y hyx
    refine ⟨hx y, fun hyx' => ?_⟩
    have half : (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by norm_num
    exact (hsc x y x (1 / 2) half hyx' (complete_refl hr.1 x) hyx).2 (hx _)
  have between : ∀ y z : Set.Icc a b, ((y : ℝ) < z ∧ (z : ℝ) < x) ∨ ((x : ℝ) < z ∧ (z : ℝ) < y) →
      Strict r z y := by
    intro y z hyzx
    have hxy : (x : ℝ) ≠ y := by rcases hyzx with h | h <;> intro e <;> linarith [e ▸ h.1]
    set α := ((z : ℝ) - y) / ((x : ℝ) - y) with hα
    have hαI : α ∈ Set.Ioo (0 : ℝ) 1 := by
      rcases hyzx with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · constructor
        · exact div_pos (by linarith) (by linarith)
        · rw [div_lt_one (by linarith)]
          linarith
      · constructor
        · exact div_pos_of_neg_of_neg (by linarith) (by linarith)
        · rw [div_lt_one_of_neg (by linarith)]
          linarith
    have hcomb : iccComb α (Set.Ioo_subset_Icc_self hαI) x y = z := by
      apply Subtype.ext
      change α * x + (1 - α) * y = z
      rw [hα]
      field_simp [sub_ne_zero.2 hxy]
      ring
    have := hsc y x y α hαI (hx y) (complete_refl hr.1 y) (fun e => hxy (congrArg _ e))
    rwa [hcomb] at this
  refine ⟨hr, x, fun y z => ⟨fun hzx hyz => ?_, fun hxz hzy => ?_⟩⟩
  · rcases eq_or_lt_of_le hzx with e | e
    · rw [e]
      exact best y (ne_of_lt (e ▸ hyz))
    · exact between y z (Or.inl ⟨Subtype.coe_lt_coe.2 hyz, Subtype.coe_lt_coe.2 e⟩)
  · rcases eq_or_lt_of_le hxz with e | e
    · rw [← e]
      exact best y (ne_of_gt (e ▸ hzy))
    · exact between y z (Or.inr ⟨Subtype.coe_lt_coe.2 e, Subtype.coe_lt_coe.2 hzy⟩)

/-- **Example 21.D.4** (MWG, p. 801). On a nonempty interval `[a, b]`, a continuous rational
preference is single peaked iff it is strictly convex. -/
theorem example_21_D_4 (hab : a ≤ b) {r : Set.Icc a b → Set.Icc a b → Prop} (hr : Rational r)
    (hc : ContinuousPref r) : SinglePeaked r ↔ StrictlyConvexPref r :=
  ⟨exercise_21_D_4, example_21_D_4_sufficiency hab hr hc⟩

/-- **Example 21.D.4**, correction (MWG, p. 801). On an empty "interval" (`a > b`) every relation
is strictly convex, but none is single peaked. -/
theorem example_21_D_4_empty (hab : b < a) (r : Set.Icc a b → Set.Icc a b → Prop) :
    StrictlyConvexPref r ∧ ¬SinglePeaked r := by
  have hem : ∀ w : Set.Icc a b, False := fun w => by linarith [w.2.1, w.2.2]
  exact ⟨fun w => (hem w).elim, fun h => hem h.2.choose⟩

/-- **Example 21.D.4** (MWG, p. 801). Preferences generated by a strictly quasiconcave utility
are strictly convex. -/
theorem strictlyConvex_of_strictQuasiconcave {u : ℝ → ℝ}
    (hu : ∀ y z : ℝ, y ∈ Set.Icc a b → z ∈ Set.Icc a b → y ≠ z → ∀ α ∈ Set.Ioo (0 : ℝ) 1,
      min (u y) (u z) < u (α * y + (1 - α) * z)) :
    StrictlyConvexPref fun s t : Set.Icc a b => u t ≤ u s := by
  intro w y z α hα hyw hzw hyz
  have := hu y z y.2 z.2 (fun e => hyz (Subtype.ext e)) α hα
  have hmin : u w ≤ min (u y) (u z) := le_min hyw hzw
  exact ⟨by change u w ≤ u (α * y + (1 - α) * z); linarith,
    fun h => by change u (α * y + (1 - α) * z) ≤ u w at h; linarith⟩

end MWG.SocialChoice
