/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGProduction.Geometry
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Exercises 5.B.4-5.B.6 (MWG, pp. 160-161)

* **Exercise 5.B.4**: the additive closure `Y⁺` (the smallest additive set containing `Y`), and
  the decreasing-returns technology `{y₁ ≤ 0, y₂ ≤ √(-y₁)}` whose additive closure is not closed
  (it contains `(-ε, 1)` for every `ε > 0` but not `(0, 1)`).
* **Exercise 5.B.5**: closed, convex and `-ℝ^L_+ ⊆ Y` imply free disposal.
* **Exercise 5.B.6**: two techniques with input requirement functions `φ₁, φ₂`; (b) subadditive
  `φ_i` give additivity; (c) first-order conditions and their sufficiency for convex `φ_i`;
  (d) with strictly concave `φ_i` a cost-minimizing plan never uses both techniques.
-/

namespace MWG.Production

open MWG.ClassicalDemand MWG.ConsumerChoice Filter Topology

variable {L : ℕ}

/-- **Exercise 5.B.4** (MWG, p. 160). The additive closure `Y⁺`: all finite sums of elements of
`Y` (at least one). -/
def addClosure (Y : Set (Fin L → ℝ)) : Set (Fin L → ℝ) :=
  {y | ∃ (k : ℕ) (ys : ℕ → Fin L → ℝ), (∀ i ≤ k, ys i ∈ Y) ∧ y = ∑ i ∈ Finset.range (k + 1), ys i}

/-- **Exercise 5.B.4** (MWG, p. 160). `Y⁺` contains `Y`, is additive, and is contained in every
additive set containing `Y`: it is the smallest additive production set containing `Y`. -/
theorem exercise_5_B_4_closure (Y : Set (Fin L → ℝ)) :
    Y ⊆ addClosure Y ∧ Additive (addClosure Y) ∧
      ∀ Z : Set (Fin L → ℝ), Y ⊆ Z → Additive Z → addClosure Y ⊆ Z := by
  refine ⟨fun y hy => ⟨0, fun _ => y, fun _ _ => hy, by simp⟩, ?_, ?_⟩
  · rintro _ ⟨k, ys, hys, rfl⟩ _ ⟨k', ys', hys', rfl⟩
    refine ⟨k + k' + 1, fun i => if i < k + 1 then ys i else ys' (i - (k + 1)), fun i hi => ?_, ?_⟩
    · dsimp only
      split_ifs with h
      · exact hys i (by omega)
      · exact hys' _ (by omega)
    · have e : k + k' + 1 + 1 = (k + 1) + (k' + 1) := by omega
      rw [e, Finset.sum_range_add (fun i => if i < k + 1 then ys i else ys' (i - (k + 1)))
        (k + 1) (k' + 1)]
      congr 1
      · exact Finset.sum_congr rfl fun i hi => by
          simp [Finset.mem_range.mp hi]
      · exact Finset.sum_congr rfl fun i _ => by
          simp only [show ¬ (k + 1 + i < k + 1) by omega, ↓reduceIte, Nat.add_sub_cancel_left]
  · intro Z hYZ hadd
    rintro _ ⟨k, ys, hys, rfl⟩
    induction k with
    | zero => simpa using hYZ (hys 0 le_rfl)
    | succ k ih =>
      rw [Finset.sum_range_succ]
      exact hadd _ (ih fun i hi => hys i (by omega)) _ (hYZ (hys _ le_rfl))

/-- The decreasing-returns technology of Figure 5.B.5(a): `{y : y₁ ≤ 0, y₂ ≤ √(-y₁)}`. -/
def sqrtTech : Set (Fin 2 → ℝ) := {y | y 0 ≤ 0 ∧ y 1 ≤ Real.sqrt (-y 0)}

/-- **Exercise 5.B.4** (MWG, p. 160). For the decreasing-returns technology `{y₁ ≤ 0,
y₂ ≤ √(-y₁)}` (closed, with free disposal), the additive closure violates closedness:
`(-ε, 1) ∈ Y⁺` for every `ε > 0`, but `(0, 1) ∉ Y⁺`. -/
theorem exercise_5_B_4_not_closed :
    IsClosed sqrtTech ∧ FreeDisposal sqrtTech ∧
      (∀ ε : ℝ, 0 < ε → (![-ε, 1] : Fin 2 → ℝ) ∈ addClosure sqrtTech) ∧
      (![0, 1] : Fin 2 → ℝ) ∉ addClosure sqrtTech ∧ ¬ IsClosed (addClosure sqrtTech) := by
  have hmem : ∀ ε : ℝ, 0 < ε → (![-ε, 1] : Fin 2 → ℝ) ∈ addClosure sqrtTech := by
    intro ε hε
    obtain ⟨k, hk⟩ := exists_nat_gt (1 / ε)
    set m : ℝ := k + 1 with hm
    have hm0 : 0 < m := by positivity
    set r := Real.sqrt (ε / m) with hr
    have hr0 : 0 ≤ r := Real.sqrt_nonneg _
    have hrr : r ^ 2 = ε / m := Real.sq_sqrt (by positivity)
    have hkε : 1 < m * ε := by
      have h1 : 1 < (k : ℝ) * ε := by rwa [div_lt_iff₀ hε] at hk
      rw [hm]
      nlinarith
    have hmr : 1 ≤ m * r := by
      have h1 : (m * r) ^ 2 = m * ε := by rw [mul_pow, hrr]; field_simp
      have h2 : 0 ≤ m * r := by positivity
      nlinarith
    have hneg : -(-ε / m) = ε / m := by ring
    have hε0 : -ε / m ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hm0.le
    refine ⟨k, fun i => if i = 0 then ![-ε / m, 1 - k * r] else ![-ε / m, r],
      fun i _ => ?_, ?_⟩
    · dsimp only
      split_ifs with hi
      · refine ⟨hε0, ?_⟩
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hneg]
        rw [← hr]
        nlinarith
      · exact ⟨hε0, by simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hneg, hr, le_refl]⟩
    · funext l
      rw [Finset.sum_apply, Finset.sum_range_succ']
      simp only [Nat.add_one_ne_zero, ↓reduceIte, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul]
      fin_cases l
      · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
        rw [hm]
        field_simp
        ring
      · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
        ring
  have hnot : (![0, 1] : Fin 2 → ℝ) ∉ addClosure sqrtTech := by
    rintro ⟨k, ys, hys, hsum⟩
    have h0 := congrFun hsum 0
    have h1 := congrFun hsum 1
    simp only [Finset.sum_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    have hle : ∀ j ∈ Finset.range (k + 1), ys j 0 ≤ 0 := fun j hj =>
      (hys j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))).1
    have hall : ∀ i ∈ Finset.range (k + 1), ys i 0 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonpos hle).mp h0.symm
    have hle1 : ∀ i ∈ Finset.range (k + 1), ys i 1 ≤ 0 := fun i hi => by
      have := (hys i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))).2
      rw [hall i hi, neg_zero, Real.sqrt_zero] at this
      exact this
    have := Finset.sum_nonpos hle1
    linarith
  refine ⟨?_, ?_, hmem, hnot, fun hcl => hnot ?_⟩
  · exact (isClosed_le (continuous_apply 0) continuous_const).inter
      (isClosed_le (continuous_apply 1) ((continuous_apply 0).neg.sqrt))
  · rintro y ⟨h0, h1⟩ y' hy'
    have a0 : y' 0 ≤ y 0 := hy' 0
    have a1 : y' 1 ≤ y 1 := hy' 1
    exact ⟨by linarith, a1.trans (h1.trans (Real.sqrt_le_sqrt (by linarith)))⟩
  · have hlim : Tendsto (fun n : ℕ => (![-(1 / (n + 1 : ℝ)), 1] : Fin 2 → ℝ)) atTop
        (𝓝 ![0, 1]) := by
      rw [tendsto_pi_nhds]
      intro l
      fin_cases l
      · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
        have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).neg
        rw [neg_zero] at this
        exact this
      · simp
    exact hcl.mem_of_tendsto hlim (Eventually.of_forall fun n => hmem _ (by positivity))

/-- **Exercise 5.B.5** (MWG, p. 160). If `Y` is closed and convex and `-ℝ^L_+ ⊆ Y`, then `Y` has
free disposal. -/
theorem exercise_5_B_5 {Y : Set (Fin L → ℝ)} (hcl : IsClosed Y) (hc : Convex ℝ Y)
    (hneg : ∀ v : Fin L → ℝ, 0 ≤ v → -v ∈ Y) : FreeDisposal Y := by
  intro y hy y' hy'
  set v := y - y' with hv
  have hv0 : 0 ≤ v := sub_nonneg.mpr hy'
  -- `(1 - t)y + t(-v/t) = (1 - t)y - v ∈ Y`, and `→ y - v = y'` as `t → 0⁺`
  have hmem : ∀ t : ℝ, 0 < t → t < 1 → (1 - t) • y - v ∈ Y := by
    intro t ht0 ht1
    have := hc hy (hneg (t⁻¹ • v) (smul_nonneg (inv_nonneg.mpr ht0.le) hv0))
      (by linarith : (0 : ℝ) ≤ 1 - t) ht0.le (by ring)
    rwa [smul_neg, smul_smul, mul_inv_cancel₀ ht0.ne', one_smul, ← sub_eq_add_neg] at this
  have hlim : Tendsto (fun t : ℝ => (1 - t) • y - v) (𝓝[>] 0) (𝓝 y') := by
    have hcont : Continuous fun t : ℝ => (1 - t) • y - v := by fun_prop
    have := hcont.tendsto 0
    simp only [sub_zero, one_smul] at this
    rw [hv, sub_sub_cancel] at this
    exact this.mono_left nhdsWithin_le_nhds
  apply hcl.mem_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (eventually_lt_nhds one_pos)]
    with t ht ht1
  exact hmem t ht ht1

/-! ### Exercise 5.B.6 -/

/-- **Exercise 5.B.6(a)** (MWG, p. 161). The three-good production set of two techniques with
minimal input requirements `φ₁(q₁)` (input 1 only) and `φ₂(q₂)` (input 2 only), with free
disposal: `(-z₁, -z₂, q)` with `q ≤ q₁ + q₂`, `φ₁(q₁) ≤ z₁`, `φ₂(q₂) ≤ z₂`, `q₁, q₂ ≥ 0`. -/
def twoTechSet (φ₁ φ₂ : ℝ → ℝ) : Set (Fin 3 → ℝ) :=
  {y | ∃ q₁ q₂ : ℝ, 0 ≤ q₁ ∧ 0 ≤ q₂ ∧ y 2 ≤ q₁ + q₂ ∧ φ₁ q₁ ≤ -y 0 ∧ φ₂ q₂ ≤ -y 1}

/-- **Exercise 5.B.6(b)** (MWG, p. 161). If `φ₁` and `φ₂` are subadditive
(`φ(a + b) ≤ φ(a) + φ(b)`, e.g. concave with `φ(0) = 0`, or linear), the production set is
additive. -/
theorem exercise_5_B_6b {φ₁ φ₂ : ℝ → ℝ}
    (h₁ : ∀ a b, 0 ≤ a → 0 ≤ b → φ₁ (a + b) ≤ φ₁ a + φ₁ b)
    (h₂ : ∀ a b, 0 ≤ a → 0 ≤ b → φ₂ (a + b) ≤ φ₂ a + φ₂ b) : Additive (twoTechSet φ₁ φ₂) := by
  rintro y ⟨q₁, q₂, hq₁, hq₂, hy2, hy0, hy1⟩ y' ⟨q₁', q₂', hq₁', hq₂', hy2', hy0', hy1'⟩
  refine ⟨q₁ + q₁', q₂ + q₂', by positivity, by positivity, ?_, ?_, ?_⟩ <;>
    simp only [Pi.add_apply]
  · linarith
  · linarith [h₁ q₁ q₁' hq₁ hq₁']
  · linarith [h₂ q₂ q₂' hq₂ hq₂']

/-- **Exercise 5.B.6(c)** (MWG, p. 161). With output price `p` and input prices `w₁, w₂`, profit
maximization separates by technique: if `q_i* ≥ 0` maximizes `pq_i - w_iφ_i(q_i)` and `φ_i` is
differentiable there, then `p ≤ w_iφ_i'(q_i*)` with equality if `q_i* > 0` (marginal cost of each
technique equals the price); these conditions are sufficient when `φ_i` is convex. -/
theorem exercise_5_B_6c {φ : ℝ → ℝ} {w p q d : ℝ} (hq : 0 ≤ q) (hd : HasDerivAt φ d q) :
    ((∀ q', 0 ≤ q' → p * q' - w * φ q' ≤ p * q - w * φ q) → p - w * d ≤ 0 ∧ (0 < q → p = w * d))
      ∧ (0 ≤ w → ConvexOn ℝ (Set.Ici 0) φ → p - w * d ≤ 0 → (0 < q → p = w * d) →
        ∀ q', 0 ≤ q' → p * q' - w * φ q' ≤ p * q - w * φ q) := by
  have hd' : HasDerivAt (fun x => w * φ x) (w * d) q := hd.const_mul w
  exact ⟨fun hopt => foc_5_C_6 hq hopt hd', fun hw hc hle heq =>
    foc_5_C_6_sufficient (hc.smul hw) hq hd' hle heq⟩

/-- **Exercise 5.B.6(d)** (MWG, p. 161). If `φ₁` and `φ₂` are strictly concave on `[0, ∞)` and
`w₁, w₂ > 0`, a cost-minimizing way to produce `q > 0` never uses both techniques: the cost
`g(q₁) = w₁φ₁(q₁) + w₂φ₂(q - q₁)` of any split with `0 < q₁ < q` exceeds that of producing with
one technique only. -/
theorem exercise_5_B_6d_aux {φ₁ φ₂ : ℝ → ℝ} (h₁ : StrictConcaveOn ℝ (Set.Ici 0) φ₁)
    (h₂ : StrictConcaveOn ℝ (Set.Ici 0) φ₂) {w₁ w₂ q q₁ : ℝ} (hw₁ : 0 < w₁) (hw₂ : 0 < w₂)
    (hq₁ : 0 < q₁) (hq₁q : q₁ < q) :
    min (w₁ * φ₁ 0 + w₂ * φ₂ q) (w₁ * φ₁ q + w₂ * φ₂ 0) < w₁ * φ₁ q₁ + w₂ * φ₂ (q - q₁) := by
  have hq : 0 < q := by linarith
  set t := q₁ / q with ht
  have ht0 : 0 < t := div_pos hq₁ hq
  have ht1 : t < 1 := by rw [div_lt_one hq]; exact hq₁q
  have e1 : q₁ = (1 - t) * 0 + t * q := by rw [ht]; field_simp; ring
  have e2 : q - q₁ = (1 - t) * q + t * 0 := by rw [ht]; field_simp; ring
  have a1 := h₁.2 (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hq.le) (ne_of_lt hq)
    (by linarith : 0 < 1 - t) ht0 (by ring)
  have a2 := h₂.2 (Set.mem_Ici.mpr hq.le) (Set.mem_Ici.mpr le_rfl) (ne_of_gt hq)
    (by linarith : 0 < 1 - t) ht0 (by ring)
  simp only [smul_eq_mul] at a1 a2
  rw [← e1] at a1
  rw [← e2] at a2
  have hcomb : (1 - t) * (w₁ * φ₁ 0 + w₂ * φ₂ q) + t * (w₁ * φ₁ q + w₂ * φ₂ 0) <
      w₁ * φ₁ q₁ + w₂ * φ₂ (q - q₁) := by nlinarith
  rcases le_total (w₁ * φ₁ 0 + w₂ * φ₂ q) (w₁ * φ₁ q + w₂ * φ₂ 0) with h | h
  · rw [min_eq_left h]; nlinarith
  · rw [min_eq_right h]; nlinarith

/-- **Exercise 5.B.6(d)** (MWG, p. 161), as stated: a cost-minimizing split `(q₁, q - q₁)` of `q`
between strictly concave techniques uses only one of them (`q₁ = 0` or `q₁ = q`). -/
theorem exercise_5_B_6d {φ₁ φ₂ : ℝ → ℝ} (h₁ : StrictConcaveOn ℝ (Set.Ici 0) φ₁)
    (h₂ : StrictConcaveOn ℝ (Set.Ici 0) φ₂) {w₁ w₂ q q₁ : ℝ} (hw₁ : 0 < w₁) (hw₂ : 0 < w₂)
    (hq₁ : 0 ≤ q₁) (hq₁q : q₁ ≤ q)
    (hmin : ∀ q₁', 0 ≤ q₁' → q₁' ≤ q →
      w₁ * φ₁ q₁ + w₂ * φ₂ (q - q₁) ≤ w₁ * φ₁ q₁' + w₂ * φ₂ (q - q₁')) :
    q₁ = 0 ∨ q₁ = q := by
  by_contra h
  push Not at h
  have hlt := exercise_5_B_6d_aux h₁ h₂ hw₁ hw₂ (lt_of_le_of_ne hq₁ (Ne.symm h.1))
    (lt_of_le_of_ne hq₁q h.2)
  have m1 := hmin 0 le_rfl (by linarith)
  have m2 := hmin q (by linarith) le_rfl
  simp only [sub_zero, sub_self] at m1 m2
  rcases le_total (w₁ * φ₁ 0 + w₂ * φ₂ q) (w₁ * φ₁ q + w₂ * φ₂ 0) with hh | hh
  · rw [min_eq_left hh] at hlt; linarith
  · rw [min_eq_right hh] at hlt; linarith

end MWG.Production
