/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGClassicalDemand.UMPExamples
import MWGClassicalDemand.ExpBasic
import ConsumerDemand.CobbDouglasDemand

/-!
# The linear expenditure system: Exercises 3.D.6 and 3.G.3(a)

MWG, Exercise 3.D.6, p. 98 and Exercise 3.G.3(a), p. 99: the Stone-Geary utility
`u(x) = (x₁ - b₁)^α (x₂ - b₂)^β (x₃ - b₃)^γ`. It is formalized for any number `L ≥ 1` of goods
(the book's case is `L = 3`) as `u(x) = ∏_l (max (x_l - b_l) 0)^{a_l}` with `a_l > 0` and
`b ≥ 0`: on `{x ≥ b}` this is the book's formula, and it is `0` (the lowest utility) where some
`x_l ≤ b_l`, which keeps `u` continuous on `ℝ^L_+` (correction E2).

* **(3.D.6(a))** Exponents may be normalized to sum to one: `u^{1/∑a}` has exponents
  `a_l/∑a` and the same demand (`exercise_3_D_6a`).
* **(3.D.6(b))** With `∑ a = 1`, `p ≫ 0` and `w > p·b`: `x_l(p, w) = b_l + a_l (w - p·b)/p_l`
  and `v(p, w) = (w - p·b) ∏ (a_l/p_l)^{a_l}` (`exercise_3_D_6b_demand`,
  `exercise_3_D_6b_indirect`); the proof reduces to Cobb-Douglas demand for `y = x - b` with
  wealth `w - p·b` (Kreps `cobbDouglas_demand`).
* **(3.D.6(c))** The properties of Propositions 3.D.2 and 3.D.3 on `{w > p·b}`.
* **(3.G.3(a))** `e(p, ū) = p·b + ū ∏ (p_l/a_l)^{a_l}` and
  `h_l(p, ū) = b_l + a_l ū ∏ (p/a)^a / p_l` for `ū > 0`, with the properties of Propositions
  3.E.2 and 3.E.3.
-/

namespace MWG.ClassicalDemand

open Filter Topology MWG.ConsumerChoice Kreps.PreferenceProperties

/-- **Exercise 3.D.6** (MWG, p. 98). The Stone-Geary (linear expenditure system) utility
`∏_l (x_l - b_l)^{a_l}`, written with `max (x_l - b_l) 0` so that it is `0` off `{x ≫ b}`. -/
noncomputable def lesUtility {L : ℕ} (a b : Fin L → ℝ) (x : Fin L → ℝ) : ℝ :=
  ∏ l, (max (x l - b l) 0) ^ a l

/-- **Exercise 3.D.6(b)** (MWG, p. 98). The linear expenditure system
`x_l(p, w) = b_l + a_l (w - p·b)/p_l`. -/
noncomputable def lesDemand {L : ℕ} (a b p : Fin L → ℝ) (w : ℝ) : Fin L → ℝ :=
  fun l => b l + a l * (w - p ⬝ᵥ b) / p l

/-- **Exercise 3.D.6(b)** (MWG, p. 98). The indirect utility `(w - p·b) ∏ (a_l/p_l)^{a_l}`. -/
noncomputable def lesIndirect {L : ℕ} (a b p : Fin L → ℝ) (w : ℝ) : ℝ :=
  (w - p ⬝ᵥ b) * ∏ l, (a l / p l) ^ a l

/-- The Stone-Geary utility is nonnegative. -/
theorem lesUtility_nonneg {L : ℕ} (a b x : Fin L → ℝ) : 0 ≤ lesUtility a b x :=
  Finset.prod_nonneg fun _ _ => Real.rpow_nonneg (le_max_right _ _) _

/-- If `u(x) > 0` (with `a > 0`), then `x ≫ b`. -/
theorem les_gt_of_pos {L : ℕ} {a b x : Fin L → ℝ} (ha : ∀ l, 0 < a l)
    (hu : 0 < lesUtility a b x) (l : Fin L) : b l < x l := by
  by_contra h
  push Not at h
  have : lesUtility a b x = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ l)
    rw [max_eq_right (by linarith), Real.zero_rpow (ha l).ne']
  linarith

/-- The Stone-Geary utility is continuous. -/
theorem lesUtility_continuous {L : ℕ} {a : Fin L → ℝ} (ha : ∀ l, 0 < a l) (b : Fin L → ℝ) :
    Continuous (lesUtility a b) := by
  unfold lesUtility
  refine continuous_finsetProd _ fun l _ => ?_
  exact (Real.continuous_rpow_const (ha l).le).comp
    ((((continuous_apply l).sub continuous_const)).max continuous_const)

/-- **Exercise 3.D.6(a)** (MWG, p. 98). Normalizing the exponents to `a_l / ∑ a` is the
increasing transformation `t ↦ t^{1/∑a}` of utility, so it leaves demand unchanged: one may
assume `α + β + γ = 1`. -/
theorem exercise_3_D_6a {L : ℕ} {a : Fin L → ℝ} (ha : ∀ l, 0 < a l) (hL : 0 < L)
    (b p : Fin L → ℝ) (w : ℝ) :
    (∀ x, lesUtility (fun l => a l / ∑ k, a k) b x = lesUtility a b x ^ (1 / ∑ k, a k)) ∧
      walrasianDemand (lesUtility (fun l => a l / ∑ k, a k) b) p w =
        walrasianDemand (lesUtility a b) p w := by
  have hs : 0 < ∑ k, a k :=
    Finset.sum_pos (fun l _ => ha l) ⟨⟨0, hL⟩, Finset.mem_univ _⟩
  have hpow : ∀ x, lesUtility (fun l => a l / ∑ k, a k) b x =
      lesUtility a b x ^ (1 / ∑ k, a k) := by
    intro x
    unfold lesUtility
    rw [← Real.finsetProd_rpow _ _ fun l _ => Real.rpow_nonneg (le_max_right _ _) _]
    refine Finset.prod_congr rfl fun l _ => ?_
    rw [← Real.rpow_mul (le_max_right _ _)]
    ring_nf
  refine ⟨hpow, ?_⟩
  ext x
  simp only [mem_walrasianDemand_iff, hpow]
  constructor
  · rintro ⟨hx, h⟩
    refine ⟨hx, fun y hy => ?_⟩
    have := h y hy
    exact (Real.rpow_le_rpow_iff (lesUtility_nonneg _ _ _) (lesUtility_nonneg _ _ _)
      (one_div_pos.2 hs)).1 this
  · rintro ⟨hx, h⟩
    exact ⟨hx, fun y hy => Real.rpow_le_rpow (lesUtility_nonneg _ _ _) (h y hy)
      (one_div_pos.2 hs).le⟩


/-- On `{x ≥ b}` the Stone-Geary utility is Cobb-Douglas utility of `x - b`. -/
theorem lesUtility_eq_cobbDouglas {L : ℕ} (a b : Fin L → ℝ) {x : Fin L → ℝ}
    (hy : 0 ≤ fun l => x l - b l) :
    lesUtility a b x = Kreps.ConsumerDemand.CobbDouglas a ⟨fun l => x l - b l, hy⟩ := by
  unfold lesUtility Kreps.ConsumerDemand.CobbDouglas Kreps.ConsumerDemand.ShiftedCobbDouglas
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [max_eq_left (show 0 ≤ x l - b l from hy l)]
  simp

/-- `∏ (c z_l)^{a_l} = c ∏ z_l^{a_l}` when `∑ a = 1`, `c > 0`, `z ≥ 0`. -/
theorem les_prod_scale {L : ℕ} {a : Fin L → ℝ} (hsum : ∑ l, a l = 1) {c : ℝ} (hc : 0 < c)
    {z : Fin L → ℝ} (hz : ∀ l, 0 ≤ z l) :
    ∏ l, (c * z l) ^ a l = c * ∏ l, z l ^ a l := by
  rw [Finset.prod_congr rfl fun l _ => Real.mul_rpow hc.le (hz l), Finset.prod_mul_distrib,
    ← Real.rpow_sum_of_pos hc, hsum, Real.rpow_one]

/-- Walras' law for the linear expenditure system: `p·x(p, w) = w` when `∑ a = 1`. -/
theorem lesDemand_walras {L : ℕ} {a b : Fin L → ℝ} (hsum : ∑ l, a l = 1) {p : Fin L → ℝ}
    (hp : StrictlyPositive p) (w : ℝ) : p ⬝ᵥ lesDemand a b p w = w := by
  have key : ∀ l, p l * lesDemand a b p w l = p l * b l + a l * (w - p ⬝ᵥ b) := by
    intro l
    simp only [lesDemand]
    field_simp [(hp l).ne']
  calc p ⬝ᵥ lesDemand a b p w = ∑ l, p l * lesDemand a b p w l := rfl
    _ = ∑ l, (p l * b l + a l * (w - p ⬝ᵥ b)) := Finset.sum_congr rfl fun l _ => key l
    _ = p ⬝ᵥ b + (∑ l, a l) * (w - p ⬝ᵥ b) := by
      rw [Finset.sum_add_distrib, Finset.sum_mul]; rfl
    _ = w := by rw [hsum]; ring

/-- **Exercise 3.D.6(b)** (MWG, p. 98). With `a_l > 0`, `∑ a = 1`, `b ≥ 0`, `p ≫ 0` and
`w > p·b`, the UMP has the unique solution `x_l(p, w) = b_l + a_l (w - p·b)/p_l` (the linear
expenditure system). -/
theorem exercise_3_D_6b_demand {L : ℕ} [NeZero L] {a b : Fin L → ℝ} (ha : ∀ l, 0 < a l)
    (hsum : ∑ l, a l = 1) (hb : b ∈ nonnegOrthant L) {p : Fin L → ℝ}
    (hp : StrictlyPositive p) {w : ℝ} (hw : p ⬝ᵥ b < w) :
    walrasianDemand (lesUtility a b) p w = {lesDemand a b p w} := by
  set w' := w - p ⬝ᵥ b with hw'
  have hw'0 : 0 < w' := sub_pos.2 hw
  set P : Kreps.ConsumerDemand.PositivePrices L := ⟨p, hp⟩ with hP
  set Y : NNReal := w'.toNNReal with hYdef
  have hY : (Y : ℝ) = w' := Real.coe_toNNReal _ hw'0.le
  set ystar := Kreps.ConsumerDemand.CobbDouglasBundle a ha P Y with hys
  have hystar : ∀ l, ystar.val l = a l * w' / p l := by
    intro l
    simp only [hys, Kreps.ConsumerDemand.CobbDouglasBundle, hsum, hY, hP]
    ring
  have hmem : ystar ∈ Kreps.ConsumerDemand.MarshallianDemand
      (Kreps.ConsumerDemand.CobbDouglas a) P Y := by
    rw [Kreps.ConsumerDemand.cobbDouglas_demand a ha P Y]; rfl
  set xs := lesDemand a b p w with hxs
  have hxsy : (fun l => xs l - b l) = ystar.val := by
    funext l
    rw [hystar l, hxs, lesDemand]
    ring
  have hys0 : 0 ≤ fun l => xs l - b l := by rw [hxsy]; exact ystar.2
  have hux : lesUtility a b xs = Kreps.ConsumerDemand.CobbDouglas a ystar := by
    rw [lesUtility_eq_cobbDouglas a b hys0]
    congr 1
    exact Subtype.ext hxsy
  have hupos : 0 < lesUtility a b xs := by
    unfold lesUtility
    refine Finset.prod_pos fun l _ => Real.rpow_pos_of_pos ?_ _
    rw [max_eq_left (show 0 ≤ xs l - b l from hys0 l)]
    have := congrFun hxsy l
    rw [this, hystar l]
    exact div_pos (mul_pos (ha l) hw'0) (hp l)
  have hxsB : xs ∈ budgetSet p w := by
    refine ⟨fun l => ?_, ?_⟩
    · simp only [hxs, lesDemand]
      exact add_nonneg (hb l) (div_nonneg (mul_nonneg (ha l).le hw'0.le) (hp l).le)
    · rw [hxs, lesDemand_walras hsum hp]
  have hbound : ∀ y ∈ budgetSet p w, lesUtility a b y ≤ lesUtility a b xs ∧
      (lesUtility a b y = lesUtility a b xs → y = xs) := by
    intro y hy
    by_cases hge : ∀ l, b l ≤ y l
    · have hz0 : 0 ≤ fun l => y l - b l := fun l => sub_nonneg.2 (hge l)
      set z : Kreps.ConsumerDemand.NonnegativeOrthant L := ⟨fun l => y l - b l, hz0⟩ with hz
      have hzB : z ∈ Kreps.ConsumerDemand.BudgetSet P Y := by
        change ∑ l, p l * (y l - b l) ≤ (Y : ℝ)
        rw [hY]
        have : ∑ l, p l * (y l - b l) = p ⬝ᵥ y - p ⬝ᵥ b := by
          simp [dotProduct, mul_sub, Finset.sum_sub_distrib]
        rw [this]
        linarith [hy.2]
      have hle : Kreps.ConsumerDemand.CobbDouglas a z ≤
          Kreps.ConsumerDemand.CobbDouglas a ystar := hmem.2 z hzB
      rw [lesUtility_eq_cobbDouglas a b hz0, hux]
      refine ⟨hle, fun heq => ?_⟩
      have hzmem : z ∈ Kreps.ConsumerDemand.MarshallianDemand
          (Kreps.ConsumerDemand.CobbDouglas a) P Y := by
        refine ⟨hzB, fun z' hz' => ?_⟩
        change Kreps.ConsumerDemand.CobbDouglas a z' ≤ Kreps.ConsumerDemand.CobbDouglas a z
        rw [heq]
        exact hmem.2 z' hz'
      rw [Kreps.ConsumerDemand.cobbDouglas_demand a ha P Y] at hzmem
      have hzy : z.val = ystar.val := congrArg Subtype.val hzmem
      funext l
      have h1 := congrFun hzy l
      have h2 := congrFun hxsy l
      simp only [hz] at h1 h2
      linarith
    · push Not at hge
      obtain ⟨l, hl⟩ := hge
      have h0 : lesUtility a b y = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ l)
        rw [max_eq_right (by linarith), Real.zero_rpow (ha l).ne']
      rw [h0]
      exact ⟨hupos.le, fun h => absurd h.symm hupos.ne'⟩
  ext y
  rw [mem_walrasianDemand_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hy, hmax⟩
    exact (hbound y hy).2 (le_antisymm (hbound y hy).1 (hmax xs hxsB))
  · rintro rfl
    exact ⟨hxsB, fun y hy => (hbound y hy).1⟩

/-- `u(x(p, w)) = (w - p·b) ∏ (a_l/p_l)^{a_l}`. -/
theorem lesUtility_lesDemand {L : ℕ} {a b : Fin L → ℝ} (ha : ∀ l, 0 < a l)
    (hsum : ∑ l, a l = 1) {p : Fin L → ℝ} (hp : StrictlyPositive p) {w : ℝ}
    (hw : p ⬝ᵥ b < w) : lesUtility a b (lesDemand a b p w) = lesIndirect a b p w := by
  have hw'0 : 0 < w - p ⬝ᵥ b := sub_pos.2 hw
  unfold lesUtility lesIndirect
  rw [← les_prod_scale hsum hw'0 fun l => (div_pos (ha l) (hp l)).le]
  refine Finset.prod_congr rfl fun l _ => ?_
  have : lesDemand a b p w l - b l = (w - p ⬝ᵥ b) * (a l / p l) := by
    simp only [lesDemand]; ring
  rw [this, max_eq_left (mul_nonneg hw'0.le (div_pos (ha l) (hp l)).le)]

/-- **Exercise 3.D.6(b)** (MWG, p. 98). The indirect utility of the linear expenditure system,
`v(p, w) = (w - p·b) ∏ (a_l/p_l)^{a_l}` for `w > p·b`. -/
theorem exercise_3_D_6b_indirect {L : ℕ} [NeZero L] {a b : Fin L → ℝ} (ha : ∀ l, 0 < a l)
    (hsum : ∑ l, a l = 1) (hb : b ∈ nonnegOrthant L) {p : Fin L → ℝ}
    (hp : StrictlyPositive p) {w : ℝ} (hw : p ⬝ᵥ b < w) :
    indirectUtility (lesUtility a b) p w = lesIndirect a b p w := by
  have hx : lesDemand a b p w ∈ walrasianDemand (lesUtility a b) p w := by
    rw [exercise_3_D_6b_demand ha hsum hb hp hw]; rfl
  rw [indirectUtility_eq_of_mem hx, lesUtility_lesDemand ha hsum hp hw]

/-- `(αp)·b < αw` and `α • p ≫ 0` for `α > 0`. -/
theorem les_smul_domain {L : ℕ} {b p : Fin L → ℝ} (hp : StrictlyPositive p) {w : ℝ}
    (hw : p ⬝ᵥ b < w) {α : ℝ} (hα : 0 < α) :
    StrictlyPositive (α • p) ∧ (α • p) ⬝ᵥ b < α * w := by
  refine ⟨fun l => by simpa using mul_pos hα (hp l), ?_⟩
  rw [smul_dotProduct, smul_eq_mul]
  exact mul_lt_mul_of_pos_left hw hα

/-- **Exercise 3.D.6(c)** (MWG, p. 98), Proposition 3.D.2: the linear expenditure system is
homogeneous of degree zero, satisfies Walras' law, and is single-valued
(`exercise_3_D_6b_demand`). -/
theorem exercise_3_D_6c_demand {L : ℕ} [NeZero L] {a b : Fin L → ℝ} (ha : ∀ l, 0 < a l)
    (hsum : ∑ l, a l = 1) (hb : b ∈ nonnegOrthant L) {p : Fin L → ℝ}
    (hp : StrictlyPositive p) {w : ℝ} (hw : p ⬝ᵥ b < w) {α : ℝ} (hα : 0 < α) :
    lesDemand a b (α • p) (α * w) = lesDemand a b p w ∧ p ⬝ᵥ lesDemand a b p w = w := by
  obtain ⟨hp', hw'⟩ := les_smul_domain hp hw hα
  refine ⟨?_, ?_⟩
  · have h := proposition_3_D_2_i (lesUtility a b) p w hα
    rw [exercise_3_D_6b_demand ha hsum hb hp' hw', exercise_3_D_6b_demand ha hsum hb hp hw] at h
    exact Set.singleton_eq_singleton_iff.1 h
  · exact lesDemand_walras hsum hp w

/-- The domain `{(p, w) : p ≫ 0, w > p·b}` of the linear expenditure system. -/
def lesDomain {L : ℕ} (b : Fin L → ℝ) : Set ((Fin L → ℝ) × ℝ) :=
  {q | StrictlyPositive q.1 ∧ q.1 ⬝ᵥ b < q.2}

/-- The domain `{p ≫ 0, w > p·b}` is convex and, for `b ≥ 0`, inside the price-wealth domain. -/
theorem lesDomain_convex_subset {L : ℕ} {b : Fin L → ℝ} (hb : b ∈ nonnegOrthant L) :
    Convex ℝ (lesDomain b) ∧ lesDomain b ⊆ pwDomainSet L := by
  refine ⟨?_, fun q hq => ⟨hq.1, lt_of_le_of_lt
    (Finset.sum_nonneg fun l _ => mul_nonneg (hq.1 l).le (hb l)) hq.2⟩⟩
  intro q hq q' hq' s t hs ht hst
  refine ⟨fun l => ?_, ?_⟩
  · simp only [Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases hs.lt_or_eq with hs | rfl
    · exact add_pos_of_pos_of_nonneg (mul_pos hs (hq.1 l)) (mul_nonneg ht (hq'.1 l).le)
    · rw [zero_add] at hst
      subst hst
      simpa using hq'.1 l
  · simp only [Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, add_dotProduct,
      smul_dotProduct, smul_eq_mul]
    rcases hs.lt_or_eq with hs | rfl
    · nlinarith [mul_lt_mul_of_pos_left hq.2 hs, mul_le_mul_of_nonneg_left hq'.2.le ht]
    · rw [zero_add] at hst
      subst hst
      simpa using hq'.2

/-- **Exercise 3.D.6(c)** (MWG, p. 98), Proposition 3.D.3: on `{p ≫ 0, w > p·b}` the indirect
utility is homogeneous of degree zero, strictly increasing in `w`, nonincreasing in `p`,
quasiconvex and continuous. -/
theorem exercise_3_D_6c_indirect {L : ℕ} [NeZero L] {a b : Fin L → ℝ} (ha : ∀ l, 0 < a l)
    (hsum : ∑ l, a l = 1) (hb : b ∈ nonnegOrthant L) :
    (∀ p w α, StrictlyPositive p → p ⬝ᵥ b < w → 0 < α →
        lesIndirect a b (α • p) (α * w) = lesIndirect a b p w) ∧
      (∀ p w w', StrictlyPositive p → w < w' → lesIndirect a b p w < lesIndirect a b p w') ∧
      (∀ p p' w, StrictlyPositive p → p ≤ p' → p' ⬝ᵥ b < w →
        lesIndirect a b p' w ≤ lesIndirect a b p w) ∧
      QuasiconvexOn ℝ (lesDomain b) (fun q => lesIndirect a b q.1 q.2) ∧
      ContinuousOn (fun q : (Fin L → ℝ) × ℝ => lesIndirect a b q.1 q.2) (lesDomain b) := by
  have hcont : ContinuousOn (lesUtility a b) (nonnegOrthant L) :=
    (lesUtility_continuous ha b).continuousOn
  obtain ⟨hconv, hsub⟩ := lesDomain_convex_subset hb
  have heq : ∀ q ∈ lesDomain b, indirectUtility (lesUtility a b) q.1 q.2 =
      lesIndirect a b q.1 q.2 := fun q hq => exercise_3_D_6b_indirect ha hsum hb hq.1 hq.2
  refine ⟨fun p w α hp hw hα => ?_, fun p w w' hp hww => ?_, fun p p' w hp hpp hw => ?_, ?_, ?_⟩
  · obtain ⟨hp', hw'⟩ := les_smul_domain hp hw hα
    rw [← exercise_3_D_6b_indirect ha hsum hb hp' hw', ← exercise_3_D_6b_indirect ha hsum hb hp hw]
    exact proposition_3_D_3_i _ p w hα
  · unfold lesIndirect
    exact mul_lt_mul_of_pos_right (by linarith)
      (Finset.prod_pos fun l _ => Real.rpow_pos_of_pos (div_pos (ha l) (hp l)) _)
  · have hp' : StrictlyPositive p' := fun l => lt_of_lt_of_le (hp l) (hpp l)
    have hwb : p ⬝ᵥ b < w := lt_of_le_of_lt (Finset.sum_le_sum fun l _ =>
      mul_le_mul_of_nonneg_right (hpp l) (hb l)) hw
    rw [← exercise_3_D_6b_indirect ha hsum hb hp hwb, ← exercise_3_D_6b_indirect ha hsum hb hp' hw]
    exact proposition_3_D_3_ii_prices hcont hp hp' hpp (le_of_lt (lt_of_le_of_lt
      (Finset.sum_nonneg fun l _ => mul_nonneg (hp' l).le (hb l)) hw))
  · intro t
    have h2 := hconv.inter (proposition_3_D_3_iii hcont t)
    convert h2 using 1
    ext q
    simp only [Set.mem_sep_iff, Set.mem_inter_iff]
    constructor
    · rintro ⟨hq, hle⟩
      exact ⟨hq, hsub hq, by rwa [heq q hq]⟩
    · rintro ⟨hq, -, hle⟩
      exact ⟨hq, by rwa [← heq q hq]⟩
  · exact ((proposition_3_D_3_iv hcont).mono hsub).congr fun q hq => (heq q hq).symm

/-- **Exercise 3.G.3(a)** (MWG, p. 99). The expenditure function of the linear expenditure
system, `e(p, ū) = p·b + ū ∏ (p_l/a_l)^{a_l}`. -/
noncomputable def lesExpenditure {L : ℕ} (a b p : Fin L → ℝ) (ub : ℝ) : ℝ :=
  p ⬝ᵥ b + ub * ∏ l, (p l / a l) ^ a l

/-- **Exercise 3.G.3(a)** (MWG, p. 99). The Hicksian demand `h(p, ū) = x(p, e(p, ū))`, i.e.
`h_l = b_l + a_l ū ∏ (p/a)^a / p_l`. -/
noncomputable def lesHicks {L : ℕ} (a b p : Fin L → ℝ) (ub : ℝ) : Fin L → ℝ :=
  lesDemand a b p (lesExpenditure a b p ub)

/-- `∏ (p/a)^a · ∏ (a/p)^a = 1`. -/
theorem les_prod_inv {L : ℕ} {a p : Fin L → ℝ} (ha : ∀ l, 0 < a l) (hp : StrictlyPositive p) :
    (∏ l, (p l / a l) ^ a l) * ∏ l, (a l / p l) ^ a l = 1 := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun l _ => ?_
  have h1 : p l / a l * (a l / p l) = 1 := by field_simp [(ha l).ne', (hp l).ne']
  rw [← Real.mul_rpow (div_pos (hp l) (ha l)).le (div_pos (ha l) (hp l)).le, h1,
    Real.one_rpow]

/-- **Exercise 3.G.3(a)** (MWG, p. 99). For `ū > 0` the Hicksian demand of the linear
expenditure system is the single bundle `lesHicks a b p ū`, and `e(p, ū) = p·b + ū ∏ (p/a)^a`.
-/
theorem exercise_3_G_3a {L : ℕ} [NeZero L] {a b : Fin L → ℝ} (ha : ∀ l, 0 < a l)
    (hsum : ∑ l, a l = 1) (hb : b ∈ nonnegOrthant L) {p : Fin L → ℝ}
    (hp : StrictlyPositive p) {ub : ℝ} (hub : 0 < ub) :
    hicksianDemand (lesUtility a b) p ub = {lesHicks a b p ub} ∧
      expenditure (lesUtility a b) p ub = lesExpenditure a b p ub := by
  set C := ∏ l, (a l / p l) ^ a l with hC
  have hC0 : 0 < C := Finset.prod_pos fun l _ => Real.rpow_pos_of_pos (div_pos (ha l) (hp l)) _
  set Q := ∏ l, (p l / a l) ^ a l with hQ
  have hQ0 : 0 < Q := Finset.prod_pos fun l _ => Real.rpow_pos_of_pos (div_pos (hp l) (ha l)) _
  have hQC : Q * C = 1 := les_prod_inv ha hp
  set W := lesExpenditure a b p ub with hW
  have hWb : p ⬝ᵥ b < W := by
    simp only [hW, lesExpenditure]
    linarith [mul_pos hub hQ0]
  have hdem := exercise_3_D_6b_demand ha hsum hb hp hWb
  have hvW : lesIndirect a b p W = ub := by
    simp only [lesIndirect, hW, lesExpenditure, add_sub_cancel_left]
    rw [← hC, mul_assoc, hQC, mul_one]
  have hxu : lesUtility a b (lesHicks a b p ub) = ub := by
    rw [lesHicks, lesUtility_lesDemand ha hsum hp hWb, hvW]
  have hxmem : lesHicks a b p ub ∈ walrasianDemand (lesUtility a b) p W := by
    rw [lesHicks, hdem]; rfl
  have hxp : p ⬝ᵥ lesHicks a b p ub = W := (exercise_3_D_6c_demand ha hsum hb hp hWb one_pos).2
  have hcheap : ∀ z ∈ nonnegOrthant L, ub ≤ lesUtility a b z → W ≤ p ⬝ᵥ z := by
    intro z hz hzu
    have hpos : 0 < lesUtility a b z := lt_of_lt_of_le hub hzu
    have hzb : p ⬝ᵥ b < p ⬝ᵥ z := by
      apply Finset.sum_lt_sum (fun l _ => mul_le_mul_of_nonneg_left
        (les_gt_of_pos ha hpos l).le (hp l).le)
      exact ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne L)⟩, Finset.mem_univ _,
        mul_lt_mul_of_pos_left (les_gt_of_pos ha hpos _) (hp _)⟩
    have hzx : lesDemand a b p (p ⬝ᵥ z) ∈ walrasianDemand (lesUtility a b) p (p ⬝ᵥ z) := by
      rw [exercise_3_D_6b_demand ha hsum hb hp hzb]; rfl
    have h1 := hzx.2 z ⟨hz, le_rfl⟩
    rw [lesUtility_lesDemand ha hsum hp hzb, lesIndirect] at h1
    have h2 : ub = (W - p ⬝ᵥ b) * C := by rw [← hvW, lesIndirect]
    have : (W - p ⬝ᵥ b) * C ≤ (p ⬝ᵥ z - p ⬝ᵥ b) * C := by rw [← h2]; exact hzu.trans h1
    have := le_of_mul_le_mul_right this hC0
    linarith
  have hh : hicksianDemand (lesUtility a b) p ub = {lesHicks a b p ub} := by
    ext y
    rw [mem_hicksianDemand_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨hy0, hyu⟩, hmin⟩
      have hle : p ⬝ᵥ y ≤ W := hxp ▸ hmin _ hxmem.1.1 hxu.ge
      have hy : y ∈ walrasianDemand (lesUtility a b) p W :=
        ⟨⟨hy0, hle⟩, fun z hz => (hxmem.2 z hz).trans (by rw [hxu]; exact hyu)⟩
      rw [hdem] at hy
      exact hy
    · rintro rfl
      exact ⟨⟨hxmem.1.1, hxu.ge⟩, fun z hz hzu => hxp ▸ hcheap z hz hzu⟩
  refine ⟨hh, ?_⟩
  have hx : lesHicks a b p ub ∈ hicksianDemand (lesUtility a b) p ub := by rw [hh]; rfl
  rw [expenditure_eq_of_mem hx, hxp]

/-- **Exercise 3.G.3(a)** (MWG, p. 99): the properties of Propositions 3.E.2 and 3.E.3 for the
linear expenditure system (`ū > 0`): `e` is homogeneous of degree one in `p`, strictly
increasing in `ū`, nondecreasing and concave in `p`; `h` is homogeneous of degree zero in `p`
and has no excess utility; `h` is single-valued (`exercise_3_G_3a`). -/
theorem exercise_3_G_3a_properties {L : ℕ} [NeZero L] {a b : Fin L → ℝ} (ha : ∀ l, 0 < a l)
    (hsum : ∑ l, a l = 1) (hb : b ∈ nonnegOrthant L) {ub : ℝ} (hub : 0 < ub) :
    (∀ p α, StrictlyPositive p → 0 < α →
        lesExpenditure a b (α • p) ub = α * lesExpenditure a b p ub) ∧
      (∀ p ub', StrictlyPositive p → ub < ub' →
        lesExpenditure a b p ub < lesExpenditure a b p ub') ∧
      (∀ p p', StrictlyPositive p → p ≤ p' →
        lesExpenditure a b p ub ≤ lesExpenditure a b p' ub) ∧
      ConcaveOn ℝ {p : Fin L → ℝ | StrictlyPositive p} (fun p => lesExpenditure a b p ub) ∧
      (∀ (p : Fin L → ℝ) (α : ℝ), StrictlyPositive p → 0 < α →
        lesHicks a b (α • p) ub = lesHicks a b p ub) ∧
      (∀ p, StrictlyPositive p → lesUtility a b (lesHicks a b p ub) = ub) := by
  have hE : ∀ p, StrictlyPositive p →
      expenditure (lesUtility a b) p ub = lesExpenditure a b p ub := fun p hp =>
    (exercise_3_G_3a ha hsum hb hp hub).2
  have hsp : ∀ (p : Fin L → ℝ) (α : ℝ), StrictlyPositive p → 0 < α →
      StrictlyPositive (α • p) := fun p α hp hα l =>
    by simpa using mul_pos hα (hp l)
  refine ⟨fun p α hp hα => ?_, fun p ub' hp hlt => ?_, fun p p' hp hpp => ?_,
    (proposition_3_E_2_iii (lesUtility a b) ub).congr fun p hp => hE p hp,
    fun p α hp hα => ?_, fun p hp => ?_⟩
  · rw [← hE _ (hsp p α hp hα), ← hE p hp]
    exact proposition_3_E_2_i _ p ub hα
  · simp only [lesExpenditure]
    have : 0 < ∏ l, (p l / a l) ^ a l :=
      Finset.prod_pos fun l _ => Real.rpow_pos_of_pos (div_pos (hp l) (ha l)) _
    nlinarith
  · have hp' : StrictlyPositive p' := fun l => lt_of_lt_of_le (hp l) (hpp l)
    rw [← hE p hp, ← hE p' hp']
    exact proposition_3_E_2_ii_prices _ hp hpp ub
  · have h := proposition_3_E_3_i (lesUtility a b) p ub hα
    rw [(exercise_3_G_3a ha hsum hb (hsp p α hp hα) hub).1,
      (exercise_3_G_3a ha hsum hb hp hub).1] at h
    exact Set.singleton_eq_singleton_iff.1 h
  · have hx : lesHicks a b p ub ∈ hicksianDemand (lesUtility a b) p ub := by
      rw [(exercise_3_G_3a ha hsum hb hp hub).1]; rfl
    exact proposition_3_E_3_ii (lesUtility_continuous ha b).continuousOn hp
      (by
        have : lesUtility a b 0 = 0 := by
          apply Finset.prod_eq_zero (Finset.mem_univ ⟨0, Nat.pos_of_ne_zero (NeZero.ne L)⟩)
          simp only [Pi.zero_apply, zero_sub]
          rw [max_eq_right (neg_nonpos.2 (hb _)), Real.zero_rpow (ha _).ne']
        rw [this]; exact hub.le) hx

end MWG.ClassicalDemand
