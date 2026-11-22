/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGSocialChoice.Euclidean
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Medians of symmetric distributions; intermediate preferences

MWG, Figure 21.D.8(a), p. 806, and Exercise 21.D.9 (Grandmont), pp. 813-814.

A distribution of peaks that is symmetric about `x` has `x` as a median; in particular the
centre of a rectangle is a median of the uniform distribution on it (Figure 21.D.8(a)).

Exercise 21.D.9: (a) a positive combination of two utilities represents preferences
intermediate between them; (b) for utilities `u_β = ∑ βₙ hₙ` linear in the parameter, the set
`B(x, y)` of parameters preferring `x` to `y` is `ℝ^N_{++}` intersected with an open half-space;
(c) **correction**: with merely intermediate preferences along segments of parameters the set
`{β : y ≿_β x}` is convex, but `B(x, y)` itself need not be the intersection of the parameter
set with a half-space (it need not even be convex): `exercise_21_D_9c_counterexample`;
(d) a median agent exists for a symmetric density (the uniform density on a rectangle); the
nonexistence half (the triangle of Figure 21.D.8(b)) is in `TriangleMedian`; (e) a median agent
`β*` whose neighbourhoods carry positive mass (MWG: `g(β*) > 0`; for a density this needs
continuity at `β*`, which we assume in the form of positive mass on open sets approaching `β*`)
makes its
unique best alternative a strict majority winner; (f) Euclidean preferences are of this form,
with alternatives and agents kept separate.
-/

namespace MWG.SocialChoice

open Kreps.ChoicePreferenceUtility MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E]

local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

/-- **Example 21.D.6** (MWG, p. 806). A measure invariant under the point reflection about `x`
has `x` as a median. -/
theorem isMedianPoint_of_symmetric (μ : Measure E) (x : E)
    (hsym : Measure.map (fun z => (x + x) - z) μ = μ) : IsMedianPoint μ x := by
  intro q _
  have hmeas : Measurable fun z : E => (x + x) - z :=
    (continuous_const.sub continuous_id).measurable
  have hpre : (fun z => (x + x) - z) ⁻¹' openHalfSpace x q = openHalfSpace x (-q) := by
    ext z
    simp only [openHalfSpace, Set.mem_preimage, Set.mem_ofPred_eq, inner_neg_right]
    have : x + x - z - x = -(z - x) := by abel
    rw [this, inner_neg_left]
  have h1 : μ (openHalfSpace x q) = μ (openHalfSpace x (-q)) := by
    conv_lhs => rw [← hsym]
    rw [Measure.map_apply hmeas (measurableSet_openHalfSpace x q), hpre]
  calc 2 * μ (openHalfSpace x q) = μ (openHalfSpace x q) + μ (openHalfSpace x (-q)) := by
        rw [two_mul, ← h1]
    _ = μ (openHalfSpace x q ∪ openHalfSpace x (-q)) :=
        (measure_union (disjoint_openHalfSpace x q) (measurableSet_openHalfSpace x (-q))).symm
    _ ≤ μ Set.univ := measure_mono (Set.subset_univ _)

/-- Point reflection preserves Lebesgue measure on a finite-dimensional inner product space. -/
theorem measurePreserving_reflect [FiniteDimensional ℝ E] (c : E) :
    MeasurePreserving (fun z : E => c - z) volume volume := by
  have h1 := (LinearIsometryEquiv.neg ℝ (E := E)).measurePreserving
  have h2 := measurePreserving_add_left (volume : Measure E) c
  convert h2.comp h1 using 1
  funext x
  simp [sub_eq_add_neg]

/-- The axis-parallel rectangle `[a₀, b₀] × [a₁, b₁]` in the plane. -/
def rectangle (a0 b0 a1 b1 : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {z | a0 ≤ z 0 ∧ z 0 ≤ b0 ∧ a1 ≤ z 1 ∧ z 1 ≤ b1}

/-- **Figure 21.D.8(a)** (MWG, p. 806). The centre of a rectangle is a median of the uniform
distribution on it (Lebesgue measure restricted to the rectangle). -/
theorem figure_21_D_8a (a0 b0 a1 b1 : ℝ) (c : EuclideanSpace ℝ (Fin 2))
    (hc0 : c 0 = (a0 + b0) / 2) (hc1 : c 1 = (a1 + b1) / 2) :
    IsMedianPoint (volume.restrict (rectangle a0 b0 a1 b1)) c := by
  apply isMedianPoint_of_symmetric
  have hR : MeasurableSet (rectangle a0 b0 a1 b1) := by
    unfold rectangle
    measurability
  have hpre : (fun z => (c + c) - z) ⁻¹' rectangle a0 b0 a1 b1 = rectangle a0 b0 a1 b1 := by
    ext z
    simp only [rectangle, Set.mem_preimage, Set.mem_ofPred_eq, PiLp.sub_apply, PiLp.add_apply,
      hc0, hc1]
    constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  have := (measurePreserving_reflect (c + c)).restrict_preimage hR
  rw [hpre] at this
  exact this.map_eq

/-- **Figure 21.D.8(a)**, non-vacuity: the centre exists. -/
theorem figure_21_D_8a_center (a0 b0 a1 b1 : ℝ) :
    ∃ c : EuclideanSpace ℝ (Fin 2), c 0 = (a0 + b0) / 2 ∧ c 1 = (a1 + b1) / 2 :=
  ⟨EuclideanSpace.single 0 ((a0 + b0) / 2) + EuclideanSpace.single 1 ((a1 + b1) / 2),
    by simp, by simp⟩

/-- **Exercise 21.D.9** (MWG, p. 813). `≿''` is intermediate between `≿` and `≿'`: `x ≿ y` and
`x ≿' y` imply `x ≿'' y`. -/
def Intermediate {X : Type*} (r r' r'' : X → X → Prop) : Prop :=
  ∀ x y, r x y → r' x y → r'' x y

/-- **Exercise 21.D.9(a)** (MWG, p. 813). For `ψ, γ > 0`, `ψu + γu'` represents preferences
intermediate between those represented by `u` and `u'`. -/
theorem exercise_21_D_9a {X : Type*} (u u' : X → ℝ) {ψ γ : ℝ} (hψ : 0 < ψ) (hγ : 0 < γ) :
    Intermediate (UtilityPref u) (UtilityPref u') (UtilityPref fun x => ψ * u x + γ * u' x) :=
  fun _ _ h1 h2 => by
    simp only [UtilityPref] at *
    nlinarith

/-- The utility `u_β(x) = ∑ βₙ hₙ(x)` (Exercise 21.D.9(b)). -/
def linParamUtil {X : Type*} {N : ℕ} (h : Fin N → X → ℝ) (β : Fin N → ℝ) (x : X) : ℝ :=
  ∑ n, β n * h n x

/-- **Exercise 21.D.9(b)** (MWG, p. 813). `B(x, y) = {β ∈ ℝ^N_{++} : u_β(x) > u_β(y)}` is the
intersection of `ℝ^N_{++}` with the open half-space `{β : ∑ βₙ (hₙ(x) - hₙ(y)) > 0}` (whose
boundary passes through the origin; empty if `h(x) = h(y)`). -/
theorem exercise_21_D_9b {X : Type*} {N : ℕ} (h : Fin N → X → ℝ) (x y : X) :
    {β : Fin N → ℝ | (∀ n, 0 < β n) ∧ linParamUtil h β y < linParamUtil h β x} =
      {β : Fin N → ℝ | ∀ n, 0 < β n} ∩ {β | 0 < ∑ n, β n * (h n x - h n y)} := by
  ext β
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, linParamUtil, mul_sub,
    Finset.sum_sub_distrib, sub_pos]

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Exercise 21.D.9(c)** (MWG, p. 814), what remains true. If the parameter set `P` is convex
and the preference of every convex combination of two parameters is intermediate between
theirs, then for all alternatives `x, y` the set `{β ∈ P : y ≿_β x}` (the complement of
`B(x, y)` in `P` for complete preferences) is convex. -/
theorem exercise_21_D_9c {X : Type*} {P : Set E} (hP : Convex ℝ P) (r : E → X → X → Prop)
    (hint : ∀ β ∈ P, ∀ β' ∈ P, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      Intermediate (r β) (r β') (r (a • β + b • β'))) (x y : X) :
    Convex ℝ {β ∈ P | r β y x} := by
  intro β hβ β' hβ' a b ha hb hab
  exact ⟨hP hβ.1 hβ'.1 ha hb hab, hint β hβ.1 β' hβ'.1 a b ha hb hab y x hβ.2 hβ'.2⟩

/-- The family of Exercise 21.D.9(c)'s counterexample, on alternatives `true` (`x`) and
`false` (`y`) and parameters `β ∈ [0, 1]`: `x ≻ y` at `β = 0, 1`, and `x ∼ y` for
`0 < β < 1`. -/
def e219Family (β : ℝ) (a b : Bool) : Prop :=
  a = b ∨ (a = true ∧ b = false) ∨ β ∈ Set.Ioo (0 : ℝ) 1

/-- **Exercise 21.D.9(c)** (MWG, p. 814), correction. The family `e219Family` on the convex
parameter set `[0, 1]` has intermediate preferences along segments, yet
`B(x, y) = {β ∈ [0, 1] : x ≻_β y} = {0, 1}` is not convex, so it is not the intersection of
`[0, 1]` with any half-space: the conclusion of (b) does not carry over. -/
theorem exercise_21_D_9c_counterexample :
    (∀ β ∈ Set.Icc (0 : ℝ) 1, ∀ β' ∈ Set.Icc (0 : ℝ) 1, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      a + b = 1 → Intermediate (e219Family β) (e219Family β') (e219Family (a • β + b • β'))) ∧
      ¬Convex ℝ {β ∈ Set.Icc (0 : ℝ) 1 | Strict (e219Family β) true false} ∧
      ¬∃ (s c : ℝ), {β ∈ Set.Icc (0 : ℝ) 1 | Strict (e219Family β) true false} =
        Set.Icc (0 : ℝ) 1 ∩ {β | c < s * β} := by
  have key : {β ∈ Set.Icc (0 : ℝ) 1 | Strict (e219Family β) true false} =
      Set.Icc (0 : ℝ) 1 \ Set.Ioo 0 1 := by
    ext β
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Strict, e219Family]
    simp
  have hnc : ¬Convex ℝ {β ∈ Set.Icc (0 : ℝ) 1 | Strict (e219Family β) true false} := by
    rw [key]
    intro hc
    have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 \ Set.Ioo 0 1 := by simp
    have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 \ Set.Ioo 0 1 := by simp
    have := hc h0 h1 (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)
    simp only [smul_eq_mul] at this
    norm_num at this
  refine ⟨?_, hnc, ?_⟩
  · intro β hβ β' hβ' a b ha hb hab u v h1 h2
    simp only [e219Family] at h1 h2 ⊢
    rcases h1 with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    rcases h2 with h2 | h2 | h2
    · exact Or.inl h2
    · exact Or.inr (Or.inl h2)
    exact Or.inr (Or.inr ((convex_Ioo (0 : ℝ) 1) h1 h2 ha hb hab))
  · rintro ⟨s, c, he⟩
    apply hnc
    rw [he]
    refine (convex_Icc 0 1).inter ?_
    intro u hu v hv a b ha hb hab
    simp only [Set.mem_ofPred_eq, smul_eq_mul] at hu hv ⊢
    have e : s * (a * u + b * v) - c = a * (s * u - c) + b * (s * v - c) := by
      linear_combination c * hab
    have hpos : 0 < a * (s * u - c) + b * (s * v - c) := by
      rcases eq_or_lt_of_le ha with h | h
      · have hb1 : b = 1 := by linarith
        rw [← h, hb1]
        linarith
      · nlinarith [mul_pos h (sub_pos.2 hu), mul_nonneg hb (sub_pos.2 hv).le]
    linarith

/-- **Exercise 21.D.9(d)** (MWG, p. 814), existence half. For the uniform density on the square
`[1, 2]² ⊆ ℝ²_{++}` of parameters, the centre `(3/2, 3/2)` is a median agent. -/
theorem exercise_21_D_9d_exists :
    ∃ c : EuclideanSpace ℝ (Fin 2), (∀ i, 0 < c i) ∧ IsMedianPoint (volume.restrict
      (rectangle 1 2 1 2)) c ∧ rectangle 1 2 1 2 ⊆ {z | ∀ i, 0 < z i} := by
  obtain ⟨c, hc0, hc1⟩ := figure_21_D_8a_center 1 2 1 2
  refine ⟨c, fun i => ?_, figure_21_D_8a 1 2 1 2 c hc0 hc1, fun z hz i => ?_⟩
  · fin_cases i
    · simp only [Fin.zero_eta, hc0]
      norm_num
    · simp only [Fin.mk_one, hc1]
      norm_num
  · obtain ⟨h1, -, h3, -⟩ := hz
    fin_cases i
    · simp only [Fin.zero_eta]
      linarith
    · simp only [Fin.mk_one]
      linarith

/-- **Exercise 21.D.9(e)** (MWG, p. 814). Let utilities be linear in the parameter,
`u_β(x) = ⟪β, H x⟫`, let `β*` be a median agent of the distribution `μ`, with positive mass on
every open set approaching `β*` (MWG: `g(β*) > 0`), and let `x*` be the single most preferred
alternative of `β*`. Then `x*` defeats every other alternative in pairwise majority voting. -/
theorem exercise_21_D_9e {X : Type*} (μ : Measure E) [IsProbabilityMeasure μ] (H : X → E)
    (βs : E) (hmed : IsMedianPoint μ βs)
    (hpos : ∀ U : Set E, IsOpen U → βs ∈ closure U → 0 < μ U) (xs : X)
    (hbest : ∀ y, y ≠ xs → ⟪βs, H y⟫ < ⟪βs, H xs⟫) (y : X) (hy : y ≠ xs) :
    μ {β | ⟪β, H xs⟫ < ⟪β, H y⟫} < μ {β | ⟪β, H y⟫ < ⟪β, H xs⟫} := by
  set a := H xs - H y with ha
  set c := ⟪βs, a⟫ with hc
  have hcpos : 0 < c := by
    rw [hc, ha, inner_sub_right]
    linarith [hbest y hy]
  have ha0 : a ≠ 0 := by
    intro h0
    rw [hc, h0, inner_zero_right] at hcpos
    exact lt_irrefl _ hcpos
  have hdecomp : ∀ β, ⟪β, a⟫ = ⟪β - βs, a⟫ + c := fun β => by
    rw [hc, inner_sub_left]
    ring
  set Cc := openHalfSpace βs (-a) with hCc
  have hCcm := measurableSet_openHalfSpace βs (-a)
  set S := {β : E | -c < ⟪β - βs, a⟫ ∧ ⟪β - βs, a⟫ < 0} with hS
  have hSopen : IsOpen S := by
    have hf : Continuous fun β : E => ⟪β - βs, a⟫ :=
      (continuous_id.sub continuous_const).inner continuous_const
    exact (isOpen_lt continuous_const hf).inter (isOpen_lt hf continuous_const)
  have hSclos : βs ∈ closure S := by
    have hlim : Tendsto (fun t : ℝ => βs - t • a) (𝓝[>] 0) (𝓝 βs) := by
      have : Continuous fun t : ℝ => βs - t • a := continuous_const.sub (continuous_id.smul
        continuous_const)
      have h0 := this.tendsto 0
      simp only [zero_smul, sub_zero] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    have hna : 0 < ‖a‖ ^ 2 := pow_pos (norm_pos_iff.2 ha0) 2
    refine mem_closure_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsGT (div_pos hcpos hna)] with t ht
    have e : ⟪βs - t • a - βs, a⟫ = -(t * ‖a‖ ^ 2) := by
      rw [show βs - t • a - βs = -(t • a) by abel, inner_neg_left, real_inner_smul_left,
        real_inner_self_eq_norm_sq]
    simp only [hS, Set.mem_ofPred_eq, e]
    obtain ⟨ht0, ht1⟩ := ht
    rw [lt_div_iff₀ hna] at ht1
    constructor
    · linarith
    · nlinarith
  have hSpos := hpos S hSopen hSclos
  have hsub1 : {β | ⟪β, H xs⟫ < ⟪β, H y⟫} ⊆ Cc := by
    intro β hβ
    simp only [Set.mem_ofPred_eq] at hβ
    simp only [hCc, openHalfSpace, Set.mem_ofPred_eq, inner_neg_right]
    have h1 := hdecomp β
    rw [ha, inner_sub_right] at h1
    linarith
  have hsub2 : Ccᶜ ∪ S ⊆ {β | ⟪β, H y⟫ < ⟪β, H xs⟫} := by
    intro β hβ
    have h1 := hdecomp β
    rw [ha, inner_sub_right] at h1
    simp only [Set.mem_ofPred_eq]
    rcases hβ with hβ | hβ
    · simp only [hCc, openHalfSpace, Set.mem_compl_iff, Set.mem_ofPred_eq, inner_neg_right,
        not_lt] at hβ
      linarith
    · simp only [hS, Set.mem_ofPred_eq] at hβ
      linarith [hβ.1]
  have hdisj : Disjoint Ccᶜ S := by
    rw [Set.disjoint_left]
    intro β h1 h2
    simp only [hCc, openHalfSpace, Set.mem_compl_iff, Set.mem_ofPred_eq, inner_neg_right,
      not_lt] at h1
    simp only [hS, Set.mem_ofPred_eq] at h2
    linarith [h2.2]
  have hmed' := hmed (-a) (neg_ne_zero.2 ha0)
  rw [← measure_add_measure_compl hCcm, two_mul] at hmed'
  have hle : μ Cc ≤ μ Ccᶜ := (ENNReal.add_le_add_iff_left (measure_ne_top μ Cc)).1 hmed'
  calc μ {β | ⟪β, H xs⟫ < ⟪β, H y⟫} ≤ μ Cc := measure_mono hsub1
    _ ≤ μ Ccᶜ := hle
    _ < μ Ccᶜ + μ S := ENNReal.lt_add_right (measure_ne_top μ _) (ne_of_gt hSpos)
    _ = μ (Ccᶜ ∪ S) := (measure_union hdisj hSopen.measurableSet).symm
    _ ≤ μ {β | ⟪β, H y⟫ < ⟪β, H xs⟫} := measure_mono hsub2

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Exercise 21.D.9(f)** (MWG, p. 814). Euclidean preferences fit the framework with agents
and alternatives kept apart: the agent with peak `x` ranks alternatives by
`v_x(y) = ⟪x, y⟫ - ‖y‖²/2`, which is affine in the parameter `x`. -/
theorem exercise_21_D_9f (x y z : E) :
    euclidPref x y z ↔ ⟪x, z⟫ - ‖z‖ ^ 2 / 2 ≤ ⟪x, y⟫ - ‖y‖ ^ 2 / 2 := by
  have ey : ‖y - x‖ ^ 2 = ‖y‖ ^ 2 - 2 * ⟪y, x⟫ + ‖x‖ ^ 2 := norm_sub_sq_real y x
  have ez : ‖z - x‖ ^ 2 = ‖z‖ ^ 2 - 2 * ⟪z, x⟫ + ‖x‖ ^ 2 := norm_sub_sq_real z x
  rw [real_inner_comm x y] at ey
  rw [real_inner_comm x z] at ez
  simp only [euclidPref]
  have h1 := norm_nonneg (y - x)
  have h2 := norm_nonneg (z - x)
  constructor
  · intro h
    nlinarith
  · intro h
    by_contra hc
    push Not at hc
    nlinarith

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Exercise 21.D.9(f)** (MWG, p. 814). The Euclidean preference with peak `ax + bx'`
(`a, b ≥ 0`, `a + b = 1`) is intermediate between those with peaks `x` and `x'`. -/
theorem exercise_21_D_9f_intermediate (x x' : E) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) :
    Intermediate (euclidPref x) (euclidPref x') (euclidPref (a • x + b • x')) := by
  intro y z h1 h2
  rw [exercise_21_D_9f] at h1 h2 ⊢
  rw [inner_add_left, inner_add_left, real_inner_smul_left, real_inner_smul_left,
    real_inner_smul_left, real_inner_smul_left]
  have e : ∀ t : ℝ, t = a * t + b * t := fun t => by linear_combination (-t) * hab
  rw [e (‖z‖ ^ 2 / 2), e (‖y‖ ^ 2 / 2)]
  nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]

/-- **Exercise 21.D.9(e)**, non-vacuity. On the parameter line `ℝ` with the uniform distribution
on `[0, 1]`, `β* = 1/2` is a median, open sets approaching `1/2` have positive mass, and with
`H(true) = 1`, `H(false) = -1` the alternative `true` is the single best one for `β*`. -/
theorem exercise_21_D_9e_instance :
    IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) ∧
      IsMedianPoint (volume.restrict (Set.Icc (0 : ℝ) 1)) (1 / 2) ∧
      (∀ U : Set ℝ, IsOpen U → (1 / 2 : ℝ) ∈ closure U →
        0 < volume.restrict (Set.Icc (0 : ℝ) 1) U) ∧
      ∀ y : Bool, y ≠ true → ⟪(1 / 2 : ℝ), (if y then (1 : ℝ) else -1)⟫ <
        ⟪(1 / 2 : ℝ), (if true then (1 : ℝ) else -1)⟫ := by
  refine ⟨⟨by simp⟩, ?_, fun U hU hcl => ?_, fun y hy => ?_⟩
  · intro q hq
    rw [Measure.restrict_apply_univ, Real.volume_Icc, Measure.restrict_apply
      (measurableSet_openHalfSpace _ _)]
    rcases lt_or_gt_of_ne hq with hneg | hpos
    · have e : openHalfSpace (1 / 2 : ℝ) q ∩ Set.Icc 0 1 = Set.Ico 0 (1 / 2) := by
        ext z
        simp only [openHalfSpace, Set.mem_inter_iff, Set.mem_ofPred_eq, Real.inner_apply,
          Set.mem_Icc, Set.mem_Ico]
        constructor
        · rintro ⟨h1, h2, h3⟩
          exact ⟨h2, by nlinarith⟩
        · rintro ⟨h1, h2⟩
          exact ⟨by nlinarith, h1, by linarith⟩
      rw [e, Real.volume_Ico]
      norm_num
      rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
      norm_num
    · have e : openHalfSpace (1 / 2 : ℝ) q ∩ Set.Icc 0 1 = Set.Ioc (1 / 2) 1 := by
        ext z
        simp only [openHalfSpace, Set.mem_inter_iff, Set.mem_ofPred_eq, Real.inner_apply,
          Set.mem_Icc, Set.mem_Ioc]
        constructor
        · rintro ⟨h1, h2, h3⟩
          exact ⟨by nlinarith, h3⟩
        · rintro ⟨h1, h2⟩
          exact ⟨by nlinarith, by linarith, h2⟩
      rw [e, Real.volume_Ioc]
      norm_num
      rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
      norm_num
  · obtain ⟨z, hz, hzU⟩ := mem_closure_iff_nhds.1 hcl (Set.Ioo 0 1)
      (Ioo_mem_nhds (by norm_num) (by norm_num))
    rw [Measure.restrict_apply hU.measurableSet]
    have hpos : 0 < volume (U ∩ Set.Ioo 0 1) :=
      (hU.inter isOpen_Ioo).measure_pos volume ⟨z, hzU, hz⟩
    exact lt_of_lt_of_le hpos
      (measure_mono (Set.inter_subset_inter_right _ Set.Ioo_subset_Icc_self))
  · have : y = false := by simpa using hy
    subst this
    simp only [Bool.false_eq_true, ↓reduceIte, Real.inner_apply]
    norm_num

end MWG.SocialChoice
