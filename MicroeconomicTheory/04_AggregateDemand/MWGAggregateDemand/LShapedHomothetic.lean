/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGAggregateDemand.LShaped
import MWGAggregateDemand.AggregateWealth
import MWGClassicalDemand.UtilityExercises
import MWGConsumerChoice.Aggregation
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# Exercise 4.C.4: L-shaped indifference curves and the ULD

MWG, Exercise 4.C.4 (p. 124). The preference on `ℝ²_+` has L-shaped indifference curves with
kinks on the graph of `φ` (`u(x) = min(φ(x₁), x₂)`, `φ` continuous, strictly increasing,
`φ(0) = 0`, unbounded). Following the hint (differentiable demand):

* `slutsky_zero_minUtility`: the Slutsky matrix is zero (no substitution effects);
* `exercise_4_C_4_hint`: if `S = 0`, `p·D_w x = 1` and `D_w x ≠ x/w`, some `v` has
  `v·D_p x v > 0`;
* `exercise_4_C_4`: if the demand is differentiable and satisfies the ULD, then
  `D_w x = x/w` everywhere, so `x(p, w) = w x(p, 1)`, the kink curve is a ray (`φ(t) = φ(1) t`)
  and the preference is homothetic.
-/

namespace MWG.AggregateDemand

open MWG.ConsumerChoice MWG.ClassicalDemand Filter Topology

/-- **Exercise 4.C.4** (MWG, p. 124), the hint. Let `D` be the derivative of a demand function at
`(p, w)` with `x̄ = x(p, w)`, `p·x̄ = w > 0`, Slutsky matrix `S = 0` and `p·D_w x = 1`. If
`D_w x ≠ x̄/w`, there is `v` with `v·D_p x v > 0`. -/
theorem exercise_4_C_4_hint {L : ℕ} {D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)}
    {x p : Fin L → ℝ} {w : ℝ} (hw : 0 < w) (hpx : p ⬝ᵥ x = w)
    (hS : slutskyMatrix D x = 0) (hpb : p ⬝ᵥ wealthJacobian D = 1)
    (hne : wealthJacobian D ≠ w⁻¹ • x) :
    ∃ v : Fin L → ℝ, 0 < v ⬝ᵥ Matrix.mulVec (priceJacobian D) v := by
  set b := wealthJacobian D with hbdef
  have hDp : priceJacobian D = -Matrix.vecMulVec b x := by
    have := slutskyMatrix_eq D x
    rw [hS] at this
    rw [eq_neg_iff_add_eq_zero, ← this]
  -- `b` and `x` are not parallel
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [dotProduct_zero] at hpx
    linarith
  have hC : 0 < x ⬝ᵥ x := by
    rcases Function.ne_iff.mp hx0 with ⟨l, hl⟩
    calc (0 : ℝ) < x l * x l := mul_self_pos.mpr hl
      _ ≤ x ⬝ᵥ x := Finset.single_le_sum (f := fun k => x k * x k)
          (fun k _ => mul_self_nonneg (x k)) (Finset.mem_univ l)
  have hid : ((x ⬝ᵥ x) • b - (b ⬝ᵥ x) • x) ⬝ᵥ ((x ⬝ᵥ x) • b - (b ⬝ᵥ x) • x) =
      (x ⬝ᵥ x) * ((b ⬝ᵥ b) * (x ⬝ᵥ x) - (b ⬝ᵥ x) * (b ⬝ᵥ x)) := by
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [dotProduct_comm x b]
    ring
  have hdet : 0 < (b ⬝ᵥ b) * (x ⬝ᵥ x) - (b ⬝ᵥ x) * (b ⬝ᵥ x) := by
    have hnn : 0 ≤ ((x ⬝ᵥ x) • b - (b ⬝ᵥ x) • x) ⬝ᵥ ((x ⬝ᵥ x) • b - (b ⬝ᵥ x) • x) :=
      Finset.sum_nonneg fun l _ => mul_self_nonneg _
    rcases hnn.lt_or_eq with h | h
    · rw [hid] at h
      exact pos_of_mul_pos_right h hC.le
    · exfalso
      have h0 : (x ⬝ᵥ x) • b - (b ⬝ᵥ x) • x = 0 := dotProduct_self_eq_zero.mp h.symm
      have hb : b = ((b ⬝ᵥ x) / (x ⬝ᵥ x)) • x := by
        rw [sub_eq_zero] at h0
        rw [div_eq_inv_mul, mul_smul, ← h0, smul_smul, inv_mul_cancel₀ hC.ne', one_smul]
      apply hne
      have hc : (b ⬝ᵥ x) / (x ⬝ᵥ x) * w = 1 := by
        have := hpb
        rw [hb, dotProduct_smul, smul_eq_mul, hpx] at this
        exact this
      rw [hb]
      congr 1
      field_simp at hc ⊢
      linarith
  -- `v = α b + β x` with `v·b = 1`, `v·x = -1`
  set δ := (b ⬝ᵥ b) * (x ⬝ᵥ x) - (b ⬝ᵥ x) * (b ⬝ᵥ x) with hδ
  set v := ((x ⬝ᵥ x + b ⬝ᵥ x) / δ) • b + (-(b ⬝ᵥ x + b ⬝ᵥ b) / δ) • x with hv
  have hvb : v ⬝ᵥ b = 1 := by
    simp only [hv, add_dotProduct, smul_dotProduct, smul_eq_mul]
    rw [dotProduct_comm x b]
    field_simp
    rw [hδ]
    ring
  have hvx : x ⬝ᵥ v = -1 := by
    simp only [hv, dotProduct_add, dotProduct_smul, smul_eq_mul]
    rw [dotProduct_comm x b]
    field_simp
    rw [hδ]
    ring
  refine ⟨v, ?_⟩
  rw [hDp, Matrix.neg_mulVec, dotProduct_neg, dot_vecMulVec_mulVec, hvb, hvx]
  norm_num

/-- With the kink curve `x₂ = φ(x₁)` and `φ` continuous, strictly increasing, `φ(0) = 0` and
unbounded, every budget line `p·y = w` (`p ≫ 0`, `w > 0`) meets the kink curve at a unique
point, which is the demand. -/
theorem minUtility_kink_point {φ : ℝ → ℝ} (hφc : Continuous φ) (hφ : StrictMono φ)
    (hφ0 : φ 0 = 0) (hφu : Tendsto φ atTop atTop) {p : Fin 2 → ℝ} (hp : StrictlyPositive p)
    {w : ℝ} (hw : 0 < w) : ∃ t, 0 < t ∧ p 0 * t + p 1 * φ t = w := by
  have hc : Continuous fun t => p 0 * t + p 1 * φ t := by fun_prop
  obtain ⟨T, hT⟩ := eventually_atTop.mp ((tendsto_atTop.mp hφu) (w / p 1))
  have hT' := hT (max T (w / p 0)) (le_max_left _ _)
  set M := max T (w / p 0)
  have hM : 0 ≤ M := (div_pos hw (hp 0)).le.trans (le_max_right _ _)
  have hφM : 0 ≤ φ M := by rw [← hφ0]; exact hφ.monotone hM
  have hval : w ≤ p 0 * M + p 1 * φ M := by
    have h1 : p 1 * (w / p 1) ≤ p 1 * φ M := mul_le_mul_of_nonneg_left hT' (hp 1).le
    rw [mul_div_cancel₀ _ (hp 1).ne'] at h1
    nlinarith [hp 0]
  obtain ⟨t, ht, hteq⟩ := intermediate_value_Icc hM hc.continuousOn
    ⟨by simpa [hφ0] using hw.le, hval⟩
  refine ⟨t, ?_, hteq⟩
  rcases ht.1.lt_or_eq with h | h
  · exact h
  · rw [← h] at hteq
    simp [hφ0] at hteq
    linarith

/-- The demand of `min(φ(x₁), x₂)` at `(p, w)` is the kink point on the budget line. -/
theorem minUtility_demand_eq {φ : ℝ → ℝ} (hφc : Continuous φ) (hφ : StrictMono φ)
    (hφ0 : φ 0 = 0) (hφu : Tendsto φ atTop atTop) {xf : DemandFunction 2}
    (hxf : ∀ p w, PWDomain p w → xf p w ∈ walrasianDemand (minUtility φ id) p w)
    {p : Fin 2 → ℝ} {w : ℝ} (hd : PWDomain p w) :
    ∃ t, 0 < t ∧ p 0 * t + p 1 * φ t = w ∧ xf p w = ![t, φ t] := by
  obtain ⟨t, ht, hteq⟩ := minUtility_kink_point hφc hφ hφ0 hφu hd.1 hd.2
  have hφt : 0 ≤ φ t := by rw [← hφ0]; exact hφ.monotone ht.le
  have h := walrasianDemand_minUtility hφ strictMono_id hd.1 (w := w) (y := ![t, φ t])
    (by simpa using ht.le) (by simpa using hφt) (by simp)
    (by rw [dotProduct_two]; simpa using hteq)
  have := hxf p w hd
  rw [h] at this
  exact ⟨t, ht, hteq, this⟩

/-- **Exercise 4.C.4** (MWG, p. 124), the hint's first claim. With L-shaped indifference curves
there are no substitution effects: wherever the demand is differentiable, `S(p, w) = 0`. -/
theorem slutsky_zero_minUtility {φ : ℝ → ℝ} (hφc : Continuous φ) (hφ : StrictMono φ)
    (hφ0 : φ 0 = 0) (hφu : Tendsto φ atTop atTop) {xf : DemandFunction 2}
    (hxf : ∀ p w, PWDomain p w → xf p w ∈ walrasianDemand (minUtility φ id) p w)
    {p : Fin 2 → ℝ} {w : ℝ} (hd : PWDomain p w) {D : ((Fin 2 → ℝ) × ℝ) →L[ℝ] (Fin 2 → ℝ)}
    (hD : HasFDerivAt (Function.uncurry xf) D (p, w)) : slutskyMatrix D (xf p w) = 0 := by
  obtain ⟨t, ht, hteq, hx⟩ := minUtility_demand_eq hφc hφ hφ0 hφu hxf hd
  have hφt : 0 ≤ φ t := by rw [← hφ0]; exact hφ.monotone ht.le
  have hSv : ∀ v : Fin 2 → ℝ, Matrix.mulVec (slutskyMatrix D (xf p w)) v = 0 := by
    intro v
    rw [slutskyMatrix_mulVec]
    have hpath := hasDerivAt_path hD v (v ⬝ᵥ xf p w)
    have hev : (fun s : ℝ => xf (p + s • v) (w + s * (v ⬝ᵥ xf p w))) =ᶠ[𝓝 0]
        fun _ => xf p w := by
      have hc : Continuous fun s : ℝ => (p + s • v, w + s * (v ⬝ᵥ xf p w)) := by fun_prop
      have hlim := hc.tendsto 0
      simp only [zero_smul, add_zero, zero_mul] at hlim
      filter_upwards [hlim.eventually ((isOpen_pwDomain 2).mem_nhds hd)] with s hs
      have hpx : p ⬝ᵥ xf p w = w := by
        rw [hx, dotProduct_two]
        simpa using hteq
      have h := walrasianDemand_minUtility hφ strictMono_id hs.1
        (w := w + s * (v ⬝ᵥ xf p w)) (y := xf p w)
        (by rw [hx]; simpa using ht.le) (by rw [hx]; simpa using hφt) (by rw [hx]; simp)
        (by rw [add_dotProduct, smul_dotProduct, smul_eq_mul, hpx])
      have := hxf _ _ hs
      rw [h] at this
      exact this
    exact hpath.unique ((hasDerivAt_const (0 : ℝ) (xf p w)).congr_of_eventuallyEq hev)
  ext l k
  have := congrFun (hSv (Pi.single k 1)) l
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this

/-- **Exercise 4.C.4** (MWG, p. 124). Let `≿` on `ℝ²_+` have L-shaped indifference curves with
kinks on the graph of `φ` (`u(x) = min(φ(x₁), x₂)`, `φ` continuous, strictly increasing,
`φ(0) = 0`, unbounded) and let its demand function be differentiable on the domain (as in the
hint). If the demand satisfies the ULD, then the kink curve is a ray, `φ(t) = φ(1) t`, and `≿`
is homothetic. -/
theorem exercise_4_C_4 {φ : ℝ → ℝ} (hφc : Continuous φ) (hφ : StrictMono φ) (hφ0 : φ 0 = 0)
    (hφu : Tendsto φ atTop atTop) {xf : DemandFunction 2}
    (hxf : ∀ p w, PWDomain p w → xf p w ∈ walrasianDemand (minUtility φ id) p w)
    (hdiff : ∀ p w, PWDomain p w → DifferentiableAt ℝ (Function.uncurry xf) (p, w))
    (hU : UncompensatedLawOfDemand xf) :
    (∀ t, 0 ≤ t → φ t = φ 1 * t) ∧
      Homothetic (nonnegOrthant 2) (utilityPref (minUtility φ id)) := by
  have hW : WalrasLaw xf := by
    intro p w hd
    obtain ⟨t, -, hteq, hx⟩ := minUtility_demand_eq hφc hφ hφ0 hφu hxf hd
    rw [hx, dotProduct_two]
    simpa using hteq
  -- `D_w x = x/w` everywhere
  have hwe : ∀ p w, PWDomain p w →
      wealthJacobian (fderiv ℝ (Function.uncurry xf) (p, w)) = w⁻¹ • xf p w := by
    intro p w hd
    by_contra hne
    have hD := (hdiff p w hd).hasFDerivAt
    obtain ⟨v, hv⟩ := exercise_4_C_4_hint hd.2 (hW p w hd)
      (slutsky_zero_minUtility hφc hφ hφ0 hφu hxf hd hD) (proposition_2_E_3_matrix hW hd hD) hne
    have := exercise_4_C_1_nsd hU hd hD v
    linarith
  set pb : Fin 2 → ℝ := ![1, 1] with hpb
  have hpbpos : StrictlyPositive pb := by intro l; fin_cases l <;> simp [pb]
  -- `w ↦ x(p̄, w)/w` is constant
  have hder : ∀ w ∈ Set.Ioi (0 : ℝ), HasDerivAt (fun w => w⁻¹ • xf pb w) 0 w := by
    intro w hw
    have hw' : (0 : ℝ) < w := hw
    have hd : PWDomain pb w := ⟨hpbpos, hw'⟩
    have hD := (hdiff pb w hd).hasFDerivAt
    have hl : HasDerivAt (fun s : ℝ => ((pb, s) : (Fin 2 → ℝ) × ℝ)) ((0 : Fin 2 → ℝ), (1 : ℝ)) w :=
      (hasDerivAt_const w pb).prodMk (hasDerivAt_id w)
    have hx : HasDerivAt (fun s => xf pb s) (w⁻¹ • xf pb w) w := by
      have := hD.comp_hasDerivAt w hl
      rw [← hwe pb w hd]
      exact this
    have := (hasDerivAt_inv hw'.ne').smul hx
    convert this using 1
    rw [smul_smul]
    field_simp
    simp
  have hconst : ∀ w, 0 < w → xf pb w = w • xf pb 1 := by
    intro w hw
    have := (isOpen_Ioi (a := (0 : ℝ))).is_const_of_deriv_eq_zero (convex_Ioi 0).isPreconnected
      (fun s hs => (hder s hs).differentiableAt.differentiableWithinAt)
      (fun s hs => (hder s hs).deriv) (Set.mem_Ioi.mpr hw) (Set.mem_Ioi.mpr one_pos)
    simp only [inv_one, one_smul] at this
    rw [← this, smul_smul, mul_inv_cancel₀ hw.ne', one_smul]
  -- the kink point on the budget line `t + φ(t) = w` at `p̄`
  have hkink : ∀ t, 0 < t → xf pb (t + φ t) = ![t, φ t] := by
    intro t ht
    have hφt : 0 ≤ φ t := by rw [← hφ0]; exact hφ.monotone ht.le
    have h := walrasianDemand_minUtility hφ strictMono_id hpbpos (w := t + φ t) (y := ![t, φ t])
      (by simpa using ht.le) (by simpa using hφt) (by simp)
      (by rw [dotProduct_two]; simp [pb])
    have := hxf pb (t + φ t) ⟨hpbpos, by linarith⟩
    rw [h] at this
    exact this
  obtain ⟨s, hs, -, hx1⟩ := minUtility_demand_eq hφc hφ hφ0 hφu hxf (p := pb) (w := 1)
    ⟨hpbpos, one_pos⟩
  have hray : ∀ t, 0 < t → φ t = φ s / s * t := by
    intro t ht
    have hφt : 0 ≤ φ t := by rw [← hφ0]; exact hφ.monotone ht.le
    have e := hconst (t + φ t) (by linarith)
    rw [hkink t ht, hx1] at e
    have e0 : t = (t + φ t) * s := by simpa using congrFun e 0
    have e1 : φ t = (t + φ t) * φ s := by simpa using congrFun e 1
    have hs0 := hs.ne'
    have key : φ t * s = φ s * t := by linear_combination s * e1 - φ s * e0
    field_simp
    linarith
  have hφ1 : φ 1 = φ s / s := by rw [hray 1 one_pos, mul_one]
  have hlin : ∀ t, 0 ≤ t → φ t = φ 1 * t := by
    intro t ht
    rcases ht.lt_or_eq with ht | ht
    · rw [hray t ht, hφ1]
    · rw [← ht, hφ0, mul_zero]
  refine ⟨hlin, exercise_3_C_5a_if (representsOn_utilityPref _ _) fun x hx a ha => ?_⟩
  simp only [minUtility, Pi.smul_apply, smul_eq_mul, id]
  rw [hlin _ (mul_nonneg ha.le (hx 0)), hlin _ (hx 0), mul_left_comm, mul_min_of_nonneg _ _ ha.le]

end MWG.AggregateDemand
