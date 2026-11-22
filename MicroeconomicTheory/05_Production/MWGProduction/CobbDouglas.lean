/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGProduction.Geometry
import MWGClassicalDemand.ExpCobbDouglas
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# The Cobb-Douglas production function (MWG Examples 5.B.2, 5.B.3, 5.C.1)

`f(z₁, z₂) = z₁^α z₂^β` (`cdProd α β`).

* **Example 5.B.2** (p. 130): `MRTS₁₂(z) = αz₂/(βz₁)`.
* **Example 5.B.3** (p. 133): `f(tz) = t^{α+β} f(z)`; constant, decreasing and increasing returns
  for `α + β = 1`, `< 1`, `> 1`.
* **Example 5.C.1** (pp. 142-143): the conditional factor demands and the cost function
  `c(w, q) = q^{1/(α+β)} θ φ(w)`, obtained from Chapter 3's Example 3.E.1 (the CMP for `f` is the
  EMP for the Cobb-Douglas utility `z₁^{α/(α+β)} z₂^{β/(α+β)}` at utility level `q^{1/(α+β)}`);
  the supply behaviour for `α + β < 1`, `= 1` and `> 1`.

Corrections: the printed output supply `q = (α+β)[p/θφ]^{(α+β)/(1-α-β)}` should read
`q = [(α+β)p/θφ]^{(α+β)/(1-α-β)}` (`example_5_C_1_supply`,
`example_5_C_1_printed_supply_counterexample`); and for `α + β > 1` doubling output multiplies
costs by `2^{1/(α+β)} < 2`, not `> 2` as printed (`example_5_C_1_doubling`).
-/

namespace MWG.Production

open MWG.ClassicalDemand MWG.ConsumerChoice Filter Topology

/-- **Example 5.B.2** (MWG, p. 130). The Cobb-Douglas production function `z₁^α z₂^β`. -/
noncomputable def cdProd (α β : ℝ) (z : Fin 2 → ℝ) : ℝ := z 0 ^ α * z 1 ^ β

theorem cdProd_differentiableAt (α β : ℝ) {z : Fin 2 → ℝ} (hz : StrictlyPositive z) :
    DifferentiableAt ℝ (cdProd α β) z :=
  ((differentiableAt_apply (𝕜 := ℝ) (0 : Fin 2) z).rpow_const (Or.inl (hz 0).ne')).mul
    ((differentiableAt_apply (𝕜 := ℝ) (1 : Fin 2) z).rpow_const (Or.inl (hz 1).ne'))

/-- The partial derivatives of the Cobb-Douglas function at `z ≫ 0`. -/
theorem cdProd_partial (α β : ℝ) {z : Fin 2 → ℝ} (hz : StrictlyPositive z) :
    partialF (cdProd α β) z 0 = α * z 0 ^ (α - 1) * z 1 ^ β ∧
      partialF (cdProd α β) z 1 = β * z 1 ^ (β - 1) * z 0 ^ α := by
  have hd := cdProd_differentiableAt α β hz
  constructor
  · have h1 := mc_line_hasDerivAt hd.hasFDerivAt (Pi.single 0 1)
    have heq : (fun t : ℝ => cdProd α β (z + t • Pi.single 0 1)) =
        fun t => (z 0 + t) ^ α * z 1 ^ β := by
      funext t
      simp [cdProd]
    rw [heq] at h1
    have h2 : HasDerivAt (fun t : ℝ => (z 0 + t) ^ α * z 1 ^ β)
        (1 * α * (z 0 + 0) ^ (α - 1) * z 1 ^ β) 0 :=
      (((hasDerivAt_id (0 : ℝ)).const_add (z 0)).rpow_const
        (Or.inl (by simp only [id_eq, add_zero]; exact (hz 0).ne'))).mul_const _
    simp only [add_zero, one_mul] at h2
    exact h1.unique h2
  · have h1 := mc_line_hasDerivAt hd.hasFDerivAt (Pi.single 1 1)
    have heq : (fun t : ℝ => cdProd α β (z + t • Pi.single 1 1)) =
        fun t => (z 1 + t) ^ β * z 0 ^ α := by
      funext t
      simp [cdProd, mul_comm]
    rw [heq] at h1
    have h2 : HasDerivAt (fun t : ℝ => (z 1 + t) ^ β * z 0 ^ α)
        (1 * β * (z 1 + 0) ^ (β - 1) * z 0 ^ α) 0 :=
      (((hasDerivAt_id (0 : ℝ)).const_add (z 1)).rpow_const
        (Or.inl (by simp only [id_eq, add_zero]; exact (hz 1).ne'))).mul_const _
    simp only [add_zero, one_mul] at h2
    exact h1.unique h2

/-- **Example 5.B.2** (MWG, p. 130). For `z ≫ 0` (and `β > 0`, so that `∂f/∂z₂ ≠ 0`),
`MRTS₁₂(z) = αz₂/(βz₁)`. -/
theorem example_5_B_2 {α β : ℝ} (hβ : 0 < β) {z : Fin 2 → ℝ} (hz : StrictlyPositive z) :
    MRTS (cdProd α β) z 0 1 = α * z 1 / (β * z 0) := by
  obtain ⟨h0, h1⟩ := cdProd_partial α β hz
  rw [MRTS, h0, h1, Real.rpow_sub_one (hz 0).ne', Real.rpow_sub_one (hz 1).ne']
  have := Real.rpow_pos_of_pos (hz 0) α
  have := Real.rpow_pos_of_pos (hz 1) β
  have := hz 0
  have := hz 1
  field_simp

/-- **Example 5.B.3** (MWG, p. 133). `f(tz) = t^{α+β} f(z)` for `t > 0`, `z ≥ 0`; in particular
`f(2z) = 2^{α+β} f(z)`. -/
theorem example_5_B_3_hom (α β : ℝ) {t : ℝ} (ht : 0 < t) {z : Fin 2 → ℝ} (hz : 0 ≤ z) :
    cdProd α β (t • z) = t ^ (α + β) * cdProd α β z := by
  simp only [cdProd, Pi.smul_apply, smul_eq_mul]
  rw [Real.mul_rpow ht.le (hz 0), Real.mul_rpow ht.le (hz 1), Real.rpow_add ht]
  ring

/-- **Example 5.B.3** (MWG, p. 133). Returns to scale of the Cobb-Douglas technology: constant
returns when `α + β = 1`; for `t > 1` and `f(z) > 0`, `f(tz) < tf(z)` when `α + β < 1` (decreasing
returns) and `f(tz) > tf(z)` when `α + β > 1` (increasing returns). -/
theorem example_5_B_3 {α β : ℝ} :
    (α + β = 1 → ConstantReturns (singleOutputSet (cdProd α β))) ∧
      (α + β < 1 → ∀ t : ℝ, 1 < t → ∀ z : Fin 2 → ℝ, 0 ≤ z → 0 < cdProd α β z →
        cdProd α β (t • z) < t * cdProd α β z) ∧
      (1 < α + β → ∀ t : ℝ, 1 < t → ∀ z : Fin 2 → ℝ, 0 ≤ z → 0 < cdProd α β z →
        t * cdProd α β z < cdProd α β (t • z)) := by
  refine ⟨fun h => ?_, fun h t ht z hz hf => ?_, fun h t ht z hz hf => ?_⟩
  · rw [exercise_5_B_2]
    intro z hz t ht
    rw [example_5_B_3_hom α β ht hz, h, Real.rpow_one]
  · rw [example_5_B_3_hom α β (by linarith) hz]
    have : t ^ (α + β) < t := by
      have := Real.rpow_lt_rpow_of_exponent_lt ht h
      rwa [Real.rpow_one] at this
    exact mul_lt_mul_of_pos_right this hf
  · rw [example_5_B_3_hom α β (by linarith) hz]
    have : t < t ^ (α + β) := by
      have := Real.rpow_lt_rpow_of_exponent_lt ht h
      rwa [Real.rpow_one] at this
    exact mul_lt_mul_of_pos_right this hf

/-! ### Example 5.C.1 -/

/-- The constant `θ = (α/β)^{β/(α+β)} + (α/β)^{-α/(α+β)}` of Example 5.C.1. -/
noncomputable def cdTheta (α β : ℝ) : ℝ :=
  (α / β) ^ (β / (α + β)) + (α / β) ^ (-(α / (α + β)))

/-- The function `φ(w) = w₁^{α/(α+β)} w₂^{β/(α+β)}` of Example 5.C.1. -/
noncomputable def cdPhi (α β : ℝ) (w : Fin 2 → ℝ) : ℝ :=
  w 0 ^ (α / (α + β)) * w 1 ^ (β / (α + β))

/-- The CMP for `z₁^α z₂^β` at output `q > 0` is the EMP for the Cobb-Douglas utility with
exponent `α/(α+β)` at utility level `q^{1/(α+β)}`. -/
theorem cd_inputReq_eq {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) {q : ℝ} (hq : 0 < q) :
    inputReq (cdProd α β) q =
      empConstraintSet (cobbDouglasUtility 1 (α / (α + β))) (q ^ (1 / (α + β))) := by
  have hs : 0 < α + β := by linarith
  ext z
  simp only [inputReq, empConstraintSet, Set.mem_ofPred_eq, cobbDouglasUtility, one_mul,
    nonnegOrthant]
  have h1a : 1 - α / (α + β) = β / (α + β) := by field_simp; ring
  rw [h1a]
  constructor
  · rintro ⟨hz, hqz⟩
    refine ⟨fun l => hz l, ?_⟩
    have hz0 : 0 ≤ z 0 := hz 0
    have hz1 : 0 ≤ z 1 := hz 1
    have hX : 0 ≤ z 0 ^ (α / (α + β)) * z 1 ^ (β / (α + β)) := by positivity
    have hpow : (z 0 ^ (α / (α + β)) * z 1 ^ (β / (α + β))) ^ (α + β) = cdProd α β z := by
      rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hz0,
        ← Real.rpow_mul hz1, div_mul_cancel₀ _ hs.ne', div_mul_cancel₀ _ hs.ne']
      rfl
    rw [← Real.rpow_le_rpow_iff (by positivity) hX hs, ← Real.rpow_mul hq.le,
      one_div_mul_cancel hs.ne', Real.rpow_one, hpow]
    exact hqz
  · rintro ⟨hz, hqz⟩
    have hz' : 0 ≤ z := fun l => hz l
    refine ⟨hz', ?_⟩
    have hz0 : 0 ≤ z 0 := hz 0
    have hz1 : 0 ≤ z 1 := hz 1
    have hpow : (z 0 ^ (α / (α + β)) * z 1 ^ (β / (α + β))) ^ (α + β) = cdProd α β z := by
      rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hz0,
        ← Real.rpow_mul hz1, div_mul_cancel₀ _ hs.ne', div_mul_cancel₀ _ hs.ne']
      rfl
    have := Real.rpow_le_rpow (by positivity) hqz hs.le
    rw [← Real.rpow_mul hq.le, one_div_mul_cancel hs.ne', Real.rpow_one, hpow] at this
    exact this

/-- `α^{-α}(1-α)^{α-1}` with `α = a/(a+b)` equals the book's `θ`. -/
theorem cdTheta_eq {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    (α / (α + β)) ^ (-(α / (α + β))) * (1 - α / (α + β)) ^ (α / (α + β) - 1) = cdTheta α β := by
  have hs : 0 < α + β := by linarith
  have h1a : 1 - α / (α + β) = β / (α + β) := by field_simp; ring
  have h2 : α / (α + β) - 1 = -(β / (α + β)) := by field_simp; ring
  have hA := Real.rpow_pos_of_pos hα (α / (α + β))
  have hB := Real.rpow_pos_of_pos hβ (β / (α + β))
  have hsplit : (α + β) ^ (α / (α + β)) * (α + β) ^ (β / (α + β)) = α + β := by
    rw [← Real.rpow_add hs, ← add_div, div_self hs.ne', Real.rpow_one]
  have hαs : α ^ (β / (α + β)) = α / α ^ (α / (α + β)) := by
    rw [eq_div_iff hA.ne', ← Real.rpow_add hα, ← add_div, add_comm, div_self hs.ne',
      Real.rpow_one]
  have hβs : β ^ (α / (α + β)) = β / β ^ (β / (α + β)) := by
    rw [eq_div_iff hB.ne', ← Real.rpow_add hβ, ← add_div, div_self hs.ne', Real.rpow_one]
  have e1 : (α / (α + β)) ^ (-(α / (α + β))) = (α + β) ^ (α / (α + β)) / α ^ (α / (α + β)) := by
    rw [Real.rpow_neg (div_pos hα hs).le, Real.div_rpow hα.le hs.le, inv_div]
  have e2 : (β / (α + β)) ^ (-(β / (α + β))) = (α + β) ^ (β / (α + β)) / β ^ (β / (α + β)) := by
    rw [Real.rpow_neg (div_pos hβ hs).le, Real.div_rpow hβ.le hs.le, inv_div]
  have e3 : (α / β) ^ (β / (α + β)) = α / α ^ (α / (α + β)) / β ^ (β / (α + β)) := by
    rw [Real.div_rpow hα.le hβ.le, hαs]
  have e4 : (α / β) ^ (-(α / (α + β))) = β / β ^ (β / (α + β)) / α ^ (α / (α + β)) := by
    rw [Real.rpow_neg (div_pos hα hβ).le, Real.div_rpow hα.le hβ.le, inv_div, hβs]
  rw [h1a, h2, cdTheta, e1, e2, e3, e4, div_mul_div_comm, hsplit]
  field_simp

/-- **Example 5.C.1** (MWG, p. 142). For `f(z) = z₁^α z₂^β` (`α, β > 0`), `w ≫ 0` and `q > 0`:
the conditional factor demands are
`z₁(w, q) = q^{1/(α+β)}(αw₂/(βw₁))^{β/(α+β)}`, `z₂(w, q) = q^{1/(α+β)}(βw₁/(αw₂))^{α/(α+β)}`,
and the cost function is `c(w, q) = q^{1/(α+β)} θ φ(w)`. -/
theorem example_5_C_1_cost {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) {w : Fin 2 → ℝ}
    (hw : StrictlyPositive w) {q : ℝ} (hq : 0 < q) :
    costFn (cdProd α β) w q = q ^ (1 / (α + β)) * cdTheta α β * cdPhi α β w ∧
      condDemand (cdProd α β) w q =
        {![q ^ (1 / (α + β)) * (α * w 1 / (β * w 0)) ^ (β / (α + β)),
          q ^ (1 / (α + β)) * (β * w 0 / (α * w 1)) ^ (α / (α + β))]} := by
  have hs : 0 < α + β := by linarith
  have ha0 : 0 < α / (α + β) := div_pos hα hs
  have ha1 : α / (α + β) < 1 := by rw [div_lt_one hs]; linarith
  have hub : 0 < q ^ (1 / (α + β)) := Real.rpow_pos_of_pos hq _
  obtain ⟨hexp, hhick⟩ := example_3_E_1 ha0 ha1 hw hub
  have h1a : 1 - α / (α + β) = β / (α + β) := by field_simp; ring
  have hratio : α / (α + β) / (1 - α / (α + β)) = α / β := by rw [h1a]; field_simp
  constructor
  · unfold costFn
    rw [cd_inputReq_eq hα hβ hq, ← expenditure_eq_supportFn, hexp,
      cdExpenditure_eq_book ha0 ha1 hw, ← cdTheta_eq hα hβ, cdPhi, h1a]
    ring
  · unfold condDemand
    rw [cd_inputReq_eq hα hβ hq]
    change hicksianDemand _ _ _ = _
    rw [hhick]
    congr 1
    obtain ⟨e0, e1⟩ := cdHicksian_eq_book ha0 ha1 hw (q ^ (1 / (α + β)))
    funext l
    fin_cases l
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      rw [e0, h1a]
      have : α / (α + β) * w 1 / (β / (α + β) * w 0) = α * w 1 / (β * w 0) := by
        field_simp
      rw [this, mul_comm]
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [e1, h1a]
      have : β / (α + β) * w 0 / (α / (α + β) * w 1) = β * w 0 / (α * w 1) := by
        field_simp
      rw [this, mul_comm]

/-- **Example 5.C.1** (MWG, p. 142), `α + β < 1`, corrected: with `c(q) = Kq^{1/s}`
(`K = θφ(w) > 0`, `s = α + β ∈ (0, 1)`) and `p > 0`, the unique solution of the first-order
condition (5.C.7), `q* = (sp/K)^{s/(1-s)}`, maximizes profits (5.C.5) (sufficient because `c` is
convex in `q`). -/
theorem example_5_C_1_supply {s K p : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hK : 0 < K) (hp : 0 < p) :
    let qs := (s * p / K) ^ (s / (1 - s))
    HasDerivAt (fun q => K * q ^ (1 / s)) p qs ∧
      ∀ q, 0 ≤ q → p * q - K * q ^ (1 / s) ≤ p * qs - K * qs ^ (1 / s) := by
  intro qs
  have hspK : 0 < s * p / K := by positivity
  have hqs : 0 < qs := Real.rpow_pos_of_pos hspK _
  have hr : 1 ≤ 1 / s := by rw [le_div_iff₀ hs0]; linarith
  have hpow : qs ^ (1 / s - 1) = s * p / K := by
    rw [← Real.rpow_mul hspK.le]
    have h1s : (1 - s) ≠ 0 := by linarith
    have : s / (1 - s) * (1 / s - 1) = 1 := by field_simp
    rw [this, Real.rpow_one]
  have hd : HasDerivAt (fun q => K * q ^ (1 / s)) p qs := by
    have := (Real.hasDerivAt_rpow_const (p := 1 / s) (Or.inl hqs.ne')).const_mul K
    convert this using 1
    rw [hpow]
    field_simp
  refine ⟨hd, ?_⟩
  have hconv : ConvexOn ℝ (Set.Ici 0) (fun q : ℝ => K * q ^ (1 / s)) :=
    (convexOn_rpow hr).smul hK.le
  exact foc_5_C_6_sufficient hconv hqs.le hd (by linarith) (fun _ => rfl)

/-- The printed supply `q = (α+β)[p/θφ]^{(α+β)/(1-α-β)}` (MWG, p. 142) is wrong (correction): for
`s = α + β = 1/3`, `K = θφ = 1`, `p = 1` it gives `q = 1/3`, at which (5.C.7) fails
(`K(1/s)q^{1/s - 1} = 1/3 ≠ p`) and profits `q - q³` are lower than at `q = 1/2`. -/
theorem example_5_C_1_printed_supply_counterexample :
    let s : ℝ := 1 / 3
    let qbook : ℝ := s * (1 / 1) ^ (s / (1 - s))
    qbook = 1 / 3 ∧ 1 * (1 / s) * qbook ^ ((1 / s) - 1) ≠ 1 ∧
      1 * qbook - 1 * qbook ^ (1 / s) < 1 * (1 / 2) - 1 * (1 / 2 : ℝ) ^ (1 / s) := by
  intro s qbook
  have hs : (1 / s : ℝ) = 3 := by norm_num [s]
  have hq : qbook = 1 / 3 := by simp [qbook, s]
  refine ⟨hq, ?_, ?_⟩
  · rw [hs, hq, show (3 : ℝ) - 1 = (2 : ℕ) by norm_num, Real.rpow_natCast]
    norm_num
  · rw [hs, hq, show (3 : ℝ) = (3 : ℕ) by norm_num, Real.rpow_natCast, Real.rpow_natCast]
    norm_num

/-- **Example 5.C.1** (MWG, p. 142), `α + β = 1`: with `c(q) = Kq`, `q = 0` is the unique optimum
if `K > p`, no solution exists if `K < p`, and every `q ≥ 0` is optimal (with zero profit) if
`K = p`. -/
theorem example_5_C_1_crs {K p : ℝ} :
    (p < K → outputSupply (fun q => K * q) p = {0}) ∧
      (K < p → outputSupply (fun q => K * q) p = ∅) ∧
      (K = p → outputSupply (fun q => K * q) p = Set.Ici 0) := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · ext q
    simp only [outputSupply, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hq, hopt⟩
      have := hopt 0 le_rfl
      nlinarith
    · rintro rfl
      exact ⟨le_rfl, fun q' hq' => by nlinarith⟩
  · ext q
    simp only [outputSupply, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hq hopt
    have := hopt (q + 1) (by linarith)
    nlinarith
  · ext q
    simp only [outputSupply, Set.mem_ofPred_eq, Set.mem_Ici]
    subst h
    constructor
    · exact fun h => h.1
    · exact fun hq => ⟨hq, fun q' _ => by ring_nf; exact le_rfl⟩

/-- **Example 5.C.1** (MWG, p. 143), `α + β > 1`: with `c(q) = Kq^{1/s}`, `s > 1`, and `p > 0`,
profits are unbounded, so the PMP has no solution. -/
theorem example_5_C_1_irs {s K p : ℝ} (hs : 1 < s) (hK : 0 < K) (hp : 0 < p) (M : ℝ) :
    ∃ q, 0 ≤ q ∧ M < p * q - K * q ^ (1 / s) := by
  have hr0 : 0 < 1 / s := by positivity
  have hr1 : 1 / s < 1 := by rw [div_lt_one (by linarith)]; exact hs
  set q := max ((2 * K / p) ^ (1 / (1 - 1 / s))) (2 * (|M| + 1) / p) with hq
  have hq1 : 0 < q := lt_max_of_lt_right (by positivity)
  refine ⟨q, hq1.le, ?_⟩
  -- `K q^{1/s} ≤ pq/2` because `q^{1 - 1/s} ≥ 2K/p`
  have hA : 2 * K / p ≤ q ^ (1 - 1 / s) := by
    have h1 : (2 * K / p) ^ (1 / (1 - 1 / s)) ≤ q := le_max_left _ _
    have h2 := Real.rpow_le_rpow (by positivity) h1 (by linarith : (0 : ℝ) ≤ 1 - 1 / s)
    rwa [← Real.rpow_mul (by positivity), one_div_mul_cancel (by linarith), Real.rpow_one]
      at h2
  have hsplit : q = q ^ (1 / s) * q ^ (1 - 1 / s) := by
    rw [← Real.rpow_add hq1, add_sub_cancel, Real.rpow_one]
  have hB : K * q ^ (1 / s) ≤ p * q / 2 := by
    have hqs := Real.rpow_pos_of_pos hq1 (1 / s)
    calc K * q ^ (1 / s) = (p / 2) * (2 * K / p) * q ^ (1 / s) := by field_simp
      _ ≤ (p / 2) * q ^ (1 - 1 / s) * q ^ (1 / s) := by gcongr
      _ = (p / 2) * (q ^ (1 / s) * q ^ (1 - 1 / s)) := by ring
      _ = p * q / 2 := by rw [← hsplit]; ring
  have hC : 2 * (|M| + 1) / p ≤ q := le_max_right _ _
  rw [div_le_iff₀ hp] at hC
  linarith [le_abs_self M]

/-- **Example 5.C.1** (MWG, p. 143), correction of "a factor of `2^{1/(α+β)} > 2`": with increasing
returns (`α + β > 1`), doubling output multiplies costs by `2^{1/(α+β)}`, which is `< 2`. -/
theorem example_5_C_1_doubling {s K q : ℝ} (hs : 1 < s) (hq : 0 ≤ q) :
    K * (2 * q) ^ (1 / s) = (2 : ℝ) ^ (1 / s) * (K * q ^ (1 / s)) ∧ (2 : ℝ) ^ (1 / s) < 2 := by
  refine ⟨by rw [Real.mul_rpow (by norm_num) hq]; ring, ?_⟩
  have h := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2)
    (show 1 / s < 1 by rw [div_lt_one (by linarith)]; exact hs)
  rwa [Real.rpow_one] at h

end MWG.Production
