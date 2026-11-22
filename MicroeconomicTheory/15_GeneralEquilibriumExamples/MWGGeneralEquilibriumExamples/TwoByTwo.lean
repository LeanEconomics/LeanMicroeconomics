/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGGeneralEquilibriumExamples.FactorMarkets
import MWGCompetitiveMarkets.FOCTools
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# The 2 × 2 production model (MWG Section 15.D, pp. 532-538)

Two constant-returns firms produce goods 1 and 2 (indices `0`, `1`) from two factors. The model is
described by the production functions `fⱼ` together with the cost-minimizing unit input vectors
`aⱼ(w) = (a_{1j}(w), a_{2j}(w))` (assumed unique, as in the book), whose standing properties are
collected in `TwoByTwo.IsModel`; the unit cost is `cⱼ(w) = w·aⱼ(w)`. We assume in addition that the
unit input vectors are continuous in `w` (true in every example, and a consequence of uniqueness
by the maximum theorem); differentiability of `cⱼ` (Shephard's lemma `∇cⱼ = aⱼ`, used by the book)
is then proved (`unitCost_hasDerivAt`).

* **Definition 15.D.1** (`TwoByTwo.FactorIntensity`).
* Constant returns: profit maximization means zero profit, `pⱼ ≤ cⱼ(w)` with equality when
  `qⱼ > 0`, and `zⱼ = qⱼ aⱼ(w)` (`crs_profitMax_iff`); the equilibrium conditions allowing for
  specialization (**Exercise 15.D.6(a)**, `exercise_15_D_6a`), (15.D.7) and (15.D.3)-(15.D.4) in
  their constant-returns form (`interior_eqm_iff`), and the equilibrium factor allocation of
  Figure 15.D.5 (`interior_eqm_allocation`).
* Under factor intensity the curves `c₁(w) = p₁` and `c₂(w) = p₂` cross at most once
  (`unitCost_ratio_strictMono`, footnote 14): the **factor price equalization theorem**
  (`factor_price_equalization`).
* **Proposition 15.D.1** (Stolper-Samuelson; `proposition_15_D_1`, global form) and its
  differential proof (`proposition_15_D_1_differential`); **Exercise 15.D.3**: the factor price
  rises proportionally more than the good's price and the owner of that factor is better off.
* **Proposition 15.D.2** (Rybczynski) and **Exercise 15.D.5** (magnification).
* **Exercise 15.D.6(b)** and footnote 15: the economy is diversified exactly when the endowment
  lies in the diversification cone.
* An instance: the Leontief model (`leontiefModel`) satisfies all standing assumptions and the
  factor intensity condition.
-/

namespace MWG.GeneralEquilibriumExamples

open MWG.ConsumerChoice MWG.CompetitiveMarkets Filter Topology

/-- **Section 15.D** (MWG, p. 532). The 2 × 2 production model: production functions `fⱼ` and
unit input vectors `aⱼ(w)` (`a j w ℓ` is the amount of factor `ℓ` per unit of good `j`). -/
structure TwoByTwo where
  /-- The production functions. -/
  f : Fin 2 → (Fin 2 → ℝ) → ℝ
  /-- The cost-minimizing unit input vectors. -/
  a : Fin 2 → (Fin 2 → ℝ) → Fin 2 → ℝ

/-- **Section 15.D** (MWG, p. 532). The standing assumptions: `fⱼ ≥ 0`, homogeneous of degree one
on `ℝ²₊`; `aⱼ(w)` (for `w ≫ 0`) produces one unit, is the unique cost minimizer among bundles
producing at least one unit, is strictly positive and continuous in the relative factor price. -/
structure TwoByTwo.IsModel (M : TwoByTwo) : Prop where
  f_nonneg : ∀ j, ∀ z ∈ nonnegOrthant 2, 0 ≤ M.f j z
  hom : ∀ j, ∀ z ∈ nonnegOrthant 2, ∀ t : ℝ, 0 ≤ t → M.f j (t • z) = t * M.f j z
  a_mem : ∀ j w, StrictlyPositive w → M.a j w ∈ nonnegOrthant 2 ∧ M.f j (M.a j w) = 1
  a_min : ∀ j w, StrictlyPositive w → ∀ z ∈ nonnegOrthant 2, 1 ≤ M.f j z →
    w ⬝ᵥ M.a j w ≤ w ⬝ᵥ z
  a_unique : ∀ j w, StrictlyPositive w → ∀ z ∈ nonnegOrthant 2, 1 ≤ M.f j z →
    w ⬝ᵥ z ≤ w ⬝ᵥ M.a j w → z = M.a j w
  a_pos : ∀ j w l, StrictlyPositive w → 0 < M.a j w l
  a_cont : ∀ j l, ContinuousOn (fun t : ℝ => M.a j ![t, 1] l) (Set.Ioi 0)

/-- **Section 15.D** (MWG, p. 532). The unit cost `cⱼ(w) = w·aⱼ(w)`. -/
def TwoByTwo.c (M : TwoByTwo) (j : Fin 2) (w : Fin 2 → ℝ) : ℝ := w ⬝ᵥ M.a j w

/-- **Definition 15.D.1** (MWG, p. 534). The production of good 1 is relatively more intensive in
factor 1 than that of good 2: `a₁₁(w)/a₂₁(w) > a₁₂(w)/a₂₂(w)` at all factor prices `w ≫ 0`. -/
def TwoByTwo.FactorIntensity (M : TwoByTwo) : Prop :=
  ∀ w, StrictlyPositive w → M.a 1 w 0 / M.a 1 w 1 < M.a 0 w 0 / M.a 0 w 1

namespace TwoByTwo

variable {M : TwoByTwo}

theorem dot_two (u v : Fin 2 → ℝ) : u ⬝ᵥ v = u 0 * v 0 + u 1 * v 1 := by
  simp [dotProduct, Fin.sum_univ_two]

/-- The relative-price vector `(ω, 1)` is strictly positive for `ω > 0`. -/
theorem relPrice_pos {ω : ℝ} (hω : 0 < ω) : StrictlyPositive ![ω, 1] := fun l => by
  fin_cases l
  · exact hω
  · exact one_pos

/-- Factor intensity in determinant form: `a₁₁a₂₂ - a₁₂a₂₁ > 0`. -/
theorem FactorIntensity.det_pos (hM : M.IsModel) (hFI : M.FactorIntensity) {w : Fin 2 → ℝ}
    (hw : StrictlyPositive w) : 0 < M.a 0 w 0 * M.a 1 w 1 - M.a 1 w 0 * M.a 0 w 1 := by
  have h := hFI w hw
  have h01 := hM.a_pos 0 w 1 hw
  have h11 := hM.a_pos 1 w 1 hw
  rw [div_lt_div_iff₀ h11 h01] at h
  linarith

/-- The unit cost is positive. -/
theorem c_pos (hM : M.IsModel) (j : Fin 2) {w : Fin 2 → ℝ} (hw : StrictlyPositive w) :
    0 < M.c j w := by
  rw [c, dot_two]
  have := hM.a_pos j w 0 hw
  have := hM.a_pos j w 1 hw
  nlinarith [hw 0, hw 1]

/-- Cost minimization: `cⱼ(w') ≤ w'·aⱼ(w)` (the unit cost is concave with supergradient `aⱼ`). -/
theorem c_le (hM : M.IsModel) (j : Fin 2) {w w' : Fin 2 → ℝ} (hw : StrictlyPositive w)
    (hw' : StrictlyPositive w') : M.c j w' ≤ w' ⬝ᵥ M.a j w :=
  hM.a_min j w' hw' _ (hM.a_mem j w hw).1 (hM.a_mem j w hw).2.ge

/-- The unit cost is homogeneous of degree one: `cⱼ(t w) = t cⱼ(w)` for `t > 0`. -/
theorem c_smul (hM : M.IsModel) (j : Fin 2) {w : Fin 2 → ℝ} (hw : StrictlyPositive w) {t : ℝ}
    (ht : 0 < t) : M.c j (t • w) = t * M.c j w := by
  have htw : StrictlyPositive (t • w) := fun l => by simpa using mul_pos ht (hw l)
  apply le_antisymm
  · have := c_le hM j hw htw
    rw [smul_dotProduct, smul_eq_mul] at this
    exact this
  · have := c_le hM j htw hw
    unfold c at this ⊢
    simp only [smul_dotProduct, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left this ht.le

/-- The unit input vector is homogeneous of degree zero in factor prices. -/
theorem a_smul (hM : M.IsModel) (j : Fin 2) {w : Fin 2 → ℝ} (hw : StrictlyPositive w) {t : ℝ}
    (ht : 0 < t) : M.a j (t • w) = M.a j w := by
  have htw : StrictlyPositive (t • w) := fun l => by simpa using mul_pos ht (hw l)
  symm
  refine hM.a_unique j (t • w) htw _ (hM.a_mem j w hw).1 (hM.a_mem j w hw).2.ge ?_
  have h2 := c_smul hM j hw ht
  unfold c at h2
  rw [h2, smul_dotProduct, smul_eq_mul]

/-- The unit cost along relative prices: `gⱼ(ω) = cⱼ(ω, 1)`. -/
def g (M : TwoByTwo) (j : Fin 2) (ω : ℝ) : ℝ := M.c j ![ω, 1]

/-- `cⱼ(w) = w₂ gⱼ(w₁/w₂)`. -/
theorem c_eq_g (hM : M.IsModel) (j : Fin 2) {w : Fin 2 → ℝ} (hw : StrictlyPositive w) :
    M.c j w = w 1 * M.g j (w 0 / w 1) := by
  have h1 := hw 1
  have e : w = w 1 • ![w 0 / w 1, 1] := by
    funext l
    fin_cases l
    · simp; field_simp
    · simp
  rw [g, ← c_smul hM j (relPrice_pos (div_pos (hw 0) h1)) h1, ← e]

/-- `aⱼ(w) = aⱼ(w₁/w₂, 1)`. -/
theorem a_eq_rel (hM : M.IsModel) (j : Fin 2) {w : Fin 2 → ℝ} (hw : StrictlyPositive w) :
    M.a j w = M.a j ![w 0 / w 1, 1] := by
  have h1 := hw 1
  have e : w = w 1 • ![w 0 / w 1, 1] := by
    funext l
    fin_cases l
    · simp; field_simp
    · simp
  conv_lhs => rw [e]
  exact a_smul hM j (relPrice_pos (div_pos (hw 0) h1)) h1

/-- **Shephard's lemma along relative prices** (MWG, p. 532, Proposition 5.C.2): `gⱼ` is
differentiable with `gⱼ'(ω) = a_{1j}(ω, 1)`. -/
theorem unitCost_hasDerivAt (hM : M.IsModel) (j : Fin 2) {ω : ℝ} (hω : 0 < ω) :
    HasDerivAt (M.g j) (M.a j ![ω, 1] 0) ω := by
  have hcont : ContinuousAt (fun t : ℝ => M.a j ![t, 1] 0) ω :=
    (hM.a_cont j 0).continuousAt (Ioi_mem_nhds hω)
  -- `gⱼ(y) - gⱼ(ω) - (y - ω) aⱼ₁(ω)` lies between `(y - ω)(aⱼ₁(y) - aⱼ₁(ω))` and `0`
  refine hasDerivAt_of_sandwich (e₁ := fun y => (y - ω) * (M.a j ![y, 1] 0 - M.a j ![ω, 1] 0))
    (e₂ := fun _ => 0) ?_ (Asymptotics.isLittleO_zero _ _) ?_
  · have h0 : (fun y => M.a j ![y, 1] 0 - M.a j ![ω, 1] 0) =o[𝓝 ω] (fun _ => (1 : ℝ)) := by
      rw [Asymptotics.isLittleO_one_iff]
      have := hcont.tendsto.sub_const (M.a j ![ω, 1] 0)
      simpa using this
    have := h0.mul_isBigO (Asymptotics.isBigO_refl (fun y : ℝ => y - ω) (𝓝 ω))
    simpa [mul_comm] using this
  · filter_upwards [Ioi_mem_nhds hω] with y hy
    have hy' : StrictlyPositive ![y, 1] := relPrice_pos hy
    have hω' : StrictlyPositive ![ω, 1] := relPrice_pos hω
    have h1 := c_le hM j hω' hy'
    have h2 := c_le hM j hy' hω'
    simp only [g, c, dot_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h1 h2 ⊢
    constructor <;> nlinarith

/-- The unit cost `gⱼ` is continuous on `(0, ∞)`. -/
theorem g_continuousOn (hM : M.IsModel) (j : Fin 2) : ContinuousOn (M.g j) (Set.Ioi 0) :=
  fun _ hω => (unitCost_hasDerivAt hM j hω).continuousAt.continuousWithinAt

/-- `gⱼ(ω) = ω a_{1j}(ω, 1) + a_{2j}(ω, 1)`. -/
theorem g_eq (j : Fin 2) (ω : ℝ) :
    M.g j ω = ω * M.a j ![ω, 1] 0 + M.a j ![ω, 1] 1 := by
  simp only [g, c, dot_two, Matrix.cons_val_zero, Matrix.cons_val_one, one_mul]

/-- **Footnote 14** (MWG, p. 534). Under factor intensity the ratio `g₁(ω)/g₂(ω)` of unit costs is
strictly increasing in the relative factor price `ω = w₁/w₂`; hence the curves `c₁(w) = p₁` and
`c₂(w) = p₂` cross at most once. Its derivative is `(a₁₁a₂₂ - a₁₂a₂₁)/g₂² > 0`. -/
theorem unitCost_ratio_strictMono (hM : M.IsModel) (hFI : M.FactorIntensity) :
    StrictMonoOn (fun ω => M.g 0 ω / M.g 1 ω) (Set.Ioi 0) := by
  have hderiv : ∀ ω ∈ Set.Ioi (0 : ℝ), HasDerivAt (fun ω => M.g 0 ω / M.g 1 ω)
      ((M.a 0 ![ω, 1] 0 * M.g 1 ω - M.g 0 ω * M.a 1 ![ω, 1] 0) / M.g 1 ω ^ 2) ω := by
    intro ω hω
    exact (unitCost_hasDerivAt hM 0 hω).div (unitCost_hasDerivAt hM 1 hω)
      (c_pos hM 1 (relPrice_pos hω)).ne'
  refine strictMonoOn_of_deriv_pos (convex_Ioi 0) ?_ fun ω hω => ?_
  · exact fun ω hω => (hderiv ω hω).continuousAt.continuousWithinAt
  · rw [interior_Ioi] at hω
    rw [(hderiv ω hω).deriv]
    have hpos := (relPrice_pos hω)
    have hdet := hFI.det_pos hM hpos
    have hg1 := c_pos hM 1 hpos
    apply div_pos _ (pow_pos hg1 2)
    rw [g_eq, g_eq]
    nlinarith

/-- `g₂` is strictly increasing (its derivative is `a₁₂ > 0`). -/
theorem g_strictMono (hM : M.IsModel) (j : Fin 2) : StrictMonoOn (M.g j) (Set.Ioi 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioi 0) (g_continuousOn hM j) fun ω hω => ?_
  rw [interior_Ioi] at hω
  rw [(unitCost_hasDerivAt hM j hω).deriv]
  exact hM.a_pos j _ 0 (relPrice_pos hω)

/-- `ω/gⱼ(ω)` is strictly increasing (its derivative is `a_{2j}/gⱼ² > 0`). -/
theorem div_g_strictMono (hM : M.IsModel) (j : Fin 2) :
    StrictMonoOn (fun ω => ω / M.g j ω) (Set.Ioi 0) := by
  have hderiv : ∀ ω ∈ Set.Ioi (0 : ℝ), HasDerivAt (fun ω => ω / M.g j ω)
      ((1 * M.g j ω - ω * M.a j ![ω, 1] 0) / M.g j ω ^ 2) ω := fun ω hω =>
    (hasDerivAt_id ω).div (unitCost_hasDerivAt hM j hω) (c_pos hM j (relPrice_pos hω)).ne'
  refine strictMonoOn_of_deriv_pos (convex_Ioi 0)
    (fun ω hω => (hderiv ω hω).continuousAt.continuousWithinAt) fun ω hω => ?_
  rw [interior_Ioi] at hω
  rw [(hderiv ω hω).deriv]
  apply div_pos _ (pow_pos (c_pos hM j (relPrice_pos hω)) 2)
  rw [g_eq]
  have := hM.a_pos j ![ω, 1] 1 (relPrice_pos hω)
  linarith

/-- Revealed cost minimization: as the relative price `ω` of factor 1 rises, each firm uses less of
factor 1 relative to factor 2: `0 < ω ≤ ω'` implies `a_{1j}(ω')/a_{2j}(ω') ≤ a_{1j}(ω)/a_{2j}(ω)`
(MWG, p. 532). -/
theorem intensity_antitone (hM : M.IsModel) (j : Fin 2) {ω ω' : ℝ} (hω : 0 < ω) (hωω : ω ≤ ω') :
    M.a j ![ω', 1] 0 / M.a j ![ω', 1] 1 ≤ M.a j ![ω, 1] 0 / M.a j ![ω, 1] 1 := by
  have hp := relPrice_pos hω
  have hp' := relPrice_pos (lt_of_lt_of_le hω hωω)
  have h1 := c_le hM j hp' hp
  have h2 := c_le hM j hp hp'
  simp only [c, dot_two, Matrix.cons_val_zero, Matrix.cons_val_one, one_mul] at h1 h2
  have ha0 := hM.a_pos j ![ω, 1] 0 hp
  have ha1 := hM.a_pos j ![ω, 1] 1 hp
  have ha0' := hM.a_pos j ![ω', 1] 0 hp'
  have ha1' := hM.a_pos j ![ω', 1] 1 hp'
  rcases eq_or_lt_of_le hωω with h | h
  · rw [h]
  have hA0 : M.a j ![ω', 1] 0 ≤ M.a j ![ω, 1] 0 := by nlinarith
  have hA1 : M.a j ![ω, 1] 1 ≤ M.a j ![ω', 1] 1 := by nlinarith
  rw [div_le_div_iff₀ ha1' ha1]
  nlinarith

/-- **Section 15.D** (MWG, p. 534), constant returns. With `w ≫ 0`, `zⱼ` maximizes firm `j`'s profit
if and only if `pⱼ ≤ cⱼ(w)` and `zⱼ = qⱼ aⱼ(w)` for some `qⱼ ≥ 0` with `pⱼ = cⱼ(w)` if `qⱼ > 0`
(profits are zero at the optimum). -/
theorem crs_profitMax_iff (hM : M.IsModel) {p : Fin 2 → ℝ} {w : Fin 2 → ℝ}
    (hw : StrictlyPositive w) (j : Fin 2) (z : Fin 2 → ℝ) :
    IsOptimalInput M.f p w j z ↔ p j ≤ M.c j w ∧ ∃ q : ℝ, 0 ≤ q ∧ z = q • M.a j w ∧
      (0 < q → p j = M.c j w) := by
  have hf0 : M.f j 0 = 0 := by
    have := hM.hom j 0 (fun _ => le_refl _) 0 le_rfl
    simpa using this
  have ham := hM.a_mem j w hw
  constructor
  · rintro ⟨hz, hopt⟩
    have hq0 := hM.f_nonneg j z hz
    -- zero profit
    have hπle : p j * M.f j z - w ⬝ᵥ z ≤ 0 := by
      have h2z : (2 : ℝ) • z ∈ nonnegOrthant 2 := fun l => by simp; linarith [hz l]
      have := hopt _ h2z
      rw [hM.hom j z hz 2 (by norm_num), dotProduct_smul, smul_eq_mul] at this
      linarith
    have hπge : 0 ≤ p j * M.f j z - w ⬝ᵥ z := by
      have := hopt 0 (fun _ => le_refl _)
      simpa [hf0] using this
    have hpc : p j ≤ M.c j w := by
      have := hopt _ ham.1
      rw [ham.2] at this
      unfold c
      linarith
    refine ⟨hpc, M.f j z, hq0, ?_, fun hq => ?_⟩
    · rcases eq_or_lt_of_le hq0 with hq | hq
      · -- no output: no inputs
        have hwz : w ⬝ᵥ z ≤ 0 := by rw [← hq] at hπge; linarith
        have hz0 := eq_zero_of_dotProduct_nonpos hw hz hwz
        rw [← hq, zero_smul]
        exact hz0
      · have hz' : (M.f j z)⁻¹ • z ∈ nonnegOrthant 2 := fun l => by
          simp only [Pi.smul_apply, smul_eq_mul]; exact mul_nonneg (inv_nonneg.2 hq0) (hz l)
        have hf1 : 1 ≤ M.f j ((M.f j z)⁻¹ • z) := by
          rw [hM.hom j z hz _ (inv_nonneg.2 hq0), inv_mul_cancel₀ hq.ne']
        have hcost : w ⬝ᵥ ((M.f j z)⁻¹ • z) ≤ w ⬝ᵥ M.a j w := by
          rw [dotProduct_smul, smul_eq_mul]
          have : w ⬝ᵥ z = p j * M.f j z := by linarith
          rw [this, mul_comm (p j), ← mul_assoc, inv_mul_cancel₀ hq.ne', one_mul]
          exact hpc
        have := hM.a_unique j w hw _ hz' hf1 hcost
        rw [← this, smul_smul, mul_inv_cancel₀ hq.ne', one_smul]
    · have hf1 : 1 ≤ M.f j ((M.f j z)⁻¹ • z) := by
        rw [hM.hom j z hz _ (inv_nonneg.2 hq0), inv_mul_cancel₀ hq.ne']
      have hz' : (M.f j z)⁻¹ • z ∈ nonnegOrthant 2 := fun l => by
        simp only [Pi.smul_apply, smul_eq_mul]; exact mul_nonneg (inv_nonneg.2 hq0) (hz l)
      have := hM.a_min j w hw _ hz' hf1
      rw [dotProduct_smul, smul_eq_mul] at this
      have hwz : w ⬝ᵥ z = p j * M.f j z := by linarith
      rw [hwz, mul_comm (p j), ← mul_assoc, inv_mul_cancel₀ hq.ne', one_mul] at this
      exact le_antisymm hpc this
  · rintro ⟨hpc, q, hq, rfl, hqp⟩
    refine ⟨fun l => by simp only [Pi.smul_apply, smul_eq_mul]; exact mul_nonneg hq (ham.1 l),
      fun z' hz' => ?_⟩
    have hval : p j * M.f j (q • M.a j w) - w ⬝ᵥ (q • M.a j w) = 0 := by
      rw [hM.hom j _ ham.1 q hq, ham.2, dotProduct_smul, smul_eq_mul]
      rcases eq_or_lt_of_le hq with h | h
      · rw [← h]; ring
      · rw [hqp h]; unfold c; ring
    rw [hval]
    have hs := hM.f_nonneg j z' hz'
    rcases eq_or_lt_of_le hs with h | h
    · rw [← h, mul_zero, zero_sub, neg_nonpos]
      exact dotProduct_nonneg_of_nonneg (fun l => (hw l).le) hz'
    · have hz'' : (M.f j z')⁻¹ • z' ∈ nonnegOrthant 2 := fun l => by
        simp only [Pi.smul_apply, smul_eq_mul]; exact mul_nonneg (inv_nonneg.2 hs) (hz' l)
      have hf1 : 1 ≤ M.f j ((M.f j z')⁻¹ • z') := by
        rw [hM.hom j z' hz' _ (inv_nonneg.2 hs), inv_mul_cancel₀ h.ne']
      have := hM.a_min j w hw _ hz'' hf1
      rw [dotProduct_smul, smul_eq_mul] at this
      have h2 : M.f j z' * M.c j w ≤ w ⬝ᵥ z' := by
        unfold c
        have := mul_le_mul_of_nonneg_left this hs
        rwa [← mul_assoc, mul_inv_cancel₀ h.ne', one_mul] at this
      have h3 := mul_le_mul_of_nonneg_left hpc hs
      nlinarith

/-- **Exercise 15.D.6(a)** (MWG, p. 543). The equilibrium conditions allowing for specialization:
`(w, z)` is a factor market equilibrium if and only if `w ≫ 0` and there are outputs `q ≥ 0` with
`pⱼ ≤ cⱼ(w)` (equality if `qⱼ > 0`), `zⱼ = qⱼ aⱼ(w)` and full employment
`∑ⱼ qⱼ aⱼ(w) = z̄`. -/
theorem exercise_15_D_6a (hM : M.IsModel) (p zbar w : Fin 2 → ℝ) (z : Fin 2 → Fin 2 → ℝ) :
    IsFactorEqm M.f p zbar w z ↔ StrictlyPositive w ∧ ∃ q : Fin 2 → ℝ, (∀ j, 0 ≤ q j) ∧
      (∀ j, p j ≤ M.c j w) ∧ (∀ j, 0 < q j → p j = M.c j w) ∧ (∀ j, z j = q j • M.a j w) ∧
      ∑ j, q j • M.a j w = zbar := by
  constructor
  · rintro ⟨hw, hopt, hsum⟩
    have h := fun j => (crs_profitMax_iff hM hw j (z j)).1 (hopt j)
    choose hpc q hq hz hqp using h
    refine ⟨hw, q, hq, hpc, hqp, hz, ?_⟩
    rw [← hsum]
    exact Finset.sum_congr rfl fun j _ => (hz j).symm
  · rintro ⟨hw, q, hq, hpc, hqp, hz, hsum⟩
    refine ⟨hw, fun j => (crs_profitMax_iff hM hw j (z j)).2 ⟨hpc j, q j, hq j, hz j, hqp j⟩, ?_⟩
    rw [← hsum]
    exact Finset.sum_congr rfl fun j _ => hz j

/-- **(15.D.7) and (15.D.3)-(15.D.4)** (MWG, pp. 531, 534), constant returns: with `w ≫ 0` and
outputs `q ≫ 0`, the allocation `zⱼ = qⱼ aⱼ(w)` is an equilibrium if and only if every price equals
unit cost, `pⱼ = cⱼ(w)` (15.D.7), and the factor markets clear, `∑ⱼ qⱼ a_{ℓj}(w) = z̄_ℓ` (15.D.4,
with Shephard's lemma `∂cⱼ(w, qⱼ)/∂w_ℓ = qⱼ a_{ℓj}(w)`). -/
theorem interior_eqm_iff (hM : M.IsModel) {p zbar w : Fin 2 → ℝ} (hw : StrictlyPositive w)
    {q : Fin 2 → ℝ} (hq : ∀ j, 0 < q j) :
    IsFactorEqm M.f p zbar w (fun j => q j • M.a j w) ↔
      (∀ j, p j = M.c j w) ∧ ∑ j, q j • M.a j w = zbar := by
  rw [exercise_15_D_6a hM]
  constructor
  · rintro ⟨-, q', hq', hpc, hqp, hz, hsum⟩
    have hqq : ∀ j, q' j = q j := by
      intro j
      have := congrFun (hz j) 0
      simp only [Pi.smul_apply, smul_eq_mul] at this
      have ha := hM.a_pos j w 0 hw
      exact (mul_right_cancel₀ ha.ne' this).symm
    refine ⟨fun j => hqp j (by rw [hqq]; exact hq j), ?_⟩
    rw [← hsum]
    exact Finset.sum_congr rfl fun j _ => by rw [hqq]
  · rintro ⟨hpc, hsum⟩
    exact ⟨hw, q, fun j => (hq j).le, fun j => (hpc j).le, fun j _ => hpc j, fun j => rfl, hsum⟩

/-- **Figure 15.D.5** (MWG, p. 535). In an equilibrium with positive outputs each firm uses the
factors in the proportions `a_{1j}(w*)/a_{2j}(w*)`: `z*_{1j}/z*_{2j} = a_{1j}(w*)/a_{2j}(w*)`. -/
theorem interior_eqm_allocation (hM : M.IsModel) {p zbar w : Fin 2 → ℝ}
    {z : Fin 2 → Fin 2 → ℝ} (h : IsFactorEqm M.f p zbar w z) (j : Fin 2)
    (hq : 0 < M.f j (z j)) : z j 0 / z j 1 = M.a j w 0 / M.a j w 1 := by
  obtain ⟨hw, q, hq0, -, -, hz, -⟩ := (exercise_15_D_6a hM p zbar w z).1 h
  have hqpos : 0 < q j := by
    rcases eq_or_lt_of_le (hq0 j) with h0 | h0
    · rw [hz j, ← h0, zero_smul, show M.f j 0 = 0 by
        simpa using hM.hom j 0 (fun _ => le_refl _) 0 le_rfl] at hq
      exact absurd hq (lt_irrefl 0)
    · exact h0
  rw [hz j]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [mul_div_mul_left _ _ hqpos.ne']

/-- **Factor price equalization theorem** (MWG, p. 535). Under factor intensity, there is at most
one factor price vector `w ≫ 0` solving (15.D.7), `c₁(w) = p₁`, `c₂(w) = p₂`: interior
equilibrium factor prices depend only on the technologies and the output prices. -/
theorem factor_price_equalization (hM : M.IsModel) (hFI : M.FactorIntensity)
    {p w w' : Fin 2 → ℝ} (hw : StrictlyPositive w) (hw' : StrictlyPositive w')
    (h : ∀ j, M.c j w = p j) (h' : ∀ j, M.c j w' = p j) : w = w' := by
  have hω := div_pos (hw 0) (hw 1)
  have hω' := div_pos (hw' 0) (hw' 1)
  have hg0 : 0 < M.g 0 (w 0 / w 1) := c_pos hM 0 (relPrice_pos hω)
  have hg1 : 0 < M.g 1 (w 0 / w 1) := c_pos hM 1 (relPrice_pos hω)
  have hratio : M.g 0 (w 0 / w 1) / M.g 1 (w 0 / w 1) =
      M.g 0 (w' 0 / w' 1) / M.g 1 (w' 0 / w' 1) := by
    have e1 := c_eq_g hM 0 hw
    have e2 := c_eq_g hM 1 hw
    have e3 := c_eq_g hM 0 hw'
    have e4 := c_eq_g hM 1 hw'
    have hg1' : 0 < M.g 1 (w' 0 / w' 1) := c_pos hM 1 (relPrice_pos hω')
    rw [h 0] at e1; rw [h 1] at e2; rw [h' 0] at e3; rw [h' 1] at e4
    rw [div_eq_div_iff hg1.ne' hg1'.ne']
    have hw1 := hw 1
    have hw1' := hw' 1
    have : w 1 * M.g 0 (w 0 / w 1) * (w' 1 * M.g 1 (w' 0 / w' 1)) =
        w' 1 * M.g 0 (w' 0 / w' 1) * (w 1 * M.g 1 (w 0 / w 1)) := by
      rw [← e1, ← e4, ← e3, ← e2]
    have hpos : 0 < w 1 * w' 1 := mul_pos hw1 hw1'
    nlinarith
  have hωeq : w 0 / w 1 = w' 0 / w' 1 :=
    (unitCost_ratio_strictMono hM hFI).injOn hω hω' hratio
  have hw1eq : w 1 = w' 1 := by
    have e1 := c_eq_g hM 0 hw
    have e3 := c_eq_g hM 0 hw'
    rw [h 0] at e1
    rw [h' 0, ← hωeq] at e3
    have := e1.symm.trans e3
    exact mul_right_cancel₀ hg0.ne' this
  funext l
  fin_cases l
  · have := hωeq
    rw [hw1eq] at this
    exact (div_left_inj' (hw' 1).ne').1 this
  · exact hw1eq

/-- **Proposition 15.D.1** (Stolper-Samuelson theorem; MWG, p. 536), global form. Under factor
intensity, if `w` and `w'` are the (interior equilibrium) factor prices solving (15.D.7) at output
prices `p` and `p'` with `p'₁ > p₁` and `p'₂ = p₂`, then the price of factor 1 (used intensively
in good 1) rises and the price of factor 2 falls. -/
theorem proposition_15_D_1 (hM : M.IsModel) (hFI : M.FactorIntensity) {p p' w w' : Fin 2 → ℝ}
    (hw : StrictlyPositive w) (hw' : StrictlyPositive w') (h : ∀ j, M.c j w = p j)
    (h' : ∀ j, M.c j w' = p' j) (hp0 : p 0 < p' 0) (hp1 : p' 1 = p 1) :
    w 0 < w' 0 ∧ w' 1 < w 1 := by
  obtain ⟨ω, hωd⟩ : ∃ ω, ω = w 0 / w 1 := ⟨_, rfl⟩
  obtain ⟨ω', hωd'⟩ : ∃ ω', ω' = w' 0 / w' 1 := ⟨_, rfl⟩
  have hω : 0 < ω := by rw [hωd]; exact div_pos (hw 0) (hw 1)
  have hω' : 0 < ω' := by rw [hωd']; exact div_pos (hw' 0) (hw' 1)
  have e0 : p 0 = w 1 * M.g 0 ω := by rw [← h 0, c_eq_g hM 0 hw, hωd]
  have e1 : p 1 = w 1 * M.g 1 ω := by rw [← h 1, c_eq_g hM 1 hw, hωd]
  have e0' : p' 0 = w' 1 * M.g 0 ω' := by rw [← h' 0, c_eq_g hM 0 hw', hωd']
  have e1' : p 1 = w' 1 * M.g 1 ω' := by rw [← hp1, ← h' 1, c_eq_g hM 1 hw', hωd']
  have hg0 : 0 < M.g 0 ω := c_pos hM 0 (relPrice_pos hω)
  have hg1 : 0 < M.g 1 ω := c_pos hM 1 (relPrice_pos hω)
  have hg0' : 0 < M.g 0 ω' := c_pos hM 0 (relPrice_pos hω')
  have hg1' : 0 < M.g 1 ω' := c_pos hM 1 (relPrice_pos hω')
  have hw1 := hw 1
  have hw1' := hw' 1
  have hp1pos : 0 < p 1 := by rw [e1]; positivity
  have hp0pos : 0 < p 0 := by rw [e0]; positivity
  -- the relative factor price rises
  have hlt : ω < ω' := by
    have hmono := unitCost_ratio_strictMono hM hFI
    rw [← hmono.lt_iff_lt hω hω', div_lt_div_iff₀ hg1 hg1']
    have h1 : M.g 0 ω * M.g 1 ω' * (w 1 * w' 1) = p 0 * p 1 := by rw [e0, e1']; ring
    have h2 : M.g 0 ω' * M.g 1 ω * (w 1 * w' 1) = p' 0 * p 1 := by rw [e0', e1]; ring
    have : M.g 0 ω * M.g 1 ω' * (w 1 * w' 1) < M.g 0 ω' * M.g 1 ω * (w 1 * w' 1) := by
      rw [h1, h2]
      exact mul_lt_mul_of_pos_right hp0 hp1pos
    exact lt_of_mul_lt_mul_right this (by positivity)
  constructor
  · -- `w₁ = p₁ (ω/g₁(ω))` with `ω ↦ ω/g₁(ω)` increasing
    have hm := (div_g_strictMono hM 0).lt_iff_lt hω hω' |>.2 hlt
    have hw0 : w 0 = p 0 * (ω / M.g 0 ω) := by
      have : w 1 * M.g 0 ω * (ω / M.g 0 ω) = w 1 * ω := by field_simp
      rw [e0, this, hωd]; field_simp
    have hw0' : w' 0 = p' 0 * (ω' / M.g 0 ω') := by
      have : w' 1 * M.g 0 ω' * (ω' / M.g 0 ω') = w' 1 * ω' := by field_simp
      rw [e0', this, hωd']; field_simp
    rw [hw0, hw0']
    have : 0 < ω / M.g 0 ω := div_pos hω hg0
    have : ω / M.g 0 ω < ω' / M.g 0 ω' := hm
    nlinarith
  · -- `w₂ = p₂/g₂(ω)` with `g₂` increasing
    have hgm := (g_strictMono hM 1).lt_iff_lt hω hω' |>.2 hlt
    have hw1e : w 1 = p 1 / M.g 1 ω := by rw [e1]; field_simp
    have hw1e' : w' 1 = p 1 / M.g 1 ω' := by rw [e1']; field_simp
    rw [hw1e, hw1e']
    exact div_lt_div_of_pos_left hp1pos hg1 hgm

/-- **Exercise 15.D.3** (MWG, p. 543). In the setting of Proposition 15.D.1 the price of the
intensive factor rises proportionally more than the price of the good: `w'₁/w₁ > p'₁/p₁`. -/
theorem exercise_15_D_3 (hM : M.IsModel) (hFI : M.FactorIntensity) {p p' w w' : Fin 2 → ℝ}
    (hw : StrictlyPositive w) (hw' : StrictlyPositive w') (h : ∀ j, M.c j w = p j)
    (h' : ∀ j, M.c j w' = p' j) (hp0 : p 0 < p' 0) (hp1 : p' 1 = p 1) :
    p' 0 / p 0 < w' 0 / w 0 := by
  obtain ⟨ω, hωd⟩ : ∃ ω, ω = w 0 / w 1 := ⟨_, rfl⟩
  obtain ⟨ω', hωd'⟩ : ∃ ω', ω' = w' 0 / w' 1 := ⟨_, rfl⟩
  have hω : 0 < ω := by rw [hωd]; exact div_pos (hw 0) (hw 1)
  have hω' : 0 < ω' := by rw [hωd']; exact div_pos (hw' 0) (hw' 1)
  have hlt := proposition_15_D_1 hM hFI hw hw' h h' hp0 hp1
  have hωlt : ω < ω' := by
    rw [hωd, hωd', div_lt_div_iff₀ (hw 1) (hw' 1)]
    nlinarith [hw 0, hw' 1]
  have e0 : p 0 = w 1 * M.g 0 ω := by rw [← h 0, c_eq_g hM 0 hw, hωd]
  have e0' : p' 0 = w' 1 * M.g 0 ω' := by rw [← h' 0, c_eq_g hM 0 hw', hωd']
  have hg0 : 0 < M.g 0 ω := c_pos hM 0 (relPrice_pos hω)
  have hg0' : 0 < M.g 0 ω' := c_pos hM 0 (relPrice_pos hω')
  have hm : ω / M.g 0 ω < ω' / M.g 0 ω' := (div_g_strictMono hM 0).lt_iff_lt hω hω' |>.2 hωlt
  have hw1 := hw 1
  have hw1' := hw' 1
  have hw0 : w 0 = p 0 * (ω / M.g 0 ω) := by
    have : w 1 * M.g 0 ω * (ω / M.g 0 ω) = w 1 * ω := by field_simp
    rw [e0, this, hωd]; field_simp
  have hw0' : w' 0 = p' 0 * (ω' / M.g 0 ω') := by
    have : w' 1 * M.g 0 ω' * (ω' / M.g 0 ω') = w' 1 * ω' := by field_simp
    rw [e0', this, hωd']; field_simp
  have hp0pos : 0 < p 0 := by rw [e0]; positivity
  have hp0' : 0 < p' 0 := by linarith
  have hr : 0 < ω / M.g 0 ω := div_pos hω hg0
  have hr' : 0 < ω' / M.g 0 ω' := div_pos hω' hg0'
  rw [hw0, hw0', div_lt_div_iff₀ hp0pos (mul_pos hp0pos hr)]
  nlinarith [mul_pos hp0' hp0pos]

/-- **Exercise 15.D.3** (MWG, p. 543). A consumer who owns one unit of the intensive factor only is
strictly better off after the price increase, whatever his (locally nonsatiated) preferences:
every bundle affordable before is strictly inside the new budget set, so some bundle affordable
afterwards is strictly preferred. -/
theorem exercise_15_D_3_welfare (hM : M.IsModel) (hFI : M.FactorIntensity)
    {p p' w w' : Fin 2 → ℝ} (hw : StrictlyPositive w) (hw' : StrictlyPositive w')
    (h : ∀ j, M.c j w = p j) (h' : ∀ j, M.c j w' = p' j) (hp0 : p 0 < p' 0) (hp1 : p' 1 = p 1)
    {u : (Fin 2 → ℝ) → ℝ} (hlns : UtilityLNS u) {x : Fin 2 → ℝ}
    (hx : x ∈ budgetSet p (w 0)) : ∃ y ∈ budgetSet p' (w' 0), u x < u y := by
  have hmag := exercise_15_D_3 hM hFI hw hw' h h' hp0 hp1
  have hp0pos : 0 < p 0 := by
    rw [← h 0]; exact c_pos hM 0 hw
  have hp1pos : 0 < p 1 := by
    rw [← h 1]; exact c_pos hM 1 hw
  have hb := hx.2
  rw [dot_two] at hb
  have hx0 := hx.1 0
  have hx1 := hx.1 1
  have hcost : p' ⬝ᵥ x < w' 0 := by
    rw [dot_two, hp1]
    rw [div_lt_div_iff₀ hp0pos (hw 0)] at hmag
    have h1 : p' 0 * x 0 + p 1 * x 1 ≤ p' 0 / p 0 * (p 0 * x 0 + p 1 * x 1) := by
      rw [mul_add, ← mul_assoc, div_mul_cancel₀ _ hp0pos.ne']
      have : p 1 * x 1 ≤ p' 0 / p 0 * (p 1 * x 1) := by
        have : 1 ≤ p' 0 / p 0 := by rw [le_div_iff₀ hp0pos]; linarith
        nlinarith [mul_nonneg hp1pos.le hx1]
      linarith
    have h2 : p' 0 / p 0 * (p 0 * x 0 + p 1 * x 1) ≤ p' 0 / p 0 * w 0 :=
      mul_le_mul_of_nonneg_left hb (div_nonneg (by linarith) hp0pos.le)
    have h3 : p' 0 / p 0 * w 0 < w' 0 := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ hp0pos]
      linarith
    linarith
  obtain ⟨y, hy, hpy, hu⟩ := hlns.exists_better p' hx.1 hcost
  exact ⟨y, ⟨hy, hpy.le⟩, hu⟩

/-- **Proposition 15.D.1** (MWG, pp. 536-537), the book's differential proof. With
`A = [[a₁₁, a₂₁], [a₁₂, a₂₂]]` (rows: `dpⱼ = ∇cⱼ·dw`) and `|A| = a₁₁a₂₂ - a₁₂a₂₁ > 0` (factor
intensity), `A⁻¹ = |A|⁻¹ [[a₂₂, -a₂₁], [-a₁₂, a₁₁]]` has positive diagonal and negative off-diagonal
entries, and the response to `dp = (1, 0)` is `dw = (a₂₂/|A|, -a₁₂/|A|)`, so `dw₁ > 0 > dw₂`. -/
theorem proposition_15_D_1_differential {a₁₁ a₂₁ a₁₂ a₂₂ : ℝ} (h₁₂ : 0 < a₁₂) (h₂₂ : 0 < a₂₂)
    (hdet : 0 < a₁₁ * a₂₂ - a₁₂ * a₂₁) :
    !![a₁₁, a₂₁; a₁₂, a₂₂] * ((a₁₁ * a₂₂ - a₁₂ * a₂₁)⁻¹ • !![a₂₂, -a₂₁; -a₁₂, a₁₁]) = 1 ∧
      (∀ dw₁ dw₂ : ℝ, (a₁₁ * dw₁ + a₂₁ * dw₂ = 1 ∧ a₁₂ * dw₁ + a₂₂ * dw₂ = 0) ↔
        (dw₁ = a₂₂ / (a₁₁ * a₂₂ - a₁₂ * a₂₁) ∧ dw₂ = -a₁₂ / (a₁₁ * a₂₂ - a₁₂ * a₂₁))) ∧
      0 < a₂₂ / (a₁₁ * a₂₂ - a₁₂ * a₂₁) ∧ -a₁₂ / (a₁₁ * a₂₂ - a₁₂ * a₂₁) < 0 := by
  have hD := hdet.ne'
  refine ⟨?_, fun dw₁ dw₂ => ⟨fun ⟨e1, e2⟩ => ⟨?_, ?_⟩, fun ⟨e1, e2⟩ => ⟨?_, ?_⟩⟩, by positivity,
    div_neg_of_neg_of_pos (by linarith) hdet⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring
  · rw [eq_div_iff hD]; linear_combination a₂₂ * e1 - a₂₁ * e2
  · rw [eq_div_iff hD]; linear_combination -a₁₂ * e1 + a₁₁ * e2
  · rw [e1, e2]; field_simp; ring
  · rw [e1, e2]; field_simp; ring

/-- The outputs supporting an interior allocation at given factor prices solve
`∑ⱼ qⱼ aⱼ = z̄` (Cramer's rule): `q₁ = (a₂₂z̄₁ - a₁₂z̄₂)/|A|`, `q₂ = (a₁₁z̄₂ - a₂₁z̄₁)/|A|`. -/
theorem outputs_cramer {a : Fin 2 → Fin 2 → ℝ} {q zbar : Fin 2 → ℝ}
    (hD : a 0 0 * a 1 1 - a 1 0 * a 0 1 ≠ 0) (h : ∑ j, q j • a j = zbar) :
    q 0 = (a 1 1 * zbar 0 - a 1 0 * zbar 1) / (a 0 0 * a 1 1 - a 1 0 * a 0 1) ∧
      q 1 = (a 0 0 * zbar 1 - a 0 1 * zbar 0) / (a 0 0 * a 1 1 - a 1 0 * a 0 1) := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h0 h1
  constructor
  · rw [eq_div_iff hD, ← h0, ← h1]; ring
  · rw [eq_div_iff hD, ← h0, ← h1]; ring

/-- **Proposition 15.D.2** (Rybczynski theorem; MWG, p. 537). Under factor intensity, compare
interior equilibria (`q ≫ 0`, `q' ≫ 0`) at the same output prices with endowments `z̄` and
`z̄' = z̄ + (δ, 0)`, `δ > 0`: the output of good 1 (intensive in factor 1) rises and that of good 2
falls. -/
theorem proposition_15_D_2 (hM : M.IsModel) (hFI : M.FactorIntensity)
    {p zbar w w' q q' : Fin 2 → ℝ} {δ : ℝ} (hδ : 0 < δ) (hw : StrictlyPositive w)
    (hw' : StrictlyPositive w') (hq : ∀ j, 0 < q j) (hq' : ∀ j, 0 < q' j)
    (h : IsFactorEqm M.f p zbar w (fun j => q j • M.a j w))
    (h' : IsFactorEqm M.f p (zbar + ![δ, 0]) w' (fun j => q' j • M.a j w')) :
    q 0 < q' 0 ∧ q' 1 < q 1 := by
  obtain ⟨hpc, hsum⟩ := (interior_eqm_iff hM hw hq).1 h
  obtain ⟨hpc', hsum'⟩ := (interior_eqm_iff hM hw' hq').1 h'
  have hww : w = w' := factor_price_equalization hM hFI hw hw' (fun j => (hpc j).symm)
    (fun j => (hpc' j).symm)
  subst hww
  have hdet := hFI.det_pos hM hw
  obtain ⟨c0, c1⟩ := outputs_cramer (a := fun j => M.a j w) hdet.ne' hsum
  obtain ⟨c0', c1'⟩ := outputs_cramer (a := fun j => M.a j w) hdet.ne' hsum'
  simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, add_zero] at c0' c1'
  have ha11 := hM.a_pos 1 w 1 hw
  have ha01 := hM.a_pos 0 w 1 hw
  constructor
  · rw [c0, c0', div_lt_div_iff_of_pos_right hdet]
    nlinarith
  · rw [c1, c1', div_lt_div_iff_of_pos_right hdet]
    nlinarith

/-- **Exercise 15.D.5** (MWG, p. 543). In the Rybczynski setting the output of good 1 rises
proportionally more than the endowment of factor 1: `q'₁/q₁ > z̄'₁/z̄₁`. -/
theorem exercise_15_D_5 (hM : M.IsModel) (hFI : M.FactorIntensity)
    {p zbar w w' q q' : Fin 2 → ℝ} {δ : ℝ} (hδ : 0 < δ) (hw : StrictlyPositive w)
    (hw' : StrictlyPositive w') (hq : ∀ j, 0 < q j) (hq' : ∀ j, 0 < q' j)
    (h : IsFactorEqm M.f p zbar w (fun j => q j • M.a j w))
    (h' : IsFactorEqm M.f p (zbar + ![δ, 0]) w' (fun j => q' j • M.a j w')) :
    (zbar 0 + δ) / zbar 0 < q' 0 / q 0 := by
  obtain ⟨hpc, hsum⟩ := (interior_eqm_iff hM hw hq).1 h
  obtain ⟨hpc', hsum'⟩ := (interior_eqm_iff hM hw' hq').1 h'
  have hww : w = w' := factor_price_equalization hM hFI hw hw' (fun j => (hpc j).symm)
    (fun j => (hpc' j).symm)
  subst hww
  have hdet := hFI.det_pos hM hw
  obtain ⟨c0, -⟩ := outputs_cramer (a := fun j => M.a j w) hdet.ne' hsum
  obtain ⟨c0', -⟩ := outputs_cramer (a := fun j => M.a j w) hdet.ne' hsum'
  simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, add_zero] at c0'
  have hz := congrFun hsum 0
  have hz1 := congrFun hsum 1
  simp only [Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hz hz1
  have hz0pos : 0 < zbar 0 := by
    rw [← hz]
    have := hM.a_pos 0 w 0 hw
    have := hM.a_pos 1 w 0 hw
    nlinarith [hq 0, hq 1]
  have hz1pos : 0 < zbar 1 := by
    rw [← hz1]
    have := hM.a_pos 0 w 1 hw
    have := hM.a_pos 1 w 1 hw
    nlinarith [hq 0, hq 1]
  have ha10 := hM.a_pos 1 w 0 hw
  rw [div_lt_div_iff₀ hz0pos (hq 0), c0, c0']
  rw [div_mul_eq_mul_div, mul_div_assoc', div_lt_div_iff_of_pos_right hdet]
  nlinarith [mul_pos (mul_pos ha10 hz1pos) hδ]

/-- **Exercise 15.D.6(b)** and **footnote 15** (MWG, pp. 535, 543). Let `ŵ ≫ 0` solve (15.D.7),
`cⱼ(ŵ) = pⱼ`, let `z̄ ≫ 0`, and let `w` with outputs `q` satisfy the equilibrium conditions of
Exercise 15.D.6(a). Under factor
intensity both outputs are positive if and only if `z̄` lies in the diversification cone,
`a₁₂(ŵ)/a₂₂(ŵ) < z̄₁/z̄₂ < a₁₁(ŵ)/a₂₁(ŵ)`. -/
theorem exercise_15_D_6b (hM : M.IsModel) (hFI : M.FactorIntensity) {p zbar w what : Fin 2 → ℝ}
    {q : Fin 2 → ℝ} (hwhat : StrictlyPositive what)
    (hc : ∀ j, M.c j what = p j) (hz : StrictlyPositive zbar)
    (hq : ∀ j, 0 ≤ q j) (hpc : ∀ j, p j ≤ M.c j w) (hqp : ∀ j, 0 < q j → p j = M.c j w)
    (hw : StrictlyPositive w) (hsum : ∑ j, q j • M.a j w = zbar) :
    (∀ j, 0 < q j) ↔ M.a 1 what 0 / M.a 1 what 1 < zbar 0 / zbar 1 ∧
      zbar 0 / zbar 1 < M.a 0 what 0 / M.a 0 what 1 := by
  have hz0 := congrFun hsum 0
  have hz1 := congrFun hsum 1
  simp only [Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hz0 hz1
  constructor
  · intro hqpos
    have hww : w = what := factor_price_equalization hM hFI hw hwhat
      (fun j => (hqp j (hqpos j)).symm) hc
    subst hww
    have a00 := hM.a_pos 0 w 0 hw
    have a01 := hM.a_pos 0 w 1 hw
    have a10 := hM.a_pos 1 w 0 hw
    have a11 := hM.a_pos 1 w 1 hw
    have hdet := hFI.det_pos hM hw
    have hq0 := hqpos 0
    have hq1 := hqpos 1
    rw [← hz0, ← hz1]
    constructor
    · rw [div_lt_div_iff₀ a11 (by positivity)]
      nlinarith [mul_pos hq0 hdet]
    · rw [div_lt_div_iff₀ (by positivity) a01]
      nlinarith [mul_pos hq1 hdet]
  · rintro ⟨hlo, hhi⟩
    have hω := div_pos (hw 0) (hw 1)
    have hωh := div_pos (hwhat 0) (hwhat 1)
    have hratio := unitCost_ratio_strictMono hM hFI
    have eg : ∀ j, M.c j w = w 1 * M.g j (w 0 / w 1) := fun j => c_eq_g hM j hw
    have egh : ∀ j, M.c j what = what 1 * M.g j (what 0 / what 1) := fun j => c_eq_g hM j hwhat
    have hgpos : ∀ j, 0 < M.g j (w 0 / w 1) := fun j => c_pos hM j (relPrice_pos hω)
    have hghpos : ∀ j, 0 < M.g j (what 0 / what 1) := fun j => c_pos hM j (relPrice_pos hωh)
    have hrel : M.a 0 w = M.a 0 ![w 0 / w 1, 1] ∧ M.a 1 w = M.a 1 ![w 0 / w 1, 1] :=
      ⟨a_eq_rel hM 0 hw, a_eq_rel hM 1 hw⟩
    have hrelh : M.a 0 what = M.a 0 ![what 0 / what 1, 1] ∧
        M.a 1 what = M.a 1 ![what 0 / what 1, 1] :=
      ⟨a_eq_rel hM 0 hwhat, a_eq_rel hM 1 hwhat⟩
    by_contra hnot
    simp only [not_forall, not_lt] at hnot
    obtain ⟨j, hj⟩ := hnot
    have hqj : q j = 0 := le_antisymm hj (hq j)
    fin_cases j
    · -- specialization in good 2: `z̄ = q₂ a₂(w)`, `c₂(w) = p₂`, `c₁(w) ≥ p₁`
      have hq1 : 0 < q 1 := by
        rcases eq_or_lt_of_le (hq 1) with h | h
        · exfalso
          simp only [Fin.zero_eta] at hqj
          rw [hqj, ← h] at hz0
          simp at hz0
          linarith [hz 0]
        · exact h
      have hp1 := hqp 1 hq1
      have hp0 := hpc 0
      -- the relative factor price is at least `ŵ₁/ŵ₂`
      have hge : what 0 / what 1 ≤ w 0 / w 1 := by
        by_contra hlt
        rw [not_le] at hlt
        have := (hratio.lt_iff_lt hω hωh).2 hlt
        rw [div_lt_div_iff₀ (hgpos 1) (hghpos 1)] at this
        have h1 := hc 0
        have h2 := hc 1
        rw [egh 0] at h1
        rw [egh 1] at h2
        rw [eg 1] at hp1
        rw [eg 0] at hp0
        have hw1 := hw 1
        have hwh1 := hwhat 1
        have key := mul_lt_mul_of_pos_left this (mul_pos hwh1 hw1)
        have key2 : (w 1 * M.g 0 (w 0 / w 1)) * (what 1 * M.g 1 (what 0 / what 1)) <
            (what 1 * M.g 0 (what 0 / what 1)) * (w 1 * M.g 1 (w 0 / w 1)) := by
          linarith [key]
        rw [h1, h2, ← hp1] at key2
        have hp1pos : 0 < p 1 := by rw [← h2]; exact mul_pos hwh1 (hghpos 1)
        have := lt_of_mul_lt_mul_right key2 hp1pos.le
        linarith
      have hint := intensity_antitone hM 1 hωh hge
      rw [← hrel.2, ← hrelh.2] at hint
      simp only [Fin.zero_eta] at hqj
      rw [hqj, zero_mul, zero_add] at hz0 hz1
      have : zbar 0 / zbar 1 = M.a 1 w 0 / M.a 1 w 1 := by
        rw [← hz0, ← hz1, mul_div_mul_left _ _ hq1.ne']
      linarith
    · -- specialization in good 1
      have hq0 : 0 < q 0 := by
        rcases eq_or_lt_of_le (hq 0) with h | h
        · exfalso
          simp only [Fin.mk_one] at hqj
          rw [hqj, ← h] at hz0
          simp at hz0
          linarith [hz 0]
        · exact h
      have hp0 := hqp 0 hq0
      have hp1 := hpc 1
      have hle : w 0 / w 1 ≤ what 0 / what 1 := by
        by_contra hlt
        rw [not_le] at hlt
        have := (hratio.lt_iff_lt hωh hω).2 hlt
        rw [div_lt_div_iff₀ (hghpos 1) (hgpos 1)] at this
        have h1 := hc 0
        have h2 := hc 1
        rw [egh 0] at h1
        rw [egh 1] at h2
        rw [eg 0] at hp0
        rw [eg 1] at hp1
        have hw1 := hw 1
        have hwh1 := hwhat 1
        have key := mul_lt_mul_of_pos_left this (mul_pos hwh1 hw1)
        have key2 : (what 1 * M.g 0 (what 0 / what 1)) * (w 1 * M.g 1 (w 0 / w 1)) <
            (w 1 * M.g 0 (w 0 / w 1)) * (what 1 * M.g 1 (what 0 / what 1)) := by
          linarith [key]
        rw [h1, h2, ← hp0] at key2
        have hp0pos : 0 < p 0 := by rw [← h1]; exact mul_pos hwh1 (hghpos 0)
        have := lt_of_mul_lt_mul_left key2 hp0pos.le
        linarith
      have hint := intensity_antitone hM 0 hω hle
      rw [← hrel.1, ← hrelh.1] at hint
      simp only [Fin.mk_one] at hqj
      rw [hqj, zero_mul, add_zero] at hz0 hz1
      have : zbar 0 / zbar 1 = M.a 0 w 0 / M.a 0 w 1 := by
        rw [← hz0, ← hz1, mul_div_mul_left _ _ hq0.ne']
      linarith

end TwoByTwo

/-- An instance of the 2 × 2 model: Leontief technologies `f₁(z) = min(z₁/2, z₂)`,
`f₂(z) = min(z₁, z₂/2)` with unit input vectors `a₁ = (2, 1)` and `a₂ = (1, 2)`. -/
noncomputable def leontiefModel : TwoByTwo where
  f := ![fun z => min (z 0 / 2) (z 1), fun z => min (z 0) (z 1 / 2)]
  a := fun j _ => ![![2, 1], ![1, 2]] j

/-- The Leontief model satisfies the standing assumptions of the 2 × 2 model. -/
theorem leontiefModel_isModel : leontiefModel.IsModel where
  f_nonneg := by
    intro j z hz
    fin_cases j
    · exact le_min (by linarith [hz 0]) (hz 1)
    · exact le_min (hz 0) (by linarith [hz 1])
  hom := by
    intro j z _ t ht
    fin_cases j
    · change min (t * z 0 / 2) (t * z 1) = t * min (z 0 / 2) (z 1)
      rw [mul_min_of_nonneg _ _ ht, mul_div_assoc]
    · change min (t * z 0) (t * z 1 / 2) = t * min (z 0) (z 1 / 2)
      rw [mul_min_of_nonneg _ _ ht, mul_div_assoc]
  a_mem := by
    intro j w _
    fin_cases j
    · refine ⟨fun l => by fin_cases l <;> norm_num [leontiefModel], ?_⟩
      norm_num [leontiefModel]
    · refine ⟨fun l => by fin_cases l <;> norm_num [leontiefModel], ?_⟩
      norm_num [leontiefModel]
  a_min := by
    intro j w hw z _ hz
    have hw0 := hw 0
    have hw1 := hw 1
    fin_cases j
    · change 1 ≤ min (z 0 / 2) (z 1) at hz
      rw [le_min_iff] at hz
      simp [leontiefModel, Matrix.vecHead, Matrix.vecTail]
      nlinarith [hz.1, hz.2]
    · change 1 ≤ min (z 0) (z 1 / 2) at hz
      rw [le_min_iff] at hz
      simp [leontiefModel, Matrix.vecHead, Matrix.vecTail]
      nlinarith [hz.1, hz.2]
  a_unique := by
    intro j w hw z _ hz hle
    have hw0 := hw 0
    have hw1 := hw 1
    fin_cases j
    · change 1 ≤ min (z 0 / 2) (z 1) at hz
      rw [le_min_iff] at hz
      simp [leontiefModel, Matrix.vecHead, Matrix.vecTail] at hle
      have e0 : z 0 = 2 := by nlinarith [hz.1, hz.2]
      have e1 : z 1 = 1 := by nlinarith [hz.1, hz.2]
      funext l
      fin_cases l
      · simpa [leontiefModel] using e0
      · simpa [leontiefModel] using e1
    · change 1 ≤ min (z 0) (z 1 / 2) at hz
      rw [le_min_iff] at hz
      simp [leontiefModel, Matrix.vecHead, Matrix.vecTail] at hle
      have e0 : z 0 = 1 := by nlinarith [hz.1, hz.2]
      have e1 : z 1 = 2 := by nlinarith [hz.1, hz.2]
      funext l
      fin_cases l
      · simpa [leontiefModel] using e0
      · simpa [leontiefModel] using e1
  a_pos := by
    intro j w l _
    fin_cases j <;> fin_cases l <;> norm_num [leontiefModel]
  a_cont := fun _ _ => continuousOn_const

/-- The Leontief model satisfies the factor intensity condition: `2/1 > 1/2`. -/
theorem leontiefModel_factorIntensity : leontiefModel.FactorIntensity := by
  intro w _
  norm_num [leontiefModel]

/-- Non-vacuity of Propositions 15.D.1-15.D.2 in the Leontief model: `w = (1, 1)` solves (15.D.7)
at `p = (3, 3)`, `w' = (5/3, 2/3)` at `p' = (4, 3)` (Stolper-Samuelson: `w₁` rises, `w₂` falls),
and at `w = (1, 1)` the endowments `(3, 3)` and `(4, 3)` are produced with outputs `(1, 1)` and
`(5/3, 2/3)` (Rybczynski: `q₁` rises, `q₂` falls). -/
theorem leontief_instances :
    (∀ j, leontiefModel.c j ![1, 1] = ![3, 3] j) ∧
      (∀ j, leontiefModel.c j ![5 / 3, 2 / 3] = ![4, 3] j) ∧
      IsFactorEqm leontiefModel.f ![3, 3] ![3, 3] ![1, 1]
        (fun j => (![1, 1] : Fin 2 → ℝ) j • leontiefModel.a j ![1, 1]) ∧
      IsFactorEqm leontiefModel.f ![3, 3] (![3, 3] + ![1, 0]) ![1, 1]
        (fun j => (![5 / 3, 2 / 3] : Fin 2 → ℝ) j • leontiefModel.a j ![1, 1]) := by
  have hc1 : ∀ j, leontiefModel.c j ![1, 1] = ![3, 3] j := by
    intro j; fin_cases j <;> norm_num [TwoByTwo.c, leontiefModel, TwoByTwo.dot_two]
  have hw : StrictlyPositive (![1, 1] : Fin 2 → ℝ) := fun l => by fin_cases l <;> norm_num
  refine ⟨hc1, ?_, ?_, ?_⟩
  · intro j; fin_cases j <;> norm_num [TwoByTwo.c, leontiefModel, TwoByTwo.dot_two]
  · refine (TwoByTwo.interior_eqm_iff (p := ![3, 3]) (zbar := ![3, 3]) (q := ![1, 1])
      leontiefModel_isModel hw
      (fun j => by fin_cases j <;> norm_num)).2 ⟨fun j => (hc1 j).symm, ?_⟩
    funext l
    fin_cases l <;> norm_num [leontiefModel, Fin.sum_univ_two]
  · refine (TwoByTwo.interior_eqm_iff (p := ![3, 3]) (zbar := ![3, 3] + ![1, 0])
      (q := ![5 / 3, 2 / 3]) leontiefModel_isModel hw
      (fun j => by fin_cases j <;> norm_num)).2 ⟨fun j => (hc1 j).symm, ?_⟩
    funext l
    fin_cases l <;> norm_num [leontiefModel, Fin.sum_univ_two]

end MWG.GeneralEquilibriumExamples
