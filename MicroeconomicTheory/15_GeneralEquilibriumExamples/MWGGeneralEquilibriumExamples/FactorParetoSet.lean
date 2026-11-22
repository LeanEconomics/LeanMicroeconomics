/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGGeneralEquilibriumExamples.CobbDouglasTwoByTwo
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# The Pareto set of factor allocations; Exercise 15.D.1 and footnote 16 (MWG pp. 532-536)

In the 2 × 2 production model (`TwoByTwo`) with total factor endowment `z̄`:

* p. 533, Figure 15.D.2(b): a factor allocation (`IsFactorAllocation`) is *efficient*
  (`TwoByTwo.IsEfficientAllocation`, the Pareto set) if no other allocation of `z̄` produces at
  least as much of both goods and more of one. An allocation is *supported*
  (`TwoByTwo.IsSupportedBy`, `TwoByTwo.IsSupportedAllocation`) if `zⱼ = qⱼ aⱼ(w)` for common
  factor prices `w ≫ 0` (the book's tangency of the isoquants). Supported allocations are efficient
  (`TwoByTwo.supported_isEfficient`); conversely, with ray-surjective technologies that are
  differentiable along rays, every efficient allocation with `zⱼ ≫ 0` is supported
  (`TwoByTwo.efficient_isSupported`).
* **Exercise 15.D.1(a)** and the claim of p. 533: along the interior supported allocations of a
  given `z̄` the intensity ranking `r₀ = a₁₁/a₂₁` versus `r₁ = a₁₂/a₂₂` never flips
  (`TwoByTwo.factorRatio_order_preserved`, `TwoByTwo.exercise_15_D_1a`); if one interior
  supported allocation lies on the diagonal of the Edgeworth box, every interior point of the
  diagonal is supported with the same factor prices and every interior supported allocation is
  on the diagonal (`TwoByTwo.diagonal_pareto_set`). For smooth technologies these are
  statements about the Pareto set itself (`TwoByTwo.exercise_15_D_1a_pareto`).
* **Exercise 15.D.1(b)**: false as printed in this generality. In the Leontief model a ray from
  firm 1's origin meets the Pareto set twice, and the Pareto set is not the diagonal
  (`exercise_15_D_1b_counterexample`). Corrected statement: when the technologies are
  differentiable along rays the factor intensities are strictly decreasing in `w₁/w₂`
  (`TwoByTwo.relRatio_strictAnti`), along the interior supported allocations with `r₀ > r₁`
  a higher relative factor price means lower intensities in both firms and strictly more of both
  factors for firm 1 (`TwoByTwo.exercise_15_D_1b_monotone`), and a ray from either origin meets
  the interior supported allocations at most once (`TwoByTwo.exercise_15_D_1b`); instance
  `exercise_15_D_1b_cdModel`.
* **Footnote 16** (p. 536): the Stolper-Samuelson conclusion holds without the global factor
  intensity condition when firm 1 is more intensive in factor 1 at the initial interior
  equilibrium (`TwoByTwo.footnote_16`; instance `footnote_16_leontief`).
-/

namespace MWG.GeneralEquilibriumExamples

open MWG.ConsumerChoice Filter Topology

/-- **Figure 15.D.2** (MWG, pp. 532-533). A factor allocation of the endowment `z̄` between the two
firms: `zⱼ ∈ ℝ²₊` are the inputs of firm `j` and `z₀ + z₁ = z̄` (a point of the Edgeworth box). -/
def IsFactorAllocation (zbar : Fin 2 → ℝ) (z : Fin 2 → Fin 2 → ℝ) : Prop :=
  (∀ j, z j ∈ nonnegOrthant 2) ∧ z 0 + z 1 = zbar

/-- **Figure 15.D.2(b)** (MWG, p. 533). The Pareto set of factor allocations: allocations of `z̄`
at which it is not possible to produce more of one good without producing less of the other. -/
def TwoByTwo.IsEfficientAllocation (M : TwoByTwo) (zbar : Fin 2 → ℝ) (z : Fin 2 → Fin 2 → ℝ) :
    Prop :=
  IsFactorAllocation zbar z ∧ ¬ ∃ z', IsFactorAllocation zbar z' ∧
    (∀ j, M.f j (z j) ≤ M.f j (z' j)) ∧ ∃ j, M.f j (z j) < M.f j (z' j)

/-- **Section 15.D** (MWG, p. 533). The allocation `z` of `z̄` is supported by the factor prices
`w ≫ 0` with outputs `q ≥ 0`: `zⱼ = qⱼ aⱼ(w)` (both firms minimize costs at the same factor
prices, the tangency of the isoquants in Figure 15.D.2(b)). -/
def TwoByTwo.IsSupportedBy (M : TwoByTwo) (zbar w q : Fin 2 → ℝ) (z : Fin 2 → Fin 2 → ℝ) :
    Prop :=
  StrictlyPositive w ∧ (∀ j, 0 ≤ q j) ∧ (∀ j, z j = q j • M.a j w) ∧ z 0 + z 1 = zbar

/-- **Section 15.D** (MWG, p. 533). The allocation `z` of `z̄` is supported by some factor prices
`w ≫ 0`. -/
def TwoByTwo.IsSupportedAllocation (M : TwoByTwo) (zbar : Fin 2 → ℝ) (z : Fin 2 → Fin 2 → ℝ) :
    Prop :=
  ∃ w q, M.IsSupportedBy zbar w q z

/-- **Exercise 15.D.1** (MWG, p. 533). An interior supported allocation: factor prices `w ≫ 0` and
outputs `q ≫ 0` with `q₀ a₀(w) + q₁ a₁(w) = z̄` (the allocation is `zⱼ = qⱼ aⱼ(w)`). -/
def TwoByTwo.IsInteriorSupport (M : TwoByTwo) (zbar w q : Fin 2 → ℝ) : Prop :=
  StrictlyPositive w ∧ (∀ j, 0 < q j) ∧ q 0 • M.a 0 w + q 1 • M.a 1 w = zbar

/-- **Exercise 15.D.1** (MWG, p. 533). The factor intensity of firm `j` at factor prices `w`: its
use of factor 1 relative to factor 2, `a_{1j}(w)/a_{2j}(w)`. -/
noncomputable def TwoByTwo.factorRatio (M : TwoByTwo) (j : Fin 2) (w : Fin 2 → ℝ) : ℝ :=
  M.a j w 0 / M.a j w 1

namespace TwoByTwo

variable {M : TwoByTwo}

/-- Producing with the unit input vector: `fⱼ(q aⱼ(w)) = q` for `q ≥ 0`. -/
theorem f_smul_a (hM : M.IsModel) (j : Fin 2) {w : Fin 2 → ℝ} (hw : StrictlyPositive w) {q : ℝ}
    (hq : 0 ≤ q) : M.f j (q • M.a j w) = q := by
  rw [hM.hom j _ (hM.a_mem j w hw).1 q hq, (hM.a_mem j w hw).2, mul_one]

/-! ### Supported allocations are efficient -/

/-- **Figure 15.D.2(b)** (MWG, p. 533). An allocation supported by common factor prices `w ≫ 0` is
in the Pareto set: if `z'` produced at least as much of both goods and more of one, then
`∑ⱼ fⱼ(z'ⱼ) cⱼ(w) > ∑ⱼ qⱼ cⱼ(w) = w·z̄`, while duality gives `fⱼ(z'ⱼ) cⱼ(w) ≤ w·z'ⱼ`. -/
theorem supported_isEfficient (hM : M.IsModel) {zbar w q : Fin 2 → ℝ} {z : Fin 2 → Fin 2 → ℝ}
    (h : M.IsSupportedBy zbar w q z) : M.IsEfficientAllocation zbar z := by
  obtain ⟨hw, hq, hz, hsum⟩ := h
  have hzm : ∀ j, z j ∈ nonnegOrthant 2 := fun j l => by
    rw [hz j]
    simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_nonneg (hq j) ((hM.a_mem j w hw).1 l)
  refine ⟨⟨hzm, hsum⟩, ?_⟩
  rintro ⟨z', ⟨hz'm, hsum'⟩, hge, j, hlt⟩
  have hfz : ∀ k, M.f k (z k) = q k := fun k => by rw [hz k]; exact f_smul_a hM k hw (hq k)
  have hdual : ∀ k, M.f k (z' k) * M.c k w ≤ w ⬝ᵥ z' k := fun k => f_mul_c_le hM k hw (hz'm k)
  have hcost : ∀ k, w ⬝ᵥ z k = q k * M.c k w := fun k => by
    rw [hz k, dotProduct_smul, smul_eq_mul]
    rfl
  have htot : w ⬝ᵥ z' 0 + w ⬝ᵥ z' 1 = w ⬝ᵥ z 0 + w ⬝ᵥ z 1 := by
    rw [← dotProduct_add, ← dotProduct_add, hsum, hsum']
  rw [hcost 0, hcost 1] at htot
  have hc0 := c_pos hM 0 hw
  have hc1 := c_pos hM 1 hw
  have h0 := hge 0
  have h1 := hge 1
  rw [hfz] at h0 h1 hlt
  have hd0 := hdual 0
  have hd1 := hdual 1
  rcases Fin.exists_fin_two.1 (⟨j, hlt⟩ : ∃ k, q k < M.f k (z' k)) with hl | hl
  · nlinarith [mul_le_mul_of_nonneg_right h1 hc1.le, mul_lt_mul_of_pos_right hl hc0]
  · nlinarith [mul_le_mul_of_nonneg_right h0 hc0.le, mul_lt_mul_of_pos_right hl hc1]

/-! ### Exercise 15.D.1(a): the intensity ranking along the supported allocations -/

/-- The second endowment coordinate of an interior supported allocation is positive. -/
theorem interiorSupport_zbar_pos (hM : M.IsModel) {zbar w q : Fin 2 → ℝ}
    (h : M.IsInteriorSupport zbar w q) : StrictlyPositive zbar := by
  obtain ⟨hw, hq, hsum⟩ := h
  intro l
  rw [← hsum]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have := mul_pos (hq 0) (hM.a_pos 0 w l hw)
  have := mul_pos (hq 1) (hM.a_pos 1 w l hw)
  linarith

/-- The full-employment identities of an interior supported allocation, with `rⱼ` the factor
intensities at `w`: `q₀ a₂₁ (r₀ - r₁) = z̄₁ - r₁ z̄₂` and `q₁ a₂₂ (r₀ - r₁) = r₀ z̄₂ - z̄₁`. -/
theorem interiorSupport_identities (hM : M.IsModel) {zbar w q : Fin 2 → ℝ}
    (h : M.IsInteriorSupport zbar w q) :
    q 0 * M.a 0 w 1 * (M.factorRatio 0 w - M.factorRatio 1 w) =
        zbar 0 - M.factorRatio 1 w * zbar 1 ∧
      q 1 * M.a 1 w 1 * (M.factorRatio 0 w - M.factorRatio 1 w) =
        M.factorRatio 0 w * zbar 1 - zbar 0 := by
  obtain ⟨hw, -, hsum⟩ := h
  have e0 := congrFun hsum 0
  have e1 := congrFun hsum 1
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e0 e1
  have h01 := (hM.a_pos 0 w 1 hw).ne'
  have h11 := (hM.a_pos 1 w 1 hw).ne'
  unfold factorRatio
  rw [← e0, ← e1]
  constructor <;> field_simp <;> ring

/-- **Exercise 15.D.1(a)** (MWG, p. 533). At an interior supported allocation with
`r₁ < r₀`, the endowment ratio `ρ̄ = z̄₁/z̄₂` lies strictly between the intensities:
`r₁ < ρ̄ < r₀`. -/
theorem interiorSupport_between (hM : M.IsModel) {zbar w q : Fin 2 → ℝ}
    (h : M.IsInteriorSupport zbar w q) (hlt : M.factorRatio 1 w < M.factorRatio 0 w) :
    M.factorRatio 1 w < zbar 0 / zbar 1 ∧ zbar 0 / zbar 1 < M.factorRatio 0 w := by
  obtain ⟨e0, e1⟩ := interiorSupport_identities hM h
  have hz1 := interiorSupport_zbar_pos hM h 1
  have hp0 := mul_pos (mul_pos (h.2.1 0) (hM.a_pos 0 w 1 h.1)) (sub_pos.2 hlt)
  have hp1 := mul_pos (mul_pos (h.2.1 1) (hM.a_pos 1 w 1 h.1)) (sub_pos.2 hlt)
  rw [lt_div_iff₀ hz1, div_lt_iff₀ hz1]
  constructor <;> linarith

/-- The mirror image: if `r₀ < r₁` then `r₀ < ρ̄ < r₁`. -/
theorem interiorSupport_between' (hM : M.IsModel) {zbar w q : Fin 2 → ℝ}
    (h : M.IsInteriorSupport zbar w q) (hlt : M.factorRatio 0 w < M.factorRatio 1 w) :
    M.factorRatio 0 w < zbar 0 / zbar 1 ∧ zbar 0 / zbar 1 < M.factorRatio 1 w := by
  obtain ⟨e0, e1⟩ := interiorSupport_identities hM h
  have hz1 := interiorSupport_zbar_pos hM h 1
  have hp0 := mul_pos (mul_pos (h.2.1 0) (hM.a_pos 0 w 1 h.1)) (sub_pos.2 hlt)
  have hp1 := mul_pos (mul_pos (h.2.1 1) (hM.a_pos 1 w 1 h.1)) (sub_pos.2 hlt)
  rw [lt_div_iff₀ hz1, div_lt_iff₀ hz1]
  constructor <;> nlinarith

/-- With equal intensities, `r₀ = r₁ = ρ̄`: both firms use the factors in the endowment
proportions. -/
theorem interiorSupport_eq (hM : M.IsModel) {zbar w q : Fin 2 → ℝ}
    (h : M.IsInteriorSupport zbar w q) (heq : M.factorRatio 0 w = M.factorRatio 1 w) :
    M.factorRatio 0 w = zbar 0 / zbar 1 ∧ M.factorRatio 1 w = zbar 0 / zbar 1 := by
  obtain ⟨e0, -⟩ := interiorSupport_identities hM h
  have hz1 := interiorSupport_zbar_pos hM h 1
  rw [heq, sub_self, mul_zero] at e0
  have : M.factorRatio 1 w = zbar 0 / zbar 1 := by
    rw [eq_div_iff hz1.ne']
    linarith
  exact ⟨heq.trans this, this⟩

/-- Revealed cost minimization in terms of `w`: the factor intensities are antitone in the
relative factor price `w₁/w₂` (MWG, p. 532). -/
theorem factorRatio_antitone (hM : M.IsModel) (j : Fin 2) {w w' : Fin 2 → ℝ}
    (hw : StrictlyPositive w) (hw' : StrictlyPositive w') (h : w 0 / w 1 ≤ w' 0 / w' 1) :
    M.factorRatio j w' ≤ M.factorRatio j w := by
  unfold factorRatio
  rw [a_eq_rel hM j hw, a_eq_rel hM j hw']
  exact intensity_antitone hM j (div_pos (hw 0) (hw 1)) h

/-- **Exercise 15.D.1(a)** (MWG, p. 533). If firm 1 is more intensive in factor 1 at one interior
supported allocation of `z̄`, it is so at every interior supported allocation of `z̄`. (A flip
would put `ρ̄` on opposite sides, which the monotonicity of both intensities in `w₁/w₂` rules
out.) -/
theorem factorRatio_order_preserved (hM : M.IsModel) {zbar w q w' q' : Fin 2 → ℝ}
    (h : M.IsInteriorSupport zbar w q) (h' : M.IsInteriorSupport zbar w' q')
    (hlt : M.factorRatio 1 w < M.factorRatio 0 w) :
    M.factorRatio 1 w' < M.factorRatio 0 w' := by
  by_contra hn
  rw [not_lt] at hn
  obtain ⟨hb1, hb2⟩ := interiorSupport_between hM h hlt
  have hρ' : M.factorRatio 0 w' ≤ zbar 0 / zbar 1 ∧ zbar 0 / zbar 1 ≤ M.factorRatio 1 w' := by
    rcases eq_or_lt_of_le hn with he | hl
    · have := interiorSupport_eq hM h' he
      exact ⟨this.1.le, this.2.ge⟩
    · have := interiorSupport_between' hM h' hl
      exact ⟨this.1.le, this.2.le⟩
  rcases le_or_gt (w' 0 / w' 1) (w 0 / w 1) with hle | hgt
  · have := factorRatio_antitone hM 0 h'.1 h.1 hle
    linarith
  · have := factorRatio_antitone hM 1 h.1 h'.1 hgt.le
    linarith

/-- **Exercise 15.D.1(a)** (MWG, p. 533), the mirror image: if firm 2 is more intensive in
factor 1 at one interior supported allocation of `z̄`, it is so at all of them. -/
theorem factorRatio_order_preserved' (hM : M.IsModel) {zbar w q w' q' : Fin 2 → ℝ}
    (h : M.IsInteriorSupport zbar w q) (h' : M.IsInteriorSupport zbar w' q')
    (hlt : M.factorRatio 0 w < M.factorRatio 1 w) :
    M.factorRatio 0 w' < M.factorRatio 1 w' := by
  by_contra hn
  rw [not_lt] at hn
  obtain ⟨hb1, hb2⟩ := interiorSupport_between' hM h hlt
  have hρ' : M.factorRatio 1 w' ≤ zbar 0 / zbar 1 ∧ zbar 0 / zbar 1 ≤ M.factorRatio 0 w' := by
    rcases eq_or_lt_of_le hn with he | hl
    · have := interiorSupport_eq hM h' he.symm
      exact ⟨this.2.le, this.1.ge⟩
    · have := interiorSupport_between hM h' hl
      exact ⟨this.1.le, this.2.le⟩
  rcases le_or_gt (w' 0 / w' 1) (w 0 / w 1) with hle | hgt
  · have := factorRatio_antitone hM 1 h'.1 h.1 hle
    linarith
  · have := factorRatio_antitone hM 0 h.1 h'.1 hgt.le
    linarith

/-- **Exercise 15.D.1(a)** (MWG, p. 533). Equal intensities at one interior supported allocation
of `z̄` force equal intensities at all of them. -/
theorem factorRatio_eq_preserved (hM : M.IsModel) {zbar w q w' q' : Fin 2 → ℝ}
    (h : M.IsInteriorSupport zbar w q) (h' : M.IsInteriorSupport zbar w' q')
    (heq : M.factorRatio 0 w = M.factorRatio 1 w) :
    M.factorRatio 0 w' = M.factorRatio 1 w' := by
  rcases lt_trichotomy (M.factorRatio 0 w') (M.factorRatio 1 w') with hl | he | hg
  · have := factorRatio_order_preserved' hM h' h hl
    linarith
  · exact he
  · have := factorRatio_order_preserved hM h' h hg
    linarith

/-- **Exercise 15.D.1(a)** (MWG, p. 533). For a given endowment `z̄`, either firm 1 is more
intensive in factor 1 at every interior supported allocation, or firm 2 is at every one, or at
every one both firms use the factors in the endowment proportions `ρ̄ = z̄₁/z̄₂` (the diagonal of
the Edgeworth box). -/
theorem exercise_15_D_1a (hM : M.IsModel) (zbar : Fin 2 → ℝ) :
    (∀ w q, M.IsInteriorSupport zbar w q → M.factorRatio 1 w < M.factorRatio 0 w) ∨
      (∀ w q, M.IsInteriorSupport zbar w q → M.factorRatio 0 w < M.factorRatio 1 w) ∨
      (∀ w q, M.IsInteriorSupport zbar w q →
        M.factorRatio 0 w = zbar 0 / zbar 1 ∧ M.factorRatio 1 w = zbar 0 / zbar 1) := by
  by_cases hex : ∃ w q, M.IsInteriorSupport zbar w q
  · obtain ⟨w, q, h⟩ := hex
    rcases lt_trichotomy (M.factorRatio 0 w) (M.factorRatio 1 w) with hl | he | hg
    · exact Or.inr (Or.inl fun w' q' h' => factorRatio_order_preserved' hM h h' hl)
    · exact Or.inr (Or.inr fun w' q' h' =>
        interiorSupport_eq hM h' (factorRatio_eq_preserved hM h h' he))
    · exact Or.inl fun w' q' h' => factorRatio_order_preserved hM h h' hg
  · exact Or.inl fun w q h => absurd ⟨w, q, h⟩ hex

/-- **Section 15.D** (MWG, p. 533), the diagonal claim: "if [the Pareto set] ever cuts the
diagonal then ... the diagonal must be the Pareto set". If at an interior supported allocation
firm 1 uses `t z̄` (`0 < t < 1`), then every point `s z̄` (`0 < s < 1`) of the diagonal is
supported by the same factor prices, and every interior supported allocation of `z̄` lies on the
diagonal. -/
theorem diagonal_pareto_set (hM : M.IsModel) {zbar w q : Fin 2 → ℝ}
    (h : M.IsInteriorSupport zbar w q) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hdiag : q 0 • M.a 0 w = t • zbar) :
    (∀ s : ℝ, 0 < s → s < 1 →
        M.IsInteriorSupport zbar w ![s * q 0 / t, (1 - s) * q 1 / (1 - t)] ∧
          (s * q 0 / t) • M.a 0 w = s • zbar) ∧
      ∀ w' q', M.IsInteriorSupport zbar w' q' →
        ∃ s : ℝ, 0 < s ∧ s < 1 ∧ q' 0 • M.a 0 w' = s • zbar := by
  obtain ⟨hw, hq, hsum⟩ := h
  have d0 : ∀ l, q 0 * M.a 0 w l = t * zbar l := fun l => by simpa using congrFun hdiag l
  have d1 : ∀ l, q 1 * M.a 1 w l = (1 - t) * zbar l := fun l => by
    have := congrFun hsum l
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    rw [sub_mul, one_mul, ← d0 l]
    linarith
  have ht1' : 0 < 1 - t := sub_pos.2 ht1
  constructor
  · intro s hs0 hs1
    have hs1' : 0 < 1 - s := sub_pos.2 hs1
    have e0 : ∀ l, s * q 0 / t * M.a 0 w l = s * zbar l := fun l => by
      rw [show s * q 0 / t * M.a 0 w l = s / t * (q 0 * M.a 0 w l) by ring, d0 l]
      field_simp
    have e1 : ∀ l, (1 - s) * q 1 / (1 - t) * M.a 1 w l = (1 - s) * zbar l := fun l => by
      rw [show (1 - s) * q 1 / (1 - t) * M.a 1 w l = (1 - s) / (1 - t) * (q 1 * M.a 1 w l)
        by ring, d1 l]
      field_simp
    refine ⟨⟨hw, fun j => ?_, ?_⟩, ?_⟩
    · fin_cases j
      · simpa using div_pos (mul_pos hs0 (hq 0)) ht0
      · simpa using div_pos (mul_pos hs1' (hq 1)) ht1'
    · funext l
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
        Matrix.cons_val_one]
      rw [e0 l, e1 l]
      ring
    · funext l
      simp only [Pi.smul_apply, smul_eq_mul]
      exact e0 l
  · intro w' q' h'
    have hz1 := interiorSupport_zbar_pos hM ⟨hw, hq, hsum⟩ 1
    have hr0 : M.factorRatio 0 w = M.factorRatio 1 w := by
      have hq0 := (hq 0).ne'
      have hq1 := (hq 1).ne'
      have h01 := (hM.a_pos 0 w 1 hw).ne'
      have h11 := (hM.a_pos 1 w 1 hw).ne'
      unfold factorRatio
      rw [div_eq_div_iff h01 h11]
      have k0 : q 0 * (M.a 0 w 0 * zbar 1) = q 0 * (M.a 0 w 1 * zbar 0) := by
        linear_combination zbar 1 * d0 0 - zbar 0 * d0 1
      have k1 : q 1 * (M.a 1 w 0 * zbar 1) = q 1 * (M.a 1 w 1 * zbar 0) := by
        linear_combination zbar 1 * d1 0 - zbar 0 * d1 1
      have k0' := mul_left_cancel₀ hq0 k0
      have k1' := mul_left_cancel₀ hq1 k1
      have hzb := hz1.ne'
      have : M.a 0 w 0 * M.a 1 w 1 * zbar 1 = M.a 1 w 0 * M.a 0 w 1 * zbar 1 := by
        linear_combination M.a 1 w 1 * k0' - M.a 0 w 1 * k1'
      exact mul_right_cancel₀ hzb this
    have he' := factorRatio_eq_preserved hM ⟨hw, hq, hsum⟩ h' hr0
    have hρ := (interiorSupport_eq hM h' he').1
    have hw' := h'.1
    have hq' := h'.2.1
    have hs' := congrFun h'.2.2 1
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hs'
    have ha01 := hM.a_pos 0 w' 1 hw'
    have ha11 := hM.a_pos 1 w' 1 hw'
    refine ⟨q' 0 * M.a 0 w' 1 / zbar 1, div_pos (mul_pos (hq' 0) ha01) hz1, ?_, ?_⟩
    · rw [div_lt_one hz1]
      nlinarith [mul_pos (hq' 1) ha11]
    · unfold factorRatio at hρ
      rw [div_eq_div_iff ha01.ne' hz1.ne'] at hρ
      funext l
      simp only [Pi.smul_apply, smul_eq_mul]
      fin_cases l
      · simp only [Fin.zero_eta, Fin.isValue]
        field_simp
        linear_combination q' 0 * hρ
      · simp only [Fin.mk_one, Fin.isValue]
        field_simp

/-! ### Exercise 15.D.1(b), corrected: smooth technologies -/

/-- **Exercise 15.D.1(b)** (MWG, p. 533), corrected hypothesis. If good `j`'s technology is
differentiable along rays, its factor intensity is strictly decreasing in the relative factor
price: two relative prices with the same cost-minimizing ratio `ρ` would give two different
slopes `ω/gⱼ(ω) = Fⱼ(ρ) ω/(ωρ + 1)` of the isoquant at `ρ` (`rayF_deriv_eq`). -/
theorem relRatio_strictAnti (hM : M.IsModel) (j : Fin 2) (hd : M.RayDifferentiable j)
    {ω ω' : ℝ} (hω : 0 < ω) (hlt : ω < ω') :
    M.a j ![ω', 1] 0 / M.a j ![ω', 1] 1 < M.a j ![ω, 1] 0 / M.a j ![ω, 1] 1 := by
  have hω' : 0 < ω' := hω.trans hlt
  refine lt_of_le_of_ne (intensity_antitone hM j hω hlt.le) fun heq => ?_
  obtain ⟨ρ, hρ⟩ : ∃ ρ, M.a j ![ω, 1] 0 / M.a j ![ω, 1] 1 = ρ := ⟨_, rfl⟩
  rw [hρ] at heq
  have hp := relPrice_pos hω
  have hρpos : 0 < ρ := hρ ▸ div_pos (hM.a_pos j _ 0 hp) (hM.a_pos j _ 1 hp)
  have hD := (hd ρ hρpos).hasDerivAt
  have e1 := rayF_deriv_eq hM j hω hρ hD
  have e2 := rayF_deriv_eq hM j hω' heq hD
  have f1 := rayF_mul_g_eq hM j hω hρ
  have f2 := rayF_mul_g_eq hM j hω' heq
  have hg : 0 < M.g j ω := c_pos hM j hp
  have hg' : 0 < M.g j ω' := c_pos hM j (relPrice_pos hω')
  rw [e1, div_eq_div_iff hg.ne' hg'.ne'] at e2
  have key : ω * (ω' * ρ + 1) = ω' * (ω * ρ + 1) := by
    rw [← f1, ← f2]
    linear_combination M.f j ![ρ, 1] * e2
  have : ω = ω' := by linear_combination key
  exact absurd this hlt.ne

/-- **Exercise 15.D.1(b)** (MWG, p. 533), corrected. With technologies differentiable along rays,
a higher relative factor price `w₁/w₂` makes both firms strictly less intensive in factor 1. -/
theorem exercise_15_D_1b_ratios_fall (hM : M.IsModel) (hd : ∀ j, M.RayDifferentiable j)
    {w w' : Fin 2 → ℝ} (hw : StrictlyPositive w) (hw' : StrictlyPositive w')
    (hlt : w 0 / w 1 < w' 0 / w' 1) (j : Fin 2) : M.factorRatio j w' < M.factorRatio j w := by
  unfold factorRatio
  rw [a_eq_rel hM j hw, a_eq_rel hM j hw']
  exact relRatio_strictAnti hM j (hd j) (div_pos (hw 0) (hw 1)) hlt

/-- **Exercise 15.D.1(b)** (MWG, p. 533), corrected: "the factor intensities of the two firms and
the supporting relative factor prices change monotonically as we move along the Pareto set from
one origin to the other". For interior supported allocations of `z̄` with firm 1 more intensive
in factor 1, and technologies differentiable along rays: if the supporting relative factor price
is higher at `w'` than at `w`, both intensities are strictly lower at `w'`, and firm 1 uses
strictly more of both factors (the allocation moves from firm 1's origin towards firm 2's). -/
theorem exercise_15_D_1b_monotone (hM : M.IsModel) (hd : ∀ j, M.RayDifferentiable j)
    {zbar w q w' q' : Fin 2 → ℝ} (h : M.IsInteriorSupport zbar w q)
    (h' : M.IsInteriorSupport zbar w' q') (hint : M.factorRatio 1 w < M.factorRatio 0 w)
    (hlt : w 0 / w 1 < w' 0 / w' 1) :
    M.factorRatio 0 w' < M.factorRatio 0 w ∧ M.factorRatio 1 w' < M.factorRatio 1 w ∧
      q 0 * M.a 0 w 0 < q' 0 * M.a 0 w' 0 ∧ q 0 * M.a 0 w 1 < q' 0 * M.a 0 w' 1 := by
  have ha0 := exercise_15_D_1b_ratios_fall hM hd h.1 h'.1 hlt 0
  have ha1 := exercise_15_D_1b_ratios_fall hM hd h.1 h'.1 hlt 1
  have hint' := factorRatio_order_preserved hM h h' hint
  obtain ⟨hb1, hb2⟩ := interiorSupport_between hM h hint
  obtain ⟨hb1', hb2'⟩ := interiorSupport_between hM h' hint'
  obtain ⟨eS, -⟩ := interiorSupport_identities hM h
  obtain ⟨eS', -⟩ := interiorSupport_identities hM h'
  have hz1 := interiorSupport_zbar_pos hM h 1
  have hbpos : 0 < M.factorRatio 1 w := div_pos (hM.a_pos 1 w 0 h.1) (hM.a_pos 1 w 1 h.1)
  have c0 : q 0 * M.a 0 w 0 = M.factorRatio 0 w * (q 0 * M.a 0 w 1) := by
    have := (hM.a_pos 0 w 1 h.1).ne'
    unfold factorRatio
    field_simp
  have c0' : q' 0 * M.a 0 w' 0 = M.factorRatio 0 w' * (q' 0 * M.a 0 w' 1) := by
    have := (hM.a_pos 0 w' 1 h'.1).ne'
    unfold factorRatio
    field_simp
  rw [lt_div_iff₀ hz1] at hb1 hb1'
  rw [div_lt_iff₀ hz1] at hb2 hb2'
  refine ⟨ha0, ha1, ?_, ?_⟩
  · rw [c0, c0']
    set a := M.factorRatio 0 w
    set b := M.factorRatio 1 w
    set a' := M.factorRatio 0 w'
    set b' := M.factorRatio 1 w'
    set S := q 0 * M.a 0 w 1
    set S' := q' 0 * M.a 0 w' 1
    have key : (a' * S' - a * S) * ((a - b) * (a' - b')) * (a' - b) =
        a' * (b - b') * (a' * zbar 1 - zbar 0) * (a - b) +
          (zbar 0 - b * zbar 1) * b * (a - a') * (a' - b') := by
      linear_combination (a' * (a - b) * (a' - b)) * eS' - (a * (a' - b') * (a' - b)) * eS
    have ha'pos : 0 < a' := by nlinarith
    have hR : 0 < a' * (b - b') * (a' * zbar 1 - zbar 0) * (a - b) +
        (zbar 0 - b * zbar 1) * b * (a - a') * (a' - b') := by
      apply add_pos
      · apply mul_pos (mul_pos (mul_pos ha'pos (by linarith)) (by linarith)) (by linarith)
      · apply mul_pos (mul_pos (mul_pos (by linarith) hbpos) (by linarith)) (by linarith)
    have hP : 0 < (a - b) * (a' - b') * (a' - b) :=
      mul_pos (mul_pos (by linarith) (by linarith)) (by nlinarith)
    by_contra hc
    rw [not_lt] at hc
    have : (a' * S' - a * S) * ((a - b) * (a' - b')) * (a' - b) ≤ 0 :=
      calc _ = (a' * S' - a * S) * ((a - b) * (a' - b') * (a' - b)) := by ring
        _ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hP.le
    linarith
  · set a := M.factorRatio 0 w
    set b := M.factorRatio 1 w
    set a' := M.factorRatio 0 w'
    set b' := M.factorRatio 1 w'
    set S := q 0 * M.a 0 w 1
    set S' := q' 0 * M.a 0 w' 1
    have key : (S' - S) * ((a - b) * (a' - b')) =
        (zbar 0 - b * zbar 1) * (a - a') + (b - b') * (zbar 1 * a - zbar 0) := by
      linear_combination (a - b) * eS' - (a' - b') * eS
    have hR : 0 < (zbar 0 - b * zbar 1) * (a - a') + (b - b') * (zbar 1 * a - zbar 0) :=
      add_pos (mul_pos (by linarith) (by linarith)) (mul_pos (by linarith) (by linarith))
    have hP : 0 < (a - b) * (a' - b') := mul_pos (by linarith) (by linarith)
    by_contra hc
    rw [not_lt] at hc
    have : (S' - S) * ((a - b) * (a' - b')) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) hP.le
    linarith

/-- **Exercise 15.D.1(b)** (MWG, p. 533), corrected: "any ray from the origin of either of the
firms can intersect the Pareto set at most once". With technologies differentiable along rays,
two interior supported allocations of `z̄` off the diagonal (`r₀ ≠ r₁`) at which firm `j` uses
the factors in the same proportion (the same ray from firm `j`'s origin) are equal. -/
theorem exercise_15_D_1b (hM : M.IsModel) (hd : ∀ j, M.RayDifferentiable j)
    {zbar w q w' q' : Fin 2 → ℝ} (h : M.IsInteriorSupport zbar w q)
    (h' : M.IsInteriorSupport zbar w' q') (hne : M.factorRatio 0 w ≠ M.factorRatio 1 w)
    (j : Fin 2) (hray : M.factorRatio j w = M.factorRatio j w') :
    (fun k => q k • M.a k w) = fun k => q' k • M.a k w' := by
  have hω : w 0 / w 1 = w' 0 / w' 1 := by
    rcases lt_trichotomy (w 0 / w 1) (w' 0 / w' 1) with hl | he | hg
    · have := exercise_15_D_1b_ratios_fall hM hd h.1 h'.1 hl j
      linarith
    · exact he
    · have := exercise_15_D_1b_ratios_fall hM hd h'.1 h.1 hg j
      linarith
  have ha : ∀ k, M.a k w = M.a k w' := fun k => by
    rw [a_eq_rel hM k h.1, a_eq_rel hM k h'.1, hω]
  have h01 := hM.a_pos 0 w 1 h.1
  have h11 := hM.a_pos 1 w 1 h.1
  have hD : M.a 0 w 0 * M.a 1 w 1 - M.a 1 w 0 * M.a 0 w 1 ≠ 0 := by
    intro hD0
    apply hne
    unfold factorRatio
    rw [div_eq_div_iff h01.ne' h11.ne']
    linarith
  have hs : ∑ k, q k • M.a k w = zbar := by rw [Fin.sum_univ_two]; exact h.2.2
  have hs' : ∑ k, q' k • M.a k w = zbar := by
    rw [Fin.sum_univ_two, ha 0, ha 1]
    exact h'.2.2
  have hc := outputs_cramer (a := fun k => M.a k w) hD hs
  have hc' := outputs_cramer (a := fun k => M.a k w) hD hs'
  have hq : q = q' := by
    funext k
    fin_cases k
    · exact hc.1.trans hc'.1.symm
    · exact hc.2.trans hc'.2.symm
  funext k
  rw [hq, ha k]

/-! ### Efficient interior allocations are supported (smooth technologies) -/

/-- Moving along a line from an interior point keeps it interior for small steps. -/
theorem eventually_strictlyPositive_line {z : Fin 2 → ℝ} (hz : StrictlyPositive z)
    (d : Fin 2 → ℝ) : ∀ᶠ t in 𝓝 (0 : ℝ), StrictlyPositive (z + t • d) := by
  have : ∀ l, ∀ᶠ t in 𝓝 (0 : ℝ), 0 < (z + t • d) l := by
    intro l
    have hc : Continuous fun t : ℝ => (z + t • d) l := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      fun_prop
    exact (hc.tendsto 0).eventually (lt_mem_nhds (by simpa using hz l))
  exact Filter.eventually_all.2 this

/-- A function with positive derivative at `0` exceeds its value at `0` just to the right. -/
theorem eventually_lt_of_hasDerivAt_pos {φ : ℝ → ℝ} {D : ℝ} (hφ : HasDerivAt φ D 0)
    (hD : 0 < D) : ∀ᶠ t in 𝓝[>] (0 : ℝ), φ 0 < φ t := by
  have h1 := hφ.tendsto_slope_zero_right.eventually (lt_mem_nhds hD)
  filter_upwards [h1, self_mem_nhdsWithin] with t ht htpos
  simp only [zero_add, smul_eq_mul] at ht
  have htpos' : 0 < t := htpos
  have := mul_pos htpos' ht
  rwa [← mul_assoc, mul_inv_cancel₀ htpos'.ne', one_mul, sub_pos] at this

/-- The derivative of `fⱼ` along a line through an interior point `z` whose factor ratio is
cost-minimizing at the relative factor price `ω`: `d/dt fⱼ(z + t d) = (ω d₁ + d₂)/gⱼ(ω)` at
`t = 0`. The gradient of `fⱼ` at `z` is a positive multiple of `(ω, 1)` (by homogeneity,
`fⱼ(x) = x₂ Fⱼ(x₁/x₂)`, and `rayF_deriv_eq`). -/
theorem f_hasDerivAt_line (hM : M.IsModel) (j : Fin 2) (hd : M.RayDifferentiable j)
    {z d : Fin 2 → ℝ} (hz : StrictlyPositive z) {ω : ℝ} (hω : 0 < ω)
    (hk : M.a j ![ω, 1] 0 / M.a j ![ω, 1] 1 = z 0 / z 1) :
    HasDerivAt (fun t : ℝ => M.f j (z + t • d)) ((ω * d 0 + d 1) / M.g j ω) 0 := by
  have hz0 := hz 0
  have hz1 := hz 1
  have hρ : 0 < z 0 / z 1 := div_pos hz0 hz1
  have hF := (hd _ hρ).hasDerivAt
  have hF' := rayF_deriv_eq hM j hω hk hF
  have hFg := rayF_mul_g_eq hM j hω hk
  have hg : 0 < M.g j ω := c_pos hM j (relPrice_pos hω)
  have h0 : HasDerivAt (fun t : ℝ => z 0 + t * d 0) (d 0) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (d 0)).const_add (z 0)
  have h1 : HasDerivAt (fun t : ℝ => z 1 + t * d 1) (d 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (d 1)).const_add (z 1)
  have hr : HasDerivAt (fun t : ℝ => (z 0 + t * d 0) / (z 1 + t * d 1))
      ((d 0 * (z 1 + 0 * d 1) - (z 0 + 0 * d 0) * d 1) / (z 1 + 0 * d 1) ^ 2) 0 :=
    h0.div h1 (by simpa using hz1.ne')
  have hF0 : HasDerivAt (fun s : ℝ => M.f j ![s, 1])
      (deriv (fun s : ℝ => M.f j ![s, 1]) (z 0 / z 1))
      ((fun t : ℝ => (z 0 + t * d 0) / (z 1 + t * d 1)) 0) := by
    simpa using hF
  have hprod := h1.mul (hF0.comp (0 : ℝ) hr)
  have heq : (fun t : ℝ => M.f j (z + t • d)) =ᶠ[𝓝 0] fun t =>
      (z 1 + t * d 1) * ((fun s : ℝ => M.f j ![s, 1]) ∘
        (fun t : ℝ => (z 0 + t * d 0) / (z 1 + t * d 1))) t := by
    filter_upwards [eventually_strictlyPositive_line hz d] with t ht
    rw [f_eq_ray hM j ht]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply]
  have := hprod.congr_of_eventuallyEq heq
  convert this using 1
  rw [hF']
  have hFρ : M.f j ![z 0 / z 1, 1] = (ω * (z 0 / z 1) + 1) / M.g j ω := by
    rw [eq_div_iff hg.ne']
    exact hFg
  simp only [Function.comp_apply, zero_mul, add_zero]
  rw [hFρ]
  field_simp
  ring

/-- **Figure 15.D.2(b)** (MWG, p. 533), the converse: with ray-surjective technologies that are
differentiable along rays, every efficient allocation with `zⱼ ≫ 0` for both firms is supported
by common factor prices (the isoquants are tangent). Otherwise the gradients of `f₁` and `f₂`
point in different directions, and moving a little of the factors from firm 2 to firm 1 along a
suitable direction raises both outputs. -/
theorem efficient_isSupported (hM : M.IsModel) (hs : ∀ j, M.RaySurjective j)
    (hd : ∀ j, M.RayDifferentiable j) {zbar : Fin 2 → ℝ} {z : Fin 2 → Fin 2 → ℝ}
    (h : M.IsEfficientAllocation zbar z) (hint : ∀ j, StrictlyPositive (z j)) :
    M.IsSupportedAllocation zbar z := by
  obtain ⟨⟨-, hsum⟩, hne⟩ := h
  choose ω hω hk using fun j => hs j (z j 0 / z j 1) (div_pos (hint j 0) (hint j 1))
  have hrep : ∀ j, z j = (z j 1 / M.a j ![ω j, 1] 1) • M.a j ![ω j, 1] := by
    intro j
    have ha1 := hM.a_pos j ![ω j, 1] 1 (relPrice_pos (hω j))
    have hk' := hk j
    rw [div_eq_div_iff ha1.ne' (hint j 1).ne'] at hk'
    funext l
    fin_cases l
    · simp only [Fin.zero_eta, Fin.isValue, Pi.smul_apply, smul_eq_mul]
      field_simp
      linarith
    · simp only [Fin.mk_one, Fin.isValue, Pi.smul_apply, smul_eq_mul]
      field_simp
  have heq : ω 0 = ω 1 := by
    by_contra hne'
    have hδ : 0 < (ω 0 - ω 1) ^ 2 / 2 := by
      have := sub_ne_zero.2 hne'
      positivity
    set d : Fin 2 → ℝ := ![ω 0 - ω 1, -((ω 0 - ω 1) * (ω 0 + ω 1) / 2)] with hdd
    have hD0 := f_hasDerivAt_line hM 0 (hd 0) (hint 0) (d := d) (hω 0) (hk 0)
    have hD1 := f_hasDerivAt_line hM 1 (hd 1) (hint 1) (d := -d) (hω 1) (hk 1)
    have hv0 : 0 < (ω 0 * d 0 + d 1) / M.g 0 (ω 0) := by
      apply div_pos _ (c_pos hM 0 (relPrice_pos (hω 0)))
      have : ω 0 * d 0 + d 1 = (ω 0 - ω 1) ^ 2 / 2 := by
        simp only [hdd, Matrix.cons_val_zero, Matrix.cons_val_one]
        ring
      rw [this]
      exact hδ
    have hv1 : 0 < (ω 1 * (-d) 0 + (-d) 1) / M.g 1 (ω 1) := by
      apply div_pos _ (c_pos hM 1 (relPrice_pos (hω 1)))
      have : ω 1 * (-d) 0 + (-d) 1 = (ω 0 - ω 1) ^ 2 / 2 := by
        simp only [hdd, Pi.neg_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
        ring
      rw [this]
      exact hδ
    have e0 := eventually_lt_of_hasDerivAt_pos hD0 hv0
    have e1 := eventually_lt_of_hasDerivAt_pos hD1 hv1
    have ep0 := (eventually_strictlyPositive_line (hint 0) d).filter_mono
      (nhdsWithin_le_nhds (s := Set.Ioi 0))
    have ep1 := (eventually_strictlyPositive_line (hint 1) (-d)).filter_mono
      (nhdsWithin_le_nhds (s := Set.Ioi 0))
    obtain ⟨t, ht0, ht1, hp0, hp1⟩ := (e0.and (e1.and (ep0.and ep1))).exists
    simp only [zero_smul, add_zero] at ht0 ht1
    apply hne
    refine ⟨![z 0 + t • d, z 1 + t • -d], ⟨Fin.forall_fin_two.2 ⟨fun l => (hp0 l).le,
      fun l => (hp1 l).le⟩, ?_⟩, Fin.forall_fin_two.2 ⟨ht0.le, ht1.le⟩, 0, ht0⟩
    rw [← hsum]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, smul_neg]
    abel
  refine ⟨![ω 0, 1], fun j => z j 1 / M.a j ![ω 0, 1] 1, relPrice_pos (hω 0),
    fun j => div_nonneg (hint j 1).le (hM.a_pos j _ 1 (relPrice_pos (hω 0))).le,
    Fin.forall_fin_two.2 ⟨hrep 0, ?_⟩, hsum⟩
  rw [heq]
  exact hrep 1

/-- An allocation supported by `w` with both firms' inputs `≫ 0` is an interior supported
allocation, and its factor proportions are the intensities at `w`. -/
theorem interiorSupport_of_supportedBy (hM : M.IsModel) {zbar w q : Fin 2 → ℝ}
    {z : Fin 2 → Fin 2 → ℝ} (h : M.IsSupportedBy zbar w q z)
    (hint : ∀ j, StrictlyPositive (z j)) :
    M.IsInteriorSupport zbar w q ∧ ∀ j, z j 0 / z j 1 = M.factorRatio j w := by
  obtain ⟨hw, -, hz, hsum⟩ := h
  have hq : ∀ j, 0 < q j := by
    intro j
    have := hint j 0
    rw [hz j] at this
    simp only [Pi.smul_apply, smul_eq_mul] at this
    by_contra hc
    rw [not_lt] at hc
    nlinarith [mul_le_mul_of_nonneg_right hc (hM.a_pos j w 0 hw).le]
  refine ⟨⟨hw, hq, by rw [← hz 0, ← hz 1]; exact hsum⟩, fun j => ?_⟩
  rw [hz j]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [mul_div_mul_left _ _ (hq j).ne']
  rfl

/-- **Exercise 15.D.1(a)** (MWG, p. 533), for the Pareto set itself (smooth technologies): if at
one efficient allocation with both firms' inputs `≫ 0` firm 1 uses factor 1 more intensively,
it does so at every such efficient allocation of `z̄`. -/
theorem exercise_15_D_1a_pareto (hM : M.IsModel) (hs : ∀ j, M.RaySurjective j)
    (hd : ∀ j, M.RayDifferentiable j) {zbar : Fin 2 → ℝ} {z z' : Fin 2 → Fin 2 → ℝ}
    (h : M.IsEfficientAllocation zbar z) (hint : ∀ j, StrictlyPositive (z j))
    (h' : M.IsEfficientAllocation zbar z') (hint' : ∀ j, StrictlyPositive (z' j))
    (hlt : z 1 0 / z 1 1 < z 0 0 / z 0 1) : z' 1 0 / z' 1 1 < z' 0 0 / z' 0 1 := by
  obtain ⟨w, q, hS⟩ := efficient_isSupported hM hs hd h hint
  obtain ⟨w', q', hS'⟩ := efficient_isSupported hM hs hd h' hint'
  obtain ⟨hI, hr⟩ := interiorSupport_of_supportedBy hM hS hint
  obtain ⟨hI', hr'⟩ := interiorSupport_of_supportedBy hM hS' hint'
  rw [hr, hr] at hlt
  rw [hr', hr']
  exact factorRatio_order_preserved hM hI hI' hlt

/-- **Section 15.D** (MWG, p. 533), the diagonal claim for the Pareto set (smooth technologies):
if one efficient allocation with both firms' inputs `≫ 0` lies on the diagonal, `z₁ = t z̄`, then
every point `(s z̄, (1 - s) z̄)` of the diagonal is efficient, and every efficient allocation with
both firms' inputs `≫ 0` lies on the diagonal: "the diagonal must be the Pareto set". -/
theorem diagonal_pareto_set_efficient (hM : M.IsModel) (hs : ∀ j, M.RaySurjective j)
    (hd : ∀ j, M.RayDifferentiable j) {zbar : Fin 2 → ℝ} {z : Fin 2 → Fin 2 → ℝ}
    (h : M.IsEfficientAllocation zbar z) (hint : ∀ j, StrictlyPositive (z j)) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (hdiag : z 0 = t • zbar) :
    (∀ s : ℝ, 0 < s → s < 1 → M.IsEfficientAllocation zbar ![s • zbar, (1 - s) • zbar]) ∧
      ∀ z', M.IsEfficientAllocation zbar z' → (∀ j, StrictlyPositive (z' j)) →
        ∃ s : ℝ, 0 < s ∧ s < 1 ∧ z' 0 = s • zbar := by
  obtain ⟨w, q, hS⟩ := efficient_isSupported hM hs hd h hint
  obtain ⟨hI, -⟩ := interiorSupport_of_supportedBy hM hS hint
  have hdiag' : q 0 • M.a 0 w = t • zbar := by rw [← hS.2.2.1 0]; exact hdiag
  have hD := diagonal_pareto_set hM hI ht0 ht1 hdiag'
  constructor
  · intro s hs0 hs1
    obtain ⟨hS2, h0⟩ := hD.1 s hs0 hs1
    obtain ⟨hw2, hq2, hsum2⟩ := hS2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hsum2 hq2
    refine supported_isEfficient hM (w := w) (q := ![s * q 0 / t, (1 - s) * q 1 / (1 - t)])
      ⟨hw2, fun j => (hq2 j).le, Fin.forall_fin_two.2 ⟨?_, ?_⟩, ?_⟩
    · simp only [Matrix.cons_val_zero]
      exact h0.symm
    · simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [h0] at hsum2
      funext l
      have := congrFun hsum2 l
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
      linarith
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      module
  · intro z' h' hint'
    obtain ⟨w', q', hS'⟩ := efficient_isSupported hM hs hd h' hint'
    obtain ⟨hI', -⟩ := interiorSupport_of_supportedBy hM hS' hint'
    obtain ⟨s, hs0, hs1, hs⟩ := hD.2 w' q' hI'
    exact ⟨s, hs0, hs1, by rw [hS'.2.2.1 0]; exact hs⟩

/-! ### Footnote 16: Stolper-Samuelson without the global factor intensity condition -/

/-- **Footnote 16** (MWG, p. 536). The Stolper-Samuelson conclusion without the factor intensity
condition. Compare interior factor market equilibria (`q ≫ 0`, `q' ≫ 0`) for the same endowment
at output prices `p` and `p'` with `p'₁ > p₁`, `p'₂ = p₂`, where firm 1 is more intensive in
factor 1 at the initial equilibrium. Then `w'₁ > w₁` and `w'₂ < w₂`. By Exercise 15.D.1(a) the
intensity ranking also holds at `w'`, hence at every relative factor price between, so the ratio
of unit costs is increasing on that interval and the relative price of factor 1 rises. -/
theorem footnote_16 (hM : M.IsModel) {p p' zbar w w' q q' : Fin 2 → ℝ}
    (h : IsFactorEqm M.f p zbar w (fun j => q j • M.a j w))
    (h' : IsFactorEqm M.f p' zbar w' (fun j => q' j • M.a j w'))
    (hq : ∀ j, 0 < q j) (hq' : ∀ j, 0 < q' j) (hp0 : p 0 < p' 0) (hp1 : p' 1 = p 1)
    (hint : M.factorRatio 1 w < M.factorRatio 0 w) : w 0 < w' 0 ∧ w' 1 < w 1 := by
  have hw := h.1
  have hw' := h'.1
  obtain ⟨hc, hsum⟩ := (interior_eqm_iff hM hw hq).1 h
  obtain ⟨hc', hsum'⟩ := (interior_eqm_iff hM hw' hq').1 h'
  have hS : M.IsInteriorSupport zbar w q := ⟨hw, hq, by rw [← hsum, Fin.sum_univ_two]⟩
  have hS' : M.IsInteriorSupport zbar w' q' := ⟨hw', hq', by rw [← hsum', Fin.sum_univ_two]⟩
  obtain ⟨-, hb2⟩ := interiorSupport_between hM hS hint
  have hint' := factorRatio_order_preserved hM hS hS' hint
  obtain ⟨hb1', -⟩ := interiorSupport_between hM hS' hint'
  obtain ⟨ω, hωd⟩ : ∃ ω, ω = w 0 / w 1 := ⟨_, rfl⟩
  obtain ⟨ω', hωd'⟩ : ∃ ω', ω' = w' 0 / w' 1 := ⟨_, rfl⟩
  have hω : 0 < ω := by rw [hωd]; exact div_pos (hw 0) (hw 1)
  have hω' : 0 < ω' := by rw [hωd']; exact div_pos (hw' 0) (hw' 1)
  have hb2r : zbar 0 / zbar 1 < M.a 0 ![ω, 1] 0 / M.a 0 ![ω, 1] 1 := by
    rw [hωd, ← a_eq_rel hM 0 hw]
    exact hb2
  have hb1r : M.a 1 ![ω', 1] 0 / M.a 1 ![ω', 1] 1 < zbar 0 / zbar 1 := by
    rw [hωd', ← a_eq_rel hM 1 hw']
    exact hb1'
  have hp1pos : 0 < p 1 := by rw [hc 1]; exact c_pos hM 1 hw
  -- the relative factor price rises
  have hlt : ω < ω' := by
    by_contra hn
    rw [not_lt] at hn
    have hpos : ∀ t ∈ Set.Icc ω' ω,
        M.a 1 ![t, 1] 0 / M.a 1 ![t, 1] 1 < M.a 0 ![t, 1] 0 / M.a 0 ![t, 1] 1 := by
      intro t ht
      have ht0 : 0 < t := lt_of_lt_of_le hω' ht.1
      have k0 := intensity_antitone hM 0 ht0 ht.2
      have k1 := intensity_antitone hM 1 hω' ht.1
      linarith
    have hderiv : ∀ t ∈ Set.Icc ω' ω, HasDerivAt (fun t => M.g 0 t / M.g 1 t)
        ((M.a 0 ![t, 1] 0 * M.g 1 t - M.g 0 t * M.a 1 ![t, 1] 0) / M.g 1 t ^ 2) t := by
      intro t ht
      have ht0 : 0 < t := lt_of_lt_of_le hω' ht.1
      exact (unitCost_hasDerivAt hM 0 ht0).div (unitCost_hasDerivAt hM 1 ht0)
        (c_pos hM 1 (relPrice_pos ht0)).ne'
    have hmono : StrictMonoOn (fun t => M.g 0 t / M.g 1 t) (Set.Icc ω' ω) := by
      refine strictMonoOn_of_deriv_pos (convex_Icc ω' ω)
        (fun t ht => (hderiv t ht).continuousAt.continuousWithinAt) fun t ht => ?_
      rw [interior_Icc] at ht
      have htI := Set.Ioo_subset_Icc_self ht
      have ht0 : 0 < t := lt_of_lt_of_le hω' htI.1
      rw [(hderiv t htI).deriv]
      have hpt := relPrice_pos ht0
      have hpp := hpos t htI
      rw [div_lt_div_iff₀ (hM.a_pos 1 _ 1 hpt) (hM.a_pos 0 _ 1 hpt)] at hpp
      apply div_pos _ (pow_pos (c_pos hM 1 hpt) 2)
      rw [g_eq, g_eq]
      nlinarith
    have hle := hmono.monotoneOn (Set.left_mem_Icc.2 hn) (Set.right_mem_Icc.2 hn) hn
    have e := c_ratio_eq_g hM hw
    have e' := c_ratio_eq_g hM hw'
    rw [← hωd] at e
    rw [← hωd'] at e'
    have : M.c 0 w / M.c 1 w < M.c 0 w' / M.c 1 w' := by
      rw [← hc 0, ← hc 1, ← hc' 0, ← hc' 1, hp1]
      exact div_lt_div_of_pos_right hp0 hp1pos
    rw [e, e'] at this
    linarith
  have e0 : p 0 = w 1 * M.g 0 ω := by rw [hc 0, c_eq_g hM 0 hw, hωd]
  have e1 : p 1 = w 1 * M.g 1 ω := by rw [hc 1, c_eq_g hM 1 hw, hωd]
  have e0' : p' 0 = w' 1 * M.g 0 ω' := by rw [hc' 0, c_eq_g hM 0 hw', hωd']
  have e1' : p 1 = w' 1 * M.g 1 ω' := by rw [← hp1, hc' 1, c_eq_g hM 1 hw', hωd']
  have hg0 : 0 < M.g 0 ω := c_pos hM 0 (relPrice_pos hω)
  have hg1 : 0 < M.g 1 ω := c_pos hM 1 (relPrice_pos hω)
  have hg0' : 0 < M.g 0 ω' := c_pos hM 0 (relPrice_pos hω')
  have hg1' : 0 < M.g 1 ω' := c_pos hM 1 (relPrice_pos hω')
  have hw1 := hw 1
  have hw1' := hw' 1
  have hp0pos : 0 < p 0 := by rw [e0]; positivity
  constructor
  · have hm := (div_g_strictMono hM 0).lt_iff_lt hω hω' |>.2 hlt
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
  · have hgm := (g_strictMono hM 1).lt_iff_lt hω hω' |>.2 hlt
    have hw1e : w 1 = p 1 / M.g 1 ω := by rw [e1]; field_simp
    have hw1e' : w' 1 = p 1 / M.g 1 ω' := by rw [e1']; field_simp
    rw [hw1e, hw1e']
    exact div_lt_div_of_pos_left hp1pos hg1 hgm

end TwoByTwo

theorem leontief_f0 (x : Fin 2 → ℝ) : leontiefModel.f 0 x = min (x 0 / 2) (x 1) := rfl

theorem leontief_f1 (x : Fin 2 → ℝ) : leontiefModel.f 1 x = min (x 0) (x 1 / 2) := rfl

/-- In the Leontief model with `z̄ = (3, 3)`, every allocation satisfies the full-employment bounds
`2q₁ + q₂ ≤ 3` and `q₁ + 2q₂ ≤ 3` on the outputs `qⱼ = fⱼ(zⱼ)`. -/
theorem leontief_output_bounds {z : Fin 2 → Fin 2 → ℝ} (hz : IsFactorAllocation ![3, 3] z) :
    2 * leontiefModel.f 0 (z 0) + leontiefModel.f 1 (z 1) ≤ 3 ∧
      leontiefModel.f 0 (z 0) + 2 * leontiefModel.f 1 (z 1) ≤ 3 := by
  obtain ⟨-, hsum⟩ := hz
  have s0 := congrFun hsum 0
  have s1 := congrFun hsum 1
  simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at s0 s1
  rw [leontief_f0, leontief_f1]
  have a1 := min_le_left (z 0 0 / 2) (z 0 1)
  have a2 := min_le_right (z 0 0 / 2) (z 0 1)
  have b1 := min_le_left (z 1 0) (z 1 1 / 2)
  have b2 := min_le_right (z 1 0) (z 1 1 / 2)
  constructor <;> linarith

/-- **Exercise 15.D.1(b)** (MWG, p. 533): false as printed for the model as formalized. In the
Leontief model (which satisfies all standing assumptions and the factor intensity condition) with
`z̄ = (3, 3)`, the Pareto set is not the diagonal (the diagonal allocation `((2, 2), (1, 1))`
producing `(1, 1/2)` is dominated), yet the two distinct allocations
`z = ((1, 1/2), (2, 5/2))` (outputs `(1/2, 5/4)`) and `z' = ((2, 1), (1, 2))` (outputs `(1, 1)`)
are both efficient and lie on the same ray from firm 1's origin (`z₁ = z'₁/2`). So a ray from an
origin can meet the Pareto set more than once. The corrected statement assumes differentiable
technologies (`TwoByTwo.exercise_15_D_1b`). -/
theorem exercise_15_D_1b_counterexample :
    leontiefModel.IsEfficientAllocation ![3, 3] ![![1, 1 / 2], ![2, 5 / 2]] ∧
      leontiefModel.IsEfficientAllocation ![3, 3] ![![2, 1], ![1, 2]] ∧
      (![![1, 1 / 2], ![2, 5 / 2]] : Fin 2 → Fin 2 → ℝ) 0 =
        (1 / 2 : ℝ) • (![![2, 1], ![1, 2]] : Fin 2 → Fin 2 → ℝ) 0 ∧
      (![![1, 1 / 2], ![2, 5 / 2]] : Fin 2 → Fin 2 → ℝ) ≠ ![![2, 1], ![1, 2]] ∧
      IsFactorAllocation ![3, 3] ![![2, 2], ![1, 1]] ∧
      (![![2, 2], ![1, 1]] : Fin 2 → Fin 2 → ℝ) 0 = (2 / 3 : ℝ) • ![3, 3] ∧
      ¬ leontiefModel.IsEfficientAllocation ![3, 3] ![![2, 2], ![1, 1]] := by
  have hA : IsFactorAllocation ![3, 3] ![![1, 1 / 2], ![2, 5 / 2]] :=
    ⟨fun j l => by fin_cases j <;> fin_cases l <;> norm_num,
      by funext l; fin_cases l <;> norm_num⟩
  have hB : IsFactorAllocation ![3, 3] ![![2, 1], ![1, 2]] :=
    ⟨fun j l => by fin_cases j <;> fin_cases l <;> norm_num,
      by funext l; fin_cases l <;> norm_num⟩
  have hD : IsFactorAllocation ![3, 3] ![![2, 2], ![1, 1]] :=
    ⟨fun j l => by fin_cases j <;> fin_cases l <;> norm_num,
      by funext l; fin_cases l <;> norm_num⟩
  have fA0 : leontiefModel.f 0 ![1, 1 / 2] = 1 / 2 := by rw [leontief_f0]; norm_num
  have fA1 : leontiefModel.f 1 ![2, 5 / 2] = 5 / 4 := by rw [leontief_f1]; norm_num [min_def]
  have fB0 : leontiefModel.f 0 ![2, 1] = 1 := by rw [leontief_f0]; norm_num
  have fB1 : leontiefModel.f 1 ![1, 2] = 1 := by rw [leontief_f1]; norm_num
  have fD0 : leontiefModel.f 0 ![2, 2] = 1 := by rw [leontief_f0]; norm_num [min_def]
  have fD1 : leontiefModel.f 1 ![1, 1] = 1 / 2 := by rw [leontief_f1]; norm_num [min_def]
  refine ⟨⟨hA, ?_⟩, ⟨hB, ?_⟩, ?_, ?_, hD, ?_, ?_⟩
  · rintro ⟨z', hz', hge, j, hlt⟩
    have hb := leontief_output_bounds hz'
    have g0 := hge 0
    have g1 := hge 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, fA0, fA1] at g0 g1
    fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero,
      Matrix.cons_val_one, fA0, fA1] at hlt <;> linarith
  · rintro ⟨z', hz', hge, j, hlt⟩
    have hb := leontief_output_bounds hz'
    have g0 := hge 0
    have g1 := hge 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, fB0, fB1] at g0 g1
    fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero,
      Matrix.cons_val_one, fB0, fB1] at hlt <;> linarith
  · funext l
    fin_cases l <;> norm_num
  · intro he
    have := congrFun (congrFun he 0) 0
    norm_num at this
  · funext l
    fin_cases l <;> norm_num
  · rintro ⟨-, hne⟩
    refine hne ⟨![![2, 1], ![1, 2]], hB, Fin.forall_fin_two.2 ⟨?_, ?_⟩, 1, ?_⟩ <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, fB0, fB1, fD0, fD1] <;> norm_num

/-- **Exercise 15.D.1(b)** (MWG, p. 533), corrected statement for the Cobb-Douglas model of
Exercise 15.D.8 (differentiable along rays): a ray from either firm's origin meets the interior
supported (= interior efficient) allocations off the diagonal at most once. -/
theorem exercise_15_D_1b_cdModel {zbar w q w' q' : Fin 2 → ℝ}
    (h : cdModel.IsInteriorSupport zbar w q) (h' : cdModel.IsInteriorSupport zbar w' q')
    (hne : cdModel.factorRatio 0 w ≠ cdModel.factorRatio 1 w) (j : Fin 2)
    (hray : cdModel.factorRatio j w = cdModel.factorRatio j w') :
    (fun k => q k • cdModel.a k w) = fun k => q' k • cdModel.a k w' :=
  TwoByTwo.exercise_15_D_1b cdModel_isModel (fun k => cdtModel_rayDifferentiable _ k) h h' hne j
    hray

/-- **Figure 15.D.2(b)** (MWG, p. 533), instance: in the Cobb-Douglas model of Exercise 15.D.8
every efficient allocation with both firms' inputs `≫ 0` is supported by common factor
prices. -/
theorem efficient_isSupported_cdModel {zbar : Fin 2 → ℝ} {z : Fin 2 → Fin 2 → ℝ}
    (h : cdModel.IsEfficientAllocation zbar z) (hint : ∀ j, StrictlyPositive (z j)) :
    cdModel.IsSupportedAllocation zbar z :=
  TwoByTwo.efficient_isSupported cdModel_isModel (cdtModel_raySurjective cdModel_alpha)
    (fun k => cdtModel_rayDifferentiable _ k) h hint

/-- **Footnote 16** (MWG, p. 536), non-vacuity: in the Leontief model with `z̄ = (3, 3)`, the
interior equilibria at `p = (3, 3)` (`w = (1, 1)`) and `p' = (4, 3)` (`w' = (5/3, 2/3)`), with
outputs `(1, 1)`, satisfy the hypotheses of `TwoByTwo.footnote_16`, which yields
`w'₁ > w₁` and `w'₂ < w₂`. -/
theorem footnote_16_leontief :
    IsFactorEqm leontiefModel.f ![3, 3] ![3, 3] ![1, 1]
        (fun j => (![1, 1] : Fin 2 → ℝ) j • leontiefModel.a j ![1, 1]) ∧
      IsFactorEqm leontiefModel.f ![4, 3] ![3, 3] ![5 / 3, 2 / 3]
        (fun j => (![1, 1] : Fin 2 → ℝ) j • leontiefModel.a j ![5 / 3, 2 / 3]) ∧
      leontiefModel.factorRatio 1 ![1, 1] < leontiefModel.factorRatio 0 ![1, 1] ∧
      (![1, 1] : Fin 2 → ℝ) 0 < (![5 / 3, 2 / 3] : Fin 2 → ℝ) 0 ∧
      (![5 / 3, 2 / 3] : Fin 2 → ℝ) 1 < (![1, 1] : Fin 2 → ℝ) 1 := by
  have hq : ∀ j, 0 < (![1, 1] : Fin 2 → ℝ) j := fun j => by fin_cases j <;> norm_num
  have h1 : IsFactorEqm leontiefModel.f ![3, 3] ![3, 3] ![1, 1]
      (fun j => (![1, 1] : Fin 2 → ℝ) j • leontiefModel.a j ![1, 1]) :=
    leontief_instances.2.2.1
  have hw' : StrictlyPositive (![5 / 3, 2 / 3] : Fin 2 → ℝ) := fun l => by
    fin_cases l <;> norm_num
  have h2 : IsFactorEqm leontiefModel.f ![4, 3] ![3, 3] ![5 / 3, 2 / 3]
      (fun j => (![1, 1] : Fin 2 → ℝ) j • leontiefModel.a j ![5 / 3, 2 / 3]) := by
    refine (TwoByTwo.interior_eqm_iff leontiefModel_isModel hw' hq).2
      ⟨fun j => (leontief_instances.2.1 j).symm, ?_⟩
    funext l
    fin_cases l <;> norm_num [leontiefModel, Fin.sum_univ_two]
  have h3 : leontiefModel.factorRatio 1 ![1, 1] < leontiefModel.factorRatio 0 ![1, 1] := by
    norm_num [TwoByTwo.factorRatio, leontiefModel]
  exact ⟨h1, h2, h3, TwoByTwo.footnote_16 leontiefModel_isModel h1 h2 hq hq (by norm_num)
    (by norm_num) h3⟩

end MWG.GeneralEquilibriumExamples
