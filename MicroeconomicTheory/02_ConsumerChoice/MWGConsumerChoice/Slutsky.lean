/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGConsumerChoice.Aggregation
import MWGConsumerChoice.WeakAxiom
import MWGConsumerChoice.MatrixDefiniteness
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# The Slutsky substitution matrix

MWG, Section 2.F, pp. 33–35, and Exercises 2.F.5, 2.F.7, 2.F.8, 2.F.9(b) and 2.F.11
(pp. 38–39).

* The Slutsky matrix `S(p, w)` with entries
  `s_ℓk = ∂x_ℓ/∂p_k + (∂x_ℓ/∂w) x_k` (2.F.10); `S v = D(v, v·x)` is the derivative of demand
  along a compensated price path (2.F.6)–(2.F.8).
* Proposition 2.F.2: under Walras' law and the weak axiom, `S(p, w)` is negative
  semidefinite. The book's differential argument ((2.F.5)–(2.F.9)) is made rigorous with the
  compensated path `t ↦ (p + t v, p·x(p,w) + t v·x(p, w))` and one-sided difference quotients.
  Homogeneity, assumed in the book, is not used. Consequences: `s_ℓℓ ≤ 0`, and a Giffen good
  is inferior (p. 34).
* Proposition 2.F.3 (= Exercise 2.F.7): `p·S(p, w) = 0` and `S(p, w) p = 0`; hence `S` is
  singular and not negative definite (p. 35).
* Exercise 2.F.11 and the remark on p. 34: for `L = 2` the Slutsky matrix is symmetric.
* Exercise 2.F.9(b): for `L = 2` and `S` of rank 1, negative semidefiniteness is equivalent to
  a negative diagonal entry.
* Exercise 2.F.5: homogeneity of degree one in wealth gives the law of demand for
  uncompensated price changes (both the finite and the infinitesimal versions).
* Exercise 2.F.8: substitution terms in elasticity form.
-/

namespace MWG.ConsumerChoice

open Filter Topology

/-- **Section 2.F** (MWG, p. 34), equation (2.F.10). The Slutsky (substitution) matrix
`s_ℓk = ∂x_ℓ/∂p_k + (∂x_ℓ/∂w) x_k`, from a derivative `D` and the bundle `x(p, w)`. -/
def slutskyMatrix {L : ℕ} (D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)) (xv : Fin L → ℝ) :
    Matrix (Fin L) (Fin L) ℝ :=
  Matrix.of fun l k => priceEffect D l k + wealthEffect D l * xv k

/-- Equation (2.F.8) (MWG, p. 33): `S = D_p x + D_w x xᵀ`. -/
theorem slutskyMatrix_eq {L : ℕ} (D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)) (xv : Fin L → ℝ) :
    slutskyMatrix D xv = priceJacobian D + Matrix.vecMulVec (wealthJacobian D) xv := by
  ext l k
  simp [slutskyMatrix, priceJacobian, wealthJacobian, Matrix.vecMulVec]

/-- Equations (2.F.6)–(2.F.8) (MWG, p. 33): `S v = D(v, v·x)`, the derivative of demand in the
compensated direction `dp = v`, `dw = x·dp`. -/
theorem slutskyMatrix_mulVec {L : ℕ} (D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ))
    (xv v : Fin L → ℝ) : Matrix.mulVec (slutskyMatrix D xv) v = D (v, v ⬝ᵥ xv) := by
  funext l
  rw [deriv_apply_eq]
  simp only [Matrix.mulVec, dotProduct, slutskyMatrix, Matrix.of_apply]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- A real function with derivative `g'` at `0` that does not exceed `g 0` immediately to the
right of `0` has `g' ≤ 0`. -/
theorem hasDerivAt_nonpos_of_right_le {g : ℝ → ℝ} {g' : ℝ} (hg : HasDerivAt g g' 0)
    (h : ∀ᶠ t in 𝓝[>] (0 : ℝ), g t ≤ g 0) : g' ≤ 0 := by
  have hs := hasDerivAt_iff_tendsto_slope.mp hg
  have hs' : Tendsto (slope g 0) (𝓝[>] 0) (𝓝 g') :=
    hs.mono_left (nhdsWithin_mono _ fun t ht => ne_of_gt ht)
  apply le_of_tendsto hs'
  filter_upwards [h, self_mem_nhdsWithin] with t ht htpos
  rw [slope_def_field]
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by simp only [sub_zero]; exact htpos.le)

/-- **Proposition 2.F.2** (MWG, p. 34). If a differentiable Walrasian demand function satisfies
Walras' law and the weak axiom, then at any `(p, w)` the Slutsky matrix is negative
semidefinite: `v·S(p, w) v ≤ 0` for all `v ∈ ℝ^L`. (The book also assumes homogeneity of
degree zero; it is not needed.) -/
theorem proposition_2_F_2 {L : ℕ} {x : DemandFunction L} (hW : WalrasLaw x)
    (hWA : WeakAxiom x) {p : Fin L → ℝ} {w : ℝ} (hd : PWDomain p w)
    {D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)} (hD : HasFDerivAt (Function.uncurry x) D (p, w))
    (v : Fin L → ℝ) : v ⬝ᵥ Matrix.mulVec (slutskyMatrix D (x p w)) v ≤ 0 := by
  rw [slutskyMatrix_mulVec]
  set c := v ⬝ᵥ x p w with hc
  have hpath := hasDerivAt_path hD v c
  have hg : HasDerivAt (fun t : ℝ => v ⬝ᵥ x (p + t • v) (w + t * c)) (v ⬝ᵥ D (v, c)) 0 := by
    have := HasDerivAt.fun_sum (u := Finset.univ) (fun l _ =>
      (hasDerivAt_pi.mp hpath l).const_mul (v l))
    simpa [dotProduct] using this
  apply hasDerivAt_nonpos_of_right_le hg
  have hdom := eventually_pwDomain hd v c
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds hdom, self_mem_nhdsWithin]
    with t ht htpos
  have hpt : StrictlyPositive (p + t • v) := ht.1
  have hcw : compensatedWealth x p w (p + t • v) = w + t * c := by
    simp only [compensatedWealth, add_dotProduct, smul_dotProduct, smul_eq_mul, hW p w hd, hc]
  obtain ⟨hle, _⟩ := proposition_2_F_1_i hW hWA p w (p + t • v) hd hpt (by rw [hcw]; exact ht.2)
  rw [hcw, add_sub_cancel_left, smul_dotProduct, smul_eq_mul] at hle
  have hle' : v ⬝ᵥ (x (p + t • v) (w + t * c) - x p w) ≤ 0 := by
    by_contra hcon
    push Not at hcon
    have := mul_pos (show (0 : ℝ) < t from htpos) hcon
    linarith
  simp only [zero_smul, add_zero, zero_mul]
  rw [dotProduct_sub, sub_nonpos] at hle'
  exact hle'

/-- **Section 2.F** (MWG, p. 34). Under the hypotheses of Proposition 2.F.2, the substitution
effect of good `ℓ` with respect to its own price is nonpositive: `s_ℓℓ(p, w) ≤ 0`. -/
theorem slutsky_diag_nonpos {L : ℕ} {x : DemandFunction L} (hW : WalrasLaw x)
    (hWA : WeakAxiom x) {p : Fin L → ℝ} {w : ℝ} (hd : PWDomain p w)
    {D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)} (hD : HasFDerivAt (Function.uncurry x) D (p, w))
    (l : Fin L) : slutskyMatrix D (x p w) l l ≤ 0 := by
  have h := proposition_2_F_2 hW hWA hd hD (Pi.single l 1)
  simpa [Matrix.mulVec_single, single_dotProduct] using h

/-- **Section 2.F** (MWG, p. 34). A good can be a Giffen good at `(p, w)` only if it is
inferior there: if `∂x_ℓ/∂p_ℓ > 0` then `∂x_ℓ/∂w < 0` (demand in `ℝ^L_+`). -/
theorem giffen_imp_inferior {L : ℕ} {x : DemandFunction L} (hW : WalrasLaw x)
    (hWA : WeakAxiom x) (hX : ValuesInOrthant x) {p : Fin L → ℝ} {w : ℝ} (hd : PWDomain p w)
    {D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)} (hD : HasFDerivAt (Function.uncurry x) D (p, w))
    (l : Fin L) (hG : 0 < priceEffect D l l) : wealthEffect D l < 0 := by
  have h := slutsky_diag_nonpos hW hWA hd hD l
  simp only [slutskyMatrix, Matrix.of_apply] at h
  have hx := hX p w hd l
  by_contra hcon
  push Not at hcon
  nlinarith [mul_nonneg hcon hx]

/-- **Proposition 2.F.3** (MWG, p. 35). If a differentiable demand function is homogeneous of
degree zero and satisfies Walras' law, then `p·S(p, w) = 0` and `S(p, w) p = 0`. -/
theorem proposition_2_F_3 {L : ℕ} {x : DemandFunction L} (hH : HomogeneousZero x)
    (hW : WalrasLaw x) {p : Fin L → ℝ} {w : ℝ} (hd : PWDomain p w)
    {D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)} (hD : HasFDerivAt (Function.uncurry x) D (p, w)) :
    Matrix.vecMul p (slutskyMatrix D (x p w)) = 0 ∧
      Matrix.mulVec (slutskyMatrix D (x p w)) p = 0 := by
  constructor
  · funext k
    have h2 := proposition_2_E_2 hW hd hD k
    have h3 := proposition_2_E_3 hW hd hD
    simp only [Matrix.vecMul, dotProduct, slutskyMatrix, Matrix.of_apply, Pi.zero_apply,
      mul_add, Finset.sum_add_distrib]
    have : ∑ l, p l * (wealthEffect D l * x p w k) =
        (∑ l, p l * wealthEffect D l) * x p w k := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun l _ => by ring
    rw [this, h3, one_mul]
    linarith
  · rw [slutskyMatrix_mulVec, hW p w hd, homogeneous_deriv_identity hH hd hD]

/-- **Exercise 2.F.7** (MWG, p. 35): proof of Proposition 2.F.3 from Propositions 2.E.1–2.E.3.
-/
theorem exercise_2_F_7 {L : ℕ} {x : DemandFunction L} (hH : HomogeneousZero x)
    (hW : WalrasLaw x) {p : Fin L → ℝ} {w : ℝ} (hd : PWDomain p w)
    {D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)} (hD : HasFDerivAt (Function.uncurry x) D (p, w)) :
    Matrix.vecMul p (slutskyMatrix D (x p w)) = 0 ∧
      Matrix.mulVec (slutskyMatrix D (x p w)) p = 0 :=
  proposition_2_F_3 hH hW hd hD

/-- **Section 2.F** (MWG, p. 35). Under the hypotheses of Proposition 2.F.3 (with at least one
good), `S(p, w)` is singular. -/
theorem slutsky_det_eq_zero {L : ℕ} {x : DemandFunction L} (hH : HomogeneousZero x)
    (hW : WalrasLaw x) {p : Fin L → ℝ} {w : ℝ} (hd : PWDomain p w)
    {D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)} (hD : HasFDerivAt (Function.uncurry x) D (p, w))
    (l : Fin L) : (slutskyMatrix D (x p w)).det = 0 := by
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨p, fun h => ?_, (proposition_2_F_3 hH hW hd hD).2⟩
  have := hd.1 l
  rw [h] at this
  exact lt_irrefl _ this

/-- **Section 2.F** (MWG, p. 35). Under the hypotheses of Proposition 2.F.3 (with at least one
good), `S(p, w)` is not negative definite: `p·S(p, w) p = 0` with `p ≠ 0`. -/
theorem slutsky_not_negDef {L : ℕ} {x : DemandFunction L} (hH : HomogeneousZero x)
    (hW : WalrasLaw x) {p : Fin L → ℝ} {w : ℝ} (hd : PWDomain p w)
    {D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)} (hD : HasFDerivAt (Function.uncurry x) D (p, w))
    (l : Fin L) : ¬ NegDef (slutskyMatrix D (x p w)) := by
  intro h
  have hp : p ≠ 0 := fun h0 => by have := hd.1 l; rw [h0] at this; exact lt_irrefl _ this
  have := h p hp
  rw [(proposition_2_F_3 hH hW hd hD).2, dotProduct_zero] at this
  exact lt_irrefl _ this

/-- **Exercise 2.F.11** (MWG, p. 38), matrix form. A `2 × 2` matrix with `S p = 0` and
`p·S = 0` for some `p` with `p₂ ≠ 0` is symmetric. -/
theorem symmetric_of_two_by_two {S : Matrix (Fin 2) (Fin 2) ℝ} {p : Fin 2 → ℝ} (hp : p 1 ≠ 0)
    (h1 : Matrix.vecMul p S = 0) (h2 : Matrix.mulVec S p = 0) : S.IsSymm := by
  have a := congrFun h1 0
  have b := congrFun h2 0
  simp only [Matrix.vecMul, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.zero_apply] at a b
  have h01 : S 0 1 = S 1 0 := by
    have : p 1 * (S 0 1 - S 1 0) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hp
    · linarith
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply, h01]

/-- **Exercise 2.F.11** (MWG, p. 38) and the remark on p. 34. For `L = 2`, under the
hypotheses of Proposition 2.F.3, `S(p, w)` is symmetric. -/
theorem exercise_2_F_11 {x : DemandFunction 2} (hH : HomogeneousZero x) (hW : WalrasLaw x)
    {p : Fin 2 → ℝ} {w : ℝ} (hd : PWDomain p w) {D : ((Fin 2 → ℝ) × ℝ) →L[ℝ] (Fin 2 → ℝ)}
    (hD : HasFDerivAt (Function.uncurry x) D (p, w)) : (slutskyMatrix D (x p w)).IsSymm :=
  symmetric_of_two_by_two (hd.1 1).ne' (proposition_2_F_3 hH hW hd hD).1
    (proposition_2_F_3 hH hW hd hD).2

/-- **Exercise 2.F.9(b)** (MWG, p. 38). For `L = 2`, a matrix `S` with `S p = 0` and `p·S = 0`
for some `p ≫ 0` (as the Slutsky matrix, by Proposition 2.F.3) and of rank 1 is negative
semidefinite iff any diagonal entry is negative. -/
theorem exercise_2_F_9b {S : Matrix (Fin 2) (Fin 2) ℝ} {p : Fin 2 → ℝ}
    (hp : StrictlyPositive p) (h1 : Matrix.vecMul p S = 0) (h2 : Matrix.mulVec S p = 0)
    (hrank : S.rank = 1) :
    (NegSemidef S ↔ S 0 0 < 0) ∧ (NegSemidef S ↔ S 1 1 < 0) := by
  have hp0 := hp 0
  have hp1 := hp 1
  have a0 := congrFun h1 0
  have a1 := congrFun h1 1
  have b0 := congrFun h2 0
  have b1 := congrFun h2 1
  simp only [Matrix.vecMul, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.zero_apply]
    at a0 a1 b0 b1
  -- all entries are determined by `S 0 0`
  have e01 : S 0 1 = -(p 0 / p 1) * S 0 0 := by field_simp; linarith
  have e10 : S 1 0 = -(p 0 / p 1) * S 0 0 := by field_simp; linarith
  have e11 : S 1 1 = (p 0 / p 1) ^ 2 * S 0 0 := by
    field_simp
    have : p 1 * S 1 1 = -(p 0 * S 1 0) := by linarith
    rw [e10] at this
    field_simp at this
    nlinarith
  have hS0 : S 0 0 ≠ 0 := by
    intro h0
    have hz : S = 0 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h0, e01, e10, e11]
    rw [hz, Matrix.rank_zero] at hrank
    exact zero_ne_one hrank
  have hq : ∀ z : Fin 2 → ℝ, z ⬝ᵥ S.mulVec z = S 0 0 * (z 0 - (p 0 / p 1) * z 1) ^ 2 := by
    intro z
    simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_two, e01, e10, e11]
    ring
  have hns : NegSemidef S ↔ S 0 0 < 0 := by
    constructor
    · intro h
      have := h ![1, 0]
      have e : ((![1, 0] : Fin 2 → ℝ) 0 - p 0 / p 1 * (![1, 0] : Fin 2 → ℝ) 1) ^ 2 = 1 := by
        simp
      rw [hq, e, mul_one] at this
      exact lt_of_le_of_ne this hS0
    · intro h z
      rw [hq]
      exact mul_nonpos_of_nonpos_of_nonneg h.le (sq_nonneg _)
  refine ⟨hns, hns.trans ?_⟩
  rw [e11]
  have : 0 < (p 0 / p 1) ^ 2 := by positivity
  constructor
  · intro h; nlinarith
  · intro h
    by_contra hc
    push Not at hc
    nlinarith

/-- **Exercise 2.F.8** (MWG, p. 38). Substitution terms in elasticity form:
`s̃_ℓk = (p_k/x_ℓ) s_ℓk = ε_ℓk + ε_ℓw b_k`. -/
theorem exercise_2_F_8 {L : ℕ} (D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)) (p xv : Fin L → ℝ)
    {w : ℝ} (hw : w ≠ 0) (l k : Fin L) :
    p k / xv l * slutskyMatrix D xv l k =
      priceElasticity D p xv l k + wealthElasticity D w xv l * budgetShare p xv w k := by
  simp only [slutskyMatrix, Matrix.of_apply, priceElasticity, wealthElasticity, budgetShare]
  field_simp

/-- **Exercise 2.F.5** (MWG, p. 38). If a demand function satisfying the weak axiom, Walras'
law (with values in `ℝ^L_+`) is homogeneous of degree one in wealth, then the law of demand
holds for uncompensated price changes: `(p' - p)·[x(p', w) - x(p, w)] ≤ 0`. -/
theorem exercise_2_F_5 {L : ℕ} {x : DemandFunction L} (hW : WalrasLaw x) (hWA : WeakAxiom x)
    (hX : ValuesInOrthant x) (h1 : HomogeneousOneInWealth x) {p p' : Fin L → ℝ} {w : ℝ}
    (hd : PWDomain p w) (hp' : StrictlyPositive p') :
    (p' - p) ⬝ᵥ (x p' w - x p w) ≤ 0 := by
  have hw := hd.2
  have hd' : PWDomain p' w := ⟨hp', hw⟩
  have hcw : 0 < compensatedWealth x p w p' := compensatedWealth_pos hW hX hd hp'
  set a := compensatedWealth x p w p' / w with ha
  have ha0 : 0 < a := div_pos hcw hw
  have hcwa : compensatedWealth x p w p' = a * w := by rw [ha]; field_simp
  obtain ⟨hc, _⟩ := proposition_2_F_1_i hW hWA p w p' hd hp' hcw
  rw [hcwa, h1 p' w a hd' ha0] at hc
  have hWp := hW p w hd
  have hWp' := hW p' w hd'
  set b := p ⬝ᵥ x p' w / w with hb
  have hpx' : p ⬝ᵥ x p' w = b * w := by rw [hb]; field_simp
  have hp'x : p' ⬝ᵥ x p w = a * w := hcwa
  -- the compensated law gives `1 ≤ a b`
  have hab : w * (1 - a * b) ≤ 0 := by
    have : (p' - p) ⬝ᵥ (a • x p' w - x p w) = w * (1 - a * b) := by
      rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, dotProduct_smul, dotProduct_smul,
        smul_eq_mul, smul_eq_mul, hWp', hp'x, hpx', hWp]
      ring
    linarith
  have hab' : 1 ≤ a * b := by nlinarith
  have hb0 : 0 < b := by
    by_contra hb0
    push Not at hb0
    nlinarith
  have hexp : (p' - p) ⬝ᵥ (x p' w - x p w) = w * (2 - a - b) := by
    rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, hWp', hp'x, hpx', hWp]
    ring
  rw [hexp]
  have : 2 ≤ a + b := by nlinarith [sq_nonneg (a - b)]
  nlinarith

/-- **Exercise 2.F.5** (MWG, p. 38), infinitesimal version: under the same hypotheses and
differentiability, `dp·D_p x(p, w) dp ≤ 0` for every `dp`. -/
theorem exercise_2_F_5_infinitesimal {L : ℕ} {x : DemandFunction L} (hW : WalrasLaw x)
    (hWA : WeakAxiom x) (h1 : HomogeneousOneInWealth x) {p : Fin L → ℝ} {w : ℝ}
    (hd : PWDomain p w) {D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)}
    (hD : HasFDerivAt (Function.uncurry x) D (p, w)) (v : Fin L → ℝ) :
    v ⬝ᵥ Matrix.mulVec (priceJacobian D) v ≤ 0 := by
  have hS := proposition_2_F_2 hW hWA hd hD v
  have hDw := exercise_2_E_4_wealthJacobian h1 hd hD
  rw [slutskyMatrix_mulVec, deriv_apply_eq_mulVec, dotProduct_add, dotProduct_smul, hDw,
    dotProduct_smul, smul_eq_mul, smul_eq_mul] at hS
  have hw := hd.2
  have : 0 ≤ (v ⬝ᵥ x p w) * (w⁻¹ * (v ⬝ᵥ x p w)) := by
    rw [mul_left_comm]
    exact mul_nonneg (inv_nonneg.mpr hw.le) (mul_self_nonneg _)
  linarith

end MWG.ConsumerChoice
