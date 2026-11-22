/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGAggregateDemand.LawOfDemand
import MWGConsumerChoice.SamuelsonSufficiency
import MWGConsumerChoice.MatrixDefiniteness

/-!
# The Slutsky matrix of aggregate demand

MWG, Section 4.C, pp. 114-115, and Exercises 4.C.2, 4.C.8 and 4.C.9 (p. 124).

* `hasFDerivAt_shareDemand`: the derivative of `x(p, w) = ∑ᵢ xᵢ(p, αᵢ w)`, with
  `D_p x = ∑ᵢ D_p xᵢ` and `D_w x = ∑ᵢ αᵢ D_w xᵢ`.
* Equations (4.C.4)-(4.C.8) (`equation_4_C_4` ... `equation_4_C_8`, Exercise 4.C.8): the
  aggregate Slutsky matrix is `S = ∑ᵢ Sᵢ - C` with
  `C = ∑ᵢ αᵢ [D_w xᵢ - D_w x][(1/αᵢ) xᵢ - x]ᵀ`, a covariance matrix whose two "deviation"
  vectors have zero `α`-weighted means (`covariance_means_zero`).
* The sufficient condition (p. 114): if `C` is positive semidefinite and every `Sᵢ` is negative
  off the price ray, so is `S` (`slutsky_negative_of_cov_psd`); with the aggregate's
  homogeneity and Walras' law this gives the weak axiom (`weakAxiom_of_cov_psd`).
* The two cases of p. 115: equal wealth effects or proportional consumption give `C = 0`
  (`cov_zero_of_equal_wealth_effects`, `cov_zero_of_proportional_consumption`).
* Exercise 4.C.9: homothetic preferences give `C` positive semidefinite.
* Exercise 4.C.2: the differential versions of the ULD and the weak axiom give a version of
  Proposition 4.C.1 (`exercise_4_C_2`).
* p. 114 states that an individual Slutsky matrix always has `dp·Sᵢ dp < 0` for `dp` not
  proportional to `p`. This is false: the Leontief demand `x(p, w) = w/(p₁ + p₂) (1, 1)` has
  `S = 0` (`leontief_slutsky_zero`, correction 3). The sufficient condition is therefore stated
  with the extra hypothesis.
-/

namespace MWG.AggregateDemand

open MWG.ConsumerChoice MWG.ClassicalDemand Filter Topology

variable {L I : ℕ}

/-- The linear map `(p, w) ↦ (p, a w)`. -/
noncomputable def scaleWealthCLM (L : ℕ) (a : ℝ) :
    ((Fin L → ℝ) × ℝ) →L[ℝ] ((Fin L → ℝ) × ℝ) :=
  (ContinuousLinearMap.fst ℝ (Fin L → ℝ) ℝ).prod (a • ContinuousLinearMap.snd ℝ (Fin L → ℝ) ℝ)

/-- `(p, w) ↦ (p, a w)` applied. -/
theorem scaleWealthCLM_apply (a : ℝ) (q : (Fin L → ℝ) × ℝ) :
    scaleWealthCLM L a q = (q.1, a * q.2) := by
  simp [scaleWealthCLM]

/-- **Section 4.C** (MWG, p. 114). The derivative of aggregate demand
`x(p, w) = ∑ᵢ xᵢ(p, αᵢ w)` from the individual derivatives `Dᵢ` at `(p, αᵢ w)`. -/
theorem hasFDerivAt_shareDemand {xs : Fin I → DemandFunction L} {α : Fin I → ℝ}
    {p : Fin L → ℝ} {w : ℝ} {D : Fin I → ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)}
    (hD : ∀ i, HasFDerivAt (Function.uncurry (xs i)) (D i) (p, α i * w)) :
    HasFDerivAt (Function.uncurry (shareDemand xs α))
      (∑ i, (D i).comp (scaleWealthCLM L (α i))) (p, w) := by
  have h : ∀ i ∈ Finset.univ, HasFDerivAt
      (fun q : (Fin L → ℝ) × ℝ => Function.uncurry (xs i) (scaleWealthCLM L (α i) q))
      ((D i).comp (scaleWealthCLM L (α i))) (p, w) := by
    intro i _
    have hl := (scaleWealthCLM L (α i)).hasFDerivAt (x := (p, w))
    have hDi : HasFDerivAt (Function.uncurry (xs i)) (D i) (scaleWealthCLM L (α i) (p, w)) := by
      rw [scaleWealthCLM_apply]
      exact hD i
    exact hDi.comp (p, w) hl
  have hs := HasFDerivAt.sum h
  convert hs using 1
  funext q
  simp only [shareDemand, Function.uncurry, scaleWealthCLM_apply, Finset.sum_apply]

/-- **Section 4.C** (MWG, p. 114). `D_p x(p, w) = ∑ᵢ D_p xᵢ(p, αᵢ w)`. -/
theorem priceJacobian_shareDemand (α : Fin I → ℝ)
    (D : Fin I → ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)) :
    priceJacobian (∑ i, (D i).comp (scaleWealthCLM L (α i))) = ∑ i, priceJacobian (D i) := by
  ext l k
  simp [priceJacobian, priceEffect, scaleWealthCLM_apply, Matrix.sum_apply]

/-- **Section 4.C** (MWG, p. 114). `D_w x(p, w) = ∑ᵢ αᵢ D_w xᵢ(p, αᵢ w)`. -/
theorem wealthJacobian_shareDemand (α : Fin I → ℝ)
    (D : Fin I → ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)) :
    wealthJacobian (∑ i, (D i).comp (scaleWealthCLM L (α i))) =
      ∑ i, α i • wealthJacobian (D i) := by
  funext l
  have : ∀ i, (D i) ((0 : Fin L → ℝ), α i) = α i • (D i) (0, 1) := by
    intro i
    rw [← map_smul]
    simp
  simp [wealthJacobian, wealthEffect, scaleWealthCLM_apply, Finset.sum_apply, this]

/-- **Equation (4.C.8)** (MWG, p. 114). The matrix
`C = ∑ᵢ αᵢ [D_w xᵢ - D_w x][(1/αᵢ) xᵢ - x]ᵀ` built from the individual wealth-effect vectors
`dwᵢ` and consumption vectors `xvᵢ`, with `D_w x = ∑ⱼ αⱼ dwⱼ` and `x = ∑ⱼ xvⱼ`. -/
noncomputable def covMatrix (α : Fin I → ℝ) (dw xv : Fin I → Fin L → ℝ) :
    Matrix (Fin L) (Fin L) ℝ :=
  ∑ i, α i • Matrix.vecMulVec (dw i - ∑ j, α j • dw j) ((α i)⁻¹ • xv i - ∑ j, xv j)

/-- **Section 4.C** (MWG, p. 114). The two deviation vectors in `C` have zero weighted means:
`∑ᵢ αᵢ [D_w xᵢ - D_w x] = 0` and `∑ᵢ αᵢ [(1/αᵢ) xᵢ - x] = 0`. -/
theorem covariance_means_zero {α : Fin I → ℝ} (hα : ∀ i, α i ≠ 0) (hα1 : ∑ i, α i = 1)
    (dw xv : Fin I → Fin L → ℝ) :
    ∑ i, α i • (dw i - ∑ j, α j • dw j) = 0 ∧
      ∑ i, α i • ((α i)⁻¹ • xv i - ∑ j, xv j) = 0 := by
  constructor
  · simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hα1, one_smul, sub_self]
  · simp only [smul_sub, smul_smul, mul_inv_cancel₀ (hα _), one_smul, Finset.sum_sub_distrib,
      ← Finset.sum_smul, hα1, sub_self]

/-- **Equations (4.C.7)-(4.C.8)** (MWG, p. 114), the algebraic core. For any matrices `Dpᵢ`,
wealth-effect vectors `dwᵢ`, bundles `xvᵢ` and shares `αᵢ ≠ 0` with `∑ αᵢ = 1`:
`(∑ᵢ Dpᵢ + (∑ᵢ αᵢ dwᵢ)(∑ᵢ xvᵢ)ᵀ) = ∑ᵢ (Dpᵢ + dwᵢ xvᵢᵀ) - C`. -/
theorem slutsky_aggregate_algebra {α : Fin I → ℝ} (hα : ∀ i, α i ≠ 0) (hα1 : ∑ i, α i = 1)
    (Dp : Fin I → Matrix (Fin L) (Fin L) ℝ) (dw xv : Fin I → Fin L → ℝ) :
    (∑ i, Dp i) + Matrix.vecMulVec (∑ i, α i • dw i) (∑ i, xv i) =
      ∑ i, (Dp i + Matrix.vecMulVec (dw i) (xv i)) - covMatrix α dw xv := by
  ext l k
  simp only [covMatrix, Matrix.add_apply, Matrix.sub_apply, Matrix.sum_apply,
    Matrix.vecMulVec_apply, Matrix.smul_apply, Finset.sum_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul, Finset.sum_add_distrib]
  have h1 : ∀ i, α i * ((dw i l - ∑ j, α j * dw j l) * ((α i)⁻¹ * xv i k - ∑ j, xv j k)) =
      dw i l * xv i k - α i * dw i l * ∑ j, xv j k - (∑ j, α j * dw j l) * xv i k +
        α i * ((∑ j, α j * dw j l) * ∑ j, xv j k) := by
    intro i
    have := hα i
    field_simp
    ring
  rw [Finset.sum_congr rfl fun i _ => h1 i]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
    hα1]
  rw [Finset.sum_mul]
  ring

/-- **Equations (4.C.4)-(4.C.5)** (MWG, p. 114). The Slutsky matrix of aggregate demand is
`S(p, w) = D_p x(p, w) + D_w x(p, w) x(p, w)ᵀ` with `D_w x = ∑ᵢ αᵢ D_w xᵢ(p, αᵢ w)`. -/
theorem equation_4_C_4_5 (α : Fin I → ℝ) (D : Fin I → ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ))
    (x : Fin L → ℝ) :
    slutskyMatrix (∑ i, (D i).comp (scaleWealthCLM L (α i))) x =
      ∑ i, priceJacobian (D i) + Matrix.vecMulVec (∑ i, α i • wealthJacobian (D i)) x := by
  rw [slutskyMatrix_eq, priceJacobian_shareDemand, wealthJacobian_shareDemand]

/-- **Equation (4.C.6)** (MWG, p. 114). Adding the individual Slutsky equations:
`∑ᵢ Sᵢ = ∑ᵢ D_p xᵢ + ∑ᵢ D_w xᵢ xᵢᵀ`. -/
theorem equation_4_C_6 (D : Fin I → ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ))
    (xv : Fin I → Fin L → ℝ) :
    ∑ i, slutskyMatrix (D i) (xv i) =
      ∑ i, priceJacobian (D i) + ∑ i, Matrix.vecMulVec (wealthJacobian (D i)) (xv i) := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => slutskyMatrix_eq (D i) (xv i)

/-- **Equation (4.C.7)** (MWG, p. 114; Exercise 4.C.8, p. 124). With shares `αᵢ ≠ 0`,
`∑ αᵢ = 1`, individual derivatives `Dᵢ` at `(p, αᵢ w)` and bundles `xvᵢ = xᵢ(p, αᵢ w)`, the
aggregate Slutsky matrix is
`S(p, w) = ∑ᵢ Sᵢ(p, αᵢ w) - ∑ᵢ αᵢ [D_w xᵢ - D_w x][(1/αᵢ) xᵢ - x]ᵀ`. -/
theorem equation_4_C_7 {α : Fin I → ℝ} (hα : ∀ i, α i ≠ 0) (hα1 : ∑ i, α i = 1)
    (D : Fin I → ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)) (xv : Fin I → Fin L → ℝ) :
    slutskyMatrix (∑ i, (D i).comp (scaleWealthCLM L (α i))) (∑ i, xv i) =
      ∑ i, slutskyMatrix (D i) (xv i) - covMatrix α (fun i => wealthJacobian (D i)) xv := by
  rw [equation_4_C_4_5, slutsky_aggregate_algebra hα hα1]
  congr 1

/-- **Exercise 4.C.8** (MWG, p. 124). Derivation of (4.C.7) for actual demand functions: if each
`xᵢ` has derivative `Dᵢ` at `(p, αᵢ w)`, then aggregate demand has a derivative `D` at `(p, w)`
whose Slutsky matrix is `∑ᵢ Sᵢ(p, αᵢ w) - C(p, w)`. -/
theorem exercise_4_C_8 {xs : Fin I → DemandFunction L} {α : Fin I → ℝ} (hα : ∀ i, α i ≠ 0)
    (hα1 : ∑ i, α i = 1) {p : Fin L → ℝ} {w : ℝ}
    {D : Fin I → ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)}
    (hD : ∀ i, HasFDerivAt (Function.uncurry (xs i)) (D i) (p, α i * w)) :
    ∃ Dx, HasFDerivAt (Function.uncurry (shareDemand xs α)) Dx (p, w) ∧
      slutskyMatrix Dx (shareDemand xs α p w) =
        ∑ i, slutskyMatrix (D i) (xs i p (α i * w)) -
          covMatrix α (fun i => wealthJacobian (D i)) (fun i => xs i p (α i * w)) :=
  ⟨_, hasFDerivAt_shareDemand hD, equation_4_C_7 hα hα1 D (fun i => xs i p (α i * w))⟩

/-- **Equation (4.C.8)** (MWG, p. 114). `C(p, w) = ∑ᵢ Sᵢ(p, αᵢ w) - S(p, w)`. -/
theorem equation_4_C_8 {α : Fin I → ℝ} (hα : ∀ i, α i ≠ 0) (hα1 : ∑ i, α i = 1)
    (D : Fin I → ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)) (xv : Fin I → Fin L → ℝ) :
    covMatrix α (fun i => wealthJacobian (D i)) xv =
      ∑ i, slutskyMatrix (D i) (xv i) -
        slutskyMatrix (∑ i, (D i).comp (scaleWealthCLM L (α i))) (∑ i, xv i) := by
  rw [equation_4_C_7 hα hα1]
  abel

/-- **Section 4.C** (MWG, p. 114). A sufficient condition: if every individual Slutsky matrix is
negative off the price ray and `C(p, w)` is positive semidefinite, then
`dp·S(p, w) dp < 0` for every `dp` not proportional to `p`. -/
theorem slutsky_negative_of_cov_psd {α : Fin I → ℝ} (hα : ∀ i, α i ≠ 0) (hα1 : ∑ i, α i = 1)
    (hI : 0 < I) (D : Fin I → ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)) (xv : Fin I → Fin L → ℝ)
    {p : Fin L → ℝ}
    (hSi : ∀ i, ∀ v : Fin L → ℝ, (∀ c : ℝ, v ≠ c • p) →
      v ⬝ᵥ Matrix.mulVec (slutskyMatrix (D i) (xv i)) v < 0)
    (hC : PosSemidefMWG (covMatrix α (fun i => wealthJacobian (D i)) xv)) (v : Fin L → ℝ)
    (hv : ∀ c : ℝ, v ≠ c • p) :
    v ⬝ᵥ Matrix.mulVec
      (slutskyMatrix (∑ i, (D i).comp (scaleWealthCLM L (α i))) (∑ i, xv i)) v < 0 := by
  rw [equation_4_C_7 hα hα1, Matrix.sub_mulVec, dotProduct_sub, Matrix.sum_mulVec,
    dotProduct_sum]
  have h1 : ∑ i, v ⬝ᵥ Matrix.mulVec (slutskyMatrix (D i) (xv i)) v < 0 := by
    have := Finset.sum_lt_sum_of_nonempty (s := Finset.univ) (g := fun _ => (0 : ℝ))
      ⟨⟨0, hI⟩, Finset.mem_univ _⟩ (fun i _ => hSi i v hv)
    simpa using this
  have h2 := hC v
  linarith

/-- **Section 4.C** (MWG, p. 115), case (i). If all consumers have the same wealth effects,
`C(p, w) = 0` (so `S = ∑ᵢ Sᵢ`). -/
theorem cov_zero_of_equal_wealth_effects {α : Fin I → ℝ} (hα1 : ∑ i, α i = 1)
    {dw xv : Fin I → Fin L → ℝ} {d : Fin L → ℝ} (hdw : ∀ i, dw i = d) :
    covMatrix α dw xv = 0 := by
  have : ∑ j, α j • dw j = d := by
    simp only [hdw, ← Finset.sum_smul, hα1, one_smul]
  have h0 : ∀ i, dw i - ∑ j, α j • dw j = 0 := by
    intro i
    rw [this, hdw, sub_self]
  simp [covMatrix, h0]

/-- **Section 4.C** (MWG, p. 115), case (ii). If all proportionate consumption vectors
`(1/αᵢ) xᵢ(p, αᵢ w)` are equal, `C(p, w) = 0`. -/
theorem cov_zero_of_proportional_consumption {α : Fin I → ℝ} (hα1 : ∑ i, α i = 1)
    {dw xv : Fin I → Fin L → ℝ} {y : Fin L → ℝ} (hxv : ∀ i, (α i)⁻¹ • xv i = y)
    (hα : ∀ i, α i ≠ 0) : covMatrix α dw xv = 0 := by
  have hx : ∀ i, xv i = α i • y := by
    intro i
    rw [← hxv i, smul_smul, mul_inv_cancel₀ (hα i), one_smul]
  have : ∑ j, xv j = y := by
    simp only [hx, ← Finset.sum_smul, hα1, one_smul]
  simp [covMatrix, this, hxv]

/-- **Exercise 4.C.9** (MWG, p. 124). If every consumer's demand is homogeneous of degree one in
wealth near `(p, αᵢ w)` (homothetic preferences), then `C(p, w)` is positive semidefinite:
`D_w xᵢ = xᵢ/(αᵢ w)`, so `C = (1/w) ∑ᵢ αᵢ (yᵢ - x)(yᵢ - x)ᵀ` with `yᵢ = xᵢ/αᵢ`. -/
theorem exercise_4_C_9 {xs : Fin I → DemandFunction L} {α : Fin I → ℝ} (hα : ∀ i, 0 < α i)
    {p : Fin L → ℝ} {w : ℝ} (hw : 0 < w)
    (hhd : ∀ i, ∀ t : ℝ, 0 < t → xs i p (t * (α i * w)) = t • xs i p (α i * w))
    {D : Fin I → ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)}
    (hD : ∀ i, HasFDerivAt (Function.uncurry (xs i)) (D i) (p, α i * w)) :
    PosSemidefMWG (covMatrix α (fun i => wealthJacobian (D i)) (fun i => xs i p (α i * w))) := by
  have hdw : ∀ i, wealthJacobian (D i) = w⁻¹ • ((α i)⁻¹ • xs i p (α i * w)) := by
    intro i
    rw [(proposition_4_C_2_differential (mul_pos (hα i) hw) (hhd i) (hD i)).1, smul_smul,
      mul_inv_rev, mul_comm]
  set y : Fin I → Fin L → ℝ := fun i => (α i)⁻¹ • xs i p (α i * w) with hy
  have hsumx : ∑ j, xs j p (α j * w) = ∑ j, α j • y j := by
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [y, smul_smul, mul_inv_cancel₀ (hα j).ne', one_smul]
  have hsumd : ∑ j, α j • wealthJacobian (D j) = w⁻¹ • ∑ j, α j • y j := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hdw j, smul_comm]
  intro v
  simp only [covMatrix, Matrix.sum_mulVec, dotProduct_sum, Matrix.smul_mulVec, dotProduct_smul,
    smul_eq_mul, dot_vecMulVec_mulVec]
  refine Finset.sum_nonneg fun i _ => ?_
  rw [hsumd, hsumx, hdw i]
  have : w⁻¹ • y i - w⁻¹ • ∑ j, α j • y j = w⁻¹ • (y i - ∑ j, α j • y j) := by rw [smul_sub]
  rw [this, dotProduct_smul, smul_eq_mul]
  have e : v ⬝ᵥ (y i - ∑ j, α j • y j) = (y i - ∑ j, α j • y j) ⬝ᵥ v := dotProduct_comm _ _
  rw [e]
  have := mul_nonneg (mul_nonneg (hα i).le (inv_pos.mpr hw).le)
    (mul_self_nonneg ((y i - ∑ j, α j • y j) ⬝ᵥ v))
  simpa [y, mul_assoc] using this

/-- **Exercise 4.C.2** (MWG, p. 124), the key step. If a differentiable demand function is
homogeneous of degree zero, satisfies Walras' law and `D_p x(p, w)` is negative definite, then
`v·S(p, w) v < 0` for every `v` not proportional to `p` (the differential version of the weak
axiom recalled from Section 2.F). -/
theorem slutsky_negative_of_negDef {x : DemandFunction L} (hH : HomogeneousZero x)
    (hW : WalrasLaw x) {p : Fin L → ℝ} {w : ℝ} (hd : PWDomain p w)
    {D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)} (hD : HasFDerivAt (Function.uncurry x) D (p, w))
    (hnd : NegDef (priceJacobian D)) (v : Fin L → ℝ) (hv : ∀ c : ℝ, v ≠ c • p) :
    v ⬝ᵥ Matrix.mulVec (slutskyMatrix D (x p w)) v < 0 := by
  obtain ⟨hpS, hSp⟩ := proposition_2_F_3 hH hW hd hD
  set S := slutskyMatrix D (x p w) with hS
  set c := (v ⬝ᵥ x p w) / w with hc
  set v' := v - c • p with hv'
  have hv'0 : v' ≠ 0 := by
    intro h
    exact hv c (sub_eq_zero.mp h)
  have hv'x : x p w ⬝ᵥ v' = 0 := by
    rw [hv', dotProduct_sub, dotProduct_smul, smul_eq_mul, dotProduct_comm (x p w) p,
      hW p w hd, hc, dotProduct_comm]
    field_simp [hd.2.ne']
    ring
  have hquad : v ⬝ᵥ Matrix.mulVec S v = v' ⬝ᵥ Matrix.mulVec S v' := by
    have hv_eq : v = v' + c • p := by rw [hv']; abel
    have hpv : p ⬝ᵥ Matrix.mulVec S v' = 0 := by
      rw [Matrix.dotProduct_mulVec, hpS, zero_dotProduct]
    rw [hv_eq, Matrix.mulVec_add, Matrix.mulVec_smul, hSp, smul_zero, add_zero, add_dotProduct,
      smul_dotProduct, hpv, smul_zero, add_zero]
  rw [hquad, hS, slutskyMatrix_eq, Matrix.add_mulVec, dotProduct_add, dot_vecMulVec_mulVec,
    hv'x, mul_zero, add_zero]
  exact hnd v' hv'0

/-- **Exercise 4.C.2** (MWG, p. 124). A version of Proposition 4.C.1 from the differential
versions of the ULD and of the weak axiom: if every consumer's demand is homogeneous of degree
zero, satisfies Walras' law, takes values in `ℝ^L_+`, is differentiable on the domain with
`D_p xᵢ` negative definite, then the aggregate `x(p, w) = ∑ᵢ xᵢ(p, αᵢ w)` (`αᵢ > 0`,
`∑ αᵢ = 1`) has `D_p x` negative definite and satisfies the weak axiom (via the sufficient
condition `v·S(p, w) v < 0` for `v` not proportional to `p`, MWG Chapter 2's
`samuelson_sufficiency`). -/
theorem exercise_4_C_2 (hI : 0 < I) {xs : Fin I → DemandFunction L} {α : Fin I → ℝ}
    (hα : ∀ i, 0 < α i) (hα1 : ∑ i, α i = 1) (hH : ∀ i, HomogeneousZero (xs i))
    (hW : ∀ i, WalrasLaw (xs i)) (hX : ∀ i, ValuesInOrthant (xs i))
    {D : Fin I → (Fin L → ℝ) → ℝ → ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)}
    (hD : ∀ i p w, PWDomain p w → HasFDerivAt (Function.uncurry (xs i)) (D i p w) (p, w))
    (hnd : ∀ i p w, PWDomain p w → NegDef (priceJacobian (D i p w))) :
    WeakAxiom (shareDemand xs α) := by
  have hpos : ∀ i (p : Fin L → ℝ) w, PWDomain p w → 0 < shareRule α i p w :=
    fun i _ _ hd => mul_pos (hα i) hd.2
  have hHa : HomogeneousZero (shareDemand xs α) :=
    ruleDemand_homogeneousZero hH hpos fun i p w a _ _ => mul_left_comm (α i) a w
  have hWa : WalrasLaw (shareDemand xs α) :=
    ruleDemand_walrasLaw hW (isWealthDistributionRule_shareRule hα1) hpos
  have hXa : ValuesInOrthant (shareDemand xs α) := by
    intro p w hd l
    simp only [shareDemand, Finset.sum_apply]
    exact Finset.sum_nonneg fun i _ => hX i p (α i * w) ⟨hd.1, mul_pos (hα i) hd.2⟩ l
  have hDa : ∀ p w, PWDomain p w → HasFDerivAt (Function.uncurry (shareDemand xs α))
      (∑ i, (D i p (α i * w)).comp (scaleWealthCLM L (α i))) (p, w) := fun p w hd =>
    hasFDerivAt_shareDemand fun i => hD i p (α i * w) ⟨hd.1, mul_pos (hα i) hd.2⟩
  have hnda : ∀ p w, PWDomain p w →
      NegDef (priceJacobian (∑ i, (D i p (α i * w)).comp (scaleWealthCLM L (α i)))) := by
    intro p w hd v hv
    rw [priceJacobian_shareDemand, Matrix.sum_mulVec, dotProduct_sum]
    have := Finset.sum_lt_sum_of_nonempty (s := Finset.univ) (g := fun _ => (0 : ℝ))
      ⟨⟨0, hI⟩, Finset.mem_univ _⟩
      (fun i _ => hnd i p (α i * w) ⟨hd.1, mul_pos (hα i) hd.2⟩ v hv)
    simpa using this
  apply samuelson_sufficiency hHa hWa hXa fun p w hd => (hDa p w hd).differentiableAt
  intro p w hd v hv
  rw [(hDa p w hd).fderiv]
  exact slutsky_negative_of_negDef hHa hWa hd (hDa p w hd) (hnda p w hd) v hv

/-- **Section 4.C** (MWG, p. 114), sufficient condition, global form. If aggregate demand is
homogeneous of degree zero, satisfies Walras' law, takes values in `ℝ^L_+`, every consumer's
demand is differentiable with Slutsky matrix negative off the price ray, and `C(p, w)` is
positive semidefinite at every `(p, w)`, then aggregate demand satisfies the weak axiom. -/
theorem weakAxiom_of_cov_psd (hI : 0 < I) {xs : Fin I → DemandFunction L} {α : Fin I → ℝ}
    (hα : ∀ i, 0 < α i) (hα1 : ∑ i, α i = 1) (hH : ∀ i, HomogeneousZero (xs i))
    (hW : ∀ i, WalrasLaw (xs i)) (hX : ∀ i, ValuesInOrthant (xs i))
    {D : Fin I → (Fin L → ℝ) → ℝ → ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)}
    (hD : ∀ i p w, PWDomain p w → HasFDerivAt (Function.uncurry (xs i)) (D i p w) (p, w))
    (hSi : ∀ i p w, PWDomain p w → ∀ v : Fin L → ℝ, (∀ c : ℝ, v ≠ c • p) →
      v ⬝ᵥ Matrix.mulVec (slutskyMatrix (D i p w) (xs i p w)) v < 0)
    (hC : ∀ p w, PWDomain p w → PosSemidefMWG (covMatrix α
      (fun i => wealthJacobian (D i p (α i * w))) (fun i => xs i p (α i * w)))) :
    WeakAxiom (shareDemand xs α) := by
  have hpos : ∀ i (p : Fin L → ℝ) w, PWDomain p w → 0 < shareRule α i p w :=
    fun i _ _ hd => mul_pos (hα i) hd.2
  have hHa : HomogeneousZero (shareDemand xs α) :=
    ruleDemand_homogeneousZero hH hpos fun i p w a _ _ => mul_left_comm (α i) a w
  have hWa : WalrasLaw (shareDemand xs α) :=
    ruleDemand_walrasLaw hW (isWealthDistributionRule_shareRule hα1) hpos
  have hXa : ValuesInOrthant (shareDemand xs α) := by
    intro p w hd l
    simp only [shareDemand, Finset.sum_apply]
    exact Finset.sum_nonneg fun i _ => hX i p (α i * w) ⟨hd.1, mul_pos (hα i) hd.2⟩ l
  have hDa : ∀ p w, PWDomain p w → HasFDerivAt (Function.uncurry (shareDemand xs α))
      (∑ i, (D i p (α i * w)).comp (scaleWealthCLM L (α i))) (p, w) := fun p w hd =>
    hasFDerivAt_shareDemand fun i => hD i p (α i * w) ⟨hd.1, mul_pos (hα i) hd.2⟩
  apply samuelson_sufficiency hHa hWa hXa fun p w hd => (hDa p w hd).differentiableAt
  intro p w hd v hv
  rw [(hDa p w hd).fderiv]
  exact slutsky_negative_of_cov_psd (fun i => (hα i).ne') hα1 hI _ _
    (fun i => hSi i p (α i * w) ⟨hd.1, mul_pos (hα i) hd.2⟩) (hC p w hd) v hv

/-! ### The Leontief demand: a zero Slutsky matrix -/

/-- **Section 4.C** (MWG, p. 114), correction. The book states that an individual Slutsky matrix
always satisfies `dp·Sᵢ(p, αᵢ w) dp < 0` for `dp` not proportional to `p`. The Leontief demand
`x(p, w) = w/(p₁ + p₂) (1, 1)` (generated by `min(x₁, x₂)`; MWG Chapter 2's `leontiefDemand`,
which satisfies the weak axiom) has the zero Slutsky matrix at every `(p, w)`, so
`dp·S dp = 0` for every `dp`. -/
theorem leontief_slutsky_zero {p : Fin 2 → ℝ} {w : ℝ} (hd : PWDomain p w) :
    ∃ D, HasFDerivAt (Function.uncurry leontiefDemand) D (p, w) ∧
      slutskyMatrix D (leontiefDemand p w) = 0 := by
  have hs : p 0 + p 1 ≠ 0 := (add_pos (hd.1 0) (hd.1 1)).ne'
  have hfun : Function.uncurry leontiefDemand =
      fun q : (Fin 2 → ℝ) × ℝ => fun _ : Fin 2 => q.2 / (q.1 0 + q.1 1) := by
    funext q
    rfl
  have hdiff : DifferentiableAt ℝ (Function.uncurry leontiefDemand) (p, w) := by
    rw [hfun]
    fun_prop (disch := exact hs)
  refine ⟨_, hdiff.hasFDerivAt, ?_⟩
  -- along a compensated path the Leontief demand is constant, so `S v = D(v, v·x) = 0`
  have hSv : ∀ v : Fin 2 → ℝ,
      Matrix.mulVec (slutskyMatrix (fderiv ℝ (Function.uncurry leontiefDemand) (p, w))
        (leontiefDemand p w)) v = 0 := by
    intro v
    rw [slutskyMatrix_mulVec]
    have hpath := hasDerivAt_path hdiff.hasFDerivAt v (v ⬝ᵥ leontiefDemand p w)
    have hev : (fun t : ℝ => leontiefDemand (p + t • v) (w + t * (v ⬝ᵥ leontiefDemand p w)))
        =ᶠ[𝓝 0] fun _ => leontiefDemand p w := by
      have hc : Continuous fun t : ℝ => (p + t • v) 0 + (p + t • v) 1 := by fun_prop
      have := hc.tendsto 0
      simp only [zero_smul, add_zero] at this
      filter_upwards [this.eventually (isOpen_ne.mem_nhds hs)] with t ht
      funext l
      simp only [leontiefDemand, dotProduct, Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul] at ht ⊢
      field_simp
      ring
    have h0 := (hasDerivAt_const (0 : ℝ) (leontiefDemand p w)).congr_of_eventuallyEq hev
    exact hpath.unique h0
  ext l k
  have := congrFun (hSv (Pi.single k 1)) l
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this

end MWG.AggregateDemand
