/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPositiveEquilibriumTheory.ComparativeStatics
import MWGPositiveEquilibriumTheory.PriceEffectsEconomy

/-!
# Any first-order comparative statics effect is possible (MWG Proposition 17.G.1, p. 617)

Goods `1, …, L` with `L = n + 1`, prices normalized `p_L = 1`, `p = (p̂, 1)`. The parameter is the
vector `ω̂₁ ∈ ℝ^{L-1}` of the first consumer's endowments of goods `1, …, L - 1`.

**Proposition 17.G.1** (`proposition_17_G_1`). Given `p̂ ≫ 0`, `ω̂₁ ≥ 0` and a nonsingular
`(L - 1) × (L - 1)` matrix `B`, there is an exchange economy of `L + 1` consumers
(`cseEconomy E' ω̂₁`) in which the first consumer has the endowments `ω̂₁` (and one unit of good
`L`), with `ẑ(p̂; ω̂₁) = 0`, `ẑ(·; ω̂₁) = 0` regular at `p̂`, and an implicit solution function
`p(·)` with `Dp(ω̂₁) = B`.

The proof follows the book. The first consumer is Cobb-Douglas with equal exponents
(`cdUtility 1`); his `D_{ω̂₁} ẑ₁ = (1/L) p̂⁻¹ p̂ᵀ - I` (`cseM`) is nonsingular
(`cseM_det`: a strict normality condition, Exercise 17.G.1). The other `L` consumers come from
**Proposition 17.E.2** (`proposition_17_E_2`, now with a strict derivative), fitted to the
`L × L` matrix `cseA` whose `(L - 1) × (L - 1)` block is the required
`Â = -D_{ω̂₁} ẑ₁ B⁻¹ - D_p ẑ₁` (the bordering rows and columns make `Ap = 0`, `pᵀA = -z`: the
restrictions of Proposition 17.E.2 place no restriction on `Â`, `cseA_mulVec`, `cseA_vecMul`).
Then `D_p ẑ = -D_{ω̂₁} ẑ₁ B⁻¹` (17.G.2) and (17.G.1) gives `Dp(ω̂₁) = B`.

The economy is concrete: `cseZ` is the chapter's `excessDemand` of `cseEconomy E' ω̂₁`, truncated
and evaluated at `(p̂, 1)`, as a function of `(p̂, ω̂₁)`.
-/

namespace MWG.PositiveEquilibriumTheory

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.GeneralEquilibriumExamples Filter Topology

variable {n : ℕ}

/-! ### Preliminaries -/

/-- `p̂ ↦ (p̂, 1)` is strictly differentiable with derivative `v ↦ (v, 0)`. -/
theorem cse_hasStrictFDerivAt_normPrice (q : Fin n → ℝ) :
    HasStrictFDerivAt normPrice (inclCLM n) q := by
  have heq : (normPrice : (Fin n → ℝ) → Fin (n + 1) → ℝ) =
      fun q => inclCLM n q + Pi.single (Fin.last n) 1 := by
    funext q k
    refine Fin.lastCases ?_ (fun l => ?_) k
    · simp
    · simp [Fin.castSucc_ne_last]
  rw [heq]
  exact (inclCLM n).hasStrictFDerivAt.add_const _

theorem cse_normPrice_castSucc (q : Fin n → ℝ) (l : Fin n) : normPrice q (Fin.castSucc l) = q l :=
  Fin.snoc_castSucc (α := fun _ => ℝ) _ _ _

theorem cse_normPrice_last (q : Fin n → ℝ) : normPrice q (Fin.last n) = 1 :=
  Fin.snoc_last (α := fun _ => ℝ) _ _

/-- A matrix as a continuous linear map. -/
noncomputable def cseCLM (B : Matrix (Fin n) (Fin n) ℝ) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.mulVecLin B)

theorem cseCLM_apply (B : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) : cseCLM B v = B.mulVec v :=
  rfl

/-- If `T v = M v` for all `v`, the matrix of `T` is `M`. -/
theorem cse_toMatrix'_eq {T : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)} {M : Matrix (Fin n) (Fin n) ℝ}
    (h : ∀ v, T v = M.mulVec v) :
    LinearMap.toMatrix' (T : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) = M := by
  have : (T : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) = Matrix.toLin' M := by
    ext v; simp [h]
  rw [this, LinearMap.toMatrix'_toLin']

/-! ### The first consumer -/

/-- The first consumer's truncated excess demand `ẑ₁(p̂; ω̂)`: Cobb-Douglas with equal
exponents, endowment `(ω̂, 1)`: `ẑ₁ₗ = (1/L)(p̂·ω̂ + 1)/p̂ₗ - ω̂ₗ`. -/
noncomputable def cseG (x : (Fin n → ℝ) × (Fin n → ℝ)) : Fin n → ℝ :=
  fun l => ((n : ℝ) + 1)⁻¹ * ((∑ k, x.1 k * x.2 k + 1) / x.1 l) - x.2 l

theorem cseG_eq (q ω : Fin n → ℝ) :
    truncCLM n (cd1ED (fun _ => 1) (normPrice ω) (normPrice q)) = cseG (q, ω) := by
  funext l
  simp only [truncCLM, ContinuousLinearMap.pi_apply, ContinuousLinearMap.proj_apply, cd1ED,
    Pi.sub_apply, cdDemand, cseG, normPrice_dotProduct, cse_normPrice_castSucc,
    cse_normPrice_last, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one]
  push_cast
  ring

/-- `ẑ₁` is `C¹` where `p̂ ≫ 0`. -/
theorem cseG_contDiffAt {x : (Fin n → ℝ) × (Fin n → ℝ)} (hx : ∀ l, 0 < x.1 l) :
    ContDiffAt ℝ 1 cseG x := by
  refine contDiffAt_pi.2 fun l => ?_
  have hsum : ContDiffAt ℝ 1 (fun x : (Fin n → ℝ) × (Fin n → ℝ) => ∑ k, x.1 k * x.2 k + 1) x :=
    by fun_prop
  have hden : ContDiffAt ℝ 1 (fun x : (Fin n → ℝ) × (Fin n → ℝ) => x.1 l) x := by fun_prop
  have h2 : ContDiffAt ℝ 1 (fun x : (Fin n → ℝ) × (Fin n → ℝ) => x.2 l) x := by fun_prop
  exact (contDiffAt_const.mul (hsum.div hden (hx l).ne')).sub h2

/-- `D_{ω̂} ẑ₁ = diag(-1) + (1/L)(1/p̂) p̂ᵀ`. -/
noncomputable def cseM (q : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (fun _ => -1) + Matrix.vecMulVec (fun l => ((n : ℝ) + 1)⁻¹ / q l) q

/-- **Exercise 17.G.1** for the first consumer: `|D_{ω̂} ẑ₁| = (-1)^{L-1}/L ≠ 0`. -/
theorem cseM_det {q : Fin n → ℝ} (hq : ∀ l, 0 < q l) : (cseM q).det = (-1) ^ n / ((n : ℝ) + 1) := by
  rw [cseM, det_diagonal_add_vecMulVec _ _ _ (fun _ => by norm_num)]
  have : ∀ l, q l * (((n : ℝ) + 1)⁻¹ / q l / -1) = -((n : ℝ) + 1)⁻¹ := fun l => by
    field_simp [(hq l).ne']
  simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Finset.prod_const]
  field_simp
  ring

/-- `(cseM q) v = (1/L)(q·v)/qₗ - vₗ`. -/
theorem cseM_mulVec (q v : Fin n → ℝ) (l : Fin n) :
    (cseM q).mulVec v l = ((n : ℝ) + 1)⁻¹ / q l * ∑ k, q k * v k - v l := by
  simp only [cseM, Matrix.add_mulVec, Pi.add_apply, Matrix.mulVec_diagonal]
  simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Finset.mul_sum]
  ring_nf

/-- `ẑ₁(p̂; ω̂)` is affine in `ω̂` with linear part `cseM p̂`. -/
theorem cseG_omega (q : Fin n → ℝ) (hq : ∀ l, 0 < q l) (ω : Fin n → ℝ) :
    cseG (q, ω) = (cseM q).mulVec ω + fun l => ((n : ℝ) + 1)⁻¹ / q l := by
  funext l
  rw [Pi.add_apply, cseM_mulVec]
  simp only [cseG]
  have := (hq l).ne'
  field_simp
  ring

/-- The `ω̂`-part of the derivative of `ẑ₁` is `cseM p̂`. -/
theorem cseG_fderiv_inr {q : Fin n → ℝ} (hq : ∀ l, 0 < q l) (ω v : Fin n → ℝ) :
    fderiv ℝ cseG (q, ω) (0, v) = (cseM q).mulVec v := by
  have hd : HasFDerivAt cseG (fderiv ℝ cseG (q, ω)) (q, ω) :=
    ((cseG_contDiffAt (x := (q, ω)) hq).differentiableAt (by norm_num)).hasFDerivAt
  have h1 : HasFDerivAt (fun ω' => cseG (q, ω'))
      ((fderiv ℝ cseG (q, ω)).comp (ContinuousLinearMap.inr ℝ (Fin n → ℝ) (Fin n → ℝ))) ω :=
    hd.comp ω (hasFDerivAt_prodMk_right q ω)
  have h2 : HasFDerivAt (fun ω' => cseG (q, ω')) (cseCLM (cseM q)) ω := by
    have : (fun ω' => cseG (q, ω')) = fun ω' => cseCLM (cseM q) ω' +
        fun l => ((n : ℝ) + 1)⁻¹ / q l := by
      funext ω'; rw [cseG_omega q hq, cseCLM_apply]
    rw [this]
    exact (cseCLM (cseM q)).hasFDerivAt.add_const _
  have := congrArg (fun T : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) => T v) (h1.unique h2)
  simpa [cseCLM_apply] using this

/-! ### The bordered matrix of the other consumers -/

/-- The first `L - 1` rows: `Âᵢ` bordered by `-Âᵢ·p̂` (so that `Ap = 0`). -/
noncomputable def cseTop (Ah : Matrix (Fin n) (Fin n) ℝ) (q : Fin n → ℝ) (i : Fin n) :
    Fin (n + 1) → ℝ :=
  Fin.snoc (α := fun _ => ℝ) (Ah i) (-∑ j, Ah i j * q j)

/-- The `L × L` matrix with block `Â`, `Ap = 0` and `pᵀA = -z` at `p = (q, 1)`. -/
noncomputable def cseA (Ah : Matrix (Fin n) (Fin n) ℝ) (q : Fin n → ℝ) (z : Fin (n + 1) → ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Fin.snoc (α := fun _ => Fin (n + 1) → ℝ) (cseTop Ah q)
    (fun k => -z k - ∑ i, q i * cseTop Ah q i k)

theorem cseA_castSucc (Ah : Matrix (Fin n) (Fin n) ℝ) (q : Fin n → ℝ) (z : Fin (n + 1) → ℝ)
    (i : Fin n) : cseA Ah q z (Fin.castSucc i) = cseTop Ah q i :=
  Fin.snoc_castSucc (α := fun _ => Fin (n + 1) → ℝ) _ _ _

theorem cseA_last (Ah : Matrix (Fin n) (Fin n) ℝ) (q : Fin n → ℝ) (z : Fin (n + 1) → ℝ) :
    cseA Ah q z (Fin.last n) = fun k => -z k - ∑ i, q i * cseTop Ah q i k :=
  Fin.snoc_last (α := fun _ => Fin (n + 1) → ℝ) _ _

theorem cseTop_castSucc (Ah : Matrix (Fin n) (Fin n) ℝ) (q : Fin n → ℝ) (i j : Fin n) :
    cseTop Ah q i (Fin.castSucc j) = Ah i j :=
  Fin.snoc_castSucc (α := fun _ => ℝ) _ _ _

theorem cseTop_last (Ah : Matrix (Fin n) (Fin n) ℝ) (q : Fin n → ℝ) (i : Fin n) :
    cseTop Ah q i (Fin.last n) = -∑ j, Ah i j * q j :=
  Fin.snoc_last (α := fun _ => ℝ) _ _

theorem cseTop_dot (Ah : Matrix (Fin n) (Fin n) ℝ) (q : Fin n → ℝ) (i : Fin n) :
    cseTop Ah q i ⬝ᵥ normPrice q = 0 := by
  rw [dotProduct, Fin.sum_univ_castSucc]
  simp only [cseTop_castSucc, cseTop_last, cse_normPrice_castSucc, cse_normPrice_last, mul_one]
  ring

/-- **Proposition 17.E.2**'s first restriction: `A p = 0`. -/
theorem cseA_mulVec (Ah : Matrix (Fin n) (Fin n) ℝ) (q : Fin n → ℝ) {z : Fin (n + 1) → ℝ}
    (hz : normPrice q ⬝ᵥ z = 0) : (cseA Ah q z).mulVec (normPrice q) = 0 := by
  funext r
  refine Fin.lastCases ?_ (fun i => ?_) r
  · simp only [Matrix.mulVec, cseA_last, Pi.zero_apply]
    have h1 : (fun k => -z k - ∑ i, q i * cseTop Ah q i k) =
        -z - ∑ i, q i • cseTop Ah q i := by
      funext k; simp [Finset.sum_apply]
    rw [h1, sub_dotProduct, neg_dotProduct, dotProduct_comm, hz, sum_dotProduct]
    simp [cseTop_dot]
  · simp only [Matrix.mulVec, cseA_castSucc, Pi.zero_apply]
    exact cseTop_dot Ah q i

/-- **Proposition 17.E.2**'s second restriction: `pᵀ A = -z`. -/
theorem cseA_vecMul (Ah : Matrix (Fin n) (Fin n) ℝ) (q : Fin n → ℝ) (z : Fin (n + 1) → ℝ) :
    Matrix.vecMul (normPrice q) (cseA Ah q z) = -z := by
  funext k
  simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_castSucc, cse_normPrice_castSucc,
    cse_normPrice_last, cseA_castSucc, cseA_last, one_mul, Pi.neg_apply]
  ring

/-- The other consumers' truncated price effects at `(p̂, 1)`: `trunc(A (v, 0)) = Â v`. -/
theorem cseA_trunc (Ah : Matrix (Fin n) (Fin n) ℝ) (q : Fin n → ℝ) (z : Fin (n + 1) → ℝ)
    (v : Fin n → ℝ) : truncCLM n ((cseA Ah q z).mulVec (inclCLM n v)) = Ah.mulVec v := by
  funext l
  simp only [truncCLM, ContinuousLinearMap.pi_apply, ContinuousLinearMap.proj_apply,
    Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, cseA_castSucc, cseTop_castSucc,
    inclCLM_castSucc, inclCLM_last, mul_zero, add_zero]

/-! ### The economy -/

/-- **Proposition 17.G.1** (MWG, p. 617). The economy of `L + 1` consumers: the first (`none`) is
Cobb-Douglas with equal exponents on `ℝ^L₊` and endowment `(ω̂, 1)`; the others are those of
`E'`. -/
noncomputable def cseEconomy (E' : ExchangeEconomy (Fin (n + 1)) (n + 1)) (ω : Fin n → ℝ) :
    ExchangeEconomy (Option (Fin (n + 1))) (n + 1) where
  X := fun o => o.elim (nonnegOrthant (n + 1)) E'.X
  u := fun o => o.elim (cdUtility (fun _ => 1)) E'.u
  ω := fun o => o.elim (normPrice ω) E'.ω

/-- The excess demand of `cseEconomy` at `p ≫ 0` with `p·(ω̂, 1) ≥ 0`: the first consumer's
Cobb-Douglas excess demand plus that of `E'`. -/
theorem cse_excessDemand (E' : ExchangeEconomy (Fin (n + 1)) (n + 1)) {ω p : Fin (n + 1) → ℝ}
    {ωh : Fin n → ℝ} (hω : ω = normPrice ωh) (hp : ∀ l, 0 < p l) (hw : 0 ≤ p ⬝ᵥ ω) :
    excessDemand (cseEconomy E' ωh) p = cd1ED (fun _ => 1) ω p + excessDemand E' p := by
  subst hω
  unfold excessDemand
  rw [Fintype.sum_option]
  congr 1
  have hd : (cseEconomy E' ωh).demand none p =
      {cdDemand (fun _ => 1) p (p ⬝ᵥ normPrice ωh)} :=
    walrasianDemand_cobbDouglas (fun _ => one_pos) hp hw
  rw [indivExcessDemand, demandFn_eq _ hd]
  rfl

/-- **Proposition 17.G.1** (MWG, p. 617). The truncated aggregate excess demand
`ẑ(p̂; ω̂) = trunc z(p̂, 1)` of `cseEconomy E' ω̂`, as a function of `(p̂, ω̂)`. -/
noncomputable def cseZ (E' : ExchangeEconomy (Fin (n + 1)) (n + 1))
    (x : (Fin n → ℝ) × (Fin n → ℝ)) : Fin n → ℝ :=
  truncCLM n (excessDemand (cseEconomy E' x.2) (normPrice x.1))

/-- **Proposition 17.G.1** (MWG, p. 617). Given `p̂ ≫ 0`, the first consumer's endowments
`ω̂₁ ≥ 0` of the first `L - 1` goods and a nonsingular `(L - 1) × (L - 1)` matrix `B`, there is an
exchange economy formed by `L + 1` consumers (`cseEconomy E' ω̂₁`: the first is Cobb-Douglas
with endowment `(ω̂₁, 1)`; the other `L` have continuous, strongly monotone utilities on `ℝ^L₊`
and endowments `≫ 0`) such that `ẑ(p̂; ω̂₁) = 0`, `ẑ(·; ω̂₁) = 0` is regular at `p̂`
(`|D_p ẑ| ≠ 0`), and the system is locally solved by a function `p(·)` with `Dp(ω̂₁) = B`. -/
theorem proposition_17_G_1 {q ω : Fin n → ℝ} (hq : ∀ l, 0 < q l) (hω : ∀ l, 0 ≤ ω l)
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.det ≠ 0) :
    ∃ E' : ExchangeEconomy (Fin (n + 1)) (n + 1), (∀ i, E'.X i = nonnegOrthant (n + 1)) ∧
      (∀ i, StrictlyPositive (E'.ω i)) ∧
      (∀ i, Continuous (E'.u i) ∧ UtilityStronglyMonotone (E'.u i)) ∧
      cseZ E' (q, ω) = 0 ∧
      ∃ f' : (Fin n → ℝ) × (Fin n → ℝ) →L[ℝ] (Fin n → ℝ), HasStrictFDerivAt (cseZ E') f' (q, ω) ∧
        (f'.comp (ContinuousLinearMap.inl ℝ (Fin n → ℝ) (Fin n → ℝ))).det ≠ 0 ∧
        (∀ v, f' (v, 0) = (-(cseM q * B⁻¹)).mulVec v) ∧ (∀ v, f' (0, v) = (cseM q).mulVec v) ∧
        ∃ η : (Fin n → ℝ) → Fin n → ℝ, LocallySolvable (cseZ E') q ω η ∧
          HasStrictFDerivAt η (cseCLM B) ω := by
  set p := normPrice q with hpdef
  have hp : ∀ l, 0 < p l := normPrice_mem_posOrthant.2 hq
  have hu : IsUnit B.det := isUnit_iff_ne_zero.2 hB
  -- the first consumer
  set f1 := fderiv ℝ cseG (q, ω) with hf1
  have hG : HasStrictFDerivAt cseG f1 (q, ω) :=
    (cseG_contDiffAt (x := (q, ω)) hq).hasStrictFDerivAt (by norm_num)
  set P1 := LinearMap.toMatrix' ((f1.comp (ContinuousLinearMap.inl ℝ (Fin n → ℝ)
    (Fin n → ℝ)) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) with hP1
  have hP1v : ∀ v, f1 (v, 0) = P1.mulVec v := fun v => by
    rw [hP1, LinearMap.toMatrix'_mulVec]; rfl
  -- the target block and the other consumers
  set Ah := -(cseM q * B⁻¹) - P1 with hAh
  set zt : Fin (n + 1) → ℝ := -cd1ED (fun _ => 1) (normPrice ω) p with hzt
  have hwealth : 0 ≤ p ⬝ᵥ normPrice ω := by
    rw [hpdef, normPrice_dotProduct]
    have := Finset.sum_nonneg fun k (_ : k ∈ Finset.univ) => mul_nonneg (hq k).le (hω k)
    rw [cse_normPrice_last]
    simp only [cse_normPrice_castSucc]
    linarith
  have hzt0 : p ⬝ᵥ zt = 0 := by
    rw [hzt, dotProduct_neg, cd1ED, dotProduct_sub,
      dotProduct_cdDemand (fun _ => one_pos) hp, sub_self, neg_zero]
  obtain ⟨E', hX, hωpos, hu', hz', D', hD', hDv⟩ := proposition_17_E_2 hp (cseA Ah q zt) hzt0
    (cseA_mulVec Ah q hzt0) (cseA_vecMul Ah q zt)
  -- the derivative of the other consumers' part
  set R : (Fin n → ℝ) × (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
    (truncCLM n).comp (D'.comp ((inclCLM n).comp
      (ContinuousLinearMap.fst ℝ (Fin n → ℝ) (Fin n → ℝ)))) with hR
  have hRd : HasStrictFDerivAt (fun x : (Fin n → ℝ) × (Fin n → ℝ) =>
      truncCLM n (excessDemand E' (normPrice x.1))) R (q, ω) :=
    (truncCLM n).hasStrictFDerivAt.comp (q, ω) (hD'.comp (q, ω)
      ((cse_hasStrictFDerivAt_normPrice q).comp (q, ω) hasStrictFDerivAt_fst))
  have hRv : ∀ v w, R (v, w) = Ah.mulVec v := fun v w => by
    simp only [hR, ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.coe_fst', hDv]
    exact cseA_trunc Ah q zt v
  -- the total
  have hev : ∀ᶠ x in 𝓝 (q, ω), cseG x + truncCLM n (excessDemand E' (normPrice x.1)) =
      cseZ E' x := by
    have hopen : ∀ᶠ x : (Fin n → ℝ) × (Fin n → ℝ) in 𝓝 (q, ω), ∀ l, 0 < x.1 l := by
      refine eventually_all.2 fun l => ?_
      exact continuousAt_const.eventually_lt
        (continuous_apply l |>.comp continuous_fst).continuousAt (hq l)
    have hw : ∀ᶠ x : (Fin n → ℝ) × (Fin n → ℝ) in 𝓝 (q, ω),
        0 < normPrice x.1 ⬝ᵥ normPrice x.2 := by
      have hc : Continuous fun x : (Fin n → ℝ) × (Fin n → ℝ) =>
          normPrice x.1 ⬝ᵥ normPrice x.2 := by
        simp only [normPrice_dotProduct, cse_normPrice_castSucc, cse_normPrice_last]
        fun_prop
      have h0 : 0 < normPrice q ⬝ᵥ normPrice ω := by
        rw [normPrice_dotProduct, cse_normPrice_last]
        have := Finset.sum_nonneg fun k (_ : k ∈ Finset.univ) => mul_nonneg (hq k).le (hω k)
        simp only [cse_normPrice_castSucc]
        linarith
      exact continuousAt_const.eventually_lt hc.continuousAt h0
    filter_upwards [hopen, hw] with x hx hxw
    rw [cseZ, cse_excessDemand E' rfl (normPrice_mem_posOrthant.2 hx) hxw.le, map_add,
      cseG_eq]
  set f' := f1 + R with hf'
  have hZd : HasStrictFDerivAt (cseZ E') f' (q, ω) := (hG.add hRd).congr_of_eventuallyEq hev
  have hf'l : ∀ v, f' (v, 0) = (-(cseM q * B⁻¹)).mulVec v := fun v => by
    change f1 (v, 0) + R (v, 0) = _
    rw [hP1v, hRv, ← Matrix.add_mulVec, hAh]
    congr 1; abel
  have hf'r : ∀ v, f' (0, v) = (cseM q).mulVec v := fun v => by
    change f1 (0, v) + R (0, v) = _
    rw [hRv, Matrix.mulVec_zero, add_zero,
      cseG_fderiv_inr hq]
  -- regularity
  have hMdet : (cseM q).det ≠ 0 := by
    rw [cseM_det hq]
    exact div_ne_zero (pow_ne_zero _ (by norm_num)) (by positivity)
  have hmat : LinearMap.toMatrix' ((f'.comp (ContinuousLinearMap.inl ℝ (Fin n → ℝ)
      (Fin n → ℝ)) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) =
      -(cseM q * B⁻¹) := cse_toMatrix'_eq fun v => hf'l v
  have hreg : (f'.comp (ContinuousLinearMap.inl ℝ (Fin n → ℝ) (Fin n → ℝ))).det ≠ 0 := by
    rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix', hmat, Matrix.det_neg,
      Matrix.det_mul, Matrix.det_nonsing_inv]
    refine mul_ne_zero (pow_ne_zero _ (by norm_num)) (mul_ne_zero hMdet ?_)
    rw [Ring.inverse_eq_inv']
    exact inv_ne_zero hB
  -- the equilibrium
  have hzero : cseZ E' (q, ω) = 0 := by
    have h := hev.self_of_nhds
    change cseG (q, ω) + truncCLM n (excessDemand E' p) = cseZ E' (q, ω) at h
    rw [← h, hz', ← cseG_eq, hzt, hpdef, map_neg, add_neg_cancel]
  refine ⟨E', hX, hωpos, hu', hzero, f', hZd, hreg, hf'l, hf'r, ?_⟩
  obtain ⟨η, hloc, hηd⟩ := eq_17_G_1 hZd hzero hreg
  refine ⟨η, hloc, ?_⟩
  -- `Dp(ω̂₁) = B`
  obtain ⟨hηq, ε, hε, δ, hδ, hball⟩ := hloc
  have hsol : ∀ᶠ q' in 𝓝 ω, cseZ E' (η q', q') = 0 := by
    filter_upwards [Metric.ball_mem_nhds ω hδ] with q' hq'
    exact (hball q' hq').2.1
  have hinj : Function.Injective (f'.comp (ContinuousLinearMap.inl ℝ (Fin n → ℝ) (Fin n → ℝ))) := by
    obtain ⟨e, he⟩ := (isInvertible_iff_det_ne_zero _).2 hreg
    rw [← he]
    exact e.injective
  convert hηd using 1
  ext1 v
  apply hinj
  have h1 := eq_17_G_1_any hZd.hasFDerivAt hηd.hasFDerivAt hηq hsol v
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.inl_apply]
  rw [hf'l, cseCLM_apply, Matrix.mulVec_mulVec, Matrix.neg_mul, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ hu, Matrix.mul_one, Matrix.neg_mulVec, ← hf'r]
  linear_combination (exp := 1) -h1

end MWG.PositiveEquilibriumTheory
