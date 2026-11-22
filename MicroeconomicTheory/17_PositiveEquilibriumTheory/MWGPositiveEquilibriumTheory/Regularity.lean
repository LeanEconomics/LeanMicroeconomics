/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPositiveEquilibriumTheory.Existence
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Regular economies and local uniqueness (MWG Section 17.D, pp. 589-593)

With `L = n + 1` goods and the normalization `p_L = 1`, a normalized price vector is
`p = (p̂, 1)` (`normPrice`), and `ẑ(p̂) = (z₁(p), …, z_{L-1}(p))` (`normED`).

* **Definition 17.D.1** (`IsRegularEqm`, `IsRegularEconomy`): an equilibrium `(p̂, 1)` is regular
  if `ẑ` is differentiable at `p̂` and the `(L-1) × (L-1)` matrix `Dẑ(p̂)` is nonsingular
  (`det ≠ 0`; equivalently invertible, `isInvertible_iff_det_ne_zero`).
* **Proposition 17.D.1**: a regular equilibrium is locally isolated
  (`proposition_17_D_1_isolated`); for `z` with (i)-(v) the set of normalized equilibria is
  compact (`isCompact_normEqm`, via the boundary condition), bounded away from zero and infinity
  (`proposition_17_D_1_bounds`, the `r` of the proof) and, if the economy is regular, finite
  (`proposition_17_D_1_finite`).
* **Definition 17.D.2** (`eqmIndex`): `index p = (-1)^{L-1} sign |Dẑ(p)|`, with the sign function
  of footnote 15 (Mathlib's `SignType.sign`, `footnote_17_15`).
* **Footnote 14**: if `A = Dz(p)` (`L × L`) has rank `L - 1` with `A p = 0` (homogeneity,
  `euler_fderiv`) and `pᵀ A = 0` (Walras' law at an equilibrium, `walras_fderiv`), then every
  principal `(L-1) × (L-1)` minor is nonzero and all have the same sign (`footnote_17_14`), so
  regularity and the index do not depend on which good is the numeraire. The normalization of
  the last good gives exactly the minor that deletes good `L` (`normED_hasFDerivAt`).
-/

namespace MWG.PositiveEquilibriumTheory

open Filter Topology

variable {n : ℕ}

/-! ### Normalized prices -/

/-- The normalized price vector `(p̂, 1)` (normalization `p_L = 1`, MWG p. 591). -/
def normPrice (q : Fin n → ℝ) : Fin (n + 1) → ℝ := Fin.snoc q 1

/-- `(p̂, 1)` agrees with `p̂` on the first `L - 1` goods. -/
@[simp] theorem normPrice_castSucc (q : Fin n → ℝ) (l : Fin n) :
    normPrice q (Fin.castSucc l) = q l := by
  simp [normPrice]

/-- The numeraire's price is `1`. -/
@[simp] theorem normPrice_last (q : Fin n → ℝ) : normPrice q (Fin.last n) = 1 := by
  simp [normPrice]

/-- `(p̂, 1) ≫ 0` iff `p̂ ≫ 0`. -/
theorem normPrice_mem_posOrthant {q : Fin n → ℝ} :
    normPrice q ∈ posOrthant (n + 1) ↔ q ∈ posOrthant n := by
  constructor
  · intro h l
    simpa using h (Fin.castSucc l)
  · intro h l
    refine Fin.lastCases ?_ (fun l => ?_) l
    · simp
    · simpa using h l

/-- A price vector with `p_L = 1` is `(p̂, 1)` for `p̂ = (p₁, …, p_{L-1})`. -/
theorem normPrice_init {p : Fin (n + 1) → ℝ} (h : p (Fin.last n) = 1) :
    normPrice (Fin.init p) = p := by
  rw [normPrice, ← h]
  exact Fin.snoc_init_self p

/-- Normalizing does not increase distances: `‖p̂' - p̂‖ ≤ ‖p' - p‖`. -/
theorem dist_init_le (p : Fin (n + 1) → ℝ) (q : Fin n → ℝ) :
    dist (Fin.init p) q ≤ dist p (normPrice q) := by
  refine (dist_pi_le_iff dist_nonneg).2 fun l => ?_
  have := dist_le_pi_dist p (normPrice q) (Fin.castSucc l)
  simpa [Fin.init] using this

/-- `p̂ ↦ (p̂, 1)` is continuous. -/
theorem continuous_normPrice : Continuous (normPrice (n := n)) := by
  refine continuous_pi fun l => ?_
  refine Fin.lastCases ?_ (fun l => ?_) l
  · simpa using continuous_const
  · simpa using continuous_apply l

/-- `ẑ(p̂) = (z₁(p̂, 1), …, z_{L-1}(p̂, 1))`, the normalized excess demand (MWG p. 591). -/
def normED (z : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ) (q : Fin n → ℝ) : Fin n → ℝ :=
  truncExcessDemand z (normPrice q)

/-- `p̂` is a normalized equilibrium: `(p̂, 1)` is an equilibrium price vector. -/
def IsNormEqm (z : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ) (q : Fin n → ℝ) : Prop :=
  IsEqmPrice z (normPrice q)

/-- **Section 17.D** (MWG, p. 591). With Walras' law, `(p̂, 1)` (`p̂ ≫ 0`) is a Walrasian
equilibrium iff it solves the `L - 1` equations `ẑ(p̂) = 0` in `L - 1` unknowns. -/
theorem isNormEqm_iff {z : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ} (hW : EDWalrasLaw z)
    {q : Fin n → ℝ} : IsNormEqm z q ↔ q ∈ posOrthant n ∧ normED z q = 0 := by
  constructor
  · rintro ⟨hp, hz⟩
    exact ⟨normPrice_mem_posOrthant.1 hp, (eqm_iff_trunc_eq_zero hW hp).1 hz⟩
  · rintro ⟨hq, hz⟩
    have hp := normPrice_mem_posOrthant.2 hq
    exact ⟨hp, (eqm_iff_trunc_eq_zero hW hp).2 hz⟩

/-- An equilibrium solves `ẑ(p̂) = 0`. -/
theorem IsNormEqm.normED_eq_zero {z : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ} {q : Fin n → ℝ}
    (h : IsNormEqm z q) : normED z q = 0 := by
  funext l
  simp [normED, truncExcessDemand, h.2]

/-! ### Definition 17.D.1 -/

/-- **Definition 17.D.1** (MWG, p. 591). The normalized equilibrium `(p̂, 1)` is *regular*:
`ẑ` is differentiable at `p̂` and the `(L-1) × (L-1)` matrix of price effects `Dẑ(p̂)` is
nonsingular (rank `L - 1`, i.e. nonzero determinant). -/
def IsRegularEqm (z : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ) (q : Fin n → ℝ) : Prop :=
  IsNormEqm z q ∧ DifferentiableAt ℝ (normED z) q ∧ (fderiv ℝ (normED z) q).det ≠ 0

/-- **Definition 17.D.1** (MWG, p. 591). The economy (its excess demand `z`) is *regular* if every
normalized equilibrium price vector is regular. -/
def IsRegularEconomy (z : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ) : Prop :=
  ∀ q, IsNormEqm z q → IsRegularEqm z q

/-- A linear map of `ℝ^N` is invertible iff its determinant is nonzero (nonsingular, rank `N`). -/
theorem isInvertible_iff_det_ne_zero {N : ℕ} (f : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ)) :
    f.IsInvertible ↔ f.det ≠ 0 := by
  constructor
  · rintro ⟨e, rfl⟩
    exact e.toLinearEquiv.isUnit_det'.ne_zero
  · intro hf
    exact ⟨f.toContinuousLinearEquivOfDetNeZero hf,
      ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero f hf⟩

/-! ### Proposition 17.D.1 -/

/-- **Proposition 17.D.1** (MWG, p. 592), first part. A regular normalized equilibrium
`p = (p̂, 1)` is locally isolated: there is `ε > 0` such that `z(p') ≠ 0` whenever `p' ≠ p`,
`p'_L = 1` and `‖p' - p‖ < ε` (sup norm). The proof is the inverse-function-theorem estimate:
`Dẑ(p̂)` is injective, so `ẑ(p̂') ≠ ẑ(p̂)` near `p̂` (Mathlib `HasFDerivAt.eventually_ne`). -/
theorem proposition_17_D_1_isolated {z : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ} {q : Fin n → ℝ}
    (h : IsRegularEqm z q) :
    ∃ ε > 0, ∀ p' : Fin (n + 1) → ℝ, p' (Fin.last n) = 1 → p' ≠ normPrice q →
      dist p' (normPrice q) < ε → z p' ≠ 0 := by
  obtain ⟨-, hd, hdet⟩ := h
  set e := (fderiv ℝ (normED z) q).toContinuousLinearEquivOfDetNeZero hdet
  have hanti : ∃ C, AntilipschitzWith C (fderiv ℝ (normED z) q) := by
    refine ⟨‖(e.symm : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))‖₊, ?_⟩
    have := e.antilipschitz
    rwa [show (e : (Fin n → ℝ) → Fin n → ℝ) = fderiv ℝ (normED z) q from
      congrArg DFunLike.coe
        (ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero _ hdet)] at this
  have hev := hd.hasFDerivAt.eventually_ne (c := (0 : Fin n → ℝ)) hanti
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 hev)
  refine ⟨ε, hε, fun p' hL hne hdist hz => ?_⟩
  have hp' := normPrice_init hL
  have hq' : Fin.init p' ≠ q := by
    rintro rfl
    exact hne hp'.symm
  apply hball (lt_of_le_of_lt (dist_init_le p' q) hdist) hq'
  funext l
  simp [normED, truncExcessDemand, hp', hz]

/-- The normalized equilibrium set as the image of the interior equilibria in the simplex. -/
theorem normEqm_eq_image {z : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ} (hz : IsStandardExcessDemand z) :
    {q : Fin n → ℝ | IsNormEqm z q} =
      (fun p : Fin (n + 1) → ℝ => fun l : Fin n => p (Fin.castSucc l) / p (Fin.last n)) ''
        {p | p ∈ priceSimplex (n + 1) ∧ p ∈ posOrthant (n + 1) ∧ z p = 0} := by
  ext q
  constructor
  · rintro ⟨hp, hz0⟩
    set S := ∑ l, normPrice q l
    have hS : 0 < S := Finset.sum_pos (fun l _ => hp l) Finset.univ_nonempty
    refine ⟨S⁻¹ • normPrice q, ⟨⟨fun l => (smul_mem_posOrthant hp (inv_pos.2 hS) l).le, ?_⟩,
      smul_mem_posOrthant hp (inv_pos.2 hS), ?_⟩, ?_⟩
    · simp [← Finset.mul_sum, S, inv_mul_cancel₀ hS.ne']
    · rw [hz.homogeneous _ hp _ (inv_pos.2 hS), hz0]
    · funext l
      simp only [Pi.smul_apply, smul_eq_mul, normPrice_castSucc, normPrice_last, mul_one]
      field_simp
  · rintro ⟨p, ⟨-, hp, hz0⟩, rfl⟩
    have hL := hp (Fin.last n)
    have heq : normPrice (fun l : Fin n => p (Fin.castSucc l) / p (Fin.last n)) =
        (p (Fin.last n))⁻¹ • p := by
      funext l
      refine Fin.lastCases ?_ (fun l => ?_) l
      · simp [inv_mul_cancel₀ hL.ne']
      · simp [div_eq_inv_mul]
    refine ⟨?_, ?_⟩
    · rw [heq]; exact smul_mem_posOrthant hp (inv_pos.2 hL)
    · rw [heq, hz.homogeneous _ hp _ (inv_pos.2 hL), hz0]

/-- **Proof of Proposition 17.D.1** (MWG, p. 592). For `z` satisfying (i)-(v), the set of
normalized equilibrium price vectors is compact: equilibria in the simplex form a closed set,
since by the boundary condition (v) they cannot approach prices with a zero component, and
`z` is continuous. -/
theorem isCompact_normEqm {z : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ}
    (hz : IsStandardExcessDemand z) : IsCompact {q : Fin n → ℝ | IsNormEqm z q} := by
  set K := {p | p ∈ priceSimplex (n + 1) ∧ p ∈ posOrthant (n + 1) ∧ z p = 0}
  have hclosed : IsClosed K := by
    refine IsSeqClosed.isClosed fun ps p hps hlim => ?_
    have hΔ : p ∈ priceSimplex (n + 1) :=
      (isClosed_priceSimplex (n + 1)).mem_of_tendsto hlim (Eventually.of_forall fun k => (hps k).1)
    have hpos : p ∈ posOrthant (n + 1) := by
      by_contra hnot
      have hzero : ∃ l, p l = 0 := by
        by_contra h'
        push Not at h'
        exact hnot fun l => lt_of_le_of_ne (hΔ.1 l) (h' l).symm
      have hne : p ≠ 0 := by
        intro h0
        have := hΔ.2
        simp [h0] at this
      obtain ⟨k, l, hl⟩ := (hz.boundary ps p (fun k => (hps k).2.1) hlim hne hzero 0).exists
      rw [(hps k).2.2] at hl
      simp at hl
    refine ⟨hΔ, hpos, ?_⟩
    have hc : Tendsto (fun k => z (ps k)) atTop (𝓝 (z p)) :=
      ((hz.continuous p hpos).continuousAt
        ((isOpen_posOrthant _).mem_nhds hpos)).tendsto.comp hlim
    exact tendsto_nhds_unique hc (tendsto_const_nhds.congr fun k => ((hps k).2.2).symm)
  have hK : IsCompact K := (isCompact_priceSimplex (n + 1)).of_isClosed_subset hclosed
    fun p hp => hp.1
  rw [normEqm_eq_image hz]
  refine hK.image_of_continuousOn ?_
  refine continuousOn_pi.2 fun l => ?_
  exact (continuous_apply _).continuousOn.div (continuous_apply _).continuousOn
    fun p hp => (hp.2.1 (Fin.last n)).ne'

/-- **Proof of Proposition 17.D.1** (MWG, p. 592): there is `r > 0` such that `ẑ(p̂) = 0` (at an
equilibrium) implies `1/r < p_ℓ < r` for every `ℓ`: equilibrium is not compatible with relative
prices arbitrarily close to zero. -/
theorem proposition_17_D_1_bounds {z : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ}
    (hz : IsStandardExcessDemand z) :
    ∃ r > 0, ∀ q, IsNormEqm z q → ∀ l, 1 / r < q l ∧ q l < r := by
  set K := {q : Fin n → ℝ | IsNormEqm z q}
  have hcont : ContinuousOn (fun q : Fin n → ℝ => ∑ l, (q l + (q l)⁻¹)) K :=
    continuousOn_finsetSum _ fun l _ => (continuous_apply l).continuousOn.add
      ((continuous_apply l).continuousOn.inv₀ fun q hq =>
        (normPrice_mem_posOrthant.1 hq.1 l).ne')
  obtain ⟨B, hB⟩ := (isCompact_normEqm hz).bddAbove_image hcont
  refine ⟨|B| + 1, by positivity, fun q hq l => ?_⟩
  have hqpos := normPrice_mem_posOrthant.1 hq.1
  have hle : q l + (q l)⁻¹ ≤ B := by
    have hsum := hB ⟨q, hq, rfl⟩
    have := Finset.single_le_sum (f := fun l => q l + (q l)⁻¹)
      (fun k _ => add_nonneg (hqpos k).le (inv_nonneg.2 (hqpos k).le)) (Finset.mem_univ l)
    exact this.trans hsum
  have hql := hqpos l
  have hinv := inv_pos.2 hql
  have hB' : B ≤ |B| := le_abs_self B
  refine ⟨?_, by linarith⟩
  rw [div_lt_iff₀ (by positivity)]
  have : (q l)⁻¹ < |B| + 1 := by linarith
  calc 1 = q l * (q l)⁻¹ := (mul_inv_cancel₀ hql.ne').symm
    _ < q l * (|B| + 1) := mul_lt_mul_of_pos_left this hql

/-- **Proposition 17.D.1** (MWG, p. 592), second part. If `z` satisfies (i)-(v) of Proposition
17.B.2 and the economy is regular, the number of normalized equilibrium price vectors is finite:
the equilibrium set is compact and each of its points is isolated. -/
theorem proposition_17_D_1_finite {z : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ}
    (hz : IsStandardExcessDemand z) (hreg : IsRegularEconomy z) :
    {q : Fin n → ℝ | IsNormEqm z q}.Finite := by
  set K := {q : Fin n → ℝ | IsNormEqm z q}
  have hiso : ∀ q ∈ K, ∃ ε > 0, ∀ q' ∈ K, dist q' q < ε → q' = q := by
    intro q hq
    obtain ⟨ε, hε, h⟩ := proposition_17_D_1_isolated (hreg q hq)
    refine ⟨ε, hε, fun q' hq' hd => ?_⟩
    by_contra hne
    have hne' : normPrice q' ≠ normPrice q := by
      intro heq
      apply hne
      funext l
      simpa using congrFun heq (Fin.castSucc l)
    have hd' : dist (normPrice q') (normPrice q) < ε := by
      refine lt_of_le_of_lt ?_ hd
      refine (dist_pi_le_iff dist_nonneg).2 fun l => ?_
      refine Fin.lastCases ?_ (fun l => ?_) l
      · simp
      · simpa using dist_le_pi_dist q' q l
    exact h _ (normPrice_last q') hne' hd' hq'.2
  choose! ε hε hball using hiso
  obtain ⟨t, htK, hcover⟩ := (isCompact_normEqm hz).elim_nhds_subcover
    (fun q => Metric.ball q (ε q)) fun q hq => Metric.ball_mem_nhds q (hε q hq)
  refine (t.finite_toSet).subset fun q hq => ?_
  obtain ⟨c, hct, hqc⟩ := Set.mem_iUnion₂.1 (hcover hq)
  rw [hball c (htK c hct) q hq (Metric.mem_ball.1 hqc)]
  exact hct

/-! ### Definition 17.D.2: the index -/

/-- **Footnote 15** (MWG, p. 592). For `α ≠ 0`, `sign α = +1` or `-1` according to whether
`α > 0` or `α < 0` (Mathlib's `SignType.sign`, cast to `ℤ`). -/
theorem footnote_17_15 {α : ℝ} (hα : α ≠ 0) :
    ((SignType.sign α : SignType) : ℤ) = if 0 < α then 1 else -1 := by
  rcases hα.lt_or_gt with h | h
  · simp [sign_neg h, not_lt.2 h.le]
  · simp [sign_pos h, h]

/-- **Definition 17.D.2** (MWG, p. 592). The index of a regular normalized equilibrium `(p̂, 1)`:
`index p = (-1)^{L-1} sign |Dẑ(p)|`. -/
noncomputable def eqmIndex (z : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ) (q : Fin n → ℝ) : ℤ :=
  (-1) ^ n * ((SignType.sign (fderiv ℝ (normED z) q).det : SignType) : ℤ)

/-- The index of a regular equilibrium is `+1` or `-1`. -/
theorem eqmIndex_eq_one_or {z : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ} {q : Fin n → ℝ}
    (h : IsRegularEqm z q) : eqmIndex z q = 1 ∨ eqmIndex z q = -1 := by
  unfold eqmIndex
  rcases neg_one_pow_eq_or ℤ n with hn | hn <;>
    rcases h.2.2.lt_or_gt with hd | hd <;> simp [hn, sign_neg, sign_pos, hd]

/-! ### Footnote 14: independence of the normalization -/

/-- A matrix of rank `n` on `ℝ^{n+1}` has a one-dimensional kernel: if `B p = 0` with `p ≠ 0`,
every `v` with `B v = 0` is a multiple of `p`. -/
theorem ker_eq_smul_of_rank {B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hrank : B.rank = n)
    {p : Fin (n + 1) → ℝ} (hp0 : p ≠ 0) (hBp : B.mulVec p = 0) {v : Fin (n + 1) → ℝ}
    (hv : B.mulVec v = 0) : ∃ c : ℝ, v = c • p := by
  have hk : Module.finrank ℝ (LinearMap.ker B.mulVecLin) = 1 := by
    have h := LinearMap.finrank_range_add_finrank_ker B.mulVecLin
    rw [Module.finrank_fin_fun] at h
    unfold Matrix.rank at hrank
    omega
  have hpk : (⟨p, by simpa using hBp⟩ : LinearMap.ker B.mulVecLin) ≠ 0 := by
    intro h
    exact hp0 (congrArg Subtype.val h)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hpk).1 hk ⟨v, by simpa using hv⟩
  exact ⟨c, (congrArg Subtype.val hc).symm⟩

/-- **Footnote 14** (MWG, p. 591). Let `A = Dz(p)` be `L × L` with `p ≫ 0`, `A p = 0` and
`pᵀ A = 0` (homogeneity and Walras' law at an equilibrium: `euler_fderiv`, `walras_fderiv`).
If `A` has rank `L - 1`, then for every good `k` the `(L-1) × (L-1)` matrix obtained by deleting
row and column `k` (the price effects when good `k` is the numeraire) is nonsingular, and all
these determinants have the same sign: `det A_{kk} = λ p_k²` for a constant `λ ≠ 0`
(the adjugate of `A` is `λ p pᵀ`). -/
theorem footnote_17_14 {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {p : Fin (n + 1) → ℝ}
    (hp : ∀ l, 0 < p l) (hAp : A.mulVec p = 0) (hpA : Matrix.vecMul p A = 0) (hrank : A.rank = n) :
    (∀ k : Fin (n + 1), (A.submatrix k.succAbove k.succAbove).det ≠ 0) ∧
      ∀ k k' : Fin (n + 1), SignType.sign (A.submatrix k.succAbove k.succAbove).det =
        SignType.sign (A.submatrix k'.succAbove k'.succAbove).det := by
  have hp0 : p ≠ 0 := fun h => (hp 0).ne' (by simp [h])
  have hrankT : A.transpose.rank = n := by rw [Matrix.rank_transpose, hrank]
  have hATp : A.transpose.mulVec p = 0 := by rw [Matrix.mulVec_transpose, hpA]
  -- every principal minor is nonzero
  have hminor : ∀ k : Fin (n + 1), (A.submatrix k.succAbove k.succAbove).det ≠ 0 := by
    intro k hdet
    obtain ⟨y, hy0, hy⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
    set x : Fin (n + 1) → ℝ := Fin.insertNth k 0 y
    have hAx_succ : ∀ i, (A.mulVec x) (k.succAbove i) = 0 := by
      intro i
      have h := congrFun hy i
      simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, Pi.zero_apply] at h ⊢
      rw [Fin.sum_univ_succAbove _ k]
      simp [x, h]
    have hdot : p ⬝ᵥ (A.mulVec x) = 0 := by rw [Matrix.dotProduct_mulVec, hpA, zero_dotProduct]
    have hAx_k : (A.mulVec x) k = 0 := by
      rw [dotProduct, Fin.sum_univ_succAbove _ k] at hdot
      simp only [hAx_succ, mul_zero, Finset.sum_const_zero, add_zero] at hdot
      exact (mul_eq_zero.1 hdot).resolve_left (hp k).ne'
    have hAx : A.mulVec x = 0 := by
      funext i
      rcases Fin.eq_self_or_eq_succAbove k i with rfl | ⟨j, rfl⟩
      · exact hAx_k
      · exact hAx_succ j
    obtain ⟨c, hc⟩ := ker_eq_smul_of_rank hrank hp0 hAp hAx
    have hxk : x k = 0 := by simp [x]
    have hc0 : c = 0 := by
      have := congrFun hc k
      rw [hxk, Pi.smul_apply, smul_eq_mul] at this
      exact (mul_eq_zero.1 this.symm).resolve_right (hp k).ne'
    apply hy0
    funext j
    have := congrFun hc (k.succAbove j)
    simpa [x, hc0] using this
  refine ⟨hminor, ?_⟩
  -- the adjugate is `λ p pᵀ`
  have hdetA : A.det = 0 := Matrix.exists_mulVec_eq_zero_iff.1 ⟨p, hp0, hAp⟩
  have hcol : ∀ j, ∃ c : ℝ, (fun i => A.adjugate i j) = c • p := by
    intro j
    refine ker_eq_smul_of_rank hrank hp0 hAp ?_
    funext i
    have := congrFun (congrFun (Matrix.mul_adjugate A) i) j
    simpa [hdetA, Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  have hrow : ∀ i, ∃ d : ℝ, (fun j => A.adjugate i j) = d • p := by
    intro i
    refine ker_eq_smul_of_rank hrankT hp0 hATp ?_
    funext j
    have := congrFun (congrFun (Matrix.adjugate_mul A) i) j
    simp only [hdetA, zero_smul, Matrix.zero_apply, Matrix.mul_apply] at this
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.zero_apply]
    rw [← this]
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  choose c hc using hcol
  choose d hd using hrow
  -- `A.adjugate i j = c j * p i = d i * p j`
  have hcd : ∀ i j, c j * p i = d i * p j := by
    intro i j
    have h1 := congrFun (hc j) i
    have h2 := congrFun (hd i) j
    simp only [Pi.smul_apply, smul_eq_mul] at h1 h2
    rw [← h1, ← h2]
  have hkk : ∀ k, (A.submatrix k.succAbove k.succAbove).det = c 0 / p 0 * p k ^ 2 := by
    intro k
    have hadj := Matrix.adjugate_fin_succ_eq_det_submatrix A k k
    have hev : ((-1 : ℝ)) ^ ((k : ℕ) + k) = 1 := Even.neg_one_pow ⟨k, rfl⟩
    rw [hev, one_mul] at hadj
    rw [← hadj]
    have h1 := congrFun (hc k) k
    simp only [Pi.smul_apply, smul_eq_mul] at h1
    rw [h1]
    have hp0' := (hp 0).ne'
    have hd0 : d 0 = c 0 := (mul_right_cancel₀ hp0' (hcd 0 0)).symm
    have hck : c k * p 0 = c 0 * p k := by rw [hcd 0 k, hd0]
    field_simp
    linear_combination (p k) * hck
  intro k k'
  rw [hkk k, hkk k']
  have hk := pow_pos (hp k) 2
  have hk' := pow_pos (hp k') 2
  rcases lt_trichotomy (c 0 / p 0) 0 with h | h | h
  · rw [sign_neg (mul_neg_of_neg_of_pos h hk), sign_neg (mul_neg_of_neg_of_pos h hk')]
  · simp [h]
  · rw [sign_pos (mul_pos h hk), sign_pos (mul_pos h hk')]

/-- **Footnote 14**, first hypothesis (Euler). If `z` is homogeneous of degree zero and
differentiable at `p ≫ 0` with derivative `D`, then `D p = 0` (`Dz(p) p = 0`). -/
theorem euler_fderiv {L : ℕ} {z : (Fin L → ℝ) → Fin L → ℝ} (hH : EDHomogeneous z)
    {p : Fin L → ℝ} (hp : p ∈ posOrthant L) {D : (Fin L → ℝ) →L[ℝ] (Fin L → ℝ)}
    (hd : HasFDerivAt z D p) : D p = 0 := by
  have h1 : HasDerivAt (fun t : ℝ => t • p) p 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).smul_const p
  have h2 : HasDerivAt (fun t : ℝ => z (t • p)) (D p) 1 :=
    hd.comp_hasDerivAt_of_eq (1 : ℝ) h1 (by simp)
  have h3 : HasDerivAt (fun t : ℝ => z (t • p)) 0 1 :=
    (hasDerivAt_const (1 : ℝ) (z p)).congr_of_eventuallyEq (by
      filter_upwards [lt_mem_nhds one_pos] with t ht
      exact hH p hp t ht)
  exact h2.unique h3

/-- **Footnote 14**, second hypothesis (Walras' law differentiated). If `z` satisfies Walras' law
and is differentiable at `p ≫ 0` with derivative `D`, then `v·z(p) + p·D v = 0` for every `v`;
at an equilibrium (`z(p) = 0`) this is `pᵀ Dz(p) = 0`. -/
theorem walras_fderiv {L : ℕ} {z : (Fin L → ℝ) → Fin L → ℝ} (hW : EDWalrasLaw z)
    {p : Fin L → ℝ} (hp : p ∈ posOrthant L) {D : (Fin L → ℝ) →L[ℝ] (Fin L → ℝ)}
    (hd : HasFDerivAt z D p) (v : Fin L → ℝ) : v ⬝ᵥ z p + p ⬝ᵥ D v = 0 := by
  have hline : HasDerivAt (fun t : ℝ => p + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add p
  have hz : HasDerivAt (fun t : ℝ => z (p + t • v)) (D v) 0 :=
    hd.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
  have hsum : HasDerivAt (fun t : ℝ => ∑ l, (p + t • v) l * z (p + t • v) l)
      (∑ l, (v l * z (p + (0 : ℝ) • v) l + (p + (0 : ℝ) • v) l * D v l)) 0 := by
    refine HasDerivAt.fun_sum fun l _ => ?_
    exact (hasDerivAt_pi.1 hline l).mul (hasDerivAt_pi.1 hz l)
  have hzero : HasDerivAt (fun t : ℝ => ∑ l, (p + t • v) l * z (p + t • v) l) 0 0 := by
    refine (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq ?_
    have hopen := (isOpen_posOrthant L).mem_nhds hp
    have hcont : Continuous fun t : ℝ => p + t • v := by fun_prop
    have hev : ∀ᶠ t in 𝓝 (0 : ℝ), p + t • v ∈ posOrthant L :=
      hcont.continuousAt.preimage_mem_nhds (by simpa using hopen)
    filter_upwards [hev] with t ht
    exact hW _ ht
  have := hsum.unique hzero
  simp only [zero_smul, add_zero] at this
  rw [← this, Finset.sum_add_distrib]
  rfl

/-- The truncation `y ↦ (y₁, …, y_{L-1})` as a continuous linear map. -/
def truncCLM (n : ℕ) : (Fin (n + 1) → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi fun l => ContinuousLinearMap.proj (Fin.castSucc l)

/-- The inclusion `v ↦ (v, 0)` as a continuous linear map. -/
def inclCLM (n : ℕ) : (Fin n → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) :=
  ContinuousLinearMap.pi fun k =>
    Fin.lastCases (motive := fun _ => (Fin n → ℝ) →L[ℝ] ℝ) 0
      (fun l => ContinuousLinearMap.proj l) k

/-- `(inclCLM v)ₖ`: `v` on the first `L - 1` goods, `0` on the numeraire. -/
@[simp] theorem inclCLM_castSucc (v : Fin n → ℝ) (l : Fin n) :
    inclCLM n v (Fin.castSucc l) = v l := by
  simp [inclCLM]

@[simp] theorem inclCLM_last (v : Fin n → ℝ) : inclCLM n v (Fin.last n) = 0 := by
  simp [inclCLM]

/-- `p̂ ↦ (p̂, 1)` is affine with linear part `v ↦ (v, 0)`. -/
theorem hasFDerivAt_normPrice (q : Fin n → ℝ) : HasFDerivAt normPrice (inclCLM n) q := by
  have heq : (normPrice : (Fin n → ℝ) → Fin (n + 1) → ℝ) =
      fun q => inclCLM n q + Pi.single (Fin.last n) 1 := by
    funext q k
    refine Fin.lastCases ?_ (fun l => ?_) k
    · simp
    · simp [Fin.castSucc_ne_last]
  rw [heq]
  exact (inclCLM n).hasFDerivAt.add_const _

/-- **Footnote 14** / (Section 17.D, p. 591). If `z` is differentiable at `(p̂, 1)` with derivative
`D`, then `ẑ` is differentiable at `p̂` and `Dẑ(p̂)` is the `(L-1) × (L-1)` submatrix of `Dz(p)`
obtained by deleting the numeraire's row and column. -/
theorem normED_hasFDerivAt {z : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ} {q : Fin n → ℝ}
    {D : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ)} (hd : HasFDerivAt z D (normPrice q)) :
    HasFDerivAt (normED z) ((truncCLM n).comp (D.comp (inclCLM n))) q ∧
      LinearMap.toMatrix' (((truncCLM n).comp (D.comp (inclCLM n))) :
        (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) =
        (LinearMap.toMatrix' (D : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ))).submatrix
          (Fin.last n).succAbove (Fin.last n).succAbove := by
  refine ⟨(truncCLM n).hasFDerivAt.comp q (hd.comp q (hasFDerivAt_normPrice q)), ?_⟩
  ext l k
  have hs : inclCLM n (Pi.single k 1) = Pi.single (Fin.castSucc k) 1 := by
    funext j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp [(Fin.castSucc_ne_last k).symm]
    · simp [Pi.single_apply, Fin.castSucc_inj]
  simp [LinearMap.toMatrix'_apply, truncCLM, hs, Fin.succAbove_last]

/-- **Footnote 14** (MWG, p. 591), economic form. At an equilibrium `(p̂, 1)` of a homogeneous `z`
satisfying Walras' law, if `z` is differentiable with `Dz(p)` of rank `L - 1`, then the
equilibrium is regular (`Dẑ(p̂)` has rank `L - 1`). -/
theorem isRegularEqm_of_rank {z : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ} (hH : EDHomogeneous z)
    (hW : EDWalrasLaw z) {q : Fin n → ℝ} (heq : IsNormEqm z q)
    {D : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ)} (hd : HasFDerivAt z D (normPrice q))
    (hrank : (LinearMap.toMatrix' (D : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ))).rank = n) :
    IsRegularEqm z q := by
  obtain ⟨hD, hmat⟩ := normED_hasFDerivAt hd
  set A := LinearMap.toMatrix' (D : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ))
  have hp := heq.1
  have hAp : A.mulVec (normPrice q) = 0 := by
    rw [LinearMap.toMatrix'_mulVec]
    exact euler_fderiv hH hp hd
  have hpA : Matrix.vecMul (normPrice q) A = 0 := by
    funext k
    have h := walras_fderiv hW hp hd (Pi.single k 1)
    rw [heq.2, dotProduct_zero, zero_add] at h
    simp only [Matrix.vecMul, dotProduct, A, LinearMap.toMatrix'_apply, Pi.zero_apply]
    simpa [dotProduct] using h
  refine ⟨heq, hD.differentiableAt, ?_⟩
  rw [hD.fderiv, ContinuousLinearMap.det, ← LinearMap.det_toMatrix', hmat]
  exact (footnote_17_14 hp hAp hpA hrank).1 (Fin.last n)

end MWG.PositiveEquilibriumTheory
