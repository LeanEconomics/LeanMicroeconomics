/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPositiveEquilibriumTheory.WeakAxiomED
import MWGPositiveEquilibriumTheory.PriceEffects

/-!
# The differential weak axiom and homothetic economies (MWG Section 17.F, pp. 610-611)

* **(17.F.1)** (`eq_17_F_1_sufficient`): if `z` is differentiable, homogeneous of degree zero, and
  satisfies Walras' law, and `dp·Dz(p) dp < 0` whenever `dp·z(p) = 0` and `dp` is not
  proportional to `p`, then `z` satisfies the weak axiom (the book: "it can be shown"). The proof
  follows `g(t) = (p' - p)·z((1 - t)p + tp')`, which can only cross zero downwards.
* **Footnote 42** (`footnote_17_42`): conversely, the weak axiom implies `dp·Dz(p) dp ≤ 0`
  whenever `dp·z(p) = 0`; at an equilibrium `Dz(p)` is negative semidefinite (`wa_nsd_at_eqm`,
  p. 615).
* **(17.F.2)**: with homothetic preferences `D_w xᵢ = xᵢ/(p·ωᵢ)` (`homothetic_wealthJacobian`), and
  `Dz(p)` decomposes into substitution, "variance", "covariance" and `x̄ z(p)ᵀ` terms
  (`eq_17_F_2_identity`, for demand functions `eq_17_F_2`); for `dp·z(p) = 0` the first two terms
  are `≤ 0` and the fourth vanishes (`eq_17_F_2_terms`).
* **Exercise 17.F.1** (footnote 43): with proportional endowments, or proportional consumptions,
  `dp·Dz(p) dp ≤ 0` whenever `dp·z(p) = 0` (`exercise_17_F_1a`, `exercise_17_F_1b`); without the
  restriction `dp·z(p) = 0` the matrix (17.F.2) need not be negative semidefinite
  (`exercise_17_F_1_unrestricted`).
-/

namespace MWG.PositiveEquilibriumTheory

open MWG.ConsumerChoice Filter Topology

variable {L : ℕ}

/-! ### Calculus lemmas -/

/-- The derivative of `t ↦ v·f(t)`. -/
theorem wad_hasDerivAt_dot {f : ℝ → Fin L → ℝ} {f' : Fin L → ℝ} {t : ℝ} (v : Fin L → ℝ)
    (h : HasDerivAt f f' t) : HasDerivAt (fun s => v ⬝ᵥ f s) (v ⬝ᵥ f') t := by
  simp only [dotProduct]
  exact HasDerivAt.fun_sum fun l _ => (hasDerivAt_pi.1 h l).const_mul (v l)

/-- If `g` has derivative `c` at `x` and `g(t) ≤ g(x)` for `t > x` close to `x`, then `c ≤ 0`. -/
theorem wad_deriv_nonpos {g : ℝ → ℝ} {c x : ℝ} (h : HasDerivAt g c x)
    (hle : ∀ᶠ t in 𝓝[>] x, g t ≤ g x) : c ≤ 0 := by
  have hs : Tendsto (slope g x) (𝓝[>] x) (𝓝 c) := (hasDerivAt_iff_tendsto_slope.1 h).mono_left
    (nhdsWithin_mono x fun t ht => ne_of_gt (Set.mem_Ioi.1 ht))
  refine le_of_tendsto hs ?_
  filter_upwards [hle, self_mem_nhdsWithin] with t ht hxt
  rw [slope_def_field]
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith [show x < t from hxt])

/-- If `g` has derivative `c < 0` at `x`, then `g(t) < g(x)` for `t > x` close to `x`, and
`g(t) > g(x)` for `t < x` close to `x`. -/
theorem wad_deriv_neg {g : ℝ → ℝ} {c x : ℝ} (h : HasDerivAt g c x) (hc : c < 0) :
    (∀ᶠ t in 𝓝[>] x, g t < g x) ∧ ∀ᶠ t in 𝓝[<] x, g x < g t := by
  have hs := hasDerivAt_iff_tendsto_slope.1 h
  have hev : ∀ᶠ t in 𝓝[≠] x, slope g x t < 0 := hs (Iio_mem_nhds hc)
  constructor
  · filter_upwards [hev.filter_mono (nhdsWithin_mono x fun t (ht : x < t) => ne_of_gt ht),
      self_mem_nhdsWithin] with t ht hxt
    rw [slope_def_field] at ht
    have : (0 : ℝ) < t - x := by linarith [show x < t from hxt]
    have := (div_neg_iff.1 ht)
    rcases this with ⟨_, h2⟩ | ⟨h1, _⟩ <;> linarith
  · filter_upwards [hev.filter_mono (nhdsWithin_mono x fun t (ht : t < x) => ne_of_lt ht),
      self_mem_nhdsWithin] with t ht hxt
    rw [slope_def_field] at ht
    have : t - x < 0 := by linarith [show t < x from hxt]
    have := (div_neg_iff.1 ht)
    rcases this with ⟨_, h2⟩ | ⟨h1, _⟩ <;> linarith

/-! ### Footnote 42: necessity of the weak differential condition -/

/-- **Footnote 42** (MWG, p. 610). If `z` satisfies Walras' law and the weak axiom and is
differentiable at `p ≫ 0` with derivative `D`, then `dp·D dp ≤ 0` whenever `dp·z(p) = 0`
(the weak version of (17.F.1) is necessary). -/
theorem footnote_17_42 {z : (Fin L → ℝ) → Fin L → ℝ} (hW : EDWalrasLaw z) (hWA : WeakAxiomED z)
    {p : Fin L → ℝ} (hp : p ∈ posOrthant L) {D : (Fin L → ℝ) →L[ℝ] (Fin L → ℝ)}
    (hd : HasFDerivAt z D p) {v : Fin L → ℝ} (hv : v ⬝ᵥ z p = 0) : v ⬝ᵥ D v ≤ 0 := by
  have hline : HasDerivAt (fun t : ℝ => p + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add p
  have hz : HasDerivAt (fun t : ℝ => z (p + t • v)) (D v) 0 :=
    hd.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
  have hg := wad_hasDerivAt_dot v hz
  refine wad_deriv_nonpos hg ?_
  have hcont : Continuous fun t : ℝ => p + t • v := by fun_prop
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), p + t • v ∈ posOrthant L :=
    hcont.continuousAt.preimage_mem_nhds (by simpa using (isOpen_posOrthant L).mem_nhds hp)
  filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with t ht htpos
  have htpos' : (0 : ℝ) < t := htpos
  simp only [zero_smul, add_zero, hv]
  by_cases heq : z (p + t • v) = z p
  · rw [heq, hv]
  · have hpz : (p + t • v) ⬝ᵥ z p ≤ 0 := by
      rw [add_dotProduct, smul_dotProduct, hv, smul_zero, hW p hp, add_zero]
    have h1 := hWA _ ht p hp heq hpz
    have h2 := hW _ ht
    rw [add_dotProduct, smul_dotProduct, smul_eq_mul] at h2
    nlinarith

/-- **Section 17.F** (MWG, p. 615). Under the weak axiom (and Walras' law), at an equilibrium
`p` (`z(p) = 0`) the matrix `Dz(p)` is negative semidefinite. -/
theorem wa_nsd_at_eqm {z : (Fin L → ℝ) → Fin L → ℝ} (hW : EDWalrasLaw z) (hWA : WeakAxiomED z)
    {p : Fin L → ℝ} (hp : IsEqmPrice z p) {D : (Fin L → ℝ) →L[ℝ] (Fin L → ℝ)}
    (hd : HasFDerivAt z D p) (v : Fin L → ℝ) : v ⬝ᵥ D v ≤ 0 :=
  footnote_17_42 hW hWA hp.1 hd (by rw [hp.2, dotProduct_zero])

/-! ### (17.F.1): sufficiency of the strict differential condition -/

/-- **(17.F.1)** (MWG, p. 610), auxiliary. If `z` is homogeneous of degree zero and
`z(p) ≠ z(p')`, the direction `p' - p` is not proportional to any point `(1 - t)p + tp'` of the
line through `p` and `p'`. -/
theorem wad_not_proportional {z : (Fin L → ℝ) → Fin L → ℝ} (hH : EDHomogeneous z)
    {p p' : Fin L → ℝ} (hp : p ∈ posOrthant L) (hp' : p' ∈ posOrthant L) (hne : z p ≠ z p')
    (t α : ℝ) : p' - p ≠ α • (p + t • (p' - p)) := by
  intro h
  rcases Nat.eq_zero_or_pos L with hL | hL
  · subst hL
    exact hne (funext fun l => Fin.elim0 l)
  have l0 : Fin L := ⟨0, hL⟩
  have hcoord : ∀ l, (1 - α * t) * (p' l - p l) = α * p l := by
    intro l
    have := congrFun h l
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul] at this
    linarith
  have hden : 1 - α * t ≠ 0 := by
    intro h0
    have h1 := hcoord l0
    rw [h0, zero_mul] at h1
    have hα : α = 0 := by
      rcases mul_eq_zero.1 h1.symm with h | h
      · exact h
      · exact absurd h (hp l0).ne'
    rw [hα, zero_mul, sub_zero] at h0
    exact one_ne_zero h0
  set β := 1 + α / (1 - α * t) with hβ
  have hp'eq : p' = β • p := by
    funext l
    have h1 := hcoord l
    simp only [Pi.smul_apply, smul_eq_mul, hβ]
    field_simp
    linarith
  have hβpos : 0 < β := by
    have h1 := hp' l0
    rw [hp'eq] at h1
    simp only [Pi.smul_apply, smul_eq_mul] at h1
    exact pos_of_mul_pos_left h1 (hp l0).le
  exact hne (by rw [hp'eq, hH p hp β hβpos])

/-- **(17.F.1)** (MWG, p. 610). The strict differential weak axiom is sufficient for the weak
axiom: if `z` is homogeneous of degree zero, satisfies Walras' law, is differentiable on
`ℝ^L_{++}` (derivative `D p`), and `dp·Dz(p) dp < 0` whenever `dp·z(p) = 0` and `dp` is not
proportional to `p`, then `z` satisfies the weak axiom. -/
theorem eq_17_F_1_sufficient {z : (Fin L → ℝ) → Fin L → ℝ} (hH : EDHomogeneous z)
    (hW : EDWalrasLaw z) {D : (Fin L → ℝ) → (Fin L → ℝ) →L[ℝ] (Fin L → ℝ)}
    (hd : ∀ p ∈ posOrthant L, HasFDerivAt z (D p) p)
    (hneg : ∀ p ∈ posOrthant L, ∀ v, v ⬝ᵥ z p = 0 → (∀ α : ℝ, v ≠ α • p) →
      v ⬝ᵥ D p v < 0) : WeakAxiomED z := by
  intro p hp p' hp' hne hle
  by_contra hcon
  rw [not_lt] at hcon
  set dp := p' - p with hdp
  set c : ℝ → Fin L → ℝ := fun t => p + t • dp with hc
  set g : ℝ → ℝ := fun t => dp ⬝ᵥ z (c t) with hg
  have hcmem : ∀ t, 0 ≤ t → t ≤ 1 → c t ∈ posOrthant L := fun t h0 h1 => by
    have := convex_posOrthant L hp hp' (a := 1 - t) (b := t) (by linarith) h0 (by ring)
    convert this using 1
    simp only [hc, hdp]
    module
  have hderiv : ∀ t, 0 ≤ t → t ≤ 1 → HasDerivAt g (dp ⬝ᵥ D (c t) dp) t := by
    intro t h0 h1
    have hline : HasDerivAt c dp t := by
      change HasDerivAt (fun s => p + s • dp) dp t
      simpa only [id_eq, one_smul] using ((hasDerivAt_id t).smul_const dp).const_add p
    exact wad_hasDerivAt_dot dp ((hd _ (hcmem t h0 h1)).comp_hasDerivAt t hline)
  have hzero : ∀ t, 0 ≤ t → t ≤ 1 → g t = 0 → dp ⬝ᵥ D (c t) dp < 0 := fun t h0 h1 hgt =>
    hneg _ (hcmem t h0 h1) dp hgt (wad_not_proportional hH hp hp' hne t)
  have hg0 : g 0 ≤ 0 := by
    simp only [hg, hc, zero_smul, add_zero, hdp, sub_dotProduct, hW p hp, sub_zero]
    exact hcon
  have hg1 : 0 ≤ g 1 := by
    simp only [hg, hc, one_smul, hdp, add_sub_cancel, sub_dotProduct, hW p' hp', zero_sub]
    linarith
  -- a point `t₁ ∈ (0, 1]` with `g t₁ > 0`
  obtain ⟨t1, ht10, ht11, hgt1⟩ : ∃ t1, 0 < t1 ∧ t1 ≤ 1 ∧ 0 < g t1 := by
    rcases lt_or_eq_of_le hg1 with h | h
    · exact ⟨1, one_pos, le_rfl, h⟩
    · have hev := (wad_deriv_neg (hderiv 1 zero_le_one le_rfl)
        (hzero 1 zero_le_one le_rfl h.symm)).2
      have hev2 : ∀ᶠ t in 𝓝[<] (1 : ℝ), 0 < t := nhdsWithin_le_nhds (lt_mem_nhds one_pos)
      obtain ⟨t, ht, htpos, htlt⟩ := (hev.and (hev2.and self_mem_nhdsWithin)).exists
      exact ⟨t, htpos, le_of_lt htlt, lt_of_eq_of_lt h ht⟩
  -- the last point of `[0, t₁]` where `g ≤ 0`
  have hgcont : ContinuousOn g (Set.Icc 0 1) := fun t ht =>
    (hderiv t ht.1 ht.2).continuousAt.continuousWithinAt
  set A := {t | t ∈ Set.Icc 0 t1 ∧ g t ≤ 0} with hA
  have hAclosed : IsClosed A := by
    have : A = Set.Icc 0 t1 ∩ g ⁻¹' Set.Iic 0 := rfl
    rw [this]
    exact (hgcont.mono (Set.Icc_subset_Icc le_rfl ht11)).preimage_isClosed_of_isClosed
      isClosed_Icc isClosed_Iic
  have hAne : A.Nonempty := ⟨0, ⟨le_rfl, ht10.le⟩, hg0⟩
  have hAbdd : BddAbove A := ⟨t1, fun t ht => ht.1.2⟩
  set a := sSup A with ha
  have haA : a ∈ A := hAclosed.csSup_mem hAne hAbdd
  have hat1 : a < t1 := lt_of_le_of_ne haA.1.2 (fun h => by
    have := haA.2; rw [h] at this; linarith)
  have ha0 : 0 ≤ a := haA.1.1
  have ha1 : a ≤ 1 := haA.1.2.trans ht11
  have hright : ∀ᶠ t in 𝓝[>] a, g t ≤ 0 := by
    rcases lt_or_eq_of_le haA.2 with h | h
    · have hca : ContinuousAt g a := (hderiv a ha0 ha1).continuousAt
      exact ((hca.eventually (Iio_mem_nhds h)).filter_mono nhdsWithin_le_nhds).mono
        fun t ht => le_of_lt ht
    · exact (wad_deriv_neg (hderiv a ha0 ha1) (hzero a ha0 ha1 h)).1.mono fun t ht => by
        rw [← h]; exact ht.le
  have hlt : ∀ᶠ t in 𝓝[>] a, t < t1 := nhdsWithin_le_nhds (Iio_mem_nhds hat1)
  obtain ⟨t, hgt, htt1, hat⟩ := (hright.and (hlt.and self_mem_nhdsWithin)).exists
  have hat' : a < t := hat
  have htA : t ∈ A := ⟨⟨by linarith, htt1.le⟩, hgt⟩
  have := le_csSup hAbdd htA
  linarith

/-! ### (17.F.2): homothetic preferences -/

/-- **Section 17.F** (MWG, p. 610). If demand is homogeneous of degree one in wealth
(homothetic preferences, `x(p, αw) = αx(p, w)`) and differentiable at `(p, w)`, `w > 0`, then
`D_w x(p, w) = x(p, w)/w`. -/
theorem homothetic_wealthJacobian {x : DemandFunction L} {p : Fin L → ℝ} {w : ℝ} (hw : 0 < w)
    (hhom : ∀ α : ℝ, 0 < α → x p (α * w) = α • x p w)
    {Dx : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)} (hDx : HasFDerivAt (Function.uncurry x) Dx (p, w)) :
    wealthJacobian Dx = (1 / w) • x p w := by
  have hline : HasDerivAt (fun α : ℝ => ((p, α * w) : (Fin L → ℝ) × ℝ)) ((0, w)) 1 := by
    refine (hasDerivAt_const (1 : ℝ) p).prodMk ?_
    simpa using (hasDerivAt_id (1 : ℝ)).mul_const w
  have h1 : HasDerivAt (fun α : ℝ => x p (α * w)) (Dx (0, w)) 1 := by
    have := hDx.comp_hasDerivAt_of_eq (1 : ℝ) hline (by simp)
    exact this
  have h2 : HasDerivAt (fun α : ℝ => x p (α * w)) (x p w) 1 := by
    have h3 : HasDerivAt (fun α : ℝ => α • x p w) (x p w) 1 := by
      simpa using (hasDerivAt_id (1 : ℝ)).smul_const (x p w)
    refine h3.congr_of_eventuallyEq ?_
    filter_upwards [lt_mem_nhds one_pos] with α hα
    exact hhom α hα
  have heq : Dx (0, w) = x p w := h1.unique h2
  have hsc : Dx (0, w) = w • Dx (0, 1) := by
    rw [← map_smul]
    congr 1
    ext <;> simp
  funext l
  simp only [wealthJacobian, wealthEffect, Pi.smul_apply, smul_eq_mul]
  have := congrFun (hsc.symm.trans heq) l
  simp only [Pi.smul_apply, smul_eq_mul] at this
  field_simp
  linarith

/-- The quadratic form of `a bᵀ`: `v·(a bᵀ) v = (v·a)(b·v)`. -/
theorem wad_quad_vecMulVec (a b v : Fin L → ℝ) :
    v ⬝ᵥ (Matrix.vecMulVec a b).mulVec v = (v ⬝ᵥ a) * (b ⬝ᵥ v) := by
  simp only [Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by ring

variable {ι : Type*} [Fintype ι]

/-- **(17.F.2)** (MWG, p. 610), the algebraic identity. With wealth levels `wᵢ = p·ωᵢ ≠ 0`,
`W = ∑ᵢ wᵢ ≠ 0`, `x̄ = ∑ᵢ xᵢ`, `ω̄ = ∑ᵢ ωᵢ`, `z = ∑ᵢ (xᵢ - ωᵢ)`:
`∑ᵢ Sᵢ - ∑ᵢ (1/wᵢ) xᵢ zᵢᵀ = ∑ᵢ Sᵢ - ∑ᵢ (1/wᵢ)[xᵢ - (wᵢ/W)x̄][xᵢ - (wᵢ/W)x̄]ᵀ
+ ∑ᵢ (1/wᵢ)[xᵢ - (wᵢ/W)x̄][ωᵢ - (wᵢ/W)ω̄]ᵀ - (1/W) x̄ zᵀ`. -/
theorem eq_17_F_2_identity (S : ι → Matrix (Fin L) (Fin L) ℝ) (x ω : ι → Fin L → ℝ)
    (p : Fin L → ℝ) (hw : ∀ i, p ⬝ᵥ ω i ≠ 0) (hW : ∑ i, p ⬝ᵥ ω i ≠ 0) :
    ∑ i, S i - ∑ i, (1 / p ⬝ᵥ ω i) • Matrix.vecMulVec (x i) (x i - ω i) =
      ∑ i, S i - ∑ i, (1 / p ⬝ᵥ ω i) • Matrix.vecMulVec
          (x i - (p ⬝ᵥ ω i / ∑ j, p ⬝ᵥ ω j) • ∑ j, x j)
          (x i - (p ⬝ᵥ ω i / ∑ j, p ⬝ᵥ ω j) • ∑ j, x j) +
        ∑ i, (1 / p ⬝ᵥ ω i) • Matrix.vecMulVec
          (x i - (p ⬝ᵥ ω i / ∑ j, p ⬝ᵥ ω j) • ∑ j, x j)
          (ω i - (p ⬝ᵥ ω i / ∑ j, p ⬝ᵥ ω j) • ∑ j, ω j) -
        (1 / ∑ j, p ⬝ᵥ ω j) • Matrix.vecMulVec (∑ j, x j) (∑ j, (x j - ω j)) := by
  set w : ι → ℝ := fun i => p ⬝ᵥ ω i with hwdef
  set W := ∑ j, w j with hWdef
  ext k l
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, smul_eq_mul, Pi.sub_apply, Pi.smul_apply, Finset.sum_apply]
  change _ - ∑ i, 1 / w i * (x i k * (x i l - ω i l)) = _ - ∑ i, 1 / w i *
      ((x i k - w i / W * ∑ j, x j k) * (x i l - w i / W * ∑ j, x j l)) +
    ∑ i, 1 / w i * ((x i k - w i / W * ∑ j, x j k) * (ω i l - w i / W * ∑ j, ω j l)) -
    1 / W * ((∑ j, x j k) * ∑ j, (x j l - ω j l))
  set X := ∑ j, x j k
  set Xl := ∑ j, x j l
  set Ol := ∑ j, ω j l
  have hterm : ∀ i, 1 / w i * ((x i k - w i / W * X) * (x i l - w i / W * Xl)) -
      1 / w i * ((x i k - w i / W * X) * (ω i l - w i / W * Ol)) =
      1 / w i * (x i k * (x i l - ω i l)) - 1 / W * (x i k * (Xl - Ol)) -
        1 / W * (X * (x i l - ω i l)) + w i / W ^ 2 * (X * (Xl - Ol)) := by
    intro i
    have : w i ≠ 0 := hw i
    field_simp
    ring
  have hsum := Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hterm i
  rw [Finset.sum_sub_distrib] at hsum
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.sum_mul] at hsum
  have hz : ∑ j, (x j l - ω j l) = Xl - Ol := Finset.sum_sub_distrib _ _
  rw [hz]
  have hWW : ∑ i, w i / W ^ 2 = 1 / W := by
    rw [← Finset.sum_div, ← hWdef]
    field_simp
  rw [show (∑ i, x i l - ∑ i, ω i l) = Xl - Ol from rfl, hWW] at hsum
  linear_combination hsum

/-- **(17.F.2)** (MWG, p. 610). For consumers with homothetic demand functions `xᵢ` (homogeneous
of degree one in wealth), differentiable at `(p, p·ωᵢ)` with `p·ωᵢ > 0`, the excess demand
`z(p)` is differentiable at `p` and `Dz(p)` is given by (17.F.2): substitution matrices
`Sᵢ`, minus the "variance" terms, plus the "covariance" terms, minus `(1/p·ω̄) x̄ z(p)ᵀ`. -/
theorem eq_17_F_2 [Nonempty ι] (x : ι → DemandFunction L) (ω : ι → Fin L → ℝ)
    {p : Fin L → ℝ} (hw : ∀ i, 0 < p ⬝ᵥ ω i)
    (hhom : ∀ i, ∀ α : ℝ, 0 < α → x i p (α * p ⬝ᵥ ω i) = α • x i p (p ⬝ᵥ ω i))
    (Dx : ι → ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ))
    (hx : ∀ i, HasFDerivAt (Function.uncurry (x i)) (Dx i) (p, p ⬝ᵥ ω i)) :
    ∃ D : (Fin L → ℝ) →L[ℝ] (Fin L → ℝ), HasFDerivAt (aggExcessDemand x ω) D p ∧
      ∀ v, D v = Matrix.mulVec (∑ i, slutskyMatrix (Dx i) (x i p (p ⬝ᵥ ω i)) -
        ∑ i, (1 / p ⬝ᵥ ω i) • Matrix.vecMulVec
          (x i p (p ⬝ᵥ ω i) - (p ⬝ᵥ ω i / ∑ j, p ⬝ᵥ ω j) • ∑ j, x j p (p ⬝ᵥ ω j))
          (x i p (p ⬝ᵥ ω i) - (p ⬝ᵥ ω i / ∑ j, p ⬝ᵥ ω j) • ∑ j, x j p (p ⬝ᵥ ω j)) +
        ∑ i, (1 / p ⬝ᵥ ω i) • Matrix.vecMulVec
          (x i p (p ⬝ᵥ ω i) - (p ⬝ᵥ ω i / ∑ j, p ⬝ᵥ ω j) • ∑ j, x j p (p ⬝ᵥ ω j))
          (ω i - (p ⬝ᵥ ω i / ∑ j, p ⬝ᵥ ω j) • ∑ j, ω j) -
        (1 / ∑ j, p ⬝ᵥ ω j) • Matrix.vecMulVec (∑ j, x j p (p ⬝ᵥ ω j))
          (∑ j, (x j p (p ⬝ᵥ ω j) - ω j))) v := by
  obtain ⟨D, hD, hDv⟩ := eq_17_E_3 x ω Dx hx
  refine ⟨D, hD, fun v => ?_⟩
  rw [hDv v]
  congr 1
  have hWJ : ∀ i, wealthJacobian (Dx i) = (1 / p ⬝ᵥ ω i) • x i p (p ⬝ᵥ ω i) := fun i =>
    homothetic_wealthJacobian (hw i) (hhom i) (hx i)
  have hW : ∑ i, p ⬝ᵥ ω i ≠ 0 :=
    (Finset.sum_pos (fun i _ => hw i) Finset.univ_nonempty).ne'
  rw [← eq_17_F_2_identity _ _ ω p (fun i => (hw i).ne') hW, Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hWJ i]
  ext k l
  simp [Matrix.vecMulVec_apply, mul_assoc]

/-- **Section 17.F** (MWG, p. 610). For a price change `dp` with `dp·z(p) = 0`: the
substitution term of (17.F.2) is `≤ 0` when each `Sᵢ` is negative semidefinite, the variance
term `-∑ᵢ (1/wᵢ) aᵢaᵢᵀ` is `≤ 0` (`wᵢ > 0`), and the term `x̄ zᵀ` contributes `0`. -/
theorem eq_17_F_2_terms (S : ι → Matrix (Fin L) (Fin L) ℝ)
    (hS : ∀ i, ∀ v, v ⬝ᵥ (S i).mulVec v ≤ 0) (a : ι → Fin L → ℝ) (w : ι → ℝ)
    (hw : ∀ i, 0 < w i) (xbar zz dp : Fin L → ℝ) (hdp : dp ⬝ᵥ zz = 0) :
    dp ⬝ᵥ (∑ i, S i).mulVec dp ≤ 0 ∧
      dp ⬝ᵥ (-∑ i, (1 / w i) • Matrix.vecMulVec (a i) (a i)).mulVec dp ≤ 0 ∧
      dp ⬝ᵥ (Matrix.vecMulVec xbar zz).mulVec dp = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.sum_mulVec, dotProduct_sum]
    exact Finset.sum_nonpos fun i _ => hS i dp
  · rw [Matrix.neg_mulVec, Matrix.sum_mulVec, dotProduct_neg, dotProduct_sum, neg_nonpos]
    refine Finset.sum_nonneg fun i _ => ?_
    rw [Matrix.smul_mulVec, dotProduct_smul, wad_quad_vecMulVec, smul_eq_mul,
      dotProduct_comm (a i) dp]
    exact mul_nonneg (by have := hw i; positivity) (mul_self_nonneg _)
  · rw [wad_quad_vecMulVec, dotProduct_comm zz dp, hdp, mul_zero]

/-- The matrix of (17.F.2) at given data: substitution matrices `Sᵢ`, consumptions `xᵢ`,
endowments `ωᵢ`, prices `p`. -/
noncomputable def wadMatrix (S : ι → Matrix (Fin L) (Fin L) ℝ) (x ω : ι → Fin L → ℝ)
    (p : Fin L → ℝ) : Matrix (Fin L) (Fin L) ℝ :=
  ∑ i, S i - ∑ i, (1 / p ⬝ᵥ ω i) • Matrix.vecMulVec (x i) (x i - ω i)

/-- With zero covariance terms, the quadratic form of (17.F.2) is `≤ 0` on `dp·z(p) = 0`. -/
theorem wad_nsd_of_cov_zero {S : ι → Matrix (Fin L) (Fin L) ℝ} (hS : ∀ i, ∀ v,
    v ⬝ᵥ (S i).mulVec v ≤ 0) {x ω : ι → Fin L → ℝ} {p : Fin L → ℝ} (hw : ∀ i, 0 < p ⬝ᵥ ω i)
    (hcov : ∀ i, p ⬝ᵥ ω i ≠ 0 → (ω i - (p ⬝ᵥ ω i / ∑ j, p ⬝ᵥ ω j) • ∑ j, ω j) = 0 ∨
      (x i - (p ⬝ᵥ ω i / ∑ j, p ⬝ᵥ ω j) • ∑ j, x j) = 0)
    [Nonempty ι] (dp : Fin L → ℝ) (hdp : dp ⬝ᵥ ∑ j, (x j - ω j) = 0) :
    dp ⬝ᵥ (wadMatrix S x ω p).mulVec dp ≤ 0 := by
  have hW : ∑ i, p ⬝ᵥ ω i ≠ 0 :=
    (Finset.sum_pos (fun i _ => hw i) Finset.univ_nonempty).ne'
  unfold wadMatrix
  rw [eq_17_F_2_identity S x ω p (fun i => (hw i).ne') hW]
  have hcov0 : ∑ i, (1 / p ⬝ᵥ ω i) • Matrix.vecMulVec
      (x i - (p ⬝ᵥ ω i / ∑ j, p ⬝ᵥ ω j) • ∑ j, x j)
      (ω i - (p ⬝ᵥ ω i / ∑ j, p ⬝ᵥ ω j) • ∑ j, ω j) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rcases hcov i (hw i).ne' with h | h <;> simp [h]
  rw [hcov0, add_zero, sub_eq_add_neg, sub_eq_add_neg, Matrix.add_mulVec, Matrix.add_mulVec,
    dotProduct_add, dotProduct_add]
  obtain ⟨h1, h2, h3⟩ := eq_17_F_2_terms S hS
    (fun i => x i - (p ⬝ᵥ ω i / ∑ j, p ⬝ᵥ ω j) • ∑ j, x j) (fun i => p ⬝ᵥ ω i) hw (∑ j, x j)
    (∑ j, (x j - ω j)) dp hdp
  rw [Matrix.neg_mulVec, dotProduct_neg] at h2
  have e3 : dp ⬝ᵥ (-((1 / ∑ j, p ⬝ᵥ ω j) • Matrix.vecMulVec (∑ j, x j)
      (∑ j, (x j - ω j)))).mulVec dp = 0 := by
    rw [Matrix.neg_mulVec, dotProduct_neg, Matrix.smul_mulVec, dotProduct_smul, h3, smul_zero,
      neg_zero]
  rw [e3, add_zero, Matrix.neg_mulVec, dotProduct_neg]
  linarith

/-- **Exercise 17.F.1** (MWG, p. 645), proportional endowments (footnote 43). If the endowments are
proportional among themselves (`ωᵢ = sᵢ ω₀`), with positive wealths `p·ωᵢ` and negative
semidefinite substitution matrices, then (17.F.2) is negative semidefinite on price changes with
`dp·z(p) = 0`. -/
theorem exercise_17_F_1a [Nonempty ι] {S : ι → Matrix (Fin L) (Fin L) ℝ}
    (hS : ∀ i, ∀ v, v ⬝ᵥ (S i).mulVec v ≤ 0) (x : ι → Fin L → ℝ) {ω₀ : Fin L → ℝ}
    {s : ι → ℝ} {p : Fin L → ℝ} (hw : ∀ i, 0 < p ⬝ᵥ (s i • ω₀)) (dp : Fin L → ℝ)
    (hdp : dp ⬝ᵥ ∑ j, (x j - s j • ω₀) = 0) :
    dp ⬝ᵥ (wadMatrix S x (fun i => s i • ω₀) p).mulVec dp ≤ 0 := by
  refine wad_nsd_of_cov_zero hS hw (fun i _ => Or.inl ?_) dp hdp
  have hpω : p ⬝ᵥ ω₀ ≠ 0 := by
    intro h
    have := hw i
    rw [dotProduct_smul, h, smul_zero] at this
    exact lt_irrefl _ this
  simp only [dotProduct_smul, smul_eq_mul, ← Finset.sum_mul, ← Finset.sum_smul, smul_smul]
  have hs : ∑ j, s j ≠ 0 := by
    intro h
    have hsum : 0 < ∑ j, p ⬝ᵥ (s j • ω₀) :=
      Finset.sum_pos (fun j _ => hw j) Finset.univ_nonempty
    simp only [dotProduct_smul, smul_eq_mul, ← Finset.sum_mul, h, zero_mul] at hsum
    exact lt_irrefl _ hsum
  rw [show s i * (p ⬝ᵥ ω₀) / ((∑ j, s j) * (p ⬝ᵥ ω₀)) * ∑ j, s j = s i by field_simp, sub_self]

/-- **Exercise 17.F.1** (MWG, p. 645), proportional consumptions (footnote 43). If the consumptions
are proportional among themselves (`xᵢ = sᵢ x₀`) and exhaust wealth (`p·xᵢ = p·ωᵢ > 0`), then
(17.F.2) is negative semidefinite on price changes with `dp·z(p) = 0`. -/
theorem exercise_17_F_1b [Nonempty ι] {S : ι → Matrix (Fin L) (Fin L) ℝ}
    (hS : ∀ i, ∀ v, v ⬝ᵥ (S i).mulVec v ≤ 0) {x₀ : Fin L → ℝ} {s : ι → ℝ}
    (ω : ι → Fin L → ℝ) {p : Fin L → ℝ} (hw : ∀ i, 0 < p ⬝ᵥ ω i)
    (hbud : ∀ i, p ⬝ᵥ (s i • x₀) = p ⬝ᵥ ω i) (dp : Fin L → ℝ)
    (hdp : dp ⬝ᵥ ∑ j, (s j • x₀ - ω j) = 0) :
    dp ⬝ᵥ (wadMatrix S (fun i => s i • x₀) ω p).mulVec dp ≤ 0 := by
  refine wad_nsd_of_cov_zero hS hw (fun i _ => Or.inr ?_) dp hdp
  simp only [← hbud, dotProduct_smul, smul_eq_mul, ← Finset.sum_mul, ← Finset.sum_smul,
    smul_smul]
  have hpx : p ⬝ᵥ x₀ ≠ 0 := by
    intro h
    have := hw i
    rw [← hbud i, dotProduct_smul, h, smul_zero] at this
    exact lt_irrefl _ this
  have hs : ∑ j, s j ≠ 0 := by
    intro h
    have hsum : 0 < ∑ j, p ⬝ᵥ ω j := Finset.sum_pos (fun j _ => hw j) Finset.univ_nonempty
    simp only [← hbud, dotProduct_smul, smul_eq_mul, ← Finset.sum_mul, h, zero_mul] at hsum
    exact lt_irrefl _ hsum
  rw [show s i * (p ⬝ᵥ x₀) / ((∑ j, s j) * (p ⬝ᵥ x₀)) * ∑ j, s j = s i by field_simp, sub_self]

/-- **Exercise 17.F.1** (MWG, p. 645), the restriction `dp·z(p) = 0` is needed. One consumer
(endowments and consumptions trivially proportional) with `S = 0`, `p = (1, 1)`, `ω = (1, 1)`,
`x = (2, 0)`: the matrix (17.F.2) is `-(1/2) x zᵀ` and `dp = (1, 2)` gives `dp·D dp = 1 > 0`. -/
theorem exercise_17_F_1_unrestricted :
    0 < ![(1 : ℝ), 2] ⬝ᵥ (wadMatrix (fun _ : Fin 1 => 0) (fun _ => ![2, 0]) (fun _ => ![1, 1])
      ![1, 1]).mulVec ![1, 2] := by
  simp [wadMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  norm_num

end MWG.PositiveEquilibriumTheory
