/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGWelfareTheorems.FirstOrder

/-!
# First-order conditions and the welfare theorems (MWG Section 16.F, pp. 563-566)

* p. 563: at a solution of (16.F.1) (`ūᵢ ≥ 0`, `uᵢ(0) = 0`) all constraints bind.
* **Exercise 16.F.3**: at an interior solution, (16.F.2)-(16.F.3) give the ratio conditions
  (16.F.4)-(16.F.6).
* The exact correspondences between (16.F.2)-(16.F.3) and the first-order conditions
  (16.F.10)-(16.F.11) of utility and profit maximization (`μ = p`, `δᵢ = 1/αᵢ`, `γⱼ = βⱼ`), and
  (16.F.13)-(16.F.14) of the weighted welfare problem (16.F.12) (`δᵢ = λᵢ/λ₁`, `μ = ψ/λ₁`,
  `γ = η/λ₁`).
* p. 565: with quasiconcave utilities and convex `Fⱼ`, a Pareto optimum is a price equilibrium
  with transfers at prices `p = μ ≫ 0`, wealth `wᵢ = p·xᵢ`; conversely every price equilibrium
  with transfers is Pareto optimal (first welfare theorem). The consumer and firm sufficiency
  steps are `consumer_max_of_foc` and `firm_max_of_foc`.
* **Proposition 16.F.1**: with concave `uᵢ` and convex `Fⱼ`, every Pareto optimum maximizes
  `∑ᵢ λᵢ uᵢ(xᵢ)` subject to the resource and technology constraints, with `λ_{i₀} = 1`; for
  `λᵢ > 0`, `1/λᵢ` is consumer `i`'s marginal utility of wealth `αᵢ` in (16.F.10) at the
  supporting prices. (The book writes `λ ≫ 0`; a weight can vanish, but only for a consumer with
  `xᵢ = 0`, where `αᵢ` is undefined.)
-/

namespace MWG.WelfareTheorems

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.Production Kreps.PreferenceProperties
open MWG.CompetitiveMarkets (Allocation)
open Filter Topology

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {L : ℕ}

/-- The tangent inequality of a convex function differentiable at `x`:
`F(x) + DF(x)(y - x) ≤ F(y)` for `x, y` in a convex set on which `F` is convex. -/
theorem convexOn_tangent_le {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {S : Set V} {F : V → ℝ} {F' : V →L[ℝ] ℝ} (hF : ConvexOn ℝ S F) {x y : V} (hx : x ∈ S)
    (hy : y ∈ S) (hd : HasFDerivAt F F' x) : F x + F' (y - x) ≤ F y := by
  set d := y - x with hdd
  have hline : HasDerivAt (fun t : ℝ => F (x + t • d)) (F' d) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => x + t • d) d 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const d).const_add x
    have h2 : HasFDerivAt F F' (x + (0 : ℝ) • d) := by simpa using hd
    exact h2.comp_hasDerivAt 0 h1
  have hslope := hline.tendsto_slope_zero_right
  have hbound : ∀ᶠ t in 𝓝[>] (0 : ℝ), t⁻¹ • (F (x + (0 + t) • d) - F (x + (0 : ℝ) • d)) ≤
      F y - F x := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    have hconv := hF.2 hx hy (by linarith [ht.2] : (0 : ℝ) ≤ 1 - t) ht.1.le (by ring)
    have heq : (1 - t) • x + t • y = x + t • d := by
      simp only [hdd, smul_sub, sub_smul, one_smul]; abel
    rw [heq, smul_eq_mul, smul_eq_mul] at hconv
    rw [zero_add, zero_smul, add_zero, smul_eq_mul, inv_mul_le_iff₀ ht.1]
    linarith
  exact (by linarith [le_of_tendsto hslope hbound] : F x + F' d ≤ F y)

/-- The tangent inequality of a concave function: `G(y) ≤ G(x) + DG(x)(y - x)`. -/
theorem concaveOn_le_tangent {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {S : Set V} {G : V → ℝ} {G' : V →L[ℝ] ℝ} (hG : ConcaveOn ℝ S G) {x y : V} (hx : x ∈ S)
    (hy : y ∈ S) (hd : HasFDerivAt G G' x) : G y ≤ G x + G' (y - x) := by
  have := convexOn_tangent_le hG.neg hx hy hd.neg
  simp only [Pi.neg_apply, neg_apply] at this
  linarith

/-- **Section 16.F** (MWG, p. 565), the consumer's side. Let `u` be quasiconcave, continuous and
nondecreasing on `ℝ^L₊`, differentiable at `x ≥ 0`, and let `p ≫ 0`, `δ > 0` satisfy
`δ ∂u/∂xₗ ≤ pₗ` with equality where `xₗ > 0` (that is, (16.F.10) with `α = 1/δ`). Then `x` is
maximal for `u` in the budget set `{y ≥ 0 : p·y ≤ p·x}`. -/
theorem consumer_max_of_foc {u : (Fin L → ℝ) → ℝ} {u' : (Fin L → ℝ) →L[ℝ] ℝ}
    (hq : QuasiconcaveOn ℝ (nonnegOrthant L) u) (hcont : ContinuousOn u (nonnegOrthant L))
    (hmono : ∀ x ∈ nonnegOrthant L, ∀ y, x ≤ y → u x ≤ u y) {x : Fin L → ℝ}
    (hx : x ∈ nonnegOrthant L) (hu : HasFDerivAt u u' x) {p : Fin L → ℝ}
    (hp : StrictlyPositive p) {δ : ℝ} (hδ : 0 < δ)
    (hfoc : ∀ l, δ * u' (Pi.single l 1) - p l ≤ 0)
    (hfoc_eq : ∀ l, 0 < x l → δ * u' (Pi.single l 1) - p l = 0) :
    IsMaximalFor (utilityPref u) (budgetSetOn (nonnegOrthant L) p (p ⬝ᵥ x)) x := by
  refine ⟨⟨hx, le_rfl⟩, fun y hy => ?_⟩
  change u y ≤ u x
  by_contra hlt
  push Not at hlt
  have hyX : y ∈ nonnegOrthant L := hy.1
  -- `y ≠ 0`, so `p·y > 0`
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact absurd (hmono 0 (fun _ => le_rfl) x hx) (not_le.mpr hlt)
  have hpy : 0 < p ⬝ᵥ y := by
    rw [dotProduct_comm]
    exact dotProduct_pos_of_nonneg_ne_zero hyX hy0 hp
  -- shrink `y` slightly: still better than `x`, now strictly cheaper
  set zs : ℕ → Fin L → ℝ := fun n => (1 - 1 / ((n : ℝ) + 2)) • y with hzs
  have hzsX : ∀ n, zs n ∈ nonnegOrthant L := fun n l => by
    have : 1 / ((n : ℝ) + 2) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    simp only [hzs, Pi.smul_apply, smul_eq_mul]
    exact mul_nonneg (by linarith) (hyX l)
  have hzst : Tendsto zs atTop (𝓝 y) := by
    have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
      refine this.congr fun n => ?_
      simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
      ring
    have h2 : Tendsto (fun n : ℕ => 1 - 1 / ((n : ℝ) + 2)) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h1
    have := ((continuous_id.smul (continuous_const (y := y))).tendsto (1 : ℝ)).comp h2
    simpa [hzs, Function.comp_def] using this
  obtain ⟨n, hn⟩ := exists_strict_of_tendsto (rationalOn_utilityPref _ u)
    (prefContinuous_utilityPref hcont) hyX hx ⟨hlt.le, not_le.mpr hlt⟩ hzsX hzst
  have hzx : u x ≤ u (zs n) := hn.1
  have hcheap : p ⬝ᵥ zs n < p ⬝ᵥ x := by
    have hs : 0 < 1 / ((n : ℝ) + 2) := by positivity
    simp only [hzs, dotProduct_smul, smul_eq_mul]
    nlinarith [hy.2]
  -- quasiconcavity: `∇u(x)·(zₙ - x) ≥ 0`, but the first-order conditions make it negative
  have hgrad := theorem_M_C_3_necessity hq hx (hzsX n) hu hzx
  have hle : u' (zs n - x) ≤ (p ⬝ᵥ zs n - p ⬝ᵥ x) / δ := by
    rw [clm_apply_eq_sum_partials, ← dotProduct_sub, dotProduct, Finset.sum_div]
    refine Finset.sum_le_sum fun l _ => ?_
    rw [mul_div_right_comm]
    rcases (hx l).lt_or_eq with hxl | hxl
    · have := hfoc_eq l hxl
      have : u' (Pi.single l 1) = p l / δ := by field_simp; linarith
      rw [this]
    · have h1 : (zs n - x) l = zs n l := by rw [Pi.sub_apply, ← hxl, sub_zero]
      rw [h1]
      have h2 : u' (Pi.single l 1) ≤ p l / δ := by
        rw [le_div_iff₀ hδ]; linarith [hfoc l]
      exact mul_le_mul_of_nonneg_right h2 (hzsX n l)
  have : (p ⬝ᵥ zs n - p ⬝ᵥ x) / δ < 0 := div_neg_of_neg_of_pos (by linarith) hδ
  linarith

/-- **Section 16.F** (MWG, p. 565), the firm's side. If `F` is convex and differentiable at `y*`,
`F(y*) ≤ 0`, `γ ≥ 0` with `γ F(y*) = 0`, and `pₗ = γ ∂F/∂yₗ(y*)` (16.F.11), then `y*` maximizes
profit on `{y : F(y) ≤ 0}`. -/
theorem firm_max_of_foc {F : (Fin L → ℝ) → ℝ} {F' : (Fin L → ℝ) →L[ℝ] ℝ}
    (hF : ConvexOn ℝ Set.univ F) {ys : Fin L → ℝ} (hys : F ys ≤ 0) (hd : HasFDerivAt F F' ys)
    {p : Fin L → ℝ} {γ : ℝ} (hγ : 0 ≤ γ) (hcs : γ * F ys = 0)
    (hfoc : ∀ l, p l - γ * F' (Pi.single l 1) = 0) : ys ∈ supply {y | F y ≤ 0} p := by
  refine ⟨hys, fun y hy => ?_⟩
  have hpl : ∀ l, p l = γ * F' (Pi.single l 1) := fun l => by linarith [hfoc l]
  have hp : ∀ z, p ⬝ᵥ z = γ * F' z := fun z => by
    rw [clm_apply_eq_sum_partials, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by rw [hpl l]; ring
  have htan := convexOn_tangent_le hF (Set.mem_univ ys) (Set.mem_univ y) hd
  have : p ⬝ᵥ (y - ys) ≤ 0 := by
    rw [hp]
    have hy' : F y ≤ 0 := hy
    nlinarith [mul_le_mul_of_nonneg_left htan hγ]
  rw [dotProduct_sub] at this
  linarith

/-- **Section 16.F** (MWG, p. 563). Under the assumptions of Exercise 16.F.2, with `uᵢ(0) = 0` and
required utility levels `ūᵢ ≥ 0`, all constraints of (16.F.1) bind at a solution: `uᵢ(xᵢ) = ūᵢ`
for `i ≠ i₀`, the resource constraints hold with equality and `Fⱼ(yⱼ) = 0`. -/
theorem section_16_F_constraints_bind [Nonempty κ] (hL : 0 < L) {u : ι → (Fin L → ℝ) → ℝ}
    {F : κ → (Fin L → ℝ) → ℝ} {ω : Fin L → ℝ} {i₀ : ι} {ub : ι → ℝ}
    {v : (ι → Fin L → ℝ) × (κ → Fin L → ℝ)} (hv : IsSolution16F1 u F ω i₀ ub v)
    {u' : ι → (Fin L → ℝ) →L[ℝ] ℝ} {F' : κ → (Fin L → ℝ) →L[ℝ] ℝ}
    (hu : ∀ i, HasFDerivAt (u i) (u' i) (v.1 i)) (hF : ∀ j, HasFDerivAt (F j) (F' j) (v.2 j))
    (hupos : ∀ i l, 0 < u' i (Pi.single l 1)) (hFpos : ∀ j l, 0 < F' j (Pi.single l 1))
    (hu0 : ∀ i, u i 0 = 0) (hub : ∀ i, 0 ≤ ub i) :
    (∀ i, i ≠ i₀ → u i (v.1 i) = ub i) ∧ (∀ l, ∑ i, v.1 i l = ω l + ∑ j, v.2 j l) ∧
      ∀ j, F j (v.2 j) = 0 := by
  obtain ⟨δ, μ, γ, hδ1, hδ0, hμ0, hγ0, hfoc, hfoc_eq, hfoc_y, hcsU, hcsR, hcsF⟩ :=
    exercise_16_F_2 hL hv hu hF hupos hFpos
  have hμpos : ∀ l, 0 < μ l := fun l => by
    have := hfoc i₀ l; rw [hδ1, one_mul] at this; linarith [hupos i₀ l]
  obtain ⟨j₀⟩ := ‹Nonempty κ›
  have hγpos : ∀ j, 0 < γ j := fun j => by
    have h1 := hfoc_y j ⟨0, hL⟩
    by_contra h
    have : γ j = 0 := le_antisymm (not_lt.mp h) (hγ0 j)
    rw [this, zero_mul, sub_zero] at h1
    linarith [hμpos ⟨0, hL⟩]
  refine ⟨fun i hi => ?_, fun l => ?_, fun j => ?_⟩
  · rcases (hδ0 i).lt_or_eq with hpos | hzero
    · have := hcsU i hi
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hpos.ne'
      · linarith
    · -- zero weight: consumer `i` consumes nothing
      have hx0 : v.1 i = 0 := funext fun l => by
        by_contra hne
        have hx : 0 < v.1 i l := lt_of_le_of_ne (hv.1.2.2.2 i l) (Ne.symm hne)
        have := hfoc_eq i l hx
        rw [← hzero, zero_mul, zero_sub, neg_eq_zero] at this
        exact absurd this (hμpos l).ne'
      have h1 := hv.1.1 i hi
      rw [hx0, hu0] at h1 ⊢
      linarith [hub i]
  · have := hcsR l
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (hμpos l).ne'
    · linarith
  · rcases mul_eq_zero.mp (hcsF j) with h | h
    · exact absurd h (hγpos j).ne'
    · exact h

omit [Fintype ι] [Fintype κ] in
/-- **Exercise 16.F.3** (MWG, p. 576; (16.F.4)-(16.F.6), p. 564). If the multipliers satisfy
(16.F.2) with equality (interior solution) and (16.F.3), with `δ_{i₀} = 1` and positive partial
derivatives `aᵢₗ = ∂uᵢ/∂x_{ℓi}`, `bⱼₗ = ∂Fⱼ/∂y_{ℓj}`, then all marginal rates of substitution and
transformation coincide: (16.F.4) `aᵢₗ/aᵢₗ' = aᵢ'ₗ/aᵢ'ₗ'`, (16.F.5) `bⱼₗ/bⱼₗ' = bⱼ'ₗ/bⱼ'ₗ'`,
(16.F.6) `aᵢₗ/aᵢₗ' = bⱼₗ/bⱼₗ'`. -/
theorem exercise_16_F_3 {a : ι → Fin L → ℝ} {b : κ → Fin L → ℝ} {δ : ι → ℝ} {μ : Fin L → ℝ}
    {γ : κ → ℝ} {i₀ : ι} (ha : ∀ i l, 0 < a i l) (hb : ∀ j l, 0 < b j l) (hδ1 : δ i₀ = 1)
    (hx : ∀ i l, δ i * a i l - μ l = 0) (hy : ∀ j l, μ l - γ j * b j l = 0) :
    (∀ i i' l l', a i l / a i l' = a i' l / a i' l') ∧
      (∀ j j' l l', b j l / b j l' = b j' l / b j' l') ∧
      (∀ i j l l', a i l / a i l' = b j l / b j l') := by
  have hμpos : ∀ l, 0 < μ l := fun l => by
    have := hx i₀ l; rw [hδ1, one_mul] at this; linarith [ha i₀ l]
  have key_a : ∀ i l l', a i l / a i l' = μ l / μ l' := by
    intro i l l'
    have hδ : 0 < δ i := by
      by_contra h
      have : δ i * a i l ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp h) (ha i l).le
      linarith [hμpos l, hx i l]
    have e1 : a i l = μ l / δ i := by field_simp; linarith [hx i l]
    have e2 : a i l' = μ l' / δ i := by field_simp; linarith [hx i l']
    rw [e1, e2]
    field_simp
  have key_b : ∀ j l l', b j l / b j l' = μ l / μ l' := by
    intro j l l'
    have hγ : 0 < γ j := by
      by_contra h
      have : γ j * b j l ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp h) (hb j l).le
      linarith [hμpos l, hy j l]
    have e1 : b j l = μ l / γ j := by field_simp; linarith [hy j l]
    have e2 : b j l' = μ l' / γ j := by field_simp; linarith [hy j l']
    rw [e1, e2]
    field_simp
  exact ⟨fun i i' l l' => by rw [key_a, key_a], fun j j' l l' => by rw [key_b, key_b],
    fun i j l l' => by rw [key_a, key_b]⟩

/-- **Section 16.F** (MWG, p. 565): (16.F.2) for consumer `i` with weight `δᵢ > 0` and prices
`μ` is (16.F.10) with `p = μ` and marginal utility of wealth `αᵢ = 1/δᵢ`. -/
theorem foc_16F2_iff_16F10 {a : Fin L → ℝ} {δ : ℝ} (hδ : 0 < δ) (μ x : Fin L → ℝ) :
    (∀ l, δ * a l - μ l ≤ 0 ∧ (0 < x l → δ * a l - μ l = 0)) ↔
      ∀ l, a l - (1 / δ) * μ l ≤ 0 ∧ (0 < x l → a l - (1 / δ) * μ l = 0) := by
  have key : ∀ l, a l - (1 / δ) * μ l = (δ * a l - μ l) / δ := fun l => by field_simp
  simp only [key, div_nonpos_iff, div_eq_zero_iff, hδ.ne', or_false]
  constructor
  · intro h l
    exact ⟨Or.inr ⟨(h l).1, hδ.le⟩, (h l).2⟩
  · intro h l
    refine ⟨?_, (h l).2⟩
    rcases (h l).1 with ⟨-, h2⟩ | ⟨h1, -⟩
    · linarith
    · exact h1

omit [Fintype ι] [Fintype κ] in
/-- **Section 16.F** (MWG, p. 566): with welfare weights `λ` (`λ_{i₀} > 0`), the first-order
conditions (16.F.13)-(16.F.14) of (16.F.12) with multipliers `ψ`, `η` are (16.F.2)-(16.F.3) with
`δᵢ = λᵢ/λ_{i₀}`, `μ = ψ/λ_{i₀}`, `γ = η/λ_{i₀}`. -/
theorem foc_16F13_iff_16F2 {a : ι → Fin L → ℝ} {b : κ → Fin L → ℝ} {lam : ι → ℝ}
    {ψ : Fin L → ℝ} {η : κ → ℝ} {i₀ : ι} (hl : 0 < lam i₀) (x : ι → Fin L → ℝ) :
    ((∀ i l, lam i * a i l - ψ l ≤ 0 ∧ (0 < x i l → lam i * a i l - ψ l = 0)) ∧
      ∀ j l, ψ l - η j * b j l = 0) ↔
    ((∀ i l, lam i / lam i₀ * a i l - ψ l / lam i₀ ≤ 0 ∧
        (0 < x i l → lam i / lam i₀ * a i l - ψ l / lam i₀ = 0)) ∧
      ∀ j l, ψ l / lam i₀ - η j / lam i₀ * b j l = 0) := by
  have k1 : ∀ i l, lam i / lam i₀ * a i l - ψ l / lam i₀ = (lam i * a i l - ψ l) / lam i₀ :=
    fun i l => by field_simp
  have k2 : ∀ j l, ψ l / lam i₀ - η j / lam i₀ * b j l = (ψ l - η j * b j l) / lam i₀ :=
    fun j l => by field_simp
  simp only [k1, k2, div_eq_zero_iff, hl.ne', or_false]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun i l => ⟨div_nonpos_of_nonpos_of_nonneg (h1 i l).1 hl.le, (h1 i l).2⟩, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun i l => ⟨?_, (h1 i l).2⟩, h2⟩
    have := (h1 i l).1
    rwa [div_nonpos_iff, or_iff_right (fun h => absurd h.2 (not_le.mpr hl)), and_iff_left hl.le]
      at this

/-- **Section 16.F** (MWG, p. 565). In the economy of Section 16.F (`J ≥ 1`, `L ≥ 1`, `∇uᵢ ≫ 0`,
`∇Fⱼ ≫ 0` everywhere), with quasiconcave utilities and convex `Fⱼ`, every Pareto optimal
allocation is a price equilibrium with transfers at some prices `p ≫ 0` (the multipliers `μ` of
(16.F.1)), with wealth levels `wᵢ = p·xᵢ`. -/
theorem section_16_F_pareto_isPriceEqm [Nonempty κ] (hL : 0 < L) {u : ι → (Fin L → ℝ) → ℝ}
    {u' : ι → (Fin L → ℝ) → (Fin L → ℝ) →L[ℝ] ℝ} {F : κ → (Fin L → ℝ) → ℝ}
    {F' : κ → (Fin L → ℝ) → (Fin L → ℝ) →L[ℝ] ℝ} {ω : Fin L → ℝ}
    (hu : ∀ i x, HasFDerivAt (u i) (u' i x) x) (hupos : ∀ i x l, 0 < u' i x (Pi.single l 1))
    (hF : ∀ j y, HasFDerivAt (F j) (F' j y) y) (hFpos : ∀ j y l, 0 < F' j y (Pi.single l 1))
    (hq : ∀ i, QuasiconcaveOn ℝ (nonnegOrthant L) (u i)) (hFc : ∀ j, ConvexOn ℝ Set.univ (F j))
    (i₀ : ι) {a : Allocation ι κ L} (hpo : (economy16F u F ω).IsParetoOptimal a) :
    ∃ p, StrictlyPositive p ∧
      (economy16F u F ω).IsPriceEqmWithTransfers a p (fun i => p ⬝ᵥ a.x i) := by
  have hFmono : ∀ j x y, x ≤ y → F j x ≤ F j y := fun j x y hxy =>
    mono_of_grad_pos (hF j) (hFpos j) hxy
  have hsol := exercise_16_F_1_ii (i₀ := i₀) hFmono hpo
  obtain ⟨δ, μ, γ, hδ1, hδ0, hμ0, hγ0, hfoc, hfoc_eq, hfoc_y, -, -, hcsF⟩ :=
    exercise_16_F_2 hL hsol (fun i => hu i (a.x i)) (fun j => hF j (a.y j))
      (fun i l => hupos i _ l) (fun j l => hFpos j _ l)
  have hμpos : ∀ l, 0 < μ l := fun l => by
    have := hfoc i₀ l; rw [hδ1, one_mul] at this; linarith [hupos i₀ (a.x i₀) l]
  obtain ⟨⟨hx, hy⟩, hc⟩ := hpo.1
  refine ⟨μ, hμpos, ?_, fun j => ?_, fun i => ?_, hc⟩
  · change ∑ i, μ ⬝ᵥ a.x i = μ ⬝ᵥ ω + ∑ j, μ ⬝ᵥ a.y j
    have hc' : ∑ i, a.x i = ω + ∑ j, a.y j := hc
    rw [← dotProduct_finset_sum, hc', dotProduct_add, dotProduct_finset_sum]
  · exact firm_max_of_foc (hFc j) (hy j) (hF j (a.y j)) (hγ0 j) (hcsF j) (hfoc_y j)
  · rcases (hδ0 i).lt_or_eq with hpos | hzero
    · exact consumer_max_of_foc (hq i) (fun x _ => (hu i x).continuousAt.continuousWithinAt)
        (fun x _ y hxy => by
          by_cases h : x = y
          · rw [h]
          · exact (strictMono_of_grad_pos (hu i) (hupos i) hxy h).le)
        (hx i) (hu i (a.x i)) hμpos hpos (hfoc i) (hfoc_eq i)
    · have hx0 : a.x i = 0 := funext fun l => by
        by_contra hne
        have hxl : 0 < a.x i l := lt_of_le_of_ne (hx i l) (Ne.symm hne)
        have := hfoc_eq i l hxl
        rw [← hzero, zero_mul, zero_sub, neg_eq_zero] at this
        exact absurd this (hμpos l).ne'
      refine ⟨⟨hx i, le_rfl⟩, fun y hy => ?_⟩
      have hy0 : y = 0 := by
        by_contra hne
        have := dotProduct_pos_of_nonneg_ne_zero hy.1 hne hμpos
        rw [dotProduct_comm] at this
        have h2 : μ ⬝ᵥ y ≤ μ ⬝ᵥ a.x i := hy.2
        rw [hx0, dotProduct_zero] at h2
        linarith
      rw [hy0, hx0]
      exact le_rfl

/-- **Section 16.F** (MWG, p. 565), both directions: in the economy of Section 16.F with
quasiconcave utilities and convex `Fⱼ`, an allocation is Pareto optimal if and only if it is a
price equilibrium with transfers for some price vector (and wealth levels). -/
theorem section_16_F_pareto_iff_priceEqm [Nonempty κ] (hL : 0 < L) {u : ι → (Fin L → ℝ) → ℝ}
    {u' : ι → (Fin L → ℝ) → (Fin L → ℝ) →L[ℝ] ℝ} {F : κ → (Fin L → ℝ) → ℝ}
    {F' : κ → (Fin L → ℝ) → (Fin L → ℝ) →L[ℝ] ℝ} {ω : Fin L → ℝ}
    (hu : ∀ i x, HasFDerivAt (u i) (u' i x) x) (hupos : ∀ i x l, 0 < u' i x (Pi.single l 1))
    (hF : ∀ j y, HasFDerivAt (F j) (F' j y) y) (hFpos : ∀ j y l, 0 < F' j y (Pi.single l 1))
    (hq : ∀ i, QuasiconcaveOn ℝ (nonnegOrthant L) (u i)) (hFc : ∀ j, ConvexOn ℝ Set.univ (F j))
    (i₀ : ι) (a : Allocation ι κ L) :
    (economy16F u F ω).IsParetoOptimal a ↔
      ∃ p w, (economy16F u F ω).IsPriceEqmWithTransfers a p w := by
  constructor
  · intro hpo
    obtain ⟨p, -, h⟩ := section_16_F_pareto_isPriceEqm hL hu hupos hF hFpos hq hFc i₀ hpo
    exact ⟨p, _, h⟩
  · rintro ⟨p, w, h⟩
    refine proposition_16_C_1 (fun i => rationalOn_utilityPref _ _) (fun i => ?_) h
    have hsm : PrefStronglyMonotone (nonnegOrthant L) (utilityPref (u i)) :=
      fun x _ y _ hxy hne => by
        have := strictMono_of_grad_pos (hu i) (hupos i) hxy (Ne.symm hne)
        exact ⟨this.le, not_le.mpr this⟩
    exact exercise_3_B_1b_orthant hL (exercise_3_B_1a hL hsm)

/-- **Proposition 16.F.1** (MWG, p. 566). In the economy of Section 16.F with concave utilities and
convex `Fⱼ` (`J ≥ 1`, `L ≥ 1`, `∇uᵢ ≫ 0`, `∇Fⱼ ≫ 0`), every Pareto optimal allocation maximizes a
weighted sum of utilities `∑ᵢ λᵢ uᵢ(xᵢ)` subject to `x ≥ 0`, the resource constraints and the
technology constraints, with `λ ≥ 0`, `λ_{i₀} = 1`. At the supporting prices `p = μ ≫ 0`, every
consumer with `λᵢ > 0` satisfies (16.F.10) with marginal utility of wealth `αᵢ = 1/λᵢ`; a consumer
with `λᵢ = 0` consumes nothing. -/
theorem proposition_16_F_1 [Nonempty κ] (hL : 0 < L) {u : ι → (Fin L → ℝ) → ℝ}
    {u' : ι → (Fin L → ℝ) → (Fin L → ℝ) →L[ℝ] ℝ} {F : κ → (Fin L → ℝ) → ℝ}
    {F' : κ → (Fin L → ℝ) → (Fin L → ℝ) →L[ℝ] ℝ} {ω : Fin L → ℝ}
    (hu : ∀ i x, HasFDerivAt (u i) (u' i x) x) (hupos : ∀ i x l, 0 < u' i x (Pi.single l 1))
    (hF : ∀ j y, HasFDerivAt (F j) (F' j y) y) (hFpos : ∀ j y l, 0 < F' j y (Pi.single l 1))
    (hcc : ∀ i, ConcaveOn ℝ (nonnegOrthant L) (u i)) (hFc : ∀ j, ConvexOn ℝ Set.univ (F j))
    (i₀ : ι) {a : Allocation ι κ L} (hpo : (economy16F u F ω).IsParetoOptimal a) :
    ∃ lam : ι → ℝ, lam i₀ = 1 ∧ (∀ i, 0 ≤ lam i) ∧
      (∀ (x : ι → Fin L → ℝ) (y : κ → Fin L → ℝ), (∀ i l, 0 ≤ x i l) →
        (∀ l, ∑ i, x i l ≤ ω l + ∑ j, y j l) → (∀ j, F j (y j) ≤ 0) →
        ∑ i, lam i * u i (x i) ≤ ∑ i, lam i * u i (a.x i)) ∧
      ∃ p, StrictlyPositive p ∧ (∀ i, lam i = 0 → a.x i = 0) ∧
        ∀ i, 0 < lam i → ∀ l, u' i (a.x i) (Pi.single l 1) - (1 / lam i) * p l ≤ 0 ∧
          (0 < a.x i l → u' i (a.x i) (Pi.single l 1) - (1 / lam i) * p l = 0) := by
  have hFmono : ∀ j x y, x ≤ y → F j x ≤ F j y := fun j x y hxy =>
    mono_of_grad_pos (hF j) (hFpos j) hxy
  have hsol := exercise_16_F_1_ii (i₀ := i₀) hFmono hpo
  obtain ⟨δ, μ, γ, hδ1, hδ0, hμ0, hγ0, hfoc, hfoc_eq, hfoc_y, -, -, hcsF⟩ :=
    exercise_16_F_2 hL hsol (fun i => hu i (a.x i)) (fun j => hF j (a.y j))
      (fun i l => hupos i _ l) (fun j l => hFpos j _ l)
  have hμpos : ∀ l, 0 < μ l := fun l => by
    have := hfoc i₀ l; rw [hδ1, one_mul] at this; linarith [hupos i₀ (a.x i₀) l]
  obtain ⟨⟨hx, hy⟩, hc⟩ := hpo.1
  have hc' : ∀ l, ∑ i, a.x i l = ω l + ∑ j, a.y j l := fun l => by
    have := congrFun hc l
    simpa [Finset.sum_apply, economy16F, PrefEconomy.ofUtility] using this
  have hzero : ∀ i, δ i = 0 → a.x i = 0 := fun i hz => funext fun l => by
    by_contra hne
    have hxl : 0 < a.x i l := lt_of_le_of_ne (hx i l) (Ne.symm hne)
    have := hfoc_eq i l hxl
    rw [hz, zero_mul, zero_sub, neg_eq_zero] at this
    exact absurd this (hμpos l).ne'
  refine ⟨δ, hδ1, hδ0, fun x y hxnn hres hFy => ?_, μ, hμpos, hzero, fun i hpos l => ?_⟩
  · -- the Lagrangian sufficiency argument
    have hcons : ∀ i, δ i * u i (x i) ≤ δ i * u i (a.x i) + δ i * u' i (a.x i) (x i - a.x i) :=
      fun i => by
        have := concaveOn_le_tangent (hcc i) (hx i) (fun l => hxnn i l) (hu i (a.x i))
        nlinarith [hδ0 i]
    have hgrad : ∀ i, δ i * u' i (a.x i) (x i - a.x i) ≤ ∑ l, μ l * (x i l - a.x i l) :=
      fun i => by
        rw [clm_apply_eq_sum_partials, Finset.mul_sum]
        refine Finset.sum_le_sum fun l _ => ?_
        rw [← mul_assoc, Pi.sub_apply]
        rcases (hx i l).lt_or_eq with hxl | hxl
        · have := hfoc_eq i l hxl
          have h2 : δ i * u' i (a.x i) (Pi.single l 1) = μ l := by linarith
          rw [h2]
        · rw [← hxl, sub_zero]
          exact mul_le_mul_of_nonneg_right (by linarith [hfoc i l]) (hxnn i l)
    have hfirm : ∀ j, ∑ l, μ l * (y j l - a.y j l) ≤ γ j * F j (y j) := fun j => by
      have htan := convexOn_tangent_le (hFc j) (Set.mem_univ (a.y j)) (Set.mem_univ (y j))
        (hF j (a.y j))
      have h1 : ∑ l, μ l * (y j l - a.y j l) = γ j * F' j (a.y j) (y j - a.y j) := by
        rw [clm_apply_eq_sum_partials, Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [show μ l = γ j * F' j (a.y j) (Pi.single l 1) by linarith [hfoc_y j l], Pi.sub_apply]
        ring
      rw [h1]
      have h2 := mul_le_mul_of_nonneg_left htan (hγ0 j)
      nlinarith [hcsF j]
    have hres' : ∑ i, ∑ l, μ l * (x i l - a.x i l) ≤ ∑ j, ∑ l, μ l * (y j l - a.y j l) := by
      rw [Finset.sum_comm, Finset.sum_comm (s := Finset.univ (α := κ))]
      refine Finset.sum_le_sum fun l _ => ?_
      rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
      refine mul_le_mul_of_nonneg_left ?_ (hμ0 l)
      linarith [hres l, hc' l]
    have h1 : ∑ i, δ i * u i (x i) ≤ ∑ i, δ i * u i (a.x i) +
        ∑ i, ∑ l, μ l * (x i l - a.x i l) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun i _ => (hcons i).trans (by linarith [hgrad i])
    have h2 : ∑ j, ∑ l, μ l * (y j l - a.y j l) ≤ 0 :=
      (Finset.sum_le_sum fun j _ => hfirm j).trans (Finset.sum_nonpos fun j _ =>
        mul_nonpos_of_nonneg_of_nonpos (hγ0 j) (hFy j))
    linarith
  · exact (foc_16F2_iff_16F10 hpos μ (a.x i)).mp (fun l => ⟨hfoc i l, hfoc_eq i l⟩) l

/-- **Footnote 18** (MWG, p. 563), correction 7: strictly positive gradients do not give the
constraint qualification of Theorem M.K.2 (linear independence of the binding constraint
gradients). Two consumers and one good, `u₁(x) = u₂(x) = x`, one firm `F(y) = y`, `ω̄ = 1`, and the
requirement `ū₂ = 1`: the solution of (16.F.1) is `x₁ = 0`, `x₂ = 1`, `y = 0`; four constraints
bind (consumer 2's utility, the resource constraint, the technology and `x₁ ≥ 0`) and their
gradients sum to zero. (The Kuhn-Tucker conditions still hold: `exercise_16_F_2`.) -/
theorem footnote_18_counterexample :
    IsSolution16F1 (ι := Fin 2) (κ := Unit) (L := 1) (fun _ x => x 0) (fun _ y => y 0) ![1] 0
        ![0, 1] (![![0], ![1]], fun _ => 0) ∧
      ¬ LinearIndependent ℝ ![resLin (ι := Fin 2) (κ := Unit) 0,
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).comp (projY ()),
        -((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).comp (projX 0)),
        -((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).comp (projX 1))] := by
  refine ⟨⟨⟨fun i hi => ?_, fun l => ?_, fun _ => le_rfl, fun i l => ?_⟩, ?_⟩, ?_⟩
  · fin_cases i
    · exact absurd rfl hi
    · simp
  · fin_cases l; simp [Fin.sum_univ_two]
  · fin_cases i <;> fin_cases l <;> simp
  · rintro v' ⟨hu, hres, hF, hnn⟩
    have h1 := hu 1 (by decide)
    have h2 := hres 0
    have h3 := hF ()
    have h4 := hnn 1 0
    simp [Fin.sum_univ_two] at h1 h2 h3 ⊢
    linarith
  · rw [Fintype.not_linearIndependent_iff]
    refine ⟨fun _ => 1, ?_, 0, one_ne_zero⟩
    refine ContinuousLinearMap.ext fun v => ?_
    simp [Fin.sum_univ_succ, resLin, projX, projY]
    ring

end MWG.WelfareTheorems
