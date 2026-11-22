/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGCoreFoundations.DebreuScarf
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# The book's proof of Proposition 18.B.3 (MWG Section 18.B, pp. 657-659, 685)

* The special-case proof (pp. 657-658): from a type allocation that is not Walrasian, take a
  favoured type `h₁` (`exists_favoured_type`, `grad_dot_pos_of_proportional`) and form the
  coalition of `N - 1` members of type `h₁` and `N` of every other type, each member of type `h`
  getting `x'ₕ = xₕ + (x_{h₁} - ω_{h₁}) / ((N - 1) + N(H - 1))`. The displayed identity
  (`special_coalition_identity`) makes it feasible (`special_coalition_blocks`), the `x'ₕ` are
  nonnegative for large `N` when `xₕ ≫ 0` (`special_nonneg_eventually`), and, by
  **Exercise 18.B.4** (`exercise_18_B_4`, first-order Taylor: `∇u(x)·v > 0` gives
  `u(x + αv) > u(x)` for `0 < α < ᾱ`), every member gains for large `N`. Together:
  `proposition_18_B_3_special_case`.
* p. 659, pure exchange: `Vᵢ = {xᵢ ≥ 0 : xᵢ ≻ᵢ x*ᵢ} ∪ {ωᵢ}` (`coreVset`), `V = ∑ᵢ Vᵢ` (`coreV`),
  `∑ᵢ ωᵢ ∈ V` (`sum_endow_mem_coreV`), and the core property implies that `∑ᵢ ωᵢ` is not interior
  to `V` (`core_not_mem_interior_coreV`; this needs at least one good). If `p ≠ 0` supports `V` at
  `∑ᵢ ωᵢ`, then `p` is a Walrasian price vector for `x*` (`supporting_price_isWalrasEqm`) with
  continuity, strong monotonicity and **`ωᵢ ≫ 0`** (an added hypothesis: the final step
  `p·x'ᵢ > p·ωᵢ` needs `p·ωᵢ > 0`; without it the claim fails,
  `supporting_price_needs_positive_endowment`). `V` need not be convex
  (`coreVset_not_convex`).
* Footnote 6 (Anderson's proof) and the Aumann-Vind continuum remark are verbal.
-/

namespace MWG.CoreFoundations

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.Production MWG.WelfareTheorems
open Kreps.PreferenceProperties
open Filter Topology

variable {L : ℕ}

/-! ### The special-case proof (pp. 657-658) -/

/-- **Section 18.B** (MWG, p. 657). If the net trades of the types are worth `0` in total at `p`
but not all zero, some type `h` has `p·(xₕ - ωₕ) > 0` (a favoured type). -/
theorem exists_favoured_type {H : Type*} [Fintype H] {p : Fin L → ℝ} {x ω : H → Fin L → ℝ}
    (hsum : ∑ h, p ⬝ᵥ (x h - ω h) = 0) (hne : ∃ h, p ⬝ᵥ (x h - ω h) ≠ 0) :
    ∃ h, 0 < p ⬝ᵥ (x h - ω h) := by
  by_contra hall
  push Not at hall
  obtain ⟨h, hh⟩ := hne
  have := (Finset.sum_eq_zero_iff_of_nonpos fun k _ => hall k).mp hsum h (Finset.mem_univ h)
  exact hh this

/-- **Section 18.B** (MWG, p. 658). If `∇uₕ(xₕ) = μₕ p` with `μₕ > 0` and `p·(x₁ - ω₁) > 0`, then
`∇uₕ(xₕ)·(x₁ - ω₁) > 0`. -/
theorem grad_dot_pos_of_proportional {g p v : Fin L → ℝ} {μ : ℝ} (hμ : 0 < μ) (hg : g = μ • p)
    (hv : 0 < p ⬝ᵥ v) : 0 < g ⬝ᵥ v := by
  rw [hg, smul_dotProduct, smul_eq_mul]
  exact mul_pos hμ hv

/-- **Section 18.B** (MWG, p. 658), the displayed identity. Let `x` be a feasible type allocation,
`∑ₕ xₕ = y + ∑ₕ ωₕ`, and consider the coalition with `N - 1` members of type `h₁` and `N` of every
other type, `cₕ` members of type `h`, `D = ∑ₕ cₕ = (N - 1) + N(H - 1)`; every member of type `h`
gets `x'ₕ = xₕ + (x_{h₁} - ω_{h₁}) / D`. Then `∑ₕ cₕ x'ₕ = N y + ∑ₕ cₕ ωₕ` (the book has
`y = 0`). -/
theorem special_coalition_identity {H : Type*} [Fintype H] [DecidableEq H] (h₁ : H) (N : ℕ)
    {x ω : H → Fin L → ℝ} {y : Fin L → ℝ} (hsum : ∑ h, x h = y + ∑ h, ω h)
    (hD : (N : ℝ) * Fintype.card H - 1 ≠ 0) :
    ∑ h, ((N : ℝ) - if h = h₁ then 1 else 0) •
        (x h + ((N : ℝ) * Fintype.card H - 1)⁻¹ • (x h₁ - ω h₁)) =
      (N : ℝ) • y + ∑ h, ((N : ℝ) - if h = h₁ then 1 else 0) • ω h := by
  have hc : ∑ h : H, ((N : ℝ) - if h = h₁ then 1 else 0) = (N : ℝ) * Fintype.card H - 1 := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_ite_eq', Finset.mem_univ,
      ↓reduceIte, Finset.card_univ, nsmul_eq_mul]
    ring
  have hsplit : ∀ f : H → Fin L → ℝ,
      ∑ h, ((N : ℝ) - if h = h₁ then 1 else 0) • f h = (N : ℝ) • ∑ h, f h - f h₁ := by
    intro f
    simp only [sub_smul, Finset.sum_sub_distrib, ← Finset.smul_sum, ite_smul, one_smul,
      zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  simp only [smul_add, Finset.sum_add_distrib]
  rw [← Finset.sum_smul, hc, smul_smul, mul_inv_cancel₀ hD, one_smul, hsplit x, hsplit ω, hsum,
    smul_add]
  abel

/-- **Section 18.B** (MWG, p. 658). The coalition of all consumers of the `N`-replica except one of
type `h₁` blocks the equal-treatment allocation of `x` if every member of type `h` strictly
prefers `x'ₕ = xₕ + (x_{h₁} - ω_{h₁}) / ((N - 1) + N(H - 1))` and `x'ₕ ≥ 0` (constant returns:
`N y ∈ Y`). -/
theorem special_coalition_blocks {H : Type*} [Fintype H] [DecidableEq H] (E : CoreEconomy H L)
    (hY : IsCRSTechnology E.Y) (h₁ : H) {N : ℕ} (hN : 1 ≤ N)
    (hD : (N : ℝ) * Fintype.card H - 1 ≠ 0) {x : H → Fin L → ℝ} (hx : E.IsFeasible x)
    (hX : ∀ h, x h + ((N : ℝ) * Fintype.card H - 1)⁻¹ • (x h₁ - E.ω h₁) ∈ nonnegOrthant L)
    (hS : ∀ h, Strict (E.pref h) (x h + ((N : ℝ) * Fintype.card H - 1)⁻¹ • (x h₁ - E.ω h₁))
      (x h)) :
    (E.replica N).Blocks (Finset.univ.erase (h₁, ⟨0, hN⟩)) (typeAlloc x N) := by
  obtain ⟨-, y, hy, hsum⟩ := hx
  set x' : H → Fin L → ℝ := fun h => x h + ((N : ℝ) * Fintype.card H - 1)⁻¹ • (x h₁ - E.ω h₁)
    with hx'
  -- summing a function of the type over the coalition
  have hcoal : ∀ f : H → Fin L → ℝ, ∑ i ∈ Finset.univ.erase ((h₁, ⟨0, hN⟩) : H × Fin N), f i.1 =
      ∑ h, ((N : ℝ) - if h = h₁ then 1 else 0) • f h := by
    intro f
    have h1 := Finset.add_sum_erase Finset.univ (fun i : H × Fin N => f i.1)
      (Finset.mem_univ (h₁, ⟨0, hN⟩))
    have h2 : ∑ i : H × Fin N, f i.1 = (N : ℝ) • ∑ h, f h := by
      rw [Fintype.sum_prod_type]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ,
        Finset.smul_sum]
    simp only [sub_smul, Finset.sum_sub_distrib, ← Finset.smul_sum, ite_smul, one_smul,
      zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    rw [← h2, ← h1]
    abel
  refine ⟨?_, fun i => x' i.1, fun i _ => ⟨hX i.1,
    hS i.1⟩, (N : ℝ) • y, hY.2.2 y hy _ (Nat.cast_nonneg N), ?_⟩
  · obtain ⟨i, hi⟩ : (Finset.univ.erase ((h₁, ⟨0, hN⟩) : H × Fin N)).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
        Fintype.card_prod, Fintype.card_fin]
      have hH : 1 ≤ Fintype.card H := Fintype.card_pos_iff.mpr ⟨h₁⟩
      have h1 : 1 ≤ Fintype.card H * N := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero
        (Nat.one_le_iff_ne_zero.mp hH) (Nat.one_le_iff_ne_zero.mp hN))
      by_contra h0
      have : Fintype.card H * N = 1 := by omega
      apply hD
      have : ((Fintype.card H * N : ℕ) : ℝ) = 1 := by exact_mod_cast this
      push_cast at this
      linarith
    exact ⟨i, hi⟩
  · change ∑ i ∈ Finset.univ.erase ((h₁, ⟨0, hN⟩) : H × Fin N), x' i.1 =
      (N : ℝ) • y + ∑ i ∈ Finset.univ.erase ((h₁, ⟨0, hN⟩) : H × Fin N), E.ω i.1
    rw [hcoal, hcoal]
    exact special_coalition_identity h₁ N hsum hD

/-- **Section 18.B** (MWG, p. 658). If every `xₕ ≫ 0`, the consumptions
`x'ₕ = xₕ + (x_{h₁} - ω_{h₁}) / ((N - 1) + N(H - 1))` are nonnegative for all `N` large enough. -/
theorem special_nonneg_eventually {H : Type*} [Fintype H] (h₁ : H) {x ω : H → Fin L → ℝ}
    (hx : ∀ h l, 0 < x h l) : ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ h,
      x h + ((N : ℝ) * Fintype.card H - 1)⁻¹ • (x h₁ - ω h₁) ∈ nonnegOrthant L := by
  classical
  set v := x h₁ - ω h₁ with hv
  have hex : ∀ q : H × Fin L, ∃ M : ℕ, |v q.2| / x q.1 q.2 + 1 < M := fun q => exists_nat_gt _
  choose M hM using hex
  refine ⟨Finset.univ.sup M + 1, fun N hN h l => ?_⟩
  have hH : (1 : ℝ) ≤ Fintype.card H := by exact_mod_cast Fintype.card_pos_iff.mpr ⟨h₁⟩
  have hMN : (M (h, l) : ℝ) + 1 ≤ N := by
    have : M (h, l) ≤ Finset.univ.sup M := Finset.le_sup (Finset.mem_univ (h, l))
    exact_mod_cast (show M (h, l) + 1 ≤ N by omega)
  have hD : (N : ℝ) - 1 ≤ (N : ℝ) * Fintype.card H - 1 := by
    nlinarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have hlt := hM (h, l)
  have hxl := hx h l
  have hDpos : |v l| / x h l + 1 < (N : ℝ) * Fintype.card H - 1 := by
    simp only at hlt
    linarith
  have hD0 : 0 < (N : ℝ) * Fintype.card H - 1 := by
    have := div_nonneg (abs_nonneg (v l)) hxl.le
    linarith
  have habs : |v l| < ((N : ℝ) * Fintype.card H - 1) * x h l := by
    rw [div_add_one hxl.ne', div_lt_iff₀ hxl] at hDpos
    nlinarith
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have h1 : -(((N : ℝ) * Fintype.card H - 1) * x h l) < v l := by
    linarith [neg_abs_le (v l)]
  have h2 : -x h l < ((N : ℝ) * Fintype.card H - 1)⁻¹ * v l := by
    rw [inv_mul_eq_div, lt_div_iff₀ hD0]
    linarith
  change 0 ≤ x h l + ((N : ℝ) * Fintype.card H - 1)⁻¹ * v l
  linarith

/-- **Exercise 18.B.4** (MWG, p. 685), Taylor's formula to first order: if `u` is differentiable at
`x` with derivative `u'` and `u'(v) = ∇u(x)·v > 0`, there is `ᾱ > 0` with `u(x + αv) > u(x)` for all
`0 < α < ᾱ`. -/
theorem exercise_18_B_4 {u : (Fin L → ℝ) → ℝ} {u' : (Fin L → ℝ) →L[ℝ] ℝ} {x v : Fin L → ℝ}
    (hu : HasFDerivAt u u' x) (hv : 0 < u' v) :
    ∃ abar : ℝ, 0 < abar ∧ ∀ a : ℝ, 0 < a → a < abar → u x < u (x + a • v) := by
  have hl : HasDerivAt (fun a : ℝ => x + a • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hu0 : HasFDerivAt u u' (x + (0 : ℝ) • v) := by simpa using hu
  have hg : HasDerivAt (fun a : ℝ => u (x + a • v)) (u' v) 0 := hu0.comp_hasDerivAt 0 hl
  have hs := hasDerivAt_iff_tendsto_slope.mp hg
  have hev : ∀ᶠ a in 𝓝[>] (0 : ℝ), 0 < slope (fun a : ℝ => u (x + a • v)) 0 a :=
    ((hs.mono_left (nhdsWithin_mono 0 fun a (ha : 0 < a) => ha.ne')).eventually
      (lt_mem_nhds hv))
  obtain ⟨b, hb, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  refine ⟨b, hb, fun a ha hab => ?_⟩
  have := hsub ⟨ha, hab⟩
  change 0 < slope (fun a : ℝ => u (x + a • v)) 0 a at this
  simp only [slope_def_field, zero_smul, add_zero, sub_zero] at this
  have := (div_pos_iff_of_pos_right ha).mp this
  linarith

/-- **Exercise 18.B.4** (MWG, p. 685), with the gradient: `∇u(x)·v > 0` gives `u(x + αv) > u(x)`
for `0 < α < ᾱ`. -/
theorem exercise_18_B_4_grad {u : (Fin L → ℝ) → ℝ} {u' : (Fin L → ℝ) →L[ℝ] ℝ}
    {x v g : Fin L → ℝ} (hu : HasFDerivAt u u' x) (hg : ∀ w, u' w = g ⬝ᵥ w) (hv : 0 < g ⬝ᵥ v) :
    ∃ abar : ℝ, 0 < abar ∧ ∀ a : ℝ, 0 < a → a < abar → u x < u (x + a • v) :=
  exercise_18_B_4 hu (by rw [hg]; exact hv)

/-- **Proposition 18.B.3** (MWG, pp. 657-658), the book's special-case argument completed with
Exercise 18.B.4: let preferences be represented by utilities `uₕ` differentiable at `xₕ` with
`∇uₕ(xₕ)·(x_{h₁} - ω_{h₁}) > 0` for every type (the favoured type `h₁` of p. 657), `xₕ ≫ 0`, and
`x` a feasible type allocation (constant returns technology). Then for some `N ≥ 1` the coalition
of `N - 1` members of type `h₁` and `N` of every other type blocks, so `x ∉ C_N`. -/
theorem proposition_18_B_3_special_case {H : Type*} [Fintype H] (E : CoreEconomy H L)
    (hY : IsCRSTechnology E.Y) (u : H → (Fin L → ℝ) → ℝ) (hu : ∀ h, E.pref h = utilityPref (u h))
    (u' : H → (Fin L → ℝ) →L[ℝ] ℝ) {x : H → Fin L → ℝ} (hx : E.IsFeasible x)
    (hpos : ∀ h l, 0 < x h l) (h₁ : H) (hd : ∀ h, HasFDerivAt (u h) (u' h) (x h))
    (hgain : ∀ h, 0 < u' h (x h₁ - E.ω h₁)) : ∃ N, 1 ≤ N ∧ x ∉ E.CN N := by
  classical
  have hTay := fun h => exercise_18_B_4 (hd h) (hgain h)
  choose abar habar hgt using hTay
  have hne : (Finset.univ : Finset H).Nonempty := ⟨h₁, Finset.mem_univ h₁⟩
  set A := Finset.univ.inf' hne abar with hA
  have hA0 : 0 < A := (Finset.lt_inf'_iff hne).mpr fun h _ => habar h
  have hAle : ∀ h, A ≤ abar h := fun h => Finset.inf'_le _ (Finset.mem_univ h)
  obtain ⟨N₀, hN₀⟩ := special_nonneg_eventually (ω := E.ω) h₁ hpos
  obtain ⟨M, hM⟩ := exists_nat_gt (1 / A)
  set N := max (max N₀ 2) (M + 2) with hN
  have hN2 : 2 ≤ N := le_trans (le_max_right _ _) (le_max_left _ _)
  have hNM : M + 2 ≤ N := le_max_right _ _
  have hH : (1 : ℝ) ≤ Fintype.card H := by exact_mod_cast Fintype.card_pos_iff.mpr ⟨h₁⟩
  have hDge : (N : ℝ) - 1 ≤ (N : ℝ) * Fintype.card H - 1 := by
    nlinarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have hNM' : (M : ℝ) + 2 ≤ N := by exact_mod_cast hNM
  have hD0 : 0 < (N : ℝ) * Fintype.card H - 1 := by
    have : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    linarith
  have hDA : ((N : ℝ) * Fintype.card H - 1)⁻¹ < A := by
    rw [inv_lt_comm₀ hD0 hA0]
    have : 1 / A = A⁻¹ := one_div A
    linarith
  refine ⟨N, le_trans one_le_two hN2, fun hxC => hxC.2.2 _
    (special_coalition_blocks E hY h₁ (le_trans one_le_two hN2) hD0.ne' hx
    (hN₀ N (le_trans (le_max_left _ _) (le_max_left _ _))) fun h => ?_)⟩
  have := hgt h _ (inv_pos.mpr hD0) (lt_of_lt_of_le hDA (hAle h))
  rw [hu h]
  exact ⟨this.le, not_le.mpr this⟩

/-! ### Core allocations and supporting prices (p. 659) -/

/-- **Section 18.B** (MWG, p. 659). `Vᵢ = {xᵢ ∈ ℝ^L₊ : xᵢ ≻ᵢ x*ᵢ} ∪ {ωᵢ}`. -/
def coreVset {ι : Type*} (E : CoreEconomy ι L) (x : ι → Fin L → ℝ) (i : ι) :
    Set (Fin L → ℝ) :=
  {z | z ∈ nonnegOrthant L ∧ Strict (E.pref i) z (x i)} ∪ {E.ω i}

/-- **Section 18.B** (MWG, p. 659). `V = ∑ᵢ Vᵢ`. -/
def coreV {ι : Type*} [Fintype ι] (E : CoreEconomy ι L) (x : ι → Fin L → ℝ) :
    Set (Fin L → ℝ) :=
  {z | ∃ v : ι → Fin L → ℝ, (∀ i, v i ∈ coreVset E x i) ∧ ∑ i, v i = z}

/-- **Section 18.B** (MWG, p. 659). `∑ᵢ ωᵢ ∈ V`. -/
theorem sum_endow_mem_coreV {ι : Type*} [Fintype ι] (E : CoreEconomy ι L)
    (x : ι → Fin L → ℝ) : ∑ i, E.ω i ∈ coreV E x :=
  ⟨E.ω, fun _ => Or.inr rfl, rfl⟩

/-- **Section 18.B** (MWG, p. 659). In a pure exchange economy (with at least one good), if `x*`
has the core property then `∑ᵢ ωᵢ` is not in the interior of `V`: otherwise some `z ≪ ∑ᵢ ωᵢ` is in
`V`, and the consumers with `x'ᵢ ≠ ωᵢ` form a blocking coalition. -/
theorem core_not_mem_interior_coreV {ι : Type*} [Fintype ι] (E : CoreEconomy ι L)
    (hY : E.Y = nonposOrthant L) (hL : 0 < L) {x : ι → Fin L → ℝ} (hx : x ∈ E.core) :
    ∑ i, E.ω i ∉ interior (coreV E x) := by
  classical
  intro hint
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hint)
  set z : Fin L → ℝ := ∑ i, E.ω i - fun _ => ε / 2 with hz
  have hzb : z ∈ Metric.ball (∑ i, E.ω i) ε := by
    rw [Metric.mem_ball, dist_pi_lt_iff hε]
    intro l
    simp only [hz, Pi.sub_apply, Real.dist_eq, sub_sub_cancel_left, abs_neg]
    rw [abs_of_pos (by linarith)]
    linarith
  obtain ⟨v, hv, hvz⟩ := hball hzb
  set S := Finset.univ.filter (fun i => v i ≠ E.ω i) with hS
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => v i ≠ E.ω i) v
  have hrest : ∑ i ∈ Finset.univ.filter (fun i => ¬ v i ≠ E.ω i), v i =
      ∑ i ∈ Finset.univ.filter (fun i => ¬ v i ≠ E.ω i), E.ω i :=
    Finset.sum_congr rfl fun i hi => not_not.mp (Finset.mem_filter.mp hi).2
  have hsplitω := Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => v i ≠ E.ω i) E.ω
  apply hx.2 S
  refine ⟨?_, v, fun i hi => ?_, -(fun _ => ε / 2), ?_, ?_⟩
  · by_contra hSe
    rw [Finset.not_nonempty_iff_eq_empty] at hSe
    rw [← hS, hSe, Finset.sum_empty, zero_add, hrest] at hsplit
    have h1 : ∑ i ∈ Finset.univ.filter (fun i => ¬ v i ≠ E.ω i), E.ω i = ∑ i, E.ω i := by
      rw [← hsplitω, ← hS, hSe, Finset.sum_empty, zero_add]
    rw [h1, hvz] at hsplit
    have := congrFun hsplit ⟨0, hL⟩
    simp only [hz, Pi.sub_apply] at this
    linarith
  · rcases hv i with h | h
    · exact h
    · exact absurd h (Finset.mem_filter.mp hi).2
  · rw [hY]
    intro l
    simp only [Pi.neg_apply]
    linarith
  · rw [← hS] at hsplit hsplitω
    rw [hrest, hvz] at hsplit
    have : ∑ i ∈ S, v i = z - ∑ i ∈ Finset.univ.filter (fun i => ¬ v i ≠ E.ω i), E.ω i := by
      rw [← hsplit]; abel
    rw [this, hz, ← hsplitω]
    abel

/-- **Section 18.B** (MWG, p. 659), corrected. In a pure exchange economy with rational,
continuous, strongly monotone preferences and **strictly positive endowments**, if `x*` has the
core property and `p ≠ 0` supports `V` at `∑ᵢ ωᵢ` (`p·z ≥ p·∑ᵢ ωᵢ` on `V`), then `p` is a Walrasian
price vector for `x*`. The book's argument gives `p ≥ 0`, `p·x*ᵢ = p·ωᵢ` and `x'ᵢ ≻ᵢ x*ᵢ ⟹
p·x'ᵢ ≥ p·ωᵢ`; the final strengthening to `>` uses `p·ωᵢ > 0`, which needs an assumption such as
`ωᵢ ≫ 0` (`supporting_price_needs_positive_endowment`). -/
theorem supporting_price_isWalrasEqm {ι : Type*} [Fintype ι] [Nonempty ι] (E : CoreEconomy ι L)
    (hY : E.Y = nonposOrthant L) (hr : ∀ i, RationalOn (nonnegOrthant L) (E.pref i))
    (hc : ∀ i, PrefContinuous (nonnegOrthant L) (E.pref i))
    (hm : ∀ i, PrefStronglyMonotone (nonnegOrthant L) (E.pref i)) (hω : ∀ i l, 0 < E.ω i l)
    {x : ι → Fin L → ℝ} (hx : x ∈ E.core) {p : Fin L → ℝ} (hp : p ≠ 0)
    (hsupp : ∀ z ∈ coreV E x, p ⬝ᵥ ∑ i, E.ω i ≤ p ⬝ᵥ z) : E.IsWalrasEqm x p := by
  classical
  obtain ⟨⟨hxX, y, hy, hsum⟩, -⟩ := hx
  rw [hY] at hy
  -- a strictly preferred bundle costs at least `p·ωᵢ`
  have hpref : ∀ i, ∀ x' ∈ nonnegOrthant L, Strict (E.pref i) x' (x i) →
      p ⬝ᵥ E.ω i ≤ p ⬝ᵥ x' := by
    intro i x' hx' hs
    have hmem : ∑ k, Function.update E.ω i x' k ∈ coreV E x := by
      refine ⟨Function.update E.ω i x', fun k => ?_, rfl⟩
      by_cases hk : k = i
      · subst hk
        rw [Function.update_self]
        exact Or.inl ⟨hx', hs⟩
      · rw [Function.update_of_ne hk]
        exact Or.inr rfl
    have h1 := hsupp _ hmem
    rw [dotProduct_sum, dotProduct_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ i),
      ← Finset.add_sum_erase _ (fun k => p ⬝ᵥ Function.update E.ω i x' k)
        (Finset.mem_univ i), Function.update_self] at h1
    have h2 : ∑ k ∈ Finset.univ.erase i, p ⬝ᵥ Function.update E.ω i x' k =
        ∑ k ∈ Finset.univ.erase i, p ⬝ᵥ E.ω k :=
      Finset.sum_congr rfl fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
    linarith
  obtain ⟨i₀⟩ := (inferInstance : Nonempty ι)
  have hL : 0 < L := by
    by_contra hL0
    push Not at hL0
    apply hp
    funext l
    exact absurd l.2 (by omega)
  have hup : ∀ i, ∀ w : Fin L → ℝ, (∀ l, 0 ≤ w l) → w ≠ 0 →
      x i + w ∈ nonnegOrthant L ∧ Strict (E.pref i) (x i + w) (x i) := by
    intro i w hw hw0
    have hX : x i + w ∈ nonnegOrthant L := fun l => by
      simp only [Pi.add_apply]; linarith [hxX i l, hw l]
    refine ⟨hX, hm i (x i) (hxX i) _ hX (fun l => ?_) fun heq => hw0 ?_⟩
    · simp only [Pi.add_apply]; linarith [hw l]
    · simpa using heq
  have hone : p ⬝ᵥ (fun _ => (1 : ℝ)) = ∑ l, p l := by simp [dotProduct]
  -- `p ≥ 0`
  have hp0 : ∀ l, 0 ≤ p l := by
    intro l
    by_contra hneg
    push Not at hneg
    set c := p ⬝ᵥ x i₀ + ∑ k, p k - p ⬝ᵥ E.ω i₀ with hcdef
    set t := max 0 (c / -p l) + 1 with ht
    have ht0 : 0 ≤ t := by linarith [le_max_left 0 (c / -p l)]
    have ht2 : c / -p l ≤ t - 1 := by linarith [le_max_right 0 (c / -p l)]
    have hw : ∀ k, 0 ≤ ((fun _ => (1 : ℝ)) + Pi.single l t : Fin L → ℝ) k := by
      intro k
      by_cases hk : k = l
      · subst hk; simp; linarith
      · simp [hk]
    have hw0 : ((fun _ => (1 : ℝ)) + Pi.single l t : Fin L → ℝ) ≠ 0 := by
      intro h
      have := congrFun h l
      simp at this
      linarith
    obtain ⟨hX, hs⟩ := hup i₀ _ hw hw0
    have := hpref i₀ _ hX hs
    rw [dotProduct_add, dotProduct_add, hone] at this
    have hdot : p ⬝ᵥ (Pi.single l t : Fin L → ℝ) = p l * t := by simp
    rw [hdot] at this
    rw [div_le_iff₀ (by linarith)] at ht2
    nlinarith
  -- `p·x*ᵢ ≥ p·ωᵢ` (bundles slightly above `x*ᵢ`)
  have hS0 : 0 ≤ ∑ l, p l := Finset.sum_nonneg fun l _ => hp0 l
  have hxω : ∀ i, p ⬝ᵥ E.ω i ≤ p ⬝ᵥ x i := by
    intro i
    refine le_of_forall_pos_le_add fun ε' hε' => ?_
    set ε := ε' / (∑ k, p k + 1) with hε
    have hε0 : 0 < ε := div_pos hε' (by linarith)
    have hw0 : (fun _ => ε : Fin L → ℝ) ≠ 0 := by
      intro h
      have := congrFun h ⟨0, hL⟩
      simp only [Pi.zero_apply] at this
      linarith
    obtain ⟨hX, hs⟩ := hup i _ (fun _ => hε0.le) hw0
    have := hpref i _ hX hs
    rw [dotProduct_add] at this
    have hdot : p ⬝ᵥ (fun _ => ε) = ε * ∑ k, p k := by
      simp only [dotProduct]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    rw [hdot] at this
    have hεS : ε * ∑ k, p k ≤ ε' := by
      rw [hε, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  -- budgets balance, `p·y = 0`
  have hpy : p ⬝ᵥ y ≤ 0 :=
    Finset.sum_nonpos fun l _ => mul_nonpos_of_nonneg_of_nonpos (hp0 l) (hy l)
  have hsump : ∑ i, (p ⬝ᵥ x i - p ⬝ᵥ E.ω i) = p ⬝ᵥ y := by
    rw [Finset.sum_sub_distrib, ← dotProduct_sum, ← dotProduct_sum, hsum, dotProduct_add]
    ring
  have hbal : ∀ i, p ⬝ᵥ x i - p ⬝ᵥ E.ω i = 0 := by
    have hle : ∑ i, (p ⬝ᵥ x i - p ⬝ᵥ E.ω i) ≤ 0 := by rw [hsump]; exact hpy
    have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sub_nonneg.mpr (hxω i)).mp
      (le_antisymm hle (Finset.sum_nonneg fun i _ => sub_nonneg.mpr (hxω i)))
    exact fun i => this i (Finset.mem_univ i)
  have hy0 : p ⬝ᵥ y = 0 := by rw [← hsump]; exact Finset.sum_eq_zero fun i _ => hbal i
  refine ⟨⟨y, hY ▸ hy, hsum, fun y' hy' => ?_⟩, fun i => ?_⟩
  · rw [hY] at hy'
    rw [hy0]
    exact Finset.sum_nonpos fun l _ => mul_nonpos_of_nonneg_of_nonpos (hp0 l) (hy' l)
  -- the cheaper point argument, with `p·ωᵢ > 0`
  have hpω : 0 < p ⬝ᵥ E.ω i := dotProduct_pos_of_nonneg_ne_zero hp0 hp (hω i)
  refine isMaximalFor_of_strict_gt (hr i) (hxX i) (by linarith [hbal i]) fun x' hx' hs => ?_
  rcases (hpref i x' hx' hs).lt_or_eq with h3 | h3
  · exact h3
  exfalso
  obtain ⟨m, hmpos⟩ : ∃ m, 0 < p m * x' m := by
    by_contra hall
    push Not at hall
    have : p ⬝ᵥ x' ≤ 0 := Finset.sum_nonpos fun m _ => hall m
    linarith
  have hxm : 0 < x' m := by
    by_contra hle
    push Not at hle
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (hp0 m) hle]
  have hpm : 0 < p m := by
    by_contra hle
    push Not at hle
    have : p m = 0 := le_antisymm hle (hp0 m)
    rw [this, zero_mul] at hmpos
    exact lt_irrefl 0 hmpos
  obtain ⟨δ, hδ, hmem, hs'⟩ := exists_strict_sub_single (hr i) (hc i) hx' (hxX i) hs hxm
  have h4 := hpref i _ hmem hs'
  rw [dotProduct_sub, ← h3, dotProduct_single] at h4
  nlinarith

/-- **Section 18.B** (MWG, p. 659): the claim that a nonzero supporting price is Walrasian fails
without a positivity assumption on endowments. One consumer with `u = √x₁ + √x₂` and `ω = (1, 0)`:
`x* = ω` is in the core and `p = (0, 1) ≠ 0` supports `V` at `ω`, but `p` is not a Walrasian price
vector for `x*` (`(2, 0)` is affordable and better). -/
theorem supporting_price_needs_positive_endowment :
    (fun _ => ![1, 0]) ∈ dsEconomy.core ∧ (![0, 1] : Fin 2 → ℝ) ≠ 0 ∧
      (∀ z ∈ coreV dsEconomy (fun _ => ![1, 0]),
        ![0, 1] ⬝ᵥ ∑ i, dsEconomy.ω i ≤ ![0, 1] ⬝ᵥ z) ∧
      ¬ dsEconomy.IsWalrasEqm (fun _ => ![1, 0]) ![0, 1] := by
  refine ⟨oneZero_mem_core dsEconomy (fun _ => rfl) (fun _ => rfl) rfl, fun h => ?_, ?_,
    fun h => not_maximal_one_zero _ (h.2 0)⟩
  · have := congrFun h 1
    simp at this
  · rintro z ⟨v, hv, rfl⟩
    rw [Fin.sum_univ_one, Fin.sum_univ_one, dot_two, dot_two]
    change (0 : ℝ) * 1 + 1 * 0 ≤ 0 * v 0 0 + 1 * v 0 1
    rcases hv 0 with h | h
    · linarith [h.1 1]
    · rw [Set.mem_singleton_iff] at h
      rw [h]
      change (0 : ℝ) * 1 + 1 * 0 ≤ 0 * 1 + 1 * 0
      norm_num

/-- **Section 18.B** (MWG, p. 659). The sets `Vᵢ` need not be convex: in the example of p. 655
(`x*₁ = (1/3, 1/3)`, `ω₁ = (1, 0)`), `ω₁` and `(1, 1/4)` belong to `V₁` but `(1, 1/100)` does
not. -/
theorem coreVset_not_convex :
    ¬ Convex ℝ (coreVset (sqrtEconomy exampleEndow) exampleAlloc 0) := by
  intro hconv
  have h1 : (![1, 0] : Fin 2 → ℝ) ∈ coreVset (sqrtEconomy exampleEndow) exampleAlloc 0 :=
    Or.inr rfl
  have h2 : (![1, 1 / 4] : Fin 2 → ℝ) ∈ coreVset (sqrtEconomy exampleEndow) exampleAlloc 0 := by
    refine Or.inl ⟨fun l => by fin_cases l <;> norm_num, ?_⟩
    have hlt : sqrtU ![1 / 3, 1 / 3] < sqrtU ![1, 1 / 4] := by
      rw [sqrtU_vec, sqrtU_vec, Real.sqrt_one]
      have : (1 : ℝ) / 2 ≤ Real.sqrt (1 / 4) := Real.le_sqrt_of_sq_le (by norm_num)
      linarith [two_sqrt_third_lt]
    exact ⟨hlt.le, not_le.mpr hlt⟩
  have h3 := hconv h1 h2 (a := 24 / 25) (b := 1 / 25) (by norm_num) (by norm_num) (by norm_num)
  have heq : (24 / 25 : ℝ) • (![1, 0] : Fin 2 → ℝ) + (1 / 25 : ℝ) • ![1, 1 / 4] =
      ![1, 1 / 100] := by
    funext l
    fin_cases l <;> simp <;> norm_num
  rw [heq] at h3
  rcases h3 with h | h
  · have hlt : sqrtU ![1, 1 / 100] < sqrtU ![1 / 3, 1 / 3] := by
      rw [sqrtU_vec, sqrtU_vec, Real.sqrt_one]
      have ha : Real.sqrt (1 / 100) < 11 / 100 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
      have hb : (111 : ℝ) / 200 < Real.sqrt (1 / 3) := Real.lt_sqrt_of_sq_lt (by norm_num)
      linarith
    exact h.2.2 hlt.le
  · have := congrFun (Set.mem_singleton_iff.mp h) 1
    simp [sqrtEconomy, exampleEndow] at this

end MWG.CoreFoundations
