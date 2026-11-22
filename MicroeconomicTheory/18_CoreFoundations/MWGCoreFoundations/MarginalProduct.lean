/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGCoreFoundations.Basic
import MWGWelfareTheorems.FirstOrderWelfare
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Equilibrium and the marginal productivity principle (MWG Section 18.E, pp. 670-673)

The quasilinear exchange economy of Section 18.E: `H` types, bundles `x = (y, m)` with
`y ∈ ℝ^K₊` (the `K = L - 1` non-numeraire goods) and money `m ∈ ℝ`, utilities
`u_h(y, m) = ψ_h(y) + m`, endowments `ω_h`. For a population `μ ∈ ℝ^H₊`,
`v(μ) = sup {∑ μ_h u_h(x_h) : ∑ μ_h x_h ≤ ∑ μ_h ω_h, y_h ≥ 0}` (18.E.1)/(18.E.2) (`QLEconomy.v`,
defined with `sSup`).

Proved here (examples and Exercise 18.E.3 are in `MarginalProductExamples`):
* homogeneity of `v` (p. 670) for every `r ≥ 0`, unconditionally, and `v(I/I) = v(I)/I`;
* finiteness: an affine majorant bounds `v` (`QLEconomy.v_le_of_majorant`), and concave,
  nondecreasing `ψ_h` differentiable at some point of `ℝ^K₊` admit one
  (`QLEconomy.exists_majorant`);
* **Exercise 18.E.1**: `v` is superadditive, concave and homogeneous of degree one on `ℝ^H₊`;
* **Footnote 20**: averaging within a type keeps feasibility and does not lower the objective, so
  the supremum over unequal allocations of a finite economy equals (18.E.1);
* **Definition 18.E.1** (with footnote 22 built in) and the Walrasian equilibrium of the
  continuum population;
* Euler's formula (`ql_euler`, Section M.B) by differentiating `t ↦ v(tμ)` at `t = 1`;
* **Proposition 18.E.1** (`proposition_18_E_1`), with **(18.E.4)** (`supporting_prices`) and
  **(18.E.5)** = **Exercise 18.E.2** (`exercise_18_E_2`);
* the finite-economy claims of p. 672: `Δ_h v ≥ ∂v/∂μ_h`, `∑ I_h Δ_h v ≥ v(I)`, impossibility of
  paying every consumer her marginal contribution (equal and unequal treatment), and the
  characterisation of Walrasian allocations of a finite economy by `u_h(x*_h) = ∂v(I)/∂μ_h`.

Departures. The multipliers (18.E.4) are obtained from first-order conditions for transfers of a
good between two types and for a surplus (not from Section M.K), and (18.E.5) from
`v(ν) ≤ ∑ ν_h [u_h(x*_h) + p·(ω_h - x*_h)]` on `ℝ^H₊` with equality at `μ` (not from the
envelope theorem of Section M.L). Hypotheses used are weaker than the book's: `ψ_h` concave and
nondecreasing (not strictly), differentiable only at `y*_h`; `v` differentiable only at `μ`;
`x* ≫ 0` only through `y* ≫ 0`; `ω_h ≥ 0` only for the non-numeraire goods. `v` is defined
with `sSup`; the book's "Max" is attained wherever an optimal allocation exists (e.g. at a
Walrasian allocation).
-/

namespace MWG.CoreFoundations

open Filter Topology

/-- **Section 18.E** (MWG, p. 670). A quasilinear exchange economy with types `h : H`: bundles
are pairs `(y, m)` with `y : Fin K → ℝ` the non-numeraire goods and `m ∈ ℝ` the numeraire (good
`L`); `u_h(y, m) = ψ_h(y) + m`; `ω h` is the endowment of type `h`. -/
structure QLEconomy (H : Type*) (K : ℕ) where
  /-- The functions `ψ_h` of the non-numeraire goods. -/
  ψ : H → (Fin K → ℝ) → ℝ
  /-- Endowments `ω_h = (ω_h^y, ω_h^m)`. -/
  ω : H → (Fin K → ℝ) × ℝ

variable {H : Type*} {K : ℕ}

/-- **Section 18.E** (MWG, p. 670). The quasilinear utility `u_h(y, m) = ψ_h(y) + m`. -/
def QLEconomy.u (E : QLEconomy H K) (h : H) (x : (Fin K → ℝ) × ℝ) : ℝ := E.ψ h x.1 + x.2

/-- **Section 18.E** (MWG, pp. 671-672). The value `p·x = q·y + m` of the bundle `x = (y, m)` at
the price vector `p = (q, 1)` (the numeraire has price `1`). -/
def qlPrice (q : Fin K → ℝ) (x : (Fin K → ℝ) × ℝ) : ℝ := q ⬝ᵥ x.1 + x.2

/-- **(18.E.2)** constraints and **footnote 22** (MWG, pp. 671). An equal-treatment allocation
`x` (one bundle per type) is feasible for the population `μ`: (ii) `y_h ≥ 0` for all `h`, and
(i) `∑_h μ_h x_h ≤ ∑_h μ_h ω_h`. -/
def QLEconomy.IsFeasible [Fintype H] (E : QLEconomy H K) (μ : H → ℝ)
    (x : H → (Fin K → ℝ) × ℝ) : Prop :=
  (∀ h, 0 ≤ (x h).1) ∧ ∑ h, μ h • x h ≤ ∑ h, μ h • E.ω h

/-- **(18.E.2)** (MWG, p. 671). The objective `∑_h μ_h u_h(x_h)`. -/
def QLEconomy.welfare [Fintype H] (E : QLEconomy H K) (μ : H → ℝ)
    (x : H → (Fin K → ℝ) × ℝ) : ℝ :=
  ∑ h, μ h * E.u h (x h)

/-- **(18.E.2)** (MWG, p. 671). The set of values of the objective over feasible allocations. -/
def QLEconomy.valueSet [Fintype H] (E : QLEconomy H K) (μ : H → ℝ) : Set ℝ :=
  {s | ∃ x, E.IsFeasible μ x ∧ E.welfare μ x = s}

/-- **(18.E.1)/(18.E.2)** (MWG, pp. 670-671). The maximal social utility
`v(μ) = sup {∑ μ_h u_h(x_h) : x feasible for μ}` (a `sSup`; it is a maximum whenever an
allocation attains it, `QLEconomy.IsOptimal`). -/
noncomputable def QLEconomy.v [Fintype H] (E : QLEconomy H K) (μ : H → ℝ) : ℝ :=
  sSup (E.valueSet μ)

/-- **(18.E.2)** (MWG, p. 671). `x` solves problem (18.E.2) for `μ`. -/
def QLEconomy.IsOptimal [Fintype H] (E : QLEconomy H K) (μ : H → ℝ)
    (x : H → (Fin K → ℝ) × ℝ) : Prop :=
  E.IsFeasible μ x ∧ ∀ x', E.IsFeasible μ x' → E.welfare μ x' ≤ E.welfare μ x

/-- **Definition 18.E.1** (MWG, p. 671). A feasible allocation `x*` for the population `μ` is a
marginal product (no-surplus) allocation: `u_h(x*_h) = ∂v(μ)/∂μ_h` for all `h` (18.E.3). The
partial derivatives are those of the Fréchet derivative; the book assumes `v` differentiable
(footnote 21), and every result below using this definition takes `DifferentiableAt ℝ E.v μ`. -/
def QLEconomy.IsMarginalProduct [Fintype H] [DecidableEq H] (E : QLEconomy H K)
    (μ : H → ℝ) (x : H → (Fin K → ℝ) × ℝ) : Prop :=
  E.IsFeasible μ x ∧ ∀ h, E.u h (x h) = fderiv ℝ E.v μ (Pi.single h 1)

/-- **Section 18.E** (MWG, pp. 671-672). A Walrasian equilibrium of the continuum population
`μ` with non-numeraire prices `q` (numeraire price `1`): the allocation is feasible as in
footnote 22, and each `x*_h` maximizes `u_h` on the budget set
`{x : y ≥ 0, q·y + m ≤ q·ω_h^y + ω_h^m}`. -/
def QLEconomy.IsWalrasEqm [Fintype H] (E : QLEconomy H K) (μ : H → ℝ) (q : Fin K → ℝ)
    (x : H → (Fin K → ℝ) × ℝ) : Prop :=
  E.IsFeasible μ x ∧ ∀ h, qlPrice q (x h) ≤ qlPrice q (E.ω h) ∧
    ∀ x' : (Fin K → ℝ) × ℝ, 0 ≤ x'.1 → qlPrice q x' ≤ qlPrice q (E.ω h) →
      E.u h x' ≤ E.u h (x h)

/-! ### The price functional -/

/-- The price functional is linear in aggregates: `p·∑ μ_h x_h = ∑ μ_h p·x_h`. -/
theorem qlPrice_sum [Fintype H] (q : Fin K → ℝ) (μ : H → ℝ) (x : H → (Fin K → ℝ) × ℝ) :
    qlPrice q (∑ h, μ h • x h) = ∑ h, μ h * qlPrice q (x h) := by
  simp only [qlPrice, Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd, dotProduct_sum,
    dotProduct_smul, smul_eq_mul, mul_add, Finset.sum_add_distrib]

/-- The price functional of a difference. -/
theorem qlPrice_sub (q : Fin K → ℝ) (x x' : (Fin K → ℝ) × ℝ) :
    qlPrice q (x - x') = qlPrice q x - qlPrice q x' := by
  simp only [qlPrice, Prod.fst_sub, Prod.snd_sub, dotProduct_sub]
  ring

/-- With `q ≥ 0` the price functional is monotone. -/
theorem qlPrice_mono {q : Fin K → ℝ} (hq : 0 ≤ q) {x x' : (Fin K → ℝ) × ℝ} (h : x ≤ x') :
    qlPrice q x ≤ qlPrice q x' := by
  unfold qlPrice
  have h1 : q ⬝ᵥ x.1 ≤ q ⬝ᵥ x'.1 := dotProduct_le_dotProduct_of_nonneg_left h.1 hq
  linarith [h.2]

/-! ### Upper bounds and finiteness of `v` -/

/-- The endowment allocation is feasible when `ω_h^y ≥ 0`, so the value set is nonempty. -/
theorem QLEconomy.valueSet_nonempty [Fintype H] (E : QLEconomy H K)
    (hω : ∀ h, 0 ≤ (E.ω h).1) (μ : H → ℝ) : (E.valueSet μ).Nonempty :=
  ⟨_, E.ω, ⟨hω, le_rfl⟩, rfl⟩

/-- If every `u_h` is majorised on `{y ≥ 0}` by `c_h + p·x` with `p = (q, 1)`, `q ≥ 0`, then the
objective of every feasible allocation for `μ ≥ 0` is at most `∑ μ_h c_h + p·∑ μ_h ω_h`. -/
theorem QLEconomy.welfare_le_of_majorant [Fintype H] (E : QLEconomy H K) {μ : H → ℝ}
    (hμ : 0 ≤ μ) {q : Fin K → ℝ} (hq : 0 ≤ q) (c : H → ℝ)
    (hmaj : ∀ h x, 0 ≤ x.1 → E.u h x ≤ c h + qlPrice q x) {x : H → (Fin K → ℝ) × ℝ}
    (hx : E.IsFeasible μ x) :
    E.welfare μ x ≤ ∑ h, μ h * c h + qlPrice q (∑ h, μ h • E.ω h) := by
  have h1 : E.welfare μ x ≤ ∑ h, μ h * (c h + qlPrice q (x h)) :=
    Finset.sum_le_sum fun h _ => mul_le_mul_of_nonneg_left (hmaj h (x h) (hx.1 h)) (hμ h)
  have h2 : ∑ h, μ h * (c h + qlPrice q (x h)) =
      ∑ h, μ h * c h + qlPrice q (∑ h, μ h • x h) := by
    rw [qlPrice_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun h _ => by ring
  have h3 := qlPrice_mono hq hx.2
  linarith

/-- Under an affine majorant, `v(μ) ≤ ∑ μ_h c_h + p·∑ μ_h ω_h` for `μ ≥ 0`. -/
theorem QLEconomy.v_le_of_majorant [Fintype H] (E : QLEconomy H K)
    (hω : ∀ h, 0 ≤ (E.ω h).1) {μ : H → ℝ} (hμ : 0 ≤ μ) {q : Fin K → ℝ} (hq : 0 ≤ q)
    (c : H → ℝ) (hmaj : ∀ h x, 0 ≤ x.1 → E.u h x ≤ c h + qlPrice q x) :
    E.v μ ≤ ∑ h, μ h * c h + qlPrice q (∑ h, μ h • E.ω h) := by
  refine csSup_le (E.valueSet_nonempty hω μ) ?_
  rintro s ⟨x, hx, rfl⟩
  exact E.welfare_le_of_majorant hμ hq c hmaj hx

/-- Under an affine majorant the value set is bounded above for every `μ ≥ 0`. -/
theorem QLEconomy.bddAbove_of_majorant [Fintype H] (E : QLEconomy H K) {μ : H → ℝ}
    (hμ : 0 ≤ μ) {q : Fin K → ℝ} (hq : 0 ≤ q) (c : H → ℝ)
    (hmaj : ∀ h x, 0 ≤ x.1 → E.u h x ≤ c h + qlPrice q x) : BddAbove (E.valueSet μ) := by
  refine ⟨∑ h, μ h * c h + qlPrice q (∑ h, μ h • E.ω h), ?_⟩
  rintro s ⟨x, hx, rfl⟩
  exact E.welfare_le_of_majorant hμ hq c hmaj hx

/-- A continuous linear functional on `ι → ℝ` is `z ↦ ∑ᵢ zᵢ D(eᵢ)`. -/
theorem ql_clm_apply_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : (ι → ℝ) →L[ℝ] ℝ) (z : ι → ℝ) : D z = ∑ i, z i * D (Pi.single i 1) := by
  conv_lhs => rw [← Finset.univ_sum_single z]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : Pi.single i (z i) = z i • (Pi.single i (1 : ℝ) : ι → ℝ) := by
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  rw [this, map_smul, smul_eq_mul]

/-- The line `t ↦ z + t • d` has derivative `D d` under `f` when `f` has derivative `D` at
`z`. -/
theorem ql_hasDerivAt_line {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {f : E' → ℝ} {D : E' →L[ℝ] ℝ} {z : E'} (hf : HasFDerivAt f D z) (d : E') :
    HasDerivAt (fun t : ℝ => f (z + t • d)) (D d) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => z + t • d) d 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const d).const_add z
  have h2 : HasFDerivAt f D (z + (0 : ℝ) • d) := by simpa using hf
  exact h2.comp_hasDerivAt 0 h1

/-- The derivative of a function nondecreasing on `ℝ^K₊`, at a point `z ≥ 0`, is nonnegative
in every coordinate direction. -/
theorem ql_fderiv_single_nonneg {f : (Fin K → ℝ) → ℝ} {D : (Fin K → ℝ) →L[ℝ] ℝ}
    {z : Fin K → ℝ} (hmono : MonotoneOn f (Set.Ici 0)) (hz : 0 ≤ z) (hf : HasFDerivAt f D z)
    (l : Fin K) : 0 ≤ D (Pi.single l 1) := by
  have hslope := (ql_hasDerivAt_line hf (Pi.single l 1)).tendsto_slope_zero_right
  refine ge_of_tendsto hslope ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  have hle : z ≤ z + t • (Pi.single l 1 : Fin K → ℝ) := by
    intro k
    have : 0 ≤ t * (Pi.single l (1 : ℝ) : Fin K → ℝ) k := by
      rcases eq_or_ne k l with rfl | hk
      · simp [ht.le]
      · simp [hk]
    simpa using this
  have hmon := hmono (Set.mem_Ici.2 hz) (Set.mem_Ici.2 (hz.trans hle)) hle
  simp only [zero_add, zero_smul, add_zero, smul_eq_mul]
  exact mul_nonneg (inv_nonneg.2 ht.le) (by linarith)

/-- **Section 18.E** (MWG, p. 670): finiteness of the supremum. If each `ψ_h` is concave and
nondecreasing on `ℝ^K₊` and differentiable at some `z_h ≥ 0`, then all `u_h` share an affine
majorant `c_h + q·y + m` with `q ≥ 0` (tangent planes, with `q` the sum of the gradients). -/
theorem QLEconomy.exists_majorant [Finite H] (E : QLEconomy H K)
    (hconc : ∀ h, ConcaveOn ℝ (Set.Ici 0) (E.ψ h)) (hmono : ∀ h, MonotoneOn (E.ψ h) (Set.Ici 0))
    (hdiff : ∀ h, ∃ z, 0 ≤ z ∧ DifferentiableAt ℝ (E.ψ h) z) :
    ∃ q : Fin K → ℝ, 0 ≤ q ∧ ∃ c : H → ℝ, ∀ h x, 0 ≤ x.1 → E.u h x ≤ c h + qlPrice q x := by
  have : Fintype H := Fintype.ofFinite H
  choose z hz hdz using hdiff
  set D := fun h => fderiv ℝ (E.ψ h) (z h)
  have hD : ∀ h, HasFDerivAt (E.ψ h) (D h) (z h) := fun h => (hdz h).hasFDerivAt
  have hg : ∀ h l, 0 ≤ D h (Pi.single l 1) := fun h l =>
    ql_fderiv_single_nonneg (hmono h) (hz h) (hD h) l
  refine ⟨fun l => ∑ h, D h (Pi.single l 1), fun l => Finset.sum_nonneg fun h _ => hg h l,
    fun h => E.ψ h (z h) - D h (z h), fun h x hx => ?_⟩
  have ht := MWG.WelfareTheorems.concaveOn_le_tangent (hconc h) (Set.mem_Ici.2 (hz h))
    (Set.mem_Ici.2 hx) (hD h)
  rw [map_sub] at ht
  have hle : D h x.1 ≤ (fun l => ∑ k, D k (Pi.single l 1)) ⬝ᵥ x.1 := by
    rw [ql_clm_apply_eq_sum, dotProduct]
    refine Finset.sum_le_sum fun l _ => ?_
    rw [mul_comm (x.1 l)]
    refine mul_le_mul_of_nonneg_right ?_ (hx l)
    exact Finset.single_le_sum (f := fun k => D k (Pi.single l 1)) (fun k _ => hg k l)
      (Finset.mem_univ h)
  simp only [QLEconomy.u, qlPrice]
  linarith

/-! ### Homogeneity (p. 670) -/

open Pointwise in
/-- Scaling the population by `r > 0` scales the value set. -/
theorem QLEconomy.valueSet_smul [Fintype H] (E : QLEconomy H K) {r : ℝ} (hr : 0 < r)
    (μ : H → ℝ) : E.valueSet (r • μ) = r • E.valueSet μ := by
  ext s
  constructor
  · rintro ⟨x, ⟨hx0, hx⟩, rfl⟩
    refine ⟨E.welfare μ x, ⟨x, ⟨hx0, ?_⟩, rfl⟩, ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul, ← smul_smul, ← Finset.smul_sum] at hx
      exact (smul_le_smul_iff_of_pos_left hr).1 hx
    · simp only [QLEconomy.welfare, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
  · rintro ⟨t, ⟨x, ⟨hx0, hx⟩, rfl⟩, rfl⟩
    refine ⟨x, ⟨hx0, ?_⟩, ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul, ← smul_smul, ← Finset.smul_sum]
      exact (smul_le_smul_iff_of_pos_left hr).2 hx
    · simp only [QLEconomy.welfare, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

/-- `v(0) = 0`. -/
theorem QLEconomy.v_zero [Fintype H] (E : QLEconomy H K) : E.v 0 = 0 := by
  have : E.valueSet 0 = {0} := by
    ext s
    constructor
    · rintro ⟨x, -, rfl⟩
      simp [QLEconomy.welfare]
    · rintro rfl
      exact ⟨0, ⟨fun _ => le_rfl, by simp⟩, by simp [QLEconomy.welfare]⟩
  rw [QLEconomy.v, this, csSup_singleton]

open Pointwise in
/-- **Section 18.E** (MWG, p. 670). `v` is homogeneous of degree one:
`v(r μ) = r v(μ)` for every `r ≥ 0` (no assumption needed: the value set scales). -/
theorem QLEconomy.v_smul [Fintype H] (E : QLEconomy H K) {r : ℝ} (hr : 0 ≤ r) (μ : H → ℝ) :
    E.v (r • μ) = r * E.v μ := by
  rcases hr.eq_or_lt with rfl | hr
  · rw [zero_smul, zero_mul, E.v_zero]
  · rw [QLEconomy.v, E.valueSet_smul hr, Real.sSup_smul_of_nonneg hr.le, smul_eq_mul,
      QLEconomy.v]

/-- **Section 18.E** (MWG, p. 670). `v(I₁/I, …, I_H/I) = v(I₁, …, I_H)/I` for `I > 0`. -/
theorem QLEconomy.v_div [Fintype H] (E : QLEconomy H K) (I : H → ℝ) {N : ℝ} (hN : 0 < N) :
    E.v (fun h => I h / N) = E.v I / N := by
  have : (fun h => I h / N) = N⁻¹ • I := by
    ext h; simp [div_eq_inv_mul]
  rw [this, E.v_smul (inv_nonneg.2 hN.le), inv_mul_eq_div]

/-! ### Exercise 18.E.1: concavity -/

/-- The set `{x : y ≥ 0}` of bundles is convex. -/
theorem ql_convex_bundles : Convex ℝ {x : (Fin K → ℝ) × ℝ | 0 ≤ x.1} := by
  intro x hx y hy a b ha hb _
  change 0 ≤ (a • x + b • y).1
  simp only [Prod.fst_add, Prod.smul_fst]
  exact add_nonneg (smul_nonneg ha hx) (smul_nonneg hb hy)

/-- `u_h(y, m) = ψ_h(y) + m` is concave on `{y ≥ 0}` when `ψ_h` is concave on `ℝ^K₊`. -/
theorem QLEconomy.u_concaveOn (E : QLEconomy H K) {h : H}
    (hconc : ConcaveOn ℝ (Set.Ici 0) (E.ψ h)) :
    ConcaveOn ℝ {x : (Fin K → ℝ) × ℝ | 0 ≤ x.1} (E.u h) := by
  refine ⟨ql_convex_bundles, fun x hx y hy a b ha hb hab => ?_⟩
  have h1 := hconc.2 (Set.mem_Ici.2 hx) (Set.mem_Ici.2 hy) ha hb hab
  simp only [QLEconomy.u, Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd,
    smul_eq_mul] at h1 ⊢
  linarith

/-- **Exercise 18.E.1** (MWG, p. 671), superadditivity: for `μ, ν ≥ 0`,
`v(μ) + v(ν) ≤ v(μ + ν)` (given bounded value sets and `ω_h^y ≥ 0`). Each type's bundle in the
merged population is the population-weighted average, which is feasible, and concavity of `u_h`
does the rest. -/
theorem QLEconomy.v_superadditive [Fintype H] (E : QLEconomy H K)
    (hconc : ∀ h, ConcaveOn ℝ (Set.Ici 0) (E.ψ h)) (hω : ∀ h, 0 ≤ (E.ω h).1)
    (hbdd : ∀ μ : H → ℝ, 0 ≤ μ → BddAbove (E.valueSet μ)) {μ ν : H → ℝ} (hμ : 0 ≤ μ)
    (hν : 0 ≤ ν) : E.v μ + E.v ν ≤ E.v (μ + ν) := by
  have hμh : ∀ h, 0 ≤ μ h := fun h => hμ h
  have hνh : ∀ h, 0 ≤ ν h := fun h => hν h
  -- the key inequality for a pair of allocations
  have key : ∀ x x', E.IsFeasible μ x → E.IsFeasible ν x' →
      E.welfare μ x + E.welfare ν x' ≤ E.v (μ + ν) := by
    intro x x' hx hx'
    classical
    let s : H → ℝ := fun h => μ h + ν h
    let z : H → (Fin K → ℝ) × ℝ := fun h =>
      if s h = 0 then 0 else ((s h)⁻¹ * μ h) • x h + ((s h)⁻¹ * ν h) • x' h
    have hz : ∀ h, s h • z h = μ h • x h + ν h • x' h ∧
        μ h * E.u h (x h) + ν h * E.u h (x' h) ≤ s h * E.u h (z h) ∧ 0 ≤ (z h).1 := by
      intro h
      by_cases hs : s h = 0
      · have h0 : μ h = 0 := by linarith [hμh h, hνh h, show μ h + ν h = 0 from hs]
        have h0' : ν h = 0 := by linarith [hμh h, hνh h, show μ h + ν h = 0 from hs]
        simp only [z, hs, ↓reduceIte, h0, h0', zero_smul, add_zero, zero_mul, le_refl,
          true_and]
        exact le_rfl
      · have hspos : 0 < s h := lt_of_le_of_ne (add_nonneg (hμh h) (hνh h)) (Ne.symm hs)
        have hw1 : 0 ≤ (s h)⁻¹ * μ h := mul_nonneg (inv_nonneg.2 hspos.le) (hμh h)
        have hw2 : 0 ≤ (s h)⁻¹ * ν h := mul_nonneg (inv_nonneg.2 hspos.le) (hνh h)
        have hw : (s h)⁻¹ * μ h + (s h)⁻¹ * ν h = 1 := by
          rw [← mul_add]; exact inv_mul_cancel₀ hs
        simp only [z, hs, ↓reduceIte]
        refine ⟨?_, ?_, ?_⟩
        · rw [smul_add, smul_smul, smul_smul, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hs,
            one_mul, one_mul]
        · have hc := (E.u_concaveOn (hconc h)).2 (hx.1 h) (hx'.1 h) hw1 hw2 hw
          simp only [smul_eq_mul] at hc
          have := mul_le_mul_of_nonneg_left hc hspos.le
          calc μ h * E.u h (x h) + ν h * E.u h (x' h)
              = s h * ((s h)⁻¹ * μ h * E.u h (x h) + (s h)⁻¹ * ν h * E.u h (x' h)) := by
                field_simp
            _ ≤ _ := this
        · exact ql_convex_bundles (hx.1 h) (hx'.1 h) hw1 hw2 hw
    have hfeas : E.IsFeasible (μ + ν) z := by
      refine ⟨fun h => (hz h).2.2, ?_⟩
      have e1 : ∑ h, (μ + ν) h • z h = ∑ h, μ h • x h + ∑ h, ν h • x' h := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun h _ => (hz h).1
      have e2 : ∑ h, (μ + ν) h • E.ω h = ∑ h, μ h • E.ω h + ∑ h, ν h • E.ω h := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun h _ => by rw [Pi.add_apply, add_smul]
      rw [e1, e2]
      exact ⟨add_le_add hx.2.1 hx'.2.1, add_le_add hx.2.2 hx'.2.2⟩
    have hle : E.welfare μ x + E.welfare ν x' ≤ E.welfare (μ + ν) z := by
      unfold QLEconomy.welfare
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun h _ => (hz h).2.1
    exact hle.trans (le_csSup (hbdd _ (add_nonneg hμh hν)) ⟨z, hfeas, rfl⟩)
  -- pass to suprema
  have step : ∀ x', E.IsFeasible ν x' → E.v μ ≤ E.v (μ + ν) - E.welfare ν x' := by
    intro x' hx'
    refine csSup_le (E.valueSet_nonempty hω μ) ?_
    rintro s ⟨x, hx, rfl⟩
    linarith [key x x' hx hx']
  have : E.v ν ≤ E.v (μ + ν) - E.v μ := by
    refine csSup_le (E.valueSet_nonempty hω ν) ?_
    rintro s ⟨x', hx', rfl⟩
    linarith [step x' hx']
  linarith

/-- **Exercise 18.E.1** (MWG, p. 671). `v : ℝ^H₊ → ℝ` is concave and homogeneous of degree
one, for `ψ_h` concave, nondecreasing and differentiable at some point of `ℝ^K₊`, and
`ω_h^y ≥ 0`. -/
theorem exercise_18_E_1 [Fintype H] (E : QLEconomy H K)
    (hconc : ∀ h, ConcaveOn ℝ (Set.Ici 0) (E.ψ h)) (hmono : ∀ h, MonotoneOn (E.ψ h) (Set.Ici 0))
    (hdiff : ∀ h, ∃ z, 0 ≤ z ∧ DifferentiableAt ℝ (E.ψ h) z) (hω : ∀ h, 0 ≤ (E.ω h).1) :
    ConcaveOn ℝ (Set.Ici 0) E.v ∧ ∀ r : ℝ, 0 ≤ r → ∀ μ, E.v (r • μ) = r * E.v μ := by
  obtain ⟨q, hq, c, hmaj⟩ := E.exists_majorant hconc hmono hdiff
  have hbdd : ∀ μ : H → ℝ, 0 ≤ μ → BddAbove (E.valueSet μ) := fun μ hμ =>
    E.bddAbove_of_majorant hμ hq c hmaj
  refine ⟨⟨convex_Ici 0, fun μ hμ ν hν a b ha hb _ => ?_⟩, fun r hr μ => E.v_smul hr μ⟩
  have hμ' : 0 ≤ μ := hμ
  have hν' : 0 ≤ ν := hν
  rw [smul_eq_mul, smul_eq_mul, ← E.v_smul ha, ← E.v_smul hb]
  exact E.v_superadditive hconc hω hbdd (smul_nonneg ha hμ') (smul_nonneg hb hν')

/-! ### Footnote 20: equal treatment is without loss -/

/-- **Footnote 20** (MWG, p. 670). A finite economy with consumers `i : ι` of types `τ i`: an
allocation `x` (not necessarily treating equals equally) is feasible if `y_i ≥ 0` and
`∑ᵢ xᵢ ≤ ∑ᵢ ω_{τ i}`. -/
def QLEconomy.IsFeasibleFinite {ι : Type*} [Fintype ι] (E : QLEconomy H K) (τ : ι → H)
    (x : ι → (Fin K → ℝ) × ℝ) : Prop :=
  (∀ i, 0 ≤ (x i).1) ∧ ∑ i, x i ≤ ∑ i, E.ω (τ i)

/-- **Footnote 20** (MWG, p. 670). The profile `I_h = #{i : τ i = h}` of a finite economy. -/
def qlTypeCount {ι : Type*} [Fintype ι] [DecidableEq H] (τ : ι → H) (h : H) : ℝ :=
  ((Finset.univ.filter fun i => τ i = h).card : ℝ)

/-- Summing over consumers is summing over types with multiplicities `I_h`. -/
theorem ql_sum_fiber {ι M : Type*} [Fintype ι] [Fintype H] [DecidableEq H] [AddCommGroup M]
    [Module ℝ M] (τ : ι → H) (f : H → M) :
    ∑ i, f (τ i) = ∑ h, qlTypeCount τ h • f h := by
  rw [← Finset.sum_fiberwise Finset.univ τ (fun i => f (τ i))]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Finset.sum_congr rfl fun i hi => by rw [(Finset.mem_filter.1 hi).2], Finset.sum_const,
    qlTypeCount, Nat.cast_smul_eq_nsmul]

/-- **Footnote 20** (MWG, p. 670). Because utilities are concave, the maximum is reached treating
consumers of the same type equally: replacing the bundles of the consumers of each type by their
average keeps feasibility (for the profile `I`) and does not lower the sum of utilities, so every
feasible allocation of the finite economy gives at most `v(I)`. -/
theorem footnote_18_20 {ι : Type*} [Fintype ι] [Fintype H] [DecidableEq H] (E : QLEconomy H K)
    (hconc : ∀ h, ConcaveOn ℝ (Set.Ici 0) (E.ψ h)) (τ : ι → H)
    (hbdd : BddAbove (E.valueSet (qlTypeCount τ))) {x : ι → (Fin K → ℝ) × ℝ}
    (hx : E.IsFeasibleFinite τ x) : ∑ i, E.u (τ i) (x i) ≤ E.v (qlTypeCount τ) := by
  set I := qlTypeCount τ with hI
  let F : H → Finset ι := fun h => Finset.univ.filter fun i => τ i = h
  let xb : H → (Fin K → ℝ) × ℝ := fun h => (I h)⁻¹ • ∑ i ∈ F h, x i
  have hcard : ∀ h, I h = ((F h).card : ℝ) := fun h => rfl
  have hsmul : ∀ h, I h • xb h = ∑ i ∈ F h, x i := by
    intro h
    by_cases h0 : I h = 0
    · have hF : F h = ∅ := by
        rw [hcard] at h0
        exact Finset.card_eq_zero.1 (by exact_mod_cast h0)
      simp [h0, hF]
    · simp only [xb, smul_smul, mul_inv_cancel₀ h0, one_smul]
  have hjensen : ∀ h, ∑ i ∈ F h, E.u h (x i) ≤ I h * E.u h (xb h) := by
    intro h
    by_cases h0 : I h = 0
    · have hF : F h = ∅ := by
        rw [hcard] at h0
        exact Finset.card_eq_zero.1 (by exact_mod_cast h0)
      simp [h0, hF]
    · have hpos : 0 < I h := lt_of_le_of_ne (by rw [hcard]; positivity) (Ne.symm h0)
      have hJ := (E.u_concaveOn (hconc h)).le_map_sum (t := F h) (w := fun _ => (I h)⁻¹)
        (p := x) (fun _ _ => inv_nonneg.2 hpos.le)
        (by rw [Finset.sum_const, nsmul_eq_mul, ← hcard, mul_inv_cancel₀ h0])
        (fun i _ => hx.1 i)
      simp only [smul_eq_mul, ← Finset.smul_sum, ← Finset.mul_sum] at hJ
      have := mul_le_mul_of_nonneg_left hJ hpos.le
      rwa [← mul_assoc, mul_inv_cancel₀ h0, one_mul] at this
  have hfeas : E.IsFeasible I xb := by
    refine ⟨fun h => ?_, ?_⟩
    · change 0 ≤ ((I h)⁻¹ • ∑ i ∈ F h, x i).1
      rw [Prod.smul_fst, Prod.fst_sum]
      exact smul_nonneg (inv_nonneg.2 (by rw [hcard]; positivity))
        (Finset.sum_nonneg fun i _ => hx.1 i)
    · have e1 : ∑ h, I h • xb h = ∑ i, x i := by
        simp only [hsmul]
        exact Finset.sum_fiberwise Finset.univ τ x
      rw [e1, hI, ← ql_sum_fiber τ E.ω]
      exact hx.2
  have hsum : ∑ i, E.u (τ i) (x i) = ∑ h, ∑ i ∈ F h, E.u h (x i) := by
    rw [← Finset.sum_fiberwise Finset.univ τ (fun i => E.u (τ i) (x i))]
    refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun i hi => ?_
    rw [(Finset.mem_filter.1 hi).2]
  have hle : ∑ i, E.u (τ i) (x i) ≤ E.welfare I xb := by
    rw [hsum]
    exact Finset.sum_le_sum fun h _ => hjensen h
  exact hle.trans (le_csSup hbdd ⟨xb, hfeas, rfl⟩)

/-- **Footnote 20** (MWG, p. 670). The supremum of the sum of utilities over all feasible
allocations of the finite economy (unequal treatment allowed) equals `v(I)` of (18.E.1). -/
theorem footnote_18_20_sSup {ι : Type*} [Fintype ι] [Fintype H] [DecidableEq H]
    (E : QLEconomy H K) (hconc : ∀ h, ConcaveOn ℝ (Set.Ici 0) (E.ψ h))
    (hω : ∀ h, 0 ≤ (E.ω h).1) (τ : ι → H) (hbdd : BddAbove (E.valueSet (qlTypeCount τ))) :
    sSup {s | ∃ x, E.IsFeasibleFinite τ x ∧ ∑ i, E.u (τ i) (x i) = s} =
      E.v (qlTypeCount τ) := by
  have hsub : E.valueSet (qlTypeCount τ) ⊆
      {s | ∃ x, E.IsFeasibleFinite τ x ∧ ∑ i, E.u (τ i) (x i) = s} := by
    rintro s ⟨x, hx, rfl⟩
    refine ⟨fun i => x (τ i), ⟨fun i => hx.1 (τ i), ?_⟩, ?_⟩
    · rw [ql_sum_fiber τ x, ql_sum_fiber τ E.ω]
      exact hx.2
    · rw [ql_sum_fiber τ (fun h => E.u h (x h))]
      rfl
  have hne := E.valueSet_nonempty hω (qlTypeCount τ)
  have hbdd' : BddAbove {s | ∃ x, E.IsFeasibleFinite τ x ∧ ∑ i, E.u (τ i) (x i) = s} := by
    refine ⟨E.v (qlTypeCount τ), ?_⟩
    rintro s ⟨x, hx, rfl⟩
    exact footnote_18_20 E hconc τ hbdd hx
  refine le_antisymm (csSup_le (hne.mono hsub) ?_) (csSup_le_csSup hbdd' hne hsub)
  rintro s ⟨x, hx, rfl⟩
  exact footnote_18_20 E hconc τ hbdd hx

/-! ### Euler's formula and the comparison lemma -/

/-- **Section M.B** (MWG, p. 671, Euler's formula). If `v` is homogeneous of degree one
(`v(tμ) = t v(μ)` for `t > 0`) and differentiable at `μ`, then `v(μ) = ∑_h μ_h ∂v(μ)/∂μ_h`:
differentiate `t ↦ v(tμ)` at `t = 1`. -/
theorem ql_euler [Fintype H] [DecidableEq H] {v : (H → ℝ) → ℝ} {D : (H → ℝ) →L[ℝ] ℝ}
    {μ : H → ℝ} (hv : HasFDerivAt v D μ) (hhom : ∀ t : ℝ, 0 < t → v (t • μ) = t * v μ) :
    v μ = ∑ h, μ h * D (Pi.single h 1) := by
  have h1 : HasDerivAt (fun t : ℝ => v (t • μ)) (D μ) 1 := by
    have hl : HasDerivAt (fun t : ℝ => t • μ) μ 1 := by
      simpa using (hasDerivAt_id (1 : ℝ)).smul_const μ
    have hv' : HasFDerivAt v D ((1 : ℝ) • μ) := by simpa using hv
    exact hv'.comp_hasDerivAt (1 : ℝ) hl
  have h2 : HasDerivAt (fun t : ℝ => v (t • μ)) (v μ) 1 := by
    have : HasDerivAt (fun t : ℝ => t * v μ) (v μ) 1 := by
      simpa using (hasDerivAt_id (1 : ℝ)).mul_const (v μ)
    refine this.congr_of_eventuallyEq ?_
    filter_upwards [lt_mem_nhds one_pos] with t ht using hhom t ht
  rw [h2.unique h1, ql_clm_apply_eq_sum]

/-- The comparison lemma behind (18.E.5): if `v ≤ g` on `ℝ^H₊` for the linear
`g(ν) = ∑ ν_k a_k`, with equality at `μ`, and `v` is differentiable at `μ` with `μ_h > 0`, then
`∂v(μ)/∂μ_h = a_h` (`g - v` has a local minimum along the `h`-th coordinate line). -/
theorem ql_partial_eq_of_le_linear [Fintype H] [DecidableEq H] {v : (H → ℝ) → ℝ}
    {D : (H → ℝ) →L[ℝ] ℝ} {μ : H → ℝ} (hv : HasFDerivAt v D μ) (hμ : 0 ≤ μ) (a : H → ℝ)
    (hle : ∀ ν : H → ℝ, 0 ≤ ν → v ν ≤ ∑ k, ν k * a k) (heq : v μ = ∑ k, μ k * a k) {h : H}
    (hμh : 0 < μ h) : D (Pi.single h 1) = a h := by
  set e : H → ℝ := Pi.single h 1 with he
  have hlin : ∀ t : ℝ, ∑ k, (μ + t • e) k * a k = ∑ k, μ k * a k + t * a h := by
    intro t
    simp [he, add_mul, Finset.sum_add_distrib, Pi.single_apply]
  have hφ : HasDerivAt (fun t : ℝ => (∑ k, μ k * a k + t * a h) - v (μ + t • e))
      (a h - D e) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => ∑ k, μ k * a k + t * a h) (a h) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (a h)).const_add (∑ k, μ k * a k)
    exact h1.sub (ql_hasDerivAt_line hv e)
  have hmin : IsLocalMin (fun t : ℝ => (∑ k, μ k * a k + t * a h) - v (μ + t • e)) 0 := by
    filter_upwards [lt_mem_nhds (show -μ h < 0 by linarith)] with t ht
    have hnn : 0 ≤ μ + t • e := by
      intro k
      by_cases hk : k = h
      · subst hk
        simp [he]
        linarith
      · simpa [he, hk] using hμ k
    have := hle _ hnn
    rw [hlin] at this
    simp only [zero_mul, add_zero, zero_smul]
    linarith
  linarith [hmin.hasDerivAt_eq_zero hφ]

/-! ### First-order conditions for (18.E.2) -/

/-- Along a line `t ↦ y + t d` from a strictly positive `y`, nonnegativity holds near `t = 0`. -/
theorem ql_eventually_nonneg_line {ι : Type*} [Finite ι] {y : ι → Fin K → ℝ}
    (hy : ∀ h l, 0 < y h l) (d : ι → Fin K → ℝ) :
    ∀ᶠ t in 𝓝 (0 : ℝ), ∀ h, 0 ≤ y h + t • d h := by
  rw [Filter.eventually_all]
  intro h
  have : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ l, 0 < y h l + t * d h l := by
    rw [Filter.eventually_all]
    intro l
    have hc : Continuous fun t : ℝ => y h l + t * d h l := by fun_prop
    exact (hc.tendsto 0).eventually (lt_mem_nhds (by simpa using hy h l))
  filter_upwards [this] with t ht l
  simpa using (ht l).le

/-- Aggregate of a perturbation of the non-numeraire goods. -/
theorem ql_sum_perturb [Fintype H] (μ : H → ℝ) (x : H → (Fin K → ℝ) × ℝ)
    (d : H → Fin K → ℝ) (t : ℝ) :
    ∑ h, μ h • (x h + (t • d h, (0 : ℝ))) = ∑ h, μ h • x h + (t • ∑ h, μ h • d h, 0) := by
  simp only [smul_add, Finset.sum_add_distrib]
  congr 1
  refine Prod.ext ?_ ?_
  · simp [Prod.fst_sum, Finset.smul_sum, smul_smul, mul_comm]
  · simp [Prod.snd_sum]

/-- **(18.E.2)** first-order conditions (MWG, p. 671). If `x` solves (18.E.2) for `μ`, each
`ψ_h` is differentiable at `y_h` with derivative `Dψ_h`, and the perturbed allocations
`x_h + (t d_h, 0)` are feasible for `t` near `0`, then `∑_h μ_h Dψ_h(d_h) = 0`. -/
theorem QLEconomy.foc_of_optimal [Fintype H] (E : QLEconomy H K) {μ : H → ℝ}
    {x : H → (Fin K → ℝ) × ℝ} (hopt : E.IsOptimal μ x) {Dψ : H → (Fin K → ℝ) →L[ℝ] ℝ}
    (hDψ : ∀ h, HasFDerivAt (E.ψ h) (Dψ h) (x h).1) (d : H → Fin K → ℝ)
    (hfeas : ∀ᶠ t in 𝓝 (0 : ℝ), E.IsFeasible μ (fun h => x h + (t • d h, 0))) :
    ∑ h, μ h * Dψ h (d h) = 0 := by
  let φ : ℝ → ℝ := fun t => ∑ h, μ h * (E.ψ h ((x h).1 + t • d h) + (x h).2)
  have hφeq : ∀ t, E.welfare μ (fun h => x h + (t • d h, 0)) = φ t := by
    intro t
    simp [φ, QLEconomy.welfare, QLEconomy.u]
  have hφ0 : φ 0 = E.welfare μ x := by
    simp [φ, QLEconomy.welfare, QLEconomy.u]
  have hder : HasDerivAt φ (∑ h, μ h * Dψ h (d h)) 0 :=
    HasDerivAt.fun_sum (u := Finset.univ) fun h _ =>
      ((ql_hasDerivAt_line (hDψ h) (d h)).add_const ((x h).2)).const_mul (μ h)
  have hmax : IsLocalMax φ 0 := by
    filter_upwards [hfeas] with t ht
    rw [← hφeq, hφ0]
    exact hopt.2 _ ht
  exact hmax.hasDerivAt_eq_zero hder

/-- **(18.E.2)** (MWG, p. 671). `x` solves (18.E.2) iff it is feasible and attains `v(μ)`
(given a bounded value set). -/
theorem QLEconomy.isOptimal_iff [Fintype H] (E : QLEconomy H K) {μ : H → ℝ}
    {x : H → (Fin K → ℝ) × ℝ} (hbdd : BddAbove (E.valueSet μ)) :
    E.IsOptimal μ x ↔ E.IsFeasible μ x ∧ E.v μ = E.welfare μ x := by
  constructor
  · intro hopt
    refine ⟨hopt.1, ?_⟩
    refine le_antisymm (csSup_le ⟨_, x, hopt.1, rfl⟩ ?_) (le_csSup hbdd ⟨x, hopt.1, rfl⟩)
    rintro s ⟨x', hx', rfl⟩
    exact hopt.2 x' hx'
  · rintro ⟨hx, hv⟩
    exact ⟨hx, fun x' hx' => hv ▸ le_csSup hbdd ⟨x', hx', rfl⟩⟩

/-! ### Walrasian equilibrium of the continuum economy -/

/-- With `ψ_h` nondecreasing on `ℝ^K₊`, Walrasian prices are nonnegative (`q_l < 0` would let a
consumer buy one more unit of good `l` and keep the money). -/
theorem QLEconomy.walras_price_nonneg [Fintype H] (E : QLEconomy H K)
    (hmono : ∀ h, MonotoneOn (E.ψ h) (Set.Ici 0)) {μ : H → ℝ} {q : Fin K → ℝ}
    {x : H → (Fin K → ℝ) × ℝ} (hW : E.IsWalrasEqm μ q x) (h : H) : 0 ≤ q := by
  intro l
  by_contra hneg
  have hql : q l < 0 := lt_of_not_ge hneg
  set x' : (Fin K → ℝ) × ℝ := ((x h).1 + Pi.single l 1, (x h).2 - q l)
  have hy : (x h).1 ≤ x'.1 := by
    intro k
    have : 0 ≤ (Pi.single l (1 : ℝ) : Fin K → ℝ) k := by
      rcases eq_or_ne k l with rfl | hk
      · simp
      · simp [hk]
    simpa [x'] using this
  have hx'0 : 0 ≤ x'.1 := (hW.1.1 h).trans hy
  have hp : qlPrice q x' = qlPrice q (x h) := by
    simp only [qlPrice, x', dotProduct_add, dotProduct_single, mul_one]
    ring
  have hle := (hW.2 h).2 x' hx'0 (hp ▸ (hW.2 h).1)
  have hm := hmono h (Set.mem_Ici.2 (hW.1.1 h)) (Set.mem_Ici.2 hx'0) hy
  simp only [QLEconomy.u, x'] at hle hm
  linarith

/-- In a Walrasian equilibrium every budget binds: `p·x*_h = p·ω_h` (money is desirable). -/
theorem QLEconomy.walras_budget_eq [Fintype H] (E : QLEconomy H K) {μ : H → ℝ}
    {q : Fin K → ℝ} {x : H → (Fin K → ℝ) × ℝ} (hW : E.IsWalrasEqm μ q x) (h : H) :
    qlPrice q (x h) = qlPrice q (E.ω h) := by
  refine le_antisymm (hW.2 h).1 (not_lt.1 fun hlt => ?_)
  set x' : (Fin K → ℝ) × ℝ := ((x h).1, (x h).2 + (qlPrice q (E.ω h) - qlPrice q (x h)))
  have hp : qlPrice q x' = qlPrice q (E.ω h) := by
    simp only [qlPrice, x'] at hlt ⊢
    ring
  have hle := (hW.2 h).2 x' (hW.1.1 h) hp.le
  simp only [QLEconomy.u, x'] at hle
  linarith

/-- By quasilinearity, `x*_h` maximizes `u_h(x) - p·x` over `{y ≥ 0}`:
`u_h(x) ≤ u_h(x*_h) - p·x*_h + p·x`. -/
theorem QLEconomy.walras_majorant [Fintype H] (E : QLEconomy H K) {μ : H → ℝ}
    {q : Fin K → ℝ} {x : H → (Fin K → ℝ) × ℝ} (hW : E.IsWalrasEqm μ q x) (h : H)
    (x' : (Fin K → ℝ) × ℝ) (hx' : 0 ≤ x'.1) :
    E.u h x' ≤ (E.u h (x h) - qlPrice q (x h)) + qlPrice q x' := by
  set x'' : (Fin K → ℝ) × ℝ := (x'.1, x'.2 + (qlPrice q (x h) - qlPrice q x'))
  have hp : qlPrice q x'' = qlPrice q (x h) := by
    simp only [qlPrice, x'']
    ring
  have hle := (hW.2 h).2 x'' hx' (hp ▸ (hW.2 h).1)
  simp only [QLEconomy.u, x''] at hle ⊢
  linarith

/-- The linear upper bound `v(ν) ≤ ∑ ν_k (c_k + p·ω_k)` on `ℝ^H₊` from an affine majorant. -/
theorem QLEconomy.v_le_linear [Fintype H] (E : QLEconomy H K) (hω : ∀ h, 0 ≤ (E.ω h).1)
    {q : Fin K → ℝ} (hq : 0 ≤ q) (c : H → ℝ)
    (hmaj : ∀ h x, 0 ≤ x.1 → E.u h x ≤ c h + qlPrice q x) (ν : H → ℝ) (hν : 0 ≤ ν) :
    E.v ν ≤ ∑ k, ν k * (c k + qlPrice q (E.ω k)) := by
  have := E.v_le_of_majorant hω hν hq c hmaj
  rw [qlPrice_sum, ← Finset.sum_add_distrib] at this
  simpa only [mul_add] using this

/-- **(18.E.5)** at a Walrasian equilibrium, and the "Walrasian ⇒ marginal product" half of
**Proposition 18.E.1** (MWG, pp. 671-672). Let `ψ_h` be nondecreasing on `ℝ^K₊`, `ω_h^y ≥ 0`,
`μ ≫ 0`, `(q, x*)` a Walrasian equilibrium and `v` differentiable at `μ`. Then
`∂v(μ)/∂μ_h = u_h(x*_h)`.

Proof (in place of the envelope theorem): each type's `x*_h` maximizes `u_h(x) - p·x`, so
`v(ν) ≤ ∑ ν_h [u_h(x*_h) + p·(ω_h - x*_h)]` for every `ν ≥ 0`; budgets bind, so the right side
equals `∑ μ_h u_h(x*_h) ≤ v(μ)` at `ν = μ`; a differentiable function lying below a linear one,
with contact at the interior point `μ`, has the linear function's partial derivatives. -/
theorem QLEconomy.partial_v_of_walras [Fintype H] [DecidableEq H] (E : QLEconomy H K)
    (hmono : ∀ h, MonotoneOn (E.ψ h) (Set.Ici 0)) (hω : ∀ h, 0 ≤ (E.ω h).1) {μ : H → ℝ}
    (hμ : ∀ h, 0 < μ h) {q : Fin K → ℝ} {x : H → (Fin K → ℝ) × ℝ} (hW : E.IsWalrasEqm μ q x)
    {D : (H → ℝ) →L[ℝ] ℝ} (hv : HasFDerivAt E.v D μ) (h : H) :
    D (Pi.single h 1) = E.u h (x h) := by
  have hq := E.walras_price_nonneg hmono hW h
  have hμ0 : 0 ≤ μ := fun k => (hμ k).le
  set c : H → ℝ := fun k => E.u k (x k) - qlPrice q (x k)
  have hmaj : ∀ k x', 0 ≤ x'.1 → E.u k x' ≤ c k + qlPrice q x' := fun k x' hx' =>
    E.walras_majorant hW k x' hx'
  have ha : ∀ k, c k + qlPrice q (E.ω k) = E.u k (x k) := fun k => by
    simp only [c, E.walras_budget_eq hW k]; ring
  have hle := E.v_le_linear hω hq c hmaj
  have heq : E.v μ = ∑ k, μ k * (c k + qlPrice q (E.ω k)) := by
    refine le_antisymm (hle μ hμ0) ?_
    have hbdd := E.bddAbove_of_majorant hμ0 hq c hmaj
    simp only [ha]
    exact le_csSup hbdd ⟨x, hW.1, rfl⟩
  rw [ql_partial_eq_of_le_linear hv hμ0 _ hle heq (hμ h), ha]

/-- **Proposition 18.E.1** (MWG, p. 671), "if" direction: a Walrasian equilibrium allocation of
the continuum population `μ ≫ 0` is a marginal product allocation (`ψ_h` nondecreasing,
`ω_h^y ≥ 0`, `v` differentiable at `μ`; neither concavity, differentiability of `ψ_h` nor
interiority of `x*` is needed in this direction). -/
theorem proposition_18_E_1_of_walras [Fintype H] [DecidableEq H] (E : QLEconomy H K)
    (hmono : ∀ h, MonotoneOn (E.ψ h) (Set.Ici 0)) (hω : ∀ h, 0 ≤ (E.ω h).1) {μ : H → ℝ}
    (hμ : ∀ h, 0 < μ h) {q : Fin K → ℝ} {x : H → (Fin K → ℝ) × ℝ} (hW : E.IsWalrasEqm μ q x)
    (hv : DifferentiableAt ℝ E.v μ) : E.IsMarginalProduct μ x :=
  ⟨hW.1, fun h => (E.partial_v_of_walras hmono hω hμ hW hv.hasFDerivAt h).symm⟩

/-- **(18.E.4)** (MWG, p. 671), the supporting prices of a solution of (18.E.2). Let `ψ_h` be
concave and nondecreasing on `ℝ^K₊`, `μ ≫ 0`, and let `x` solve (18.E.2) with `y_h ≫ 0` and `ψ_h`
differentiable at `y_h` (derivative `Dψ_h`). Then there is `q ≥ 0` with
`q_l = ∂ψ_h(y_h)/∂y_l` for all `h, l` (18.E.4); `x_h` maximizes `u_h(x) - p·x` over `{y ≥ 0}`
(concavity: the tangent plane majorises `ψ_h`); and `∑ μ_h p·(ω_h - x_h) = 0` (no surplus has
positive value). The multipliers are obtained from first-order conditions for transfers of a
good between two types and for disposal of a surplus, not from Section M.K. -/
theorem QLEconomy.supporting_prices [Fintype H] (E : QLEconomy H K)
    (hconc : ∀ h, ConcaveOn ℝ (Set.Ici 0) (E.ψ h)) (hmono : ∀ h, MonotoneOn (E.ψ h) (Set.Ici 0))
    {μ : H → ℝ} (hμ : ∀ h, 0 < μ h) {x : H → (Fin K → ℝ) × ℝ} (hint : ∀ h l, 0 < (x h).1 l)
    (hopt : E.IsOptimal μ x) {Dψ : H → (Fin K → ℝ) →L[ℝ] ℝ}
    (hDψ : ∀ h, HasFDerivAt (E.ψ h) (Dψ h) (x h).1) :
    ∃ q : Fin K → ℝ, (∀ h l, Dψ h (Pi.single l 1) = q l) ∧ 0 ≤ q ∧
      (∀ h x', 0 ≤ x'.1 → E.u h x' ≤ (E.u h (x h) - qlPrice q (x h)) + qlPrice q x') ∧
      ∑ h, μ h * qlPrice q (E.ω h - x h) = 0 := by
  classical
  rcases isEmpty_or_nonempty H with hH | hH
  · exact ⟨0, fun h => isEmptyElim h, le_rfl, fun h => isEmptyElim h, by simp⟩
  obtain ⟨h0⟩ := hH
  set q : Fin K → ℝ := fun l => Dψ h0 (Pi.single l 1) with hqdef
  set e : Fin K → Fin K → ℝ := fun l => Pi.single l 1
  -- (18.E.4): transfers between `h` and `h0`
  have hgrad : ∀ h l, Dψ h (Pi.single l 1) = q l := by
    intro h l
    let d : H → Fin K → ℝ := fun j =>
      (if j = h then (μ h)⁻¹ • e l else 0) - (if j = h0 then (μ h0)⁻¹ • e l else 0)
    have hsumd : ∑ j, μ j • d j = 0 := by
      simp only [d, smul_sub, Finset.sum_sub_distrib, smul_ite, smul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, ↓reduceIte, smul_smul, mul_inv_cancel₀ (hμ _).ne', one_smul, sub_self]
    have hfeas : ∀ᶠ t in 𝓝 (0 : ℝ), E.IsFeasible μ (fun j => x j + (t • d j, 0)) := by
      filter_upwards [ql_eventually_nonneg_line hint d] with t ht
      refine ⟨fun j => by simpa using ht j, ?_⟩
      rw [ql_sum_perturb, hsumd, smul_zero, Prod.mk_zero_zero, add_zero]
      exact hopt.1.2
    have hfoc := E.foc_of_optimal hopt hDψ d hfeas
    have hterm : ∀ j, μ j * Dψ j (d j) = (if j = h then Dψ h (e l) else 0) -
        (if j = h0 then Dψ h0 (e l) else 0) := by
      intro j
      by_cases hjh : j = h <;> by_cases hj0 : j = h0
      · subst hjh; subst hj0; simp [d]
      · subst hjh; simp [d, hj0, map_smul, smul_eq_mul, ← mul_assoc,
          mul_inv_cancel₀ (hμ j).ne']
      · subst hj0; simp [d, hjh, map_smul, smul_eq_mul, ← mul_assoc,
          mul_inv_cancel₀ (hμ j).ne']
      · simp [d, hjh, hj0]
    simp only [hterm, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ,
      ↓reduceIte] at hfoc
    simp only [hqdef]
    exact sub_eq_zero.1 hfoc
  have hq : 0 ≤ q := fun l => ql_fderiv_single_nonneg (hmono h0) (hopt.1.1 h0) (hDψ h0) l
  have hDq : ∀ h z, Dψ h z = q ⬝ᵥ z := by
    intro h z
    rw [ql_clm_apply_eq_sum, dotProduct]
    exact Finset.sum_congr rfl fun l _ => by rw [hgrad, mul_comm]
  have hmaj : ∀ h x', 0 ≤ x'.1 → E.u h x' ≤ (E.u h (x h) - qlPrice q (x h)) + qlPrice q x' := by
    intro h x' hx'
    have ht := MWG.WelfareTheorems.concaveOn_le_tangent (hconc h)
      (Set.mem_Ici.2 (hopt.1.1 h)) (Set.mem_Ici.2 hx') (hDψ h)
    rw [hDq, dotProduct_sub] at ht
    simp only [QLEconomy.u, qlPrice]
    linarith
  -- the surplus `s = ∑ μ ω - ∑ μ x ≥ 0` has zero value
  set S : (Fin K → ℝ) × ℝ := ∑ j, μ j • E.ω j - ∑ j, μ j • x j with hS
  have hgood : ∀ l, q l * S.1 l = 0 := by
    intro l
    have hS1 : 0 ≤ S.1 l := by
      simp only [hS, Prod.fst_sub, Pi.sub_apply, sub_nonneg]
      exact hopt.1.2.1 l
    rcases hS1.eq_or_lt with h0l | hpos
    · rw [← h0l, mul_zero]
    let d : H → Fin K → ℝ := fun j => if j = h0 then (μ h0)⁻¹ • e l else 0
    have hsumd : ∑ j, μ j • d j = e l := by
      simp only [d, smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
        smul_smul, mul_inv_cancel₀ (hμ h0).ne', one_smul]
    have hfeas : ∀ᶠ t in 𝓝 (0 : ℝ), E.IsFeasible μ (fun j => x j + (t • d j, 0)) := by
      filter_upwards [ql_eventually_nonneg_line hint d, Iio_mem_nhds hpos] with t ht ht'
      refine ⟨fun j => by simpa using ht j, ?_⟩
      rw [ql_sum_perturb, hsumd]
      refine ⟨fun k => ?_, ?_⟩
      · have hk := hopt.1.2.1 k
        rcases eq_or_ne k l with rfl | hkl
        · have : t < (∑ j, μ j • E.ω j).1 k - (∑ j, μ j • x j).1 k := by
            simpa [hS] using ht'
          simp [e]
          linarith
        · simpa [e, hkl] using hk
      · simpa using hopt.1.2.2
    have hfoc := E.foc_of_optimal hopt hDψ d hfeas
    have hterm : ∀ j, μ j * Dψ j (d j) = if j = h0 then q l else 0 := by
      intro j
      by_cases hj0 : j = h0
      · subst hj0
        simp [d, hqdef, e, map_smul, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (hμ j).ne']
      · simp [d, hj0]
    simp only [hterm, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at hfoc
    rw [hfoc, zero_mul]
  have hmoney : S.2 = 0 := by
    refine le_antisymm (not_lt.1 fun hpos => ?_) (sub_nonneg.2 hopt.1.2.2)
    let x' : H → (Fin K → ℝ) × ℝ := fun j => x j + (0, if j = h0 then S.2 / μ h0 else 0)
    have hfeas : E.IsFeasible μ x' := by
      refine ⟨fun j => by simpa [x'] using hopt.1.1 j, ?_⟩
      have hagg : ∑ j, μ j • x' j = ∑ j, μ j • x j + (0, S.2) := by
        simp only [x', smul_add, Finset.sum_add_distrib]
        congr 1
        refine Prod.ext ?_ ?_
        · simp [Prod.fst_sum]
        · simp [Prod.snd_sum, mul_div_cancel₀ _ (hμ h0).ne']
      rw [hagg]
      refine ⟨by simpa using hopt.1.2.1, ?_⟩
      simp [hS]
    have hw : E.welfare μ x' = E.welfare μ x + S.2 := by
      simp only [QLEconomy.welfare, QLEconomy.u, x', Prod.fst_add, Prod.snd_add, add_zero]
      simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, ↓reduceIte, mul_div_cancel₀ _ (hμ h0).ne']
      ring
    linarith [hopt.2 x' hfeas]
  refine ⟨q, hgrad, hq, hmaj, ?_⟩
  have : ∑ h, μ h * qlPrice q (E.ω h - x h) = qlPrice q S := by
    rw [← qlPrice_sum, hS]
    simp only [smul_sub, Finset.sum_sub_distrib]
  rw [this, qlPrice, hmoney, add_zero, dotProduct]
  exact Finset.sum_eq_zero fun l _ => hgood l

/-- **Exercise 18.E.2** (MWG, p. 685): expression **(18.E.5)** (p. 672). If `x*` solves (18.E.2)
for `μ ≫ 0`, with `y*_h ≫ 0`, `ψ_h` concave and nondecreasing on `ℝ^K₊` and differentiable at
`y*_h`, `ω_h^y ≥ 0`, and `v` is differentiable at `μ`, then with the prices `p = (q, 1)` of
(18.E.4), `∂v(μ)/∂μ_h = u_h(x*_h) + p·(ω_h - x*_h)`. Derived from `v(ν) ≤ ∑ ν_h [u_h(x*_h) +
p·(ω_h - x*_h)]` on `ℝ^H₊` with equality at `μ` (`ql_partial_eq_of_le_linear`) instead of the
envelope theorem of Section M.L. -/
theorem exercise_18_E_2 [Fintype H] [DecidableEq H] (E : QLEconomy H K)
    (hconc : ∀ h, ConcaveOn ℝ (Set.Ici 0) (E.ψ h)) (hmono : ∀ h, MonotoneOn (E.ψ h) (Set.Ici 0))
    (hω : ∀ h, 0 ≤ (E.ω h).1) {μ : H → ℝ} (hμ : ∀ h, 0 < μ h) {x : H → (Fin K → ℝ) × ℝ}
    (hint : ∀ h l, 0 < (x h).1 l) (hopt : E.IsOptimal μ x) {Dψ : H → (Fin K → ℝ) →L[ℝ] ℝ}
    (hDψ : ∀ h, HasFDerivAt (E.ψ h) (Dψ h) (x h).1) {D : (H → ℝ) →L[ℝ] ℝ}
    (hv : HasFDerivAt E.v D μ) :
    ∃ q : Fin K → ℝ, (∀ h l, Dψ h (Pi.single l 1) = q l) ∧
      ∀ h, D (Pi.single h 1) = E.u h (x h) + qlPrice q (E.ω h - x h) := by
  obtain ⟨q, hgrad, hq, hmaj, hzero⟩ := E.supporting_prices hconc hmono hμ hint hopt hDψ
  refine ⟨q, hgrad, fun h => ?_⟩
  have hμ0 : 0 ≤ μ := fun k => (hμ k).le
  set c : H → ℝ := fun k => E.u k (x k) - qlPrice q (x k)
  have ha : ∀ k, c k + qlPrice q (E.ω k) = E.u k (x k) + qlPrice q (E.ω k - x k) := fun k => by
    simp only [c, qlPrice_sub]; ring
  have hle := E.v_le_linear hω hq c hmaj
  have heq : E.v μ = ∑ k, μ k * (c k + qlPrice q (E.ω k)) := by
    have hbdd := E.bddAbove_of_majorant hμ0 hq c hmaj
    rw [((E.isOptimal_iff hbdd).1 hopt).2]
    simp only [ha, mul_add, Finset.sum_add_distrib, hzero, add_zero]
    rfl
  rw [ql_partial_eq_of_le_linear hv hμ0 _ hle heq (hμ h), ha]

/-- A solution `x*` of (18.E.2) satisfying (18.E.3) is a Walrasian equilibrium allocation: by
(18.E.5) every `p·(ω_h - x*_h) = 0`, so budgets are met, and the majorant of
`QLEconomy.supporting_prices` makes `x*_h` each type's demand. -/
theorem QLEconomy.walras_of_optimal_of_partial [Fintype H] [DecidableEq H] (E : QLEconomy H K)
    (hconc : ∀ h, ConcaveOn ℝ (Set.Ici 0) (E.ψ h)) (hmono : ∀ h, MonotoneOn (E.ψ h) (Set.Ici 0))
    (hω : ∀ h, 0 ≤ (E.ω h).1) {μ : H → ℝ} (hμ : ∀ h, 0 < μ h) {x : H → (Fin K → ℝ) × ℝ}
    (hint : ∀ h l, 0 < (x h).1 l) (hopt : E.IsOptimal μ x) {Dψ : H → (Fin K → ℝ) →L[ℝ] ℝ}
    (hDψ : ∀ h, HasFDerivAt (E.ψ h) (Dψ h) (x h).1) {D : (H → ℝ) →L[ℝ] ℝ}
    (hv : HasFDerivAt E.v D μ) (hmp : ∀ h, E.u h (x h) = D (Pi.single h 1)) :
    ∃ q, E.IsWalrasEqm μ q x := by
  obtain ⟨q, hgrad, hq, hmaj, hzero⟩ := E.supporting_prices hconc hmono hμ hint hopt hDψ
  -- (18.E.5) for these prices
  have h185 : ∀ h, D (Pi.single h 1) = E.u h (x h) + qlPrice q (E.ω h - x h) := by
    intro h
    obtain ⟨q', hgrad', h5⟩ := exercise_18_E_2 E hconc hmono hω hμ hint hopt hDψ hv
    have hqq : q' = q := by
      ext l; rw [← hgrad' h l, hgrad h l]
    simpa [hqq] using h5 h
  have hbal : ∀ h, qlPrice q (x h) = qlPrice q (E.ω h) := by
    intro h
    have := h185 h
    rw [← hmp h, qlPrice_sub] at this
    linarith
  refine ⟨q, hopt.1, fun h => ⟨(hbal h).le, fun x' hx' hb => ?_⟩⟩
  have := hmaj h x' hx'
  linarith [hbal h]

/-- **Proposition 18.E.1** (MWG, p. 671). For a continuum population `μ ≫ 0`, a feasible
allocation `x*` with `y*_h ≫ 0` is a marginal product allocation iff it is a Walrasian
equilibrium allocation. Hypotheses: `ψ_h` concave and nondecreasing on `ℝ^K₊` and differentiable
at `y*_h`, `ω_h^y ≥ 0`, `v` differentiable at `μ` (footnote 21). The book's `x* ≫ 0` is used
only through `y* ≫ 0`; strict concavity and strict monotonicity of `ψ_h` are not needed.
"Only if": Euler's formula gives `v(μ) = ∑ μ_h ∂v/∂μ_h = ∑ μ_h u_h(x*_h)`, so `x*` solves
(18.E.2); then (18.E.4)-(18.E.5). "If": `proposition_18_E_1_of_walras`. -/
theorem proposition_18_E_1 [Fintype H] [DecidableEq H] (E : QLEconomy H K)
    (hconc : ∀ h, ConcaveOn ℝ (Set.Ici 0) (E.ψ h)) (hmono : ∀ h, MonotoneOn (E.ψ h) (Set.Ici 0))
    (hω : ∀ h, 0 ≤ (E.ω h).1) {μ : H → ℝ} (hμ : ∀ h, 0 < μ h) {x : H → (Fin K → ℝ) × ℝ}
    (hfeas : E.IsFeasible μ x) (hint : ∀ h l, 0 < (x h).1 l)
    (hdψ : ∀ h, DifferentiableAt ℝ (E.ψ h) (x h).1) (hv : DifferentiableAt ℝ E.v μ) :
    E.IsMarginalProduct μ x ↔ ∃ q, E.IsWalrasEqm μ q x := by
  constructor
  · intro hmp
    have hD := hv.hasFDerivAt
    have hDψ : ∀ h, HasFDerivAt (E.ψ h) (fderiv ℝ (E.ψ h) (x h).1) (x h).1 :=
      fun h => (hdψ h).hasFDerivAt
    -- Euler: `v(μ) = ∑ μ_h u_h(x*_h)`, so `x*` solves (18.E.2)
    obtain ⟨q, hq, c, hmaj⟩ := E.exists_majorant hconc hmono
      fun h => ⟨(x h).1, hfeas.1 h, hdψ h⟩
    have hbdd := E.bddAbove_of_majorant (fun k => (hμ k).le) hq c hmaj
    have heul := ql_euler hD fun t ht => E.v_smul ht.le μ
    have hopt : E.IsOptimal μ x := by
      refine (E.isOptimal_iff hbdd).2 ⟨hfeas, ?_⟩
      rw [heul, QLEconomy.welfare]
      exact Finset.sum_congr rfl fun h _ => by rw [hmp.2 h]
    exact E.walras_of_optimal_of_partial hconc hmono hω hμ hint hopt hDψ hD hmp.2
  · rintro ⟨q, hW⟩
    exact proposition_18_E_1_of_walras E hmono hω hμ hW hv

/-- Near a strictly positive population, populations are nonnegative. -/
theorem ql_eventually_nonneg_of_pos [Finite H] {μ : H → ℝ} (hμ : ∀ h, 0 < μ h) :
    ∀ᶠ ν in 𝓝 μ, 0 ≤ ν := by
  have : ∀ᶠ ν in 𝓝 μ, ∀ h, 0 < ν h := Filter.eventually_all.2 fun h =>
    ((continuous_apply h).tendsto μ).eventually (lt_mem_nhds (hμ h))
  filter_upwards [this] with ν hν h using (hν h).le

/-! ### Finite economies (p. 672) -/

/-- **Section 18.E** (MWG, p. 672). The marginal contribution of a type-`h` consumer in the
finite economy `I`: `Δ_h v(I) = v(I) - v(I - e_h)`. -/
noncomputable def QLEconomy.deltaV [Fintype H] [DecidableEq H] (E : QLEconomy H K)
    (I : H → ℝ) (h : H) : ℝ :=
  E.v I - E.v (I - Pi.single h 1)

/-- **Section 18.E** (MWG, p. 672). By concavity of `v`, `Δ_h v(I) ≥ ∂v(I)/∂μ_h` (for `I ≥ e_h`
and `v` differentiable at `I`). -/
theorem claim_18_E_deltaV_ge_partial [Fintype H] [DecidableEq H] (E : QLEconomy H K)
    (hconc : ConcaveOn ℝ (Set.Ici 0) E.v) {I : H → ℝ} {h : H} (hI : 0 ≤ I - Pi.single h 1)
    {D : (H → ℝ) →L[ℝ] ℝ} (hv : HasFDerivAt E.v D I) : D (Pi.single h 1) ≤ E.deltaV I h := by
  have hI0 : 0 ≤ I := by
    have : I = (I - Pi.single h 1) + Pi.single h 1 := by abel
    rw [this]
    exact add_nonneg hI (Pi.single_nonneg.2 zero_le_one)
  have ht := MWG.WelfareTheorems.concaveOn_le_tangent hconc (Set.mem_Ici.2 hI0)
    (Set.mem_Ici.2 hI) hv
  rw [sub_sub_cancel_left, map_neg] at ht
  unfold QLEconomy.deltaV
  linarith

/-- **Section 18.E** (MWG, p. 672). With Euler's formula, `∑_h I_h Δ_h v(I) ≥ v(I)` (for a
profile with `I_h ≥ 1`, `v` concave on `ℝ^H₊` and differentiable at `I`). -/
theorem claim_18_E_sum_deltaV_ge [Fintype H] [DecidableEq H] (E : QLEconomy H K)
    (hconc : ConcaveOn ℝ (Set.Ici 0) E.v) {I : H → ℝ} (hI : ∀ h, 0 ≤ I - Pi.single h 1)
    {D : (H → ℝ) →L[ℝ] ℝ} (hv : HasFDerivAt E.v D I) :
    E.v I ≤ ∑ h, I h * E.deltaV I h := by
  rw [ql_euler hv fun t ht => E.v_smul ht.le I]
  refine Finset.sum_le_sum fun h _ => ?_
  have hIh : 0 ≤ I h := by
    have := hI h h
    simp only [Pi.sub_apply, Pi.single_eq_same, Pi.zero_apply] at this
    linarith
  exact mul_le_mul_of_nonneg_left (claim_18_E_deltaV_ge_partial E hconc (hI h) hv) hIh

/-- **Section 18.E** (MWG, p. 672). "It is impossible to give each consumer the full extent of
her marginal contribution while maintaining feasibility": if `∑ I_h Δ_h v(I) > v(I)`, no
feasible equal-treatment allocation gives every type `h` the utility `Δ_h v(I)`. -/
theorem claim_18_E_no_full_marginal [Fintype H] [DecidableEq H] (E : QLEconomy H K)
    {I : H → ℝ} (hI : 0 ≤ I) (hbdd : BddAbove (E.valueSet I))
    (hgt : E.v I < ∑ h, I h * E.deltaV I h) :
    ¬ ∃ x, E.IsFeasible I x ∧ ∀ h, E.deltaV I h ≤ E.u h (x h) := by
  rintro ⟨x, hx, hge⟩
  have h1 : ∑ h, I h * E.deltaV I h ≤ E.welfare I x :=
    Finset.sum_le_sum fun h _ => mul_le_mul_of_nonneg_left (hge h) (hI h)
  have h2 : E.welfare I x ≤ E.v I := le_csSup hbdd ⟨x, hx, rfl⟩
  linarith

/-- **Section 18.E** (MWG, p. 672), the same for the finite economy with unequal treatment
allowed (via footnote 20): if `∑ I_h Δ_h v(I) > v(I)`, no feasible allocation of the finite
economy gives every consumer `i` the utility `Δ_{τ i} v(I)`. -/
theorem claim_18_E_no_full_marginal_finite {ι : Type*} [Fintype ι] [Fintype H] [DecidableEq H]
    (E : QLEconomy H K) (hconc : ∀ h, ConcaveOn ℝ (Set.Ici 0) (E.ψ h)) (τ : ι → H)
    (hbdd : BddAbove (E.valueSet (qlTypeCount τ)))
    (hgt : E.v (qlTypeCount τ) < ∑ h, qlTypeCount τ h * E.deltaV (qlTypeCount τ) h) :
    ¬ ∃ x, E.IsFeasibleFinite τ x ∧
      ∀ i, E.deltaV (qlTypeCount τ) (τ i) ≤ E.u (τ i) (x i) := by
  rintro ⟨x, hx, hge⟩
  have h1 : ∑ h, qlTypeCount τ h * E.deltaV (qlTypeCount τ) h ≤ ∑ i, E.u (τ i) (x i) := by
    have := ql_sum_fiber τ (fun h => E.deltaV (qlTypeCount τ) h)
    simp only [smul_eq_mul] at this
    rw [← this]
    exact Finset.sum_le_sum fun i _ => hge i
  linarith [footnote_18_20 E hconc τ hbdd hx]

/-- **Section 18.E** (MWG, p. 672). In a finite economy `I ≫ 0`, an allocation `x*` solving
(18.E.2) for `μ = I` (with `y*_h ≫ 0`) is a Walrasian equilibrium allocation iff
`u_h(x*_h) = ∂v(I)/∂μ_h` for all `h` (from (18.E.5)). -/
theorem claim_18_E_finite_walras_iff [Fintype H] [DecidableEq H] (E : QLEconomy H K)
    (hconc : ∀ h, ConcaveOn ℝ (Set.Ici 0) (E.ψ h)) (hmono : ∀ h, MonotoneOn (E.ψ h) (Set.Ici 0))
    (hω : ∀ h, 0 ≤ (E.ω h).1) {I : H → ℝ} (hI : ∀ h, 0 < I h) {x : H → (Fin K → ℝ) × ℝ}
    (hint : ∀ h l, 0 < (x h).1 l) (hopt : E.IsOptimal I x)
    (hdψ : ∀ h, DifferentiableAt ℝ (E.ψ h) (x h).1) (hv : DifferentiableAt ℝ E.v I) :
    (∃ q, E.IsWalrasEqm I q x) ↔ ∀ h, E.u h (x h) = fderiv ℝ E.v I (Pi.single h 1) := by
  constructor
  · rintro ⟨q, hW⟩
    exact (proposition_18_E_1_of_walras E hmono hω hI hW hv).2
  · intro hmp
    exact E.walras_of_optimal_of_partial hconc hmono hω hI hint hopt
      (fun h => (hdψ h).hasFDerivAt) hv.hasFDerivAt hmp

end MWG.CoreFoundations
