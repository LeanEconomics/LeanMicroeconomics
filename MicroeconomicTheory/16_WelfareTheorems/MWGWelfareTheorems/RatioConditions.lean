/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGWelfareTheorems.FirstOrderWelfare

/-!
# The three efficiency conditions (MWG Exercise 16.F.4, pp. 564-565)

Problems (16.F.7) (allocation of given aggregates across consumers) and (16.F.8) (efficient
production across technologies) and the ratio conditions (16.F.4)-(16.F.6), at interior solutions,
with differentiability at the solution:

* (16.F.7) ⟹ (16.F.4): all consumers' marginal rates of substitution coincide
  (`exercise_16_F_4_i`).
* (16.F.8) ⟹ (16.F.5): all firms' marginal rates of transformation coincide
  (`exercise_16_F_4_ii`).
* (16.F.6): every consumer's marginal rate of substitution equals every firm's marginal rate of
  transformation (`exercise_16_F_4_iii`).

Departure: the book derives the conditions from Lagrangian first-order conditions, and (16.F.6)
from problem (16.F.9) in the value functions `u(x̄)`, `f(ȳ)`, which presupposes that these value
functions are differentiable and obey envelope identities that the book does not establish. We
prove each ratio condition directly by the underlying first-order (perturbation) argument: if two
gradients are not proportional in goods `ℓ, ℓ'`, a small reallocation along a direction in which
one gradient is positive and the other negative is feasible and improves the objective; for
(16.F.6) the reallocation is between consumer `i₀` and a firm in problem (16.F.1).
-/

namespace MWG.WelfareTheorems

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.Production Kreps.PreferenceProperties
open Filter Topology

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {L : ℕ}

/-- If two pairs of positive numbers are not proportional, some direction `(d₁, d₂)` makes the
first linear form positive and the second negative. -/
theorem exists_sep_direction {a₁ a₂ b₁ b₂ : ℝ} (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hb₁ : 0 < b₁)
    (hb₂ : 0 < b₂) (hne : a₁ * b₂ ≠ a₂ * b₁) :
    ∃ d₁ d₂ : ℝ, 0 < a₁ * d₁ + a₂ * d₂ ∧ b₁ * d₁ + b₂ * d₂ < 0 := by
  set D := a₁ * b₂ - a₂ * b₁ with hD
  set N := a₁ * b₁ + a₂ * b₂ with hN
  have hNpos : 0 < N := by positivity
  rcases lt_or_gt_of_ne (sub_ne_zero.mpr hne) with hneg | hpos
  · refine ⟨-b₂ - (-D) / (2 * N) * b₁, b₁ - (-D) / (2 * N) * b₂, ?_, ?_⟩
    · have : a₁ * (-b₂ - -D / (2 * N) * b₁) + a₂ * (b₁ - -D / (2 * N) * b₂) = -D / 2 := by
        field_simp; rw [hD, hN]; ring
      rw [this]; linarith
    · have : b₁ * (-b₂ - -D / (2 * N) * b₁) + b₂ * (b₁ - -D / (2 * N) * b₂) =
          -(-D / (2 * N)) * (b₁ ^ 2 + b₂ ^ 2) := by ring
      rw [this]
      have : 0 < -D / (2 * N) := div_pos (by linarith) (by positivity)
      nlinarith [sq_nonneg b₁, mul_pos hb₁ hb₁]
  · refine ⟨b₂ - D / (2 * N) * b₁, -b₁ - D / (2 * N) * b₂, ?_, ?_⟩
    · have : a₁ * (b₂ - D / (2 * N) * b₁) + a₂ * (-b₁ - D / (2 * N) * b₂) = D / 2 := by
        field_simp; rw [hD, hN]; ring
      rw [this]; linarith
    · have : b₁ * (b₂ - D / (2 * N) * b₁) + b₂ * (-b₁ - D / (2 * N) * b₂) =
          -(D / (2 * N)) * (b₁ ^ 2 + b₂ ^ 2) := by ring
      rw [this]
      have : 0 < D / (2 * N) := div_pos (by linarith) (by positivity)
      nlinarith [sq_nonneg b₁, mul_pos hb₁ hb₁]

/-- Along a direction with positive derivative, a function eventually (for small `t > 0`)
exceeds its value. -/
theorem eventually_gt_along {g : (Fin L → ℝ) → ℝ} {g' : (Fin L → ℝ) →L[ℝ] ℝ} {z d : Fin L → ℝ}
    (hg : HasFDerivAt g g' z) (hd : 0 < g' d) : ∀ᶠ t in 𝓝[>] (0 : ℝ), g z < g (z + t • d) := by
  have := mk_eventually_gt_of_deriv_pos (mc_line_hasDerivAt hg d) hd
  simpa using this

/-- Strictly positive coordinates stay positive under small perturbations. -/
theorem eventually_pos_along {z d : Fin L → ℝ} (hz : ∀ l, 0 < z l) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ l, 0 < (z + t • d) l := by
  rw [eventually_all]
  intro l
  have hc : Continuous fun t : ℝ => (z + t • d) l := by fun_prop
  have := hc.continuousAt (x := 0) |>.eventually (lt_mem_nhds (by simpa using hz l))
  exact eventually_nhdsWithin_of_eventually_nhds this

/-- The direction `d₁ eₗ + d₂ eₗ'` evaluated by a linear form. -/
theorem single_eq_smul_single (l : Fin L) (c : ℝ) :
    (Pi.single l c : Fin L → ℝ) = c • Pi.single l 1 := by
  funext k
  by_cases h : k = l
  · subst h; simp
  · simp [h]

/-- The direction `d₁ eₗ + d₂ eₗ'` evaluated by a linear form. -/
theorem clm_two_dir (φ : (Fin L → ℝ) →L[ℝ] ℝ) (l l' : Fin L) (d₁ d₂ : ℝ) :
    φ (Pi.single l d₁ + Pi.single l' d₂) = φ (Pi.single l 1) * d₁ + φ (Pi.single l' 1) * d₂ := by
  rw [map_add, single_eq_smul_single l d₁, single_eq_smul_single l' d₂, map_smul, map_smul,
    smul_eq_mul, smul_eq_mul]
  ring

/-- **Problem (16.F.7)** (MWG, p. 564): distribute the aggregate `x̄` to maximize `u_{i₀}`
subject to `uᵢ(xᵢ) ≥ ūᵢ` (`i ≠ i₀`), `∑ᵢ xᵢ ≤ x̄` and `x ≥ 0`. -/
def Problem16F7 (u : ι → (Fin L → ℝ) → ℝ) (xb : Fin L → ℝ) (i₀ : ι) (ub : ι → ℝ) :
    Set (ι → Fin L → ℝ) :=
  {x | (∀ i, i ≠ i₀ → ub i ≤ u i (x i)) ∧ (∀ l, ∑ i, x i l ≤ xb l) ∧ ∀ i l, 0 ≤ x i l}

/-- **Exercise 16.F.4**, (16.F.7) ⟹ (16.F.4) (MWG, p. 576). At an interior solution `x ≫ 0` of
(16.F.7), with every `uᵢ` differentiable at `xᵢ` with positive partial derivatives, every
consumer's marginal rate of substitution between goods `ℓ, ℓ'` equals consumer `i₀`'s (hence all
coincide): `∂u_{i₀}/∂xₗ · ∂uᵢ/∂xₗ' = ∂u_{i₀}/∂xₗ' · ∂uᵢ/∂xₗ`. -/
theorem exercise_16_F_4_i {u : ι → (Fin L → ℝ) → ℝ} {xb : Fin L → ℝ} {i₀ : ι}
    {ub : ι → ℝ} {x : ι → Fin L → ℝ} (hx : x ∈ Problem16F7 u xb i₀ ub)
    (hopt : ∀ x' ∈ Problem16F7 u xb i₀ ub, u i₀ (x' i₀) ≤ u i₀ (x i₀))
    (hint : ∀ i l, 0 < x i l) {u' : ι → (Fin L → ℝ) →L[ℝ] ℝ}
    (hu : ∀ i, HasFDerivAt (u i) (u' i) (x i)) (hpos : ∀ i l, 0 < u' i (Pi.single l 1))
    (i : ι) (l l' : Fin L) :
    u' i₀ (Pi.single l 1) * u' i (Pi.single l' 1) =
      u' i₀ (Pi.single l' 1) * u' i (Pi.single l 1) := by
  classical
  by_contra hne
  by_cases hii : i = i₀
  · subst hii; exact hne (mul_comm _ _)
  obtain ⟨d₁, d₂, hpos₀, hneg⟩ := exists_sep_direction (hpos i₀ l) (hpos i₀ l') (hpos i l)
    (hpos i l') hne
  set d : Fin L → ℝ := Pi.single l d₁ + Pi.single l' d₂ with hd
  -- consumer `i₀` receives `t d`, consumer `i` gives it up
  have h1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), u i₀ (x i₀) < u i₀ (x i₀ + t • d) :=
    eventually_gt_along (hu i₀) (by rw [hd, clm_two_dir]; exact hpos₀)
  have h2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), u i (x i) < u i (x i + t • -d) :=
    eventually_gt_along (hu i) (by rw [map_neg, hd, clm_two_dir]; linarith)
  have h3 := eventually_pos_along (z := x i₀) (d := d) (hint i₀)
  have h4 := eventually_pos_along (z := x i) (d := -d) (hint i)
  obtain ⟨t, ht1, ht2, ht3, ht4⟩ := (h1.and (h2.and (h3.and h4))).exists
  set x' : ι → Fin L → ℝ := fun k =>
    if k = i₀ then x i₀ + t • d else if k = i then x i + t • -d else x k with hx'
  have hx'i₀ : x' i₀ = x i₀ + t • d := by simp [hx']
  have hx'i : x' i = x i + t • -d := by simp [hx', hii]
  have hmem : x' ∈ Problem16F7 u xb i₀ ub := by
    refine ⟨fun k hk => ?_, fun m => ?_, fun k m => ?_⟩
    · by_cases hki : k = i
      · subst hki; rw [hx'i]; exact (hx.1 k hk).trans ht2.le
      · simpa [hx', hk, hki] using hx.1 k hk
    · have hsum : ∑ k, x' k = ∑ k, x k := by
        have : ∀ k, x' k = x k + (if k = i₀ then t • d else 0) - (if k = i then t • d else 0) :=
          fun k => by
            by_cases h1 : k = i₀
            · subst h1; simp [hx', Ne.symm hii]
            · by_cases h2 : k = i
              · subst h2; simp [hx', h1, sub_eq_add_neg]
              · simp [hx', h1, h2]
        simp only [this, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq',
          Finset.mem_univ, ↓reduceIte, add_sub_cancel_right]
      have := congrFun hsum m
      simp only [Finset.sum_apply] at this
      rw [this]
      exact hx.2.1 m
    · by_cases h1 : k = i₀
      · subst h1; rw [hx'i₀]; exact (ht3 m).le
      · by_cases h2 : k = i
        · subst h2; rw [hx'i]; exact (ht4 m).le
        · simpa [hx', h1, h2] using hx.2.2 k m
  have := hopt x' hmem
  rw [hx'i₀] at this
  linarith

/-- **Problem (16.F.8)** (MWG, p. 564): maximize the total output `∑ⱼ y₁ⱼ` of good `0` subject to
`∑ⱼ yₗⱼ ≥ ȳₗ` for the other goods and `Fⱼ(yⱼ) ≤ 0`. -/
def Problem16F8 (F : κ → (Fin L → ℝ) → ℝ) (l₀ : Fin L) (yb : Fin L → ℝ) : Set (κ → Fin L → ℝ) :=
  {y | (∀ l, l ≠ l₀ → yb l ≤ ∑ j, y j l) ∧ ∀ j, F j (y j) ≤ 0}

/-- **Exercise 16.F.4**, (16.F.8) ⟹ (16.F.5) (MWG, p. 576). At a solution of (16.F.8), with
every `Fⱼ` differentiable at `yⱼ` with positive partial derivatives, all firms' marginal rates of
transformation between good `l₀` and every good `ℓ` coincide. -/
theorem exercise_16_F_4_ii {F : κ → (Fin L → ℝ) → ℝ} {l₀ : Fin L}
    {yb : Fin L → ℝ} {y : κ → Fin L → ℝ} (hy : y ∈ Problem16F8 F l₀ yb)
    (hopt : ∀ y' ∈ Problem16F8 F l₀ yb, ∑ j, y' j l₀ ≤ ∑ j, y j l₀)
    {F' : κ → (Fin L → ℝ) →L[ℝ] ℝ} (hF : ∀ j, HasFDerivAt (F j) (F' j) (y j))
    (hpos : ∀ j l, 0 < F' j (Pi.single l 1)) (j j' : κ) (l : Fin L) :
    F' j (Pi.single l₀ 1) * F' j' (Pi.single l 1) =
      F' j (Pi.single l 1) * F' j' (Pi.single l₀ 1) := by
  classical
  by_contra hne
  by_cases hjj : j = j'
  · subst hjj; exact hne (mul_comm _ _)
  by_cases hl : l = l₀
  · subst hl; exact hne rfl
  -- a direction `d` with `∇Fⱼ·d > 0 > ∇Fⱼ'·d`: firm `j'` moves along `d` and firm `j` along `-d`
  -- plus a little extra output of good `l₀`; both stay feasible and total output rises
  obtain ⟨d₁, d₂, hposj, hnegj'⟩ := exists_sep_direction (hpos j l₀) (hpos j l) (hpos j' l₀)
    (hpos j' l) (by intro h; exact hne (by linarith))
  set d : Fin L → ℝ := Pi.single l₀ d₁ + Pi.single l d₂ with hd
  have hFj'd : F' j' d < 0 := by rw [hd, clm_two_dir]; exact hnegj'
  have hFjd : F' j (-d) < 0 := by rw [map_neg, hd, clm_two_dir]; linarith
  -- add a little extra output of `l₀` to firm `j` while keeping its derivative negative
  set s : ℝ := -(F' j (-d)) / (2 * F' j (Pi.single l₀ 1)) with hs
  have hs0 : 0 < s := div_pos (by linarith) (by linarith [hpos j l₀])
  set e : Fin L → ℝ := -d + Pi.single l₀ s with he
  have hFje : F' j e < 0 := by
    have h1 : F' j e = F' j (-d) + s * F' j (Pi.single l₀ 1) := by
      rw [he, map_add, single_eq_smul_single l₀ s, map_smul, smul_eq_mul]
    have h2 : s * F' j (Pi.single l₀ 1) = -(F' j (-d)) / 2 := by
      have hne0 := (hpos j l₀).ne'
      rw [hs]; field_simp
    rw [h1, h2]
    linarith
  have h1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), F j' (y j' + t • d) < F j' (y j') := by
    have := eventually_gt_along (g := fun z => -F j' z) (d := d) (hF j').neg (by
      simp only [neg_apply]; linarith)
    exact this.mono fun t ht => by linarith
  have h2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), F j (y j + t • e) < F j (y j) := by
    have := eventually_gt_along (g := fun z => -F j z) (d := e) (hF j).neg (by
      simp only [neg_apply]; linarith)
    exact this.mono fun t ht => by linarith
  obtain ⟨t, ht1, ht2, ht0⟩ := (h1.and (h2.and self_mem_nhdsWithin)).exists
  set y' : κ → Fin L → ℝ := fun k =>
    if k = j then y j + t • e else if k = j' then y j' + t • d else y k with hy'
  have hy'j : y' j = y j + t • e := by simp [hy']
  have hy'j' : y' j' = y j' + t • d := by simp [hy', Ne.symm hjj]
  have hsum : ∑ k, y' k = ∑ k, y k + t • Pi.single l₀ s := by
    have : ∀ k, y' k = y k + (if k = j then t • e else 0) + (if k = j' then t • d else 0) :=
      fun k => by
        by_cases h1 : k = j
        · rw [h1, hy'j]; simp [hjj]
        · by_cases h2 : k = j'
          · rw [h2, hy'j']; simp [Ne.symm hjj]
          · simp [hy', h1, h2]
    simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    rw [he]
    module
  have hmem : y' ∈ Problem16F8 F l₀ yb := by
    refine ⟨fun m hm => ?_, fun k => ?_⟩
    · have := congrFun hsum m
      simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Pi.single_eq_of_ne hm, mul_zero, add_zero] at this
      rw [this]
      exact hy.1 m hm
    · by_cases h1 : k = j
      · subst h1; rw [hy'j]; exact ht2.le.trans (hy.2 k)
      · by_cases h2 : k = j'
        · subst h2; rw [hy'j']; exact ht1.le.trans (hy.2 k)
        · simpa [hy', h1, h2] using hy.2 k
  have := hopt y' hmem
  have h3 := congrFun hsum l₀
  simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Pi.single_eq_same] at h3
  rw [h3] at this
  have : 0 < t * s := mul_pos ht0 hs0
  linarith

/-- **Exercise 16.F.4**, (16.F.6) (MWG, p. 576). At a solution `(x, y)` of (16.F.1) with
`x_{i₀} ≫ 0`, `u_{i₀}` differentiable at `x_{i₀}` and `Fⱼ` at `yⱼ` with positive partial
derivatives, consumer `i₀`'s marginal rate of substitution between goods `ℓ, ℓ'` equals firm
`j`'s marginal rate of transformation. -/
theorem exercise_16_F_4_iii {u : ι → (Fin L → ℝ) → ℝ}
    {F : κ → (Fin L → ℝ) → ℝ} {ω : Fin L → ℝ} {i₀ : ι} {ub : ι → ℝ}
    {v : (ι → Fin L → ℝ) × (κ → Fin L → ℝ)} (hv : IsSolution16F1 u F ω i₀ ub v)
    (hint : ∀ l, 0 < v.1 i₀ l) {u' : (Fin L → ℝ) →L[ℝ] ℝ} (hu : HasFDerivAt (u i₀) u' (v.1 i₀))
    (hupos : ∀ l, 0 < u' (Pi.single l 1)) {F' : κ → (Fin L → ℝ) →L[ℝ] ℝ}
    (hF : ∀ j, HasFDerivAt (F j) (F' j) (v.2 j)) (hFpos : ∀ j l, 0 < F' j (Pi.single l 1))
    (j : κ) (l l' : Fin L) :
    u' (Pi.single l 1) * F' j (Pi.single l' 1) = u' (Pi.single l' 1) * F' j (Pi.single l 1) := by
  classical
  by_contra hne
  obtain ⟨d₁, d₂, hposu, hnegF⟩ := exists_sep_direction (hupos l) (hupos l') (hFpos j l)
    (hFpos j l') hne
  set d : Fin L → ℝ := Pi.single l d₁ + Pi.single l' d₂ with hd
  have h1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), u i₀ (v.1 i₀) < u i₀ (v.1 i₀ + t • d) :=
    eventually_gt_along hu (by rw [hd, clm_two_dir]; exact hposu)
  have h2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), F j (v.2 j + t • d) < F j (v.2 j) := by
    have := eventually_gt_along (g := fun z => -F j z) (d := d) (hF j).neg (by
      simp only [neg_apply, hd, clm_two_dir]; linarith)
    exact this.mono fun t ht => by linarith
  have h3 := eventually_pos_along (z := v.1 i₀) (d := d) hint
  obtain ⟨t, ht1, ht2, ht3⟩ := (h1.and (h2.and h3)).exists
  set x' := Function.update v.1 i₀ (v.1 i₀ + t • d) with hx'
  set y' := Function.update v.2 j (v.2 j + t • d) with hy'
  have hmem : (x', y') ∈ Problem16F1 u F ω i₀ ub := by
    refine ⟨fun i hi => ?_, fun m => ?_, fun k => ?_, fun i m => ?_⟩
    · simpa [hx', hi] using hv.1.1 i hi
    · have hx : ∑ i, x' i m = ∑ i, v.1 i m + t * d m := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀),
          ← Finset.add_sum_erase _ (fun i => v.1 i m) (Finset.mem_univ i₀)]
        have : ∑ i ∈ Finset.univ.erase i₀, x' i m = ∑ i ∈ Finset.univ.erase i₀, v.1 i m :=
          Finset.sum_congr rfl fun i hi => by simp [hx', Finset.ne_of_mem_erase hi]
        rw [this]
        simp [hx']
        ring
      have hy : ∑ k, y' k m = ∑ k, v.2 k m + t * d m := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j),
          ← Finset.add_sum_erase _ (fun k => v.2 k m) (Finset.mem_univ j)]
        have : ∑ k ∈ Finset.univ.erase j, y' k m = ∑ k ∈ Finset.univ.erase j, v.2 k m :=
          Finset.sum_congr rfl fun k hk => by simp [hy', Finset.ne_of_mem_erase hk]
        rw [this]
        simp [hy']
        ring
      rw [hx, hy]
      linarith [hv.1.2.1 m]
    · by_cases hk : k = j
      · subst hk; simp only [hy', Function.update_self]; exact ht2.le.trans (hv.1.2.2.1 k)
      · simpa [hy', hk] using hv.1.2.2.1 k
    · by_cases hi : i = i₀
      · subst hi; simp only [hx', Function.update_self]; exact (ht3 m).le
      · simpa [hx', hi] using hv.1.2.2.2 i m
  have := hv.2 _ hmem
  simp only [hx', Function.update_self] at this
  linarith

end MWG.WelfareTheorems
