/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPositiveEquilibriumTheory.Existence

/-!
# Exercise 17.B.3: excess demand near the boundary (MWG p. 642)

* **(a)** (`exercise_17_B_3a`): for `z` satisfying (i)-(v), if `pⁿ → p` with some but not all
  `p_ℓ` zero, then for large `n` the maximal excess demand is attained only at commodities whose
  price goes to zero: every `ℓ` with `p_ℓ > 0` has `z_ℓ(pⁿ) < z_k(pⁿ)` for some `k`.
* **(b)** (`exercise_17_B_3b`): an example in which a commodity whose price goes to zero stays
  in excess supply for all `n`. The function `zₗ(p) = (∑ₖ pₖ) / (pₗ² ∑ₖ 1/pₖ) - 1` (the excess
  demand of a consumer with `u = ∑ₗ √xₗ` and `ω = (1, ..., 1)`) satisfies (i)-(v)
  (`ex17B3z_isStandard`), and along `pⁿ = (1, 1/m, 1/m³)`, `m = n + 2`, good 2's price goes to
  zero but `z₂(pⁿ) < 0` for every `n`: relative prices matter (good 3 becomes cheaper faster).
-/

namespace MWG.PositiveEquilibriumTheory

open MWG.ConsumerChoice
open Filter Topology

variable {L : ℕ}

/-- **Exercise 17.B.3(a)** (MWG, p. 642). Let `z` satisfy (i)-(v) of Proposition 17.B.2 and
`pⁿ ≫ 0`, `pⁿ → p` with `p ≠ 0` and `p_ℓ = 0` for some `ℓ`. Then for `n` large the maximal excess
demand is obtained only at commodities whose price goes to zero: for every `ℓ` with `p_ℓ > 0`,
some `z_k(pⁿ)` exceeds `z_ℓ(pⁿ)`. -/
theorem exercise_17_B_3a {z : (Fin L → ℝ) → Fin L → ℝ} (hz : IsStandardExcessDemand z)
    {ps : ℕ → Fin L → ℝ} {p : Fin L → ℝ} (hps : ∀ n, ps n ∈ posOrthant L)
    (hlim : Tendsto ps atTop (𝓝 p)) (hp0 : p ≠ 0) (hpl : ∃ l, p l = 0) :
    ∀ᶠ n in atTop, ∀ l, 0 < p l → ∃ k, z (ps n) l < z (ps n) k := by
  obtain ⟨s, hs0, hs⟩ := hz.boundedBelow
  rw [eventually_all]
  intro l
  by_cases hl : 0 < p l
  swap
  · exact Eventually.of_forall fun _ h => absurd h hl
  set S := ∑ k, p k + 1 with hSdef
  have hS0 : 0 < S := by
    have : 0 ≤ ∑ k, p k := Finset.sum_nonneg fun k _ => nonneg_of_tendsto_pos hps hlim k
    linarith
  have hsumlim : Tendsto (fun n => ∑ k, ps n k) atTop (𝓝 (∑ k, p k)) :=
    tendsto_finsetSum _ fun k _ => ((continuous_apply k).tendsto p).comp hlim
  have hS : ∀ᶠ n in atTop, ∑ k, ps n k < S := hsumlim.eventually (gt_mem_nhds (by linarith))
  have hpl' : ∀ᶠ n in atTop, p l / 2 < ps n l :=
    (((continuous_apply l).tendsto p).comp hlim).eventually (lt_mem_nhds (by linarith))
  have hv := hz.boundary ps p hps hlim hp0 hpl (2 * s * S / p l)
  filter_upwards [hS, hpl', hv] with n hn1 hn2 hn3 _
  obtain ⟨k, hk⟩ := hn3
  refine ⟨k, lt_of_le_of_lt ?_ hk⟩
  have hb := footnote_17_10 hz.walras hs0 hs (hps n) l
  rw [le_div_iff₀ hl]
  have hsS : s * ∑ k, ps n k ≤ s * S := mul_le_mul_of_nonneg_left hn1.le hs0.le
  rcases le_or_gt (z (ps n) l) 0 with h | h
  · nlinarith
  · nlinarith

/-! ### Exercise 17.B.3(b): an example -/

/-- **Exercise 17.B.3(b)** (MWG, p. 642). The excess demand of a consumer with `u = ∑ₗ √xₗ` and
endowment `(1, ..., 1)`: `zₗ(p) = (∑ₖ pₖ) / (pₗ² ∑ₖ 1/pₖ) - 1`. -/
noncomputable def ex17B3z (L : ℕ) (p : Fin L → ℝ) : Fin L → ℝ :=
  fun l => (∑ k, p k) / (p l ^ 2 * ∑ k, (p k)⁻¹) - 1

/-- `∑ₖ 1/pₖ > 0` at `p ≫ 0` with at least one good. -/
theorem sum_inv_pos (hL : 0 < L) {p : Fin L → ℝ} (hp : p ∈ posOrthant L) :
    0 < ∑ k, (p k)⁻¹ :=
  Finset.sum_pos (fun k _ => inv_pos.2 (hp k)) ⟨⟨0, hL⟩, Finset.mem_univ _⟩

/-- `∑ₖ pₖ > 0` at `p ≫ 0` with at least one good. -/
theorem sum_pos_of_pos (hL : 0 < L) {p : Fin L → ℝ} (hp : p ∈ posOrthant L) :
    0 < ∑ k, p k :=
  Finset.sum_pos (fun k _ => hp k) ⟨⟨0, hL⟩, Finset.mem_univ _⟩

/-- **Exercise 17.B.3(b)**: the example satisfies (i)-(v) of Proposition 17.B.2. -/
theorem ex17B3z_isStandard (hL : 0 < L) : IsStandardExcessDemand (ex17B3z L) where
  continuous := by
    refine continuousOn_pi.2 fun l => ?_
    have hsum : ContinuousOn (fun p : Fin L → ℝ => ∑ k, p k) (posOrthant L) := by fun_prop
    have hinv : ContinuousOn (fun p : Fin L → ℝ => ∑ k, (p k)⁻¹) (posOrthant L) :=
      continuousOn_finsetSum _ fun k _ =>
        (continuous_apply k).continuousOn.inv₀ fun p hp => (hp k).ne'
    have hden : ContinuousOn (fun p : Fin L → ℝ => p l ^ 2 * ∑ k, (p k)⁻¹) (posOrthant L) :=
      ((continuous_apply l).continuousOn.pow 2).mul hinv
    exact (hsum.div hden fun p hp =>
      (mul_pos (pow_pos (hp l) 2) (sum_inv_pos hL hp)).ne').sub continuousOn_const
  homogeneous := by
    intro p hp α hα
    funext l
    simp only [ex17B3z, Pi.smul_apply, smul_eq_mul, mul_inv, ← Finset.mul_sum]
    have h1 := (sum_inv_pos hL hp).ne'
    have h2 := (hp l).ne'
    field_simp
  walras := by
    intro p hp
    have hT := (sum_inv_pos hL hp).ne'
    have hterm : ∀ l, p l * ((∑ k, p k) / (p l ^ 2 * ∑ k, (p k)⁻¹) - 1) =
        (∑ k, p k) / (∑ k, (p k)⁻¹) * (p l)⁻¹ - p l := fun l => by
      have := (hp l).ne'
      field_simp
    simp only [dotProduct, ex17B3z, hterm, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [div_mul_cancel₀ _ hT, sub_self]
  boundedBelow := ⟨2, two_pos, fun p hp l => by
    have : 0 ≤ (∑ k, p k) / (p l ^ 2 * ∑ k, (p k)⁻¹) :=
      div_nonneg (sum_pos_of_pos hL hp).le (mul_pos (pow_pos (hp l) 2) (sum_inv_pos hL hp)).le
    simp only [ex17B3z]
    linarith⟩
  boundary := by
    intro ps p hps hlim hp0 hpl M
    obtain ⟨l0, hl0⟩ := hpl
    have hS : 0 < ∑ k, p k := by
      have := dotProduct_pos_of_ne_zero (nonneg_of_tendsto_pos hps hlim) hp0
        (x := fun _ => 1) (fun _ => one_pos)
      simpa [dotProduct] using this
    set S := ∑ k, p k
    set δ := S / (2 * L * (|M| + 2)) with hδ
    have hδ0 : 0 < δ := by
      have : (0 : ℝ) < L := by exact_mod_cast hL
      positivity
    have hsumlim : Tendsto (fun n => ∑ k, ps n k) atTop (𝓝 S) :=
      tendsto_finsetSum _ fun k _ => ((continuous_apply k).tendsto p).comp hlim
    have h1 : ∀ᶠ n in atTop, S / 2 < ∑ k, ps n k := hsumlim.eventually (lt_mem_nhds (by linarith))
    have h2 : ∀ᶠ n in atTop, ps n l0 < δ :=
      (((continuous_apply l0).tendsto p).comp hlim).eventually
        (gt_mem_nhds (by rw [hl0]; exact hδ0))
    filter_upwards [h1, h2] with n hn1 hn2
    obtain ⟨m, -, hm⟩ := Finset.exists_min_image Finset.univ (ps n) ⟨l0, Finset.mem_univ _⟩
    refine ⟨m, ?_⟩
    have hpm := hps n m
    have hpm_le : ps n m < δ := lt_of_le_of_lt (hm l0 (Finset.mem_univ _)) hn2
    have hT : ∑ k, (ps n k)⁻¹ ≤ L * (ps n m)⁻¹ := by
      calc ∑ k, (ps n k)⁻¹ ≤ ∑ _k : Fin L, (ps n m)⁻¹ :=
            Finset.sum_le_sum fun k _ => inv_anti₀ hpm (hm k (Finset.mem_univ k))
        _ = L * (ps n m)⁻¹ := by simp
    have hT0 := sum_inv_pos hL (hps n)
    have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
    -- x_m ≥ (∑ pⁿ) / (L pⁿ_m)
    have hx : (∑ k, ps n k) / (L * ps n m) ≤
        (∑ k, ps n k) / (ps n m ^ 2 * ∑ k, (ps n k)⁻¹) := by
      apply div_le_div_of_nonneg_left (sum_pos_of_pos hL (hps n)).le (by positivity)
      calc ps n m ^ 2 * ∑ k, (ps n k)⁻¹ ≤ ps n m ^ 2 * (L * (ps n m)⁻¹) :=
            mul_le_mul_of_nonneg_left hT (by positivity)
        _ = L * ps n m := by field_simp
    have hbig : |M| + 2 < (∑ k, ps n k) / (L * ps n m) := by
      rw [lt_div_iff₀ (by positivity)]
      have hδ' : δ * (2 * L * (|M| + 2)) = S := by
        rw [hδ]
        field_simp
      have hM : 0 < |M| + 2 := by positivity
      have : (|M| + 2) * (L * ps n m) < (|M| + 2) * (L * δ) := by
        apply mul_lt_mul_of_pos_left _ hM
        exact mul_lt_mul_of_pos_left hpm_le hLpos
      nlinarith
    simp only [ex17B3z]
    linarith [le_abs_self M]

/-- The price path of Exercise 17.B.3(b): `pⁿ = (1, 1/m, 1/m³)`, `m = n + 2`. -/
noncomputable def ex17B3path (n : ℕ) : Fin 3 → ℝ :=
  ![1, 1 / ((n : ℝ) + 2), 1 / ((n : ℝ) + 2) ^ 3]

/-- **Exercise 17.B.3(b)** (MWG, p. 642). Along `pⁿ = (1, 1/m, 1/m³)` the price of good 2 tends
to zero, yet good 2 is in excess supply for every `n`: `z₂(pⁿ) = (m³ + m² + 1)/(m(m³ + m + 1))
- 1 < 0`. -/
theorem exercise_17_B_3b :
    (∀ n, ex17B3path n ∈ posOrthant 3) ∧
      Tendsto (fun n => ex17B3path n) atTop (𝓝 ![1, 0, 0]) ∧
      ∀ n, ex17B3z 3 (ex17B3path n) 1 < 0 := by
  have hm : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 2 := fun n => by positivity
  refine ⟨fun n l => ?_, ?_, fun n => ?_⟩
  · have h1 : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
    have h2 : (0 : ℝ) < 1 / ((n : ℝ) + 2) ^ 3 := by positivity
    fin_cases l
    · simp [ex17B3path]
    · simpa [ex17B3path] using h1
    · simpa [ex17B3path] using h2
  · refine tendsto_pi_nhds.2 fun l => ?_
    have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0)).comp (tendsto_add_atTop_nat 1)
      refine this.congr fun n => ?_
      simp only [Function.comp, Nat.cast_add, Nat.cast_one]
      ring_nf
    fin_cases l
    · simp [ex17B3path]
    · simpa [ex17B3path] using h1
    · have h3 : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 2)) ^ 3) atTop (𝓝 0) := by
        simpa using h1.pow 3
      simpa [ex17B3path, div_pow] using h3
  · set m : ℝ := (n : ℝ) + 2 with hmdef
    have hm2 : 2 ≤ m := by simp [m]
    simp only [ex17B3z, ex17B3path, Fin.sum_univ_three]
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons]
    rw [← hmdef]
    have hm0 : 0 < m := by linarith
    rw [sub_neg, div_lt_one (by positivity)]
    field_simp
    nlinarith [mul_pos hm0 hm0, mul_pos (mul_pos hm0 hm0) hm0,
      mul_pos (mul_pos (mul_pos hm0 hm0) hm0) hm0]

end MWG.PositiveEquilibriumTheory
