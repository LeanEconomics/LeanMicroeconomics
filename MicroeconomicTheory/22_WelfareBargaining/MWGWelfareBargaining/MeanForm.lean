/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGWelfareBargaining.Invariance
import Mathlib.Analysis.Convex.Quasiconvex
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Algebra.Group.Fin.Basic

/-!
# Social welfare functions of the form (22.D.1): Exercise 22.D.6

MWG, Exercise 22.D.6(a)-(e), p. 853, on social welfare functions
`W(u) = ū - g(u₁ - ū, …, u_I - ū)` (`form22D1 g`).

* (a) The nonsymmetric utilitarian `∑ bᵢuᵢ` (`b ≥ 0`, `∑ bᵢ > 0`) is a positive multiple of
  such a form, with `g` linear.
* (b) **Correction.** As printed ("if `W` is symmetric and `g(0) = 0` then `g ≥ 0`") the claim is
  false: `W(u) = ū + |u₁ - u₂|/4` is continuous, increasing and symmetric, of the form (22.D.1)
  with `g(0) = 0`, and `g(1, -1) = -1/2`. It holds when `W` is in addition quasiconcave (e.g.
  concave, as in Section 22.C): averaging the cyclic permutations of `s` gives `0`.
* (c) The symmetric Rawlsian `min uᵢ` has the form (22.D.1) with `g(s) = -min sᵢ`; a nonsymmetric
  Rawlsian `min(β₁u₁, β₂u₂)` with `β₁ ≠ β₂` is not invariant to common changes of origins, so it
  has no such form (Proposition 22.D.2 requires that invariance).
* (d) `W = (1 - c)ū + c min uᵢ`, `c ∈ [0, 1]`, has the form (22.D.1) with `g(s) = -c min sᵢ ≥ 0`
  on `{∑ sᵢ = 0}`: intermediate between utilitarian (`c = 0`) and Rawlsian (`c = 1`).
* (e) A `g` that is homogeneous of degree one on `{∑ sᵢ = 0}` and differentiable there at `0` is
  linear on that domain.
-/

namespace MWG.WelfareBargaining

open Filter Topology

variable {ι X : Type*}

theorem mean_add_const [Fintype ι] [Nonempty ι] (u : ι → ℝ) (t : ℝ) :
    mean (fun i => u i + t) = mean u + t := by
  have hn : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  simp only [mean, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

/-- **Exercise 22.D.6(a)** (MWG, p. 853). The nonsymmetric utilitarian function `∑ bᵢuᵢ` with
`∑ bᵢ > 0` equals `(∑ bᵢ) · (ū - g(u - ūe))` for the linear `g(s) = -∑ (bᵢ/∑ b) sᵢ`; it is
thus, up to a positive factor, of the form (22.D.1). -/
theorem exercise_22_D_6a [Fintype ι] (b : ι → ℝ) (hB : 0 < ∑ i, b i) (u : ι → ℝ) :
    ∑ i, b i * u i =
      (∑ i, b i) * form22D1 (fun s => -∑ i, b i / (∑ j, b j) * s i) u := by
  have hB' : (∑ j, b j) ≠ 0 := hB.ne'
  have key : ∑ i, b i / (∑ j, b j) * (u i - mean u) =
      (∑ i, b i * u i) / (∑ j, b j) - mean u := by
    simp only [mul_sub, Finset.sum_sub_distrib, div_mul_eq_mul_div, ← Finset.sum_div,
      ← Finset.sum_mul]
    field_simp
  simp only [form22D1, key]
  field_simp
  ring

/-- The social welfare function of the counterexample to Exercise 22.D.6(b). -/
noncomputable def e22D6bW (u : Fin 2 → ℝ) : ℝ := mean u + |u 0 - u 1| / 4

/-- **Exercise 22.D.6(b), counterexample** (MWG, p. 853). `W(u) = ū + |u₁ - u₂|/4` is
continuous, increasing and symmetric, it is of the form (22.D.1) with `g(s) = -|s₁ - s₂|/4`,
`g(0) = 0`, but `g(1, -1) < 0`. -/
theorem exercise_22_D_6b_counterexample :
    Continuous e22D6bW ∧ IsIncreasingSWF e22D6bW ∧
      (∀ σ : Equiv.Perm (Fin 2), ∀ u, e22D6bW (u ∘ σ) = e22D6bW u) ∧
      (∀ u, e22D6bW u = form22D1 (fun s => -|s 0 - s 1| / 4) u) ∧
      (fun s : Fin 2 → ℝ => -|s 0 - s 1| / 4) 0 = 0 ∧
      ∑ i, (![1, -1] : Fin 2 → ℝ) i = 0 ∧
      (fun s : Fin 2 → ℝ => -|s 0 - s 1| / 4) ![1, -1] < 0 := by
  have hmean : ∀ u : Fin 2 → ℝ, mean u = (u 0 + u 1) / 2 := fun u => by
    simp [mean, Fin.sum_univ_two]
  refine ⟨?_, ⟨fun u u' h => ?_, fun u u' h => ?_⟩, fun σ u => ?_, fun u => ?_, by simp,
    by simp [Fin.sum_univ_two], by norm_num⟩
  · unfold e22D6bW
    simp only [hmean]
    fun_prop
  · simp only [e22D6bW, hmean]
    have h1 := abs_sub_abs_le_abs_sub (u 0 - u 1) (u' 0 - u' 1)
    have h2 : |u 0 - u 1 - (u' 0 - u' 1)| ≤ (u' 0 - u 0) + (u' 1 - u 1) := by
      rw [abs_le]; constructor <;> linarith [h 0, h 1]
    linarith [h 0, h 1]
  · simp only [e22D6bW, hmean]
    have h1 := abs_sub_abs_le_abs_sub (u 0 - u 1) (u' 0 - u' 1)
    have h2 : |u 0 - u 1 - (u' 0 - u' 1)| ≤ (u' 0 - u 0) + (u' 1 - u 1) := by
      rw [abs_le]; constructor <;> linarith [h 0, h 1]
    linarith [h 0, h 1]
  · have h01 : σ 0 ≠ σ 1 := σ.injective.ne (by decide)
    have hcase : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
    simp only [e22D6bW, hmean, Function.comp]
    rcases hcase (σ 0) with h0 | h0 <;> rcases hcase (σ 1) with h1 | h1 <;>
      simp only [h0, h1] at h01 ⊢ <;> first | exact absurd rfl h01 | skip
    · rw [abs_sub_comm]; ring
  · simp only [e22D6bW, form22D1, hmean]
    ring_nf

/-- **Exercise 22.D.6(b), corrected** (MWG, p. 853). If `W` is symmetric and quasiconcave and is
of the form (22.D.1) with `g(0) = 0`, then `g ≥ 0` on the domain `{s : ∑ sᵢ = 0}`. -/
theorem exercise_22_D_6b {n : ℕ} [NeZero n] {W : (Fin n → ℝ) → ℝ} {g : (Fin n → ℝ) → ℝ}
    (hform : ∀ u, W u = form22D1 g u) (hsym : ∀ (σ : Equiv.Perm (Fin n)) u, W (u ∘ σ) = W u)
    (hq : QuasiconcaveOn ℝ Set.univ W) (hg0 : g 0 = 0) (s : Fin n → ℝ) (hs : ∑ i, s i = 0) :
    0 ≤ g s := by
  have hms : mean s = 0 := by simp [mean, hs]
  have hWs : W s = -g s := by
    rw [hform, form22D1, hms]
    simp
  have hW0 : W 0 = 0 := by
    rw [hform, form22D1]
    simp only [mean, Pi.zero_apply, Finset.sum_const_zero, zero_div, sub_zero, zero_sub,
      neg_eq_zero]
    exact hg0
  have hn : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne n))
  -- the cyclic shifts of `s` lie in the convex superlevel set `{W ≥ W s}`
  have hmem : ∀ k ∈ (Finset.univ : Finset (Fin n)),
      (fun i => s (i + k)) ∈ {x ∈ Set.univ | W s ≤ W x} := by
    intro k _
    refine ⟨Set.mem_univ _, ?_⟩
    have := hsym (Equiv.addRight k) s
    exact this.ge
  have hav := (hq (W s)).sum_mem (t := Finset.univ) (w := fun _ => (1 : ℝ) / n)
    (fun _ _ => by positivity) (by simp [Finset.card_univ, Fintype.card_fin]) hmem
  have hzero : (∑ k, ((1 : ℝ) / n) • fun i => s (i + k)) = 0 := by
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, ← Finset.mul_sum]
    rw [show (∑ k, s (i + k)) = ∑ j, s j from
      Fintype.sum_equiv (Equiv.addLeft i) _ _ (fun _ => rfl), hs, mul_zero]
  rw [hzero] at hav
  have := hav.2
  linarith

/-- **Exercise 22.D.6(c)** (MWG, p. 853). The symmetric Rawlsian function `min uᵢ` has the form
(22.D.1) with `g(s) = -min sᵢ`. -/
theorem exercise_22_D_6c [Fintype ι] [Nonempty ι] (u : ι → ℝ) :
    Finset.univ.inf' Finset.univ_nonempty u =
      form22D1 (fun s => -Finset.univ.inf' Finset.univ_nonempty s) u := by
  have h := Finset.apply_inf'_eq_inf'_comp (s := Finset.univ) (f := u) Finset.univ_nonempty
    (fun x => x - mean u) (fun x y => (min_sub_sub_right x y (mean u)).symm)
  simp only [form22D1]
  rw [show (fun i => u i - mean u) = (fun x => x - mean u) ∘ u from rfl, ← h]
  ring

/-- **Exercise 22.D.6(c), nonsymmetric case** (MWG, p. 853). With `β₀ ≠ β₁`, the functional
generated by the nonsymmetric Rawlsian `min(β₀u₀, β₁u₁)` is not invariant to common changes of
origins; by Proposition 22.D.2 the form (22.D.1) is therefore unavailable for it. -/
theorem exercise_22_D_6c_nonsymmetric (hX : ∃ x y : X, x ≠ y) {β : Fin 2 → ℝ}
    (hβ : ∀ i, 0 < β i) (hne : β 0 ≠ β 1) :
    ¬InvCommonOrigins (swfFunctional (X := X) fun u : Fin 2 → ℝ => min (β 0 * u 0) (β 1 * u 1)) :=
  by
  intro hO
  have key := fun u u' (h : min (β 0 * u 0) (β 1 * u 1) = min (β 0 * u' 0) (β 1 * u' 1)) α =>
    common_origin_parallel (W := fun u : Fin 2 → ℝ => min (β 0 * u 0) (β 1 * u 1)) hX
      (swfFunctional_generatedBy _) hO (u := u) (u' := u') h α
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · set α := β 0 / (β 1 - β 0) + 1
    have hαpos : 0 < α := by
      have := div_pos (hβ 0) (sub_pos.2 hlt); simp only [α]; linarith
    have hα : β 0 * (1 + α) < β 1 * α := by
      have : (β 1 - β 0) * α = β 0 + (β 1 - β 0) := by
        simp only [α]; field_simp
      nlinarith
    have h := key 0 ![1, 0] (by simp [(hβ 0).le]) α
    simp only [Pi.zero_apply, zero_add, Matrix.cons_val_zero, Matrix.cons_val_one] at h
    rw [min_eq_left (by nlinarith), min_eq_left hα.le] at h
    nlinarith [hβ 0]
  · set α := β 1 / (β 0 - β 1) + 1
    have hαpos : 0 < α := by
      have := div_pos (hβ 1) (sub_pos.2 hgt); simp only [α]; linarith
    have hα : β 1 * (1 + α) < β 0 * α := by
      have : (β 0 - β 1) * α = β 1 + (β 0 - β 1) := by
        simp only [α]; field_simp
      nlinarith
    have h := key 0 ![0, 1] (by simp [(hβ 1).le]) α
    simp only [Pi.zero_apply, zero_add, Matrix.cons_val_zero, Matrix.cons_val_one] at h
    rw [min_eq_right (by nlinarith), min_eq_right hα.le] at h
    nlinarith [hβ 1]

/-- **Exercise 22.D.6(d)** (MWG, p. 853). For `c ∈ [0, 1]`, `W(u) = (1 - c)ū + c min uᵢ` is
increasing and of the form (22.D.1) with `g(s) = -c min sᵢ`, and `g ≥ 0` on `{∑ sᵢ = 0}`;
`c = 0` is utilitarian and `c = 1` Rawlsian. -/
theorem exercise_22_D_6d [Fintype ι] [Nonempty ι] {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    IsIncreasingSWF
        (fun u : ι → ℝ => (1 - c) * mean u + c * Finset.univ.inf' Finset.univ_nonempty u)
      ∧ (∀ u : ι → ℝ, (1 - c) * mean u + c * Finset.univ.inf' Finset.univ_nonempty u =
        form22D1 (fun s => -(c * Finset.univ.inf' Finset.univ_nonempty s)) u) ∧
      ∀ s : ι → ℝ, ∑ i, s i = 0 → 0 ≤ -(c * Finset.univ.inf' Finset.univ_nonempty s) := by
  have hcard : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 Fintype.card_pos
  have hmean_mono : ∀ u u' : ι → ℝ, (∀ i, u i ≤ u' i) → mean u ≤ mean u' := fun u u' h =>
    div_le_div_of_nonneg_right (Finset.sum_le_sum fun i _ => h i) hcard.le
  have hmean_smono : ∀ u u' : ι → ℝ, (∀ i, u i < u' i) → mean u < mean u' := fun u u' h =>
    div_lt_div_of_pos_right (Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _ => h i)
      hcard
  have hinf_mono : ∀ u u' : ι → ℝ, (∀ i, u i ≤ u' i) →
      Finset.univ.inf' Finset.univ_nonempty u ≤ Finset.univ.inf' Finset.univ_nonempty u' :=
    fun u u' h => Finset.le_inf' _ _ fun i hi => (Finset.inf'_le u hi).trans (h i)
  have hinf_smono : ∀ u u' : ι → ℝ, (∀ i, u i < u' i) →
      Finset.univ.inf' Finset.univ_nonempty u < Finset.univ.inf' Finset.univ_nonempty u' := by
    intro u u' h
    obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty u'
    rw [hj]
    exact lt_of_le_of_lt (Finset.inf'_le u (Finset.mem_univ j)) (h j)
  refine ⟨⟨fun u u' h => ?_, fun u u' h => ?_⟩, fun u => ?_, fun s hs => ?_⟩
  · have := hmean_mono u u' h
    have := hinf_mono u u' h
    nlinarith
  · rcases eq_or_lt_of_le hc1 with h1 | h1
    · have := hinf_smono u u' h
      rw [h1]; linarith
    · have := hmean_smono u u' h
      have := hinf_mono u u' (fun i => (h i).le)
      nlinarith
  · have := exercise_22_D_6c u
    simp only [form22D1] at this ⊢
    rw [this]
    ring
  · have hms : Finset.univ.inf' Finset.univ_nonempty s ≤ 0 := by
      by_contra h
      push Not at h
      have : ∀ i, 0 < s i := fun i => lt_of_lt_of_le h (Finset.inf'_le s (Finset.mem_univ i))
      have := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i (_ : i ∈ Finset.univ) =>
        this i
      simp only [Finset.sum_const_zero] at this
      linarith
    nlinarith

/-- **Exercise 22.D.6(e)** (MWG, p. 853). If `g` is homogeneous of degree one on the domain
`H = {s : ∑ sᵢ = 0}` and differentiable at `0` within `H` (derivative `L`), then `g` is linear on
`H`: `g(s) = L(s)` for all `s ∈ H`. Hence (22.D.1) is then the utilitarian case. -/
theorem exercise_22_D_6e [Fintype ι] {g : (ι → ℝ) → ℝ} {L : (ι → ℝ) →L[ℝ] ℝ}
    (hhom : ∀ s : ι → ℝ, ∑ i, s i = 0 → ∀ β : ℝ, 0 < β → g (β • s) = β * g s)
    (hd : HasFDerivWithinAt g L {s | ∑ i, s i = 0} 0) (s : ι → ℝ) (hs : ∑ i, s i = 0) :
    g s = L s := by
  have hg0 : g 0 = 0 := by
    have := hhom 0 (by simp) 2 two_pos
    simp only [smul_zero] at this
    linarith
  -- the line `t ↦ t • s` stays in `H`
  have hline : HasDerivWithinAt (fun t : ℝ => g (t • s)) (L s) (Set.Ioi 0) 0 := by
    have hf : HasDerivWithinAt (fun t : ℝ => t • s) s (Set.Ioi 0) 0 := by
      simpa using
        (HasDerivAt.smul_const (hasDerivAt_id (0 : ℝ)) s).hasDerivWithinAt (s := Set.Ioi 0)
    have := HasFDerivWithinAt.comp_hasDerivWithinAt (x := (0 : ℝ)) (l := g)
      (by simpa using hd) hf (fun t _ => by
        change ∑ i, (t • s) i = 0
        simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, hs, mul_zero])
    simpa [Function.comp_def] using this
  rw [hasDerivWithinAt_iff_tendsto_slope' (by simp)] at hline
  have hconst : ∀ᶠ t in 𝓝[>] (0 : ℝ), slope (fun t : ℝ => g (t • s)) 0 t = g s := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [slope_def_field, hhom s hs t ht]
    simp only [zero_smul, hg0, sub_zero]
    have ht' : t ≠ 0 := (Set.mem_Ioi.1 ht).ne'
    field_simp
  exact (tendsto_nhds_unique (tendsto_const_nhds.congr' (hconst.mono fun _ h => h.symm))
    hline)

end MWG.WelfareBargaining
