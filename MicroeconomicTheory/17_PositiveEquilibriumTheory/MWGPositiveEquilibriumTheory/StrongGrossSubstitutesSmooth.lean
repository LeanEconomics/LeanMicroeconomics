/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPositiveEquilibriumTheory.StrongGrossSubstitutes

/-!
# A `C¹` gross substitute function has the strong gross substitute property
(MWG Exercise 17.F.16(b), p. 647)

Let `g` be continuously differentiable with the gross substitute property on `[0, r]^N`,
`g(0) ≫ 0` and `g(r, …, r) ≪ 0`. Then `g` satisfies SGS (`exercise_17_F_16b`):

* raising the other prices weakly raises `gₖ`, strictly if one of them strictly rises
  (`sgs_chain`, by changing one coordinate at a time along `sgsPath`);
* the own effect `∂gₖ/∂pₖ` is bounded on the compact box by some `M`, so for `α M ≤ 1/2` the map
  `pₖ ↦ αgₖ(p) + pₖ` is strictly increasing (`sgs_own`);
* together these give the strict monotonicity of `αg + id`, and with `g(0) ≫ 0`, `g(r, …, r) ≪ 0`
  they give `αg(p) + p ∈ [0, r]^N`.

`g` is assumed `C¹` on all of `ℝ^N` (a function on the closed box would need a `C¹` extension).
-/

namespace MWG.PositiveEquilibriumTheory

open Filter Topology

variable {N : ℕ}

/-- The path from `p` to `p'` switching the coordinates `0, …, m - 1` to `p'`. -/
def sgsPath (p p' : Fin N → ℝ) (m : ℕ) : Fin N → ℝ := fun i => if (i : ℕ) < m then p' i else p i

theorem sgsPath_zero (p p' : Fin N → ℝ) : sgsPath p p' 0 = p := by
  funext i; simp [sgsPath]

theorem sgsPath_N (p p' : Fin N → ℝ) : sgsPath p p' N = p' := by
  funext i; simp [sgsPath, i.2]

theorem sgsPath_mem {r : ℝ} {p p' : Fin N → ℝ} (hp : p ∈ sgsBox N r) (hp' : p' ∈ sgsBox N r)
    (m : ℕ) : sgsPath p p' m ∈ sgsBox N r :=
  ⟨fun i => by unfold sgsPath; split_ifs; exacts [hp'.1 i, hp.1 i],
    fun i => by unfold sgsPath; split_ifs; exacts [hp'.2 i, hp.2 i]⟩

theorem sgsPath_succ_ne (p p' : Fin N → ℝ) (m : ℕ) (i : Fin N) (hi : (i : ℕ) ≠ m) :
    sgsPath p p' (m + 1) i = sgsPath p p' m i := by
  have : (i : ℕ) < m + 1 ↔ (i : ℕ) < m := by omega
  simp only [sgsPath, this]

/-- Raising the prices of the other goods weakly raises `gₖ`, strictly if one rises strictly. -/
theorem sgs_chain {r : ℝ} {g : (Fin N → ℝ) → Fin N → ℝ} (hGS : BoxGrossSubstitute r g)
    {p p' : Fin N → ℝ} (hp : p ∈ sgsBox N r) (hp' : p' ∈ sgsBox N r) (hle : p ≤ p') {k : Fin N}
    (hk : p k = p' k) :
    g p k ≤ g p' k ∧ ∀ j, j ≠ k → p j < p' j → g p k < g p' k := by
  -- one step of the path
  have heqstep : ∀ m (hm : m < N), p ⟨m, hm⟩ = p' ⟨m, hm⟩ →
      sgsPath p p' (m + 1) = sgsPath p p' m := by
    intro m hm he
    funext i
    by_cases hi : (i : ℕ) = m
    · have : i = ⟨m, hm⟩ := Fin.ext hi
      subst this
      simp [sgsPath, he]
    · exact sgsPath_succ_ne p p' m i hi
  have hstrict : ∀ m (hm : m < N), (⟨m, hm⟩ : Fin N) ≠ k → p ⟨m, hm⟩ < p' ⟨m, hm⟩ →
      g (sgsPath p p' m) k < g (sgsPath p p' (m + 1)) k := by
    intro m hm hjk hlt
    refine hGS _ (sgsPath_mem hp hp' m) _ (sgsPath_mem hp hp' (m + 1)) ⟨m, hm⟩ ?_ ?_ k
      (Ne.symm hjk)
    · simp [sgsPath, hlt]
    · intro i hi
      exact sgsPath_succ_ne p p' m i fun h => hi (Fin.ext h)
  have hstep : ∀ m, g (sgsPath p p' m) k ≤ g (sgsPath p p' (m + 1)) k := by
    intro m
    by_cases hm : m < N
    · by_cases hjk : (⟨m, hm⟩ : Fin N) = k
      · rw [heqstep m hm (by rw [hjk]; exact hk)]
      · rcases (hle ⟨m, hm⟩).lt_or_eq with hlt | he
        · exact (hstrict m hm hjk hlt).le
        · rw [heqstep m hm he]
    · have : sgsPath p p' (m + 1) = sgsPath p p' m := by
        funext i
        have h1 : (i : ℕ) < m := by omega
        have h2 : (i : ℕ) < m + 1 := by omega
        simp [sgsPath, h1, h2]
      rw [this]
  have hmono : Monotone fun m => g (sgsPath p p' m) k := monotone_nat_of_le_succ hstep
  have hend : ∀ m, g p k ≤ g (sgsPath p p' m) k ∧ g (sgsPath p p' m) k ≤ g p' k := fun m => by
    constructor
    · have := hmono (Nat.zero_le m); simpa [sgsPath_zero] using this
    · by_cases hm : m ≤ N
      · have := hmono hm; simpa [sgsPath_N] using this
      · have : sgsPath p p' m = p' := by
          funext i; have : (i : ℕ) < m := by omega
          simp [sgsPath, this]
        rw [this]
  refine ⟨by have := hend 0; rw [sgsPath_zero] at this; exact this.2, fun j hjk hlt => ?_⟩
  have h1 := (hend (j : ℕ)).1
  have h2 := (hend ((j : ℕ) + 1)).2
  have h3 := hstrict (j : ℕ) j.2 hjk hlt
  linarith

/-- The coordinate line `t ↦ p + (t - pₖ)eᵏ` is `Function.update p k`. -/
theorem sgs_update_eq (p : Fin N → ℝ) (k : Fin N) (t : ℝ) :
    Function.update p k t = p + (t - p k) • Pi.single k 1 := by
  funext i
  by_cases h : i = k
  · subst h; simp
  · simp [h]

/-- With `α|∂gₖ/∂pₖ| ≤ 1/2` on the box, `t ↦ αgₖ(p₋ₖ, t) + t` is strictly increasing on
`[0, r]`. -/
theorem sgs_own {r : ℝ} {g : (Fin N → ℝ) → Fin N → ℝ} (hC : ContDiff ℝ 1 g) {α M : ℝ}
    (hα : 0 < α) (hαM : α * M ≤ 1 / 2)
    (hM : ∀ x ∈ sgsBox N r, ∀ k, |fderiv ℝ g x (Pi.single k 1) k| ≤ M) {p : Fin N → ℝ}
    (hp : p ∈ sgsBox N r) (k : Fin N) :
    StrictMonoOn (fun t => α * g (Function.update p k t) k + t) (Set.Icc 0 r) := by
  have hfun : (fun t => α * g (Function.update p k t) k + t) =
      fun t => α * g (p + (t - p k) • Pi.single k 1) k + t := by
    funext t; rw [sgs_update_eq]
  rw [hfun]
  have hline : ∀ t : ℝ, HasDerivAt (fun t : ℝ => p + (t - p k) • Pi.single k (1 : ℝ))
      (Pi.single k 1) t := fun t => by
    have := (((hasDerivAt_id t).sub_const (p k)).smul_const (Pi.single k (1 : ℝ))).const_add p
    simpa using this
  have hdiff : Differentiable ℝ g := hC.differentiable (by norm_num)
  have hderiv : ∀ t, HasDerivAt (fun t => α * g (p + (t - p k) • Pi.single k 1) k + t)
      (α * fderiv ℝ g (p + (t - p k) • Pi.single k 1) (Pi.single k 1) k + 1) t := fun t => by
    have h1 := (hdiff _).hasFDerivAt.comp_hasDerivAt t (hline t)
    exact ((hasDerivAt_pi.1 h1 k).const_mul α).add (hasDerivAt_id t)
  refine strictMonoOn_of_deriv_pos (convex_Icc 0 r)
    (fun t _ => (hderiv t).continuousAt.continuousWithinAt) (fun t ht => ?_)
  rw [interior_Icc] at ht
  rw [(hderiv t).deriv]
  have hmem : p + (t - p k) • Pi.single k 1 ∈ sgsBox N r := by
    rw [← sgs_update_eq]
    refine ⟨fun i => ?_, fun i => ?_⟩
    · by_cases h : i = k
      · subst h; simpa using ht.1.le
      · simpa [Function.update_of_ne h] using hp.1 i
    · by_cases h : i = k
      · subst h; simpa using ht.2.le
      · simpa [Function.update_of_ne h] using hp.2 i
  have hb := hM _ hmem k
  have := neg_abs_le (fderiv ℝ g (p + (t - p k) • Pi.single k 1) (Pi.single k 1) k)
  nlinarith [mul_le_mul_of_nonneg_left hb hα.le]

/-- **Exercise 17.F.16(b)** (MWG, p. 647), second part. If `g` is continuously differentiable and
has the gross substitute property on `[0, r]^N` (with `g(0) ≫ 0`, `g(r, …, r) ≪ 0`), then it has
the strong gross substitute property. -/
theorem exercise_17_F_16b {r : ℝ} (hr : 0 ≤ r) {g : (Fin N → ℝ) → Fin N → ℝ}
    (hC : ContDiff ℝ 1 g) (hGS : BoxGrossSubstitute r g) (h0 : ∀ k, 0 < g 0 k)
    (hrr : ∀ k, g (fun _ => r) k < 0) : StrongGrossSubstitute r g := by
  have hK : IsCompact (Set.Icc (0 : Fin N → ℝ) (fun _ => r)) := isCompact_Icc
  obtain ⟨C, hCb⟩ := hK.exists_bound_of_continuousOn
    (hC.continuous_fderiv (by norm_num)).continuousOn
  have hM : ∀ x ∈ sgsBox N r, ∀ k, |fderiv ℝ g x (Pi.single k 1) k| ≤ |C| := by
    intro x hx k
    have hs : ‖(Pi.single k (1 : ℝ) : Fin N → ℝ)‖ ≤ 1 := by
      refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
      by_cases h : i = k
      · subst h; simp
      · simp [h]
    calc |fderiv ℝ g x (Pi.single k 1) k| = ‖fderiv ℝ g x (Pi.single k 1) k‖ :=
          (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ g x (Pi.single k 1)‖ := norm_le_pi_norm _ k
      _ ≤ ‖fderiv ℝ g x‖ * ‖(Pi.single k (1 : ℝ) : Fin N → ℝ)‖ := (fderiv ℝ g x).le_opNorm _
      _ ≤ |C| * 1 := mul_le_mul ((hCb x hx).trans (le_abs_self C)) hs (norm_nonneg _)
          (abs_nonneg C)
      _ = |C| := mul_one _
  set α := 1 / (2 * (|C| + 1)) with hαdef
  have hα : 0 < α := by positivity
  have hαM : α * |C| ≤ 1 / 2 := by
    rw [hαdef, div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
    linarith [abs_nonneg C]
  have hown := fun p hp k => sgs_own hC hα hαM hM (p := p) hp k
  have hupd : ∀ p ∈ sgsBox N r, ∀ k, ∀ t ∈ Set.Icc 0 r, Function.update p k t ∈ sgsBox N r := by
    intro p hp k t ht
    refine ⟨fun i => ?_, fun i => ?_⟩
    · by_cases h : i = k
      · subst h; simpa using ht.1
      · simpa [Function.update_of_ne h] using hp.1 i
    · by_cases h : i = k
      · subst h; simpa using ht.2
      · simpa [Function.update_of_ne h] using hp.2 i
  have hzero : (0 : Fin N → ℝ) ∈ sgsBox N r := ⟨le_rfl, fun _ => hr⟩
  have hrbox : (fun _ => r : Fin N → ℝ) ∈ sgsBox N r := ⟨fun _ => hr, le_rfl⟩
  refine ⟨α, hα, fun p hp => ⟨fun k => ?_, fun k => ?_⟩, fun p hp p' hp' hle hne k => ?_⟩
  · -- `αgₖ(p) + pₖ ≥ αgₖ(p₋ₖ, 0) ≥ αgₖ(0) > 0`
    have hu := hupd p hp k 0 ⟨le_rfl, hr⟩
    have h1 := (hown p hp k).monotoneOn ⟨le_rfl, hr⟩ ⟨hp.1 k, hp.2 k⟩ (hp.1 k)
    simp only [Function.update_eq_self] at h1
    have h2 := (sgs_chain hGS hzero hu (fun i => hu.1 i) (k := k) (by simp)).1
    have := h0 k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    nlinarith
  · -- `αgₖ(p) + pₖ ≤ αgₖ(p₋ₖ, r) + r ≤ αgₖ(r, …, r) + r < r`
    have hu := hupd p hp k r ⟨hr, le_rfl⟩
    have h1 := (hown p hp k).monotoneOn ⟨hp.1 k, hp.2 k⟩ ⟨hr, le_rfl⟩ (hp.2 k)
    simp only [Function.update_eq_self] at h1
    have h2 := (sgs_chain hGS hu hrbox (fun i => hu.2 i) (k := k) (by simp)).1
    have := hrr k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith
  · set m := Function.update p' k (p k) with hmdef
    have hm : m ∈ sgsBox N r := hupd p' hp' k (p k) ⟨hp.1 k, hp.2 k⟩
    have hpm : p ≤ m := fun i => by
      by_cases h : i = k
      · subst h; simp [m]
      · simpa [m, Function.update_of_ne h] using hle i
    have hmk : p k = m k := by simp [m]
    obtain ⟨hc1, hc2⟩ := sgs_chain hGS hp hm hpm hmk
    have hown' := hown p' hp' k
    have ho : α * g m k + p k ≤ α * g p' k + p' k := by
      have := hown'.monotoneOn ⟨hp.1 k, hp.2 k⟩ ⟨hp'.1 k, hp'.2 k⟩ (hle k)
      simpa [m, Function.update_eq_self] using this
    obtain ⟨j, hj⟩ : ∃ j, p j < p' j := by
      by_contra hcon
      push Not at hcon
      exact hne (funext fun i => le_antisymm (hle i) (hcon i))
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hjk : j = k
    · subst hjk
      have := hown' ⟨hp.1 j, hp.2 j⟩ ⟨hp'.1 j, hp'.2 j⟩ hj
      simp only [Function.update_eq_self] at this
      nlinarith [mul_le_mul_of_nonneg_left hc1 hα.le]
    · have hmj : m j = p' j := by simp [m, Function.update_of_ne hjk]
      have := hc2 j hjk (by rw [hmj]; exact hj)
      nlinarith [mul_lt_mul_of_pos_left this hα]

end MWG.PositiveEquilibriumTheory
