/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Necessity of the Kuhn-Tucker conditions for convex-like programs

MWG, footnote 7 (p. 484) and Section M.K: "the (Kuhn-Tucker) first-order conditions are both
necessary and sufficient" for a convex program. The programs of Chapter 14 are convex in the
manager's utility levels but are posed over compensation schemes, an infinite-dimensional set. The
multipliers nevertheless live in a finite-dimensional space (one per constraint), so the existence
of multipliers follows from separating two convex sets in `ℝ × ℝᵏ` (Mathlib's geometric
Hahn-Banach theorem), with no topology on the set of schemes.

* `kt_convexlike`: a minimization program over an arbitrary set `X` with finitely many inequality
  constraints `G i ≤ 0` that is *convex-like* (for any two points and `t ∈ [0, 1]` some point is at
  least as good as the `t`-mixture in the objective and every constraint) and satisfies Slater's
  condition: at every optimum there are multipliers `λ_i ≥ 0` with complementary slackness such that
  the optimum minimizes the Lagrangian over all of `X`.
* `kt_convexlike_eq`: the same with an additional equality constraint `H = 0` that is affine along
  the mixtures, under the qualification that `H` takes both signs at points satisfying the
  inequality constraints strictly; its multiplier has no sign restriction.
* `kt_sign`, `kt_le`: two elementary facts used for the signs of the multipliers.
-/

namespace MWG.PrincipalAgent

/-- If `c - s a < d` for every `s > 0`, then `a ≥ 0`. -/
theorem kt_sign {a c d : ℝ} (h : ∀ s : ℝ, 0 < s → c - s * a ≤ d) : 0 ≤ a := by
  by_contra ha
  push Not at ha
  have hs : 0 < (|d - c| + 1) / -a := div_pos (by positivity) (by linarith)
  have h1 := h _ hs
  have h2 : (|d - c| + 1) / -a * a = -(|d - c| + 1) := by
    rw [div_mul_eq_mul_div, div_eq_iff (by linarith)]; ring
  rw [h2] at h1
  linarith [le_abs_self (d - c)]

/-- If `c - s a ≤ d` for every `s > 0`, then `c ≤ d`. -/
theorem kt_le {a c d : ℝ} (h : ∀ s : ℝ, 0 < s → c - s * a ≤ d) : c ≤ d := by
  by_contra hcd
  push Not at hcd
  have hs : 0 < (c - d) / (2 * (|a| + 1)) := div_pos (by linarith) (by positivity)
  have h1 := h _ hs
  have h2 : (c - d) / (2 * (|a| + 1)) * a ≤ (c - d) / (2 * (|a| + 1)) * |a| :=
    mul_le_mul_of_nonneg_left (le_abs_self a) hs.le
  have h3 : (c - d) / (2 * (|a| + 1)) * |a| < c - d := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [abs_nonneg a]
  linarith

/-- **Footnote 7 and Section M.K** (MWG, p. 484), abstract form. A program
`min J(x)` over `x ∈ X` subject to `G i x ≤ 0` (finitely many `i`). Suppose it is convex-like
(`hconv`), Slater's condition holds, and `xs` is optimal. Then there are multipliers `λ_i ≥ 0`
with complementary slackness `λ_i G_i(xs) = 0` such that `xs` minimizes the Lagrangian
`J + Σ λ_i G_i` over all of `X`. -/
theorem kt_convexlike {X ι : Type*} [Fintype ι] (J : X → ℝ) (G : ι → X → ℝ) (xs : X)
    (hfeas : ∀ i, G i xs ≤ 0) (hopt : ∀ x, (∀ i, G i x ≤ 0) → J xs ≤ J x)
    (hconv : ∀ x0 x1 : X, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∃ x, J x ≤ (1 - t) * J x0 + t * J x1 ∧
      ∀ i, G i x ≤ (1 - t) * G i x0 + t * G i x1)
    (hslater : ∃ x, ∀ i, G i x < 0) :
    ∃ lam : ι → ℝ, (∀ i, 0 ≤ lam i) ∧ (∀ i, lam i * G i xs = 0) ∧
      ∀ x, J xs ≤ J x + ∑ i, lam i * G i x := by
  classical
  let S : Set (ℝ × (ι → ℝ)) := {y | ∃ x, J x ≤ y.1 ∧ ∀ i, G i x ≤ y.2 i}
  let T : Set (ℝ × (ι → ℝ)) := {y | y.1 < J xs} ∩ ⋂ i, {y | y.2 i < 0}
  have hTo : IsOpen T := by
    refine (isOpen_lt continuous_fst continuous_const).inter (isOpen_iInter_of_finite fun i => ?_)
    exact isOpen_lt ((continuous_apply i).comp continuous_snd) continuous_const
  have hTc : Convex ℝ T := by
    intro y hy z hz a b ha hb hab
    simp only [T, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iInter] at hy hz ⊢
    refine ⟨?_, fun i => ?_⟩
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      have hm := lt_min (sub_pos.2 hy.1) (sub_pos.2 hz.1)
      have h1 := mul_le_mul_of_nonneg_left (min_le_left (J xs - y.1) (J xs - z.1)) ha
      have h2 := mul_le_mul_of_nonneg_left (min_le_right (J xs - y.1) (J xs - z.1)) hb
      have h3 : a * min (J xs - y.1) (J xs - z.1) + b * min (J xs - y.1) (J xs - z.1) =
          min (J xs - y.1) (J xs - z.1) := by rw [← add_mul, hab, one_mul]
      have h4 : a * y.1 + b * z.1 = J xs - (a * (J xs - y.1) + b * (J xs - z.1)) := by
        linear_combination J xs * hab
      rw [h4]; linarith
    · simp only [Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have hm := lt_min (neg_pos.2 (hy.2 i)) (neg_pos.2 (hz.2 i))
      have h1 := mul_le_mul_of_nonneg_left (min_le_left (-y.2 i) (-z.2 i)) ha
      have h2 := mul_le_mul_of_nonneg_left (min_le_right (-y.2 i) (-z.2 i)) hb
      have h3 : a * min (-y.2 i) (-z.2 i) + b * min (-y.2 i) (-z.2 i) =
          min (-y.2 i) (-z.2 i) := by rw [← add_mul, hab, one_mul]
      have h4 : a * y.2 i + b * z.2 i = -(a * -y.2 i + b * -z.2 i) := by ring
      rw [h4]; linarith
  have hSc : Convex ℝ S := by
    intro y hy z hz a b ha hb hab
    obtain ⟨x0, h0J, h0G⟩ := hy
    obtain ⟨x1, h1J, h1G⟩ := hz
    obtain ⟨x, hxJ, hxG⟩ := hconv x0 x1 b hb (by linarith)
    have ha' : 1 - b = a := by linarith
    rw [ha'] at hxJ hxG
    refine ⟨x, ?_, fun i => ?_⟩
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      nlinarith [mul_le_mul_of_nonneg_left h0J ha, mul_le_mul_of_nonneg_left h1J hb]
    · simp only [Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      nlinarith [mul_le_mul_of_nonneg_left (h0G i) ha, mul_le_mul_of_nonneg_left (h1G i) hb,
        hxG i]
  have hdisj : Disjoint T S := by
    rw [Set.disjoint_left]
    rintro y ⟨hy1, hy2⟩ ⟨x, hxJ, hxG⟩
    simp only [Set.mem_ofPred_eq, Set.mem_iInter] at hy1 hy2
    have := hopt x fun i => ((hxG i).trans (hy2 i).le)
    linarith
  obtain ⟨f, u, hfT, hfS⟩ := geometric_hahn_banach_open hTc hTo hSc hdisj
  -- coordinates of `f`
  let e0 : ℝ × (ι → ℝ) := ((1 : ℝ), (0 : ι → ℝ))
  let ek : ι → ℝ × (ι → ℝ) := fun k => ((0 : ℝ), (Pi.single k (1 : ℝ) : ι → ℝ))
  have hdec : ∀ y : ℝ × (ι → ℝ), f y = y.1 * f e0 + ∑ i, y.2 i * f (ek i) := by
    intro y
    have : y = y.1 • e0 + ∑ i, y.2 i • ek i := by
      refine Prod.ext ?_ ?_
      · simp [e0, ek, Prod.fst_sum]
      · funext j
        simp [e0, ek, Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [this]
    simp [map_sum, smul_eq_mul]
  set a0 := f e0
  let p : ℝ × (ι → ℝ) := (J xs, 0)
  have hpS : p ∈ S := ⟨xs, le_rfl, hfeas⟩
  have hfp : f p = J xs * a0 := by rw [hdec]; simp [p]
  have hup : u ≤ J xs * a0 := hfp ▸ hfS p hpS
  let base : ℝ × (ι → ℝ) := (J xs - 1, fun _ => -1)
  have hmemT : ∀ y : ℝ × (ι → ℝ), y.1 < J xs → (∀ i, y.2 i < 0) → y ∈ T := by
    intro y h1 h2
    simp only [T, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iInter]
    exact ⟨h1, h2⟩
  have ha0 : 0 ≤ a0 := by
    refine kt_sign (c := f base) (d := J xs * a0) fun s hs => ?_
    have hm : base - s • e0 ∈ T := hmemT _ (by simp [base, e0]; linarith)
      (fun i => by simp [base, e0])
    have := hfT _ hm
    rw [map_sub, map_smul, smul_eq_mul] at this
    linarith
  have hak : ∀ k, 0 ≤ f (ek k) := by
    intro k
    refine kt_sign (c := f base) (d := J xs * a0) fun s hs => ?_
    have hm : base - s • ek k ∈ T := hmemT _ (by simp [base, ek]) (fun i => by
      simp only [base, ek, Prod.snd_sub, Prod.smul_snd, Pi.sub_apply, Pi.smul_apply,
        smul_eq_mul]
      by_cases hik : i = k
      · subst hik; simp; linarith
      · simp [hik])
    have := hfT _ hm
    rw [map_sub, map_smul, smul_eq_mul] at this
    linarith
  have hu : J xs * a0 ≤ u := by
    refine kt_le (a := f (e0 + ∑ i, ek i)) fun s hs => ?_
    have hm : p - s • (e0 + ∑ i, ek i) ∈ T := hmemT _ (by simp [p, e0, ek, Prod.fst_sum]; linarith)
      (fun i => by simp [p, e0, ek, Prod.snd_sum, Finset.sum_apply, Pi.single_apply]; linarith)
    have := hfT _ hm
    rw [map_sub, map_smul, smul_eq_mul, hfp] at this
    exact this.le
  -- the Lagrangian inequality with `a0` on the objective
  have hlag : ∀ x, J xs * a0 ≤ J x * a0 + ∑ i, G i x * f (ek i) := by
    intro x
    have := hfS (J x, fun i => G i x) ⟨x, le_rfl, fun i => le_rfl⟩
    rw [hdec] at this
    exact hu.trans this
  -- complementary slackness
  have hcs : ∀ i, G i xs * f (ek i) = 0 := by
    have h1 := hlag xs
    have hnp : ∀ i ∈ Finset.univ, G i xs * f (ek i) ≤ 0 :=
      fun i _ => mul_nonpos_of_nonpos_of_nonneg (hfeas i) (hak i)
    have h2 : ∑ i, G i xs * f (ek i) = 0 :=
      le_antisymm (Finset.sum_nonpos hnp) (by linarith)
    intro i
    exact (Finset.sum_eq_zero_iff_of_nonpos hnp).1 h2 i (Finset.mem_univ i)
  -- Slater gives `a0 > 0`
  have ha0pos : 0 < a0 := by
    rcases ha0.lt_or_eq with h | h
    · exact h
    exfalso
    obtain ⟨xt, hxt⟩ := hslater
    have h1 := hlag xt
    rw [← h] at h1
    simp only [mul_zero, zero_add] at h1
    have hnp : ∀ i ∈ Finset.univ, G i xt * f (ek i) ≤ 0 :=
      fun i _ => mul_nonpos_of_nonpos_of_nonneg (hxt i).le (hak i)
    have h2 := (Finset.sum_eq_zero_iff_of_nonpos hnp).1
      (le_antisymm (Finset.sum_nonpos hnp) h1)
    have hz : ∀ i, f (ek i) = 0 := fun i => by
      have := h2 i (Finset.mem_univ i)
      rcases mul_eq_zero.1 this with h' | h'
      · exact absurd h' (hxt i).ne
      · exact h'
    have hf0 : ∀ y, f y = 0 := fun y => by rw [hdec, ← h]; simp [hz]
    have hbT : base ∈ T := hmemT _ (by simp [base]) (fun i => by simp [base])
    have := hfT _ hbT
    have := hfS p hpS
    rw [hf0] at *
    linarith
  refine ⟨fun i => f (ek i) / a0, fun i => div_nonneg (hak i) ha0, fun i => ?_, fun x => ?_⟩
  · rw [div_mul_eq_mul_div, mul_comm, hcs i, zero_div]
  · have h1 := hlag x
    have : ∑ i, f (ek i) / a0 * G i x = (∑ i, G i x * f (ek i)) / a0 := by
      rw [div_eq_mul_inv, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [this]
    have h2 : J xs * a0 ≤ (J x + (∑ i, G i x * f (ek i)) / a0) * a0 := by
      rw [add_mul, div_mul_cancel₀ _ ha0pos.ne']; linarith
    exact le_of_mul_le_mul_right h2 ha0pos

/-- **(14.AA.2)-(14.AA.3)** (MWG, p. 504), abstract form: a convex-like program with inequality
constraints `G i ≤ 0` and one equality constraint `H = 0` that is affine along the mixtures. If
there are points `xp`, `xm` satisfying every inequality constraint strictly with
`H(xp) > 0 > H(xm)`, then at every optimum `xs` there are multipliers `λ_i ≥ 0` (with
complementary slackness) and `ν` (of either sign) such that `xs` minimizes
`J + Σ λ_i G_i + ν H` over all of `X`. -/
theorem kt_convexlike_eq {X ι : Type*} [Fintype ι] (J : X → ℝ) (G : ι → X → ℝ) (H : X → ℝ)
    (xs : X) (hfeas : ∀ i, G i xs ≤ 0) (hHs : H xs = 0)
    (hopt : ∀ x, (∀ i, G i x ≤ 0) → H x = 0 → J xs ≤ J x)
    (hconv : ∀ x0 x1 : X, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∃ x, J x ≤ (1 - t) * J x0 + t * J x1 ∧
      (∀ i, G i x ≤ (1 - t) * G i x0 + t * G i x1) ∧ H x = (1 - t) * H x0 + t * H x1)
    {xp xm : X} (hGp : ∀ i, G i xp < 0) (hGm : ∀ i, G i xm < 0) (hHp : 0 < H xp)
    (hHm : H xm < 0) :
    ∃ (lam : ι → ℝ) (ν : ℝ), (∀ i, 0 ≤ lam i) ∧ (∀ i, lam i * G i xs = 0) ∧
      ∀ x, J xs ≤ J x + ∑ i, lam i * G i x + ν * H x := by
  classical
  let S : Set (ℝ × (ι → ℝ) × ℝ) := {y | ∃ x, J x ≤ y.1 ∧ (∀ i, G i x ≤ y.2.1 i) ∧ H x = y.2.2}
  let T : Set (ℝ × (ι → ℝ) × ℝ) := {y | y.1 < J xs ∧ (∀ i, y.2.1 i < 0) ∧ y.2.2 = 0}
  -- mixing `xm` and `xp` to hit a prescribed value of `H`
  have hmix : ∀ z, H xm ≤ z → z ≤ H xp → ∃ x, J x ≤ max (J xm) (J xp) ∧
      (∀ i, G i x ≤ max (G i xm) (G i xp)) ∧ H x = z := by
    intro z hz1 hz2
    have hd : 0 < H xp - H xm := by linarith
    set t := (z - H xm) / (H xp - H xm)
    have ht0 : 0 ≤ t := div_nonneg (by linarith) hd.le
    have ht1 : t ≤ 1 := (div_le_one hd).2 (by linarith)
    obtain ⟨x, hJ, hG, hH⟩ := hconv xm xp t ht0 ht1
    refine ⟨x, ?_, fun i => ?_, ?_⟩
    · have := mul_le_mul_of_nonneg_left (le_max_left (J xm) (J xp)) (by linarith : 0 ≤ 1 - t)
      have := mul_le_mul_of_nonneg_left (le_max_right (J xm) (J xp)) ht0
      nlinarith
    · have := mul_le_mul_of_nonneg_left (le_max_left (G i xm) (G i xp))
        (by linarith : 0 ≤ 1 - t)
      have := mul_le_mul_of_nonneg_left (le_max_right (G i xm) (G i xp)) ht0
      nlinarith [hG i]
    · rw [hH]
      simp only [t]
      field_simp
      ring
  have hSc : Convex ℝ S := by
    intro y hy z hz a b ha hb hab
    obtain ⟨x0, h0J, h0G, h0H⟩ := hy
    obtain ⟨x1, h1J, h1G, h1H⟩ := hz
    obtain ⟨x, hxJ, hxG, hxH⟩ := hconv x0 x1 b hb (by linarith)
    have ha' : 1 - b = a := by linarith
    rw [ha'] at hxJ hxG hxH
    refine ⟨x, ?_, fun i => ?_, ?_⟩
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      nlinarith [mul_le_mul_of_nonneg_left h0J ha, mul_le_mul_of_nonneg_left h1J hb]
    · simp only [Prod.snd_add, Prod.smul_snd, Prod.fst_add, Prod.smul_fst, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul]
      nlinarith [mul_le_mul_of_nonneg_left (h0G i) ha, mul_le_mul_of_nonneg_left (h1G i) hb,
        hxG i]
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      rw [hxH, h0H, h1H]
  have hTc : Convex ℝ T := by
    intro y hy z hz a b ha hb hab
    obtain ⟨hy1, hy2, hy3⟩ := hy
    obtain ⟨hz1, hz2, hz3⟩ := hz
    refine ⟨?_, fun i => ?_, ?_⟩
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      have hm := lt_min (sub_pos.2 hy1) (sub_pos.2 hz1)
      have h1 := mul_le_mul_of_nonneg_left (min_le_left (J xs - y.1) (J xs - z.1)) ha
      have h2 := mul_le_mul_of_nonneg_left (min_le_right (J xs - y.1) (J xs - z.1)) hb
      have h3 : a * min (J xs - y.1) (J xs - z.1) + b * min (J xs - y.1) (J xs - z.1) =
          min (J xs - y.1) (J xs - z.1) := by rw [← add_mul, hab, one_mul]
      have h4 : a * y.1 + b * z.1 = J xs - (a * (J xs - y.1) + b * (J xs - z.1)) := by
        linear_combination J xs * hab
      rw [h4]; linarith
    · simp only [Prod.snd_add, Prod.smul_snd, Prod.fst_add, Prod.smul_fst, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul]
      have hm := lt_min (neg_pos.2 (hy2 i)) (neg_pos.2 (hz2 i))
      have h1 := mul_le_mul_of_nonneg_left (min_le_left (-y.2.1 i) (-z.2.1 i)) ha
      have h2 := mul_le_mul_of_nonneg_left (min_le_right (-y.2.1 i) (-z.2.1 i)) hb
      have h3 : a * min (-y.2.1 i) (-z.2.1 i) + b * min (-y.2.1 i) (-z.2.1 i) =
          min (-y.2.1 i) (-z.2.1 i) := by rw [← add_mul, hab, one_mul]
      have h4 : a * y.2.1 i + b * z.2.1 i = -(a * -y.2.1 i + b * -z.2.1 i) := by ring
      rw [h4]; linarith
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      rw [hy3, hz3]; ring
  -- an open box inside `S`
  let B : Set (ℝ × (ι → ℝ) × ℝ) := {y | max (J xm) (J xp) < y.1} ∩
    (⋂ i, {y | max (G i xm) (G i xp) < y.2.1 i}) ∩ ({y | H xm < y.2.2} ∩ {y | y.2.2 < H xp})
  have hBo : IsOpen B := by
    refine ((isOpen_lt continuous_const continuous_fst).inter
      (isOpen_iInter_of_finite fun i => ?_)).inter
      ((isOpen_lt continuous_const (continuous_snd.comp continuous_snd)).inter
        (isOpen_lt (continuous_snd.comp continuous_snd) continuous_const))
    exact isOpen_lt continuous_const
      ((continuous_apply i).comp (continuous_fst.comp continuous_snd))
  have hBS : B ⊆ S := by
    rintro y ⟨⟨h1, h2⟩, h3, h4⟩
    simp only [Set.mem_ofPred_eq, Set.mem_iInter] at h1 h2 h3 h4
    obtain ⟨x, hJ, hG, hH⟩ := hmix y.2.2 h3.le h4.le
    exact ⟨x, hJ.trans h1.le, fun i => (hG i).trans (h2 i).le, hH⟩
  have hint : (interior S).Nonempty := by
    refine ⟨(max (J xm) (J xp) + 1, fun i => max (G i xm) (G i xp) + 1, 0),
      interior_maximal hBS hBo ?_⟩
    simp only [B, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iInter]
    exact ⟨⟨by linarith, fun i => by linarith⟩, hHm, hHp⟩
  have hdisj : Disjoint (interior S) T := by
    rw [Set.disjoint_left]
    rintro y hyS ⟨hy1, hy2, hy3⟩
    obtain ⟨x, hxJ, hxG, hxH⟩ := interior_subset hyS
    have := hopt x (fun i => (hxG i).trans (hy2 i).le) (hxH.trans hy3)
    linarith
  have hTne : T.Nonempty := ⟨(J xs - 1, fun _ => -1, 0), by
    refine ⟨by simp, fun i => by simp, rfl⟩⟩
  obtain ⟨f0, u0, hf0ne, hfS0, hfT0⟩ :=
    geometric_hahn_banach_of_nonempty_interior hSc hTc hdisj hint hTne
  set f := -f0
  set u := -u0
  have hfS : ∀ y ∈ S, u ≤ f y := fun y hy => by
    have := hfS0 y hy
    change -u0 ≤ -(f0 y)
    linarith
  have hfT : ∀ y ∈ T, f y ≤ u := fun y hy => by
    have := hfT0 y hy
    change -(f0 y) ≤ -u0
    linarith
  let e0 : ℝ × (ι → ℝ) × ℝ := ((1 : ℝ), (0 : ι → ℝ), (0 : ℝ))
  let ek : ι → ℝ × (ι → ℝ) × ℝ := fun k => ((0 : ℝ), (Pi.single k (1 : ℝ) : ι → ℝ), (0 : ℝ))
  let eH : ℝ × (ι → ℝ) × ℝ := ((0 : ℝ), (0 : ι → ℝ), (1 : ℝ))
  have hdec : ∀ y : ℝ × (ι → ℝ) × ℝ,
      f y = y.1 * f e0 + ∑ i, y.2.1 i * f (ek i) + y.2.2 * f eH := by
    intro y
    have : y = y.1 • e0 + ∑ i, y.2.1 i • ek i + y.2.2 • eH := by
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · simp [e0, ek, eH, Prod.fst_sum]
      · funext j
        simp [e0, ek, eH, Prod.snd_sum, Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
      · simp [e0, ek, eH, Prod.snd_sum]
    conv_lhs => rw [this]
    simp [map_sum, smul_eq_mul]
  set a0 := f e0
  set b := f eH
  let p : ℝ × (ι → ℝ) × ℝ := (J xs, 0, 0)
  have hpS : p ∈ S := ⟨xs, le_rfl, hfeas, hHs⟩
  have hfp : f p = J xs * a0 := by rw [hdec]; simp [p]
  have hup : u ≤ J xs * a0 := hfp ▸ hfS p hpS
  let base : ℝ × (ι → ℝ) × ℝ := (J xs - 1, fun _ => -1, 0)
  have ha0 : 0 ≤ a0 := by
    refine kt_sign (c := f base) (d := J xs * a0) fun s hs => ?_
    have hm : base - s • e0 ∈ T := ⟨by simp [base, e0]; linarith, fun i => by simp [base, e0],
      by simp [base, e0]⟩
    have := hfT _ hm
    rw [map_sub, map_smul, smul_eq_mul] at this
    linarith
  have hak : ∀ k, 0 ≤ f (ek k) := by
    intro k
    refine kt_sign (c := f base) (d := J xs * a0) fun s hs => ?_
    have hm : base - s • ek k ∈ T := ⟨by simp [base, ek], fun i => by
      simp only [base, ek, Prod.snd_sub, Prod.fst_sub, Prod.smul_snd, Prod.smul_fst,
        Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      by_cases hik : i = k
      · subst hik; simp; linarith
      · simp [hik], by simp [base, ek]⟩
    have := hfT _ hm
    rw [map_sub, map_smul, smul_eq_mul] at this
    linarith
  have hu : J xs * a0 ≤ u := by
    refine kt_le (a := f (e0 + ∑ i, ek i)) fun s hs => ?_
    have hm : p - s • (e0 + ∑ i, ek i) ∈ T := ⟨by simp [p, e0, ek, Prod.fst_sum]; linarith,
      fun i => by
        simp [p, e0, ek, Prod.snd_sum, Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
        linarith,
      by simp [p, e0, ek, Prod.snd_sum]⟩
    have := hfT _ hm
    rw [map_sub, map_smul, smul_eq_mul, hfp] at this
    exact this
  have hlag : ∀ x, J xs * a0 ≤ J x * a0 + ∑ i, G i x * f (ek i) + H x * b := by
    intro x
    have := hfS (J x, fun i => G i x, H x) ⟨x, le_rfl, fun i => le_rfl, rfl⟩
    rw [hdec] at this
    exact hu.trans this
  have hcs : ∀ i, G i xs * f (ek i) = 0 := by
    have h1 := hlag xs
    rw [hHs, zero_mul, add_zero] at h1
    have hnp : ∀ i ∈ Finset.univ, G i xs * f (ek i) ≤ 0 :=
      fun i _ => mul_nonpos_of_nonpos_of_nonneg (hfeas i) (hak i)
    have h2 : ∑ i, G i xs * f (ek i) = 0 :=
      le_antisymm (Finset.sum_nonpos hnp) (by linarith)
    intro i
    exact (Finset.sum_eq_zero_iff_of_nonpos hnp).1 h2 i (Finset.mem_univ i)
  have ha0pos : 0 < a0 := by
    rcases ha0.lt_or_eq with h | h
    · exact h
    exfalso
    -- a point with `H = 0` satisfying the inequality constraints strictly
    obtain ⟨x0, -, hG0, hH0⟩ := hmix 0 hHm.le hHp.le
    have h1 := hlag x0
    rw [← h, hH0] at h1
    simp only [mul_zero, zero_add, zero_mul, add_zero] at h1
    have hG0' : ∀ i, G i x0 < 0 := fun i => (hG0 i).trans_lt (max_lt (hGm i) (hGp i))
    have hnp : ∀ i ∈ Finset.univ, G i x0 * f (ek i) ≤ 0 :=
      fun i _ => mul_nonpos_of_nonpos_of_nonneg (hG0' i).le (hak i)
    have h2 := (Finset.sum_eq_zero_iff_of_nonpos hnp).1
      (le_antisymm (Finset.sum_nonpos hnp) h1)
    have hz : ∀ i, f (ek i) = 0 := fun i => by
      have := h2 i (Finset.mem_univ i)
      rcases mul_eq_zero.1 this with h' | h'
      · exact absurd h' (hG0' i).ne
      · exact h'
    have hb0 : b = 0 := by
      have hp := hlag xp
      have hm := hlag xm
      rw [← h] at hp hm
      simp only [mul_zero, hz, Finset.sum_const_zero, zero_add] at hp hm
      nlinarith
    have hf0 : f = 0 := by
      refine ContinuousLinearMap.ext fun y => ?_
      rw [hdec, ← h, hb0]
      simp [hz]
    exact hf0ne (neg_eq_zero.1 hf0)
  refine ⟨fun i => f (ek i) / a0, b / a0, fun i => div_nonneg (hak i) ha0, fun i => ?_,
    fun x => ?_⟩
  · rw [div_mul_eq_mul_div, mul_comm, hcs i, zero_div]
  · have h1 := hlag x
    have : ∑ i, f (ek i) / a0 * G i x = (∑ i, G i x * f (ek i)) / a0 := by
      rw [div_eq_mul_inv, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [this]
    have h2 : J xs * a0 ≤ (J x + (∑ i, G i x * f (ek i)) / a0 + b / a0 * H x) * a0 := by
      rw [add_mul, add_mul, div_mul_cancel₀ _ ha0pos.ne', div_mul_eq_mul_div,
        div_mul_cancel₀ _ ha0pos.ne']
      linarith
    exact le_of_mul_le_mul_right h2 ha0pos

end MWG.PrincipalAgent
