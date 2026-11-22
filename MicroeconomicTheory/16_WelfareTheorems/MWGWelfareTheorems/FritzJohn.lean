/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGWelfareTheorems.Appendix
import MWGClassicalDemand.AppendixMK

/-!
# The Fritz John conditions (tool for MWG Section 16.F)

Section 16.F appeals to the Kuhn-Tucker conditions of Section M.K for problem (16.F.1), whose
constraint qualification (footnote 18) is not of the linear-independence form proved in
Chapter 3 (`theorem_M_K_2`): at a solution with `x₁ = 0` the binding constraint gradients can be
dependent. We prove the Fritz John conditions for inequality-constrained problems on any real
normed space, assuming only differentiability at the solution: at a local maximizer `z` of `f` on
`{v : gₖ(v) ≤ 0 ∀ k}` there are `λ₀ ≥ 0`, `λₖ ≥ 0`, not all zero, with `λₖ gₖ(z) = 0` and
`λ₀ Df(z) = ∑ₖ λₖ Dgₖ(z)`. The proof: no direction strictly improves `f` while strictly decreasing
every binding constraint, and Gordan's alternative (separation of the open positive orthant from
the range of the derivative map, Mathlib's geometric Hahn-Banach theorem) gives the multipliers.
Section 16.F's normalization `δ₁ = 1` is derived in `FirstOrder` from the strictly positive
gradients.
-/

namespace MWG.WelfareTheorems

open Filter Topology

/-- No direction `d` strictly raises `f` and strictly lowers every binding constraint at a local
constrained maximizer (all functions differentiable at `z`). -/
theorem no_improving_direction {V K : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [Finite K] {f : V → ℝ} {g : K → V → ℝ} {f' : V →L[ℝ] ℝ} {g' : K → V →L[ℝ] ℝ} {z : V}
    (hz : ∀ k, g k z ≤ 0) (hmax : IsLocalMaxOn f {v | ∀ k, g k v ≤ 0} z)
    (hf : HasFDerivAt f f' z) (hg : ∀ k, HasFDerivAt (g k) (g' k) z) (d : V)
    (hfd : 0 < f' d) (hgd : ∀ k, g k z = 0 → g' k d < 0) : False := by
  have hline : ∀ {φ : V → ℝ} {φ' : V →L[ℝ] ℝ}, HasFDerivAt φ φ' z →
      HasDerivAt (fun t : ℝ => φ (z + t • d)) (φ' d) 0 := by
    intro φ φ' hφ
    have h1 : HasDerivAt (fun t : ℝ => z + t • d) d 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const d).const_add z
    have h2 : HasFDerivAt φ φ' (z + (0 : ℝ) • d) := by simpa using hφ
    exact h2.comp_hasDerivAt 0 h1
  -- `f` increases along `d`
  have hup : ∀ᶠ t in 𝓝[>] (0 : ℝ), f z < f (z + t • d) := by
    have := MWG.ClassicalDemand.mk_eventually_gt_of_deriv_pos (hline hf) hfd
    simpa using this
  -- every constraint stays satisfied along `d`
  have hfeas : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ k, g k (z + t • d) ≤ 0 := by
    rw [eventually_all]
    intro k
    rcases (hz k).lt_or_eq with hk | hk
    · have hc : ContinuousAt (fun t : ℝ => g k (z + t • d)) 0 := (hline (hg k)).continuousAt
      have := hc.eventually (gt_mem_nhds (show g k (z + (0 : ℝ) • d) < 0 by simpa using hk))
      exact (eventually_nhdsWithin_of_eventually_nhds this).mono fun t ht => ht.le
    · have hneg : HasDerivAt (fun t : ℝ => -g k (z + t • d)) (-(g' k d)) 0 :=
        (hline (hg k)).neg
      have := MWG.ClassicalDemand.mk_eventually_gt_of_deriv_pos hneg
        (by linarith [hgd k hk])
      refine this.mono fun t ht => ?_
      simp only [zero_smul, add_zero, hk, neg_zero] at ht
      linarith
  -- the path tends to `z` within the constraint set
  have htend : Tendsto (fun t : ℝ => z + t • d) (𝓝[>] 0) (𝓝[{v | ∀ k, g k v ≤ 0}] z) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, hfeas⟩
    have : Continuous fun t : ℝ => z + t • d := by fun_prop
    have h0 := (this.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simpa using h0
  have hle := htend.eventually hmax
  obtain ⟨t, ht1, ht2⟩ := (hup.and hle).exists
  linarith

/-- **The Fritz John conditions.** If `z` is a local maximizer of `f` on `{v : gₖ(v) ≤ 0 ∀ k}`
(finitely many constraints) and `f`, `gₖ` are differentiable at `z`, there are `λ₀ ≥ 0` and
`λₖ ≥ 0`, not all zero, with complementary slackness `λₖ gₖ(z) = 0` and
`λ₀ Df(z) = ∑ₖ λₖ Dgₖ(z)`. -/
theorem fritz_john {V K : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype K]
    {f : V → ℝ} {g : K → V → ℝ} {f' : V →L[ℝ] ℝ} {g' : K → V →L[ℝ] ℝ} {z : V}
    (hz : ∀ k, g k z ≤ 0) (hmax : IsLocalMaxOn f {v | ∀ k, g k v ≤ 0} z)
    (hf : HasFDerivAt f f' z) (hg : ∀ k, HasFDerivAt (g k) (g' k) z) :
    ∃ (l0 : ℝ) (l : K → ℝ), 0 ≤ l0 ∧ (∀ k, 0 ≤ l k) ∧ (l0 ≠ 0 ∨ ∃ k, l k ≠ 0) ∧
      (∀ k, l k * g k z = 0) ∧ l0 • f' = ∑ k, l k • g' k := by
  classical
  -- the derivative map into `ℝ^{1 + A}`, `A` the binding constraints
  set A := {k // g k z = 0}
  set T : V →L[ℝ] (Option A → ℝ) := ContinuousLinearMap.pi fun o => match o with
    | none => f'
    | some k => -g' k.1 with hT
  have hTnone : ∀ d, T d none = f' d := fun d => rfl
  have hTsome : ∀ d (k : A), T d (some k) = -g' k.1 d := fun d k => rfl
  set P : Set (Option A → ℝ) := {w | ∀ o, 0 < w o} with hP
  have hPopen : IsOpen P := by
    have : P = ⋂ o, {w : Option A → ℝ | 0 < w o} := by ext w; simp [hP]
    rw [this]
    exact isOpen_iInter_of_finite fun o => isOpen_lt continuous_const (continuous_apply o)
  have hPconv : Convex ℝ P := by
    intro x hx y hy a b ha hb hab o
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases ha.lt_or_eq with ha' | ha'
    · nlinarith [mul_pos ha' (hx o), mul_nonneg hb (hy o).le]
    · subst ha'
      have hb1 : b = 1 := by linarith
      subst hb1
      simpa using hy o
  have hdisj : Disjoint P (Set.range T) := by
    rw [Set.disjoint_left]
    rintro w hw ⟨d, rfl⟩
    refine no_improving_direction hz hmax hf hg d (by simpa [hTnone] using hw none)
      fun k hk => ?_
    have := hw (some ⟨k, hk⟩)
    rw [hTsome] at this
    change 0 < -(g' k d) at this
    linarith
  have hconvR : Convex ℝ (Set.range T) := by
    have := (convex_univ : Convex ℝ (Set.univ : Set V)).linear_image T.toLinearMap
    simpa [Set.image_univ] using this
  obtain ⟨φ, u, hφP, hφR⟩ := geometric_hahn_banach_open hPconv hPopen hconvR hdisj
  set c : Option A → ℝ := fun o => φ (Pi.single o 1) with hc
  have hφ : ∀ w, φ w = ∑ o, c o * w o := fun w => strongDual_apply_eq_sum φ w
  -- `φ` vanishes on the range of `T`, and `u ≤ 0`
  have hφT : ∀ d, φ (T d) = 0 := by
    intro d
    by_contra hne
    set s := φ (T d) with hs
    have h1 := hφR (T (((u - 1) / s) • d)) ⟨_, rfl⟩
    rw [map_smul, map_smul, smul_eq_mul, ← hs, div_mul_cancel₀ _ hne] at h1
    linarith
  -- `c ≤ 0` and `c ≠ 0`
  have hc_nonpos : ∀ o, c o ≤ 0 := by
    intro o
    by_contra hpos
    push Not at hpos
    set S := ∑ o', |c o'| with hS
    set t := (S + 1) / c o + 1 with ht
    have ht0 : 0 < t := by positivity
    set w : Option A → ℝ := fun o' => if o' = o then t else 1 with hw
    have hwP : w ∈ P := fun o' => by simp only [hw]; split_ifs <;> linarith
    have h1 := hφP w hwP
    rw [hφ] at h1
    have h2 : ∑ o', c o' * w o' = c o * t + ∑ o' ∈ Finset.univ.erase o, c o' := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ o)]
      congr 1
      · simp [hw]
      · exact Finset.sum_congr rfl fun o' ho' => by
          simp [hw, Finset.ne_of_mem_erase ho']
    have h3 : -S ≤ ∑ o' ∈ Finset.univ.erase o, c o' := by
      rw [hS, ← Finset.add_sum_erase _ _ (Finset.mem_univ o)]
      have : -(∑ o' ∈ Finset.univ.erase o, |c o'|) ≤ ∑ o' ∈ Finset.univ.erase o, c o' := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_le_sum fun o' _ => neg_abs_le _
      linarith [abs_nonneg (c o)]
    have h4 : c o * t = S + 1 + c o := by rw [ht]; field_simp
    have hu0 : u ≤ 0 := by simpa using hφR 0 ⟨0, map_zero T⟩
    rw [h2] at h1
    linarith
  have hc_ne : ∃ o, c o ≠ 0 := by
    by_contra hall
    push Not at hall
    have := hφP (fun _ => 1) (fun _ => one_pos)
    have hu0 : u ≤ 0 := by simpa using hφR 0 ⟨0, map_zero T⟩
    rw [hφ] at this
    simp [hall] at this
    linarith
  set l : K → ℝ := fun k => if h : g k z = 0 then -c (some ⟨k, h⟩) else 0 with hl
  refine ⟨-c none, l, by linarith [hc_nonpos none], fun k => ?_, ?_, fun k => ?_, ?_⟩
  · simp only [hl]
    split_ifs with h
    · linarith [hc_nonpos (some ⟨k, h⟩)]
    · exact le_rfl
  · obtain ⟨o, ho⟩ := hc_ne
    cases o with
    | none => exact Or.inl (neg_ne_zero.mpr ho)
    | some k =>
      right
      refine ⟨k.1, ?_⟩
      simp only [hl, k.2, ↓reduceDIte]
      exact neg_ne_zero.mpr ho
  · simp only [hl]
    split_ifs with h
    · rw [h, mul_zero]
    · rw [zero_mul]
  · -- the multiplier identity from `φ ∘ T = 0`
    ext d
    have h1 := hφT d
    rw [hφ, Fintype.sum_option, hTnone] at h1
    change -c none * f' d = (∑ k, l k • g' k) d
    rw [sum_apply]
    simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
    have h2 : ∑ k, l k * g' k d = ∑ k : A, -c (some k) * g' k.1 d := by
      rw [← Fintype.sum_subtype_add_sum_subtype (fun k => g k z = 0) (fun k => l k * g' k d)]
      have h3 : ∑ k : {k // ¬ g k z = 0}, l k.1 * g' k.1 d = 0 :=
        Finset.sum_eq_zero fun k _ => by simp [hl, k.2]
      rw [h3, add_zero]
      exact Finset.sum_congr rfl fun k _ => by simp [hl, k.2]
    rw [h2]
    have h4 : ∀ k : A, c (some k) * T d (some k) = -(c (some k) * g' k.1 d) := fun k => by
      rw [hTsome]; ring
    simp only [h4, Finset.sum_neg_distrib] at h1
    simp only [neg_mul, Finset.sum_neg_distrib]
    linarith

end MWG.WelfareTheorems
