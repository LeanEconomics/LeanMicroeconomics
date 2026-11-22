/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGClassicalDemand.AppendixMK
import ConsumerDemand.CorrespondenceMaximum

/-!
# Mathematical Appendix M.K: sufficiency, uniqueness, shadow prices, theorem of the maximum

MWG, Section M.K, pp. 960-963.

* (M.K.8): nonnegativity constraints, the equivalence of the multiplier form and the modified
  first-order condition; the minimization version of Theorem M.K.2 (p. 961).
* Theorem M.K.3: sufficiency of the Kuhn-Tucker conditions with quasiconvex constraints and
  condition (M.K.9) (the constraint qualification is not needed); (M.K.9) holds for concave
  objectives, and for quasiconcave objectives with nonvanishing gradient on `ℝ^N` (p. 962);
  quasiconvex constraints give a convex constraint set; Figure M.K.4 (`x³`).
* Theorem M.K.4: with a convex constraint set and strictly quasiconcave objective there is at
  most one global constrained maximizer. The printed "there is a unique" is false (no
  maximizer need exist: `theorem_M_K_4_no_existence`); footnote 26.
* The two small-type facts (i), (ii) on dropping a constraint (pp. 962-963).
* Theorem M.K.5 for equality constraints: `∂v/∂b̄_m = λ_m` when the value function is
  differentiable (proved directly; the book cites the envelope theorem). The inequality
  version is not formalized.
* Theorem M.K.6 (theorem of the maximum), through Kreps's Berge theorem, with continuity of the
  constraint correspondence in sequential form plus a local compact bound.
-/

namespace MWG.ClassicalDemand

open Filter Topology MWG.ConsumerChoice

variable {N M : ℕ}

/-- **Equation (M.K.8)** (MWG, pp. 960-961). With a nonnegativity constraint `x_n ≥ 0` written
as `-x_n ≤ 0` with multiplier `λ_{K+1} ≥ 0`, the conditions `∂f/∂x_n = r - λ_{K+1}` and
`λ_{K+1} x_n = 0` are equivalent to `∂f/∂x_n ≤ r` with equality if `x_n > 0`, where `r` is
the rest of the right-hand side of (M.K.5). -/
theorem equation_M_K_8_iff {d r xn : ℝ} (hxn : 0 ≤ xn) :
    (∃ ν : ℝ, 0 ≤ ν ∧ d = r - ν ∧ ν * xn = 0) ↔ (d ≤ r ∧ (0 < xn → d = r)) := by
  constructor
  · rintro ⟨ν, hν, hd, hcs⟩
    refine ⟨by linarith, fun hx => ?_⟩
    have : ν = 0 := by
      rcases mul_eq_zero.mp hcs with h | h
      · exact h
      · linarith
    rw [hd, this, sub_zero]
  · rintro ⟨hle, heq⟩
    refine ⟨r - d, by linarith, by ring, ?_⟩
    rcases hxn.lt_or_eq with hx | hx
    · rw [heq hx, sub_self, zero_mul]
    · rw [← hx, mul_zero]

/-- **Section M.K** (MWG, p. 961). At a local constrained minimizer the Kuhn-Tucker conditions
hold with nonpositive inequality multipliers. -/
theorem theorem_M_K_2_min {K : ℕ} {f : (Fin N → ℝ) → ℝ} {f' : (Fin N → ℝ) →L[ℝ] ℝ}
    {g : Fin M → (Fin N → ℝ) → ℝ} {g' : Fin M → (Fin N → ℝ) →L[ℝ] ℝ} {b : Fin M → ℝ}
    {h : Fin K → (Fin N → ℝ) → ℝ} {h' : Fin K → (Fin N → ℝ) →L[ℝ] ℝ} {c : Fin K → ℝ}
    {x : Fin N → ℝ} (hx : x ∈ kktConstraintSet g b h c)
    (hmin : IsLocalMinOn f (kktConstraintSet g b h c) x) (hf : HasStrictFDerivAt f f' x)
    (hg : ∀ m, HasStrictFDerivAt (g m) (g' m) x) (hh : ∀ k, HasStrictFDerivAt (h k) (h' k) x)
    (hCQ : LinearIndependent ℝ (Sum.elim g' fun k : {k // h k x = c k} => h' k.1)) :
    ∃ lam : Fin M → ℝ, ∃ mu : Fin K → ℝ, (∀ k, mu k ≤ 0) ∧
      f' = ∑ m, lam m • g' m + ∑ k, mu k • h' k ∧ ∀ k, mu k * (h k x - c k) = 0 := by
  obtain ⟨lam, mu, hmu, hfoc, hcs⟩ := theorem_M_K_2 hx hmin.neg hf.neg hg hh hCQ
  refine ⟨-lam, -mu, fun k => neg_nonpos.mpr (hmu k), ?_,
    fun k => by rw [Pi.neg_apply, neg_mul, hcs k, neg_zero]⟩
  rw [← neg_neg f', hfoc, neg_add, ← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib]
  congr 1 <;> exact Finset.sum_congr rfl fun i _ => (neg_smul _ _).symm

/-- **Theorem M.K.3** (MWG, p. 961). Inequality constraints only (`M = 0`), every `h_k`
quasiconvex and differentiable at `x̄`, and the objective satisfies (M.K.9) at `x̄`. If
`x̄ ∈ C` satisfies the Kuhn-Tucker conditions (M.K.6)-(M.K.7), then `x̄` is a global
constrained maximizer. (The book also assumes the constraint qualification; it is not
needed.) -/
theorem theorem_M_K_3 {K : ℕ} {f : (Fin N → ℝ) → ℝ} {f' : (Fin N → ℝ) →L[ℝ] ℝ}
    {h : Fin K → (Fin N → ℝ) → ℝ} {h' : Fin K → (Fin N → ℝ) →L[ℝ] ℝ} {c : Fin K → ℝ}
    {x : Fin N → ℝ} (hh : ∀ k, HasFDerivAt (h k) (h' k) x)
    (hq : ∀ k, QuasiconvexOn ℝ Set.univ (h k))
    (hMK9 : ∀ y, f x < f y → 0 < f' (y - x)) {mu : Fin K → ℝ} (hmu : ∀ k, 0 ≤ mu k)
    (hfoc : f' = ∑ k, mu k • h' k) (hcs : ∀ k, mu k * (h k x - c k) = 0) :
    ∀ y, (∀ k, h k y ≤ c k) → f y ≤ f x := by
  intro y hy
  by_contra hlt
  push Not at hlt
  have hpos := hMK9 y hlt
  rw [hfoc] at hpos
  have hle : (∑ k, mu k • h' k) (y - x) ≤ 0 := by
    rw [sum_apply]
    refine Finset.sum_nonpos fun k _ => ?_
    rw [smul_apply, smul_eq_mul]
    rcases (hmu k).lt_or_eq with hk | hk
    · have hbind : h k x = c k := by
        have := hcs k
        rcases mul_eq_zero.mp this with h0 | h0
        · exact absurd h0 hk.ne'
        · linarith
      -- quasiconvexity: `h_k(y) ≤ h_k(x̄)` forces `∇h_k(x̄)·(y - x̄) ≤ 0`
      have hqc : QuasiconcaveOn ℝ Set.univ (-h k) := by
        rw [quasiconcaveOn_iff_neg_quasiconvexOn, neg_neg]
        exact hq k
      have := theorem_M_C_3_necessity hqc (Set.mem_univ x) (Set.mem_univ y) (hh k).neg
        (by simp only [Pi.neg_apply, neg_le_neg_iff]; rw [hbind]; exact hy k)
      have hneg : h' k (y - x) ≤ 0 := by
        simp only [neg_apply] at this
        linarith
      exact mul_nonpos_of_nonneg_of_nonpos hk.le hneg
    · rw [← hk, zero_mul]
  linarith

/-- **Section M.K** (MWG, p. 962). Condition (M.K.9) holds for a differentiable concave
objective. -/
theorem MK9_of_concave {f : (Fin N → ℝ) → ℝ} {f' : (Fin N → ℝ) → (Fin N → ℝ) →L[ℝ] ℝ}
    (hf : ∀ x, HasFDerivAt f (f' x) x) (hc : ConcaveOn ℝ Set.univ f) :
    ∀ x y, f x < f y → 0 < f' x (y - x) := by
  intro x y hlt
  have := theorem_M_C_1_necessity (z := y - x) (fun x _ => hf x) hc (Set.mem_univ x)
    (Set.mem_univ _)
  rw [add_sub_cancel] at this
  linarith

/-- **Section M.K** (MWG, p. 962). Condition (M.K.9) holds for a quasiconcave objective,
differentiable on `ℝ^N`, whose gradient never vanishes. -/
theorem MK9_of_quasiconcave {f : (Fin N → ℝ) → ℝ} {f' : (Fin N → ℝ) → (Fin N → ℝ) →L[ℝ] ℝ}
    (hf : ∀ x, HasFDerivAt f (f' x) x) (hq : QuasiconcaveOn ℝ Set.univ f)
    (hne : ∀ x, f' x ≠ 0) : ∀ x y, f x < f y → 0 < f' x (y - x) := by
  intro x y hlt
  have hnn := theorem_M_C_3_necessity hq (Set.mem_univ x) (Set.mem_univ y) (hf x) hlt.le
  rcases hnn.lt_or_eq with hpos | hzero
  · exact hpos
  exfalso
  obtain ⟨v, hv⟩ : ∃ v, 0 < f' x v := by
    by_contra hall
    push Not at hall
    apply hne x
    ext w
    have h1 := hall w
    have h2 := hall (-w)
    rw [map_neg] at h2
    simp only [zero_apply]
    linarith
  have hev : ∀ᶠ δ in 𝓝 (0 : ℝ), f x < f (y - δ • v) := by
    have hpath : Tendsto (fun δ : ℝ => y - δ • v) (𝓝 0) (𝓝 y) := by
      have : Continuous (fun δ : ℝ => y - δ • v) := by fun_prop
      simpa using this.tendsto 0
    exact hpath.eventually ((hf y).continuousAt.eventually (lt_mem_nhds hlt))
  obtain ⟨δ, hδ, hδpos⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))).exists
  have hδ0 : 0 < δ := hδpos
  have hge := theorem_M_C_3_necessity hq (Set.mem_univ x) (Set.mem_univ (y - δ • v)) (hf x)
    hδ.le
  have hdec : y - δ • v - x = (y - x) - δ • v := by abel
  rw [hdec, map_sub, map_smul, ← hzero, smul_eq_mul] at hge
  nlinarith

/-- **Footnote 25** (MWG, p. 962). Quasiconvex constraint functions give a convex constraint
set. -/
theorem convex_constraintSet_of_quasiconvex {K : ℕ} {h : Fin K → (Fin N → ℝ) → ℝ}
    (hq : ∀ k, QuasiconvexOn ℝ Set.univ (h k)) (c : Fin K → ℝ) :
    Convex ℝ {x | ∀ k, h k x ≤ c k} := by
  have : {x : Fin N → ℝ | ∀ k, h k x ≤ c k} = ⋂ k, {x | x ∈ Set.univ ∧ h k x ≤ c k} := by
    ext x
    simp
  rw [this]
  exact convex_iInter fun k => hq k (c k)

/-- **Figure M.K.4** (MWG, p. 962). Condition (M.K.9) is indispensable in Theorem M.K.3: for
`max x³` subject to `x - 1 ≤ 0`, the point `x̄ = 0` satisfies the Kuhn-Tucker conditions with
multiplier `0` (the constraint does not bind and `f'(0) = 0`), `f` is quasiconcave and the
constraint quasiconvex, but `x* = 1` is better; (M.K.9) fails at `x̄ = 0`, `x' = 1`. -/
theorem figure_M_K_4 :
    HasDerivAt (fun x : ℝ => x ^ 3) 0 0 ∧ (0 : ℝ) - 1 < 0 ∧
      QuasiconcaveOn ℝ Set.univ (fun x : ℝ => x ^ 3) ∧
      QuasiconvexOn ℝ Set.univ (fun x : ℝ => x - 1) ∧
      (1 : ℝ) - 1 ≤ 0 ∧ (0 : ℝ) ^ 3 < 1 ^ 3 ∧ ¬ (0 < (0 : ℝ) * (1 - 0)) := by
  refine ⟨by simpa using hasDerivAt_pow 3 (0 : ℝ), by norm_num,
    quasiconcave_not_concave_cube.1, ?_, by norm_num, by norm_num, by norm_num⟩
  exact Monotone.quasiconvexOn (fun a b (hab : a ≤ b) => by linarith : Monotone fun x : ℝ => x - 1)

/-- **Theorem M.K.4** (MWG, p. 962). If the constraint set `C` is convex and `f` is strictly
quasiconcave on `C`, there is at most one global constrained maximizer. -/
theorem theorem_M_K_4 {C : Set (Fin N → ℝ)} {f : (Fin N → ℝ) → ℝ}
    (hf : StrictlyQuasiconcaveOn C f) :
    {x | x ∈ C ∧ ∀ y ∈ C, f y ≤ f x}.Subsingleton := by
  intro x hx x' hx'
  by_contra hne
  have heq : f x = f x' := le_antisymm (hx'.2 x hx.1) (hx.2 x' hx'.1)
  have hmem : (1 / 2 : ℝ) • x + (1 - 1 / 2 : ℝ) • x' ∈ C :=
    hf.1 hx.1 hx'.1 (by norm_num) (by norm_num) (by norm_num)
  have := hf.2 x hx.1 x' hx'.1 hne (1 / 2) (by norm_num) (by norm_num) (f x) le_rfl heq.le
  exact absurd (hx.2 _ hmem) (not_le.mpr this)

/-- **Theorem M.K.4** (MWG, p. 962), as printed ("there is a unique global constrained
maximizer") is false: existence can fail. `f(x) = x` on `ℝ¹` is strictly quasiconcave on the
convex set `C = ℝ¹` and has no maximizer. -/
theorem theorem_M_K_4_no_existence :
    StrictlyQuasiconcaveOn (Set.univ : Set (Fin 1 → ℝ)) (fun x => x 0) ∧
      ¬ ∃ x : Fin 1 → ℝ, ∀ y : Fin 1 → ℝ, y 0 ≤ x 0 := by
  constructor
  · refine ⟨convex_univ, ?_⟩
    intro x _ x' _ hne α h0 h1 t ht ht'
    have hne0 : x 0 ≠ x' 0 := by
      intro h
      apply hne
      funext i
      fin_cases i
      exact h
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases lt_or_gt_of_ne hne0 with h | h <;> nlinarith
  · rintro ⟨x, hx⟩
    have := hx (fun _ => x 0 + 1)
    linarith

/-- **Footnote 26** (MWG, p. 962). If `C` is convex and `f` quasiconcave, the set of global
constrained maximizers is convex. -/
theorem footnote_M_K_26 {C : Set (Fin N → ℝ)} (hC : Convex ℝ C) {f : (Fin N → ℝ) → ℝ}
    (hf : QuasiconcaveOn ℝ C f) : Convex ℝ {x | x ∈ C ∧ ∀ y ∈ C, f y ≤ f x} := by
  intro x hx x' hx' a b ha hb hab
  have heq : f x = f x' := le_antisymm (hx'.2 x hx.1) (hx.2 x' hx'.1)
  have hmin := (quasiconcaveOn_iff_min_le.mp hf).2 hx.1 hx'.1 ha hb hab
  rw [heq, min_self] at hmin
  exact ⟨hC hx.1 hx'.1 ha hb hab, fun y hy => (hx'.2 y hy).trans hmin⟩

/-- **Section M.K, small type (i)** (MWG, p. 962). If `x̄` maximizes `f` on the relaxed set
`C₋ₖ` (constraint `k` dropped) and satisfies the dropped constraint, it maximizes `f` on `C`. -/
theorem drop_constraint_i {K : ℕ} {f : (Fin N → ℝ) → ℝ} {h : Fin K → (Fin N → ℝ) → ℝ}
    {c : Fin K → ℝ} {k : Fin K} {x : Fin N → ℝ} (hxk : ∀ j, j ≠ k → h j x ≤ c j)
    (hmax : ∀ y, (∀ j, j ≠ k → h j y ≤ c j) → f y ≤ f x) (hk : h k x ≤ c k) :
    (∀ j, h j x ≤ c j) ∧ ∀ y, (∀ j, h j y ≤ c j) → f y ≤ f x := by
  refine ⟨fun j => ?_, fun y hy => hmax y fun j _ => hy j⟩
  by_cases hj : j = k
  · rw [hj]
    exact hk
  · exact hxk j hj

/-- **Section M.K, small type (ii)** (MWG, p. 963). With continuous quasiconvex constraints and
(M.K.9) at a solution `x̄` of (M.K.4) at which constraint `k` does not bind, `x̄` also solves the
problem with constraint `k` dropped. -/
theorem drop_constraint_ii {K : ℕ} {f : (Fin N → ℝ) → ℝ} {f' : (Fin N → ℝ) →L[ℝ] ℝ}
    {h : Fin K → (Fin N → ℝ) → ℝ} {c : Fin K → ℝ} {k : Fin K} {x : Fin N → ℝ}
    (hcont : ∀ j, Continuous (h j)) (hq : ∀ j, QuasiconvexOn ℝ Set.univ (h j))
    (hf : HasFDerivAt f f' x) (hMK9 : ∀ y, f x < f y → 0 < f' (y - x))
    (hx : ∀ j, h j x ≤ c j) (hsol : ∀ y, (∀ j, h j y ≤ c j) → f y ≤ f x) (hk : h k x < c k) :
    ∀ y, (∀ j, j ≠ k → h j y ≤ c j) → f y ≤ f x := by
  intro y hy
  by_contra hlt
  push Not at hlt
  have hpos := hMK9 y hlt
  -- the segment `x(α) = αy + (1 - α)x̄` stays in `C₋ₖ`, and in `C` for small `α`
  set seg : ℝ → Fin N → ℝ := fun α => x + α • (y - x) with hseg
  have hsegC : ∀ α : ℝ, 0 ≤ α → α ≤ 1 → ∀ j, j ≠ k → h j (seg α) ≤ c j := by
    intro α h0 h1 j hj
    have hmem := hq j (c j) (x := y) ⟨Set.mem_univ _, hy j hj⟩ (y := x)
      ⟨Set.mem_univ _, hx j⟩ h0 (by linarith : (0 : ℝ) ≤ 1 - α) (by ring)
    have heq : seg α = α • y + (1 - α) • x := by
      simp only [hseg]
      module
    rw [heq]
    exact hmem.2
  have hsegk : ∀ᶠ α in 𝓝 (0 : ℝ), h k (seg α) < c k := by
    have : Continuous seg := by
      simp only [hseg]
      fun_prop
    have ht := this.tendsto 0
    simp only [hseg, zero_smul, add_zero] at ht
    exact ht.eventually ((hcont k).continuousAt.eventually (gt_mem_nhds hk))
  have hd : HasDerivAt (fun α : ℝ => f (seg α)) (f' (y - x)) 0 := mc_line_hasDerivAt hf (y - x)
  have hfpos := mk_eventually_gt_of_deriv_pos hd hpos
  obtain ⟨α, ⟨hα1, hα2⟩, hα3, hα0⟩ := ((hfpos.and (hsegk.filter_mono nhdsWithin_le_nhds)).and
    (Ioo_mem_nhdsGT (show (0 : ℝ) < 1 from one_pos))).exists
  have hfeas : ∀ j, h j (seg α) ≤ c j := by
    intro j
    by_cases hj : j = k
    · rw [hj]
      exact hα2.le
    · exact hsegC α hα3.le hα0.le j hj
  have := hsol (seg α) hfeas
  simp only [hseg, zero_smul, add_zero] at hα1
  linarith

/-- **Theorem M.K.5** (MWG, p. 963), equality constraints. Let `x̄` solve the problem at
`b̄` with Lagrange multipliers `λ` (M.K.3), the constraint gradients linearly independent, and
let `v(b)` bound the objective on the constraint set `{g = b}` for `b` near `b̄`, with
`v(b̄) = f(x̄)` (e.g. the value function). If `v` is differentiable at `b̄`, then
`∂v(b̄)/∂b_m = λ_m`: the multipliers are shadow prices. -/
theorem theorem_M_K_5 {f : (Fin N → ℝ) → ℝ} {f' : (Fin N → ℝ) →L[ℝ] ℝ}
    {g : Fin M → (Fin N → ℝ) → ℝ} {g' : Fin M → (Fin N → ℝ) →L[ℝ] ℝ} {x : Fin N → ℝ}
    {bbar : Fin M → ℝ} {v : (Fin M → ℝ) → ℝ} {v' : (Fin M → ℝ) →L[ℝ] ℝ}
    (hx : ∀ m, g m x = bbar m) (hval : v bbar = f x)
    (hbound : ∀ᶠ b in 𝓝 bbar, ∀ y, (∀ m, g m y = b m) → f y ≤ v b)
    (hv : HasFDerivAt v v' bbar) (hf : HasFDerivAt f f' x)
    (hg : ∀ m, HasFDerivAt (g m) (g' m) x) (hCQ : LinearIndependent ℝ g')
    {lam : Fin M → ℝ} (hlam : f' = ∑ m, lam m • g' m) :
    ∀ m, v' (Pi.single m 1) = lam m := by
  classical
  have hG : HasFDerivAt (fun y m => g m y) (ContinuousLinearMap.pi g') x :=
    hasFDerivAt_pi.mpr hg
  have hGx : (fun m => g m x) = bbar := funext hx
  have hv' : HasFDerivAt v v' ((fun y m => g m y) x) := by
    change HasFDerivAt v v' (fun m => g m x)
    rw [hGx]
    exact hv
  have hcomp := hv'.comp x hG
  have hψ : HasFDerivAt (fun y => v (fun m => g m y) - f y)
      (v'.comp (ContinuousLinearMap.pi g') - f') x := hcomp.sub hf
  have hmin : IsLocalMin (fun y => v (fun m => g m y) - f y) x := by
    have hcont : Tendsto (fun y m => g m y) (𝓝 x) (𝓝 bbar) := by
      have := hG.continuousAt.tendsto
      rwa [hGx] at this
    filter_upwards [hcont.eventually hbound] with y hy
    have := hy y fun m => rfl
    have hxv : v (fun m => g m x) - f x = 0 := by rw [hGx, hval, sub_self]
    rw [hxv]
    linarith
  have hzero := hmin.hasFDerivAt_eq_zero hψ
  have hcomb : ∑ m, (v' (Pi.single m 1) - lam m) • g' m = 0 := by
    ext w
    have h1 := congrArg (fun φ : (Fin N → ℝ) →L[ℝ] ℝ => φ w) hzero
    simp only [sub_apply, ContinuousLinearMap.coe_comp,
      Function.comp_apply, zero_apply] at h1
    have hdec : v' (ContinuousLinearMap.pi g' w) = ∑ m, g' m w * v' (Pi.single m 1) := by
      conv_lhs => rw [← Finset.univ_sum_single (ContinuousLinearMap.pi g' w)]
      rw [map_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [← smul_eq_mul, ← map_smul, ← Pi.single_smul, smul_eq_mul, mul_one]
      rfl
    rw [hdec, hlam] at h1
    simp only [sum_apply, smul_apply, smul_eq_mul] at h1 ⊢
    rw [show ∑ m, (v' (Pi.single m 1) - lam m) * g' m w =
        ∑ m, g' m w * v' (Pi.single m 1) - ∑ m, lam m * g' m w by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun m _ => by ring]
    simpa using h1
  intro m
  have := (Fintype.linearIndependent_iff.mp hCQ) _ hcomb m
  linarith

/-- **Theorem M.K.6** (MWG, p. 963), the theorem of the maximum. Maximize a continuous `f`
over `x ∈ C(q)`. If the constraint correspondence `C` is continuous (here: sequentially upper
and lower hemicontinuous, in Kreps's closed-graph form, with a local compact bound) and has
nonempty values, then the maximizer correspondence has nonempty values, a closed graph and a
local compact bound (so it is upper hemicontinuous), and the value function is continuous.
Applied from Kreps's Berge theorem. -/
theorem theorem_M_K_6 {Q : Type*} [TopologicalSpace Q] [FirstCountableTopology Q]
    {C : Q → Set (Fin N → ℝ)} {f : (Fin N → ℝ) → ℝ} (hf : Continuous f)
    (hl : Kreps.ConsumerDemand.SequentialLower C) (hu : Kreps.ConsumerDemand.SequentialUpper C)
    (hb : Kreps.ConsumerDemand.LocalCompactBound C) (hne : ∀ q, (C q).Nonempty) :
    (∀ q, (Kreps.ConsumerDemand.ParametricMaxima C (fun _ => f) q).Nonempty) ∧
      Kreps.ConsumerDemand.SequentialUpper (Kreps.ConsumerDemand.ParametricMaxima C fun _ => f) ∧
      Kreps.ConsumerDemand.LocalCompactBound
        (Kreps.ConsumerDemand.ParametricMaxima C fun _ => f) ∧
      Continuous (Kreps.ConsumerDemand.ParametricValue C fun _ => f) :=
  Kreps.ConsumerDemand.maximum_theorem (hf.comp continuous_snd) hl hu hb hne

end MWG.ClassicalDemand
