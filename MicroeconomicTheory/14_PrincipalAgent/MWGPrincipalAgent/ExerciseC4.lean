/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPrincipalAgent.ExampleHA
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Exercise 14.C.4: a risk-averse but not infinitely risk-averse manager

MWG, Exercise 14.C.4, p. 509, in the two-state hidden-information model of Section 14.C
(pp. 489-490): the manager's utility is `v(w - g(e, θ))` with `v` strictly concave, strictly
increasing and differentiable; he accepts the contract before learning `θ`, so the participation
constraint is in expected utility, `λ v(w_H - g(e_H, θ_H)) + (1 - λ) v(w_L - g(e_L, θ_L)) ≥ ū`
(instead of (i)-(ii) of (14.C.8)), and the self-selection constraints (iii)-(iv) are as in
(14.C.8). Write `c_i = w_i - g(e_i, θ_i)` and `D(e) = g(e, θ_L) - g(e, θ_H)` (strictly increasing
on `[0, ∞)`: single crossing, `g_eθ < 0`).

* `exercise_14_C_4`: **the characterization**. In every optimal contract the participation
  constraint and the high state's self-selection constraint (iii) bind; `e_L ≤ e_H`; there is no
  distortion at the top (`e_H = e*_H`) and a downward distortion `e_L ≤ e*_L`; and the manager
  bears risk: `c_H - c_L = D(e_L)`, which is positive when `e_L > 0` (unlike the infinitely
  risk-averse case, where `c_H = c_L` is not required but `c_L = v⁻¹(ū)`).
* `exercise_14_C_4_strict`: with differentiability (`D' > 0`), the distortion is strict:
  `e_L < e*_L` whenever `e*_L > 0`.
* `exercise_14_C_4_instance`: `λ = 1/2`, `v(c) = -exp(-c)`, `ū = -1`, `π(e) = e`,
  `D(e) = κ e²` with `κ = log(11/9)`: the optimal contract has `e_L = 1 < e*_L`, `e_H = e*_H`,
  `c_H = log(10/9) > c_L = log(10/11)`; its optimality is proved with a Lagrangian certificate
  and the two theorems apply to it.
-/

namespace MWG.PrincipalAgent

open Set Filter Topology

/-- The constraints of Exercise 14.C.4: nonnegative efforts, expected-utility participation and
the self-selection constraints (iii)-(iv) of (14.C.8). -/
def C4Feas (v : ℝ → ℝ) (g : ℝ → ℝ → ℝ) (θH θL lam ubar wH eH wL eL : ℝ) : Prop :=
  0 ≤ eH ∧ 0 ≤ eL ∧ ubar ≤ lam * v (wH - g eH θH) + (1 - lam) * v (wL - g eL θL) ∧
    wL - g eL θH ≤ wH - g eH θH ∧ wH - g eH θL ≤ wL - g eL θL

/-- The owner's expected profit `λ [π(e_H) - w_H] + (1 - λ) [π(e_L) - w_L]`. -/
def c4Prof (prof : ℝ → ℝ) (lam wH eH wL eL : ℝ) : ℝ :=
  lam * (prof eH - wH) + (1 - lam) * (prof eL - wL)

/-- A contract described by the certainty incomes `c_i` and efforts: feasibility. -/
theorem c4_mk {v : ℝ → ℝ} {g : ℝ → ℝ → ℝ} {θH θL lam ubar cH eH cL eL : ℝ} (hH : 0 ≤ eH)
    (hL : 0 ≤ eL) (hIR : ubar ≤ lam * v cH + (1 - lam) * v cL)
    (hiii : cL + (g eL θL - g eL θH) ≤ cH) (hiv : cH - (g eH θL - g eH θH) ≤ cL) :
    C4Feas v g θH θL lam ubar (cH + g eH θH) eH (cL + g eL θL) eL := by
  refine ⟨hH, hL, by simpa using hIR, by linarith, by linarith⟩

/-- The profit of a contract described by certainty incomes. -/
theorem c4_prof_mk {prof : ℝ → ℝ} {g : ℝ → ℝ → ℝ} {θH θL lam cH eH cL eL : ℝ} :
    c4Prof prof lam (cH + g eH θH) eH (cL + g eL θL) eL =
      lam * (prof eH - g eH θH - cH) + (1 - lam) * (prof eL - g eL θL - cL) := by
  unfold c4Prof; ring

/-- Concavity makes the derivative antitone (strictly, under strict concavity). -/
theorem c4_dv_lt {v dv : ℝ → ℝ} (hv : StrictConcaveOn ℝ univ v)
    (hdv : ∀ x, HasDerivAt v (dv x) x) {x y : ℝ} (hxy : x < y) : dv y < dv x := by
  have h1 := tpa_tangent_lt hv (mem_univ x) (mem_univ y) hxy.ne' (hdv x).hasDerivWithinAt
  have h2 := tpa_tangent_lt hv (mem_univ y) (mem_univ x) hxy.ne (hdv y).hasDerivWithinAt
  nlinarith

/-- Spreading utilities more than needed is costly: if `a < a' ≤ b' < b` and moving from
`(a, b)` to `(a', b')` keeps `λ v(b) + (1 - λ) v(a)`, then the expected income falls:
`(1 - λ)(a' - a) < λ (b - b')` (strict concavity). -/
theorem c4_spread {v dv : ℝ → ℝ} (hv : StrictConcaveOn ℝ univ v)
    (hdv : ∀ x, HasDerivAt v (dv x) x) (hdvpos : ∀ x, 0 < dv x) {lam a b a' b' : ℝ}
    (hl0 : 0 < lam) (hl1 : lam < 1) (ha : a < a') (hab : a' ≤ b') (hb : b' < b)
    (heq : (1 - lam) * (v a' - v a) = lam * (v b - v b')) :
    (1 - lam) * (a' - a) < lam * (b - b') := by
  have t1 := tpa_tangent_le hv.concaveOn (mem_univ a') (mem_univ a) (hdv a').hasDerivWithinAt
  have t2 := tpa_tangent_lt hv (mem_univ b') (mem_univ b) hb.ne' (hdv b').hasDerivWithinAt
  have hdd : dv b' ≤ dv a' := by
    rcases hab.lt_or_eq with h | h
    · exact (c4_dv_lt hv hdv h).le
    · rw [h]
  have hp := hdvpos b'
  have k1 : 0 ≤ (1 - lam) * (a' - a) := mul_nonneg (by linarith) (by linarith)
  have e1 : (1 - lam) * (a' - a) * dv b' ≤ (1 - lam) * (a' - a) * dv a' :=
    mul_le_mul_of_nonneg_left hdd k1
  have e2 : (1 - lam) * ((a' - a) * dv a') ≤ (1 - lam) * (v a' - v a) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have e3 : lam * (v b - v b') < lam * (dv b' * (b - b')) :=
    mul_lt_mul_of_pos_left (by linarith) hl0
  have : (1 - lam) * (a' - a) * dv b' < lam * (b - b') * dv b' := by
    have r1 : (1 - lam) * (a' - a) * dv a' = (1 - lam) * ((a' - a) * dv a') := by ring
    have r2 : lam * (dv b' * (b - b')) = lam * (b - b') * dv b' := by ring
    linarith
  exact lt_of_mul_lt_mul_right this hp.le

/-- The participation bound used for the strict distortion: moving from `(a, b)` to
`(x, y) = (a + κΔ, b - (1 - κ)Δ)` with `A ≤ v'(x)`, `v'(y) ≤ B` and
`κ ((1 - λ) A + λ B) = λ B` does not lower `λ v(b) + (1 - λ) v(a)`. -/
theorem c4_part {v dv : ℝ → ℝ} (hv : ConcaveOn ℝ univ v) (hdv : ∀ x, HasDerivAt v (dv x) x)
    {lam a b x y A B κ Δ : ℝ} (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1) (hx : x = a + κ * Δ)
    (hy : b = y + (1 - κ) * Δ) (hΔ : 0 ≤ Δ) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (hA : A ≤ dv x)
    (hB : dv y ≤ B) (hκeq : κ * ((1 - lam) * A + lam * B) = lam * B) :
    lam * v b + (1 - lam) * v a ≤ lam * v y + (1 - lam) * v x := by
  subst hx hy
  have t1 := tpa_tangent_le hv (mem_univ (a + κ * Δ)) (mem_univ a)
    (hdv (a + κ * Δ)).hasDerivWithinAt
  have t2 := tpa_tangent_le hv (mem_univ y) (mem_univ (y + (1 - κ) * Δ))
    (hdv y).hasDerivWithinAt
  have k1 : A * (κ * Δ) ≤ dv (a + κ * Δ) * (κ * Δ) :=
    mul_le_mul_of_nonneg_right hA (mul_nonneg hκ0 hΔ)
  have k2 : dv y * ((1 - κ) * Δ) ≤ B * ((1 - κ) * Δ) :=
    mul_le_mul_of_nonneg_right hB (mul_nonneg (by linarith) hΔ)
  have h1 : v (a + κ * Δ) - v a ≥ A * (κ * Δ) := by nlinarith
  have h2 : v (y + (1 - κ) * Δ) - v y ≤ B * ((1 - κ) * Δ) := by nlinarith
  have h3 := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ 1 - lam)
  have h4 := mul_le_mul_of_nonneg_left h2 hl0
  have h5 : lam * (B * ((1 - κ) * Δ)) - (1 - lam) * (A * (κ * Δ)) = 0 := by
    linear_combination (-Δ) * hκeq
  nlinarith

/-- **Exercise 14.C.4** (MWG, p. 509), the characterization. Assumptions: `0 < λ < 1`; `v` strictly
concave and differentiable with `v' > 0`; `D(e) = g(e, θ_L) - g(e, θ_H)` strictly increasing on
`[0, ∞)` with `g(0, θ) = 0`; `e*_i ≥ 0` the unique maximizer of `π(e) - g(e, θ_i)` on `[0, ∞)`,
with `e*_L ≤ e*_H`. Every optimal contract has (a) binding participation; (b) binding (iii):
`c_H = c_L + D(e_L)`; (c) `e_L ≤ e_H`; (d) `e_L ≤ e*_L`; (e) `e_H = e*_H`; (f) `c_L < c_H` when
`e_L > 0` (the manager bears risk). -/
theorem exercise_14_C_4 {v dv prof : ℝ → ℝ} {g : ℝ → ℝ → ℝ} {θH θL lam ubar esH esL : ℝ}
    (hl0 : 0 < lam) (hl1 : lam < 1) (hv : StrictConcaveOn ℝ univ v)
    (hdv : ∀ x, HasDerivAt v (dv x) x) (hdvpos : ∀ x, 0 < dv x)
    (hD : StrictMonoOn (fun e => g e θL - g e θH) (Ici 0)) (hg0 : ∀ t, g 0 t = 0)
    (hsH0 : 0 ≤ esH) (hsL0 : 0 ≤ esL)
    (hsH : ∀ x, 0 ≤ x → x ≠ esH → prof x - g x θH < prof esH - g esH θH)
    (hsL : ∀ x, 0 ≤ x → x ≠ esL → prof x - g x θL < prof esL - g esL θL) (hord : esL ≤ esH)
    {wH eH wL eL : ℝ} (hf : C4Feas v g θH θL lam ubar wH eH wL eL)
    (hopt : ∀ wH' eH' wL' eL', C4Feas v g θH θL lam ubar wH' eH' wL' eL' →
      c4Prof prof lam wH' eH' wL' eL' ≤ c4Prof prof lam wH eH wL eL) :
    lam * v (wH - g eH θH) + (1 - lam) * v (wL - g eL θL) = ubar ∧
      wH - g eH θH = wL - g eL θL + (g eL θL - g eL θH) ∧ eL ≤ eH ∧ eL ≤ esL ∧ eH = esH ∧
      (0 < eL → wL - g eL θL < wH - g eH θH) := by
  obtain ⟨hH0, hL0, hIR, hiii, hiv⟩ := hf
  set cH := wH - g eH θH with hcH
  set cL := wL - g eL θL with hcL
  set D : ℝ → ℝ := fun e => g e θL - g e θH with hDdef
  have hvm : StrictMono v := by
    intro x y hxy
    have := tpa_tangent_lt hv (mem_univ y) (mem_univ x) hxy.ne (hdv y).hasDerivWithinAt
    nlinarith [hdvpos y]
  have hvc : Continuous v := continuous_iff_continuousAt.2 fun x => (hdv x).continuousAt
  have hwH : wH = cH + g eH θH := by rw [hcH]; ring
  have hwL : wL = cL + g eL θL := by rw [hcL]; ring
  have hprof : c4Prof prof lam wH eH wL eL =
      lam * (prof eH - g eH θH - cH) + (1 - lam) * (prof eL - g eL θL - cL) := by
    rw [hwH, hwL, c4_prof_mk]
  have hiii' : cL + D eL ≤ cH := by simp only [D, hcH, hcL]; linarith
  have hiv' : cH - D eH ≤ cL := by simp only [D, hcH, hcL]; linarith
  -- (c) `e_L ≤ e_H`
  have hLH : eL ≤ eH := (hD.le_iff_le (mem_Ici.2 hL0) (mem_Ici.2 hH0)).1 (by linarith)
  -- (a) participation binds
  have hbindIR : lam * v cH + (1 - lam) * v cL = ubar := by
    by_contra hne
    have hlt : ubar < lam * v cH + (1 - lam) * v cL := lt_of_le_of_ne hIR (Ne.symm hne)
    have hcont : Continuous fun ε : ℝ => lam * v (cH - ε) + (1 - lam) * v (cL - ε) := by
      fun_prop
    have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), ubar < lam * v (cH - ε) + (1 - lam) * v (cL - ε) :=
      hcont.continuousAt.eventually (lt_mem_nhds (by simpa using hlt))
    obtain ⟨ε, hε, hεpos⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
      (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0)).exists
    have hfeas := c4_mk (v := v) (g := g) (θH := θH) (θL := θL) (lam := lam) (ubar := ubar)
      (cH := cH - ε) (cL := cL - ε) hH0 hL0 hε.le (by simp only [D] at hiii'; linarith)
      (by simp only [D] at hiv'; linarith)
    have := hopt _ _ _ _ hfeas
    rw [c4_prof_mk, hprof] at this
    have hεpos' : (0 : ℝ) < ε := hεpos
    have e : lam * (prof eH - g eH θH - (cH - ε)) + (1 - lam) * (prof eL - g eL θL - (cL - ε)) =
        lam * (prof eH - g eH θH - cH) + (1 - lam) * (prof eL - g eL θL - cL) + ε := by ring
    linarith
  -- (b) (iii) binds
  have hbind : cH = cL + D eL := by
    by_contra hne
    have hslack : cL + D eL < cH := lt_of_le_of_ne hiii' (Ne.symm hne)
    set U := lam * v cH + (1 - lam) * v cL
    have hc : Continuous fun s : ℝ => lam * v (s + D eL) + (1 - lam) * v s := by fun_prop
    have hlo : lam * v (cL + D eL) + (1 - lam) * v cL ≤ U := by
      have := hvm.monotone hslack.le
      nlinarith
    have hhi : U ≤ lam * v (cH - D eL + D eL) + (1 - lam) * v (cH - D eL) := by
      have := hvm.monotone (show cL ≤ cH - D eL by linarith)
      simp only [sub_add_cancel]
      nlinarith
    obtain ⟨s, ⟨hs1, hs2⟩, hs⟩ := intermediate_value_Icc (show cL ≤ cH - D eL by linarith)
      hc.continuousOn ⟨hlo, hhi⟩
    simp only at hs
    -- the new contract `(s + D(e_L), s)` is cheaper
    have ha : cL < s := by
      rcases hs1.lt_or_eq with h | h
      · exact h
      · subst h
        have := mul_lt_mul_of_pos_left (hvm (show cL + D eL < cH from hslack)) hl0
        simp only [U] at hs
        linarith
    have hb : s + D eL < cH := by
      rcases hs2.lt_or_eq with h | h
      · linarith
      · have := mul_lt_mul_of_pos_left (hvm (show cL < s from ha)) (by linarith : 0 < 1 - lam)
        rw [h] at hs this
        simp only [sub_add_cancel, U] at hs
        linarith
    have hDnn : 0 ≤ D eL := by
      have := hD.monotoneOn (mem_Ici.2 le_rfl) (mem_Ici.2 hL0) hL0
      simpa [D, hg0] using this
    have key : (1 - lam) * (s - cL) < lam * (cH - (s + D eL)) :=
      c4_spread hv hdv hdvpos hl0 hl1 ha (by linarith) hb (by simp only [U] at hs; linarith)
    have hDLH := hD.monotoneOn (mem_Ici.2 hL0) (mem_Ici.2 hH0) hLH
    have hfeas := c4_mk (v := v) (g := g) (θH := θH) (θL := θL) (lam := lam) (ubar := ubar)
      (cH := s + D eL) (cL := s) hH0 hL0 (by simp only [U] at hs; linarith)
      (by simp only [D]; linarith) (by simp only [D] at hiv' hDLH ⊢; linarith)
    have := hopt _ _ _ _ hfeas
    rw [c4_prof_mk, hprof] at this
    linarith
  -- (d) `e_L ≤ e*_L`
  have hLs : eL ≤ esL := by
    by_contra hlt
    push Not at hlt
    have hfeas := c4_mk (v := v) (g := g) (θH := θH) (θL := θL) (lam := lam) (ubar := ubar)
      (cH := cH) (cL := cL) (eL := esL) hH0 hsL0 hIR
      (by have := hD.monotoneOn (mem_Ici.2 hsL0) (mem_Ici.2 hL0) hlt.le
          simp only [D] at hiii' this ⊢; linarith)
      (by simp only [D] at hiv' ⊢; linarith)
    have := hopt _ _ _ _ hfeas
    rw [c4_prof_mk, hprof] at this
    have := hsL eL hL0 hlt.ne'
    nlinarith
  -- (e) `e_H = e*_H`
  have hHs : eH = esH := by
    by_contra hne
    have hfeas := c4_mk (v := v) (g := g) (θH := θH) (θL := θL) (lam := lam) (ubar := ubar)
      (cH := cH) (cL := cL) (eH := esH) hsH0 hL0 hIR (by simp only [D] at hiii' ⊢; linarith)
      (by
        have := hD.monotoneOn (mem_Ici.2 hL0) (mem_Ici.2 hsH0) (hLs.trans hord)
        simp only [D] at hbind this ⊢; linarith)
    have := hopt _ _ _ _ hfeas
    rw [c4_prof_mk, hprof] at this
    have := hsH eH hH0 hne
    nlinarith
  refine ⟨hbindIR, hbind, hLH, hLs, hHs, fun hpos => ?_⟩
  have := hD (mem_Ici.2 le_rfl) (mem_Ici.2 hL0) hpos
  have hD0 : D 0 = 0 := by simp [D, hg0]
  linarith

/-- A function with negative derivative at `x` is larger than at `x` just to the left of `x`. -/
theorem c4_left_gt {ψ : ℝ → ℝ} {d x : ℝ} (hψ : HasDerivAt ψ d x) (hd : d < 0) :
    ∀ᶠ y in 𝓝[<] x, ψ x < ψ y := by
  have h := hasDerivAt_iff_tendsto_slope.1 hψ
  have h' := h.mono_left (nhdsWithin_mono x (fun y (hy : y < x) => ne_of_lt hy))
  filter_upwards [h'.eventually (gt_mem_nhds hd), self_mem_nhdsWithin] with y hy hyx
  rw [slope_def_field] at hy
  have hyx' : y - x < 0 := by simp only [mem_Iio] at hyx; linarith
  have := (div_neg_iff.1 hy)
  rcases this with ⟨_, h2⟩ | ⟨h1, _⟩
  · linarith
  · linarith

/-- **Exercise 14.C.4** (MWG, p. 509), strict downward distortion. In addition to the assumptions
of `exercise_14_C_4`, let `π(e) - g(e, θ_L)` be differentiable at `e*_L > 0` and `D` differentiable
at `e*_L` with `D'(e*_L) > 0` (as `g_eθ < 0`). Then every optimal contract has `e_L < e*_L`. -/
theorem exercise_14_C_4_strict {v dv prof : ℝ → ℝ} {g : ℝ → ℝ → ℝ}
    {θH θL lam ubar esH esL sL dD : ℝ}
    (hl0 : 0 < lam) (hl1 : lam < 1) (hv : StrictConcaveOn ℝ univ v)
    (hdv : ∀ x, HasDerivAt v (dv x) x) (hdvpos : ∀ x, 0 < dv x)
    (hD : StrictMonoOn (fun e => g e θL - g e θH) (Ici 0)) (hg0 : ∀ t, g 0 t = 0)
    (hsH0 : 0 ≤ esH) (hsLpos : 0 < esL)
    (hsH : ∀ x, 0 ≤ x → x ≠ esH → prof x - g x θH < prof esH - g esH θH)
    (hsL : ∀ x, 0 ≤ x → x ≠ esL → prof x - g x θL < prof esL - g esL θL) (hord : esL ≤ esH)
    (hSd : HasDerivAt (fun e => prof e - g e θL) sL esL)
    (hDd : HasDerivAt (fun e => g e θL - g e θH) dD esL) (hdD : 0 < dD)
    {wH eH wL eL : ℝ} (hf : C4Feas v g θH θL lam ubar wH eH wL eL)
    (hopt : ∀ wH' eH' wL' eL', C4Feas v g θH θL lam ubar wH' eH' wL' eL' →
      c4Prof prof lam wH' eH' wL' eL' ≤ c4Prof prof lam wH eH wL eL) :
    eL < esL := by
  obtain ⟨hbIR, hbind, hLH, hLs, hHs, hrisk⟩ := exercise_14_C_4 hl0 hl1 hv hdv hdvpos hD hg0
    hsH0 hsLpos.le hsH hsL hord hf hopt
  rcases hLs.lt_or_eq with h | h
  · exact h
  exfalso
  obtain ⟨hH0, hL0, hIR, hiii, hiv⟩ := hf
  subst h
  set D : ℝ → ℝ := fun e => g e θL - g e θH with hDdef
  set S : ℝ → ℝ := fun e => prof e - g e θL with hSdef
  set cH := wH - g eH θH with hcH
  set cL := wL - g eL θL with hcL
  have hsL0 : sL = 0 := by
    refine IsLocalMax.hasDerivAt_eq_zero ?_ hSd
    filter_upwards [Ioi_mem_nhds hsLpos] with x hx
    rcases eq_or_ne x eL with rfl | hne
    · exact le_rfl
    · exact (hsL x (le_of_lt hx) hne).le
  have hgap : cL < cH := hrisk hsLpos
  set m1 := cL + (cH - cL) / 3
  set m2 := cL + 2 * (cH - cL) / 3
  have hA := hdvpos m1
  have hB := hdvpos m2
  have hAB : dv m2 < dv m1 := c4_dv_lt hv hdv (by simp only [m1, m2]; linarith)
  set κ := lam * dv m2 / ((1 - lam) * dv m1 + lam * dv m2)
  have hden : 0 < (1 - lam) * dv m1 + lam * dv m2 := by nlinarith
  have hκ0 : 0 ≤ κ := div_nonneg (by positivity) hden.le
  have hκl : κ < lam := by
    rw [div_lt_iff₀ hden]
    nlinarith [mul_pos (mul_pos hl0 (by linarith : (0 : ℝ) < 1 - lam)) (sub_pos.2 hAB)]
  have hκ1 : κ ≤ 1 := hκl.le.trans hl1.le
  have hκeq : κ * ((1 - lam) * dv m1 + lam * dv m2) = lam * dv m2 := div_mul_cancel₀ _ hden.ne'
  -- choosing the new effort `y < e*_L`
  have hψ : HasDerivAt (fun e => (1 - lam) * S e - (lam - κ) * D e)
      ((1 - lam) * sL - (lam - κ) * dD) eL := (hSd.const_mul _).sub (hDd.const_mul _)
  have hneg : (1 - lam) * sL - (lam - κ) * dD < 0 := by
    rw [hsL0]; nlinarith [mul_pos (sub_pos.2 hκl) hdD]
  have hDc : Tendsto D (𝓝[<] eL) (𝓝 (D eL)) :=
    hDd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hgap3 : 0 < (cH - cL) / 3 := by linarith
  obtain ⟨y, ⟨hy1, hy2⟩, hy4⟩ := (((c4_left_gt hψ hneg).and
    (hDc.eventually (Metric.ball_mem_nhds (D eL) hgap3))).and
    (Ioo_mem_nhdsLT hsLpos)).exists
  rw [Real.dist_eq] at hy2
  have hy0 : 0 < y := hy4.1
  have hyL : y < eL := hy4.2
  have hDy : D y < D eL := hD (mem_Ici.2 hy0.le) (mem_Ici.2 hL0) hyL
  set Δ := D eL - D y
  have hΔ : 0 < Δ := by simp only [Δ]; linarith
  have hΔ3 : Δ < (cH - cL) / 3 := by
    rw [abs_sub_comm] at hy2
    simp only [Δ]
    linarith [le_abs_self (D eL - D y)]
  set t := κ * Δ
  have ht0 : 0 ≤ t := mul_nonneg hκ0 hΔ.le
  have htΔ : t ≤ Δ := by simp only [t]; nlinarith
  have hcHb : cH = cL + D eL := by simp only [D]; linarith [hbind]
  -- participation for the new contract `(c_L + t + D(y), c_L + t)`
  have d1 : dv m1 ≤ dv (cL + t) := by
    rcases (show cL + t ≤ m1 by simp only [m1]; linarith).lt_or_eq with h | h
    · exact (c4_dv_lt hv hdv h).le
    · rw [h]
  have hm2 : m2 ≤ cL + t + D y := by
    have : D y = D eL - Δ := by simp only [Δ]; ring
    rw [this]; simp only [m2]; rw [hcHb] at hΔ3 ⊢; linarith
  have d2 : dv (cL + t + D y) ≤ dv m2 := by
    rcases hm2.lt_or_eq with h | h
    · exact (c4_dv_lt hv hdv h).le
    · rw [h]
  have hpart : lam * v cH + (1 - lam) * v cL ≤
      lam * v (cL + t + D y) + (1 - lam) * v (cL + t) :=
    c4_part hv.concaveOn hdv hl0.le hl1.le rfl (by simp only [t, Δ]; rw [hcHb]; ring) hΔ.le
      hκ0 hκ1 d1 d2 hκeq
  have hfeas := c4_mk (v := v) (g := g) (θH := θH) (θL := θL) (lam := lam) (ubar := ubar)
    (cH := cL + t + D y) (cL := cL + t) (eH := eH) (eL := y) hH0 hy0.le (hIR.trans
      (by simpa [hcH, hcL] using hpart)) (by simp only [D]; linarith)
    (by
      have := hD.monotoneOn (mem_Ici.2 hy0.le) (mem_Ici.2 hH0) (hyL.le.trans hLH)
      simp only [D] at this ⊢; linarith)
  have hp := hopt _ _ _ _ hfeas
  have hwH : wH = cH + g eH θH := by rw [hcH]; ring
  have hwL : wL = cL + g eL θL := by rw [hcL]; ring
  rw [c4_prof_mk, hwH, hwL, c4_prof_mk] at hp
  have e : lam * (prof eH - g eH θH - (cL + t + D y)) + (1 - lam) * (prof y - g y θL - (cL + t)) -
      (lam * (prof eH - g eH θH - cH) + (1 - lam) * (prof eL - g eL θL - cL)) =
      ((1 - lam) * S y - (lam - κ) * D y) - ((1 - lam) * S eL - (lam - κ) * D eL) := by
    simp only [t, Δ, S]; rw [hcHb]; ring
  linarith

/-- The exponential bound behind the instance: with `e^{-L} = q > 0`,
`-k c - e^{-c}/2 ≤ -k L - k` when `k = q/2`. -/
theorem c4_exp_bound {c L q : ℝ} (hL : Real.exp (-L) = q) (hq : 0 < q) :
    -(q / 2) * c - Real.exp (-c) / 2 ≤ -(q / 2) * L - q / 2 := by
  have h1 := Real.add_one_le_exp (-(c - L))
  have h2 : Real.exp (-c) = Real.exp (-L) * Real.exp (-(c - L)) := by
    rw [← Real.exp_add]; ring_nf
  rw [h2, hL]
  nlinarith

/-- The instance of Exercise 14.C.4: `κ = log(10/9) - log(10/11)` (`= log(11/9)`). -/
noncomputable def c4κ : ℝ := Real.log (10 / 9) - Real.log (10 / 11)

/-- The instance: `a = 1 - 11κ/5`. -/
noncomputable def c4a : ℝ := 1 - 11 * c4κ / 5

/-- The instance: `g(e, θ) = a e²/2 + κ (1 - θ) e²` (`θ_L = 0`, `θ_H = 1`). -/
noncomputable def c4g (e θ : ℝ) : ℝ := c4a * e ^ 2 / 2 + c4κ * (1 - θ) * e ^ 2

/-- The instance: the wage in state `θ_H`, `log(10/9) + g(1/a, θ_H)`. -/
noncomputable def c4wH : ℝ := Real.log (10 / 9) + c4g (1 / c4a) 1

/-- The instance: the wage in state `θ_L`, `log(10/11) + g(1, θ_L)`. -/
noncomputable def c4wL : ℝ := Real.log (10 / 11) + c4g 1 0

/-- **Exercise 14.C.4, an instance** (MWG, p. 509). `λ = 1/2`, `v(c) = -exp(-c)`, `ū = -1`,
`π(e) = e`, `θ_L = 0`, `θ_H = 1`, `c4g(e, θ) = c4a e²/2 + c4κ (1 - θ) e²` with
`c4κ = log(10/9) - log(10/11)` (`= log(11/9)`) and `c4a = 1 - 11κ/5`, so that `D(e) = c4κ e²`,
`e*_H = 1/c4a` and `e*_L = 1/(1 - c4κ/5)`. The contract `e_H = 1/c4a`, `e_L = 1`,
`c_H = log(10/9)`, `c_L = log(10/11)` is optimal (Lagrangian certificate with multipliers `1` on
participation and `1/20` on (iii)); for it the characterization holds and `e_L = 1 < e*_L`. -/
theorem exercise_14_C_4_instance :
    C4Feas (fun c => -Real.exp (-c)) c4g 1 0 (1 / 2) (-1) c4wH (1 / c4a) c4wL 1 ∧
      (∀ wH' eH' wL' eL', C4Feas (fun c => -Real.exp (-c)) c4g 1 0 (1 / 2) (-1) wH' eH' wL' eL' →
        c4Prof id (1 / 2) wH' eH' wL' eL' ≤ c4Prof id (1 / 2) c4wH (1 / c4a) c4wL 1) ∧
      (1 : ℝ) < 1 / (1 - c4κ / 5) ∧ c4wL - c4g 1 0 < c4wH - c4g (1 / c4a) 1 := by
  have hL1 : 0 < Real.log (10 / 9) := Real.log_pos (by norm_num)
  have hL1' : Real.log (10 / 9) < 1 / 9 := by
    have := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 10 / 9) (by norm_num)
    linarith
  have hL2 : Real.log (10 / 11) < 0 := Real.log_neg (by norm_num) (by norm_num)
  have hL2' : -(1 / 10) < Real.log (10 / 11) := by
    have := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 11 / 10) (by norm_num)
    have e : Real.log (10 / 11) = -Real.log (11 / 10) := by
      rw [← Real.log_inv]; norm_num
    linarith
  have hκ0 : 0 < c4κ := by simp only [c4κ]; linarith
  have hκ1 : c4κ < 1 / 4 := by simp only [c4κ]; linarith
  have ha0 : 0 < c4a := by simp only [c4a]; linarith
  have ha1 : c4a < 1 := by simp only [c4a]; linarith
  have hb0 : 0 < 1 - c4κ / 5 := by linarith
  have e9 : Real.exp (-Real.log (10 / 9)) = 9 / 10 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  have e11 : Real.exp (-Real.log (10 / 11)) = 11 / 10 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  have hgH : ∀ e, c4g e 1 = c4a * e ^ 2 / 2 := fun e => by simp only [c4g]; ring
  have hgL : ∀ e, c4g e 0 = c4a * e ^ 2 / 2 + c4κ * e ^ 2 := fun e => by simp only [c4g]; ring
  have hcH : c4wH - c4g (1 / c4a) 1 = Real.log (10 / 9) := by simp only [c4wH]; ring
  have hcL : c4wL - c4g 1 0 = Real.log (10 / 11) := by simp only [c4wL]; ring
  have hinv : c4a * (1 / c4a) = 1 := by field_simp
  have hfeas : C4Feas (fun c => -Real.exp (-c)) c4g 1 0 (1 / 2) (-1) c4wH (1 / c4a) c4wL 1 := by
    refine ⟨by positivity, by norm_num, ?_, ?_, ?_⟩
    · rw [hcH, hcL]; simp only [e9, e11]; norm_num
    · have : c4wL - c4g 1 1 = Real.log (10 / 11) + c4κ := by
        simp only [c4wL, hgH, hgL]; ring
      rw [this, hcH]; simp only [c4κ]; linarith
    · have h1 : 1 ≤ 1 / c4a := by rw [le_div_iff₀ ha0]; linarith
      have h2 : 1 ≤ (1 / c4a) ^ 2 := by nlinarith
      have : c4wH - c4g (1 / c4a) 0 = Real.log (10 / 9) - c4κ * (1 / c4a) ^ 2 := by
        simp only [c4wH, hgH, hgL]; ring
      rw [this, hcL]
      simp only [c4κ] at hκ0 ⊢
      nlinarith
  refine ⟨hfeas, fun wH' eH' wL' eL' hf => ?_, ?_, ?_⟩
  · obtain ⟨hH0, hL0, hIR, hiii, _⟩ := hf
    set cH := wH' - c4g eH' 1
    set cL := wL' - c4g eL' 0
    have hiii' : cL + c4κ * eL' ^ 2 ≤ cH := by
      have : wL' - c4g eL' 1 = cL + c4κ * eL' ^ 2 := by simp only [cL, hgH, hgL]; ring
      linarith
    have hprof : c4Prof id (1 / 2) wH' eH' wL' eL' =
        1 / 2 * (eH' - c4a * eH' ^ 2 / 2 - cH) +
          1 / 2 * (eL' - (c4a * eL' ^ 2 / 2 + c4κ * eL' ^ 2) - cL) := by
      simp only [c4Prof, id, cH, cL, hgH, hgL]; ring
    have hprof0 : c4Prof id (1 / 2) c4wH (1 / c4a) c4wL 1 =
        1 / 2 * (1 / c4a - c4a * (1 / c4a) ^ 2 / 2 - Real.log (10 / 9)) +
          1 / 2 * (1 - (c4a * 1 ^ 2 / 2 + c4κ * 1 ^ 2) - Real.log (10 / 11)) := by
      simp only [c4Prof, id, ← hcH, ← hcL, hgH, hgL]; ring
    rw [hprof, hprof0]
    have b1 := c4_exp_bound (c := cH) e9 (by norm_num)
    have b2 := c4_exp_bound (c := cL) e11 (by norm_num)
    have hIR' : -1 ≤ 1 / 2 * -Real.exp (-cH) + (1 - 1 / 2) * -Real.exp (-cL) := hIR
    have s1 : eH' - c4a * eH' ^ 2 / 2 ≤ 1 / c4a - c4a * (1 / c4a) ^ 2 / 2 := by
      have : 1 / c4a - c4a * (1 / c4a) ^ 2 / 2 - (eH' - c4a * eH' ^ 2 / 2) =
          c4a / 2 * (eH' - 1 / c4a) ^ 2 := by
        field_simp; ring
      nlinarith [sq_nonneg (eH' - 1 / c4a)]
    have s2 : 1 / 2 * (eL' - (c4a * eL' ^ 2 / 2 + c4κ * eL' ^ 2)) - 1 / 20 * (c4κ * eL' ^ 2) ≤
        1 / 2 * (1 - (c4a * 1 ^ 2 / 2 + c4κ * 1 ^ 2)) - 1 / 20 * c4κ := by
      have : 1 / 2 * (1 - (c4a * 1 ^ 2 / 2 + c4κ * 1 ^ 2)) - 1 / 20 * c4κ -
          (1 / 2 * (eL' - (c4a * eL' ^ 2 / 2 + c4κ * eL' ^ 2)) - 1 / 20 * (c4κ * eL' ^ 2)) =
          1 / 4 * (eL' - 1) ^ 2 := by simp only [c4a]; ring
      nlinarith [sq_nonneg (eL' - 1)]
    have hκdef : c4κ = Real.log (10 / 9) - Real.log (10 / 11) := rfl
    linarith
  · rw [lt_div_iff₀ hb0]; linarith
  · rw [hcH, hcL]; linarith

/-- **Exercise 14.C.4, the theorems applied to the instance**: in the instance the participation
constraint and (iii) bind, `e_H = e*_H`, and the distortion `e_L = 1 < e*_L` is strict. -/
theorem exercise_14_C_4_instance_applied :
    1 / 2 * -Real.exp (-(c4wH - c4g (1 / c4a) 1)) +
      (1 - 1 / 2) * -Real.exp (-(c4wL - c4g 1 0)) = -1 ∧ (1 : ℝ) < 1 / (1 - c4κ / 5) ∧
      c4wH - c4g (1 / c4a) 1 = c4wL - c4g 1 0 + (c4g 1 0 - c4g 1 1) := by
  obtain ⟨hf, hopt, -, -⟩ := exercise_14_C_4_instance
  have hκ0 : 0 < c4κ := by
    have : Real.log (10 / 11) < Real.log (10 / 9) := Real.log_lt_log (by norm_num) (by norm_num)
    simp only [c4κ]; linarith
  have hκ1 : c4κ < 1 / 4 := by
    have h1 := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 10 / 9) (by norm_num)
    have h2 := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 11 / 10) (by norm_num)
    have e : Real.log (10 / 11) = -Real.log (11 / 10) := by rw [← Real.log_inv]; norm_num
    simp only [c4κ]; linarith
  have ha0 : 0 < c4a := by simp only [c4a]; linarith
  have hb0 : 0 < 1 - c4κ / 5 := by linarith
  have hgD : ∀ e, c4g e 0 - c4g e 1 = c4κ * e ^ 2 := fun e => by simp only [c4g]; ring
  have hD : StrictMonoOn (fun e => c4g e 0 - c4g e 1) (Ici 0) := by
    intro x hx y hy hxy
    simp only [hgD]
    simp only [mem_Ici] at hx hy
    exact mul_lt_mul_of_pos_left (by nlinarith) hκ0
  have hS : ∀ (c x : ℝ), 0 < c → 0 ≤ x → x ≠ 1 / c →
      x - c * x ^ 2 / 2 < 1 / c - c * (1 / c) ^ 2 / 2 := by
    intro c x hc _ hne
    have : 1 / c - c * (1 / c) ^ 2 / 2 - (x - c * x ^ 2 / 2) = c / 2 * (x - 1 / c) ^ 2 := by
      field_simp; ring
    have := mul_pos (half_pos hc) (pow_pos (abs_pos.2 (sub_ne_zero.2 hne)) 2)
    rw [sq_abs] at this
    linarith
  have hgL : ∀ e, c4g e 0 = (1 - c4κ / 5) * e ^ 2 / 2 := fun e => by simp only [c4g, c4a]; ring
  have hgH : ∀ e, c4g e 1 = c4a * e ^ 2 / 2 := fun e => by simp only [c4g]; ring
  have hstrict := exercise_14_C_4_strict (v := fun c => -Real.exp (-c))
    (dv := fun c => Real.exp (-c)) (prof := id)
    (g := c4g) (θH := 1) (θL := 0) (lam := 1 / 2) (ubar := -1) (esH := 1 / c4a)
    (esL := 1 / (1 - c4κ / 5)) (sL := 1 - (1 - c4κ / 5) * (1 / (1 - c4κ / 5)))
    (dD := 2 * c4κ * (1 / (1 - c4κ / 5))) (by norm_num) (by norm_num) exA_strictConcave
    exA_hasDeriv (fun _ => Real.exp_pos _) hD (fun t => by simp [c4g]) (by positivity)
    (by positivity)
    (fun x hx hne => by simp only [id, hgH]; exact hS c4a x ha0 hx hne)
    (fun x hx hne => by simp only [id, hgL]; exact hS _ x hb0 hx hne)
    (one_div_le_one_div_of_le ha0 (by simp only [c4a]; linarith))
    (by
      have := ((hasDerivAt_id' (1 / (1 - c4κ / 5))).sub
        (((hasDerivAt_pow 2 (1 / (1 - c4κ / 5))).const_mul (1 - c4κ / 5)).div_const 2))
      simp only [id, hgL]
      convert this using 1; ring)
    (by
      have := (hasDerivAt_pow 2 (1 / (1 - c4κ / 5))).const_mul c4κ
      simp only [hgD]
      convert this using 1; ring)
    (by positivity) hf hopt
  have hchar := exercise_14_C_4 (v := fun c => -Real.exp (-c))
    (dv := fun c => Real.exp (-c)) (prof := id)
    (g := c4g) (θH := 1) (θL := 0) (lam := 1 / 2) (ubar := -1) (esH := 1 / c4a)
    (esL := 1 / (1 - c4κ / 5)) (by norm_num) (by norm_num) exA_strictConcave
    exA_hasDeriv (fun _ => Real.exp_pos _) hD (fun t => by simp [c4g]) (by positivity)
    (by positivity)
    (fun x hx hne => by simp only [id, hgH]; exact hS c4a x ha0 hx hne)
    (fun x hx hne => by simp only [id, hgL]; exact hS _ x hb0 hx hne)
    (one_div_le_one_div_of_le ha0 (by simp only [c4a]; linarith)) hf hopt
  exact ⟨hchar.1, hstrict, hchar.2.1⟩

end MWG.PrincipalAgent
