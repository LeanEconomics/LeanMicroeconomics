/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPositiveEquilibriumTheory.Tatonnement
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Existence of tâtonnement trajectories (MWG Section 17.H, pp. 621-622)

The book takes the trajectories of (17.H.1) as given. This module proves that they exist for all
`t ≥ 0` when `z` is continuously differentiable on `ℝ^L_{++}`, satisfies Walras' law, and pushes
small prices up: for every level `N > 0` of the weighted norm there is `η > 0` with `zₗ(q) > 0`
whenever `qₗ ≤ η` (`tat_exists`).

* Local existence with a uniform time step on the invariant region
  `{q : |q|²_c = |p(0)|²_c, qₗ ≥ η₁}` is Picard-Lindelöf (Mathlib's `IsPicardLindelof`), with the
  solution kept in a ball inside a compact box of `ℝ^L_{++}` (`tex_picard`).
* On each step the weighted norm is constant (Walras' law) and no price falls below `η₁`
  (a comparison argument, `tex_piece`), so the steps can be concatenated (`tex_glue`).
* Instance: the one-consumer Cobb-Douglas economy (`a, ω ≫ 0`) for any speeds `c ≫ 0` and any
  initial `p(0) ≫ 0` (`cd1_tat_exists`); its trajectories converge to the ray of the equilibrium
  `p* = (aₗ/ωₗ)ₗ` (`cd1_tat_converges`), a worked instance of Proposition 17.H.1.
-/

namespace MWG.PositiveEquilibriumTheory

open Filter Topology Set Metric
open scoped NNReal

/-! ### Picard-Lindelöf on `[0, h]`, keeping the solution in the ball -/

open ODE in
/-- Picard-Lindelöf for an autonomous field `f`, Lipschitz and bounded by `Lb` on the closed ball
`B(x, a)`, on `[0, h]` with `Lb h ≤ a`: a solution from `x` exists and stays in `B(x, a)`. -/
theorem tex_picard {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : E → E} {x : E} {a Lb K : ℝ≥0} {h : ℝ} (hh : 0 ≤ h)
    (hb : ∀ y ∈ closedBall x a, ‖f y‖ ≤ Lb) (hl : LipschitzOnWith K f (closedBall x a))
    (hm : (Lb : ℝ) * h ≤ a) :
    ∃ α : ℝ → E, α 0 = x ∧ ∀ t ∈ Icc 0 h,
      HasDerivWithinAt α (f (α t)) (Icc 0 h) t ∧ α t ∈ closedBall x a := by
  have hf : IsPicardLindelof (fun _ => f) (tmin := 0) (tmax := h) ⟨0, le_rfl, hh⟩ x a 0 Lb K :=
    IsPicardLindelof.of_time_independent hb hl (by simpa [hh] using hm)
  have hx : x ∈ closedBall x ((0 : ℝ≥0) : ℝ) := mem_closedBall_self le_rfl
  obtain ⟨α, hα⟩ := FunSpace.exists_isFixedPt_next hf hx
  refine ⟨α.compProj, ?_, fun t ht => ⟨?_, α.compProj_mem_closedBall hf.mul_max_le⟩⟩
  · have := FunSpace.next_apply₀ hf hx α
    rw [hα] at this
    rw [FunSpace.compProj_of_mem ⟨le_rfl, hh⟩]
    exact this
  · apply hasDerivWithinAt_picard_Icc (t₀ := 0) ⟨le_rfl, hh⟩ hf.continuousOn_uncurry
      α.continuous_compProj.continuousOn (fun _ _ ↦ α.compProj_mem_closedBall hf.mul_max_le)
      x ht |>.congr_of_mem _ ht
    intro t' ht'
    nth_rw 1 [← hα]
    rw [FunSpace.compProj_of_mem ht', FunSpace.next_apply]

/-! ### Concatenating steps -/

/-- Concatenation of solutions with a uniform time step. If from every point `x` of a set `R` a
solution `φ x` of `dq/dt = v(q)` exists on `[0, h]`, stays in `U` and ends in `R`, then from every
`x₀ ∈ R` there is a solution on `[0, ∞)` with values in `U`. -/
theorem tex_glue {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {v : E → E}
    {R U : Set E} {h : ℝ} (hh : 0 < h) (φ : E → ℝ → E) (hφ0 : ∀ x ∈ R, φ x 0 = x)
    (hφd : ∀ x ∈ R, ∀ t ∈ Icc 0 h, HasDerivWithinAt (φ x) (v (φ x t)) (Icc 0 h) t)
    (hφU : ∀ x ∈ R, ∀ t ∈ Icc 0 h, φ x t ∈ U) (hφR : ∀ x ∈ R, φ x h ∈ R) {x₀ : E}
    (hx₀ : x₀ ∈ R) :
    ∃ p : ℝ → E, p 0 = x₀ ∧ ∀ t, 0 ≤ t → p t ∈ U ∧ HasDerivWithinAt p (v (p t)) (Ici 0) t := by
  let y : ℕ → E := fun n => Nat.rec x₀ (fun _ y => φ y h) n
  have hy0 : y 0 = x₀ := rfl
  have hys : ∀ n, y (n + 1) = φ (y n) h := fun n => rfl
  have hyR : ∀ n, y n ∈ R := by
    intro n
    induction n with
    | zero => exact hx₀
    | succ n ih => rw [hys]; exact hφR _ ih
  set p : ℝ → E := fun t => φ (y ⌊t / h⌋₊) (t - ⌊t / h⌋₊ * h) with hp
  set piece : ℕ → ℝ → E := fun n u => φ (y n) (u - n * h) with hpiece
  have hfloor : ∀ (n : ℕ) (u : ℝ), n * h ≤ u → u < (n + 1) * h → ⌊u / h⌋₊ = n := by
    intro n u h1 h2
    have hu : 0 ≤ u / h := div_nonneg ((by positivity : (0 : ℝ) ≤ n * h).trans h1) hh.le
    rw [Nat.floor_eq_iff hu, le_div_iff₀ hh, div_lt_iff₀ hh]
    exact ⟨h1, h2⟩
  have hA : ∀ (n : ℕ) (u : ℝ), u ∈ Icc (n * h) ((n + 1) * h) → p u = piece n u := by
    intro n u hu
    rcases lt_or_eq_of_le hu.2 with hlt | heq
    · simp only [hp, hpiece, hfloor n u hu.1 hlt]
    · have hf1 : ⌊u / h⌋₊ = n + 1 := by
        rw [heq]
        have := hfloor (n + 1) ((n + 1) * h) (by push_cast; exact le_rfl)
          (by push_cast; nlinarith)
        exact_mod_cast this
      simp only [hp, hpiece, hf1, hys]
      rw [heq]
      push_cast
      rw [sub_self, hφ0 _ (hφR _ (hyR n)), show (n + 1 : ℝ) * h - n * h = h by ring]
  have hpieced : ∀ (n : ℕ) (u : ℝ), u ∈ Icc (n * h) ((n + 1) * h) →
      HasDerivWithinAt p (v (p u)) (Icc (n * h) ((n + 1) * h)) u := by
    intro n u hu
    have hu' : u - n * h ∈ Icc 0 h := ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have hmaps : MapsTo (fun w : ℝ => id w - n * h) (Icc (n * h) ((n + 1) * h)) (Icc 0 h) :=
      fun w hw => ⟨by simp only [id]; linarith [hw.1], by simp only [id]; linarith [hw.2]⟩
    have h1 := (hφd (y n) (hyR n) (u - n * h) hu').scomp u
      ((hasDerivWithinAt_id u (Icc (n * h) ((n + 1) * h))).sub_const (n * h)) hmaps
    rw [one_smul] at h1
    have h2 : HasDerivWithinAt (piece n) (v (piece n u)) (Icc (n * h) ((n + 1) * h)) u := h1
    rw [← hA n u hu] at h2
    exact h2.congr_of_mem (fun w hw => hA n w hw) hu
  have hnt : ∀ t, 0 ≤ t → (⌊t / h⌋₊ : ℝ) * h ≤ t ∧ t < ((⌊t / h⌋₊ : ℝ) + 1) * h := by
    intro t ht
    have h1 := Nat.floor_le (div_nonneg ht hh.le)
    have h2 := Nat.lt_floor_add_one (t / h)
    exact ⟨(le_div_iff₀ hh).1 h1, (div_lt_iff₀ hh).1 h2⟩
  refine ⟨p, ?_, fun t ht => ⟨?_, ?_⟩⟩
  · simp only [hp, zero_div, Nat.floor_zero, Nat.cast_zero, zero_mul, sub_zero, hy0]
    exact hφ0 x₀ hx₀
  · set n := ⌊t / h⌋₊
    obtain ⟨h1, h2⟩ := hnt t ht
    rw [hA n t ⟨h1, h2.le⟩]
    exact hφU _ (hyR n) _ ⟨by linarith, by linarith⟩
  · set n := ⌊t / h⌋₊ with hn
    obtain ⟨h1, h2⟩ := hnt t ht
    have hright : HasDerivWithinAt p (v (p t)) (Ici t) t :=
      (hpieced n t ⟨h1, h2.le⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ⟨h1, h2⟩)
    rcases eq_or_lt_of_le ht with h0 | hpos
    · rw [← h0] at hright ⊢
      exact hright
    have hleft : HasDerivWithinAt p (v (p t)) (Iic t) t := by
      rcases lt_or_eq_of_le h1 with hlt | heq
      · exact (hpieced n t ⟨h1, h2.le⟩).mono_of_mem_nhdsWithin
          (Icc_mem_nhdsLE_of_mem ⟨hlt, h2.le⟩)
      · obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := by
          refine Nat.exists_eq_succ_of_ne_zero fun h0 => ?_
          rw [← hn, h0] at heq
          simp at heq
          linarith
        rw [← hn, hm] at heq
        have ht' : t = (m + 1 : ℝ) * h := by rw [← heq]; push_cast; ring
        have hmem : t ∈ Icc ((m : ℝ) * h) ((m + 1) * h) := ⟨by rw [ht']; nlinarith, ht'.le⟩
        exact (hpieced m t hmem).mono_of_mem_nhdsWithin
          (Icc_mem_nhdsLE_of_mem ⟨by rw [ht']; nlinarith, ht'.le⟩)
    have hall := hleft.union hright
    rw [Iic_union_Ici, hasDerivWithinAt_univ] at hall
    exact hall.hasDerivWithinAt


/-! ### Existence of trajectories -/

variable {L : ℕ} {c : Fin L → ℝ} {z : (Fin L → ℝ) → Fin L → ℝ}

/-- On the sphere `|q|²_c = N`, every coordinate satisfies `|qₗ| ≤ ∑ₖ √(cₖ N)`. -/
theorem tex_coord_le (hc : ∀ l, 0 < c l) {N : ℝ} {q : Fin L → ℝ} (hq : wNormSq c q = N)
    (l : Fin L) : |q l| ≤ ∑ k, Real.sqrt (c k * N) := by
  have h1 : |q l| ≤ Real.sqrt (c l * N) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (hq ▸ sq_le_wNormSq hc q l)
  exact h1.trans (Finset.single_le_sum (f := fun k => Real.sqrt (c k * N))
    (fun k _ => Real.sqrt_nonneg _) (Finset.mem_univ l))

/-- One step of the construction. A solution on `[0, h]` with values in `ℝ^L_{++}`, starting with
`|q(0)|²_c = N₀` and `qₗ(0) ≥ η₁`, keeps `|q(t)|²_c = N₀` (Walras' law) and `qₗ(t) ≥ η₁`, when
`zₗ(q) > 0` at every `q` with `|q|²_c = N₀` and `qₗ ≤ η₁`. -/
theorem tex_piece (hc : ∀ l, 0 < c l) (hW : EDWalrasLaw z) {N0 η1 h : ℝ}
    (hrep : ∀ q ∈ posOrthant L, wNormSq c q = N0 → ∀ l, q l ≤ η1 → 0 < z q l)
    {α : ℝ → Fin L → ℝ} (hpos : ∀ t ∈ Icc 0 h, α t ∈ posOrthant L)
    (hd : ∀ t ∈ Icc 0 h, HasDerivWithinAt α (tatField c z (α t)) (Icc 0 h) t)
    (h0N : wNormSq c (α 0) = N0) (h0η : ∀ l, η1 ≤ α 0 l) :
    ∀ t ∈ Icc 0 h, wNormSq c (α t) = N0 ∧ ∀ l, η1 ≤ α t l := by
  have hright : ∀ t ∈ Ico 0 h, HasDerivWithinAt α (tatField c z (α t)) (Ici t) t :=
    fun t ht => (hd t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht)
  have hcont : ContinuousOn α (Icc 0 h) := fun t ht => (hd t ht).continuousWithinAt
  have hN : ∀ t ∈ Icc 0 h, wNormSq c (α t) = N0 := by
    intro t ht
    have := constant_of_has_deriv_right_zero (f := fun u => wNormSq c (α u))
      ((continuous_wNormSq c).comp_continuousOn hcont) (fun u hu => by
        have := tatField_hasDeriv_wNormSq hc (hright u hu)
        rwa [hW _ (hpos u (Ico_subset_Icc_self hu)), mul_zero] at this) t ht
    simpa [h0N] using this
  refine fun t ht => ⟨hN t ht, fun l => ?_⟩
  have := image_le_of_deriv_right_lt_deriv_boundary' (f := fun u => -α u l)
    (f' := fun u => -(c l * z (α u) l)) (B := fun _ => -η1) (B' := fun _ => 0)
    (fun u hu => ((continuous_apply l).continuousAt.comp_continuousWithinAt (hcont u hu)).neg)
    (fun u hu => (hasDerivWithinAt_pi.1 (hright u hu) l).neg)
    (by simpa using h0η l) continuousOn_const (fun _ _ => hasDerivWithinAt_const _ _ _)
    (fun u hu heq => by
      have hl : α u l ≤ η1 := by linarith
      have := hrep (α u) (hpos u (Ico_subset_Icc_self hu)) (hN u (Ico_subset_Icc_self hu)) l hl
      have := mul_pos (hc l) this
      linarith) ht
  linarith

/-- **(17.H.1)** (MWG, p. 621), existence of trajectories. Let `z` be continuously
differentiable on `ℝ^L_{++}` and satisfy Walras' law, and suppose that small prices rise: for
every `N > 0` there is `η > 0` with `zₗ(q) > 0` whenever `q ≫ 0`, `|q|²_c = N` and `qₗ ≤ η`. Then
from every `p(0) ≫ 0` there is a tâtonnement trajectory defined for all `t ≥ 0`. -/
theorem tat_exists [NeZero L] (hc : ∀ l, 0 < c l) (hW : EDWalrasLaw z)
    (hz : ContDiffOn ℝ 1 z (posOrthant L))
    (hrep : ∀ N : ℝ, 0 < N → ∃ η > 0, ∀ q ∈ posOrthant L, wNormSq c q = N → ∀ l, q l ≤ η →
      0 < z q l)
    {p0 : Fin L → ℝ} (hp0 : p0 ∈ posOrthant L) :
    ∃ p : ℝ → Fin L → ℝ, p 0 = p0 ∧ IsTatPath c z p := by
  set N0 := wNormSq c p0 with hN0def
  have hN0 : 0 < N0 := wNormSq_pos hc (posOrthant_ne_zero hp0)
  obtain ⟨η, hη, hrepη⟩ := hrep N0 hN0
  obtain ⟨k0, -, hk0⟩ := Finset.exists_min_image Finset.univ p0 Finset.univ_nonempty
  set η1 := min η (p0 k0) with hη1def
  have hη1 : 0 < η1 := lt_min hη (hp0 k0)
  set Mx := ∑ k, Real.sqrt (c k * N0) with hMx
  set Bx : Set (Fin L → ℝ) := Icc (fun _ => η1 / 2) (fun _ => Mx + η1 / 2) with hBx
  have hBpos : Bx ⊆ posOrthant L := fun q hq l => lt_of_lt_of_le (half_pos hη1) (hq.1 l)
  set v := tatField c z with hvdef
  have hv : ContDiffOn ℝ 1 v (posOrthant L) :=
    contDiffOn_pi.2 fun l => contDiffOn_const.mul (contDiffOn_pi.1 hz l)
  obtain ⟨K, hK⟩ := (hv.mono hBpos).exists_lipschitzOnWith one_ne_zero (convex_Icc _ _)
    isCompact_Icc
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := fun _ : Fin L => η1 / 2)
    (b := fun _ => Mx + η1 / 2)).exists_bound_of_continuousOn (hv.mono hBpos).continuousOn
  set Lb : ℝ≥0 := ⟨max C 0, le_max_right _ _⟩ with hLb
  set a : ℝ≥0 := ⟨η1 / 2, (half_pos hη1).le⟩ with ha
  set h : ℝ := (a : ℝ) / (Lb + 1) with hh
  have hhpos : 0 < h := div_pos (half_pos hη1) (by positivity)
  set R : Set (Fin L → ℝ) := {q | wNormSq c q = N0 ∧ ∀ l, η1 ≤ q l} with hR
  have hball : ∀ x ∈ R, closedBall x a ⊆ Bx := by
    intro x hx y hy
    rw [mem_closedBall, dist_eq_norm] at hy
    have hy' : ∀ l, |y l - x l| ≤ η1 / 2 := fun l => by
      have := (norm_le_pi_norm (y - x) l).trans hy
      rw [Pi.sub_apply, Real.norm_eq_abs] at this
      exact this
    refine ⟨fun l => ?_, fun l => ?_⟩
    · have h1 := hy' l
      have h2 := hx.2 l
      have := neg_abs_le (y l - x l)
      change η1 / 2 ≤ y l
      linarith
    · have h1 := hy' l
      have h2 := (le_abs_self (x l)).trans (tex_coord_le hc hx.1 l)
      have := le_abs_self (y l - x l)
      change y l ≤ Mx + η1 / 2
      linarith
  have hstep : ∀ x ∈ R, ∃ α : ℝ → Fin L → ℝ, α 0 = x ∧ ∀ t ∈ Icc 0 h,
      HasDerivWithinAt α (v (α t)) (Icc 0 h) t ∧ α t ∈ closedBall x a := by
    intro x hx
    refine tex_picard hhpos.le (Lb := Lb) (K := K)
      (fun y hy => (hC y (hball x hx hy)).trans (le_max_left _ _)) (hK.mono (hball x hx)) ?_
    have hL0 : (0 : ℝ) ≤ Lb := Lb.2
    rw [hh, mul_div_assoc']
    rw [div_le_iff₀ (by positivity)]
    nlinarith [a.2]
  choose! φ hφ using hstep
  have hrep1 : ∀ q ∈ posOrthant L, wNormSq c q = N0 → ∀ l, q l ≤ η1 → 0 < z q l :=
    fun q hq hqN l hl => hrepη q hq hqN l (hl.trans (min_le_left _ _))
  have hφR : ∀ x ∈ R, φ x h ∈ R := by
    intro x hx
    have := tex_piece hc hW hrep1 (α := φ x)
      (fun t ht => hBpos (hball x hx ((hφ x hx).2 t ht).2)) (fun t ht => ((hφ x hx).2 t ht).1)
      (by rw [(hφ x hx).1]; exact hx.1) (by rw [(hφ x hx).1]; exact hx.2) h
      ⟨hhpos.le, le_rfl⟩
    exact this
  have hx0 : p0 ∈ R := ⟨rfl, fun l => (min_le_right _ _).trans (hk0 l (Finset.mem_univ l))⟩
  obtain ⟨p, hp0', hp⟩ := tex_glue (v := v) (U := posOrthant L) hhpos φ
    (fun x hx => (hφ x hx).1) (fun x hx t ht => ((hφ x hx).2 t ht).1)
    (fun x hx t ht => hBpos (hball x hx ((hφ x hx).2 t ht).2)) hφR hx0
  exact ⟨p, hp0', fun t ht => (hp t ht).1, fun t ht => (hp t ht).2⟩


/-! ### Instance: one Cobb-Douglas consumer -/

/-- The one-consumer Cobb-Douglas excess demand is continuously differentiable on `ℝ^L_{++}`
(`ω ≫ 0`). -/
theorem cd1ED_contDiffOn [NeZero L] {a ω : Fin L → ℝ} (hω : ∀ l, 0 < ω l) :
    ContDiffOn ℝ 1 (cd1ED a ω) (posOrthant L) := by
  have hg : ContDiff ℝ 1 (fun q : Fin L → ℝ => (q, q ⬝ᵥ ω)) := by
    refine contDiff_id.prodMk ?_
    simp only [dotProduct]
    exact ContDiff.sum fun l _ => (contDiff_apply ℝ ℝ l).mul contDiff_const
  have hmaps : MapsTo (fun q : Fin L → ℝ => (q, q ⬝ᵥ ω)) (posOrthant L)
      (posOrthant L ×ˢ Ioi 0) := fun q hq =>
    ⟨hq, Finset.sum_pos (fun l _ => mul_pos (hq l) (hω l)) Finset.univ_nonempty⟩
  exact ((contDiffOn_cdDemand a).comp hg.contDiffOn hmaps).sub (contDiffOn_const (c := ω))

/-- The one-consumer Cobb-Douglas excess demand pushes small prices up: on `|q|²_c = N`, the
value of the endowment is at least `√(N/S)` with `S = ∑ₖ 1/(ωₖ² cₖ)`, so `zₗ(q) > 0` once `qₗ` is
small. -/
theorem cd1ED_repel [NeZero L] {a ω : Fin L → ℝ} (ha : ∀ l, 0 < a l) (hω : ∀ l, 0 < ω l)
    (hc : ∀ l, 0 < c l) {N : ℝ} (hN : 0 < N) :
    ∃ η > 0, ∀ q ∈ posOrthant L, wNormSq c q = N → ∀ l, q l ≤ η → 0 < cd1ED a ω q l := by
  set S := ∑ k, 1 / (ω k ^ 2 * c k) with hS
  have hSpos : 0 < S := Finset.sum_pos (fun k _ => by have := hω k; have := hc k; positivity)
    Finset.univ_nonempty
  set W0 := Real.sqrt (N / S) with hW0
  have hW0pos : 0 < W0 := Real.sqrt_pos.2 (div_pos hN hSpos)
  set A := ∑ k, a k with hA
  have hApos : 0 < A := Finset.sum_pos (fun k _ => ha k) Finset.univ_nonempty
  obtain ⟨k0, -, hk0⟩ := Finset.exists_min_image Finset.univ (fun l => a l / (2 * A * ω l))
    Finset.univ_nonempty
  set m := a k0 / (2 * A * ω k0) with hm
  have hmpos : 0 < m := div_pos (ha k0) (by have := hω k0; positivity)
  refine ⟨W0 * m, mul_pos hW0pos hmpos, fun q hq hqN l hl => ?_⟩
  -- the value of the endowment is at least `W0`
  set w := q ⬝ᵥ ω with hw
  have hwpos : 0 < w := Finset.sum_pos (fun k _ => mul_pos (hq k) (hω k)) Finset.univ_nonempty
  have hqk : ∀ k, q k ≤ w / ω k := fun k => by
    rw [le_div_iff₀ (hω k)]
    exact Finset.single_le_sum (f := fun j => q j * ω j)
      (fun j _ => (mul_pos (hq j) (hω j)).le) (Finset.mem_univ k)
  have hNle : N ≤ w ^ 2 * S := by
    rw [← hqN, hS, Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    have h1 : q k ^ 2 ≤ (w / ω k) ^ 2 := pow_le_pow_left₀ (hq k).le (hqk k) 2
    have hck := hc k
    have hωk := hω k
    rw [div_pow] at h1
    calc q k ^ 2 / c k ≤ w ^ 2 / ω k ^ 2 / c k := div_le_div_of_nonneg_right h1 hck.le
      _ = w ^ 2 * (1 / (ω k ^ 2 * c k)) := by field_simp
  have hwW : W0 ≤ w := by
    rw [hW0, ← Real.sqrt_sq hwpos.le]
    exact Real.sqrt_le_sqrt ((div_le_iff₀ hSpos).2 hNle)
  -- hence `zₗ(q) > 0`
  have hml : m ≤ a l / (2 * A * ω l) := hk0 l (Finset.mem_univ l)
  have hωl := hω l
  have hql := hq l
  have hal := ha l
  have h1 : A * ω l * q l ≤ a l * W0 / 2 := by
    have : q l ≤ W0 * (a l / (2 * A * ω l)) :=
      hl.trans (mul_le_mul_of_nonneg_left hml hW0pos.le)
    have h2 : 0 < A * ω l := mul_pos hApos hωl
    calc A * ω l * q l ≤ A * ω l * (W0 * (a l / (2 * A * ω l))) :=
          mul_le_mul_of_nonneg_left this h2.le
      _ = a l * W0 / 2 := by field_simp
  have h2 : A * ω l * q l < a l * w := by nlinarith
  simp only [cd1ED, cdDemand, Pi.sub_apply, sub_pos, ← hA, ← hw]
  rw [div_mul_div_comm, lt_div_iff₀ (mul_pos hApos hql)]
  linarith

/-- The equilibrium price vector of one Cobb-Douglas consumer: `p*ₗ = aₗ/ωₗ`. -/
theorem cd1ED_eqm [NeZero L] {a ω : Fin L → ℝ} (ha : ∀ l, 0 < a l) (hω : ∀ l, 0 < ω l) :
    IsEqmPrice (cd1ED a ω) (fun l => a l / ω l) := by
  refine ⟨fun l => div_pos (ha l) (hω l), funext fun l => ?_⟩
  have hdot : (fun l => a l / ω l) ⬝ᵥ ω = ∑ k, a k := by
    simp only [dotProduct]
    exact Finset.sum_congr rfl fun k _ => by field_simp [(hω k).ne']
  have hA : 0 < ∑ k, a k := Finset.sum_pos (fun k _ => ha k) Finset.univ_nonempty
  simp only [cd1ED, cdDemand, Pi.sub_apply, hdot, Pi.zero_apply]
  have := (ha l).ne'
  have := (hω l).ne'
  field_simp
  ring

/-- **(17.H.1)**, instance of existence (MWG, p. 621). For one Cobb-Douglas consumer (`a, ω ≫ 0`),
any speeds `c ≫ 0` and any `p(0) ≫ 0`, a tâtonnement trajectory exists for all `t ≥ 0`. -/
theorem cd1_tat_exists [NeZero L] {a ω : Fin L → ℝ} (ha : ∀ l, 0 < a l) (hω : ∀ l, 0 < ω l)
    (hc : ∀ l, 0 < c l) {p0 : Fin L → ℝ} (hp0 : p0 ∈ posOrthant L) :
    ∃ p : ℝ → Fin L → ℝ, p 0 = p0 ∧ IsTatPath c (cd1ED a ω) p :=
  tat_exists hc (cd1ED_isStandard ha hω).walras (cd1ED_contDiffOn hω)
    (fun _ hN => cd1ED_repel ha hω hc hN) hp0

/-- **Proposition 17.H.1**, worked instance (MWG, p. 623). For one Cobb-Douglas consumer
(`a, ω ≫ 0`, gross substitutes), any speeds `c ≫ 0` and any `p(0) ≫ 0`, a trajectory exists and
converges to a point of the equilibrium ray `{α(aₗ/ωₗ)ₗ : α > 0}`. -/
theorem cd1_tat_converges [NeZero L] {a ω : Fin L → ℝ} (ha : ∀ l, 0 < a l) (hω : ∀ l, 0 < ω l)
    (hc : ∀ l, 0 < c l) {p0 : Fin L → ℝ} (hp0 : p0 ∈ posOrthant L) :
    ∃ p : ℝ → Fin L → ℝ, p 0 = p0 ∧ IsTatPath c (cd1ED a ω) p ∧
      ∃ lam : ℝ, 0 < lam ∧ Tendsto p atTop (𝓝 (lam • fun l => a l / ω l)) := by
  obtain ⟨p, hp0', hp⟩ := cd1_tat_exists ha hω hc hp0
  exact ⟨p, hp0', hp, tat_global_stability_gs hc (cd1ED_isStandard ha hω)
    (cd1_grossSubstitute ha hω) (cd1ED_eqm ha hω) hp⟩

end MWG.PositiveEquilibriumTheory
