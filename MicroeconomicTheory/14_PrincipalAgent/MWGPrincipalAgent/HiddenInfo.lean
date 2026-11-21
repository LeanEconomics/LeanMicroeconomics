/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPrincipalAgent.Screen
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# The hidden-information model

MWG, Section 14.C, pp. 488-500, and Appendix B, pp. 504-506.

Effort `e ∈ [0, ∞)` is observable; profits are `π(e)` with `π(0) = 0`, `π' > 0`, `π'' < 0`; the
manager has utility `v(w - g(e, θ))` with `v' > 0`, `v'' < 0`, where `g(0, θ) = 0`,
`g_e(0, θ) = 0`, `g_ee > 0` and `g_eθ < 0` for `e > 0`; two states `θ_L < θ_H` with
`Prob(θ_H) = λ ∈ (0, 1)`. To cover Exercise 14.C.5 and the monopolistic screening model (14.C.10)
the owner's profit may depend on the state (`π_H`, `π_L` with `π'_H ≥ π'_L > 0`); the model of
Section 14.C is `π_H = π_L = π`. Derivatives are taken within `[0, ∞)`; `π'' < 0` and `g_ee > 0`
are used only through the strict concavity of `π` and strict convexity of `g(·, θ)` they imply,
and `g_eθ < 0` through `g_e(e, θ_H) < g_e(e, θ_L)` for `e > 0` (`hi_cross_of_deriv` derives this).

* `hi_g_theta_inconsistent`: MWG's `g_θ(e, θ) < 0` "for all `e`" contradicts `g(0, θ) = 0`; it
  is not used (correction).
* `hi_hyp`, `hi_fb_of_foc`, `hi_fb_order`: single crossing; the first-best efforts (14.C.7) and
  `e*_H > e*_L`.
* `proposition_14_C_1`, `hi_obs_foc`: Proposition 14.C.1 and the first-order conditions
  (14.C.2)-(14.C.6).
* `hi_H_prefers_L`: in state `θ_H` the manager would lie (p. 492).
* `hi_eL_pos`, `hi_foc_14_C_9`, `lemma_14_C_4`, `proposition_14_C_3`: Appendix B Step 3, (14.C.9)
  = (14.BB.7), Lemma 14.C.4, Proposition 14.C.3.
* `hi_eL_falls`: the optimal `e_L` falls as `λ / (1 - λ)` rises (p. 499).
* `footnote_17`: `e_L = 0` can be optimal only if `g_e(0, θ_L) > 0`.
* `appendix_B_steps`, `appendix_B_multipliers`: Steps 1-5 of Appendix B and the multipliers.
-/

namespace MWG.PrincipalAgent

open Set Filter Topology

/-- A function with positive derivative within `[a, ∞)` at `a` exceeds `f a` somewhere to the
right of `a`. -/
theorem hi_exists_gt_of_deriv_pos {f : ℝ → ℝ} {a d : ℝ} (hf : HasDerivWithinAt f d (Ici a) a)
    (hd : 0 < d) : ∃ y, a < y ∧ f a < f y := by
  have ht := (hasDerivWithinAt_iff_tendsto_slope.1 hf).eventually (lt_mem_nhds hd)
  have hset : Ici a \ {a} = Ioi a := by
    ext x; simp only [Set.mem_sdiff, mem_Ici, mem_singleton_iff, mem_Ioi]
    constructor
    · rintro ⟨h1, h2⟩; exact lt_of_le_of_ne h1 (Ne.symm h2)
    · intro h; exact ⟨h.le, h.ne'⟩
  rw [hset] at ht
  obtain ⟨y, hy, hya⟩ := (ht.and self_mem_nhdsWithin).exists
  refine ⟨y, hya, ?_⟩
  rw [slope_def_field, lt_div_iff₀ (sub_pos.2 hya)] at hy
  linarith

/-- The derivative of a strictly concave function is strictly decreasing. -/
theorem hi_deriv_anti {S : Set ℝ} {h : ℝ → ℝ} (hc : StrictConcaveOn ℝ S h) {x y dx dy : ℝ}
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) (hdx : HasDerivWithinAt h dx S x)
    (hdy : HasDerivWithinAt h dy S y) : dy < dx := by
  have h1 := tpa_tangent_lt hc hx hy hxy.ne' hdx
  have h2 := tpa_tangent_lt hc hy hx hxy.ne hdy
  nlinarith

/-- The derivative of a strictly convex function is strictly increasing. -/
theorem hi_deriv_mono {S : Set ℝ} {h : ℝ → ℝ} (hc : StrictConvexOn ℝ S h) {x y dx dy : ℝ}
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) (hdx : HasDerivWithinAt h dx S x)
    (hdy : HasDerivWithinAt h dy S y) : dx < dy := by
  have := hi_deriv_anti hc.neg hx hy hxy hdx.neg hdy.neg
  linarith

/-- **Correction** (MWG, p. 489). The assumptions `g(0, θ) = 0` for all `θ` and `g_θ(e, θ) < 0`
"for all `e`" are inconsistent: at `e = 0` the function `θ ↦ g(0, θ)` is constant, so its
derivative vanishes. (Only `g_θ < 0` for `e > 0` is consistent; it is not needed here.) -/
theorem hi_g_theta_inconsistent (g gθ : ℝ → ℝ → ℝ) (hg0 : ∀ θ, g 0 θ = 0) (θ : ℝ)
    (hd : HasDerivAt (fun θ => g 0 θ) (gθ 0 θ) θ) : ¬ gθ 0 θ < 0 := by
  have hc : (fun θ => g 0 θ) = fun _ => 0 := funext hg0
  rw [hc] at hd
  rw [hd.unique (hasDerivAt_const θ 0)]
  exact lt_irrefl 0

/-- **The single-crossing assumption** (MWG, p. 489): `g_eθ < 0` for `e > 0` gives
`g_e(e, θ_H) < g_e(e, θ_L)` when `θ_L < θ_H`. -/
theorem hi_cross_of_deriv {ge geθ : ℝ → ℝ → ℝ} {e : ℝ}
    (hd : ∀ θ, HasDerivAt (fun θ => ge e θ) (geθ e θ) θ) (hneg : ∀ θ, geθ e θ < 0)
    {θL θH : ℝ} (hθ : θL < θH) : ge e θH < ge e θL :=
  strictAnti_of_hasDerivAt_neg hd hneg hθ

/-- **Section 14.C** (MWG, pp. 489-490). The hidden-information model with state-dependent profits
`π_H`, `π_L` (derivatives `dpH`, `dpL`), disutility `g(e, θ)` with `g_e = ge`, utility `v` with
`v' = dv`, the two states, `λ = Prob(θ_H)`, the reservation utility `ū`, and `c = v⁻¹(ū)`. -/
structure HIModel where
  pH : ℝ → ℝ
  pL : ℝ → ℝ
  dpH : ℝ → ℝ
  dpL : ℝ → ℝ
  g : ℝ → ℝ → ℝ
  ge : ℝ → ℝ → ℝ
  v : ℝ → ℝ
  dv : ℝ → ℝ
  θL : ℝ
  θH : ℝ
  lam : ℝ
  ubar : ℝ
  c : ℝ

namespace HIModel

/-- **Section 14.C** (MWG, pp. 489-490). The standing assumptions. -/
structure Standing (M : HIModel) : Prop where
  pH_zero : M.pH 0 = 0
  pL_zero : M.pL 0 = 0
  pH_deriv : ∀ e, 0 ≤ e → HasDerivWithinAt M.pH (M.dpH e) (Ici 0) e
  pL_deriv : ∀ e, 0 ≤ e → HasDerivWithinAt M.pL (M.dpL e) (Ici 0) e
  dpL_pos : ∀ e, 0 ≤ e → 0 < M.dpL e
  dp_le : ∀ e, 0 ≤ e → M.dpL e ≤ M.dpH e
  pH_conc : StrictConcaveOn ℝ (Ici 0) M.pH
  pL_conc : StrictConcaveOn ℝ (Ici 0) M.pL
  g_zero : ∀ θ, M.g 0 θ = 0
  g_deriv : ∀ θ e, 0 ≤ e → HasDerivWithinAt (fun e => M.g e θ) (M.ge e θ) (Ici 0) e
  ge_zero : ∀ θ, M.ge 0 θ = 0
  g_conv : ∀ θ, StrictConvexOn ℝ (Ici 0) fun e => M.g e θ
  θ_lt : M.θL < M.θH
  ge_cross : ∀ e, 0 < e → M.ge e M.θH < M.ge e M.θL
  lam_pos : 0 < M.lam
  lam_lt : M.lam < 1
  v_deriv : ∀ w, HasDerivAt M.v (M.dv w) w
  dv_pos : ∀ w, 0 < M.dv w
  v_conc : StrictConcaveOn ℝ univ M.v
  v_c : M.v M.c = M.ubar

/-- The screening program (14.C.8) of the model (with `c = v⁻¹(ū)`). -/
def scr (M : HIModel) : Screen := ⟨M.pH, M.pL, M.g, M.θL, M.θH, M.lam, M.c⟩

/-- `v` is strictly increasing. -/
theorem hi_v_strictMono {M : HIModel} (hM : M.Standing) : StrictMono M.v :=
  strictMono_of_hasDerivAt_pos hM.v_deriv hM.dv_pos

/-- The derivative of `D(e) = g(e, θ_L) - g(e, θ_H)`. -/
theorem hi_D_deriv {M : HIModel} (hM : M.Standing) {e : ℝ} (he : 0 ≤ e) :
    HasDerivWithinAt M.scr.D (M.ge e M.θL - M.ge e M.θH) (Ici 0) e :=
  (hM.g_deriv M.θL e he).sub (hM.g_deriv M.θH e he)

/-- **Single crossing** (MWG, p. 490): the standing assumptions give the hypotheses of the
screening program; in particular `D` is strictly increasing on `[0, ∞)`. -/
theorem hi_hyp {M : HIModel} (hM : M.Standing) : M.scr.Hyp := by
  refine ⟨hM.lam_pos, hM.lam_lt, ?_, ?_⟩
  · change M.g 0 M.θL - M.g 0 M.θH = 0
    rw [hM.g_zero, hM.g_zero, sub_self]
  · refine strictMonoOn_of_hasDerivWithinAt_pos (convex_Ici 0)
      (fun e he => (hi_D_deriv hM he).continuousWithinAt) (f' := fun e => M.ge e M.θL - M.ge e M.θH)
      (fun e he => ?_) (fun e he => ?_)
    · rw [interior_Ici] at he ⊢
      exact (hi_D_deriv hM (le_of_lt he)).mono Ioi_subset_Ici_self
    · rw [interior_Ici] at he
      exact sub_pos.2 (hM.ge_cross e he)

/-- The surplus `S_H(e) = π_H(e) - g(e, θ_H)` is strictly concave. -/
theorem hi_SH_conc {M : HIModel} (hM : M.Standing) : StrictConcaveOn ℝ (Ici 0) M.scr.SH :=
  hM.pH_conc.sub (hM.g_conv M.θH)

/-- The surplus `S_L(e) = π_L(e) - g(e, θ_L)` is strictly concave. -/
theorem hi_SL_conc {M : HIModel} (hM : M.Standing) : StrictConcaveOn ℝ (Ici 0) M.scr.SL :=
  hM.pL_conc.sub (hM.g_conv M.θL)

theorem hi_SH_deriv {M : HIModel} (hM : M.Standing) {e : ℝ} (he : 0 ≤ e) :
    HasDerivWithinAt M.scr.SH (M.dpH e - M.ge e M.θH) (Ici 0) e :=
  (hM.pH_deriv e he).sub (hM.g_deriv M.θH e he)

theorem hi_SL_deriv {M : HIModel} (hM : M.Standing) {e : ℝ} (he : 0 ≤ e) :
    HasDerivWithinAt M.scr.SL (M.dpL e - M.ge e M.θL) (Ici 0) e :=
  (hM.pL_deriv e he).sub (hM.g_deriv M.θL e he)

/-- A critical point of a strictly concave function on `[0, ∞)` is its unique maximizer. -/
theorem hi_isFB_of_crit {S : ℝ → ℝ} (hc : StrictConcaveOn ℝ (Ici 0) S) {e : ℝ} (he : 0 ≤ e)
    (hd : HasDerivWithinAt S 0 (Ici 0) e) : Screen.IsFB S e :=
  ⟨he, fun y hy hne => by
    have := tpa_tangent_lt hc (mem_Ici.2 he) (mem_Ici.2 hy) hne hd
    simpa using this⟩

/-- **(14.C.7)** (MWG, p. 491). If `π'_H(e*) = g_e(e*, θ_H)` then `e* > 0` and `e*` is the unique
maximizer of `π_H(e) - g(e, θ_H)` on `[0, ∞)` (the first-best effort in state `θ_H`). -/
theorem hi_fbH_of_foc {M : HIModel} (hM : M.Standing) {e : ℝ} (he : 0 ≤ e)
    (hfoc : M.dpH e = M.ge e M.θH) : 0 < e ∧ Screen.IsFB M.scr.SH e := by
  refine ⟨?_, hi_isFB_of_crit (hi_SH_conc hM) he (by simpa [hfoc] using hi_SH_deriv hM he)⟩
  rcases he.lt_or_eq with h | rfl
  · exact h
  · exfalso
    have := hM.dp_le 0 le_rfl
    have := hM.dpL_pos 0 le_rfl
    rw [hM.ge_zero] at hfoc
    linarith

/-- **(14.C.7)** (MWG, p. 491), state `θ_L`. -/
theorem hi_fbL_of_foc {M : HIModel} (hM : M.Standing) {e : ℝ} (he : 0 ≤ e)
    (hfoc : M.dpL e = M.ge e M.θL) : 0 < e ∧ Screen.IsFB M.scr.SL e := by
  refine ⟨?_, hi_isFB_of_crit (hi_SL_conc hM) he (by simpa [hfoc] using hi_SL_deriv hM he)⟩
  rcases he.lt_or_eq with h | rfl
  · exact h
  · exfalso
    have := hM.dpL_pos 0 le_rfl
    rw [hM.ge_zero] at hfoc
    linarith

/-- **`e*_H > e*_L`** (MWG, p. 492): from (14.C.7), `g_eθ < 0`, `π'' < 0`, `g_ee > 0` (and
`π'_H ≥ π'_L` when profits depend on the state, Exercise 14.C.5). -/
theorem hi_fb_order {M : HIModel} (hM : M.Standing) {eHs eLs : ℝ} (hH0 : 0 ≤ eHs)
    (hHf : M.dpH eHs = M.ge eHs M.θH) (hL0 : 0 ≤ eLs) (hLf : M.dpL eLs = M.ge eLs M.θL) :
    eLs < eHs := by
  have hHpos := (hi_fbH_of_foc hM hH0 hHf).1
  by_contra hle
  rw [not_lt] at hle
  -- π'_L(e*_L) ≤ π'_L(e*_H) ≤ π'_H(e*_H) = g_e(e*_H, θ_H) < g_e(e*_H, θ_L) ≤ g_e(e*_L, θ_L)
  have h1 : M.dpL eLs ≤ M.dpL eHs := by
    rcases hle.lt_or_eq with h | h
    · exact (hi_deriv_anti hM.pL_conc (mem_Ici.2 hH0) (mem_Ici.2 hL0) h (hM.pL_deriv _ hH0)
        (hM.pL_deriv _ hL0)).le
    · rw [h]
  have h2 := hM.dp_le eHs hH0
  have h3 := hM.ge_cross eHs hHpos
  have h4 : M.ge eHs M.θL ≤ M.ge eLs M.θL := by
    rcases hle.lt_or_eq with h | h
    · exact (hi_deriv_mono (hM.g_conv M.θL) (mem_Ici.2 hH0) (mem_Ici.2 hL0) h
        (hM.g_deriv _ _ hH0) (hM.g_deriv _ _ hL0)).le
    · rw [h]
  linarith

/-- The feasible contracts of (14.C.1) (MWG, p. 490): nonnegative efforts and expected utility at
least `ū`. -/
def ObsFeas (M : HIModel) (K : HIContract) : Prop :=
  0 ≤ K.eH ∧ 0 ≤ K.eL ∧
    M.ubar ≤ M.lam * M.v (K.wH - M.g K.eH M.θH) + (1 - M.lam) * M.v (K.wL - M.g K.eL M.θL)

/-- A solution of (14.C.1). -/
def IsObsOpt (M : HIModel) (K : HIContract) : Prop :=
  M.ObsFeas K ∧ ∀ K', M.ObsFeas K' → M.scr.Pi K' ≤ M.scr.Pi K

/-- The full-information contract: `e*_i` and `w*_i` with `v(w*_i - g(e*_i, θ_i)) = ū`. -/
def fbK (M : HIModel) (eHs eLs : ℝ) : HIContract :=
  ⟨M.c + M.g eHs M.θH, eHs, M.c + M.g eLs M.θL, eLs⟩

/-- **Proposition 14.C.1** (MWG, p. 492). With an observable state, the optimal contract specifies
the efforts `e*_i` with `π'(e*_i) = g_e(e*_i, θ_i)` and fully insures the manager, paying `w*_i`
with `v(w*_i - g(e*_i, θ_i)) = ū`; it is the unique optimal contract. -/
theorem proposition_14_C_1 {M : HIModel} (hM : M.Standing) {eHs eLs : ℝ} (hH0 : 0 ≤ eHs)
    (hHf : M.dpH eHs = M.ge eHs M.θH) (hL0 : 0 ≤ eLs) (hLf : M.dpL eLs = M.ge eLs M.θL) :
    M.IsObsOpt (M.fbK eHs eLs) ∧ ∀ K, M.IsObsOpt K → K = M.fbK eHs eLs := by
  have hH := (hi_fbH_of_foc hM hH0 hHf).2
  have hL := (hi_fbL_of_foc hM hL0 hLf).2
  have hl := hM.lam_pos; have hl' := hM.lam_lt
  have hmono := hi_v_strictMono hM
  have hfeas : M.ObsFeas (M.fbK eHs eLs) := by
    refine ⟨hH0, hL0, ?_⟩
    simp only [fbK, add_sub_cancel_right, hM.v_c]; linarith
  have hPifb : M.scr.Pi (M.fbK eHs eLs) = M.lam * M.scr.SH eHs + (1 - M.lam) * M.scr.SL eLs -
      M.c := by
    simp only [Screen.Pi, Screen.SH, Screen.SL, fbK, scr]; ring
  -- the bound for every feasible contract
  have key : ∀ K, M.ObsFeas K → M.c ≤ M.lam * (K.wH - M.g K.eH M.θH) +
      (1 - M.lam) * (K.wL - M.g K.eL M.θL) := by
    intro K hK
    have hJ := tpa_jensen_two hM.v_conc.concaveOn hl.le hl'.le (K.wH - M.g K.eH M.θH)
      (K.wL - M.g K.eL M.θL)
    exact hmono.le_iff_le.1 (by rw [hM.v_c]; linarith [hK.2.2])
  have hPi : ∀ K, M.scr.Pi K = M.lam * M.scr.SH K.eH + (1 - M.lam) * M.scr.SL K.eL -
      (M.lam * (K.wH - M.g K.eH M.θH) + (1 - M.lam) * (K.wL - M.g K.eL M.θL)) := by
    intro K; simp only [Screen.Pi, Screen.SH, Screen.SL, scr]; ring
  have hSHle : ∀ e, 0 ≤ e → M.scr.SH e ≤ M.scr.SH eHs := fun e he => by
    rcases eq_or_ne e eHs with rfl | hne
    · exact le_rfl
    · exact (hH.2 e he hne).le
  have hSLle : ∀ e, 0 ≤ e → M.scr.SL e ≤ M.scr.SL eLs := fun e he => by
    rcases eq_or_ne e eLs with rfl | hne
    · exact le_rfl
    · exact (hL.2 e he hne).le
  have hopt : M.IsObsOpt (M.fbK eHs eLs) := by
    refine ⟨hfeas, fun K hK => ?_⟩
    rw [hPi K, hPifb]
    nlinarith [key K hK, mul_le_mul_of_nonneg_left (hSHle _ hK.1) hl.le,
      mul_le_mul_of_nonneg_left (hSLle _ hK.2.1) (by linarith : (0:ℝ) ≤ 1 - M.lam)]
  refine ⟨hopt, fun K hK => ?_⟩
  have heq : M.scr.Pi K = M.scr.Pi (M.fbK eHs eLs) := le_antisymm (hopt.2 K hK.1) (hK.2 _ hfeas)
  rw [hPi K, hPifb] at heq
  have hk := key K hK.1
  have a1 := mul_le_mul_of_nonneg_left (hSHle _ hK.1.1) hl.le
  have a2 := mul_le_mul_of_nonneg_left (hSLle _ hK.1.2.1) (by linarith : (0:ℝ) ≤ 1 - M.lam)
  have hHe : K.eH = eHs := by
    by_contra hne
    have := mul_lt_mul_of_pos_left (hH.2 _ hK.1.1 hne) hl
    linarith
  have hLe : K.eL = eLs := by
    by_contra hne
    have := mul_lt_mul_of_pos_left (hL.2 _ hK.1.2.1 hne) (by linarith : (0:ℝ) < 1 - M.lam)
    linarith
  have hsum : M.lam * (K.wH - M.g K.eH M.θH) + (1 - M.lam) * (K.wL - M.g K.eL M.θL) = M.c := by
    linarith
  have hxeq : K.wH - M.g K.eH M.θH = K.wL - M.g K.eL M.θL := by
    by_contra hne
    have hJ := tpa_jensen_two_lt hM.v_conc hl hl' hne
    rw [hsum, hM.v_c] at hJ
    linarith [hK.1.2.2]
  have hx : K.wL - M.g K.eL M.θL = M.c := by
    rw [hxeq] at hsum; linarith
  obtain ⟨wH, eH, wL, eL⟩ := K
  simp only at hHe hLe hx hxeq
  subst hHe hLe
  have e1 : wH = M.c + M.g eH M.θH := by linarith
  have e2 : wL = M.c + M.g eL M.θL := by linarith
  simp only [fbK, e1, e2]

/-- **(14.C.2)-(14.C.6)** (MWG, pp. 490-491). At the full-information contract the first-order
conditions hold with the multiplier `γ = 1 / v'(v⁻¹(ū))`: marginal utilities of income are equal
across states (14.C.6) and the effort conditions hold with equality. -/
theorem hi_obs_foc {M : HIModel} (hM : M.Standing) {eHs eLs : ℝ}
    (hHf : M.dpH eHs = M.ge eHs M.θH) (hLf : M.dpL eLs = M.ge eLs M.θL) :
    let K := M.fbK eHs eLs
    let γ := 1 / M.dv M.c
    (-M.lam + γ * M.lam * M.dv (K.wH - M.g K.eH M.θH) = 0 ∧
    -(1 - M.lam) + γ * (1 - M.lam) * M.dv (K.wL - M.g K.eL M.θL) = 0 ∧
    M.lam * M.dpH K.eH - γ * M.lam * M.dv (K.wH - M.g K.eH M.θH) * M.ge K.eH M.θH = 0 ∧
    (1 - M.lam) * M.dpL K.eL - γ * (1 - M.lam) * M.dv (K.wL - M.g K.eL M.θL) *
      M.ge K.eL M.θL = 0 ∧
    M.dv (K.wH - M.g K.eH M.θH) = M.dv (K.wL - M.g K.eL M.θL)) := by
  intro K γ
  have hd := (hM.dv_pos M.c).ne'
  simp only [K, γ, fbK, add_sub_cancel_right]
  refine ⟨by field_simp; ring, by field_simp; ring, ?_, ?_, trivial⟩
  · rw [hHf]; field_simp; ring
  · rw [hLf]; field_simp; ring

/-- The isoprofit curve `π(e) - w = Π` meets the vertical axis `e = 0` at `w = -Π`, since
`π(0) = 0` (MWG, pp. 491-492, Figure 14.C.1). -/
theorem hi_isoprofit_axis {M : HIModel} (hM : M.Standing) (P0 w : ℝ) :
    M.pH 0 - w = P0 ↔ w = -P0 := by
  rw [hM.pH_zero]; constructor <;> intro h <;> linarith

/-- **p. 492**: facing the full-information contract, the manager in state `θ_H` strictly prefers
the `θ_L` pair, and the misrepresentation lowers the owner's profit in that state. -/
theorem hi_H_prefers_L {M : HIModel} (hM : M.Standing) {eHs eLs : ℝ} (hH0 : 0 ≤ eHs)
    (hHf : M.dpH eHs = M.ge eHs M.θH) (hL0 : 0 ≤ eLs) (hLf : M.dpL eLs = M.ge eLs M.θL)
    (hπ : M.pH = M.pL) :
    let K := M.fbK eHs eLs
    K.wH - M.g K.eH M.θH < K.wL - M.g K.eL M.θH ∧ M.pH K.eL - K.wL < M.pH K.eH - K.wH := by
  intro K
  have hLpos := (hi_fbL_of_foc hM hL0 hLf).1
  have hD := Screen.screen_D_pos (hi_hyp hM) hLpos
  have hH := (hi_fbH_of_foc hM hH0 hHf).2
  have hne : eLs ≠ eHs := (hi_fb_order hM hH0 hHf hL0 hLf).ne
  have hS := hH.2 eLs hL0 hne
  simp only [K, fbK]
  change 0 < M.g eLs M.θL - M.g eLs M.θH at hD
  change M.pH eLs - M.g eLs M.θH < M.pH eHs - M.g eHs M.θH at hS
  constructor
  · linarith
  · rw [hπ] at hS ⊢; linarith

/-- The derivative of the virtual surplus `Q(e) = (1 - λ) S_L(e) - λ D(e)`. -/
theorem hi_Q_deriv {M : HIModel} (hM : M.Standing) {e : ℝ} (he : 0 ≤ e) :
    HasDerivWithinAt M.scr.Q ((1 - M.lam) * (M.dpL e - M.ge e M.θL) -
      M.lam * (M.ge e M.θL - M.ge e M.θH)) (Ici 0) e :=
  ((hi_SL_deriv hM he).const_mul (1 - M.lam)).sub ((hi_D_deriv hM he).const_mul M.lam)

/-- **Appendix B, Step 3** (MWG, p. 505). At an optimal contract `e_L > 0`. -/
theorem hi_eL_pos {M : HIModel} (hM : M.Standing) {eHs eLs : ℝ} (hH0 : 0 ≤ eHs)
    (hHf : M.dpH eHs = M.ge eHs M.θH) (hL0 : 0 ≤ eLs) (hLf : M.dpL eLs = M.ge eLs M.θL)
    {K : HIContract} (hK : M.scr.IsOpt K) : 0 < K.eL := by
  have hH := (hi_fbH_of_foc hM hH0 hHf).2
  have hL := (hi_fbL_of_foc hM hL0 hLf).2
  have hord := (hi_fb_order hM hH0 hHf hL0 hLf).le
  obtain ⟨h0, hmax, -⟩ := (Screen.screen_opt_iff (hi_hyp hM) hH hL hord K).1 hK
  rcases h0.lt_or_eq with h | h
  · exact h
  exfalso
  have hd := hi_Q_deriv hM (le_refl (0 : ℝ))
  rw [hM.ge_zero, hM.ge_zero] at hd
  simp only [sub_zero, mul_zero] at hd
  have hpos : 0 < (1 - M.lam) * M.dpL 0 :=
    mul_pos (by linarith [hM.lam_lt]) (hM.dpL_pos 0 le_rfl)
  obtain ⟨y, hy, hgt⟩ := hi_exists_gt_of_deriv_pos hd hpos
  have := hmax y hy.le
  rw [← h] at this
  linarith

/-- An interior maximizer of `Q` on `[0, ∞)` is a critical point. -/
theorem hi_Q_crit {M : HIModel} (hM : M.Standing) {e : ℝ} (hpos : 0 < e)
    (hmax : ∀ e', 0 ≤ e' → M.scr.Q e' ≤ M.scr.Q e) :
    (1 - M.lam) * (M.dpL e - M.ge e M.θL) - M.lam * (M.ge e M.θL - M.ge e M.θH) = 0 := by
  have hd := (hi_Q_deriv hM hpos.le).hasDerivAt (Ici_mem_nhds hpos)
  have hloc : IsLocalMax M.scr.Q e :=
    Filter.mem_of_superset (Ici_mem_nhds hpos) fun y hy => hmax y hy
  exact hloc.hasDerivAt_eq_zero hd

/-- **(14.C.9) = (14.BB.7) and (14.BB.6)** (MWG, pp. 499, 506). At an optimal contract
`π'_H(e_H) = g_e(e_H, θ_H)` and
`[π'(e_L) - g_e(e_L, θ_L)] + λ/(1 - λ) [g_e(e_L, θ_H) - g_e(e_L, θ_L)] = 0`. -/
theorem hi_foc_14_C_9 {M : HIModel} (hM : M.Standing) {eHs eLs : ℝ} (hH0 : 0 ≤ eHs)
    (hHf : M.dpH eHs = M.ge eHs M.θH) (hL0 : 0 ≤ eLs) (hLf : M.dpL eLs = M.ge eLs M.θL)
    {K : HIContract} (hK : M.scr.IsOpt K) :
    M.dpH K.eH - M.ge K.eH M.θH = 0 ∧
      (M.dpL K.eL - M.ge K.eL M.θL) + M.lam / (1 - M.lam) * (M.ge K.eL M.θH - M.ge K.eL M.θL) =
        0 := by
  have hH := (hi_fbH_of_foc hM hH0 hHf).2
  have hL := (hi_fbL_of_foc hM hL0 hLf).2
  have hord := (hi_fb_order hM hH0 hHf hL0 hLf).le
  obtain ⟨-, hmax, -⟩ := (Screen.screen_opt_iff (hi_hyp hM) hH hL hord K).1 hK
  have hHe := (Screen.lemma_14_C_3 (hi_hyp hM) hH hL hord hK).2
  have hc := hi_Q_crit hM (hi_eL_pos hM hH0 hHf hL0 hLf hK) hmax
  have hl : (0:ℝ) < 1 - M.lam := by linarith [hM.lam_lt]
  refine ⟨by rw [hHe, hHf]; ring, ?_⟩
  field_simp
  linarith

/-- **Lemma 14.C.4** (MWG, p. 497). In any optimal contract `e_L < e*_L`. -/
theorem lemma_14_C_4 {M : HIModel} (hM : M.Standing) {eHs eLs : ℝ} (hH0 : 0 ≤ eHs)
    (hHf : M.dpH eHs = M.ge eHs M.θH) (hL0 : 0 ≤ eLs) (hLf : M.dpL eLs = M.ge eLs M.θL)
    {K : HIContract} (hK : M.scr.IsOpt K) : K.eL < eLs := by
  have hH := (hi_fbH_of_foc hM hH0 hHf).2
  have hL := (hi_fbL_of_foc hM hL0 hLf)
  have hord := (hi_fb_order hM hH0 hHf hL0 hLf).le
  have hle := (Screen.lemma_14_C_3 (hi_hyp hM) hH hL.2 hord hK).1
  rcases hle.lt_or_eq with h | h
  · exact h
  exfalso
  obtain ⟨-, hmax, -⟩ := (Screen.screen_opt_iff (hi_hyp hM) hH hL.2 hord K).1 hK
  have hc := hi_Q_crit hM (h ▸ hL.1) hmax
  rw [h, hLf, sub_self, mul_zero, zero_sub, neg_eq_zero] at hc
  have := mul_pos hM.lam_pos (sub_pos.2 (hM.ge_cross eLs hL.1))
  linarith

/-- **(14.C.9), the two terms** (MWG, p. 499): `π'(e) - g_e(e, θ_L)` is zero at `e*_L` and strictly
positive for `0 ≤ e < e*_L`; `g_e(e, θ_H) - g_e(e, θ_L)` is strictly negative for `e > 0`. -/
theorem hi_14_C_9_terms {M : HIModel} (hM : M.Standing) {eLs : ℝ} (hL0 : 0 ≤ eLs)
    (hLf : M.dpL eLs = M.ge eLs M.θL) :
    M.dpL eLs - M.ge eLs M.θL = 0 ∧
    (∀ e, 0 ≤ e → e < eLs → 0 < M.dpL e - M.ge e M.θL) ∧
    ∀ e, 0 < e → M.ge e M.θH - M.ge e M.θL < 0 := by
  refine ⟨by rw [hLf, sub_self], fun e he hlt => ?_, fun e he => sub_neg.2 (hM.ge_cross e he)⟩
  have := hi_deriv_anti (hi_SL_conc hM) (mem_Ici.2 he) (mem_Ici.2 hL0) hlt (hi_SL_deriv hM he)
    (hi_SL_deriv hM hL0)
  rw [hLf, sub_self] at this
  exact this

/-- **Proposition 14.C.3** (MWG, p. 499). With an infinitely risk-averse manager the optimal
contract sets `e_H = e*_H`, distorts `e_L` strictly below `e*_L` (with `e_L > 0`), gives the manager
exactly `ū` in state `θ_L` and strictly more than `ū` in state `θ_H`, and gives the owner a strictly
lower expected payoff than when `θ` is observable. -/
theorem proposition_14_C_3 {M : HIModel} (hM : M.Standing) {eHs eLs : ℝ} (hH0 : 0 ≤ eHs)
    (hHf : M.dpH eHs = M.ge eHs M.θH) (hL0 : 0 ≤ eLs) (hLf : M.dpL eLs = M.ge eLs M.θL)
    {K : HIContract} (hK : M.scr.IsOpt K) :
    K.eH = eHs ∧ 0 < K.eL ∧ K.eL < eLs ∧ M.v (K.wL - M.g K.eL M.θL) = M.ubar ∧
      M.ubar < M.v (K.wH - M.g K.eH M.θH) ∧ M.scr.Pi K < M.scr.FBval eHs eLs := by
  have hH := (hi_fbH_of_foc hM hH0 hHf).2
  have hL := (hi_fbL_of_foc hM hL0 hLf).2
  have hord := (hi_fb_order hM hH0 hHf hL0 hLf).le
  have hpos := hi_eL_pos hM hH0 hHf hL0 hLf hK
  obtain ⟨hU1, -, hU3⟩ := Screen.screen_H_rent (hi_hyp hM) hK
  refine ⟨(Screen.lemma_14_C_3 (hi_hyp hM) hH hL hord hK).2, hpos,
    lemma_14_C_4 hM hH0 hHf hL0 hLf hK, ?_, ?_, Screen.screen_loss (hi_hyp hM) hH hL hord hK hpos⟩
  · have : K.wL - M.g K.eL M.θL = M.c := hU1
    rw [this, hM.v_c]
  · rw [← hM.v_c]; exact hi_v_strictMono hM (hU3 hpos)

/-- **p. 499**: the optimal `e_L` falls as `λ / (1 - λ)` rises. If `e₁ > 0` maximizes the virtual
surplus for `λ₁` and `e₂ > 0` for `λ₂ > λ₁` (both in `(0, 1)`), then `e₂ < e₁`. -/
theorem hi_eL_falls {M : HIModel} (hM : M.Standing) {l1 l2 e1 e2 : ℝ} (hl1 : 0 < l1)
    (hl12 : l1 < l2) (hl2 : l2 < 1) (he1 : 0 < e1) (he2 : 0 < e2)
    (hm1 : ∀ e, 0 ≤ e → (1 - l1) * M.scr.SL e - l1 * M.scr.D e ≤
      (1 - l1) * M.scr.SL e1 - l1 * M.scr.D e1)
    (hm2 : ∀ e, 0 ≤ e → (1 - l2) * M.scr.SL e - l2 * M.scr.D e ≤
      (1 - l2) * M.scr.SL e2 - l2 * M.scr.D e2) : e2 < e1 := by
  have hyp := hi_hyp hM
  -- weak monotonicity from revealed preference
  have a := hm1 e2 he2.le
  have b := hm2 e1 he1.le
  have hle : e2 ≤ e1 := by
    by_contra hc
    rw [not_le] at hc
    have hD := hyp.D_mono he1.le he2.le hc
    -- divide by (1 - l): S_L - k D with k = l/(1-l); compare via cross-multiplication
    have h1 : (1 - l2) * ((1 - l1) * M.scr.SL e2 - l1 * M.scr.D e2) ≤
        (1 - l2) * ((1 - l1) * M.scr.SL e1 - l1 * M.scr.D e1) :=
      mul_le_mul_of_nonneg_left a (by linarith)
    have h2 : (1 - l1) * ((1 - l2) * M.scr.SL e1 - l2 * M.scr.D e1) ≤
        (1 - l1) * ((1 - l2) * M.scr.SL e2 - l2 * M.scr.D e2) :=
      mul_le_mul_of_nonneg_left b (by linarith)
    nlinarith
  rcases hle.lt_or_eq with h | h
  · exact h
  exfalso
  subst h
  -- both critical points coincide: contradiction with g_e(e, θ_H) < g_e(e, θ_L)
  have hd1 := ((hi_SL_deriv hM he2.le).const_mul (1 - l1)).sub ((hi_D_deriv hM he2.le).const_mul l1)
  have hd2 := ((hi_SL_deriv hM he2.le).const_mul (1 - l2)).sub ((hi_D_deriv hM he2.le).const_mul l2)
  have c1 := IsLocalMax.hasDerivAt_eq_zero
    (Filter.mem_of_superset (Ici_mem_nhds he2) fun y hy => hm1 y hy)
    (hd1.hasDerivAt (Ici_mem_nhds he2))
  have c2 := IsLocalMax.hasDerivAt_eq_zero
    (Filter.mem_of_superset (Ici_mem_nhds he2) fun y hy => hm2 y hy)
    (hd2.hasDerivAt (Ici_mem_nhds he2))
  have hx := sub_pos.2 (hM.ge_cross e2 he2)
  have : (l2 - l1) * ((M.dpL e2 - M.ge e2 M.θL) + (M.ge e2 M.θL - M.ge e2 M.θH)) = 0 := by
    linarith
  have hS : M.dpL e2 - M.ge e2 M.θL + (M.ge e2 M.θL - M.ge e2 M.θH) = 0 := by
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · exact h
  have : (1 - l1) * (M.dpL e2 - M.ge e2 M.θL) = l1 * (M.ge e2 M.θL - M.ge e2 M.θH) := by
    linarith
  nlinarith

/-- **Footnote 17** (MWG, p. 499). In a variant of the model where `g_e(0, θ)` may be positive
(with `g_e(0, θ_H) ≥ 0`), `e_L = 0` maximizes the virtual surplus only if `g_e(0, θ_L) > 0`. -/
theorem footnote_17 {Q dpL : ℝ → ℝ} {ge : ℝ → ℝ → ℝ} {lam θL θH : ℝ} (hl : lam < 1)
    (hd : HasDerivWithinAt Q ((1 - lam) * (dpL 0 - ge 0 θL) - lam * (ge 0 θL - ge 0 θH))
      (Ici 0) 0)
    (hdp : 0 < dpL 0) (hH : 0 ≤ ge 0 θH) (hl0 : 0 ≤ lam) (hmax : ∀ e, 0 ≤ e → Q e ≤ Q 0) :
    0 < ge 0 θL := by
  by_contra hc
  rw [not_lt] at hc
  have hpos : 0 < (1 - lam) * (dpL 0 - ge 0 θL) - lam * (ge 0 θL - ge 0 θH) := by
    have : 0 < (1 - lam) * (dpL 0 - ge 0 θL) := mul_pos (by linarith) (by linarith)
    nlinarith
  obtain ⟨y, hy, hgt⟩ := hi_exists_gt_of_deriv_pos hd hpos
  linarith [hmax y hy.le]

/-- **Appendix B, (14.BB.2)-(14.BB.5) and Steps 1-5** (MWG, pp. 505-506). If `K` is feasible and the
Kuhn-Tucker conditions hold with multipliers `(γ, φ_H, φ_L) ≥ 0` and complementary slackness, then
`φ_H > 0` and (iii) binds (Step 1), `γ = 1` and (i) binds (Step 2), `e_L, e_H > 0` (Step 3),
`φ_L = 0` (Step 4), and (14.BB.6)-(14.BB.7) hold (Step 5). -/
theorem appendix_B_steps {M : HIModel} (hM : M.Standing) {K : HIContract} (hK : M.scr.Feas K)
    {γ φH φL : ℝ} (hφL : 0 ≤ φL)
    (h2 : -M.lam + φH - φL = 0) (h3 : -(1 - M.lam) + γ - φH + φL = 0)
    (h4 : M.lam * M.dpH K.eH - φH * M.ge K.eH M.θH + φL * M.ge K.eH M.θL ≤ 0)
    (h4' : 0 < K.eH → M.lam * M.dpH K.eH - φH * M.ge K.eH M.θH + φL * M.ge K.eH M.θL = 0)
    (h5 : (1 - M.lam) * M.dpL K.eL - (γ + φL) * M.ge K.eL M.θL + φH * M.ge K.eL M.θH ≤ 0)
    (h5' : 0 < K.eL →
      (1 - M.lam) * M.dpL K.eL - (γ + φL) * M.ge K.eL M.θL + φH * M.ge K.eL M.θH = 0)
    (cs1 : γ * (K.wL - M.g K.eL M.θL - M.c) = 0)
    (cs3 : φH * (K.wH - M.g K.eH M.θH - (K.wL - M.g K.eL M.θH)) = 0)
    (cs4 : φL * (K.wL - M.g K.eL M.θL - (K.wH - M.g K.eH M.θL)) = 0) :
    0 < φH ∧ K.wH - M.g K.eH M.θH = K.wL - M.g K.eL M.θH ∧ γ = 1 ∧
      K.wL - M.g K.eL M.θL = M.c ∧ 0 < K.eL ∧ 0 < K.eH ∧ φL = 0 ∧ φH = M.lam ∧
      M.dpH K.eH - M.ge K.eH M.θH = 0 ∧
      (M.dpL K.eL - M.ge K.eL M.θL) + M.lam / (1 - M.lam) * (M.ge K.eL M.θH - M.ge K.eL M.θL) =
        0 := by
  have hl := hM.lam_pos; have hl' := hM.lam_lt
  -- Step 1
  have hφHpos : 0 < φH := by linarith
  have hiii : K.wH - M.g K.eH M.θH = K.wL - M.g K.eL M.θH := by
    rcases mul_eq_zero.1 cs3 with h | h
    · linarith
    · linarith
  -- Step 2
  have hγ1 : γ = 1 := by linarith
  have hi : K.wL - M.g K.eL M.θL = M.c := by
    rw [hγ1] at cs1; linarith
  -- Step 3
  have hpos : ∀ e : ℝ, 0 ≤ e → ¬ 0 < e → e = 0 := fun e he hne => le_antisymm (not_lt.1 hne) he
  have heL : 0 < K.eL := by
    by_contra hc
    have h0 := hpos _ hK.2.1 hc
    rw [h0, hM.ge_zero, hM.ge_zero] at h5
    have := hM.dpL_pos 0 le_rfl
    nlinarith
  have heH : 0 < K.eH := by
    by_contra hc
    have h0 := hpos _ hK.1 hc
    rw [h0, hM.ge_zero, hM.ge_zero] at h4
    have := hM.dp_le 0 le_rfl
    have := hM.dpL_pos 0 le_rfl
    nlinarith
  have e4 := h4' heH
  have e5 := h5' heL
  -- Step 4
  have hφL : φL = 0 := by
    by_contra hne
    have hφLpos : 0 < φL := lt_of_le_of_ne hφL (Ne.symm hne)
    have hφHv : φH = φL + M.lam := by linarith
    rw [hφHv] at e4 e5
    rw [hγ1] at e5
    have a4 : M.lam * (M.dpH K.eH - M.ge K.eH M.θH) +
        φL * (M.ge K.eH M.θL - M.ge K.eH M.θH) = 0 := by linarith
    have a5 : (1 - M.lam) * (M.dpL K.eL - M.ge K.eL M.θH) +
        (1 + φL) * (M.ge K.eL M.θH - M.ge K.eL M.θL) = 0 := by linarith
    -- (iv) binds since φL > 0
    have hiv : K.wL - M.g K.eL M.θL = K.wH - M.g K.eH M.θL := by
      rcases mul_eq_zero.1 cs4 with h | h
      · exact absurd h hne
      · linarith
    -- then D(e_H) = D(e_L), so e_H = e_L
    have hDeq : M.scr.D K.eH = M.scr.D K.eL := by
      change M.g K.eH M.θL - M.g K.eH M.θH = M.g K.eL M.θL - M.g K.eL M.θH; linarith
    have heq : K.eH = K.eL := (hi_hyp hM).D_mono.injOn hK.1 hK.2.1 hDeq
    have hcH := hM.ge_cross K.eH heH
    -- with e_H = e_L =: e, (14.BB.4) and (14.BB.5) are incompatible
    rw [heq] at a4 hcH
    have hp := hM.dp_le K.eL heL.le
    have hlpos : 0 < M.ge K.eL M.θL - M.ge K.eL M.θH := by linarith
    -- a4: λ (π'_H - g_eH) = -φL (g_eL - g_eH) < 0; a5: (1 - λ)(π'_L - g_eH) > 0
    have b4 : M.dpH K.eL - M.ge K.eL M.θH < 0 := by nlinarith
    have b5 : 0 < M.dpL K.eL - M.ge K.eL M.θH := by nlinarith
    linarith
  -- Step 5
  have hφHl : φH = M.lam := by linarith
  rw [hφL, hφHl] at e4 e5
  rw [hγ1] at e5
  refine ⟨hφHpos, hiii, hγ1, hi, heL, heH, hφL, hφHl, ?_, ?_⟩
  · have : M.lam * (M.dpH K.eH - M.ge K.eH M.θH) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · exact h
  · have hl1 : (0:ℝ) < 1 - M.lam := by linarith
    field_simp
    linarith

/-- **Appendix B** (MWG, p. 505): at every optimal contract the Kuhn-Tucker conditions
(14.BB.2)-(14.BB.5) hold, with multipliers `γ = 1`, `φ_H = λ`, `φ_L = 0`. -/
theorem appendix_B_multipliers {M : HIModel} (hM : M.Standing) {eHs eLs : ℝ} (hH0 : 0 ≤ eHs)
    (hHf : M.dpH eHs = M.ge eHs M.θH) (hL0 : 0 ≤ eLs) (hLf : M.dpL eLs = M.ge eLs M.θL)
    {K : HIContract} (hK : M.scr.IsOpt K) :
    -M.lam + M.lam - 0 = 0 ∧ -(1 - M.lam) + 1 - M.lam + 0 = 0 ∧
    M.lam * M.dpH K.eH - M.lam * M.ge K.eH M.θH + 0 * M.ge K.eH M.θL = 0 ∧
    (1 - M.lam) * M.dpL K.eL - (1 + 0) * M.ge K.eL M.θL + M.lam * M.ge K.eL M.θH = 0 ∧
    1 * (K.wL - M.g K.eL M.θL - M.c) = 0 ∧
    M.lam * (K.wH - M.g K.eH M.θH - (K.wL - M.g K.eL M.θH)) = 0 := by
  obtain ⟨hf1, hf2⟩ := hi_foc_14_C_9 hM hH0 hHf hL0 hLf hK
  obtain ⟨hwL, hwH⟩ := Screen.lemma_14_C_2 (hi_hyp hM) hK
  have hl1 : (0:ℝ) < 1 - M.lam := by linarith [hM.lam_lt]
  refine ⟨by ring, by ring, by linear_combination M.lam * hf1, ?_, ?_, ?_⟩
  · field_simp at hf2; linear_combination hf2
  · have e1 : K.wL = M.c + M.g K.eL M.θL := hwL
    rw [e1]; ring
  · have e1 : K.wL = M.c + M.g K.eL M.θL := hwL
    have e2 : K.wH = M.c + (M.g K.eL M.θL - M.g K.eL M.θH) + M.g K.eH M.θH := hwH
    rw [e1, e2]; ring

end HIModel

end MWG.PrincipalAgent
