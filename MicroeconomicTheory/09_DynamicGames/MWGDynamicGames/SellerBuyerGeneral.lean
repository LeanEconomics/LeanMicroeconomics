/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGDynamicGames.SellerBuyer

/-!
# Exercise 9.C.3(b) with a general lower bound `v̲ ≥ 0`

MWG, Exercise 9.C.3(b) (p. 304) and Exercise 9.C.6 for it: the buyer's value is uniform on
`[v̲, v̄]` with `0 ≤ v̲ < v̄` (written `vl`, `vh`), the discount factor is `δ ∈ (0, 1)`.

The reduced model is that of `SellerBuyer.lean` (where `v̲ = 0`, `v̄ = 1`), with the prior's
mass of `[k, v̄]` equal to `(v̄ − k)/(v̄ − v̲)`. The seller's payoffs are multiplied by
`v̄ − v̲ > 0` and her period-2 revenue for the posterior uniform on `[v̲, k)` by `k − v̲ > 0`;
this changes no comparison. `sbgCut` is the cutoff `κ` of `exercise_9_C_3b_cutoff` clamped to
`[v̲, v̄]`, `sbgPay` the seller's payoff, `sbgRev` the period-2 revenue, `IsSBGWeakPBE` and
`IsSBGConsistent` the weak PBE and consistency conditions (`isSBGWeakPBE_zero_one_iff`: for
`v̲ = 0`, `v̄ = 1` they are those of `SellerBuyer.lean`).

* `sbgRev_opt_iff`: for the posterior uniform on `[v̲, k)` the unique optimal second price is
  `max (v̲, k/2)`: the **corner** `v̲` when `k ≤ 2v̲`.
* `sbg_consistent`: with consistent beliefs, after every price `p > v̲` the cutoff is
  `K(p) = min ((p − δv̲)/(1 − δ), 2p/(2 − δ), v̄)` and the second price `max (v̲, K(p)/2)`.
* `exercise_9_C_3b_general`: the characterisation of the weak PBE with consistent beliefs.
  With `G_C = (1 − δ) v̄²/4 + δ v̲ v̄ − δ v̲²` (corner value) and `G_I = (2 − δ)² v̄²/(4 (4 − 3δ))`
  (interior value): (i) if `v̄ ≤ 2v̲` the first price is `v̲` and every type buys at once;
  (ii) if `2v̲ < v̄` and `G_C ≤ G_I` the first price is `(2 − δ)² v̄/(2 (4 − 3δ))`, the cutoff
  `k* = (2 − δ) v̄/(4 − 3δ)` and the second price `k*/2`; (iii) if `2v̲ < v̄` and `G_I ≤ G_C` the
  first price is `(1 − δ) v̄/2 + δ v̲`, the cutoff `v̄/2` and the second price is the corner
  `v̲`. `sbgGI_sub_sbgGC`: `G_I − G_C = δ (v̲² − v̲ v̄ + (3 − 2δ) v̄²/(4 (4 − 3δ)))`.
  `exercise_9_C_3b_general_outcomes`, `exercise_9_C_3b_general_exists`, and the instances
  `exercise_9_C_3b_general_examples` (one per case).
-/

namespace MWG.DynamicGames

/-- The cutoff clamped to `[v̲, v̄]`: the types in `[v̲, k)` reject the first price `p` when they
expect the second price `r`. -/
noncomputable def sbgCut (vl vh δ p r : ℝ) : ℝ := max vl (min (sbKappa δ p r) vh)

/-- The seller's payoff (times `v̄ − v̲`) from the first price `p` and second price `q` when the
buyer expects the second price `r`: the types `[k, v̄]` buy at `p`, the types in `[max q v̲, k)`
buy at `q` in period 2. -/
noncomputable def sbgPay (vl vh δ p r q : ℝ) : ℝ :=
  p * (vh - sbgCut vl vh δ p r) + δ * q * max 0 (sbgCut vl vh δ p r - max q vl)

/-- The seller's period-2 revenue at price `q` (times `k − v̲`) for the belief uniform on
`[v̲, k)`. -/
noncomputable def sbgRev (vl k q : ℝ) : ℝ := q * max 0 (k - max q vl)

/-- **Exercise 9.C.3(b)** (MWG, p. 304), values uniform on `[v̲, v̄]`. A pure-strategy weak PBE in
reduced form: second prices `r p ∈ [v̲, v̄]` after every rejected price (each optimal for the
belief concentrated on `v = r p`), optimal for the Bayes posterior after `p1` if some types
reject it, and `p1` optimal against every deviation `(p, q)`. -/
def IsSBGWeakPBE (vl vh δ p1 : ℝ) (r : ℝ → ℝ) : Prop :=
  (∀ p, vl ≤ r p ∧ r p ≤ vh) ∧
  (vl < sbgCut vl vh δ p1 (r p1) → ∀ q, sbgRev vl (sbgCut vl vh δ p1 (r p1)) q ≤
    sbgRev vl (sbgCut vl vh δ p1 (r p1)) (r p1)) ∧
  ∀ p q, sbgPay vl vh δ p (r p) q ≤ sbgPay vl vh δ p1 (r p1) (r p1)

/-- **Exercise 9.C.6 for 9.C.3(b)** (MWG, p. 304). Structural consistency: after every price that
a positive mass of types rejects, the second price is optimal for the Bayes posterior. -/
def IsSBGConsistent (vl vh δ : ℝ) (r : ℝ → ℝ) : Prop :=
  ∀ p, vl < sbgCut vl vh δ p (r p) → ∀ q, sbgRev vl (sbgCut vl vh δ p (r p)) q ≤
    sbgRev vl (sbgCut vl vh δ p (r p)) (r p)

/-- The consistent cutoff after the first price `p > v̲`. -/
noncomputable def sbgK (vl vh δ p : ℝ) : ℝ :=
  min (min ((p - δ * vl) / (1 - δ)) (2 * p / (2 - δ))) vh

/-- The consistent second price after the first price `p > v̲`. -/
noncomputable def sbgR (vl vh δ p : ℝ) : ℝ := max vl (sbgK vl vh δ p / 2)

/-- The first price whose consistent cutoff is `k` (the inverse of `sbgK` on `[v̲, v̄]`). -/
noncomputable def sbgPhi (vl δ k : ℝ) : ℝ := max ((1 - δ) * k + δ * vl) ((2 - δ) * k / 2)

/-- The seller's maximal period-2 revenue (times `k − v̲`) for the belief uniform on `[v̲, k)`. -/
noncomputable def sbgMaxRev (vl k : ℝ) : ℝ := if 2 * vl ≤ k then k ^ 2 / 4 else vl * (k - vl)

/-- The seller's payoff when the consistent cutoff is `k`. -/
noncomputable def sbgVal (vl vh δ k : ℝ) : ℝ := sbgPhi vl δ k * (vh - k) + δ * sbgMaxRev vl k

/-- The payoff for cutoff `k` when the second price is interior (`k ≥ 2v̲`). -/
noncomputable def sbgGIk (vh δ k : ℝ) : ℝ := (2 - δ) * vh * k / 2 - (4 - 3 * δ) * k ^ 2 / 4

/-- The payoff for cutoff `k` when the second price is the corner `v̲` (`k ≤ 2v̲`). -/
noncomputable def sbgGCk (vl vh δ k : ℝ) : ℝ :=
  ((1 - δ) * k + δ * vl) * (vh - k) + δ * vl * (k - vl)

/-- The interior cutoff `k* = (2 − δ) v̄/(4 − 3δ)`. -/
noncomputable def sbgKI (vh δ : ℝ) : ℝ := (2 - δ) * vh / (4 - 3 * δ)

/-- The interior value `G_I`. -/
noncomputable def sbgGI (vh δ : ℝ) : ℝ := sbgGIk vh δ (sbgKI vh δ)

/-- The corner value `G_C` (cutoff `v̄/2`). -/
noncomputable def sbgGC (vl vh δ : ℝ) : ℝ := sbgGCk vl vh δ (vh / 2)

/-- The interior first price `(2 − δ)² v̄/(2 (4 − 3δ))`. -/
noncomputable def sbgPI (vh δ : ℝ) : ℝ := (2 - δ) ^ 2 * vh / (2 * (4 - 3 * δ))

/-- The corner first price `(1 − δ) v̄/2 + δ v̲`. -/
noncomputable def sbgPC (vl vh δ : ℝ) : ℝ := (1 - δ) * vh / 2 + δ * vl

variable {vl vh δ : ℝ}

/-- The period-2 revenue is at most `sbgMaxRev`. -/
theorem sbgRev_le (hvl : 0 ≤ vl) {k : ℝ} (hk : vl ≤ k) (q : ℝ) :
    sbgRev vl k q ≤ sbgMaxRev vl k := by
  unfold sbgRev sbgMaxRev
  rcases le_total q vl with hq | hq
  · rw [max_eq_right hq, max_eq_right (by linarith : (0 : ℝ) ≤ k - vl)]
    have h1 := mul_nonneg (sub_nonneg.2 hq) (sub_nonneg.2 hk)
    split_ifs with h
    · nlinarith [sq_nonneg (k - 2 * vl)]
    · nlinarith
  · rw [max_eq_left hq]
    rcases le_total (k - q) 0 with h1 | h1
    · rw [max_eq_left h1, mul_zero]
      split_ifs
      · positivity
      · exact mul_nonneg hvl (by linarith)
    · rw [max_eq_right h1]
      split_ifs with h
      · nlinarith [sq_nonneg (q - k / 2)]
      · nlinarith [mul_nonneg (sub_nonneg.2 hq) (by linarith : (0 : ℝ) ≤ q + vl - k)]

/-- The revenue at `max (v̲, k/2)` is `sbgMaxRev`. -/
theorem sbgRev_opt_val (hvl : 0 ≤ vl) {k : ℝ} (hk : vl ≤ k) :
    sbgRev vl k (max vl (k / 2)) = sbgMaxRev vl k := by
  unfold sbgRev sbgMaxRev
  split_ifs with h
  · rw [max_eq_right (by linarith : vl ≤ k / 2), max_eq_left (by linarith : vl ≤ k / 2),
      max_eq_right (by linarith : (0 : ℝ) ≤ k - k / 2)]
    ring
  · rw [max_eq_left (by linarith : k / 2 ≤ vl), max_self, max_eq_right (by linarith)]

/-- **Exercise 9.C.3(b), the second price** (MWG, p. 304). For the belief uniform on `[v̲, k)`,
`v̲ < k`, the unique optimal second price is `max (v̲, k/2)`: the corner `v̲` when `k ≤ 2v̲`. -/
theorem sbgRev_opt_iff (hvl : 0 ≤ vl) {k : ℝ} (hk : vl < k) (r : ℝ) :
    (∀ q, sbgRev vl k q ≤ sbgRev vl k r) ↔ r = max vl (k / 2) := by
  constructor
  · intro h
    have h1 := h (max vl (k / 2))
    rw [sbgRev_opt_val hvl hk.le] at h1
    unfold sbgRev sbgMaxRev at h1
    split_ifs at h1 with h2
    · rw [max_eq_right (by linarith : vl ≤ k / 2)]
      rcases le_total r vl with hr | hr
      · rw [max_eq_right hr, max_eq_right (by linarith : (0 : ℝ) ≤ k - vl)] at h1
        have h3 : (k - 2 * vl) ^ 2 ≤ 0 := by
          nlinarith [mul_nonneg (sub_nonneg.2 hr) (sub_nonneg.2 hk.le)]
        have h4 : k = 2 * vl := by
          have := le_antisymm h3 (sq_nonneg _)
          have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
          linarith
        subst h4
        nlinarith
      · rw [max_eq_left hr] at h1
        rcases le_total (k - r) 0 with h5 | h5
        · rw [max_eq_left h5] at h1
          nlinarith
        · rw [max_eq_right h5] at h1
          have h6 : (r - k / 2) ^ 2 ≤ 0 := by nlinarith
          have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (le_antisymm h6 (sq_nonneg _))
          linarith
    · rw [max_eq_left (by linarith : k / 2 ≤ vl)]
      have hvl0 : 0 < vl := by linarith
      rcases le_total r vl with hr | hr
      · rw [max_eq_right hr, max_eq_right (by linarith : (0 : ℝ) ≤ k - vl)] at h1
        have : vl ≤ r := by nlinarith
        linarith
      · rcases hr.eq_or_lt with h6 | h6
        · exact h6.symm
        exfalso
        rw [max_eq_left hr] at h1
        rcases le_total (k - r) 0 with h5 | h5
        · rw [max_eq_left h5] at h1
          nlinarith
        · rw [max_eq_right h5] at h1
          nlinarith [mul_pos (sub_pos.2 h6) (by linarith : (0 : ℝ) < r + vl - k)]
  · rintro rfl q
    rw [sbgRev_opt_val hvl hk.le]
    exact sbgRev_le hvl hk.le q

/-- After a first price `p ≤ v̲`, if the expected second price is at least `v̲`, every type
buys at once. -/
theorem sbgCut_of_le (hd0 : 0 < δ) (hd1 : δ < 1) {p r : ℝ} (hp : p ≤ vl)
    (hr : vl ≤ r) : sbgCut vl vh δ p r = vl := by
  have hκ : sbKappa δ p r ≤ vl := by
    unfold sbKappa
    split_ifs
    · rw [div_le_iff₀ (by linarith)]
      nlinarith
    · exact hp
  unfold sbgCut
  exact max_eq_left ((min_le_left _ _).trans hκ)

/-- After a first price `p > v̲` some types reject, whatever second price they expect. -/
theorem sbgCut_gt (hlh : vl < vh) (hd0 : 0 < δ) (hd1 : δ < 1) {p : ℝ} (hp : vl < p)
    (r : ℝ) : vl < sbgCut vl vh δ p r := by
  have hκ : p ≤ sbKappa δ p r := by
    unfold sbKappa
    split_ifs
    · rw [le_div_iff₀ (by linarith)]
      nlinarith
    · exact le_rfl
  unfold sbgCut
  exact lt_max_of_lt_right (lt_min (hp.trans_le hκ) hlh)

/-- **Exercise 9.C.3(b), consistent continuation** (MWG, p. 304). With consistent beliefs, after
every first price `p > v̲` the second price is `sbgR p = max (v̲, K(p)/2)` and the cutoff is
`K(p) = min ((p − δv̲)/(1 − δ), 2p/(2 − δ), v̄)`. -/
theorem sbg_consistent (hvl : 0 ≤ vl) (hlh : vl < vh) (hd0 : 0 < δ) (hd1 : δ < 1)
    {r : ℝ → ℝ} (hc : IsSBGConsistent vl vh δ r) {p : ℝ} (hp : vl < p) :
    r p = sbgR vl vh δ p ∧ sbgCut vl vh δ p (r p) = sbgK vl vh δ p := by
  have h1 : 0 < 1 - δ := by linarith
  have h2 : 0 < 2 - δ := by linarith
  set k := sbgCut vl vh δ p (r p) with hkdef
  have hk := sbgCut_gt hlh hd0 hd1 hp (r p)
  rw [← hkdef] at hk
  have hr := (sbgRev_opt_iff hvl hk (r p)).1 (hc p hk)
  have hrvl : vl ≤ r p := hr ▸ le_max_left _ _
  have hrk : k / 2 ≤ r p := hr ▸ le_max_right _ _
  have hkle : k = min (sbKappa δ p (r p)) vh := by
    rw [hkdef, sbgCut]
    refine max_eq_right ?_
    by_contra hn
    have : sbgCut vl vh δ p (r p) = vl := max_eq_left (le_of_not_ge hn)
    rw [← hkdef] at this
    linarith
  have hrp : r p ≤ p := by
    by_contra hn
    have hκ : sbKappa δ p (r p) = p := by simp [sbKappa, hn]
    rw [hκ] at hkle
    have hkp : k ≤ p := hkle ▸ min_le_left _ _
    rcases max_choice vl (k / 2) with h | h
    · rw [h] at hr; linarith
    · rw [h] at hr; linarith
  have hκ : sbKappa δ p (r p) * (1 - δ) = p - δ * r p := by
    simp only [sbKappa, hrp, ↓reduceIte]
    field_simp
  have hKk : k = sbgK vl vh δ p := by
    refine le_antisymm ?_ ?_
    · have hkκ : k ≤ sbKappa δ p (r p) := hkle ▸ min_le_left _ _
      refine le_min (le_min ?_ ?_) (hkle ▸ min_le_right _ _)
      · rw [le_div_iff₀ h1]
        nlinarith
      · rw [le_div_iff₀ h2]
        nlinarith
    · rcases min_choice (sbKappa δ p (r p)) vh with h | h
      · rw [h] at hkle
        rcases max_choice vl (k / 2) with h' | h'
        · rw [h'] at hr
          refine (min_le_left _ _).trans ((min_le_left _ _).trans (le_of_eq ?_))
          rw [div_eq_iff h1.ne', hkle, hκ, hr]
        · rw [h'] at hr
          refine (min_le_left _ _).trans ((min_le_right _ _).trans (le_of_eq ?_))
          rw [div_eq_iff h2.ne']
          have e : sbKappa δ p (r p) * (1 - δ) = p - δ * (k / 2) := by rw [hκ, hr]
          rw [← hkle] at e
          linear_combination (-2) * e
      · rw [h] at hkle
        rw [hkle]
        exact min_le_right _ _
  exact ⟨by rw [hr, hKk, sbgR], hKk⟩

/-- The consistent cutoff after `p > v̲` lies in `(v̲, v̄]`. -/
theorem sbgK_mem (hvl : 0 ≤ vl) (hlh : vl < vh) (hd0 : 0 < δ) (hd1 : δ < 1) {p : ℝ}
    (hp : vl < p) : vl < sbgK vl vh δ p ∧ sbgK vl vh δ p ≤ vh := by
  have h1 : 0 < 1 - δ := by linarith
  have h2 : 0 < 2 - δ := by linarith
  refine ⟨lt_min (lt_min ?_ ?_) hlh, min_le_right _ _⟩
  · rw [lt_div_iff₀ h1]; nlinarith
  · rw [lt_div_iff₀ h2]; nlinarith

/-- The price `sbgPhi k` has consistent cutoff `k`. -/
theorem sbgK_phi (hd0 : 0 < δ) (hd1 : δ < 1) {k : ℝ} (hkh : k ≤ vh) :
    sbgK vl vh δ (sbgPhi vl δ k) = k := by
  have h1 : 0 < 1 - δ := by linarith
  have h2 : 0 < 2 - δ := by linarith
  unfold sbgK sbgPhi
  set m := max ((1 - δ) * k + δ * vl) ((2 - δ) * k / 2) with hm
  have hA : k ≤ (m - δ * vl) / (1 - δ) := by
    rw [le_div_iff₀ h1]; linarith [le_max_left ((1 - δ) * k + δ * vl) ((2 - δ) * k / 2)]
  have hB : k ≤ 2 * m / (2 - δ) := by
    rw [le_div_iff₀ h2]; linarith [le_max_right ((1 - δ) * k + δ * vl) ((2 - δ) * k / 2)]
  have hmin : min ((m - δ * vl) / (1 - δ)) (2 * m / (2 - δ)) = k := by
    refine le_antisymm ?_ (le_min hA hB)
    rcases max_choice ((1 - δ) * k + δ * vl) ((2 - δ) * k / 2) with h | h
    · refine (min_le_left _ _).trans (le_of_eq ?_)
      rw [hm, h, div_eq_iff h1.ne']
      ring
    · refine (min_le_right _ _).trans (le_of_eq ?_)
      rw [hm, h, div_eq_iff h2.ne']
      ring
  rw [hmin, min_eq_left hkh]

/-- When the consistent cutoff after `p` is below `v̄`, `p = sbgPhi (K(p))`. -/
theorem sbgPhi_K (hd0 : 0 < δ) (hd1 : δ < 1) {p : ℝ} (hK : sbgK vl vh δ p < vh) :
    sbgPhi vl δ (sbgK vl vh δ p) = p := by
  have h1 : 0 < 1 - δ := by linarith
  have h2 : 0 < 2 - δ := by linarith
  set A := (p - δ * vl) / (1 - δ) with hA
  set B := 2 * p / (2 - δ) with hB
  have hA' : A * (1 - δ) = p - δ * vl := by rw [hA]; field_simp
  have hB' : B * (2 - δ) = 2 * p := by rw [hB]; field_simp
  have hKe : sbgK vl vh δ p = min A B := by
    unfold sbgK at hK ⊢
    exact min_eq_left (le_of_lt (by
      rcases min_choice (min A B) vh with h | h
      · rw [h] at hK; exact hK
      · rw [h] at hK; exact absurd hK (lt_irrefl _)))
  rw [hKe]
  unfold sbgPhi
  have hle1 : (1 - δ) * min A B + δ * vl ≤ p := by
    nlinarith [mul_le_mul_of_nonneg_left (min_le_left A B) h1.le]
  have hle2 : (2 - δ) * min A B / 2 ≤ p := by
    nlinarith [mul_le_mul_of_nonneg_left (min_le_right A B) h2.le]
  refine le_antisymm (max_le hle1 hle2) ?_
  rcases min_choice A B with h | h
  · rw [h]; exact le_max_of_le_left (by linarith)
  · rw [h]; exact le_max_of_le_right (by linarith)

/-- The consistent second price yields the consistent cutoff. -/
theorem sbgCut_R (hvl : 0 ≤ vl) (hlh : vl < vh) (hd0 : 0 < δ) (hd1 : δ < 1) {p : ℝ}
    (hp : vl < p) : sbgCut vl vh δ p (sbgR vl vh δ p) = sbgK vl vh δ p := by
  have h1 : 0 < 1 - δ := by linarith
  have h2 : 0 < 2 - δ := by linarith
  obtain ⟨hK0, hK1⟩ := sbgK_mem hvl hlh hd0 hd1 hp
  set K := sbgK vl vh δ p with hKdef
  set A := (p - δ * vl) / (1 - δ) with hA
  set B := 2 * p / (2 - δ) with hB
  have hA' : A * (1 - δ) = p - δ * vl := by rw [hA]; field_simp
  have hB' : B * (2 - δ) = 2 * p := by rw [hB]; field_simp
  have hKAB : K = min (min A B) vh := rfl
  have hKB : K ≤ B := hKAB ▸ (min_le_left _ _).trans (min_le_right _ _)
  have hKA : K ≤ A := hKAB ▸ (min_le_left _ _).trans (min_le_left _ _)
  have hRp : sbgR vl vh δ p ≤ p := by
    unfold sbgR
    refine max_le hp.le ?_
    rw [← hKdef]
    nlinarith
  have hκ : sbKappa δ p (sbgR vl vh δ p) * (1 - δ) = p - δ * sbgR vl vh δ p := by
    simp only [sbKappa, hRp, ↓reduceIte]
    field_simp
  -- `κ = K` when `K < v̄`, `κ ≥ v̄` otherwise
  have hmain : min (sbKappa δ p (sbgR vl vh δ p)) vh = K := by
    rcases le_total (min A B) vh with hc | hc
    · have hKe : K = min A B := by rw [hKAB]; exact min_eq_left hc
      have hκK : sbKappa δ p (sbgR vl vh δ p) = K := by
        rcases min_choice A B with h | h
        · rw [h] at hKe
          -- `A ≤ B` gives `K ≤ 2 v̲`, so the second price is `v̲`
          have hAB : A ≤ B := h ▸ min_le_right A B
          have hK2 : K ≤ 2 * vl := by nlinarith
          have hR : sbgR vl vh δ p = vl := by
            unfold sbgR; rw [← hKdef]; exact max_eq_left (by linarith)
          refine mul_right_cancel₀ h1.ne' (hκ.trans ?_)
          rw [hR, hKe, hA']
        · rw [h] at hKe
          have hBA : B ≤ A := h ▸ min_le_left A B
          have hK2 : 2 * vl ≤ K := by nlinarith
          have hR : sbgR vl vh δ p = K / 2 := by
            unfold sbgR; rw [← hKdef]; exact max_eq_right (by linarith)
          refine mul_right_cancel₀ h1.ne' (hκ.trans ?_)
          rw [hR, hKe, hB]
          field_simp
          ring
      rw [hκK]
      exact min_eq_left hK1
    · have hKe : K = vh := by rw [hKAB]; exact min_eq_right hc
      have hAv : vh ≤ A := hc.trans (min_le_left _ _)
      have hBv : vh ≤ B := hc.trans (min_le_right _ _)
      rw [hKe]
      refine min_eq_right (le_of_mul_le_mul_right ?_ h1)
      rw [hκ]
      unfold sbgR
      rw [← hKdef, hKe]
      rcases max_choice vl (vh / 2) with h | h
      · rw [h]; nlinarith
      · rw [h]; nlinarith
  unfold sbgCut
  rw [hmain]
  exact max_eq_right hK0.le

/-- The seller's optimal value: `v̲ (v̄ − v̲)` if `v̄ ≤ 2v̲`, otherwise `max (G_I, G_C)`. -/
noncomputable def sbgOpt (vl vh δ : ℝ) : ℝ :=
  if vh ≤ 2 * vl then vl * (vh - vl) else max (sbgGI vh δ) (sbgGC vl vh δ)

/-- For `k ≤ 2v̲` the second price is the corner `v̲` and the payoff is `G_C(k)`. -/
theorem sbgVal_corner (hd0 : 0 < δ) {k : ℝ} (hk : k ≤ 2 * vl) :
    sbgVal vl vh δ k = sbgGCk vl vh δ k := by
  unfold sbgVal sbgPhi sbgMaxRev sbgGCk
  rw [max_eq_left (by nlinarith [mul_le_mul_of_nonneg_left hk hd0.le])]
  split_ifs with h
  · have : k = 2 * vl := le_antisymm hk h
    subst this
    ring
  · ring

/-- For `k ≥ 2v̲` the second price is `k/2` and the payoff is `G_I(k)`. -/
theorem sbgVal_interior (hd0 : 0 < δ) {k : ℝ} (hk : 2 * vl ≤ k) :
    sbgVal vl vh δ k = sbgGIk vh δ k := by
  unfold sbgVal sbgPhi sbgMaxRev sbgGIk
  rw [max_eq_right (by nlinarith [mul_le_mul_of_nonneg_left hk hd0.le])]
  simp only [hk, ↓reduceIte]
  ring

/-- `G_C − G_C(k) = (1 − δ) (k − v̄/2)²`. -/
theorem sbgGC_sub (k : ℝ) :
    sbgGC vl vh δ - sbgGCk vl vh δ k = (1 - δ) * (k - vh / 2) ^ 2 := by
  unfold sbgGC sbgGCk
  ring

/-- `G_I − G_I(k) = (4 − 3δ)/4 · (k − k*)²`. -/
theorem sbgGI_sub (hd1 : δ < 1) (k : ℝ) :
    sbgGI vh δ - sbgGIk vh δ k = (4 - 3 * δ) / 4 * (k - sbgKI vh δ) ^ 2 := by
  have h : (4 - 3 * δ) ≠ 0 := (by linarith : (0 : ℝ) < 4 - 3 * δ).ne'
  have hK : sbgKI vh δ * (4 - 3 * δ) = (2 - δ) * vh := div_mul_cancel₀ _ h
  unfold sbgGI sbgGIk
  linear_combination (-(sbgKI vh δ - k) / 2) * hK

/-- `G_I(k) − G_C(k) = δ (k/2 − v̲) (v̄ − k/2 − v̲)`. -/
theorem sbgGIk_sub_sbgGCk (k : ℝ) :
    sbgGIk vh δ k - sbgGCk vl vh δ k = δ * (k / 2 - vl) * (vh - k / 2 - vl) := by
  unfold sbgGIk sbgGCk
  ring

/-- **Exercise 9.C.3(b), the comparison** (MWG, p. 304).
`4 (4 − 3δ) (G_I − G_C) = δ (4 (4 − 3δ) (v̲² − v̲ v̄) + (3 − 2δ) v̄²)`: the interior solution is
better iff `v̲² − v̲ v̄ + (3 − 2δ) v̄²/(4 (4 − 3δ)) > 0`. -/
theorem sbgGI_sub_sbgGC (hd1 : δ < 1) :
    4 * (4 - 3 * δ) * (sbgGI vh δ - sbgGC vl vh δ) =
      δ * (4 * (4 - 3 * δ) * (vl ^ 2 - vl * vh) + (3 - 2 * δ) * vh ^ 2) := by
  have h : (4 - 3 * δ) ≠ 0 := (by linarith : (0 : ℝ) < 4 - 3 * δ).ne'
  have hK : sbgKI vh δ * (4 - 3 * δ) = (2 - δ) * vh := div_mul_cancel₀ _ h
  unfold sbgGI sbgGIk sbgGC sbgGCk
  linear_combination ((2 - δ) * vh - sbgKI vh δ * (4 - 3 * δ)) * hK

/-- Every consistent payoff is at most `sbgOpt`. -/
theorem sbgVal_le_opt (hd0 : 0 < δ) (hd1 : δ < 1) {k : ℝ} (hk0 : vl ≤ k)
    (hk1 : k ≤ vh) : sbgVal vl vh δ k ≤ sbgOpt vl vh δ := by
  have h1 : 0 < 1 - δ := by linarith
  unfold sbgOpt
  split_ifs with h
  · rw [sbgVal_corner hd0 (by linarith)]
    unfold sbgGCk
    nlinarith [mul_nonneg h1.le (mul_nonneg (sub_nonneg.2 hk0)
      (by linarith : (0 : ℝ) ≤ k + vl - vh))]
  · rcases le_total k (2 * vl) with hk | hk
    · rw [sbgVal_corner hd0 hk]
      have := sbgGC_sub (vl := vl) (vh := vh) (δ := δ) k
      exact le_max_of_le_right (by nlinarith [sq_nonneg (k - vh / 2)])
    · rw [sbgVal_interior hd0 hk]
      have := sbgGI_sub (vh := vh) hd1 k
      have h43 : 0 < 4 - 3 * δ := by linarith
      exact le_max_of_le_left (by nlinarith [mul_nonneg h43.le (sq_nonneg (k - sbgKI vh δ))])

/-- After a first price `p ≤ v̲` (and a second price `r ≥ v̲`) the seller earns `p (v̄ − v̲)`. -/
theorem sbgPay_low (hd0 : 0 < δ) (hd1 : δ < 1) {p r : ℝ} (hp : p ≤ vl) (hr : vl ≤ r)
    (q : ℝ) : sbgPay vl vh δ p r q = p * (vh - vl) := by
  unfold sbgPay
  rw [sbgCut_of_le hd0 hd1 hp hr, max_eq_left (by linarith [le_max_right q vl])]
  ring

/-- After a first price `p > v̲` with the consistent continuation, the seller earns at most
`sbgVal (K(p))`, with equality at the consistent second price. -/
theorem sbgPay_cons (hvl : 0 ≤ vl) (hlh : vl < vh) (hd0 : 0 < δ) (hd1 : δ < 1) {p : ℝ}
    (hp : vl < p) (q : ℝ) :
    sbgPay vl vh δ p (sbgR vl vh δ p) q ≤ sbgVal vl vh δ (sbgK vl vh δ p) ∧
      sbgPay vl vh δ p (sbgR vl vh δ p) (sbgR vl vh δ p) = sbgVal vl vh δ (sbgK vl vh δ p) := by
  obtain ⟨hK0, hK1⟩ := sbgK_mem hvl hlh hd0 hd1 hp
  have hcut := sbgCut_R hvl hlh hd0 hd1 hp
  set K := sbgK vl vh δ p with hK
  have hpk : p * (vh - K) = sbgPhi vl δ K * (vh - K) := by
    rcases hK1.lt_or_eq with h | h
    · rw [sbgPhi_K hd0 hd1 h]
    · rw [h, sub_self, mul_zero, mul_zero]
  have e : ∀ q, sbgPay vl vh δ p (sbgR vl vh δ p) q = p * (vh - K) + δ * sbgRev vl K q := by
    intro q
    unfold sbgPay sbgRev
    rw [hcut]
    ring
  have hR : sbgR vl vh δ p = max vl (K / 2) := rfl
  unfold sbgVal
  refine ⟨?_, ?_⟩
  · rw [e, hpk]
    nlinarith [sbgRev_le hvl hK0.le q]
  · rw [e, hpk, hR, sbgRev_opt_val hvl hK0.le]

/-- The candidate first prices: `sbgPI = sbgPhi k*` (if `2v̲ ≤ k*`) and `sbgPC = sbgPhi (v̄/2)`
(if `v̄/2 ≤ 2v̲`). -/
theorem sbgPhi_cand (hd0 : 0 < δ) (hd1 : δ < 1) :
    (2 * vl ≤ sbgKI vh δ → sbgPhi vl δ (sbgKI vh δ) = sbgPI vh δ) ∧
    (vh / 2 ≤ 2 * vl → sbgPhi vl δ (vh / 2) = sbgPC vl vh δ) := by
  have h43 : (4 - 3 * δ) ≠ 0 := (by linarith : (0 : ℝ) < 4 - 3 * δ).ne'
  refine ⟨fun h => ?_, fun h => ?_⟩
  · unfold sbgPhi
    rw [max_eq_right (by nlinarith [mul_le_mul_of_nonneg_left h hd0.le])]
    unfold sbgKI sbgPI
    field_simp
  · unfold sbgPhi
    rw [max_eq_left (by nlinarith [mul_le_mul_of_nonneg_left h hd0.le])]
    unfold sbgPC
    ring

/-- If `2v̲ < v̄` and `G_C ≤ G_I` the interior cutoff satisfies `2v̲ ≤ k*`; if `G_I ≤ G_C` the
corner cutoff satisfies `v̄/2 ≤ 2v̲`. -/
theorem sbg_cand_valid (hvl : 0 ≤ vl) (hd0 : 0 < δ) (hd1 : δ < 1) (h2 : 2 * vl < vh) :
    (sbgGC vl vh δ ≤ sbgGI vh δ → 2 * vl ≤ sbgKI vh δ) ∧
    (sbgGI vh δ ≤ sbgGC vl vh δ → vh / 2 ≤ 2 * vl) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · by_contra hn
    push Not at hn
    have e1 := sbgGIk_sub_sbgGCk (vl := vl) (vh := vh) (δ := δ) (sbgKI vh δ)
    have e2 := sbgGC_sub (vl := vl) (vh := vh) (δ := δ) (sbgKI vh δ)
    have : sbgGI vh δ = sbgGIk vh δ (sbgKI vh δ) := rfl
    nlinarith [mul_pos hd0 (mul_pos (by linarith : (0 : ℝ) < vl - sbgKI vh δ / 2)
      (by linarith : (0 : ℝ) < vh - sbgKI vh δ / 2 - vl)), sq_nonneg (sbgKI vh δ - vh / 2)]
  · by_contra hn
    push Not at hn
    have e1 := sbgGIk_sub_sbgGCk (vl := vl) (vh := vh) (δ := δ) (vh / 2)
    have e2 := sbgGI_sub (vh := vh) hd1 (vh / 2)
    have : sbgGC vl vh δ = sbgGCk vl vh δ (vh / 2) := rfl
    have h43 : 0 < 4 - 3 * δ := by linarith
    nlinarith [mul_pos hd0 (mul_pos (by linarith : (0 : ℝ) < vh / 4 - vl)
      (by linarith : (0 : ℝ) < vh - vh / 4 - vl)),
      mul_nonneg h43.le (sq_nonneg (vh / 2 - sbgKI vh δ))]

/-- The interior cutoff is below `v̄` (`δ > 0`) and positive. -/
theorem sbgKI_mem (hlh : vl < vh) (hvl : 0 ≤ vl) (hd0 : 0 < δ) (hd1 : δ < 1) :
    0 < sbgKI vh δ ∧ sbgKI vh δ < vh := by
  have h43 : 0 < 4 - 3 * δ := by linarith
  have hvh : 0 < vh := by linarith
  unfold sbgKI
  refine ⟨by apply div_pos <;> nlinarith, ?_⟩
  rw [div_lt_iff₀ h43]
  nlinarith

/-- **Exercise 9.C.3(b), uniform on `[v̲, v̄]`** (MWG, p. 304; with Exercise 9.C.6). Let
`0 ≤ v̲ < v̄` and `δ ∈ (0, 1)`. A first price `p1` and second prices `r` form a weak PBE with
consistent beliefs iff every `r p ∈ [v̲, v̄]`, after every `p > v̲` the second price is the
consistent one `sbgR p = max (v̲, K(p)/2)`, and either (i) `v̄ ≤ 2v̲` and `p1 = v̲` (every type
buys at once), or (ii) `2v̲ < v̄`, `G_C ≤ G_I` and `p1 = (2 − δ)² v̄/(2 (4 − 3δ))` (interior
second price), or (iii) `2v̲ < v̄`, `G_I ≤ G_C` and `p1 = (1 − δ) v̄/2 + δ v̲` (second price at
the corner `v̲`). -/
theorem exercise_9_C_3b_general (hvl : 0 ≤ vl) (hlh : vl < vh) (hd0 : 0 < δ) (hd1 : δ < 1)
    (p1 : ℝ) (r : ℝ → ℝ) :
    IsSBGWeakPBE vl vh δ p1 r ∧ IsSBGConsistent vl vh δ r ↔
      (∀ p, vl ≤ r p ∧ r p ≤ vh) ∧ (∀ p, vl < p → r p = sbgR vl vh δ p) ∧
      ((vh ≤ 2 * vl ∧ p1 = vl) ∨
        (2 * vl < vh ∧ sbgGC vl vh δ ≤ sbgGI vh δ ∧ p1 = sbgPI vh δ) ∨
        (2 * vl < vh ∧ sbgGI vh δ ≤ sbgGC vl vh δ ∧ p1 = sbgPC vl vh δ)) := by
  have h1 : 0 < 1 - δ := by linarith
  have h43 : 0 < 4 - 3 * δ := by linarith
  obtain ⟨hKI0, hKI1⟩ := sbgKI_mem hlh hvl hd0 hd1
  -- payoffs of a profile with the consistent continuation
  have hbound : ∀ r : ℝ → ℝ, (∀ p, vl ≤ r p) → (∀ p, vl < p → r p = sbgR vl vh δ p) →
      ∀ p q, sbgPay vl vh δ p (r p) q ≤ sbgOpt vl vh δ := by
    intro r hr hrs p q
    by_cases hp : vl < p
    · rw [hrs p hp]
      obtain ⟨hK0, hK1⟩ := sbgK_mem hvl hlh hd0 hd1 hp
      exact (sbgPay_cons hvl hlh hd0 hd1 hp q).1.trans (sbgVal_le_opt hd0 hd1 hK0.le hK1)
    · rw [sbgPay_low hd0 hd1 (not_lt.1 hp) (hr p)]
      have hv := sbgVal_le_opt (vh := vh) hd0 hd1 le_rfl hlh.le
      rw [sbgVal_corner hd0 (by linarith)] at hv
      unfold sbgGCk at hv
      nlinarith [mul_le_mul_of_nonneg_right (not_lt.1 hp) (by linarith : (0 : ℝ) ≤ vh - vl)]
  -- the value of each candidate
  have hcand : ∀ r : ℝ → ℝ, (∀ p, vl ≤ r p) → (∀ p, vl < p → r p = sbgR vl vh δ p) →
      ((vh ≤ 2 * vl → sbgPay vl vh δ vl (r vl) (r vl) = sbgOpt vl vh δ) ∧
      (2 * vl < vh → sbgGC vl vh δ ≤ sbgGI vh δ →
        sbgPay vl vh δ (sbgPI vh δ) (r (sbgPI vh δ)) (r (sbgPI vh δ)) = sbgOpt vl vh δ) ∧
      (2 * vl < vh → sbgGI vh δ ≤ sbgGC vl vh δ →
        sbgPay vl vh δ (sbgPC vl vh δ) (r (sbgPC vl vh δ)) (r (sbgPC vl vh δ)) =
          sbgOpt vl vh δ)) := by
    intro r hr hrs
    refine ⟨fun h => ?_, fun h hG => ?_, fun h hG => ?_⟩
    · rw [sbgPay_low hd0 hd1 le_rfl (hr vl)]
      simp only [sbgOpt, h, ↓reduceIte]
    · have hv := (sbg_cand_valid hvl hd0 hd1 h).1 hG
      have hphi := (sbgPhi_cand (vl := vl) (vh := vh) hd0 hd1).1 hv
      have hgt : vl < sbgPI vh δ := by
        rw [← hphi]; unfold sbgPhi
        exact lt_max_of_lt_left (by nlinarith)
      rw [hrs _ hgt, (sbgPay_cons hvl hlh hd0 hd1 hgt 0).2, ← hphi,
        sbgK_phi hd0 hd1 hKI1.le, sbgVal_interior hd0 hv]
      simp only [sbgOpt, not_le.2 h, ↓reduceIte]
      exact (max_eq_left hG).symm
    · have hv := (sbg_cand_valid hvl hd0 hd1 h).2 hG
      have hphi := (sbgPhi_cand (vl := vl) (vh := vh) hd0 hd1).2 hv
      have hgt : vl < sbgPC vl vh δ := by
        rw [← hphi]; unfold sbgPhi
        exact lt_max_of_lt_left (by nlinarith)
      rw [hrs _ hgt, (sbgPay_cons hvl hlh hd0 hd1 hgt 0).2, ← hphi,
        sbgK_phi hd0 hd1 (by linarith), sbgVal_corner hd0 hv]
      simp only [sbgOpt, not_le.2 h, ↓reduceIte]
      exact (max_eq_right hG).symm
  -- consistency of the consistent continuation
  have hcons : ∀ r : ℝ → ℝ, (∀ p, vl ≤ r p) → (∀ p, vl < p → r p = sbgR vl vh δ p) →
      IsSBGConsistent vl vh δ r := by
    intro r hr hrs p hpos q
    by_cases hp : vl < p
    · rw [hrs p hp] at hpos ⊢
      rw [sbgCut_R hvl hlh hd0 hd1 hp] at hpos ⊢
      exact (sbgRev_opt_iff hvl hpos _).2 rfl q
    · rw [sbgCut_of_le hd0 hd1 (not_lt.1 hp) (hr p)] at hpos
      exact absurd hpos (lt_irrefl _)
  constructor
  · rintro ⟨⟨hr01, -, hroot⟩, hC⟩
    have hrs : ∀ p, vl < p → r p = sbgR vl vh δ p := fun p hp =>
      (sbg_consistent hvl hlh hd0 hd1 hC hp).1
    have hr : ∀ p, vl ≤ r p := fun p => (hr01 p).1
    obtain ⟨cA, cB, cC⟩ := hcand r hr hrs
    refine ⟨hr01, hrs, ?_⟩
    -- the equilibrium payoff is at least `sbgOpt`
    have hopt : sbgOpt vl vh δ ≤ sbgPay vl vh δ p1 (r p1) (r p1) := by
      by_cases h : vh ≤ 2 * vl
      · rw [← cA h]; exact hroot _ _
      · push Not at h
        rcases le_total (sbgGC vl vh δ) (sbgGI vh δ) with hG | hG
        · rw [← cB h hG]; exact hroot _ _
        · rw [← cC h hG]; exact hroot _ _
    by_cases hp : vl < p1
    · rw [hrs p1 hp, (sbgPay_cons hvl hlh hd0 hd1 hp 0).2] at hopt
      obtain ⟨hK0, hK1⟩ := sbgK_mem hvl hlh hd0 hd1 hp
      set K := sbgK vl vh δ p1 with hK
      by_cases h : vh ≤ 2 * vl
      · exfalso
        simp only [sbgOpt, h, ↓reduceIte] at hopt
        rw [sbgVal_corner hd0 (by linarith)] at hopt
        unfold sbgGCk at hopt
        nlinarith [mul_pos h1 (mul_pos (sub_pos.2 hK0) (by linarith : (0 : ℝ) < K + vl - vh))]
      push Not at h
      simp only [sbgOpt, not_le.2 h, ↓reduceIte] at hopt
      rcases le_total K (2 * vl) with hk | hk
      · rw [sbgVal_corner hd0 hk] at hopt
        have e := sbgGC_sub (vl := vl) (vh := vh) (δ := δ) K
        have hGC := le_of_max_le_right hopt
        have hGI := le_of_max_le_left hopt
        have hsq : (K - vh / 2) ^ 2 = 0 := by
          have : (1 - δ) * (K - vh / 2) ^ 2 ≤ 0 := by linarith
          nlinarith [sq_nonneg (K - vh / 2)]
        have hKv : K = vh / 2 := by
          have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hsq
          linarith
        have hp1 : p1 = sbgPhi vl δ K := (sbgPhi_K hd0 hd1 (by rw [← hK, hKv]; linarith)).symm
        rw [hKv] at hp1 hk
        refine Or.inr (Or.inr ⟨h, ?_, ?_⟩)
        · have := sbgGC_sub (vl := vl) (vh := vh) (δ := δ) K
          nlinarith [sq_nonneg (K - vh / 2)]
        · rw [hp1, (sbgPhi_cand hd0 hd1).2 hk]
      · rw [sbgVal_interior hd0 hk] at hopt
        have e := sbgGI_sub (vh := vh) hd1 K
        have hGI := le_of_max_le_left hopt
        have hGC := le_of_max_le_right hopt
        have hsq : (K - sbgKI vh δ) ^ 2 = 0 := by
          have : (4 - 3 * δ) / 4 * (K - sbgKI vh δ) ^ 2 ≤ 0 := by linarith
          nlinarith [sq_nonneg (K - sbgKI vh δ)]
        have hKv : K = sbgKI vh δ := by
          have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hsq
          linarith
        have hp1 : p1 = sbgPhi vl δ K := (sbgPhi_K hd0 hd1 (by rw [← hK, hKv]; exact hKI1)).symm
        rw [hKv] at hp1 hk
        refine Or.inr (Or.inl ⟨h, ?_, ?_⟩)
        · have := sbgGI_sub (vh := vh) hd1 K
          nlinarith [sq_nonneg (K - sbgKI vh δ)]
        · rw [hp1, (sbgPhi_cand hd0 hd1).1 hk]
    · push Not at hp
      rw [sbgPay_low hd0 hd1 hp (hr p1)] at hopt
      by_cases h : vh ≤ 2 * vl
      · simp only [sbgOpt, h, ↓reduceIte] at hopt
        refine Or.inl ⟨h, le_antisymm hp ?_⟩
        nlinarith
      · exfalso
        push Not at h
        simp only [sbgOpt, not_le.2 h, ↓reduceIte] at hopt
        have e := sbgGC_sub (vl := vl) (vh := vh) (δ := δ) vl
        have hGC := le_of_max_le_right hopt
        unfold sbgGCk at e
        nlinarith [mul_pos h1 (sq_pos_of_pos (by linarith : (0 : ℝ) < vh / 2 - vl)),
          mul_le_mul_of_nonneg_right hp (by linarith : (0 : ℝ) ≤ vh - vl)]
  · rintro ⟨hr01, hrs, hcase⟩
    have hr : ∀ p, vl ≤ r p := fun p => (hr01 p).1
    obtain ⟨cA, cB, cC⟩ := hcand r hr hrs
    have hC := hcons r hr hrs
    have hval : sbgPay vl vh δ p1 (r p1) (r p1) = sbgOpt vl vh δ := by
      rcases hcase with ⟨h, rfl⟩ | ⟨h, hG, rfl⟩ | ⟨h, hG, rfl⟩
      · exact cA h
      · exact cB h hG
      · exact cC h hG
    exact ⟨⟨hr01, fun h => hC p1 h, fun p q => hval ▸ hbound r hr hrs p q⟩, hC⟩

/-- **Exercise 9.C.3(b), the equilibrium outcomes** (MWG, p. 304). (i) If `v̄ ≤ 2v̲`, at the first
price `v̲` every type buys at once (whatever second price is expected). (ii) If `2v̲ < v̄` and
`G_C ≤ G_I`, at `sbgPI` the cutoff is `k* = (2 − δ) v̄/(4 − 3δ)` and the second price `k*/2`.
(iii) If `2v̲ < v̄` and `G_I ≤ G_C`, at `sbgPC` the cutoff is `v̄/2` and the second price is the
corner `v̲`. -/
theorem exercise_9_C_3b_general_outcomes (hvl : 0 ≤ vl) (hlh : vl < vh) (hd0 : 0 < δ)
    (hd1 : δ < 1) :
    (∀ r, vl ≤ r → sbgCut vl vh δ vl r = vl) ∧
    (2 * vl < vh → sbgGC vl vh δ ≤ sbgGI vh δ →
      sbgCut vl vh δ (sbgPI vh δ) (sbgR vl vh δ (sbgPI vh δ)) = sbgKI vh δ ∧
      sbgR vl vh δ (sbgPI vh δ) = sbgKI vh δ / 2) ∧
    (2 * vl < vh → sbgGI vh δ ≤ sbgGC vl vh δ →
      sbgCut vl vh δ (sbgPC vl vh δ) (sbgR vl vh δ (sbgPC vl vh δ)) = vh / 2 ∧
      sbgR vl vh δ (sbgPC vl vh δ) = vl) := by
  obtain ⟨hKI0, hKI1⟩ := sbgKI_mem hlh hvl hd0 hd1
  refine ⟨fun r hr => sbgCut_of_le hd0 hd1 le_rfl hr, fun h hG => ?_, fun h hG => ?_⟩
  · have hv := (sbg_cand_valid hvl hd0 hd1 h).1 hG
    have hphi := (sbgPhi_cand (vl := vl) (vh := vh) hd0 hd1).1 hv
    have hgt : vl < sbgPI vh δ := by
      rw [← hphi]; unfold sbgPhi
      exact lt_max_of_lt_left (by nlinarith)
    have hK : sbgK vl vh δ (sbgPI vh δ) = sbgKI vh δ := by
      rw [← hphi, sbgK_phi hd0 hd1 hKI1.le]
    rw [sbgCut_R hvl hlh hd0 hd1 hgt, hK]
    refine ⟨rfl, ?_⟩
    unfold sbgR
    rw [hK]
    exact max_eq_right (by linarith)
  · have hv := (sbg_cand_valid hvl hd0 hd1 h).2 hG
    have hphi := (sbgPhi_cand (vl := vl) (vh := vh) hd0 hd1).2 hv
    have hgt : vl < sbgPC vl vh δ := by
      rw [← hphi]; unfold sbgPhi
      exact lt_max_of_lt_left (by nlinarith)
    have hK : sbgK vl vh δ (sbgPC vl vh δ) = vh / 2 := by
      rw [← hphi, sbgK_phi hd0 hd1 (by linarith)]
    rw [sbgCut_R hvl hlh hd0 hd1 hgt, hK]
    refine ⟨rfl, ?_⟩
    unfold sbgR
    rw [hK]
    exact max_eq_left (by linarith)

/-- **Exercise 9.C.3(b), existence** (MWG, p. 304). A weak PBE with consistent beliefs exists
for all `0 ≤ v̲ < v̄` and `δ ∈ (0, 1)`. -/
theorem exercise_9_C_3b_general_exists (hvl : 0 ≤ vl) (hlh : vl < vh) (hd0 : 0 < δ)
    (hd1 : δ < 1) : ∃ p1 r, IsSBGWeakPBE vl vh δ p1 r ∧ IsSBGConsistent vl vh δ r := by
  classical
  set r : ℝ → ℝ := fun p => if vl < p then sbgR vl vh δ p else vl with hr
  have hr01 : ∀ p, vl ≤ r p ∧ r p ≤ vh := by
    intro p
    simp only [hr]
    split_ifs with hp
    · obtain ⟨hK0, hK1⟩ := sbgK_mem hvl hlh hd0 hd1 hp
      exact ⟨le_max_left _ _, max_le hlh.le (by linarith)⟩
    · exact ⟨le_rfl, hlh.le⟩
  have hrs : ∀ p, vl < p → r p = sbgR vl vh δ p := fun p hp => by simp [hr, hp]
  by_cases h : vh ≤ 2 * vl
  · exact ⟨vl, r, (exercise_9_C_3b_general hvl hlh hd0 hd1 vl r).2
      ⟨hr01, hrs, Or.inl ⟨h, rfl⟩⟩⟩
  · push Not at h
    rcases le_total (sbgGC vl vh δ) (sbgGI vh δ) with hG | hG
    · exact ⟨_, r, (exercise_9_C_3b_general hvl hlh hd0 hd1 _ r).2
        ⟨hr01, hrs, Or.inr (Or.inl ⟨h, hG, rfl⟩)⟩⟩
    · exact ⟨_, r, (exercise_9_C_3b_general hvl hlh hd0 hd1 _ r).2
        ⟨hr01, hrs, Or.inr (Or.inr ⟨h, hG, rfl⟩)⟩⟩

/-- For `v̲ = 0`, `v̄ = 1` the weak PBE conditions are those of `IsSBUWeakPBE`
(`SellerBuyer.lean`): the period-2 revenues differ by the factor `1/k`. -/
theorem isSBGWeakPBE_zero_one_iff (δ p1 : ℝ) (r : ℝ → ℝ) :
    IsSBGWeakPBE 0 1 δ p1 r ↔ IsSBUWeakPBE δ p1 r := by
  have hiff : ∀ k : ℝ, 0 < k → ∀ x y, sbURev k x ≤ sbURev k y ↔ sbgRev 0 k x ≤ sbgRev 0 k y := by
    intro k hk x y
    have e : ∀ z, sbURev k z = sbgRev 0 k z / k := fun z => by
      unfold sbURev sbgRev
      ring
    rw [e, e]
    exact div_le_div_iff_of_pos_right hk
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, fun hk q => (hiff _ hk _ _).2 (h2 hk q), h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, fun hk q => (hiff _ hk _ _).1 (h2 hk q), h3⟩

/-- **Exercise 9.C.3(b), instances** (MWG, p. 304), `v̄ = 1`, `δ = 1/2`. (i) `v̲ = 0`: the unique
consistent weak PBE first price is the interior `9/20 = sbPStar (1/2)` (the `v̲ = 0` answer of
`exercise_9_C_3b`). (ii) `v̲ = 3/10`: it is the corner price `2/5`, with cutoff `1/2` and second
price `3/10 = v̲`. (iii) `v̲ = 3/5`: it is `3/5 = v̲` and every type buys at once. -/
theorem exercise_9_C_3b_general_examples :
    (∀ p1 r, IsSBGWeakPBE 0 1 (1 / 2) p1 r ∧ IsSBGConsistent 0 1 (1 / 2) r →
      p1 = 9 / 20 ∧ p1 = sbPStar (1 / 2)) ∧
    (∀ p1 r, IsSBGWeakPBE (3 / 10) 1 (1 / 2) p1 r ∧ IsSBGConsistent (3 / 10) 1 (1 / 2) r →
      p1 = 2 / 5 ∧ sbgCut (3 / 10) 1 (1 / 2) p1 (r p1) = 1 / 2 ∧ r p1 = 3 / 10) ∧
    (∀ p1 r, IsSBGWeakPBE (3 / 5) 1 (1 / 2) p1 r ∧ IsSBGConsistent (3 / 5) 1 (1 / 2) r →
      p1 = 3 / 5 ∧ sbgCut (3 / 5) 1 (1 / 2) p1 (r p1) = 3 / 5) := by
  have hGI : sbgGI 1 (1 / 2) = 9 / 40 := by
    norm_num [sbgGI, sbgGIk, sbgKI]
  refine ⟨fun p1 r h => ?_, fun p1 r h => ?_, fun p1 r h => ?_⟩
  · obtain ⟨-, -, hc⟩ := (exercise_9_C_3b_general (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) p1 r).1 h
    have hGC : sbgGC 0 1 (1 / 2) = 1 / 8 := by norm_num [sbgGC, sbgGCk]
    rcases hc with ⟨h1, -⟩ | ⟨-, -, rfl⟩ | ⟨-, h3, -⟩
    · norm_num at h1
    · norm_num [sbgPI, sbPStar]
    · rw [hGI, hGC] at h3; norm_num at h3
  · have hc := (exercise_9_C_3b_general (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) p1 r).1 h
    obtain ⟨-, hrs, hc⟩ := hc
    have hGC : sbgGC (3 / 10) 1 (1 / 2) = 23 / 100 := by norm_num [sbgGC, sbgGCk]
    have hlt : sbgGI 1 (1 / 2) ≤ sbgGC (3 / 10) 1 (1 / 2) := by rw [hGI, hGC]; norm_num
    rcases hc with ⟨h1, -⟩ | ⟨-, h2, -⟩ | ⟨h2, h3, rfl⟩
    · norm_num at h1
    · rw [hGI, hGC] at h2; norm_num at h2
    · obtain ⟨-, -, hout⟩ := exercise_9_C_3b_general_outcomes (vl := 3 / 10) (vh := 1)
        (δ := 1 / 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      obtain ⟨o1, o2⟩ := hout h2 h3
      have hgt : (3 / 10 : ℝ) < sbgPC (3 / 10) 1 (1 / 2) := by norm_num [sbgPC]
      rw [hrs _ hgt, o1, o2]
      norm_num [sbgPC]
  · have hc := (exercise_9_C_3b_general (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) p1 r).1 h
    obtain ⟨hr01, -, hc⟩ := hc
    rcases hc with ⟨-, rfl⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
    · exact ⟨rfl, ((exercise_9_C_3b_general_outcomes (by norm_num) (by norm_num) (by norm_num)
        (by norm_num)).1 _ (hr01 _).1)⟩
    · norm_num at h1
    · norm_num at h1

end MWG.DynamicGames
