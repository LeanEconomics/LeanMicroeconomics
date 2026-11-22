/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPositiveEquilibriumTheory.TatonnementTwoGoods

/-!
# Property (b) with two goods and several equilibria (MWG Section 17.H, p. 622)

Property (b) (p. 622): with two goods "from any initial position, the relative prices converge to
some equilibrium". `footnote_17_62_two_goods` proves it for a unique equilibrium; here it is
proved for any excess demand satisfying (i)-(v) of Proposition 17.B.2, with any number of
equilibria (`section_17_H_property_b`).

The relative price `r(t) = p₁(t)/p₂(t)` solves `dr/dt = g(r) k(t)` with `g(r) = z₁(r, 1)` merely
continuous and `k(t) > 0` (footnote 60). Trajectories need not be unique, so the argument is
one-dimensional and global:
* a scalar solution of `dF/dt = G(F) k` (`k > 0`) crossing a level `c` downwards has `G(c) ≤ 0`
  (`ctg_fall`), upwards `G(c) ≥ 0` (`ctg_rise`), and cannot cross a band of zeros of `G`
  (`ctg_plateau`); hence it has no strict peak or valley (`ctg_no_peak`) and is monotone
  (`ctg_monotone`);
* a monotone solution bounded by the boundary behaviour (footnote 8) converges, and its limit is a
  zero of `G` (`ctg_converges`); the decreasing case reduces to the increasing one through
  `1/r(t)`.
-/

namespace MWG.PositiveEquilibriumTheory

open Filter Topology Set

/-! ### One-dimensional solutions with a sign-preserving factor -/

/-- A positive (right) derivative makes `F` larger just to the right of `s`. -/
theorem ctg_right_gt {F : ℝ → ℝ} {d s : ℝ} (hF : HasDerivWithinAt F d (Ici s) s) (hd : 0 < d) :
    ∀ᶠ t in 𝓝[>] s, F s < F t := by
  have h := (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl s)).1
    (hF.mono Ioi_subset_Ici_self)
  filter_upwards [h.eventually (lt_mem_nhds hd), self_mem_nhdsWithin] with t ht hts
  rw [slope_def_field] at ht
  have hts' : 0 < t - s := sub_pos.2 hts
  have := (div_pos_iff_of_pos_right hts').1 ht
  linarith

variable {F G k : ℝ → ℝ}

/-- A solution of `dF/dt = G(F) k` (`k > 0`) on `[a, b] ⊆ [0, ∞)` with `F(a) ≥ c > F(b)` has
`G(c) ≤ 0`: at the last time `s` with `F(s) = c`, `G(c) > 0` would push `F` above `c`. -/
theorem ctg_fall (hF : ∀ t, 0 ≤ t → HasDerivWithinAt F (G (F t) * k t) (Ici 0) t)
    (hk : ∀ t, 0 ≤ t → 0 < k t) {a b c : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hca : c ≤ F a)
    (hbc : F b < c) : G c ≤ 0 := by
  have hcont : ∀ a', 0 ≤ a' → ∀ b', ContinuousOn F (Icc a' b') := fun a' ha' b' t ht =>
    (hF t (ha'.trans ht.1)).continuousWithinAt.mono fun u hu => ha'.trans hu.1
  have hS : IsCompact (Icc a b ∩ F ⁻¹' {c}) :=
    isCompact_Icc.of_isClosed_subset
      ((hcont a ha b).preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton)
      inter_subset_left
  obtain ⟨u, hu, hFu⟩ := intermediate_value_Icc' hab (hcont a ha b) ⟨hbc.le, hca⟩
  obtain ⟨s, ⟨hsI, hsc⟩, hsmax⟩ := hS.exists_isGreatest ⟨u, hu, hFu⟩
  have hsc' : F s = c := hsc
  have hs0 : 0 ≤ s := ha.trans hsI.1
  have hsb : s < b := lt_of_le_of_ne hsI.2 fun h => by rw [h] at hsc'; linarith
  have hafter : ∀ t ∈ Ioc s b, F t < c := by
    intro t ht
    by_contra hge
    push Not at hge
    obtain ⟨w, hw, hwc⟩ := intermediate_value_Icc' ht.2 (hcont t (hs0.trans ht.1.le) b)
      ⟨hbc.le, hge⟩
    have := hsmax ⟨⟨(hsI.1.trans ht.1.le).trans hw.1, hw.2⟩, hwc⟩
    linarith [hw.1, ht.1]
  by_contra hG
  push Not at hG
  have hd : HasDerivWithinAt F (G (F s) * k s) (Ici s) s :=
    (hF s hs0).mono fun u (hu : s ≤ u) => hs0.trans hu
  rw [hsc'] at hd
  obtain ⟨t, h1, h2⟩ := ((ctg_right_gt hd (mul_pos hG (hk s hs0))).and (Ioc_mem_nhdsGT hsb)).exists
  have := hafter t h2
  rw [hsc'] at h1
  linarith

/-- A solution of `dF/dt = G(F) k` (`k > 0`) on `[a, b] ⊆ [0, ∞)` with `F(a) ≤ c < F(b)` has
`G(c) ≥ 0` (`ctg_fall` applied to `-F`). -/
theorem ctg_rise (hF : ∀ t, 0 ≤ t → HasDerivWithinAt F (G (F t) * k t) (Ici 0) t)
    (hk : ∀ t, 0 ≤ t → 0 < k t) {a b c : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hac : F a ≤ c)
    (hcb : c < F b) : 0 ≤ G c := by
  have h := ctg_fall (F := fun t => -F t) (G := fun v => -G (-v)) (k := k)
    (fun t ht => by convert (hF t ht).neg using 1; simp) hk ha hab (c := -c)
    (by linarith) (by linarith)
  simp only [neg_neg] at h
  linarith

/-- A solution of `dF/dt = G(F) k` (`k > 0`) cannot rise from `c₁` to `c₂ > c₁` if `G = 0` on
`[c₁, c₂)`: between the last time at `c₁` and the next time at `c₂` its derivative vanishes. -/
theorem ctg_plateau (hF : ∀ t, 0 ≤ t → HasDerivWithinAt F (G (F t) * k t) (Ici 0) t)
    {a b c₁ c₂ : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (h1 : F a ≤ c₁) (h12 : c₁ < c₂) (h2 : c₂ ≤ F b)
    (hG : ∀ v, c₁ ≤ v → v < c₂ → G v = 0) : False := by
  have hcont : ∀ a', 0 ≤ a' → ∀ b', ContinuousOn F (Icc a' b') := fun a' ha' b' t ht =>
    (hF t (ha'.trans ht.1)).continuousWithinAt.mono fun u hu => ha'.trans hu.1
  have hS1 : IsCompact (Icc a b ∩ F ⁻¹' {c₁}) :=
    isCompact_Icc.of_isClosed_subset
      ((hcont a ha b).preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton)
      inter_subset_left
  obtain ⟨u, hu, hFu⟩ := intermediate_value_Icc hab (hcont a ha b) ⟨h1, by linarith⟩
  obtain ⟨s₁, ⟨hs1I, hs1c⟩, hs1max⟩ := hS1.exists_isGreatest ⟨u, hu, hFu⟩
  have hs1c' : F s₁ = c₁ := hs1c
  have hs10 : 0 ≤ s₁ := ha.trans hs1I.1
  have hafter : ∀ t ∈ Ioc s₁ b, c₁ < F t := by
    intro t ht
    by_contra hle
    push Not at hle
    obtain ⟨w, hw, hwc⟩ := intermediate_value_Icc ht.2 (hcont t (hs10.trans ht.1.le) b)
      ⟨hle, by linarith⟩
    have := hs1max ⟨⟨(hs1I.1.trans ht.1.le).trans hw.1, hw.2⟩, hwc⟩
    linarith [hw.1, ht.1]
  have hS2 : IsCompact (Icc s₁ b ∩ F ⁻¹' {c₂}) :=
    isCompact_Icc.of_isClosed_subset
      ((hcont s₁ hs10 b).preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton)
      inter_subset_left
  obtain ⟨u2, hu2, hFu2⟩ := intermediate_value_Icc hs1I.2 (hcont s₁ hs10 b)
    ⟨by rw [hs1c']; exact h12.le, h2⟩
  obtain ⟨s₂, ⟨hs2I, hs2c⟩, hs2min⟩ := hS2.exists_isLeast ⟨u2, hu2, hFu2⟩
  have hs2c' : F s₂ = c₂ := hs2c
  have hbefore : ∀ t ∈ Ico s₁ s₂, F t < c₂ := by
    intro t ht
    by_contra hge
    push Not at hge
    obtain ⟨w, hw, hwc⟩ := intermediate_value_Icc ht.1 (hcont s₁ hs10 t)
      ⟨by rw [hs1c']; exact h12.le, hge⟩
    have := hs2min ⟨⟨hw.1, hw.2.trans (ht.2.le.trans hs2I.2)⟩, hwc⟩
    linarith [hw.2, ht.2]
  have hconst := constant_of_has_deriv_right_zero (hcont s₁ hs10 s₂) (fun x hx => by
    have hx0 : 0 ≤ x := hs10.trans hx.1
    have hlo : c₁ ≤ F x := by
      rcases eq_or_lt_of_le hx.1 with h | h
      · rw [← h, hs1c']
      · exact (hafter x ⟨h, hx.2.le.trans hs2I.2⟩).le
    have hd := (hF x hx0).mono fun u (hu : x ≤ u) => hx0.trans hu
    rwa [hG (F x) hlo (hbefore x hx), zero_mul] at hd) s₂ ⟨hs2I.1, le_rfl⟩
  rw [hs2c', hs1c'] at hconst
  linarith

/-- A solution of `dF/dt = G(F) k` (`k > 0`) has no strict peak `F(a) < F(b) > F(c)`,
`0 ≤ a < b < c`: every level between `max(F(a), F(c))` and `F(b)` is crossed upwards and
downwards, so `G` vanishes there, and `ctg_plateau` applies. -/
theorem ctg_no_peak (hF : ∀ t, 0 ≤ t → HasDerivWithinAt F (G (F t) * k t) (Ici 0) t)
    (hk : ∀ t, 0 ≤ t → 0 < k t) {a b c : ℝ} (ha : 0 ≤ a) (hab : a < b) (hbc : b < c)
    (h1 : F a < F b) (h2 : F c < F b) : False := by
  set m := max (F a) (F c) with hm
  have hmv : m < F b := max_lt h1 h2
  have hG : ∀ v, m < v → v < F b → G v = 0 := fun v hv1 hv2 =>
    le_antisymm (ctg_fall hF hk (ha.trans hab.le) hbc.le hv2.le
      (lt_of_le_of_lt (le_max_right _ _) hv1))
      (ctg_rise hF hk ha hab.le ((le_max_left _ _).trans hv1.le) hv2)
  refine ctg_plateau hF ha hab.le (c₁ := (2 * m + F b) / 3) (c₂ := (m + 2 * F b) / 3)
    (by linarith [le_max_left (F a) (F c)]) (by linarith) (by linarith) fun v hv1 hv2 =>
      hG v (by linarith) (by linarith)

/-- A solution of `dF/dt = G(F) k` (`k > 0`, `G` arbitrary) on `[0, ∞)` is monotone. -/
theorem ctg_monotone (hF : ∀ t, 0 ≤ t → HasDerivWithinAt F (G (F t) * k t) (Ici 0) t)
    (hk : ∀ t, 0 ≤ t → 0 < k t) : MonotoneOn F (Ici 0) ∨ AntitoneOn F (Ici 0) := by
  by_contra h
  push Not at h
  obtain ⟨a, ha, b, -, c, -, hab, hbc, h⟩ :=
    not_monotoneOn_not_antitoneOn_iff_exists_lt_lt.1 h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ctg_no_peak hF hk ha hab hbc h1 h2
  · refine ctg_no_peak (F := fun t => -F t) (G := fun v => -G (-v)) (k := k)
      (fun t ht => by convert (hF t ht).neg using 1; simp) hk ha hab hbc
      (by linarith) (by linarith)

/-- A nondecreasing positive solution of `dF/dt = G(F) k` with `k ≥ κ > 0`, `G` continuous on
`(0, ∞)` and negative along every sequence tending to `∞`, converges to a zero `L > 0` of `G`. -/
theorem ctg_converges (hF : ∀ t, 0 ≤ t → HasDerivWithinAt F (G (F t) * k t) (Ici 0) t)
    {κ : ℝ} (hκ : 0 < κ) (hk : ∀ t, 0 ≤ t → κ ≤ k t) (hpos : ∀ t, 0 ≤ t → 0 < F t)
    (hmono : MonotoneOn F (Ici 0)) (hGc : ContinuousOn G (Ioi 0))
    (hhigh : ∀ bs : ℕ → ℝ, (∀ n, 0 < bs n) → Tendsto bs atTop atTop →
      ∀ᶠ n in atTop, G (bs n) < 0) :
    ∃ L, 0 < L ∧ G L = 0 ∧ Tendsto F atTop (𝓝 L) := by
  have hk0 : ∀ t, 0 ≤ t → 0 < k t := fun t ht => lt_of_lt_of_le hκ (hk t ht)
  -- `G(F(t)) ≥ 0`
  have hGnn : ∀ t, 0 ≤ t → 0 ≤ G (F t) := by
    intro t ht
    by_contra hneg
    push Not at hneg
    have hd : HasDerivWithinAt (fun u => -F u) (-(G (F t) * k t)) (Ici t) t :=
      ((hF t ht).mono fun u (hu : t ≤ u) => ht.trans hu).neg
    obtain ⟨u, h1, h2⟩ := ((ctg_right_gt hd (by nlinarith [hk0 t ht])).and
      self_mem_nhdsWithin).exists
    have := hmono (Set.mem_Ici.2 ht) (Set.mem_Ici.2 (ht.trans (le_of_lt h2))) (le_of_lt h2)
    linarith
  -- bounded above
  have hbdd : ∃ M, ∀ t, 0 ≤ t → F t ≤ M := by
    by_contra hun
    push Not at hun
    have htend : Tendsto (fun n : ℕ => F n) atTop atTop := by
      refine tendsto_atTop.2 fun M => ?_
      obtain ⟨t, ht, hMt⟩ := hun M
      refine (eventually_ge_atTop ⌈t⌉₊).mono fun n hn => ?_
      have htn : t ≤ n := (Nat.le_ceil t).trans (by exact_mod_cast hn)
      exact hMt.le.trans (hmono (Set.mem_Ici.2 ht) (Set.mem_Ici.2 (ht.trans htn)) htn)
    obtain ⟨n, hn⟩ := (hhigh _ (fun n => hpos n n.cast_nonneg) htend).exists
    linarith [hGnn n n.cast_nonneg]
  obtain ⟨M, hM⟩ := hbdd
  -- the limit
  set Ft : ℝ → ℝ := fun t => F (max t 0) with hFt
  have hFtm : Monotone Ft := fun x y hxy =>
    hmono (Set.mem_Ici.2 (le_max_right _ _)) (Set.mem_Ici.2 (le_max_right _ _))
      (max_le_max hxy le_rfl)
  have hFtb : BddAbove (range Ft) := ⟨M, by rintro _ ⟨t, rfl⟩; exact hM _ (le_max_right _ _)⟩
  have hlimt := tendsto_atTop_ciSup hFtm hFtb
  set L := ⨆ t, Ft t with hL
  have hlim : Tendsto F atTop (𝓝 L) := hlimt.congr' ((eventually_ge_atTop 0).mono fun t ht => by
    simp only [hFt, max_eq_left ht])
  have hFL : ∀ t, 0 ≤ t → F t ≤ L := fun t ht => by
    have := hFtm.ge_of_tendsto hlimt t
    simpa [hFt, max_eq_left ht] using this
  have hLpos : 0 < L := lt_of_lt_of_le (hpos 0 le_rfl) (hFL 0 le_rfl)
  have hGlim : Tendsto (fun t => G (F t)) atTop (𝓝 (G L)) :=
    ((hGc.continuousAt (Ioi_mem_nhds hLpos)).tendsto).comp hlim
  have hGL0 : 0 ≤ G L := ge_of_tendsto hGlim ((eventually_ge_atTop 0).mono hGnn)
  refine ⟨L, hLpos, le_antisymm ?_ hGL0, hlim⟩
  -- `G(L) > 0` would make `F` grow at a linear rate
  by_contra hGL
  push Not at hGL
  obtain ⟨T, hT⟩ := eventually_atTop.1 ((hGlim.eventually (lt_mem_nhds (half_lt_self hGL))).and
    (eventually_ge_atTop 0))
  have hT0 : 0 ≤ T := (hT T le_rfl).2
  set δ := G L / 2 * κ with hδ
  have hδpos : 0 < δ := by positivity
  have hgrow : ∀ t, T ≤ t → F T + δ * (t - T) ≤ F t := by
    intro t hTt
    refine image_le_of_deriv_right_le_deriv_boundary (f := fun x => F T + δ * (x - T))
      (f' := fun _ => δ) (B := F) (B' := fun x => G (F x) * k x)
      ((continuous_const.add (continuous_const.mul (continuous_id.sub continuous_const))
        ).continuousOn) (fun x _ => by
          simpa using ((hasDerivWithinAt_id x (Ici x)).sub_const T).const_mul δ |>.const_add
            (F T)) (by simp) (fun x hx => (hF x (hT0.trans hx.1)).continuousWithinAt.mono
              fun u hu => hT0.trans hu.1)
      (fun x hx => (hF x (hT0.trans hx.1)).mono fun u (hu : x ≤ u) => (hT0.trans hx.1).trans hu)
      (fun x hx => ?_) ⟨hTt, le_rfl⟩
    have hx0 : 0 ≤ x := hT0.trans hx.1
    have h1 := (hT x hx.1).1
    have h2 := hk x hx0
    have : G L / 2 * κ ≤ G (F x) * k x :=
      mul_le_mul h1.le h2 hκ.le ((half_pos hGL).le.trans h1.le)
    simpa [hδ] using this
  set t := T + (L - F T) / δ + 1 with ht
  have hTt : T ≤ t := by
    have : 0 ≤ (L - F T) / δ := div_nonneg (by linarith [hFL T hT0]) hδpos.le
    linarith
  have h1 := hgrow t hTt
  have h2 := hFL t (hT0.trans hTt)
  have : δ * (t - T) = L - F T + δ := by
    rw [ht]
    field_simp
    ring
  linarith

/-! ### Property (b) -/

variable {c : Fin 2 → ℝ} {z : (Fin 2 → ℝ) → Fin 2 → ℝ} {p : ℝ → Fin 2 → ℝ}

/-- **Section 17.H, property (b)** (MWG, p. 622). With two goods and an excess demand
satisfying (i)-(v) of Proposition 17.B.2, along every tâtonnement trajectory the relative price
`p₁(t)/p₂(t)` converges to the relative price `r̄` of some equilibrium `(r̄, 1)`, whatever the
number of equilibria. -/
theorem section_17_H_property_b (hc : ∀ l, 0 < c l) (hz : IsStandardExcessDemand z)
    (hp : IsTatPath c z p) :
    ∃ rb : ℝ, IsEqmPrice z ![rb, 1] ∧ Tendsto (fun t => p t 0 / p t 1) atTop (𝓝 rb) := by
  set r : ℝ → ℝ := fun t => p t 0 / p t 1 with hr
  set g : ℝ → ℝ := fun s => z ![s, 1] 0 with hg
  set k : ℝ → ℝ := fun t => ttgFactor c (p t) with hkdef
  set κ := c 0 / Real.sqrt (c 1 * wNormSq c (p 0)) with hκ
  have hκpos : 0 < κ := div_pos (hc 0) (Real.sqrt_pos.2 (mul_pos (hc 1)
    (wNormSq_pos hc (posOrthant_ne_zero (hp.1 0 le_rfl)))))
  have hF : ∀ t, 0 ≤ t → HasDerivWithinAt r (g (r t) * k t) (Ici 0) t := fun t ht =>
    footnote_17_60 hz.homogeneous hz.walras hp ht
  have hkκ : ∀ t, 0 ≤ t → κ ≤ k t := fun t ht => ttg_factor_lower hc hz.walras hp ht
  have hk0 : ∀ t, 0 ≤ t → 0 < k t := fun t ht => ttgFactor_pos hc (hp.1 t ht)
  have hrpos : ∀ t, 0 ≤ t → 0 < r t := fun t ht => div_pos (hp.1 t ht 0) (hp.1 t ht 1)
  have hvec : Continuous fun s : ℝ => (![s, 1] : Fin 2 → ℝ) := by
    refine continuous_pi fun l => ?_
    fin_cases l
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      exact continuous_id'
    · simpa using continuous_const
  have hgc : ContinuousOn g (Ioi 0) :=
    (continuous_apply 0).comp_continuousOn (hz.continuous.comp hvec.continuousOn
      fun s hs => ttg_vec_mem hs)
  have heqm : ∀ rb, 0 < rb → g rb = 0 → IsEqmPrice z ![rb, 1] := by
    intro rb hrb h0
    refine ⟨ttg_vec_mem hrb, funext fun l => ?_⟩
    fin_cases l
    · exact h0
    · have := ttg_walras hz.walras (ttg_vec_mem hrb)
      simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        Pi.zero_apply] at this ⊢
      rw [this]
      change -(rb / 1) * g rb = 0
      rw [h0, mul_zero]
  rcases ctg_monotone hF hk0 with hmono | hanti
  · obtain ⟨L, hL, hgL, hlim⟩ := ctg_converges hF hκpos hkκ hrpos hmono hgc
      fun bs hbs htend => footnote_17_8_high hz hbs htend
    exact ⟨L, heqm L hL hgL, hlim⟩
  · -- the decreasing case: `1/r(t)` is nondecreasing
    set κ' := κ / r 0 ^ 2 with hκ'
    have hr0 := hrpos 0 le_rfl
    have hκ'pos : 0 < κ' := by positivity
    have hF' : ∀ t, 0 ≤ t → HasDerivWithinAt (fun u => (r u)⁻¹)
        ((fun v => -g v⁻¹) ((r t)⁻¹) * (k t / r t ^ 2)) (Ici 0) t := by
      intro t ht
      convert (hF t ht).inv (hrpos t ht).ne' using 1
      simp only [inv_inv]
      ring
    have hk' : ∀ t, 0 ≤ t → κ' ≤ k t / r t ^ 2 := by
      intro t ht
      have hrt := hrpos t ht
      have hle : r t ≤ r 0 := hanti (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 ht) ht
      have hsq : r t ^ 2 ≤ r 0 ^ 2 := pow_le_pow_left₀ hrt.le hle 2
      calc κ' = κ / r 0 ^ 2 := rfl
        _ ≤ k t / r 0 ^ 2 := div_le_div_of_nonneg_right (hkκ t ht) (by positivity)
        _ ≤ k t / r t ^ 2 := div_le_div_of_nonneg_left (hk0 t ht).le (by positivity) hsq
    have hmono' : MonotoneOn (fun u => (r u)⁻¹) (Ici 0) := fun x hx y hy hxy =>
      inv_anti₀ (hrpos y hy) (hanti hx hy hxy)
    have hgc' : ContinuousOn (fun v => -g v⁻¹) (Ioi 0) :=
      (hgc.comp (continuousOn_inv₀.mono fun v (hv : 0 < v) => hv.ne')
        fun v (hv : 0 < v) => inv_pos.2 hv).neg
    obtain ⟨L, hL, hgL, hlim⟩ := ctg_converges hF' hκ'pos hk'
      (fun t ht => inv_pos.2 (hrpos t ht)) hmono' hgc' fun bs hbs htend => by
        have hlow := footnote_17_8_low hz (as := fun n => (bs n)⁻¹) (fun n => inv_pos.2 (hbs n))
          (tendsto_inv_atTop_zero.comp htend)
        exact hlow.mono fun n hn => by simp only [hg] at hn ⊢; linarith
    refine ⟨L⁻¹, heqm L⁻¹ (inv_pos.2 hL) (by linarith), ?_⟩
    have := hlim.inv₀ hL.ne'
    simpa using this

end MWG.PositiveEquilibriumTheory
