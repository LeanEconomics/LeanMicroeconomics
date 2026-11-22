/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPositiveEquilibriumTheory.Regularity
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# The index theorem with two goods (MWG Section 17.D, pp. 592-593)

For `L = 2` (normalization `p₂ = 1`), `Dẑ(p̂)` is the slope of `t ↦ z₁(t, 1)` and the index of
a regular equilibrium is `-sign ∂z₁/∂p₁`. This module proves, from properties (i)-(v) of
Proposition 17.B.2 and regularity alone:

* the slopes alternate in sign, starting (and ending) negative: the smallest equilibrium has
  negative slope (`two_goods_first_slope_neg`), the largest too (`two_goods_last_slope_neg`), and
  consecutive equilibria have slopes of opposite sign (`two_goods_slopes_alternate`) (MWG p. 592);
* **Proposition 17.D.2** for `L = 2` (`proposition_17_D_2_two_goods`): the sum of the indices of
  the (finitely many) equilibria is `+1`;
* the number of equilibria of a regular economy is odd (`two_goods_card_odd`, p. 593) and in
  particular nonzero.

The core is a one-variable telescoping argument (`two_goods_telescope`): if `g` is continuous on
`(0, ∞)`, has finitely many zeros there, each with nonzero derivative, then for `0 < a < b` with
`g(a), g(b) ≠ 0`, `2 ∑_{zeros t ∈ (a,b)} (-sign g'(t)) = sign g(a) - sign g(b)`. The sign of
`g` is constant between zeros (intermediate value theorem, `two_goods_pos_iff`) and changes at a
regular zero according to the sign of the slope (`two_goods_local_sign`).
-/

namespace MWG.PositiveEquilibriumTheory

open Filter Topology

/-- The sign of a real number as an integer (`+1`, `0`, `-1`; footnote 15). -/
noncomputable def itgSgn (x : ℝ) : ℤ := ((SignType.sign x : SignType) : ℤ)

theorem itgSgn_pos {x : ℝ} (h : 0 < x) : itgSgn x = 1 := by simp [itgSgn, sign_pos h]

theorem itgSgn_neg {x : ℝ} (h : x < 0) : itgSgn x = -1 := by simp [itgSgn, sign_neg h]

/-- Two nonzero numbers with the same positivity have the same sign. -/
theorem itgSgn_eq_of_pos_iff {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) (h : 0 < x ↔ 0 < y) :
    itgSgn x = itgSgn y := by
  rcases hx.lt_or_gt with hx' | hx'
  · have : y < 0 := lt_of_le_of_ne (not_lt.1 fun h' => absurd (h.2 h') (not_lt.2 hx'.le)) hy
    rw [itgSgn_neg hx', itgSgn_neg this]
  · rw [itgSgn_pos hx', itgSgn_pos (h.1 hx')]

variable {g : ℝ → ℝ}

/-- No zero on `[a, b]`: `g` has the same sign at `a` and `b` (intermediate value theorem). -/
theorem two_goods_pos_iff {a b : ℝ} (hab : a ≤ b) (hc : ContinuousOn g (Set.Icc a b))
    (hne : ∀ t ∈ Set.Icc a b, g t ≠ 0) : (0 < g a ↔ 0 < g b) := by
  have ha := hne a ⟨le_rfl, hab⟩
  have hb := hne b ⟨hab, le_rfl⟩
  constructor
  · intro h
    by_contra h'
    have hb' : g b < 0 := lt_of_le_of_ne (not_lt.1 h') hb
    obtain ⟨t, ht, ht0⟩ := intermediate_value_Icc' hab hc ⟨hb'.le, h.le⟩
    exact hne t ht ht0
  · intro h
    by_contra h'
    have ha' : g a < 0 := lt_of_le_of_ne (not_lt.1 h') ha
    obtain ⟨t, ht, ht0⟩ := intermediate_value_Icc hab hc ⟨ha'.le, h.le⟩
    exact hne t ht ht0

/-- At a regular zero `g(t) = 0`, `g'(t) = d ≠ 0`, `g` changes sign: near `t`,
`g(s)(s - t) d > 0` (positive to the right iff `d > 0`, negative to the left iff `d > 0`). -/
theorem two_goods_local_sign {t d : ℝ} (hd : HasDerivAt g d t) (h0 : g t = 0) (hd0 : d ≠ 0) :
    ∃ δ > 0, ∀ s, s ≠ t → |s - t| < δ → 0 < g s * (s - t) * d := by
  have hsl := hasDerivAt_iff_tendsto_slope.1 hd
  have hev : ∀ᶠ s in 𝓝[≠] t, 0 < slope g t s * d :=
    (hsl.mul_const d).eventually (lt_mem_nhds (mul_self_pos.2 hd0))
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 hev)
  refine ⟨δ, hδ, fun s hs hdist => ?_⟩
  have h := hball (by rwa [Real.dist_eq]) hs
  have hst : s - t ≠ 0 := sub_ne_zero.2 hs
  rw [slope_def_field, h0, sub_zero] at h
  have : g s * (s - t) * d = g s / (s - t) * d * (s - t) ^ 2 := by field_simp
  rw [this]
  exact mul_pos h (lt_of_le_of_ne (sq_nonneg _) (pow_ne_zero 2 hst).symm)

variable {Z : Finset ℝ} {d : ℝ → ℝ}

/-- **The telescoping step behind Proposition 17.D.2 for `L = 2`.** Let `g` be continuous on
`(0, ∞)` with zero set `Z` (finite), each zero regular (`g'(t) = d(t) ≠ 0`). For `0 < a < b`
with `g(a), g(b) ≠ 0`: `2 ∑_{t ∈ Z ∩ (a,b)} (-sign d(t)) = sign g(a) - sign g(b)`. -/
theorem two_goods_telescope (hc : ContinuousOn g (Set.Ioi 0))
    (hZ : ∀ t, t ∈ Z ↔ 0 < t ∧ g t = 0) (hd : ∀ t ∈ Z, HasDerivAt g (d t) t)
    (hd0 : ∀ t ∈ Z, d t ≠ 0) {a : ℝ} (ha0 : 0 < a) (hga : g a ≠ 0) :
    ∀ m : ℕ, ∀ b, a < b → g b ≠ 0 → (Z.filter fun t => a < t ∧ t < b).card = m →
      2 * ∑ t ∈ Z.filter (fun t => a < t ∧ t < b), -itgSgn (d t) = itgSgn (g a) - itgSgn (g b) := by
  have hcIcc : ∀ x y, 0 < x → ContinuousOn g (Set.Icc x y) := fun x y hx =>
    hc.mono fun s hs => lt_of_lt_of_le hx hs.1
  -- no zero in `[x, y]` when none lies in `(x, y)` and `g(x), g(y) ≠ 0`
  have hnozero : ∀ x y, 0 < x → x ≤ y → g x ≠ 0 → g y ≠ 0 →
      (∀ t ∈ Z, ¬ (x < t ∧ t < y)) → ∀ t ∈ Set.Icc x y, g t ≠ 0 := by
    intro x y hx _ hgx hgy hZxy t ht hgt
    rcases ht.1.lt_or_eq with h1 | h1
    · rcases ht.2.lt_or_eq with h2 | h2
      · exact hZxy t ((hZ t).2 ⟨hx.trans h1, hgt⟩) ⟨h1, h2⟩
      · exact hgy (h2 ▸ hgt)
    · exact hgx (h1 ▸ hgt)
  intro m
  induction m with
  | zero =>
    intro b hab hgb hcard
    rw [Finset.card_eq_zero] at hcard
    rw [hcard, Finset.sum_empty, mul_zero, eq_comm, sub_eq_zero]
    refine itgSgn_eq_of_pos_iff hga hgb (two_goods_pos_iff hab.le (hcIcc a b ha0) ?_)
    refine hnozero a b ha0 hab.le hga hgb fun t ht hat => ?_
    have : t ∈ Z.filter (fun t => a < t ∧ t < b) := Finset.mem_filter.2 ⟨ht, hat⟩
    rw [hcard] at this
    simp at this
  | succ m ih =>
    intro b hab hgb hcard
    set S := Z.filter fun t => a < t ∧ t < b with hSdef
    have hne : S.Nonempty := by
      rw [← Finset.card_pos, hcard]; exact Nat.succ_pos m
    set t := S.max' hne
    have htS : t ∈ S := S.max'_mem hne
    obtain ⟨htZ, hat, htb⟩ := Finset.mem_filter.1 htS
    have hgt := ((hZ t).1 htZ).2
    obtain ⟨δ, hδ, hloc⟩ := two_goods_local_sign (hd t htZ) hgt (hd0 t htZ)
    -- the largest point of `{a} ∪ (S \ {t})`
    set u := (insert a (S.erase t)).max' (Finset.insert_nonempty _ _)
    have hu_lt : u < t := by
      refine ((insert a (S.erase t)).max'_lt_iff _).2 fun y hy => ?_
      rcases Finset.mem_insert.1 hy with rfl | hy
      · exact hat
      · exact lt_of_le_of_ne (S.le_max' y (Finset.mem_of_mem_erase hy))
          (Finset.ne_of_mem_erase hy)
    have hau : a ≤ u := (insert a (S.erase t)).le_max' a (Finset.mem_insert_self _ _)
    set c := (max u (t - δ) + t) / 2
    have hmax_lt : max u (t - δ) < t := max_lt hu_lt (by linarith)
    have hc_lt : c < t := by simp only [c]; linarith
    have hc_gt : max u (t - δ) < c := by simp only [c]; linarith
    have hac : a < c := lt_of_le_of_lt (hau.trans (le_max_left _ _)) hc_gt
    have hcδ : |c - t| < δ := by
      rw [abs_of_neg (by linarith)]
      linarith [le_max_right u (t - δ)]
    have hgc := hloc c hc_lt.ne hcδ
    set e := (t + min b (t + δ)) / 2
    have hmin : t < min b (t + δ) := lt_min htb (by linarith)
    have he_gt : t < e := by simp only [e]; linarith
    have he_lt : e < min b (t + δ) := by simp only [e]; linarith
    have heb : e < b := lt_of_lt_of_le he_lt (min_le_left _ _)
    have heδ : |e - t| < δ := by
      rw [abs_of_pos (by linarith)]
      linarith [min_le_right b (t + δ)]
    have hge := hloc e he_gt.ne' heδ
    have hgc0 : g c ≠ 0 := fun h => by rw [h] at hgc; simp at hgc
    have hge0 : g e ≠ 0 := fun h => by rw [h] at hge; simp at hge
    -- the zeros in `(a, c)` are those of `S` other than `t`
    have hSc : (Z.filter fun s => a < s ∧ s < c) = S.erase t := by
      ext s
      simp only [Finset.mem_filter, Finset.mem_erase, hSdef]
      constructor
      · rintro ⟨hs, has, hsc⟩
        exact ⟨(hsc.trans hc_lt).ne, hs, has, hsc.trans (hc_lt.trans htb)⟩
      · rintro ⟨hst, hs, has, hsb⟩
        have : s ∈ S.erase t := Finset.mem_erase.2 ⟨hst, Finset.mem_filter.2 ⟨hs, has, hsb⟩⟩
        have hsu : s ≤ u := (insert a (S.erase t)).le_max' s (Finset.mem_insert_of_mem this)
        exact ⟨hs, has, lt_of_le_of_lt (hsu.trans (le_max_left _ _)) hc_gt⟩
    have hcard' : (Z.filter fun s => a < s ∧ s < c).card = m := by
      rw [hSc, Finset.card_erase_of_mem htS, hcard]; rfl
    have hIH := ih c hac hgc0 hcard'
    rw [hSc] at hIH
    -- no zero in `[e, b]`
    have hsame : itgSgn (g e) = itgSgn (g b) := by
      refine itgSgn_eq_of_pos_iff hge0 hgb (two_goods_pos_iff heb.le
        (hcIcc e b (by linarith)) (hnozero e b (by linarith) heb.le hge0 hgb fun s hs hes => ?_))
      have : s ∈ S := Finset.mem_filter.2 ⟨hs, by linarith, hes.2⟩
      have := S.le_max' s this
      linarith [hes.1]
    -- signs at `c` and `e`
    have hdt := hd0 t htZ
    have hsc : itgSgn (g c) = -itgSgn (d t) := by
      rcases hdt.lt_or_gt with hneg | hpos
      · have : 0 < g c := by
          by_contra h'
          have h'' : g c < 0 := lt_of_le_of_ne (not_lt.1 h') hgc0
          nlinarith [mul_pos_of_neg_of_neg h'' (by linarith : c - t < 0)]
        rw [itgSgn_pos this, itgSgn_neg hneg]; rfl
      · have : g c < 0 := by
          by_contra h'
          have h'' : 0 < g c := lt_of_le_of_ne (not_lt.1 h') hgc0.symm
          nlinarith [mul_neg_of_pos_of_neg h'' (by linarith : c - t < 0)]
        rw [itgSgn_neg this, itgSgn_pos hpos]
    have hse : itgSgn (g e) = itgSgn (d t) := by
      rcases hdt.lt_or_gt with hneg | hpos
      · have : g e < 0 := by
          by_contra h'
          have h'' : 0 < g e := lt_of_le_of_ne (not_lt.1 h') hge0.symm
          nlinarith [mul_pos h'' (by linarith : 0 < e - t)]
        rw [itgSgn_neg this, itgSgn_neg hneg]
      · have : 0 < g e := by
          by_contra h'
          have h'' : g e < 0 := lt_of_le_of_ne (not_lt.1 h') hge0
          nlinarith [mul_neg_of_neg_of_pos h'' (by linarith : 0 < e - t)]
        rw [itgSgn_pos this, itgSgn_pos hpos]
    rw [← Finset.add_sum_erase S _ htS, mul_add, hIH, ← hsame, hse, hsc]
    ring

/-- To the right of a zero, `g(s)(s - t)d > 0` gives `g(s) > 0 ↔ d > 0`. -/
theorem two_goods_sign_right {gs st dd : ℝ} (h : 0 < gs * st * dd) (hst : 0 < st) :
    (0 < gs ↔ 0 < dd) := by
  constructor
  · intro hg
    by_contra hd
    nlinarith [mul_pos hg hst, not_lt.1 hd]
  · intro hd
    by_contra hg
    nlinarith [mul_pos hd hst, not_lt.1 hg]

/-- To the left of a zero, `g(s)(s - t)d > 0` gives `g(s) > 0 ↔ d < 0`. -/
theorem two_goods_sign_left {gs st dd : ℝ} (h : 0 < gs * st * dd) (hst : st < 0) :
    (0 < gs ↔ dd < 0) := by
  constructor
  · intro hg
    by_contra hd
    nlinarith [mul_neg_of_pos_of_neg hg hst, not_lt.1 hd]
  · intro hd
    by_contra hg
    nlinarith [mul_pos_of_neg_of_neg hd hst, not_lt.1 hg]

/-- If the sum of `±1` values over a finite set is `1`, the set has an odd number of elements. -/
theorem odd_card_of_sum_eq_one {α : Type*} (S : Finset α) (f : α → ℤ)
    (hf : ∀ x ∈ S, f x = 1 ∨ f x = -1) (hsum : ∑ x ∈ S, f x = 1) : Odd S.card := by
  classical
  have key : ∀ T ⊆ S, ∃ k : ℤ, ∑ x ∈ T, f x = T.card - 2 * k := by
    intro T
    induction T using Finset.induction_on with
    | empty => intro _; exact ⟨0, by simp⟩
    | insert y T hy ih =>
      intro hT
      obtain ⟨k, hk⟩ := ih ((Finset.subset_insert y T).trans hT)
      rw [Finset.sum_insert hy, Finset.card_insert_of_notMem hy, hk]
      rcases hf y (hT (Finset.mem_insert_self y T)) with h | h
      · exact ⟨k, by rw [h]; push_cast; ring⟩
      · exact ⟨k + 1, by rw [h]; push_cast; ring⟩
  obtain ⟨k, hk⟩ := key S le_rfl
  rw [hsum] at hk
  refine ⟨(k.toNat), ?_⟩
  have hk0 : 0 ≤ k := by
    by_contra h
    have : (S.card : ℤ) = 1 + 2 * k := by linarith
    have : (0 : ℤ) ≤ S.card := Nat.cast_nonneg _
    omega
  have : (S.card : ℤ) = 2 * (k.toNat : ℤ) + 1 := by rw [Int.toNat_of_nonneg hk0]; linarith
  exact_mod_cast this

/-! ### The economy with two goods -/

/-- The normalized price `p̂ = p₁` as a vector of `ℝ¹`. -/
def vec1 (t : ℝ) : Fin 1 → ℝ := fun _ => t

theorem normPrice_vec1 (t : ℝ) : normPrice (vec1 t) = ![t, 1] := by
  funext k
  fin_cases k
  · rfl
  · rfl

theorem vec1_apply_zero (q : Fin 1 → ℝ) : vec1 (q 0) = q :=
  funext fun i => by rw [Subsingleton.elim i 0]; rfl

/-- The slope `∂z₁(p₁, 1)/∂p₁` at `p₁ = t`, read off `Dẑ`. -/
noncomputable def slope2 (z : (Fin 2 → ℝ) → Fin 2 → ℝ) (t : ℝ) : ℝ :=
  fderiv ℝ (normED z) (vec1 t) (vec1 1) 0

variable {z : (Fin 2 → ℝ) → Fin 2 → ℝ}

/-- If `ẑ` is differentiable at `p̂ = (t)`, then `t ↦ z₁(t, 1)` has derivative `slope2 z t`. -/
theorem two_goods_hasDerivAt {t : ℝ} (hdiff : DifferentiableAt ℝ (normED z) (vec1 t)) :
    HasDerivAt (fun s => z ![s, 1] 0) (slope2 z t) t := by
  have he : HasDerivAt vec1 (vec1 1) t := hasDerivAt_pi.2 fun _ => hasDerivAt_id t
  have h := hasDerivAt_pi.1 (hdiff.hasFDerivAt.comp_hasDerivAt t he) 0
  unfold slope2
  convert h using 1
  funext s
  simp [normED, truncExcessDemand, normPrice_vec1]

/-- With two goods, `|Dẑ(p̂)|` is the slope of `z₁(·, 1)` (MWG p. 592). -/
theorem det_eq_slope2 (t : ℝ) : (fderiv ℝ (normED z) (vec1 t)).det = slope2 z t := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix', Matrix.det_fin_one,
    LinearMap.toMatrix'_apply, slope2]
  have : (Pi.single 0 1 : Fin 1 → ℝ) = vec1 1 := funext fun i => by
    rw [Subsingleton.elim i 0]; rfl
  rw [this]
  rfl

/-- **Definition 17.D.2** with `L = 2` (MWG p. 592): the index is `+1` or `-1` according to
whether the slope of `z₁(·, 1)` is negative or positive. -/
theorem eqmIndex_two (q : Fin 1 → ℝ) : eqmIndex z q = -itgSgn (slope2 z (q 0)) := by
  rw [eqmIndex, ← vec1_apply_zero q, det_eq_slope2, vec1_apply_zero q, pow_one, neg_one_mul]
  rfl

/-- With two goods, `(p₁, 1) ≫ 0` is an equilibrium iff `z₁(p₁, 1) = 0` (Walras' law). -/
theorem isNormEqm_vec1_iff (hW : EDWalrasLaw z) {t : ℝ} :
    IsNormEqm z (vec1 t) ↔ 0 < t ∧ z ![t, 1] 0 = 0 := by
  constructor
  · rintro ⟨hp, hz⟩
    rw [normPrice_vec1] at hp hz
    exact ⟨by simpa using hp 0, by rw [hz]; rfl⟩
  · rintro ⟨ht, hz0⟩
    have hp := vec2_mem_posOrthant ht one_pos
    have hw := walras_two hW ht one_pos
    rw [hz0, mul_zero, zero_add, one_mul] at hw
    refine ⟨by rw [normPrice_vec1]; exact hp, ?_⟩
    rw [normPrice_vec1]
    funext l
    fin_cases l
    · exact hz0
    · exact hw

/-- Prices bracketing finitely many positive numbers: `0 < a < t < b` for all `t ∈ Z`, with
`z₁(a, 1) > 0` and `z₁(b, 1) < 0` (footnote 8). -/
theorem two_goods_bracket (hz : IsStandardExcessDemand z) (Z : Finset ℝ)
    (hZ : ∀ t ∈ Z, 0 < t) :
    ∃ a b, 0 < a ∧ a < b ∧ 0 < z ![a, 1] 0 ∧ z ![b, 1] 0 < 0 ∧ ∀ t ∈ Z, a < t ∧ t < b := by
  set m := (insert 1 Z).min' (Finset.insert_nonempty _ _)
  set M := (insert 1 Z).max' (Finset.insert_nonempty _ _)
  have hm : 0 < m := by
    rw [Finset.lt_min'_iff]
    intro y hy
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact one_pos
    · exact hZ y hy
  have hlow := footnote_17_8_low hz (as := fun k : ℕ => 1 / ((k : ℝ) + 1))
    (fun k => by positivity) tendsto_one_div_add_atTop_nhds_zero_nat
  have hhigh := footnote_17_8_high hz (bs := fun k : ℕ => (k : ℝ) + 1) (fun k => by positivity)
    (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have hsmall : ∀ᶠ k : ℕ in atTop, 1 / ((k : ℝ) + 1) < m :=
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually (gt_mem_nhds hm)
  have hlarge : ∀ᶠ k : ℕ in atTop, M < (k : ℝ) + 1 :=
    (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop).eventually_gt_atTop M
  obtain ⟨k, h1, h2, h3, h4⟩ := (hlow.and (hhigh.and (hsmall.and hlarge))).exists
  refine ⟨1 / ((k : ℝ) + 1), (k : ℝ) + 1, by positivity, ?_, h1, h2, fun t ht => ?_⟩
  · have : m ≤ 1 := (insert 1 Z).min'_le 1 (Finset.mem_insert_self _ _)
    have : 1 ≤ M := (insert 1 Z).le_max' 1 (Finset.mem_insert_self _ _)
    linarith
  · exact ⟨lt_of_lt_of_le h3 ((insert 1 Z).min'_le t (Finset.mem_insert_of_mem ht)),
      lt_of_le_of_lt ((insert 1 Z).le_max' t (Finset.mem_insert_of_mem ht)) h4⟩

/-- The data of a regular two-good economy for the one-variable argument: `g(t) = z₁(t, 1)`. -/
theorem two_goods_data (hz : IsStandardExcessDemand z) (hreg : IsRegularEconomy z)
    (hfin : {q : Fin 1 → ℝ | IsNormEqm z q}.Finite) :
    ContinuousOn (fun t => z ![t, 1] 0) (Set.Ioi 0) ∧
      (∀ t, t ∈ hfin.toFinset.image (fun q => q 0) ↔ 0 < t ∧ z ![t, 1] 0 = 0) ∧
      (∀ t ∈ hfin.toFinset.image (fun q => q 0),
        HasDerivAt (fun s => z ![s, 1] 0) (slope2 z t) t ∧ slope2 z t ≠ 0) := by
  have hvec : Continuous fun t : ℝ => (![t, 1] : Fin 2 → ℝ) := by
    refine continuous_pi fun l => ?_
    fin_cases l
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      exact continuous_id'
    · simpa using continuous_const
  refine ⟨?_, fun t => ?_, fun t ht => ?_⟩
  · exact (continuous_apply 0).comp_continuousOn (hz.continuous.comp hvec.continuousOn
      fun t ht => vec2_mem_posOrthant ht one_pos)
  · rw [Finset.mem_image]
    constructor
    · rintro ⟨q, hq, rfl⟩
      rw [Set.Finite.mem_toFinset] at hq
      have hq' : IsNormEqm z (vec1 (q 0)) := by rw [vec1_apply_zero]; exact hq
      exact (isNormEqm_vec1_iff hz.walras).1 hq'
    · intro h
      exact ⟨vec1 t, by
        rw [Set.Finite.mem_toFinset]; exact (isNormEqm_vec1_iff hz.walras).2 h, rfl⟩
  · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 ht
    rw [Set.Finite.mem_toFinset] at hq
    obtain ⟨-, hdiff, hdet⟩ := hreg q hq
    rw [← vec1_apply_zero q] at hdiff hdet
    exact ⟨two_goods_hasDerivAt hdiff, by rwa [det_eq_slope2] at hdet⟩

/-- **Proposition 17.D.2 (the index theorem) for `L = 2`** (MWG, p. 593). If `z` satisfies
(i)-(v) of Proposition 17.B.2 with two goods and the economy is regular, the set of normalized
equilibria is finite and the indices sum to `+1`. -/
theorem proposition_17_D_2_two_goods (hz : IsStandardExcessDemand z)
    (hreg : IsRegularEconomy z) :
    ∃ hfin : {q : Fin 1 → ℝ | IsNormEqm z q}.Finite, ∑ q ∈ hfin.toFinset, eqmIndex z q = 1 := by
  have hfin := proposition_17_D_1_finite hz hreg
  refine ⟨hfin, ?_⟩
  obtain ⟨hc, hZ, hd⟩ := two_goods_data hz hreg hfin
  set Z := hfin.toFinset.image (fun q => q 0)
  obtain ⟨a, b, ha0, hab, hga, hgb, hZab⟩ := two_goods_bracket hz Z fun t ht => ((hZ t).1 ht).1
  have hinj : Set.InjOn (fun q : Fin 1 → ℝ => q 0) hfin.toFinset := fun q _ q' _ h => by
    rw [← vec1_apply_zero q, ← vec1_apply_zero q']
    exact congrArg vec1 h
  have hsum : ∑ q ∈ hfin.toFinset, eqmIndex z q = ∑ t ∈ Z, -itgSgn (slope2 z t) := by
    rw [Finset.sum_image hinj]
    exact Finset.sum_congr rfl fun q _ => eqmIndex_two q
  have hfilter : (Z.filter fun t => a < t ∧ t < b) = Z :=
    Finset.filter_true_of_mem fun t ht => hZab t ht
  have htel := two_goods_telescope hc hZ (fun t ht => (hd t ht).1) (fun t ht => (hd t ht).2)
    ha0 hga.ne' _ b hab hgb.ne rfl
  rw [hfilter, itgSgn_pos hga, itgSgn_neg hgb] at htel
  rw [hsum]
  linarith

/-- **Section 17.D** (MWG, p. 593). With two goods, a regular economy has an odd number of
normalized equilibria (in particular at least one; Dierker, footnote 16). -/
theorem two_goods_card_odd (hz : IsStandardExcessDemand z) (hreg : IsRegularEconomy z) :
    Odd {q : Fin 1 → ℝ | IsNormEqm z q}.ncard := by
  obtain ⟨hfin, hsum⟩ := proposition_17_D_2_two_goods hz hreg
  rw [Set.ncard_eq_toFinset_card _ hfin]
  refine odd_card_of_sum_eq_one _ _ (fun q hq => ?_) hsum
  rw [Set.Finite.mem_toFinset] at hq
  exact eqmIndex_eq_one_or (hreg q hq)

/-- **Section 17.D** (MWG, p. 592): with two goods the slope of excess demand at the smallest
equilibrium price `p₁` is negative (index `+1`): excess demand is positive for `p₁` very low. -/
theorem two_goods_first_slope_neg (hz : IsStandardExcessDemand z) (hreg : IsRegularEconomy z)
    {t : ℝ} (ht : IsNormEqm z (vec1 t)) (hmin : ∀ t', IsNormEqm z (vec1 t') → t ≤ t') :
    slope2 z t < 0 := by
  have hfin := proposition_17_D_1_finite hz hreg
  obtain ⟨hc, hZ, hd⟩ := two_goods_data hz hreg hfin
  set Z := hfin.toFinset.image (fun q => q 0)
  obtain ⟨a, b, ha0, -, hga, -, hZab⟩ := two_goods_bracket hz Z fun s hs => ((hZ s).1 hs).1
  have htZ : t ∈ Z := (hZ t).2 ((isNormEqm_vec1_iff hz.walras).1 ht)
  obtain ⟨hder, hd0⟩ := hd t htZ
  obtain ⟨δ, hδ, hloc⟩ := two_goods_local_sign hder ((hZ t).1 htZ).2 hd0
  have hat := (hZab t htZ).1
  set s := (max a (t - δ) + t) / 2
  have hmx : max a (t - δ) < t := max_lt hat (by linarith)
  have hs_lt : s < t := by simp only [s]; linarith
  have hs_gt : max a (t - δ) < s := by simp only [s]; linarith
  have has : a < s := lt_of_le_of_lt (le_max_left _ _) hs_gt
  have hsδ : |s - t| < δ := by
    rw [abs_of_neg (by linarith)]; linarith [le_max_right a (t - δ)]
  have hgs := hloc s hs_lt.ne hsδ
  have hgs0 : z ![s, 1] 0 ≠ 0 := fun h => by rw [h] at hgs; simp at hgs
  have hpos : 0 < z ![s, 1] 0 := by
    refine (two_goods_pos_iff has.le (hc.mono fun x hx => lt_of_lt_of_le ha0 hx.1)
      fun x hx hx0 => ?_).1 hga
    have hx0' : 0 < x := lt_of_lt_of_le ha0 hx.1
    have := hmin x ((isNormEqm_vec1_iff hz.walras).2 ⟨hx0', hx0⟩)
    linarith [hx.2]
  exact (two_goods_sign_left hgs (by linarith)).1 hpos

/-- **Section 17.D** (MWG, p. 592): with two goods the slope at the largest equilibrium price is
negative: excess demand is negative for `p₁` very high. -/
theorem two_goods_last_slope_neg (hz : IsStandardExcessDemand z) (hreg : IsRegularEconomy z)
    {t : ℝ} (ht : IsNormEqm z (vec1 t)) (hmax : ∀ t', IsNormEqm z (vec1 t') → t' ≤ t) :
    slope2 z t < 0 := by
  have hfin := proposition_17_D_1_finite hz hreg
  obtain ⟨hc, hZ, hd⟩ := two_goods_data hz hreg hfin
  set Z := hfin.toFinset.image (fun q => q 0)
  obtain ⟨a, b, -, -, -, hgb, hZab⟩ := two_goods_bracket hz Z fun s hs => ((hZ s).1 hs).1
  have htZ : t ∈ Z := (hZ t).2 ((isNormEqm_vec1_iff hz.walras).1 ht)
  obtain ⟨hder, hd0⟩ := hd t htZ
  obtain ⟨δ, hδ, hloc⟩ := two_goods_local_sign hder ((hZ t).1 htZ).2 hd0
  have htb := (hZab t htZ).2
  have ht0 := ((hZ t).1 htZ).1
  set s := (t + min b (t + δ)) / 2
  have hmn : t < min b (t + δ) := lt_min htb (by linarith)
  have hs_gt : t < s := by simp only [s]; linarith
  have hs_lt : s < min b (t + δ) := by simp only [s]; linarith
  have hsb : s < b := lt_of_lt_of_le hs_lt (min_le_left _ _)
  have hsδ : |s - t| < δ := by
    rw [abs_of_pos (by linarith)]; linarith [min_le_right b (t + δ)]
  have hgs := hloc s hs_gt.ne' hsδ
  have hgs0 : z ![s, 1] 0 ≠ 0 := fun h => by rw [h] at hgs; simp at hgs
  have hneg : ¬ 0 < z ![s, 1] 0 := by
    intro hpos
    have := (two_goods_pos_iff hsb.le (hc.mono fun x hx => lt_trans ht0 (lt_of_lt_of_le hs_gt hx.1))
      fun x hx hx0 => ?_).1 hpos
    · linarith
    have hx0' : 0 < x := lt_trans ht0 (lt_of_lt_of_le hs_gt hx.1)
    have := hmax x ((isNormEqm_vec1_iff hz.walras).2 ⟨hx0', hx0⟩)
    linarith [hx.1]
  by_contra hd'
  exact hneg ((two_goods_sign_right hgs (by linarith)).2
    (lt_of_le_of_ne (not_lt.1 hd') hd0.symm))

/-- **Section 17.D** (MWG, p. 592): with two goods the slopes at consecutive equilibria have
opposite signs (the indices alternate). -/
theorem two_goods_slopes_alternate (hz : IsStandardExcessDemand z) (hreg : IsRegularEconomy z)
    {t t' : ℝ} (ht : IsNormEqm z (vec1 t)) (ht' : IsNormEqm z (vec1 t')) (htt : t < t')
    (hbetween : ∀ s, t < s → s < t' → ¬ IsNormEqm z (vec1 s)) :
    (0 < slope2 z t ↔ slope2 z t' < 0) := by
  have hfin := proposition_17_D_1_finite hz hreg
  obtain ⟨hc, hZ, hd⟩ := two_goods_data hz hreg hfin
  set Z := hfin.toFinset.image (fun q => q 0)
  have htZ : t ∈ Z := (hZ t).2 ((isNormEqm_vec1_iff hz.walras).1 ht)
  have htZ' : t' ∈ Z := (hZ t').2 ((isNormEqm_vec1_iff hz.walras).1 ht')
  obtain ⟨hder, hd0⟩ := hd t htZ
  obtain ⟨hder', hd0'⟩ := hd t' htZ'
  obtain ⟨δ, hδ, hloc⟩ := two_goods_local_sign hder ((hZ t).1 htZ).2 hd0
  obtain ⟨δ', hδ', hloc'⟩ := two_goods_local_sign hder' ((hZ t').1 htZ').2 hd0'
  have ht0 := ((hZ t).1 htZ).1
  set c := t + min ((t' - t) / 3) (δ / 2)
  set e := t' - min ((t' - t) / 3) (δ' / 2)
  have h1 : 0 < min ((t' - t) / 3) (δ / 2) := lt_min (by linarith) (by linarith)
  have h2 : 0 < min ((t' - t) / 3) (δ' / 2) := lt_min (by linarith) (by linarith)
  have h3 := min_le_left ((t' - t) / 3) (δ / 2)
  have h4 := min_le_left ((t' - t) / 3) (δ' / 2)
  have h5 := min_le_right ((t' - t) / 3) (δ / 2)
  have h6 := min_le_right ((t' - t) / 3) (δ' / 2)
  have hce : c < e := by simp only [c, e]; linarith
  have hgc := hloc c (by simp only [c]; linarith) (by
    rw [abs_of_pos (by simp only [c]; linarith)]; simp only [c]; linarith)
  have hge := hloc' e (by simp only [e]; linarith) (by
    rw [abs_of_neg (by simp only [e]; linarith)]; simp only [e]; linarith)
  have hgc0 : z ![c, 1] 0 ≠ 0 := fun h => by rw [h] at hgc; simp at hgc
  have hge0 : z ![e, 1] 0 ≠ 0 := fun h => by rw [h] at hge; simp at hge
  have hc0 : 0 < c := by simp only [c]; linarith
  have hsame := two_goods_pos_iff hce.le (hc.mono fun x hx => lt_of_lt_of_le hc0 hx.1)
    fun x hx hx0 => hbetween x (by simp only [c] at hx; linarith [hx.1])
      (by simp only [e] at hx; linarith [hx.2])
      ((isNormEqm_vec1_iff hz.walras).2 ⟨lt_of_lt_of_le hc0 hx.1, hx0⟩)
  rw [← two_goods_sign_right hgc (by simp only [c]; linarith), hsame]
  exact two_goods_sign_left hge (by simp only [e]; linarith)

end MWG.PositiveEquilibriumTheory
