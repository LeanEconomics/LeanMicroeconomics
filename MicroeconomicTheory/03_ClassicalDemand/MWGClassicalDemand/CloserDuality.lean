/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGClassicalDemand.DualitySupport
import Mathlib.Topology.Order.Compact

/-!
# One-sided derivatives of the support function (small type, pp. 66-67, Figure 3.F.5)

MWG, Section 3.F, small type on pp. 66-67: when the minimizing set at `p̄` is not a singleton,
the support function `μ_K` has a kink at `p̄`, but "the range of these directional derivatives
at `p̄` is equal to the range of `x_l` in the minimizing vectors at that point".

For a nonempty compact `K ⊆ ℝ^L` (Danskin's theorem):

* the right derivative of `t ↦ μ_K(p̄ + t d)` at `0` is `min {d·x : x ∈ argmin}`
  (`closerDuality_right_derivative`);
* the left derivative is `max {d·x : x ∈ argmin}` (`closerDuality_left_derivative`);
* so with `d = e_l` the one-sided partial derivatives are the least and the largest `x_l` over
  the minimizing set, and they agree iff `x_l` is constant on it (`proposition_3_F_small_type`).

The book's `K` is closed (Figure 3.F.5 draws an unbounded `K`); the theorem is proved for
compact `K` (correction E5).
-/

namespace MWG.ClassicalDemand

open Filter Topology

variable {L : ℕ}

/-- For compact nonempty `K` every price vector has a minimizer. -/
theorem closerDuality_argmin_nonempty {K : Set (Fin L → ℝ)} (hK : IsCompact K)
    (hne : K.Nonempty) (q : Fin L → ℝ) : (supportArgmin K q).Nonempty := by
  obtain ⟨x, hx, hmin⟩ := hK.exists_isMinOn hne
    (Continuous.continuousOn (f := fun x => q ⬝ᵥ x) (by fun_prop))
  exact ⟨x, hx, fun y hy => hmin hy⟩

/-- **Section 3.F, small type** (MWG, pp. 66-67), right derivative (Danskin). For nonempty
compact `K`, `p̄` and a direction `d`, some `x* ∈ argmin_K p̄` minimizes `d·x` over the
minimizing set, and `(μ_K(p̄ + t d) - μ_K(p̄))/t → d·x*` as `t → 0⁺`. -/
theorem closerDuality_right_derivative {K : Set (Fin L → ℝ)} (hK : IsCompact K)
    (hne : K.Nonempty) (p d : Fin L → ℝ) :
    ∃ xs ∈ supportArgmin K p, (∀ x ∈ supportArgmin K p, d ⬝ᵥ xs ≤ d ⬝ᵥ x) ∧
      Tendsto (fun t => (supportFn K (p + t • d) - supportFn K p) / t) (𝓝[>] 0)
        (𝓝 (d ⬝ᵥ xs)) := by
  have hdot : ∀ q : Fin L → ℝ, Continuous fun x : Fin L → ℝ => q ⬝ᵥ x := fun q => by fun_prop
  have hbdd : ∀ q : Fin L → ℝ, BddBelow ((fun x => q ⬝ᵥ x) '' K) := fun q =>
    (hK.image (hdot q)).bddBelow
  obtain ⟨x0, hx0⟩ := closerDuality_argmin_nonempty hK hne p
  set A := supportArgmin K p with hA
  have hAc : IsCompact A := by
    have : A = K ∩ {x | p ⬝ᵥ x ≤ p ⬝ᵥ x0} := by
      ext x
      constructor
      · rintro ⟨hx, hmin⟩
        exact ⟨hx, hmin x0 hx0.1⟩
      · rintro ⟨hx, hle⟩
        exact ⟨hx, fun y hy => hle.trans (hx0.2 y hy)⟩
    rw [this]
    exact hK.inter_right (isClosed_le (hdot p) continuous_const)
  obtain ⟨xs, hxs, hxsmin⟩ := hAc.exists_isMinOn ⟨x0, hx0⟩ (hdot d).continuousOn
  refine ⟨xs, hxs, fun x hx => hxsmin hx, ?_⟩
  set m := d ⬝ᵥ xs with hm
  have hμp : supportFn K p = p ⬝ᵥ xs := supportFn_eq_of_mem_argmin hxs
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hdot d).continuousOn
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC xs hxs.1)
  have hdC : ∀ x ∈ K, |d ⬝ᵥ x| ≤ C := fun x hx => by simpa [Real.norm_eq_abs] using hC x hx
  -- the upper bound
  have hupper : ∀ t : ℝ, 0 < t → (supportFn K (p + t • d) - supportFn K p) / t ≤ m := by
    intro t ht
    have h1 := supportFn_le (hbdd (p + t • d)) hxs.1
    rw [add_dotProduct, smul_dotProduct, smul_eq_mul] at h1
    rw [div_le_iff₀ ht]
    linarith
  -- the lower bound, uniformly near `0`
  have hlower : ∀ ε : ℝ, 0 < ε → ∀ᶠ t in 𝓝[>] (0 : ℝ),
      m - ε < (supportFn K (p + t • d) - supportFn K p) / t := by
    intro ε hε
    -- every minimizer at `p + t d` has `d·x > m - ε` for small `t`
    have hkey : ∃ η : ℝ, 0 < η ∧ ∀ t : ℝ, 0 < t → t < η →
        ∀ x ∈ supportArgmin K (p + t • d), m - ε < d ⬝ᵥ x := by
      set K' := K ∩ {x | d ⬝ᵥ x ≤ m - ε} with hK'
      rcases K'.eq_empty_or_nonempty with hK'e | hK'ne
      · refine ⟨1, one_pos, fun t _ _ x hx => ?_⟩
        by_contra hle
        push Not at hle
        have : x ∈ K' := ⟨hx.1, hle⟩
        rw [hK'e] at this
        exact this
      · have hK'c : IsCompact K' := hK.inter_right (isClosed_le (hdot d) continuous_const)
        obtain ⟨y, hy, hymin⟩ := hK'c.exists_isMinOn hK'ne (hdot p).continuousOn
        set δ := p ⬝ᵥ y - supportFn K p with hδ
        have hδ0 : 0 < δ := by
          rcases (sub_nonneg.2 (supportFn_le (hbdd p) hy.1)).lt_or_eq with h | h
          · exact h
          · exfalso
            have hpy : p ⬝ᵥ y = supportFn K p := by linarith
            have hyA : y ∈ A := ⟨hy.1, fun z hz => by
              rw [hpy]
              exact supportFn_le (hbdd p) hz⟩
            have := isMinOn_iff.1 hxsmin y hyA
            have h2 : d ⬝ᵥ y ≤ m - ε := hy.2
            linarith
        refine ⟨δ / (2 * C + 1), by positivity, fun t ht htη x hx => ?_⟩
        by_contra hle
        push Not at hle
        have hxK' : x ∈ K' := ⟨hx.1, hle⟩
        have h1 : p ⬝ᵥ y ≤ p ⬝ᵥ x := hymin hxK'
        have h2 : (p + t • d) ⬝ᵥ x ≤ (p + t • d) ⬝ᵥ xs := hx.2 xs hxs.1
        rw [add_dotProduct, add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul,
          smul_eq_mul] at h2
        have h3 := (abs_le.1 (hdC x hx.1)).1
        have h4 := (abs_le.1 (hdC xs hxs.1)).2
        have htC : t * (2 * C + 1) < δ := by
          rwa [lt_div_iff₀ (by positivity)] at htη
        nlinarith [mul_le_mul_of_nonneg_left h4 ht.le, mul_le_mul_of_nonneg_left h3 ht.le]
    obtain ⟨η, hη, hη'⟩ := hkey
    filter_upwards [Ioo_mem_nhdsGT hη] with t ht
    obtain ⟨x, hx⟩ := closerDuality_argmin_nonempty hK hne (p + t • d)
    have h1 := hη' t ht.1 ht.2 x hx
    have h2 : supportFn K (p + t • d) = (p + t • d) ⬝ᵥ x := supportFn_eq_of_mem_argmin hx
    have h3 : supportFn K p ≤ p ⬝ᵥ x := supportFn_le (hbdd p) hx.1
    rw [lt_div_iff₀ ht.1, h2, add_dotProduct, smul_dotProduct, smul_eq_mul]
    nlinarith [mul_lt_mul_of_pos_right h1 ht.1]
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · filter_upwards [hlower (m - a) (by linarith)] with t ht
    linarith
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact lt_of_le_of_lt (hupper t ht) ha

/-- **Section 3.F, small type** (MWG, pp. 66-67), left derivative. For nonempty compact `K`,
some `x* ∈ argmin_K p̄` maximizes `d·x` over the minimizing set, and
`(μ_K(p̄ - t d) - μ_K(p̄))/(-t) → d·x*` as `t → 0⁺`. -/
theorem closerDuality_left_derivative {K : Set (Fin L → ℝ)} (hK : IsCompact K)
    (hne : K.Nonempty) (p d : Fin L → ℝ) :
    ∃ xs ∈ supportArgmin K p, (∀ x ∈ supportArgmin K p, d ⬝ᵥ x ≤ d ⬝ᵥ xs) ∧
      Tendsto (fun t => (supportFn K (p - t • d) - supportFn K p) / (-t)) (𝓝[>] 0)
        (𝓝 (d ⬝ᵥ xs)) := by
  obtain ⟨xs, hxs, hmin, hlim⟩ := closerDuality_right_derivative hK hne p (-d)
  refine ⟨xs, hxs, fun x hx => ?_, ?_⟩
  · have := hmin x hx
    simp only [neg_dotProduct] at this
    linarith
  · have := hlim.neg
    simp only [neg_dotProduct, neg_neg] at this
    refine this.congr fun t => ?_
    rw [smul_neg, ← sub_eq_add_neg, div_neg]

/-- **Section 3.F, small type** (MWG, pp. 66-67). For nonempty compact `K` and a good `l`, the
right and left partial derivatives of `μ_K` with respect to `p_l` at `p̄` are the least and the
largest `x_l` over the minimizing set; in particular `μ_K` has equal one-sided partial
derivatives iff `x_l` takes a single value on the minimizing set. -/
theorem proposition_3_F_small_type {K : Set (Fin L → ℝ)} (hK : IsCompact K)
    (hne : K.Nonempty) (p : Fin L → ℝ) (l : Fin L) :
    ∃ xlo ∈ supportArgmin K p, ∃ xhi ∈ supportArgmin K p,
      (∀ x ∈ supportArgmin K p, xlo l ≤ x l ∧ x l ≤ xhi l) ∧
      Tendsto (fun t => (supportFn K (p + t • Pi.single l 1) - supportFn K p) / t) (𝓝[>] 0)
        (𝓝 (xlo l)) ∧
      Tendsto (fun t => (supportFn K (p - t • Pi.single l 1) - supportFn K p) / (-t)) (𝓝[>] 0)
        (𝓝 (xhi l)) := by
  obtain ⟨xlo, hlo, hlomin, hlolim⟩ := closerDuality_right_derivative hK hne p (Pi.single l 1)
  obtain ⟨xhi, hhi, hhimax, hhilim⟩ := closerDuality_left_derivative hK hne p (Pi.single l 1)
  simp only [single_dotProduct, one_mul] at hlomin hlolim hhimax hhilim
  exact ⟨xlo, hlo, xhi, hhi, fun x hx => ⟨hlomin x hx, hhimax x hx⟩, hlolim, hhilim⟩

end MWG.ClassicalDemand
