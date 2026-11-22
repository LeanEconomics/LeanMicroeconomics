/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGClassicalDemand.RelationsExercises
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Data.Rat.Cast.Order

/-!
# Additively separable utility: Exercise 3.G.4(a) "only linear", (c), (d)

MWG, Exercise 3.G.4, p. 99, for `u(x) = ∑_l u_l(x_l)`.

* **(a)** Additive separability is preserved only by affine transformations: if `f` is
  increasing and `f(x₁ + x₂) = v₁(x₁) + v₂(x₂)` for all `x₁, x₂ ≥ 0` (so `f` preserves the
  additive separability of `x₁ + x₂` on `ℝ²_+`), then `f(s) = c s + d` on `[0, ∞)`
  (`exercise_3_G_4a_only_affine`). The proof reduces to Cauchy's equation on `[0, ∞)` for a
  monotone function.
* **(c)** With interior solutions characterized by the first-order conditions
  `u_l'(x_l) = λ p_l` and each `u_l'` strictly decreasing (strict concavity), an increase in
  wealth raises the demand for every good: no good is inferior (`exercise_3_G_4c`).
* **(d)** With identical `u_l = û`, `û' > 0` and `-t û''(t)/û'(t) < 1`, a rise in the price of
  good `k` (other prices fixed) strictly raises the demand for every other good: the gross
  substitute property (`exercise_3_G_4d`). Both (c) and (d) are proved as comparisons of two
  interior solutions (finite changes), which give the signs of the derivatives.
-/

namespace MWG.ClassicalDemand

open MWG.ConsumerChoice Filter Topology

/-- A monotone function additive on `[0, ∞)` is linear there: `φ(s) = s φ(1)`. -/
theorem closer_additive_monotone_linear {φ : ℝ → ℝ} (hmono : MonotoneOn φ (Set.Ici 0))
    (hadd : ∀ s t, 0 ≤ s → 0 ≤ t → φ (s + t) = φ s + φ t) :
    ∀ s, 0 ≤ s → φ s = s * φ 1 := by
  have h0 : φ 0 = 0 := by
    have := hadd 0 0 le_rfl le_rfl
    simp only [add_zero] at this
    linarith
  have hnat : ∀ (n : ℕ) (s : ℝ), 0 ≤ s → φ (n * s) = n * φ s := by
    intro n s hs
    induction n with
    | zero => simp [h0]
    | succ n ih =>
      push_cast
      rw [add_mul, one_mul, hadd _ _ (by positivity) hs, ih]
      ring
  have hrat : ∀ (m n : ℕ), 0 < n → φ (m / n) = m / n * φ 1 := by
    intro m n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have h1 : φ (n * (m / n)) = n * φ (m / n) := hnat n _ (by positivity)
    rw [mul_div_cancel₀ _ hn'.ne'] at h1
    have h2 : φ m = m * φ 1 := by simpa using hnat m 1 zero_le_one
    rw [eq_comm, div_mul_eq_mul_div, div_eq_iff hn'.ne']
    linarith
  intro s hs
  have hφ1 : 0 ≤ φ 1 := by
    have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 zero_le_one) zero_le_one
    rwa [h0] at this
  -- squeeze between rationals
  apply le_antisymm
  · by_contra hcon
    push Not at hcon
    -- find a rational `q ≥ s` with `q φ(1) < φ(s)`
    obtain ⟨q, hsq, hq⟩ : ∃ q : ℚ, s ≤ q ∧ (q : ℝ) * φ 1 < φ s := by
      rcases hφ1.lt_or_eq with hpos | hzero
      · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show s < φ s / φ 1 by
          rwa [lt_div_iff₀ hpos])
        exact ⟨q, hq1.le, by rwa [lt_div_iff₀ hpos] at hq2⟩
      · obtain ⟨n, hn⟩ := exists_nat_ge s
        refine ⟨n, by exact_mod_cast hn, ?_⟩
        rw [← hzero, mul_zero] at hcon ⊢
        exact hcon
    have hq0 : (0 : ℚ) ≤ q := by exact_mod_cast hs.trans hsq
    have hqval : φ q = q * φ 1 := by
      have := hrat q.num.toNat q.den q.pos
      rw [show ((q.num.toNat : ℕ) : ℝ) / (q.den : ℝ) = (q : ℝ) by
        rw [Rat.cast_def]
        congr 1
        exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.2 hq0)] at this
      exact this
    have := hmono (Set.mem_Ici.2 hs) (Set.mem_Ici.2 (hs.trans hsq)) hsq
    linarith
  · by_contra hcon
    push Not at hcon
    obtain ⟨q, hq0, hqs, hq⟩ : ∃ q : ℚ, 0 ≤ q ∧ (q : ℝ) ≤ s ∧ φ s < q * φ 1 := by
      rcases hφ1.lt_or_eq with hpos | hzero
      · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show max (φ s / φ 1) 0 < s by
          rw [max_lt_iff]
          refine ⟨by rwa [div_lt_iff₀ hpos], ?_⟩
          by_contra hs0'
          push Not at hs0'
          have hs0 : s = 0 := le_antisymm hs0' hs
          rw [hs0, h0, zero_mul] at hcon
          exact lt_irrefl _ hcon)
        refine ⟨q, by exact_mod_cast (le_max_right _ _).trans hq1.le, hq2.le, ?_⟩
        have := (le_max_left _ _).trans_lt hq1
        rwa [div_lt_iff₀ hpos] at this
      · refine ⟨0, le_rfl, by simpa using hs, ?_⟩
        rw [← hzero] at hcon ⊢
        simpa using hcon
    have hqval : φ q = q * φ 1 := by
      have := hrat q.num.toNat q.den q.pos
      rw [show ((q.num.toNat : ℕ) : ℝ) / (q.den : ℝ) = (q : ℝ) by
        rw [Rat.cast_def]
        congr 1
        exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.2 hq0)] at this
      exact this
    have := hmono (Set.mem_Ici.2 (by exact_mod_cast hq0)) (Set.mem_Ici.2 hs) hqs
    linarith

/-- **Exercise 3.G.4(a)** (MWG, p. 99), "preserved only under linear transformations". Let `f`
be increasing on `[0, ∞)` and suppose `f ∘ u` is again additively separable for the additively
separable `u(x₁, x₂) = x₁ + x₂` on `ℝ²_+`: `f(x₁ + x₂) = v₁(x₁) + v₂(x₂)`. Then `f` is affine on
`[0, ∞)`. -/
theorem exercise_3_G_4a_only_affine {f v₁ v₂ : ℝ → ℝ} (hf : MonotoneOn f (Set.Ici 0))
    (hsep : ∀ x₁ x₂, 0 ≤ x₁ → 0 ≤ x₂ → f (x₁ + x₂) = v₁ x₁ + v₂ x₂) :
    ∃ c d : ℝ, ∀ s, 0 ≤ s → f s = c * s + d := by
  set φ := fun s => f s - f 0 with hφ
  have hadd : ∀ s t, 0 ≤ s → 0 ≤ t → φ (s + t) = φ s + φ t := by
    intro s t hs ht
    have h1 := hsep s t hs ht
    have h2 := hsep s 0 hs le_rfl
    have h3 := hsep 0 t le_rfl ht
    have h4 := hsep 0 0 le_rfl le_rfl
    simp only [add_zero, zero_add] at h2 h3 h4
    simp only [hφ]
    linarith
  have hmono : MonotoneOn φ (Set.Ici 0) := fun a ha b hb hab => by
    simp only [hφ]
    linarith [hf ha hb hab]
  have hlin := closer_additive_monotone_linear hmono hadd
  refine ⟨φ 1, f 0, fun s hs => ?_⟩
  have := hlin s hs
  simp only [hφ] at this ⊢
  linarith

/-- **Exercise 3.G.4(c)** (MWG, p. 99). Additively separable utility with strictly concave
`u_l` (each `u_l'` strictly decreasing on `(0, ∞)`). Let `x ≫ 0` and `x' ≫ 0` be interior
solutions at prices `p ≫ 0` and wealth `w < w'`, characterized by the first-order conditions
`u_l'(x_l) = λ p_l`, `u_l'(x'_l) = λ' p_l` with exhausted budgets. Then `x'_l > x_l` for every
`l`: no good is inferior. -/
theorem exercise_3_G_4c {L : ℕ} {du : Fin L → ℝ → ℝ}
    (hconc : ∀ l, StrictAntiOn (du l) (Set.Ioi 0)) {p x x' : Fin L → ℝ}
    (hp : StrictlyPositive p) (hx : ∀ l, 0 < x l) (hx' : ∀ l, 0 < x' l) {lam lam' w w' : ℝ}
    (hfoc : ∀ l, du l (x l) = lam * p l) (hfoc' : ∀ l, du l (x' l) = lam' * p l)
    (hw : p ⬝ᵥ x = w) (hw' : p ⬝ᵥ x' = w') (hww : w < w') : ∀ l, x l < x' l := by
  have hlam : lam' < lam := by
    by_contra hcon
    push Not at hcon
    have hle : ∀ l, x' l ≤ x l := by
      intro l
      by_contra h
      push Not at h
      have := hconc l (hx l) (hx' l) h
      rw [hfoc, hfoc'] at this
      nlinarith [hp l]
    have : p ⬝ᵥ x' ≤ p ⬝ᵥ x :=
      Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (hle l) (hp l).le
    linarith
  intro l
  by_contra h
  push Not at h
  rcases h.lt_or_eq with h | h
  · have := hconc l (hx' l) (hx l) h
    rw [hfoc, hfoc'] at this
    nlinarith [hp l]
  · have := congrArg (du l) h
    rw [hfoc, hfoc'] at this
    have := mul_right_cancel₀ (hp l).ne' this
    linarith

/-- If `û' > 0` and `-t û''(t)/û'(t) < 1` on `(0, ∞)`, then `t û'(t)` is strictly increasing
there. -/
theorem closer_mul_deriv_strictMono {du ddu : ℝ → ℝ}
    (hd : ∀ t, 0 < t → HasDerivAt du (ddu t) t) (hpos : ∀ t, 0 < t → 0 < du t)
    (hrra : ∀ t, 0 < t → -(t * ddu t) / du t < 1) :
    StrictMonoOn (fun t => t * du t) (Set.Ioi 0) := by
  have hderiv : ∀ t ∈ Set.Ioi (0 : ℝ), HasDerivAt (fun t => t * du t) (du t + t * ddu t) t := by
    intro t ht
    exact ((hasDerivAt_id' t).mul (hd t ht)).congr_deriv (by ring)
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · exact fun t ht => (hderiv t ht).continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Ioi] at ht
    rw [(hderiv t ht).deriv]
    have h1 := hrra t ht
    have h2 := hpos t ht
    rw [div_lt_one h2] at h1
    linarith

/-- **Exercise 3.G.4(d)** (MWG, p. 99). Identical `u_l = û` with `û' > 0` strictly decreasing
(strict concavity) and `-t û''(t)/û'(t) < 1`. Let `x ≫ 0` and `x' ≫ 0` be interior solutions at
wealth `w`, prices `p` and `p'` with `p'_k > p_k` and `p'_l = p_l` for `l ≠ k`, characterized by
`û'(x_l) = λ p_l`, `û'(x'_l) = λ' p'_l` and `p·x = p'·x' = w`. Then `x'_l > x_l` for every
`l ≠ k`: the Walrasian demand has the gross substitute property. -/
theorem exercise_3_G_4d {L : ℕ} {du ddu : ℝ → ℝ}
    (hd : ∀ t, 0 < t → HasDerivAt du (ddu t) t) (hpos : ∀ t, 0 < t → 0 < du t)
    (hconc : StrictAntiOn du (Set.Ioi 0)) (hrra : ∀ t, 0 < t → -(t * ddu t) / du t < 1)
    {p p' x x' : Fin L → ℝ} (hp : StrictlyPositive p) {k : Fin L} (hk : p k < p' k)
    (hother : ∀ l, l ≠ k → p' l = p l) (hx : ∀ l, 0 < x l) (hx' : ∀ l, 0 < x' l)
    {lam lam' w : ℝ} (hfoc : ∀ l, du (x l) = lam * p l) (hfoc' : ∀ l, du (x' l) = lam' * p' l)
    (hw : p ⬝ᵥ x = w) (hw' : p' ⬝ᵥ x' = w) : ∀ l, l ≠ k → x l < x' l := by
  have hmono := closer_mul_deriv_strictMono hd hpos hrra
  have hp' : StrictlyPositive p' := fun l => by
    by_cases h : l = k
    · subst h; linarith [hp l]
    · rw [hother l h]; exact hp l
  have hlam : 0 < lam := by
    have := hfoc k
    have h1 := hpos _ (hx k)
    rw [this] at h1
    exact pos_of_mul_pos_left h1 (hp k).le
  have hlam' : 0 < lam' := by
    have := hfoc' k
    have h1 := hpos _ (hx' k)
    rw [this] at h1
    exact pos_of_mul_pos_left h1 (hp' k).le
  have hlt : lam' < lam := by
    by_contra hcon
    push Not at hcon
    have hle : ∀ l, l ≠ k → p' l * x' l ≤ p l * x l := by
      intro l hl
      rw [hother l hl]
      refine mul_le_mul_of_nonneg_left ?_ (hp l).le
      by_contra h
      push Not at h
      have := hconc (hx l) (hx' l) h
      rw [hfoc, hfoc', hother l hl] at this
      nlinarith [hp l]
    have hkk : p' k * x' k < p k * x k := by
      have hxk : x' k < x k := by
        by_contra h
        push Not at h
        rcases h.lt_or_eq with h | h
        · have := hconc (hx k) (hx' k) h
          rw [hfoc, hfoc'] at this
          nlinarith [mul_le_mul_of_nonneg_right hcon (hp k).le]
        · have := congrArg du h
          rw [hfoc, hfoc'] at this
          nlinarith [mul_le_mul_of_nonneg_right hcon (hp k).le]
      have hm := hmono (hx' k) (hx k) hxk
      simp only at hm
      rw [hfoc, hfoc'] at hm
      -- `p'_k x'_k = x'_k û'(x'_k)/λ'` and `p_k x_k = x_k û'(x_k)/λ`
      have e1 : p' k * x' k = x' k * (lam' * p' k) / lam' := by field_simp
      have e2 : p k * x k = x k * (lam * p k) / lam := by field_simp
      rw [e1, e2]
      calc x' k * (lam' * p' k) / lam' ≤ x' k * (lam' * p' k) / lam :=
            div_le_div_of_nonneg_left (by have := hp' k; have := hx' k; positivity) hlam hcon
        _ < x k * (lam * p k) / lam := (div_lt_div_iff_of_pos_right hlam).2 hm
    have hsum : p' ⬝ᵥ x' < p ⬝ᵥ x := by
      unfold dotProduct
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k),
        ← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
      exact add_lt_add_of_lt_of_le hkk (Finset.sum_le_sum fun l hl =>
        hle l (Finset.ne_of_mem_erase hl))
    linarith
  intro l hl
  by_contra h
  push Not at h
  rcases h.lt_or_eq with h | h
  · have := hconc (hx' l) (hx l) h
    rw [hfoc, hfoc', hother l hl] at this
    nlinarith [hp l]
  · have := congrArg du h
    rw [hfoc, hfoc', hother l hl] at this
    have := mul_right_cancel₀ (hp l).ne' this
    linarith

end MWG.ClassicalDemand
