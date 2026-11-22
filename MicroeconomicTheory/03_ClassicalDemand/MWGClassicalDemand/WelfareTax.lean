/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGClassicalDemand.WelfareIntegrals

/-!
# Welfare evaluation: a commodity tax with lump-sum rebate (Exercise 3.I.9)

MWG, Exercise 3.I.9 (p. 103). A tax `t` per unit on good `l` raises its price to `p_l + t`; the
revenue `R = t x_l` is rebated lump sum, so in equilibrium the consumer faces
`(p + t e_l, w + R)` with `R = t x_l(p + t e_l, w + R)`.

* The bundle bought in such an equilibrium costs exactly `w` at the pretax prices (Walras' law),
  so it was affordable without the tax: utility under any tax-rebate equilibrium is at most
  `v(p, w)`, the utility with `t = 0` (`exercise_3_I_9`). This needs no assumption on `s_ll`.
* With strictly convex preferences, a differentiable demand and `s_ll(p, w) < 0` everywhere, every
  `t ≠ 0` is strictly worse (`exercise_3_I_9_strict`): otherwise the Hicksian demand for good `l`
  at the pretax utility would take the same value at `p_l` and `p_l + t`, while its derivative
  `s_ll` (Slutsky equation) is negative.
-/

namespace MWG.ClassicalDemand

open MWG.ConsumerChoice Kreps.PreferenceProperties Filter Topology

variable {L : ℕ}

/-- `priceLine p l (p_l + t) = p + t e_l`, so its cost of a bundle is `p·x + t x_l`. -/
theorem priceLine_dot (p : Fin L → ℝ) (l : Fin L) (t : ℝ) (x : Fin L → ℝ) :
    priceLine p l (p l + t) ⬝ᵥ x = p ⬝ᵥ x + t * x l := by
  have : priceLine p l (p l + t) = p + t • Pi.single l 1 := by
    funext k
    by_cases hk : k = l
    · subst hk; simp [priceLine]
    · simp [priceLine, hk]
  rw [this, add_dotProduct, smul_dotProduct, single_dotProduct, one_mul, smul_eq_mul]

/-- **Exercise 3.I.9** (MWG, p. 103), optimality of `t = 0`. If `x = x(p + t e_l, w + R)` with the
rebate `R = t x_l` (and `p + t e_l ≫ 0`), then `v(p + t e_l, w + R) ≤ v(p, w)`, and the bundle
costs `w` at the pretax prices. -/
theorem exercise_3_I_9 {u : (Fin L → ℝ) → ℝ} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hrep : RepresentsOn (nonnegOrthant L) u r) (hu : ContinuousOn u (nonnegOrthant L))
    (hlns : LocallyNonsatiated (nonnegOrthant L) r) {xs : DemandFunction L}
    {p : Fin L → ℝ} (hp : StrictlyPositive p) (l : Fin L) {t R w : ℝ}
    (hx : xs (priceLine p l (p l + t)) (w + R) ∈
      walrasianDemand u (priceLine p l (p l + t)) (w + R))
    (hR : R = t * xs (priceLine p l (p l + t)) (w + R) l) :
    p ⬝ᵥ xs (priceLine p l (p l + t)) (w + R) = w ∧
      indirectUtility u (priceLine p l (p l + t)) (w + R) ≤ indirectUtility u p w := by
  set x := xs (priceLine p l (p l + t)) (w + R)
  have hw := proposition_3_D_2_ii hrep hlns hx
  rw [priceLine_dot] at hw
  have hpx : p ⬝ᵥ x = w := by linarith
  refine ⟨hpx, ?_⟩
  rw [indirectUtility_eq_of_mem hx]
  exact le_indirectUtility hu hp ⟨hx.1.1, hpx.le⟩

/-- **Exercise 3.I.9** (MWG, p. 103): the optimal tax is zero, strictly. Let `≿` be strictly
convex, the demand function `x(·, ·)` differentiable on `p ≫ 0, w > 0` with
`s_ll(p, w) < 0` everywhere. For `t ≠ 0` with `p_l + t > 0`, any tax-rebate equilibrium
`(p + t e_l, w + R)`, `R = t x_l`, `w + R > 0`, gives strictly lower utility than `t = 0`. -/
theorem exercise_3_I_9_strict {u : (Fin L → ℝ) → ℝ} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hrep : RepresentsOn (nonnegOrthant L) u r) (hu : ContinuousOn u (nonnegOrthant L))
    (hlns : LocallyNonsatiated (nonnegOrthant L) r)
    (hsc : PrefStrictlyConvex (nonnegOrthant L) r) {xs : DemandFunction L}
    (hxs : ∀ q w, StrictlyPositive q → 0 ≤ w → xs q w ∈ walrasianDemand u q w)
    {Dx : (Fin L → ℝ) → ℝ → ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)}
    (hD : ∀ q w, PWDomain q w → HasFDerivAt (Function.uncurry xs) (Dx q w) (q, w))
    {l : Fin L} (hs : ∀ q w, PWDomain q w → slutskyMatrix (Dx q w) (xs q w) l l < 0)
    {p : Fin L → ℝ} (hp : StrictlyPositive p) {t R w : ℝ} (hw : 0 < w) (ht : t ≠ 0)
    (hpt : 0 < p l + t) (hwR : 0 < w + R)
    (hR : R = t * xs (priceLine p l (p l + t)) (w + R) l) :
    indirectUtility u (priceLine p l (p l + t)) (w + R) < indirectUtility u p w := by
  have hq := (prefStrictlyConvex_iff_strictlyQuasiconcaveOn (convex_nonnegOrthant L) hrep).mp hsc
  have hpt' := priceLine_pos hp l hpt
  have hx := hxs _ _ hpt' hwR.le
  obtain ⟨hpx, hle⟩ := exercise_3_I_9 hrep hu hlns hp l hx hR
  rcases hle.lt_or_eq with hlt | heq
  · exact hlt
  exfalso
  set x := xs (priceLine p l (p l + t)) (w + R) with hxdef
  set u₀ := indirectUtility u p w with hu₀
  have hx0 : x ∈ walrasianDemand u p w := by
    refine ⟨⟨hx.1.1, hpx.le⟩, fun y hy => ?_⟩
    rw [← indirectUtility_eq_of_mem hx, heq]
    exact le_indirectUtility hu hp hy
  have hxeq : x = xs p w :=
    proposition_3_D_2_iii_unique hq p w hx0 (hxs p w hp hw.le)
  have hub : u 0 < u₀ := relations_indirectUtility_gt_zero hrep hu hlns hp hw
  have hne : ∃ y ∈ nonnegOrthant L, u₀ ≤ u y := welfare_v_attainable hu hp hw.le
  -- the Hicksian demand curve for good `l` at `u⁰` takes the value `x_l` at both prices
  set g : ℝ → ℝ := fun s => hicksianOf u xs (priceLine p l s) u₀ l with hg
  have he₀ : expenditure u (priceLine p l (p l)) u₀ = w := by
    rw [show priceLine p l (p l) = p by simp [priceLine]]
    exact equation_3_E_1_left hrep hu hlns hp hw.le
  have he₁ : expenditure u (priceLine p l (p l + t)) u₀ = w + R := by
    have := equation_3_E_1_left hrep hu hlns hpt' hwR.le (p := priceLine p l (p l + t))
    rw [heq] at this
    exact this
  have hg0 : g (p l) = x l := by
    change hicksianOf u xs (priceLine p l (p l)) u₀ l = x l
    rw [hicksianOf, he₀, show priceLine p l (p l) = p by simp [priceLine], ← hxeq]
  have hg1 : g (p l + t) = x l := by
    change hicksianOf u xs (priceLine p l (p l + t)) u₀ l = x l
    rw [hicksianOf, he₁]
  -- `g` has derivative `s_ll < 0` at every positive price
  have hderiv : ∀ s, 0 < s → ∃ d < 0, HasDerivAt g d s := by
    intro s hs0
    have hqs := priceLine_pos hp l hs0
    set q := priceLine p l s
    have heps : 0 < expenditure u q u₀ := by
      rcases (expenditure_nonneg u hqs u₀).lt_or_eq with h | h
      · exact h
      · exfalso
        have h1 := equation_3_E_1_right hu hqs hub hne
        rw [← h, exp_indirectUtility_zero_wealth u hqs] at h1
        linarith
    have hpw : PWDomain q (expenditure u q u₀) := ⟨hqs, heps⟩
    have hv : indirectUtility u q (expenditure u q u₀) = u₀ :=
      equation_3_E_1_right hu hqs hub hne
    obtain ⟨hhd, hjac⟩ := proposition_3_G_3 hrep hu hlns hsc
      (fun q' w' hd => hxs q' w' hd.1 hd.2.le) hpw (hD _ _ hpw)
      (hf := fun q' => hicksianOf u xs q' u₀)
      (fun q' hq' => by rw [hv]; exact hicksianOf_mem hrep hu hlns hxs hq' hub hne)
    refine ⟨slutskyMatrix (Dx q (expenditure u q u₀)) (xs q (expenditure u q u₀)) l l,
      hs _ _ hpw, ?_⟩
    have h1 := hhd.comp_hasDerivAt s (priceLine_hasDerivAt p l s)
    have h2 := hasDerivAt_pi.mp h1 l
    rw [← hjac]
    exact h2
  -- strictly decreasing on the segment between `p_l` and `p_l + t`
  have hsub : ∀ s ∈ Set.uIcc (p l) (p l + t), 0 < s := fun s hs =>
    lt_of_lt_of_le (lt_min (hp l) hpt) hs.1
  have hanti : StrictAntiOn g (Set.uIcc (p l) (p l + t)) := by
    apply strictAntiOn_of_deriv_neg (convex_uIcc _ _)
    · intro s hs
      obtain ⟨d, -, hd⟩ := hderiv s (hsub s hs)
      exact hd.continuousAt.continuousWithinAt
    · intro s hs
      obtain ⟨d, hd0, hd⟩ := hderiv s (hsub s (interior_subset hs))
      rw [hd.deriv]
      exact hd0
  rcases lt_or_gt_of_ne ht with htn | htp
  · have := hanti (Set.right_mem_uIcc) (Set.left_mem_uIcc) (by linarith)
    rw [hg0, hg1] at this
    exact lt_irrefl _ this
  · have := hanti (Set.left_mem_uIcc) (Set.right_mem_uIcc) (by linarith)
    rw [hg0, hg1] at this
    exact lt_irrefl _ this

end MWG.ClassicalDemand
