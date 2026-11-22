/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPositiveEquilibriumTheory.IndexTwoGoods
import MWGPositiveEquilibriumTheory.CobbDouglasEconomy
import MWGPositiveEquilibriumTheory.Exercise17C6

/-!
# Section 17.D: figures, instances and Exercise 17.D.7 (MWG pp. 590-597, 645)

* Two-good excess demand functions `z(p) = (g(t), -t g(t))`, `t = p₁/p₂` (`twoGoodED`), satisfy
  (i)-(v) under simple conditions on `g` (`twoGoodED_isStandard`).
* **Figures 17.D.2-17.D.3** (`fig_17_D_3`): a continuum of equilibria is possible. For
  `g = 1/t - 1` on `(0, 1]`, `0` on `[1, 2]`, `2/t - 1` on `[2, ∞)`, every `p₁ ∈ [1, 2]` is an
  equilibrium, none of them is regular (zero slope), and there are infinitely many.
* **Proposition 17.D.2** for `L = 2`, instance: a two-good Cobb-Douglas economy
  (`proposition_17_D_2_two_goods_instance`).
* **Exercise 17.D.7** (`exercise_17_D_7a`, `exercise_17_D_7b`): `N` islands without communication,
  each with three equilibria, have `3^N` equilibria (one normalization per island); identical
  islands with free transport (one price system, aggregate market clearing) have three.
-/

namespace MWG.PositiveEquilibriumTheory

open Filter Topology

/-! ### Two-good excess demand functions from one function of relative prices -/

/-- The two-good excess demand `z(p) = (g(p₁/p₂), -(p₁/p₂) g(p₁/p₂))`: homogeneous and satisfying
Walras' law by construction. -/
noncomputable def twoGoodED (g : ℝ → ℝ) (p : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![g (p 0 / p 1), -(p 0 / p 1 * g (p 0 / p 1))]

/-- `twoGoodED g` satisfies (i)-(v) if `g` is continuous on `(0, ∞)`, `-s < g(t)` and
`t g(t) < s`, `g(t) → ∞` as `t → 0` and `t g(t) → -∞` as `t → ∞`. -/
theorem twoGoodED_isStandard {g : ℝ → ℝ} (hc : ContinuousOn g (Set.Ioi 0))
    (hb : ∃ s > 0, ∀ t > 0, -s < g t ∧ t * g t < s)
    (h0 : ∀ M : ℝ, ∃ δ > 0, ∀ t, 0 < t → t < δ → M < g t)
    (hinf : ∀ M : ℝ, ∃ K : ℝ, ∀ t, K < t → M < -(t * g t)) :
    IsStandardExcessDemand (twoGoodED g) := by
  have hr : ContinuousOn (fun p : Fin 2 → ℝ => p 0 / p 1) (posOrthant 2) :=
    (continuous_apply 0).continuousOn.div (continuous_apply 1).continuousOn
      fun p hp => (hp 1).ne'
  have hmaps : Set.MapsTo (fun p : Fin 2 → ℝ => p 0 / p 1) (posOrthant 2) (Set.Ioi 0) :=
    fun p hp => div_pos (hp 0) (hp 1)
  have hg : ContinuousOn (fun p : Fin 2 → ℝ => g (p 0 / p 1)) (posOrthant 2) := hc.comp hr hmaps
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine continuousOn_pi.2 fun l => ?_
    fin_cases l
    · simpa [twoGoodED] using hg
    · simp only [twoGoodED, Fin.mk_one, Fin.isValue, Matrix.cons_val_one,
        Matrix.cons_val_fin_one]
      exact (hr.mul hg).neg
  · intro p hp α hα
    have : (α • p) 0 / (α • p) 1 = p 0 / p 1 := by
      simp [mul_div_mul_left _ _ hα.ne']
    simp only [twoGoodED, this]
  · intro p hp
    have h1 := (hp 1).ne'
    simp only [twoGoodED, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    field_simp
    ring
  · obtain ⟨s, hs, hsb⟩ := hb
    refine ⟨s, hs, fun p hp l => ?_⟩
    have := hsb _ (div_pos (hp 0) (hp 1))
    fin_cases l
    · simpa [twoGoodED] using this.1
    · simp only [twoGoodED, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      linarith [this.2]
  · refine edBoundary_two (fun M => ?_) (fun M => ?_)
    · obtain ⟨δ, hδ, hM⟩ := h0 M
      refine ⟨δ, hδ, fun p hp h => ⟨0, ?_⟩⟩
      have := hM (p 0 / p 1) (div_pos (hp 0) (hp 1)) (by rw [div_lt_iff₀ (hp 1)]; linarith)
      simpa [twoGoodED] using this
    · obtain ⟨K, hK⟩ := hinf M
      refine ⟨1 / (|K| + 1), by positivity, fun p hp h => ⟨1, ?_⟩⟩
      have hK' : K < p 0 / p 1 := by
        have h1 := hp 0
        have h2 := hp 1
        rw [lt_div_iff₀ h2]
        have : p 1 * (|K| + 1) < p 0 := by
          have := mul_lt_mul_of_pos_right h (by positivity : (0 : ℝ) < |K| + 1)
          rwa [show 1 / (|K| + 1) * p 0 * (|K| + 1) = p 0 by field_simp] at this
        nlinarith [le_abs_self K, abs_nonneg K]
      simpa [twoGoodED] using hK _ hK'

/-! ### Figures 17.D.2 and 17.D.3: a continuum of equilibria -/

/-- The relative-price excess demand of Figure 17.D.3: `1/t - 1` on `(0, 1]`, `0` on `[1, 2]`,
`2/t - 1` on `[2, ∞)`. -/
noncomputable def fig17D3g (t : ℝ) : ℝ := max (1 / t - 1) 0 + min (2 / t - 1) 0

theorem fig17D3g_eq_zero {t : ℝ} (h1 : 1 ≤ t) (h2 : t ≤ 2) : fig17D3g t = 0 := by
  have ht : 0 < t := by linarith
  have : 1 / t ≤ 1 := by rw [div_le_one ht]; exact h1
  have : 1 ≤ 2 / t := by rw [le_div_iff₀ ht]; linarith
  simp only [fig17D3g]
  rw [max_eq_right (by linarith), min_eq_right (by linarith)]
  simp

/-- The excess demand of Figures 17.D.2-17.D.3. -/
noncomputable def fig17D3z : (Fin 2 → ℝ) → Fin 2 → ℝ := twoGoodED fig17D3g

/-- **Figures 17.D.2-17.D.3** (MWG, pp. 590-591). A continuum of equilibria is possible: the
excess demand `fig17D3z` satisfies (i)-(v) of Proposition 17.B.2, every `(p₁, 1)` with
`p₁ ∈ [1, 2]` is an equilibrium, none of these equilibria is regular (the slope of `z₁(·, 1)` is
zero), and there are infinitely many equilibria. -/
theorem fig_17_D_3 :
    IsStandardExcessDemand fig17D3z ∧ (∀ t ∈ Set.Icc (1 : ℝ) 2, IsNormEqm fig17D3z (vec1 t)) ∧
      (∀ t ∈ Set.Ioo (1 : ℝ) 2, ¬ IsRegularEqm fig17D3z (vec1 t)) ∧
      ¬ IsRegularEconomy fig17D3z ∧ {q | IsNormEqm fig17D3z q}.Infinite := by
  have hstd : IsStandardExcessDemand fig17D3z := by
    refine twoGoodED_isStandard ?_ ⟨2, two_pos, fun t ht => ⟨?_, ?_⟩⟩ (fun M => ?_) (fun M => ?_)
    · have h1 : ContinuousOn (fun t : ℝ => 1 / t - 1) (Set.Ioi 0) :=
        (continuousOn_const.div continuousOn_id fun t ht => ne_of_gt ht).sub continuousOn_const
      have h2 : ContinuousOn (fun t : ℝ => 2 / t - 1) (Set.Ioi 0) :=
        (continuousOn_const.div continuousOn_id fun t ht => ne_of_gt ht).sub continuousOn_const
      exact (continuous_max.comp_continuousOn (h1.prodMk continuousOn_const)).add
        (continuous_min.comp_continuousOn (h2.prodMk continuousOn_const))
    · have h1 := le_max_right (1 / t - 1) 0
      have h2 : -1 ≤ min (2 / t - 1) 0 := le_min (by
        have : 0 < 2 / t := by positivity
        linarith) (by norm_num)
      simp only [fig17D3g]; linarith
    · have ht' : (0 : ℝ) < t := ht
      have e1 : t * max (1 / t - 1) 0 = max (1 - t) 0 := by
        rw [mul_max_of_nonneg _ _ ht'.le, mul_zero, mul_sub, mul_one_div_cancel ht'.ne', mul_one]
      have e2 : t * min (2 / t - 1) 0 = min (2 - t) 0 := by
        rw [mul_min_of_nonneg _ _ ht'.le, mul_zero, mul_sub, mul_div_cancel₀ _ ht'.ne', mul_one]
      simp only [fig17D3g, mul_add, e1, e2]
      have : max (1 - t) 0 ≤ 1 := max_le (by linarith) (by norm_num)
      have : min (2 - t) 0 ≤ 0 := min_le_right _ _
      linarith
    · refine ⟨1 / (|M| + 2), by positivity, fun t ht htd => ?_⟩
      have h1 : |M| + 2 < 1 / t := by
        rw [lt_div_iff₀ ht]
        rw [lt_div_iff₀ (by positivity)] at htd
        linarith
      have h2 := le_max_left (1 / t - 1) 0
      have ht1 : t < 1 := by
        have : 1 / (|M| + 2) ≤ 1 / 2 := by
          gcongr
          linarith [abs_nonneg M]
        linarith
      have h3 : 0 ≤ min (2 / t - 1) 0 := by
        rw [min_eq_right]
        have : 2 < 2 / t := by rw [lt_div_iff₀ ht]; linarith
        linarith
      simp only [fig17D3g]
      linarith [le_abs_self M]
    · refine ⟨|M| + 3, fun t ht => ?_⟩
      have ht0 : 0 < t := by linarith [abs_nonneg M]
      have e1 : t * max (1 / t - 1) 0 = max (1 - t) 0 := by
        rw [mul_max_of_nonneg _ _ ht0.le, mul_zero, mul_sub, mul_one_div_cancel ht0.ne', mul_one]
      have e2 : t * min (2 / t - 1) 0 = min (2 - t) 0 := by
        rw [mul_min_of_nonneg _ _ ht0.le, mul_zero, mul_sub, mul_div_cancel₀ _ ht0.ne', mul_one]
      simp only [fig17D3g, mul_add, e1, e2]
      rw [max_eq_right (by linarith [abs_nonneg M]), min_eq_left (by linarith [abs_nonneg M])]
      linarith [le_abs_self M]
  have heqm : ∀ t ∈ Set.Icc (1 : ℝ) 2, IsNormEqm fig17D3z (vec1 t) := by
    intro t ht
    refine (isNormEqm_vec1_iff hstd.walras).2 ⟨by linarith [ht.1], ?_⟩
    simp [fig17D3z, twoGoodED, fig17D3g_eq_zero ht.1 ht.2]
  have hnreg : ∀ t ∈ Set.Ioo (1 : ℝ) 2, ¬ IsRegularEqm fig17D3z (vec1 t) := by
    rintro t ht ⟨-, -, hdet⟩
    apply hdet
    have hloc : normED fig17D3z =ᶠ[𝓝 (vec1 t)] fun _ => 0 := by
      have hopen : IsOpen {q : Fin 1 → ℝ | q 0 ∈ Set.Ioo (1 : ℝ) 2} :=
        isOpen_Ioo.preimage (continuous_apply 0)
      filter_upwards [hopen.mem_nhds (show vec1 t 0 ∈ Set.Ioo (1 : ℝ) 2 from ht)] with q hq
      funext l
      have hl : l = 0 := Subsingleton.elim l 0
      subst hl
      rw [← vec1_apply_zero q]
      simp [normED, truncExcessDemand, normPrice_vec1, fig17D3z, twoGoodED,
        fig17D3g_eq_zero hq.1.le hq.2.le]
    rw [hloc.fderiv_eq]
    simp only [fderiv_const_apply]
    change LinearMap.det (0 : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ)) = 0
    rw [LinearMap.det_zero]
    simp
  refine ⟨hstd, heqm, hnreg, fun hreg => hnreg (3 / 2) ⟨by norm_num, by norm_num⟩
    (hreg _ (heqm _ ⟨by norm_num, by norm_num⟩)), ?_⟩
  have hinj : Set.InjOn vec1 (Set.Icc (1 : ℝ) 2) := fun a _ b _ h => congrFun h 0
  have hsub : vec1 '' Set.Icc (1 : ℝ) 2 ⊆ {q | IsNormEqm fig17D3z q} := by
    rintro q ⟨t, ht, rfl⟩
    exact heqm t ht
  exact ((Set.Icc_infinite (by norm_num : (1 : ℝ) < 2)).image hinj).mono hsub

/-! ### Instance of the index theorem with two goods -/

/-- **Proposition 17.D.2** for `L = 2`, instance: the hypotheses hold for a two-good, one-consumer
Cobb-Douglas economy, whose indices therefore sum to `+1`. -/
theorem proposition_17_D_2_two_goods_instance :
    ∃ hfin : {q : Fin 1 → ℝ | IsNormEqm (cd1ED ![1, 1] ![1, 1]) q}.Finite,
      ∑ q ∈ hfin.toFinset, eqmIndex (cd1ED ![1, 1] ![1, 1]) q = 1 := by
  have ha : ∀ l : Fin (1 + 1), 0 < (![1, 1] : Fin 2 → ℝ) l := fun l => by
    fin_cases l <;> simp
  exact proposition_17_D_2_two_goods (cd1ED_isStandard ha ha) (cd1_isRegularEconomy ha ha)

/-! ### Exercise 17.D.7: islands -/

variable {n N : ℕ}

/-- **Exercise 17.D.7(a)** (MWG, p. 644). `N` island economies with excess demands `z_k` and no
communication: the overall economy's market for each island's goods clears separately, and with
one price normalization per island its equilibria are the tuples of island equilibria. If every
island has exactly three equilibria, the overall economy has `3^N`. -/
theorem exercise_17_D_7a (z : Fin N → (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ)
    (h3 : ∀ k, {q | IsNormEqm (z k) q}.ncard = 3) :
    {Q : Fin N → Fin n → ℝ | ∀ k, normPrice (Q k) ∈ posOrthant (n + 1) ∧
      z k (normPrice (Q k)) = 0}.ncard = 3 ^ N := by
  have hset : {Q : Fin N → Fin n → ℝ | ∀ k, normPrice (Q k) ∈ posOrthant (n + 1) ∧
      z k (normPrice (Q k)) = 0} = Set.univ.pi fun k => {q | IsNormEqm (z k) q} := by
    ext Q
    simp only [Set.mem_pi, Set.mem_univ, true_imp_iff]
    rfl
  rw [hset, ← Nat.card_coe_set_eq, Nat.card_congr (Equiv.Set.univPi _), Nat.card_pi]
  simp only [Nat.card_coe_set_eq, h3, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **Exercise 17.D.7(b)** (MWG, p. 644). Identical islands (`N ≥ 1`, excess demand `z`) with free
and costless transportation: arbitrage equalizes prices across islands, and only aggregate
excess demand `∑_k z(p_k) = N z(p)` must vanish. The equilibria correspond to those of one
island, so if an island has three equilibria, so does the overall economy. -/
theorem exercise_17_D_7b (hN : 0 < N) (z : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ)
    (h3 : {q | IsNormEqm z q}.ncard = 3) :
    {Q : Fin N → Fin n → ℝ | (∀ k, Q k = Q ⟨0, hN⟩) ∧
      (∀ k, normPrice (Q k) ∈ posOrthant (n + 1)) ∧ ∑ k, z (normPrice (Q k)) = 0}.ncard = 3 := by
  set S := {Q : Fin N → Fin n → ℝ | (∀ k, Q k = Q ⟨0, hN⟩) ∧
      (∀ k, normPrice (Q k) ∈ posOrthant (n + 1)) ∧ ∑ k, z (normPrice (Q k)) = 0}
  have hS : S = (fun q k => q) '' {q | IsNormEqm z q} := by
    ext Q
    constructor
    · rintro ⟨hc, hp, hsum⟩
      refine ⟨Q ⟨0, hN⟩, ⟨hp _, ?_⟩, funext fun k => (hc k).symm⟩
      have : ∑ k : Fin N, z (normPrice (Q k)) = (N : ℝ) • z (normPrice (Q ⟨0, hN⟩)) := by
        rw [Finset.sum_congr rfl fun k _ => by rw [hc k], Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, Nat.cast_smul_eq_nsmul]
      rw [this] at hsum
      exact (smul_eq_zero.1 hsum).resolve_left (by exact_mod_cast hN.ne')
    · rintro ⟨q, ⟨hp, hz⟩, rfl⟩
      exact ⟨fun _ => rfl, fun _ => hp, by simp [hz]⟩
  rw [hS, Set.ncard_image_of_injective _ fun a b h => congrFun h ⟨0, hN⟩, h3]

end MWG.PositiveEquilibriumTheory
