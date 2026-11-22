/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPositiveEquilibriumTheory.StandardProperties
import LeanEconomics.FixedPoint.Kakutani
import Mathlib.Topology.Order.IntermediateValue

/-!
# Existence of Walrasian equilibrium (MWG Section 17.C, pp. 584-588)

* The unit simplex `Δ` (`priceSimplex`) is nonempty, compact and convex; a maximizer of a linear
  function `v·q` on `Δ` puts no weight on non-maximal coordinates (`simplex_argmax_zero`), and
  the maximizers form the face of `Δ` spanned by the maximal coordinates
  (`simplex_argmax_iff`, **footnote 9**).
* **The case `L = 2`** (Figure 17.C.1, footnote 8): `z₁(p₁, 1) > 0` for small `p₁`
  (`footnote_17_8_low`), `z₁(p₁, 1) < 0` for large `p₁` (`footnote_17_8_high`), and an
  equilibrium exists by the intermediate value theorem (`existence_two_goods`).
* **Proposition 17.C.1** by the book's five steps: the correspondence `f : Δ ⇉ Δ`
  (`fixedPointCorr`; Step 1 at `p ≫ 0`, `f(p) = argmax_{q ∈ Δ} z(p)·q`; Step 2 on the boundary,
  `f(p) = {q ∈ Δ : p·q = 0}`); Step 3, a fixed point is an equilibrium (`step3_fixed_isEqm`);
  Step 4, `f` is convex valued (**Exercise 17.C.1**, `exercise_17_C_1`) and has a closed graph
  (`step4_isClosed_graph`, using the bound of **footnote 10**, `footnote_17_10`); Step 5,
  LeanEconomics' `kakutani` (`proposition_17_C_1`). The economy corollary:
  `proposition_17_C_1_economy`.
-/

namespace MWG.PositiveEquilibriumTheory

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.GeneralEquilibriumExamples
open MWG.WelfareTheorems
open Filter Topology

variable {L : ℕ}

/-! ### The simplex -/

/-- `Δ` is closed. -/
theorem isClosed_priceSimplex (L : ℕ) : IsClosed (priceSimplex L) := by
  have h : priceSimplex L = (⋂ l, {p : Fin L → ℝ | 0 ≤ p l}) ∩ {p | ∑ l, p l = 1} := by
    ext p
    simp [priceSimplex]
  rw [h]
  exact (isClosed_iInter fun l => isClosed_le continuous_const (continuous_apply l)).inter
    (isClosed_eq (by fun_prop) continuous_const)

/-- `Δ ⊆ [0, 1]^L`. -/
theorem priceSimplex_subset_Icc : priceSimplex L ⊆ Set.Icc 0 1 := fun p hp =>
  ⟨fun l => hp.1 l, fun l => by
    have h := Finset.single_le_sum (fun k _ => hp.1 k) (Finset.mem_univ l)
    rw [hp.2] at h
    exact h⟩

/-- `Δ` is compact. -/
theorem isCompact_priceSimplex (L : ℕ) : IsCompact (priceSimplex L) :=
  isCompact_Icc.of_isClosed_subset (isClosed_priceSimplex L) priceSimplex_subset_Icc

/-- `Δ` is convex. -/
theorem convex_priceSimplex (L : ℕ) : Convex ℝ (priceSimplex L) := by
  intro p hp q hq a b ha hb hab
  refine ⟨fun l => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hp.1 l)) (mul_nonneg hb (hq.1 l))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hp.2, hq.2]
    linarith

/-- The vertices `eₗ` of `Δ`. -/
theorem single_mem_priceSimplex (l : Fin L) : Pi.single l (1 : ℝ) ∈ priceSimplex L := by
  refine ⟨fun k => ?_, by simp⟩
  by_cases h : k = l
  · subst h
    simp
  · simp [h]

/-- No point of `Δ` is orthogonal to itself. -/
theorem dotProduct_self_pos_of_mem_priceSimplex {p : Fin L → ℝ} (hp : p ∈ priceSimplex L) :
    0 < p ⬝ᵥ p := by
  obtain ⟨l, hl⟩ : ∃ l, 0 < p l := by
    by_contra h
    push Not at h
    have : ∑ l, p l ≤ 0 := Finset.sum_nonpos fun l _ => h l
    linarith [hp.2]
  have h := Finset.single_le_sum (fun k _ => mul_self_nonneg (p k)) (Finset.mem_univ l)
  exact lt_of_lt_of_le (mul_pos hl hl) h

/-- A maximizer `q` of `v·q` on `Δ` puts zero weight on a coordinate `ℓ` with `vₗ < vₖ` for some
`k`: moving that weight to `k` would raise `v·q`. -/
theorem simplex_argmax_zero {v q : Fin L → ℝ} (hq : q ∈ priceSimplex L)
    (hmax : ∀ q' ∈ priceSimplex L, v ⬝ᵥ q' ≤ v ⬝ᵥ q) {l k : Fin L} (hlk : v l < v k) :
    q l = 0 := by
  have hne : l ≠ k := fun h => by subst h; exact lt_irrefl _ hlk
  set q' := q + q l • (Pi.single k (1 : ℝ) - Pi.single l 1) with hq'def
  have hk : q' k = q k + q l := by simp [q', hne.symm]
  have hl : q' l = 0 := by simp [q', hne]
  have hm : ∀ m, m ≠ k → m ≠ l → q' m = q m := fun m h1 h2 => by simp [q', h1, h2]
  have hq' : q' ∈ priceSimplex L := by
    refine ⟨fun m => ?_, ?_⟩
    · by_cases h1 : m = k
      · rw [h1, hk]
        exact add_nonneg (hq.1 k) (hq.1 l)
      · by_cases h2 : m = l
        · rw [h2, hl]
        · rw [hm m h1 h2]
          exact hq.1 m
    · simp [q', Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, hq.2]
  have hv : v ⬝ᵥ q' = v ⬝ᵥ q + q l * (v k - v l) := by
    simp only [q', dotProduct_add, dotProduct_smul, dotProduct_sub, dotProduct_single,
      smul_eq_mul]
    ring
  have h := hmax q' hq'
  rw [hv] at h
  have hql := hq.1 l
  nlinarith

/-- **Footnote 9** (MWG, p. 587) and the display of p. 586. The maximizers of `v·q` on `Δ` are
the `q ∈ Δ` with `q_ℓ = 0` whenever `v_ℓ < Max {v₁, ..., v_L}`: the face of `Δ` spanned by the
coordinates where `v` is maximal. -/
theorem simplex_argmax_iff {v q : Fin L → ℝ} (hq : q ∈ priceSimplex L) :
    (∀ q' ∈ priceSimplex L, v ⬝ᵥ q' ≤ v ⬝ᵥ q) ↔ ∀ l, (∃ k, v l < v k) → q l = 0 := by
  refine ⟨fun h l ⟨k, hk⟩ => simplex_argmax_zero hq h hk, fun h q' hq' => ?_⟩
  have hne : (Finset.univ : Finset (Fin L)).Nonempty := by
    by_contra h0
    rw [Finset.not_nonempty_iff_eq_empty] at h0
    have := hq.2
    rw [h0] at this
    simp at this
  obtain ⟨k0, -, hk0⟩ := Finset.exists_max_image Finset.univ v hne
  have h1 : v ⬝ᵥ q = v k0 := by
    have hc : ∀ l, v l * q l = v k0 * q l := fun l => by
      rcases (hk0 l (Finset.mem_univ l)).lt_or_eq with hlt | heq
      · rw [h l ⟨k0, hlt⟩]
        ring
      · rw [heq]
    simp only [dotProduct, hc, ← Finset.mul_sum, hq.2, mul_one]
  have h2 : v ⬝ᵥ q' ≤ v k0 := by
    calc v ⬝ᵥ q' = ∑ l, v l * q' l := rfl
      _ ≤ ∑ l, v k0 * q' l := Finset.sum_le_sum fun l _ =>
          mul_le_mul_of_nonneg_right (hk0 l (Finset.mem_univ l)) (hq'.1 l)
      _ = v k0 := by rw [← Finset.mul_sum, hq'.2, mul_one]
  linarith

/-- **Footnote 10** (MWG, p. 587). With Walras' law and the bound `z_k(p) > -s` (`s > 0`), the
expenditure on any commodity is bounded: `p_ℓ z_ℓ(p) ≤ s ∑ₖ pₖ` for `p ≫ 0` (`≤ s` on `Δ`). -/
theorem footnote_17_10 {z : (Fin L → ℝ) → Fin L → ℝ} (hW : EDWalrasLaw z) {s : ℝ}
    (hs0 : 0 < s) (hs : ∀ p ∈ posOrthant L, ∀ l, -s < z p l) {p : Fin L → ℝ}
    (hp : p ∈ posOrthant L) (l : Fin L) : p l * z p l ≤ s * ∑ k, p k := by
  have hterm : ∀ k ∈ Finset.univ, 0 ≤ p k * z p k + s * p k := fun k _ => by
    nlinarith [hs p hp k, hp k]
  have hsum : ∑ k, (p k * z p k + s * p k) = s * ∑ k, p k := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    have h := hW p hp
    simp only [dotProduct] at h
    rw [h, zero_add]
  have h := Finset.single_le_sum hterm (Finset.mem_univ l)
  rw [hsum] at h
  nlinarith [hp l]

/-! ### The case `L = 2` (Figure 17.C.1 and footnote 8) -/

/-- `(a, b) ≫ 0` for `a, b > 0`. -/
theorem vec2_mem_posOrthant {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (![a, b] : Fin 2 → ℝ) ∈ posOrthant 2 := fun l => by
  fin_cases l
  · simpa using ha
  · simpa using hb

/-- Walras' law with two goods. -/
theorem walras_two {z : (Fin 2 → ℝ) → Fin 2 → ℝ} (hW : EDWalrasLaw z) {a b : ℝ} (ha : 0 < a)
    (hb : 0 < b) : a * z ![a, b] 0 + b * z ![a, b] 1 = 0 := by
  have h := hW _ (vec2_mem_posOrthant ha hb)
  simpa [dotProduct, Fin.sum_univ_two] using h

/-- **Footnote 8** (MWG, p. 585), first claim. For `z` satisfying (i)-(v) with `L = 2`,
`z₁(p₁, 1) > 0` for `p₁` sufficiently small: along every sequence `p₁ⁿ → 0`, `p₁ⁿ > 0`. -/
theorem footnote_17_8_low {z : (Fin 2 → ℝ) → Fin 2 → ℝ} (hz : IsStandardExcessDemand z)
    {as : ℕ → ℝ} (has0 : ∀ n, 0 < as n) (has : Tendsto as atTop (𝓝 0)) :
    ∀ᶠ n in atTop, 0 < z ![as n, 1] 0 := by
  obtain ⟨s, hs0, hs⟩ := hz.boundedBelow
  have hlim : Tendsto (fun n => (![as n, 1] : Fin 2 → ℝ)) atTop (𝓝 ![0, 1]) := by
    refine tendsto_pi_nhds.2 fun l => ?_
    fin_cases l
    · simpa using has
    · simp
  have hne : (![0, 1] : Fin 2 → ℝ) ≠ 0 := fun h => by simpa using congrFun h 1
  have hv := hz.boundary _ _ (fun n => vec2_mem_posOrthant (has0 n) one_pos) hlim hne
    ⟨0, by simp⟩ s
  filter_upwards [hv, has.eventually (gt_mem_nhds one_pos)] with n hn h1
  obtain ⟨l, hl⟩ := hn
  have hw := walras_two hz.walras (has0 n) one_pos
  have hb0 := hs _ (vec2_mem_posOrthant (has0 n) one_pos) 0
  fin_cases l
  · simp only [Fin.zero_eta] at hl
    linarith
  · simp only [Fin.mk_one] at hl
    nlinarith [has0 n]

/-- **Footnote 8** (MWG, p. 585), second claim. For `z` satisfying (i)-(v) with `L = 2`,
`z₁(p₁, 1) < 0` for `p₁` sufficiently large: by homogeneity `z(p₁, 1) = z(1, 1/p₁)`, and as
`1/p₁ → 0` the second good is in excess demand. -/
theorem footnote_17_8_high {z : (Fin 2 → ℝ) → Fin 2 → ℝ} (hz : IsStandardExcessDemand z)
    {bs : ℕ → ℝ} (hbs0 : ∀ n, 0 < bs n) (hbs : Tendsto bs atTop atTop) :
    ∀ᶠ n in atTop, z ![bs n, 1] 0 < 0 := by
  obtain ⟨s, hs0, hs⟩ := hz.boundedBelow
  have hinv : Tendsto (fun n => (bs n)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hbs
  have hlim : Tendsto (fun n => (![1, (bs n)⁻¹] : Fin 2 → ℝ)) atTop (𝓝 ![1, 0]) := by
    refine tendsto_pi_nhds.2 fun l => ?_
    fin_cases l
    · simp
    · simpa using hinv
  have hne : (![1, 0] : Fin 2 → ℝ) ≠ 0 := fun h => by simpa using congrFun h 0
  have hpos : ∀ n, (![1, (bs n)⁻¹] : Fin 2 → ℝ) ∈ posOrthant 2 := fun n =>
    vec2_mem_posOrthant one_pos (inv_pos.2 (hbs0 n))
  have hv := hz.boundary _ _ hpos hlim hne ⟨1, by simp⟩ s
  filter_upwards [hv, hbs.eventually (eventually_gt_atTop 1)] with n hn h1
  have hsm : (bs n) • (![1, (bs n)⁻¹] : Fin 2 → ℝ) = ![bs n, 1] := by
    ext l
    fin_cases l
    · simp
    · simp [(hbs0 n).ne']
  have hhom := hz.homogeneous _ (hpos n) (bs n) (hbs0 n)
  rw [hsm] at hhom
  rw [hhom]
  obtain ⟨l, hl⟩ := hn
  have hw := walras_two hz.walras one_pos (inv_pos.2 (hbs0 n))
  have hb1 := hs _ (hpos n) 1
  have hb := hbs0 n
  have hmul : bs n * (bs n)⁻¹ = 1 := mul_inv_cancel₀ hb.ne'
  fin_cases l
  · simp only [Fin.zero_eta] at hl
    nlinarith
  · simp only [Fin.mk_one] at hl
    nlinarith [inv_pos.2 hb]

/-- **Section 17.C, the case `L = 2`** (MWG, pp. 584-585, Figure 17.C.1). If `z` satisfies
(i)-(v) of Proposition 17.B.2 with two goods, an equilibrium price vector `(p₁*, 1)` exists:
`z₁(·, 1)` is continuous, positive for small and negative for large `p₁`. -/
theorem existence_two_goods {z : (Fin 2 → ℝ) → Fin 2 → ℝ} (hz : IsStandardExcessDemand z) :
    ∃ p₁ : ℝ, 0 < p₁ ∧ IsEqmPrice z ![p₁, 1] := by
  have hlow := footnote_17_8_low hz (as := fun n : ℕ => 1 / ((n : ℝ) + 1))
    (fun n => by positivity) tendsto_one_div_add_atTop_nhds_zero_nat
  have hhigh := footnote_17_8_high hz (bs := fun n : ℕ => (n : ℝ) + 1) (fun n => by positivity)
    (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  obtain ⟨N, hN⟩ := (hlow.and hhigh).exists
  set a := 1 / ((N : ℝ) + 1)
  set b := (N : ℝ) + 1
  have ha : 0 < a := by positivity
  have hab : a ≤ b := by
    have h1 : a ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
    linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have hvec : Continuous fun t : ℝ => (![t, 1] : Fin 2 → ℝ) := by
    refine continuous_pi fun l => ?_
    fin_cases l
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      exact continuous_id'
    · simpa using continuous_const
  have hcont : ContinuousOn (fun t : ℝ => z ![t, 1] 0) (Set.Icc a b) := by
    have hz' : ContinuousOn (fun t : ℝ => z ![t, 1]) (Set.Icc a b) :=
      hz.continuous.comp hvec.continuousOn fun t ht =>
        vec2_mem_posOrthant (lt_of_lt_of_le ha ht.1) one_pos
    exact (continuous_apply 0).comp_continuousOn hz'
  obtain ⟨p₁, hp₁, hzero⟩ := intermediate_value_Icc' hab hcont ⟨hN.2.le, hN.1.le⟩
  have hp₁0 : 0 < p₁ := lt_of_lt_of_le ha hp₁.1
  refine ⟨p₁, hp₁0, vec2_mem_posOrthant hp₁0 one_pos, ?_⟩
  have hw := walras_two hz.walras hp₁0 one_pos
  simp only at hzero
  rw [hzero, mul_zero, zero_add, one_mul] at hw
  funext l
  fin_cases l
  · simpa using hzero
  · simpa using hw

/-! ### Proposition 17.C.1 -/

open Classical in
/-- **Proof of Proposition 17.C.1, Steps 1 and 2** (MWG, p. 586). The fixed-point
correspondence `f : Δ ⇉ Δ`: for `p ≫ 0`, `f(p) = {q ∈ Δ : z(p)·q ≥ z(p)·q' for all q' ∈ Δ}`;
for `p` on the boundary of `Δ`, `f(p) = {q ∈ Δ : p·q = 0}`. -/
noncomputable def fixedPointCorr (z : (Fin L → ℝ) → Fin L → ℝ) (p : Fin L → ℝ) :
    Set (Fin L → ℝ) :=
  if p ∈ posOrthant L then
    {q | q ∈ priceSimplex L ∧ ∀ q' ∈ priceSimplex L, z p ⬝ᵥ q' ≤ z p ⬝ᵥ q}
  else {q | q ∈ priceSimplex L ∧ p ⬝ᵥ q = 0}

/-- **Step 1** (MWG, p. 586). `f` at `p ≫ 0`. -/
theorem fixedPointCorr_pos (z : (Fin L → ℝ) → Fin L → ℝ) {p : Fin L → ℝ}
    (hp : p ∈ posOrthant L) :
    fixedPointCorr z p =
      {q | q ∈ priceSimplex L ∧ ∀ q' ∈ priceSimplex L, z p ⬝ᵥ q' ≤ z p ⬝ᵥ q} := by
  simp only [fixedPointCorr, hp, ↓reduceIte]

/-- **Step 2** (MWG, p. 586). `f` on the boundary. -/
theorem fixedPointCorr_not_pos (z : (Fin L → ℝ) → Fin L → ℝ) {p : Fin L → ℝ}
    (hp : p ∉ posOrthant L) :
    fixedPointCorr z p = {q | q ∈ priceSimplex L ∧ p ⬝ᵥ q = 0} := by
  simp only [fixedPointCorr, hp, ↓reduceIte]

/-- `f(p) ⊆ Δ`. -/
theorem fixedPointCorr_subset (z : (Fin L → ℝ) → Fin L → ℝ) (p : Fin L → ℝ) :
    fixedPointCorr z p ⊆ priceSimplex L := by
  intro q hq
  unfold fixedPointCorr at hq
  split_ifs at hq
  · exact hq.1
  · exact hq.1

/-- **Step 1** (MWG, p. 586), the display: for `p ≫ 0`,
`f(p) = {q ∈ Δ : q_ℓ = 0 if z_ℓ(p) < Max {z₁(p), ..., z_L(p)}}`. -/
theorem step1_face (z : (Fin L → ℝ) → Fin L → ℝ) {p : Fin L → ℝ} (hp : p ∈ posOrthant L) :
    fixedPointCorr z p =
      {q | q ∈ priceSimplex L ∧ ∀ l, (∃ k, z p l < z p k) → q l = 0} := by
  rw [fixedPointCorr_pos z hp]
  ext q
  exact ⟨fun h => ⟨h.1, (simplex_argmax_iff h.1).1 h.2⟩,
    fun h => ⟨h.1, (simplex_argmax_iff h.1).2 h.2⟩⟩

/-- **Step 1** (MWG, p. 586). If `z(p) ≠ 0` at `p ≫ 0`, Walras' law gives a good in excess
supply and one in excess demand, so `f(p) ⊆ Boundary Δ`. -/
theorem step1_subset_boundary {z : (Fin L → ℝ) → Fin L → ℝ} (hW : EDWalrasLaw z)
    {p : Fin L → ℝ} (hp : p ∈ posOrthant L) (hz : z p ≠ 0) :
    ∀ q ∈ fixedPointCorr z p, q ∉ posOrthant L := by
  have hterms : (∀ l, 0 ≤ z p l) → z p = 0 := fun h => by
    have hw := hW p hp
    simp only [dotProduct] at hw
    funext l
    have := (Finset.sum_eq_zero_iff_of_nonneg fun k _ => mul_nonneg (hp k).le (h k)).1 hw l
      (Finset.mem_univ l)
    simpa using (mul_eq_zero.1 this).resolve_left (hp l).ne'
  have htermsn : (∀ l, z p l ≤ 0) → z p = 0 := fun h => by
    have hw := hW p hp
    simp only [dotProduct] at hw
    funext l
    have := (Finset.sum_eq_zero_iff_of_nonpos fun k _ =>
      mul_nonpos_of_nonneg_of_nonpos (hp k).le (h k)).1 hw l (Finset.mem_univ l)
    simpa using (mul_eq_zero.1 this).resolve_left (hp l).ne'
  obtain ⟨l, hl⟩ : ∃ l, z p l < 0 := by
    by_contra h
    push Not at h
    exact hz (hterms h)
  obtain ⟨k, hk⟩ : ∃ k, 0 < z p k := by
    by_contra h
    push Not at h
    exact hz (htermsn h)
  intro q hq hqpos
  rw [fixedPointCorr_pos z hp] at hq
  exact (hqpos l).ne' (simplex_argmax_zero hq.1 hq.2 (hl.trans hk))

/-- **Step 1** (MWG, p. 586). If `z(p) = 0`, then `f(p) = Δ`. -/
theorem step1_eq_simplex {z : (Fin L → ℝ) → Fin L → ℝ} {p : Fin L → ℝ}
    (hp : p ∈ posOrthant L) (hz : z p = 0) : fixedPointCorr z p = priceSimplex L := by
  rw [fixedPointCorr_pos z hp, hz]
  ext q
  simp only [zero_dotProduct, le_refl, implies_true, and_true, Set.mem_ofPred_eq]

/-- **Footnote 9** (MWG, p. 587), boundary case. For `p ∈ Boundary Δ`, `f(p)` is the face of `Δ`
spanned by the zero coordinates of `p`. -/
theorem footnote_17_9_boundary (z : (Fin L → ℝ) → Fin L → ℝ) {p : Fin L → ℝ}
    (hpΔ : p ∈ priceSimplex L) (hp : p ∉ posOrthant L) :
    fixedPointCorr z p = {q | q ∈ priceSimplex L ∧ ∀ l, 0 < p l → q l = 0} := by
  rw [fixedPointCorr_not_pos z hp]
  ext q
  simp only [Set.mem_ofPred_eq]
  refine ⟨fun h => ⟨h.1, fun l hl => ?_⟩, fun h => ⟨h.1, ?_⟩⟩
  · have := (Finset.sum_eq_zero_iff_of_nonneg fun k _ => mul_nonneg (hpΔ.1 k) (h.1.1 k)).1 h.2 l
      (Finset.mem_univ l)
    exact (mul_eq_zero.1 this).resolve_left hl.ne'
  · refine Finset.sum_eq_zero fun l _ => ?_
    rcases (hpΔ.1 l).lt_or_eq with hl | hl
    · rw [h.2 l hl, mul_zero]
    · rw [← hl, zero_mul]

/-- **Step 2** (MWG, p. 586). `f(p) ≠ ∅` on the boundary: some `p_ℓ = 0`, and `eₗ ∈ f(p)`. -/
theorem step2_nonempty (z : (Fin L → ℝ) → Fin L → ℝ) {p : Fin L → ℝ}
    (hpΔ : p ∈ priceSimplex L) (hp : p ∉ posOrthant L) : (fixedPointCorr z p).Nonempty := by
  simp only [mem_posOrthant, not_forall, not_lt] at hp
  obtain ⟨l, hl⟩ := hp
  have hl0 : p l = 0 := le_antisymm hl (hpΔ.1 l)
  rw [fixedPointCorr_not_pos z (by simp only [mem_posOrthant, not_forall, not_lt]; exact ⟨l, hl⟩)]
  exact ⟨Pi.single l 1, single_mem_priceSimplex l, by simp [hl0]⟩

/-- **Step 2** (MWG, p. 586). No boundary price vector is a fixed point: `p·p > 0`. -/
theorem step2_not_fixed (z : (Fin L → ℝ) → Fin L → ℝ) {p : Fin L → ℝ}
    (hpΔ : p ∈ priceSimplex L) (hp : p ∉ posOrthant L) : p ∉ fixedPointCorr z p := by
  rw [fixedPointCorr_not_pos z hp]
  exact fun h => (dotProduct_self_pos_of_mem_priceSimplex hpΔ).ne' h.2

/-- `f(p) ≠ ∅` for every `p ∈ Δ` (Steps 1-2): at `p ≫ 0` a linear function attains its maximum
on the compact set `Δ`. -/
theorem fixedPointCorr_nonempty (z : (Fin L → ℝ) → Fin L → ℝ) {p : Fin L → ℝ}
    (hpΔ : p ∈ priceSimplex L) : (fixedPointCorr z p).Nonempty := by
  by_cases hp : p ∈ posOrthant L
  · rw [fixedPointCorr_pos z hp]
    have hne : (priceSimplex L).Nonempty := ⟨p, hpΔ⟩
    have hc : Continuous fun q : Fin L → ℝ => z p ⬝ᵥ q := by
      simp only [dotProduct]
      fun_prop
    obtain ⟨q, hq, hmax⟩ := (isCompact_priceSimplex L).exists_isMaxOn hne hc.continuousOn
    exact ⟨q, hq, fun q' hq' => hmax hq'⟩
  · exact step2_nonempty z hpΔ hp

/-- **Step 3** (MWG, p. 586). A fixed point `p* ∈ f(p*)` is an equilibrium price vector: it is
not on the boundary (Step 2), and at `p* ≫ 0` all `z_ℓ(p*)` are equal (else `p*_ℓ = 0`), so
Walras' law forces `z(p*) = 0`. -/
theorem step3_fixed_isEqm {z : (Fin L → ℝ) → Fin L → ℝ} (hW : EDWalrasLaw z)
    {p : Fin L → ℝ} (hpΔ : p ∈ priceSimplex L) (hfix : p ∈ fixedPointCorr z p) :
    IsEqmPrice z p := by
  by_cases hpos : p ∈ posOrthant L
  · rw [fixedPointCorr_pos z hpos] at hfix
    refine ⟨hpos, ?_⟩
    have hle : ∀ l k, z p k ≤ z p l := fun l k =>
      not_lt.1 fun h => (hpos l).ne' (simplex_argmax_zero hfix.1 hfix.2 h)
    funext l
    have hall : ∀ k, z p k = z p l := fun k => le_antisymm (hle l k) (hle k l)
    have hw := hW p hpos
    simp only [dotProduct, hall, ← Finset.sum_mul, hpΔ.2, one_mul] at hw
    exact hw
  · exact (step2_not_fixed z hpΔ hpos hfix).elim

/-- **Exercise 17.C.1** (MWG, p. 642), Step 4 (MWG, p. 587). The correspondence `f` is convex
valued: both cases are level sets of a linear function on the convex set `Δ`. -/
theorem exercise_17_C_1 (z : (Fin L → ℝ) → Fin L → ℝ) (p : Fin L → ℝ) :
    Convex ℝ (fixedPointCorr z p) := by
  unfold fixedPointCorr
  split_ifs
  · intro q hq q₂ hq₂ a b ha hb hab
    refine ⟨convex_priceSimplex L hq.1 hq₂.1 ha hb hab, fun q' hq' => ?_⟩
    rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    have h1 := mul_le_mul_of_nonneg_left (hq.2 q' hq') ha
    have h2 := mul_le_mul_of_nonneg_left (hq₂.2 q' hq') hb
    have h3 : z p ⬝ᵥ q' = a * z p ⬝ᵥ q' + b * z p ⬝ᵥ q' := by rw [← add_mul, hab, one_mul]
    linarith
  · intro q hq q₂ hq₂ a b ha hb hab
    refine ⟨convex_priceSimplex L hq.1 hq₂.1 ha hb hab, ?_⟩
    rw [dotProduct_add, dotProduct_smul, dotProduct_smul, hq.2, hq₂.2]
    simp

/-- **Step 4** (MWG, p. 587). The correspondence `f` has a closed graph over `Δ` (equivalently,
it is upper hemicontinuous). At an interior limit this is continuity of `z`; at a boundary
limit `p` with `p_ℓ > 0`, eventually `qⁿ_ℓ = 0`: on boundary `pⁿ` by definition, and on
interior `pⁿ` because `z_ℓ(pⁿ) ≤ 2s/p_ℓ` (footnote 10) while by (v) some `z_k(pⁿ)` exceeds this
bound. -/
theorem step4_isClosed_graph {z : (Fin L → ℝ) → Fin L → ℝ} (hz : IsStandardExcessDemand z) :
    IsClosed (LeanEconomics.FixedPoint.graphOn (priceSimplex L) (fixedPointCorr z)) := by
  obtain ⟨s, hs0, hs⟩ := hz.boundedBelow
  refine IsSeqClosed.isClosed fun {xs} {a} hxs hlim => ?_
  have hP : Tendsto (fun n => (xs n).1) atTop (𝓝 a.1) := (continuous_fst.tendsto a).comp hlim
  have hQ : Tendsto (fun n => (xs n).2) atTop (𝓝 a.2) := (continuous_snd.tendsto a).comp hlim
  have hpΔ : a.1 ∈ priceSimplex L := (isClosed_priceSimplex L).mem_of_tendsto hP
    (Eventually.of_forall fun n => (hxs n).1)
  have hqΔ : a.2 ∈ priceSimplex L := (isClosed_priceSimplex L).mem_of_tendsto hQ
    (Eventually.of_forall fun n => fixedPointCorr_subset z _ (hxs n).2)
  refine ⟨hpΔ, ?_⟩
  by_cases hpos : a.1 ∈ posOrthant L
  · rw [fixedPointCorr_pos z hpos]
    refine ⟨hqΔ, fun q' hq' => ?_⟩
    have hev : ∀ᶠ n in atTop, (xs n).1 ∈ posOrthant L :=
      hP.eventually ((isOpen_posOrthant L).mem_nhds hpos)
    have hZ : Tendsto (fun n => z (xs n).1) atTop (𝓝 (z a.1)) :=
      (hz.continuous a.1 hpos).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hP, hev⟩)
    refine le_of_tendsto_of_tendsto (appendixA_tendsto_dotProduct_seq hZ tendsto_const_nhds)
      (appendixA_tendsto_dotProduct_seq hZ hQ) ?_
    filter_upwards [hev] with n hn
    have h := (hxs n).2
    rw [fixedPointCorr_pos z hn] at h
    exact h.2 q' hq'
  · rw [footnote_17_9_boundary z hpΔ hpos]
    refine ⟨hqΔ, fun l hl => ?_⟩
    have hev0 : ∀ᶠ n in atTop, (xs n).2 l = 0 := by
      by_contra hcon
      rw [Filter.not_eventually] at hcon
      have hpl : ∀ᶠ n in atTop, a.1 l / 2 < (xs n).1 l :=
        (((continuous_apply l).tendsto _).comp hP).eventually (lt_mem_nhds (by linarith))
      obtain ⟨φ, hφ, hφP⟩ := Filter.extraction_of_frequently_atTop (hcon.and_eventually hpl)
      have hposφ : ∀ k, (xs (φ k)).1 ∈ posOrthant L := by
        intro k
        by_contra hk
        have h := (hxs (φ k)).2
        rw [fixedPointCorr_not_pos z hk] at h
        have hpn := (hxs (φ k)).1
        have hterm := (Finset.sum_eq_zero_iff_of_nonneg fun m _ =>
          mul_nonneg (hpn.1 m) (h.1.1 m)).1 h.2 l (Finset.mem_univ l)
        rcases mul_eq_zero.1 hterm with h1 | h1
        · linarith [(hφP k).2]
        · exact (hφP k).1 h1
      have hzero : ∃ l', a.1 l' = 0 := by
        simp only [mem_posOrthant, not_forall, not_lt] at hpos
        obtain ⟨l', hl'⟩ := hpos
        exact ⟨l', le_antisymm hl' (hpΔ.1 l')⟩
      have hne0 : a.1 ≠ 0 := fun h => by
        have := hpΔ.2
        rw [h] at this
        simp at this
      have hv := hz.boundary (fun k => (xs (φ k)).1) a.1 hposφ (hP.comp hφ.tendsto_atTop) hne0
        hzero (2 * s / a.1 l)
      obtain ⟨k, m, hm⟩ := hv.exists
      have hb := footnote_17_10 hz.walras hs0 hs (hposφ k) l
      rw [(hxs (φ k)).1.2, mul_one] at hb
      have hzl : z (xs (φ k)).1 l < z (xs (φ k)).1 m := by
        refine lt_of_le_of_lt ?_ hm
        rw [le_div_iff₀ hl]
        have h2 := (hφP k).2
        rcases le_or_gt (z (xs (φ k)).1 l) 0 with h3 | h3
        · nlinarith
        · nlinarith
      have h := (hxs (φ k)).2
      rw [fixedPointCorr_pos z (hposφ k)] at h
      exact (hφP k).1 (simplex_argmax_zero h.1 h.2 hzl)
    exact tendsto_nhds_unique (((continuous_apply l).tendsto _).comp hQ)
      (tendsto_const_nhds.congr' (hev0.mono fun n hn => hn.symm))

/-- **Proposition 17.C.1** (MWG, p. 585). If `z(p)`, defined for all `p ≫ 0`, satisfies
conditions (i)-(v) of Proposition 17.B.2, then `z(p) = 0` has a solution. Step 5: Kakutani's
theorem applied to `f : Δ ⇉ Δ`. -/
theorem proposition_17_C_1 {z : (Fin L → ℝ) → Fin L → ℝ} (hz : IsStandardExcessDemand z) :
    ∃ p, IsEqmPrice z p := by
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · exact ⟨0, fun l => l.elim0, funext fun l => l.elim0⟩
  have hne : (priceSimplex L).Nonempty := ⟨Pi.single ⟨0, hL⟩ 1, single_mem_priceSimplex _⟩
  obtain ⟨p, hpΔ, hfix⟩ := LeanEconomics.FixedPoint.kakutani (isCompact_priceSimplex L)
    (convex_priceSimplex L) hne (fun p hp => fixedPointCorr_nonempty z hp)
    (fun p _ => exercise_17_C_1 z p) (fun p _ => fixedPointCorr_subset z p)
    (step4_isClosed_graph hz)
  exact ⟨p, step3_fixed_isEqm hz.walras hpΔ hfix⟩

/-- **Proposition 17.C.1** (MWG, p. 585), second sentence. A Walrasian equilibrium exists in any
pure exchange economy (`Xᵢ = ℝ^L₊`, `L ≥ 1`) with `∑ᵢ ωᵢ ≫ 0`, `ωᵢ ∈ ℝ^L₊`, and continuous,
strictly convex and strongly monotone preferences. -/
theorem proposition_17_C_1_economy {ι : Type*} [Fintype ι] {E : ExchangeEconomy ι L}
    (hL : 0 < L) (hX : ∀ i, E.X i = nonnegOrthant L) (hu : ∀ i, StandardUtility (E.u i))
    (hω : ∀ i, E.ω i ∈ nonnegOrthant L) (hpos : ∀ l, 0 < E.totalEndowment l) :
    ∃ p a, (pureExchangeEconomy E).IsWalrasEqm a p := by
  have hι : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := hpos ⟨0, hL⟩
    simp [ExchangeEconomy.totalEndowment] at this
  obtain ⟨p, hp⟩ := proposition_17_C_1 (proposition_17_B_2 hX hu hω hpos)
  exact ⟨p, (eqm_iff_isEqmPrice hL hX hu hω p).2 hp⟩

end MWG.PositiveEquilibriumTheory
