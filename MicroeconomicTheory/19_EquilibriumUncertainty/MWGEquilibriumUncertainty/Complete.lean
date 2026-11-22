/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGEquilibriumUncertainty.AssetsFOC

/-!
# Complete asset structures, spanning and pricing by arbitrage (MWG pp. 705-707, 727-728)

* **Proposition 19.E.2(i)** with **Exercise 19.E.3**: with a complete asset structure, an
  Arrow-Debreu equilibrium is a Radner equilibrium with `q_k = ∑_s p_{gs} r_{sk}`
  (`proposition_19_E_2_i`).
* **Proposition 19.E.2(ii)**: a Radner equilibrium with a complete structure is an Arrow-Debreu
  equilibrium at prices `μ_s p_s`, `μ ≫ 0` (`proposition_19_E_2_ii`). As with Proposition
  19.D.1(ii), exact market clearing needs monotone preferences (strong monotonicity is assumed;
  correction 2).
* Uniqueness of the multipliers when `rank R = S` (p. 703), and `μ_s` is the price of the Arrow
  security of state `s` (p. 707).
* **Proposition 19.E.3**: if `Range R' = Range R`, Radner equilibrium allocations for `R` are Radner
  equilibrium allocations for `R'` (with strongly monotone preferences, used as in the book's
  proof), and redundant assets do not change the range (p. 706).
* **Exercise 19.E.4**: pricing by arbitrage of a redundant asset.
* **Example 19.E.6**: pricing an option; the formula (19.E.2), its monotonicity in `c` and `q₂`,
  and in the dispersion `α`. The printed argument for the last claim prices `r'₂(c) - r₂(c)` and
  `r₂(c)` with the multipliers of the original economy; the identity `q'₂(c) = q₃ + q₂(c)` it uses
  fails (`example_19_E_6_identity_fails`), but the conclusion is true
  (`example_19_E_6_dispersion`). Correction 5.
* **Exercise 19.E.6(a)-(f)**: pricing derived assets on `r₁ = (64, 16, 4)`, `r₂ = (0, 0, 1)`. In (d)
  the added riskless asset at price `1` creates an arbitrage (correction 6).
-/

namespace MWG.EquilibriumUncertainty

open Matrix

variable {S L K : ℕ}

/-- `q·z = ∑_s ν_s (Rz)_s` when `q_k = ∑_s ν_s r_{sk}`. -/
theorem dot_eq_of_pricing {R : Matrix (Fin S) (Fin K) ℝ} {ν : Fin S → ℝ} {q : Fin K → ℝ}
    (hq : ∀ k, q k = ∑ s, ν s * R s k) (z : Fin K → ℝ) : q ⬝ᵥ z = ν ⬝ᵥ (R *ᵥ z) := by
  simp only [dotProduct, mulVec, hq, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun k _ => by ring

/-! ## Proposition 19.E.2 -/

/-- **Proposition 19.E.2(i)** (MWG, p. 705) with **Exercise 19.E.3** (p. 727). Suppose the asset
structure is complete. If `x*` and `p` with `p_{gs} > 0` form an Arrow-Debreu equilibrium, then with
`q_k = ∑_s p_{gs} r_{sk}` there are portfolios `z*` such that `(q, p, z*, x*)` is a Radner
equilibrium: each `z*ᵢ` finances the Arrow-Debreu transfers `p_s·(x*_{si} - ω_{si})`, and the
Arrow-Debreu consumptions are utility maximizing in the Radner budget sets (Exercise 19.E.3). -/
theorem proposition_19_E_2_i {ι : Type*} [Fintype ι] [Nonempty ι] (g : Fin L)
    {R : Matrix (Fin S) (Fin K) ℝ} (hR : IsComplete R) {U : ι → CVec S L → ℝ}
    {ω x : ι → CVec S L} {p : CVec S L} (hp : ∀ s, 0 < p s g) (h : IsADEqmU U ω x p) :
    ∃ z : ι → Fin K → ℝ, IsRadnerEqm g R U ω (fun k => ∑ s, p s g * R s k) p x z := by
  classical
  have hsurj := (isComplete_iff_surjective R).mp hR
  set m : ι → Fin S → ℝ := fun i s => p s ⬝ᵥ (x i s - ω i s) / p s g with hm
  choose z₀ hz₀ using fun i => hsurj (m i)
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  set W := ∑ i, z₀ i with hW
  have hsum_m : ∑ i, m i = 0 := by
    funext s
    simp only [hm, Finset.sum_apply, Pi.zero_apply, ← Finset.sum_div, ← dotProduct_sum,
      Finset.sum_sub_distrib]
    have : ∑ i, x i s = ∑ i, ω i s := by
      have := congrFun h.2 s; simpa [Finset.sum_apply] using this
    rw [this, sub_self, dotProduct_zero, zero_div]
  have hRW : R *ᵥ W = 0 := by
    rw [hW, mulVec_sum]; simp only [hz₀]; exact hsum_m
  set z : ι → Fin K → ℝ := fun i => z₀ i - if i = i₀ then W else 0 with hz
  have hRz : ∀ i, R *ᵥ z i = m i := by
    intro i
    simp only [hz, mulVec_sub]
    split_ifs
    · rw [hRW, sub_zero, hz₀]
    · rw [mulVec_zero, sub_zero, hz₀]
  have hzsum : ∑ i, z i = 0 := by
    simp only [hz, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [hW, sub_self]
  have hq := dot_eq_of_pricing (R := R) (ν := fun s => p s g) (q := fun k => ∑ s, p s g * R s k)
    (fun k => rfl)
  have hval : ∀ (i : ι) (x' : CVec S L) (z' : Fin K → ℝ),
      radnerFeasible g R (fun k => ∑ s, p s g * R s k) p (ω i) x' z' → x' ∈ adBudget p (ω i) := by
    rintro i x' z' ⟨hx', hqz, hs⟩
    refine ⟨hx', ?_⟩
    rw [hq] at hqz
    have h1 : ∑ s, (p s ⬝ᵥ x' s - p s ⬝ᵥ ω i s) ≤ ∑ s, p s g * (R *ᵥ z') s :=
      Finset.sum_le_sum fun s _ => by linarith [hs s]
    rw [Finset.sum_sub_distrib] at h1
    simp only [dotProduct] at hqz h1
    unfold cval
    simp only [dotProduct]
    linarith
  refine ⟨z, ⟨fun i => ⟨⟨(h.1 i).1.1, ?_, fun s => ?_⟩, fun x' z' hf => ?_⟩, fun k => ?_,
    h.2.le⟩⟩
  · rw [hq, hRz]
    have e1 : (fun s => p s g) ⬝ᵥ m i = ∑ s, p s ⬝ᵥ (x i s - ω i s) := by
      simp only [dotProduct, hm]
      exact Finset.sum_congr rfl fun s _ => by field_simp [(hp s).ne']
    have e2 : ∑ s, p s ⬝ᵥ (x i s - ω i s) = cval p (x i) - cval p (ω i) := by
      simp [cval, dotProduct_sub, Finset.sum_sub_distrib]
    rw [e1, e2]; linarith [(h.1 i).1.2]
  · rw [hRz, hm]
    simp only [mul_div_cancel₀ _ (hp s).ne', dotProduct_sub]
    linarith
  · exact (h.1 i).2 x' (hval i x' z' hf).1 (hval i x' z' hf).2
  · have := congrFun hzsum k
    simp only [Finset.sum_apply, Pi.zero_apply] at this
    rw [this]

/-- With a complete structure and strongly monotone preferences, the multipliers of Proposition
19.E.1 are strictly positive: `ν_s` is the price of the Arrow security of state `s`, which is
spanned. -/
theorem multipliers_pos_of_complete {R : Matrix (Fin S) (Fin K) ℝ} (hR : IsComplete R)
    {q : Fin K → ℝ} (haf : ArbitrageFree R q) {ν : Fin S → ℝ}
    (hq : ∀ k, q k = ∑ s, ν s * R s k) (s : Fin S) : 0 < ν s := by
  classical
  obtain ⟨zs, hzs⟩ := (isComplete_iff_surjective R).mp hR (Pi.single s 1)
  have hval : q ⬝ᵥ zs = ν s := by rw [dot_eq_of_pricing hq, hzs]; simp [dotProduct_single]
  by_contra hle
  push Not at hle
  refine haf ⟨zs, by rw [hval]; exact hle, fun s' => ?_, ?_⟩
  · rw [hzs]; simp [Pi.single_apply]; split_ifs <;> norm_num
  · rw [hzs]; intro h0; have := congrFun h0 s; simp at this

/-- **Proposition 19.E.2(ii)** (MWG, p. 705). Suppose the asset structure is complete, returns are
nonnegative and nonzero, preferences are strongly monotone and spot prices are strictly positive.
If `(q, p, z*, x*)` is a Radner equilibrium, there are multipliers `μ ≫ 0` such that `x*` and the
contingent prices `(μ₁ p₁, …, μ_S p_S)` form an Arrow-Debreu equilibrium. (`μ_s` is the value at
`t = 0` of a unit of the numeraire good in state `s`, divided by its spot price.) -/
theorem proposition_19_E_2_ii [NeZero S] [NeZero L] {ι : Type*} [Fintype ι] [Nonempty ι]
    (g : Fin L) {R : Matrix (Fin S) (Fin K) ℝ} (hR : IsComplete R) (hRn : NonnegNonzeroReturns R)
    {U : ι → CVec S L → ℝ} (hU : ∀ i, StronglyMonotoneC (U i)) {ω x : ι → CVec S L}
    {q : Fin K → ℝ} {p : CVec S L} (hp : ∀ s l, 0 < p s l) {z : ι → Fin K → ℝ}
    (h : IsRadnerEqm g R U ω q p x z) :
    ∃ μ : Fin S → ℝ, (∀ s, 0 < μ s) ∧ IsADEqmU U ω x (fun s => μ s • p s) := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have haf := radner_arbitrageFree g h i₀ (hU i₀)
  obtain ⟨ν, -, hq⟩ := lemma_19_E_1 hRn haf
  have hν := multipliers_pos_of_complete hR haf hq
  have hsurj := (isComplete_iff_surjective R).mp hR
  set μ : Fin S → ℝ := fun s => ν s / p s g with hμ
  have hμpos : ∀ s, 0 < μ s := fun s => div_pos (hν s) (hp s g)
  have hcv : ∀ y : CVec S L, cval (fun s => μ s • p s) y = ∑ s, μ s * (p s ⬝ᵥ y s) := by
    intro y; simp [cval, smul_dotProduct]
  have hequiv : ∀ (i : ι) (x' : CVec S L), (∃ z', radnerFeasible g R q p (ω i) x' z') ↔
      x' ∈ adBudget (fun s => μ s • p s) (ω i) := by
    intro i x'
    constructor
    · rintro ⟨z', hx', hqz, hs⟩
      refine ⟨hx', ?_⟩
      rw [hcv, hcv]
      have h1 : ∀ s, μ s * (p s ⬝ᵥ x' s) ≤ μ s * (p s ⬝ᵥ ω i s) + ν s * (R *ᵥ z') s := by
        intro s
        have := mul_le_mul_of_nonneg_left (hs s) (hμpos s).le
        rw [mul_add, ← mul_assoc, hμ, div_mul_cancel₀ _ (hp s g).ne'] at this
        exact this
      have h2 := Finset.sum_le_sum fun s (_ : s ∈ Finset.univ) => h1 s
      rw [Finset.sum_add_distrib] at h2
      rw [dot_eq_of_pricing hq] at hqz
      simp only [dotProduct] at hqz
      linarith
    · rintro ⟨hx', hb⟩
      obtain ⟨z', hz'⟩ := hsurj fun s => p s ⬝ᵥ (x' s - ω i s) / p s g
      refine ⟨z', hx', ?_, fun s => ?_⟩
      · rw [dot_eq_of_pricing hq, hz']
        rw [hcv, hcv] at hb
        have e : ν ⬝ᵥ (fun s => p s ⬝ᵥ (x' s - ω i s) / p s g) =
            ∑ s, μ s * (p s ⬝ᵥ x' s) - ∑ s, μ s * (p s ⬝ᵥ ω i s) := by
          simp only [dotProduct_sub]
          rw [dotProduct, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun s _ => by rw [hμ]; field_simp
        rw [e]; linarith
      · rw [hz']; simp only [mul_div_cancel₀ _ (hp s g).ne', dotProduct_sub]; linarith
  have hopt : ∀ i, (NonnegC (x i) ∧ cval (fun s => μ s • p s) (x i) ≤
      cval (fun s => μ s • p s) (ω i)) ∧ ∀ x', NonnegC x' →
        cval (fun s => μ s • p s) x' ≤ cval (fun s => μ s • p s) (ω i) → U i x' ≤ U i (x i) := by
    intro i
    refine ⟨(hequiv i (x i)).mp ⟨z i, (h.1 i).1⟩, fun x' hx' hb => ?_⟩
    obtain ⟨z', hz'⟩ := (hequiv i x').mpr ⟨hx', hb⟩
    exact (h.1 i).2 x' z' hz'
  have hbind : ∀ i, cval (fun s => μ s • p s) (x i) = cval (fun s => μ s • p s) (ω i) := by
    intro i
    refine le_antisymm (hopt i).1.2 (not_lt.mp fun hlt => ?_)
    obtain ⟨x', hle', hne, hc⟩ := exists_larger_cheap (fun s => μ s • p s) (x i)
      (sub_pos.mpr hlt)
    have hx := (hopt i).1.1
    have := (hopt i).2 x' (fun s l => (hx s l).trans (hle' s l)) (by linarith)
    linarith [hU i _ _ hx hle' hne]
  refine ⟨μ, hμpos, hopt, clear_eq_of_binding (fun s l => ?_) h.2.2 hbind⟩
  simp only [Pi.smul_apply, smul_eq_mul]
  exact mul_pos (hμpos s) (hp s l)

/-- **p. 703**. With `rank R = S` the multipliers are unique. -/
theorem multipliers_unique {R : Matrix (Fin S) (Fin K) ℝ} (hR : IsComplete R) {μ μ' : Fin S → ℝ}
    (h : ∀ k, ∑ s, μ s * R s k = ∑ s, μ' s * R s k) : μ = μ' := by
  classical
  funext s
  obtain ⟨zs, hzs⟩ := (isComplete_iff_surjective R).mp hR (Pi.single s 1)
  have h1 := dot_eq_of_pricing (q := fun k => ∑ s, μ s * R s k) (fun k => rfl) zs
  have h2 := dot_eq_of_pricing (q := fun k => ∑ s, μ s * R s k) (ν := μ') (fun k => h k) zs
  rw [hzs] at h1 h2
  simp only [dotProduct_single, mul_one] at h1 h2
  rw [← h1, ← h2]

/-- **p. 707**. `μ_s` is the price of the Arrow security of state `s` (when it is spanned). -/
theorem arrow_price {R : Matrix (Fin S) (Fin K) ℝ} {μ : Fin S → ℝ} {q : Fin K → ℝ}
    (hq : ∀ k, q k = ∑ s, μ s * R s k) {s : Fin S} {z : Fin K → ℝ}
    (hz : R *ᵥ z = Pi.single s 1) : q ⬝ᵥ z = μ s := by
  classical
  rw [dot_eq_of_pricing hq, hz, dotProduct_single, mul_one]

/-! ## Proposition 19.E.3 and redundant assets -/

/-- With strongly monotone preferences and nonnegative nonzero returns, the date-0 budget
constraint binds at a Radner equilibrium. -/
theorem radner_date0_binds {ι : Type*} [Fintype ι] (g : Fin L) {R : Matrix (Fin S) (Fin K) ℝ}
    (hRn : NonnegNonzeroReturns R) {U : ι → CVec S L → ℝ} {ω x : ι → CVec S L} {q : Fin K → ℝ}
    {p : CVec S L} {z : ι → Fin K → ℝ} (h : IsRadnerEqm g R U ω q p x z) (i : ι)
    (hU : StronglyMonotoneC (U i)) : q ⬝ᵥ z i = 0 := by
  classical
  have hqpos := (radner_arbitrageFree g h i hU).pos hRn
  obtain ⟨⟨hx, hqz, hsp⟩, hopt⟩ := h.1 i
  refine le_antisymm hqz (not_lt.mp fun hlt => ?_)
  obtain ⟨k₀⟩ : Nonempty (Fin K) := by
    by_contra hK
    rw [not_nonempty_iff] at hK
    simp [dotProduct] at hlt
  set ε := -(q ⬝ᵥ z i) / q k₀ with hε
  have hεpos : 0 < ε := div_pos (by linarith) (hqpos k₀)
  set δ : CVec S L := fun s l => if l = g then ε * R s k₀ else 0 with hδ
  have hle : x i ≤ x i + δ := fun s l => by
    simp only [Pi.add_apply, hδ]; split_ifs
    · nlinarith [hRn.1 s k₀]
    · linarith
  have hne : x i ≠ x i + δ := by
    intro h0
    obtain ⟨s, hs⟩ := hRn.2 k₀
    have h1 := congrFun (congrFun h0 s) g
    simp only [Pi.add_apply, hδ, ite_true] at h1
    have : ε * R s k₀ = 0 := by linarith
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd h' hεpos.ne'
    · exact hs h'
  have hfeas : radnerFeasible g R q p (ω i) (x i + δ) (z i + ε • Pi.single k₀ 1) := by
    refine ⟨fun s l => (hx s l).trans (hle s l), ?_, fun s => ?_⟩
    · rw [dotProduct_add, dotProduct_smul, dotProduct_single, smul_eq_mul, mul_one, hε]
      field_simp [(hqpos k₀).ne']
      linarith
    · have hd : p s ⬝ᵥ δ s = p s g * (ε * R s k₀) := by simp [hδ, dotProduct]
      rw [Pi.add_apply, dotProduct_add, hd, mulVec_add, mulVec_smul, Pi.add_apply,
        Pi.smul_apply, mulVec_single, smul_eq_mul]
      linarith [hsp s]
  linarith [hopt _ _ hfeas, hU _ _ hx hle hne]

/-- **Proposition 19.E.3** (MWG, p. 706). Let `(q, p, z*, x*)` be a Radner equilibrium for the
return matrix `R` (nonnegative nonzero returns; strongly monotone preferences, as used in the
book's proof), and let `R'` be an `S × K'` return matrix with `Range R' = Range R`. Then `x*` is
also a Radner equilibrium allocation for `R'`, with asset prices `q' = μ·R'` and the same spot
prices. -/
theorem proposition_19_E_3 {ι : Type*} [Fintype ι] [Nonempty ι] (g : Fin L) {K' : ℕ}
    {R : Matrix (Fin S) (Fin K) ℝ} (hRn : NonnegNonzeroReturns R)
    {R' : Matrix (Fin S) (Fin K') ℝ} (hrange : ∀ v, (∃ z, R *ᵥ z = v) ↔ ∃ z', R' *ᵥ z' = v)
    {U : ι → CVec S L → ℝ} (hU : ∀ i, StronglyMonotoneC (U i)) {ω x : ι → CVec S L}
    {q : Fin K → ℝ} {p : CVec S L} {z : ι → Fin K → ℝ} (h : IsRadnerEqm g R U ω q p x z) :
    ∃ (q' : Fin K' → ℝ) (z' : ι → Fin K' → ℝ), IsRadnerEqm g R' U ω q' p x z' := by
  classical
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have haf := radner_arbitrageFree g h i₀ (hU i₀)
  have hqpos := haf.pos hRn
  obtain ⟨μ, -, hq⟩ := lemma_19_E_1 hRn haf
  set q' : Fin K' → ℝ := fun k => ∑ s, μ s * R' s k with hq'
  have hdot := dot_eq_of_pricing hq
  have hdot' := dot_eq_of_pricing (R := R') (q := q') (fun k => rfl)
  -- the budget sets coincide (19.E.1)
  have hequiv : ∀ (i : ι) (x' : CVec S L), (∃ z', radnerFeasible g R' q' p (ω i) x' z') →
      ∃ z'', radnerFeasible g R q p (ω i) x' z'' := by
    rintro i x' ⟨z', hx', hqz, hs⟩
    obtain ⟨z'', hz''⟩ := (hrange (R' *ᵥ z')).mpr ⟨z', rfl⟩
    refine ⟨z'', hx', ?_, fun s => ?_⟩
    · rw [hdot, hz'', ← hdot']; exact hqz
    · rw [hz'']; exact hs s
  -- the date-0 budgets bind and the asset markets clear exactly
  have hbind : ∀ i, q ⬝ᵥ z i = 0 := fun i => radner_date0_binds g hRn h i (hU i)
  have hzsum : ∑ i, z i = 0 := by
    have hq0 : q ⬝ᵥ ∑ i, z i = 0 := by rw [dotProduct_sum]; simp [hbind]
    have hnp : ∀ k, q k * (∑ i, z i) k ≤ 0 := fun k =>
      mul_nonpos_of_nonneg_of_nonpos (hqpos k).le (by simpa [Finset.sum_apply] using h.2.1 k)
    funext k
    have := (Finset.sum_eq_zero_iff_of_nonpos fun k _ => hnp k).mp hq0 k (Finset.mem_univ _)
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd h' (hqpos k).ne'
    · exact h'
  choose z₀ hz₀ using fun i => (hrange (R *ᵥ z i)).mp ⟨z i, rfl⟩
  set W := ∑ i, z₀ i with hW
  have hRW : R' *ᵥ W = 0 := by
    rw [hW, mulVec_sum]; simp only [hz₀]; rw [← mulVec_sum, hzsum, mulVec_zero]
  set z' : ι → Fin K' → ℝ := fun i => z₀ i - if i = i₀ then W else 0 with hz'
  have hRz' : ∀ i, R' *ᵥ z' i = R *ᵥ z i := by
    intro i
    simp only [hz', mulVec_sub]
    split_ifs
    · rw [hRW, sub_zero, hz₀]
    · rw [mulVec_zero, sub_zero, hz₀]
  have hz'sum : ∑ i, z' i = 0 := by
    simp only [hz', Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [hW, sub_self]
  refine ⟨q', z', ⟨fun i => ⟨⟨(h.1 i).1.1, ?_, fun s => ?_⟩, fun x' z'' hf => ?_⟩,
    fun k => ?_, h.2.2⟩⟩
  · rw [hdot', hRz', ← hdot]; exact (h.1 i).1.2.1
  · rw [hRz']; exact (h.1 i).1.2.2 s
  · obtain ⟨w, hw⟩ := hequiv i x' ⟨z'', hf⟩
    exact (h.1 i).2 x' w hw
  · have := congrFun hz'sum k
    simp only [Finset.sum_apply, Pi.zero_apply] at this
    rw [this]

/-- The asset structure `R` with one more asset `r` appended. -/
def appendAsset (R : Matrix (Fin S) (Fin K) ℝ) (r : ReturnVector S) :
    Matrix (Fin S) (Fin (K + 1)) ℝ :=
  Matrix.of fun s k => Fin.lastCases (r s) (fun k => R s k) k

/-- **p. 706**. A redundant asset (one whose return vector is a combination of the others) does
not change the space `Range R` of spannable wealth transfers; by Proposition 19.E.3 its addition
or deletion does not change the Radner equilibrium allocations. -/
theorem redundant_range {R : Matrix (Fin S) (Fin K) ℝ} {r : ReturnVector S}
    (hr : ∃ a, R *ᵥ a = r) (v : Fin S → ℝ) :
    (∃ z, R *ᵥ z = v) ↔ ∃ z', appendAsset R r *ᵥ z' = v := by
  obtain ⟨a, ha⟩ := hr
  have hmv : ∀ z' : Fin (K + 1) → ℝ, appendAsset R r *ᵥ z' =
      R *ᵥ (fun k => z' k.castSucc) + z' (Fin.last K) • r := by
    intro z'
    funext s
    simp [appendAsset, mulVec, dotProduct, Fin.sum_univ_castSucc, mul_comm]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨Fin.snoc z 0, by rw [hmv]; simp⟩
  · rintro ⟨z', rfl⟩
    exact ⟨(fun k => z' k.castSucc) + z' (Fin.last K) • a, by
      rw [hmv, mulVec_add, mulVec_smul, ha]⟩

/-- **Exercise 19.E.4** (MWG, p. 706). Pricing by arbitrage: if `r₃ = α₁ r₁ + α₂ r₂` and the asset
prices are given by multipliers (`q_k = ∑_s μ_s r_{sk}`, Proposition 19.E.1), then
`q₃ = α₁ q₁ + α₂ q₂`. -/
theorem exercise_19_E_4 {R : Matrix (Fin S) (Fin K) ℝ} {μ : Fin S → ℝ} {q : Fin K → ℝ}
    (hq : ∀ k, q k = ∑ s, μ s * R s k) {k₁ k₂ k₃ : Fin K} {α₁ α₂ : ℝ}
    (hr : ∀ s, R s k₃ = α₁ * R s k₁ + α₂ * R s k₂) : q k₃ = α₁ * q k₁ + α₂ * q k₂ := by
  rw [hq, hq, hq, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun s _ => by rw [hr]; ring

/-- **Exercise 19.E.4** (MWG, p. 706), at a Radner equilibrium: with unlimited short sales,
nonnegative nonzero returns and some strongly monotone consumer, `r₃ = α₁ r₁ + α₂ r₂` forces
`q₃ = α₁ q₁ + α₂ q₂`. -/
theorem exercise_19_E_4_eqm {ι : Type*} [Fintype ι] (g : Fin L) {R : Matrix (Fin S) (Fin K) ℝ}
    (hRn : NonnegNonzeroReturns R) {U : ι → CVec S L → ℝ} {ω x : ι → CVec S L} {q : Fin K → ℝ}
    {p : CVec S L} {z : ι → Fin K → ℝ} (h : IsRadnerEqm g R U ω q p x z) (i : ι)
    (hU : StronglyMonotoneC (U i)) {k₁ k₂ k₃ : Fin K} {α₁ α₂ : ℝ}
    (hr : ∀ s, R s k₃ = α₁ * R s k₁ + α₂ * R s k₂) : q k₃ = α₁ * q k₁ + α₂ * q k₂ := by
  obtain ⟨μ, -, hq⟩ := proposition_19_E_1 g hRn h i hU
  exact exercise_19_E_4 hq hr

/-! ## Example 19.E.6: pricing an option -/

/-- The two assets of Example 19.E.6: `r₁ = (1, 1)` and `r₂ = (3 + α, 1 - α)`. -/
def r2_19E6 (α : ℝ) : ReturnVector 2 := ![3 + α, 1 - α]

/-- **Example 19.E.6** (MWG, p. 707). For `α > 0` and `c ∈ (1, 3)`, the call option on `r₂` with
strike `c` returns `(3 + α - c, 0)`, and
`r₂(c) = (3 + α - c)/(2 + 2α) · r₂ - (1 - α)(3 + α - c)/(2 + 2α) · r₁`. -/
theorem example_19_E_6_returns {α c : ℝ} (hα : 0 < α) (hc1 : 1 < c) (hc3 : c < 3) :
    callOption (r2_19E6 α) c = ![3 + α - c, 0] ∧
      ∀ s, callOption (r2_19E6 α) c s = (3 + α - c) / (2 + 2 * α) * r2_19E6 α s -
        (1 - α) * (3 + α - c) / (2 + 2 * α) * 1 := by
  have h1 : callOption (r2_19E6 α) c = ![3 + α - c, 0] := by
    funext s
    fin_cases s
    · simp [callOption, r2_19E6]; linarith
    · simp [callOption, r2_19E6]; linarith
  refine ⟨h1, fun s => ?_⟩
  rw [h1]
  have hpos : (2 + 2 * α) ≠ 0 := by positivity
  fin_cases s <;> simp [r2_19E6] <;> field_simp <;> ring

/-- **Example 19.E.6** (MWG, p. 707). The multipliers are determined by `(1, q₂) = μ·R`:
`μ₁ = (q₂ - (1 - α))/(2 + 2α)`, `μ₂ = 1 - μ₁`, and the arbitrage price of the option is (19.E.2):
`q₂(c) = μ·r₂(c) = (3 + α - c)/(2 + 2α) · (q₂ - (1 - α))`. -/
theorem example_19_E_6_price {α c q₂ : ℝ} (hα : 0 < α) (hc1 : 1 < c) (hc3 : c < 3)
    {μ : Fin 2 → ℝ} (h1 : μ 0 + μ 1 = 1) (h2 : μ 0 * (3 + α) + μ 1 * (1 - α) = q₂) :
    μ 0 = (q₂ - (1 - α)) / (2 + 2 * α) ∧ μ 1 = 1 - μ 0 ∧
      μ ⬝ᵥ callOption (r2_19E6 α) c = (3 + α - c) / (2 + 2 * α) * (q₂ - (1 - α)) := by
  have hpos : (2 + 2 * α) ≠ 0 := by positivity
  have hμ0 : μ 0 = (q₂ - (1 - α)) / (2 + 2 * α) := by
    field_simp; nlinarith
  refine ⟨hμ0, by linarith, ?_⟩
  rw [(example_19_E_6_returns hα hc1 hc3).1]
  simp [dotProduct, Fin.sum_univ_two, hμ0]
  ring

/-- **Example 19.E.6** (MWG, p. 707). If the prices of `r₁` and `r₂` are arbitrage free
(`μ ≥ 0`), then `3 + α ≥ q₂ ≥ 1 - α`; hence `q₂(c) ≥ 0`, `q₂(c)` is decreasing in `c` and
increasing in `q₂`. -/
theorem example_19_E_6_bounds {α q₂ : ℝ} (hα : 0 < α) {μ : Fin 2 → ℝ} (hμ : ∀ s, 0 ≤ μ s)
    (h1 : μ 0 + μ 1 = 1) (h2 : μ 0 * (3 + α) + μ 1 * (1 - α) = q₂) :
    1 - α ≤ q₂ ∧ q₂ ≤ 3 + α ∧
      (∀ c, c < 3 + α → 0 ≤ (3 + α - c) / (2 + 2 * α) * (q₂ - (1 - α))) ∧
      (∀ c c', c ≤ c' → (3 + α - c') / (2 + 2 * α) * (q₂ - (1 - α)) ≤
        (3 + α - c) / (2 + 2 * α) * (q₂ - (1 - α))) ∧
      ∀ c q₂', c ≤ 3 + α → q₂ ≤ q₂' → (3 + α - c) / (2 + 2 * α) * (q₂ - (1 - α)) ≤
        (3 + α - c) / (2 + 2 * α) * (q₂' - (1 - α)) := by
  have hlo : 1 - α ≤ q₂ := by nlinarith [hμ 0, hμ 1]
  have hhi : q₂ ≤ 3 + α := by nlinarith [hμ 0, hμ 1]
  have hd : 0 < 2 + 2 * α := by positivity
  refine ⟨hlo, hhi, fun c hc => ?_, fun c c' hcc => ?_, fun c q₂' hc hq => ?_⟩
  · exact mul_nonneg (div_nonneg (by linarith) hd.le) (by linarith)
  · apply mul_le_mul_of_nonneg_right _ (by linarith)
    exact div_le_div_of_nonneg_right (by linarith) hd.le
  · exact mul_le_mul_of_nonneg_left (by linarith) (div_nonneg (by linarith) hd.le)

/-- The option price `q₂(c)` of (19.E.2) as a function of the dispersion `α`. -/
noncomputable def optionPrice19E6 (α c q₂ : ℝ) : ℝ := (3 + α - c) / (2 + 2 * α) * (q₂ - (1 - α))

/-- **Example 19.E.6** (MWG, p. 707), the dispersion claim, proved directly: if `q₂` stays constant
and `α' > α`, the option becomes (weakly) more valuable: `q'₂(c) ≥ q₂(c)` (for `c ∈ (1, 3)` and
arbitrage-free `q₂`, i.e. `1 - α ≤ q₂ ≤ 3 + α`). -/
theorem example_19_E_6_dispersion {α α' c q₂ : ℝ} (hα : 0 < α) (hαα : α ≤ α') (hc1 : 1 < c)
    (hc3 : c < 3) (hlo : 1 - α ≤ q₂) (hhi : q₂ ≤ 3 + α) :
    optionPrice19E6 α c q₂ ≤ optionPrice19E6 α' c q₂ := by
  unfold optionPrice19E6
  have h1 : 0 < 2 + 2 * α := by positivity
  have h2 : 0 < 2 + 2 * α' := by linarith
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff₀ h1 h2]
  -- `(A+a')(Q+a')(1+a) - (A+a)(Q+a)(1+a') = (a'-a)((1+a)(1+a') - (1-A)(1-Q))`
  have key : (3 + α' - c) * (q₂ - (1 - α')) * (2 + 2 * α) -
      (3 + α - c) * (q₂ - (1 - α)) * (2 + 2 * α') =
      2 * (α' - α) * ((1 + α) * (1 + α') - (c - 2) * (2 - q₂)) := by ring
  have hb : (c - 2) * (2 - q₂) ≤ (1 + α) * (1 + α') := by
    have hc : |c - 2| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    have hq : |2 - q₂| ≤ 1 + α := abs_le.mpr ⟨by linarith, by linarith⟩
    calc (c - 2) * (2 - q₂) ≤ |c - 2| * |2 - q₂| := by
          rw [← abs_mul]; exact le_abs_self _
      _ ≤ 1 * (1 + α) := mul_le_mul hc hq (abs_nonneg _) zero_le_one
      _ ≤ (1 + α) * (1 + α') := by nlinarith
  nlinarith [key, hb, mul_nonneg (sub_nonneg.mpr hαα) (sub_nonneg.mpr hb)]

/-- **Example 19.E.6** (MWG, p. 707), correction 5: the printed argument claims
`q'₂(c) = q₃ + q₂(c)` with `q₃` the arbitrage price of `r₃ = r'₂(c) - r₂(c)`. With `α = 1/2`,
`α' = 1`, `q₂ = 3`, `c = 2`, this fails whether `q₃` is priced with the multipliers `μ` of the
original economy or `μ'` of the new one: `q₂(c) = 5/4`, `q'₂(c) = 3/2`, while `μ·r₃ = 5/12` and
`μ'·r₃ = 3/8`. -/
theorem example_19_E_6_identity_fails :
    let μ : Fin 2 → ℝ := ![5 / 6, 1 / 6]
    let μ' : Fin 2 → ℝ := ![3 / 4, 1 / 4]
    let r₃ := callOption (r2_19E6 1) 2 - callOption (r2_19E6 (1 / 2)) 2
    μ 0 + μ 1 = 1 ∧ μ 0 * (3 + 1 / 2) + μ 1 * (1 - 1 / 2) = 3 ∧
      μ' 0 + μ' 1 = 1 ∧ μ' 0 * (3 + 1) + μ' 1 * (1 - 1) = 3 ∧
      optionPrice19E6 (1 / 2) 2 3 = 5 / 4 ∧ optionPrice19E6 1 2 3 = 3 / 2 ∧
      μ ⬝ᵥ r₃ = 5 / 12 ∧ μ' ⬝ᵥ r₃ = 3 / 8 ∧
      optionPrice19E6 1 2 3 ≠ μ ⬝ᵥ r₃ + optionPrice19E6 (1 / 2) 2 3 ∧
      optionPrice19E6 1 2 3 ≠ μ' ⬝ᵥ r₃ + optionPrice19E6 (1 / 2) 2 3 := by
  intro μ μ' r₃
  have hr : r₃ = ![1 / 2, 0] := by
    funext s; fin_cases s <;> simp [r₃, callOption, r2_19E6] <;> norm_num
  simp only [hr, optionPrice19E6, μ, μ', dotProduct, Fin.sum_univ_two]
  norm_num

/-! ## Exercise 19.E.6 -/

/-- The primary assets of Exercise 19.E.6: `r₁ = (64, 16, 4)`, `r₂ = (0, 0, 1)`. -/
def r1_19E6x : ReturnVector 3 := ![64, 16, 4]

/-- `r₂ = (0, 0, 1)`. -/
def r2_19E6x : ReturnVector 3 := ![0, 0, 1]

/-- State prices consistent with `q₁ = 32`, `q₂ = 1`. -/
def ConsistentStatePrices (μ : Fin 3 → ℝ) : Prop :=
  μ ⬝ᵥ r1_19E6x = 32 ∧ μ ⬝ᵥ r2_19E6x = 1

/-- **Exercise 19.E.6(a)** (MWG, p. 727). "The right to buy one unit of asset 1 at 75% of its spot
value": returns `max{0, r₁ - 0.75 r₁} = (16, 4, 1) = r₁/4`, price `q₁/4 = 8`. -/
theorem exercise_19_E_6a :
    (fun s => max 0 (r1_19E6x s - 0.75 * r1_19E6x s)) = ![16, 4, 1] ∧
      ∀ μ, ConsistentStatePrices μ →
        μ ⬝ᵥ (fun s => max 0 (r1_19E6x s - 0.75 * r1_19E6x s)) = 8 := by
  have h : (fun s => max 0 (r1_19E6x s - 0.75 * r1_19E6x s)) = ![16, 4, 1] := by
    funext s; fin_cases s <;> simp [r1_19E6x] <;> norm_num
  refine ⟨h, fun μ ⟨h1, _⟩ => ?_⟩
  rw [h]
  simp [r1_19E6x, dotProduct, Fin.sum_univ_three] at h1 ⊢
  linarith

/-- **Exercise 19.E.6(b)** (MWG, p. 727). Exercisable only if the spot value is at least `10`:
returns `(16, 4, 0) = r₁/4 - r₂`, price `8 - 1 = 7`. -/
theorem exercise_19_E_6b :
    (fun s => if 10 ≤ r1_19E6x s then max 0 (r1_19E6x s - 0.75 * r1_19E6x s) else 0) =
        ![16, 4, 0] ∧
      ∀ μ, ConsistentStatePrices μ → μ ⬝ᵥ
        (fun s => if 10 ≤ r1_19E6x s then max 0 (r1_19E6x s - 0.75 * r1_19E6x s) else 0) = 7 := by
  have h : (fun s => if 10 ≤ r1_19E6x s then max 0 (r1_19E6x s - 0.75 * r1_19E6x s) else 0) =
      ![16, 4, 0] := by
    funext s; fin_cases s <;> simp [r1_19E6x] <;> norm_num
  refine ⟨h, fun μ ⟨h1, h2⟩ => ?_⟩
  rw [h]
  simp [r1_19E6x, r2_19E6x, dotProduct, Fin.sum_univ_three] at h1 h2 ⊢
  linarith

/-- **Exercise 19.E.6(c)** (MWG, p. 727). With "at least 19" the returns are `(16, 0, 0)`, which is
not a combination of `r₁` and `r₂`; it cannot be priced by arbitrage: two nonnegative state-price
vectors consistent with `q₁ = 32`, `q₂ = 1` give it the prices `7` and `0`. -/
theorem exercise_19_E_6c :
    (fun s => if 19 ≤ r1_19E6x s then max 0 (r1_19E6x s - 0.75 * r1_19E6x s) else 0) =
        ![16, 0, 0] ∧
      (¬ ∃ a b : ℝ, ∀ s, ![(16 : ℝ), 0, 0] s = a * r1_19E6x s + b * r2_19E6x s) ∧
      ConsistentStatePrices ![7 / 16, 0, 1] ∧ ConsistentStatePrices ![0, 7 / 4, 1] ∧
      ![(7 : ℝ) / 16, 0, 1] ⬝ᵥ ![16, 0, 0] = 7 ∧ ![(0 : ℝ), 7 / 4, 1] ⬝ᵥ ![16, 0, 0] = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · funext s; fin_cases s <;> simp [r1_19E6x] <;> norm_num
  · rintro ⟨a, b, h⟩
    have h0 := h 0; have h1 := h 1
    simp [r1_19E6x, r2_19E6x] at h0 h1
    linarith
  all_goals simp [ConsistentStatePrices, r1_19E6x, r2_19E6x, dotProduct, Fin.sum_univ_three]
  all_goals norm_num

/-- **Exercise 19.E.6(d)** (MWG, p. 727), correction 6. Adding a riskless asset `(1, 1, 1)` makes
the structure complete, but at the price `1` the three prices admit an arbitrage (buy the riskless
asset, sell `r₂`: cost `0`, returns `(1, 1, 0)`); the unique linear state prices are
`(7/12, -7/12, 1)`, not nonnegative. So the prices cannot arise at an equilibrium with strongly
monotone preferences; linear pricing would give `(16, 0, 0)` the value `28/3`. -/
theorem exercise_19_E_6d :
    let R : Matrix (Fin 3) (Fin 3) ℝ := returnMatrix ![r1_19E6x, r2_19E6x, fun _ => 1]
    IsComplete R ∧ ¬ ArbitrageFree R ![32, 1, 1] ∧
      (∀ μ : Fin 3 → ℝ, (∀ k, ![(32 : ℝ), 1, 1] k = ∑ s, μ s * R s k) → μ = ![7 / 12, -7 / 12, 1]) ∧
      ![(7 : ℝ) / 12, -7 / 12, 1] ⬝ᵥ ![16, 0, 0] = 28 / 3 := by
  intro R
  have hR : R = !![64, 0, 1; 16, 0, 1; 4, 1, 1] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [R, returnMatrix, r1_19E6x, r2_19E6x]
  refine ⟨?_, ?_, fun μ hμ => ?_, ?_⟩
  · unfold IsComplete
    rw [hR, Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).mpr ?_), Fintype.card_fin]
    rw [Matrix.det_fin_three]; norm_num
  · intro h
    apply h
    refine ⟨![0, -1, 1], by simp [dotProduct, Fin.sum_univ_three], fun s => ?_, fun h0 => ?_⟩
    · rw [hR]; fin_cases s <;> simp [mulVec, dotProduct, Fin.sum_univ_three]
    · have := congrFun h0 0
      rw [hR] at this
      simp [mulVec, dotProduct, Fin.sum_univ_three] at this
  · have h0 := hμ 0; have h1 := hμ 1; have h2 := hμ 2
    rw [hR] at h0 h1 h2
    simp [Fin.sum_univ_three] at h0 h1 h2
    funext s
    fin_cases s <;> simp <;> linarith
  · simp [dotProduct, Fin.sum_univ_three]; norm_num

/-- **Exercise 19.E.6(e)** (MWG, pp. 727-728). At the holder's choice, `1` dollar or the right of
(a): returns `max{1, r₁/4} = (16, 4, 1)`, price `8`. -/
theorem exercise_19_E_6e :
    (fun s => max 1 (max 0 (r1_19E6x s - 0.75 * r1_19E6x s))) = ![16, 4, 1] ∧
      ∀ μ, ConsistentStatePrices μ →
        μ ⬝ᵥ (fun s => max 1 (max 0 (r1_19E6x s - 0.75 * r1_19E6x s))) = 8 := by
  have h : (fun s => max 1 (max 0 (r1_19E6x s - 0.75 * r1_19E6x s))) = ![16, 4, 1] := by
    funext s; fin_cases s <;> simp [r1_19E6x] <;> norm_num
  refine ⟨h, fun μ hμ => ?_⟩
  rw [h, ← (exercise_19_E_6a.1)]
  exact exercise_19_E_6a.2 μ hμ

/-- **Exercise 19.E.6(f)** (MWG, p. 728). As in (e), with the right exercisable only if the spot
value is at least `10`: returns `(16, 4, 1)` again (in state 3 the dollar is chosen), price `8`. -/
theorem exercise_19_E_6f :
    (fun s => if 10 ≤ r1_19E6x s then max 1 (max 0 (r1_19E6x s - 0.75 * r1_19E6x s)) else 1) =
        ![16, 4, 1] ∧
      ∀ μ, ConsistentStatePrices μ → μ ⬝ᵥ
        (fun s => if 10 ≤ r1_19E6x s then max 1 (max 0 (r1_19E6x s - 0.75 * r1_19E6x s))
          else 1) = 8 := by
  have h : (fun s => if 10 ≤ r1_19E6x s then max 1 (max 0 (r1_19E6x s - 0.75 * r1_19E6x s))
      else 1) = ![16, 4, 1] := by
    funext s; fin_cases s <;> simp [r1_19E6x] <;> norm_num
  refine ⟨h, fun μ hμ => ?_⟩
  rw [h, ← (exercise_19_E_6a.1)]
  exact exercise_19_E_6a.2 μ hμ

end MWG.EquilibriumUncertainty
