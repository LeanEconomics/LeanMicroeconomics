/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPositiveEquilibriumTheory.SMDRationalization

/-!
# The Sonnenschein-Mantel-Debreu theorem for two goods (MWG pp. 602-603)

* The domain `P_ε = {p ∈ ℝ^L_+ : pₗ/pₗ' ≥ ε for all ℓ, ℓ'}` (`pEps`); its prices are `≫ 0`.
* From a utility `u` on excess demands with unique maximizer `ζ` on `{p·z ≤ 0}`, the consumer
  with consumption set `ℝ^L_+`, endowment `ω` and utility `x ↦ u(x - ω)` demands exactly
  `ω + ζ` at every positive multiple of `p` (`smd_demand_eq`), and inherits continuity, strong
  monotonicity and convexity (`smd_consumer_props`).
* `smd_curve_rationalize`: the rationalization lemma for offer curves parametrized by one real
  number (the two-good case).
* **Proposition 17.E.3, `L = 2`** (the book's proof): with `|z₁(p)| < r` on `P_ε`, the functions
  `z¹₁ = z₁/2 + r`, `z¹₂ = -(p₁/p₂) z¹₁` and `z²₁ = z₁/2 - r`, `z²₂ = -(p₁/p₂) z²₁` are
  continuous, homogeneous of degree zero, satisfy Walras' law, never vanish, and sum to `z`
  (`smd2_decomposition`). Each is the excess demand of a consumer with continuous, convex,
  strongly monotone preferences and endowment `ωᵢ ≫ 0` with `ωᵢ + zⁱ(p) ≫ 0`
  (`proposition_17_E_3_two`).
-/

namespace MWG.PositiveEquilibriumTheory

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.GeneralEquilibriumExamples Filter Topology

variable {L : ℕ}

/-- **Proposition 17.E.3** (MWG, p. 602). The price domain
`P_ε = {p ∈ ℝ^L_+ : pₗ/pₗ' ≥ ε for every ℓ and ℓ'}`. -/
def pEps (L : ℕ) (ε : ℝ) : Set (Fin L → ℝ) := {p | (∀ l, 0 ≤ p l) ∧ ∀ l l', ε ≤ p l / p l'}

/-- Prices in `P_ε` (`ε > 0`) are strictly positive. -/
theorem pEps_pos {ε : ℝ} (hε : 0 < ε) {p : Fin L → ℝ} (hp : p ∈ pEps L ε) (l : Fin L) :
    0 < p l := by
  rcases (hp.1 l).lt_or_eq with h | h
  · exact h
  · have := hp.2 l l
    rw [← h, zero_div] at this
    linarith

/-- `P_ε` is a cone. -/
theorem pEps_smul {ε : ℝ} {p : Fin L → ℝ} (hp : p ∈ pEps L ε) {α : ℝ} (hα : 0 < α) :
    α • p ∈ pEps L ε := by
  refine ⟨fun l => by simpa using mul_nonneg hα.le (hp.1 l), fun l l' => ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [mul_div_mul_left _ _ hα.ne']
  exact hp.2 l l'

/-- The consumer built from a utility `u` on excess demands and an endowment `ω`: if `ζ` is
the unique maximizer of `u` on `{z : p·z ≤ 0}`, `p·ζ = 0` and `ω + ζ ≥ 0`, then at every
positive multiple `t p` the demand of `x ↦ u(x - ω)` on `ℝ^L_+` with wealth `t p·ω` is `{ω + ζ}`. -/
theorem smd_demand_eq {u : (Fin L → ℝ) → ℝ} {ω p ζp : Fin L → ℝ} {t : ℝ} (ht : 0 < t)
    (hmax : ∀ z, p ⬝ᵥ z ≤ 0 → u z ≤ u ζp ∧ (u ζp ≤ u z → z = ζp)) (hpz : p ⬝ᵥ ζp = 0)
    (hX : ω + ζp ∈ nonnegOrthant L) :
    walrasianDemandOn (nonnegOrthant L) (fun x => u (x - ω)) (t • p) ((t • p) ⬝ᵥ ω) =
      {ω + ζp} := by
  have hb : ∀ x, (t • p) ⬝ᵥ x ≤ (t • p) ⬝ᵥ ω → p ⬝ᵥ (x - ω) ≤ 0 := by
    intro x hx
    rw [smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul] at hx
    rw [dotProduct_sub]
    have := le_of_mul_le_mul_left hx ht
    linarith
  have hin : ω + ζp ∈ budgetSetOn (nonnegOrthant L) (t • p) ((t • p) ⬝ᵥ ω) := by
    refine ⟨hX, ?_⟩
    simp only [dotProduct_add, smul_dotProduct, hpz, smul_zero, add_zero, le_refl]
  ext x
  simp only [Set.mem_singleton_iff]
  constructor
  · rintro ⟨hx, hmx⟩
    have h1 := hmx _ hin
    simp only [add_sub_cancel_left] at h1
    have := (hmax (x - ω) (hb x hx.2)).2 h1
    rw [← this]; abel
  · rintro rfl
    refine ⟨hin, fun y hy => ?_⟩
    simp only [add_sub_cancel_left]
    exact (hmax (y - ω) (hb y hy.2)).1

/-- The consumer `x ↦ u(x - ω)` inherits continuity, strong monotonicity and convexity. -/
theorem smd_consumer_props {u : (Fin L → ℝ) → ℝ} (ω : Fin L → ℝ) (hc : Continuous u)
    (hq : ∀ c, Convex ℝ {z | c ≤ u z}) (hm : ∀ z z', z ≤ z' → z ≠ z' → u z < u z') :
    Continuous (fun x => u (x - ω)) ∧ UtilityStronglyMonotone (fun x => u (x - ω)) ∧
      PrefConvex (nonnegOrthant L) (utilityPref fun x => u (x - ω)) := by
  refine ⟨hc.comp (continuous_id.sub continuous_const), ?_, ?_⟩
  · intro x _ y _ hxy hne
    have hlt : u (x - ω) < u (y - ω) :=
      hm _ _ (fun l => by simpa using hxy l) (fun h => hne (by simpa using h.symm))
    exact ⟨hlt.le, not_le.2 hlt⟩
  · intro x _ y₁ hy₁ y₂ hy₂ a b ha hb hab
    refine ⟨convex_nonnegOrthant L hy₁.1 hy₂.1 ha hb hab, ?_⟩
    have h := hq (u (x - ω)) hy₁.2 hy₂.2 ha hb hab
    change u (x - ω) ≤ u (a • y₁ + b • y₂ - ω)
    have e : a • y₁ + b • y₂ - ω = a • (y₁ - ω) + b • (y₂ - ω) := by
      rw [smul_sub, smul_sub, sub_add_sub_comm, ← add_smul, hab, one_smul]
    rw [e]; exact h

/-- **The rationalization lemma along a price curve** (the two-good case of MWG p. 603). Let
`P : [a, b] → (θ, Θ)^L` be a curve of prices with a continuous left inverse, and `ζ` a continuous
curve of excess demands with `P(q)·ζ(q) = 0` and `β (q - q') ≤ P(q)·ζ(q')` for `q' ≤ q`
(`ζ(q')` is affordable at `P(q)` only if `q' > q`, quantitatively). Then a continuous,
quasiconcave, strongly monotone `u` has `ζ(q)` as unique maximizer on `{P(q)·z ≤ 0}`. -/
theorem smd_curve_rationalize (hL : 0 < L) {a b : ℝ} (hab : a ≤ b) {P : ℝ → Fin L → ℝ}
    {Pinv : (Fin L → ℝ) → ℝ} {ζ : ℝ → Fin L → ℝ} {θ Θ β : ℝ} (hθ : 0 < θ) (hθΘ : θ ≤ Θ)
    (hβ : 0 < β) (hζc : ContinuousOn ζ (Set.Icc a b))
    (hPinv : ∀ q ∈ Set.Icc a b, Pinv (P q) = q)
    (hbox : ∀ q ∈ Set.Icc a b, ∀ l, θ < P q l ∧ P q l < Θ)
    (hW : ∀ q ∈ Set.Icc a b, P q ⬝ᵥ ζ q = 0)
    (hQ : ∀ q ∈ Set.Icc a b, ∀ q' ∈ Set.Icc a b, q' ≤ q → β * (q - q') ≤ P q ⬝ᵥ ζ q') :
    ∃ u : (Fin L → ℝ) → ℝ, Continuous u ∧ (∀ c, Convex ℝ {z | c ≤ u z}) ∧
      (∀ z z', z ≤ z' → z ≠ z' → u z < u z') ∧
      ∀ q ∈ Set.Icc a b, ∀ z, P q ⬝ᵥ z ≤ 0 → u z ≤ u (ζ q) ∧ (u (ζ q) ≤ u z → z = ζ q) := by
  have : CompactSpace (Set.Icc a b) := isCompact_iff_compactSpace.mp isCompact_Icc
  have : Nonempty (Set.Icc a b) := ⟨⟨a, le_rfl, hab⟩⟩
  set cl : ℝ → ℝ := fun x => max a (min x b) with hcl
  have hclmem : ∀ x, cl x ∈ Set.Icc a b := fun x => ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩
  have hclid : ∀ x ∈ Set.Icc a b, cl x = x := fun x hx => by simp [hcl, hx.1, hx.2]
  have hclc : Continuous cl := continuous_const.max (continuous_id.min continuous_const)
  set mm : ℝ → Set.Icc a b → ℝ := fun c d => cl (min d.1 c) with hmm
  have hmmc : Continuous fun x : ℝ × Set.Icc a b => mm x.1 x.2 :=
    hclc.comp ((continuous_subtype_val.comp continuous_snd).min continuous_fst)
  have hmmI : ∀ c ∈ Set.Icc a b, ∀ d : Set.Icc a b, mm c d = min d.1 c := by
    intro c hc d
    exact hclid _ ⟨le_min d.2.1 hc.1, (min_le_right _ _).trans hc.2⟩
  obtain ⟨u, hu1, hu2, hu3, hu4⟩ := smd_rationalize (D := Set.Icc a b) hL
    (K := P '' Set.Icc a b) (ζ := fun p => ζ (Pinv p)) (lev := Pinv)
    (g := fun c d => ζ (mm c d)) (ℓ := mm) (lo := a) (hi := b) (θ := θ) (Θ := Θ) (m := β)
    (hζc.comp_continuous hmmc fun x => hclmem _) hmmc hab hθ hθΘ hβ
    (by rintro _ ⟨q, hq, rfl⟩; exact hbox q hq)
    (by rintro _ ⟨q, hq, rfl⟩; rw [hPinv q hq]; exact hq)
    (fun c hc d => by rw [hmmI c hc d]; exact min_le_right _ _)
    (by
      rintro _ ⟨q, hq, rfl⟩ c hc hcq d
      rw [hPinv q hq] at hcq ⊢
      rw [hmmI c hc d]
      exact hQ q hq _ ⟨le_min d.2.1 hc.1, (min_le_right _ _).trans hc.2⟩
        ((min_le_right _ _).trans hcq))
    (by
      rintro _ ⟨q, hq, rfl⟩ d _ hℓ
      exact congrArg ζ hℓ)
    (by
      rintro _ ⟨q, hq, rfl⟩
      refine ⟨⟨q, hq⟩, ?_, ?_⟩
      · rw [hPinv q hq, hmmI q hq, min_self]
      · rw [hPinv q hq, hmmI q hq, min_self])
    (by rintro _ ⟨q, hq, rfl⟩; simp only [hPinv q hq]; exact hW q hq)
    (by
      intro c hc c' hc' hcc d
      refine ⟨⟨min d.1 c, le_min d.2.1 hc.1, (min_le_right _ _).trans hc.2⟩, ?_⟩
      have e : mm c' ⟨min d.1 c, le_min d.2.1 hc.1, (min_le_right _ _).trans hc.2⟩ = mm c d := by
        rw [hmmI c' hc', hmmI c hc]
        exact min_eq_left ((min_le_right _ _).trans hcc)
      exact ⟨by simp only [e], e⟩)
  refine ⟨u, hu1, hu2, hu3, fun q hq z hz => ?_⟩
  have := hu4 (P q) ⟨q, hq, rfl⟩ z hz
  simpa only [hPinv q hq] using this

/-! ### Two goods -/

/-- For two goods, `(q, 1) ∈ P_ε` when `ε ≤ q ≤ 1/ε`. -/
theorem pEps2_mk {ε : ℝ} (hε : 0 < ε) {q : ℝ} (hq : q ∈ Set.Icc ε (1 / ε)) :
    (![q, 1] : Fin 2 → ℝ) ∈ pEps 2 ε := by
  have hq0 : 0 < q := hε.trans_le hq.1
  have hε1 : ε ≤ 1 := by
    have h := hq.1.trans hq.2
    rw [le_div_iff₀ hε] at h
    nlinarith
  refine ⟨fun l => ?_, fun l l' => ?_⟩
  · fin_cases l <;> simp [hq0.le]
  · have h1 : ε ≤ 1 / q := by
      rw [le_div_iff₀ hq0]
      have := hq.2
      rw [le_div_iff₀ hε] at this
      linarith
    fin_cases l <;> fin_cases l' <;> simp [hq0.ne', hε1, hq.1]
    simpa using h1

/-- For two goods, `p ∈ P_ε` is `p₂ (q, 1)` with `q = p₁/p₂ ∈ [ε, 1/ε]`. -/
theorem pEps2_decomp {ε : ℝ} (hε : 0 < ε) {p : Fin 2 → ℝ} (hp : p ∈ pEps 2 ε) :
    p 0 / p 1 ∈ Set.Icc ε (1 / ε) ∧ p = p 1 • ![p 0 / p 1, 1] := by
  have h0 := pEps_pos hε hp 0
  have h1 := pEps_pos hε hp 1
  refine ⟨⟨hp.2 0 1, ?_⟩, ?_⟩
  · have h := hp.2 1 0
    rw [le_div_iff₀ h0] at h
    rw [div_le_div_iff₀ h1 hε]
    linarith
  · funext l
    fin_cases l
    · simp only [Fin.zero_eta, Pi.smul_apply, Matrix.cons_val_zero, smul_eq_mul]
      field_simp
    · simp

/-- **Proposition 17.E.3** (MWG, p. 602), `L = 2`: the first function of the book's
decomposition, `z¹₁(p) = z₁(p)/2 + r`, `z¹₂(p) = -(p₁/p₂) z¹₁(p)`. -/
noncomputable def smd2z1 (z : (Fin 2 → ℝ) → Fin 2 → ℝ) (r : ℝ) (p : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![z p 0 / 2 + r, -(p 0 / p 1) * (z p 0 / 2 + r)]

/-- **Proposition 17.E.3** (MWG, p. 602), `L = 2`: the second function of the book's
decomposition, `z²₁(p) = z₁(p)/2 - r`, `z²₂(p) = -(p₁/p₂) z²₁(p)`. -/
noncomputable def smd2z2 (z : (Fin 2 → ℝ) → Fin 2 → ℝ) (r : ℝ) (p : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![z p 0 / 2 - r, -(p 0 / p 1) * (z p 0 / 2 - r)]

/-- **Proposition 17.E.3** (MWG, p. 602), `L = 2`: there is `r > 0` with `|z₁(p)| < r` on `P_ε`
(continuity and homogeneity of degree zero). -/
theorem smd2_bound {ε : ℝ} (hε : 0 < ε) {z : (Fin 2 → ℝ) → Fin 2 → ℝ}
    (hc : ContinuousOn z (pEps 2 ε)) (hH : ∀ p ∈ pEps 2 ε, ∀ α : ℝ, 0 < α → z (α • p) = z p) :
    ∃ r, 0 < r ∧ ∀ p ∈ pEps 2 ε, |z p 0| < r := by
  have hcq : ContinuousOn (fun q : ℝ => z ![q, 1] 0) (Set.Icc ε (1 / ε)) := by
    have hm : Continuous fun q : ℝ => (![q, 1] : Fin 2 → ℝ) := by
      refine continuous_pi fun l => ?_
      fin_cases l
      · exact continuous_id
      · exact continuous_const
    exact (continuous_apply 0).comp_continuousOn
      (hc.comp hm.continuousOn fun q hq => pEps2_mk hε hq)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcq
  refine ⟨|M| + 1, by positivity, fun p hp => ?_⟩
  obtain ⟨hq, hpe⟩ := pEps2_decomp hε hp
  have : z p = z ![p 0 / p 1, 1] := by
    conv_lhs => rw [hpe]
    exact hH _ (pEps2_mk hε hq) (p 1) (pEps_pos hε hp 1)
  rw [this]
  have := hM _ hq
  rw [Real.norm_eq_abs] at this
  linarith [le_abs_self M]

/-- **Proposition 17.E.3** (MWG, p. 602), `L = 2`, the book's decomposition: if `|z₁| < r` on
`P_ε`, then `z¹ + z² = z`, each `zⁱ` satisfies Walras' law, is homogeneous of degree zero and
continuous on `P_ε`, and `zⁱ(p) ≠ 0` for every `p ∈ P_ε` (indeed `z¹₁ > 0 > z²₁`). -/
theorem smd2_decomposition {ε : ℝ} (hε : 0 < ε) {z : (Fin 2 → ℝ) → Fin 2 → ℝ}
    (hc : ContinuousOn z (pEps 2 ε)) (hH : ∀ p ∈ pEps 2 ε, ∀ α : ℝ, 0 < α → z (α • p) = z p)
    (hW : ∀ p ∈ pEps 2 ε, p ⬝ᵥ z p = 0) {r : ℝ} (hr : ∀ p ∈ pEps 2 ε, |z p 0| < r) :
    (∀ p ∈ pEps 2 ε, smd2z1 z r p + smd2z2 z r p = z p) ∧
    (∀ p ∈ pEps 2 ε, p ⬝ᵥ smd2z1 z r p = 0 ∧ p ⬝ᵥ smd2z2 z r p = 0) ∧
    (∀ p ∈ pEps 2 ε, ∀ α : ℝ, 0 < α →
      smd2z1 z r (α • p) = smd2z1 z r p ∧ smd2z2 z r (α • p) = smd2z2 z r p) ∧
    ContinuousOn (smd2z1 z r) (pEps 2 ε) ∧ ContinuousOn (smd2z2 z r) (pEps 2 ε) ∧
    (∀ p ∈ pEps 2 ε, 0 < smd2z1 z r p 0 ∧ smd2z2 z r p 0 < 0) := by
  refine ⟨fun p hp => ?_, fun p hp => ?_, fun p hp α hα => ?_, ?_, ?_, fun p hp => ?_⟩
  · have h1 := pEps_pos hε hp 1
    have hw := hW p hp
    simp only [dotProduct, Fin.sum_univ_two] at hw
    funext l
    fin_cases l
    · simp [smd2z1, smd2z2]
    · simp [smd2z1, smd2z2]
      field_simp
      linarith
  · have h1 := pEps_pos hε hp 1
    constructor <;> simp [smd2z1, smd2z2, dotProduct, Fin.sum_univ_two] <;> field_simp <;> ring
  · have e : (α • p) 0 / (α • p) 1 = p 0 / p 1 := by
      simp only [Pi.smul_apply, smul_eq_mul]; rw [mul_div_mul_left _ _ hα.ne']
    refine ⟨?_, ?_⟩ <;> simp only [smd2z1, smd2z2, hH p hp α hα, e]
  · have h0 : ContinuousOn (fun p => z p 0) (pEps 2 ε) := (continuous_apply 0).comp_continuousOn hc
    have hq : ContinuousOn (fun p : Fin 2 → ℝ => p 0 / p 1) (pEps 2 ε) :=
      (continuous_apply 0).continuousOn.div (continuous_apply 1).continuousOn
        fun p hp => (pEps_pos hε hp 1).ne'
    refine continuousOn_pi.2 fun l => ?_
    fin_cases l
    · exact ((h0.div_const 2).add (continuousOn_const (c := r))).congr fun p _ => by
        simp [smd2z1]
    · exact (hq.neg.mul ((h0.div_const 2).add (continuousOn_const (c := r)))).congr
        fun p _ => by simp [smd2z1]
  · have h0 : ContinuousOn (fun p => z p 0) (pEps 2 ε) := (continuous_apply 0).comp_continuousOn hc
    have hq : ContinuousOn (fun p : Fin 2 → ℝ => p 0 / p 1) (pEps 2 ε) :=
      (continuous_apply 0).continuousOn.div (continuous_apply 1).continuousOn
        fun p hp => (pEps_pos hε hp 1).ne'
    refine continuousOn_pi.2 fun l => ?_
    fin_cases l
    · exact ((h0.div_const 2).sub (continuousOn_const (c := r))).congr fun p _ => by
        simp [smd2z2]
    · exact (hq.neg.mul ((h0.div_const 2).sub (continuousOn_const (c := r)))).congr
        fun p _ => by simp [smd2z2]
  · have := abs_lt.1 (hr p hp)
    simp only [smd2z1, smd2z2, Matrix.cons_val_zero]
    constructor <;> linarith

/-- The linear utility `z ↦ ∑ₗ zₗ`: continuous, quasiconcave, strongly monotone. -/
theorem smd_sum_props :
    Continuous (fun z : Fin L → ℝ => ∑ l, z l) ∧
      (∀ c, Convex ℝ {z : Fin L → ℝ | c ≤ ∑ l, z l}) ∧
      (∀ z z' : Fin L → ℝ, z ≤ z' → z ≠ z' → ∑ l, z l < ∑ l, z' l) := by
  refine ⟨continuous_finsetSum _ fun l _ => continuous_apply l, fun c => ?_, ?_⟩
  · intro x hx y hy a b ha hb hab
    change c ≤ ∑ l, (a • x + b • y) l
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum]
    have hx' : c ≤ ∑ l, x l := hx
    have hy' : c ≤ ∑ l, y l := hy
    have e : a * c + b * c = c := by rw [← add_mul, hab, one_mul]
    have h1 := mul_le_mul_of_nonneg_left hx' ha
    have h2 := mul_le_mul_of_nonneg_left hy' hb
    linarith
  · intro z z' hzz hne
    obtain ⟨k, hk⟩ : ∃ k, z k < z' k := by
      by_contra h; push Not at h; exact hne (le_antisymm hzz fun k => h k)
    exact Finset.sum_lt_sum (fun l _ => hzz l) ⟨k, Finset.mem_univ k, hk⟩

/-- **Proposition 17.E.3** (MWG, p. 602), `L = 2`, the book's proof. Let `z` be continuous on
`P_ε`, homogeneous of degree zero, and satisfy Walras' law. Then there is an exchange economy
with two consumers (consumption sets `ℝ²_+`, endowments `ωᵢ ≫ 0`, continuous, convex and strongly
monotone preferences) whose demand at every `p ∈ P_ε` is a single bundle and whose aggregate
excess demand coincides with `z` on `P_ε`. Consumer `i`'s excess demand is the book's `zⁱ`
(`smd2z1`, `smd2z2`). -/
theorem proposition_17_E_3_two {ε : ℝ} (hε : 0 < ε) {z : (Fin 2 → ℝ) → Fin 2 → ℝ}
    (hc : ContinuousOn z (pEps 2 ε)) (hH : ∀ p ∈ pEps 2 ε, ∀ α : ℝ, 0 < α → z (α • p) = z p)
    (hW : ∀ p ∈ pEps 2 ε, p ⬝ᵥ z p = 0) :
    ∃ E : ExchangeEconomy (Fin 2) 2, (∀ i, E.X i = nonnegOrthant 2) ∧
      (∀ i, StrictlyPositive (E.ω i)) ∧
      (∀ i, Continuous (E.u i) ∧ UtilityStronglyMonotone (E.u i) ∧
        PrefConvex (nonnegOrthant 2) (utilityPref (E.u i))) ∧
      ∀ p ∈ pEps 2 ε, (∀ i, ∃ x, E.demand i p = {x}) ∧ excessDemand E p = z p := by
  rcases lt_or_ge 1 ε with hε1 | hε1
  · -- `P_ε` is empty
    have hempty : ∀ p ∈ pEps 2 ε, False := fun p hp => by
      have := hp.2 0 0
      rw [div_self (pEps_pos hε hp 0).ne'] at this
      linarith
    obtain ⟨h1, h2, h3⟩ := smd_sum_props (L := 2)
    have hP := smd_consumer_props (0 : Fin 2 → ℝ) h1 h2 h3
    exact ⟨ExchangeEconomy.ofOrthant (fun _ x => ∑ l, (x - 0) l)
      (fun _ _ => 1), fun _ => rfl, fun _ _ => one_pos, fun _ => hP,
      fun p hp => (hempty p hp).elim⟩
  have hab : ε ≤ 1 / ε := by rw [le_div_iff₀ hε]; nlinarith
  obtain ⟨r, hr0, hr⟩ := smd2_bound hε hc hH
  have hm : Continuous fun q : ℝ => (![q, 1] : Fin 2 → ℝ) := by
    refine continuous_pi fun l => ?_
    fin_cases l
    · exact continuous_id
    · exact continuous_const
  have hzq : ContinuousOn (fun q : ℝ => z ![q, 1] 0) (Set.Icc ε (1 / ε)) :=
    (continuous_apply 0).comp_continuousOn (hc.comp hm.continuousOn fun q hq => pEps2_mk hε hq)
  have hbnd : ∀ q ∈ Set.Icc ε (1 / ε), |z ![q, 1] 0| < r := fun q hq => hr _ (pEps2_mk hε hq)
  have hneg : ∀ q, q ∈ Set.Icc (-(1 / ε)) (-ε) ↔ -q ∈ Set.Icc ε (1 / ε) := by
    intro q; simp only [Set.mem_Icc]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  have hzq' : ContinuousOn (fun q : ℝ => z ![-q, 1] 0) (Set.Icc (-(1 / ε)) (-ε)) :=
    hzq.comp continuous_neg.continuousOn fun q hq => (hneg q).1 hq
  -- the two offer curves
  set b₁ : ℝ → ℝ := fun q => z ![q, 1] 0 / 2 + r with hb₁
  set b₂ : ℝ → ℝ := fun q => z ![-q, 1] 0 / 2 - r with hb₂
  set ζ₁ : ℝ → Fin 2 → ℝ := fun q => b₁ q • ![1, -q] with hζ₁
  set ζ₂ : ℝ → Fin 2 → ℝ := fun q => b₂ q • ![1, q] with hζ₂
  have hb₁r : ∀ q ∈ Set.Icc ε (1 / ε), r / 2 < b₁ q ∧ b₁ q < 3 * r / 2 := by
    intro q hq; have := abs_lt.1 (hbnd q hq); simp only [hb₁]; constructor <;> linarith
  have hb₂r : ∀ q ∈ Set.Icc ε (1 / ε), -(3 * r / 2) < b₂ (-q) ∧ b₂ (-q) < -(r / 2) := by
    intro q hq; have := abs_lt.1 (hbnd q hq); simp only [hb₂, neg_neg]
    constructor <;> linarith
  set θ := min ε 1 / 2 with hθ
  have hθ0 : 0 < θ := by positivity
  have hθε : θ < ε := by have := min_le_left ε 1; linarith
  have hθ1 : θ < 1 := by have := min_le_right ε 1; linarith
  set Θ := 1 / ε + 1 with hΘ
  have hεpos : (0 : ℝ) < 1 / ε := by positivity
  have hθΘ : θ ≤ Θ := by linarith
  have hεΘ : 1 / ε < Θ := by linarith
  have h1Θ : 1 < Θ := by linarith
  have hvc : ∀ c : ℝ, Continuous fun q : ℝ => (![1, c * q] : Fin 2 → ℝ) := by
    intro c
    refine continuous_pi fun l => ?_
    fin_cases l
    · exact continuous_const
    · exact continuous_const.mul continuous_id
  -- consumer 1
  obtain ⟨u₁, hu₁c, hu₁q, hu₁m, hu₁d⟩ := smd_curve_rationalize (L := 2) (by norm_num)
    (a := ε) (b := 1 / ε) (P := fun q => ![q, 1]) (Pinv := fun p => p 0) (ζ := ζ₁)
    (θ := θ) (Θ := Θ) (β := r / 2) hab hθ0 hθΘ (by positivity)
    (((hzq.div_const 2).add continuousOn_const).smul
      (by simpa using (hvc (-1)).continuousOn))
    (fun q _ => by simp)
    (fun q hq l => by
      fin_cases l
      · exact ⟨by simp; linarith [hq.1], by simp; linarith [hq.2]⟩
      · exact ⟨by simp; linarith, by simp; linarith⟩)
    (fun q _ => by simp [hζ₁, dotProduct, Fin.sum_univ_two]; ring)
    (fun q hq q' hq' hqq => by
      have := hb₁r q' hq'
      have e : (![q, 1] : Fin 2 → ℝ) ⬝ᵥ ζ₁ q' = b₁ q' * (q - q') := by
        simp [hζ₁, dotProduct, Fin.sum_univ_two]; ring
      rw [e]
      nlinarith)
  -- consumer 2
  obtain ⟨u₂, hu₂c, hu₂q, hu₂m, hu₂d⟩ := smd_curve_rationalize (L := 2) (by norm_num)
    (a := -(1 / ε)) (b := -ε) (P := fun q => ![-q, 1]) (Pinv := fun p => -p 0) (ζ := ζ₂)
    (θ := θ) (Θ := Θ) (β := r / 2) (by linarith) hθ0 hθΘ (by positivity)
    (((hzq'.div_const 2).sub continuousOn_const).smul
      (by simpa using (hvc 1).continuousOn))
    (fun q _ => by simp)
    (fun q hq l => by
      have hq' := (hneg q).1 hq
      fin_cases l
      · exact ⟨by simp; linarith [hq'.1], by simp; linarith [hq'.2]⟩
      · exact ⟨by simp; linarith, by simp; linarith⟩)
    (fun q _ => by simp [hζ₂, dotProduct, Fin.sum_univ_two]; ring)
    (fun q hq q' hq' hqq => by
      have := hb₂r (-q') ((hneg q').1 hq')
      rw [neg_neg] at this
      have e : (![-q, 1] : Fin 2 → ℝ) ⬝ᵥ ζ₂ q' = -b₂ q' * (q - q') := by
        simp [hζ₂, dotProduct, Fin.sum_univ_two]; ring
      rw [e]
      nlinarith)
  -- endowments
  set R : ℝ := 1 + 2 * r * (1 + 1 / ε) with hR
  set ω : Fin 2 → ℝ := fun _ => R with hω
  have hR : 3 * r / 2 * (1 / ε) + 3 * r / 2 < R := by rw [hR]; nlinarith
  have hX₁ : ∀ q ∈ Set.Icc ε (1 / ε), ω + ζ₁ q ∈ nonnegOrthant 2 := by
    intro q hq l
    have hb := hb₁r q hq
    have hq0 : 0 < q := hε.trans_le hq.1
    have hprod : b₁ q * q ≤ 3 * r / 2 * (1 / ε) :=
      mul_le_mul hb.2.le hq.2 hq0.le (by linarith)
    fin_cases l
    · simp [hω, hζ₁]; nlinarith
    · simp [hω, hζ₁]; nlinarith
  have hX₂ : ∀ q ∈ Set.Icc ε (1 / ε), ω + ζ₂ (-q) ∈ nonnegOrthant 2 := by
    intro q hq l
    have hb := hb₂r q hq
    have hq0 : 0 < q := hε.trans_le hq.1
    have hprod : 0 ≤ -b₂ (-q) * q := mul_nonneg (by linarith) hq0.le
    fin_cases l
    · simp [hω, hζ₂]; nlinarith
    · simp [hω, hζ₂]; nlinarith
  have hP₁ := smd_consumer_props ω hu₁c hu₁q hu₁m
  have hP₂ := smd_consumer_props ω hu₂c hu₂q hu₂m
  let E : ExchangeEconomy (Fin 2) 2 :=
    ExchangeEconomy.ofOrthant ![fun x => u₁ (x - ω), fun x => u₂ (x - ω)] fun _ => ω
  have hR0 : 0 < R := by
    have : 0 ≤ 3 * r / 2 * (1 / ε) + 3 * r / 2 := by positivity
    linarith
  refine ⟨E, fun _ => rfl, fun _ _ => hR0, fun i => ?_, fun p hp => ?_⟩
  · fin_cases i
    · exact hP₁
    · exact hP₂
  obtain ⟨hq, hpe⟩ := pEps2_decomp hε hp
  set q := p 0 / p 1 with hqdef
  have ht := pEps_pos hε hp 1
  have hd0 : E.demand 0 p = {ω + ζ₁ q} := by
    have h := smd_demand_eq (u := u₁) (ω := ω) (p := ![q, 1]) ht (hu₁d q hq)
      (by simp [hζ₁, dotProduct, Fin.sum_univ_two]; ring) (hX₁ q hq)
    rw [← hpe] at h
    exact h
  have hd1 : E.demand 1 p = {ω + ζ₂ (-q)} := by
    have hq' : -q ∈ Set.Icc (-(1 / ε)) (-ε) := (hneg (-q)).2 (by rw [neg_neg]; exact hq)
    have h := smd_demand_eq (u := u₂) (ω := ω) (p := ![-(-q), 1]) ht (hu₂d (-q) hq')
      (by simp [hζ₂, dotProduct, Fin.sum_univ_two]; ring) (hX₂ q hq)
    simp only [neg_neg] at h
    rw [← hpe] at h
    exact h
  refine ⟨fun i => ?_, ?_⟩
  · fin_cases i
    · exact ⟨_, hd0⟩
    · exact ⟨_, hd1⟩
  have hzp : z p = z ![q, 1] := by
    conv_lhs => rw [hpe]
    exact hH _ (pEps2_mk hε hq) (p 1) ht
  have hw := hW _ (pEps2_mk hε hq)
  simp [dotProduct, Fin.sum_univ_two] at hw
  rw [excessDemand, Fin.sum_univ_two, indivExcessDemand, indivExcessDemand,
    demandFn_eq E hd0, demandFn_eq E hd1, hzp]
  funext l
  fin_cases l
  · simp [hω, hζ₁, hζ₂, hb₁, hb₂, E, ExchangeEconomy.ofOrthant]
  · simp [hω, hζ₁, hζ₂, hb₁, hb₂, E, ExchangeEconomy.ofOrthant]
    linarith

end MWG.PositiveEquilibriumTheory
