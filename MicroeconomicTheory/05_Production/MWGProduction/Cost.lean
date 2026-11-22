/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGProduction.ProfitFOC

/-!
# The cost minimization problem (MWG Section 5.C, pp. 139-142)

For a single-output technology with production function `f`, the input requirement set is
`V(q) = {z ≥ 0 : f(z) ≥ q}`; the cost function `c(w, q)` is Chapter 3's support function of
`V(q)` and the conditional factor demand `z(w, q)` is its set of minimizers (the book's remark
on p. 140 that the CMP is the EMP with `f` in place of `u`).

Most results are proved for an arbitrary input requirement set `V ⊆ ℝ^n_+` (`vcost_*`), so
that they apply to the single-output case (**Proposition 5.C.2**) and to multiple outputs
(**Exercise 5.C.4**).

* **Proposition 5.C.2** (i)-(ix); (vi), Shephard's lemma, without convexity: for closed
  `V(q)` and `w̄ ≫ 0` a unique minimizer gives differentiability (`vcost_shephard`), by a
  Danskin-type argument (`supportFn_hasFDerivAt_of_compact`).
* **Exercises 5.C.3** and **5.C.5** (quasiconcavity suffices for (iii); quasiconcavity with
  increasing returns).
-/

namespace MWG.Production

open MWG.ClassicalDemand MWG.ConsumerChoice Filter Topology

variable {n : ℕ}

/-- **Section 5.C** (MWG, p. 139). The input requirement set `V(q) = {z ≥ 0 : f(z) ≥ q}`, the
constraint set of the cost minimization problem (CMP). -/
def inputReq (f : (Fin n → ℝ) → ℝ) (q : ℝ) : Set (Fin n → ℝ) := {z | 0 ≤ z ∧ q ≤ f z}

/-- **Section 5.C** (MWG, p. 139). The cost function `c(w, q) = min {w·z : z ≥ 0, f(z) ≥ q}`,
the support function of `V(q)` (real-valued; it is the minimum when `V(q) ≠ ∅` and `w ≥ 0`). -/
noncomputable def costFn (f : (Fin n → ℝ) → ℝ) (w : Fin n → ℝ) (q : ℝ) : ℝ :=
  supportFn (inputReq f q) w

/-- The cost function with values in `[-∞, +∞]`: `+∞` when `q` cannot be produced. -/
noncomputable def costFnE (f : (Fin n → ℝ) → ℝ) (w : Fin n → ℝ) (q : ℝ) : EReal :=
  supportFnE (inputReq f q) w

/-- **Section 5.C** (MWG, p. 139). The conditional factor demand correspondence `z(w, q)`. -/
def condDemand (f : (Fin n → ℝ) → ℝ) (w : Fin n → ℝ) (q : ℝ) : Set (Fin n → ℝ) :=
  supportArgmin (inputReq f q) w

theorem inputReq_subset_nonneg (f : (Fin n → ℝ) → ℝ) (q : ℝ) :
    inputReq f q ⊆ {z | 0 ≤ z} := fun _ hz => hz.1

theorem dot_nonneg_of_nonneg {w z : Fin n → ℝ} (hw : 0 ≤ w) (hz : 0 ≤ z) : 0 ≤ w ⬝ᵥ z :=
  Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (hz i)

/-- Costs are bounded below by `0` on `V ⊆ ℝ^n_+` for `w ≥ 0`. -/
theorem bddBelow_of_subset_nonneg {V : Set (Fin n → ℝ)} (hV : V ⊆ {z | 0 ≤ z})
    {w : Fin n → ℝ} (hw : 0 ≤ w) : BddBelow ((fun z => w ⬝ᵥ z) '' V) :=
  ⟨0, by rintro _ ⟨z, hz, rfl⟩; exact dot_nonneg_of_nonneg hw (hV hz)⟩

/-! ### Results for an arbitrary input requirement set `V ⊆ ℝ^n_+` -/

/-- Homogeneity of degree one in `w`. -/
theorem vcost_smul (V : Set (Fin n → ℝ)) (w : Fin n → ℝ) {α : ℝ} (hα : 0 ≤ α) :
    supportFn V (α • w) = α * supportFn V w :=
  supportFn_smul V w hα

/-- Monotonicity in the requirement: a smaller `V` costs more. -/
theorem vcost_mono {V V' : Set (Fin n → ℝ)} (hV : V ⊆ {z | 0 ≤ z}) (hsub : V' ⊆ V)
    (hne : V'.Nonempty) {w : Fin n → ℝ} (hw : 0 ≤ w) : supportFn V w ≤ supportFn V' w :=
  csInf_le_csInf (bddBelow_of_subset_nonneg hV hw) (hne.image _) (Set.image_mono hsub)

/-- Concavity in `w` on `ℝ^n_+`. -/
theorem vcost_concaveOn {V : Set (Fin n → ℝ)} (hV : V ⊆ {z | 0 ≤ z}) (hne : V.Nonempty) :
    ConcaveOn ℝ {w : Fin n → ℝ | 0 ≤ w} (supportFn V) :=
  (supportFn_concaveOn hne).subset (fun _ hw => bddBelow_of_subset_nonneg hV hw)
    (fun x hx y hy a b ha hb _ =>
      show 0 ≤ a • x + b • y from add_nonneg (smul_nonneg ha hx) (smul_nonneg hb hy))

/-- Duality for input requirement sets: if `V ⊆ ℝ^n_+` is closed, convex and upward closed (free
disposal of inputs), then `z ∈ V` iff `w·z ≥ μ_V(w)` for every `w ≫ 0`. -/
theorem vcost_iii {V : Set (Fin n → ℝ)} (hcl : IsClosed V) (hc : Convex ℝ V)
    (hup : ∀ z ∈ V, ∀ z', z ≤ z' → z' ∈ V) (hV : V ⊆ {z | 0 ≤ z}) (z : Fin n → ℝ) :
    z ∈ V ↔ ∀ w : Fin n → ℝ, StrictlyPositive w → supportFnE V w ≤ ((w ⬝ᵥ z : ℝ) : EReal) := by
  constructor
  · intro hz w _
    exact iInf₂_le z hz
  · intro h
    by_contra hz
    rcases V.eq_empty_or_nonempty with hV0 | hne
    · have := h 1 (fun _ => one_pos)
      rw [hV0] at this
      simp [supportFnE] at this
    obtain ⟨q, c, hqz, hqV⟩ := separation_section_3_F hcl hc hz
    have hq0 : 0 ≤ q := by
      intro l
      by_contra hl0
      have hl : q l < 0 := not_le.mp hl0
      obtain ⟨v, hv⟩ := hne
      set t := (|c| + |q ⬝ᵥ v| + 1) / (-q l) with ht
      have htpos : 0 ≤ t := div_nonneg (by positivity) (by linarith)
      have hmem : v + t • Pi.single l 1 ∈ V :=
        hup v hv _ (le_add_of_nonneg_right (smul_nonneg htpos (Pi.single_nonneg.mpr zero_le_one)))
      have := hqV _ hmem
      rw [dotProduct_add, dotProduct_smul, dotProduct_single, mul_one, smul_eq_mul] at this
      have h2 : t * q l = -(|c| + |q ⬝ᵥ v| + 1) := by
        rw [ht, div_mul_eq_mul_div, div_neg, mul_div_assoc, div_self hl.ne, mul_one]
      rw [h2] at this
      linarith [neg_abs_le c, le_abs_self (q ⬝ᵥ v)]
    set s := ∑ i, |z i| with hs
    set ε := (c - q ⬝ᵥ z) / (2 * (s + 1)) with hε
    have hεpos : 0 < ε := div_pos (by linarith) (by positivity)
    set w := q + ε • (1 : Fin n → ℝ) with hw
    have hwpos : StrictlyPositive w := fun l => by
      simp only [hw, Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
      have hql : 0 ≤ q l := hq0 l
      linarith
    have hlow : (c : EReal) ≤ supportFnE V w := by
      refine le_iInf₂ fun v hv => EReal.coe_le_coe_iff.mpr ?_
      have h1 := hqV v hv
      have h2 : 0 ≤ ε • (1 : Fin n → ℝ) ⬝ᵥ v :=
        dot_nonneg_of_nonneg (smul_nonneg hεpos.le (fun _ => zero_le_one)) (hV hv)
      rw [hw, add_dotProduct]
      linarith
    have hup' := hlow.trans (h w hwpos)
    have h3 := EReal.coe_le_coe_iff.mp hup'
    rw [hw, add_dotProduct, smul_dotProduct, smul_eq_mul] at h3
    have h4 : (1 : Fin n → ℝ) ⬝ᵥ z ≤ s := by
      simp only [dotProduct, Pi.one_apply, one_mul, hs]
      exact Finset.sum_le_sum fun i _ => le_abs_self (z i)
    have hs0 : 0 ≤ s := Finset.sum_nonneg fun i _ => abs_nonneg (z i)
    have h5 : ε * (s + 1) = (c - q ⬝ᵥ z) / 2 := by
      rw [hε]
      field_simp
    nlinarith

/-- Homogeneity of degree zero of the minimizers in `w`. -/
theorem vdemand_smul (V : Set (Fin n → ℝ)) (w : Fin n → ℝ) {α : ℝ} (hα : 0 < α) :
    supportArgmin V (α • w) = supportArgmin V w := by
  ext z
  simp only [supportArgmin, Set.mem_ofPred_eq, smul_dotProduct, smul_eq_mul]
  constructor
  · rintro ⟨hz, h⟩
    exact ⟨hz, fun y hy => le_of_mul_le_mul_left (h y hy) hα⟩
  · rintro ⟨hz, h⟩
    exact ⟨hz, fun y hy => mul_le_mul_of_nonneg_left (h y hy) hα.le⟩

/-- Convexity of the set of minimizers for convex `V`. -/
theorem vdemand_convex {V : Set (Fin n → ℝ)} (hc : Convex ℝ V) (w : Fin n → ℝ) :
    Convex ℝ (supportArgmin V w) := by
  rintro y ⟨hy, hmin⟩ y' ⟨hy', hmin'⟩ a b ha hb hab
  refine ⟨hc hy hy' ha hb hab, fun z hz => ?_⟩
  rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  have h1 := hmin z hz
  have h2 := hmin' z hz
  calc a * w ⬝ᵥ y + b * w ⬝ᵥ y' ≤ a * w ⬝ᵥ z + b * w ⬝ᵥ z :=
        add_le_add (mul_le_mul_of_nonneg_left h1 ha) (mul_le_mul_of_nonneg_left h2 hb)
    _ = w ⬝ᵥ z := by rw [← add_mul, hab, one_mul]

/-- At most one minimizer for strictly convex `V` and `w ≠ 0`. -/
theorem vdemand_strict {V : Set (Fin n → ℝ)} (hsc : StrictConvex ℝ V) {w : Fin n → ℝ}
    (hw : w ≠ 0) : (supportArgmin V w).Subsingleton := by
  intro y hy y' hy'
  by_contra hne
  have hint := hsc hy.1 hy'.1 hne (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num)
  set m := (1 / 2 : ℝ) • y + (1 / 2 : ℝ) • y'
  have hnhds : V ∈ 𝓝 m := mem_interior_iff_mem_nhds.mp hint
  have hg : Continuous fun t : ℝ => m - t • w := by fun_prop
  have hpre := hg.continuousAt (x := 0) (by simpa using hnhds)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hpre
  have hmem : ε / 2 ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith
  have hin : m - (ε / 2) • w ∈ V := hball hmem
  have hle := hy.2 _ hin
  have hle' := hy'.2 y hy.1
  have hle'' := hy.2 y' hy'.1
  have hww : 0 < w ⬝ᵥ w := by
    have h0 : 0 ≤ w ⬝ᵥ w := Finset.sum_nonneg fun i _ => mul_self_nonneg (w i)
    exact lt_of_le_of_ne h0 (Ne.symm fun h => hw (dotProduct_self_eq_zero.mp h))
  simp only [m, dotProduct_sub, dotProduct_add, dotProduct_smul, smul_eq_mul] at hle
  nlinarith

/-- **Danskin's lemma** for a compact set with a unique minimizer: if `K` is compact and `x̄` is
the unique minimizer of `p̄·x` on `K`, then `μ_K` is differentiable at `p̄` with gradient `x̄`
(no convexity needed). -/
theorem supportFn_hasFDerivAt_of_compact {K : Set (Fin n → ℝ)} (hK : IsCompact K)
    {p x : Fin n → ℝ} (hx : x ∈ supportArgmin K p) (huniq : ∀ y ∈ supportArgmin K p, y = x) :
    HasFDerivAt (supportFn K) (dualityDotCLM x) p := by
  have hbdd : ∀ q : Fin n → ℝ, BddBelow ((fun y => q ⬝ᵥ y) '' K) := fun q =>
    (hK.image (by fun_prop : Continuous fun y => q ⬝ᵥ y)).isBounded.bddBelow
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  have hRx : ‖x‖ ≤ R := hR x hx.1
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  set ε' := ε / (n + 1) with hε'
  have hε'pos : 0 < ε' := by positivity
  -- the far part of `K` is compact; its minimal excess cost is positive
  set Kf := K ∩ {y | ε' ≤ ‖y - x‖} with hKf
  have hKfc : IsCompact Kf :=
    hK.inter_right (isClosed_le continuous_const (by fun_prop))
  obtain ⟨η, hηpos, hη⟩ : ∃ η > 0, ∀ y ∈ Kf, p ⬝ᵥ x + η ≤ p ⬝ᵥ y := by
    rcases Kf.eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, fun y hy => by rw [he] at hy; exact absurd hy (Set.notMem_empty _)⟩
    obtain ⟨y0, hy0, hmin⟩ := hKfc.exists_isMinOn hne
      (by fun_prop : Continuous fun y => p ⬝ᵥ y).continuousOn
    have hlt : p ⬝ᵥ x < p ⬝ᵥ y0 := by
      rcases (hx.2 y0 hy0.1).lt_or_eq with h | h
      · exact h
      · exfalso
        have := huniq y0 ⟨hy0.1, fun z hz => h ▸ hx.2 z hz⟩
        have h3 : ε' ≤ ‖y0 - x‖ := hy0.2
        rw [this, sub_self, norm_zero] at h3
        linarith
    refine ⟨p ⬝ᵥ y0 - p ⬝ᵥ x, by linarith, fun y hy => ?_⟩
    have := hmin hy
    simp only [Set.mem_ofPred_eq] at this
    linarith
  have hball : ∀ᶠ q in 𝓝 p, ‖q - p‖ * (n * (2 * R)) ≤ η := by
    have hc : Tendsto (fun q : Fin n → ℝ => ‖q - p‖ * (n * (2 * R))) (𝓝 p) (𝓝 0) := by
      have : Tendsto (fun q : Fin n → ℝ => ‖q - p‖) (𝓝 p) (𝓝 0) := tendsto_norm_sub_self p
      simpa using this.mul_const (n * (2 * R))
    exact hc.eventually (eventually_le_nhds hηpos)
  filter_upwards [hball] with q hq
  have hup : supportFn K q ≤ q ⬝ᵥ x := supportFn_le (hbdd q) hx.1
  have hlow : supportFn K p + x ⬝ᵥ (q - p) - ε * ‖q - p‖ ≤ supportFn K q := by
    apply le_supportFn ⟨x, hx.1⟩
    intro y hy
    rw [supportFn_eq_of_mem_argmin hx]
    have hdot := duality_abs_dotProduct_le (q - p) (y - x)
    have hyx : ‖y - x‖ ≤ 2 * R := by
      calc ‖y - x‖ ≤ ‖y‖ + ‖x‖ := norm_sub_le y x
        _ ≤ 2 * R := by linarith [hR y hy]
    have hkey : q ⬝ᵥ y = p ⬝ᵥ x + x ⬝ᵥ (q - p) + (p ⬝ᵥ y - p ⬝ᵥ x) + (q - p) ⬝ᵥ (y - x) := by
      simp only [dotProduct_sub, sub_dotProduct, dotProduct_comm x q, dotProduct_comm x p]
      ring
    rw [hkey]
    have hpy := hx.2 y hy
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hqp := norm_nonneg (q - p)
    by_cases hfar : ε' ≤ ‖y - x‖
    · have h1 := hη y ⟨hy, hfar⟩
      have h2 : |(q - p) ⬝ᵥ (y - x)| ≤ η := by
        calc |(q - p) ⬝ᵥ (y - x)| ≤ n * (‖q - p‖ * ‖y - x‖) := hdot
          _ ≤ n * (‖q - p‖ * (2 * R)) := by gcongr
          _ ≤ η := by linarith
      have := neg_abs_le ((q - p) ⬝ᵥ (y - x))
      nlinarith [mul_nonneg hε.le hqp]
    · rw [not_le] at hfar
      have h2 : |(q - p) ⬝ᵥ (y - x)| ≤ ε * ‖q - p‖ := by
        calc |(q - p) ⬝ᵥ (y - x)| ≤ n * (‖q - p‖ * ‖y - x‖) := hdot
          _ ≤ n * (‖q - p‖ * ε') := by gcongr
          _ ≤ ε * ‖q - p‖ := by
            rw [hε']
            have : (n : ℝ) * (‖q - p‖ * (ε / (n + 1))) = ε * ‖q - p‖ * (n / (n + 1)) := by
              field_simp
            rw [this]
            have hfrac : (n : ℝ) / (n + 1) ≤ 1 := by
              rw [div_le_one (by positivity)]
              linarith
            calc ε * ‖q - p‖ * (n / (n + 1)) ≤ ε * ‖q - p‖ * 1 :=
                  mul_le_mul_of_nonneg_left hfrac (mul_nonneg hε.le hqp)
              _ = ε * ‖q - p‖ := mul_one _
      have := neg_abs_le ((q - p) ⬝ᵥ (y - x))
      linarith
  rw [dualityDotCLM_apply, Real.norm_eq_abs, abs_le]
  have hsp : supportFn K p = p ⬝ᵥ x := supportFn_eq_of_mem_argmin hx
  have hxq : x ⬝ᵥ (q - p) = q ⬝ᵥ x - p ⬝ᵥ x := by
    rw [dotProduct_sub, dotProduct_comm x q, dotProduct_comm x p]
  have := mul_nonneg hε.le (norm_nonneg (q - p))
  constructor <;> linarith

/-- **Shephard's lemma** for an input requirement set, without convexity: if `V ⊆ ℝ^n_+` is
closed, `w̄ ≫ 0` and `z̄` is the unique cost-minimizing input vector at `w̄`, then `μ_V` is
differentiable at `w̄` with gradient `z̄`. -/
theorem vcost_shephard {V : Set (Fin n → ℝ)} (hcl : IsClosed V) (hV : V ⊆ {z | 0 ≤ z})
    {w z : Fin n → ℝ} (hw : StrictlyPositive w) (hz : supportArgmin V w = {z}) :
    HasFDerivAt (supportFn V) (dualityDotCLM z) w := by
  have hzm : z ∈ supportArgmin V w := by rw [hz]; rfl
  set M := 4 * (w ⬝ᵥ z) + 1 with hM
  set K := V ∩ {y | w ⬝ᵥ y ≤ M} with hK
  have hwz : 0 ≤ w ⬝ᵥ z := dot_nonneg_of_nonneg (fun i => (hw i).le) (hV hzm.1)
  have hzK : z ∈ K := ⟨hzm.1, show w ⬝ᵥ z ≤ M by rw [hM]; linarith⟩
  -- `K` is compact
  have hM0 : 0 ≤ M := by rw [hM]; linarith
  have hKc : IsCompact K := by
    set R := ∑ j, M / w j with hR
    have hR0 : 0 ≤ R := Finset.sum_nonneg fun j _ => div_nonneg hM0 (hw j).le
    apply (isCompact_closedBall (0 : Fin n → ℝ) R).of_isClosed_subset
    · exact hcl.inter (isClosed_le (by fun_prop) continuous_const)
    · intro y hy
      rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hR0]
      intro i
      have hy0 : 0 ≤ y := hV hy.1
      have hyi : 0 ≤ y i := hy0 i
      have hyM : w ⬝ᵥ y ≤ M := hy.2
      rw [Real.norm_eq_abs, abs_of_nonneg hyi]
      have h1 : w i * y i ≤ w ⬝ᵥ y :=
        Finset.single_le_sum (f := fun j => w j * y j)
          (fun j _ => mul_nonneg (hw j).le (hy0 j)) (Finset.mem_univ i)
      have h2 : y i ≤ M / w i := by
        rw [le_div_iff₀ (hw i)]
        linarith
      have h3 : M / w i ≤ R :=
        Finset.single_le_sum (f := fun j => M / w j)
          (fun j _ => div_nonneg hM0 (hw j).le) (Finset.mem_univ i)
      linarith
  -- the minimizer on `K` is unique
  have hzK' : z ∈ supportArgmin K w := ⟨hzK, fun y hy => hzm.2 y hy.1⟩
  have huniqK : ∀ y ∈ supportArgmin K w, y = z := by
    intro y hy
    have : y ∈ supportArgmin V w := by
      refine ⟨hy.1.1, fun v hv => ?_⟩
      exact (hy.2 z hzK).trans (hzm.2 v hv)
    rw [hz] at this
    exact this
  have hdK := supportFn_hasFDerivAt_of_compact hKc hzK' huniqK
  -- `μ_V = μ_K` near `w`
  have hnear : ∀ᶠ q in 𝓝 w, ∀ i, w i / 2 ≤ q i ∧ q i ≤ 2 * w i := by
    rw [eventually_all]
    intro i
    have hc : Continuous fun q : Fin n → ℝ => q i := continuous_apply i
    have h1 : ∀ᶠ q in 𝓝 w, w i / 2 < q i :=
      hc.continuousAt.eventually (eventually_gt_nhds (by linarith [hw i]))
    have h2 : ∀ᶠ q in 𝓝 w, q i < 2 * w i :=
      hc.continuousAt.eventually (eventually_lt_nhds (by linarith [hw i]))
    filter_upwards [h1, h2] with q hq1 hq2
    exact ⟨hq1.le, hq2.le⟩
  have heq : supportFn V =ᶠ[𝓝 w] supportFn K := by
    filter_upwards [hnear] with q hq
    have hq0 : 0 ≤ q := fun i => show (0 : ℝ) ≤ q i by linarith [hw i, (hq i).1]
    apply le_antisymm
    · exact vcost_mono hV Set.inter_subset_left ⟨z, hzK⟩ hq0
    · apply le_csInf (Set.Nonempty.image (fun y => q ⬝ᵥ y) ⟨z, hzm.1⟩)
      rintro _ ⟨v, hv, rfl⟩
      by_cases hvK : w ⬝ᵥ v ≤ M
      · exact supportFn_le (bddBelow_of_subset_nonneg
          (fun y hy => hV hy.1) hq0) ⟨hv, hvK⟩
      · rw [not_le] at hvK
        have hv0 := hV hv
        have h1 : w ⬝ᵥ v ≤ 2 * (q ⬝ᵥ v) := by
          simp only [dotProduct, Finset.mul_sum]
          exact Finset.sum_le_sum fun i _ => by
            have hvi : 0 ≤ v i := hv0 i
            nlinarith [(hq i).1]
        have h2 : q ⬝ᵥ z ≤ 2 * (w ⬝ᵥ z) := by
          simp only [dotProduct, Finset.mul_sum]
          exact Finset.sum_le_sum fun i _ => by
            have hzi : 0 ≤ z i := hV hzm.1 i
            nlinarith [(hq i).2]
        have h3 := supportFn_le (bddBelow_of_subset_nonneg
          (fun y hy => hV hy.1) hq0) hzK
        linarith
  exact hdK.congr_of_eventuallyEq heq

/-- The law of demand for minimizers: `(w - w')·(z - z') ≤ 0`. -/
theorem vdemand_law {V : Set (Fin n → ℝ)} {w w' z z' : Fin n → ℝ}
    (hz : z ∈ supportArgmin V w) (hz' : z' ∈ supportArgmin V w') :
    (w - w') ⬝ᵥ (z - z') ≤ 0 := by
  have h1 := hz.2 z' hz'.1
  have h2 := hz'.2 z hz.1
  rw [sub_dotProduct, dotProduct_sub, dotProduct_sub]
  linarith

/-- Derivative properties of a single-valued minimizer selection: if `V ⊆ ℝ^n_+` is closed,
`w̄ ≫ 0`, `supportArgmin V w = {zs w}` for `w` near `w̄` and `zs` has derivative `D` at `w̄`,
then `D = D²μ_V(w̄)`, `D` is symmetric and negative semidefinite, and `D w̄ = 0`. -/
theorem vdemand_derivative {V : Set (Fin n → ℝ)} (hcl : IsClosed V) (hV : V ⊆ {z | 0 ≤ z})
    {zs : (Fin n → ℝ) → (Fin n → ℝ)} {w : Fin n → ℝ} (hw : StrictlyPositive w)
    (hzs : ∀ᶠ q in 𝓝 w, supportArgmin V q = {zs q})
    {D : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)} (hD : HasFDerivAt zs D w) :
    hessianMatrix (supportFn V) w = jacobian D ∧
      (∀ i j, jacobian D i j = jacobian D j i) ∧ NegSemidef (jacobian D) ∧ D w = 0 := by
  have hpos : ∀ᶠ q in 𝓝 w, StrictlyPositive q := relations_eventually_strictlyPositive hw
  have hgrad : ∀ᶠ q in 𝓝 w, HasFDerivAt (supportFn V) (dualityDotCLM (zs q)) q := by
    filter_upwards [hzs, hpos] with q hq hqpos
    exact vcost_shephard hcl hV hqpos hq
  refine ⟨?_, ?_, ?_, ?_⟩
  · have heq : (fun q => gradientVec (fderiv ℝ (supportFn V) q)) =ᶠ[𝓝 w] zs := by
      filter_upwards [hgrad] with q hq
      rw [hq.fderiv, gradientVec_dualityDotCLM]
    rw [hessianMatrix, (hD.congr_of_eventuallyEq heq).fderiv]
  · have h1 : ∀ᶠ q in 𝓝 w, HasFDerivAt (supportFn V) (dualityDotLin (zs q)) q := by
      filter_upwards [hgrad] with q hq
      rwa [dualityDotLin_apply]
    have h2 : HasFDerivAt (fun q => dualityDotLin (zs q)) (dualityDotLin.comp D) w :=
      dualityDotLin.hasFDerivAt.comp w hD
    intro i j
    have := second_derivative_symmetric_of_eventually h1 h2 (Pi.single j 1) (Pi.single i 1)
    simp only [ContinuousLinearMap.comp_apply, dualityDotLin_apply, dualityDotCLM_apply,
      dotProduct_single, mul_one] at this
    simpa [jacobian] using this
  · intro v
    rw [jacobian_mulVec]
    set γ : ℝ → Fin n → ℝ := fun t => w + t • v with hγ
    have hγd : HasDerivAt γ v 0 := by
      have h := ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add w
      simp only [id, one_smul] at h
      exact h
    have hγ0 : γ 0 = w := by simp [γ]
    have hcomp : HasDerivAt (fun t => zs (γ t)) (D v) 0 := by
      have hD' := hD
      rw [← hγ0] at hD'
      exact hD'.comp_hasDerivAt 0 hγd
    have hg : HasDerivAt (fun t => ∑ l, v l * zs (γ t) l) (∑ l, v l * D v l) 0 :=
      HasDerivAt.fun_sum fun l _ => (hasDerivAt_pi.mp hcomp l).const_mul (v l)
    apply hasDerivAt_nonpos_of_right_le hg
    have hcont : Tendsto γ (𝓝[>] 0) (𝓝 w) := by
      rw [← hγ0]
      exact hγd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    filter_upwards [hcont.eventually hzs, self_mem_nhdsWithin] with t ht htpos
    have hm1 : zs (γ t) ∈ supportArgmin V (γ t) := by rw [ht]; rfl
    have hm2 : zs w ∈ supportArgmin V w := by rw [hzs.self_of_nhds]; rfl
    have hlaw := vdemand_law hm1 hm2
    have hsub : γ t - w = t • v := by simp [γ]
    rw [hsub, smul_dotProduct, smul_eq_mul, dotProduct_sub] at hlaw
    have : v ⬝ᵥ zs (γ t) - v ⬝ᵥ zs w ≤ 0 := by
      by_contra h
      rw [not_le] at h
      have := mul_pos (show (0 : ℝ) < t from htpos) h
      linarith
    simp only [dotProduct] at this
    simp only [hγ0]
    linarith
  · set γ : ℝ → Fin n → ℝ := fun t => w + t • w with hγ
    have hγd : HasDerivAt γ w 0 := by
      have h := ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add w
      simp only [id, one_smul] at h
      exact h
    have hγ0 : γ 0 = w := by simp [γ]
    have hcomp : HasDerivAt (fun t => zs (γ t)) (D w) 0 := by
      have hD' := hD
      rw [← hγ0] at hD'
      exact hD'.comp_hasDerivAt 0 hγd
    have hcont : Tendsto γ (𝓝 0) (𝓝 w) := by
      rw [← hγ0]
      exact hγd.continuousAt.tendsto
    have hconst : (fun t => zs (γ t)) =ᶠ[𝓝 0] fun _ => zs w := by
      have : ∀ᶠ t : ℝ in 𝓝 0, -1 < t := lt_mem_nhds (by norm_num)
      filter_upwards [this, hcont.eventually hzs] with t ht hst
      have hpos : 0 < 1 + t := by linarith
      have hγt : γ t = (1 + t) • w := by simp [γ, add_smul]
      rw [hγt, vdemand_smul V w hpos, hzs.self_of_nhds] at hst
      rw [hγt]
      have : zs ((1 + t) • w) ∈ ({zs w} : Set (Fin n → ℝ)) := by rw [hst]; rfl
      exact this
    have h0 : HasDerivAt (fun t => zs (γ t)) 0 0 :=
      (hasDerivAt_const (0 : ℝ) (zs w)).congr_of_eventuallyEq hconst
    exact hcomp.unique h0

/-! ### Proposition 5.C.2 -/

/-- **Proposition 5.C.2(i)** (MWG, p. 141), first part: `c(·, q)` is homogeneous of degree one
in `w`. -/
theorem proposition_5_C_2_i_hom (f : (Fin n → ℝ) → ℝ) (w : Fin n → ℝ) (q : ℝ) {α : ℝ}
    (hα : 0 ≤ α) : costFn f (α • w) q = α * costFn f w q :=
  vcost_smul _ w hα

/-- **Proposition 5.C.2(i)** (MWG, p. 141), second part: `c(w, ·)` is nondecreasing in `q`
(where `q'` can be produced and `w ≥ 0`). -/
theorem proposition_5_C_2_i_mono (f : (Fin n → ℝ) → ℝ) {w : Fin n → ℝ} (hw : 0 ≤ w)
    {q q' : ℝ} (hqq : q ≤ q') (hne : (inputReq f q').Nonempty) :
    costFn f w q ≤ costFn f w q' :=
  vcost_mono (inputReq_subset_nonneg f q) (fun _ hz => ⟨hz.1, hqq.trans hz.2⟩) hne hw

/-- **Proposition 5.C.2(ii)** (MWG, p. 141): `c(·, q)` is concave in `w` on `ℝ^n_+`. -/
theorem proposition_5_C_2_ii (f : (Fin n → ℝ) → ℝ) {q : ℝ} (hne : (inputReq f q).Nonempty) :
    ConcaveOn ℝ {w : Fin n → ℝ | 0 ≤ w} (fun w => costFn f w q) :=
  vcost_concaveOn (inputReq_subset_nonneg f q) hne

theorem continuous_extendVec_neg (q : ℝ) :
    Continuous fun z : Fin n → ℝ => extendVec (-z) q := by
  refine continuous_pi fun i => ?_
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [extendVec, Fin.snoc_last]
    exact continuous_const
  · simp only [extendVec, Fin.snoc_castSucc, Pi.neg_apply]
    exact (continuous_apply j).neg

/-- The input requirement set is the section of the production set at output `q`. -/
theorem inputReq_eq_section (f : (Fin n → ℝ) → ℝ) (q : ℝ) :
    inputReq f q = {z | extendVec (-z) q ∈ singleOutputSet f} := by
  ext z
  exact mem_singleOutputSet.symm

theorem isClosed_inputReq {f : (Fin n → ℝ) → ℝ} (hcl : IsClosed (singleOutputSet f)) (q : ℝ) :
    IsClosed (inputReq f q) := by
  rw [inputReq_eq_section]
  exact hcl.preimage (continuous_extendVec_neg q)

theorem upward_inputReq {f : (Fin n → ℝ) → ℝ} (hfd : FreeDisposal (singleOutputSet f)) (q : ℝ) :
    ∀ z ∈ inputReq f q, ∀ z', z ≤ z' → z' ∈ inputReq f q := by
  intro z hz z' hzz
  rw [inputReq_eq_section] at hz ⊢
  apply hfd _ hz
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [extendVec]
  · simp only [extendVec, Fin.snoc_castSucc, Pi.neg_apply, neg_le_neg_iff]
    exact hzz j

/-- **Proposition 5.C.2(iii)** (MWG, p. 141). If `Y` is closed with free disposal and every
`{z ≥ 0 : f(z) ≥ q}` is convex, then `Y = {(-z, q) : w·z ≥ c(w, q) for all w ≫ 0}` (with
`c(w, q) = +∞` when `q` cannot be produced). -/
theorem proposition_5_C_2_iii {f : (Fin n → ℝ) → ℝ} (hcl : IsClosed (singleOutputSet f))
    (hfd : FreeDisposal (singleOutputSet f)) (hc : ∀ q, Convex ℝ (inputReq f q)) :
    singleOutputSet f = {y | ∀ w : Fin n → ℝ, StrictlyPositive w →
      costFnE f w (y (Fin.last n)) ≤ ((w ⬝ᵥ inputsOf y : ℝ) : EReal)} := by
  ext y
  have hy : y ∈ singleOutputSet f ↔ inputsOf y ∈ inputReq f (y (Fin.last n)) := by
    rw [inputReq_eq_section, Set.mem_ofPred_eq, extendVec_inputsOf]
  rw [hy, vcost_iii (isClosed_inputReq hcl _) (hc _) (upward_inputReq hfd _)
    (inputReq_subset_nonneg f _)]
  rfl

/-- **Proposition 5.C.2(iv)** (MWG, p. 141): `z(·, q)` is homogeneous of degree zero in `w`. -/
theorem proposition_5_C_2_iv (f : (Fin n → ℝ) → ℝ) (w : Fin n → ℝ) (q : ℝ) {α : ℝ}
    (hα : 0 < α) : condDemand f (α • w) q = condDemand f w q :=
  vdemand_smul _ w hα

/-- **Proposition 5.C.2(v)** (MWG, p. 141), first part: if `{z ≥ 0 : f(z) ≥ q}` is convex,
`z(w, q)` is convex. -/
theorem proposition_5_C_2_v_convex {f : (Fin n → ℝ) → ℝ} {q : ℝ} (hc : Convex ℝ (inputReq f q))
    (w : Fin n → ℝ) : Convex ℝ (condDemand f w q) :=
  vdemand_convex hc w

/-- **Proposition 5.C.2(v)** (MWG, p. 141), second part: if `{z ≥ 0 : f(z) ≥ q}` is strictly
convex, `z(w, q)` has at most one element (`w ≠ 0`). -/
theorem proposition_5_C_2_v_strict {f : (Fin n → ℝ) → ℝ} {q : ℝ}
    (hsc : StrictConvex ℝ (inputReq f q)) {w : Fin n → ℝ} (hw : w ≠ 0) :
    (condDemand f w q).Subsingleton :=
  vdemand_strict hsc hw

/-- **Proposition 5.C.2(vi), Shephard's lemma** (MWG, p. 141). If `Y` is closed, `w̄ ≫ 0` and
`z(w̄, q) = {z̄}`, then `c(·, q)` is differentiable at `w̄` with `∇_w c(w̄, q) = z̄`. No
convexity is needed. -/
theorem proposition_5_C_2_vi {f : (Fin n → ℝ) → ℝ} (hcl : IsClosed (singleOutputSet f))
    {w z : Fin n → ℝ} {q : ℝ} (hw : StrictlyPositive w) (hz : condDemand f w q = {z}) :
    HasFDerivAt (fun w => costFn f w q) (dualityDotCLM z) w :=
  vcost_shephard (isClosed_inputReq hcl q) (inputReq_subset_nonneg f q) hw hz

/-- **Proposition 5.C.2(vii)** (MWG, p. 141). If `Y` is closed, `w̄ ≫ 0`, `z(w, q) = {zs w}` for
`w` near `w̄` and `zs` has derivative `D` at `w̄`, then `D_w z(w̄, q) = D²_w c(w̄, q)`, symmetric
and negative semidefinite, with `D_w z(w̄, q) w̄ = 0`. -/
theorem proposition_5_C_2_vii {f : (Fin n → ℝ) → ℝ} (hcl : IsClosed (singleOutputSet f))
    {q : ℝ} {zs : (Fin n → ℝ) → (Fin n → ℝ)} {w : Fin n → ℝ} (hw : StrictlyPositive w)
    (hzs : ∀ᶠ v in 𝓝 w, condDemand f v q = {zs v})
    {D : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)} (hD : HasFDerivAt zs D w) :
    hessianMatrix (fun w => costFn f w q) w = jacobian D ∧
      (∀ i j, jacobian D i j = jacobian D j i) ∧ NegSemidef (jacobian D) ∧ D w = 0 :=
  vdemand_derivative (isClosed_inputReq hcl q) (inputReq_subset_nonneg f q) hw hzs hD

/-- If `f` is homogeneous of degree one on `ℝ^n_+`, `V(αq) = αV(q)` for `α > 0`. -/
theorem inputReq_smul {f : (Fin n → ℝ) → ℝ}
    (hf : ∀ z : Fin n → ℝ, 0 ≤ z → ∀ α : ℝ, 0 < α → f (α • z) = α * f z) {α : ℝ} (hα : 0 < α)
    (q : ℝ) : inputReq f (α * q) = (fun z => α • z) '' inputReq f q := by
  ext z
  constructor
  · rintro ⟨hz, hq⟩
    refine ⟨α⁻¹ • z, ⟨smul_nonneg (inv_nonneg.mpr hα.le) hz, ?_⟩, ?_⟩
    · rw [hf z hz α⁻¹ (inv_pos.mpr hα)]
      rw [← mul_le_mul_iff_of_pos_left hα, ← mul_assoc, mul_inv_cancel₀ hα.ne', one_mul]
      exact hq
    · simp only [smul_smul, mul_inv_cancel₀ hα.ne', one_smul]
  · rintro ⟨z', ⟨hz', hq⟩, rfl⟩
    exact ⟨smul_nonneg hα.le hz', by rw [hf z' hz' α hα]; exact mul_le_mul_of_nonneg_left hq hα.le⟩

/-- **Proposition 5.C.2(viii)** (MWG, p. 141) and **Exercise 5.C.3** (p. 161). If `f` is
homogeneous of degree one, `c(w, ·)` and `z(w, ·)` are homogeneous of degree one in `q`:
`c(w, αq) = αc(w, q)` and `z(w, αq) = αz(w, q)` for `α > 0`. -/
theorem proposition_5_C_2_viii {f : (Fin n → ℝ) → ℝ}
    (hf : ∀ z : Fin n → ℝ, 0 ≤ z → ∀ α : ℝ, 0 < α → f (α • z) = α * f z) (w : Fin n → ℝ)
    (q : ℝ) {α : ℝ} (hα : 0 < α) :
    costFn f w (α * q) = α * costFn f w q ∧
      condDemand f w (α * q) = (fun z => α • z) '' condDemand f w q := by
  have hV := inputReq_smul hf hα q
  constructor
  · unfold costFn supportFn
    rw [hV, Set.image_image]
    have : (fun z => w ⬝ᵥ (α • z)) = fun z => α * (w ⬝ᵥ z) := by
      funext z
      rw [dotProduct_smul, smul_eq_mul]
    rw [this, ← smul_eq_mul, ← Real.sInf_smul_of_nonneg hα.le]
    congr 1
    ext t
    simp [Set.mem_smul_set]
  · unfold condDemand supportArgmin
    rw [hV]
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · rintro ⟨⟨z', hz', rfl⟩, h⟩
      refine ⟨z', ⟨hz', fun y hy => ?_⟩, rfl⟩
      have := h (α • y) ⟨y, hy, rfl⟩
      simp only [dotProduct_smul, smul_eq_mul] at this
      exact le_of_mul_le_mul_left this hα
    · rintro ⟨z', ⟨hz', h⟩, rfl⟩
      refine ⟨⟨z', hz', rfl⟩, fun y hy => ?_⟩
      obtain ⟨x, hx, rfl⟩ := hy
      simp only [dotProduct_smul, smul_eq_mul]
      exact mul_le_mul_of_nonneg_left (h x hx) hα.le

/-- **Proposition 5.C.2(ix)** (MWG, p. 141) and **Exercise 5.C.3** (p. 161). If `f` is concave
on `ℝ^n_+`, then `c(w, ·)` is convex on the set of producible output levels (`w ≥ 0`); in
particular marginal costs are nondecreasing. -/
theorem proposition_5_C_2_ix {f : (Fin n → ℝ) → ℝ} (hf : ConcaveOn ℝ {z : Fin n → ℝ | 0 ≤ z} f)
    {w : Fin n → ℝ} (hw : 0 ≤ w) :
    ConvexOn ℝ {q : ℝ | (inputReq f q).Nonempty} (fun q => costFn f w q) := by
  have hconvQ : Convex ℝ {q : ℝ | (inputReq f q).Nonempty} := by
    rintro q ⟨z, hz⟩ q' ⟨z', hz'⟩ a b ha hb hab
    refine ⟨a • z + b • z', add_nonneg (smul_nonneg ha hz.1) (smul_nonneg hb hz'.1), ?_⟩
    have := hf.2 hz.1 hz'.1 ha hb hab
    simp only [smul_eq_mul] at this ⊢
    nlinarith [hz.2, hz'.2]
  refine ⟨hconvQ, fun q hq q' hq' a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  have hne : (inputReq f (a * q + b * q')).Nonempty := hconvQ hq hq' ha hb hab
  -- for any `z ∈ V(q)`, `z' ∈ V(q')`, the mixture is in `V(aq + bq')`
  have key : ∀ z ∈ inputReq f q, ∀ z' ∈ inputReq f q',
      costFn f w (a * q + b * q') ≤ a * (w ⬝ᵥ z) + b * (w ⬝ᵥ z') := by
    intro z hz z' hz'
    have hmem : a • z + b • z' ∈ inputReq f (a * q + b * q') := by
      refine ⟨add_nonneg (smul_nonneg ha hz.1) (smul_nonneg hb hz'.1), ?_⟩
      have := hf.2 hz.1 hz'.1 ha hb hab
      simp only [smul_eq_mul] at this
      nlinarith [hz.2, hz'.2]
    have := supportFn_le (bddBelow_of_subset_nonneg (inputReq_subset_nonneg f _) hw) hmem
    rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul] at this
    exact this
  -- take infima
  have hb1 := bddBelow_of_subset_nonneg (inputReq_subset_nonneg f q) hw
  have hb2 := bddBelow_of_subset_nonneg (inputReq_subset_nonneg f q') hw
  by_contra hlt
  rw [not_le] at hlt
  rcases ha.lt_or_eq with ha' | ha'
  · rcases hb.lt_or_eq with hb' | hb'
    · set d := costFn f w (a * q + b * q') - (a * costFn f w q + b * costFn f w q')
      have hd : 0 < d := by simp only [d]; linarith
      obtain ⟨_, ⟨z, hz, rfl⟩, hzlt⟩ := exists_lt_of_csInf_lt (hq.image _)
        (show costFn f w q < costFn f w q + d / (2 * a) by
          have : 0 < d / (2 * a) := by positivity
          linarith)
      obtain ⟨_, ⟨z', hz', rfl⟩, hzlt'⟩ := exists_lt_of_csInf_lt (hq'.image _)
        (show costFn f w q' < costFn f w q' + d / (2 * b) by
          have : 0 < d / (2 * b) := by positivity
          linarith)
      have h1 := key z hz z' hz'
      have e1 : a * (d / (2 * a)) = d / 2 := by field_simp
      have e2 : b * (d / (2 * b)) = d / 2 := by field_simp
      have m1 := mul_lt_mul_of_pos_left hzlt ha'
      have m2 := mul_lt_mul_of_pos_left hzlt' hb'
      simp only [mul_add] at m1 m2
      simp only [d] at e1 e2
      nlinarith
    · subst hb'
      have ha1 : a = 1 := by linarith
      subst ha1
      simp at hlt
  · subst ha'
    have hb1' : b = 1 := by linarith
    subst hb1'
    simp at hlt

/-! ### Exercise 5.C.5 -/

/-- **Exercise 5.C.5** (MWG, p. 161), first part. Property (iii) of Proposition 5.C.2 holds when
`f` is quasiconcave on `ℝ^n_+` (and `Y` is closed with free disposal): quasiconcavity is exactly
convexity of the sets `{z ≥ 0 : f(z) ≥ q}`. -/
theorem exercise_5_C_5_i {f : (Fin n → ℝ) → ℝ} (hcl : IsClosed (singleOutputSet f))
    (hfd : FreeDisposal (singleOutputSet f)) (hq : QuasiconcaveOn ℝ {z : Fin n → ℝ | 0 ≤ z} f) :
    singleOutputSet f = {y | ∀ w : Fin n → ℝ, StrictlyPositive w →
      costFnE f w (y (Fin.last n)) ≤ ((w ⬝ᵥ inputsOf y : ℝ) : EReal)} :=
  proposition_5_C_2_iii hcl hfd fun q => by
    have := hq q
    have heq : inputReq f q = {z ∈ {z : Fin n → ℝ | 0 ≤ z} | q ≤ f z} := rfl
    rw [heq]
    exact this

/-- **Exercise 5.C.5** (MWG, p. 161), second part: quasiconcavity is compatible with increasing
returns. `f(z) = (min{z₁, z₂})²` is quasiconcave on `ℝ²_+` and `f(tz) = t²f(z)`, so
`f(tz) > tf(z)` for `t > 1` whenever `f(z) > 0`. -/
theorem exercise_5_C_5_ii :
    QuasiconcaveOn ℝ {z : Fin 2 → ℝ | 0 ≤ z} (fun z => (min (z 0) (z 1)) ^ 2) ∧
      ∀ z : Fin 2 → ℝ, 0 ≤ z → ∀ t : ℝ, 1 < t → 0 < (min (z 0) (z 1)) ^ 2 →
        t * (min (z 0) (z 1)) ^ 2 < (min ((t • z) 0) ((t • z) 1)) ^ 2 := by
  constructor
  · intro r x hx y hy a b ha hb hab
    obtain ⟨hx0, hxr⟩ := hx
    obtain ⟨hy0, hyr⟩ := hy
    refine ⟨show 0 ≤ a • x + b • y from
      add_nonneg (smul_nonneg ha hx0) (smul_nonneg hb hy0), ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hmx : 0 ≤ min (x 0) (x 1) := le_min (hx0 0) (hx0 1)
    have hmy : 0 ≤ min (y 0) (y 1) := le_min (hy0 0) (hy0 1)
    have hlow : a * min (x 0) (x 1) + b * min (y 0) (y 1) ≤
        min (a * x 0 + b * y 0) (a * x 1 + b * y 1) :=
      le_min (add_le_add (mul_le_mul_of_nonneg_left (min_le_left _ _) ha)
          (mul_le_mul_of_nonneg_left (min_le_left _ _) hb))
        (add_le_add (mul_le_mul_of_nonneg_left (min_le_right _ _) ha)
          (mul_le_mul_of_nonneg_left (min_le_right _ _) hb))
    have hm := min_le_max (a := min (x 0) (x 1)) (b := min (y 0) (y 1))
    rcases le_total (min (x 0) (x 1)) (min (y 0) (y 1)) with hxy | hxy
    · have h1 : min (x 0) (x 1) ≤ a * min (x 0) (x 1) + b * min (y 0) (y 1) := by nlinarith
      calc r ≤ (min (x 0) (x 1)) ^ 2 := hxr
        _ ≤ (a * min (x 0) (x 1) + b * min (y 0) (y 1)) ^ 2 := pow_le_pow_left₀ hmx h1 2
        _ ≤ _ := pow_le_pow_left₀ (by positivity) hlow 2
    · have h1 : min (y 0) (y 1) ≤ a * min (x 0) (x 1) + b * min (y 0) (y 1) := by nlinarith
      calc r ≤ (min (y 0) (y 1)) ^ 2 := hyr
        _ ≤ (a * min (x 0) (x 1) + b * min (y 0) (y 1)) ^ 2 := pow_le_pow_left₀ hmy h1 2
        _ ≤ _ := pow_le_pow_left₀ (by positivity) hlow 2
  · intro z hz t ht hpos
    simp only [Pi.smul_apply, smul_eq_mul]
    have ht0 : 0 ≤ t := by linarith
    rw [← mul_min_of_nonneg _ _ ht0, mul_pow]
    have : t < t ^ 2 := by nlinarith
    nlinarith

end MWG.Production
