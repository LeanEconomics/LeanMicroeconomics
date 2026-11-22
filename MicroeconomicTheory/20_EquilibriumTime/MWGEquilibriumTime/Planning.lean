/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGEquilibriumTime.OneConsumer
import MWGEquilibriumTime.RamseySolowPrices
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# Equilibrium and the planning problem (MWG Section 20.D, pp. 747-749)

MWG, Chapter 20, Propositions 20.D.3-20.D.6, pp. 747-749.

The planning problem (20.D.7) maximizes `∑_t δ^t u(c_t)` over feasible bounded production paths
(`PlanOptimal`; MWG restrict all paths to be bounded, p. 744).

* **Proposition 20.D.3** (`proposition_20_D_3`): equilibrium paths solve the planning problem.
* **Proposition 20.D.4** (`proposition_20_D_4`): a planning solution with consumption bounded away
  from zero is an equilibrium for `p_t = δ^t ∇u(c_t)`, with a complete proof (MWG sketch it).
* **Proposition 20.D.5** (`proposition_20_D_5`): existence of a planning solution, by Tychonoff
  compactness of the space of paths and continuity of the discounted objective.
* **Proposition 20.D.6** (`proposition_20_D_6`): uniqueness of the planning consumption stream.

Departure. Proposition 20.D.5 assumes a uniform bound on all feasible production paths (the
alternative MWG offer on p. 744), not only on the consumption streams they generate.
-/

open Filter Topology

namespace MWG.EquilibriumTime

variable {L : ℕ}

/-- A production path is **feasible** for the endowments `ω` (MWG, p. 744): it is a path of `Y`
and sustains nonnegative consumption at every date. -/
def FeasiblePath (Y : Set (ProdPlan (Fin L))) (ω : ℕ → Fin L → ℝ) (y : ℕ → ProdPlan (Fin L)) :
    Prop :=
  IsProdPath Y y ∧ ∀ t, 0 ≤ consumption ω y t

/-- The **planning problem (20.D.7)** (MWG, p. 747): `y` is a feasible bounded path whose
consumption stream has the largest utility among all feasible bounded paths. -/
def PlanOptimal (Y : Set (ProdPlan (Fin L))) (δ : ℝ) (u : (Fin L → ℝ) → ℝ)
    (ω : ℕ → Fin L → ℝ) (y : ℕ → ProdPlan (Fin L)) : Prop :=
  FeasiblePath Y ω y ∧ BoundedPath y ∧ Summable (fun t => δ ^ t * u (consumption ω y t)) ∧
    ∀ y', FeasiblePath Y ω y' → BoundedPath y' →
      Summable (fun t => δ ^ t * u (consumption ω y' t)) →
      discountedUtility δ u (consumption ω y') ≤ discountedUtility δ u (consumption ω y)

/-- A bounded path with bounded endowments has a bounded consumption stream. -/
theorem boundedStream_consumption {ω : ℕ → Fin L → ℝ} {y : ℕ → ProdPlan (Fin L)}
    (hy : BoundedPath y) (hω : BoundedStream ω) : BoundedStream (consumption ω y) := by
  obtain ⟨α, hα⟩ := hy
  obtain ⟨M, hM⟩ := hω
  refine ⟨2 * α + M, fun t i => ?_⟩
  cases t with
  | zero =>
    simp only [consumption, netOutput, Pi.add_apply]
    have := abs_add_le ((y 0).1 i) (ω 0 i)
    linarith [(hα 0 i).1, (hα 0 i).2, hM 0 i, abs_nonneg ((y 0).2 i)]
  | succ t =>
    simp only [consumption, netOutput, Pi.add_apply]
    have h1 := abs_add_le ((y t).2 i + (y (t + 1)).1 i) (ω (t + 1) i)
    have h2 := abs_add_le ((y t).2 i) ((y (t + 1)).1 i)
    linarith [(hα t i).2, (hα (t + 1) i).1, hM (t + 1) i]

/-- **Proposition 20.D.3** (MWG, p. 747): a Walrasian equilibrium path solves the planning problem
(20.D.7). Uses inaction (`0 ∈ Y`), truncation, and nonnegative bounded endowments. -/
theorem proposition_20_D_3 {Y : Set (ProdPlan (Fin L))} (h0 : (0 : ProdPlan (Fin L)) ∈ Y)
    (htr : ∀ z ∈ Y, (z.1, 0) ∈ Y) {δ : ℝ} {u : (Fin L → ℝ) → ℝ} {ω p : ℕ → Fin L → ℝ}
    (hω0 : ∀ t, 0 ≤ ω t) (hωb : BoundedStream ω) {y : ℕ → ProdPlan (Fin L)}
    (he : WalrasEq (Set.Ici 0) Y δ u ω p y) : PlanOptimal Y δ u ω y := by
  set w := ∑' t, (periodProfit p y t + p t ⬝ᵥ ω t)
  have hnn : ∀ t, 0 ≤ periodProfit p y t + p t ⬝ᵥ ω t := by
    intro t
    have h1 : 0 ≤ periodProfit p y t := by
      have := he.myopic.2 t 0 h0
      simpa [planValue] using this
    exact add_nonneg h1 (dotProduct_nonneg_of_nonneg (he.pricesNonneg t) (hω0 t))
  refine ⟨⟨he.myopic.1, fun t => he.feasible t⟩, he.boundedPath, he.utilityMax.2.1,
    fun y' hy' hb' hs' => he.utilityMax.2.2 _ ⟨fun t => hy'.2 t,
      boundedStream_consumption hb' hωb, fun T => ?_⟩ hs'⟩
  rcases T with _ | T
  · simpa using tsum_nonneg hnn
  · -- the budget inequality, by the possibility of truncation and short-run profit maximization
    have h1 := sum_value_le_of_myopic htr he.myopic hy'.1 T
    have h2 := sum_value_netOutput p y T
    have h3 : ∑ t ∈ Finset.range (T + 1), (periodProfit p y t + p t ⬝ᵥ ω t) ≤ w :=
      he.wealthSummable.sum_le_tsum _ (fun t _ => hnn t)
    simp only [consumption, dotProduct_add, Finset.sum_add_distrib] at h3 ⊢
    linarith

/-! ### Proposition 20.D.4 -/

/-- Changing one plan of a bounded path keeps it bounded. -/
theorem BoundedPath.update {y : ℕ → ProdPlan (Fin L)} (hy : BoundedPath y) (T : ℕ)
    (z : ProdPlan (Fin L)) : BoundedPath (Function.update y T z) := by
  obtain ⟨α, hα⟩ := hy
  refine ⟨α + ‖z‖, fun t i => ?_⟩
  rcases eq_or_ne t T with rfl | ht
  · simp only [Function.update_self]
    have h1 : |z.1 i| ≤ ‖z‖ := by
      rw [← Real.norm_eq_abs]; exact (norm_le_pi_norm z.1 i).trans (norm_fst_le z)
    have h2 : |z.2 i| ≤ ‖z‖ := by
      rw [← Real.norm_eq_abs]; exact (norm_le_pi_norm z.2 i).trans (norm_snd_le z)
    have := (hα t i).1
    exact ⟨by linarith [abs_nonneg ((y t).1 i)], by linarith [abs_nonneg ((y t).1 i)]⟩
  · simp only [Function.update_of_ne ht]
    exact ⟨by linarith [(hα t i).1, norm_nonneg z], by linarith [(hα t i).2, norm_nonneg z]⟩

/-- A function with positive derivative at `0` and value `0` there is positive just to the right
of `0`. -/
theorem eventually_pos_of_hasDerivAt {g : ℝ → ℝ} {D : ℝ} (hg : HasDerivAt g D 0) (h0 : g 0 = 0)
    (hD : 0 < D) : ∀ᶠ θ in 𝓝[>] (0 : ℝ), 0 < g θ := by
  have hs := (hasDerivAt_iff_tendsto_slope.1 hg).mono_left (nhdsGT_le_nhdsNE 0)
  filter_upwards [hs.eventually (lt_mem_nhds hD), self_mem_nhdsWithin] with θ hθ hpos
  rw [slope_def_field, h0, sub_zero, sub_zero] at hθ
  exact (div_pos_iff_of_pos_right (Set.mem_Ioi.1 hpos)).1 hθ

/-- Bounds on the marginal utilities of a concave nondecreasing `u` at a point `x ≥ ε` of
`ℝ^L_+` below `(B, ..., B)`: `0 ≤ ∂_i u(x) ≤ (u(B, ..., B) - u(0)) / ε`. -/
theorem partial_bounds {u : (Fin L → ℝ) → ℝ} (hconc : ConcaveOn ℝ (Set.Ici 0) u)
    (hmono : MonotoneOn u (Set.Ici 0)) {x : Fin L → ℝ} {ε B : ℝ} (hε : 0 < ε)
    (hxε : ∀ i, ε ≤ x i) (hxB : ∀ i, x i ≤ B) {D : (Fin L → ℝ) →L[ℝ] ℝ}
    (hD : HasFDerivAt u D x) (i : Fin L) :
    0 ≤ D (Pi.single i 1) ∧ D (Pi.single i 1) ≤ (u (fun _ => B) - u 0) / ε := by
  have hx0 : (0 : Fin L → ℝ) ≤ x := fun j => hε.le.trans (hxε j)
  have he : (0 : Fin L → ℝ) ≤ Pi.single i 1 := by
    intro j; by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  constructor
  · have hxe : x ≤ x + Pi.single i 1 := le_add_of_nonneg_right he
    have g := MWG.GeneralEquilibriumExamples.concave_le_fderiv hconc (Set.mem_Ici.2 hx0)
      (Set.mem_Ici.2 (hx0.trans hxe)) hD
    have m := hmono (Set.mem_Ici.2 hx0) (Set.mem_Ici.2 (hx0.trans hxe)) hxe
    rw [add_sub_cancel_left] at g
    linarith
  · have hxm : (0 : Fin L → ℝ) ≤ x - ε • Pi.single i 1 := by
      intro j; by_cases hj : j = i
      · subst hj; simp [hxε j]
      · simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_apply, hj, ↓reduceIte, smul_eq_mul,
          mul_zero, sub_zero]
        exact hx0 j
    have g := MWG.GeneralEquilibriumExamples.concave_le_fderiv hconc (Set.mem_Ici.2 hx0)
      (Set.mem_Ici.2 hxm) hD
    rw [sub_sub_cancel_left, map_neg, map_smul, smul_eq_mul] at g
    have m1 := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hxm) hxm
    have hxB' : x ≤ fun _ => B := hxB
    have m2 := hmono (Set.mem_Ici.2 hx0) (Set.mem_Ici.2 (hx0.trans hxB')) hxB'
    rw [le_div_iff₀ hε]
    linarith

/-- **Proposition 20.D.4** (MWG, p. 748): a bounded solution of the planning problem (20.D.7) whose
consumption is bounded away from zero (`c_t ≥ ε` in every coordinate) is a Walrasian equilibrium
for the prices `p_t = δ^t ∇u(c_t)`. Here `Y` is convex, `u` is concave and nondecreasing on
`ℝ^L_+` and differentiable at every `c_t`, `0 < δ < 1`, and endowments are bounded. MWG sketch
the proof; it is given in full (prices are summable, which yields transversality, the budget
identity and, by Proposition 20.D.2, utility maximization; profit maximization follows from the
first-order term of a small convex perturbation of one plan). -/
theorem proposition_20_D_4 {Y : Set (ProdPlan (Fin L))} (hY : Convex ℝ Y) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1) {u : (Fin L → ℝ) → ℝ} (hconc : ConcaveOn ℝ (Set.Ici 0) u)
    (hmono : MonotoneOn u (Set.Ici 0)) {ω : ℕ → Fin L → ℝ} (hωb : BoundedStream ω)
    {y : ℕ → ProdPlan (Fin L)} (hopt : PlanOptimal Y δ u ω y) {ε : ℝ} (hε : 0 < ε)
    (hcε : ∀ t i, ε ≤ consumption ω y t i) {Du : ℕ → (Fin L → ℝ) →L[ℝ] ℝ}
    (hDu : ∀ t, HasFDerivAt u (Du t) (consumption ω y t)) :
    WalrasEq (Set.Ici 0) Y δ u ω (fun t i => δ ^ t * Du t (Pi.single i 1)) y := by
  set c := consumption ω y with hc
  set p : ℕ → Fin L → ℝ := fun t i => δ ^ t * Du t (Pi.single i 1) with hp
  obtain ⟨⟨hpath, hfeas⟩, hbdd, hsum, hmax⟩ := hopt
  obtain ⟨B, hB⟩ := boundedStream_consumption hbdd hωb
  set K := (u (fun _ => B) - u 0) / ε with hK
  have hpb : ∀ t i, 0 ≤ Du t (Pi.single i 1) ∧ Du t (Pi.single i 1) ≤ K := fun t i =>
    partial_bounds hconc hmono hε (hcε t) (fun j => (le_abs_self _).trans (hB t j)) (hDu t) i
  have hp0 : ∀ t, 0 ≤ p t := fun t i => mul_nonneg (pow_nonneg hδ0.le t) (hpb t i).1
  have hpsum : Summable fun t => ∑ i, p t i := by
    refine Summable.of_nonneg_of_le (fun t => Finset.sum_nonneg fun i _ => hp0 t i)
      (fun t => ?_) ((summable_geometric_of_lt_one hδ0.le hδ1).mul_right (Fintype.card (Fin L) * K))
    calc ∑ i, p t i ≤ ∑ _i : Fin L, δ ^ t * K :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hpb t i).2 (pow_nonneg hδ0.le t)
      _ = δ ^ t * (Fintype.card (Fin L) * K) := by simp; ring
  have hfoc : ∀ t v, 1 * (p t ⬝ᵥ v) = δ ^ t * Du t v := by
    intro t v
    rw [one_mul, clm_apply_eq_sum (Du t) v, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by simp only [hp]; ring
  have hpabs : ∀ t i, |p t i| ≤ K := fun t i => by
    simp only [hp]
    rw [abs_of_nonneg (mul_nonneg (pow_nonneg hδ0.le t) (hpb t i).1)]
    calc δ ^ t * Du t (Pi.single i 1) ≤ 1 * K :=
          mul_le_mul (pow_le_one₀ hδ0.le hδ1.le) (hpb t i).2 (hpb t i).1 zero_le_one
      _ = K := one_mul K
  clear_value p
  obtain ⟨α, hα⟩ := hbdd
  -- myopic profit maximization
  have hmyopic : MyopicProfitMax Y p y := by
    refine ⟨hpath, fun T z hz => ?_⟩
    by_contra hlt
    push Not at hlt
    set db := z.1 - (y T).1
    set da := z.2 - (y T).2
    set g : ℝ → ℝ := fun θ => δ ^ T * (u (c T + θ • db) - u (c T))
      + δ ^ (T + 1) * (u (c (T + 1) + θ • da) - u (c (T + 1))) with hg
    have hgd : HasDerivAt g (δ ^ T * Du T db + δ ^ (T + 1) * Du (T + 1) da) 0 := by
      have h1 : HasDerivAt (fun θ : ℝ => c T + θ • db) db 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const db).const_add (c T)
      have h2 : HasDerivAt (fun θ : ℝ => c (T + 1) + θ • da) da 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const da).const_add (c (T + 1))
      have g1 := (hDu T).comp_hasDerivAt_of_eq (0 : ℝ) h1 (by simp)
      have g2 := (hDu (T + 1)).comp_hasDerivAt_of_eq (0 : ℝ) h2 (by simp)
      have := ((g1.sub_const (u (c T))).const_mul (δ ^ T)).add
        ((g2.sub_const (u (c (T + 1)))).const_mul (δ ^ (T + 1)))
      exact this
    have hDpos : 0 < δ ^ T * Du T db + δ ^ (T + 1) * Du (T + 1) da := by
      rw [← hfoc T db, ← hfoc (T + 1) da]
      simp only [one_mul, db, da, dotProduct_sub, periodProfit, planValue] at hlt ⊢
      linarith
    have hev := eventually_pos_of_hasDerivAt hgd (by simp [hg]) hDpos
    -- small perturbations keep consumption nonnegative
    have hpos_open : IsOpen (Set.univ.pi fun _ : Fin L => Set.Ioi (0 : ℝ)) :=
      isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioi
    have hn : ∀ (x d : Fin L → ℝ), (∀ i, 0 < x i) →
        ∀ᶠ θ in 𝓝[>] (0 : ℝ), ∀ i, 0 < (x + θ • d) i := by
      intro x d hx
      have hcont : Continuous fun θ : ℝ => x + θ • d := by fun_prop
      have := hcont.continuousAt.preimage_mem_nhds (x := 0) (hpos_open.mem_nhds (by
        simp only [zero_smul, add_zero]
        exact Set.mem_univ_pi.2 fun k => Set.mem_Ioi.2 (hx k)))
      filter_upwards [nhdsWithin_le_nhds this] with θ hθ
      exact fun i => Set.mem_univ_pi.1 hθ i
    have hcpos : ∀ t i, 0 < c t i := fun t i => hε.trans_le (hcε t i)
    have hlt1 : ∀ᶠ θ in 𝓝[>] (0 : ℝ), θ < 1 :=
      nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)
    obtain ⟨θ, hgθ, hθ1, hθ2, hθlt, hθpos⟩ :=
      (hev.and ((hn _ db (hcpos T)).and ((hn _ da (hcpos (T + 1))).and
        (hlt1.and self_mem_nhdsWithin)))).exists
    have hθpos' : 0 < θ := hθpos
    -- the perturbed path
    set y' := Function.update y T ((1 - θ) • y T + θ • z) with hy'
    have hpath' : IsProdPath Y y' := fun t => by
      rcases eq_or_ne t T with rfl | ht
      · simp only [hy', Function.update_self]
        exact hY (hpath t) hz (by linarith) hθpos'.le (by ring)
      · simp only [hy', Function.update_of_ne ht]; exact hpath t
    have hc'T : consumption ω y' T = c T + θ • db := by
      funext i
      cases T with
      | zero => simp [consumption, netOutput, hy', c, db]; ring
      | succ T =>
        simp [consumption, netOutput, hy', c, db]
        ring
    have hc'T1 : consumption ω y' (T + 1) = c (T + 1) + θ • da := by
      funext i
      simp [consumption, netOutput, hy', c, da]
      ring
    have hc'other : ∀ t, t ≠ T → t ≠ T + 1 → consumption ω y' t = c t := by
      intro t h1 h2
      cases t with
      | zero => simp [consumption, netOutput, hy', c, Function.update_of_ne h1]
      | succ t =>
        have h3 : t ≠ T := fun h => h2 (by rw [h])
        simp [consumption, netOutput, hy', c, Function.update_of_ne h1, Function.update_of_ne h3]
    have hfin : ∀ t ∉ ({T, T + 1} : Finset ℕ), consumption ω y' t = c t := fun t ht => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht
      exact hc'other t ht.1 ht.2
    have hfeas' : FeasiblePath Y ω y' := by
      refine ⟨hpath', fun t => ?_⟩
      rcases eq_or_ne t T with rfl | h1
      · rw [hc'T]; exact fun i => (hθ1 i).le
      rcases eq_or_ne t (T + 1) with rfl | h2
      · rw [hc'T1]; exact fun i => (hθ2 i).le
      rw [hc'other t h1 h2]; exact hfeas t
    have hs' := summable_of_finite_change _ hfin hsum
    have hd := discountedUtility_sub_of_finite _ hfin hsum hs'
    rw [Finset.sum_pair (by omega), hc'T, hc'T1] at hd
    have := hmax y' hfeas' (BoundedPath.update ⟨α, hα⟩ T _) hs'
    simp only [hg] at hgθ
    linarith
  -- the wealth series
  have hwealth : Summable fun t => periodProfit p y t + p t ⬝ᵥ ω t := by
    obtain ⟨M, hM⟩ := hωb
    have hdot : ∀ (q v : Fin L → ℝ) (A : ℝ), 0 ≤ q → (∀ i, |v i| ≤ A) →
        |q ⬝ᵥ v| ≤ (∑ i, q i) * A := by
      intro q v A hq hv
      calc |q ⬝ᵥ v| ≤ ∑ i, |q i * v i| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i, q i * A := Finset.sum_le_sum fun i _ => by
            rw [abs_mul, abs_of_nonneg (hq i)]
            exact mul_le_mul_of_nonneg_left (hv i) (hq i)
        _ = (∑ i, q i) * A := by rw [Finset.sum_mul]
    have hps1 : Summable fun t => ∑ i, p (t + 1) i :=
      (summable_nat_add_iff (f := fun t => ∑ i, p t i) 1).2 hpsum
    refine Summable.of_norm_bounded ((hpsum.mul_right α).add ((hps1.mul_right α).add
      (hpsum.mul_right M))) fun t => ?_
    rw [Real.norm_eq_abs]
    simp only [periodProfit, planValue]
    have e1 := hdot (p t) (y t).1 α (hp0 t) fun i => (hα t i).1
    have e2 := hdot (p (t + 1)) (y t).2 α (hp0 (t + 1)) fun i => (hα t i).2
    have e3 := hdot (p t) (ω t) M (hp0 t) (hM t)
    calc |p t ⬝ᵥ (y t).1 + p (t + 1) ⬝ᵥ (y t).2 + p t ⬝ᵥ ω t|
        ≤ |p t ⬝ᵥ (y t).1| + |p (t + 1) ⬝ᵥ (y t).2| + |p t ⬝ᵥ ω t| := by
          have := abs_add_le (p t ⬝ᵥ (y t).1 + p (t + 1) ⬝ᵥ (y t).2) (p t ⬝ᵥ ω t)
          have := abs_add_le (p t ⬝ᵥ (y t).1) (p (t + 1) ⬝ᵥ (y t).2)
          linarith
      _ ≤ _ := by linarith
  -- transversality and the budget identity
  have htc : Tendsto (fun t => p (t + 1) ⬝ᵥ (y t).2) atTop (𝓝 0) :=
    tendsto_value_of_bounded (p := fun t => p (t + 1)) (v := fun t => (y t).2)
      (fun t => hp0 (t + 1)) ((summable_nat_add_iff (f := fun t => ∑ i, p t i) 1).2 hpsum)
      (fun t i => (hα t i).2)
  have hbind : HasSum (fun t => p t ⬝ᵥ c t) (∑' t, (periodProfit p y t + p t ⬝ᵥ ω t)) := by
    refine (hasSum_iff_tendsto_nat_of_nonneg
      (fun t => dotProduct_nonneg_of_nonneg (hp0 t) (hfeas t)) _).2 ?_
    have h1 := hwealth.hasSum.tendsto_sum_nat
    have h2 : Tendsto (fun T => ∑ t ∈ Finset.range (T + 1), (periodProfit p y t + p t ⬝ᵥ ω t)
        - p (T + 1) ⬝ᵥ (y T).2) atTop (𝓝 (∑' t, (periodProfit p y t + p t ⬝ᵥ ω t) - 0)) :=
      (h1.comp (tendsto_add_atTop_nat 1)).sub htc
    rw [sub_zero] at h2
    have h3 : Tendsto (fun T => ∑ t ∈ Finset.range (T + 1), p t ⬝ᵥ c t) atTop
        (𝓝 (∑' t, (periodProfit p y t + p t ⬝ᵥ ω t))) :=
      h2.congr fun T => by have := identity_20_D_1 p y ω T; simp only [c]; linarith
    exact (tendsto_add_atTop_iff_nat 1).1 h3
  refine ⟨⟨α, hα⟩, ⟨K, hpabs⟩, hp0, hfeas, hmyopic, hwealth, ?_⟩
  exact proposition_20_D_2 (fun _ h => h) hδ0.le hconc hp0 (fun t => hfeas t)
    (boundedStream_consumption ⟨α, hα⟩ hωb) hsum hbind hDu zero_le_one hfoc

/-! ### Propositions 20.D.5 and 20.D.6 -/

/-- A one-period utility continuous on `ℝ^L_+` has a convergent discounted series along every
bounded nonnegative stream. -/
theorem summable_of_continuousOn {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) {u : (Fin L → ℝ) → ℝ}
    (hu : ContinuousOn u (Set.Ici 0)) {c : ℕ → Fin L → ℝ} (hc : ∀ t, 0 ≤ c t)
    (hb : BoundedStream c) : Summable fun t => δ ^ t * u (c t) := by
  obtain ⟨M, hM⟩ := hb
  set R := max M 0
  have hK : IsCompact (Set.Ici (0 : Fin L → ℝ) ∩ Metric.closedBall 0 R) :=
    (isCompact_closedBall 0 R).inter_left isClosed_Ici
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hu.mono Set.inter_subset_left)
  refine summable_discounted hδ0 hδ1 (M := C) fun t => ?_
  have hmem : c t ∈ Set.Ici (0 : Fin L → ℝ) ∩ Metric.closedBall 0 R := by
    refine ⟨hc t, ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (pi_norm_le_iff_of_nonneg (le_max_right _ _)).2 fun i => by
      rw [Real.norm_eq_abs]; exact (hM t i).trans (le_max_left _ _)
  simpa [Real.norm_eq_abs] using hC _ hmem


/-- The consumption at a date depends continuously on the path (product topology). -/
theorem continuous_consumption (ω : ℕ → Fin L → ℝ) (t : ℕ) :
    Continuous fun y : ℕ → ProdPlan (Fin L) => consumption ω y t := by
  cases t with
  | zero =>
    simp only [consumption, netOutput]
    exact ((continuous_fst.comp (continuous_apply 0)).add continuous_const)
  | succ t =>
    simp only [consumption, netOutput]
    exact ((continuous_snd.comp (continuous_apply t)).add
      (continuous_fst.comp (continuous_apply (t + 1)))).add continuous_const

/-- The zero path consumes the endowments. -/
theorem consumption_zero (ω : ℕ → Fin L → ℝ) (t : ℕ) :
    consumption ω (fun _ => (0 : ProdPlan (Fin L))) t = ω t := by
  cases t <;> simp [consumption, netOutput]

/-- **Proposition 20.D.5** (MWG, p. 749): the planning problem (20.D.7) attains its maximum.
Hypotheses: `Y` closed with `0 ∈ Y`, endowments nonnegative and bounded, `u` continuous on
`ℝ^L_+`, `0 ≤ δ < 1`, and (departure) a uniform bound `‖y_t‖ ≤ B` on all feasible production
paths. The feasible paths form a compact set in the product topology (Tychonoff) and the
discounted objective is continuous on it (uniform convergence, by the Weierstrass M-test). -/
theorem proposition_20_D_5 {Y : Set (ProdPlan (Fin L))} (hYc : IsClosed Y)
    (h0 : (0 : ProdPlan (Fin L)) ∈ Y) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    {u : (Fin L → ℝ) → ℝ} (hu : ContinuousOn u (Set.Ici 0)) {ω : ℕ → Fin L → ℝ}
    (hω0 : ∀ t, 0 ≤ ω t) (hωb : BoundedStream ω) {B : ℝ}
    (hB : ∀ y, FeasiblePath Y ω y → ∀ t, ‖y t‖ ≤ B) :
    ∃ y, PlanOptimal Y δ u ω y := by
  set K := {y : ℕ → ProdPlan (Fin L) | FeasiblePath Y ω y} with hK
  have hclosed : IsClosed K := by
    have : K = ⋂ t, ({y : ℕ → ProdPlan (Fin L) | y t ∈ Y} ∩
        {y | 0 ≤ consumption ω y t}) := by
      ext y
      simp only [hK, FeasiblePath, IsProdPath, Set.mem_iInter, Set.mem_inter_iff]
      exact ⟨fun h t => ⟨h.1 t, h.2 t⟩, fun h => ⟨fun t => (h t).1, fun t => (h t).2⟩⟩
    rw [this]
    exact isClosed_iInter fun t => (hYc.preimage (continuous_apply t)).inter
      (isClosed_le continuous_const (continuous_consumption ω t))
  have hcompact : IsCompact K :=
    (isCompact_univ_pi fun _ => isCompact_closedBall (0 : ProdPlan (Fin L)) B).of_isClosed_subset
      hclosed fun y hy => Set.mem_univ_pi.2 fun t => by
        rw [Metric.mem_closedBall, dist_zero_right]; exact hB y hy t
  have hne : K.Nonempty := ⟨fun _ => 0, fun _ => h0, fun t => by
    rw [consumption_zero]; exact hω0 t⟩
  -- a bound on consumption, hence on utility, over `K`
  obtain ⟨M, hM⟩ := hωb
  set R := 2 * B + max M 0
  have hcR : ∀ y ∈ K, ∀ t, ‖consumption ω y t‖ ≤ R := by
    intro y hy t
    have hω : ‖ω t‖ ≤ max M 0 := (pi_norm_le_iff_of_nonneg (le_max_right _ _)).2 fun i => by
      rw [Real.norm_eq_abs]; exact (hM t i).trans (le_max_left _ _)
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB y hy 0)
    cases t with
    | zero =>
      simp only [consumption, netOutput]
      have := (norm_fst_le (y 0)).trans (hB y hy 0)
      linarith [norm_add_le (y 0).1 (ω 0)]
    | succ t =>
      simp only [consumption, netOutput]
      have h1 := (norm_snd_le (y t)).trans (hB y hy t)
      have h2 := (norm_fst_le (y (t + 1))).trans (hB y hy (t + 1))
      linarith [norm_add_le ((y t).2 + (y (t + 1)).1) (ω (t + 1)),
        norm_add_le (y t).2 (y (t + 1)).1]
  have hS : IsCompact (Set.Ici (0 : Fin L → ℝ) ∩ Metric.closedBall 0 R) :=
    (isCompact_closedBall 0 R).inter_left isClosed_Ici
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn (hu.mono Set.inter_subset_left)
  have hmemS : ∀ y ∈ K, ∀ t, consumption ω y t ∈ Set.Ici (0 : Fin L → ℝ) ∩
      Metric.closedBall 0 R := fun y hy t =>
    ⟨hy.2 t, by rw [Metric.mem_closedBall, dist_zero_right]; exact hcR y hy t⟩
  have hcont : ContinuousOn (fun y => ∑' t, δ ^ t * u (consumption ω y t)) K := by
    refine continuousOn_tsum (u := fun t => δ ^ t * C) (fun t => ?_)
      ((summable_geometric_of_lt_one hδ0 hδ1).mul_right C) (fun t y hy => ?_)
    · exact continuousOn_const.mul (hu.comp (continuous_consumption ω t).continuousOn
        fun y hy => hy.2 t)
    · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hδ0 t)]
      exact mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using hC _ (hmemS y hy t))
        (pow_nonneg hδ0 t)
  obtain ⟨y, hyK, hymax⟩ := hcompact.exists_isMaxOn hne hcont
  have hbdd : ∀ y' ∈ K, BoundedPath y' := fun y' hy' => ⟨B, fun t i => by
    constructor
    · rw [← Real.norm_eq_abs]
      exact ((norm_le_pi_norm (y' t).1 i).trans (norm_fst_le _)).trans (hB y' hy' t)
    · rw [← Real.norm_eq_abs]
      exact ((norm_le_pi_norm (y' t).2 i).trans (norm_snd_le _)).trans (hB y' hy' t)⟩
  refine ⟨y, hyK, hbdd y hyK, summable_discounted hδ0 hδ1 (M := C) fun t => ?_,
    fun y' hy' _ _ => hymax hy'⟩
  simpa [Real.norm_eq_abs] using hC _ (hmemS y hyK t)

/-- The consumption of a mixture of paths is the mixture of their consumptions. -/
theorem consumption_mix (ω : ℕ → Fin L → ℝ) (y y' : ℕ → ProdPlan (Fin L)) (t : ℕ) :
    consumption ω (fun s => (1 / 2 : ℝ) • y s + (1 / 2 : ℝ) • y' s) t
      = (1 / 2 : ℝ) • consumption ω y t + (1 / 2 : ℝ) • consumption ω y' t := by
  funext i
  cases t <;> simp [consumption, netOutput] <;> ring

/-- **Proposition 20.D.6** (MWG, p. 749): the planning problem (20.D.7) has at most one
consumption stream solution, for convex `Y`, `u` strictly concave and continuous on `ℝ^L_+`,
`0 < δ < 1` and bounded endowments. -/
theorem proposition_20_D_6 {Y : Set (ProdPlan (Fin L))} (hY : Convex ℝ Y) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1) {u : (Fin L → ℝ) → ℝ} (hu : StrictConcaveOn ℝ (Set.Ici 0) u)
    (hcont : ContinuousOn u (Set.Ici 0)) {ω : ℕ → Fin L → ℝ} (hωb : BoundedStream ω)
    {y y' : ℕ → ProdPlan (Fin L)} (h : PlanOptimal Y δ u ω y) (h' : PlanOptimal Y δ u ω y') :
    consumption ω y = consumption ω y' := by
  by_contra hne
  obtain ⟨t₀, ht₀⟩ : ∃ t, consumption ω y t ≠ consumption ω y' t := by
    by_contra hc; push Not at hc; exact hne (funext hc)
  set m : ℕ → ProdPlan (Fin L) := fun s => (1 / 2 : ℝ) • y s + (1 / 2 : ℝ) • y' s with hm
  have hcm : ∀ t, consumption ω m t
      = (1 / 2 : ℝ) • consumption ω y t + (1 / 2 : ℝ) • consumption ω y' t :=
    consumption_mix ω y y'
  have hmfeas : FeasiblePath Y ω m := by
    refine ⟨fun t => hY (h.1.1 t) (h'.1.1 t) (by norm_num) (by norm_num) (by norm_num),
      fun t => ?_⟩
    rw [hcm t]
    exact add_nonneg (smul_nonneg (by norm_num) (h.1.2 t)) (smul_nonneg (by norm_num) (h'.1.2 t))
  have hmb : BoundedPath m := by
    obtain ⟨α, hα⟩ := h.2.1
    obtain ⟨α', hα'⟩ := h'.2.1
    refine ⟨α + α', fun t i => ⟨?_, ?_⟩⟩
    · simp only [hm, Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have := abs_add_le (1 / 2 * (y t).1 i) (1 / 2 * (y' t).1 i)
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at this
      linarith [(hα t i).1, (hα' t i).1, abs_nonneg ((y t).1 i), abs_nonneg ((y' t).1 i)]
    · simp only [hm, Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have := abs_add_le (1 / 2 * (y t).2 i) (1 / 2 * (y' t).2 i)
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at this
      linarith [(hα t i).2, (hα' t i).2, abs_nonneg ((y t).2 i), abs_nonneg ((y' t).2 i)]
  have hms := summable_of_continuousOn hδ0.le hδ1 hcont hmfeas.2
    (boundedStream_consumption hmb hωb)
  have hle := h.2.2.2 m hmfeas hmb hms
  have heq : discountedUtility δ u (consumption ω y) = discountedUtility δ u (consumption ω y')
    := le_antisymm (h'.2.2.2 y h.1 h.2.1 h.2.2.1) (h.2.2.2 y' h'.1 h'.2.1 h'.2.2.1)
  have hs := h.2.2.1
  have hs' := h'.2.2.1
  have hlt : (1 / 2 : ℝ) * discountedUtility δ u (consumption ω y)
      + (1 / 2 : ℝ) * discountedUtility δ u (consumption ω y')
      < discountedUtility δ u (consumption ω m) := by
    unfold discountedUtility
    rw [← hs.tsum_mul_left, ← hs'.tsum_mul_left, ← (hs.mul_left _).tsum_add (hs'.mul_left _)]
    refine Summable.tsum_lt_tsum (i := t₀) (fun t => ?_) ?_ ((hs.mul_left _).add (hs'.mul_left _))
      hms
    · rw [hcm t]
      have hc := (StrictConcaveOn.concaveOn hu).2 (h.1.2 t) (h'.1.2 t)
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
      simp only [smul_eq_mul] at hc
      have hp := pow_nonneg hδ0.le t
      nlinarith [mul_le_mul_of_nonneg_left hc hp]
    · rw [hcm t₀]
      have hc := hu.2 (h.1.2 t₀) (h'.1.2 t₀) ht₀ (by norm_num : (0 : ℝ) < 1 / 2)
        (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
      simp only [smul_eq_mul] at hc
      have hp := pow_pos hδ0 t₀
      nlinarith [mul_lt_mul_of_pos_left hc hp]
  rw [heq] at hlt hle
  linarith

end MWG.EquilibriumTime
