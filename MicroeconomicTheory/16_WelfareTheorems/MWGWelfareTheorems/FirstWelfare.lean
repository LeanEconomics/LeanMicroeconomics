/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGWelfareTheorems.Basic
import MWGClassicalDemand.EconDebreu

/-!
# The first fundamental theorem of welfare economics (MWG Section 16.C, pp. 549-550)

* (16.C.1): at a price equilibrium with transfers anything strictly preferred to `x*ᵢ` costs more
  than `wᵢ`; (16.C.2) (Exercise 16.C.2): with locally nonsatiated (and transitive) preferences,
  anything weakly preferred costs at least `wᵢ`.
* **Proposition 16.C.1** (first welfare theorem) for price equilibria with transfers and for
  Walrasian equilibria. Only local nonsatiation and transitivity are used; no convexity.
* **Figure 16.C.1**: a price equilibrium with transfers in an Edgeworth box with a thick
  indifference "curve" that is not Pareto optimal (local nonsatiation fails).
* **Exercise 16.C.1** and the claim of p. 549: a continuous, locally nonsatiated preference has
  no nonempty closed bounded consumption set.
* **Exercise 16.C.3**: with convex consumption sets and strictly convex preferences, (a) there
  is at most one global satiation point and local nonsatiation holds everywhere else, (b) every
  price equilibrium with transfers is Pareto optimal.
* **Exercise 16.C.4**: Pareto optima for altruistic utilities `Uᵢ(u₁(x₁), ..., u_I(x_I))` are
  Pareto optima for the pleasure functions `uᵢ` (no concavity used); the converse fails.
-/

namespace MWG.WelfareTheorems

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.Production Kreps.PreferenceProperties
open MWG.CompetitiveMarkets (Allocation)

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {L : ℕ}

/-- **(16.C.1)** (MWG, p. 549). If `x*` is maximal for `≿` in `{x ∈ X : p·x ≤ w}`, every `x ∈ X`
with `x ≻ x*` has `p·x > w`. -/
theorem equation_16_C_1 {X : Set (Fin L → ℝ)} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    {p : Fin L → ℝ} {w : ℝ} {xs : Fin L → ℝ} (h : IsMaximalFor r (budgetSetOn X p w) xs)
    {x : Fin L → ℝ} (hx : x ∈ X) (hs : Strict r x xs) : w < p ⬝ᵥ x := by
  by_contra hle
  exact hs.2 (h.2 x ⟨hx, not_lt.mp hle⟩)

/-- **Exercise 16.C.2** (MWG, p. 575), property (16.C.2) of p. 549. If `≿` is locally
nonsatiated and transitive on `X` and `x*` is maximal for `≿` in `{x ∈ X : p·x ≤ w}`, then
`x ≿ x*` implies `p·x ≥ w`. -/
theorem exercise_16_C_2 {X : Set (Fin L → ℝ)} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hlns : LocallyNonsatiated X r) (htr : ∀ x ∈ X, ∀ y ∈ X, ∀ z ∈ X, r x y → r y z → r x z)
    {p : Fin L → ℝ} {w : ℝ} {xs : Fin L → ℝ} (h : IsMaximalFor r (budgetSetOn X p w) xs)
    {x : Fin L → ℝ} (hx : x ∈ X) (hpref : r x xs) : w ≤ p ⬝ᵥ x := by
  by_contra hlt
  obtain ⟨y, hy, hpy, hs⟩ := lns_exists_better_cheaper hlns p hx (not_le.mp hlt)
  have hys : r xs y := h.2 y ⟨hy, hpy.le⟩
  exact hs.2 (htr x hx xs h.1.1 y hy hpref hys)

/-- **Proposition 16.C.1 (first fundamental theorem of welfare economics)** (MWG, p. 549). If
preferences are locally nonsatiated (and, as throughout, rational) and `(x*, y*, p)` is a price
equilibrium with transfers, then `(x*, y*)` is Pareto optimal. -/
theorem proposition_16_C_1 {E : PrefEconomy ι κ L}
    (hrat : ∀ i, RationalOn (E.X i) (E.pref i))
    (hlns : ∀ i, LocallyNonsatiated (E.X i) (E.pref i)) {a : Allocation ι κ L}
    {p : Fin L → ℝ} {w : ι → ℝ} (h : E.IsPriceEqmWithTransfers a p w) : E.IsParetoOptimal a := by
  refine ⟨h.isFeasible, ?_⟩
  rintro ⟨a', ⟨⟨hx', hy'⟩, hc'⟩, hle, k, hk⟩
  have hge : ∀ i, w i ≤ p ⬝ᵥ a'.x i := fun i =>
    exercise_16_C_2 (hlns i) (hrat i).2 (h.2.2.1 i) (hx' i) (hle i)
  have hgt : w k < p ⬝ᵥ a'.x k := equation_16_C_1 (h.2.2.1 k) (hx' k) hk
  have h1 : ∑ i, w i < ∑ i, p ⬝ᵥ a'.x i :=
    Finset.sum_lt_sum (fun i _ => hge i) ⟨k, Finset.mem_univ k, hgt⟩
  have h2 : ∑ i, p ⬝ᵥ a'.x i = p ⬝ᵥ E.ω + ∑ j, p ⬝ᵥ a'.y j := by
    rw [← dotProduct_finset_sum, hc', dotProduct_add, dotProduct_finset_sum]
  have h3 : ∑ j, p ⬝ᵥ a'.y j ≤ ∑ j, p ⬝ᵥ a.y j :=
    Finset.sum_le_sum fun j _ => (h.2.1 j).2 (a'.y j) (hy' j)
  linarith [h.1]

/-- **Proposition 16.C.1** (MWG, p. 549), second part: with locally nonsatiated rational
preferences and shares summing to one, every Walrasian equilibrium allocation is Pareto
optimal. -/
theorem proposition_16_C_1_walras {E : PrivPrefEconomy ι κ L}
    (hrat : ∀ i, RationalOn (E.X i) (E.pref i))
    (hlns : ∀ i, LocallyNonsatiated (E.X i) (E.pref i)) (hθ : ∀ j, ∑ i, E.θ i j = 1)
    {a : Allocation ι κ L} {p : Fin L → ℝ} (h : E.IsWalrasEqm a p) :
    E.toEconomy.IsParetoOptimal a :=
  proposition_16_C_1 hrat hlns (h.isPriceEqmWithTransfers hθ)

/-! ## Figure 16.C.1: a thick indifference curve -/

/-- Consumer 1 of Figure 16.C.1: `u₁(x) = min(x₁ + x₂, 1)`, satiated on `{x₁ + x₂ ≥ 1}`. -/
noncomputable def fig16C1u1 (x : Fin 2 → ℝ) : ℝ := min (x 0 + x 1) 1

/-- Consumer 2 of Figure 16.C.1: `u₂(x) = x₁ + x₂`, strongly monotone. -/
def fig16C1u2 (x : Fin 2 → ℝ) : ℝ := x 0 + x 1

/-- **Figure 16.C.1** (MWG, p. 550). The Edgeworth box economy (one disposal firm) with
`ω̄ = (2, 2)` and the utilities `fig16C1u1`, `fig16C1u2`. -/
noncomputable def fig16C1Economy : PrefEconomy (Fin 2) Unit 2 :=
  PrefEconomy.ofUtility (fun _ => nonnegOrthant 2) ![fig16C1u1, fig16C1u2]
    (fun _ => nonposOrthant 2) ![2, 2]

/-- The allocation `x*` of Figure 16.C.1: `x*₁ = (3/2, 0)`, `x*₂ = (1/2, 2)`, no production. -/
noncomputable def fig16C1Eqm : Allocation (Fin 2) Unit 2 :=
  ⟨![![3 / 2, 0], ![1 / 2, 2]], fun _ => 0⟩

/-- Dot products in `ℝ²`. -/
theorem dot_two (p x : Fin 2 → ℝ) : p ⬝ᵥ x = p 0 * x 0 + p 1 * x 1 := by
  simp [dotProduct, Fin.sum_univ_two]

/-- Free disposal: at prices `p ≥ 0` no plan of `-ℝ^L₊` makes positive profit, so `0` maximizes
profit. -/
theorem zero_mem_supply_nonpos {p : Fin L → ℝ} (hp : ∀ l, 0 ≤ p l) :
    (0 : Fin L → ℝ) ∈ supply (nonposOrthant L) p := by
  refine ⟨fun _ => le_rfl, fun y hy => ?_⟩
  rw [dotProduct_zero]
  exact Finset.sum_nonpos fun l _ => mul_nonpos_of_nonneg_of_nonpos (hp l) (hy l)

/-- **Figure 16.C.1** (MWG, p. 550). `x*` with `p = (1, 1)` and wealth levels `(3/2, 5/2)` is a
price equilibrium with transfers, yet the allocation `x₁ = (1, 0)`, `x₂ = (1, 2)` Pareto dominates
it (consumer 1 is indifferent, consumer 2 strictly better off); local nonsatiation fails for
consumer 1 at `x*₁`. -/
theorem figure_16_C_1 :
    fig16C1Economy.IsPriceEqmWithTransfers fig16C1Eqm ![1, 1] ![3 / 2, 5 / 2] ∧
      ¬ fig16C1Economy.IsParetoOptimal fig16C1Eqm ∧
      ¬ LocallyNonsatiated (nonnegOrthant 2) (fig16C1Economy.pref 0) := by
  have hdot : ∀ x : Fin 2 → ℝ, (![1, 1] : Fin 2 → ℝ) ⬝ᵥ x = x 0 + x 1 := fun x => by
    rw [dot_two]; simp
  refine ⟨⟨?_, fun _ => ?_, fun i => ?_, ?_⟩, ?_, ?_⟩
  · simp [fig16C1Economy, PrefEconomy.ofUtility, fig16C1Eqm, hdot, Fin.sum_univ_two]
    norm_num
  · simpa [fig16C1Economy, PrefEconomy.ofUtility, fig16C1Eqm] using
      zero_mem_supply_nonpos (L := 2) (p := ![1, 1]) (fun l => by fin_cases l <;> simp)
  · fin_cases i
    · refine ⟨⟨fun l => ?_, ?_⟩, fun x hx => ?_⟩
      · fin_cases l <;> norm_num [fig16C1Eqm]
      · simp [fig16C1Eqm, hdot]
      · simp only [fig16C1Economy, PrefEconomy.ofUtility, utilityPref, fig16C1Eqm]
        simp [fig16C1u1]
        norm_num
    · refine ⟨⟨fun l => ?_, ?_⟩, fun x hx => ?_⟩
      · fin_cases l <;> norm_num [fig16C1Eqm]
      · simp [fig16C1Eqm, hdot]
        norm_num
      · simp only [fig16C1Economy, PrefEconomy.ofUtility, utilityPref, fig16C1Eqm]
        have := hx.2
        rw [hdot] at this
        simp [fig16C1u2]
        norm_num at this ⊢
        linarith
  · funext l
    fin_cases l <;> norm_num [fig16C1Economy, PrefEconomy.ofUtility, fig16C1Eqm, Fin.sum_univ_two]
  · rintro ⟨-, hno⟩
    refine hno ⟨⟨![![1, 0], ![1, 2]], fun _ => 0⟩, ⟨⟨fun i => ?_, fun _ => ?_⟩, ?_⟩,
      fun i => ?_, 1, ?_, ?_⟩
    · fin_cases i <;> intro l <;> fin_cases l <;> simp
    · simp [fig16C1Economy, PrefEconomy.ofUtility, nonposOrthant]
    · funext l
      fin_cases l <;> norm_num [fig16C1Economy, PrefEconomy.ofUtility, Fin.sum_univ_two]
    · fin_cases i <;>
        norm_num [fig16C1Economy, PrefEconomy.ofUtility, utilityPref, fig16C1Eqm, fig16C1u1,
          fig16C1u2]
    · simp [fig16C1Economy, PrefEconomy.ofUtility, utilityPref, fig16C1Eqm, fig16C1u2]
      norm_num
    · simp [fig16C1Economy, PrefEconomy.ofUtility, utilityPref, fig16C1Eqm, fig16C1u2]
      norm_num
  · intro hlns
    obtain ⟨y, -, -, hs⟩ := hlns ![3 / 2, 0] (fun l => by fin_cases l <;> norm_num)
      1 one_pos
    apply hs.2
    simp only [fig16C1Economy, PrefEconomy.ofUtility, utilityPref]
    simp [fig16C1u1]
    norm_num

/-! ## Exercise 16.C.1 -/

/-- **Exercise 16.C.1** (MWG, p. 575). If `X ⊆ ℝ^L` is nonempty, closed and bounded and the
(rational) preference `≿` on `X` is continuous, then `≿` is not locally nonsatiated: a continuous
utility representation (Proposition 3.C.1, Chapter 3's `proposition_3_C_1_general`) attains a
maximum on the compact set `X`. -/
theorem exercise_16_C_1 {X : Set (Fin L → ℝ)} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hne : X.Nonempty) (hcl : IsClosed X) (hb : Bornology.IsBounded X) (hr : RationalOn X r)
    (hc : PrefContinuous X r) : ¬ LocallyNonsatiated X r := by
  intro hlns
  obtain ⟨u, hu, hrep⟩ := proposition_3_C_1_general hr hc
  have hK : IsCompact X := Metric.isCompact_of_isClosed_isBounded hcl hb
  obtain ⟨x, hx, hmax⟩ := hK.exists_isMaxOn hne hu
  obtain ⟨y, hy, -, hs⟩ := hlns x hx 1 one_pos
  exact hs.2 ((hrep x hx y hy).mpr (hmax hy))

/-- **Section 16.C** (MWG, p. 549). If `≿` is continuous and locally nonsatiated, a nonempty
closed consumption set must be unbounded. -/
theorem unbounded_of_lns {X : Set (Fin L → ℝ)} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hne : X.Nonempty) (hcl : IsClosed X) (hr : RationalOn X r) (hc : PrefContinuous X r)
    (hlns : LocallyNonsatiated X r) : ¬ Bornology.IsBounded X :=
  fun hb => exercise_16_C_1 hne hcl hb hr hc hlns

/-! ## Exercise 16.C.3 -/

/-- **Exercise 16.C.3** (MWG, p. 575). Strict convexity in the form used there: `x' ≿ x` and
`x' ≠ x` imply `αx' + (1 - α)x ≻ x` for `0 < α < 1`. -/
def StrictlyConvexC3 (X : Set (Fin L → ℝ)) (r : (Fin L → ℝ) → (Fin L → ℝ) → Prop) : Prop :=
  ∀ x ∈ X, ∀ x' ∈ X, r x' x → x' ≠ x → ∀ α : ℝ, 0 < α → α < 1 →
    Strict r (α • x' + (1 - α) • x) x

/-- With a complete preference, Definition 3.B.5's strict convexity implies the form of Exercise
16.C.3. -/
theorem strictlyConvexC3_of_prefStrictlyConvex {X : Set (Fin L → ℝ)}
    {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop} (hr : RationalOn X r)
    (h : PrefStrictlyConvex X r) : StrictlyConvexC3 X r := by
  intro x hx x' hx' hxx hne α h0 h1
  have hrefl : r x x := (hr.1 x hx x hx).elim id id
  exact h x hx x' hx' x hx hxx hrefl hne α h0 h1

/-- With a rational preference on a convex set, the form of Exercise 16.C.3 implies Definition
3.B.5's strict convexity. -/
theorem prefStrictlyConvex_of_strictlyConvexC3 {X : Set (Fin L → ℝ)}
    {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop} (hX : Convex ℝ X) (hr : RationalOn X r)
    (h : StrictlyConvexC3 X r) : PrefStrictlyConvex X r := by
  intro x hx y hy z hz hyx hzx hne α h0 h1
  have hmem : α • y + (1 - α) • z ∈ X := hX hy hz h0.le (by linarith) (by ring)
  rcases hr.1 y hy z hz with hyz | hzy
  · have hs := h z hz y hy hyz hne α h0 h1
    refine ⟨hr.2 _ hmem z hz x hx hs.1 hzx, fun hxm => hs.2 (hr.2 z hz x hx _ hmem hzx hxm)⟩
  · have hs := h y hy z hz hzy (Ne.symm hne) (1 - α) (by linarith) (by linarith)
    have heq : (1 - α) • z + (1 - (1 - α)) • y = α • y + (1 - α) • z := by
      rw [sub_sub_cancel, add_comm]
    rw [heq] at hs
    refine ⟨hr.2 _ hmem y hy x hx hs.1 hyx, fun hxm => hs.2 (hr.2 y hy x hx _ hmem hyx hxm)⟩

/-- The Euclidean distance from `x` to `x + α(z - x)` is `α‖z - x‖` for `α ≥ 0`. -/
theorem euclidDist_segment {x z : Fin L → ℝ} {α : ℝ} (hα : 0 ≤ α) :
    euclidDist (α • z + (1 - α) • x) x = α * euclidDist z x := by
  unfold euclidDist
  have : ∀ l, ((α • z + (1 - α) • x) l - x l) ^ 2 = α ^ 2 * (z l - x l) ^ 2 := fun l => by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  simp only [this, ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg α), Real.sqrt_sq hα]

/-- **Exercise 16.C.3(a)** (MWG, p. 575), first part. With `X` convex and `≿` rational and
strictly convex, there is at most one global satiation point. -/
theorem exercise_16_C_3a_unique {X : Set (Fin L → ℝ)} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hX : Convex ℝ X) (h : StrictlyConvexC3 X r) {s s' : Fin L → ℝ} (hs : s ∈ X)
    (hs' : s' ∈ X) (hsat : ∀ z ∈ X, r s z) (hsat' : ∀ z ∈ X, r s' z) : s = s' := by
  by_contra hne
  have hmem : (1 / 2 : ℝ) • s' + ((1 : ℝ) - 1 / 2) • s ∈ X :=
    hX hs' hs (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 - 1 / 2) (by norm_num)
  have := h s hs s' hs' (hsat' s hs) (Ne.symm hne) (1 / 2) (by norm_num) (by norm_num)
  exact this.2 (hsat _ hmem)

/-- **Exercise 16.C.3(a)** (MWG, p. 575), second part. With `X` convex and `≿` rational and
strictly convex, `≿` is locally nonsatiated at every bundle that is not a global satiation
point. -/
theorem exercise_16_C_3a_lns {X : Set (Fin L → ℝ)} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hX : Convex ℝ X) (hr : RationalOn X r) (h : StrictlyConvexC3 X r) {x : Fin L → ℝ}
    (hx : x ∈ X) (hns : ¬ ∀ z ∈ X, r x z) :
    ∀ ε : ℝ, 0 < ε → ∃ y ∈ X, euclidDist y x ≤ ε ∧ Strict r y x := by
  intro ε hε
  push Not at hns
  obtain ⟨z, hz, hxz⟩ := hns
  have hzx : r z x := (hr.1 x hx z hz).resolve_left hxz
  have hne : z ≠ x := by
    rintro rfl
    exact hxz ((hr.1 z hz z hz).elim id id)
  have hd : 0 < euclidDist z x := by
    rcases (euclidDist_nonneg z x).lt_or_eq with h0 | h0
    · exact h0
    · exfalso
      apply hne
      funext l
      have := abs_sub_le_euclidDist z x l
      rw [← h0] at this
      linarith [abs_nonneg (z l - x l), abs_le.mp this]
  set α := min (1 / 2) (ε / euclidDist z x) with hα
  have hα0 : 0 < α := lt_min (by norm_num) (div_pos hε hd)
  have hα1 : α < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  refine ⟨α • z + (1 - α) • x, hX hz hx hα0.le (by linarith) (by ring), ?_,
    h x hx z hz hzx hne α hα0 hα1⟩
  rw [euclidDist_segment hα0.le]
  calc α * euclidDist z x ≤ ε / euclidDist z x * euclidDist z x :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) hd.le
    _ = ε := div_mul_cancel₀ ε hd.ne'

/-- **Exercise 16.C.3(b)** (MWG, p. 575). If every `Xᵢ` is convex and every `≿ᵢ` is rational and
strictly convex (in the form of the exercise; rationality is not needed), every price
equilibrium with transfers is Pareto optimal; satiation is allowed. -/
theorem exercise_16_C_3b {E : PrefEconomy ι κ L} (hX : ∀ i, Convex ℝ (E.X i))
    (hsc : ∀ i, StrictlyConvexC3 (E.X i) (E.pref i))
    {a : Allocation ι κ L} {p : Fin L → ℝ} {w : ι → ℝ} (h : E.IsPriceEqmWithTransfers a p w) :
    E.IsParetoOptimal a := by
  refine ⟨h.isFeasible, ?_⟩
  rintro ⟨a', ⟨⟨hx', hy'⟩, hc'⟩, hle, k, hk⟩
  have hge : ∀ i, p ⬝ᵥ a.x i ≤ p ⬝ᵥ a'.x i := by
    intro i
    by_cases heq : a'.x i = a.x i
    · rw [heq]
    by_contra hlt
    push Not at hlt
    have hmax := h.2.2.1 i
    have hs := hsc i (a.x i) hmax.1.1 (a'.x i) (hx' i) (hle i) heq (1 / 2) (by norm_num)
      (by norm_num)
    have hmem : (1 / 2 : ℝ) • a'.x i + ((1 : ℝ) - 1 / 2) • a.x i ∈ budgetSetOn (E.X i) p (w i) := by
      refine ⟨(hX i) (hx' i) hmax.1.1 (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (0 : ℝ) ≤ 1 - 1 / 2) (by norm_num), ?_⟩
      simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]
      have := hmax.1.2
      linarith
    exact hs.2 (hmax.2 _ hmem)
  have hgt : p ⬝ᵥ a.x k < p ⬝ᵥ a'.x k :=
    lt_of_le_of_lt (h.2.2.1 k).1.2 (equation_16_C_1 (h.2.2.1 k) (hx' k) hk)
  have h1 : ∑ i, p ⬝ᵥ a.x i < ∑ i, p ⬝ᵥ a'.x i :=
    Finset.sum_lt_sum (fun i _ => hge i) ⟨k, Finset.mem_univ k, hgt⟩
  have h2 : ∑ i, p ⬝ᵥ a'.x i = p ⬝ᵥ E.ω + ∑ j, p ⬝ᵥ a'.y j := by
    rw [← dotProduct_finset_sum, hc', dotProduct_add, dotProduct_finset_sum]
  have h2' : ∑ i, p ⬝ᵥ a.x i = p ⬝ᵥ E.ω + ∑ j, p ⬝ᵥ a.y j := by
    rw [← dotProduct_finset_sum, h.2.2.2, dotProduct_add, dotProduct_finset_sum]
  have h3 : ∑ j, p ⬝ᵥ a'.y j ≤ ∑ j, p ⬝ᵥ a.y j :=
    Finset.sum_le_sum fun j _ => (h.2.1 j).2 (a'.y j) (hy' j)
  linarith

/-! ## Exercise 16.C.4: altruism -/

/-- **Exercise 16.C.4** (MWG, p. 575). Pareto optimality for utilities `Vᵢ` defined on whole
allocations (consumption externalities). -/
def PrefEconomy.IsParetoOptimalWrt (E : PrefEconomy ι κ L)
    (V : ι → Allocation ι κ L → ℝ) (a : Allocation ι κ L) : Prop :=
  E.IsFeasible a ∧ ¬ ∃ a', E.IsFeasible a' ∧ (∀ i, V i a ≤ V i a') ∧ ∃ i, V i a < V i a'

/-- **Exercise 16.C.4** (MWG, p. 575). If every altruistic utility
`Uᵢ(x) = Wᵢ(u₁(x₁), ..., u_I(x_I))` is nondecreasing in every consumer's pleasure and strictly
increasing in `i`'s own, an allocation Pareto optimal for the `Uᵢ` is Pareto optimal for the
pleasure functions `uᵢ`. No concavity of the `uᵢ` or the `Wᵢ` is used. -/
theorem exercise_16_C_4 {X : ι → Set (Fin L → ℝ)} {u : ι → (Fin L → ℝ) → ℝ}
    {Y : κ → Set (Fin L → ℝ)} {ω : Fin L → ℝ} {W : ι → (ι → ℝ) → ℝ}
    (hmono : ∀ i, Monotone (W i))
    (hown : ∀ i (v v' : ι → ℝ), v ≤ v' → v i < v' i → W i v < W i v')
    {a : Allocation ι κ L}
    (h : (PrefEconomy.ofUtility X u Y ω).IsParetoOptimalWrt
      (fun i b => W i (fun k => u k (b.x k))) a) :
    (PrefEconomy.ofUtility X u Y ω).IsParetoOptimal a := by
  refine ⟨h.1, ?_⟩
  rintro ⟨a', ha', hle, k, hk⟩
  have hle' : (fun k => u k (a.x k)) ≤ fun k => u k (a'.x k) := fun i => hle i
  have hlt : u k (a.x k) < u k (a'.x k) := not_le.mp hk.2
  exact h.2 ⟨a', ha', fun i => hmono i hle', k, hown k _ _ hle' hlt⟩

/-- The pleasure function `x ↦ x₁` of the one-good example of Exercise 16.C.4. -/
def altruismPleasure : Fin 2 → (Fin 1 → ℝ) → ℝ := fun _ x => x 0

/-- The altruistic utilities of the example: `U₁ = v₁ + 2v₂`, `U₂ = v₁ + v₂`. -/
def altruismW : Fin 2 → (Fin 2 → ℝ) → ℝ := ![fun v => v 0 + 2 * v 1, fun v => v 0 + v 1]

/-- **Exercise 16.C.4** (MWG, p. 575): the converse fails, so competitive markets need not reach
altruistic Pareto optima. With one good, endowment `2`, `uᵢ(x) = x` and `U₁ = u₁ + 2u₂`,
`U₂ = u₁ + u₂`, giving everything to consumer 1 is Pareto optimal for the pleasure functions (and
is a Walrasian equilibrium allocation when consumer 1 owns everything) but not for the
altruistic utilities: giving everything to consumer 2 raises `U₁` and leaves `U₂` unchanged. -/
theorem exercise_16_C_4_converse_fails :
    (∀ i, Monotone (altruismW i)) ∧
    (∀ i (v v' : Fin 2 → ℝ), v ≤ v' → v i < v' i → altruismW i v < altruismW i v') ∧
    (PrefEconomy.ofUtility (fun _ => nonnegOrthant 1) altruismPleasure
        (fun _ : Unit => nonposOrthant 1) ![2]).IsParetoOptimal
      ⟨![![2], 0], fun _ => 0⟩ ∧
    ¬ (PrefEconomy.ofUtility (fun _ => nonnegOrthant 1) altruismPleasure
        (fun _ : Unit => nonposOrthant 1) ![2]).IsParetoOptimalWrt
      (fun i b => altruismW i (fun k => altruismPleasure k (b.x k))) ⟨![![2], 0], fun _ => 0⟩ := by
  refine ⟨fun i => ?_, fun i v v' hle hlt => ?_, ?_, ?_⟩
  · intro v v' hle
    have h0 := hle 0
    have h1 := hle 1
    fin_cases i <;> simp [altruismW] <;> linarith
  · have h0 := hle 0
    have h1 := hle 1
    fin_cases i <;> simp [altruismW] at hlt ⊢ <;> linarith
  · have h := paretoOptimal_all_to_one (E := PrefEconomy.ofUtility (fun _ => nonnegOrthant 1)
      altruismPleasure (fun _ : Unit => nonposOrthant 1) ![2]) (fun _ => rfl) (fun _ => rfl)
      (fun l => by fin_cases l; simp [PrefEconomy.ofUtility]) 0 ?_
    · have heq : (fun i : Fin 2 => if i = 0 then (![2] : Fin 1 → ℝ) else 0) = ![![2], 0] := by
        funext i
        fin_cases i <;> simp
      simpa [PrefEconomy.ofUtility, heq] using h
    · intro x hx y hy hxy hne
      simp only [PrefEconomy.ofUtility, utilityPref, altruismPleasure, Strict]
      have : x 0 ≠ y 0 := fun h0 => hne (funext fun l => by
        rw [Subsingleton.elim l 0]; exact h0.symm)
      have h0 := hxy 0
      exact ⟨h0, not_le.mpr (lt_of_le_of_ne h0 this)⟩
  · rintro ⟨-, hno⟩
    refine hno ⟨⟨![0, ![2]], fun _ => 0⟩, ⟨⟨fun i => ?_, fun _ => ?_⟩, ?_⟩, fun i => ?_,
      0, ?_⟩
    · fin_cases i <;> intro l <;> fin_cases l <;> simp
    · simp [PrefEconomy.ofUtility, nonposOrthant]
    · funext l
      fin_cases l
      simp [PrefEconomy.ofUtility, Fin.sum_univ_two]
    · fin_cases i <;> norm_num [altruismW, altruismPleasure]
    · simp [altruismW, altruismPleasure]

end MWG.WelfareTheorems
