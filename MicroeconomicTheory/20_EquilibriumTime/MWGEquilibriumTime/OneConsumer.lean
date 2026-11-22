/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGEquilibriumTime.Utility
import MWGEquilibriumTime.Production
import MWGGeneralEquilibriumExamples.FactorMarkets
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Equilibrium with one consumer (MWG Section 20.D, pp. 743-746)

MWG, Chapter 20, Section 20.D up to Proposition 20.D.2, pp. 743-746, with Exercises 20.D.1-20.D.4
(p. 784).

The consumer's consumption set is `X ⊆ ℝ^L` (`ℝ^L_+` in MWG; the positive orthant when the
one-period utility is logarithmic, footnote 10). The budget set at prices `p` and wealth `w` is
the set of bounded streams in `X` whose expenditure `∑_t p_t · c_t` does not exceed `w`, stated
through the partial sums (`InBudget`).

* The consumption stream of a path, `c_t = y_{a,t-1} + y_{bt} + ω_t` (`consumption`), and the
  identity **(20.D.1)** (`identity_20_D_1`).
* **Definition 20.D.1** (`WalrasEq`), with a proved instance (`example_20_D_1_ii`).
* Strict monotonicity makes the budget constraint bind (`budget_binds`).
* **Proposition 20.D.1** (`proposition_20_D_1`): equilibrium satisfies transversality.
* Condition (ii') and **Exercise 20.D.2** (`exercise_20_D_2_to`, `exercise_20_D_2_of`).
* **Definition 20.D.2** (`MyopicUtilityMax`), **Exercise 20.D.3** (`exercise_20_D_3`), the
  equivalence of (20.D.5) and (20.D.6) (`foc_20_D_5_iff_20_D_6`).
* **Proposition 20.D.2** (`proposition_20_D_2`).
* **Example 20.D.1** and **Exercise 20.D.4**: `example_20_D_1_foc`, `exercise_20_D_4`,
  `example_20_D_1_i`, `example_20_D_1_ii` (a full Walrasian equilibrium), and the correction of
  part (iii) (`example_20_D_1_iii_false`, `example_20_D_1_iii_corrected`).
* **Exercise 20.D.1**: the single budget constraint as a sequence of constraints
  (`exercise_20_D_1`).

Departures. Prices are required to be nonnegative and the wealth series to converge in
Definition 20.D.1 (MWG derives the finiteness of `w` from monotonicity). The claim in
Example 20.D.1(iii) that a fraction `δ` of wealth is invested is false for a general `F`.
-/

open Filter Topology

namespace MWG.EquilibriumTime

variable {L : ℕ}

/-- The consumption stream `c_t = y_{a,t-1} + y_{bt} + ω_t` of a path (MWG, p. 744). -/
def consumption (ω : ℕ → Fin L → ℝ) (y : ℕ → ProdPlan (Fin L)) (t : ℕ) : Fin L → ℝ :=
  netOutput y t + ω t

/-- **(20.D.1)** (MWG, p. 744): `∑_{t ≤ T} (π_t + p_t · ω_t) - ∑_{t ≤ T} p_t · c_t =
p_{T+1} · y_{aT}`. -/
theorem identity_20_D_1 (p : ℕ → Fin L → ℝ) (y : ℕ → ProdPlan (Fin L)) (ω : ℕ → Fin L → ℝ)
    (T : ℕ) :
    ∑ t ∈ Finset.range (T + 1), (periodProfit p y t + p t ⬝ᵥ ω t)
      - ∑ t ∈ Finset.range (T + 1), p t ⬝ᵥ consumption ω y t = p (T + 1) ⬝ᵥ (y T).2 := by
  have h := sum_value_netOutput p y T
  simp only [consumption, dotProduct_add, Finset.sum_add_distrib] at h ⊢
  linarith

/-- `c` lies in the budget set of prices `p` and wealth `w` (MWG, (20.D.4)): a bounded stream in
the consumption set `X` with `∑_{t < T} p_t · c_t ≤ w` for every `T`. -/
def InBudget (X : Set (Fin L → ℝ)) (p : ℕ → Fin L → ℝ) (w : ℝ) (c : ℕ → Fin L → ℝ) : Prop :=
  (∀ t, c t ∈ X) ∧ BoundedStream c ∧ ∀ T, ∑ t ∈ Finset.range T, p t ⬝ᵥ c t ≤ w

/-- `c` **maximizes utility** (20.B.1) in the budget set: it is in the budget set, its utility
series converges, and no budget-feasible stream with a convergent utility series is better. -/
def UtilityMax (X : Set (Fin L → ℝ)) (δ : ℝ) (u : (Fin L → ℝ) → ℝ) (p : ℕ → Fin L → ℝ)
    (w : ℝ) (c : ℕ → Fin L → ℝ) : Prop :=
  InBudget X p w c ∧ Summable (fun t => δ ^ t * u (c t)) ∧
    ∀ c', InBudget X p w c' → Summable (fun t => δ ^ t * u (c' t)) →
      discountedUtility δ u c' ≤ discountedUtility δ u c

/-- With nonnegative prices and consumption, the partial-sum budget constraint is the
constraint `∑_t p_t · c_t ≤ w`. -/
theorem expenditure_summable {p c : ℕ → Fin L → ℝ} (hp : ∀ t, 0 ≤ p t) (hc : ∀ t, 0 ≤ c t)
    {w : ℝ} (h : ∀ T, ∑ t ∈ Finset.range T, p t ⬝ᵥ c t ≤ w) :
    Summable (fun t => p t ⬝ᵥ c t) ∧ ∑' t, p t ⬝ᵥ c t ≤ w :=
  ⟨summable_of_sum_range_le (fun t => dotProduct_nonneg_of_nonneg (hp t) (hc t)) h,
    Real.tsum_le_of_sum_range_le (fun t => dotProduct_nonneg_of_nonneg (hp t) (hc t)) h⟩

/-- Two streams that differ only on a finite set of dates differ in utility by the finite sum
over those dates. -/
theorem discountedUtility_sub_of_finite {δ : ℝ} {u : (Fin L → ℝ) → ℝ} {c c' : ℕ → Fin L → ℝ}
    (s : Finset ℕ) (hs : ∀ t ∉ s, c' t = c t) (h : Summable fun t => δ ^ t * u (c t))
    (h' : Summable fun t => δ ^ t * u (c' t)) :
    discountedUtility δ u c' - discountedUtility δ u c
      = ∑ t ∈ s, δ ^ t * (u (c' t) - u (c t)) := by
  unfold discountedUtility
  rw [← h'.tsum_sub h]
  rw [tsum_eq_sum (s := s) (fun t ht => by rw [hs t ht]; ring)]
  exact Finset.sum_congr rfl fun t _ => by ring

/-- Changing a stream at finitely many dates keeps its utility series convergent. -/
theorem summable_of_finite_change {δ : ℝ} {u : (Fin L → ℝ) → ℝ} {c c' : ℕ → Fin L → ℝ}
    (s : Finset ℕ) (hs : ∀ t ∉ s, c' t = c t) (h : Summable fun t => δ ^ t * u (c t)) :
    Summable fun t => δ ^ t * u (c' t) := by
  have hfin : Summable fun t => if t ∈ s then δ ^ t * u (c' t) - δ ^ t * u (c t) else 0 :=
    summable_of_ne_finset_zero (s := s) (fun t ht => by simp [ht])
  refine (h.add hfin).congr fun t => ?_
  by_cases ht : t ∈ s
  · simp [ht]
  · simp [ht, hs t ht]

/-- A coordinate bump changes one coordinate by at most its size. -/
theorem abs_add_smul_single_le (x : Fin L → ℝ) (a : ℝ) (i j : Fin L) :
    |(x + a • (Pi.single i 1 : Fin L → ℝ)) j| ≤ |x j| + |a| := by
  by_cases h : j = i
  · subst h
    simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
    exact abs_add_le _ _
  · simp [h]

/-- A positive coordinate bump is a nonzero nonnegative vector. -/
theorem single_smul_pos {a : ℝ} (ha : 0 < a) (i : Fin L) :
    (0 : Fin L → ℝ) < a • Pi.single i 1 := by
  refine lt_of_le_of_ne (fun j => ?_) (fun h => ?_)
  · by_cases hj : j = i
    · subst hj; simp [ha.le]
    · simp [hj]
  · have := congrFun h i
    simp at this
    exact ha.ne' this.symm

/-- **Strict monotonicity makes the budget constraint bind** (MWG, p. 745): if `u` is strictly
increasing on an upward-closed consumption set and no budget-feasible change of `c` at date `0`
raises utility, then `∑_t p_t · c_t = w`. Prices are assumed nonnegative. -/
theorem budget_binds [NeZero L] {X : Set (Fin L → ℝ)} (hX0 : X ⊆ Set.Ici 0)
    (hXup : ∀ x ∈ X, ∀ x', x ≤ x' → x' ∈ X) {δ : ℝ} {u : (Fin L → ℝ) → ℝ}
    (hu : StrictMonoOn u X) {p : ℕ → Fin L → ℝ} (hp : ∀ t, 0 ≤ p t) {w : ℝ}
    {c : ℕ → Fin L → ℝ} (hc : InBudget X p w c) (hs : Summable fun t => δ ^ t * u (c t))
    (hmax : ∀ c', InBudget X p w c' → (∀ t, t ≠ 0 → c' t = c t) →
      discountedUtility δ u c' ≤ discountedUtility δ u c) :
    HasSum (fun t => p t ⬝ᵥ c t) w := by
  obtain ⟨hsum, hle⟩ := expenditure_summable hp (fun t => hX0 (hc.1 t)) hc.2.2
  refine (hsum.hasSum_iff).2 (le_antisymm hle ?_)
  by_contra hlt
  push Not at hlt
  set S := ∑' t, p t ⬝ᵥ c t
  set i : Fin L := 0
  set ε := (w - S) / (p 0 i + 1) with hε
  have hpi : 0 ≤ p 0 i := hp 0 i
  have hεpos : 0 < ε := div_pos (by linarith) (by linarith)
  have hεle : p 0 i * ε ≤ w - S := by
    rw [hε, mul_div_assoc']
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  set c' : ℕ → Fin L → ℝ := fun t => c t + if t = 0 then ε • Pi.single i 1 else 0 with hc'
  have hdiff : ∀ t, t ≠ 0 → c' t = c t := fun t ht => by simp [hc', ht]
  have hc'0 : c' 0 = c 0 + ε • Pi.single i 1 := by simp [hc']
  have hlt0 : c 0 < c' 0 := by
    rw [hc'0]
    exact lt_add_of_pos_right _ (single_smul_pos hεpos i)
  have hbud : InBudget X p w c' := by
    refine ⟨fun t => ?_, ?_, fun T => ?_⟩
    · rcases eq_or_ne t 0 with rfl | ht
      · exact hXup _ (hc.1 0) _ hlt0.le
      · rw [hdiff t ht]; exact hc.1 t
    · obtain ⟨M, hM⟩ := hc.2.1
      refine ⟨M + ε, fun t j => ?_⟩
      rcases eq_or_ne t 0 with rfl | ht
      · rw [hc'0]
        have := abs_add_smul_single_le (c 0) ε i j
        rw [abs_of_pos hεpos] at this
        linarith [hM 0 j]
      · rw [hdiff t ht]; linarith [hM t j]
    · have hpart : ∑ t ∈ Finset.range T, p t ⬝ᵥ c' t
          = ∑ t ∈ Finset.range T, p t ⬝ᵥ c t
            + ∑ t ∈ Finset.range T, if t = 0 then p 0 ⬝ᵥ (ε • Pi.single i 1) else 0 := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun t _ => ?_
        rcases eq_or_ne t 0 with rfl | ht
        · simp [hc', dotProduct_add]
        · simp [hc', ht]
      have hextra : (∑ t ∈ Finset.range T, if t = 0 then p 0 ⬝ᵥ (ε • Pi.single i 1) else 0)
          ≤ p 0 i * ε := by
        rw [Finset.sum_ite_eq' (Finset.range T) 0]
        split_ifs
        · simp [dotProduct_smul, dotProduct_single, mul_comm]
        · exact mul_nonneg hpi hεpos.le
      have hS : ∑ t ∈ Finset.range T, p t ⬝ᵥ c t ≤ S :=
        hsum.sum_le_tsum _ (fun t _ => dotProduct_nonneg_of_nonneg (hp t) (hX0 (hc.1 t)))
      linarith
  have hgt : discountedUtility δ u c < discountedUtility δ u c' := by
    have hs' := summable_of_finite_change {0} (fun t ht => hdiff t (by simpa using ht)) hs
    have := discountedUtility_sub_of_finite {0} (fun t ht => hdiff t (by simpa using ht)) hs hs'
    rw [Finset.sum_singleton, pow_zero, one_mul] at this
    have hu0 : u (c 0) < u (c' 0) := hu (hc.1 0) (hbud.1 0) hlt0
    linarith
  exact absurd (hmax c' hbud hdiff) (not_le.2 hgt)

variable (X : Set (Fin L → ℝ)) (Y : Set (ProdPlan (Fin L))) (δ : ℝ) (u : (Fin L → ℝ) → ℝ)
  (ω p : ℕ → Fin L → ℝ) (y : ℕ → ProdPlan (Fin L)) in
/-- **Definition 20.D.1** (MWG, p. 744): a bounded production path `y` and a bounded price
sequence `p` form a Walrasian equilibrium if (i) consumptions are feasible, (ii) the path is
myopically profit maximizing, and (iii) the consumption stream maximizes utility in the budget
set with wealth `w = ∑_t π_t + ∑_t p_t · ω_t`. Departures: prices are nonnegative and the wealth
series converges (MWG derive the finiteness of `w` from monotonicity, p. 745). -/
structure WalrasEq where
  /-- The production path is bounded. -/
  boundedPath : BoundedPath y
  /-- The price sequence is bounded. -/
  boundedPrices : ∃ B : ℝ, ∀ t i, |p t i| ≤ B
  /-- Prices are nonnegative. -/
  pricesNonneg : ∀ t, 0 ≤ p t
  /-- (i), (20.D.2): consumption is feasible. -/
  feasible : ∀ t, consumption ω y t ∈ X
  /-- (ii), (20.D.3): short-run profit maximization. -/
  myopic : MyopicProfitMax Y p y
  /-- Wealth is finite. -/
  wealthSummable : Summable fun t => periodProfit p y t + p t ⬝ᵥ ω t
  /-- (iii), (20.D.4): utility maximization in the budget set. -/
  utilityMax : UtilityMax X δ u p (∑' t, (periodProfit p y t + p t ⬝ᵥ ω t)) (consumption ω y)

/-- **Proposition 20.D.1** (MWG, p. 745): at a Walrasian equilibrium (with a strictly increasing
one-period utility on an upward-closed consumption set in `ℝ^L_+`), the transversality condition
`p_{t+1} · y_{at} → 0` holds. -/
theorem proposition_20_D_1 [NeZero L] {X : Set (Fin L → ℝ)} (hX0 : X ⊆ Set.Ici 0)
    (hXup : ∀ x ∈ X, ∀ x', x ≤ x' → x' ∈ X) {Y : Set (ProdPlan (Fin L))} {δ : ℝ}
    {u : (Fin L → ℝ) → ℝ} (hu : StrictMonoOn u X) {ω p : ℕ → Fin L → ℝ}
    {y : ℕ → ProdPlan (Fin L)} (he : WalrasEq X Y δ u ω p y) : Transversality p y := by
  set w := ∑' t, (periodProfit p y t + p t ⬝ᵥ ω t)
  have hexp : HasSum (fun t => p t ⬝ᵥ consumption ω y t) w :=
    budget_binds hX0 hXup hu he.pricesNonneg he.utilityMax.1 he.utilityMax.2.1
      fun c' hc' _ => he.utilityMax.2.2 c' hc'
        (summable_of_finite_change {0} (fun t ht => by simp_all) he.utilityMax.2.1)
  have h1 := he.wealthSummable.hasSum.tendsto_sum_nat
  have h2 := hexp.tendsto_sum_nat
  have h3 : Tendsto (fun T => ∑ t ∈ Finset.range (T + 1), (periodProfit p y t + p t ⬝ᵥ ω t)
      - ∑ t ∈ Finset.range (T + 1), p t ⬝ᵥ consumption ω y t) atTop (𝓝 (w - w)) :=
    (h1.comp (tendsto_add_atTop_nat 1)).sub (h2.comp (tendsto_add_atTop_nat 1))
  rw [sub_self] at h3
  unfold Transversality
  exact h3.congr fun T => identity_20_D_1 p y ω T

/-- **Condition (ii')** (MWG, p. 745): the path maximizes total profits: the profit series
converges and, for every path and every horizon `T`, the profits up to `T` do not exceed the
total profits of `y`. -/
def TotalProfitMax (Y : Set (ProdPlan (Fin L))) (p : ℕ → Fin L → ℝ) (y : ℕ → ProdPlan (Fin L)) :
    Prop :=
  IsProdPath Y y ∧ Summable (periodProfit p y) ∧
    ∀ y', IsProdPath Y y' → ∀ T, ∑ t ∈ Finset.range (T + 1), periodProfit p y' t ≤
      ∑' t, periodProfit p y t

/-- **Exercise 20.D.2**, first part (MWG, p. 784): condition (ii') implies condition (ii). -/
theorem exercise_20_D_2_to {Y : Set (ProdPlan (Fin L))} {p : ℕ → Fin L → ℝ}
    {y : ℕ → ProdPlan (Fin L)} (h : TotalProfitMax Y p y) : MyopicProfitMax Y p y := by
  refine ⟨h.1, fun t z hz => ?_⟩
  by_contra hlt
  push Not at hlt
  set y' := Function.update y t z with hy'
  have hpath : IsProdPath Y y' := fun s => by
    rcases eq_or_ne s t with rfl | hs
    · simpa [hy'] using hz
    · simpa [hy', hs] using h.1 s
  set g := planValue (p t) (p (t + 1)) z - periodProfit p y t with hg
  have hgpos : 0 < g := by rw [hg]; linarith
  have hsplit : ∀ T, t ≤ T → ∑ s ∈ Finset.range (T + 1), periodProfit p y' s
      = ∑ s ∈ Finset.range (T + 1), periodProfit p y s + g := by
    intro T hT
    rw [← Finset.sum_erase_add _ _ (Finset.mem_range.2 (Nat.lt_succ_of_le hT)),
      ← Finset.sum_erase_add (s := Finset.range (T + 1)) (f := periodProfit p y)
        (Finset.mem_range.2 (Nat.lt_succ_of_le hT))]
    have he : ∑ s ∈ (Finset.range (T + 1)).erase t, periodProfit p y' s
        = ∑ s ∈ (Finset.range (T + 1)).erase t, periodProfit p y s :=
      Finset.sum_congr rfl fun s hs => by
        simp [periodProfit, hy', Finset.ne_of_mem_erase hs]
    rw [he, hg]
    simp [periodProfit, hy']
  have hlim := (h.2.1.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)).add_const g
  have hbound : ∀ T, t ≤ T →
      ∑ s ∈ Finset.range (T + 1), periodProfit p y s + g ≤ ∑' s, periodProfit p y s :=
    fun T hT => (hsplit T hT) ▸ h.2.2 y' hpath T
  have := le_of_tendsto hlim (eventually_atTop.2 ⟨t, hbound⟩)
  linarith

/-- **Exercise 20.D.2**, second part (MWG, p. 784): condition (ii), with `0 ∈ Y` (assumption (ii)
of Section 20.C) and a convergent profit series (part of `w < ∞`), implies condition (ii'). -/
theorem exercise_20_D_2_of {Y : Set (ProdPlan (Fin L))} (h0 : (0 : ProdPlan (Fin L)) ∈ Y)
    {p : ℕ → Fin L → ℝ} {y : ℕ → ProdPlan (Fin L)} (h : MyopicProfitMax Y p y)
    (hs : Summable (periodProfit p y)) : TotalProfitMax Y p y := by
  refine ⟨h.1, hs, fun y' hy' T => ?_⟩
  have hnn : ∀ t, 0 ≤ periodProfit p y t := fun t => by
    have := h.2 t 0 h0
    simpa [planValue] using this
  calc ∑ t ∈ Finset.range (T + 1), periodProfit p y' t
      ≤ ∑ t ∈ Finset.range (T + 1), periodProfit p y t :=
        Finset.sum_le_sum fun t _ => h.2 t _ (hy' t)
    _ ≤ ∑' t, periodProfit p y t := hs.sum_le_tsum _ (fun t _ => hnn t)

/-- **Definition 20.D.2** (MWG, p. 745): `c` is myopically (short-run) utility maximizing in the
budget set of `p` and `w` if no budget-feasible stream differing from `c` only at two consecutive
dates `t, t+1` gives higher utility. -/
def MyopicUtilityMax (X : Set (Fin L → ℝ)) (δ : ℝ) (u : (Fin L → ℝ) → ℝ)
    (p : ℕ → Fin L → ℝ) (w : ℝ) (c : ℕ → Fin L → ℝ) : Prop :=
  InBudget X p w c ∧ Summable (fun t => δ ^ t * u (c t)) ∧
    ∀ t c', InBudget X p w c' → (∀ s, s ≠ t → s ≠ t + 1 → c' s = c s) →
      discountedUtility δ u c' ≤ discountedUtility δ u c

/-- A continuous linear functional on `ℝ^L` is the sum of its partial derivatives weighted by
the coordinates. -/
theorem clm_apply_eq_sum (D : (Fin L → ℝ) →L[ℝ] ℝ) (v : Fin L → ℝ) :
    D v = ∑ i, v i * D (Pi.single i 1) := by
  conv_lhs => rw [show v = ∑ i, v i • (Pi.single i 1 : Fin L → ℝ) by
    funext j; simp [Finset.sum_apply, Pi.single_apply]]
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul]

/-- The conditions **(20.D.5)** (MWG, p. 745): for every `t` there is `λ_t > 0` with
`λ_t p_t = ∇u(c_t)` and `λ_t p_{t+1} = δ ∇u(c_{t+1})`. -/
def Foc20D5 (δ : ℝ) (p : ℕ → Fin L → ℝ) (Du : ℕ → (Fin L → ℝ) →L[ℝ] ℝ) : Prop :=
  ∀ t, ∃ lam : ℝ, 0 < lam ∧ (∀ v, lam * (p t ⬝ᵥ v) = Du t v) ∧
    ∀ v, lam * (p (t + 1) ⬝ᵥ v) = δ * Du (t + 1) v

/-- The conditions **(20.D.6)** (MWG, p. 746): for some `λ > 0`, `λ p_t = δ^t ∇u(c_t)` for all
`t`. -/
def Foc20D6 (δ : ℝ) (p : ℕ → Fin L → ℝ) (Du : ℕ → (Fin L → ℝ) →L[ℝ] ℝ) : Prop :=
  ∃ lam : ℝ, 0 < lam ∧ ∀ t v, lam * (p t ⬝ᵥ v) = δ ^ t * Du t v

/-- **(20.D.5) is equivalent to (20.D.6)** (MWG, pp. 745-746), for `δ > 0` and nonzero prices:
`λ_{t-1} = δ λ_t`, so `λ = λ_0` works. -/
theorem foc_20_D_5_iff_20_D_6 {δ : ℝ} (hδ : 0 < δ) {p : ℕ → Fin L → ℝ}
    (hp : ∀ t, p t ≠ 0) {Du : ℕ → (Fin L → ℝ) →L[ℝ] ℝ} :
    Foc20D5 δ p Du ↔ Foc20D6 δ p Du := by
  constructor
  · intro h
    choose lam hlam h1 h2 using h
    -- `λ_t = δ λ_{t+1}`
    have hrec : ∀ t, lam t = δ * lam (t + 1) := by
      intro t
      obtain ⟨i, hi⟩ : ∃ i, p (t + 1) i ≠ 0 := by
        by_contra hc; push Not at hc; exact hp (t + 1) (funext hc)
      have e1 := h2 t (Pi.single i 1)
      have e2 := h1 (t + 1) (Pi.single i 1)
      simp only [dotProduct_single, mul_one] at e1 e2
      have : lam t * p (t + 1) i = δ * lam (t + 1) * p (t + 1) i := by rw [e1, ← e2]; ring
      exact mul_right_cancel₀ hi this
    have hpow : ∀ t, lam 0 = δ ^ t * lam t := by
      intro t
      induction t with
      | zero => simp
      | succ t ih => rw [ih, hrec t, pow_succ]; ring
    refine ⟨lam 0, hlam 0, fun t v => ?_⟩
    rw [hpow t, mul_assoc, h1 t v]
  · rintro ⟨lam, hlam, h⟩
    refine fun t => ⟨lam / δ ^ t, div_pos hlam (pow_pos hδ t), fun v => ?_, fun v => ?_⟩
    · rw [div_mul_eq_mul_div, h t v]
      field_simp
    · rw [div_mul_eq_mul_div, h (t + 1) v, pow_succ]
      field_simp

/-- **Exercise 20.D.3** (MWG, p. 745): a strictly positive bounded stream `c ≫ 0` is myopically
utility maximizing for `p` and `w` if and only if `∑_t p_t · c_t = w` and the first-order
conditions (20.D.5) hold. Here `u` is concave and strictly increasing on `ℝ^L_+`, differentiable
at every `c_t` with strictly positive marginal utilities, and `0 < δ`. -/
theorem exercise_20_D_3 [NeZero L] {δ : ℝ} (hδ : 0 < δ) {u : (Fin L → ℝ) → ℝ}
    (hconc : ConcaveOn ℝ (Set.Ici 0) u) (hmono : StrictMonoOn u (Set.Ici 0))
    {c : ℕ → Fin L → ℝ} (hc : ∀ t, StrictPos (c t)) (hb : BoundedStream c)
    (hs : Summable fun t => δ ^ t * u (c t)) {Du : ℕ → (Fin L → ℝ) →L[ℝ] ℝ}
    (hDu : ∀ t, HasFDerivAt u (Du t) (c t)) (hDpos : ∀ t i, 0 < Du t (Pi.single i 1))
    {p : ℕ → Fin L → ℝ} {w : ℝ} :
    MyopicUtilityMax (Set.Ici 0) δ u p w c ↔
      HasSum (fun t => p t ⬝ᵥ c t) w ∧ Foc20D5 δ p Du := by
  have hc0 : ∀ t, 0 ≤ c t := fun t i => (hc t i).le
  constructor
  · rintro ⟨hbud, -, hmax⟩
    -- prices are strictly positive
    have hppos : ∀ t i, 0 < p t i := by
      intro t i
      by_contra hneg
      push Not at hneg
      set c' : ℕ → Fin L → ℝ := fun s => c s + if s = t then (1 : ℝ) • Pi.single i 1 else 0
        with hc'
      have hdiff : ∀ s, s ≠ t → c' s = c s := fun s hs => by simp [hc', hs]
      have hc't : c' t = c t + (1 : ℝ) • Pi.single i 1 := by simp [hc']
      have hlt : c t < c' t := by
        rw [hc't]; exact lt_add_of_pos_right _ (single_smul_pos one_pos i)
      have hbud' : InBudget (Set.Ici 0) p w c' := by
        refine ⟨fun s => ?_, ?_, fun T => ?_⟩
        · rcases eq_or_ne s t with rfl | hs
          · exact Set.mem_Ici.2 ((hc0 s).trans hlt.le)
          · rw [hdiff s hs]; exact hc0 s
        · obtain ⟨M, hM⟩ := hb
          refine ⟨M + 1, fun s j => ?_⟩
          rcases eq_or_ne s t with rfl | hs
          · rw [hc't]
            have := abs_add_smul_single_le (c s) 1 i j
            rw [abs_one] at this
            linarith [hM s j]
          · rw [hdiff s hs]; linarith [hM s j]
        · have hle : ∑ s ∈ Finset.range T, p s ⬝ᵥ c' s ≤ ∑ s ∈ Finset.range T, p s ⬝ᵥ c s := by
            refine Finset.sum_le_sum fun s _ => ?_
            rcases eq_or_ne s t with rfl | hs
            · rw [hc't, dotProduct_add, dotProduct_smul, dotProduct_single, mul_one, one_smul]
              linarith
            · rw [hdiff s hs]
          exact hle.trans (hbud.2.2 T)
      have hs' := summable_of_finite_change {t} (fun s hst => hdiff s (by simpa using hst)) hs
      have hd := discountedUtility_sub_of_finite {t}
        (fun s hst => hdiff s (by simpa using hst)) hs hs'
      rw [Finset.sum_singleton] at hd
      have hu := hmono (Set.mem_Ici.2 (hc0 t)) (Set.mem_Ici.2 ((hc0 t).trans hlt.le)) hlt
      have := hmax t c' hbud' (fun s hs _ => hdiff s hs)
      have : 0 < δ ^ t * (u (c' t) - u (c t)) := mul_pos (pow_pos hδ t) (by linarith)
      linarith
    have hp0 : ∀ t, 0 ≤ p t := fun t i => (hppos t i).le
    have hbind : HasSum (fun t => p t ⬝ᵥ c t) w :=
      budget_binds (fun _ h => h) (fun x hx x' hxx' => Set.mem_Ici.2 ((Set.mem_Ici.1 hx).trans
        hxx')) hmono hp0 hbud hs
        (fun c' hc' hdiff => hmax 0 c' hc' (fun s hs _ => hdiff s hs))
    have hpos_open : IsOpen (Set.univ.pi fun _ : Fin L => Set.Ioi (0 : ℝ)) :=
      isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioi
    refine ⟨hbind, fun t => ?_⟩
    -- the cross-date first-order conditions
    have hcross : ∀ i j, p (t + 1) j * Du t (Pi.single i 1)
        = δ * p t i * Du (t + 1) (Pi.single j 1) := by
      intro i j
      set v : Fin L → ℝ := p (t + 1) j • Pi.single i 1 with hv
      set v' : Fin L → ℝ := -(p t i • Pi.single j 1) with hv'
      set φ : ℝ → ℝ := fun θ => δ ^ t * u (c t + θ • v) + δ ^ (t + 1) * u (c (t + 1) + θ • v')
        with hφdef
      have hφ : HasDerivAt φ (δ ^ t * Du t v + δ ^ (t + 1) * Du (t + 1) v') 0 := by
        have h1 : HasDerivAt (fun θ : ℝ => c t + θ • v) v 0 := by
          simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add (c t)
        have h2 : HasDerivAt (fun θ : ℝ => c (t + 1) + θ • v') v' 0 := by
          simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v').const_add (c (t + 1))
        have g1 := (hDu t).comp_hasDerivAt_of_eq (0 : ℝ) h1 (by simp)
        have g2 := (hDu (t + 1)).comp_hasDerivAt_of_eq (0 : ℝ) h2 (by simp)
        exact (g1.const_mul _).add (g2.const_mul _)
      have hloc : IsLocalMax φ 0 := by
        have hcont1 : Continuous fun θ : ℝ => c t + θ • v := by fun_prop
        have hcont2 : Continuous fun θ : ℝ => c (t + 1) + θ • v' := by fun_prop
        have hn1 : ∀ᶠ θ in 𝓝 (0 : ℝ), c t + θ • v ∈ Set.univ.pi fun _ => Set.Ioi 0 :=
          hcont1.continuousAt.preimage_mem_nhds (hpos_open.mem_nhds (by
            simp only [zero_smul, add_zero]
            exact Set.mem_univ_pi.2 fun k => Set.mem_Ioi.2 (hc t k)))
        have hn2 : ∀ᶠ θ in 𝓝 (0 : ℝ), c (t + 1) + θ • v' ∈ Set.univ.pi fun _ => Set.Ioi 0 :=
          hcont2.continuousAt.preimage_mem_nhds (hpos_open.mem_nhds (by
            simp only [zero_smul, add_zero]
            exact Set.mem_univ_pi.2 fun k => Set.mem_Ioi.2 (hc (t + 1) k)))
        filter_upwards [hn1, hn2] with θ hθ1 hθ2
        rw [Set.mem_univ_pi] at hθ1 hθ2
        set c' : ℕ → Fin L → ℝ := fun s => c s + (if s = t then θ • v else 0)
          + (if s = t + 1 then θ • v' else 0) with hc'
        have ht1 : t + 1 ≠ t := by omega
        have hc't : c' t = c t + θ • v := by simp [hc']
        have hc't1 : c' (t + 1) = c (t + 1) + θ • v' := by simp [hc']
        have hdiff : ∀ s, s ≠ t → s ≠ t + 1 → c' s = c s := fun s h1 h2 => by
          simp [hc', h1, h2]
        have hcnn : ∀ s, 0 ≤ c' s := fun s => by
          rcases eq_or_ne s t with rfl | h1
          · rw [hc't]; exact fun k => (hθ1 k).le
          rcases eq_or_ne s (t + 1) with rfl | h2
          · rw [hc't1]; exact fun k => (hθ2 k).le
          rw [hdiff s h1 h2]; exact hc0 s
        have hcost : p t ⬝ᵥ (θ • v) + p (t + 1) ⬝ᵥ (θ • v') = 0 := by
          simp only [hv, hv', dotProduct_smul, dotProduct_neg, dotProduct_single, smul_eq_mul,
            mul_one]
          ring
        have hbud' : InBudget (Set.Ici 0) p w c' := by
          refine ⟨hcnn, ?_, ?_⟩
          · obtain ⟨M, hM⟩ := hb
            refine ⟨M + |θ * p (t + 1) j| + |θ * -p t i|, fun s k => ?_⟩
            have hv1 : θ • v = (θ * p (t + 1) j) • (Pi.single i 1 : Fin L → ℝ) := by
              rw [hv, smul_smul]
            have hv2 : θ • v' = (θ * -p t i) • (Pi.single j 1 : Fin L → ℝ) := by
              rw [hv', smul_neg, smul_smul, ← neg_smul, mul_neg]
            rcases eq_or_ne s t with rfl | h1
            · rw [hc't, hv1]
              have := abs_add_smul_single_le (c s) (θ * p (s + 1) j) i k
              linarith [hM s k, abs_nonneg (θ * -p s i)]
            rcases eq_or_ne s (t + 1) with rfl | h2
            · rw [hc't1, hv2]
              have := abs_add_smul_single_le (c (t + 1)) (θ * -p t i) j k
              linarith [hM (t + 1) k, abs_nonneg (θ * p (t + 1) j)]
            rw [hdiff s h1 h2]
            linarith [hM s k, abs_nonneg (θ * p (t + 1) j), abs_nonneg (θ * -p t i)]
          · have hsum' : HasSum (fun s => p s ⬝ᵥ c' s) w := by
              have hfin : HasSum (fun s => (if s = t then p t ⬝ᵥ (θ • v) else 0)
                  + (if s = t + 1 then p (t + 1) ⬝ᵥ (θ • v') else 0)) 0 := by
                have := (hasSum_ite_eq t (p t ⬝ᵥ (θ • v))).add
                  (hasSum_ite_eq (t + 1) (p (t + 1) ⬝ᵥ (θ • v')))
                rwa [hcost] at this
              have := hbind.add hfin
              rw [add_zero] at this
              refine this.congr_fun fun s => ?_
              simp only [hc', dotProduct_add]
              split_ifs <;> simp_all
            intro T
            rw [← hsum'.tsum_eq]
            exact hsum'.summable.sum_le_tsum _
              (fun s _ => dotProduct_nonneg_of_nonneg (hp0 s) (hcnn s))
        have hfs : ∀ s ∉ ({t, t + 1} : Finset ℕ), c' s = c s := fun s hst => by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hst
          exact hdiff s hst.1 hst.2
        have hs' := summable_of_finite_change _ hfs hs
        have hd := discountedUtility_sub_of_finite _ hfs hs hs'
        rw [Finset.sum_pair (by omega), hc't, hc't1] at hd
        have hle := hmax t c' hbud' hdiff
        simp only [hφdef, zero_smul, add_zero]
        nlinarith
      have h0 := hloc.hasDerivAt_eq_zero hφ
      simp only [hv, hv', map_smul, map_neg, smul_eq_mul, pow_succ] at h0
      have hδt : 0 < δ ^ t := pow_pos hδ t
      have : δ ^ t * (p (t + 1) j * Du t (Pi.single i 1)
          - δ * (p t i * Du (t + 1) (Pi.single j 1))) = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h hδt.ne'
      · linarith
    obtain ⟨i₀⟩ : Nonempty (Fin L) := inferInstance
    have hratio : ∀ i, Du t (Pi.single i 1) * p t i₀ = p t i * Du t (Pi.single i₀ 1) := by
      intro i
      have h1 := hcross i₀ i₀
      have h2 := hcross i i₀
      have : p (t + 1) i₀ * (Du t (Pi.single i 1) * p t i₀)
          = p (t + 1) i₀ * (p t i * Du t (Pi.single i₀ 1)) := by
        linear_combination (p t i₀) * h2 - (p t i) * h1
      exact mul_left_cancel₀ (hppos (t + 1) i₀).ne' this
    have hp0' := (hppos t i₀).ne'
    refine ⟨Du t (Pi.single i₀ 1) / p t i₀, div_pos (hDpos t i₀) (hppos t i₀), fun v => ?_,
      fun v => ?_⟩
    · rw [clm_apply_eq_sum (Du t) v, dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [div_mul_eq_mul_div, div_eq_iff hp0']
      linear_combination (-(v i)) * hratio i
    · rw [clm_apply_eq_sum (Du (t + 1)) v, dotProduct, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [div_mul_eq_mul_div, div_eq_iff hp0']
      linear_combination (v j) * hcross i₀ j
  · rintro ⟨hbind, hfoc⟩
    have hppos : ∀ t i, 0 < p t i := by
      intro t i
      obtain ⟨lam, hlam, h1, -⟩ := hfoc t
      have := h1 (Pi.single i 1)
      rw [dotProduct_single, mul_one] at this
      have := hDpos t i
      nlinarith
    have hp0 : ∀ t, 0 ≤ p t := fun t i => (hppos t i).le
    have hbud : InBudget (Set.Ici 0) p w c := by
      refine ⟨fun t => hc0 t, hb, fun T => ?_⟩
      rw [← hbind.tsum_eq]
      exact hbind.summable.sum_le_tsum _
        (fun s _ => dotProduct_nonneg_of_nonneg (hp0 s) (hc0 s))
    refine ⟨hbud, hs, fun t c' hc' hdiff => ?_⟩
    obtain ⟨lam, hlam, h1, h2⟩ := hfoc t
    have hfinset : ∀ s ∉ ({t, t + 1} : Finset ℕ), c' s = c s := fun s hst => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hst
      exact hdiff s hst.1 hst.2
    have hs' := summable_of_finite_change _ hfinset hs
    have hd := discountedUtility_sub_of_finite _ hfinset hs hs'
    rw [Finset.sum_pair (by omega)] at hd
    -- the expenditure of `c'` is at most `w`
    obtain ⟨hsum', hle'⟩ := expenditure_summable hp0 (fun s => hc'.1 s) hc'.2.2
    have hcost : p t ⬝ᵥ (c' t - c t) + p (t + 1) ⬝ᵥ (c' (t + 1) - c (t + 1)) ≤ 0 := by
      have heq : ∑' s, p s ⬝ᵥ c' s - ∑' s, p s ⬝ᵥ c s
          = p t ⬝ᵥ (c' t - c t) + p (t + 1) ⬝ᵥ (c' (t + 1) - c (t + 1)) := by
        rw [← hsum'.tsum_sub hbind.summable,
          tsum_eq_sum (s := {t, t + 1}) (fun s hs => by rw [hfinset s hs, sub_self]),
          Finset.sum_pair (by omega), dotProduct_sub, dotProduct_sub]
      rw [← heq, hbind.tsum_eq]
      linarith
    have g1 := MWG.GeneralEquilibriumExamples.concave_le_fderiv hconc (Set.mem_Ici.2 (hc0 t))
      (hc'.1 t) (hDu t)
    have g2 := MWG.GeneralEquilibriumExamples.concave_le_fderiv hconc
      (Set.mem_Ici.2 (hc0 (t + 1))) (hc'.1 (t + 1)) (hDu (t + 1))
    rw [← h1] at g1
    have e2 := h2 (c' (t + 1) - c (t + 1))
    have hδt : 0 < δ ^ t := pow_pos hδ t
    have key : δ ^ t * (u (c' t) - u (c t)) + δ ^ (t + 1) * (u (c' (t + 1)) - u (c (t + 1)))
        ≤ δ ^ t * (lam * (p t ⬝ᵥ (c' t - c t) + p (t + 1) ⬝ᵥ (c' (t + 1) - c (t + 1)))) := by
      rw [pow_succ]
      have : δ * (u (c' (t + 1)) - u (c (t + 1))) ≤ lam * (p (t + 1) ⬝ᵥ (c' (t + 1) - c (t + 1)))
          := by rw [e2]; nlinarith
      nlinarith
    have : δ ^ t * (lam * (p t ⬝ᵥ (c' t - c t) + p (t + 1) ⬝ᵥ (c' (t + 1) - c (t + 1)))) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hδt.le (mul_nonpos_of_nonneg_of_nonpos hlam.le hcost)
    linarith

/-- **Proposition 20.D.2** (MWG, p. 746): if `∑_t p_t · c_t = w < ∞` and (20.D.6) holds, then `c`
maximizes utility in the budget set of `p` and `w`. Proved for a one-period utility concave on a
convex consumption set `X ⊆ ℝ^L_+` and differentiable at every `c_t`, with nonnegative prices. -/
theorem proposition_20_D_2 {X : Set (Fin L → ℝ)} (hX0 : X ⊆ Set.Ici 0) {δ : ℝ} (hδ : 0 ≤ δ)
    {u : (Fin L → ℝ) → ℝ} (hconc : ConcaveOn ℝ X u) {p : ℕ → Fin L → ℝ} (hp : ∀ t, 0 ≤ p t)
    {w : ℝ} {c : ℕ → Fin L → ℝ} (hcX : ∀ t, c t ∈ X) (hb : BoundedStream c)
    (hs : Summable fun t => δ ^ t * u (c t)) (hbind : HasSum (fun t => p t ⬝ᵥ c t) w)
    {Du : ℕ → (Fin L → ℝ) →L[ℝ] ℝ} (hDu : ∀ t, HasFDerivAt u (Du t) (c t)) {lam : ℝ}
    (hlam : 0 ≤ lam) (hfoc : ∀ t v, lam * (p t ⬝ᵥ v) = δ ^ t * Du t v) :
    UtilityMax X δ u p w c := by
  have hbud : InBudget X p w c := by
    refine ⟨hcX, hb, fun T => ?_⟩
    rw [← hbind.tsum_eq]
    exact hbind.summable.sum_le_tsum _
      (fun s _ => dotProduct_nonneg_of_nonneg (hp s) (hX0 (hcX s)))
  refine ⟨hbud, hs, fun c' hc' hs' => ?_⟩
  obtain ⟨hsum', hle'⟩ := expenditure_summable hp (fun s => hX0 (hc'.1 s)) hc'.2.2
  have hterm : ∀ t, δ ^ t * u (c' t) ≤ δ ^ t * u (c t) + lam * (p t ⬝ᵥ c' t - p t ⬝ᵥ c t) := by
    intro t
    have g := MWG.GeneralEquilibriumExamples.concave_le_fderiv hconc (hcX t) (hc'.1 t) (hDu t)
    have e := hfoc t (c' t - c t)
    rw [dotProduct_sub] at e
    have := mul_le_mul_of_nonneg_left g (pow_nonneg hδ t)
    nlinarith
  have hrhs : Summable fun t => δ ^ t * u (c t) + lam * (p t ⬝ᵥ c' t - p t ⬝ᵥ c t) :=
    hs.add ((hsum'.sub hbind.summable).mul_left lam)
  have := Summable.tsum_le_tsum hterm hs' hrhs
  rw [hs.tsum_add ((hsum'.sub hbind.summable).mul_left lam),
    (hsum'.sub hbind.summable).tsum_mul_left, hsum'.tsum_sub hbind.summable,
    hbind.tsum_eq] at this
  unfold discountedUtility
  nlinarith [mul_le_mul_of_nonneg_left (sub_nonpos.2 hle') hlam]

/-- **Exercise 20.D.1** (MWG, p. 784): with borrowing and lending at a zero nominal rate, the
single budget constraint is a sequence of budget constraints. The asset (money) holdings
`m_t = m_{t-1} + p_t · (ω_t - c_t)`, `m_{-1} = 0`, satisfy the period-`t` constraint
`p_t · c_t + m_t = p_t · ω_t + m_{t-1}`, and `∑ p_t · c_t ≤ ∑ p_t · ω_t` exactly when the limit
of the holdings is nonnegative (no debt is left at infinity). -/
theorem exercise_20_D_1 {p c ω : ℕ → Fin L → ℝ} (hc : Summable fun t => p t ⬝ᵥ c t)
    (hω : Summable fun t => p t ⬝ᵥ ω t) :
    let m : ℕ → ℝ := fun t => ∑ s ∈ Finset.range (t + 1), p s ⬝ᵥ (ω s - c s)
    (p 0 ⬝ᵥ c 0 + m 0 = p 0 ⬝ᵥ ω 0) ∧
      (∀ t, p (t + 1) ⬝ᵥ c (t + 1) + m (t + 1) = p (t + 1) ⬝ᵥ ω (t + 1) + m t) ∧
      Tendsto m atTop (𝓝 (∑' t, p t ⬝ᵥ ω t - ∑' t, p t ⬝ᵥ c t)) ∧
      (∑' t, p t ⬝ᵥ c t ≤ ∑' t, p t ⬝ᵥ ω t ↔ 0 ≤ ∑' t, p t ⬝ᵥ ω t - ∑' t, p t ⬝ᵥ c t) := by
  intro m
  refine ⟨by simp [m, dotProduct_sub], fun t => ?_, ?_, by constructor <;> intro h <;> linarith⟩
  · simp only [m, Finset.sum_range_succ _ (t + 1), dotProduct_sub]
    ring
  · have h := (hω.sub hc).hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
    rw [hω.tsum_sub hc] at h
    refine h.congr fun t => ?_
    simp [m, dotProduct_sub, Function.comp]

/-! ### Example 20.D.1: logarithmic utility -/

/-- **Example 20.D.1** (MWG, p. 746): with one good and `u = ln`, the first-order conditions
`λ p_t = δ^t / c_t` and `∑ p_t c_t = w` give `w = 1 / (λ (1 - δ))` and
`p_t c_t = δ^t (1 - δ) w`. -/
theorem example_20_D_1_foc {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) {p c : ℕ → ℝ} {lam w : ℝ}
    (hlam : 0 < lam) (hfoc : ∀ t, lam * p t * c t = δ ^ t)
    (hw : HasSum (fun t => p t * c t) w) :
    w = 1 / (lam * (1 - δ)) ∧ ∀ t, p t * c t = δ ^ t * (1 - δ) * w := by
  have hpc : ∀ t, p t * c t = δ ^ t / lam := fun t => by
    rw [← hfoc t]; field_simp
  have hg : HasSum (fun t => p t * c t) ((1 - δ)⁻¹ / lam) := by
    have := (hasSum_geometric_of_lt_one hδ0 hδ1).div_const lam
    exact this.congr_fun fun t => hpc t
  have hweq : w = 1 / (lam * (1 - δ)) := by
    rw [hw.unique hg]; field_simp
  refine ⟨hweq, fun t => ?_⟩
  rw [hpc t, hweq]
  have : (1 : ℝ) - δ ≠ 0 := by linarith
  field_simp

/-- **Exercise 20.D.4** (MWG, p. 784): with `p_t c_t = δ^t (1 - δ) w` and `w > 0`, the savings
rate is constant: `p_T c_T / ∑_{t ≥ T} p_t c_t = 1 - δ` for every `T`. -/
theorem exercise_20_D_4 {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) {p c : ℕ → ℝ} {w : ℝ}
    (hw : 0 < w) (h : ∀ t, p t * c t = δ ^ t * (1 - δ) * w) (T : ℕ) :
    p T * c T / ∑' t, p (t + T) * c (t + T) = 1 - δ := by
  have hsum : ∑' t, p (t + T) * c (t + T) = δ ^ T * w := by
    simp_rw [h, pow_add]
    rw [show (fun t => δ ^ t * δ ^ T * (1 - δ) * w) = fun t => δ ^ t * (δ ^ T * (1 - δ) * w)
      by funext t; ring, tsum_mul_right, tsum_geometric_of_lt_one hδ0.le hδ1]
    have : (1 : ℝ) - δ ≠ 0 := by linarith
    field_simp
  rw [hsum, h T]
  have : δ ^ T * w ≠ 0 := (mul_pos (pow_pos hδ0 T) hw).ne'
  field_simp

/-- **Example 20.D.1(i)** (MWG, p. 746): in the exchange economy with one good and log utility, the
equilibrium consumption is `c* = ω`; with the normalization `∑ p_t ω_t = 1` the first-order
conditions force `p_t = δ^t (1 - δ) / ω_t`, and these prices satisfy the normalization and the
conditions (20.D.6) with `λ = 1 / (1 - δ)`. -/
theorem example_20_D_1_i {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) {ω p : ℕ → ℝ}
    (hω : ∀ t, 0 < ω t) :
    ((∃ lam, 0 < lam ∧ (∀ t, lam * p t * ω t = δ ^ t) ∧ HasSum (fun t => p t * ω t) 1) →
      ∀ t, p t = δ ^ t * (1 - δ) / ω t) ∧
    (HasSum (fun t => δ ^ t * (1 - δ) / ω t * ω t) 1 ∧
      ∀ t, 1 / (1 - δ) * (δ ^ t * (1 - δ) / ω t) * ω t = δ ^ t) := by
  have h1δ : (1 : ℝ) - δ ≠ 0 := by linarith
  refine ⟨fun ⟨lam, hlam, hfoc, hw⟩ t => ?_, ?_, fun t => ?_⟩
  · obtain ⟨-, h⟩ := example_20_D_1_foc hδ0 hδ1 hlam hfoc hw
    have := h t
    field_simp [(hω t).ne'] at this ⊢
    linarith
  · have := (hasSum_geometric_of_lt_one hδ0 hδ1).mul_right (1 - δ)
    rw [inv_mul_cancel₀ h1δ] at this
    exact this.congr_fun fun t => by field_simp [(hω t).ne']
  · field_simp [(hω t).ne']

/-- The linear technology of Example 20.D.1(ii): `a` units of output at `t + 1` per unit of
input at `t`, `Y = {(-k, k') : k ≥ 0, k' ≤ a k}` (one good). -/
def linearTech (a : ℝ) : Set (ProdPlan (Fin 1)) :=
  {y | y.1 0 ≤ 0 ∧ y.2 0 ≤ -(a * y.1 0)}

/-- The strictly positive orthant of `ℝ¹`, the consumption set of the logarithmic utility. -/
def posOrthant1 : Set (Fin 1 → ℝ) := {x | 0 < x 0}

/-- The logarithmic one-period utility `u(x) = ln x₀`. -/
noncomputable def logUtil (x : Fin 1 → ℝ) : ℝ := Real.log (x 0)

theorem logUtil_concaveOn : ConcaveOn ℝ posOrthant1 logUtil := by
  refine ⟨?_, fun x hx y hy a b ha hb hab => ?_⟩
  · intro x hx y hy a b ha hb hab
    simp only [posOrthant1, Set.mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at *
    rcases eq_or_lt_of_le ha with rfl | ha'
    · have hb1 : b = 1 := by linarith
      subst hb1; simpa using hy
    · nlinarith [mul_pos ha' hx]
  · simp only [logUtil, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact (StrictConcaveOn.concaveOn strictConcaveOn_log_Ioi).2 hx hy ha hb hab

theorem logUtil_hasFDerivAt {x : Fin 1 → ℝ} (hx : 0 < x 0) :
    HasFDerivAt logUtil ((ContinuousLinearMap.toSpanSingleton ℝ (x 0)⁻¹).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0)) x :=
  (Real.hasDerivAt_log hx.ne').hasFDerivAt.comp x
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).hasFDerivAt

/-- **Example 20.D.1(ii)** (MWG, p. 747): one good, log utility, `ω₀ = 1`, `ω_t = 0` for `t > 0`,
and the linear technology `a`. With `1 ≤ a` and `a δ ≤ 1`, the prices `p_t = 1/a^t`, the
investments `k_t = δ (aδ)^t` and the consumptions `c_t = (aδ)^t (1 - δ)` form a Walrasian
equilibrium (Definition 20.D.1, with consumption set the positive reals). This is also a proved
instance of `WalrasEq`. -/
theorem example_20_D_1_ii {a δ : ℝ} (ha : 1 ≤ a) (hδ0 : 0 < δ) (hδ1 : δ < 1) (haδ : a * δ ≤ 1) :
    WalrasEq posOrthant1 (linearTech a) δ logUtil (fun t _ => if t = 0 then 1 else 0)
      (fun t _ => (a ^ t)⁻¹)
      (fun t => (fun _ => -(δ * (a * δ) ^ t), fun _ => a * (δ * (a * δ) ^ t))) := by
  set ω : ℕ → Fin 1 → ℝ := fun t _ => if t = 0 then 1 else 0 with hω
  set p : ℕ → Fin 1 → ℝ := fun t _ => (a ^ t)⁻¹ with hp
  set y : ℕ → ProdPlan (Fin 1) :=
    fun t => (fun _ => -(δ * (a * δ) ^ t), fun _ => a * (δ * (a * δ) ^ t)) with hy
  have ha0 : 0 < a := by linarith
  have haδ0 : 0 ≤ a * δ := by positivity
  have hpow : ∀ t, (a * δ) ^ t ≤ 1 := fun t => pow_le_one₀ haδ0 haδ
  -- consumption
  have hcons : ∀ t, consumption ω y t = fun _ => (a * δ) ^ t * (1 - δ) := by
    intro t
    funext i
    cases t with
    | zero => simp [consumption, netOutput, hy, hω]; ring
    | succ t => simp [consumption, netOutput, hy, hω, pow_succ]; ring
  have hprofit : ∀ t, periodProfit p y t = 0 := by
    intro t
    simp [periodProfit, planValue, dotProduct, hp, hy, pow_succ]
    field_simp
    ring
  have hwealth : HasSum (fun t => periodProfit p y t + p t ⬝ᵥ ω t) 1 := by
    have : (fun t => periodProfit p y t + p t ⬝ᵥ ω t) = fun t => if t = 0 then 1 else 0 := by
      funext t
      rw [hprofit t]
      rcases eq_or_ne t 0 with rfl | ht
      · simp [dotProduct, hp, hω]
      · simp [dotProduct, hp, hω, ht]
    rw [this]
    exact hasSum_ite_eq 0 1
  have hpc : ∀ t, p t ⬝ᵥ consumption ω y t = δ ^ t * (1 - δ) := by
    intro t
    rw [hcons t]
    simp [dotProduct, hp, mul_pow]
    field_simp
  refine ⟨⟨1, fun t i => ⟨?_, ?_⟩⟩, ⟨1, fun t i => ?_⟩, fun t i => ?_, fun t => ?_, ⟨fun t => ?_,
    fun t z hz => ?_⟩, hwealth.summable, ?_⟩
  · simp only [hy, abs_neg]
    rw [abs_of_nonneg (by positivity)]
    calc δ * (a * δ) ^ t ≤ 1 * 1 := mul_le_mul hδ1.le (hpow t) (by positivity) zero_le_one
      _ = 1 := one_mul 1
  · simp only [hy]
    rw [abs_of_nonneg (by positivity)]
    have : a * (δ * (a * δ) ^ t) = (a * δ) * (a * δ) ^ t := by ring
    rw [this]
    calc (a * δ) * (a * δ) ^ t ≤ 1 * 1 := mul_le_mul haδ (hpow t) (by positivity) zero_le_one
      _ = 1 := one_mul 1
  · simp only [hp]
    rw [abs_of_pos (by positivity)]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ ha)
  · simp only [hp]; positivity
  · rw [hcons t]; simp only [posOrthant1, Set.mem_ofPred_eq]
    exact mul_pos (pow_pos (by positivity) t) (by linarith)
  · simp only [linearTech, Set.mem_ofPred_eq, hy]
    constructor
    · have : 0 ≤ δ * (a * δ) ^ t := by positivity
      linarith
    · linarith
  · simp only [linearTech, Set.mem_ofPred_eq] at hz
    obtain ⟨h1, h2⟩ := hz
    rw [hprofit t]
    simp only [planValue, dotProduct, Finset.univ_unique, Fin.default_eq_zero,
      Finset.sum_singleton, hp]
    have hpt : 0 < (a ^ (t + 1))⁻¹ := by positivity
    have : (a ^ t)⁻¹ = a * (a ^ (t + 1))⁻¹ := by
      rw [pow_succ]; field_simp
    rw [this]
    nlinarith [mul_le_mul_of_nonneg_left h2 hpt.le]
  · rw [hwealth.tsum_eq]
    have hbind : HasSum (fun t => p t ⬝ᵥ consumption ω y t) 1 := by
      have := (hasSum_geometric_of_lt_one hδ0.le hδ1).mul_right (1 - δ)
      rw [inv_mul_cancel₀ (by linarith : (1 : ℝ) - δ ≠ 0)] at this
      exact this.congr_fun fun t => hpc t
    have hcpos : ∀ t, 0 < consumption ω y t 0 := fun t => by
      rw [hcons t]; exact mul_pos (pow_pos (by positivity) t) (by linarith)
    refine proposition_20_D_2 (fun x hx => fun i => ?_) hδ0.le logUtil_concaveOn
      (fun t i => by simp only [hp]; positivity) (fun t => hcpos t) ⟨1, fun t i => ?_⟩ ?_ hbind
      (fun t => logUtil_hasFDerivAt (hcpos t)) (lam := 1 / (1 - δ)) (by
        have : 0 < 1 - δ := by linarith
        positivity) (fun t v => ?_)
    · fin_cases i; exact (show 0 < x 0 from hx).le
    · rw [hcons t]
      simp only
      rw [abs_of_nonneg (by have := pow_nonneg haδ0 t; nlinarith)]
      nlinarith [hpow t]
    · -- the utility series converges: `δ^t (t ln(aδ) + ln(1 - δ))`
      have hc : ∀ t, logUtil (consumption ω y t) = t * Real.log (a * δ) + Real.log (1 - δ) := by
        intro t
        rw [hcons t]
        simp only [logUtil]
        rw [Real.log_mul (pow_pos (by positivity) t).ne' (by linarith), Real.log_pow]
      simp_rw [hc]
      have h1 : Summable fun t : ℕ => δ ^ t * (t * Real.log (a * δ)) := by
        have := (summable_pow_mul_geometric_of_norm_lt_one 1
          (by rw [Real.norm_eq_abs, abs_of_pos hδ0]; exact hδ1) : Summable fun n : ℕ =>
            ((n : ℝ) ^ 1 * δ ^ n)).mul_right (Real.log (a * δ))
        refine this.congr fun t => ?_
        ring
      have h2 := (summable_geometric_of_lt_one hδ0.le hδ1).mul_right (Real.log (1 - δ))
      refine (h1.add h2).congr fun t => ?_
      ring
    · rw [hcons t]
      simp only [dotProduct, Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, hp,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
        ContinuousLinearMap.proj_apply, smul_eq_mul]
      have : 0 < 1 - δ := by linarith
      field_simp
      rw [mul_pow]
      ring

/-- **Correction to Example 20.D.1(iii)** (MWG, p. 747): with `F(k) = k^α`, `0 < α < 1`, and log
utility, the rule "invest the fraction `δ` of wealth", `k_{t+1} = δ F(k_t)`, is incompatible with
the equilibrium conditions: the first-order conditions `λ p_t c_t = δ^t` (20.D.6) at `t = 1, 2`,
profit maximization `p_2 F'(k_1) = p_1`, and the resource constraints `c_{t+1} + k_{t+1} =
F(k_t)` with `k_{t+1} = δ F(k_t)` force `α = 1`. (The step `∑_{t ≥ T+1} p_t c_t = p_{T+1} F(k_T)`
fails because future profits are positive under decreasing returns.) -/
theorem example_20_D_1_iii_false {α δ lam : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    {k c p : ℕ → ℝ} (hk : ∀ t, 0 < k t) (hp : ∀ t, 0 < p t)
    (hfoc : ∀ t, lam * p t * c t = δ ^ t) (hprofit : p 2 * (α * k 1 ^ (α - 1)) = p 1)
    (hres : ∀ t, c (t + 1) + k (t + 1) = k t ^ α) (hrule : ∀ t, k (t + 1) = δ * k t ^ α) :
    α = 1 := by
  have hc1 : c 1 = (1 - δ) * k 0 ^ α := by have := hres 0; rw [hrule 0] at this; linarith
  have hc2 : c 2 = (1 - δ) * k 1 ^ α := by have := hres 1; rw [hrule 1] at this; linarith
  have hk0 : 0 < k 0 ^ α := Real.rpow_pos_of_pos (hk 0) α
  have hk1' : 0 < k 1 ^ α := Real.rpow_pos_of_pos (hk 1) α
  have h1δ : 0 < 1 - δ := by linarith
  have e1 := hfoc 1
  have e2 := hfoc 2
  -- `p_1 / p_2 = c_2 / (δ c_1)`
  have hlam : lam ≠ 0 := by
    rintro rfl; simp at e1; exact hδ0.ne' e1.symm
  have hratio : p 1 * δ * c 1 = p 2 * c 2 := by
    have : lam * (p 1 * δ * c 1) = lam * (p 2 * c 2) := by
      calc lam * (p 1 * δ * c 1) = δ * (lam * p 1 * c 1) := by ring
        _ = δ * δ ^ 1 := by rw [e1]
        _ = δ ^ 2 := by ring
        _ = lam * (p 2 * c 2) := by rw [← e2]; ring
    exact mul_left_cancel₀ hlam this
  rw [← hprofit, hc1, hc2] at hratio
  -- `α k_1^{α-1} k_1 = k_1^α`
  have hpow : k 1 ^ (α - 1) * k 1 = k 1 ^ α := by
    rw [← Real.rpow_add_one (hk 1).ne']; congr 1; ring
  have hk1 : δ * k 0 ^ α = k 1 := (hrule 0).symm
  have key : p 2 * (1 - δ) * k 1 ^ α * (α - 1) = 0 := by
    calc p 2 * (1 - δ) * k 1 ^ α * (α - 1)
        = p 2 * (α * k 1 ^ (α - 1)) * ((1 - δ) * (δ * k 0 ^ α))
          - p 2 * ((1 - δ) * k 1 ^ α) := by rw [hk1, ← hpow]; ring
      _ = 0 := by rw [sub_eq_zero, ← hratio]; ring
  have hne : p 2 * (1 - δ) * k 1 ^ α ≠ 0 := (mul_pos (mul_pos (hp 2) h1δ) hk1').ne'
  have := (mul_eq_zero.1 key).resolve_left hne
  linarith

/-- **Example 20.D.1(iii), corrected** (MWG, p. 747): with `F(k) = k^α` and log utility, the
investment rule `k_{t+1} = α δ F(k_t)` (with `c_{t+1} = (1 - αδ) F(k_t)`) satisfies, for every
`α` and `δ` (in particular `0 < α < 1`, `0 < δ < 1`), the Euler
equation `c_{t+1} / c_t = δ F'(k_t)`, i.e. the first-order conditions (20.D.6) with prices from
profit maximization `p_{t+1} F'(k_t) = p_t`. -/
theorem example_20_D_1_iii_corrected {α δ : ℝ} {k : ℕ → ℝ} (hk : ∀ t, 0 < k t)
    (hrule : ∀ t, k (t + 1) = α * δ * k t ^ α)
    (t : ℕ) :
    (1 - α * δ) * k (t + 1) ^ α = δ * (α * k (t + 1) ^ (α - 1)) * ((1 - α * δ) * k t ^ α) := by
  have hpow : k (t + 1) ^ (α - 1) * k (t + 1) = k (t + 1) ^ α := by
    rw [← Real.rpow_add_one (hk (t + 1)).ne']; congr 1; ring
  rw [← hpow]
  nth_rewrite 2 [hrule t]
  ring

end MWG.EquilibriumTime
