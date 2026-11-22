/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGEquilibriumTime.Planning

/-!
# Equilibrium with several consumers (MWG Section 20.G, pp. 765-769)

MWG, Chapter 20, Section 20.G and Exercises 20.G.1, 20.G.4, 20.G.5 (pp. 785-786).

Consumers `i : ι` (a finite type) have one-period utilities `u i`, a common discount factor `δ`,
endowment streams `ω i` and shares `θ i t ≥ 0` of period-`t` profits (`∑_i θ_{it} = 1`).

* **Definition 20.G.1** (`WalrasEqI`), with a proved instance (`walrasEqI_example`).
* **Proposition 20.G.1** (first welfare theorem, `proposition_20_G_1`).
* **Proposition 20.G.2** (the representative consumer of a Walrasian equilibrium with Negishi
  weights `η_i = 1/λ_i`, `proposition_20_G_2`), with a complete proof for interior equilibria of
  differentiable concave utilities (MWG give an intuitive argument).
* **Exercise 20.G.1** (`exercise_20_G_1`): with one good, two consumers and constant aggregate
  endowment, equilibrium consumption is stationary, prices are proportional with rate of interest
  `(1 - δ)/δ`, and each consumer consumes `(1 - δ) ∑_t δ^t ω_{it}`.
* **(20.G.6)** (`eq_20_G_6`), **Exercise 20.G.5** (`exercise_20_G_5`), and the dampening criterion
  `|dk_{t+1}/dk_t|, |dk_{t+1}/dk_{t-1}| < 1/2` (`dampening_of_small_coefficients`).

OPEN: Exercise 20.G.2 (Pareto optima equalize the marginal utilities of wealth across periods),
Exercise 20.G.3 (the Negishi equation and generic finiteness, Kehoe-Levine), Exercise 20.G.4 and
footnote 32, and the existence of robust continua of equilibria with externalities (no explicit
example is given in MWG).
-/

open Filter Topology

namespace MWG.EquilibriumTime

variable {L : ℕ} {ι : Type*} [Fintype ι]

variable (X : Set (Fin L → ℝ)) (Y : Set (ProdPlan (Fin L))) (δ : ℝ) (u : ι → (Fin L → ℝ) → ℝ)
  (ω : ι → ℕ → Fin L → ℝ) (θ : ι → ℕ → ℝ) (p : ℕ → Fin L → ℝ) (y : ℕ → ProdPlan (Fin L))
  (c : ι → ℕ → Fin L → ℝ) in
/-- **Definition 20.G.1** (MWG, pp. 765-766): a bounded production path `y`, a bounded nonnegative
price sequence `p` and consumption streams `c i` form a Walrasian equilibrium if (i) aggregate
consumption is feasible, (20.G.1), (ii) the path is myopically profit maximizing, (20.G.2), and
(iii) every consumer maximizes utility subject to the single budget constraint with wealth
`w_i = ∑_t θ_{it} π_t + ∑_t p_t · ω_{it}`, (20.G.3). (As in Definition 20.D.1, the profit and
endowment series are required to converge.) -/
structure WalrasEqI where
  /-- The production path is bounded. -/
  boundedPath : BoundedPath y
  /-- The price sequence is bounded. -/
  boundedPrices : ∃ B : ℝ, ∀ t i, |p t i| ≤ B
  /-- Prices are nonnegative. -/
  pricesNonneg : ∀ t, 0 ≤ p t
  /-- (i), (20.G.1): feasibility. -/
  feasible : ∀ t, ∑ i, c i t = netOutput y t + ∑ i, ω i t
  /-- (ii), (20.G.2): short-run profit maximization. -/
  myopic : MyopicProfitMax Y p y
  /-- Profits converge. -/
  profitSummable : Summable (periodProfit p y)
  /-- Every consumer's endowment has finite value. -/
  endowSummable : ∀ i, Summable fun t => p t ⬝ᵥ ω i t
  /-- (iii), (20.G.3): utility maximization. -/
  utilityMax : ∀ i, UtilityMax X δ (u i) p
    (∑' t, θ i t * periodProfit p y t + ∑' t, p t ⬝ᵥ ω i t) (c i)

/-- The wealth of consumer `i`. -/
noncomputable def wealthI (θ : ι → ℕ → ℝ) (p : ℕ → Fin L → ℝ) (y : ℕ → ProdPlan (Fin L))
    (ω : ι → ℕ → Fin L → ℝ) (i : ι) : ℝ :=
  ∑' t, θ i t * periodProfit p y t + ∑' t, p t ⬝ᵥ ω i t

/-- A **feasible allocation**: a production path and consumption streams in `X` with
`∑_i c'_{it} ≤ y'_{a,t-1} + y'_{bt} + ∑_i ω_{it}` (MWG, p. 766). -/
def FeasibleAlloc (X : Set (Fin L → ℝ)) (Y : Set (ProdPlan (Fin L))) (ω : ι → ℕ → Fin L → ℝ)
    (y : ℕ → ProdPlan (Fin L)) (c : ι → ℕ → Fin L → ℝ) : Prop :=
  IsProdPath Y y ∧ (∀ i t, c i t ∈ X) ∧ ∀ t, ∑ i, c i t ≤ netOutput y t + ∑ i, ω i t

/-- A stream with expenditure strictly below `w` can be improved within the budget set (strict
monotonicity, upward-closed `X ⊆ ℝ^L_+`). -/
theorem exists_better_of_slack [NeZero L] {X : Set (Fin L → ℝ)} (hX0 : X ⊆ Set.Ici 0)
    (hXup : ∀ x ∈ X, ∀ x', x ≤ x' → x' ∈ X)
    {δ : ℝ} {v : (Fin L → ℝ) → ℝ} (hv : StrictMonoOn v X) {p : ℕ → Fin L → ℝ}
    (hp : ∀ t, 0 ≤ p t) {w : ℝ} {c : ℕ → Fin L → ℝ} (hcX : ∀ t, c t ∈ X) (hb : BoundedStream c)
    (hsum : Summable fun t => p t ⬝ᵥ c t) (hlt : ∑' t, p t ⬝ᵥ c t < w)
    (hs : Summable fun t => δ ^ t * v (c t)) :
    ∃ c', InBudget X p w c' ∧ Summable (fun t => δ ^ t * v (c' t)) ∧
      discountedUtility δ v c < discountedUtility δ v c' := by
  set S := ∑' t, p t ⬝ᵥ c t
  set i : Fin L := 0
  set ε := (w - S) / (p 0 i + 1) with hε
  have hpi : 0 ≤ p 0 i := hp 0 i
  have hεpos : 0 < ε := div_pos (by linarith) (by linarith)
  have hεle : p 0 i * ε ≤ w - S := by
    rw [hε, mul_div_assoc', div_le_iff₀ (by linarith)]
    nlinarith
  set c' : ℕ → Fin L → ℝ := fun t => c t + if t = 0 then ε • Pi.single i 1 else 0 with hc'
  have hdiff : ∀ t, t ≠ 0 → c' t = c t := fun t ht => by simp [hc', ht]
  have hc'0 : c' 0 = c 0 + ε • Pi.single i 1 := by simp [hc']
  have hlt0 : c 0 < c' 0 := by rw [hc'0]; exact lt_add_of_pos_right _ (single_smul_pos hεpos i)
  have hfs : ∀ t ∉ ({0} : Finset ℕ), c' t = c t := fun t ht => hdiff t (by simpa using ht)
  refine ⟨c', ⟨fun t => ?_, ?_, fun T => ?_⟩, summable_of_finite_change _ hfs hs, ?_⟩
  · rcases eq_or_ne t 0 with rfl | ht
    · exact hXup _ (hcX 0) _ hlt0.le
    · rw [hdiff t ht]; exact hcX t
  · obtain ⟨M, hM⟩ := hb
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
      hsum.sum_le_tsum _ (fun t _ => dotProduct_nonneg_of_nonneg (hp t) (hX0 (hcX t)))
    linarith
  · have hs' := summable_of_finite_change _ hfs hs
    have := discountedUtility_sub_of_finite _ hfs hs hs'
    rw [Finset.sum_singleton, pow_zero, one_mul] at this
    have hu0 : v (c 0) < v (c' 0) := hv (hcX 0) (hXup _ (hcX 0) _ hlt0.le) hlt0
    linarith

/-- **Aggregate wealth** (MWG, p. 766): with shares `θ_{it} ≥ 0` summing to one, the wealths add up
to `∑_t π_t + ∑_t p_t · ∑_i ω_{it}`. -/
theorem sum_wealthI {θ : ι → ℕ → ℝ} (hθ0 : ∀ i t, 0 ≤ θ i t) (hθ1 : ∀ t, ∑ i, θ i t = 1)
    {p : ℕ → Fin L → ℝ} {y : ℕ → ProdPlan (Fin L)} {ω : ι → ℕ → Fin L → ℝ}
    (hπ : Summable (periodProfit p y)) (hω : ∀ i, Summable fun t => p t ⬝ᵥ ω i t) :
    Summable (fun t => periodProfit p y t + p t ⬝ᵥ ∑ i, ω i t) ∧
      ∑ i, wealthI θ p y ω i = ∑' t, (periodProfit p y t + p t ⬝ᵥ ∑ i, ω i t) := by
  have hθle : ∀ i t, θ i t ≤ 1 := fun i t => by
    rw [← hθ1 t]
    exact Finset.single_le_sum (fun j _ => hθ0 j t) (Finset.mem_univ i)
  have hθπ : ∀ i, Summable fun t => θ i t * periodProfit p y t := fun i =>
    Summable.of_norm_bounded hπ.abs fun t => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hθ0 i t)]
      exact mul_le_of_le_one_left (abs_nonneg _) (hθle i t)
  have hωsum : Summable fun t => p t ⬝ᵥ ∑ i, ω i t := by
    simp_rw [dotProduct_sum]
    exact summable_sum fun i _ => hω i
  refine ⟨hπ.add hωsum, ?_⟩
  simp only [wealthI, Finset.sum_add_distrib]
  rw [← Summable.tsum_finsetSum (fun i _ => hθπ i), ← Summable.tsum_finsetSum (fun i _ => hω i),
    hπ.tsum_add hωsum]
  congr 1
  · refine tsum_congr fun t => ?_
    rw [← Finset.sum_mul, hθ1 t, one_mul]
  · refine tsum_congr fun t => ?_
    rw [dotProduct_sum]

/-- **Proposition 20.G.1** (MWG, p. 766), the first welfare theorem: a Walrasian equilibrium
allocation is Pareto optimal. No feasible allocation (with bounded consumption streams whose
utility series converge) makes every consumer at least as well off and one strictly better off.
Hypotheses: `X ⊆ ℝ^L_+` upward closed, strictly increasing one-period utilities, `0 ∈ Y`,
truncation, nonnegative endowments, and nonnegative shares summing to one. -/
theorem proposition_20_G_1 [NeZero L] {X : Set (Fin L → ℝ)} (hX0 : X ⊆ Set.Ici 0)
    (hXup : ∀ x ∈ X, ∀ x', x ≤ x' → x' ∈ X) {Y : Set (ProdPlan (Fin L))}
    (h0 : (0 : ProdPlan (Fin L)) ∈ Y) (htr : ∀ z ∈ Y, (z.1, 0) ∈ Y) {δ : ℝ}
    {u : ι → (Fin L → ℝ) → ℝ} (hu : ∀ i, StrictMonoOn (u i) X) {ω : ι → ℕ → Fin L → ℝ}
    (hω0 : ∀ i t, 0 ≤ ω i t) {θ : ι → ℕ → ℝ} (hθ0 : ∀ i t, 0 ≤ θ i t)
    (hθ1 : ∀ t, ∑ i, θ i t = 1) {p : ℕ → Fin L → ℝ} {y : ℕ → ProdPlan (Fin L)}
    {c : ι → ℕ → Fin L → ℝ} (he : WalrasEqI X Y δ u ω θ p y c) :
    ¬ ∃ y' c', FeasibleAlloc X Y ω y' c' ∧ (∀ i, BoundedStream (c' i)) ∧
      (∀ i, Summable fun t => δ ^ t * u i (c' i t)) ∧
      (∀ i, discountedUtility δ (u i) (c i) ≤ discountedUtility δ (u i) (c' i)) ∧
      ∃ j, discountedUtility δ (u j) (c j) < discountedUtility δ (u j) (c' j) := by
  rintro ⟨y', c', ⟨hpath', hcX', hfeas'⟩, hb', hs', hge, j, hj⟩
  obtain ⟨hWs, hW⟩ := sum_wealthI hθ0 hθ1 he.profitSummable he.endowSummable
  set W := ∑' t, (periodProfit p y t + p t ⬝ᵥ ∑ i, ω i t)
  have hp := he.pricesNonneg
  have hπ0 : ∀ t, 0 ≤ periodProfit p y t := fun t => by
    have := he.myopic.2 t 0 h0; simpa [planValue] using this
  have hnn : ∀ t, 0 ≤ periodProfit p y t + p t ⬝ᵥ ∑ i, ω i t := fun t =>
    add_nonneg (hπ0 t) (dotProduct_nonneg_of_nonneg (hp t)
      (Finset.sum_nonneg fun i _ => hω0 i t))
  -- the aggregate value of the new consumptions is at most `W` at every horizon
  have hagg : ∀ T, ∑ t ∈ Finset.range T, ∑ i, p t ⬝ᵥ c' i t ≤ W := by
    intro T
    rcases T with _ | T
    · simpa using tsum_nonneg hnn
    have h1 := sum_value_le_of_myopic htr he.myopic hpath' T
    have h2 := sum_value_netOutput p y T
    have h3 : ∑ t ∈ Finset.range (T + 1), (periodProfit p y t + p t ⬝ᵥ ∑ i, ω i t) ≤ W :=
      hWs.sum_le_tsum _ (fun t _ => hnn t)
    have h4 : ∀ t, ∑ i, p t ⬝ᵥ c' i t ≤ p t ⬝ᵥ netOutput y' t + p t ⬝ᵥ ∑ i, ω i t := by
      intro t
      rw [← dotProduct_sum, ← dotProduct_add]
      exact dotProduct_le_dotProduct_of_nonneg_left (hfeas' t) (hp t)
    have h5 := Finset.sum_le_sum fun t (_ : t ∈ Finset.range (T + 1)) => h4 t
    rw [Finset.sum_add_distrib] at h5
    rw [Finset.sum_add_distrib] at h3
    linarith
  have hci0 : ∀ i t, 0 ≤ p t ⬝ᵥ c' i t := fun i t =>
    dotProduct_nonneg_of_nonneg (hp t) (hX0 (hcX' i t))
  -- every consumer's expenditure series converges
  have hpart : ∀ i T, ∑ t ∈ Finset.range T, p t ⬝ᵥ c' i t ≤ W := by
    intro i T
    refine le_trans (Finset.sum_le_sum fun t _ => ?_) (hagg T)
    exact Finset.single_le_sum (f := fun k => p t ⬝ᵥ c' k t) (fun k _ => hci0 k t)
      (Finset.mem_univ i)
  have hsumi : ∀ i, Summable fun t => p t ⬝ᵥ c' i t := fun i =>
    summable_of_sum_range_le (hci0 i) (hpart i)
  -- the new streams cost at least the wealth, strictly so for `j`
  have hcost : ∀ i, wealthI θ p y ω i ≤ ∑' t, p t ⬝ᵥ c' i t := by
    intro i
    by_contra hlt
    push Not at hlt
    obtain ⟨c'', hbud, hs'', hbetter⟩ := exists_better_of_slack hX0 hXup (hu i) hp (hcX' i)
      (hb' i) (hsumi i) hlt (hs' i)
    have := (he.utilityMax i).2.2 c'' hbud hs''
    linarith [hge i]
  have hcostj : wealthI θ p y ω j < ∑' t, p t ⬝ᵥ c' j t := by
    by_contra hle
    push Not at hle
    have hbud : InBudget X p (wealthI θ p y ω j) (c' j) := ⟨hcX' j, hb' j, fun T =>
      ((hsumi j).sum_le_tsum _ (fun t _ => hci0 j t)).trans hle⟩
    have := (he.utilityMax j).2.2 (c' j) hbud (hs' j)
    exact absurd this (not_le.2 hj)
  have htot : ∑ i, ∑' t, p t ⬝ᵥ c' i t ≤ W := by
    rw [← Summable.tsum_finsetSum (fun i _ => hsumi i)]
    exact Real.tsum_le_of_sum_range_le (fun t => Finset.sum_nonneg fun i _ => hci0 i t)
      (fun T => by rw [Finset.sum_comm]; exact hagg T |>.trans_eq' (Finset.sum_comm))
  have hlt : ∑ i, wealthI θ p y ω i < ∑ i, ∑' t, p t ⬝ᵥ c' i t :=
    Finset.sum_lt_sum (fun i _ => hcost i) ⟨j, Finset.mem_univ _, hcostj⟩
  rw [hW] at hlt
  linarith

/-- An instance of `WalrasEqI`: two consumers with linear utility `u(x) = x₀`, one good,
`δ = 1/2`, endowments `1/2` each, the technology `{y ≤ 0}` used at inaction, prices
`p_t = (1/2)^t`, and consumption equal to the endowments. -/
theorem walrasEqI_example :
    WalrasEqI (Set.Ici 0) {y : ProdPlan (Fin 1) | y ≤ 0} (1 / 2) (fun (_ : Fin 2) x => x 0)
      (fun _ _ _ => 1 / 2) (fun _ _ => 1 / 2) (fun t _ => (1 / 2) ^ t) (fun _ => 0)
      (fun _ _ _ => 1 / 2) := by
  have hπ : ∀ t, periodProfit (fun t (_ : Fin 1) => ((1 : ℝ) / 2) ^ t)
      (fun _ => (0 : ProdPlan (Fin 1))) t = 0 := fun t => by simp [periodProfit, planValue]
  have hg := summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  refine ⟨⟨0, fun t i => by simp⟩, ⟨1, fun t i => ?_⟩, fun t i => by positivity, fun t => ?_,
    ⟨fun t => show (0 : ProdPlan (Fin 1)) ≤ 0 from le_refl _, fun t z hz => ?_⟩,
    summable_zero.congr fun t => (hπ t).symm,
    fun i => ?_, fun i => ?_⟩
  · rw [abs_of_nonneg (by positivity)]; exact pow_le_one₀ (by norm_num) (by norm_num)
  · funext k
    cases t <;> simp [netOutput]
  · rw [hπ]
    simp only [planValue, dotProduct, Finset.univ_unique, Fin.default_eq_zero,
      Finset.sum_singleton]
    have h1 : z.1 0 ≤ 0 := hz.1 0
    have h2 : z.2 0 ≤ 0 := hz.2 0
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) t,
      pow_pos (by norm_num : (0 : ℝ) < 1 / 2) (t + 1)]
  · refine (hg.mul_right (1 / 2)).congr fun t => ?_
    simp [dotProduct]
  · simp_rw [hπ, mul_zero, tsum_zero, zero_add]
    refine ⟨⟨fun t _ => by norm_num, ⟨1, fun t k => by norm_num⟩, fun T => ?_⟩, ?_,
      fun c' hc' hs' => ?_⟩
    · have hnn : ∀ t, 0 ≤ (fun t (_ : Fin 1) => ((1 : ℝ) / 2) ^ t) t ⬝ᵥ fun _ => (1 : ℝ) / 2 :=
        fun t => by simp [dotProduct]
      exact (hg.mul_right (1 / 2) |>.congr (fun t => by simp [dotProduct])).sum_le_tsum _
        (fun t _ => hnn t)
    · exact (hg.mul_right (1 / 2)).congr fun t => by simp
    · -- linear utility: the utility of a budget-feasible stream is its expenditure
      obtain ⟨hsum, hle⟩ := expenditure_summable (fun t i => by simp)
        (fun t => hc'.1 t) hc'.2.2
      unfold discountedUtility
      have e1 : ∑' t, ((1 : ℝ) / 2) ^ t * c' t 0
          = ∑' t, (fun t (_ : Fin 1) => ((1 : ℝ) / 2) ^ t) t ⬝ᵥ c' t :=
        tsum_congr fun t => by simp [dotProduct]
      have e2 : ∑' t, ((1 : ℝ) / 2) ^ t * (fun (_ : Fin 1) => (1 : ℝ) / 2) 0
          = ∑' t, (fun t (_ : Fin 1) => ((1 : ℝ) / 2) ^ t) t ⬝ᵥ fun _ => (1 : ℝ) / 2 :=
        tsum_congr fun t => by simp [dotProduct]
      rw [e1, e2]
      exact hle

/-! ### Proposition 20.G.2: the representative consumer -/

/-- The **representative one-period utility** of Proposition 20.G.2 (MWG, p. 767):
`u(x) = max ∑_i η_i u_i(x_i)` subject to `∑_i x_i ≤ x`, `x_i ≥ 0` (a supremum). -/
noncomputable def negishiUtility (η : ι → ℝ) (u : ι → (Fin L → ℝ) → ℝ) (x : Fin L → ℝ) : ℝ :=
  sSup {r | ∃ z : ι → Fin L → ℝ, (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ x ∧ r = ∑ i, η i * u i (z i)}

/-- The weighted utilities have a common supergradient `q` at an allocation where the weighted
marginal utilities `η_i ∇u_i(z⁰_i)` all equal `q`. -/
theorem weighted_supergradient {η : ι → ℝ} (hη : ∀ i, 0 < η i) {u : ι → (Fin L → ℝ) → ℝ}
    (hconc : ∀ i, ConcaveOn ℝ (Set.Ici 0) (u i)) {z0 : ι → Fin L → ℝ} (hz0 : ∀ i, 0 ≤ z0 i)
    {D : ι → (Fin L → ℝ) →L[ℝ] ℝ} (hD : ∀ i, HasFDerivAt (u i) (D i) (z0 i)) {q : Fin L → ℝ}
    (hq : ∀ i v, η i * D i v = q ⬝ᵥ v) {z : ι → Fin L → ℝ} (hz : ∀ i, 0 ≤ z i) :
    ∑ i, η i * u i (z i) ≤ ∑ i, η i * u i (z0 i) + q ⬝ᵥ (∑ i, z i - ∑ i, z0 i) := by
  have h : ∀ i, η i * u i (z i) ≤ η i * u i (z0 i) + q ⬝ᵥ (z i - z0 i) := by
    intro i
    have g := MWG.GeneralEquilibriumExamples.concave_le_fderiv (hconc i) (Set.mem_Ici.2 (hz0 i))
      (Set.mem_Ici.2 (hz i)) (hD i)
    rw [← hq i]
    nlinarith [mul_le_mul_of_nonneg_left g (hη i).le]
  calc ∑ i, η i * u i (z i) ≤ ∑ i, (η i * u i (z0 i) + q ⬝ᵥ (z i - z0 i)) :=
        Finset.sum_le_sum fun i _ => h i
    _ = _ := by
        rw [Finset.sum_add_distrib, ← dotProduct_sum, Finset.sum_sub_distrib]

/-- The representative utility at the equilibrium aggregate is the weighted sum of the
individual utilities, and it has supergradient `q` there. -/
theorem negishiUtility_props {η : ι → ℝ} (hη : ∀ i, 0 < η i) {u : ι → (Fin L → ℝ) → ℝ}
    (hconc : ∀ i, ConcaveOn ℝ (Set.Ici 0) (u i)) {z0 : ι → Fin L → ℝ} (hz0 : ∀ i, 0 ≤ z0 i)
    {D : ι → (Fin L → ℝ) →L[ℝ] ℝ} (hD : ∀ i, HasFDerivAt (u i) (D i) (z0 i)) {q : Fin L → ℝ}
    (hq0 : 0 ≤ q) (hq : ∀ i v, η i * D i v = q ⬝ᵥ v) :
    negishiUtility η u (∑ i, z0 i) = ∑ i, η i * u i (z0 i) ∧
      ∀ x, 0 ≤ x → negishiUtility η u x ≤ ∑ i, η i * u i (z0 i) + q ⬝ᵥ (x - ∑ i, z0 i) := by
  have hbound : ∀ x, ∀ r ∈ {r | ∃ z : ι → Fin L → ℝ, (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ x ∧
      r = ∑ i, η i * u i (z i)}, r ≤ ∑ i, η i * u i (z0 i) + q ⬝ᵥ (x - ∑ i, z0 i) := by
    rintro x r ⟨z, hz, hzx, rfl⟩
    have := weighted_supergradient hη hconc hz0 hD hq hz
    have hmono : q ⬝ᵥ (∑ i, z i - ∑ i, z0 i) ≤ q ⬝ᵥ (x - ∑ i, z0 i) :=
      dotProduct_le_dotProduct_of_nonneg_left (sub_le_sub_right hzx _) hq0
    linarith
  have hne : ∀ x : Fin L → ℝ, 0 ≤ x → ({r | ∃ z : ι → Fin L → ℝ, (∀ i, 0 ≤ z i) ∧
      ∑ i, z i ≤ x ∧ r = ∑ i, η i * u i (z i)} : Set ℝ).Nonempty :=
    fun x hx => ⟨_, fun _ => 0, fun _ => le_rfl, by simpa using hx, rfl⟩
  refine ⟨le_antisymm ?_ ?_, fun x hx => csSup_le (hne x hx) (hbound x)⟩
  · have := csSup_le (hne _ (Finset.sum_nonneg fun i _ => hz0 i)) (hbound (∑ i, z0 i))
    rw [sub_self, dotProduct_zero, add_zero] at this
    exact this
  · exact le_csSup ⟨_, hbound (∑ i, z0 i)⟩ ⟨z0, hz0, le_rfl, rfl⟩

/-- **Proposition 20.G.2** (MWG, p. 767): at a Walrasian equilibrium of an economy with several
consumers (common discount factor `0 < δ`), with strictly positive bounded consumption streams and
one-period utilities that are concave and strictly increasing on `ℝ^L_+`, differentiable along the
equilibrium with strictly positive marginal utilities, there are weights `η_i > 0` (the
reciprocals of the marginal utilities of wealth) such that the production path and prices form a
Walrasian equilibrium of the one-consumer economy with utility `∑ δ^t u(c_t)`, where
`u(c) = max {∑_i η_i u_i(c_i) : ∑_i c_i ≤ c}`, and aggregate endowments. Hypotheses on the
economy: nonnegative shares summing to one. -/
theorem proposition_20_G_2 [NeZero L] {Y : Set (ProdPlan (Fin L))}
    {δ : ℝ} (hδ : 0 < δ) {u : ι → (Fin L → ℝ) → ℝ}
    (hconc : ∀ i, ConcaveOn ℝ (Set.Ici 0) (u i)) (hmono : ∀ i, StrictMonoOn (u i) (Set.Ici 0))
    {ω : ι → ℕ → Fin L → ℝ} {θ : ι → ℕ → ℝ}
    (hθ0 : ∀ i t, 0 ≤ θ i t) (hθ1 : ∀ t, ∑ i, θ i t = 1) {p : ℕ → Fin L → ℝ}
    {y : ℕ → ProdPlan (Fin L)} {c : ι → ℕ → Fin L → ℝ}
    (he : WalrasEqI (Set.Ici 0) Y δ u ω θ p y c) (hcpos : ∀ i t, StrictPos (c i t))
    {D : ι → ℕ → (Fin L → ℝ) →L[ℝ] ℝ} (hD : ∀ i t, HasFDerivAt (u i) (D i t) (c i t))
    (hDpos : ∀ i t k, 0 < D i t (Pi.single k 1)) :
    ∃ η : ι → ℝ, (∀ i, 0 < η i) ∧
      (∀ t, consumption (fun t => ∑ i, ω i t) y t = ∑ i, c i t) ∧
      (∀ t, negishiUtility η u (∑ i, c i t) = ∑ i, η i * u i (c i t)) ∧
      WalrasEq (Set.Ici 0) Y δ (negishiUtility η u) (fun t => ∑ i, ω i t) p y := by
  have hc0 : ∀ i t, 0 ≤ c i t := fun i t k => (hcpos i t k).le
  -- each consumer's first-order conditions (20.D.6)
  have hfoc : ∀ i, ∃ lam : ℝ, 0 < lam ∧ ∀ t v, lam * (p t ⬝ᵥ v) = δ ^ t * D i t v := by
    intro i
    obtain ⟨hbud, hs, hmax⟩ := he.utilityMax i
    have hmyo : MyopicUtilityMax (Set.Ici 0) δ (u i) p (wealthI θ p y ω i) (c i) := by
      refine ⟨hbud, hs, fun t c' hc' hdiff => hmax c' hc' ?_⟩
      exact summable_of_finite_change {t, t + 1} (fun s hst => by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hst
        exact hdiff s hst.1 hst.2) hs
    obtain ⟨-, h5⟩ := (exercise_20_D_3 hδ (hconc i) (hmono i) (hcpos i) hbud.2.1 hs (hD i)
      (hDpos i)).1 hmyo
    have hpne : ∀ t, p t ≠ 0 := by
      intro t hpt
      obtain ⟨lam, hlam, h1, -⟩ := h5 t
      have := h1 (Pi.single 0 1)
      rw [hpt, zero_dotProduct, mul_zero] at this
      exact (hDpos i t 0).ne' this.symm
    exact (foc_20_D_5_iff_20_D_6 hδ hpne).1 h5
  choose lam hlam hlamfoc using hfoc
  set η : ι → ℝ := fun i => (lam i)⁻¹ with hη
  have hηpos : ∀ i, 0 < η i := fun i => inv_pos.2 (hlam i)
  set q : ℕ → Fin L → ℝ := fun t => (δ ^ t)⁻¹ • p t with hq
  have hqfoc : ∀ t i v, η i * D i t v = q t ⬝ᵥ v := by
    intro t i v
    have := hlamfoc i t v
    simp only [hη, hq, smul_dotProduct, smul_eq_mul]
    have hδt : δ ^ t ≠ 0 := pow_ne_zero t hδ.ne'
    field_simp
    rw [div_eq_iff (hlam i).ne']
    linarith
  have hq0 : ∀ t, 0 ≤ q t := fun t k => by
    simp only [hq, Pi.smul_apply, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.2 (pow_nonneg hδ.le t)) (he.pricesNonneg t k)
  have hprops : ∀ t, negishiUtility η u (∑ i, c i t) = ∑ i, η i * u i (c i t) ∧
      ∀ x, 0 ≤ x → negishiUtility η u x ≤ ∑ i, η i * u i (c i t)
        + q t ⬝ᵥ (x - ∑ i, c i t) := fun t =>
    negishiUtility_props hηpos hconc (fun i => hc0 i t) (fun i => hD i t) (hq0 t)
      (fun i v => hqfoc t i v)
  have hcons : ∀ t, consumption (fun t => ∑ i, ω i t) y t = ∑ i, c i t := fun t => by
    rw [he.feasible t]; rfl
  obtain ⟨hWs, hW⟩ := sum_wealthI hθ0 hθ1 he.profitSummable he.endowSummable
  -- every consumer's budget binds
  have hbind : ∀ i, HasSum (fun t => p t ⬝ᵥ c i t) (wealthI θ p y ω i) := fun i =>
    budget_binds (fun _ h => h) (fun x hx x' hxx' => Set.mem_Ici.2 ((Set.mem_Ici.1 hx).trans
      hxx')) (hmono i) he.pricesNonneg (he.utilityMax i).1 (he.utilityMax i).2.1
      (fun c' hc' hdiff => (he.utilityMax i).2.2 c' hc'
        (summable_of_finite_change {0} (fun t ht => hdiff t (by simpa using ht))
          (he.utilityMax i).2.1))
  have hbindT : HasSum (fun t => p t ⬝ᵥ ∑ i, c i t)
      (∑' t, (periodProfit p y t + p t ⬝ᵥ ∑ i, ω i t)) := by
    rw [← hW]
    have := hasSum_sum (s := Finset.univ) fun i _ => hbind i
    exact this.congr_fun fun t => by rw [dotProduct_sum]
  have hsumU : Summable fun t => δ ^ t * negishiUtility η u (∑ i, c i t) := by
    have := summable_sum (s := Finset.univ) fun i _ => ((he.utilityMax i).2.1.mul_left (η i))
    refine this.congr fun t => ?_
    rw [(hprops t).1, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  refine ⟨η, hηpos, hcons, fun t => (hprops t).1, he.boundedPath, he.boundedPrices,
    he.pricesNonneg, fun t => ?_, he.myopic, hWs, ?_⟩
  · rw [hcons t]; exact Finset.sum_nonneg fun i _ => hc0 i t
  · refine ⟨⟨fun t => ?_, ?_, fun T => ?_⟩, ?_, fun C' hC' hsC' => ?_⟩
    · rw [hcons t]; exact Finset.sum_nonneg fun i _ => hc0 i t
    · choose Mi hMi using fun i => (he.utilityMax i).1.2.1
      refine ⟨∑ i, Mi i, fun t k => ?_⟩
      rw [hcons t, Finset.sum_apply]
      exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => hMi i t k)
    · have hnn : ∀ t, 0 ≤ p t ⬝ᵥ consumption (fun t => ∑ i, ω i t) y t := fun t => by
        rw [hcons t]
        exact dotProduct_nonneg_of_nonneg (he.pricesNonneg t)
          (Finset.sum_nonneg fun i _ => hc0 i t)
      have hb' : HasSum (fun t => p t ⬝ᵥ consumption (fun t => ∑ i, ω i t) y t)
          (∑' t, (periodProfit p y t + p t ⬝ᵥ ∑ i, ω i t)) :=
        hbindT.congr_fun fun t => by rw [hcons t]
      rw [← hb'.tsum_eq]
      exact hb'.summable.sum_le_tsum _ (fun t _ => hnn t)
    · simpa [hcons] using hsumU
    · -- the supergradient inequality, summed over dates
      obtain ⟨hsum', hle'⟩ := expenditure_summable he.pricesNonneg (fun t => hC'.1 t) hC'.2.2
      have hterm : ∀ t, δ ^ t * negishiUtility η u (C' t) ≤
          δ ^ t * negishiUtility η u (∑ i, c i t) + (p t ⬝ᵥ C' t - p t ⬝ᵥ ∑ i, c i t) := by
        intro t
        have h1 := (hprops t).2 (C' t) (hC'.1 t)
        rw [← (hprops t).1] at h1
        have hδt : 0 < δ ^ t := pow_pos hδ t
        have hpq : δ ^ t * (q t ⬝ᵥ (C' t - ∑ i, c i t)) = p t ⬝ᵥ C' t - p t ⬝ᵥ ∑ i, c i t := by
          simp only [hq, smul_dotProduct, smul_eq_mul, dotProduct_sub]
          field_simp
        nlinarith [mul_le_mul_of_nonneg_left h1 hδt.le]
      have hrhs : Summable fun t => δ ^ t * negishiUtility η u (∑ i, c i t)
          + (p t ⬝ᵥ C' t - p t ⬝ᵥ ∑ i, c i t) :=
        hsumU.add (hsum'.sub hbindT.summable)
      have := Summable.tsum_le_tsum hterm hsC' hrhs
      rw [hsumU.tsum_add (hsum'.sub hbindT.summable), hsum'.tsum_sub hbindT.summable,
        hbindT.tsum_eq] at this
      unfold discountedUtility
      have hC : consumption (fun t => ∑ i, ω i t) y = fun t => ∑ i, c i t := funext hcons
      rw [hC]
      linarith

/-! ### Exercise 20.G.1 -/

/-- **Exercise 20.G.1** (MWG, p. 785): one good, two consumers with a common discount factor
`0 < δ < 1` and aggregate endowment `ω₁ₜ + ω₂ₜ = 1`. At an interior equilibrium the first-order
conditions `λ_i p_t = δ^t u_i'(c_{it})` hold (Exercise 20.D.3, (20.D.6)) and each budget binds
(Proposition 20.D.1's argument). With strictly decreasing marginal utilities it follows that
consumption is stationary, prices are proportional `p_t = δ^t p₀` (rate of interest
`(1 - δ)/δ`), and consumer 1's consumption is uniquely `(1 - δ) ∑_t δ^t ω₁ₜ`. -/
theorem exercise_20_G_1 {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) {u1' u2' : ℝ → ℝ}
    (h1 : StrictAntiOn u1' (Set.Ioo 0 1)) (h2 : StrictAntiOn u2' (Set.Ioo 0 1))
    {c p ω : ℕ → ℝ} (hc : ∀ t, c t ∈ Set.Ioo 0 1) (hp : ∀ t, 0 < p t) {lam₁ lam₂ : ℝ}
    (hl₁ : 0 < lam₁) (hl₂ : 0 < lam₂) (hfoc₁ : ∀ t, lam₁ * p t = δ ^ t * u1' (c t))
    (hfoc₂ : ∀ t, lam₂ * p t = δ ^ t * u2' (1 - c t))
    (hbud : HasSum (fun t => p t * c t) (∑' t, p t * ω t)) :
    (∀ t, c t = c 0) ∧ (∀ t, p t = δ ^ t * p 0) ∧
      (∀ t, p t = (1 + (1 - δ) / δ) * p (t + 1)) ∧
      c 0 = (1 - δ) * ∑' t, δ ^ t * ω t := by
  -- `λ₂ u₁'(c_t) = λ₁ u₂'(1 - c_t)` and the left side minus the right is strictly decreasing
  have hkey : ∀ t, lam₂ * u1' (c t) - lam₁ * u2' (1 - c t) = 0 := by
    intro t
    have := pow_pos hδ0 t
    have e : δ ^ t * (lam₂ * u1' (c t) - lam₁ * u2' (1 - c t)) = 0 := by
      have a1 := hfoc₁ t
      have a2 := hfoc₂ t
      nlinarith
    exact (mul_eq_zero.1 e).resolve_left this.ne'
  have hmono : StrictAntiOn (fun x => lam₂ * u1' x - lam₁ * u2' (1 - x)) (Set.Ioo 0 1) := by
    intro x hx z hz hxz
    have a := h1 hx hz hxz
    have hx' : 1 - x ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [hx.2], by linarith [hx.1]⟩
    have hz' : 1 - z ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [hz.2], by linarith [hz.1]⟩
    have b := h2 hz' hx' (by linarith)
    simp only
    nlinarith
  have hconst : ∀ t, c t = c 0 := fun t =>
    hmono.injOn (hc t) (hc 0) ((hkey t).trans (hkey 0).symm)
  have hprop : ∀ t, p t = δ ^ t * p 0 := by
    intro t
    have a := hfoc₁ t
    have b := hfoc₁ 0
    rw [hconst t] at a
    simp only [pow_zero, one_mul] at b
    have : lam₁ * p t = lam₁ * (δ ^ t * p 0) := by rw [a, ← b]; ring
    exact mul_left_cancel₀ hl₁.ne' this
  refine ⟨hconst, hprop, fun t => ?_, ?_⟩
  · rw [hprop t, hprop (t + 1), pow_succ]; field_simp; ring
  · have hg := hasSum_geometric_of_lt_one hδ0.le hδ1
    have h1' : HasSum (fun t => p t * c t) (p 0 * c 0 * (1 - δ)⁻¹) := by
      have := (hg.mul_left (p 0 * c 0))
      exact this.congr_fun fun t => by rw [hprop t, hconst t]; ring
    have h2' : ∑' t, p t * ω t = p 0 * ∑' t, δ ^ t * ω t := by
      rw [← tsum_mul_left]; exact tsum_congr fun t => by rw [hprop t]; ring
    have := hbud.unique h1'
    rw [h2'] at this
    have hp0 := hp 0
    have h1δ : (1 : ℝ) - δ ≠ 0 := by linarith
    field_simp at this
    nlinarith

/-! ### Externalities: (20.G.5)-(20.G.6) and Exercise 20.G.5 -/

/-- **(20.G.6)** (MWG, p. 769): differentiating the equilibrium condition (20.G.5)
`∇₂u(k_{t-1}, k_t, k_t) + δ ∇₁u(k_t, k_{t+1}, k_{t+1}) = 0` along a solution `k_{t+1} = φ(k_t)`
(implicit function theorem) gives
`dk_{t+1}/dk_t = -(∇²₂₂u + ∇²₂₃u + δ∇²₁₁u) / (δ(∇²₁₂u + ∇²₁₃u))`. -/
theorem eq_20_G_6 {u22 u23 u11 u12 u13 δ dφ : ℝ} (hden : δ * (u12 + u13) ≠ 0)
    (htotal : (u22 + u23 + δ * u11) + δ * (u12 + u13) * dφ = 0) :
    dφ = -(u22 + u23 + δ * u11) / (δ * (u12 + u13)) := by
  rw [eq_div_iff hden]; linarith

/-- **Exercise 20.G.5** (MWG, p. 786): without externalities (`∇²₂₃u = ∇²₁₃u = 0`), concavity
(`∇²₁₁u ≤ 0`, `∇²₂₂u ≤ 0`, `(∇²₁₂u)² ≤ ∇²₁₁u ∇²₂₂u`), `∇²₁₂u ≠ 0` and `0 < δ < 1` make
(20.G.6) larger than one in absolute value. -/
theorem exercise_20_G_5 {u11 u22 u12 δ : ℝ} (h11 : u11 ≤ 0) (h22 : u22 ≤ 0)
    (hconc : u12 ^ 2 ≤ u11 * u22) (h12 : u12 ≠ 0) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    1 < |-(u22 + 0 + δ * u11) / (δ * (u12 + 0))| := by
  rw [add_zero, add_zero, abs_div, abs_neg, abs_mul, abs_of_pos hδ0,
    one_lt_div (mul_pos hδ0 (abs_pos.2 h12))]
  have hsum : |u22 + δ * u11| = -u22 + δ * -u11 := by
    rw [abs_of_nonpos (by nlinarith)]; ring
  rw [hsum]
  have hu12 : 0 < |u12| := abs_pos.2 h12
  have hsq : |u12| ^ 2 ≤ (-u11) * (-u22) := by rw [sq_abs]; linarith
  -- `(a + δb)² ≥ 4δab ≥ 4δ u12² > δ² u12²`
  have hs0 : 0 ≤ -u22 + δ * -u11 := by nlinarith
  have hsq2 : (δ * |u12|) ^ 2 < (-u22 + δ * -u11) ^ 2 := by
    have e1 : 4 * δ * ((-u11) * (-u22)) ≤ (-u22 + δ * -u11) ^ 2 := by
      nlinarith [sq_nonneg (-u22 - δ * -u11)]
    have e2 : 4 * δ * |u12| ^ 2 ≤ 4 * δ * ((-u11) * (-u22)) :=
      mul_le_mul_of_nonneg_left hsq (by linarith)
    have e3 : (δ * |u12|) ^ 2 < 4 * δ * |u12| ^ 2 := by
      have : 0 < δ * (4 - δ) * |u12| ^ 2 := by
        have := pow_pos hu12 2
        have h4 : 0 < 4 - δ := by linarith
        positivity
      nlinarith
    linarith
  exact lt_of_pow_lt_pow_left₀ 2 hs0 hsq2

/-- **The dampening criterion** (MWG, p. 769): if the linearized dynamics are
`x_{t+2} = a x_{t+1} + b x_t` with `|a| < 1/2` and `|b| < 1/2`, every perturbation dies out,
`x_t → 0`. -/
theorem dampening_of_small_coefficients {a b : ℝ} (ha : |a| < 1 / 2) (hb : |b| < 1 / 2)
    {x : ℕ → ℝ} (hrec : ∀ t, x (t + 2) = a * x (t + 1) + b * x t) :
    Tendsto x atTop (𝓝 0) := by
  set ρ := |a| + |b| with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ < 1 := by linarith
  set m : ℕ → ℝ := fun t => max |x t| |x (t + 1)| with hm
  have hstep : ∀ t, |x (t + 2)| ≤ ρ * m t := by
    intro t
    rw [hrec t]
    calc |a * x (t + 1) + b * x t| ≤ |a| * |x (t + 1)| + |b| * |x t| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ |a| * m t + |b| * m t := add_le_add
          (mul_le_mul_of_nonneg_left (le_max_right _ _) (abs_nonneg _))
          (mul_le_mul_of_nonneg_left (le_max_left _ _) (abs_nonneg _))
      _ = ρ * m t := by ring
  have hm0 : ∀ t, 0 ≤ m t := fun t => (abs_nonneg _).trans (le_max_left _ _)
  have hmono : ∀ t, m (t + 1) ≤ m t := by
    intro t
    refine max_le (le_max_right _ _) ?_
    exact (hstep t).trans ((mul_le_of_le_one_left (hm0 t) hρ1.le))
  have hdec : ∀ n, m (2 * n) ≤ ρ ^ n * m 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h1 : m (2 * (n + 1)) ≤ ρ * m (2 * n) := by
        rw [show 2 * (n + 1) = 2 * n + 2 by ring]
        refine max_le (hstep (2 * n)) ?_
        exact (hstep (2 * n + 1)).trans (mul_le_mul_of_nonneg_left (hmono _) hρ0)
      calc m (2 * (n + 1)) ≤ ρ * m (2 * n) := h1
        _ ≤ ρ * (ρ ^ n * m 0) := mul_le_mul_of_nonneg_left ih hρ0
        _ = ρ ^ (n + 1) * m 0 := by ring
  have hanti : Antitone m := antitone_nat_of_succ_le hmono
  have hbound : ∀ t, |x t| ≤ ρ ^ (t / 2) * m 0 := by
    intro t
    calc |x t| ≤ m t := le_max_left _ _
      _ ≤ m (2 * (t / 2)) := hanti (Nat.mul_div_le t 2)
      _ ≤ ρ ^ (t / 2) * m 0 := hdec _
  have hlim : Tendsto (fun t : ℕ => ρ ^ (t / 2) * m 0) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).comp
      (Nat.tendsto_div_const_atTop (by norm_num : (2 : ℕ) ≠ 0))
    simpa using this.mul_const (m 0)
  exact squeeze_zero_norm (fun t => by rw [Real.norm_eq_abs]; exact hbound t) hlim

end MWG.EquilibriumTime
