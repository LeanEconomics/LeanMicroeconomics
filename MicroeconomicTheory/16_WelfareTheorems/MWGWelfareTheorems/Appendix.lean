/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGWelfareTheorems.UtilityFrontier

/-!
# Appendix A: technical properties of the set of feasible allocations (MWG pp. 573-574)

The set `A` of feasible allocations is `PrefEconomy.feasiblePairs`, a subset of
`ℝ^{LI} × ℝ^{LJ}`; the aggregate production set is `Y = ∑ⱼ Yⱼ` (`aggregateProduction`).

* **Exercise 16.AA.1**: if every `Xᵢ` and `Yⱼ` is closed, `A` is closed.
* **Proposition 16.AA.1**: as printed, the aggregate production set `Y` is only assumed convex
  (not closed), and the text asserts that irreversibility "yields the closedness of `Y`". Both
  fail: `aaCounterEconomy` has closed `Xᵢ` bounded below, closed `Yⱼ`, and a convex aggregate `Y`
  with `0 ∈ Y`, no free lunch and irreversibility, yet `Y` is not closed and `A` is unbounded
  (`proposition_16_AA_1_counterexample`, correction 3). With `Y` closed (an added assumption) the
  proposition holds: `A` is bounded (`proposition_16_AA_1`), and nonempty when `-ℝ^L₊ ⊆ Y` and
  some `x̂ᵢ ∈ Xᵢ` have `∑ᵢ x̂ᵢ ≤ ω̄` (`proposition_16_AA_1_nonempty`). The proof is the standard
  normalization argument: an unbounded sequence of feasible allocations, scaled down, has a
  nonzero limit direction that the assumptions force to be zero.
* **Exercise 16.AA.2**: `(Y + {ω̄}) ∩ ℝ^L₊` is compact for closed convex `Y ∋ 0` without free
  lunch; each of the four assumptions is indispensable (four examples).
* **Exercise 16.AA.3**: with `0 ∈ Y₁, Y₂` and irreversibility of `Y = Y₁ + Y₂`, the feasible
  production plans of firm 1 are bounded.
* **Proposition 16.AA.2**: if `A` is nonempty and compact and the `uᵢ` are continuous, `U` is
  closed and bounded above.
-/

namespace MWG.WelfareTheorems

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.Production Kreps.PreferenceProperties
open MWG.CompetitiveMarkets (Allocation)
open Filter Topology

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {L : ℕ}

/-- **Appendix A** (MWG, p. 573). The aggregate production set `Y = ∑ⱼ Yⱼ`. -/
def aggregateProduction (Y : κ → Set (Fin L → ℝ)) : Set (Fin L → ℝ) :=
  {z | ∃ y : κ → Fin L → ℝ, (∀ j, y j ∈ Y j) ∧ z = ∑ j, y j}

/-- **Appendix A** (MWG, p. 573). The set `A ⊆ ℝ^{LI} × ℝ^{LJ}` of feasible allocations. -/
def PrefEconomy.feasiblePairs (E : PrefEconomy ι κ L) :
    Set ((ι → Fin L → ℝ) × (κ → Fin L → ℝ)) :=
  {z | E.IsFeasible ⟨z.1, z.2⟩}

/-- The nonnegative orthant is closed. -/
theorem isClosed_nonnegOrthant : IsClosed (nonnegOrthant L) := by
  simp only [nonnegOrthant, Set.ofPred_forall]
  exact isClosed_iInter fun l => isClosed_le continuous_const (continuous_apply l)

/-- The nonpositive orthant is closed. -/
theorem isClosed_nonposOrthant : IsClosed (nonposOrthant L) := by
  simp only [nonposOrthant, Set.ofPred_forall]
  exact isClosed_iInter fun l => isClosed_le (continuous_apply l) continuous_const

/-- **Exercise 16.AA.1** (MWG, p. 577). If every `Xᵢ` and every `Yⱼ` is closed, the set `A` of
feasible allocations is closed. -/
theorem exercise_16_AA_1 {E : PrefEconomy ι κ L} (hX : ∀ i, IsClosed (E.X i))
    (hY : ∀ j, IsClosed (E.Y j)) : IsClosed E.feasiblePairs := by
  have h1 : IsClosed {z : (ι → Fin L → ℝ) × (κ → Fin L → ℝ) | ∀ i, z.1 i ∈ E.X i} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => (hX i).preimage ((continuous_apply i).comp continuous_fst)
  have h2 : IsClosed {z : (ι → Fin L → ℝ) × (κ → Fin L → ℝ) | ∀ j, z.2 j ∈ E.Y j} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun j => (hY j).preimage ((continuous_apply j).comp continuous_snd)
  have h3 : IsClosed {z : (ι → Fin L → ℝ) × (κ → Fin L → ℝ) |
      ∑ i, z.1 i = E.ω + ∑ j, z.2 j} :=
    isClosed_eq (continuous_finsetSum _ fun i _ => (continuous_apply i).comp continuous_fst)
      (continuous_const.add
        (continuous_finsetSum _ fun j _ => (continuous_apply j).comp continuous_snd))
  have : E.feasiblePairs = {z | ∀ i, z.1 i ∈ E.X i} ∩ {z | ∀ j, z.2 j ∈ E.Y j} ∩
      {z | ∑ i, z.1 i = E.ω + ∑ j, z.2 j} := by
    ext z
    simp only [PrefEconomy.feasiblePairs, PrefEconomy.IsFeasible, PrefEconomy.IsAllocation,
      Set.mem_ofPred_eq, Set.mem_inter_iff, and_assoc]
  rw [this]
  exact (h1.inter h2).inter h3

/-- **Proposition 16.AA.1** (MWG, p. 573), nonemptiness. If `-ℝ^L₊ ⊆ Y` and some `x̂ᵢ ∈ Xᵢ`
satisfy `∑ᵢ x̂ᵢ ≤ ω̄`, then `A` is nonempty. -/
theorem proposition_16_AA_1_nonempty {E : PrefEconomy ι κ L}
    (hY : nonposOrthant L ⊆ aggregateProduction E.Y) {xh : ι → Fin L → ℝ}
    (hxh : ∀ i, xh i ∈ E.X i) (hle : ∑ i, xh i ≤ E.ω) : E.feasiblePairs.Nonempty := by
  obtain ⟨y, hy, hsum⟩ := hY (show ∑ i, xh i - E.ω ∈ nonposOrthant L from fun l => by
    have := hle l
    simp only [Pi.sub_apply]
    linarith)
  exact ⟨(xh, y), ⟨hxh, hy⟩, by rw [← hsum]; abel⟩

/-- A limit of scaled-down points `sₙ⁻¹ cₙ`, `sₙ ≥ 1`, of a closed convex set containing `0`
belongs to the set. -/
theorem mem_of_tendsto_inv_smul {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {Y : Set V} (hc : IsClosed Y) (hconv : Convex ℝ Y) (h0 : (0 : V) ∈ Y) {c : ℕ → V}
    {s : ℕ → ℝ} (hcY : ∀ n, c n ∈ Y) (hs : ∀ n, 1 ≤ s n) {d : V}
    (ht : Tendsto (fun n => (s n)⁻¹ • c n) atTop (𝓝 d)) : d ∈ Y :=
  hc.mem_of_tendsto ht (Eventually.of_forall fun n => hconv.smul_mem_of_zero_mem h0 (hcY n)
    ⟨inv_nonneg.mpr (by linarith [hs n]), inv_le_one_of_one_le₀ (hs n)⟩)

/-- **Proposition 16.AA.1** (MWG, p. 573), boundedness, with the aggregate production set `Y`
assumed closed (correction 3). If every `Xᵢ` is bounded below and `Y = ∑ⱼ Yⱼ` is closed and
convex, contains `0`, has no free lunch and is irreversible, there is `r > 0` with `|x_{ℓi}| < r`
and `|y_{ℓj}| < r` for every feasible allocation. (Closedness of the `Xᵢ` and `Yⱼ` is not needed
for boundedness.) -/
theorem proposition_16_AA_1 {E : PrefEconomy ι κ L}
    (hXb : ∀ i, ∃ r : ℝ, ∀ x ∈ E.X i, ∀ l, -r < x l)
    (hYc : IsClosed (aggregateProduction E.Y)) (hYconv : Convex ℝ (aggregateProduction E.Y))
    (hY0 : (0 : Fin L → ℝ) ∈ aggregateProduction E.Y)
    (hnfl : ∀ y ∈ aggregateProduction E.Y, (∀ l, 0 ≤ y l) → y = 0)
    (hirr : ∀ y ∈ aggregateProduction E.Y, -y ∈ aggregateProduction E.Y → y = 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ a : Allocation ι κ L, E.IsFeasible a →
      (∀ i l, |a.x i l| < r) ∧ ∀ j l, |a.y j l| < r := by
  classical
  -- it suffices to bound the norm of `(x, y)`
  suffices hR : ∃ R : ℝ, ∀ a : Allocation ι κ L, E.IsFeasible a → ‖(a.x, a.y)‖ ≤ R by
    obtain ⟨R, hR⟩ := hR
    refine ⟨|R| + 1, by positivity, fun a ha => ⟨fun i l => ?_, fun j l => ?_⟩⟩
    · calc |a.x i l| = ‖a.x i l‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖a.x i‖ := norm_le_pi_norm _ l
        _ ≤ ‖a.x‖ := norm_le_pi_norm _ i
        _ ≤ ‖(a.x, a.y)‖ := by rw [Prod.norm_def]; exact le_max_left _ _
        _ ≤ R := hR a ha
        _ < |R| + 1 := by linarith [le_abs_self R]
    · calc |a.y j l| = ‖a.y j l‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖a.y j‖ := norm_le_pi_norm _ l
        _ ≤ ‖a.y‖ := norm_le_pi_norm _ j
        _ ≤ ‖(a.x, a.y)‖ := by rw [Prod.norm_def]; exact le_max_right _ _
        _ ≤ R := hR a ha
        _ < |R| + 1 := by linarith [le_abs_self R]
  by_contra hno
  push Not at hno
  have hex : ∀ n : ℕ, ∃ a : Allocation ι κ L, E.IsFeasible a ∧ (n : ℝ) + 1 < ‖(a.x, a.y)‖ :=
    fun n => hno _
  choose a ha hbig using hex
  set s : ℕ → ℝ := fun n => ‖((a n).x, (a n).y)‖ with hs
  have hs1 : ∀ n, 1 ≤ s n := fun n => by
    have := hbig n; have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; simp only [hs]; linarith
  have hspos : ∀ n, 0 < s n := fun n => by linarith [hs1 n]
  set w : ℕ → (ι → Fin L → ℝ) × (κ → Fin L → ℝ) := fun n => (s n)⁻¹ • ((a n).x, (a n).y)
    with hw
  have hwS : ∀ n, w n ∈ Metric.sphere (0 : (ι → Fin L → ℝ) × (κ → Fin L → ℝ)) 1 := by
    intro n
    rw [mem_sphere_zero_iff_norm, hw, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (hspos n))]
    exact inv_mul_cancel₀ (hspos n).ne'
  obtain ⟨z, hzS, φ, hφ, hlim⟩ := (isCompact_sphere _ _).tendsto_subseq hwS
  have hz1 : ‖z‖ = 1 := mem_sphere_zero_iff_norm.mp hzS
  -- the scale tends to infinity along the subsequence
  have hinv : Tendsto (fun n => (s (φ n))⁻¹) atTop (𝓝 0) := by
    refine tendsto_inv_atTop_zero.comp (tendsto_atTop_mono (fun n => ?_)
      (tendsto_natCast_atTop_atTop (R := ℝ)))
    have h1 := hbig (φ n)
    have h2 : (n : ℝ) ≤ φ n := by exact_mod_cast hφ.id_le n
    simp only [hs]
    linarith
  have hx : ∀ i, Tendsto (fun n => (s (φ n))⁻¹ • (a (φ n)).x i) atTop (𝓝 (z.1 i)) := by
    intro i
    have := ((continuous_apply i).comp continuous_fst).continuousAt.tendsto.comp hlim
    simpa [hw, Function.comp_def] using this
  have hy : ∀ j, Tendsto (fun n => (s (φ n))⁻¹ • (a (φ n)).y j) atTop (𝓝 (z.2 j)) := by
    intro j
    have := ((continuous_apply j).comp continuous_snd).continuousAt.tendsto.comp hlim
    simpa [hw, Function.comp_def] using this
  -- Step 1: the consumption directions are nonnegative
  have hxnn : ∀ i l, 0 ≤ z.1 i l := by
    intro i l
    obtain ⟨r, hr⟩ := hXb i
    have hcoord : Tendsto (fun n => (s (φ n))⁻¹ * (a (φ n)).x i l) atTop (𝓝 (z.1 i l)) := by
      have := ((continuous_apply l).continuousAt.tendsto).comp (hx i)
      simpa [Function.comp_def] using this
    have hlow : Tendsto (fun n => (s (φ n))⁻¹ * -r) atTop (𝓝 0) := by
      simpa using hinv.mul_const (-r)
    exact le_of_tendsto_of_tendsto hlow hcoord (Eventually.of_forall fun n =>
      mul_le_mul_of_nonneg_left (hr _ ((ha (φ n)).1.1 i) l).le
        (inv_nonneg.mpr (hspos _).le))
  -- membership of scaled production limits in `Y`
  have hmemY : ∀ (T : Finset κ) (c : ℕ → Fin L → ℝ), (∀ n, c n ∈ aggregateProduction E.Y) →
      Tendsto (fun n => (s (φ n))⁻¹ • c n) atTop (𝓝 (∑ j ∈ T, z.2 j)) →
      ∑ j ∈ T, z.2 j ∈ aggregateProduction E.Y := fun T c hc ht =>
    mem_of_tendsto_inv_smul hYc hYconv hY0 hc (fun n => hs1 (φ n)) ht
  -- a fixed feasible production plan
  set y0 := (a 0).y with hy0
  have hy0Y : ∀ j, y0 j ∈ E.Y j := (ha 0).1.2
  -- the mixed plan: firms in `T` use the `n`-th plans, the others the fixed plan
  set mix : Finset κ → ℕ → κ → Fin L → ℝ := fun T n j =>
    if j ∈ T then (a (φ n)).y j else y0 j with hmix
  have hmixY : ∀ T n, ∑ j, mix T n j ∈ aggregateProduction E.Y := fun T n =>
    ⟨mix T n, fun j => by
      by_cases hj : j ∈ T
      · simp only [hmix, hj, ↓reduceIte]; exact (ha (φ n)).1.2 j
      · simp only [hmix, hj, ↓reduceIte]; exact hy0Y j, rfl⟩
  have hmixT : ∀ T : Finset κ,
      Tendsto (fun n => (s (φ n))⁻¹ • ∑ j, mix T n j) atTop (𝓝 (∑ j ∈ T, z.2 j)) := by
    intro T
    have hsplit : ∀ n, (s (φ n))⁻¹ • ∑ j, mix T n j =
        ∑ j ∈ T, (s (φ n))⁻¹ • (a (φ n)).y j + (s (φ n))⁻¹ • ∑ j ∈ Finset.univ \ T, y0 j := by
      intro n
      rw [← Finset.sum_sdiff (Finset.subset_univ T), smul_add, Finset.smul_sum,
        Finset.smul_sum, Finset.smul_sum, add_comm]
      congr 1
      · exact Finset.sum_congr rfl fun j hj => by simp [hmix, hj]
      · exact Finset.sum_congr rfl fun j hj => by
          simp [hmix, (Finset.mem_sdiff.mp hj).2]
    simp_rw [hsplit]
    have h1 : Tendsto (fun n => ∑ j ∈ T, (s (φ n))⁻¹ • (a (φ n)).y j) atTop
        (𝓝 (∑ j ∈ T, z.2 j)) := tendsto_finsetSum T fun j _ => hy j
    have h2 : Tendsto (fun n => (s (φ n))⁻¹ • ∑ j ∈ Finset.univ \ T, y0 j) atTop (𝓝 0) := by
      simpa using hinv.smul_const (∑ j ∈ Finset.univ \ T, y0 j)
    simpa using h1.add h2
  have hTY : ∀ T : Finset κ, ∑ j ∈ T, z.2 j ∈ aggregateProduction E.Y := fun T =>
    hmemY T _ (hmixY T) (hmixT T)
  -- Step 2: the aggregate direction equals the consumption direction
  have hsumeq : ∑ i, z.1 i = ∑ j, z.2 j := by
    have hfeas : ∀ n, ∑ i, (s (φ n))⁻¹ • (a (φ n)).x i =
        (s (φ n))⁻¹ • E.ω + ∑ j, (s (φ n))⁻¹ • (a (φ n)).y j := fun n => by
      rw [← Finset.smul_sum, ← Finset.smul_sum, (ha (φ n)).2, smul_add]
    have h1 : Tendsto (fun n => ∑ i, (s (φ n))⁻¹ • (a (φ n)).x i) atTop (𝓝 (∑ i, z.1 i)) :=
      tendsto_finsetSum _ fun i _ => hx i
    have h2 : Tendsto (fun n => (s (φ n))⁻¹ • E.ω + ∑ j, (s (φ n))⁻¹ • (a (φ n)).y j) atTop
        (𝓝 (∑ j, z.2 j)) := by
      have := (hinv.smul_const E.ω).add (tendsto_finsetSum Finset.univ fun j _ => hy j)
      simpa using this
    simp_rw [hfeas] at h1
    exact tendsto_nhds_unique h1 h2
  -- Step 3: no free lunch kills the aggregate direction and the consumption directions
  have hagg0 : ∑ j, z.2 j = 0 := by
    refine hnfl _ (by simpa using hTY Finset.univ) fun l => ?_
    rw [← hsumeq, Finset.sum_apply]
    exact Finset.sum_nonneg fun i _ => hxnn i l
  have hx0 : ∀ i, z.1 i = 0 := by
    have hsum0 : ∑ i, z.1 i = 0 := hsumeq.trans hagg0
    intro i
    funext l
    have := congrFun hsum0 l
    rw [Finset.sum_apply] at this
    exact (Finset.sum_eq_zero_iff_of_nonneg fun k _ => hxnn k l).mp this i (Finset.mem_univ i)
  -- Step 4: irreversibility kills every firm's direction
  have hy0' : ∀ j, z.2 j = 0 := by
    intro j
    have hj : z.2 j ∈ aggregateProduction E.Y := by simpa using hTY {j}
    have hrest : -z.2 j ∈ aggregateProduction E.Y := by
      have h1 := hTY (Finset.univ.erase j)
      have h2 : ∑ k ∈ Finset.univ.erase j, z.2 k = -z.2 j := by
        rw [eq_neg_iff_add_eq_zero, add_comm, Finset.add_sum_erase _ _ (Finset.mem_univ j),
          hagg0]
      rwa [h2] at h1
    exact hirr _ hj hrest
  have : z = 0 := Prod.ext (funext hx0) (funext hy0')
  rw [this, norm_zero] at hz1
  exact zero_ne_one hz1

/-! ## The counterexample to Proposition 16.AA.1 as printed -/

/-- Firm 1 of the counterexample: `{0} ∪ {(a, b) : a ≥ 0, ab ≤ -1}` (closed, not convex). -/
def aaY1 : Set (Fin 2 → ℝ) := {y | y = 0 ∨ (0 ≤ y 0 ∧ y 0 * y 1 ≤ -1)}

/-- **Proposition 16.AA.1** counterexample economy: one consumer with `X = ℝ²₊`, `ω̄ = (1, 1)`,
firm 1 with `aaY1`, firm 2 with free disposal. -/
def aaCounterEconomy : PrefEconomy Unit (Fin 2) 2 where
  X := fun _ => nonnegOrthant 2
  pref := fun _ _ _ => True
  Y := ![aaY1, nonposOrthant 2]
  ω := ![1, 1]

/-- The aggregate production set of `aaCounterEconomy` is
`{y : y₂ < 0} ∪ {(y₁, 0) : y₁ ≤ 0}`. -/
theorem aaCounter_agg (z : Fin 2 → ℝ) :
    z ∈ aggregateProduction aaCounterEconomy.Y ↔ z 1 < 0 ∨ (z 1 = 0 ∧ z 0 ≤ 0) := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    have h1 : y 1 ∈ nonposOrthant 2 := hy 1
    simp only [Fin.sum_univ_two, Pi.add_apply]
    rcases hy 0 with h0 | ⟨ha, hab⟩
    · rw [h0]
      simp only [Pi.zero_apply, zero_add]
      rcases (h1 1).lt_or_eq with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h, h1 0⟩
    · left
      have hb : y 0 1 < 0 := by
        by_contra hb
        push Not at hb
        nlinarith
      linarith [h1 1]
  · rintro (h | ⟨h1, h0⟩)
    · set A := max (max 1 (z 0)) (-1 / z 1) with hA
      have hA1 : 1 ≤ A := le_trans (le_max_left _ _) (le_max_left _ _)
      have hA0 : z 0 ≤ A := le_trans (le_max_right _ _) (le_max_left _ _)
      have hAz : -1 / z 1 ≤ A := le_max_right _ _
      refine ⟨![![A, z 1], ![z 0 - A, 0]], fun j => ?_, ?_⟩
      · fin_cases j
        · right
          refine ⟨by simp; linarith, ?_⟩
          simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
          rw [div_le_iff_of_neg h] at hAz
          linarith
        · intro l
          fin_cases l
          · simp; linarith
          · simp
      · funext l
        fin_cases l <;> simp
    · refine ⟨![0, z], fun j => ?_, ?_⟩
      · fin_cases j
        · left; rfl
        · intro l
          fin_cases l
          · simpa using h0
          · simp [h1]
      · simp

/-- **Proposition 16.AA.1** (MWG, pp. 573-574), correction 3. In `aaCounterEconomy` every
assumption of Proposition 16.AA.1 as printed holds (`Xᵢ` closed and bounded below; `Yⱼ` closed;
`Y` convex with `0 ∈ Y`, no free lunch and irreversibility), but `Y` is not closed (so
irreversibility does not yield closedness of `Y`, contrary to p. 574) and the set of feasible
allocations is unbounded. -/
theorem proposition_16_AA_1_counterexample :
    (∀ i, IsClosed (aaCounterEconomy.X i)) ∧
    (∀ i, ∀ x ∈ aaCounterEconomy.X i, ∀ l, -1 < x l) ∧
    (∀ j, IsClosed (aaCounterEconomy.Y j)) ∧
    Convex ℝ (aggregateProduction aaCounterEconomy.Y) ∧
    (0 : Fin 2 → ℝ) ∈ aggregateProduction aaCounterEconomy.Y ∧
    (∀ y ∈ aggregateProduction aaCounterEconomy.Y, (∀ l, 0 ≤ y l) → y = 0) ∧
    (∀ y ∈ aggregateProduction aaCounterEconomy.Y,
      -y ∈ aggregateProduction aaCounterEconomy.Y → y = 0) ∧
    ¬ IsClosed (aggregateProduction aaCounterEconomy.Y) ∧
    ∀ r : ℝ, ∃ a : Allocation Unit (Fin 2) 2, aaCounterEconomy.IsFeasible a ∧ r < a.y 0 0 := by
  refine ⟨fun _ => ?_, fun _ x hx l => by linarith [hx l], fun j => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact isClosed_nonnegOrthant
  · fin_cases j
    · have : aaY1 = {y : Fin 2 → ℝ | y = 0} ∪ ({y | 0 ≤ y 0} ∩ {y | y 0 * y 1 ≤ -1}) := by
        ext y; simp [aaY1]
      change IsClosed aaY1
      rw [this]
      exact isClosed_singleton.union ((isClosed_le continuous_const (continuous_apply 0)).inter
        (isClosed_le ((continuous_apply 0).mul (continuous_apply 1)) continuous_const))
    · exact isClosed_nonposOrthant
  · intro x hx y hy α β hα hβ hαβ
    rw [aaCounter_agg] at hx hy ⊢
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases hx with hx | ⟨hx1, hx0⟩ <;> rcases hy with hy | ⟨hy1, hy0⟩
    · left
      rcases hα.lt_or_eq with ha | ha
      · nlinarith [mul_neg_of_pos_of_neg ha hx, mul_nonpos_of_nonneg_of_nonpos hβ hy.le]
      · subst ha; rw [zero_add] at hαβ; subst hαβ; simpa using hy
    · rcases hα.lt_or_eq with ha | ha
      · left; rw [hy1]; nlinarith [mul_neg_of_pos_of_neg ha hx]
      · subst ha; rw [zero_add] at hαβ; subst hαβ; right; simp [hy1, hy0]
    · rcases hβ.lt_or_eq with hb | hb
      · left; rw [hx1]; nlinarith [mul_neg_of_pos_of_neg hb hy]
      · subst hb; rw [add_zero] at hαβ; subst hαβ; right; simp [hx1, hx0]
    · right
      rw [hx1, hy1]
      refine ⟨by ring, ?_⟩
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hα hx0, mul_nonpos_of_nonneg_of_nonpos hβ hy0]
  · rw [aaCounter_agg]; right; simp
  · intro y hy hnn
    rw [aaCounter_agg] at hy
    rcases hy with h | ⟨h1, h0⟩
    · linarith [hnn 1]
    · funext l; fin_cases l
      · exact le_antisymm h0 (hnn 0)
      · exact h1
  · intro y hy hny
    rw [aaCounter_agg] at hy hny
    simp only [Pi.neg_apply] at hny
    rcases hy with h | ⟨h1, h0⟩
    · rcases hny with h' | ⟨h', -⟩ <;> linarith
    · rcases hny with h' | ⟨-, h0'⟩
      · linarith
      · funext l; fin_cases l
        · change y 0 = 0; linarith
        · exact h1
  · intro hc
    have hmem : ∀ n : ℕ, (![1, -1 / ((n : ℝ) + 1)] : Fin 2 → ℝ) ∈
        aggregateProduction aaCounterEconomy.Y := fun n => by
      rw [aaCounter_agg]; left
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
      have : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      exact div_neg_of_neg_of_pos (by norm_num) this
    have ht : Tendsto (fun n : ℕ => (![1, -1 / ((n : ℝ) + 1)] : Fin 2 → ℝ)) atTop
        (𝓝 ![1, 0]) := by
      rw [tendsto_pi_nhds]
      intro l
      fin_cases l
      · simp
      · change Tendsto (fun n : ℕ => -1 / ((n : ℝ) + 1)) atTop (𝓝 0)
        have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).neg
        rw [neg_zero] at this
        exact this.congr fun n => by ring
    have := hc.mem_of_tendsto ht (Eventually.of_forall hmem)
    rw [aaCounter_agg] at this
    norm_num at this
  · intro r
    set t := max r 1 + 1 with ht
    have ht1 : 1 ≤ t := by linarith [le_max_right r 1]
    have ht0 : 0 < t := by linarith
    refine ⟨⟨fun _ => ![1, 1 - 1 / t], ![![t, -1 / t], ![-t, 0]]⟩, ⟨⟨fun _ l => ?_, fun j => ?_⟩,
      ?_⟩, ?_⟩
    · fin_cases l
      · simp
      · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
        have : 1 / t ≤ 1 := by rw [div_le_one ht0]; exact ht1
        linarith
    · fin_cases j
      · right
        simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
        refine ⟨ht0.le, ?_⟩
        field_simp
        rfl
      · intro l
        fin_cases l
        · simp; linarith
        · simp
    · funext l
      fin_cases l
      · simp [aaCounterEconomy, Fin.sum_univ_two]
      · simp [aaCounterEconomy, Fin.sum_univ_two]; ring
    · simp only [Matrix.cons_val_zero]
      linarith [le_max_left r 1]

/-! ## Exercise 16.AA.2 -/

/-- **Exercise 16.AA.2** (MWG, p. 577). If `Y` is closed and convex, `0 ∈ Y`, and `Y ∩ ℝ^L₊ ⊆ {0}`,
then `(Y + {ω̄}) ∩ ℝ^L₊` is compact. -/
theorem exercise_16_AA_2 {Y : Set (Fin L → ℝ)} (hc : IsClosed Y) (hconv : Convex ℝ Y)
    (h0 : (0 : Fin L → ℝ) ∈ Y) (hnfl : ∀ y ∈ Y, (∀ l, 0 ≤ y l) → y = 0) (ω : Fin L → ℝ) :
    IsCompact {z | z - ω ∈ Y ∧ ∀ l, 0 ≤ z l} := by
  have hclosed : IsClosed {z : Fin L → ℝ | z - ω ∈ Y ∧ ∀ l, 0 ≤ z l} :=
    (hc.preimage (continuous_id.sub continuous_const)).inter isClosed_nonnegOrthant
  refine Metric.isCompact_of_isClosed_isBounded hclosed ?_
  rw [Metric.isBounded_iff_subset_closedBall 0]
  by_contra hno
  push Not at hno
  have hex : ∀ n : ℕ, ∃ z, (z - ω ∈ Y ∧ ∀ l, 0 ≤ z l) ∧ (n : ℝ) + 1 + ‖ω‖ < ‖z‖ := by
    intro n
    obtain ⟨z, hz, hzb⟩ := Set.not_subset.mp (hno ((n : ℝ) + 1 + ‖ω‖))
    refine ⟨z, hz, ?_⟩
    simpa [Metric.mem_closedBall, dist_zero_right] using hzb
  choose z hz hbig using hex
  set c : ℕ → Fin L → ℝ := fun n => z n - ω with hcdef
  set s : ℕ → ℝ := fun n => ‖c n‖ with hs
  have hs1 : ∀ n : ℕ, (n : ℝ) + 1 ≤ s n := fun n => by
    have h1 := hbig n
    have h2 := norm_sub_norm_le (z n) ω
    simp only [hs, hcdef]
    linarith
  have hs1' : ∀ n, 1 ≤ s n := fun n => by linarith [hs1 n, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hspos : ∀ n, 0 < s n := fun n => by linarith [hs1' n]
  have hwS : ∀ n, (s n)⁻¹ • c n ∈ Metric.sphere (0 : Fin L → ℝ) 1 := fun n => by
    rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr
      (hspos n))]
    exact inv_mul_cancel₀ (hspos n).ne'
  obtain ⟨d, hdS, φ, hφ, hlim⟩ := (isCompact_sphere _ _).tendsto_subseq hwS
  have hinv : Tendsto (fun n => (s (φ n))⁻¹) atTop (𝓝 0) := by
    refine tendsto_inv_atTop_zero.comp (tendsto_atTop_mono (fun n => ?_)
      (tendsto_natCast_atTop_atTop (R := ℝ)))
    have h2 : (n : ℝ) ≤ φ n := by exact_mod_cast hφ.id_le n
    linarith [hs1 (φ n)]
  have hdY : d ∈ Y := mem_of_tendsto_inv_smul hc hconv h0 (fun n => (hz (φ n)).1)
    (fun n => hs1' (φ n)) hlim
  have hdnn : ∀ l, 0 ≤ d l := by
    intro l
    have hcoord : Tendsto (fun n => (s (φ n))⁻¹ * c (φ n) l) atTop (𝓝 (d l)) := by
      have := ((continuous_apply l).continuousAt.tendsto).comp hlim
      simpa [Function.comp_def] using this
    have hlow : Tendsto (fun n => (s (φ n))⁻¹ * -ω l) atTop (𝓝 0) := by
      simpa using hinv.mul_const (-ω l)
    refine le_of_tendsto_of_tendsto hlow hcoord (Eventually.of_forall fun n => ?_)
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (hspos _).le)
    simp only [hcdef, Pi.sub_apply]
    linarith [(hz (φ n)).2 l]
  have := hnfl d hdY hdnn
  rw [this, mem_sphere_zero_iff_norm, norm_zero] at hdS
  exact zero_ne_one hdS

/-- **Exercise 16.AA.2** (MWG, p. 577): closedness of `Y` is indispensable. `Y = (-1, 0] ⊆ ℝ`
is convex, contains `0` and has no free lunch, but `(Y + {1}) ∩ ℝ₊ = (0, 1]` is not compact. -/
theorem exercise_16_AA_2_needs_closed :
    Convex ℝ {y : Fin 1 → ℝ | -1 < y 0 ∧ y 0 ≤ 0} ∧ (0 : Fin 1 → ℝ) ∈ {y | -1 < y 0 ∧ y 0 ≤ 0} ∧
      (∀ y ∈ {y : Fin 1 → ℝ | -1 < y 0 ∧ y 0 ≤ 0}, (∀ l, 0 ≤ y l) → y = 0) ∧
      ¬ IsCompact {z : Fin 1 → ℝ | z - ![1] ∈ {y : Fin 1 → ℝ | -1 < y 0 ∧ y 0 ≤ 0} ∧
        ∀ l, 0 ≤ z l} := by
  refine ⟨?_, by simp, fun y hy hnn => funext fun l => ?_, fun hK => ?_⟩
  · intro x hx y hy a b ha hb hab
    simp only [Set.mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hx hy ⊢
    constructor
    · rcases ha.lt_or_eq with ha' | ha'
      · nlinarith [mul_lt_mul_of_pos_left hx.1 ha', mul_le_mul_of_nonneg_left hy.1.le hb]
      · subst ha'
        have hb1 : b = 1 := by linarith
        subst hb1
        simpa using hy.1
    · nlinarith [mul_nonpos_of_nonneg_of_nonpos ha hx.2, mul_nonpos_of_nonneg_of_nonpos hb hy.2]
  · fin_cases l; exact le_antisymm hy.2 (hnn 0)
  · have hmem : ∀ n : ℕ, (![1 / ((n : ℝ) + 1)] : Fin 1 → ℝ) ∈ {z : Fin 1 → ℝ |
        z - ![1] ∈ {y : Fin 1 → ℝ | -1 < y 0 ∧ y 0 ≤ 0} ∧ ∀ l, 0 ≤ z l} := fun n => by
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      have hle : 1 / ((n : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      refine ⟨⟨?_, ?_⟩, fun l => ?_⟩
      · change -1 < 1 / ((n : ℝ) + 1) - 1; linarith
      · change 1 / ((n : ℝ) + 1) - 1 ≤ 0; linarith
      · fin_cases l; exact hpos.le
    have ht : Tendsto (fun n : ℕ => (![1 / ((n : ℝ) + 1)] : Fin 1 → ℝ)) atTop (𝓝 0) := by
      rw [tendsto_pi_nhds]
      intro l; fin_cases l
      exact tendsto_one_div_add_atTop_nhds_zero_nat
    have := hK.isClosed.mem_of_tendsto ht (Eventually.of_forall hmem)
    simp at this

/-- **Exercise 16.AA.2** (MWG, p. 577): convexity of `Y` is indispensable. The closed set
`aaY1 = {0} ∪ {(a, b) : a ≥ 0, ab ≤ -1}` contains `0` and has no free lunch, but
`(Y + {(1, 1)}) ∩ ℝ²₊` is unbounded. -/
theorem exercise_16_AA_2_needs_convex :
    IsClosed aaY1 ∧ (0 : Fin 2 → ℝ) ∈ aaY1 ∧ (∀ y ∈ aaY1, (∀ l, 0 ≤ y l) → y = 0) ∧
      ¬ IsCompact {z : Fin 2 → ℝ | z - ![1, 1] ∈ aaY1 ∧ ∀ l, 0 ≤ z l} := by
  have hclosed := (proposition_16_AA_1_counterexample.2.2.1 0)
  refine ⟨hclosed, Or.inl rfl, fun y hy hnn => ?_, fun hK => ?_⟩
  · rcases hy with h | ⟨-, h⟩
    · exact h
    · nlinarith [mul_nonneg (hnn 0) (hnn 1)]
  · obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
    set t := max R 1 + 1 with ht
    have ht1 : 1 < t := by linarith [le_max_right R 1]
    have hmem : (![1 + t, 0] : Fin 2 → ℝ) ∈ {z : Fin 2 → ℝ | z - ![1, 1] ∈ aaY1 ∧
        ∀ l, 0 ≤ z l} := by
      refine ⟨Or.inr ⟨by simp; linarith, by simp; linarith⟩, fun l => ?_⟩
      fin_cases l
      · simp; linarith
      · simp
    have h1 := hR hmem
    rw [Metric.mem_closedBall, dist_zero_right] at h1
    have h2 : |(![1 + t, 0] : Fin 2 → ℝ) 0| ≤ ‖(![1 + t, 0] : Fin 2 → ℝ)‖ := by
      rw [← Real.norm_eq_abs]; exact norm_le_pi_norm _ 0
    simp only [Matrix.cons_val_zero] at h2
    rw [abs_of_pos (by linarith)] at h2
    linarith [le_max_left R 1]

/-- **Exercise 16.AA.2** (MWG, p. 577): `0 ∈ Y` is indispensable. `Y = {y : y₂ ≤ -1}` is closed
and convex with `Y ∩ ℝ²₊ = ∅`, but `(Y + {(1, 1)}) ∩ ℝ²₊` is unbounded. -/
theorem exercise_16_AA_2_needs_zero :
    IsClosed {y : Fin 2 → ℝ | y 1 ≤ -1} ∧ Convex ℝ {y : Fin 2 → ℝ | y 1 ≤ -1} ∧
      (0 : Fin 2 → ℝ) ∉ {y : Fin 2 → ℝ | y 1 ≤ -1} ∧
      (∀ y ∈ {y : Fin 2 → ℝ | y 1 ≤ -1}, (∀ l, 0 ≤ y l) → y = 0) ∧
      ¬ IsCompact {z : Fin 2 → ℝ | z - ![1, 1] ∈ {y : Fin 2 → ℝ | y 1 ≤ -1} ∧ ∀ l, 0 ≤ z l} := by
  refine ⟨isClosed_le (continuous_apply 1) continuous_const, ?_, by simp, fun y hy hnn => ?_,
    fun hK => ?_⟩
  · intro x hx y hy a b ha hb hab
    simp only [Set.mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hx hy ⊢
    nlinarith
  · exact absurd (hnn 1) (by simp only [Set.mem_ofPred_eq] at hy; linarith)
  · obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
    set t := max R 1 + 1 with ht
    have hmem : (![t, 0] : Fin 2 → ℝ) ∈ {z : Fin 2 → ℝ |
        z - ![1, 1] ∈ {y : Fin 2 → ℝ | y 1 ≤ -1} ∧ ∀ l, 0 ≤ z l} := by
      refine ⟨by simp, fun l => ?_⟩
      fin_cases l <;> simp; linarith [le_max_right R 1]
    have h1 := hR hmem
    rw [Metric.mem_closedBall, dist_zero_right] at h1
    have h2 : |(![t, 0] : Fin 2 → ℝ) 0| ≤ ‖(![t, 0] : Fin 2 → ℝ)‖ := by
      rw [← Real.norm_eq_abs]; exact norm_le_pi_norm _ 0
    simp only [Matrix.cons_val_zero] at h2
    rw [abs_of_pos (by linarith [le_max_right R 1])] at h2
    linarith [le_max_left R 1]

/-- **Exercise 16.AA.2** (MWG, p. 577): no free lunch is indispensable. `Y = ℝ` is closed and
convex with `0 ∈ Y`, and `(Y + {1}) ∩ ℝ₊ = ℝ₊` is unbounded. -/
theorem exercise_16_AA_2_needs_no_free_lunch :
    ¬ IsCompact {z : Fin 1 → ℝ | z - ![1] ∈ (Set.univ : Set (Fin 1 → ℝ)) ∧ ∀ l, 0 ≤ z l} := by
  intro hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  set t := max R 1 + 1 with ht
  have hmem : (![t] : Fin 1 → ℝ) ∈ {z : Fin 1 → ℝ | z - ![1] ∈ (Set.univ : Set (Fin 1 → ℝ)) ∧
      ∀ l, 0 ≤ z l} := ⟨trivial, fun l => by fin_cases l; simp; linarith [le_max_right R 1]⟩
  have h1 := hR hmem
  rw [Metric.mem_closedBall, dist_zero_right] at h1
  have h2 : |(![t] : Fin 1 → ℝ) 0| ≤ ‖(![t] : Fin 1 → ℝ)‖ := by
    rw [← Real.norm_eq_abs]; exact norm_le_pi_norm _ 0
  simp only [Matrix.cons_val_zero] at h2
  rw [abs_of_pos (by linarith [le_max_right R 1])] at h2
  linarith [le_max_left R 1]

/-! ## Exercise 16.AA.3 -/

/-- **Exercise 16.AA.3** (MWG, p. 577). If `Y = Y₁ + Y₂` satisfies the assumptions of Exercise
16.AA.2 (closed, convex, no free lunch), `0 ∈ Y₁`, `0 ∈ Y₂` and `Y` is irreversible, then the set
`{y₁ ∈ Y₁ : y₁ + y₂ + ω̄ ≥ 0 for some y₂ ∈ Y₂}` is bounded. -/
theorem exercise_16_AA_3 {Y₁ Y₂ : Set (Fin L → ℝ)}
    (hc : IsClosed {z | ∃ y₁ ∈ Y₁, ∃ y₂ ∈ Y₂, z = y₁ + y₂})
    (hconv : Convex ℝ {z | ∃ y₁ ∈ Y₁, ∃ y₂ ∈ Y₂, z = y₁ + y₂})
    (hnfl : ∀ y ∈ {z | ∃ y₁ ∈ Y₁, ∃ y₂ ∈ Y₂, z = y₁ + y₂}, (∀ l, 0 ≤ y l) → y = 0)
    (h01 : (0 : Fin L → ℝ) ∈ Y₁) (h02 : (0 : Fin L → ℝ) ∈ Y₂)
    (hirr : ∀ y ∈ {z | ∃ y₁ ∈ Y₁, ∃ y₂ ∈ Y₂, z = y₁ + y₂},
      -y ∈ {z | ∃ y₁ ∈ Y₁, ∃ y₂ ∈ Y₂, z = y₁ + y₂} → y = 0) (ω : Fin L → ℝ) :
    Bornology.IsBounded {y₁ | y₁ ∈ Y₁ ∧ ∃ y₂ ∈ Y₂, ∀ l, 0 ≤ (y₁ + y₂ + ω) l} := by
  set Y := {z | ∃ y₁ ∈ Y₁, ∃ y₂ ∈ Y₂, z = y₁ + y₂} with hY
  have h0 : (0 : Fin L → ℝ) ∈ Y := ⟨0, h01, 0, h02, by simp⟩
  -- the aggregate plans are bounded (Exercise 16.AA.2)
  obtain ⟨M, hM⟩ := (exercise_16_AA_2 hc hconv h0 hnfl ω).isBounded.subset_closedBall 0
  rw [Metric.isBounded_iff_subset_closedBall 0]
  by_contra hno
  push Not at hno
  have hex : ∀ n : ℕ, ∃ y₁, (y₁ ∈ Y₁ ∧ ∃ y₂ ∈ Y₂, ∀ l, 0 ≤ (y₁ + y₂ + ω) l) ∧
      (n : ℝ) + 1 < ‖y₁‖ := by
    intro n
    obtain ⟨y, hy, hyb⟩ := Set.not_subset.mp (hno ((n : ℝ) + 1))
    exact ⟨y, hy, by simpa [Metric.mem_closedBall, dist_zero_right] using hyb⟩
  choose y₁ hy₁ hbig using hex
  choose hy₁Y y₂ hy₂Y hnn using hy₁
  set s : ℕ → ℝ := fun n => ‖y₁ n‖ with hs
  have hs1 : ∀ n, 1 ≤ s n := fun n => by
    have := hbig n; have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; simp only [hs]; linarith
  have hspos : ∀ n, 0 < s n := fun n => by linarith [hs1 n]
  have hwS : ∀ n, (s n)⁻¹ • y₁ n ∈ Metric.sphere (0 : Fin L → ℝ) 1 := fun n => by
    rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (hspos n))]
    exact inv_mul_cancel₀ (hspos n).ne'
  obtain ⟨d, hdS, φ, hφ, hlim⟩ := (isCompact_sphere _ _).tendsto_subseq hwS
  have hinv : Tendsto (fun n => (s (φ n))⁻¹) atTop (𝓝 0) := by
    refine tendsto_inv_atTop_zero.comp (tendsto_atTop_mono (fun n => ?_)
      (tendsto_natCast_atTop_atTop (R := ℝ)))
    have h2 : (n : ℝ) ≤ φ n := by exact_mod_cast hφ.id_le n
    have := hbig (φ n)
    simp only [hs]
    linarith
  -- the aggregate `y₁ + y₂` stays bounded, so `y₂ / s → -d`
  have hagg : ∀ n, ‖y₁ n + y₂ n‖ ≤ M + ‖ω‖ := by
    intro n
    have hmem : y₁ n + y₂ n + ω ∈ {z | z - ω ∈ Y ∧ ∀ l, 0 ≤ z l} :=
      ⟨⟨y₁ n, hy₁Y n, y₂ n, hy₂Y n, by abel⟩, hnn n⟩
    have h1 := hM hmem
    rw [Metric.mem_closedBall, dist_zero_right] at h1
    have h2 := norm_sub_le (y₁ n + y₂ n + ω) ω
    rw [add_sub_cancel_right] at h2
    linarith [norm_nonneg ω]
  have haggt : Tendsto (fun n => (s (φ n))⁻¹ • (y₁ (φ n) + y₂ (φ n))) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
      (by simpa using hinv.mul_const (M + ‖ω‖))
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hspos _))]
    exact mul_le_mul_of_nonneg_left (hagg _) (inv_nonneg.mpr (hspos _).le)
  have hy2t : Tendsto (fun n => (s (φ n))⁻¹ • y₂ (φ n)) atTop (𝓝 (-d)) := by
    have := haggt.sub hlim
    rw [zero_sub] at this
    refine this.congr fun n => ?_
    simp [smul_add]
  have hdY : d ∈ Y := mem_of_tendsto_inv_smul hc hconv h0
    (c := fun n => y₁ (φ n)) (fun n => ⟨y₁ (φ n), hy₁Y _, 0, h02, by simp⟩)
    (fun n => hs1 (φ n)) hlim
  have hndY : -d ∈ Y := mem_of_tendsto_inv_smul hc hconv h0
    (c := fun n => y₂ (φ n)) (fun n => ⟨0, h01, y₂ (φ n), hy₂Y _, by simp⟩)
    (fun n => hs1 (φ n)) hy2t
  have := hirr d hdY hndY
  rw [this, mem_sphere_zero_iff_norm, norm_zero] at hdS
  exact zero_ne_one hdS

/-! ## Proposition 16.AA.2 -/

/-- **Proposition 16.AA.2** (MWG, p. 574). If the set `A` of feasible allocations is nonempty
and compact and every `uᵢ` is continuous on `Xᵢ`, the utility possibility set `U` is closed and
bounded above. -/
theorem proposition_16_AA_2 {X : ι → Set (Fin L → ℝ)} {u : ι → (Fin L → ℝ) → ℝ}
    {Y : κ → Set (Fin L → ℝ)} {ω : Fin L → ℝ}
    (hA : IsCompact (PrefEconomy.ofUtility X u Y ω).feasiblePairs)
    (hu : ∀ i, ContinuousOn (u i) (X i)) :
    IsClosed (utilityPossibilitySet (PrefEconomy.ofUtility X u Y ω) u) ∧
      BddAbove (utilityPossibilitySet (PrefEconomy.ofUtility X u Y ω) u) := by
  set A := (PrefEconomy.ofUtility X u Y ω).feasiblePairs with hAdef
  set F : (ι → Fin L → ℝ) × (κ → Fin L → ℝ) → ι → ℝ := fun z i => u i (z.1 i) with hF
  have hFc : ContinuousOn F A := by
    refine continuousOn_pi.mpr fun i => ?_
    refine (hu i).comp ((continuous_apply i).comp continuous_fst).continuousOn fun z hz => ?_
    exact hz.1.1 i
  have hU : utilityPossibilitySet (PrefEconomy.ofUtility X u Y ω) u =
      {v | ∃ z ∈ A, v ≤ F z} := by
    ext v
    constructor
    · rintro ⟨a, ha, hv⟩; exact ⟨(a.x, a.y), ha, hv⟩
    · rintro ⟨z, hz, hv⟩; exact ⟨⟨z.1, z.2⟩, hz, hv⟩
  rw [hU]
  have hK : IsCompact (F '' A) := hA.image_of_continuousOn hFc
  refine ⟨?_, ?_⟩
  · refine IsSeqClosed.isClosed fun v w hv hvw => ?_
    choose z hz hle using hv
    obtain ⟨z', hz', φ, hφ, hlim⟩ := hA.tendsto_subseq hz
    refine ⟨z', hz', fun i => ?_⟩
    have hF' : Tendsto (fun n => F (z (φ n))) atTop (𝓝 (F z')) :=
      ((hFc z' hz').tendsto).comp (tendsto_nhdsWithin_iff.mpr
        ⟨hlim, Eventually.of_forall fun n => hz (φ n)⟩)
    have h1 : Tendsto (fun n => v (φ n) i) atTop (𝓝 (w i)) :=
      ((continuous_apply i).tendsto w).comp (hvw.comp hφ.tendsto_atTop)
    have h2 : Tendsto (fun n => F (z (φ n)) i) atTop (𝓝 (F z' i)) :=
      ((continuous_apply i).tendsto _).comp hF'
    exact le_of_tendsto_of_tendsto' h1 h2 fun n => hle (φ n) i
  · obtain ⟨b, hb⟩ := hK.isBounded.subset_closedBall 0
    refine ⟨fun _ => b, ?_⟩
    rintro v ⟨z, hz, hv⟩ i
    have h1 := hb ⟨z, hz, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right] at h1
    have h2 : |F z i| ≤ ‖F z‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm _ i
    exact (hv i).trans ((le_abs_self _).trans (h2.trans h1))

end MWG.WelfareTheorems
