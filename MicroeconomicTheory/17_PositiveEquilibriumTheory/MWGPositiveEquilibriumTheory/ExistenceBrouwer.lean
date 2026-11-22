/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPositiveEquilibriumTheory.Existence
import MWGGeneralEquilibriumExamples.Nonexistence
import LeanEconomics.FixedPoint.Brouwer

/-!
# Existence: Proposition 17.C.2, the examples of Figure 15.B.10, and the second welfare theorem
(MWG Section 17.C, pp. 587-589)

* **Proposition 17.C.2** (`proposition_17_C_2`): a continuous `z` on the nonzero nonnegative
  price vectors satisfying Walras' law has `z(p*) ≤ 0` at some `p* ∈ Δ`, by Brouwer's theorem
  (LeanEconomics' `brouwer`) applied to `f(p) = (p + z⁺(p))/α(p)` (Figure 17.C.2). The book's
  remark "`z⁺(p)·z(p) = 0` implies `z(p) ≤ 0`" is `le_zero_of_zPlus_dotProduct_eq_zero`.
* **The discussion of Figures 15.B.10(a),(b)** (pp. 587-588), with Chapter 15's economies: in
  Figure 15.B.10(a) property (v) fails, as excess demand stays bounded along every sequence
  `pⁿ → (1, 0)` (`fig_15_B_10a_excessDemand_bounded`, `fig_15_B_10a_not_boundary`), while
  consumer 2 is not strongly monotone; in Figure 15.B.10(b) demand is not single valued
  (`fig_15_B_10b_demand_not_subsingleton`), so `z(·)` is not a function.
* **The second welfare theorem as a corollary of existence** (small type, p. 589): a Pareto
  optimal allocation of a pure exchange economy with standard preferences and `∑ᵢ ωᵢ ≫ 0` is
  supportable as an equilibrium with transfers (`secondWelfare_of_existence`).
-/

namespace MWG.PositiveEquilibriumTheory

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.GeneralEquilibriumExamples
open MWG.WelfareTheorems
open Filter Topology

variable {L : ℕ}

/-! ### Proposition 17.C.2 -/

/-- The nonzero, nonnegative price vectors `ℝ^L₊ \ {0}`, the domain of Proposition 17.C.2. -/
def nonzeroNonneg (L : ℕ) : Set (Fin L → ℝ) := {p | (∀ l, 0 ≤ p l) ∧ p ≠ 0}

/-- `Δ ⊆ ℝ^L₊ \ {0}`. -/
theorem priceSimplex_subset_nonzeroNonneg : priceSimplex L ⊆ nonzeroNonneg L := fun p hp =>
  ⟨hp.1, fun h => (dotProduct_self_pos_of_mem_priceSimplex hp).ne' (by rw [h]; simp)⟩

/-- **Proof of Proposition 17.C.2** (MWG, p. 588). `z⁺(p)`, `z⁺_ℓ(p) = Max {z_ℓ(p), 0}`. -/
noncomputable def zPlus (z : (Fin L → ℝ) → Fin L → ℝ) (p : Fin L → ℝ) : Fin L → ℝ :=
  fun l => max (z p l) 0

/-- **Proof of Proposition 17.C.2** (MWG, p. 588). The fixed-point function
`f(p) = [1/α(p)](p + z⁺(p))`, `α(p) = ∑ₗ [pₗ + z⁺_ℓ(p)]` (Figure 17.C.2). -/
noncomputable def brouwerMap (z : (Fin L → ℝ) → Fin L → ℝ) (p : Fin L → ℝ) : Fin L → ℝ :=
  (∑ l, (p l + zPlus z p l))⁻¹ • (p + zPlus z p)

/-- **Proof of Proposition 17.C.2** (MWG, p. 588). `z⁺(p)·z(p) = 0` implies `z(p) ≤ 0`. -/
theorem le_zero_of_zPlus_dotProduct_eq_zero (v : Fin L → ℝ)
    (h : (fun l => max (v l) 0) ⬝ᵥ v = 0) : ∀ l, v l ≤ 0 := by
  have hterm : ∀ l ∈ Finset.univ, 0 ≤ max (v l) 0 * v l := fun l _ => by
    rcases le_total (v l) 0 with h1 | h1
    · rw [max_eq_right h1, zero_mul]
    · rw [max_eq_left h1]
      exact mul_self_nonneg _
  intro l
  by_contra hl
  push Not at hl
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg hterm).1 h l (Finset.mem_univ l)
  rw [max_eq_left hl.le] at h0
  exact (mul_pos hl hl).ne' h0

/-- **Proof of Proposition 17.C.2** (MWG, p. 588). `α(p) ≥ 1` on `Δ`. -/
theorem one_le_sum_zPlus (z : (Fin L → ℝ) → Fin L → ℝ) {p : Fin L → ℝ}
    (hp : p ∈ priceSimplex L) : 1 ≤ ∑ l, (p l + zPlus z p l) := by
  rw [Finset.sum_add_distrib, hp.2]
  have : 0 ≤ ∑ l, zPlus z p l := Finset.sum_nonneg fun l _ => le_max_right _ _
  linarith

/-- **Proof of Proposition 17.C.2** (MWG, p. 588). `f` maps `Δ` into itself. -/
theorem brouwerMap_mapsTo (z : (Fin L → ℝ) → Fin L → ℝ) :
    Set.MapsTo (brouwerMap z) (priceSimplex L) (priceSimplex L) := by
  intro p hp
  have hα := one_le_sum_zPlus z hp
  have hα0 : 0 < ∑ l, (p l + zPlus z p l) := by linarith
  refine ⟨fun l => ?_, ?_⟩
  · simp only [brouwerMap, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.2 hα0.le) (add_nonneg (hp.1 l) (le_max_right _ _))
  · simp only [brouwerMap, Pi.smul_apply, Pi.add_apply, smul_eq_mul, ← Finset.mul_sum]
    exact inv_mul_cancel₀ hα0.ne'

/-- **Proof of Proposition 17.C.2** (MWG, p. 588). `f` is continuous on `Δ`. -/
theorem brouwerMap_continuousOn {z : (Fin L → ℝ) → Fin L → ℝ}
    (hc : ContinuousOn z (priceSimplex L)) : ContinuousOn (brouwerMap z) (priceSimplex L) := by
  have hzp : ContinuousOn (zPlus z) (priceSimplex L) :=
    continuousOn_pi.2 fun l =>
      ContinuousOn.sup ((continuous_apply l).comp_continuousOn hc) continuousOn_const
  have hα : ContinuousOn (fun p => ∑ l, (p l + zPlus z p l)) (priceSimplex L) :=
    continuousOn_finsetSum _ fun l _ =>
      (continuous_apply l).continuousOn.add ((continuous_apply l).comp_continuousOn hzp)
  have hinv : ContinuousOn (fun p => (∑ l, (p l + zPlus z p l))⁻¹) (priceSimplex L) :=
    hα.inv₀ fun p hp => by linarith [one_le_sum_zPlus z hp]
  exact hinv.smul (continuousOn_id.add hzp)

/-- **Proposition 17.C.2** (MWG, p. 588). Suppose `z(p)`, defined for all nonzero `p ∈ ℝ^L₊`
(`L ≥ 1`), is continuous, homogeneous of degree zero and satisfies Walras' law there. Then
there is a price vector `p*` (in `Δ`) with `z(p*) ≤ 0`. (Homogeneity only justifies restricting
the search to `Δ`; the proof does not use it.) -/
theorem proposition_17_C_2 (hL : 0 < L) {z : (Fin L → ℝ) → Fin L → ℝ}
    (hc : ContinuousOn z (nonzeroNonneg L))
    (_hH : ∀ p ∈ nonzeroNonneg L, ∀ α : ℝ, 0 < α → z (α • p) = z p)
    (hW : ∀ p ∈ nonzeroNonneg L, p ⬝ᵥ z p = 0) :
    ∃ p ∈ priceSimplex L, z p ≤ 0 := by
  have hne : (priceSimplex L).Nonempty := ⟨Pi.single ⟨0, hL⟩ 1, single_mem_priceSimplex _⟩
  obtain ⟨p, hp, hfix⟩ := LeanEconomics.FixedPoint.brouwer (isCompact_priceSimplex L)
    (convex_priceSimplex L) hne
    (brouwerMap_continuousOn (hc.mono priceSimplex_subset_nonzeroNonneg)) (brouwerMap_mapsTo z)
  refine ⟨p, hp, fun l => le_zero_of_zPlus_dotProduct_eq_zero (z p) ?_ l⟩
  have hw := hW p (priceSimplex_subset_nonzeroNonneg hp)
  have hα0 : 0 < ∑ l, (p l + zPlus z p l) := by linarith [one_le_sum_zPlus z hp]
  have h1 : brouwerMap z p ⬝ᵥ z p =
      (∑ l, (p l + zPlus z p l))⁻¹ * (p ⬝ᵥ z p + zPlus z p ⬝ᵥ z p) := by
    simp only [brouwerMap, smul_dotProduct, add_dotProduct, smul_eq_mul]
  rw [hfix, hw, zero_add] at h1
  have h2 := (mul_eq_zero.1 h1.symm).resolve_left (inv_ne_zero hα0.ne')
  exact h2

/-! ### Figures 15.B.10(a) and (b) -/

/-- A consumer's `demandFn` is always affordable (it is demanded, or it is `0`). -/
theorem demandFn_mem_budget {ι : Type*} {E : ExchangeEconomy ι L}
    (hX : ∀ i, E.X i = nonnegOrthant L) (i : ι) {p : Fin L → ℝ} (hw : 0 ≤ p ⬝ᵥ E.ω i) :
    demandFn E i p ∈ budgetSetOn (nonnegOrthant L) p (p ⬝ᵥ E.ω i) := by
  by_cases h : (E.demand i p).Nonempty
  · have hm := (demandFn_mem E h).1
    rw [hX i] at hm
    exact hm
  · unfold demandFn
    simp only [h, ↓reduceDIte]
    exact ⟨fun _ => le_rfl, by simpa using hw⟩

/-- **Section 17.C** (MWG, p. 588), Figure 15.B.10(a). Along every sequence `pⁿ ≫ 0` with
`pⁿ → (1, 0)`, the excess demand of `fig10aEconomy` stays bounded: eventually
`z_ℓ(pⁿ) ≤ 1` for both goods. (Consumer 2 demands only his endowment; consumer 1's wealth
`pⁿ₂` tends to zero.) -/
theorem fig_15_B_10a_excessDemand_bounded {ps : ℕ → Fin 2 → ℝ}
    (hps : ∀ n, ps n ∈ posOrthant 2) (hlim : Tendsto ps atTop (𝓝 ![1, 0])) :
    ∀ᶠ n in atTop, ∀ l, excessDemand fig10aEconomy (ps n) l ≤ 1 := by
  have h0 : ∀ᶠ n in atTop, 1 / 2 < ps n 0 :=
    (((continuous_apply 0).tendsto _).comp hlim).eventually (lt_mem_nhds (by norm_num))
  have h1 : ∀ᶠ n in atTop, ps n 1 < 1 / 2 :=
    (((continuous_apply 1).tendsto _).comp hlim).eventually (gt_mem_nhds (by norm_num))
  filter_upwards [h0, h1] with n hn0 hn1
  have hX : ∀ i, fig10aEconomy.X i = nonnegOrthant 2 := fun _ => rfl
  have hω : ps n ⬝ᵥ fig10aEconomy.ω 0 = ps n 1 := by
    simp [fig10a_ω0, dotProduct, Fin.sum_univ_two]
  have hb := demandFn_mem_budget hX 0 (p := ps n) (by rw [hω]; exact (hps n 1).le)
  rw [hω] at hb
  obtain ⟨hx0, hbud⟩ := hb
  rw [fig10a_dot] at hbud
  have hd1 : demandFn fig10aEconomy 1 (ps n) = ![1, 0] :=
    demandFn_eq _ (fig_15_B_10a_demand1 (hps n))
  have e0 := hx0 0
  have e1 := hx0 1
  have hp0 := hps n 0
  have hp1 := hps n 1
  intro l
  rw [excessDemand_apply, Fin.sum_univ_two, hd1]
  fin_cases l
  · simp [fig10a_ω0, fig10a_ω1]
    nlinarith
  · simp [fig10a_ω0, fig10a_ω1]
    nlinarith

/-- **Section 17.C** (MWG, p. 588), Figure 15.B.10(a). Property (v) of Proposition 17.B.2 fails
for the economy of Figure 15.B.10(a), whose consumer 2 is not strongly monotone
(`fig_15_B_10a_not_stronglyMonotone`, Chapter 15). -/
theorem fig_15_B_10a_not_boundary : ¬ EDBoundary (excessDemand fig10aEconomy) := by
  intro h
  set ps : ℕ → Fin 2 → ℝ := fun n => ![1, 1 / ((n : ℝ) + 1)]
  have hps : ∀ n, ps n ∈ posOrthant 2 := fun n => vec2_mem_posOrthant one_pos (by positivity)
  have hlim : Tendsto ps atTop (𝓝 ![1, 0]) := by
    refine tendsto_pi_nhds.2 fun l => ?_
    fin_cases l
    · simp [ps]
    · simpa [ps] using (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0))
  have hne : (![1, 0] : Fin 2 → ℝ) ≠ 0 := fun h => by simpa using congrFun h 0
  obtain ⟨n, hn1, l, hl⟩ :=
    ((fig_15_B_10a_excessDemand_bounded hps hlim).and (h ps _ hps hlim hne ⟨1, by simp⟩ 1)).exists
  linarith [hn1 l]

/-- **Section 17.C** (MWG, p. 588), Figure 15.B.10(b). The nonconvex consumer 1 of
`fig10bEconomy` (`u₁ = x₁² + x₂²`, `ω₁ = (1, 1)`) demands both `(2, 0)` and `(0, 2)` at
`p = (1, 1)`: his demand, hence `z(·)`, is not single valued (condition (i) fails). -/
theorem fig_15_B_10b_demand_not_subsingleton :
    (![2, 0] : Fin 2 → ℝ) ∈ fig10bEconomy.demand 0 ![1, 1] ∧
      (![0, 2] : Fin 2 → ℝ) ∈ fig10bEconomy.demand 0 ![1, 1] ∧
      ¬ (fig10bEconomy.demand 0 ![1, 1]).Subsingleton := by
  have hbud : ∀ y ∈ budgetSetOn (fig10bEconomy.X 0) ![1, 1] (![1, 1] ⬝ᵥ fig10bEconomy.ω 0),
      fig10bEconomy.u 0 y ≤ 4 := by
    rintro y ⟨hy, hb⟩
    have hy0 := hy 0
    have hy1 := hy 1
    simp [fig10bEconomy, ExchangeEconomy.ofOrthant, dotProduct, Fin.sum_univ_two] at hb
    simp only [fig10bEconomy, ExchangeEconomy.ofOrthant, Matrix.cons_val_zero,
      MWG.GeneralEquilibriumExamples.sqUtility]
    nlinarith
  have hmem : ∀ x : Fin 2 → ℝ, x ∈ nonnegOrthant 2 → x 0 + x 1 = 2 →
      MWG.GeneralEquilibriumExamples.sqUtility x = 4 → x ∈ fig10bEconomy.demand 0 ![1, 1] := by
    intro x hx hs hu
    refine ⟨⟨hx, ?_⟩, fun y hy => ?_⟩
    · simp [fig10bEconomy, ExchangeEconomy.ofOrthant, dotProduct, Fin.sum_univ_two]
      linarith
    · have := hbud y hy
      simp only [fig10bEconomy, ExchangeEconomy.ofOrthant, Matrix.cons_val_zero] at this ⊢
      linarith
  have h1 : (![2, 0] : Fin 2 → ℝ) ∈ fig10bEconomy.demand 0 ![1, 1] :=
    hmem _ (fun l => by fin_cases l <;> simp) (by simp)
      (by simp [MWG.GeneralEquilibriumExamples.sqUtility]; norm_num)
  have h2 : (![0, 2] : Fin 2 → ℝ) ∈ fig10bEconomy.demand 0 ![1, 1] :=
    hmem _ (fun l => by fin_cases l <;> simp) (by simp)
      (by simp [MWG.GeneralEquilibriumExamples.sqUtility]; norm_num)
  refine ⟨h1, h2, fun hs => ?_⟩
  have := congrFun (hs h1 h2) 0
  simp at this

/-! ### The second welfare theorem as a corollary of existence (small type, p. 589) -/

/-- **Section 17.C, small type** (MWG, p. 589). The second welfare theorem as a particular case
of the existence result: in a pure exchange economy (`Xᵢ = ℝ^L₊`, `L ≥ 1`) with continuous,
strictly convex, strongly monotone preferences and `∑ᵢ ωᵢ ≫ 0`, every Pareto optimal
allocation `x` is supported as a price equilibrium with transfers `Tᵢ = p·xᵢ - p·ωᵢ`. Proof:
an equilibrium `(p, x̂)` of the economy with endowments `xᵢ` exists (Proposition 17.C.1);
`x̂ᵢ ≿ᵢ xᵢ` since `xᵢ` is affordable, so by Pareto optimality `x̂ᵢ ∼ᵢ xᵢ`, and `xᵢ` is then
also optimal at `(p, p·xᵢ)`. -/
theorem secondWelfare_of_existence {ι : Type*} [Fintype ι] {E : ExchangeEconomy ι L}
    (hL : 0 < L) (hX : ∀ i, E.X i = nonnegOrthant L) (hu : ∀ i, StandardUtility (E.u i))
    (hpos : ∀ l, 0 < E.totalEndowment l) {x : ι → Fin L → ℝ} (hPO : E.IsParetoOptimal x) :
    ∃ p, p ∈ posOrthant L ∧ E.IsEqmWithTransfers p (fun i => p ⬝ᵥ x i - p ⬝ᵥ E.ω i) x := by
  have hι : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := hpos ⟨0, hL⟩
    simp [ExchangeEconomy.totalEndowment] at this
  set E' : ExchangeEconomy ι L := { X := E.X, u := E.u, ω := x } with hE'
  have hxX : ∀ i, x i ∈ nonnegOrthant L := fun i => hX i ▸ hPO.1.1 i
  have htot : E'.totalEndowment = E.totalEndowment := hPO.1.2
  obtain ⟨p, a, ha⟩ := proposition_17_C_1_economy (E := E') hL hX hu hxX (fun l => htot ▸ hpos l)
  have hp := eqm_price_pos (E := E') hX (fun i => (hu i).2.2) ha
  obtain ⟨⟨hy, hpy, -⟩, hxd, hc⟩ := (conditions_i'_iii' E' a p).1 ha
  have hy0 : a.y () = 0 := by
    have h := eq_zero_of_dotProduct_nonpos hp (x := -a.y ()) (fun l => by simpa using hy l)
      (by rw [dotProduct_neg, hpy, neg_zero])
    simpa using h
  rw [hy0, sub_eq_zero] at hc
  have hbox : E.InBox a.x := ⟨fun i => (hxd i).1.1, by rw [hc]; exact hPO.1.2⟩
  have hge : ∀ i, E.u i (x i) ≤ E.u i (a.x i) := fun i =>
    (hxd i).2 (x i) ⟨hX i ▸ hxX i, le_rfl⟩
  have heq : ∀ i, E.u i (a.x i) = E.u i (x i) := by
    by_contra h
    push Not at h
    obtain ⟨i, hi⟩ := h
    exact hPO.2 ⟨a.x, hbox, hge, i, lt_of_le_of_ne (hge i) (Ne.symm hi)⟩
  refine ⟨p, hp, hPO.1, ?_, fun i y hy hpy => ?_⟩
  · rw [Finset.sum_sub_distrib, ← dotProduct_sum, ← dotProduct_sum, hPO.1.2]
    simp [ExchangeEconomy.totalEndowment]
  · rw [← heq i]
    exact (hxd i).2 y ⟨hy, by linarith⟩

end MWG.PositiveEquilibriumTheory
