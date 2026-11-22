/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGWelfareTheorems.CheaperPoint

/-!
# A quasiequilibrium that is not an equilibrium (MWG Figure 16.D.2, p. 554)

The Edgeworth box of Figure 15.B.10(a), reproduced in Figure 16.D.2, made concrete: `ω̄ = (1, 1)`,
consumer 1 has `u₁(x) = √x₁ + x₂` (an infinite marginal rate of substitution on the axis
`x₁ = 0`), consumer 2 has `u₂(x) = x₁`, and there is one disposal firm.

* `x* = ((0, 1), (1, 0))` is Pareto optimal, and with `p = (1, 0)` and wealth levels
  `w = (0, 1)` it is a price quasiequilibrium with transfers (`figure_16_D_2_quasi`).
* Normalizing `p₁ = 1`, `p = (1, 0)` is the only supporting price vector, and consumer 1's wealth
  is `0` (`figure_16_D_2_unique_price`).
* `x*₁` satisfies condition (ii) of Definition 16.D.1 but is not maximal in consumer 1's budget
  set `{x : x₁ = 0}`; in fact `x*` is not a price equilibrium with transfers for any prices and
  wealth levels (`figure_16_D_2_not_eqm`). There is no cheaper consumption for `(p, w₁) = (p, 0)`,
  as Proposition 16.D.2 requires.
-/

namespace MWG.WelfareTheorems

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.Production Kreps.PreferenceProperties
open MWG.CompetitiveMarkets (Allocation)

variable {L : ℕ}

/-- The Euclidean distance moved by adding `c` units of one good is `|c|`. -/
theorem euclidDist_add_single (x : Fin L → ℝ) (l : Fin L) (c : ℝ) :
    euclidDist (x + Pi.single l c) x = |c| := by
  unfold euclidDist
  have : ∀ k, ((x + (Pi.single l c : Fin L → ℝ)) k - x k) ^ 2 =
      (Pi.single l c : Fin L → ℝ) k ^ 2 := fun k => by
    simp only [Pi.add_apply, add_sub_cancel_left]
  simp only [this]
  rw [Finset.sum_eq_single l (fun k _ hk => by simp [hk]) (by simp), Pi.single_eq_same,
    Real.sqrt_sq_eq_abs]

/-- A utility on `ℝ^L₊` that strictly increases in good `l` everywhere is locally nonsatiated. -/
theorem lns_of_strictMono_coord {u : (Fin L → ℝ) → ℝ} (l : Fin L)
    (h : ∀ x ∈ nonnegOrthant L, ∀ c : ℝ, 0 < c → u x < u (x + Pi.single l c)) :
    LocallyNonsatiated (nonnegOrthant L) (utilityPref u) := by
  intro x hx ε hε
  refine ⟨x + Pi.single l ε, fun k => ?_, ?_, ?_, ?_⟩
  · have := hx k
    by_cases hk : k = l
    · subst hk; simp; linarith
    · simp [hk]; linarith
  · rw [euclidDist_add_single, abs_of_pos hε]
  · exact (h x hx ε hε).le
  · exact not_le.mpr (h x hx ε hε)

/-- Consumer 1 of Figure 16.D.2: `u₁(x) = √x₁ + x₂`. -/
noncomputable def fig16D2u1 (x : Fin 2 → ℝ) : ℝ := Real.sqrt (x 0) + x 1

/-- Consumer 2 of Figure 16.D.2: `u₂(x) = x₁`. -/
def fig16D2u2 (x : Fin 2 → ℝ) : ℝ := x 0

/-- **Figure 16.D.2** (MWG, p. 555). The Edgeworth box economy with `ω̄ = (1, 1)`. -/
noncomputable def fig16D2Economy : PrefEconomy (Fin 2) Unit 2 :=
  PrefEconomy.ofUtility (fun _ => nonnegOrthant 2) ![fig16D2u1, fig16D2u2]
    (fun _ => nonposOrthant 2) ![1, 1]

/-- The allocation `x*` of Figure 16.D.2: `x*₁ = (0, 1)`, `x*₂ = (1, 0)`, no production. -/
def fig16D2Alloc : Allocation (Fin 2) Unit 2 := ⟨![![0, 1], ![1, 0]], fun _ => 0⟩

/-- Both consumers of Figure 16.D.2 are locally nonsatiated on `ℝ²₊`. -/
theorem fig16D2_lns : ∀ i, LocallyNonsatiated (fig16D2Economy.X i) (fig16D2Economy.pref i) := by
  intro i
  fin_cases i
  · refine lns_of_strictMono_coord 1 fun x _ c hc => ?_
    simp [fig16D2u1]
    linarith
  · refine lns_of_strictMono_coord 0 fun x _ c hc => ?_
    simp [fig16D2u2]
    linarith

/-- **Figure 16.D.2** (MWG, pp. 554-555). `x*` is Pareto optimal, and with `p = (1, 0)` and
`w = (0, 1)` it is a price quasiequilibrium with transfers but not a price equilibrium with
transfers: `(0, 2)` is affordable for consumer 1 and better than `x*₁`. -/
theorem figure_16_D_2_quasi :
    fig16D2Economy.IsParetoOptimal fig16D2Alloc ∧
      fig16D2Economy.IsPriceQuasiEqmWithTransfers fig16D2Alloc ![1, 0] ![0, 1] ∧
      ¬ fig16D2Economy.IsPriceEqmWithTransfers fig16D2Alloc ![1, 0] ![0, 1] := by
  have hdot : ∀ x : Fin 2 → ℝ, (![1, 0] : Fin 2 → ℝ) ⬝ᵥ x = x 0 := fun x => by
    rw [dot_two]; simp
  have hfeas : fig16D2Economy.IsFeasible fig16D2Alloc := by
    refine ⟨⟨fun i => ?_, fun _ => fun _ => le_rfl⟩, ?_⟩
    · fin_cases i <;> intro l <;> fin_cases l <;> simp [fig16D2Alloc]
    · funext l
      fin_cases l <;> simp [fig16D2Economy, PrefEconomy.ofUtility, fig16D2Alloc]
  refine ⟨⟨hfeas, ?_⟩, ⟨?_, ?_, fun _ => ?_, fun i => ⟨hfeas.1.1 i, fun x hx hs => ?_⟩,
    hfeas.2⟩, fun h => ?_⟩
  · rintro ⟨a', ⟨⟨hx', hy'⟩, hc'⟩, hle, k, hk⟩
    have hx0 : ∀ i l, 0 ≤ a'.x i l := fun i => hx' i
    have hy0 : ∀ l, a'.y () l ≤ 0 := hy' ()
    have hc0 := congrFun hc' 0
    have hc1 := congrFun hc' 1
    simp [fig16D2Economy, PrefEconomy.ofUtility, Fin.sum_univ_two] at hc0 hc1
    have h2 : 1 ≤ a'.x 1 0 := by
      have := hle 1
      simpa [fig16D2Economy, PrefEconomy.ofUtility, utilityPref, fig16D2u2, fig16D2Alloc]
        using this
    have hy00 := hy0 0
    have hy01 := hy0 1
    have h10 : a'.x 0 0 = 0 := by linarith [hx0 0 0, hx0 1 1]
    apply hk.2
    fin_cases k
    · simp only [fig16D2Economy, PrefEconomy.ofUtility, utilityPref, fig16D2Alloc]
      simp [fig16D2u1, h10]
      linarith [hx0 1 1]
    · simp only [fig16D2Economy, PrefEconomy.ofUtility, utilityPref, fig16D2Alloc]
      simp [fig16D2u2]
      linarith [hx0 0 0]
  · intro h
    have := congrFun h 0
    simp at this
  · simp [fig16D2Economy, PrefEconomy.ofUtility, Fin.sum_univ_two, hdot, fig16D2Alloc]
  · exact zero_mem_supply_nonpos (fun l => by fin_cases l <;> simp)
  · rw [hdot]
    have hxn : ∀ l, 0 ≤ x l := hx
    fin_cases i
    · simpa using hxn 0
    · have := hs.2
      simp only [fig16D2Economy, PrefEconomy.ofUtility, utilityPref, fig16D2Alloc] at this
      simp [fig16D2u2] at this
      simp
      linarith
  · have hb : (![0, 2] : Fin 2 → ℝ) ∈ budgetSetOn (fig16D2Economy.X 0) ![1, 0] (![0, 1] 0) :=
      ⟨fun l => by fin_cases l <;> simp, by rw [hdot]; simp⟩
    have := (h.2.2.1 0).2 _ hb
    simp only [fig16D2Economy, PrefEconomy.ofUtility, utilityPref, fig16D2Alloc] at this
    simp [fig16D2u1] at this

/-- **Figure 16.D.2** (MWG, p. 554). Every price quasiequilibrium with transfers supporting `x*`
has `p₂ = 0` (so `p = (1, 0)` after normalizing `p₁ = 1`) and gives consumer 1 wealth `w₁ = 0`. -/
theorem figure_16_D_2_unique_price {p : Fin 2 → ℝ} {w : Fin 2 → ℝ}
    (h : fig16D2Economy.IsPriceQuasiEqmWithTransfers fig16D2Alloc p w) :
    p 1 = 0 ∧ w 0 = 0 ∧ 0 < p 0 := by
  have hp : ∀ l, 0 ≤ p l := footnote_9 (h.2.2.1 ())
  have hw := h.wealth_eq fig16D2_lns
  have hw0 : w 0 = p 1 := by
    rw [← hw 0, dot_two]; simp [fig16D2Alloc]
  have hp1 : p 1 = 0 := by
    by_contra hne
    have hpos : 0 < p 1 := lt_of_le_of_ne (hp 1) (Ne.symm hne)
    set t := min 1 (p 1 / (4 * (p 0 + 1))) with ht
    have hp0 := hp 0
    have ht0 : 0 < t := lt_min one_pos (div_pos hpos (by linarith))
    have ht1 : t ≤ 1 := min_le_left _ _
    have htle : t ≤ p 1 / (4 * (p 0 + 1)) := min_le_right _ _
    have hmem : (![t ^ 2, 1 - t / 2] : Fin 2 → ℝ) ∈ fig16D2Economy.X 0 := fun l => by
      fin_cases l
      · change 0 ≤ t ^ 2; positivity
      · change 0 ≤ 1 - t / 2; linarith
    have hs : Strict (fig16D2Economy.pref 0) ![t ^ 2, 1 - t / 2] (fig16D2Alloc.x 0) := by
      simp only [fig16D2Economy, PrefEconomy.ofUtility, utilityPref, fig16D2Alloc, Strict]
      simp only [Matrix.cons_val_zero, fig16D2u1, Matrix.cons_val_one, Real.sqrt_zero]
      rw [Real.sqrt_sq ht0.le]
      constructor <;> linarith
    have := (h.2.2.2.1 0).2 _ hmem hs
    rw [hw0, dot_two] at this
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
    -- `p₂ t / 2 ≤ p₁ t²`, so `p₂ ≤ 2 p₁ t < p₂`
    have h1 : p 1 * t / 2 ≤ p 0 * t ^ 2 := by nlinarith
    have h2 : p 1 / 2 ≤ p 0 * t := by
      by_contra hlt
      push Not at hlt
      nlinarith [mul_lt_mul_of_pos_right hlt ht0]
    have h3 : p 0 * t ≤ p 0 * (p 1 / (4 * (p 0 + 1))) := mul_le_mul_of_nonneg_left htle hp0
    have h4 : p 0 * (p 1 / (4 * (p 0 + 1))) < p 1 / 2 := by
      rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  refine ⟨hp1, by rw [hw0, hp1], ?_⟩
  rcases (hp 0).lt_or_eq with h0 | h0
  · exact h0
  · exfalso
    apply h.1
    funext l
    fin_cases l
    · simp [← h0]
    · simp [hp1]

/-- **Figure 16.D.2** (MWG, p. 554). `x*` is not a price equilibrium with transfers for any price
vector and wealth levels. -/
theorem figure_16_D_2_not_eqm (p w : Fin 2 → ℝ) :
    ¬ fig16D2Economy.IsPriceEqmWithTransfers fig16D2Alloc p w := by
  intro h
  have hq := h.isPriceQuasiEqm_of_lns fig16D2_lns
  obtain ⟨hp1, hw0, -⟩ := figure_16_D_2_unique_price hq
  have hb : (![0, 2] : Fin 2 → ℝ) ∈ budgetSetOn (fig16D2Economy.X 0) p (w 0) :=
    ⟨fun l => by fin_cases l <;> simp, by rw [dot_two, hw0, hp1]; simp⟩
  have := (h.2.2.1 0).2 _ hb
  simp only [fig16D2Economy, PrefEconomy.ofUtility, utilityPref, fig16D2Alloc] at this
  simp [fig16D2u1] at this

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **Section 16.D** (MWG, p. 556). In a pure exchange economy with `ω̄ ≫ 0`, `Xᵢ = ℝ^L₊` and
continuous, strongly monotone (rational) preferences (`I ≥ 1`), every price quasiequilibrium with
transfers has `p ≫ 0` and is a price equilibrium with transfers: Exercise 16.D.3 with the
inaction plans `ŷⱼ = 0`. -/
theorem pureExchange_quasiEqm_isPriceEqm_of_strongMono [Nonempty ι] {E : PrefEconomy ι κ L}
    (hpe : E.IsPureExchange) (hX : ∀ i, E.X i = nonnegOrthant L)
    (hr : ∀ i, RationalOn (E.X i) (E.pref i)) (hc : ∀ i, PrefContinuous (E.X i) (E.pref i))
    (hmono : ∀ i, PrefStronglyMonotone (nonnegOrthant L) (E.pref i)) (hω : ∀ l, 0 < E.ω l)
    {a : Allocation ι κ L} {p : Fin L → ℝ} {w : ι → ℝ}
    (h : E.IsPriceQuasiEqmWithTransfers a p w) :
    E.IsPriceEqmWithTransfers a p w ∧ StrictlyPositive p :=
  exercise_16_D_3 hX hr hc hmono (yh := fun _ => 0) (fun j => by rw [hpe j]; exact fun _ => le_rfl)
    (fun l => by simpa using hω l) h

end MWG.WelfareTheorems
