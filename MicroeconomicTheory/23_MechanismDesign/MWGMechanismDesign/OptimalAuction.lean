/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGMechanismDesign.RevenueEquivalence

/-!
# Optimal auctions

MWG, Section 23.F, Example 23.F.2 (pp. 903-905), and Exercises 23.F.3, 23.F.4 (p. 923).

`I` buyers with linear utilities `θᵢyᵢ + tᵢ`, independent types with densities `φᵢ > 0` on
`[θ̲ᵢ, θ̄ᵢ]` (`TypeDensity`), virtual valuations `Jᵢ(θᵢ) = θᵢ - (1 - Φᵢ(θᵢ))/φᵢ(θᵢ)`. A social
choice function is `(y, t)`; the seller's expected revenue is `∑ᵢ E[-tᵢ(θ)]` (no waste,
footnote 51).

* `OptAuctionFeasible`: `y(θ)` a feasible allocation on `Θ` (constraint (ii)), Bayesian incentive
  compatible, interim individually rational, with the expectations existing.
* **Example 23.F.2** (`example_23_F_2`): if `(y*, t*)` is feasible in this sense, has
  `Uᵢ(θ̲ᵢ) = 0`, and `y*(θ)` maximises `∑ᵢ yᵢJᵢ(θᵢ)` over feasible allocations at every `θ ∈ Θ`
  (the relaxed problem (23.F.8)), it maximises expected revenue among all feasible `(y, t)`. The
  proof is (23.F.7)-(23.F.8) via (23.D.16) (`eq_23_D_16`), and (iv) ⇔ (iv') (`eq_23_F_iv_iff`).
* (23.F.9): a pointwise maximiser gives the good to `i` when `Jᵢ > max{0, max_{k≠i} Jₖ}` and not
  when `Jᵢ < max{0, max_{k≠i} Jₖ}` (`eq_23_F_9`); conversely without ties these conditions give a
  maximiser (`eq_23_F_9_converse`).
* Remark (1): with asymmetric bidders (uniform on `[0, 1]` and `[0, 2]`) the optimal auction can
  give the good to a bidder without the highest valuation (`example_23_F_2_remark1`).
* Remark (2): symmetric bidders with `J` nondecreasing and `J(θ̲) > 0`: giving the good to a
  highest-valuation bidder solves (23.F.8) (`example_23_F_2_remark2_pointwise`), so any feasible
  mechanism doing this with `U(θ̲) = 0` (first-price, second-price) is optimal
  (`example_23_F_2_remark2`).
* Remark (3): `I = 1`: the posted price `p*` with `J(p*) = 0` solves (23.F.8)
  (`example_23_F_2_remark3_pointwise`); the FOC of `p(1 - Φ(p))` is `1 - Φ(p) - pφ(p) = 0`
  (`example_23_F_2_remark3_foc`, at a continuity point of `φ`) and is equivalent to `J(p) = 0`.
  Instance: uniform on `[0, 1]`, posted price `1/2` is an optimal mechanism
  (`example_23_F_2_instance`).
* Exercise 23.F.3: with symmetric bidders a second-price auction with reserve `r`, `J(r) = 0`,
  solves (23.F.8) (`exercise_23_F_3`). Exercise 23.F.4: with seller valuation `θ₀`, the seller's
  expected payoff is `∑ᵢ E[yᵢ(Jᵢ - θ₀)] + θ₀ - ∑ᵢ Uᵢ(θ̲ᵢ)` and a pointwise maximiser of
  `∑ᵢ yᵢ(Jᵢ - θ₀)` is optimal; it gives the good to `i` iff `Jᵢ > max{θ₀, max_{k≠i} Jₖ}`
  (`exercise_23_F_4`, `exercise_23_F_4_rule`).

Departures: feasibility is required on `Θ` and the competing social choice functions are those
whose expectations exist (integrability is part of `OptAuctionFeasible`); MWG's ties
(`Jᵢ = max{…}`, probability zero) are left free, and optimality is stated for any pointwise
maximiser.
-/

namespace MWG.MechanismDesign

open MeasureTheory Function

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Example 23.F.2** (MWG, p. 904), constraint (ii): a feasible allocation `yᵢ ≥ 0`,
`∑ᵢ yᵢ ≤ 1` (so `yᵢ ∈ [0, 1]`; the seller keeps `y₀ = 1 - ∑ᵢ yᵢ`). -/
def FeasAlloc (w : ι → ℝ) : Prop := (∀ i, 0 ≤ w i) ∧ ∑ i, w i ≤ 1

/-- The allocation `w` maximises `∑ᵢ wᵢJᵢ` over feasible allocations: it solves the relaxed
problem (23.F.8) at one profile, with `Jv i = Jᵢ(θᵢ)`. -/
def PointwiseOptAlloc (Jv w : ι → ℝ) : Prop :=
  FeasAlloc w ∧ ∀ w', FeasAlloc w' → ∑ i, w' i * Jv i ≤ ∑ i, w i * Jv i

/-- The seller's expected revenue `∑ᵢ E[-tᵢ(θ)]` (MWG, p. 904). -/
noncomputable def auctionRevenue (D : ι → TypeDensity) (t : (ι → ℝ) → ι → ℝ) : ℝ :=
  ∑ i, ∫ θ, -t θ i ∂Measure.pi (fun j => (D j).measure)

/-- **Example 23.F.2** (MWG, p. 904). The social choice functions the seller may choose:
`y(θ)` is a feasible allocation for `θ ∈ Θ` (ii); `(y, t)` is Bayesian incentive compatible;
interim individually rational `Uᵢ(θᵢ) ≥ 0` (iv); and the expectations involved exist. -/
def OptAuctionFeasible (D : ι → TypeDensity) (y t : (ι → ℝ) → ι → ℝ) : Prop :=
  (∀ θ, (∀ i, θ i ∈ Set.Icc (D i).lo (D i).hi) → FeasAlloc (y θ)) ∧
    InterimIntegrable (Measure.pi fun j => (D j).measure) allocV y t
      (fun i => (D i).lo) (fun i => (D i).hi) ∧
    BayesianICOn (Measure.pi fun j => (D j).measure) allocV y t
      (fun i => (D i).lo) (fun i => (D i).hi) ∧
    (∀ i, Integrable (fun θ => t θ i) (Measure.pi fun j => (D j).measure)) ∧
    (∀ i, Integrable (fun θ => y θ i * (D i).virtualValue (θ i))
      (Measure.pi fun j => (D j).measure)) ∧
    ∀ i, ∀ x ∈ Set.Icc (D i).lo (D i).hi,
      0 ≤ interimU (Measure.pi fun j => (D j).measure) allocV y t i x

/-- **Example 23.F.2** (MWG, p. 904), (iv) ⇔ (iv'): for a Bayesian incentive compatible `(y, t)`,
`Uᵢ(θᵢ) ≥ 0` for all `θᵢ ∈ Θᵢ` iff `Uᵢ(θ̲ᵢ) ≥ 0` (since `Uᵢ(θᵢ) = Uᵢ(θ̲ᵢ) + ∫_{θ̲ᵢ}^{θᵢ} ȳᵢ` and
`ȳᵢ ≥ 0`). -/
theorem eq_23_F_iv_iff (D : ι → TypeDensity) {y t : (ι → ℝ) → ι → ℝ}
    (hint : InterimIntegrable (Measure.pi fun j => (D j).measure) allocV y t
      (fun i => (D i).lo) fun i => (D i).hi)
    (hf : BayesianICOn (Measure.pi fun j => (D j).measure) allocV y t
      (fun i => (D i).lo) fun i => (D i).hi)
    (hy0 : ∀ θ i, 0 ≤ y θ i) (i : ι) :
    (∀ x ∈ Set.Icc (D i).lo (D i).hi,
        0 ≤ interimU (Measure.pi fun j => (D j).measure) allocV y t i x) ↔
      0 ≤ interimU (Measure.pi fun j => (D j).measure) allocV y t i (D i).lo := by
  refine ⟨fun h => h _ ⟨le_rfl, (D i).lo_lt_hi.le⟩, fun h x hx => ?_⟩
  rw [((proposition_23_D_2 hint).1 hf i).2 x hx]
  have : 0 ≤ ∫ s in (D i).lo..x, interimBenefit (Measure.pi fun j => (D j).measure) allocV y i s :=
    intervalIntegral.integral_nonneg hx.1 fun s _ => integral_nonneg fun θ => hy0 _ _
  linarith

/-- **Example 23.F.2** (MWG, pp. 904-905). If `(y*, t*)` is feasible, leaves the lowest type of
every buyer with `Uᵢ(θ̲ᵢ) = 0`, and `y*(θ)` solves the relaxed problem (23.F.8) pointwise on `Θ`,
then `(y*, t*)` maximises the seller's expected revenue among all feasible social choice
functions. -/
theorem example_23_F_2 (D : ι → TypeDensity) {ys ts : (ι → ℝ) → ι → ℝ}
    (hs : OptAuctionFeasible D ys ts)
    (hU0 : ∀ i, interimU (Measure.pi fun j => (D j).measure) allocV ys ts i (D i).lo = 0)
    (hopt : ∀ θ, (∀ i, θ i ∈ Set.Icc (D i).lo (D i).hi) →
      PointwiseOptAlloc (fun i => (D i).virtualValue (θ i)) (ys θ))
    {y t : (ι → ℝ) → ι → ℝ} (h : OptAuctionFeasible D y t) :
    auctionRevenue D t ≤ auctionRevenue D ts := by
  have : ∀ j, IsProbabilityMeasure (D j).measure := fun j => (D j).isProbabilityMeasure
  obtain ⟨hyF, hint, hbic, ht, hyJ, hIR⟩ := h
  obtain ⟨-, hint', hbic', ht', hyJ', -⟩ := hs
  rw [auctionRevenue, auctionRevenue, eq_23_D_16 D hint hbic ht hyJ,
    eq_23_D_16 D hint' hbic' ht' hyJ']
  simp only [hU0, Finset.sum_const_zero, sub_zero]
  have hU : 0 ≤ ∑ i, interimU (Measure.pi fun j => (D j).measure) allocV y t i (D i).lo :=
    Finset.sum_nonneg fun i _ => hIR i _ ⟨le_rfl, (D i).lo_lt_hi.le⟩
  have hle : ∑ i, ∫ θ, y θ i * (D i).virtualValue (θ i) ∂Measure.pi (fun j => (D j).measure) ≤
      ∑ i, ∫ θ, ys θ i * (D i).virtualValue (θ i) ∂Measure.pi (fun j => (D j).measure) := by
    rw [← integral_finsetSum _ fun i _ => hyJ i, ← integral_finsetSum _ fun i _ => hyJ' i]
    refine integral_mono_ae (integrable_finsetSum _ fun i _ => hyJ i)
      (integrable_finsetSum _ fun i _ => hyJ' i) ?_
    filter_upwards [re_ae_mem (fun j => (D j).measure) fun j => (D j).measure_compl_Icc]
      with θ hθ
    have h1 := (hopt θ hθ).2 (y θ) (hyF θ hθ)
    simpa using h1
  linarith

/-! ### (23.F.9) -/

/-- `∑ₖ fₖ = fᵢ + ∑_{k ≠ i} fₖ`. -/
theorem oa_sum_split (f : ι → ℝ) (i : ι) :
    ∑ k, f k = f i + ∑ k ∈ Finset.univ.erase i, f k :=
  (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm

omit [DecidableEq ι] in
/-- **(23.F.9)** (MWG, p. 905). A solution of the relaxed problem (23.F.8) at a profile has
`yᵢ = 1` if `Jᵢ > max{0, max_{k≠i} Jₖ}` and `yᵢ = 0` if `Jᵢ < max{0, max_{k≠i} Jₖ}`. -/
theorem eq_23_F_9 {Jv w : ι → ℝ} (h : PointwiseOptAlloc Jv w) (i : ι) :
    ((0 < Jv i ∧ ∀ k ≠ i, Jv k < Jv i) → w i = 1) ∧
      ((Jv i < 0 ∨ ∃ k ≠ i, Jv i < Jv k) → w i = 0) := by
  classical
  obtain ⟨⟨hw0, hw1⟩, hmax⟩ := h
  have hsw := oa_sum_split w i
  have hswJ := oa_sum_split (fun k => w k * Jv k) i
  refine ⟨fun ⟨hJ, hk⟩ => ?_, fun hcase => ?_⟩
  · by_contra hne
    set A := ∑ k ∈ Finset.univ.erase i, w k * Jv k
    set Wn := ∑ k ∈ Finset.univ.erase i, w k
    have hA : A ≤ Wn * Jv i := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun k hk' =>
        mul_le_mul_of_nonneg_left (hk k (Finset.ne_of_mem_erase hk')).le (hw0 k)
    have hWn : 0 ≤ Wn := Finset.sum_nonneg fun k _ => hw0 k
    have hstrict : A + w i * Jv i < Jv i := by
      rcases lt_or_eq_of_le (show w i + Wn ≤ 1 by linarith) with hlt | heq
      · nlinarith
      · have hWpos : 0 < Wn := by
          rcases lt_or_eq_of_le hWn with h' | h'
          · exact h'
          · exact absurd (by linarith : w i = 1) hne
        obtain ⟨k, hkm, hkpos⟩ : ∃ k ∈ Finset.univ.erase i, 0 < w k := by
          by_contra hn
          push Not at hn
          have : Wn ≤ 0 := Finset.sum_nonpos hn
          linarith
        have hA' : A < Wn * Jv i := by
          rw [Finset.sum_mul]
          exact Finset.sum_lt_sum (fun k hk' =>
            mul_le_mul_of_nonneg_left (hk k (Finset.ne_of_mem_erase hk')).le (hw0 k))
            ⟨k, hkm, mul_lt_mul_of_pos_left (hk k (Finset.ne_of_mem_erase hkm)) hkpos⟩
        nlinarith
    have hw' : FeasAlloc (fun k => if k = i then (1 : ℝ) else 0) :=
      ⟨fun k => by dsimp only; split_ifs <;> norm_num, by simp⟩
    have := hmax _ hw'
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true] at this
    linarith
  · by_contra hne
    have hpos : 0 < w i := lt_of_le_of_ne (hw0 i) (Ne.symm hne)
    rcases hcase with hJ | ⟨k, hki, hk⟩
    · have hw' : FeasAlloc (fun l => w l - if l = i then w i else 0) := by
        refine ⟨fun l => ?_, ?_⟩
        · by_cases hl : l = i
          · subst hl; simp
          · simp [hl, hw0 l]
        · rw [Finset.sum_sub_distrib]
          simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
          linarith
      have := hmax _ hw'
      simp only [sub_mul, ite_mul, zero_mul, Finset.sum_sub_distrib, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true] at this
      nlinarith
    · have hw' : FeasAlloc
          (fun l => w l + (if l = k then w i else 0) - if l = i then w i else 0) := by
        refine ⟨fun l => ?_, ?_⟩
        · by_cases hl : l = i
          · subst hl; simp [hki.symm]
          · by_cases hlk : l = k
            · subst hlk; simp [hl]; linarith [hw0 l]
            · simp [hl, hlk, hw0 l]
        · rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
          simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
          linarith
      have := hmax _ hw'
      simp only [sub_mul, add_mul, ite_mul, zero_mul, Finset.sum_sub_distrib,
        Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at this
      nlinarith

omit [DecidableEq ι] in
/-- **(23.F.9)** (MWG, p. 905), converse. If there is no tie (`Jᵢ = max{0, max_{k≠i} Jₖ}` has
probability zero), any feasible allocation satisfying the two conditions of (23.F.9) solves the
relaxed problem (23.F.8). -/
theorem eq_23_F_9_converse {Jv w : ι → ℝ} (hw : FeasAlloc w)
    (h9 : ∀ i, ((0 < Jv i ∧ ∀ k ≠ i, Jv k < Jv i) → w i = 1) ∧
      ((Jv i < 0 ∨ ∃ k ≠ i, Jv i < Jv k) → w i = 0))
    (hnt : (∃ i, 0 < Jv i ∧ ∀ k ≠ i, Jv k < Jv i) ∨ ∀ i, Jv i < 0) :
    PointwiseOptAlloc Jv w := by
  classical
  refine ⟨hw, fun w' ⟨hw0', hw1'⟩ => ?_⟩
  rcases hnt with ⟨i, hJ, hk⟩ | hneg
  · have hwi := (h9 i).1 ⟨hJ, hk⟩
    have hwk : ∀ k ∈ Finset.univ.erase i, w k * Jv k = 0 := fun k hk' => by
      rw [(h9 k).2 (Or.inr ⟨i, (Finset.ne_of_mem_erase hk').symm,
        hk k (Finset.ne_of_mem_erase hk')⟩), zero_mul]
    rw [oa_sum_split (fun k => w k * Jv k) i, Finset.sum_eq_zero hwk, hwi]
    calc ∑ k, w' k * Jv k ≤ ∑ k, w' k * Jv i := Finset.sum_le_sum fun k _ => by
          by_cases hki : k = i
          · rw [hki]
          · exact mul_le_mul_of_nonneg_left (hk k hki).le (hw0' k)
      _ = (∑ k, w' k) * Jv i := by rw [Finset.sum_mul]
      _ ≤ 1 * Jv i := mul_le_mul_of_nonneg_right hw1' hJ.le
      _ = 1 * Jv i + 0 := by ring
  · have hw0 : ∀ k, w k = 0 := fun k => (h9 k).2 (Or.inl (hneg k))
    simp only [hw0, zero_mul, Finset.sum_const_zero]
    exact Finset.sum_nonpos fun k _ => mul_nonpos_of_nonneg_of_nonpos (hw0' k) (hneg k).le

/-! ### Remarks on p. 905 -/

/-- The uniform distribution on `[a, b]` has `Φ(x) = (x - a)/(b - a)` on `[a, b]`. -/
theorem oa_uniform_cdf {a b : ℝ} (h : a < b) {x : ℝ} (hx : x ∈ Set.Icc a b) :
    (uniformDensity a b h).cdf x = (x - a) / (b - a) := by
  change ∫ s in a..x, (Set.Icc a b).indicator (fun _ => (b - a)⁻¹) s = (x - a) / (b - a)
  rw [intervalIntegral.integral_congr (g := fun _ => (b - a)⁻¹) fun s hs => by
    rw [Set.uIcc_of_le hx.1] at hs
    rw [Set.indicator_of_mem (show s ∈ Set.Icc a b from ⟨hs.1, hs.2.trans hx.2⟩)]]
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  ring

/-- The uniform distribution on `[a, b]` has virtual valuation `J(x) = 2x - b` on `[a, b]`. -/
theorem oa_uniform_virtualValue {a b : ℝ} (h : a < b) {x : ℝ} (hx : x ∈ Set.Icc a b) :
    (uniformDensity a b h).virtualValue x = 2 * x - b := by
  have hd : (uniformDensity a b h).dens x = (b - a)⁻¹ := by
    change (Set.Icc a b).indicator (fun _ => (b - a)⁻¹) x = _
    exact Set.indicator_of_mem hx _
  have hba : b - a ≠ 0 := (sub_pos.2 h).ne'
  rw [TypeDensity.virtualValue, oa_uniform_cdf h hx, hd]
  field_simp
  ring

/-- **Example 23.F.2**, remark (1) (MWG, p. 905). With asymmetric bidders, uniform on `[0, 1]`
and on `[0, 2]` (`J₁(θ) = 2θ - 1`, `J₂(θ) = 2θ - 2`), at `θ = (9/10, 1)` every solution of the
relaxed problem gives the good to bidder `1` although bidder `2` has the higher valuation: the
optimal auction is not ex post (classically) efficient. -/
theorem example_23_F_2_remark1 (w : Fin 2 → ℝ)
    (hw : PointwiseOptAlloc (fun i => (![uniformDensity 0 1 zero_lt_one,
      uniformDensity 0 2 zero_lt_two] i).virtualValue (![9 / 10, 1] i)) w) :
    w 0 = 1 ∧ w 1 = 0 ∧ (![9 / 10, 1] : Fin 2 → ℝ) 0 < ![9 / 10, 1] 1 := by
  have h0 : (uniformDensity 0 1 zero_lt_one).virtualValue (9 / 10) = 4 / 5 := by
    rw [oa_uniform_virtualValue _ ⟨by norm_num, by norm_num⟩]; norm_num
  have h1 : (uniformDensity 0 2 zero_lt_two).virtualValue 1 = 0 := by
    rw [oa_uniform_virtualValue _ ⟨by norm_num, by norm_num⟩]; norm_num
  obtain ⟨⟨hw0, hw1⟩, hmax⟩ := hw
  have := hmax ![1, 0] ⟨fun i => by fin_cases i <;> norm_num, by simp⟩
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, h0, h1] at this hw1
  have := hw0 1
  have := hw0 0
  refine ⟨by linarith, by linarith, by norm_num⟩

/-- **Example 23.F.2**, remark (2) (MWG, p. 905). Symmetric bidders, `J` nondecreasing on
`[θ̲, θ̄]` with `J(θ̲) > 0`: giving the good to a bidder `i` with the highest valuation solves the
relaxed problem (23.F.8). -/
theorem example_23_F_2_remark2_pointwise {J : ℝ → ℝ} {lo hi : ℝ}
    (hJ : MonotoneOn J (Set.Icc lo hi)) (hJlo : 0 < J lo) {θ : ι → ℝ}
    (hθ : ∀ k, θ k ∈ Set.Icc lo hi) {i : ι} (hi : ∀ k, θ k ≤ θ i) :
    PointwiseOptAlloc (fun k => J (θ k)) (fun k => if k = i then 1 else 0) := by
  have hJi : 0 < J (θ i) := lt_of_lt_of_le hJlo (hJ ⟨le_rfl, (hθ i).1.trans (hθ i).2⟩ (hθ i)
    (hθ i).1)
  refine ⟨⟨fun k => by dsimp only; split_ifs <;> norm_num, by simp⟩, fun w' ⟨hw0', hw1'⟩ => ?_⟩
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  calc ∑ k, w' k * J (θ k) ≤ ∑ k, w' k * J (θ i) := Finset.sum_le_sum fun k _ =>
        mul_le_mul_of_nonneg_left (hJ (hθ k) (hθ i) (hi k)) (hw0' k)
    _ = (∑ k, w' k) * J (θ i) := by rw [Finset.sum_mul]
    _ ≤ 1 * J (θ i) := mul_le_mul_of_nonneg_right hw1' hJi.le
    _ = J (θ i) := one_mul _

/-- **Example 23.F.2**, remark (2) (MWG, p. 905). Symmetric bidders (all `Dᵢ = D`), `J`
nondecreasing with `J(θ̲) > 0`: any feasible social choice function that gives the good to a
highest-valuation bidder and leaves `U(θ̲) = 0` (e.g. the first-price or second-price auction
equilibrium, by the revenue equivalence theorem) is an optimal auction. -/
theorem example_23_F_2_remark2 (D : TypeDensity) (hJ : MonotoneOn D.virtualValue
      (Set.Icc D.lo D.hi)) (hJlo : 0 < D.virtualValue D.lo) {ys ts : (ι → ℝ) → ι → ℝ}
    (hs : OptAuctionFeasible (fun _ => D) ys ts)
    (hU0 : ∀ i, interimU (Measure.pi fun _ => D.measure) allocV ys ts i D.lo = 0)
    (hwin : ∀ θ, (∀ k, θ k ∈ Set.Icc D.lo D.hi) →
      ∃ i, (∀ k, θ k ≤ θ i) ∧ ys θ = fun k => if k = i then 1 else 0)
    {y t : (ι → ℝ) → ι → ℝ} (h : OptAuctionFeasible (fun _ => D) y t) :
    auctionRevenue (fun _ => D) t ≤ auctionRevenue (fun _ => D) ts := by
  refine example_23_F_2 (fun _ => D) hs hU0 (fun θ hθ => ?_) h
  obtain ⟨i, hi, he⟩ := hwin θ hθ
  rw [he]
  exact example_23_F_2_remark2_pointwise hJ hJlo hθ hi

/-- **Example 23.F.2**, remark (3) (MWG, p. 905). One buyer: if `J` is nondecreasing on
`[θ̲, θ̄]` and `J(p*) = 0` with `p* ∈ [θ̲, θ̄]`, the posted price `p*` (sell iff `θ ≥ p*`) solves
the relaxed problem (23.F.8) at every type. -/
theorem example_23_F_2_remark3_pointwise {J : ℝ → ℝ} {lo hi p : ℝ}
    (hJ : MonotoneOn J (Set.Icc lo hi)) (hp : p ∈ Set.Icc lo hi) (hJp : J p = 0) {x : ℝ}
    (hx : x ∈ Set.Icc lo hi) :
    PointwiseOptAlloc (fun _ : Fin 1 => J x) (fun _ => if p ≤ x then 1 else 0) := by
  refine ⟨⟨fun _ => by split_ifs <;> norm_num, by simp; split_ifs <;> norm_num⟩,
    fun w' ⟨hw0', hw1'⟩ => ?_⟩
  simp only [Fin.sum_univ_one] at hw1' ⊢
  have h0 := hw0' 0
  split_ifs with hpx
  · have : 0 ≤ J x := hJp ▸ hJ hp hx hpx
    nlinarith
  · have : J x ≤ 0 := hJp ▸ hJ hx hp (le_of_lt (not_le.1 hpx))
    nlinarith

/-- **Example 23.F.2**, remark (3) (MWG, p. 905). Where `φ(p) > 0`, the first-order condition
`1 - Φ(p) - pφ(p) = 0` of the posted price problem is equivalent to `J(p) = 0`. -/
theorem example_23_F_2_remark3_foc_iff (D : TypeDensity) {p : ℝ} (hp : 0 < D.dens p) :
    1 - D.cdf p - p * D.dens p = 0 ↔ D.virtualValue p = 0 := by
  rw [TypeDensity.virtualValue, sub_eq_zero, sub_eq_zero, eq_div_iff hp.ne']
  constructor <;> intro h <;> linarith

/-- **Example 23.F.2**, remark (3) (MWG, p. 905). At a point `p` where the density is
continuous, the posted-price revenue `p(1 - Φ(p))` has derivative `1 - Φ(p) - pφ(p)`. -/
theorem example_23_F_2_remark3_foc (D : TypeDensity) {p : ℝ} (hc : ContinuousAt D.dens p) :
    HasDerivAt (fun q => q * (1 - D.cdf q)) (1 - D.cdf p - p * D.dens p) p := by
  have hΦ : HasDerivAt D.cdf (D.dens p) p :=
    intervalIntegral.integral_hasDerivAt_right (D.integrable_dens.intervalIntegrable)
      (D.measurable_dens.stronglyMeasurable.stronglyMeasurableAtFilter) hc
  have := (hasDerivAt_id' p).mul ((hasDerivAt_const p (1 : ℝ)).sub hΦ)
  exact this.congr_deriv (by simp only [Pi.sub_apply]; ring)

/-- **Exercise 23.F.3** (MWG, p. 923). Symmetric bidders with `θ̲ = 0`, `J` nondecreasing and
`J(r) = 0`: the second-price auction with reserve price `r` (the good goes to a highest bidder if
his valuation is at least `r`, and is kept otherwise) solves the relaxed problem (23.F.8), so the
optimal reserve price is the `r` with `J(r) = 0`, independent of the number of bidders. -/
theorem exercise_23_F_3 {J : ℝ → ℝ} {hi r : ℝ} (hJ : MonotoneOn J (Set.Icc 0 hi))
    (hr : r ∈ Set.Icc 0 hi) (hJr : J r = 0) {θ : ι → ℝ} (hθ : ∀ k, θ k ∈ Set.Icc 0 hi)
    {i : ι} (hi : ∀ k, θ k ≤ θ i) :
    PointwiseOptAlloc (fun k => J (θ k)) (fun k => if k = i ∧ r ≤ θ i then 1 else 0) := by
  refine ⟨⟨fun k => by dsimp only; split_ifs <;> norm_num, ?_⟩, fun w' ⟨hw0', hw1'⟩ => ?_⟩
  · by_cases hri : r ≤ θ i
    · simp [hri]
    · simp [hri]
  · by_cases hri : r ≤ θ i
    · have hJi : 0 ≤ J (θ i) := hJr ▸ hJ hr (hθ i) hri
      simp only [hri, and_true, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true]
      calc ∑ k, w' k * J (θ k) ≤ ∑ k, w' k * J (θ i) := Finset.sum_le_sum fun k _ =>
            mul_le_mul_of_nonneg_left (hJ (hθ k) (hθ i) (hi k)) (hw0' k)
        _ = (∑ k, w' k) * J (θ i) := by rw [Finset.sum_mul]
        _ ≤ 1 * J (θ i) := mul_le_mul_of_nonneg_right hw1' hJi
        _ = J (θ i) := one_mul _
    · simp only [hri, and_false, ite_false, zero_mul, Finset.sum_const_zero]
      refine Finset.sum_nonpos fun k _ => mul_nonpos_of_nonneg_of_nonpos (hw0' k) ?_
      have := hJ (hθ k) hr ((hi k).trans (le_of_lt (not_le.1 hri)))
      linarith

/-- **Exercise 23.F.4** (MWG, p. 923). When the seller values the object at `θ₀`, his expected
payoff `∑ᵢ E[-tᵢ(θ)] + θ₀E[1 - ∑ᵢ yᵢ(θ)]` equals `∑ᵢ E[yᵢ(θ)(Jᵢ(θᵢ) - θ₀)] + θ₀ - ∑ᵢ Uᵢ(θ̲ᵢ)`; hence
a feasible `(y*, t*)` with `Uᵢ(θ̲ᵢ) = 0` whose allocation maximises `∑ᵢ yᵢ(Jᵢ(θᵢ) - θ₀)` at every
`θ ∈ Θ` maximises the seller's expected payoff among feasible social choice functions. -/
theorem exercise_23_F_4 (D : ι → TypeDensity) (θ0 : ℝ) {ys ts : (ι → ℝ) → ι → ℝ}
    (hs : OptAuctionFeasible D ys ts)
    (hU0 : ∀ i, interimU (Measure.pi fun j => (D j).measure) allocV ys ts i (D i).lo = 0)
    (hopt : ∀ θ, (∀ i, θ i ∈ Set.Icc (D i).lo (D i).hi) →
      PointwiseOptAlloc (fun i => (D i).virtualValue (θ i) - θ0) (ys θ))
    {y t : (ι → ℝ) → ι → ℝ} (h : OptAuctionFeasible D y t)
    (hy : ∀ i, Integrable (fun θ => y θ i) (Measure.pi fun j => (D j).measure))
    (hys : ∀ i, Integrable (fun θ => ys θ i) (Measure.pi fun j => (D j).measure)) :
    auctionRevenue D t + θ0 * ∫ θ, (1 - ∑ i, y θ i) ∂Measure.pi (fun j => (D j).measure) ≤
      auctionRevenue D ts + θ0 * ∫ θ, (1 - ∑ i, ys θ i) ∂Measure.pi (fun j => (D j).measure) := by
  have : ∀ j, IsProbabilityMeasure (D j).measure := fun j => (D j).isProbabilityMeasure
  obtain ⟨hyF, hint, hbic, ht, hyJ, hIR⟩ := h
  obtain ⟨-, hint', hbic', ht', hyJ', -⟩ := hs
  -- the seller's payoff identity
  have key : ∀ (y t : (ι → ℝ) → ι → ℝ),
      (∀ i, Integrable (fun θ => y θ i) (Measure.pi fun j => (D j).measure)) →
      (∀ i, Integrable (fun θ => y θ i * (D i).virtualValue (θ i))
        (Measure.pi fun j => (D j).measure)) →
      ∑ i, ∫ θ, y θ i * (D i).virtualValue (θ i) ∂Measure.pi (fun j => (D j).measure) +
        θ0 * ∫ θ, (1 - ∑ i, y θ i) ∂Measure.pi (fun j => (D j).measure) =
      ∫ θ, ∑ i, y θ i * ((D i).virtualValue (θ i) - θ0) ∂Measure.pi (fun j => (D j).measure) +
        θ0 := by
    intro y t hy hyJ
    have hs1 : Integrable (fun θ => ∑ i, y θ i) (Measure.pi fun j => (D j).measure) :=
      integrable_finsetSum _ fun i _ => hy i
    have hi : ∀ i, Integrable (fun θ => y θ i * ((D i).virtualValue (θ i) - θ0))
        (Measure.pi fun j => (D j).measure) ∧
        ∫ θ, y θ i * ((D i).virtualValue (θ i) - θ0) ∂Measure.pi (fun j => (D j).measure) =
          ∫ θ, y θ i * (D i).virtualValue (θ i) ∂Measure.pi (fun j => (D j).measure) -
            (∫ θ, y θ i ∂Measure.pi (fun j => (D j).measure)) * θ0 := by
      intro i
      simp_rw [mul_sub]
      exact ⟨(hyJ i).sub ((hy i).mul_const θ0), by
        rw [integral_sub (hyJ i) ((hy i).mul_const θ0), integral_mul_const]⟩
    rw [integral_sub (integrable_const _) hs1, integral_const, probReal_univ, one_smul,
      integral_finsetSum _ fun i _ => hy i, integral_finsetSum _ fun i _ => (hi i).1]
    simp_rw [fun i => (hi i).2]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
    ring
  rw [auctionRevenue, auctionRevenue, eq_23_D_16 D hint hbic ht hyJ,
    eq_23_D_16 D hint' hbic' ht' hyJ']
  simp only [hU0, Finset.sum_const_zero, sub_zero]
  have k1 := key y t hy hyJ
  have k2 := key ys ts hys hyJ'
  have hU : 0 ≤ ∑ i, interimU (Measure.pi fun j => (D j).measure) allocV y t i (D i).lo :=
    Finset.sum_nonneg fun i _ => hIR i _ ⟨le_rfl, (D i).lo_lt_hi.le⟩
  have hint1 : ∀ (y : (ι → ℝ) → ι → ℝ),
      (∀ i, Integrable (fun θ => y θ i) (Measure.pi fun j => (D j).measure)) →
      (∀ i, Integrable (fun θ => y θ i * (D i).virtualValue (θ i))
        (Measure.pi fun j => (D j).measure)) →
      Integrable (fun θ => ∑ i, y θ i * ((D i).virtualValue (θ i) - θ0))
        (Measure.pi fun j => (D j).measure) := fun y hy hyJ =>
    integrable_finsetSum _ fun i _ => by
      simp_rw [mul_sub]; exact (hyJ i).sub ((hy i).mul_const θ0)
  have hle := integral_mono_ae (hint1 y hy hyJ) (hint1 ys hys hyJ') (by
    filter_upwards [re_ae_mem (fun j => (D j).measure) fun j => (D j).measure_compl_Icc]
      with θ hθ
    exact (hopt θ hθ).2 (y θ) (hyF θ hθ))
  linarith

omit [DecidableEq ι] in
/-- **Exercise 23.F.4** (MWG, p. 923). With seller valuation `θ₀`, the optimal allocation gives the
good to buyer `i` if `Jᵢ(θᵢ) > max{θ₀, max_{k≠i} Jₖ(θₖ)}` and not if
`Jᵢ(θᵢ) < max{θ₀, max_{k≠i} Jₖ(θₖ)}` (the (23.F.9) rule with `Jᵢ - θ₀`). -/
theorem exercise_23_F_4_rule {Jv w : ι → ℝ} {θ0 : ℝ}
    (h : PointwiseOptAlloc (fun i => Jv i - θ0) w) (i : ι) :
    ((θ0 < Jv i ∧ ∀ k ≠ i, Jv k < Jv i) → w i = 1) ∧
      ((Jv i < θ0 ∨ ∃ k ≠ i, Jv i < Jv k) → w i = 0) := by
  obtain ⟨h1, h2⟩ := eq_23_F_9 h i
  refine ⟨fun ⟨ha, hb⟩ => h1 ⟨by linarith, fun k hk => by linarith [hb k hk]⟩,
    fun hc => h2 ?_⟩
  rcases hc with hc | ⟨k, hk, hc⟩
  · exact Or.inl (by linarith)
  · exact Or.inr ⟨k, hk, by linarith⟩

/-! ### A concrete instance: one buyer, uniform on `[0, 1]`, posted price `1/2` -/

/-- The posted price `1/2` allocation: the buyer gets the good iff `θ ≥ 1/2`. -/
noncomputable def oaPostY : (Fin 1 → ℝ) → Fin 1 → ℝ := fun θ _ => if 1 / 2 ≤ θ 0 then 1 else 0

/-- The posted price `1/2` transfers: the buyer pays `1/2` iff he gets the good. -/
noncomputable def oaPostT : (Fin 1 → ℝ) → Fin 1 → ℝ :=
  fun θ _ => -(1 / 2) * (if 1 / 2 ≤ θ 0 then 1 else 0)

/-- The uniform distribution on `[0, 1]` has `J(x) = 2x - 1` on `[0, 1]`. -/
theorem oa_uniform01_virtualValue {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    uniform01.virtualValue x = 2 * x - 1 :=
  oa_uniform_virtualValue zero_lt_one hx

/-- **Example 23.F.2**, remark (3) (MWG, p. 905), instance. One buyer with type uniform on
`[0, 1]` (`J(θ) = 2θ - 1`, `J(1/2) = 0`): the posted price `1/2` is feasible (Bayesian incentive
compatible, interim individually rational), leaves `U(0) = 0`, solves (23.F.8), and so maximises
expected revenue among all feasible social choice functions. -/
theorem example_23_F_2_instance :
    OptAuctionFeasible (fun _ : Fin 1 => uniform01) oaPostY oaPostT ∧
      ∀ y t, OptAuctionFeasible (fun _ : Fin 1 => uniform01) y t →
        auctionRevenue (fun _ : Fin 1 => uniform01) t ≤
          auctionRevenue (fun _ : Fin 1 => uniform01) oaPostT := by
  have : IsProbabilityMeasure uniform01.measure := uniform01.isProbabilityMeasure
  have hm : Measurable fun θ : Fin 1 → ℝ => (if 1 / 2 ≤ θ 0 then (1 : ℝ) else 0) :=
    Measurable.ite (measurableSet_le measurable_const (measurable_pi_apply 0))
      measurable_const measurable_const
  have hb : ∀ (i : Fin 1) (a : ℝ), interimBenefit (Measure.pi fun j => uniform01.measure)
      allocV oaPostY i a = if 1 / 2 ≤ a then 1 else 0 := by
    intro i a
    obtain rfl : i = 0 := Subsingleton.elim i 0
    simp [interimBenefit, allocV, oaPostY]
  have hU : ∀ (i : Fin 1) (a : ℝ), interimU (Measure.pi fun j => uniform01.measure)
      allocV oaPostY oaPostT i a = (a - 1 / 2) * (if 1 / 2 ≤ a then 1 else 0) := by
    intro i a
    obtain rfl : i = 0 := Subsingleton.elim i 0
    rw [interimU, hb]
    simp only [interimTransfer, oaPostT, update_self, integral_const, probReal_univ, one_smul]
    ring
  have hJm : Measurable uniform01.virtualValue :=
    measurable_id.sub (((continuous_const.sub uniform01.continuous_cdf).measurable).div
      uniform01.measurable_dens)
  have hfeas : OptAuctionFeasible (fun _ : Fin 1 => uniform01) oaPostY oaPostT := by
    refine ⟨fun θ _ => ⟨fun i => ?_, ?_⟩, fun i a _ => ?_, fun i θi hθi θh hθh => ?_,
      fun i => ?_, fun i => ?_, fun i x hx => ?_⟩
    · simp only [oaPostY]; split_ifs <;> norm_num
    · simp only [oaPostY, Fin.sum_univ_one]; split_ifs <;> norm_num
    · obtain rfl : i = 0 := Subsingleton.elim i 0
      simp only [allocV, oaPostY, oaPostT, update_self]
      exact ⟨integrable_const _, integrable_const _⟩
    · obtain rfl : i = 0 := Subsingleton.elim i 0
      simp only [linU, allocV, oaPostY, oaPostT, update_self, integral_const, probReal_univ,
        one_smul]
      split_ifs <;> nlinarith [hθi.1]
    · exact Integrable.of_bound (hm.const_mul _).aestronglyMeasurable 1
        (ae_of_all _ fun θ => by
          simp only [oaPostT, Real.norm_eq_abs]; split_ifs <;> norm_num)
    · obtain rfl : i = 0 := Subsingleton.elim i 0
      refine Integrable.of_bound ((hm.mul (hJm.comp (measurable_pi_apply 0)))).aestronglyMeasurable
        1 ?_
      filter_upwards [re_ae_mem (fun j => ((fun _ : Fin 1 => uniform01) j).measure)
        fun j => ((fun _ : Fin 1 => uniform01) j).measure_compl_Icc] with θ hθ
      have h0 : θ 0 ∈ Set.Icc (0 : ℝ) 1 := hθ 0
      simp only [oaPostY, Real.norm_eq_abs]
      rw [oa_uniform01_virtualValue h0]
      have := h0.1
      have := h0.2
      split_ifs
      · rw [abs_le]; constructor <;> linarith
      · simp
    · rw [hU]
      split_ifs <;> nlinarith
  refine ⟨hfeas, fun y t h => example_23_F_2 _ hfeas (fun i => ?_) (fun θ hθ => ?_) h⟩
  · rw [hU]; norm_num [uniform01, uniformDensity]
  · have hJ : MonotoneOn uniform01.virtualValue (Set.Icc 0 1) := fun a ha b hb' hab => by
      rw [oa_uniform01_virtualValue ha, oa_uniform01_virtualValue hb']; linarith
    have hp := example_23_F_2_remark3_pointwise hJ (p := 1 / 2) ⟨by norm_num, by norm_num⟩
      (by rw [oa_uniform01_virtualValue ⟨by norm_num, by norm_num⟩]; norm_num) (hθ 0)
    have he : (fun i : Fin 1 => uniform01.virtualValue (θ i)) =
        fun _ => uniform01.virtualValue (θ 0) :=
      funext fun i => by rw [Subsingleton.elim i 0]
    rw [he]
    exact hp

end MWG.MechanismDesign
