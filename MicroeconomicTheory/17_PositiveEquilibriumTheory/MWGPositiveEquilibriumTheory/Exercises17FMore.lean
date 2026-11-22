/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPositiveEquilibriumTheory.StrongGrossSubstitutesSmooth
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Exercises 17.F.15 and 17.F.17 (MWG pp. 646-647)

* **Exercise 17.F.15** (taxes, `exercise_17_F_15`). One consumer, a Leontief technology (one
  primary factor, good `0`; good `l + 1` made from `aₗ > 0` units of it, constant returns, no joint
  production), ad valorem taxes `pₗ = (1 + tₗ)qₗ` and lump-sum rebate of the receipts
  (`IsLeontiefTaxEqm`). Producer prices are pinned down by the technology (`q = (1, a)`, zero
  profit:
  `taxProfit_zero`), and if every good is normal the equilibrium is unique: market clearing gives
  `q·x(W) = q·ω`, and `W ↦ q·x(W)` is strictly increasing when `x(·)` is nondecreasing and
  exhausts wealth. Normality cannot be dropped (`exercise_17_F_15_normality`): with one input and
  one output, a subsidy `t₁ = -1/2` and an inferior output, every `W ∈ [1/2, 1]` gives an
  equilibrium (the example is a wealth-expansion path at the fixed consumer prices; preferences
  generating it are not constructed).
* **Exercise 17.F.17** (Becker 1962, Grandmont 1992; `exercise_17_F_17`). With `L = 2`, a
  consumer choosing at random, uniformly on the budget line `{x ≥ 0 : p·x = w}`
  (`beckerLine`, a constant-speed parametrization by `s ∈ [0, 1]`), has expected choice
  `(w/2p₁, w/2p₂)` (`beckerMean`): the average excess demand of a continuum of such consumers with
  endowment `ω` is the excess demand of a Cobb-Douglas consumer `x₁^{1/2}x₂^{1/2}` with endowment
  `ω`, a positive representative consumer.
-/

namespace MWG.PositiveEquilibriumTheory

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.GeneralEquilibriumExamples

variable {n : ℕ}

/-! ### Exercise 17.F.15 -/

/-- **Exercise 17.F.15** (MWG, p. 646). Producer prices of the Leontief economy: the factor
(good `0`) is the numeraire and good `l + 1` costs `aₗ` (zero profit). -/
def taxProducerPrice (a : Fin n → ℝ) : Fin (n + 1) → ℝ := Fin.cons 1 a

/-- Consumer prices `pₗ = (1 + tₗ) qₗ`. -/
def taxConsumerPrice (a : Fin n → ℝ) (t : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  fun l => (1 + t l) * taxProducerPrice a l

/-- The Leontief production plan with activity levels `s`: `y₀ = -∑ aₗ sₗ`, `y_{l+1} = sₗ`. -/
def leontiefPlan (a s : Fin n → ℝ) : Fin (n + 1) → ℝ := Fin.cons (-∑ l, a l * s l) s

/-- At the producer prices `q = (1, a)` every Leontief plan makes zero profit (so every plan is
profit maximizing, and these are the only prices at which all goods can be produced). -/
theorem taxProfit_zero (a s : Fin n → ℝ) : taxProducerPrice a ⬝ᵥ leontiefPlan a s = 0 := by
  simp [taxProducerPrice, leontiefPlan, dotProduct, Fin.sum_univ_succ]

/-- **Exercise 17.F.15** (MWG, p. 646): the definition of a (distorted) equilibrium. The consumer
(demand `X(W)` at the consumer prices `p = (1 + t)q`, wealth `W`) has endowment `ω`; activity
levels `s ≥ 0`, and the lump-sum transfer `T` satisfy: demand at `W = p·ω + T` equals `ω + y(s)`
(market clearing), and `T = ∑ₗ tₗ qₗ (xₗ - ωₗ)` (tax receipts returned lump sum). -/
def IsLeontiefTaxEqm (a : Fin n → ℝ) (t ω : Fin (n + 1) → ℝ) (X : ℝ → Fin (n + 1) → ℝ)
    (s : Fin n → ℝ) (T : ℝ) : Prop :=
  (∀ l, 0 ≤ s l) ∧ X (taxConsumerPrice a t ⬝ᵥ ω + T) = ω + leontiefPlan a s ∧
    T = ∑ l, t l * taxProducerPrice a l * (X (taxConsumerPrice a t ⬝ᵥ ω + T) l - ω l)

/-- **Exercise 17.F.15** (MWG, p. 646). In the one-consumer economy with a Leontief technology and
ad valorem taxes, if demand exhausts wealth (`p·X(W) = W`) and all goods are normal
(`X` nondecreasing in `W`), the equilibrium is unique: equal activity levels and transfers. -/
theorem exercise_17_F_15 {a : Fin n → ℝ} (ha : ∀ l, 0 < a l) {t ω : Fin (n + 1) → ℝ}
    {X : ℝ → Fin (n + 1) → ℝ}
    (hX : ∀ W, taxConsumerPrice a t ⬝ᵥ X W = W) (hnormal : Monotone X) {s s' : Fin n → ℝ}
    {T T' : ℝ} (he : IsLeontiefTaxEqm a t ω X s T) (he' : IsLeontiefTaxEqm a t ω X s' T') :
    s = s' ∧ T = T' := by
  set q := taxProducerPrice a with hq
  set p := taxConsumerPrice a t with hp
  have hq0 : ∀ l, 0 < q l := fun l => by
    refine Fin.cases ?_ (fun l => ?_) l
    · simp [q, taxProducerPrice]
    · simp [q, taxProducerPrice, ha l]
  -- `q·X(W) = q·ω` at an equilibrium
  have hfeas : ∀ {s : Fin n → ℝ} {T : ℝ}, IsLeontiefTaxEqm a t ω X s T →
      q ⬝ᵥ X (p ⬝ᵥ ω + T) = q ⬝ᵥ ω :=
    fun {s T} h => by rw [h.2.1, dotProduct_add, taxProfit_zero, add_zero]
  -- `W ↦ q·X(W)` is strictly increasing
  have hstrict : StrictMono fun W => q ⬝ᵥ X W := by
    intro W W' hW
    have hle : X W ≤ X W' := hnormal hW.le
    have hne : X W ≠ X W' := fun h => by
      have := congrArg (fun x => p ⬝ᵥ x) h
      simp only [hX] at this
      exact hW.ne this
    obtain ⟨j, hj⟩ : ∃ j, X W j < X W' j := by
      by_contra hcon
      push Not at hcon
      exact hne (funext fun i => le_antisymm (hle i) (hcon i))
    exact Finset.sum_lt_sum (fun i _ => mul_le_mul_of_nonneg_left (hle i) (hq0 i).le)
      ⟨j, Finset.mem_univ j, mul_lt_mul_of_pos_left hj (hq0 j)⟩
  have hW : p ⬝ᵥ ω + T = p ⬝ᵥ ω + T' :=
    hstrict.injective ((hfeas he).trans (hfeas he').symm)
  have hT : T = T' := by linarith
  refine ⟨?_, hT⟩
  have h1 := he.2.1
  have h2 := he'.2.1
  rw [hW] at h1
  rw [h1] at h2
  funext l
  have := congrFun h2 l.succ
  simpa [leontiefPlan] using this

/-- The wealth-expansion path of the example: `x₁(W) = min(2W, max(0, 2 - 2W))`,
`x₀(W) = W - x₁(W)/2` (consumer prices `(1, 1/2)`). Good 1 is inferior on `[1/2, 1]`. -/
noncomputable def taxPath (W : ℝ) : Fin 2 → ℝ :=
  ![W - min (2 * W) (max 0 (2 - 2 * W)) / 2, min (2 * W) (max 0 (2 - 2 * W))]

/-- **Exercise 17.F.15** (MWG, p. 646), nondispensability of normality. One input (good `0`,
endowment `1`) and one output (`a = 1`), a subsidy `t₁ = -1/2` on the output: consumer prices
`(1, 1/2)`. The demand path `taxPath` exhausts wealth and is nonnegative, but good 1 is inferior,
and every `W ∈ [1/2, 1]` is an equilibrium (`T = W - 1`, output `s = 2 - 2W`): two distinct ones
are `(s, T) = (1/2, -1/4)` and `(1/4, -1/8)`. -/
theorem exercise_17_F_15_normality :
    (∀ W, taxConsumerPrice ![1] ![0, -1 / 2] ⬝ᵥ taxPath W = W) ∧
      (∀ W, 0 ≤ W → ∀ l, 0 ≤ taxPath W l) ∧ taxPath (7 / 8) 1 < taxPath (3 / 4) 1 ∧
      IsLeontiefTaxEqm ![1] ![0, -1 / 2] ![1, 0] taxPath ![1 / 2] (-1 / 4) ∧
      IsLeontiefTaxEqm ![1] ![0, -1 / 2] ![1, 0] taxPath ![1 / 4] (-1 / 8) := by
  have hp : taxConsumerPrice ![1] ![0, -1 / 2] = ![1, 1 / 2] := by
    funext l; fin_cases l <;> norm_num [taxConsumerPrice, taxProducerPrice]
  have hpω : taxConsumerPrice ![1] ![0, -1 / 2] ⬝ᵥ ![1, 0] = 1 := by
    rw [hp]; norm_num [dotProduct, Fin.sum_univ_succ]
  refine ⟨fun W => ?_, fun W hW l => ?_, ?_, ?_, ?_⟩
  · rw [hp]; simp [taxPath, dotProduct, Fin.sum_univ_two]; ring
  · set m := min (2 * W) (max 0 (2 - 2 * W))
    have h1 : m ≤ 2 * W := min_le_left _ _
    have h2 : 0 ≤ m := le_min (by linarith) (le_max_left _ _)
    fin_cases l
    · simp [taxPath]; linarith
    · simpa [taxPath, m] using h2
  · simp only [taxPath, Matrix.cons_val_one, Matrix.cons_val_zero]
    norm_num [min_def, max_def]
  · refine ⟨fun l => by fin_cases l; norm_num, ?_, ?_⟩
    · rw [hpω]
      funext l
      fin_cases l <;> norm_num [taxPath, leontiefPlan, min_def, max_def]
    · rw [hpω]
      norm_num [Fin.sum_univ_succ, taxProducerPrice, taxPath, min_def, max_def]
  · refine ⟨fun l => by fin_cases l; norm_num, ?_, ?_⟩
    · rw [hpω]
      funext l
      fin_cases l <;> norm_num [taxPath, leontiefPlan, min_def, max_def]
    · rw [hpω]
      norm_num [Fin.sum_univ_succ, taxProducerPrice, taxPath, min_def, max_def]

/-! ### Exercise 17.F.17 -/

/-- **Exercise 17.F.17** (MWG, p. 647). The budget line `{x ≥ 0 : p·x = w}` parametrized by
`s ∈ [0, 1]`: `x(s) = (sw/p₁, (1 - s)w/p₂)`, affine with constant velocity, so the uniform
distribution on the budget line is the image of the uniform distribution on `[0, 1]`. -/
noncomputable def beckerLine (p : Fin 2 → ℝ) (w s : ℝ) : Fin 2 → ℝ :=
  ![s * w / p 0, (1 - s) * w / p 1]

/-- The parametrization is affine (constant velocity `(w/p₁, -w/p₂)`), lies on the budget line,
is nonnegative for `s ∈ [0, 1]`, and reaches every point of the budget line. -/
theorem beckerLine_props {p : Fin 2 → ℝ} (hp : ∀ l, 0 < p l) {w : ℝ} (hw : 0 < w) :
    (∀ s, beckerLine p w s = beckerLine p w 0 + s • ![w / p 0, -(w / p 1)]) ∧
      (∀ s, p ⬝ᵥ beckerLine p w s = w) ∧
      (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ l, 0 ≤ beckerLine p w s l) ∧
      ∀ x : Fin 2 → ℝ, (∀ l, 0 ≤ x l) → p ⬝ᵥ x = w →
        ∃ s ∈ Set.Icc (0 : ℝ) 1, beckerLine p w s = x := by
  have h0 := (hp 0).ne'
  have h1 := (hp 1).ne'
  refine ⟨fun s => ?_, fun s => ?_, fun s hs l => ?_, fun x hx hpx => ?_⟩
  · funext l; fin_cases l <;> simp [beckerLine] <;> ring
  · simp [beckerLine, dotProduct, Fin.sum_univ_two]; field_simp; ring
  · fin_cases l
    · exact div_nonneg (mul_nonneg hs.1 hw.le) (hp 0).le
    · exact div_nonneg (mul_nonneg (by linarith [hs.2]) hw.le) (hp 1).le
  · have hpx' : p 0 * x 0 + p 1 * x 1 = w := by simpa [dotProduct, Fin.sum_univ_two] using hpx
    refine ⟨p 0 * x 0 / w, ⟨div_nonneg (mul_nonneg (hp 0).le (hx 0)) hw.le, ?_⟩, ?_⟩
    · rw [div_le_one hw]; nlinarith [mul_nonneg (hp 1).le (hx 1)]
    · funext l
      fin_cases l
      · simp [beckerLine]; field_simp
      · simp [beckerLine]; field_simp; linarith

/-- The expected choice: the mean of `x(s)` for `s` uniform on `[0, 1]`. -/
noncomputable def beckerMean (p : Fin 2 → ℝ) (w : ℝ) : Fin 2 → ℝ :=
  fun l => ∫ s in (0 : ℝ)..1, beckerLine p w s l

theorem beckerMean_eq (p : Fin 2 → ℝ) (w : ℝ) :
    beckerMean p w = ![w / (2 * p 0), w / (2 * p 1)] := by
  funext l
  fin_cases l
  · simp only [beckerMean, beckerLine, Matrix.cons_val_zero, Fin.zero_eta]
    rw [intervalIntegral.integral_div, intervalIntegral.integral_mul_const, integral_id]
    simp; ring
  · simp only [beckerMean, beckerLine, Matrix.cons_val_one, Fin.mk_one, Matrix.cons_val_zero]
    rw [intervalIntegral.integral_div, intervalIntegral.integral_mul_const,
      intervalIntegral.integral_sub intervalIntegrable_const intervalIntegral.intervalIntegrable_id,
      integral_id]
    simp; ring

/-- **Exercise 17.F.17** (MWG, p. 647). With `L = 2` and a continuum of consumers with endowment
`ω ≥ 0`, each choosing uniformly at random on the budget line, the average excess demand
`z(p) = E[x] - ω` is the excess demand of one Cobb-Douglas consumer with utility
`x₁^{1/2} x₂^{1/2}` and endowment `ω`: `E[x]` is exactly the Cobb-Douglas demand. So the economy
admits a positive representative consumer (Section 4.D). -/
theorem exercise_17_F_17 {p ω : Fin 2 → ℝ} (hp : ∀ l, 0 < p l) (hω : ∀ l, 0 ≤ ω l) :
    beckerMean p (p ⬝ᵥ ω) - ω = cd1ED (fun _ => 1) ω p ∧
      walrasianDemand (cdUtility (fun _ => 1)) p (p ⬝ᵥ ω) = {beckerMean p (p ⬝ᵥ ω)} := by
  have hmean : beckerMean p (p ⬝ᵥ ω) = cdDemand (fun _ => 1) p (p ⬝ᵥ ω) := by
    rw [beckerMean_eq]
    funext l
    fin_cases l <;> simp [cdDemand] <;> field_simp
  refine ⟨by rw [hmean]; rfl, ?_⟩
  rw [hmean]
  exact walrasianDemand_cobbDouglas (fun _ => one_pos) hp (cd_wealth_nonneg hp hω)

end MWG.PositiveEquilibriumTheory
