/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import ChoiceUnderUncertainty.MixtureRepresentation
import ChoiceUnderUncertainty.AffineUniqueness
import ChoiceUnderUncertainty.SegmentOrder
import MWGPreferenceChoice.PreferenceRelations

/-!
# Simple and compound lotteries

MWG, Section 6.B, pp. 168-170: Definitions 6.B.1 and 6.B.2, the reduced lottery, footnote 4
and Figures 6.B.2-6.B.3.

A simple lottery over a finite outcome set `C` is Kreps's `SimpleLottery C`
(`Kreps.ChoiceUnderUncertainty`, Mathlib's `StdSimplex ℝ C`): on a finite type a finitely
supported probability vector is exactly MWG's list `(p₁, …, p_N)` with `p_n ≥ 0` and
`∑ p_n = 1` (`definition_6_B_1`). Binary mixtures `αL + (1 - α)L'` are Kreps's `Mix`. The
reduced lottery of a compound lottery `(L₁, …, L_K; α₁, …, α_K)` is `reducedLottery`, whose
`n`-th probability is `∑_k α_k p_n^k`. The rationality notion of this chapter is Kreps's,
which is MWG's Definition 1.B.1 (`rational_iff_mwg`).
-/

namespace MWG.ChoiceUnderUncertainty

open Kreps.ChoiceUnderUncertainty Convexity

variable {C : Type*} [Fintype C]

/-- The rationality notion used with lotteries (Kreps Chapter 5's copy) is MWG's
Definition 1.B.1. -/
theorem rational_iff_mwg {X : Type*} (r : X → X → Prop) :
    Rational r ↔ Kreps.ChoicePreferenceUtility.Rational r :=
  Iff.rfl

/-- The simple lottery with a given probability vector. -/
noncomputable def lotteryOfVec (p : C → ℝ) (h0 : ∀ n, 0 ≤ p n) (h1 : ∑ n, p n = 1) :
    SimpleLottery C where
  weights := Finsupp.equivFunOnFinite.symm p
  nonneg := fun n => h0 n
  total := by
    rw [Finsupp.sum_fintype _ _ (by simp)]
    simpa using h1

/-- The probabilities of `lotteryOfVec` are the given vector. -/
@[simp] theorem lotteryOfVec_weights (p : C → ℝ) (h0 : ∀ n, 0 ≤ p n) (h1 : ∑ n, p n = 1)
    (n : C) : (lotteryOfVec p h0 h1).weights n = p n := rfl

/-- **Definition 6.B.1** (MWG, p. 168). A simple lottery is a list `(p₁, …, p_N)` with
`p_n ≥ 0` and `∑ p_n = 1`: the probability vector of a `SimpleLottery C` lies in the simplex,
every vector of the simplex is one, and the vector determines the lottery. -/
theorem definition_6_B_1 :
    (∀ L : SimpleLottery C, (∀ n, 0 ≤ L.weights n) ∧ ∑ n, L.weights n = 1) ∧
    (∀ p : C → ℝ, (∀ n, 0 ≤ p n) → ∑ n, p n = 1 → ∃ L : SimpleLottery C, ⇑L.weights = p) ∧
    (∀ L L' : SimpleLottery C, ⇑L.weights = ⇑L'.weights → L = L') := by
  refine ⟨fun L => ⟨fun n => L.weights_nonneg n, L.total_of_fintype⟩,
    fun p h0 h1 => ⟨lotteryOfVec p h0 h1, rfl⟩, fun L L' h => ?_⟩
  exact StdSimplex.ext (Finsupp.ext (congrFun h))

/-- **p. 169**. The simplex `Δ = {p ∈ ℝ^N_+ : ∑ p_n = 1}` is the set of probability vectors of
simple lotteries. -/
theorem lottery_vectors_eq_simplex :
    Set.range (fun L : SimpleLottery C => ⇑L.weights) =
      {p : C → ℝ | (∀ n, 0 ≤ p n) ∧ ∑ n, p n = 1} := by
  ext p
  constructor
  · rintro ⟨L, rfl⟩
    exact ⟨fun n => L.weights_nonneg n, L.total_of_fintype⟩
  · rintro ⟨h0, h1⟩
    exact ⟨lotteryOfVec p h0 h1, rfl⟩

omit [Fintype C] in
/-- **p. 169**. Each vertex of the simplex is the degenerate lottery giving one outcome for
sure. -/
theorem degenerate_lottery_weights [DecidableEq C] (n m : C) :
    (PureLottery n : SimpleLottery C).weights m = if m = n then 1 else 0 := by
  simp [PureLottery, StdSimplex.single, Finsupp.single_apply, eq_comm]

/-- The reduced probability vector `p_n = α₁ p_n^1 + ⋯ + α_K p_n^K`. -/
noncomputable def reducedVec {K : Type*} [Fintype K] (L : K → SimpleLottery C) (α : K → ℝ)
    (n : C) : ℝ :=
  ∑ k, α k * (L k).weights n

/-- **Footnote 4** (MWG, p. 170). The reduced probabilities are nonnegative and sum to one:
`∑_n p_n = ∑_k α_k (∑_n p_n^k) = ∑_k α_k = 1`. -/
theorem footnote_6_4 {K : Type*} [Fintype K] (L : K → SimpleLottery C) (α : K → ℝ)
    (hα : ∀ k, 0 ≤ α k) (h1 : ∑ k, α k = 1) :
    (∀ n, 0 ≤ reducedVec L α n) ∧ ∑ n, reducedVec L α n = 1 := by
  refine ⟨fun n => Finset.sum_nonneg fun k _ => mul_nonneg (hα k) ((L k).weights_nonneg n), ?_⟩
  unfold reducedVec
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, StdSimplex.total_of_fintype, mul_one, h1]

/-- **Definition 6.B.2** (MWG, p. 169). The reduced lottery of the compound lottery
`(L₁, …, L_K; α₁, …, α_K)`. -/
noncomputable def reducedLottery {K : Type*} [Fintype K] (L : K → SimpleLottery C) (α : K → ℝ)
    (hα : ∀ k, 0 ≤ α k) (h1 : ∑ k, α k = 1) : SimpleLottery C :=
  lotteryOfVec (reducedVec L α) (footnote_6_4 L α hα h1).1 (footnote_6_4 L α hα h1).2

/-- **p. 169**. The `n`-th probability of the reduced lottery. -/
@[simp] theorem reducedLottery_weights {K : Type*} [Fintype K] (L : K → SimpleLottery C)
    (α : K → ℝ) (hα : ∀ k, 0 ≤ α k) (h1 : ∑ k, α k = 1) (n : C) :
    (reducedLottery L α hα h1).weights n = ∑ k, α k * (L k).weights n := rfl

/-- **p. 170**. For two lotteries the reduced lottery is the binary mixture
`αL₁ + (1 - α)L₂`, the point on the segment between `L₁` and `L₂`. -/
theorem reducedLottery_two (L : Fin 2 → SimpleLottery C) (a : Weight) :
    reducedLottery L ![a.val, 1 - a.val]
      (by intro k; fin_cases k <;> simp [a.property.1, a.property.2]) (by simp) =
      Mix a (L 0) (L 1) := by
  apply StdSimplex.ext
  ext n
  simp [lottery_mix_weight]

omit [Fintype C] in
/-- **Figure 6.B.2** (MWG, p. 170). The reduced lottery of `(L₁, L₂; 1/2, 1/2)` is the
midpoint `(1/2)L₁ + (1/2)L₂`. -/
theorem figure_6_B_2 (L₁ L₂ : SimpleLottery C) (n : C) :
    (Mix ⟨1 / 2, by norm_num, by norm_num⟩ L₁ L₂).weights n =
      (L₁.weights n + L₂.weights n) / 2 := by
  rw [lottery_mix_weight]
  ring

/-- **Figure 6.B.3** (MWG, p. 170). The compound lottery giving `(1,0,0)`,
`(1/4,3/8,3/8)`, `(1/4,3/8,3/8)` with probability `1/3` each, and the one giving
`(1/2,1/2,0)`, `(1/2,0,1/2)` with probability `1/2` each, both reduce to `(1/2,1/4,1/4)`. -/
theorem figure_6_B_3 :
    (fun n : Fin 3 => ∑ k : Fin 3, (1 / 3 : ℝ) * (![![1, 0, 0], ![1 / 4, 3 / 8, 3 / 8],
      ![1 / 4, 3 / 8, 3 / 8]] k n)) = ![1 / 2, 1 / 4, 1 / 4] ∧
    (fun n : Fin 3 => ∑ k : Fin 2, (1 / 2 : ℝ) * (![![1 / 2, 1 / 2, 0], ![1 / 2, 0, 1 / 2]] k n))
      = ![1 / 2, 1 / 4, 1 / 4] := by
  constructor <;> ext n <;> fin_cases n <;> simp [Fin.sum_univ_succ] <;> norm_num

/-- **Footnote 2** (MWG, p. 169, Figure 6.B.1(b)). In the equilateral triangle of altitude `1`
with vertices `v₁ = (-1/√3, 0)`, `v₂ = (1/√3, 0)`, `v₃ = (0, 1)`, the point
`p₁v₁ + p₂v₂ + p₃v₃` of a lottery has perpendicular distance `p_n` to the side opposite
`v_n` (distances to the lines `(√3/2)x + y/2 = 1/2`, `-(√3/2)x + y/2 = 1/2` and `y = 0`, written
with unit normals); in particular the three distances sum to the altitude `1`. -/
theorem footnote_6_2 {p₁ p₂ p₃ : ℝ} (h1 : 0 ≤ p₁) (h2 : 0 ≤ p₂) (h3 : 0 ≤ p₃)
    (hs : p₁ + p₂ + p₃ = 1) :
    let X := p₁ * (-1 / Real.sqrt 3) + p₂ * (1 / Real.sqrt 3) + p₃ * 0
    let Y := p₁ * 0 + p₂ * 0 + p₃ * 1
    |Real.sqrt 3 / 2 * X + 1 / 2 * Y - 1 / 2| = p₁ ∧
      |-(Real.sqrt 3 / 2) * X + 1 / 2 * Y - 1 / 2| = p₂ ∧ |Y| = p₃ ∧
      (Real.sqrt 3 / 2) ^ 2 + (1 / 2) ^ 2 = 1 := by
  intro X Y
  have h3' : Real.sqrt 3 ≠ 0 := by positivity
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have eX : Real.sqrt 3 / 2 * X = (p₂ - p₁) / 2 := by
    simp only [X]; field_simp; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [eX, show (p₂ - p₁) / 2 + 1 / 2 * Y - 1 / 2 = -p₁ by simp only [Y]; linarith, abs_neg,
      abs_of_nonneg h1]
  · rw [neg_mul, eX, show -((p₂ - p₁) / 2) + 1 / 2 * Y - 1 / 2 = -p₂ by simp only [Y]; linarith,
      abs_neg, abs_of_nonneg h2]
  · simp only [Y]; rw [abs_of_nonneg (by linarith)]; ring
  · rw [div_pow, hsq]; norm_num

end MWG.ChoiceUnderUncertainty
