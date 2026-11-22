/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGGeneralEquilibriumExamples.TwoByTwo

/-!
# Exercise 15.D.4: a closed 2 × 2 economy (MWG p. 543)

Two consumers, two constant-returns firms and two factors; consumer `i` owns `ownᵢ` of the factors
and consumes only the produced goods.

* **Exercise 15.D.4(a)** (`IsClosedEqm`): prices `p ≫ 0` and `w ≥ 0`, outputs `q ≥ 0` with
  `pⱼ ≤ cⱼ(w)` (equality if `qⱼ > 0`; constant-returns profit maximization, `crs_profitMax_iff`),
  factor demand `∑ⱼ qⱼ aⱼ(w)` at most the endowment with equality for factors with a positive
  price, consumers demanding with incomes `w·ownᵢ`, and goods markets clearing.
* For the Leontief technologies of `leontiefModel` (factor 1 intensive in good 1), consumer 1 owning
  one unit of factor 1 and consumer 2 one unit of factor 2:
  **Exercise 15.D.4(b)**: if consumer 1 only values good 2 and consumer 2 only good 1, there is a
  unique equilibrium (`exercise_15_D_4b`);
  **Exercise 15.D.4(c)**: if consumer 1 only values good 1 and consumer 2 only good 2, there are
  three equilibria with different allocations (`exercise_15_D_4c`).
  (The book's parts (b) and (c) are general graphical arguments; we prove them for this economy.)
-/

namespace MWG.GeneralEquilibriumExamples

open MWG.ConsumerChoice MWG.ClassicalDemand

/-- **Exercise 15.D.4(a)** (MWG, p. 543). An equilibrium of the closed 2 × 2 economy. -/
def IsClosedEqm (M : TwoByTwo) (u : Fin 2 → (Fin 2 → ℝ) → ℝ) (own : Fin 2 → Fin 2 → ℝ)
    (p w q : Fin 2 → ℝ) (x : Fin 2 → Fin 2 → ℝ) : Prop :=
  (∀ j, 0 < p j) ∧ (∀ l, 0 ≤ w l) ∧ (∀ j, 0 ≤ q j) ∧ (∀ j, p j ≤ M.c j w) ∧
    (∀ j, 0 < q j → p j = M.c j w) ∧ (∀ l, ∑ j, q j * M.a j w l ≤ ∑ i, own i l) ∧
    (∀ l, 0 < w l → ∑ j, q j * M.a j w l = ∑ i, own i l) ∧
    (∀ i, x i ∈ walrasianDemand (u i) p (w ⬝ᵥ own i)) ∧ ∀ j, ∑ i, x i j = q j

/-- A consumer who values only good `k`: `u(x) = x_k`. -/
def onlyGood (k : Fin 2) (x : Fin 2 → ℝ) : ℝ := x k

/-- The demand of a consumer who values only good `k`, at `p ≫ 0` and wealth `m ≥ 0`: all wealth
is spent on good `k`. -/
theorem onlyGood_demand {p : Fin 2 → ℝ} (hp : StrictlyPositive p) {m : ℝ} (hm : 0 ≤ m)
    (k : Fin 2) : walrasianDemand (onlyGood k) p m = {Pi.single k (m / p k)} := by
  have hpk := hp k
  ext x
  simp only [Set.mem_singleton_iff]
  have hdot : ∀ y : Fin 2 → ℝ, p ⬝ᵥ y = p 0 * y 0 + p 1 * y 1 := TwoByTwo.dot_two p
  have hmem : Pi.single k (m / p k) ∈ budgetSet p m := by
    refine ⟨fun l => ?_, ?_⟩
    · simp only [Pi.single_apply]
      split_ifs
      · positivity
      · exact le_refl _
    · rw [dotProduct_single, mul_div_cancel₀ _ hpk.ne']
  have hval : onlyGood k (Pi.single k (m / p k)) = m / p k := by simp [onlyGood]
  constructor
  · rintro ⟨⟨hx, hb⟩, hmax⟩
    have h1 := hmax _ hmem
    rw [hval] at h1
    simp only [onlyGood] at h1
    rw [hdot] at hb
    have hp0 := hp 0
    have hp1 := hp 1
    have hx0 := hx 0
    have hx1 := hx 1
    rw [div_le_iff₀ hpk] at h1
    funext l
    fin_cases k
    · simp only [Fin.zero_eta, Fin.isValue] at h1
      have e1 : x 1 = 0 := by nlinarith
      have e0 : x 0 = m / p 0 := by rw [eq_div_iff hp0.ne']; nlinarith
      fin_cases l
      · simpa using e0
      · simpa using e1
    · simp only [Fin.mk_one, Fin.isValue] at h1
      have e0 : x 0 = 0 := by nlinarith
      have e1 : x 1 = m / p 1 := by rw [eq_div_iff hp1.ne']; nlinarith
      fin_cases l
      · simpa using e0
      · simpa using e1
  · rintro rfl
    refine ⟨hmem, fun y hy => ?_⟩
    rw [hval]
    simp only [onlyGood]
    have hb := hy.2
    rw [hdot] at hb
    rw [le_div_iff₀ hpk]
    have hp0 := hp 0
    have hp1 := hp 1
    have hy0 := hy.1 0
    have hy1 := hy.1 1
    fin_cases k <;> simp <;> nlinarith

/-- The ownership pattern of Exercise 15.D.4: consumer 1 owns one unit of factor 1, consumer 2 one
unit of factor 2. -/
def ex15D4own : Fin 2 → Fin 2 → ℝ := ![![1, 0], ![0, 1]]

/-- **Exercise 15.D.4(c)** (MWG, p. 543). With consumer 1 caring only for good 1 and consumer 2 only
for good 2, the Leontief economy has (at least) three equilibria with different allocations:
`w = (1, 1)`, `q = (1/3, 1/3)`; `w = (1, 0)` (factor 2 free), `q = (1/2, 0)`; and `w = (0, 1)`,
`q = (0, 1/2)`. -/
theorem leontief_c0 (w : Fin 2 → ℝ) : leontiefModel.c 0 w = 2 * w 0 + w 1 := by
  simp [TwoByTwo.c, leontiefModel, Matrix.vecHead, Matrix.vecTail]; ring

theorem leontief_c1 (w : Fin 2 → ℝ) : leontiefModel.c 1 w = w 0 + 2 * w 1 := by
  simp [TwoByTwo.c, leontiefModel, Matrix.vecHead, Matrix.vecTail]; ring

/-- A sufficient set of numerical conditions for an equilibrium of the Leontief closed economy
in which consumer `i` values only good `kᵢ`. -/
theorem leontief_closedEqm_of {k : Fin 2 → Fin 2} {p w q : Fin 2 → ℝ}
    {x : Fin 2 → Fin 2 → ℝ} (hp : StrictlyPositive p) (hw : ∀ l, 0 ≤ w l) (hq : ∀ j, 0 ≤ q j)
    (hc0 : p 0 ≤ 2 * w 0 + w 1) (hc1 : p 1 ≤ w 0 + 2 * w 1)
    (hq0 : 0 < q 0 → p 0 = 2 * w 0 + w 1) (hq1 : 0 < q 1 → p 1 = w 0 + 2 * w 1)
    (hf0 : 2 * q 0 + q 1 ≤ 1) (hf1 : q 0 + 2 * q 1 ≤ 1)
    (hb0 : 0 < w 0 → 2 * q 0 + q 1 = 1) (hb1 : 0 < w 1 → q 0 + 2 * q 1 = 1)
    (hx0 : x 0 = Pi.single (k 0) (w 0 / p (k 0))) (hx1 : x 1 = Pi.single (k 1) (w 1 / p (k 1)))
    (hg : ∀ j, x 0 j + x 1 j = q j) :
    IsClosedEqm leontiefModel (fun i => onlyGood (k i)) ex15D4own p w q x := by
  have hown : ∀ i, w ⬝ᵥ ex15D4own i = w i := fun i => by
    fin_cases i <;> simp [ex15D4own, Matrix.vecHead, Matrix.vecTail]
  have hsum : ∀ l, ∑ j, q j * leontiefModel.a j w l = ![2 * q 0 + q 1, q 0 + 2 * q 1] l := by
    intro l
    fin_cases l <;> simp [leontiefModel, Fin.sum_univ_two] <;> ring
  have hownsum : ∀ l, ∑ i, ex15D4own i l = 1 := fun l => by
    fin_cases l <;> simp [ex15D4own, Fin.sum_univ_two]
  refine ⟨hp, hw, hq, fun j => ?_, fun j hj => ?_, fun l => ?_, fun l hl => ?_, fun i => ?_,
    fun j => ?_⟩
  · fin_cases j
    · exact hc0.trans (leontief_c0 w).ge
    · exact hc1.trans (leontief_c1 w).ge
  · fin_cases j
    · exact (hq0 hj).trans (leontief_c0 w).symm
    · exact (hq1 hj).trans (leontief_c1 w).symm
  · rw [hsum, hownsum]
    fin_cases l
    · exact hf0
    · exact hf1
  · rw [hsum, hownsum]
    fin_cases l
    · exact hb0 hl
    · exact hb1 hl
  · rw [hown, onlyGood_demand hp (hw i)]
    fin_cases i
    · exact hx0
    · exact hx1
  · rw [Fin.sum_univ_two]
    exact hg j

/-- **Exercise 15.D.4(c)** (MWG, p. 543). With consumer 1 caring only for good 1 and consumer 2 only
for good 2, the Leontief economy has (at least) three equilibria with different allocations:
`w = (1, 1)`, `q = (1/3, 1/3)`; `w = (1, 0)` (factor 2 free), `q = (1/2, 0)`; and `w = (0, 1)`,
`q = (0, 1/2)`. -/
theorem exercise_15_D_4c :
    IsClosedEqm leontiefModel (fun i => onlyGood (![0, 1] i)) ex15D4own ![3, 3] ![1, 1]
        ![1 / 3, 1 / 3] ![![1 / 3, 0], ![0, 1 / 3]] ∧
      IsClosedEqm leontiefModel (fun i => onlyGood (![0, 1] i)) ex15D4own ![2, 1] ![1, 0]
        ![1 / 2, 0] ![![1 / 2, 0], ![0, 0]] ∧
      IsClosedEqm leontiefModel (fun i => onlyGood (![0, 1] i)) ex15D4own ![1, 2] ![0, 1]
        ![0, 1 / 2] ![![0, 0], ![0, 1 / 2]] := by
  refine ⟨leontief_closedEqm_of (fun l => by fin_cases l <;> norm_num)
      (fun l => by fin_cases l <;> norm_num) (fun j => by fin_cases j <;> norm_num)
      (by norm_num) (by norm_num) (fun _ => by norm_num) (fun _ => by norm_num) (by norm_num)
      (by norm_num) (fun _ => by norm_num) (fun _ => by norm_num) ?_ ?_
      (fun j => by fin_cases j <;> norm_num),
    leontief_closedEqm_of (fun l => by fin_cases l <;> norm_num)
      (fun l => by fin_cases l <;> norm_num) (fun j => by fin_cases j <;> norm_num)
      (by norm_num) (by norm_num) (fun _ => by norm_num) (fun h => by norm_num at h)
      (by norm_num) (by norm_num) (fun _ => by norm_num) (fun h => by norm_num at h) ?_ ?_
      (fun j => by fin_cases j <;> norm_num),
    leontief_closedEqm_of (fun l => by fin_cases l <;> norm_num)
      (fun l => by fin_cases l <;> norm_num) (fun j => by fin_cases j <;> norm_num)
      (by norm_num) (by norm_num) (fun h => by norm_num at h) (fun _ => by norm_num)
      (by norm_num) (by norm_num) (fun h => by norm_num at h) (fun _ => by norm_num) ?_ ?_
      (fun j => by fin_cases j <;> norm_num)⟩ <;>
    (funext l; fin_cases l <;> simp)

/-- **Exercise 15.D.4(b)** (MWG, p. 543). With consumer 1 (owner of factor 1) caring only for
good 2 and consumer 2 only for good 1, every equilibrium of the Leontief economy has equal factor
prices, outputs `q = (1/3, 1/3)` and allocation `x₁ = (0, 1/3)`, `x₂ = (1/3, 0)`: the equilibrium
is unique (up to the scale of prices). -/
theorem exercise_15_D_4b {p w q : Fin 2 → ℝ} {x : Fin 2 → Fin 2 → ℝ}
    (h : IsClosedEqm leontiefModel (fun i => onlyGood (![1, 0] i)) ex15D4own p w q x) :
    w 0 = w 1 ∧ q = ![1 / 3, 1 / 3] ∧ x = ![![0, 1 / 3], ![1 / 3, 0]] := by
  obtain ⟨hp, hw, hq, hpc, hqp, hf, hb, hx, hg⟩ := h
  have hown : ∀ i, w ⬝ᵥ ex15D4own i = w i := fun i => by
    fin_cases i <;> simp [ex15D4own, Matrix.vecHead, Matrix.vecTail]
  have hsum0 : ∑ j, q j * leontiefModel.a j w 0 = 2 * q 0 + q 1 := by
    simp [leontiefModel, Fin.sum_univ_two]; ring
  have hsum1 : ∑ j, q j * leontiefModel.a j w 1 = q 0 + 2 * q 1 := by
    simp [leontiefModel, Fin.sum_univ_two]; ring
  have hown0 : ∑ i, ex15D4own i 0 = 1 := by simp [ex15D4own, Fin.sum_univ_two]
  have hown1 : ∑ i, ex15D4own i 1 = 1 := by simp [ex15D4own, Fin.sum_univ_two]
  -- consumer 1 spends `w₁` on good 2, consumer 2 spends `w₂` on good 1
  have hx0 := hx 0
  have hx1 := hx 1
  simp only [hown] at hx0 hx1
  rw [onlyGood_demand hp (hw 0)] at hx0
  rw [onlyGood_demand hp (hw 1)] at hx1
  have hx0' : x 0 = Pi.single 1 (w 0 / p 1) := hx0
  have hx1' : x 1 = Pi.single 0 (w 1 / p 0) := hx1
  have hq0 : q 0 = w 1 / p 0 := by
    have := hg 0; rw [Fin.sum_univ_two, hx0', hx1'] at this; simp at this; linarith
  have hq1 : q 1 = w 0 / p 1 := by
    have := hg 1; rw [Fin.sum_univ_two, hx0', hx1'] at this; simp at this; linarith
  have hp0 := hp 0
  have hp1 := hp 1
  have hf0 := hf 0
  have hf1 := hf 1
  rw [hsum0, hown0] at hf0
  rw [hsum1, hown1] at hf1
  have hc0 := hpc 0
  have hc1 := hpc 1
  rw [leontief_c0] at hc0
  rw [leontief_c1] at hc1
  -- both factor prices are positive
  have hw0 : 0 < w 0 := by
    rcases eq_or_lt_of_le (hw 0) with h0 | h0
    · exfalso
      -- then good 1 is bought by consumer 2 with income `w₂` and costs `w₂`
      have hw1 : 0 < w 1 := by
        rcases eq_or_lt_of_le (hw 1) with h1 | h1
        · rw [← h0, ← h1] at hc0; linarith
        · exact h1
      have hq0pos : 0 < q 0 := by rw [hq0]; positivity
      have := hqp 0 hq0pos
      rw [leontief_c0, ← h0] at this
      have hq0one : q 0 = 1 := by rw [hq0, this]; field_simp; ring
      nlinarith [hq 1]
    · exact h0
  have hw1 : 0 < w 1 := by
    rcases eq_or_lt_of_le (hw 1) with h1 | h1
    · exfalso
      have hq1pos : 0 < q 1 := by rw [hq1]; positivity
      have := hqp 1 hq1pos
      rw [leontief_c1, ← h1] at this
      have hq1one : q 1 = 1 := by rw [hq1, this]; field_simp; ring
      nlinarith [hq 0]
    · exact h1
  have hb0 := hb 0 hw0
  have hb1 := hb 1 hw1
  rw [hsum0, hown0] at hb0
  rw [hsum1, hown1] at hb1
  have e0 : q 0 = 1 / 3 := by linarith
  have e1 : q 1 = 1 / 3 := by linarith
  have hpc1 : p 1 = w 0 + 2 * w 1 := by
    have := hqp 1 (by rw [e1]; norm_num); rwa [leontief_c1] at this
  have hww : w 0 = w 1 := by
    rw [hq1, hpc1, div_eq_iff (by positivity)] at e1
    linarith
  refine ⟨hww, ?_, ?_⟩
  · funext l
    fin_cases l
    · simpa using e0
    · simpa using e1
  · have g00 : x 0 0 = 0 := by rw [hx0']; simp
    have g01 : x 0 1 = 1 / 3 := by rw [hx0']; simp; linarith
    have g10 : x 1 0 = 1 / 3 := by rw [hx1']; simp; linarith
    have g11 : x 1 1 = 0 := by rw [hx1']; simp
    funext i l
    fin_cases i <;> fin_cases l <;> simp [g00, g01, g10, g11]

end MWG.GeneralEquilibriumExamples
