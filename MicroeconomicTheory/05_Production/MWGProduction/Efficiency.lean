/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGProduction.Cost
import MWGClassicalDemand.AppendixMG

/-!
# Efficient production (MWG Section 5.F, pp. 149-152)

* **Definition 5.F.1** (`Efficient`) and weak efficiency (footnote 13, `WeaklyEfficient`).
* Efficient plans lie on the boundary of `Y` (`efficient_mem_frontier`), but not conversely
  (Figure 5.F.1(b), `frontier_not_efficient`).
* **Proposition 5.F.1** (first fundamental theorem, `proposition_5_F_1`); **Exercise 5.F.1**
  (`p ≥ 0, p ≠ 0` is not enough).
* **Proposition 5.F.2** (second fundamental theorem, `proposition_5_F_2`, via Chapter 3's
  separating hyperplane theorem M.G.2) and its weakly efficient form (footnote 13); the price
  vector cannot be chosen `≫ 0` (Figure 5.F.4, `figure_5_F_4`).
* The single-output illustration on p. 152 (`efficient_single_output_concave`).

Departure: Proposition 5.F.2 needs `L ≥ 1` (in `ℝ⁰` every plan is efficient and no `p ≠ 0`
exists, `proposition_5_F_2_needs_dimension`).
-/

namespace MWG.Production

open MWG.ClassicalDemand MWG.ConsumerChoice Filter Topology

variable {L : ℕ}

/-- **Definition 5.F.1** (MWG, p. 150). `y ∈ Y` is efficient if no `y' ∈ Y` has `y' ≥ y` and
`y' ≠ y`. -/
def Efficient (Y : Set (Fin L → ℝ)) (y : Fin L → ℝ) : Prop :=
  y ∈ Y ∧ ¬ ∃ y' ∈ Y, y ≤ y' ∧ y' ≠ y

/-- **Footnote 13** (MWG, p. 151). `y ∈ Y` is weakly efficient if no `y' ∈ Y` has `y' ≫ y`. -/
def WeaklyEfficient (Y : Set (Fin L → ℝ)) (y : Fin L → ℝ) : Prop :=
  y ∈ Y ∧ ¬ ∃ y' ∈ Y, ∀ i, y i < y' i

theorem Efficient.weaklyEfficient {Y : Set (Fin L → ℝ)} {y : Fin L → ℝ} (h : Efficient Y y)
    (hL : 0 < L) : WeaklyEfficient Y y := by
  refine ⟨h.1, fun ⟨y', hy', hlt⟩ => h.2 ⟨y', hy', fun i => (hlt i).le, fun he => ?_⟩⟩
  have := hlt ⟨0, hL⟩
  rw [he] at this
  exact lt_irrefl _ this

/-- **Section 5.F** (MWG, p. 150, Figure 5.F.1). Every efficient production plan is on the
boundary of `Y` (for `L ≥ 1`). -/
theorem efficient_mem_frontier {Y : Set (Fin L → ℝ)} {y : Fin L → ℝ} (h : Efficient Y y)
    (hL : 0 < L) : y ∈ frontier Y := by
  refine ⟨subset_closure h.1, fun hint => ?_⟩
  have hnhds : Y ∈ 𝓝 y := mem_interior_iff_mem_nhds.mp hint
  have hg : Continuous fun t : ℝ => y + t • (1 : Fin L → ℝ) := by fun_prop
  have hpre := hg.continuousAt (x := 0) (by simpa using hnhds)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hpre
  have hmem : ε / 2 ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith
  have hin : y + (ε / 2) • (1 : Fin L → ℝ) ∈ Y := hball hmem
  have hle : y ≤ y + (ε / 2) • (1 : Fin L → ℝ) := fun i => by
    simp only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
    linarith
  apply h.2 ⟨_, hin, hle, fun he => ?_⟩
  have := congrFun he ⟨0, hL⟩
  simp at this
  linarith

/-- **Figure 5.F.1(b)** (MWG, p. 150). Not every boundary point is efficient: `(-1, 0)` is on the
boundary of `ℝ²_-` but `0 ≥ (-1, 0)`. -/
theorem frontier_not_efficient :
    (![-1, 0] : Fin 2 → ℝ) ∈ frontier {y : Fin 2 → ℝ | y ≤ 0} ∧
      ¬ Efficient {y : Fin 2 → ℝ | y ≤ 0} ![-1, 0] := by
  have hcl : IsClosed {y : Fin 2 → ℝ | y ≤ 0} := isClosed_le continuous_id continuous_const
  have hmem : (![-1, 0] : Fin 2 → ℝ) ∈ {y : Fin 2 → ℝ | y ≤ 0} := by
    intro i; fin_cases i <;> simp
  refine ⟨⟨subset_closure hmem, fun hint => ?_⟩,
    fun h => h.2 ⟨0, show (0 : Fin 2 → ℝ) ≤ 0 from le_rfl, ?_, ?_⟩⟩
  · have hnhds := mem_interior_iff_mem_nhds.mp hint
    have hg : Continuous fun t : ℝ => (![-1, 0] : Fin 2 → ℝ) + t • (1 : Fin 2 → ℝ) := by
      fun_prop
    have hpre := hg.continuousAt (x := 0) (by simpa using hnhds)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hpre
    have hm : ε / 2 ∈ Metric.ball (0 : ℝ) ε := by
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos (by positivity)]
      linarith
    have := hball hm 1
    simp at this
    linarith
  · intro i; fin_cases i <;> simp
  · intro he
    have := congrFun he 0
    simp at this

/-- **Proposition 5.F.1** (MWG, p. 150). If `y ∈ Y` is profit maximizing for some `p ≫ 0`, then
`y` is efficient. Convexity is not needed (Figure 5.F.2). -/
theorem proposition_5_F_1 {Y : Set (Fin L → ℝ)} {p y : Fin L → ℝ} (hp : StrictlyPositive p)
    (hy : y ∈ supply Y p) : Efficient Y y := by
  refine ⟨hy.1, fun ⟨y', hy', hle, hne⟩ => ?_⟩
  obtain ⟨i, hi⟩ : ∃ i, y i < y' i := by
    by_contra h
    push Not at h
    exact hne (funext fun i => le_antisymm (h i) (hle i))
  have h1 : p ⬝ᵥ y < p ⬝ᵥ y' := by
    apply Finset.sum_lt_sum (fun j _ => mul_le_mul_of_nonneg_left (hle j) (hp j).le)
    exact ⟨i, Finset.mem_univ i, mul_lt_mul_of_pos_left hi (hp i)⟩
  exact absurd (hy.2 y' hy') (not_le.mpr h1)

/-- **Exercise 5.F.1** (MWG, p. 151). A plan can be profit maximizing for some `p ≥ 0`, `p ≠ 0`
and yet be inefficient: in `Y = ℝ²_-`, `y = (-1, 0)` maximizes profits at `p = (0, 1)`. -/
theorem exercise_5_F_1 :
    (0 : Fin 2 → ℝ) ≤ ![0, 1] ∧ (![0, 1] : Fin 2 → ℝ) ≠ 0 ∧
      (![-1, 0] : Fin 2 → ℝ) ∈ supply {y : Fin 2 → ℝ | y ≤ 0} ![0, 1] ∧
      ¬ Efficient {y : Fin 2 → ℝ | y ≤ 0} ![-1, 0] := by
  refine ⟨fun i => by fin_cases i <;> simp, fun h => by simpa using congrFun h 1,
    ⟨fun i => by fin_cases i <;> simp, fun y' hy' => ?_⟩, frontier_not_efficient.2⟩
  have h1 : y' 1 ≤ 0 := hy' 1
  simp [dotProduct, Fin.sum_univ_two, h1]

/-- **Proposition 5.F.2**, weakly efficient form (MWG, p. 151 and footnote 13). If `Y` is convex
and `y ∈ Y` is weakly efficient, then `y` is profit maximizing for some `p ≥ 0`, `p ≠ 0`
(`L ≥ 1`). -/
theorem proposition_5_F_2_weak (hL : 0 < L) {Y : Set (Fin L → ℝ)} (hc : Convex ℝ Y)
    {y : Fin L → ℝ} (hy : WeaklyEfficient Y y) :
    ∃ p : Fin L → ℝ, 0 ≤ p ∧ p ≠ 0 ∧ y ∈ supply Y p := by
  set P := {y' : Fin L → ℝ | ∀ i, y i < y' i} with hP
  have hPc : Convex ℝ P := by
    intro a ha b hb s t hs ht hst i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases hs.lt_or_eq with hs' | hs'
    · have h1 : y i < a i := ha i
      have h2 : y i < b i := hb i
      have h3 : s * y i + t * y i = y i := by rw [← add_mul, hst, one_mul]
      nlinarith [mul_lt_mul_of_pos_left h1 hs', mul_le_mul_of_nonneg_left h2.le ht]
    · subst hs'
      have ht1 : t = 1 := by linarith
      subst ht1
      simp only [zero_mul, one_mul, zero_add]
      exact hb i
  have hPne : P.Nonempty := ⟨y + 1, fun i => by simp⟩
  have hdisj : Disjoint P Y := Set.disjoint_left.mpr fun y' hy'P hy'Y => hy.2 ⟨y', hy'Y, hy'P⟩
  obtain ⟨p, hp0, c, hP', hY'⟩ := theorem_M_G_2_ii hL hPc hc hPne ⟨y, hy.1⟩ hdisj
  have hnonneg : 0 ≤ p := by
    intro l
    by_contra hl0
    have hl : p l < 0 := not_le.mp hl0
    set t := (|c| + |p ⬝ᵥ (y + 1)| + 1) / (-p l) with ht
    have htpos : 0 ≤ t := div_nonneg (by positivity) (by linarith)
    have hmem : y + 1 + t • Pi.single l 1 ∈ P := by
      intro i
      have : 0 ≤ (t • (Pi.single l 1 : Fin L → ℝ)) i := by
        simp only [Pi.smul_apply, smul_eq_mul]
        have hs1 : (0 : Fin L → ℝ) ≤ Pi.single l 1 := Pi.single_nonneg.mpr zero_le_one
        exact mul_nonneg htpos (hs1 i)
      simp only [Pi.add_apply, Pi.one_apply] at this ⊢
      linarith
    have := hP' _ hmem
    rw [dotProduct_add, dotProduct_smul, dotProduct_single, mul_one, smul_eq_mul] at this
    have h2 : t * p l = -(|c| + |p ⬝ᵥ (y + 1)| + 1) := by
      rw [ht, div_mul_eq_mul_div, div_neg, mul_div_assoc, div_self hl.ne, mul_one]
    rw [h2] at this
    linarith [neg_abs_le c, le_abs_self (p ⬝ᵥ (y + 1))]
  refine ⟨p, hnonneg, hp0, hy.1, fun y'' hy'' => ?_⟩
  have hc' : c ≤ p ⬝ᵥ y := by
    apply le_of_forall_pos_le_add
    intro ε hε
    have hp1 : 0 ≤ p ⬝ᵥ (1 : Fin L → ℝ) := dot_nonneg_of_nonneg hnonneg (fun _ => zero_le_one)
    set δ := ε / (p ⬝ᵥ (1 : Fin L → ℝ) + 1) with hδ
    have hδpos : 0 < δ := by positivity
    have hmem : y + δ • (1 : Fin L → ℝ) ∈ P := fun i => by
      simp only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
      linarith
    have := hP' _ hmem
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul] at this
    have : δ * (p ⬝ᵥ (1 : Fin L → ℝ)) ≤ ε := by
      rw [hδ, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  exact (hY' y'' hy'').trans hc'

/-- **Proposition 5.F.2** (MWG, p. 151), second fundamental theorem for production. If `Y` is
convex, every efficient `y ∈ Y` is profit maximizing for some `p ≥ 0`, `p ≠ 0` (`L ≥ 1`). -/
theorem proposition_5_F_2 (hL : 0 < L) {Y : Set (Fin L → ℝ)} (hc : Convex ℝ Y)
    {y : Fin L → ℝ} (hy : Efficient Y y) :
    ∃ p : Fin L → ℝ, 0 ≤ p ∧ p ≠ 0 ∧ y ∈ supply Y p :=
  proposition_5_F_2_weak hL hc (hy.weaklyEfficient hL)

/-- **Proposition 5.F.2** needs `L ≥ 1` (correction): in `ℝ⁰` the plan `0` of `Y = {0}` is
efficient but there is no `p ≠ 0`. -/
theorem proposition_5_F_2_needs_dimension :
    Convex ℝ ({0} : Set (Fin 0 → ℝ)) ∧ Efficient ({0} : Set (Fin 0 → ℝ)) 0 ∧
      ∀ p : Fin 0 → ℝ, p = 0 :=
  ⟨convex_singleton 0, ⟨rfl, fun ⟨_, hy', _, hne⟩ => hne hy'⟩,
    fun _ => funext fun i => i.elim0⟩

/-- The convex technology `{y ∈ ℝ² : y₁ + (max{y₂, 0})² ≤ 0}` of Figure 5.F.4. -/
def figure5F4Set : Set (Fin 2 → ℝ) := {y | y 0 + (max (y 1) 0) ^ 2 ≤ 0}

/-- **Figure 5.F.4** (MWG, p. 152). The second part of Proposition 5.F.2 cannot be strengthened to
`p ≫ 0`: the convex set `Y = {y₁ + (max{y₂, 0})² ≤ 0}` has `0` efficient, `0` is profit maximizing
at `p = (1, 0)`, but at no `p ≫ 0`. -/
theorem figure_5_F_4 :
    Convex ℝ figure5F4Set ∧ Efficient figure5F4Set 0 ∧
      (0 : Fin 2 → ℝ) ∈ supply figure5F4Set ![1, 0] ∧
      ∀ p : Fin 2 → ℝ, StrictlyPositive p → (0 : Fin 2 → ℝ) ∉ supply figure5F4Set p := by
  refine ⟨?_, ⟨by simp [figure5F4Set], fun ⟨y', hy', hle, hne⟩ => ?_⟩, ⟨by simp [figure5F4Set],
    fun y' hy' => ?_⟩, fun p hp h0 => ?_⟩
  · intro y hy y' hy' a b ha hb hab
    simp only [figure5F4Set, Set.mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      at hy hy' ⊢
    set u := max (y 1) 0
    set v := max (y' 1) 0
    have hu : 0 ≤ u := le_max_right _ _
    have hv : 0 ≤ v := le_max_right _ _
    have hmax : max (a * y 1 + b * y' 1) 0 ≤ a * u + b * v := by
      apply max_le
      · exact add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) ha)
          (mul_le_mul_of_nonneg_left (le_max_left _ _) hb)
      · positivity
    have h0 : 0 ≤ max (a * y 1 + b * y' 1) 0 := le_max_right _ _
    have hsq : (max (a * y 1 + b * y' 1) 0) ^ 2 ≤ (a * u + b * v) ^ 2 :=
      pow_le_pow_left₀ h0 hmax 2
    have hconv : (a * u + b * v) ^ 2 ≤ a * u ^ 2 + b * v ^ 2 := by
      have hb' : b = 1 - a := by linarith
      subst hb'
      nlinarith [mul_nonneg (mul_nonneg ha hb) (sq_nonneg (u - v))]
    nlinarith
  · have h0 : 0 ≤ y' 0 := hle 0
    have h1 : 0 ≤ y' 1 := hle 1
    have hy'0 : y' 0 + (max (y' 1) 0) ^ 2 ≤ 0 := hy'
    have hsq : 0 ≤ (max (y' 1) 0) ^ 2 := sq_nonneg _
    have hy0 : y' 0 = 0 := by linarith
    have hm : max (y' 1) 0 = 0 := by nlinarith
    have hy1 : y' 1 = 0 := by
      have := le_max_left (y' 1) 0
      linarith
    apply hne
    funext i
    fin_cases i <;> simp [hy0, hy1]
  · have hy'0 : y' 0 + (max (y' 1) 0) ^ 2 ≤ 0 := hy'
    have hsq : 0 ≤ (max (y' 1) 0) ^ 2 := sq_nonneg _
    simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, one_mul,
      zero_mul, add_zero, Pi.zero_apply, mul_zero]
    linarith
  · set t := p 1 / (2 * p 0) with ht
    have htpos : 0 < t := div_pos (hp 1) (by linarith [hp 0])
    have hmem : (![-(t ^ 2), t] : Fin 2 → ℝ) ∈ figure5F4Set := by
      simp only [figure5F4Set, Set.mem_ofPred_eq, Matrix.cons_val_zero, Matrix.cons_val_one,
        max_eq_left htpos.le]
      linarith
    have := h0.2 _ hmem
    simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Pi.zero_apply, mul_zero, add_zero] at this
    have h2 : p 0 * t ^ 2 = p 1 * t / 2 := by
      rw [ht]; field_simp
    nlinarith [hp 0, hp 1]

/-- **Section 5.F** (MWG, p. 152). For a single-output technology with `f` concave on `ℝ^n_+`,
differentiable at `z̄ ≥ 0` with `∇f(z̄) ≫ 0`, the plan `(-z̄, f(z̄))` is efficient, and it is
profit maximizing at output price `1` and input prices `w = ∇f(z̄)`. -/
theorem efficient_single_output_concave {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hc : ConcaveOn ℝ {z : Fin n → ℝ | 0 ≤ z} f) {z : Fin n → ℝ} (hz : 0 ≤ z)
    (hf : DifferentiableAt ℝ f z) (hgrad : ∀ l, 0 < partialF f z l) :
    extendVec (-z) (f z) ∈ supply (singleOutputSet f) (extendVec (fun l => partialF f z l) 1) ∧
      Efficient (singleOutputSet f) (extendVec (-z) (f z)) := by
  set w : Fin n → ℝ := fun l => partialF f z l
  have hopt := foc_5_C_2_sufficient (w := w) hc zero_le_one hz hf (fun l => by simp [w])
    (by simp [w, dotProduct])
  have hprof : ∀ (z' : Fin n → ℝ) (q : ℝ),
      extendVec w 1 ⬝ᵥ extendVec (-z') q = q - w ⬝ᵥ z' := by
    intro z' q
    simp only [extendVec, dotProduct, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last,
      Pi.neg_apply, mul_neg, Finset.sum_neg_distrib, one_mul]
    ring
  have hmem : extendVec (-z) (f z) ∈ supply (singleOutputSet f) (extendVec w 1) := by
    refine ⟨mem_singleOutputSet.mpr ⟨hz, le_rfl⟩, fun y' hy' => ?_⟩
    rw [← extendVec_inputsOf y'] at hy' ⊢
    obtain ⟨hz', hq'⟩ := mem_singleOutputSet.mp hy'
    rw [hprof, hprof]
    have := hopt _ hz'
    linarith
  refine ⟨hmem, proposition_5_F_1 (fun i => ?_) hmem⟩
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [extendVec]
  · simp only [extendVec, Fin.snoc_castSucc]
    exact hgrad j

end MWG.Production
