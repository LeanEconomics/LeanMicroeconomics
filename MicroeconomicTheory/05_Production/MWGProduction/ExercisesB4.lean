/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGProduction.ExercisesB

/-!
# Exercise 5.B.4: the closed case (MWG, p. 160)

`ExercisesB` shows that the additive closure `Y⁺` of the decreasing-returns technology of
Figure 5.B.5(a) is not closed. The reason is that arbitrarily small plants have positive output
at a high average product. In the technology of Figure 5.B.5(b) returns are increasing at small
scale, so two small plants can be merged into one without loss.

`exercise_5_B_4_closed` makes this precise for one input (good 1) and one output (good 2): let
`Y` be closed, use good 1 as an input (`y₁ ≤ 0`), have bounded output for bounded input, and
let two plans with input below some `δ > 0` be replaceable by their sum
(`y, y' ∈ Y`, `y₁, y'₁ > -δ` imply `y + y' ∈ Y`, increasing returns at small scale). Then `Y⁺`
is closed. The proof puts each element of `Y⁺` in a normal form with at most one plan using
less than `δ` of the input (`b4_normal_form`), so an element of `Y⁺` with input at most `B`
is a sum of at most `B/δ + 1` plans from a compact set, and `Y⁺` is locally a finite union of
compact sets.

`exercise_5_B_4_closed_instance`: the S-shaped technology `{y₁ ≤ 0, y₂ ≤ min(y₁², 1)}`
(increasing then decreasing returns, nonincreasing returns violated, as in Figure 5.B.5(b))
satisfies the hypotheses, so its additive closure is closed.
-/

namespace MWG.Production

open MWG.ClassicalDemand MWG.ConsumerChoice Filter Topology

/-- A finite sum `Σ_{i ≤ m} y_i` of elements of `Y` lies in `Y⁺`. -/
theorem b4_sum_mem_addClosure {L : ℕ} {Y : Set (Fin L → ℝ)} :
    ∀ (m : ℕ) (ys : Fin (m + 1) → Fin L → ℝ), (∀ i, ys i ∈ Y) → ∑ i, ys i ∈ addClosure Y := by
  have hc := exercise_5_B_4_closure Y
  intro m
  induction m with
  | zero => intro ys hys; simpa using hc.1 (hys 0)
  | succ m ih =>
    intro ys hys
    rw [Fin.sum_univ_succ]
    exact hc.2.1 _ (hc.1 (hys 0)) _ (ih (fun i => ys i.succ) fun i => hys _)

/-- Normal form: if two plans using less than `δ` of the input can be merged, every element of
`Y⁺` is a sum `Σ_{i ≤ m} y_i` of plans of `Y` in which all but `y₀` use at least `δ`. -/
theorem b4_normal_form {Y : Set (Fin 2 → ℝ)} {δ : ℝ}
    (hmerge : ∀ y ∈ Y, ∀ y' ∈ Y, -δ < y 0 → -δ < y' 0 → y + y' ∈ Y) {x : Fin 2 → ℝ}
    (hx : x ∈ addClosure Y) :
    ∃ (m : ℕ) (ys : Fin (m + 1) → Fin 2 → ℝ), (∀ i, ys i ∈ Y) ∧
      (∀ i : Fin m, ys i.succ 0 ≤ -δ) ∧ x = ∑ i, ys i := by
  obtain ⟨k, zs, hzs, rfl⟩ := hx
  induction k with
  | zero => exact ⟨0, fun _ => zs 0, fun _ => hzs 0 le_rfl, fun i => i.elim0, by simp⟩
  | succ k ih =>
    obtain ⟨m, ys, hys, hbig, hsum⟩ := ih fun i hi => hzs i (by omega)
    set y := zs (k + 1) with hy
    have hyY : y ∈ Y := hzs (k + 1) le_rfl
    rw [Finset.sum_range_succ, hsum]
    by_cases h1 : y 0 ≤ -δ
    · refine ⟨m + 1, Fin.cons (ys 0) (Fin.cons y (Fin.tail ys)), ?_, ?_, ?_⟩
      · intro i
        refine Fin.cases (hys 0) (fun j => ?_) i
        refine Fin.cases hyY (fun l => ?_) j
        exact hys l.succ
      · intro i
        refine Fin.cases h1 (fun l => ?_) i
        exact hbig l
      · simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.tail, hy]
        abel
    · push Not at h1
      by_cases h2 : ys 0 0 ≤ -δ
      · refine ⟨m + 1, Fin.cons y ys, ?_, ?_, ?_⟩
        · intro i
          refine Fin.cases hyY (fun l => ?_) i
          exact hys l
        · intro i
          refine Fin.cases h2 (fun l => ?_) i
          exact hbig l
        · simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, hy]
          abel
      · push Not at h2
        refine ⟨m, Fin.cons (ys 0 + y) (Fin.tail ys), ?_, ?_, ?_⟩
        · intro i
          refine Fin.cases (hmerge _ (hys 0) _ hyY h2 h1) (fun l => ?_) i
          exact hys l.succ
        · intro i
          exact hbig i
        · simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.tail, hy]
          abel

/-- **Exercise 5.B.4** (MWG, p. 160), the closed case of Figure 5.B.5(b). Let `Y ⊆ ℝ²` be closed,
with good 1 an input (`y₁ ≤ 0`), output bounded for bounded input, and increasing returns at
small scale: two plans each using less than `δ > 0` of the input can be merged
(`y + y' ∈ Y`). Then the additive closure `Y⁺` is closed. -/
theorem exercise_5_B_4_closed {Y : Set (Fin 2 → ℝ)} (hcl : IsClosed Y)
    (hin : ∀ y ∈ Y, y 0 ≤ 0) (hbdd : ∀ B : ℝ, ∃ U : ℝ, ∀ y ∈ Y, -B ≤ y 0 → y 1 ≤ U)
    {δ : ℝ} (hδ : 0 < δ) (hmerge : ∀ y ∈ Y, ∀ y' ∈ Y, -δ < y 0 → -δ < y' 0 → y + y' ∈ Y) :
    IsClosed (addClosure Y) := by
  -- closedness on each box `R_B = {x₁ ≥ -B, x₂ ≥ -B}`
  have hbox : ∀ B : ℝ, IsClosed (addClosure Y ∩ {x | -B ≤ x 0 ∧ -B ≤ x 1}) := by
    intro B
    obtain ⟨U, hU⟩ := hbdd B
    set U' := max U 0 with hU'
    set K : ℕ := ⌊B / δ⌋₊ with hK
    set lo : ℝ := -B - K * U' with hlo
    set box : Set (Fin 2 → ℝ) := Set.univ.pi fun l => Set.Icc (![-B, lo] l) (![0, U'] l)
      with hboxdef
    have hboxc : IsCompact box := isCompact_univ_pi fun l => isCompact_Icc
    have hboxmem : ∀ v : Fin 2 → ℝ, v ∈ box ↔ (-B ≤ v 0 ∧ v 0 ≤ 0) ∧ (lo ≤ v 1 ∧ v 1 ≤ U') := by
      intro v
      simp only [hboxdef, Set.mem_univ_pi, Set.mem_Icc, Fin.forall_fin_two]
      simp
    -- the compact sets of tuples
    set T : ℕ → Set (Fin 2 → ℝ) := fun m =>
      (fun ys : Fin (m + 1) → Fin 2 → ℝ => ∑ i, ys i) ''
        {ys | ∀ i, ys i ∈ Y ∧ ys i ∈ box} with hT
    have hTc : ∀ m, IsClosed (T m) := by
      intro m
      have hcpt : IsCompact {ys : Fin (m + 1) → Fin 2 → ℝ | ∀ i, ys i ∈ Y ∧ ys i ∈ box} := by
        refine (isCompact_univ_pi fun _ => hboxc).of_isClosed_subset ?_ ?_
        · have : {ys : Fin (m + 1) → Fin 2 → ℝ | ∀ i, ys i ∈ Y ∧ ys i ∈ box} =
              ⋂ i, (fun ys : Fin (m + 1) → Fin 2 → ℝ => ys i) ⁻¹' (Y ∩ box) := by
            ext ys; simp [Set.mem_iInter]
          rw [this]
          exact isClosed_iInter fun i => (hcl.inter hboxc.isClosed).preimage (continuous_apply i)
        · intro ys hys
          simp only [Set.mem_univ_pi]
          exact fun i => (hys i).2
      exact (hcpt.image (continuous_finsetSum _ fun i _ => continuous_apply i)).isClosed
    have hRc : IsClosed {x : Fin 2 → ℝ | -B ≤ x 0 ∧ -B ≤ x 1} :=
      (isClosed_le continuous_const (continuous_apply 0)).inter
        (isClosed_le continuous_const (continuous_apply 1))
    have heq : addClosure Y ∩ {x | -B ≤ x 0 ∧ -B ≤ x 1} =
        (⋃ m ∈ Finset.range (K + 1), T m) ∩ {x | -B ≤ x 0 ∧ -B ≤ x 1} := by
      ext x
      constructor
      · rintro ⟨hx, hxB⟩
        refine ⟨?_, hxB⟩
        obtain ⟨m, ys, hys, hbig, rfl⟩ := b4_normal_form hmerge hx
        have hsum0 : (∑ i, ys i) 0 = ∑ i, ys i 0 := Finset.sum_apply _ _ _
        have hsum1 : (∑ i, ys i) 1 = ∑ i, ys i 1 := Finset.sum_apply _ _ _
        have hneg : ∀ i, ys i 0 ≤ 0 := fun i => hin _ (hys i)
        -- each plan uses at most the total input
        have hge : ∀ i, (∑ j, ys j) 0 ≤ ys i 0 := by
          intro i
          rw [hsum0]
          calc ∑ j, ys j 0 ≤ ∑ j ∈ {i}, ys j 0 :=
                Finset.sum_le_sum_of_subset_of_nonpos (by simp) fun j _ _ => hneg j
            _ = ys i 0 := by simp
        have hm : (m : ℝ) * δ ≤ B := by
          have h1 : ∑ i : Fin m, ys i.succ 0 ≤ ∑ _i : Fin m, -δ :=
            Finset.sum_le_sum fun i _ => hbig i
          have h2 : (∑ j, ys j) 0 = ys 0 0 + ∑ i : Fin m, ys i.succ 0 := by
            rw [hsum0, Fin.sum_univ_succ]
          have h3 := hneg 0
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
          linarith [hxB.1]
        have hmK : m ≤ K := by
          rw [hK]
          apply Nat.le_floor
          rw [le_div_iff₀ hδ]
          exact hm
        have hmK' : (m : ℝ) ≤ K := by exact_mod_cast hmK
        have hup : ∀ i, ys i 1 ≤ U' := fun i =>
          (hU _ (hys i) (le_trans hxB.1 (hge i))).trans (le_max_left _ _)
        have hU0 : 0 ≤ U' := le_max_right _ _
        refine Set.mem_biUnion (x := m) (Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega))) ?_
        refine ⟨ys, fun i => ⟨hys i, (hboxmem _).mpr ⟨⟨le_trans hxB.1 (hge i), hneg i⟩,
          ?_, hup i⟩⟩, rfl⟩
        -- lower bound on the output of each plan
        have hrest : ∑ j ∈ Finset.univ.erase i, ys j 1 ≤ m * U' := by
          calc ∑ j ∈ Finset.univ.erase i, ys j 1 ≤ ∑ _j ∈ Finset.univ.erase i, U' :=
                Finset.sum_le_sum fun j _ => hup j
            _ = m * U' := by
                rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i)]
                simp
        have hsplit : ∑ j, ys j 1 = ys i 1 + ∑ j ∈ Finset.univ.erase i, ys j 1 :=
          (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
        have h1 := hxB.2
        rw [hsum1, hsplit] at h1
        have : (m : ℝ) * U' ≤ K * U' := mul_le_mul_of_nonneg_right hmK' hU0
        rw [hlo]
        linarith
      · rintro ⟨hx, hxB⟩
        refine ⟨?_, hxB⟩
        obtain ⟨m, -, hm⟩ := Set.mem_iUnion₂.mp hx
        obtain ⟨ys, hys, rfl⟩ := hm
        exact b4_sum_mem_addClosure m ys fun i => (hys i).1
    rw [heq]
    refine IsClosed.inter ?_ hRc
    exact isClosed_biUnion_finset fun m _ => hTc m
  -- closedness from the boxes
  refine isClosed_of_closure_subset fun x hx => ?_
  set B := max (-x 0) (-x 1) + 1 with hB
  set O : Set (Fin 2 → ℝ) := {v | -B < v 0 ∧ -B < v 1} with hO
  have hOo : IsOpen O :=
    (isOpen_lt continuous_const (continuous_apply 0)).inter
      (isOpen_lt continuous_const (continuous_apply 1))
  have hxO : x ∈ O := ⟨by rw [hB]; linarith [le_max_left (-x 0) (-x 1)],
    by rw [hB]; linarith [le_max_right (-x 0) (-x 1)]⟩
  have h1 := hOo.inter_closure ⟨hxO, hx⟩
  have h2 : closure (O ∩ addClosure Y) ⊆ addClosure Y ∩ {x | -B ≤ x 0 ∧ -B ≤ x 1} := by
    refine (hbox B).closure_subset_iff.mpr ?_
    rintro v ⟨hvO, hv⟩
    exact ⟨hv, hvO.1.le, hvO.2.le⟩
  exact (h2 h1).1

/-- The S-shaped technology `{y : y₁ ≤ 0, y₂ ≤ min(y₁², 1)}` of Figure 5.B.5(b). -/
def sTech : Set (Fin 2 → ℝ) := {y | y 0 ≤ 0 ∧ y 1 ≤ min (y 0 ^ 2) 1}

/-- **Exercise 5.B.4** (MWG, p. 160), Figure 5.B.5(b): the S-shaped technology
`{y₁ ≤ 0, y₂ ≤ min(y₁², 1)}` is closed, allows inaction, violates nonincreasing returns
(`(-1, 1) ∈ Y` but `(-1/2, 1/2) ∉ Y`), satisfies the hypotheses of `exercise_5_B_4_closed`
(with `δ = 1/2`), and its additive closure `Y⁺` is closed. -/
theorem exercise_5_B_4_closed_instance :
    IsClosed sTech ∧ InactionPossible sTech ∧ ¬ NonincreasingReturns sTech ∧
      (∀ y ∈ sTech, y 0 ≤ 0) ∧ (∀ B : ℝ, ∃ U : ℝ, ∀ y ∈ sTech, -B ≤ y 0 → y 1 ≤ U) ∧
      (∀ y ∈ sTech, ∀ y' ∈ sTech, -(1 / 2) < y 0 → -(1 / 2) < y' 0 → y + y' ∈ sTech) ∧
      IsClosed (addClosure sTech) := by
  have hcl : IsClosed sTech :=
    (isClosed_le (continuous_apply 0) continuous_const).inter
      (isClosed_le (continuous_apply 1) (((continuous_apply 0).pow 2).min continuous_const))
  have hin : ∀ y ∈ sTech, y 0 ≤ 0 := fun y hy => hy.1
  have hbdd : ∀ B : ℝ, ∃ U : ℝ, ∀ y ∈ sTech, -B ≤ y 0 → y 1 ≤ U :=
    fun _ => ⟨1, fun y hy _ => hy.2.trans (min_le_right _ _)⟩
  have hmerge : ∀ y ∈ sTech, ∀ y' ∈ sTech, -(1 / 2) < y 0 → -(1 / 2) < y' 0 →
      y + y' ∈ sTech := by
    intro y hy y' hy' h h'
    refine ⟨by simp only [Pi.add_apply]; linarith [hy.1, hy'.1], ?_⟩
    simp only [Pi.add_apply]
    have a := hy.2.trans (min_le_left _ _)
    have b := hy'.2.trans (min_le_left _ _)
    have hprod : 0 ≤ y 0 * y' 0 := mul_nonneg_of_nonpos_of_nonpos hy.1 hy'.1
    refine le_min (by nlinarith) ?_
    have : (y 0 + y' 0) ^ 2 < 1 := by nlinarith [hy.1, hy'.1]
    nlinarith
  refine ⟨hcl, ⟨le_rfl, by simp⟩, fun hnirs => ?_, hin, hbdd, hmerge,
    exercise_5_B_4_closed hcl hin hbdd (by norm_num) hmerge⟩
  have hmem : (![-1, 1] : Fin 2 → ℝ) ∈ sTech := ⟨by simp, by simp⟩
  have := hnirs _ hmem (1 / 2) (by norm_num) (by norm_num)
  have h2 := this.2
  simp at h2
  norm_num at h2

end MWG.Production
