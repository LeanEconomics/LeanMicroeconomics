/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGAdverseSelection.GameTheoretic
import MWGAdverseSelection.Uniform

/-!
# Market unraveling: Example 13.B.1, and the counterexample to Proposition 13.B.1(i)

MWG, Section 13.B, pp. 442-445.

* `example_13_B_1`: with `r(θ) = αθ` (`0 < α < 1`) and `θ` uniform on `[0, 2]`,
  `E[θ | r(θ) ≤ w] = w/(2α)` for `0 < w ≤ 2α`; for `α > 1/2`, `E[θ | r(θ) ≤ 0] = 0` and
  `E[θ | r(θ) ≤ w] < w` for every `w > 0`, so `W* = {0}`: complete market failure (Figure 13.B.2).
  Akerlof's case `α = 2/3` (footnote 10) is `example_13_B_1_akerlof`. Proposition 13.B.1(ii)
  applies (`example_13_B_1_spne`).
* `example_13_B_1_lowα`: for `α < 1/2`, `W* = {0, 1}` with `Max W* = 1 > r(θ̲)`, an instance of
  Proposition 13.B.1(i) (`proposition_13_B_1_i_instance`).
* `counterexample_13_B_1_i` (correction 2): Proposition 13.B.1(i) fails when `r` is strictly
  increasing but discontinuous.
-/

namespace MWG.AdverseSelection

open MeasureTheory Set MWG.SimultaneousMoveGames

/-- **Example 13.B.1** (MWG, p. 442). The home-production function `r(θ) = αθ`. -/
def akerlofR (α : ℝ) : ℝ → ℝ := fun θ => α * θ

theorem acceptSet_akerlofR {α : ℝ} (hα : 0 < α) (w : ℝ) :
    acceptSet (akerlofR α) w = Iic (w / α) := by
  ext θ
  simp only [acceptSet, akerlofR, mem_ofPred_eq, mem_Iic, le_div_iff₀ hα]
  rw [mul_comm]

/-- **Example 13.B.1** (MWG, p. 442). The model with `r(θ) = αθ`, `0 < α < 1`, and `θ` uniform on
`[0, 2]` satisfies the assumptions of p. 441. -/
theorem akerlof_regular {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    RegularModel (unifMeas 0 2) 0 2 (akerlofR α) where
  dist := unifMeas_typeDist le_rfl two_pos
  dens := unifMeas_density two_pos
  meas := measurable_const.mul measurable_id
  mono := fun a _ b _ hab => mul_lt_mul_of_pos_left hab hα
  cont := (continuous_const.mul continuous_id).continuousOn
  le := fun θ hθ => by simp only [akerlofR]; nlinarith [hθ.1]

/-- **Example 13.B.1** (MWG, p. 442). `E[θ | r(θ) ≤ w] = w/(2α)` for `0 < w ≤ 2α`. -/
theorem example_13_B_1 {α w : ℝ} (hα : 0 < α) (hw : 0 < w) (hw2 : w ≤ 2 * α) :
    condMean (unifMeas 0 2) 0 2 (acceptSet (akerlofR α) w) = w / (2 * α) := by
  have hc0 : 0 ≤ w / α := (div_pos hw hα).le
  have hc2 : w / α ≤ 2 := (div_le_iff₀ hα).2 (by linarith)
  have hcpos : 0 < w / α := div_pos hw hα
  rw [acceptSet_akerlofR hα]
  have hμ := unifMeas_Iic (a := 0) (b := 2) two_pos hc0 hc2
  have hpos : 0 < unifMeas 0 2 (Iic (w / α)) := by
    rw [hμ]; exact ENNReal.ofReal_pos.2 (by positivity)
  simp only [condMean, hpos, ↓reduceIte]
  rw [unifMeas_setIntegral_Iic two_pos hc0 hc2, hμ, ENNReal.toReal_ofReal (by positivity)]
  have hw0 : w ≠ 0 := hw.ne'
  field_simp
  rw [div_eq_iff (by simpa using hw0)]
  ring

/-- **Example 13.B.1** (MWG, p. 442). `E[θ | r(θ) ≤ 0] = 0`. -/
theorem example_13_B_1_zero {α : ℝ} (hα : 0 < α) :
    condMean (unifMeas 0 2) 0 2 (acceptSet (akerlofR α) 0) = 0 := by
  rw [acceptSet_akerlofR hα, zero_div]
  have h0 : unifMeas 0 2 (Iic 0) = 0 := by
    rw [unifMeas_Iic two_pos le_rfl zero_le_two]; simp
  have hne : (Iic (0 : ℝ) ∩ Icc 0 2).Nonempty := ⟨0, by simp⟩
  simp only [condMean, h0, lt_self_iff_false, ↓reduceIte, hne]

/-- **Example 13.B.1** (MWG, p. 442). Above `2α` every type accepts, so
`E[θ | r(θ) ≤ w] = E[θ] = 1`. -/
theorem example_13_B_1_high {α w : ℝ} (hα : 0 < α) (hw : 2 * α ≤ w) :
    condMean (unifMeas 0 2) 0 2 (acceptSet (akerlofR α) w) = 1 := by
  rw [condMean_of_superset (unifMeas_typeDist le_rfl two_pos), unifMeas_mean two_pos]
  · norm_num
  · intro θ hθ
    simp only [acceptSet, akerlofR, mem_ofPred_eq]
    nlinarith [hθ.1, hθ.2]

/-- **Example 13.B.1** (MWG, p. 442). For `α > 1/2`, `E[θ | r(θ) ≤ w] < w` for all `w > 0`. -/
theorem example_13_B_1_lt {α w : ℝ} (hα : 1 / 2 < α) (hw : 0 < w) :
    condMean (unifMeas 0 2) 0 2 (acceptSet (akerlofR α) w) < w := by
  have hα0 : 0 < α := by linarith
  rcases le_or_gt w (2 * α) with h | h
  · rw [example_13_B_1 hα0 hw h, div_lt_iff₀ (by linarith)]
    nlinarith
  · rw [example_13_B_1_high hα0 h.le]; linarith

/-- **Example 13.B.1, Figure 13.B.2** (MWG, p. 442). For `1/2 < α < 1` the only competitive
equilibrium wage is `w* = θ̲ = 0`: the market unravels completely. -/
theorem example_13_B_1_unravel {α : ℝ} (hα : 1 / 2 < α) :
    eqWages (unifMeas 0 2) 0 2 (akerlofR α) = {0} := by
  have hα0 : 0 < α := by linarith
  ext w
  rw [mem_eqWages_iff, mem_singleton_iff]
  constructor
  · intro h
    rcases lt_trichotomy w 0 with hw | hw | hw
    · have hne : ¬ (acceptSet (akerlofR α) w ∩ Icc 0 2).Nonempty := by
        rintro ⟨θ, h1, h2⟩
        simp only [acceptSet, akerlofR, mem_ofPred_eq] at h1
        nlinarith [h2.1]
      have h0 : unifMeas 0 2 (acceptSet (akerlofR α) w) = 0 := by
        rw [← measure_acceptSet_inter (unifMeas_typeDist le_rfl two_pos),
          not_nonempty_iff_eq_empty.1 hne, measure_empty]
      simp only [condMean, h0, lt_self_iff_false, ↓reduceIte, hne, unifMeas_mean two_pos] at h
      linarith
    · exact hw
    · exact absurd h (example_13_B_1_lt hα hw).ne'
  · rintro rfl; exact (example_13_B_1_zero hα0).symm

/-- **Footnote 10** (MWG, p. 442). Akerlof's case `α = 2/3`. -/
theorem example_13_B_1_akerlof : eqWages (unifMeas 0 2) 0 2 (akerlofR (2 / 3)) = {0} :=
  example_13_B_1_unravel (by norm_num)

/-- **Example 13.B.1 with Proposition 13.B.1(ii)** (MWG, pp. 442-445). For `1/2 < α < 1` the
pure SPNE of the wage game are exactly the pairs of wages `≤ 0`. -/
theorem example_13_B_1_spne {α : ℝ} (hα : 1 / 2 < α) (hα1 : α < 1) (w : Fin 2 → ℝ) :
    IsNashEquilibrium (wageGame (firmProfit (unifMeas 0 2) (akerlofR α))) w ↔
      w 0 ≤ 0 ∧ w 1 ≤ 0 := by
  refine proposition_13_B_1_ii (akerlof_regular (by linarith) hα1) ?_ (by simp [akerlofR]) w
  rw [example_13_B_1_unravel hα]
  exact ⟨rfl, fun x hx => le_of_eq hx⟩

/-- **Example 13.B.1, `α < 1/2`** (MWG, pp. 442-443). Then `W* = {0, 1}`. -/
theorem example_13_B_1_lowα {α : ℝ} (hα : 0 < α) (hα2 : α < 1 / 2) :
    eqWages (unifMeas 0 2) 0 2 (akerlofR α) = {0, 1} := by
  ext w
  rw [mem_eqWages_iff, mem_insert_iff, mem_singleton_iff]
  constructor
  · intro h
    rcases lt_trichotomy w 0 with hw | hw | hw
    · exfalso
      have hne : ¬ (acceptSet (akerlofR α) w ∩ Icc 0 2).Nonempty := by
        rintro ⟨θ, h1, h2⟩
        simp only [acceptSet, akerlofR, mem_ofPred_eq] at h1
        nlinarith [h2.1]
      have h0 : unifMeas 0 2 (acceptSet (akerlofR α) w) = 0 := by
        rw [← measure_acceptSet_inter (unifMeas_typeDist le_rfl two_pos),
          not_nonempty_iff_eq_empty.1 hne, measure_empty]
      simp only [condMean, h0, lt_self_iff_false, ↓reduceIte, hne, unifMeas_mean two_pos] at h
      linarith
    · exact Or.inl hw
    · right
      rcases le_or_gt w (2 * α) with h2 | h2
      · rw [example_13_B_1 hα hw h2] at h
        exfalso
        have : w * (2 * α) = w := by field_simp at h; linarith
        nlinarith
      · rw [example_13_B_1_high hα h2.le] at h; exact h
  · rintro (rfl | rfl)
    · exact (example_13_B_1_zero hα).symm
    · exact (example_13_B_1_high hα (by linarith)).symm

/-- **Proposition 13.B.1(i), an instance** (MWG, pp. 442-444). With `r(θ) = αθ`, `0 < α < 1/2`,
and `θ` uniform on `[0, 2]`, `w* = 1` and the unique pure SPNE has both firms offering `1`. -/
theorem proposition_13_B_1_i_instance {α : ℝ} (hα : 0 < α) (hα2 : α < 1 / 2) (w : Fin 2 → ℝ) :
    IsNashEquilibrium (wageGame (firmProfit (unifMeas 0 2) (akerlofR α))) w ↔
      w 0 = 1 ∧ w 1 = 1 := by
  refine proposition_13_B_1_i (akerlof_regular hα (by linarith)) ?_ (by simp [akerlofR])
    one_pos ?_ w
  · rw [example_13_B_1_lowα hα hα2]
    refine ⟨by simp, fun x hx => ?_⟩
    rcases hx with rfl | rfl <;> norm_num
  · intro w' h1 h2
    have hw' : 0 < w' := by linarith
    rcases le_or_gt w' (2 * α) with h | h
    · rw [example_13_B_1 hα hw' h, lt_div_iff₀ (by linarith)]
      nlinarith
    · rw [example_13_B_1_high hα h.le]; exact h2

end MWG.AdverseSelection

namespace MWG.AdverseSelection

open MeasureTheory Set MWG.SimultaneousMoveGames

/-- Correction 2: a strictly increasing, discontinuous home-production function on `[1, 2]`:
`r(θ) = 0` for `θ ≤ 1` and `r(θ) = θ` for `θ > 1`. -/
noncomputable def jumpR : ℝ → ℝ := fun θ => if θ ≤ 1 then 0 else θ

theorem jumpR_inter_subset {w : ℝ} (hw : w ≤ 1) : acceptSet jumpR w ∩ Icc 1 2 ⊆ {1} := by
  rintro θ ⟨h1, h2⟩
  simp only [acceptSet, jumpR, mem_ofPred_eq] at h1
  split_ifs at h1 with h
  · exact le_antisymm h h2.1
  · exact absurd (h1.trans hw) h

theorem jumpR_null {w : ℝ} (hw : w ≤ 1) : unifMeas 1 2 (acceptSet jumpR w) = 0 := by
  rw [← measure_acceptSet_inter (unifMeas_typeDist zero_le_one one_lt_two)]
  exact measure_mono_null (jumpR_inter_subset hw) ((unifMeas_density one_lt_two).noAtom 1)

theorem jumpR_meas : Measurable jumpR :=
  Measurable.ite measurableSet_Iic measurable_const measurable_id

theorem jumpR_profit_neg {w : ℝ} (hw : 1 < w) : firmProfit (unifMeas 1 2) jumpR w < 0 := by
  have hd := unifMeas_typeDist zero_le_one one_lt_two
  have hden := unifMeas_density one_lt_two
  have hpos : 0 < unifMeas 1 2 (acceptSet jumpR w) := by
    refine (hden.pos 1 (min w 2) le_rfl (lt_min hw one_lt_two) (min_le_right _ _)).trans_le
      (measure_mono fun θ hθ => ?_)
    simp only [acceptSet, jumpR, mem_ofPred_eq]
    split_ifs
    · linarith
    · exact hθ.2.trans (min_le_left _ _)
  refine firmProfit_neg_of_ae_lt hd jumpR_meas hpos ?_
  have hne : ∀ᵐ θ ∂(unifMeas 1 2), θ ≠ w := by
    have : unifMeas 1 2 {w} = 0 := hden.noAtom w
    exact measure_eq_zero_iff_ae_notMem.1 this |>.mono fun _ h => h
  filter_upwards [hd.ae_mem, hne] with θ hθ hθw hm
  simp only [acceptSet, jumpR, mem_ofPred_eq] at hm
  split_ifs at hm with h
  · linarith
  · exact lt_of_le_of_ne hm hθw

/-- **Proposition 13.B.1(i) is false without continuity of `r`** (correction 2; MWG,
pp. 443-444). Types uniform on `[1, 2]` (positive density), `r = jumpR` strictly increasing with
`r(θ) ≤ θ`, `W* = {1}` so `w* = 1 > r(θ̲) = 0`, and `E[θ | r(θ) ≤ w'] > w'` on `(0, 1)`. Yet
both firms offering `1/2` is a pure SPNE, so the SPNE is not unique and need not pay `w*`. -/
theorem counterexample_13_B_1_i :
    TypeDist (unifMeas 1 2) 1 2 ∧ HasPosDensity (unifMeas 1 2) 1 2 ∧ Measurable jumpR ∧
      StrictMonoOn jumpR (Icc 1 2) ∧ (∀ θ ∈ Icc (1 : ℝ) 2, jumpR θ ≤ θ) ∧
      IsGreatest (eqWages (unifMeas 1 2) 1 2 jumpR) 1 ∧ jumpR 1 < 1 ∧
      (∀ w', 1 - 1 < w' → w' < 1 → w' < condMean (unifMeas 1 2) 1 2 (acceptSet jumpR w')) ∧
      IsNashEquilibrium (wageGame (firmProfit (unifMeas 1 2) jumpR)) ![1 / 2, 1 / 2] ∧
      ¬ ((![1 / 2, 1 / 2] : Fin 2 → ℝ) 0 = 1) := by
  have hd := unifMeas_typeDist zero_le_one one_lt_two
  -- below `1` only the null type `1` accepts
  have hcm : ∀ w, 0 ≤ w → w ≤ 1 → condMean (unifMeas 1 2) 1 2 (acceptSet jumpR w) = 1 := by
    intro w h0 h1
    have hne : (acceptSet jumpR w ∩ Icc 1 2).Nonempty :=
      ⟨1, by simp [acceptSet, jumpR, h0], by norm_num⟩
    simp only [condMean, jumpR_null h1, lt_self_iff_false, ↓reduceIte, hne]
  refine ⟨hd, unifMeas_density one_lt_two, jumpR_meas, ?_, ?_, ⟨?_, ?_⟩, by norm_num [jumpR],
    ?_, ?_, by norm_num⟩
  · intro a ha b hb hab
    simp only [jumpR]
    split_ifs with h1 h2 h2 <;> linarith [hb.1, ha.1]
  · intro θ hθ
    simp only [jumpR]; split_ifs <;> linarith [hθ.1]
  · rw [mem_eqWages_iff, hcm 1 zero_le_one le_rfl]
  · intro w hw
    by_contra hlt
    rw [not_le] at hlt
    have hpos : 0 < unifMeas 1 2 (acceptSet jumpR w) := by
      by_contra h0
      have h0' : unifMeas 1 2 (acceptSet jumpR w) = 0 := le_antisymm (not_lt.1 h0) bot_le
      exact (jumpR_profit_neg hlt).ne (firmProfit_of_null jumpR_meas h0')
    exact (jumpR_profit_neg hlt).ne ((mem_eqWages_iff_profit hd jumpR_meas hpos).1 hw)
  · intro w' h1 h2
    rw [hcm w' (by linarith) h2.le]; exact h2
  · refine (wageGame_flat (ws := 1) (fun t ht => firmProfit_of_null jumpR_meas (jumpR_null ht))
      (fun t ht => jumpR_profit_neg ht) _).2 ?_
    norm_num

end MWG.AdverseSelection
