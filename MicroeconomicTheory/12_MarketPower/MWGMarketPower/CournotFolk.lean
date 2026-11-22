/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGMarketPower.StickCarrot
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Order.Field

/-!
# Example 12.AA.1: an average payoff of zero in the repeated Cournot game

MWG, Example 12.AA.1, pp. 422-423, with footnotes 36-37.

The stage game is the Cournot duopoly with unit cost `c > 0`, nonincreasing inverse demand `p`,
and (footnote 36) quantities in a compact interval `[0, B]` (`cfG`). With `π(q) = (p(2q) − c)q`
for symmetric outputs, the strategies are: play `q̄` in period 1 and `qᵐ` afterwards; a deviation
when `q̄` is due restarts; a deviation when `qᵐ` is due triggers Nash reversion. Here
(12.AA.7) `π(q̄) + δπ(qᵐ)/(1 − δ) = 0`.

* `example_12_AA_1`: if `q̄ ≥ q_c` (`p(q_c) ≤ c`, so that a best response to `q̄` earns `0`),
  the strategies form an SPNE (using Chapter 9's one-shot deviation principle, footnote 37)
  with average payoff `0` for both firms.
* `example_12_AA_1_qbar`: for `δ` close to `1` such a `q̄ ≥ q_c` exists (when `p(x) → 0`).
* `example_12_AA_1_instance`: `p(x) = max(4 − x, 0)`, `c = 1`, `B = 11`, `δ = 9/10`.
-/

namespace MWG.MarketPower

open MWG.DynamicGames Function Filter Topology Set

/-- The Cournot duopoly with quantities in `[0, B]` (MWG, p. 422 and footnote 36). -/
def cfG (p : ℝ → ℝ) (c B : ℝ) (i : Fin 2) (q : Fin 2 → Icc (0 : ℝ) B) : ℝ :=
  (p ((q 0 : ℝ) + q 1) - c) * q i

theorem cfG_update_sum {B : ℝ} (x : Icc (0 : ℝ) B) (i : Fin 2) (a : Icc (0 : ℝ) B) :
    ((update (fun _ => x) i a 0 : ℝ) + update (fun _ => x) i a 1) = a + x := by
  fin_cases i <;> simp [update, add_comm]

theorem cfG_update_own {B : ℝ} (x : Icc (0 : ℝ) B) (i : Fin 2) (a : Icc (0 : ℝ) B) :
    (update (fun _ => x) i a i : ℝ) = a := by simp

/-- **Example 12.AA.1** (MWG, pp. 422-423). Let `c > 0`, `p` nonincreasing on `[0, ∞)` with
`p(q_c) ≤ c` and `|p| ≤ P` on `[0, 2B]`, `q*` a stage Nash equilibrium, `q̄ ≥ q_c`, and
(12.AA.7) `π(q̄) + δπ(qᵐ)/(1 − δ) = 0`. If Nash reversion deters deviations from `qᵐ`, the
stick-and-carrot strategies are an SPNE in which both firms earn an average payoff of `0`. -/
theorem example_12_AA_1 {p : ℝ → ℝ} {c B δ qc P : ℝ} (hc : 0 < c) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hanti : AntitoneOn p (Ici 0)) (hqc : 0 ≤ qc) (hpqc : p qc ≤ c)
    (hP : ∀ x ∈ Icc (0 : ℝ) (2 * B), |p x| ≤ P) (qs : Fin 2 → Icc (0 : ℝ) B)
    (hqs : IsStageNash (cfG p c B) qs) (qbar qm : Icc (0 : ℝ) B) (hqbar : qc ≤ qbar)
    (h7 : cfG p c B 0 (fun _ => qbar) + δ / (1 - δ) * cfG p c B 0 (fun _ => qm) = 0)
    (hdet : ∀ i a, a ≠ qm → cfG p c B i (update (fun _ => qm) i a) +
      δ * (cfG p c B i qs / (1 - δ)) ≤ cfG p c B i (fun _ => qm) / (1 - δ)) :
    IsRepeatedSPNE (cfG p c B) δ (scProfile (fun _ => qbar) (fun _ => qm) qs 2) ∧
      ∀ i, (1 - δ) * osValue (stageU (cfG p c B)) δ
        (scProfile (fun _ => qbar) (fun _ => qm) qs 2) [] i = 0 := by
  have h1δ : (1 - δ) ≠ 0 := by linarith
  have hsym : ∀ (x : Icc (0 : ℝ) B) i, cfG p c B i (fun _ => x) = cfG p c B 0 (fun _ => x) := by
    intro x i; fin_cases i <;> rfl
  have hB : ∀ i x, |cfG p c B i x| ≤ (P + c) * B := by
    intro i x
    unfold cfG
    have hx0 := (x 0).2
    have hx1 := (x 1).2
    have hxi := (x i).2
    have hp := hP ((x 0 : ℝ) + x 1) ⟨by linarith [hx0.1, hx1.1], by linarith [hx0.2, hx1.2]⟩
    rw [abs_mul, abs_of_nonneg hxi.1]
    have h1 : |p ((x 0 : ℝ) + x 1) - c| ≤ P + c := by
      refine (abs_sub _ _).trans ?_
      rw [abs_of_pos hc]; linarith
    exact mul_le_mul h1 hxi.2 hxi.1 ((abs_nonneg _).trans h1)
  obtain ⟨hspne, hval⟩ := scProfile_spne hδ0 hδ1 hB (fun _ => qbar) (fun _ => qm) qs 2 hqs
    (fun i a => by
      -- a best response to `q̄ ≥ q_c` earns at most `0`
      have hle : cfG p c B i (update (fun _ => qbar) i a) ≤ 0 := by
        unfold cfG
        rw [cfG_update_sum, cfG_update_own]
        have ha := a.2
        have hle : p ((a : ℝ) + qbar) ≤ c :=
          (hanti (mem_Ici.2 hqc) (mem_Ici.2 (by linarith [ha.1])) (by linarith [ha.1])).trans
            hpqc
        exact mul_nonpos_of_nonpos_of_nonneg (by linarith) ha.1
      have : (1 - δ) * cfG p c B i (fun _ => qbar) + δ * cfG p c B i (fun _ => qm) = 0 := by
        rw [hsym, hsym qm]
        have := congrArg (fun z => (1 - δ) * z) h7
        simp only [mul_zero] at this
        rw [← this]; field_simp
      linarith)
    (fun i a ha => by simpa [scVal] using hdet i a ha)
  refine ⟨hspne, fun i => ?_⟩
  rw [hval]
  rw [hsym, hsym qm]
  have := congrArg (fun z => (1 - δ) * z) h7
  simp only [mul_zero] at this
  rw [← this]; field_simp

/-- **Example 12.AA.1, existence of the stick** (MWG, p. 423). Let `c > 0`, `p` continuous,
nonincreasing on `[0, ∞)` with `p(x) → 0`, `q_c ≥ 0`, and `π(qᵐ) > 0`. There is `δ_c < 1` such
that for all `δ ∈ (δ_c, 1)` some `q̄ ≥ q_c` solves (12.AA.7):
`(p(2q̄) − c)q̄ + δπ(qᵐ)/(1 − δ) = 0`. -/
theorem example_12_AA_1_qbar {p : ℝ → ℝ} {c qc πm : ℝ} (hc : 0 < c)
    (hcont : ContinuousOn p (Ici 0)) (hanti : AntitoneOn p (Ici 0))
    (hlim : Tendsto p atTop (𝓝 0)) (hqc : 0 ≤ qc) (hπm : 0 < πm) :
    ∃ δc < 1, ∀ δ, δc < δ → δ < 1 →
      ∃ qbar, qc ≤ qbar ∧ (p (2 * qbar) - c) * qbar + δ / (1 - δ) * πm = 0 := by
  -- `p ≥ 0` on `[0, ∞)`
  have hp0 : ∀ x, 0 ≤ x → 0 ≤ p x := by
    intro x hx
    refine le_of_tendsto hlim ?_
    filter_upwards [eventually_ge_atTop x] with y hy
    exact hanti (mem_Ici.2 hx) (mem_Ici.2 (hx.trans hy)) hy
  obtain ⟨X, hX⟩ := eventually_atTop.1 (hlim.eventually (gt_mem_nhds (by linarith : 0 < c / 2)))
  refine ⟨c * qc / (c * qc + πm), (div_lt_one (by positivity)).2 (by linarith),
    fun δ hδ hδ1 => ?_⟩
  have h1δ : 0 < 1 - δ := by linarith
  set T := δ / (1 - δ) * πm with hT
  have hTq : c * qc ≤ T := by
    rw [div_lt_iff₀ (by positivity)] at hδ
    rw [hT, div_mul_eq_mul_div, le_div_iff₀ h1δ]
    nlinarith
  have hT0 : 0 ≤ T := le_trans (by positivity) hTq
  set Q := max (max qc (|X| / 2)) (2 * T / c) + 1 with hQ
  have hQqc : qc ≤ Q := by
    have := le_max_left (max qc (|X| / 2)) (2 * T / c)
    have := le_max_left qc (|X| / 2); linarith
  have hQX : X ≤ 2 * Q := by
    have := le_max_right qc (|X| / 2)
    have := le_max_left (max qc (|X| / 2)) (2 * T / c)
    have := le_abs_self X; linarith
  have hQT : 2 * T / c ≤ Q := by have := le_max_right (max qc (|X| / 2)) (2 * T / c); linarith
  set f : ℝ → ℝ := fun q => (p (2 * q) - c) * q with hf
  have hfc : ContinuousOn f (Icc qc Q) := by
    refine ContinuousOn.mul (ContinuousOn.sub ?_ continuousOn_const) continuousOn_id
    exact hcont.comp (continuousOn_const.mul continuousOn_id) fun x hx => by
      simp only [mem_Ici]; nlinarith [hx.1]
  have hfQ : f Q ≤ -T := by
    have hpQ := hX (2 * Q) hQX
    have hQ0 : 0 ≤ Q := hqc.trans hQqc
    have : (p (2 * Q) - c) * Q ≤ -(c / 2) * Q := mul_le_mul_of_nonneg_right (by linarith) hQ0
    have : T ≤ c / 2 * Q := by
      have := (div_le_iff₀ hc).1 hQT; linarith
    simp only [hf]; linarith
  have hfqc : -T ≤ f qc := by
    have := hp0 (2 * qc) (by linarith)
    simp only [hf]; nlinarith
  obtain ⟨qbar, hqbar, hfq⟩ := intermediate_value_Icc' hQqc hfc ⟨hfQ, hfqc⟩
  exact ⟨qbar, hqbar.1, by simp only [hf] at hfq; linarith⟩

/-- The inverse demand `p(x) = max(4 − x, 0)` of the instance. -/
noncomputable def pLin4 (x : ℝ) : ℝ := max (4 - x) 0

/-- **Example 12.AA.1, an instance.** With `p(x) = max(4 − x, 0)`, `c = 1`, quantities in
`[0, 11]` and `δ = 9/10`: the Cournot equilibrium is `q* = (1, 1)`, `qᵐ = 3/4` (half the
monopoly output), and `q̄ = 81/8 ≥ q_c = 3` solves (12.AA.7); the stick-and-carrot strategies
are an SPNE with average payoff `0`. -/
theorem example_12_AA_1_instance :
    let qs : Fin 2 → Icc (0 : ℝ) 11 := fun _ => ⟨1, by norm_num, by norm_num⟩
    let qbar : Icc (0 : ℝ) 11 := ⟨81 / 8, by norm_num, by norm_num⟩
    let qm : Icc (0 : ℝ) 11 := ⟨3 / 4, by norm_num, by norm_num⟩
    IsRepeatedSPNE (cfG pLin4 1 11) (9 / 10) (scProfile (fun _ => qbar) (fun _ => qm) qs 2) ∧
      ∀ i, (1 - 9 / 10) * osValue (stageU (cfG pLin4 1 11)) (9 / 10)
        (scProfile (fun _ => qbar) (fun _ => qm) qs 2) [] i = 0 := by
  intro qs qbar qm
  have hanti : AntitoneOn pLin4 (Ici 0) := fun x _ y _ hxy => by
    unfold pLin4; exact max_le_max (by linarith) le_rfl
  have hqs_val : ∀ i, cfG pLin4 1 11 i qs = 1 := by
    intro i; fin_cases i <;> norm_num [cfG, qs, pLin4]
  have hqs : IsStageNash (cfG pLin4 1 11) qs := by
    intro i a
    rw [hqs_val]
    have hsum : ((update qs i a 0 : ℝ) + update qs i a 1) = a + 1 := cfG_update_sum _ i a
    unfold cfG
    rw [hsum, cfG_update_own]
    have ha := a.2
    unfold pLin4
    rcases le_total (4 - ((a : ℝ) + 1)) 0 with h | h
    · rw [max_eq_right h]; nlinarith [ha.1]
    · rw [max_eq_left h]; nlinarith [sq_nonneg ((a : ℝ) - 1)]
  refine example_12_AA_1 (qc := 3) (P := 4) (by norm_num) (by norm_num) (by norm_num) hanti
    (by norm_num) (by norm_num [pLin4]) (fun x hx => ?_) qs hqs qbar qm (by norm_num [qbar])
    (by norm_num [cfG, qbar, qm, pLin4]) (fun i a _ => ?_)
  · unfold pLin4
    rw [abs_le]
    constructor
    · exact le_trans (by norm_num) (le_max_right _ _)
    · exact max_le (by linarith [hx.1]) (by norm_num)
  · rw [hqs_val]
    have hqm : cfG pLin4 1 11 i (fun _ => qm) = 9 / 8 := by
      fin_cases i <;> norm_num [cfG, qm, pLin4]
    rw [hqm]
    have hsum : ((update (fun _ => qm) i a 0 : ℝ) + update (fun _ => qm) i a 1) = a + 3 / 4 :=
      cfG_update_sum _ i a
    unfold cfG
    rw [hsum, cfG_update_own]
    have ha := a.2
    unfold pLin4
    rcases le_total (4 - ((a : ℝ) + 3 / 4)) 0 with h | h
    · rw [max_eq_right h]; nlinarith [ha.1]
    · rw [max_eq_left h]; nlinarith [sq_nonneg ((a : ℝ) - 9 / 8)]

end MWG.MarketPower
