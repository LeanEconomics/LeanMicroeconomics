/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGMarketPower.Bertrand
import MWGMarketPower.NashReversion

/-!
# Repeated interaction: the infinitely repeated Bertrand game

MWG, Section 12.D, pp. 400-405, and Exercise 12.D.2.

The stage game is the Bertrand game of Section 12.C with `J` firms (`ι`), prices restricted to
`p ≥ 0` (so that per-period profits are bounded; prices are nonnegative in MWG's model anyway),
and the repeated game is that of Appendix A (`RepeatedGames`). The Nash reversion strategies
(12.D.1) for a price `p` are `nashReversion (fun _ => p̂) ĉ`: charge `p` as long as everybody
always has, and `c` otherwise.

* `bertrandStage_nash`: all firms charging `c` is a stage Nash equilibrium.
* `bertrand_nashReversion_iff`: if `p > c`, `x(p) > 0` and no lower price earns more than `p`
  (`(a − c)x(a) ≤ (p − c)x(p)` for `a < p`), then Nash reversion sustains `p` iff
  `δ ≥ (J − 1)/J`.
* `proposition_12_D_1`: the strategies (12.D.1) with the monopoly price are an SPNE iff
  `δ ≥ 1/2`.
* `exercise_12_D_2_corrected`, `proposition_12_D_2_part1_corrected`.
* `proposition_12_D_2_counterexample`, `exercise_12_D_2_counterexample` (correction): a demand
  for which the price `2 ∈ (c, pᵐ)` cannot be sustained by Nash reversion at `δ = 1/2`, because
  a lower price earns more than `2`; Proposition 12.D.2's first part and Exercise 12.D.2 assume
  implicitly that profit `(p − c)x(p)` increases up to `pᵐ`.
-/

namespace MWG.MarketPower

open MWG.DynamicGames Function Filter Topology Set

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Bertrand stage game with nonnegative prices. -/
noncomputable def bertrandStage (x : ℝ → ℝ) (c : ℝ) (j : ι) (p : ι → Ici (0 : ℝ)) : ℝ :=
  bertrandProfit x c (fun k => (p k : ℝ)) j

/-- The constant price profile. -/
def constPrice (ι : Type*) (p : Ici (0 : ℝ)) : ι → Ici (0 : ℝ) := fun _ => p

omit [DecidableEq ι] in
/-- Per-period profits are bounded: `|(p − c)x_j| ≤ (p̄ + c)x(0)` for `p ≥ 0`. -/
theorem bertrandStage_bound {x : ℝ → ℝ} {pbar c : ℝ} (hx : IsBertrandDemand x pbar)
    (hc : 0 ≤ c) (hpbar : 0 ≤ pbar) :
    ∀ j (p : ι → Ici (0 : ℝ)), |bertrandStage x c j p| ≤ (pbar + c) * x 0 := by
  intro j p
  unfold bertrandStage bertrandProfit
  have hs0 := bertrandSales_nonneg hx.nonneg (fun k => (p k : ℝ)) j
  have hsx := bertrandSales_le hx.nonneg (fun k => (p k : ℝ)) j
  have hp0 : 0 ≤ (p j : ℝ) := (p j).2
  have hx0 : x (p j) ≤ x 0 := by
    rcases eq_or_lt_of_le hp0 with h | h
    · rw [← h]
    · rcases eq_or_lt_of_le (hx.nonneg (p j)) with h' | h'
      · rw [← h']; exact hx.nonneg 0
      · exact (hx.strictAnti 0 _ h h').le
  rcases le_or_gt pbar (p j) with h | h
  · rw [hx.zero _ h] at hsx
    have : bertrandSales x (fun k => (p k : ℝ)) j = 0 := le_antisymm hsx hs0
    rw [this, mul_zero, abs_zero]
    exact mul_nonneg (by linarith) (hx.nonneg 0)
  · rw [abs_mul, abs_of_nonneg hs0]
    have h1 : |(p j : ℝ) - c| ≤ pbar + c := by rw [abs_le]; constructor <;> linarith
    exact mul_le_mul h1 (hsx.trans hx0) hs0 (by linarith)

/-- All firms charging `c` is a Nash equilibrium of the stage game (any number of firms
`J ≥ 2`; Proposition 12.C.1). -/
theorem bertrandStage_nash {x : ℝ → ℝ} {pbar : ℝ} (hx : IsBertrandDemand x pbar)
    (cc : Ici (0 : ℝ)) (h2 : 2 ≤ Fintype.card ι) :
    IsStageNash (bertrandStage (ι := ι) x cc) (constPrice ι cc) := by
  intro j a
  have h0 : bertrandStage x cc j (constPrice ι cc) = 0 := by
    simp [bertrandStage, bertrandProfit, constPrice]
  rw [h0]
  unfold bertrandStage
  rcases le_or_gt (a : ℝ) cc with h | h
  · exact bertrandProfit_le_zero hx.nonneg (by simpa using h)
  · obtain ⟨k, hk⟩ := Fintype.exists_ne_of_one_lt_card (by omega) j
    unfold bertrandProfit
    rw [bertrandSales_of_gt (k := k) (by simpa [constPrice, update_of_ne hk] using h), mul_zero]

/-- The profit of a firm undercutting all rivals' common price, or matching it. -/
theorem bertrandStage_update {x : ℝ → ℝ} {c : ℝ} (p a : Ici (0 : ℝ)) (j : ι)
    (h2 : 2 ≤ Fintype.card ι) :
    ((a : ℝ) < p → bertrandStage x c j (update (constPrice ι p) j a) = (a - c) * x a) ∧
    ((p : ℝ) < a → bertrandStage x c j (update (constPrice ι p) j a) = 0) ∧
    bertrandStage x c j (constPrice ι p) = (p - c) * (x p / Fintype.card ι) := by
  refine ⟨fun h => ?_, fun h => ?_, ?_⟩
  · unfold bertrandStage bertrandProfit
    rw [bertrandSales_of_lt (fun k hk => by simpa [constPrice, update_of_ne hk] using h)]
    simp
  · obtain ⟨k, hk⟩ := Fintype.exists_ne_of_one_lt_card (by omega) j
    unfold bertrandStage bertrandProfit
    rw [bertrandSales_of_gt (k := k) (by simpa [constPrice, update_of_ne hk] using h), mul_zero]
  · unfold bertrandStage bertrandProfit bertrandSales
    simp [constPrice]

/-- **Nash reversion in the repeated Bertrand game** (MWG, pp. 401-405). Let `J ≥ 2`,
`c ≥ 0`, `p > c` with `x(p) > 0`, and suppose no lower price earns more than `p`:
`(a − c)x(a) ≤ (p − c)x(p)` for `0 ≤ a < p`. Then the Nash reversion strategies that charge `p`
are an SPNE iff `δ ≥ (J − 1)/J`. -/
theorem bertrand_nashReversion_iff {x : ℝ → ℝ} {pbar δ : ℝ} (hx : IsBertrandDemand x pbar)
    (cc p : Ici (0 : ℝ)) (hpbar : 0 ≤ pbar) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (h2 : 2 ≤ Fintype.card ι) (hpc : (cc : ℝ) < p) (hxp : 0 < x p)
    (hmax : ∀ a : ℝ, 0 ≤ a → a < p → (a - cc) * x a ≤ (p - cc) * x p) :
    IsRepeatedSPNE (bertrandStage (ι := ι) x cc) δ
        (nashReversion (fun _ => constPrice ι p) (constPrice ι cc)) ↔
      ((Fintype.card ι : ℝ) - 1) / Fintype.card ι ≤ δ := by
  set J : ℝ := (Fintype.card ι : ℝ) with hJ
  have hJ2 : (2 : ℝ) ≤ J := by rw [hJ]; exact_mod_cast h2
  have hJ0 : 0 < J := by linarith
  have h1δ : 0 < 1 - δ := by linarith
  set R := ((p : ℝ) - cc) * x p with hR
  have hRpos : 0 < R := mul_pos (by linarith) hxp
  rw [nashReversion_spne_iff hδ0 hδ1 (bertrandStage_bound hx cc.2 hpbar) _
    (bertrandStage_nash hx cc h2)]
  have hc0 : ∀ j, bertrandStage (ι := ι) x cc j (constPrice ι cc) = 0 := fun j => by
    simp [bertrandStage, bertrandProfit, constPrice]
  have hpv : ∀ j t, pathValue (bertrandStage (ι := ι) x cc) δ (fun _ => constPrice ι p) t j =
      R / J / (1 - δ) := fun j t => by
    rw [pathValue_const _ hδ0 hδ1, (bertrandStage_update p p j h2).2.2]
    rw [hR]; ring
  simp only [hc0, zero_div, mul_zero, add_zero, hpv]
  -- the condition says every deviation earns at most `R/(J(1 − δ))`
  have hkey : R / J / (1 - δ) ≥ R ↔ (J - 1) / J ≤ δ := by
    rw [ge_iff_le, le_div_iff₀ h1δ, div_le_iff₀ hJ0, le_div_iff₀ hJ0]
    constructor
    · intro h; nlinarith
    · intro h; nlinarith
  constructor
  · intro h
    rw [← hkey]
    -- deviations just below `p` earn almost `R`
    by_contra hlt
    push Not at hlt
    have hcont : ContinuousAt (fun a : ℝ => (a - cc) * x a) p :=
      ((continuous_id.sub continuous_const).mul hx.cont).continuousAt
    have hev : ∀ᶠ a in 𝓝 (p : ℝ), R / J / (1 - δ) < (a - cc) * x a :=
      hcont.eventually (lt_mem_nhds hlt)
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
    set a : ℝ := max ((p : ℝ) - ε / 2) ((cc + p) / 2) with ha
    have hap : a < p := max_lt (by linarith) (by linarith)
    have hcc0 : (0 : ℝ) ≤ cc := cc.2
    have ha0 : 0 ≤ a := le_trans (by linarith) (le_max_right _ _)
    have hdist : dist a p < ε := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [le_max_left ((p : ℝ) - ε / 2) ((cc + p) / 2)]
    obtain ⟨j⟩ : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
    have hne : (⟨a, ha0⟩ : Ici (0 : ℝ)) ≠ constPrice ι p j := by
      intro heq; have := congrArg Subtype.val heq; simp [constPrice] at this; linarith
    have := h 0 j ⟨a, ha0⟩ hne
    rw [(bertrandStage_update p ⟨a, ha0⟩ j h2).1 hap] at this
    linarith [hball hdist]
  · intro hδ t j a ha
    have hRle := (hkey.2 hδ)
    rcases lt_trichotomy (a : ℝ) p with h | h | h
    · rw [(bertrandStage_update p a j h2).1 h]
      linarith [hmax a a.2 h]
    · exact absurd (Subtype.ext h) (by simpa [constPrice] using ha)
    · rw [(bertrandStage_update p a j h2).2.1 h]
      exact div_nonneg (div_nonneg hRpos.le hJ0.le) h1δ.le

/-- **Proposition 12.D.1** (MWG, p. 401). In the infinitely repeated Bertrand duopoly, the
Nash reversion strategies (12.D.1) with the monopoly price `pᵐ` (a maximizer of `(p − c)x(p)`
with `pᵐ > c`, `x(pᵐ) > 0`) constitute an SPNE if and only if `δ ≥ 1/2`. -/
theorem proposition_12_D_1 {x : ℝ → ℝ} {pbar δ : ℝ} (hx : IsBertrandDemand x pbar)
    (cc pm : Ici (0 : ℝ)) (hpbar : 0 ≤ pbar) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hpc : (cc : ℝ) < pm) (hxp : 0 < x pm)
    (hmono : ∀ a : ℝ, 0 ≤ a → (a - cc) * x a ≤ (pm - cc) * x pm) :
    IsRepeatedSPNE (bertrandStage (ι := Fin 2) x cc) δ
        (nashReversion (fun _ => constPrice (Fin 2) pm) (constPrice (Fin 2) cc)) ↔ 1 / 2 ≤ δ := by
  rw [bertrand_nashReversion_iff hx cc pm hpbar hδ0 hδ1 (by simp) hpc hxp
    (fun a ha _ => hmono a ha)]
  norm_num

/-- **Exercise 12.D.2, corrected** (MWG, p. 405). With `J ≥ 2` firms, repeated choice of a price
`p ∈ (c, pᵐ]` with `x(p) > 0` is sustained as a stationary SPNE outcome path with Nash reversion
iff `δ ≥ (J − 1)/J`, provided no lower price earns more than `p` (true for `p = pᵐ`, and for all
`p ∈ (c, pᵐ]` when `(p − c)x(p)` is nondecreasing on `[0, pᵐ]`). More firms make collusion
harder to sustain: `(J − 1)/J` increases with `J`. -/
theorem exercise_12_D_2_corrected {x : ℝ → ℝ} {pbar δ : ℝ} (hx : IsBertrandDemand x pbar)
    (cc p : Ici (0 : ℝ)) (hpbar : 0 ≤ pbar) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (h2 : 2 ≤ Fintype.card ι) (hpc : (cc : ℝ) < p) (hxp : 0 < x p)
    (hmono : MonotoneOn (fun a : ℝ => (a - cc) * x a) (Icc 0 p)) :
    (IsRepeatedSPNE (bertrandStage (ι := ι) x cc) δ
        (nashReversion (fun _ => constPrice ι p) (constPrice ι cc)) ↔
      ((Fintype.card ι : ℝ) - 1) / Fintype.card ι ≤ δ) ∧
    StrictMono (fun J : ℕ => ((J : ℝ) + 1 - 1) / ((J : ℝ) + 1)) := by
  refine ⟨bertrand_nashReversion_iff hx cc p hpbar hδ0 hδ1 h2 hpc hxp
    fun a ha hap => hmono ⟨ha, hap.le⟩ ⟨le_trans cc.2 hpc.le, le_rfl⟩ hap.le, ?_⟩
  intro m n hmn
  have : (m : ℝ) < n := by exact_mod_cast hmn
  simp only [add_sub_cancel_right]
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- **Proposition 12.D.2, first part, corrected** (MWG, p. 403). With `δ ≥ 1/2`, repeated choice
of any price `p ∈ (c, pᵐ]` with `x(p) > 0` can be supported by Nash reversion if `(p − c)x(p)` is
nondecreasing on `[0, p]` (the price `c` is the repeated stage equilibrium). -/
theorem proposition_12_D_2_part1_corrected {x : ℝ → ℝ} {pbar δ : ℝ}
    (hx : IsBertrandDemand x pbar) (cc p : Ici (0 : ℝ)) (hpbar : 0 ≤ pbar) (hδ : 1 / 2 ≤ δ)
    (hδ1 : δ < 1) (hpc : (cc : ℝ) < p) (hxp : 0 < x p)
    (hmono : MonotoneOn (fun a : ℝ => (a - cc) * x a) (Icc 0 p)) :
    IsRepeatedSPNE (bertrandStage (ι := Fin 2) x cc) δ
      (nashReversion (fun _ => constPrice (Fin 2) p) (constPrice (Fin 2) cc)) := by
  refine ((exercise_12_D_2_corrected hx cc p hpbar (by linarith) hδ1 (by simp) hpc hxp
    hmono).1).2 ?_
  norm_num; linarith

/-- The demand of the counterexample (`c = 1`): `x(p) = 19 − 9p` for `p ≤ 2`,
`(102 − p)/100` for `2 ≤ p ≤ 102`, and `0` above. Profit `(p − 1)x(p)` has a local peak
`25/9` at `p = 14/9` and its global maximum at `pᵐ = 103/2`; at `p = 2` it is only `1`. -/
noncomputable def cexDemand (p : ℝ) : ℝ :=
  if p ≤ 2 then 19 - 9 * p else if p ≤ 102 then (102 - p) / 100 else 0

theorem cexDemand_isBertrand : IsBertrandDemand cexDemand 102 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold cexDemand
    refine Continuous.if_le (by fun_prop) ?_ continuous_id continuous_const ?_
    · refine Continuous.if_le (by fun_prop) continuous_const continuous_id continuous_const ?_
      intro p hp; rw [hp]; norm_num
    · intro p hp; rw [hp]; norm_num
  · intro p; unfold cexDemand
    split_ifs
    · linarith
    · exact div_nonneg (by linarith) (by norm_num)
    · exact le_rfl
  · intro p p' hpp' hpos
    unfold cexDemand at hpos ⊢
    split_ifs at hpos ⊢ <;> linarith
  · intro p hp; unfold cexDemand
    split_ifs <;> linarith

/-- The cost `c = 1` of the counterexample, as a nonnegative price. -/
def cexC1 : Ici (0 : ℝ) := ⟨1, by norm_num⟩

/-- The price `p = 2` of the counterexample. -/
def cexP2 : Ici (0 : ℝ) := ⟨2, by norm_num⟩

/-- **Proposition 12.D.2 and Exercise 12.D.2 are false as printed** (MWG, pp. 403 and 405;
correction). With `c = 1` and the demand `cexDemand`, the monopoly price is `pᵐ = 103/2`, the
price `p = 2 ∈ (c, pᵐ]` has `x(2) = 1 > 0`, and `δ = 1/2 ≥ (J − 1)/J` for `J = 2`; yet repeated
choice of `p = 2` is not sustained by Nash reversion, since undercutting to `14/9` earns
`25/9 > 1 = (p − c)x(p)/(2(1 − δ))`. -/
theorem proposition_12_D_2_counterexample :
    (∀ a : ℝ, 0 ≤ a → (a - 1) * cexDemand a ≤ (103 / 2 - 1) * cexDemand (103 / 2)) ∧
    0 < cexDemand 2 ∧
    ¬ IsRepeatedSPNE (bertrandStage (ι := Fin 2) cexDemand cexC1) (1 / 2)
      (nashReversion (fun _ => constPrice (Fin 2) cexP2) (constPrice (Fin 2) cexC1)) := by
  refine ⟨fun a ha => ?_, by norm_num [cexDemand], fun h => ?_⟩
  · have hm : (103 / 2 - 1) * cexDemand (103 / 2) = 10201 / 400 := by norm_num [cexDemand]
    rw [hm]
    unfold cexDemand
    split_ifs
    · nlinarith [sq_nonneg (a - 14 / 9)]
    · nlinarith [sq_nonneg (a - 103 / 2)]
    · norm_num
  · rw [nashReversion_spne_iff (δ := 1 / 2) (by norm_num) (by norm_num)
      (bertrandStage_bound cexDemand_isBertrand cexC1.2 (by norm_num)) _
      (bertrandStage_nash cexDemand_isBertrand cexC1 (by simp))] at h
    have hdev := h 0 0 ⟨14 / 9, by norm_num⟩ (by
      intro heq; have := congrArg Subtype.val heq
      simp [constPrice, cexP2] at this; norm_num at this)
    rw [(bertrandStage_update (c := cexC1) (x := cexDemand) cexP2 ⟨14 / 9, by norm_num⟩
      0 (by simp)).1 (by norm_num [cexP2]), pathValue_const _ (by norm_num) (by norm_num),
      (bertrandStage_update (c := cexC1) (x := cexDemand) cexP2 cexP2 0 (by simp)).2.2] at hdev
    have h1 : bertrandStage (ι := Fin 2) cexDemand cexC1 0 (constPrice (Fin 2) cexC1) = 0 := by
      simp [bertrandStage, bertrandProfit, constPrice]
    rw [h1] at hdev
    norm_num [cexDemand, cexC1, cexP2] at hdev

end MWG.MarketPower
