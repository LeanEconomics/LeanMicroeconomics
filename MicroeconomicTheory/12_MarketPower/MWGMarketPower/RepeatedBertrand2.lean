/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGMarketPower.RepeatedBertrand

/-!
# Proposition 12.D.2: no collusion when `δ < 1/2`

MWG, Proposition 12.D.2 (second part) and its small-type proof, pp. 403-404.

`proposition_12_D_2_part2`: in the infinitely repeated Bertrand duopoly with `δ < 1/2`, along
the outcome path of any SPNE (from any history), the lowest price is `c` in every period, so all
sales take place at a price equal to cost.

The proof follows MWG: a firm can always secure `0` from any period on (price `c`), and can earn
almost the whole industry profit `π_t` by undercutting in period `t` (12.D.3); adding over the
two firms gives `2π_t ≤ v_{1t} + v_{2t} ≤ π̄/(1 − δ)` with `π̄ = sup π_t`, impossible for
`π̄ > 0` and `δ < 1/2`. MWG's argument stops at "`π_t ≤ 0` for all `t`"; to conclude that sales
occur at the price `c` we add: then every firm earns `0` in every period, so the lowest price
cannot be below `c` (a loss) nor above `c` (a profitable deviation would exist).
-/

namespace MWG.MarketPower

open MWG.DynamicGames Function Filter Topology Set

theorem osPath_succ' {I : Type*} {A : I → Type*} (σ : OSProfile A) (h : OSHist A) (n : ℕ) :
    osPath σ h (n + 1) = osPlay σ (osPath σ h n) :: osPath σ h n := by
  induction n generalizing h with
  | zero => rfl
  | succ n ih =>
    change osPath σ (osPlay σ h :: h) (n + 1) = _
    rw [ih]
    rfl

/-- Duopoly profits with `R(a) = (a − c)x(a)`: the strictly lowest-priced firm earns `R`. -/
theorem duopoly_profit_lt (x : ℝ → ℝ) (c : ℝ) (q : Fin 2 → ℝ) {j k : Fin 2} (hk : k ≠ j)
    (h : q j < q k) : bertrandProfit x c q j = (q j - c) * x (q j) := by
  have hall : ∀ l : Fin 2, l = j ∨ l = k := by
    intro l; fin_cases j <;> fin_cases k <;> fin_cases l <;> simp_all
  unfold bertrandProfit
  rw [bertrandSales_of_lt fun l hl => by rcases hall l with rfl | rfl; exacts [absurd rfl hl, h]]

/-- At a tie each firm earns `R/2`. -/
theorem duopoly_profit_eq (x : ℝ → ℝ) (c : ℝ) (q : Fin 2 → ℝ) {j k : Fin 2} (hk : k ≠ j)
    (h : q j = q k) : bertrandProfit x c q j = (q j - c) * x (q j) / 2 := by
  have hall : ∀ l : Fin 2, l = j ∨ l = k := by
    intro l; fin_cases j <;> fin_cases k <;> fin_cases l <;> simp_all
  unfold bertrandProfit bertrandSales
  have hmin : ∀ l, q j ≤ q l := fun l => by rcases hall l with rfl | rfl <;> simp [h]
  have hcard : (Finset.univ.filter fun l => q l = q j) = Finset.univ := by
    ext l; rcases hall l with rfl | rfl <;> simp [h]
  simp only [hmin, implies_true, ↓reduceIte, hcard]
  simp; ring

/-- The higher-priced firm earns nothing. -/
theorem duopoly_profit_gt (x : ℝ → ℝ) (c : ℝ) (q : Fin 2 → ℝ) {j k : Fin 2}
    (h : q k < q j) : bertrandProfit x c q j = 0 := by
  unfold bertrandProfit
  rw [bertrandSales_of_gt (k := k) h, mul_zero]

/-- **Proposition 12.D.2, second part** (MWG, pp. 403-404). In the infinitely repeated Bertrand
duopoly with `c > 0`, `x(c) > 0` and `δ < 1/2`, along the outcome path of any SPNE `σ` starting
from any history, the lowest price in every period equals `c`. -/
theorem proposition_12_D_2_part2 {x : ℝ → ℝ} {pbar δ : ℝ} (hx : IsBertrandDemand x pbar)
    (cc : Ici (0 : ℝ)) (hc : 0 < (cc : ℝ)) (hxc : 0 < x cc) (hpbar : 0 ≤ pbar) (hδ0 : 0 ≤ δ)
    (hδ : δ < 1 / 2) {σ : OSProfile (fun _ : Fin 2 => Ici (0 : ℝ))}
    (hσ : IsRepeatedSPNE (bertrandStage (ι := Fin 2) x cc) δ σ) (h : OSHist _) (t : ℕ) :
    min ((osPlay σ (osPath σ h t) 0 : ℝ)) (osPlay σ (osPath σ h t) 1) = cc := by
  classical
  set g := bertrandStage (ι := Fin 2) x cc with hgdef
  have hδ1 : δ < 1 := by linarith
  have h1δ : 0 < 1 - δ := by linarith
  set M := (pbar + cc) * x 0 with hM
  have hg : ∀ j p, |g j p| ≤ M := bertrandStage_bound hx cc.2 hpbar
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hg 0 (fun _ => cc))
  set P : ℕ → Fin 2 → Ici (0 : ℝ) := fun t => osPlay σ (osPath σ h t) with hP
  set V : Fin 2 → ℕ → ℝ := fun j t => osValue (stageU g) δ σ (osPath σ h t) j with hV
  have hrec : ∀ j t, V j t = g j (P t) + δ * V j (t + 1) := by
    intro j t
    simp only [hV, hP]
    rw [osValue_succ hδ0 hδ1 (stageU_bound hg) σ _ j, osPath_succ']
    rfl
  have hVb : ∀ j t, |V j t| ≤ M / (1 - δ) := fun j t =>
    osValue_abs_le hδ0 hδ1 (stageU_bound hg) σ _ j
  -- a firm pricing at `c` earns nothing
  have hzero : ∀ j (p : Fin 2 → Ici (0 : ℝ)), g j (update p j cc) = 0 := by
    intro j p; simp [hgdef, bertrandStage, bertrandProfit]
  -- deviating in period `t` to `a` and charging `c` afterwards
  have hdev : ∀ j t (a : Ici (0 : ℝ)), g j (update (P t) j a) ≤ V j t := by
    intro j t a
    set H := osPath σ h t with hH
    set τ : OSHist (fun _ : Fin 2 => Ici (0 : ℝ)) → Ici (0 : ℝ) :=
      fun h' => if h' = H then a else cc with hτ
    have hs := hσ j τ H
    rw [osValue_succ hδ0 hδ1 (stageU_bound hg) _ H j, osPlay_update] at hs
    have hτH : τ H = a := by simp [hτ]
    rw [hτH] at hs
    have hW : osValue (stageU g) δ (update σ j τ) (update (osPlay σ H) j a :: H) j = 0 := by
      unfold osValue
      have : ∀ n, δ ^ n * stageU g j
          (osPath (update σ j τ) (update (osPlay σ H) j a :: H) n)
          (osPlay (update σ j τ) (osPath (update σ j τ) (update (osPlay σ H) j a :: H) n)) =
          0 := by
        intro n
        rw [osPlay_update]
        have hne : osPath (update σ j τ) (update (osPlay σ H) j a :: H) n ≠ H := by
          intro heq
          have := congrArg List.length heq
          rw [osPath_length, List.length_cons] at this
          omega
        have : τ (osPath (update σ j τ) (update (osPlay σ H) j a :: H) n) = cc := by
          simp only [hτ]
          exact ite_eq_right_iff.mpr fun h' => absurd h' hne
        rw [this]
        simp only [stageU, hzero, mul_zero]
      simp [this]
    rw [hW, mul_zero, add_zero] at hs
    exact hs
  have hV0 : ∀ j t, 0 ≤ V j t := fun j t => by
    have := hdev j t cc; rwa [hzero] at this
  set R : ℝ → ℝ := fun a => (a - cc) * x a with hR
  have hRc : Continuous R := (continuous_id.sub continuous_const).mul hx.cont
  set m : ℕ → ℝ := fun t => min ((P t 0 : ℝ)) (P t 1) with hm
  have hother : ∀ j : Fin 2, ∃ k, k ≠ j ∧ ∀ l : Fin 2, l = j ∨ l = k := by
    intro j; fin_cases j
    · exact ⟨1, by decide, fun l => by fin_cases l <;> decide⟩
    · exact ⟨0, by decide, fun l => by fin_cases l <;> decide⟩
  -- industry profit `π_t = R(m_t)` and each firm's profit
  have hfirm : ∀ j t, g j (P t) = R (m t) ∨ g j (P t) = R (m t) / 2 ∨ g j (P t) = 0 := by
    intro j t
    have h10 : (1 : Fin 2) ≠ 0 := by decide
    have h01 : (0 : Fin 2) ≠ 1 := by decide
    simp only [hgdef, bertrandStage]
    rcases (show j = 0 ∨ j = 1 by fin_cases j <;> simp) with rfl | rfl
    · rcases lt_trichotomy ((P t 0 : ℝ)) (P t 1) with h1 | h1 | h1
      · left; rw [duopoly_profit_lt x cc _ h10 h1]; simp only [hm, hR, min_eq_left h1.le]
      · right; left; rw [duopoly_profit_eq x cc _ h10 h1]; simp only [hm, hR, h1, min_self]
      · right; right; exact duopoly_profit_gt x cc _ h1
    · rcases lt_trichotomy ((P t 1 : ℝ)) (P t 0) with h1 | h1 | h1
      · left; rw [duopoly_profit_lt x cc _ h01 h1]; simp only [hm, hR, min_eq_right h1.le]
      · right; left; rw [duopoly_profit_eq x cc _ h01 h1]; simp only [hm, hR, h1, min_self]
      · right; right; exact duopoly_profit_gt x cc _ h1
  have hπ : ∀ t, g 0 (P t) + g 1 (P t) = R (m t) := by
    intro t
    have h10 : (1 : Fin 2) ≠ 0 := by decide
    have h01 : (0 : Fin 2) ≠ 1 := by decide
    simp only [hgdef, bertrandStage]
    rcases lt_trichotomy ((P t 0 : ℝ)) (P t 1) with h1 | h1 | h1
    · rw [duopoly_profit_lt x cc _ h10 h1, duopoly_profit_gt x cc _ h1, hm]
      simp only [min_eq_left h1.le, hR]; ring
    · rw [duopoly_profit_eq x cc _ h10 h1, duopoly_profit_eq x cc _ h01 h1.symm, hm]
      simp only [h1, min_self, hR]; ring
    · rw [duopoly_profit_gt x cc _ h1, duopoly_profit_lt x cc _ h01 h1, hm]
      simp only [min_eq_right h1.le, hR]; ring
  -- (12.D.3): each firm earns at least `π_t`
  have hER : ∀ j t, R (m t) ≤ V j t := by
    intro j t
    obtain ⟨k, hk, hall⟩ := hother j
    have hm0 : 0 ≤ m t := le_min (P t 0).2 (P t 1).2
    rcases eq_or_lt_of_le hm0 with h0 | h0
    · rw [← h0]; simp only [hR, zero_sub]
      nlinarith [hx.nonneg 0, hV0 j t]
    · have hlim : Tendsto R (𝓝[<] (m t)) (𝓝 (R (m t))) :=
        hRc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      refine le_of_tendsto hlim ?_
      filter_upwards [Ioo_mem_nhdsLT h0] with a ha
      have hlow : ∀ l, l ≠ j → (update (P t) j ⟨a, ha.1.le⟩ j : ℝ) <
          (update (P t) j ⟨a, ha.1.le⟩ l : ℝ) := by
        intro l hl
        rw [update_self, update_of_ne hl]
        exact lt_of_lt_of_le ha.2 (by
          rcases hall l with rfl | rfl
          · exact absurd rfl hl
          · fin_cases l <;> simp [hm])
      have := hdev j t ⟨a, ha.1.le⟩
      simp only [hgdef, bertrandStage] at this
      unfold bertrandProfit at this
      rw [bertrandSales_of_lt hlow] at this
      simpa [hR] using this
  -- `π_t ≤ 0` for all `t`
  have hπbd : ∀ t, R (m t) ≤ 2 * M := fun t => by
    rw [← hπ t]; linarith [(abs_le.1 (hg 0 (P t))).2, (abs_le.1 (hg 1 (P t))).2]
  set U := ⨆ t, R (m t) with hU
  have hbdd : BddAbove (Set.range fun t => R (m t)) := ⟨2 * M, fun _ ⟨t, ht⟩ => ht ▸ hπbd t⟩
  have hSU : ∀ t, V 0 t + V 1 t ≤ U / (1 - δ) := by
    have hgap : ∀ n t, V 0 t + V 1 t - U / (1 - δ) ≤
        δ ^ n * (2 * (M / (1 - δ)) + |U| / (1 - δ)) := by
      intro n
      induction n with
      | zero =>
        intro t
        have h0 := abs_le.1 (hVb 0 t); have h1 := abs_le.1 (hVb 1 t)
        have : -(|U| / (1 - δ)) ≤ U / (1 - δ) := by
          rw [← neg_div]; exact div_le_div_of_nonneg_right (neg_abs_le U) h1δ.le
        rw [pow_zero, one_mul]; linarith
      | succ n ih =>
        intro t
        have hπU : R (m t) ≤ U := le_ciSup hbdd t
        rw [hrec 0 t, hrec 1 t]
        have := ih (t + 1)
        have e : U / (1 - δ) = U + δ * (U / (1 - δ)) := by field_simp; ring
        have h2 := hπ t
        rw [pow_succ]
        nlinarith [mul_le_mul_of_nonneg_left this hδ0]
    intro t
    have ht : Tendsto (fun n : ℕ => δ ^ n * (2 * (M / (1 - δ)) + |U| / (1 - δ))) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hδ0 hδ1).mul_const _
    have := ge_of_tendsto ht (Eventually.of_forall fun n => hgap n t)
    linarith
  have hU0 : U ≤ 0 := by
    have h2U : 2 * U ≤ U / (1 - δ) := by
      rw [show 2 * U = ⨆ t, 2 * R (m t) by
        rw [Real.mul_iSup_of_nonneg (by norm_num)]]
      refine ciSup_le fun t => ?_
      have := hER 0 t; have := hER 1 t; have := hSU t; linarith
    rw [le_div_iff₀ h1δ] at h2U
    nlinarith
  have hπ0 : ∀ t, R (m t) ≤ 0 := fun t => (le_ciSup hbdd t).trans hU0
  -- every firm earns `0` in every period
  have hg0 : ∀ j t, g j (P t) ≤ 0 := by
    intro j t
    rcases hfirm j t with h | h | h <;> rw [h] <;> linarith [hπ0 t]
  have hVle : ∀ j t, V j t ≤ 0 := by
    intro j
    have hgap : ∀ n t, V j t ≤ δ ^ n * (M / (1 - δ)) := by
      intro n
      induction n with
      | zero => intro t; rw [pow_zero, one_mul]; exact (le_abs_self _).trans (hVb j t)
      | succ n ih =>
        intro t
        rw [hrec j t, pow_succ]
        nlinarith [hg0 j t, mul_le_mul_of_nonneg_left (ih (t + 1)) hδ0]
    intro t
    have ht : Tendsto (fun n : ℕ => δ ^ n * (M / (1 - δ))) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hδ0 hδ1).mul_const _
    exact ge_of_tendsto ht (Eventually.of_forall fun n => hgap n t)
  have hVz : ∀ j t, V j t = 0 := fun j t => le_antisymm (hVle j t) (hV0 j t)
  have hgz : ∀ j t, g j (P t) = 0 := fun j t => by
    have := hrec j t; rw [hVz, hVz] at this; linarith
  -- the lowest price is `c`
  change m t = cc
  rcases lt_trichotomy (m t) cc with hlt | heq | hgt
  · exfalso
    have hxm : 0 < x (m t) := by
      by_contra hn; push Not at hn
      linarith [hx.strictAnti _ _ hlt hxc, hx.nonneg (m t)]
    have hRneg : (m t - cc) * x (m t) < 0 := mul_neg_of_neg_of_pos (by linarith) hxm
    -- the lowest-priced firm sells at a loss
    have h10 : (1 : Fin 2) ≠ 0 := by decide
    have h01 : (0 : Fin 2) ≠ 1 := by decide
    have hg00 := hgz 0 t
    have hg01 := hgz 1 t
    simp only [hgdef, bertrandStage] at hg00 hg01
    rcases lt_trichotomy ((P t 0 : ℝ)) (P t 1) with h1 | h1 | h1
    · rw [duopoly_profit_lt x cc _ h10 h1] at hg00
      have : m t = (P t 0 : ℝ) := min_eq_left h1.le
      rw [← this] at hg00; linarith
    · rw [duopoly_profit_eq x cc _ h10 h1] at hg00
      have : m t = (P t 0 : ℝ) := by rw [hm]; simp [h1]
      rw [← this] at hg00; linarith
    · rw [duopoly_profit_lt x cc _ h01 h1] at hg01
      have : m t = (P t 1 : ℝ) := min_eq_right h1.le
      rw [← this] at hg01; linarith
  · exact heq
  · exfalso
    obtain ⟨a, hac, ham, hgain⟩ := bertrand_deviation hx hxc hgt
    have hRm : 0 ≤ R (m t) := mul_nonneg (by linarith) (hx.nonneg _)
    have ha0 : 0 ≤ a := by linarith
    have hlow : ∀ l, l ≠ (0 : Fin 2) → (update (P t) 0 ⟨a, ha0⟩ 0 : ℝ) <
        (update (P t) 0 ⟨a, ha0⟩ l : ℝ) := by
      intro l hl
      rw [update_self, update_of_ne hl]
      have : l = 1 := by
        rcases (show l = 0 ∨ l = 1 by fin_cases l <;> simp) with h | h
        · exact absurd h hl
        · exact h
      subst this
      exact lt_of_lt_of_le ham (min_le_right _ _)
    have := hdev 0 t ⟨a, ha0⟩
    simp only [hgdef, bertrandStage] at this
    unfold bertrandProfit at this
    rw [bertrandSales_of_lt hlow, hVz] at this
    simp only [update_self] at this
    linarith

end MWG.MarketPower
