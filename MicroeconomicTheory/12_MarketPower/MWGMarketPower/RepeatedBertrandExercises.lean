/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGMarketPower.FiniteRepeatedBertrand
import Mathlib.Topology.Order.IntermediateValue

/-!
# Repeated Bertrand exercises: cost changes and Rotemberg-Saloner

MWG, Exercises 12.D.4 and 12.D.5, p. 434.

The stage game is the Bertrand duopoly with prices `p ≥ 0` (`bertrandStage`); `R(p) = (p − c)x(p)`
is the profit of a firm serving the whole market.

**Exercise 12.D.4** (`δ ∈ [1/2, 1)`; we treat the duopoly, the case in which `δ ≥ 1/2` is the
threshold of Proposition 12.D.1).
* (a) `exercise_12_D_4a`: after a (permanent) change of the cost to `c'`, the monopoly price
  `pᵐ(c')` at the new cost is sustained by Nash reversion and no stationary price earns more, so
  it is the most profitable sustainable price; `exercise_12_D_4a_monotone`: `pᵐ(c)` is weakly
  increasing in `c`.
* (b) The cost is `c₁` in period 1 and `c₂` from period 2 on. The game is Chapter 9's multi-stage
  game with per-period payoffs depending on the period (`costChangeU`); the profile
  `costChangeProfile p₁ p₂` is Nash reversion along the path `(p₁, p₂, p₂, …)` with reversion to
  `c₂`. `costChange_spne_iff`: with `p₂ = pᵐ(c₂)` (the most profitable continuation, by (a)) it is
  an SPNE iff no period-1 deviation pays against the continuation value `Γ/2`, where
  `Γ = δR₂(pᵐ(c₂))/(1 − δ)`. `exercise_12_D_4b`: a price `p₁ ∈ (c₁, pᵐ(c₁)]` is sustainable iff
  `R₁(p₁) ≤ Γ`; if `Γ ≥ R₁(pᵐ(c₁))` the period-1 monopoly price is sustainable, and otherwise the
  maximal sustainable period-1 price is the `p̂ ∈ (c₁, pᵐ(c₁))` with `R₁(p̂) = Γ`, strictly below
  the period-1 monopoly price; `exercise_12_D_4b_compare`: a cost increase lowers the monopoly
  profit, so at `δ = 1/2` the second case always obtains. Instance: `exercise_12_D_4b_instance`.

**Exercise 12.D.5** (Rotemberg and Saloner). Demand is `x(p)` with probability `λ` and `αx(p)`
with probability `1 − λ`, i.i.d. across periods and observed before prices are set. Nash
reversion with state-contingent prices `(p_H, p_L)` (`IsRSNashReversion`) is formalized by its
one-shot deviation conditions: in state `s`, following earns `π_s(p_s)/2 + δV` where
`V = [λπ_H(p_H)/2 + (1 − λ)π_L(p_L)/2]/(1 − δ)` is the expected value from the next period
(`rsValue`); a deviation to `a` earns the stage profit from `a` and then zero (reversion to `c`,
whose stage profits are zero in both states); after a deviation, `c` must be a stage Nash
equilibrium in both states. Reduction: with bounded payoffs and `δ ∈ [0, 1)`, the one-shot
deviation principle (Chapter 9, `oneShot_deviation_principle_discounted_iff`, whose proof
carries over verbatim to i.i.d. states with expected continuation values) makes these conditions
equivalent to subgame perfection of the Nash reversion profile in the stochastic game; the
stochastic game itself is not built here.
* (a) `exercise_12_D_5a`: for `δ ≥ δ̂ = 1/(1 + λ + (1 − λ)α)`, `p_H = p_L = pᵐ` is an SPNE.
* (b) `exercise_12_D_5b`: `1/2 < δ̂ < 1`; for `δ < δ̂` charging `pᵐ` in the high state is never
  sustainable (whatever `p_L`); for `δ ∈ [1/2, δ̂)` the highest sustainable `p_H` with
  `p_L = pᵐ` is the `p̂ ∈ (c, pᵐ)` with `R(p̂) = δ(1 − λ)αR(pᵐ)/(1 − δ(1 + λ))`, and
  `(p̂, pᵐ)` is sustainable: prices are countercyclical, `p_H < p_L`.
* (c) `exercise_12_D_5c`: for `δ < 1/2` every Nash reversion profile of this form has
  `p_H = p_L = c`. (The book's claim concerns these strategies; we prove it for all of them.)
Instances: `exercise_12_D_5_instance`.
-/

namespace MWG.MarketPower

open MWG.DynamicGames Function Filter Topology Set

/-- If every price `a ∈ [0, p)` earns at most `B`, so does `p` (continuity from the left). -/
theorem rbx_le_of_below {x : ℝ → ℝ} (hx : Continuous x) {c p B : ℝ} (hc : 0 ≤ c) (hpc : c < p)
    (h : ∀ a, 0 ≤ a → a < p → (a - c) * x a ≤ B) : (p - c) * x p ≤ B := by
  have hf : Continuous fun a : ℝ => (a - c) * x a := (continuous_id.sub continuous_const).mul hx
  refine le_of_tendsto ((hf.tendsto p).mono_left (nhdsWithin_le_nhds (s := Iio p))) ?_
  filter_upwards [Ioo_mem_nhdsLT hpc] with a ha
  exact h a (by linarith [ha.1]) ha.2

/-- A scaled Bertrand demand `αx` (`α > 0`) is a Bertrand demand. -/
theorem rbx_scaled_isBertrand {x : ℝ → ℝ} {pbar α : ℝ} (hx : IsBertrandDemand x pbar)
    (hα : 0 < α) : IsBertrandDemand (fun p => α * x p) pbar where
  cont := continuous_const.mul hx.cont
  nonneg p := mul_nonneg hα.le (hx.nonneg p)
  strictAnti p p' h h0 := by
    have : 0 < x p' := by
      rcases (hx.nonneg p').lt_or_eq with h' | h'
      · exact h'
      · rw [← h', mul_zero] at h0; exact absurd h0 (lt_irrefl 0)
    exact mul_lt_mul_of_pos_left (hx.strictAnti p p' h this) hα
  zero p hp := by simp [hx.zero p hp]

/-- Deviation payoffs in the duopoly against a common price `p`: undercutting to `a < p` earns
`(a − c)x(a)`, overpricing earns `0`, matching earns `(p − c)x(p)/2`. -/
theorem rbx_update {x : ℝ → ℝ} {c : ℝ} (p a : Ici (0 : ℝ)) (j : Fin 2) :
    ((a : ℝ) < p → bertrandStage x c j (update (constPrice (Fin 2) p) j a) = (a - c) * x a) ∧
    ((p : ℝ) < a → bertrandStage x c j (update (constPrice (Fin 2) p) j a) = 0) ∧
    bertrandStage x c j (constPrice (Fin 2) p) = (p - c) * (x p / 2) := by
  have := bertrandStage_update (x := x) (c := c) p a j (by simp)
  simpa using this

/-- Linear demand `max{0, 10 − p}` with cost `c ∈ [0, 10)`: `pᵐ = (10 + c)/2` maximizes
`(p − c)x(p)` over `p ≥ 0`, profit is strictly increasing on `[c, pᵐ]`, and `x(pᵐ) > 0`. -/
theorem rbx_lin_facts {c : ℝ} (hc : c < 10) :
    (∀ a : ℝ, (a - c) * bcLinDemand 10 a ≤
      ((10 + c) / 2 - c) * bcLinDemand 10 ((10 + c) / 2)) ∧
    StrictMonoOn (fun p => (p - c) * bcLinDemand 10 p) (Icc c ((10 + c) / 2)) ∧
    0 < bcLinDemand 10 ((10 + c) / 2) := by
  have hm : bcLinDemand 10 ((10 + c) / 2) = (10 - c) / 2 := by
    simp only [bcLinDemand]; rw [max_eq_right (by linarith)]; ring
  refine ⟨fun a => ?_, fun p hp q hq hpq => ?_, by rw [hm]; linarith⟩
  · rw [hm]
    simp only [bcLinDemand]
    rcases le_total (10 - a) 0 with h | h
    · rw [max_eq_left h]; nlinarith
    · rw [max_eq_right h]; nlinarith [sq_nonneg (a - (10 + c) / 2)]
  · simp only [bcLinDemand]
    rw [max_eq_right (by linarith [hp.2]), max_eq_right (by linarith [hq.2])]
    nlinarith [hp.1, hq.2]

/-! ### Exercise 12.D.4(a) -/

/-- **Exercise 12.D.4(a)** (MWG, p. 434). After the cost changes to `c'` (from then on), the
most profitable sustainable price is the monopoly price `pᵐ(c')` at the new cost: for
`δ ∈ [1/2, 1)` Nash reversion sustains it (Proposition 12.D.1 at cost `c'`), and no stationary
price earns a firm more per period. -/
theorem exercise_12_D_4a {x : ℝ → ℝ} {pbar δ : ℝ} (hx : IsBertrandDemand x pbar)
    (cc' pm' : Ici (0 : ℝ)) (hpbar : 0 ≤ pbar) (hδ : 1 / 2 ≤ δ) (hδ1 : δ < 1)
    (hpc : (cc' : ℝ) < pm') (hxp : 0 < x pm')
    (hmono : ∀ a : ℝ, 0 ≤ a → (a - cc') * x a ≤ (pm' - cc') * x pm') :
    IsRepeatedSPNE (bertrandStage (ι := Fin 2) x cc') δ
        (nashReversion (fun _ => constPrice (Fin 2) pm') (constPrice (Fin 2) cc')) ∧
      ∀ (p : Ici (0 : ℝ)) (j : Fin 2), bertrandStage x cc' j (constPrice (Fin 2) p) ≤
        bertrandStage x cc' j (constPrice (Fin 2) pm') := by
  refine ⟨(proposition_12_D_1 hx cc' pm' hpbar (by linarith) hδ1 hpc hxp hmono).2 hδ,
    fun p j => ?_⟩
  rw [(rbx_update p p j).2.2, (rbx_update pm' pm' j).2.2]
  have := hmono p p.2
  linarith

/-- **Exercise 12.D.4(a), comparative statics** (MWG, p. 434). The monopoly price is weakly
increasing in the cost: if `c < c'`, `pᵐ(c)` and `pᵐ(c')` maximize `(p − c)x(p)` and
`(p − c')x(p)`, and `x(pᵐ(c)) > 0`, then `pᵐ(c) ≤ pᵐ(c')`. So a cost increase (weakly) raises
the most profitable sustainable price. -/
theorem exercise_12_D_4a_monotone {x : ℝ → ℝ} {pbar c c' pm pm' : ℝ}
    (hx : IsBertrandDemand x pbar) (hcc : c < c')
    (hm : (pm' - c) * x pm' ≤ (pm - c) * x pm) (hm' : (pm - c') * x pm ≤ (pm' - c') * x pm')
    (hxp : 0 < x pm) : pm ≤ pm' := by
  by_contra hlt
  push Not at hlt
  have hx' := hx.strictAnti pm' pm hlt hxp
  nlinarith [mul_pos (sub_pos.2 hcc) (sub_pos.2 hx')]

/-- **Exercise 12.D.4(a), instance.** Linear demand `max{0, 10 − p}`, cost rising from `1` to
`2`: the monopoly price rises from `11/2` to `6`, and at `δ = 1/2` Nash reversion sustains `6`. -/
theorem exercise_12_D_4a_instance :
    IsRepeatedSPNE (bertrandStage (ι := Fin 2) (bcLinDemand 10) cexP2) (1 / 2)
        (nashReversion (fun _ => constPrice (Fin 2) ⟨6, by norm_num⟩)
          (constPrice (Fin 2) cexP2)) ∧ (11 / 2 : ℝ) ≤ 6 := by
  obtain ⟨h1, -, h3⟩ := rbx_lin_facts (c := 2) (by norm_num)
  norm_num at h1 h3
  refine ⟨(exercise_12_D_4a (bcLinDemand_isBertrand 10) cexP2 ⟨6, by norm_num⟩ (by norm_num)
    (by norm_num) (by norm_num) (by simp [cexP2]; norm_num) h3 fun a _ => ?_).1, by norm_num⟩
  have := h1 a
  simp only [cexP2]
  norm_num at this ⊢
  exact this

/-! ### Exercise 12.D.4(b) -/

/-- Per-period payoffs of the repeated Bertrand duopoly whose unit cost is `c₁` in period 1 (the
empty history) and `c₂` from period 2 on. -/
noncomputable def costChangeU (x : ℝ → ℝ) (c₁ c₂ : Ici (0 : ℝ)) :
    Fin 2 → OSHist (fun _ : Fin 2 => Ici (0 : ℝ)) → (Fin 2 → Ici (0 : ℝ)) → ℝ :=
  fun j h q => bertrandStage x (if h.length = 0 then (c₁ : ℝ) else c₂) j q

/-- The outcome path `(p₁, p₂, p₂, …)`. -/
def costChangePath (p₁ p₂ : Ici (0 : ℝ)) : ℕ → Fin 2 → Ici (0 : ℝ) :=
  fun t => if t = 0 then constPrice (Fin 2) p₁ else constPrice (Fin 2) p₂

/-- Nash reversion along `(p₁, p₂, p₂, …)`, reverting to the price `c₂` (strategies (12.D.1)
adapted to the cost change). -/
noncomputable def costChangeProfile (p₁ p₂ c₂ : Ici (0 : ℝ)) :
    OSProfile fun _ : Fin 2 => Ici (0 : ℝ) :=
  nashReversion (costChangePath p₁ p₂) (constPrice (Fin 2) c₂)

/-- Subgame perfection of `costChangeProfile p₁ p₂ c₂` in the game with the cost change. -/
def CostChangeSustains (x : ℝ → ℝ) (δ : ℝ) (c₁ c₂ p₁ p₂ : Ici (0 : ℝ)) : Prop :=
  ∀ i (τ : OSHist (fun _ : Fin 2 => Ici (0 : ℝ)) → Ici (0 : ℝ)) h,
    osValue (costChangeU x c₁ c₂) δ (update (costChangeProfile p₁ p₂ c₂) i τ) h i ≤
      osValue (costChangeU x c₁ c₂) δ (costChangeProfile p₁ p₂ c₂) h i

open Classical in
/-- The continuation values of `costChangeProfile`: `R₁(p₁)/2 + δW` at the start, `W` on the path
afterwards and `0` after a deviation, where `W = (p₂ − c₂)x(p₂)/(2(1 − δ))`. -/
noncomputable def costChangeValue (x : ℝ → ℝ) (δ : ℝ) (c₁ c₂ p₁ p₂ : Ici (0 : ℝ))
    (h : OSHist (fun _ : Fin 2 => Ici (0 : ℝ))) : ℝ :=
  if h = [] then (p₁ - c₁) * (x p₁ / 2) + δ * ((p₂ - c₂) * (x p₂ / 2) / (1 - δ))
  else if h = pathHist (costChangePath p₁ p₂) h.length then (p₂ - c₂) * (x p₂ / 2) / (1 - δ)
  else 0

theorem costChangeValue_on {x : ℝ → ℝ} {δ : ℝ} {c₁ c₂ p₁ p₂ : Ici (0 : ℝ)} {t : ℕ}
    (ht : t ≠ 0) : costChangeValue x δ c₁ c₂ p₁ p₂ (pathHist (costChangePath p₁ p₂) t) =
      (p₂ - c₂) * (x p₂ / 2) / (1 - δ) := by
  have hne : pathHist (costChangePath p₁ p₂) t ≠ [] := by
    intro h; have := congrArg List.length h; simp [pathHist_length] at this; omega
  simp [costChangeValue, hne, pathHist_length]

theorem costChangeValue_off {x : ℝ → ℝ} {δ : ℝ} {c₁ c₂ p₁ p₂ : Ici (0 : ℝ)}
    {h : OSHist (fun _ : Fin 2 => Ici (0 : ℝ))}
    (hh : h ≠ pathHist (costChangePath p₁ p₂) h.length) :
    costChangeValue x δ c₁ c₂ p₁ p₂ h = 0 := by
  have hne : h ≠ [] := by rintro rfl; exact hh rfl
  simp [costChangeValue, hne, hh]

/-- The value of `costChangeProfile` is `costChangeValue`. -/
theorem osValue_costChange {x : ℝ → ℝ} {pbar δ : ℝ} (hx : IsBertrandDemand x pbar)
    (hpbar : 0 ≤ pbar) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (c₁ c₂ p₁ p₂ : Ici (0 : ℝ)) (j : Fin 2)
    (h : OSHist (fun _ : Fin 2 => Ici (0 : ℝ))) :
    osValue (costChangeU x c₁ c₂) δ (costChangeProfile p₁ p₂ c₂) h j =
      costChangeValue x δ c₁ c₂ p₁ p₂ h := by
  have hx0 := hx.nonneg 0
  have hu : ∀ i h q, |costChangeU x c₁ c₂ i h q| ≤ (pbar + c₁) * x 0 + (pbar + c₂) * x 0 := by
    intro i h q
    have h1 := bertrandStage_bound hx c₁.2 hpbar i q
    have h2 := bertrandStage_bound hx c₂.2 hpbar i q
    have h3 : 0 ≤ (pbar + c₁) * x 0 := mul_nonneg (by linarith [Set.mem_Ici.1 c₁.2]) hx0
    have h4 : 0 ≤ (pbar + c₂) * x 0 := mul_nonneg (by linarith [Set.mem_Ici.1 c₂.2]) hx0
    unfold costChangeU
    split_ifs <;> linarith
  unfold costChangeProfile
  set W := ((p₂ : ℝ) - c₂) * (x p₂ / 2) / (1 - δ) with hW
  set Q := costChangePath p₁ p₂ with hQ
  refine osValue_eq_of_rec hδ0 hδ1 hu _ j _
    (B := |((p₁ : ℝ) - c₁) * (x p₁ / 2) + δ * W| + |W|) (fun h => ?_) (fun h => ?_) h
  · unfold costChangeValue
    split_ifs
    · exact le_add_of_nonneg_right (abs_nonneg _)
    · exact le_add_of_nonneg_left (abs_nonneg _)
    · simp only [abs_zero]; positivity
  · have hupd : ∀ (c : Ici (0 : ℝ)) (p : Ici (0 : ℝ)),
        bertrandStage x c j (constPrice (Fin 2) p) = (p - c) * (x p / 2) :=
      fun c p => (rbx_update (c := c) p p j).2.2
    by_cases h0 : h = []
    · subst h0
      have hplay : osPlay (nashReversion Q (constPrice (Fin 2) c₂)) [] =
          constPrice (Fin 2) p₁ := by
        have := osPlay_nashReversion_on (Q := Q) (qs := constPrice (Fin 2) c₂) 0
        simpa [hQ, costChangePath, pathHist] using this
      rw [hplay]
      have hnext : [constPrice (Fin 2) p₁] = pathHist Q 1 := by
        simp [hQ, pathHist, costChangePath]
      rw [hnext, costChangeValue_on one_ne_zero]
      simp [costChangeValue, costChangeU, hupd, ← hW]
    · by_cases hp : h = pathHist Q h.length
      · set t := h.length with ht
        have ht0 : t ≠ 0 := by intro h'; exact h0 (List.length_eq_zero_iff.1 h')
        rw [hp, osPlay_nashReversion_on (Q := Q), pathHist_succ_eq,
          costChangeValue_on ht0, costChangeValue_on (Nat.succ_ne_zero t)]
        have hQt : Q t = constPrice (Fin 2) p₂ := by simp [hQ, costChangePath, ht0]
        rw [hQt]
        simp only [costChangeU, pathHist_length, ht0, ite_false, hupd]
        have : (1 - δ) ≠ 0 := by linarith
        field_simp
        ring
      · rw [osPlay_nashReversion_off hp, costChangeValue_off hp,
          costChangeValue_off (not_pathHist_cons hp _)]
        have hl : h.length ≠ 0 := fun h' => h0 (List.length_eq_zero_iff.1 h')
        simp [costChangeU, hl, hupd]

/-- **Exercise 12.D.4(b): the SPNE condition** (MWG, p. 434). Let `δ ∈ [1/2, 1)` and let `pᵐ₂`
be a monopoly price at the period-2 cost `c₂` (`pᵐ₂ > c₂`, `x(pᵐ₂) > 0`). Nash reversion along
`(p₁, pᵐ₂, pᵐ₂, …)` is an SPNE iff no period-1 deviation `a ≠ p₁` earns more than
`R₁(p₁)/2 + δW`, `W = R₂(pᵐ₂)/(2(1 − δ))`: from period 2 on the condition is that of
Proposition 12.D.1. -/
theorem costChange_spne_iff {x : ℝ → ℝ} {pbar δ : ℝ} (hx : IsBertrandDemand x pbar)
    (hpbar : 0 ≤ pbar) (hδ : 1 / 2 ≤ δ) (hδ1 : δ < 1) (c₁ c₂ p₁ pm₂ : Ici (0 : ℝ))
    (hpc₂ : (c₂ : ℝ) < pm₂) (hxp₂ : 0 < x pm₂)
    (hmono₂ : ∀ a : ℝ, 0 ≤ a → (a - c₂) * x a ≤ (pm₂ - c₂) * x pm₂) :
    CostChangeSustains x δ c₁ c₂ p₁ pm₂ ↔
      ∀ (j : Fin 2) (a : Ici (0 : ℝ)), a ≠ p₁ →
        bertrandStage x c₁ j (update (constPrice (Fin 2) p₁) j a) ≤
          (p₁ - c₁) * (x p₁ / 2) + δ * ((pm₂ - c₂) * (x pm₂ / 2) / (1 - δ)) := by
  have hδ0 : 0 ≤ δ := by linarith
  have h1δ : 0 < 1 - δ := by linarith
  have hx0 := hx.nonneg 0
  have hu : ∀ i h q, |costChangeU x c₁ c₂ i h q| ≤ (pbar + c₁) * x 0 + (pbar + c₂) * x 0 := by
    intro i h q
    have h1 := bertrandStage_bound hx c₁.2 hpbar i q
    have h2 := bertrandStage_bound hx c₂.2 hpbar i q
    have h3 : 0 ≤ (pbar + c₁) * x 0 := mul_nonneg (by linarith [Set.mem_Ici.1 c₁.2]) hx0
    have h4 : 0 ≤ (pbar + c₂) * x 0 := mul_nonneg (by linarith [Set.mem_Ici.1 c₂.2]) hx0
    unfold costChangeU
    split_ifs <;> linarith
  set Q := costChangePath p₁ pm₂ with hQ
  set W := ((pm₂ : ℝ) - c₂) * (x pm₂ / 2) / (1 - δ) with hW
  have hR₂ : 0 < ((pm₂ : ℝ) - c₂) * x pm₂ := mul_pos (by linarith) hxp₂
  have hWge : ((pm₂ : ℝ) - c₂) * x pm₂ ≤ W := by
    rw [hW, le_div_iff₀ h1δ]; nlinarith
  have hval := fun i h => osValue_costChange (j := i) hx hpbar hδ0 hδ1 c₁ c₂ p₁ pm₂ h
  have hplay0 : osPlay (nashReversion Q (constPrice (Fin 2) c₂)) [] = constPrice (Fin 2) p₁ := by
    have := osPlay_nashReversion_on (Q := Q) (qs := constPrice (Fin 2) c₂) 0
    simpa [hQ, costChangePath, pathHist] using this
  unfold CostChangeSustains
  rw [oneShot_deviation_principle_discounted_iff hδ0 hδ1 hu]
  simp only [hval]
  unfold costChangeProfile
  rw [← hQ]
  constructor
  · intro hos j a ha
    have := hos j [] a
    rw [hplay0] at this
    have hoff : update (Q 0) j a :: pathHist Q 0 ≠
        pathHist Q (update (Q 0) j a :: pathHist Q 0).length :=
      update_cons_off (by simpa [hQ, costChangePath, constPrice] using ha)
    have hQ0 : Q 0 = constPrice (Fin 2) p₁ := by simp [hQ, costChangePath]
    rw [hQ0] at hoff
    have e := costChangeValue_off (x := x) (δ := δ) (c₁ := c₁) (c₂ := c₂) hoff
    change costChangeValue x δ c₁ c₂ p₁ pm₂ [update (constPrice (Fin 2) p₁) j a] = 0 at e
    rw [e] at this
    simpa [costChangeU, costChangeValue] using this
  · intro hcond i h a
    by_cases h0 : h = []
    · subst h0
      rw [hplay0]
      by_cases ha : a = p₁
      · subst ha
        have : update (constPrice (Fin 2) a) i a = constPrice (Fin 2) a := by
          funext k; by_cases hk : k = i
          · subst hk; simp [constPrice]
          · simp [update_of_ne hk, constPrice]
        rw [this]
        have hnext : [constPrice (Fin 2) a] = pathHist Q 1 := by
          simp [hQ, pathHist, costChangePath]
        rw [hnext, costChangeValue_on one_ne_zero]
        simp [costChangeU, costChangeValue, (rbx_update (c := c₁) a a i).2.2, ← hW]
      · have hoff : update (Q 0) i a :: pathHist Q 0 ≠
            pathHist Q (update (Q 0) i a :: pathHist Q 0).length :=
          update_cons_off (by simpa [hQ, costChangePath, constPrice] using ha)
        have hQ0 : Q 0 = constPrice (Fin 2) p₁ := by simp [hQ, costChangePath]
        rw [hQ0] at hoff
        have e := costChangeValue_off (x := x) (δ := δ) (c₁ := c₁) (c₂ := c₂) hoff
        change costChangeValue x δ c₁ c₂ p₁ pm₂ [update (constPrice (Fin 2) p₁) i a] = 0 at e
        rw [e]
        have := hcond i a ha
        simpa [costChangeU, costChangeValue, ← hW] using this
    · have hl : h.length ≠ 0 := fun h' => h0 (List.length_eq_zero_iff.1 h')
      by_cases hp : h = pathHist Q h.length
      · set t := h.length with ht
        have hQt : Q t = constPrice (Fin 2) pm₂ := by simp [hQ, costChangePath, hl]
        rw [hp, osPlay_nashReversion_on (Q := Q), costChangeValue_on hl, hQt]
        by_cases ha : a = pm₂
        · subst ha
          have : update (constPrice (Fin 2) a) i a = constPrice (Fin 2) a := by
            funext k; by_cases hk : k = i
            · subst hk; simp [constPrice]
            · simp [update_of_ne hk, constPrice]
          rw [this, ← hQt, pathHist_succ_eq, costChangeValue_on (Nat.succ_ne_zero t), hQt]
          simp only [costChangeU, pathHist_length, hl, ite_false]
          rw [(rbx_update (c := c₂) a a i).2.2]
          have hne : (1 - δ) ≠ 0 := by linarith
          apply le_of_eq
          field_simp
          ring
        · have hoff : update (Q t) i a :: pathHist Q t ≠
              pathHist Q (update (Q t) i a :: pathHist Q t).length :=
            update_cons_off (by simpa [hQt, constPrice] using ha)
          rw [hQt] at hoff
          rw [costChangeValue_off hoff, mul_zero, add_zero]
          simp only [costChangeU, pathHist_length, hl, ite_false]
          rcases lt_trichotomy (a : ℝ) pm₂ with h' | h' | h'
          · rw [(rbx_update pm₂ a i).1 h']
            linarith [hmono₂ a a.2]
          · exact absurd (Subtype.ext h') ha
          · rw [(rbx_update pm₂ a i).2.1 h']
            linarith
      · rw [osPlay_nashReversion_off hp, costChangeValue_off hp,
          costChangeValue_off (not_pathHist_cons hp _), mul_zero, add_zero]
        simp only [costChangeU, hl, ite_false]
        have := bertrandStage_nash (ι := Fin 2) hx c₂ (by simp) i a
        rw [(rbx_update (c := c₂) c₂ c₂ i).2.2] at this
        simpa using this

/-- **Exercise 12.D.4(b)** (MWG, p. 434). The cost is `c₁` in period 1 and `c₂` afterwards; play
from period 2 on follows Nash reversion at the monopoly price `pᵐ₂` for `c₂`, and
`δ ∈ [1/2, 1)`. Let `R₁(p) = (p − c₁)x(p)`, `Γ = δR₂(pᵐ₂)/(1 − δ)`, and suppose `pᵐ₁ > c₁`
maximizes `R₁` with `R₁` strictly increasing on `[c₁, pᵐ₁]`. Then:
* a period-1 price `p₁ ∈ (c₁, pᵐ₁]` is sustainable iff `R₁(p₁) ≤ Γ`;
* if `Γ ≥ R₁(pᵐ₁)`, the period-1 monopoly price is sustainable;
* if `Γ < R₁(pᵐ₁)`, the maximal sustainable period-1 price is the `p̂ ∈ (c₁, pᵐ₁)` with
  `R₁(p̂) = Γ`: strictly below the monopoly price for the period-1 cost. -/
theorem exercise_12_D_4b {x : ℝ → ℝ} {pbar δ : ℝ} (hx : IsBertrandDemand x pbar)
    (hpbar : 0 ≤ pbar) (hδ : 1 / 2 ≤ δ) (hδ1 : δ < 1) (c₁ c₂ pm₁ pm₂ : Ici (0 : ℝ))
    (hpc₂ : (c₂ : ℝ) < pm₂) (hxp₂ : 0 < x pm₂)
    (hmono₂ : ∀ a : ℝ, 0 ≤ a → (a - c₂) * x a ≤ (pm₂ - c₂) * x pm₂)
    (hpc₁ : (c₁ : ℝ) < pm₁) (hmono₁ : ∀ a : ℝ, 0 ≤ a → (a - c₁) * x a ≤ (pm₁ - c₁) * x pm₁)
    (hsm₁ : StrictMonoOn (fun p => (p - c₁) * x p) (Icc (c₁ : ℝ) pm₁)) :
    (∀ p₁ : Ici (0 : ℝ), (c₁ : ℝ) < p₁ → (p₁ : ℝ) ≤ pm₁ →
      (CostChangeSustains x δ c₁ c₂ p₁ pm₂ ↔
        (p₁ - c₁) * x p₁ ≤ δ * ((pm₂ - c₂) * x pm₂) / (1 - δ))) ∧
    ((pm₁ - c₁) * x pm₁ ≤ δ * ((pm₂ - c₂) * x pm₂) / (1 - δ) →
      CostChangeSustains x δ c₁ c₂ pm₁ pm₂) ∧
    (δ * ((pm₂ - c₂) * x pm₂) / (1 - δ) < (pm₁ - c₁) * x pm₁ →
      ∃ ph : Ici (0 : ℝ), (c₁ : ℝ) < ph ∧ (ph : ℝ) < pm₁ ∧
        (ph - c₁) * x ph = δ * ((pm₂ - c₂) * x pm₂) / (1 - δ) ∧
        IsGreatest {q : Ici (0 : ℝ) | CostChangeSustains x δ c₁ c₂ q pm₂} ph) := by
  have h1δ : 0 < 1 - δ := by linarith
  have hc₁0 : (0 : ℝ) ≤ c₁ := c₁.2
  set Γ := δ * ((pm₂ - c₂) * x pm₂) / (1 - δ) with hΓ
  have hR₂ : 0 < ((pm₂ : ℝ) - c₂) * x pm₂ := mul_pos (by linarith) hxp₂
  have hΓpos : 0 < Γ := div_pos (mul_pos (by linarith) hR₂) h1δ
  have hB : ∀ p₁ : Ici (0 : ℝ), ((p₁ : ℝ) - c₁) * (x p₁ / 2) +
      δ * ((pm₂ - c₂) * (x pm₂ / 2) / (1 - δ)) = ((p₁ - c₁) * x p₁ + Γ) / 2 := by
    intro p₁; rw [hΓ]; field_simp
  have hiff := fun p₁ => costChange_spne_iff hx hpbar hδ hδ1 c₁ c₂ p₁ pm₂ hpc₂ hxp₂ hmono₂
  have hbelow : ∀ (p₁ : Ici (0 : ℝ)) (a : ℝ), (c₁ : ℝ) < p₁ → (p₁ : ℝ) ≤ pm₁ → a < p₁ →
      (a - c₁) * x a ≤ (p₁ - c₁) * x p₁ := by
    intro p₁ a hp1 hp2 hap
    rcases le_or_gt (c₁ : ℝ) a with hac | hac
    · exact hsm₁.monotoneOn ⟨hac, by linarith⟩ ⟨hp1.le, hp2⟩ hap.le
    · have h1 : (a - c₁) * x a ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) (hx.nonneg a)
      have h2 : 0 ≤ ((p₁ : ℝ) - c₁) * x p₁ := mul_nonneg (by linarith) (hx.nonneg _)
      linarith
  have part1 : ∀ p₁ : Ici (0 : ℝ), (c₁ : ℝ) < p₁ → (p₁ : ℝ) ≤ pm₁ →
      (CostChangeSustains x δ c₁ c₂ p₁ pm₂ ↔ (p₁ - c₁) * x p₁ ≤ Γ) := by
    intro p₁ hp1 hp2
    rw [hiff p₁]
    simp only [hB]
    constructor
    · intro h
      have := rbx_le_of_below hx.cont hc₁0 hp1 (B := ((p₁ - c₁) * x p₁ + Γ) / 2)
        (fun a ha hap => by
          have h' := h 0 ⟨a, ha⟩ (fun heq => by
            have := congrArg Subtype.val heq; simp at this; linarith)
          rwa [(rbx_update p₁ ⟨a, ha⟩ 0).1 hap] at h')
      linarith
    · intro hle j a ha
      rcases lt_trichotomy (a : ℝ) p₁ with h' | h' | h'
      · rw [(rbx_update p₁ a j).1 h']
        linarith [hbelow p₁ a hp1 hp2 h']
      · exact absurd (Subtype.ext h') ha
      · rw [(rbx_update p₁ a j).2.1 h']
        have : 0 ≤ ((p₁ : ℝ) - c₁) * x p₁ := mul_nonneg (by linarith) (hx.nonneg _)
        linarith
  refine ⟨part1, fun h => (part1 pm₁ hpc₁ le_rfl).2 h, fun hlt => ?_⟩
  have hcont : ContinuousOn (fun p => (p - (c₁ : ℝ)) * x p) (Icc (c₁ : ℝ) pm₁) :=
    ((continuous_id.sub continuous_const).mul hx.cont).continuousOn
  obtain ⟨ph, hph, hval⟩ := intermediate_value_Icc hpc₁.le hcont
    (show Γ ∈ Icc (((c₁ : ℝ) - c₁) * x c₁) ((pm₁ - c₁) * x pm₁) by
      rw [sub_self, zero_mul]; exact ⟨hΓpos.le, hlt.le⟩)
  simp only at hval
  have hph1 : (c₁ : ℝ) < ph := by
    rcases eq_or_lt_of_le hph.1 with h | h
    · rw [← h, sub_self, zero_mul] at hval; linarith
    · exact h
  have hph2 : ph < (pm₁ : ℝ) := by
    rcases eq_or_lt_of_le hph.2 with h | h
    · rw [h] at hval; linarith
    · exact h
  refine ⟨⟨ph, by simp only [mem_Ici]; linarith⟩, hph1, hph2, hval, ?_, ?_⟩
  · exact (part1 ⟨ph, _⟩ hph1 hph2.le).2 hval.le
  · intro q hq
    change (q : ℝ) ≤ ph
    rcases le_or_gt (q : ℝ) c₁ with h | h
    · linarith
    rcases le_or_gt (q : ℝ) pm₁ with h' | h'
    · have hRq := (part1 q h h').1 hq
      exact (hsm₁.le_iff_le ⟨h.le, h'⟩ hph).1 (by linarith)
    · exfalso
      have hc := (hiff q).1 hq 0 pm₁ (fun heq => by
        have := congrArg Subtype.val heq; linarith)
      rw [(rbx_update q pm₁ 0).1 h', hB] at hc
      have := hmono₁ q q.2
      linarith

/-- **Exercise 12.D.4(b), comparison** (MWG, p. 434). A cost increase lowers the monopoly profit:
if `c₁ < c₂`, `x(pᵐ₂) > 0` and `pᵐ₁` maximizes `R₁`, then `R₂(pᵐ₂) < R₁(pᵐ₁)`. Hence at
`δ = 1/2` (where `Γ = R₂(pᵐ₂)`) the maximal sustainable period-1 price is strictly below the
period-1 monopoly price. -/
theorem exercise_12_D_4b_compare {x : ℝ → ℝ} {c₁ c₂ pm₁ pm₂ : ℝ} (hc : c₁ < c₂)
    (hxp₂ : 0 < x pm₂) (hmono₁ : (pm₂ - c₁) * x pm₂ ≤ (pm₁ - c₁) * x pm₁) :
    (pm₂ - c₂) * x pm₂ < (pm₁ - c₁) * x pm₁ ∧
      (1 / 2 : ℝ) * ((pm₂ - c₂) * x pm₂) / (1 - 1 / 2) < (pm₁ - c₁) * x pm₁ := by
  have : (pm₂ - c₂) * x pm₂ < (pm₂ - c₁) * x pm₂ := by nlinarith
  constructor
  · linarith
  · norm_num; linarith

/-- **Exercise 12.D.4(b), instance.** Linear demand `max{0, 10 − p}`, cost `1` in period 1 and
`2` afterwards, `δ = 1/2`: `Γ = 16 < 81/4 = R₁(11/2)`, so the maximal sustainable period-1 price
lies strictly between `1` and the period-1 monopoly price `11/2`. -/
theorem exercise_12_D_4b_instance :
    ∃ ph : Ici (0 : ℝ), (1 : ℝ) < ph ∧ (ph : ℝ) < 11 / 2 ∧
      IsGreatest {q : Ici (0 : ℝ) |
        CostChangeSustains (bcLinDemand 10) (1 / 2) cexC1 cexP2 q ⟨6, by norm_num⟩} ph := by
  obtain ⟨m1, s1, x1⟩ := rbx_lin_facts (c := 1) (by norm_num)
  obtain ⟨m2, -, x2⟩ := rbx_lin_facts (c := 2) (by norm_num)
  norm_num at m1 s1 x1 m2 x2
  obtain ⟨ph, h1, h2, -, h4⟩ := (exercise_12_D_4b (bcLinDemand_isBertrand 10) (by norm_num)
    (le_refl _) (by norm_num) cexC1 cexP2 ⟨11 / 2, by norm_num⟩ ⟨6, by norm_num⟩
    (by simp [cexP2]; norm_num) x2 (fun a _ => by simp only [cexP2]; norm_num; exact m2 a)
    (by simp [cexC1]; norm_num) (fun a _ => by simp only [cexC1]; norm_num; exact m1 a)
    (by simpa [cexC1] using s1)).2.2 (by
      simp only [cexC1, cexP2, bcLinDemand]; norm_num)
  exact ⟨ph, by simpa [cexC1] using h1, by simpa using h2, h4⟩

/-! ### Exercise 12.D.5 (Rotemberg and Saloner) -/

/-- The expected discounted value `V`, measured before the state is drawn, of following Nash
reversion with prices `(p_H, p_L)`:
`V = [λ(p_H − c)x(p_H)/2 + (1 − λ)(p_L − c)αx(p_L)/2]/(1 − δ)`. -/
noncomputable def rsValue (x : ℝ → ℝ) (α lam δ : ℝ) (c pH pL : Ici (0 : ℝ)) : ℝ :=
  (lam * ((pH - c) * (x pH / 2)) + (1 - lam) * ((pL - c) * (α * x pL / 2))) / (1 - δ)

/-- **Exercise 12.D.5: Nash reversion with state-contingent prices** (MWG, p. 434). The one-shot
deviation conditions of the strategies "charge `p_H` in the high state (demand `x`) and `p_L` in
the low state (demand `αx`) if no one has deviated, and `c` otherwise": after a deviation, `c` is
a stage Nash equilibrium in both states; on the path, in each state no deviation `a` beats
following, `π_s(a) + δ·0 ≤ π_s(p_s)/2 + δV` (`V = rsValue`). See the module docstring for the
reduction from subgame perfection in the stochastic game. -/
def IsRSNashReversion (x : ℝ → ℝ) (α lam δ : ℝ) (c pH pL : Ici (0 : ℝ)) : Prop :=
  IsStageNash (bertrandStage (ι := Fin 2) x c) (constPrice (Fin 2) c) ∧
  IsStageNash (bertrandStage (ι := Fin 2) (fun p => α * x p) c) (constPrice (Fin 2) c) ∧
  (∀ (j : Fin 2) (a : Ici (0 : ℝ)), a ≠ pH →
    bertrandStage x c j (update (constPrice (Fin 2) pH) j a) ≤
      bertrandStage x c j (constPrice (Fin 2) pH) + δ * rsValue x α lam δ c pH pL) ∧
  (∀ (j : Fin 2) (a : Ici (0 : ℝ)), a ≠ pL →
    bertrandStage (fun p => α * x p) c j (update (constPrice (Fin 2) pL) j a) ≤
      bertrandStage (fun p => α * x p) c j (constPrice (Fin 2) pL) +
        δ * rsValue x α lam δ c pH pL)

/-- The no-deviation condition in one state, against a common price `p` with continuation
`δV`: no undercut `a < p` earns more than `(p − c)y(p)/2 + δV`, which is nonnegative. -/
theorem rs_state_iff (y : ℝ → ℝ) (c p : Ici (0 : ℝ)) (B : ℝ) :
    (∀ (j : Fin 2) (a : Ici (0 : ℝ)), a ≠ p →
      bertrandStage y c j (update (constPrice (Fin 2) p) j a) ≤
        bertrandStage y c j (constPrice (Fin 2) p) + B) ↔
    (∀ a : ℝ, 0 ≤ a → a < p → (a - c) * y a ≤ (p - c) * (y p / 2) + B) ∧
      0 ≤ (p - c) * (y p / 2) + B := by
  constructor
  · intro h
    refine ⟨fun a ha hap => ?_, ?_⟩
    · have h' := h 0 ⟨a, ha⟩ (fun heq => by
        have := congrArg Subtype.val heq; simp at this; linarith)
      rwa [(rbx_update p ⟨a, ha⟩ 0).1 hap, (rbx_update p p 0).2.2] at h'
    · have h' := h 0 ⟨p + 1, by simp only [mem_Ici]; linarith [Set.mem_Ici.1 p.2]⟩
        (fun heq => by have := congrArg Subtype.val heq; simp at this)
      rwa [(rbx_update p ⟨p + 1, _⟩ 0).2.1 (by simp), (rbx_update p p 0).2.2] at h'
  · rintro ⟨h1, h2⟩ j a ha
    rw [(rbx_update p p j).2.2]
    rcases lt_trichotomy (a : ℝ) p with h' | h' | h'
    · rw [(rbx_update p a j).1 h']; exact h1 a a.2 h'
    · exact absurd (Subtype.ext h') ha
    · rw [(rbx_update p a j).2.1 h']; exact h2

/-- The threshold argument: if the monopoly profit `R > 0` is not beaten by the deviation in the
high state although on-path profits are at most `R`, then `δ(1 + λ + (1 − λ)α) ≥ 1`. -/
theorem rs_threshold {R RH RL lam α δ : ℝ} (hR : 0 < R) (hRH : RH ≤ R) (hRL : RL ≤ R)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) (hα0 : 0 ≤ α) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (h : R ≤ RH / 2 + δ * ((lam * (RH / 2) + (1 - lam) * (α * RL / 2)) / (1 - δ))) :
    1 ≤ δ * (1 + lam + (1 - lam) * α) := by
  have h1δ : 0 < 1 - δ := by linarith
  set V := (lam * (RH / 2) + (1 - lam) * (α * RL / 2)) / (1 - δ) with hV
  have hVe : V * (1 - δ) = lam * (RH / 2) + (1 - lam) * (α * RL / 2) := by
    rw [hV]; field_simp
  have hs : lam * (RH / 2) + (1 - lam) * (α * RL / 2) ≤ (lam + (1 - lam) * α) * (R / 2) := by
    have := mul_le_mul_of_nonneg_left hRH hlam0
    have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hRL hα0)
      (sub_nonneg.2 hlam1)
    nlinarith
  have h2 : R / 2 ≤ δ * V := by linarith
  have h3 : R / 2 * (1 - δ) ≤ δ * (V * (1 - δ)) := by nlinarith
  rw [hVe] at h3
  have h4 : R / 2 * (1 - δ) ≤ δ * ((lam + (1 - lam) * α) * (R / 2)) :=
    h3.trans (mul_le_mul_of_nonneg_left hs hδ0)
  nlinarith

/-- **Exercise 12.D.5(a)** (MWG, p. 434). Let `pᵐ > c` maximize `R(p) = (p − c)x(p)` with
`x(pᵐ) > 0`, `0 < α ≤ 1`, `λ ∈ [0, 1]`. If `δ ≥ δ̂ = 1/(1 + λ + (1 − λ)α)` (and `δ < 1`), then
`p_H = p_L = pᵐ` is sustained by Nash reversion. -/
theorem exercise_12_D_5a {x : ℝ → ℝ} {pbar α lam δ : ℝ} (hx : IsBertrandDemand x pbar)
    (c pm : Ici (0 : ℝ)) (hpc : (c : ℝ) < pm) (hxp : 0 < x pm)
    (hmono : ∀ a : ℝ, 0 ≤ a → (a - c) * x a ≤ (pm - c) * x pm) (hα : 0 < α) (hα1 : α ≤ 1)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) (hδ1 : δ < 1)
    (hδ : 1 / (1 + lam + (1 - lam) * α) ≤ δ) :
    IsRSNashReversion x α lam δ c pm pm := by
  have h1δ : 0 < 1 - δ := by linarith
  set R := ((pm : ℝ) - c) * x pm with hR
  have hRpos : 0 < R := mul_pos (by linarith) hxp
  have hs0 : 0 < 1 + lam + (1 - lam) * α := by nlinarith
  have hδs : 1 ≤ δ * (1 + lam + (1 - lam) * α) := by
    rw [div_le_iff₀ hs0] at hδ; linarith
  have hδ0 : 0 ≤ δ := by nlinarith
  have hV : δ * rsValue x α lam δ c pm pm =
      δ * (lam + (1 - lam) * α) * R / (2 * (1 - δ)) := by
    unfold rsValue; rw [hR]; field_simp
  have hkey : R / 2 ≤ δ * rsValue x α lam δ c pm pm := by
    rw [hV, le_div_iff₀ (by positivity)]; nlinarith
  refine ⟨bertrandStage_nash hx c (by simp),
    bertrandStage_nash (rbx_scaled_isBertrand hx hα) c (by simp), ?_, ?_⟩
  · rw [rs_state_iff]
    refine ⟨fun a ha _ => ?_, ?_⟩
    · have := hmono a ha
      linarith
    · linarith
  · rw [rs_state_iff]
    refine ⟨fun a ha _ => ?_, ?_⟩
    · have h1 : (a - c) * (α * x a) = α * ((a - c) * x a) := by ring
      have h2 : ((pm : ℝ) - c) * (α * x pm / 2) = α * (R / 2) := by rw [hR]; ring
      rw [h1, h2]
      nlinarith [hmono a ha]
    · have h2 : ((pm : ℝ) - c) * (α * x pm / 2) = α * (R / 2) := by rw [hR]; ring
      rw [h2]; nlinarith

/-- A sustained high-state price at or below `c`, or in `(c, pᵐ]`, or above `pᵐ`: the high-state
condition of Nash reversion with `p_L = pᵐ`, in terms of `R(p_H)`. -/
theorem rs_high_nec {x : ℝ → ℝ} {pbar α lam δ : ℝ} (hx : IsBertrandDemand x pbar)
    (c pH pL : Ici (0 : ℝ)) (hpc : (c : ℝ) < pH)
    (h : IsRSNashReversion x α lam δ c pH pL) :
    (pH - c) * x pH ≤ (pH - c) * (x pH / 2) + δ * rsValue x α lam δ c pH pL := by
  have h3 := ((rs_state_iff x c pH _).1 h.2.2.1).1
  exact rbx_le_of_below hx.cont c.2 hpc h3

/-- **Exercise 12.D.5(b)** (MWG, p. 434). With `0 < α < 1`, `0 < λ < 1` and the hypotheses of
(a), let `δ̂ = 1/(1 + λ + (1 − λ)α)`. Then `1/2 < δ̂ < 1`; for `0 ≤ δ < δ̂` the monopoly price
cannot be sustained in the high state, whatever `p_L`; and if `R` is strictly increasing on
`[c, pᵐ]` and `1/2 ≤ δ < δ̂`, the highest `p_H` sustainable together with `p_L = pᵐ` is the
`p̂ ∈ (c, pᵐ)` with `R(p̂) = δ(1 − λ)αR(pᵐ)/(1 − δ(1 + λ))`, and `(p̂, pᵐ)` is sustainable:
prices are countercyclical (`p_H = p̂ < pᵐ = p_L`). -/
theorem exercise_12_D_5b {x : ℝ → ℝ} {pbar α lam : ℝ} (hx : IsBertrandDemand x pbar)
    (c pm : Ici (0 : ℝ)) (hpc : (c : ℝ) < pm) (hxp : 0 < x pm)
    (hmono : ∀ a : ℝ, 0 ≤ a → (a - c) * x a ≤ (pm - c) * x pm) (hα : 0 < α) (hα1 : α < 1)
    (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    (1 / 2 < 1 / (1 + lam + (1 - lam) * α) ∧ 1 / (1 + lam + (1 - lam) * α) < 1) ∧
    (∀ δ, 0 ≤ δ → δ < 1 / (1 + lam + (1 - lam) * α) →
      ∀ pL, ¬ IsRSNashReversion x α lam δ c pm pL) ∧
    (StrictMonoOn (fun p => (p - c) * x p) (Icc (c : ℝ) pm) →
      ∀ δ, 1 / 2 ≤ δ → δ < 1 / (1 + lam + (1 - lam) * α) →
      ∃ ph : Ici (0 : ℝ), (c : ℝ) < ph ∧ (ph : ℝ) < pm ∧
        (ph - c) * x ph = δ * (1 - lam) * α * ((pm - c) * x pm) / (1 - δ * (1 + lam)) ∧
        IsGreatest {q : Ici (0 : ℝ) | IsRSNashReversion x α lam δ c q pm} ph) := by
  set R := ((pm : ℝ) - c) * x pm with hR
  have hRpos : 0 < R := mul_pos (by linarith) hxp
  set s := lam + (1 - lam) * α with hs
  have hs1 : s < 1 := by rw [hs]; nlinarith
  have hs0 : 0 < s := by rw [hs]; nlinarith
  have hc0 : (0 : ℝ) ≤ c := c.2
  -- part (ii)
  have part2 : ∀ δ, 0 ≤ δ → δ < 1 / (1 + lam + (1 - lam) * α) →
      ∀ (pH pL : Ici (0 : ℝ)), (pm : ℝ) ≤ pH → ¬ IsRSNashReversion x α lam δ c pH pL := by
    intro δ hδ0 hδ pH pL hpH h
    have hδ1 : δ < 1 := lt_of_lt_of_le hδ (by rw [div_le_one (by nlinarith)]; nlinarith)
    have hdev : R ≤ (pH - c) * (x pH / 2) + δ * rsValue x α lam δ c pH pL := by
      rcases eq_or_lt_of_le hpH with heq | hlt
      · have := rs_high_nec hx c pH pL (by rw [← heq]; exact hpc) h
        have e : pm = pH := Subtype.ext heq
        rw [← e] at this ⊢; exact this
      · have := ((rs_state_iff x c pH _).1 h.2.2.1).1 pm pm.2 hlt
        exact this
    have hth := rs_threshold (R := R) (RH := (pH - c) * x pH) (RL := (pL - c) * x pL) hRpos
      (hmono pH pH.2) (hmono pL pL.2) hlam0.le hlam1.le hα.le hδ0 hδ1 (by
        unfold rsValue at hdev
        convert hdev using 2 <;> ring)
    rw [lt_div_iff₀ (by nlinarith)] at hδ
    linarith
  refine ⟨⟨?_, ?_⟩, fun δ hδ0 hδ pL => part2 δ hδ0 hδ pm pL le_rfl, fun hsm δ hδ hδh => ?_⟩
  · rw [lt_div_iff₀ (by nlinarith)]; nlinarith
  · rw [div_lt_one (by nlinarith)]; nlinarith
  -- part (iii)
  have hδs : δ * (1 + s) < 1 := by
    rw [lt_div_iff₀ (by nlinarith)] at hδh; rw [hs]; linarith
  have hD : 0 < 1 - δ * (1 + lam) := by nlinarith
  have h1δ : 0 < 1 - δ := by nlinarith
  set Rs := δ * (1 - lam) * α * R / (1 - δ * (1 + lam)) with hRs
  have hRs0 : 0 < Rs := div_pos (by
    have : 0 < 1 - lam := by linarith
    have : 0 < δ := by linarith
    positivity) hD
  have hRsR : Rs < R := by
    rw [hRs, div_lt_iff₀ hD]; rw [hs] at hδs; nlinarith
  have hcont : ContinuousOn (fun p => (p - (c : ℝ)) * x p) (Icc (c : ℝ) pm) :=
    ((continuous_id.sub continuous_const).mul hx.cont).continuousOn
  obtain ⟨ph, hph, hval⟩ := intermediate_value_Icc hpc.le hcont
    (show Rs ∈ Icc (((c : ℝ) - c) * x c) ((pm - c) * x pm) by
      rw [sub_self, zero_mul]; exact ⟨hRs0.le, hRsR.le⟩)
  simp only at hval
  have hph1 : (c : ℝ) < ph := by
    rcases eq_or_lt_of_le hph.1 with h | h
    · rw [← h, sub_self, zero_mul] at hval; linarith
    · exact h
  have hph2 : ph < (pm : ℝ) := by
    rcases eq_or_lt_of_le hph.2 with h | h
    · rw [h] at hval; linarith
    · exact h
  set PH : Ici (0 : ℝ) := ⟨ph, by simp only [mem_Ici]; linarith⟩ with hPH
  -- the value at `(p̂, pᵐ)`: `δV = R*/2`
  have hV : δ * rsValue x α lam δ c PH pm = Rs / 2 := by
    unfold rsValue
    have e1 : ((PH : ℝ) - c) * (x PH / 2) = Rs / 2 := by
      simp only [hPH]; rw [← hval]; ring
    have e2 : ((pm : ℝ) - c) * (α * x pm / 2) = α * R / 2 := by rw [hR]; ring
    rw [e1, e2, hRs]
    field_simp
    ring
  have hbelow : ∀ a : ℝ, a < ph → (a - c) * x a ≤ (ph - c) * x ph := by
    intro a hap
    rcases le_or_gt (c : ℝ) a with hac | hac
    · exact hsm.monotoneOn ⟨hac, by linarith⟩ ⟨hph1.le, hph2.le⟩ hap.le
    · have h1 : (a - c) * x a ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) (hx.nonneg a)
      linarith
  refine ⟨PH, hph1, hph2, hval, ⟨bertrandStage_nash hx c (by simp),
    bertrandStage_nash (rbx_scaled_isBertrand hx hα) c (by simp), ?_, ?_⟩, ?_⟩
  · rw [rs_state_iff, hV]
    have e1 : ((PH : ℝ) - c) * (x PH / 2) = Rs / 2 := by
      simp only [hPH]; rw [← hval]; ring
    rw [e1]
    refine ⟨fun a _ hap => ?_, by linarith⟩
    have := hbelow a hap
    linarith
  · rw [rs_state_iff, hV]
    have e2 : ((pm : ℝ) - c) * (α * x pm / 2) = α * R / 2 := by rw [hR]; ring
    rw [e2]
    have hαR : α * R ≤ Rs := by
      rw [hRs, le_div_iff₀ hD]
      have : 1 - δ * (1 + lam) ≤ δ * (1 - lam) := by linarith
      nlinarith [mul_le_mul_of_nonneg_left this (mul_pos hα hRpos).le]
    refine ⟨fun a ha _ => ?_, by positivity⟩
    have h1 : (a - c) * (α * x a) = α * ((a - c) * x a) := by ring
    rw [h1]
    nlinarith [hmono a ha]
  · intro q hq
    change (q : ℝ) ≤ ph
    rcases le_or_gt (q : ℝ) c with h | h
    · linarith
    rcases le_or_gt (q : ℝ) pm with h' | h'
    · have hn := rs_high_nec hx c q pm h hq
      unfold rsValue at hn
      have hRq : ((q : ℝ) - c) * x q ≤ Rs := by
        rw [hRs, le_div_iff₀ hD]
        have e : (pm - c) * (α * x pm / 2) = α * R / 2 := by rw [hR]; ring
        rw [e] at hn
        set Rq := ((q : ℝ) - c) * x q
        have e3 : ((q : ℝ) - c) * (x q / 2) = Rq / 2 := by ring
        rw [e3] at hn
        have hn' : Rq / 2 ≤ δ * ((lam * (Rq / 2) + (1 - lam) * (α * R / 2)) / (1 - δ)) := by
          linarith
        have hVe : (lam * (Rq / 2) + (1 - lam) * (α * R / 2)) / (1 - δ) * (1 - δ) =
            lam * (Rq / 2) + (1 - lam) * (α * R / 2) := by field_simp
        have h2 : Rq / 2 * (1 - δ) ≤ δ * (lam * (Rq / 2) + (1 - lam) * (α * R / 2)) := by
          have := mul_le_mul_of_nonneg_right hn' h1δ.le
          rw [mul_assoc, hVe] at this; exact this
        linarith
      rw [← hval] at hRq
      exact (hsm.le_iff_le ⟨h.le, h'⟩ hph).1 hRq
    · exact absurd hq (part2 δ (by linarith) hδh q pm h'.le)

/-- A price with zero profit that no undercut can beat with a positive profit equals `c`
(demand positive at `c`). -/
theorem rbx_price_eq_c {y : ℝ → ℝ} {pbar : ℝ} (hy : IsBertrandDemand y pbar) (c p : Ici (0 : ℝ))
    (hyc : 0 < y c) (hR : ((p : ℝ) - c) * y p = 0)
    (hdev : ∀ a : ℝ, 0 ≤ a → a < p → (a - c) * y a ≤ 0) : (p : ℝ) = c := by
  rcases lt_trichotomy (p : ℝ) c with h | h | h
  · have hyp : 0 < y p := lt_trans hyc (hy.strictAnti p c h hyc)
    have : ((p : ℝ) - c) * y p < 0 := mul_neg_of_neg_of_pos (by linarith) hyp
    linarith
  · exact h
  · exfalso
    have hev : ∀ᶠ a in 𝓝[>] (c : ℝ), 0 < y a ∧ a < p ∧ (c : ℝ) < a := by
      have h1 : ∀ᶠ a in 𝓝[>] (c : ℝ), 0 < y a :=
        (hy.cont.continuousAt.eventually (lt_mem_nhds hyc)).filter_mono nhdsWithin_le_nhds
      filter_upwards [h1, Ioo_mem_nhdsGT h] with a ha1 ha2
      exact ⟨ha1, ha2.2, ha2.1⟩
    obtain ⟨a, ha1, ha2, ha3⟩ := hev.exists
    have := hdev a (by linarith [Set.mem_Ici.1 c.2]) ha2
    have : 0 < (a - c) * y a := mul_pos (by linarith) ha1
    linarith

/-- **Exercise 12.D.5(c)** (MWG, p. 434). If `δ < 1/2` (with `δ ≥ 0`, `0 < α`, `λ ∈ [0, 1]`,
`c ≥ 0` and `x(c) > 0`), every Nash reversion profile of this form has `p_H = p_L = c`; and
`p_H = p_L = c` is one (for every `δ`). The book's claim concerns these Nash reversion
strategies; we prove it for all of them. -/
theorem exercise_12_D_5c {x : ℝ → ℝ} {pbar α lam δ : ℝ} (hx : IsBertrandDemand x pbar)
    (c : Ici (0 : ℝ)) (hxc : 0 < x c) (hα : 0 < α) (hlam0 : 0 ≤ lam)
    (hlam1 : lam ≤ 1) (hδ0 : 0 ≤ δ) (hδ : δ < 1 / 2) :
    (∀ pH pL : Ici (0 : ℝ), IsRSNashReversion x α lam δ c pH pL →
      (pH : ℝ) = c ∧ (pL : ℝ) = c) ∧ IsRSNashReversion x α lam δ c c c := by
  have hδ1 : δ < 1 := by linarith
  have h1δ : 0 < 1 - δ := by linarith
  have hxα := rbx_scaled_isBertrand hx hα
  have hc0 : (0 : ℝ) ≤ c := c.2
  constructor
  · intro pH pL h
    obtain ⟨-, -, hH, hL⟩ := h
    rw [rs_state_iff] at hH hL
    set V := rsValue x α lam δ c pH pL with hV
    set RH := ((pH : ℝ) - c) * x pH with hRH
    set RL := ((pL : ℝ) - c) * (α * x pL) with hRL
    have eH : ((pH : ℝ) - c) * (x pH / 2) = RH / 2 := by rw [hRH]; ring
    have eL : ((pL : ℝ) - c) * (α * x pL / 2) = RL / 2 := by rw [hRL]; ring
    rw [eH] at hH; rw [eL] at hL
    have hVe : V * (1 - δ) = lam * (RH / 2) + (1 - lam) * (RL / 2) := by
      rw [hV]; unfold rsValue; rw [eH, eL]; field_simp
    -- a state with positive profit gives `R ≤ R/2 + δV`
    have hposH : 0 < RH → RH ≤ RH / 2 + δ * V := by
      intro hpos
      have hpc : (c : ℝ) < pH := by
        by_contra hle; push Not at hle
        have : RH ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) (hx.nonneg _)
        linarith
      exact rbx_le_of_below hx.cont hc0 hpc hH.1
    have hposL : 0 < RL → RL ≤ RL / 2 + δ * V := by
      intro hpos
      have hpc : (c : ℝ) < pL := by
        by_contra hle; push Not at hle
        have : RL ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) (hxα.nonneg _)
        linarith
      exact rbx_le_of_below hxα.cont hc0 hpc hL.1
    have hle : RH ≤ 0 ∧ RL ≤ 0 := by
      by_contra hn
      rw [not_and_or] at hn
      set M := max RH RL with hM
      have hMpos : 0 < M := by
        rcases hn with h | h
        · push Not at h; exact lt_of_lt_of_le h (le_max_left _ _)
        · push Not at h; exact lt_of_lt_of_le h (le_max_right _ _)
      have hVM : V * (1 - δ) ≤ M / 2 := by
        rw [hVe]
        have := mul_le_mul_of_nonneg_left (le_max_left RH RL) hlam0
        have := mul_le_mul_of_nonneg_left (le_max_right RH RL) (sub_nonneg.2 hlam1)
        nlinarith
      have hMle : M ≤ M / 2 + δ * V := by
        rcases le_total RL RH with h | h
        · rw [hM, max_eq_left h] at hMpos ⊢; exact hposH hMpos
        · rw [hM, max_eq_right h] at hMpos ⊢; exact hposL hMpos
      have h3 : M / 2 * (1 - δ) ≤ δ * (V * (1 - δ)) := by nlinarith
      have h4 : M / 2 * (1 - δ) ≤ δ * (M / 2) := h3.trans (mul_le_mul_of_nonneg_left hVM hδ0)
      nlinarith
    have hV0 : V ≤ 0 := by
      have : V * (1 - δ) ≤ 0 := by
        rw [hVe]; nlinarith [mul_nonneg hlam0 (show 0 ≤ -RH by linarith),
          mul_nonneg (sub_nonneg.2 hlam1) (show 0 ≤ -RL by linarith)]
      by_contra hpos; push Not at hpos
      nlinarith
    have hδV : δ * V ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hδ0 hV0
    have hRH0 : RH = 0 := by linarith [hH.2, hle.1]
    have hRL0 : RL = 0 := by linarith [hL.2, hle.2]
    have hVz : δ * V = 0 := by
      have : V * (1 - δ) = 0 := by rw [hVe, hRH0, hRL0]; ring
      have : V = 0 := by
        rcases mul_eq_zero.1 this with h | h
        · exact h
        · linarith
      rw [this, mul_zero]
    refine ⟨rbx_price_eq_c hx c pH hxc hRH0 fun a ha hap => ?_,
      rbx_price_eq_c hxα c pL (by simpa using mul_pos hα hxc) hRL0 fun a ha hap => ?_⟩
    · have := hH.1 a ha hap; rw [hRH0, hVz] at this; linarith
    · have := hL.1 a ha hap; rw [hRL0, hVz] at this; linarith
  · refine ⟨bertrandStage_nash hx c (by simp), bertrandStage_nash hxα c (by simp), ?_, ?_⟩
    · intro j a ha
      have h1 := bertrandStage_nash (ι := Fin 2) hx c (by simp) j a
      have hV : rsValue x α lam δ c c c = 0 := by simp [rsValue]
      rw [hV, mul_zero, add_zero]
      exact h1
    · intro j a ha
      have h1 := bertrandStage_nash (ι := Fin 2) hxα c (by simp) j a
      have hV : rsValue x α lam δ c c c = 0 := by simp [rsValue]
      rw [hV, mul_zero, add_zero]
      exact h1

/-- **Exercise 12.D.5, instance.** Linear demand `max{0, 10 − p}`, `c = 1` (`pᵐ = 11/2`),
`λ = α = 1/2`, so `δ̂ = 4/7`: at `δ = 4/7` the monopoly price is sustained in both states; at
`δ = 1/2` it is not sustained in the high state, and the highest sustainable `p_H` (with
`p_L = 11/2`) lies strictly between `1` and `11/2`; at `δ = 1/4` both prices must equal `1`. -/
theorem exercise_12_D_5_instance :
    IsRSNashReversion (bcLinDemand 10) (1 / 2) (1 / 2) (4 / 7) cexC1 ⟨11 / 2, by norm_num⟩
      ⟨11 / 2, by norm_num⟩ ∧
    ¬ IsRSNashReversion (bcLinDemand 10) (1 / 2) (1 / 2) (1 / 2) cexC1 ⟨11 / 2, by norm_num⟩
      ⟨11 / 2, by norm_num⟩ ∧
    (∃ ph : Ici (0 : ℝ), (1 : ℝ) < ph ∧ (ph : ℝ) < 11 / 2 ∧
      IsGreatest {q : Ici (0 : ℝ) | IsRSNashReversion (bcLinDemand 10) (1 / 2) (1 / 2) (1 / 2)
        cexC1 q ⟨11 / 2, by norm_num⟩} ph) ∧
    ∀ pH pL : Ici (0 : ℝ), IsRSNashReversion (bcLinDemand 10) (1 / 2) (1 / 2) (1 / 4) cexC1 pH pL →
      (pH : ℝ) = 1 ∧ (pL : ℝ) = 1 := by
  obtain ⟨m1, s1, x1⟩ := rbx_lin_facts (c := 1) (by norm_num)
  norm_num at m1 s1 x1
  have hm : ∀ a : ℝ, 0 ≤ a → (a - (cexC1 : ℝ)) * bcLinDemand 10 a ≤
      (((⟨11 / 2, by norm_num⟩ : Ici (0 : ℝ)) : ℝ) - cexC1) *
        bcLinDemand 10 ((⟨11 / 2, by norm_num⟩ : Ici (0 : ℝ)) : ℝ) := by
    intro a _; simp only [cexC1]; norm_num; exact m1 a
  have hpc : (cexC1 : ℝ) < ((⟨11 / 2, by norm_num⟩ : Ici (0 : ℝ)) : ℝ) := by
    simp only [cexC1]; norm_num
  have hb := exercise_12_D_5b (α := 1 / 2) (lam := 1 / 2) (bcLinDemand_isBertrand 10) cexC1
    ⟨11 / 2, by norm_num⟩ hpc x1 hm
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨exercise_12_D_5a (bcLinDemand_isBertrand 10) cexC1 _ hpc x1 hm (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hb.2.1 (1 / 2) (by norm_num) (by norm_num) _, ?_, fun pH pL h => ?_⟩
  · obtain ⟨ph, h1, h2, -, h4⟩ := hb.2.2 (by simpa [cexC1] using s1) (1 / 2) le_rfl
      (by norm_num)
    exact ⟨ph, by simpa [cexC1] using h1, by simpa using h2, h4⟩
  · have := (exercise_12_D_5c (bcLinDemand_isBertrand 10) cexC1
      (by simp [cexC1, bcLinDemand]) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)).1 pH pL h
    simpa [cexC1] using this

end MWG.MarketPower
