/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGEquilibriumUncertainty.RationalExpectations
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Rational expectations: Examples 19.H.4-19.H.6, Exercises 19.H.4, 19.H.5, 19.H.7

* **Exercise 19.H.7(a)-(d)** (MWG, pp. 730-731): spot prices with full information
  `(1, 6/(6+ε))`, with consumer 1 uninformed `(7/6, 5/(6+ε))`; for `ε ≠ 0` the full-information
  prices are a (revealing) rational expectations equilibrium; for `ε = 0` there is none.
* **Example 19.H.4** and **Exercise 19.H.4** (pp. 722-723): the 50 states `(β, ε₁, ε₂)` of
  footnote 47, signals `σᵢ = β² + εᵢ`. The pooled information price is `2` if some `σᵢ ∈ {4,5,6}`,
  `1` if some `σᵢ ∈ {-1,0,1}`, and `3/2` otherwise; it is not fully revealing but is a rational
  expectations equilibrium price function. The book prints `β/2` and `3/4`, which are the prices
  when each consumer owns two units of good 1, not one as in Example 19.H.2 (correction 8).
* **Example 19.H.5** and **Exercise 19.H.5** (p. 723): the pooled price `β + (1/I)∑ εᵢ`, its
  separation of the two values of `β`, the identification of `εᵢ` from `β` and `σᵢ`, and a `δ > 0`
  independent of `I` and of the price for which a consumer pays `δ` for his signal.
* **Example 19.H.6** (the lemons market, p. 724, footnote 49).
-/

namespace MWG.EquilibriumUncertainty

/-! ## Exercise 19.H.7 -/

/-- The coefficients of Exercise 19.H.7: consumer 1 has `2 ln x₁₁ + x₂₁` in state 1 and
`4 ln x₁₁ + x₂₁` in state 2; consumer 2 has `4` and `2`. -/
def coef19H7 : Fin 2 → Fin 2 → ℝ := ![![2, 4], ![4, 2]]

/-- The endowments of good 1 in Exercise 19.H.7: all held by consumer 2, `6` in state 1 and
`6 + ε` in state 2. -/
def endow19H7 (ε : ℝ) : Fin 2 → Fin 2 → ℝ := ![fun _ => 0, ![6, 6 + ε]]

/-- The signals of Exercise 19.H.7: consumer 1 is uninformed, consumer 2 observes the state. -/
def sig19H7 (i : Fin 2) (s : Fin 2) : ℕ := if i = 0 then 0 else s.val

theorem coef19H7_pos (i s : Fin 2) : 0 < coef19H7 i s := by
  fin_cases i <;> fin_cases s <;> norm_num [coef19H7]

/-- **Exercise 19.H.7(a)** (MWG, p. 730). With both consumers informed the spot prices are
`p̂₁ = 1` and `p̂₂(ε) = 6/(6 + ε)`. -/
theorem exercise_19_H_7a {ε : ℝ} (hε : -6 < ε) :
    QLClears half2 coef19H7 (endow19H7 ε) 0 (fun _ => {0}) 1 ∧
      QLClears half2 coef19H7 (endow19H7 ε) 1 (fun _ => {1}) (6 / (6 + ε)) := by
  have c : ∀ i s, postCoef half2 (coef19H7 i) {s} = coef19H7 i s := fun i s =>
    postCoef_singleton half2_pos _ s
  refine ⟨?_, ?_⟩
  · rw [qlClears_two half2_pos (fun _ => by simp) (fun i => by rw [c]; exact coef19H7_pos i 0)
      (by norm_num [endow19H7]), c, c]
    norm_num [coef19H7, endow19H7]
  · rw [qlClears_two half2_pos (fun _ => by simp) (fun i => by rw [c]; exact coef19H7_pos i 1)
      (by simp [endow19H7]; linarith), c, c]
    simp [coef19H7, endow19H7]
    norm_num

/-- The events of Exercise 19.H.7(b): consumer 1 knows nothing, consumer 2 knows the state. -/
def events19H7b (s : Fin 2) : Fin 2 → Finset (Fin 2) := ![Finset.univ, {s}]

theorem u0_19H7 (s : Fin 2) : postCoef half2 (coef19H7 0) (events19H7b s 0) = 3 := by
  simp [postCoef, half2, coef19H7, events19H7b, Fin.sum_univ_two]; norm_num

theorem u1_19H7 (s : Fin 2) : postCoef half2 (coef19H7 1) (events19H7b s 1) = coef19H7 1 s :=
  postCoef_singleton half2_pos _ s

theorem pos_19H7b (s i : Fin 2) : 0 < postCoef half2 (coef19H7 i) (events19H7b s i) := by
  fin_cases i
  · exact (u0_19H7 s) ▸ by norm_num
  · exact (u1_19H7 s) ▸ coef19H7_pos 1 s

theorem ne_19H7b (s i : Fin 2) : (events19H7b s i).Nonempty := by
  fin_cases i <;> simp [events19H7b]

/-- **Exercise 19.H.7(b)** (MWG, p. 730). With consumer 1 uninformed (and prices not used as
signals) the spot prices are `p̄₁ = 7/6` and `p̄₂(ε) = 5/(6 + ε)`. -/
theorem exercise_19_H_7b {ε : ℝ} (hε : -6 < ε) :
    QLClears half2 coef19H7 (endow19H7 ε) 0 (events19H7b 0) (7 / 6) ∧
      QLClears half2 coef19H7 (endow19H7 ε) 1 (events19H7b 1) (5 / (6 + ε)) := by
  refine ⟨?_, ?_⟩
  · rw [qlClears_two half2_pos (ne_19H7b 0) (pos_19H7b 0) (by norm_num [endow19H7]), u0_19H7,
      u1_19H7]
    norm_num [coef19H7, endow19H7]
  · rw [qlClears_two half2_pos (ne_19H7b 1) (pos_19H7b 1) (by simp [endow19H7]; linarith),
      u0_19H7, u1_19H7]
    simp [coef19H7, endow19H7]
    norm_num

/-- **Exercise 19.H.7(c)** (MWG, pp. 730-731). For `ε ≠ 0` the full-information prices
`(1, 6/(6+ε))` differ, so consumer 1 learns the state from them, and they form a rational
expectations equilibrium. -/
theorem exercise_19_H_7c {ε : ℝ} (hε : -6 < ε) (hε0 : ε ≠ 0) :
    IsREE (QLClears half2 coef19H7 (endow19H7 ε)) ![1, 6 / (6 + ε)] sig19H7 := by
  have hne : (1 : ℝ) ≠ 6 / (6 + ε) := by
    rw [ne_eq, eq_div_iff (by linarith)]; intro h; apply hε0; linarith
  have hev : ∀ s, (fun i => reeEvent ![1, 6 / (6 + ε)] sig19H7 i s) = fun _ => {s} := by
    intro s; funext i; ext s'
    fin_cases i <;> fin_cases s <;> fin_cases s' <;> simp [reeEvent, sig19H7, hne, hne.symm]
  intro s
  rw [hev s]
  fin_cases s
  · exact (exercise_19_H_7a hε).1
  · exact (exercise_19_H_7a hε).2

/-- **Exercise 19.H.7(d)** (MWG, p. 731). If `ε = 0` there is no rational expectations equilibrium
pair of prices: revealing prices would be `(1, 1)`, which do not reveal, and non-revealing prices
would be `(7/6, 5/6)`, which reveal (compare Example 19.H.3). -/
theorem exercise_19_H_7d (P : Fin 2 → ℝ) :
    ¬ IsREE (QLClears half2 coef19H7 (endow19H7 0)) P sig19H7 := by
  intro hP
  have he : ∀ s : Fin 2, 0 < endow19H7 0 0 s + endow19H7 0 1 s := fun s => by
    fin_cases s <;> norm_num [endow19H7]
  by_cases hrev : P 0 = P 1
  · have hev : ∀ s, (fun i => reeEvent P sig19H7 i s) = events19H7b s := by
      intro s; funext i; ext s'
      fin_cases i <;> fin_cases s <;> fin_cases s' <;> simp [reeEvent, sig19H7, hrev, events19H7b]
    have h0 := hP 0
    have h1 := hP 1
    rw [hev, qlClears_two half2_pos (ne_19H7b 0) (pos_19H7b 0) (he 0), u0_19H7, u1_19H7] at h0
    rw [hev, qlClears_two half2_pos (ne_19H7b 1) (pos_19H7b 1) (he 1), u0_19H7, u1_19H7] at h1
    rw [h0, h1] at hrev
    norm_num [coef19H7, endow19H7] at hrev
  · have hrev' : P 1 ≠ P 0 := Ne.symm hrev
    have hev : ∀ s, (fun i => reeEvent P sig19H7 i s) = fun _ => {s} := by
      intro s; funext i; ext s'
      fin_cases i <;> fin_cases s <;> fin_cases s' <;> simp [reeEvent, sig19H7, hrev, hrev']
    have c : ∀ i s, postCoef half2 (coef19H7 i) {s} = coef19H7 i s := fun i s =>
      postCoef_singleton half2_pos _ s
    have h0 := hP 0
    have h1 := hP 1
    rw [hev, qlClears_two half2_pos (fun _ => by simp)
      (fun i => by rw [c]; exact coef19H7_pos i 0) (he 0), c, c] at h0
    rw [hev, qlClears_two half2_pos (fun _ => by simp)
      (fun i => by rw [c]; exact coef19H7_pos i 1) (he 1), c, c] at h1
    apply hrev
    rw [h0, h1]
    norm_num [coef19H7, endow19H7]

/-! ## Example 19.H.4 and Exercise 19.H.4 -/

/-- **Footnote 47** (MWG, p. 722). The `2 × 5 × 5 = 50` states `s = (β, ε₁, ε₂)`, coded as
`s = 25 b + 5 k₁ + k₂` with `β = b + 1`, `εᵢ = kᵢ - 2`. -/
def bOf (s : Fin 50) : ℕ := s.val / 25

/-- `εᵢ + 2` in state `s`. -/
def kOf (i : Fin 2) (s : Fin 50) : ℕ := if i = 0 then s.val / 5 % 5 else s.val % 5

/-- **Example 19.H.4** (MWG, p. 722). The signal `σᵢ = β² + εᵢ`. -/
def sig19H4 (i : Fin 2) (s : Fin 50) : ℤ := ((bOf s : ℤ) + 1) ^ 2 + (kOf i s : ℤ) - 2

/-- `β` in state `s`. -/
def beta19H4 (s : Fin 50) : ℝ := (bOf s : ℝ) + 1

/-- The three cases of Example 19.H.4: some `σᵢ ∈ {4, 5, 6}` (`0`), some `σᵢ ∈ {-1, 0, 1}` (`1`),
both `σᵢ ∈ {2, 3}` (`2`). -/
def case19H4 (s : Fin 50) : Fin 3 :=
  if 4 ≤ sig19H4 0 s ∨ 4 ≤ sig19H4 1 s then 0
  else if sig19H4 0 s ≤ 1 ∨ sig19H4 1 s ≤ 1 then 1 else 2

/-- The pooled information price of Example 19.H.4 (correct values for one unit each). -/
noncomputable def price19H4 (s : Fin 50) : ℝ := ![2, 1, 3 / 2] (case19H4 s)

/-- The uniform prior on the 50 states. -/
noncomputable def unif50 : Fin 50 → ℝ := fun _ => 1 / 50

/-- Both consumers have `β ln x₁ + x₂`. -/
def betaBoth19H4 : Fin 2 → Fin 50 → ℝ := fun _ => beta19H4

/-- With a uniform prior, the posterior coefficient is `(n₀ + 2 n₁)/(n₀ + n₁)` where `n_b` counts
the states of the event with `β = b + 1`. -/
theorem postCoef_unif50 (E : Finset (Fin 50)) (hE : E.Nonempty) :
    postCoef unif50 beta19H4 E = (((E.filter fun s => bOf s = 0).card : ℝ) +
      2 * (E.filter fun s => bOf s ≠ 0).card) /
      (((E.filter fun s => bOf s = 0).card : ℝ) + (E.filter fun s => bOf s ≠ 0).card) := by
  have hb : ∀ s : Fin 50, bOf s ≠ 0 → bOf s = 1 := fun s h => by
    have : bOf s < 2 := by unfold bOf; omega
    omega
  unfold postCoef
  rw [← Finset.sum_filter_add_sum_filter_not E (fun s => bOf s = 0),
    ← Finset.sum_filter_add_sum_filter_not E (fun s => bOf s = 0) (f := unif50)]
  have e1 : ∑ x ∈ E.filter (fun s => bOf s = 0), unif50 x * beta19H4 x =
      (1 / 50) * ((E.filter fun s => bOf s = 0).card : ℝ) := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun s hs => by
      simp [unif50, beta19H4, (Finset.mem_filter.mp hs).2]
  have e2 : ∑ x ∈ E.filter (fun s => ¬ bOf s = 0), unif50 x * beta19H4 x =
      (1 / 50) * (2 * ((E.filter fun s => bOf s ≠ 0).card : ℝ)) := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun s hs => by
      simp [unif50, beta19H4, hb s (Finset.mem_filter.mp hs).2]; norm_num
  have e3 : ∀ F : Finset (Fin 50), ∑ x ∈ F, unif50 x = (1 / 50) * (F.card : ℝ) := fun F => by
    simp [unif50, Finset.sum_const]; ring
  rw [e1, e2, e3, e3]
  have hpos : (0 : ℝ) < ((E.filter fun s => bOf s = 0).card : ℝ) +
      (E.filter fun s => bOf s ≠ 0).card := by
    have := Finset.card_filter_add_card_filter_not (s := E) (fun s => bOf s = 0)
    rw [← Nat.cast_add, this]
    exact_mod_cast hE.card_pos
  field_simp

set_option maxRecDepth 100000 in
/-- The decidable facts behind Example 19.H.4: in case (i) every state with the same signal
values has `β = 2`, in case (ii) `β = 1`, and in case (iii) the pooled event has one state with each
value of `β`. -/
theorem facts19H4 :
    (∀ s s' : Fin 50, case19H4 s = 0 → (∀ k, sig19H4 k s' = sig19H4 k s) → bOf s' ≠ 0) ∧
    (∀ s s' : Fin 50, case19H4 s = 1 → (∀ k, sig19H4 k s' = sig19H4 k s) → bOf s' = 0) ∧
    (∀ s : Fin 50, case19H4 s = 2 →
      (((pooledEvent sig19H4 s).filter fun s' => bOf s' = 0).card = 1 ∧
       ((pooledEvent sig19H4 s).filter fun s' => bOf s' ≠ 0).card = 1)) := by
  decide

set_option maxRecDepth 100000 in
/-- The decidable facts behind the rational expectations property: within one case and one own
signal value, case (i) states have `β = 2`, case (ii) states `β = 1`, and in case (iii) the two
values of `β` are equally frequent (two states each). -/
theorem factsREE19H4 :
    (∀ s s' : Fin 50, case19H4 s = 0 → case19H4 s' = 0 → bOf s' ≠ 0) ∧
    (∀ s s' : Fin 50, case19H4 s = 1 → case19H4 s' = 1 → bOf s' = 0) ∧
    (∀ (i : Fin 2) (s : Fin 50), case19H4 s = 2 →
      (((Finset.univ.filter fun s' => case19H4 s' = case19H4 s ∧ sig19H4 i s' = sig19H4 i s).filter
          fun s' => bOf s' = 0).card = 2 ∧
       ((Finset.univ.filter fun s' => case19H4 s' = case19H4 s ∧ sig19H4 i s' = sig19H4 i s).filter
          fun s' => bOf s' ≠ 0).card = 2)) ∧
    (∃ s s' : Fin 50, case19H4 s = 2 ∧ case19H4 s' = 2 ∧ sig19H4 0 s ≠ sig19H4 0 s') := by
  decide

theorem price19H4_eq_iff (s s' : Fin 50) :
    price19H4 s' = price19H4 s ↔ case19H4 s' = case19H4 s := by
  unfold price19H4
  constructor
  · intro h
    generalize case19H4 s = a at h
    generalize case19H4 s' = b at h
    fin_cases a <;> fin_cases b <;> first | rfl | (norm_num at h)
  · intro h; rw [h]

/-- The pooled coefficient (and price) of Example 19.H.4 in each case. -/
theorem postCoef_pooled19H4 (s : Fin 50) :
    postCoef unif50 beta19H4 (pooledEvent sig19H4 s) = price19H4 s := by
  obtain ⟨f0, f1, f2⟩ := facts19H4
  have hne := pooledEvent_nonempty sig19H4 s
  have hcase : case19H4 s = 0 ∨ case19H4 s = 1 ∨ case19H4 s = 2 := by
    generalize case19H4 s = a; fin_cases a <;> simp
  rcases hcase with h | h | h
  · rw [postCoef_const (fun _ => by norm_num [unif50]) hne (c := 2) fun s' hs' => by
      have := f0 s s' h (by simpa [pooledEvent] using hs')
      have hb : bOf s' = 1 := by have : bOf s' < 2 := by unfold bOf; omega
                                 omega
      simp [beta19H4, hb]; norm_num]
    simp [price19H4, h]
  · rw [postCoef_const (fun _ => by norm_num [unif50]) hne (c := 1) fun s' hs' => by
      simp [beta19H4, f1 s s' h (by simpa [pooledEvent] using hs')]]
    simp [price19H4, h]
  · rw [postCoef_unif50 _ hne]
    rw [(f2 s h).1, (f2 s h).2]
    simp [price19H4, h]; norm_num

/-- **Example 19.H.4** (MWG, pp. 722-723) and **Exercise 19.H.4**, with the endowments of
Example 19.H.2 (one unit of good 1 each): the pooled information price is `2` in case (i), `1` in
case (ii) and `3/2` in case (iii) (the posterior on `β` stays `1/2`); it is not fully revealing,
yet it is a rational expectations equilibrium price function: the price is a sufficient statistic
for the signals. -/
theorem example_19_H_4 :
    IsPooledPrice (QLClears unif50 betaBoth19H4 (fun _ _ => 1)) price19H4 sig19H4 ∧
      ¬ FullyRevealing price19H4 sig19H4 ∧
      IsREE (QLClears unif50 betaBoth19H4 (fun _ _ => 1)) price19H4 sig19H4 := by
  have hu : ∀ s, 0 < unif50 s := fun _ => by norm_num [unif50]
  have hpr : ∀ s, 0 < price19H4 s := fun s => by
    unfold price19H4; generalize case19H4 s = a; fin_cases a <;> norm_num
  obtain ⟨g0, g1, g2, ⟨s₁, s₂, hs₁, hs₂, hsig⟩⟩ := factsREE19H4
  refine ⟨fun s => ?_, fun hfr => ?_, fun s => ?_⟩
  · have c : ∀ i, postCoef unif50 (betaBoth19H4 i) (pooledEvent sig19H4 s) = price19H4 s :=
      fun _ => postCoef_pooled19H4 s
    rw [qlClears_two hu (fun _ => pooledEvent_nonempty _ _) (fun i => by rw [c]; exact hpr s)
      (by norm_num), c, c]
    ring
  · exact hfr s₁ s₂ ⟨0, hsig⟩ ((price19H4_eq_iff s₂ s₁).mpr (hs₁.trans hs₂.symm))
  · have c : ∀ i, postCoef unif50 (betaBoth19H4 i) (reeEvent price19H4 sig19H4 i s) =
        price19H4 s := by
      intro i
      have hev : reeEvent price19H4 sig19H4 i s = Finset.univ.filter
          fun s' => case19H4 s' = case19H4 s ∧ sig19H4 i s' = sig19H4 i s := by
        ext s'; simp [reeEvent, price19H4_eq_iff]
      have hne := reeEvent_nonempty price19H4 sig19H4 i s
      rw [hev] at hne ⊢
      have hcase : case19H4 s = 0 ∨ case19H4 s = 1 ∨ case19H4 s = 2 := by
        generalize case19H4 s = a; fin_cases a <;> simp
      rcases hcase with h | h | h
      · rw [postCoef_const hu hne (c := 2) fun s' hs' => by
          have hc := (Finset.mem_filter.mp hs').2.1
          have := g0 s s' h (hc.trans h)
          have hb : bOf s' = 1 := by have : bOf s' < 2 := by unfold bOf; omega
                                     omega
          simp [betaBoth19H4, beta19H4, hb]; norm_num]
        simp [price19H4, h]
      · rw [postCoef_const hu hne (c := 1) fun s' hs' => by
          have hc := (Finset.mem_filter.mp hs').2.1
          simp [betaBoth19H4, beta19H4, g1 s s' h (hc.trans h)]]
        simp [price19H4, h]
      · rw [show betaBoth19H4 i = beta19H4 from rfl, postCoef_unif50 _ hne]
        rw [(g2 i s h).1, (g2 i s h).2]
        simp [price19H4, h]; norm_num
    rw [qlClears_two hu (fun i => reeEvent_nonempty _ _ i s) (fun i => by rw [c]; exact hpr s)
      (by norm_num), c, c]
    ring

/-- **Example 19.H.4**, correction 8: the printed prices `β/2 = 1`, `β/2 = 1/2` and `3/4` are not
the clearing prices with one unit of good 1 per consumer (they are `2`, `1`, `3/2`); they are the
clearing prices when each consumer owns two units. -/
theorem example_19_H_4_printed (s : Fin 50) :
    QLClears unif50 betaBoth19H4 (fun _ _ => 2) s (fun _ => pooledEvent sig19H4 s)
      (price19H4 s / 2) ∧ price19H4 s / 2 ≠ price19H4 s := by
  have hu : ∀ s, 0 < unif50 s := fun _ => by norm_num [unif50]
  have hpr : 0 < price19H4 s := by
    unfold price19H4; generalize case19H4 s = a; fin_cases a <;> norm_num
  have c : ∀ i, postCoef unif50 (betaBoth19H4 i) (pooledEvent sig19H4 s) = price19H4 s :=
    fun _ => postCoef_pooled19H4 s
  refine ⟨?_, by linarith⟩
  rw [qlClears_two hu (fun _ => pooledEvent_nonempty _ _) (fun i => by rw [c]; exact hpr)
    (by norm_num), c, c]
  ring

/-! ## Example 19.H.5 and Exercise 19.H.5 -/

/-- **Example 19.H.5** (MWG, p. 723). With `I` consumers, one unit of good 1 each, utilities
`(β + εᵢ) ln x₁ + x₂` and pooled information (`β` and all `εᵢ` known), the clearing price is
`p̂ = β + (1/I) ∑ εᵢ`. -/
theorem example_19_H_5_pooled {I : ℕ} [NeZero I] {β : ℝ} (hβ : 1 ≤ β) {ε : Fin I → ℝ}
    (hε : ∀ i, |ε i| ≤ 1 / 2) :
    QLSpotEqm (fun i => β + ε i) (fun _ => 1) (β + (∑ i, ε i) / I) := by
  have hI : (0 : ℝ) < I := by exact_mod_cast NeZero.pos I
  rw [qlSpotEqm_iff (fun i => by linarith [(abs_le.mp (hε i)).1]) (by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    exact hI)]
  simp [Finset.sum_add_distrib]
  field_simp

/-- **Example 19.H.5** (MWG, p. 723). If at most half of the consumers have noise terms in
`[-1/2, 1/2]` and the others are perfectly informed (`εᵢ = 0`), then `|(1/I) ∑ εᵢ| ≤ 1/4`: the
pooled price is below `1.5` when `β = 1` and above `1.5` when `β = 2`, so it reveals `β`. -/
theorem example_19_H_5_separates {I : ℕ} [NeZero I] {ε : Fin I → ℝ} {N : Finset (Fin I)}
    (hN : 2 * N.card ≤ I) (hε : ∀ i, |ε i| ≤ 1 / 2) (h0 : ∀ i ∉ N, ε i = 0) :
    1 + (∑ i, ε i) / I < 3 / 2 ∧ 3 / 2 < 2 + (∑ i, ε i) / I := by
  have hI : (0 : ℝ) < I := by exact_mod_cast NeZero.pos I
  have hsum : |∑ i, ε i| ≤ N.card / 2 := by
    rw [← Finset.sum_subset (Finset.subset_univ N) (fun i _ hi => h0 i hi)]
    calc |∑ i ∈ N, ε i| ≤ ∑ i ∈ N, |ε i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ N, (1 / 2 : ℝ) := Finset.sum_le_sum fun i _ => hε i
      _ = N.card / 2 := by simp; ring
  have hN' : (N.card : ℝ) / 2 ≤ I / 4 := by
    have : (2 * N.card : ℝ) ≤ I := by exact_mod_cast hN
    linarith
  have hb := abs_le.mp (hsum.trans hN')
  have h1 : (∑ i, ε i) / I ≤ 1 / 4 := by rw [div_le_iff₀ hI]; linarith
  have h2 : -(1 / 4) ≤ (∑ i, ε i) / I := by rw [le_div_iff₀ hI]; linarith
  constructor <;> linarith

/-- **Example 19.H.5** (MWG, p. 723). A consumer who knows `β` and his signal `σᵢ = β² + εᵢ` knows
`εᵢ`; with the price revealing `β`, the consumer's information `(p̂, σᵢ)` determines his pooled
demand coefficient `β + εᵢ`, so his demand at `p̂` is the pooled demand and the pooled
information equilibrium is a rational expectations equilibrium. -/
theorem example_19_H_5_identifies {β β' εi εi' p p' : ℝ} (hβ : β = 1 ∨ β = 2)
    (hβ' : β' = 1 ∨ β' = 2) (hp : β = 1 → p < 3 / 2) (hp2 : β = 2 → 3 / 2 < p)
    (hp' : β' = 1 → p' < 3 / 2) (hp2' : β' = 2 → 3 / 2 < p') (hpp : p = p')
    (hσ : β ^ 2 + εi = β' ^ 2 + εi') : β = β' ∧ β + εi = β' + εi' := by
  have hb : β = β' := by
    rcases hβ with h | h <;> rcases hβ' with h' | h'
    · rw [h, h']
    · have := hp h; have := hp2' h'; linarith
    · have := hp2 h; have := hp' h'; linarith
    · rw [h, h']
  subst hb
  exact ⟨rfl, by linarith⟩

/-- The gain from knowing `εᵢ` (Exercise 19.H.5): `(β + ε) ln((β + ε)/β) - ε`. -/
noncomputable def infoGain (β ε : ℝ) : ℝ := (β + ε) * Real.log ((β + ε) / β) - ε

/-- **Exercise 19.H.5** (MWG, p. 730). At any price `p > 0` and wealth `w`, the realized utility of
a consumer who knows `εᵢ` (demand `(β + ε)/p`) exceeds that of one who only knows `β` (demand
`β/p`) by `infoGain β ε`, independent of `p`, `w` and `I`. -/
theorem infoGain_eq {β ε p w : ℝ} (hβ : 0 < β) (hpos : 0 < β + ε) (hp : 0 < p) :
    ((β + ε) * Real.log ((β + ε) / p) + (w - (β + ε))) -
      ((β + ε) * Real.log (β / p) + (w - β)) = infoGain β ε := by
  unfold infoGain
  rw [Real.log_div hpos.ne' hp.ne', Real.log_div hβ.ne' hp.ne', Real.log_div hpos.ne' hβ.ne']
  ring

theorem infoGain_nonneg {β ε : ℝ} (hβ : 0 < β) (hpos : 0 < β + ε) : 0 ≤ infoGain β ε := by
  unfold infoGain
  have hx : 0 < (β + ε) / β := div_pos hpos hβ
  have := Real.one_sub_inv_le_log_of_pos hx
  rw [inv_div] at this
  have h2 : (β + ε) * (1 - β / (β + ε)) = ε := by field_simp; ring
  nlinarith [mul_le_mul_of_nonneg_left this hpos.le]

theorem infoGain_pos {β ε : ℝ} (hβ : 0 < β) (hpos : 0 < β + ε) (hε : ε ≠ 0) :
    0 < infoGain β ε := by
  unfold infoGain
  have hx : 0 < β / (β + ε) := div_pos hβ hpos
  have hx1 : β / (β + ε) ≠ 1 := by
    rw [ne_eq, div_eq_one_iff_eq hpos.ne']; intro h; apply hε; linarith
  have := Real.log_lt_sub_one_of_pos hx hx1
  rw [Real.log_div hβ.ne' hpos.ne'] at this
  rw [Real.log_div hpos.ne' hβ.ne']
  have h2 : (β + ε) * (β / (β + ε) - 1) = -ε := by field_simp; ring
  nlinarith [mul_lt_mul_of_pos_left this hpos]

theorem continuousOn_infoGain {β : ℝ} (hβ : 1 ≤ β) :
    ContinuousOn (infoGain β) (Set.uIcc (-1 / 2) (1 / 2)) := by
  have hpos : ∀ ε ∈ Set.uIcc (-1 / 2 : ℝ) (1 / 2), 0 < β + ε := fun ε hε => by
    rw [Set.uIcc_of_le (by norm_num)] at hε; linarith [hε.1]
  unfold infoGain
  refine ((continuousOn_const.add continuousOn_id).mul ?_).sub continuousOn_id
  exact ((continuousOn_const.add continuousOn_id).div_const β).log fun ε hε =>
    (div_pos (hpos ε hε) (by linarith)).ne'

/-- **Exercise 19.H.5** (MWG, p. 723). With `εᵢ` uniform on `[-1/2, 1/2]` the expected gain from
the private signal, `∫_{-1/2}^{1/2} infoGain β ε dε`, is strictly positive (for `β ≥ 1`). -/
theorem integral_infoGain_pos {β : ℝ} (hβ : 1 ≤ β) :
    0 < ∫ ε in (-1 / 2 : ℝ)..(1 / 2), infoGain β ε := by
  have hβ0 : 0 < β := by linarith
  have hc := continuousOn_infoGain hβ
  have hint : ∀ a b : ℝ, -1 / 2 ≤ a → a ≤ b → b ≤ 1 / 2 →
      IntervalIntegrable (infoGain β) MeasureTheory.volume a b := fun a b ha hab hb =>
    (hc.mono (by
      rw [Set.uIcc_of_le hab, Set.uIcc_of_le (by norm_num)]
      exact Set.Icc_subset_Icc ha hb)).intervalIntegrable
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0)
    (hint _ _ le_rfl (by norm_num) (by norm_num)) (hint _ _ (by norm_num) (by norm_num) le_rfl)]
  have h1 : 0 ≤ ∫ ε in (-1 / 2 : ℝ)..0, infoGain β ε :=
    intervalIntegral.integral_nonneg (by norm_num) fun ε hε =>
      infoGain_nonneg hβ0 (by linarith [hε.1])
  have h2 : 0 < ∫ ε in (0 : ℝ)..(1 / 2), infoGain β ε :=
    intervalIntegral.intervalIntegral_pos_of_pos_on (hint _ _ (by norm_num) (by norm_num) le_rfl)
      (fun ε hε => infoGain_pos hβ0 (by linarith [hε.1]) hε.1.ne') (by norm_num)
  linarith

/-- **Exercise 19.H.5** (MWG, p. 723). There is `δ > 0`, independent of the number `I` of consumers
and of the price `p`, such that a consumer with noise uniform on `[-1/2, 1/2]` who already knows
`β ∈ {1, 2}` strictly gains (in expectation) from buying his signal at cost `δ`. -/
theorem exercise_19_H_5 : ∃ δ > 0, ∀ β : ℝ, (β = 1 ∨ β = 2) →
    δ < ∫ ε in (-1 / 2 : ℝ)..(1 / 2), infoGain β ε := by
  have ha := integral_infoGain_pos (β := 1) le_rfl
  have hb := integral_infoGain_pos (β := 2) (by norm_num)
  refine ⟨min (∫ ε in (-1 / 2 : ℝ)..(1 / 2), infoGain 1 ε)
    (∫ ε in (-1 / 2 : ℝ)..(1 / 2), infoGain 2 ε) / 2, half_pos (lt_min ha hb), fun β hβ => ?_⟩
  rcases hβ with rfl | rfl
  · linarith [min_le_left (∫ ε in (-1 / 2 : ℝ)..(1 / 2), infoGain 1 ε)
      (∫ ε in (-1 / 2 : ℝ)..(1 / 2), infoGain 2 ε)]
  · linarith [min_le_right (∫ ε in (-1 / 2 : ℝ)..(1 / 2), infoGain 1 ε)
      (∫ ε in (-1 / 2 : ℝ)..(1 / 2), infoGain 2 ε)]

/-! ## Example 19.H.6: the lemons market -/

/-- **Example 19.H.6** (MWG, p. 724). Supply of good units: none if `p < 1`, all `N` if `p > 1`,
anything in `[0, N]` if `p = 1` (good units are worth `1` to sellers); the `N` bad units are always
supplied at `p > 0`. -/
def GoodSupply (N p g : ℝ) : Prop :=
  (p < 1 ∧ g = 0) ∨ (p = 1 ∧ 0 ≤ g ∧ g ≤ N) ∨ (1 < p ∧ g = N)

/-- **Example 19.H.6** (MWG, p. 724). The pair `(α, p)` is admissible: `α = 0` for `p < 1`,
`α ∈ [0, 1/2]` for `p = 1`, `α = 1/2` for `p > 1`. -/
def LemonsAdmissible (α p : ℝ) : Prop :=
  (p < 1 → α = 0) ∧ (p = 1 → 0 ≤ α ∧ α ≤ 1 / 2) ∧ (1 < p → α = 1 / 2)

/-- **Example 19.H.6** (MWG, p. 724). Admissibility is consistency of the state of the market `α`
(the fraction of good units supplied) with the supply decisions. -/
theorem lemons_admissible_iff {N α p : ℝ} (hN : 0 < N) :
    LemonsAdmissible α p ↔ ∃ g, GoodSupply N p g ∧ α = g / (g + N) := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    rcases lt_trichotomy p 1 with hp | hp | hp
    · exact ⟨0, Or.inl ⟨hp, rfl⟩, by rw [h1 hp]; simp⟩
    · obtain ⟨ha0, ha1⟩ := h2 hp
      refine ⟨α * N / (1 - α), Or.inr (Or.inl ⟨hp, ?_, ?_⟩), ?_⟩
      · exact div_nonneg (mul_nonneg ha0 hN.le) (by linarith)
      · rw [div_le_iff₀ (by linarith)]; nlinarith
      · have h1α : 1 - α ≠ 0 := by intro h; linarith
        field_simp
        ring
    · exact ⟨N, Or.inr (Or.inr ⟨hp, rfl⟩), by rw [h3 hp]; field_simp; ring⟩
  · rintro ⟨g, hg, rfl⟩
    rcases hg with ⟨hp, rfl⟩ | ⟨hp, hg0, hgN⟩ | ⟨hp, rfl⟩
    · exact ⟨fun _ => by simp, fun h => by linarith, fun h => by linarith⟩
    · refine ⟨fun h => by linarith, fun _ => ⟨by positivity, ?_⟩, fun h => by linarith⟩
      rw [div_le_iff₀ (by linarith)]; linarith
    · exact ⟨fun h => by linarith, fun h => by linarith, fun _ => by field_simp; ring⟩

/-- **Example 19.H.6** (MWG, p. 724). Equivalently, the admissible pairs (with `p > 0`) are
`α = 0, p ≤ 1`; `α ∈ (0, 1/2), p = 1`; and `α = 1/2, p ≥ 1`. -/
theorem lemons_admissible_cases {α p : ℝ} (hα : 0 ≤ α) :
    LemonsAdmissible α p ↔
      (α = 0 ∧ p ≤ 1) ∨ (0 < α ∧ α < 1 / 2 ∧ p = 1) ∨ (α = 1 / 2 ∧ 1 ≤ p) := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    rcases lt_trichotomy p 1 with hp | hp | hp
    · exact Or.inl ⟨h1 hp, hp.le⟩
    · obtain ⟨_, ha1⟩ := h2 hp
      rcases hα.lt_or_eq with h | h
      · rcases ha1.lt_or_eq with h' | h'
        · exact Or.inr (Or.inl ⟨h, h', hp⟩)
        · exact Or.inr (Or.inr ⟨h', hp.ge⟩)
      · exact Or.inl ⟨h.symm, hp.le⟩
    · exact Or.inr (Or.inr ⟨h3 hp, hp.le⟩)
  · rintro (⟨rfl, hp⟩ | ⟨h0, h1, rfl⟩ | ⟨rfl, hp⟩)
    · exact ⟨fun _ => rfl, fun _ => ⟨le_rfl, by norm_num⟩, fun h => by linarith⟩
    · exact ⟨fun h => by linarith, fun _ => ⟨h0.le, h1.le⟩, fun h => by linarith⟩
    · exact ⟨fun h => by linarith, fun _ => ⟨by norm_num, le_rfl⟩, fun _ => rfl⟩

/-- **Example 19.H.6** (MWG, p. 724). Every admissible pair is a rational expectations equilibrium:
with `N` buyers (each demanding at most one unit, only if `4α - p ≥ 0`) and `2N` sellers, demand is
at most `N`, while at `p > 0` the `N` bad units are always supplied; so demand never exceeds
supply. At `α = 1/2`, `p = 3` no demand is expressed (`4α - p < 0`). -/
theorem example_19_H_6 {N d g : ℝ} (hd : d ≤ N) (hg : 0 ≤ g) :
    d ≤ N + g ∧ 4 * (1 / 2 : ℝ) - 3 < 0 := ⟨by linarith, by norm_num⟩

/-- **Footnote 49** (MWG, p. 724). At `α = 1/2`, `p = 1.5`, every buyer wants a unit
(`4α - p > 0`) and every seller supplies: total supply `2` per buyer, total demand `1`. -/
theorem footnote_19_49 : 0 < 4 * (1 / 2 : ℝ) - 1.5 ∧ LemonsAdmissible (1 / 2) 1.5 ∧
    GoodSupply 1 1.5 1 := by
  refine ⟨by norm_num, ⟨fun h => by norm_num at h, fun h => by norm_num at h, fun _ => rfl⟩,
    Or.inr (Or.inr ⟨by norm_num, rfl⟩)⟩

end MWG.EquilibriumUncertainty
