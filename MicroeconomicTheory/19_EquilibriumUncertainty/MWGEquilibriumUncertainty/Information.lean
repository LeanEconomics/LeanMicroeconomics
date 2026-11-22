/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGEquilibriumUncertainty.Firms

/-!
# Imperfect information: signals and the value of information (MWG Section 19.H, pp. 716-719)

States `Fin S` with prior `π ≫ 0`; a signal function `σ : Fin S → β`.

* Measurability of endowments and plans with respect to a signal (p. 716), symmetric information
  (p. 717), posterior probabilities `π_{s'}|σ(s)` and conditional expected utility (p. 717).
* **Definition 19.H.1**: at least as informative / more informative; **footnote 43**: in terms of
  partitions, the finer signal's cells refine the coarser one's (`footnote_19_43`).
* The single-consumer problem: the plan `x^σ` (`IsSignalPlan`), **Proposition 19.H.1**
  (`proposition_19_H_1`) with its two steps (**Exercise 19.H.3**), the state-dependent budgets of
  **Exercise 19.H.2**, and **Exercise 19.H.1(a)-(d)** (ex post optimality under full revelation and
  a counterexample otherwise, interim optimality, and the two conditional comparisons).
* **Example 19.H.1** (Hirshleifer): without information both consumers get `1/√2`; with perfect
  information every spot equilibrium gives them `1` in one state and `0` in the other, so ex ante
  `1/2 < 1/√2` (`example_19_H_1`).
-/

namespace MWG.EquilibriumUncertainty

variable {S : ℕ} {β α : Type*}

/-! ## Signals -/

/-- **p. 716**. `x` (an endowment or a plan) is measurable with respect to the signal `σ`:
`x_s = x_{s'}` whenever `σ(s) = σ(s')`. -/
def SigmaMeas (σ : Fin S → β) (x : Fin S → α) : Prop := ∀ s s', σ s = σ s' → x s = x s'

/-- **p. 717**. Symmetric information: two states are distinguished by one consumer iff they are
distinguished by every other consumer. -/
def SymmetricInfo {ι : Type*} (σ : ι → Fin S → β) : Prop :=
  ∀ i k s s', σ i s ≠ σ i s' ↔ σ k s ≠ σ k s'

/-- **Definition 19.H.1** (MWG, p. 717). `σ'` is at least as informative as `σ`:
`σ(s) ≠ σ(s')` implies `σ'(s) ≠ σ'(s')`. -/
def AtLeastAsInformative {β' : Type*} (σ' : Fin S → β') (σ : Fin S → β) : Prop :=
  ∀ s s', σ s ≠ σ s' → σ' s ≠ σ' s'

/-- **Definition 19.H.1** (MWG, p. 717). `σ'` is more informative than `σ`: at least as informative,
and `σ'(s) ≠ σ'(s')` for some `s, s'` with `σ(s) = σ(s')`. -/
def MoreInformative {β' : Type*} (σ' : Fin S → β') (σ : Fin S → β) : Prop :=
  AtLeastAsInformative σ' σ ∧ ∃ s s', σ s = σ s' ∧ σ' s ≠ σ' s'

/-- **Footnote 43** (MWG, p. 717). `σ'` is at least as informative as `σ` iff the information
partition of `σ'` refines that of `σ`: states in the same `σ'`-cell are in the same `σ`-cell. -/
theorem footnote_19_43 {β' : Type*} (σ' : Fin S → β') (σ : Fin S → β) :
    AtLeastAsInformative σ' σ ↔ ∀ s s', σ' s = σ' s' → σ s = σ s' :=
  ⟨fun h s s' h' => by by_contra hne; exact h s s' hne h',
    fun h s s' hne h' => hne (h s s' h')⟩

/-- A `σ`-measurable plan is `σ'`-measurable when `σ'` is at least as informative. -/
theorem SigmaMeas.mono {β' : Type*} {σ' : Fin S → β'} {σ : Fin S → β}
    (h : AtLeastAsInformative σ' σ) {x : Fin S → α} (hx : SigmaMeas σ x) : SigmaMeas σ' x :=
  fun s s' h' => hx s s' ((footnote_19_43 σ' σ).mp h s s' h')

variable [DecidableEq β]

/-- The prior mass of the `σ`-cell of `s`. -/
def cellMass (π : Fin S → ℝ) (σ : Fin S → β) (s : Fin S) : ℝ :=
  ∑ t, if σ t = σ s then π t else 0

/-- **p. 717**. The posterior `π_{s'}|σ(s) = π_{s'} / ∑_{s'' : σ(s'') = σ(s)} π_{s''}` for
`σ(s') = σ(s)` and `0` otherwise. -/
noncomputable def posterior (π : Fin S → ℝ) (σ : Fin S → β) (s t : Fin S) : ℝ :=
  if σ t = σ s then π t / cellMass π σ s else 0

/-- **p. 717**. Conditional expected utility `∑_{s'} (π_{s'}|σ(s)) u_{s'}(y)`. -/
noncomputable def condEU (π : Fin S → ℝ) (u : Fin S → α → ℝ) (σ : Fin S → β) (s : Fin S)
    (y : α) : ℝ :=
  ∑ t, posterior π σ s t * u t y

theorem cellMass_pos {π : Fin S → ℝ} (hπ : ∀ s, 0 < π s) (σ : Fin S → β) (s : Fin S) :
    0 < cellMass π σ s :=
  lt_of_lt_of_le (by simpa using hπ s) (Finset.single_le_sum (f := fun t =>
    if σ t = σ s then π t else 0) (fun t _ => by split_ifs <;> simp [(hπ t).le])
    (Finset.mem_univ s))

/-- **p. 717**. Posterior probabilities sum to one. -/
theorem posterior_sum {π : Fin S → ℝ} (hπ : ∀ s, 0 < π s) (σ : Fin S → β) (s : Fin S) :
    ∑ t, posterior π σ s t = 1 := by
  have hM := cellMass_pos hπ σ s
  unfold posterior
  rw [show (∑ t, if σ t = σ s then π t / cellMass π σ s else 0) =
    (∑ t, if σ t = σ s then π t else 0) / cellMass π σ s by
      rw [Finset.sum_div]; exact Finset.sum_congr rfl fun t _ => by split_ifs <;> simp]
  exact div_self hM.ne'

theorem cellMass_congr {π : Fin S → ℝ} {σ : Fin S → β} {s s' : Fin S} (h : σ s = σ s') :
    cellMass π σ s = cellMass π σ s' := by
  simp [cellMass, h]

/-- Conditional expected utility is the cell sum divided by the cell mass. -/
theorem condEU_eq (π : Fin S → ℝ) (u : Fin S → α → ℝ) (σ : Fin S → β) (s : Fin S) (y : α) :
    condEU π u σ s y = (∑ t, if σ t = σ s then π t * u t y else 0) / cellMass π σ s := by
  unfold condEU posterior
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun t _ => by split_ifs <;> ring

/-- **p. 718**. The plan `x^σ`: it is `σ`-measurable, feasible in every state's budget `B_s`, and
for every state `s`, `x^σ_s` maximizes expected utility conditional on `σ(s)` in `B_s`. -/
def IsSignalPlan (π : Fin S → ℝ) (u : Fin S → α → ℝ) (σ : Fin S → β) (B : Fin S → Set α)
    (x : Fin S → α) : Prop :=
  SigmaMeas σ x ∧ (∀ s, x s ∈ B s) ∧ ∀ s, ∀ y ∈ B s, condEU π u σ s y ≤ condEU π u σ s (x s)

/-- The key identity: for a `σ`-measurable `y` and a set `C` of states that is a union of
`σ`-cells, `∑_{s∈C} π_s u_s(y_s) = ∑_{s∈C} (π_s / M_s) ∑_{t ∼ s} π_t u_t(y_s)`. -/
theorem sum_eq_sum_cells {π : Fin S → ℝ} (hπ : ∀ s, 0 < π s) (u : Fin S → α → ℝ)
    (σ : Fin S → β) (C : Fin S → Prop) [DecidablePred C]
    (hC : ∀ s t, σ s = σ t → (C s ↔ C t)) {y : Fin S → α} (hy : SigmaMeas σ y) :
    (∑ s, if C s then π s * u s (y s) else 0) =
      ∑ s, if C s then π s / cellMass π σ s *
        (∑ t, if σ t = σ s then π t * u t (y s) else 0) else 0 := by
  symm
  calc (∑ s, if C s then π s / cellMass π σ s *
        (∑ t, if σ t = σ s then π t * u t (y s) else 0) else 0)
      = ∑ s, ∑ t, if C s ∧ σ t = σ s then π s / cellMass π σ s * (π t * u t (y t)) else 0 := by
        refine Finset.sum_congr rfl fun s _ => ?_
        split_ifs with hs
        · rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun t _ => ?_
          by_cases ht : σ t = σ s
          · simp [hs, ht, hy t s ht]
          · simp [ht]
        · simp [hs]
    _ = ∑ t, ∑ s, if C s ∧ σ t = σ s then π s / cellMass π σ s * (π t * u t (y t)) else 0 :=
        Finset.sum_comm
    _ = ∑ t, if C t then π t * u t (y t) else 0 := by
        refine Finset.sum_congr rfl fun t _ => ?_
        have hM := cellMass_pos hπ σ t
        have e : ∀ s, (if C s ∧ σ t = σ s then π s / cellMass π σ s * (π t * u t (y t)) else 0)
            = (if C t then (if σ s = σ t then π s else 0) / cellMass π σ t * (π t * u t (y t))
              else 0) := by
          intro s
          by_cases hst : σ t = σ s
          · have hCs := hC s t hst.symm
            rw [cellMass_congr hst.symm]
            by_cases hCt : C t
            · simp [hCs.mpr hCt, hst, hCt]
            · simp [hCt, show ¬ C s from fun h => hCt (hCs.mp h)]
          · have : ¬ σ s = σ t := fun h => hst h.symm
            simp [hst, this]
        simp only [e]
        split_ifs with hCt
        · rw [← Finset.sum_mul, ← Finset.sum_div]
          have : (∑ s, if σ s = σ t then π s else 0) = cellMass π σ t := rfl
          rw [this, div_self hM.ne', one_mul]
        · simp

/-- **Optimality of `x^σ` on unions of cells.** If `x` is a signal plan for `σ` and `y` is a
`σ`-measurable plan feasible in every state, then `∑_{s∈C} π_s u_s(y_s) ≤ ∑_{s∈C} π_s u_s(x_s)`
for every union `C` of `σ`-cells. -/
theorem signalPlan_optimal_on {π : Fin S → ℝ} (hπ : ∀ s, 0 < π s) {u : Fin S → α → ℝ}
    {σ : Fin S → β} {B : Fin S → Set α} {x : Fin S → α} (hx : IsSignalPlan π u σ B x)
    (C : Fin S → Prop) [DecidablePred C] (hC : ∀ s t, σ s = σ t → (C s ↔ C t))
    {y : Fin S → α} (hy : SigmaMeas σ y) (hyB : ∀ s, y s ∈ B s) :
    (∑ s, if C s then π s * u s (y s) else 0) ≤ ∑ s, if C s then π s * u s (x s) else 0 := by
  rw [sum_eq_sum_cells hπ u σ C hC hy, sum_eq_sum_cells hπ u σ C hC hx.1]
  refine Finset.sum_le_sum fun s _ => ?_
  split_ifs with hs
  · have hM := cellMass_pos hπ σ s
    have h1 := hx.2.2 s (y s) (hyB s)
    rw [condEU_eq, condEU_eq, div_le_div_iff_of_pos_right hM] at h1
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div,
      div_le_div_iff_of_pos_right hM]
    exact mul_le_mul_of_nonneg_left h1 (hπ s).le
  · exact le_rfl

/-- **Exercise 19.H.3** (MWG, p. 729), first step of the proof of Proposition 19.H.1: `x^σ` solves
`max ∑_s π_s u_s(x_s)` over `B^σ`, the `σ`-measurable plans in the budget sets. -/
theorem exercise_19_H_3_max {π : Fin S → ℝ} (hπ : ∀ s, 0 < π s) {u : Fin S → α → ℝ}
    {σ : Fin S → β} {B : Fin S → Set α} {x : Fin S → α} (hx : IsSignalPlan π u σ B x)
    {y : Fin S → α} (hy : SigmaMeas σ y) (hyB : ∀ s, y s ∈ B s) :
    ∑ s, π s * u s (y s) ≤ ∑ s, π s * u s (x s) := by
  simpa using signalPlan_optimal_on hπ hx (fun _ => True) (fun _ _ _ => Iff.rfl) hy hyB

omit [DecidableEq β] in
/-- **Exercise 19.H.3** (MWG, p. 729), second step: if `σ'` is at least as informative as `σ`,
`B^σ ⊆ B^{σ'}`. -/
theorem exercise_19_H_3_subset {β' : Type*} {σ : Fin S → β} {σ' : Fin S → β'}
    (h : AtLeastAsInformative σ' σ)
    {B : Fin S → Set α} {y : Fin S → α} (hy : SigmaMeas σ y ∧ ∀ s, y s ∈ B s) :
    SigmaMeas σ' y ∧ ∀ s, y s ∈ B s :=
  ⟨hy.1.mono h, hy.2⟩

/-- **Proposition 19.H.1** (MWG, p. 718), with the state-dependent budgets of **Exercise 19.H.2**
(the book's case is `B_s = {y : p y₁ + y₂ ≤ w}` for all `s`). In the single-consumer problem, if
`σ'` is at least as informative as `σ`, the ex ante utility of `x^{σ'}` is at least that of
`x^σ`. -/
theorem proposition_19_H_1 {β' : Type*} [DecidableEq β'] {π : Fin S → ℝ} (hπ : ∀ s, 0 < π s)
    {u : Fin S → α → ℝ} {σ : Fin S → β} {σ' : Fin S → β'} (h : AtLeastAsInformative σ' σ)
    {B : Fin S → Set α} {x x' : Fin S → α} (hx : IsSignalPlan π u σ B x)
    (hx' : IsSignalPlan π u σ' B x') :
    ∑ s, π s * u s (x s) ≤ ∑ s, π s * u s (x' s) :=
  exercise_19_H_3_max hπ hx' (hx.1.mono h) hx.2.1

/-- **Exercise 19.H.2** (MWG, p. 729). For Proposition 19.H.1 the spot price and wealth may depend
on the state provided they are `σ`-measurable (then they are `σ'`-measurable as well, and the
budget of the signal `σ(s)` is well defined): with `B_s = {y : p_s y₁ + y₂ ≤ w_s}`. -/
theorem exercise_19_H_2 {β' : Type*} [DecidableEq β'] {π : Fin S → ℝ} (hπ : ∀ s, 0 < π s)
    {u : Fin S → (Fin 2 → ℝ) → ℝ} {σ : Fin S → β} {σ' : Fin S → β'}
    (h : AtLeastAsInformative σ' σ) {p w : Fin S → ℝ} (hp : SigmaMeas σ p) (hw : SigmaMeas σ w)
    {x x' : Fin S → Fin 2 → ℝ}
    (hx : IsSignalPlan π u σ (fun s => {y | p s * y 0 + y 1 ≤ w s}) x)
    (hx' : IsSignalPlan π u σ' (fun s => {y | p s * y 0 + y 1 ≤ w s}) x') :
    SigmaMeas σ' p ∧ SigmaMeas σ' w ∧ ∑ s, π s * u s (x s) ≤ ∑ s, π s * u s (x' s) :=
  ⟨hp.mono h, hw.mono h, proposition_19_H_1 hπ h hx hx'⟩

/-! ## Exercise 19.H.1 -/

/-- With a completely revealing signal, conditional expected utility is the state's utility. -/
theorem condEU_of_injective {π : Fin S → ℝ} (hπ : ∀ s, 0 < π s) {σ : Fin S → β}
    (hσ : Function.Injective σ) (u : Fin S → α → ℝ) (s : Fin S) (y : α) :
    condEU π u σ s y = u s y := by
  rw [condEU_eq]
  have hcell : cellMass π σ s = π s := by
    unfold cellMass
    rw [Finset.sum_eq_single s (fun t _ ht => by simp [hσ.ne ht]) (by simp)]
    simp
  rw [hcell, Finset.sum_eq_single s (fun t _ ht => by simp [hσ.ne ht]) (by simp)]
  simp only [ite_true]
  field_simp [(hπ s).ne']

/-- **Exercise 19.H.1(a)** (MWG, p. 729). If `σ` is completely revealing, `x^σ` is ex post optimal:
in every state the consumption is optimal for that state's spot economy. -/
theorem exercise_19_H_1a {π : Fin S → ℝ} (hπ : ∀ s, 0 < π s) {u : Fin S → α → ℝ}
    {σ : Fin S → β} (hσ : Function.Injective σ) {B : Fin S → Set α} {x : Fin S → α}
    (hx : IsSignalPlan π u σ B x) : ∀ s, ∀ y ∈ B s, u s y ≤ u s (x s) := by
  intro s y hy
  have := hx.2.2 s y hy
  rwa [condEU_of_injective hπ hσ, condEU_of_injective hπ hσ] at this

/-- **Exercise 19.H.1(a)** (MWG, p. 729): without complete revelation `x^σ` need not be ex post
optimal. Two equally likely states, no information (`σ` constant), `u_s(y) = -(y₁ - t_s)²` with
`t = (1, -1)` and budget `y₁ + y₂ ≤ 0`: the plan `x = (0, 0)` in both states is `x^σ`, but in state
`1` the bundle `(1, -1)` is affordable and better. -/
theorem exercise_19_H_1a_counterexample :
    IsSignalPlan (fun _ : Fin 2 => (1 / 2 : ℝ)) ![fun y : Fin 2 → ℝ => -(y 0 - 1) ^ 2,
        fun y => -(y 0 + 1) ^ 2] (fun _ => (0 : ℕ)) (fun _ => {y | y 0 + y 1 ≤ 0})
        (fun _ => 0) ∧
      (![(1 : ℝ), -1] ∈ {y : Fin 2 → ℝ | y 0 + y 1 ≤ 0}) ∧
      (fun y : Fin 2 → ℝ => -(y 0 - 1) ^ 2) (0 : Fin 2 → ℝ) <
        (fun y : Fin 2 → ℝ => -(y 0 - 1) ^ 2) ![1, -1] := by
  refine ⟨⟨fun _ _ _ => rfl, fun _ => by simp, fun s y _ => ?_⟩, by simp, by norm_num⟩
  rw [condEU_eq, condEU_eq]
  simp [cellMass, Fin.sum_univ_two]
  nlinarith [sq_nonneg (y 0)]

/-- **Exercise 19.H.1(b)** (MWG, p. 729). `x^σ` is interim optimal: no `σ`-measurable feasible plan
has a higher expected utility conditional on `σ(s)` for any `s`. -/
theorem exercise_19_H_1b {π : Fin S → ℝ} {u : Fin S → α → ℝ} {σ : Fin S → β}
    {B : Fin S → Set α} {x : Fin S → α} (hx : IsSignalPlan π u σ B x) :
    ¬ ∃ y : Fin S → α, SigmaMeas σ y ∧ (∀ s, y s ∈ B s) ∧
      ∃ s, condEU π u σ s (x s) < condEU π u σ s (y s) := by
  rintro ⟨y, -, hyB, s, hs⟩
  linarith [hx.2.2 s (y s) (hyB s)]

/-- **Exercise 19.H.1(c)** (MWG, p. 729). If `σ'` is at least as informative as `σ`, then for every
`s` the expected utility of `x^{σ'}` conditional on `σ'(s)` is at least that of `x^σ`. -/
theorem exercise_19_H_1c {β' : Type*} [DecidableEq β'] {π : Fin S → ℝ} {u : Fin S → α → ℝ}
    {σ : Fin S → β} {σ' : Fin S → β'} {B : Fin S → Set α} {x x' : Fin S → α}
    (hx : IsSignalPlan π u σ B x) (hx' : IsSignalPlan π u σ' B x') (s : Fin S) :
    condEU π u σ' s (x s) ≤ condEU π u σ' s (x' s) :=
  hx'.2.2 s (x s) (hx.2.1 s)

/-- **Exercise 19.H.1(d)** (MWG, p. 729). If `σ'` is at least as informative as `σ`, then for every
`s` the expected utility of the plan `x^{σ'}` conditional on `σ(s)` is at least that of `x^σ`. -/
theorem exercise_19_H_1d {β' : Type*} [DecidableEq β'] {π : Fin S → ℝ} (hπ : ∀ s, 0 < π s)
    {u : Fin S → α → ℝ} {σ : Fin S → β} {σ' : Fin S → β'} (h : AtLeastAsInformative σ' σ)
    {B : Fin S → Set α} {x x' : Fin S → α} (hx : IsSignalPlan π u σ B x)
    (hx' : IsSignalPlan π u σ' B x') (s : Fin S) :
    ∑ t, posterior π σ s t * u t (x t) ≤ ∑ t, posterior π σ s t * u t (x' t) := by
  have hC : ∀ t t', σ' t = σ' t' → (σ t = σ s ↔ σ t' = σ s) := fun t t' h' => by
    rw [(footnote_19_43 σ' σ).mp h t t' h']
  have key := signalPlan_optimal_on hπ hx' (fun t => σ t = σ s) hC (hx.1.mono h) hx.2.1
  have hM := cellMass_pos hπ σ s
  have e : ∀ z : Fin S → α, ∑ t, posterior π σ s t * u t (z t) =
      (∑ t, if σ t = σ s then π t * u t (z t) else 0) / cellMass π σ s := by
    intro z
    unfold posterior
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun t _ => by split_ifs <;> ring
  rw [e, e]
  exact div_le_div_of_nonneg_right key hM.le

/-! ## Example 19.H.1 (Hirshleifer) -/

/-- **Example 19.H.1** (MWG, pp. 718-719), no information: both consumers maximize
`½√x₁ + ½√x₂`; at prices `(1, 1)` each consumer gets `(½, ½)`, an equilibrium, with expected
utility `1/√2 = √(1/2)`. -/
theorem example_19_H_1_noinfo :
    IsSpotEqm (fun (_ : Fin 2) (y : Fin 2 → ℝ) => 1 / 2 * √(y 0) + 1 / 2 * √(y 1))
        ![![1, 0], ![0, 1]] ![1, 1] ![![1 / 2, 1 / 2], ![1 / 2, 1 / 2]] ∧
      1 / 2 * √(1 / 2 : ℝ) + 1 / 2 * √(1 / 2) = √(1 / 2) := by
  refine ⟨⟨fun i => ⟨⟨fun l => ?_, ?_⟩, fun y hy hb => ?_⟩, fun l => ?_⟩, by ring⟩
  · fin_cases i <;> fin_cases l <;> norm_num
  · fin_cases i <;> simp [dotProduct, Fin.sum_univ_two] <;> norm_num
  · have hb' : y 0 + y 1 ≤ 1 := by
      fin_cases i <;> simpa [dotProduct, Fin.sum_univ_two] using hb
    have h0 := hy 0; have h1 := hy 1
    have hs : (√(y 0) + √(y 1)) ^ 2 ≤ 2 := by
      have e0 := Real.sq_sqrt h0; have e1 := Real.sq_sqrt h1
      nlinarith [sq_nonneg (√(y 0) - √(y 1)), Real.sqrt_nonneg (y 0), Real.sqrt_nonneg (y 1)]
    have hle : 1 / 2 * √(y 0) + 1 / 2 * √(y 1) ≤ √(1 / 2) := by
      rw [show 1 / 2 * √(y 0) + 1 / 2 * √(y 1) = (√(y 0) + √(y 1)) / 2 by ring]
      apply Real.le_sqrt_of_sq_le
      nlinarith
    fin_cases i <;>
      (change 1 / 2 * √(y 0) + 1 / 2 * √(y 1) ≤ 1 / 2 * √(1 / 2) + 1 / 2 * √(1 / 2)
       linarith [hle])
  · fin_cases l <;> simp [Fin.sum_univ_two] <;> norm_num

/-- In any spot equilibrium where both consumers value only good `0` (utility `√y₀`), the
consumer owning the unit of good `0` consumes it all and the other consumes none: utilities `1`
and `0` (perfect information, state 1 of Example 19.H.1). -/
theorem example_19_H_1_state1 {p : Fin 2 → ℝ} {y : Fin 2 → Fin 2 → ℝ}
    (h : IsSpotEqm (fun (_ : Fin 2) (v : Fin 2 → ℝ) => √(v 0)) ![![1, 0], ![0, 1]] p y) :
    √(y 0 0) = 1 ∧ √(y 1 0) = 0 := by
  obtain ⟨hc, hclear⟩ := h
  obtain ⟨⟨hy0, hb0⟩, hopt0⟩ := hc 0
  obtain ⟨⟨hy1, -⟩, -⟩ := hc 1
  simp only [Matrix.cons_val_zero, dotProduct, Fin.sum_univ_two, Matrix.cons_val_one] at hb0 hopt0
  simp only [mul_one, mul_zero, add_zero] at hb0 hopt0
  have hp0 : 0 < p 0 := by
    by_contra hle
    push Not at hle
    have := hopt0 ![y 0 0 + 1, 0] (fun l => by
      fin_cases l
      · change 0 ≤ y 0 0 + 1; linarith [hy0 0]
      · simp)
      (by change p 0 * (y 0 0 + 1) + p 1 * 0 ≤ p 0; nlinarith [hy0 0])
    change √(y 0 0 + 1) ≤ √(y 0 0) at this
    linarith [Real.sqrt_lt_sqrt (hy0 0) (lt_add_one (y 0 0))]
  have hp1 : 0 ≤ p 1 := by
    by_contra hneg
    push Not at hneg
    have := hopt0 ![y 0 0 + 1, p 0 * y 0 0 / (-p 1)]
      (fun l => by
        fin_cases l
        · change 0 ≤ y 0 0 + 1; linarith [hy0 0]
        · change 0 ≤ p 0 * y 0 0 / (-p 1)
          exact div_nonneg (mul_nonneg hp0.le (hy0 0)) (by linarith))
      (by
        change p 0 * (y 0 0 + 1) + p 1 * (p 0 * y 0 0 / (-p 1)) ≤ p 0
        have : p 1 * (p 0 * y 0 0 / (-p 1)) = -(p 0 * y 0 0) := by
          have := hneg.ne; field_simp
        linarith)
    change √(y 0 0 + 1) ≤ √(y 0 0) at this
    linarith [Real.sqrt_lt_sqrt (hy0 0) (lt_add_one (y 0 0))]
  have hle1 : y 0 0 ≤ 1 := by nlinarith [hy0 1]
  have hge1 : 1 ≤ y 0 0 := by
    have := hopt0 ![1, 0] (fun l => by fin_cases l <;> simp) (by simp)
    change √1 ≤ √(y 0 0) at this
    rwa [Real.sqrt_one, Real.one_le_sqrt] at this
  have hy00 : y 0 0 = 1 := le_antisymm hle1 hge1
  have hy10 : y 1 0 = 0 := by
    have := hclear 0
    simp [Fin.sum_univ_two] at this
    linarith [hy1 0]
  exact ⟨by rw [hy00, Real.sqrt_one], by rw [hy10, Real.sqrt_zero]⟩

/-- In state 2 of Example 19.H.1 only good `1` is valued; its owner (consumer 2) gets utility `1`
and consumer 1 gets `0`. -/
theorem example_19_H_1_state2 {p : Fin 2 → ℝ} {y : Fin 2 → Fin 2 → ℝ}
    (h : IsSpotEqm (fun (_ : Fin 2) (v : Fin 2 → ℝ) => √(v 1)) ![![1, 0], ![0, 1]] p y) :
    √(y 1 1) = 1 ∧ √(y 0 1) = 0 := by
  obtain ⟨hc, hclear⟩ := h
  obtain ⟨⟨hy1, hb1⟩, hopt1⟩ := hc 1
  obtain ⟨⟨hy0, -⟩, -⟩ := hc 0
  simp only [Matrix.cons_val_one, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero] at hb1 hopt1
  simp only [mul_one, mul_zero, zero_add] at hb1 hopt1
  have hp1 : 0 < p 1 := by
    by_contra hle
    push Not at hle
    have := hopt1 ![0, y 1 1 + 1] (fun l => by
      fin_cases l
      · simp
      · change 0 ≤ y 1 1 + 1; linarith [hy1 1])
      (by change p 0 * 0 + p 1 * (y 1 1 + 1) ≤ p 1; nlinarith [hy1 1])
    change √(y 1 1 + 1) ≤ √(y 1 1) at this
    linarith [Real.sqrt_lt_sqrt (hy1 1) (lt_add_one (y 1 1))]
  have hp0 : 0 ≤ p 0 := by
    by_contra hneg
    push Not at hneg
    have := hopt1 ![p 1 * y 1 1 / (-p 0), y 1 1 + 1]
      (fun l => by
        fin_cases l
        · change 0 ≤ p 1 * y 1 1 / (-p 0)
          exact div_nonneg (mul_nonneg hp1.le (hy1 1)) (by linarith)
        · change 0 ≤ y 1 1 + 1; linarith [hy1 1])
      (by
        change p 0 * (p 1 * y 1 1 / (-p 0)) + p 1 * (y 1 1 + 1) ≤ p 1
        have : p 0 * (p 1 * y 1 1 / (-p 0)) = -(p 1 * y 1 1) := by
          have := hneg.ne; field_simp
        linarith)
    change √(y 1 1 + 1) ≤ √(y 1 1) at this
    linarith [Real.sqrt_lt_sqrt (hy1 1) (lt_add_one (y 1 1))]
  have hle1 : y 1 1 ≤ 1 := by nlinarith [hy1 0]
  have hge1 : 1 ≤ y 1 1 := by
    have := hopt1 ![0, 1] (fun l => by fin_cases l <;> simp) (by simp)
    change √1 ≤ √(y 1 1) at this
    rwa [Real.sqrt_one, Real.one_le_sqrt] at this
  have hy11 : y 1 1 = 1 := le_antisymm hle1 hge1
  have hy01 : y 0 1 = 0 := by
    have := hclear 1
    simp [Fin.sum_univ_two] at this
    linarith [hy0 1]
  exact ⟨by rw [hy11, Real.sqrt_one], by rw [hy01, Real.sqrt_zero]⟩

/-- **Example 19.H.1** (MWG, p. 719). With perfect information each consumer gets utility `1` in one
state and `0` in the other at every spot equilibrium, hence an ex ante utility of `1/2`, which is
less than the `1/√2` of the no-information equilibrium: better information makes everybody worse
off. -/
theorem example_19_H_1 {p₁ p₂ : Fin 2 → ℝ} {y₁ y₂ : Fin 2 → Fin 2 → ℝ}
    (h₁ : IsSpotEqm (fun (_ : Fin 2) (v : Fin 2 → ℝ) => √(v 0)) ![![1, 0], ![0, 1]] p₁ y₁)
    (h₂ : IsSpotEqm (fun (_ : Fin 2) (v : Fin 2 → ℝ) => √(v 1)) ![![1, 0], ![0, 1]] p₂ y₂) :
    1 / 2 * √(y₁ 0 0) + 1 / 2 * √(y₂ 0 1) = 1 / 2 ∧
      1 / 2 * √(y₁ 1 0) + 1 / 2 * √(y₂ 1 1) = 1 / 2 ∧ (1 / 2 : ℝ) < √(1 / 2) := by
  obtain ⟨a1, a2⟩ := example_19_H_1_state1 h₁
  obtain ⟨b1, b2⟩ := example_19_H_1_state2 h₂
  refine ⟨by rw [a1, b2]; ring, by rw [a2, b1]; ring, ?_⟩
  rw [Real.lt_sqrt (by norm_num)]
  norm_num

end MWG.EquilibriumUncertainty
