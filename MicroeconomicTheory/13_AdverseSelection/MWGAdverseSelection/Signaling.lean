/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGAdverseSelection.WageGame

/-!
# The education signaling model

MWG, Section 13.C, pp. 450-453.

Two types `θ_L < θ_H` (`true` is the high type), `λ = Prob(θ = θ_H) ∈ (0, 1)`, home earnings
`r` (the main text has `r = 0`, the small type on p. 459 has `r ∈ (θ_L, θ_H)`; we allow any
`0 ≤ r < θ_H`), and education cost `c(e, θ)`. A worker of type `θ` choosing `e` and earning `w`
gets `w - c(e, θ)`.

Assumptions (`SigModel.Valid`). From the book's assumptions on `c` we use: `c(0, θ) = 0`,
`c(·, θ)` strictly increasing on `e ≥ 0` (`c_e > 0`), and the single-crossing property in the
integrated form `c(e', θ_H) - c(e, θ_H) < c(e', θ_L) - c(e, θ_L)` for `0 ≤ e < e'` (implied by
`c_{eθ} < 0`). `c_θ < 0` then follows
(`c_lt_of_pos`). Convexity (`c_ee > 0`) is not needed.

The game (Figure 13.C.1): nature draws the type, the worker chooses `e ≥ 0`, two firms see `e`
and simultaneously offer wages, the worker accepts a highest offer if it is at least `r`.
Education is a continuous choice, so the game is not one of the finite extensive forms of
Chapter 9; we use the book's equivalent definition of a pure strategy perfect Bayesian
equilibrium (p. 452, conditions (i)-(iii)), with condition (iii) a Nash equilibrium of the
Chapter 8 wage game `wageGame` (`IsPBE`).

* `bertrand_wage`: in the wage game after `e` with belief `μ(e)`, every Nash equilibrium gives
  the worker `max(μ(e)θ_H + (1 - μ(e))θ_L, r)` (p. 452: both firms offer the expected
  productivity when it is at least `r`).
* `pbe_iff`: a PBE is the same as an education strategy and beliefs satisfying Bayes' rule on
  the path such that each type's education is optimal against the wage schedule
  `w(e) = μ(e)θ_H + (1 - μ(e))θ_L`.
-/

namespace MWG.AdverseSelection

open Set MWG.SimultaneousMoveGames

/-- **Section 13.C** (MWG, p. 450). The two-type signaling model: types `θ_L`, `θ_H`, the
probability `λ` of `θ_H`, home earnings `r` and the education cost `c(e, θ)`. -/
structure SigModel where
  θL : ℝ
  θH : ℝ
  lam : ℝ
  r : ℝ
  c : ℝ → ℝ → ℝ

namespace SigModel

/-- The productivity of type `b` (`true` = high). -/
def θ (M : SigModel) (b : Bool) : ℝ := if b then M.θH else M.θL

/-- `E[θ] = λθ_H + (1 - λ)θ_L`. -/
def Eθ (M : SigModel) : ℝ := M.lam * M.θH + (1 - M.lam) * M.θL

/-- Expected productivity `μθ_H + (1 - μ)θ_L` when the firms' belief that the worker is of high
ability is `μ`. -/
def expProd (M : SigModel) (m : ℝ) : ℝ := m * M.θH + (1 - m) * M.θL

/-- **Section 13.C** (MWG, p. 450). The assumptions on the model. -/
structure Valid (M : SigModel) : Prop where
  θL_pos : 0 < M.θL
  lt : M.θL < M.θH
  lam_pos : 0 < M.lam
  lam_lt : M.lam < 1
  r_nonneg : 0 ≤ M.r
  r_lt : M.r < M.θH
  c_zero : ∀ θ, M.c 0 θ = 0
  c_mono : ∀ b, StrictMonoOn (fun e => M.c e (M.θ b)) (Ici 0)
  c_cont : ∀ b, ContinuousOn (fun e => M.c e (M.θ b)) (Ici 0)
  sc : ∀ e e', 0 ≤ e → e < e' → M.c e' M.θH - M.c e M.θH < M.c e' M.θL - M.c e M.θL

/-- A firm's profit from offering `w` after education `e` when the expected productivity is
`p`: the worker accepts iff `w ≥ r`. -/
noncomputable def offerProfit (M : SigModel) (p : ℝ) (w : ℝ) : ℝ := if M.r ≤ w then p - w else 0

/-- **Section 13.C** (MWG, p. 451). The worker's payoff when she is of type `b`, chooses `e` and
faces the offers `w`: she accepts a highest offer if it is at least `r`. -/
def workerPay (M : SigModel) (b : Bool) (w : Fin 2 → ℝ) (e : ℝ) : ℝ :=
  max (max (w 0) (w 1)) M.r - M.c e (M.θ b)

/-- **Section 13.C** (MWG, p. 452). Beliefs derived from the worker's strategy by Bayes' rule
on the equilibrium path: after the high type's education the belief is `1` if the types
separate and `λ` if they pool; after the low type's education it is `0` if they separate. -/
def BayesOnPath (M : SigModel) (eS : Bool → ℝ) (μ : ℝ → ℝ) : Prop :=
  (eS false ≠ eS true → μ (eS true) = 1 ∧ μ (eS false) = 0) ∧
    (eS false = eS true → μ (eS true) = M.lam)

/-- **Section 13.C** (MWG, p. 452). A pure strategy perfect Bayesian equilibrium of the
education signaling game: education choices `e*(θ) ≥ 0`, beliefs `μ(e) ∈ [0, 1]` and wage
offers `w_j(e)` such that (i) each type's education choice is optimal given the firms'
strategies, (ii) beliefs follow Bayes' rule on the path, (iii) after every `e` the offers are a
Nash equilibrium of the firms' wage game with expected productivity `μ(e)θ_H + (1 - μ(e))θ_L`. -/
def IsPBE (M : SigModel) (eS : Bool → ℝ) (μ : ℝ → ℝ) (wO : ℝ → Fin 2 → ℝ) : Prop :=
  (∀ b, 0 ≤ eS b) ∧ (∀ e, 0 ≤ μ e ∧ μ e ≤ 1) ∧
    (∀ b e, 0 ≤ e → M.workerPay b (wO e) e ≤ M.workerPay b (wO (eS b)) (eS b)) ∧
    M.BayesOnPath eS μ ∧
    ∀ e, 0 ≤ e → IsNashEquilibrium (wageGame (M.offerProfit (M.expProd (μ e)))) (wO e)

/-- A separating equilibrium: the two types choose different education levels. -/
def Separating (eS : Bool → ℝ) : Prop := eS false ≠ eS true

/-- A pooling equilibrium: the two types choose the same education level. -/
def Pooling (eS : Bool → ℝ) : Prop := eS false = eS true

variable {M : SigModel}

theorem θ_true (M : SigModel) : M.θ true = M.θH := rfl
theorem θ_false (M : SigModel) : M.θ false = M.θL := rfl

/-- Expected productivity lies in `[θ_L, θ_H]`. -/
theorem Valid.expProd_mem (hM : M.Valid) {m : ℝ} (h0 : 0 ≤ m) (h1 : m ≤ 1) :
    M.θL ≤ M.expProd m ∧ M.expProd m ≤ M.θH := by
  unfold expProd
  constructor <;> nlinarith [hM.lt]

theorem expProd_one (M : SigModel) : M.expProd 1 = M.θH := by simp [expProd]
theorem expProd_zero (M : SigModel) : M.expProd 0 = M.θL := by simp [expProd]
theorem expProd_lam (M : SigModel) : M.expProd M.lam = M.Eθ := by simp [expProd, Eθ]

/-- `θ_L < E[θ] < θ_H`. -/
theorem Valid.Eθ_mem (hM : M.Valid) : M.θL < M.Eθ ∧ M.Eθ < M.θH := by
  unfold Eθ
  constructor <;> nlinarith [hM.lt, hM.lam_pos, hM.lam_lt]

/-- `c(e, θ_H) < c(e, θ_L)` for `e > 0` (`c_θ < 0`). -/
theorem Valid.c_lt_of_pos (hM : M.Valid) {e : ℝ} (he : 0 < e) : M.c e M.θH < M.c e M.θL := by
  have := hM.sc 0 e le_rfl he
  rw [hM.c_zero, hM.c_zero] at this
  linarith

/-- `c(e, θ_H) ≤ c(e, θ_L)` for `e ≥ 0`. -/
theorem Valid.c_le (hM : M.Valid) {e : ℝ} (he : 0 ≤ e) : M.c e M.θH ≤ M.c e M.θL := by
  rcases eq_or_lt_of_le he with h | h
  · rw [← h, hM.c_zero, hM.c_zero]
  · exact (hM.c_lt_of_pos h).le

/-- `c(e, θ) ≥ 0` for `e ≥ 0`, and `> 0` for `e > 0`. -/
theorem Valid.c_pos (hM : M.Valid) (b : Bool) {e : ℝ} (he : 0 < e) : 0 < M.c e (M.θ b) := by
  have := hM.c_mono b (le_refl (0 : ℝ)) he.le he
  simp only [hM.c_zero] at this
  exact this

theorem Valid.c_nonneg (hM : M.Valid) (b : Bool) {e : ℝ} (he : 0 ≤ e) : 0 ≤ M.c e (M.θ b) := by
  rcases eq_or_lt_of_le he with h | h
  · rw [← h, hM.c_zero]
  · exact (hM.c_pos b h).le

/-- The firm's profit in the wage game is right-continuous. -/
theorem offerProfit_rc (M : SigModel) (p x : ℝ) :
    ContinuousWithinAt (M.offerProfit p) (Ici x) x := by
  by_cases hx : M.r ≤ x
  · have hc : ContinuousWithinAt (fun y : ℝ => p - y) (Ici x) x :=
      (continuous_const.sub continuous_id).continuousWithinAt
    refine hc.congr (fun y hy => ?_) ?_
    · simp [offerProfit, hx.trans hy]
    · simp [offerProfit, hx]
  · have hc : ContinuousWithinAt (fun _ : ℝ => (0 : ℝ)) (Ici x) x := continuousWithinAt_const
    refine hc.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds (not_le.1 hx))] with y hy
      simp [offerProfit, not_le.2 (show y < M.r from hy)]
    · simp [offerProfit, hx]

/-- **Section 13.C** (MWG, p. 452). The Nash equilibria of the wage game after education `e`
with expected productivity `p ≥ 0`: if `p > r` both firms offer exactly `p` (Bertrand); if
`p = r`, any offers `≤ r`; if `p < r`, any offers `< r` (no worker accepts). -/
theorem bertrand_iff (M : SigModel) {p : ℝ} (hp : 0 ≤ p) (w : Fin 2 → ℝ) :
    IsNashEquilibrium (wageGame (M.offerProfit p)) w ↔
      (M.r < p → w 0 = p ∧ w 1 = p) ∧ (M.r = p → w 0 ≤ p ∧ w 1 ≤ p) ∧
        (p < M.r → w 0 < M.r ∧ w 1 < M.r) := by
  rcases lt_trichotomy M.r p with hlt | heq | hgt
  · rw [wageGame_unique (M.offerProfit_rc p) (by unfold offerProfit; split_ifs <;> linarith)
      (ws := p) (ε := p - M.r) (by linarith) (by simp [offerProfit, hlt.le])
      (fun w hw => by simp [offerProfit, hlt.le.trans hw.le]; linarith)
      (fun w h1 h2 => by simp [offerProfit, show M.r ≤ w by linarith]; linarith) w]
    simp [hlt, hlt.ne, not_lt.2 hlt.le]
  · rw [wageGame_flat (ws := M.r) (fun t ht => by
      unfold offerProfit; split_ifs with h
      · rw [← heq, le_antisymm ht h, sub_self]
      · rfl) (fun t ht => by simp [offerProfit, ht.le]; linarith) w]
    simp [heq]
  · rw [wageGame_flat_open (ws := M.r) (fun t ht => by simp [offerProfit, not_le.2 ht])
      (fun t ht => by simp [offerProfit, ht]; linarith) w]
    simp [hgt, hgt.ne', not_lt.2 hgt.le]

/-- **Section 13.C** (MWG, p. 452). In every Nash equilibrium of the wage game with expected
productivity `p ≥ 0` the worker ends up with `max(p, r)`. -/
theorem bertrand_wage (M : SigModel) {p : ℝ} (hp : 0 ≤ p) (w : Fin 2 → ℝ)
    (hne : IsNashEquilibrium (wageGame (M.offerProfit p)) w) :
    max (max (w 0) (w 1)) M.r = max p M.r := by
  obtain ⟨h1, h2, h3⟩ := (M.bertrand_iff hp w).1 hne
  rcases lt_trichotomy M.r p with hlt | heq | hgt
  · rw [(h1 hlt).1, (h1 hlt).2, max_self]
  · rw [max_eq_right (max_le ((h2 heq).1.trans heq.ge) ((h2 heq).2.trans heq.ge)), heq,
      max_self]
  · rw [max_eq_right (max_le (h3 hgt).1.le (h3 hgt).2.le), max_eq_right hgt.le]

/-- **Section 13.C** (MWG, p. 452). The wage game always has a pure Nash equilibrium: both
firms offer `p` if `p ≥ r`, and `r - 1` otherwise. -/
noncomputable def bertrandOffer (M : SigModel) (p : ℝ) : Fin 2 → ℝ :=
  fun _ => if M.r ≤ p then p else M.r - 1

theorem bertrandOffer_nash (M : SigModel) {p : ℝ} (hp : 0 ≤ p) :
    IsNashEquilibrium (wageGame (M.offerProfit p)) (M.bertrandOffer p) := by
  rw [M.bertrand_iff hp]
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · simp [bertrandOffer, h.le]
  · simp [bertrandOffer, h.le]
  · simp [bertrandOffer, not_le.2 h]

theorem bertrandOffer_max (M : SigModel) (p : ℝ) :
    max (max (M.bertrandOffer p 0) (M.bertrandOffer p 1)) M.r = max p M.r := by
  unfold bertrandOffer
  split_ifs with h
  · simp [max_eq_left h]
  · simp [max_eq_right (not_le.1 h).le]

/-- The worker's payoff from education `e` against the equilibrium wage schedule
`w(e) = μ(e)θ_H + (1 - μ(e))θ_L` (she works at home if `w(e) < r`). -/
def redPay (M : SigModel) (μ : ℝ → ℝ) (b : Bool) (e : ℝ) : ℝ :=
  max (M.expProd (μ e)) M.r - M.c e (M.θ b)

/-- **Section 13.C** (MWG, pp. 452-453). The reduced form of a PBE: education choices `≥ 0`,
beliefs in `[0, 1]` derived by Bayes' rule on the path, and each type's education optimal
against the wage schedule `w(e) = μ(e)θ_H + (1 - μ(e))θ_L`. -/
def IsPBERed (M : SigModel) (eS : Bool → ℝ) (μ : ℝ → ℝ) : Prop :=
  (∀ b, 0 ≤ eS b) ∧ (∀ e, 0 ≤ μ e ∧ μ e ≤ 1) ∧
    (∀ b e, 0 ≤ e → M.redPay μ b e ≤ M.redPay μ b (eS b)) ∧ M.BayesOnPath eS μ

/-- **Section 13.C** (MWG, p. 452). A PBE gives the worker `w(e) = max(μ(e)θ_H + (1-μ(e))θ_L, r)`
after every education level, so its strategies and beliefs form a reduced-form PBE. -/
theorem Valid.isPBERed_of_isPBE (hM : M.Valid) {eS : Bool → ℝ} {μ : ℝ → ℝ}
    {wO : ℝ → Fin 2 → ℝ} (h : M.IsPBE eS μ wO) : M.IsPBERed eS μ := by
  obtain ⟨h0, hμ, hopt, hB, hNE⟩ := h
  have hw : ∀ e, 0 ≤ e → max (max (wO e 0) (wO e 1)) M.r = max (M.expProd (μ e)) M.r :=
    fun e he => M.bertrand_wage (hM.θL_pos.le.trans (hM.expProd_mem (hμ e).1 (hμ e).2).1)
      _ (hNE e he)
  refine ⟨h0, hμ, fun b e he => ?_, hB⟩
  have := hopt b e he
  unfold workerPay at this
  rw [hw e he, hw _ (h0 b)] at this
  exact this

/-- **Section 13.C** (MWG, p. 452). Conversely, a reduced-form PBE with the Bertrand offers
`bertrandOffer` is a PBE. -/
theorem Valid.isPBE_of_isPBERed (hM : M.Valid) {eS : Bool → ℝ} {μ : ℝ → ℝ}
    (h : M.IsPBERed eS μ) : M.IsPBE eS μ (fun e => M.bertrandOffer (M.expProd (μ e))) := by
  obtain ⟨h0, hμ, hopt, hB⟩ := h
  refine ⟨h0, hμ, fun b e he => ?_, hB, fun e _ => M.bertrandOffer_nash
    (hM.θL_pos.le.trans (hM.expProd_mem (hμ e).1 (hμ e).2).1)⟩
  unfold workerPay
  rw [bertrandOffer_max, bertrandOffer_max]
  exact hopt b e he

/-- **Section 13.C** (MWG, p. 452). Strategies and beliefs are part of a PBE iff they form a
reduced-form PBE. -/
theorem Valid.exists_isPBE_iff (hM : M.Valid) (eS : Bool → ℝ) (μ : ℝ → ℝ) :
    (∃ wO, M.IsPBE eS μ wO) ↔ M.IsPBERed eS μ :=
  ⟨fun ⟨_, h⟩ => hM.isPBERed_of_isPBE h, fun h => ⟨_, hM.isPBE_of_isPBERed h⟩⟩

/-- **Section 13.C** (MWG, p. 453). In any PBE the wage after every education level lies in
`[θ_L, θ_H]`. -/
theorem Valid.wage_mem (hM : M.Valid) {μ : ℝ → ℝ} (hμ : ∀ e, 0 ≤ μ e ∧ μ e ≤ 1) (e : ℝ) :
    M.θL ≤ M.expProd (μ e) ∧ M.expProd (μ e) ≤ M.θH :=
  hM.expProd_mem (hμ e).1 (hμ e).2

end SigModel

end MWG.AdverseSelection
