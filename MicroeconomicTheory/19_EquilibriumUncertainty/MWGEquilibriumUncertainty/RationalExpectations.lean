/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGEquilibriumUncertainty.Information

/-!
# Rational expectations equilibrium (MWG Section 19.H, pp. 719-724, Exercises 19.H.4, 19.H.7)

* **Definition 19.H.2** in general form: a price function `P` is a rational expectations
  equilibrium price function if for every state the price clears the spot market when every
  consumer knows the event `{s' : P(s') = P(s), σᵢ(s') = σᵢ(s)}` (`IsREE`, for any notion of
  market clearing `Clears`). The pooled information price function, full revelation, and the
  theorem of p. 721: a fully revealing pooled information price function is a rational
  expectations equilibrium (`pooled_fullyRevealing_isREE`).
* The quasilinear economies of Examples 19.H.2-19.H.5 and Exercise 19.H.7: utilities
  `β_{s} ln x₁ + x₂`, updated utilities `∑_{s'} π(s'|E) u_{s'}`, demand `x₁ = b/p` (`qlOptimal_iff`)
  and the clearing price `p = ∑ bᵢ / ∑ eᵢ` (`qlSpotEqm_iff`).
* **Example 19.H.2**: the naive price `p(β) = (3 + 2β)/4` reveals `β` and is not a rational
  expectations equilibrium; the pooled price `β` is (`example_19_H_2`, `example_19_H_2_continued`).
* **Example 19.H.3** (Kreps): no rational expectations equilibrium exists (`example_19_H_3`).
* Examples 19.H.4-19.H.6 and Exercises 19.H.4-19.H.7 are in `REExamples`.
-/

namespace MWG.EquilibriumUncertainty

variable {S : ℕ} {ι : Type*} [Fintype ι]

/-! ## Definition 19.H.2 and the pooled information price function -/

variable {β : Type*} [DecidableEq β]

/-- The event `{s' : P(s') = P(s), σᵢ(s') = σᵢ(s)}` known to consumer `i` at `s` (p. 720). -/
noncomputable def reeEvent (P : Fin S → ℝ) (σ : ι → Fin S → β) (i : ι) (s : Fin S) :
    Finset (Fin S) :=
  Finset.univ.filter fun s' => P s' = P s ∧ σ i s' = σ i s

/-- The pooled information event `{s' : σ_k(s') = σ_k(s) for all k}` (p. 721). -/
def pooledEvent (σ : ι → Fin S → β) (s : Fin S) : Finset (Fin S) :=
  Finset.univ.filter fun s' => ∀ k, σ k s' = σ k s

/-- **Definition 19.H.2** (MWG, p. 721). `P` is a rational expectations equilibrium price function
if for every `s`, `P(s)` clears the spot market when every consumer `i` knows that
`s ∈ E_{P(s), σᵢ(s)}` and evaluates bundles with the updated utility. Market clearing given the
consumers' events is the parameter `Clears s E p`. -/
def IsREE (Clears : Fin S → (ι → Finset (Fin S)) → ℝ → Prop) (P : Fin S → ℝ)
    (σ : ι → Fin S → β) : Prop :=
  ∀ s, Clears s (fun i => reeEvent P σ i s) (P s)

/-- **p. 721**. The pooled information equilibrium price function: `P(s)` clears the market when
every consumer knows the vector of all signals. -/
def IsPooledPrice (Clears : Fin S → (ι → Finset (Fin S)) → ℝ → Prop) (P : Fin S → ℝ)
    (σ : ι → Fin S → β) : Prop :=
  ∀ s, Clears s (fun _ => pooledEvent σ s) (P s)

/-- **p. 721**. `P` is fully revealing: it distinguishes any two states distinguished by some
consumer. -/
def FullyRevealing (P : Fin S → ℝ) (σ : ι → Fin S → β) : Prop :=
  ∀ s s', (∃ i, σ i s ≠ σ i s') → P s ≠ P s'

/-- **p. 721**. The price depends only on the vector of signals, `P(s) = P̂(σ₁(s), …, σ_I(s))`. -/
def DependsOnSignals (P : Fin S → ℝ) (σ : ι → Fin S → β) : Prop :=
  ∀ s s', (∀ i, σ i s = σ i s') → P s = P s'

/-- **p. 721**. A fully revealing pooled information price function generates, for every consumer,
exactly the pooled event. -/
theorem reeEvent_eq_pooled {P : Fin S → ℝ} {σ : ι → Fin S → β} (hfr : FullyRevealing P σ)
    (hdep : DependsOnSignals P σ) (i : ι) (s : Fin S) : reeEvent P σ i s = pooledEvent σ s := by
  ext s'
  simp only [reeEvent, pooledEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hP, -⟩ k
    by_contra hk
    exact hfr s' s ⟨k, hk⟩ hP
  · intro h
    exact ⟨hdep s' s h, h i⟩

/-- **p. 721**. If the pooled information equilibrium price function is fully revealing, it is a
rational expectations equilibrium price function: the information used by consumers is obtained
from the public price signal. -/
theorem pooled_fullyRevealing_isREE {Clears : Fin S → (ι → Finset (Fin S)) → ℝ → Prop}
    {P : Fin S → ℝ} {σ : ι → Fin S → β} (hpool : IsPooledPrice Clears P σ)
    (hfr : FullyRevealing P σ) (hdep : DependsOnSignals P σ) : IsREE Clears P σ := by
  intro s
  have : (fun i => reeEvent P σ i s) = fun _ => pooledEvent σ s :=
    funext fun i => reeEvent_eq_pooled hfr hdep i s
  rw [this]
  exact hpool s

/-! ## Quasilinear economies -/

/-- The bundle `y = (y₁, y₂)` maximizes `b ln y₁ + y₂` on `{y₁ > 0, p y₁ + y₂ ≤ p e}`. -/
def QLOptimal (b p e : ℝ) (y : ℝ × ℝ) : Prop :=
  0 < y.1 ∧ p * y.1 + y.2 ≤ p * e ∧
    ∀ y' : ℝ × ℝ, 0 < y'.1 → p * y'.1 + y'.2 ≤ p * e → b * Real.log y'.1 + y'.2 ≤
      b * Real.log y.1 + y.2

/-- The demand of a quasilinear consumer: `y₁ = b/p`, `y₂ = p e - b`. -/
theorem qlOptimal_iff {b p e : ℝ} (hb : 0 < b) (hp : 0 < p) (y : ℝ × ℝ) :
    QLOptimal b p e y ↔ y.1 = b / p ∧ y.2 = p * e - b := by
  constructor
  · rintro ⟨hy, hbud, hmax⟩
    have hbp : 0 < b / p := div_pos hb hp
    have h1 := hmax (b / p, p * e - b) hbp (by simp; field_simp; linarith)
    exact quasilinearLog_eq_iff hb hp hy hbud (by simpa using h1.trans_eq' (by ring))
  · rintro ⟨h1, h2⟩
    have hbp : 0 < b / p := div_pos hb hp
    refine ⟨h1 ▸ hbp, by rw [h1, h2]; field_simp; linarith, fun y' hy' hb' => ?_⟩
    rw [h1, h2]
    have := quasilinearLog_le hb hp hy' hb'
    linarith

/-- A quasilinear consumer with `b > 0` has no optimal bundle when `p ≤ 0`. -/
theorem qlOptimal_price_pos {b p e : ℝ} (hb : 0 < b) {y : ℝ × ℝ} (h : QLOptimal b p e y) :
    0 < p := by
  by_contra hp
  push Not at hp
  have := h.2.2 (y.1 + 1, y.2) (by linarith [h.1]) (by simp; nlinarith [h.2.1])
  have hlog := Real.log_lt_log h.1 (lt_add_one y.1)
  simp at this
  nlinarith

/-- A spot equilibrium price of the quasilinear economy with coefficients `bᵢ` and endowments `eᵢ`
of good 1: optimal bundles that clear the market for good 1. -/
def QLSpotEqm (b e : ι → ℝ) (p : ℝ) : Prop :=
  ∃ y : ι → ℝ × ℝ, (∀ i, QLOptimal (b i) p (e i) (y i)) ∧ ∑ i, (y i).1 = ∑ i, e i

/-- The spot equilibrium price is `p = ∑ bᵢ / ∑ eᵢ` (with `bᵢ > 0`, `∑ eᵢ > 0`). -/
theorem qlSpotEqm_iff {b e : ι → ℝ} (hb : ∀ i, 0 < b i) (he : 0 < ∑ i, e i) (p : ℝ) :
    QLSpotEqm b e p ↔ p = (∑ i, b i) / ∑ i, e i := by
  constructor
  · rintro ⟨y, hy, hcl⟩
    obtain ⟨i₀⟩ : Nonempty ι := by
      by_contra h; rw [not_nonempty_iff] at h; simp at he
    have hp := qlOptimal_price_pos (hb i₀) (hy i₀)
    have h1 : ∀ i, (y i).1 = b i / p := fun i => ((qlOptimal_iff (hb i) hp _).mp (hy i)).1
    simp only [h1, ← Finset.sum_div] at hcl
    rw [eq_div_iff he.ne']
    field_simp at hcl
    linarith
  · intro hp
    have hbs : 0 < ∑ i, b i := by
      obtain ⟨i₀⟩ : Nonempty ι := by
        by_contra h; rw [not_nonempty_iff] at h; simp at he
      exact Finset.sum_pos (fun i _ => hb i) ⟨i₀, Finset.mem_univ _⟩
    have hp0 : 0 < p := by rw [hp]; exact div_pos hbs he
    refine ⟨fun i => (b i / p, p * e i - b i), fun i => (qlOptimal_iff (hb i) hp0 _).mpr
      ⟨rfl, rfl⟩, ?_⟩
    simp only [← Finset.sum_div]
    rw [div_eq_iff hp0.ne', hp]
    field_simp

/-- The posterior mean coefficient `∑_{s∈E} π_s β_s / ∑_{s∈E} π_s`. -/
noncomputable def postCoef (π β : Fin S → ℝ) (E : Finset (Fin S)) : ℝ :=
  (∑ s ∈ E, π s * β s) / ∑ s ∈ E, π s

/-- The updated utility `∑_{s' ∈ E} (π_{s'} / π(E)) (β_{s'} ln y₁ + y₂)` (Definition 19.H.2). -/
noncomputable def updU (π β : Fin S → ℝ) (E : Finset (Fin S)) (y : ℝ × ℝ) : ℝ :=
  ∑ s ∈ E, π s / (∑ t ∈ E, π t) * (β s * Real.log y.1 + y.2)

/-- The updated utility is `postCoef · ln y₁ + y₂`. -/
theorem updU_eq {π : Fin S → ℝ} (hπ : ∀ s, 0 < π s) (β : Fin S → ℝ) {E : Finset (Fin S)}
    (hE : E.Nonempty) (y : ℝ × ℝ) :
    updU π β E y = postCoef π β E * Real.log y.1 + y.2 := by
  have hM : 0 < ∑ t ∈ E, π t := Finset.sum_pos (fun t _ => hπ t) hE
  unfold updU postCoef
  have e : ∀ s ∈ E, π s / (∑ t ∈ E, π t) * (β s * Real.log y.1 + y.2) =
      π s * β s / (∑ t ∈ E, π t) * Real.log y.1 + π s / (∑ t ∈ E, π t) * y.2 :=
    fun s _ => by ring
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
    ← Finset.sum_div, ← Finset.sum_div, div_self hM.ne', one_mul]

/-- Market clearing in the quasilinear economy at state `s` when consumer `i` knows the event
`E i`: optimal bundles for the updated utilities clear the market for good 1. -/
def QLClears (π : Fin S → ℝ) (βc : ι → Fin S → ℝ) (e : ι → Fin S → ℝ) (s : Fin S)
    (E : ι → Finset (Fin S)) (p : ℝ) : Prop :=
  ∃ y : ι → ℝ × ℝ, (∀ i, 0 < (y i).1 ∧ p * (y i).1 + (y i).2 ≤ p * e i s ∧
    ∀ y' : ℝ × ℝ, 0 < y'.1 → p * y'.1 + y'.2 ≤ p * e i s →
      updU π (βc i) (E i) y' ≤ updU π (βc i) (E i) (y i)) ∧ ∑ i, (y i).1 = ∑ i, e i s

/-- Clearing with updated utilities is the spot equilibrium with the posterior coefficients. -/
theorem qlClears_iff {π : Fin S → ℝ} (hπ : ∀ s, 0 < π s) (βc : ι → Fin S → ℝ)
    (e : ι → Fin S → ℝ) (s : Fin S) {E : ι → Finset (Fin S)} (hE : ∀ i, (E i).Nonempty)
    (p : ℝ) :
    QLClears π βc e s E p ↔ QLSpotEqm (fun i => postCoef π (βc i) (E i)) (fun i => e i s) p := by
  unfold QLClears QLSpotEqm QLOptimal
  simp only [updU_eq hπ _ (hE _)]

theorem postCoef_singleton {π : Fin S → ℝ} (hπ : ∀ s, 0 < π s) (β : Fin S → ℝ) (s : Fin S) :
    postCoef π β {s} = β s := by
  simp [postCoef, (hπ s).ne']

theorem postCoef_const {π : Fin S → ℝ} (hπ : ∀ s, 0 < π s) {β : Fin S → ℝ} {E : Finset (Fin S)}
    (hE : E.Nonempty) {c : ℝ} (hc : ∀ s ∈ E, β s = c) : postCoef π β E = c := by
  have hM : 0 < ∑ t ∈ E, π t := Finset.sum_pos (fun t _ => hπ t) hE
  unfold postCoef
  rw [show (∑ s ∈ E, π s * β s) = (∑ s ∈ E, π s) * c from by
    rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun s hs => by rw [hc s hs]]
  field_simp

omit [Fintype ι] in
theorem reeEvent_nonempty (P : Fin S → ℝ) (σ : ι → Fin S → β) (i : ι) (s : Fin S) :
    (reeEvent P σ i s).Nonempty := ⟨s, by simp [reeEvent]⟩

theorem pooledEvent_nonempty (σ : ι → Fin S → β) (s : Fin S) : (pooledEvent σ s).Nonempty :=
  ⟨s, by simp [pooledEvent]⟩

/-- Two consumers: the clearing price is `(b₀ + b₁)/(e₀ + e₁)`. -/
theorem qlSpotEqm_two {b e : Fin 2 → ℝ} (hb0 : 0 < b 0) (hb1 : 0 < b 1) (he : 0 < e 0 + e 1)
    (p : ℝ) : QLSpotEqm b e p ↔ p = (b 0 + b 1) / (e 0 + e 1) := by
  rw [qlSpotEqm_iff (fun i => by fin_cases i <;> assumption) (by simpa [Fin.sum_univ_two]),
    Fin.sum_univ_two, Fin.sum_univ_two]

/-! ## Examples 19.H.2 and 19.H.3 -/

/-- The two equally likely states of Examples 19.H.2-19.H.3: `β = 1` (state `0`), `β = 2`
(state `1`). -/
def beta19H (s : Fin 2) : ℝ := s.val + 1

theorem beta19H_pos (s : Fin 2) : 0 < beta19H s := by unfold beta19H; positivity

/-- Equal prior probabilities. -/
noncomputable def half2 : Fin 2 → ℝ := fun _ => 1 / 2

theorem half2_pos : ∀ s, 0 < half2 s := fun _ => by norm_num [half2]

theorem postCoef_univ_beta : postCoef half2 beta19H Finset.univ = 3 / 2 := by
  simp [postCoef, half2, beta19H, Fin.sum_univ_two]; norm_num

/-- The coefficients of Example 19.H.2: both consumers have `β ln x₁ + x₂`. -/
def betaBoth : Fin 2 → Fin 2 → ℝ := fun _ => beta19H

/-- One unit of good 1 for each consumer in each state. -/
def ones2 : Fin 2 → Fin 2 → ℝ := fun _ _ => 1

/-- The signals of Example 19.H.2: consumer `0` observes the state, consumer `1` observes
nothing. -/
def sig19H2 (i : Fin 2) (s : Fin 2) : ℕ := if i = 0 then s.val else 0

/-- Two consumers: clearing with updated utilities at the price
`(c₀ + c₁)/(e₀ + e₁)`, `cᵢ` the posterior coefficients. -/
theorem qlClears_two {π : Fin S → ℝ} (hπ : ∀ s, 0 < π s) {βc e : Fin 2 → Fin S → ℝ} {s : Fin S}
    {E : Fin 2 → Finset (Fin S)} (hE : ∀ i, (E i).Nonempty)
    (hb : ∀ i, 0 < postCoef π (βc i) (E i)) (he : 0 < e 0 s + e 1 s) (p : ℝ) :
    QLClears π βc e s E p ↔
      p = (postCoef π (βc 0) (E 0) + postCoef π (βc 1) (E 1)) / (e 0 s + e 1 s) := by
  rw [qlClears_iff hπ βc e s hE, qlSpotEqm_two (hb 0) (hb 1) he]

/-- The events of Example 19.H.2 without learning from prices: consumer 1 knows the state,
consumer 2 knows nothing. -/
def naiveEvents19H2 (s : Fin 2) : Fin 2 → Finset (Fin 2) := ![{s}, Finset.univ]

/-- **Example 19.H.2** (MWG, p. 720). Both consumers have `u = β ln x₁ + x₂` and one unit of good 1;
consumer 1 knows `β`, consumer 2 does not. If consumer 2 does not learn from the price, the
clearing price is `p(β) = (3 + 2β)/4`, which reveals `β` (`p(1) ≠ p(2)`); but this price function
is not a rational expectations equilibrium: once consumer 2 infers `β` from it, it no longer
clears the market. -/
theorem example_19_H_2 :
    (∀ s, QLClears half2 betaBoth ones2 s (naiveEvents19H2 s) ((3 + 2 * beta19H s) / 4)) ∧
      (3 + 2 * beta19H 0) / 4 ≠ (3 + 2 * beta19H 1) / 4 ∧
      ¬ IsREE (QLClears half2 betaBoth ones2) (fun s => (3 + 2 * beta19H s) / 4) sig19H2 := by
  have hones : ∀ s, ones2 0 s + ones2 1 s = 2 := fun s => by norm_num [ones2]
  refine ⟨fun s => ?_, by norm_num [beta19H], fun h => ?_⟩
  · have c0 : postCoef half2 (betaBoth 0) (naiveEvents19H2 s 0) = beta19H s :=
      postCoef_singleton half2_pos _ s
    have c1 : postCoef half2 (betaBoth 1) (naiveEvents19H2 s 1) = 3 / 2 := postCoef_univ_beta
    rw [qlClears_two half2_pos (fun i => by fin_cases i <;> simp [naiveEvents19H2])
      (fun i => by fin_cases i
                   · exact c0 ▸ beta19H_pos s
                   · exact c1 ▸ by norm_num) (by rw [hones]; norm_num), c0, c1, hones]
    ring
  · have h0 := h 0
    have hev : (fun i => reeEvent (fun s => (3 + 2 * beta19H s) / 4) sig19H2 i 0) =
        fun _ => {0} := by
      funext i
      ext s'
      fin_cases i <;> fin_cases s' <;> simp [reeEvent, sig19H2, beta19H]
    unfold IsREE at h
    rw [hev] at h0
    have c : ∀ i, postCoef half2 (betaBoth i) {0} = 1 := fun i => by
      rw [postCoef_singleton half2_pos]; simp [betaBoth, beta19H]
    rw [qlClears_two half2_pos (fun _ => by simp) (fun i => by rw [c]; norm_num)
      (by rw [hones]; norm_num), c, c, hones] at h0
    norm_num [beta19H] at h0

/-- **Example 19.H.2 continued** (MWG, p. 721). If both consumers are informed, the pooled
information price function is `p̂(β) = β`; it is fully revealing and therefore a rational
expectations equilibrium. -/
theorem example_19_H_2_continued :
    IsPooledPrice (QLClears half2 betaBoth ones2) beta19H sig19H2 ∧
      IsREE (QLClears half2 betaBoth ones2) beta19H sig19H2 := by
  have hones : ∀ s, ones2 0 s + ones2 1 s = 2 := fun s => by norm_num [ones2]
  have hpool : ∀ s, pooledEvent sig19H2 s = {s} := by
    intro s; ext s'
    fin_cases s <;> fin_cases s' <;> simp [pooledEvent, sig19H2, Fin.forall_fin_two]
  have hP : IsPooledPrice (QLClears half2 betaBoth ones2) beta19H sig19H2 := by
    intro s
    have c : ∀ i, postCoef half2 (betaBoth i) {s} = beta19H s := fun i =>
      postCoef_singleton half2_pos _ s
    simp only [hpool]
    rw [qlClears_two half2_pos (fun _ => by simp) (fun i => by rw [c]; exact beta19H_pos s)
      (by rw [hones]; norm_num), c, c, hones]
    ring
  refine ⟨hP, pooled_fullyRevealing_isREE hP ?_ ?_⟩
  · rintro s s' ⟨i, hi⟩ hst
    fin_cases s <;> fin_cases s' <;> simp_all [beta19H]
  · intro s s' h
    have : s.val = s'.val := by simpa [sig19H2] using h 0
    rw [Fin.ext_iff.mpr this]

/-- The coefficients of Example 19.H.3: `β` for consumer 1 and `3 - β` for consumer 2. -/
def beta19H3 : Fin 2 → Fin 2 → ℝ := ![beta19H, fun s => 3 - beta19H s]

theorem beta19H3_pos (i s : Fin 2) : 0 < beta19H3 i s := by
  fin_cases i <;> fin_cases s <;> norm_num [beta19H3, beta19H]

/-- **Example 19.H.3** (MWG, p. 722; Kreps 1977). Utilities `β ln x₁₁ + x₂₁` and
`(3 - β) ln x₁₂ + x₂₂`, total endowment of good 1 equal to `3` in both states, consumer 1 informed,
consumer 2 not. The pooled information price is `1` in both states (so it is not revealing), and
no price function is a rational expectations equilibrium. -/
theorem example_19_H_3 {e : Fin 2 → Fin 2 → ℝ} (he : ∀ s, e 0 s + e 1 s = 3) :
    (∀ s, QLClears half2 beta19H3 e s (fun _ => {s}) 1) ∧
      ∀ P : Fin 2 → ℝ, ¬ IsREE (QLClears half2 beta19H3 e) P sig19H2 := by
  have hsing : ∀ i s, postCoef half2 (beta19H3 i) {s} = beta19H3 i s := fun i s =>
    postCoef_singleton half2_pos _ s
  have hsum : ∀ s, beta19H3 0 s + beta19H3 1 s = 3 := fun s => by simp [beta19H3]
  have he' : ∀ s, 0 < e 0 s + e 1 s := fun s => by rw [he s]; norm_num
  refine ⟨fun s => ?_, fun P hP => ?_⟩
  · rw [qlClears_two half2_pos (fun _ => by simp) (fun i => by rw [hsing]; exact beta19H3_pos i s)
      (he' s), hsing, hsing, hsum, he]
    norm_num
  · by_cases hrev : P 0 = P 1
    · -- not revealing: consumer 2 stays uninformed
      have hev : ∀ s, (fun i => reeEvent P sig19H2 i s) = naiveEvents19H2 s := by
        intro s; funext i; ext s'
        fin_cases i <;> fin_cases s <;> fin_cases s' <;>
          simp [reeEvent, sig19H2, hrev, naiveEvents19H2]
      have hpr : ∀ s, P s = (beta19H s + 3 / 2) / 3 := by
        intro s
        have hu : postCoef half2 (beta19H3 1) (naiveEvents19H2 s 1) = 3 / 2 := by
          simp [postCoef, half2, beta19H3, beta19H, Fin.sum_univ_two, naiveEvents19H2]
          norm_num
        have h0 : postCoef half2 (beta19H3 0) (naiveEvents19H2 s 0) = beta19H s := by
          rw [show naiveEvents19H2 s 0 = {s} from rfl, hsing]; rfl
        have := hP s
        rw [hev s, qlClears_two half2_pos (fun i => by fin_cases i <;> simp [naiveEvents19H2])
          (fun i => by
            fin_cases i
            · exact h0 ▸ beta19H_pos s
            · exact hu ▸ by norm_num) (he' s), h0, hu, he] at this
        exact this
      rw [hpr 0, hpr 1] at hrev
      norm_num [beta19H] at hrev
    · -- revealing: both informed, so the price is `1` in both states
      have hrev' : P 1 ≠ P 0 := Ne.symm hrev
      have hev : ∀ s, (fun i => reeEvent P sig19H2 i s) = fun _ => {s} := by
        intro s; funext i; ext s'
        fin_cases i <;> fin_cases s <;> fin_cases s' <;> simp [reeEvent, sig19H2, hrev, hrev']
      have hpr : ∀ s, P s = 1 := by
        intro s
        have := hP s
        rw [hev s, qlClears_two half2_pos (fun _ => by simp)
          (fun i => by rw [hsing]; exact beta19H3_pos i s) (he' s), hsing, hsing, hsum, he]
          at this
        linarith
      exact hrev ((hpr 0).trans (hpr 1).symm)

end MWG.EquilibriumUncertainty
