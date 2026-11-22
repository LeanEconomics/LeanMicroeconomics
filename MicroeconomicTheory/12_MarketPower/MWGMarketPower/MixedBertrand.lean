/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGMarketPower.Bertrand
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Mixed strategies in the Bertrand duopoly

MWG, Exercise 12.C.2, p. 430 (footnote 9, p. 388).

A mixed strategy is a probability measure `σ` on prices (Mathlib's `Measure ℝ`) that puts no
mass on negative prices (`IsMixedPrice`). A firm naming `p` against a rival naming `q` earns
`(p − c)x(p)` if `p < q`, half of it if `p = q` and `0` if `p > q` (`mbProfit`; this is firm 0's
and, with the arguments swapped, firm 1's payoff in Chapter 12's `bertrandProfit`,
`mbProfit_fst`, `mbProfit_snd`). Expected profit is the iterated integral
`∫∫ mbProfit(p, q) dτ(q) dσ(p)` (`mbPayoff`); on the price set `[0, ∞)` the profit is bounded and
measurable, so this is the expectation over the product of the two mixed strategies.
`IsMixedBertrandNE` asks that no firm gain from any mixed deviation.

* `mbProfit_integral`: against a mixed strategy `τ`, the pure price `p` earns
  `(p − c)x(p)·(τ(p, ∞) + τ[p, ∞))/2`.
* `exercise_12_C_2`: under the assumptions of Proposition 12.C.1 (`x` continuous, nonnegative,
  strictly decreasing where positive, `x(p) = 0` for `p ≥ p̄`, `x(c) > 0`, `c > 0`), both firms
  naming `c` with certainty is a Nash equilibrium in mixed strategies, and it is the only one.

The proof of uniqueness: in an equilibrium each firm's expected profit `Vᵢ` is attained at almost
every price it names (`mb_ae_eq`). If `V₁ > 0`, firm 1 never names a price below
`c + V₁/x(c)`, so firm 2 earns a positive profit by naming a price just above `c`
(`mb_rival_pos`). If both profits are positive, both strategies have an atom at a common highest
price `B` (`mb_top_atom`), and undercutting `B` slightly almost doubles firm 1's profit. So
`V₁ = V₂ = 0`; then no firm names a price above `c` (it would leave the rival a profitable
price) and no firm names a price below `c` with positive probability (`mb_below_null`).

Departure: MWG does not specify the price space; mixed strategies here are supported on
`[0, ∞)`, which makes expected profits bounded (see `docs/corrections.md`).
-/

namespace MWG.MarketPower

open MeasureTheory Set Function

/-- The profit of a duopolist naming `p` against a rival naming `q` (MWG, p. 388):
`(p − c)x(p)` if `p < q`, `(p − c)x(p)/2` if `p = q`, `0` if `p > q`. -/
noncomputable def mbProfit (x : ℝ → ℝ) (c p q : ℝ) : ℝ :=
  (p - c) * (if p < q then x p else if p = q then x p / 2 else 0)

theorem mbProfit_fst (x : ℝ → ℝ) (c p q : ℝ) :
    bertrandProfit x c ![p, q] 0 = mbProfit x c p q := by
  unfold bertrandProfit mbProfit
  rw [bertrandSales_duopoly]
  rfl

theorem mbProfit_snd (x : ℝ → ℝ) (c p q : ℝ) :
    bertrandProfit x c ![p, q] 1 = mbProfit x c q p := by
  unfold bertrandProfit mbProfit
  rcases lt_trichotomy q p with h | h | h
  · unfold bertrandSales
    have hall : ∀ k, ![p, q] 1 ≤ ![p, q] k := by intro k; fin_cases k <;> simp [h.le]
    have hcard : (Finset.univ.filter fun k => ![p, q] k = ![p, q] 1) = {1} := by
      ext k; fin_cases k <;> simp [h.ne']
    simp only [hall, implies_true, ↓reduceIte]
    rw [hcard]
    simp [h]
  · unfold bertrandSales
    have hall : ∀ k, ![p, q] 1 ≤ ![p, q] k := by intro k; fin_cases k <;> simp [h.le]
    have hcard : (Finset.univ.filter fun k => ![p, q] k = ![p, q] 1) = Finset.univ := by
      ext k; fin_cases k <;> simp [h]
    simp only [hall, implies_true, ↓reduceIte]
    rw [hcard]
    simp [h]
  · rw [bertrandSales_of_gt (k := 0) (by simpa using h)]
    simp [h.not_gt, h.ne']

/-- The probability weight with which a price `p` wins against `τ`, counting ties half:
`(τ(p, ∞) + τ[p, ∞))/2 = τ(p, ∞) + τ{p}/2`. -/
noncomputable def mbWin (τ : Measure ℝ) (p : ℝ) : ℝ := (τ.real (Ioi p) + τ.real (Ici p)) / 2

theorem mbProfit_indicator (x : ℝ → ℝ) (c p q : ℝ) :
    mbProfit x c p q = (p - c) * x p * (((Ioi p).indicator 1 q + (Ici p).indicator 1 q) / 2) := by
  unfold mbProfit
  rcases lt_trichotomy p q with h | h | h
  · simp [h, h.le]
  · subst h; simp; ring
  · have h1 : q ∉ Ioi p := fun hq => absurd (mem_Ioi.1 hq) (not_lt.2 h.le)
    have h2 : q ∉ Ici p := fun hq => absurd (mem_Ici.1 hq) (not_le.2 h)
    simp [h.not_gt, h.ne', h1, h2]

/-- **Expected profit of a pure price against a mixed strategy** (MWG, Exercise 12.C.2):
`∫ mbProfit(p, q) dτ(q) = (p − c)x(p)·mbWin τ p` for any finite measure `τ`. -/
theorem mbProfit_integral (x : ℝ → ℝ) (c p : ℝ) (τ : Measure ℝ) [IsFiniteMeasure τ] :
    ∫ q, mbProfit x c p q ∂τ = (p - c) * x p * mbWin τ p := by
  simp_rw [mbProfit_indicator]
  rw [integral_const_mul, integral_div, integral_add, integral_indicator_one measurableSet_Ioi,
    integral_indicator_one measurableSet_Ici]
  · rfl
  · exact (integrable_const (1 : ℝ)).indicator measurableSet_Ioi
  · exact (integrable_const (1 : ℝ)).indicator measurableSet_Ici

/-- A mixed price strategy: a probability measure on prices with no mass on negative prices. -/
def IsMixedPrice (σ : Measure ℝ) : Prop := IsProbabilityMeasure σ ∧ σ (Iio 0) = 0

/-- The expected profit of a firm playing `σ` against a rival playing `τ`. -/
noncomputable def mbPayoff (x : ℝ → ℝ) (c : ℝ) (σ τ : Measure ℝ) : ℝ :=
  ∫ p, ∫ q, mbProfit x c p q ∂τ ∂σ

/-- A Nash equilibrium in mixed strategies of the Bertrand duopoly: no firm gains from any mixed
deviation (MWG, p. 388, footnote 9, and Exercise 12.C.2). -/
def IsMixedBertrandNE (x : ℝ → ℝ) (c : ℝ) (σ₁ σ₂ : Measure ℝ) : Prop :=
  IsMixedPrice σ₁ ∧ IsMixedPrice σ₂ ∧
    (∀ σ, IsMixedPrice σ → mbPayoff x c σ σ₂ ≤ mbPayoff x c σ₁ σ₂) ∧
    (∀ σ, IsMixedPrice σ → mbPayoff x c σ σ₁ ≤ mbPayoff x c σ₂ σ₁)

theorem mbPayoff_eq (x : ℝ → ℝ) (c : ℝ) (σ τ : Measure ℝ) [IsFiniteMeasure τ] :
    mbPayoff x c σ τ = ∫ p, (p - c) * x p * mbWin τ p ∂σ := by
  unfold mbPayoff
  congr 1
  funext p
  exact mbProfit_integral x c p τ

theorem mbPayoff_dirac (x : ℝ → ℝ) (c p : ℝ) (τ : Measure ℝ) [IsFiniteMeasure τ] :
    mbPayoff x c (Measure.dirac p) τ = (p - c) * x p * mbWin τ p := by
  rw [mbPayoff_eq, integral_dirac]

theorem isMixedPrice_dirac {p : ℝ} (hp : 0 ≤ p) : IsMixedPrice (Measure.dirac p) := by
  refine ⟨inferInstance, ?_⟩
  rw [Measure.dirac_apply' p measurableSet_Iio]
  exact indicator_of_notMem (fun h => absurd (mem_Iio.1 h) (not_lt.2 hp)) _

theorem mbWin_nonneg (τ : Measure ℝ) (p : ℝ) : 0 ≤ mbWin τ p := by
  unfold mbWin; positivity

theorem mbWin_le_Ici (τ : Measure ℝ) [IsFiniteMeasure τ] (p : ℝ) :
    mbWin τ p ≤ τ.real (Ici p) := by
  unfold mbWin
  have := measureReal_mono (μ := τ) (Ioi_subset_Ici_self (a := p))
  linarith

theorem mbWin_le_one (τ : Measure ℝ) [IsProbabilityMeasure τ] (p : ℝ) : mbWin τ p ≤ 1 := by
  have h1 := mbWin_le_Ici τ p
  have h2 : τ.real (Ici p) ≤ 1 := measureReal_le_one
  linarith

theorem mbWin_antitone (τ : Measure ℝ) [IsFiniteMeasure τ] : Antitone (mbWin τ) := by
  intro p p' h
  unfold mbWin
  have h1 := measureReal_mono (μ := τ) (Ioi_subset_Ioi h)
  have h2 := measureReal_mono (μ := τ) (Ici_subset_Ici.2 h)
  linarith

theorem mb_x_anti {x : ℝ → ℝ} {pbar : ℝ} (hx : IsBertrandDemand x pbar) {p p' : ℝ}
    (h : p ≤ p') : x p' ≤ x p := by
  rcases eq_or_lt_of_le h with rfl | h
  · exact le_rfl
  rcases eq_or_lt_of_le (hx.nonneg p') with h0 | h0
  · rw [← h0]; exact hx.nonneg p
  · exact (hx.strictAnti p p' h h0).le

/-- The profit `(p − c)x(p)` is bounded on `[0, ∞)`. -/
theorem mb_bound {x : ℝ → ℝ} {pbar : ℝ} (hx : IsBertrandDemand x pbar) (c : ℝ) :
    ∃ G, 0 ≤ G ∧ ∀ p, 0 ≤ p → |(p - c) * x p| ≤ G := by
  have hg : Continuous fun p => (p - c) * x p :=
    (continuous_id.sub continuous_const).mul hx.cont
  obtain ⟨G, hG⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := max pbar 0)).exists_bound_of_continuousOn
    hg.continuousOn
  refine ⟨max G 0, le_max_right _ _, fun p hp => ?_⟩
  by_cases h : p ≤ max pbar 0
  · have := hG p ⟨hp, h⟩
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  · push Not at h
    rw [hx.zero p (le_trans (le_max_left _ _) h.le), mul_zero, abs_zero]
    exact le_max_right _ _

/-- A property holding almost everywhere holds at some point of a set of positive measure. -/
theorem mb_exists_mem {σ : Measure ℝ} {s : Set ℝ} {Q : ℝ → Prop} (hs : σ s ≠ 0)
    (hQ : ∀ᵐ p ∂σ, Q p) : ∃ p ∈ s, Q p := by
  by_contra h
  push Not at h
  exact hs (measure_mono_null (fun p hp => h p hp) (ae_iff.1 hQ))

theorem mb_ae_nonneg {σ : Measure ℝ} (h0 : σ (Iio 0) = 0) : ∀ᵐ p ∂σ, 0 ≤ p := by
  rw [ae_iff]
  simp only [not_le]
  exact h0

/-- In a best response `σ` to `τ`, almost every price named earns the expected profit: if no
pure price `p ≥ 0` earns more than `V = U(σ, τ)`, then `(p − c)x(p)·mbWin τ p = V` for
`σ`-almost every `p`. -/
theorem mb_ae_eq {x : ℝ → ℝ} {pbar c : ℝ} (hx : IsBertrandDemand x pbar) {σ τ : Measure ℝ}
    [IsProbabilityMeasure σ] [IsProbabilityMeasure τ] (h0 : σ (Iio 0) = 0)
    (hbr : ∀ p, 0 ≤ p → (p - c) * x p * mbWin τ p ≤ mbPayoff x c σ τ) :
    ∀ᵐ p ∂σ, (p - c) * x p * mbWin τ p = mbPayoff x c σ τ := by
  have hpos := mb_ae_nonneg h0
  obtain ⟨G, -, hG⟩ := mb_bound hx c
  have hmeas : Measurable fun p => (p - c) * x p * mbWin τ p :=
    (((continuous_id.sub continuous_const).mul hx.cont).measurable).mul
      (mbWin_antitone τ).measurable
  have hint : Integrable (fun p => (p - c) * x p * mbWin τ p) σ := by
    refine Integrable.of_bound hmeas.aestronglyMeasurable G (hpos.mono fun p hp => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mbWin_nonneg τ p)]
    have h1 := hG p hp
    have h2 := mbWin_le_one τ p
    have h3 := mbWin_nonneg τ p
    nlinarith [abs_nonneg ((p - c) * x p)]
  have hle : (fun p => (p - c) * x p * mbWin τ p) ≤ᵐ[σ] fun _ => mbPayoff x c σ τ :=
    hpos.mono fun p hp => hbr p hp
  have heq : ∫ p, (p - c) * x p * mbWin τ p ∂σ = ∫ _, mbPayoff x c σ τ ∂σ := by
    rw [integral_const, ← mbPayoff_eq]
    simp
  exact (integral_eq_iff_of_ae_le hint (integrable_const _) hle).1 heq

/-- If a firm's best response earns `V > 0`, it names no price below `c + V/x(c)`. -/
theorem mb_gap {x : ℝ → ℝ} {pbar c : ℝ} (hx : IsBertrandDemand x pbar) (hxc : 0 < x c)
    {σ τ : Measure ℝ} [IsProbabilityMeasure τ] {V : ℝ} (hV : 0 < V)
    (hae : ∀ᵐ p ∂σ, 0 ≤ p ∧ (p - c) * x p * mbWin τ p = V) : σ (Iio (c + V / x c)) = 0 := by
  refine measure_mono_null ?_ (ae_iff.1 hae)
  intro p hp hgood
  obtain ⟨-, heq⟩ := hgood
  have hw0 := mbWin_nonneg τ p
  have hw1 := mbWin_le_one τ p
  rcases le_or_gt p c with h | h
  · have : (p - c) * x p ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) (hx.nonneg p)
    nlinarith
  · have hg0 : 0 ≤ (p - c) * x p := mul_nonneg (by linarith) (hx.nonneg p)
    have h1 : (p - c) * x p * mbWin τ p ≤ (p - c) * x p := mul_le_of_le_one_right hg0 hw1
    have h2 : (p - c) * x p ≤ (p - c) * x c :=
      mul_le_mul_of_nonneg_left (mb_x_anti hx h.le) (by linarith)
    have h3 : (p - c) * x c < V := by
      have : p - c < V / x c := by linarith [mem_Iio.1 hp]
      exact (lt_div_iff₀ hxc).1 this
    linarith

/-- Against a strategy with no mass below `e`, prices below `e` win for sure. -/
theorem mb_win_one {σ : Measure ℝ} [IsProbabilityMeasure σ] {e p : ℝ} (he : σ (Iio e) = 0)
    (hp : p < e) : mbWin σ p = 1 := by
  have h0 : σ (Iic p) = 0 := measure_mono_null (Iic_subset_Iio.2 hp) he
  have h1 : σ (Ioi p) = 1 := by
    rw [← compl_Iic, prob_compl_eq_one_sub measurableSet_Iic, h0, tsub_zero]
  have h2 : σ (Ici p) = 1 := le_antisymm prob_le_one (h1 ▸ measure_mono Ioi_subset_Ici_self)
  unfold mbWin
  simp [Measure.real, h1, h2]

/-- If the rival names no price below `e > c`, a price just above `c` earns a positive
profit. -/
theorem mb_rival_pos {x : ℝ → ℝ} {pbar c : ℝ} (hx : IsBertrandDemand x pbar) (hc : 0 < c)
    (hxc : 0 < x c) {σ : Measure ℝ} [IsProbabilityMeasure σ] {e : ℝ} (hce : c < e)
    (he : σ (Iio e) = 0) : ∃ p, 0 ≤ p ∧ 0 < (p - c) * x p * mbWin σ p := by
  obtain ⟨p, hpc, hpe, hgain⟩ := bertrand_deviation hx hxc hce
  refine ⟨p, by linarith, ?_⟩
  rw [mb_win_one he hpe, mul_one]
  have : 0 ≤ (e - c) * x e / 2 := div_nonneg (mul_nonneg (by linarith) (hx.nonneg e)) (by norm_num)
  linarith

/-- Almost every point `p` has `μ[p, ∞) > 0`. -/
theorem mb_ae_Ici_ne_zero (μ : Measure ℝ) : ∀ᵐ p ∂μ, μ (Ici p) ≠ 0 := by
  rw [ae_iff]
  simp only [ne_eq, not_not]
  by_cases hmin : ∃ m, μ (Ici m) = 0 ∧ ∀ p, μ (Ici p) = 0 → m ≤ p
  · obtain ⟨m, hm, hle⟩ := hmin
    exact measure_mono_null (fun p hp => mem_Ici.2 (hle p hp)) hm
  · push Not at hmin
    have hsub : {p | μ (Ici p) = 0} ⊆
        ⋃ q : {q : ℚ // μ (Ici ((q : ℚ) : ℝ)) = 0}, Ici ((q.1 : ℚ) : ℝ) := by
      intro p hp
      obtain ⟨p', hp', hlt⟩ := hmin p hp
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
      exact mem_iUnion.2 ⟨⟨q, measure_mono_null (Ici_subset_Ici.2 hq1.le) hp'⟩, hq2.le⟩
    exact measure_mono_null hsub (measure_iUnion_null fun q => q.2)

/-- If both firms earn positive profits, both mixed strategies have an atom at a common top
price; this is the one-sided step: `σ` has no mass above `B`, an atom at `B`, and `τ[B, ∞) > 0`.
-/
theorem mb_top_atom {σ τ : Measure ℝ} [IsProbabilityMeasure σ] [IsProbabilityMeasure τ]
    {ε pbar : ℝ} (hε : 0 < ε) (hσ : ∀ᵐ p ∂σ, ε ≤ τ.real (Ici p))
    (hτ : ∀ᵐ p ∂τ, σ (Ici p) ≠ 0) (hbar : τ (Ici pbar) = 0) :
    ∃ B, σ (Ioi B) = 0 ∧ σ {B} ≠ 0 ∧ τ (Ici B) ≠ 0 := by
  set T := {p | ε ≤ τ.real (Ici p)} with hT
  have hTne : T.Nonempty := by
    obtain ⟨p, -, hp⟩ := mb_exists_mem (s := univ) (by simp) hσ
    exact ⟨p, hp⟩
  have hTbdd : BddAbove T := by
    refine ⟨pbar, fun p hp => ?_⟩
    by_contra h
    push Not at h
    have : τ.real (Ici p) = 0 :=
      (measureReal_eq_zero_iff).2 (measure_mono_null (Ici_subset_Ici.2 h.le) hbar)
    have hp' : ε ≤ τ.real (Ici p) := hp
    linarith
  set B := sSup T with hB
  have hIoi : σ (Ioi B) = 0 := by
    refine measure_mono_null ?_ (ae_iff.1 hσ)
    intro p hp hpT
    exact absurd (le_csSup hTbdd hpT) (not_le.2 hp)
  have hIci : τ (Ici B) ≠ 0 := by
    have hseq : ⋂ n : ℕ, Ici (B - 1 / ((n : ℝ) + 1)) = Ici B := by
      ext p
      simp only [mem_iInter, mem_Ici]
      constructor
      · intro h
        by_contra hlt
        push Not at hlt
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hlt)
        have := h n
        linarith
      · intro h n
        have : 0 < 1 / ((n : ℝ) + 1) := by positivity
        linarith
    have hanti : Antitone fun n : ℕ => Ici (B - 1 / ((n : ℝ) + 1)) := by
      intro m n hmn
      apply Ici_subset_Ici.2
      have hmn' : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hmn 1
      have : 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) hmn'
      linarith
    have hlow : ∀ n : ℕ, ENNReal.ofReal ε ≤ τ (Ici (B - 1 / ((n : ℝ) + 1))) := by
      intro n
      have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
      obtain ⟨t, ht, hlt⟩ := exists_lt_of_lt_csSup hTne (show B - 1 / ((n : ℝ) + 1) < B by
        linarith)
      have ht' : ε ≤ τ.real (Ici t) := ht
      have h1 : ε ≤ τ.real (Ici (B - 1 / ((n : ℝ) + 1))) :=
        le_trans ht' (measureReal_mono (Ici_subset_Ici.2 hlt.le))
      rw [← ofReal_measureReal]
      exact ENNReal.ofReal_le_ofReal h1
    have hinf := hanti.measure_iInter (μ := τ) (fun n => measurableSet_Ici.nullMeasurableSet)
      ⟨0, measure_ne_top _ _⟩
    rw [hseq] at hinf
    have hge : ENNReal.ofReal ε ≤ τ (Ici B) := by rw [hinf]; exact le_iInf hlow
    exact ne_of_gt (lt_of_lt_of_le (ENNReal.ofReal_pos.2 hε) hge)
  obtain ⟨p, hpB, hp⟩ := mb_exists_mem hIci hτ
  have hpB' : p ≤ B := by
    by_contra h
    push Not at h
    exact hp (measure_mono_null (Ici_subset_Ioi.2 h) hIoi)
  have hpeq : p = B := le_antisymm hpB' hpB
  refine ⟨B, hIoi, fun h0 => hp ?_, hIci⟩
  rw [hpeq]
  refine measure_mono_null (fun q hq => ?_) (measure_union_null h0 hIoi)
  rcases eq_or_lt_of_le (mem_Ici.1 hq) with h | h
  · exact Or.inl h.symm
  · exact Or.inr h

/-- Undercutting a common atom: if firm `i` earns `V > 0` at a price `B` at which the rival has
no mass above `B`, a price slightly below `B` earns more than `V`. -/
theorem mb_undercut {x : ℝ → ℝ} {pbar c : ℝ} (hx : IsBertrandDemand x pbar) (hc : 0 < c)
    (hxc : 0 < x c) {τ : Measure ℝ} [IsProbabilityMeasure τ] {B V : ℝ} (hV : 0 < V)
    (hB : (B - c) * x B * mbWin τ B = V) (hτB : τ (Ioi B) = 0)
    (hbr : ∀ p, 0 ≤ p → (p - c) * x p * mbWin τ p ≤ V) : False := by
  set a := τ.real (Ici B) with ha_def
  have hw : mbWin τ B = a / 2 := by
    unfold mbWin
    rw [show τ.real (Ioi B) = 0 from (measureReal_eq_zero_iff).2 hτB]
    ring
  have ha : 0 ≤ a := measureReal_nonneg
  rw [hw] at hB
  have hgB : 0 < (B - c) * x B := by
    by_contra h
    push Not at h
    nlinarith
  have hBc : c < B := by
    by_contra h
    push Not at h
    nlinarith [hx.nonneg B]
  obtain ⟨p', hp'c, hp'B, hgain⟩ := bertrand_deviation hx hxc hBc
  have hw' : a ≤ mbWin τ p' := by
    unfold mbWin
    have h1 : a ≤ τ.real (Ioi p') := measureReal_mono (Ici_subset_Ioi.2 hp'B)
    have h2 : a ≤ τ.real (Ici p') := measureReal_mono (Ici_subset_Ici.2 hp'B.le)
    linarith
  have hdev := hbr p' (by linarith)
  have hg' : 0 < (p' - c) * x p' := by linarith [half_pos hgB]
  have ha' : 0 < a := by
    rcases eq_or_lt_of_le ha with h | h
    · rw [← h] at hB; simp at hB; linarith
    · exact h
  nlinarith [mul_le_mul_of_nonneg_left hw' hg'.le, mul_lt_mul_of_pos_right hgain ha']

/-- If no price `p ≥ 0` earns a positive profit against `τ`, then `τ` puts no mass above `c`. -/
theorem mb_above_null {x : ℝ → ℝ} {pbar c : ℝ} (hx : IsBertrandDemand x pbar) (hc : 0 < c)
    (hxc : 0 < x c) {τ : Measure ℝ} [IsFiniteMeasure τ]
    (hbr : ∀ p, 0 ≤ p → (p - c) * x p * mbWin τ p ≤ 0) : τ (Ioi c) = 0 := by
  have hev : ∀ᶠ p in nhds c, 0 < x p := hx.cont.continuousAt.eventually (lt_mem_nhds hxc)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
  have hnull : ∀ p, c < p → p < c + δ → τ (Ici p) = 0 := by
    intro p h1 h2
    have hxp : 0 < x p := hball (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
    have hg : 0 < (p - c) * x p := mul_pos (by linarith) hxp
    have hle := hbr p (by linarith)
    have hw0 := mbWin_nonneg τ p
    have hw : mbWin τ p = 0 := by
      by_contra hne
      have := mul_pos hg (lt_of_le_of_ne hw0 (Ne.symm hne))
      linarith
    have hr : τ.real (Ici p) = 0 := by
      unfold mbWin at hw
      linarith [measureReal_nonneg (μ := τ) (s := Ioi p), measureReal_nonneg (μ := τ) (s := Ici p)]
    exact (measureReal_eq_zero_iff).1 hr
  have hsub : Ioi c ⊆ ⋃ n : ℕ, Ici (c + δ / ((n : ℝ) + 2)) := by
    intro p hp
    have hpc : 0 < (p - c) / δ := div_pos (sub_pos.2 hp) hδ
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpc
    refine mem_iUnion.2 ⟨n, mem_Ici.2 ?_⟩
    have h1 : δ / ((n : ℝ) + 2) ≤ δ / ((n : ℝ) + 1) :=
      div_le_div_of_nonneg_left hδ.le (by positivity) (by linarith)
    have h2 : δ / ((n : ℝ) + 1) < p - c := by
      rw [lt_div_iff₀ hδ] at hn
      rw [div_lt_iff₀ (by positivity)]
      have := hn
      field_simp at this ⊢
      linarith
    linarith
  refine measure_mono_null hsub (measure_iUnion_null fun n => hnull _ ?_ ?_)
  · have : 0 < δ / ((n : ℝ) + 2) := by positivity
    linarith
  · have : δ / ((n : ℝ) + 2) < δ := by
      rw [div_lt_iff₀ (by positivity)]
      nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    linarith

/-- A price below `c` that earns zero against `τ` leaves `τ` no mass at or above it. -/
theorem mb_low_price {x : ℝ → ℝ} {pbar c : ℝ} (hx : IsBertrandDemand x pbar) (hxc : 0 < x c)
    {τ : Measure ℝ} [IsFiniteMeasure τ] {p : ℝ} (hp : p < c)
    (h0 : (p - c) * x p * mbWin τ p = 0) : τ (Ici p) = 0 := by
  have hxp : 0 < x p := lt_of_lt_of_le hxc (mb_x_anti hx hp.le)
  have hg : (p - c) * x p ≠ 0 := (mul_neg_of_neg_of_pos (by linarith) hxp).ne
  have hw : mbWin τ p = 0 := (mul_eq_zero.1 h0).resolve_left hg
  have hr : τ.real (Ici p) = 0 := by
    unfold mbWin at hw
    linarith [measureReal_nonneg (μ := τ) (s := Ioi p), measureReal_nonneg (μ := τ) (s := Ici p)]
  exact (measureReal_eq_zero_iff).1 hr

/-- When both firms earn zero, neither names a price below `c` with positive probability. -/
theorem mb_below_null {x : ℝ → ℝ} {pbar c : ℝ} (hx : IsBertrandDemand x pbar) (hxc : 0 < x c)
    {σ τ : Measure ℝ} [IsProbabilityMeasure σ] [IsProbabilityMeasure τ]
    (hσ : ∀ᵐ p ∂σ, (p - c) * x p * mbWin τ p = 0) (hτ : ∀ᵐ p ∂τ, (p - c) * x p * mbWin σ p = 0) :
    σ (Iio c) = 0 := by
  by_contra h1
  obtain ⟨p₁, hp₁, hF, hne⟩ := mb_exists_mem h1 (hσ.and (mb_ae_Ici_ne_zero σ))
  have hp₁c : p₁ < c := hp₁
  have hτ1 : τ (Ici p₁) = 0 := mb_low_price hx hxc hp₁c hF
  have hτlow : τ (Iio p₁) ≠ 0 := by
    intro h
    have : τ univ ≤ τ (Iio p₁) + τ (Ici p₁) :=
      calc τ univ = τ (Iio p₁ ∪ Ici p₁) := by rw [Iio_union_Ici]
        _ ≤ _ := measure_union_le _ _
    simp [h, hτ1] at this
  obtain ⟨p₂, hp₂, hF'⟩ := mb_exists_mem hτlow hτ
  have hp₂' : p₂ < p₁ := hp₂
  have hσ2 : σ (Ici p₂) = 0 := mb_low_price hx hxc (by linarith) hF'
  exact hne (measure_mono_null (Ici_subset_Ici.2 hp₂'.le) hσ2)

/-- A probability measure with no mass off `{c}` is the point mass at `c`. -/
theorem mb_eq_dirac {σ : Measure ℝ} [IsProbabilityMeasure σ] {c : ℝ} (h1 : σ (Iio c) = 0)
    (h2 : σ (Ioi c) = 0) : σ = Measure.dirac c := by
  have hcompl : σ ({c}ᶜ) = 0 := by
    refine measure_mono_null (fun p hp => ?_) (measure_union_null h1 h2)
    rcases lt_or_gt_of_ne (show p ≠ c from hp) with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hone : σ {c} = 1 := (prob_compl_eq_zero_iff (measurableSet_singleton c)).1 hcompl
  have hae : ∀ᵐ p ∂σ, p ∈ ({c} : Finset ℝ) := by
    rw [ae_iff]
    refine measure_mono_null (fun p hp => ?_) hcompl
    simpa using hp
  rw [Measure.ae_mem_finset_iff] at hae
  rw [hae]
  simp [hone]

/-- **Exercise 12.C.2** (MWG, p. 430). Under the assumptions of Proposition 12.C.1 (demand `x`
continuous, nonnegative, strictly decreasing where positive, `x(p) = 0` for `p ≥ p̄`, `x(c) > 0`,
`c > 0`), both firms setting their price equal to `c` with certainty is a Nash equilibrium of the
Bertrand duopoly in mixed strategies, and it is the unique one: every mixed-strategy Nash
equilibrium is `(δ_c, δ_c)`. -/
theorem exercise_12_C_2 {x : ℝ → ℝ} {pbar c : ℝ} (hx : IsBertrandDemand x pbar) (hc : 0 < c)
    (hxc : 0 < x c) :
    IsMixedBertrandNE x c (Measure.dirac c) (Measure.dirac c) ∧
    ∀ σ₁ σ₂, IsMixedBertrandNE x c σ₁ σ₂ → σ₁ = Measure.dirac c ∧ σ₂ = Measure.dirac c := by
  constructor
  · -- against `δ_c` no strategy earns a positive profit
    have hle : ∀ σ : Measure ℝ, mbPayoff x c σ (Measure.dirac c) ≤ 0 := by
      intro σ
      rw [mbPayoff_eq]
      refine integral_nonpos fun p => ?_
      rcases le_or_gt p c with h | h
      · exact mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonpos_of_nonneg (by linarith) (hx.nonneg p)) (mbWin_nonneg _ p)
      · have hw : mbWin (Measure.dirac c) p = 0 := by
          unfold mbWin
          rw [Measure.dirac_real_apply, Measure.dirac_real_apply,
            indicator_of_notMem (fun hm => absurd (mem_Ioi.1 hm) (not_lt.2 h.le)),
            indicator_of_notMem (fun hm => absurd (mem_Ici.1 hm) (not_le.2 h))]
          norm_num
        simp [hw]
    have h0 : mbPayoff x c (Measure.dirac c) (Measure.dirac c) = 0 := by
      rw [mbPayoff_dirac]; ring
    have hP : IsMixedPrice (Measure.dirac c) := isMixedPrice_dirac hc.le
    exact ⟨hP, hP, fun σ _ => h0 ▸ hle σ, fun σ _ => h0 ▸ hle σ⟩
  · rintro σ₁ σ₂ ⟨⟨hP1, h01⟩, ⟨hP2, h02⟩, hbr1, hbr2⟩
    -- pure deviations
    have hb1 : ∀ p, 0 ≤ p → (p - c) * x p * mbWin σ₂ p ≤ mbPayoff x c σ₁ σ₂ := fun p hp => by
      rw [← mbPayoff_dirac]; exact hbr1 _ (isMixedPrice_dirac hp)
    have hb2 : ∀ p, 0 ≤ p → (p - c) * x p * mbWin σ₁ p ≤ mbPayoff x c σ₂ σ₁ := fun p hp => by
      rw [← mbPayoff_dirac]; exact hbr2 _ (isMixedPrice_dirac hp)
    set V₁ := mbPayoff x c σ₁ σ₂ with hV₁
    set V₂ := mbPayoff x c σ₂ σ₁ with hV₂
    have hae1 : ∀ᵐ p ∂σ₁, (p - c) * x p * mbWin σ₂ p = V₁ := mb_ae_eq hx h01 hb1
    have hae2 : ∀ᵐ p ∂σ₂, (p - c) * x p * mbWin σ₁ p = V₂ := mb_ae_eq hx h02 hb2
    have hpos1 := mb_ae_nonneg h01
    have hpos2 := mb_ae_nonneg h02
    -- profits are nonnegative: a price above `p̄` sells nothing
    have hq : ∀ τ : Measure ℝ, (max pbar 0 - c) * x (max pbar 0) * mbWin τ (max pbar 0) = 0 := by
      intro τ; rw [hx.zero _ (le_max_left _ _)]; ring
    have hV₁0 : 0 ≤ V₁ := (hq σ₂).symm.le.trans (hb1 _ (le_max_right _ _))
    have hV₂0 : 0 ≤ V₂ := (hq σ₁).symm.le.trans (hb2 _ (le_max_right _ _))
    -- step 1: a positive profit for one firm gives a positive profit to the other
    have step1 : ∀ (σ τ : Measure ℝ) [IsProbabilityMeasure σ] [IsProbabilityMeasure τ] (V W : ℝ),
        0 < V → (∀ᵐ p ∂σ, 0 ≤ p ∧ (p - c) * x p * mbWin τ p = V) →
        (∀ p, 0 ≤ p → (p - c) * x p * mbWin σ p ≤ W) → 0 < W := by
      intro σ τ _ _ V W hV hae hbr
      have hgap := mb_gap hx hxc hV hae
      have hce : c < c + V / x c := by have := div_pos hV hxc; linarith
      obtain ⟨p, hp, hpos⟩ := mb_rival_pos hx hc hxc hce hgap
      linarith [hbr p hp]
    -- step 2: both profits cannot be positive
    have step2 : ¬ (0 < V₁ ∧ 0 < V₂) := by
      rintro ⟨hv1, hv2⟩
      obtain ⟨G, hG0, hG⟩ := mb_bound hx c
      -- almost every price of firm `i` wins with probability at least `Vᵢ/G`
      have hwin : ∀ (σ τ : Measure ℝ) [IsProbabilityMeasure σ] [IsProbabilityMeasure τ] (V : ℝ),
          0 < V → (∀ᵐ p ∂σ, 0 ≤ p ∧ (p - c) * x p * mbWin τ p = V) →
          0 < G ∧ ∀ᵐ p ∂σ, V / G ≤ τ.real (Ici p) := by
        intro σ τ _ _ V hV hae
        have hkey : ∀ p, 0 ≤ p → (p - c) * x p * mbWin τ p = V → V ≤ G * τ.real (Ici p) := by
          intro p hp heq
          have h1 := hG p hp
          have h2 := mbWin_le_Ici τ p
          have h3 := mbWin_nonneg τ p
          have h4 : (p - c) * x p ≤ G := (le_abs_self _).trans h1
          calc V = (p - c) * x p * mbWin τ p := heq.symm
            _ ≤ G * mbWin τ p := mul_le_mul_of_nonneg_right h4 h3
            _ ≤ G * τ.real (Ici p) := mul_le_mul_of_nonneg_left h2 hG0
        obtain ⟨p, -, hp, heq⟩ := mb_exists_mem (s := univ) (by simp) hae
        have hGpos : 0 < G := by
          have := hkey p hp heq
          have h5 : τ.real (Ici p) ≤ 1 := measureReal_le_one
          nlinarith
        refine ⟨hGpos, hae.mono fun p ⟨hp, heq⟩ => ?_⟩
        rw [div_le_iff₀ hGpos, mul_comm]
        exact hkey p hp heq
      -- almost every price named earns a positive profit, so wins with positive probability
      have hsupp : ∀ (σ τ : Measure ℝ) [IsProbabilityMeasure σ] [IsFiniteMeasure τ] (V : ℝ),
          0 < V → (∀ᵐ p ∂σ, (p - c) * x p * mbWin τ p = V) →
          (∀ᵐ p ∂σ, τ (Ici p) ≠ 0) ∧ σ (Ici pbar) = 0 := by
        intro σ τ _ _ V hV hae
        constructor
        · refine hae.mono fun p heq h0 => ?_
          have hr : τ.real (Ici p) = 0 := (measureReal_eq_zero_iff).2 h0
          have := mbWin_le_Ici τ p
          have hw : mbWin τ p = 0 := le_antisymm (hr ▸ this) (mbWin_nonneg τ p)
          rw [hw, mul_zero] at heq
          linarith
        · refine measure_mono_null ?_ (ae_iff.1 hae)
          intro p hp heq
          rw [hx.zero p hp] at heq
          simp at heq
          linarith
      have hae1' : ∀ᵐ p ∂σ₁, 0 ≤ p ∧ (p - c) * x p * mbWin σ₂ p = V₁ := hpos1.and hae1
      have hae2' : ∀ᵐ p ∂σ₂, 0 ≤ p ∧ (p - c) * x p * mbWin σ₁ p = V₂ := hpos2.and hae2
      obtain ⟨hG1, hw1⟩ := hwin σ₁ σ₂ V₁ hv1 hae1'
      obtain ⟨-, hw2⟩ := hwin σ₂ σ₁ V₂ hv2 hae2'
      obtain ⟨hs1, hbar1⟩ := hsupp σ₁ σ₂ V₁ hv1 hae1
      obtain ⟨hs2, hbar2⟩ := hsupp σ₂ σ₁ V₂ hv2 hae2
      obtain ⟨B₁, hB1, hA1, hC1⟩ := mb_top_atom (div_pos hv1 hG1) hw1 hs2 hbar2
      obtain ⟨B₂, hB2, -, hC2⟩ := mb_top_atom (div_pos hv2 hG1) hw2 hs1 hbar1
      have h21 : B₂ ≤ B₁ := by
        by_contra h
        push Not at h
        exact hC2 (measure_mono_null (Ici_subset_Ioi.2 h) hB1)
      have h12 : B₁ ≤ B₂ := by
        by_contra h
        push Not at h
        exact hC1 (measure_mono_null (Ici_subset_Ioi.2 h) hB2)
      have hBeq : B₂ = B₁ := le_antisymm h21 h12
      rw [hBeq] at hB2
      obtain ⟨p, hpB, heq⟩ := mb_exists_mem hA1 hae1
      rw [mem_singleton_iff.1 hpB] at heq
      exact mb_undercut hx hc hxc hv1 heq hB2 hb1
    have hv1 : V₁ = 0 := by
      by_contra h
      have hv1 : 0 < V₁ := lt_of_le_of_ne hV₁0 (Ne.symm h)
      exact step2 ⟨hv1, step1 σ₁ σ₂ V₁ V₂ hv1 (hpos1.and hae1) hb2⟩
    have hv2 : V₂ = 0 := by
      by_contra h
      have hv2 : 0 < V₂ := lt_of_le_of_ne hV₂0 (Ne.symm h)
      exact step2 ⟨step1 σ₂ σ₁ V₂ V₁ hv2 (hpos2.and hae2) hb1, hv2⟩
    -- step 3: with zero profits, both strategies are the point mass at `c`
    rw [hv1] at hb1 hae1
    rw [hv2] at hb2 hae2
    have hup2 := mb_above_null hx hc hxc hb1
    have hup1 := mb_above_null hx hc hxc hb2
    have hlow1 := mb_below_null hx hxc hae1 hae2
    have hlow2 := mb_below_null hx hxc hae2 hae1
    exact ⟨mb_eq_dirac hlow1 hup1, mb_eq_dirac hlow2 hup2⟩

end MWG.MarketPower
