/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGExternalitiesPublicGoods.Tools
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Private information: bargaining, quotas and taxes (MWG Section 11.E, pp. 368-372)

* The two-level model (p. 368): `b(θ) = π(h̄, θ) - π(0, θ)`, `c(η) = φ(0, η) - φ(h̄, η)`; the
  optimal level is `h̄` iff `b > c` (`twoLevel_optimal_iff`).
* **Bargaining under asymmetric information (11.E.1)** (p. 369): the consumer's take-it-or-leave-it
  demand `T` solves `max_T (1 - G(T))(T - c)`. The objective is positive for `T > c` and zero at
  `T = c`, so every solution has `T_c* > c` (`eq_11_E_1_gt`), and the firm rejects with positive
  probability `G(T_c*) - G(c) > 0` although `b > c` (`eq_11_E_1_inefficient`). MWG speaks of
  "the solution": a solution need not exist (`eq_11_E_1_no_solution`, with
  `G(b) = b/(1 + b)`; correction); with the exponential distribution it is `T* = c + 1`
  (`eq_11_E_1_exponential`).
* **Quotas and taxes** (pp. 369-371): a quota above which the firm still has positive marginal
  benefit binds for every `θ` (`quota_binds`); the losses under a quota or tax are the integrals of
  the marginal surplus between the chosen and optimal levels (`surplus_loss_integral`);
  Figure 11.E.4(a) (a quota is optimal for all `θ`, no tax is: `figure_11_E_4a`) and Figure
  11.E.4(b) (a tax is optimal for all `θ`, no quota is: `figure_11_E_4b`).
* Footnote 22 (a take-it-or-leave-it offer by the firm is efficient when the consumer's type is
  known: `footnote_22`); small type p. 372 (a uniform tax distributes the externality efficiently
  across firms: `uniform_tax_efficient`); tradable permits never lower surplus relative to the
  quota when only the total matters (`permits_ge_quota`), and footnote 23's counterexample when
  the sources are not perfect substitutes (`footnote_23`).
-/

namespace MWG.ExternalitiesPublicGoods

open MWG.CompetitiveMarkets

/-! ## The two-level model and bargaining -/

/-- In the two-level model (MWG, p. 368), aggregate surplus with `h̄` exceeds that with `0` by
`b - c`; so `h̄` is optimal iff `b ≥ c`, and strictly better iff `b > c`. -/
theorem twoLevel_optimal_iff (φ0 φbar π0 πbar : ℝ) :
    (φbar + πbar) - (φ0 + π0) = (πbar - π0) - (φ0 - φbar) := by ring

/-- The objective (11.E.1): the probability `1 - G(T)` that the firm accepts the demand `T`, times
the consumer's net gain `T - c`. -/
def bargObj (G : ℝ → ℝ) (c T : ℝ) : ℝ := (1 - G T) * (T - c)

/-- **(11.E.1)** (MWG, p. 369). If acceptance has positive probability at every demand
(`G < 1`), the objective is strictly positive for `T > c` and zero at `T = c`; hence every
solution satisfies `T_c* > c`. -/
theorem eq_11_E_1_gt (G : ℝ → ℝ) (hG : ∀ T, G T < 1) (c : ℝ) :
    (∀ T, c < T → 0 < bargObj G c T) ∧ bargObj G c c = 0 ∧
      ∀ Ts, (∀ T, bargObj G c T ≤ bargObj G c Ts) → c < Ts := by
  have hpos : ∀ T, c < T → 0 < bargObj G c T := fun T hT =>
    mul_pos (by linarith [hG T]) (by linarith)
  refine ⟨hpos, by simp [bargObj], fun Ts hmax => ?_⟩
  by_contra hle
  push Not at hle
  have h1 := hmax (c + 1)
  have h2 := hpos (c + 1) (by linarith)
  have h3 : bargObj G c Ts ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith [hG Ts])
    (by linarith)
  linarith

/-- **Inefficiency of bargaining** (MWG, p. 369). If `G` is strictly increasing on `[0, ∞)`
(positive density) and `0 < c < T_c*`, then with positive probability `G(T_c*) - G(c) > 0` the
firm's benefit satisfies `c < b ≤ T_c*`: the offer is rejected although `h = h̄` is optimal. -/
theorem eq_11_E_1_inefficient (G : ℝ → ℝ) (hG : StrictMonoOn G (Set.Ici 0)) {c Ts : ℝ}
    (hc : 0 < c) (hT : c < Ts) : 0 < G Ts - G c := by
  have := hG (Set.mem_Ici.2 hc.le) (Set.mem_Ici.2 (hc.trans hT).le) hT
  linarith

/-- The distribution `G(b) = b/(1 + b)` on `b ≥ 0` (density `1/(1 + b)² > 0`). -/
noncomputable def heavyG (b : ℝ) : ℝ := max b 0 / (1 + max b 0)

/-- **Correction to (11.E.1)** (MWG, p. 369): "the solution" may not exist. For
`G(b) = b/(1 + b)`, which satisfies the hypotheses (`G < 1`, strictly increasing on `[0, ∞)`),
and any cost `c > 0`, every demand `T` is beaten by another: (11.E.1) has no solution. -/
theorem eq_11_E_1_no_solution {c : ℝ} (hc : 0 < c) :
    (∀ T, heavyG T < 1) ∧ StrictMonoOn heavyG (Set.Ici 0) ∧
      ∀ T, ∃ T', bargObj heavyG c T < bargObj heavyG c T' := by
  have hval : ∀ T, 0 ≤ T → bargObj heavyG c T = (T - c) / (1 + T) := fun T hT => by
    simp only [bargObj, heavyG, max_eq_left hT]
    field_simp
    ring
  refine ⟨fun T => ?_, fun a ha b hb hab => ?_, fun T => ?_⟩
  · simp only [heavyG]
    rw [div_lt_one (by positivity)]
    linarith
  · simp only [heavyG, max_eq_left ha.out, max_eq_left hb.out]
    rw [div_lt_div_iff₀ (by linarith [ha.out]) (by linarith [hb.out])]
    linarith
  · rcases le_or_gt 0 T with hT | hT
    · refine ⟨T + 1, ?_⟩
      rw [hval T hT, hval (T + 1) (by linarith), div_lt_div_iff₀ (by linarith) (by linarith)]
      nlinarith
    · refine ⟨c + 1, ?_⟩
      have h1 : bargObj heavyG c T = T - c := by
        simp [bargObj, heavyG, max_eq_right hT.le]
      rw [h1, hval (c + 1) (by linarith)]
      have : 0 < (c + 1 - c) / (1 + (c + 1)) := by
        apply div_pos <;> linarith
      linarith

/-- The exponential distribution `G(b) = 1 - e^{-b}` on `b ≥ 0`. -/
noncomputable def expG (b : ℝ) : ℝ := 1 - Real.exp (-max b 0)

/-- **(11.E.1) with exponential benefits**: the consumer's optimal demand is `T* = c + 1 > c`. -/
theorem eq_11_E_1_exponential (c : ℝ) (hc : 0 < c) :
    (∀ T, expG T < 1) ∧ StrictMonoOn expG (Set.Ici 0) ∧
      ∀ T, bargObj expG c T ≤ bargObj expG c (c + 1) := by
  refine ⟨fun T => by simp [expG, Real.exp_pos], fun a ha b hb hab => ?_, fun T => ?_⟩
  · simp only [expG, max_eq_left ha.out, max_eq_left hb.out]
    have := Real.exp_lt_exp.2 (neg_lt_neg hab)
    linarith
  · have hv : bargObj expG c (c + 1) = Real.exp (-(c + 1)) := by
      simp only [bargObj, expG, max_eq_left (show (0 : ℝ) ≤ c + 1 by linarith)]
      ring
    rw [hv]
    rcases le_or_gt 0 T with hT | hT
    · simp only [bargObj, expG, max_eq_left hT, sub_sub_cancel]
      have h1 := Real.add_one_le_exp (T - c - 1)
      have h2 : Real.exp (-T) * Real.exp (T - c - 1) = Real.exp (-(c + 1)) := by
        rw [← Real.exp_add]; ring_nf
      have h3 := Real.exp_pos (-T)
      nlinarith
    · simp only [bargObj, expG, max_eq_right hT.le, neg_zero, Real.exp_zero, sub_self,
        sub_zero, one_mul]
      have := Real.exp_pos (-(c + 1))
      linarith

/-! ## Quotas and taxes -/

/-- The firm's choice under a quota `ĥ` (MWG, p. 369): `h^q` maximizes `π(·, θ)` on `[0, ĥ]`. -/
def IsQuotaChoice (pr : ℝ → ℝ) (hq h : ℝ) : Prop :=
  0 ≤ h ∧ h ≤ hq ∧ ∀ y, 0 ≤ y → y ≤ hq → pr y ≤ pr h

/-- **A binding quota** (MWG, p. 370). If the firm's marginal profit is decreasing and still
positive at the quota, `∂π(ĥ, θ)/∂h > 0`, then the firm produces exactly the quota:
`h^q(ĥ, θ) = ĥ`. (The firm's choice never depends on the consumer's type `η`.) -/
theorem quota_binds {pr dpr : ℝ → ℝ} (hpr : ∀ x, HasDerivAt pr (dpr x) x)
    (hanti : AntitoneOn dpr (Set.Ici 0)) {hq : ℝ} (hq0 : 0 ≤ hq) (hpos : 0 < dpr hq) (h : ℝ) :
    IsQuotaChoice pr hq h ↔ h = hq := by
  have hmono : StrictMonoOn pr (Set.Icc 0 hq) :=
    strictMonoOn_Icc_of_deriv_pos hpr fun x hx hxq =>
      lt_of_lt_of_le hpos (hanti hx hq0 hxq.le)
  constructor
  · rintro ⟨h0, hle, hmax⟩
    by_contra hne
    have := hmono ⟨h0, hle⟩ ⟨hq0, le_rfl⟩ (lt_of_le_of_ne hle hne)
    linarith [hmax hq hq0 le_rfl]
  · rintro rfl
    refine ⟨hq0, le_rfl, fun y hy hyq => ?_⟩
    rcases eq_or_lt_of_le hyq with heq | hlt
    · rw [heq]
    · exact (hmono ⟨hy, hyq⟩ ⟨hq0, le_rfl⟩ hlt).le

/-- **The loss in aggregate surplus** (MWG, p. 370). For surplus `φ(·, η) + π(·, θ)` with
decreasing marginal benefits, the difference in surplus between any two levels `a, b ≥ 0` (the
optimum `h°(θ, η)` and the level `h^q(ĥ, θ)` under a quota or `h^t(t, θ)` under a tax) is the
integral of the marginal surplus `∂π/∂h + ∂φ/∂h` between them. -/
theorem surplus_loss_integral {φ dφ pr dpr : ℝ → ℝ} (hφ : ∀ x, HasDerivAt φ (dφ x) x)
    (hpr : ∀ x, HasDerivAt pr (dpr x) x) (hφa : AntitoneOn dφ (Set.Ici 0))
    (hpra : AntitoneOn dpr (Set.Ici 0)) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (φ b + pr b) - (φ a + pr a) = ∫ h in a..b, (dpr h + dφ h) := by
  have hsub : Set.uIcc a b ⊆ Set.Ici 0 := fun x hx => by
    rcases Set.mem_uIcc.1 hx with h | h
    · exact Set.mem_Ici.2 (ha.trans h.1)
    · exact Set.mem_Ici.2 (hb.trans h.1)
  have hint : IntervalIntegrable (fun h => dpr h + dφ h) MeasureTheory.volume a b :=
    AntitoneOn.intervalIntegrable fun x hx y hy hxy =>
      add_le_add (hpra (hsub hx) (hsub hy) hxy) (hφa (hsub hx) (hsub hy) hxy)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => (hpr x).add (hφ x)) hint]
  simp only [Pi.add_apply]
  ring

/-- The firm's choice under a per-unit tax `t` (MWG, p. 370): `max_{h ≥ 0} π(h, θ) - t h`. -/
def IsTaxChoice' (pr : ℝ → ℝ) (t h : ℝ) : Prop :=
  0 ≤ h ∧ ∀ y, 0 ≤ y → pr y - t * y ≤ pr h - t * h

/-- With profit `θ h - h²/2` and tax `t`, the firm's choice is `max(θ - t, 0)`. -/
theorem lq_tax_choice (θ t h : ℝ) :
    IsTaxChoice' (fun h => θ * h - h ^ 2 / 2) t h ↔ h = max (θ - t) 0 := by
  have key : ∀ y, (θ * y - y ^ 2 / 2) - t * y = (θ - t) ^ 2 / 2 - (y - (θ - t)) ^ 2 / 2 :=
    fun y => by ring
  simp only [IsTaxChoice', key]
  constructor
  · rintro ⟨h0, hmax⟩
    rcases le_or_gt 0 (θ - t) with hp | hn
    · have := hmax (θ - t) hp
      rw [max_eq_left hp]
      nlinarith [sq_nonneg (h - (θ - t))]
    · have := hmax 0 le_rfl
      rw [max_eq_right hn.le]
      nlinarith
  · rintro rfl
    refine ⟨le_max_right _ _, fun y hy => ?_⟩
    rcases le_or_gt 0 (θ - t) with hp | hn
    · rw [max_eq_left hp]; nlinarith [sq_nonneg (y - (θ - t))]
    · rw [max_eq_right hn.le]; nlinarith

/-- With profit `θ h - h²/2` (`θ ≥ 0`) and quota `ĥ ≥ 0`, the firm's choice is `min(ĥ, θ)`. -/
theorem lq_quota_choice {θ hq : ℝ} (hθ : 0 ≤ θ) (hq0 : 0 ≤ hq) (h : ℝ) :
    IsQuotaChoice (fun h => θ * h - h ^ 2 / 2) hq h ↔ h = min hq θ := by
  have key : ∀ y, θ * y - y ^ 2 / 2 = θ ^ 2 / 2 - (y - θ) ^ 2 / 2 := fun y => by ring
  simp only [IsQuotaChoice, key]
  constructor
  · rintro ⟨h0, hle, hmax⟩
    rcases le_total hq θ with hqθ | hθq
    · rw [min_eq_left hqθ]
      have := hmax hq hq0 le_rfl
      nlinarith
    · rw [min_eq_right hθq]
      have := hmax θ hθ hθq
      nlinarith [sq_nonneg (h - θ)]
  · rintro rfl
    refine ⟨le_min hq0 hθ, min_le_left _ _, fun y hy hyq => ?_⟩
    rcases le_total hq θ with hqθ | hθq
    · rw [min_eq_left hqθ]; nlinarith
    · rw [min_eq_right hθq]; nlinarith [sq_nonneg (y - θ)]

/-- **Figure 11.E.4(a)** (MWG, pp. 371-372). The consumer's marginal cost is zero up to `h*` and
(effectively) infinite beyond: `φ(h) = -K max(h - h*, 0)` with `K` exceeding the firm's marginal
benefit `θ - h*`. For profits `θ h - h²/2` with types `h* < θ' < θ'' < h* + K`, the quota `ĥ = h*`
maximizes aggregate surplus for both types, but no tax gives `h*` for both types. -/
theorem figure_11_E_4a {hs K θ₁ θ₂ : ℝ} (hhs : 0 < hs) (h1 : hs < θ₁) (h12 : θ₁ < θ₂)
    (h2 : θ₂ < hs + K) :
    (∀ θ ∈ ({θ₁, θ₂} : Set ℝ), ∀ y, 0 ≤ y →
      (θ * y - y ^ 2 / 2) - K * max (y - hs) 0 ≤ (θ * hs - hs ^ 2 / 2) - K * max (hs - hs) 0) ∧
    IsQuotaChoice (fun h => θ₁ * h - h ^ 2 / 2) hs hs ∧
    IsQuotaChoice (fun h => θ₂ * h - h ^ 2 / 2) hs hs ∧
    ∀ t, ¬ (IsTaxChoice' (fun h => θ₁ * h - h ^ 2 / 2) t hs ∧
      IsTaxChoice' (fun h => θ₂ * h - h ^ 2 / 2) t hs) := by
  refine ⟨fun θ hθs y hy => ?_, ?_, ?_, fun t ⟨ht1, ht2⟩ => ?_⟩
  · have hθ : hs < θ ∧ θ < hs + K := by
      rcases hθs with h | h
      · rw [h]; exact ⟨h1, by linarith⟩
      · rw [Set.mem_singleton_iff.1 h]; exact ⟨by linarith, h2⟩
    rw [sub_self, max_self, mul_zero, sub_zero]
    rcases le_total y hs with hyle | hyge
    · rw [max_eq_right (by linarith), mul_zero, sub_zero]
      nlinarith
    · rw [max_eq_left (by linarith)]
      nlinarith
  · exact (lq_quota_choice (by linarith) hhs.le hs).2 (min_eq_left (by linarith)).symm
  · exact (lq_quota_choice (by linarith) hhs.le hs).2 (min_eq_left (by linarith)).symm
  · have e1 := (lq_tax_choice θ₁ t hs).1 ht1
    have e2 := (lq_tax_choice θ₂ t hs).1 ht2
    have p1 : hs = θ₁ - t := by
      rcases le_total 0 (θ₁ - t) with hp | hn
      · rwa [max_eq_left hp] at e1
      · rw [max_eq_right hn] at e1; linarith
    have p2 : hs = θ₂ - t := by
      rcases le_total 0 (θ₂ - t) with hp | hn
      · rwa [max_eq_left hp] at e2
      · rw [max_eq_right hn] at e2; linarith
    linarith

/-- **Figure 11.E.4(b)** (MWG, p. 371). If the consumer's marginal cost is a constant `t*`
(`φ(h) = -t* h`), the tax `t = t*` makes the firm maximize aggregate surplus for every `θ`
(for any profit function); with profits `θ h - h²/2` and types `t* < θ' < θ''`, no quota gives
the optimal levels `θ - t*` for both types. -/
theorem figure_11_E_4b (ts : ℝ) :
    (∀ (pr : ℝ → ℝ) (h : ℝ), IsTaxChoice' pr ts h ↔
      0 ≤ h ∧ ∀ y, 0 ≤ y → pr y + -ts * y ≤ pr h + -ts * h) ∧
    ∀ θ₁ θ₂ hq : ℝ, 0 < ts → ts < θ₁ → θ₁ < θ₂ → 0 ≤ hq →
      ¬ (IsQuotaChoice (fun h => θ₁ * h - h ^ 2 / 2) hq (θ₁ - ts) ∧
        IsQuotaChoice (fun h => θ₂ * h - h ^ 2 / 2) hq (θ₂ - ts)) := by
  refine ⟨fun pr h => ⟨fun ⟨h0, hm⟩ => ⟨h0, fun y hy => by linarith [hm y hy]⟩,
    fun ⟨h0, hm⟩ => ⟨h0, fun y hy => by linarith [hm y hy]⟩⟩,
    fun θ₁ θ₂ hq hts h1 h12 hq0 ⟨q1, q2⟩ => ?_⟩
  have e1 := (lq_quota_choice (by linarith) hq0 _).1 q1
  have e2 := (lq_quota_choice (by linarith) hq0 _).1 q2
  have a1 : θ₁ - ts = hq := by
    rcases le_total hq θ₁ with h | h
    · rwa [min_eq_left h] at e1
    · rw [min_eq_right h] at e1; linarith
  have a2 : θ₂ - ts = hq := by
    rcases le_total hq θ₂ with h | h
    · rwa [min_eq_left h] at e2
    · rw [min_eq_right h] at e2; linarith
  linarith

/-- **Footnote 22** (MWG, p. 371). If the firm makes the take-it-or-leave-it offer and the
consumer's type is known (she accepts iff `φ(h) + T ≥ φ(0)`), the firm's offer maximizes
`π(h) - T`, so `h` maximizes aggregate surplus: the outcome is optimal. -/
theorem footnote_22 (φ pr : ℝ → ℝ) (h T : ℝ) :
    IsTIOLIOffer (Set.Ici 0) pr φ (φ 0) h (-T) ↔
      0 ≤ h ∧ (∀ y, 0 ≤ y → pr y + φ y ≤ pr h + φ h) ∧ T = φ 0 - φ h := by
  rw [tioli_iff]
  simp only [Set.mem_Ici]
  constructor
  · rintro ⟨a, b, c⟩; exact ⟨a, b, by linarith⟩
  · rintro ⟨a, b, c⟩; exact ⟨a, b, by linarith⟩

/-- **Small type, p. 372.** Under a uniform tax `t`, the total externality generated is
distributed efficiently across firms: if each `hⱼ` maximizes `πⱼ(hⱼ) - t hⱼ` on `ℝ₊`, then `h`
maximizes `∑ⱼ πⱼ` among all `h' ≥ 0` with the same total. -/
theorem uniform_tax_efficient {κ : Type*} [Fintype κ] (pr : κ → ℝ → ℝ) (t : ℝ) (h : κ → ℝ)
    (hch : ∀ j, IsTaxChoice' (pr j) t (h j)) (h' : κ → ℝ) (h0' : ∀ j, 0 ≤ h' j)
    (hsum : ∑ j, h' j = ∑ j, h j) : ∑ j, pr j (h' j) ≤ ∑ j, pr j (h j) := by
  have := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => (hch j).2 (h' j) (h0' j)
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, hsum] at this
  linarith

/-- **Tradable permits versus quotas** (MWG, small type, p. 372). Firms endowed with `h̄ⱼ` permits
(which they would fully use without trade) trade at price `p`; if each firm's choice `hⱼ` is optimal
given the price and the permit market clears, total profit is at least the quota profit
`∑ πⱼ(h̄ⱼ)`, and the total externality is unchanged. -/
theorem permits_ge_quota {κ : Type*} [Fintype κ] (pr : κ → ℝ → ℝ) (p : ℝ) (hbar h : κ → ℝ)
    (hbar0 : ∀ j, 0 ≤ hbar j)
    (hch : ∀ j, ∀ y, 0 ≤ y → pr j y + p * (hbar j - y) ≤ pr j (h j) + p * (hbar j - h j))
    (hclear : ∑ j, h j = ∑ j, hbar j) : ∑ j, pr j (hbar j) ≤ ∑ j, pr j (h j) := by
  have := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hch j (hbar j) (hbar0 j)
  simp only [sub_self, mul_zero, add_zero, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_sub_distrib, hclear] at this
  linarith

/-- **Footnote 23** (MWG, p. 372): if the externalities of different firms are not perfect
substitutes for the consumer, trading permits can lower aggregate surplus. Two firms with profits
`h - h²/2` and `3h - h²/2`, one permit each; the consumer's damage is `10 h₂` (only firm 2's
emissions harm her). The permit price `1` clears the market with uses `(0, 2)`: aggregate surplus
falls from `3 - 10 = -7` under the quota to `4 - 20 = -16`. -/
theorem footnote_23 :
    let pr : Fin 2 → ℝ → ℝ := fun j h => (if j = 0 then 1 else 3) * h - h ^ 2 / 2
    (∀ j : Fin 2, ∀ y, 0 ≤ y → pr j y + 1 * (1 - y) ≤
      pr j (![0, 2] j) + 1 * (1 - ![0, 2] j)) ∧ (0 : ℝ) + 2 = 1 + 1 ∧
      (pr 0 0 + pr 1 2 - 10 * 2) < (pr 0 1 + pr 1 1 - 10 * 1) := by
  intro pr
  refine ⟨fun j y hy => ?_, by norm_num, by simp only [pr]; norm_num⟩
  fin_cases j
  · simp only [pr]; norm_num; nlinarith
  · simp only [pr]; norm_num; nlinarith [sq_nonneg (y - 2)]

end MWG.ExternalitiesPublicGoods
