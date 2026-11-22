/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGMechanismDesign.Independent
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Abs

/-!
# Bayesian incentive compatibility with linear utility

MWG, Section 23.D, pp. 887-889: utilities `uᵢ(x, θᵢ) = θᵢvᵢ(k) + tᵢ` with types in intervals
`Θᵢ = [θ̲ᵢ, θ̄ᵢ]`, Proposition 23.D.2.

Agent `i`'s interim expected benefit and transfer when he announces `θ̂ᵢ` (the others telling the
truth) are `v̄ᵢ(θ̂ᵢ) = E_{θ₋ᵢ}[vᵢ(k(θ̂ᵢ, θ₋ᵢ))]` and `t̄ᵢ(θ̂ᵢ) = E_{θ₋ᵢ}[tᵢ(θ̂ᵢ, θ₋ᵢ)]`, and
`Uᵢ(θᵢ) = θᵢv̄ᵢ(θᵢ) + t̄ᵢ(θᵢ)`; (23.D.10) is `E[uᵢ | θᵢ, θ̂ᵢ] = θᵢv̄ᵢ(θ̂ᵢ) + t̄ᵢ(θ̂ᵢ)`.

* `integral_eq_of_slope_bounds`: if `(y - x)v̄(x) ≤ U(y) - U(x) ≤ (y - x)v̄(y)` and `v̄` is
  nondecreasing, then `U(θ) = U(θ̲) + ∫_{θ̲}^{θ} v̄`. (Proved by a telescoping estimate over
  uniform partitions; no differentiability of `U` is used.)
* `linearIC_iff` and **Proposition 23.D.2** (`proposition_23_D_2`): `f` is Bayesian incentive
  compatible iff each `v̄ᵢ` is nondecreasing (23.D.11) and (23.D.12) holds.
* **Correction**: the proof's claim "`Uᵢ'(θᵢ) = v̄ᵢ(θᵢ)` for all `θᵢ`" fails where `v̄ᵢ` jumps:
  for `k(θ) = 1{θ ≥ 1/2}`, `t(θ) = -k(θ)/2` (Bayesian incentive compatible), `U(θ) =
  max(0, θ - 1/2)` is not differentiable at `1/2` (`proposition_23_D_2_derivative_false`). Only
  the integral form (23.D.12) is needed, and it holds.
* p. 889: the expected transfers are `t̄ᵢ(θᵢ) = t̄ᵢ(θ̲ᵢ) + θ̲ᵢv̄ᵢ(θ̲ᵢ) - θᵢv̄ᵢ(θᵢ) + ∫ v̄ᵢ`
  (`expected_transfer_formula`), and `tᵢ(θ) = t̄ᵢ(θᵢ)` realizes given expected transfers.
-/

namespace MWG.MechanismDesign

open MeasureTheory Set Finset Function

/-- If `v̄` is nondecreasing on `[a, b]` and `(y - x)v̄(x) ≤ U(y) - U(x) ≤ (y - x)v̄(y)` for
`a ≤ x ≤ y ≤ b`, then `U(θ) = U(a) + ∫_a^θ v̄` on `[a, b]`. -/
theorem integral_eq_of_slope_bounds {U vb : ℝ → ℝ} {a b : ℝ} (hvb : MonotoneOn vb (Icc a b))
    (hU : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x ≤ y →
      (y - x) * vb x ≤ U y - U x ∧ U y - U x ≤ (y - x) * vb y) :
    ∀ θ ∈ Icc a b, U θ = U a + ∫ s in a..θ, vb s := by
  intro θ hθ
  have hab : a ≤ b := hθ.1.trans hθ.2
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  let G : ℝ → ℝ := fun x => U x - ∫ s in a..x, vb s
  have hii : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, IntervalIntegrable vb volume x y :=
    fun x hx y hy => (hvb.mono (uIcc_subset_Icc hx hy)).intervalIntegrable
  have hstep : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x ≤ y → |G y - G x| ≤ (y - x) * (vb y - vb x) := by
    intro x hx y hy hxy
    have hsplit : ∫ s in a..y, vb s = (∫ s in a..x, vb s) + ∫ s in x..y, vb s :=
      (intervalIntegral.integral_add_adjacent_intervals (hii a ha x hx) (hii x hx y hy)).symm
    have hlo : (y - x) * vb x ≤ ∫ s in x..y, vb s := by
      have := intervalIntegral.integral_mono_on hxy intervalIntegrable_const (hii x hx y hy)
        fun s hs => hvb hx ⟨hx.1.trans hs.1, hs.2.trans hy.2⟩ hs.1
      simpa [intervalIntegral.integral_const, smul_eq_mul] using this
    have hhi : ∫ s in x..y, vb s ≤ (y - x) * vb y := by
      have := intervalIntegral.integral_mono_on hxy (hii x hx y hy) intervalIntegrable_const
        fun s hs => hvb ⟨hx.1.trans hs.1, hs.2.trans hy.2⟩ hy hs.2
      simpa [intervalIntegral.integral_const, smul_eq_mul] using this
    obtain ⟨h1, h2⟩ := hU x hx y hy hxy
    have hG : G y - G x = (U y - U x) - ∫ s in x..y, vb s := by
      simp only [G, hsplit]; ring
    rw [hG, abs_le]
    constructor <;> nlinarith
  have hvθ : vb a ≤ vb θ := hvb ha hθ hθ.1
  have key : ∀ n : ℕ, 0 < n → |G θ - G a| ≤ (θ - a) * (vb θ - vb a) / n := by
    intro n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    set d := (θ - a) / n with hd
    have hd0 : 0 ≤ d := div_nonneg (by linarith [hθ.1]) hn'.le
    let x : ℕ → ℝ := fun k => a + k * d
    have hxn : x n = θ := by simp only [x, d]; field_simp; ring
    have hx0 : x 0 = a := by simp [x]
    have hxmem : ∀ k ≤ n, x k ∈ Icc a b := by
      intro k hk
      have hk' : (k : ℝ) ≤ n := by exact_mod_cast hk
      refine ⟨by simp only [x]; nlinarith, ?_⟩
      have : x k ≤ x n := by simp only [x]; nlinarith
      rw [hxn] at this
      exact this.trans hθ.2
    have htel : G θ - G a = ∑ k ∈ range n, (G (x (k + 1)) - G (x k)) := by
      rw [sum_range_sub (fun k => G (x k)), hxn, hx0]
    have htel2 : vb θ - vb a = ∑ k ∈ range n, (vb (x (k + 1)) - vb (x k)) := by
      rw [sum_range_sub (fun k => vb (x k)), hxn, hx0]
    have heq : (θ - a) * (vb θ - vb a) / n = d * (vb θ - vb a) := by rw [hd]; ring
    rw [heq, htel, htel2, mul_sum]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k hk => ?_)
    have hk' : k + 1 ≤ n := mem_range.1 hk
    have hxd : x (k + 1) - x k = d := by simp only [x]; push_cast; ring
    have := hstep (x k) (hxmem k (by omega)) (x (k + 1)) (hxmem (k + 1) hk') (by linarith)
    rwa [hxd] at this
  have hC : 0 ≤ (θ - a) * (vb θ - vb a) := mul_nonneg (by linarith [hθ.1]) (by linarith)
  have hle : |G θ - G a| ≤ 0 := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨n, hn⟩ := exists_nat_gt ((θ - a) * (vb θ - vb a) / ε)
    have hn0 : 0 < n := by
      have : (0 : ℝ) < n := lt_of_le_of_lt (div_nonneg hC hε.le) hn
      exact_mod_cast this
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
    have h1 := key n hn0
    have h2 : (θ - a) * (vb θ - vb a) / n ≤ ε := by
      rw [div_le_iff₀ hn']
      rw [div_lt_iff₀ hε] at hn
      linarith
    linarith
  have hG0 : G θ = G a := by
    have := abs_nonneg (G θ - G a)
    have h0 : |G θ - G a| = 0 := le_antisymm hle this
    linarith [abs_eq_zero.1 h0]
  simp only [G, intervalIntegral.integral_same, sub_zero] at hG0
  linarith

/-- **(23.D.1)** in the linear model, for one agent (MWG, p. 888, via (23.D.10)): truth telling
is optimal for every type `θ ∈ [θ̲, θ̄]` facing the interim functions `v̄`, `t̄`:
`θv̄(θ̂) + t̄(θ̂) ≤ θv̄(θ) + t̄(θ)` for all `θ̂ ∈ [θ̲, θ̄]`. -/
def LinearIC (vb tb : ℝ → ℝ) (lo hi : ℝ) : Prop :=
  ∀ θ ∈ Icc lo hi, ∀ θh ∈ Icc lo hi, θ * vb θh + tb θh ≤ θ * vb θ + tb θ

/-- **Proposition 23.D.2** (MWG, p. 888), one agent's interim functions: incentive compatibility
holds iff `v̄` is nondecreasing (23.D.11) and `U(θ) = U(θ̲) + ∫_{θ̲}^{θ} v̄` (23.D.12), where
`U(θ) = θv̄(θ) + t̄(θ)`. -/
theorem linearIC_iff {vb tb : ℝ → ℝ} {lo hi : ℝ} :
    LinearIC vb tb lo hi ↔ MonotoneOn vb (Icc lo hi) ∧
      ∀ θ ∈ Icc lo hi, θ * vb θ + tb θ = (lo * vb lo + tb lo) + ∫ s in lo..θ, vb s := by
  constructor
  · intro h
    -- (23.D.13)
    have hmono : MonotoneOn vb (Icc lo hi) := by
      intro x hx y hy hxy
      rcases hxy.lt_or_eq with hlt | heq
      · have h1 := h x hx y hy
        have h2 := h y hy x hx
        by_contra hc
        push Not at hc
        nlinarith
      · rw [heq]
    refine ⟨hmono, integral_eq_of_slope_bounds (U := fun θ => θ * vb θ + tb θ) hmono
      fun x hx y hy _ => ⟨?_, ?_⟩⟩
    · have := h y hy x hx; linarith
    · have := h x hx y hy; linarith
  · rintro ⟨hmono, hU⟩ θ hθ θh hθh
    have hii : ∀ x ∈ Icc lo hi, ∀ y ∈ Icc lo hi, IntervalIntegrable vb volume x y :=
      fun x hx y hy => (hmono.mono (uIcc_subset_Icc hx hy)).intervalIntegrable
    have hlo : lo ∈ Icc lo hi := ⟨le_rfl, hθ.1.trans hθ.2⟩
    have hdiff : (θ * vb θ + tb θ) - (θh * vb θh + tb θh) = ∫ s in θh..θ, vb s := by
      rw [hU θ hθ, hU θh hθh]
      rw [← intervalIntegral.integral_add_adjacent_intervals (hii lo hlo θh hθh) (hii θh hθh θ hθ)]
      ring
    rcases le_total θh θ with hle | hle
    · have := intervalIntegral.integral_mono_on hle intervalIntegrable_const (hii θh hθh θ hθ)
        fun s hs => hmono hθh ⟨hθh.1.trans hs.1, hs.2.trans hθ.2⟩ hs.1
      simp only [intervalIntegral.integral_const, smul_eq_mul] at this
      nlinarith
    · have := intervalIntegral.integral_mono_on hle (hii θ hθ θh hθh) intervalIntegrable_const
        fun s hs => hmono ⟨hθ.1.trans hs.1, hs.2.trans hθh.2⟩ hθh hs.2
      simp only [intervalIntegral.integral_const, smul_eq_mul] at this
      rw [intervalIntegral.integral_symm] at hdiff
      nlinarith

variable {ι : Type*} [DecidableEq ι] {K : Type*}

/-- Linear utility `uᵢ(x, θᵢ) = θᵢvᵢ(k) + tᵢ` (MWG, p. 887, with `m̄ᵢ = 0`). -/
def linU (vk : ι → K → ℝ) : (i : ι) → K × (ι → ℝ) → ℝ → ℝ :=
  fun i x θi => θi * vk i x.1 + x.2 i

/-- Agent `i`'s expected benefit `v̄ᵢ(θ̂ᵢ) = E_{θ₋ᵢ}[vᵢ(k(θ̂ᵢ, θ₋ᵢ))]` (MWG, p. 887). -/
noncomputable def interimBenefit (P : Measure (ι → ℝ)) (vk : ι → K → ℝ) (k : (ι → ℝ) → K)
    (i : ι) (a : ℝ) : ℝ :=
  ∫ θ', vk i (k (update θ' i a)) ∂P

/-- Agent `i`'s expected transfer `t̄ᵢ(θ̂ᵢ) = E_{θ₋ᵢ}[tᵢ(θ̂ᵢ, θ₋ᵢ)]` (MWG, p. 887). -/
noncomputable def interimTransfer (P : Measure (ι → ℝ)) (t : (ι → ℝ) → ι → ℝ) (i : ι)
    (a : ℝ) : ℝ :=
  ∫ θ', t (update θ' i a) i ∂P

/-- Agent `i`'s interim utility from truth telling, `Uᵢ(θᵢ) = θᵢv̄ᵢ(θᵢ) + t̄ᵢ(θᵢ)` (MWG, p. 888). -/
noncomputable def interimU (P : Measure (ι → ℝ)) (vk : ι → K → ℝ) (k : (ι → ℝ) → K)
    (t : (ι → ℝ) → ι → ℝ) (i : ι) (a : ℝ) : ℝ :=
  a * interimBenefit P vk k i a + interimTransfer P t i a

/-- **(23.D.1)** with linear utilities and independent types (MWG, p. 887): for all `i` and
`θᵢ, θ̂ᵢ ∈ [θ̲ᵢ, θ̄ᵢ]`, `E_{θ₋ᵢ}[uᵢ(f(θ̂ᵢ, θ₋ᵢ), θᵢ)] ≤ E_{θ₋ᵢ}[uᵢ(f(θᵢ, θ₋ᵢ), θᵢ)]`, where the
expectation over `θ₋ᵢ` is taken under the prior `P`. -/
def BayesianICOn (P : Measure (ι → ℝ)) (vk : ι → K → ℝ) (k : (ι → ℝ) → K)
    (t : (ι → ℝ) → ι → ℝ) (lo hi : ι → ℝ) : Prop :=
  ∀ i, ∀ θi ∈ Icc (lo i) (hi i), ∀ θh ∈ Icc (lo i) (hi i),
    ∫ θ', linU vk i (k (update θ' i θh), t (update θ' i θh)) θi ∂P ≤
      ∫ θ', linU vk i (k (update θ' i θi), t (update θ' i θi)) θi ∂P

/-- The expectations of (23.D.10) exist: `vᵢ(k(θ̂ᵢ, ·))` and `tᵢ(θ̂ᵢ, ·)` are integrable for every
announcement `θ̂ᵢ ∈ Θᵢ`. -/
def InterimIntegrable (P : Measure (ι → ℝ)) (vk : ι → K → ℝ) (k : (ι → ℝ) → K)
    (t : (ι → ℝ) → ι → ℝ) (lo hi : ι → ℝ) : Prop :=
  ∀ i, ∀ a ∈ Icc (lo i) (hi i), Integrable (fun θ' => vk i (k (update θ' i a))) P ∧
    Integrable (fun θ' => t (update θ' i a) i) P

/-- **(23.D.10)** (MWG, p. 888). `E_{θ₋ᵢ}[uᵢ(f(θ̂ᵢ, θ₋ᵢ), θᵢ)] = θᵢv̄ᵢ(θ̂ᵢ) + t̄ᵢ(θ̂ᵢ)`. -/
theorem eq_23_D_10 {P : Measure (ι → ℝ)} {vk : ι → K → ℝ} {k : (ι → ℝ) → K}
    {t : (ι → ℝ) → ι → ℝ} {i : ι} {a : ℝ} (hv : Integrable (fun θ' => vk i (k (update θ' i a))) P)
    (ht : Integrable (fun θ' => t (update θ' i a) i) P) (θi : ℝ) :
    ∫ θ', linU vk i (k (update θ' i a), t (update θ' i a)) θi ∂P =
      θi * interimBenefit P vk k i a + interimTransfer P t i a := by
  simp only [linU]
  rw [integral_add (hv.const_mul θi) ht, integral_const_mul]
  rfl

/-- **Proposition 23.D.2** (MWG, p. 888). With linear utilities, types in intervals and
independent types (agent `i`'s beliefs about `θ₋ᵢ` are the prior `P` whatever his type), the
social choice function `f = (k, t)` is Bayesian incentive compatible iff for every `i`,
(i) `v̄ᵢ` is nondecreasing on `Θᵢ` (23.D.11) and
(ii) `Uᵢ(θᵢ) = Uᵢ(θ̲ᵢ) + ∫_{θ̲ᵢ}^{θᵢ} v̄ᵢ(s) ds` for all `θᵢ ∈ Θᵢ` (23.D.12).
(MWG assume densities `φᵢ > 0`; they are not needed here.) -/
theorem proposition_23_D_2 {P : Measure (ι → ℝ)} {vk : ι → K → ℝ} {k : (ι → ℝ) → K}
    {t : (ι → ℝ) → ι → ℝ} {lo hi : ι → ℝ} (hint : InterimIntegrable P vk k t lo hi) :
    BayesianICOn P vk k t lo hi ↔ ∀ i, MonotoneOn (interimBenefit P vk k i) (Icc (lo i) (hi i)) ∧
      ∀ θ ∈ Icc (lo i) (hi i), interimU P vk k t i θ =
        interimU P vk k t i (lo i) + ∫ s in (lo i)..θ, interimBenefit P vk k i s := by
  have hiff : BayesianICOn P vk k t lo hi ↔
      ∀ i, LinearIC (interimBenefit P vk k i) (interimTransfer P t i) (lo i) (hi i) := by
    refine forall_congr' fun i => ?_
    refine forall₂_congr fun θi hθi => forall₂_congr fun θh hθh => ?_
    rw [eq_23_D_10 (hint i θh hθh).1 (hint i θh hθh).2,
      eq_23_D_10 (hint i θi hθi).1 (hint i θi hθi).2]
  rw [hiff]
  exact forall_congr' fun i => linearIC_iff

/-- **Section 23.D** (MWG, p. 889). For a Bayesian incentive compatible `f`, the expected transfers
are `t̄ᵢ(θᵢ) = t̄ᵢ(θ̲ᵢ) + θ̲ᵢv̄ᵢ(θ̲ᵢ) - θᵢv̄ᵢ(θᵢ) + ∫_{θ̲ᵢ}^{θᵢ} v̄ᵢ(s) ds`. -/
theorem expected_transfer_formula {P : Measure (ι → ℝ)} {vk : ι → K → ℝ} {k : (ι → ℝ) → K}
    {t : (ι → ℝ) → ι → ℝ} {lo hi : ι → ℝ} (hint : InterimIntegrable P vk k t lo hi)
    (hf : BayesianICOn P vk k t lo hi) (i : ι) {θ : ℝ} (hθ : θ ∈ Icc (lo i) (hi i)) :
    interimTransfer P t i θ = interimTransfer P t i (lo i) + lo i * interimBenefit P vk k i (lo i)
      - θ * interimBenefit P vk k i θ + ∫ s in (lo i)..θ, interimBenefit P vk k i s := by
  have := ((proposition_23_D_2 hint).1 hf i).2 θ hθ
  simp only [interimU] at this
  linarith

/-- **Section 23.D** (MWG, p. 889). Given expected transfer functions `τᵢ`, the transfers
`tᵢ(θ) = τᵢ(θᵢ)` have expected transfers `t̄ᵢ = τᵢ` (beliefs are probability measures). -/
theorem interimTransfer_of_own {P : Measure (ι → ℝ)} [IsProbabilityMeasure P]
    (τ : ι → ℝ → ℝ) (i : ι) (a : ℝ) :
    interimTransfer P (fun θ j => τ j (θ j)) i a = τ i a := by
  simp [interimTransfer]

/-- **Proposition 23.D.2**, correction (MWG, p. 888). The claim "`Uᵢ'(θᵢ) = v̄ᵢ(θᵢ)` for all
`θᵢ`" fails at jumps of `v̄ᵢ`: with one agent on `[0, 1]`, `v̄(θ) = 1{θ ≥ 1/2}` and
`t̄ = -v̄/2` satisfy (23.D.1), but `U(θ) = θv̄(θ) + t̄(θ) = max(0, θ - 1/2)` is not differentiable
at `1/2`. -/
theorem proposition_23_D_2_derivative_false :
    let vb : ℝ → ℝ := fun θ => if θ < 1 / 2 then 0 else 1
    LinearIC vb (fun θ => -vb θ / 2) 0 1 ∧
      ¬DifferentiableAt ℝ (fun θ => θ * vb θ + -vb θ / 2) (1 / 2) := by
  intro vb
  have hU : (fun θ => θ * vb θ + -vb θ / 2) = fun θ => ((θ - 1 / 2) + |θ - 1 / 2|) / 2 := by
    funext θ
    simp only [vb]
    split_ifs with h
    · rw [abs_of_neg (by linarith)]; ring
    · rw [abs_of_nonneg (by linarith)]; ring
  refine ⟨fun θ _ θh _ => ?_, fun hd => ?_⟩
  · simp only [vb]
    split_ifs <;> nlinarith
  · rw [hU] at hd
    have hd' : DifferentiableAt ℝ (fun θ : ℝ => (θ + 1 / 2 - 1 / 2 + |θ + 1 / 2 - 1 / 2|) / 2) 0 :=
      (differentiableAt_comp_add_const (f := fun θ : ℝ => (θ - 1 / 2 + |θ - 1 / 2|) / 2)
        (a := 0) (b := 1 / 2)).2 (by rw [zero_add]; exact hd)
    have e : (fun θ : ℝ => |θ|) = fun θ => 2 * ((θ + 1 / 2 - 1 / 2 + |θ + 1 / 2 - 1 / 2|) / 2) -
        (θ + 1 / 2 - 1 / 2) := by
      funext θ
      simp only [add_sub_cancel_right]
      ring
    have h3 : DifferentiableAt ℝ (fun θ : ℝ => |θ|) 0 := by
      rw [e]
      exact (hd'.const_mul 2).sub ((differentiableAt_id.add_const _).sub_const _)
    exact not_differentiableAt_abs_zero h3

end MWG.MechanismDesign
