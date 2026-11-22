/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Probability.ConditionalProbability

/-!
# Pretrial settlement with an informed defendant

MWG, Exercise 9.C.4 (p. 304). Ms. P sues Ms. D for damages `π > 0` (`dmg` here: `π` may not
be used as a name); D knows the probability `λ ∈ [0, 1]` that P wins, P only knows its prior
distribution `μ` (a probability measure on `ℝ` concentrated on `[0, 1]`); going to trial costs
`c_p, c_d > 0`. P makes a take-it-or-leave-it offer `s`; D accepts (pays `s`) or rejects (trial:
P gets `λπ − c_p`, D pays `λπ + c_d`).

(a) The weak PBE (`IsSetWeakPBE`). D's information sets are singletons and P moves once, so a
weak PBE is: D best responds at every `(λ, s)` (`SetBR`: accept only if `s ≤ λπ + c_d`, reject
only if `s ≥ λπ + c_d`), and P's offer maximises her expected payoff against D's strategy.
`exercise_9_C_4a`: when the prior has no atoms (in particular when it has a density, as in the
book), `(s, acc)` is a weak PBE iff D best responds and `s` maximises
`V(s) = E[s·1{λπ + c_d ≥ s} + (λπ − c_p)·1{λπ + c_d < s}]`; and (`setV_eq`) with
`t = (s − c_d)/π` (the type indifferent at `s`),
`V(s) = π E[min(λ, t)] + c_d − (c_p + c_d) Prob(λ < t)`; the equilibrium offer satisfies
`s ≥ c_d` (`setOffer_ge`), and trial happens with probability `Prob(λ < t)` (`setTrial_eq`).

(b) Comparative statics, without any assumption on the prior beyond no atoms
(`exercise_9_C_4b`): the equilibrium probability of trial is weakly decreasing in
`(c_p + c_d)/π`, hence weakly decreasing in `c_p` and in `c_d` and weakly increasing in `π`;
P's equilibrium payoff is weakly decreasing in `c_p` and weakly increasing in `c_d` and in `π`
(`exercise_9_C_4b_payoff`). Example: with the uniform prior and `c_p + c_d ≥ π`, P offers `c_d`
and every type settles (`exercise_9_C_4_uniform`).

(c) (the book says "Ms. D"; the agent whose offer was rejected is Ms. P, see
docs/corrections.md): after a rejection P chooses between trial and dropping the case. See
`exercise_9_C_4c_no_trial`, `exercise_9_C_4c_drop`, `exercise_9_C_4c_settle`.
-/

namespace MWG.DynamicGames

open MeasureTheory ProbabilityTheory

/-- **Exercise 9.C.4(a)** (MWG, p. 304). D's best responses: type `x` accepts the offer `s`
only if paying `s` is no worse than the expected trial payment `x π + c_d`, and rejects only if
it is no better. -/
def SetBR (dmg cd : ℝ) (acc : ℝ → ℝ → Bool) : Prop :=
  ∀ x s, (acc x s = true → s ≤ x * dmg + cd) ∧ (acc x s = false → x * dmg + cd ≤ s)

/-- P's expected payoff from the offer `s` against D's strategy `acc`. -/
noncomputable def setPay (μ : Measure ℝ) (dmg cp : ℝ) (acc : ℝ → ℝ → Bool) (s : ℝ) : ℝ :=
  ∫ x, (if acc x s then s else x * dmg - cp) ∂μ

/-- **Exercise 9.C.4(a)** (MWG, p. 304). A pure-strategy weak PBE: D best responds at each of
her (singleton) information sets, and P's offer is optimal given D's strategy and the prior. -/
def IsSetWeakPBE (μ : Measure ℝ) (dmg cp cd s : ℝ) (acc : ℝ → ℝ → Bool) : Prop :=
  SetBR dmg cd acc ∧ ∀ s', setPay μ dmg cp acc s' ≤ setPay μ dmg cp acc s

/-- P's expected payoff from the offer `s` when the types that weakly prefer settling accept. -/
noncomputable def setV (μ : Measure ℝ) (dmg cp cd s : ℝ) : ℝ :=
  ∫ x, (if s ≤ x * dmg + cd then s else x * dmg - cp) ∂μ

/-- `E[min(λ, t)]` under the prior. -/
noncomputable def setM (μ : Measure ℝ) (t : ℝ) : ℝ := ∫ x, min x t ∂μ

variable {μ : Measure ℝ}

/-- Against a best-responding D, P's payoff is `V(s)` when the prior has no atoms (only the
type indifferent at `s` may act otherwise, and it has probability zero). -/
theorem setPay_eq_setV [NullSingletonClass μ] {dmg cp cd : ℝ} (hdmg : 0 < dmg)
    {acc : ℝ → ℝ → Bool} (h : SetBR dmg cd acc) (s : ℝ) :
    setPay μ dmg cp acc s = setV μ dmg cp cd s := by
  refine integral_congr_ae ?_
  have hne : ∀ᵐ x ∂μ, x ≠ (s - cd) / dmg := by
    rw [ae_iff]
    simp
  filter_upwards [hne] with x hx
  have hx' : x * dmg + cd ≠ s := fun he => hx (by field_simp; linarith)
  cases hc : acc x s
  · have h1 := (h x s).2 hc
    have h2 : ¬ s ≤ x * dmg + cd := fun h3 => hx' (le_antisymm h1 h3)
    simp [h2]
  · simp [(h x s).1 hc]

/-- **Exercise 9.C.4(a)** (MWG, p. 304). With an atomless prior, `(s, acc)` is a weak PBE iff D
best responds and `s` maximises `V`. -/
theorem exercise_9_C_4a [NullSingletonClass μ] {dmg cp cd s : ℝ} (hdmg : 0 < dmg)
    {acc : ℝ → ℝ → Bool} :
    IsSetWeakPBE μ dmg cp cd s acc ↔ SetBR dmg cd acc ∧ ∀ s', setV μ dmg cp cd s' ≤
      setV μ dmg cp cd s := by
  constructor
  · rintro ⟨h, hopt⟩
    refine ⟨h, fun s' => ?_⟩
    rw [← setPay_eq_setV hdmg h, ← setPay_eq_setV hdmg h]
    exact hopt s'
  · rintro ⟨h, hopt⟩
    refine ⟨h, fun s' => ?_⟩
    rw [setPay_eq_setV hdmg h, setPay_eq_setV hdmg h]
    exact hopt s'

/-- `min λ t` is integrable for a probability measure concentrated on `[0, 1]`. -/
theorem integrable_min [IsProbabilityMeasure μ] (hsupp : ∀ᵐ x ∂μ, x ∈ Set.Icc (0 : ℝ) 1)
    (t : ℝ) : Integrable (fun x => min x t) μ := by
  refine Integrable.of_bound (continuous_id.min continuous_const).aestronglyMeasurable
    (max 1 |t|) ?_
  filter_upwards [hsupp] with x hx
  rw [Real.norm_eq_abs]
  rcases le_total x t with h | h
  · rw [min_eq_left h, abs_of_nonneg hx.1]
    exact le_trans hx.2 (le_max_left _ _)
  · rw [min_eq_right h]
    exact le_max_right _ _

/-- **Exercise 9.C.4(a)**, the reduced form (MWG, p. 304). With `t = (s − c_d)/π`,
`V(s) = π E[min(λ, t)] + c_d − (c_p + c_d) Prob(λ < t)`. -/
theorem setV_eq [IsProbabilityMeasure μ] (hsupp : ∀ᵐ x ∂μ, x ∈ Set.Icc (0 : ℝ) 1)
    {dmg cp cd : ℝ} (hdmg : 0 < dmg) (s : ℝ) :
    setV μ dmg cp cd s = dmg * setM μ ((s - cd) / dmg) + cd -
      (cp + cd) * μ.real (Set.Iio ((s - cd) / dmg)) := by
  set t := (s - cd) / dmg with ht
  have hs : s = cd + dmg * t := by rw [ht]; field_simp; ring
  have hpt : ∀ x, (if s ≤ x * dmg + cd then s else x * dmg - cp) =
      dmg * min x t + cd - (cp + cd) * (Set.Iio t).indicator 1 x := by
    intro x
    by_cases hx : t ≤ x
    · have : s ≤ x * dmg + cd := by rw [hs]; nlinarith
      rw [min_eq_right hx, Set.indicator_of_notMem (show x ∉ Set.Iio t from not_lt.2 hx)]
      simp only [this, ↓reduceIte]
      linarith
    · have hx' : x < t := not_le.1 hx
      have : ¬ s ≤ x * dmg + cd := by rw [hs]; nlinarith
      rw [min_eq_left hx'.le, Set.indicator_of_mem (show x ∈ Set.Iio t from hx'), Pi.one_apply]
      simp only [this, ↓reduceIte]
      ring
  unfold setV
  simp_rw [hpt]
  have hI1 : Integrable (fun x => dmg * min x t) μ := (integrable_min hsupp t).const_mul dmg
  have hI2 : Integrable (fun x => (cp + cd) * (Set.Iio t).indicator 1 x) μ :=
    ((integrable_const (1 : ℝ)).indicator measurableSet_Iio).const_mul _
  have hA : Integrable (fun x => dmg * min x t + cd) μ := hI1.add (integrable_const cd)
  rw [integral_sub hA hI2, integral_add hI1 (integrable_const cd),
    integral_const_mul, integral_const_mul, integral_indicator_one measurableSet_Iio,
    integral_const, probReal_univ, one_smul]
  rfl

/-- Against a best-responding D, the probability of trial is `Prob(λ < t)` (atomless prior). -/
theorem setTrial_eq [IsProbabilityMeasure μ] [NullSingletonClass μ] {dmg cd : ℝ} (hdmg : 0 < dmg)
    {acc : ℝ → ℝ → Bool} (h : SetBR dmg cd acc) (s : ℝ) :
    μ.real {x | acc x s = false} = μ.real (Set.Iio ((s - cd) / dmg)) := by
  set t := (s - cd) / dmg with ht
  have hs : s = cd + dmg * t := by rw [ht]; field_simp; ring
  have h1 : Set.Iio t ⊆ {x | acc x s = false} := by
    intro x hx
    change acc x s = false
    cases hc : acc x s
    · rfl
    · have := (h x s).1 hc
      rw [hs] at this
      have : t ≤ x := by nlinarith [Set.mem_Iio.1 hx]
      exact absurd hx (not_lt.2 this)
  have h2 : {x | acc x s = false} ⊆ Set.Iic t := by
    intro x hx
    have := (h x s).2 hx
    rw [hs] at this
    change x ≤ t
    nlinarith
  refine le_antisymm ?_ (measureReal_mono h1)
  calc μ.real {x | acc x s = false} ≤ μ.real (Set.Iic t) := measureReal_mono h2
    _ = μ.real (Set.Iio t) := by rw [measureReal_def, measureReal_def, measure_congr Iio_ae_eq_Iic]

/-- `E[min(λ, t)] = t` for `t ≤ 0`, and `E[min(λ, t)] ≥ 0` for `t ≥ 0`. -/
theorem setM_facts [IsProbabilityMeasure μ] (hsupp : ∀ᵐ x ∂μ, x ∈ Set.Icc (0 : ℝ) 1) (t : ℝ) :
    (t ≤ 0 → setM μ t = t) ∧ (0 ≤ t → 0 ≤ setM μ t) := by
  constructor
  · intro h
    unfold setM
    rw [integral_congr_ae (g := fun _ => t) ?_, integral_const, probReal_univ, one_smul]
    filter_upwards [hsupp] with x hx
    exact min_eq_right (le_trans h hx.1)
  · intro h
    exact integral_nonneg_of_ae (by filter_upwards [hsupp] with x hx; exact le_min hx.1 h)

/-- `Prob(λ < t) = 0` for `t ≤ 0`. -/
theorem setG_zero [IsProbabilityMeasure μ] (hsupp : ∀ᵐ x ∂μ, x ∈ Set.Icc (0 : ℝ) 1) {t : ℝ}
    (h : t ≤ 0) : μ.real (Set.Iio t) = 0 := by
  have h0 : μ {x | ¬ x ∈ Set.Icc (0 : ℝ) 1} = 0 := ae_iff.1 hsupp
  have hsub : Set.Iio t ⊆ {x | x ∉ Set.Icc (0 : ℝ) 1} := fun x hx hm =>
    absurd (lt_of_lt_of_le (Set.mem_Iio.1 hx) h) (not_lt.2 hm.1)
  rw [measureReal_def, measure_mono_null hsub h0, ENNReal.toReal_zero]

/-- `V` below `c_d`: an offer `s ≤ c_d` is accepted by every type and earns `s`. -/
theorem setV_of_le [IsProbabilityMeasure μ] (hsupp : ∀ᵐ x ∂μ, x ∈ Set.Icc (0 : ℝ) 1)
    {dmg cp cd : ℝ} (hdmg : 0 < dmg) {s : ℝ} (hs : s ≤ cd) : setV μ dmg cp cd s = s := by
  have ht : (s - cd) / dmg ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hdmg.le
  rw [setV_eq hsupp hdmg, (setM_facts hsupp _).1 ht, setG_zero hsupp ht]
  field_simp
  ring

/-- **Exercise 9.C.4(a)** (MWG, p. 304). In every weak PBE the offer is at least `c_d` (lower
offers are accepted by all types and are beaten by `c_d`), so the indifferent type
`t = (s − c_d)/π` is nonnegative. -/
theorem setOffer_ge [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (hsupp : ∀ᵐ x ∂μ, x ∈ Set.Icc (0 : ℝ) 1) {dmg cp cd s : ℝ} (hdmg : 0 < dmg)
    {acc : ℝ → ℝ → Bool} (h : IsSetWeakPBE μ dmg cp cd s acc) : cd ≤ s := by
  by_contra hn
  have hopt := ((exercise_9_C_4a hdmg).1 h).2 cd
  rw [setV_of_le hsupp hdmg le_rfl, setV_of_le hsupp hdmg (not_le.1 hn).le] at hopt
  exact hn hopt

/-- P's payoff from the offer that makes type `t` indifferent, in reduced form. -/
theorem setV_thr [IsProbabilityMeasure μ] (hsupp : ∀ᵐ x ∂μ, x ∈ Set.Icc (0 : ℝ) 1)
    {dmg cp cd : ℝ} (hdmg : 0 < dmg) (t : ℝ) :
    setV μ dmg cp cd (cd + dmg * t) = dmg * setM μ t + cd - (cp + cd) * μ.real (Set.Iio t) := by
  rw [setV_eq hsupp hdmg]
  have : (cd + dmg * t - cd) / dmg = t := by field_simp; ring
  rw [this]

/-- **Exercise 9.C.4(b)** (MWG, p. 304), the key comparison. Let `(s₁, acc₁)` and `(s₂, acc₂)`
be weak PBE for parameters `(c_p, c_d, π)₁` and `(c_p, c_d, π)₂` (same prior, no atoms). If
`(c_p + c_d)/π` is smaller in the first, the probability of trial is weakly larger in the
first. -/
theorem setTrial_anti [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (hsupp : ∀ᵐ x ∂μ, x ∈ Set.Icc (0 : ℝ) 1) {dmg₁ cp₁ cd₁ s₁ dmg₂ cp₂ cd₂ s₂ : ℝ}
    (hd₁ : 0 < dmg₁) (hd₂ : 0 < dmg₂) {acc₁ acc₂ : ℝ → ℝ → Bool}
    (h₁ : IsSetWeakPBE μ dmg₁ cp₁ cd₁ s₁ acc₁) (h₂ : IsSetWeakPBE μ dmg₂ cp₂ cd₂ s₂ acc₂)
    (hk : (cp₁ + cd₁) / dmg₁ < (cp₂ + cd₂) / dmg₂) :
    μ.real {x | acc₂ x s₂ = false} ≤ μ.real {x | acc₁ x s₁ = false} := by
  obtain ⟨b₁, o₁⟩ := (exercise_9_C_4a hd₁).1 h₁
  obtain ⟨b₂, o₂⟩ := (exercise_9_C_4a hd₂).1 h₂
  rw [setTrial_eq hd₁ b₁, setTrial_eq hd₂ b₂]
  set t₁ := (s₁ - cd₁) / dmg₁ with ht₁
  set t₂ := (s₂ - cd₂) / dmg₂ with ht₂
  have e₁ : s₁ = cd₁ + dmg₁ * t₁ := by rw [ht₁]; field_simp; ring
  have e₂ : s₂ = cd₂ + dmg₂ * t₂ := by rw [ht₂]; field_simp; ring
  have i₁ := o₁ (cd₁ + dmg₁ * t₂)
  have i₂ := o₂ (cd₂ + dmg₂ * t₁)
  rw [e₁, setV_thr hsupp hd₁, setV_thr hsupp hd₁] at i₁
  rw [e₂, setV_thr hsupp hd₂, setV_thr hsupp hd₂] at i₂
  set k₁ := (cp₁ + cd₁) / dmg₁
  set k₂ := (cp₂ + cd₂) / dmg₂
  have a₁ : cp₁ + cd₁ = k₁ * dmg₁ := by simp only [k₁]; field_simp
  have a₂ : cp₂ + cd₂ = k₂ * dmg₂ := by simp only [k₂]; field_simp
  rw [a₁] at i₁
  rw [a₂] at i₂
  set M₁ := setM μ t₁
  set M₂ := setM μ t₂
  set G₁ := μ.real (Set.Iio t₁)
  set G₂ := μ.real (Set.Iio t₂)
  have f₁ : 0 ≤ dmg₁ * (M₁ - M₂ - k₁ * (G₁ - G₂)) := by linarith
  have f₂ : 0 ≤ dmg₂ * (M₂ - M₁ - k₂ * (G₂ - G₁)) := by linarith
  have g₁ := (mul_nonneg_iff_of_pos_left hd₁).1 f₁
  have g₂ := (mul_nonneg_iff_of_pos_left hd₂).1 f₂
  by_contra hn
  nlinarith [mul_pos (sub_pos.2 hk) (sub_pos.2 (not_le.1 hn))]

/-- **Exercise 9.C.4(b)** (MWG, p. 304). Effects on the equilibrium probability of trial (any
atomless prior): it weakly falls when `c_p` rises, weakly falls when `c_d` rises, and weakly
rises when `π` rises. -/
theorem exercise_9_C_4b [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (hsupp : ∀ᵐ x ∂μ, x ∈ Set.Icc (0 : ℝ) 1) {dmg cp cd : ℝ} (hdmg : 0 < dmg) (hcp : 0 < cp)
    (hcd : 0 < cd) {s₁ s₂ : ℝ} {acc₁ acc₂ : ℝ → ℝ → Bool} :
    (∀ cp', cp < cp' → IsSetWeakPBE μ dmg cp cd s₁ acc₁ → IsSetWeakPBE μ dmg cp' cd s₂ acc₂ →
      μ.real {x | acc₂ x s₂ = false} ≤ μ.real {x | acc₁ x s₁ = false}) ∧
    (∀ cd', cd < cd' → IsSetWeakPBE μ dmg cp cd s₁ acc₁ → IsSetWeakPBE μ dmg cp cd' s₂ acc₂ →
      μ.real {x | acc₂ x s₂ = false} ≤ μ.real {x | acc₁ x s₁ = false}) ∧
    (∀ dmg', dmg < dmg' → IsSetWeakPBE μ dmg cp cd s₁ acc₁ →
      IsSetWeakPBE μ dmg' cp cd s₂ acc₂ →
      μ.real {x | acc₁ x s₁ = false} ≤ μ.real {x | acc₂ x s₂ = false}) := by
  refine ⟨fun cp' hlt h₁ h₂ => setTrial_anti hsupp hdmg hdmg h₁ h₂ ?_,
    fun cd' hlt h₁ h₂ => setTrial_anti hsupp hdmg hdmg h₁ h₂ ?_,
    fun dmg' hlt h₁ h₂ => setTrial_anti hsupp (by linarith) hdmg h₂ h₁ ?_⟩
  · exact div_lt_div_of_pos_right (by linarith) hdmg
  · exact div_lt_div_of_pos_right (by linarith) hdmg
  · exact div_lt_div_of_pos_left (by linarith) hdmg hlt

/-- **Exercise 9.C.4(b)** (MWG, p. 304). Effects on P's equilibrium payoff (any atomless prior):
it weakly falls when `c_p` rises and weakly rises when `c_d` or `π` rises. -/
theorem exercise_9_C_4b_payoff [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (hsupp : ∀ᵐ x ∂μ, x ∈ Set.Icc (0 : ℝ) 1) {dmg cp cd : ℝ} (hdmg : 0 < dmg)
    {s₁ s₂ : ℝ} {acc₁ acc₂ : ℝ → ℝ → Bool} :
    (∀ cp', cp ≤ cp' → IsSetWeakPBE μ dmg cp cd s₁ acc₁ → IsSetWeakPBE μ dmg cp' cd s₂ acc₂ →
      setPay μ dmg cp' acc₂ s₂ ≤ setPay μ dmg cp acc₁ s₁) ∧
    (∀ cd', cd ≤ cd' → IsSetWeakPBE μ dmg cp cd s₁ acc₁ → IsSetWeakPBE μ dmg cp cd' s₂ acc₂ →
      setPay μ dmg cp acc₁ s₁ ≤ setPay μ dmg cp acc₂ s₂) ∧
    (∀ dmg', dmg ≤ dmg' → IsSetWeakPBE μ dmg cp cd s₁ acc₁ →
      IsSetWeakPBE μ dmg' cp cd s₂ acc₂ →
      setPay μ dmg cp acc₁ s₁ ≤ setPay μ dmg' cp acc₂ s₂) := by
  have hG : ∀ t, 0 ≤ μ.real (Set.Iio t) ∧ μ.real (Set.Iio t) ≤ 1 :=
    fun t => ⟨measureReal_nonneg, measureReal_le_one⟩
  refine ⟨fun cp' hle h₁ h₂ => ?_, fun cd' hle h₁ h₂ => ?_, fun dmg' hle h₁ h₂ => ?_⟩
  · obtain ⟨b₁, o₁⟩ := (exercise_9_C_4a hdmg).1 h₁
    obtain ⟨b₂, -⟩ := (exercise_9_C_4a hdmg).1 h₂
    rw [setPay_eq_setV hdmg b₁, setPay_eq_setV hdmg b₂]
    refine le_trans ?_ (o₁ s₂)
    rw [setV_eq hsupp hdmg, setV_eq hsupp hdmg]
    nlinarith [(hG ((s₂ - cd) / dmg)).1]
  · obtain ⟨b₁, -⟩ := (exercise_9_C_4a hdmg).1 h₁
    obtain ⟨b₂, o₂⟩ := (exercise_9_C_4a hdmg).1 h₂
    rw [setPay_eq_setV hdmg b₁, setPay_eq_setV hdmg b₂]
    refine le_trans ?_ (o₂ (cd' + dmg * ((s₁ - cd) / dmg)))
    rw [setV_eq hsupp hdmg, setV_thr hsupp hdmg]
    nlinarith [(hG ((s₁ - cd) / dmg)).2]
  · have hd' : 0 < dmg' := by linarith
    obtain ⟨b₁, -⟩ := (exercise_9_C_4a hdmg).1 h₁
    obtain ⟨b₂, o₂⟩ := (exercise_9_C_4a hd').1 h₂
    rw [setPay_eq_setV hdmg b₁, setPay_eq_setV hd' b₂]
    refine le_trans ?_ (o₂ (cd + dmg' * ((s₁ - cd) / dmg)))
    rw [setV_eq hsupp hdmg, setV_thr hsupp hd']
    have ht : 0 ≤ (s₁ - cd) / dmg := div_nonneg (by linarith [setOffer_ge hsupp hdmg h₁]) hdmg.le
    nlinarith [(setM_facts hsupp _).2 ht]

/-- The uniform prior on `[0, 1]`. -/
noncomputable def unifPrior : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)

theorem unifPrior_isProbabilityMeasure : IsProbabilityMeasure unifPrior :=
  ⟨by simp [unifPrior, Real.volume_Icc]⟩

theorem unifPrior_supp : ∀ᵐ x ∂unifPrior, x ∈ Set.Icc (0 : ℝ) 1 :=
  ae_restrict_mem measurableSet_Icc

/-- D's best response (accepting when indifferent). -/
noncomputable def setAccBR (dmg cd : ℝ) (x s : ℝ) : Bool := decide (s ≤ x * dmg + cd)

theorem setAccBR_BR (dmg cd : ℝ) : SetBR dmg cd (setAccBR dmg cd) := by
  intro x s
  refine ⟨fun h => by simpa [setAccBR] using h, fun h => ?_⟩
  simp only [setAccBR, decide_eq_false_iff_not, not_le] at h
  exact h.le

/-- **Exercise 9.C.4(a), an example** (MWG, p. 304). With the uniform prior and
`c_p + c_d ≥ π`, offering `c_d` (accepted by every type) is a weak PBE: no trials occur. -/
theorem exercise_9_C_4_uniform {dmg cp cd : ℝ} (hdmg : 0 < dmg) (hk : dmg ≤ cp + cd) :
    IsSetWeakPBE unifPrior dmg cp cd cd (setAccBR dmg cd) ∧
      unifPrior.real {x | setAccBR dmg cd x cd = false} = 0 := by
  have hP := unifPrior_isProbabilityMeasure
  have hs := unifPrior_supp
  have hN : NullSingletonClass unifPrior := Measure.restrict.instNullSingletonClass _
  refine ⟨(exercise_9_C_4a hdmg).2 ⟨setAccBR_BR dmg cd, fun s' => ?_⟩, ?_⟩
  · rw [setV_of_le hs hdmg le_rfl, setV_eq hs hdmg]
    set t := (s' - cd) / dmg
    rcases le_total t 0 with ht | ht
    · rw [(setM_facts hs t).1 ht, setG_zero hs ht]
      nlinarith
    · -- `E[min(λ, t)] ≤ min(t, 1) ≤ Prob(λ < t)`
      set m := min t 1 with hm
      have hM : setM unifPrior t ≤ m := by
        have := integral_mono_ae (integrable_min hs t) (integrable_const m) (by
          filter_upwards [hs] with x hx
          exact le_min (min_le_right _ _) (le_trans (min_le_left _ _) hx.2))
        rwa [integral_const, probReal_univ, one_smul] at this
      have hG : m ≤ unifPrior.real (Set.Iio t) := by
        have h1 : unifPrior (Set.Ico 0 m) = ENNReal.ofReal m := by
          rw [unifPrior, Measure.restrict_apply measurableSet_Ico,
            Set.inter_eq_left.2 (Set.Ico_subset_Icc_self.trans
              (Set.Icc_subset_Icc le_rfl (min_le_right _ _))), Real.volume_Ico, sub_zero]
        have h2 : Set.Ico 0 m ⊆ Set.Iio t := fun x hx => lt_of_lt_of_le hx.2 (min_le_left _ _)
        calc m = unifPrior.real (Set.Ico 0 m) := by
              rw [measureReal_def, h1, ENNReal.toReal_ofReal (le_min ht zero_le_one)]
          _ ≤ unifPrior.real (Set.Iio t) := measureReal_mono h2
      have hG0 : 0 ≤ unifPrior.real (Set.Iio t) := measureReal_nonneg
      nlinarith
  · rw [measureReal_def, ENNReal.toReal_eq_zero_iff]
    left
    have hsub : {x | setAccBR dmg cd x cd = false} ⊆ {x | x ∉ Set.Icc (0 : ℝ) 1} := by
      intro x hx hm
      have hx' : x * dmg + cd < cd := by
        have := (setAccBR_BR dmg cd x cd).2 hx
        rcases this.lt_or_eq with h | h
        · exact h
        · have h2 : setAccBR dmg cd x cd = true := by simp [setAccBR, h]
          have hx2 : setAccBR dmg cd x cd = false := hx
          rw [h2] at hx2
          exact absurd hx2 (by decide)
      nlinarith [hm.1]
    exact measure_mono_null hsub (ae_iff.1 hs)

/-- The identity is integrable for a probability measure concentrated on `[0, 1]`. -/
theorem integrable_id_of_supp [IsProbabilityMeasure μ]
    (hsupp : ∀ᵐ x ∂μ, x ∈ Set.Icc (0 : ℝ) 1) : Integrable (fun x : ℝ => x) μ := by
  refine Integrable.of_bound continuous_id.aestronglyMeasurable 1 ?_
  filter_upwards [hsupp] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg hx.1]
  exact hx.2

/-- `E[λ π − c_p] = E[λ] π − c_p`. -/
theorem integral_trial [IsProbabilityMeasure μ] (hsupp : ∀ᵐ x ∂μ, x ∈ Set.Icc (0 : ℝ) 1)
    (dmg cp : ℝ) : ∫ x, (x * dmg - cp) ∂μ = (∫ x, x ∂μ) * dmg - cp := by
  rw [integral_sub ((integrable_id_of_supp hsupp).mul_const dmg) (integrable_const cp),
    integral_mul_const, integral_const, probReal_univ, one_smul]

/-- The mean of `λ` over a lower set `L` is at most its mean over all types:
`∫_L λ ≤ Prob(L) E[λ]` (the types that reject an offer are the low ones). -/
theorem setIntegral_lower_le [IsProbabilityMeasure μ] (hsupp : ∀ᵐ x ∂μ, x ∈ Set.Icc (0 : ℝ) 1)
    {L : Set ℝ} (hL : MeasurableSet L) (hlow : ∀ x y, y ∈ L → x ≤ y → x ∈ L) :
    ∫ x in L, x ∂μ ≤ μ.real L * ∫ x, x ∂μ := by
  set m := ∫ x, x ∂μ with hm
  have hI := integrable_id_of_supp hsupp
  have hsub : ∫ x in L, (x - m) ∂μ = ∫ x in L, x ∂μ - μ.real L * m := by
    rw [integral_sub hI.integrableOn (integrable_const m).integrableOn, setIntegral_const,
      smul_eq_mul]
  suffices h : ∫ x in L, (x - m) ∂μ ≤ 0 by linarith
  by_cases hcase : ∀ y ∈ L, y ≤ m
  · exact setIntegral_nonpos hL fun x hx => by linarith [hcase x hx]
  · push Not at hcase
    obtain ⟨y, hyL, hym⟩ := hcase
    have hzero : ∫ x, (x - m) ∂μ = 0 := by
      rw [integral_sub hI (integrable_const m), integral_const, probReal_univ, one_smul, sub_self]
    have hsplit := integral_add_compl hL (hI.sub (integrable_const m))
    have hcomp : 0 ≤ ∫ x in Lᶜ, (x - m) ∂μ := by
      refine setIntegral_nonneg hL.compl fun x hx => ?_
      have : y < x := by
        by_contra hn
        exact hx (hlow x y hyL (not_lt.1 hn))
      linarith
    simp only [Pi.sub_apply] at hsplit
    linarith

/-- **Exercise 9.C.4(c)** (MWG, p. 304). A profile of the game in which, after a rejection of the
offer `s'`, P decides whether to go to court (`court s'`) holding the belief `ν s'` about `λ`. -/
structure SetCProfile where
  /-- P's offer. -/
  s : ℝ
  /-- Whether type `x` accepts the offer `s'`. -/
  acc : ℝ → ℝ → Bool
  /-- Whether P goes to court after the offer `s'` is rejected. -/
  court : ℝ → Bool
  /-- P's belief about `λ` after the offer `s'` is rejected. -/
  ν : ℝ → Measure ℝ

/-- P's expected payoff from the offer `s'` followed by court (`g' = true`) or dropping the case
after a rejection, against D's strategy `acc`. -/
noncomputable def setCPay (μ : Measure ℝ) (dmg cp : ℝ) (acc : ℝ → ℝ → Bool) (s' : ℝ)
    (g' : Bool) : ℝ :=
  ∫ x, (if acc x s' then s' else if g' then x * dmg - cp else 0) ∂μ

/-- **Exercise 9.C.4(c)** (MWG, p. 304). A pure-strategy weak PBE of the game with the option to
drop the case: D best responds to P's court decision at every offer; P's beliefs are
probability measures on `[0, 1]`; P's court decision is optimal for her belief after every
rejected offer; the belief after the equilibrium offer is Bayes' (the prior conditioned on the
rejecting types) when rejection has positive probability; P's offer and court decision are
optimal against D's strategy. -/
def IsSetCWeakPBE (μ : Measure ℝ) (dmg cp cd : ℝ) (P : SetCProfile) : Prop :=
  (∀ x s', (P.acc x s' = true → (if P.court s' then s' ≤ x * dmg + cd else s' ≤ 0)) ∧
    (P.acc x s' = false → (if P.court s' then x * dmg + cd ≤ s' else 0 ≤ s'))) ∧
  (∀ s', IsProbabilityMeasure (P.ν s') ∧ ∀ᵐ x ∂(P.ν s'), x ∈ Set.Icc (0 : ℝ) 1) ∧
  (∀ s', (P.court s' = true → 0 ≤ ∫ x, (x * dmg - cp) ∂(P.ν s')) ∧
    (P.court s' = false → ∫ x, (x * dmg - cp) ∂(P.ν s') ≤ 0)) ∧
  (0 < μ {x | P.acc x P.s = false} → P.ν P.s = μ[|{x | P.acc x P.s = false}]) ∧
  ∀ s' g', setCPay μ dmg cp P.acc s' g' ≤ setCPay μ dmg cp P.acc P.s (P.court P.s)

/-- **Exercise 9.C.4(c)** (MWG, p. 304). If `E[λ] π < c_p`, no weak PBE has trials: after the
equilibrium offer either P drops the case or rejection has probability zero. The rejecting
types are the low ones, so P's posterior mean after a rejection is at most `E[λ]`, and court is
not credible. -/
theorem exercise_9_C_4c_no_trial [IsProbabilityMeasure μ]
    (hsupp : ∀ᵐ x ∂μ, x ∈ Set.Icc (0 : ℝ) 1) {dmg cp cd : ℝ} (hdmg : 0 < dmg)
    (hmean : (∫ x, x ∂μ) * dmg < cp) {P : SetCProfile} (h : IsSetCWeakPBE μ dmg cp cd P) :
    ¬ (P.court P.s = true ∧ 0 < μ {x | P.acc x P.s = false}) := by
  rintro ⟨hc, hpos⟩
  obtain ⟨hBR, -, hSR, hB, -⟩ := h
  set R := {x | P.acc x P.s = false} with hR
  set t := (P.s - cd) / dmg with ht
  have hs : P.s = cd + dmg * t := by rw [ht]; field_simp; ring
  have h1 : Set.Iio t ⊆ R := by
    intro x hx
    change P.acc x P.s = false
    cases hcx : P.acc x P.s
    · rfl
    · have := (hBR x P.s).1 hcx
      simp only [hc, ↓reduceIte] at this
      rw [hs] at this
      have : t ≤ x := by nlinarith [Set.mem_Iio.1 hx]
      exact absurd hx (not_lt.2 this)
  have h2 : R ⊆ Set.Iic t := by
    intro x hx
    have := (hBR x P.s).2 hx
    simp only [hc, ↓reduceIte] at this
    rw [hs] at this
    change x ≤ t
    nlinarith
  have hRm : MeasurableSet R ∧ ∀ x y, y ∈ R → x ≤ y → x ∈ R := by
    by_cases htR : t ∈ R
    · have : R = Set.Iic t := Set.Subset.antisymm h2 fun x hx => by
        rcases (Set.mem_Iic.1 hx).lt_or_eq with h' | h'
        · exact h1 h'
        · rw [h']; exact htR
      rw [this]
      exact ⟨measurableSet_Iic, fun x y hy hxy => le_trans hxy hy⟩
    · have : R = Set.Iio t := Set.Subset.antisymm (fun x hx => by
          rcases (Set.mem_Iic.1 (h2 hx)).lt_or_eq with h' | h'
          · exact h'
          · rw [h'] at hx; exact absurd hx htR) h1
      rw [this]
      exact ⟨measurableSet_Iio, fun x y hy hxy => lt_of_le_of_lt hxy hy⟩
  have hcourt := (hSR P.s).1 hc
  rw [hB hpos, ProbabilityTheory.cond, integral_smul_measure, smul_eq_mul] at hcourt
  have hRpos : 0 < μ.real R := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos hpos.ne' (measure_ne_top μ R)
  have hinv : 0 < (μ R)⁻¹.toReal := by
    rw [ENNReal.toReal_inv]
    exact inv_pos.2 hRpos
  have hint : 0 ≤ ∫ x in R, (x * dmg - cp) ∂μ := nonneg_of_mul_nonneg_right hcourt hinv
  have hI := integrable_id_of_supp hsupp
  rw [integral_sub (hI.mul_const dmg).integrableOn (integrable_const cp).integrableOn,
    integral_mul_const, setIntegral_const, smul_eq_mul] at hint
  have hlow := setIntegral_lower_le hsupp hRm.1 hRm.2
  nlinarith [mul_le_mul_of_nonneg_right hlow hdmg.le, mul_lt_mul_of_pos_left hmean hRpos]

/-- The no-settlement profile of Exercise 9.C.4(c): P offers `1`, D rejects every positive offer,
P drops the case after every rejection and keeps the prior as belief. -/
noncomputable def setDrop (μ : Measure ℝ) : SetCProfile where
  s := 1
  acc _ s' := decide (s' ≤ 0)
  court _ := false
  ν _ := μ

/-- **Exercise 9.C.4(c)** (MWG, p. 304). The profile in which P's offer is rejected and she
drops the case (payoffs `0`) is a weak PBE iff `E[λ] π ≤ c_p`. -/
theorem exercise_9_C_4c_drop [IsProbabilityMeasure μ]
    (hsupp : ∀ᵐ x ∂μ, x ∈ Set.Icc (0 : ℝ) 1) {dmg cp cd : ℝ} :
    IsSetCWeakPBE μ dmg cp cd (setDrop μ) ↔ (∫ x, x ∂μ) * dmg ≤ cp := by
  have hE := integral_trial hsupp dmg cp
  constructor
  · rintro ⟨-, -, hSR, -, -⟩
    have := (hSR 1).2 rfl
    simp only [setDrop] at this
    linarith
  · intro hm
    have hR : {x | (setDrop μ).acc x (setDrop μ).s = false} = Set.univ := by
      ext x; simp [setDrop]
    refine ⟨fun x s' => ⟨fun h => ?_, fun h => ?_⟩,
      fun _ => ⟨show IsProbabilityMeasure μ from inferInstance, hsupp⟩,
      fun _ => ⟨fun h => absurd h (by simp [setDrop]), fun _ => by simp only [setDrop]; linarith⟩,
      fun _ => by rw [hR, cond_univ]; rfl, fun s' g' => ?_⟩
    · simpa [setDrop] using h
    · simp only [setDrop, decide_eq_false_iff_not, not_le] at h
      simp only [setDrop, Bool.false_eq_true, ↓reduceIte]
      exact h.le
    · have h0 : setCPay μ dmg cp (setDrop μ).acc (setDrop μ).s ((setDrop μ).court
          (setDrop μ).s) = 0 := by
        simp [setCPay, setDrop]
      rw [h0]
      unfold setCPay
      by_cases hs : s' ≤ 0
      · simp only [setDrop, hs, decide_true, ↓reduceIte, integral_const, probReal_univ,
          one_smul]
      · simp only [setDrop, hs, decide_false, Bool.false_eq_true, ↓reduceIte]
        cases g'
        · simp
        · simp only [↓reduceIte]
          linarith

/-- The all-settle profile of Exercise 9.C.4(c) at the offer `s`: P goes to court only after a
rejection of `s` (believing `λ = 1` there) and drops the case after any other rejected offer
(keeping the prior); D accepts `s` iff `s ≤ λπ + c_d`, and any other offer iff it is `≤ 0`. -/
noncomputable def setSettle (μ : Measure ℝ) (dmg cd s : ℝ) : SetCProfile where
  s := s
  acc x s' := if s' = s then decide (s' ≤ x * dmg + cd) else decide (s' ≤ 0)
  court s' := decide (s' = s)
  ν s' := if s' = s then Measure.dirac 1 else μ

/-- **Exercise 9.C.4(c)** (MWG, p. 304). When `E[λ] π ≤ c_p ≤ π`, for every `s ∈ (0, c_d]`
there is a weak PBE in which P offers `s`, every type settles, and P earns `s`: going to court
is credible after a rejection of `s` (an off-path event, where any belief is allowed), and
not after other offers. So the weak PBE of (c) are far from unique. -/
theorem exercise_9_C_4c_settle [IsProbabilityMeasure μ]
    (hsupp : ∀ᵐ x ∂μ, x ∈ Set.Icc (0 : ℝ) 1) {dmg cp cd s : ℝ} (hdmg : 0 < dmg)
    (hcp : cp ≤ dmg) (hmean : (∫ x, x ∂μ) * dmg ≤ cp) (hs0 : 0 < s) (hs1 : s ≤ cd) :
    IsSetCWeakPBE μ dmg cp cd (setSettle μ dmg cd s) ∧
      μ {x | (setSettle μ dmg cd s).acc x s = false} = 0 ∧
      setCPay μ dmg cp (setSettle μ dmg cd s).acc s true = s := by
  have hE := integral_trial hsupp dmg cp
  have hacc : ∀ᵐ x ∂μ, (setSettle μ dmg cd s).acc x s = true := by
    filter_upwards [hsupp] with x hx
    simp only [setSettle, ↓reduceIte, decide_eq_true_eq]
    nlinarith [hx.1]
  have hnull : μ {x | (setSettle μ dmg cd s).acc x s = false} = 0 := by
    rw [← ae_iff.1 hacc]
    congr 1
    ext x
    simp
  have hpay : ∀ g', setCPay μ dmg cp (setSettle μ dmg cd s).acc s g' = s := by
    intro g'
    unfold setCPay
    rw [integral_congr_ae (g := fun _ => s) (by
      filter_upwards [hacc] with x hx
      simp [hx]), integral_const, probReal_univ, one_smul]
  refine ⟨⟨fun x s' => ⟨fun h => ?_, fun h => ?_⟩, fun s' => ?_, fun s' => ⟨fun h => ?_,
    fun h => ?_⟩, fun h => absurd h (by
    rw [show (setSettle μ dmg cd s).s = s from rfl, hnull]; exact lt_irrefl 0), fun s' g' => ?_⟩,
    hnull, hpay true⟩
  · by_cases hs : s' = s
    · simp only [setSettle, hs, ↓reduceIte, decide_true, decide_eq_true_eq] at h ⊢
      exact h
    · simp only [setSettle, hs, ↓reduceIte, decide_false, Bool.false_eq_true,
        decide_eq_true_eq] at h ⊢
      exact h
  · by_cases hs : s' = s
    · simp only [setSettle, hs, ↓reduceIte, decide_true, decide_eq_false_iff_not,
        not_le] at h ⊢
      exact h.le
    · simp only [setSettle, hs, ↓reduceIte, decide_false, Bool.false_eq_true,
        decide_eq_false_iff_not, not_le] at h ⊢
      exact h.le
  · by_cases hs : s' = s
    · simp only [setSettle, hs, ↓reduceIte]
      refine ⟨inferInstance, ?_⟩
      exact (ae_dirac_iff (p := fun x => x ∈ Set.Icc (0 : ℝ) 1) measurableSet_Icc).2
        ⟨zero_le_one, le_rfl⟩
    · simp only [setSettle, hs, ↓reduceIte]
      exact ⟨inferInstance, hsupp⟩
  · have hs : s' = s := by simpa [setSettle] using h
    simp only [setSettle, hs, ↓reduceIte]
    rw [integral_dirac]
    linarith
  · have hs : s' ≠ s := by simpa [setSettle] using h
    simp only [setSettle, hs, ↓reduceIte]
    linarith
  · rw [show (setSettle μ dmg cd s).s = s from rfl, hpay]
    by_cases hs : s' = s
    · rw [hs, hpay]
    · unfold setCPay
      by_cases h0 : s' ≤ 0
      · simp only [setSettle, hs, h0, ↓reduceIte, decide_true, integral_const, probReal_univ,
          one_smul]
        linarith
      · simp only [setSettle, hs, h0, ↓reduceIte, decide_false, Bool.false_eq_true]
        cases g'
        · simp only [Bool.false_eq_true, ↓reduceIte, integral_zero]
          exact hs0.le
        · simp only [↓reduceIte]
          linarith

end MWG.DynamicGames
