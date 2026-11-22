/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGDynamicGames.Settlement

/-!
# Pretrial settlement with an informed plaintiff

MWG, Exercise 9.C.5 (p. 304): Exercise 9.C.4 when it is Ms. P who knows `λ` (and makes the
offer), and the sequential-equilibrium reading of Exercise 9.C.6 for Exercises 9.C.4(c) and
9.C.5.

Model (`IsSet5WeakPBE`): P's offer is a function `σ` of her type `λ ∈ [0, 1]`; D accepts or
rejects each offer (`acc s`) holding a belief `ν s` (a probability measure on `[0, 1]`) about
`λ`; D accepts only if paying `s` is no worse than the expected trial payment `E_ν[λ] π + c_d`,
rejects only if it is no better; each type of P chooses an optimal offer; and D's belief after
an offer made with positive prior probability is Bayes' (the prior conditioned on the types
making it).

* `exercise_9_C_5`: in every weak PBE all settling types settle at the same amount, every type
  gets at least `max (c_d, λπ − c_p)`, and the types going to trial are the high ones (if `λ`
  goes to trial, so does every `λ' > λ`): high types do not settle because no offer above what
  the low types would accept is accepted.
* `exercise_9_C_5_semi`: for every prior there is a weak PBE in which the types with
  `λπ − c_p ≤ c_d` settle at `c_d` and the others go to trial.
* `exercise_9_C_5_pooling`: if `π − c_p ≤ E[λ] π + c_d`, every `s` with
  `max (c_d, π − c_p) ≤ s ≤ E[λ] π + c_d` is the offer of a pooling weak PBE in which every type
  settles at `s` (off-path offers above `c_d` are believed to come from `λ = 0`); with the
  prior as belief after every offer (`exercise_9_C_5_passive`) the pooling offer is
  `E[λ] π + c_d`.
* Exercise 9.C.6 for 9.C.4(c): `IsSetCConsistent` (structural consistency: after every offer
  rejected with positive probability, P's belief is the prior conditioned on the rejecting
  types). `exercise_9_C_6_settlement`: the multiple weak PBE of `exercise_9_C_4c_settle` and
  `exercise_9_C_4c_drop` are consistent, so the sequential equilibria are not unique either.
-/

namespace MWG.DynamicGames

open MeasureTheory ProbabilityTheory

/-- P's payoff in Exercise 9.C.5 when her type is `x`, she offers `s`, and D's strategy is
`acc`. -/
noncomputable def set5Pay (dmg cp : ℝ) (acc : ℝ → Bool) (x s : ℝ) : ℝ :=
  if acc s then s else x * dmg - cp

theorem set5Pay_acc {dmg cp : ℝ} {acc : ℝ → Bool} {s : ℝ} (h : acc s = true) (x : ℝ) :
    set5Pay dmg cp acc x s = s := by
  simp [set5Pay, h]

theorem set5Pay_rej {dmg cp : ℝ} {acc : ℝ → Bool} {s : ℝ} (h : acc s = false) (x : ℝ) :
    set5Pay dmg cp acc x s = x * dmg - cp := by
  simp [set5Pay, h]

/-- **Exercise 9.C.5** (MWG, p. 304). A profile: P's offer as a function of her type, D's
acceptance rule, and D's beliefs after each offer. -/
structure Set5Profile where
  /-- The offer of P's type `x`. -/
  σ : ℝ → ℝ
  /-- Whether D accepts the offer `s`. -/
  acc : ℝ → Bool
  /-- D's belief about `λ` after the offer `s`. -/
  ν : ℝ → Measure ℝ

/-- **Exercise 9.C.5** (MWG, p. 304). A pure-strategy weak PBE. -/
def IsSet5WeakPBE (μ : Measure ℝ) (dmg cp cd : ℝ) (P : Set5Profile) : Prop :=
  (∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ s', set5Pay dmg cp P.acc x s' ≤ set5Pay dmg cp P.acc x (P.σ x)) ∧
  (∀ s, IsProbabilityMeasure (P.ν s) ∧ ∀ᵐ x ∂(P.ν s), x ∈ Set.Icc (0 : ℝ) 1) ∧
  (∀ s, (P.acc s = true → s ≤ (∫ x, x ∂(P.ν s)) * dmg + cd) ∧
    (P.acc s = false → (∫ x, x ∂(P.ν s)) * dmg + cd ≤ s)) ∧
  ∀ s, 0 < μ (P.σ ⁻¹' {s}) → P.ν s = μ[|P.σ ⁻¹' {s}]

/-- The mean of a probability measure concentrated on `[0, 1]` lies in `[0, 1]`. -/
theorem mean_mem_Icc {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (h : ∀ᵐ x ∂ν, x ∈ Set.Icc (0 : ℝ) 1) : 0 ≤ ∫ x, x ∂ν ∧ ∫ x, x ∂ν ≤ 1 := by
  refine ⟨integral_nonneg_of_ae (by filter_upwards [h] with x hx; exact hx.1), ?_⟩
  have := integral_mono_ae (integrable_id_of_supp h) (integrable_const (1 : ℝ))
    (by filter_upwards [h] with x hx; exact hx.2)
  rwa [integral_const, probReal_univ, one_smul] at this

/-- In a weak PBE of Exercise 9.C.5, D accepts every offer below `c_d` and rejects every offer
above `π + c_d`, whatever her belief. -/
theorem set5_acc_facts {μ : Measure ℝ} {dmg cp cd : ℝ} (hdmg : 0 < dmg) {P : Set5Profile}
    (h : IsSet5WeakPBE μ dmg cp cd P) :
    (∀ s, s < cd → P.acc s = true) ∧ (∀ s, dmg + cd < s → P.acc s = false) := by
  obtain ⟨-, hν, hD, -⟩ := h
  refine ⟨fun s hs => ?_, fun s hs => ?_⟩
  · have := (hν s).1
    obtain ⟨h0, -⟩ := mean_mem_Icc (hν s).2
    cases hc : P.acc s
    · have := (hD s).2 hc
      nlinarith
    · rfl
  · have := (hν s).1
    obtain ⟨-, h1⟩ := mean_mem_Icc (hν s).2
    cases hc : P.acc s
    · rfl
    · have := (hD s).1 hc
      nlinarith

/-- **Exercise 9.C.5** (MWG, p. 304). In every weak PBE: (i) all settling types make the same
offer; (ii) every type gets at least `c_d` and at least `λπ − c_p`; (iii) the types going to
trial are the high ones: if type `x` goes to trial, so does every type `y > x`. -/
theorem exercise_9_C_5 {μ : Measure ℝ} {dmg cp cd : ℝ} (hdmg : 0 < dmg) {P : Set5Profile}
    (h : IsSet5WeakPBE μ dmg cp cd P) :
    (∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, P.acc (P.σ x) = true →
      P.acc (P.σ y) = true → P.σ x = P.σ y) ∧
    (∀ x ∈ Set.Icc (0 : ℝ) 1, cd ≤ set5Pay dmg cp P.acc x (P.σ x) ∧
      x * dmg - cp ≤ set5Pay dmg cp P.acc x (P.σ x)) ∧
    (∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, x < y → P.acc (P.σ x) = false →
      P.acc (P.σ y) = false) := by
  obtain ⟨hacc, hrej⟩ := set5_acc_facts hdmg h
  have hopt := h.1
  refine ⟨fun x hx y hy hax hay => ?_, fun x hx => ⟨?_, ?_⟩, fun x hx y hy hxy hrx => ?_⟩
  · have h1 := hopt x hx (P.σ y)
    have h2 := hopt y hy (P.σ x)
    simp only [set5Pay, hax, hay, ↓reduceIte] at h1 h2
    linarith
  · by_contra hn
    push Not at hn
    set u := set5Pay dmg cp P.acc x (P.σ x)
    have := hopt x hx ((u + cd) / 2)
    rw [set5Pay_acc (hacc _ (by linarith))] at this
    linarith
  · have := hopt x hx (dmg + cd + 1)
    rwa [set5Pay_rej (hrej _ (by linarith))] at this
  · cases hay : P.acc (P.σ y)
    · rfl
    · have h1 := hopt x hx (P.σ y)
      have h2 := hopt y hy (dmg + cd + 1)
      rw [set5Pay_acc hay, set5Pay_rej hrx] at h1
      rw [set5Pay_rej (hrej _ (by linarith)), set5Pay_acc hay] at h2
      nlinarith [hx.1, hy.1]

/-- The pooling profile of Exercise 9.C.5 at the offer `s`: every type offers `s`; D accepts
`s` and every offer `≤ c_d`; D believes the prior after `s` and `λ = 0` after other offers. -/
noncomputable def set5Pool (μ : Measure ℝ) (cd s : ℝ) : Set5Profile where
  σ _ := s
  acc s' := decide (s' = s ∨ s' ≤ cd)
  ν s' := if s' = s then μ else Measure.dirac 0

/-- **Exercise 9.C.5** (MWG, p. 304). If `max (c_d, π − c_p) ≤ s ≤ E[λ] π + c_d`, every type of P
offering `s` and every type settling is a weak PBE. -/
theorem exercise_9_C_5_pooling {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hsupp : ∀ᵐ x ∂μ, x ∈ Set.Icc (0 : ℝ) 1) {dmg cp cd s : ℝ} (hdmg : 0 < dmg)
    (hs1 : cd ≤ s) (hs2 : dmg - cp ≤ s) (hs3 : s ≤ (∫ x, x ∂μ) * dmg + cd) :
    IsSet5WeakPBE μ dmg cp cd (set5Pool μ cd s) ∧ ∀ x, (set5Pool μ cd s).acc
      ((set5Pool μ cd s).σ x) = true := by
  have hacc : (set5Pool μ cd s).acc s = true := by simp [set5Pool]
  refine ⟨⟨fun x hx s' => ?_, fun s' => ?_, fun s' => ⟨fun h => ?_, fun h => ?_⟩,
    fun s' hpos => ?_⟩, fun _ => hacc⟩
  · change _ ≤ set5Pay dmg cp _ x s
    rw [set5Pay_acc hacc]
    cases hc : (set5Pool μ cd s).acc s'
    · rw [set5Pay_rej hc]
      nlinarith [hx.2]
    · rw [set5Pay_acc hc]
      simp only [set5Pool, decide_eq_true_eq] at hc
      rcases hc with hc | hc <;> linarith
  · by_cases hs : s' = s
    · simp only [set5Pool, hs, ↓reduceIte]
      exact ⟨inferInstance, hsupp⟩
    · simp only [set5Pool, hs, ↓reduceIte]
      exact ⟨inferInstance,
        (ae_dirac_iff (p := fun x => x ∈ Set.Icc (0 : ℝ) 1) measurableSet_Icc).2
          ⟨le_rfl, zero_le_one⟩⟩
  · by_cases hs : s' = s
    · simp only [set5Pool, hs, ↓reduceIte]
      exact hs3
    · simp only [set5Pool, hs, ↓reduceIte, integral_dirac, zero_mul, zero_add]
      simp only [set5Pool, hs, false_or, decide_eq_true_eq] at h
      exact h
  · by_cases hs : s' = s
    · rw [hs, hacc] at h
      exact absurd h (by decide)
    · simp only [set5Pool, hs, ↓reduceIte, integral_dirac, zero_mul, zero_add]
      simp only [set5Pool, hs, false_or, decide_eq_false_iff_not, not_le] at h
      exact h.le
  · by_cases hs : s' = s
    · have : (set5Pool μ cd s).σ ⁻¹' {s'} = Set.univ := by
        ext x; simp [set5Pool, hs]
      rw [this, cond_univ]
      simp [set5Pool, hs]
    · have : (set5Pool μ cd s).σ ⁻¹' {s'} = ∅ := by
        ext x; simp [set5Pool, Ne.symm hs]
      rw [this, measure_empty] at hpos
      exact absurd hpos (lt_irrefl 0)

/-- The pooling profile with passive beliefs: every type offers `E[λ] π + c_d`, and D keeps the
prior as her belief after every offer. -/
noncomputable def set5Passive (μ : Measure ℝ) (dmg cd : ℝ) : Set5Profile where
  σ _ := (∫ x, x ∂μ) * dmg + cd
  acc s' := decide (s' ≤ (∫ x, x ∂μ) * dmg + cd)
  ν _ := μ

/-- **Exercise 9.C.5** (MWG, p. 304). If `π − c_p ≤ E[λ] π + c_d`, every type offering
`E[λ] π + c_d`, D accepting exactly the offers up to `E[λ] π + c_d` and keeping the prior as
her belief after every offer, is a weak PBE in which every type settles. (These beliefs are the
limits of the Bayes beliefs when every type trembles to every offer with the same probability,
so this is a sequential equilibrium in the reading of Exercise 9.C.6.) -/
theorem exercise_9_C_5_passive {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hsupp : ∀ᵐ x ∂μ, x ∈ Set.Icc (0 : ℝ) 1) {dmg cp cd : ℝ} (hdmg : 0 < dmg)
    (hle : dmg - cp ≤ (∫ x, x ∂μ) * dmg + cd) :
    IsSet5WeakPBE μ dmg cp cd (set5Passive μ dmg cd) := by
  set m := (∫ x, x ∂μ) * dmg + cd with hm
  have hacc : (set5Passive μ dmg cd).acc m = true := by simp [set5Passive, hm]
  refine ⟨fun x hx s' => ?_, fun _ => ⟨show IsProbabilityMeasure μ from inferInstance, hsupp⟩,
    fun s' => ⟨fun h => ?_, fun h => ?_⟩, fun s' hpos => ?_⟩
  · change _ ≤ set5Pay dmg cp _ x m
    rw [set5Pay_acc hacc]
    cases hc : (set5Passive μ dmg cd).acc s'
    · rw [set5Pay_rej hc]
      nlinarith [hx.2]
    · rw [set5Pay_acc hc]
      simpa [set5Passive, hm] using hc
  · simpa [set5Passive] using h
  · simp only [set5Passive, decide_eq_false_iff_not, not_le] at h
    exact h.le
  · by_cases hs : s' = m
    · have : (set5Passive μ dmg cd).σ ⁻¹' {s'} = Set.univ := by
        ext x; simp [set5Passive, hs, hm]
      rw [this, cond_univ]
      rfl
    · have : (set5Passive μ dmg cd).σ ⁻¹' {s'} = ∅ := by
        ext x; simp only [set5Passive, Set.mem_preimage, Set.mem_singleton_iff,
          Set.mem_empty_iff_false, iff_false]; exact fun h => hs (by rw [← h])
      rw [this, measure_empty] at hpos
      exact absurd hpos (lt_irrefl 0)

/-- A belief: the prior conditioned on `S` if `S` has positive probability, `λ = 0` otherwise. -/
noncomputable def condOrZero (μ : Measure ℝ) (S : Set ℝ) : Measure ℝ :=
  if 0 < μ S then μ[|S] else Measure.dirac 0

theorem condOrZero_facts {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hsupp : ∀ᵐ x ∂μ, x ∈ Set.Icc (0 : ℝ) 1) (S : Set ℝ) :
    IsProbabilityMeasure (condOrZero μ S) ∧
      ∀ᵐ x ∂(condOrZero μ S), x ∈ Set.Icc (0 : ℝ) 1 := by
  unfold condOrZero
  split_ifs with h
  · exact ⟨cond_isProbabilityMeasure h.ne', cond_absolutelyContinuous.ae_le hsupp⟩
  · exact ⟨inferInstance, (ae_dirac_iff (p := fun x => x ∈ Set.Icc (0 : ℝ) 1)
      measurableSet_Icc).2 ⟨le_rfl, zero_le_one⟩⟩

/-- The semi-pooling profile of Exercise 9.C.5: the types with `λπ − c_p ≤ c_d` offer `c_d`,
the others offer `π + c_d + 1` (rejected, so they go to trial); D accepts exactly the offers up
to `c_d`. -/
noncomputable def set5Semi (μ : Measure ℝ) (dmg cp cd : ℝ) : Set5Profile where
  σ x := if x ≤ (cd + cp) / dmg then cd else dmg + cd + 1
  acc s' := decide (s' ≤ cd)
  ν s' := if s' = cd then condOrZero μ (Set.Iic ((cd + cp) / dmg))
    else if s' = dmg + cd + 1 then condOrZero μ (Set.Ioi ((cd + cp) / dmg))
    else Measure.dirac 0

/-- **Exercise 9.C.5** (MWG, p. 304). For every prior, the types with `λπ − c_p ≤ c_d` settling
at `c_d` and the others going to trial is a weak PBE; in particular a weak PBE always exists.
-/
theorem exercise_9_C_5_semi {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hsupp : ∀ᵐ x ∂μ, x ∈ Set.Icc (0 : ℝ) 1) {dmg cp cd : ℝ} (hdmg : 0 < dmg) :
    IsSet5WeakPBE μ dmg cp cd (set5Semi μ dmg cp cd) ∧
      ∀ x, ((set5Semi μ dmg cp cd).acc ((set5Semi μ dmg cp cd).σ x) = true ↔
        x * dmg - cp ≤ cd) := by
  set τ := (cd + cp) / dmg with hτ
  have hne : cd ≠ dmg + cd + 1 := by intro h; linarith
  have hτ' : ∀ x, x ≤ τ ↔ x * dmg - cp ≤ cd := fun x => by
    rw [hτ, le_div_iff₀ hdmg]; constructor <;> intro <;> linarith
  have hσacc : ∀ x, ((set5Semi μ dmg cp cd).acc ((set5Semi μ dmg cp cd).σ x) = true ↔
      x * dmg - cp ≤ cd) := by
    intro x
    by_cases hx : x ≤ τ
    · simp only [set5Semi, ← hτ, hx, ↓reduceIte, le_refl, decide_true, true_iff]
      exact (hτ' x).1 hx
    · simp only [set5Semi, ← hτ, hx, ↓reduceIte, decide_eq_true_eq]
      constructor
      · intro h; linarith
      · intro h; exact absurd ((hτ' x).2 h) hx
  have hbel : ∀ s', IsProbabilityMeasure ((set5Semi μ dmg cp cd).ν s') ∧
      ∀ᵐ x ∂((set5Semi μ dmg cp cd).ν s'), x ∈ Set.Icc (0 : ℝ) 1 := by
    intro s'
    simp only [set5Semi, ← hτ]
    split_ifs
    · exact condOrZero_facts hsupp _
    · exact condOrZero_facts hsupp _
    · exact ⟨inferInstance, (ae_dirac_iff (p := fun x => x ∈ Set.Icc (0 : ℝ) 1)
        measurableSet_Icc).2 ⟨le_rfl, zero_le_one⟩⟩
  refine ⟨⟨fun x hx s' => ?_, hbel, fun s' => ⟨fun h => ?_, fun h => ?_⟩,
    fun s' hpos => ?_⟩, hσacc⟩
  · by_cases hx' : x * dmg - cp ≤ cd
    · rw [set5Pay_acc ((hσacc x).2 hx')]
      have hc : (set5Semi μ dmg cp cd).σ x = cd := by
        simp [set5Semi, ← hτ, (hτ' x).2 hx']
      rw [hc]
      cases hs : (set5Semi μ dmg cp cd).acc s'
      · rw [set5Pay_rej hs]; exact hx'
      · rw [set5Pay_acc hs]; simpa [set5Semi] using hs
    · have hr : (set5Semi μ dmg cp cd).acc ((set5Semi μ dmg cp cd).σ x) = false := by
        cases hc : (set5Semi μ dmg cp cd).acc ((set5Semi μ dmg cp cd).σ x)
        · rfl
        · exact absurd ((hσacc x).1 hc) hx'
      rw [set5Pay_rej hr]
      cases hs : (set5Semi μ dmg cp cd).acc s'
      · rw [set5Pay_rej hs]
      · rw [set5Pay_acc hs]
        have : s' ≤ cd := by simpa [set5Semi] using hs
        linarith
  · have hs : s' ≤ cd := by simpa [set5Semi] using h
    have := (hbel s').1
    obtain ⟨h0, -⟩ := mean_mem_Icc (hbel s').2
    nlinarith
  · have hs : cd < s' := by simpa [set5Semi] using h
    by_cases h1 : s' = dmg + cd + 1
    · have := (hbel s').1
      obtain ⟨-, h1'⟩ := mean_mem_Icc (hbel s').2
      nlinarith
    · have hcd : s' ≠ cd := fun h' => by rw [h'] at hs; exact lt_irrefl _ hs
      simp only [set5Semi, hcd, h1, ↓reduceIte, integral_dirac, zero_mul, zero_add]
      exact hs.le
  · by_cases h1 : s' = cd
    · have hpre : (set5Semi μ dmg cp cd).σ ⁻¹' {s'} = Set.Iic τ := by
        ext x
        simp only [set5Semi, ← hτ, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_Iic, h1]
        split_ifs with hx
        · simp [hx]
        · simp only [hx, iff_false]; exact fun h => hne h.symm
      rw [hpre] at hpos ⊢
      simp only [set5Semi, ← hτ, h1, ↓reduceIte, condOrZero, hpos]
    · by_cases h2 : s' = dmg + cd + 1
      · have hpre : (set5Semi μ dmg cp cd).σ ⁻¹' {s'} = Set.Ioi τ := by
          ext x
          simp only [set5Semi, ← hτ, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_Ioi, h2]
          split_ifs with hx
          · simp only [hne, false_iff, not_lt]; exact hx
          · simp only [true_iff]; exact not_le.1 hx
        rw [hpre] at hpos ⊢
        simp only [set5Semi, ← hτ, h2, ↓reduceIte, condOrZero, hpos, Ne.symm hne]
      · have hpre : (set5Semi μ dmg cp cd).σ ⁻¹' {s'} = ∅ := by
          ext x
          simp only [set5Semi, Set.mem_preimage, Set.mem_singleton_iff,
            Set.mem_empty_iff_false, iff_false]
          split_ifs
          · exact fun h => h1 h.symm
          · exact fun h => h2 h.symm
        rw [hpre, measure_empty] at hpos
        exact absurd hpos (lt_irrefl 0)

/-- **Exercise 9.C.6** (MWG, p. 304), structural consistency for Exercise 9.C.4(c): after every
offer that is rejected with positive probability (on or off the equilibrium path), P's belief
is the prior conditioned on the rejecting types (P's own trembles do not depend on `λ`). -/
def IsSetCConsistent (μ : Measure ℝ) (P : SetCProfile) : Prop :=
  ∀ s', 0 < μ {x | P.acc x s' = false} → P.ν s' = μ[|{x | P.acc x s' = false}]

/-- **Exercise 9.C.6 for Exercise 9.C.4(c)** (MWG, p. 304). The weak PBE of
`exercise_9_C_4c_settle` (every type settles at any `s ∈ (0, c_d]`) and of
`exercise_9_C_4c_drop` (no settlement, P drops the case) have consistent beliefs, so they are
sequential equilibria in the reading of Exercise 9.C.6, which therefore does not remove the
multiplicity. -/
theorem exercise_9_C_6_settlement {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hsupp : ∀ᵐ x ∂μ, x ∈ Set.Icc (0 : ℝ) 1) {dmg cd s : ℝ} (hdmg : 0 < dmg)
    (hs1 : s ≤ cd) :
    IsSetCConsistent μ (setSettle μ dmg cd s) ∧ IsSetCConsistent μ (setDrop μ) := by
  constructor
  · intro s' hpos
    by_cases hs : s' = s
    · exfalso
      subst hs
      have hnull : μ {x | (setSettle μ dmg cd s').acc x s' = false} = 0 := by
        have hsub : {x | (setSettle μ dmg cd s').acc x s' = false} ⊆
            {x | x ∉ Set.Icc (0 : ℝ) 1} := by
          intro x hx hm
          have hx' : s' > x * dmg + cd := by
            have hx2 : (setSettle μ dmg cd s').acc x s' = false := hx
            simpa [setSettle] using hx2
          nlinarith [hm.1]
        exact measure_mono_null hsub (ae_iff.1 hsupp)
      rw [hnull] at hpos
      exact lt_irrefl 0 hpos
    · by_cases h0 : s' ≤ 0
      · have : {x | (setSettle μ dmg cd s).acc x s' = false} = ∅ := by
          ext x; simp [setSettle, hs, h0]
        rw [this, measure_empty] at hpos
        exact absurd hpos (lt_irrefl 0)
      · have : {x | (setSettle μ dmg cd s).acc x s' = false} = Set.univ := by
          ext x; simp [setSettle, hs, h0]
        rw [this, cond_univ]
        simp [setSettle, hs]
  · intro s' hpos
    by_cases h0 : s' ≤ 0
    · have : {x | (setDrop μ).acc x s' = false} = ∅ := by
        ext x; simp [setDrop, h0]
      rw [this, measure_empty] at hpos
      exact absurd hpos (lt_irrefl 0)
    · have : {x | (setDrop μ).acc x s' = false} = Set.univ := by
        ext x; simp [setDrop, h0]
      rw [this, cond_univ]
      rfl

/-- **Exercises 9.C.4(c) and 9.C.5, examples** (MWG, p. 304), with the uniform prior and
`π = c_d = 1`: for `c_p = 2` the no-settlement profile is a weak PBE and trials never occur in
any weak PBE (`E[λ] π ≤ 1 < 2`); for `c_p = 1` every type settling at `1/2` is a weak PBE; and in
the informed-plaintiff game the semi-pooling profile is a weak PBE. -/
theorem exercise_9_C_4c_5_examples :
    IsSetCWeakPBE unifPrior 1 2 1 (setDrop unifPrior) ∧
    (∀ P, IsSetCWeakPBE unifPrior 1 2 1 P →
      ¬ (P.court P.s = true ∧ 0 < unifPrior {x | P.acc x P.s = false})) ∧
    IsSetCWeakPBE unifPrior 1 1 1 (setSettle unifPrior 1 1 (1 / 2)) ∧
    IsSet5WeakPBE unifPrior 1 1 1 (set5Semi unifPrior 1 1 1) := by
  have hP := unifPrior_isProbabilityMeasure
  have hs := unifPrior_supp
  have hE := (mean_mem_Icc hs).2
  refine ⟨(exercise_9_C_4c_drop hs).2 (by linarith), fun P h =>
    exercise_9_C_4c_no_trial hs one_pos (by linarith) h,
    (exercise_9_C_4c_settle hs one_pos le_rfl (by linarith) (by norm_num) (by norm_num)).1,
    (exercise_9_C_5_semi hs one_pos).1⟩

end MWG.DynamicGames
