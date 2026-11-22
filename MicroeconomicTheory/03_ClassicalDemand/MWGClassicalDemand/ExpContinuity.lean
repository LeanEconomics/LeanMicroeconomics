/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGClassicalDemand.ExpBasic

/-!
# Continuity of the expenditure function

MWG, Proposition 3.E.2(iv), p. 59 (proof omitted in the book). The expenditure function
`e(p, ū)` of a continuous utility representing a locally nonsatiated `≿` on `ℝ^L_+` is jointly
continuous on `{(p, ū) : p ≫ 0, ū attainable}`.

The proof runs through the indirect utility function (Proposition 3.D.3(iv), proved in part A
with Berge's theorem): for `c ≥ 0`, `c < e(p, ū) ⟺ v(p, c) < ū`, and for `c > 0`,
`e(p, ū) < c ⟺ ū < v(p, c)` (`lt_expenditure_iff`, `expenditure_lt_iff`).
-/

namespace MWG.ClassicalDemand

open MWG.ConsumerChoice Kreps.PreferenceProperties Filter Topology

variable {L : ℕ}

/-- The domain `{(p, ū) : p ≫ 0, ū ≤ u(x) for some x ∈ ℝ^L_+}` of the expenditure function. -/
def expDomain (u : (Fin L → ℝ) → ℝ) : Set ((Fin L → ℝ) × ℝ) :=
  {z | StrictlyPositive z.1 ∧ ∃ x ∈ nonnegOrthant L, z.2 ≤ u x}

/-- For `c ≥ 0`: `c < e(p, ū) ⟺ v(p, c) < ū`. -/
theorem lt_expenditure_iff {u : (Fin L → ℝ) → ℝ} (hu : ContinuousOn u (nonnegOrthant L))
    {p : Fin L → ℝ} (hp : StrictlyPositive p) {ub c : ℝ} (hc : 0 ≤ c)
    (hne : ∃ x ∈ nonnegOrthant L, ub ≤ u x) :
    c < expenditure u p ub ↔ indirectUtility u p c < ub := by
  obtain ⟨y, hy⟩ := exercise_3_E_3 hu hp hne
  rw [expenditure_eq_of_mem hy]
  constructor
  · intro hlt
    by_contra hge
    rw [not_lt] at hge
    obtain ⟨x, hx⟩ := proposition_3_D_1 hu hp hc
    rw [indirectUtility_eq_of_mem hx] at hge
    have := hy.2 x ⟨hx.1.1, hge⟩
    linarith [hx.1.2]
  · intro hlt
    by_contra hge
    rw [not_lt] at hge
    have := le_indirectUtility hu hp (⟨hy.1.1, hge⟩ : y ∈ budgetSet p c)
    linarith [hy.1.2]

/-- For `c > 0` and locally nonsatiated `≿`: `e(p, ū) < c ⟺ ū < v(p, c)`. -/
theorem expenditure_lt_iff {u : (Fin L → ℝ) → ℝ} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hrep : RepresentsOn (nonnegOrthant L) u r) (hu : ContinuousOn u (nonnegOrthant L))
    (hlns : LocallyNonsatiated (nonnegOrthant L) r) {p : Fin L → ℝ} (hp : StrictlyPositive p)
    {ub c : ℝ} (hc : 0 < c) (hne : ∃ x ∈ nonnegOrthant L, ub ≤ u x) :
    expenditure u p ub < c ↔ ub < indirectUtility u p c := by
  obtain ⟨y, hy⟩ := exercise_3_E_3 hu hp hne
  rw [expenditure_eq_of_mem hy]
  constructor
  · intro hlt
    obtain ⟨z, hz, hpz, hs⟩ := exists_better_affordable hlns p hy.1.1 hlt
    have h1 := (hrep.strict_iff hz hy.1.1).mp hs
    have h2 := le_indirectUtility hu hp (⟨hz, hpz.le⟩ : z ∈ budgetSet p c)
    linarith [hy.1.2]
  · intro hlt
    obtain ⟨x, hx⟩ := proposition_3_D_1 hu hp hc.le
    rw [indirectUtility_eq_of_mem hx] at hlt
    obtain ⟨α, hα0, hα1, hα⟩ := exp_exists_scale_down hu hx.1.1 hlt
    have h1 := hy.2 (α • x) ⟨fun l => mul_nonneg hα0.le (hx.1.1 l), hα.le⟩
    rw [dotProduct_smul, smul_eq_mul] at h1
    have h2 := hx.1.2
    nlinarith

/-- `v(p, 0) = u(0)` for `p ≫ 0`: the only affordable bundle is `0`. -/
theorem exp_indirectUtility_zero_wealth (u : (Fin L → ℝ) → ℝ) {p : Fin L → ℝ}
    (hp : StrictlyPositive p) : indirectUtility u p 0 = u 0 := by
  have hb : ∀ x ∈ budgetSet p 0, x = 0 := by
    intro x hx
    by_contra hne
    have := exp_dotProduct_pos hp hx.1 hne
    linarith [hx.2]
  have hmem : (0 : Fin L → ℝ) ∈ walrasianDemand u p 0 :=
    ⟨zero_mem_budgetSet p le_rfl, fun y hy => by rw [hb y hy]⟩
  exact indirectUtility_eq_of_mem hmem

/-- `q ↦ v(q, c)` is continuous at `p ≫ 0` for every `c ≥ 0`. -/
theorem exp_continuousAt_indirectUtility_prices {u : (Fin L → ℝ) → ℝ}
    (hu : ContinuousOn u (nonnegOrthant L)) {p : Fin L → ℝ} (hp : StrictlyPositive p) {c : ℝ}
    (hc : 0 ≤ c) : ContinuousAt (fun q => indirectUtility u q c) p := by
  rcases hc.lt_or_eq with hc' | hc'
  · have hopen : IsOpen (pwDomainSet L) := by
      have : pwDomainSet L = {q : (Fin L → ℝ) × ℝ | StrictlyPositive q.1} ∩ {q | 0 < q.2} := by
        ext q; rfl
      rw [this]
      refine IsOpen.inter ?_ (isOpen_lt continuous_const continuous_snd)
      have : {q : (Fin L → ℝ) × ℝ | StrictlyPositive q.1} =
          ⋂ l, {q : (Fin L → ℝ) × ℝ | 0 < q.1 l} := by
        ext q; simp [StrictlyPositive]
      rw [this]
      exact isOpen_iInter_of_finite fun l =>
        isOpen_lt continuous_const ((continuous_apply l).comp continuous_fst)
    have hca : ContinuousAt (fun q : (Fin L → ℝ) × ℝ => indirectUtility u q.1 q.2) (p, c) :=
      (proposition_3_D_3_iv hu).continuousAt (hopen.mem_nhds ⟨hp, hc'⟩)
    exact hca.comp (f := fun q => (q, c)) (continuous_id.prodMk continuous_const).continuousAt
  · subst hc'
    have hopen : IsOpen {q : Fin L → ℝ | StrictlyPositive q} := by
      have : {q : Fin L → ℝ | StrictlyPositive q} = ⋂ l, {q : Fin L → ℝ | 0 < q l} := by
        ext q; simp [StrictlyPositive]
      rw [this]
      exact isOpen_iInter_of_finite fun l => isOpen_lt continuous_const (continuous_apply l)
    apply (continuousAt_const (y := u 0)).congr
    filter_upwards [hopen.mem_nhds hp] with q hq
    exact (exp_indirectUtility_zero_wealth u hq).symm

/-- **Proposition 3.E.2(iv)** (MWG, p. 59). For `u` continuous on `ℝ^L_+` representing a
locally nonsatiated `≿`, the expenditure function is jointly continuous in `(p, ū)` on
`{(p, ū) : p ≫ 0, ū attainable}`. (The book omits the proof.) -/
theorem proposition_3_E_2_iv {u : (Fin L → ℝ) → ℝ} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hrep : RepresentsOn (nonnegOrthant L) u r) (hu : ContinuousOn u (nonnegOrthant L))
    (hlns : LocallyNonsatiated (nonnegOrthant L) r) :
    ContinuousOn (fun z : (Fin L → ℝ) × ℝ => expenditure u z.1 z.2) (expDomain u) := by
  rintro ⟨p, ub⟩ ⟨hp, hne⟩
  have hfst : Tendsto (fun z : (Fin L → ℝ) × ℝ => z.1) (𝓝[expDomain u] (p, ub)) (𝓝 p) :=
    continuous_fst.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hsnd : Tendsto (fun z : (Fin L → ℝ) × ℝ => z.2) (𝓝[expDomain u] (p, ub)) (𝓝 ub) :=
    continuous_snd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · simp only at ha
    rcases lt_or_ge a 0 with ha0 | ha0
    · filter_upwards [self_mem_nhdsWithin] with z hz
      exact ha0.trans_le (expenditure_nonneg u hz.1 z.2)
    have hv : indirectUtility u p a < ub := (lt_expenditure_iff hu hp ha0 hne).mp ha
    have hvt : Tendsto (fun z : (Fin L → ℝ) × ℝ => indirectUtility u z.1 a)
        (𝓝[expDomain u] (p, ub)) (𝓝 (indirectUtility u p a)) :=
      (exp_continuousAt_indirectUtility_prices hu hp ha0).tendsto.comp hfst
    filter_upwards [self_mem_nhdsWithin, hvt.eventually_lt hsnd hv] with z hz hlt
    exact (lt_expenditure_iff hu hz.1 ha0 hz.2).mpr hlt
  · simp only at hb
    have hb0 : 0 < b := (expenditure_nonneg u hp ub).trans_lt hb
    have hv : ub < indirectUtility u p b := (expenditure_lt_iff hrep hu hlns hp hb0 hne).mp hb
    have hvt : Tendsto (fun z : (Fin L → ℝ) × ℝ => indirectUtility u z.1 b)
        (𝓝[expDomain u] (p, ub)) (𝓝 (indirectUtility u p b)) :=
      (exp_continuousAt_indirectUtility_prices hu hp hb0.le).tendsto.comp hfst
    filter_upwards [self_mem_nhdsWithin, hsnd.eventually_lt hvt hv] with z hz hlt
    exact (expenditure_lt_iff hrep hu hlns hz.1 hb0 hz.2).mpr hlt

end MWG.ClassicalDemand
