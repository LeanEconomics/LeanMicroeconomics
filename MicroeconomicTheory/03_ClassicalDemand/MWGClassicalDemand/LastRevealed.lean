/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGClassicalDemand.EconRevealed

/-!
# Exercise 3.D.7(d): both goods normal, sufficiency

MWG, Exercise 3.D.7(d), p. 98. Two goods; `p⁰ = (1, 1)`, `w⁰ = 8`, `x⁰ = (4, 4)`; `p¹ = (1, 4)`,
`w¹ = 26`, `x¹ = (26 - 4t, t)`, `t = x¹₂ ≥ 0`.

The necessity half (`t ≤ 11/2`) is `exercise_3_D_7d`, but its hypothesis asks the demand
selection to be optimal at *every* `(p, w)`, including `p = 0`, where a locally nonsatiated
preference has no optimum: that hypothesis is never satisfied
(`last_exercise_3_D_7d_hyp_unsatisfiable`, correction G-1). Here the exercise is stated with the
demand function defined on `p ≫ 0`, `w ≥ 0` (the book's domain of `x(p, w)`), and both
directions are proved (`exercise_3_D_7d_iff`):

* necessity again (`last_exercise_3_D_7d_necessary`), now from optimality at `(p⁰, 8)`,
  `(p¹, 20)` and `(p¹, 26)` only;
* sufficiency: for every `t ≤ 11/2` the continuous, concave, monotone utility
  `u(x) = x₂ + φ(x₁)`, `φ(τ) = min(τ, 3 + τ/4, 3 + x¹₁/4)`, on `ℝ²_+` (not on the quasilinear
  set) has the demand function
  `x₁(p, w) = min(w/p₁, c(p))`, `x₂(p, w) = max(w - p₁c(p), 0)/p₂`, where `c(p)` is `0`, `4` or
  `x¹₁` according as `p₁/p₂ > 1`, `1/4 < p₁/p₂ ≤ 1` or `p₁/p₂ ≤ 1/4` (`lastNormalDemand`). Both
  coordinates are nondecreasing in `w`, so both goods are normal at every `p ≫ 0`, and the
  demand passes through `x⁰` and `x¹`.
-/

namespace MWG.ClassicalDemand

open MWG.ConsumerChoice Kreps.PreferenceProperties

/-- The kinked concave function `φ(τ) = min(τ, 3 + τ/4, 3 + T/4)` (`T = x¹₁`). -/
noncomputable def lastPhi (T τ : ℝ) : ℝ := min τ (min (3 + τ / 4) (3 + T / 4))

/-- The utility `u(x) = x₂ + φ(x₁)` on `ℝ²_+`. -/
noncomputable def lastNormalUtility (T : ℝ) (x : Fin 2 → ℝ) : ℝ := x 1 + lastPhi T (x 0)

/-- The selected optimal level `c(p)` of good 1 when wealth does not bind:
`0` if `p₁ > p₂`, `4` if `p₂/4 < p₁ ≤ p₂`, `T` if `p₁ ≤ p₂/4`. -/
noncomputable def lastNormalLevel (T : ℝ) (p : Fin 2 → ℝ) : ℝ :=
  if p 1 < p 0 then 0 else if p 1 < 4 * p 0 then 4 else T

/-- The demand function `x₁ = min(w/p₁, c(p))`, `x₂ = (w - p₁x₁)/p₂`. -/
noncomputable def lastNormalDemand (T : ℝ) (p : Fin 2 → ℝ) (w : ℝ) : Fin 2 → ℝ :=
  ![min (w / p 0) (lastNormalLevel T p), (w - p 0 * min (w / p 0) (lastNormalLevel T p)) / p 1]

/-- `φ` has slope at least `1/4` below `T`: `τ ↦ φ(τ) - τ/4` is nondecreasing on `(-∞, T]`. -/
theorem lastPhi_quarter {T a b : ℝ} (hab : a ≤ b) (hb : b ≤ T) :
    lastPhi T a - a / 4 ≤ lastPhi T b - b / 4 := by
  unfold lastPhi
  have h1 : min (3 + b / 4) (3 + T / 4) = 3 + b / 4 := min_eq_left (by linarith)
  have h2 : min (3 + a / 4) (3 + T / 4) = 3 + a / 4 := min_eq_left (by linarith)
  rw [h1, h2]
  rcases le_total a 4 with ha | ha <;> rcases le_total b 4 with hb4 | hb4
  · rw [min_eq_left (by linarith), min_eq_left (by linarith)]; linarith
  · rw [min_eq_left (by linarith), min_eq_right (by linarith)]; linarith
  · have : a = b := by linarith
    rw [this]
  · rw [min_eq_right (by linarith), min_eq_right (by linarith)]; linarith

/-- The key inequality: `c = c(p)`-type optimality of `x₁` for the one-dimensional problem
`max φ(y₁) - r y₁` over `0 ≤ y₁ ≤ m`, with `x₁ = min(m, c)`. -/
theorem lastPhi_opt {T : ℝ} (hT : 4 ≤ T) {p : Fin 2 → ℝ} (hp : StrictlyPositive p) {m y : ℝ}
    (hm : 0 ≤ m) (hy0 : 0 ≤ y) (hym : y ≤ m) :
    p 1 * lastPhi T y - p 0 * y ≤
      p 1 * lastPhi T (min m (lastNormalLevel T p)) - p 0 * min m (lastNormalLevel T p) := by
  have hp0 := hp 0
  have hp1 := hp 1
  unfold lastNormalLevel
  split_ifs with h1 h2
  · -- `c = 0`: `x₁ = 0`
    rw [min_eq_right hm]
    have hφ : lastPhi T y ≤ y := min_le_left _ _
    have hφ0 : lastPhi T 0 = 0 := by
      unfold lastPhi; rw [min_eq_left (le_min (by norm_num) (by linarith))]
    rw [hφ0]
    nlinarith
  · -- `c = 4`
    rw [not_lt] at h1
    have hφa : lastPhi T y ≤ y := min_le_left _ _
    have hφb : lastPhi T y ≤ 3 + y / 4 := (min_le_right _ _).trans (min_le_left _ _)
    rcases le_total m 4 with hm4 | hm4
    · rw [min_eq_left hm4]
      have hφm : lastPhi T m = m := by
        unfold lastPhi; rw [min_eq_left (le_min (by linarith) (by linarith))]
      rw [hφm]
      nlinarith
    · rw [min_eq_right hm4]
      have hφ4 : lastPhi T 4 = 4 := by
        unfold lastPhi; rw [min_eq_left (le_min (by linarith) (by linarith))]
      rw [hφ4]
      rcases le_total y 4 with hy4 | hy4
      · nlinarith
      · nlinarith
  · -- `c = T`
    rw [not_lt] at h1 h2
    rcases le_total m T with hmT | hmT
    · rw [min_eq_left hmT]
      have hq := lastPhi_quarter hym hmT
      nlinarith
    · rw [min_eq_right hmT]
      rcases le_total y T with hyT | hyT
      · have hq := lastPhi_quarter hyT le_rfl
        nlinarith
      · have hφy : lastPhi T y ≤ 3 + T / 4 := (min_le_right _ _).trans (min_le_right _ _)
        have hφT : lastPhi T T = 3 + T / 4 := by
          unfold lastPhi
          rw [min_self, min_eq_right (by linarith)]
        rw [hφT]
        nlinarith

/-- `c(p) ≥ 0`. -/
theorem lastNormalLevel_nonneg {T : ℝ} (hT : 4 ≤ T) (p : Fin 2 → ℝ) :
    0 ≤ lastNormalLevel T p := by
  unfold lastNormalLevel
  split_ifs <;> linarith

/-- The demand function is a solution of the UMP for `u(x) = x₂ + φ(x₁)` at every `p ≫ 0`,
`w ≥ 0`. -/
theorem lastNormalDemand_mem {T : ℝ} (hT : 4 ≤ T) {p : Fin 2 → ℝ} (hp : StrictlyPositive p)
    {w : ℝ} (hw : 0 ≤ w) : lastNormalDemand T p w ∈ walrasianDemand (lastNormalUtility T) p w := by
  have hp0 := hp 0
  have hp1 := hp 1
  set c := lastNormalLevel T p with hc
  have hc0 : 0 ≤ c := lastNormalLevel_nonneg hT p
  set m := w / p 0 with hm
  have hm0 : 0 ≤ m := div_nonneg hw hp0.le
  have hmw : p 0 * m = w := by rw [hm]; field_simp
  have hx0 : 0 ≤ min m c := le_min hm0 hc0
  have hx0m : min m c ≤ m := min_le_left _ _
  have hspend : p 0 * min m c ≤ w := by rw [← hmw]; exact mul_le_mul_of_nonneg_left hx0m hp0.le
  have hdot : ∀ y : Fin 2 → ℝ, p ⬝ᵥ y = p 0 * y 0 + p 1 * y 1 := fun y => by
    simp [dotProduct, Fin.sum_univ_two]
  have hD0 : lastNormalDemand T p w 0 = min m c := rfl
  have hD1 : lastNormalDemand T p w 1 = (w - p 0 * min m c) / p 1 := rfl
  refine ⟨⟨fun l => ?_, ?_⟩, fun y hy => ?_⟩
  · fin_cases l
    · exact hx0
    · exact div_nonneg (by linarith) hp1.le
  · rw [hdot, hD0, hD1]
    field_simp
    linarith
  · have hy2 := hy.2
    rw [hdot] at hy2
    have hy0 := hy.1 0
    have hy1 := hy.1 1
    have hym : y 0 ≤ m := by
      rw [hm, le_div_iff₀ hp0]; nlinarith
    have hopt := lastPhi_opt hT hp hm0 hy0 hym
    rw [← hc] at hopt
    unfold lastNormalUtility
    rw [hD0, hD1]
    have key : p 1 * (y 1 + lastPhi T (y 0)) ≤
        p 1 * ((w - p 0 * min m c) / p 1 + lastPhi T (min m c)) := by
      rw [mul_add, mul_add, mul_div_cancel₀ _ hp1.ne']
      linarith
    exact le_of_mul_le_mul_left key hp1

/-- Both goods are normal: each coordinate of the demand function is nondecreasing in wealth. -/
theorem lastNormalDemand_mono (T : ℝ) {p : Fin 2 → ℝ} (hp : StrictlyPositive p) {w w' : ℝ}
    (hww : w ≤ w') : lastNormalDemand T p w ≤ lastNormalDemand T p w' := by
  have hp0 := hp 0
  have hp1 := hp 1
  set c := lastNormalLevel T p
  have hmul : ∀ v : ℝ, p 0 * min (v / p 0) c = min v (p 0 * c) := fun v => by
    rw [mul_min_of_nonneg _ _ hp0.le, mul_div_cancel₀ _ hp0.ne']
  intro l
  fin_cases l
  · change min (w / p 0) c ≤ min (w' / p 0) c
    exact min_le_min_right _ (div_le_div_of_nonneg_right hww hp0.le)
  · change (w - p 0 * min (w / p 0) c) / p 1 ≤ (w' - p 0 * min (w' / p 0) c) / p 1
    rw [hmul, hmul]
    refine div_le_div_of_nonneg_right ?_ hp1.le
    rcases le_total w (p 0 * c) with h | h <;> rcases le_total w' (p 0 * c) with h' | h'
    · rw [min_eq_left h, min_eq_left h']; linarith
    · rw [min_eq_left h, min_eq_right h']; linarith
    · have : w = w' := by linarith
      rw [this]
    · rw [min_eq_right h, min_eq_right h']; linarith

/-- The utility `x₂ + φ(x₁)` is continuous. -/
theorem lastNormalUtility_continuous (T : ℝ) : Continuous (lastNormalUtility T) := by
  unfold lastNormalUtility lastPhi
  fun_prop

/-- The utility `x₂ + φ(x₁)` is concave on `ℝ²_+` (a minimum of three affine functions). -/
theorem lastNormalUtility_concaveOn (T : ℝ) :
    ConcaveOn ℝ (nonnegOrthant 2) (lastNormalUtility T) := by
  have hq : ∀ (a b c : ℝ), ConcaveOn ℝ (nonnegOrthant 2) fun x : Fin 2 → ℝ =>
      a * x 0 + b * x 1 + c := by
    intro a b c
    refine (econ_affine_concaveOn ![a, b] c).congr fun x _ => ?_
    simp [dotProduct, Fin.sum_univ_two]
  have h := ((hq 1 1 0).inf (hq (1 / 4) 1 3)).inf (hq 0 1 (3 + T / 4))
  refine h.congr fun x _ => ?_
  simp only [lastNormalUtility, lastPhi, Pi.inf_apply]
  rw [← min_add_add_left, ← min_add_add_left]
  rw [min_assoc, show 1 * x 0 + 1 * x 1 + 0 = x 1 + x 0 by ring,
    show 1 / 4 * x 0 + 1 * x 1 + 3 = x 1 + (3 + x 0 / 4) by ring,
    show 0 * x 0 + 1 * x 1 + (3 + T / 4) = x 1 + (3 + T / 4) by ring]

/-- The utility `x₂ + φ(x₁)` is monotone on `ℝ²_+`. -/
theorem lastNormalUtility_monotone (T : ℝ) :
    PrefMonotone (nonnegOrthant 2) (utilityPref (lastNormalUtility T)) := by
  intro x _ y _ hxy
  have h0 : x 0 < y 0 := hxy 0
  have h1 : x 1 < y 1 := hxy 1
  have hφ : lastPhi T (x 0) ≤ lastPhi T (y 0) := by
    unfold lastPhi
    exact min_le_min h0.le (min_le_min (by linarith) le_rfl)
  have hlt : lastNormalUtility T x < lastNormalUtility T y := by
    unfold lastNormalUtility; linarith
  exact ⟨hlt.le, not_le.mpr hlt⟩

/-- A monotone preference on `ℝ²_+` is locally nonsatiated. -/
theorem last_lns_of_monotone {u : (Fin 2 → ℝ) → ℝ}
    (hmono : PrefMonotone (nonnegOrthant 2) (utilityPref u)) :
    LocallyNonsatiated (nonnegOrthant 2) (utilityPref u) := by
  intro x hx ε hε
  refine ⟨x + fun _ => ε / 2, fun l => by simp only [Pi.add_apply]; linarith [hx l], ?_,
    hmono x hx _ (fun l => by simp only [Pi.add_apply]; linarith [hx l])
      fun l => by simp only [Pi.add_apply]; linarith⟩
  rw [euclidDist_add_const, abs_of_pos (by linarith)]
  have h2 : Real.sqrt (2 : ℕ) ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have := mul_le_mul_of_nonneg_right h2 (by linarith : (0 : ℝ) ≤ ε / 2)
  linarith

/-- The hypothesis of `exercise_3_D_7d` (a demand selection optimal at every `(p, w)`,
`p = 0` included) is never satisfied by a locally nonsatiated preference on `ℝ²_+`: at
`p = 0`, `w = 0` the whole of `ℝ²_+` is affordable and has no best element (correction G-1). -/
theorem last_exercise_3_D_7d_hyp_unsatisfiable {u : (Fin 2 → ℝ) → ℝ}
    {r : (Fin 2 → ℝ) → (Fin 2 → ℝ) → Prop} (hrep : RepresentsOn (nonnegOrthant 2) u r)
    (hlns : LocallyNonsatiated (nonnegOrthant 2) r) (xs : (Fin 2 → ℝ) → ℝ → Fin 2 → ℝ) :
    ¬ ∀ p w, xs p w ∈ walrasianDemand u p w := by
  intro hxs
  have hx := hxs 0 0
  obtain ⟨y, hy, -, hs⟩ := hlns _ hx.1.1 1 one_pos
  have hlt := (hrep.strict_iff hy hx.1.1).mp hs
  have := hx.2 y ⟨hy, by simp⟩
  linarith

/-- **Exercise 3.D.7(d)** (MWG, p. 98), necessity, with the demand function defined on
`p ≫ 0`, `w ≥ 0`. If `u` represents a locally nonsatiated `≿` on `ℝ²_+` and `xs` is a demand
function for it with good 1 normal at `p¹`, `xs p⁰ 8 = x⁰` and `xs p¹ 26 = x¹`, then
`x¹₂ ≤ 11/2`. -/
theorem last_exercise_3_D_7d_necessary {u : (Fin 2 → ℝ) → ℝ}
    {r : (Fin 2 → ℝ) → (Fin 2 → ℝ) → Prop}
    (hrep : RepresentsOn (nonnegOrthant 2) u r) (hlns : LocallyNonsatiated (nonnegOrthant 2) r)
    {xs : (Fin 2 → ℝ) → ℝ → Fin 2 → ℝ}
    (hxs : ∀ p w, StrictlyPositive p → 0 ≤ w → xs p w ∈ walrasianDemand u p w)
    (hnormal : xs econP1 20 0 ≤ xs econP1 26 0)
    (h0 : xs econP0 8 = econX0) : xs econP1 26 1 ≤ 11 / 2 := by
  have hP0 : StrictlyPositive econP0 := fun l => by fin_cases l <;> norm_num [econP0]
  have hP1 : StrictlyPositive econP1 := fun l => by fin_cases l <;> norm_num [econP1]
  set x' := xs econP1 20
  have hx' := hxs econP1 20 hP1 (by norm_num)
  have hwal' := proposition_3_D_2_ii hrep hlns hx'
  rw [econP1_dot] at hwal'
  have hwal1 := proposition_3_D_2_ii hrep hlns (hxs econP1 26 hP1 (by norm_num))
  rw [econP1_dot] at hwal1
  have h0d := hxs econP0 8 hP0 (by norm_num)
  rw [h0] at h0d
  have hcost : 8 ≤ x' 0 + x' 1 := by
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨z, hz, hpz, hs⟩ := exists_better_affordable hlns econP0 hx'.1.1
      (by rw [econP0_dot]; exact hlt)
    have hzlt := (hrep.strict_iff hz hx'.1.1).mp hs
    have := h0d.2 z ⟨hz, hpz.le⟩
    have hle := hx'.2 econX0 ⟨econX0_mem, by rw [econP1_dot]; norm_num [econX0]⟩
    linarith
  linarith

/-- **Exercise 3.D.7(d)** (MWG, p. 98). For `x¹ ∈ ℝ²_+` on the budget line `p¹·x = 26`: there
are a continuous, concave, monotone utility `u` on `ℝ²_+` and a demand function `xs` for it
(`xs p w ∈ x(p, w)` for all `p ≫ 0`, `w ≥ 0`) with both goods normal at every `p ≫ 0` and
`xs p⁰ 8 = x⁰`, `xs p¹ 26 = x¹`, iff `x¹₂ ≤ 11/2`. Necessity holds for every locally
nonsatiated preference with good 1 normal at `p¹` (`last_exercise_3_D_7d_necessary`). -/
theorem exercise_3_D_7d_iff {x1 : Fin 2 → ℝ} (hx1 : x1 ∈ nonnegOrthant 2)
    (hb : x1 0 + 4 * x1 1 = 26) :
    (∃ (u : (Fin 2 → ℝ) → ℝ) (xs : (Fin 2 → ℝ) → ℝ → Fin 2 → ℝ), Continuous u ∧
      ConcaveOn ℝ (nonnegOrthant 2) u ∧ PrefMonotone (nonnegOrthant 2) (utilityPref u) ∧
      (∀ p w, StrictlyPositive p → 0 ≤ w → xs p w ∈ walrasianDemand u p w) ∧
      (∀ p, StrictlyPositive p → ∀ w w', w ≤ w' → xs p w ≤ xs p w') ∧
      xs econP0 8 = econX0 ∧ xs econP1 26 = x1) ↔ x1 1 ≤ 11 / 2 := by
  constructor
  · rintro ⟨u, xs, -, -, hmono, hxs, hnorm, h0, h1⟩
    have hP1 : StrictlyPositive econP1 := fun l => by fin_cases l <;> norm_num [econP1]
    have := last_exercise_3_D_7d_necessary (fun _ _ _ _ => Iff.rfl) (last_lns_of_monotone hmono)
      hxs (hnorm econP1 hP1 20 26 (by norm_num) 0) h0
    rwa [h1] at this
  · intro ht
    set T := x1 0 with hTdef
    have hT : 4 ≤ T := by linarith
    have hT26 : T ≤ 26 := by linarith [hx1 1]
    refine ⟨lastNormalUtility T, lastNormalDemand T, lastNormalUtility_continuous T,
      lastNormalUtility_concaveOn T, lastNormalUtility_monotone T,
      fun p w hp hw => lastNormalDemand_mem hT hp hw,
      fun p hp w w' hww => lastNormalDemand_mono T hp hww, ?_, ?_⟩
    · have hc : lastNormalLevel T econP0 = 4 := by
        unfold lastNormalLevel; norm_num [econP0]
      ext l
      fin_cases l
      · change min (8 / econP0 0) (lastNormalLevel T econP0) = econX0 0
        rw [hc]; norm_num [econP0, econX0]
      · change (8 - econP0 0 * min (8 / econP0 0) (lastNormalLevel T econP0)) / econP0 1 = econX0 1
        rw [hc]; norm_num [econP0, econX0]
    · have hc : lastNormalLevel T econP1 = T := by
        unfold lastNormalLevel; norm_num [econP1]
      ext l
      fin_cases l
      · change min (26 / econP1 0) (lastNormalLevel T econP1) = x1 0
        rw [hc]; norm_num [econP1]; exact min_eq_right hT26
      · change (26 - econP1 0 * min (26 / econP1 0) (lastNormalLevel T econP1)) / econP1 1 = x1 1
        rw [hc]; norm_num [econP1]
        rw [min_eq_right hT26]
        linarith

end MWG.ClassicalDemand
