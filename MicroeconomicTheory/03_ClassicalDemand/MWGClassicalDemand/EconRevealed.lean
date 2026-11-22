/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGClassicalDemand.UMPBasic

/-!
# Exercise 3.D.7: regions of choices consistent with preference maximization

MWG, Exercise 3.D.7, p. 98. Two goods; `p⁰ = (1, 1)`, `w⁰ = 8`, `x⁰ = (4, 4)`; `p¹ = (1, 4)`,
`w¹ = 26`, and `x¹` with `p¹·x¹ = 26`. Write `t = x¹₂`, so `x¹ = (26 - 4t, t)`.

* **(a)** Consistent with maximization of a locally nonsatiated preference iff `t < 6`
  (`exercise_3_D_7a`). Necessity: `x⁰` is strictly affordable at `(p¹, w¹)` (cost 20), so
  `x¹ ≻ x⁰`; then `x¹` must cost more than 8 at `p⁰`. Sufficiency: the continuous, concave,
  strictly increasing `u(x) = min(p⁰·x - 8, c(p¹·x - 26) + s - 8)`, `s = x¹₁ + x¹₂`,
  `c = (s - 8)/6` (Afriat's construction).
* **(b)** Quasilinear in the first good (`u = x₁ + φ(x₂)` on `ℝ × ℝ_+`): iff `t ≤ 4`
  (`exercise_3_D_7b`); rationalized by `φ(τ) = min(4τ, 3t + τ, 3t + 4)`.
* **(c)** Quasilinear in the second good (`u = x₂ + φ(x₁)` on `ℝ_+ × ℝ`): iff `x¹₁ ≥ 4`, i.e.
  `t ≤ 11/2` (`exercise_3_D_7c`); rationalized by `φ(τ) = min(τ, 3 + τ/4, 3 + x¹₁/4)`.
* **(d)** Both goods normal: necessarily `t ≤ 11/2` (`exercise_3_D_7d`): `x' = x(p¹, 20)` is
  revealed preferred to `x⁰` and must cost at least 8 at `p⁰`, and `x' ≤ x¹`.
* **(e)** Homothetic (a representation homogeneous of degree one): iff `t ≤ 26/5`
  (`exercise_3_D_7e`); rationalized by `u(x) = min(p⁰·x, (2/5) p¹·x)`.

Departures (corrections F2-2, F2-3): the necessity parts need local nonsatiation (a constant
utility rationalizes every choice); "quasilinear" is taken in the form `x_k + φ(x_{-k})` on the
quasilinear consumption set of Definition 3.B.7; in (d) only the necessity bound is proved, the
construction of a demand function with normal goods through every `t ≤ 11/2` is OPEN.
-/

namespace MWG.ClassicalDemand

open MWG.ConsumerChoice Kreps.PreferenceProperties

/-- `p⁰ = (1, 1)`. -/
def econP0 : Fin 2 → ℝ := ![1, 1]

/-- `p¹ = (1, 4)`. -/
def econP1 : Fin 2 → ℝ := ![1, 4]

/-- `x⁰ = (4, 4)`. -/
def econX0 : Fin 2 → ℝ := ![4, 4]

/-- `p⁰·x = x₁ + x₂`. -/
theorem econP0_dot (x : Fin 2 → ℝ) : econP0 ⬝ᵥ x = x 0 + x 1 := by
  simp [econP0, dotProduct, Fin.sum_univ_two]

/-- `p¹·x = x₁ + 4x₂`. -/
theorem econP1_dot (x : Fin 2 → ℝ) : econP1 ⬝ᵥ x = x 0 + 4 * x 1 := by
  simp [econP1, dotProduct, Fin.sum_univ_two]

/-- `x⁰ ∈ ℝ²_+`. -/
theorem econX0_mem : econX0 ∈ nonnegOrthant 2 := by
  intro l
  fin_cases l <;> norm_num [econX0]

/-- Affine functions are concave on `ℝ²_+`. -/
theorem econ_affine_concaveOn (q : Fin 2 → ℝ) (c : ℝ) :
    ConcaveOn ℝ (nonnegOrthant 2) fun x => q ⬝ᵥ x + c := by
  refine ⟨convex_nonnegOrthant 2, fun x _ y _ a b _ _ hab => ?_⟩
  simp only [smul_eq_mul, dotProduct_add, dotProduct_smul]
  have : a * c + b * c = c := by rw [← add_mul, hab, one_mul]
  linarith

/-- **Exercise 3.D.7(a)** (MWG, p. 98), necessity. If `u` represents a locally nonsatiated `≿`
on `ℝ²_+`, `x⁰ ∈ x(p⁰, 8)` and `x¹ ∈ x(p¹, 26)`, then `x¹₂ < 6`. -/
theorem exercise_3_D_7a_necessary {u : (Fin 2 → ℝ) → ℝ} {r : (Fin 2 → ℝ) → (Fin 2 → ℝ) → Prop}
    (hrep : RepresentsOn (nonnegOrthant 2) u r) (hlns : LocallyNonsatiated (nonnegOrthant 2) r)
    {x1 : Fin 2 → ℝ} (h0 : econX0 ∈ walrasianDemand u econP0 8)
    (h1 : x1 ∈ walrasianDemand u econP1 26) : x1 1 < 6 := by
  by_contra hge
  rw [not_lt] at hge
  have hb1 := proposition_3_D_2_ii hrep hlns h1
  rw [econP1_dot] at hb1
  have hx1p0 : x1 ∈ budgetSet econP0 8 := ⟨h1.1.1, by rw [econP0_dot]; linarith⟩
  have hle := h0.2 x1 hx1p0
  have hcost : econP1 ⬝ᵥ econX0 < 26 := by rw [econP1_dot]; norm_num [econX0]
  obtain ⟨z, hz, hpz, hs⟩ := exists_better_affordable hlns econP1 econX0_mem hcost
  have hlt := (hrep.strict_iff hz econX0_mem).mp hs
  have := h1.2 z ⟨hz, hpz.le⟩
  linarith

/-- **Exercise 3.D.7(a)** (MWG, p. 98). For `x¹ ∈ ℝ²_+` on the budget line `p¹·x = 26`: `x⁰` and
`x¹` are the choices of some continuous, concave, monotone (`PrefMonotone`, hence locally
nonsatiated) utility iff `x¹₂ < 6`. -/
theorem exercise_3_D_7a {x1 : Fin 2 → ℝ} (hx1 : x1 ∈ nonnegOrthant 2)
    (hb : x1 0 + 4 * x1 1 = 26) :
    (∃ u : (Fin 2 → ℝ) → ℝ, Continuous u ∧ ConcaveOn ℝ (nonnegOrthant 2) u ∧
      PrefMonotone (nonnegOrthant 2) (utilityPref u) ∧
      econX0 ∈ walrasianDemand u econP0 8 ∧ x1 ∈ walrasianDemand u econP1 26) ↔ x1 1 < 6 := by
  constructor
  · rintro ⟨u, -, -, hmono, h0, h1⟩
    have hlns : LocallyNonsatiated (nonnegOrthant 2) (utilityPref u) := by
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
    exact exercise_3_D_7a_necessary (fun _ _ _ _ => Iff.rfl) hlns h0 h1
  · intro ht
    set s := x1 0 + x1 1 with hs
    have hs8 : 8 < s := by linarith
    set c := (s - 8) / 6 with hc
    have hc0 : 0 < c := by rw [hc]; linarith
    refine ⟨fun x => min (econP0 ⬝ᵥ x - 8) (c * (econP1 ⬝ᵥ x - 26) + (s - 8)), ?_, ?_, ?_, ?_, ?_⟩
    · simp only [econP0_dot, econP1_dot]
      fun_prop
    · refine ConcaveOn.inf ?_ ?_
      · simpa [sub_eq_add_neg] using econ_affine_concaveOn econP0 (-8)
      · have := econ_affine_concaveOn (c • econP1) (-(c * 26) + (s - 8))
        refine this.congr fun x _ => ?_
        simp only [smul_dotProduct, smul_eq_mul]
        ring
    · intro x _ y _ hxy
      have h0 : x 0 < y 0 := hxy 0
      have h1 : x 1 < y 1 := hxy 1
      have hlt : min (econP0 ⬝ᵥ x - 8) (c * (econP1 ⬝ᵥ x - 26) + (s - 8)) <
          min (econP0 ⬝ᵥ y - 8) (c * (econP1 ⬝ᵥ y - 26) + (s - 8)) := by
        simp only [econP0_dot, econP1_dot]
        refine min_lt_min (by linarith) ?_
        nlinarith
      exact ⟨hlt.le, not_le.mpr hlt⟩
    · refine ⟨⟨econX0_mem, by rw [econP0_dot]; norm_num [econX0]⟩, fun y hy => ?_⟩
      have hy2 := hy.2
      rw [econP0_dot] at hy2
      have hx0 : min (econP0 ⬝ᵥ econX0 - 8) (c * (econP1 ⬝ᵥ econX0 - 26) + (s - 8)) = 0 := by
        simp only [econP0_dot, econP1_dot, econX0]
        norm_num
        rw [hc]
        ring_nf
        simp
      beta_reduce
      rw [hx0, econP0_dot]
      exact (min_le_left _ _).trans (by linarith)
    · refine ⟨⟨hx1, by rw [econP1_dot]; linarith⟩, fun y hy => ?_⟩
      have hy2 := hy.2
      rw [econP1_dot] at hy2
      have hx1v : min (econP0 ⬝ᵥ x1 - 8) (c * (econP1 ⬝ᵥ x1 - 26) + (s - 8)) = s - 8 := by
        rw [econP0_dot, econP1_dot, hb, ← hs]
        simp
      beta_reduce
      rw [hx1v, econP1_dot]
      refine (min_le_right _ _).trans ?_
      nlinarith

/-- The quasilinear utility `x_k + φ(x_j)` in two goods. -/
def econQL (k j : Fin 2) (φ : ℝ → ℝ) (x : Fin 2 → ℝ) : ℝ := x k + φ (x j)

/-- **Exercise 3.D.7(b)** (MWG, p. 98). With preferences quasilinear in the first good
(`u = x₁ + φ(x₂)` on the quasilinear set `ℝ × ℝ_+`), `x⁰` and `x¹ = (26 - 4t, t)`, `t ≥ 0`,
are both chosen for some `φ` iff `t ≤ 4`. -/
theorem exercise_3_D_7b {x1 : Fin 2 → ℝ} (hx1 : x1 ∈ quasilinearDomain (0 : Fin 2))
    (hb : x1 0 + 4 * x1 1 = 26) :
    (∃ φ : ℝ → ℝ, econX0 ∈ walrasianDemandOn (quasilinearDomain 0) (econQL 0 1 φ) econP0 8 ∧
      x1 ∈ walrasianDemandOn (quasilinearDomain 0) (econQL 0 1 φ) econP1 26) ↔ x1 1 ≤ 4 := by
  have hmem : ∀ a b : ℝ, 0 ≤ b → (![a, b] : Fin 2 → ℝ) ∈ quasilinearDomain (0 : Fin 2) := by
    intro a b hb' l hl
    fin_cases l
    · exact absurd rfl hl
    · simpa using hb'
  have ht0 : 0 ≤ x1 1 := hx1 1 (by decide)
  constructor
  · rintro ⟨φ, h0, h1⟩
    set t := x1 1
    have e0 := h0.2 ![8 - t, t] ⟨hmem _ _ ht0, by rw [econP0_dot]; simp⟩
    have e1 := h1.2 ![10, 4] ⟨hmem _ _ (by norm_num), by rw [econP1_dot]; norm_num⟩
    simp only [econQL, econX0] at e0 e1
    norm_num at e0 e1
    linarith
  · intro ht
    set t := x1 1
    refine ⟨fun τ => min (4 * τ) (min (3 * t + τ) (3 * t + 4)), ⟨⟨hmem _ _ (by norm_num),
      by rw [econP0_dot]; norm_num [econX0]⟩, fun y hy => ?_⟩,
      ⟨⟨hx1, by rw [econP1_dot]; linarith⟩, fun y hy => ?_⟩⟩
    · have hy2 := hy.2
      rw [econP0_dot] at hy2
      simp only [econQL, econX0]
      norm_num
      have h1 : min (4 * y 1) (min (3 * t + y 1) (3 * t + 4)) ≤ 3 * t + y 1 :=
        (min_le_right _ _).trans (min_le_left _ _)
      have h2 : min (16 : ℝ) (3 * t + 4) = 3 * t + 4 := min_eq_right (by linarith)
      rw [h2]
      linarith
    · have hy2 := hy.2
      rw [econP1_dot] at hy2
      simp only [econQL]
      have h1 : min (4 * y 1) (min (3 * t + y 1) (3 * t + 4)) ≤ 4 * y 1 := min_le_left _ _
      have h2 : min (4 * t) (min (3 * t + t) (3 * t + 4)) = 4 * t := by
        rw [min_eq_left]
        exact le_min (by linarith) (by linarith)
      rw [h2]
      linarith

/-- **Exercise 3.D.7(c)** (MWG, p. 98). With preferences quasilinear in the second good
(`u = x₂ + φ(x₁)` on the quasilinear set `ℝ_+ × ℝ`), `x⁰` and `x¹` (with `x¹₁ ≥ 0`,
`x¹₁ + 4x¹₂ = 26`) are both chosen for some `φ` iff `x¹₁ ≥ 4`, i.e. `x¹₂ ≤ 11/2`. -/
theorem exercise_3_D_7c {x1 : Fin 2 → ℝ} (hx1 : x1 ∈ quasilinearDomain (1 : Fin 2))
    (hb : x1 0 + 4 * x1 1 = 26) :
    (∃ φ : ℝ → ℝ, econX0 ∈ walrasianDemandOn (quasilinearDomain 1) (econQL 1 0 φ) econP0 8 ∧
      x1 ∈ walrasianDemandOn (quasilinearDomain 1) (econQL 1 0 φ) econP1 26) ↔
      4 ≤ x1 0 := by
  have hmem : ∀ a b : ℝ, 0 ≤ a → (![a, b] : Fin 2 → ℝ) ∈ quasilinearDomain (1 : Fin 2) := by
    intro a b ha l hl
    fin_cases l
    · simpa using ha
    · exact absurd rfl hl
  have hT0 : 0 ≤ x1 0 := hx1 0 (by decide)
  constructor
  · rintro ⟨φ, h0, h1⟩
    set T := x1 0
    have e0 := h0.2 ![T, 8 - T] ⟨hmem _ _ hT0, by rw [econP0_dot]; simp⟩
    have e1 := h1.2 ![4, 11 / 2] ⟨hmem _ _ (by norm_num), by rw [econP1_dot]; norm_num⟩
    simp only [econQL, econX0] at e0 e1
    norm_num at e0 e1
    linarith
  · intro hT
    set T := x1 0
    refine ⟨fun τ => min τ (min (3 + τ / 4) (3 + T / 4)), ⟨⟨hmem _ _ (by norm_num),
      by rw [econP0_dot]; norm_num [econX0]⟩, fun y hy => ?_⟩,
      ⟨⟨hx1, by rw [econP1_dot]; linarith⟩, fun y hy => ?_⟩⟩
    · have hy2 := hy.2
      rw [econP0_dot] at hy2
      simp only [econQL, econX0]
      norm_num
      have h1 : min (y 0) (min (3 + y 0 / 4) (3 + T / 4)) ≤ y 0 := min_le_left _ _
      have h2 : min (4 : ℝ) (3 + T / 4) = 4 := min_eq_left (by linarith)
      rw [h2]
      linarith
    · have hy2 := hy.2
      rw [econP1_dot] at hy2
      simp only [econQL]
      have h1 : min (y 0) (min (3 + y 0 / 4) (3 + T / 4)) ≤ 3 + y 0 / 4 :=
        (min_le_right _ _).trans (min_le_left _ _)
      have h2 : min T (min (3 + T / 4) (3 + T / 4)) = 3 + T / 4 := by
        rw [min_self, min_eq_right (by linarith)]
      rw [h2]
      linarith

/-- **Exercise 3.D.7(d)** (MWG, p. 98), necessity. Let `u` represent a locally nonsatiated `≿`
on `ℝ²_+` and `xs` be a demand function for it (`xs p w ∈ x(p, w)`) with both goods normal at
`p¹` (`xs p¹ w` nondecreasing in `w`). If `xs p⁰ 8 = x⁰` and `xs p¹ 26 = x¹`, then
`x¹₂ ≤ 11/2`. -/
theorem exercise_3_D_7d {u : (Fin 2 → ℝ) → ℝ} {r : (Fin 2 → ℝ) → (Fin 2 → ℝ) → Prop}
    (hrep : RepresentsOn (nonnegOrthant 2) u r) (hlns : LocallyNonsatiated (nonnegOrthant 2) r)
    {xs : (Fin 2 → ℝ) → ℝ → Fin 2 → ℝ} (hxs : ∀ p w, xs p w ∈ walrasianDemand u p w)
    (hnormal : ∀ w w' : ℝ, w ≤ w' → xs econP1 w ≤ xs econP1 w')
    (h0 : xs econP0 8 = econX0) : xs econP1 26 1 ≤ 11 / 2 := by
  set x' := xs econP1 20
  have hx' := hxs econP1 20
  have hwal' := proposition_3_D_2_ii hrep hlns hx'
  rw [econP1_dot] at hwal'
  have hwal1 := proposition_3_D_2_ii hrep hlns (hxs econP1 26)
  rw [econP1_dot] at hwal1
  have h0d := hxs econP0 8
  rw [h0] at h0d
  -- `x'` is revealed preferred to `x⁰`, so it costs at least 8 at `p⁰`
  have hcost : 8 ≤ x' 0 + x' 1 := by
    by_contra hlt
    rw [not_le] at hlt
    have hle := hx'.2 econX0 ⟨econX0_mem, by rw [econP1_dot]; norm_num [econX0]⟩
    obtain ⟨z, hz, hpz, hs⟩ := exists_better_affordable hlns econP0 hx'.1.1
      (by rw [econP0_dot]; exact hlt)
    have hzlt := (hrep.strict_iff hz hx'.1.1).mp hs
    have := h0d.2 z ⟨hz, hpz.le⟩
    linarith
  have hn := hnormal 20 26 (by norm_num)
  have hn0 : x' 0 ≤ xs econP1 26 0 := hn 0
  have hx'1 : 0 ≤ x' 1 := hx'.1.1 1
  linarith

/-- **Exercise 3.D.7(e)** (MWG, p. 98). For `x¹ ∈ ℝ²_+` on the budget line `p¹·x = 26`:
(i) if `u` is homogeneous of degree one on `ℝ²_+` (homothetic preferences) and represents a
locally nonsatiated `≿` with `x⁰ ∈ x(p⁰, 8)`, `x¹ ∈ x(p¹, 26)`, then `x¹₂ ≤ 26/5`; (ii) if
`x¹₂ ≤ 26/5`, the continuous, concave, degree-one homogeneous, monotone
`u(x) = min(p⁰·x, (2/5) p¹·x)` chooses `x⁰` and `x¹`. -/
theorem exercise_3_D_7e {x1 : Fin 2 → ℝ} (hx1 : x1 ∈ nonnegOrthant 2)
    (hb : x1 0 + 4 * x1 1 = 26) :
    (∀ (u : (Fin 2 → ℝ) → ℝ) (r : (Fin 2 → ℝ) → (Fin 2 → ℝ) → Prop),
      RepresentsOn (nonnegOrthant 2) u r → LocallyNonsatiated (nonnegOrthant 2) r →
      (∀ x ∈ nonnegOrthant 2, ∀ α : ℝ, 0 < α → u (α • x) = α * u x) →
      econX0 ∈ walrasianDemand u econP0 8 → x1 ∈ walrasianDemand u econP1 26 →
      x1 1 ≤ 26 / 5) ∧
    (x1 1 ≤ 26 / 5 → ∃ u : (Fin 2 → ℝ) → ℝ, Continuous u ∧ ConcaveOn ℝ (nonnegOrthant 2) u ∧
      (∀ x : Fin 2 → ℝ, ∀ α : ℝ, 0 ≤ α → u (α • x) = α * u x) ∧
      PrefMonotone (nonnegOrthant 2) (utilityPref u) ∧
      econX0 ∈ walrasianDemand u econP0 8 ∧ x1 ∈ walrasianDemand u econP1 26) := by
  constructor
  · intro u r hrep hlns hhom h0 h1
    set x' : Fin 2 → ℝ := (20 / 26 : ℝ) • x1 with hx'
    have hx'm : x' ∈ nonnegOrthant 2 := fun l => by
      simp only [hx', Pi.smul_apply, smul_eq_mul]; nlinarith [hx1 l]
    -- `u(x') ≥ u(x⁰)`: scale `x⁰` up to the budget `26`
    have hscale := hhom econX0 econX0_mem (26 / 20) (by norm_num)
    have hx0big : (26 / 20 : ℝ) • econX0 ∈ budgetSet econP1 26 := by
      refine ⟨fun l => ?_, ?_⟩
      · simp only [Pi.smul_apply, smul_eq_mul]; nlinarith [econX0_mem l]
      · rw [econP1_dot]; norm_num [econX0]
    have hle := h1.2 _ hx0big
    rw [hscale] at hle
    have hx'u := hhom x1 hx1 (20 / 26) (by norm_num)
    have hge : u econX0 ≤ u x' := by
      rw [hx', hx'u]
      nlinarith
    by_contra hgt
    rw [not_le] at hgt
    have hcost : econP0 ⬝ᵥ x' < 8 := by
      rw [econP0_dot]
      simp only [hx', Pi.smul_apply, smul_eq_mul]
      nlinarith
    obtain ⟨z, hz, hpz, hs⟩ := exists_better_affordable hlns econP0 hx'm hcost
    have hzlt := (hrep.strict_iff hz hx'm).mp hs
    have := h0.2 z ⟨hz, hpz.le⟩
    linarith
  · intro ht
    have hs : 52 / 5 ≤ x1 0 + x1 1 := by linarith
    refine ⟨fun x => min (econP0 ⬝ᵥ x) (2 / 5 * econP1 ⬝ᵥ x), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [econP0_dot, econP1_dot]
      fun_prop
    · refine ConcaveOn.inf ?_ ?_
      · exact (econ_affine_concaveOn econP0 0).congr fun x _ => by simp
      · have := econ_affine_concaveOn ((2 / 5 : ℝ) • econP1) 0
        refine this.congr fun x _ => ?_
        simp only [smul_dotProduct, smul_eq_mul, add_zero]
    · intro x α hα
      simp only [dotProduct_smul, smul_eq_mul]
      rw [show 2 / 5 * (α * econP1 ⬝ᵥ x) = α * (2 / 5 * econP1 ⬝ᵥ x) by ring]
      exact (mul_min_of_nonneg _ _ hα).symm
    · intro x _ y _ hxy
      have h0 : x 0 < y 0 := hxy 0
      have h1 : x 1 < y 1 := hxy 1
      have hlt : min (econP0 ⬝ᵥ x) (2 / 5 * econP1 ⬝ᵥ x) <
          min (econP0 ⬝ᵥ y) (2 / 5 * econP1 ⬝ᵥ y) := by
        simp only [econP0_dot, econP1_dot]
        exact min_lt_min (by linarith) (by linarith)
      exact ⟨hlt.le, not_le.mpr hlt⟩
    · refine ⟨⟨econX0_mem, by rw [econP0_dot]; norm_num [econX0]⟩, fun y hy => ?_⟩
      have hy2 := hy.2
      rw [econP0_dot] at hy2
      change min (econP0 ⬝ᵥ y) (2 / 5 * econP1 ⬝ᵥ y) ≤
        min (econP0 ⬝ᵥ econX0) (2 / 5 * econP1 ⬝ᵥ econX0)
      have hv : min (econP0 ⬝ᵥ econX0) (2 / 5 * econP1 ⬝ᵥ econX0) = 8 := by
        rw [econP0_dot, econP1_dot]
        norm_num [econX0]
      rw [hv, econP0_dot]
      exact (min_le_left _ _).trans hy2
    · refine ⟨⟨hx1, by rw [econP1_dot]; linarith⟩, fun y hy => ?_⟩
      have hy2 := hy.2
      rw [econP1_dot] at hy2
      have hv : min (econP0 ⬝ᵥ x1) (2 / 5 * econP1 ⬝ᵥ x1) = 52 / 5 := by
        rw [econP0_dot, econP1_dot, hb, min_eq_right (by linarith)]
        norm_num
      beta_reduce
      rw [hv, econP1_dot]
      refine (min_le_right _ _).trans ?_
      linarith

end MWG.ClassicalDemand
