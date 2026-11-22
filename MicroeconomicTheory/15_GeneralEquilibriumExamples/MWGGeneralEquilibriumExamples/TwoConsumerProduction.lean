/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGGeneralEquilibriumExamples.RobinsonCrusoe
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# One firm, two consumers: multiple equilibria (MWG Exercise 15.C.1(c), p. 542)

Exercise 15.C.1(c) asks for an example of multiple equilibria in a strictly convex economy with
one firm and two consumers, each endowed with labor alone, who split the profits equally, and
whether this can happen under constant returns to scale.

* The economy (`TCEconomy`): utilities over (leisure, consumption good), labor endowments `L̄ᵢ`,
  a production function `f`; profit maximization, the consumers' budgets with half the profit
  each, and Walrasian equilibrium (`TCEconomy.IsWalrasEqm`), mirroring Section 15.C.
* Tools: the utility index `v(s) = -(a/5)(a/(s + e))⁵` (`tcpPowFive`) is strictly concave and
  strictly increasing on `s ≥ 0`, with the tangent inequality `tcpPowFive_tangent` (from
  `x⁶ - 6xy⁵ + 5y⁶ ≥ 0`); utilities `c·x + φ(d·x)` (`tcpAffineUtility`) are continuous, strongly
  monotone and strictly convex under simple conditions; strictly convex preferences have at most
  one maximizer on a convex set (`tcp_eq_of_strictlyConvex`).
* **The example** (`ex15C1cEconomy`): `f(z) = 7 z^{1/7}` (strictly concave), consumer 1
  quasilinear in leisure, consumer 2 quasilinear in consumption. At `p = 1` both `w = 1` and
  `w = (8/9)⁶ = 262144/531441` are equilibrium wages, with different allocations
  (`exercise_15_C_1c`); the economy is strictly convex (`ex15C1c_strictlyConvex`).
* **Constant returns** `f(z) = αz`: with strongly monotone, strictly convex preferences, all
  equilibria have the same allocation (`exercise_15_C_1c_crs`), the real wage is `w/p = α`
  whenever production is positive (`exercise_15_C_1c_crs_wage`), and there is no equilibrium with
  `w < αp` (`exercise_15_C_1c_crs_no_low_wage`). (Equilibrium price ratios can differ only when
  nothing is produced.)
-/

namespace MWG.GeneralEquilibriumExamples

open MWG.ConsumerChoice MWG.ClassicalDemand Kreps.PreferenceProperties

/-! ### Tools -/

/-- `x⁶ - 6xy⁵ + 5y⁶ = (x - y)²(x⁴ + 2x³y + 3x²y² + 4xy³ + 5y⁴) ≥ 0` for `x, y ≥ 0`. -/
theorem tcp_six_poly_nonneg {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ x ^ 6 - 6 * x * y ^ 5 + 5 * y ^ 6 := by
  have e : x ^ 6 - 6 * x * y ^ 5 + 5 * y ^ 6 =
      (x - y) ^ 2 * (x ^ 4 + 2 * x ^ 3 * y + 3 * x ^ 2 * y ^ 2 + 4 * x * y ^ 3 + 5 * y ^ 4) := by
    ring
  rw [e]
  positivity

/-- `x⁶ - 6xy⁵ + 5y⁶ > 0` for `x, y > 0`, `x ≠ y`. -/
theorem tcp_six_poly_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hne : x ≠ y) :
    0 < x ^ 6 - 6 * x * y ^ 5 + 5 * y ^ 6 := by
  have e : x ^ 6 - 6 * x * y ^ 5 + 5 * y ^ 6 =
      (x - y) ^ 2 * (x ^ 4 + 2 * x ^ 3 * y + 3 * x ^ 2 * y ^ 2 + 4 * x * y ^ 3 + 5 * y ^ 4) := by
    ring
  rw [e]
  have h1 : 0 < (x - y) ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (sub_ne_zero.2 hne)))
  have h2 : 0 < x ^ 4 + 2 * x ^ 3 * y + 3 * x ^ 2 * y ^ 2 + 4 * x * y ^ 3 + 5 * y ^ 4 := by
    positivity
  exact mul_pos h1 h2

/-- The utility index `v(s) = -(a/5)(a/(s + e))⁵`, with `v'(s) = (a/(s + e))⁶`. -/
noncomputable def tcpPowFive (a e s : ℝ) : ℝ := -(a / 5) * (a / (s + e)) ^ 5

/-- The difference between the tangent line of `tcpPowFive` at `s` and its value at `t`. -/
theorem tcpPowFive_gap {a e s t : ℝ} (ha : 0 < a) (hs : 0 < s + e) (ht : 0 < t + e) :
    tcpPowFive a e s + (a / (s + e)) ^ 6 * (t - s) - tcpPowFive a e t =
      a / (5 * (a / (t + e))) * ((a / (t + e)) ^ 6 - 6 * (a / (t + e)) * (a / (s + e)) ^ 5 +
        5 * (a / (s + e)) ^ 6) := by
  unfold tcpPowFive
  field_simp
  ring

/-- The tangent inequality for `v = tcpPowFive a e` (concavity): for `s, t > -e`,
`v(t) ≤ v(s) + v'(s)(t - s)`. -/
theorem tcpPowFive_tangent {a e s t : ℝ} (ha : 0 < a) (hs : 0 < s + e) (ht : 0 < t + e) :
    tcpPowFive a e t ≤ tcpPowFive a e s + (a / (s + e)) ^ 6 * (t - s) := by
  have hg := tcpPowFive_gap ha hs ht
  have hr : 0 < a / (t + e) := div_pos ha ht
  have hm : 0 < a / (s + e) := div_pos ha hs
  have key := tcp_six_poly_nonneg hr.le hm.le
  have : 0 ≤ a / (5 * (a / (t + e))) * ((a / (t + e)) ^ 6 -
      6 * (a / (t + e)) * (a / (s + e)) ^ 5 + 5 * (a / (s + e)) ^ 6) :=
    mul_nonneg (by positivity) key
  linarith

/-- The strict tangent inequality for `v = tcpPowFive a e`: for `s, t > -e`, `t ≠ s`,
`v(t) < v(s) + v'(s)(t - s)`. -/
theorem tcpPowFive_tangent_strict {a e s t : ℝ} (ha : 0 < a) (hs : 0 < s + e) (ht : 0 < t + e)
    (hne : t ≠ s) : tcpPowFive a e t < tcpPowFive a e s + (a / (s + e)) ^ 6 * (t - s) := by
  have hg := tcpPowFive_gap ha hs ht
  have hr : 0 < a / (t + e) := div_pos ha ht
  have hm : 0 < a / (s + e) := div_pos ha hs
  have hrm : a / (t + e) ≠ a / (s + e) := by
    intro h
    rw [div_eq_div_iff ht.ne' hs.ne'] at h
    apply hne
    have := mul_left_cancel₀ ha.ne' h
    linarith
  have key := tcp_six_poly_pos hr hm hrm
  have : 0 < a / (5 * (a / (t + e))) * ((a / (t + e)) ^ 6 -
      6 * (a / (t + e)) * (a / (s + e)) ^ 5 + 5 * (a / (s + e)) ^ 6) :=
    mul_pos (by positivity) key
  linarith

/-- `v = tcpPowFive a e` (`a, e > 0`) is strictly concave on `[0, ∞)`. -/
theorem tcpPowFive_strictConcaveOn {a e : ℝ} (ha : 0 < a) (he : 0 < e) :
    StrictConcaveOn ℝ (Set.Ici 0) (tcpPowFive a e) := by
  refine ⟨convex_Ici 0, fun x hx y hy hxy α β hα hβ hαβ => ?_⟩
  have hx' : (0 : ℝ) ≤ x := hx
  have hy' : (0 : ℝ) ≤ y := hy
  simp only [smul_eq_mul]
  have hb : β = 1 - α := by linarith
  subst hb
  have hm0 : 0 < α * x + (1 - α) * y + e := by
    have : 0 ≤ α * x := mul_nonneg hα.le hx'
    have : 0 ≤ (1 - α) * y := mul_nonneg hβ.le hy'
    linarith
  have hxm : x ≠ α * x + (1 - α) * y := by
    intro h
    apply hxy
    have : (1 - α) * (x - y) = 0 := by linarith
    rcases mul_eq_zero.1 this with h1 | h1
    · linarith
    · linarith
  have hym : y ≠ α * x + (1 - α) * y := by
    intro h
    apply hxy
    have : α * (x - y) = 0 := by linarith
    rcases mul_eq_zero.1 this with h1 | h1
    · linarith
    · linarith
  have h1 := tcpPowFive_tangent_strict ha hm0 (by linarith) hxm
  have h2 := tcpPowFive_tangent_strict ha hm0 (by linarith) hym
  set D := (a / (α * x + (1 - α) * y + e)) ^ 6
  set m := α * x + (1 - α) * y
  have hz : α * (D * (x - m)) + (1 - α) * (D * (y - m)) = 0 := by
    simp only [m]
    ring
  nlinarith [mul_lt_mul_of_pos_left h1 hα, mul_lt_mul_of_pos_left h2 hβ]

/-- `v = tcpPowFive a e` (`a, e > 0`) is strictly increasing on `[0, ∞)`. -/
theorem tcpPowFive_strictMonoOn {a e : ℝ} (ha : 0 < a) (he : 0 < e) :
    StrictMonoOn (tcpPowFive a e) (Set.Ici 0) := by
  intro s hs t ht hst
  have hs' : (0 : ℝ) ≤ s := hs
  have ht' : (0 : ℝ) ≤ t := ht
  have h := tcpPowFive_tangent_strict ha (s := t) (t := s) (e := e) (by linarith)
    (by linarith) hst.ne
  have hD : 0 < (a / (t + e)) ^ 6 := by
    have : 0 < t + e := by linarith
    positivity
  have : (a / (t + e)) ^ 6 * (s - t) < 0 := mul_neg_of_pos_of_neg hD (by linarith)
  linarith

/-- `v = tcpPowFive a e` (`e > 0`) is continuous on `[0, ∞)`. -/
theorem tcpPowFive_continuousOn {a e : ℝ} (he : 0 < e) :
    ContinuousOn (tcpPowFive a e) (Set.Ici 0) := by
  intro s hs
  have hs' : (0 : ℝ) ≤ s := hs
  have hne : s + e ≠ 0 := by linarith
  have : ContinuousAt (fun s : ℝ => -(a / 5) * (a / (s + e)) ^ 5) s := by
    fun_prop (disch := exact hne)
  exact this.continuousWithinAt

/-- A utility `u(x) = c₀x₁ + c₁x₂ + φ(d₀x₁ + d₁x₂)`: a linear part plus an index of a linear
form (quasilinear utilities are the cases `c = e₁, d = e₂` and `c = e₂, d = e₁`). -/
def tcpAffineUtility (c₀ c₁ d₀ d₁ : ℝ) (φ : ℝ → ℝ) (x : Fin 2 → ℝ) : ℝ :=
  c₀ * x 0 + c₁ * x 1 + φ (d₀ * x 0 + d₁ * x 1)

/-- `c·x + φ(d·x)` is continuous on `ℝ²₊` when `d ≥ 0` and `φ` is continuous on `[0, ∞)`. -/
theorem tcpAffineUtility_continuousOn {c₀ c₁ d₀ d₁ : ℝ} (hd₀ : 0 ≤ d₀) (hd₁ : 0 ≤ d₁)
    {φ : ℝ → ℝ} (hφ : ContinuousOn φ (Set.Ici 0)) :
    ContinuousOn (tcpAffineUtility c₀ c₁ d₀ d₁ φ) (nonnegOrthant 2) := by
  have hlin : Continuous fun x : Fin 2 → ℝ => d₀ * x 0 + d₁ * x 1 := by fun_prop
  have hmaps : Set.MapsTo (fun x : Fin 2 → ℝ => d₀ * x 0 + d₁ * x 1) (nonnegOrthant 2)
      (Set.Ici 0) :=
    fun x hx => Set.mem_Ici.2 (add_nonneg (mul_nonneg hd₀ (hx 0)) (mul_nonneg hd₁ (hx 1)))
  have h2 := hφ.comp hlin.continuousOn hmaps
  have h1 : Continuous fun x : Fin 2 → ℝ => c₀ * x 0 + c₁ * x 1 := by fun_prop
  exact h1.continuousOn.add h2

/-- `c·x + φ(d·x)` is strongly monotone on `ℝ²₊` when `c, d ≥ 0`, every good enters `c` or `d`
with a positive weight, and `φ` is strictly increasing on `[0, ∞)`. -/
theorem tcpAffineUtility_stronglyMonotone {c₀ c₁ d₀ d₁ : ℝ} (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁)
    (hd₀ : 0 ≤ d₀) (hd₁ : 0 ≤ d₁) (h₀ : 0 < c₀ ∨ 0 < d₀) (h₁ : 0 < c₁ ∨ 0 < d₁) {φ : ℝ → ℝ}
    (hφ : StrictMonoOn φ (Set.Ici 0)) :
    UtilityStronglyMonotone (tcpAffineUtility c₀ c₁ d₀ d₁ φ) := by
  intro x hx y _ hxy hne
  have hx0 := hx 0
  have hx1 := hx 1
  have hle0 := hxy 0
  have hle1 := hxy 1
  have hsx : (0 : ℝ) ≤ d₀ * x 0 + d₁ * x 1 :=
    add_nonneg (mul_nonneg hd₀ hx0) (mul_nonneg hd₁ hx1)
  have hsy : (0 : ℝ) ≤ d₀ * y 0 + d₁ * y 1 :=
    add_nonneg (mul_nonneg hd₀ (hx0.trans hle0)) (mul_nonneg hd₁ (hx1.trans hle1))
  have m0 := mul_le_mul_of_nonneg_left hle0 hd₀
  have m1 := mul_le_mul_of_nonneg_left hle1 hd₁
  have n0 := mul_le_mul_of_nonneg_left hle0 hc₀
  have n1 := mul_le_mul_of_nonneg_left hle1 hc₁
  have hsle : d₀ * x 0 + d₁ * x 1 ≤ d₀ * y 0 + d₁ * y 1 := by linarith
  have hφle : φ (d₀ * x 0 + d₁ * x 1) ≤ φ (d₀ * y 0 + d₁ * y 1) :=
    (hφ.le_iff_le (Set.mem_Ici.2 hsx) (Set.mem_Ici.2 hsy)).2 hsle
  have hl : x 0 < y 0 ∨ x 1 < y 1 := by
    by_contra hall
    simp only [not_or, not_lt] at hall
    exact hne (funext fun l => by
      fin_cases l
      · exact le_antisymm hall.1 (hxy 0)
      · exact le_antisymm hall.2 (hxy 1))
  have hlt : tcpAffineUtility c₀ c₁ d₀ d₁ φ x < tcpAffineUtility c₀ c₁ d₀ d₁ φ y := by
    simp only [tcpAffineUtility]
    rcases hl with hl | hl
    · rcases h₀ with hc | hd
      · have := mul_lt_mul_of_pos_left hl hc
        linarith
      · have hs : d₀ * x 0 + d₁ * x 1 < d₀ * y 0 + d₁ * y 1 := by
          have := mul_lt_mul_of_pos_left hl hd
          linarith
        have := hφ (Set.mem_Ici.2 hsx) (Set.mem_Ici.2 hsy) hs
        linarith
    · rcases h₁ with hc | hd
      · have := mul_lt_mul_of_pos_left hl hc
        linarith
      · have hs : d₀ * x 0 + d₁ * x 1 < d₀ * y 0 + d₁ * y 1 := by
          have := mul_lt_mul_of_pos_left hl hd
          linarith
        have := hφ (Set.mem_Ici.2 hsx) (Set.mem_Ici.2 hsy) hs
        linarith
  exact ⟨hlt.le, not_le.2 hlt⟩

/-- `c·x + φ(d·x)` represents strictly convex preferences on `ℝ²₊` when `d ≥ 0`, `c` and `d` are
linearly independent, and `φ` is strictly concave on `[0, ∞)`: bundles with different `d·x` gain
from the strict concavity of `φ`; bundles with the same `d·x` differ in `c·x`, hence in utility. -/
theorem tcpAffineUtility_strictlyConvex {c₀ c₁ d₀ d₁ : ℝ} (hd₀ : 0 ≤ d₀) (hd₁ : 0 ≤ d₁)
    (hdet : c₀ * d₁ - c₁ * d₀ ≠ 0) {φ : ℝ → ℝ} (hφ : StrictConcaveOn ℝ (Set.Ici 0) φ) :
    PrefStrictlyConvex (nonnegOrthant 2) (utilityPref (tcpAffineUtility c₀ c₁ d₀ d₁ φ)) := by
  intro x _ y hy z hz hyx hzx hne α hα0 hα1
  change tcpAffineUtility c₀ c₁ d₀ d₁ φ x ≤ tcpAffineUtility c₀ c₁ d₀ d₁ φ y at hyx
  change tcpAffineUtility c₀ c₁ d₀ d₁ φ x ≤ tcpAffineUtility c₀ c₁ d₀ d₁ φ z at hzx
  suffices h : tcpAffineUtility c₀ c₁ d₀ d₁ φ x <
      tcpAffineUtility c₀ c₁ d₀ d₁ φ (α • y + (1 - α) • z) from ⟨h.le, not_le.2 h⟩
  have hm : tcpAffineUtility c₀ c₁ d₀ d₁ φ (α • y + (1 - α) • z) =
      α * (c₀ * y 0 + c₁ * y 1) + (1 - α) * (c₀ * z 0 + c₁ * z 1) +
        φ (α * (d₀ * y 0 + d₁ * y 1) + (1 - α) * (d₀ * z 0 + d₁ * z 1)) := by
    simp only [tcpAffineUtility, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have : d₀ * (α * y 0 + (1 - α) * z 0) + d₁ * (α * y 1 + (1 - α) * z 1) =
        α * (d₀ * y 0 + d₁ * y 1) + (1 - α) * (d₀ * z 0 + d₁ * z 1) := by ring
    rw [this]
    ring
  have huy : tcpAffineUtility c₀ c₁ d₀ d₁ φ y =
      c₀ * y 0 + c₁ * y 1 + φ (d₀ * y 0 + d₁ * y 1) := rfl
  have huz : tcpAffineUtility c₀ c₁ d₀ d₁ φ z =
      c₀ * z 0 + c₁ * z 1 + φ (d₀ * z 0 + d₁ * z 1) := rfl
  rw [hm]
  rw [huy] at hyx
  rw [huz] at hzx
  have hsy : (0 : ℝ) ≤ d₀ * y 0 + d₁ * y 1 :=
    add_nonneg (mul_nonneg hd₀ (hy 0)) (mul_nonneg hd₁ (hy 1))
  have hsz : (0 : ℝ) ≤ d₀ * z 0 + d₁ * z 1 :=
    add_nonneg (mul_nonneg hd₀ (hz 0)) (mul_nonneg hd₁ (hz 1))
  by_cases hs : d₀ * y 0 + d₁ * y 1 = d₀ * z 0 + d₁ * z 1
  · -- same index: the linear parts differ
    have hc : c₀ * y 0 + c₁ * y 1 ≠ c₀ * z 0 + c₁ * z 1 := by
      intro hc
      apply hne
      have h0 : (c₀ * d₁ - c₁ * d₀) * (y 0 - z 0) = 0 := by linear_combination d₁ * hc - c₁ * hs
      have h1 : (c₀ * d₁ - c₁ * d₀) * (y 1 - z 1) = 0 := by linear_combination c₀ * hs - d₀ * hc
      have e0 := (mul_eq_zero.1 h0).resolve_left hdet
      have e1 := (mul_eq_zero.1 h1).resolve_left hdet
      funext l
      fin_cases l
      · simp only [Fin.zero_eta, Fin.isValue]
        linarith
      · simp only [Fin.mk_one, Fin.isValue]
        linarith
    have hφ' : α * (d₀ * y 0 + d₁ * y 1) + (1 - α) * (d₀ * z 0 + d₁ * z 1) =
        d₀ * z 0 + d₁ * z 1 := by rw [hs]; ring
    rw [hφ']
    rw [hs] at hyx
    rcases lt_or_gt_of_ne hc with h | h
    · nlinarith [mul_lt_mul_of_pos_left h hα0]
    · have h1α : 0 < 1 - α := by linarith
      nlinarith [mul_lt_mul_of_pos_left h h1α]
  · have h := hφ.2 (Set.mem_Ici.2 hsy) (Set.mem_Ici.2 hsz) hs hα0
      (by linarith : (0 : ℝ) < 1 - α) (by ring : α + (1 - α) = 1)
    simp only [smul_eq_mul] at h
    nlinarith

/-- Strictly convex preferences have at most one maximizer on a convex subset of `ℝ^L₊`: the
midpoint of two maximizers would be strictly better. -/
theorem tcp_eq_of_strictlyConvex {L : ℕ} {u : (Fin L → ℝ) → ℝ}
    (hsc : PrefStrictlyConvex (nonnegOrthant L) (utilityPref u)) {B : Set (Fin L → ℝ)}
    (hB : Convex ℝ B) (hBX : B ⊆ nonnegOrthant L) {x y : Fin L → ℝ} (hx : x ∈ B) (hy : y ∈ B)
    (hxo : ∀ z ∈ B, u z ≤ u x) (hyo : ∀ z ∈ B, u z ≤ u y) : x = y := by
  by_contra hne
  have hmB : (1 / 2 : ℝ) • x + ((1 : ℝ) - 1 / 2) • y ∈ B :=
    hB hx hy (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 - 1 / 2)
      (by norm_num)
  have h := hsc x (hBX hx) x (hBX hx) y (hBX hy) (le_refl (u x)) (hyo x hx) hne (1 / 2)
    (by norm_num) (by norm_num)
  exact h.2 (hxo _ hmB)

/-! ### The economy -/

/-- **Exercise 15.C.1(c)** (MWG, p. 542). One firm and two consumers `i : Fin 2`, each endowed
with labor alone: utilities `uᵢ` over (leisure, consumption good), time endowments `L̄ᵢ`, and the
production function `f`; each consumer owns half of the firm. -/
structure TCEconomy where
  /-- The consumers' utilities over (leisure, consumption good). -/
  u : Fin 2 → (Fin 2 → ℝ) → ℝ
  /-- The time endowments `L̄ᵢ`. -/
  Lbar : Fin 2 → ℝ
  /-- The production function `f(z)`. -/
  f : ℝ → ℝ

/-- **Exercise 15.C.1(c)** (MWG, p. 542), as (15.C.1). `z` maximizes the firm's profit
`p f(z) - w z` over `z ≥ 0`. -/
def TCEconomy.IsProfitMax (E : TCEconomy) (p w z : ℝ) : Prop :=
  0 ≤ z ∧ ∀ z', 0 ≤ z' → p * E.f z' - w * z' ≤ p * E.f z - w * z

/-- **Exercise 15.C.1(c)** (MWG, p. 542), as (15.C.2). Consumer `i`'s budget set at prices
`(p, w)` with nonlabor income `m`: `x ∈ ℝ²₊` with `p x₂ ≤ w(L̄ᵢ - x₁) + m`. -/
def TCEconomy.budget (E : TCEconomy) (i : Fin 2) (p w m : ℝ) : Set (Fin 2 → ℝ) :=
  {x | x ∈ nonnegOrthant 2 ∧ p * x 1 ≤ w * (E.Lbar i - x 0) + m}

/-- **Exercise 15.C.1(c)** (MWG, p. 542). `x` solves consumer `i`'s problem. -/
def TCEconomy.IsConsumerOpt (E : TCEconomy) (i : Fin 2) (p w m : ℝ) (x : Fin 2 → ℝ) : Prop :=
  x ∈ E.budget i p w m ∧ ∀ y ∈ E.budget i p w m, E.u i y ≤ E.u i x

/-- **Exercise 15.C.1(c)** (MWG, p. 542). A Walrasian equilibrium: prices `(p, w)`, labor demand
`z` maximizing profit, bundles `xᵢ` maximizing utility with income `w L̄ᵢ + π/2`,
`π = p f(z) - w z`, and market clearing `x₂₁ + x₂₂ = f(z)`, `z = (L̄₁ - x₁₁) + (L̄₂ - x₁₂)`. -/
def TCEconomy.IsWalrasEqm (E : TCEconomy) (p w : ℝ) (x : Fin 2 → Fin 2 → ℝ) (z : ℝ) : Prop :=
  E.IsProfitMax p w z ∧ (∀ i, E.IsConsumerOpt i p w ((p * E.f z - w * z) / 2) (x i)) ∧
    x 0 1 + x 1 1 = E.f z ∧ z = (E.Lbar 0 - x 0 0) + (E.Lbar 1 - x 1 0)

/-! ### The example with strictly decreasing returns -/

/-- **Exercise 15.C.1(c)** (MWG, p. 542). The example: `f(z) = 7 z^{1/7}`; consumer 1 has
`u₁(x) = x₁ + v_A(x₂)`, `v_A = tcpPowFive (15841/2175) (3/10)`, `L̄₁ = 6`; consumer 2 has
`u₂(x) = x₂ + v_B(x₁)`, `v_B = tcpPowFive (7141/2175) (1/10)`, `L̄₂ = 1/5`. -/
noncomputable def ex15C1cEconomy : TCEconomy where
  u := ![tcpAffineUtility 1 0 0 1 (tcpPowFive (15841 / 2175) (3 / 10)),
    tcpAffineUtility 0 1 1 0 (tcpPowFive (7141 / 2175) (1 / 10))]
  Lbar := ![6, 1 / 5]
  f := fun z => 7 * z ^ (1 / 7 : ℝ)

/-- Consumer 1 of `ex15C1cEconomy`, quasilinear in leisure. -/
theorem ex15C1c_u0 :
    ex15C1cEconomy.u 0 = tcpAffineUtility 1 0 0 1 (tcpPowFive (15841 / 2175) (3 / 10)) := rfl

/-- Consumer 2 of `ex15C1cEconomy`, quasilinear in consumption. -/
theorem ex15C1c_u1 :
    ex15C1cEconomy.u 1 = tcpAffineUtility 0 1 1 0 (tcpPowFive (7141 / 2175) (1 / 10)) := rfl

/-- Consumer 1 of `ex15C1cEconomy` has six units of time. -/
theorem ex15C1c_Lbar0 : ex15C1cEconomy.Lbar 0 = 6 := rfl

/-- Consumer 2 of `ex15C1cEconomy` has one fifth of a unit of time. -/
theorem ex15C1c_Lbar1 : ex15C1cEconomy.Lbar 1 = 1 / 5 := rfl

/-- Consumer 1 (quasilinear in leisure, `u = x₁ + v(x₂)`, `v = tcpPowFive a e`) at the wage
`w = θ⁶` (`p = 1`): a bundle on the budget line with `x₂ + e = aθ` (so `v'(x₂) = 1/w`) is
optimal in the budget set, whatever the income. -/
theorem tcp_consumerA_opt {a e θ L m : ℝ} (ha : 0 < a) (he : 0 < e) (hθ : 0 < θ)
    {x : Fin 2 → ℝ} (hx : x ∈ nonnegOrthant 2) (hc : x 1 + e = a * θ)
    (hbud : x 1 = θ ^ 6 * (L - x 0) + m) {y : Fin 2 → ℝ} (hy : y ∈ nonnegOrthant 2)
    (hyb : 1 * y 1 ≤ θ ^ 6 * (L - y 0) + m) :
    tcpAffineUtility 1 0 0 1 (tcpPowFive a e) y ≤ tcpAffineUtility 1 0 0 1 (tcpPowFive a e) x := by
  simp only [tcpAffineUtility, one_mul, zero_mul, add_zero, zero_add]
  have ht := tcpPowFive_tangent ha (s := x 1) (t := y 1) (e := e) (by linarith [hx 1])
    (by linarith [hy 1])
  have hD : (a / (x 1 + e)) ^ 6 = 1 / θ ^ 6 := by
    rw [hc]
    field_simp
  rw [hD] at ht
  have hw : 0 < θ ^ 6 := by positivity
  have h1 : (y 1 - x 1) / θ ^ 6 ≤ x 0 - y 0 := by
    rw [div_le_iff₀ hw]
    nlinarith
  have h2 : 1 / θ ^ 6 * (y 1 - x 1) = (y 1 - x 1) / θ ^ 6 := by ring
  linarith

/-- Consumer 2 (quasilinear in consumption, `u = x₂ + v(x₁)`, `v = tcpPowFive b e`) at the wage
`w = θ⁶` (`p = 1`): a bundle on the budget line with `x₁ + e = b/θ` (so `v'(x₁) = w`) is optimal
in the budget set, whatever the income. -/
theorem tcp_consumerB_opt {b e θ L m : ℝ} (hb : 0 < b) (he : 0 < e) (hθ : 0 < θ)
    {x : Fin 2 → ℝ} (hx : x ∈ nonnegOrthant 2) (hl : x 0 + e = b / θ)
    (hbud : x 1 = θ ^ 6 * (L - x 0) + m) {y : Fin 2 → ℝ} (hy : y ∈ nonnegOrthant 2)
    (hyb : 1 * y 1 ≤ θ ^ 6 * (L - y 0) + m) :
    tcpAffineUtility 0 1 1 0 (tcpPowFive b e) y ≤ tcpAffineUtility 0 1 1 0 (tcpPowFive b e) x := by
  simp only [tcpAffineUtility, one_mul, zero_mul, add_zero, zero_add]
  have ht := tcpPowFive_tangent hb (s := x 0) (t := y 0) (e := e) (by linarith [hx 0])
    (by linarith [hy 0])
  have hD : (b / (x 0 + e)) ^ 6 = θ ^ 6 := by
    rw [hl]
    field_simp
  rw [hD] at ht
  nlinarith

/-- The firm of the example at the wage `w = θ⁶` (`p = 1`): `z* = θ⁻⁷` maximizes
`7 z^{1/7} - θ⁶ z` (with `u = θ z^{1/7}`: `u⁷ - 7u + 6 = (u - 1)²(u⁵ + 2u⁴ + ⋯ + 6) ≥ 0`), with
output `7/θ` and profit `6/θ`. -/
theorem ex15C1c_profitMax {θ : ℝ} (hθ : 0 < θ) :
    ex15C1cEconomy.IsProfitMax 1 (θ ^ 6) ((θ⁻¹) ^ 7) ∧
      ex15C1cEconomy.f ((θ⁻¹) ^ 7) = 7 / θ := by
  have h7 : (1 / 7 : ℝ) = ((7 : ℕ) : ℝ)⁻¹ := by norm_num
  have hf : ex15C1cEconomy.f ((θ⁻¹) ^ 7) = 7 / θ := by
    change 7 * ((θ⁻¹) ^ 7) ^ (1 / 7 : ℝ) = 7 / θ
    rw [h7, Real.pow_rpow_inv_natCast (by positivity) (by norm_num)]
    ring
  refine ⟨⟨by positivity, fun z hz => ?_⟩, hf⟩
  rw [hf]
  change 1 * (7 * z ^ (1 / 7 : ℝ)) - θ ^ 6 * z ≤ 1 * (7 / θ) - θ ^ 6 * θ⁻¹ ^ 7
  set t := z ^ (1 / 7 : ℝ) with ht
  have ht0 : 0 ≤ t := Real.rpow_nonneg hz _
  have htz : t ^ 7 = z := by
    rw [ht, h7]
    exact Real.rpow_inv_natCast_pow hz (by norm_num)
  rw [← htz]
  have hv : 0 ≤ θ * t := mul_nonneg hθ.le ht0
  have key : 0 ≤ (θ * t) ^ 7 - 7 * (θ * t) + 6 := by
    have e : (θ * t) ^ 7 - 7 * (θ * t) + 6 = (θ * t - 1) ^ 2 * ((θ * t) ^ 5 + 2 * (θ * t) ^ 4 +
        3 * (θ * t) ^ 3 + 4 * (θ * t) ^ 2 + 5 * (θ * t) + 6) := by ring
    rw [e]
    positivity
  have hr : 1 * (7 / θ) - θ ^ 6 * θ⁻¹ ^ 7 = 6 / θ := by
    field_simp
    ring
  rw [hr, le_div_iff₀ hθ]
  nlinarith [key]

/-- The example at the wage `w = θ⁶`, `p = 1`, labor `z = θ⁻⁷`: an allocation `x ≥ 0` with
consumer 1 at `x₂₁ + 3/10 = (15841/2175)θ`, consumer 2 at `x₁₂ + 1/10 = (7141/2175)/θ`, both on
their budget lines with profit share `3/θ`, and clearing markets, is a Walrasian equilibrium. -/
theorem ex15C1c_eqm_of {θ : ℝ} (hθ : 0 < θ) {x : Fin 2 → Fin 2 → ℝ}
    (hx : ∀ i, x i ∈ nonnegOrthant 2) (hA : x 0 1 + 3 / 10 = 15841 / 2175 * θ)
    (hB : x 1 0 + 1 / 10 = 7141 / 2175 / θ) (hbA : x 0 1 = θ ^ 6 * (6 - x 0 0) + 3 / θ)
    (hbB : x 1 1 = θ ^ 6 * (1 / 5 - x 1 0) + 3 / θ) (hgoods : x 0 1 + x 1 1 = 7 / θ)
    (hlabor : (θ⁻¹) ^ 7 = (6 - x 0 0) + (1 / 5 - x 1 0)) :
    ex15C1cEconomy.IsWalrasEqm 1 (θ ^ 6) x ((θ⁻¹) ^ 7) := by
  obtain ⟨hpm, hf⟩ := ex15C1c_profitMax hθ
  have hm : (1 * ex15C1cEconomy.f ((θ⁻¹) ^ 7) - θ ^ 6 * (θ⁻¹) ^ 7) / 2 = 3 / θ := by
    rw [hf]
    field_simp
    ring
  refine ⟨hpm, Fin.forall_fin_two.2 ⟨?_, ?_⟩, by rw [hf]; exact hgoods, hlabor⟩
  · rw [hm]
    refine ⟨⟨hx 0, ?_⟩, fun y hy => ?_⟩
    · rw [ex15C1c_Lbar0]
      linarith
    · rw [ex15C1c_u0]
      have hyb := hy.2
      rw [ex15C1c_Lbar0] at hyb
      exact tcp_consumerA_opt (by norm_num) (by norm_num) hθ (hx 0) hA hbA hy.1 hyb
  · rw [hm]
    refine ⟨⟨hx 1, ?_⟩, fun y hy => ?_⟩
    · rw [ex15C1c_Lbar1]
      linarith
    · rw [ex15C1c_u1]
      have hyb := hy.2
      rw [ex15C1c_Lbar1] at hyb
      exact tcp_consumerB_opt (by norm_num) (by norm_num) hθ (hx 1) hB hbB hy.1 hyb

/-- The equilibrium allocation of the example at `w = 1`. -/
noncomputable def ex15C1cAlloc1 : Fin 2 → Fin 2 → ℝ :=
  ![![8773 / 4350, 30377 / 4350], ![13847 / 4350, 73 / 4350]]

/-- The equilibrium allocation of the example at `w = (8/9)⁶`. -/
noncomputable def ex15C1cAlloc2 : Fin 2 → Fin 2 → ℝ :=
  ![![495178323 / 1520435200, 241711 / 39150], ![20843 / 5800, 266381 / 156600]]

/-- **Exercise 15.C.1(c)** (MWG, p. 542). Multiple equilibria with one firm and two consumers
endowed with labor alone, profits split equally: in `ex15C1cEconomy` (strictly convex, see
`ex15C1c_strictlyConvex`), at `p = 1` both `w = 1` (labor `z = 1`, output `7`) and
`w = 262144/531441 = (8/9)⁶` (labor `z = (9/8)⁷`, output `63/8`) are equilibrium wages; the real
wages and the allocations differ. -/
theorem exercise_15_C_1c :
    ex15C1cEconomy.IsWalrasEqm 1 1 ex15C1cAlloc1 1 ∧
      ex15C1cEconomy.IsWalrasEqm 1 (262144 / 531441) ex15C1cAlloc2 (4782969 / 2097152) ∧
      (1 : ℝ) / 1 ≠ (262144 / 531441) / 1 ∧ ex15C1cAlloc1 ≠ ex15C1cAlloc2 ∧
      (1 : ℝ) ≠ 4782969 / 2097152 := by
  refine ⟨?_, ?_, by norm_num, fun h => ?_, by norm_num⟩
  · have h := ex15C1c_eqm_of (θ := 1) one_pos (x := ex15C1cAlloc1)
      (fun i => by fin_cases i <;> intro l <;> fin_cases l <;> norm_num [ex15C1cAlloc1])
      (by norm_num [ex15C1cAlloc1]) (by norm_num [ex15C1cAlloc1]) (by norm_num [ex15C1cAlloc1])
      (by norm_num [ex15C1cAlloc1]) (by norm_num [ex15C1cAlloc1]) (by norm_num [ex15C1cAlloc1])
    rwa [one_pow, inv_one, one_pow] at h
  · have h := ex15C1c_eqm_of (θ := 8 / 9) (by norm_num) (x := ex15C1cAlloc2)
      (fun i => by fin_cases i <;> intro l <;> fin_cases l <;> norm_num [ex15C1cAlloc2])
      (by norm_num [ex15C1cAlloc2]) (by norm_num [ex15C1cAlloc2]) (by norm_num [ex15C1cAlloc2])
      (by norm_num [ex15C1cAlloc2]) (by norm_num [ex15C1cAlloc2]) (by norm_num [ex15C1cAlloc2])
    rwa [show ((8 : ℝ) / 9) ^ 6 = 262144 / 531441 by norm_num,
      show ((8 / 9 : ℝ)⁻¹) ^ 7 = 4782969 / 2097152 by norm_num] at h
  · have := congrFun (congrFun h 0) 1
    norm_num [ex15C1cAlloc1, ex15C1cAlloc2] at this

/-- **Exercise 15.C.1(c)** (MWG, p. 542). The example economy is strictly convex: each utility is
continuous on `ℝ²₊`, strongly monotone and strictly convex, and `f(z) = 7 z^{1/7}` is strictly
concave on `[0, ∞)` (strictly decreasing returns to scale). -/
theorem ex15C1c_strictlyConvex :
    (∀ i, ContinuousOn (ex15C1cEconomy.u i) (nonnegOrthant 2) ∧
      UtilityStronglyMonotone (ex15C1cEconomy.u i) ∧
      PrefStrictlyConvex (nonnegOrthant 2) (utilityPref (ex15C1cEconomy.u i))) ∧
      StrictConcaveOn ℝ (Set.Ici 0) ex15C1cEconomy.f := by
  refine ⟨Fin.forall_fin_two.2 ⟨?_, ?_⟩, ?_⟩
  · rw [ex15C1c_u0]
    have ha : (0 : ℝ) < 15841 / 2175 := by norm_num
    have he : (0 : ℝ) < 3 / 10 := by norm_num
    exact ⟨tcpAffineUtility_continuousOn le_rfl zero_le_one (tcpPowFive_continuousOn he),
      tcpAffineUtility_stronglyMonotone zero_le_one le_rfl le_rfl zero_le_one
        (Or.inl one_pos) (Or.inr one_pos) (tcpPowFive_strictMonoOn ha he),
      tcpAffineUtility_strictlyConvex le_rfl zero_le_one (by norm_num)
        (tcpPowFive_strictConcaveOn ha he)⟩
  · rw [ex15C1c_u1]
    have hb : (0 : ℝ) < 7141 / 2175 := by norm_num
    have he : (0 : ℝ) < 1 / 10 := by norm_num
    exact ⟨tcpAffineUtility_continuousOn zero_le_one le_rfl (tcpPowFive_continuousOn he),
      tcpAffineUtility_stronglyMonotone le_rfl zero_le_one zero_le_one le_rfl
        (Or.inr one_pos) (Or.inl one_pos) (tcpPowFive_strictMonoOn hb he),
      tcpAffineUtility_strictlyConvex zero_le_one le_rfl (by norm_num)
        (tcpPowFive_strictConcaveOn hb he)⟩
  · refine ⟨convex_Ici 0, fun x hx y hy hxy a b ha hb hab => ?_⟩
    have := (Real.strictConcaveOn_rpow (p := 1 / 7) (by norm_num) (by norm_num)).2 hx hy hxy
      ha hb hab
    simp only [smul_eq_mul] at this ⊢
    change a * (7 * x ^ (1 / 7 : ℝ)) + b * (7 * y ^ (1 / 7 : ℝ)) < 7 * (a * x + b * y) ^ (1 / 7 : ℝ)
    nlinarith

/-! ### Constant returns to scale -/

/-- In an equilibrium with consumer 1's preferences strongly monotone, the price of the
consumption good is positive (otherwise more of it is free). -/
theorem tcp_eqm_price_pos {E : TCEconomy} (hmono : UtilityStronglyMonotone (E.u 0)) {p w : ℝ}
    {x : Fin 2 → Fin 2 → ℝ} {z : ℝ} (h : E.IsWalrasEqm p w x z) : 0 < p := by
  by_contra hp
  rw [not_lt] at hp
  have hx := h.2.1 0
  have hmem : x 0 + Pi.single 1 1 ∈ E.budget 0 p w ((p * E.f z - w * z) / 2) := by
    refine ⟨fun l => ?_, ?_⟩
    · fin_cases l
      · simpa using hx.1.1 0
      · simp; linarith [hx.1.1 1]
    · have := hx.1.2
      simp only [Pi.add_apply, Pi.single_eq_same]
      simp only [ne_eq, zero_ne_one, not_false_eq_true, Pi.single_eq_of_ne, add_zero]
      nlinarith
  have h1 := hx.2 _ hmem
  have h2 := hmono.lt hx.1.1 (y := x 0 + Pi.single 1 1) (fun l => by
    fin_cases l <;> simp) (fun he => by simpa using congrFun he 1)
  linarith

/-- Profit maximization with `f(z) = αz`: the wage is at least `αp` and profit is zero. -/
theorem tcp_crs_profitMax {E : TCEconomy} {α : ℝ} (hf : E.f = fun z => α * z) {p w z : ℝ}
    (h : E.IsProfitMax p w z) : α * p ≤ w ∧ p * E.f z - w * z = 0 := by
  obtain ⟨hz, hmax⟩ := h
  rw [hf] at hmax ⊢
  have h1 := hmax (z + 1) (by linarith)
  have h0 := hmax 0 le_rfl
  simp only at h1 h0 ⊢
  have hw : α * p ≤ w := by nlinarith
  refine ⟨hw, ?_⟩
  have : (α * p - w) * z ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hz
  nlinarith

/-- **Exercise 15.C.1(c)** (MWG, p. 542), constant returns `f(z) = αz`: there is no equilibrium
with `w < αp` (profits would be unbounded). -/
theorem exercise_15_C_1c_crs_no_low_wage {E : TCEconomy} {α : ℝ} (hf : E.f = fun z => α * z)
    {p w : ℝ} (hw : w < α * p) (x : Fin 2 → Fin 2 → ℝ) (z : ℝ) : ¬ E.IsWalrasEqm p w x z :=
  fun h => absurd (tcp_crs_profitMax hf h.1).1 (not_le.2 hw)

/-- With constant returns `f(z) = αz` (`α > 0`) and strongly monotone preferences, each consumer's
equilibrium bundle solves his problem at the prices `(p, w) = (1, α)` with zero profit. -/
theorem tcp_crs_consumerOpt {E : TCEconomy} {α : ℝ} (hα : 0 < α) (hf : E.f = fun z => α * z)
    (hmono : UtilityStronglyMonotone (E.u 0)) {p w : ℝ} {x : Fin 2 → Fin 2 → ℝ} {z : ℝ}
    (h : E.IsWalrasEqm p w x z) (i : Fin 2) : E.IsConsumerOpt i 1 α 0 (x i) := by
  have hp := tcp_eqm_price_pos hmono h
  obtain ⟨hw, hπ⟩ := tcp_crs_profitMax hf h.1
  obtain ⟨hpm, hopt, hgoods, hlabor⟩ := h
  rw [hπ, zero_div] at hopt
  -- the budget set at `(1, α)` lies in the equilibrium budget set
  have hsub : E.budget i 1 α 0 ⊆ E.budget i p w 0 := by
    intro y hy
    refine ⟨hy.1, ?_⟩
    have hb := hy.2
    have hy1 := hy.1 1
    have hL : 0 ≤ E.Lbar i - y 0 := by
      by_contra hneg
      rw [not_le] at hneg
      have : α * (E.Lbar i - y 0) < 0 := mul_neg_of_pos_of_neg hα hneg
      linarith
    have : α * p * (E.Lbar i - y 0) ≤ w * (E.Lbar i - y 0) := mul_le_mul_of_nonneg_right hw hL
    nlinarith
  -- the equilibrium bundle is affordable at `(1, α)`
  have hmem : x i ∈ E.budget i 1 α 0 := by
    refine ⟨(hopt i).1.1, ?_⟩
    rcases eq_or_lt_of_le hw with hweq | hwlt
    · have hb := (hopt i).1.2
      rw [← hweq] at hb
      have : p * x i 1 ≤ p * (α * (E.Lbar i - x i 0) + 0) := by nlinarith
      have := le_of_mul_le_mul_left this hp
      linarith
    · -- `w > αp`: nothing is produced and every consumer stays at his endowment point
      have hz : z = 0 := by
        have hfz : p * E.f z - w * z = (α * p - w) * z := by rw [hf]; ring
        rw [hfz] at hπ
        rcases mul_eq_zero.1 hπ with h1 | h1
        · linarith
        · exact h1
      have hf0 : E.f z = 0 := by rw [hf, hz]; ring
      have hw0 : 0 < w := by nlinarith
      have hL : ∀ j, 0 ≤ E.Lbar j - x j 0 := by
        intro j
        have hb := (hopt j).1.2
        have := (hopt j).1.1 1
        by_contra hneg
        rw [not_le] at hneg
        have : w * (E.Lbar j - x j 0) < 0 := mul_neg_of_pos_of_neg hw0 hneg
        nlinarith
      have hL0 := hL 0
      have hL1 := hL 1
      have hc0 := (hopt 0).1.1 1
      have hc1 := (hopt 1).1.1 1
      rw [hf0] at hgoods
      fin_cases i
      · simp only [Fin.zero_eta, Fin.isValue]
        nlinarith
      · simp only [Fin.mk_one, Fin.isValue]
        nlinarith
  exact ⟨hmem, fun y hy => (hopt i).2 y (hsub hy)⟩

/-- The budget set `{x ∈ ℝ²₊ : p x₂ ≤ w(L̄ᵢ - x₁) + m}` is convex. -/
theorem TCEconomy.convex_budget (E : TCEconomy) (i : Fin 2) (p w m : ℝ) :
    Convex ℝ (E.budget i p w m) := by
  intro y hy z hz a b ha hb hab
  refine ⟨convex_nonnegOrthant 2 hy.1 hz.1 ha hb hab, ?_⟩
  have h1 := mul_le_mul_of_nonneg_left hy.2 ha
  have h2 := mul_le_mul_of_nonneg_left hz.2 hb
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have e : m = (a + b) * m := by rw [hab, one_mul]
  have e2 : w * E.Lbar i = (a + b) * (w * E.Lbar i) := by rw [hab, one_mul]
  nlinarith

/-- **Exercise 15.C.1(c)** (MWG, p. 542), second question. With constant returns `f(z) = αz`
(`α > 0`) and strongly monotone, strictly convex preferences, the equilibrium allocation is
unique: any two equilibria have the same consumption bundles and the same level of production.
(Every equilibrium bundle is the unique demand at `(p, w) = (1, α)` with zero profit.) -/
theorem exercise_15_C_1c_crs {E : TCEconomy} {α : ℝ} (hα : 0 < α) (hf : E.f = fun z => α * z)
    (hmono : ∀ i, UtilityStronglyMonotone (E.u i))
    (hsc : ∀ i, PrefStrictlyConvex (nonnegOrthant 2) (utilityPref (E.u i))) {p w p' w' z z' : ℝ}
    {x x' : Fin 2 → Fin 2 → ℝ} (h : E.IsWalrasEqm p w x z) (h' : E.IsWalrasEqm p' w' x' z') :
    x = x' ∧ z = z' := by
  have hx : ∀ i, x i = x' i := by
    intro i
    have o := tcp_crs_consumerOpt hα hf (hmono 0) h i
    have o' := tcp_crs_consumerOpt hα hf (hmono 0) h' i
    exact tcp_eq_of_strictlyConvex (hsc i) (E.convex_budget i 1 α 0) (fun y hy => hy.1) o.1 o'.1
      o.2 o'.2
  have hxx : x = x' := funext hx
  refine ⟨hxx, ?_⟩
  rw [h.2.2.2, h'.2.2.2, hxx]

/-- **Exercise 15.C.1(c)** (MWG, p. 542), constant returns `f(z) = αz`: in an equilibrium with
positive production the real wage is `w/p = α`. -/
theorem exercise_15_C_1c_crs_wage {E : TCEconomy} {α : ℝ} (hf : E.f = fun z => α * z)
    (hmono : UtilityStronglyMonotone (E.u 0)) {p w : ℝ} {x : Fin 2 → Fin 2 → ℝ} {z : ℝ}
    (h : E.IsWalrasEqm p w x z) (hz : 0 < z) : w / p = α := by
  have hp := tcp_eqm_price_pos hmono h
  have hπ := (tcp_crs_profitMax hf h.1).2
  rw [hf] at hπ
  simp only at hπ
  have : (α * p - w) * z = 0 := by linarith
  have hw : α * p - w = 0 := (mul_eq_zero.1 this).resolve_right hz.ne'
  rw [div_eq_iff hp.ne']
  linarith

end MWG.GeneralEquilibriumExamples
