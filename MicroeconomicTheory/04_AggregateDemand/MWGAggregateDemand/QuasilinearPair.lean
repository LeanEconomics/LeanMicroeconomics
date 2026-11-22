/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGAggregateDemand.AggregateSlutsky
import MWGAggregateDemand.LShaped
import MWGAggregateDemand.AggregateWealth
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Exercise 4.C.11: two quasilinear consumers

MWG, Exercise 4.C.11 (pp. 124-125). Two goods; `u₁(x) = x₁ + 4√x₂`, `u₂(x) = 4√x₁ + x₂`; equal
wealths `w/2`.

* `ql_bound`: the one-variable inequality behind both demands.
* `exercise_4_C_11a_consumer1`, `exercise_4_C_11a_consumer2` (part (a)): the individual demands,
  interior (`w/2 ≥ 4 p₁²/p₂`, resp. `w/2 ≥ 4 p₂²/p₁`) and at the corner; `exercise_4_C_11a`:
  aggregate demand where both are interior.
* `exercise_4_C_11c` (part (c)): at `p = (1, 1)` and `w > 8`, `v·C(p, w) v = (w - 16)(v₁ - v₂)²/4`,
  so `C` is positive semidefinite iff `w ≥ 16`, and for `8 < w < 16` it is negative semidefinite
  with `dp·C dp < 0` at `dp = (1, -1)`.

Part (b) (the Slutsky matrices and the weak axiom) is in `QuasilinearSlutsky`; part (d) is
graphical.
-/

namespace MWG.AggregateDemand

open MWG.ConsumerChoice MWG.ClassicalDemand Filter Topology

/-- **Exercise 4.C.11** (MWG, p. 124), the inequality behind both demands: with `a, b > 0`,
`y₀, y₁ ≥ 0` and `a y₀ + b y₁ ≤ W`, (i) if `4a²/b ≤ W` then
`y₀ + 4√y₁ ≤ W/a + 4a/b`, with equality only at `y = (W/a - 4a/b, 4a²/b²)`; (ii) if
`W < 4a²/b` then `y₀ + 4√y₁ ≤ 4√(W/b)`, with equality only at `y = (0, W/b)`. -/
theorem ql_bound {a b W y₀ y₁ : ℝ} (ha : 0 < a) (hb : 0 < b) (hy₀ : 0 ≤ y₀) (hy₁ : 0 ≤ y₁)
    (hbud : a * y₀ + b * y₁ ≤ W) :
    (4 * a ^ 2 / b ≤ W → y₀ + 4 * Real.sqrt y₁ ≤ W / a + 4 * a / b ∧
      (y₀ + 4 * Real.sqrt y₁ = W / a + 4 * a / b →
        y₀ = W / a - 4 * a / b ∧ y₁ = 4 * a ^ 2 / b ^ 2)) ∧
    (W < 4 * a ^ 2 / b → y₀ + 4 * Real.sqrt y₁ ≤ 4 * Real.sqrt (W / b) ∧
      (y₀ + 4 * Real.sqrt y₁ = 4 * Real.sqrt (W / b) → y₀ = 0 ∧ y₁ = W / b)) := by
  set s := Real.sqrt y₁ with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hss : s ^ 2 = y₁ := Real.sq_sqrt hy₁
  have hy0b : y₀ ≤ (W - b * s ^ 2) / a := by
    rw [le_div_iff₀ ha, hss]
    linarith
  constructor
  · intro _
    have hgap : W / a + 4 * a / b - ((W - b * s ^ 2) / a + 4 * s) =
        b / a * (s - 2 * a / b) ^ 2 := by
      field_simp
      ring
    have hnn : 0 ≤ b / a * (s - 2 * a / b) ^ 2 := by positivity
    refine ⟨by linarith, fun heq => ?_⟩
    have hsq : b / a * (s - 2 * a / b) ^ 2 = 0 := by linarith
    have hs' : s = 2 * a / b := by
      have : (s - 2 * a / b) ^ 2 = 0 := by
        rcases mul_eq_zero.mp hsq with h | h
        · exact absurd h (div_pos hb ha).ne'
        · exact h
      linarith [pow_eq_zero_iff (n := 2) (two_ne_zero) |>.mp this]
    have hy1 : y₁ = 4 * a ^ 2 / b ^ 2 := by
      rw [← hss, hs']
      ring
    refine ⟨?_, hy1⟩
    have h1 : y₀ = (W - b * s ^ 2) / a := by linarith
    rw [h1, hs']
    field_simp
    ring
  · intro hW
    set t := Real.sqrt (W / b) with ht
    have hWb : 0 ≤ W / b := by
      have : 0 ≤ b * y₁ := mul_nonneg hb.le hy₁
      exact div_nonneg (by nlinarith) hb.le
    have htt : t ^ 2 = W / b := Real.sq_sqrt hWb
    have ht0 : 0 ≤ t := Real.sqrt_nonneg _
    have hst : s ≤ t := by
      rw [hs, ht]
      apply Real.sqrt_le_sqrt
      rw [le_div_iff₀ hb]
      nlinarith
    have htlt : t < 2 * a / b := by
      have h1 : t ^ 2 < (2 * a / b) ^ 2 := by
        rw [htt, div_pow, div_lt_div_iff₀ hb (by positivity)]
        rw [lt_div_iff₀ hb] at hW
        nlinarith
      exact lt_of_pow_lt_pow_left₀ 2 (by positivity) h1
    have hWt : W = b * t ^ 2 := by rw [htt]; field_simp
    have hgap : 4 * t - ((W - b * s ^ 2) / a + 4 * s) = (t - s) * (4 - b / a * (t + s)) := by
      rw [hWt]
      field_simp
      ring
    have hfac : 0 < 4 - b / a * (t + s) := by
      have : b / a * (t + s) < b / a * (4 * a / b) := by
        apply mul_lt_mul_of_pos_left _ (div_pos hb ha)
        have : 4 * a / b = 2 * (2 * a / b) := by ring
        linarith
      have e : b / a * (4 * a / b) = 4 := by field_simp
      linarith
    have hnn : 0 ≤ (t - s) * (4 - b / a * (t + s)) := mul_nonneg (by linarith) hfac.le
    refine ⟨by linarith, fun heq => ?_⟩
    have h0 : (t - s) * (4 - b / a * (t + s)) = 0 := by linarith
    have hst' : s = t := by
      rcases mul_eq_zero.mp h0 with h | h
      · linarith
      · linarith
    have hy1 : y₁ = W / b := by rw [← hss, hst', htt]
    refine ⟨?_, hy1⟩
    have h1 : y₀ ≤ (W - b * s ^ 2) / a := hy0b
    rw [hst', htt] at h1
    have : (W - b * (W / b)) / a = 0 := by field_simp; ring
    linarith

/-- Consumer 1 of Exercise 4.C.11: `u₁(x) = x₁ + 4√x₂`. -/
noncomputable def ql1 (x : Fin 2 → ℝ) : ℝ := x 0 + 4 * Real.sqrt (x 1)

/-- Consumer 2 of Exercise 4.C.11: `u₂(x) = 4√x₁ + x₂`. -/
noncomputable def ql2 (x : Fin 2 → ℝ) : ℝ := 4 * Real.sqrt (x 0) + x 1

/-- **Exercise 4.C.11(a)** (MWG, p. 124), consumer 1. With wealth `W`: if `W ≥ 4p₁²/p₂`, demand is
`(W/p₁ - 4p₁/p₂, 4p₁²/p₂²)`; if `W < 4p₁²/p₂`, demand is `(0, W/p₂)`. -/
theorem exercise_4_C_11a_consumer1 {p : Fin 2 → ℝ} (hp : StrictlyPositive p) {W : ℝ} :
    (4 * p 0 ^ 2 / p 1 ≤ W → walrasianDemand ql1 p W =
      {![W / p 0 - 4 * p 0 / p 1, 4 * p 0 ^ 2 / p 1 ^ 2]}) ∧
    (0 ≤ W → W < 4 * p 0 ^ 2 / p 1 → walrasianDemand ql1 p W = {![0, W / p 1]}) := by
  have ha := hp 0
  have hb := hp 1
  constructor
  · intro hW
    have hy0 : 0 ≤ W / p 0 - 4 * p 0 / p 1 := by
      rw [sub_nonneg, div_le_div_iff₀ hb ha]
      rw [div_le_iff₀ hb] at hW
      nlinarith
    have hstar : ![W / p 0 - 4 * p 0 / p 1, 4 * p 0 ^ 2 / p 1 ^ 2] ∈ budgetSet p W := by
      refine ⟨fun l => ?_, ?_⟩
      · fin_cases l
        · simpa using hy0
        · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
          positivity
      · rw [dotProduct_two]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
        apply le_of_eq
        field_simp
        ring
    have hval : ql1 ![W / p 0 - 4 * p 0 / p 1, 4 * p 0 ^ 2 / p 1 ^ 2] =
        W / p 0 + 4 * p 0 / p 1 := by
      simp only [ql1, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      have : Real.sqrt (4 * p 0 ^ 2 / p 1 ^ 2) = 2 * p 0 / p 1 := by
        rw [show 4 * p 0 ^ 2 / p 1 ^ 2 = (2 * p 0 / p 1) ^ 2 by ring]
        exact Real.sqrt_sq (by positivity)
      rw [this]
      ring
    ext z
    constructor
    · intro hz
      have hb' := ql_bound (W := W) ha hb (hz.1.1 0) (hz.1.1 1)
        (by rw [← dotProduct_two]; exact hz.1.2)
      have hge := hz.2 _ hstar
      rw [hval] at hge
      obtain ⟨hle, heq⟩ := hb'.1 hW
      obtain ⟨e0, e1⟩ := heq (le_antisymm hle hge)
      funext l
      fin_cases l
      · simpa using e0
      · simpa using e1
    · rintro rfl
      refine ⟨hstar, fun y hy => ?_⟩
      rw [hval]
      exact ((ql_bound (W := W) ha hb (hy.1 0) (hy.1 1)
        (by rw [← dotProduct_two]; exact hy.2)).1 hW).1
  · intro hW0 hW
    have hstar : ![0, W / p 1] ∈ budgetSet p W := by
      refine ⟨fun l => ?_, ?_⟩
      · fin_cases l
        · simp
        · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
          positivity
      · rw [dotProduct_two]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
        apply le_of_eq
        field_simp
        ring
    have hval : ql1 ![0, W / p 1] = 4 * Real.sqrt (W / p 1) := by simp [ql1]
    ext z
    constructor
    · intro hz
      have hb' := ql_bound (W := W) ha hb (hz.1.1 0) (hz.1.1 1)
        (by rw [← dotProduct_two]; exact hz.1.2)
      have hge := hz.2 _ hstar
      rw [hval] at hge
      obtain ⟨hle, heq⟩ := hb'.2 hW
      obtain ⟨e0, e1⟩ := heq (le_antisymm hle hge)
      funext l
      fin_cases l
      · simpa using e0
      · simpa using e1
    · rintro rfl
      refine ⟨hstar, fun y hy => ?_⟩
      rw [hval]
      exact ((ql_bound (W := W) ha hb (hy.1 0) (hy.1 1)
        (by rw [← dotProduct_two]; exact hy.2)).2 hW).1

/-- Swapping the two goods. -/
def swap2 (x : Fin 2 → ℝ) : Fin 2 → ℝ := ![x 1, x 0]

/-- **Exercise 4.C.11(a)** (MWG, p. 124), consumer 2 (the mirror image of consumer 1). With
wealth `W`: if `W ≥ 4p₂²/p₁`, demand is `(4p₂²/p₁², W/p₂ - 4p₂/p₁)`; if `W < 4p₂²/p₁`, demand
is `(W/p₁, 0)`. -/
theorem exercise_4_C_11a_consumer2 {p : Fin 2 → ℝ} (hp : StrictlyPositive p) {W : ℝ} :
    (4 * p 1 ^ 2 / p 0 ≤ W → walrasianDemand ql2 p W =
      {![4 * p 1 ^ 2 / p 0 ^ 2, W / p 1 - 4 * p 1 / p 0]}) ∧
    (0 ≤ W → W < 4 * p 1 ^ 2 / p 0 → walrasianDemand ql2 p W = {![W / p 0, 0]}) := by
  have hq : StrictlyPositive (swap2 p) := by
    intro l; fin_cases l
    · exact hp 1
    · exact hp 0
  have hmap : ∀ z, z ∈ walrasianDemand ql2 p W ↔ swap2 z ∈ walrasianDemand ql1 (swap2 p) W := by
    intro z
    have hsw : ∀ y : Fin 2 → ℝ, swap2 (swap2 y) = y := by
      intro y; funext l; fin_cases l <;> rfl
    have hdot : ∀ y : Fin 2 → ℝ, swap2 p ⬝ᵥ swap2 y = p ⬝ᵥ y := by
      intro y; simp only [swap2, dotProduct_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one]; ring
    have hu : ∀ y : Fin 2 → ℝ, ql1 (swap2 y) = ql2 y := by
      intro y; simp [ql1, ql2, swap2]; ring
    have hnn : ∀ y : Fin 2 → ℝ, swap2 y ∈ nonnegOrthant 2 ↔ y ∈ nonnegOrthant 2 := by
      intro y
      constructor
      · intro h l; fin_cases l
        · exact h 1
        · exact h 0
      · intro h l; fin_cases l
        · exact h 1
        · exact h 0
    constructor
    · rintro ⟨⟨h0, hb⟩, hmax⟩
      refine ⟨⟨(hnn z).mpr h0, by rw [hdot]; exact hb⟩, fun y hy => ?_⟩
      have hy' : swap2 y ∈ budgetSet p W :=
        ⟨(hnn y).mpr hy.1, by rw [← hdot, hsw]; exact hy.2⟩
      have := hmax (swap2 y) hy'
      rw [← hu (swap2 y), hsw, ← hu z] at this
      exact this
    · rintro ⟨⟨h0, hb⟩, hmax⟩
      refine ⟨⟨(hnn z).mp h0, by rw [← hdot]; exact hb⟩, fun y hy => ?_⟩
      have := hmax (swap2 y) ⟨(hnn y).mpr hy.1, by rw [hdot]; exact hy.2⟩
      rwa [hu, hu] at this
  have hset : ∀ (S : Set (Fin 2 → ℝ)) (c : Fin 2 → ℝ), walrasianDemand ql1 (swap2 p) W = {c} →
      walrasianDemand ql2 p W = {swap2 c} := by
    intro S c h
    ext z
    rw [hmap, h, Set.mem_singleton_iff, Set.mem_singleton_iff]
    constructor
    · intro hz; rw [← hz]; funext l; fin_cases l <;> rfl
    · intro hz; rw [hz]; funext l; fin_cases l <;> rfl
  have h1 := exercise_4_C_11a_consumer1 hq (W := W)
  simp only [swap2, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at h1
  refine ⟨fun hW => ?_, fun hW0 hW => ?_⟩
  · have := hset ∅ _ (h1.1 hW)
    rw [this]
    congr 1
  · have := hset ∅ _ (h1.2 hW0 hW)
    rw [this]
    congr 1

/-- **Exercise 4.C.11(a)** (MWG, p. 124), aggregate demand. With equal wealths `w/2`, where both
consumers are interior (`w/2 ≥ 4p₁²/p₂` and `w/2 ≥ 4p₂²/p₁`), aggregate demand is
`x(p, w) = (w/(2p₁) - 4p₁/p₂ + 4p₂²/p₁², 4p₁²/p₂² + w/(2p₂) - 4p₂/p₁)`. -/
theorem exercise_4_C_11a {x1 x2 : DemandFunction 2}
    (hx1 : ∀ p w, PWDomain p w → x1 p w ∈ walrasianDemand ql1 p w)
    (hx2 : ∀ p w, PWDomain p w → x2 p w ∈ walrasianDemand ql2 p w) {p : Fin 2 → ℝ} {w : ℝ}
    (hd : PWDomain p w) (h1 : 4 * p 0 ^ 2 / p 1 ≤ w / 2) (h2 : 4 * p 1 ^ 2 / p 0 ≤ w / 2) :
    shareDemand ![x1, x2] ![1 / 2, 1 / 2] p w =
      ![w / (2 * p 0) - 4 * p 0 / p 1 + 4 * p 1 ^ 2 / p 0 ^ 2,
        4 * p 0 ^ 2 / p 1 ^ 2 + w / (2 * p 1) - 4 * p 1 / p 0] := by
  have hdW : PWDomain p (1 / 2 * w) := ⟨hd.1, by linarith [hd.2]⟩
  have e1 := hx1 p _ hdW
  have e2 := hx2 p _ hdW
  rw [(exercise_4_C_11a_consumer1 hd.1).1 (by linarith)] at e1
  rw [(exercise_4_C_11a_consumer2 hd.1).1 (by linarith)] at e2
  simp only [shareDemand, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  rw [Set.mem_singleton_iff.mp e1, Set.mem_singleton_iff.mp e2]
  have := hd.1 0
  have := hd.1 1
  funext l
  fin_cases l
  · simp only [Fin.zero_eta, Matrix.cons_val_zero, Pi.add_apply]
    field_simp
  · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.add_apply]
    field_simp
    ring

/-- **Exercise 4.C.11(c)** (MWG, p. 125). At `p = (1, 1)` and `w > 8` both consumers are interior;
their wealth effects are `(1, 0)` and `(0, 1)` and the matrix `C(p, w)` of (4.C.8) has quadratic
form `v·C v = (w - 16)(v₁ - v₂)²/4`. Hence `C` is positive semidefinite iff `w ≥ 16`; for
`8 < w < 16` it is negative semidefinite and `dp·C dp < 0` at `dp = (1, -1)`. (The book's
conclusion that `C` psd is not necessary for the weak axiom is
`exercise_4_C_11c_conclusion`.) -/
theorem exercise_4_C_11c {x1 x2 : DemandFunction 2}
    (hx1 : ∀ p w, PWDomain p w → x1 p w ∈ walrasianDemand ql1 p w)
    (hx2 : ∀ p w, PWDomain p w → x2 p w ∈ walrasianDemand ql2 p w) {w : ℝ} (hw : 8 < w) :
    ∃ D1 D2 : ((Fin 2 → ℝ) × ℝ) →L[ℝ] (Fin 2 → ℝ),
      HasFDerivAt (Function.uncurry x1) D1 (![1, 1], 1 / 2 * w) ∧
      HasFDerivAt (Function.uncurry x2) D2 (![1, 1], 1 / 2 * w) ∧
      (∀ v : Fin 2 → ℝ, v ⬝ᵥ Matrix.mulVec (covMatrix ![1 / 2, 1 / 2]
        ![wealthJacobian D1, wealthJacobian D2] ![x1 ![1, 1] (1 / 2 * w),
          x2 ![1, 1] (1 / 2 * w)]) v = (w - 16) * (v 0 - v 1) ^ 2 / 4) ∧
      (PosSemidefMWG (covMatrix ![1 / 2, 1 / 2] ![wealthJacobian D1, wealthJacobian D2]
        ![x1 ![1, 1] (1 / 2 * w), x2 ![1, 1] (1 / 2 * w)]) ↔ 16 ≤ w) := by
  set pb : Fin 2 → ℝ := ![1, 1] with hpb
  have hpbpos : StrictlyPositive pb := by intro l; fin_cases l <;> simp [pb]
  -- near `(p̄, w/2)` both demands are given by the interior formulas
  set F1 : (Fin 2 → ℝ) × ℝ → Fin 2 → ℝ :=
    fun q => ![q.2 / q.1 0 - 4 * q.1 0 / q.1 1, 4 * q.1 0 ^ 2 / q.1 1 ^ 2] with hF1
  set F2 : (Fin 2 → ℝ) × ℝ → Fin 2 → ℝ :=
    fun q => ![4 * q.1 1 ^ 2 / q.1 0 ^ 2, q.2 / q.1 1 - 4 * q.1 1 / q.1 0] with hF2
  have hopen : ∀ᶠ q in 𝓝 ((pb, 1 / 2 * w) : (Fin 2 → ℝ) × ℝ),
      PWDomain q.1 q.2 ∧ 4 * q.1 0 ^ 2 / q.1 1 < q.2 ∧ 4 * q.1 1 ^ 2 / q.1 0 < q.2 := by
    have hc1 : ContinuousAt (fun q : (Fin 2 → ℝ) × ℝ => q.2 - 4 * q.1 0 ^ 2 / q.1 1)
        (pb, 1 / 2 * w) := by
      apply ContinuousAt.sub (by fun_prop)
      apply ContinuousAt.div (by fun_prop) (by fun_prop)
      simp [pb]
    have hc2 : ContinuousAt (fun q : (Fin 2 → ℝ) × ℝ => q.2 - 4 * q.1 1 ^ 2 / q.1 0)
        (pb, 1 / 2 * w) := by
      apply ContinuousAt.sub (by fun_prop)
      apply ContinuousAt.div (by fun_prop) (by fun_prop)
      simp [pb]
    have h1 := hc1.eventually (lt_mem_nhds (show (0 : ℝ) < _ by simp [pb]; linarith))
    have h2 := hc2.eventually (lt_mem_nhds (show (0 : ℝ) < _ by simp [pb]; linarith))
    filter_upwards [(isOpen_pwDomain 2).mem_nhds (show PWDomain pb (1 / 2 * w) from
      ⟨hpbpos, by linarith⟩), h1, h2] with q hq hq1 hq2
    exact ⟨hq, by linarith, by linarith⟩
  have hev1 : Function.uncurry x1 =ᶠ[𝓝 (pb, 1 / 2 * w)] F1 := by
    filter_upwards [hopen] with q hq
    have := hx1 q.1 q.2 hq.1
    rw [(exercise_4_C_11a_consumer1 hq.1.1).1 hq.2.1.le] at this
    exact this
  have hev2 : Function.uncurry x2 =ᶠ[𝓝 (pb, 1 / 2 * w)] F2 := by
    filter_upwards [hopen] with q hq
    have := hx2 q.1 q.2 hq.1
    rw [(exercise_4_C_11a_consumer2 hq.1.1).1 hq.2.2.le] at this
    exact this
  have hdF1 : DifferentiableAt ℝ F1 (pb, 1 / 2 * w) := by
    simp only [F1]
    refine differentiableAt_pi.mpr fun l => ?_
    fin_cases l <;>
      simp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one] <;>
      fun_prop (disch := simp [pb])
  have hdF2 : DifferentiableAt ℝ F2 (pb, 1 / 2 * w) := by
    simp only [F2]
    refine differentiableAt_pi.mpr fun l => ?_
    fin_cases l <;>
      simp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one] <;>
      fun_prop (disch := simp [pb])
  have hD1 := hdF1.hasFDerivAt.congr_of_eventuallyEq hev1
  have hD2 := hdF2.hasFDerivAt.congr_of_eventuallyEq hev2
  -- wealth effects `(1, 0)` and `(0, 1)`
  have hwe : ∀ (F : (Fin 2 → ℝ) × ℝ → Fin 2 → ℝ) (D : ((Fin 2 → ℝ) × ℝ) →L[ℝ] (Fin 2 → ℝ))
      (g : ℝ → Fin 2 → ℝ) (d : Fin 2 → ℝ), HasFDerivAt F D (pb, 1 / 2 * w) →
      (∀ t, F (pb, 1 / 2 * w + t) = g t) → HasDerivAt g d 0 → wealthJacobian D = d := by
    intro F D g d hF hg hgd
    have hl : HasDerivAt (fun t : ℝ => ((pb, 1 / 2 * w + t) : (Fin 2 → ℝ) × ℝ))
        ((0 : Fin 2 → ℝ), (1 : ℝ)) 0 :=
      (hasDerivAt_const 0 pb).prodMk ((hasDerivAt_id 0).const_add _)
    have := hF.comp_hasDerivAt_of_eq 0 hl (by simp)
    simp only [Function.comp_def, hg] at this
    exact funext fun l => congrFun (this.unique hgd) l
  have hw1 : wealthJacobian (fderiv ℝ F1 (pb, 1 / 2 * w)) = ![1, 0] := by
    apply hwe F1 _ (fun t => ![1 / 2 * w + t - 4, 4]) _ hdF1.hasFDerivAt
    · intro t; simp [F1, pb]
    · refine hasDerivAt_pi.mpr fun l => ?_
      fin_cases l
      · simpa using ((hasDerivAt_id (0 : ℝ)).const_add (1 / 2 * w)).sub_const 4
      · simpa using hasDerivAt_const (0 : ℝ) (4 : ℝ)
  have hw2 : wealthJacobian (fderiv ℝ F2 (pb, 1 / 2 * w)) = ![0, 1] := by
    apply hwe F2 _ (fun t => ![4, 1 / 2 * w + t - 4]) _ hdF2.hasFDerivAt
    · intro t; simp [F2, pb]
    · refine hasDerivAt_pi.mpr fun l => ?_
      fin_cases l
      · simpa using hasDerivAt_const (0 : ℝ) (4 : ℝ)
      · simpa using ((hasDerivAt_id (0 : ℝ)).const_add (1 / 2 * w)).sub_const 4
  have hx1v : x1 pb (1 / 2 * w) = ![1 / 2 * w - 4, 4] := by
    have := hev1.eq_of_nhds
    simp only [Function.uncurry] at this
    rw [this]
    simp [F1, pb]
  have hx2v : x2 pb (1 / 2 * w) = ![4, 1 / 2 * w - 4] := by
    have := hev2.eq_of_nhds
    simp only [Function.uncurry] at this
    rw [this]
    simp [F2, pb]
  have hquad : ∀ v : Fin 2 → ℝ, v ⬝ᵥ Matrix.mulVec (covMatrix ![1 / 2, 1 / 2]
      ![wealthJacobian (fderiv ℝ F1 (pb, 1 / 2 * w)),
        wealthJacobian (fderiv ℝ F2 (pb, 1 / 2 * w))]
      ![x1 pb (1 / 2 * w), x2 pb (1 / 2 * w)]) v = (w - 16) * (v 0 - v 1) ^ 2 / 4 := by
    intro v
    rw [hw1, hw2, hx1v, hx2v]
    simp only [covMatrix, Fin.sum_univ_two, Matrix.add_mulVec, Matrix.smul_mulVec,
      dotProduct_add, dotProduct_smul, smul_eq_mul, dot_vecMulVec_mulVec]
    simp [Matrix.vecHead, Matrix.vecTail]
    ring
  refine ⟨_, _, hD1, hD2, hquad, ?_⟩
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    have := h ![1, -1]
    rw [hquad] at this
    norm_num at this
    nlinarith
  · intro h v
    rw [hquad]
    have := sq_nonneg (v 0 - v 1)
    have : 0 ≤ w - 16 := by linarith
    positivity

end MWG.AggregateDemand
