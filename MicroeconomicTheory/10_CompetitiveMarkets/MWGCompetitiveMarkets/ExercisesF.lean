/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGCompetitiveMarkets.FreeEntry
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Exercises 10.F.2-10.F.4 (MWG, pp. 347-348)

* The quadratic cost with a fixed cost, `c(q) = K + αq + βq²` (`q > 0`), `c(0) = 0`: efficient
  scale `q̄ = √(K/β)`, minimum average cost `c̄ = α + 2√(Kβ)` (`quadLumpy_efficientScale`).
* `lr_efficientScale_real`: Definition 10.F.1 ignoring the integer constraint.
* **Exercise 10.F.2**: (a) the long-run equilibrium with demand `A - Bp` and its dependence on
  `A`; (b) the short-run response to `A` (fixed cost sunk), whose derivative tends to `0` as
  `A → ∞`.
* **Exercise 10.F.3** (Pearce): as printed (`φ'' < 0`) the cost `K + φ(q)` has no efficient
  scale (correction); with `φ'' > 0`, the ad valorem tax leads to a higher price and the lump-sum
  tax to larger firms; the ad valorem tax raises more revenue with inelastic demand, but not in
  general (an explicit example where the lump-sum tax raises more).
* **Exercise 10.F.4** (Panzer): the long-run price `p*(w) = min_q c(w, q)/q` is nondecreasing,
  homogeneous of degree one and concave in `w`.
-/

namespace MWG.CompetitiveMarkets

open Filter Topology

/-- **Definition 10.F.1** ignoring the integer constraint: the efficient-scale characterization
(MWG, pp. 337-338) with a real number of firms. -/
theorem lr_efficientScale_real {x c : ℝ → ℝ} {qb : ℝ} (hc0 : c 0 = 0)
    (hqb : IsEfficientScale c qb) (huniq : ∀ q, 0 < q → c q / q = c qb / qb → q = qb)
    (hx : 0 < x (c qb / qb)) (hmono : AntitoneOn x (Set.Iic (c qb / qb))) {p q J : ℝ} :
    IsLREqmReal x c p q J ↔ p = c qb / qb ∧ q = qb ∧ J = x (c qb / qb) / qb := by
  set cb := c qb / qb with hcb
  have hqb0 := hqb.1
  have hcbq : c qb = cb * qb := by rw [hcb]; field_simp
  constructor
  · rintro ⟨hJ, ⟨hq, hmax⟩, hxp, hz⟩
    have hp1 : p ≤ cb := by
      by_contra hlt; push Not at hlt
      have := hmax qb hqb0.le; nlinarith
    have hp2 : cb ≤ p := by
      by_contra hlt; push Not at hlt
      have hq0 : q = 0 := by
        by_contra hne
        have hq' : 0 < q := lt_of_le_of_ne hq (Ne.symm hne)
        have := hqb.le_cost hc0 hq; nlinarith
      rw [hq0, mul_zero] at hxp
      have := hmono (Set.mem_Iic.2 hlt.le) (Set.mem_Iic.2 le_rfl) hlt.le
      linarith
    have hpeq : p = cb := le_antisymm hp1 hp2
    subst hpeq
    have hq0 : 0 < q := by rw [hxp] at hx; exact pos_of_mul_pos_right hx hJ
    have hAC : c q / q = cb := by rw [div_eq_iff hq0.ne']; linarith
    have := huniq q hq0 hAC
    subst this
    refine ⟨rfl, rfl, ?_⟩
    rw [hxp]; field_simp
  · rintro ⟨rfl, rfl, rfl⟩
    refine ⟨div_nonneg hx.le hqb0.le, ⟨hqb0.le, fun q' hq' => ?_⟩, by field_simp, by
      rw [hcbq]; ring⟩
    have := hqb.le_cost hc0 hq'
    rw [hcbq]
    nlinarith

/-! ## The quadratic cost with a fixed cost -/

/-- `c(q) = K + αq + βq²` for `q > 0`, `c(0) = 0` (Exercise 10.F.2). -/
noncomputable def quadLumpyCost (K α β : ℝ) : ℝ → ℝ :=
  lumpyCost K fun q => α * q + β * q ^ 2

/-- With `K = βs²` (`s > 0`), the average cost is `βs²/q + α + βq`, minimized uniquely at
`q̄ = s` with `c̄ = α + 2βs`. -/
theorem quadLumpy_efficientScale {α β s : ℝ} (hβ : 0 < β) (hs : 0 < s) :
    IsEfficientScale (quadLumpyCost (β * s ^ 2) α β) s ∧
      quadLumpyCost (β * s ^ 2) α β s / s = α + 2 * β * s ∧
      ∀ q, 0 < q → quadLumpyCost (β * s ^ 2) α β q / q =
        quadLumpyCost (β * s ^ 2) α β s / s → q = s := by
  have hAC : ∀ q, 0 < q → quadLumpyCost (β * s ^ 2) α β q / q =
      α + 2 * β * s + β * (q - s) ^ 2 / q := by
    intro q hq
    simp only [quadLumpyCost, lumpyCost, hq.ne', ↓reduceIte]
    field_simp
    ring
  have hcb := hAC s hs
  simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    zero_div, add_zero] at hcb
  refine ⟨⟨hs, fun q hq => ?_⟩, hcb, fun q hq heq => ?_⟩
  · rw [hcb, hAC q hq]
    have : 0 ≤ β * (q - s) ^ 2 / q := by positivity
    linarith
  · rw [hcb, hAC q hq] at heq
    have h1 : β * (q - s) ^ 2 / q = 0 := by linarith
    rcases div_eq_zero_iff.1 h1 with h | h
    · rcases mul_eq_zero.1 h with h' | h'
      · exact absurd h' hβ.ne'
      · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h'; linarith
    · exact absurd h hq.ne'

/-- In the book's parameters: `q̄ = √(K/β)` and `c̄ = α + 2√(Kβ)`. -/
theorem quadLumpy_book {K β : ℝ} (hK : 0 < K) (hβ : 0 < β) :
    β * Real.sqrt (K / β) ^ 2 = K ∧ 2 * β * Real.sqrt (K / β) = 2 * Real.sqrt (K * β) := by
  have hs : 0 ≤ K / β := by positivity
  refine ⟨by rw [Real.sq_sqrt hs]; field_simp, ?_⟩
  have : β * Real.sqrt (K / β) = Real.sqrt (K * β) := by
    rw [show K * β = (β * Real.sqrt (K / β)) ^ 2 by rw [mul_pow, Real.sq_sqrt hs]; field_simp]
    exact (Real.sqrt_sq (by positivity)).symm
  rw [mul_assoc, this]

/-- **Exercise 10.F.2(a)** (MWG, p. 347). With demand `x(p) = A - Bp` (`B > 0`) and cost
`K + αq + βq²` (`K = βs²`, so `s = √(K/β)`), if `A > B c̄` the long-run equilibrium (ignoring
the integer constraint) is `p* = c̄ = α + 2βs`, `q* = s`, aggregate output `A - Bc̄` and
`J* = (A - Bc̄)/s`. Price and firm size do not depend on `A`; output and the number of firms
increase with `A` (at rates `1` and `1/s`). -/
theorem exercise_10_F_2a {A B α β s : ℝ} (hB : 0 < B) (hβ : 0 < β) (hs : 0 < s)
    (hA : B * (α + 2 * β * s) < A) {p q J : ℝ} :
    IsLREqmReal (fun p => A - B * p) (quadLumpyCost (β * s ^ 2) α β) p q J ↔
      p = α + 2 * β * s ∧ q = s ∧ J = (A - B * (α + 2 * β * s)) / s := by
  obtain ⟨hqb, hcb, huniq⟩ := quadLumpy_efficientScale (α := α) hβ hs
  have hc0 : quadLumpyCost (β * s ^ 2) α β 0 = 0 := by simp [quadLumpyCost, lumpyCost]
  rw [lr_efficientScale_real hc0 hqb huniq (by rw [hcb]; linarith)
    (fun a _ b _ hab => by nlinarith), hcb]

/-- **Exercise 10.F.2(a)**: the comparative statics in `A`. -/
theorem exercise_10_F_2a_statics {B α β s : ℝ} (hs : 0 < s) (A : ℝ) :
    HasDerivAt (fun A => A - B * (α + 2 * β * s)) 1 A ∧
      HasDerivAt (fun A => (A - B * (α + 2 * β * s)) / s) (1 / s) A ∧ 0 < 1 / s :=
  ⟨by simpa using (hasDerivAt_id A).sub_const (B * (α + 2 * β * s)),
    by simpa using ((hasDerivAt_id A).sub_const (B * (α + 2 * β * s))).div_const s,
    by positivity⟩

/-- **Exercise 10.F.2(b)** (MWG, p. 347): short-run supply. With the fixed cost sunk, a firm's
short-run profit `pq - K - αq - βq²` is maximized at `q = (p - α)/(2β)` for `p ≥ α`. -/
theorem exercise_10_F_2b_supply {K α β p : ℝ} (hβ : 0 < β) (hp : α ≤ p) (q : ℝ) :
    0 ≤ (p - α) / (2 * β) ∧ p * q - (K + α * q + β * q ^ 2) ≤
      p * ((p - α) / (2 * β)) - (K + α * ((p - α) / (2 * β)) + β * ((p - α) / (2 * β)) ^ 2) := by
  refine ⟨div_nonneg (by linarith) (by positivity), ?_⟩
  have : p * ((p - α) / (2 * β)) - (K + α * ((p - α) / (2 * β)) + β * ((p - α) / (2 * β)) ^ 2) -
      (p * q - (K + α * q + β * q ^ 2)) = β * (q - (p - α) / (2 * β)) ^ 2 := by
    field_simp; ring
  nlinarith [sq_nonneg (q - (p - α) / (2 * β))]

/-- **Exercise 10.F.2(b)** (MWG, p. 347). With `J` firms fixed, the short-run equilibrium price
for demand `A' - Bp` is `pₛ(A') = (A' + Jα/(2β))/(B + J/(2β))`, with
`dpₛ/dA' = 1/(B + J/(2β))`. -/
theorem exercise_10_F_2b {B α β J A' : ℝ} (hB : 0 < B) (hβ : 0 < β) (hJ : 0 ≤ J) :
    A' - B * ((A' + J * α / (2 * β)) / (B + J / (2 * β))) =
        J * (((A' + J * α / (2 * β)) / (B + J / (2 * β)) - α) / (2 * β)) ∧
      HasDerivAt (fun A' => (A' + J * α / (2 * β)) / (B + J / (2 * β)))
        (1 / (B + J / (2 * β))) A' := by
  have hden : 0 < B + J / (2 * β) := by
    have := div_nonneg hJ (by positivity : (0 : ℝ) ≤ 2 * β); linarith [hB]
  have hden' := hden.ne'
  refine ⟨by field_simp; ring, ?_⟩
  simpa using ((hasDerivAt_id A').add_const (J * α / (2 * β))).div_const (B + J / (2 * β))

/-- **Exercise 10.F.2(b)** (MWG, p. 347). Starting from the long-run equilibrium for `A`, the
short-run price response `1/(B + J*(A)/(2β))` (with `J*(A) = (A - Bc̄)/s`) tends to `0` as
`A → ∞`: in a larger market there are more firms and the short-run industry supply is flatter. -/
theorem exercise_10_F_2b_limit {B β s cb : ℝ} (hβ : 0 < β) (hs : 0 < s) :
    Tendsto (fun A => 1 / (B + (A - B * cb) / s / (2 * β))) atTop (𝓝 0) := by
  refine Tendsto.div_atTop tendsto_const_nhds ?_
  refine tendsto_atTop_add_const_left _ B ?_
  have h1 : Tendsto (fun A : ℝ => A - B * cb) atTop atTop := tendsto_atTop_add_const_right _ _
    tendsto_id
  have h2 := (h1.atTop_div_const hs).atTop_div_const (by positivity : (0 : ℝ) < 2 * β)
  exact h2

/-! ## Exercise 10.F.3 -/

/-- **Exercise 10.F.3, as printed** (MWG, p. 347; correction): with `φ'' < 0` there is no
efficient scale. If `φ` is concave on `q ≥ 0` with `φ(0) ≥ 0` and `K > 0`, average cost
`(K + φ(q))/q` strictly decreases from `q` to `2q`, so it has no minimizer. -/
theorem exercise_10_F_3_printed {K : ℝ} (hK : 0 < K) {φ : ℝ → ℝ}
    (hφ : ConcaveOn ℝ (Set.Ici 0) φ) (hφ0 : 0 ≤ φ 0) :
    ∀ qb, ¬ IsEfficientScale (lumpyCost K φ) qb := by
  rintro qb ⟨hqb, hmin⟩
  have h2 := hmin (2 * qb) (by positivity)
  have hconc := hφ.2 (Set.mem_Ici.2 (by positivity : (0 : ℝ) ≤ 2 * qb)) (Set.mem_Ici.2 le_rfl)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul, mul_zero, add_zero] at hconc
  have e : 1 / 2 * (2 * qb) = qb := by ring
  rw [e] at hconc
  simp only [lumpyCost, hqb.ne', (by positivity : (2 : ℝ) * qb ≠ 0), ↓reduceIte] at h2
  rw [div_le_div_iff₀ hqb (by positivity)] at h2
  nlinarith

/-- **Exercise 10.F.3** (MWG, p. 347): a lump-sum tax `T` per operating firm raises the fixed
cost to `K + T`; the efficient scale weakly increases (`q̄ ≤ q̄_T`), and the new minimum average
cost satisfies `c̄_T ≤ c̄ + T/q̄`. -/
theorem exercise_10_F_3_scale {K T : ℝ} (hT : 0 < T) {φ : ℝ → ℝ} {qb qT : ℝ}
    (h : IsEfficientScale (lumpyCost K φ) qb) (hT' : IsEfficientScale (lumpyCost (K + T) φ) qT) :
    qb ≤ qT ∧ lumpyCost (K + T) φ qT / qT ≤ lumpyCost K φ qb / qb + T / qb := by
  have hqb := h.1
  have hqT := hT'.1
  have e1 := h.2 qT hqT
  have e2 := hT'.2 qb hqb
  simp only [lumpyCost, hqb.ne', hqT.ne', ↓reduceIte] at e1 e2 ⊢
  have h1 : (K + T + φ qT) / qT = (K + φ qT) / qT + T / qT := by field_simp; ring
  have h2 : (K + T + φ qb) / qb = (K + φ qb) / qb + T / qb := by field_simp; ring
  refine ⟨?_, by rw [← h2]; exact e2⟩
  have hsum : T / qT ≤ T / qb := by
    rw [h1, h2] at e2
    linarith
  by_contra hlt
  push Not at hlt
  have : T / qb < T / qT := div_lt_div_of_pos_left hT hqT hlt
  linarith

/-- **Exercise 10.F.3** (MWG, pp. 347-348): prices. With equal initial revenue
`T = τ c̄ q̄` (`0 < τ < 1`), the long-run price under the lump-sum tax is at most `c̄(1 + τ)`,
strictly below the long-run price `c̄/(1 - τ)` under the ad valorem tax. -/
theorem exercise_10_F_3_prices {cb cT qb τ : ℝ} (hcb : 0 < cb) (hqb : 0 < qb) (hτ0 : 0 < τ)
    (hτ1 : τ < 1) (hle : cT ≤ cb + τ * cb * qb / qb) : cT < cb / (1 - τ) := by
  rw [mul_div_assoc, div_self hqb.ne', mul_one] at hle
  rw [lt_div_iff₀ (by linarith)]
  nlinarith [mul_le_mul_of_nonneg_right hle (by linarith : (0 : ℝ) ≤ 1 - τ),
    mul_pos hcb (mul_pos hτ0 hτ0)]

/-- **Exercise 10.F.3** (MWG, pp. 347-348): with perfectly inelastic demand `X > 0` the ad valorem
tax raises more revenue after the long-run adjustment: `T X/q̄_T < τ (c̄/(1 - τ)) X`. -/
theorem exercise_10_F_3_inelastic {cb qb qT τ X : ℝ} (hcb : 0 < cb) (hqb : 0 < qb)
    (hscale : qb ≤ qT) (hτ0 : 0 < τ) (hτ1 : τ < 1) (hX : 0 < X) :
    τ * cb * qb * (X / qT) < τ * (cb / (1 - τ)) * X := by
  have hqT : 0 < qT := hqb.trans_le hscale
  have h1 : τ * cb * qb * (X / qT) ≤ τ * cb * X := by
    rw [mul_div_assoc', div_le_iff₀ hqT]
    have : 0 ≤ τ * cb * X := by positivity
    nlinarith
  have h2 : τ * cb * X < τ * (cb / (1 - τ)) * X := by
    have : cb < cb / (1 - τ) := by rw [lt_div_iff₀ (by linarith)]; nlinarith
    have := mul_lt_mul_of_pos_left this hτ0
    nlinarith
  linarith

/-- **Exercise 10.F.3** (MWG, pp. 347-348): the ad valorem tax does not always raise more. With
`c(q) = 1 + q + q²` (`q̄ = 1`, `c̄ = 3`), `τ = 1/2`, `T = τ c̄ q̄ = 3/2` and demand
`x(p) = 61/10 - p`, the ad valorem long-run revenue is `τ (c̄/(1-τ)) x(c̄/(1-τ)) = 3/10`, while
the lump-sum long-run revenue `T x(c̄_T)/q̄_T` (with `q̄_T = √(5/2)`, `c̄_T = 1 + 2√(5/2)`)
exceeds `17/10`. -/
theorem exercise_10_F_3_counterexample :
    let x : ℝ → ℝ := fun p => 61 / 10 - p
    let sT := Real.sqrt (5 / 2)
    IsEfficientScale (quadLumpyCost (1 * 1 ^ 2) 1 1) 1 ∧
      quadLumpyCost (1 * 1 ^ 2) 1 1 1 / 1 = 3 ∧
      IsEfficientScale (quadLumpyCost (1 * sT ^ 2) 1 1) sT ∧
      quadLumpyCost (1 * sT ^ 2) 1 1 sT / sT = 1 + 2 * sT ∧
      1 * sT ^ 2 = 1 * 1 ^ 2 + 3 / 2 ∧
      1 / 2 * (3 / (1 - 1 / 2)) * x (3 / (1 - 1 / 2)) = 3 / 10 ∧
      17 / 10 < 3 / 2 * (x (1 + 2 * sT) / sT) := by
  intro x sT
  have hsT : sT ^ 2 = 5 / 2 := Real.sq_sqrt (by norm_num)
  have hsT0 : 0 < sT := Real.sqrt_pos.2 (by norm_num)
  have hsTlt : sT < 8 / 5 := by nlinarith
  obtain ⟨h1, h2, -⟩ := quadLumpy_efficientScale (α := 1) one_pos one_pos
  obtain ⟨h3, h4, -⟩ := quadLumpy_efficientScale (α := 1) one_pos hsT0
  refine ⟨h1, by rw [h2]; norm_num, h3, by rw [h4]; ring, by rw [hsT]; norm_num, by
    simp only [x]; norm_num, ?_⟩
  simp only [x]
  have key : 17 / 15 < (61 / 10 - (1 + 2 * sT)) / sT := by
    rw [lt_div_iff₀ hsT0]; nlinarith
  linarith

/-! ## Exercise 10.F.4 (Panzer) -/

/-- **Exercise 10.F.4** (MWG, p. 348). Let `p*(w) = min_{q>0} c(w, q)/q` be the long-run
equilibrium price (the minimum average cost, attained at the efficient scale `q̄(w) > 0`), where
for each `q` the cost `c(·, q)` is nondecreasing, homogeneous of degree one and concave in
`w ≫ 0` (Proposition 5.C.2(i)-(ii)). Then `p*` is nondecreasing, homogeneous of degree one and
concave. -/
theorem exercise_10_F_4 {n : ℕ} (c : (Fin n → ℝ) → ℝ → ℝ) (pstar qbar : (Fin n → ℝ) → ℝ)
    (S : Set (Fin n → ℝ)) (hS : Convex ℝ S) (hSs : ∀ w ∈ S, ∀ t : ℝ, 0 < t → t • w ∈ S)
    (hmono : ∀ q, 0 < q → ∀ w ∈ S, ∀ w' ∈ S, w ≤ w' → c w q ≤ c w' q)
    (hhom : ∀ q, 0 < q → ∀ w ∈ S, ∀ t : ℝ, 0 < t → c (t • w) q = t * c w q)
    (hconc : ∀ q, 0 < q → ConcaveOn ℝ S fun w => c w q)
    (hq : ∀ w ∈ S, 0 < qbar w) (hval : ∀ w ∈ S, pstar w = c w (qbar w) / qbar w)
    (hmin : ∀ w ∈ S, ∀ q, 0 < q → pstar w ≤ c w q / q) :
    (∀ w ∈ S, ∀ w' ∈ S, w ≤ w' → pstar w ≤ pstar w') ∧
    (∀ w ∈ S, ∀ t : ℝ, 0 < t → pstar (t • w) = t * pstar w) ∧ ConcaveOn ℝ S pstar := by
  refine ⟨fun w hw w' hw' hle => ?_, fun w hw t ht => ?_, ⟨hS, fun w hw w' hw' a b ha hb hab => ?_⟩⟩
  · rw [hval w' hw']
    exact (hmin w hw _ (hq w' hw')).trans
      (div_le_div_of_nonneg_right (hmono _ (hq w' hw') w hw w' hw' hle) (hq w' hw').le)
  · have htw := hSs w hw t ht
    apply le_antisymm
    · rw [hval w hw]
      have := hmin _ htw _ (hq w hw)
      rw [hhom _ (hq w hw) w hw t ht, mul_div_assoc] at this
      exact this
    · rw [hval _ htw]
      have := hmin w hw _ (hq _ htw)
      have e : c (t • w) (qbar (t • w)) / qbar (t • w) =
          t * (c w (qbar (t • w)) / qbar (t • w)) := by
        rw [hhom _ (hq _ htw) w hw t ht, mul_div_assoc]
      rw [e]
      exact mul_le_mul_of_nonneg_left this ht.le
  · have hmem : a • w + b • w' ∈ S := hS hw hw' ha hb hab
    set q := qbar (a • w + b • w')
    have hq0 : 0 < q := hq _ hmem
    have h1 := (hconc q hq0).2 hw hw' ha hb hab
    simp only [smul_eq_mul] at h1 ⊢
    rw [hval _ hmem]
    have e1 := hmin w hw q hq0
    have e2 := hmin w' hw' q hq0
    have : a * (c w q / q) + b * (c w' q / q) ≤ c (a • w + b • w') q / q := by
      rw [← mul_div_assoc, ← mul_div_assoc, ← add_div]
      exact div_le_div_of_nonneg_right h1 hq0.le
    nlinarith [mul_le_mul_of_nonneg_left e1 ha, mul_le_mul_of_nonneg_left e2 hb]

end MWG.CompetitiveMarkets
