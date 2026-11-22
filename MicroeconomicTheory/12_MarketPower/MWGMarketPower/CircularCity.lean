/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGMarketPower.CityModels
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Quadratic travel costs and the circular city

MWG, Exercise 12.C.15 (p. 433), the circular city of p. 399 (Salop, 1979), and Exercise 12.C.16.

**Exercise 12.C.15.** With total cost `p_j + td²`, a consumer at `z` prefers firm 1 iff
`z < ẑ = (t + p₂ − p₁)/(2t)`, exactly as with linear costs (`quadCity_prefers`), so firm 1's
demand is (12.C.8) (`quadCity_demand`) and the unique equilibrium is `p₁* = p₂* = c + t`
(`exercise_12_C_15`).

**The circular city.** `J` firms sit at equal intervals `1/J` on a circle of circumference 1 with
`M` consumers spread uniformly. Firm `j` charges `q`, all other firms `p`. With travel cost
`t·d` (linear) or `t·d²` (quadratic), a consumer between firm `j` and a neighbour at distance `x`
from `j` buys from `j` iff `x < x̂(q)` (`circLin_prefers`, `circQuad_prefers`), where
`x̂(q) = (p − q + w)/(2s)` with `(s, w) = (t, t/J)` (linear) or `(t/J, t/J²)` (quadratic). As long
as `q ≥ p − w`, consumers beyond a neighbour prefer that neighbour to firm `j`
(`circLin_beyond`, `circQuad_beyond`), so firm `j`'s demand is
`2M·max{0, min{1/J, x̂(q)}}` (`circDemand`). For lower prices only nonnegativity of demand is
used (the margin is then negative at the candidate equilibrium).

* `circ_symmetric_eqm`, `circ_symmetric_unique`: the symmetric equilibrium price is `c + w`, and
  no other symmetric profile is an equilibrium.
* `circularCity_linear`: with linear travel cost the equilibrium price is `c + t/J` and each firm
  earns `tM/J²` (the model of p. 399; MWG states no equilibrium there).
* `exercise_12_C_16`: with quadratic travel cost the equilibrium price is `c + t/J²` and each firm
  earns `tM/J³`; `exercise_12_C_16_limits`: as `J → ∞` the price tends to `c` and profits to `0`,
  and price and profit fall as `t` falls.
-/

namespace MWG.MarketPower

open Filter Topology

/-! ### Exercise 12.C.15 -/

/-- **Exercise 12.C.15** (MWG, p. 433). With quadratic travel cost a consumer at `z` strictly
prefers firm 1 iff `z < ẑ`, the same indifferent consumer (12.C.7) as with linear costs. -/
theorem quadCity_prefers {t p1 p2 z : ℝ} (ht : 0 < t) :
    p1 + t * z ^ 2 < p2 + t * (1 - z) ^ 2 ↔ z < lcHat t p1 p2 := by
  rw [← linearCity_prefers ht]
  constructor <;> intro h <;> nlinarith

/-- Firm 1's demand (12.C.8) is `M` times the length of the set of consumers buying from it. -/
theorem lcDemand_eq_share {t M p1 p2 : ℝ} (ht : 0 < t) :
    lcDemand t M p1 p2 = M * max 0 (min 1 (lcHat t p1 p2)) := by
  unfold lcDemand lcHat
  split_ifs with h1 h2
  · rw [max_eq_left (min_le_of_right_le (div_nonpos_of_nonpos_of_nonneg (by linarith)
      (by positivity)))]; ring
  · rw [min_eq_left (by rw [le_div_iff₀ (by positivity)]; linarith),
      max_eq_right zero_le_one, mul_one]
  · push Not at h1 h2
    rw [min_eq_right (by rw [div_le_one (by positivity)]; linarith),
      max_eq_right (div_nonneg (by linarith) (by positivity))]
    ring

/-- **Exercise 12.C.15** (MWG, p. 433). With quadratic travel cost (and `v` large enough that
everyone buys), firm 1's demand is `M` times the length of
`{z ∈ [0, 1] : p₁ + tz² < p₂ + t(1 − z)²}` and equals (12.C.8); hence `p₁* = p₂* = c + t` is
the unique Nash equilibrium, with profits `tM/2`. -/
theorem exercise_12_C_15 {t M c : ℝ} (ht : 0 < t) (hM : 0 < M) :
    (∀ p1 p2, lcDemand t M p1 p2 = M *
      (MeasureTheory.volume
        {z ∈ Set.Icc (0 : ℝ) 1 | p1 + t * z ^ 2 < p2 + t * (1 - z) ^ 2}).toReal) ∧
    IsLCNash t M c (c + t) (c + t) ∧ lcProfit t M c (c + t) (c + t) = t * M / 2 ∧
    ∀ p1 p2, IsLCNash t M c p1 p2 → p1 = c + t ∧ p2 = c + t := by
  refine ⟨fun p1 p2 => ?_, (example_12_C_2 ht hM).1, (example_12_C_2 ht hM).2.2.1,
    (example_12_C_2 ht hM).2.2.2⟩
  have hs : {z ∈ Set.Icc (0 : ℝ) 1 | p1 + t * z ^ 2 < p2 + t * (1 - z) ^ 2} =
      Set.Icc (0 : ℝ) 1 ∩ Set.Iio (lcHat t p1 p2) := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_Iio, quadCity_prefers ht]
  rw [hs, volume_unit_inter_Iio, ENNReal.toReal_ofReal (le_max_left _ _), lcDemand_eq_share ht]

/-! ### The circular city -/

/-- **The circular city** (MWG, p. 399), linear travel cost: a consumer at distance
`x` from firm `j` (charging `q`) on the arc to a neighbour (charging `p`, at distance `1/J`) buys
from `j` iff `x < (p − q + t/J)/(2t)`. -/
theorem circLin_prefers {t J p q x : ℝ} (ht : 0 < t) :
    q + t * x < p + t * (1 / J - x) ↔ x < (p - q + t / J) / (2 * t) := by
  rw [lt_div_iff₀ (by positivity)]
  have e : t * (1 / J - x) = t / J - t * x := by ring
  rw [e]
  constructor <;> intro h <;> linarith

/-- With linear travel cost and `q ≥ p − t/J`, a consumer beyond a neighbour (at distance `y ≥ 0`
past it) weakly prefers the neighbour to firm `j`. -/
theorem circLin_beyond {t J p q y : ℝ} (h : p - t / J ≤ q) :
    p + t * y ≤ q + t * (1 / J + y) := by
  have : t * (1 / J) = t / J := by ring
  nlinarith

/-- **Exercise 12.C.16** (MWG, p. 433), quadratic travel cost: a consumer at distance `x` from
firm `j` on the arc to a neighbour buys from `j` iff `x < (p − q + t/J²)/(2t/J)`. -/
theorem circQuad_prefers {t J p q x : ℝ} (ht : 0 < t) (hJ : 0 < J) :
    q + t * x ^ 2 < p + t * (1 / J - x) ^ 2 ↔ x < (p - q + t / J ^ 2) / (2 * (t / J)) := by
  rw [lt_div_iff₀ (by positivity)]
  have e : t * (1 / J - x) ^ 2 = t * x ^ 2 + t / J ^ 2 - x * (2 * (t / J)) := by
    field_simp; ring
  rw [e]
  constructor <;> intro h <;> linarith

/-- With quadratic travel cost and `q ≥ p − t/J²`, a consumer beyond a neighbour weakly prefers
the neighbour to firm `j`. -/
theorem circQuad_beyond {t J p q y : ℝ} (ht : 0 < t) (hJ : 0 < J) (hy : 0 ≤ y)
    (h : p - t / J ^ 2 ≤ q) : p + t * y ^ 2 ≤ q + t * (1 / J + y) ^ 2 := by
  have e : t * (1 / J + y) ^ 2 = t / J ^ 2 + 2 * (t / J) * y + t * y ^ 2 := by field_simp; ring
  rw [e]
  have : 0 ≤ 2 * (t / J) * y := by positivity
  linarith

/-- Firm `j`'s demand in the circular city when it charges `q ≥ p − w` and all other firms charge
`p`: `2M·max{0, min{1/J, (p − q + w)/(2s)}}`. -/
noncomputable def circDemand (M J s w p q : ℝ) : ℝ :=
  2 * M * max 0 (min (1 / J) ((p - q + w) / (2 * s)))

/-- **The circular city: symmetric equilibrium** (MWG, p. 399 and Exercise 12.C.16). Let
`s, J, M > 0` and `w = s/J`, and let `D` be firm `j`'s demand when the others charge `c + w`:
nonnegative, and equal to `circDemand` at every price `q ≥ c`. Then `q = c + w` is a best
response for firm `j`, which sells `M/J` and earns `wM/J`. -/
theorem circ_symmetric_eqm {M J s w c : ℝ} (hM : 0 < M) (hJ : 0 < J) (hs : 0 < s)
    (hw : w * J = s) {D : ℝ → ℝ} (hD0 : ∀ q, 0 ≤ D q)
    (hDloc : ∀ q, c + w - w ≤ q → D q = circDemand M J s w (c + w) q) :
    D (c + w) = M / J ∧ (c + w - c) * D (c + w) = w * M / J ∧
      ∀ q, (q - c) * D q ≤ (c + w - c) * D (c + w) := by
  have hwpos : 0 < w := by
    by_contra h; push Not at h; nlinarith
  have hws : w / (2 * s) = 1 / (2 * J) := by
    rw [← hw]; field_simp
  have hD : D (c + w) = M / J := by
    rw [hDloc _ (by linarith)]
    unfold circDemand
    rw [show c + w - (c + w) + w = w by ring, hws, min_eq_right (by
      rw [div_le_div_iff₀ (by positivity) hJ]; linarith), max_eq_right (by positivity)]
    field_simp
  refine ⟨hD, by rw [hD]; ring, fun q => ?_⟩
  rw [hD]
  rcases lt_or_ge q c with h | h
  · have : (q - c) * D q ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) (hD0 q)
    have : 0 < (c + w - c) * (M / J) := by
      rw [show c + w - c = w by ring]; positivity
    linarith
  · rw [hDloc q (by linarith)]
    unfold circDemand
    have hx : (q - c) * max 0 (min (1 / J) ((c + w - q + w) / (2 * s))) ≤
        max 0 ((q - c) * ((c + w - q + w) / (2 * s))) :=
      lcv_mul_le (by linarith) (le_max_left _ _) (max_le_max le_rfl (min_le_right _ _))
    have hb : (q - c) * ((c + w - q + w) / (2 * s)) ≤ w / (2 * J) := by
      rw [← hw, mul_div_assoc']
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [sq_nonneg (q - c - w), mul_pos hJ hwpos]
    have hb' : max 0 ((q - c) * ((c + w - q + w) / (2 * s))) ≤ w / (2 * J) :=
      max_le (by positivity) hb
    calc (q - c) * (2 * M * max 0 (min (1 / J) ((c + w - q + w) / (2 * s))))
        = 2 * M * ((q - c) * max 0 (min (1 / J) ((c + w - q + w) / (2 * s)))) := by ring
      _ ≤ 2 * M * (w / (2 * J)) := by
          apply mul_le_mul_of_nonneg_left (hx.trans hb') (by positivity)
      _ = (c + w - c) * (M / J) := by field_simp; ring

/-- **The circular city: uniqueness among symmetric profiles** (MWG, p. 399 and Exercise 12.C.16).
If every firm charging `p` is an equilibrium (firm `j`'s demand `D`, when the others charge `p`,
equals `circDemand` at every `q ≥ p − w`), then `p = c + w`. -/
theorem circ_symmetric_unique {M J s w c p : ℝ} (hM : 0 < M) (hJ : 0 < J) (hs : 0 < s)
    (hw : w * J = s) {D : ℝ → ℝ} (hDloc : ∀ q, p - w ≤ q → D q = circDemand M J s w p q)
    (hne : ∀ q, (q - c) * D q ≤ (p - c) * D p) : p = c + w := by
  have hwpos : 0 < w := by
    by_contra h; push Not at h; nlinarith
  -- on `[p − w, p + w]` the profit is `(q − c)M(p − q + w)/s`
  have hloc : ∀ δ, -w ≤ δ → δ ≤ w → (p + δ - c) * D (p + δ) = (p + δ - c) * M * (w - δ) / s := by
    intro δ h1 h2
    rw [hDloc _ (by linarith)]
    unfold circDemand
    have hX0 : 0 ≤ (p - (p + δ) + w) / (2 * s) := div_nonneg (by linarith) (by positivity)
    have hX1 : (p - (p + δ) + w) / (2 * s) ≤ 1 / J := by
      rw [div_le_div_iff₀ (by positivity) hJ, ← hw]; nlinarith
    rw [min_eq_right hX1, max_eq_right hX0]
    field_simp; ring
  have hgain : ∀ δ, -w ≤ δ → δ ≤ w →
      (p + δ - c) * D (p + δ) - (p - c) * D p = M / s * δ * (w - (p - c) - δ) := by
    intro δ h1 h2
    have h0 := hloc 0 (by linarith) (by linarith)
    rw [add_zero, sub_zero] at h0
    rw [hloc δ h1 h2, h0]; field_simp; ring
  by_contra hne'
  set e := w - (p - c) with he
  have he0 : e ≠ 0 := by intro h; apply hne'; linarith
  have hMs : 0 < M / s := div_pos hM hs
  rcases lt_or_gt_of_ne he0 with hneg | hpos
  · by_cases hbig : -(2 * w) ≤ e
    · have := hgain (e / 2) (by linarith) (by linarith)
      have h := hne (p + e / 2)
      have : 0 < M / s * (e / 2) * (e - e / 2) := by
        have : M / s * (e / 2) * (e - e / 2) = M / s * (e / 2) ^ 2 := by ring
        rw [this]; have : e / 2 ≠ 0 := by positivity
        positivity
      linarith
    · push Not at hbig
      have := hgain (-w) le_rfl (by linarith)
      have h := hne (p + -w)
      have : 0 < M / s * (-w) * (e - -w) :=
        mul_pos_of_neg_of_neg (mul_neg_of_pos_of_neg hMs (by linarith)) (by linarith)
      linarith
  · by_cases hbig : e ≤ 2 * w
    · have := hgain (e / 2) (by linarith) (by linarith)
      have h := hne (p + e / 2)
      have : 0 < M / s * (e / 2) * (e - e / 2) :=
        mul_pos (mul_pos hMs (by linarith)) (by linarith)
      linarith
    · push Not at hbig
      have := hgain w (by linarith) le_rfl
      have h := hne (p + w)
      have : 0 < M / s * w * (e - w) := mul_pos (mul_pos hMs hwpos) (by linarith)
      linarith

/-- **The circular city with linear travel cost** (MWG, p. 399; Salop 1979): with `J ≥ 1` firms
the symmetric equilibrium price is `c + t/J`; each firm sells `M/J` and earns `tM/J²`; and no other
symmetric price is an equilibrium. -/
theorem circularCity_linear {t M c : ℝ} (ht : 0 < t) (hM : 0 < M) {J : ℕ} (hJ : 0 < J)
    {D : ℝ → ℝ} (hD0 : ∀ q, 0 ≤ D q)
    (hDloc : ∀ q, c + t / J - t / J ≤ q → D q = circDemand M J t (t / J) (c + t / J) q) :
    (c + t / J - c) * D (c + t / J) = t * M / (J : ℝ) ^ 2 ∧
      (∀ q, (q - c) * D q ≤ (c + t / J - c) * D (c + t / J)) ∧
      ∀ p (E : ℝ → ℝ), (∀ q, p - t / J ≤ q → E q = circDemand M J t (t / J) p q) →
        (∀ q, (q - c) * E q ≤ (p - c) * E p) → p = c + t / J := by
  have hJ' : (0 : ℝ) < J := by exact_mod_cast hJ
  have hw : t / J * J = t := by field_simp
  obtain ⟨_, hval, hbr⟩ := circ_symmetric_eqm hM hJ' ht hw hD0 hDloc
  refine ⟨by rw [hval]; field_simp, hbr, fun p E hE hne => ?_⟩
  exact circ_symmetric_unique hM hJ' ht hw hE hne

/-- **Exercise 12.C.16** (MWG, p. 433). In the circular city with `J ≥ 1` firms and quadratic
travel cost `td²`, the symmetric equilibrium price is `c + t/J²`; each firm sells `M/J` and earns
`tM/J³`; and no other symmetric price is an equilibrium. -/
theorem exercise_12_C_16 {t M c : ℝ} (ht : 0 < t) (hM : 0 < M) {J : ℕ} (hJ : 0 < J)
    {D : ℝ → ℝ} (hD0 : ∀ q, 0 ≤ D q)
    (hDloc : ∀ q, c + t / (J : ℝ) ^ 2 - t / (J : ℝ) ^ 2 ≤ q →
      D q = circDemand M J (t / J) (t / (J : ℝ) ^ 2) (c + t / (J : ℝ) ^ 2) q) :
    D (c + t / (J : ℝ) ^ 2) = M / J ∧
      (c + t / (J : ℝ) ^ 2 - c) * D (c + t / (J : ℝ) ^ 2) = t * M / (J : ℝ) ^ 3 ∧
      (∀ q, (q - c) * D q ≤ (c + t / (J : ℝ) ^ 2 - c) * D (c + t / (J : ℝ) ^ 2)) ∧
      ∀ p (E : ℝ → ℝ), (∀ q, p - t / (J : ℝ) ^ 2 ≤ q →
        E q = circDemand M J (t / J) (t / (J : ℝ) ^ 2) p q) →
        (∀ q, (q - c) * E q ≤ (p - c) * E p) → p = c + t / (J : ℝ) ^ 2 := by
  have hJ' : (0 : ℝ) < J := by exact_mod_cast hJ
  have hw : t / (J : ℝ) ^ 2 * J = t / J := by field_simp
  obtain ⟨hD, hval, hbr⟩ := circ_symmetric_eqm hM hJ' (div_pos ht hJ') hw hD0 hDloc
  refine ⟨hD, by rw [hval]; field_simp, hbr, fun p E hE hne => ?_⟩
  exact circ_symmetric_unique hM hJ' (div_pos ht hJ') hw hE hne

/-- **Exercise 12.C.16** (MWG, p. 433): "What happens as `J` grows large? As `t` falls?" As
`J → ∞` the equilibrium price `c + t/J²` tends to `c` and each firm's profit `tM/J³` (and the
industry profit `tM/J²`) to `0`; for fixed `J`, a fall in `t` strictly lowers price and
profit. -/
theorem exercise_12_C_16_limits {t M c : ℝ} :
    Tendsto (fun J : ℕ => c + t / (J : ℝ) ^ 2) atTop (𝓝 c) ∧
      Tendsto (fun J : ℕ => t * M / (J : ℝ) ^ 3) atTop (𝓝 0) ∧
      Tendsto (fun J : ℕ => (J : ℝ) * (t * M / (J : ℝ) ^ 3)) atTop (𝓝 0) ∧
      ∀ {J : ℕ}, 0 < J → 0 < M → ∀ {t' : ℝ}, t' < t →
        c + t' / (J : ℝ) ^ 2 < c + t / (J : ℝ) ^ 2 ∧
          t' * M / (J : ℝ) ^ 3 < t * M / (J : ℝ) ^ 3 := by
  have h2 : Tendsto (fun J : ℕ => ((J : ℝ) ^ 2)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop two_ne_zero).comp
      tendsto_natCast_atTop_atTop)
  have h3 : Tendsto (fun J : ℕ => ((J : ℝ) ^ 3)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop three_ne_zero).comp
      tendsto_natCast_atTop_atTop)
  refine ⟨?_, ?_, ?_, fun {J} hJ hM {t'} htt => ?_⟩
  · have := (h2.const_mul t).const_add c
    rw [mul_zero, add_zero] at this
    exact this.congr fun J => by simp [div_eq_mul_inv]
  · have := h3.const_mul (t * M)
    rw [mul_zero] at this
    exact this.congr fun J => by simp [div_eq_mul_inv]
  · have := h2.const_mul (t * M)
    rw [mul_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with J hJ
    have : (0 : ℝ) < J := by exact_mod_cast hJ
    field_simp
  · have hJ' : (0 : ℝ) < J := by exact_mod_cast hJ
    constructor
    · have := div_lt_div_of_pos_right htt (pow_pos hJ' 2); linarith
    · exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_right htt hM) (pow_pos hJ' 3)

end MWG.MarketPower
