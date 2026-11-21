/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGMarketPower.CityModels

/-!
# Linear city exercises and the small type of p. 398

MWG, small type on p. 398, and Exercises 12.C.13 and 12.C.14 (p. 432-433), in the linear city
with nonpurchase of `MWGMarketPower.CityModels`. Throughout `t > 0` and `M > 0`; write
`L = (4v − 3t − c)/3` and `U = (3v − 2t − c)/2`.

* `smallType_12_C_398`: for every `v ≥ c + 3t/2` the profile `p₁ = p₂ = c + t` is the unique Nash
  equilibrium, with profits `tM/2` ("the equilibrium just derived remains valid as long as
  `v ≥ c + 3t/2`"); `smallType_12_C_398_kink`: for `v ∈ [c + t, c + 3t/2]` the profile
  `p₁ = p₂ = v − t/2` is an equilibrium at the kink, every consumer buys, and the consumer at `ẑ`
  gets no surplus.
* `exercise_12_C_13`: with `v > c + 3t`, every best response to every rival price leaves all
  consumers purchasing (the two shares sum to one).
* `exercise_12_C_14a`, `exercise_12_C_14b`: best responses and the unique equilibrium `c + t`.
* `exercise_12_C_14c`: for `c < v < c + t`, best responses, the unique equilibrium `(v + c)/2`, and
  some consumers do not buy. The hypothesis `v > c` is needed:
  `exercise_12_C_14c_counterexample` (correction 26).
* `exercise_12_C_14d`: for `v ∈ (c + t, c + 3t/2)` the equilibria are exactly the pairs with
  `p₁ + p₂ = 2v − t` and `p₁, p₂ ∈ [L, U]`; the unique symmetric one is `v − t/2`, and there are
  asymmetric equilibria (the answer to (d)'s question is yes).
* `exercise_12_C_14e`: in case (d) a fall in `t` raises the equilibrium price and profits; in
  cases (a) and (b) it lowers them.
-/

namespace MWG.MarketPower

/-- **Small type, p. 398** (MWG). For every `v ≥ c + 3t/2`, `p₁* = p₂* = c + t` is the unique Nash
equilibrium of the linear city with nonpurchase, and each firm earns `tM/2`. -/
theorem smallType_12_C_398 {v t M c : ℝ} (ht : 0 < t) (hM : 0 < M) (hv : 2 * c + 3 * t ≤ 2 * v) :
    IsLCVNash v t M c (c + t) (c + t) ∧ lcvProfit v t M c (c + t) (c + t) = t * M / 2 ∧
      ∀ p1 p2, IsLCVNash v t M c p1 p2 → p1 = c + t ∧ p2 = c + t := by
  have hcv : c < v := by linarith
  have hbr := (lcvBR_duo (v := v) (M := M) (c := c) ht hM (p2 := c + t) (by linarith) (by linarith)
    (by linarith))
  have e : (t + (c + t) + c) / 2 = c + t := by ring
  rw [e] at hbr
  refine ⟨lcvNash_of_BR hbr.2 hbr.2, ?_, fun p1 p2 hne => ?_⟩
  · unfold lcvProfit; rw [hbr.1]; field_simp; ring
  obtain ⟨hc1, hc2⟩ := lcvNash_ge_c ht hM hcv hne
  rcases le_or_gt v (c + 2 * t) with hlow | hv2
  · have h1 := lcv_eq_of_uniqueBR (lcvBRLow_spec ht hM hcv hlow (by linarith)) hne.1
    have h2 := lcv_eq_of_uniqueBR (lcvBRLow_spec ht hM hcv hlow (by linarith)) hne.2
    unfold lcvBRLow at h1 h2
    split_ifs at h1 h2 <;> constructor <;> linarith
  rcases lt_or_ge v (c + 3 * t) with hmid | hhigh
  · have h1 := lcv_eq_of_uniqueBR (lcvBRMid_spec ht hM hv2.le hmid (by linarith)) hne.1
    have h2 := lcv_eq_of_uniqueBR (lcvBRMid_spec ht hM hv2.le hmid (by linarith)) hne.2
    unfold lcvBRMid at h1 h2
    split_ifs at h1 h2 <;> constructor <;> linarith
  · have h1 := lcv_eq_of_uniqueBR (lcvBRHigh_spec ht hM hhigh (by linarith)) hne.1
    have h2 := lcv_eq_of_uniqueBR (lcvBRHigh_spec ht hM hhigh (by linarith)) hne.2
    unfold lcvBRHigh at h1 h2
    split_ifs at h1 h2 <;> constructor <;> linarith

/-- **Small type, p. 398** (MWG). For `v ∈ [c + t, c + 3t/2]`, `p₁ = p₂ = v − t/2` is a Nash
equilibrium "at a kink": each firm serves half the market, so every consumer buys, and the
consumer at `ẑ = 1/2` gets no surplus from his purchase. -/
theorem smallType_12_C_398_kink {v t M c : ℝ} (ht : 0 < t) (hM : 0 < M) (hv1 : c + t ≤ v)
    (hv2 : 2 * v ≤ 2 * c + 3 * t) :
    IsLCVNash v t M c (v - t / 2) (v - t / 2) ∧ lcvShare v t (v - t / 2) (v - t / 2) = 1 / 2 ∧
      lcHat t (v - t / 2) (v - t / 2) = 1 / 2 ∧ v - (v - t / 2) - t * (1 / 2) = 0 := by
  have hcv : c < v := by linarith
  have hbr := lcvBRLow_spec (M := M) ht hM hcv (by linarith) (show c - t < v - t / 2 by linarith)
  have e : lcvBRLow v t c (v - t / 2) = v - t / 2 := by
    unfold lcvBRLow; split_ifs <;> linarith
  rw [e] at hbr
  refine ⟨lcvNash_of_BR hbr hbr, lcvShare_symm_half ht (by linarith), ?_, by ring⟩
  unfold lcHat; field_simp; ring

/-- **Exercise 12.C.13** (MWG, p. 432). If `v > c + 3t`, any best response of firm 1 to any price
`p₂` of firm 2 results in all consumers purchasing from one of the two firms: the shares sum to
one. -/
theorem exercise_12_C_13 {v t M c : ℝ} (ht : 0 < t) (hM : 0 < M) (hv : c + 3 * t < v)
    (p2 p1 : ℝ) (hbr : ∀ q, lcvProfit v t M c q p2 ≤ lcvProfit v t M c p1 p2) :
    lcvShare v t p1 p2 + lcvShare v t p2 p1 = 1 := by
  have hcv : c < v := by linarith
  rcases le_or_gt p2 (c - t) with hlow | hp2
  · have hz : lcHat t p1 p2 ≤ 0 := by
      rcases lt_or_ge p1 c with h | h
      · have h0 : 0 ≤ lcvProfit v t M c p1 p2 := by
          have := hbr c; unfold lcvProfit at this ⊢; linarith [this, show (c - c) * (M *
            lcvShare v t c p2) = 0 by ring]
        have := lcv_rival_low ht hM hcv h h0
        unfold lcHat; exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
      · unfold lcHat; exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
    rw [lcvShare_eq_zero hz, zero_add]
    apply lcvShare_eq_of zero_le_one le_rfl
    · rw [le_div_iff₀ ht]; linarith
    · rw [lcHat_symm ht]; linarith
    · left; rfl
  · have h1 := lcv_eq_of_uniqueBR (lcvBRHigh_spec ht hM hv.le hp2) hbr
    unfold lcvBRHigh at h1
    split_ifs at h1 with ha hb
    · rw [h1, (lcvBR_duo (v := v) (M := M) (c := c) ht hM hp2 ha (by linarith)).1]
      have hz : lcHat t ((t + p2 + c) / 2) p2 = (t + p2 - c) / (4 * t) := by
        unfold lcHat; field_simp; ring
      have hs2 : lcvShare v t p2 ((t + p2 + c) / 2) = (3 * t - p2 + c) / (4 * t) := by
        have e : lcHat t p2 ((t + p2 + c) / 2) = (3 * t - p2 + c) / (4 * t) := by
          rw [lcHat_symm ht, hz]; field_simp; ring
        apply lcvShare_eq_of
        · exact div_nonneg (by linarith) (by positivity)
        · rw [div_le_one (by positivity)]; linarith
        · rw [div_le_div_iff₀ (by positivity) ht]; nlinarith
        · rw [e]
        · right; right; rw [e]
      rw [hs2]; field_simp; ring
    · rw [h1, (lcvBR_capture (v := v) (M := M) (c := c) ht hM (by linarith) hb).1,
        lcvShare_eq_zero (by unfold lcHat; field_simp; linarith)]
      ring
    · rw [h1, (lcvBR_cover (v := v) (M := M) (c := c) ht hM (by linarith) (by linarith)).1,
        lcvShare_eq_zero]
      · ring
      · unfold lcHat; exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)

/-- **Exercise 12.C.14(a)** (MWG, p. 432). For `v ∈ (c + 2t, c + 3t)`: the best response to
`p₂ > c − t` is `lcvBRMid` (interior duopoly up to `L`, the kink `2v − t − p₂` on `(L, v]`, then
`v − t`), no price earns a positive profit against `p₂ ≤ c − t`, and the unique Nash equilibrium
is `p₁* = p₂* = c + t`. -/
theorem exercise_12_C_14a {v t M c : ℝ} (ht : 0 < t) (hM : 0 < M) (hv1 : c + 2 * t < v)
    (hv2 : v < c + 3 * t) :
    (∀ p2, c - t < p2 → IsLCVUniqueBR v t M c p2 (lcvBRMid v t c p2)) ∧
    (∀ p2, p2 ≤ c - t → ∀ p, lcvProfit v t M c p p2 ≤ 0) ∧
    IsLCVNash v t M c (c + t) (c + t) ∧
      ∀ p1 p2, IsLCVNash v t M c p1 p2 → p1 = c + t ∧ p2 = c + t :=
  ⟨fun _ h => lcvBRMid_spec ht hM hv1.le hv2 h, fun _ h => (lcvBR_low ht hM h).2,
    (smallType_12_C_398 ht hM (by linarith)).1, (smallType_12_C_398 ht hM (by linarith)).2.2⟩

/-- **Exercise 12.C.14(b)** (MWG, p. 432). For `v ∈ (c + 3t/2, c + 2t)`: the best response to
`p₂ > c − t` is `lcvBRLow` (interior duopoly up to `L`, the kink on `(L, U]`, then the local
monopoly price `(v + c)/2`), and the unique Nash equilibrium is `p₁* = p₂* = c + t`. -/
theorem exercise_12_C_14b {v t M c : ℝ} (ht : 0 < t) (hM : 0 < M) (hv1 : 2 * c + 3 * t < 2 * v)
    (hv2 : v < c + 2 * t) :
    (∀ p2, c - t < p2 → IsLCVUniqueBR v t M c p2 (lcvBRLow v t c p2)) ∧
    (∀ p2, p2 ≤ c - t → ∀ p, lcvProfit v t M c p p2 ≤ 0) ∧
    IsLCVNash v t M c (c + t) (c + t) ∧
      ∀ p1 p2, IsLCVNash v t M c p1 p2 → p1 = c + t ∧ p2 = c + t :=
  ⟨fun _ h => lcvBRLow_spec ht hM (by linarith) hv2.le h, fun _ h => (lcvBR_low ht hM h).2,
    (smallType_12_C_398 ht hM hv1.le).1, (smallType_12_C_398 ht hM hv1.le).2.2⟩

/-- **Exercise 12.C.14(c)** (MWG, p. 432), with `v > c` added. For `c < v < c + t`: the best
response to `p₂ > c − t` is `lcvBRLow`; the unique Nash equilibrium is
`p₁* = p₂* = (v + c)/2`; each firm serves `(v − c)/(2t)` of the market, so a fraction
`1 − (v − c)/t > 0` of consumers buys from neither firm ("local monopolists", p. 398). -/
theorem exercise_12_C_14c {v t M c : ℝ} (ht : 0 < t) (hM : 0 < M) (hcv : c < v)
    (hv : v < c + t) :
    (∀ p2, c - t < p2 → IsLCVUniqueBR v t M c p2 (lcvBRLow v t c p2)) ∧
    IsLCVNash v t M c ((v + c) / 2) ((v + c) / 2) ∧
    (∀ p1 p2, IsLCVNash v t M c p1 p2 → p1 = (v + c) / 2 ∧ p2 = (v + c) / 2) ∧
    lcvShare v t ((v + c) / 2) ((v + c) / 2) = (v - c) / (2 * t) ∧
    lcvShare v t ((v + c) / 2) ((v + c) / 2) + lcvShare v t ((v + c) / 2) ((v + c) / 2) < 1 := by
  have hbr := lcvBR_mono (M := M) (p2 := (v + c) / 2) ht hM hcv (by linarith) (by linarith)
  refine ⟨fun _ h => lcvBRLow_spec ht hM hcv (by linarith) h, lcvNash_of_BR hbr.2 hbr.2,
    fun p1 p2 hne => ?_, hbr.1, ?_⟩
  · obtain ⟨hc1, hc2⟩ := lcvNash_ge_c ht hM hcv hne
    have h1 := lcv_eq_of_uniqueBR (lcvBRLow_spec ht hM hcv (by linarith) (by linarith)) hne.1
    have h2 := lcv_eq_of_uniqueBR (lcvBRLow_spec ht hM hcv (by linarith) (by linarith)) hne.2
    unfold lcvBRLow at h1 h2
    split_ifs at h1 h2 <;> constructor <;> linarith
  · rw [hbr.1, ← add_div, div_lt_one (by positivity)]; linarith

/-- **Exercise 12.C.14(c)** (MWG, p. 432): without `v > c` the equilibrium is not unique. With
`v = c`, both `p₁ = p₂ = c = (v + c)/2` and `p₁ = p₂ = c + 1` are Nash equilibria (nobody can earn
a positive profit). -/
theorem exercise_12_C_14c_counterexample {t M c : ℝ} (ht : 0 < t) (hM : 0 < M) :
    IsLCVNash c t M c ((c + c) / 2) ((c + c) / 2) ∧ IsLCVNash c t M c (c + 1) (c + 1) := by
  have hle : ∀ p q, lcvProfit c t M c p q ≤ 0 := by
    intro p q
    rcases lt_or_ge p c with h | h
    · exact lcv_le_zero_of_lt hM.le h
    · refine (lcv_le_A hM.le h).trans ?_
      have : (p - c) * ((c - p) / t) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by linarith) (div_nonpos_of_nonpos_of_nonneg
          (by linarith) ht.le)
      rw [max_eq_left this, mul_zero]
  have hz1 : ∀ q, lcvProfit c t M c ((c + c) / 2) q = 0 := fun q => by
    unfold lcvProfit; ring
  have hz2 : ∀ q, lcvProfit c t M c (c + 1) q = 0 := fun q => by
    unfold lcvProfit lcvShare
    have : (c - (c + 1)) / t < 0 := div_neg_of_neg_of_pos (by linarith) ht
    rw [max_eq_left ((min_le_right _ _).trans ((min_le_left _ _).trans this.le))]
    ring
  exact ⟨⟨fun q => by rw [hz1]; exact hle _ _, fun q => by rw [hz1]; exact hle _ _⟩,
    ⟨fun q => by rw [hz2]; exact hle _ _, fun q => by rw [hz2]; exact hle _ _⟩⟩

/-- **Exercise 12.C.14(d)** (MWG, p. 432). For `v ∈ (c + t, c + 3t/2)`: the best response to
`p₂ > c − t` is `lcvBRLow`; the Nash equilibria are exactly the pairs with `p₁ + p₂ = 2v − t`
and `L ≤ p₁, p₂ ≤ U`; the unique symmetric equilibrium is `p₁* = p₂* = v − t/2`; and asymmetric
equilibria exist. -/
theorem exercise_12_C_14d {v t M c : ℝ} (ht : 0 < t) (hM : 0 < M) (hv1 : c + t < v)
    (hv2 : 2 * v < 2 * c + 3 * t) :
    (∀ p2, c - t < p2 → IsLCVUniqueBR v t M c p2 (lcvBRLow v t c p2)) ∧
    (∀ p1 p2, IsLCVNash v t M c p1 p2 ↔ p1 + p2 = 2 * v - t ∧
      (4 * v - 3 * t - c) / 3 ≤ p1 ∧ p1 ≤ (3 * v - 2 * t - c) / 2 ∧
      (4 * v - 3 * t - c) / 3 ≤ p2 ∧ p2 ≤ (3 * v - 2 * t - c) / 2) ∧
    (∀ p, IsLCVNash v t M c p p ↔ p = v - t / 2) ∧
    ∃ p1 p2, p1 ≠ p2 ∧ IsLCVNash v t M c p1 p2 := by
  have hcv : c < v := by linarith
  have hspec : ∀ p2, c - t < p2 → IsLCVUniqueBR v t M c p2 (lcvBRLow v t c p2) :=
    fun _ h => lcvBRLow_spec ht hM hcv (by linarith) h
  have hchar : ∀ p1 p2, IsLCVNash v t M c p1 p2 ↔ p1 + p2 = 2 * v - t ∧
      (4 * v - 3 * t - c) / 3 ≤ p1 ∧ p1 ≤ (3 * v - 2 * t - c) / 2 ∧
      (4 * v - 3 * t - c) / 3 ≤ p2 ∧ p2 ≤ (3 * v - 2 * t - c) / 2 := by
    intro p1 p2
    constructor
    · intro hne
      obtain ⟨hc1, hc2⟩ := lcvNash_ge_c ht hM hcv hne
      have h1 := lcv_eq_of_uniqueBR (hspec p2 (by linarith)) hne.1
      have h2 := lcv_eq_of_uniqueBR (hspec p1 (by linarith)) hne.2
      unfold lcvBRLow at h1 h2
      split_ifs at h1 h2 <;> refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith
    · rintro ⟨hs, h1, h2, h3, h4⟩
      have e1 : lcvBRLow v t c p2 = p1 := by unfold lcvBRLow; split_ifs <;> linarith
      have e2 : lcvBRLow v t c p1 = p2 := by unfold lcvBRLow; split_ifs <;> linarith
      have b1 := hspec p2 (by linarith)
      have b2 := hspec p1 (by linarith)
      rw [e1] at b1; rw [e2] at b2
      exact lcvNash_of_BR b1 b2
  refine ⟨hspec, hchar, fun p => ?_, ?_⟩
  · rw [hchar]
    constructor
    · rintro ⟨hs, -⟩; linarith
    · intro hp; subst hp; refine ⟨by ring, ?_, ?_, ?_, ?_⟩ <;> linarith
  · set δ := min ((3 * t + 2 * c - 2 * v) / 6) ((v - c - t) / 2) with hδ
    have hδpos : 0 < δ := lt_min (by linarith) (by linarith)
    have hδ1 : δ ≤ (3 * t + 2 * c - 2 * v) / 6 := min_le_left _ _
    have hδ2 : δ ≤ (v - c - t) / 2 := min_le_right _ _
    refine ⟨v - t / 2 + δ, v - t / 2 - δ, by linarith, (hchar _ _).2 ⟨by ring, ?_, ?_, ?_, ?_⟩⟩ <;>
      linarith

/-- **Exercise 12.C.14(e)** (MWG, p. 433). Let `t₁ < t₂`. If both travel costs are in case (d)
(`c + t₂ < v` and `2v < 2c + 3t₁`), the symmetric equilibrium price and profit are higher at the
lower travel cost `t₁`. If both are in cases (a)-(b) (`2v ≥ 2c + 3t₂`), they are lower at `t₁`:
a fall in `t` raises prices and profits in case (d) but lowers them in cases (a) and (b). -/
theorem exercise_12_C_14e {v M c t1 t2 : ℝ} (hM : 0 < M) (ht1 : 0 < t1) (h12 : t1 < t2) :
    ((c + t2 < v ∧ 2 * v < 2 * c + 3 * t1) → ∀ p q, IsLCVNash v t1 M c p p →
      IsLCVNash v t2 M c q q → q < p ∧ lcvProfit v t2 M c q q < lcvProfit v t1 M c p p) ∧
    (2 * c + 3 * t2 ≤ 2 * v → ∀ p q, IsLCVNash v t1 M c p p →
      IsLCVNash v t2 M c q q → p < q ∧ lcvProfit v t1 M c p p < lcvProfit v t2 M c q q) := by
  have ht2 : 0 < t2 := by linarith
  constructor
  · rintro ⟨hv1, hv2⟩ p q hp hq
    have ep := ((exercise_12_C_14d ht1 hM (by linarith) hv2).2.2.1 p).1 hp
    have eq := ((exercise_12_C_14d ht2 hM hv1 (by linarith)).2.2.1 q).1 hq
    subst ep; subst eq
    have s1 := lcvShare_symm_half (v := v) ht1 (p := v - t1 / 2) (by linarith)
    have s2 := lcvShare_symm_half (v := v) ht2 (p := v - t2 / 2) (by linarith)
    refine ⟨by linarith, ?_⟩
    unfold lcvProfit; rw [s1, s2]; nlinarith
  · intro hv p q hp hq
    have ep := ((smallType_12_C_398 ht1 hM (by linarith)).2.2 p p hp).1
    have eq := ((smallType_12_C_398 ht2 hM hv).2.2 q q hq).1
    subst ep; subst eq
    rw [(smallType_12_C_398 ht1 hM (by linarith)).2.1, (smallType_12_C_398 ht2 hM hv).2.1]
    exact ⟨by linarith, by nlinarith⟩

end MWG.MarketPower
