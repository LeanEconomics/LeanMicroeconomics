/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGMarketPower.CompetitiveLimit
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Competitive-limit exercises

MWG, Exercises 12.F.2-12.F.4, p. 435.

* `exercise_12_F_2a`: `I` consumers with demand `a − bp` give market demand `I(a − bp)` and
  inverse demand `a/b − Q/(bI)`, i.e. the Section 12.F model with `x(p) = a − bp` and `α = I`.
* `exercise_12_F_2b`: Cournot entry with cost `cq` and entry cost `K`, both two-stage
  (`IsEntryEquilibrium`, Section 12.E) and one-stage (`IsOneStageCournotEntry`: active firms play
  the Cournot equilibrium and earn at least `K`; no outsider gains by entering with any output
  against the active firms' outputs). In both, per-firm profit lies in `[K, 4K]`
  (`cournot_entry_profit_bounds`), so as `I → ∞` the number of firms tends to infinity, the price
  tends to `c`, output per consumer to the competitive `a − bc`, per-firm output per consumer to
  `0`, and consumer surplus per consumer to the competitive `(a − bc)²/(2b)`.
* `exercise_12_F_3`: in the linear two-stage Cournot entry model (Example 12.E.1, the model in
  which Section 12.F's phenomenon was first seen) with `α` fixed, the welfare loss relative to the
  first best, and hence relative to the welfare-optimal number of firms, tends to `0` as `K → 0`.
* Exercise 12.F.4 as printed is ill-posed: the demand `xⱼ(p) = α[γ − β(Jpⱼ/∑ₖ pₖ)]` is
  homogeneous of degree zero in prices. `exercise_12_F_4_br`: when `γ < βJ` the best response to
  rivals' price sum `s` is unique and proportional to `s`; `exercise_12_F_4_no_br`: when
  `γ ≥ βJ` there is no best response; `exercise_12_F_4_symmetric`: a symmetric price `p > 0` is
  an equilibrium iff `γ = β(2 − 1/J)` (a knife-edge that fixes `J`);
  `exercise_12_F_4_indeterminate`: then every `p > 0` is an equilibrium, with quantities
  `α(γ − β)` independent of `p` and profit `αp(γ − β)` taking every positive value, so neither
  prices nor the entry outcome are determined by `α` and `β`.

Departures: in Exercise 12.F.2(b) the stage-2 outputs are the symmetric linear Cournot
equilibrium (unique, Exercise 12.C.7); Exercise 12.F.3 is proved for the linear model; Exercise
12.F.4 is analysed as stated and found ill-posed (`docs/corrections.md`).
-/

namespace MWG.MarketPower

open Set Filter Topology

/-! ### Exercise 12.F.2 -/

/-- **Exercise 12.F.2(a)** (MWG, p. 435). With `I` consumers each demanding `a − bp`, market
demand is `I(a − bp)`; the market inverse demand is `p(Q) = a/b − Q/(bI)`, which is the
size-`I` inverse demand `p(Q/I)` of the individual demand `x(p) = a − bp`. -/
theorem exercise_12_F_2a {a b : ℝ} (hb : 0 < b) {I : ℕ} (hI : 0 < I) (p Q : ℝ) :
    ∑ _i ∈ Finset.range I, (a - b * p) = I * (a - b * p) ∧
    (Q = I * (a - b * p) ↔ p = a / b - Q / (b * I)) ∧
    sizedDemand (fun s => a / b - s / b) I Q = a / b - Q / (b * I) := by
  have hI' : (0 : ℝ) < I := by exact_mod_cast hI
  refine ⟨by simp; ring, ⟨fun h => ?_, fun h => ?_⟩, ?_⟩
  · rw [h]; field_simp; ring
  · rw [h]; field_simp; ring
  · unfold sizedDemand; field_simp

/-- Per-firm Cournot output with `J` firms in the market of Exercise 12.F.2:
`(a/b − c)/(B(J + 1))` with `B = 1/(bI)`, i.e. `(a − bc)I/(J + 1)`. -/
noncomputable def fqJ (a b c I : ℝ) (J : ℕ) : ℝ := (a - b * c) * I / (J + 1)

/-- Consumer surplus at total output `Q` for the inverse demand `a/b − s/(bI)`:
`∫₀^Q p(s) ds − p(Q)Q`. -/
noncomputable def linCS (a b I Q : ℝ) : ℝ :=
  (∫ s in (0 : ℝ)..Q, (a / b - s / (b * I))) - (a / b - Q / (b * I)) * Q

/-- Consumer surplus with linear inverse demand is `Q²/(2bI)`. -/
theorem linCS_eq {a b I : ℝ} (hb : 0 < b) (hI : 0 < I) (Q : ℝ) :
    linCS a b I Q = Q ^ 2 / (2 * b * I) := by
  unfold linCS
  rw [intervalIntegral.integral_sub intervalIntegrable_const
    ((by fun_prop : Continuous fun s : ℝ => s / (b * I)).intervalIntegrable _ _),
    intervalIntegral.integral_const, intervalIntegral.integral_div, integral_id]
  simp only [smul_eq_mul]
  field_simp
  ring

/-- A one-stage Cournot entry equilibrium with `J` active firms (MWG, Section 12.E and Exercise
12.F.2(b)), linear inverse demand `A − BQ`, marginal cost `c` and entry cost `K` (paid only by
active firms): the active firms produce the Cournot output `(A − c)/(B(J + 1))` and earn at least
`K`, and no outsider can earn a positive net profit by entering with any output `y ≥ 0` against
the active firms' outputs. -/
def IsOneStageCournotEntry (A B c K : ℝ) (J : ℕ) : Prop :=
  1 ≤ J ∧ K ≤ cournotEntryProfit A B c J ∧
  ∀ y, 0 ≤ y → (A - B * (J * ((A - c) / (B * (J + 1))) + y) - c) * y - K ≤ 0

/-- In both the two-stage and the one-stage linear Cournot entry models, equilibrium per-firm
profit lies in `[K, 4K]`. -/
theorem cournot_entry_profit_bounds {A B c K : ℝ} (hB : 0 < B) (hAc : c ≤ A) {J : ℕ}
    (hJ : IsEntryEquilibrium (cournotEntryProfit A B c) K J ∨ IsOneStageCournotEntry A B c K J) :
    K ≤ cournotEntryProfit A B c J ∧ cournotEntryProfit A B c J ≤ 4 * K := by
  rcases hJ with h | h
  · refine ⟨h.2.1, ?_⟩
    have e : cournotEntryProfit A B c J * ((J : ℝ) + 1) ^ 2 =
        cournotEntryProfit A B c (J + 1) * ((J : ℝ) + 2) ^ 2 := by
      unfold cournotEntryProfit; push_cast; field_simp; ring
    have hnn : 0 ≤ cournotEntryProfit A B c (J + 1) := by
      unfold cournotEntryProfit; positivity
    have h2 := h.2.2
    have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg J
    have hle : ((J : ℝ) + 2) ^ 2 ≤ 4 * ((J : ℝ) + 1) ^ 2 := by nlinarith
    have hpos : (0 : ℝ) < ((J : ℝ) + 1) ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hle hnn]
  · refine ⟨h.2.1, ?_⟩
    have hy := h.2.2 ((A - c) / (B * (J + 1)) / 2) (by
      have : 0 ≤ A - c := by linarith
      positivity)
    have e : (A - B * (J * ((A - c) / (B * (J + 1))) + (A - c) / (B * (J + 1)) / 2) - c) *
        ((A - c) / (B * (J + 1)) / 2) = cournotEntryProfit A B c J / 4 := by
      unfold cournotEntryProfit; field_simp; ring
    linarith

/-- **Exercise 12.F.2(b)** (MWG, p. 435). Market of `I` consumers with demand `a − bp`
(`bc < a`), Cournot competition with cost `cq` and entry cost `K > 0`. Let `J(I)` be an
equilibrium number of firms of either the two-stage or the one-stage entry model for each `I ≥ 1`.
Each firm produces `fqJ = (a − bc)I/(J + 1)`. As `I → ∞`: the number of firms tends to infinity;
the price tends to `c`; total output per consumer tends to the competitive `a − bc`; each firm's
output per consumer tends to `0`; consumer surplus per consumer tends to the competitive
`(a − bc)²/(2b)`. -/
theorem exercise_12_F_2b {a b c K : ℝ} (hb : 0 < b) (hbc : b * c < a) (hK : 0 < K)
    (J : ℕ → ℕ) (hJ : ∀ I : ℕ, 1 ≤ I →
      IsEntryEquilibrium (cournotEntryProfit (a / b) (1 / (b * I)) c) K (J I) ∨
      IsOneStageCournotEntry (a / b) (1 / (b * I)) c K (J I)) :
    (∀ I : ℕ, 1 ≤ I → (a / b - c) / (1 / (b * I) * (J I + 1)) = fqJ a b c I (J I)) ∧
    Tendsto J atTop atTop ∧
    Tendsto (fun I : ℕ => a / b - J I * fqJ a b c I (J I) / (b * I)) atTop (𝓝 c) ∧
    Tendsto (fun I : ℕ => J I * fqJ a b c I (J I) / I) atTop (𝓝 (a - b * c)) ∧
    Tendsto (fun I : ℕ => fqJ a b c I (J I) / I) atTop (𝓝 0) ∧
    Tendsto (fun I : ℕ => linCS a b I (J I * fqJ a b c I (J I)) / I) atTop
      (𝓝 ((a - b * c) ^ 2 / (2 * b))) := by
  have hA : c < a / b := (lt_div_iff₀ hb).2 (by linarith)
  have hAc : 0 < a / b - c := sub_pos.2 hA
  have hD : 0 < (a / b - c) ^ 2 * b := by positivity
  have hJinf : Tendsto J atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro M
    refine ⟨⌈4 * K * (M : ℝ) ^ 2 / ((a / b - c) ^ 2 * b)⌉₊ + 1, fun I hI => ?_⟩
    have hI1 : 1 ≤ I := le_trans (Nat.le_add_left 1 _) hI
    have hIr : (0 : ℝ) < I := by exact_mod_cast hI1
    have hbd := (cournot_entry_profit_bounds (by positivity) hA.le (hJ I hI1)).2
    unfold cournotEntryProfit at hbd
    have e : ((a / b - c) / ((J I : ℝ) + 1)) ^ 2 / (1 / (b * I)) =
        (a / b - c) ^ 2 * b * I / ((J I : ℝ) + 1) ^ 2 := by
      field_simp
    rw [e, div_le_iff₀ (by positivity)] at hbd
    have hceil : 4 * K * (M : ℝ) ^ 2 / ((a / b - c) ^ 2 * b) < I := by
      have h1 := Nat.le_ceil (4 * K * (M : ℝ) ^ 2 / ((a / b - c) ^ 2 * b))
      have h2 : ((⌈4 * K * (M : ℝ) ^ 2 / ((a / b - c) ^ 2 * b)⌉₊ + 1 : ℕ) : ℝ) ≤ I := by
        exact_mod_cast hI
      push_cast at h2
      linarith
    rw [div_lt_iff₀ hD] at hceil
    by_contra hlt
    push Not at hlt
    have h3 : ((J I : ℝ) + 1) ≤ M := by exact_mod_cast hlt
    have h4 : ((J I : ℝ) + 1) ^ 2 ≤ (M : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) h3 2
    nlinarith
  have hJr : Tendsto (fun I => ((J I : ℕ) : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop.comp hJinf)
  have hev : ∀ᶠ I : ℕ in atTop, (1 : ℝ) ≤ I :=
    Filter.eventually_atTop.2 ⟨1, fun I hI => by exact_mod_cast hI⟩
  have hQI : Tendsto (fun I : ℕ => J I * fqJ a b c I (J I) / I) atTop (𝓝 (a - b * c)) := by
    have h := ((exercise_12_C_7_limits (b := 1) hbc one_pos).2.2.2.2).comp hJinf
    rw [div_one] at h
    refine h.congr' ?_
    filter_upwards [hev] with I hI
    simp only [Function.comp, fqJ]
    field_simp
  refine ⟨fun I hI => ?_, hJinf, ?_, hQI, ?_, ?_⟩
  · have hIr : (0 : ℝ) < I := by exact_mod_cast hI
    unfold fqJ; field_simp
  · have h := ((exercise_12_C_7_limits hA hb).2.2.2.1).comp hJinf
    refine h.congr' ?_
    filter_upwards [hev] with I hI
    simp only [Function.comp, fqJ]
    field_simp
    ring
  · have h := (tendsto_const_nhds (x := a - b * c)).div_atTop hJr
    refine h.congr' ?_
    filter_upwards [hev] with I hI
    simp only [fqJ]
    field_simp
  · have h := (hQI.pow 2).div_const (2 * b)
    refine h.congr' ?_
    filter_upwards [hev] with I hI
    rw [linCS_eq hb (by linarith)]
    field_simp

/-- **Instance for Exercise 12.F.2(b)** (MWG, p. 435). With `a = 2`, `b = 1`, `c = 0`,
`K = 1`, per-firm profit is `π_J = 4I/(J + 1)²`, a two-stage entry equilibrium exists for every
`I ≥ 1` (`entry_equilibrium_exists`), so the hypotheses of `exercise_12_F_2b` hold and the price
tends to `0 = c`. -/
theorem exercise_12_F_2b_instance :
    ∃ J : ℕ → ℕ, (∀ I : ℕ, 1 ≤ I →
      IsEntryEquilibrium (cournotEntryProfit (2 / 1) (1 / (1 * I)) 0) 1 (J I)) ∧
      Tendsto (fun I : ℕ => 2 / 1 - J I * fqJ 2 1 0 I (J I) / (1 * I)) atTop (𝓝 0) := by
  have h : ∀ I : ℕ, ∃ J, 1 ≤ I →
      IsEntryEquilibrium (cournotEntryProfit (2 / 1) (1 / (1 * I)) 0) 1 J := by
    intro I
    by_cases hI : 1 ≤ I
    · have hIr : (1 : ℝ) ≤ I := by exact_mod_cast hI
      have hpi : ∀ n : ℕ, cournotEntryProfit (2 / 1) (1 / (1 * I)) 0 n =
          4 * I / ((n : ℝ) + 1) ^ 2 := by
        intro n; unfold cournotEntryProfit; field_simp; ring
      obtain ⟨J, hJ⟩ := entry_equilibrium_exists
        (π := cournotEntryProfit (2 / 1) (1 / (1 * I)) 0) (K := 1)
        (by rw [hpi]; norm_num; linarith)
        ⟨2 * I, by
          rw [hpi, div_lt_one (by positivity)]
          push_cast
          nlinarith⟩
      exact ⟨J, fun _ => hJ⟩
    · exact ⟨0, fun h => absurd h hI⟩
  choose J hJ using h
  exact ⟨J, hJ, (exercise_12_F_2b (a := 2) (b := 1) (c := 0) (K := 1) one_pos (by norm_num)
    one_pos J (fun I hI => Or.inl (hJ I hI))).2.2.1⟩

/-! ### Exercise 12.F.3 -/

/-- The first-best welfare in the linear model with marginal cost `c` and entry cost `K`: one firm
producing the competitive output `(a − c)/b`, `W = (a − c)²/(2b) − K`. -/
noncomputable def firstBestWelfare (a b c K : ℝ) : ℝ := (a - c) ^ 2 / (2 * b) - K

/-- Welfare (12.E.5) with `J` firms each producing `q_J`, linear demand, constant marginal cost:
`(a − c)Q − bQ²/2 − JK` with `Q = Jq_J`. -/
theorem entryWelfare_linear_general {a b c K : ℝ} (q : ℕ → ℝ) (J : ℕ) :
    entryWelfare (fun s => a - b * s) (fun q => c * q) q K J =
      (a - c) * (J * q J) - b * (J * q J) ^ 2 / 2 - J * K := by
  unfold entryWelfare
  rw [intervalIntegral.integral_sub intervalIntegrable_const
    ((by fun_prop : Continuous fun s : ℝ => b * s).intervalIntegrable _ _),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_id]
  simp only [smul_eq_mul]
  ring

/-- **Exercise 12.F.3** (MWG, p. 435). In the linear two-stage Cournot entry model (inverse
demand `a − bq`, cost `cq`, entry cost `K`, market size fixed): the first-best welfare
`(a − c)²/(2b) − K` bounds the welfare of every configuration of `J ≥ 1` firms and is attained
by one firm producing `(a − c)/b`; and as `K → 0` the welfare loss of the free-entry equilibrium
relative to the first best, hence also relative to any number `J°` of firms (in particular the
welfare-optimal one), tends to `0`. -/
theorem exercise_12_F_3 {a b c : ℝ} (hac : c < a) (hb : 0 < b) :
    (∀ K, 0 ≤ K → ∀ (q : ℕ → ℝ) (J : ℕ), 1 ≤ J →
      entryWelfare (fun s => a - b * s) (fun q => c * q) q K J ≤ firstBestWelfare a b c K) ∧
    (∀ K, entryWelfare (fun s => a - b * s) (fun q => c * q) (fun _ => (a - c) / b) K 1 =
      firstBestWelfare a b c K) ∧
    ∀ ε, 0 < ε → ∃ δ, 0 < δ ∧ ∀ K, 0 < K → K < δ → ∀ J,
      IsEntryEquilibrium (cournotEntryProfit a b c) K J →
      firstBestWelfare a b c K - entryWelfare (fun s => a - b * s) (fun q => c * q)
          (fun J => (a - c) / (b * (J + 1))) K J < ε ∧
      ∀ (Jo : ℕ) (q : ℕ → ℝ), 1 ≤ Jo →
        entryWelfare (fun s => a - b * s) (fun q => c * q) q K Jo -
          entryWelfare (fun s => a - b * s) (fun q => c * q)
            (fun J => (a - c) / (b * (J + 1))) K J < ε := by
  have hFB : ∀ K, 0 ≤ K → ∀ (q : ℕ → ℝ) (J : ℕ), 1 ≤ J →
      entryWelfare (fun s => a - b * s) (fun q => c * q) q K J ≤ firstBestWelfare a b c K := by
    intro K hK q J hJ
    rw [entryWelfare_linear_general, firstBestWelfare]
    have hJ1 : (1 : ℝ) ≤ J := by exact_mod_cast hJ
    have e : (a - c) ^ 2 / (2 * b) - ((a - c) * (J * q J) - b * (J * q J) ^ 2 / 2) =
        (b * (J * q J) - (a - c)) ^ 2 / (2 * b) := by
      field_simp; ring
    have : 0 ≤ (b * (J * q J) - (a - c)) ^ 2 / (2 * b) := by positivity
    nlinarith
  refine ⟨hFB, fun K => ?_, fun ε hε => ?_⟩
  · rw [entryWelfare_linear_general, firstBestWelfare]
    push_cast
    field_simp
    ring
  set D := (a - c) ^ 2 with hD
  have hD0 : 0 < D := by have := sub_pos.2 hac; positivity
  refine ⟨min (ε / 4) (ε ^ 2 * b / (4 * (D + 1))), lt_min (by linarith) (by positivity),
    fun K hK hKδ J hJ => ?_⟩
  have hK1 : K < ε / 4 := lt_of_lt_of_le hKδ (min_le_left _ _)
  have hK2 : K < ε ^ 2 * b / (4 * (D + 1)) := lt_of_lt_of_le hKδ (min_le_right _ _)
  have hJ1 : 1 ≤ J := hJ.1
  have hnum := (example_12_E_1_number hb hK hJ1).1 hJ
  have hbK : 0 < b * K := by positivity
  rw [le_div_iff₀ hbK, div_lt_iff₀ hbK] at hnum
  obtain ⟨h1, h2⟩ := hnum
  rw [← hD] at h1 h2
  have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg J
  have hJp : (0 : ℝ) < (J : ℝ) + 1 := by linarith
  have hloss : firstBestWelfare a b c K - entryWelfare (fun s => a - b * s) (fun q => c * q)
      (fun J => (a - c) / (b * (J + 1))) K J = D / (2 * b * ((J : ℝ) + 1) ^ 2) + (J - 1) * K := by
    rw [entryWelfare_linear hb, firstBestWelfare, hD]
    field_simp
    ring
  -- first term `< 2K`
  have t1 : D / (2 * b * ((J : ℝ) + 1) ^ 2) < 2 * K := by
    rw [div_lt_iff₀ (by positivity)]
    have hle : ((J : ℝ) + 2) ^ 2 ≤ 4 * ((J : ℝ) + 1) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hle hbK.le]
  -- second term: `(JK)² ≤ DK/b < ε²/4`
  have hJK : (J : ℝ) * K < ε / 2 := by
    have hsq : ((J : ℝ) * K) ^ 2 * b ≤ D * K := by
      have hJJ : (J : ℝ) ^ 2 ≤ ((J : ℝ) + 1) ^ 2 := by nlinarith
      have := mul_le_mul_of_nonneg_right h1 hK.le
      have := mul_le_mul_of_nonneg_right hJJ (show 0 ≤ K ^ 2 * b by positivity)
      nlinarith
    have hDK : D * K < ε ^ 2 * b / 4 := by
      rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 4)]
      rw [lt_div_iff₀ (by positivity)] at hK2
      nlinarith
    by_contra hge
    push Not at hge
    have : (ε / 2) ^ 2 ≤ ((J : ℝ) * K) ^ 2 := pow_le_pow_left₀ (by positivity) hge 2
    nlinarith
  have hmain : firstBestWelfare a b c K - entryWelfare (fun s => a - b * s) (fun q => c * q)
      (fun J => (a - c) / (b * (J + 1))) K J < ε := by
    rw [hloss]; nlinarith
  refine ⟨hmain, fun Jo q hJo => ?_⟩
  have := hFB K hK.le q Jo hJo
  linarith

/-! ### Exercise 12.F.4 -/

/-- Firm `j`'s profit in the differentiated-products price game of Exercise 12.F.4 when it charges
`p`, the other active firms' prices sum to `s`, and `J` firms are active:
`p xⱼ = αp[γ − β(Jp/(p + s))]` (zero marginal cost). -/
noncomputable def dpProfit (α γ β J s p : ℝ) : ℝ := α * p * (γ - β * (J * p / (p + s)))

/-- `p ≥ 0` is a best response to the rivals' price sum `s`. -/
def IsDPBR (α γ β J s p : ℝ) : Prop :=
  0 ≤ p ∧ ∀ p', 0 ≤ p' → dpProfit α γ β J s p' ≤ dpProfit α γ β J s p

/-- **Exercise 12.F.4, best responses** (MWG, p. 435). If `γ < βJ`, write `D = βJ − γ > 0` and
let `u > 1` solve `u²D = βJ`. Against rivals' price sum `s > 0` the unique best response is
`p* = (u − 1)s`: `π(p*) − π(p) = αD(p + s − us)²/(p + s)`. -/
theorem exercise_12_F_4_br {α γ β J s u : ℝ} (hα : 0 < α) (hs : 0 < s) (hu : 1 < u)
    (hD : 0 < β * J - γ) (hu2 : u ^ 2 * (β * J - γ) = β * J) :
    IsDPBR α γ β J s ((u - 1) * s) ∧ ∀ p, IsDPBR α γ β J s p → p = (u - 1) * s := by
  have key : ∀ p, 0 ≤ p → dpProfit α γ β J s ((u - 1) * s) - dpProfit α γ β J s p =
      α * (β * J - γ) * (p + s - u * s) ^ 2 / (p + s) := by
    intro p hp
    unfold dpProfit
    have hps : 0 < p + s := by linarith
    have hus : 0 < u * s := by positivity
    rw [show (u - 1) * s + s = u * s by ring]
    have e1 : β * (J * p / (p + s)) = β * J * p / (p + s) := by ring
    have e2 : β * (J * ((u - 1) * s) / (u * s)) = β * J * ((u - 1) * s) / (u * s) := by ring
    rw [e1, e2]
    generalize hM : β * J = M at hu2 ⊢
    obtain ⟨D, rfl⟩ : ∃ D, γ = M - D := ⟨M - γ, by ring⟩
    have hMD : M = u ^ 2 * D := by rw [← hu2]; ring
    subst hMD
    field_simp
    ring
  have hnn : ∀ p, 0 ≤ p → 0 ≤ α * (β * J - γ) * (p + s - u * s) ^ 2 / (p + s) := by
    intro p hp
    have : 0 < p + s := by linarith
    positivity
  refine ⟨⟨by nlinarith, fun p hp => by linarith [key p hp, hnn p hp]⟩, fun p hp => ?_⟩
  have h1 := hp.2 ((u - 1) * s) (mul_nonneg (by linarith) hs.le)
  have h2 := key p hp.1
  have hps : 0 < p + s := by linarith [hp.1]
  have h3 : α * (β * J - γ) * (p + s - u * s) ^ 2 / (p + s) = 0 :=
    le_antisymm (by linarith) (hnn p hp.1)
  rw [div_eq_zero_iff] at h3
  rcases h3 with h3 | h3
  · have : α * (β * J - γ) ≠ 0 := by positivity
    have := (mul_eq_zero.1 h3).resolve_left this
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
    linarith
  · linarith

/-- The root `u = √(βJ/(βJ − γ)) > 1` of `u²(βJ − γ) = βJ` exists when `0 < γ < βJ`. -/
theorem exercise_12_F_4_root {γ β J : ℝ} (hγ : 0 < γ) (hD : 0 < β * J - γ) :
    ∃ u, 1 < u ∧ u ^ 2 * (β * J - γ) = β * J := by
  refine ⟨Real.sqrt (β * J / (β * J - γ)), ?_, ?_⟩
  · rw [Real.lt_sqrt zero_le_one, one_pow, lt_div_iff₀ hD]; linarith
  · rw [Real.sq_sqrt (div_nonneg (by linarith) hD.le)]; field_simp

/-- **Exercise 12.F.4, no best response when `γ ≥ βJ`** (MWG, p. 435). Then profit is strictly
increasing in own price: `π(p + 1) > π(p)` for every `p ≥ 0`, so no best response exists. -/
theorem exercise_12_F_4_no_br {α γ β J s : ℝ} (hα : 0 < α) (hβJ : 0 < β * J) (hγ : β * J ≤ γ)
    (hs : 0 < s) (p : ℝ) (hp : 0 ≤ p) : dpProfit α γ β J s p < dpProfit α γ β J s (p + 1) := by
  have e : dpProfit α γ β J s (p + 1) - dpProfit α γ β J s p =
      α * ((γ - β * J) + β * J * s ^ 2 / ((p + s) * (p + 1 + s))) := by
    unfold dpProfit
    have e1 : ∀ x, β * (J * x / (x + s)) = β * J * x / (x + s) := fun x => by ring
    rw [e1, e1]
    field_simp
    ring
  have : 0 < α * ((γ - β * J) + β * J * s ^ 2 / ((p + s) * (p + 1 + s))) := by
    have : 0 < β * J * s ^ 2 / ((p + s) * (p + 1 + s)) := by
      have : 0 < p + s := by linarith
      positivity
    have : 0 ≤ γ - β * J := by linarith
    positivity
  linarith

/-- **Exercise 12.F.4, symmetric equilibria** (MWG, p. 435). With `J ≥ 2` active firms,
`α, β, γ > 0` and a common price `p > 0`, `p` is a best response to the others' prices (sum
`(J − 1)p`) iff `γ = β(2 − 1/J)`, equivalently `J(2β − γ) = β`. So a symmetric equilibrium with
positive prices exists only on this knife-edge, which pins down the number of firms. -/
theorem exercise_12_F_4_symmetric {α γ β : ℝ} {J : ℕ} (hJ : 2 ≤ J) (hα : 0 < α) (hβ : 0 < β)
    (hγ : 0 < γ) {p : ℝ} (hp : 0 < p) :
    (IsDPBR α γ β J ((J - 1) * p) p ↔ γ = β * (2 - 1 / J)) ∧
    (γ = β * (2 - 1 / J) ↔ (J : ℝ) * (2 * β - γ) = β) := by
  have hJr : (2 : ℝ) ≤ J := by exact_mod_cast hJ
  have hJ1 : (0 : ℝ) < (J : ℝ) - 1 := by linarith
  have hJ0 : (0 : ℝ) < J := by linarith
  have hs : 0 < ((J : ℝ) - 1) * p := by positivity
  refine ⟨⟨fun hbr => ?_, fun hγe => ?_⟩, ⟨fun h => by rw [h]; field_simp; ring, fun h => ?_⟩⟩
  · by_cases hlt : γ < β * J
    · obtain ⟨u, hu, hu2⟩ := exercise_12_F_4_root (β := β) (J := (J : ℝ)) hγ (by linarith)
      have hpu := (exercise_12_F_4_br hα hs hu (by linarith) hu2).2 p hbr
      -- `(u − 1)(J − 1) = 1`, so `u = J/(J − 1)`
      have hu' : u * ((J : ℝ) - 1) = J := by
        have : p * ((u - 1) * ((J : ℝ) - 1) - 1) = 0 := by linear_combination -hpu
        have := (mul_eq_zero.1 this).resolve_left hp.ne'
        linarith
      have h4 : (u * ((J : ℝ) - 1)) ^ 2 * (β * J - γ) = β * J * ((J : ℝ) - 1) ^ 2 := by
        calc (u * ((J : ℝ) - 1)) ^ 2 * (β * J - γ) = (u ^ 2 * (β * J - γ)) * ((J : ℝ) - 1) ^ 2 :=
              by ring
          _ = _ := by rw [hu2]
      rw [hu'] at h4
      have h5 : (J : ℝ) * (γ * J - β * (2 * J - 1)) = 0 := by linear_combination (-1 : ℝ) * h4
      have h6 := (mul_eq_zero.1 h5).resolve_left hJ0.ne'
      field_simp
      linarith
    · exfalso
      push Not at hlt
      have := hbr.2 (p + 1) (by linarith)
      have := exercise_12_F_4_no_br hα (by positivity) hlt hs p hp.le
      linarith
  · have hD : 0 < β * J - γ := by
      rw [hγe]
      have : β * J - β * (2 - 1 / J) = β * ((J : ℝ) - 1) ^ 2 / J := by field_simp; ring
      rw [this]; positivity
    have hu : 1 < (J : ℝ) / (J - 1) := by rw [lt_div_iff₀ hJ1]; linarith
    have hu2 : ((J : ℝ) / (J - 1)) ^ 2 * (β * J - γ) = β * J := by
      rw [hγe]; field_simp; ring
    have h := (exercise_12_F_4_br hα hs hu hD hu2).1
    have e : ((J : ℝ) / (J - 1) - 1) * (((J : ℝ) - 1) * p) = p := by field_simp; ring
    rwa [e] at h
  · field_simp
    linarith

/-- **Exercise 12.F.4, indeterminacy** (MWG, p. 435). On the knife-edge `γ = β(2 − 1/J)`
(`J ≥ 2`, `α, β > 0`), every common price `p > 0` is a symmetric equilibrium of the stage-2 price
game; each firm sells `α(γ − β) > 0` whatever `p` is, and earns `αp(γ − β)`, which takes every
positive value as `p` varies. So the equilibrium price level, profits, and hence the entry
outcome, are not determined by the size `α` and substitution `β` parameters. -/
theorem exercise_12_F_4_indeterminate {α β : ℝ} {J : ℕ} (hJ : 2 ≤ J) (hα : 0 < α)
    (hβ : 0 < β) :
    let γ := β * (2 - 1 / J)
    0 < γ - β ∧ (∀ p, 0 < p → IsDPBR α γ β J ((J - 1) * p) p ∧
      α * (γ - β * (J * p / (p + (J - 1) * p))) = α * (γ - β) ∧
      dpProfit α γ β J ((J - 1) * p) p = α * p * (γ - β)) ∧
    ∀ π, 0 < π → ∃ p, 0 < p ∧ dpProfit α γ β J ((J - 1) * p) p = π := by
  intro γ
  have hJr : (2 : ℝ) ≤ J := by exact_mod_cast hJ
  have hJ0 : (0 : ℝ) < J := by linarith
  have hγβ : 0 < γ - β := by
    have : γ - β = β * ((J : ℝ) - 1) / J := by simp only [γ]; field_simp; ring
    rw [this]
    have : (0 : ℝ) < (J : ℝ) - 1 := by linarith
    positivity
  have hγ : 0 < γ := by linarith
  have hq : ∀ p, 0 < p → α * (γ - β * (J * p / (p + (J - 1) * p))) = α * (γ - β) := by
    intro p hp
    have : (J : ℝ) * p / (p + (J - 1) * p) = 1 := by
      rw [div_eq_one_iff_eq (by nlinarith)]; ring
    rw [this, mul_one]
  have hprof : ∀ p, 0 < p → dpProfit α γ β J ((J - 1) * p) p = α * p * (γ - β) := by
    intro p hp
    unfold dpProfit
    rw [show α * p * (γ - β * (J * p / (p + (J - 1) * p))) =
      p * (α * (γ - β * (J * p / (p + (J - 1) * p)))) by ring, hq p hp]
    ring
  refine ⟨hγβ, fun p hp => ⟨((exercise_12_F_4_symmetric hJ hα hβ hγ hp).1).2 rfl, hq p hp,
    hprof p hp⟩, fun π hπ => ⟨π / (α * (γ - β)), by positivity, ?_⟩⟩
  rw [hprof _ (by positivity)]
  field_simp

end MWG.MarketPower
