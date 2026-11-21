/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGAdverseSelection.ScreeningGen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Exercise 13.D.2: screening in insurance markets (Rothschild-Stiglitz)

MWG, Exercise 13.D.2, p. 476.

**The general model (`RSModel`).** Two states (`1`: no loss / good output, `2`: loss / bad
output) and two types: the "safe" type `true` (probability `q_S` of state `1`, prior probability
`λ`) and the "risky" type `false` (`q_R < q_S`). The endowment (or output) is `(a₁, a₂)`,
`a₂ < a₁`. An expected-utility maximizer with strictly increasing, strictly concave Bernoulli
utility `u` is described by `h = u⁻¹`: a contract is given by the utility levels `(v₁, v₂)` it
yields in the two states, i.e. by the wealth levels `(h v₁, h v₂)`. Type `b` gets
`V_b = q_b v₁ + (1 - q_b) v₂` and her firm the expected profit
`Pr_b = q_b (a₁ - h v₁) + (1 - q_b)(a₂ - h v₂)`; she accepts a contract iff `V_b ≥ ρ_b`. The game
is the `ScrGame` `M.game` with tie-breaking key `v₁ - v₂` (an indifferent individual takes the
contract with more coverage).

* `rs_characterization`: in every SPNE the risky type is fully insured at her fair price
  (`(v*, v*)`, `h v* = q_R a₁ + (1 - q_R) a₂`); the safe type takes a contract `k_S` that is
  fair for her (`Pr_S = 0`), partial (`k_S.2 < k_S.1`) and on the risky type's indifference
  curve (`V_R(k_S) = v*`); both firms earn zero.
* `rs_point_unique`: there is at most one such `k_S`.
* `rs_isEq` (existence criterion), `rs_no_eq` (nonexistence via a pooling contract).
* `log_isEq`, `log_no_eq`: with `u = log` (`h = exp`, shifted by a constant `κ`),
  `q_S = 2/3`, `q_R = 1/2`, `(a₁, a₂) = (10, 2) + κ`: the SPNE exists for `λ ≤ 9/19` and does
  not exist for `λ = 9/10`.

**The exercise.** Wealth `W`, loss `L`, loss probabilities `p_L < p_H`; a policy `(M, R)`
(premium, payment in case of loss).
* (a) `exercise_13_D_2a`: `(M, R) ↦ (W - M, W - L - M + R)` is a bijection from policies to
  wealth levels in the two states, under which expected utility and expected profit become
  functions of the wealth levels; `exercise_13_D_2a_log`: with `u = log`, positive wealth levels
  correspond bijectively to utility levels.
* (b) `insModel`; `exercise_13_D_2b`: the SPNE outcome (high risk: full insurance at her fair
  premium `p_H L`; low risk: partial insurance, fair for her, on the high-risk type's
  indifference curve); `exercise_13_D_2b_exists` (`W = 10`, `L = 8`, `p_L = 1/3`, `p_H = 1/2`,
  `u = log`, `λ = 1/10`) and `exercise_13_D_2b_nonexistence` (`λ = 9/10`): an equilibrium need not
  exist.

Departures: utility levels are used as coordinates, so `u` must map the wealth domain onto `ℝ`
(e.g. `log` on `(0, ∞)`); we assume `0 < p_L < p_H < 1` and `0 < L`; an indifferent individual
chooses the policy with more coverage.
-/

namespace MWG.AdverseSelection

open Set

/-- **Exercise 13.D.2** (MWG, p. 476). The two-type insurance (Rothschild-Stiglitz) screening
model in utility coordinates. -/
structure RSModel where
  qS : ℝ
  qR : ℝ
  a₁ : ℝ
  a₂ : ℝ
  h : ℝ → ℝ
  ρS : ℝ
  ρR : ℝ
  lam : ℝ

namespace RSModel

variable {M : RSModel}

/-- The probability of state `1` for type `b`. -/
def q (M : RSModel) (b : Bool) : ℝ := if b then M.qS else M.qR

/-- Expected utility of type `b` from the utility levels `k`. -/
def V (M : RSModel) (b : Bool) (k : ℝ × ℝ) : ℝ := M.q b * k.1 + (1 - M.q b) * k.2

/-- Expected profit on type `b`. -/
def Pr (M : RSModel) (b : Bool) (k : ℝ × ℝ) : ℝ :=
  M.q b * (M.a₁ - M.h k.1) + (1 - M.q b) * (M.a₂ - M.h k.2)

/-- Expected endowment `q_b a₁ + (1 - q_b) a₂` of type `b`. -/
def abar (M : RSModel) (b : Bool) : ℝ := M.q b * M.a₁ + (1 - M.q b) * M.a₂

/-- **Exercise 13.D.2** (MWG, p. 476). The screening game. -/
noncomputable def game (M : RSModel) : ScrGame where
  U := M.V
  P := M.Pr
  ρ b := if b then M.ρS else M.ρR
  key k := k.1 - k.2
  lam := M.lam
  adm _ := True

/-- The assumptions: `0 < q_R < q_S < 1`, `0 < λ < 1`, `a₂ < a₁`, and `h = u⁻¹` strictly
increasing, strictly convex and continuous (`u` strictly increasing and strictly concave). -/
structure Valid (M : RSModel) : Prop where
  qR_pos : 0 < M.qR
  q_lt : M.qR < M.qS
  qS_lt : M.qS < 1
  lam_pos : 0 < M.lam
  lam_lt : M.lam < 1
  a_lt : M.a₂ < M.a₁
  h_mono : StrictMono M.h
  h_conv : StrictConvexOn ℝ univ M.h
  h_cont : Continuous M.h

theorem q_true (M : RSModel) : M.q true = M.qS := rfl
theorem q_false (M : RSModel) : M.q false = M.qR := rfl

theorem Valid.q_pos (hM : M.Valid) (b : Bool) : 0 < M.q b := by
  cases b
  · exact hM.qR_pos
  · exact hM.qR_pos.trans hM.q_lt

theorem Valid.q_lt_one (hM : M.Valid) (b : Bool) : M.q b < 1 := by
  cases b
  · exact hM.q_lt.trans hM.qS_lt
  · exact hM.qS_lt

theorem game_inj (M : RSModel) : M.game.Inj := by
  intro b k k' hu hk
  simp only [game, V] at hu hk
  have h2 : k.2 = k'.2 := by
    have : M.q b * (k.1 - k.2) = M.q b * (k'.1 - k'.2) := by rw [hk]
    nlinarith
  exact Prod.ext (by linarith) h2

theorem V_diag (M : RSModel) (b : Bool) (v : ℝ) : M.V b (v, v) = v := by
  simp only [V]; ring

theorem Pr_diag (M : RSModel) (b : Bool) (v : ℝ) : M.Pr b (v, v) = M.abar b - M.h v := by
  simp only [Pr, abar]; ring

theorem abar_lt (hM : M.Valid) : M.abar false < M.abar true := by
  simp only [abar, q_true, q_false]
  nlinarith [mul_pos (sub_pos.2 hM.q_lt) (sub_pos.2 hM.a_lt)]

/-- Jensen's inequality: `h(V_b(k)) ≤ q_b h(k₁) + (1 - q_b) h(k₂)`, so
`Pr_b(k) ≤ a̅_b - h(V_b(k))`. -/
theorem Pr_le (hM : M.Valid) (b : Bool) (k : ℝ × ℝ) : M.Pr b k ≤ M.abar b - M.h (M.V b k) := by
  have := hM.h_conv.convexOn.2 (mem_univ k.1) (mem_univ k.2) (hM.q_pos b).le
    (sub_nonneg.2 (hM.q_lt_one b).le) (by ring)
  simp only [smul_eq_mul] at this
  simp only [Pr, abar, V]
  linarith

/-- Strict Jensen: `Pr_b(k) < a̅_b - h(V_b(k))` unless `k₁ = k₂`. -/
theorem Pr_lt (hM : M.Valid) (b : Bool) {k : ℝ × ℝ} (hk : k.1 ≠ k.2) :
    M.Pr b k < M.abar b - M.h (M.V b k) := by
  have := hM.h_conv.2 (mem_univ k.1) (mem_univ k.2) hk (hM.q_pos b)
    (sub_pos.2 (hM.q_lt_one b)) (by ring)
  simp only [smul_eq_mul] at this
  simp only [Pr, abar, V]
  linarith

theorem V_add (M : RSModel) (b : Bool) (k d : ℝ × ℝ) (τ : ℝ) :
    M.V b (k.1 + τ * d.1, k.2 + τ * d.2) = M.V b k + τ * (M.q b * d.1 + (1 - M.q b) * d.2) := by
  simp only [V]; ring

/-- Profits change continuously along a line. -/
theorem Pr_cont (hM : M.Valid) (b : Bool) (k d : ℝ × ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ τ₀, 0 < τ₀ ∧ ∀ τ, 0 < τ → τ ≤ τ₀ → M.Pr b k - η < M.Pr b (k.1 + τ * d.1, k.2 + τ * d.2) := by
  have hc : Continuous fun τ : ℝ => M.Pr b (k.1 + τ * d.1, k.2 + τ * d.2) := by
    have := hM.h_cont
    simp only [Pr]
    fun_prop
  have hev := (hc.tendsto 0).eventually (lt_mem_nhds (a := M.Pr b k - η)
    (by simp only [zero_mul, add_zero, Prod.mk.eta]; linarith))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨ε / 2, half_pos hε, fun τ hτ hτle => hball ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_pos hτ]
  linarith

/-- **Lemma 13.D.1** for the insurance model: zero profits in every SPNE. -/
theorem game_zero (hM : M.Valid) {A₁ A₂ : Finset (ℝ × ℝ)} (h : M.game.IsEq A₁ A₂) :
    M.game.profit A₁ A₂ = 0 ∧ M.game.profit A₂ A₁ = 0 := by
  refine ScrGame.IsEq.zero (game_inj M) hM.lam_pos.le hM.lam_lt.le
    (fun δ k => (k.1 + δ, k.2 + δ)) (fun _ _ _ _ => trivial) (fun δ b k => ?_)
    (fun δ k => ?_) (fun b k η hη => ?_) h
  · simp only [game, V]; ring
  · simp only [game]; ring
  · obtain ⟨τ₀, hτ₀, hτ⟩ := Pr_cont hM b k (1, 1) hη
    refine ⟨τ₀, hτ₀, fun δ hδ hδle => ?_⟩
    have := hτ δ hδ hδle
    simp only [mul_one] at this
    exact this

/-- From a contract `e` with `Pr_S(e) ≥ 0` that the risky type values below `v*`, there is a
contract the safe type strictly prefers, profitable on her, still valued below `v*` by the risky
type (move towards full insurance along the safe type's indifference curve, then sweeten). -/
theorem exists_improve (hM : M.Valid) {vs : ℝ} (hv : M.h vs = M.abar false) {e : ℝ × ℝ}
    (he0 : 0 ≤ M.Pr true e) (heR : M.V false e < vs) :
    ∃ k', M.V true e < M.V true k' ∧ 0 < M.Pr true k' ∧ M.V false k' < vs := by
  have hab := abar_lt hM
  -- a contract with the same value for the safe type and a strictly positive profit
  obtain ⟨z, hzS, hzP, hzR⟩ : ∃ z, M.V true z = M.V true e ∧ 0 < M.Pr true z ∧
      M.V false z < vs := by
    by_cases hd : e.1 = e.2
    · refine ⟨e, rfl, ?_, heR⟩
      have he : e = (e.1, e.1) := Prod.ext rfl hd.symm
      rw [he, Pr_diag]
      rw [he, V_diag] at heR
      have := hM.h_mono heR
      linarith
    · set m := M.V true e
      set D := vs - M.V false e
      set A := |m - M.V false e|
      have hD : 0 < D := by simp only [D]; linarith
      have hA : 0 ≤ A := abs_nonneg _
      set τ := min (1 / 2) (D / (2 * (A + 1)))
      have hτ0 : 0 < τ := lt_min (by norm_num) (by positivity)
      have hτ1 : τ ≤ 1 / 2 := min_le_left _ _
      have hτ2 : τ * (2 * (A + 1)) ≤ D :=
        (le_div_iff₀ (by positivity)).1 (min_le_right _ _)
      refine ⟨((1 - τ) * e.1 + τ * m, (1 - τ) * e.2 + τ * m), ?_, ?_, ?_⟩
      · simp only [V, m]; ring
      · have c1 := hM.h_conv.convexOn.2 (mem_univ e.1) (mem_univ m) (by linarith : 0 ≤ 1 - τ)
          hτ0.le (by ring)
        have c2 := hM.h_conv.convexOn.2 (mem_univ e.2) (mem_univ m) (by linarith : 0 ≤ 1 - τ)
          hτ0.le (by ring)
        have j := Pr_lt hM true hd
        simp only [smul_eq_mul] at c1 c2
        have hq := hM.q_pos true
        have hq1 := hM.q_lt_one true
        simp only [Pr, abar] at j he0 ⊢
        have k1 := mul_le_mul_of_nonneg_left c1 hq.le
        have k2 := mul_le_mul_of_nonneg_left c2 (sub_nonneg.2 hq1.le)
        nlinarith [mul_lt_mul_of_pos_left j hτ0]
      · have hle : τ * (m - M.V false e) ≤ τ * A :=
          mul_le_mul_of_nonneg_left (le_abs_self _) hτ0.le
        have : M.V false ((1 - τ) * e.1 + τ * m, (1 - τ) * e.2 + τ * m) =
            M.V false e + τ * (m - M.V false e) := by simp only [V]; ring
        rw [this]
        nlinarith
  -- sweeten it slightly
  obtain ⟨τ₀, hτ₀, hτ⟩ := Pr_cont hM true z (1, 1) (half_pos hzP)
  set δ := min τ₀ ((vs - M.V false z) / 2)
  have hδ : 0 < δ := lt_min hτ₀ (by linarith)
  have hδ2 : δ ≤ (vs - M.V false z) / 2 := min_le_right _ _
  have hP := hτ δ hδ (min_le_left _ _)
  simp only [mul_one] at hP
  refine ⟨(z.1 + δ, z.2 + δ), ?_, by linarith, ?_⟩
  · have := V_add M true z (1, 1) δ
    simp only [mul_one] at this
    rw [this, hzS]; simp only [q_true]; linarith
  · have := V_add M false z (1, 1) δ
    simp only [mul_one] at this
    rw [this]; simp only [q_false]; linarith

/-- **Exercise 13.D.2(b)** (MWG, p. 476), the general characterization. Suppose `h v* = a̅_R`,
the risky type's outside option is worse than `v*`, and the safe type's outside option is the
value of a contract `e` with `Pr_S(e) ≥ 0` and `V_R(e) < v*` (both hold for insurance and for
Exercise 13.D.3(c)). In every SPNE the risky type takes full insurance `(v*, v*)` at her fair
price, the safe type takes a contract `k_S` with `Pr_S(k_S) = 0`, `V_R(k_S) = v*` and
`k_S.2 < k_S.1` (partial insurance), and both firms earn zero. -/
theorem rs_characterization (hM : M.Valid) {vs : ℝ} (hv : M.h vs = M.abar false)
    (hR : M.ρR < vs) (hS : ∃ e : ℝ × ℝ, M.V true e = M.ρS ∧ 0 ≤ M.Pr true e ∧ M.V false e < vs)
    {A₁ A₂ : Finset (ℝ × ℝ)} (h : M.game.IsEq A₁ A₂) :
    ∃ kS, M.game.Chooses false (A₁ ∪ A₂) (vs, vs) ∧ M.game.Chooses true (A₁ ∪ A₂) kS ∧
      M.Pr true kS = 0 ∧ M.V false kS = vs ∧ kS.2 < kS.1 ∧
      M.game.profit A₁ A₂ = 0 ∧ M.game.profit A₂ A₁ = 0 := by
  have hI := game_inj M
  have hz := game_zero hM h
  have hl0 := hM.lam_pos
  have hl1 := hM.lam_lt
  have hab := abar_lt hM
  have hU : ∀ b k, M.game.U b k = M.V b k := fun _ _ => rfl
  have hP : ∀ b k, M.game.P b k = M.Pr b k := fun _ _ => rfl
  have hρf : M.game.ρ false = M.ρR := rfl
  have hρt : M.game.ρ true = M.ρS := rfl
  -- full insurance slightly above the risky type's utility is profitable
  have devR : ∀ v, M.ρR ≤ v → v < vs → (∀ k ∈ A₁ ∪ A₂, M.V false k < v) → False := by
    intro v hv0 hvs hlt
    have hhv : M.h v < M.abar false := hv ▸ hM.h_mono hvs
    refine ScrGame.IsEq.dev_false hI hl1 hl0.le h hz.1 (k' := (v, v)) trivial
      (by rw [hρf, hU, V_diag]; exact hv0) (fun k hk => ?_) (by rw [hP, Pr_diag]; linarith)
      (by rw [hP, Pr_diag]; linarith)
    rw [hU, hU, V_diag]; exact hlt k (Finset.mem_union_right _ hk)
  obtain ⟨kR, hkR⟩ : ∃ kR, M.game.Chooses false (A₁ ∪ A₂) kR := by
    by_contra hno
    refine devR M.ρR le_rfl hR fun k hk => ?_
    by_contra hle
    exact hno (ScrGame.exists_chooses false ⟨k, hk, by rw [hρf, hU]; linarith⟩)
  have hRge : vs ≤ M.V false kR := by
    by_contra hlt
    rw [not_le] at hlt
    have h0 : M.ρR ≤ M.V false kR := hkR.2.1
    refine devR ((M.V false kR + vs) / 2) (by linarith) (by linarith) fun k hk => ?_
    have := hkR.2.2.1 k hk
    rw [hU, hU] at this
    linarith
  have hPR : M.Pr false kR ≤ 0 := by
    have := Pr_le hM false kR
    have := hM.h_mono.monotone hRge
    linarith
  -- the safe type works
  obtain ⟨kS, hkS⟩ : ∃ kS, M.game.Chooses true (A₁ ∪ A₂) kS := by
    by_contra hno
    obtain ⟨e, he1, he2, he3⟩ := hS
    obtain ⟨k', hk1, hk2, hk3⟩ := exists_improve hM hv he2 he3
    refine ScrGame.IsEq.dev_true' hI hl0 h hz hkR trivial (k' := k')
      (by rw [hρt, hU]; linarith) (fun k hk => ?_) (by rw [hU, hU]; linarith) hk2
    rw [hU, hU]
    by_contra hle
    exact hno (ScrGame.exists_chooses true ⟨k, hk, by rw [hρt, hU]; linarith⟩)
  -- no profit on the safe type
  have hPS : M.Pr true kS ≤ 0 := by
    by_contra hpos
    rw [not_le] at hpos
    set qm := (M.qR + M.qS) / 2
    obtain ⟨τ₀, hτ₀, hτ⟩ := Pr_cont hM true kS (1 - qm, -qm) (half_pos hpos)
    have hP' := hτ τ₀ hτ₀ le_rfl
    have hVt := V_add M true kS (1 - qm, -qm) τ₀
    have hVf := V_add M false kS (1 - qm, -qm) τ₀
    simp only [q_true, q_false] at hVt hVf
    have hq := hM.q_lt
    have e1 : M.qS * (1 - qm) + (1 - M.qS) * -qm = M.qS - qm := by ring
    have e2 : M.qR * (1 - qm) + (1 - M.qR) * -qm = M.qR - qm := by ring
    rw [e1] at hVt
    rw [e2] at hVf
    have h1 : 0 < τ₀ * (M.qS - qm) := mul_pos hτ₀ (by simp only [qm]; linarith)
    have h2 : τ₀ * (M.qR - qm) < 0 := mul_neg_of_pos_of_neg hτ₀ (by simp only [qm]; linarith)
    have hkSR := hkR.2.2.1 kS hkS.1
    refine ScrGame.IsEq.dev_true' hI hl0 h hz hkR trivial
      (k' := (kS.1 + τ₀ * (1 - qm), kS.2 + τ₀ * -qm)) ?_ (fun k hk => ?_) ?_
      (by change 0 < M.Pr true _; linarith)
    · have := hkS.2.1; rw [hρt, hU] at this; rw [hρt, hU, hVt]; linarith
    · have := hkS.2.2.1 k hk; rw [hU, hU] at this; rw [hU, hU, hVt]; linarith
    · rw [hU, hU] at hkSR; rw [hU, hU, hVf]; linarith
  -- both chosen contracts break even
  have htot := ScrGame.profit_add (G := M.game) A₁ A₂
  rw [hz.1, hz.2, ScrGame.typeProfit_add hI hkR, ScrGame.typeProfit_add hI hkS, hP, hP] at htot
  have hlam : M.game.lam = M.lam := rfl
  rw [hlam] at htot
  have hPR0 : M.Pr false kR = 0 := by nlinarith
  have hPS0 : M.Pr true kS = 0 := by nlinarith
  -- the risky type is fully insured at her fair price
  have hdiag : kR.1 = kR.2 := by
    by_contra hne
    have := Pr_lt hM false hne
    have := hM.h_mono.monotone hRge
    linarith
  have hkReq : kR = (vs, vs) := by
    have hk : kR = (kR.1, kR.1) := Prod.ext rfl hdiag.symm
    rw [hk, Pr_diag] at hPR0
    have : M.h kR.1 = M.h vs := by linarith
    rw [hk, hM.h_mono.injective this]
  rw [hkReq] at hkR
  have hVRS : M.V false kS ≤ vs := by
    have := hkR.2.2.1 kS hkS.1
    rw [hU, hU, V_diag] at this; exact this
  have hVSS : vs ≤ M.V true kS := by
    have := hkS.2.2.1 (vs, vs) hkR.1
    rw [hU, hU, V_diag] at this; exact this
  have hpart : kS.2 < kS.1 := by
    by_contra hle
    rw [not_lt] at hle
    have hd : M.V true kS - M.V false kS = (M.qS - M.qR) * (kS.1 - kS.2) := by
      simp only [V, q_true, q_false]; ring
    have hq := hM.q_lt
    have h1 : (M.qS - M.qR) * (kS.1 - kS.2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    have h2 : (M.qS - M.qR) * (kS.1 - kS.2) = 0 := by linarith
    have h3 : kS.1 = kS.2 := by
      rcases mul_eq_zero.1 h2 with h4 | h4
      · linarith
      · linarith
    have hk : kS = (kS.1, kS.1) := Prod.ext rfl h3.symm
    have hm : kS.1 = vs := by
      have := hVSS; rw [hk, V_diag] at this
      have := hVRS; rw [hk, V_diag] at this
      linarith
    rw [hk, Pr_diag, hm] at hPS0
    linarith
  refine ⟨kS, hkR, hkS, hPS0, le_antisymm hVRS ?_, hpart, hz.1, hz.2⟩
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨k', hk1, hk2, hk3⟩ := exists_improve hM hv hPS0.ge hlt
  refine ScrGame.IsEq.dev_true' hI hl0 h hz hkR trivial (k' := k') ?_ (fun k hk => ?_)
    (by rw [hU, hU, V_diag]; exact hk3) hk2
  · have := hkS.2.1; rw [hρt, hU] at this; rw [hρt, hU]; linarith
  · have := hkS.2.2.1 k hk; rw [hU, hU] at this; rw [hU, hU]; linarith

/-- The safe type's equilibrium contract is unique: the risky type's indifference line through
`(v*, v*)` meets the safe type's zero-profit curve at most once with `k₂ < k₁`. -/
theorem rs_point_lt (hM : M.Valid) {vs : ℝ} (hv : M.h vs = M.abar false) {k k' : ℝ × ℝ}
    (hk : M.Pr true k = 0 ∧ M.V false k = vs ∧ k.2 < k.1)
    (hk' : M.Pr true k' = 0 ∧ M.V false k' = vs ∧ k'.2 < k'.1)
    (hlt : k.1 - k.2 < k'.1 - k'.2) : False := by
  have hab := abar_lt hM
  set s := k.1 - k.2
  set s' := k'.1 - k'.2
  have hs : 0 < s := by simp only [s]; linarith [hk.2.2]
  have hqR := hM.qR_pos
  have hqR1 := hM.q_lt_one false
  rw [q_false] at hqR1
  have hk1 : k.1 = vs + (1 - M.qR) * s := by
    have := hk.2.1; simp only [V, q_false] at this; simp only [s]; linear_combination this
  have hk2 : k.2 = vs - M.qR * s := by
    have := hk.2.1; simp only [V, q_false] at this; simp only [s]; linear_combination this
  have hk1' : k'.1 = vs + (1 - M.qR) * s' := by
    have := hk'.2.1; simp only [V, q_false] at this; simp only [s']; linear_combination this
  have hk2' : k'.2 = vs - M.qR * s' := by
    have := hk'.2.1; simp only [V, q_false] at this; simp only [s']; linear_combination this
  set t := s / s'
  have hs' : 0 < s' := hs.trans hlt
  have ht0 : 0 < t := div_pos hs hs'
  have ht1 : t < 1 := (div_lt_one hs').2 hlt
  have hts : t * s' = s := by simp only [t]; field_simp
  have hne1 : vs ≠ k'.1 := by
    rw [hk1']; nlinarith [mul_pos (sub_pos.2 hqR1) hs']
  have c1 := hM.h_conv.2 (mem_univ vs) (mem_univ k'.1) hne1 (sub_pos.2 ht1) ht0 (by ring)
  have c2 := hM.h_conv.convexOn.2 (mem_univ vs) (mem_univ k'.2) (sub_pos.2 ht1).le ht0.le
    (by ring)
  simp only [smul_eq_mul] at c1 c2
  have e1 : (1 - t) * vs + t * k'.1 = k.1 := by rw [hk1', hk1, ← hts]; ring
  have e2 : (1 - t) * vs + t * k'.2 = k.2 := by rw [hk2', hk2, ← hts]; ring
  rw [e1] at c1
  rw [e2] at c2
  have hq := hM.q_pos true
  have hq1 := hM.q_lt_one true
  have h0 := hk.1
  have h0' := hk'.1
  simp only [Pr, abar, q_true, q_false] at h0 h0' hv hab
  rw [q_true] at hq hq1
  have k1 := mul_lt_mul_of_pos_left c1 hq
  have k2 := mul_le_mul_of_nonneg_left c2 (sub_nonneg.2 hq1.le)
  nlinarith [mul_pos (sub_pos.2 ht1) (sub_pos.2 hab)]

theorem rs_point_unique (hM : M.Valid) {vs : ℝ} (hv : M.h vs = M.abar false) {k k' : ℝ × ℝ}
    (hk : M.Pr true k = 0 ∧ M.V false k = vs ∧ k.2 < k.1)
    (hk' : M.Pr true k' = 0 ∧ M.V false k' = vs ∧ k'.2 < k'.1) : k = k' := by
  rcases lt_trichotomy (k.1 - k.2) (k'.1 - k'.2) with hlt | heq | hgt
  · exact (rs_point_lt hM hv hk hk' hlt).elim
  · exact game_inj M false k k'
      (by change M.V false k = M.V false k'; rw [hk.2.1, hk'.2.1]) heq
  · exact (rs_point_lt hM hv hk' hk hgt).elim

/-- **Exercise 13.D.2(b)** (MWG, p. 476), an existence criterion. Let `k_S` be the safe type's
contract of `rs_characterization`. If every contract `k` that the safe type weakly prefers to
`k_S` either is unprofitable on her when the risky type does not strictly prefer it to full
insurance, or, when the risky type strictly prefers it, loses money once the risky type's best
response is taken into account (`λ Pr_S(k) + (1 - λ)(a̅_R - h(V_R(k))) ≤ 0`), then both firms
offering `{(v*, v*), k_S}` is an SPNE. -/
theorem rs_isEq (hM : M.Valid) {vs : ℝ} (hv : M.h vs = M.abar false) {kS : ℝ × ℝ}
    (hP : M.Pr true kS = 0) (hVR : M.V false kS = vs) (hlt : kS.2 < kS.1) (hρR : M.ρR ≤ vs)
    (hρS : M.ρS ≤ M.V true kS)
    (hN : ∀ k, M.V true kS ≤ M.V true k → (M.V false k ≤ vs → M.Pr true k ≤ 0) ∧
      (vs < M.V false k → M.lam * M.Pr true k + (1 - M.lam) * (M.abar false - M.h (M.V false k))
        ≤ 0)) :
    M.game.IsEq {(vs, vs), kS} {(vs, vs), kS} := by
  have hI := game_inj M
  have hl0 := hM.lam_pos
  have hl1 := hM.lam_lt
  set A : Finset (ℝ × ℝ) := {(vs, vs), kS} with hA
  have hU : ∀ b k, M.game.U b k = M.V b k := fun _ _ => rfl
  have hPd : ∀ b k, M.game.P b k = M.Pr b k := fun _ _ => rfl
  have hρf : M.game.ρ false = M.ρR := rfl
  have hρt : M.game.ρ true = M.ρS := rfl
  have hkey : ∀ k, M.game.key k = k.1 - k.2 := fun _ => rfl
  have hVSS : vs < M.V true kS := by
    have : M.V true kS - M.V false kS = (M.qS - M.qR) * (kS.1 - kS.2) := by
      simp only [V, q_true, q_false]; ring
    nlinarith [mul_pos (sub_pos.2 hM.q_lt) (sub_pos.2 hlt)]
  have hmemd : (vs, vs) ∈ A := by simp [hA]
  have hmemS : kS ∈ A := by simp [hA]
  have hmemA : ∀ k ∈ A, k = (vs, vs) ∨ k = kS := fun k hk => by
    simpa [hA] using hk
  have hchR : M.game.Chooses false (A ∪ A) (vs, vs) := by
    rw [Finset.union_self]
    refine ⟨hmemd, by rw [hρf, hU, V_diag]; exact hρR, fun k hk => ?_, fun k hk hu => ?_⟩
    · rw [hU, hU, V_diag]
      rcases hmemA k hk with rfl | rfl
      · rw [V_diag]
      · rw [hVR]
    · rw [hkey, hkey]
      rcases hmemA k hk with rfl | rfl
      · exact le_rfl
      · simp only; linarith
  have hchS : M.game.Chooses true (A ∪ A) kS := by
    rw [Finset.union_self]
    refine ScrGame.chooses_of_strict hmemS (by rw [hρt, hU]; exact hρS) fun k hk hne => ?_
    rcases hmemA k hk with rfl | rfl
    · rw [hU, hU, V_diag]; exact hVSS
    · exact absurd rfl hne
  have hzero : M.game.profit A A = 0 := by
    unfold ScrGame.profit
    rw [ScrGame.typeProfit_of_chooses hI hchR, ScrGame.typeProfit_of_chooses hI hchS, hPd, hPd,
      Pr_diag, hv, hP]
    ring
  -- the risky type never yields a profit
  have hYle : ∀ B k', M.game.Chooses false (B ∪ A) k' →
      M.Pr false k' ≤ M.abar false - M.h (M.V false k') ∧ vs ≤ M.V false k' := by
    intro B k' hk'
    have h1 := hk'.2.2.1 (vs, vs) (Finset.mem_union_right _ hmemd)
    rw [hU, hU, V_diag] at h1
    exact ⟨Pr_le hM false k', h1⟩
  have hY : ∀ B, M.game.typeProfit false B A ≤ 0 := by
    intro B
    by_cases hex : ∃ k', M.game.Chooses false (B ∪ A) k'
    · obtain ⟨k', hk'⟩ := hex
      rw [ScrGame.typeProfit_of_chooses hI hk', hPd]
      obtain ⟨h1, h2⟩ := hYle B k' hk'
      have := hM.h_mono.monotone h2
      exact mul_nonpos_of_nonneg_of_nonpos (SigModel.share_nonneg _ _ _) (by linarith)
    · rw [ScrGame.typeProfit_of_not hex]
  have hdev : ∀ B, M.game.Menu B → M.game.profit B A ≤ 0 := by
    intro B _
    have hYB := hY B
    unfold ScrGame.profit
    have hlam : M.game.lam = M.lam := rfl
    rw [hlam]
    by_cases hexS : ∃ k, M.game.Chooses true (B ∪ A) k
    · obtain ⟨k, hk⟩ := hexS
      rw [ScrGame.typeProfit_of_chooses hI hk, hPd]
      have hge := hk.2.2.1 kS (Finset.mem_union_right _ hmemS)
      rw [hU, hU] at hge
      rcases le_or_gt (M.Pr true k) 0 with hPk | hPk
      · have := mul_nonpos_of_nonneg_of_nonpos (SigModel.share_nonneg B A k) hPk
        nlinarith
      · have hkA : k ∉ A := by
          intro hm
          rcases hmemA k hm with rfl | rfl
          · rw [V_diag] at hge; linarith
          · linarith
        have hkB : k ∈ B := by
          rcases Finset.mem_union.1 hk.1 with hm | hm
          · exact hm
          · exact absurd hm hkA
        have hsh : SigModel.share B A k = 1 := by simp [SigModel.share, hkB, hkA]
        have hRk : vs < M.V false k := by
          by_contra hle
          rw [not_lt] at hle
          linarith [(hN k hge).1 hle]
        obtain ⟨k', hk'⟩ := ScrGame.exists_chooses (G := M.game) false
          ⟨k, hk.1, by rw [hρf, hU]; linarith⟩
        have hk'k := hk'.2.2.1 k hk.1
        rw [hU, hU] at hk'k
        have hk'A : k' ∉ A := by
          intro hm
          rcases hmemA k' hm with rfl | rfl
          · rw [V_diag] at hk'k; linarith
          · linarith
        have hk'B : k' ∈ B := by
          rcases Finset.mem_union.1 hk'.1 with hm | hm
          · exact hm
          · exact absurd hm hk'A
        have hpR : M.game.typeProfit false B A = M.Pr false k' := by
          rw [ScrGame.typeProfit_of_chooses hI hk', hPd]
          simp [SigModel.share, hk'B, hk'A]
        have h1 := (hYle B k' hk').1
        have h2 := hM.h_mono.monotone hk'k
        have h3 := (hN k hge).2 hRk
        rw [hpR, hsh, one_mul]
        nlinarith
    · rw [ScrGame.typeProfit_of_not hexS]
      nlinarith
  refine ⟨fun _ _ => trivial, fun _ _ => trivial, fun B hB => ?_, fun B hB => ?_⟩ <;>
    rw [hzero] <;> exact hdev B hB

/-- **Exercise 13.D.2(b)** (MWG, p. 476), nonexistence. If some contract `k'` gives both types
strictly more than their equilibrium contracts (`(v*, v*)` and the safe type's `k_S`) at a
positive expected profit, no SPNE exists. -/
theorem rs_no_eq (hM : M.Valid) {vs : ℝ} (hv : M.h vs = M.abar false) (hR : M.ρR < vs)
    (hS : ∃ e : ℝ × ℝ, M.V true e = M.ρS ∧ 0 ≤ M.Pr true e ∧ M.V false e < vs)
    {kS : ℝ × ℝ} (hkS : M.Pr true kS = 0 ∧ M.V false kS = vs ∧ kS.2 < kS.1) {k' : ℝ × ℝ}
    (hS' : M.V true kS < M.V true k') (hR' : vs < M.V false k')
    (hpos : 0 < (1 - M.lam) * M.Pr false k' + M.lam * M.Pr true k') :
    ¬ ∃ A₁ A₂, M.game.IsEq A₁ A₂ := by
  rintro ⟨A₁, A₂, h⟩
  obtain ⟨kS', hkR, hkS', hP0, hV0, hlt0, hz, -⟩ := rs_characterization hM hv hR hS h
  have he := rs_point_unique hM hv ⟨hP0, hV0, hlt0⟩ hkS
  rw [he] at hkS'
  refine ScrGame.IsEq.dev_both (game_inj M) h hz (k' := k') trivial (fun b => ?_)
    (fun b k hk => ?_) hpos
  · cases b
    · have := hkR.2.1; change M.ρR ≤ M.V false (vs, vs) at this
      rw [V_diag] at this; change M.ρR ≤ M.V false k'; linarith
    · have := hkS'.2.1; change M.ρS ≤ M.V true kS at this
      change M.ρS ≤ M.V true k'; linarith
  · cases b
    · have := hkR.2.2.1 k (Finset.mem_union_right _ hk)
      change M.V false k ≤ M.V false (vs, vs) at this
      rw [V_diag] at this; change M.V false k < M.V false k'; linarith
    · have := hkS'.2.2.1 k (Finset.mem_union_right _ hk)
      change M.V true k ≤ M.V true kS at this
      change M.V true k < M.V true k'; linarith

/-- The tangent line of `exp` at `log x₀`: `x₀ (1 + v - log x₀) ≤ exp v`. -/
theorem exp_ge_tangent {x0 : ℝ} (hx0 : 0 < x0) (v : ℝ) :
    x0 * (1 + (v - Real.log x0)) ≤ Real.exp v := by
  have h1 : Real.exp v = x0 * Real.exp (v - Real.log x0) := by
    rw [← Real.exp_log hx0, ← Real.exp_add, Real.exp_log hx0]; ring_nf
  rw [h1]
  have := Real.add_one_le_exp (v - Real.log x0)
  nlinarith

theorem log9_add_log4 : Real.log 9 + Real.log 4 = 2 * Real.log 6 := by
  rw [← Real.log_mul (by norm_num) (by norm_num), two_mul,
    ← Real.log_mul (by norm_num) (by norm_num)]
  norm_num

theorem log4_lt_log9 : Real.log 4 < Real.log 9 := Real.log_lt_log (by norm_num) (by norm_num)

/-- The model with `u = log` (`h = exp + κ`), `q_S = 2/3`, `q_R = 1/2`, `(a₁, a₂) = (10, 2) + κ`
satisfies the assumptions. -/
theorem log_valid (M : RSModel) {κ : ℝ} (hqS : M.qS = 2 / 3) (hqR : M.qR = 1 / 2)
    (ha1 : M.a₁ = 10 + κ) (ha2 : M.a₂ = 2 + κ) (hh : M.h = fun v => Real.exp v + κ)
    (hl0 : 0 < M.lam) (hl1 : M.lam < 1) : M.Valid where
  qR_pos := by rw [hqR]; norm_num
  q_lt := by rw [hqR, hqS]; norm_num
  qS_lt := by rw [hqS]; norm_num
  lam_pos := hl0
  lam_lt := hl1
  a_lt := by rw [ha1, ha2]; linarith
  h_mono := by rw [hh]; exact fun a b hab => by simp only; linarith [Real.exp_lt_exp.2 hab]
  h_conv := by rw [hh]; exact strictConvexOn_exp.add_const κ
  h_cont := by rw [hh]; fun_prop

/-- **Exercise 13.D.2(b)** (MWG, p. 476), an existence instance (`u = log`). With `q_S = 2/3`,
`q_R = 1/2`, `(a₁, a₂) = (10, 2) + κ` and `λ ≤ 9/19`, both firms offering
`{(log 6, log 6), (log 9, log 4)}` (wealth `(6, 6) + κ` and `(9, 4) + κ`) is an SPNE, provided
the outside options are not better than the equilibrium contracts. -/
theorem log_isEq (M : RSModel) {κ : ℝ} (hqS : M.qS = 2 / 3) (hqR : M.qR = 1 / 2)
    (ha1 : M.a₁ = 10 + κ) (ha2 : M.a₂ = 2 + κ) (hh : M.h = fun v => Real.exp v + κ)
    (hl0 : 0 < M.lam) (hl : M.lam ≤ 9 / 19) (hρR : M.ρR ≤ Real.log 6)
    (hρS : M.ρS ≤ M.V true (Real.log 9, Real.log 4)) :
    M.game.IsEq {(Real.log 6, Real.log 6), (Real.log 9, Real.log 4)}
      {(Real.log 6, Real.log 6), (Real.log 9, Real.log 4)} := by
  have hM := log_valid M hqS hqR ha1 ha2 hh hl0 (by linarith)
  have h94 := log9_add_log4
  have e9 : Real.exp (Real.log 9) = 9 := Real.exp_log (by norm_num)
  have e4 : Real.exp (Real.log 4) = 4 := Real.exp_log (by norm_num)
  have e6 : Real.exp (Real.log 6) = 6 := Real.exp_log (by norm_num)
  refine rs_isEq hM (vs := Real.log 6) ?_ ?_ ?_ log4_lt_log9 hρR hρS fun k hk => ⟨?_, ?_⟩
  · rw [hh]; simp only [abar, q_false, hqR, ha1, ha2, e6]; ring
  · simp only [Pr, hh, q_true, hqS, ha1, ha2, e9, e4]; ring
  · simp only [V, q_false, hqR]; linarith
  · intro hR
    simp only [V, q_true, q_false, hqS, hqR] at hk hR
    have t1 := exp_ge_tangent (x0 := 9) (by norm_num) k.1
    have t2 := exp_ge_tangent (x0 := 4) (by norm_num) k.2
    simp only [Pr, hh, q_true, hqS, ha1, ha2]
    nlinarith
  · intro hR
    simp only [V, q_true, q_false, hqS, hqR] at hk hR
    have t1 := exp_ge_tangent (x0 := 9) (by norm_num) k.1
    have t2 := exp_ge_tangent (x0 := 4) (by norm_num) k.2
    have t3 := exp_ge_tangent (x0 := 6) (by norm_num) (1 / 2 * k.1 + (1 - 1 / 2) * k.2)
    simp only [Pr, abar, V, hh, q_true, q_false, hqS, hqR, ha1, ha2]
    set d1 := k.1 - Real.log 9
    set d2 := k.2 - Real.log 4
    have hd : 0 ≤ 2 * d1 + d2 := by simp only [d1, d2]; linarith
    have hd' : 0 < d1 + d2 := by simp only [d1, d2]; linarith
    have hS : 2 / 3 * (10 + κ - (Real.exp k.1 + κ)) + (1 - 2 / 3) * (2 + κ - (Real.exp k.2 + κ))
        ≤ -6 * d1 - 4 / 3 * d2 := by simp only [d1, d2]; linarith
    have hRb : 1 / 2 * (10 + κ) + (1 - 1 / 2) * (2 + κ) -
        (Real.exp (1 / 2 * k.1 + (1 - 1 / 2) * k.2) + κ) ≤ -3 * (d1 + d2) := by
      simp only [d1, d2]; linarith
    have hl1 : 0 ≤ 1 - M.lam := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hS hl0.le, mul_le_mul_of_nonneg_left hRb hl1,
      mul_nonneg hl0.le hd, mul_nonneg (by linarith : (0 : ℝ) ≤ 9 / 19 - M.lam) hd'.le]

/-- **Exercise 13.D.2(b)** (MWG, p. 476), a nonexistence instance (`u = log`). With the data of
`log_isEq` and `λ = 9/10`, the pooling contract `(log 7, log 7)` (wealth `7 + κ` in both states)
attracts both types at a profit: no SPNE exists. -/
theorem log_no_eq (M : RSModel) {κ : ℝ} (hqS : M.qS = 2 / 3) (hqR : M.qR = 1 / 2)
    (ha1 : M.a₁ = 10 + κ) (ha2 : M.a₂ = 2 + κ) (hh : M.h = fun v => Real.exp v + κ)
    (hl : M.lam = 9 / 10) (hR : M.ρR < Real.log 6)
    (hS : ∃ e : ℝ × ℝ, M.V true e = M.ρS ∧ 0 ≤ M.Pr true e ∧ M.V false e < Real.log 6) :
    ¬ ∃ A₁ A₂, M.game.IsEq A₁ A₂ := by
  have hM := log_valid M hqS hqR ha1 ha2 hh (by rw [hl]; norm_num) (by rw [hl]; norm_num)
  have h94 := log9_add_log4
  have e9 : Real.exp (Real.log 9) = 9 := Real.exp_log (by norm_num)
  have e4 : Real.exp (Real.log 4) = 4 := Real.exp_log (by norm_num)
  have e6 : Real.exp (Real.log 6) = 6 := Real.exp_log (by norm_num)
  have e7 : Real.exp (Real.log 7) = 7 := Real.exp_log (by norm_num)
  have h76 : Real.log 6 < Real.log 7 := Real.log_lt_log (by norm_num) (by norm_num)
  have h7 : 2 * Real.log 9 + Real.log 4 < 3 * Real.log 7 := by
    have a : 2 * Real.log 9 + Real.log 4 = Real.log (9 ^ 2 * 4) := by
      rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow]; norm_num
    have b : 3 * Real.log 7 = Real.log (7 ^ 3) := by rw [Real.log_pow]; norm_num
    rw [a, b]
    exact Real.log_lt_log (by norm_num) (by norm_num)
  refine rs_no_eq hM (vs := Real.log 6) ?_ hR hS (kS := (Real.log 9, Real.log 4)) ⟨?_, ?_,
    log4_lt_log9⟩ (k' := (Real.log 7, Real.log 7)) ?_ ?_ ?_
  · rw [hh]; simp only [abar, q_false, hqR, ha1, ha2, e6]; ring
  · simp only [Pr, hh, q_true, hqS, ha1, ha2, e9, e4]; ring
  · simp only [V, q_false, hqR]; linarith
  · simp only [V, q_true, hqS]; linarith
  · rw [V_diag]; exact h76
  · rw [Pr_diag, Pr_diag, hh, hl]
    simp only [abar, q_true, q_false, hqS, hqR, ha1, ha2, e7]
    linarith

/-- **Exercise 13.D.2(a)** (MWG, p. 476). A policy `(M, R)` (premium `M`, payment `R` in case of
loss) corresponds to the wealth levels `(W - M, W - L - M + R)` in the states "no loss" and
"loss". -/
def policyWealth (W L : ℝ) : ℝ × ℝ ≃ ℝ × ℝ where
  toFun p := (W - p.1, W - L - p.1 + p.2)
  invFun x := (W - x.1, x.2 - x.1 + L)
  left_inv p := by ext <;> simp only <;> ring
  right_inv x := by ext <;> simp only <;> ring

/-- **Exercise 13.D.2(a)** (MWG, p. 476). Policies and wealth levels correspond bijectively, and
the insured's expected utility and the insurer's expected profit `M - pR` are functions of the
wealth levels `x = (x₁, x₂)`: `(1 - p) u(x₁) + p u(x₂)` and `(1 - p)(W - x₁) + p(W - L - x₂)`. -/
theorem exercise_13_D_2a (W L p : ℝ) (u : ℝ → ℝ) (pol : ℝ × ℝ) :
    Function.Bijective (policyWealth W L) ∧
      (1 - p) * u (W - pol.1) + p * u (W - L - pol.1 + pol.2) =
        (1 - p) * u (policyWealth W L pol).1 + p * u (policyWealth W L pol).2 ∧
      pol.1 - p * pol.2 =
        (1 - p) * (W - (policyWealth W L pol).1) + p * (W - L - (policyWealth W L pol).2) := by
  refine ⟨(policyWealth W L).bijective, rfl, ?_⟩
  simp only [policyWealth, Equiv.coe_fn_mk]; ring

/-- **Exercise 13.D.2(a)** (MWG, p. 476), with `u = log`: positive wealth levels and utility
levels correspond bijectively (`h = exp` is the inverse of `u`). -/
theorem exercise_13_D_2a_log (x v : ℝ × ℝ) (hx1 : 0 < x.1) (hx2 : 0 < x.2) :
    (Real.exp (Real.log x.1), Real.exp (Real.log x.2)) = x ∧
      (Real.log (Real.exp v.1), Real.log (Real.exp v.2)) = v := by
  rw [Real.exp_log hx1, Real.exp_log hx2, Real.log_exp, Real.log_exp]
  exact ⟨rfl, rfl⟩

/-- **Exercise 13.D.2(b)** (MWG, p. 476). The insurance model: wealth `W`, loss `L`, loss
probabilities `p_L` (low risk, the safe type `true`) and `p_H` (high risk), `λ` the probability
of low risk, `h = u⁻¹`; `(e₁, e₂)` are the utility levels of the endowment (no insurance). -/
def insModel (W L pL pH lam : ℝ) (h : ℝ → ℝ) (e₁ e₂ : ℝ) : RSModel where
  qS := 1 - pL
  qR := 1 - pH
  a₁ := W
  a₂ := W - L
  h := h
  ρS := (1 - pL) * e₁ + pL * e₂
  ρR := (1 - pH) * e₁ + pH * e₂
  lam := lam

/-- In the insurance model the outside options satisfy the hypotheses of
`rs_characterization` (Jensen's inequality). -/
theorem ins_participation {W L pL pH lam : ℝ} {h : ℝ → ℝ} {e₁ e₂ vs : ℝ}
    (hM : (insModel W L pL pH lam h e₁ e₂).Valid) (he₁ : h e₁ = W) (he₂ : h e₂ = W - L)
    (hv : h vs = (insModel W L pL pH lam h e₁ e₂).abar false) :
    (insModel W L pL pH lam h e₁ e₂).ρR < vs ∧
      ∃ e : ℝ × ℝ, (insModel W L pL pH lam h e₁ e₂).V true e =
        (insModel W L pL pH lam h e₁ e₂).ρS ∧ 0 ≤ (insModel W L pL pH lam h e₁ e₂).Pr true e ∧
        (insModel W L pL pH lam h e₁ e₂).V false e < vs := by
  set N := insModel W L pL pH lam h e₁ e₂
  have hL : W - L < W := hM.a_lt
  have hne : e₁ ≠ e₂ := by
    intro he
    have : h e₁ = h e₂ := by rw [he]
    linarith
  have hPe : ∀ b, N.Pr b (e₁, e₂) = 0 := fun b => by
    simp only [N, Pr, insModel, he₁, he₂]; ring
  have hj := Pr_lt hM false (k := (e₁, e₂)) hne
  rw [hPe, ← hv] at hj
  have hv'' : N.h vs = N.abar false := hv
  have hlt : N.V false (e₁, e₂) < vs := hM.h_mono.lt_iff_lt.1 (by linarith)
  have hρR : N.ρR = N.V false (e₁, e₂) := by simp only [N, V, q_false, insModel]; ring
  refine ⟨hρR ▸ hlt, (e₁, e₂), ?_, (hPe true).ge, hlt⟩
  simp only [N, V, q_true, insModel]; ring

/-- **Exercise 13.D.2(b)** (MWG, p. 476). In every SPNE of the insurance game the high-risk type
buys full insurance at her fair premium (wealth `h v* = W - p_H L` in both states; the policy
`(p_H L, L)`), the low-risk type buys a policy that is fair for her, gives her strictly less
wealth in the loss state (partial insurance), and leaves the high-risk type indifferent
(`(1 - p_H) v₁ + p_H v₂ = v*`); both firms earn zero. -/
theorem exercise_13_D_2b {W L pL pH lam : ℝ} {h : ℝ → ℝ} {e₁ e₂ vs : ℝ}
    (hM : (insModel W L pL pH lam h e₁ e₂).Valid) (he₁ : h e₁ = W) (he₂ : h e₂ = W - L)
    (hv : h vs = W - pH * L) {A₁ A₂ : Finset (ℝ × ℝ)}
    (heq : (insModel W L pL pH lam h e₁ e₂).game.IsEq A₁ A₂) :
    ∃ kS, (insModel W L pL pH lam h e₁ e₂).game.Chooses false (A₁ ∪ A₂) (vs, vs) ∧
      (insModel W L pL pH lam h e₁ e₂).game.Chooses true (A₁ ∪ A₂) kS ∧
      (policyWealth W L).symm (h vs, h vs) = (pH * L, L) ∧
      (1 - pL) * (W - h kS.1) + pL * (W - L - h kS.2) = 0 ∧
      (1 - pH) * kS.1 + pH * kS.2 = vs ∧ h kS.2 < h kS.1 ∧
      (insModel W L pL pH lam h e₁ e₂).game.profit A₁ A₂ = 0 ∧
      (insModel W L pL pH lam h e₁ e₂).game.profit A₂ A₁ = 0 := by
  have hv' : h vs = (insModel W L pL pH lam h e₁ e₂).abar false := by
    rw [hv]; simp only [abar, q_false, insModel]; ring
  obtain ⟨hR, hS⟩ := ins_participation hM he₁ he₂ hv'
  obtain ⟨kS, hkR, hkS, hP, hV, hlt, hz1, hz2⟩ := rs_characterization hM hv' hR hS heq
  refine ⟨kS, hkR, hkS, ?_, ?_, ?_, hM.h_mono hlt, hz1, hz2⟩
  · simp only [policyWealth, Equiv.coe_fn_symm_mk, hv]; ext <;> simp only <;> ring
  · simp only [Pr, q_true, insModel] at hP; linarith
  · simp only [V, q_false, insModel] at hV; linarith

/-- **Exercise 13.D.2(b)** (MWG, p. 476), existence: `W = 10`, `L = 8`, `p_L = 1/3`,
`p_H = 1/2`, `u = log`, `λ = 1/10`. Both firms offering the policies with wealth levels
`(6, 6)` (full insurance at premium `4`) and `(9, 4)` (premium `1`, coverage `3`) is an SPNE. -/
theorem exercise_13_D_2b_exists :
    (insModel 10 8 (1 / 3) (1 / 2) (1 / 10) Real.exp (Real.log 10) (Real.log 2)).game.IsEq
      {(Real.log 6, Real.log 6), (Real.log 9, Real.log 4)}
      {(Real.log 6, Real.log 6), (Real.log 9, Real.log 4)} := by
  have h1 : Real.log 10 + Real.log 2 ≤ 2 * Real.log 6 := by
    rw [← Real.log_mul (by norm_num) (by norm_num), two_mul,
      ← Real.log_mul (by norm_num) (by norm_num)]
    exact Real.log_le_log (by norm_num) (by norm_num)
  have h2 : 2 * Real.log 10 + Real.log 2 ≤ 2 * Real.log 9 + Real.log 4 := by
    have a : 2 * Real.log 10 + Real.log 2 = Real.log (10 ^ 2 * 2) := by
      rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow]; norm_num
    have b : 2 * Real.log 9 + Real.log 4 = Real.log (9 ^ 2 * 4) := by
      rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow]; norm_num
    rw [a, b]
    exact Real.log_le_log (by norm_num) (by norm_num)
  refine log_isEq _ (κ := 0) (by norm_num [insModel]) (by norm_num [insModel])
    (by norm_num [insModel]) (by norm_num [insModel]) (by funext v; simp [insModel])
    (by norm_num [insModel]) (by norm_num [insModel]) ?_ ?_
  · simp only [insModel]; linarith
  · simp only [insModel, V, q_true]; linarith

/-- **Exercise 13.D.2(b)** (MWG, p. 476): an equilibrium need not exist. With the data of
`exercise_13_D_2b_exists` but `λ = 9/10` (mostly low risks), the pooling policy with wealth `7`
in both states attracts everybody at a profit, and no SPNE exists. -/
theorem exercise_13_D_2b_nonexistence :
    ¬ ∃ A₁ A₂, (insModel 10 8 (1 / 3) (1 / 2) (9 / 10) Real.exp (Real.log 10)
      (Real.log 2)).game.IsEq A₁ A₂ := by
  set N := insModel 10 8 (1 / 3) (1 / 2) (9 / 10) Real.exp (Real.log 10) (Real.log 2)
  have hN : N.Valid := log_valid N (κ := 0) (by norm_num [N, insModel]) (by norm_num [N, insModel])
    (by norm_num [N, insModel]) (by norm_num [N, insModel]) (by funext v; simp [N, insModel])
    (by norm_num [N, insModel]) (by norm_num [N, insModel])
  have hv : Real.exp (Real.log 6) = N.abar false := by
    rw [Real.exp_log (by norm_num)]; simp only [N, abar, q_false, insModel]; norm_num
  obtain ⟨hR, hS⟩ := ins_participation (vs := Real.log 6) hN (Real.exp_log (by norm_num))
    (by rw [Real.exp_log (by norm_num)]; norm_num) hv
  exact log_no_eq N (κ := 0) (by norm_num [N, insModel]) (by norm_num [N, insModel])
    (by norm_num [N, insModel]) (by norm_num [N, insModel]) (by funext v; simp [N, insModel])
    (by norm_num [N, insModel]) hR hS

/-- **Exercise 13.D.2(b)** (MWG, p. 476), the instance of `exercise_13_D_2b_exists`: in every
SPNE the high-risk type gets wealth `(6, 6)` and the low-risk type `(9, 4)`. -/
theorem exercise_13_D_2b_outcome {A₁ A₂ : Finset (ℝ × ℝ)}
    (h : (insModel 10 8 (1 / 3) (1 / 2) (1 / 10) Real.exp (Real.log 10)
      (Real.log 2)).game.IsEq A₁ A₂) :
    (insModel 10 8 (1 / 3) (1 / 2) (1 / 10) Real.exp (Real.log 10) (Real.log 2)).game.Chooses
        false (A₁ ∪ A₂) (Real.log 6, Real.log 6) ∧
      (insModel 10 8 (1 / 3) (1 / 2) (1 / 10) Real.exp (Real.log 10) (Real.log 2)).game.Chooses
        true (A₁ ∪ A₂) (Real.log 9, Real.log 4) := by
  set N := insModel 10 8 (1 / 3) (1 / 2) (1 / 10) Real.exp (Real.log 10) (Real.log 2)
  have hN : N.Valid := log_valid N (κ := 0) (by norm_num [N, insModel]) (by norm_num [N, insModel])
    (by norm_num [N, insModel]) (by norm_num [N, insModel]) (by funext v; simp [N, insModel])
    (by norm_num [N, insModel]) (by norm_num [N, insModel])
  have hv : N.h (Real.log 6) = N.abar false := by
    simp only [N, insModel, abar, q_false]; rw [Real.exp_log (by norm_num)]; norm_num
  obtain ⟨hR, hS⟩ := ins_participation (vs := Real.log 6) hN (Real.exp_log (by norm_num))
    (by rw [Real.exp_log (by norm_num)]; norm_num) hv
  obtain ⟨kS, hkR, hkS, hP, hV, hlt, -⟩ := rs_characterization hN hv hR hS h
  have h94 := log9_add_log4
  have e9 : Real.exp (Real.log 9) = 9 := Real.exp_log (by norm_num)
  have e4 : Real.exp (Real.log 4) = 4 := Real.exp_log (by norm_num)
  have he := rs_point_unique hN hv ⟨hP, hV, hlt⟩ (k' := (Real.log 9, Real.log 4))
    ⟨by simp only [N, insModel, Pr, q_true, e9, e4]; norm_num,
      by simp only [N, insModel, V, q_false]; linarith, log4_lt_log9⟩
  exact ⟨hkR, he ▸ hkS⟩

end RSModel

end MWG.AdverseSelection
