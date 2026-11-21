/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGCompetitiveMarkets.ExercisesE
import MWGCompetitiveMarkets.TaxIncidence
import Mathlib.Analysis.Calculus.LagrangeMultipliers

/-!
# Derived equilibrium paths and Lagrange multipliers (Exercises 10.C.5, 10.E.1, 10.E.3)

This module removes the assumed ingredients of three exercises.

* `implicit_1d`: a one-variable implicit function theorem. If `A(s(τ) + τ) = B(s(τ))` near `τ₀`,
  `s` is continuous at `τ₀`, `A' = a`, `B' = b` and `b ≠ a`, then `s'(τ₀) = a/(b - a)`.
* `implicit_path`: with `N` continuous and nonincreasing and `S` continuous and strictly
  increasing, the equation `N(s + τ) = S(s)` has, for `τ` near `0`, a unique solution `s(τ)`,
  continuous at `0`.
* **Exercise 10.C.5**: in the model of Section 10.C, the equilibrium paths `xᵢ(t)`, `qⱼ(t)`,
  `p*(t)` are derived to be differentiable and to satisfy (10.C.4)-(10.C.6) near `t = 0`
  (`exercise_10_C_5_derived`).
* **Exercise 10.E.1(a)**: the foreign price path under a tariff is derived (`implicit_path`,
  `implicit_1d`) and a small tariff raises domestic welfare (`exercise_10_E_1a_derived`).
* **Exercise 10.E.3(b)**: the Lagrange multiplier exists at a constrained optimum (Mathlib's
  `IsLocalExtrOn.exists_multipliers_of_hasStrictFDerivAt_1d`), so the Ramsey rule holds
  unconditionally (`exercise_10_E_3b_lagrange`).
-/

namespace MWG.CompetitiveMarkets

open Filter Topology MeasureTheory

/-! ## A one-variable implicit function theorem -/

/-- **Implicit differentiation in one variable.** If `A(s(τ) + τ) = B(s(τ))` for `τ` near `τ₀`,
`s` is continuous at `τ₀`, `A` has derivative `a` at `s(τ₀) + τ₀`, `B` has derivative `b` at
`s(τ₀)` and `b ≠ a`, then `s` is differentiable at `τ₀` with `s'(τ₀) = a/(b - a)`. -/
theorem implicit_1d {A B s : ℝ → ℝ} {τ₀ a b : ℝ} (hs : ContinuousAt s τ₀)
    (hA : HasDerivAt A a (s τ₀ + τ₀)) (hB : HasDerivAt B b (s τ₀)) (hab : b - a ≠ 0)
    (heq : ∀ᶠ τ in 𝓝 τ₀, A (s τ + τ) = B (s τ)) : HasDerivAt s (a / (b - a)) τ₀ := by
  set y₀ := s τ₀ + τ₀
  have hg : Tendsto (fun τ => s τ + τ) (𝓝 τ₀) (𝓝 y₀) := hs.add continuousAt_id
  have rA := (remainder_isLittleO hA).comp_tendsto hg
  have rB := (remainder_isLittleO hB).comp_tendsto hs
  simp only [Function.comp_def] at rA rB
  -- notation: `u = s τ - s τ₀`, `v = τ - τ₀`
  have hk : 0 < |b - a| := abs_pos.2 hab
  set ε := |b - a| / 4 with hε
  have hε0 : 0 < ε := by positivity
  have hAb := rA.bound hε0
  have hBb := rB.bound hε0
  have heq0 : A y₀ = B (s τ₀) := heq.self_of_nhds
  -- `u = O(v)`
  have hO : (fun τ => s τ - s τ₀) =O[𝓝 τ₀] fun τ => τ - τ₀ := by
    refine Asymptotics.IsBigO.of_bound ((|a| + ε) / (|b - a| / 2)) ?_
    filter_upwards [hAb, hBb, heq] with τ h1 h2 h3
    simp only [Real.norm_eq_abs] at h1 h2 ⊢
    set u := s τ - s τ₀
    set v := τ - τ₀
    have key : (b - a) * u - a * v = (A (s τ + τ) - A y₀ - (s τ + τ - y₀) * a) -
        (B (s τ) - B (s τ₀) - (s τ - s τ₀) * b) := by
      simp only [u, v, y₀]; rw [h3, heq0]; ring
    have huv : |s τ + τ - y₀| ≤ |u| + |v| := by
      have : s τ + τ - y₀ = u + v := by simp only [u, v, y₀]; ring
      rw [this]; exact abs_add_le u v
    have h4 : |b - a| * |u| ≤ |a| * |v| + ε * (|u| + |v|) + ε * |u| := by
      have e1 : |(b - a) * u| ≤ |a * v| + |A (s τ + τ) - A y₀ - (s τ + τ - y₀) * a| +
          |B (s τ) - B (s τ₀) - (s τ - s τ₀) * b| := by
        have : (b - a) * u = a * v + ((A (s τ + τ) - A y₀ - (s τ + τ - y₀) * a) -
            (B (s τ) - B (s τ₀) - (s τ - s τ₀) * b)) := by linarith
        rw [this, abs_le]
        set Y := A (s τ + τ) - A y₀ - (s τ + τ - y₀) * a
        set Z := B (s τ) - B (s τ₀) - (s τ - s τ₀) * b
        have := le_abs_self (a * v); have := neg_abs_le (a * v)
        have := le_abs_self Y; have := neg_abs_le Y
        have := le_abs_self Z; have := neg_abs_le Z
        constructor <;> linarith
      rw [abs_mul, abs_mul] at e1
      nlinarith [h1, h2, huv, hε0.le]
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith [abs_nonneg u, abs_nonneg v]
  have huv : (fun τ => s τ + τ - y₀) =O[𝓝 τ₀] fun τ => τ - τ₀ := by
    have : (fun τ => s τ + τ - y₀) = fun τ => (s τ - s τ₀) + (τ - τ₀) := by
      funext τ; simp only [y₀]; ring
    rw [this]
    exact hO.add (Asymptotics.isBigO_refl _ _)
  have rA' := rA.trans_isBigO huv
  have rB' := rB.trans_isBigO hO
  rw [hasDerivAt_iff_isLittleO]
  have hdiff := (rA'.sub rB').const_mul_left (1 / (b - a))
  refine hdiff.congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [heq] with τ h3
  simp only [smul_eq_mul]
  rw [h3, heq0]
  field_simp
  ring

/-! ## Existence and continuity of an equilibrium path -/

/-- **An equilibrium path.** Let `N` be continuous and nonincreasing and `S` continuous and
strictly increasing with `N(s₀) = S(s₀)`. Then for `τ` near `0` the equation `N(s + τ) = S(s)` has
a solution `s(τ)` (unique for every `τ`), with `s(0) = s₀` and `s` continuous at `0`. -/
theorem implicit_path {N S : ℝ → ℝ} (hN : Continuous N) (hNa : Antitone N) (hS : Continuous S)
    (hSm : StrictMono S) {s₀ : ℝ} (h0 : N s₀ = S s₀) :
    ∃ s : ℝ → ℝ, s 0 = s₀ ∧ (∀ᶠ τ in 𝓝 (0 : ℝ), N (s τ + τ) = S (s τ)) ∧ ContinuousAt s 0 ∧
      ∀ τ y, N (y + τ) = S y → s τ = y := by
  classical
  -- uniqueness of solutions
  have huniq : ∀ τ y₁ y₂, N (y₁ + τ) = S y₁ → N (y₂ + τ) = S y₂ → y₁ = y₂ := by
    intro τ y₁ y₂ h₁ h₂
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := hNa (by linarith : y₁ + τ ≤ y₂ + τ); have := hSm hlt; linarith
    · have := hNa (by linarith : y₂ + τ ≤ y₁ + τ); have := hSm hlt; linarith
  set s : ℝ → ℝ := fun τ => if h : ∃ y, N (y + τ) = S y then h.choose else s₀ with hsdef
  have hspec : ∀ τ, (∃ y, N (y + τ) = S y) → N (s τ + τ) = S (s τ) := by
    intro τ h
    simp only [hsdef, dite_eq_left_of_eq_true (eq_true h)]
    exact h.choose_spec
  have hsol : ∀ τ y, N (y + τ) = S y → s τ = y := fun τ y hy =>
    huniq τ _ _ (hspec τ ⟨y, hy⟩) hy
  -- brackets
  have hbr : ∀ ε, 0 < ε → ∀ᶠ τ in 𝓝 (0 : ℝ),
      S (s₀ - ε) < N (s₀ - ε + τ) ∧ N (s₀ + ε + τ) < S (s₀ + ε) := by
    intro ε hε
    have hl : S (s₀ - ε) < N (s₀ - ε + 0) := by
      rw [add_zero]
      have := hNa (by linarith : s₀ - ε ≤ s₀); have := hSm (by linarith : s₀ - ε < s₀)
      linarith
    have hr : N (s₀ + ε + 0) < S (s₀ + ε) := by
      rw [add_zero]
      have := hNa (by linarith : s₀ ≤ s₀ + ε); have := hSm (by linarith : s₀ < s₀ + ε)
      linarith
    have c1 : ContinuousAt (fun τ => N (s₀ - ε + τ)) 0 :=
      (hN.comp (continuous_const.add continuous_id)).continuousAt
    have c2 : ContinuousAt (fun τ => N (s₀ + ε + τ)) 0 :=
      (hN.comp (continuous_const.add continuous_id)).continuousAt
    exact (c1.eventually (lt_mem_nhds hl)).and (c2.eventually (gt_mem_nhds hr))
  -- inside a bracket the solution exists and lies in it
  have hin : ∀ ε, 0 < ε → ∀ τ, S (s₀ - ε) < N (s₀ - ε + τ) → N (s₀ + ε + τ) < S (s₀ + ε) →
      N (s τ + τ) = S (s τ) ∧ s₀ - ε < s τ ∧ s τ < s₀ + ε := by
    intro ε hε τ h1 h2
    have hc : ContinuousOn (fun y => N (y + τ) - S y) (Set.Icc (s₀ - ε) (s₀ + ε)) :=
      ((hN.comp (continuous_id.add continuous_const)).sub hS).continuousOn
    obtain ⟨y, hy, hyz⟩ := intermediate_value_Icc' (by linarith : s₀ - ε ≤ s₀ + ε) hc
      ⟨by change N (s₀ + ε + τ) - S (s₀ + ε) ≤ 0; linarith,
        by change 0 ≤ N (s₀ - ε + τ) - S (s₀ - ε); linarith⟩
    have hy' : N (y + τ) = S y := by simp only at hyz; linarith
    have e := hsol τ y hy'
    rw [e]
    refine ⟨hy', lt_of_le_of_ne hy.1 fun h => ?_, lt_of_le_of_ne hy.2 fun h => ?_⟩
    · rw [← h] at hy'; linarith
    · rw [h] at hy'; linarith
  have hs0 : s 0 = s₀ := hsol 0 s₀ (by rw [add_zero, h0])
  refine ⟨s, hs0, ?_, ?_, hsol⟩
  · filter_upwards [hbr 1 one_pos] with τ hτ
    exact (hin 1 one_pos τ hτ.1 hτ.2).1
  · rw [ContinuousAt, hs0, Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [hbr ε hε] with τ hτ
    obtain ⟨-, h1, h2⟩ := hin ε hε τ hτ.1 hτ.2
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith

/-! ## Exercise 10.E.1(a), derived -/

/-- **Exercise 10.E.1(a)** (MWG, p. 346), with the equilibrium path derived. Let domestic demand
`D` and domestic supply `S_d` give a continuous nonincreasing net demand `D - S_d`, and let
foreign supply `S_f` be continuous and strictly increasing (strictly convex foreign costs), with
free-trade equilibrium price `s₀` (`D(s₀) - S_d(s₀) = S_f(s₀)`, imports `S_f(s₀) > 0`). Then the
foreign price `s(τ)` under a tariff `τ` (consumer and domestic-firm price `s(τ) + τ`) is
well defined near `τ = 0` and differentiable at `0` with `s'(0) = (d - s_d)/(s_f - d + s_d) < 0`,
and with price-taking consumers and domestic firms (`B' = C_d' = p`) a small tariff raises
domestic welfare `W(τ) = B(Q_d + Q_f) - C_d(Q_d) - s Q_f`. -/
theorem exercise_10_E_1a_derived {D Sd Sf B Cd : ℝ → ℝ} {s₀ d sd sf : ℝ}
    (hN : Continuous fun p => D p - Sd p) (hNa : Antitone fun p => D p - Sd p)
    (hSf : Continuous Sf) (hSfm : StrictMono Sf) (h0 : D s₀ - Sd s₀ = Sf s₀)
    (hD : HasDerivAt D d s₀) (hSd : HasDerivAt Sd sd s₀) (hSf' : HasDerivAt Sf sf s₀)
    (hsf : 0 < sf) (hdsd : d - sd < 0) (hQf : 0 < Sf s₀)
    (hB : HasDerivAt B s₀ (Sd s₀ + Sf s₀)) (hC : HasDerivAt Cd s₀ (Sd s₀)) :
    ∃ s : ℝ → ℝ, s 0 = s₀ ∧
      (∀ᶠ τ in 𝓝 (0 : ℝ), D (s τ + τ) - Sd (s τ + τ) = Sf (s τ)) ∧
      HasDerivAt s ((d - sd) / (sf - (d - sd))) 0 ∧ (d - sd) / (sf - (d - sd)) < 0 ∧
      ∃ δ > 0, ∀ τ, 0 < τ → τ < δ →
        B (Sd (s 0 + 0) + Sf (s 0)) - Cd (Sd (s 0 + 0)) - s 0 * Sf (s 0) <
          B (Sd (s τ + τ) + Sf (s τ)) - Cd (Sd (s τ + τ)) - s τ * Sf (s τ) := by
  obtain ⟨s, hs0, heq, hcont, -⟩ := implicit_path hN hNa hSf hSfm h0
  have hab : sf - (d - sd) ≠ 0 := by linarith
  have hA : HasDerivAt (fun p => D p - Sd p) (d - sd) (s 0 + 0) := by
    rw [hs0, add_zero]; exact hD.sub hSd
  have hBd : HasDerivAt Sf sf (s 0) := by rw [hs0]; exact hSf'
  have hsd := implicit_1d hcont hA hBd hab heq
  have hneg : (d - sd) / (sf - (d - sd)) < 0 := div_neg_of_neg_of_pos hdsd (by linarith)
  refine ⟨s, hs0, heq, hsd, hneg, ?_⟩
  set s' := (d - sd) / (sf - (d - sd))
  have hpath : HasDerivAt (fun τ => s τ + τ) (s' + 1) 0 := hsd.add (hasDerivAt_id 0)
  have hQd : HasDerivAt (fun τ => Sd (s τ + τ)) (sd * (s' + 1)) 0 := by
    have h1 : HasDerivAt Sd sd (s 0 + 0) := by rw [hs0, add_zero]; exact hSd
    exact HasDerivAt.comp (h := fun τ => s τ + τ) (0 : ℝ) h1 hpath
  have hQf' : HasDerivAt (fun τ => Sf (s τ)) (sf * s') 0 := by
    have h1 : HasDerivAt Sf sf (s 0) := by rw [hs0]; exact hSf'
    exact HasDerivAt.comp (h := s) (0 : ℝ) h1 hsd
  have hW := exercise_10_E_1_deriv (B := B) (Cd := Cd) (Qd := fun τ => Sd (s τ + τ))
    (Qf := fun τ => Sf (s τ)) (s := s) (τ₀ := 0) (p := s₀)
    (by simpa [hs0] using hB) (by simpa [hs0] using hC) hQd hQf' hsd (by rw [hs0]; ring)
  exact exercise_10_E_1a hW hneg (by simpa [hs0] using hQf)

/-- **Instance of Exercise 10.E.1(a), derived**: demand `3 - p`, domestic supply `p`, foreign
supply `s`, gross benefit `3X - X²/2` and domestic cost `Q²/2`; free-trade price `1`. -/
theorem inst_exercise_10_E_1a :
    ∃ s : ℝ → ℝ, s 0 = 1 ∧ ∃ δ > 0, ∀ τ, 0 < τ → τ < δ →
      (3 * (s 0 + 0 + s 0) - (s 0 + 0 + s 0) ^ 2 / 2) - (s 0 + 0) ^ 2 / 2 - s 0 * s 0 <
        (3 * (s τ + τ + s τ) - (s τ + τ + s τ) ^ 2 / 2) - (s τ + τ) ^ 2 / 2 - s τ * s τ := by
  obtain ⟨s, hs0, -, -, -, δ, hδ, h⟩ := exercise_10_E_1a_derived (D := fun p => 3 - p)
    (Sd := fun p => p) (Sf := fun s => s) (B := fun X => 3 * X - X ^ 2 / 2)
    (Cd := fun Q => Q ^ 2 / 2) (s₀ := 1) (d := -1) (sd := 1) (sf := 1)
    (by fun_prop) (fun a b hab => by simp only; linarith) continuous_id strictMono_id
    (by norm_num) (by simpa using (hasDerivAt_id (1 : ℝ)).const_sub 3) (hasDerivAt_id 1)
    (hasDerivAt_id 1) one_pos (by norm_num) one_pos
    (by
      have := ((hasDerivAt_id (2 : ℝ)).const_mul 3).sub ((hasDerivAt_pow 2 (2 : ℝ)).div_const 2)
      norm_num at this ⊢; convert this using 1)
    (by
      have := (hasDerivAt_pow 2 (1 : ℝ)).div_const 2
      norm_num at this ⊢; exact this)
  exact ⟨s, hs0, δ, hδ, h⟩

/-! ## Exercise 10.E.3(b): existence of the Lagrange multiplier -/

/-- With a continuously differentiable demand, the deadweight loss and the revenue of a tax on one
good are strictly differentiable. -/
theorem ramsey_strict {x x' : ℝ → ℝ} (c : ℝ) (hx : ∀ s, HasDerivAt x (x' s) s)
    (hx'c : Continuous x') (t : ℝ) :
    HasStrictDerivAt (fun t => (∫ s in c..c + t, x s) - t * x (c + t)) (-t * x' (c + t)) t ∧
      HasStrictDerivAt (fun t => t * x (c + t)) (x (c + t) + t * x' (c + t)) t := by
  have hxc : Continuous x := continuous_iff_continuousAt.2 fun s => (hx s).continuousAt
  have hshift : Continuous fun t : ℝ => c + t := continuous_const.add continuous_id
  constructor
  · refine hasStrictDerivAt_of_hasDerivAt_of_continuousAt (f' := fun t => -t * x' (c + t))
      (Eventually.of_forall fun y => (exercise_10_E_3b_marginal hxc (hx (c + y))).1) ?_
    exact (continuous_neg.mul (hx'c.comp hshift)).continuousAt
  · refine hasStrictDerivAt_of_hasDerivAt_of_continuousAt
      (f' := fun t => x (c + t) + t * x' (c + t))
      (Eventually.of_forall fun y => (exercise_10_E_3b_marginal hxc (hx (c + y))).2) ?_
    exact ((hxc.comp hshift).add (continuous_id.mul (hx'c.comp hshift))).continuousAt

/-- **Exercise 10.E.3(b)** (MWG, p. 347), unconditionally. Let goods `ℓ` have continuously
differentiable demands `x_ℓ` with `x_ℓ > 0` and `x_ℓ' < 0` at the optimal consumer prices
`c_ℓ + t_ℓ > 0`, and let `t` minimize the total deadweight loss
`∑ (∫_{c_ℓ}^{c_ℓ+t_ℓ} x_ℓ - t_ℓ x_ℓ(c_ℓ + t_ℓ))` locally among tax vectors raising the same revenue
`∑ t_ℓ x_ℓ(c_ℓ + t_ℓ)`, with some marginal revenue nonzero. Then a Lagrange multiplier `λ ≠ -1`
exists (Lagrange's theorem) and every tax satisfies the Ramsey rule
`t_ℓ/p_ℓ = (λ/(1 + λ))(1/|ε_ℓ|)`. -/
theorem exercise_10_E_3b_lagrange {n : ℕ} (c : Fin n → ℝ) (x x' : Fin n → ℝ → ℝ)
    (hx : ∀ l s, HasDerivAt (x l) (x' l s) s) (hx'c : ∀ l, Continuous (x' l)) (t : Fin n → ℝ)
    (hmin : IsLocalMinOn
      (fun t : Fin n → ℝ => ∑ l, ((∫ s in c l..c l + t l, x l s) - t l * x l (c l + t l)))
      {t' | ∑ l, t' l * x l (c l + t' l) = ∑ l, t l * x l (c l + t l)} t)
    (hp : ∀ l, 0 < c l + t l) (hxp : ∀ l, 0 < x l (c l + t l)) (hneg : ∀ l, x' l (c l + t l) < 0)
    (hqual : ∃ l, x l (c l + t l) + t l * x' l (c l + t l) ≠ 0) :
    ∃ lam : ℝ, 1 + lam ≠ 0 ∧ ∀ l, t l / (c l + t l) =
      lam / (1 + lam) * (1 / |(c l + t l) * x' l (c l + t l) / x l (c l + t l)|) := by
  classical
  set D' : Fin n → ℝ := fun l => -t l * x' l (c l + t l)
  set R' : Fin n → ℝ := fun l => x l (c l + t l) + t l * x' l (c l + t l)
  have hD : HasStrictFDerivAt
      (fun t : Fin n → ℝ => ∑ l, ((∫ s in c l..c l + t l, x l s) - t l * x l (c l + t l)))
      (∑ l, D' l • ContinuousLinearMap.proj l) t :=
    HasStrictFDerivAt.fun_sum fun l _ =>
      HasStrictDerivAt.comp_hasStrictFDerivAt (f := fun t : Fin n → ℝ => t l) t
        (ramsey_strict (c l) (hx l) (hx'c l) (t l)).1 (hasStrictFDerivAt_apply (𝕜 := ℝ) l t)
  have hR : HasStrictFDerivAt (fun t : Fin n → ℝ => ∑ l, t l * x l (c l + t l))
      (∑ l, R' l • ContinuousLinearMap.proj l) t :=
    HasStrictFDerivAt.fun_sum fun l _ =>
      HasStrictDerivAt.comp_hasStrictFDerivAt (f := fun t : Fin n → ℝ => t l) t
        (ramsey_strict (c l) (hx l) (hx'c l) (t l)).2 (hasStrictFDerivAt_apply (𝕜 := ℝ) l t)
  obtain ⟨a, b, hab, hlin⟩ :=
    IsLocalExtrOn.exists_multipliers_of_hasStrictFDerivAt_1d (Or.inl hmin) hR hD
  have hcoord : ∀ l, a * R' l + b * D' l = 0 := by
    intro l
    have := congrArg (fun L => L (Pi.single l 1)) hlin
    simpa [Pi.single_apply] using this
  have hb : b ≠ 0 := by
    intro hb0
    obtain ⟨l, hl⟩ := hqual
    have ha : a ≠ 0 := fun ha0 => hab (by rw [ha0, hb0]; rfl)
    have := hcoord l
    rw [hb0, zero_mul, add_zero] at this
    exact hl ((mul_eq_zero.1 this).resolve_left ha)
  set lam := -a / b
  have hfoc : ∀ l, -t l * x' l (c l + t l) = lam * (x l (c l + t l) + t l * x' l (c l + t l)) := by
    intro l
    have := hcoord l
    simp only [lam, D', R'] at this ⊢
    field_simp
    linarith
  have hlam : 1 + lam ≠ 0 := by
    intro h
    obtain ⟨l, -⟩ := hqual
    have := hfoc l
    rw [show lam = -1 by linarith] at this
    have := hxp l
    linarith
  exact ⟨lam, hlam, fun l => exercise_10_E_3b (hp l) (hxp l) (hneg l) hlam (hfoc l)⟩

/-- **Instance of `exercise_10_E_3b_lagrange`**: one taxed good with unit cost `1/2`, demand
`2 - p` and the tax `1/4` (revenue `5/16`); locally it is the only tax raising that revenue. -/
theorem inst_exercise_10_E_3b :
    ∃ lam : ℝ, 1 + lam ≠ 0 ∧ ∀ l : Fin 1, (fun _ : Fin 1 => (1 / 4 : ℝ)) l /
      ((fun _ : Fin 1 => (1 / 2 : ℝ)) l + (fun _ : Fin 1 => (1 / 4 : ℝ)) l) =
      lam / (1 + lam) * (1 / |((fun _ : Fin 1 => (1 / 2 : ℝ)) l +
        (fun _ : Fin 1 => (1 / 4 : ℝ)) l) * (-1) /
        (2 - ((fun _ : Fin 1 => (1 / 2 : ℝ)) l + (fun _ : Fin 1 => (1 / 4 : ℝ)) l))|) := by
  refine exercise_10_E_3b_lagrange (fun _ => 1 / 2) (fun _ p => 2 - p) (fun _ _ => -1)
    (fun _ s => by simpa using (hasDerivAt_id s).const_sub 2) (fun _ => continuous_const)
    (fun _ => 1 / 4) ?_ (fun _ => by norm_num) (fun _ => by norm_num) (fun _ => by norm_num)
    ⟨0, by norm_num⟩
  rw [IsLocalMinOn, IsMinFilter, eventually_nhdsWithin_iff]
  filter_upwards [Metric.ball_mem_nhds (fun _ : Fin 1 => (1 / 4 : ℝ)) one_pos] with y hy hys
  have hy0 : |y 0 - 1 / 4| < 1 := by
    have := (dist_le_pi_dist y (fun _ => (1 / 4 : ℝ)) 0).trans_lt hy
    rwa [Real.dist_eq] at this
  simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton]
    at hys
  have hq : (y 0 - 1 / 4) * (y 0 - 5 / 4) = 0 := by nlinarith
  have h14 : y 0 = 1 / 4 := by
    rcases mul_eq_zero.1 hq with h | h
    · linarith
    · rw [abs_lt] at hy0; linarith
  have hyy : y = fun _ => 1 / 4 := by funext i; fin_cases i; exact h14
  rw [hyy]

/-! ## Exercise 10.C.5, derived -/

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **Exercise 10.C.5** (MWG, p. 345), with the equilibrium paths derived. In the model of
Section 10.C with a sales tax, if at `t = 0` every consumer and firm is active and every
`cⱼ'' > 0`, then the equilibrium paths `xᵢ(t) = xᵢ(p*(t) + t)`, `qⱼ(t) = qⱼ(p*(t))`, `p*(t)` are
differentiable at `0`, satisfy (10.C.4)-(10.C.6) near `0`, and the implicit-function computation
(`exercise_10_C_5`) gives
`p*'(0) = -∑[φᵢ'']⁻¹ / (∑[φᵢ'']⁻¹ - ∑[cⱼ'']⁻¹)`. -/
theorem exercise_10_C_5_derived [Nonempty ι] [Nonempty κ] (C : ι → QLConsumer)
    (F : κ → QLFirmStrict) (h0 : (0 : ℝ) ∈ taxRange C F)
    (hxa : ∀ i, taxPrice C F 0 < (C i).dφ 0) (hqa : ∀ j, (F j).dc 0 < taxPrice C F 0)
    (hc2 : ∀ j, 0 < (F j).d2c ((F j).supply (taxPrice C F 0))) :
    ∃ p' : ℝ, HasDerivAt (taxPrice C F) p' 0 ∧
      (∀ i, HasDerivAt (fun t => (C i).demand (taxPrice C F t + t))
        (((C i).d2φ ((C i).demand (taxPrice C F 0 + 0)))⁻¹ * (p' + 1)) 0) ∧
      (∀ j, HasDerivAt (fun t => (F j).supply (taxPrice C F t))
        (((F j).d2c ((F j).supply (taxPrice C F 0)))⁻¹ * p') 0) ∧
      (∀ᶠ t in 𝓝 (0 : ℝ), ∀ i,
        (C i).dφ ((C i).demand (taxPrice C F t + t)) = taxPrice C F t + t) ∧
      (∀ᶠ t in 𝓝 (0 : ℝ), ∀ j, (F j).dc ((F j).supply (taxPrice C F t)) = taxPrice C F t) ∧
      (∀ᶠ t in 𝓝 (0 : ℝ), ∑ i, (C i).demand (taxPrice C F t + t) =
        ∑ j, (F j).supply (taxPrice C F t)) ∧
      p' = -(∑ i, ((C i).d2φ ((C i).demand (taxPrice C F 0 + 0)))⁻¹) /
        (∑ i, ((C i).d2φ ((C i).demand (taxPrice C F 0 + 0)))⁻¹ -
          ∑ j, ((F j).d2c ((F j).supply (taxPrice C F 0)))⁻¹) := by
  set p₀ := taxPrice C F 0
  have hp0 : 0 < p₀ := (minMC_pos F).trans (taxPrice_spec C F h0).1
  obtain ⟨p', hp'⟩ : ∃ p', HasDerivAt (taxPrice C F) p' 0 :=
    ⟨_, example_10_C_1_formula C F h0 hxa hqa hc2⟩
  have hcont := taxPrice_continuousAt C F h0
  have hpath : HasDerivAt (fun t => taxPrice C F t + t) (p' + 1) 0 := hp'.add (hasDerivAt_id 0)
  have hx : ∀ i, HasDerivAt (fun t => (C i).demand (taxPrice C F t + t))
      (((C i).d2φ ((C i).demand (p₀ + 0)))⁻¹ * (p' + 1)) 0 := by
    intro i
    have h1 : HasDerivAt (C i).demand ((C i).d2φ ((C i).demand (p₀ + 0)))⁻¹ (p₀ + 0) := by
      rw [add_zero]; exact (C i).demand_hasDerivAt hp0 (hxa i)
    exact HasDerivAt.comp (h := fun t => taxPrice C F t + t) (0 : ℝ) h1 hpath
  have hq : ∀ j, HasDerivAt (fun t => (F j).supply (taxPrice C F t))
      (((F j).d2c ((F j).supply p₀))⁻¹ * p') 0 := fun j =>
    HasDerivAt.comp (h := taxPrice C F) (0 : ℝ) ((F j).supply_hasDerivAt (hqa j) (hc2 j)) hp'
  have hrange : ∀ᶠ t in 𝓝 (0 : ℝ), t ∈ taxRange C F := isOpen_Ioo.mem_nhds h0
  have hcont2 : ContinuousAt (fun t => taxPrice C F t + t) 0 := hcont.add continuousAt_id
  have e4 : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ i,
      (C i).dφ ((C i).demand (taxPrice C F t + t)) = taxPrice C F t + t := by
    have hall : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ i, taxPrice C F t + t < (C i).dφ 0 :=
      eventually_all.2 fun i => hcont2.eventually (gt_mem_nhds (by simpa using hxa i))
    filter_upwards [hall, hrange] with t ht hr i
    have hpt : 0 < taxPrice C F t + t := by
      linarith [(taxPrice_spec C F hr).1, hr.1]
    exact (C i).dφ_demand hpt (((C i).demand_pos_iff hpt).2 (ht i))
  have e5 : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ j, (F j).dc ((F j).supply (taxPrice C F t)) = taxPrice C F t := by
    have hall : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ j, (F j).dc 0 < taxPrice C F t :=
      eventually_all.2 fun j => hcont.eventually (lt_mem_nhds (hqa j))
    filter_upwards [hall] with t ht j
    exact ((F j).supply_foc _).2.2 (((F j).supply_pos_iff _).2 (ht j)) |>.symm
  have e6 : ∀ᶠ t in 𝓝 (0 : ℝ), ∑ i, (C i).demand (taxPrice C F t + t) =
      ∑ j, (F j).supply (taxPrice C F t) := by
    filter_upwards [hrange] with t hr
    exact (taxPrice_spec C F hr).2.2
  have hpos0 : ∀ i, 0 < (C i).demand (p₀ + 0) := fun i => by
    rw [add_zero]; exact ((C i).demand_pos_iff hp0).2 (hxa i)
  have hform := exercise_10_C_5 (fun i => (C i).dφ) (fun i => (C i).d2φ) (fun j => (F j).dc)
    (fun j => (F j).d2c) (fun i t => (C i).demand (taxPrice C F t + t))
    (fun j t => (F j).supply (taxPrice C F t)) (taxPrice C F) (t₀ := 0) _ _
    (fun i => foc_hasDerivAt (C i).hasDeriv2 (hpos0 i))
    (fun j => foc_hasDerivAt (F j).hasDeriv2 (((F j).supply_pos_iff _).2 (hqa j)))
    (fun i => (C i).d2φ_neg _ (hpos0 i).le) (fun j => hc2 j) hx hq hp' e4 e5 e6
  exact ⟨p', hp', hx, hq, e4, e5, e6, hform⟩

/-- **Instance of `exercise_10_C_5_derived`**: the economy of `example_10_C_1_instance` (one
consumer `2(1 - e^{-x})`, one firm `q + q²/2`) satisfies its hypotheses. -/
theorem inst_exercise_10_C_5 :
    let C := fun _ : Fin 1 => expConsumer 2 two_pos
    let F := fun _ : Fin 1 => quadFirm 1 1 one_pos one_pos
    (0 : ℝ) ∈ taxRange C F ∧ (∀ i, taxPrice C F 0 < (C i).dφ 0) ∧
      (∀ j, (F j).dc 0 < taxPrice C F 0) ∧
      (∀ j, 0 < (F j).d2c ((F j).supply (taxPrice C F 0))) := by
  intro C F
  have hM : maxMB C = 2 := by simp [maxMB, C, expConsumer, Finset.sup'_const]
  have hm : minMC F = 1 := by
    simp [minMC, F, quadFirm, quadFirmBase, QLFirmStrict.dc, Finset.inf'_const]
  have h0 : (0 : ℝ) ∈ taxRange C F := by
    simp only [taxRange, hM, hm, Set.mem_Ioo]; norm_num
  obtain ⟨a, b, -⟩ := taxPrice_spec C F h0
  rw [hm] at a
  rw [hM, add_zero] at b
  have hd : ∀ i, (C i).dφ 0 = 2 := fun _ => by simp [C, expConsumer]
  have hdc : ∀ j, (F j).dc 0 = 1 := fun _ => by simp [F, quadFirm, quadFirmBase, QLFirmStrict.dc]
  exact ⟨h0, fun i => by rw [hd i]; exact b, fun j => by rw [hdc j]; exact a,
    fun _ => by simp [F, quadFirm, quadFirmBase, QLFirmStrict.d2c]⟩

end MWG.CompetitiveMarkets
