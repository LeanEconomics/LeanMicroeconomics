/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGExternalitiesPublicGoods.Tools
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Exercises 11.D.5-11.D.7 (MWG, pp. 380-381)

* **Exercise 11.D.5** (the problem of the commons). `f(b)` fish from `b` boats, `f' > 0`, `f'`
  strictly decreasing, and `f(0) = 0` (no boats, no fish; assumed, MWG leaves it implicit).
  (a) Free entry: `p f(b*)/b* = r` (`IsCommonsEq`); (b) the optimum: `p f'(b°) ≤ r`, equality if
  `b° > 0` (`exercise_11_D_5b`), and `b° < b*` (`exercise_11_D_5_compare`); (c) the per-boat tax
  `τ = p f(b°)/b° - r` makes `b°` the unique entry equilibrium (`exercise_11_D_5c`); (d) a single
  owner chooses `b°` (`exercise_11_D_5d`). An instance with `f(b) = 1 - e^{-b}`.
* **Exercise 11.D.6** (bargaining coalitions). `π(h) = α + βh - μh²`, `φ(h) = γ - ηh`, `I` consumers
  with `φ(h)/I + w` each. A coalition of `k` consumers (fraction `θ = k/I`) offers the firm
  `h(θ) = (β - θη)/(2μ)` and the payment that leaves it at `π(β/(2μ))` (`exercise_11_D_6_offer`).
  Staying in is optimal iff `k ≤ 2` and staying out iff `k ≥ 1` (`exercise_11_D_6_stay`,
  `exercise_11_D_6_join`). So with `I = 1` the coalition forms and `h° = h(1)` results; for `I ≥ 2`
  the equilibria are `k ∈ {1, 2}`, `θ ∈ {1/I, 2/I}`. **Correction**: for `I = 2`, `θ = 1` is an
  equilibrium, so "`θ < 1` when `I > 1`" fails at `I = 2`; it holds for `I ≥ 3`, where too much of
  the externality results (`exercise_11_D_6a`). (b) Equilibrium `θ ≤ 2/I → 0` (`exercise_11_D_6b`).
* **Exercise 11.D.7** (neighborhood prestige). (a) Everyone in `A` is never an equilibrium; everyone
  in `B` is not an equilibrium when a lone mover to `A` gets her own prestige, but is one if the
  empty neighborhood is assigned prestige `0` (correction: the claim depends on that convention).
  (b) With different prestige levels the richer-prestige neighborhood is `A` and the allocation is a
  cutoff; the cutoff equilibrium has `θ̂ = 2(c_A - c_B) - 1`. (c) Raising the cutoff slightly makes
  every type strictly better off.
-/

namespace MWG.ExternalitiesPublicGoods

open MWG.CompetitiveMarkets

/-! ## Exercise 11.D.5 -/

/-- Average product exceeds marginal product: for `b > 0`, `f(b)/b > f'(b)` (`f(0) = 0`, `f'`
strictly decreasing). -/
theorem avg_gt_marginal {f df : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (df x) x)
    (hanti : StrictAntiOn df (Set.Ici 0)) (h0 : f 0 = 0) {b : ℝ} (hb : 0 < b) :
    df b < f b / b ∧ f b / b < df 0 := by
  obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope f df hb
    (fun x _ => (hf x).continuousAt.continuousWithinAt) (fun x _ => hf x)
  rw [h0, sub_zero, sub_zero] at hξeq
  rw [← hξeq]
  exact ⟨hanti (Set.mem_Ici.2 hξ.1.le) (Set.mem_Ici.2 hb.le) hξ.2,
    hanti (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hξ.1.le) hξ.1⟩

/-- The average product `f(b)/b` is strictly decreasing on `(0, ∞)`. -/
theorem avg_strictAnti {f df : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (df x) x)
    (hanti : StrictAntiOn df (Set.Ici 0)) (h0 : f 0 = 0) :
    StrictAntiOn (fun b => f b / b) (Set.Ioi 0) := by
  intro a ha b hb hab
  have ha' : (0 : ℝ) < a := ha
  have hb' : (0 : ℝ) < b := hb
  -- `f(b) - f(a) = f'(ξ)(b - a)` with `f'(ξ) < f'(a) < f(a)/a`
  obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope f df hab
    (fun x _ => (hf x).continuousAt.continuousWithinAt) (fun x _ => hf x)
  have h1 : df ξ < df a := hanti (Set.mem_Ici.2 ha'.le) (Set.mem_Ici.2 (ha'.le.trans hξ.1.le)) hξ.1
  have h2 := (avg_gt_marginal hf hanti h0 ha').1
  have hfb : f b = f a + df ξ * (b - a) := by
    rw [hξeq]; field_simp [(sub_pos.2 hab).ne']; ring
  simp only
  rw [div_lt_div_iff₀ hb' ha', hfb]
  rw [lt_div_iff₀ ha'] at h2
  nlinarith [mul_lt_mul_of_pos_right h1 (sub_pos.2 hab)]

/-- **Exercise 11.D.5(a)** (MWG, p. 380). A free-entry equilibrium number of boats: either
`b* > 0` and each boat's catch value equals its cost, `p f(b*)/b* = r`, or no boat would earn
`r`: `b* = 0` and `p f'(0) ≤ r`. -/
def IsCommonsEq (f df : ℝ → ℝ) (p r b : ℝ) : Prop :=
  (0 < b ∧ p * (f b / b) = r) ∨ (b = 0 ∧ p * df 0 ≤ r)

/-- **Exercise 11.D.5(b)** (MWG, p. 380). The optimal number of boats maximizes `p f(b) - r b` on
`b ≥ 0`: iff `p f'(b°) ≤ r`, with equality if `b° > 0`. -/
theorem exercise_11_D_5b {f df : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (df x) x)
    (hanti : StrictAntiOn df (Set.Ici 0)) {p r : ℝ} (hp : 0 < p) (b : ℝ) :
    (0 ≤ b ∧ ∀ y, 0 ≤ y → p * f y - r * y ≤ p * f b - r * b) ↔
      0 ≤ b ∧ p * df b ≤ r ∧ (0 < b → p * df b = r) := by
  have hg : ∀ x, HasDerivAt (fun y => p * f y - r * y) (p * df x - r) x := fun x => by
    have h2 : HasDerivAt (fun y => r * y) r x := by simpa using (hasDerivAt_id x).const_mul r
    exact ((hf x).const_mul p).sub h2
  have hga : AntitoneOn (fun x => p * df x - r) (Set.Ici 0) := fun a ha b hb hab => by
    have := hanti.antitoneOn ha hb hab; simp only; nlinarith
  rw [kt_isMax_iff hg hga]
  simp only [IsFOCSol]
  constructor
  · rintro ⟨a, b, c⟩; exact ⟨a, by linarith, fun h => by linarith [c h]⟩
  · rintro ⟨a, b, c⟩; exact ⟨a, by linarith, fun h => by linarith [c h]⟩

/-- **Exercise 11.D.5(a)-(b), the comparison.** At an interior free-entry equilibrium too many
boats are sent out: `b° < b*` (the entrant ignores the catch she takes from the others). -/
theorem exercise_11_D_5_compare {f df : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (df x) x)
    (hanti : StrictAntiOn df (Set.Ici 0)) (h0 : f 0 = 0) {p r bs bo : ℝ} (hp : 0 < p)
    (hbs : 0 < bs) (heq : p * (f bs / bs) = r)
    (hopt : 0 ≤ bo ∧ p * df bo ≤ r ∧ (0 < bo → p * df bo = r)) : bo < bs := by
  rcases eq_or_lt_of_le hopt.1 with h | hbo
  · rw [← h]; exact hbs
  · by_contra hle
    push Not at hle
    have h1 := (avg_gt_marginal hf hanti h0 hbs).1
    have h2 : df bo ≤ df bs := hanti.antitoneOn (Set.mem_Ici.2 hbs.le) (Set.mem_Ici.2 hbo.le) hle
    have := hopt.2.2 hbo
    nlinarith

/-- **Exercise 11.D.5(c)** (MWG, p. 380). With `b° > 0`, the per-boat tax
`τ = p f(b°)/b° - r > 0` makes `b°` the unique interior free-entry equilibrium:
`p f(b)/b = r + τ` iff `b = b°`. -/
theorem exercise_11_D_5c {f df : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (df x) x)
    (hanti : StrictAntiOn df (Set.Ici 0)) (h0 : f 0 = 0) {p r bo : ℝ} (hp : 0 < p)
    (hbo : 0 < bo) (hfoc : p * df bo = r) :
    0 < p * (f bo / bo) - r ∧
      ∀ b, 0 < b → (p * (f b / b) = r + (p * (f bo / bo) - r) ↔ b = bo) := by
  refine ⟨by have := (avg_gt_marginal hf hanti h0 hbo).1; nlinarith, fun b hb => ⟨fun h => ?_,
    fun h => by rw [h]; ring⟩⟩
  have hav : f b / b = f bo / bo := by
    have : p * (f b / b) = p * (f bo / bo) := by linarith
    exact mul_left_cancel₀ hp.ne' this
  exact (avg_strictAnti hf hanti h0).injOn hb hbo hav

/-- **Exercise 11.D.5(d)** (MWG, p. 380). A single owner of the lake chooses `b` to maximize her
profit `p f(b) - r b`, i.e. exactly the optimal number of boats. -/
theorem exercise_11_D_5d (f : ℝ → ℝ) (p r b : ℝ) :
    (0 ≤ b ∧ ∀ y, 0 ≤ y → p * f y - r * y ≤ p * f b - r * b) ↔
      (0 ≤ b ∧ ∀ y, 0 ≤ y → p * f y - r * y ≤ p * f b - r * b) := Iff.rfl

/-- An instance of Exercise 11.D.5: `f(b) = 1 - e^{-b}`, `p = 2`, `r = 1`. The optimum is
`b° = log 2`, and a free-entry equilibrium `b* ∈ (1, 2)` exists. -/
theorem exercise_11_D_5_instance :
    (∀ x, HasDerivAt (fun b => 1 - Real.exp (-b)) (Real.exp (-x)) x) ∧
      StrictAntiOn (fun x => Real.exp (-x)) (Set.Ici 0) ∧ (1 - Real.exp (-0) = 0) ∧
      (0 ≤ Real.log 2 ∧ 2 * Real.exp (-Real.log 2) ≤ 1 ∧
        (0 < Real.log 2 → 2 * Real.exp (-Real.log 2) = 1)) ∧
      ∃ bs, 1 < bs ∧ bs < 2 ∧ 2 * ((1 - Real.exp (-bs)) / bs) = 1 := by
  have hd : ∀ x, HasDerivAt (fun b => 1 - Real.exp (-b)) (Real.exp (-x)) x := fun x => by
    have := ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).const_sub 1
    simpa using this
  have e2 : 2 * Real.exp (-Real.log 2) = 1 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  refine ⟨hd, fun a _ b _ hab => Real.exp_lt_exp.2 (by linarith), by simp,
    ⟨(Real.log_pos (by norm_num)).le, e2.le, fun _ => e2⟩, ?_⟩
  -- intermediate value theorem for `g(b) = 2(1 - e^{-b}) - b` on `[1, 2]`
  have hcont : ContinuousOn (fun b : ℝ => 2 * (1 - Real.exp (-b)) - b) (Set.Icc 1 2) :=
    ((continuous_const.mul (continuous_const.sub (Real.continuous_exp.comp
      continuous_neg))).sub continuous_id).continuousOn
  have hg1 : 0 < 2 * (1 - Real.exp (-1)) - 1 := by
    have : Real.exp (-1) < 1 / 2 := by
      rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos 1) (by norm_num)]
      have := Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)
      linarith
    linarith
  have hg2 : 2 * (1 - Real.exp (-2)) - 2 < 0 := by
    have := Real.exp_pos (-2); linarith
  obtain ⟨bs, hbs, hbs0⟩ := intermediate_value_Icc' (by norm_num : (1 : ℝ) ≤ 2) hcont
    ⟨hg2.le, hg1.le⟩
  have hne1 : bs ≠ 1 := fun h => by rw [h] at hbs0; linarith
  have hne2 : bs ≠ 2 := fun h => by rw [h] at hbs0; linarith
  refine ⟨bs, lt_of_le_of_ne hbs.1 (Ne.symm hne1), lt_of_le_of_ne hbs.2 hne2, ?_⟩
  have hpos : 0 < bs := by linarith [hbs.1]
  simp only at hbs0
  field_simp
  linarith

/-! ## Exercise 11.D.6 -/

/-- The data of Exercise 11.D.6: `π(h) = α + βh - μh²`, `φ(h) = γ - ηh`. -/
structure LandModel where
  α : ℝ
  β : ℝ
  μ : ℝ
  γ : ℝ
  η : ℝ
  hμ : 0 < μ
  hη : 0 < η
  hβη : η ≤ β

namespace LandModel

variable (L : LandModel)

/-- The firm's profit. -/
def prof (h : ℝ) : ℝ := L.α + L.β * h - L.μ * h ^ 2

/-- The total land yield. -/
def yld (h : ℝ) : ℝ := L.γ - L.η * h

/-- The coalition's choice of `h` when it holds the fraction `θ`. -/
noncomputable def hθ (θ : ℝ) : ℝ := (L.β - θ * L.η) / (2 * L.μ)

/-- The payment to the firm: its loss relative to its unconstrained choice `β/(2μ)`. -/
noncomputable def pay (θ : ℝ) : ℝ := L.prof (L.β / (2 * L.μ)) - L.prof (L.hθ θ)

/-- **Exercise 11.D.6** (MWG, p. 380), the subgame after membership. A coalition holding the
fraction `θ ∈ [0, 1]` offers `(h, T)` maximizing `θφ(h) - T` subject to the firm's acceptance
`π(h) + T ≥ π(β/(2μ))`: the offer is `h = h(θ) = (β - θη)/(2μ)`, `T = π(β/(2μ)) - π(h(θ))`. -/
theorem exercise_11_D_6_offer {θ : ℝ} (hθ1 : θ ≤ 1) (h T : ℝ) :
    IsTIOLIOffer (Set.Ici 0) (fun h => θ * L.yld h) L.prof (L.prof (L.β / (2 * L.μ))) h (-T) ↔
      h = L.hθ θ ∧ T = L.pay θ := by
  rw [tioli_iff]
  have hθpos : 0 ≤ L.hθ θ := by
    simp only [hθ]
    apply div_nonneg _ (by linarith [L.hμ])
    nlinarith [L.hη, L.hβη]
  have key : ∀ y, θ * L.yld y + L.prof y =
      θ * L.γ + L.α - L.μ * (y - L.hθ θ) ^ 2 + L.μ * L.hθ θ ^ 2 := fun y => by
    simp only [yld, prof, hθ]; field_simp [L.hμ.ne']; ring
  simp only [Set.mem_Ici, key]
  constructor
  · rintro ⟨h0, hmax, hT⟩
    have := hmax (L.hθ θ) hθpos
    have hh : h = L.hθ θ := by
      have : L.μ * (h - L.hθ θ) ^ 2 ≤ 0 := by nlinarith
      have h2 : (h - L.hθ θ) ^ 2 = 0 := le_antisymm (by
        by_contra hc; push Not at hc; nlinarith [L.hμ]) (sq_nonneg _)
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h2
      linarith
    refine ⟨hh, ?_⟩
    rw [pay, ← hh]; linarith
  · rintro ⟨rfl, hT⟩
    refine ⟨hθpos, fun y _ => by nlinarith [sq_nonneg (y - L.hθ θ), L.hμ], ?_⟩
    rw [hT, pay]; ring

/-- A member's payoff in a coalition of `k ≥ 1` of the `I` consumers: her share `φ(h)/I` of the
yield less her share `T/k` of the payment. -/
noncomputable def memberPay (I k : ℕ) : ℝ := L.yld (L.hθ (k / I)) / I - L.pay (k / I) / k

/-- A non-member's payoff when the coalition has `k` members. -/
noncomputable def outPay (I k : ℕ) : ℝ := L.yld (L.hθ (k / I)) / I

/-- **Exercise 11.D.6**: a member of a `k`-coalition gains `(η²/(4μI²))(2 - k)` by staying in
rather than leaving (so the coalition shrinks to `k - 1`). -/
theorem exercise_11_D_6_stay (I k : ℕ) (hI : 0 < I) (hk : 1 ≤ k) :
    L.memberPay I k - L.outPay I (k - 1) = L.η ^ 2 / (4 * L.μ * I ^ 2) * (2 - k) := by
  have hI' : (I : ℝ) ≠ 0 := by positivity
  have hk' : (k : ℝ) ≠ 0 := (by exact_mod_cast (show 0 < k by omega) : (0 : ℝ) < k).ne'
  simp only [memberPay, outPay, pay, prof, yld, hθ, Nat.cast_sub hk, Nat.cast_one]
  field_simp [L.hμ.ne']
  ring

/-- **Exercise 11.D.6**: a non-member of a `k`-coalition gains `(η²/(4μI²))(1 - k)` by joining. -/
theorem exercise_11_D_6_join (I k : ℕ) (hI : 0 < I) :
    L.memberPay I (k + 1) - L.outPay I k = L.η ^ 2 / (4 * L.μ * I ^ 2) * (1 - k) := by
  have := L.exercise_11_D_6_stay I (k + 1) hI (by omega)
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] at this
  rw [this]; ring

/-- A subgame-perfect equilibrium membership size `k ∈ {0, …, I}`: no member wants to leave and
no non-member wants to join. -/
def IsMembershipEq (I k : ℕ) : Prop :=
  k ≤ I ∧ (1 ≤ k → L.outPay I (k - 1) ≤ L.memberPay I k) ∧
    (k < I → L.memberPay I (k + 1) ≤ L.outPay I k)

/-- The equilibrium membership sizes are `k ∈ {1, 2}` (intersected with `{0, …, I}`). -/
theorem membershipEq_iff (I k : ℕ) (hI : 0 < I) :
    L.IsMembershipEq I k ↔ k ≤ I ∧ (1 ≤ k → k ≤ 2) ∧ (k < I → 1 ≤ k) := by
  have hc : 0 < L.η ^ 2 / (4 * L.μ * I ^ 2) := by
    have := L.hμ; have := L.hη; positivity
  simp only [IsMembershipEq]
  refine and_congr Iff.rfl (and_congr ?_ ?_)
  · refine imp_congr_right fun hk => ?_
    have := L.exercise_11_D_6_stay I k hI hk
    constructor
    · intro h
      have h2 : (0 : ℝ) ≤ L.η ^ 2 / (4 * L.μ * I ^ 2) * (2 - k) := by linarith
      have : (k : ℝ) ≤ 2 := by
        by_contra hk2; push Not at hk2; nlinarith
      exact_mod_cast this
    · intro h
      have : (k : ℝ) ≤ 2 := by exact_mod_cast h
      nlinarith
  · refine imp_congr_right fun _ => ?_
    have := L.exercise_11_D_6_join I k hI
    constructor
    · intro h
      have : (1 : ℝ) ≤ k := by
        by_contra hk1; push Not at hk1; nlinarith
      exact_mod_cast this
    · intro h
      have : (1 : ℝ) ≤ k := by exact_mod_cast h
      nlinarith

/-- **Exercise 11.D.6(a)** (MWG, p. 380), with **correction**. (i) With one consumer the coalition
forms (`k = 1`, `θ = 1`) and the optimal level `h(1)` (maximizing `φ + π`) results. (ii) With two
consumers `θ = 1` is an equilibrium: the printed claim "`θ < 1` when `I > 1`" fails at `I = 2`.
(iii) With `I ≥ 3` every equilibrium has `θ = k/I ≤ 2/I < 1` and `h(θ) > h(1)`: too much of the
externality. -/
theorem exercise_11_D_6a :
    (∀ k, L.IsMembershipEq 1 k ↔ k = 1) ∧ L.IsMembershipEq 2 2 ∧
      ∀ I k, 3 ≤ I → L.IsMembershipEq I k →
        (k : ℝ) / I < 1 ∧ L.hθ 1 < L.hθ ((k : ℝ) / I) := by
  refine ⟨fun k => ?_, ?_, fun I k hI he => ?_⟩
  · rw [membershipEq_iff _ 1 k one_pos]
    constructor
    · rintro ⟨h1, h2, h3⟩
      rcases Nat.lt_or_ge k 1 with h | h
      · exact absurd (h3 h) (by omega)
      · omega
    · rintro rfl; exact ⟨le_rfl, fun _ => by norm_num, fun h => absurd h (lt_irrefl 1)⟩
  · rw [membershipEq_iff _ 2 2 two_pos]
    exact ⟨le_rfl, fun _ => le_rfl, fun h => absurd h (lt_irrefl 2)⟩
  · have hI0 : 0 < I := by omega
    obtain ⟨_, h2, h3⟩ := (L.membershipEq_iff I k hI0).1 he
    have hk1 : 1 ≤ k := h3 (by omega)
    have hk2 := h2 hk1
    have hIr : (3 : ℝ) ≤ I := by exact_mod_cast hI
    have hkr : (k : ℝ) ≤ 2 := by exact_mod_cast hk2
    have hlt : (k : ℝ) / I < 1 := by rw [div_lt_one (by linarith)]; linarith
    refine ⟨hlt, ?_⟩
    simp only [hθ]
    rw [div_lt_div_iff_of_pos_right (by linarith [L.hμ])]
    nlinarith [L.hη]

/-- **Exercise 11.D.6(b)** (MWG, p. 381). Every equilibrium fraction satisfies `θ = k/I ≤ 2/I`,
which declines in `I` and tends to `0` as `I → ∞`. -/
theorem exercise_11_D_6b (I k : ℕ) (hI : 0 < I) (he : L.IsMembershipEq I k) :
    (k : ℝ) / I ≤ 2 / I := by
  obtain ⟨_, h2, h3⟩ := (L.membershipEq_iff I k hI).1 he
  have hI' : (0 : ℝ) < I := by exact_mod_cast hI
  rcases Nat.eq_zero_or_pos k with h | h
  · rw [h]; simp only [Nat.cast_zero, zero_div]; positivity
  · have : (k : ℝ) ≤ 2 := by exact_mod_cast h2 h
    exact div_le_div_of_nonneg_right this hI'.le

/-- The bound `2/I` tends to `0` as `I → ∞`. -/
theorem exercise_11_D_6b_limit :
    Filter.Tendsto (fun I : ℕ => (2 : ℝ) / I) Filter.atTop (nhds 0) :=
  tendsto_const_div_atTop_nhds_zero_nat 2

end LandModel

/-- An instance of the land model: `π(h) = 1 + 4h - h²`, `φ(h) = 10 - h`. -/
def landEx : LandModel where
  α := 1
  β := 4
  μ := 1
  γ := 10
  η := 1
  hμ := one_pos
  hη := one_pos
  hβη := by norm_num

/-! ## Exercise 11.D.7 -/

/-- The derived utility of a type-`θ` resident of a neighborhood with prestige `p` and building
cost `c`: `(1 + θ)(1 + p) - c`. -/
def nbUtil (θ p c : ℝ) : ℝ := (1 + θ) * (1 + p) - c

/-- **Exercise 11.D.7(a)** (MWG, p. 381): everyone building in `A` (prestige `1/2`, the population
mean) is not an equilibrium: whatever prestige `p_B ≥ 0` the empty neighborhood `B` is assigned,
type `θ = 0` strictly prefers to move to `B`, because `c_A - c_B > 1/2`. -/
theorem exercise_11_D_7a_allA {cA cB : ℝ} (hc : 1 / 2 < cA - cB) {pB : ℝ} (hpB : 0 ≤ pB) :
    nbUtil 0 (1 / 2) cA < nbUtil 0 pB cB := by
  simp only [nbUtil]; linarith

/-- **Exercise 11.D.7(a)**: everyone building in `B` is not an equilibrium if a lone mover to the
empty neighborhood `A` gets her own prestige: type `θ = 1` strictly prefers `A`, since
`c_A - c_B < 1`. -/
theorem exercise_11_D_7a_allB {cA cB : ℝ} (hc : cA - cB < 1) :
    nbUtil 1 (1 / 2) cB < nbUtil 1 1 cA := by
  simp only [nbUtil]; linarith

/-- **Correction to Exercise 11.D.7(a)**: if the empty neighborhood `A` is assigned prestige `0`,
everyone building in `B` is an equilibrium (every type weakly prefers `B`). So "both neighborhoods
must be occupied" depends on how the prestige of an empty neighborhood is defined. -/
theorem exercise_11_D_7a_counterexample {cA cB : ℝ} (hc : 1 / 2 < cA - cB) :
    ∀ θ, 0 ≤ θ → θ ≤ 1 → nbUtil θ 0 cA ≤ nbUtil θ (1 / 2) cB := by
  intro θ h0 _
  simp only [nbUtil]; nlinarith

/-- **Exercise 11.D.7(b)** (MWG, p. 381). In an equilibrium with prestige levels `p_A ≠ p_B` in
which both neighborhoods have a resident (`θ_A` in `A` weakly prefers `A`, `θ_B` in `B` weakly
prefers `B`), necessarily `p_A > p_B`, and every resident of `A` has at least the prestige of every
resident of `B`. -/
theorem exercise_11_D_7b {cA cB pA pB : ℝ} (hc : 0 < cA - cB) (hne : pA ≠ pB)
    (inA : ℝ → Prop)
    (hA : ∀ θ, 0 ≤ θ → θ ≤ 1 → inA θ → nbUtil θ pB cB ≤ nbUtil θ pA cA)
    (hB : ∀ θ, 0 ≤ θ → θ ≤ 1 → ¬ inA θ → nbUtil θ pA cA ≤ nbUtil θ pB cB)
    {θa : ℝ} (ha0 : 0 ≤ θa) (ha1 : θa ≤ 1) (ha : inA θa) :
    pB < pA ∧ ∀ θb, 0 ≤ θb → θb ≤ 1 → ¬ inA θb → θb ≤ θa := by
  have hgt : pB < pA := by
    rcases lt_or_gt_of_ne hne with h | h
    · have := hA θa ha0 ha1 ha
      simp only [nbUtil] at this
      nlinarith
    · exact h
  refine ⟨hgt, fun θb hb0 hb1 hb => ?_⟩
  by_contra hlt
  push Not at hlt
  have h1 := hA θa ha0 ha1 ha
  have h2 := hB θb hb0 hb1 hb
  simp only [nbUtil] at h1 h2
  nlinarith

/-- Average prestige over an interval of types `[a, b]` (uniform distribution): `(a + b)/2`. -/
theorem avg_interval {a b : ℝ} (hab : a < b) : (∫ θ in a..b, θ) / (b - a) = (a + b) / 2 := by
  rw [integral_id]
  field_simp [(sub_pos.2 hab).ne']
  ring

/-- **Exercise 11.D.7(b)**, the cutoff equilibrium. With `A = [θ̂, 1]` and `B = [0, θ̂)`, the
prestige levels are `(1 + θ̂)/2` and `θ̂/2` (`avg_interval`); this allocation is an equilibrium iff
`θ̂ = 2(c_A - c_B) - 1`, which lies in `(0, 1)` when `c_A - c_B ∈ (1/2, 1)`. -/
theorem exercise_11_D_7b_cutoff {cA cB s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    ((∀ θ, s ≤ θ → θ ≤ 1 → nbUtil θ (s / 2) cB ≤ nbUtil θ ((1 + s) / 2) cA) ∧
      (∀ θ, 0 ≤ θ → θ < s → nbUtil θ ((1 + s) / 2) cA ≤ nbUtil θ (s / 2) cB)) ↔
      s = 2 * (cA - cB) - 1 := by
  simp only [nbUtil]
  constructor
  · rintro ⟨h1, h2⟩
    have a := h1 s le_rfl hs1.le
    have b : (1 + s) / 2 ≤ cA - cB := by
      by_contra hlt
      push Not at hlt
      -- a type just below `s` would strictly prefer `A`
      set ε := min (s / 2) ((1 + s) / 2 - (cA - cB))
      have hε : 0 < ε := lt_min (by linarith) (by linarith)
      have := h2 (s - ε) (by linarith [min_le_left (s / 2) ((1 + s) / 2 - (cA - cB))])
        (by linarith)
      have hε2 : ε ≤ (1 + s) / 2 - (cA - cB) := min_le_right _ _
      nlinarith
    nlinarith
  · intro h
    constructor
    · intro θ hθ _; nlinarith
    · intro θ _ hθ; nlinarith

/-- **Exercise 11.D.7(c)** (MWG, p. 381). At the cutoff equilibrium `θ̂ = 2(c_A - c_B) - 1`,
raising the cutoff to `θ̂ + ε` (`0 < ε ≤ 1 - θ̂`) makes every type strictly better off: the
residents of each neighborhood enjoy a higher prestige, and the movers `θ ∈ [θ̂, θ̂ + ε)` were
nearly indifferent. -/
theorem exercise_11_D_7c {cA cB s ε : ℝ} (hs : s = 2 * (cA - cB) - 1) (_hs0 : 0 ≤ s)
    (hε : 0 < ε) (_hε1 : ε ≤ 1 - s) (θ : ℝ) (hθ0 : 0 ≤ θ) (_hθ1 : θ ≤ 1) :
    (if s ≤ θ then nbUtil θ ((1 + s) / 2) cA else nbUtil θ (s / 2) cB) <
      (if s + ε ≤ θ then nbUtil θ ((1 + (s + ε)) / 2) cA else nbUtil θ ((s + ε) / 2) cB) := by
  simp only [nbUtil]
  split_ifs with h1 h2 h2
  · nlinarith
  · -- the movers
    push Not at h2
    nlinarith
  · exact absurd (by linarith : s ≤ θ) h1
  · nlinarith

end MWG.ExternalitiesPublicGoods
