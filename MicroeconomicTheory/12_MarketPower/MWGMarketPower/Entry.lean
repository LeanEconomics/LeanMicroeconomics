/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGMarketPower.Cournot
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Entry

MWG, Section 12.E, pp. 405-411, and Exercise 12.E.2.

The two-stage entry model: firms decide to enter (paying `K > 0`), then the `J` entrants play a
unique symmetric stage-2 equilibrium with profit `π_J` per firm. With the convention that a firm
enters when indifferent, `J*` entrants form an SPNE iff (12.E.1) `π_{J*} ≥ K` and
(12.E.2) `π_{J*+1} < K` (`IsEntryEquilibrium`).

* `entry_equilibrium_unique`, `entry_equilibrium_exists`, `entry_equilibrium_iff`: with `π_J`
  decreasing, the equilibrium number is the unique `Ĵ` with `π_J ≥ K` for `J ≤ Ĵ` and `π_J < K`
  for `J > Ĵ`; `footnote_12_22`: with weak inequalities `Ĵ − 1` is also an equilibrium when
  `π_Ĵ = K`.
* `example_12_E_1`: Cournot entry, `π_J = ((a − c)/(J + 1))²/b`, and `J*` is the largest
  integer `≤ J̃ = (a − c)/√(bK) − 1`; comparative statics in `K`.
* `example_12_E_2`: Bertrand entry, `J* = 1`.
* `entryWelfare` (12.E.5), `example_12_E_3`: the linear welfare function and the three numerical
  cases `J° = 2, 3, 8` with `J* = 4, 7, 26`.
* `exercise_12_E_2`, `proposition_12_E_1`: under (A1)-(A3) the equilibrium number of entrants
  is at least `J° − 1`, for every welfare maximizer `J°` (so also footnote 23).
-/

namespace MWG.MarketPower

open Set MWG.CompetitiveMarkets

/-- **Conditions (12.E.1)-(12.E.2)** (MWG, p. 406): `J ≥ 1` entrants form an equilibrium of the
two-stage entry game (firms enter when indifferent) iff `π_J ≥ K` and `π_{J+1} < K`. -/
def IsEntryEquilibrium (π : ℕ → ℝ) (K : ℝ) (J : ℕ) : Prop := 1 ≤ J ∧ K ≤ π J ∧ π (J + 1) < K

/-- With `π_J` decreasing there is at most one equilibrium number of firms (MWG, p. 406). -/
theorem entry_equilibrium_unique {π : ℕ → ℝ} {K : ℝ} (hπ : Antitone π) {J₁ J₂ : ℕ}
    (h₁ : IsEntryEquilibrium π K J₁) (h₂ : IsEntryEquilibrium π K J₂) : J₁ = J₂ := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have := hπ (show J₁ + 1 ≤ J₂ by omega); linarith [h₁.2.2, h₂.2.1]
  · have := hπ (show J₂ + 1 ≤ J₁ by omega); linarith [h₂.2.2, h₁.2.1]

/-- With `π_J` decreasing, `π₁ ≥ K` and `π_J < K` for some `J` (e.g. `π_J → 0`), an equilibrium
number of entrants exists (MWG, p. 406). -/
theorem entry_equilibrium_exists {π : ℕ → ℝ} {K : ℝ} (h1 : K ≤ π 1)
    (hex : ∃ n, π (n + 1) < K) : ∃ J, IsEntryEquilibrium π K J := by
  classical
  set n := Nat.find hex with hn
  have hspec : π (n + 1) < K := Nat.find_spec hex
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · rw [h0] at hspec; linarith
  · refine ⟨n, hpos, ?_, hspec⟩
    have := Nat.find_min hex (show n - 1 < n by omega)
    push Not at this
    rwa [Nat.sub_add_cancel hpos] at this

/-- **The equilibrium number of firms** (MWG, p. 406). With `π_J` decreasing, `J*` is an
equilibrium iff `π_J ≥ K` for all `1 ≤ J ≤ J*` and `π_J < K` for all `J > J*`. -/
theorem entry_equilibrium_iff {π : ℕ → ℝ} {K : ℝ} (hπ : Antitone π) {J : ℕ} (hJ : 1 ≤ J) :
    IsEntryEquilibrium π K J ↔ (∀ J', J' ≤ J → K ≤ π J') ∧ ∀ J', J < J' → π J' < K := by
  constructor
  · rintro ⟨-, h1, h2⟩
    exact ⟨fun J' hJ' => h1.trans (hπ hJ'), fun J' hJ' => lt_of_le_of_lt (hπ hJ') h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨hJ, h1 J le_rfl, h2 (J + 1) (by omega)⟩

/-- **Footnote 22** (MWG, p. 406). If firms need not enter when indifferent, the conditions are
`π_{J*} ≥ K` and `π_{J*+1} ≤ K`; when `π_Ĵ = K` exactly, both `Ĵ` and `Ĵ − 1` satisfy them. -/
theorem footnote_12_22 {π : ℕ → ℝ} {K : ℝ} (hπ : Antitone π) {J : ℕ} (hJ : 2 ≤ J)
    (heq : π J = K) (hnext : π (J + 1) ≤ K) :
    (K ≤ π J ∧ π (J + 1) ≤ K) ∧ (K ≤ π (J - 1) ∧ π (J - 1 + 1) ≤ K) := by
  refine ⟨⟨heq.ge, hnext⟩, ⟨heq ▸ hπ (Nat.sub_le J 1), ?_⟩⟩
  rw [Nat.sub_add_cancel (by omega)]; exact heq.le

/-! ### Examples 12.E.1 and 12.E.2 -/

/-- Per-firm Cournot profit with `J` firms, linear demand and constant cost (12.E.4). -/
noncomputable def cournotEntryProfit (a b c : ℝ) (J : ℕ) : ℝ := ((a - c) / (J + 1)) ^ 2 / b

/-- **Example 12.E.1** (MWG, p. 407). With `J` Cournot firms, `p(q) = a − bq`, `c(q) = cq`:
each produces `q_J = (a − c)/(b(J + 1))` (12.E.3) at the price `(a + Jc)/(J + 1)`
(Exercise 12.C.7) and earns `π_J = ((a − c)/(J + 1))²/b` (12.E.4); `π_J` is strictly decreasing,
`π_J → 0` and `Jq_J → (a − c)/b`. -/
theorem example_12_E_1 {a b c : ℝ} (hac : c < a) (hb : 0 < b) :
    (∀ J : ℕ, ((a + J * c) / (J + 1) - c) * ((a - c) / (b * (J + 1))) =
      cournotEntryProfit a b c J) ∧
    StrictAnti (cournotEntryProfit a b c) ∧
    Filter.Tendsto (cournotEntryProfit a b c) Filter.atTop (nhds 0) ∧
    Filter.Tendsto (fun J : ℕ => J * ((a - c) / (b * (J + 1)))) Filter.atTop
      (nhds ((a - c) / b)) := by
  have hA : 0 < a - c := by linarith
  refine ⟨fun J => by unfold cournotEntryProfit; field_simp; ring, fun m n hmn => ?_, ?_, ?_⟩
  · unfold cournotEntryProfit
    have : (m : ℝ) < n := by exact_mod_cast hmn
    apply div_lt_div_of_pos_right _ hb
    have h1 : (a - c) / (n + 1) < (a - c) / (m + 1) :=
      div_lt_div_of_pos_left hA (by positivity) (by linarith)
    have h2 : 0 < (a - c) / (n + 1) := by positivity
    nlinarith
  · unfold cournotEntryProfit
    have h : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 := (h.mul h).const_mul ((a - c) ^ 2 / b)
    rw [mul_zero, mul_zero] at h2
    refine h2.congr fun J => ?_
    field_simp
  · have := (exercise_12_C_7_limits hac hb).2.2.2.2
    refine this.congr fun J => ?_
    field_simp

/-- **Example 12.E.1, the equilibrium number of firms** (MWG, p. 407). `J ≥ 1` is the
equilibrium number of Cournot entrants iff `(J + 1)² ≤ (a − c)²/(bK) < (J + 2)²`, i.e. iff `J`
is the largest integer not exceeding `J̃ = (a − c)/√(bK) − 1`. -/
theorem example_12_E_1_number {a b c K : ℝ} (hb : 0 < b) (hK : 0 < K) {J : ℕ}
    (hJ : 1 ≤ J) :
    IsEntryEquilibrium (cournotEntryProfit a b c) K J ↔
      ((J : ℝ) + 1) ^ 2 ≤ (a - c) ^ 2 / (b * K) ∧ (a - c) ^ 2 / (b * K) < ((J : ℝ) + 2) ^ 2 := by
  have hbK : 0 < b * K := by positivity
  have aux : ∀ n : ℝ, 0 < n → ((K ≤ ((a - c) / n) ^ 2 / b ↔ n ^ 2 ≤ (a - c) ^ 2 / (b * K)) ∧
      (((a - c) / n) ^ 2 / b < K ↔ (a - c) ^ 2 / (b * K) < n ^ 2)) := by
    intro n hn
    have hn2 : 0 < n ^ 2 := by positivity
    rw [le_div_iff₀ hb, div_pow, le_div_iff₀ hn2, le_div_iff₀ hbK, div_lt_iff₀ hb,
      div_lt_iff₀ hn2, div_lt_iff₀ hbK]
    constructor
    · constructor <;> intro h <;> linarith
    · constructor <;> intro h <;> linarith
  unfold IsEntryEquilibrium cournotEntryProfit
  push_cast
  rw [(aux _ (by positivity)).1, (aux _ (by positivity)).2]
  simp only [hJ, true_and]
  rw [show ((J : ℝ) + 1 + 1) = J + 2 by ring]

/-- **Example 12.E.1, comparative statics** (MWG, p. 407). A lower entry cost weakly raises the
equilibrium number of firms, and `J* → ∞` as `K → 0`. -/
theorem example_12_E_1_statics {a b c : ℝ} (hac : c < a) (hb : 0 < b) {K K' : ℝ}
    (hKK : K' ≤ K) {J J' : ℕ}
    (hJ : IsEntryEquilibrium (cournotEntryProfit a b c) K J)
    (hJ' : IsEntryEquilibrium (cournotEntryProfit a b c) K' J') :
    J ≤ J' ∧ ∀ N : ℕ, ∃ K₀ > 0, ∀ K'', 0 < K'' → K'' < K₀ → ∀ J'',
      IsEntryEquilibrium (cournotEntryProfit a b c) K'' J'' → N ≤ J'' := by
  have hanti : StrictAnti (cournotEntryProfit a b c) := (example_12_E_1 hac hb).2.1
  constructor
  · by_contra hlt
    push Not at hlt
    have := hanti.antitone (show J' + 1 ≤ J by omega)
    linarith [hJ.2.1, hJ'.2.2]
  · intro N
    refine ⟨cournotEntryProfit a b c N, by unfold cournotEntryProfit; positivity,
      fun K'' _ hK'' J'' hJ'' => ?_⟩
    by_contra hlt
    push Not at hlt
    have := hanti.antitone (show J'' + 1 ≤ N by omega)
    linarith [hJ''.2.2]

/-- **Example 12.E.2** (MWG, p. 407). With Bertrand competition in stage 2, `π₁ = πᵐ` and
`π_J = 0` for `J ≥ 2`; if `πᵐ ≥ K > 0`, the unique equilibrium has one entrant, the monopolist. -/
theorem example_12_E_2 {πm K : ℝ} (hK : 0 < K) (hπm : K ≤ πm) :
    let π : ℕ → ℝ := fun J => if J = 1 then πm else 0
    IsEntryEquilibrium π K 1 ∧ ∀ J, IsEntryEquilibrium π K J → J = 1 := by
  intro π
  refine ⟨⟨le_rfl, by simp [π, hπm], by simp [π, hK]⟩, fun J hJ => ?_⟩
  by_contra hne
  have := hJ.2.1
  simp only [π, hne, ite_false] at this
  linarith

/-! ### Entry and welfare -/

/-- **Social welfare with `J` firms** (12.E.5), MWG, p. 408:
`W(J) = ∫₀^{Jq_J} p(s) ds − Jc(q_J) − JK`. -/
noncomputable def entryWelfare (p c : ℝ → ℝ) (q : ℕ → ℝ) (K : ℝ) (J : ℕ) : ℝ :=
  (∫ s in (0 : ℝ)..(J * q J), p s) - J * c (q J) - J * K

/-- The linear welfare function of Example 12.E.3:
`W(J) = ((a − c)²/b)(J² + 2J)/(2(J + 1)²) − JK`. -/
theorem entryWelfare_linear {a b c K : ℝ} (hb : 0 < b) (J : ℕ) :
    entryWelfare (fun s => a - b * s) (fun q => c * q) (fun J => (a - c) / (b * (J + 1))) K J =
      (a - c) ^ 2 / b * ((J ^ 2 + 2 * J) / (2 * (J + 1) ^ 2)) - J * K := by
  unfold entryWelfare
  simp only []
  rw [intervalIntegral.integral_sub intervalIntegrable_const
    ((by fun_prop : Continuous fun s : ℝ => b * s).intervalIntegrable _ _),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_id]
  simp only [smul_eq_mul]
  field_simp
  ring

/-- The welfare comparison polynomial. -/
theorem example_12_E_3_aux (A : ℝ) (J : ℝ) (hJ : 0 ≤ J) (m : ℝ) (hm : 0 < m)
    (hA : A = (m + 1) ^ 3) :
    A * ((J ^ 2 + 2 * J) / (2 * (J + 1) ^ 2)) - J ≤
      A * ((m ^ 2 + 2 * m) / (2 * (m + 1) ^ 2)) - m := by
  subst hA
  have h1 : (0 : ℝ) < J + 1 := by linarith
  have h2 : (0 : ℝ) < m + 1 := by linarith
  rw [← sub_nonneg]
  have key : (m + 1) ^ 3 * ((m ^ 2 + 2 * m) / (2 * (m + 1) ^ 2)) - m -
      ((m + 1) ^ 3 * ((J ^ 2 + 2 * J) / (2 * (J + 1) ^ 2)) - J) =
      (J - m) ^ 2 * (2 * J + m + 3) / (2 * (J + 1) ^ 2) := by
    field_simp; ring
  rw [key]
  positivity

/-- **Example 12.E.3** (MWG, p. 408). In the linear Cournot model with `A = (a − c)²/b`, if
`A/K = (J̄ + 1)³` for an integer `J̄`, then `J° = J̄` maximizes welfare among all numbers of firms
(the real welfare function is maximized at `J̄`, where `(J̄ + 1)³ = A/K`, (12.E.6)), while the
equilibrium number is the integer part of `J̃ = (J̄ + 1)^{3/2} − 1` ((12.E.7)). In particular:
`J° = 2` gives `J* = 4`, `J° = 3` gives `J* = 7`, `J° = 8` gives `J* = 26`. -/
theorem example_12_E_3 {a b c K : ℝ} (hb : 0 < b) (hK : 0 < K) (m : ℕ) (hm : 1 ≤ m)
    (hA : (a - c) ^ 2 / b = ((m : ℝ) + 1) ^ 3 * K) :
    (∀ J : ℕ, entryWelfare (fun s => a - b * s) (fun q => c * q)
      (fun J => (a - c) / (b * (J + 1))) K J ≤ entryWelfare (fun s => a - b * s) (fun q => c * q)
      (fun J => (a - c) / (b * (J + 1))) K m) ∧
    ((m = 2 → IsEntryEquilibrium (cournotEntryProfit a b c) K 4) ∧
     (m = 3 → IsEntryEquilibrium (cournotEntryProfit a b c) K 7) ∧
     (m = 8 → IsEntryEquilibrium (cournotEntryProfit a b c) K 26)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  refine ⟨fun J => ?_, ?_, ?_, ?_⟩
  · rw [entryWelfare_linear hb, entryWelfare_linear hb, hA]
    have := example_12_E_3_aux (((m : ℝ) + 1) ^ 3) J (Nat.cast_nonneg J) m hm0 rfl
    have hK' := mul_le_mul_of_nonneg_right this hK.le
    nlinarith
  all_goals intro hmv
  all_goals subst hmv
  all_goals rw [example_12_E_1_number hb hK (by norm_num)]
  all_goals rw [div_mul_eq_div_div, hA, mul_div_assoc, div_self hK.ne', mul_one]
  all_goals norm_num

/-! ### Proposition 12.E.1 -/

/-- **Exercise 12.E.2** (MWG, p. 434). Under (A1)-(A3), `p` nonincreasing and `c` convex
(tangent-line inequality with derivative `c'`), per-firm profit `π_J = p(Jq_J)q_J − c(q_J)` is
nonincreasing in `J`. -/
theorem exercise_12_E_2 {p c c' : ℝ → ℝ} {q : ℕ → ℝ} (hp : Antitone p)
    (hc : ∀ x ∈ Ici (0 : ℝ), HasDerivWithinAt c (c' x) (Ici 0) x) (hc' : MonotoneOn c' (Ici 0))
    (hq0 : ∀ J, 0 ≤ q J)
    (hA1 : ∀ J J' : ℕ, J' ≤ J → J' * q J' ≤ J * q J) (hA2 : ∀ J J' : ℕ, J' ≤ J → q J ≤ q J')
    (hA3 : ∀ J : ℕ, c' (q J) ≤ p (J * q J)) :
    Antitone fun J : ℕ => p (J * q J) * q J - c (q J) := by
  intro J' J hJ
  simp only
  have h1 : p (J * q J) ≤ p (J' * q J') := hp (hA1 J J' hJ)
  have h2 : q J ≤ q J' := hA2 J J' hJ
  -- `p(Q_{J'})q − c(q)` is nondecreasing for `q ≤ q_{J'}`
  have htan := foc_le_tangent_convex hc hc' (hq0 J) (hq0 J')
  have htan2 := foc_le_tangent_convex hc hc' (hq0 J') (hq0 J)
  have h3 : c' (q J) ≤ c' (q J') := hc' (hq0 J) (hq0 J') h2
  nlinarith [hA3 J', mul_le_mul_of_nonneg_right h1 (hq0 J)]

/-- **Proposition 12.E.1** (MWG, p. 409). Suppose the post-entry game satisfies (A1)-(A3),
`p` is nonincreasing and continuous, and `c` is convex (with derivative `c'`) with `c(0) = 0`.
Let `J° ≥ 1` maximize welfare `W(J)` (12.E.5) among `J ≥ 1`. Then any equilibrium number of
entrants satisfies `J* ≥ J° − 1`; indeed `π_{J°−1} ≥ K` (via (12.E.8)). -/
theorem proposition_12_E_1 {p c c' : ℝ → ℝ} {q : ℕ → ℝ} {K : ℝ} (hp : Antitone p)
    (hpc : Continuous p)
    (hc : ∀ x ∈ Ici (0 : ℝ), HasDerivWithinAt c (c' x) (Ici 0) x) (hc' : MonotoneOn c' (Ici 0))
    (hq0 : ∀ J, 0 ≤ q J)
    (hA1 : ∀ J J' : ℕ, J' ≤ J → J' * q J' ≤ J * q J) (hA2 : ∀ J J' : ℕ, J' ≤ J → q J ≤ q J')
    (hA3 : ∀ J : ℕ, c' (q J) ≤ p (J * q J)) {Jo : ℕ} (hJo : 1 ≤ Jo)
    (hmax : ∀ J, 1 ≤ J → entryWelfare p c q K J ≤ entryWelfare p c q K Jo) :
    (2 ≤ Jo → K ≤ p ((Jo - 1 : ℕ) * q (Jo - 1)) * q (Jo - 1) - c (q (Jo - 1))) ∧
    ∀ J, IsEntryEquilibrium (fun J : ℕ => p (J * q J) * q J - c (q J)) K J → Jo - 1 ≤ J := by
  have hanti := exercise_12_E_2 hp hc hc' hq0 hA1 hA2 hA3
  have key : 2 ≤ Jo → K ≤ p ((Jo - 1 : ℕ) * q (Jo - 1)) * q (Jo - 1) - c (q (Jo - 1)) := by
    intro h2
    set J' := Jo - 1 with hJ'
    have hJo' : Jo = J' + 1 := by omega
    have hW := hmax J' (by omega)
    unfold entryWelfare at hW
    set Q := (Jo : ℝ) * q Jo with hQ
    set Q' := (J' : ℝ) * q J' with hQ'
    have hQQ : Q' ≤ Q := hA1 Jo J' (by omega)
    have hQ'0 : 0 ≤ Q' := mul_nonneg (Nat.cast_nonneg _) (hq0 _)
    have hint : (∫ s in (0 : ℝ)..Q, p s) - ∫ s in (0 : ℝ)..Q', p s = ∫ s in Q'..Q, p s :=
      intervalIntegral.integral_interval_sub_left (hpc.intervalIntegrable _ _)
        (hpc.intervalIntegrable _ _)
    have hbound : (∫ s in Q'..Q, p s) ≤ p Q' * (Q - Q') := by
      have := intervalIntegral.integral_mono_on hQQ (hpc.intervalIntegrable _ _)
        (intervalIntegrable_const (μ := MeasureTheory.volume) (c := p Q')) (fun s hs => hp hs.1)
      simpa [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using this
    have htan := foc_le_tangent_convex hc hc' (hq0 J') (hq0 Jo)
    have hA3' := hA3 J'
    have hA2' : q Jo ≤ q J' := hA2 Jo J' (by omega)
    have hJ'cast : (Jo : ℝ) = J' + 1 := by rw [hJo']; push_cast; ring
    -- (12.E.8) and the convexity step
    have e : q J' + Q' - Q = Jo * (q J' - q Jo) := by
      rw [hQ, hQ', hJ'cast]; ring
    have hJo0 : (0 : ℝ) ≤ Jo := Nat.cast_nonneg _
    have hfinal : 0 ≤ (p Q' - c' (q J')) * (Jo * (q J' - q Jo)) :=
      mul_nonneg (by linarith) (mul_nonneg hJo0 (by linarith))
    have step1 : K ≤ (∫ s in Q'..Q, p s) - Jo * c (q Jo) + J' * c (q J') := by
      rw [← hint]; rw [hJ'cast] at hW ⊢; linarith
    rw [hJ'cast] at hfinal step1 e
    have e2 : p Q' * (q J' + Q' - Q) = p Q' * ((J' + 1) * (q J' - q Jo)) := by rw [e]
    have h4 := mul_le_mul_of_nonneg_left htan (show (0 : ℝ) ≤ J' + 1 by positivity)
    linarith
  refine ⟨key, fun J hJ => ?_⟩
  by_contra hlt
  push Not at hlt
  have h2 : 2 ≤ Jo := by omega
  have := hanti (show J + 1 ≤ Jo - 1 by omega)
  simp only at this
  linarith [key h2, hJ.2.2]

end MWG.MarketPower
