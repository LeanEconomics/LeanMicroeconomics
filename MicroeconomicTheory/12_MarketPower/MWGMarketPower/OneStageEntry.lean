/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGMarketPower.Entry
import MWGMarketPower.RepeatedBertrandExercises

/-!
# One-stage entry and contestable markets

MWG, Section 12.E, pp. 409-411: footnote 24, the one-stage entry game, Example 12.E.4 and
footnotes 26-27.

* `footnote_12_24`: with strict (A1) and `p` strictly decreasing, Proposition 12.E.1 holds with
  `π_{J°−1} > K`, so `J* ≥ J° − 1` even if firms do not enter when indifferent.
* **The one-stage entry game with price competition** (p. 410). Potential firms `ι` (at least
  two) name prices simultaneously; a firm incurs the setup cost `K` only if it sells. As in
  footnote 26, the whole demand goes to one of the firms naming the lowest price, selected by a
  rule `w` (`IsLowestPriceRule`); firm `j` earns `(p_j − c)x(p_j) − K` if it is the selected firm
  and `x(p_j) > 0`, and `0` otherwise (`oneStageProfit`). `IsOneStageEq` is pure-strategy Nash
  equilibrium.
* `oneStagePrice` is `p* = min{p : (p − c)x(p) ≥ K}`; `example_12_E_4_set`: for `x(p) > 0` this
  is MWG's set `{p : p ≥ [K + cx(p)]/x(p)}`. `oneStagePrice_spec`: `c < p* < pᵐ`, `R(p*) = K`,
  `R < K` below `p*`, `R > K` on `(p*, pᵐ]`.
* `example_12_E_4`: under MWG's hypothesis `(p − c)x(p) > K` for some `p` and **single
  peakedness** (`R` strictly increasing on `[c, pᵐ]`; added, see below), for every rule `w` every
  equilibrium has the selected firm charging `p*` with positive sales, and every firm earns zero;
  `example_12_E_4_exists`: all firms charging `p*` is an equilibrium for every rule;
  `example_12_E_4_welfare`: welfare at `p*` strictly exceeds welfare at the monopoly price of
  Example 12.E.2.
* `example_12_E_4_counterexample` (correction): without single peakedness the claim fails: a
  Bertrand demand with a flat stretch of `R = K` has an equilibrium at a price above `p*`.
* `footnote_12_26`: with MWG's earlier equal-sharing rule (`bertrandSales`) the one-stage game
  has no pure-strategy equilibrium, so giving the demand to one firm is needed.
* `footnote_12_27`: the outcome solves the problem of a planner who controls outputs subject to
  nonnegative profit for every active firm: one firm producing the largest `Q` with
  `(P(Q) − c)Q ≥ K`.
-/

namespace MWG.MarketPower

open Set Function Filter Topology MWG.CompetitiveMarkets

/-! ### Footnote 24 -/

/-- **Footnote 24** (MWG, p. 409). Under the hypotheses of Proposition 12.E.1 with (A1) strict
(`J' < J → J'q_{J'} < Jq_J`) and `p` strictly decreasing (MWG's `p' < 0`), the inequality
(12.E.8) is strict and `π_{J°−1} > K`; hence `J* ≥ J° − 1` also when firms do not enter when
indifferent (equilibrium conditions `π_J ≥ K ≥ π_{J+1}`, footnote 22). -/
theorem footnote_12_24 {p c c' : ℝ → ℝ} {q : ℕ → ℝ} {K : ℝ} (hp : StrictAnti p)
    (hpc : Continuous p)
    (hc : ∀ x ∈ Ici (0 : ℝ), HasDerivWithinAt c (c' x) (Ici 0) x) (hc' : MonotoneOn c' (Ici 0))
    (hq0 : ∀ J, 0 ≤ q J)
    (hA1 : ∀ J J' : ℕ, J' < J → J' * q J' < J * q J) (hA2 : ∀ J J' : ℕ, J' ≤ J → q J ≤ q J')
    (hA3 : ∀ J : ℕ, c' (q J) ≤ p (J * q J)) {Jo : ℕ} (hJo : 1 ≤ Jo)
    (hmax : ∀ J, 1 ≤ J → entryWelfare p c q K J ≤ entryWelfare p c q K Jo) :
    (2 ≤ Jo → K < p ((Jo - 1 : ℕ) * q (Jo - 1)) * q (Jo - 1) - c (q (Jo - 1))) ∧
    ∀ J, 1 ≤ J → K ≤ p (J * q J) * q J - c (q J) →
      p ((J + 1 : ℕ) * q (J + 1)) * q (J + 1) - c (q (J + 1)) ≤ K → Jo - 1 ≤ J := by
  have hA1w : ∀ J J' : ℕ, J' ≤ J → J' * q J' ≤ J * q J := by
    intro J J' h
    rcases eq_or_lt_of_le h with h' | h'
    · rw [h']
    · exact (hA1 J J' h').le
  have hanti := exercise_12_E_2 hp.antitone hc hc' hq0 hA1w hA2 hA3
  have key : 2 ≤ Jo → K < p ((Jo - 1 : ℕ) * q (Jo - 1)) * q (Jo - 1) - c (q (Jo - 1)) := by
    intro h2
    set J' := Jo - 1 with hJ'
    have hJo' : Jo = J' + 1 := by omega
    have hW := hmax J' (by omega)
    unfold entryWelfare at hW
    set Q := (Jo : ℝ) * q Jo with hQ
    set Q' := (J' : ℝ) * q J' with hQ'
    have hQQ : Q' < Q := hA1 Jo J' (by omega)
    have hint : (∫ s in (0 : ℝ)..Q, p s) - ∫ s in (0 : ℝ)..Q', p s = ∫ s in Q'..Q, p s :=
      intervalIntegral.integral_interval_sub_left (hpc.intervalIntegrable _ _)
        (hpc.intervalIntegrable _ _)
    have hbound : (∫ s in Q'..Q, p s) < p Q' * (Q - Q') := by
      have := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt hQQ
        hpc.continuousOn (continuousOn_const (c := p Q'))
        (fun s hs => (hp hs.1).le) ⟨Q, ⟨hQQ.le, le_rfl⟩, hp hQQ⟩
      simpa [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using this
    have htan := foc_le_tangent_convex hc hc' (hq0 J') (hq0 Jo)
    have hA3' := hA3 J'
    have hA2' : q Jo ≤ q J' := hA2 Jo J' (by omega)
    have hJ'cast : (Jo : ℝ) = J' + 1 := by rw [hJo']; push_cast; ring
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
  refine ⟨key, fun J _ _ hJ2 => ?_⟩
  by_contra hlt
  push Not at hlt
  have h2 : 2 ≤ Jo := by omega
  have := hanti (show J + 1 ≤ Jo - 1 by omega)
  simp only at this
  linarith [key h2]

/-- **Footnote 24, instance.** The linear Cournot model of Example 12.E.1 (`a = 3`, `b = 1`,
`c = 0`, so `p(Q) = 3 − Q`, `q_J = 3/(J + 1)`) satisfies strict (A1), (A2), (A3) with `p`
strictly decreasing. -/
theorem footnote_12_24_instance :
    StrictAnti (fun s : ℝ => 3 - s) ∧
    (∀ J J' : ℕ, J' < J → (J' : ℝ) * (3 / (J' + 1)) < J * (3 / (J + 1))) ∧
    (∀ J J' : ℕ, J' ≤ J → (3 : ℝ) / (J + 1) ≤ 3 / (J' + 1)) ∧
    (∀ J : ℕ, (0 : ℝ) ≤ 3 - J * (3 / (J + 1))) := by
  refine ⟨fun a b h => by linarith, fun J J' h => ?_, fun J J' h => ?_, fun J => ?_⟩
  · have : (J' : ℝ) < J := by exact_mod_cast h
    rw [mul_div_assoc', mul_div_assoc', div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  · have : (J' : ℝ) ≤ J := by exact_mod_cast h
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
  · have : (J : ℝ) * (3 / (J + 1)) ≤ 3 := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
    linarith

/-! ### The one-stage entry game with price competition -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A rule selecting, at every price profile, one of the firms naming the lowest price
(footnote 26: the whole demand may go to one firm when several name the same price). -/
def IsLowestPriceRule (w : (ι → ℝ) → ι) : Prop := ∀ (p : ι → ℝ) (k : ι), p (w p) ≤ p k

/-- Firm `j`'s profit in the one-stage entry game (MWG, p. 410): the selected lowest-price firm
sells `x(p_j)` and, if this is positive, pays `K + cx(p_j)`; every other firm sells nothing and
pays nothing. -/
noncomputable def oneStageProfit (x : ℝ → ℝ) (c K : ℝ) (w : (ι → ℝ) → ι) (p : ι → ℝ)
    (j : ι) : ℝ :=
  if j = w p ∧ 0 < x (p j) then (p j - c) * x (p j) - K else 0

/-- Pure-strategy Nash equilibrium of the one-stage entry game. -/
def IsOneStageEq (x : ℝ → ℝ) (c K : ℝ) (w : (ι → ℝ) → ι) (p : ι → ℝ) : Prop :=
  ∀ j a, oneStageProfit x c K w (update p j a) j ≤ oneStageProfit x c K w p j

/-- The price `p* = min{p : (p − c)x(p) ≥ K}` of Example 12.E.4. -/
noncomputable def oneStagePrice (x : ℝ → ℝ) (c K : ℝ) : ℝ := sInf {p | K ≤ (p - c) * x p}

omit [Fintype ι] [DecidableEq ι] in
/-- A lowest-price rule exists (choose a minimizer). -/
theorem exists_lowestPriceRule [Finite ι] [Nonempty ι] :
    ∃ w : (ι → ℝ) → ι, IsLowestPriceRule w :=
  ⟨fun p => Classical.choose (Finite.exists_min p),
    fun p => Classical.choose_spec (Finite.exists_min p)⟩

/-- **Example 12.E.4: the set defining `p*`** (MWG, p. 410). For `x(p) > 0`,
`p ≥ [K + cx(p)]/x(p)` iff `(p − c)x(p) ≥ K`. -/
theorem example_12_E_4_set {x : ℝ → ℝ} {c K p : ℝ} (hxp : 0 < x p) :
    (K + c * x p) / x p ≤ p ↔ K ≤ (p - c) * x p := by
  rw [div_le_iff₀ hxp]; constructor <;> intro h <;> nlinarith

/-- **The price `p*`** (MWG, p. 410). Let demand be Bertrand, `c ≥ 0`, `K > 0`, and let
`(p − c)x(p) > K` at some `pᵐ > c` (MWG's hypothesis), with `R(p) = (p − c)x(p)` strictly
increasing on `[c, pᵐ]`. Then `p* = min{p : R(p) ≥ K}` exists, `c < p* < pᵐ`, `R(p*) = K`,
`R(a) < K` for `a < p*`, and `R(a) > K` for `p* < a ≤ pᵐ`. -/
theorem oneStagePrice_spec {x : ℝ → ℝ} {pbar c K pm : ℝ} (hx : IsBertrandDemand x pbar)
    (hc : 0 ≤ c) (hK : 0 < K) (hpm : K < (pm - c) * x pm)
    (hsm : StrictMonoOn (fun p => (p - c) * x p) (Icc c pm)) :
    c < oneStagePrice x c K ∧ oneStagePrice x c K < pm ∧
    (oneStagePrice x c K - c) * x (oneStagePrice x c K) = K ∧
    (∀ a, a < oneStagePrice x c K → (a - c) * x a < K) ∧
    (∀ a, oneStagePrice x c K < a → a ≤ pm → K < (a - c) * x a) := by
  set S := {p : ℝ | K ≤ (p - c) * x p} with hS
  have hf : Continuous fun p : ℝ => (p - c) * x p :=
    (continuous_id.sub continuous_const).mul hx.cont
  have hgt : ∀ p ∈ S, c < p := by
    intro p hp
    by_contra hle; push Not at hle
    have : (p - c) * x p ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) (hx.nonneg p)
    change K ≤ (p - c) * x p at hp
    linarith
  have hne : S.Nonempty := ⟨pm, hpm.le⟩
  have hbdd : BddBelow S := ⟨c, fun p hp => (hgt p hp).le⟩
  have hclosed : IsClosed S := isClosed_le continuous_const hf
  have hmem : oneStagePrice x c K ∈ S := hclosed.csInf_mem hne hbdd
  have hpmc : c < pm := hgt pm hpm.le
  have hle : oneStagePrice x c K ≤ pm := csInf_le hbdd hpm.le
  have hbelow : ∀ a, a < oneStagePrice x c K → (a - c) * x a < K := by
    intro a ha
    by_contra hge; push Not at hge
    exact absurd (csInf_le hbdd hge) (not_le.2 ha)
  have hc1 := hgt _ hmem
  have heq : (oneStagePrice x c K - c) * x (oneStagePrice x c K) = K := by
    refine le_antisymm ?_ hmem
    exact rbx_le_of_below hx.cont hc hc1 fun a _ ha => (hbelow a ha).le
  have hlt : oneStagePrice x c K < pm := by
    rcases eq_or_lt_of_le hle with h | h
    · rw [h] at heq; linarith
    · exact h
  refine ⟨hc1, hlt, heq, hbelow, fun a ha hapm => ?_⟩
  have := hsm ⟨hc1.le, hle⟩ ⟨by linarith, hapm⟩ ha
  simp only at this
  linarith

omit [Fintype ι] in
/-- A firm naming a price strictly below all others is selected. -/
theorem lowestRule_update_lt {w : (ι → ℝ) → ι} (hw : IsLowestPriceRule w) {p : ι → ℝ} {k : ι}
    {a : ℝ} (h : ∀ l, l ≠ k → a < p l) : w (update p k a) = k := by
  by_contra hne
  have h1 := hw (update p k a) k
  rw [update_self, update_of_ne hne] at h1
  linarith [h _ hne]

omit [Fintype ι] in
/-- A firm naming a price above someone else's is not selected. -/
theorem lowestRule_update_gt {w : (ι → ℝ) → ι} (hw : IsLowestPriceRule w) {p : ι → ℝ} {k l : ι}
    (hlk : l ≠ k) {a : ℝ} (h : p l < a) : w (update p k a) ≠ k := by
  intro heq
  have h1 := hw (update p k a) l
  rw [heq, update_self, update_of_ne hlk] at h1
  linarith

omit [Fintype ι] in
/-- The profit of a firm selected with a positive demand. -/
theorem oneStageProfit_of_win {x : ℝ → ℝ} {c K : ℝ} {w : (ι → ℝ) → ι} {p : ι → ℝ} {j : ι}
    (hj : j = w p) (hx : 0 < x (p j)) : oneStageProfit x c K w p j = (p j - c) * x (p j) - K := by
  unfold oneStageProfit
  split_ifs with h
  · rfl
  · exact absurd ⟨hj, hx⟩ h

omit [Fintype ι] in
theorem oneStageProfit_of_lose {x : ℝ → ℝ} {c K : ℝ} {w : (ι → ℝ) → ι} {p : ι → ℝ} {j : ι}
    (hj : j ≠ w p) : oneStageProfit x c K w p j = 0 := by
  simp [oneStageProfit, hj]

omit [Fintype ι] in
/-- A firm earns at most `max(R(p_j) − K, 0)`. -/
theorem oneStageProfit_le {x : ℝ → ℝ} {c K : ℝ} (w : (ι → ℝ) → ι) (p : ι → ℝ) (j : ι)
    {B : ℝ} (hB : 0 ≤ B) (hR : 0 < x (p j) → (p j - c) * x (p j) - K ≤ B) :
    oneStageProfit x c K w p j ≤ B := by
  unfold oneStageProfit
  split_ifs with h
  · exact hR h.2
  · exact hB

/-- **Example 12.E.4** (MWG, pp. 410-411), with single peakedness added. Let demand be Bertrand,
`c ≥ 0`, `K > 0`, `(pᵐ − c)x(pᵐ) > K` with `R` strictly increasing on `[c, pᵐ]`, and at least two
potential firms. For every lowest-price rule, in every equilibrium the selected firm charges
`p* = min{p : R(p) ≥ K}` and sells `x(p*) > 0` (all sales occur at `p*`), and every firm earns
zero. -/
theorem example_12_E_4 {x : ℝ → ℝ} {pbar c K pm : ℝ} (hx : IsBertrandDemand x pbar)
    (hc : 0 ≤ c) (hK : 0 < K) (hpm : K < (pm - c) * x pm)
    (hsm : StrictMonoOn (fun p => (p - c) * x p) (Icc c pm)) (h2 : 2 ≤ Fintype.card ι)
    {w : (ι → ℝ) → ι} (hw : IsLowestPriceRule w) {p : ι → ℝ} (hp : IsOneStageEq x c K w p) :
    p (w p) = oneStagePrice x c K ∧ 0 < x (oneStagePrice x c K) ∧
      ∀ j, oneStageProfit x c K w p j = 0 := by
  obtain ⟨hc1, hlt, heq, hbelow, habove⟩ := oneStagePrice_spec hx hc hK hpm hsm
  set ps := oneStagePrice x c K with hps
  set j0 := w p with hj0
  set m := p j0 with hm
  have hxps : 0 < x ps := by
    rcases (hx.nonneg ps).lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at heq; linarith
  obtain ⟨k, hk⟩ := Fintype.exists_ne_of_one_lt_card (by omega) j0
  -- every firm earns at least `0` (it can name `p̄`, where demand is zero)
  have hnn : ∀ j, 0 ≤ oneStageProfit x c K w p j := by
    intro j
    refine le_trans ?_ (hp j pbar)
    unfold oneStageProfit
    rw [update_self, hx.zero pbar le_rfl]
    simp
  -- a positive-profit undercut by `k`
  have hundercut : ∀ a, a < m → K < (a - c) * x a → False := by
    intro a ham hRa
    have hxa : 0 < x a := by
      rcases (hx.nonneg a).lt_or_eq with h | h
      · exact h
      · rw [← h, mul_zero] at hRa; linarith
    have hlow : ∀ l, l ≠ k → a < p l := fun l _ => lt_of_lt_of_le ham (hw p l)
    have hwin := lowestRule_update_lt hw hlow
    have h1 := hp k a
    rw [oneStageProfit_of_win hwin.symm (by rw [update_self]; exact hxa), update_self,
      oneStageProfit_of_lose hk] at h1
    linarith
  have hmle : m ≤ ps := by
    by_contra hgt; push Not at hgt
    set a := (ps + min m pm) / 2 with ha
    have h1 : ps < min m pm := lt_min hgt hlt
    exact hundercut a (by linarith [min_le_left m pm]) (habove a (by linarith)
      (by linarith [min_le_right m pm]))
  have hmge : ps ≤ m := by
    by_contra hlt'; push Not at hlt'
    have hxm : 0 < x m := lt_trans hxps (hx.strictAnti m ps hlt' hxps)
    have := hnn j0
    rw [oneStageProfit_of_win rfl hxm] at this
    linarith [hbelow m hlt']
  have hmps : m = ps := le_antisymm hmle hmge
  refine ⟨hmps, hxps, fun j => ?_⟩
  by_cases hj : j = j0
  · rw [hj, oneStageProfit_of_win rfl (by change 0 < x m; rw [hmps]; exact hxps)]
    change (m - c) * x m - K = 0
    rw [hmps, heq, sub_self]
  · exact oneStageProfit_of_lose hj

/-- **Example 12.E.4, existence** (MWG, p. 411). Under the hypotheses of `example_12_E_4`, all
firms naming `p*` is an equilibrium for every lowest-price rule. -/
theorem example_12_E_4_exists {x : ℝ → ℝ} {pbar c K pm : ℝ} (hx : IsBertrandDemand x pbar)
    (hc : 0 ≤ c) (hK : 0 < K) (hpm : K < (pm - c) * x pm)
    (hsm : StrictMonoOn (fun p => (p - c) * x p) (Icc c pm)) (h2 : 2 ≤ Fintype.card ι)
    {w : (ι → ℝ) → ι} (hw : IsLowestPriceRule w) :
    IsOneStageEq x c K w (fun _ : ι => oneStagePrice x c K) := by
  obtain ⟨_, _, heq, hbelow, _⟩ := oneStagePrice_spec hx hc hK hpm hsm
  set ps := oneStagePrice x c K with hps
  have hzero : ∀ j, oneStageProfit x c K w (fun _ : ι => ps) j = 0 := by
    intro j
    unfold oneStageProfit
    split_ifs
    · rw [heq, sub_self]
    · rfl
  intro j a
  rw [hzero]
  obtain ⟨l, hl⟩ := Fintype.exists_ne_of_one_lt_card (by omega) j
  unfold oneStageProfit
  split_ifs with hsel
  · rw [update_self] at hsel ⊢
    rcases lt_trichotomy a ps with h | h | h
    · linarith [hbelow a h]
    · rw [h, heq, sub_self]
    · exact absurd hsel.1.symm (lowestRule_update_gt (p := fun _ : ι => ps) hw hl h)
  · exact le_rfl

/-- Aggregate surplus when one firm sells `x(p)` at the price `p` and pays `K`: consumer surplus
`∫_p^{p̄} x` plus profit `(p − c)x(p) − K`. -/
noncomputable def oneStageWelfare (x : ℝ → ℝ) (pbar c K p : ℝ) : ℝ :=
  (∫ s in p..pbar, x s) + (p - c) * x p - K

/-- **Example 12.E.4, welfare** (MWG, p. 411). The one-stage outcome (one firm at `p*`) is
strictly better than the two-stage outcome of Example 12.E.2 (one firm at the monopoly price
`pᵐ`). -/
theorem example_12_E_4_welfare {x : ℝ → ℝ} {pbar c K pm : ℝ} (hx : IsBertrandDemand x pbar)
    (hc : 0 ≤ c) (hK : 0 < K) (hpm : K < (pm - c) * x pm)
    (hsm : StrictMonoOn (fun p => (p - c) * x p) (Icc c pm)) :
    oneStageWelfare x pbar c K pm < oneStageWelfare x pbar c K (oneStagePrice x c K) := by
  obtain ⟨hc1, hlt, _, _, _⟩ := oneStagePrice_spec hx hc hK hpm hsm
  set ps := oneStagePrice x c K
  have hxpm : 0 < x pm := by
    rcases (hx.nonneg pm).lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at hpm; linarith
  have hxps : x pm < x ps := hx.strictAnti ps pm hlt hxpm
  have hadd : (∫ s in ps..pm, x s) + (∫ s in pm..pbar, x s) = ∫ s in ps..pbar, x s :=
    intervalIntegral.integral_add_adjacent_intervals (hx.cont.intervalIntegrable _ _)
      (hx.cont.intervalIntegrable _ _)
  have hint : (pm - ps) * x pm ≤ ∫ s in ps..pm, x s := by
    have := intervalIntegral.integral_mono_on hlt.le
      (intervalIntegrable_const (μ := MeasureTheory.volume) (c := x pm))
      (hx.cont.intervalIntegrable _ _) (fun s hs => by
        rcases eq_or_lt_of_le hs.2 with h | h
        · rw [h]
        · exact (hx.strictAnti s pm h hxpm).le)
    simpa [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using this
  unfold oneStageWelfare
  rw [← hadd]
  nlinarith [mul_pos (sub_pos.2 hc1) (sub_pos.2 hxps)]

/-- **Example 12.E.4, instance** (MWG, p. 410). Demand `max{0, 10 − p}`, `c = 1`, `K = 8`:
`R(11/2) = 81/4 > 8`, `R` is strictly increasing on `[1, 11/2]`, and `p* = 2`. -/
theorem example_12_E_4_instance :
    (8 : ℝ) < (11 / 2 - 1) * bcLinDemand 10 (11 / 2) ∧
    StrictMonoOn (fun p => (p - 1) * bcLinDemand 10 p) (Icc 1 (11 / 2)) ∧
    oneStagePrice (bcLinDemand 10) 1 8 = 2 := by
  obtain ⟨_, s1, _⟩ := rbx_lin_facts (c := 1) (by norm_num)
  norm_num at s1
  refine ⟨by norm_num [bcLinDemand], s1, ?_⟩
  refine IsLeast.csInf_eq ⟨by norm_num [bcLinDemand], fun p hp => ?_⟩
  change (8 : ℝ) ≤ (p - 1) * bcLinDemand 10 p at hp
  by_contra hlt; push Not at hlt
  simp only [bcLinDemand] at hp
  rw [max_eq_right (by linarith)] at hp
  nlinarith

/-! ### Example 12.E.4 without single peakedness: a counterexample -/

/-- A Bertrand demand (with `c = 1`, `K = 1`) whose profit `R(p) = (p − 1)x(p)` equals `K` on the
whole interval `[2, 3]`: `x(p) = 3 − p` for `p ≤ 2`, `1/(p − 1)` on `[2, 3]`, `(7 − p)/8` on
`[3, 7]` and `0` above. `R(4) = 9/8 > K`. -/
noncomputable def osCexDemand (p : ℝ) : ℝ :=
  if p ≤ 2 then 3 - p else if p ≤ 3 then 1 / max (p - 1) 1 else if p ≤ 7 then (7 - p) / 8 else 0

theorem osCexDemand_mid {p : ℝ} (h1 : ¬ p ≤ 2) (h2 : p ≤ 3) : osCexDemand p = 1 / (p - 1) := by
  simp only [osCexDemand, h1, h2, ite_false, ite_true]
  rw [max_eq_left (by linarith)]

theorem osCexDemand_isBertrand : IsBertrandDemand osCexDemand 7 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold osCexDemand
    refine Continuous.if_le (by fun_prop) ?_ continuous_id continuous_const ?_
    · refine Continuous.if_le ?_ ?_ continuous_id continuous_const ?_
      · exact continuous_const.div ((continuous_id.sub continuous_const).max continuous_const)
          fun p => (lt_of_lt_of_le one_pos (le_max_right _ _)).ne'
      · refine Continuous.if_le (by fun_prop) (by fun_prop) continuous_id continuous_const ?_
        intro p hp; rw [hp]; norm_num
      · intro p hp; rw [hp]; norm_num
    · intro p hp; rw [hp]; norm_num
  · intro p; unfold osCexDemand
    split_ifs
    · linarith
    · positivity
    · exact div_nonneg (by linarith) (by norm_num)
    · exact le_rfl
  · intro p p' hpp' hpos
    by_cases h1 : p' ≤ 2
    · have : p ≤ 2 := by linarith
      simp only [osCexDemand, h1, this, ite_true]; linarith
    by_cases h2 : p' ≤ 3
    · rw [osCexDemand_mid h1 h2]
      by_cases h3 : p ≤ 2
      · simp only [osCexDemand, h3, ite_true]
        rw [div_lt_iff₀ (by linarith)]; nlinarith
      · rw [osCexDemand_mid h3 (by linarith)]
        exact one_div_lt_one_div_of_lt (by linarith) (by linarith)
    by_cases h4 : p' ≤ 7
    · have hx' : osCexDemand p' = (7 - p') / 8 := by simp [osCexDemand, h1, h2, h4]
      rw [hx']
      by_cases h3 : p ≤ 2
      · simp only [osCexDemand, h3, ite_true]; linarith
      by_cases h5 : p ≤ 3
      · rw [osCexDemand_mid h3 h5, lt_div_iff₀ (by linarith)]; nlinarith
      · have hx : osCexDemand p = (7 - p) / 8 := by
          simp [osCexDemand, h3, h5, show p ≤ 7 by linarith]
        rw [hx]; linarith
    · have : osCexDemand p' = 0 := by simp [osCexDemand, h1, h2, h4]
      rw [this] at hpos; exact absurd hpos (lt_irrefl 0)
  · intro p hp; unfold osCexDemand
    split_ifs <;> linarith

/-- **Example 12.E.4 is false without single peakedness** (MWG, p. 410; correction). With the
demand `osCexDemand`, `c = 1`, `K = 1`: MWG's hypothesis holds (`(4 − 1)x(4) = 9/8 > K`) and
`p* = 2`, yet for every lowest-price rule all firms naming `3` is an equilibrium, so sales take
place at `3 ≠ p*`. -/
theorem example_12_E_4_counterexample (h2 : 2 ≤ Fintype.card ι) {w : (ι → ℝ) → ι}
    (hw : IsLowestPriceRule w) :
    IsBertrandDemand osCexDemand 7 ∧ (1 : ℝ) < (4 - 1) * osCexDemand 4 ∧
    oneStagePrice osCexDemand 1 1 = 2 ∧
    IsOneStageEq osCexDemand 1 1 w (fun _ : ι => 3) ∧
      (fun _ : ι => (3 : ℝ)) (w fun _ => 3) ≠ 2 := by
  have hR : ∀ p : ℝ, p ≤ 3 → (p - 1) * osCexDemand p ≤ 1 := by
    intro p hp
    by_cases h1 : p ≤ 2
    · simp only [osCexDemand, h1, ite_true]; nlinarith [sq_nonneg (p - 2)]
    · rw [osCexDemand_mid h1 hp]
      rw [mul_one_div, div_self (by linarith)]
  have h3 : (3 - 1) * osCexDemand 3 = 1 := by
    rw [osCexDemand_mid (by norm_num) le_rfl]; norm_num
  refine ⟨osCexDemand_isBertrand, by norm_num [osCexDemand], ?_, ?_, by norm_num⟩
  · refine IsLeast.csInf_eq ⟨by norm_num [osCexDemand], fun p hp => ?_⟩
    change (1 : ℝ) ≤ (p - 1) * osCexDemand p at hp
    by_contra hlt; push Not at hlt
    simp only [osCexDemand, hlt.le, ite_true] at hp
    nlinarith [sq_nonneg (p - 2)]
  · have hzero : ∀ j, oneStageProfit osCexDemand 1 1 w (fun _ : ι => 3) j = 0 := by
      intro j
      unfold oneStageProfit
      split_ifs
      · rw [h3, sub_self]
      · rfl
    intro j a
    rw [hzero]
    obtain ⟨l, hl⟩ := Fintype.exists_ne_of_one_lt_card (by omega) j
    unfold oneStageProfit
    split_ifs with hsel
    · rw [update_self] at hsel ⊢
      rcases le_or_gt a 3 with h | h
      · linarith [hR a h]
      · exact absurd hsel.1.symm (lowestRule_update_gt (p := fun _ : ι => (3 : ℝ)) hw hl h)
    · exact le_rfl

/-! ### Footnote 26: no equilibrium under equal sharing -/

/-- Firm `j`'s profit in the one-stage game when the lowest-price firms share demand equally
(`bertrandSales`, the rule of Section 12.C): `(p_j − c)x_j − K` if it sells, `0` otherwise. -/
noncomputable def shareProfit (x : ℝ → ℝ) (c K : ℝ) (p : ι → ℝ) (j : ι) : ℝ :=
  if 0 < bertrandSales x p j then (p j - c) * bertrandSales x p j - K else 0

/-- Pure-strategy Nash equilibrium of the one-stage game with equal sharing. -/
def IsShareEq (x : ℝ → ℝ) (c K : ℝ) (p : ι → ℝ) : Prop :=
  ∀ j a, shareProfit x c K (update p j a) j ≤ shareProfit x c K p j

omit [Fintype ι] in
theorem shareProfit_of_lowest {x : ℝ → ℝ} {c K a : ℝ} {p : ι → ℝ} {k : ι} [Fintype ι]
    (h : ∀ l, l ≠ k → a < p l) (hxa : 0 < x a) :
    shareProfit x c K (update p k a) k = (a - c) * x a - K := by
  have hs : bertrandSales x (update p k a) k = x a := by
    rw [bertrandSales_of_lt (fun l hl => by simp [update_of_ne hl, h l hl])]
    simp
  unfold shareProfit
  rw [hs, update_self]
  simp [hxa]

omit [Fintype ι] [DecidableEq ι] in
theorem shareProfit_of_gt {x : ℝ → ℝ} {c K : ℝ} {p : ι → ℝ} {j l : ι} [Fintype ι]
    (h : p l < p j) : shareProfit x c K p j = 0 := by
  unfold shareProfit
  rw [bertrandSales_of_gt h]
  simp

/-- **Footnote 26** (MWG, p. 411). Under the hypotheses of `example_12_E_4`, if the firms naming
the lowest price share demand equally (the division used before), the one-stage entry game has
no pure-strategy equilibrium: giving the whole demand to one firm is needed for the equilibrium
of Example 12.E.4. -/
theorem footnote_12_26 {x : ℝ → ℝ} {pbar c K pm : ℝ} (hx : IsBertrandDemand x pbar)
    (hc : 0 ≤ c) (hK : 0 < K) (hpm : K < (pm - c) * x pm)
    (hsm : StrictMonoOn (fun p => (p - c) * x p) (Icc c pm)) (h2 : 2 ≤ Fintype.card ι)
    (p : ι → ℝ) : ¬ IsShareEq x c K p := by
  intro hp
  obtain ⟨hc1, hlt, heq, hbelow, habove⟩ := oneStagePrice_spec hx hc hK hpm hsm
  set ps := oneStagePrice x c K with hps
  have hpos : ∀ a, c < a → K < (a - c) * x a → 0 < x a := by
    intro a _ hRa
    rcases (hx.nonneg a).lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at hRa; linarith
  have : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨j0, hj0⟩ := Finite.exists_min p
  set m := p j0 with hm
  -- every firm earns at least `0`
  have hnn : ∀ j, 0 ≤ shareProfit x c K p j := by
    intro j
    refine le_trans (le_of_eq ?_) (hp j pbar)
    unfold shareProfit
    have h1 := bertrandSales_le hx.nonneg (update p j pbar) j
    rw [update_self, hx.zero pbar le_rfl] at h1
    split_ifs with hh
    · linarith
    · rfl
  -- a profitable undercut of all prices is impossible for a firm earning `0`
  have hund : ∀ k a, (∀ l, l ≠ k → a < p l) → c < a → K < (a - c) * x a →
      shareProfit x c K p k = 0 → False := by
    intro k a hlow hac hRa h0
    have := hp k a
    rw [shareProfit_of_lowest hlow (hpos a hac hRa), h0] at this
    linarith
  obtain ⟨k, hk⟩ := Fintype.exists_ne_of_one_lt_card (by omega) j0
  rcases (hx.nonneg m).lt_or_eq with hxm | hxm
  · -- positive demand at the lowest price
    have hsales : 0 < bertrandSales x p j0 := by
      unfold bertrandSales
      split_ifs with hh
      · exact div_pos hxm (by exact_mod_cast Finset.card_pos.2 ⟨j0, by simp⟩)
      · exact absurd hj0 hh
    have hprof : shareProfit x c K p j0 = (m - c) * bertrandSales x p j0 - K := by
      unfold shareProfit
      split_ifs
      rfl
    have hmc : c < m := by
      have := hnn j0
      rw [hprof] at this
      by_contra hle; push Not at hle
      nlinarith
    by_cases htie : ∃ l, l ≠ j0 ∧ p l = m
    · obtain ⟨l, hl, hlm⟩ := htie
      have hxc : 0 < x c := lt_trans hxm (hx.strictAnti c m hmc hxm)
      obtain ⟨a, hac, ham, hgain⟩ := bertrand_deviation hx hxc hmc
      have hhalf : bertrandSales x p j0 ≤ x m / 2 := by
        unfold bertrandSales
        have hcard : 2 ≤ (Finset.univ.filter fun k => p k = p j0).card :=
          Finset.one_lt_card.2 ⟨j0, by simp, l, by simp [hlm, hm], hl.symm⟩
        split_ifs with hh
        · exact div_le_div_of_nonneg_left (hx.nonneg _) (by norm_num) (by exact_mod_cast hcard)
        · exact absurd hj0 hh
      have hRa : 0 < (a - c) * x a := lt_of_le_of_lt
        (div_nonneg (mul_nonneg (by linarith) (hx.nonneg m)) (by norm_num)) hgain
      have hxa : 0 < x a := by
        rcases (hx.nonneg a).lt_or_eq with h | h
        · exact h
        · rw [← h, mul_zero] at hRa; linarith
      have := hp j0 a
      rw [shareProfit_of_lowest (fun l' _ => lt_of_lt_of_le ham (hj0 l')) hxa, hprof] at this
      have := mul_le_mul_of_nonneg_left hhalf (show 0 ≤ m - c by linarith)
      nlinarith
    · push Not at htie
      have hlow : ∀ l, l ≠ j0 → m < p l := fun l hl =>
        lt_of_le_of_ne (hj0 l) (fun h => htie l hl h.symm)
      have hprof' : shareProfit x c K p j0 = (m - c) * x m - K := by
        rw [hprof, bertrandSales_of_lt hlow]
      have hmps : ps ≤ m := by
        by_contra h; push Not at h
        have := hnn j0; rw [hprof'] at this; linarith [hbelow m h]
      rcases eq_or_lt_of_le hmps with he | hgt
      · -- `m = p*`: the selected firm raises its price towards the second-lowest price
        obtain ⟨k₂, hk₂, hmin⟩ := Finset.exists_min_image (Finset.univ.erase j0) p
          ⟨k, by simp [hk]⟩
        have hm₂ : m < p k₂ := hlow k₂ (Finset.ne_of_mem_erase hk₂)
        set a := (ps + min (p k₂) pm) / 2 with ha
        have hmin' : ps < min (p k₂) pm := lt_min (by rw [he]; exact hm₂) hlt
        have hRa := habove a (by linarith) (by linarith [min_le_right (p k₂) pm])
        have hlow' : ∀ l, l ≠ j0 → a < p l := fun l hl =>
          lt_of_lt_of_le (by linarith [min_le_left (p k₂) pm])
            (hmin l (Finset.mem_erase.2 ⟨hl, Finset.mem_univ l⟩))
        have := hp j0 a
        rw [shareProfit_of_lowest hlow' (hpos a (by linarith) hRa), hprof', ← he, heq] at this
        linarith
      · -- `m > p*`: another firm undercuts profitably
        set a := (ps + min m pm) / 2 with ha
        have hmin' : ps < min m pm := lt_min hgt hlt
        have hRa := habove a (by linarith) (by linarith [min_le_right m pm])
        refine hund k a (fun l hl => lt_of_lt_of_le (by linarith [min_le_left m pm]) (hj0 l))
          (by linarith) hRa (shareProfit_of_gt (l := j0) (hlow k hk))
  · -- zero demand at the lowest price: nobody sells, and an undercut to `(p* + pᵐ)/2` pays
    set a := (ps + pm) / 2 with ha
    have hRa := habove a (by linarith) (by linarith)
    have hxa := hpos a (by linarith) hRa
    have ham : a < m := by
      by_contra hle; push Not at hle
      rcases eq_or_lt_of_le hle with h | h
      · rw [← h, ← hxm] at hxa; exact lt_irrefl 0 hxa
      · have := hx.strictAnti m a h hxa; rw [← hxm] at this; linarith [hx.nonneg a]
    have h0 : shareProfit x c K p j0 = 0 := by
      unfold shareProfit
      have h1 := bertrandSales_le hx.nonneg p j0
      rw [← hm, ← hxm] at h1
      split_ifs with hh
      · linarith
      · rfl
    exact hund j0 a (fun l _ => lt_of_lt_of_le ham (hj0 l)) (by linarith) hRa h0

/-! ### Footnote 27: the planner's problem -/

/-- **Footnote 27** (MWG, p. 411). A planner chooses outputs `y_j ≥ 0` for `n` firms, subject to
nonnegative profit `P(Q)y_j ≥ cy_j + K` for every active firm (`y_j > 0`), `Q = ∑ y_j`, to
maximize aggregate surplus `∫₀^Q P − cQ − K·#{active firms}`. If `Q*` is the largest `Q ≥ 0`
with `(P(Q) − c)Q ≥ K` (`P` nonincreasing and continuous, `K > 0`), no feasible plan beats one
firm producing `Q*`, which is feasible. In Example 12.E.4, `Q* = x(p*)`: the one-stage
equilibrium outcome (`footnote_12_27_instance`). -/
theorem footnote_12_27 {P : ℝ → ℝ} {c K Qs : ℝ} (hP : Antitone P) (hPc : Continuous P)
    (hK : 0 < K) (hQs : IsGreatest {Q | 0 ≤ Q ∧ K ≤ (P Q - c) * Q} Qs) {n : ℕ}
    (y : Fin n → ℝ) (hy0 : ∀ j, 0 ≤ y j)
    (hfeas : ∀ j, 0 < y j → c * y j + K ≤ P (∑ k, y k) * y j) :
    (∫ s in (0 : ℝ)..∑ k, y k, P s) - c * ∑ k, y k - K * ∑ k, (if 0 < y k then (1 : ℝ) else 0)
      ≤ (∫ s in (0 : ℝ)..Qs, P s) - c * Qs - K ∧ c * Qs + K ≤ P Qs * Qs := by
  obtain ⟨⟨hQs0, hQsK⟩, hQsmax⟩ := hQs
  refine ⟨?_, by linarith⟩
  set Q := ∑ k, y k with hQ
  set N := ∑ k, (if 0 < y k then (1 : ℝ) else 0) with hN
  have hPQs : c < P Qs := by
    by_contra hle; push Not at hle
    nlinarith
  -- `∫_a^{Qs} P ≥ P(Qs)(Qs − a)` for `0 ≤ a ≤ Qs`
  have hint : ∀ a, a ≤ Qs → (∫ s in (0 : ℝ)..a, P s) + P Qs * (Qs - a) ≤
      ∫ s in (0 : ℝ)..Qs, P s := by
    intro a ha
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (hPc.intervalIntegrable (μ := MeasureTheory.volume) 0 a) (hPc.intervalIntegrable a Qs)
    have hm := intervalIntegral.integral_mono_on ha
      (intervalIntegrable_const (μ := MeasureTheory.volume) (c := P Qs))
      (hPc.intervalIntegrable _ _) (fun s hs => hP hs.2)
    simp only [intervalIntegral.integral_const, smul_eq_mul] at hm
    linarith
  have hN0 : 0 ≤ N := Finset.sum_nonneg fun k _ => by split_ifs <;> norm_num
  have hsum : c * Q + K * N ≤ P Q * Q := by
    rw [hQ, hN, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    split_ifs with h
    · simpa using hfeas j h
    · have : y j = 0 := le_antisymm (not_lt.1 h) (hy0 j)
      simp [this]
  by_cases hact : ∃ j, 0 < y j
  · obtain ⟨j, hj⟩ := hact
    have hN1 : 1 ≤ N := by
      rw [hN]
      have := Finset.single_le_sum (f := fun k => if 0 < y k then (1 : ℝ) else 0)
        (fun k _ => by split_ifs <;> norm_num) (Finset.mem_univ j)
      simpa [hj] using this
    have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun k _ => hy0 k
    have hQle : Q ≤ Qs := hQsmax ⟨hQ0, by nlinarith⟩
    have := hint Q hQle
    nlinarith
  · push Not at hact
    have hy : ∀ k, y k = 0 := fun k => le_antisymm (hact k) (hy0 k)
    have hQ0 : Q = 0 := by simp [hQ, hy]
    have hNz : N = 0 := by simp [hN, hy]
    rw [hQ0, hNz]
    have := hint 0 hQs0
    simp only [intervalIntegral.integral_same] at this ⊢
    nlinarith

/-- **Footnote 27, instance.** With `P(Q) = 10 − Q`, `c = 1`, `K = 8`, the largest `Q` with
`(P(Q) − c)Q ≥ K` is `8 = x(p*)`, the output of the one-stage equilibrium (`p* = 2`). -/
theorem footnote_12_27_instance :
    IsGreatest {Q : ℝ | 0 ≤ Q ∧ 8 ≤ (10 - Q - 1) * Q} 8 ∧
      bcLinDemand 10 (oneStagePrice (bcLinDemand 10) 1 8) = 8 := by
  refine ⟨⟨⟨by norm_num, by norm_num⟩, fun Q hQ => ?_⟩, ?_⟩
  · by_contra h; push Not at h; nlinarith [hQ.2]
  · rw [example_12_E_4_instance.2.2]; norm_num [bcLinDemand]

end MWG.MarketPower
