/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGMarketPower.Entry
import MWGMarketPower.Precommitment

/-!
# Strategic entry deterrence and accommodation

MWG, Appendix B of Chapter 12, pp. 423-427 (Figures 12.BB.1-12.BB.8), Exercise 12.BB.1, and the
stage-1.5 entry remark of Section 12.G (p. 417).

Dixit's three-stage game: in stage 1 the incumbent I builds capacity `k_I` at `r` per unit; in
stage 2 the potential entrant E decides whether to enter at cost `F`; in stage 3 the active
firms choose quantities, I at marginal cost `w` up to its capacity and E at `w + r`.

**General results** (inverse demand `p` concave and strictly decreasing on `[0, ∞)`, as in the
book):
* `appendixB_profit_strictConcave`: concavity of `p` makes each firm's profit strictly concave in
  its own quantity (the book's "sufficient condition"); `appendixB_br_antitone`: it also makes
  best responses (weakly) downward sloping.
* `figure_12_BB_1`: E's best-response profit strictly falls as I's output rises.
* `figure_12_BB_2`: firm I's stage-3 best response is `b_I(q_E | k_I) = min{b(q_E | w), k_I}`.
* `exercise_12_BB_1`: if the Stackelberg point `S` lies to the right of `Z`, deterring entry
  (capacity `k_Z`, no entry) beats every accommodation outcome.

**The linear model.** Every other claim of the appendix is a statement about the curves of the
figures; we prove them in the linear specification `p(Q) = a − Q` with `r > 0` and
`a − w − 2r > 0` (so that point `B` is interior). Write `u = a − w − r`.
* `figure_12_BB_3`: the stage-3 game after entry has the unique Nash equilibrium
  `q_I = min{k_I, k_B}`, `q_E = (u − q_I)/2` with `k_B = (a − w + r)/3`; point `A` (no
  first-mover advantage) is `(u/3, u/3)`, and `k_B > u/3` (I can move right of `A`);
  `figure_12_BB_3_range`: I can induce exactly the points of E's best response up to `B`.
* `figure_12_BB_4`: with `k_I > k_B` firm I uses only `k_B`; producing `k_I` is not credible.
* `appendixB_stage3_noEntry`: without entry I produces `b_I(0 | k_I) = min{k_I, (a − w)/2}`.
* `appendixB_stage2`: with `k_Z = u − 2√F`, E's post-entry profit is at least `F` iff the
  post-entry equilibrium lies at or to the left of `Z` (`q_I ≤ k_Z`).
* `figure_12_BB_5` (blockaded entry), `figure_12_BB_6` (entry inevitable: the Stackelberg point
  `S = u/2`, or `k_B` if `S` lies right of `B`; first-mover advantage
  `figure_12_BB_6_firstMover`), `figure_12_BB_7_deter` / `figure_12_BB_7_accommodate`
  (deterrence possible but not inevitable) and `figure_12_BB_8` (the comparison of `k_π`, the
  monopoly output earning the Stackelberg profit, with `k_Z`): each with existence and
  uniqueness of the SPNE capacity, and proved parameter instances.
* `appendixB_deterrence_raises_output`: deterrence raises output and welfare relative to a
  situation where no entry is possible.

**Departures** (docs/corrections.md): the book's tie rule (E enters when its net profit is
nonnegative) is incompatible with "a capacity at least `k_Z` deters entry": under that rule
`k_Z` does not deter, and when deterrence is optimal no SPNE exists
(`appendixB_bookRule_no_spne`); in every SPNE E stays out at `k_Z`
(`figure_12_BB_7_deter`). In the linear model the Stackelberg point never lies strictly to the
right of `Z` when entry is not blockaded (`appendixB_linear_S_le_Z`), so Exercise 12.BB.1 is
proved in the general model.
-/

namespace MWG.MarketPower

/-! ## General results -/

/-- Increments of a concave function fall: for `p` concave on `[0, ∞)`, `0 ≤ x ≤ y` and `h ≥ 0`,
`p(y + h) − p(y) ≤ p(x + h) − p(x)`. -/
theorem appendixB_concave_increment {p : ℝ → ℝ} (hp : ConcaveOn ℝ (Set.Ici 0) p) {x y h : ℝ}
    (hx : 0 ≤ x) (hxy : x ≤ y) (hh : 0 ≤ h) : p (y + h) - p y ≤ p (x + h) - p x := by
  rcases eq_or_lt_of_le hh with rfl | hh'
  · simp
  have hd : 0 < y + h - x := by linarith
  set l := h / (y + h - x) with hl
  have hl0 : 0 ≤ l := div_nonneg hh hd.le
  have hl1 : 0 ≤ 1 - l := by
    rw [hl, sub_nonneg, div_le_one hd]; linarith
  have hX : x ∈ Set.Ici (0 : ℝ) := hx
  have hY : y + h ∈ Set.Ici (0 : ℝ) := by simp only [Set.mem_Ici]; linarith
  have h1 := hp.2 hX hY hl1 hl0 (by ring)
  have h2 := hp.2 hX hY hl0 hl1 (by ring)
  have e1 : (1 - l) • x + l • (y + h) = x + h := by
    simp only [smul_eq_mul]; rw [hl]; field_simp; ring
  have e2 : l • x + (1 - l) • (y + h) = y := by
    simp only [smul_eq_mul]; rw [hl]; field_simp; ring
  rw [e1] at h1
  rw [e2] at h2
  simp only [smul_eq_mul] at h1 h2
  linarith

/-- **Concavity of profits** (MWG, p. 424). If the inverse demand `p` is concave and strictly
decreasing on `[0, ∞)`, then for every rival output `Q ≥ 0` and marginal cost `c` the profit
`q ↦ q(p(q + Q) − c)` is strictly concave on `[0, ∞)`: "a sufficient condition for this is for
`p(·)` to be concave". -/
theorem appendixB_profit_strictConcave {p : ℝ → ℝ} (hp : ConcaveOn ℝ (Set.Ici 0) p)
    (hpd : StrictAntiOn p (Set.Ici 0)) (c : ℝ) {Q : ℝ} (hQ : 0 ≤ Q) :
    StrictConcaveOn ℝ (Set.Ici 0) (fun q => q * (p (q + Q) - c)) := by
  refine ⟨convex_Ici 0, fun x hx y hy hxy a b ha hb hab => ?_⟩
  simp only [Set.mem_Ici] at hx hy
  simp only [smul_eq_mul]
  have hxQ : x + Q ∈ Set.Ici (0 : ℝ) := by simp only [Set.mem_Ici]; linarith
  have hyQ : y + Q ∈ Set.Ici (0 : ℝ) := by simp only [Set.mem_Ici]; linarith
  have hc := hp.2 hxQ hyQ ha.le hb.le hab
  simp only [smul_eq_mul] at hc
  have hz : a * (x + Q) + b * (y + Q) = a * x + b * y + Q := by
    linear_combination Q * hab
  rw [hz] at hc
  have hmono : 0 < (y - x) * (p (x + Q) - p (y + Q)) := by
    rcases lt_or_gt_of_ne hxy with h | h
    · have := hpd hxQ hyQ (by linarith)
      exact mul_pos (by linarith) (by linarith)
    · have := hpd hyQ hxQ (by linarith)
      exact mul_pos_of_neg_of_neg (by linarith) (by linarith)
  have hz0 : 0 ≤ a * x + b * y := by positivity
  have key : (a * x + b * y) * (a * p (x + Q) + b * p (y + Q)) - a * x * p (x + Q) -
      b * y * p (y + Q) = a * b * ((y - x) * (p (x + Q) - p (y + Q))) := by
    have hb' : b = 1 - a := by linarith
    subst hb'; ring
  have h1 := mul_le_mul_of_nonneg_left hc hz0
  have h2 : 0 < a * b * ((y - x) * (p (x + Q) - p (y + Q))) := mul_pos (mul_pos ha hb) hmono
  have hcz : a * x * c + b * y * c = (a * x + b * y) * c := by ring
  nlinarith

/-- **Downward-sloping best responses** (MWG, p. 424). If `p` is concave and strictly
decreasing on `[0, ∞)`, `0 ≤ Q ≤ Q'`, `b` is a best response to `Q` and `b'` a best response to
`Q'` (over outputs `q ≥ 0`), then `b' ≤ b`: "the concavity of `p(·)` also implies that firms'
best-response functions are downward sloping". -/
theorem appendixB_br_antitone {p : ℝ → ℝ} (hp : ConcaveOn ℝ (Set.Ici 0) p)
    (hpd : StrictAntiOn p (Set.Ici 0)) {c Q Q' b b' : ℝ} (hQ : 0 ≤ Q) (hQQ : Q ≤ Q')
    (hb : 0 ≤ b) (hbm : ∀ q, 0 ≤ q → q * (p (q + Q) - c) ≤ b * (p (b + Q) - c))
    (hb' : 0 ≤ b') (hbm' : ∀ q, 0 ≤ q → q * (p (q + Q') - c) ≤ b' * (p (b' + Q') - c)) :
    b' ≤ b := by
  by_contra hlt
  have hlt : b < b' := lt_of_not_ge hlt
  have hinc := appendixB_concave_increment hp (x := b + Q) (y := b' + Q) (h := Q' - Q)
    (by linarith) (by linarith) (by linarith)
  have e1 : b + Q + (Q' - Q) = b + Q' := by ring
  have e2 : b' + Q + (Q' - Q) = b' + Q' := by ring
  rw [e1, e2] at hinc
  have hB : p (b + Q') ≤ p (b + Q) :=
    hpd.antitoneOn (show b + Q ∈ Set.Ici (0 : ℝ) by simp only [Set.mem_Ici]; linarith)
      (show b + Q' ∈ Set.Ici (0 : ℝ) by simp only [Set.mem_Ici]; linarith) (by linarith)
  have hd1 : b' * ((p (b' + Q') - p (b' + Q)) - (p (b + Q') - p (b + Q))) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hb' (by linarith)
  have hd2 : (b' - b) * (p (b + Q') - p (b + Q)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  have h1 := hbm b' hb'
  have hbmax : b' * (p (b' + Q') - c) ≤ b * (p (b + Q') - c) := by nlinarith
  have hsc := appendixB_profit_strictConcave hp hpd c (show 0 ≤ Q' by linarith)
  have hmid := hsc.2 (show b ∈ Set.Ici (0 : ℝ) from hb) (show b' ∈ Set.Ici (0 : ℝ) from hb')
    (ne_of_lt hlt) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at hmid
  have := hbm' (1 / 2 * b + 1 / 2 * b') (by positivity)
  linarith

/-- **Figure 12.BB.1** (MWG, p. 424). "Firm E's stage 3 profits decline as we move along this
curve to the right": if `p` is strictly decreasing, `0 ≤ Q < Q'`, `b` is a best response to `Q`
and `b' > 0` is any output, then E's profit `b'(p(b' + Q') − c)` against `Q'` is strictly below
its best-response profit against `Q`. -/
theorem figure_12_BB_1 {p : ℝ → ℝ} (hpd : StrictAntiOn p (Set.Ici 0)) {c Q Q' b b' : ℝ}
    (hQ : 0 ≤ Q) (hQQ : Q < Q') (hbm : ∀ q, 0 ≤ q → q * (p (q + Q) - c) ≤ b * (p (b + Q) - c))
    (hb' : 0 < b') : b' * (p (b' + Q') - c) < b * (p (b + Q) - c) := by
  have hlt : p (b' + Q') < p (b' + Q) :=
    hpd (show b' + Q ∈ Set.Ici (0 : ℝ) by simp only [Set.mem_Ici]; linarith)
      (show b' + Q' ∈ Set.Ici (0 : ℝ) by simp only [Set.mem_Ici]; linarith) (by linarith)
  have := hbm b' hb'.le
  have : b' * (p (b' + Q') - c) < b' * (p (b' + Q) - c) :=
    mul_lt_mul_of_pos_left (by linarith) hb'
  linarith

/-- **Firm I's stage-3 best response; Figure 12.BB.2** (MWG, pp. 424-425). If I's profit `f`
(as a function of its own output, given `q_E`) is strictly concave on `[0, ∞)` with maximizer
`m = b(q_E | w) ≥ 0`, then with capacity `k_I ≥ 0` its unique best response is
`b_I(q_E | k_I) = min{b(q_E | w), k_I}`. -/
theorem figure_12_BB_2 {f : ℝ → ℝ} (hf : StrictConcaveOn ℝ (Set.Ici 0) f) {m k : ℝ}
    (hm0 : 0 ≤ m) (hm : ∀ q, 0 ≤ q → f q ≤ f m) (hk : 0 ≤ k) :
    min m k ∈ Set.Icc 0 k ∧ ∀ q ∈ Set.Icc 0 k, q ≠ min m k → f q < f (min m k) := by
  refine ⟨⟨le_min hm0 hk, min_le_right _ _⟩, fun q hq hne => ?_⟩
  obtain ⟨hq0, hqk⟩ := hq
  rcases le_or_gt m k with hmk | hkm
  · rw [min_eq_left hmk] at hne ⊢
    by_contra hge
    have hge : f m ≤ f q := le_of_not_gt hge
    have hmid := hf.2 (show q ∈ Set.Ici (0 : ℝ) from hq0) (show m ∈ Set.Ici (0 : ℝ) from hm0)
      hne (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
    simp only [smul_eq_mul] at hmid
    have := hm (1 / 2 * q + 1 / 2 * m) (by positivity)
    have := hm q hq0
    linarith
  · rw [min_eq_right hkm.le] at hne ⊢
    have hqk' : q < k := lt_of_le_of_ne hqk hne
    have hz : k ∈ openSegment ℝ q m := by
      rw [openSegment_eq_Ioo (by linarith)]; exact ⟨hqk', hkm⟩
    have h := hf.lt_on_openSegment (show q ∈ Set.Ici (0 : ℝ) from hq0)
      (show m ∈ Set.Ici (0 : ℝ) from hm0) (by intro h; linarith) hz
    rwa [min_eq_left (hm q hq0)] at h

/-- **Exercise 12.BB.1** (MWG, p. 427). Entry deterrence is better than accommodation when the
Stackelberg point `S` lies to the right of `Z`. Let `p` be strictly decreasing, E's best
response `b_E`, and `G(x) = x(p(x + b_E(x)) − (w + r))` I's profit along E's best response
(concave, maximized on `[0, ∞)` at `q_S`). If `0 < k_Z ≤ q_S` (`S` to the right of `Z`) and
`b_E(k_Z) > 0`, then every accommodation outcome (I produces `q ≤ k_Z` from capacity `k ≥ q`
and E plays `b_E(q)`; entry occurs only left of `Z`) earns I strictly less than deterrence
(capacity `k_Z`, monopoly output `k_Z`). -/
theorem exercise_12_BB_1 {p bE G : ℝ → ℝ} {w r kZ qS q k : ℝ} (hp : StrictAntiOn p (Set.Ici 0))
    (hG : ∀ x, G x = x * (p (x + bE x) - (w + r))) (hGc : ConcaveOn ℝ (Set.Ici 0) G)
    (hS : ∀ x, 0 ≤ x → G x ≤ G qS) (hZS : kZ ≤ qS) (hkZ : 0 < kZ) (hbZ : 0 < bE kZ)
    (hq : 0 ≤ q) (hqZ : q ≤ kZ) (hqk : q ≤ k) (hr : 0 ≤ r) :
    q * (p (q + bE q) - w) - r * k < kZ * (p kZ - w) - r * kZ := by
  have hseg : kZ ∈ segment ℝ q qS := by
    rw [segment_eq_Icc (by linarith)]; exact ⟨hqZ, hZS⟩
  have hmin := hGc.ge_on_segment (show q ∈ Set.Ici (0 : ℝ) from hq)
    (show qS ∈ Set.Ici (0 : ℝ) by simp only [Set.mem_Ici]; linarith) hseg
  rw [min_eq_left (hS q hq)] at hmin
  have hlt : p (kZ + bE kZ) < p kZ :=
    hp (show kZ ∈ Set.Ici (0 : ℝ) by simp only [Set.mem_Ici]; linarith)
      (show kZ + bE kZ ∈ Set.Ici (0 : ℝ) by simp only [Set.mem_Ici]; linarith) (by linarith)
  rw [hG, hG] at hmin
  have h1 : kZ * (p (kZ + bE kZ) - (w + r)) < kZ * (p kZ - (w + r)) :=
    mul_lt_mul_of_pos_left (by linarith) hkZ
  have h2 : r * q ≤ r * k := mul_le_mul_of_nonneg_left hqk hr
  nlinarith

/-- A proved instance of `exercise_12_BB_1`: `p(Q) = 10 − Q`, `w = r = 1`, `b_E(x) = (8 − x)/2`,
`G(x) = x(8 − x)/2`, `q_S = 4`, `k_Z = 3`, `q = k = 2`. -/
theorem exercise_12_BB_1_instance :
    (2 : ℝ) * ((fun x : ℝ => 10 - x) (2 + (fun x : ℝ => (8 - x) / 2) 2) - 1) - 1 * 2 <
      3 * ((fun x : ℝ => 10 - x) 3 - 1) - 1 * 3 := by
  refine exercise_12_BB_1 (p := fun x => 10 - x) (bE := fun x => (8 - x) / 2)
    (G := fun x => x * (8 - x) / 2) (qS := 4) ?_ ?_ ?_ ?_ (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) le_rfl (by norm_num)
  · intro x hx y _ hxy; simp only; linarith
  · intro x; ring
  · refine ⟨convex_Ici 0, fun x _ y _ a b ha hb hab => ?_⟩
    simp only [smul_eq_mul]
    have hb' : b = 1 - a := by linarith
    subst hb'
    nlinarith [mul_nonneg (mul_nonneg ha hb) (sq_nonneg (x - y))]
  · intro x _; nlinarith [sq_nonneg (x - 4)]

/-! ## The linear model -/

/-- Profit `(a − (q + Q))q − cq` of a firm with marginal cost `c` producing `q` against rival
output `Q`, with the linear inverse demand `p(Q) = a − Q`. -/
noncomputable def edProfit (a c q Q : ℝ) : ℝ := (a - (q + Q)) * q - c * q

theorem edProfit_eq (a c q Q : ℝ) : edProfit a c q Q = q * (a - c - Q - q) := by
  unfold edProfit; ring

/-- The maximizer of the quadratic `q(α − q)` on `[0, k]` (`α, k ≥ 0`) is `min{k, α/2}`, and it
is the unique maximizer. -/
theorem appendixB_quad_max {α k : ℝ} (hα : 0 ≤ α) (hk : 0 ≤ k) :
    min k (α / 2) ∈ Set.Icc 0 k ∧ ∀ q ∈ Set.Icc 0 k, q ≠ min k (α / 2) →
      q * (α - q) < min k (α / 2) * (α - min k (α / 2)) := by
  refine ⟨⟨le_min hk (by linarith), min_le_left _ _⟩, fun q hq hne => ?_⟩
  obtain ⟨hq0, hqk⟩ := hq
  have key : q * (α - q) - min k (α / 2) * (α - min k (α / 2)) =
      (q - min k (α / 2)) * (α - q - min k (α / 2)) := by ring
  rcases lt_or_gt_of_ne hne with h | h
  · have hm : min k (α / 2) ≤ α / 2 := min_le_right _ _
    nlinarith
  · have hm : min k (α / 2) = α / 2 := by
      rcases min_cases k (α / 2) with ⟨h1, _⟩ | ⟨h1, _⟩
      · rw [h1] at h; linarith
      · exact h1
    rw [hm] at h key ⊢
    nlinarith

/-- For every `q ≠ α/2`, `q(α − q) < (α/2)(α − α/2)`: for `α ≥ 0`, `α/2` is the unique maximizer
of `q(α − q)` on `[0, ∞)`. -/
theorem appendixB_quad_max_Ici (α : ℝ) :
    ∀ q, 0 ≤ q → q ≠ α / 2 → q * (α - q) < α / 2 * (α - α / 2) := by
  intro q _ hne
  have : 0 < (q - α / 2) ^ 2 := by
    have : q - α / 2 ≠ 0 := sub_ne_zero.2 hne
    positivity
  nlinarith

/-- The capacity `k_B = (a − w + r)/3` at point `B`, the intersection of `b(q_E | w)` and
`b(q_I | w + r)` (Figure 12.BB.3). -/
noncomputable def edKB (a w r : ℝ) : ℝ := (a - w + r) / 3

/-- Firm I's stage-3 output after entry, `min{k_I, k_B}`. -/
noncomputable def edQI (a w r k : ℝ) : ℝ := min k (edKB a w r)

/-- Firm E's stage-3 output after entry, `b(q_I | w + r) = (a − w − r − q_I)/2`. -/
noncomputable def edQE (a w r k : ℝ) : ℝ := (a - w - r - edQI a w r k) / 2

/-- Firm I's stage-3 output without entry, `b_I(0 | k_I) = min{k_I, (a − w)/2}`. -/
noncomputable def edQM (a w k : ℝ) : ℝ := min k ((a - w) / 2)

/-- Firm E's stage-3 (gross) profit after entry, given I's capacity `k`. -/
noncomputable def edProfE (a w r k : ℝ) : ℝ := edProfit a (w + r) (edQE a w r k) (edQI a w r k)

/-- The capacity `k_Z = a − w − r − 2√F` at point `Z`, where E's post-entry profit equals `F`
(Figure 12.BB.1). -/
noncomputable def edKZ (a w r F : ℝ) : ℝ := a - w - r - 2 * Real.sqrt F

/-- The capacity `k_π = u(2 + √2)/4` (`u = a − w − r`) of Figure 12.BB.8: the monopoly output
above `b(0 | w + r)` that earns the Stackelberg profit `u²/8`. -/
noncomputable def edKPi (a w r : ℝ) : ℝ := (a - w - r) * (2 + Real.sqrt 2) / 4

/-- Nash equilibrium of the stage-3 quantity game after entry, given I's capacity `k`: I
chooses `q_I ∈ [0, k]` at marginal cost `w`, E chooses `q_E ≥ 0` at marginal cost `w + r`. -/
def IsStage3Nash (a w r k qI qE : ℝ) : Prop :=
  qI ∈ Set.Icc 0 k ∧ 0 ≤ qE ∧ (∀ q ∈ Set.Icc 0 k, edProfit a w q qE ≤ edProfit a w qI qE) ∧
    ∀ q, 0 ≤ q → edProfit a (w + r) q qI ≤ edProfit a (w + r) qE qI

theorem edKB_pos {a w r : ℝ} (hr : 0 < r) (hB : 0 < a - w - 2 * r) : 0 < edKB a w r := by
  unfold edKB; linarith

theorem edQI_le {a w r k : ℝ} : edQI a w r k ≤ k := min_le_left _ _

theorem edQI_le_kB {a w r k : ℝ} : edQI a w r k ≤ edKB a w r := min_le_right _ _

theorem edQI_nonneg {a w r k : ℝ} (hr : 0 < r) (hB : 0 < a - w - 2 * r) (hk : 0 ≤ k) :
    0 ≤ edQI a w r k := le_min hk (edKB_pos hr hB).le

theorem edQI_of_le {a w r k : ℝ} (h : k ≤ edKB a w r) : edQI a w r k = k := min_eq_left h

theorem edProfE_eq (a w r k : ℝ) : edProfE a w r k = edQE a w r k ^ 2 := by
  unfold edProfE edProfit edQE; ring

/-- Firm I's stage-3 best response after entry in the linear model (Figure 12.BB.2): for
`0 ≤ q_E ≤ a − w` and `k ≥ 0`, the unique best response is `min{k, (a − w − q_E)/2}`. -/
theorem figure_12_BB_2_linear {a w qE k : ℝ} (hqE : qE ≤ a - w) (hk : 0 ≤ k) :
    min k ((a - w - qE) / 2) ∈ Set.Icc 0 k ∧ ∀ q ∈ Set.Icc 0 k, q ≠ min k ((a - w - qE) / 2) →
      edProfit a w q qE < edProfit a w (min k ((a - w - qE) / 2)) qE := by
  have h := appendixB_quad_max (α := a - w - qE) (by linarith) hk
  refine ⟨h.1, fun q hq hne => ?_⟩
  rw [edProfit_eq, edProfit_eq]
  have := h.2 q hq hne
  linarith

/-- **Stage-3 equilibrium after entry; Figure 12.BB.3** (MWG, pp. 424-425). With `r > 0`,
`a − w − 2r > 0` and capacity `k ≥ 0`, the stage-3 game has the unique Nash equilibrium
`q_I = min{k, k_B}`, `q_E = (a − w − r − q_I)/2`. Point `A`, the outcome without first-mover
advantage (both firms at cost `w + r`), is `(u/3, u/3)` with `u = a − w − r`, and point `B`
lies to its right: `k_B > u/3`, with `q_E = (a − w − 2r)/3 < u/3` at `B`. -/
theorem figure_12_BB_3 {a w r k : ℝ} (hr : 0 < r) (hB : 0 < a - w - 2 * r) (hk : 0 ≤ k) :
    IsStage3Nash a w r k (edQI a w r k) (edQE a w r k) ∧
    (∀ qI qE, IsStage3Nash a w r k qI qE → qI = edQI a w r k ∧ qE = edQE a w r k) ∧
    (∀ q, 0 ≤ q → edProfit a (w + r) q ((a - w - r) / 3) ≤
        edProfit a (w + r) ((a - w - r) / 3) ((a - w - r) / 3)) ∧
    (a - w - r) / 3 < edKB a w r ∧
    (a - w - r - edKB a w r) / 2 = (a - w - 2 * r) / 3 ∧ (a - w - 2 * r) / 3 < (a - w - r) / 3 := by
  have hKB := edKB_pos hr hB
  have hqI0 := edQI_nonneg hr hB hk
  have hqIk : edQI a w r k ≤ k := edQI_le
  have hqIB : edQI a w r k ≤ edKB a w r := edQI_le_kB
  -- the unique best response of E on `[0, ∞)`
  have hEbr : ∀ qI qE, 0 ≤ qE → qI ≤ a - w - r →
      (∀ q, 0 ≤ q → edProfit a (w + r) q qI ≤ edProfit a (w + r) qE qI) →
      qE = (a - w - r - qI) / 2 := by
    intro qI qE _ hqI h
    by_contra hne
    have := appendixB_quad_max_Ici (a - w - r - qI) qE (by assumption)
      (by intro h'; exact hne (by linarith))
    have h2 := h ((a - w - r - qI) / 2) (by linarith)
    rw [edProfit_eq, edProfit_eq] at h2
    have e : a - (w + r) - qI = a - w - r - qI := by ring
    rw [e] at h2
    linarith
  refine ⟨⟨⟨hqI0, hqIk⟩, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · unfold edQE; unfold edKB at hqIB; linarith
  · -- I's best response
    intro q hq
    have hqE : edQE a w r k ≤ a - w := by unfold edQE; unfold edKB at hqIB; linarith
    have hbr := figure_12_BB_2_linear hqE hk
    have hm : min k ((a - w - edQE a w r k) / 2) = edQI a w r k := by
      unfold edQE edQI edKB
      rcases le_or_gt k ((a - w + r) / 3) with h | h
      · rw [min_eq_left h, min_eq_left]; linarith
      · rw [min_eq_right h.le, min_eq_right] <;> linarith
    rw [hm] at hbr
    rcases eq_or_ne q (edQI a w r k) with rfl | hne
    · exact le_rfl
    · exact (hbr.2 q hq hne).le
  · intro q hq
    have h := appendixB_quad_max_Ici (a - w - r - edQI a w r k)
    rw [edProfit_eq, edProfit_eq]
    have e : a - (w + r) - edQI a w r k = a - w - r - edQI a w r k := by ring
    rw [e]
    unfold edQE
    rcases eq_or_ne q ((a - w - r - edQI a w r k) / 2) with rfl | hne
    · exact le_rfl
    · exact (h q hq hne).le
  · -- uniqueness
    rintro qI qE ⟨⟨hI0, hIk⟩, hE0, hI, hE⟩
    -- step 1: `q_I ≤ u`
    have hqIu : qI ≤ a - w - r := by
      by_contra hgt
      have hgt : a - w - r < qI := lt_of_not_ge hgt
      have hE0' : qE = 0 := by
        by_contra hne
        have hpos : 0 < qE := lt_of_le_of_ne hE0 (Ne.symm hne)
        have := hE 0 le_rfl
        rw [edProfit_eq, edProfit_eq] at this
        nlinarith
      subst hE0'
      have hbr := figure_12_BB_2_linear (a := a) (w := w) (qE := 0) (by linarith) hk
      have hqm : qI = min k ((a - w - 0) / 2) := by
        by_contra hne
        have := hbr.2 qI ⟨hI0, hIk⟩ hne
        have := hI _ hbr.1
        linarith
      have : qI ≤ (a - w - 0) / 2 := hqm ▸ min_le_right _ _
      linarith
    have hqE := hEbr qI qE hE0 hqIu hE
    subst hqE
    have hbr := figure_12_BB_2_linear (a := a) (w := w) (qE := (a - w - r - qI) / 2)
      (by linarith) hk
    have hqm : qI = min k ((a - w - (a - w - r - qI) / 2) / 2) := by
      by_contra hne
      have := hbr.2 qI ⟨hI0, hIk⟩ hne
      have := hI _ hbr.1
      linarith
    have hqI : qI = edQI a w r k := by
      unfold edQI edKB
      rcases min_cases k ((a - w - (a - w - r - qI) / 2) / 2) with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1] at hqm
        subst hqm
        rw [min_eq_left]; linarith
      · rw [h1] at hqm
        have hv : qI = (a - w + r) / 3 := by linarith
        rw [min_eq_right]
        · exact hv
        · linarith
    refine ⟨hqI, ?_⟩
    unfold edQE; rw [hqI]
  · intro q hq
    have h := appendixB_quad_max_Ici (a - w - r - (a - w - r) / 3)
    rw [edProfit_eq, edProfit_eq]
    have e : a - (w + r) - (a - w - r) / 3 = a - w - r - (a - w - r) / 3 := by ring
    have e2 : (a - w - r) / 3 = (a - w - r - (a - w - r) / 3) / 2 := by ring
    rw [e]
    rcases eq_or_ne q ((a - w - r - (a - w - r) / 3) / 2) with h' | hne
    · rw [h', ← e2]
    · have := h q hq hne
      rw [← e2] at this
      exact this.le
  · unfold edKB; linarith
  · unfold edKB; ring
  · linarith

/-- **Figure 12.BB.3, the reachable points** (MWG, p. 425). By its choice of capacity, firm I
can make the post-entry equilibrium any point of E's best-response function up to `B`: for
every `q ∈ [0, k_B]` the capacity `k = q` yields `(q, (u − q)/2)`; and no capacity yields a
point beyond `B` (`q_I ≤ k_B` always). -/
theorem figure_12_BB_3_range {a w r : ℝ} (hr : 0 < r) (hB : 0 < a - w - 2 * r) :
    (∀ q, 0 ≤ q → q ≤ edKB a w r → IsStage3Nash a w r q q ((a - w - r - q) / 2)) ∧
    ∀ k, edQI a w r k ≤ edKB a w r := by
  refine ⟨fun q hq hqB => ?_, fun k => edQI_le_kB⟩
  have h := (figure_12_BB_3 hr hB hq).1
  have e : edQI a w r q = q := edQI_of_le hqB
  unfold edQE at h
  rwa [e] at h

/-- **Figure 12.BB.4** (MWG, p. 425). If I builds capacity `k > k_B`, the post-entry equilibrium
is `B` and I does not use all its capacity (`q_I = k_B < k`); a threat to produce up to
capacity is not credible: producing `k` against E's equilibrium output is strictly worse for I
than producing `k_B`. -/
theorem figure_12_BB_4 {a w r k : ℝ} (hr : 0 < r) (hB : 0 < a - w - 2 * r)
    (hk : edKB a w r < k) :
    edQI a w r k = edKB a w r ∧ edQI a w r k < k ∧
    edProfit a w k (edQE a w r k) < edProfit a w (edQI a w r k) (edQE a w r k) := by
  have hqI : edQI a w r k = edKB a w r := min_eq_right hk.le
  refine ⟨hqI, by rw [hqI]; exact hk, ?_⟩
  have hk0 : 0 ≤ k := by linarith [edKB_pos hr hB]
  have hqE : edQE a w r k ≤ a - w := by
    unfold edQE; rw [hqI]; unfold edKB; linarith
  have hbr := figure_12_BB_2_linear hqE hk0
  have hm : min k ((a - w - edQE a w r k) / 2) = edQI a w r k := by
    unfold edQE; rw [hqI]; unfold edKB at hk ⊢
    rw [min_eq_right] <;> linarith
  rw [hm] at hbr
  exact hbr.2 k ⟨hk0, le_rfl⟩ (by rw [hqI]; exact ne_of_gt hk)

/-- **Stage-3 outcome without entry** (MWG, p. 425). If E does not enter, I is a monopolist with
capacity `k ≥ 0`, and its unique optimal output is `b_I(0 | k) = min{k, (a − w)/2}`. -/
theorem appendixB_stage3_noEntry {a w k : ℝ} (hw : w < a) (hk : 0 ≤ k) :
    edQM a w k ∈ Set.Icc 0 k ∧
    ∀ q ∈ Set.Icc 0 k, q ≠ edQM a w k → edProfit a w q 0 < edProfit a w (edQM a w k) 0 := by
  have h := figure_12_BB_2_linear (a := a) (w := w) (qE := 0) (by linarith) hk
  simpa [edQM] using h

/-- **Figure 12.BB.1, linear model** (MWG, p. 424). Along E's best response `b(q_I | w + r)`,
E's profit is `((u − q_I)/2)²`, strictly decreasing in `q_I ∈ [0, u]`; for `0 ≤ F` and
`q_I ≤ u`, it is at least `F` iff `q_I ≤ k_Z = u − 2√F`, and it equals `F` at `k_Z`. -/
theorem figure_12_BB_1_linear {a w r F : ℝ} (hF : 0 ≤ F) :
    (∀ q, edProfit a (w + r) ((a - w - r - q) / 2) q = ((a - w - r - q) / 2) ^ 2) ∧
    (∀ q q', q < q' → q' ≤ a - w - r → ((a - w - r - q') / 2) ^ 2 < ((a - w - r - q) / 2) ^ 2) ∧
    (∀ q, q ≤ a - w - r → (F ≤ ((a - w - r - q) / 2) ^ 2 ↔ q ≤ edKZ a w r F)) ∧
    (∀ q, q ≤ a - w - r → (F < ((a - w - r - q) / 2) ^ 2 ↔ q < edKZ a w r F)) ∧
    ((a - w - r - edKZ a w r F) / 2) ^ 2 = F := by
  have hs := Real.sq_sqrt hF
  have hs0 := Real.sqrt_nonneg F
  refine ⟨fun q => by unfold edProfit; ring, fun q q' hq hq' => by nlinarith, fun q hq => ?_,
    fun q hq => ?_, by unfold edKZ; nlinarith⟩
  · unfold edKZ
    constructor
    · intro h
      by_contra hc
      have : (a - w - r - q) / 2 < Real.sqrt F := by linarith
      nlinarith
    · intro h
      have : Real.sqrt F ≤ (a - w - r - q) / 2 := by linarith
      nlinarith
  · unfold edKZ
    constructor
    · intro h
      by_contra hc
      have : (a - w - r - q) / 2 ≤ Real.sqrt F := by linarith
      nlinarith
    · intro h
      have : Real.sqrt F < (a - w - r - q) / 2 := by linarith
      nlinarith

/-- **Stage 2: firm E's entry decision** (MWG, p. 426; also Section 12.G, p. 417). Given I's
capacity `k ≥ 0` and `F ≥ 0`, E's post-entry profit is at least `F` iff the post-entry
equilibrium lies at or to the left of `Z` (`q_I ≤ k_Z`), and exceeds `F` iff it lies strictly to
the left. -/
theorem appendixB_stage2 {a w r F k : ℝ} (hB : 0 < a - w - 2 * r) (hF : 0 ≤ F) :
    (F ≤ edProfE a w r k ↔ edQI a w r k ≤ edKZ a w r F) ∧
    (F < edProfE a w r k ↔ edQI a w r k < edKZ a w r F) := by
  have hu : edQI a w r k ≤ a - w - r := by
    have := edQI_le_kB (a := a) (w := w) (r := r) (k := k); unfold edKB at this; linarith
  have h := figure_12_BB_1_linear (a := a) (w := w) (r := r) hF
  rw [edProfE_eq]
  exact ⟨h.2.2.1 _ hu, h.2.2.2.1 _ hu⟩

/-! ## Stage 1 and the subgame perfect equilibria -/

/-- Firm I's overall profit when it builds capacity `k` and E enters (`true`) or stays out
(`false`), with stage-3 play at the unique stage-3 equilibrium (`figure_12_BB_3`,
`appendixB_stage3_noEntry`). -/
noncomputable def edPayI (a w r k : ℝ) (enter : Bool) : ℝ :=
  cond enter (edProfit a w (edQI a w r k) (edQE a w r k) - r * k)
    (edProfit a w (edQM a w k) 0 - r * k)

/-- E's stage-2 strategy `e` (enter after capacity `k` iff `e k = true`) is optimal in every
stage-2 subgame: E enters when its post-entry profit exceeds `F` and stays out when it falls
short of `F` (either choice is optimal at a tie). -/
def EDEntryOptimal (a w r F : ℝ) (e : ℝ → Bool) : Prop :=
  ∀ k, 0 ≤ k → (F < edProfE a w r k → e k = true) ∧ (edProfE a w r k < F → e k = false)

/-- A subgame perfect Nash equilibrium of the three-stage game: E's entry strategy is optimal
after every capacity, stage 3 is played at its unique equilibrium, and I's capacity `k`
maximizes its overall profit given E's strategy. -/
def IsEDSPNE (a w r F k : ℝ) (e : ℝ → Bool) : Prop :=
  0 ≤ k ∧ EDEntryOptimal a w r F e ∧
    ∀ k', 0 ≤ k' → edPayI a w r k' (e k') ≤ edPayI a w r k (e k)

/-- The book's stage-2 rule (p. 426): E enters iff it expects nonnegative profits net of `F`. -/
noncomputable def edBookRule (a w r F k : ℝ) : Bool := decide (F ≤ edProfE a w r k)

/-- The rule under which E stays out when indifferent. -/
noncomputable def edStayOutRule (a w r F k : ℝ) : Bool := decide (F < edProfE a w r k)

theorem edBookRule_optimal (a w r F : ℝ) : EDEntryOptimal a w r F (edBookRule a w r F) :=
  fun _ _ => ⟨fun h => decide_eq_true h.le, fun h => decide_eq_false (not_le.2 h)⟩

theorem edStayOutRule_optimal (a w r F : ℝ) : EDEntryOptimal a w r F (edStayOutRule a w r F) :=
  fun _ _ => ⟨fun h => decide_eq_true h, fun h => decide_eq_false (not_lt.2 h.le)⟩

theorem edPayI_true_eq (a w r k : ℝ) : edPayI a w r k true =
    edQI a w r k * (a - w - r - edQI a w r k) / 2 - r * (k - edQI a w r k) := by
  change edProfit a w (edQI a w r k) (edQE a w r k) - r * k = _
  unfold edProfit edQE; ring

theorem edPayI_false_eq (a w r k : ℝ) : edPayI a w r k false =
    edQM a w k * (a - w - r - edQM a w k) - r * (k - edQM a w k) := by
  change edProfit a w (edQM a w k) 0 - r * k = _
  unfold edProfit; ring

/-- With entry, I earns at most the Stackelberg profit `u²/8`. -/
theorem edPayI_true_le {a w r k : ℝ} (hr : 0 < r) : edPayI a w r k true ≤ (a - w - r) ^ 2 / 8 := by
  rw [edPayI_true_eq]
  have h1 : edQI a w r k ≤ k := edQI_le
  nlinarith [sq_nonneg (a - w - r - 2 * edQI a w r k), mul_nonneg hr.le (sub_nonneg.2 h1)]

/-- Without entry, I earns at most the monopoly profit `u²/4` of a firm with cost `w + r`. -/
theorem edPayI_false_le {a w r k : ℝ} (hr : 0 < r) :
    edPayI a w r k false ≤ (a - w - r) ^ 2 / 4 := by
  rw [edPayI_false_eq]
  have h1 : edQM a w k ≤ k := min_le_left _ _
  nlinarith [sq_nonneg (a - w - r - 2 * edQM a w k), mul_nonneg hr.le (sub_nonneg.2 h1)]

/-- **Blockaded entry; Figure 12.BB.5** (MWG, p. 426). If E would not enter even when I builds
the uncontested-monopoly capacity `b(0 | w + r) = u/2` (`π_E(u/2) < F`), then I achieves its
best possible outcome: no capacity and entry decision gives more than `u²/4`; for every optimal
entry strategy, `k_I = u/2` with no entry and output `u/2` is an SPNE earning `u²/4`; and every
SPNE has `k_I = u/2` and no entry. -/
theorem figure_12_BB_5 {a w r F : ℝ} (hr : 0 < r) (hB : 0 < a - w - 2 * r)
    (hbl : edProfE a w r ((a - w - r) / 2) < F) :
    (∀ k : ℝ, ∀ b : Bool, edPayI a w r k b ≤ (a - w - r) ^ 2 / 4) ∧
    edQM a w ((a - w - r) / 2) = (a - w - r) / 2 ∧
    edPayI a w r ((a - w - r) / 2) false = (a - w - r) ^ 2 / 4 ∧
    (∀ e, EDEntryOptimal a w r F e →
      IsEDSPNE a w r F ((a - w - r) / 2) e ∧ e ((a - w - r) / 2) = false) ∧
    ∀ k e, IsEDSPNE a w r F k e → k = (a - w - r) / 2 ∧ e k = false := by
  have hu : 0 < a - w - r := by linarith
  have hqM : edQM a w ((a - w - r) / 2) = (a - w - r) / 2 := min_eq_left (by linarith)
  have hval : edPayI a w r ((a - w - r) / 2) false = (a - w - r) ^ 2 / 4 := by
    rw [edPayI_false_eq, hqM]; ring
  have hbound : ∀ k : ℝ, ∀ b : Bool, edPayI a w r k b ≤ (a - w - r) ^ 2 / 4 := by
    intro k b
    cases b
    · exact edPayI_false_le hr
    · exact (edPayI_true_le hr).trans (by nlinarith)
  refine ⟨hbound, hqM, hval, fun e he => ?_, fun k e hspne => ?_⟩
  · have hout : e ((a - w - r) / 2) = false := (he _ (by linarith)).2 hbl
    refine ⟨⟨by linarith, he, fun k' _ => ?_⟩, hout⟩
    rw [hout, hval]; exact hbound _ _
  · obtain ⟨_, he, hopt⟩ := hspne
    have hout : e ((a - w - r) / 2) = false := (he _ (by linarith)).2 hbl
    have h := hopt _ (by linarith : (0 : ℝ) ≤ (a - w - r) / 2)
    rw [hout, hval] at h
    cases hek : e k
    · rw [hek, edPayI_false_eq] at h
      have h1 : edQM a w k ≤ k := min_le_left _ _
      have h2 := mul_nonneg hr.le (sub_nonneg.2 h1)
      have hsq : (a - w - r - 2 * edQM a w k) ^ 2 = 0 := by
        nlinarith [sq_nonneg (a - w - r - 2 * edQM a w k)]
      have hrk : r * (k - edQM a w k) = 0 := by
        nlinarith [sq_nonneg (a - w - r - 2 * edQM a w k)]
      have hq : edQM a w k = (a - w - r) / 2 := by
        have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hsq
        linarith
      have hk : k - edQM a w k = 0 := by
        rcases mul_eq_zero.1 hrk with h | h
        · linarith
        · exact h
      exact ⟨by linarith, rfl⟩
    · rw [hek] at h
      have := edPayI_true_le (a := a) (w := w) (k := k) hr
      nlinarith

/-- **Entry inevitable: strategic accommodation; Figure 12.BB.6** (MWG, pp. 426-427). If `Z`
lies to the right of `B` (`π_E(k_B) > F`), E enters after every capacity, and the SPNE
capacity is the Stackelberg output `S = u/2`, or `k_B` if `S` lies to the right of `B`: for
every optimal entry strategy `k_I = min{k_B, u/2}` is an SPNE, every SPNE has this capacity,
and I's profit is `k_I(u − k_I)/2`. -/
theorem figure_12_BB_6 {a w r F : ℝ} (hr : 0 < r) (hB : 0 < a - w - 2 * r)
    (hacc : F < edProfE a w r (edKB a w r)) :
    (∀ e, EDEntryOptimal a w r F e → ∀ k, 0 ≤ k → e k = true) ∧
    (∀ e, EDEntryOptimal a w r F e →
      IsEDSPNE a w r F (min (edKB a w r) ((a - w - r) / 2)) e) ∧
    (∀ k e, IsEDSPNE a w r F k e → k = min (edKB a w r) ((a - w - r) / 2)) ∧
    edPayI a w r (min (edKB a w r) ((a - w - r) / 2)) true =
      min (edKB a w r) ((a - w - r) / 2) *
        (a - w - r - min (edKB a w r) ((a - w - r) / 2)) / 2 := by
  have hu : 0 < a - w - r := by linarith
  have hKB := edKB_pos hr hB
  have hmono : ∀ k, edProfE a w r (edKB a w r) ≤ edProfE a w r k := by
    intro k
    rw [edProfE_eq, edProfE_eq]
    unfold edQE
    rw [edQI_of_le le_rfl]
    have h1 : edQI a w r k ≤ edKB a w r := edQI_le_kB
    have h2 : edKB a w r ≤ a - w - r := by unfold edKB; linarith
    nlinarith
  have hin : ∀ e, EDEntryOptimal a w r F e → ∀ k, 0 ≤ k → e k = true :=
    fun e he k hk => (he k hk).1 (lt_of_lt_of_le hacc (hmono k))
  obtain ⟨⟨hS0, hSB⟩, hstrict⟩ := appendixB_quad_max (α := a - w - r) hu.le hKB.le
  have hqIS : edQI a w r (min (edKB a w r) ((a - w - r) / 2)) =
      min (edKB a w r) ((a - w - r) / 2) := edQI_of_le hSB
  have hval : edPayI a w r (min (edKB a w r) ((a - w - r) / 2)) true =
      min (edKB a w r) ((a - w - r) / 2) * (a - w - r - min (edKB a w r) ((a - w - r) / 2)) /
        2 := by
    rw [edPayI_true_eq, hqIS]; ring
  -- every entry payoff is at most the value at `min{k_B, u/2}`, with equality only there
  have hle : ∀ k, 0 ≤ k → edPayI a w r k true ≤
      edPayI a w r (min (edKB a w r) ((a - w - r) / 2)) true ∧
      (edPayI a w r (min (edKB a w r) ((a - w - r) / 2)) true ≤ edPayI a w r k true →
        k = min (edKB a w r) ((a - w - r) / 2)) := by
    intro k hk
    have hq0 := edQI_nonneg hr hB hk
    have hqB : edQI a w r k ≤ edKB a w r := edQI_le_kB
    have hqk : edQI a w r k ≤ k := edQI_le
    have hrk := mul_nonneg hr.le (sub_nonneg.2 hqk)
    rw [hval, edPayI_true_eq]
    constructor
    · rcases eq_or_ne (edQI a w r k) (min (edKB a w r) ((a - w - r) / 2)) with h | h
      · rw [h] at hrk ⊢; linarith
      · have := hstrict _ ⟨hq0, hqB⟩ h; linarith
    · intro hge
      have hq : edQI a w r k = min (edKB a w r) ((a - w - r) / 2) := by
        by_contra h
        have := hstrict _ ⟨hq0, hqB⟩ h; linarith
      rw [hq] at hge hrk
      have : r * (k - min (edKB a w r) ((a - w - r) / 2)) = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · linarith
      · linarith
  refine ⟨hin, fun e he => ⟨hS0, he, fun k' hk' => ?_⟩, fun k e hspne => ?_, hval⟩
  · rw [hin e he k' hk', hin e he _ hS0]
    exact (hle k' hk').1
  · obtain ⟨hk, he, hopt⟩ := hspne
    have h := hopt _ hS0
    rw [hin e he k hk, hin e he _ hS0] at h
    exact (hle k hk).2 h

/-- **First-mover advantage at `S`** (MWG, p. 426). If `S` lies (weakly) to the left of `B`,
then at `S` firm I produces `u/2`, E produces `u/4`, I earns `u²/8`, and this is strictly more
than E's net profit `u²/16 − F` (for `F ≥ 0`). -/
theorem figure_12_BB_6_firstMover {a w r F : ℝ} (hr : 0 < r) (hB : 0 < a - w - 2 * r)
    (hF : 0 ≤ F) (hS : (a - w - r) / 2 ≤ edKB a w r) :
    edQI a w r ((a - w - r) / 2) = (a - w - r) / 2 ∧
    edQE a w r ((a - w - r) / 2) = (a - w - r) / 4 ∧
    edPayI a w r ((a - w - r) / 2) true = (a - w - r) ^ 2 / 8 ∧
    edProfE a w r ((a - w - r) / 2) - F < edPayI a w r ((a - w - r) / 2) true := by
  have hu : 0 < a - w - r := by linarith
  have hq : edQI a w r ((a - w - r) / 2) = (a - w - r) / 2 := edQI_of_le hS
  have hE : edQE a w r ((a - w - r) / 2) = (a - w - r) / 4 := by unfold edQE; rw [hq]; ring
  have hP : edPayI a w r ((a - w - r) / 2) true = (a - w - r) ^ 2 / 8 := by
    rw [edPayI_true_eq, hq]; ring
  refine ⟨hq, hE, hP, ?_⟩
  rw [hP, edProfE_eq, hE]
  nlinarith

/-- **`S` to the right of `B`** (MWG, pp. 426-427). If `k_B < u/2`, the optimal accommodation
capacity is `k_B` and I's profit there is strictly below the Stackelberg profit `u²/8`. -/
theorem figure_12_BB_6_rightOfB {a w r : ℝ} (hSB : edKB a w r < (a - w - r) / 2) :
    min (edKB a w r) ((a - w - r) / 2) = edKB a w r ∧
    edPayI a w r (edKB a w r) true < (a - w - r) ^ 2 / 8 := by
  refine ⟨min_eq_left hSB.le, ?_⟩
  rw [edPayI_true_eq, edQI_of_le le_rfl]
  have : 0 < (a - w - r - 2 * edKB a w r) ^ 2 := by
    have : a - w - r - 2 * edKB a w r ≠ 0 := by intro h; linarith
    positivity
  nlinarith

/-- **The region where deterrence is possible but not inevitable** (MWG, p. 427): if
`π_E(k_B) < F ≤ π_E(u/2)` (`Z` left of `B`, entry not blockaded), then `F > 0`,
`u/2 ≤ k_B`, and `u/2 ≤ k_Z < k_B ≤ (a − w)/2`. -/
theorem appendixB_deter_region {a w r F : ℝ} (hB : 0 < a - w - 2 * r)
    (hD1 : edProfE a w r (edKB a w r) < F) (hD2 : F ≤ edProfE a w r ((a - w - r) / 2)) :
    0 < F ∧ (a - w - r) / 2 ≤ edKB a w r ∧ (a - w - r) / 2 ≤ edKZ a w r F ∧
    edKZ a w r F < edKB a w r ∧ edKB a w r ≤ (a - w) / 2 := by
  have hF : 0 < F := lt_of_le_of_lt (by rw [edProfE_eq]; positivity) hD1
  have hSB : (a - w - r) / 2 ≤ edKB a w r := by
    by_contra h
    have h : edKB a w r < (a - w - r) / 2 := lt_of_not_ge h
    have e1 : edQI a w r ((a - w - r) / 2) = edKB a w r := min_eq_right h.le
    have e2 : edProfE a w r ((a - w - r) / 2) = edProfE a w r (edKB a w r) := by
      rw [edProfE_eq, edProfE_eq]; unfold edQE; rw [e1, edQI_of_le le_rfl]
    linarith
  have h2 := (appendixB_stage2 (k := (a - w - r) / 2) hB hF.le).1.1 hD2
  rw [edQI_of_le hSB] at h2
  have h3 : ¬ edQI a w r (edKB a w r) ≤ edKZ a w r F := fun h =>
    absurd ((appendixB_stage2 (k := edKB a w r) hB hF.le).1.2 h) (not_le.2 hD1)
  rw [edQI_of_le le_rfl] at h3
  exact ⟨hF, hSB, h2, lt_of_not_ge h3, by unfold edKB; linarith⟩

/-- **The linear model never has `S` strictly to the right of `Z` unless entry is blockaded**
(remark to Exercise 12.BB.1). If entry is not blockaded (`F ≤ π_E(u/2)`, `F ≥ 0`) and `S` lies
weakly left of `B`, then `S = u/2 ≤ k_Z`. -/
theorem appendixB_linear_S_le_Z {a w r F : ℝ} (hB : 0 < a - w - 2 * r) (hF : 0 ≤ F)
    (hnb : F ≤ edProfE a w r ((a - w - r) / 2)) (hSB : (a - w - r) / 2 ≤ edKB a w r) :
    (a - w - r) / 2 ≤ edKZ a w r F := by
  have h2 := (appendixB_stage2 (k := (a - w - r) / 2) hB hF).1.1 hnb
  rwa [edQI_of_le hSB] at h2

/-- **Entry in the deterrence region** (MWG, p. 427). Under any optimal entry strategy, E enters
after every capacity `k < k_Z` and stays out after every `k > k_Z` ("a capacity level at least
as large as `k_Z`" deters, up to the tie at `k_Z`). -/
theorem appendixB_deter_entry {a w r F : ℝ} (hB : 0 < a - w - 2 * r)
    (hD1 : edProfE a w r (edKB a w r) < F) (hD2 : F ≤ edProfE a w r ((a - w - r) / 2))
    {e : ℝ → Bool} (he : EDEntryOptimal a w r F e) :
    (∀ k, 0 ≤ k → k < edKZ a w r F → e k = true) ∧
    (∀ k, edKZ a w r F < k → e k = false) := by
  obtain ⟨hF, _, hZ, hZB, _⟩ := appendixB_deter_region hB hD1 hD2
  have hu : 0 < a - w - r := by linarith
  refine ⟨fun k hk hkZ => (he k hk).1 ?_, fun k hk => (he k (by linarith)).2 ?_⟩
  · exact (appendixB_stage2 hB hF.le).2.2 (lt_of_le_of_lt edQI_le hkZ)
  · have hq : edKZ a w r F < edQI a w r k := lt_min hk hZB
    by_contra h
    exact absurd ((appendixB_stage2 hB hF.le).1.1 (le_of_not_gt h)) (not_le.2 hq)

/-- No-entry payoffs in the deterrence region: for `k ≥ k_Z`, I's profit without entry is at
most the deterrence profit `k_Z(u − k_Z)`, strictly less if `k > k_Z`, and equal to it at
`k = k_Z`. -/
theorem appendixB_deter_noEntry {a w r F : ℝ} (hr : 0 < r) (hB : 0 < a - w - 2 * r)
    (hD1 : edProfE a w r (edKB a w r) < F) (hD2 : F ≤ edProfE a w r ((a - w - r) / 2)) :
    edPayI a w r (edKZ a w r F) false = edKZ a w r F * (a - w - r - edKZ a w r F) ∧
    ∀ k, edKZ a w r F ≤ k →
      edPayI a w r k false ≤ edKZ a w r F * (a - w - r - edKZ a w r F) ∧
      (edKZ a w r F < k → edPayI a w r k false < edKZ a w r F * (a - w - r - edKZ a w r F)) := by
  obtain ⟨_, _, hZ, hZB, hBw⟩ := appendixB_deter_region hB hD1 hD2
  refine ⟨?_, fun k hk => ?_⟩
  · rw [edPayI_false_eq, show edQM a w (edKZ a w r F) = edKZ a w r F from
      min_eq_left (by linarith)]
    ring
  have hqk : edQM a w k ≤ k := min_le_left _ _
  have hqZ : edKZ a w r F ≤ edQM a w k := le_min hk (by linarith)
  have hrk := mul_nonneg hr.le (sub_nonneg.2 hqk)
  rw [edPayI_false_eq]
  refine ⟨by nlinarith, fun hlt => ?_⟩
  have hqZ' : edKZ a w r F < edQM a w k := lt_min hlt (by linarith)
  nlinarith

/-- **Figure 12.BB.8: the capacity `k_π`** (MWG, p. 427). `k_π = u(2 + √2)/4` is the monopoly
output above `u/2` earning exactly the Stackelberg profit `u²/8`; for every `k ≥ u/2`, the
monopoly profit `k(u − k)` exceeds `u²/8` iff `k < k_π` and falls short of it iff `k > k_π`.
So, comparing the deterrence profit `k_Z(u − k_Z)` with the accommodation profit `u²/8`: if
`k_π > k_Z` deterrence is better, and if `k_π < k_Z` accommodation is better. -/
theorem figure_12_BB_8 {a w r k : ℝ} (hu : 0 < a - w - r) (hk : (a - w - r) / 2 ≤ k) :
    edKPi a w r * (a - w - r - edKPi a w r) = (a - w - r) ^ 2 / 8 ∧
    (a - w - r) / 2 < edKPi a w r ∧
    ((a - w - r) ^ 2 / 8 < k * (a - w - r - k) ↔ k < edKPi a w r) ∧
    (k * (a - w - r - k) < (a - w - r) ^ 2 / 8 ↔ edKPi a w r < k) := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hs0 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hpi : edKPi a w r * (a - w - r - edKPi a w r) = (a - w - r) ^ 2 / 8 := by
    unfold edKPi; nlinarith
  have hgt : (a - w - r) / 2 < edKPi a w r := by
    unfold edKPi; nlinarith
  have key : k * (a - w - r - k) - (a - w - r) ^ 2 / 8 =
      (edKPi a w r - k) * (k + edKPi a w r - (a - w - r)) := by rw [← hpi]; ring
  have hpos : 0 < k + edKPi a w r - (a - w - r) := by linarith
  refine ⟨hpi, hgt, ⟨fun h => ?_, fun h => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩⟩
  · by_contra h'
    have : (edKPi a w r - k) * (k + edKPi a w r - (a - w - r)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) hpos.le
    linarith
  · have := mul_pos (sub_pos.2 h) hpos; linarith
  · by_contra h'
    have : 0 ≤ (edKPi a w r - k) * (k + edKPi a w r - (a - w - r)) :=
      mul_nonneg (by linarith) hpos.le
    linarith
  · have := mul_neg_of_neg_of_pos (sub_neg.2 h) hpos; linarith

/-- **Entry deterrence possible but not inevitable, deterrence optimal; Figures 12.BB.7 and
12.BB.8** (MWG, p. 427). In the region `π_E(k_B) < F ≤ π_E(u/2)`, if `k_Z < k_π`: for every
optimal entry strategy under which E stays out at the tie `k_Z`, capacity `k_Z` (no entry,
output `k_Z`) is an SPNE; every SPNE has capacity `k_Z` and E staying out at `k_Z`; and such
an entry strategy exists (`edStayOutRule`). -/
theorem figure_12_BB_7_deter {a w r F : ℝ} (hr : 0 < r) (hB : 0 < a - w - 2 * r)
    (hD1 : edProfE a w r (edKB a w r) < F) (hD2 : F ≤ edProfE a w r ((a - w - r) / 2))
    (hlt : edKZ a w r F < edKPi a w r) :
    (∀ e, EDEntryOptimal a w r F e → e (edKZ a w r F) = false →
      IsEDSPNE a w r F (edKZ a w r F) e) ∧
    (∀ k e, IsEDSPNE a w r F k e → k = edKZ a w r F ∧ e (edKZ a w r F) = false) ∧
    EDEntryOptimal a w r F (edStayOutRule a w r F) ∧
    edStayOutRule a w r F (edKZ a w r F) = false := by
  obtain ⟨hF, _, hZ, hZB, hBw⟩ := appendixB_deter_region hB hD1 hD2
  have hu : 0 < a - w - r := by linarith
  have hpi := figure_12_BB_8 (k := edKZ a w r F) hu hZ
  have hDA : (a - w - r) ^ 2 / 8 < edKZ a w r F * (a - w - r - edKZ a w r F) := hpi.2.2.1.2 hlt
  obtain ⟨hval, hno⟩ := appendixB_deter_noEntry hr hB hD1 hD2
  have hZ0 : 0 ≤ edKZ a w r F := by linarith
  -- every payoff is at most the deterrence payoff
  have hbound : ∀ e, EDEntryOptimal a w r F e → ∀ k', 0 ≤ k' →
      edPayI a w r k' (e k') ≤ edKZ a w r F * (a - w - r - edKZ a w r F) := by
    intro e he k' hk'
    have hent := appendixB_deter_entry hB hD1 hD2 he
    cases hek : e k'
    · have : edKZ a w r F ≤ k' := by
        by_contra h
        have := hent.1 k' hk' (lt_of_not_ge h)
        rw [hek] at this; exact absurd this (by decide)
      exact (hno k' this).1
    · exact (edPayI_true_le hr).trans hDA.le
  have hout : edStayOutRule a w r F (edKZ a w r F) = false := by
    unfold edStayOutRule
    have h := (figure_12_BB_1_linear (a := a) (w := w) (r := r) hF.le).2.2.2.2
    rw [edProfE_eq]; unfold edQE; rw [edQI_of_le hZB.le, h]
    exact decide_eq_false (lt_irrefl F)
  refine ⟨fun e he hez => ⟨hZ0, he, fun k' hk' => ?_⟩, fun k e hspne => ?_,
    edStayOutRule_optimal a w r F, hout⟩
  · rw [hez, hval]; exact hbound e he k' hk'
  · obtain ⟨hk, he, hopt⟩ := hspne
    have hent := appendixB_deter_entry hB hD1 hD2 he
    -- I's equilibrium payoff is at least the deterrence payoff
    have hge : edKZ a w r F * (a - w - r - edKZ a w r F) ≤ edPayI a w r k (e k) := by
      by_contra hlt'
      have hlt' := lt_of_not_ge hlt'
      have hg : 0 < edKZ a w r F * (a - w - r - edKZ a w r F) - edPayI a w r k (e k) := by
        linarith
      have hc : 0 < 2 * edKZ a w r F - (a - w - r) + 2 := by linarith
      obtain ⟨δ, hδ0, hδ1, hδ2, hδ3⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
          δ ≤ (a - w) / 2 - edKZ a w r F ∧ δ * (2 * edKZ a w r F - (a - w - r) + 2) ≤
            edKZ a w r F * (a - w - r - edKZ a w r F) - edPayI a w r k (e k) := by
        refine ⟨min (min 1 ((a - w) / 2 - edKZ a w r F))
          ((edKZ a w r F * (a - w - r - edKZ a w r F) - edPayI a w r k (e k)) /
            (2 * edKZ a w r F - (a - w - r) + 2)),
          lt_min (lt_min one_pos (by linarith)) (div_pos hg hc),
          (min_le_left _ _).trans (min_le_left _ _), (min_le_left _ _).trans (min_le_right _ _),
          ?_⟩
        have := min_le_right (min 1 ((a - w) / 2 - edKZ a w r F))
          ((edKZ a w r F * (a - w - r - edKZ a w r F) - edPayI a w r k (e k)) /
            (2 * edKZ a w r F - (a - w - r) + 2))
        rwa [le_div_iff₀ hc] at this
      have hout' := hent.2 (edKZ a w r F + δ) (by linarith)
      have hqM : edQM a w (edKZ a w r F + δ) = edKZ a w r F + δ := min_eq_left (by linarith)
      have hpay : edPayI a w r (edKZ a w r F + δ) false =
          (edKZ a w r F + δ) * (a - w - r - (edKZ a w r F + δ)) := by
        rw [edPayI_false_eq, hqM]; ring
      have h := hopt (edKZ a w r F + δ) (by linarith)
      rw [hout', hpay] at h
      nlinarith [mul_nonneg hδ0.le (sub_nonneg.2 hδ1)]
    cases hek : e k
    · rw [hek] at hge
      have hkZ : edKZ a w r F ≤ k := by
        by_contra h
        have := hent.1 k hk (lt_of_not_ge h)
        rw [hek] at this; exact absurd this (by decide)
      rcases eq_or_lt_of_le hkZ with h | h
      · subst h; exact ⟨rfl, hek⟩
      · have := (hno k hkZ).2 h; linarith
    · rw [hek] at hge
      have := edPayI_true_le (a := a) (w := w) (k := k) hr
      linarith

/-- **Correction: the book's tie rule.** Under the book's stage-2 rule ("enter if it expects
nonnegative profits", `edBookRule`), which is an optimal entry strategy, E enters at the
capacity `k_Z` itself; hence in the deterrence region with `k_Z < k_π` the three-stage game has
no SPNE in which E follows the book's rule: capacity `k_Z` does not deter, and capacities above
`k_Z` are dominated by smaller ones still above `k_Z`. -/
theorem appendixB_bookRule_no_spne {a w r F : ℝ} (hr : 0 < r) (hB : 0 < a - w - 2 * r)
    (hD1 : edProfE a w r (edKB a w r) < F) (hD2 : F ≤ edProfE a w r ((a - w - r) / 2))
    (hlt : edKZ a w r F < edKPi a w r) :
    EDEntryOptimal a w r F (edBookRule a w r F) ∧ edBookRule a w r F (edKZ a w r F) = true ∧
    ¬ ∃ k, IsEDSPNE a w r F k (edBookRule a w r F) := by
  obtain ⟨hF, _, _, hZB, _⟩ := appendixB_deter_region hB hD1 hD2
  have hin : edBookRule a w r F (edKZ a w r F) = true := by
    unfold edBookRule
    have h := (figure_12_BB_1_linear (a := a) (w := w) (r := r) hF.le).2.2.2.2
    rw [edProfE_eq]; unfold edQE; rw [edQI_of_le hZB.le, h]
    exact decide_eq_true le_rfl
  refine ⟨edBookRule_optimal a w r F, hin, fun ⟨k, hk⟩ => ?_⟩
  have := ((figure_12_BB_7_deter hr hB hD1 hD2 hlt).2.1 k _ hk).2
  rw [hin] at this
  exact absurd this (by decide)

/-- **Entry deterrence possible but not inevitable, accommodation optimal; Figures 12.BB.7 and
12.BB.8** (MWG, p. 427). In the region `π_E(k_B) < F ≤ π_E(u/2)`, if `k_π < k_Z`: for every
optimal entry strategy, the Stackelberg capacity `u/2` with entry is an SPNE, and every SPNE
has capacity `u/2`. -/
theorem figure_12_BB_7_accommodate {a w r F : ℝ} (hr : 0 < r) (hB : 0 < a - w - 2 * r)
    (hD1 : edProfE a w r (edKB a w r) < F) (hD2 : F ≤ edProfE a w r ((a - w - r) / 2))
    (hgt : edKPi a w r < edKZ a w r F) :
    (∀ e, EDEntryOptimal a w r F e →
      IsEDSPNE a w r F ((a - w - r) / 2) e ∧ e ((a - w - r) / 2) = true) ∧
    ∀ k e, IsEDSPNE a w r F k e → k = (a - w - r) / 2 := by
  obtain ⟨hF, hSB, hZ, _, _⟩ := appendixB_deter_region hB hD1 hD2
  have hu : 0 < a - w - r := by linarith
  have hpi := figure_12_BB_8 (k := edKZ a w r F) hu hZ
  have hDA : edKZ a w r F * (a - w - r - edKZ a w r F) < (a - w - r) ^ 2 / 8 :=
    hpi.2.2.2.2 hgt
  have hSZ : (a - w - r) / 2 < edKZ a w r F := lt_trans hpi.2.1 hgt
  obtain ⟨_, hno⟩ := appendixB_deter_noEntry hr hB hD1 hD2
  have hP := (figure_12_BB_6_firstMover hr hB hF.le hSB).2.2.1
  have hS0 : (0 : ℝ) ≤ (a - w - r) / 2 := by linarith
  -- no-entry payoffs fall short of `u²/8`
  have hfalse : ∀ e, EDEntryOptimal a w r F e → ∀ k, 0 ≤ k → e k = false →
      edPayI a w r k false < (a - w - r) ^ 2 / 8 := by
    intro e he k hk hek
    have hkZ : edKZ a w r F ≤ k := by
      by_contra h
      have := (appendixB_deter_entry hB hD1 hD2 he).1 k hk (lt_of_not_ge h)
      rw [hek] at this; exact absurd this (by decide)
    exact lt_of_le_of_lt (hno k hkZ).1 hDA
  refine ⟨fun e he => ?_, fun k e hspne => ?_⟩
  · have hin : e ((a - w - r) / 2) = true :=
      (appendixB_deter_entry hB hD1 hD2 he).1 _ hS0 hSZ
    refine ⟨⟨hS0, he, fun k' hk' => ?_⟩, hin⟩
    rw [hin, hP]
    cases hek : e k'
    · exact (hfalse e he k' hk' hek).le
    · exact edPayI_true_le hr
  · obtain ⟨hk, he, hopt⟩ := hspne
    have hin : e ((a - w - r) / 2) = true :=
      (appendixB_deter_entry hB hD1 hD2 he).1 _ hS0 hSZ
    have h := hopt _ hS0
    rw [hin, hP] at h
    cases hek : e k
    · rw [hek] at h
      have := hfalse e he k hk hek; linarith
    · rw [hek, edPayI_true_eq] at h
      have h1 : edQI a w r k ≤ k := edQI_le
      have h2 := mul_nonneg hr.le (sub_nonneg.2 h1)
      have hsq : (a - w - r - 2 * edQI a w r k) ^ 2 = 0 := by
        nlinarith [sq_nonneg (a - w - r - 2 * edQI a w r k)]
      have hrk : r * (k - edQI a w r k) = 0 := by
        nlinarith [sq_nonneg (a - w - r - 2 * edQI a w r k)]
      have hq : edQI a w r k = (a - w - r) / 2 := by
        have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hsq
        linarith
      rcases mul_eq_zero.1 hrk with h' | h'
      · linarith
      · linarith

/-- Total surplus `∫₀^Q (a − x) dx − cost` when total output is `Q` and total cost is `cost`. -/
noncomputable def edSurplus (a Q cost : ℝ) : ℝ := a * Q - Q ^ 2 / 2 - cost

theorem edSurplus_eq_integral (a Q cost : ℝ) :
    edSurplus a Q cost = (∫ x in (0 : ℝ)..Q, (a - x)) - cost := by
  rw [intervalIntegral.integral_sub intervalIntegrable_const
    intervalIntegral.intervalIntegrable_id, intervalIntegral.integral_const, integral_id]
  unfold edSurplus; simp only [sub_zero, smul_eq_mul]; ring

/-- **The threat of entry raises output and welfare** (MWG, p. 427). In the deterrence region,
the deterrence output `k_Z` is at least the output `u/2` of a monopolist facing no possible
entry, and total surplus is at least as high; both strictly if `F < π_E(u/2)`. -/
theorem appendixB_deterrence_raises_output {a w r F : ℝ} (hB : 0 < a - w - 2 * r)
    (hD1 : edProfE a w r (edKB a w r) < F) (hD2 : F ≤ edProfE a w r ((a - w - r) / 2)) :
    (a - w - r) / 2 ≤ edKZ a w r F ∧
    edSurplus a ((a - w - r) / 2) ((w + r) * ((a - w - r) / 2)) ≤
      edSurplus a (edKZ a w r F) ((w + r) * edKZ a w r F) ∧
    (F < edProfE a w r ((a - w - r) / 2) → (a - w - r) / 2 < edKZ a w r F ∧
      edSurplus a ((a - w - r) / 2) ((w + r) * ((a - w - r) / 2)) <
        edSurplus a (edKZ a w r F) ((w + r) * edKZ a w r F)) := by
  obtain ⟨hF, hSB, hZ, hZB, _⟩ := appendixB_deter_region hB hD1 hD2
  have hZu : edKZ a w r F ≤ a - w - r := by unfold edKB at hZB; linarith
  have key : edSurplus a (edKZ a w r F) ((w + r) * edKZ a w r F) -
      edSurplus a ((a - w - r) / 2) ((w + r) * ((a - w - r) / 2)) =
      (edKZ a w r F - (a - w - r) / 2) * (a - w - r - (edKZ a w r F + (a - w - r) / 2) / 2) := by
    unfold edSurplus; ring
  have hp : 0 < a - w - r - (edKZ a w r F + (a - w - r) / 2) / 2 := by linarith
  refine ⟨hZ, by nlinarith [mul_nonneg (sub_nonneg.2 hZ) hp.le], fun hlt => ?_⟩
  have h := (appendixB_stage2 (k := (a - w - r) / 2) hB hF.le).2.1 hlt
  rw [edQI_of_le hSB] at h
  exact ⟨h, by nlinarith [mul_pos (sub_pos.2 h) hp]⟩

/-- **Exercise 12.BB.2** (MWG, p. 435). If, in the deterrence region, the incumbent is
indifferent between deterring entry (capacity `k_Z`, output `k_Z`, no entry) and
accommodating it (capacity and output `u/2`, E producing `u/4` and paying `F`), then total
surplus is strictly higher under deterrence. (The "discuss generally" part is verbal.) -/
theorem exercise_12_BB_2 {a w r F : ℝ} (hr : 0 < r) (hB : 0 < a - w - 2 * r)
    (hD1 : edProfE a w r (edKB a w r) < F) (hD2 : F ≤ edProfE a w r ((a - w - r) / 2))
    (hind : edPayI a w r (edKZ a w r F) false = edPayI a w r ((a - w - r) / 2) true) :
    edQI a w r ((a - w - r) / 2) = (a - w - r) / 2 ∧
    edQE a w r ((a - w - r) / 2) = (a - w - r) / 4 ∧
    edSurplus a ((a - w - r) / 2 + (a - w - r) / 4)
        ((w + r) * ((a - w - r) / 2) + (w + r) * ((a - w - r) / 4) + F) <
      edSurplus a (edKZ a w r F) ((w + r) * edKZ a w r F) := by
  obtain ⟨hF, hSB, hZ, _, _⟩ := appendixB_deter_region hB hD1 hD2
  have hu : 0 < a - w - r := by linarith
  obtain ⟨hq, hE, hP, _⟩ := figure_12_BB_6_firstMover hr hB hF.le hSB
  refine ⟨hq, hE, ?_⟩
  rw [(appendixB_deter_noEntry hr hB hD1 hD2).1, hP] at hind
  have hFz := (figure_12_BB_1_linear (a := a) (w := w) (r := r) hF.le).2.2.2.2
  have h34 : 3 * (a - w - r) / 4 < edKZ a w r F := by
    by_contra h
    have h := le_of_not_gt h
    nlinarith [mul_nonpos_of_nonpos_of_nonneg (show edKZ a w r F - 3 * (a - w - r) / 4 ≤ 0 by
      linarith) (show 0 ≤ edKZ a w r F - (a - w - r) / 4 by linarith)]
  unfold edSurplus
  nlinarith [mul_pos hu (sub_pos.2 h34), hFz, hind]

/-! ## Proved parameter instances -/

/-- Instance of the general hypotheses (`appendixB_profit_strictConcave`,
`appendixB_br_antitone`, `figure_12_BB_1`, `figure_12_BB_2`): `p(Q) = 10 − Q` is concave and
strictly decreasing on `[0, ∞)`; with `c = 2`, `b = 4` is a best response to `Q = 0` and
`b' = 3` a best response to `Q' = 2`. -/
theorem appendixB_general_instance :
    ConcaveOn ℝ (Set.Ici 0) (fun x : ℝ => 10 - x) ∧ StrictAntiOn (fun x : ℝ => 10 - x) (Set.Ici 0) ∧
    (∀ q : ℝ, 0 ≤ q → q * ((fun x : ℝ => 10 - x) (q + 0) - 2) ≤
      4 * ((fun x : ℝ => 10 - x) (4 + 0) - 2)) ∧
    ∀ q : ℝ, 0 ≤ q → q * ((fun x : ℝ => 10 - x) (q + 2) - 2) ≤
      3 * ((fun x : ℝ => 10 - x) (3 + 2) - 2) := by
  refine ⟨⟨convex_Ici 0, fun x _ y _ a b _ _ hab => ?_⟩, fun x _ y _ hxy => ?_,
    fun q _ => ?_, fun q _ => ?_⟩
  · simp only [smul_eq_mul]
    have hb' : b = 1 - a := by linarith
    subst hb'; nlinarith
  · simp only; linarith
  · nlinarith [sq_nonneg (q - 4)]
  · nlinarith [sq_nonneg (q - 3)]

/-- Instance of the linear-model standing hypotheses and of `figure_12_BB_5` (blockaded entry):
`a = 4`, `w = 0`, `r = 1`, `F = 1` (`π_E(u/2) = 9/16`). -/
theorem figure_12_BB_5_instance :
    (0 : ℝ) < 1 ∧ (0 : ℝ) < 4 - 0 - 2 * 1 ∧ edProfE 4 0 1 ((4 - 0 - 1) / 2) < 1 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  simp only [edProfE_eq, edQE, edQI, edKB]
  norm_num [min_def]

/-- Instance of `figure_12_BB_6` (entry inevitable) and `figure_12_BB_6_firstMover`: `a = 4`,
`w = 0`, `r = 1`, `F = 1/4` (`π_E(k_B) = 4/9`; `u/2 = 3/2 ≤ k_B = 5/3`). -/
theorem figure_12_BB_6_instance :
    (1 : ℝ) / 4 < edProfE 4 0 1 (edKB 4 0 1) ∧ ((4 : ℝ) - 0 - 1) / 2 ≤ edKB 4 0 1 := by
  simp only [edProfE_eq, edQE, edQI, edKB]
  norm_num [min_def]

/-- Instance of `figure_12_BB_6_rightOfB`: `a = 10`, `w = 0`, `r = 1` (`k_B = 11/3 < u/2 = 9/2`).
-/
theorem figure_12_BB_6_rightOfB_instance : edKB 10 0 1 < ((10 : ℝ) - 0 - 1) / 2 := by
  unfold edKB; norm_num

/-- Instance of the deterrence region with deterrence optimal (`figure_12_BB_7_deter`,
`appendixB_bookRule_no_spne`, `appendixB_deterrence_raises_output` including its strict part,
`appendixB_linear_S_le_Z`): `a = 4`, `w = 0`, `r = 1`, `F = 49/100`, so `k_Z = 8/5`,
`π_E(k_B) = 4/9 < F < π_E(u/2) = 9/16` and `k_Z < k_π = 3(2 + √2)/4`. -/
theorem figure_12_BB_7_deter_instance :
    edProfE 4 0 1 (edKB 4 0 1) < 49 / 100 ∧ 49 / 100 < edProfE 4 0 1 ((4 - 0 - 1) / 2) ∧
    edKZ 4 0 1 (49 / 100) = 8 / 5 ∧ edKZ 4 0 1 (49 / 100) < edKPi 4 0 1 := by
  have hs : Real.sqrt (49 / 100) = 7 / 10 := by
    rw [show (49 / 100 : ℝ) = (7 / 10) ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
  have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have h20 := Real.sqrt_nonneg 2
  have hZ : edKZ 4 0 1 (49 / 100) = 8 / 5 := by unfold edKZ; rw [hs]; norm_num
  refine ⟨?_, ?_, hZ, ?_⟩
  · simp only [edProfE_eq, edQE, edQI, edKB]; norm_num [min_def]
  · simp only [edProfE_eq, edQE, edQI, edKB]; norm_num [min_def]
  · rw [hZ]; unfold edKPi; nlinarith

/-- Instance of the deterrence region with accommodation optimal
(`figure_12_BB_7_accommodate`): `a = 11/5`, `w = 0`, `r = 1`, `F = 16/2500`, so
`k_Z = 26/25`, `π_E(k_B) = 1/225 < F ≤ π_E(u/2) = 9/100` and `k_π = 3(2 + √2)/10 < k_Z`. -/
theorem figure_12_BB_7_accommodate_instance :
    edProfE (11 / 5) 0 1 (edKB (11 / 5) 0 1) < 16 / 2500 ∧
    16 / 2500 ≤ edProfE (11 / 5) 0 1 ((11 / 5 - 0 - 1) / 2) ∧
    edKPi (11 / 5) 0 1 < edKZ (11 / 5) 0 1 (16 / 2500) := by
  have hs : Real.sqrt (16 / 2500) = 2 / 25 := by
    rw [show (16 / 2500 : ℝ) = (2 / 25) ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
  have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have h20 := Real.sqrt_nonneg 2
  refine ⟨?_, ?_, ?_⟩
  · simp only [edProfE_eq, edQE, edQI, edKB]; norm_num [min_def]
  · simp only [edProfE_eq, edQE, edQI, edKB]; norm_num [min_def]
  · unfold edKPi edKZ; rw [hs]; nlinarith

/-- Instance of `exercise_12_BB_2` (indifference between deterring and accommodating):
`a = 11/5`, `w = 0`, `r = 1`, `F = (3(2 − √2)/20)²`, so `k_Z = k_π = 3(2 + √2)/10`. -/
theorem exercise_12_BB_2_instance :
    edProfE (11 / 5) 0 1 (edKB (11 / 5) 0 1) < (3 * (2 - Real.sqrt 2) / 20) ^ 2 ∧
    (3 * (2 - Real.sqrt 2) / 20) ^ 2 ≤ edProfE (11 / 5) 0 1 ((11 / 5 - 0 - 1) / 2) ∧
    edPayI (11 / 5) 0 1 (edKZ (11 / 5) 0 1 ((3 * (2 - Real.sqrt 2) / 20) ^ 2)) false =
      edPayI (11 / 5) 0 1 ((11 / 5 - 0 - 1) / 2) true := by
  have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have h20 := Real.sqrt_nonneg 2
  have hlt2 : Real.sqrt 2 < 3 / 2 := by nlinarith
  have hgt2 : 7 / 5 < Real.sqrt 2 := by nlinarith
  have hs : Real.sqrt ((3 * (2 - Real.sqrt 2) / 20) ^ 2) = 3 * (2 - Real.sqrt 2) / 20 :=
    Real.sqrt_sq (by linarith)
  have hZ : edKZ (11 / 5) 0 1 ((3 * (2 - Real.sqrt 2) / 20) ^ 2) = (6 + 3 * Real.sqrt 2) / 10 := by
    unfold edKZ; rw [hs]; ring
  refine ⟨?_, ?_, ?_⟩
  · simp only [edProfE_eq, edQE, edQI, edKB]; norm_num [min_def]; nlinarith
  · simp only [edProfE_eq, edQE, edQI, edKB]; norm_num [min_def]; nlinarith
  · rw [hZ, edPayI_false_eq, edPayI_true_eq]
    have hM : edQM (11 / 5) 0 ((6 + 3 * Real.sqrt 2) / 10) = (6 + 3 * Real.sqrt 2) / 10 :=
      min_eq_left (by linarith)
    have hI : edQI (11 / 5) 0 1 ((11 / 5 - 0 - 1) / 2) = (11 / 5 - 0 - 1) / 2 :=
      edQI_of_le (by unfold edKB; norm_num)
    rw [hM, hI]
    nlinarith

end MWG.MarketPower
