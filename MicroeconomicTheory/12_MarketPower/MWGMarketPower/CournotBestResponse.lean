/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGMarketPower.Entry
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.Sequences
import Mathlib.Topology.Order.IsLUB

/-!
# Cournot best responses with general costs

MWG, Exercise 12.C.8(a)-(f), p. 431: the homogeneous-good `J`-firm Cournot model with a
downward-sloping inverse demand `P` and an identical increasing convex cost `c`.

* `cbrProfit`, `IsBROn`: the profit `P(Q₋ⱼ + q)q − c(q)` of a firm facing rivals' aggregate
  `Q₋ⱼ`, and best responses within a strategy set `S`; `cgProfit`, `IsCournotGameNE`: the game
  among the firms of a finite set `E`; `IsCournotEqm`: every firm best-responds to its rivals'
  aggregate output.
* (a) `exercise_12_C_8a`: a firm's profit depends on the others' outputs only through `Q₋ⱼ`, so
  Nash equilibria are exactly profiles of best responses `qⱼ ∈ b(Q₋ⱼ)`.
* (b) `exercise_12_C_8b`: a strictly decreasing continuous demand and linear cost with two
  best responses to `Q₋ⱼ = 0`.
* (c) `exercise_12_C_8c`: if `Q̂₋ⱼ > Q₋ⱼ`, `q ∈ b(Q₋ⱼ)`, `q̂ ∈ b(Q̂₋ⱼ)` then
  `q̂ + Q̂₋ⱼ ≥ q + Q₋ⱼ` (revealed preference, using `P` strictly decreasing and `c` convex; the
  monotonicity of `c` is not needed). Consequences: `exercise_12_C_8c_monotone` (`b(R) + R` is
  nondecreasing along any selection), `exercise_12_C_8c_jump` (jumps are upward),
  `exercise_12_C_8c_deriv` (`b' ≥ −1` where `b` is differentiable).
* (d) As printed the existence claim is false: `exercise_12_C_8d_counterexample` has a strictly
  decreasing continuous demand and increasing linear cost with no best response at all, hence no
  equilibrium. Corrected (`exercise_12_C_8d`): with quantities in a compact interval `[0, B]` and
  `P`, `c` continuous, a symmetric pure-strategy equilibrium exists; the proof is the book's hint,
  part (c) plus a supremum argument (no fixed-point theorem).
* (e) `exercise_12_C_8e`: a kinked (concave, strictly decreasing) demand with a continuum of
  duopoly equilibria `(t, 2 − t)`, `t ∈ [1/2, 3/2]`.
* (f) `exercise_12_C_8f`: if `P` is differentiable with `P' < 0` and `c` is differentiable and
  convex, every pure equilibrium is symmetric; if in addition each firm's marginal revenue
  `P(Q) + qP'(Q)` is nonincreasing in `Q` (e.g. `P` concave), the equilibrium is unique.
  `exercise_12_C_8f_instance` verifies the hypotheses for linear demand and quadratic cost.

Departures: inverse demand `P : ℝ → ℝ` is primitive ("downward sloping" read as strictly
decreasing on `[0, ∞)`); (d) adds compactness and continuity (see `docs/corrections.md`).
-/

namespace MWG.MarketPower

open Set Filter Topology

variable {ι : Type*} [DecidableEq ι]

/-- Profit of a Cournot firm producing `y` when its rivals produce `R` in total:
`P(R + y)y − c(y)` (MWG, Exercise 12.C.8). -/
def cbrProfit (P c : ℝ → ℝ) (R y : ℝ) : ℝ := P (R + y) * y - c y

/-- `y` is a best response to the rivals' aggregate output `R` within the strategy set `S`. -/
def IsBROn (P c : ℝ → ℝ) (S : Set ℝ) (R y : ℝ) : Prop :=
  y ∈ S ∧ ∀ y' ∈ S, cbrProfit P c R y' ≤ cbrProfit P c R y

/-- Firm `j`'s profit in the Cournot game among the firms of `E` at the output profile `q`. -/
def cgProfit (P c : ℝ → ℝ) (E : Finset ι) (q : ι → ℝ) (j : ι) : ℝ :=
  P (∑ k ∈ E, q k) * q j - c (q j)

/-- A pure-strategy Nash equilibrium of the Cournot game among the firms of `E`, strategy set
`S`: no firm gains by a unilateral change of its own output. -/
def IsCournotGameNE (P c : ℝ → ℝ) (S : Set ℝ) (E : Finset ι) (q : ι → ℝ) : Prop :=
  ∀ j ∈ E, q j ∈ S ∧ ∀ y ∈ S, cgProfit P c E (Function.update q j y) j ≤ cgProfit P c E q j

/-- Every firm of `E` best-responds to its rivals' aggregate output `Q₋ⱼ`. -/
def IsCournotEqm (P c : ℝ → ℝ) (S : Set ℝ) (E : Finset ι) (q : ι → ℝ) : Prop :=
  ∀ j ∈ E, IsBROn P c S (∑ k ∈ E.erase j, q k) (q j)

/-- A firm's game profit after changing its own output to `y` depends on the others' outputs only
through their aggregate `Q₋ⱼ` (MWG, Exercise 12.C.8(a)). -/
theorem cgProfit_update (P c : ℝ → ℝ) (E : Finset ι) (q : ι → ℝ) {j : ι} (hj : j ∈ E) (y : ℝ) :
    cgProfit P c E (Function.update q j y) j = cbrProfit P c (∑ k ∈ E.erase j, q k) y := by
  unfold cgProfit cbrProfit
  rw [Finset.sum_update_of_mem hj, Finset.sdiff_singleton_eq_erase, Function.update_self,
    add_comm]

/-- **Exercise 12.C.8(a)** (MWG, p. 431). Firm `j`'s best response can be written as
`b(Q₋ⱼ)`: a profile is a Nash equilibrium of the Cournot game iff each `qⱼ` is a best response to
the rivals' aggregate output `Q₋ⱼ = ∑_{k ≠ j} q_k`. -/
theorem exercise_12_C_8a (P c : ℝ → ℝ) (S : Set ℝ) (E : Finset ι) (q : ι → ℝ) :
    IsCournotGameNE P c S E q ↔ IsCournotEqm P c S E q := by
  have hown : ∀ j ∈ E, cgProfit P c E q j = cbrProfit P c (∑ k ∈ E.erase j, q k) (q j) := by
    intro j hj
    rw [← cgProfit_update P c E q hj, Function.update_eq_self]
  constructor
  · intro h j hj
    refine ⟨(h j hj).1, fun y hy => ?_⟩
    rw [← cgProfit_update P c E q hj, ← hown j hj]
    exact (h j hj).2 y hy
  · intro h j hj
    refine ⟨(h j hj).1, fun y hy => ?_⟩
    rw [cgProfit_update P c E q hj, hown j hj]
    exact (h j hj).2 y hy

/-- The inverse demand of Exercise 12.C.8(b): `3 − Q` up to `Q = 1`, then `1 + 1/Q`. -/
noncomputable def cbrDemandB (Q : ℝ) : ℝ := if Q ≤ 1 then 3 - Q else 1 + 1 / Q

/-- **Exercise 12.C.8(b)** (MWG, p. 431). The best response need not be unique: with the
strictly decreasing inverse demand `cbrDemandB` and the increasing linear (convex) cost
`c(q) = q`, both `q = 1` and `q = 2` are best responses to `Q₋ⱼ = 0` (indeed every `q ≥ 1` is). -/
theorem exercise_12_C_8b :
    StrictAnti cbrDemandB ∧ StrictMono (fun y : ℝ => y) ∧ ConvexOn ℝ (Ici 0) (fun y : ℝ => y) ∧
    IsBROn cbrDemandB (fun y => y) (Ici 0) 0 1 ∧ IsBROn cbrDemandB (fun y => y) (Ici 0) 0 2 := by
  have hprof : ∀ y : ℝ, 0 ≤ y → cbrProfit cbrDemandB (fun y => y) 0 y ≤ 1 := by
    intro y hy
    unfold cbrProfit cbrDemandB
    rw [zero_add]
    split_ifs with h
    · nlinarith [sq_nonneg (y - 1)]
    · have hy1 : (1 : ℝ) < y := lt_of_not_ge h
      field_simp
      linarith
  have h1 : cbrProfit cbrDemandB (fun y => y) 0 1 = 1 := by
    unfold cbrProfit cbrDemandB; norm_num
  have h2 : cbrProfit cbrDemandB (fun y => y) 0 2 = 1 := by
    unfold cbrProfit cbrDemandB; norm_num
  refine ⟨fun x y hxy => ?_, strictMono_id, convexOn_id (convex_Ici 0),
    ⟨mem_Ici.2 zero_le_one, fun y hy => by rw [h1]; exact hprof y hy⟩,
    ⟨mem_Ici.2 zero_le_two, fun y hy => by rw [h2]; exact hprof y hy⟩⟩
  unfold cbrDemandB
  split_ifs with hy hx hx
  · linarith
  · exact absurd (hxy.le.trans hy) hx
  · have hx1 : (1 : ℝ) < y := lt_of_not_ge hy
    have : 1 / y < 1 := (div_lt_one (by linarith)).2 hx1
    linarith
  · have hx1 : (1 : ℝ) < x := lt_of_not_ge hx
    have : 1 / y < 1 / x := one_div_lt_one_div_of_lt (by linarith) hxy
    linarith

/-- For a convex `c` on `[0, ∞)`, moving two points inwards keeping their sum fixed lowers
`c(x) + c(y)`: `c(x) + c(a + b − x) ≤ c(a) + c(b)` for `0 ≤ a ≤ x ≤ b`. -/
theorem cbr_convex_pair {c : ℝ → ℝ} (hc : ConvexOn ℝ (Ici 0) c) {a b x : ℝ} (ha : 0 ≤ a)
    (hax : a ≤ x) (hxb : x ≤ b) : c x + c (a + b - x) ≤ c a + c b := by
  rcases eq_or_lt_of_le (hax.trans hxb) with hab | hab
  · have h1 : x = a := le_antisymm (hab ▸ hxb) hax
    rw [h1, show a + b - a = b by ring]
  · set t := (b - x) / (b - a) with ht
    have hba : 0 < b - a := by linarith
    have ht0 : 0 ≤ t := div_nonneg (by linarith) hba.le
    have ht1 : 0 ≤ 1 - t := by
      rw [ht, sub_nonneg, div_le_one hba]; linarith
    have e1 : x = t * a + (1 - t) * b := by rw [ht]; field_simp; ring
    have e2 : a + b - x = (1 - t) * a + t * b := by rw [ht]; field_simp; ring
    have hb0 : (b : ℝ) ∈ Ici (0 : ℝ) := mem_Ici.2 (by linarith)
    have i1 := hc.2 (mem_Ici.2 ha) hb0 ht0 ht1 (by ring)
    have i2 := hc.2 (mem_Ici.2 ha) hb0 ht1 ht0 (by ring)
    simp only [smul_eq_mul] at i1 i2
    calc c x + c (a + b - x) = c (t * a + (1 - t) * b) + c ((1 - t) * a + t * b) := by
          rw [← e1, ← e2]
      _ ≤ _ := by linarith

/-- **Exercise 12.C.8(c)** (MWG, p. 431). If `Q̂₋ⱼ > Q₋ⱼ ≥ 0`, `q ∈ b(Q₋ⱼ)` and
`q̂ ∈ b(Q̂₋ⱼ)`, then `q̂ + Q̂₋ⱼ ≥ q + Q₋ⱼ`. Here `P` is strictly decreasing and `c` convex on
`[0, ∞)`, and the strategy set `S ⊆ [0, ∞)` is an interval (`[0, ∞)` in the book). -/
theorem exercise_12_C_8c {P c : ℝ → ℝ} {S : Set ℝ} (hP : StrictAntiOn P (Ici 0))
    (hc : ConvexOn ℝ (Ici 0) c) (hS : S.OrdConnected) (hS0 : S ⊆ Ici 0)
    {R R' y y' : ℝ} (hR : 0 ≤ R) (hRR : R < R') (hy : IsBROn P c S R y)
    (hy' : IsBROn P c S R' y') : y + R ≤ y' + R' := by
  by_contra hlt
  push Not at hlt
  set d := R' - R with hd
  have hd0 : 0 < d := by linarith
  have hy'0 : 0 ≤ y' := hS0 hy'.1
  have hm1 : y' + d ∈ S := hS.out hy'.1 hy.1 ⟨by linarith, by linarith⟩
  have hm2 : y - d ∈ S := hS.out hy'.1 hy.1 ⟨by linarith, by linarith⟩
  have i1 := hy.2 _ hm1
  have i2 := hy'.2 _ hm2
  unfold cbrProfit at i1 i2
  rw [show R + (y' + d) = R' + y' by rw [hd]; ring] at i1
  rw [show R' + (y - d) = R + y by rw [hd]; ring] at i2
  have hPlt : P (R + y) < P (R' + y') :=
    hP (mem_Ici.2 (by linarith)) (mem_Ici.2 (by linarith)) (by linarith)
  have hcv := cbr_convex_pair hc hy'0 (x := y' + d) (b := y) (by linarith) (by linarith)
  rw [show y' + y - (y' + d) = y - d by ring] at hcv
  nlinarith [mul_pos (sub_pos.2 hPlt) hd0]

/-- **Exercise 12.C.8(c), consequence** (MWG, p. 431). Along any selection `b` of the
best-response correspondence, `Q₋ⱼ ↦ b(Q₋ⱼ) + Q₋ⱼ` is nondecreasing. -/
theorem exercise_12_C_8c_monotone {P c : ℝ → ℝ} {S : Set ℝ} (hP : StrictAntiOn P (Ici 0))
    (hc : ConvexOn ℝ (Ici 0) c) (hS : S.OrdConnected) (hS0 : S ⊆ Ici 0) {b : ℝ → ℝ}
    (hb : ∀ R, 0 ≤ R → IsBROn P c S R (b R)) : MonotoneOn (fun R => b R + R) (Ici 0) := by
  intro R hR R' hR' hle
  rcases eq_or_lt_of_le hle with h | h
  · rw [h]
  · exact exercise_12_C_8c hP hc hS hS0 hR h (hb R hR) (hb R' hR')

/-- **Exercise 12.C.8(c), "`b` can jump only upward"** (MWG, p. 431). If a selection `b` of the
best-response correspondence has a left limit `L` and a right limit `U` at `R₀ > 0`, then
`L ≤ U`. -/
theorem exercise_12_C_8c_jump {P c : ℝ → ℝ} {S : Set ℝ} (hP : StrictAntiOn P (Ici 0))
    (hc : ConvexOn ℝ (Ici 0) c) (hS : S.OrdConnected) (hS0 : S ⊆ Ici 0) {b : ℝ → ℝ}
    (hb : ∀ R, 0 ≤ R → IsBROn P c S R (b R)) {R₀ L U : ℝ} (hR₀ : 0 < R₀)
    (hL : Tendsto b (𝓝[<] R₀) (𝓝 L)) (hU : Tendsto b (𝓝[>] R₀) (𝓝 U)) : L ≤ U := by
  have hmono := exercise_12_C_8c_monotone hP hc hS hS0 hb
  have hgL : Tendsto (fun R => b R + R) (𝓝[<] R₀) (𝓝 (L + R₀)) :=
    hL.add (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id)
  have hgU : Tendsto (fun R => b R + R) (𝓝[>] R₀) (𝓝 (U + R₀)) :=
    hU.add (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id)
  have hstep : ∀ R', R₀ < R' → L + R₀ ≤ b R' + R' := by
    intro R' hR'
    refine le_of_tendsto hgL ?_
    filter_upwards [Ioo_mem_nhdsLT hR₀] with R hR
    exact hmono (mem_Ici.2 hR.1.le) (mem_Ici.2 (by linarith)) (by linarith [hR.2])
  have : L + R₀ ≤ U + R₀ := by
    refine ge_of_tendsto hgU ?_
    filter_upwards [self_mem_nhdsWithin] with R' hR'
    exact hstep R' hR'
  linarith

/-- **Exercise 12.C.8(c), "`b'(Q₋ⱼ) ≥ −1` whenever this derivative is defined"** (MWG,
p. 431), for a selection `b` of the best-response correspondence and `Q₋ⱼ > 0`. -/
theorem exercise_12_C_8c_deriv {P c : ℝ → ℝ} {S : Set ℝ} (hP : StrictAntiOn P (Ici 0))
    (hc : ConvexOn ℝ (Ici 0) c) (hS : S.OrdConnected) (hS0 : S ⊆ Ici 0) {b : ℝ → ℝ}
    (hb : ∀ R, 0 ≤ R → IsBROn P c S R (b R)) {R₀ b' : ℝ} (hR₀ : 0 < R₀)
    (hd : HasDerivAt b b' R₀) : -1 ≤ b' := by
  have hmono := exercise_12_C_8c_monotone hP hc hS hS0 hb
  have hg : HasDerivAt (fun R => b R + R) (b' + 1) R₀ := hd.add (hasDerivAt_id R₀)
  have hsl := (hasDerivAt_iff_tendsto_slope.1 hg).mono_left
    (nhdsWithin_mono R₀ (s := Ioi R₀) (fun x hx => ne_of_gt (mem_Ioi.1 hx)))
  have : 0 ≤ b' + 1 := by
    refine ge_of_tendsto hsl ?_
    filter_upwards [self_mem_nhdsWithin] with R hR
    rw [slope_def_field]
    exact div_nonneg (sub_nonneg.2 (hmono (mem_Ici.2 hR₀.le) (mem_Ici.2 (by linarith [hR.out]))
      (le_of_lt hR))) (by linarith [hR.out])
  linarith

/-- **Exercise 12.C.8(d), the printed claim is false** (MWG, p. 431). With the strictly
decreasing, continuous, positive inverse demand `P(Q) = 1 + 1/(1 + Q)` and the increasing linear
(hence convex) cost `c(q) = q`, no output `q ≥ 0` is a best response to any `Q₋ⱼ ≥ 0` (profit
`q/(1 + Q₋ⱼ + q)` increases without attaining its supremum), so for every nonempty set of firms
there is no pure-strategy Nash equilibrium at all, symmetric or not. -/
theorem exercise_12_C_8d_counterexample :
    StrictAntiOn (fun Q : ℝ => 1 + 1 / (1 + Q)) (Ici 0) ∧ Continuous (fun y : ℝ => y) ∧
    StrictMono (fun y : ℝ => y) ∧ ConvexOn ℝ (Ici 0) (fun y : ℝ => y) ∧
    (∀ R y : ℝ, 0 ≤ R → ¬ IsBROn (fun Q => 1 + 1 / (1 + Q)) (fun y => y) (Ici 0) R y) ∧
    ∀ (E : Finset ι) (q : ι → ℝ), E.Nonempty →
      ¬ IsCournotEqm (fun Q => 1 + 1 / (1 + Q)) (fun y => y) (Ici 0) E q := by
  have hnobr : ∀ R y : ℝ, 0 ≤ R →
      ¬ IsBROn (fun Q => 1 + 1 / (1 + Q)) (fun y => y) (Ici 0) R y := by
    intro R y hR ⟨hy, hmax⟩
    have hy0 : 0 ≤ y := hy
    have h := hmax (y + 1) (mem_Ici.2 (by linarith))
    unfold cbrProfit at h
    have e : ∀ z : ℝ, 0 ≤ z → (1 + 1 / (1 + (R + z))) * z - z = z / (1 + (R + z)) := by
      intro z hz
      field_simp
      ring
    rw [e y hy0, e (y + 1) (by linarith), div_le_div_iff₀ (by linarith) (by linarith)] at h
    nlinarith
  refine ⟨fun x hx y hy hxy => ?_, continuous_id, strictMono_id, convexOn_id (convex_Ici 0),
    hnobr, fun E q ⟨j, hj⟩ h => ?_⟩
  · have hx0 : (0 : ℝ) ≤ x := hx
    have : 1 / (1 + y) < 1 / (1 + x) := one_div_lt_one_div_of_lt (by linarith) (by linarith)
    simp only
    linarith
  · have hR : 0 ≤ ∑ k ∈ E.erase j, q k :=
      Finset.sum_nonneg fun k hk => (h k (Finset.mem_of_mem_erase hk)).1
    exact hnobr _ _ hR (h j hj)

/-- Best responses exist on a compact interval `[0, B]` when `P` and `c` are continuous. -/
theorem cbr_exists_Icc {P c : ℝ → ℝ} {B : ℝ} (hB : 0 ≤ B) (hPc : Continuous P)
    (hcc : Continuous c) (R : ℝ) : ∃ y, IsBROn P c (Icc 0 B) R y := by
  obtain ⟨y, hy, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hB)
    (f := fun y => cbrProfit P c R y) (by unfold cbrProfit; fun_prop)
  exact ⟨y, hy, fun y' hy' => hmax hy'⟩

/-- The fixed-point step of Exercise 12.C.8(d): for `m ≥ 0` (the number `J − 1` of rivals) there
is `x ∈ [0, B]` with `x ∈ b(mx)`, where `b` is the best response on `[0, B]`. Proof: the largest
`x` with some best response to `mx` above `x` works, by part (c) and compactness. -/
theorem cbr_symmetric_fixed_point {P c : ℝ → ℝ} {B m : ℝ} (hB : 0 ≤ B) (hm : 0 ≤ m)
    (hPc : Continuous P) (hcc : Continuous c) (hP : StrictAntiOn P (Ici 0))
    (hc : ConvexOn ℝ (Ici 0) c) : ∃ x ∈ Icc 0 B, IsBROn P c (Icc 0 B) (m * x) x := by
  have hS : (Icc (0 : ℝ) B).OrdConnected := ordConnected_Icc
  have hS0 : Icc (0 : ℝ) B ⊆ Ici 0 := Icc_subset_Ici_self
  have hex := cbr_exists_Icc hB hPc hcc
  set T : Set ℝ := {x | x ∈ Icc (0 : ℝ) B ∧ ∃ y, IsBROn P c (Icc 0 B) (m * x) y ∧ x ≤ y}
    with hT
  have hT0 : (0 : ℝ) ∈ T := by
    obtain ⟨y, hy⟩ := hex (m * 0)
    exact ⟨⟨le_rfl, hB⟩, y, hy, hy.1.1⟩
  have hTb : BddAbove T := ⟨B, fun x hx => hx.1.2⟩
  set s := sSup T with hs
  have hs0 : 0 ≤ s := le_csSup hTb hT0
  obtain ⟨u, -, hu, huT⟩ := exists_seq_tendsto_sSup ⟨0, hT0⟩ hTb
  choose y hy hxy using fun n => (huT n).2
  obtain ⟨z, hz, φ, hφ, hzlim⟩ := isCompact_Icc.tendsto_subseq (fun n => (hy n).1)
  have hus : Tendsto (u ∘ φ) atTop (𝓝 s) := hu.comp hφ.tendsto_atTop
  have hsz : s ≤ z := le_of_tendsto_of_tendsto' hus hzlim (fun n => hxy (φ n))
  have hcont : Continuous (fun pr : ℝ × ℝ => cbrProfit P c (m * pr.1) pr.2) := by
    unfold cbrProfit; fun_prop
  have hzbr : IsBROn P c (Icc 0 B) (m * s) z := by
    refine ⟨hz, fun y' hy' => ?_⟩
    have h1 : Tendsto (fun n => cbrProfit P c (m * (u ∘ φ) n) y') atTop
        (𝓝 (cbrProfit P c (m * s) y')) :=
      (hcont.tendsto (s, y')).comp (hus.prodMk_nhds tendsto_const_nhds)
    have h2 : Tendsto (fun n => cbrProfit P c (m * (u ∘ φ) n) ((y ∘ φ) n)) atTop
        (𝓝 (cbrProfit P c (m * s) z)) :=
      (hcont.tendsto (s, z)).comp (hus.prodMk_nhds hzlim)
    exact le_of_tendsto_of_tendsto' h1 h2 (fun n => (hy (φ n)).2 y' hy')
  rcases eq_or_lt_of_le hsz with h | h
  · exact ⟨s, ⟨hs0, h ▸ hz.2⟩, h ▸ hzbr⟩
  · exfalso
    rcases eq_or_lt_of_le hm with hm0 | hm0
    · have hzT : z ∈ T := by
        refine ⟨hz, z, ?_, le_rfl⟩
        rw [← hm0, zero_mul] at hzbr ⊢
        exact hzbr
      linarith [le_csSup hTb hzT]
    · have hsB : s < B := lt_of_lt_of_le h hz.2
      set w := (z + m * s) / (1 + m) with hw
      have hsw : s < w := by rw [hw, lt_div_iff₀ (by linarith)]; nlinarith
      set x := min B ((s + w) / 2) with hx
      have hsx : s < x := lt_min hsB (by linarith)
      have hxw : x < w := lt_of_le_of_lt (min_le_right _ _) (by linarith)
      have hxw' : x * (1 + m) < z + m * s := by
        rw [hw, lt_div_iff₀ (by linarith)] at hxw; exact hxw
      obtain ⟨y', hy'⟩ := hex (m * x)
      have key := exercise_12_C_8c hP hc hS hS0 (by positivity) (by nlinarith) hzbr hy'
      have hxT : x ∈ T := ⟨⟨by linarith, min_le_left _ _⟩, y', hy', by nlinarith⟩
      linarith [le_csSup hTb hxT]

/-- **Exercise 12.C.8(d), corrected** (MWG, p. 431). With quantities in a compact interval
`[0, B]`, `P` continuous and strictly decreasing on `[0, ∞)` and `c` continuous and convex, the
`J`-firm Cournot game among the firms of any finite `E` has a symmetric pure-strategy Nash
equilibrium. -/
theorem exercise_12_C_8d {P c : ℝ → ℝ} {B : ℝ} (hB : 0 ≤ B) (hPc : Continuous P)
    (hcc : Continuous c) (hP : StrictAntiOn P (Ici 0)) (hc : ConvexOn ℝ (Ici 0) c)
    (E : Finset ι) : ∃ x ∈ Icc 0 B, IsCournotGameNE P c (Icc 0 B) E (fun _ => x) := by
  rcases E.eq_empty_or_nonempty with hE | hE
  · exact ⟨0, ⟨le_rfl, hB⟩, fun j hj => by simp [hE] at hj⟩
  have h1 : 1 ≤ E.card := Nat.succ_le_of_lt hE.card_pos
  have hcard : (1 : ℝ) ≤ E.card := by exact_mod_cast h1
  obtain ⟨x, hx, hbr⟩ := cbr_symmetric_fixed_point (m := (E.card : ℝ) - 1) hB (by linarith)
    hPc hcc hP hc
  refine ⟨x, hx, (exercise_12_C_8a P c _ E _).2 fun j hj => ?_⟩
  have hsum : ∑ k ∈ E.erase j, (fun _ => x) k = ((E.card : ℝ) - 1) * x := by
    rw [Finset.sum_const, Finset.card_erase_of_mem hj, nsmul_eq_mul, Nat.cast_sub h1,
      Nat.cast_one]
  rw [hsum]
  exact hbr

/-! ### Instances for parts (c) and (d) -/

/-- The best-response selection `b(R) = max(0, (2 − R)/4)` for `P(Q) = 2 − Q`, `c(q) = q²`. -/
noncomputable def cbrSelLinear (R : ℝ) : ℝ := max 0 ((2 - R) / 4)

/-- **Instance for Exercise 12.C.8(c)** (MWG, p. 431). For `P(Q) = 2 − Q` and `c(q) = q²` all
hypotheses of `exercise_12_C_8c`, `exercise_12_C_8c_jump` and `exercise_12_C_8c_deriv` hold:
`b(R) = max(0, (2 − R)/4)` is a best-response selection, differentiable at `R₀ = 1` with
`b'(1) = −1/4 ≥ −1`, and continuous there. -/
theorem exercise_12_C_8c_instance :
    StrictAntiOn (fun Q : ℝ => 2 - Q) (Ici 0) ∧ ConvexOn ℝ (Ici 0) (fun y : ℝ => y ^ 2) ∧
    (Ici (0 : ℝ)).OrdConnected ∧
    (∀ R : ℝ, 0 ≤ R → IsBROn (fun Q => 2 - Q) (fun y => y ^ 2) (Ici 0) R (cbrSelLinear R)) ∧
    HasDerivAt cbrSelLinear (-1 / 4) 1 ∧ Tendsto cbrSelLinear (𝓝[<] 1) (𝓝 (1 / 4)) ∧
    Tendsto cbrSelLinear (𝓝[>] 1) (𝓝 (1 / 4)) := by
  have hcont : Continuous cbrSelLinear := by unfold cbrSelLinear; fun_prop
  have h1 : cbrSelLinear 1 = 1 / 4 := by unfold cbrSelLinear; norm_num
  have hlim : Tendsto cbrSelLinear (𝓝 1) (𝓝 (1 / 4)) := h1 ▸ hcont.tendsto 1
  refine ⟨fun x _ y _ h => by simp only; linarith, convexOn_pow 2, ordConnected_Ici,
    fun R _ => ?_, ?_, hlim.mono_left nhdsWithin_le_nhds, hlim.mono_left nhdsWithin_le_nhds⟩
  · refine ⟨mem_Ici.2 (le_max_left _ _), fun y hy => ?_⟩
    have hy0 : (0 : ℝ) ≤ y := hy
    unfold cbrProfit cbrSelLinear
    rcases le_total R 2 with h | h
    · rw [max_eq_right (by linarith)]
      nlinarith [sq_nonneg (y - (2 - R) / 4)]
    · rw [max_eq_left (by linarith)]
      nlinarith
  · have hd : HasDerivAt (fun R : ℝ => (2 - R) / 4) (-1 / 4) 1 := by
      simpa using ((hasDerivAt_id (1 : ℝ)).const_sub 2).div_const 4
    refine hd.congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds (show (1 : ℝ) < 2 by norm_num)] with R hR
    unfold cbrSelLinear
    rw [max_eq_right (by linarith [hR.out])]

/-- **Instance for Exercise 12.C.8(d)** (MWG, p. 431). With `P(Q) = 2 − Q`, `c(q) = q²` and
quantities in `[0, 1]` every hypothesis of `exercise_12_C_8d` holds, so a symmetric equilibrium
exists for every finite set of firms. -/
theorem exercise_12_C_8d_instance (E : Finset ι) :
    Continuous (fun Q : ℝ => 2 - Q) ∧ Continuous (fun y : ℝ => y ^ 2) ∧
    StrictAntiOn (fun Q : ℝ => 2 - Q) (Ici 0) ∧ ConvexOn ℝ (Ici 0) (fun y : ℝ => y ^ 2) ∧
    ∃ x ∈ Icc (0 : ℝ) 1,
      IsCournotGameNE (fun Q => 2 - Q) (fun y => y ^ 2) (Icc 0 1) E (fun _ => x) := by
  have hP : StrictAntiOn (fun Q : ℝ => 2 - Q) (Ici 0) := fun x _ y _ h => by simp only; linarith
  exact ⟨by fun_prop, by fun_prop, hP, convexOn_pow 2,
    exercise_12_C_8d zero_le_one (by fun_prop) (by fun_prop) hP (convexOn_pow 2) E⟩

/-! ### Part (e): multiple equilibria -/

/-- The kinked inverse demand of Exercise 12.C.8(e): `P(Q) = 1 + min(2 − Q/2, 9 − 4Q)`
(concave and strictly decreasing, kinked at `Q = 2`). -/
noncomputable def cbrDemandE (Q : ℝ) : ℝ := 1 + min (2 - Q / 2) (9 - 4 * Q)

/-- With demand `cbrDemandE` and cost `c(q) = q`, any `y ∈ [1/4, 2]` is a best response to
`Q₋ⱼ = 2 − y`. -/
theorem cbrDemandE_br {R y : ℝ} (hy1 : 1 / 4 ≤ y) (hy2 : y ≤ 2) (hRy : R + y = 2) :
    IsBROn cbrDemandE (fun y => y) (Ici 0) R y := by
  refine ⟨mem_Ici.2 (by linarith), fun y' hy' => ?_⟩
  have hy'0 : (0 : ℝ) ≤ y' := hy'
  have hval : cbrProfit cbrDemandE (fun y => y) R y = y := by
    unfold cbrProfit cbrDemandE; rw [hRy]; norm_num; ring
  rw [hval]
  unfold cbrProfit cbrDemandE
  have e : (1 + min (2 - (R + y') / 2) (9 - 4 * (R + y'))) * y' - y' =
      min (2 - (R + y') / 2) (9 - 4 * (R + y')) * y' := by ring
  rw [e]
  have hR : R = 2 - y := by linarith
  subst hR
  rcases le_total y' y with h | h
  · have := mul_le_mul_of_nonneg_right
      (min_le_left (2 - (2 - y + y') / 2) (9 - 4 * (2 - y + y'))) hy'0
    nlinarith [mul_nonneg (sub_nonneg.2 h) (show (0 : ℝ) ≤ 1 - y' / 2 by linarith)]
  · have := mul_le_mul_of_nonneg_right
      (min_le_right (2 - (2 - y + y') / 2) (9 - 4 * (2 - y + y'))) hy'0
    nlinarith [mul_nonneg (sub_nonneg.2 h) (show (0 : ℝ) ≤ 4 * y' - 1 by linarith)]

/-- **Exercise 12.C.8(e)** (MWG, p. 431). Multiple equilibria are possible: with the strictly
decreasing inverse demand `cbrDemandE` and the increasing convex cost `c(q) = q`, every profile
`(t, 2 − t)` with `t ∈ [1/2, 3/2]` is a pure-strategy Nash equilibrium of the duopoly; e.g.
`(1, 1)` and `(1/2, 3/2)`. -/
theorem exercise_12_C_8e :
    StrictAnti cbrDemandE ∧ StrictMono (fun y : ℝ => y) ∧ ConvexOn ℝ (Ici 0) (fun y : ℝ => y) ∧
    (∀ t ∈ Icc (1 / 2 : ℝ) (3 / 2), IsCournotGameNE cbrDemandE (fun y => y) (Ici 0)
      (Finset.univ : Finset (Fin 2)) ![t, 2 - t]) ∧ (![1, 1] : Fin 2 → ℝ) ≠ ![1 / 2, 3 / 2] := by
  refine ⟨fun x y hxy => ?_, strictMono_id, convexOn_id (convex_Ici 0), fun t ht => ?_, ?_⟩
  · unfold cbrDemandE
    have : min (2 - y / 2) (9 - 4 * y) < min (2 - x / 2) (9 - 4 * x) :=
      lt_min (min_lt_of_left_lt (by linarith)) (min_lt_of_right_lt (by linarith))
    linarith
  · rw [exercise_12_C_8a]
    intro j _
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ j), Fin.sum_univ_two]
    fin_cases j
    · exact cbrDemandE_br (by simp; linarith [ht.1]) (by simp; linarith [ht.2]) (by simp)
    · exact cbrDemandE_br (by simp; linarith [ht.2]) (by simp; linarith [ht.1]) (by simp)
  · intro h
    have := congrFun h 0
    norm_num at this

/-! ### Part (f): uniqueness -/

/-- First-order conditions at a best response on `[0, ∞)`: `P(Q) + qP'(Q) ≤ c'(q)`, with
equality when `q > 0`, where `Q = Q₋ⱼ + q`. -/
theorem cbr_foc {P P' c c' : ℝ → ℝ} (hP : ∀ Q, HasDerivAt P (P' Q) Q)
    (hc : ∀ y, HasDerivAt c (c' y) y) {R y : ℝ} (hy : IsBROn P c (Ici 0) R y) :
    P (R + y) + y * P' (R + y) ≤ c' y ∧ (0 < y → P (R + y) + y * P' (R + y) = c' y) := by
  have hy0 : (0 : ℝ) ≤ y := hy.1
  have hg : HasDerivAt (fun t => cbrProfit P c R t) (P (R + y) + y * P' (R + y) - c' y) y := by
    have h1 : HasDerivAt (fun t => P (R + t)) (P' (R + y)) y := (hP (R + y)).comp_const_add R y
    have := (h1.mul (hasDerivAt_id' y)).sub (hc y)
    unfold cbrProfit
    convert this using 1
    ring
  constructor
  · have hsl := (hasDerivAt_iff_tendsto_slope.1 hg).mono_left
      (nhdsWithin_mono y (s := Ioi y) (fun x hx => ne_of_gt (mem_Ioi.1 hx)))
    have : P (R + y) + y * P' (R + y) - c' y ≤ 0 := by
      refine le_of_tendsto hsl ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      rw [slope_def_field]
      have ht' : y < t := ht
      exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 (hy.2 t (mem_Ici.2 (by linarith))))
        (by linarith)
    linarith
  · intro hpos
    have hmax : IsLocalMax (fun t => cbrProfit P c R t) y :=
      Filter.eventually_of_mem (Ioi_mem_nhds hpos)
        (fun t ht => hy.2 t (mem_Ici.2 (le_of_lt (mem_Ioi.1 ht))))
    have := hmax.hasDerivAt_eq_zero hg
    linarith

/-- First-order conditions at a Cournot equilibrium, in terms of total output `Q = ∑ q_k`. -/
theorem cournotEqm_foc {P P' c c' : ℝ → ℝ} (hP : ∀ Q, HasDerivAt P (P' Q) Q)
    (hc : ∀ y, HasDerivAt c (c' y) y) {E : Finset ι} {q : ι → ℝ}
    (hq : IsCournotEqm P c (Ici 0) E q) {j : ι} (hj : j ∈ E) :
    0 ≤ q j ∧ P (∑ k ∈ E, q k) + q j * P' (∑ k ∈ E, q k) ≤ c' (q j) ∧
      (0 < q j → P (∑ k ∈ E, q k) + q j * P' (∑ k ∈ E, q k) = c' (q j)) := by
  have h := cbr_foc hP hc (hq j hj)
  rw [Finset.sum_erase_add E q hj] at h
  exact ⟨(hq j hj).1, h⟩

/-- **Exercise 12.C.8(f)** (MWG, p. 431). Sufficient conditions for the symmetric equilibrium
to be the only pure-strategy equilibrium. If `P` is differentiable with `P' < 0` and `c` is
differentiable with nondecreasing `c'` (convex), every pure-strategy equilibrium is symmetric;
if moreover each firm's marginal revenue `P(Q) + qP'(Q)` is nonincreasing in total output `Q`
(e.g. `P` concave), any two equilibria coincide. -/
theorem exercise_12_C_8f {P P' c c' : ℝ → ℝ} (hP : ∀ Q, HasDerivAt P (P' Q) Q)
    (hP' : ∀ Q, 0 ≤ Q → P' Q < 0) (hc : ∀ y, HasDerivAt c (c' y) y)
    (hc' : MonotoneOn c' (Ici 0)) (E : Finset ι) :
    (∀ q, IsCournotEqm P c (Ici 0) E q → ∀ i ∈ E, ∀ j ∈ E, q i = q j) ∧
    ((∀ y, 0 ≤ y → AntitoneOn (fun Q => P Q + y * P' Q) (Ici 0)) →
      ∀ q q', IsCournotEqm P c (Ici 0) E q → IsCournotEqm P c (Ici 0) E q' →
        ∀ i ∈ E, q i = q' i) := by
  have hQ0 : ∀ q, IsCournotEqm P c (Ici 0) E q → 0 ≤ ∑ k ∈ E, q k :=
    fun q hq => Finset.sum_nonneg fun k hk => (hq k hk).1
  have part1 : ∀ q, IsCournotEqm P c (Ici 0) E q → ∀ i ∈ E, ∀ j ∈ E, ¬ q i < q j := by
    intro q hq i hi j hj hlt
    obtain ⟨hi0, hfi, -⟩ := cournotEqm_foc hP hc hq hi
    obtain ⟨-, -, hfj⟩ := cournotEqm_foc hP hc hq hj
    have hneg := hP' _ (hQ0 q hq)
    have e := hfj (by linarith)
    have hc'le := hc' (mem_Ici.2 hi0) (mem_Ici.2 (by linarith)) hlt.le
    nlinarith [mul_lt_mul_of_neg_right hlt hneg]
  have hsym : ∀ q, IsCournotEqm P c (Ici 0) E q → ∀ i ∈ E, ∀ j ∈ E, q i = q j :=
    fun q hq i hi j hj => le_antisymm (not_lt.1 (part1 q hq j hj i hi))
      (not_lt.1 (part1 q hq i hi j hj))
  refine ⟨hsym, fun H => ?_⟩
  have part2 : ∀ q q', IsCournotEqm P c (Ici 0) E q → IsCournotEqm P c (Ici 0) E q' →
      ∀ i ∈ E, ¬ q i < q' i := by
    intro q q' hq hq' i hi hlt
    have hQQ : ∑ k ∈ E, q k ≤ ∑ k ∈ E, q' k := Finset.sum_le_sum fun k hk => by
      rw [hsym q hq k hk i hi, hsym q' hq' k hk i hi]; exact hlt.le
    obtain ⟨hi0, hfi, -⟩ := cournotEqm_foc hP hc hq hi
    obtain ⟨-, -, hfi'⟩ := cournotEqm_foc hP hc hq' hi
    have e' := hfi' (by linarith)
    have hneg := hP' _ (hQ0 q' hq')
    have hanti := H (q i) hi0 (mem_Ici.2 (hQ0 q hq)) (mem_Ici.2 (hQ0 q' hq')) hQQ
    simp only at hanti
    have hc'le := hc' (mem_Ici.2 hi0) (mem_Ici.2 (by linarith)) hlt.le
    nlinarith [mul_lt_mul_of_neg_right hlt hneg]
  intro q q' hq hq' i hi
  exact le_antisymm (not_lt.1 (part2 q' q hq' hq i hi)) (not_lt.1 (part2 q q' hq hq' i hi))

/-- **Instance for Exercise 12.C.8(f)** (MWG, p. 431). Linear demand `P(Q) = a − Q` and
quadratic cost `c(q) = q²/2` satisfy every hypothesis of `exercise_12_C_8f` (including the
marginal-revenue condition), so any two Cournot equilibria coincide and each is symmetric. -/
theorem exercise_12_C_8f_instance (a : ℝ) (E : Finset ι) :
    (∀ q, IsCournotEqm (fun Q => a - Q) (fun y => y ^ 2 / 2) (Ici 0) E q →
      ∀ i ∈ E, ∀ j ∈ E, q i = q j) ∧
    ∀ q q', IsCournotEqm (fun Q => a - Q) (fun y => y ^ 2 / 2) (Ici 0) E q →
      IsCournotEqm (fun Q => a - Q) (fun y => y ^ 2 / 2) (Ici 0) E q' → ∀ i ∈ E, q i = q' i := by
  have hP : ∀ Q : ℝ, HasDerivAt (fun Q : ℝ => a - Q) ((fun _ => (-1 : ℝ)) Q) Q := fun Q => by
    simpa using (hasDerivAt_id Q).const_sub a
  have hc : ∀ y : ℝ, HasDerivAt (fun y : ℝ => y ^ 2 / 2) ((fun y => y) y) y := fun y => by
    convert (hasDerivAt_pow 2 y).div_const 2 using 1
    norm_num
  have h := exercise_12_C_8f hP (fun _ _ => by norm_num) hc (fun x _ y _ h => h) E
  refine ⟨h.1, h.2 fun y _ Q _ Q' _ hQQ => ?_⟩
  simp only
  linarith

end MWG.MarketPower
