/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGGeneralEquilibriumExamples.Welfare
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-!
# The Pareto curve of an Edgeworth box (MWG Exercises 15.B.7 and 15.B.10(d), pp. 541-542)

Standing hypotheses (`ExchangeEconomy.ParetoCurveHyp`): an Edgeworth box economy with consumption
sets `ℝ²₊`, utilities continuous on `ℝ²₊`, strongly monotone and representing strictly convex
preferences, and a strictly positive total endowment `ω̄`. Write `a = u₁(0)`, `b = u₁(ω̄)`.

* **Exercise 15.B.7** (first part): the Pareto set is connected (`exercise_15_B_7_connected`).
  We prove more: consumer 1's utility is a homeomorphism from the Pareto set onto `[a, b]`
  (`exercise_15_B_7_homeomorph`). Its inverse is the *Pareto curve* `ExchangeEconomy.paretoCurve`,
  continuous on all of `ℝ` (`pc_continuous_paretoCurve`, values clamped to `[a, b]`), with every
  Pareto optimum on it (`pc_eq_paretoCurve`). The Pareto set is compact (`pc_isCompact_paretoSet`).
* **Exercise 15.B.7** (second part): with homothetic preferences as well, the Pareto set lies
  weakly on one side of the diagonal of the box (`exercise_15_B_7_homothetic`; weakly, since the
  two origins are always on the diagonal), and if a Pareto optimum other than the two origins lies
  on the diagonal, the Pareto set is the whole diagonal `{(s ω̄, (1 - s) ω̄) : s ∈ [0, 1]}`
  (`exercise_15_B_7_diagonal`, `ExchangeEconomy.diagonalAllocation`). The key step: homothetic,
  continuous, strongly monotone preferences rank `s y` against `s x` as they rank `y` against `x`
  (`pc_homothetic_le`, `pc_homothetic_lt`), so the supporting prices of one diagonal optimum
  support every diagonal allocation (`pc_diagonal_po`).
* **Exercise 15.B.10(d)**: if `(p', x')` is a Walrasian equilibrium after a transfer `z ≥ 0` to
  consumer 1 (endowments `ω₁ + z`, `ω₂ - z`, with `ω₁ ≥ 0`), then before the transfer there is a
  Walrasian equilibrium (with `p ≫ 0`) at which consumer 1's utility is no higher than at `x'`
  (`exercise_15_B_10d_lower_eqm`); hence a transfer paradox (consumer 1 strictly worse off than at
  some pre-transfer equilibrium) forces multiple equilibria before the transfer
  (`exercise_15_B_10d`). The book's graphical hint is made rigorous by a connectedness argument
  along the Pareto curve with normalized quasi-equilibrium supporting prices
  (`ExchangeEconomy.QuasiSupports`, closed graph `pc_isClosed_quasiSupports`), which are then
  shown to be strictly positive equilibrium prices (`pc_quasiSupports_pos`,
  `pc_walras_of_quasiSupports`). Departure: the hint's "even lower" level of utility is proved in
  the weak form "no higher" (`≤`). The book's "(but, be warned, not more generally)" is a remark.
* Instance: both consumers with `u = √x₁ + √x₂` and endowments `(1, 0)`, `(0, 1)` satisfy all
  hypotheses (`sqrtEconomy_hyp`, `sqrtEconomy_homothetic`); the Pareto set is the diagonal
  (`sqrtEconomy_paretoSet`); after the transfer `z = (0, 1/2)` there is an equilibrium
  (`sqrtEconomy_transfer_eqm`) to which the theorem of Exercise 15.B.10(d) applies
  (`sqrtEconomy_15_B_10d`).
-/

namespace MWG.GeneralEquilibriumExamples

open MWG.ConsumerChoice MWG.ClassicalDemand Kreps.PreferenceProperties Filter Topology

/-- **Exercise 15.B.7** (MWG, p. 541). The standing hypotheses on an Edgeworth box economy:
consumption sets `ℝ²₊`, continuous, strongly monotone utilities representing strictly convex
preferences, and a strictly positive total endowment. -/
structure ExchangeEconomy.ParetoCurveHyp (E : EdgeworthEconomy) : Prop where
  /-- Consumption sets `ℝ²₊`. -/
  X_eq : ∀ i, E.X i = nonnegOrthant 2
  /-- Utilities continuous on `ℝ²₊`. -/
  cont : ∀ i, ContinuousOn (E.u i) (nonnegOrthant 2)
  /-- Strongly monotone utilities. -/
  mono : ∀ i, UtilityStronglyMonotone (E.u i)
  /-- Strictly convex preferences. -/
  sconv : ∀ i, PrefStrictlyConvex (nonnegOrthant 2) (utilityPref (E.u i))
  /-- `ω̄ ≫ 0`. -/
  ω_pos : ∀ l, 0 < E.totalEndowment l

/-! ### General lemmas -/

/-- Shrinking a bundle a little keeps a continuous utility above `c`. -/
theorem pc_exists_shrink {L : ℕ} {u : (Fin L → ℝ) → ℝ} (hc : ContinuousOn u (nonnegOrthant L))
    {z : Fin L → ℝ} (hz : z ∈ nonnegOrthant L) {c : ℝ} (hcz : c < u z) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ c < u ((1 - t) • z) := by
  have hg : Continuous fun t : ℝ => (1 - t) • z :=
    (continuous_const.sub continuous_id).smul continuous_const
  have hmem : ∀ t ∈ Set.Icc (0 : ℝ) 1, (1 - t) • z ∈ nonnegOrthant L := by
    intro t ht l
    simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_nonneg (by linarith [ht.2]) (hz l)
  have h0 : c < u ((1 - 0 : ℝ) • z) := by simpa using hcz
  exact exists_pos_continuous_lt hc hg hmem h0

/-- Adding a nonzero bundle `z ≥ 0` strictly raises a strongly monotone utility. -/
theorem pc_lt_add {L : ℕ} {u : (Fin L → ℝ) → ℝ} (hm : UtilityStronglyMonotone u)
    {w z : Fin L → ℝ} (hw : w ∈ nonnegOrthant L) (hz : z ∈ nonnegOrthant L) (hz0 : z ≠ 0) :
    u w < u (w + z) :=
  hm.lt hw (fun l => le_add_of_nonneg_right (hz l)) fun he => hz0 (by
    have := congrArg (· - w) he
    simpa using this)

/-- `t • z ∈ ℝ^L₊` for `t ≥ 0`, `z ∈ ℝ^L₊`. -/
theorem pc_smul_mem {L : ℕ} {z : Fin L → ℝ} (hz : z ∈ nonnegOrthant L) {t : ℝ} (ht : 0 ≤ t) :
    t • z ∈ nonnegOrthant L := fun l => by
  simp only [Pi.smul_apply, smul_eq_mul]
  exact mul_nonneg ht (hz l)

variable {E : EdgeworthEconomy}

/-- Box membership in coordinates. -/
theorem pc_inBox_iff (h : E.ParetoCurveHyp) (x : Fin 2 → Fin 2 → ℝ) :
    E.InBox x ↔ x 0 ∈ nonnegOrthant 2 ∧ x 1 ∈ nonnegOrthant 2 ∧
      x 0 + x 1 = E.totalEndowment := by
  simp only [ExchangeEconomy.InBox, ExchangeEconomy.IsAllocation, h.X_eq, Fin.forall_fin_two,
    Fin.sum_univ_two, and_assoc]

/-- Box membership, entrywise. -/
theorem pc_inBox_iff' (h : E.ParetoCurveHyp) (x : Fin 2 → Fin 2 → ℝ) :
    E.InBox x ↔ (∀ i l, 0 ≤ x i l) ∧ x 0 + x 1 = E.totalEndowment := by
  rw [pc_inBox_iff h, Fin.forall_fin_two, ← and_assoc]
  rfl

/-- In the box, `x₁ ≤ ω̄`. -/
theorem pc_le_total (h : E.ParetoCurveHyp) {x : Fin 2 → Fin 2 → ℝ} (hx : E.InBox x) :
    x 0 ≤ E.totalEndowment := by
  obtain ⟨-, h1, hs⟩ := (pc_inBox_iff h x).1 hx
  intro l
  rw [← hs, Pi.add_apply]
  linarith [h1 l]

/-- `ω̄ ∈ ℝ²₊`. -/
theorem pc_total_mem (h : E.ParetoCurveHyp) : E.totalEndowment ∈ nonnegOrthant 2 :=
  fun l => (h.ω_pos l).le

/-- `0 ∈ ℝ²₊`. -/
theorem pc_zero_mem : (0 : Fin 2 → ℝ) ∈ nonnegOrthant 2 := fun _ => le_rfl

/-- Consumer 1 gains strictly from a transfer of part of consumer 1's bundle to consumer 2,
keeping consumer 1 above `c ≥ u₁(0)`; consumer 2 then gains strictly. -/
theorem pc_transfer0 (h : E.ParetoCurveHyp) {x : Fin 2 → Fin 2 → ℝ} (hx : E.InBox x) {c : ℝ}
    (hc : c < E.u 0 (x 0)) (hc0 : E.u 0 0 ≤ c) :
    ∃ x', E.InBox x' ∧ c < E.u 0 (x' 0) ∧ E.u 1 (x 1) < E.u 1 (x' 1) := by
  obtain ⟨h0, h1, hs⟩ := (pc_inBox_iff h x).1 hx
  have hne : x 0 ≠ 0 := by
    intro he
    rw [he] at hc
    linarith
  obtain ⟨t, ht0, ht1, hlt⟩ := pc_exists_shrink (h.cont 0) h0 hc
  have htz0 : t • x 0 ≠ 0 := smul_ne_zero ht0.ne' hne
  refine ⟨![(1 - t) • x 0, x 1 + t • x 0], (pc_inBox_iff h _).2 ⟨?_, ?_, ?_⟩, by simpa using hlt,
    by simpa using pc_lt_add (h.mono 1) h1 (pc_smul_mem h0 ht0.le) htz0⟩
  · simpa using pc_smul_mem h0 (by linarith)
  · intro l
    simp only [Matrix.cons_val_one]
    exact add_nonneg (h1 l) (pc_smul_mem h0 ht0.le l)
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← hs]
    module

/-- Mirror image of `pc_transfer0`: part of consumer 2's bundle goes to consumer 1. -/
theorem pc_transfer1 (h : E.ParetoCurveHyp) {x : Fin 2 → Fin 2 → ℝ} (hx : E.InBox x) {c : ℝ}
    (hc : c < E.u 1 (x 1)) (hc0 : E.u 1 0 ≤ c) :
    ∃ x', E.InBox x' ∧ E.u 0 (x 0) < E.u 0 (x' 0) ∧ c < E.u 1 (x' 1) := by
  obtain ⟨h0, h1, hs⟩ := (pc_inBox_iff h x).1 hx
  have hne : x 1 ≠ 0 := by
    intro he
    rw [he] at hc
    linarith
  obtain ⟨t, ht0, ht1, hlt⟩ := pc_exists_shrink (h.cont 1) h1 hc
  have htz0 : t • x 1 ≠ 0 := smul_ne_zero ht0.ne' hne
  refine ⟨![x 0 + t • x 1, (1 - t) • x 1], (pc_inBox_iff h _).2 ⟨?_, ?_, ?_⟩,
    by simpa using pc_lt_add (h.mono 0) h0 (pc_smul_mem h1 ht0.le) htz0, by simpa using hlt⟩
  · intro l
    simp only [Matrix.cons_val_zero, Pi.add_apply]
    exact add_nonneg (h0 l) (pc_smul_mem h1 ht0.le l)
  · simpa using pc_smul_mem h1 (by linarith)
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← hs]
    module

/-- Pareto optimality equals weak Pareto optimality (no allocation in the box makes both
consumers strictly better off). -/
theorem pc_isParetoOptimal_iff (h : E.ParetoCurveHyp) (x : Fin 2 → Fin 2 → ℝ) :
    E.IsParetoOptimal x ↔ E.InBox x ∧
      ∀ x', E.InBox x' → ¬ (E.u 0 (x 0) < E.u 0 (x' 0) ∧ E.u 1 (x 1) < E.u 1 (x' 1)) := by
  constructor
  · rintro ⟨hb, hno⟩
    refine ⟨hb, fun x' hx' ⟨h0, h1⟩ => hno ⟨x', hx', ?_, 0, h0⟩⟩
    rw [Fin.forall_fin_two]
    exact ⟨h0.le, h1.le⟩
  · rintro ⟨hb, hno⟩
    refine ⟨hb, ?_⟩
    rintro ⟨x', hx', hle, i, hi⟩
    rw [Fin.forall_fin_two] at hle
    obtain ⟨hm0, hm1, -⟩ := (pc_inBox_iff h x).1 hb
    have hge0 : E.u 0 0 ≤ E.u 0 (x 0) := (h.mono 0).le pc_zero_mem hm0
    have hge1 : E.u 1 0 ≤ E.u 1 (x 1) := (h.mono 1).le pc_zero_mem hm1
    have hcases : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    rcases hcases with rfl | rfl
    · obtain ⟨x'', hx'', h0, h1⟩ := pc_transfer0 h hx' hi hge0
      exact hno x'' hx'' ⟨h0, lt_of_le_of_lt hle.2 h1⟩
    · obtain ⟨x'', hx'', h0, h1⟩ := pc_transfer1 h hx' hi hge1
      exact hno x'' hx'' ⟨lt_of_le_of_lt hle.1 h0, h1⟩

/-- Every Pareto optimum gives consumer 1 a utility in `[u₁(0), u₁(ω̄)]`. -/
theorem pc_po_bounds (h : E.ParetoCurveHyp) {x : Fin 2 → Fin 2 → ℝ} (hx : E.IsParetoOptimal x) :
    E.u 0 0 ≤ E.u 0 (x 0) ∧ E.u 0 (x 0) ≤ E.u 0 E.totalEndowment := by
  obtain ⟨h0, -, -⟩ := (pc_inBox_iff h x).1 hx.1
  exact ⟨(h.mono 0).le pc_zero_mem h0, (h.mono 0).le h0 (pc_le_total h hx.1)⟩

/-- `u₁(0) ≤ u₁(ω̄)`. -/
theorem pc_a_le_b (h : E.ParetoCurveHyp) : E.u 0 0 ≤ E.u 0 E.totalEndowment :=
  (h.mono 0).le pc_zero_mem (pc_total_mem h)

/-- The set of box allocations is closed. -/
theorem pc_isClosed_box (h : E.ParetoCurveHyp) : IsClosed {x : Fin 2 → Fin 2 → ℝ | E.InBox x} := by
  simp only [pc_inBox_iff' h, Set.ofPred_and, Set.ofPred_forall]
  exact (isClosed_iInter fun i => isClosed_iInter fun l =>
    isClosed_le continuous_const (by fun_prop)).inter (isClosed_eq (by fun_prop) continuous_const)

/-- The set of box allocations is compact. -/
theorem pc_isCompact_box (h : E.ParetoCurveHyp) :
    IsCompact {x : Fin 2 → Fin 2 → ℝ | E.InBox x} := by
  refine (isCompact_Icc (a := (0 : Fin 2 → Fin 2 → ℝ))
    (b := fun _ => E.totalEndowment)).of_isClosed_subset
    (pc_isClosed_box h) fun x hx => ⟨fun i l => ?_, fun i l => ?_⟩
  · exact ((pc_inBox_iff' h x).1 hx).1 i l
  · obtain ⟨h0, h1, hs⟩ := (pc_inBox_iff h x).1 hx
    have hl := congrFun hs l
    simp only [Pi.add_apply] at hl
    fin_cases i
    · simp only [Fin.zero_eta]
      linarith [h1 l]
    · simp only [Fin.mk_one]
      linarith [h0 l]

/-- `x ↦ u₁(x₁)` is continuous on the box. -/
theorem pc_continuousOn_u (h : E.ParetoCurveHyp) (i : Fin 2) :
    ContinuousOn (fun x : Fin 2 → Fin 2 → ℝ => E.u i (x i)) {x | E.InBox x} :=
  (h.cont i).comp (continuous_apply i).continuousOn fun x hx => by
    rw [← h.X_eq i]
    exact hx.1 i

/-! ### Exercise 15.B.7: the Pareto set is the graph of a homeomorphism onto `[a, b]` -/

/-- **Exercise 15.B.7** (MWG, p. 541). The Pareto set is closed. -/
theorem pc_isClosed_paretoSet (h : E.ParetoCurveHyp) : IsClosed E.paretoSet := by
  set B := {x : Fin 2 → Fin 2 → ℝ | E.InBox x}
  have hS : E.paretoSet = B ∩ ⋂ x' ∈ B,
      ((B ∩ (fun x : Fin 2 → Fin 2 → ℝ => E.u 0 (x 0)) ⁻¹' Set.Ici (E.u 0 (x' 0))) ∪
        (B ∩ (fun x : Fin 2 → Fin 2 → ℝ => E.u 1 (x 1)) ⁻¹' Set.Ici (E.u 1 (x' 1)))) := by
    ext x
    simp only [ExchangeEconomy.paretoSet, Set.mem_ofPred_eq, pc_isParetoOptimal_iff h,
      Set.mem_inter_iff, Set.mem_iInter, Set.mem_union, Set.mem_preimage, Set.mem_Ici, B,
      not_and_or, not_lt]
    constructor
    · rintro ⟨hb, hno⟩
      exact ⟨hb, fun x' hx' => (hno x' hx').imp (fun h' => ⟨hb, h'⟩) fun h' => ⟨hb, h'⟩⟩
    · rintro ⟨hb, hno⟩
      exact ⟨hb, fun x' hx' => (hno x' hx').imp (fun h' => h'.2) fun h' => h'.2⟩
  rw [hS]
  refine (pc_isClosed_box h).inter (isClosed_biInter fun x' _ => ?_)
  exact ((pc_continuousOn_u h 0).preimage_isClosed_of_isClosed (pc_isClosed_box h)
    isClosed_Ici).union
    ((pc_continuousOn_u h 1).preimage_isClosed_of_isClosed (pc_isClosed_box h) isClosed_Ici)

/-- **Exercise 15.B.7** (MWG, p. 541). The Pareto set is compact. -/
theorem pc_isCompact_paretoSet (h : E.ParetoCurveHyp) : IsCompact E.paretoSet :=
  (pc_isCompact_box h).of_isClosed_subset (pc_isClosed_paretoSet h) fun _ hx => hx.1

/-- **Exercise 15.B.7** (MWG, p. 541). Two Pareto optima giving consumer 1 the same utility are
equal (strict convexity: otherwise their midpoint is better for both consumers). -/
theorem pc_po_injective (h : E.ParetoCurveHyp) {x y : Fin 2 → Fin 2 → ℝ}
    (hx : E.IsParetoOptimal x) (hy : E.IsParetoOptimal y) (he : E.u 0 (x 0) = E.u 0 (y 0)) :
    x = y := by
  obtain ⟨hx0, hx1, hxs⟩ := (pc_inBox_iff h x).1 hx.1
  obtain ⟨hy0, hy1, hys⟩ := (pc_inBox_iff h y).1 hy.1
  have he1 : E.u 1 (x 1) = E.u 1 (y 1) := by
    rcases lt_trichotomy (E.u 1 (x 1)) (E.u 1 (y 1)) with hlt | heq | hgt
    · exact absurd ⟨y, hy.1, Fin.forall_fin_two.2 ⟨he.le, hlt.le⟩, 1, hlt⟩ hx.2
    · exact heq
    · exact absurd ⟨x, hx.1, Fin.forall_fin_two.2 ⟨he.ge, hgt.le⟩, 1, hgt⟩ hy.2
  have h0 : x 0 = y 0 := by
    by_contra hne
    have hne1 : x 1 ≠ y 1 := by
      intro h1
      apply hne
      have : x 0 + x 1 = y 0 + y 1 := hxs.trans hys.symm
      rw [h1] at this
      exact add_right_cancel this
    set m : Fin 2 → Fin 2 → ℝ := fun k => (1 / 2 : ℝ) • x k + (1 - 1 / 2 : ℝ) • y k with hm
    have hmm : ∀ k, x k ∈ nonnegOrthant 2 → y k ∈ nonnegOrthant 2 → m k ∈ nonnegOrthant 2 :=
      fun k hxk hyk l => by
        simp only [hm, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        nlinarith [hxk l, hyk l]
    have g0 : E.u 0 (x 0) < E.u 0 (m 0) :=
      not_le.1 (h.sconv 0 (x 0) hx0 (x 0) hx0 (y 0) hy0 le_rfl he.le hne (1 / 2) (by norm_num)
        (by norm_num)).2
    have g1 : E.u 1 (x 1) < E.u 1 (m 1) :=
      not_le.1 (h.sconv 1 (x 1) hx1 (x 1) hx1 (y 1) hy1 le_rfl he1.le hne1 (1 / 2) (by norm_num)
        (by norm_num)).2
    refine hx.2 ⟨m, (pc_inBox_iff h m).2 ⟨hmm 0 hx0 hy0, hmm 1 hx1 hy1, ?_⟩,
      Fin.forall_fin_two.2 ⟨g0.le, g1.le⟩, 0, g0⟩
    simp only [hm]
    calc (1 / 2 : ℝ) • x 0 + (1 - 1 / 2 : ℝ) • y 0 + ((1 / 2 : ℝ) • x 1 + (1 - 1 / 2 : ℝ) • y 1)
        = (1 / 2 : ℝ) • (x 0 + x 1) + (1 - 1 / 2 : ℝ) • (y 0 + y 1) := by module
      _ = E.totalEndowment := by rw [hxs, hys]; module
  funext i
  fin_cases i
  · exact h0
  · simp only [Fin.mk_one]
    have : x 0 + x 1 = y 0 + y 1 := hxs.trans hys.symm
    rw [h0] at this
    exact add_left_cancel this

/-- **Exercise 15.B.7** (MWG, p. 541). For every `v ∈ [u₁(0), u₁(ω̄)]` there is a Pareto optimum
giving consumer 1 utility exactly `v`: maximise consumer 2's utility over the compact set of box
allocations giving consumer 1 at least `v`. -/
theorem pc_exists_po (h : E.ParetoCurveHyp) {v : ℝ} (hva : E.u 0 0 ≤ v)
    (hvb : v ≤ E.u 0 E.totalEndowment) : ∃ x, E.IsParetoOptimal x ∧ E.u 0 (x 0) = v := by
  set B := {x : Fin 2 → Fin 2 → ℝ | E.InBox x}
  set C := B ∩ (fun x : Fin 2 → Fin 2 → ℝ => E.u 0 (x 0)) ⁻¹' Set.Ici v with hC
  have hCc : IsCompact C := (pc_isCompact_box h).of_isClosed_subset
    ((pc_continuousOn_u h 0).preimage_isClosed_of_isClosed (pc_isClosed_box h) isClosed_Ici)
    Set.inter_subset_left
  have hCne : C.Nonempty := by
    refine ⟨![E.totalEndowment, 0], (pc_inBox_iff h _).2 ⟨?_, ?_, ?_⟩, ?_⟩
    · simpa using pc_total_mem h
    · simpa using pc_zero_mem
    · simp
    · simpa using hvb
  obtain ⟨xs, hxs, hmax⟩ := hCc.exists_isMaxOn hCne ((pc_continuousOn_u h 1).mono
    Set.inter_subset_left)
  rw [isMaxOn_iff] at hmax
  have hxsv : E.u 0 (xs 0) = v := by
    refine le_antisymm (not_lt.1 fun hlt => ?_) hxs.2
    obtain ⟨x'', hx'', h0, h1⟩ := pc_transfer0 h hxs.1 hlt hva
    exact absurd (hmax x'' ⟨hx'', h0.le⟩) (not_le.2 h1)
  refine ⟨xs, (pc_isParetoOptimal_iff h xs).2 ⟨hxs.1, fun x' hx' ⟨h0, h1⟩ => ?_⟩, hxsv⟩
  exact absurd (hmax x' ⟨hx', by rw [← hxsv] at *; exact h0.le⟩) (not_le.2 h1)

/-- **Exercise 15.B.7** (MWG, p. 541). The Pareto curve: the Pareto optimum giving consumer 1 the
utility `v` clamped to `[u₁(0), u₁(ω̄)]` (and `0` if there is none, which does not happen under
`ParetoCurveHyp`). -/
noncomputable def ExchangeEconomy.paretoCurve (E : EdgeworthEconomy) (v : ℝ) :
    Fin 2 → Fin 2 → ℝ := by
  classical
  exact if hx : ∃ x, E.IsParetoOptimal x ∧
      E.u 0 (x 0) = max (E.u 0 0) (min (E.u 0 E.totalEndowment) v) then hx.choose else 0

/-- **Exercise 15.B.7** (MWG, p. 541). The Pareto curve at `v` is Pareto optimal and gives
consumer 1 utility `v` clamped to `[u₁(0), u₁(ω̄)]`. -/
theorem pc_paretoCurve_spec (h : E.ParetoCurveHyp) (v : ℝ) :
    E.IsParetoOptimal (E.paretoCurve v) ∧
      E.u 0 (E.paretoCurve v 0) = max (E.u 0 0) (min (E.u 0 E.totalEndowment) v) := by
  have hab := pc_a_le_b h
  have hex := pc_exists_po h (v := max (E.u 0 0) (min (E.u 0 E.totalEndowment) v))
    (le_max_left _ _) (max_le hab (min_le_left _ _))
  unfold ExchangeEconomy.paretoCurve
  split_ifs with hc
  · exact hc.choose_spec
  · exact absurd hex hc

/-- **Exercise 15.B.7** (MWG, p. 541). For `v ∈ [u₁(0), u₁(ω̄)]` the Pareto curve gives
consumer 1 utility exactly `v`. -/
theorem pc_paretoCurve_u (h : E.ParetoCurveHyp) {v : ℝ}
    (hv : v ∈ Set.Icc (E.u 0 0) (E.u 0 E.totalEndowment)) : E.u 0 (E.paretoCurve v 0) = v := by
  rw [(pc_paretoCurve_spec h v).2, min_eq_right hv.2, max_eq_right hv.1]

/-- **Exercise 15.B.7** (MWG, p. 541). Every Pareto optimum lies on the Pareto curve. -/
theorem pc_eq_paretoCurve (h : E.ParetoCurveHyp) {x : Fin 2 → Fin 2 → ℝ}
    (hx : E.IsParetoOptimal x) : x = E.paretoCurve (E.u 0 (x 0)) :=
  pc_po_injective h hx (pc_paretoCurve_spec h _).1
    (pc_paretoCurve_u h (pc_po_bounds h hx)).symm

/-- **Exercise 15.B.7** (MWG, p. 541). Consumer 1's utility is a homeomorphism from the Pareto set
onto `[u₁(0), u₁(ω̄)]` (a continuous bijection from a compact space onto a Hausdorff space). -/
theorem exercise_15_B_7_homeomorph (h : E.ParetoCurveHyp) :
    ∃ g : E.paretoSet ≃ₜ Set.Icc (E.u 0 0) (E.u 0 E.totalEndowment),
      ∀ x, (g x : ℝ) = E.u 0 (x.1 0) := by
  have : CompactSpace E.paretoSet := isCompact_iff_compactSpace.mp (pc_isCompact_paretoSet h)
  let f : E.paretoSet → Set.Icc (E.u 0 0) (E.u 0 E.totalEndowment) :=
    fun x => ⟨E.u 0 (x.1 0), pc_po_bounds h x.2⟩
  have hfc : Continuous f := by
    refine Continuous.subtype_mk ((h.cont 0).comp_continuous
      ((continuous_apply 0).comp continuous_subtype_val) fun x => ?_) _
    have := ((pc_inBox_iff h x.1).1 x.2.1).1
    exact this
  have hbij : Function.Bijective f := by
    refine ⟨fun x y hxy => Subtype.ext (pc_po_injective h x.2 y.2 (congrArg Subtype.val hxy)),
      fun w => ?_⟩
    obtain ⟨x, hx, hxv⟩ := pc_exists_po h w.2.1 w.2.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxv⟩
  exact ⟨Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f hbij) hfc, fun _ => rfl⟩

/-- **Exercise 15.B.7** (MWG, p. 541). The Pareto curve is continuous (it is the inverse of the
homeomorphism `exercise_15_B_7_homeomorph`, composed with the clamp onto `[u₁(0), u₁(ω̄)]`). -/
theorem pc_continuous_paretoCurve (h : E.ParetoCurveHyp) : Continuous E.paretoCurve := by
  obtain ⟨g, hg⟩ := exercise_15_B_7_homeomorph h
  have hab := pc_a_le_b h
  have key : E.paretoCurve = fun v => (g.symm (Set.projIcc _ _ hab v)).1 := by
    funext v
    set w := g.symm (Set.projIcc _ _ hab v)
    have hw : (g w : ℝ) = max (E.u 0 0) (min (E.u 0 E.totalEndowment) v) := by
      rw [g.apply_symm_apply, Set.coe_projIcc]
    rw [hg] at hw
    exact pc_po_injective h (pc_paretoCurve_spec h v).1 w.2
      (by rw [(pc_paretoCurve_spec h v).2, hw])
  rw [key]
  exact continuous_subtype_val.comp (g.symm.continuous.comp continuous_projIcc)

/-- **Exercise 15.B.7** (MWG, p. 541). The Pareto set is the image of `[u₁(0), u₁(ω̄)]` under the
Pareto curve. -/
theorem pc_paretoSet_eq_image (h : E.ParetoCurveHyp) :
    E.paretoSet = E.paretoCurve '' Set.Icc (E.u 0 0) (E.u 0 E.totalEndowment) := by
  ext x
  constructor
  · intro hx
    exact ⟨_, pc_po_bounds h hx, (pc_eq_paretoCurve h hx).symm⟩
  · rintro ⟨v, -, rfl⟩
    exact (pc_paretoCurve_spec h v).1

/-- **Exercise 15.B.7** (MWG, p. 541), first part. With continuous, strongly monotone and strictly
convex preferences (and `ω̄ ≫ 0`) the Pareto set has no "holes": it is connected. -/
theorem exercise_15_B_7_connected (h : E.ParetoCurveHyp) : IsConnected E.paretoSet := by
  rw [pc_paretoSet_eq_image h]
  exact (isConnected_Icc (pc_a_le_b h)).image _ (pc_continuous_paretoCurve h).continuousOn

/-! ### Exercise 15.B.7, second part: homothetic preferences -/

/-- A homothetic (Definition 3.B.6), continuous and strongly monotone utility preserves weak
rankings under scaling: `u(y) ≤ u(x)` implies `u(s y) ≤ u(s x)` for `s ≥ 0`. (If `u(y) < u(x)`,
`y` is indifferent to a point `t x`, `t ∈ [0, 1]`, of the ray through `x`.) -/
theorem pc_homothetic_le {L : ℕ} {u : (Fin L → ℝ) → ℝ} (hc : ContinuousOn u (nonnegOrthant L))
    (hm : UtilityStronglyMonotone u) (hh : Homothetic (nonnegOrthant L) (utilityPref u))
    {x y : Fin L → ℝ} (hx : x ∈ nonnegOrthant L) (hy : y ∈ nonnegOrthant L) (hxy : u y ≤ u x)
    {s : ℝ} (hs : 0 ≤ s) : u (s • y) ≤ u (s • x) := by
  rcases hxy.lt_or_eq with hlt | heq
  · have hcf : ContinuousOn (fun t : ℝ => u (t • x)) (Set.Icc 0 1) :=
      hc.comp (continuous_id.smul continuous_const).continuousOn fun t ht => pc_smul_mem hx ht.1
    have h0 : u ((0 : ℝ) • x) ≤ u y := by
      rw [zero_smul]
      exact hm.le (fun _ => le_rfl) fun l => hy l
    obtain ⟨t, ht, hty⟩ := intermediate_value_Icc zero_le_one hcf
      ⟨h0, by rw [one_smul]; exact hlt.le⟩
    have htx : t • x ∈ nonnegOrthant L := pc_smul_mem hx ht.1
    have hind := (hh (t • x) htx y hy ⟨hty.ge, hty.le⟩ s hs).1
    refine le_trans hind (hm.le (pc_smul_mem htx hs) fun l => ?_)
    simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (hx l) ht.2) hs
  · exact (hh x hx y hy ⟨heq.le, heq.ge⟩ s hs).1

/-- Strict form of `pc_homothetic_le`: `u(y) < u(x)` implies `u(s y) < u(s x)` for `s > 0`. -/
theorem pc_homothetic_lt {L : ℕ} {u : (Fin L → ℝ) → ℝ} (hc : ContinuousOn u (nonnegOrthant L))
    (hm : UtilityStronglyMonotone u) (hh : Homothetic (nonnegOrthant L) (utilityPref u))
    {x y : Fin L → ℝ} (hx : x ∈ nonnegOrthant L) (hy : y ∈ nonnegOrthant L) (hxy : u y < u x)
    {s : ℝ} (hs : 0 < s) : u (s • y) < u (s • x) := by
  by_contra hle
  rw [not_lt] at hle
  have := pc_homothetic_le hc hm hh (pc_smul_mem hy hs.le) (pc_smul_mem hx hs.le) hle
    (inv_nonneg.2 hs.le)
  rw [inv_smul_smul₀ hs.ne', inv_smul_smul₀ hs.ne'] at this
  linarith

/-- With homothetic preferences, if `t c` (`t > 0`) is optimal in the budget set
`{y ≥ 0 : p·y ≤ p·(t c)}`, then `s c` is optimal in `{y ≥ 0 : p·y ≤ p·(s c)}` for every
`s ≥ 0`. -/
theorem pc_scaled_support {L : ℕ} {u : (Fin L → ℝ) → ℝ} (hc : ContinuousOn u (nonnegOrthant L))
    (hm : UtilityStronglyMonotone u) (hh : Homothetic (nonnegOrthant L) (utilityPref u))
    {p c : Fin L → ℝ} (hp : StrictlyPositive p) (hcm : c ∈ nonnegOrthant L) {t : ℝ}
    (ht : 0 < t)
    (hmax : ∀ y ∈ nonnegOrthant L, p ⬝ᵥ y ≤ p ⬝ᵥ (t • c) → u y ≤ u (t • c)) {s : ℝ}
    (hs : 0 ≤ s) : ∀ y ∈ nonnegOrthant L, p ⬝ᵥ y ≤ p ⬝ᵥ (s • c) → u y ≤ u (s • c) := by
  intro y hy hpy
  rcases hs.lt_or_eq with hs | rfl
  · have h1 : u ((t / s) • y) ≤ u (t • c) := by
      refine hmax _ (pc_smul_mem hy (by positivity)) ?_
      rw [dotProduct_smul, smul_eq_mul, dotProduct_smul, smul_eq_mul] at *
      calc t / s * (p ⬝ᵥ y) ≤ t / s * (s * (p ⬝ᵥ c)) :=
            mul_le_mul_of_nonneg_left hpy (by positivity)
        _ = t * (p ⬝ᵥ c) := by field_simp
    have h2 := pc_homothetic_le hc hm hh (pc_smul_mem hcm ht.le) (pc_smul_mem hy (by positivity))
      h1 (s := s / t) (by positivity)
    have e1 : (s / t) • ((t / s) • y) = y := by
      rw [smul_smul, div_mul_div_comm, mul_comm s t, div_self (by positivity), one_smul]
    have e2 : (s / t) • (t • c) = s • c := by rw [smul_smul, div_mul_cancel₀ s ht.ne']
    rwa [e1, e2] at h2
  · have := eq_zero_of_dotProduct_nonpos hp hy (by simpa using hpy)
    rw [this, zero_smul]

/-- **Exercise 15.B.7** (MWG, p. 541). The allocation `(s ω̄, (1 - s) ω̄)` on the diagonal of the
Edgeworth box. -/
noncomputable def ExchangeEconomy.diagonalAllocation (E : EdgeworthEconomy) (s : ℝ) :
    Fin 2 → Fin 2 → ℝ :=
  ![s • E.totalEndowment, (1 - s) • E.totalEndowment]

/-- The diagonal allocations with `s ∈ [0, 1]` are in the box. -/
theorem pc_diagonal_inBox (h : E.ParetoCurveHyp) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    E.InBox (E.diagonalAllocation s) := by
  refine (pc_inBox_iff h _).2 ⟨?_, ?_, ?_⟩
  · simpa [ExchangeEconomy.diagonalAllocation] using pc_smul_mem (pc_total_mem h) hs.1
  · simpa [ExchangeEconomy.diagonalAllocation] using
      pc_smul_mem (pc_total_mem h) (sub_nonneg.2 hs.2)
  · simp only [ExchangeEconomy.diagonalAllocation, Matrix.cons_val_zero, Matrix.cons_val_one]
    module

/-- **Exercise 15.B.7** (MWG, p. 541). With homothetic preferences, if a Pareto optimum `z` has
`z₁ = t ω̄` with `0 < t < 1`, then every diagonal allocation `(s ω̄, (1 - s) ω̄)`, `s ∈ [0, 1]`,
is Pareto optimal: the supporting prices of `z` (second welfare theorem) support every diagonal
allocation, by homotheticity. -/
theorem pc_diagonal_po (h : E.ParetoCurveHyp)
    (hom : ∀ i, Homothetic (nonnegOrthant 2) (utilityPref (E.u i)))
    {z : Fin 2 → Fin 2 → ℝ} (hz : E.IsParetoOptimal z) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hzt : z 0 = t • E.totalEndowment) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    E.IsParetoOptimal (E.diagonalAllocation s) := by
  obtain ⟨p, hp, hT⟩ := second_welfare_theorem two_pos h.X_eq h.cont
    (fun i => (h.sconv i).prefConvex (convex_nonnegOrthant 2)) h.mono h.ω_pos hz
  have hsup : ∀ i, ∀ y ∈ nonnegOrthant 2, p ⬝ᵥ y ≤ p ⬝ᵥ z i → E.u i y ≤ E.u i (z i) := by
    intro i y hy hpy
    exact hT.2.2 i y (by rw [h.X_eq i]; exact hy) (by beta_reduce; linarith)
  have hz1 : z 1 = (1 - t) • E.totalEndowment := by
    obtain ⟨-, -, hsum⟩ := (pc_inBox_iff h z).1 hz.1
    have : z 1 = E.totalEndowment - z 0 := by rw [← hsum]; abel
    rw [this, hzt]
    module
  have h0 := pc_scaled_support (h.cont 0) (h.mono 0) (hom 0) hp (pc_total_mem h) ht0
    (by rw [← hzt]; exact hsup 0) hs.1
  have h1 := pc_scaled_support (h.cont 1) (h.mono 1) (hom 1) hp (pc_total_mem h)
    (sub_pos.2 ht1) (by rw [← hz1]; exact hsup 1) (sub_nonneg.2 hs.2)
  refine (pc_isParetoOptimal_iff h _).2 ⟨pc_diagonal_inBox h hs, fun x' hx' ⟨g0, g1⟩ => ?_⟩
  simp only [ExchangeEconomy.diagonalAllocation, Matrix.cons_val_zero, Matrix.cons_val_one] at g0 g1
  obtain ⟨m0, m1, hsum⟩ := (pc_inBox_iff h x').1 hx'
  have c0 : p ⬝ᵥ (s • E.totalEndowment) < p ⬝ᵥ x' 0 := by
    by_contra hc
    exact absurd (h0 _ m0 (not_lt.1 hc)) (not_le.2 g0)
  have c1 : p ⬝ᵥ ((1 - s) • E.totalEndowment) < p ⬝ᵥ x' 1 := by
    by_contra hc
    exact absurd (h1 _ m1 (not_lt.1 hc)) (not_le.2 g1)
  have hadd : p ⬝ᵥ (x' 0 + x' 1) =
      p ⬝ᵥ (s • E.totalEndowment) + p ⬝ᵥ ((1 - s) • E.totalEndowment) := by
    rw [hsum, ← dotProduct_add]
    congr 1
    module
  rw [dotProduct_add] at hadd
  linarith

/-- **Exercise 15.B.7** (MWG, p. 541) and the claim of p. 533. With homothetic preferences (as
well as continuous, strongly monotone and strictly convex ones, and `ω̄ ≫ 0`), if some Pareto
optimum `z` other than the two origins lies on the diagonal of the box, then the Pareto set is the
whole diagonal `{(s ω̄, (1 - s) ω̄) : s ∈ [0, 1]}`. -/
theorem exercise_15_B_7_diagonal (h : E.ParetoCurveHyp)
    (hom : ∀ i, Homothetic (nonnegOrthant 2) (utilityPref (E.u i)))
    {z : Fin 2 → Fin 2 → ℝ} (hz : E.IsParetoOptimal z) (hz0 : z 0 ≠ 0)
    (hzw : z 0 ≠ E.totalEndowment)
    (hdiag : z 0 0 * E.totalEndowment 1 = z 0 1 * E.totalEndowment 0) :
    E.paretoSet = E.diagonalAllocation '' Set.Icc 0 1 := by
  have hw0 := h.ω_pos 0
  have hzm := ((pc_inBox_iff h z).1 hz.1).1
  set t := z 0 0 / E.totalEndowment 0 with ht
  have hzt : z 0 = t • E.totalEndowment := by
    funext l
    fin_cases l
    · simp only [Fin.zero_eta, Pi.smul_apply, smul_eq_mul, ht]
      field_simp
    · simp only [Fin.mk_one, Pi.smul_apply, smul_eq_mul, ht]
      field_simp
      linarith
  have ht0 : 0 < t := by
    rcases (show (0 : ℝ) ≤ t from div_nonneg (hzm 0) hw0.le).lt_or_eq with hlt | heq
    · exact hlt
    · exact absurd (by rw [hzt, ← heq, zero_smul]) hz0
  have ht1 : t < 1 := by
    have hle : t ≤ 1 := by rw [ht, div_le_one hw0]; exact pc_le_total h hz.1 0
    rcases hle.lt_or_eq with hlt | heq
    · exact hlt
    · exact absurd (by rw [hzt, heq, one_smul]) hzw
  ext x
  constructor
  · intro hx
    obtain ⟨hva, hvb⟩ := pc_po_bounds h hx
    have hcf : ContinuousOn (fun s : ℝ => E.u 0 (s • E.totalEndowment)) (Set.Icc 0 1) :=
      (h.cont 0).comp (continuous_id.smul continuous_const).continuousOn
        fun s hs => pc_smul_mem (pc_total_mem h) hs.1
    obtain ⟨s, hs, hsv⟩ := intermediate_value_Icc zero_le_one hcf
      ⟨by simpa using hva, by simpa using hvb⟩
    refine ⟨s, hs, (pc_po_injective h hx (pc_diagonal_po h hom hz ht0 ht1 hzt hs) ?_).symm⟩
    simp only [ExchangeEconomy.diagonalAllocation, Matrix.cons_val_zero]
    exact hsv.symm
  · rintro ⟨s, hs, rfl⟩
    exact pc_diagonal_po h hom hz ht0 ht1 hzt hs

/-- **Exercise 15.B.7** (MWG, p. 541), second part. If, in addition, preferences are homothetic,
the Pareto set lies (weakly) on one side of the diagonal of the box: either every Pareto optimum
`x` has `x₁₁ ω̄₂ ≤ x₂₁ ω̄₁` (consumer 1's bundle on or below the diagonal ray) or every one has
`≥`. (Weakly: the two origins are always on the diagonal, and by `exercise_15_B_7_diagonal` the
whole Pareto set may be the diagonal.) -/
theorem exercise_15_B_7_homothetic (h : E.ParetoCurveHyp)
    (hom : ∀ i, Homothetic (nonnegOrthant 2) (utilityPref (E.u i))) :
    (∀ x ∈ E.paretoSet, x 0 0 * E.totalEndowment 1 - x 0 1 * E.totalEndowment 0 ≤ 0) ∨
      (∀ x ∈ E.paretoSet, 0 ≤ x 0 0 * E.totalEndowment 1 - x 0 1 * E.totalEndowment 0) := by
  by_contra hcon
  simp only [not_or, not_forall, not_le, exists_prop] at hcon
  obtain ⟨⟨x, hx, hDx⟩, ⟨y, hy, hDy⟩⟩ := hcon
  -- a Pareto optimum off the diagonal is not at an origin
  have hint : ∀ q ∈ E.paretoSet,
      q 0 0 * E.totalEndowment 1 - q 0 1 * E.totalEndowment 0 ≠ 0 →
      E.u 0 0 < E.u 0 (q 0) ∧ E.u 0 (q 0) < E.u 0 E.totalEndowment := by
    intro q hq hD
    have hqm := ((pc_inBox_iff h q).1 hq.1).1
    refine ⟨(h.mono 0).lt pc_zero_mem (fun l => hqm l) fun he => hD ?_,
      (h.mono 0).lt hqm (pc_le_total h hq.1) fun he => hD ?_⟩
    · rw [he]
      simp
    · rw [← he]
      ring
  have hxi := hint x hx hDx.ne'
  have hyi := hint y hy hDy.ne
  set S := E.paretoCurve '' Set.uIcc (E.u 0 (y 0)) (E.u 0 (x 0)) with hS
  have hSc : IsPreconnected S :=
    isPreconnected_uIcc.image _ (pc_continuous_paretoCurve h).continuousOn
  have hxS : x ∈ S := ⟨_, Set.right_mem_uIcc, (pc_eq_paretoCurve h hx).symm⟩
  have hyS : y ∈ S := ⟨_, Set.left_mem_uIcc, (pc_eq_paretoCurve h hy).symm⟩
  have hDc : ContinuousOn
      (fun q : Fin 2 → Fin 2 → ℝ => q 0 0 * E.totalEndowment 1 - q 0 1 * E.totalEndowment 0) S :=
    (by fun_prop : Continuous fun q : Fin 2 → Fin 2 → ℝ =>
      q 0 0 * E.totalEndowment 1 - q 0 1 * E.totalEndowment 0).continuousOn
  obtain ⟨q, ⟨v, hv, rfl⟩, hq0⟩ := hSc.intermediate_value hyS hxS hDc ⟨hDy.le, hDx.le⟩
  have hva : E.u 0 0 < v ∧ v < E.u 0 E.totalEndowment := by
    rcases Set.mem_uIcc.1 hv with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨by linarith [hyi.1], by linarith [hxi.2]⟩
    · exact ⟨by linarith [hxi.1], by linarith [hyi.2]⟩
  have hu := pc_paretoCurve_u h ⟨hva.1.le, hva.2.le⟩
  have hpo := (pc_paretoCurve_spec h v).1
  have hz0 : E.paretoCurve v 0 ≠ 0 := fun he => by
    rw [he] at hu
    linarith [hva.1]
  have hzw : E.paretoCurve v 0 ≠ E.totalEndowment := fun he => by
    rw [he] at hu
    linarith [hva.2]
  have hset := exercise_15_B_7_diagonal h hom hpo hz0 hzw (by linarith)
  have hxd : x ∈ E.diagonalAllocation '' Set.Icc 0 1 := hset ▸ hx
  obtain ⟨s, -, rfl⟩ := hxd
  simp only [ExchangeEconomy.diagonalAllocation, Matrix.cons_val_zero, Pi.smul_apply,
    smul_eq_mul] at hDx
  linarith

/-! ### Exercise 15.B.10(d): a transfer paradox needs multiple equilibria -/

/-- The value of `y` at the normalized prices `(q, 1 - q)`. -/
theorem pc_dot_pair (q : ℝ) (y : Fin 2 → ℝ) : ![q, 1 - q] ⬝ᵥ y = q * y 0 + (1 - q) * y 1 := by
  simp [dotProduct, Fin.sum_univ_two]

/-- Normalizing `p` with `p₁ + p₂ > 0` to the price simplex. -/
theorem pc_normalize {p : Fin 2 → ℝ} (hp : 0 < p 0 + p 1) :
    ![p 0 / (p 0 + p 1), 1 - p 0 / (p 0 + p 1)] = (p 0 + p 1)⁻¹ • p := by
  funext l
  fin_cases l
  · simp [div_eq_inv_mul]
  · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.smul_apply,
      smul_eq_mul]
    field_simp
    ring

/-- **Exercise 15.B.10(d)** (MWG, p. 542). The normalized prices `(q, 1 - q)` support the
allocation `x` as a quasi-equilibrium: a bundle that a consumer strictly prefers to his bundle
costs at least as much. -/
def ExchangeEconomy.QuasiSupports (E : EdgeworthEconomy) (q : ℝ) (x : Fin 2 → Fin 2 → ℝ) :
    Prop :=
  ∀ i, ∀ y ∈ nonnegOrthant 2, E.u i (x i) < E.u i y → ![q, 1 - q] ⬝ᵥ x i ≤ ![q, 1 - q] ⬝ᵥ y

/-- Prices `p ≫ 0` with `p·xᵢ ≤ p·y` whenever `y` is strictly preferred give, normalized, a
quasi-equilibrium support. -/
theorem pc_quasiSupports_of_pos {p : Fin 2 → ℝ} (hp : StrictlyPositive p)
    {x : Fin 2 → Fin 2 → ℝ}
    (hx : ∀ i, ∀ y ∈ nonnegOrthant 2, E.u i (x i) < E.u i y → p ⬝ᵥ x i ≤ p ⬝ᵥ y) :
    p 0 / (p 0 + p 1) ∈ Set.Icc (0 : ℝ) 1 ∧ E.QuasiSupports (p 0 / (p 0 + p 1)) x := by
  have hs : 0 < p 0 + p 1 := add_pos (hp 0) (hp 1)
  refine ⟨⟨div_nonneg (hp 0).le hs.le, (div_le_one hs).2 (by linarith [hp 1])⟩, ?_⟩
  intro i y hy hlt
  rw [pc_normalize hs, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul]
  exact mul_le_mul_of_nonneg_left (hx i y hy hlt) (inv_nonneg.2 hs.le)

/-- The bundles on the Pareto curve lie in `ℝ²₊`. -/
theorem pc_paretoCurve_mem (h : E.ParetoCurveHyp) (v : ℝ) (i : Fin 2) :
    E.paretoCurve v i ∈ nonnegOrthant 2 := by
  rw [← h.X_eq i]
  exact (pc_paretoCurve_spec h v).1.1.1 i

/-- Consumer `i`'s utility along the Pareto curve is continuous. -/
theorem pc_continuous_u_paretoCurve (h : E.ParetoCurveHyp) (i : Fin 2) :
    Continuous fun v => E.u i (E.paretoCurve v i) :=
  (h.cont i).comp_continuous ((continuous_apply i).comp (pc_continuous_paretoCurve h))
    fun v => pc_paretoCurve_mem h v i

/-- **Exercise 15.B.10(d)** (MWG, p. 542). Every point of the Pareto curve has a
quasi-equilibrium support (second welfare theorem, normalized). -/
theorem pc_exists_quasiSupports (h : E.ParetoCurveHyp) (v : ℝ) :
    ∃ q ∈ Set.Icc (0 : ℝ) 1, E.QuasiSupports q (E.paretoCurve v) := by
  obtain ⟨p, hp, hT⟩ := second_welfare_theorem two_pos h.X_eq h.cont
    (fun i => (h.sconv i).prefConvex (convex_nonnegOrthant 2)) h.mono h.ω_pos
    (pc_paretoCurve_spec h v).1
  refine ⟨_, pc_quasiSupports_of_pos hp fun i y hy hlt => ?_⟩
  by_contra hc
  exact absurd (hT.2.2 i y (by rw [h.X_eq i]; exact hy) (by beta_reduce; linarith))
    (not_le.2 hlt)

/-- **Exercise 15.B.10(d)** (MWG, p. 542). The graph `{(v, q) : (q, 1 - q) supports the Pareto
curve at v}` is closed: a limit of supporting prices supports the limit allocation. -/
theorem pc_isClosed_quasiSupports (h : E.ParetoCurveHyp) :
    IsClosed {vq : ℝ × ℝ | E.QuasiSupports vq.2 (E.paretoCurve vq.1)} := by
  have hpc := pc_continuous_paretoCurve h
  have hS : {vq : ℝ × ℝ | E.QuasiSupports vq.2 (E.paretoCurve vq.1)} =
      ⋂ i, ⋂ y ∈ nonnegOrthant 2, ({vq : ℝ × ℝ | E.u i y ≤ E.u i (E.paretoCurve vq.1 i)} ∪
        {vq : ℝ × ℝ | vq.2 * E.paretoCurve vq.1 i 0 + (1 - vq.2) * E.paretoCurve vq.1 i 1 ≤
          vq.2 * y 0 + (1 - vq.2) * y 1}) := by
    ext vq
    simp only [ExchangeEconomy.QuasiSupports, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_union,
      pc_dot_pair]
    refine forall_congr' fun i => forall_congr' fun y => forall_congr' fun _ => ?_
    rw [imp_iff_not_or, not_lt]
  rw [hS]
  refine isClosed_iInter fun i => isClosed_biInter fun y _ => IsClosed.union ?_ ?_
  · exact isClosed_le continuous_const ((pc_continuous_u_paretoCurve h i).comp continuous_fst)
  · exact isClosed_le (by fun_prop) (by fun_prop)

/-- Projecting a closed subset of `ℝ × [0, 1]` to the first factor gives a closed set. -/
theorem pc_isClosed_exists_Icc {C : Set (ℝ × ℝ)} (hC : IsClosed C) :
    IsClosed {v : ℝ | ∃ q ∈ Set.Icc (0 : ℝ) 1, (v, q) ∈ C} := by
  have hT : IsClosed {vq : ℝ × Set.Icc (0 : ℝ) 1 | ((vq.1, (vq.2 : ℝ)) : ℝ × ℝ) ∈ C} :=
    hC.preimage (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have key : {v : ℝ | ∃ q ∈ Set.Icc (0 : ℝ) 1, (v, q) ∈ C} =
      Prod.fst '' {vq : ℝ × Set.Icc (0 : ℝ) 1 | ((vq.1, (vq.2 : ℝ)) : ℝ × ℝ) ∈ C} := by
    ext v
    constructor
    · rintro ⟨q, hq, hc⟩
      exact ⟨(v, ⟨q, hq⟩), hc, rfl⟩
    · rintro ⟨⟨v', q⟩, hc, rfl⟩
      exact ⟨q.1, q.2, hc⟩
  rw [key]
  exact isClosedMap_fst_of_compactSpace _ hT

/-- Quasi-equilibrium supports at a fixed allocation form an interval of `q`'s. -/
theorem pc_quasiSupports_uIcc {x : Fin 2 → Fin 2 → ℝ} {q₁ q₂ q : ℝ}
    (h₁ : E.QuasiSupports q₁ x) (h₂ : E.QuasiSupports q₂ x) (hq : q ∈ Set.uIcc q₁ q₂) :
    E.QuasiSupports q x := by
  intro i y hy hlt
  have a₁ := h₁ i y hy hlt
  have a₂ := h₂ i y hy hlt
  rw [pc_dot_pair, pc_dot_pair] at a₁ a₂ ⊢
  rcases le_total (y 0 - x i 0) (y 1 - x i 1) with hd | hd <;>
    rcases Set.mem_uIcc.1 hq with ⟨hl, hr⟩ | ⟨hl, hr⟩
  · nlinarith [mul_nonneg (sub_nonneg.2 hr) (sub_nonneg.2 hd)]
  · nlinarith [mul_nonneg (sub_nonneg.2 hr) (sub_nonneg.2 hd)]
  · nlinarith [mul_nonneg (sub_nonneg.2 hl) (sub_nonneg.2 hd)]
  · nlinarith [mul_nonneg (sub_nonneg.2 hl) (sub_nonneg.2 hd)]

/-- Adding `e ≥ 0`, `e ≠ 0` to a bundle and removing a small fraction of `f`, `0 ≤ f ≤ x`, leaves
a strongly monotone, continuous utility strictly higher. -/
theorem pc_exists_better_cheaper {L : ℕ} {u : (Fin L → ℝ) → ℝ}
    (hc : ContinuousOn u (nonnegOrthant L)) (hm : UtilityStronglyMonotone u)
    {x e f : Fin L → ℝ} (hx : x ∈ nonnegOrthant L) (he : e ∈ nonnegOrthant L) (he0 : e ≠ 0)
    (hf : f ∈ nonnegOrthant L) (hfx : f ≤ x) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ x + e - t • f ∈ nonnegOrthant L ∧ u x < u (x + e - t • f) := by
  have hmem : ∀ t ∈ Set.Icc (0 : ℝ) 1, x + e - t • f ∈ nonnegOrthant L := by
    intro t ht l
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [hf l, hfx l, he l, ht.1, ht.2, mul_nonneg (sub_nonneg.2 ht.2) (hf l)]
  have hg : Continuous fun t : ℝ => x + e - t • f := by fun_prop
  have h0 : u x < u (x + e - (0 : ℝ) • f) := by simpa using pc_lt_add hm hx he he0
  obtain ⟨t, ht0, ht1, hlt⟩ := exists_pos_continuous_lt hc hg hmem h0
  exact ⟨t, ht0, ht1, hmem t ⟨ht0.le, ht1⟩, hlt⟩

/-- **Exercise 15.B.10(d)** (MWG, p. 542). Quasi-equilibrium supporting prices of a box allocation
are strictly positive: if a good were free, the consumer holding some of the other good (`ω̄ ≫ 0`)
would find a strictly better and strictly cheaper bundle. -/
theorem pc_quasiSupports_pos (h : E.ParetoCurveHyp) {q : ℝ} (hq : q ∈ Set.Icc (0 : ℝ) 1)
    {x : Fin 2 → Fin 2 → ℝ} (hx : E.InBox x) (hS : E.QuasiSupports q x) : 0 < q ∧ q < 1 := by
  obtain ⟨h0, h1, hs⟩ := (pc_inBox_iff h x).1 hx
  have hxm : ∀ i, x i ∈ nonnegOrthant 2 := Fin.forall_fin_two.2 ⟨h0, h1⟩
  have hpos : ∀ l, ∃ i, 0 < x i l := by
    intro l
    by_contra hc
    simp only [not_exists, not_lt] at hc
    have := congrFun hs l
    simp only [Pi.add_apply] at this
    linarith [h.ω_pos l, hc 0, hc 1]
  have e0m : (![1, 0] : Fin 2 → ℝ) ∈ nonnegOrthant 2 := fun l => by fin_cases l <;> simp
  have e1m : (![0, 1] : Fin 2 → ℝ) ∈ nonnegOrthant 2 := fun l => by fin_cases l <;> simp
  have e0ne : (![1, 0] : Fin 2 → ℝ) ≠ 0 := fun he => by simpa using congrFun he 0
  have e1ne : (![0, 1] : Fin 2 → ℝ) ≠ 0 := fun he => by simpa using congrFun he 1
  refine ⟨lt_of_le_of_ne hq.1 fun hq0 => ?_, lt_of_le_of_ne hq.2 fun hq1 => ?_⟩
  · obtain ⟨i, hi⟩ := hpos 1
    have hfm : (![0, x i 1] : Fin 2 → ℝ) ∈ nonnegOrthant 2 := fun l => by
      fin_cases l <;> simp [hi.le]
    have hfx : (![0, x i 1] : Fin 2 → ℝ) ≤ x i := fun l => by
      fin_cases l <;> simp [hxm i 0]
    obtain ⟨t, ht0, -, hmem, hlt⟩ :=
      pc_exists_better_cheaper (h.cont i) (h.mono i) (hxm i) e0m e0ne hfm hfx
    have := hS i _ hmem hlt
    rw [pc_dot_pair, pc_dot_pair, ← hq0] at this
    simp [Matrix.vecHead, Matrix.vecTail] at this
    nlinarith [mul_pos ht0 hi]
  · obtain ⟨i, hi⟩ := hpos 0
    have hfm : (![x i 0, 0] : Fin 2 → ℝ) ∈ nonnegOrthant 2 := fun l => by
      fin_cases l <;> simp [hi.le]
    have hfx : (![x i 0, 0] : Fin 2 → ℝ) ≤ x i := fun l => by
      fin_cases l <;> simp [hxm i 1]
    obtain ⟨t, ht0, -, hmem, hlt⟩ :=
      pc_exists_better_cheaper (h.cont i) (h.mono i) (hxm i) e1m e1ne hfm hfx
    have := hS i _ hmem hlt
    rw [pc_dot_pair, pc_dot_pair, hq1] at this
    simp [Matrix.vecHead, Matrix.vecTail] at this
    nlinarith [mul_pos ht0 hi]

/-- **Exercise 15.B.10(d)** (MWG, p. 542). A quasi-equilibrium with strictly positive prices at
which every consumer's bundle is worth his endowment is a Walrasian equilibrium: a consumer with a
nonzero bundle could shrink a strictly preferred affordable bundle to a strictly cheaper one, and
a consumer with the zero bundle can afford only `0`. -/
theorem pc_walras_of_quasiSupports (h : E.ParetoCurveHyp) {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    {x : Fin 2 → Fin 2 → ℝ} (hx : E.InBox x) (hS : E.QuasiSupports q x)
    (hb : ∀ i, ![q, 1 - q] ⬝ᵥ x i = ![q, 1 - q] ⬝ᵥ E.ω i) : E.IsWalrasEqm ![q, 1 - q] x := by
  have hp : StrictlyPositive ![q, 1 - q] := fun l => by
    fin_cases l
    · simpa using hq0
    · simpa using hq1
  refine ⟨hx, fun i y hy => ?_⟩
  obtain ⟨hym, hpy⟩ := hy
  rw [h.X_eq i] at hym
  have hxi : x i ∈ nonnegOrthant 2 := by
    rw [← h.X_eq i]
    exact hx.1 i
  by_contra hlt
  rw [not_le] at hlt
  by_cases hx0 : x i = 0
  · rw [← hb i, hx0, dotProduct_zero] at hpy
    have hy0 := eq_zero_of_dotProduct_nonpos hp hym hpy
    rw [hy0, ← hx0] at hlt
    exact lt_irrefl _ hlt
  · have hpos := dotProduct_pos_of_strictlyPositive hp hxi hx0
    obtain ⟨t, ht0, ht1, hlt'⟩ := pc_exists_shrink (h.cont i) hym hlt
    have := hS i _ (pc_smul_mem hym (by linarith)) hlt'
    rw [dotProduct_smul, smul_eq_mul] at this
    rw [← hb i] at hpy
    nlinarith [mul_le_mul_of_nonneg_left hpy (sub_nonneg.2 ht1), mul_pos ht0 hpos]

/-- Moving endowments between consumers without changing the total does not change the Pareto
set. -/
theorem pc_isParetoOptimal_with (ω' : Fin 2 → Fin 2 → ℝ) (hsum : ∑ i, ω' i = ∑ i, E.ω i)
    (x : Fin 2 → Fin 2 → ℝ) :
    ({ E with ω := ω' } : EdgeworthEconomy).IsParetoOptimal x ↔ E.IsParetoOptimal x := by
  have hb : ∀ y, ({ E with ω := ω' } : EdgeworthEconomy).InBox y ↔ E.InBox y := fun y => by
    change ((∀ i, y i ∈ E.X i) ∧ ∑ i, y i = ∑ i, ω' i) ↔
      ((∀ i, y i ∈ E.X i) ∧ ∑ i, y i = ∑ i, E.ω i)
    rw [hsum]
  change (({ E with ω := ω' } : EdgeworthEconomy).InBox x ∧
      ¬ ∃ x', ({ E with ω := ω' } : EdgeworthEconomy).InBox x' ∧
        (∀ i, E.u i (x i) ≤ E.u i (x' i)) ∧ ∃ i, E.u i (x i) < E.u i (x' i)) ↔
    (E.InBox x ∧ ¬ ∃ x', E.InBox x' ∧ (∀ i, E.u i (x i) ≤ E.u i (x' i)) ∧
      ∃ i, E.u i (x i) < E.u i (x' i))
  simp only [hb]

/-- **Exercise 15.B.10(d)** (MWG, p. 542), the hint. Let `(p', x')` be a Walrasian equilibrium of
the economy after a transfer `z ≥ 0` from consumer 2 to consumer 1 (endowments `ω₁ + z`,
`ω₂ - z`). Then the economy before the transfer has a Walrasian equilibrium `(p, x)` with `p ≫ 0`
at which consumer 1's utility is no higher than at `x'`. Proof: along the Pareto curve from
consumer 1's origin (where consumer 1's excess value `p·(x₁ - ω₁)` at supporting prices is
`≤ 0`) to `x'` (where it is `≥ 0`), the closed sets of utility levels with a supporting price
making it `≤ 0`, resp. `≥ 0`, cover a connected interval and so intersect; there a supporting
price makes it `0`, and that quasi-equilibrium is a Walrasian equilibrium. (The hint's "even lower
level of utility" is proved in the weak form `≤`.) -/
theorem exercise_15_B_10d_lower_eqm (h : E.ParetoCurveHyp) (hω0 : E.ω 0 ∈ nonnegOrthant 2)
    {z : Fin 2 → ℝ} (hz : z ∈ nonnegOrthant 2) {p' : Fin 2 → ℝ} {x' : Fin 2 → Fin 2 → ℝ}
    (heq : ({ E with ω := ![E.ω 0 + z, E.ω 1 - z] } : EdgeworthEconomy).IsWalrasEqm p' x') :
    ∃ p x, StrictlyPositive p ∧ E.IsWalrasEqm p x ∧ E.u 0 (x 0) ≤ E.u 0 (x' 0) := by
  set E' : EdgeworthEconomy := { E with ω := ![E.ω 0 + z, E.ω 1 - z] } with hE'
  have hsum : ∑ i, E'.ω i = ∑ i, E.ω i := by
    change ∑ i, (![E.ω 0 + z, E.ω 1 - z] : Fin 2 → Fin 2 → ℝ) i = ∑ i, E.ω i
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    abel
  have hlns : ∀ i, UtilityLNS (E.u i) := fun i => (h.mono i).lns two_pos
  have hd' : E'.IsDemandEqm p' x' := (isWalrasEqm_iff_isDemandEqm (E := E') h.X_eq hlns p' x').1 heq
  have hpo : E.IsParetoOptimal x' :=
    (pc_isParetoOptimal_with _ hsum x').1 (first_welfare_theorem (E := E') h.X_eq hlns heq)
  have hx'm : ∀ i, x' i ∈ nonnegOrthant 2 := fun i => by
    rw [← h.X_eq i]
    exact hpo.1.1 i
  -- the equilibrium prices of the economy after the transfer are strictly positive
  have hp' : StrictlyPositive p' := by
    intro l
    by_contra hc
    rw [not_lt] at hc
    have hel : (Pi.single l 1 : Fin 2 → ℝ) ∈ nonnegOrthant 2 := fun k => by
      by_cases hk : k = l
      · subst hk
        simp
      · simp [hk]
    have hel0 : (Pi.single l 1 : Fin 2 → ℝ) ≠ 0 := fun he => by
      simpa using congrFun he l
    have hy : x' 0 + Pi.single l 1 ∈ E'.budget 0 p' := by
      refine ⟨?_, ?_⟩
      · change x' 0 + Pi.single l 1 ∈ E.X 0
        rw [h.X_eq 0]
        exact fun k => add_nonneg (hx'm 0 k) (hel k)
      · rw [dotProduct_add, dotProduct_single, mul_one]
        linarith [(hd'.2 0).1.2]
    have := (hd'.2 0).2 _ hy
    linarith [pc_lt_add (h.mono 0) (hx'm 0) hel hel0]
  set v' := E.u 0 (x' 0) with hv'
  have hx'c : x' = E.paretoCurve v' := pc_eq_paretoCurve h hpo
  have hav' : E.u 0 0 ≤ v' := (pc_po_bounds h hpo).1
  have hpc := pc_continuous_paretoCurve h
  set g : ℝ → ℝ → ℝ := fun v q => ![q, 1 - q] ⬝ᵥ (E.paretoCurve v 0 - E.ω 0) with hg
  have hgc : Continuous fun vq : ℝ × ℝ => g vq.1 vq.2 := by
    simp only [hg, pc_dot_pair, Pi.sub_apply]
    fun_prop
  set A := {v : ℝ | ∃ q ∈ Set.Icc (0 : ℝ) 1, E.QuasiSupports q (E.paretoCurve v) ∧ g v q ≤ 0}
    with hA
  set B := {v : ℝ | ∃ q ∈ Set.Icc (0 : ℝ) 1, E.QuasiSupports q (E.paretoCurve v) ∧ 0 ≤ g v q}
    with hB
  have hAc : IsClosed A := pc_isClosed_exists_Icc
    ((pc_isClosed_quasiSupports h).inter (isClosed_le hgc continuous_const))
  have hBc : IsClosed B := pc_isClosed_exists_Icc
    ((pc_isClosed_quasiSupports h).inter (isClosed_le continuous_const hgc))
  have hcover : Set.Icc (E.u 0 0) v' ⊆ A ∪ B := by
    intro v _
    obtain ⟨q, hq, hS⟩ := pc_exists_quasiSupports h v
    rcases le_total (g v q) 0 with hle | hle
    · exact Or.inl ⟨q, hq, hS, hle⟩
    · exact Or.inr ⟨q, hq, hS, hle⟩
  -- at consumer 1's origin the excess value is `≤ 0`
  have haA : E.u 0 0 ∈ A := by
    have hu := pc_paretoCurve_u h ⟨le_rfl, pc_a_le_b h⟩
    have h0 : E.paretoCurve (E.u 0 0) 0 = 0 := by
      by_contra hne
      exact absurd hu ((h.mono 0).lt pc_zero_mem (fun l => pc_paretoCurve_mem h _ 0 l) hne).ne'
    obtain ⟨q, hq, hS⟩ := pc_exists_quasiSupports h (E.u 0 0)
    refine ⟨q, hq, hS, ?_⟩
    simp only [hg, h0, zero_sub, dotProduct_neg, neg_nonpos]
    refine dotProduct_nonneg_of_nonneg (fun l => ?_) hω0
    fin_cases l
    · simpa using hq.1
    · simpa using hq.2
  -- at `x'` the excess value is `≥ 0`
  have hv'B : v' ∈ B := by
    have hsupp : ∀ i, ∀ y ∈ nonnegOrthant 2, E.u i (x' i) < E.u i y → p' ⬝ᵥ x' i ≤ p' ⬝ᵥ y := by
      intro i y hy hlt
      by_contra hc
      rw [not_le] at hc
      have hyb : y ∈ E'.budget i p' := by
        refine ⟨?_, ?_⟩
        · change y ∈ E.X i
          rw [h.X_eq i]
          exact hy
        · linarith [(hd'.2 i).1.2]
      linarith [(hd'.2 i).2 y hyb]
    obtain ⟨hq, hS⟩ := pc_quasiSupports_of_pos (E := E) hp' hsupp
    refine ⟨_, hq, hx'c ▸ hS, ?_⟩
    have hs : 0 < p' 0 + p' 1 := add_pos (hp' 0) (hp' 1)
    have hbud := budget_line_of_inBox hd'.1 (fun i => (hd'.2 i).1.2) 0
    have hω'0 : E'.ω 0 = E.ω 0 + z := rfl
    rw [hω'0, dotProduct_add] at hbud
    simp only [hg]
    rw [← hx'c, pc_normalize hs, smul_dotProduct, smul_eq_mul, dotProduct_sub, hbud]
    exact mul_nonneg (inv_nonneg.2 hs.le)
      (by linarith [dotProduct_nonneg_of_nonneg (fun l => (hp' l).le) hz])
  obtain ⟨v, hv, hvA, hvB⟩ := isPreconnected_closed_iff.1 isPreconnected_Icc A B hAc hBc hcover
    ⟨_, Set.left_mem_Icc.2 hav', haA⟩ ⟨v', Set.right_mem_Icc.2 hav', hv'B⟩
  obtain ⟨q₁, hq₁, hS₁, hg₁⟩ := hvA
  obtain ⟨q₂, hq₂, hS₂, hg₂⟩ := hvB
  have hgv : ContinuousOn (fun q => g v q) (Set.uIcc q₁ q₂) := by
    simp only [hg, pc_dot_pair]
    fun_prop
  obtain ⟨q, hq, hgq⟩ :=
    isPreconnected_uIcc.intermediate_value Set.left_mem_uIcc Set.right_mem_uIcc hgv ⟨hg₁, hg₂⟩
  have hqI : q ∈ Set.Icc (0 : ℝ) 1 := Set.uIcc_subset_Icc hq₁ hq₂ hq
  have hSq := pc_quasiSupports_uIcc hS₁ hS₂ hq
  set x := E.paretoCurve v with hx
  have hxb : E.InBox x := (pc_paretoCurve_spec h v).1.1
  obtain ⟨hq0, hq1⟩ := pc_quasiSupports_pos h hqI hxb hSq
  have hb0 : ![q, 1 - q] ⬝ᵥ x 0 = ![q, 1 - q] ⬝ᵥ E.ω 0 := by
    have : ![q, 1 - q] ⬝ᵥ (x 0 - E.ω 0) = 0 := hgq
    rw [dotProduct_sub] at this
    linarith
  have hb : ∀ i, ![q, 1 - q] ⬝ᵥ x i = ![q, 1 - q] ⬝ᵥ E.ω i := by
    rw [Fin.forall_fin_two]
    refine ⟨hb0, ?_⟩
    obtain ⟨-, -, hsx⟩ := (pc_inBox_iff h x).1 hxb
    have htot : E.totalEndowment = E.ω 0 + E.ω 1 := by
      simp [ExchangeEconomy.totalEndowment, Fin.sum_univ_two]
    have := congrArg (fun y => ![q, 1 - q] ⬝ᵥ y) hsx
    simp only [htot, dotProduct_add] at this
    linarith
  refine ⟨![q, 1 - q], x, fun l => ?_, pc_walras_of_quasiSupports h hq0 hq1 hxb hSq hb, ?_⟩
  · fin_cases l
    · simpa using hq0
    · simpa using hq1
  · rw [hx, pc_paretoCurve_u h ⟨hv.1, hv.2.trans (pc_po_bounds h hpo).2⟩]
    exact hv.2

/-- **Exercise 15.B.10(d)** (MWG, p. 542). In an Edgeworth box economy with continuous, strictly
convex and strongly monotone preferences, the transfer paradox can happen only if there is a
multiplicity of equilibria: if after a transfer `z ≥ 0` to consumer 1 there is an equilibrium
`(p', x')` at which consumer 1 is strictly worse off than at some equilibrium `(p, x)` before the
transfer, then the economy before the transfer has two equilibria with different allocations. -/
theorem exercise_15_B_10d (h : E.ParetoCurveHyp) (hω0 : E.ω 0 ∈ nonnegOrthant 2)
    {z : Fin 2 → ℝ} (hz : z ∈ nonnegOrthant 2) {p' : Fin 2 → ℝ} {x' : Fin 2 → Fin 2 → ℝ}
    (heq : ({ E with ω := ![E.ω 0 + z, E.ω 1 - z] } : EdgeworthEconomy).IsWalrasEqm p' x')
    {p : Fin 2 → ℝ} {x : Fin 2 → Fin 2 → ℝ} (hE : E.IsWalrasEqm p x)
    (hlt : E.u 0 (x' 0) < E.u 0 (x 0)) :
    ∃ p₁ x₁ p₂ x₂, E.IsWalrasEqm p₁ x₁ ∧ E.IsWalrasEqm p₂ x₂ ∧ x₁ ≠ x₂ := by
  obtain ⟨p₂, x₂, -, h₂, hle⟩ := exercise_15_B_10d_lower_eqm h hω0 hz heq
  refine ⟨p, x, p₂, x₂, hE, h₂, fun he => ?_⟩
  rw [he] at hlt
  linarith

/-! ### The instance `u = √x₁ + √x₂` -/

/-- **Exercises 15.B.7 and 15.B.10(d)** (MWG, pp. 541-542), instance. The utility function
`u(x) = √x₁ + √x₂`. -/
noncomputable def sqrtUtility (x : Fin 2 → ℝ) : ℝ := Real.sqrt (x 0) + Real.sqrt (x 1)

/-- **Exercises 15.B.7 and 15.B.10(d)** (MWG, pp. 541-542), instance. The Edgeworth box economy
in which both consumers have `u = √x₁ + √x₂`, with endowments `ω₁ = (1, 0)` and `ω₂ = (0, 1)`. -/
noncomputable def sqrtEconomy : EdgeworthEconomy :=
  ExchangeEconomy.ofOrthant (fun _ => sqrtUtility) ![![1, 0], ![0, 1]]

/-- The total endowment of `sqrtEconomy` is `(1, 1)`. -/
theorem sqrtEconomy_total : sqrtEconomy.totalEndowment = ![1, 1] := by
  funext l
  fin_cases l <;>
    simp [ExchangeEconomy.totalEndowment, sqrtEconomy, ExchangeEconomy.ofOrthant,
      Fin.sum_univ_two]

/-- `√x₁ + √x₂` is strongly monotone on `ℝ²₊`. -/
theorem sqrtUtility_stronglyMonotone : UtilityStronglyMonotone sqrtUtility := by
  intro x hx y _ hxy hne
  have key : sqrtUtility x < sqrtUtility y := by
    have h0 := Real.sqrt_le_sqrt (hxy 0)
    have h1 := Real.sqrt_le_sqrt (hxy 1)
    have hor : x 0 ≠ y 0 ∨ x 1 ≠ y 1 := by
      by_contra hc
      simp only [not_or, not_not] at hc
      exact hne (funext (Fin.forall_fin_two.2 ⟨hc.1.symm, hc.2.symm⟩))
    unfold sqrtUtility
    rcases hor with hl | hl
    · linarith [Real.sqrt_lt_sqrt (hx 0) (lt_of_le_of_ne (hxy 0) hl)]
    · linarith [Real.sqrt_lt_sqrt (hx 1) (lt_of_le_of_ne (hxy 1) hl)]
  exact ⟨key.le, not_le.2 key⟩

/-- `√x₁ + √x₂` represents strictly convex preferences on `ℝ²₊` (it is strictly concave). -/
theorem sqrtUtility_strictlyConvex :
    PrefStrictlyConvex (nonnegOrthant 2) (utilityPref sqrtUtility) := by
  intro x _ y hy z hz hyx hzx hne α h0 h1
  have hyx' : sqrtUtility x ≤ sqrtUtility y := hyx
  have hzx' : sqrtUtility x ≤ sqrtUtility z := hzx
  have hm : ∀ l, (α • y + (1 - α) • z) l = α * y l + (1 - α) * z l := fun l => by
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hc : ∀ l, α * Real.sqrt (y l) + (1 - α) * Real.sqrt (z l) ≤
      Real.sqrt (α * y l + (1 - α) * z l) := fun l => by
    simpa [smul_eq_mul] using Real.strictConcaveOn_sqrt.concaveOn.2 (hy l) (hz l) h0.le
      (by linarith) (by ring)
  have hsc : ∀ l, y l ≠ z l → α * Real.sqrt (y l) + (1 - α) * Real.sqrt (z l) <
      Real.sqrt (α * y l + (1 - α) * z l) := fun l hl => by
    simpa [smul_eq_mul] using Real.strictConcaveOn_sqrt.2 (hy l) (hz l) hl h0
      (by linarith) (by ring)
  have hor : y 0 ≠ z 0 ∨ y 1 ≠ z 1 := by
    by_contra hc'
    simp only [not_or, not_not] at hc'
    exact hne (funext (Fin.forall_fin_two.2 ⟨hc'.1, hc'.2⟩))
  have hmean : sqrtUtility x ≤ α * sqrtUtility y + (1 - α) * sqrtUtility z := by
    nlinarith [mul_le_mul_of_nonneg_left hyx' h0.le,
      mul_le_mul_of_nonneg_left hzx' (sub_nonneg.2 h1.le)]
  have key : sqrtUtility x < sqrtUtility (α • y + (1 - α) • z) := by
    unfold sqrtUtility at hmean ⊢
    rw [hm 0, hm 1]
    rcases hor with hl | hl
    · linarith [hsc 0 hl, hc 1]
    · linarith [hc 0, hsc 1 hl]
  exact ⟨key.le, not_le.2 key⟩

/-- **Exercises 15.B.7 and 15.B.10(d)** (MWG, pp. 541-542), instance. `sqrtEconomy` satisfies the
standing hypotheses. -/
theorem sqrtEconomy_hyp : sqrtEconomy.ParetoCurveHyp where
  X_eq _ := rfl
  cont _ := ((Real.continuous_sqrt.comp (continuous_apply 0)).add
    (Real.continuous_sqrt.comp (continuous_apply 1))).continuousOn
  mono _ := sqrtUtility_stronglyMonotone
  sconv _ := sqrtUtility_strictlyConvex
  ω_pos l := by
    rw [sqrtEconomy_total]
    fin_cases l <;> simp

/-- **Exercise 15.B.7** (MWG, p. 541), instance. `√x₁ + √x₂` is homothetic (Definition 3.B.6):
`√(αx₁) + √(αx₂) = √α (√x₁ + √x₂)`. -/
theorem sqrtEconomy_homothetic :
    ∀ i, Homothetic (nonnegOrthant 2) (utilityPref (sqrtEconomy.u i)) := by
  intro _ x _ y _ hxy α hα
  have e : ∀ v : Fin 2 → ℝ, sqrtUtility (α • v) = Real.sqrt α * sqrtUtility v := fun v => by
    simp only [sqrtUtility, Pi.smul_apply, smul_eq_mul, Real.sqrt_mul hα]
    ring
  have hxy' : sqrtUtility y ≤ sqrtUtility x ∧ sqrtUtility x ≤ sqrtUtility y := hxy
  change sqrtUtility (α • y) ≤ sqrtUtility (α • x) ∧ sqrtUtility (α • x) ≤ sqrtUtility (α • y)
  rw [e, e]
  exact ⟨mul_le_mul_of_nonneg_left hxy'.1 (Real.sqrt_nonneg _),
    mul_le_mul_of_nonneg_left hxy'.2 (Real.sqrt_nonneg _)⟩

/-- With `√x₁ + √x₂`, a bundle with `y₁ + y₂ ≤ 2c` is no better than `(c, c)`. -/
theorem sqrtUtility_le_diag {y : Fin 2 → ℝ} (hy : y ∈ nonnegOrthant 2) {c : ℝ} (hc : 0 ≤ c)
    (hyc : y 0 + y 1 ≤ 2 * c) : sqrtUtility y ≤ sqrtUtility ![c, c] := by
  simp only [sqrtUtility, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  have ha := Real.sq_sqrt (hy 0)
  have hb := Real.sq_sqrt (hy 1)
  have hs := Real.sq_sqrt hc
  have hsq : (Real.sqrt (y 0) + Real.sqrt (y 1)) ^ 2 ≤ (Real.sqrt c + Real.sqrt c) ^ 2 := by
    nlinarith [sq_nonneg (Real.sqrt (y 0) - Real.sqrt (y 1))]
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 hsq

/-- **Exercise 15.B.7** (MWG, p. 541), instance. In `sqrtEconomy` the equal split
`((1/2, 1/2), (1/2, 1/2))` is Pareto optimal. -/
theorem sqrtEconomy_half_po :
    sqrtEconomy.IsParetoOptimal (sqrtEconomy.diagonalAllocation (1 / 2)) := by
  have hh : (1 / 2 : ℝ) • (![1, 1] : Fin 2 → ℝ) = ![1 / 2, 1 / 2] := by
    funext l
    fin_cases l <;> simp
  have hh' : (1 - 1 / 2 : ℝ) • (![1, 1] : Fin 2 → ℝ) = ![1 / 2, 1 / 2] := by
    funext l
    fin_cases l <;> norm_num
  refine (pc_isParetoOptimal_iff sqrtEconomy_hyp _).2
    ⟨pc_diagonal_inBox sqrtEconomy_hyp ⟨by norm_num, by norm_num⟩, fun x' hx' ⟨g0, g1⟩ => ?_⟩
  obtain ⟨m0, m1, hsum⟩ := (pc_inBox_iff sqrtEconomy_hyp x').1 hx'
  rw [sqrtEconomy_total] at hsum
  have s0 := congrFun hsum 0
  have s1 := congrFun hsum 1
  simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] at s0 s1
  simp only [ExchangeEconomy.diagonalAllocation, sqrtEconomy_total, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, hh, hh'] at g0 g1
  change sqrtUtility ![1 / 2, 1 / 2] < sqrtUtility (x' 0) at g0
  change sqrtUtility ![1 / 2, 1 / 2] < sqrtUtility (x' 1) at g1
  rcases le_total (x' 0 0 + x' 0 1) 1 with hle | hle
  · exact absurd (sqrtUtility_le_diag m0 (by norm_num) (by linarith)) (not_le.2 g0)
  · exact absurd (sqrtUtility_le_diag m1 (by norm_num) (by linarith)) (not_le.2 g1)

/-- **Exercise 15.B.7** (MWG, p. 541), instance. With identical homothetic preferences
`u = √x₁ + √x₂` the Pareto set of `sqrtEconomy` is the diagonal of the box. -/
theorem sqrtEconomy_paretoSet :
    sqrtEconomy.paretoSet = sqrtEconomy.diagonalAllocation '' Set.Icc 0 1 := by
  refine exercise_15_B_7_diagonal sqrtEconomy_hyp sqrtEconomy_homothetic sqrtEconomy_half_po
    ?_ ?_ ?_ <;>
    simp only [ExchangeEconomy.diagonalAllocation, sqrtEconomy_total, Matrix.cons_val_zero]
  · intro he
    simpa using congrFun he 0
  · intro he
    have := congrFun he 0
    norm_num at this
  · simp

/-- **Exercise 15.B.10(d)** (MWG, p. 542), instance. After the transfer `z = (0, 1/2)` to
consumer 1 in `sqrtEconomy` (endowments `(1, 1/2)` and `(0, 1/2)`), the prices `(1, 1)` and the
allocation `((3/4, 3/4), (1/4, 1/4))` form a Walrasian equilibrium. -/
theorem sqrtEconomy_transfer_eqm :
    ({ sqrtEconomy with ω := ![sqrtEconomy.ω 0 + ![0, 1 / 2], sqrtEconomy.ω 1 - ![0, 1 / 2]] } :
      EdgeworthEconomy).IsWalrasEqm ![1, 1] ![![3 / 4, 3 / 4], ![1 / 4, 1 / 4]] := by
  refine ⟨⟨fun i l => ?_, ?_⟩, fun i y hy => ?_⟩
  · fin_cases i <;> fin_cases l <;> norm_num
  · funext l
    fin_cases l <;>
      simp [sqrtEconomy, ExchangeEconomy.ofOrthant, ExchangeEconomy.totalEndowment,
        Fin.sum_univ_two] <;> norm_num
  · obtain ⟨hym, hpy⟩ := hy
    change y ∈ nonnegOrthant 2 at hym
    have hb : (![1, 1] : Fin 2 → ℝ) ⬝ᵥ y = y 0 + y 1 := by simp [dotProduct, Fin.sum_univ_two]
    rw [hb] at hpy
    fin_cases i
    · have hw := hpy.trans_eq (by
        norm_num [sqrtEconomy, ExchangeEconomy.ofOrthant, dotProduct, Fin.sum_univ_two] :
          _ = (3 / 2 : ℝ))
      change sqrtUtility y ≤ sqrtUtility ![3 / 4, 3 / 4]
      exact sqrtUtility_le_diag hym (by norm_num) (by linarith)
    · have hw := hpy.trans_eq (by
        norm_num [sqrtEconomy, ExchangeEconomy.ofOrthant, dotProduct, Fin.sum_univ_two] :
          _ = (1 / 2 : ℝ))
      change sqrtUtility y ≤ sqrtUtility ![1 / 4, 1 / 4]
      exact sqrtUtility_le_diag hym (by norm_num) (by linarith)

/-- **Exercise 15.B.10(d)** (MWG, p. 542), instance. The theorem `exercise_15_B_10d_lower_eqm`
applies to `sqrtEconomy` with the transfer `z = (0, 1/2)`: before the transfer there is a
Walrasian equilibrium with strictly positive prices at which consumer 1's utility is at most his
utility `√3` at the post-transfer equilibrium. -/
theorem sqrtEconomy_15_B_10d :
    ∃ p x, StrictlyPositive p ∧ sqrtEconomy.IsWalrasEqm p x ∧
      sqrtEconomy.u 0 (x 0) ≤ sqrtUtility ![3 / 4, 3 / 4] :=
  exercise_15_B_10d_lower_eqm sqrtEconomy_hyp
    (fun l => by fin_cases l <;> simp [sqrtEconomy, ExchangeEconomy.ofOrthant])
    (fun l => by fin_cases l <;> norm_num) sqrtEconomy_transfer_eqm

end MWG.GeneralEquilibriumExamples
