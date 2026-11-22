/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPositiveEquilibriumTheory.ExcessDemand
import MWGClassicalDemand.AppendixAContinuity

/-!
# Demand as a function of prices and wealth (MWG Section 17.B, pp. 581-582)

Tools for **Proposition 17.B.2**: the single-valued demand of a consumer with continuous,
strictly convex preferences on `ℝ^L₊`, its continuity, and its behaviour near the boundary of
the price domain.

* `uDemand u p w`: the element of the demand set `x(p, w)` (Proposition 3.D.1 and 3.D.2(iii):
  it is a singleton at `p ≫ 0`, `w ≥ 0`), `uDemand_mem`, `walrasianDemand_eq_singleton`.
* `continuousOn_uDemand`: `(p, w) ↦ x(p, w)` is continuous on `{p ≫ 0, w ≥ 0}` (Proposition
  3.AA.1 at `w > 0`; at `w = 0` demand is `0` and nearby demands are small).
* `demand_bounded_near_boundary_false`: the core of Exercise 17.B.2. With strongly monotone
  preferences, if `pⁿ ≫ 0` tends to a price vector with a zero component and the wealths tend to
  a positive limit, demanded bundles cannot stay bounded. A bounded subsequence would have a
  limit point, which by upper hemicontinuity (the locally cheaper argument of 3.AA.1, valid at
  boundary prices) would be demanded at the limit prices, where demand is empty.
-/

namespace MWG.PositiveEquilibriumTheory

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.GeneralEquilibriumExamples
open Filter Topology

variable {L : ℕ}

/-- The price-wealth pairs `p ≫ 0`, `w ≥ 0`: the domain on which demand is a continuous
function. -/
def wealthDomain (L : ℕ) : Set ((Fin L → ℝ) × ℝ) := {q | StrictlyPositive q.1 ∧ 0 ≤ q.2}

/-- **Section 17.B** (MWG, p. 581). The Walrasian demand `x(p, w)` of the utility `u` on `ℝ^L₊`
as a function: the element of the demand set when it is nonempty, `0` otherwise. -/
noncomputable def uDemand (u : (Fin L → ℝ) → ℝ) (p : Fin L → ℝ) (w : ℝ) : Fin L → ℝ :=
  open Classical in if h : (walrasianDemand u p w).Nonempty then h.some else 0

/-- A nonempty demand set contains `uDemand`. -/
theorem uDemand_mem {u : (Fin L → ℝ) → ℝ} {p : Fin L → ℝ} {w : ℝ}
    (h : (walrasianDemand u p w).Nonempty) : uDemand u p w ∈ walrasianDemand u p w := by
  unfold uDemand
  simp only [h, ↓reduceDIte]
  exact h.some_mem

/-- `uDemand` is always a bundle in `ℝ^L₊`. -/
theorem uDemand_nonneg (u : (Fin L → ℝ) → ℝ) (p : Fin L → ℝ) (w : ℝ) :
    uDemand u p w ∈ nonnegOrthant L := by
  by_cases h : (walrasianDemand u p w).Nonempty
  · exact (uDemand_mem h).1.1
  · unfold uDemand
    simp only [h, ↓reduceDIte]
    exact fun _ => le_rfl

/-- **Propositions 3.D.1 and 3.D.2(iii)**. At `p ≫ 0` and `w ≥ 0` a continuous, strictly
quasiconcave utility on `ℝ^L₊` has exactly one demanded bundle. -/
theorem walrasianDemand_eq_singleton {u : (Fin L → ℝ) → ℝ}
    (hc : ContinuousOn u (nonnegOrthant L)) (hsq : StrictlyQuasiconcaveOn (nonnegOrthant L) u)
    {p : Fin L → ℝ} (hp : StrictlyPositive p) {w : ℝ} (hw : 0 ≤ w) :
    walrasianDemand u p w = {uDemand u p w} :=
  (proposition_3_D_2_iii_unique hsq p w).eq_singleton_of_mem
    (uDemand_mem (proposition_3_D_1 hc hp hw))

/-- Demand is homogeneous of degree zero in `(p, w)` (Proposition 3.D.2(i)). -/
theorem uDemand_smul (u : (Fin L → ℝ) → ℝ) (p : Fin L → ℝ) (w : ℝ) {α : ℝ} (hα : 0 < α) :
    uDemand u (α • p) (α * w) = uDemand u p w := by
  unfold uDemand
  rw [proposition_3_D_2_i u p w hα]

/-- At `p ≫ 0` the only affordable bundle with zero wealth is `0`. -/
theorem eq_zero_of_dotProduct_nonpos {p x : Fin L → ℝ} (hp : StrictlyPositive p)
    (hx : x ∈ nonnegOrthant L) (hpx : p ⬝ᵥ x ≤ 0) : x = 0 := by
  have hterms : ∀ l ∈ Finset.univ, 0 ≤ p l * x l := fun l _ => mul_nonneg (hp l).le (hx l)
  have hsum : ∑ l, p l * x l = 0 := le_antisymm hpx (Finset.sum_nonneg hterms)
  funext l
  have := (Finset.sum_eq_zero_iff_of_nonneg hterms).1 hsum l (Finset.mem_univ l)
  simpa using (mul_eq_zero.1 this).resolve_left (hp l).ne'

/-- With zero wealth and `p ≫ 0`, demand is `0`. -/
theorem uDemand_zero_wealth {u : (Fin L → ℝ) → ℝ} (hc : ContinuousOn u (nonnegOrthant L))
    {p : Fin L → ℝ} (hp : StrictlyPositive p) : uDemand u p 0 = 0 := by
  have hx := uDemand_mem (proposition_3_D_1 hc hp le_rfl)
  exact eq_zero_of_dotProduct_nonpos hp hx.1.1 hx.1.2

/-- A strictly positive vector has a uniform positive lower bound. -/
theorem exists_pos_le_of_strictlyPositive {p : Fin L → ℝ} (hp : StrictlyPositive p) :
    ∃ c : ℝ, 0 < c ∧ ∀ l, c ≤ p l := by
  rcases isEmpty_or_nonempty (Fin L) with h | h
  · exact ⟨1, one_pos, fun l => (IsEmpty.false l).elim⟩
  · obtain ⟨l0, -, hl0⟩ := Finset.exists_min_image Finset.univ p Finset.univ_nonempty
    exact ⟨p l0, hp l0, fun l => hl0 l (Finset.mem_univ l)⟩

/-- The price-wealth domain `(p, w) ≫ 0` is open. -/
theorem isOpen_pwDomainSet (L : ℕ) : IsOpen (pwDomainSet L) := by
  have h : pwDomainSet L = (Prod.fst ⁻¹' posOrthant L) ∩ {q | 0 < q.2} :=
    Set.ext fun _ => Iff.rfl
  rw [h]
  exact ((isOpen_posOrthant L).preimage continuous_fst).inter
    (isOpen_lt continuous_const continuous_snd)

/-- **Proposition 3.AA.1**, extended to zero wealth. For a continuous, strictly quasiconcave
utility on `ℝ^L₊`, the demand function `(p, w) ↦ x(p, w)` is continuous on
`{p ≫ 0, w ≥ 0}`. -/
theorem continuousOn_uDemand {u : (Fin L → ℝ) → ℝ} (hc : ContinuousOn u (nonnegOrthant L))
    (hsq : StrictlyQuasiconcaveOn (nonnegOrthant L) u) :
    ContinuousOn (fun q : (Fin L → ℝ) × ℝ => uDemand u q.1 q.2) (wealthDomain L) := by
  have hs : ∀ p w, PWDomain p w → walrasianDemand u p w = {uDemand u p w} :=
    fun p w hd => walrasianDemand_eq_singleton hc hsq hd.1 hd.2.le
  have hAA := proposition_3_AA_1_continuous hc hs
  intro q hq
  rcases hq.2.eq_or_lt with h0 | hpos
  · rw [Metric.continuousWithinAt_iff]
    intro ε hε
    obtain ⟨c, hc0, hcp⟩ := exists_pos_le_of_strictlyPositive hq.1
    refine ⟨min (c / 2) (c * ε / 2), by positivity, fun {q'} hq' hd => ?_⟩
    have hd' := hd.trans_le (min_le_left _ _)
    have hd'' := hd.trans_le (min_le_right _ _)
    rw [Prod.dist_eq] at hd' hd''
    have hd1 : dist q'.1 q.1 < c / 2 := (le_max_left _ _).trans_lt hd'
    have hd2 : dist q'.2 q.2 < c * ε / 2 := (le_max_right _ _).trans_lt hd''
    have hp' : ∀ l, c / 2 < q'.1 l := fun l => by
      have h1 := (dist_le_pi_dist q'.1 q.1 l).trans_lt hd1
      rw [Real.dist_eq] at h1
      have h2 := neg_abs_le (q'.1 l - q.1 l)
      linarith [hcp l]
    have hw' : q'.2 < c * ε / 2 := by
      rw [Real.dist_eq, ← h0, sub_zero] at hd2
      exact (le_abs_self _).trans_lt hd2
    have hx := uDemand_mem (proposition_3_D_1 hc hq'.1 hq'.2)
    have hq0 : uDemand u q.1 q.2 = 0 := by rw [← h0]; exact uDemand_zero_wealth hc hq.1
    rw [hq0, dist_zero_right, pi_norm_lt_iff hε]
    intro l
    rw [Real.norm_eq_abs, abs_of_nonneg (hx.1.1 l)]
    have hsingle : q'.1 l * uDemand u q'.1 q'.2 l ≤ q'.1 ⬝ᵥ uDemand u q'.1 q'.2 :=
      Finset.single_le_sum (fun k _ => mul_nonneg (hq'.1 k).le (hx.1.1 k)) (Finset.mem_univ l)
    have hb := hx.1.2
    have hxl := hx.1.1 l
    nlinarith [hp' l]
  · exact ((hAA q ⟨hq.1, hpos⟩).continuousAt
      ((isOpen_pwDomainSet L).mem_nhds ⟨hq.1, hpos⟩)).continuousWithinAt

/-- Composition: if `w` is continuous and nonnegative on `ℝ^L_{++}`, then `p ↦ x(p, w(p))` is
continuous on `ℝ^L_{++}`. -/
theorem continuousOn_uDemand_comp {u : (Fin L → ℝ) → ℝ} (hc : ContinuousOn u (nonnegOrthant L))
    (hsq : StrictlyQuasiconcaveOn (nonnegOrthant L) u) {w : (Fin L → ℝ) → ℝ}
    (hwc : ContinuousOn w (posOrthant L)) (hw0 : ∀ p ∈ posOrthant L, 0 ≤ w p) :
    ContinuousOn (fun p => uDemand u p (w p)) (posOrthant L) := by
  have hpair : ContinuousOn (fun p : Fin L → ℝ => (p, w p)) (posOrthant L) :=
    ContinuousOn.prodMk continuousOn_id hwc
  have hmaps : Set.MapsTo (fun p : Fin L → ℝ => (p, w p)) (posOrthant L) (wealthDomain L) :=
    fun p hp => ⟨hp, hw0 p hp⟩
  have h := ContinuousOn.comp (continuousOn_uDemand hc hsq) hpair hmaps
  exact h

/-- **Exercise 17.B.2, the core** (MWG, p. 642). Let `u` be continuous and strongly monotone
on `ℝ^L₊`. If `pⁿ ≫ 0` tends to `p` with `p_ℓ = 0` for some `ℓ`, the wealths `wⁿ` tend to
`w > 0`, and `xⁿ ∈ x(pⁿ, wⁿ)`, then the bundles `xⁿ` cannot all lie below a bound `B`. -/
theorem demand_bounded_near_boundary_false {u : (Fin L → ℝ) → ℝ}
    (hc : ContinuousOn u (nonnegOrthant L)) (hm : UtilityStronglyMonotone u)
    {ps : ℕ → Fin L → ℝ} {p : Fin L → ℝ} (hps : ∀ n, StrictlyPositive (ps n))
    (hlim : Tendsto ps atTop (𝓝 p)) {l0 : Fin L} (hl0 : p l0 = 0) {ws : ℕ → ℝ} {wl : ℝ}
    (hwl : 0 < wl) (hws : Tendsto ws atTop (𝓝 wl)) {xs : ℕ → Fin L → ℝ}
    (hxs : ∀ n, xs n ∈ walrasianDemand u (ps n) (ws n)) {B : ℝ}
    (hB : ∀ n l, xs n l ≤ B) : False := by
  have hbox : ∀ n, xs n ∈ Set.Icc (0 : Fin L → ℝ) (fun _ => B) :=
    fun n => ⟨fun l => (hxs n).1.1 l, fun l => hB n l⟩
  obtain ⟨a, -, ψ, hψ, ha⟩ := isCompact_Icc.tendsto_subseq hbox
  have hwev : ∀ᶠ n in atTop, 0 < ws (ψ n) :=
    (hws.comp hψ.tendsto_atTop).eventually (lt_mem_nhds hwl)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hwev
  have hP : Tendsto (fun n => ps (ψ (n + N))) atTop (𝓝 p) :=
    (hlim.comp hψ.tendsto_atTop).comp (tendsto_add_atTop_nat N)
  have hW : Tendsto (fun n => ws (ψ (n + N))) atTop (𝓝 wl) :=
    (hws.comp hψ.tendsto_atTop).comp (tendsto_add_atTop_nat N)
  have hX : Tendsto (fun n => xs (ψ (n + N))) atTop (𝓝 a) :=
    ha.comp (tendsto_add_atTop_nat N)
  have hmem := demand_uhc_of_locallyCheaper (appendixA_isClosed_nonnegOrthant L) hc
    (locallyCheaperAt_nonnegOrthant hwl) (fun n => ps (ψ (n + N))) (fun n => ws (ψ (n + N)))
    (fun n => xs (ψ (n + N))) a (fun n => ⟨hps _, hN _ (by omega)⟩) hP hW
    (fun n => hxs _) hX
  have hempty := walrasianDemand_eq_empty hm hl0.le wl
  exact (Set.eq_empty_iff_forall_notMem.1 hempty) a hmem

end MWG.PositiveEquilibriumTheory
