/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGGeneralEquilibriumExamples.Tools
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-!
# Welfare properties of Walrasian equilibria in exchange economies (MWG Section 15.B, pp. 522-525)

* **First welfare theorem** (p. 524, Exercise 15.B.3): with locally nonsatiated preferences every
  Walrasian equilibrium allocation is Pareto optimal (`first_welfare_theorem`), and it lies on the
  contract curve (`walrasEqm_mem_contractCurve`). Both are proved for any number of consumers and
  goods, and for Definition 15.B.1 as printed.
* **Tangency** (p. 523): at an interior Pareto optimum of the Edgeworth box with differentiable
  utilities the gradients are proportional (`paretoOptimal_interior_tangency`).
* **Second welfare theorem** (p. 524): with continuous, convex and strongly monotone preferences
  and a strictly positive total endowment, every Pareto optimal allocation is supportable as an
  equilibrium with transfers (`second_welfare_theorem`, any number of consumers and goods; the
  proof separates the endowment from the set of aggregate bundles that make everybody better off
  by the Hahn-Banach theorem). The supporting prices are strictly positive.
* Figure 15.B.13(b): the transfers can be made by moving endowments on the budget line, in
  particular to the allocation itself, which is then a no-trade Walrasian equilibrium
  (`walrasEqm_of_endowment_transfer`, `walrasEqm_at_allocation`).
* **Footnote 4** (p. 525): after endowments are moved to a Pareto optimal `x*`, `x*` is the unique
  Walrasian equilibrium allocation under strictly convex preferences (`footnote_4_unique`); without
  strict convexity it need not be (`footnote_4_needs_strict_convexity`).
-/

namespace MWG.GeneralEquilibriumExamples

open MWG.ConsumerChoice MWG.ClassicalDemand Kreps.PreferenceProperties Filter Topology

variable {ι : Type*} [Fintype ι] {L : ℕ}

/-- **First fundamental welfare theorem** (MWG, p. 524; Exercise 15.B.3, p. 540). With consumption
sets `ℝ^L₊` and locally nonsatiated preferences, every Walrasian equilibrium allocation
(Definition 15.B.1 as printed) is Pareto optimal (Definition 15.B.2). -/
theorem first_welfare_theorem {E : ExchangeEconomy ι L} (hX : ∀ i, E.X i = nonnegOrthant L)
    (hlns : ∀ i, UtilityLNS (E.u i)) {p : Fin L → ℝ} {x : ι → Fin L → ℝ}
    (h : E.IsWalrasEqm p x) : E.IsParetoOptimal x := by
  have hd := (isWalrasEqm_iff_isDemandEqm hX hlns p x).1 h
  refine ⟨h.1, ?_⟩
  rintro ⟨x', hx', hle, i, hi⟩
  have hx'm : ∀ k, x' k ∈ nonnegOrthant L := fun k => hX k ▸ hx'.1 k
  -- weakly preferred bundles cost at least the endowment value, strictly preferred ones more
  have hge : ∀ k, p ⬝ᵥ E.ω k ≤ p ⬝ᵥ x' k := by
    intro k
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨y, hy, hpy, hu⟩ := (hlns k).exists_better p (hx'm k) hlt
    have := (hd.2 k).2 y ⟨hX k ▸ hy, hpy.le⟩
    linarith [hle k]
  have hgt : p ⬝ᵥ E.ω i < p ⬝ᵥ x' i := by
    by_contra hle'
    rw [not_lt] at hle'
    have := (hd.2 i).2 (x' i) ⟨hx'.1 i, hle'⟩
    linarith
  have hsum : ∑ k, p ⬝ᵥ x' k = ∑ k, p ⬝ᵥ E.ω k := by
    rw [← dotProduct_sum, ← dotProduct_sum, hx'.2, ExchangeEconomy.totalEndowment]
  have := Finset.sum_lt_sum (fun k _ => hge k) ⟨i, Finset.mem_univ i, hgt⟩
  linarith

/-- **Exercise 15.B.3** (MWG, p. 540). In an Edgeworth box economy with locally nonsatiated
preferences a Walrasian equilibrium is Pareto optimal (the book asks for a graphical argument). -/
theorem exercise_15_B_3 {E : EdgeworthEconomy} (hX : ∀ i, E.X i = nonnegOrthant 2)
    (hlns : ∀ i, UtilityLNS (E.u i)) {p : Fin 2 → ℝ} {x : Fin 2 → Fin 2 → ℝ}
    (h : E.IsWalrasEqm p x) : E.IsParetoOptimal x :=
  first_welfare_theorem hX hlns h

/-- **Section 15.B** (MWG, p. 524). Every Walrasian equilibrium allocation lies on the contract
curve: it is Pareto optimal and each consumer is at least as well off as at his endowment. -/
theorem walrasEqm_mem_contractCurve {E : ExchangeEconomy ι L}
    (hX : ∀ i, E.X i = nonnegOrthant L) (hlns : ∀ i, UtilityLNS (E.u i))
    (hω : ∀ i, E.ω i ∈ E.X i) {p : Fin L → ℝ} {x : ι → Fin L → ℝ} (h : E.IsWalrasEqm p x) :
    x ∈ E.contractCurve :=
  ⟨first_welfare_theorem hX hlns h, fun i => h.2 i _ ⟨hω i, le_rfl⟩⟩

/-- **Section 15.B** (MWG, p. 523). At a Pareto optimal allocation in the interior of the
Edgeworth box at which both utilities are differentiable, the indifference curves are tangent:
the gradients `∇u₁(x₁)` and `∇u₂(x₂)` are parallel. -/
theorem paretoOptimal_interior_tangency {E : EdgeworthEconomy}
    (hX : ∀ i, E.X i = nonnegOrthant 2) {x : Fin 2 → Fin 2 → ℝ} (hpo : E.IsParetoOptimal x)
    (hint : ∀ i l, 0 < x i l) {g₁ g₂ : (Fin 2 → ℝ) →L[ℝ] ℝ}
    (h₁ : HasFDerivAt (E.u 0) g₁ (x 0)) (h₂ : HasFDerivAt (E.u 1) g₂ (x 1)) :
    g₁ (Pi.single 0 1) * g₂ (Pi.single 1 1) = g₁ (Pi.single 1 1) * g₂ (Pi.single 0 1) := by
  by_contra hne
  set a0 := g₁ (Pi.single 0 1)
  set a1 := g₁ (Pi.single 1 1)
  set b0 := g₂ (Pi.single 0 1)
  set b1 := g₂ (Pi.single 1 1)
  set D := a0 * b1 - a1 * b0 with hD
  have hD0 : D ≠ 0 := sub_ne_zero.2 hne
  set d : Fin 2 → ℝ := ![(b1 + a1) / D, -(a0 + b0) / D] with hd
  have hg : ∀ g : (Fin 2 → ℝ) →L[ℝ] ℝ, g d = d 0 * g (Pi.single 0 1) + d 1 * g (Pi.single 1 1) :=
    by
    intro g
    have := LinearMap.pi_apply_eq_sum_univ g.toLinearMap d
    simp only [ContinuousLinearMap.coe_coe, Fin.sum_univ_two, smul_eq_mul] at this
    rw [this]
    congr 2 <;> congr 1 <;> funext j <;> fin_cases j <;> simp
  have hg1 : g₁ d = 1 := by
    rw [hg]
    simp only [hd, Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp
    rw [hD]
    ring
  have hg2 : g₂ d = -1 := by
    rw [hg]
    simp only [hd, Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp
    rw [hD]
    ring
  -- move along `d` for consumer 1 and along `-d` for consumer 2
  have hl1 : HasDerivAt (fun t : ℝ => x 0 + t • d) d 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const d).const_add (x 0)
  have hl2 : HasDerivAt (fun t : ℝ => x 1 - t • d) (-d) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const d).const_sub (x 1)
  have hc1 : HasDerivAt (fun t : ℝ => E.u 0 (x 0 + t • d)) 1 0 := by
    have := HasFDerivAt.comp_hasDerivAt (0 : ℝ) (by simpa using h₁) hl1
    simpa [Function.comp_def, hg1] using this
  have hc2 : HasDerivAt (fun t : ℝ => E.u 1 (x 1 - t • d)) 1 0 := by
    have := HasFDerivAt.comp_hasDerivAt (0 : ℝ) (by simpa using h₂) hl2
    simpa [Function.comp_def, hg2] using this
  have hint1 : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ l, 0 < (x 0 + t • d) l := by
    refine eventually_all.2 fun l => ?_
    have hc : Continuous fun t : ℝ => (x 0 + t • d) l := by fun_prop
    exact hc.continuousAt.eventually (lt_mem_nhds (by simpa using hint 0 l))
  have hint2 : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ l, 0 < (x 1 - t • d) l := by
    refine eventually_all.2 fun l => ?_
    have hc : Continuous fun t : ℝ => (x 1 - t • d) l := by fun_prop
    exact hc.continuousAt.eventually (lt_mem_nhds (by simpa using hint 1 l))
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), (∀ l, 0 < (x 0 + t • d) l) ∧ (∀ l, 0 < (x 1 - t • d) l) ∧
      E.u 1 (x 1 - (0 : ℝ) • d) < E.u 1 (x 1 - t • d) :=
    (hint1.filter_mono nhdsWithin_le_nhds).and ((hint2.filter_mono nhdsWithin_le_nhds).and
      (eventually_gt_of_deriv_pos hc2 one_pos))
  obtain ⟨t, -, ⟨hm1, hm2, hu2⟩, hu1⟩ := exists_pos_deriv_pos hc1 one_pos hev
  simp only [zero_smul, add_zero, sub_zero] at hu1 hu2
  set x' : Fin 2 → Fin 2 → ℝ := ![x 0 + t • d, x 1 - t • d] with hx'
  apply hpo.2
  refine ⟨x', ⟨fun i => ?_, ?_⟩, fun i => ?_, 0, by simpa [hx'] using hu1⟩
  · rw [hX i]
    fin_cases i
    · exact fun l => (hm1 l).le
    · exact fun l => (hm2 l).le
  · rw [← hpo.1.2]
    simp [hx', Fin.sum_univ_two]
  · fin_cases i
    · simpa [hx'] using hu1.le
    · simpa [hx'] using hu2.le

/-- Strong monotonicity gives weak monotonicity: `x ≤ y` implies `u(x) ≤ u(y)`. -/
theorem UtilityStronglyMonotone.le {u : (Fin L → ℝ) → ℝ} (h : UtilityStronglyMonotone u)
    {x y : Fin L → ℝ} (hx : x ∈ nonnegOrthant L) (hxy : x ≤ y) : u x ≤ u y := by
  by_cases he : y = x
  · rw [he]
  · exact (h.lt hx hxy he).le

/-- Adding a bundle to one consumer's consumption adds it to the aggregate. -/
theorem sum_add_ite_eq [DecidableEq ι] (y : ι → Fin L → ℝ) (i : ι) (d : Fin L → ℝ) :
    ∑ k, (y k + if k = i then d else 0) = ∑ k, y k + d := by
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

/-- The constant vector with entries `1`. -/
def onesVec (L : ℕ) : Fin L → ℝ := fun _ => 1

/-- `p·(c·𝟙) = c ∑_ℓ p_ℓ`. -/
theorem dotProduct_smul_onesVec (p : Fin L → ℝ) (c : ℝ) :
    p ⬝ᵥ (c • onesVec L) = c * ∑ l, p l := by
  simp only [dotProduct, onesVec, Pi.smul_apply, smul_eq_mul, mul_one, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

/-- With at least one good, strong monotonicity makes `x + c𝟙` (`c > 0`) strictly better. -/
theorem UtilityStronglyMonotone.lt_add_ones (hL : 0 < L) {u : (Fin L → ℝ) → ℝ}
    (h : UtilityStronglyMonotone u) {x : Fin L → ℝ} (hx : x ∈ nonnegOrthant L) {c : ℝ}
    (hc : 0 < c) : u x < u (x + c • onesVec L) := by
  refine h.lt hx (fun l => by simp [onesVec, hc.le]) fun he => ?_
  have := congrFun he ⟨0, hL⟩
  simp [onesVec, hc.ne'] at this

/-- **Second fundamental welfare theorem** (MWG, p. 524). If consumption sets are `ℝ^L₊`,
preferences are represented by continuous utilities and are convex (Definition 3.B.4) and strongly
monotone (Definition 3.B.2), and the total endowment is strictly positive, then every Pareto
optimal allocation `x*` is supportable as an equilibrium with transfers (Definition 15.B.3), with
strictly positive prices `p*` and transfers `Tᵢ = p*·x*ᵢ - p*·ωᵢ`. (The book states it for the
Edgeworth box; the proof works for any number of consumers and goods.) -/
theorem second_welfare_theorem (hL : 0 < L) {E : ExchangeEconomy ι L}
    (hX : ∀ i, E.X i = nonnegOrthant L) (hcont : ∀ i, ContinuousOn (E.u i) (nonnegOrthant L))
    (hconv : ∀ i, PrefConvex (nonnegOrthant L) (utilityPref (E.u i)))
    (hmono : ∀ i, UtilityStronglyMonotone (E.u i)) (hω : ∀ l, 0 < E.totalEndowment l)
    {x : ι → Fin L → ℝ} (hpo : E.IsParetoOptimal x) :
    ∃ p, StrictlyPositive p ∧ E.IsEqmWithTransfers p (fun i => p ⬝ᵥ x i - p ⬝ᵥ E.ω i) x := by
  classical
  have hxm : ∀ i, x i ∈ nonnegOrthant L := fun i => hX i ▸ hpo.1.1 i
  have hsumx : ∑ i, x i = E.totalEndowment := hpo.1.2
  obtain ⟨i₀⟩ : Nonempty ι := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    have := hω ⟨0, hL⟩
    simp [ExchangeEconomy.totalEndowment] at this
  -- the aggregate bundles that make everybody strictly better off, and their upper set `W`
  set V : Set (Fin L → ℝ) := {v | ∃ y : ι → Fin L → ℝ,
    (∀ i, y i ∈ nonnegOrthant L ∧ E.u i (x i) < E.u i (y i)) ∧ v = ∑ i, y i} with hV
  set W : Set (Fin L → ℝ) := {z | ∃ v ∈ V, ∀ l, v l < z l} with hW
  have hWconv : Convex ℝ W := by
    rintro z ⟨v, ⟨y, hy, rfl⟩, hvz⟩ z' ⟨v', ⟨y', hy', rfl⟩, hvz'⟩ a b ha hb hab
    refine ⟨∑ i, (a • y i + b • y' i), ⟨fun i => a • y i + b • y' i, fun i => ⟨?_, ?_⟩, rfl⟩, ?_⟩
    · exact fun l => by
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        exact add_nonneg (mul_nonneg ha ((hy i).1 l)) (mul_nonneg hb ((hy' i).1 l))
    · exact lt_of_lt_of_le (lt_min (hy i).2 (hy' i).2)
        (quasiconcave_of_prefConvex (hconv i) (hy i).1 (hy' i).1 ha hb hab)
    · intro l
      simp only [Finset.sum_add_distrib, ← Finset.smul_sum, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul]
      have h1 := hvz l
      have h2 := hvz' l
      rcases eq_or_lt_of_le ha with ha0 | ha0
      · subst ha0
        have hb1 : b = 1 := by linarith
        subst hb1
        linarith
      · nlinarith [mul_lt_mul_of_pos_left h1 ha0, mul_le_mul_of_nonneg_left h2.le hb]
  have hWopen : IsOpen W := by
    have : W = ⋃ v ∈ V, ⋂ l, {z : Fin L → ℝ | v l < z l} := by
      ext z
      simp only [hW, Set.mem_iUnion, Set.mem_iInter, exists_prop]
      rfl
    rw [this]
    exact isOpen_biUnion fun v _ =>
      isOpen_iInter_of_finite fun l => isOpen_lt continuous_const (continuous_apply l)
  have hnot : E.totalEndowment ∉ W := by
    rintro ⟨v, ⟨y, hy, rfl⟩, hlt⟩
    set d := E.totalEndowment - ∑ i, y i with hd
    have hdpos : ∀ l, 0 < d l := fun l => by
      simp only [hd, Pi.sub_apply]
      linarith [hlt l]
    set y' : ι → Fin L → ℝ := fun k => y k + if k = i₀ then d else 0 with hy'
    apply hpo.2
    refine ⟨y', ⟨fun k => ?_, ?_⟩, fun k => ?_, i₀, ?_⟩
    · rw [hX k]
      intro l
      simp only [hy', Pi.add_apply]
      split_ifs
      · exact add_nonneg ((hy k).1 l) (hdpos l).le
      · simpa using (hy k).1 l
    · rw [hy', sum_add_ite_eq, hd]
      abel
    · refine ((hy k).2.trans_le ?_).le
      refine (hmono k).le (hy k).1 fun l => ?_
      simp only [hy', Pi.add_apply]
      split_ifs
      · linarith [hdpos l]
      · simp
    · refine lt_of_lt_of_le (hy i₀).2 ((hmono i₀).le (hy i₀).1 fun l => ?_)
      simp only [hy', ↓reduceIte, Pi.add_apply]
      linarith [hdpos l]
  obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hWconv hWopen hnot
  set p : Fin L → ℝ := fun l => -f (Pi.single l 1) with hp
  have hfp : ∀ z, f z = -(p ⬝ᵥ z) := by
    intro z
    have := LinearMap.pi_apply_eq_sum_univ f.toLinearMap z
    simp only [ContinuousLinearMap.coe_coe, smul_eq_mul] at this
    rw [this, dotProduct, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    have he : (fun j => if l = j then (1 : ℝ) else 0) = Pi.single l 1 := by
      funext j
      simp [Pi.single_apply, eq_comm]
    rw [he, hp]
    ring
  have hWp : ∀ z ∈ W, p ⬝ᵥ E.totalEndowment < p ⬝ᵥ z := by
    intro z hz
    have := hf z hz
    rw [hfp, hfp] at this
    linarith
  set S := ∑ l, |p l| with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun l _ => abs_nonneg _
  have hpone : ∀ c : ℝ, 0 ≤ c → p ⬝ᵥ (c • onesVec L) ≤ c * S := by
    intro c hc
    rw [dotProduct_smul_onesVec]
    exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun l _ => le_abs_self _) hc
  -- (5) aggregate bundles making everybody strictly better off cost at least `p·ω̄`
  have hP : ∀ y : ι → Fin L → ℝ, (∀ i, y i ∈ nonnegOrthant L ∧ E.u i (x i) < E.u i (y i)) →
      p ⬝ᵥ E.totalEndowment ≤ p ⬝ᵥ ∑ i, y i := by
    intro y hy
    by_contra hlt
    rw [not_le] at hlt
    set gap := p ⬝ᵥ E.totalEndowment - p ⬝ᵥ ∑ i, y i with hgap
    have hgap0 : 0 < gap := by linarith
    set ε := gap / (S + 1) with hε
    have hε0 : 0 < ε := div_pos hgap0 (by linarith)
    have hmem : ∑ i, y i + ε • onesVec L ∈ W :=
      ⟨∑ i, y i, ⟨y, hy, rfl⟩, fun l => by simp [onesVec, hε0]⟩
    have h1 := hWp _ hmem
    have h2 := hpone ε hε0.le
    rw [dotProduct_add] at h1
    have h3 : ε * S < gap := by
      rw [hε, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
      nlinarith
    linarith
  -- (6) prices are nonnegative
  have hpnn : ∀ l, 0 ≤ p l := by
    intro l
    by_contra hneg
    rw [not_le] at hneg
    set y : ι → Fin L → ℝ := fun k => x k + (1 : ℝ) • onesVec L with hy
    have hyb : ∀ k, y k ∈ nonnegOrthant L ∧ E.u k (x k) < E.u k (y k) := fun k =>
      ⟨fun l => by simp [hy, onesVec, add_nonneg (hxm k l)],
        (hmono k).lt_add_ones hL (hxm k) one_pos⟩
    set M := (|p ⬝ᵥ ∑ k, y k - p ⬝ᵥ E.totalEndowment| + 1) / (-p l) with hM
    have hM0 : 0 < M := div_pos (by positivity) (by linarith)
    set y' : ι → Fin L → ℝ := fun k => y k + if k = i₀ then M • Pi.single l 1 else 0 with hy'
    have hy'b : ∀ k, y' k ∈ nonnegOrthant L ∧ E.u k (x k) < E.u k (y' k) := by
      intro k
      have hle : y k ≤ y' k := fun j => by
        simp only [hy', Pi.add_apply]
        split_ifs
        · simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul]
          split_ifs <;> linarith
        · simp
      exact ⟨fun j => le_trans ((hyb k).1 j) (hle j),
        lt_of_lt_of_le (hyb k).2 ((hmono k).le (hyb k).1 hle)⟩
    have := hP y' hy'b
    rw [hy', sum_add_ite_eq, dotProduct_add, dotProduct_smul, smul_eq_mul] at this
    have hpl : p ⬝ᵥ Pi.single l 1 = p l := by simp
    rw [hpl] at this
    have hMp : M * p l = -(|p ⬝ᵥ ∑ k, y k - p ⬝ᵥ E.totalEndowment| + 1) := by
      rw [hM, div_mul_eq_mul_div, div_eq_iff (by linarith)]
      ring
    rw [hMp] at this
    have := le_abs_self (p ⬝ᵥ ∑ k, y k - p ⬝ᵥ E.totalEndowment)
    linarith
  have hS' : S = ∑ l, p l := Finset.sum_congr rfl fun l _ => abs_of_nonneg (hpnn l)
  -- (7) quasi-equilibrium: strictly preferred bundles cost at least as much
  have hq : ∀ i, ∀ y ∈ nonnegOrthant L, E.u i (x i) < E.u i y → p ⬝ᵥ x i ≤ p ⬝ᵥ y := by
    intro i y hy hu
    by_contra hlt
    rw [not_le] at hlt
    set gap := p ⬝ᵥ x i - p ⬝ᵥ y with hgap
    have hgap0 : 0 < gap := by linarith
    set n : ℝ := (Fintype.card ι : ℝ) with hn
    have hn0 : 0 ≤ n := Nat.cast_nonneg _
    set δ := gap / (2 * (n * S + 1)) with hδ
    have hnS : 0 ≤ n * S := mul_nonneg hn0 hS0
    have hδ0 : 0 < δ := div_pos hgap0 (by linarith)
    set Y : ι → Fin L → ℝ := fun k =>
      (x k + δ • onesVec L) + if k = i then y - x i - δ • onesVec L else 0 with hY
    have hYb : ∀ k, Y k ∈ nonnegOrthant L ∧ E.u k (x k) < E.u k (Y k) := by
      intro k
      by_cases hk : k = i
      · have : Y k = y := by
          simp only [hY, hk, ↓reduceIte]
          abel
        rw [this, hk]
        exact ⟨hy, hu⟩
      · have : Y k = x k + δ • onesVec L := by simp [hY, hk]
        rw [this]
        exact ⟨fun l => by simp [onesVec, add_nonneg (hxm k l) hδ0.le],
          (hmono k).lt_add_ones hL (hxm k) hδ0⟩
    have h1 := hP Y hYb
    rw [hY, sum_add_ite_eq, Finset.sum_add_distrib, hsumx] at h1
    simp only [Finset.sum_const, Finset.card_univ, dotProduct_add, dotProduct_sub] at h1
    have e1 : p ⬝ᵥ (Fintype.card ι • (δ • onesVec L)) = n * (δ * S) := by
      rw [← Nat.cast_smul_eq_nsmul ℝ, dotProduct_smul, dotProduct_smul_onesVec, hS', hn,
        smul_eq_mul]
    have e2 : p ⬝ᵥ (δ • onesVec L) = δ * S := by rw [dotProduct_smul_onesVec, hS']
    rw [e1, e2] at h1
    have h2 : n * (δ * S) < gap := by
      have : n * (δ * S) = δ * (n * S) := by ring
      rw [this, hδ, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
      nlinarith
    have h3 : 0 ≤ δ * S := mul_nonneg hδ0.le hS0
    linarith
  -- (8) prices are strictly positive
  have hpne : ∃ k, p k ≠ 0 := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    set y : ι → Fin L → ℝ := fun k => x k + (1 : ℝ) • onesVec L
    have hmem : ∑ k, y k + (1 : ℝ) • onesVec L ∈ W :=
      ⟨∑ k, y k, ⟨y, fun k => ⟨fun l => by simp [y, onesVec, add_nonneg (hxm k l)],
        (hmono k).lt_add_ones hL (hxm k) one_pos⟩, rfl⟩, fun l => by simp [onesVec]⟩
    have := hWp _ hmem
    simp [dotProduct, hall] at this
  have hppos : StrictlyPositive p := by
    intro l
    rcases eq_or_lt_of_le (hpnn l) with h0 | h0
    · exfalso
      obtain ⟨k, hk⟩ := hpne
      have hpk : 0 < p k := lt_of_le_of_ne (hpnn k) (Ne.symm hk)
      have hkl : k ≠ l := fun h => by rw [h] at hk; exact hk h0.symm
      obtain ⟨i, hi⟩ : ∃ i, 0 < x i k := by
        by_contra hall
        simp only [not_exists, not_lt] at hall
        have h1 : ∑ i, x i k ≤ 0 := Finset.sum_nonpos fun i _ => hall i
        have h2 := hω k
        rw [← hsumx, Finset.sum_apply] at h2
        linarith
      set g : ℝ → Fin L → ℝ := fun t => x i + Pi.single l 1 - (t * x i k) • Pi.single k 1
      have hgc : Continuous g := by fun_prop
      have hgm : ∀ t ∈ Set.Icc (0 : ℝ) 1, g t ∈ nonnegOrthant L := by
        intro t ht j
        simp only [g, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
        by_cases hjk : j = k
        · subst hjk
          simp only [hkl, ↓reduceIte, add_zero, mul_one]
          nlinarith [ht.2, hi]
        · simp only [hjk, ↓reduceIte, mul_zero, sub_zero]
          split_ifs <;> linarith [hxm i j]
      have hg0 : E.u i (x i) < E.u i (g 0) := by
        refine (hmono i).lt (hxm i) (fun j => ?_) fun he => ?_
        · simp only [g, zero_mul, zero_smul, sub_zero, Pi.add_apply, Pi.single_apply]
          split_ifs <;> linarith
        · have := congrFun he l
          simp [g] at this
      obtain ⟨t, ht0, ht1, ht⟩ := exists_pos_continuous_lt (hcont i) hgc hgm hg0
      have := hq i (g t) (hgm t ⟨ht0.le, ht1⟩) ht
      simp only [g, dotProduct_sub, dotProduct_add, dotProduct_smul, smul_eq_mul] at this
      have e1 : p ⬝ᵥ Pi.single l 1 = p l := by simp
      have e2 : p ⬝ᵥ Pi.single k 1 = p k := by simp
      rw [e1, e2, ← h0] at this
      nlinarith [mul_pos (mul_pos ht0 hi) hpk]
    · exact h0
  -- (9) the equilibrium with transfers
  refine ⟨p, hppos, hpo.1, ?_, fun i y hyX hb => ?_⟩
  · rw [Finset.sum_sub_distrib, ← dotProduct_sum, ← dotProduct_sum, hsumx,
      ExchangeEconomy.totalEndowment, sub_self]
  · have hy : y ∈ nonnegOrthant L := hX i ▸ hyX
    simp only [add_sub_cancel] at hb
    by_contra hlt
    rw [not_le] at hlt
    have hge := hq i y hy hlt
    by_cases hpy : p ⬝ᵥ y ≤ 0
    · have hy0 := eq_zero_of_dotProduct_nonpos hppos hy hpy
      have hx0 := eq_zero_of_dotProduct_nonpos hppos (hxm i) (hge.trans hpy)
      rw [hy0, hx0] at hlt
      exact lt_irrefl _ hlt
    · rw [not_le] at hpy
      set g : ℝ → Fin L → ℝ := fun t => (1 - t / 2) • y
      have hgc : Continuous g := by fun_prop
      have hgm : ∀ t ∈ Set.Icc (0 : ℝ) 1, g t ∈ nonnegOrthant L := by
        intro t ht j
        simp only [g, Pi.smul_apply, smul_eq_mul]
        exact mul_nonneg (by linarith [ht.2]) (hy j)
      have hg0 : E.u i (x i) < E.u i (g 0) := by simpa [g] using hlt
      obtain ⟨t, ht0, ht1, ht⟩ := exists_pos_continuous_lt (hcont i) hgc hgm hg0
      have := hq i (g t) (hgm t ⟨ht0.le, ht1⟩) ht
      simp only [g, dotProduct_smul, smul_eq_mul] at this
      nlinarith

/-- **Second fundamental welfare theorem** (MWG, p. 524), the Edgeworth box statement: with
continuous, convex and strongly monotone preferences (and `ω̄ ≫ 0`), every Pareto optimal
allocation is supportable as an equilibrium with transfers. -/
theorem second_welfare_theorem_edgeworth {E : EdgeworthEconomy}
    (hX : ∀ i, E.X i = nonnegOrthant 2) (hcont : ∀ i, ContinuousOn (E.u i) (nonnegOrthant 2))
    (hconv : ∀ i, PrefConvex (nonnegOrthant 2) (utilityPref (E.u i)))
    (hmono : ∀ i, UtilityStronglyMonotone (E.u i)) (hω : ∀ l, 0 < E.totalEndowment l)
    {x : Fin 2 → Fin 2 → ℝ} (hpo : E.IsParetoOptimal x) : E.IsSupportable x := by
  obtain ⟨p, -, h⟩ := second_welfare_theorem two_pos hX hcont hconv hmono hω hpo
  exact ⟨p, _, h⟩

/-- Under local nonsatiation, an equilibrium with transfers exhausts every consumer's wealth:
`p·x*ᵢ = p·ωᵢ + Tᵢ`. -/
theorem ExchangeEconomy.IsEqmWithTransfers.wealth_eq {E : ExchangeEconomy ι L}
    (hX : ∀ i, E.X i = nonnegOrthant L) (hlns : ∀ i, UtilityLNS (E.u i)) {p : Fin L → ℝ}
    {T : ι → ℝ} {x : ι → Fin L → ℝ} (h : E.IsEqmWithTransfers p T x) (i : ι) :
    p ⬝ᵥ x i = p ⬝ᵥ E.ω i + T i := by
  have hge : ∀ k, p ⬝ᵥ E.ω k + T k ≤ p ⬝ᵥ x k := by
    intro k
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨y, hy, hpy, hu⟩ := (hlns k).exists_better p (hX k ▸ h.1.1 k) hlt
    have := h.2.2 k y (hX k ▸ hy) hpy.le
    linarith
  have hsum : ∑ k, (p ⬝ᵥ E.ω k + T k) = ∑ k, p ⬝ᵥ x k := by
    rw [Finset.sum_add_distrib, h.2.1, add_zero, ← dotProduct_sum, ← dotProduct_sum, h.1.2,
      ExchangeEconomy.totalEndowment]
  exact ((Finset.sum_eq_sum_iff_of_le fun k _ => hge k).1 hsum i (Finset.mem_univ i)).symm

/-- **Figure 15.B.13(b)** (MWG, p. 525). Wealth transfers can be replaced by transfers of
endowments: if `(p*, T)` supports `x*` and the new endowments `ω'ᵢ` (with the same total) satisfy
`p*·ω'ᵢ = p*·ωᵢ + Tᵢ`, then `(p*, x*)` is a Walrasian equilibrium of the economy with
endowments `ω'`. -/
theorem walrasEqm_of_endowment_transfer {E : ExchangeEconomy ι L} {p : Fin L → ℝ}
    {T : ι → ℝ} {x : ι → Fin L → ℝ} (h : E.IsEqmWithTransfers p T x) (ω' : ι → Fin L → ℝ)
    (hsum : ∑ i, ω' i = ∑ i, E.ω i) (hval : ∀ i, p ⬝ᵥ ω' i = p ⬝ᵥ E.ω i + T i) :
    ({ E with ω := ω' } : ExchangeEconomy ι L).IsWalrasEqm p x := by
  refine ⟨⟨h.1.1, ?_⟩, fun i y hy => h.2.2 i y hy.1 ?_⟩
  · change ∑ i, x i = ∑ i, ω' i
    rw [hsum]
    exact h.1.2
  · rw [← hval i]
    exact hy.2

/-- **Figure 15.B.13(b)** (MWG, p. 525). Under local nonsatiation, moving the endowments directly to
an allocation supported with transfers makes it a Walrasian equilibrium with no trade. -/
theorem walrasEqm_at_allocation {E : ExchangeEconomy ι L} (hX : ∀ i, E.X i = nonnegOrthant L)
    (hlns : ∀ i, UtilityLNS (E.u i)) {p : Fin L → ℝ} {T : ι → ℝ} {x : ι → Fin L → ℝ}
    (h : E.IsEqmWithTransfers p T x) :
    ({ E with ω := x } : ExchangeEconomy ι L).IsWalrasEqm p x :=
  walrasEqm_of_endowment_transfer h x h.1.2 fun i => h.wealth_eq hX hlns i

/-- **Footnote 4** (MWG, p. 525). If the endowments are the Pareto optimal allocation `x*` itself
and preferences are strictly convex (Definition 3.B.5), then `x*` is the unique Walrasian
equilibrium allocation. -/
theorem footnote_4_unique {E : ExchangeEconomy ι L} (hX : ∀ i, E.X i = nonnegOrthant L)
    (hsc : ∀ i, PrefStrictlyConvex (nonnegOrthant L) (utilityPref (E.u i)))
    (hpo : E.IsParetoOptimal E.ω) {p : Fin L → ℝ} {x : ι → Fin L → ℝ}
    (h : E.IsDemandEqm p x) : x = E.ω := by
  classical
  have hωm : ∀ i, E.ω i ∈ nonnegOrthant L := fun i => hX i ▸ hpo.1.1 i
  have hxm : ∀ i, x i ∈ nonnegOrthant L := fun i => hX i ▸ h.1.1 i
  have hge : ∀ i, E.u i (E.ω i) ≤ E.u i (x i) := fun i => (h.2 i).2 _ ⟨hpo.1.1 i, le_rfl⟩
  have heq : ∀ i, E.u i (x i) = E.u i (E.ω i) := by
    intro i
    refine le_antisymm ?_ (hge i)
    by_contra hlt
    exact hpo.2 ⟨x, h.1, hge, i, not_le.1 hlt⟩
  by_contra hne
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ E.ω i := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    exact hne (funext hall)
  set m : ι → Fin L → ℝ := fun k => (1 / 2 : ℝ) • x k + (1 - 1 / 2 : ℝ) • E.ω k with hm
  have hmm : ∀ k, m k ∈ nonnegOrthant L := fun k l => by
    simp only [hm, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [hxm k l, hωm k l]
  have hmge : ∀ k, E.u k (E.ω k) ≤ E.u k (m k) := by
    intro k
    by_cases hk : x k = E.ω k
    · simp [hm, hk, ← add_smul]
    · exact (hsc k (E.ω k) (hωm k) (x k) (hxm k) (E.ω k) (hωm k) (heq k).ge le_rfl hk
        (1 / 2) (by norm_num) (by norm_num)).1
  have hmgt : E.u i (E.ω i) < E.u i (m i) :=
    not_le.1 (hsc i (E.ω i) (hωm i) (x i) (hxm i) (E.ω i) (hωm i) (heq i).ge le_rfl hi
      (1 / 2) (by norm_num) (by norm_num)).2
  apply hpo.2
  refine ⟨m, ⟨fun k => hX k ▸ hmm k, ?_⟩, hmge, i, hmgt⟩
  simp only [hm, Finset.sum_add_distrib, ← Finset.smul_sum, h.1.2]
  change (1 / 2 : ℝ) • E.totalEndowment + (1 - 1 / 2 : ℝ) • E.totalEndowment = E.totalEndowment
  rw [← add_smul]
  norm_num

/-- The linear utility `u(x) = x₁ + x₂`. -/
def linearUtility (x : Fin 2 → ℝ) : ℝ := x 0 + x 1

/-- The Edgeworth box economy of `footnote_4_needs_strict_convexity`: both consumers have the
linear utility `x₁ + x₂` and endowment `(1, 1)`. -/
def footnote4Economy : EdgeworthEconomy :=
  ExchangeEconomy.ofOrthant (fun _ => linearUtility) (fun _ => ![1, 1])

/-- **Footnote 4** (MWG, p. 525): strict convexity is needed. With linear (convex, not strictly
convex) preferences, the endowment `((1,1),(1,1))` is Pareto optimal, yet `((2,0),(0,2))` is also
a Walrasian equilibrium allocation (at `p = (1, 1)`). -/
theorem footnote_4_needs_strict_convexity :
    footnote4Economy.IsParetoOptimal footnote4Economy.ω ∧
      footnote4Economy.IsDemandEqm ![1, 1] ![![2, 0], ![0, 2]] ∧
      (![![2, 0], ![0, 2]] : Fin 2 → Fin 2 → ℝ) ≠ footnote4Economy.ω := by
  have hsumω : footnote4Economy.totalEndowment = ![2, 2] := by
    funext l
    fin_cases l <;> simp [ExchangeEconomy.totalEndowment, footnote4Economy,
      ExchangeEconomy.ofOrthant]
  refine ⟨⟨⟨fun i l => ?_, rfl⟩, ?_⟩, ⟨⟨fun i l => ?_, ?_⟩, fun i => ⟨⟨fun l => ?_, ?_⟩, ?_⟩⟩, ?_⟩
  · fin_cases l <;> simp [footnote4Economy, ExchangeEconomy.ofOrthant]
  · rintro ⟨x', hx', hle, i, hi⟩
    have hs := congrFun hx'.2 0
    have hs1 := congrFun hx'.2 1
    rw [hsumω] at hs hs1
    simp only [Fin.sum_univ_two, Finset.sum_apply] at hs hs1
    simp only [footnote4Economy, ExchangeEconomy.ofOrthant, linearUtility] at hle hi
    have h0 := hle 0
    have h1 := hle 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1 hi hs hs1
    fin_cases i <;> simp at hi <;> linarith
  · fin_cases i <;> fin_cases l <;> simp
  · rw [hsumω]
    funext l
    fin_cases l <;> simp [Fin.sum_univ_two]
  · fin_cases i <;> fin_cases l <;> simp
  · fin_cases i <;> simp [footnote4Economy, ExchangeEconomy.ofOrthant, dotProduct,
      Fin.sum_univ_two] <;> norm_num
  · intro y hy
    have hb := hy.2
    fin_cases i <;> simp [footnote4Economy, ExchangeEconomy.ofOrthant, dotProduct,
      Fin.sum_univ_two, linearUtility] at hb ⊢ <;> norm_num at hb ⊢ <;> linarith
  · intro he
    have := congrFun (congrFun he 0) 1
    simp [footnote4Economy, ExchangeEconomy.ofOrthant] at this

end MWG.GeneralEquilibriumExamples
