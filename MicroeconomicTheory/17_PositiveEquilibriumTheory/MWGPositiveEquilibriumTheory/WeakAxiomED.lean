/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPositiveEquilibriumTheory.LinearActivities
import MWGPositiveEquilibriumTheory.CobbDouglasEconomy
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Order.Interval.Set.Infinite

/-!
# The weak axiom for aggregate excess demand (MWG Section 17.F, pp. 606-609)

* **Constant returns convex technologies** (`IsCRConvexTech`): `Y` convex with `αy ∈ Y` for
  `α ≥ 0`. The economy `crEconomy E Y θ` adds one such firm to the exchange economy `E`
  (Chapter 16's `PrivPrefEconomy`). Maximum profits are zero (`cr_profit_zero`, footnote 36).
* **Proposition 17.F.1** (`proposition_17_F_1`): `p` is a Walrasian equilibrium price vector iff
  (i) `p·y ≤ 0` for all `y ∈ Y` and (ii) `z(p) ∈ Y` (`IsCREqmPrice`). Footnote 36: pure exchange
  is `Y = -ℝ^L_+` (`footnote_17_36`).
* **Definition 17.F.1** (`WeakAxiomED`): `z(p) ≠ z(p')` and `p·z(p') ≤ 0` imply `p'·z(p) > 0`.
  The excess demand of a single consumer satisfies it (`wa_indivExcessDemand`, p. 608).
* **p. 608 and Figure 17.F.1**: if the weak axiom fails at `p, p'`, both are equilibria for the
  closed convex cone `Y* = {y : p·y ≤ 0, p'·y ≤ 0}` (`wa_violation_two_eqm`).
* **Proposition 17.F.2**: uniqueness for every closed constant returns `Y` implies the weak
  axiom (`proposition_17_F_2_necessity`); the weak axiom implies that the equilibrium price set is
  convex (`proposition_17_F_2_convex`, for any `Y`), so a finite normalized equilibrium set has
  at most one element (`proposition_17_F_2_finite`); with (i)-(v) and regularity the normalized
  exchange equilibrium is unique (`proposition_17_F_2_regular`). Footnote 39: with continuity,
  all equilibria have the same `z(p)` (`footnote_17_39`).
* Instances: one Cobb-Douglas consumer (`cd1_weakAxiom`, `cd1_unique_cr_eqm`).
-/

namespace MWG.PositiveEquilibriumTheory

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.GeneralEquilibriumExamples MWG.Production
open MWG.WelfareTheorems
open MWG.CompetitiveMarkets (Allocation)

variable {L : ℕ}

/-! ### Constant returns technologies and Proposition 17.F.1 -/

/-- **Section 17.F** (MWG, p. 607). A constant returns, convex technology: `Y ⊆ ℝ^L` is convex and
a cone (`y ∈ Y`, `α ≥ 0` imply `αy ∈ Y`). -/
def IsCRConvexTech (Y : Set (Fin L → ℝ)) : Prop :=
  Convex ℝ Y ∧ ∀ y ∈ Y, ∀ α : ℝ, 0 ≤ α → α • y ∈ Y

/-- **Proposition 17.F.1** (MWG, p. 607), conditions (i)-(ii): `p ≫ 0` (the domain of `z`),
`p·y ≤ 0` for every `y ∈ Y`, and `z(p) ∈ Y`. -/
def IsCREqmPrice (z : (Fin L → ℝ) → Fin L → ℝ) (Y : Set (Fin L → ℝ)) (p : Fin L → ℝ) : Prop :=
  p ∈ posOrthant L ∧ (∀ y ∈ Y, p ⬝ᵥ y ≤ 0) ∧ z p ∈ Y

/-- **Section 17.F** (MWG, p. 607). The exchange economy `E` with one firm operating the
technology `Y`, owned in shares `θᵢ`. -/
def crEconomy {ι : Type*} (E : ExchangeEconomy ι L) (Y : Set (Fin L → ℝ)) (θ : ι → ℝ) :
    PrivPrefEconomy ι Unit L where
  X := E.X
  pref := fun i => utilityPref (E.u i)
  Y := fun _ => Y
  ωi := E.ω
  θ := fun i _ => θ i

/-- **Footnote 36** (MWG, p. 607). With a cone `Y`, maximum profits are zero: a profit maximizing
`y` has `p·y = 0`. -/
theorem cr_profit_zero {Y : Set (Fin L → ℝ)} (hY : ∀ y ∈ Y, ∀ α : ℝ, 0 ≤ α → α • y ∈ Y)
    {p y : Fin L → ℝ} (hy : y ∈ supply Y p) : p ⬝ᵥ y = 0 := by
  have h0 := hy.2 _ (hY y hy.1 0 le_rfl)
  have h2 := hy.2 _ (hY y hy.1 2 (by norm_num))
  rw [zero_smul, dotProduct_zero] at h0
  rw [dotProduct_smul, smul_eq_mul] at h2
  linarith

/-- The convex combination `a p + b p'` (`a, b ≥ 0`, `a + b = 1`) of two price vectors `≫ 0` is
`≫ 0`. -/
theorem convex_posOrthant (L : ℕ) : Convex ℝ (posOrthant L) := by
  intro p hp p' hp' a b ha hb hab l
  have h1 := hp l
  have h2 := hp' l
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  nlinarith [min_le_left (p l) (p' l), min_le_right (p l) (p' l), lt_min h1 h2]

variable {ι : Type*} [Fintype ι]

/-- Walras' law for the excess demand of an exchange economy with locally nonsatiated consumers
(strongly monotone preferences): `p·z(p) = 0` at `p ≫ 0`. -/
theorem wa_excessDemand_walras {E : ExchangeEconomy ι L} (hX : ∀ i, E.X i = nonnegOrthant L)
    (hu : ∀ i, StandardUtility (E.u i)) (hω : ∀ i, E.ω i ∈ nonnegOrthant L) {p : Fin L → ℝ}
    (hp : p ∈ posOrthant L) : p ⬝ᵥ excessDemand E p = 0 := by
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · simp [dotProduct]
  unfold excessDemand indivExcessDemand
  rw [dotProduct_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [dotProduct_sub, ed_budget_eq hX ((hu i).2.2.lns hL)
    (demandFn_mem E (demand_nonempty hX (hu i).1 (hω i) hp)), sub_self]

/-- **Proposition 17.F.1** (MWG, p. 607). In the economy formed by `E` (continuous, strictly
convex, strongly monotone preferences on `ℝ^L₊`, endowments in `ℝ^L₊`) and a constant returns
technology `Y`, `p` is a Walrasian equilibrium price vector iff `p ≫ 0`, (i) `p·y ≤ 0` for every
`y ∈ Y` and (ii) `z(p) ∈ Y`. The equilibrium consumptions are `xᵢ(p, p·ωᵢ)` and production is
`z(p)`. -/
theorem proposition_17_F_1 [Nonempty ι] {E : ExchangeEconomy ι L}
    (hX : ∀ i, E.X i = nonnegOrthant L) (hu : ∀ i, StandardUtility (E.u i))
    (hω : ∀ i, E.ω i ∈ nonnegOrthant L) {Y : Set (Fin L → ℝ)}
    (hY : ∀ y ∈ Y, ∀ α : ℝ, 0 ≤ α → α • y ∈ Y) (θ : ι → ℝ) (p : Fin L → ℝ) :
    (∃ x y, (crEconomy E Y θ).IsWalrasEqm ⟨x, fun _ => y⟩ p) ↔
      IsCREqmPrice (excessDemand E) Y p := by
  constructor
  · rintro ⟨x, y, hy, hx, hc⟩
    have hpy := cr_profit_zero hY (hy ())
    have hw : ∀ i, (crEconomy E Y θ).wealth ⟨x, fun _ => y⟩ p i = p ⬝ᵥ E.ω i := fun i => by
      simp [PrivPrefEconomy.wealth, crEconomy, hpy]
    have hxd : ∀ i, x i ∈ E.demand i p := fun i => by
      have := hx i
      rw [hw i] at this
      exact this
    have hp : p ∈ posOrthant L := by
      intro l
      by_contra hl
      rw [not_lt] at hl
      let i : ι := Classical.arbitrary ι
      have hmem := hxd i
      simp only [ExchangeEconomy.demand, hX i] at hmem
      exact (Set.eq_empty_iff_forall_notMem.1 (walrasianDemand_eq_empty (hu i).2.2 hl _)) _ hmem
    have hxe : ∀ i, x i = demandFn E i p := fun i =>
      demand_subsingleton hX (hu i).2.1 p (hxd i) (demandFn_mem E ⟨x i, hxd i⟩)
    refine ⟨hp, fun y' hy' => ?_, ?_⟩
    · have := (hy ()).2 y' hy'
      simpa [crEconomy, hpy] using this
    · have hz : excessDemand E p = y := by
        rw [excessDemand_eq, ExchangeEconomy.totalEndowment]
        simp only [crEconomy, Finset.univ_unique, Finset.sum_singleton] at hc
        have hx' : x = fun i => demandFn E i p := funext hxe
        rw [← hx', hc]
        abel
      rw [hz]
      exact (hy ()).1
  · rintro ⟨hp, hpY, hzY⟩
    have hval : p ⬝ᵥ excessDemand E p = 0 := wa_excessDemand_walras hX hu hω hp
    refine ⟨fun i => demandFn E i p, excessDemand E p, fun _ => ⟨hzY, fun y' hy' => ?_⟩,
      fun i => ?_, ?_⟩
    · rw [hval]
      exact hpY y' hy'
    · have hw : (crEconomy E Y θ).wealth ⟨fun i => demandFn E i p,
          fun _ => excessDemand E p⟩ p i = p ⬝ᵥ E.ω i := by
        simp [PrivPrefEconomy.wealth, crEconomy, hval]
      rw [hw]
      exact demandFn_mem E (demand_nonempty hX (hu i).1 (hω i) hp)
    · simp only [crEconomy, Finset.univ_unique, Finset.sum_singleton]
      rw [excessDemand_eq, ExchangeEconomy.totalEndowment]
      abel

/-- **Footnote 36** (MWG, p. 607). Pure exchange is the special case `Y = -ℝ^L_+`: it is a closed,
constant returns, convex technology, and with Walras' law `p` satisfies (i)-(ii) of Proposition
17.F.1 for it iff `p` is an equilibrium price vector of the exchange economy (`z(p) = 0`). -/
theorem footnote_17_36 {z : (Fin L → ℝ) → Fin L → ℝ} (hW : EDWalrasLaw z) :
    IsCRConvexTech {y : Fin L → ℝ | ∀ l, y l ≤ 0} ∧ IsClosed {y : Fin L → ℝ | ∀ l, y l ≤ 0} ∧
      ∀ p, IsCREqmPrice z {y | ∀ l, y l ≤ 0} p ↔ IsEqmPrice z p := by
  refine ⟨⟨?_, fun y hy α hα l => ?_⟩, ?_, fun p => ⟨?_, ?_⟩⟩
  · intro y hy y' hy' a b ha hb _ l
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [hy l, hy' l]
  · simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_nonpos_of_nonneg_of_nonpos hα (hy l)
  · have : {y : Fin L → ℝ | ∀ l, y l ≤ 0} = ⋂ l, {y | y l ≤ 0} := by ext; simp
    rw [this]
    exact isClosed_iInter fun l => isClosed_le (continuous_apply l) continuous_const
  · rintro ⟨hp, -, hz⟩
    refine ⟨hp, ?_⟩
    have h0 : -z p = 0 := eq_zero_of_dotProduct_nonpos hp (fun l => by simpa using hz l)
      (by rw [dotProduct_neg, hW p hp, neg_zero])
    simpa using h0
  · rintro ⟨hp, hz⟩
    refine ⟨hp, fun y hy => Finset.sum_nonpos fun l _ =>
      mul_nonpos_of_nonneg_of_nonpos (hp l).le (hy l), fun l => by simp [hz]⟩

/-! ### Definition 17.F.1 -/

/-- **Definition 17.F.1** (MWG, p. 607). The excess demand function `z` satisfies the weak axiom
of revealed preference: for price vectors `p, p' ≫ 0`, `z(p) ≠ z(p')` and `p·z(p') ≤ 0` imply
`p'·z(p) > 0`. -/
def WeakAxiomED (z : (Fin L → ℝ) → Fin L → ℝ) : Prop :=
  ∀ p ∈ posOrthant L, ∀ p' ∈ posOrthant L, z p ≠ z p' → p ⬝ᵥ z p' ≤ 0 → 0 < p' ⬝ᵥ z p

omit [Fintype ι] in
/-- **Section 17.F** (MWG, p. 608). The weak axiom holds for the excess demand
`zᵢ(p) = xᵢ(p) - ωᵢ` of any single consumer whose demand at every `p ≫ 0` is the single
utility-maximizing bundle `xᵢ(p)`. -/
theorem wa_of_demand_eq {E : ExchangeEconomy ι L} {i : ι} {f : (Fin L → ℝ) → Fin L → ℝ}
    (hf : ∀ p ∈ posOrthant L, E.demand i p = {f p}) :
    WeakAxiomED (fun p => f p - E.ω i) := by
  intro p hp p' hp' hne hle
  by_contra hcon
  rw [not_lt] at hcon
  have hx : f p ∈ E.demand i p := by rw [hf p hp]; rfl
  have hx' : f p' ∈ E.demand i p' := by rw [hf p' hp']; rfl
  have hle' : p ⬝ᵥ f p' ≤ p ⬝ᵥ E.ω i := by
    rw [dotProduct_sub] at hle
    linarith
  have hcon' : p' ⬝ᵥ f p ≤ p' ⬝ᵥ E.ω i := by
    rw [dotProduct_sub] at hcon
    linarith
  have h1 : E.u i (f p') ≤ E.u i (f p) := hx.2 _ ⟨hx'.1.1, hle'⟩
  have h2 : E.u i (f p) ≤ E.u i (f p') := hx'.2 _ ⟨hx.1.1, hcon'⟩
  have hmem : f p' ∈ E.demand i p :=
    ⟨⟨hx'.1.1, hle'⟩, fun y hy => (hx.2 y hy).trans h2⟩
  rw [hf p hp] at hmem
  exact hne (by simp only [show f p' = f p from hmem])

omit [Fintype ι] in
/-- **Section 17.F** (MWG, p. 608). "The axiom is always satisfied by the excess demand function
of a single individual": consumer `i`'s excess demand `zᵢ(p) = xᵢ(p, p·ωᵢ) - ωᵢ`, with continuous,
strictly convex preferences on `ℝ^L₊` and `ωᵢ ∈ ℝ^L₊`, satisfies the weak axiom. -/
theorem wa_indivExcessDemand {E : ExchangeEconomy ι L} (hX : ∀ i, E.X i = nonnegOrthant L)
    {i : ι} (hc : ContinuousOn (E.u i) (nonnegOrthant L))
    (hsq : StrictlyQuasiconcaveOn (nonnegOrthant L) (E.u i)) (hω : E.ω i ∈ nonnegOrthant L) :
    WeakAxiomED (indivExcessDemand E i) := by
  have h := wa_of_demand_eq (E := E) (i := i) (f := demandFn E i) fun p hp => by
    have hne := demand_nonempty hX hc hω hp
    exact Set.eq_singleton_iff_unique_mem.2 ⟨demandFn_mem E hne,
      fun x hx => demand_subsingleton hX hsq p hx (demandFn_mem E hne)⟩
  exact h

/-! ### Necessity of the weak axiom (p. 608, Figure 17.F.1) -/

/-- **Section 17.F** (MWG, p. 608). The technology `Y* = {y : p·y ≤ 0 and p'·y ≤ 0}`. -/
def starTech (p p' : Fin L → ℝ) : Set (Fin L → ℝ) := {y | p ⬝ᵥ y ≤ 0 ∧ p' ⬝ᵥ y ≤ 0}

/-- **Section 17.F** (MWG, p. 608). `Y*` is a closed, constant returns, convex technology. -/
theorem starTech_isCR (p p' : Fin L → ℝ) :
    IsCRConvexTech (starTech p p') ∧ IsClosed (starTech p p') := by
  refine ⟨⟨?_, fun y hy α hα => ?_⟩, ?_⟩
  · intro y hy y' hy' a b ha hb _
    obtain ⟨h1, h2⟩ := hy
    obtain ⟨h1', h2'⟩ := hy'
    refine ⟨?_, ?_⟩
    · rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
      nlinarith
    · rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
      nlinarith
  · obtain ⟨h1, h2⟩ := hy
    refine ⟨?_, ?_⟩
    · rw [dotProduct_smul, smul_eq_mul]; exact mul_nonpos_of_nonneg_of_nonpos hα h1
    · rw [dotProduct_smul, smul_eq_mul]; exact mul_nonpos_of_nonneg_of_nonpos hα h2
  · have : starTech p p' = {y | p ⬝ᵥ y ≤ 0} ∩ {y | p' ⬝ᵥ y ≤ 0} := rfl
    rw [this]
    refine IsClosed.inter (isClosed_le ?_ continuous_const) (isClosed_le ?_ continuous_const)
    · change Continuous fun y : Fin L → ℝ => ∑ l, p l * y l
      fun_prop
    · change Continuous fun y : Fin L → ℝ => ∑ l, p' l * y l
      fun_prop

/-- **Section 17.F** (MWG, p. 608, Figure 17.F.1). The weak axiom is necessary for uniqueness: if
it fails at `p, p' ≫ 0` (`z(p) ≠ z(p')`, `p·z(p') ≤ 0`, `p'·z(p) ≤ 0`), then both `p` and `p'`
are equilibrium price vectors for `Y*`, with different excess demands. -/
theorem wa_violation_two_eqm {z : (Fin L → ℝ) → Fin L → ℝ} (hW : EDWalrasLaw z)
    {p p' : Fin L → ℝ} (hp : p ∈ posOrthant L) (hp' : p' ∈ posOrthant L)
    (h1 : p ⬝ᵥ z p' ≤ 0) (h2 : p' ⬝ᵥ z p ≤ 0) :
    IsCREqmPrice z (starTech p p') p ∧ IsCREqmPrice z (starTech p p') p' :=
  ⟨⟨hp, fun _ hy => hy.1, (hW p hp).le, h2⟩, ⟨hp', fun _ hy => hy.2, h1, (hW p' hp').le⟩⟩

/-! ### Proposition 17.F.2 -/

/-- **Proposition 17.F.2** (MWG, p. 609), first part. If `z` (homogeneous of degree zero, Walras'
law) has, for every closed constant returns convex technology `Y`, a unique normalized
equilibrium price vector (any two are proportional), then `z` satisfies the weak axiom. -/
theorem proposition_17_F_2_necessity {z : (Fin L → ℝ) → Fin L → ℝ} (hH : EDHomogeneous z)
    (hW : EDWalrasLaw z)
    (huniq : ∀ Y : Set (Fin L → ℝ), IsCRConvexTech Y → IsClosed Y → ∀ p p',
      IsCREqmPrice z Y p → IsCREqmPrice z Y p' → ∃ α : ℝ, 0 < α ∧ p' = α • p) :
    WeakAxiomED z := by
  intro p hp p' hp' hne hle
  by_contra hcon
  rw [not_lt] at hcon
  obtain ⟨e1, e2⟩ := wa_violation_two_eqm hW hp hp' hle hcon
  obtain ⟨α, hα, rfl⟩ :=
    huniq _ (starTech_isCR p p').1 (starTech_isCR p p').2 p p' e1 e2
  exact hne (hH p hp α hα).symm

/-- **Proposition 17.F.2** (MWG, p. 609), the key step of the proof: under the weak axiom and
Walras' law, if `p, p'` satisfy (i)-(ii) for `Y`, then `z(αp + (1-α)p')` equals `z(p)` or
`z(p')`. -/
theorem wa_combo_eq {z : (Fin L → ℝ) → Fin L → ℝ} (hW : EDWalrasLaw z) (hWA : WeakAxiomED z)
    {Y : Set (Fin L → ℝ)} {p p' : Fin L → ℝ} (hp : IsCREqmPrice z Y p)
    (hp' : IsCREqmPrice z Y p') {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    z (a • p + b • p') = z p ∨ z (a • p + b • p') = z p' := by
  set q := a • p + b • p' with hq
  have hqpos : q ∈ posOrthant L := convex_posOrthant L hp.1 hp'.1 ha hb hab
  have hqY : ∀ y ∈ Y, q ⬝ᵥ y ≤ 0 := fun y hy => by
    rw [hq, add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul]
    nlinarith [hp.2.1 y hy, hp'.2.1 y hy]
  have hwq := hW q hqpos
  rw [hq, add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul] at hwq
  by_cases h1 : p ⬝ᵥ z q ≤ 0
  · left
    by_contra hne
    have := hWA p hp.1 q hqpos (Ne.symm hne) h1
    linarith [hqY _ hp.2.2]
  · right
    have h2 : p' ⬝ᵥ z q ≤ 0 := by
      rw [not_le] at h1
      by_contra h2
      rw [not_le] at h2
      rcases eq_or_lt_of_le ha with ha0 | ha0
      · subst ha0
        have hb1 : b = 1 := by linarith
        subst hb1
        linarith
      · nlinarith
    by_contra hne
    have := hWA p' hp'.1 q hqpos (Ne.symm hne) h2
    linarith [hqY _ hp'.2.2]

/-- **Proposition 17.F.2** (MWG, p. 609), second part. If `z` satisfies Walras' law and the weak
axiom, then for any technology `Y` the set of price vectors satisfying (i)-(ii) of Proposition
17.F.1 is convex. (The book takes `Y` constant returns and convex; the proof uses neither.) -/
theorem proposition_17_F_2_convex {z : (Fin L → ℝ) → Fin L → ℝ} (hW : EDWalrasLaw z)
    (hWA : WeakAxiomED z) (Y : Set (Fin L → ℝ)) : Convex ℝ {p | IsCREqmPrice z Y p} := by
  intro p hp p' hp' a b ha hb hab
  refine ⟨convex_posOrthant L hp.1 hp'.1 ha hb hab, fun y hy => ?_, ?_⟩
  · rw [add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul]
    nlinarith [hp.2.1 y hy, hp'.2.1 y hy]
  · rcases wa_combo_eq hW hWA hp hp' ha hb hab with h | h
    · rw [h]; exact hp.2.2
    · rw [h]; exact hp'.2.2

/-- **Footnote 39** (MWG, p. 609). If `z` is moreover continuous, any two equilibrium price
vectors `p, p'` for `Y` have `z(p) = z(p')`: every Walrasian equilibrium has the same aggregate
consumption and production vectors. -/
theorem footnote_17_39 {z : (Fin L → ℝ) → Fin L → ℝ} (hC : EDContinuous z) (hW : EDWalrasLaw z)
    (hWA : WeakAxiomED z) {Y : Set (Fin L → ℝ)} {p p' : Fin L → ℝ} (hp : IsCREqmPrice z Y p)
    (hp' : IsCREqmPrice z Y p') : z p = z p' := by
  by_contra hne
  set d := z p' - z p with hd
  have hd0 : d ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
  have hdd : 0 < d ⬝ᵥ d := by
    have hnn : 0 ≤ d ⬝ᵥ d := Finset.sum_nonneg fun l _ => mul_self_nonneg (d l)
    exact lt_of_le_of_ne hnn (Ne.symm (fun h => hd0 (dotProduct_self_eq_zero.1 h)))
  set c : ℝ → Fin L → ℝ := fun t => t • p + (1 - t) • p' with hc
  set φ : ℝ → ℝ := fun t => d ⬝ᵥ (z (c t) - z p) with hφ
  have hcmem : ∀ t ∈ Set.Icc (0 : ℝ) 1, c t ∈ posOrthant L := fun t ht =>
    convex_posOrthant L hp.1 hp'.1 ht.1 (by linarith [ht.2]) (by ring)
  have hcont : ContinuousOn φ (Set.Icc 0 1) := by
    have hcc : Continuous c := by rw [hc]; fun_prop
    have hzc : ContinuousOn (fun t => z (c t)) (Set.Icc 0 1) :=
      hC.comp hcc.continuousOn hcmem
    simp only [hφ, dotProduct]
    exact continuousOn_finsetSum _ fun l _ => continuousOn_const.mul
      (((continuous_apply l).comp_continuousOn hzc).sub continuousOn_const)
  have hφ1 : φ 1 = 0 := by simp [hφ, hc]
  have hφ0 : φ 0 = d ⬝ᵥ d := by simp [hφ, hc, hd]
  have hmid : d ⬝ᵥ d / 2 ∈ Set.Icc (φ 1) (φ 0) := by
    rw [hφ1, hφ0]; constructor <;> linarith
  obtain ⟨t, ht, hφt⟩ := intermediate_value_Icc' zero_le_one hcont hmid
  rcases wa_combo_eq (a := t) (b := 1 - t) hW hWA hp hp' ht.1 (by linarith [ht.2]) (by ring)
    with h | h
  · have : φ t = 0 := by simp only [hφ, hc]; rw [h, sub_self, dotProduct_zero]
    linarith
  · have : φ t = d ⬝ᵥ d := by simp only [hφ, hc]; rw [h]
    linarith

/-- A finite convex set has at most one point. -/
theorem subsingleton_of_convex_finite {n : ℕ} {S : Set (Fin n → ℝ)} (hS : Convex ℝ S)
    (hfin : S.Finite) : S.Subsingleton := by
  intro q hq q' hq'
  by_contra hne
  have hinj : Set.InjOn (fun t : ℝ => (1 - t) • q + t • q') (Set.Icc 0 1) := by
    intro s _ t _ hst
    have h : (t - s) • (q' - q) = 0 := by
      have e : (t - s) • (q' - q) = ((1 - t) • q + t • q') - ((1 - s) • q + s • q') := by
        module
      simp only at hst
      rw [e, hst, sub_self]
    rcases smul_eq_zero.1 h with h | h
    · linarith
    · exact absurd (sub_eq_zero.1 h) (Ne.symm hne)
  have hmaps : Set.MapsTo (fun t : ℝ => (1 - t) • q + t • q') (Set.Icc 0 1) S :=
    fun t ht => hS hq hq' (by linarith [ht.2]) ht.1 (by ring)
  exact (Set.Icc_infinite (zero_lt_one' ℝ)) (hfin.subset (Set.image_subset_iff.2 hmaps)
    |>.of_finite_image hinj)

/-- **Proposition 17.F.2** (MWG, p. 609), parenthetical. Under the weak axiom and Walras' law, if
the set of normalized equilibrium price vectors (`p_L = 1`) for `Y` is finite, it has at most one
element. -/
theorem proposition_17_F_2_finite {n : ℕ} {z : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ}
    (hW : EDWalrasLaw z) (hWA : WeakAxiomED z) (Y : Set (Fin (n + 1) → ℝ))
    (hfin : {q : Fin n → ℝ | IsCREqmPrice z Y (normPrice q)}.Finite) :
    {q : Fin n → ℝ | IsCREqmPrice z Y (normPrice q)}.Subsingleton := by
  refine subsingleton_of_convex_finite ?_ hfin
  intro q hq q' hq' a b ha hb hab
  have hlin : normPrice (a • q + b • q') = a • normPrice q + b • normPrice q' := by
    funext k
    refine Fin.lastCases ?_ (fun l => ?_) k
    · simp [hab]
    · simp
  change IsCREqmPrice z Y (normPrice (a • q + b • q'))
  rw [hlin]
  exact proposition_17_F_2_convex hW hWA Y hq hq' ha hb hab

/-- **Proposition 17.F.2 with regularity** (MWG, pp. 608-609; finiteness from Proposition
17.D.1). An exchange economy whose excess demand satisfies (i)-(v) of Proposition 17.B.2 and the
weak axiom, and which is regular, has at most one normalized equilibrium price vector. -/
theorem proposition_17_F_2_regular {n : ℕ} {z : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ}
    (hz : IsStandardExcessDemand z) (hWA : WeakAxiomED z) (hreg : IsRegularEconomy z) :
    {q : Fin n → ℝ | IsNormEqm z q}.Subsingleton := by
  have heq : {q : Fin n → ℝ | IsNormEqm z q} =
      {q | IsCREqmPrice z {y | ∀ l, y l ≤ 0} (normPrice q)} := by
    ext q
    exact ((footnote_17_36 hz.walras).2.2 (normPrice q)).symm
  have hfin := proposition_17_D_1_finite hz hreg
  rw [heq] at hfin ⊢
  exact proposition_17_F_2_finite hz.walras hWA _ hfin

/-! ### Instances: one Cobb-Douglas consumer -/

/-- One Cobb-Douglas consumer (`a ≫ 0`, `ω ≥ 0`) has the single demanded bundle `cdDemand` at every
`p ≫ 0`. -/
theorem cd1_demand_eq [NeZero L] {a ω : Fin L → ℝ} (ha : ∀ l, 0 < a l)
    (hω : ω ∈ nonnegOrthant L) {p : Fin L → ℝ} (hp : p ∈ posOrthant L) :
    (cdEconomy (fun _ : Fin 1 => a) (fun _ => ω)).demand 0 p = {cdDemand a p (p ⬝ᵥ ω)} :=
  walrasianDemand_cobbDouglas ha hp (cd_wealth_nonneg hp hω)

/-- **Section 17.F**, instance of Definition 17.F.1 (MWG, p. 608). The excess demand of one
Cobb-Douglas consumer satisfies the weak axiom. -/
theorem cd1_weakAxiom [NeZero L] {a ω : Fin L → ℝ} (ha : ∀ l, 0 < a l)
    (hω : ω ∈ nonnegOrthant L) : WeakAxiomED (cd1ED a ω) := by
  have h := wa_of_demand_eq (E := cdEconomy (fun _ : Fin 1 => a) (fun _ => ω)) (i := 0)
    (f := fun p => cdDemand a p (p ⬝ᵥ ω)) fun p hp => cd1_demand_eq ha hω hp
  exact h

/-- **Proposition 17.F.2**, instance of its hypothesis (MWG, p. 609). For one Cobb-Douglas
consumer with `ω ≫ 0`, every technology `Y` has at most one equilibrium price ray: by footnote 39
two equilibria have equal excess demands, and Cobb-Douglas demand determines relative prices. -/
theorem cd1_unique_cr_eqm [NeZero L] {a ω : Fin L → ℝ} (ha : ∀ l, 0 < a l)
    (hω : ∀ l, 0 < ω l) (Y : Set (Fin L → ℝ)) {p p' : Fin L → ℝ}
    (hp : IsCREqmPrice (cd1ED a ω) Y p) (hp' : IsCREqmPrice (cd1ED a ω) Y p') :
    ∃ α : ℝ, 0 < α ∧ p' = α • p := by
  have hst := cd1ED_isStandard ha hω
  have hω' : ω ∈ nonnegOrthant L := fun l => (hω l).le
  have heq := footnote_17_39 hst.continuous hst.walras (cd1_weakAxiom ha hω') hp hp'
  have hw : 0 < p ⬝ᵥ ω := Finset.sum_pos (fun l _ => mul_pos (hp.1 l) (hω l))
    Finset.univ_nonempty
  have hw' : 0 < p' ⬝ᵥ ω := Finset.sum_pos (fun l _ => mul_pos (hp'.1 l) (hω l))
    Finset.univ_nonempty
  have hA : 0 < ∑ k, a k := Finset.sum_pos (fun k _ => ha k) Finset.univ_nonempty
  refine ⟨(p' ⬝ᵥ ω) / (p ⬝ᵥ ω), div_pos hw' hw, funext fun l => ?_⟩
  have h := congrFun heq l
  simp only [cd1ED, cdDemand, Pi.sub_apply, sub_left_inj] at h
  have hpl := hp.1 l
  have hpl' := hp'.1 l
  have hal := ha l
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp at h ⊢
  nlinarith [h]

end MWG.PositiveEquilibriumTheory
