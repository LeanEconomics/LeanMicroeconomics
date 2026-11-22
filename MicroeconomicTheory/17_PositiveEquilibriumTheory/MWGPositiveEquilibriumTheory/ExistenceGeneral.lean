/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPositiveEquilibriumTheory.ExistenceGeneralLemmas
import MWGProduction.ExercisesB
import MWGWelfareTheorems.Appendix
import MWGWelfareTheorems.Replica
import MWGWelfareTheorems.QuasiExample

/-!
# Existence of Walrasian quasiequilibrium: Proposition 17.BB.2 (MWG Appendix B, pp. 634-639)

* `GeneralExistenceHyp E`: the hypotheses of **Proposition 17.BB.2** for a private ownership
  economy with finitely many consumers and firms in `ℝ^L`: (i.1) `Xᵢ` closed and convex;
  (i.2) `≿ᵢ` rational, continuous, locally nonsatiated and convex on `Xᵢ`; (i.3) `ωᵢ ≥ x̂ᵢ` for
  some `x̂ᵢ ∈ Xᵢ`; (ii) `Yⱼ` closed, convex, `0 ∈ Yⱼ`, free disposal; (iii) the set `A` of
  feasible allocations is compact; and the standing assumption that the shares are valid
  (`θᵢⱼ ∈ [0, 1]`, `∑ᵢ θᵢⱼ = 1`).
* **Proposition 17.BB.2** (`proposition_17_BB_2`): with `I > 0` consumers and `J > 0` firms a
  Walrasian quasiequilibrium exists. The proof is the book's: a bound `r` on `A`
  (`bb_bound_of_compact`), the truncated game, Kakutani through Lemma 17.BB.3 (Lemmas
  17.BB.4-17.BB.6 supply its hypotheses), Lemma 17.BB.2 (game equilibrium = free-disposal
  quasiequilibrium of the truncated economy), Lemma 17.BB.1 (the truncation does not bind) and
  Exercise 17.BB.4 (free disposal turns it into a quasiequilibrium). `L > 0` follows from local
  nonsatiation.
* **Footnote 82** (`footnote_17_BB_82`): if `ωᵢ ≫ x̂ᵢ` for every `i`, a Walrasian equilibrium
  exists (with `p ≥ 0`).
* **Footnote 81** (`footnote_17_BB_81`): `Y` closed convex with `-ℝ^L₊ ⊆ Y` has free disposal
  (Exercise 5.B.5).
* An instance (`bbExample`, `bbExample_hyp`): one consumer with `u(x) = x₁ + x₂` on `ℝ²₊`,
  `ω = (1, 1)`, and one firm with the linear technology `{y : y₁ ≤ 0, y₂ ≤ -y₁}` (good 1 turned
  into good 2 one for one); all hypotheses hold, `A` being closed (`isClosed_bbFeasibleSet`)
  and bounded. It has a Walrasian equilibrium (`bbExample_eqm`).
-/

namespace MWG.PositiveEquilibriumTheory

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.Production MWG.WelfareTheorems
open Kreps.PreferenceProperties
open MWG.CompetitiveMarkets (Allocation)
open Filter Topology

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {L : ℕ}

/-- **Proposition 17.BB.2** (MWG, p. 634), hypotheses: (i.1) `Xᵢ ⊆ ℝ^L` closed and convex;
(i.2) `≿ᵢ` rational, continuous, locally nonsatiated and convex on `Xᵢ`; (i.3) `ωᵢ ≥ x̂ᵢ` for
some `x̂ᵢ ∈ Xᵢ`; (ii) `Yⱼ` closed, convex, `0 ∈ Yⱼ`, free disposal; (iii) `A` compact; and
valid shares. -/
structure GeneralExistenceHyp (E : PrivPrefEconomy ι κ L) : Prop where
  /-- (i.1) `Xᵢ` is closed. -/
  X_closed : ∀ i, IsClosed (E.X i)
  /-- (i.1) `Xᵢ` is convex. -/
  X_convex : ∀ i, Convex ℝ (E.X i)
  /-- (i.2) `≿ᵢ` is rational on `Xᵢ`. -/
  rational : ∀ i, RationalOn (E.X i) (E.pref i)
  /-- (i.2) `≿ᵢ` is continuous on `Xᵢ`. -/
  cont : ∀ i, PrefContinuous (E.X i) (E.pref i)
  /-- (i.2) `≿ᵢ` is locally nonsatiated on `Xᵢ`. -/
  lns : ∀ i, LocallyNonsatiated (E.X i) (E.pref i)
  /-- (i.2) `≿ᵢ` is convex on `Xᵢ`. -/
  pconvex : ∀ i, PrefConvex (E.X i) (E.pref i)
  /-- (i.3) `ωᵢ ≥ x̂ᵢ` for some `x̂ᵢ ∈ Xᵢ`. -/
  xhat : ∀ i, ∃ x ∈ E.X i, x ≤ E.ωi i
  /-- (ii) `Yⱼ` is closed. -/
  Y_closed : ∀ j, IsClosed (E.Y j)
  /-- (ii) `Yⱼ` is convex. -/
  Y_convex : ∀ j, Convex ℝ (E.Y j)
  /-- (ii) `0 ∈ Yⱼ`. -/
  Y_zero : ∀ j, (0 : Fin L → ℝ) ∈ E.Y j
  /-- (ii) `Yⱼ` has the free-disposal property. -/
  Y_fd : ∀ j, FreeDisposal (E.Y j)
  /-- (iii) The set of feasible allocations is compact. -/
  A_compact : IsCompact (bbFeasibleSet E)
  /-- The shares are valid. -/
  shares : E.SharesValid

/-- **Section 17.BB** (MWG, p. 635). Since `A` is bounded there is `r > 0` with `|x_{ℓi}| < r`
and `|y_{ℓj}| < r` for every `(x, y) ∈ A`. -/
theorem bb_bound_of_compact {E : PrivPrefEconomy ι κ L} (hA : IsCompact (bbFeasibleSet E)) :
    ∃ r : ℝ, 0 < r ∧ ∀ a ∈ bbFeasibleSet E,
      (∀ i, a.1 i ∈ bbOpenBox L r) ∧ ∀ j, a.2 j ∈ bbOpenBox L r := by
  obtain ⟨C, hC⟩ := hA.isBounded.exists_norm_le
  refine ⟨|C| + 1, by positivity, fun a ha => ⟨fun i l => ?_, fun j l => ?_⟩⟩
  · calc |a.1 i l| = ‖a.1 i l‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖a.1 i‖ := norm_le_pi_norm _ l
      _ ≤ ‖a.1‖ := norm_le_pi_norm _ i
      _ ≤ ‖a‖ := norm_fst_le a
      _ ≤ C := hC a ha
      _ < |C| + 1 := by linarith [le_abs_self C]
  · calc |a.2 j l| = ‖a.2 j l‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖a.2 j‖ := norm_le_pi_norm _ l
      _ ≤ ‖a.2‖ := norm_le_pi_norm _ j
      _ ≤ ‖a‖ := norm_snd_le a
      _ ≤ C := hC a ha
      _ < |C| + 1 := by linarith [le_abs_self C]

/-- **Proposition 17.BB.2** (MWG, p. 634). In an economy with `I > 0` consumers and `J > 0`
firms satisfying (i)-(iii) (and valid shares), a Walrasian quasiequilibrium exists. -/
theorem proposition_17_BB_2 [Nonempty ι] [Nonempty κ] {E : PrivPrefEconomy ι κ L}
    (h : GeneralExistenceHyp E) : ∃ (a : Allocation ι κ L) (p : Fin L → ℝ),
      IsWalrasQuasiEqm E a p := by
  classical
  obtain ⟨r, hr, hA⟩ := bb_bound_of_compact h.A_compact
  choose xh hxhX hxhω using h.xhat
  have hxhA : ((xh, 0) : (ι → Fin L → ℝ) × (κ → Fin L → ℝ)) ∈ bbFeasibleSet E := by
    refine ⟨hxhX, fun j => h.Y_zero j, ?_⟩
    simp only [Pi.zero_apply, Finset.sum_const_zero, add_zero]
    exact Finset.sum_le_sum fun i _ => hxhω i
  have hxhT : ∀ i, xh i ∈ bbTruncX E r i := fun i =>
    ⟨hxhX i, bbOpenBox_subset L r ((hA _ hxhA).1 i)⟩
  have h0T : ∀ j, (0 : Fin L → ℝ) ∈ bbTruncY E r j := fun j =>
    ⟨h.Y_zero j, mem_bbBox.mpr fun l => by simp only [Pi.zero_apply, abs_zero]; linarith⟩
  have hL : 0 < L := by
    rcases Nat.eq_zero_or_pos L with hL0 | hL0
    · subst hL0
      exfalso
      obtain ⟨i⟩ := (inferInstance : Nonempty ι)
      obtain ⟨y, -, -, hs⟩ := h.lns i (xh i) (hxhX i) 1 one_pos
      have : y = xh i := funext fun l => l.elim0
      rw [this] at hs
      exact hs.2 hs.1
    · exact hL0
  obtain ⟨s, -, hfx, hfy, hfp⟩ := lemma_17_BB_3 (S := bbTruncX E r) (T := bbTruncY E r) hL
    (isCompact_bbTruncX h.X_closed r) (fun i => (h.X_convex i).inter (convex_bbBox L r))
    (fun i => ⟨_, hxhT i⟩) (isCompact_bbTruncY h.Y_closed r)
    (fun j => (h.Y_convex j).inter (convex_bbBox L r)) (fun j => ⟨_, h0T j⟩)
    (fx := fun i s => bbConsumerBR E r i s.2.1 s.2.2) (fy := fun j s => bbFirmBR E r j s.2.2)
    (fp := fun s => bbMarketBR E s.1 s.2.1)
    (fun i s hs => ⟨lemma_17_BB_4_consumer (h.X_closed i) (h.rational i) (h.cont i) (hxhT i)
      (hxhω i) _ hs.2.2, lemma_17_BB_5_consumer (h.X_convex i) (h.pconvex i) _ _,
      fun x hx => hx.1⟩)
    (fun j s _ => ⟨lemma_17_BB_4_firm (h.Y_closed j) (h0T j) _,
      exercise_17_BB_6_firm (h.Y_convex j) _, fun y hy => hy.1⟩)
    (fun s _ => ⟨lemma_17_BB_4_market E hL _ _, exercise_17_BB_6_market E _ _,
      fun q hq => hq.1⟩)
    (fun i => lemma_17_BB_6_consumer (h.X_closed i) (h.cont i))
    (fun j => exercise_17_BB_7_firm (h.Y_closed j)) (exercise_17_BB_7_market E r)
  have hq1 := lemma_17_BB_2 (x := s.1) (y := s.2.1) (p := s.2.2) hr.le h.Y_zero h.shares h.lns
    (fun a ha i => (hA a ha).1 i) hfx hfy hfp
  have hq2 := lemma_17_BB_1 h.Y_convex h.rational h.pconvex h.lns hA hq1
  obtain ⟨y', -, -, hq⟩ := exercise_17_BB_4 hq2 (Classical.arbitrary κ) (h.Y_fd _)
  exact ⟨_, _, hq⟩

/-- **Footnote 82** (MWG, p. 634). If in addition `ωᵢ ≫ x̂ᵢ` for some `x̂ᵢ ∈ Xᵢ`, for every `i`,
Proposition 17.BB.2 yields a Walrasian equilibrium (with `p ≥ 0`, `p ≠ 0`): by free disposal
`p ≥ 0`, situation (a) of p. 633 gives every consumer the cheaper consumption condition, and
Proposition 17.BB.1 applies. -/
theorem footnote_17_BB_82 [Nonempty ι] [Nonempty κ] {E : PrivPrefEconomy ι κ L}
    (h : GeneralExistenceHyp E) (hint : ∀ i, ∃ x ∈ E.X i, ∀ l, x l < E.ωi i l) :
    ∃ (a : Allocation ι κ L) (p : Fin L → ℝ), E.IsWalrasEqm a p ∧ p ≠ 0 ∧ ∀ l, 0 ≤ p l := by
  obtain ⟨a, p, hq⟩ := proposition_17_BB_2 h
  have hp : ∀ l, 0 ≤ p l :=
    smalltype_17_BB_price_nonneg (h.Y_fd (Classical.arbitrary κ)) (hq.2.1 _)
  refine ⟨a, p, proposition_17_BB_1_eqm hq h.X_convex h.rational h.cont fun i => ?_, hq.1, hp⟩
  obtain ⟨x, hx, hxω⟩ := hint i
  exact smalltype_17_BB_cheaper_a hq h.Y_zero (fun i j => (h.shares.1 i j).1) hp hx hxω

/-- **Footnote 81** (MWG, p. 634). If `Yⱼ` is convex and closed, `-ℝ^L₊ ⊆ Yⱼ` implies
`Yⱼ - ℝ^L₊ ⊆ Yⱼ` (Exercise 5.B.5). -/
theorem footnote_17_BB_81 {Y : Set (Fin L → ℝ)} (hcl : IsClosed Y) (hc : Convex ℝ Y)
    (hneg : ∀ v : Fin L → ℝ, 0 ≤ v → -v ∈ Y) : ∀ y ∈ Y, ∀ v : Fin L → ℝ, 0 ≤ v → y - v ∈ Y :=
  fun y hy _ hv => exercise_5_B_5 hcl hc hneg y hy _ (sub_le_self y hv)

/-- **Proposition 17.BB.2(iii)** (MWG, p. 634). With closed `Xᵢ` and `Yⱼ`, the set of feasible
allocations is closed (so it is compact as soon as it is bounded). -/
theorem isClosed_bbFeasibleSet {E : PrivPrefEconomy ι κ L} (hX : ∀ i, IsClosed (E.X i))
    (hY : ∀ j, IsClosed (E.Y j)) : IsClosed (bbFeasibleSet E) := by
  refine IsSeqClosed.isClosed fun {as} {a} has hlim => ?_
  have h1 : Tendsto (fun n => (as n).1) atTop (𝓝 a.1) := (continuous_fst.tendsto a).comp hlim
  have h2 : Tendsto (fun n => (as n).2) atTop (𝓝 a.2) := (continuous_snd.tendsto a).comp hlim
  refine ⟨fun i => (hX i).mem_of_tendsto (((continuous_apply i).tendsto _).comp h1)
      (Eventually.of_forall fun n => (has n).1 i),
    fun j => (hY j).mem_of_tendsto (((continuous_apply j).tendsto _).comp h2)
      (Eventually.of_forall fun n => (has n).2.1 j), fun l => ?_⟩
  have hx : Tendsto (fun n => ∑ i, (as n).1 i) atTop (𝓝 (∑ i, a.1 i)) :=
    tendsto_finsetSum _ fun i _ => ((continuous_apply i).tendsto _).comp h1
  have hy : Tendsto (fun n => ∑ i, E.ωi i + ∑ j, (as n).2 j) atTop
      (𝓝 (∑ i, E.ωi i + ∑ j, a.2 j)) :=
    tendsto_const_nhds.add (tendsto_finsetSum _ fun j _ => ((continuous_apply j).tendsto _).comp h2)
  exact le_of_tendsto_of_tendsto' (((continuous_apply l).tendsto _).comp hx)
    (((continuous_apply l).tendsto _).comp hy) fun n => (has n).2.2 l

/-! ### An instance with production -/

/-- The linear technology `{y : y₁ ≤ 0, y₂ ≤ -y₁}`: one unit of good 1 yields one unit of
good 2, with free disposal. -/
def bbExampleTech : Set (Fin 2 → ℝ) := {y | y 0 ≤ 0 ∧ y 1 ≤ -y 0}

/-- The example economy: one consumer on `ℝ²₊` with `u(x) = x₁ + x₂` and `ω = (1, 1)`, one firm
with `bbExampleTech`. -/
def bbExample : PrivPrefEconomy Unit Unit 2 where
  X := fun _ => nonnegOrthant 2
  pref := fun _ => utilityPref fun x => x 0 + x 1
  Y := fun _ => bbExampleTech
  ωi := fun _ _ => 1
  θ := fun _ _ => 1

/-- The feasible set of the example lies in the cube `[-2, 2]`. -/
theorem bbExample_feasible_bound {a : (Unit → Fin 2 → ℝ) × (Unit → Fin 2 → ℝ)}
    (ha : a ∈ bbFeasibleSet bbExample) :
    a ∈ Set.Icc ((fun _ _ => -2, fun _ _ => -2) : (Unit → Fin 2 → ℝ) × (Unit → Fin 2 → ℝ))
      (fun _ _ => 2, fun _ _ => 2) := by
  obtain ⟨hx, hy, hs⟩ := ha
  have hx0 := hx ()
  have hy0 := hy ()
  have hs0 := hs 0
  have hs1 := hs 1
  simp only [Finset.univ_unique, Finset.sum_singleton, Pi.add_apply, bbExample] at hs0 hs1
  change ∀ l, 0 ≤ a.1 () l at hx0
  change a.2 () 0 ≤ 0 ∧ a.2 () 1 ≤ -a.2 () 0 at hy0
  have e1 := hx0 0
  have e2 := hx0 1
  obtain ⟨f1, f2⟩ := hy0
  refine ⟨⟨fun i l => ?_, fun j l => ?_⟩, ⟨fun i l => ?_, fun j l => ?_⟩⟩ <;>
    [cases i; cases j; cases i; cases j] <;> fin_cases l <;> simp <;> linarith

/-- **Instance of Proposition 17.BB.2** (MWG, p. 634): the example economy satisfies every
hypothesis. -/
theorem bbExample_hyp : GeneralExistenceHyp bbExample where
  X_closed := fun _ => isClosed_nonnegOrthant
  X_convex := fun _ => convex_nonnegOrthant 2
  rational := fun _ => rationalOn_utilityPref _ _
  cont := fun _ => prefContinuous_utilityPref (by fun_prop : Continuous _).continuousOn
  lns := fun _ => lns_of_strictMono_coord 0 fun x _ c hc => by simp; linarith
  pconvex := by
    intro _ x _ y hy z hz a b ha hb hab
    refine ⟨convex_nonnegOrthant 2 hy.1 hz.1 ha hb hab, ?_⟩
    have h1 := hy.2
    have h2 := hz.2
    simp only [bbExample, utilityPref, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 ⊢
    have e : a * (x 0 + x 1) + b * (x 0 + x 1) = x 0 + x 1 := by rw [← add_mul, hab, one_mul]
    nlinarith
  xhat := fun _ => ⟨0, fun _ => le_refl 0, fun _ => by simp [bbExample]⟩
  Y_closed := fun _ =>
    (isClosed_le (continuous_apply 0) continuous_const).inter
      (isClosed_le (continuous_apply 1) (continuous_apply 0).neg)
  Y_convex := by
    intro _ y hy z hz a b ha hb hab
    obtain ⟨hy1, hy2⟩ := hy
    obtain ⟨hz1, hz2⟩ := hz
    refine ⟨?_, ?_⟩ <;> simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] <;> nlinarith
  Y_zero := fun _ => ⟨le_refl 0, by simp⟩
  Y_fd := by
    intro _ y hy y' hy'
    exact ⟨(hy' 0).trans hy.1, by linarith [hy' 0, hy' 1, hy.2]⟩
  A_compact := isCompact_Icc.of_isClosed_subset
    (isClosed_bbFeasibleSet (fun _ => isClosed_nonnegOrthant) fun _ =>
      (isClosed_le (continuous_apply 0) continuous_const).inter
        (isClosed_le (continuous_apply 1) (continuous_apply 0).neg))
    fun _ ha => bbExample_feasible_bound ha
  shares := ⟨fun _ _ => ⟨zero_le_one, le_refl 1⟩, fun _ => by simp [bbExample]⟩

/-- The example has a Walrasian equilibrium (`ω = (1, 1) ≫ 0 = x̂`, footnote 82). -/
theorem bbExample_eqm : ∃ (a : Allocation Unit Unit 2) (p : Fin 2 → ℝ),
    bbExample.IsWalrasEqm a p ∧ p ≠ 0 ∧ ∀ l, 0 ≤ p l :=
  footnote_17_BB_82 bbExample_hyp fun _ => ⟨0, fun _ => le_refl 0, fun _ => by
    simp [bbExample]⟩

end MWG.PositiveEquilibriumTheory
