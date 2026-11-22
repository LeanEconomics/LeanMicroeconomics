/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPositiveEquilibriumTheory.ExistenceGeneral

/-!
# Exercise 17.BB.9: the two-player game (MWG Appendix B, p. 640; Exercise 17.BB.9, p. 651)

The aggregate consumer-firm has the strategy set `Z = ∑ᵢ X̂ᵢ - {∑ᵢ ωᵢ} - ∑ⱼ Ŷⱼ`
(`bbAggStrategy`, the image of `∏ X̂ᵢ × ∏ Ŷⱼ` under `(x, y) ↦ ∑ᵢ xᵢ - ∑ᵢ ωᵢ - ∑ⱼ yⱼ`), and
responds to `p ∈ Δ` with the vectors `z = ∑ᵢ xᵢ - ∑ᵢ ωᵢ - ∑ⱼ yⱼ` where every `yⱼ` is profit
maximizing in `Ŷⱼ` and every `xᵢ ∈ X̂ᵢ` satisfies (1) and (2) of p. 640 (`bbAggResponse`; the
wealth `p·ωᵢ + ∑ⱼ θᵢⱼ p·yⱼ` is `bbWealth` because profits are nonnegative). The market agent
responds to `z` with the maximizers of `q·z` on `Δ` (`bbPriceResponse`).

* `bbAggResponse` is nonempty, convex valued (`bbAggResponse_convex`: profit maximizing `yⱼ`
  all have the same profit, so the consumers' budget sets do not depend on which is chosen) and
  has a closed graph (`bbAggResponse_closedGraph`: extract a convergent subsequence of the
  underlying `(xⁿ, yⁿ)` and use Lemma 17.BB.6 / Exercise 17.BB.7).
* **Exercise 17.BB.9** (`exercise_17_BB_9`): Kakutani's theorem on `Z × Δ` gives an equilibrium
  of the two-player game, which is the data of Lemma 17.BB.2; the proof then ends as for
  Proposition 17.BB.2.
-/

namespace MWG.PositiveEquilibriumTheory

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.Production MWG.WelfareTheorems
open Kreps.PreferenceProperties
open MWG.CompetitiveMarkets (Allocation)
open Filter Topology

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {L : ℕ}

/-- `(x, y) ↦ ∑ᵢ xᵢ - ∑ᵢ ωᵢ - ∑ⱼ yⱼ` is continuous. -/
theorem bb_continuous_excess (E : PrivPrefEconomy ι κ L) :
    Continuous fun a : (ι → Fin L → ℝ) × (κ → Fin L → ℝ) => bbExcess E a.1 a.2 :=
  ((continuous_finsetSum _ fun i _ => (continuous_apply i).comp continuous_fst).sub
    continuous_const).sub (continuous_finsetSum _ fun j _ => (continuous_apply j).comp
      continuous_snd)

/-- Aggregate excess demand is affine. -/
theorem bbExcess_comb (E : PrivPrefEconomy ι κ L) (x₁ x₂ : ι → Fin L → ℝ)
    (y₁ y₂ : κ → Fin L → ℝ) {a b : ℝ} (hab : a + b = 1) :
    bbExcess E (a • x₁ + b • x₂) (a • y₁ + b • y₂) =
      a • bbExcess E x₁ y₁ + b • bbExcess E x₂ y₂ := by
  funext l
  simp only [bbExcess, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_apply, Finset.sum_add_distrib, ← Finset.mul_sum]
  linear_combination (∑ i, E.ωi i l) * hab

/-- **Section 17.BB** (MWG, p. 640). The aggregate consumer-firm's strategy set
`∑ᵢ X̂ᵢ - {∑ᵢ ωᵢ} - ∑ⱼ Ŷⱼ`. -/
def bbAggStrategy (E : PrivPrefEconomy ι κ L) (r : ℝ) : Set (Fin L → ℝ) :=
  (fun a : (ι → Fin L → ℝ) × (κ → Fin L → ℝ) => bbExcess E a.1 a.2) ''
    (Set.univ.pi (bbTruncX E r) ×ˢ Set.univ.pi (bbTruncY E r))

/-- **Section 17.BB** (MWG, p. 640). The aggregate consumer-firm's response to `p`. -/
def bbAggResponse (E : PrivPrefEconomy ι κ L) (r : ℝ) (p : Fin L → ℝ) : Set (Fin L → ℝ) :=
  {z | ∃ (x : ι → Fin L → ℝ) (y : κ → Fin L → ℝ), (∀ j, y j ∈ bbFirmBR E r j p) ∧
    (∀ i, x i ∈ bbConsumerBR E r i y p) ∧ z = bbExcess E x y}

/-- **Section 17.BB** (MWG, p. 640). The market agent's response to `z`: the `q ∈ Δ`
maximizing `z·q`. -/
def bbPriceResponse (L : ℕ) (z : Fin L → ℝ) : Set (Fin L → ℝ) :=
  {q | q ∈ priceSimplex L ∧ ∀ q' ∈ priceSimplex L, q' ⬝ᵥ z ≤ q ⬝ᵥ z}

omit [Fintype ι] in
/-- Consumers' best responses depend on the production plans only through their profits. -/
theorem bbConsumerBR_congr (E : PrivPrefEconomy ι κ L) (r : ℝ) (i : ι)
    {y y' : κ → Fin L → ℝ} {p : Fin L → ℝ} (h : ∀ j, p ⬝ᵥ y j = p ⬝ᵥ y' j) :
    bbConsumerBR E r i y p = bbConsumerBR E r i y' p := by
  have hw : bbWealth E y p i = bbWealth E y' p i := by simp only [bbWealth, h]
  simp only [bbConsumerBR, hw]

/-- The aggregate response is convex valued. -/
theorem bbAggResponse_convex {E : PrivPrefEconomy ι κ L} {r : ℝ}
    (hX : ∀ i, Convex ℝ (E.X i)) (hpc : ∀ i, PrefConvex (E.X i) (E.pref i))
    (hY : ∀ j, Convex ℝ (E.Y j)) (p : Fin L → ℝ) : Convex ℝ (bbAggResponse E r p) := by
  rintro _ ⟨x₁, y₁, hy₁, hx₁, rfl⟩ _ ⟨x₂, y₂, hy₂, hx₂, rfl⟩ a b ha hb hab
  have hprof : ∀ j, p ⬝ᵥ y₂ j = p ⬝ᵥ y₁ j := fun j =>
    le_antisymm ((hy₁ j).2 _ (hy₂ j).1) ((hy₂ j).2 _ (hy₁ j).1)
  have hyc : ∀ j, (a • y₁ + b • y₂) j ∈ bbFirmBR E r j p := fun j =>
    exercise_17_BB_6_firm (hY j) p (hy₁ j) (hy₂ j) ha hb hab
  have hprof' : ∀ j, p ⬝ᵥ (a • y₁ + b • y₂) j = p ⬝ᵥ y₁ j := fun j => by
    simp only [Pi.add_apply, Pi.smul_apply, dotProduct_add, dotProduct_smul, smul_eq_mul,
      hprof j]
    rw [← add_mul, hab, one_mul]
  refine ⟨a • x₁ + b • x₂, a • y₁ + b • y₂, hyc, fun i => ?_, (bbExcess_comb E _ _ _ _ hab).symm⟩
  rw [bbConsumerBR_congr E r i hprof']
  have h₂ : x₂ i ∈ bbConsumerBR E r i y₁ p := by
    rw [← bbConsumerBR_congr E r i hprof]
    exact hx₂ i
  exact lemma_17_BB_5_consumer (hX i) (hpc i) y₁ p (hx₁ i) h₂ ha hb hab

/-- The aggregate response has a closed graph on `Δ`. -/
theorem bbAggResponse_closedGraph {E : PrivPrefEconomy ι κ L} {r : ℝ}
    (hX : ∀ i, IsClosed (E.X i)) (hc : ∀ i, PrefContinuous (E.X i) (E.pref i))
    (hY : ∀ j, IsClosed (E.Y j)) {ps : ℕ → Fin L → ℝ} {p : Fin L → ℝ}
    (hps : ∀ n, ps n ∈ priceSimplex L) (hp : p ∈ priceSimplex L)
    (hplim : Tendsto ps atTop (𝓝 p)) {zs : ℕ → Fin L → ℝ} {z : Fin L → ℝ}
    (hzs : ∀ n, zs n ∈ bbAggResponse E r (ps n)) (hzlim : Tendsto zs atTop (𝓝 z)) :
    z ∈ bbAggResponse E r p := by
  choose xs ys hys hxs hzeq using hzs
  have hC : IsCompact (Set.univ.pi (bbTruncX E r) ×ˢ Set.univ.pi (bbTruncY E r)) :=
    (isCompact_univ_pi (isCompact_bbTruncX hX r)).prod (isCompact_univ_pi (isCompact_bbTruncY hY r))
  obtain ⟨⟨x, y⟩, ⟨hxC, hyC⟩, φ, hφ, hlim⟩ := hC.tendsto_subseq (x := fun n => (xs n, ys n))
    fun n => ⟨fun i _ => (hxs n i).1, fun j _ => (hys n j).1⟩
  have hx : Tendsto (fun n => xs (φ n)) atTop (𝓝 x) := (continuous_fst.tendsto _).comp hlim
  have hy : Tendsto (fun n => ys (φ n)) atTop (𝓝 y) := (continuous_snd.tendsto _).comp hlim
  have hpφ : Tendsto (fun n => ps (φ n)) atTop (𝓝 p) := hplim.comp hφ.tendsto_atTop
  set ss : ℕ → (ι → Fin L → ℝ) × (κ → Fin L → ℝ) × (Fin L → ℝ) :=
    fun n => (xs (φ n), ys (φ n), ps (φ n))
  have hss : ∀ n, ss n ∈ bbStrategySet E r := fun n =>
    ⟨fun i _ => (hxs (φ n) i).1, fun j _ => (hys (φ n) j).1, hps (φ n)⟩
  have hs : ((x, y, p) : (ι → Fin L → ℝ) × (κ → Fin L → ℝ) × (Fin L → ℝ)) ∈ bbStrategySet E r :=
    ⟨hxC, hyC, hp⟩
  have hsl : Tendsto ss atTop (𝓝 (x, y, p)) := hx.prodMk_nhds (hy.prodMk_nhds hpφ)
  refine ⟨x, y, fun j => ?_, fun i => ?_, ?_⟩
  · exact (exercise_17_BB_7_firm (r := r) (hY j)).1 ss (fun n => ys (φ n) j) _ (y j) hss hs
      (fun n => hys (φ n) j) hsl (((continuous_apply j).tendsto y).comp hy)
  · exact (lemma_17_BB_6_consumer (r := r) (hX i) (hc i)).1 ss (fun n => xs (φ n) i) _ (x i)
      hss hs (fun n => hxs (φ n) i) hsl (((continuous_apply i).tendsto x).comp hx)
  · have h1 : Tendsto (fun n => zs (φ n)) atTop (𝓝 z) := hzlim.comp hφ.tendsto_atTop
    have h2 : Tendsto (fun n => zs (φ n)) atTop (𝓝 (bbExcess E x y)) := by
      have := ((bb_continuous_excess E).tendsto (x, y)).comp hlim
      refine this.congr fun n => ?_
      simp only [Function.comp_apply]
      exact (hzeq (φ n)).symm
    exact tendsto_nhds_unique h1 h2

/-- **Exercise 17.BB.9** (MWG, p. 651). Under the hypotheses of Proposition 17.BB.2 a Walrasian
quasiequilibrium exists, by the two-player game of p. 640: Kakutani's theorem on `Z × Δ` for
`(z, p) ↦ (aggregate response to p) × (maximizers of q·z on Δ)`. -/
theorem exercise_17_BB_9 [Nonempty ι] [Nonempty κ] {E : PrivPrefEconomy ι κ L}
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
  -- the two-player game on `K = Z × Δ`
  set Z := bbAggStrategy E r
  set K : Set ((Fin L → ℝ) × (Fin L → ℝ)) := Z ×ˢ priceSimplex L
  set F : (Fin L → ℝ) × (Fin L → ℝ) → Set ((Fin L → ℝ) × (Fin L → ℝ)) :=
    fun s => bbAggResponse E r s.2 ×ˢ bbPriceResponse L s.1
  have hC : IsCompact (Set.univ.pi (bbTruncX E r) ×ˢ Set.univ.pi (bbTruncY E r)) :=
    (isCompact_univ_pi (isCompact_bbTruncX h.X_closed r)).prod
      (isCompact_univ_pi (isCompact_bbTruncY h.Y_closed r))
  have hZc : IsCompact Z := hC.image (bb_continuous_excess E)
  have hZv : Convex ℝ Z := by
    rintro _ ⟨⟨x₁, y₁⟩, ⟨hx₁, hy₁⟩, rfl⟩ _ ⟨⟨x₂, y₂⟩, ⟨hx₂, hy₂⟩, rfl⟩ a b ha hb hab
    refine ⟨(a • x₁ + b • x₂, a • y₁ + b • y₂), ⟨fun i _ => ?_, fun j _ => ?_⟩,
      bbExcess_comb E _ _ _ _ hab⟩
    · exact ((h.X_convex i).inter (convex_bbBox L r)) (hx₁ i trivial) (hx₂ i trivial) ha hb hab
    · exact ((h.Y_convex j).inter (convex_bbBox L r)) (hy₁ j trivial) (hy₂ j trivial) ha hb hab
  have hKc : IsCompact K := hZc.prod (isCompact_priceSimplex L)
  have hKv : Convex ℝ K := hZv.prod (convex_priceSimplex L)
  have hKn : K.Nonempty := ⟨(bbExcess E xh 0, _),
    ⟨(xh, 0), ⟨fun i _ => hxhT i, fun j _ => h0T j⟩, rfl⟩, single_mem_priceSimplex ⟨0, hL⟩⟩
  have hFne : ∀ s ∈ K, (F s).Nonempty := by
    intro s hs
    choose y hy using fun j => lemma_17_BB_4_firm (h.Y_closed j) (h0T j) s.2
    choose x hx using fun i => lemma_17_BB_4_consumer (h.X_closed i) (h.rational i) (h.cont i)
      (hxhT i) (hxhω i) y hs.2
    obtain ⟨q, hq, hmax⟩ := (isCompact_priceSimplex L).exists_isMaxOn
      (priceSimplex_nonempty hL)
      ((continuous_id.dotProduct continuous_const :
        Continuous fun q : Fin L → ℝ => q ⬝ᵥ s.1)).continuousOn
    exact ⟨(bbExcess E x y, q), ⟨x, y, hy, hx, rfl⟩, hq, fun q' hq' => hmax hq'⟩
  have hFv : ∀ s ∈ K, Convex ℝ (F s) := by
    intro s _
    refine (bbAggResponse_convex h.X_convex h.pconvex h.Y_convex s.2).prod ?_
    intro q₁ h₁ q₂ h₂ a b ha hb hab
    refine ⟨convex_priceSimplex L h₁.1 h₂.1 ha hb hab, fun q' hq' => ?_⟩
    rw [add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul]
    have e : a * q' ⬝ᵥ s.1 + b * q' ⬝ᵥ s.1 = q' ⬝ᵥ s.1 := by rw [← add_mul, hab, one_mul]
    nlinarith [h₁.2 q' hq', h₂.2 q' hq']
  have hFK : ∀ s ∈ K, F s ⊆ K := by
    rintro s - t ⟨⟨x, y, hy, hx, hz⟩, hq⟩
    exact ⟨⟨(x, y), ⟨fun i _ => (hx i).1, fun j _ => (hy j).1⟩, hz.symm⟩, hq.1⟩
  have hgraph : IsClosed (LeanEconomics.FixedPoint.graphOn K F) := by
    refine IsSeqClosed.isClosed fun {ws} {w} hws hlim => ?_
    have h1 : Tendsto (fun n => (ws n).1) atTop (𝓝 w.1) := (continuous_fst.tendsto w).comp hlim
    have h2 : Tendsto (fun n => (ws n).2) atTop (𝓝 w.2) := (continuous_snd.tendsto w).comp hlim
    have hw1 : w.1 ∈ K :=
      hKc.isClosed.mem_of_tendsto h1 (Eventually.of_forall fun n => (hws n).1)
    have hz : Tendsto (fun n => (ws n).1.1) atTop (𝓝 w.1.1) := (continuous_fst.tendsto _).comp h1
    have hp : Tendsto (fun n => (ws n).1.2) atTop (𝓝 w.1.2) := (continuous_snd.tendsto _).comp h1
    have hz' : Tendsto (fun n => (ws n).2.1) atTop (𝓝 w.2.1) :=
      (continuous_fst.tendsto _).comp h2
    have hq : Tendsto (fun n => (ws n).2.2) atTop (𝓝 w.2.2) := (continuous_snd.tendsto _).comp h2
    refine ⟨hw1, bbAggResponse_closedGraph h.X_closed h.cont h.Y_closed
      (fun n => (hws n).1.2) hw1.2 hp (fun n => (hws n).2.1) hz', ?_, fun q' hq' => ?_⟩
    · exact (isClosed_priceSimplex L).mem_of_tendsto hq
        (Eventually.of_forall fun n => (hws n).2.2.1)
    · exact le_of_tendsto_of_tendsto' (tendsto_dotProduct tendsto_const_nhds hz)
        (tendsto_dotProduct hq hz) fun n => (hws n).2.2.2 q' hq'
  obtain ⟨⟨z, p⟩, -, ⟨x, y, hy, hx, hzeq⟩, hpz⟩ :=
    LeanEconomics.FixedPoint.kakutani hKc hKv hKn hFne hFv hFK hgraph
  have hpm : p ∈ bbMarketBR E x y := by
    refine ⟨hpz.1, fun q' hq' => ?_⟩
    rw [← hzeq]
    exact hpz.2 q' hq'
  have hq1 := lemma_17_BB_2 hr.le h.Y_zero h.shares h.lns (fun a ha i => (hA a ha).1 i) hx hy hpm
  have hq2 := lemma_17_BB_1 h.Y_convex h.rational h.pconvex h.lns hA hq1
  obtain ⟨y', -, -, hq⟩ := exercise_17_BB_4 hq2 (Classical.arbitrary κ) (h.Y_fd _)
  exact ⟨_, _, hq⟩

end MWG.PositiveEquilibriumTheory
