/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPositiveEquilibriumTheory.AbstractEconomy
import MWGClassicalDemand.AppendixMH

/-!
# The best responses of the `I + J + 1` player game (MWG Appendix B, pp. 638-639)

* **Lemma 17.BB.3** (`lemma_17_BB_3`): a game whose strategy sets are nonempty compact convex
  sets `Sᵢ`, `Tⱼ`, `Δ` and whose best-response correspondences are nonempty, convex valued and
  upper hemicontinuous (Definition M.H.3) has an equilibrium, by Kakutani's theorem
  (LeanEconomics' `kakutani`) applied to the product correspondence `Ψ`.
* **Lemma 17.BB.4** (`lemma_17_BB_4_consumer`, `lemma_17_BB_4_firm`, `lemma_17_BB_4_market`):
  the best responses are nonempty. For consumers the budget set `{xᵢ ∈ X̂ᵢ : p·xᵢ ≤ wᵢ}` is
  compact and contains `x̂ᵢ`, and a continuous rational preference has a maximal element on it
  (`bb_exists_maximal`).
* **Lemma 17.BB.5** (`lemma_17_BB_5_consumer`) and **Exercise 17.BB.6**
  (`exercise_17_BB_6_firm`, `exercise_17_BB_6_market`): convex values. The consumer case is
  proved with the convexity of the upper contour set of `x''ᵢ` (Definition 3.B.4); the book's
  route through Exercise 17.BB.5 is `exercise_17_BB_5`.
* **Lemma 17.BB.6** (`lemma_17_BB_6_consumer`) and **Exercise 17.BB.7**
  (`exercise_17_BB_7_firm`, `exercise_17_BB_7_market`): upper hemicontinuity, as closed graphs
  with values in the compact cube (`bbBox`).
-/

namespace MWG.PositiveEquilibriumTheory

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.Production MWG.WelfareTheorems
open Kreps.PreferenceProperties
open MWG.CompetitiveMarkets (Allocation)
open Filter Topology

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {L : ℕ}

/-- The strategy profiles `S₁ × ⋯ × S_I × T₁ × ⋯ × T_J × Δ` of a game of the form of
Section 17.BB. -/
def bbGameSet (S : ι → Set (Fin L → ℝ)) (T : κ → Set (Fin L → ℝ)) :
    Set ((ι → Fin L → ℝ) × (κ → Fin L → ℝ) × (Fin L → ℝ)) :=
  Set.univ.pi S ×ˢ Set.univ.pi T ×ˢ priceSimplex L

omit [Fintype ι] [Fintype κ] in
/-- The strategy set of the game of Section 17.BB is a game set. -/
theorem bbStrategySet_eq (E : PrivPrefEconomy ι κ L) (r : ℝ) :
    bbStrategySet E r = bbGameSet (bbTruncX E r) (bbTruncY E r) := rfl

/-- The simplex is nonempty when `L > 0`. -/
theorem priceSimplex_nonempty (hL : 0 < L) : (priceSimplex L).Nonempty :=
  ⟨_, single_mem_priceSimplex ⟨0, hL⟩⟩

/-- **Lemma 17.BB.3** (MWG, p. 638). If the strategy sets `Sᵢ`, `Tⱼ` are nonempty, compact and
convex (`L > 0`, so `Δ ≠ ∅`) and the best-response correspondences `x̃ᵢ`, `ỹⱼ`, `p̃` of the
profile `(x, y, p)` are nonempty, convex valued and upper hemicontinuous on the strategy
profiles, with values in the strategy sets, there is `(x*, y*, p)` with `x*ᵢ ∈ x̃ᵢ(x*, y*, p)`,
`y*ⱼ ∈ ỹⱼ(x*, y*, p)` and `p ∈ p̃(x*, y*, p)`: a fixed point of
`Ψ(x, y, p) = x̃₁ × ⋯ × x̃_I × ỹ₁ × ⋯ × ỹ_J × p̃`, by Kakutani's theorem. -/
theorem lemma_17_BB_3 {S : ι → Set (Fin L → ℝ)} {T : κ → Set (Fin L → ℝ)} (hL : 0 < L)
    (hSc : ∀ i, IsCompact (S i)) (hSv : ∀ i, Convex ℝ (S i)) (hSn : ∀ i, (S i).Nonempty)
    (hTc : ∀ j, IsCompact (T j)) (hTv : ∀ j, Convex ℝ (T j)) (hTn : ∀ j, (T j).Nonempty)
    {fx : ι → (ι → Fin L → ℝ) × (κ → Fin L → ℝ) × (Fin L → ℝ) → Set (Fin L → ℝ)}
    {fy : κ → (ι → Fin L → ℝ) × (κ → Fin L → ℝ) × (Fin L → ℝ) → Set (Fin L → ℝ)}
    {fp : (ι → Fin L → ℝ) × (κ → Fin L → ℝ) × (Fin L → ℝ) → Set (Fin L → ℝ)}
    (hfx : ∀ i, ∀ s ∈ bbGameSet S T, (fx i s).Nonempty ∧ Convex ℝ (fx i s) ∧ fx i s ⊆ S i)
    (hfy : ∀ j, ∀ s ∈ bbGameSet S T, (fy j s).Nonempty ∧ Convex ℝ (fy j s) ∧ fy j s ⊆ T j)
    (hfp : ∀ s ∈ bbGameSet S T, (fp s).Nonempty ∧ Convex ℝ (fp s) ∧ fp s ⊆ priceSimplex L)
    (hux : ∀ i, UpperHemicontinuousMWG (bbGameSet S T) (fx i))
    (huy : ∀ j, UpperHemicontinuousMWG (bbGameSet S T) (fy j))
    (hup : UpperHemicontinuousMWG (bbGameSet S T) fp) :
    ∃ s ∈ bbGameSet S T, (∀ i, s.1 i ∈ fx i s) ∧ (∀ j, s.2.1 j ∈ fy j s) ∧ s.2.2 ∈ fp s := by
  set K := bbGameSet S T with hK
  set F : (ι → Fin L → ℝ) × (κ → Fin L → ℝ) × (Fin L → ℝ) →
      Set ((ι → Fin L → ℝ) × (κ → Fin L → ℝ) × (Fin L → ℝ)) :=
    fun s => Set.univ.pi (fun i => fx i s) ×ˢ Set.univ.pi (fun j => fy j s) ×ˢ fp s with hF
  have hKc : IsCompact K :=
    (isCompact_univ_pi hSc).prod ((isCompact_univ_pi hTc).prod (isCompact_priceSimplex L))
  have hKv : Convex ℝ K :=
    (convex_pi fun i _ => hSv i).prod ((convex_pi fun j _ => hTv j).prod
      (convex_priceSimplex L))
  have hKn : K.Nonempty :=
    (Set.univ_pi_nonempty_iff.mpr hSn).prod ((Set.univ_pi_nonempty_iff.mpr hTn).prod
      (priceSimplex_nonempty hL))
  have hFne : ∀ s ∈ K, (F s).Nonempty := fun s hs =>
    (Set.univ_pi_nonempty_iff.mpr fun i => (hfx i s hs).1).prod
      ((Set.univ_pi_nonempty_iff.mpr fun j => (hfy j s hs).1).prod (hfp s hs).1)
  have hFv : ∀ s ∈ K, Convex ℝ (F s) := fun s hs =>
    (convex_pi fun i _ => (hfx i s hs).2.1).prod ((convex_pi fun j _ => (hfy j s hs).2.1).prod
      (hfp s hs).2.1)
  have hFK : ∀ s ∈ K, F s ⊆ K := fun s hs t ht =>
    ⟨fun i _ => (hfx i s hs).2.2 (ht.1 i trivial),
      fun j _ => (hfy j s hs).2.2 (ht.2.1 j trivial), (hfp s hs).2.2 ht.2.2⟩
  have hgraph : IsClosed (LeanEconomics.FixedPoint.graphOn K F) := by
    refine IsSeqClosed.isClosed fun {zs} {z} hzs hlim => ?_
    have h1 : Tendsto (fun n => (zs n).1) atTop (𝓝 z.1) := (continuous_fst.tendsto z).comp hlim
    have h2 : Tendsto (fun n => (zs n).2) atTop (𝓝 z.2) := (continuous_snd.tendsto z).comp hlim
    have hz1 : z.1 ∈ K :=
      hKc.isClosed.mem_of_tendsto h1 (Eventually.of_forall fun n => (hzs n).1)
    refine ⟨hz1, fun i _ => ?_, fun j _ => ?_, ?_⟩
    · exact (hux i).1 (fun n => (zs n).1) (fun n => (zs n).2.1 i) z.1 (z.2.1 i)
        (fun n => (hzs n).1) hz1 (fun n => (hzs n).2.1 i trivial) h1
        ((((continuous_apply i).comp continuous_fst).tendsto z.2).comp h2)
    · exact (huy j).1 (fun n => (zs n).1) (fun n => (zs n).2.2.1 j) z.1 (z.2.2.1 j)
        (fun n => (hzs n).1) hz1 (fun n => (hzs n).2.2.1 j trivial) h1
        ((((continuous_apply j).comp (continuous_fst.comp continuous_snd)).tendsto z.2).comp
          h2)
    · exact hup.1 (fun n => (zs n).1) (fun n => (zs n).2.2.2) z.1 z.2.2.2
        (fun n => (hzs n).1) hz1 (fun n => (hzs n).2.2.2) h1
        (((continuous_snd.comp continuous_snd).tendsto z.2).comp h2)
  obtain ⟨s, hsK, hfix⟩ := LeanEconomics.FixedPoint.kakutani hKc hKv hKn hFne hFv hFK hgraph
  exact ⟨s, hsK, fun i => hfix.1 i trivial, fun j => hfix.2.1 j trivial, hfix.2.2⟩

/-! ### Lemma 17.BB.4: nonempty values -/

/-- `x ≤ y` and `p ≥ 0` give `p·x ≤ p·y`. -/
theorem bb_dotProduct_mono {p x y : Fin L → ℝ} (hp : ∀ l, 0 ≤ p l) (hxy : x ≤ y) :
    p ⬝ᵥ x ≤ p ⬝ᵥ y :=
  Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (hxy l) (hp l)

/-- `v ↦ p·v` is continuous. -/
theorem bb_continuous_dot (p : Fin L → ℝ) : Continuous fun v : Fin L → ℝ => p ⬝ᵥ v :=
  continuous_const.dotProduct continuous_id

omit [Fintype ι] in
/-- **Lemma 17.BB.4**, consumers (MWG, p. 638). If `Xᵢ` is closed, `≿ᵢ` rational and continuous,
`x̂ᵢ ∈ X̂ᵢ` with `x̂ᵢ ≤ ωᵢ`, and `p ∈ Δ`, then `x̃ᵢ(x, y, p) ≠ ∅`: a maximal element of `≿ᵢ`
on the nonempty compact budget set `{xᵢ ∈ X̂ᵢ : p·xᵢ ≤ wᵢ(p, y)}` is a best response. -/
theorem lemma_17_BB_4_consumer {E : PrivPrefEconomy ι κ L} {r : ℝ} {i : ι}
    (hX : IsClosed (E.X i)) (hrat : RationalOn (E.X i) (E.pref i))
    (hc : PrefContinuous (E.X i) (E.pref i)) {xh : Fin L → ℝ} (hxh : xh ∈ bbTruncX E r i)
    (hxhω : xh ≤ E.ωi i) (y : κ → Fin L → ℝ) {p : Fin L → ℝ} (hp : p ∈ priceSimplex L) :
    (bbConsumerBR E r i y p).Nonempty := by
  set w := bbWealth E y p i
  set B := bbTruncX E r i ∩ {x | p ⬝ᵥ x ≤ w}
  have hB : IsCompact B := ((isCompact_bbBox L r).inter_left hX).inter_right
    (isClosed_le (bb_continuous_dot p) continuous_const)
  have hxhB : xh ∈ B :=
    ⟨hxh, (bb_dotProduct_mono hp.1 hxhω).trans (le_bbWealth E y p i)⟩
  obtain ⟨m, hmB, hm⟩ := bb_exists_maximal hrat hc hB (fun x hx => hx.1.1) ⟨xh, hxhB⟩
  exact ⟨m, hmB.1, hmB.2, fun x'' hx'' hcost => hm x'' ⟨hx'', hcost.le⟩⟩

omit [Fintype ι] [Fintype κ] in
/-- **Lemma 17.BB.4**, firms (MWG, p. 638). If `Yⱼ` is closed and `0 ∈ Ŷⱼ`, profit
maximization on the compact set `Ŷⱼ` has a solution. -/
theorem lemma_17_BB_4_firm {E : PrivPrefEconomy ι κ L} {r : ℝ} {j : κ}
    (hY : IsClosed (E.Y j)) (h0 : (0 : Fin L → ℝ) ∈ bbTruncY E r j) (p : Fin L → ℝ) :
    (bbFirmBR E r j p).Nonempty := by
  obtain ⟨y, hy, hmax⟩ := ((isCompact_bbBox L r).inter_left hY).exists_isMaxOn ⟨0, h0⟩
    (bb_continuous_dot p).continuousOn
  exact ⟨y, hy, fun y' hy' => hmax hy'⟩

/-- **Lemma 17.BB.4**, market agent (MWG, p. 638). A linear function has a maximizer on the
nonempty compact `Δ` (`L > 0`). -/
theorem lemma_17_BB_4_market (E : PrivPrefEconomy ι κ L) (hL : 0 < L)
    (x : ι → Fin L → ℝ) (y : κ → Fin L → ℝ) : (bbMarketBR E x y).Nonempty := by
  obtain ⟨q, hq, hmax⟩ := (isCompact_priceSimplex L).exists_isMaxOn (priceSimplex_nonempty hL)
    ((continuous_id.dotProduct continuous_const :
      Continuous fun q : Fin L → ℝ => q ⬝ᵥ bbExcess E x y)).continuousOn
  exact ⟨q, hq, fun q' hq' => hmax hq'⟩

/-! ### Lemma 17.BB.5 and Exercise 17.BB.6: convex values -/

omit [Fintype ι] in
/-- **Lemma 17.BB.5** (MWG, p. 638). With `Xᵢ` convex and `≿ᵢ` convex, `x̃ᵢ(x, y, p)` is
convex. -/
theorem lemma_17_BB_5_consumer {E : PrivPrefEconomy ι κ L} {r : ℝ} {i : ι}
    (hX : Convex ℝ (E.X i)) (hpc : PrefConvex (E.X i) (E.pref i)) (y : κ → Fin L → ℝ)
    (p : Fin L → ℝ) : Convex ℝ (bbConsumerBR E r i y p) := by
  intro x₁ h₁ x₂ h₂ a b ha hb hab
  refine ⟨(hX.inter (convex_bbBox L r)) h₁.1 h₂.1 ha hb hab, ?_, fun x'' hx'' hcost => ?_⟩
  · rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    have e : a * bbWealth E y p i + b * bbWealth E y p i = bbWealth E y p i := by
      rw [← add_mul, hab, one_mul]
    nlinarith [h₁.2.1, h₂.2.1]
  · exact (hpc x'' hx''.1 ⟨h₁.1.1, h₁.2.2 x'' hx'' hcost⟩ ⟨h₂.1.1, h₂.2.2 x'' hx'' hcost⟩
      ha hb hab).2

omit [Fintype ι] [Fintype κ] in
/-- **Exercise 17.BB.6**, firms (MWG, p. 650). With `Yⱼ` convex, `ỹⱼ(x, y, p)` is convex. -/
theorem exercise_17_BB_6_firm {E : PrivPrefEconomy ι κ L} {r : ℝ} {j : κ}
    (hY : Convex ℝ (E.Y j)) (p : Fin L → ℝ) : Convex ℝ (bbFirmBR E r j p) := by
  intro y₁ h₁ y₂ h₂ a b ha hb hab
  refine ⟨(hY.inter (convex_bbBox L r)) h₁.1 h₂.1 ha hb hab, fun y' hy' => ?_⟩
  rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  have e : a * p ⬝ᵥ y' + b * p ⬝ᵥ y' = p ⬝ᵥ y' := by rw [← add_mul, hab, one_mul]
  nlinarith [h₁.2 y' hy', h₂.2 y' hy']

/-- **Exercise 17.BB.6**, market agent (MWG, p. 650). `p̃(x, y, p)` is convex. -/
theorem exercise_17_BB_6_market (E : PrivPrefEconomy ι κ L) (x : ι → Fin L → ℝ)
    (y : κ → Fin L → ℝ) : Convex ℝ (bbMarketBR E x y) := by
  intro q₁ h₁ q₂ h₂ a b ha hb hab
  refine ⟨convex_priceSimplex L h₁.1 h₂.1 ha hb hab, fun q' hq' => ?_⟩
  rw [add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul]
  have e : a * q' ⬝ᵥ bbExcess E x y + b * q' ⬝ᵥ bbExcess E x y = q' ⬝ᵥ bbExcess E x y := by
    rw [← add_mul, hab, one_mul]
  nlinarith [h₁.2 q' hq', h₂.2 q' hq']

/-! ### Lemma 17.BB.6 and Exercise 17.BB.7: upper hemicontinuity -/

omit [Fintype ι] in
/-- Limited-liability wealth is continuous in `(y, p)`. -/
theorem bb_tendsto_wealth (E : PrivPrefEconomy ι κ L) (i : ι) {ys : ℕ → κ → Fin L → ℝ}
    {ps : ℕ → Fin L → ℝ} {y : κ → Fin L → ℝ} {p : Fin L → ℝ}
    (hy : Tendsto ys atTop (𝓝 y)) (hp : Tendsto ps atTop (𝓝 p)) :
    Tendsto (fun n => bbWealth E (ys n) (ps n) i) atTop (𝓝 (bbWealth E y p i)) := by
  unfold bbWealth
  refine (tendsto_dotProduct hp tendsto_const_nhds).add (tendsto_const_nhds.max
    (tendsto_finsetSum _ fun j _ => tendsto_const_nhds.mul (tendsto_dotProduct hp ?_)))
  exact ((continuous_apply j).tendsto y).comp hy

/-- Aggregate excess demand is continuous in `(x, y)`. -/
theorem bb_tendsto_excess (E : PrivPrefEconomy ι κ L) {xs : ℕ → ι → Fin L → ℝ}
    {ys : ℕ → κ → Fin L → ℝ} {x : ι → Fin L → ℝ} {y : κ → Fin L → ℝ}
    (hx : Tendsto xs atTop (𝓝 x)) (hy : Tendsto ys atTop (𝓝 y)) :
    Tendsto (fun n => bbExcess E (xs n) (ys n)) atTop (𝓝 (bbExcess E x y)) := by
  unfold bbExcess
  refine ((tendsto_finsetSum _ fun i _ => ?_).sub tendsto_const_nhds).sub
    (tendsto_finsetSum _ fun j _ => ?_)
  · exact ((continuous_apply i).tendsto x).comp hx
  · exact ((continuous_apply j).tendsto y).comp hy

/-- The best responses lie in the compact cube, so their images are bounded. -/
theorem bb_bounded_of_subset_box {α : Type*} [TopologicalSpace α] {A : Set α}
    {f : α → Set (Fin L → ℝ)} {r : ℝ}
    (hf : ∀ s ∈ A, f s ⊆ bbBox L r) :
    ∀ B ⊆ A, IsCompact B → Bornology.IsBounded (⋃ s ∈ B, f s) := fun _ hB _ =>
  (isCompact_bbBox L r).isBounded.subset (Set.iUnion₂_subset fun s hs => hf s (hB hs))

/-- **Lemma 17.BB.6** (MWG, pp. 638-639). If `Xᵢ` is closed and `≿ᵢ` is continuous,
`(x, y, p) ↦ x̃ᵢ(x, y, p)` is upper hemicontinuous on the strategy profiles: its graph is
closed (if `pⁿ → p`, `yⁿ → y`, `x'ⁿ → x'` with `x'ⁿ ∈ x̃ᵢ(xⁿ, yⁿ, pⁿ)`, then
`x' ∈ x̃ᵢ(x, y, p)`) and its values lie in the cube. -/
theorem lemma_17_BB_6_consumer {E : PrivPrefEconomy ι κ L} {r : ℝ} {i : ι}
    (hX : IsClosed (E.X i)) (hc : PrefContinuous (E.X i) (E.pref i)) :
    UpperHemicontinuousMWG (bbStrategySet E r) fun s => bbConsumerBR E r i s.2.1 s.2.2 := by
  refine ⟨fun ss xs s x' _ _ hxs hss hlim => ?_, 
    bb_bounded_of_subset_box fun s _ x (hx : x ∈ bbConsumerBR E r i s.2.1 s.2.2) => hx.1.2⟩
  have hy : Tendsto (fun n => (ss n).2.1) atTop (𝓝 s.2.1) :=
    ((continuous_fst.comp continuous_snd).tendsto s).comp hss
  have hp : Tendsto (fun n => (ss n).2.2) atTop (𝓝 s.2.2) :=
    ((continuous_snd.comp continuous_snd).tendsto s).comp hss
  have hw := bb_tendsto_wealth E i hy hp
  have hmem : x' ∈ bbTruncX E r i :=
    ((isCompact_bbBox L r).inter_left hX).isClosed.mem_of_tendsto hlim
      (Eventually.of_forall fun n => (hxs n).1)
  refine ⟨hmem, le_of_tendsto_of_tendsto' (tendsto_dotProduct hp hlim) hw
    fun n => (hxs n).2.1, fun x'' hx'' hcost => ?_⟩
  have hev : ∀ᶠ n in atTop, (ss n).2.2 ⬝ᵥ x'' < bbWealth E (ss n).2.1 (ss n).2.2 i := by
    have h := (hw.sub (tendsto_dotProduct hp tendsto_const_nhds)).eventually
      (lt_mem_nhds (sub_pos.mpr hcost))
    filter_upwards [h] with n hn
    linarith
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  exact hc (fun n => xs (n + N)) (fun _ => x'') x' x'' (fun n => (hxs (n + N)).1.1)
    (fun _ => hx''.1) hmem.1 hx''.1
    (fun n => (hxs (n + N)).2.2 x'' hx'' (hN (n + N) (Nat.le_add_left N n)))
    (hlim.comp (tendsto_add_atTop_nat N)) tendsto_const_nhds

/-- **Exercise 17.BB.7**, firms (MWG, p. 650). If `Yⱼ` is closed, `(x, y, p) ↦ ỹⱼ(x, y, p)` is
upper hemicontinuous on the strategy profiles. -/
theorem exercise_17_BB_7_firm {E : PrivPrefEconomy ι κ L} {r : ℝ} {j : κ}
    (hY : IsClosed (E.Y j)) :
    UpperHemicontinuousMWG (bbStrategySet E r) fun s => bbFirmBR E r j s.2.2 := by
  refine ⟨fun ss ys s y' _ _ hys hss hlim => ?_, 
    bb_bounded_of_subset_box fun s _ y (hy : y ∈ bbFirmBR E r j s.2.2) => hy.1.2⟩
  have hp : Tendsto (fun n => (ss n).2.2) atTop (𝓝 s.2.2) :=
    ((continuous_snd.comp continuous_snd).tendsto s).comp hss
  refine ⟨((isCompact_bbBox L r).inter_left hY).isClosed.mem_of_tendsto hlim
    (Eventually.of_forall fun n => (hys n).1), fun y'' hy'' => ?_⟩
  exact le_of_tendsto_of_tendsto' (tendsto_dotProduct hp tendsto_const_nhds)
    (tendsto_dotProduct hp hlim) fun n => (hys n).2 y'' hy''

/-- **Exercise 17.BB.7**, market agent (MWG, p. 650). `(x, y, p) ↦ p̃(x, y, p)` is upper
hemicontinuous on the strategy profiles. -/
theorem exercise_17_BB_7_market (E : PrivPrefEconomy ι κ L) (r : ℝ) :
    UpperHemicontinuousMWG (bbStrategySet E r) fun s => bbMarketBR E s.1 s.2.1 := by
  refine ⟨fun ss qs s q _ _ hqs hss hlim => ?_, fun _ _ _ =>
    (isCompact_priceSimplex L).isBounded.subset (Set.iUnion₂_subset fun s _ q hq => hq.1)⟩
  have hx : Tendsto (fun n => (ss n).1) atTop (𝓝 s.1) := (continuous_fst.tendsto s).comp hss
  have hy : Tendsto (fun n => (ss n).2.1) atTop (𝓝 s.2.1) :=
    ((continuous_fst.comp continuous_snd).tendsto s).comp hss
  have hz := bb_tendsto_excess E hx hy
  refine ⟨(isClosed_priceSimplex L).mem_of_tendsto hlim
    (Eventually.of_forall fun n => (hqs n).1), fun q' hq' => ?_⟩
  exact le_of_tendsto_of_tendsto' (tendsto_dotProduct tendsto_const_nhds hz)
    (tendsto_dotProduct hlim hz) fun n => (hqs n).2 q' hq'

end MWG.PositiveEquilibriumTheory
