/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPositiveEquilibriumTheory.QuasiEquilibrium

/-!
# The truncated economy and the `I + J + 1` player game (MWG Appendix B, pp. 635-637)

The objects of the proof of Proposition 17.BB.2.

* The set `A` of feasible allocations (`bbFeasibleSet`, assumption (iii) of Proposition
  17.BB.2), with the free-disposal market clearing inequality `∑ᵢ xᵢ ≤ ∑ᵢ ωᵢ + ∑ⱼ yⱼ`.
* The truncated sets `X̂ᵢ = {xᵢ ∈ Xᵢ : |x_{ℓi}| ≤ r}`, `Ŷⱼ = {yⱼ ∈ Yⱼ : |y_{ℓj}| ≤ r}`
  (`bbTruncX`, `bbTruncY`) and the truncated economy (`bbTruncEconomy`).
* **Lemma 17.BB.1** (`lemma_17_BB_1`): if `|x_{ℓi}|, |y_{ℓj}| < r` on `A`, a free-disposal
  quasiequilibrium of the truncated economy is one of the original economy.
* The game: limited-liability wealth `wᵢ(p, y) = p·ωᵢ + max {0, ∑ⱼ θᵢⱼ p·yⱼ}` (`bbWealth`),
  the strategy sets `X̂ᵢ`, `Ŷⱼ`, `Δ` (`bbStrategySet`), and the best responses
  `x̃ᵢ(x, y, p)` (`bbConsumerBR`, which depends on `(y, p)` only), `ỹⱼ(x, y, p)`
  (`bbFirmBR`, profit maximization on `Ŷⱼ`) and `p̃(x, y, p)` (`bbMarketBR`, the solutions of
  (17.BB.1) `max_{q ∈ Δ} (∑ᵢ xᵢ - ∑ᵢ ωᵢ - ∑ⱼ yⱼ)·q`).
* **Lemma 17.BB.2** (`lemma_17_BB_2`): an equilibrium of the game is a free-disposal
  quasiequilibrium of the truncated economy.
-/

namespace MWG.PositiveEquilibriumTheory

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.Production MWG.WelfareTheorems
open Kreps.PreferenceProperties
open MWG.CompetitiveMarkets (Allocation)
open Filter Topology

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {L : ℕ}

/-! ### The feasible set and the truncation -/

/-- **Proposition 17.BB.2(iii)** (MWG, p. 634). The set of feasible allocations
`A = {(x, y) : xᵢ ∈ Xᵢ, yⱼ ∈ Yⱼ, ∑ᵢ xᵢ ≤ ∑ᵢ ωᵢ + ∑ⱼ yⱼ}`. -/
def bbFeasibleSet (E : PrivPrefEconomy ι κ L) : Set ((ι → Fin L → ℝ) × (κ → Fin L → ℝ)) :=
  {a | (∀ i, a.1 i ∈ E.X i) ∧ (∀ j, a.2 j ∈ E.Y j) ∧ ∑ i, a.1 i ≤ ∑ i, E.ωi i + ∑ j, a.2 j}

/-- The cube `{v : |v_ℓ| ≤ r for all ℓ}`. -/
def bbBox (L : ℕ) (r : ℝ) : Set (Fin L → ℝ) := Set.Icc (fun _ => -r) (fun _ => r)

/-- The open cube `{v : |v_ℓ| < r for all ℓ}`. -/
def bbOpenBox (L : ℕ) (r : ℝ) : Set (Fin L → ℝ) := {v | ∀ l, |v l| < r}

/-- Membership in the cube. -/
theorem mem_bbBox {r : ℝ} {v : Fin L → ℝ} : v ∈ bbBox L r ↔ ∀ l, |v l| ≤ r :=
  ⟨fun h l => abs_le.mpr ⟨h.1 l, h.2 l⟩,
    fun h => ⟨fun l => (abs_le.mp (h l)).1, fun l => (abs_le.mp (h l)).2⟩⟩

/-- The cube is compact. -/
theorem isCompact_bbBox (L : ℕ) (r : ℝ) : IsCompact (bbBox L r) := isCompact_Icc

/-- The cube is convex. -/
theorem convex_bbBox (L : ℕ) (r : ℝ) : Convex ℝ (bbBox L r) := convex_Icc _ _

/-- The open cube is open. -/
theorem isOpen_bbOpenBox (L : ℕ) (r : ℝ) : IsOpen (bbOpenBox L r) := by
  have h : bbOpenBox L r = ⋂ l, {v : Fin L → ℝ | |v l| < r} := by
    ext v
    simp [bbOpenBox]
  rw [h]
  exact isOpen_iInter_of_finite fun l =>
    isOpen_lt (continuous_abs.comp (continuous_apply l)) continuous_const

/-- The open cube lies in the cube. -/
theorem bbOpenBox_subset (L : ℕ) (r : ℝ) : bbOpenBox L r ⊆ bbBox L r :=
  fun _ hv => mem_bbBox.mpr fun l => (hv l).le

/-- Around a point of the open cube, coordinatewise closeness keeps us in the cube. -/
theorem bb_near_box {r : ℝ} {v : Fin L → ℝ} (hv : v ∈ bbOpenBox L r) :
    ∃ δ > 0, ∀ w : Fin L → ℝ, (∀ l, |w l - v l| < δ) → w ∈ bbOpenBox L r := by
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp (isOpen_bbOpenBox L r) v hv
  refine ⟨δ, hδ, fun w hw => hball ?_⟩
  rw [Metric.mem_ball, dist_pi_lt_iff hδ]
  intro l
  rw [Real.dist_eq]
  exact hw l

/-- From a point of the open cube, a short step toward any `u` stays in the open cube. -/
theorem bb_segment_box {r : ℝ} {v : Fin L → ℝ} (hv : v ∈ bbOpenBox L r) (u : Fin L → ℝ) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ v + t • (u - v) ∈ bbOpenBox L r := by
  have ht : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim : Tendsto (fun n : ℕ => v + (1 / ((n : ℝ) + 1)) • (u - v)) atTop (𝓝 v) := by
    simpa using (ht.smul_const (u - v)).const_add v
  obtain ⟨n, hn⟩ := (hlim.eventually ((isOpen_bbOpenBox L r).mem_nhds hv)).exists
  refine ⟨1 / ((n : ℝ) + 1), by positivity, ?_, hn⟩
  rw [div_le_one (by positivity)]
  linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]

/-- The truncated consumption set `X̂ᵢ = {xᵢ ∈ Xᵢ : |x_{ℓi}| ≤ r}` (MWG, p. 636). -/
def bbTruncX (E : PrivPrefEconomy ι κ L) (r : ℝ) (i : ι) : Set (Fin L → ℝ) :=
  E.X i ∩ bbBox L r

/-- The truncated production set `Ŷⱼ = {yⱼ ∈ Yⱼ : |y_{ℓj}| ≤ r}` (MWG, p. 636). -/
def bbTruncY (E : PrivPrefEconomy ι κ L) (r : ℝ) (j : κ) : Set (Fin L → ℝ) :=
  E.Y j ∩ bbBox L r

/-- The truncated economy: consumption and production sets replaced by `X̂ᵢ` and `Ŷⱼ`. -/
def bbTruncEconomy (E : PrivPrefEconomy ι κ L) (r : ℝ) : PrivPrefEconomy ι κ L where
  X := bbTruncX E r
  pref := E.pref
  Y := bbTruncY E r
  ωi := E.ωi
  θ := E.θ

omit [Fintype ι] in
/-- Wealth in the truncated economy is wealth in the original economy. -/
theorem bbTruncEconomy_wealth (E : PrivPrefEconomy ι κ L) (r : ℝ) (a : Allocation ι κ L)
    (p : Fin L → ℝ) (i : ι) : (bbTruncEconomy E r).wealth a p i = E.wealth a p i := rfl

omit [Fintype ι] [Fintype κ] in
/-- `X̂ᵢ` is compact when `Xᵢ` is closed. -/
theorem isCompact_bbTruncX {E : PrivPrefEconomy ι κ L} (hX : ∀ i, IsClosed (E.X i)) (r : ℝ)
    (i : ι) : IsCompact (bbTruncX E r i) :=
  (isCompact_bbBox L r).inter_left (hX i)

omit [Fintype ι] [Fintype κ] in
/-- `Ŷⱼ` is compact when `Yⱼ` is closed. -/
theorem isCompact_bbTruncY {E : PrivPrefEconomy ι κ L} (hY : ∀ j, IsClosed (E.Y j)) (r : ℝ)
    (j : κ) : IsCompact (bbTruncY E r j) :=
  (isCompact_bbBox L r).inter_left (hY j)

/-- Strict preference followed by weak preference is strict (for rational `≿`). -/
theorem bb_strict_trans {X : Set (Fin L → ℝ)} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hr : RationalOn X r) {x y z : Fin L → ℝ} (hx : x ∈ X) (hy : y ∈ X) (hz : z ∈ X)
    (hxy : Strict r x y) (hyz : r y z) : Strict r x z :=
  ⟨hr.2 x hx y hy z hz hxy.1 hyz, fun hzx => hxy.2 (hr.2 y hy z hz x hx hyz hzx)⟩

/-- **Lemma 17.BB.1** (MWG, p. 636). Suppose every `Xᵢ`, `Yⱼ` is convex, preferences are
rational, convex and locally nonsatiated, and `|x_{ℓi}| < r`, `|y_{ℓj}| < r` for every
`(x, y) ∈ A`. If `(x*, y*, p)` is a free-disposal quasiequilibrium of the truncated economy, it
is a free-disposal quasiequilibrium of the original economy. (Convexity of `Xᵢ` is not used
beyond that of the upper contour sets.) -/
theorem lemma_17_BB_1 {E : PrivPrefEconomy ι κ L} {r : ℝ}
    (hYc : ∀ j, Convex ℝ (E.Y j)) (hrat : ∀ i, RationalOn (E.X i) (E.pref i))
    (hpc : ∀ i, PrefConvex (E.X i) (E.pref i))
    (hlns : ∀ i, LocallyNonsatiated (E.X i) (E.pref i))
    (hA : ∀ a ∈ bbFeasibleSet E, (∀ i, a.1 i ∈ bbOpenBox L r) ∧ ∀ j, a.2 j ∈ bbOpenBox L r)
    {a : Allocation ι κ L} {p : Fin L → ℝ}
    (hq : IsFreeDisposalQuasiEqm (bbTruncEconomy E r) a p) : IsFreeDisposalQuasiEqm E a p := by
  obtain ⟨hp0, hsup, hcons, hle, hval⟩ := hq
  have hfeas : (a.x, a.y) ∈ bbFeasibleSet E :=
    ⟨fun i => (hcons i).1.1, fun j => (hsup j).1.1, hle⟩
  obtain ⟨hxint, hyint⟩ := hA _ hfeas
  refine ⟨hp0, fun j => ⟨(hsup j).1.1, fun y hy => ?_⟩, fun i => ⟨(hcons i).1.1,
    (hcons i).2.1, fun x hx hs => ?_⟩, hle, hval⟩
  · -- firms: a profitable `y ∈ Yⱼ` gives a profitable point of `Ŷⱼ` on the segment
    by_contra hlt
    push Not at hlt
    obtain ⟨t, ht0, ht1, hbox⟩ := bb_segment_box (hyint j) y
    have hmem : a.y j + t • (y - a.y j) ∈ bbTruncY E r j :=
      ⟨(hYc j).add_smul_sub_mem (hsup j).1.1 hy ⟨ht0.le, ht1⟩, bbOpenBox_subset L r hbox⟩
    have := (hsup j).2 _ hmem
    rw [dotProduct_add, dotProduct_smul, dotProduct_sub, smul_eq_mul] at this
    nlinarith
  · -- consumers: a cheaper better `x ∈ Xᵢ` gives, by convexity and local nonsatiation, a
    -- cheaper better point of `X̂ᵢ`
    by_contra hlt
    push Not at hlt
    set w := E.wealth a p i
    have hxi := (hcons i).1.1
    obtain ⟨t, ht0, ht1, hbox⟩ := bb_segment_box (hxint i) x
    set xt := a.x i + t • (x - a.x i) with hxt
    obtain ⟨hxtX, hxtpref⟩ := bb_convex_comb (hpc i) hxi hxi hx (bb_refl (hrat i) hxi) hs.1
      ht0.le ht1
    have hxtcost : p ⬝ᵥ xt < w := by
      simp only [hxt, dotProduct_add, dotProduct_smul, dotProduct_sub, smul_eq_mul]
      have := (hcons i).2.1
      rw [bbTruncEconomy_wealth] at this
      nlinarith
    obtain ⟨δ, hδ, hnear⟩ := bb_near_box hbox
    obtain ⟨x', hx'X, hx'cost, hx'strict, hx'near⟩ := bb_lns_near (hlns i) p hxtX hxtcost hδ
    have hx'trunc : x' ∈ bbTruncX E r i := ⟨hx'X, bbOpenBox_subset L r (hnear x' hx'near)⟩
    have hstrict := bb_strict_trans (hrat i) hx'X hxtX hxi hx'strict hxtpref
    have := (hcons i).2.2 x' hx'trunc hstrict
    rw [bbTruncEconomy_wealth] at this
    linarith

/-! ### The game -/

/-- **Section 17.BB** (MWG, p. 636). Limited-liability wealth
`wᵢ(p, y) = p·ωᵢ + Max {0, ∑ⱼ θᵢⱼ p·yⱼ}`. -/
def bbWealth (E : PrivPrefEconomy ι κ L) (y : κ → Fin L → ℝ) (p : Fin L → ℝ) (i : ι) : ℝ :=
  p ⬝ᵥ E.ωi i + max 0 (∑ j, E.θ i j * (p ⬝ᵥ y j))

/-- **Section 17.BB** (MWG, p. 636). The strategy profiles: `X̂₁ × ⋯ × X̂_I × Ŷ₁ × ⋯ × Ŷ_J × Δ`,
a profile being `(x, y, p)`. -/
def bbStrategySet (E : PrivPrefEconomy ι κ L) (r : ℝ) :
    Set ((ι → Fin L → ℝ) × (κ → Fin L → ℝ) × (Fin L → ℝ)) :=
  Set.univ.pi (bbTruncX E r) ×ˢ Set.univ.pi (bbTruncY E r) ×ˢ priceSimplex L

/-- **Section 17.BB** (MWG, pp. 636-637). Consumer `i`'s best responses `x̃ᵢ(x, y, p)`: the
`x'ᵢ ∈ X̂ᵢ` with (1) `p·x'ᵢ ≤ wᵢ(p, y)` and (2) `x'ᵢ ≿ᵢ x''ᵢ` for all `x''ᵢ ∈ X̂ᵢ` with
`p·x''ᵢ < wᵢ(p, y)`. -/
def bbConsumerBR (E : PrivPrefEconomy ι κ L) (r : ℝ) (i : ι) (y : κ → Fin L → ℝ)
    (p : Fin L → ℝ) : Set (Fin L → ℝ) :=
  {x' | x' ∈ bbTruncX E r i ∧ p ⬝ᵥ x' ≤ bbWealth E y p i ∧
    ∀ x'' ∈ bbTruncX E r i, p ⬝ᵥ x'' < bbWealth E y p i → E.pref i x' x''}

/-- **Section 17.BB** (MWG, p. 637). Firm `j`'s best responses `ỹⱼ(x, y, p)`: the profit
maximizing productions on `Ŷⱼ`. -/
def bbFirmBR (E : PrivPrefEconomy ι κ L) (r : ℝ) (j : κ) (p : Fin L → ℝ) : Set (Fin L → ℝ) :=
  supply (bbTruncY E r j) p

/-- The aggregate excess demand `∑ᵢ xᵢ - ∑ᵢ ωᵢ - ∑ⱼ yⱼ`. -/
def bbExcess (E : PrivPrefEconomy ι κ L) (x : ι → Fin L → ℝ) (y : κ → Fin L → ℝ) :
    Fin L → ℝ :=
  ∑ i, x i - ∑ i, E.ωi i - ∑ j, y j

/-- **(17.BB.1)** (MWG, p. 637). The market agent's best responses `p̃(x, y, p)`: the solutions
of `max_{q ∈ Δ} (∑ᵢ xᵢ - ∑ᵢ ωᵢ - ∑ⱼ yⱼ)·q`. -/
def bbMarketBR (E : PrivPrefEconomy ι κ L) (x : ι → Fin L → ℝ) (y : κ → Fin L → ℝ) :
    Set (Fin L → ℝ) :=
  {q | q ∈ priceSimplex L ∧ ∀ q' ∈ priceSimplex L, q' ⬝ᵥ bbExcess E x y ≤ q ⬝ᵥ bbExcess E x y}

omit [Fintype ι] in
/-- With nonnegative profits and shares, limited liability does not bind:
`wᵢ(p, y) = p·ωᵢ + ∑ⱼ θᵢⱼ p·yⱼ`. -/
theorem bbWealth_eq {E : PrivPrefEconomy ι κ L} (hθ : ∀ i j, 0 ≤ E.θ i j)
    {y : κ → Fin L → ℝ} {p : Fin L → ℝ} (hπ : ∀ j, 0 ≤ p ⬝ᵥ y j) (x : ι → Fin L → ℝ) (i : ι) :
    bbWealth E y p i = E.wealth ⟨x, y⟩ p i := by
  unfold bbWealth PrivPrefEconomy.wealth
  rw [max_eq_right (Finset.sum_nonneg fun j _ => mul_nonneg (hθ i j) (hπ j))]

omit [Fintype ι] in
/-- `wᵢ(p, y) ≥ p·ωᵢ`. -/
theorem le_bbWealth (E : PrivPrefEconomy ι κ L) (y : κ → Fin L → ℝ) (p : Fin L → ℝ) (i : ι) :
    p ⬝ᵥ E.ωi i ≤ bbWealth E y p i := by
  unfold bbWealth
  linarith [le_max_left 0 (∑ j, E.θ i j * (p ⬝ᵥ y j))]

/-- **Lemma 17.BB.2** (MWG, p. 637). Suppose `0 ∈ Yⱼ` (and `r ≥ 0`), the shares are valid,
preferences are locally nonsatiated, and `|x_{ℓi}| < r` on `A`. If `x*ᵢ ∈ x̃ᵢ(x*, y*, p)`,
`y*ⱼ ∈ ỹⱼ(x*, y*, p)` and `p ∈ p̃(x*, y*, p)`, then `(x*, y*, p)` is a free-disposal
quasiequilibrium of the truncated economy. -/
theorem lemma_17_BB_2 {E : PrivPrefEconomy ι κ L} {r : ℝ} (hr : 0 ≤ r)
    (h0 : ∀ j, (0 : Fin L → ℝ) ∈ E.Y j) (hsh : E.SharesValid)
    (hlns : ∀ i, LocallyNonsatiated (E.X i) (E.pref i))
    (hA : ∀ a ∈ bbFeasibleSet E, ∀ i, a.1 i ∈ bbOpenBox L r)
    {x : ι → Fin L → ℝ} {y : κ → Fin L → ℝ} {p : Fin L → ℝ}
    (hx : ∀ i, x i ∈ bbConsumerBR E r i y p) (hy : ∀ j, y j ∈ bbFirmBR E r j p)
    (hp : p ∈ bbMarketBR E x y) : IsFreeDisposalQuasiEqm (bbTruncEconomy E r) ⟨x, y⟩ p := by
  have h0hat : ∀ j, (0 : Fin L → ℝ) ∈ bbTruncY E r j := fun j =>
    ⟨h0 j, mem_bbBox.mpr fun l => by simpa using hr⟩
  have hπ : ∀ j, 0 ≤ p ⬝ᵥ y j := fun j => by simpa using (hy j).2 0 (h0hat j)
  have hθ : ∀ i j, 0 ≤ E.θ i j := fun i j => (hsh.1 i j).1
  have hW : ∀ i, bbWealth E y p i = E.wealth ⟨x, y⟩ p i := bbWealth_eq hθ hπ x
  have hp0 : p ≠ 0 := by
    intro h
    have := hp.1.2
    simp [h] at this
  -- value of excess demand is nonpositive
  have hsum : ∑ i, p ⬝ᵥ x i ≤ ∑ i, E.wealth ⟨x, y⟩ p i :=
    Finset.sum_le_sum fun i _ => (hW i) ▸ (hx i).2.1
  have hsw := E.sum_wealth hsh.2 ⟨x, y⟩ p
  have hexc : p ⬝ᵥ bbExcess E x y =
      ∑ i, p ⬝ᵥ x i - p ⬝ᵥ ∑ i, E.ωi i - ∑ j, p ⬝ᵥ y j := by
    simp only [bbExcess, dotProduct_sub, dotProduct_finset_sum]
  have hval : p ⬝ᵥ bbExcess E x y ≤ 0 := by
    rw [hexc]
    simp only [PrivPrefEconomy.toEconomy] at hsw
    change ∑ i, p ⬝ᵥ x i ≤ ∑ i, E.wealth ⟨x, y⟩ p i at hsum
    linarith
  -- hence excess demand is nonpositive, good by good
  have hzle : ∀ l, bbExcess E x y l ≤ 0 := fun l => by
    have := hp.2 _ (single_mem_priceSimplex l)
    rw [single_dotProduct, one_mul] at this
    linarith
  have hle : ∑ i, x i ≤ ∑ i, E.ωi i + ∑ j, y j := fun l => by
    have := hzle l
    simp only [bbExcess, Pi.sub_apply, Pi.add_apply] at this ⊢
    linarith
  have hint := hA (x, y) ⟨fun i => (hx i).1.1, fun j => (hy j).1.1, hle⟩
  -- budgets bind, by local nonsatiation inside the truncation
  have hbind : ∀ i, p ⬝ᵥ x i = E.wealth ⟨x, y⟩ p i := by
    intro i
    refine le_antisymm ((hW i) ▸ (hx i).2.1) ?_
    by_contra hlt
    push Not at hlt
    obtain ⟨δ, hδ, hnear⟩ := bb_near_box (hint i)
    obtain ⟨x', hx'X, hx'cost, hx'strict, hx'near⟩ :=
      bb_lns_near (hlns i) p (hx i).1.1 hlt hδ
    have hx'trunc : x' ∈ bbTruncX E r i := ⟨hx'X, bbOpenBox_subset L r (hnear x' hx'near)⟩
    exact hx'strict.2 ((hx i).2.2 x' hx'trunc ((hW i).symm ▸ hx'cost))
  refine ⟨hp0, hy, fun i => ⟨(hx i).1, (hW i) ▸ (hx i).2.1, fun x' hx' hs => ?_⟩, hle, ?_⟩
  · by_contra hlt
    push Not at hlt
    exact hs.2 ((hx i).2.2 x' hx' ((hW i).symm ▸ hlt))
  · change p ⬝ᵥ bbExcess E x y = 0
    rw [hexc]
    simp only [PrivPrefEconomy.toEconomy] at hsw
    rw [Finset.sum_congr rfl fun i _ => hbind i, hsw]
    ring

end MWG.PositiveEquilibriumTheory
