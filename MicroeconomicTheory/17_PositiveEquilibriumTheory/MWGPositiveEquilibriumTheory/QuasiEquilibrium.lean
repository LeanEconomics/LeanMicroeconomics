/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPositiveEquilibriumTheory.Exercises17AA
import MWGPositiveEquilibriumTheory.Exercise17C2

/-!
# Walrasian quasiequilibrium (MWG Appendix B, pp. 632-635)

The economy is Chapter 16's private ownership economy `PrivPrefEconomy` (consumption sets
`Xᵢ`, preferences `≿ᵢ`, production sets `Yⱼ`, endowments `ωᵢ`, shares `θᵢⱼ`) with Chapter 16's
wealth `p·ωᵢ + ∑ⱼ θᵢⱼ p·yⱼ` (`PrivPrefEconomy.wealth`).

* **Definition 17.BB.1** (`IsWalrasQuasiEqm`): profit maximization, the quasi-optimality
  condition (ii') (the budget constraint and "`xᵢ ≻ᵢ x*ᵢ ⟹ p·xᵢ ≥ wᵢ`"), exact market clearing.
* **Definition 17.BB.2** (`CheaperConsumption`), **Proposition 17.BB.1**
  (`proposition_17_BB_1`, `proposition_17_BB_1_eqm`). Completeness of `≿ᵢ` (the standing
  rationality assumption) is used: without it "maximal" does not follow from "nothing strictly
  better is cheaper".
* The small type of p. 633: situations (a), (b) give the cheaper consumption condition
  (`smalltype_17_BB_cheaper_a`, `smalltype_17_BB_cheaper_b`; the "weak condition"
  `∑ωᵢ + ∑ŷⱼ ≫ ∑x̂ᵢ` is not needed for these two), free disposal of one firm gives `p ≥ 0`
  (`smalltype_17_BB_price_nonneg`), and the weak condition with `Xᵢ + ℝ^L₊ ⊆ Xᵢ` and strongly
  monotone preferences gives `p ≫ 0` (`smalltype_17_BB_price_pos`).
* **Definition 17.BB.3** (`IsFreeDisposalQuasiEqm`) and **Exercise 17.BB.4**
  (`exercise_17_BB_4`): changing the production of one free-disposal firm turns a free-disposal
  quasiequilibrium into a quasiequilibrium.
* **Exercise 17.BB.5** (`exercise_17_BB_5`): with convex preferences, `xᵢ ≻ᵢ x_{iα}` and
  `x'ᵢ ≻ᵢ x_{iα}` cannot both hold.
* **Footnote 80 / Figure 17.BB.2** (`footnote_17_BB_80`): an Edgeworth box with a consumer
  satiated at the origin has no Walrasian quasiequilibrium.
* Tools: a continuous rational preference has a maximal element on every nonempty compact
  subset of its consumption set (`bb_exists_maximal`, the use made of footnote 84 in
  Lemma 17.BB.4), and local nonsatiation below the budget gives a better, still cheaper,
  bundle within any prescribed distance (`bb_lns_near`).
-/

namespace MWG.PositiveEquilibriumTheory

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.Production MWG.WelfareTheorems
open Kreps.PreferenceProperties
open MWG.CompetitiveMarkets (Allocation)
open Filter Topology

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {L : ℕ}

/-! ### Definitions 17.BB.1-17.BB.3 -/

/-- **Definition 17.BB.1** (MWG, p. 632). The allocation `(x*, y*)` and the price system `p ≠ 0`
form a Walrasian quasiequilibrium: (i) `p·yⱼ ≤ p·y*ⱼ` for all `yⱼ ∈ Yⱼ`; (ii') `x*ᵢ ∈ Xᵢ`,
`p·x*ᵢ ≤ p·ωᵢ + ∑ⱼ θᵢⱼ p·y*ⱼ`, and `xᵢ ≻ᵢ x*ᵢ` (`xᵢ ∈ Xᵢ`) implies
`p·xᵢ ≥ p·ωᵢ + ∑ⱼ θᵢⱼ p·y*ⱼ`; (iii) `∑ᵢ x*ᵢ = ∑ᵢ ωᵢ + ∑ⱼ y*ⱼ`. -/
def IsWalrasQuasiEqm (E : PrivPrefEconomy ι κ L) (a : Allocation ι κ L) (p : Fin L → ℝ) :
    Prop :=
  p ≠ 0 ∧ (∀ j, a.y j ∈ supply (E.Y j) p) ∧
    (∀ i, a.x i ∈ E.X i ∧ p ⬝ᵥ a.x i ≤ E.wealth a p i ∧
      ∀ x ∈ E.X i, Strict (E.pref i) x (a.x i) → E.wealth a p i ≤ p ⬝ᵥ x) ∧
    ∑ i, a.x i = ∑ i, E.ωi i + ∑ j, a.y j

/-- **Definition 17.BB.2** (MWG, p. 633). The quasiequilibrium `(x*, y*, p)` satisfies the
cheaper consumption condition for consumer `i`: some `xᵢ ∈ Xᵢ` has
`p·xᵢ < p·ωᵢ + ∑ⱼ θᵢⱼ p·y*ⱼ`. -/
def CheaperConsumption (E : PrivPrefEconomy ι κ L) (a : Allocation ι κ L) (p : Fin L → ℝ)
    (i : ι) : Prop :=
  ∃ x ∈ E.X i, p ⬝ᵥ x < E.wealth a p i

/-- **Definition 17.BB.3** (MWG, p. 635). A free-disposal quasiequilibrium: as Definition
17.BB.1 with (iii) replaced by (iii') `∑ᵢ x*ᵢ ≤ ∑ᵢ ωᵢ + ∑ⱼ y*ⱼ` and
`p·(∑ᵢ x*ᵢ - ∑ᵢ ωᵢ - ∑ⱼ y*ⱼ) = 0`. -/
def IsFreeDisposalQuasiEqm (E : PrivPrefEconomy ι κ L) (a : Allocation ι κ L)
    (p : Fin L → ℝ) : Prop :=
  p ≠ 0 ∧ (∀ j, a.y j ∈ supply (E.Y j) p) ∧
    (∀ i, a.x i ∈ E.X i ∧ p ⬝ᵥ a.x i ≤ E.wealth a p i ∧
      ∀ x ∈ E.X i, Strict (E.pref i) x (a.x i) → E.wealth a p i ≤ p ⬝ᵥ x) ∧
    ∑ i, a.x i ≤ ∑ i, E.ωi i + ∑ j, a.y j ∧
    p ⬝ᵥ (∑ i, a.x i - ∑ i, E.ωi i - ∑ j, a.y j) = 0

/-- **Section 17.BB** (MWG, p. 635). A Walrasian quasiequilibrium is a free-disposal
quasiequilibrium ("all we have done is replace the exact feasibility condition"). -/
theorem IsWalrasQuasiEqm.isFreeDisposal {E : PrivPrefEconomy ι κ L} {a : Allocation ι κ L}
    {p : Fin L → ℝ} (h : IsWalrasQuasiEqm E a p) : IsFreeDisposalQuasiEqm E a p := by
  refine ⟨h.1, h.2.1, h.2.2.1, le_of_eq h.2.2.2, ?_⟩
  rw [h.2.2.2]
  simp

/-! ### Tools -/

/-- **Footnote 84** (MWG, p. 638), as used in Lemma 17.BB.4: a rational preference that is
continuous on `X` has a maximal element on every nonempty compact `K ⊆ X`. (The book passes
through a continuous utility representation; the finite intersection property of the closed
upper sections suffices.) -/
theorem bb_exists_maximal {X K : Set (Fin L → ℝ)} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hr : RationalOn X r) (hc : PrefContinuous X r) (hK : IsCompact K) (hKX : K ⊆ X)
    (hne : K.Nonempty) : ∃ x ∈ K, ∀ y ∈ K, r x y := by
  classical
  set C : K → Set (Fin L → ℝ) := fun y => {x | x ∈ K ∧ r x y.1} with hCdef
  have hCc : ∀ y, IsClosed (C y) := by
    intro y
    refine IsSeqClosed.isClosed fun {xs} {x} hxs hlim => ?_
    have hxK : x ∈ K := hK.isClosed.mem_of_tendsto hlim (Eventually.of_forall fun n => (hxs n).1)
    refine ⟨hxK, hc xs (fun _ => y.1) x y.1 (fun n => hKX (hxs n).1) (fun _ => hKX y.2)
      (hKX hxK) (hKX y.2) (fun n => (hxs n).2) hlim tendsto_const_nhds⟩
  have hfin : ∀ u : Finset K, (K ∩ ⋂ y ∈ u, C y).Nonempty := by
    intro u
    induction u using Finset.induction_on with
    | empty => simpa using hne
    | insert a s _ ih =>
      obtain ⟨x0, hx0K, hx0⟩ := ih
      simp only [Set.mem_iInter] at hx0
      rcases hr.1 x0 (hKX hx0K) a.1 (hKX a.2) with h | h
      · refine ⟨x0, hx0K, ?_⟩
        simp only [Set.mem_iInter, Finset.mem_insert]
        rintro y (rfl | hy)
        · exact ⟨hx0K, h⟩
        · exact hx0 y hy
      · refine ⟨a.1, a.2, ?_⟩
        simp only [Set.mem_iInter, Finset.mem_insert]
        rintro y (rfl | hy)
        · refine ⟨y.2, ?_⟩
          rcases hr.1 y.1 (hKX y.2) y.1 (hKX y.2) with h' | h' <;> exact h'
        · exact ⟨a.2, hr.2 _ (hKX a.2) _ (hKX hx0K) _ (hKX y.2) h (hx0 y hy).2⟩
  obtain ⟨x, hxK, hx⟩ := hK.inter_iInter_nonempty C hCc hfin
  simp only [Set.mem_iInter] at hx
  exact ⟨x, hxK, fun y hy => (hx ⟨y, hy⟩).2⟩

/-- Local nonsatiation below the budget, quantitatively: if `p·x < w` there is `y ∈ X`, `y ≻ x`,
with `p·y < w` and every coordinate of `y` within `δ` of `x`. -/
theorem bb_lns_near {X : Set (Fin L → ℝ)} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hlns : LocallyNonsatiated X r) (p : Fin L → ℝ) {x : Fin L → ℝ} (hx : x ∈ X) {w : ℝ}
    (hlt : p ⬝ᵥ x < w) {δ : ℝ} (hδ : 0 < δ) :
    ∃ y ∈ X, p ⬝ᵥ y < w ∧ Strict r y x ∧ ∀ l, |y l - x l| < δ := by
  set c := ∑ l, |p l| with hc
  have hc0 : 0 ≤ c := Finset.sum_nonneg fun l _ => abs_nonneg _
  set ε := min (δ / 2) ((w - p ⬝ᵥ x) / (c + 1)) with hε
  have hεpos : 0 < ε := lt_min (by linarith) (div_pos (by linarith) (by linarith))
  obtain ⟨y, hy, hd, hs⟩ := hlns x hx ε hεpos
  refine ⟨y, hy, ?_, hs, fun l => ?_⟩
  · have h1 := abs_dotProduct_sub_le p x y
    have h2 : c * euclidDist y x ≤ c * ε := mul_le_mul_of_nonneg_left hd hc0
    have h4 : ε ≤ (w - p ⬝ᵥ x) / (c + 1) := min_le_right _ _
    have h3 : c * ε < w - p ⬝ᵥ x := by
      have h5 : c * ε ≤ c * ((w - p ⬝ᵥ x) / (c + 1)) := mul_le_mul_of_nonneg_left h4 hc0
      have h6 : c * ((w - p ⬝ᵥ x) / (c + 1)) < w - p ⬝ᵥ x := by
        rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
        nlinarith
      linarith
    have := (abs_le.mp h1).2
    linarith
  · have h1 := abs_sub_le_euclidDist y x l
    have h2 : ε ≤ δ / 2 := min_le_left _ _
    linarith

/-- Reflexivity of a complete relation on its domain. -/
theorem bb_refl {X : Set (Fin L → ℝ)} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hr : RationalOn X r) {x : Fin L → ℝ} (hx : x ∈ X) : r x x := by
  rcases hr.1 x hx x hx with h | h <;> exact h

/-- Under completeness, "not strictly better" is "weakly worse". -/
theorem bb_not_strict {X : Set (Fin L → ℝ)} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hr : RationalOn X r) {x y : Fin L → ℝ} (hx : x ∈ X) (hy : y ∈ X)
    (h : ¬ Strict r x y) : r y x := by
  rcases hr.1 x hx y hy with hxy | hyx
  · by_contra hn
    exact h ⟨hxy, hn⟩
  · exact hyx

/-- **Section 17.BB** (MWG, p. 632). With local nonsatiation (and rational `≿ᵢ`), when the
budget binds (`p·x*ᵢ = wᵢ`) condition (ii') is equivalent to `x*ᵢ` minimizing expenditure at
`p` on `{xᵢ ∈ Xᵢ : xᵢ ≿ᵢ x*ᵢ}`. -/
theorem smalltype_17_BB_expenditure {X : Set (Fin L → ℝ)}
    {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop} (hr : RationalOn X r)
    (hlns : LocallyNonsatiated X r) {p xs : Fin L → ℝ} (hxs : xs ∈ X) :
    (∀ x ∈ X, Strict r x xs → p ⬝ᵥ xs ≤ p ⬝ᵥ x) ↔ (∀ x ∈ X, r x xs → p ⬝ᵥ xs ≤ p ⬝ᵥ x) := by
  constructor
  · intro h x hx hrx
    by_contra hlt
    push Not at hlt
    obtain ⟨x', hx'X, hx'c, hx's, -⟩ := bb_lns_near hlns p hx hlt one_pos
    have hs : Strict r x' xs :=
      ⟨hr.2 _ hx'X _ hx _ hxs hx's.1 hrx, fun h' => hx's.2 (hr.2 _ hx _ hxs _ hx'X hrx h')⟩
    exact absurd (h x' hx'X hs) (not_le.mpr hx'c)
  · exact fun h x hx hs => h x hx hs.1

/-! ### Proposition 17.BB.1 and the small type of p. 633 -/

/-- **Proposition 17.BB.1** (MWG, p. 633). With `Xᵢ` convex and `≿ᵢ` continuous (and rational,
the standing assumption), a consumer who at the quasiequilibrium `(x*, y*, p)` satisfies the
cheaper consumption condition is preference maximizing in his budget set. -/
theorem proposition_17_BB_1 {E : PrivPrefEconomy ι κ L} {a : Allocation ι κ L}
    {p : Fin L → ℝ} (hq : IsWalrasQuasiEqm E a p) {i : ι} (hX : Convex ℝ (E.X i))
    (hr : RationalOn (E.X i) (E.pref i)) (hc : PrefContinuous (E.X i) (E.pref i))
    (hcheap : CheaperConsumption E a p i) :
    IsMaximalFor (E.pref i) (budgetSetOn (E.X i) p (E.wealth a p i)) (a.x i) := by
  obtain ⟨hxi, hbud, hquasi⟩ := hq.2.2.1 i
  obtain ⟨xc, hxcX, hxc⟩ := hcheap
  refine ⟨⟨hxi, hbud⟩, fun x' hx' => ?_⟩
  set w := E.wealth a p i
  set t : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with ht
  have ht0 : ∀ n, 0 < t n := fun n => by positivity
  have ht1 : ∀ n, t n ≤ 1 := fun n => by
    simp only [ht]
    rw [div_le_one (by positivity)]
    linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  set xs : ℕ → Fin L → ℝ := fun n => x' + t n • (xc - x') with hxs
  have hmem : ∀ n, xs n ∈ E.X i := fun n =>
    hX.add_smul_sub_mem hx'.1 hxcX ⟨(ht0 n).le, ht1 n⟩
  have hcost : ∀ n, p ⬝ᵥ xs n < w := fun n => by
    simp only [hxs, dotProduct_add, dotProduct_smul, dotProduct_sub, smul_eq_mul]
    have := hx'.2
    nlinarith [ht0 n, ht1 n]
  have hlim : Tendsto xs atTop (𝓝 x') := by
    have ht' : Tendsto t atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have h := (ht'.smul_const (xc - x')).const_add x'
    simpa using h
  have hle : ∀ n, E.pref i (a.x i) (xs n) := fun n =>
    bb_not_strict hr (hmem n) hxi fun hs => absurd (hquasi _ (hmem n) hs) (not_le.mpr (hcost n))
  exact hc (fun _ => a.x i) xs (a.x i) x' (fun _ => hxi) hmem hxi hx'.1 hle tendsto_const_nhds
    hlim

/-- **Proposition 17.BB.1** (MWG, p. 633), second sentence: if the cheaper consumption condition
holds for every consumer, the quasiequilibrium is a Walrasian equilibrium. -/
theorem proposition_17_BB_1_eqm {E : PrivPrefEconomy ι κ L} {a : Allocation ι κ L}
    {p : Fin L → ℝ} (hq : IsWalrasQuasiEqm E a p) (hX : ∀ i, Convex ℝ (E.X i))
    (hr : ∀ i, RationalOn (E.X i) (E.pref i)) (hc : ∀ i, PrefContinuous (E.X i) (E.pref i))
    (hcheap : ∀ i, CheaperConsumption E a p i) : E.IsWalrasEqm a p :=
  ⟨hq.2.1, fun i => proposition_17_BB_1 hq (hX i) (hr i) (hc i) (hcheap i), hq.2.2.2⟩

omit [Fintype ι] in
/-- At a quasiequilibrium with `0 ∈ Yⱼ` and `θ ≥ 0`, profits are nonnegative and wealth is at
least `p·ωᵢ`. -/
theorem bb_wealth_ge {E : PrivPrefEconomy ι κ L} {a : Allocation ι κ L} {p : Fin L → ℝ}
    (hsup : ∀ j, a.y j ∈ supply (E.Y j) p) (h0 : ∀ j, (0 : Fin L → ℝ) ∈ E.Y j)
    (hθ : ∀ i j, 0 ≤ E.θ i j) (i : ι) : p ⬝ᵥ E.ωi i ≤ E.wealth a p i := by
  unfold PrivPrefEconomy.wealth
  have : 0 ≤ ∑ j, E.θ i j * (p ⬝ᵥ a.y j) := Finset.sum_nonneg fun j _ =>
    mul_nonneg (hθ i j) (by simpa using (hsup j).2 0 (h0 j))
  linarith

/-- **Small type, situation (a)** (MWG, p. 633; Exercise 17.BB.1 reference). If `0 ∈ Yⱼ`,
`θ ≥ 0`, and `ωᵢ ≫ x̂ᵢ` for some `x̂ᵢ ∈ Xᵢ`, then at a quasiequilibrium with `p ≥ 0`, `p ≠ 0`
consumer `i` satisfies the cheaper consumption condition. -/
theorem smalltype_17_BB_cheaper_a {E : PrivPrefEconomy ι κ L} {a : Allocation ι κ L}
    {p : Fin L → ℝ} (hq : IsWalrasQuasiEqm E a p) (h0 : ∀ j, (0 : Fin L → ℝ) ∈ E.Y j)
    (hθ : ∀ i j, 0 ≤ E.θ i j) (hp : ∀ l, 0 ≤ p l) {i : ι} {xh : Fin L → ℝ}
    (hxh : xh ∈ E.X i) (hω : ∀ l, xh l < E.ωi i l) : CheaperConsumption E a p i := by
  refine ⟨xh, hxh, ?_⟩
  have h1 := bb_wealth_ge hq.2.1 h0 hθ i
  have h2 := dotProduct_pos_of_nonneg_ne_zero (x := E.ωi i - xh) hp hq.1
    (fun l => sub_pos.mpr (hω l))
  rw [dotProduct_sub] at h2
  linarith

/-- **Small type, situation (b)** (MWG, p. 633). If `0 ∈ Yⱼ`, `θ ≥ 0`, `x̂ᵢ ∈ Xᵢ` with
`ωᵢ ≥ x̂ᵢ`, `ωᵢ ≠ x̂ᵢ`, then at a quasiequilibrium with `p ≫ 0` consumer `i` satisfies the
cheaper consumption condition. -/
theorem smalltype_17_BB_cheaper_b {E : PrivPrefEconomy ι κ L} {a : Allocation ι κ L}
    {p : Fin L → ℝ} (hq : IsWalrasQuasiEqm E a p) (h0 : ∀ j, (0 : Fin L → ℝ) ∈ E.Y j)
    (hθ : ∀ i j, 0 ≤ E.θ i j) (hp : ∀ l, 0 < p l) {i : ι} {xh : Fin L → ℝ}
    (hxh : xh ∈ E.X i) (hle : xh ≤ E.ωi i) (hne : E.ωi i ≠ xh) :
    CheaperConsumption E a p i := by
  refine ⟨xh, hxh, ?_⟩
  have h1 := bb_wealth_ge hq.2.1 h0 hθ i
  obtain ⟨l, hl⟩ : ∃ l, E.ωi i l ≠ xh l := by
    by_contra hall
    push Not at hall
    exact hne (funext hall)
  have h2 : 0 < p ⬝ᵥ (E.ωi i - xh) := by
    refine Finset.sum_pos' (fun k _ => mul_nonneg (hp k).le (sub_nonneg.mpr (hle k)))
      ⟨l, Finset.mem_univ l, mul_pos (hp l) (sub_pos.mpr (lt_of_le_of_ne (hle l) (Ne.symm hl)))⟩
  rw [dotProduct_sub] at h2
  linarith

/-- **Small type** (MWG, p. 633). If some production set has free disposal, `p ≥ 0` at any
profit maximizing price (in particular at any quasiequilibrium). -/
theorem smalltype_17_BB_price_nonneg {Y : Set (Fin L → ℝ)} (hfd : FreeDisposal Y)
    {p y : Fin L → ℝ} (h : y ∈ supply Y p) : ∀ l, 0 ≤ p l := by
  intro l
  by_contra hneg
  push Not at hneg
  have hmem : y - Pi.single l 1 ∈ Y := hfd y h.1 _ fun k => by
    by_cases hk : k = l
    · subst hk; simp
    · simp [hk]
  have := h.2 _ hmem
  rw [dotProduct_sub] at this
  simp at this
  linarith

/-- **Small type** (MWG, p. 633). Positive prices: if `p ≥ 0` at a quasiequilibrium (shares
summing to one), the weak condition `∑ᵢ x̂ᵢ ≪ ∑ᵢ ωᵢ + ∑ⱼ ŷⱼ` holds for some `x̂ᵢ ∈ Xᵢ`,
`ŷⱼ ∈ Yⱼ`, and every consumer has a convex consumption set with `Xᵢ + ℝ^L₊ ⊆ Xᵢ` and rational,
continuous, strongly monotone preferences, then `p ≫ 0`: some consumer has wealth above
`p·x̂ᵢ`, hence is preference maximizing (Proposition 17.BB.1), which strong monotonicity rules
out at a zero price. -/
theorem smalltype_17_BB_price_pos {E : PrivPrefEconomy ι κ L} {a : Allocation ι κ L}
    {p : Fin L → ℝ} (hq : IsWalrasQuasiEqm E a p) (hp : ∀ l, 0 ≤ p l)
    (hθ : ∀ j, ∑ i, E.θ i j = 1) {xh : ι → Fin L → ℝ} {yh : κ → Fin L → ℝ}
    (hxh : ∀ i, xh i ∈ E.X i) (hyh : ∀ j, yh j ∈ E.Y j)
    (hweak : ∀ l, (∑ i, xh i) l < (∑ i, E.ωi i + ∑ j, yh j) l)
    (hXup : ∀ i, ∀ x ∈ E.X i, ∀ v : Fin L → ℝ, 0 ≤ v → x + v ∈ E.X i)
    (hX : ∀ i, Convex ℝ (E.X i)) (hr : ∀ i, RationalOn (E.X i) (E.pref i))
    (hc : ∀ i, PrefContinuous (E.X i) (E.pref i))
    (hmono : ∀ i, PrefStronglyMonotone (E.X i) (E.pref i)) : ∀ l, 0 < p l := by
  have hlt : p ⬝ᵥ ∑ i, xh i < p ⬝ᵥ (∑ i, E.ωi i + ∑ j, yh j) := by
    have := dotProduct_pos_of_nonneg_ne_zero
      (x := (∑ i, E.ωi i + ∑ j, yh j) - ∑ i, xh i) hp hq.1 (fun l => sub_pos.mpr (hweak l))
    rw [dotProduct_sub] at this
    linarith
  have hsumw := E.sum_wealth hθ a p
  have hprof : ∑ j, p ⬝ᵥ yh j ≤ ∑ j, p ⬝ᵥ a.y j :=
    Finset.sum_le_sum fun j _ => (hq.2.1 j).2 _ (hyh j)
  have hlt2 : ∑ i, p ⬝ᵥ xh i < ∑ i, E.wealth a p i := by
    rw [hsumw]
    simp only [PrivPrefEconomy.toEconomy]
    rw [dotProduct_add, dotProduct_finset_sum p xh, dotProduct_finset_sum p yh] at hlt
    linarith
  obtain ⟨i, -, hi⟩ := Finset.exists_lt_of_sum_lt hlt2
  have hmax := proposition_17_BB_1 hq (hX i) (hr i) (hc i) ⟨xh i, hxh i, hi⟩
  intro l
  by_contra hl
  have hpl : p l = 0 := le_antisymm (not_lt.mp hl) (hp l)
  have hmem : a.x i + Pi.single l 1 ∈ E.X i :=
    hXup i _ hmax.1.1 _ fun k => by
      by_cases hk : k = l
      · subst hk; simp
      · simp [hk]
  have hstrict := hmono i _ hmax.1.1 _ hmem (by simp) (by simp)
  have hb : a.x i + Pi.single l 1 ∈ budgetSetOn (E.X i) p (E.wealth a p i) := by
    refine ⟨hmem, ?_⟩
    rw [dotProduct_add, dotProduct_single, hpl, zero_mul, add_zero]
    exact hmax.1.2
  exact hstrict.2 (hmax.2 _ hb)

/-! ### Exercises 17.BB.4 and 17.BB.5 -/

/-- **Exercise 17.BB.4** (MWG, p. 650). If `(x*, y*, p)` is a free-disposal quasiequilibrium and
firm `j₀` has free disposal, replacing `y*_{j₀}` by `y*_{j₀} - s`, with
`s = ∑ᵢ ωᵢ + ∑ⱼ y*ⱼ - ∑ᵢ x*ᵢ ≥ 0` the excess supply, gives a Walrasian quasiequilibrium (with
the same consumptions and price). -/
theorem exercise_17_BB_4 {E : PrivPrefEconomy ι κ L} {a : Allocation ι κ L}
    {p : Fin L → ℝ} (hq : IsFreeDisposalQuasiEqm E a p) (j₀ : κ) (hfd : FreeDisposal (E.Y j₀)) :
    ∃ y' : κ → Fin L → ℝ, (∀ j, j ≠ j₀ → y' j = a.y j) ∧ y' j₀ ≤ a.y j₀ ∧
      IsWalrasQuasiEqm E ⟨a.x, y'⟩ p := by
  classical
  obtain ⟨hp0, hsup, hcons, hle, hval⟩ := hq
  set s : Fin L → ℝ := ∑ i, E.ωi i + ∑ j, a.y j - ∑ i, a.x i with hs
  have hs0 : 0 ≤ s := sub_nonneg.mpr hle
  have hps : p ⬝ᵥ s = 0 := by
    have : s = -(∑ i, a.x i - ∑ i, E.ωi i - ∑ j, a.y j) := by rw [hs]; abel
    rw [this, dotProduct_neg, hval, neg_zero]
  set y' : κ → Fin L → ℝ := fun j => a.y j - if j = j₀ then s else 0 with hy'
  have hpy : ∀ j, p ⬝ᵥ y' j = p ⬝ᵥ a.y j := fun j => by
    simp only [hy', dotProduct_sub]
    split_ifs
    · rw [hps, sub_zero]
    · simp
  have hw : ∀ i, E.wealth ⟨a.x, y'⟩ p i = E.wealth a p i := fun i => by
    simp only [PrivPrefEconomy.wealth, hpy]
  refine ⟨y', fun j hj => by simp [hy', hj], by simp [hy', hs0], hp0, fun j => ?_,
    fun i => ?_, ?_⟩
  · by_cases hj : j = j₀
    · subst hj
      refine ⟨hfd _ (hsup j).1 _ (by simp [hy', hs0]), fun y hy => ?_⟩
      rw [hpy]
      exact (hsup j).2 y hy
    · have : y' j = a.y j := by simp [hy', hj]
      change y' j ∈ _
      rw [this]
      exact hsup j
  · rw [hw]
    exact hcons i
  · change ∑ i, a.x i = ∑ i, E.ωi i + ∑ j, y' j
    simp only [hy', Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    rw [hs]
    abel

/-- **Exercise 17.BB.5** (MWG, p. 650; the missing step of Lemma 17.BB.5). If `≿ᵢ` is rational
and convex on `Xᵢ` and `xᵢ, x'ᵢ ∈ Xᵢ`, then for `x_{iα} = αxᵢ + (1 - α)x'ᵢ`, `α ∈ [0, 1]`,
`xᵢ ≻ᵢ x_{iα}` and `x'ᵢ ≻ᵢ x_{iα}` cannot both hold. -/
theorem exercise_17_BB_5 {X : Set (Fin L → ℝ)} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hr : RationalOn X r) (hconv : PrefConvex X r) {x x' : Fin L → ℝ} (hx : x ∈ X)
    (hx' : x' ∈ X) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    ¬ (Strict r x (α • x + (1 - α) • x') ∧ Strict r x' (α • x + (1 - α) • x')) := by
  rintro ⟨h1, h2⟩
  rcases hr.1 x hx x' hx' with h | h
  · have hmem : α • x + (1 - α) • x' ∈ upperContour X r x' :=
      hconv x' hx' (⟨hx, h⟩ : x ∈ upperContour X r x') ⟨hx', bb_refl hr hx'⟩ hα0
        (by linarith) (by ring)
    exact h2.2 hmem.2
  · have hmem : α • x + (1 - α) • x' ∈ upperContour X r x :=
      hconv x hx (⟨hx, bb_refl hr hx⟩ : x ∈ upperContour X r x) ⟨hx', h⟩ hα0
        (by linarith) (by ring)
    exact h1.2 hmem.2

/-- With convex preferences, a convex combination of two bundles each `≿ᵢ`-above `z` is above
`z` (the form of convexity used in Lemmas 17.BB.1 and 17.BB.5). -/
theorem bb_convex_comb {X : Set (Fin L → ℝ)} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hconv : PrefConvex X r) {z x x' : Fin L → ℝ} (hz : z ∈ X) (hx : x ∈ X) (hx' : x' ∈ X)
    (h : r x z) (h' : r x' z) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    x + t • (x' - x) ∈ X ∧ r (x + t • (x' - x)) z := by
  have hmem := hconv z hz (⟨hx, h⟩ : x ∈ upperContour X r z) ⟨hx', h'⟩ (sub_nonneg.mpr ht1)
    ht0 (by ring)
  have heq : (1 - t) • x + t • x' = x + t • (x' - x) := by module
  rw [heq] at hmem
  exact hmem

/-! ### Footnote 80: local nonsatiation is needed -/

/-- **Figure 17.BB.2 / footnote 80** (MWG, pp. 634-635). An Edgeworth box (`Xᵢ = ℝ²₊`,
`ωᵢ = (1, 1)`, the free disposal technology `Y = -ℝ²₊`): consumer 0 treats both goods as bads
(`u₀(x) = -(x₁ + x₂)`, satiated at the origin), consumer 1 has strongly monotone preferences
(`u₁(x) = x₁ + x₂`). -/
noncomputable def fig17BB2Economy : PrivPrefEconomy (Fin 2) Unit 2 where
  X := fun _ => nonnegOrthant 2
  pref := fun i => utilityPref (if i = 0 then fun x => -(x 0 + x 1) else fun x => x 0 + x 1)
  Y := fun _ => nonposOrthant 2
  ωi := fun _ => fun _ => 1
  θ := fun _ _ => 1 / 2

/-- **Footnote 80** (MWG, p. 634). The economy of Figure 17.BB.2 has no Walrasian
quasiequilibrium: by free disposal `p ≥ 0` and profits vanish, so both consumers have wealth
`p·ωᵢ > 0`; feasibility and consumer 1's budget give `p·x*₀ ≥ p·ω₀ > 0`, so `x*₀ ≠ 0`; but
consuming nothing costs zero and is preferred by consumer 0, violating (ii'). -/
theorem footnote_17_BB_80 : ¬ ∃ (a : Allocation (Fin 2) Unit 2) (p : Fin 2 → ℝ),
    IsWalrasQuasiEqm fig17BB2Economy a p := by
  rintro ⟨a, p, hp0, hsup, hcons, hclear⟩
  have hp : ∀ l, 0 ≤ p l := footnote_9 (hsup ())
  have hprof : p ⬝ᵥ a.y () = 0 := by
    refine le_antisymm ?_ (by simpa using (hsup ()).2 0 (fun _ => le_refl 0))
    have hy := (hsup ()).1
    simp only [dotProduct, Fin.sum_univ_two]
    nlinarith [hy 0, hy 1, hp 0, hp 1]
  have hpos : 0 < p 0 + p 1 := by
    rcases (hp 0).lt_or_eq with h | h
    · linarith [hp 1]
    rcases (hp 1).lt_or_eq with h' | h'
    · linarith
    exact absurd (funext fun l => by fin_cases l <;> simp [← h, ← h']) hp0
  have hw : ∀ i, fig17BB2Economy.wealth a p i = p 0 + p 1 := fun i => by
    unfold PrivPrefEconomy.wealth
    rw [show ∑ j, fig17BB2Economy.θ i j * (p ⬝ᵥ a.y j) = 0 by simp [hprof]]
    simp [fig17BB2Economy, dotProduct, Fin.sum_univ_two]
  have hsum : p ⬝ᵥ a.x 0 + p ⬝ᵥ a.x 1 = 2 * (p 0 + p 1) := by
    have := congrArg (fun v => p ⬝ᵥ v) hclear
    simp only [Fin.sum_univ_two, dotProduct_add, Finset.univ_unique, Finset.sum_singleton,
      hprof] at this
    rw [this]
    simp [fig17BB2Economy, dotProduct, Fin.sum_univ_two]
    ring
  have h1 := (hcons 1).2.1
  rw [hw] at h1
  have hx0 : 0 < p ⬝ᵥ a.x 0 := by linarith
  have hx0mem : a.x 0 ∈ nonnegOrthant 2 := (hcons 0).1
  have hu : 0 < a.x 0 0 + a.x 0 1 := by
    simp only [dotProduct, Fin.sum_univ_two] at hx0
    by_contra hn
    push Not at hn
    have e0 : a.x 0 0 = 0 := le_antisymm (by linarith [hx0mem 1]) (hx0mem 0)
    have e1 : a.x 0 1 = 0 := le_antisymm (by linarith [hx0mem 0]) (hx0mem 1)
    rw [e0, e1] at hx0
    simp at hx0
  have hstrict : Strict (fig17BB2Economy.pref 0) 0 (a.x 0) := by
    simp only [fig17BB2Economy, ↓reduceIte, Strict, utilityPref, Pi.zero_apply]
    constructor <;> linarith
  have := (hcons 0).2.2 0 (fun _ => le_refl 0) hstrict
  rw [hw] at this
  simp at this
  linarith

end MWG.PositiveEquilibriumTheory
