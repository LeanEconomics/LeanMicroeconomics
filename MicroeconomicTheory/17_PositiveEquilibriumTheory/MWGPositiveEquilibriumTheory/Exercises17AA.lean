/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPositiveEquilibriumTheory.NegishiApproach

/-!
# Exercise 17.AA.2: existence of equilibrium through the welfare equations
(MWG Appendix A, pp. 630-631; Exercise 17.AA.2, p. 649)

The economy of Appendix A with `ωᵢ ≫ 0` for every `i` (`NegishiHyp`). As the exercise assumes,
`g(s)` is a function: the normalized supporting price `p(s) ∈ Δ` of `x(s)` is unique
(`NegishiHyp.price_unique`; the exercise's sufficient condition, differentiable utilities with
one consumer consuming every good, is the mechanism behind the instance in
`NegishiLogEconomy`). `negishiPrice E s` is `p(s)` and `negishiG E s i = p(s)·[ωᵢ - xᵢ(s)]` is
`gᵢ(s)` of (17.AA.1).

* (a) `g` is continuous on `Δ` (`exercise_17_AA_2a`): `x(·)` and `p(·)` have closed graphs and
  values in compact sets (`continuousOn_of_seq_graph`); the limit of supporting prices supports
  weakly, hence strictly (`quasiSupport_isSupporting`).
* (b) `∑ᵢ gᵢ(s) = 0` (`exercise_17_AA_2b`).
* (c) `sᵢ = 0` implies `gᵢ(s) > 0` (`exercise_17_AA_2c`): `uᵢ(xᵢ(s)) = 0` forces `xᵢ(s) = 0`.
* (d) a zero of `g` exists, by Brouwer's theorem applied to the map `f(s) = (s + g⁺(s))/α(s)` of
  Proposition 17.C.2 (`negishi_fixed_point`), and it is a Walrasian equilibrium
  (`exercise_17_AA_2d`).
-/

namespace MWG.PositiveEquilibriumTheory

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.GeneralEquilibriumExamples MWG.WelfareTheorems
open Filter Topology

variable {I L : ℕ}

/-- **Appendix A** (MWG, p. 631). The normalized supporting price `p(s) ∈ Δ` of `x(s)` (chosen),
and the barycentre of `Δ` when none exists. -/
noncomputable def negishiPrice (E : ExchangeEconomy (Fin I) L) (s : Fin I → ℝ) : Fin L → ℝ :=
  open Classical in
  if h : ∃ p, p ∈ priceSimplex L ∧ IsSupportingPrice E (negishiAlloc E s) p then h.choose
  else fun _ => (L : ℝ)⁻¹

/-- **(17.AA.1)** (MWG, p. 631). `gᵢ(s) = p(s)·[ωᵢ - xᵢ(s)]`. -/
noncomputable def negishiG (E : ExchangeEconomy (Fin I) L) (s : Fin I → ℝ) : Fin I → ℝ :=
  fun i => negishiPrice E s ⬝ᵥ (E.ω i - negishiAlloc E s i)

/-- **Exercise 17.AA.2** (MWG, p. 649). The hypotheses: at least one consumer and one good,
`Xᵢ = ℝ^L₊`, continuous, strictly convex, strongly monotone preferences represented by `uᵢ` with
`uᵢ(0) = 0`, `ωᵢ ≫ 0` for every `i`, and "`g(s)` is a function": for every `s ∈ Δ` the
supporting price of `x(s)` in `Δ` is unique. -/
structure NegishiHyp (E : ExchangeEconomy (Fin I) L) : Prop where
  /-- `I ≥ 1`. -/
  I_pos : 0 < I
  /-- `L ≥ 1`. -/
  L_pos : 0 < L
  /-- `Xᵢ = ℝ^L₊`. -/
  X_eq : ∀ i, E.X i = nonnegOrthant L
  /-- Continuous, strictly convex, strongly monotone preferences. -/
  standard : ∀ i, StandardUtility (E.u i)
  /-- `uᵢ(0) = 0`. -/
  u_zero : ∀ i, E.u i 0 = 0
  /-- `ωᵢ ≫ 0`. -/
  ω_pos : ∀ i, E.ω i ∈ posOrthant L
  /-- `g(s)` is a function: the normalized supporting price of `x(s)` is unique. -/
  price_unique : ∀ s ∈ priceSimplex I, ∀ p q, p ∈ priceSimplex L → q ∈ priceSimplex L →
    IsSupportingPrice E (negishiAlloc E s) p → IsSupportingPrice E (negishiAlloc E s) q → p = q

namespace NegishiHyp

variable {E : ExchangeEconomy (Fin I) L}

/-- Endowments are in the consumption sets. -/
theorem ω_mem (h : NegishiHyp E) (i : Fin I) : E.ω i ∈ nonnegOrthant L :=
  fun l => (h.ω_pos i l).le

/-- `∑ᵢ ωᵢ ≫ 0`. -/
theorem total_pos (h : NegishiHyp E) (l : Fin L) : 0 < E.totalEndowment l := by
  rw [ExchangeEconomy.totalEndowment, Finset.sum_apply]
  exact Finset.sum_pos (fun i _ => h.ω_pos i l) ⟨⟨0, h.I_pos⟩, Finset.mem_univ _⟩

/-- `x(s)` is the Pareto optimal allocation with utilities proportional to `s ∈ Δ`. -/
theorem alloc_spec (h : NegishiHyp E) {s : Fin I → ℝ} (hs : s ∈ priceSimplex I) :
    IsNegishiAlloc E s (negishiAlloc E s) :=
  negishiAlloc_spec h.X_eq (fun i => (h.standard i).1) (fun i => (h.standard i).2.2) h.u_zero
    h.ω_mem hs

/-- `x(s)` is feasible. -/
theorem alloc_inBox (h : NegishiHyp E) (s : Fin I → ℝ) : E.InBox (negishiAlloc E s) :=
  negishiAlloc_inBox (fun i => (h.X_eq i).symm ▸ h.ω_mem i) s

/-- `p(s) ∈ Δ` supports `x(s)`. -/
theorem price_spec (h : NegishiHyp E) {s : Fin I → ℝ} (hs : s ∈ priceSimplex I) :
    negishiPrice E s ∈ priceSimplex L ∧
      IsSupportingPrice E (negishiAlloc E s) (negishiPrice E s) := by
  obtain ⟨p, hp, -, hsup⟩ := supportingPrice_exists h.L_pos h.X_eq h.standard h.total_pos
    (h.alloc_spec hs).1
  have hex : ∃ p, p ∈ priceSimplex L ∧ IsSupportingPrice E (negishiAlloc E s) p := ⟨p, hp, hsup⟩
  unfold negishiPrice
  simp only [hex, ↓reduceDIte]
  exact hex.choose_spec

/-- `p(s) ∈ Δ` for every `s`. -/
theorem price_mem (h : NegishiHyp E) (s : Fin I → ℝ) : negishiPrice E s ∈ priceSimplex L := by
  unfold negishiPrice
  by_cases hex : ∃ p, p ∈ priceSimplex L ∧ IsSupportingPrice E (negishiAlloc E s) p
  · simp only [hex, ↓reduceDIte]
    exact hex.choose_spec.1
  · simp only [hex, ↓reduceDIte]
    have hL : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.2 h.L_pos.ne'
    refine ⟨fun _ => inv_nonneg.2 (Nat.cast_nonneg _), ?_⟩
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_inv_cancel₀ hL

end NegishiHyp

/-! ### Continuity through closed graphs -/

/-- A function into a compact set whose graph is sequentially closed over `S` is continuous on
`S`. -/
theorem continuousOn_of_seq_graph {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {f : X → Y} {S : Set X} {K : Set Y} (hK : IsCompact K) (hfK : ∀ s, f s ∈ K)
    (hg : ∀ (ss : ℕ → X) (s : X) (y : Y), s ∈ S → Tendsto ss atTop (𝓝[S] s) →
      Tendsto (fun n => f (ss n)) atTop (𝓝 y) → f s = y) :
    ContinuousOn f S := by
  intro s hs
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨a, -, φ, hφ, hlim⟩ := hK.tendsto_subseq fun n => hfK (ns n)
  refine ⟨φ, ?_⟩
  have := hg (ns ∘ φ) s a hs (hns.comp hφ.tendsto_atTop) hlim
  rw [this]
  exact hlim

/-- Dot products of convergent sequences converge. -/
theorem tendsto_dotProduct {α : Type*} {F : Filter α} {f g : α → Fin L → ℝ} {a b : Fin L → ℝ}
    (hf : Tendsto f F (𝓝 a)) (hg : Tendsto g F (𝓝 b)) :
    Tendsto (fun n => f n ⬝ᵥ g n) F (𝓝 (a ⬝ᵥ b)) := by
  simp only [dotProduct]
  exact tendsto_finsetSum _ fun l _ =>
    ((continuous_apply l).continuousAt.tendsto.comp hf).mul
      ((continuous_apply l).continuousAt.tendsto.comp hg)

/-- **Exercise 17.AA.2(a)**, first step. `s ↦ x(s)` is continuous on `Δ`. -/
theorem negishiAlloc_continuousOn {E : ExchangeEconomy (Fin I) L} (h : NegishiHyp E) :
    ContinuousOn (negishiAlloc E) (priceSimplex I) := by
  have hc : ∀ i, ContinuousOn (E.u i) (nonnegOrthant L) := fun i => (h.standard i).1
  have hm : ∀ i, UtilityStronglyMonotone (E.u i) := fun i => (h.standard i).2.2
  have hsq : ∀ i, StrictlyQuasiconcaveOn (E.X i) (E.u i) := fun i => by
    rw [h.X_eq i]
    exact (h.standard i).2.1
  refine continuousOn_of_seq_graph (isCompact_inBox h.X_eq) h.alloc_inBox ?_
  intro ss s y hs hss hy
  obtain ⟨hss', hev⟩ := tendsto_nhdsWithin_iff.1 hss
  set xn : ℕ → Fin I → Fin L → ℝ := fun n => negishiAlloc E (ss n) with hxn
  have hxm : ∀ n i, xn n i ∈ nonnegOrthant L := fun n i => h.X_eq i ▸ (h.alloc_inBox (ss n)).1 i
  have hyK : E.InBox y := (isCompact_inBox h.X_eq).isClosed.mem_of_tendsto hy
    (Eventually.of_forall fun n => h.alloc_inBox (ss n))
  have hym : ∀ i, y i ∈ nonnegOrthant L := fun i => h.X_eq i ▸ hyK.1 i
  have hcoord : ∀ i, Tendsto (fun n => xn n i) atTop (𝓝 (y i)) := fun i =>
    (continuous_apply i).continuousAt.tendsto.comp hy
  have hulim : ∀ i, Tendsto (fun n => E.u i (xn n i)) atTop (𝓝 (E.u i (y i))) := fun i =>
    ((hc i) (y i) (hym i)).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨hcoord i, Eventually.of_forall fun n => hxm n i⟩)
  have hprop : ∀ i, E.u i (y i) = (∑ j, E.u j (y j)) * s i := by
    intro i
    have hR : Tendsto (fun n => (∑ j, E.u j (xn n j)) * ss n i) atTop
        (𝓝 ((∑ j, E.u j (y j)) * s i)) :=
      (tendsto_finsetSum _ fun j _ => hulim j).mul
        ((continuous_apply i).continuousAt.tendsto.comp hss')
    refine tendsto_nhds_unique_of_eventuallyEq (hulim i) hR ?_
    filter_upwards [hev] with n hn
    exact (h.alloc_spec hn).u_eq hn i
  have hpo : E.IsParetoOptimal y := by
    refine ⟨hyK, ?_⟩
    rintro ⟨x', hx', hdom, k, hk⟩
    have hxm' : ∀ i, x' i ∈ nonnegOrthant L := fun i => h.X_eq i ▸ hx'.1 i
    have hne0 : x' k ≠ 0 := by
      intro h0
      have := (hm k).le (x := (0 : Fin L → ℝ)) (fun _ => le_refl (0 : ℝ)) (hym k)
      rw [h.u_zero, ← h.u_zero k, ← h0] at this
      exact absurd hk (not_lt.2 this)
    obtain ⟨x'', hx'', hk'', hj''⟩ := negishi_redistribute h.X_eq hc hm hx' hne0 hk
    have hall : ∀ i, E.u i (y i) < E.u i (x'' i) := fun i => by
      by_cases hi : i = k
      · rw [hi]
        exact hk''
      · exact lt_of_le_of_lt (hdom i) (hj'' i hi)
    have hev2 : ∀ᶠ n in atTop, ∀ i, E.u i (xn n i) < E.u i (x'' i) :=
      eventually_all.2 fun i => (hulim i).eventually_lt_const (hall i)
    obtain ⟨n, hn1, hn2⟩ := (hev.and hev2).exists
    exact (h.alloc_spec hn1).1.2 ⟨x'', hx'', fun i => (hn2 i).le, ⟨0, h.I_pos⟩,
      hn2 ⟨0, h.I_pos⟩⟩
  have hs0 : s ≠ 0 := fun h0 => by
    have := hs.2
    simp [h0] at this
  exact negishiAlloc_unique hsq hs.1 hs0 (h.alloc_spec hs) ⟨hpo, _, hprop⟩

/-- **Exercise 17.AA.2(a)**, second step. `s ↦ p(s)` is continuous on `Δ`. -/
theorem negishiPrice_continuousOn {E : ExchangeEconomy (Fin I) L} (h : NegishiHyp E) :
    ContinuousOn (negishiPrice E) (priceSimplex I) := by
  have hc : ∀ i, ContinuousOn (E.u i) (nonnegOrthant L) := fun i => (h.standard i).1
  have hm : ∀ i, UtilityStronglyMonotone (E.u i) := fun i => (h.standard i).2.2
  have hxc := negishiAlloc_continuousOn h
  refine continuousOn_of_seq_graph (isCompact_priceSimplex L) h.price_mem ?_
  intro ss s y hs hss hy
  obtain ⟨-, hev⟩ := tendsto_nhdsWithin_iff.1 hss
  have hyΔ : y ∈ priceSimplex L := (isCompact_priceSimplex L).isClosed.mem_of_tendsto hy
    (Eventually.of_forall fun n => h.price_mem (ss n))
  have hxlim : Tendsto (fun n => negishiAlloc E (ss n)) atTop (𝓝 (negishiAlloc E s)) :=
    (hxc s hs).tendsto.comp hss
  have hq : IsQuasiSupportingPrice E (negishiAlloc E s) y := by
    intro i z hz hlt
    have hxm : ∀ t, negishiAlloc E t i ∈ nonnegOrthant L := fun t =>
      h.X_eq i ▸ (h.alloc_inBox t).1 i
    have hci : Tendsto (fun n => negishiAlloc E (ss n) i) atTop (𝓝 (negishiAlloc E s i)) :=
      (continuous_apply i).continuousAt.tendsto.comp hxlim
    have hul : Tendsto (fun n => E.u i (negishiAlloc E (ss n) i)) atTop
        (𝓝 (E.u i (negishiAlloc E s i))) :=
      ((hc i) _ (hxm s)).tendsto.comp
        (tendsto_nhdsWithin_iff.2 ⟨hci, Eventually.of_forall fun n => hxm (ss n)⟩)
    have hev2 := hul.eventually_lt_const hlt
    refine le_of_tendsto_of_tendsto (tendsto_dotProduct hy hci)
      (tendsto_dotProduct hy tendsto_const_nhds) ?_
    filter_upwards [hev, hev2] with n hn hn2
    exact ((h.price_spec hn).2 i z hz hn2).le
  obtain ⟨-, hsup⟩ := quasiSupport_isSupporting h.X_eq hc hm h.total_pos (h.alloc_inBox s) hyΔ hq
  obtain ⟨hpΔ, hpsup⟩ := h.price_spec hs
  exact h.price_unique s hs _ _ hpΔ hyΔ hpsup hsup

/-- **Exercise 17.AA.2(a)** (MWG, p. 649). `g(s)` is continuous on `Δ`. -/
theorem exercise_17_AA_2a {E : ExchangeEconomy (Fin I) L} (h : NegishiHyp E) :
    ContinuousOn (negishiG E) (priceSimplex I) := by
  have hp := negishiPrice_continuousOn h
  have hx := negishiAlloc_continuousOn h
  refine continuousOn_pi.2 fun i => ?_
  simp only [negishiG, dotProduct, Pi.sub_apply]
  exact continuousOn_finsetSum _ fun l _ =>
    ((continuous_apply l).comp_continuousOn hp).mul (continuousOn_const.sub
      ((continuous_apply l).comp_continuousOn ((continuous_apply i).comp_continuousOn hx)))

/-- **Exercise 17.AA.2(b)** (MWG, p. 649). A sort of Walras' law: `∑ᵢ gᵢ(s) = 0`. -/
theorem exercise_17_AA_2b {E : ExchangeEconomy (Fin I) L} (h : NegishiHyp E)
    (s : Fin I → ℝ) : ∑ i, negishiG E s i = 0 := by
  simp only [negishiG]
  rw [← dotProduct_sum, Finset.sum_sub_distrib, (h.alloc_inBox s).2]
  simp [ExchangeEconomy.totalEndowment]

/-- **Exercise 17.AA.2(c)** (MWG, p. 649). If `sᵢ = 0` then `gᵢ(s) > 0`: `uᵢ(xᵢ(s)) = 0`, so
`xᵢ(s) = 0` and `gᵢ(s) = p(s)·ωᵢ > 0`. -/
theorem exercise_17_AA_2c {E : ExchangeEconomy (Fin I) L} (h : NegishiHyp E)
    {s : Fin I → ℝ} (hs : s ∈ priceSimplex I) {i : Fin I} (hsi : s i = 0) :
    0 < negishiG E s i := by
  obtain ⟨-, t, ht⟩ := h.alloc_spec hs
  have hxm : negishiAlloc E s i ∈ nonnegOrthant L := h.X_eq i ▸ (h.alloc_inBox s).1 i
  have hx0 : negishiAlloc E s i = 0 := by
    by_contra hne
    have := (h.standard i).2.2.lt (x := (0 : Fin L → ℝ)) (fun _ => le_refl (0 : ℝ)) hxm hne
    rw [ht i, hsi, mul_zero, h.u_zero] at this
    exact lt_irrefl 0 this
  have hp := h.price_mem s
  have hp0 : negishiPrice E s ≠ 0 := fun h0 => by
    have := hp.2
    simp [h0] at this
  simp only [negishiG, hx0, sub_zero]
  exact dotProduct_pos_of_nonneg_ne_zero hp.1 hp0 (h.ω_pos i)

/-- **Exercise 17.AA.2(d)**, the fixed-point step (as in Proposition 17.C.2). A function `g` on
the simplex `Δ ⊆ ℝ^I` (`I ≥ 1`) that is continuous, satisfies `∑ᵢ gᵢ(s) = 0`, and has
`gᵢ(s) > 0` whenever `sᵢ = 0`, has a zero in `Δ`: Brouwer's theorem applied to
`f(s) = (s + g⁺(s))/α(s)`. -/
theorem negishi_fixed_point {g : (Fin I → ℝ) → Fin I → ℝ} (hI : 0 < I)
    (hc : ContinuousOn g (priceSimplex I)) (hW : ∀ s ∈ priceSimplex I, ∑ i, g s i = 0)
    (hb : ∀ s ∈ priceSimplex I, ∀ i, s i = 0 → 0 < g s i) :
    ∃ s ∈ priceSimplex I, g s = 0 := by
  have hne : (priceSimplex I).Nonempty := ⟨Pi.single ⟨0, hI⟩ 1, single_mem_priceSimplex _⟩
  obtain ⟨s, hs, hfix⟩ := LeanEconomics.FixedPoint.brouwer (isCompact_priceSimplex I)
    (convex_priceSimplex I) hne (brouwerMap_continuousOn hc) (brouwerMap_mapsTo g)
  refine ⟨s, hs, ?_⟩
  set α := ∑ l, (s l + zPlus g s l) with hαdef
  have hα : 1 ≤ α := one_le_sum_zPlus g hs
  have hα0 : 0 < α := by linarith
  have hfix' : ∀ i, s i + zPlus g s i = α * s i := by
    intro i
    have := congrFun hfix i
    simp only [brouwerMap, Pi.smul_apply, Pi.add_apply, smul_eq_mul, ← hαdef] at this
    rwa [inv_mul_eq_iff_eq_mul₀ hα0.ne'] at this
  have hzp : ∀ l, 0 ≤ zPlus g s l := fun l => le_max_right _ _
  have hge : ∀ i, 0 ≤ g s i := by
    intro i
    by_contra hneg
    push Not at hneg
    have hz : zPlus g s i = 0 := max_eq_right hneg.le
    have h1 := hfix' i
    rw [hz, add_zero] at h1
    rcases eq_or_lt_of_le hα with hα1 | hα1
    · have hsum0 : ∑ l, zPlus g s l = 0 := by
        have : α = ∑ l, s l + ∑ l, zPlus g s l := Finset.sum_add_distrib
        rw [hs.2] at this
        linarith
      have hall : ∀ l, g s l ≤ 0 := fun l => by
        have := (Finset.sum_eq_zero_iff_of_nonneg fun l _ => hzp l).1 hsum0 l
          (Finset.mem_univ _)
        exact max_eq_right_iff.1 this
      have := (Finset.sum_eq_zero_iff_of_nonpos fun l _ => hall l).1 (hW s hs) i
        (Finset.mem_univ _)
      linarith
    · have hsi : s i = 0 := by nlinarith [hs.1 i]
      exact absurd (hb s hs i hsi) (not_lt.2 hneg.le)
  funext i
  exact (Finset.sum_eq_zero_iff_of_nonneg fun l _ => hge l).1 (hW s hs) i (Finset.mem_univ _)

/-- **Exercise 17.AA.2(d)** (MWG, p. 649). Under the hypotheses of the exercise there is
`s* ∈ Δ` with `g(s*) = 0`, and `(x(s*), p(s*))` is a Walrasian equilibrium. -/
theorem exercise_17_AA_2d {E : ExchangeEconomy (Fin I) L} (h : NegishiHyp E) :
    ∃ s ∈ priceSimplex I, negishiG E s = 0 ∧
      E.IsWalrasEqm (negishiPrice E s) (negishiAlloc E s) := by
  obtain ⟨s, hs, hg⟩ := negishi_fixed_point h.I_pos (exercise_17_AA_2a h)
    (fun s _ => exercise_17_AA_2b h s) fun s hs i hsi => exercise_17_AA_2c h hs hsi
  refine ⟨s, hs, hg, ?_⟩
  rw [appendix_A_walras_iff h.L_pos h.X_eq (fun i => (h.standard i).2.2) (h.alloc_inBox s)
    (h.price_spec hs).2]
  exact fun i => congrFun hg i

end MWG.PositiveEquilibriumTheory
