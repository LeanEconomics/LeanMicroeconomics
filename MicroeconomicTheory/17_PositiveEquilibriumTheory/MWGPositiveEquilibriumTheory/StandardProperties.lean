/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPositiveEquilibriumTheory.DemandContinuity
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-!
# Proposition 17.B.2: the properties of aggregate excess demand (MWG pp. 581-582, 642)

Proposition 17.B.2 is derived from the primitives of the economy.

* `wealthExcessDemand u w c`: `z(p) = ∑ᵢ xᵢ(p, wᵢ(p)) - c(p)` for consumers with utilities `uᵢ`,
  wealth functions `wᵢ(p)` and a "supply" `c(p)` (the total endowment in exchange; the total
  endowment plus the firms' supplies with production, Exercise 17.B.4; redistributed wealth,
  Exercise 17.C.4). `isStandard_wealthExcessDemand`: if the utilities are continuous, strictly
  quasiconcave and strongly monotone, `wᵢ ≥ 0` and `c` are continuous on `ℝ^L_{++}`,
  homogeneous of degrees one and zero, `∑ᵢ wᵢ(p) = p·c(p)`, `c` is bounded above, and near
  every nonzero boundary price some consumer's wealth has a positive limit point, then `z`
  satisfies (i)-(v). Properties (i)-(iv) need only local nonsatiation (footnote 3).
* **Proposition 17.B.2** (`proposition_17_B_2`): for a pure exchange economy with
  `Xᵢ = ℝ^L₊`, continuous, strictly convex, strongly monotone preferences, `ωᵢ ∈ ℝ^L₊` and
  `∑ᵢ ωᵢ ≫ 0`, the excess demand `excessDemand E` satisfies (i)-(v). Property (v) is
  **Exercise 17.B.2** (`exercise_17_B_2`); **footnote 3** (`footnote_17_3`) gives (i)-(iv) under
  local nonsatiation.
* A concrete instance: `u(x) = ∑ₗ √xₗ` is a `StandardUtility` (`standardUtility_sqrtUtility`),
  and the two-consumer economy `sqrtEconomy` has a standard excess demand function.
* Correction: the book assumes only `∑ᵢ ωᵢ ≫ 0`; with an endowment outside `ℝ^L₊` demand can be
  empty at some `p ≫ 0` (`negEndowEconomy_demand_empty`), so `z` is not defined there. The
  results assume `ωᵢ ∈ ℝ^L₊`.
-/

namespace MWG.PositiveEquilibriumTheory

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.GeneralEquilibriumExamples
open Filter Topology

variable {ι : Type*} [Fintype ι] {L : ℕ}

/-! ### Transfer along agreement on `ℝ^L_{++}` -/

/-- The properties of Proposition 17.B.2 only involve the values on `ℝ^L_{++}`. -/
theorem IsStandardExcessDemand.congr {z z' : (Fin L → ℝ) → Fin L → ℝ}
    (h : IsStandardExcessDemand z) (heq : Set.EqOn z z' (posOrthant L)) :
    IsStandardExcessDemand z' where
  continuous := h.continuous.congr fun p hp => (heq hp).symm
  homogeneous := fun p hp α hα => by
    rw [← heq hp, ← heq (smul_mem_posOrthant hp hα), h.homogeneous p hp α hα]
  walras := fun p hp => by rw [← heq hp]; exact h.walras p hp
  boundedBelow := by
    obtain ⟨s, hs, hb⟩ := h.boundedBelow
    exact ⟨s, hs, fun p hp l => by rw [← heq hp]; exact hb p hp l⟩
  boundary := fun ps p hps hlim hp0 hl M => by
    filter_upwards [h.boundary ps p hps hlim hp0 hl M] with n hn
    rw [← heq (hps n)]
    exact hn

/-- With no commodities every function satisfies (i)-(v) trivially. -/
theorem isStandardExcessDemand_of_fin_zero (z : (Fin 0 → ℝ) → Fin 0 → ℝ) :
    IsStandardExcessDemand z where
  continuous := by
    have : z = fun _ => 0 := funext fun _ => funext fun l => l.elim0
    rw [this]
    exact continuousOn_const
  homogeneous := fun _ _ _ _ => funext fun l => l.elim0
  walras := fun _ _ => by simp [dotProduct]
  boundedBelow := ⟨1, one_pos, fun _ _ l => l.elim0⟩
  boundary := fun _ p _ _ hp0 => (hp0 (funext fun l => l.elim0)).elim

/-! ### The general theorem -/

/-- The excess demand `z(p) = ∑ᵢ xᵢ(p, wᵢ(p)) - c(p)` of consumers with utilities `uᵢ` on
`ℝ^L₊` and wealth functions `wᵢ`, against the supply `c(p)`. -/
noncomputable def wealthExcessDemand (u : ι → (Fin L → ℝ) → ℝ) (w : ι → (Fin L → ℝ) → ℝ)
    (c : (Fin L → ℝ) → Fin L → ℝ) (p : Fin L → ℝ) : Fin L → ℝ :=
  ∑ i, uDemand (u i) p (w i p) - c p

/-- Coordinates of `wealthExcessDemand`. -/
theorem wealthExcessDemand_apply (u : ι → (Fin L → ℝ) → ℝ) (w : ι → (Fin L → ℝ) → ℝ)
    (c : (Fin L → ℝ) → Fin L → ℝ) (p : Fin L → ℝ) (l : Fin L) :
    wealthExcessDemand u w c p l = ∑ i, uDemand (u i) p (w i p) l - c p l := by
  simp [wealthExcessDemand, Finset.sum_apply]

/-- **Proposition 17.B.2(i)**, general form: continuity. -/
theorem wealthExcessDemand_continuous {u : ι → (Fin L → ℝ) → ℝ} {w : ι → (Fin L → ℝ) → ℝ}
    {c : (Fin L → ℝ) → Fin L → ℝ} (hc : ∀ i, ContinuousOn (u i) (nonnegOrthant L))
    (hsq : ∀ i, StrictlyQuasiconcaveOn (nonnegOrthant L) (u i))
    (hwc : ∀ i, ContinuousOn (w i) (posOrthant L)) (hw0 : ∀ i, ∀ p ∈ posOrthant L, 0 ≤ w i p)
    (hcc : ContinuousOn c (posOrthant L)) : EDContinuous (wealthExcessDemand u w c) := by
  have hsum : ContinuousOn (fun p => ∑ i, uDemand (u i) p (w i p)) (posOrthant L) :=
    continuousOn_finsetSum _ fun i _ => continuousOn_uDemand_comp (hc i) (hsq i) (hwc i) (hw0 i)
  exact hsum.sub hcc

/-- **Proposition 17.B.2(ii)**, general form: homogeneity of degree zero. -/
theorem wealthExcessDemand_homogeneous {u : ι → (Fin L → ℝ) → ℝ} {w : ι → (Fin L → ℝ) → ℝ}
    {c : (Fin L → ℝ) → Fin L → ℝ}
    (hwh : ∀ i, ∀ p ∈ posOrthant L, ∀ α : ℝ, 0 < α → w i (α • p) = α * w i p)
    (hch : ∀ p ∈ posOrthant L, ∀ α : ℝ, 0 < α → c (α • p) = c p) :
    EDHomogeneous (wealthExcessDemand u w c) := by
  intro p hp α hα
  simp only [wealthExcessDemand, hch p hp α hα, hwh _ p hp α hα, uDemand_smul _ _ _ hα]

/-- **Proposition 17.B.2(iii)**, general form: Walras' law, for locally nonsatiated consumers
whose wealths add up to the value `p·c(p)` of the supply. -/
theorem wealthExcessDemand_walras {u : ι → (Fin L → ℝ) → ℝ} {w : ι → (Fin L → ℝ) → ℝ}
    {c : (Fin L → ℝ) → Fin L → ℝ} (hc : ∀ i, ContinuousOn (u i) (nonnegOrthant L))
    (hlns : ∀ i, UtilityLNS (u i)) (hw0 : ∀ i, ∀ p ∈ posOrthant L, 0 ≤ w i p)
    (hsum : ∀ p ∈ posOrthant L, ∑ i, w i p = p ⬝ᵥ c p) :
    EDWalrasLaw (wealthExcessDemand u w c) := by
  intro p hp
  have hx : ∀ i, p ⬝ᵥ uDemand (u i) p (w i p) = w i p := fun i =>
    (hlns i).budget_eq (uDemand_mem (proposition_3_D_1 (hc i) hp (hw0 i p hp)))
  rw [wealthExcessDemand, dotProduct_sub, dotProduct_sum]
  simp only [hx]
  rw [hsum p hp, sub_self]

/-- **Proposition 17.B.2(iv)**, general form: excess supply is bounded when the supply is. -/
theorem wealthExcessDemand_boundedBelow (u : ι → (Fin L → ℝ) → ℝ) (w : ι → (Fin L → ℝ) → ℝ)
    {c : (Fin L → ℝ) → Fin L → ℝ} (hcb : ∃ b : Fin L → ℝ, ∀ p ∈ posOrthant L, c p ≤ b) :
    EDBoundedBelow (wealthExcessDemand u w c) := by
  obtain ⟨b, hb⟩ := hcb
  refine ⟨∑ l, |b l| + 1, by positivity, fun p hp l => ?_⟩
  rw [wealthExcessDemand_apply]
  have h1 : 0 ≤ ∑ i, uDemand (u i) p (w i p) l :=
    Finset.sum_nonneg fun i _ => uDemand_nonneg _ _ _ l
  have h2 : b l ≤ ∑ l, |b l| :=
    (le_abs_self _).trans (Finset.single_le_sum (fun l _ => abs_nonneg (b l)) (Finset.mem_univ l))
  linarith [hb p hp l]

/-- **Proposition 17.B.2(v)**, general form (Exercise 17.B.2): the boundary condition, for
strongly monotone consumers, a supply bounded above, and wealths such that along every sequence
`pⁿ ≫ 0` converging to a nonzero `p`, some consumer's wealth has a positive limit point. -/
theorem wealthExcessDemand_boundary {u : ι → (Fin L → ℝ) → ℝ} {w : ι → (Fin L → ℝ) → ℝ}
    {c : (Fin L → ℝ) → Fin L → ℝ} (hc : ∀ i, ContinuousOn (u i) (nonnegOrthant L))
    (hm : ∀ i, UtilityStronglyMonotone (u i)) (hw0 : ∀ i, ∀ p ∈ posOrthant L, 0 ≤ w i p)
    (hcb : ∃ b : Fin L → ℝ, ∀ p ∈ posOrthant L, c p ≤ b)
    (hbd : ∀ (ps : ℕ → Fin L → ℝ) (p : Fin L → ℝ), (∀ n, ps n ∈ posOrthant L) →
      Tendsto ps atTop (𝓝 p) → p ≠ 0 → ∃ i, ∃ wl : ℝ, 0 < wl ∧ ∃ φ : ℕ → ℕ,
        StrictMono φ ∧ Tendsto (fun k => w i (ps (φ k))) atTop (𝓝 wl)) :
    EDBoundary (wealthExcessDemand u w c) := by
  intro ps p hps hlim hp0 hl M
  obtain ⟨l0, hl0⟩ := hl
  obtain ⟨b, hb⟩ := hcb
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  have hcon' : ∃ᶠ n in atTop, ∀ l, wealthExcessDemand u w c (ps n) l ≤ M :=
    hcon.mono fun n hn => by
      push Not at hn
      exact hn
  obtain ⟨φ, hφ, hφM⟩ := Filter.extraction_of_frequently_atTop hcon'
  obtain ⟨i, wl, hwl, ψ, hψ, hws⟩ :=
    hbd (fun n => ps (φ n)) p (fun n => hps _) (hlim.comp hφ.tendsto_atTop) hp0
  refine demand_bounded_near_boundary_false (hc i) (hm i) (ps := fun k => ps (φ (ψ k)))
    (fun k => hps _) ((hlim.comp hφ.tendsto_atTop).comp hψ.tendsto_atTop) hl0 hwl hws
    (xs := fun k => uDemand (u i) (ps (φ (ψ k))) (w i (ps (φ (ψ k)))))
    (fun k => uDemand_mem (proposition_3_D_1 (hc i) (hps _) (hw0 i _ (hps _))))
    (B := M + ∑ l, |b l|) (fun k l => ?_)
  have hz := hφM (ψ k) l
  rw [wealthExcessDemand_apply] at hz
  have hsingle : uDemand (u i) (ps (φ (ψ k))) (w i (ps (φ (ψ k)))) l ≤
      ∑ j, uDemand (u j) (ps (φ (ψ k))) (w j (ps (φ (ψ k)))) l :=
    Finset.single_le_sum (f := fun j => uDemand (u j) (ps (φ (ψ k))) (w j (ps (φ (ψ k)))) l)
      (fun j _ => uDemand_nonneg _ _ _ l) (Finset.mem_univ i)
  have hbl := hb _ (hps (φ (ψ k))) l
  have habs : b l ≤ ∑ l, |b l| :=
    (le_abs_self _).trans (Finset.single_le_sum (fun l _ => abs_nonneg (b l)) (Finset.mem_univ l))
  linarith

/-- **Proposition 17.B.2**, general form: under the hypotheses above, `z(p) = ∑ᵢ xᵢ(p, wᵢ(p)) -
c(p)` satisfies (i)-(v). -/
theorem isStandard_wealthExcessDemand {u : ι → (Fin L → ℝ) → ℝ} {w : ι → (Fin L → ℝ) → ℝ}
    {c : (Fin L → ℝ) → Fin L → ℝ} (hL : 0 < L) (hu : ∀ i, StandardUtility (u i))
    (hw0 : ∀ i, ∀ p ∈ posOrthant L, 0 ≤ w i p) (hwc : ∀ i, ContinuousOn (w i) (posOrthant L))
    (hcc : ContinuousOn c (posOrthant L))
    (hwh : ∀ i, ∀ p ∈ posOrthant L, ∀ α : ℝ, 0 < α → w i (α • p) = α * w i p)
    (hch : ∀ p ∈ posOrthant L, ∀ α : ℝ, 0 < α → c (α • p) = c p)
    (hsum : ∀ p ∈ posOrthant L, ∑ i, w i p = p ⬝ᵥ c p)
    (hcb : ∃ b : Fin L → ℝ, ∀ p ∈ posOrthant L, c p ≤ b)
    (hbd : ∀ (ps : ℕ → Fin L → ℝ) (p : Fin L → ℝ), (∀ n, ps n ∈ posOrthant L) →
      Tendsto ps atTop (𝓝 p) → p ≠ 0 → ∃ i, ∃ wl : ℝ, 0 < wl ∧ ∃ φ : ℕ → ℕ,
        StrictMono φ ∧ Tendsto (fun k => w i (ps (φ k))) atTop (𝓝 wl)) :
    IsStandardExcessDemand (wealthExcessDemand u w c) where
  continuous := wealthExcessDemand_continuous (fun i => (hu i).1) (fun i => (hu i).2.1) hwc hw0 hcc
  homogeneous := wealthExcessDemand_homogeneous hwh hch
  walras := wealthExcessDemand_walras (fun i => (hu i).1) (fun i => (hu i).2.2.lns hL) hw0 hsum
  boundedBelow := wealthExcessDemand_boundedBelow u w hcb
  boundary := wealthExcessDemand_boundary (fun i => (hu i).1) (fun i => (hu i).2.2) hw0 hcb hbd

/-! ### Proposition 17.B.2 for a pure exchange economy -/

/-- A limit of strictly positive price vectors is nonnegative. -/
theorem nonneg_of_tendsto_pos {ps : ℕ → Fin L → ℝ} {p : Fin L → ℝ}
    (hps : ∀ n, ps n ∈ posOrthant L) (hlim : Tendsto ps atTop (𝓝 p)) (l : Fin L) :
    0 ≤ p l :=
  ge_of_tendsto' (((continuous_apply l).tendsto p).comp hlim) fun n => (hps n l).le

/-- A nonzero, nonnegative price vector gives positive value to a strictly positive bundle. -/
theorem dotProduct_pos_of_ne_zero {p x : Fin L → ℝ} (hp : ∀ l, 0 ≤ p l) (hp0 : p ≠ 0)
    (hx : ∀ l, 0 < x l) : 0 < p ⬝ᵥ x := by
  obtain ⟨l, hl⟩ := Function.ne_iff.1 hp0
  have hpl : 0 < p l := lt_of_le_of_ne (hp l) (Ne.symm hl)
  have hsingle : p l * x l ≤ p ⬝ᵥ x :=
    Finset.single_le_sum (fun k _ => mul_nonneg (hp k) (hx k).le) (Finset.mem_univ l)
  exact lt_of_lt_of_le (mul_pos hpl (hx l)) hsingle

/-- In a pure exchange economy, `z(p)` agrees on `ℝ^L_{++}` with the general excess demand for
wealths `wᵢ(p) = p·ωᵢ` and supply `c(p) = ∑ᵢ ωᵢ`. -/
theorem excessDemand_eqOn {E : ExchangeEconomy ι L} (hX : ∀ i, E.X i = nonnegOrthant L)
    (hc : ∀ i, ContinuousOn (E.u i) (nonnegOrthant L))
    (hsq : ∀ i, StrictlyQuasiconcaveOn (nonnegOrthant L) (E.u i))
    (hω : ∀ i, E.ω i ∈ nonnegOrthant L) :
    Set.EqOn (wealthExcessDemand E.u (fun i p => p ⬝ᵥ E.ω i) (fun _ => E.totalEndowment))
      (excessDemand E) (posOrthant L) := by
  intro p hp
  rw [excessDemand_eq, wealthExcessDemand]
  congr 1
  refine Finset.sum_congr rfl fun i _ => (demandFn_eq E ?_).symm
  have hw : 0 ≤ p ⬝ᵥ E.ω i := Finset.sum_nonneg fun l _ => mul_nonneg (hp l).le (hω i l)
  have h := walrasianDemand_eq_singleton (hc i) (hsq i) hp hw
  simp only [walrasianDemand] at h
  simp only [ExchangeEconomy.demand, hX i]
  exact h

/-- **Footnote 3** (MWG, p. 582). Properties (i)-(iv) of Proposition 17.B.2 hold when
preferences are only locally nonsatiated (continuous and strictly convex, on `ℝ^L₊`, with
`ωᵢ ∈ ℝ^L₊`). -/
theorem footnote_17_3 {E : ExchangeEconomy ι L} (hX : ∀ i, E.X i = nonnegOrthant L)
    (hc : ∀ i, ContinuousOn (E.u i) (nonnegOrthant L))
    (hsq : ∀ i, StrictlyQuasiconcaveOn (nonnegOrthant L) (E.u i))
    (hlns : ∀ i, UtilityLNS (E.u i)) (hω : ∀ i, E.ω i ∈ nonnegOrthant L) :
    EDContinuous (excessDemand E) ∧ EDHomogeneous (excessDemand E) ∧
      EDWalrasLaw (excessDemand E) ∧ EDBoundedBelow (excessDemand E) := by
  have heq := excessDemand_eqOn hX hc hsq hω
  have hw0 : ∀ i, ∀ p ∈ posOrthant L, 0 ≤ p ⬝ᵥ E.ω i := fun i p hp =>
    Finset.sum_nonneg fun l _ => mul_nonneg (hp l).le (hω i l)
  have hwc : ∀ i, ContinuousOn (fun p : Fin L → ℝ => p ⬝ᵥ E.ω i) (posOrthant L) := fun i => by
    simp only [dotProduct]
    fun_prop
  have h1 := wealthExcessDemand_continuous hc hsq hwc hw0 (c := fun _ => E.totalEndowment)
    continuousOn_const
  have h2 := wealthExcessDemand_homogeneous (u := E.u) (w := fun i p => p ⬝ᵥ E.ω i)
    (c := fun _ => E.totalEndowment)
    (fun i p _ α _ => by simp [smul_dotProduct]) (fun _ _ _ _ => rfl)
  have h3 := wealthExcessDemand_walras (c := fun _ => E.totalEndowment) hc hlns hw0
    (fun p _ => by simp [ExchangeEconomy.totalEndowment, dotProduct_sum])
  have h4 := wealthExcessDemand_boundedBelow E.u (fun i p => p ⬝ᵥ E.ω i)
    (c := fun _ => E.totalEndowment) ⟨E.totalEndowment, fun _ _ => le_rfl⟩
  refine ⟨h1.congr fun p hp => (heq hp).symm, fun p hp α hα => ?_, fun p hp => ?_, ?_⟩
  · rw [← heq hp, ← heq (smul_mem_posOrthant hp hα), h2 p hp α hα]
  · rw [← heq hp]
    exact h3 p hp
  · obtain ⟨s, hs, hb⟩ := h4
    exact ⟨s, hs, fun p hp l => by rw [← heq hp]; exact hb p hp l⟩

/-- In a pure exchange economy with `∑ᵢ ωᵢ ≫ 0` and `ωᵢ ∈ ℝ^L₊`, along every sequence
`pⁿ ≫ 0` converging to a nonzero `p`, some consumer's wealth `pⁿ·ωᵢ` converges to a positive
limit (`p·∑ᵢ ωᵢ > 0`). -/
theorem exchange_boundary_wealth {E : ExchangeEconomy ι L}
    (hpos : ∀ l, 0 < E.totalEndowment l) (ps : ℕ → Fin L → ℝ) (p : Fin L → ℝ)
    (hps : ∀ n, ps n ∈ posOrthant L) (hlim : Tendsto ps atTop (𝓝 p)) (hp0 : p ≠ 0) :
    ∃ i, ∃ wl : ℝ, 0 < wl ∧ ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (fun k => ps (φ k) ⬝ᵥ E.ω i) atTop (𝓝 wl) := by
  have hpT := dotProduct_pos_of_ne_zero (nonneg_of_tendsto_pos hps hlim) hp0 hpos
  rw [ExchangeEconomy.totalEndowment, dotProduct_sum] at hpT
  obtain ⟨i, hi⟩ : ∃ i, 0 < p ⬝ᵥ E.ω i := by
    by_contra h
    push Not at h
    exact absurd hpT (not_lt.2 (Finset.sum_nonpos fun i _ => h i))
  exact ⟨i, _, hi, id, strictMono_id, appendixA_tendsto_dotProduct_seq hlim tendsto_const_nhds⟩

/-- **Proposition 17.B.2** (MWG, pp. 581-582). In a pure exchange economy with `Xᵢ = ℝ^L₊`,
continuous, strictly convex and strongly monotone preferences, endowments `ωᵢ ∈ ℝ^L₊` and
`∑ᵢ ωᵢ ≫ 0`, the aggregate excess demand function `z(p)`, `p ≫ 0`, satisfies (i) continuity,
(ii) homogeneity of degree zero, (iii) Walras' law, (iv) a bound `z_ℓ(p) > -s` and (v) the
boundary condition. -/
theorem proposition_17_B_2 {E : ExchangeEconomy ι L} (hX : ∀ i, E.X i = nonnegOrthant L)
    (hu : ∀ i, StandardUtility (E.u i)) (hω : ∀ i, E.ω i ∈ nonnegOrthant L)
    (hpos : ∀ l, 0 < E.totalEndowment l) : IsStandardExcessDemand (excessDemand E) := by
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · exact isStandardExcessDemand_of_fin_zero _
  refine IsStandardExcessDemand.congr ?_
    (excessDemand_eqOn hX (fun i => (hu i).1) (fun i => (hu i).2.1) hω)
  refine isStandard_wealthExcessDemand hL hu
    (fun i p hp => Finset.sum_nonneg fun l _ => mul_nonneg (hp l).le (hω i l))
    (fun i => by simp only [dotProduct]; fun_prop) continuousOn_const
    (fun i p _ α _ => by simp [smul_dotProduct]) (fun _ _ _ _ => rfl)
    (fun p _ => by simp [ExchangeEconomy.totalEndowment, dotProduct_sum])
    ⟨E.totalEndowment, fun _ _ => le_rfl⟩ (exchange_boundary_wealth hpos)

/-- **Exercise 17.B.2** (MWG, p. 642). Property (v) of Proposition 17.B.2: under its
hypotheses, if `pⁿ ≫ 0`, `pⁿ → p ≠ 0` and `p_ℓ = 0` for some `ℓ`, then
`Max {z₁(pⁿ), ..., z_L(pⁿ)} → ∞`. -/
theorem exercise_17_B_2 {E : ExchangeEconomy ι L} (hX : ∀ i, E.X i = nonnegOrthant L)
    (hu : ∀ i, StandardUtility (E.u i)) (hω : ∀ i, E.ω i ∈ nonnegOrthant L)
    (hpos : ∀ l, 0 < E.totalEndowment l) : EDBoundary (excessDemand E) :=
  (proposition_17_B_2 hX hu hω hpos).boundary

/-! ### A concrete instance: `u(x) = ∑ₗ √xₗ` -/

/-- The utility `u(x) = ∑ₗ √xₗ` on `ℝ^L₊`. -/
noncomputable def sqrtUtility (L : ℕ) (x : Fin L → ℝ) : ℝ := ∑ l, Real.sqrt (x l)

/-- `∑ₗ √xₗ` is strictly quasiconcave on `ℝ^L₊` (indeed strictly concave). -/
theorem strictlyQuasiconcaveOn_sqrtUtility (L : ℕ) :
    StrictlyQuasiconcaveOn (nonnegOrthant L) (sqrtUtility L) := by
  refine ⟨convex_nonnegOrthant L, fun x hx x' hx' hne α hα hα1 t ht ht' => ?_⟩
  obtain ⟨l0, hl0⟩ := Function.ne_iff.1 hne
  have hconc : ∀ l, α * Real.sqrt (x l) + (1 - α) * Real.sqrt (x' l) ≤
      Real.sqrt ((α • x + (1 - α) • x') l) := fun l => by
    have : α • Real.sqrt (x l) + (1 - α) • Real.sqrt (x' l) ≤
        Real.sqrt (α • x l + (1 - α) • x' l) :=
      Real.strictConcaveOn_sqrt.concaveOn.2 (hx l : x l ∈ Set.Ici (0 : ℝ))
        (hx' l : x' l ∈ Set.Ici (0 : ℝ)) hα.le (by linarith) (by ring)
    simpa [smul_eq_mul] using this
  have hstrict : α * Real.sqrt (x l0) + (1 - α) * Real.sqrt (x' l0) <
      Real.sqrt ((α • x + (1 - α) • x') l0) := by
    have : α • Real.sqrt (x l0) + (1 - α) • Real.sqrt (x' l0) <
        Real.sqrt (α • x l0 + (1 - α) • x' l0) :=
      Real.strictConcaveOn_sqrt.2 (hx l0 : x l0 ∈ Set.Ici (0 : ℝ))
        (hx' l0 : x' l0 ∈ Set.Ici (0 : ℝ)) hl0 hα (by linarith) (by ring)
    simpa [smul_eq_mul] using this
  have hsum := Finset.sum_lt_sum (fun l _ => hconc l) ⟨l0, Finset.mem_univ _, hstrict⟩
  have hsplit : ∑ l, (α * Real.sqrt (x l) + (1 - α) * Real.sqrt (x' l)) =
      α * sqrtUtility L x + (1 - α) * sqrtUtility L x' := by
    simp [sqrtUtility, Finset.sum_add_distrib, Finset.mul_sum]
  have hmix : t ≤ α * sqrtUtility L x + (1 - α) * sqrtUtility L x' := by
    have h1 := mul_le_mul_of_nonneg_left ht hα.le
    have h2 := mul_le_mul_of_nonneg_left ht' (by linarith : (0 : ℝ) ≤ 1 - α)
    linarith
  unfold sqrtUtility at hsplit hmix ⊢
  linarith

/-- `∑ₗ √xₗ` is strongly monotone on `ℝ^L₊`. -/
theorem sqrtUtility_stronglyMonotone (L : ℕ) : UtilityStronglyMonotone (sqrtUtility L) := by
  intro x hx y _ hxy hne
  obtain ⟨l0, hl0⟩ := Function.ne_iff.1 hne
  have hlt : sqrtUtility L x < sqrtUtility L y :=
    Finset.sum_lt_sum (fun l _ => Real.sqrt_le_sqrt (hxy l))
      ⟨l0, Finset.mem_univ _, Real.sqrt_lt_sqrt (hx l0) (lt_of_le_of_ne (hxy l0) (Ne.symm hl0))⟩
  exact ⟨hlt.le, not_le.2 hlt⟩

/-- `u(x) = ∑ₗ √xₗ` satisfies the chapter's standing assumptions. -/
theorem standardUtility_sqrtUtility (L : ℕ) : StandardUtility (sqrtUtility L) :=
  ⟨(continuous_finsetSum _ fun l _ => Real.continuous_sqrt.comp (continuous_apply l)).continuousOn,
    strictlyQuasiconcaveOn_sqrtUtility L, sqrtUtility_stronglyMonotone L⟩

/-- A two-consumer, two-good exchange economy with `uᵢ(x) = √x₁ + √x₂` and `ωᵢ = (1, 1)`. -/
noncomputable def sqrtEconomy : ExchangeEconomy (Fin 2) 2 :=
  ExchangeEconomy.ofOrthant (fun _ => sqrtUtility 2) (fun _ _ => 1)

/-- **Proposition 17.B.2**, instance: the excess demand of `sqrtEconomy` satisfies (i)-(v). -/
theorem sqrtEconomy_isStandard : IsStandardExcessDemand (excessDemand sqrtEconomy) :=
  proposition_17_B_2 (fun _ => rfl) (fun _ => standardUtility_sqrtUtility 2)
    (fun _ _ => zero_le_one) fun l => by
      simp [ExchangeEconomy.totalEndowment, sqrtEconomy, ExchangeEconomy.ofOrthant]

/-! ### Correction: endowments must lie in `ℝ^L₊` -/

/-- An exchange economy with `∑ᵢ ωᵢ = (2, 1) ≫ 0` but `ω₁ = (2, -1) ∉ ℝ²₊`. -/
noncomputable def negEndowEconomy : ExchangeEconomy (Fin 2) 2 :=
  ExchangeEconomy.ofOrthant (fun _ => sqrtUtility 2) ![![2, -1], ![0, 2]]

/-- **Correction to Proposition 17.B.2** (MWG, p. 581). `negEndowEconomy` has `∑ᵢ ωᵢ ≫ 0` and
standard preferences, yet at `p = (1, 3) ≫ 0` consumer 1's wealth `p·ω₁ = -1` is negative, his
budget set is empty, and his demand (hence `z(p)`) is undefined. -/
theorem negEndowEconomy_demand_empty :
    (∀ l, 0 < negEndowEconomy.totalEndowment l) ∧ (![1, 3] : Fin 2 → ℝ) ∈ posOrthant 2 ∧
      negEndowEconomy.demand 0 ![1, 3] = ∅ := by
  refine ⟨fun l => ?_, fun l => ?_, Set.eq_empty_iff_forall_notMem.2 fun x hx => ?_⟩
  · fin_cases l <;>
      simp [ExchangeEconomy.totalEndowment, negEndowEconomy, ExchangeEconomy.ofOrthant]
  · fin_cases l <;> simp
  · obtain ⟨⟨hx0, hb⟩, -⟩ := hx
    have h0 := hx0 0
    have h1 := hx0 1
    simp [negEndowEconomy, ExchangeEconomy.ofOrthant, dotProduct, Fin.sum_univ_two] at hb h0 h1
    linarith

end MWG.PositiveEquilibriumTheory
