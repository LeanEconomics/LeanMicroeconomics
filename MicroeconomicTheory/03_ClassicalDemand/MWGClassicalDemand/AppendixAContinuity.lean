/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGClassicalDemand.UMPBasic
import MWGClassicalDemand.AppendixMH
import MWGConsumerChoice.Commodities

/-!
# Appendix A to Chapter 3: continuity of Walrasian demand

MWG, Appendix A to Chapter 3, pp. 92-94, and Exercise 3.AA.1, p. 104.

* **Definition 3.AA.1**: upper hemicontinuity of a demand correspondence at `(p̄, w̄)`
  (`DemandUHCAt`), with bridges to Kreps's `SequentialUpper` and to the closed graph and upper
  hemicontinuity of Section M.H (`demandUHC_iff_hasClosedGraph`, `demand_uhc_mwg`).
* Footnote 32: the Walrasian budget (hence demand) correspondence is locally bounded at
  `(p, w) ≫ 0` (`footnote_3_AA_32`).
* "If `x(p, w)` is single-valued, upper hemicontinuity is continuity" (`demandUHC_iff_continuousOn`,
  via Kreps's `continuous_of_singleton_correspondence`).
* The small-type generalisation (p. 94): on a closed consumption set, demand is upper
  hemicontinuous at every `(p̄, w̄)` that passes the locally cheaper consumption test
  (`demand_uhc_of_locallyCheaper`).
* **Proposition 3.AA.1**: for continuous `u` on `ℝ^L_+`, `x(p, w)` is upper hemicontinuous at all
  `(p, w) ≫ 0`, and continuous if it is a function (`proposition_3_AA_1`,
  `proposition_3_AA_1_continuous`). Local nonsatiation, assumed in the book, is not used.
* **Figure 3.AA.3** (good 2 indivisible) and **Exercise 3.AA.1**: the locally cheaper test fails
  and demand is not upper hemicontinuous (not continuous).
-/

namespace MWG.ClassicalDemand

open MWG.ConsumerChoice Filter Topology

variable {L : ℕ}

/-- **Definition 3.AA.1** (MWG, p. 93). The demand correspondence `x(p, w)` is upper
hemicontinuous at `(p̄, w̄)` if whenever `(pⁿ, wⁿ) → (p̄, w̄)` (price-wealth pairs `≫ 0`),
`xⁿ ∈ x(pⁿ, wⁿ)` for all `n` and `x = lim xⁿ`, then `x ∈ x(p̄, w̄)`. -/
def DemandUHCAt (x : DemandCorrespondence L) (pbar : Fin L → ℝ) (wbar : ℝ) : Prop :=
  ∀ (ps : ℕ → Fin L → ℝ) (ws : ℕ → ℝ) (xs : ℕ → Fin L → ℝ) (xl : Fin L → ℝ),
    (∀ n, PWDomain (ps n) (ws n)) → Tendsto ps atTop (𝓝 pbar) → Tendsto ws atTop (𝓝 wbar) →
    (∀ n, xs n ∈ x (ps n) (ws n)) → Tendsto xs atTop (𝓝 xl) → xl ∈ x pbar wbar

/-- Upper hemicontinuity at every `(p, w) ≫ 0` is the closed-graph condition (Definition M.H.2)
of `(p, w) ↦ x(p, w)` on the price-wealth domain. -/
theorem demandUHC_iff_hasClosedGraph (x : DemandCorrespondence L) :
    (∀ p w, PWDomain p w → DemandUHCAt x p w) ↔
      HasClosedGraph (pwDomainSet L) (fun q => x q.1 q.2) := by
  constructor
  · intro h qs xs q xl hqs hq hxs hql hxl
    exact h q.1 q.2 hq (fun n => (qs n).1) (fun n => (qs n).2) xs xl hqs
      ((continuous_fst.tendsto q).comp hql) ((continuous_snd.tendsto q).comp hql) hxs hxl
  · intro h p w hd ps ws xs xl hds hp hw hxs hxl
    exact h (fun n => (ps n, ws n)) xs (p, w) xl hds hd hxs (hp.prodMk_nhds hw) hxl

/-- Bridge to Kreps I, Appendix 4. Upper hemicontinuity at every `(p, w) ≫ 0` is Kreps's
`SequentialUpper` for the demand correspondence on the price-wealth domain. -/
theorem demandUHC_iff_sequentialUpper (x : DemandCorrespondence L) :
    (∀ p w, PWDomain p w → DemandUHCAt x p w) ↔
      Kreps.ConsumerDemand.SequentialUpper (fun q : pwDomainSet L => x q.1.1 q.1.2) := by
  rw [demandUHC_iff_hasClosedGraph, hasClosedGraph_iff_sequentialUpper]

/-- **Footnote 32** (MWG, p. 93). The Walrasian budget correspondence is locally bounded on
`(p, w) ≫ 0`: its image of every compact set of price-wealth pairs `≫ 0` is bounded. -/
theorem footnote_3_AA_32 {B : Set ((Fin L → ℝ) × ℝ)} (hBA : B ⊆ pwDomainSet L)
    (hB : IsCompact B) : Bornology.IsBounded (⋃ q ∈ B, budgetSet q.1 q.2) := by
  have hC : ∀ l : Fin L, ∃ C : ℝ, ∀ q ∈ B, q.2 / q.1 l ≤ C := by
    intro l
    have hcont : ContinuousOn (fun q : (Fin L → ℝ) × ℝ => q.2 / q.1 l) B := by
      apply ContinuousOn.div continuous_snd.continuousOn
        ((continuous_apply l).comp continuous_fst).continuousOn
      intro q hq
      exact ((hBA hq).1 l).ne'
    obtain ⟨C, hC⟩ := (hB.bddAbove_image hcont)
    exact ⟨C, fun q hq => hC ⟨q, hq, rfl⟩⟩
  choose C hC using hC
  refine (Metric.isBounded_Icc (0 : Fin L → ℝ) C).subset ?_
  intro y hy
  simp only [Set.mem_iUnion] at hy
  obtain ⟨q, hq, hyq⟩ := hy
  exact ⟨fun l => hyq.1 l, fun l => (budgetSet_coord_le (hBA hq).1 hyq l).trans (hC l q hq)⟩

/-- **Definition 3.AA.1 and Section M.H** (MWG, pp. 93, 950). A demand correspondence with
values in the budget sets that is upper hemicontinuous at every `(p, w) ≫ 0` is upper
hemicontinuous on the price-wealth domain in the sense of Definition M.H.3 (closed graph and
bounded images of compact sets, footnote 32). -/
theorem demand_uhc_mwg {x : DemandCorrespondence L}
    (hfeas : ∀ p w, PWDomain p w → x p w ⊆ budgetSet p w)
    (h : ∀ p w, PWDomain p w → DemandUHCAt x p w) :
    UpperHemicontinuousMWG (pwDomainSet L) (fun q => x q.1 q.2) :=
  ⟨(demandUHC_iff_hasClosedGraph x).mp h, fun _ hBA hB =>
    (footnote_3_AA_32 hBA hB).subset (Set.iUnion₂_mono fun q hq => hfeas q.1 q.2 (hBA hq))⟩

/-- The demand correspondence of a utility function on `X` has values in the budget sets. -/
theorem appendixA_walrasianDemand_subset_budgetSet (u : (Fin L → ℝ) → ℝ) (p : Fin L → ℝ) (w : ℝ) :
    walrasianDemand u p w ⊆ budgetSet p w := fun _ hx => hx.1

/-- **Section 3.AA** (MWG, p. 93): "if `x(p, w)` is single-valued at all `(p, w) ≫ 0`, upper
hemicontinuity is equivalent to the usual continuity property for functions". For a demand
function with values in the budget sets, upper hemicontinuity of `{x(p, w)}` at every
`(p, w) ≫ 0` is continuity on the price-wealth domain. The local bound of footnote 32 is used
through Kreps's `continuous_of_singleton_correspondence`. -/
theorem demandUHC_iff_continuousOn {s : DemandFunction L}
    (hfeas : ∀ p w, PWDomain p w → s p w ∈ budgetSet p w) :
    (∀ p w, PWDomain p w → DemandUHCAt (toCorrespondence s) p w) ↔
      ContinuousOn (fun q : (Fin L → ℝ) × ℝ => s q.1 q.2) (pwDomainSet L) := by
  constructor
  · intro h
    rw [continuousOn_iff_continuous_domRestrict]
    have hu := (demandUHC_iff_sequentialUpper (toCorrespondence s)).mp h
    apply Kreps.ConsumerDemand.continuous_of_singleton_correspondence hu
    intro q
    refine ⟨Set.Icc 0 (fun l => 4 * q.1.2 / q.1.1 l), isCompact_Icc, ?_⟩
    have hq : PWDomain q.1.1 q.1.2 := q.2
    have hcoord : ∀ l, ∀ᶠ q' : pwDomainSet L in 𝓝 q, q.1.1 l / 2 < (q' : (Fin L → ℝ) × ℝ).1 l := by
      intro l
      have ht : Tendsto (fun q' : pwDomainSet L => (q' : (Fin L → ℝ) × ℝ).1 l) (𝓝 q)
          (𝓝 (q.1.1 l)) :=
        (((continuous_apply l).comp continuous_fst).comp continuous_subtype_val).tendsto q
      exact ht.eventually (lt_mem_nhds (by linarith [hq.1 l]))
    have hwev : ∀ᶠ q' : pwDomainSet L in 𝓝 q, (q' : (Fin L → ℝ) × ℝ).2 < 2 * q.1.2 := by
      have ht : Tendsto (fun q' : pwDomainSet L => (q' : (Fin L → ℝ) × ℝ).2) (𝓝 q)
          (𝓝 q.1.2) := (continuous_snd.comp continuous_subtype_val).tendsto q
      exact ht.eventually (gt_mem_nhds (by linarith [hq.2]))
    filter_upwards [eventually_all.mpr hcoord, hwev] with q' hc hw
    rintro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    have hb := hfeas _ _ q'.2
    refine ⟨fun l => hb.1 l, fun l => ?_⟩
    have h1 := budgetSet_coord_le q'.2.1 hb l
    have hpl : 0 < q.1.1 l := hq.1 l
    have hpl' : 0 < (q' : (Fin L → ℝ) × ℝ).1 l := q'.2.1 l
    calc s (q' : (Fin L → ℝ) × ℝ).1 (q' : (Fin L → ℝ) × ℝ).2 l
        ≤ (q' : (Fin L → ℝ) × ℝ).2 / (q' : (Fin L → ℝ) × ℝ).1 l := h1
      _ ≤ 2 * q.1.2 / (q.1.1 l / 2) := by
          apply div_le_div₀ (by linarith [hq.2]) hw.le (by linarith) (hc l).le
      _ = 4 * q.1.2 / q.1.1 l := by field_simp; ring
  · intro hc p w hd ps ws xs xl hds hp hw hxs hxl
    have hxs' : xs = fun n => s (ps n) (ws n) := funext fun n => hxs n
    have hlim : Tendsto (fun n => s (ps n) (ws n)) atTop (𝓝 (s p w)) := by
      have := (hc (p, w) hd).tendsto.comp (tendsto_nhdsWithin_iff.mpr
        ⟨hp.prodMk_nhds hw, Eventually.of_forall hds⟩)
      exact this
    rw [hxs'] at hxl
    exact tendsto_nhds_unique hxl hlim

/-- **Section 3.AA, small type** (MWG, p. 94). The locally cheaper consumption test at `(p̄, w̄)`
on the consumption set `X`: for every affordable `x ∈ X` (`p̄·x ≤ w̄`) there are bundles
`y ∈ X` arbitrarily close to `x` (Euclidean distance) costing less than `w̄`. -/
def LocallyCheaperAt (X : Set (Fin L → ℝ)) (pbar : Fin L → ℝ) (wbar : ℝ) : Prop :=
  ∀ x ∈ X, pbar ⬝ᵥ x ≤ wbar → ∀ ε : ℝ, 0 < ε → ∃ y ∈ X, euclidDist y x < ε ∧ pbar ⬝ᵥ y < wbar

/-- Expenditure is jointly continuous along sequences of prices and bundles. -/
theorem appendixA_tendsto_dotProduct_seq {ps xs : ℕ → Fin L → ℝ} {p x : Fin L → ℝ}
    (hp : Tendsto ps atTop (𝓝 p)) (hx : Tendsto xs atTop (𝓝 x)) :
    Tendsto (fun n => ps n ⬝ᵥ xs n) atTop (𝓝 (p ⬝ᵥ x)) := by
  simp only [dotProduct]
  exact tendsto_finsetSum _ fun l _ =>
    (((continuous_apply l).tendsto p).comp hp).mul (((continuous_apply l).tendsto x).comp hx)

/-- **Section 3.AA, small type** (MWG, p. 94). On a closed consumption set `X`, with `u`
continuous on `X`, the demand correspondence is upper hemicontinuous at every `(p̄, w̄)` that
passes the locally cheaper consumption test (the proof of Proposition 3.AA.1). -/
theorem demand_uhc_of_locallyCheaper {X : Set (Fin L → ℝ)} (hX : IsClosed X)
    {u : (Fin L → ℝ) → ℝ} (hu : ContinuousOn u X) {pbar : Fin L → ℝ} {wbar : ℝ}
    (hlc : LocallyCheaperAt X pbar wbar) :
    DemandUHCAt (fun p w => walrasianDemandOn X u p w) pbar wbar := by
  intro ps ws xs xl _ hp hw hxs hxl
  have hxX : xl ∈ X := hX.mem_of_tendsto hxl (Eventually.of_forall fun n => (hxs n).1.1)
  have hbud : pbar ⬝ᵥ xl ≤ wbar :=
    le_of_tendsto_of_tendsto (appendixA_tendsto_dotProduct_seq hp hxl) hw
    (Eventually.of_forall fun n => (hxs n).1.2)
  refine ⟨⟨hxX, hbud⟩, fun z hz => ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨δ, hδ, hδu⟩ := Metric.continuousWithinAt_iff.mp (hu z hz.1) (u z - u xl)
    (by linarith)
  obtain ⟨y, hyX, hyd, hyc⟩ := hlc z hz.1 hz.2 δ hδ
  have hyu : u xl < u y := by
    have := hδu hyX ((dist_le_euclidDist y z).trans_lt hyd)
    rw [Real.dist_eq] at this
    linarith [neg_abs_le (u y - u z)]
  have hev : ∀ᶠ n in atTop, ps n ⬝ᵥ y < ws n := by
    have ht : Tendsto (fun n => ps n ⬝ᵥ y - ws n) atTop (𝓝 (pbar ⬝ᵥ y - wbar)) :=
      (appendixA_tendsto_dotProduct_seq hp tendsto_const_nhds).sub hw
    filter_upwards [ht.eventually (gt_mem_nhds (show pbar ⬝ᵥ y - wbar < 0 by linarith))] with n hn
    linarith
  have hle : ∀ᶠ n in atTop, u y ≤ u (xs n) := by
    filter_upwards [hev] with n hn
    exact (hxs n).2 y ⟨hyX, hn.le⟩
  have hul : Tendsto (fun n => u (xs n)) atTop (𝓝 (u xl)) :=
    (hu xl hxX).tendsto.comp (tendsto_nhdsWithin_iff.mpr
      ⟨hxl, Eventually.of_forall fun n => (hxs n).1.1⟩)
  have := ge_of_tendsto hul hle
  linarith

/-- The nonnegative orthant is closed. -/
theorem appendixA_isClosed_nonnegOrthant (L : ℕ) : IsClosed (nonnegOrthant L) := by
  have : nonnegOrthant L = ⋂ l, {x : Fin L → ℝ | 0 ≤ x l} := by
    ext x
    simp [nonnegOrthant]
  rw [this]
  exact isClosed_iInter fun l => isClosed_le continuous_const (continuous_apply l)

/-- **Proof of Proposition 3.AA.1** (MWG, pp. 93-94). On `ℝ^L_+` the locally cheaper test holds
at every `(p̄, w̄)` with `w̄ > 0`: shrink an affordable bundle towards `0`. -/
theorem locallyCheaperAt_nonnegOrthant {pbar : Fin L → ℝ} {wbar : ℝ} (hw : 0 < wbar) :
    LocallyCheaperAt (nonnegOrthant L) pbar wbar := by
  intro x hx hbud ε hε
  set c : ℝ := Real.sqrt L * ‖x‖ + 1 with hc
  have hc0 : 0 < c := by positivity
  set s : ℝ := min (1 / 2) (ε / (2 * c)) with hs
  have hs0 : 0 < s := lt_min (by norm_num) (by positivity)
  have hs1 : s ≤ 1 / 2 := min_le_left _ _
  refine ⟨(1 - s) • x, fun l => ?_, ?_, ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_nonneg (by linarith) (hx l)
  · have hd : dist ((1 - s) • x) x = s * ‖x‖ := by
      rw [dist_eq_norm, show (1 - s) • x - x = (-s) • x by module, norm_smul, Real.norm_eq_abs,
        abs_neg, abs_of_pos hs0]
    calc euclidDist ((1 - s) • x) x ≤ Real.sqrt L * dist ((1 - s) • x) x :=
          euclidDist_le_sqrt_mul_dist _ _
      _ = s * (Real.sqrt L * ‖x‖) := by rw [hd]; ring
      _ ≤ ε / (2 * c) * c := by
          apply mul_le_mul (min_le_right _ _) (by linarith) (by positivity) (by positivity)
      _ < ε := by
          rw [div_mul_eq_mul_div, mul_comm 2 c, ← div_div, mul_div_cancel_right₀ _ hc0.ne']
          linarith
  · rw [dotProduct_smul, smul_eq_mul]
    nlinarith

/-- **Proposition 3.AA.1** (MWG, p. 93), upper hemicontinuity. If `u` is continuous on
`X = ℝ^L_+` (representing a locally nonsatiated preference, an assumption the proof does not
use), the demand correspondence `x(p, w)` is upper hemicontinuous at every `(p, w) ≫ 0`. -/
theorem proposition_3_AA_1 {u : (Fin L → ℝ) → ℝ} (hu : ContinuousOn u (nonnegOrthant L))
    {p : Fin L → ℝ} {w : ℝ} (hd : PWDomain p w) : DemandUHCAt (walrasianDemand u) p w :=
  demand_uhc_of_locallyCheaper (appendixA_isClosed_nonnegOrthant L) hu
    (locallyCheaperAt_nonnegOrthant hd.2)

/-- **Proposition 3.AA.1** (MWG, p. 93), continuity. If moreover `x(p, w)` is a function
(`x(p, w) = {s(p, w)}` at every `(p, w) ≫ 0`), it is continuous on `(p, w) ≫ 0`. -/
theorem proposition_3_AA_1_continuous {u : (Fin L → ℝ) → ℝ}
    (hu : ContinuousOn u (nonnegOrthant L)) {s : DemandFunction L}
    (hs : ∀ p w, PWDomain p w → walrasianDemand u p w = {s p w}) :
    ContinuousOn (fun q : (Fin L → ℝ) × ℝ => s q.1 q.2) (pwDomainSet L) := by
  have hfeas : ∀ p w, PWDomain p w → s p w ∈ budgetSet p w := by
    intro p w hd
    have : s p w ∈ walrasianDemand u p w := by rw [hs p w hd]; rfl
    exact this.1
  apply (demandUHC_iff_continuousOn hfeas).mp
  intro p w hd ps ws xs xl hds hp hw hxs hxl
  have h1 := proposition_3_AA_1 hu hd ps ws xs xl hds hp hw
    (fun n => by rw [hs _ _ (hds n)]; exact hxs n) hxl
  rw [hs p w hd] at h1
  exact h1

/-- **Proposition 3.AA.1** (MWG, p. 93) as stated, with the locally nonsatiated preference
represented by `u` among the hypotheses: upper hemicontinuity at every `(p, w) ≫ 0`. -/
theorem proposition_3_AA_1_stated {u : (Fin L → ℝ) → ℝ}
    {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop} (hu : ContinuousOn u (nonnegOrthant L))
    (_hrep : RepresentsOn (nonnegOrthant L) u r) (_hlns : LocallyNonsatiated (nonnegOrthant L) r) :
    ∀ p w, PWDomain p w → DemandUHCAt (walrasianDemand u) p w :=
  fun _ _ hd => proposition_3_AA_1 hu hd

/-! ### Figure 3.AA.3: an indivisible good -/

/-- **Figure 3.AA.3** (MWG, p. 94). A utility on `X = ℝ_+ × {0, 1, 2, ...}` for which `(0, 1)` is
preferred to `(w̄, 0)` (the figure's dashed indifference between `(0, 1)` and `z`):
`u(x) = x₁ + 2w̄ x₂`. -/
def figure_3_AA_3_utility (wbar : ℝ) (x : Fin 2 → ℝ) : ℝ := x 0 + 2 * wbar * x 1

/-- **Figure 3.AA.3** (MWG, p. 94). When good 2 costs more than the wealth `w̄`, the demand is
`(w̄, 0)` (only good 1 is consumed). -/
theorem figure_3_AA_3_demand_dear {wbar p2 : ℝ} (hw : 0 < wbar) (hp2 : wbar < p2) :
    walrasianDemandOn figure_2_C_2_set (figure_3_AA_3_utility wbar) ![1, p2] wbar =
      {![wbar, 0]} := by
  have hB : ∀ y ∈ budgetSetOn figure_2_C_2_set ![1, p2] wbar, y 1 = 0 ∧ y 0 ≤ wbar := by
    rintro y ⟨⟨hy0, k, hk⟩, hc⟩
    simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      one_mul] at hc
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · rw [hk, Nat.cast_zero] at hc ⊢
      exact ⟨rfl, by linarith⟩
    · have : (1 : ℝ) ≤ k := by exact_mod_cast hk1
      rw [hk] at hc
      nlinarith
  have hmem : ![wbar, 0] ∈ budgetSetOn figure_2_C_2_set ![1, p2] wbar := by
    refine ⟨⟨by simpa using hw.le, 0, by simp⟩, ?_⟩
    simp [dotProduct, Fin.sum_univ_two]
  ext y
  rw [Set.mem_singleton_iff]
  constructor
  · rintro ⟨hy, hopt⟩
    have h1 := hB y hy
    have h2 := hopt _ hmem
    simp only [figure_3_AA_3_utility, Matrix.cons_val_zero, Matrix.cons_val_one, h1.1] at h2
    funext l
    fin_cases l
    · simp
      linarith [h1.2]
    · simpa using h1.1
  · rintro rfl
    refine ⟨hmem, fun y hy => ?_⟩
    have h1 := hB y hy
    simp only [figure_3_AA_3_utility, Matrix.cons_val_zero, Matrix.cons_val_one, h1.1]
    linarith [h1.2]

/-- **Figure 3.AA.3** (MWG, p. 94). At `(p̄, w̄) = (1, w̄, w̄)` a unit of good 2 is just
affordable and `x(p̄, w̄) = (0, 1)`. -/
theorem figure_3_AA_3_demand_bar {wbar : ℝ} (hw : 0 < wbar) :
    walrasianDemandOn figure_2_C_2_set (figure_3_AA_3_utility wbar) ![1, wbar] wbar =
      {![0, 1]} := by
  have hB : ∀ y ∈ budgetSetOn figure_2_C_2_set ![1, wbar] wbar,
      (y 1 = 0 ∧ y 0 ≤ wbar) ∨ y = ![0, 1] := by
    rintro y ⟨⟨hy0, k, hk⟩, hc⟩
    simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      one_mul] at hc
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · interval_cases k
      · rw [hk, Nat.cast_zero] at hc
        exact Or.inl ⟨by rw [hk, Nat.cast_zero], by linarith⟩
      · rw [hk, Nat.cast_one] at hc
        right
        funext l
        fin_cases l
        · simp
          linarith
        · simpa using hk
    · have : (2 : ℝ) ≤ k := by exact_mod_cast hk2
      rw [hk] at hc
      nlinarith
  have hmem : ![0, 1] ∈ budgetSetOn figure_2_C_2_set ![1, wbar] wbar := by
    refine ⟨⟨by simp, 1, by simp⟩, ?_⟩
    simp [dotProduct, Fin.sum_univ_two]
  ext y
  rw [Set.mem_singleton_iff]
  constructor
  · rintro ⟨hy, hopt⟩
    rcases hB y hy with h1 | h1
    · have h2 := hopt _ hmem
      simp only [figure_3_AA_3_utility, Matrix.cons_val_zero, Matrix.cons_val_one, h1.1] at h2
      linarith [h1.2]
    · exact h1
  · rintro rfl
    refine ⟨hmem, fun y hy => ?_⟩
    rcases hB y hy with h1 | h1
    · simp only [figure_3_AA_3_utility, Matrix.cons_val_zero, Matrix.cons_val_one, h1.1]
      linarith [h1.2]
    · rw [h1]

/-- **Figure 3.AA.3** (MWG, p. 94). The locally cheaper test fails at `(p̄, w̄) = (1, w̄, w̄)`:
`(0, 1)` is affordable but every nearby bundle of `X` contains a unit of good 2 and costs at
least `w̄`. -/
theorem figure_3_AA_3_not_locallyCheaper (wbar : ℝ) :
    ¬LocallyCheaperAt figure_2_C_2_set ![1, wbar] wbar := by
  intro h
  obtain ⟨y, ⟨hy0, k, hk⟩, hyd, hyc⟩ := h ![0, 1] ⟨by simp, 1, by simp⟩
    (by simp [dotProduct, Fin.sum_univ_two]) (1 / 2) (by norm_num)
  have h1 := (abs_sub_le_euclidDist y ![0, 1] 1).trans_lt hyd
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero, hk] at h1
  have hk1 : k = 1 := by
    rw [abs_lt] at h1
    have h2 : (k : ℝ) < 2 := by linarith [h1.2]
    have h3 : (0 : ℝ) < k := by linarith [h1.1]
    have : k < 2 := by exact_mod_cast h2
    have : 0 < k := by exact_mod_cast h3
    omega
  subst hk1
  simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, hk,
    Nat.cast_one] at hyc
  linarith

/-- The prices `pⁿ = (1, w̄ + 1/(n+1))` converge to `(1, w̄)`. -/
theorem appendixA_tendsto_figure_prices (wbar : ℝ) :
    Tendsto (fun n : ℕ => (![1, wbar + 1 / ((n : ℝ) + 1)] : Fin 2 → ℝ)) atTop (𝓝 ![1, wbar]) := by
  rw [tendsto_pi_nhds]
  intro l
  fin_cases l
  · simp
  · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add wbar

/-- **Figure 3.AA.3** (MWG, p. 94). Demand is not upper hemicontinuous at `(1, w̄, w̄)`: along
`pⁿ = (1, w̄ + 1/(n+1))` demand is constantly `(w̄, 0)`, which is not demanded at `(1, w̄, w̄)`. -/
theorem figure_3_AA_3_not_uhc {wbar : ℝ} (hw : 0 < wbar) :
    ¬DemandUHCAt (fun p w => walrasianDemandOn figure_2_C_2_set (figure_3_AA_3_utility wbar) p w)
      ![1, wbar] wbar := by
  intro h
  have hpos : ∀ n : ℕ, wbar < wbar + 1 / ((n : ℝ) + 1) := fun n => by
    have : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  have := h _ (fun _ => wbar) (fun _ => ![wbar, 0]) ![wbar, 0]
    (fun n => ⟨Fin.forall_fin_two.mpr ⟨by simp, by simpa using hw.trans (hpos n)⟩, hw⟩)
    (appendixA_tendsto_figure_prices wbar) tendsto_const_nhds
    (fun n => by beta_reduce; rw [figure_3_AA_3_demand_dear hw (hpos n)]; rfl) tendsto_const_nhds
  beta_reduce at this
  rw [figure_3_AA_3_demand_bar hw, Set.mem_singleton_iff] at this
  have := congrFun this 1
  simp at this

/-! ### Exercise 3.AA.1 -/

/-- **Exercise 3.AA.1** (MWG, p. 104). The consumption set `X = {x ∈ ℝ²_+ : x₁ + x₂ ≥ 1}`. -/
def exercise_3_AA_1_set : Set (Fin 2 → ℝ) := {x | 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ 1 ≤ x 0 + x 1}

/-- **Exercise 3.AA.1** (MWG, p. 104). The utility `u(x) = x₂`. -/
def exercise_3_AA_1_utility (x : Fin 2 → ℝ) : ℝ := x 1

/-- **Exercise 3.AA.1(a)** (MWG, p. 104). The locally cheaper consumption test fails at
`(p, w) = (1, 1, 1)`: every bundle of `X` costs at least `1`. -/
theorem exercise_3_AA_1a : ¬LocallyCheaperAt exercise_3_AA_1_set ![1, 1] 1 := by
  intro h
  obtain ⟨y, hy, -, hyc⟩ := h ![0, 1] ⟨by simp, by simp, by simp⟩
    (by simp [dotProduct, Fin.sum_univ_two]) 1 one_pos
  simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    one_mul] at hyc
  linarith [hy.2.2]

/-- **Exercise 3.AA.1(b)** (MWG, p. 104). Demand at `(1, 1, 1)` is `(0, 1)`. -/
theorem exercise_3_AA_1b_demand_bar :
    walrasianDemandOn exercise_3_AA_1_set exercise_3_AA_1_utility ![1, 1] 1 = {![0, 1]} := by
  have hmem : ![0, 1] ∈ budgetSetOn exercise_3_AA_1_set ![1, 1] 1 :=
    ⟨⟨by simp, by simp, by simp⟩, by simp [dotProduct, Fin.sum_univ_two]⟩
  ext y
  rw [Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨⟨hy0, hy1, hy01⟩, hc⟩, hopt⟩
    have h2 := hopt _ hmem
    simp only [exercise_3_AA_1_utility, Matrix.cons_val_one, Matrix.cons_val_zero] at h2
    simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      one_mul] at hc
    funext l
    fin_cases l
    · simp
      linarith
    · simp
      linarith
  · rintro rfl
    refine ⟨hmem, fun y hy => ?_⟩
    obtain ⟨⟨hy0, -, -⟩, hc⟩ := hy
    simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      one_mul] at hc
    simp only [exercise_3_AA_1_utility, Matrix.cons_val_one, Matrix.cons_val_zero]
    linarith

/-- **Exercise 3.AA.1(b)** (MWG, p. 104). When good 2 is dearer than good 1, `p = (1, p₂)` with
`p₂ > 1` and `w = 1`, the only affordable bundle of `X` is `(1, 0)`, so demand is `(1, 0)`. -/
theorem exercise_3_AA_1b_demand_dear {p2 : ℝ} (hp2 : 1 < p2) :
    walrasianDemandOn exercise_3_AA_1_set exercise_3_AA_1_utility ![1, p2] 1 = {![1, 0]} := by
  have hB : ∀ y ∈ budgetSetOn exercise_3_AA_1_set ![1, p2] 1, y = ![1, 0] := by
    rintro y ⟨⟨hy0, hy1, hy01⟩, hc⟩
    simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      one_mul] at hc
    have hy1' : y 1 = 0 := by nlinarith
    rw [hy1', mul_zero, add_zero] at hc
    funext l
    fin_cases l
    · simp
      linarith
    · simpa using hy1'
  have hmem : ![1, 0] ∈ budgetSetOn exercise_3_AA_1_set ![1, p2] 1 :=
    ⟨⟨by simp, by simp, by simp⟩, by simp [dotProduct, Fin.sum_univ_two]⟩
  ext y
  rw [Set.mem_singleton_iff]
  constructor
  · rintro ⟨hy, -⟩
    exact hB y hy
  · rintro rfl
    exact ⟨hmem, fun y hy => by rw [hB y hy]⟩

/-- **Exercise 3.AA.1(b)** (MWG, p. 104). Demand is single-valued near `(1, 1, 1)` along
`pⁿ = (1, 1 + 1/(n+1))` but not continuous there: `x(pⁿ, 1) = (1, 0)` for all `n` while
`x(1, 1, 1) = (0, 1)`; in particular the demand correspondence is not upper hemicontinuous at
`(1, 1, 1)`. -/
theorem exercise_3_AA_1b :
    (∀ n : ℕ, walrasianDemandOn exercise_3_AA_1_set exercise_3_AA_1_utility
        ![1, 1 + 1 / ((n : ℝ) + 1)] 1 = {![1, 0]}) ∧
      walrasianDemandOn exercise_3_AA_1_set exercise_3_AA_1_utility ![1, 1] 1 = {![0, 1]} ∧
      ¬DemandUHCAt (fun p w => walrasianDemandOn exercise_3_AA_1_set exercise_3_AA_1_utility p w)
        ![1, 1] 1 := by
  have hpos : ∀ n : ℕ, (1 : ℝ) < 1 + 1 / ((n : ℝ) + 1) := fun n => by
    have : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  refine ⟨fun n => exercise_3_AA_1b_demand_dear (hpos n), exercise_3_AA_1b_demand_bar, ?_⟩
  intro h
  have := h _ (fun _ => 1) (fun _ => ![1, 0]) ![1, 0]
    (fun n => ⟨Fin.forall_fin_two.mpr ⟨by simp, by simpa using one_pos.trans (hpos n)⟩,
      one_pos⟩)
    (appendixA_tendsto_figure_prices 1) tendsto_const_nhds
    (fun n => by beta_reduce; rw [exercise_3_AA_1b_demand_dear (hpos n)]; rfl) tendsto_const_nhds
  beta_reduce at this
  rw [exercise_3_AA_1b_demand_bar, Set.mem_singleton_iff] at this
  have := congrFun this 1
  simp at this

end MWG.ClassicalDemand
