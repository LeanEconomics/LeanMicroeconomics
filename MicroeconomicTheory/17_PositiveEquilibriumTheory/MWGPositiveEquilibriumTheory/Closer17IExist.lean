/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPositiveEquilibriumTheory.LargeEconomies
import MWGPositiveEquilibriumTheory.Exercise17C2
import MWGPositiveEquilibriumTheory.DemandContinuity
import MWGPositiveEquilibriumTheory.NegishiLogEconomy
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.LocallyConvex.Separation

/-!
# Existence for the convexified economy (MWG Section 17.I, p. 628, footnote 73)

"In the limit the excess demand correspondence is convex valued and the existence of an
equilibrium can be established as in Section 17.C." This is proved for an exchange economy with
consumption sets `ℝ^L₊`, continuous and strongly monotone (possibly nonconvex) preferences and
`ωᵢ ≫ 0` (`section_17_I_convexified_existence`): there is `p ≫ 0` and `x̄ᵢ ∈ conv xᵢ(p)` with
`∑ᵢ x̄ᵢ = ω̄`. Together with `near_equilibrium` every replica then has a near equilibrium
(`section_17_I_near_equilibrium_exists`). Instance: one nonconvex consumer (`x₁² + x₂²`) and one
convex consumer (`log(1 + x₁) + log(1 + x₂)`), `ωᵢ = (1, 1)` (`section_17_I_convexified_instance`).

* `convexHull_fin_rep`, `isCompact_convexHull_of_isCompact`: Carathéodory's theorem with
  `dim + 1` points and the compactness of the convex hull of a compact set.
* `convZ E p = ∑ᵢ conv xᵢ(p) - ω̄` (`convZ`) satisfies the hypotheses of the correspondence
  existence theorem `exercise_17_C_2`: upper hemicontinuity (`convZ_uhc`, from Proposition 3.AA.1
  for nonconvex demand and a separation argument, `convDemand_closed`), nonempty convex values,
  homogeneity, Walras' law, a lower bound and the boundary condition (`convZ_boundary`, from
  `demand_bounded_near_boundary_false`).
-/

namespace MWG.PositiveEquilibriumTheory

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.GeneralEquilibriumExamples MWG.WelfareTheorems
open Filter Topology Module

/-! ### Carathéodory with a fixed number of points -/

/-- Carathéodory's theorem with exactly `dim E + 1` points (some weights may vanish). -/
theorem convexHull_fin_rep {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {K : Set E} {x : E} (hx : x ∈ convexHull ℝ K) :
    ∃ w : Fin (finrank ℝ E + 1) → ℝ, ∃ y : Fin (finrank ℝ E + 1) → E,
      ((∀ k, 0 ≤ w k) ∧ ∑ k, w k = 1) ∧ (∀ k, y k ∈ K) ∧ ∑ k, w k • y k = x := by
  classical
  obtain ⟨ι, _, z, w, hz, hai, hw, hsum, hx⟩ := eq_pos_convex_span_of_mem_convexHull hx
  have hcard : Fintype.card ι ≤ finrank ℝ E + 1 :=
    hai.card_le_finrank_succ.trans (Nat.add_le_add_right (Submodule.finrank_le _) 1)
  set e : ι ↪ Fin (finrank ℝ E + 1) :=
    (Fintype.equivFin ι).toEmbedding.trans (Fin.castLEEmb hcard) with he
  obtain ⟨i0⟩ : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp at hsum
  have hsel : ∀ i, (∃ j, e j = e i) := fun i => ⟨i, rfl⟩
  have hch : ∀ i, (hsel i).choose = i := fun i => e.injective (hsel i).choose_spec
  refine ⟨fun k => ∑ i, if e i = k then w i else 0,
    fun k => if h : ∃ i, e i = k then z h.choose else z i0, ⟨fun k => ?_, ?_⟩, fun k => ?_, ?_⟩
  · exact Finset.sum_nonneg fun i _ => by split_ifs <;> [exact (hw i).le; exact le_rfl]
  · rw [Finset.sum_comm]
    simp [hsum]
  · dsimp only
    split_ifs with h
    · exact hz ⟨_, rfl⟩
    · exact hz ⟨_, rfl⟩
  · simp only [Finset.sum_smul, ite_smul, zero_smul]
    rw [Finset.sum_comm, ← hx]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_univ, ↓reduceIte, hsel i, ↓reduceDIte, hch i]

/-- The convex hull of a compact set in a finite-dimensional space is compact: it is the image of
the compact set `Δ × Kᵈ⁺¹` under `(w, y) ↦ ∑ₖ wₖ yₖ`. -/
theorem isCompact_convexHull_of_isCompact {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {K : Set E} (hK : IsCompact K) : IsCompact (convexHull ℝ K) := by
  set n := finrank ℝ E + 1
  set S : Set (Fin n → ℝ) := {w | (∀ k, 0 ≤ w k) ∧ ∑ k, w k = 1} with hSdef
  have heq : convexHull ℝ K = (fun q : (Fin n → ℝ) × (Fin n → E) => ∑ k, q.1 k • q.2 k) ''
      (S ×ˢ Set.pi Set.univ fun _ => K) := by
    ext x
    constructor
    · intro hx
      obtain ⟨w, y, hw, hy, hsum⟩ := convexHull_fin_rep hx
      exact ⟨(w, y), ⟨hw, fun k _ => hy k⟩, hsum⟩
    · rintro ⟨⟨w, y⟩, ⟨hw, hy⟩, rfl⟩
      exact (convex_convexHull ℝ K).sum_mem (fun k _ => hw.1 k) hw.2
        fun k _ => subset_convexHull ℝ K (hy k (Set.mem_univ k))
  rw [heq]
  have hSc : IsClosed S := by
    have : S = (⋂ k, {w : Fin n → ℝ | 0 ≤ w k}) ∩ {w | ∑ k, w k = 1} := by
      ext w
      simp [hSdef, Set.mem_iInter]
    rw [this]
    exact (isClosed_iInter fun k => isClosed_le continuous_const (continuous_apply k)).inter
      (isClosed_eq (continuous_finsetSum _ fun k _ => continuous_apply k) continuous_const)
  have hS : IsCompact S := by
    refine (isCompact_Icc (a := (0 : Fin n → ℝ)) (b := fun _ => 1)).of_isClosed_subset hSc
      fun w hw => ⟨fun k => hw.1 k, fun k => ?_⟩
    have := Finset.single_le_sum (f := w) (fun j _ => hw.1 j) (Finset.mem_univ k)
    change w k ≤ 1
    linarith [hw.2]
  exact (hS.prod (isCompact_univ_pi fun _ => hK)).image (by fun_prop)

/-- A point of `conv K` dominates (for a linear functional `f`) some point of `K`. -/
theorem exists_le_of_mem_convexHull {E : Type*} [AddCommGroup E] [Module ℝ E] {K : Set E}
    (f : E →ₗ[ℝ] ℝ) {x : E} (hx : x ∈ convexHull ℝ K) : ∃ y ∈ K, f y ≤ f x := by
  by_contra h
  push Not at h
  have hsub : convexHull ℝ K ⊆ {y | f x < f y} :=
    convexHull_min (fun y hy => h y hy) (convex_halfSpace_gt f.isLinear _)
  exact lt_irrefl (f x) (hsub hx)

/-! ### The convexified excess demand correspondence -/

variable {ι : Type*} [Fintype ι] {L : ℕ}

/-- **Section 17.I** (MWG, p. 628). The excess demand correspondence of the convexified
economy: `∑ᵢ conv xᵢ(p) - ω̄`. -/
def convZ (E : ExchangeEconomy ι L) (p : Fin L → ℝ) : Set (Fin L → ℝ) :=
  {z | ∃ x : ι → Fin L → ℝ, (∀ i, x i ∈ convexHull ℝ (E.demand i p)) ∧
    z = ∑ i, x i - E.totalEndowment}

omit [Fintype ι] in
/-- The demand set in the notation of Chapter 3. -/
theorem convZ_demand_eq {E : ExchangeEconomy ι L} (hX : ∀ i, E.X i = nonnegOrthant L) (i : ι)
    (q : Fin L → ℝ) : E.demand i q = walrasianDemand (E.u i) q (q ⬝ᵥ E.ω i) := by
  simp only [ExchangeEconomy.demand, hX i, walrasianDemand]

omit [Fintype ι] in
/-- At `q ≫ 0`, `conv xᵢ(q)` lies in the box `0 ≤ x ≤ (q·ωᵢ/qₗ)ₗ`. -/
theorem convDemand_subset_Icc {E : ExchangeEconomy ι L} (hX : ∀ i, E.X i = nonnegOrthant L)
    (i : ι) {q : Fin L → ℝ} (hq : q ∈ posOrthant L) :
    convexHull ℝ (E.demand i q) ⊆ Set.Icc 0 (fun l => (q ⬝ᵥ E.ω i) / q l) :=
  convexHull_min (demand_subset_Icc (hX i) hq) (convex_Icc _ _)

omit [Fintype ι] in
/-- Along `qⁿ → q ≫ 0`, eventually `conv xᵢ(qⁿ)` lies in the box `0 ≤ x ≤ (2(q·ωᵢ + 1)/qₗ)ₗ`. -/
theorem convDemand_eventually_Icc {E : ExchangeEconomy ι L}
    (hX : ∀ i, E.X i = nonnegOrthant L) (hω : ∀ i, E.ω i ∈ posOrthant L) (i : ι)
    {ps : ℕ → Fin L → ℝ} {p : Fin L → ℝ} (hps : ∀ n, ps n ∈ posOrthant L)
    (hp : p ∈ posOrthant L) (hlim : Tendsto ps atTop (𝓝 p)) :
    ∀ᶠ n in atTop, convexHull ℝ (E.demand i (ps n)) ⊆
      Set.Icc 0 (fun l => 2 * (p ⬝ᵥ E.ω i + 1) / p l) := by
  have hw := appendixA_tendsto_dotProduct_seq hlim (tendsto_const_nhds (x := E.ω i))
  have h1 : ∀ᶠ n in atTop, ps n ⬝ᵥ E.ω i < p ⬝ᵥ E.ω i + 1 :=
    hw.eventually (gt_mem_nhds (lt_add_one _))
  have h2 : ∀ᶠ n in atTop, ∀ l, p l / 2 < ps n l := eventually_all.2 fun l =>
    ((tendsto_pi_nhds.1 hlim) l).eventually (lt_mem_nhds (half_lt_self (hp l)))
  filter_upwards [h1, h2] with n hn1 hn2
  refine (convDemand_subset_Icc hX i (hps n)).trans fun x hx => ⟨hx.1, fun l => ?_⟩
  have hxl := hx.2 l
  have hpos : 0 ≤ ps n ⬝ᵥ E.ω i :=
    Finset.sum_nonneg fun k _ => mul_nonneg (hps n k).le (hω i k).le
  have hpl := hp l
  have hpnl := hps n l
  calc x l ≤ (ps n ⬝ᵥ E.ω i) / ps n l := hxl
    _ ≤ (p ⬝ᵥ E.ω i + 1) / (p l / 2) :=
        div_le_div₀ (by linarith) hn1.le (by positivity) (hn2 l).le
    _ = 2 * (p ⬝ᵥ E.ω i + 1) / p l := by field_simp

omit [Fintype ι] in
/-- **Section 17.I** (MWG, p. 628). The convexified demand correspondence `q ↦ conv xᵢ(q)` has a
closed graph on `ℝ^L₊₊` (continuous preferences, `ωᵢ ≫ 0`). If `xⁿ ∈ conv xᵢ(qⁿ)` tended to
`x ∉ conv xᵢ(q)`, a hyperplane `f` would separate `x` from the compact convex set `conv xᵢ(q)`;
bundles `yⁿ ∈ xᵢ(qⁿ)` with `f(yⁿ) ≤ f(xⁿ)` have a limit point in `xᵢ(q)` (Proposition 3.AA.1),
which contradicts the separation. -/
theorem convDemand_closed (hL : 0 < L) {E : ExchangeEconomy ι L}
    (hX : ∀ i, E.X i = nonnegOrthant L)
    (hc : ∀ i, ContinuousOn (E.u i) (nonnegOrthant L)) (hω : ∀ i, E.ω i ∈ posOrthant L) (i : ι)
    {ps : ℕ → Fin L → ℝ} {p : Fin L → ℝ} (hps : ∀ n, ps n ∈ posOrthant L)
    (hp : p ∈ posOrthant L) (hlim : Tendsto ps atTop (𝓝 p)) {xs : ℕ → Fin L → ℝ}
    (hxs : ∀ n, xs n ∈ convexHull ℝ (E.demand i (ps n))) {x : Fin L → ℝ}
    (hx : Tendsto xs atTop (𝓝 x)) : x ∈ convexHull ℝ (E.demand i p) := by
  by_contra hnot
  have hcl : IsClosed (convexHull ℝ (E.demand i p)) :=
    (isCompact_convexHull_of_isCompact (isCompact_demand (hX i) (hc i) hp)).isClosed
  obtain ⟨f, u, hfx, hfb⟩ := geometric_hahn_banach_point_closed (convex_convexHull ℝ _) hcl hnot
  choose y hy hfy using fun n => exists_le_of_mem_convexHull (f : (Fin L → ℝ) →ₗ[ℝ] ℝ) (hxs n)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (convDemand_eventually_Icc hX hω i hps hp hlim)
  have hbox : ∀ n, y (n + N) ∈ Set.Icc (0 : Fin L → ℝ)
      (fun l => 2 * (p ⬝ᵥ E.ω i + 1) / p l) :=
    fun n => hN (n + N) (by omega) (subset_convexHull ℝ _ (hy (n + N)))
  obtain ⟨a, -, φ, hφ, ha⟩ := isCompact_Icc.tendsto_subseq hbox
  have hP : Tendsto (fun n => ps (φ n + N)) atTop (𝓝 p) :=
    hlim.comp ((tendsto_add_atTop_nat N).comp hφ.tendsto_atTop)
  have hmem : a ∈ E.demand i p := by
    rw [convZ_demand_eq hX]
    refine proposition_3_AA_1 (hc i) ⟨hp, ?_⟩ (fun n => ps (φ n + N))
      (fun n => ps (φ n + N) ⬝ᵥ E.ω i) (fun n => y (φ n + N)) a (fun n => ⟨hps _, ?_⟩) hP
      (appendixA_tendsto_dotProduct_seq hP tendsto_const_nhds) (fun n => ?_) ha
    · exact Finset.sum_pos (fun k _ => mul_pos (hp k) (hω i k)) ⟨⟨0, hL⟩, Finset.mem_univ _⟩
    · exact Finset.sum_pos (fun k _ => mul_pos (hps _ k) (hω i k)) ⟨⟨0, hL⟩, Finset.mem_univ _⟩
    · have := hy (φ n + N)
      rwa [convZ_demand_eq hX] at this
  have hle : f a ≤ f x :=
    le_of_tendsto_of_tendsto' ((f.continuous.tendsto a).comp ha)
      ((f.continuous.tendsto x).comp (hx.comp ((tendsto_add_atTop_nat N).comp
        hφ.tendsto_atTop))) fun n => hfy (φ n + N)
  have := hfb a (subset_convexHull ℝ _ hmem)
  linarith

/-- **Section 17.I** (MWG, p. 628). The convexified excess demand correspondence is upper
hemicontinuous on `ℝ^L₊₊`. -/
theorem convZ_uhc (hL : 0 < L) {E : ExchangeEconomy ι L} (hX : ∀ i, E.X i = nonnegOrthant L)
    (hc : ∀ i, ContinuousOn (E.u i) (nonnegOrthant L)) (hω : ∀ i, E.ω i ∈ posOrthant L) :
    UpperHemicontinuousMWG (posOrthant L) (convZ E) := by
  refine ⟨fun ps zs p z hps hp hzs hlim hz => ?_, fun B hBA hB => ?_⟩
  · choose x hx hzx using hzs
    obtain ⟨N, hN⟩ := eventually_atTop.1 (eventually_all.2 fun i =>
      convDemand_eventually_Icc hX hω i hps hp hlim)
    have hbox : ∀ n, x (n + N) ∈ Set.Icc (0 : ι → Fin L → ℝ)
        (fun i l => 2 * (p ⬝ᵥ E.ω i + 1) / p l) := fun n =>
      ⟨fun i => (hN (n + N) (by omega) i (hx (n + N) i)).1,
        fun i => (hN (n + N) (by omega) i (hx (n + N) i)).2⟩
    obtain ⟨a, -, φ, hφ, ha⟩ := isCompact_Icc.tendsto_subseq hbox
    have hsub : Tendsto (fun n => φ n + N) atTop atTop :=
      (tendsto_add_atTop_nat N).comp hφ.tendsto_atTop
    have hai : ∀ i, a i ∈ convexHull ℝ (E.demand i p) := fun i =>
      convDemand_closed hL hX hc hω i (fun n => hps (φ n + N)) hp (hlim.comp hsub)
        (fun n => hx (φ n + N) i) (tendsto_pi_nhds.1 ha i)
    refine ⟨a, hai, ?_⟩
    have h1 : Tendsto (fun n => zs (φ n + N)) atTop (𝓝 (∑ i, a i - E.totalEndowment)) := by
      simp only [hzx]
      exact (tendsto_finsetSum _ fun i _ => tendsto_pi_nhds.1 ha i).sub_const _
    exact tendsto_nhds_unique (hz.comp hsub) h1
  · rcases B.eq_empty_or_nonempty with hBe | hBne
    · simp [hBe]
    -- a positive lower bound on prices and an upper bound on wealths over `B`
    have hmin : ∀ l : Fin L, ∃ m > 0, ∀ q ∈ B, m ≤ q l := fun l => by
      obtain ⟨q0, hq0, hmin⟩ := hB.exists_isMinOn hBne (continuous_apply l).continuousOn
      exact ⟨q0 l, hBA hq0 l, fun q hq => hmin hq⟩
    choose m hm hmB using hmin
    have hmax : ∀ i, ∃ M, ∀ q ∈ B, q ⬝ᵥ E.ω i ≤ M := fun i => by
      have hcont : Continuous fun q : Fin L → ℝ => q ⬝ᵥ E.ω i := by
        simp only [dotProduct]
        fun_prop
      obtain ⟨M, hM⟩ := hB.bddAbove_image hcont.continuousOn
      exact ⟨M, fun q hq => hM ⟨q, hq, rfl⟩⟩
    choose M hM using hmax
    refine (Metric.isBounded_Icc (fun l => -E.totalEndowment l)
      (fun l => ∑ i, M i / m l)).subset ?_
    simp only [Set.iUnion_subset_iff]
    rintro q hq _ ⟨x, hx, rfl⟩
    have hbd := fun i => convDemand_subset_Icc hX i (hBA hq) (hx i)
    refine ⟨fun l => ?_, fun l => ?_⟩
    · simp only [Pi.sub_apply, Finset.sum_apply]
      have := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => (hbd i).1 l
      linarith
    · simp only [Pi.sub_apply, Finset.sum_apply]
      have htot : 0 ≤ E.totalEndowment l := by
        rw [ExchangeEconomy.totalEndowment, Finset.sum_apply]
        exact Finset.sum_nonneg fun i _ => (hω i l).le
      have : ∑ i, x i l ≤ ∑ i, M i / m l := Finset.sum_le_sum fun i _ => by
        have h1 := (hbd i).2 l
        have hpos : 0 ≤ q ⬝ᵥ E.ω i :=
          Finset.sum_nonneg fun k _ => mul_nonneg (hBA hq k).le (hω i k).le
        exact h1.trans (div_le_div₀ ((hpos.trans (hM i q hq))) (hM i q hq) (hm l) (hmB l q hq))
      linarith

/-- **Section 17.I** (MWG, p. 628). The convexified excess demand correspondence satisfies the
boundary condition: along `qⁿ ≫ 0` tending to a nonzero price vector with a zero component, every
selection has an unbounded coordinate (a consumer's bundles in `conv xᵢ(qⁿ)` dominate, in total
quantity, demanded bundles, which cannot stay bounded: `demand_bounded_near_boundary_false`). -/
theorem convZ_boundary [Nonempty ι] {E : ExchangeEconomy ι L}
    (hX : ∀ i, E.X i = nonnegOrthant L) (hc : ∀ i, ContinuousOn (E.u i) (nonnegOrthant L))
    (hm : ∀ i, UtilityStronglyMonotone (E.u i)) (hω : ∀ i, E.ω i ∈ posOrthant L) :
    CorrBoundary (convZ E) := by
  intro ps p zs hps hlim hp0 ⟨l0, hl0⟩ hzs M
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  obtain ⟨φ, hφ, hφP⟩ := extraction_of_frequently_atTop hcon
  obtain ⟨i0⟩ := ‹Nonempty ι›
  have hpnn : ∀ l, 0 ≤ p l := nonneg_of_tendsto_pos hps hlim
  choose x hx hzx using hzs
  -- bounds on the selection of consumer `i0`
  set B : ℝ := ∑ l, (M + E.totalEndowment l) with hB
  have hxle : ∀ n, ∑ l, x (φ n) i0 l ≤ B := by
    intro n
    have hP := hφP n
    push Not at hP
    refine Finset.sum_le_sum fun l _ => ?_
    have hzl := hP l
    rw [hzx, Pi.sub_apply, Finset.sum_apply] at hzl
    have hnn : ∀ i, 0 ≤ x (φ n) i l := fun i =>
      (convDemand_subset_Icc hX i (hps (φ n)) (hx (φ n) i)).1 l
    have : x (φ n) i0 l ≤ ∑ i, x (φ n) i l :=
      Finset.single_le_sum (f := fun i => x (φ n) i l) (fun i _ => hnn i) (Finset.mem_univ i0)
    linarith
  set f : (Fin L → ℝ) →ₗ[ℝ] ℝ := ∑ l, LinearMap.proj l with hf
  have hfv : ∀ v : Fin L → ℝ, f v = ∑ l, v l := fun v => by
    simp [hf, LinearMap.sum_apply]
  choose y hy hfy using fun n => exists_le_of_mem_convexHull f (hx (φ n) i0)
  have hyB : ∀ n l, y n l ≤ B := by
    intro n l
    have hy0 : ∀ k, 0 ≤ y n k := fun k => by
      have := (hy n).1.1
      rw [hX i0] at this
      exact this k
    have h1 : y n l ≤ ∑ k, y n k :=
      Finset.single_le_sum (f := fun k => y n k) (fun k _ => hy0 k) (Finset.mem_univ l)
    have h2 := hfy n
    rw [hfv, hfv] at h2
    linarith [hxle n]
  have hw : Tendsto (fun n => ps (φ n) ⬝ᵥ E.ω i0) atTop (𝓝 (p ⬝ᵥ E.ω i0)) :=
    appendixA_tendsto_dotProduct_seq (hlim.comp hφ.tendsto_atTop) tendsto_const_nhds
  exact demand_bounded_near_boundary_false (hc i0) (hm i0) (fun n => hps (φ n))
    (hlim.comp hφ.tendsto_atTop) hl0 (dotProduct_pos_of_ne_zero hpnn hp0 (hω i0)) hw
    (fun n => by have := hy n; rwa [convZ_demand_eq hX] at this) hyB

/-- **Section 17.I** (MWG, p. 628; footnote 73). Existence for the convexified economy: in an
exchange economy with `L ≥ 1` goods, at least one consumer, consumption sets `ℝ^L₊`, continuous and
strongly monotone (not necessarily convex) preferences and `ωᵢ ≫ 0`, there are `p ≫ 0` and
bundles `x̄ᵢ ∈ conv xᵢ(p)` with `∑ᵢ x̄ᵢ = ω̄`: the convexified excess demand correspondence has a
zero ("existence follows as in Section 17.C", through `exercise_17_C_2`). -/
theorem section_17_I_convexified_existence [Nonempty ι] (hL : 0 < L)
    {E : ExchangeEconomy ι L} (hX : ∀ i, E.X i = nonnegOrthant L)
    (hc : ∀ i, ContinuousOn (E.u i) (nonnegOrthant L))
    (hm : ∀ i, UtilityStronglyMonotone (E.u i)) (hω : ∀ i, E.ω i ∈ posOrthant L) :
    ∃ p ∈ posOrthant L, ∃ x : ι → Fin L → ℝ,
      (∀ i, x i ∈ convexHull ℝ (E.demand i p)) ∧ ∑ i, x i = E.totalEndowment := by
  have hbud : ∀ i {q : Fin L → ℝ}, ∀ y ∈ convexHull ℝ (E.demand i q), q ⬝ᵥ y = q ⬝ᵥ E.ω i :=
    fun i q y hy => by
      have hsub : convexHull ℝ (E.demand i q) ⊆ {v | q ⬝ᵥ v = q ⬝ᵥ E.ω i} := by
        refine convexHull_min (fun v hv => ed_budget_eq hX ((hm i).lns hL) hv) ?_
        intro a ha b hb s t _ _ hst
        change q ⬝ᵥ a = q ⬝ᵥ E.ω i at ha
        change q ⬝ᵥ b = q ⬝ᵥ E.ω i at hb
        change q ⬝ᵥ (s • a + t • b) = q ⬝ᵥ E.ω i
        rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul, ha, hb,
          ← add_mul, hst, one_mul]
      exact hsub hy
  obtain ⟨p, hp, x, hx, h0⟩ := exercise_17_C_2 (Z := convZ E) (convZ_uhc hL hX hc hω)
    (fun q hq => by
      choose x hx using fun i => demand_nonempty hX (hc i) (fun l => (hω i l).le) hq
      exact ⟨_, x, fun i => subset_convexHull ℝ _ (hx i), rfl⟩)
    (fun q hq => by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩ a b ha hb hab
      refine ⟨fun i => a • x i + b • x' i, fun i => (convex_convexHull ℝ _) (hx i) (hx' i) ha hb
        hab, ?_⟩
      change a • (∑ i, x i - E.totalEndowment) + b • (∑ i, x' i - E.totalEndowment) =
        ∑ i, (a • x i + b • x' i) - E.totalEndowment
      rw [Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.smul_sum]
      conv_rhs => rw [← one_smul ℝ E.totalEndowment, ← hab, add_smul]
      rw [smul_sub, smul_sub]
      abel)
    (fun q hq α hα => by
      have hD : ∀ i, E.demand i (α • q) = E.demand i q := fun i => by
        rw [convZ_demand_eq hX, convZ_demand_eq hX, smul_dotProduct, smul_eq_mul]
        exact proposition_3_D_2_i _ _ _ hα
      simp only [convZ, hD])
    (fun q hq z hz => by
      obtain ⟨x, hx, rfl⟩ := hz
      rw [dotProduct_sub, dotProduct_sum, ExchangeEconomy.totalEndowment, dotProduct_sum]
      simp only [hbud _ _ (hx _), sub_self])
    ⟨∑ l, E.totalEndowment l + 1, fun q hq z hz l => by
      obtain ⟨x, hx, rfl⟩ := hz
      simp only [Pi.sub_apply, Finset.sum_apply]
      have h1 : 0 ≤ ∑ i, x i l := Finset.sum_nonneg fun i _ =>
        (convDemand_subset_Icc hX i hq (hx i)).1 l
      have h2 : E.totalEndowment l ≤ ∑ k, E.totalEndowment k :=
        Finset.single_le_sum (f := fun k => E.totalEndowment k) (fun k _ => by
          rw [ExchangeEconomy.totalEndowment, Finset.sum_apply]
          exact Finset.sum_nonneg fun i _ => (hω i k).le) (Finset.mem_univ l)
      linarith⟩
    (convZ_boundary hX hc hm hω)
  exact ⟨p, hp, x, hx, sub_eq_zero.1 h0.symm⟩

/-- **Section 17.I** (MWG, pp. 628-629). Under the hypotheses of
`section_17_I_convexified_existence`, there is a price vector `p ≫ 0` at which every replica has a
near equilibrium: for every `r ≥ 1` all consumers can be given demanded bundles with per-replica
excess demand of norm at most `L·∑ᵢ diam xᵢ(p)/r` (`near_equilibrium`). -/
theorem section_17_I_near_equilibrium_exists [Nonempty ι] (hL : 0 < L)
    {E : ExchangeEconomy ι L} (hX : ∀ i, E.X i = nonnegOrthant L)
    (hc : ∀ i, ContinuousOn (E.u i) (nonnegOrthant L))
    (hm : ∀ i, UtilityStronglyMonotone (E.u i)) (hω : ∀ i, E.ω i ∈ posOrthant L) :
    ∃ p ∈ posOrthant L, ∀ r : ℕ, 0 < r →
      ∃ x : ι × Fin r → Fin L → ℝ, (∀ c, x c ∈ (replica E r).demand c p) ∧
        ‖(r : ℝ)⁻¹ • (∑ c, x c - (replica E r).totalEndowment)‖ ≤
          L * (∑ i, Metric.diam (E.demand i p)) / r := by
  obtain ⟨p, hp, x, hx, hsum⟩ := section_17_I_convexified_existence hL hX hc hm hω
  exact ⟨p, hp, fun r hr =>
    (near_equilibrium E (fun i => isBounded_demand (hX i) hp) hx hsum hr).2⟩

/-- **Section 17.I**, instance (MWG, p. 628): the economy with a nonconvex consumer
`u₁ = x₁² + x₂²` and a convex consumer `u₂ = log(1 + x₁) + log(1 + x₂)`, endowments `(1, 1)`. -/
noncomputable def cvxEconomy : ExchangeEconomy (Fin 2) 2 :=
  ExchangeEconomy.ofOrthant ![sqNormU, logU] fun _ => 1

/-- **Section 17.I**, instance of `section_17_I_convexified_existence`: `cvxEconomy` satisfies
its hypotheses, so its convexified economy has an equilibrium. -/
theorem section_17_I_convexified_instance :
    ∃ p ∈ posOrthant 2, ∃ x : Fin 2 → Fin 2 → ℝ,
      (∀ i, x i ∈ convexHull ℝ (cvxEconomy.demand i p)) ∧
        ∑ i, x i = cvxEconomy.totalEndowment := by
  refine section_17_I_convexified_existence two_pos (fun _ => rfl) (fun i => ?_) (fun i => ?_)
    (fun _ _ => one_pos)
  · fin_cases i
    · exact (by unfold sqNormU; fun_prop : Continuous sqNormU).continuousOn
    · exact logU_continuousOn
  · fin_cases i
    · exact sqNormU_stronglyMonotone
    · exact logU_stronglyMonotone

end MWG.PositiveEquilibriumTheory
