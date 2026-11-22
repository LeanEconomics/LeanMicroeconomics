/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPositiveEquilibriumTheory.ShapleyFolkman
import MWGWelfareTheorems.Replica

/-!
# Large economies and nonconvexities (MWG Section 17.I, pp. 627-630)

* **Replica economies** (p. 627): `replica E r` has `r` consumers of each type `i`, consumer
  `(i, k)` with the characteristics of type `i`; `eqmPriceSet` is the set `E(r)` of equilibrium
  price vectors of footnote 71. Any equilibrium of the basic economy is one of every replica
  (`replica_isDemandEqm`), `E(1) ⊆ E(r)` (`footnote_71_one`) and `E(r') ⊆ E(mr')`
  (`footnote_71_mul`).
* **Figure 17.I.1** (p. 627): a two-good economy with a nonconvex type (`u = x₁² + x₂²`,
  Chapter 16's `sqNormU`) and a convex type (`u = x₁x₂`), endowments `(1, 1)`. For `r ≥ 1`,
  `E(r)` is empty for odd `r` and is the ray `p₁ = p₂ > 0` for even `r` (`figure_17_I_1`); so no
  equilibrium with one consumer of each type, one with two (`figure_17_I_1_one_two`). The
  converse of `E(1) ⊆ E(r)` fails and neither direction of inclusion holds in general between
  `E(r')` and `E(r'')` (`footnote_71_converse_fails`, `footnote_71_no_inclusion`).
* **The convexifying effect** (p. 628): the per-replica excess demand `z_{ir}(p)` lies in, and
  converges in the Hausdorff distance to, `conv zᵢ(p)` (`section_17_I_convexification`), by the
  Shapley-Folkman theorem.
* **Near equilibrium** (pp. 628-629, footnote 74, where the book gives no definition): if `p`
  is an equilibrium price of the convexified economy (`∑ᵢ x̄ᵢ = ω̄` with `x̄ᵢ ∈ conv xᵢ(p)`),
  then in every `r`-replica (i) markets clear exactly with all but at most `L` of the `Ir`
  consumers at a demanded bundle (the others at convex combinations of demanded bundles), and
  (ii) with every consumer at a demanded bundle, the per-replica excess demand has norm at most
  `L·∑ᵢ diam xᵢ(p) / r` (`near_equilibrium`). Instance: Figure 17.I.1 at `p = (1, 1)`
  (`figure_17_I_1_near_equilibrium`).
-/

namespace MWG.PositiveEquilibriumTheory

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.GeneralEquilibriumExamples MWG.WelfareTheorems
open Module Filter Topology

variable {ι : Type*} {L : ℕ}

/-! ### Replica economies -/

/-- **Section 17.I** (MWG, p. 627). The `r`-replica of an exchange economy whose consumers are
the `I` types: `r` consumers of each type, consumer `(i, k)` having the consumption set,
utility and endowment of type `i`. -/
def replica (E : ExchangeEconomy ι L) (r : ℕ) : ExchangeEconomy (ι × Fin r) L where
  X c := E.X c.1
  u c := E.u c.1
  ω c := E.ω c.1

/-- In the replica, consumer `(i, k)` has the demand of type `i`. -/
theorem replica_demand (E : ExchangeEconomy ι L) (r : ℕ) (c : ι × Fin r) (p : Fin L → ℝ) :
    (replica E r).demand c p = E.demand c.1 p := rfl

/-- **Footnote 71** (MWG, p. 628). The set `E(r)` of equilibrium price vectors (Definition
15.B.1 in demand form: every consumer demands his bundle and markets clear). -/
def eqmPriceSet {κ : Type*} [Fintype κ] (E : ExchangeEconomy κ L) : Set (Fin L → ℝ) :=
  {p | ∃ x, E.IsDemandEqm p x}

variable [Fintype ι]

/-- The total endowment of the `r`-replica is `r ω̄`. -/
theorem replica_totalEndowment (E : ExchangeEconomy ι L) (r : ℕ) :
    (replica E r).totalEndowment = r • E.totalEndowment := by
  simp only [ExchangeEconomy.totalEndowment, replica, Fintype.sum_prod_type, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, Finset.smul_sum]

/-- **Section 17.I** (MWG, p. 627). Any equilibrium of the basic economy, with every consumer of
type `i` consuming `xᵢ`, is an equilibrium of the `r`-replica economy. -/
theorem replica_isDemandEqm {E : ExchangeEconomy ι L} {p : Fin L → ℝ} {x : ι → Fin L → ℝ}
    (h : E.IsDemandEqm p x) (r : ℕ) : (replica E r).IsDemandEqm p (fun c => x c.1) := by
  refine ⟨⟨fun c => h.1.1 c.1, ?_⟩, fun c => h.2 c.1⟩
  rw [replica_totalEndowment, ← h.1.2, Fintype.sum_prod_type, Finset.smul_sum]
  simp

/-- An equilibrium of the `1`-replica is an equilibrium of the basic economy. -/
theorem isDemandEqm_of_replica_one {E : ExchangeEconomy ι L} {p : Fin L → ℝ}
    {x : ι × Fin 1 → Fin L → ℝ} (h : (replica E 1).IsDemandEqm p x) :
    E.IsDemandEqm p (fun i => x (i, 0)) := by
  refine ⟨⟨fun i => h.1.1 (i, 0), ?_⟩, fun i => h.2 (i, 0)⟩
  have h2 := h.1.2
  rw [replica_totalEndowment, one_smul, Fintype.sum_prod_type] at h2
  simpa using h2

/-- **Footnote 71** (MWG, p. 628). `E(r') ⊆ E(mr')`: an equilibrium of the `r'`-replica is
repeated `m` times. -/
theorem replica_mul_isDemandEqm {E : ExchangeEconomy ι L} {r : ℕ} {p : Fin L → ℝ}
    {x : ι × Fin r → Fin L → ℝ} (h : (replica E r).IsDemandEqm p x) (m : ℕ) :
    (replica E (m * r)).IsDemandEqm p (fun c => x (c.1, (finProdFinEquiv.symm c.2).2)) := by
  refine ⟨⟨fun c => h.1.1 (c.1, (finProdFinEquiv.symm c.2).2), ?_⟩,
    fun c => h.2 (c.1, (finProdFinEquiv.symm c.2).2)⟩
  have h2 := h.1.2
  rw [replica_totalEndowment] at h2 ⊢
  rw [mul_smul, ← h2, Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
  simp

/-- **Section 17.I and footnote 71** (MWG, pp. 627-628). `E(1) ⊆ E(r)`. -/
theorem footnote_71_one (E : ExchangeEconomy ι L) (r : ℕ) :
    eqmPriceSet (replica E 1) ⊆ eqmPriceSet (replica E r) := by
  rintro p ⟨x, hx⟩
  exact ⟨_, replica_isDemandEqm (isDemandEqm_of_replica_one hx) r⟩

/-- **Footnote 71** (MWG, p. 628). `E(r') ⊆ E(r'')` when `r'' = mr'`. -/
theorem footnote_71_mul (E : ExchangeEconomy ι L) (r m : ℕ) :
    eqmPriceSet (replica E r) ⊆ eqmPriceSet (replica E (m * r)) := by
  rintro p ⟨x, hx⟩
  exact ⟨_, replica_mul_isDemandEqm hx m⟩

/-! ### Excess demand sets and their convexification -/

/-- **Section 17.I** (MWG, p. 628). Type `i`'s (possibly set-valued) excess demand
`zᵢ(p) = xᵢ(p, p·ωᵢ) - ωᵢ`. -/
def excessDemandSet (E : ExchangeEconomy ι L) (i : ι) (p : Fin L → ℝ) : Set (Fin L → ℝ) :=
  (fun x => x - E.ω i) '' E.demand i p

/-- **Section 17.I** (MWG, p. 628). The per-replica excess demand of type `i` with `r` replicas,
`z_{ir}(p) = (1/r)(zᵢ(p) + ⋯ + zᵢ(p))`. -/
def perReplicaExcessDemand (E : ExchangeEconomy ι L) (i : ι) (p : Fin L → ℝ) (r : ℕ) :
    Set (Fin L → ℝ) :=
  perReplicaSet (excessDemandSet E i p) r

omit [Fintype ι] in
/-- At `p ≫ 0` and `Xᵢ = ℝ^L₊`, demand lies in the box `0 ≤ x ≤ (p·ωᵢ/pₗ)ₗ`. -/
theorem demand_subset_Icc {E : ExchangeEconomy ι L} {i : ι} (hX : E.X i = nonnegOrthant L)
    {p : Fin L → ℝ} (hp : p ∈ posOrthant L) :
    E.demand i p ⊆ Set.Icc 0 (fun l => (p ⬝ᵥ E.ω i) / p l) := by
  intro x hx
  have hx0 : ∀ l, 0 ≤ x l := by
    have := hx.1.1
    rw [hX] at this
    exact this
  refine ⟨fun l => hx0 l, fun l => ?_⟩
  rw [le_div_iff₀ (hp l), mul_comm]
  calc p l * x l ≤ p ⬝ᵥ x :=
        Finset.single_le_sum (f := fun k => p k * x k)
          (fun k _ => mul_nonneg (hp k).le (hx0 k)) (Finset.mem_univ l)
    _ ≤ p ⬝ᵥ E.ω i := hx.1.2

omit [Fintype ι] in
/-- At `p ≫ 0` and `Xᵢ = ℝ^L₊`, demand is bounded. -/
theorem isBounded_demand {E : ExchangeEconomy ι L} {i : ι} (hX : E.X i = nonnegOrthant L)
    {p : Fin L → ℝ} (hp : p ∈ posOrthant L) : Bornology.IsBounded (E.demand i p) :=
  (Metric.isBounded_Icc _ _).subset (demand_subset_Icc hX hp)

omit [Fintype ι] in
/-- **Section 17.I** (MWG, p. 628). At `p ≫ 0`, with `Xᵢ = ℝ^L₊` and `uᵢ` continuous on `ℝ^L₊`,
the demand set (and so `zᵢ(p)`) is compact. -/
theorem isCompact_demand {E : ExchangeEconomy ι L} {i : ι} (hX : E.X i = nonnegOrthant L)
    (hc : ContinuousOn (E.u i) (nonnegOrthant L)) {p : Fin L → ℝ} (hp : p ∈ posOrthant L) :
    IsCompact (E.demand i p) := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ (isBounded_demand hX hp)
  set B := budgetSetOn (nonnegOrthant L) p (p ⬝ᵥ E.ω i) with hB
  have hO : IsClosed (nonnegOrthant L) := by
    have : nonnegOrthant L = ⋂ l, {x : Fin L → ℝ | 0 ≤ x l} := by
      ext x
      simp [nonnegOrthant]
    rw [this]
    exact isClosed_iInter fun l => isClosed_le continuous_const (continuous_apply l)
  have hBc : IsClosed B :=
    hO.inter (isClosed_le (by fun_prop : Continuous fun x : Fin L → ℝ => p ⬝ᵥ x)
      continuous_const)
  have hBO : B ⊆ nonnegOrthant L := fun x hx => hx.1
  have heq : E.demand i p = B ∩ ⋂ y ∈ B, B ∩ E.u i ⁻¹' Set.Ici (E.u i y) := by
    ext x
    simp only [ExchangeEconomy.demand, walrasianDemandOn, hX, Set.mem_inter_iff,
      Set.mem_iInter, Set.mem_preimage, Set.mem_Ici]
    constructor
    · rintro ⟨hx, hmax⟩
      exact ⟨hx, fun y hy => ⟨hx, hmax y hy⟩⟩
    · rintro ⟨hx, hmax⟩
      exact ⟨hx, fun y hy => (hmax y hy).2⟩
  rw [heq]
  exact hBc.inter (isClosed_biInter fun y _ =>
    (hc.mono hBO).preimage_isClosed_of_isClosed hBc isClosed_Ici)

omit [Fintype ι] in
/-- At `p ≫ 0` and `Xᵢ = ℝ^L₊`, the excess demand set is bounded. -/
theorem isBounded_excessDemandSet {E : ExchangeEconomy ι L} {i : ι}
    (hX : E.X i = nonnegOrthant L) {p : Fin L → ℝ} (hp : p ∈ posOrthant L) :
    Bornology.IsBounded (excessDemandSet E i p) := by
  refine (Metric.isBounded_Icc (0 - E.ω i) ((fun l => (p ⬝ᵥ E.ω i) / p l) - E.ω i)).subset ?_
  rintro _ ⟨x, hx, rfl⟩
  have h := demand_subset_Icc hX hp hx
  exact ⟨sub_le_sub_right h.1 _, sub_le_sub_right h.2 _⟩

omit [Fintype ι] in
/-- **Section 17.I** (MWG, p. 628). For any `p ≫ 0` (`Xᵢ = ℝ^L₊`) and whatever the number of
commodities: `z_{ir}(p) ⊆ conv zᵢ(p)` for `r ≥ 1`, and as `r → ∞` the per-replica excess demand
`z_{ir}(p)` converges as a set (Hausdorff distance) to `conv zᵢ(p)`: in the limit
`z_{i∞}(p) = conv zᵢ(p)`. -/
theorem section_17_I_convexification {E : ExchangeEconomy ι L} {i : ι}
    (hX : E.X i = nonnegOrthant L) {p : Fin L → ℝ} (hp : p ∈ posOrthant L) :
    (∀ r, 0 < r → perReplicaExcessDemand E i p r ⊆ convexHull ℝ (excessDemandSet E i p)) ∧
    Tendsto (fun r => Metric.hausdorffDist (perReplicaExcessDemand E i p r)
      (convexHull ℝ (excessDemandSet E i p))) atTop (𝓝 0) :=
  ⟨fun _ hr => perReplicaSet_subset_convexHull _ hr,
    tendsto_hausdorffDist_perReplica (isBounded_excessDemandSet hX hp)⟩

/-! ### Near equilibrium -/

open Classical in
/-- **Section 17.I** (MWG, pp. 628-629; footnote 74). Near equilibria of large replica
economies. Let `p` be an equilibrium price vector of the convexified economy: bundles
`x̄ᵢ ∈ conv xᵢ(p)` with `∑ᵢ x̄ᵢ = ω̄` (demand sets bounded). Then for every `r ≥ 1`:
(i) there is an allocation of the `r`-replica with exact market clearing in which every
consumer's bundle is in the convex hull of his demand, and all but at most `L` consumers (out of
`Ir`, whatever `r`) consume a demanded bundle; (ii) there is an assignment of demanded bundles
to all consumers whose per-replica excess demand has norm at most `L·∑ᵢ diam xᵢ(p) / r`. -/
theorem near_equilibrium (E : ExchangeEconomy ι L) {p : Fin L → ℝ}
    (hb : ∀ i, Bornology.IsBounded (E.demand i p)) {xbar : ι → Fin L → ℝ}
    (hxbar : ∀ i, xbar i ∈ convexHull ℝ (E.demand i p))
    (hclear : ∑ i, xbar i = E.totalEndowment) {r : ℕ} (hr : 0 < r) :
    (∃ x : ι × Fin r → Fin L → ℝ, (∀ c, x c ∈ convexHull ℝ (E.demand c.1 p)) ∧
      ∑ c, x c = (replica E r).totalEndowment ∧
      (Finset.univ.filter fun c => x c ∉ E.demand c.1 p).card ≤ L) ∧
    ∃ x : ι × Fin r → Fin L → ℝ, (∀ c, x c ∈ (replica E r).demand c p) ∧
      ‖(r : ℝ)⁻¹ • (∑ c, x c - (replica E r).totalEndowment)‖ ≤
        L * (∑ i, Metric.diam (E.demand i p)) / r := by
  obtain ⟨y, hy, hsum, hcard⟩ := shapley_folkman (fun c : ι × Fin r => E.demand c.1 p)
    (fun c => xbar c.1) fun c => hxbar c.1
  rw [Module.finrank_fin_fun] at hcard
  have htot : ∑ c : ι × Fin r, xbar c.1 = (replica E r).totalEndowment := by
    rw [replica_totalEndowment, ← hclear, Fintype.sum_prod_type, Finset.smul_sum]
    simp
  refine ⟨⟨y, hy, hsum.trans htot, hcard⟩, ?_⟩
  have hne : ∀ i, (E.demand i p).Nonempty := fun i => by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have := hxbar i
    rw [h, convexHull_empty] at this
    exact this
  choose d hd using hne
  set x : ι × Fin r → Fin L → ℝ := fun c => if y c ∈ E.demand c.1 p then y c else d c.1
    with hxdef
  have hxd : ∀ c, x c ∈ E.demand c.1 p := fun c => by
    by_cases h : y c ∈ E.demand c.1 p
    · simp only [hxdef, h, ↓reduceIte]
    · simp only [hxdef, h, ↓reduceIte, hd]
  refine ⟨x, hxd, ?_⟩
  set D : ℝ := ∑ i, Metric.diam (E.demand i p) with hDdef
  have hD : ∀ i, Metric.diam (E.demand i p) ≤ D := fun i =>
    Finset.single_le_sum (f := fun j => Metric.diam (E.demand j p))
      (fun j _ => Metric.diam_nonneg) (Finset.mem_univ i)
  have hD0 : 0 ≤ D := Finset.sum_nonneg fun j _ => Metric.diam_nonneg
  have hterm : ∀ c, ‖x c - y c‖ ≤ if y c ∉ E.demand c.1 p then D else 0 := by
    intro c
    by_cases h : y c ∈ E.demand c.1 p
    · simp [hxdef, h]
    · simp only [hxdef, h, ↓reduceIte, not_false_eq_true]
      rw [← dist_eq_norm]
      calc dist (d c.1) (y c) ≤ Metric.diam (convexHull ℝ (E.demand c.1 p)) :=
            Metric.dist_le_diam_of_mem (isBounded_convexHull.2 (hb c.1))
              (subset_convexHull ℝ _ (hd c.1)) (hy c)
        _ = Metric.diam (E.demand c.1 p) := convexHull_diam _
        _ ≤ D := hD c.1
  have heq : ∑ c, x c - (replica E r).totalEndowment = ∑ c, (x c - y c) := by
    rw [Finset.sum_sub_distrib, ← htot, ← hsum]
  have hcard' : ((Finset.univ.filter fun c => y c ∉ E.demand c.1 p).card : ℝ) ≤ L := by
    exact_mod_cast hcard
  have hrpos : (0 : ℝ) < r := Nat.cast_pos.2 hr
  calc ‖(r : ℝ)⁻¹ • (∑ c, x c - (replica E r).totalEndowment)‖
        = (r : ℝ)⁻¹ * ‖∑ c, (x c - y c)‖ := by
        rw [heq, norm_smul, Real.norm_eq_abs, abs_inv, Nat.abs_cast]
    _ ≤ (r : ℝ)⁻¹ * ∑ c, (if y c ∉ E.demand c.1 p then D else 0) := by
        gcongr
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => hterm c)
    _ = (r : ℝ)⁻¹ * ((Finset.univ.filter fun c => y c ∉ E.demand c.1 p).card * D) := by
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    _ ≤ (r : ℝ)⁻¹ * (L * D) := by gcongr
    _ = L * D / r := by ring

/-! ### Figure 17.I.1 -/

/-- **Figure 17.I.1** (MWG, p. 627). The utility `u(x) = x₁x₂` of the convex type. -/
def cdU (x : Fin 2 → ℝ) : ℝ := x 0 * x 1

/-- **Figure 17.I.1** (MWG, p. 627). The economy: two goods, type `1` (index `0`) with the
nonconvex preference `u = x₁² + x₂²` (`sqNormU`), type `2` (index `1`) with the convex
preference `u = x₁x₂`, consumption sets `ℝ²₊`, endowments `ωᵢ = (1, 1)`. -/
noncomputable def fig17I1Economy : ExchangeEconomy (Fin 2) 2 :=
  ExchangeEconomy.ofOrthant ![sqNormU, cdU] fun _ => 1

/-- Demand in the economy of Figure 17.I.1, coordinatewise. -/
theorem fig17I1_demand_iff {i : Fin 2} {p x : Fin 2 → ℝ} :
    x ∈ fig17I1Economy.demand i p ↔
      ((0 ≤ x 0 ∧ 0 ≤ x 1) ∧ p 0 * x 0 + p 1 * x 1 ≤ p 0 + p 1) ∧
        ∀ y : Fin 2 → ℝ, (0 ≤ y 0 ∧ 0 ≤ y 1) → p 0 * y 0 + p 1 * y 1 ≤ p 0 + p 1 →
          ![sqNormU, cdU] i y ≤ ![sqNormU, cdU] i x := by
  have hm : ∀ z : Fin 2 → ℝ, z ∈ nonnegOrthant 2 ↔ (0 ≤ z 0 ∧ 0 ≤ z 1) := fun z => by
    simp [nonnegOrthant, Fin.forall_fin_two]
  have hd : ∀ z : Fin 2 → ℝ, p ⬝ᵥ z = p 0 * z 0 + p 1 * z 1 := fun z => by
    simp [dotProduct, Fin.sum_univ_two]
  unfold ExchangeEconomy.demand walrasianDemandOn budgetSetOn
  simp only [fig17I1Economy, ExchangeEconomy.ofOrthant, Set.mem_ofPred_eq, hm, hd, Pi.one_apply,
    mul_one, and_imp]

/-- In Figure 17.I.1 the convex consumer has a demand only at `p ≫ 0`. -/
theorem fig17I1_pos {p x : Fin 2 → ℝ} (hx : x ∈ fig17I1Economy.demand 1 p) :
    0 < p 0 ∧ 0 < p 1 := by
  rw [fig17I1_demand_iff] at hx
  obtain ⟨-, hmax⟩ := hx
  set c : ℝ := |cdU x| + 1 with hc
  have hc0 : 0 ≤ c := by positivity
  have hcx : cdU x < 1 + c := by
    have := le_abs_self (cdU x)
    linarith
  constructor
  · by_contra h
    push Not at h
    have := hmax ![1 + c, 1] (by change 0 ≤ 1 + c ∧ (0 : ℝ) ≤ 1; constructor <;> linarith)
      (by change p 0 * (1 + c) + p 1 * 1 ≤ p 0 + p 1; nlinarith)
    change (1 + c) * 1 ≤ x 0 * x 1 at this
    simp only [cdU] at hcx
    linarith
  · by_contra h
    push Not at h
    have := hmax ![1, 1 + c] (by change (0 : ℝ) ≤ 1 ∧ 0 ≤ 1 + c; constructor <;> linarith)
      (by change p 0 * 1 + p 1 * (1 + c) ≤ p 0 + p 1; nlinarith)
    change 1 * (1 + c) ≤ x 0 * x 1 at this
    simp only [cdU] at hcx
    linarith

/-- In Figure 17.I.1, at `p ≫ 0` the convex consumer spends half his wealth `p₁ + p₂` on each
good. -/
theorem fig17I1_cd {p x : Fin 2 → ℝ} (hp0 : 0 < p 0) (hp1 : 0 < p 1)
    (hx : x ∈ fig17I1Economy.demand 1 p) :
    p 0 * x 0 = (p 0 + p 1) / 2 ∧ p 1 * x 1 = (p 0 + p 1) / 2 := by
  rw [fig17I1_demand_iff] at hx
  obtain ⟨⟨⟨hx0, hx1⟩, hbud⟩, hmax⟩ := hx
  set w := p 0 + p 1 with hw
  have hcost : p 0 * (w / (2 * p 0)) + p 1 * (w / (2 * p 1)) = w := by
    field_simp
    ring
  have hy := hmax ![w / (2 * p 0), w / (2 * p 1)]
    (by change 0 ≤ w / (2 * p 0) ∧ 0 ≤ w / (2 * p 1); constructor <;> positivity)
    (by change p 0 * (w / (2 * p 0)) + p 1 * (w / (2 * p 1)) ≤ p 0 + p 1; rw [hcost])
  change w / (2 * p 0) * (w / (2 * p 1)) ≤ x 0 * x 1 at hy
  have hprod : w ^ 2 ≤ 4 * (p 0 * x 0) * (p 1 * x 1) := by
    have h2 : w / (2 * p 0) * (w / (2 * p 1)) = w ^ 2 / (4 * (p 0 * p 1)) := by
      field_simp
      ring
    rw [h2, div_le_iff₀ (by positivity)] at hy
    linarith
  have ha := mul_nonneg hp0.le hx0
  have hb := mul_nonneg hp1.le hx1
  have hsq : (p 0 * x 0 - p 1 * x 1) ^ 2 ≤ 0 := by nlinarith
  have heq : p 0 * x 0 = p 1 * x 1 := by nlinarith [sq_nonneg (p 0 * x 0 - p 1 * x 1)]
  constructor <;> nlinarith

/-- In Figure 17.I.1, at `0 < p₁ ≤ p₂` the nonconvex consumer buys `(p₁ + p₂)/p₁` units in
total, of only one good, and only good `1` if `p₁ < p₂`. -/
theorem fig17I1_sq_le {p x : Fin 2 → ℝ} (hp0 : 0 < p 0) (hle : p 0 ≤ p 1)
    (hx : x ∈ fig17I1Economy.demand 0 p) :
    x 0 + x 1 = (p 0 + p 1) / p 0 ∧ x 0 * x 1 = 0 ∧ (p 0 < p 1 → x 1 = 0) := by
  rw [fig17I1_demand_iff] at hx
  obtain ⟨⟨⟨hx0, hx1⟩, hbud⟩, hmax⟩ := hx
  set M := (p 0 + p 1) / p 0 with hM
  have hMp : p 0 * M = p 0 + p 1 := by rw [hM]; field_simp
  have hM0 : 0 ≤ M := by rw [hM]; exact div_nonneg (by linarith) hp0.le
  have hy := hmax ![M, 0] (by change 0 ≤ M ∧ (0 : ℝ) ≤ 0; exact ⟨hM0, le_rfl⟩)
    (by change p 0 * M + p 1 * 0 ≤ p 0 + p 1; linarith)
  change M ^ 2 + 0 ^ 2 ≤ x 0 ^ 2 + x 1 ^ 2 at hy
  have hsum : x 0 + x 1 ≤ M := by
    have : p 0 * (x 0 + x 1) ≤ p 0 * M := by nlinarith
    exact le_of_mul_le_mul_left this hp0
  have hsq : (x 0 + x 1) ^ 2 ≤ M ^ 2 := by nlinarith
  have hprod : x 0 * x 1 = 0 := by nlinarith [mul_nonneg hx0 hx1]
  have htot : x 0 + x 1 = M := by nlinarith
  refine ⟨htot, hprod, fun hlt => ?_⟩
  by_contra h1
  have hpos : 0 < x 1 := lt_of_le_of_ne hx1 (Ne.symm h1)
  nlinarith

/-- In Figure 17.I.1, at `0 < p₂ ≤ p₁` the nonconvex consumer buys `(p₁ + p₂)/p₂` units in
total, of only one good, and only good `2` if `p₂ < p₁`. -/
theorem fig17I1_sq_ge {p x : Fin 2 → ℝ} (hp1 : 0 < p 1) (hle : p 1 ≤ p 0)
    (hx : x ∈ fig17I1Economy.demand 0 p) :
    x 0 + x 1 = (p 0 + p 1) / p 1 ∧ x 0 * x 1 = 0 ∧ (p 1 < p 0 → x 0 = 0) := by
  rw [fig17I1_demand_iff] at hx
  obtain ⟨⟨⟨hx0, hx1⟩, hbud⟩, hmax⟩ := hx
  set M := (p 0 + p 1) / p 1 with hM
  have hMp : p 1 * M = p 0 + p 1 := by rw [hM]; field_simp
  have hM0 : 0 ≤ M := by rw [hM]; exact div_nonneg (by linarith) hp1.le
  have hy := hmax ![0, M] (by change (0 : ℝ) ≤ 0 ∧ 0 ≤ M; exact ⟨le_rfl, hM0⟩)
    (by change p 0 * 0 + p 1 * M ≤ p 0 + p 1; linarith)
  change 0 ^ 2 + M ^ 2 ≤ x 0 ^ 2 + x 1 ^ 2 at hy
  have hsum : x 0 + x 1 ≤ M := by
    have : p 1 * (x 0 + x 1) ≤ p 1 * M := by nlinarith
    exact le_of_mul_le_mul_left this hp1
  have hsq : (x 0 + x 1) ^ 2 ≤ M ^ 2 := by nlinarith
  have hprod : x 0 * x 1 = 0 := by nlinarith [mul_nonneg hx0 hx1]
  have htot : x 0 + x 1 = M := by nlinarith
  refine ⟨htot, hprod, fun hlt => ?_⟩
  by_contra h0
  have hpos : 0 < x 0 := lt_of_le_of_ne hx0 (Ne.symm h0)
  nlinarith

/-- A sum of `r` terms `±1` vanishes only if `r` is even. -/
theorem even_of_sum_pm_one {r : ℕ} (f : Fin r → ℝ) (hf : ∀ k, f k = 1 ∨ f k = -1)
    (hs : ∑ k, f k = 0) : Even r := by
  classical
  set c := (Finset.univ.filter fun k => f k = -1).card with hc
  set c' := (Finset.univ.filter fun k => ¬ f k = -1).card with hc'
  have hcc : c + c' = r := by
    rw [hc, hc', Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_fin]
  have hsum : ∑ k, f k = ∑ k, (if f k = -1 then (-1 : ℝ) else 1) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rcases hf k with h | h
    · rw [h]; norm_num
    · simp [h]
  rw [hsum, Finset.sum_ite, Finset.sum_const, Finset.sum_const, ← hc, ← hc'] at hs
  simp only [nsmul_eq_mul, mul_neg, mul_one] at hs
  have : (c' : ℝ) = c := by linarith
  have h2 : c' = c := by exact_mod_cast this
  exact ⟨c, by omega⟩

/-- The total endowment of the economy of Figure 17.I.1 is `(2, 2)`. -/
theorem fig17I1_totalEndowment (l : Fin 2) : fig17I1Economy.totalEndowment l = 2 := by
  simp [ExchangeEconomy.totalEndowment, fig17I1Economy, ExchangeEconomy.ofOrthant]

/-- At `p₁ = p₂ > 0` the nonconvex consumer demands `(2, 0)`. -/
theorem fig17I1_mem_20 {q : ℝ} (hq : 0 < q) : ![2, 0] ∈ fig17I1Economy.demand 0 ![q, q] := by
  rw [fig17I1_demand_iff]
  refine ⟨⟨⟨by norm_num, by norm_num⟩, by change q * 2 + q * 0 ≤ q + q; linarith⟩,
    fun y ⟨hy0, hy1⟩ hb => ?_⟩
  change q * y 0 + q * y 1 ≤ q + q at hb
  change y 0 ^ 2 + y 1 ^ 2 ≤ (2 : ℝ) ^ 2 + 0 ^ 2
  have : y 0 + y 1 ≤ 2 := by nlinarith
  nlinarith

/-- At `p₁ = p₂ > 0` the nonconvex consumer demands `(0, 2)`. -/
theorem fig17I1_mem_02 {q : ℝ} (hq : 0 < q) : ![0, 2] ∈ fig17I1Economy.demand 0 ![q, q] := by
  rw [fig17I1_demand_iff]
  refine ⟨⟨⟨by norm_num, by norm_num⟩, by change q * 0 + q * 2 ≤ q + q; linarith⟩,
    fun y ⟨hy0, hy1⟩ hb => ?_⟩
  change q * y 0 + q * y 1 ≤ q + q at hb
  change y 0 ^ 2 + y 1 ^ 2 ≤ (0 : ℝ) ^ 2 + 2 ^ 2
  have : y 0 + y 1 ≤ 2 := by nlinarith
  nlinarith

/-- At `p₁ = p₂ > 0` the convex consumer demands `(1, 1)`. -/
theorem fig17I1_mem_11 {q : ℝ} (hq : 0 < q) : ![1, 1] ∈ fig17I1Economy.demand 1 ![q, q] := by
  rw [fig17I1_demand_iff]
  refine ⟨⟨⟨by norm_num, by norm_num⟩, by change q * 1 + q * 1 ≤ q + q; linarith⟩,
    fun y ⟨hy0, hy1⟩ hb => ?_⟩
  change q * y 0 + q * y 1 ≤ q + q at hb
  change y 0 * y 1 ≤ 1 * 1
  have : y 0 + y 1 ≤ 2 := by nlinarith
  nlinarith [sq_nonneg (y 0 - y 1)]

/-- **Figure 17.I.1** (MWG, pp. 627-628). For `r ≥ 1`, the equilibrium price vectors of the
`r`-replica of the economy of Figure 17.I.1 are: none if `r` is odd, and the ray `p₁ = p₂ > 0` if
`r` is even (half of the nonconvex consumers at `x₁ = (2, 0)`, half at `x'₁ = (0, 2)`, the convex
consumers at their endowment). When we replicate the economy, new equilibria may emerge. -/
theorem figure_17_I_1 {r : ℕ} (hr : 0 < r) :
    eqmPriceSet (replica fig17I1Economy r) = {p | Even r ∧ 0 < p 0 ∧ p 0 = p 1} := by
  ext p
  constructor
  · rintro ⟨x, hbox, hd⟩
    have hdem : ∀ c, x c ∈ fig17I1Economy.demand c.1 p := hd
    obtain ⟨hp0, hp1⟩ := fig17I1_pos (hdem (1, ⟨0, hr⟩))
    have hcl : ∀ l, ∑ k, x (0, k) l + ∑ k, x (1, k) l = r * 2 := by
      intro l
      have h := congrFun hbox.2 l
      rw [Finset.sum_apply, Fintype.sum_prod_type, Fin.sum_univ_two, replica_totalEndowment,
        Pi.smul_apply, fig17I1_totalEndowment, nsmul_eq_mul] at h
      simpa [Finset.sum_apply] using h
    have hrpos : (0 : ℝ) < r := Nat.cast_pos.2 hr
    have hcd : ∀ k, p 0 * x (1, k) 0 = (p 0 + p 1) / 2 ∧ p 1 * x (1, k) 1 = (p 0 + p 1) / 2 :=
      fun k => fig17I1_cd hp0 hp1 (hdem (1, k))
    rcases lt_trichotomy (p 0) (p 1) with h | h | h
    · exfalso
      have h0 : ∀ k, x (0, k) 0 = (p 0 + p 1) / p 0 := fun k => by
        obtain ⟨hs, -, hz⟩ := fig17I1_sq_le hp0 h.le (hdem (0, k))
        rw [← hs, hz h, add_zero]
      have h1 : ∀ k, x (1, k) 0 = (p 0 + p 1) / (2 * p 0) := fun k => by
        rw [eq_div_iff (by positivity)]
        linarith [(hcd k).1]
      have hc := hcl 0
      simp only [h0, h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul] at hc
      have e1 : (p 0 + p 1) / (2 * p 0) = (p 0 + p 1) / p 0 / 2 := by
        rw [div_div, mul_comm]
      rw [e1] at hc
      have hA : (p 0 + p 1) / p 0 * 3 = 4 := by
        have : (r : ℝ) * ((p 0 + p 1) / p 0 * 3 - 4) = 0 := by
          ring_nf
          ring_nf at hc
          linarith
        rcases mul_eq_zero.1 this with h0 | h0
        · exact absurd h0 hrpos.ne'
        · linarith
      field_simp at hA
      linarith
    · refine ⟨?_, hp0, h⟩
      have hq : (p 0 + p 1) / p 0 = 2 := by rw [← h]; field_simp; ring
      have hsq : ∀ k, x (0, k) 0 + x (0, k) 1 = 2 ∧ x (0, k) 0 * x (0, k) 1 = 0 := fun k => by
        obtain ⟨hs, hpr, -⟩ := fig17I1_sq_le hp0 h.le (hdem (0, k))
        exact ⟨hs.trans hq, hpr⟩
      have h11 : ∀ k, x (1, k) 0 - x (1, k) 1 = 0 := fun k => by
        obtain ⟨ha, hb⟩ := hcd k
        rw [← h] at hb
        have : p 0 * (x (1, k) 0 - x (1, k) 1) = 0 := by linarith
        exact (mul_eq_zero.1 this).resolve_left hp0.ne'
      refine even_of_sum_pm_one (fun k => (x (0, k) 0 - x (0, k) 1) / 2) (fun k => ?_) ?_
      · obtain ⟨hs, hpr⟩ := hsq k
        rcases mul_eq_zero.1 hpr with h0 | h0
        · right
          rw [h0] at hs ⊢
          linarith
        · left
          rw [h0] at hs ⊢
          linarith
      · have h0 := hcl 0
        have h1 := hcl 1
        have hz : ∑ k, (x (1, k) 0 - x (1, k) 1) = 0 := by simp [h11]
        rw [Finset.sum_sub_distrib] at hz
        rw [← Finset.sum_div, Finset.sum_sub_distrib]
        have : ∑ k, x (0, k) 0 - ∑ k, x (0, k) 1 = 0 := by linarith
        rw [this, zero_div]
    · exfalso
      have h0 : ∀ k, x (0, k) 1 = (p 0 + p 1) / p 1 := fun k => by
        obtain ⟨hs, -, hz⟩ := fig17I1_sq_ge hp1 h.le (hdem (0, k))
        rw [← hs, hz h, zero_add]
      have h1 : ∀ k, x (1, k) 1 = (p 0 + p 1) / (2 * p 1) := fun k => by
        rw [eq_div_iff (by positivity)]
        linarith [(hcd k).2]
      have hc := hcl 1
      simp only [h0, h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul] at hc
      have e1 : (p 0 + p 1) / (2 * p 1) = (p 0 + p 1) / p 1 / 2 := by
        rw [div_div, mul_comm]
      rw [e1] at hc
      have hA : (p 0 + p 1) / p 1 * 3 = 4 := by
        have : (r : ℝ) * ((p 0 + p 1) / p 1 * 3 - 4) = 0 := by
          ring_nf
          ring_nf at hc
          linarith
        rcases mul_eq_zero.1 this with h0 | h0
        · exact absurd h0 hrpos.ne'
        · linarith
      field_simp at hA
      linarith
  · rintro ⟨⟨m, hm⟩, hp0, hpeq⟩
    have hpv : p = ![p 0, p 0] := by
      funext l
      fin_cases l
      · rfl
      · simp [hpeq]
    have hmr : m ≤ r := by omega
    set x : Fin 2 × Fin r → Fin 2 → ℝ := fun c =>
      if c.1 = 0 then (if (c.2 : ℕ) < m then ![2, 0] else ![0, 2]) else ![1, 1] with hxdef
    refine ⟨x, ⟨fun c => ?_, ?_⟩, fun c => ?_⟩
    · change x c ∈ nonnegOrthant 2
      intro l
      by_cases h1 : c.1 = 0
      · by_cases h2 : (c.2 : ℕ) < m
        · fin_cases l <;> simp [hxdef, h1, h2]
        · fin_cases l <;> simp [hxdef, h1, h2]
      · fin_cases l <;> simp [hxdef, h1]
    · have hs0 : ∑ k : Fin r, x (0, k) = m • ![2, 0] + (r - m) • ![0, 2] := by
        rw [← sum_fin_ite_lt hmr]
        simp [hxdef]
      have hs1 : ∑ k : Fin r, x (1, k) = r • ![1, 1] := by simp [hxdef]
      rw [Fintype.sum_prod_type, Fin.sum_univ_two, hs0, hs1, replica_totalEndowment]
      funext l
      have hrm : r - m = m := by omega
      rw [hrm]
      fin_cases l
      · simp only [Pi.add_apply, Pi.smul_apply, fig17I1_totalEndowment, hm]
        simp only [nsmul_eq_mul]
        push_cast
        ring
      · simp only [Pi.add_apply, Pi.smul_apply, fig17I1_totalEndowment, hm]
        simp only [nsmul_eq_mul]
        push_cast
        ring
    · change x c ∈ fig17I1Economy.demand c.1 p
      rw [hpv]
      by_cases h1 : c.1 = 0
      · by_cases h2 : (c.2 : ℕ) < m
        · simp only [hxdef, h1, h2, ↓reduceIte]
          exact fig17I1_mem_20 hp0
        · simp only [hxdef, h1, h2, ↓reduceIte]
          exact fig17I1_mem_02 hp0
      · have hc1 : c.1 = 1 := by
          rcases Fin.exists_fin_two.1 ⟨c.1, rfl⟩ with h | h
          · exact absurd h h1
          · exact h
        simp only [hxdef, h1, ↓reduceIte]
        rw [hc1]
        exact fig17I1_mem_11 hp0

/-- **Figure 17.I.1** (MWG, p. 627). "If there is only one consumer of each type, then no
equilibrium exists; but if we have two of each type, then there is an equilibrium." -/
theorem figure_17_I_1_one_two :
    eqmPriceSet (replica fig17I1Economy 1) = ∅ ∧
      (eqmPriceSet (replica fig17I1Economy 2)).Nonempty := by
  refine ⟨?_, ?_⟩
  · rw [figure_17_I_1 one_pos]
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro h
    exact absurd h (by decide)
  · rw [figure_17_I_1 two_pos]
    exact ⟨1, by decide, by norm_num, rfl⟩

/-- **Footnote 71** (MWG, p. 628). The converse of `E(1) ⊆ E(r)` need not be true:
`E(2) ⊄ E(1)` in the economy of Figure 17.I.1. -/
theorem footnote_71_converse_fails :
    ¬ eqmPriceSet (replica fig17I1Economy 2) ⊆ eqmPriceSet (replica fig17I1Economy 1) := by
  intro h
  obtain ⟨p, hp⟩ := figure_17_I_1_one_two.2
  have := h hp
  rw [figure_17_I_1_one_two.1] at this
  exact this

/-- **Footnote 71** (MWG, p. 628). For `r'' > r' > 1` not a multiple, the inclusion
`E(r') ⊆ E(r'')` can fail (`r' = 2`, `r'' = 3`), and so can `E(r'') ⊆ E(r')` (`r' = 3`,
`r'' = 4`), in the economy of Figure 17.I.1. -/
theorem footnote_71_no_inclusion :
    ¬ eqmPriceSet (replica fig17I1Economy 2) ⊆ eqmPriceSet (replica fig17I1Economy 3) ∧
      ¬ eqmPriceSet (replica fig17I1Economy 4) ⊆ eqmPriceSet (replica fig17I1Economy 3) := by
  have h1 : (1 : Fin 2 → ℝ) ∈ {p : Fin 2 → ℝ | Even 2 ∧ 0 < p 0 ∧ p 0 = p 1} :=
    ⟨by decide, by norm_num, rfl⟩
  have h2 : (1 : Fin 2 → ℝ) ∈ {p : Fin 2 → ℝ | Even 4 ∧ 0 < p 0 ∧ p 0 = p 1} :=
    ⟨by decide, by norm_num, rfl⟩
  have hodd : ¬ Even 3 := by decide
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [figure_17_I_1 two_pos, figure_17_I_1 (by norm_num : 0 < 3)] at h
    exact hodd (h h1).1
  · rw [figure_17_I_1 (by norm_num : 0 < 4), figure_17_I_1 (by norm_num : 0 < 3)] at h
    exact hodd (h h2).1

open Classical in
/-- **Figure 17.I.1 and Section 17.I** (MWG, pp. 627-629). The economy of Figure 17.I.1 has a
near equilibrium in every replica, at `p̄ = (1, 1)`: the convexified economy clears with
`x̄₁ = (1, 1) = ½(2, 0) + ½(0, 2)` and `x̄₂ = (1, 1)`, so (`near_equilibrium`) for every `r ≥ 1`
all consumers can be given demanded bundles with per-replica excess demand of norm at most
`2(diam x₁(p̄) + diam x₂(p̄))/r`, and exact clearing needs at most two consumers off their demand
sets. -/
theorem figure_17_I_1_near_equilibrium {r : ℕ} (hr : 0 < r) :
    (∃ x : Fin 2 × Fin r → Fin 2 → ℝ, (∀ c, x c ∈ convexHull ℝ (fig17I1Economy.demand c.1 1)) ∧
      ∑ c, x c = (replica fig17I1Economy r).totalEndowment ∧
      (Finset.univ.filter fun c : Fin 2 × Fin r => x c ∉ fig17I1Economy.demand c.1 1).card
        ≤ 2) ∧
    ∃ x : Fin 2 × Fin r → Fin 2 → ℝ, (∀ c, x c ∈ (replica fig17I1Economy r).demand c 1) ∧
      ‖(r : ℝ)⁻¹ • (∑ c, x c - (replica fig17I1Economy r).totalEndowment)‖ ≤
        2 * (∑ i, Metric.diam (fig17I1Economy.demand i 1)) / r := by
  have h1 : (1 : Fin 2 → ℝ) = ![1, 1] := by
    funext l
    fin_cases l <;> rfl
  have hpos : (1 : Fin 2 → ℝ) ∈ posOrthant 2 := fun _ => one_pos
  have hb : ∀ i, Bornology.IsBounded (fig17I1Economy.demand i 1) := fun i =>
    isBounded_demand rfl hpos
  have hxbar : ∀ i, (1 : Fin 2 → ℝ) ∈ convexHull ℝ (fig17I1Economy.demand i 1) := by
    intro i
    rw [h1]
    fin_cases i
    · have h20 := fig17I1_mem_20 one_pos
      have h02 := fig17I1_mem_02 one_pos
      refine segment_subset_convexHull h20 h02 ⟨1 / 2, 1 / 2, by norm_num, by norm_num,
        by norm_num, ?_⟩
      funext l
      fin_cases l <;> simp
    · exact subset_convexHull ℝ _ (fig17I1_mem_11 one_pos)
  have hclear : ∑ _i : Fin 2, (1 : Fin 2 → ℝ) = fig17I1Economy.totalEndowment := rfl
  exact_mod_cast near_equilibrium fig17I1Economy hb hxbar hclear hr

end MWG.PositiveEquilibriumTheory
