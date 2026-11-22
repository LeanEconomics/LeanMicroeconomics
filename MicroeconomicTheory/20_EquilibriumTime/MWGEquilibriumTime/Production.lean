/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGProduction.Efficiency
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Intertemporal production and efficiency (MWG Section 20.C)

MWG, Chapter 20, Section 20.C, pp. 736-743, Exercises 20.C.1-20.C.5(a) (p. 783).

Commodities are indexed by a finite type `ι` (MWG's `L` goods; `ι = Fin L`). A production
plan is a pair `y = (y_b, y_a) ∈ ℝ^L × ℝ^L` (`ProdPlan ι`), "before" and "after". A
production path is `y : ℕ → ProdPlan ι` with `y t ∈ Y`; its net input-output vector at `t` is
`y_{a,t-1} + y_{b,t}` with `y_{a,-1} = 0` (`netOutput`), and its profit at `t` for a price
sequence `p : ℕ → ι → ℝ` is `p_t · y_{bt} + p_{t+1} · y_{at}` (`periodProfit`).

* Assumptions (i)-(iv) on `Y` (`TechAssumptions`), with bridges to Chapter 5's no free lunch and
  free disposal (`noFreeLunch_iff_stack`, `freeDisposal_iff_stack`) and the remark that
  `y_a ≥ 0` makes truncation a consequence of free disposal (`truncation_of_nonneg_after`).
* Examples 20.C.1-20.C.4: `ramseySolowSet` (with `example_20_C_1`, a proved instance of
  `TechAssumptions`), `costAdjustmentSet`, `twoSectorSet`, `multiSectorSet`
  (`example_20_C_3_costAdjustment`, `example_20_C_3_ramseySolow`).
* Definitions 20.C.1-20.C.3: `IsProdPath`, `ProdEfficient`, `MyopicProfitMax`; the
  transversality condition `Transversality`.
* The rearrangement identity behind Proposition 20.C.1 and (20.D.1): `sum_value_netOutput`.
* Example 20.C.5 (storage): `example_20_C_5`.
* **Proposition 20.C.1**: `proposition_20_C_1`; efficient plans are on the boundary of `Y`
  (`prodEfficient_not_mem_interior`).
* Exercises 20.C.1 (`ownRate`), 20.C.2, 20.C.3, 20.C.4(a)-(b) and 20.C.5(a).
-/

open Filter Topology

namespace MWG.EquilibriumTime

variable {ι : Type*} [Fintype ι]

/-- A **production plan** `y = (y_b, y_a) ∈ ℝ^{2L}` (MWG, p. 737): `y.1 = y_b` is the plan for
the initial period and `y.2 = y_a` the plan for the last period. -/
abbrev ProdPlan (ι : Type*) := (ι → ℝ) × (ι → ℝ)

/-- A vector is **strictly positive** (`p ≫ 0`). -/
def StrictPos (v : ι → ℝ) : Prop := ∀ i, 0 < v i

/-- Strictly positive prices value a nonzero nonnegative vector strictly positively. -/
theorem dotProduct_pos_of_strictPos {p v : ι → ℝ} (hp : StrictPos p) (hv : 0 ≤ v)
    (hne : v ≠ 0) : 0 < p ⬝ᵥ v := by
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (funext h)
  refine Finset.sum_pos' (fun j _ => mul_nonneg (hp j).le (hv j)) ⟨i, Finset.mem_univ _, ?_⟩
  exact mul_pos (hp i) (lt_of_le_of_ne (hv i) (Ne.symm hi))

/-- **Assumptions (i)-(iv)** on the one-period technology `Y ⊆ ℝ^{2L}` (MWG, p. 737). -/
structure TechAssumptions (Y : Set (ProdPlan ι)) : Prop where
  /-- (i) `Y` is closed. -/
  isClosed : IsClosed Y
  /-- (i) `Y` is convex. -/
  convex : Convex ℝ Y
  /-- (ii) No free lunch, `Y ∩ ℝ^{2L}_+ = {0}`: the inclusion `⊇` (inaction is possible). -/
  zero_mem : (0 : ProdPlan ι) ∈ Y
  /-- (ii) No free lunch, `Y ∩ ℝ^{2L}_+ = {0}`: the inclusion `⊆`. -/
  noFreeLunch : ∀ y ∈ Y, 0 ≤ y → y = 0
  /-- (iii) Free disposal: `Y - ℝ^{2L}_+ ⊆ Y`. -/
  freeDisposal : ∀ y ∈ Y, ∀ y', y' ≤ y → y' ∈ Y
  /-- (iv) Possibility of truncation: `(y_b, y_a) ∈ Y` implies `(y_b, 0) ∈ Y`. -/
  truncation : ∀ y ∈ Y, (y.1, 0) ∈ Y

omit [Fintype ι] in
/-- **Remark on (iv)** (MWG, p. 737): when `y_a ≥ 0` for every `y ∈ Y`, truncation follows from
free disposal. -/
theorem truncation_of_nonneg_after {Y : Set (ProdPlan ι)}
    (hfd : ∀ y ∈ Y, ∀ y', y' ≤ y → y' ∈ Y) (hpos : ∀ y ∈ Y, 0 ≤ y.2) :
    ∀ y ∈ Y, (y.1, 0) ∈ Y :=
  fun y hy => hfd y hy _ ⟨le_rfl, hpos y hy⟩

/-! ### Bridge to Chapter 5 -/

/-- Stacking a plan `(y_b, y_a)` into one vector of `ℝ^{L+L}` (MWG, p. 737: `Y ⊂ ℝ^{2L}`). -/
def stackPlan {L : ℕ} (y : ProdPlan (Fin L)) : Fin (L + L) → ℝ := Fin.append y.1 y.2

theorem stackPlan_le_iff {L : ℕ} (y z : ProdPlan (Fin L)) :
    stackPlan y ≤ stackPlan z ↔ y ≤ z := by
  constructor
  · intro h
    refine ⟨fun i => ?_, fun i => ?_⟩
    · have := h (Fin.castAdd L i)
      simpa [stackPlan, Fin.append_left] using this
    · have := h (Fin.natAdd L i)
      simp only [stackPlan, Fin.append_right] at this
      exact this
  · rintro ⟨h1, h2⟩ i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa [stackPlan, Fin.append_left] using h1 j
    · simp only [stackPlan, Fin.append_right]
      exact h2 j

theorem stackPlan_zero {L : ℕ} : stackPlan (0 : ProdPlan (Fin L)) = 0 := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [stackPlan, Fin.append_left, Prod.fst_zero, Pi.zero_apply]
  · simp only [stackPlan, Fin.append_right, Prod.snd_zero, Pi.zero_apply]

theorem stackPlan_injective {L : ℕ} : Function.Injective (stackPlan (L := L)) := by
  intro y z h
  exact le_antisymm ((stackPlan_le_iff y z).1 h.le) ((stackPlan_le_iff z y).1 h.ge)

theorem stackPlan_surjective {L : ℕ} (v : Fin (L + L) → ℝ) :
    stackPlan (fun i => v (Fin.castAdd L i), fun i => v (Fin.natAdd L i)) = v :=
  Fin.append_castAdd_natAdd

/-- Assumption (ii) is Chapter 5's no-free-lunch property of the stacked set. -/
theorem noFreeLunch_iff_stack {L : ℕ} (Y : Set (ProdPlan (Fin L))) :
    (∀ y ∈ Y, 0 ≤ y → y = 0) ↔ MWG.Production.NoFreeLunch (stackPlan '' Y) := by
  constructor
  · rintro h _ ⟨y, hy, rfl⟩ h0
    rw [← stackPlan_zero] at h0 ⊢
    rw [h y hy ((stackPlan_le_iff _ _).1 h0)]
  · intro h y hy h0
    apply stackPlan_injective
    rw [stackPlan_zero]
    exact h _ ⟨y, hy, rfl⟩ (by rw [← stackPlan_zero]; exact (stackPlan_le_iff _ _).2 h0)

/-- Assumption (iii) is Chapter 5's free disposal of the stacked set. -/
theorem freeDisposal_iff_stack {L : ℕ} (Y : Set (ProdPlan (Fin L))) :
    (∀ y ∈ Y, ∀ y', y' ≤ y → y' ∈ Y) ↔ MWG.Production.FreeDisposal (stackPlan '' Y) := by
  constructor
  · rintro h _ ⟨y, hy, rfl⟩ v hv
    refine ⟨_, h y hy _ ?_, stackPlan_surjective v⟩
    rw [← stackPlan_le_iff, stackPlan_surjective]
    exact hv
  · intro h y hy y' hle
    obtain ⟨z, hz, hzy⟩ := h _ ⟨y, hy, rfl⟩ _ ((stackPlan_le_iff _ _).2 hle)
    rwa [stackPlan_injective hzy] at hz

/-! ### Examples 20.C.1-20.C.4 -/

/-- **Example 20.C.1** (MWG, p. 737), the Ramsey-Solow technology: goods `0` (consumption-
investment good) and `1` (labor), `Y = {(-k, -l, x, 0) : k, l ≥ 0, x ≤ F(k, l)} - ℝ^4_+`, with
the production function written `F ![k, l]`. -/
def ramseySolowSet (F : (Fin 2 → ℝ) → ℝ) : Set (ProdPlan (Fin 2)) :=
  {y | ∃ k l x : ℝ, 0 ≤ k ∧ 0 ≤ l ∧ x ≤ F ![k, l] ∧ y ≤ (![-k, -l], ![x, 0])}

/-- With a nondecreasing production function the Ramsey-Solow set is
`{y : y_b ≤ 0, y_{a,1} ≤ 0, y_{a,0} ≤ F(-y_b)}`. -/
theorem ramseySolowSet_eq {F : (Fin 2 → ℝ) → ℝ}
    (hmono : MonotoneOn F (Set.Ici 0)) :
    ramseySolowSet F = {y | y.1 ≤ 0 ∧ y.2 1 ≤ 0 ∧ y.2 0 ≤ F (-y.1)} := by
  ext ⟨yb, ya⟩
  simp only [ramseySolowSet]
  constructor
  · rintro ⟨k, l, x, hk, hl, hx, hb, ha⟩
    have hb0 : yb 0 ≤ -k := by simpa using hb 0
    have hb1 : yb 1 ≤ -l := by simpa using hb 1
    have ha0 : ya 0 ≤ x := by simpa using ha 0
    have ha1 : ya 1 ≤ 0 := by simpa using ha 1
    refine ⟨fun i => ?_, ha1, ?_⟩
    · fin_cases i
      · simp; linarith
      · simp; linarith
    · have hle : ![k, l] ≤ -yb := by
        intro i; fin_cases i
        · simp; linarith
        · simp; linarith
      have h0 : (0 : Fin 2 → ℝ) ≤ ![k, l] := by
        intro i; fin_cases i <;> simp [hk, hl]
      exact ha0.trans (hx.trans (hmono h0 (h0.trans hle) hle))
  · rintro ⟨hb, ha1, ha0⟩
    have hb0 : yb 0 ≤ 0 := hb 0
    have hb1 : yb 1 ≤ 0 := hb 1
    refine ⟨-yb 0, -yb 1, ya 0, by linarith, by linarith, ?_, fun i => ?_,
      fun i => ?_⟩
    · convert ha0 using 2
      funext i; fin_cases i <;> simp
    · fin_cases i <;> simp
    · fin_cases i
      · simp
      · simpa using ha1

/-- **Example 20.C.1** (MWG, p. 737): labor is a primary factor, it cannot be produced. -/
theorem ramseySolow_labor_primary {F : (Fin 2 → ℝ) → ℝ} :
    ∀ y ∈ ramseySolowSet F, y.1 1 ≤ 0 ∧ y.2 1 ≤ 0 := by
  rintro y ⟨k, l, x, hk, hl, -, hb, ha⟩
  have h1 : y.1 1 ≤ -l := by simpa using hb 1
  have h2 : y.2 1 ≤ 0 := by simpa using ha 1
  exact ⟨by linarith, h2⟩

/-- **Example 20.C.1** (MWG, p. 737): the Ramsey-Solow technology satisfies assumptions (i)-(iv)
when `F` is continuous, concave and nondecreasing on `ℝ²_+` with `F(0, 0) = 0`. -/
theorem example_20_C_1 {F : (Fin 2 → ℝ) → ℝ} (hcont : Continuous F)
    (hconc : ConcaveOn ℝ (Set.Ici 0) F) (hmono : MonotoneOn F (Set.Ici 0)) (h00 : F 0 = 0) :
    TechAssumptions (ramseySolowSet F) := by
  rw [ramseySolowSet_eq hmono]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine IsClosed.inter (isClosed_le continuous_fst continuous_const) ?_
    refine IsClosed.inter (isClosed_le ((continuous_apply 1).comp continuous_snd)
      continuous_const) ?_
    exact isClosed_le ((continuous_apply 0).comp continuous_snd)
      (hcont.comp continuous_fst.neg)
  · rintro ⟨yb, ya⟩ ⟨hb, ha1, ha0⟩ ⟨zb, za⟩ ⟨hb', ha1', ha0'⟩ a b ha hb'' hab
    refine ⟨?_, ?_, ?_⟩
    · intro i
      have h1 : yb i ≤ 0 := hb i
      have h2 : zb i ≤ 0 := hb' i
      simp only [Prod.smul_mk, Prod.mk_add_mk, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Pi.zero_apply]
      nlinarith
    · simp only [Prod.smul_mk, Prod.mk_add_mk, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      nlinarith
    · simp only [Prod.smul_mk, Prod.mk_add_mk, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have hyb : -yb ∈ Set.Ici (0 : Fin 2 → ℝ) := fun i => by simpa using hb i
      have hzb : -zb ∈ Set.Ici (0 : Fin 2 → ℝ) := fun i => by simpa using hb' i
      have := hconc.2 hyb hzb ha hb'' hab
      have heq : -(a • yb + b • zb) = a • -yb + b • -zb := by
        rw [neg_add, smul_neg, smul_neg]
      simp only [smul_eq_mul] at this
      rw [heq]
      nlinarith
  · refine ⟨le_rfl, le_rfl, ?_⟩
    simp [h00]
  · rintro ⟨yb, ya⟩ ⟨hb, ha1, ha0⟩ ⟨h0b, h0a⟩
    have hyb : yb = 0 := le_antisymm hb h0b
    subst hyb
    have : ya 0 ≤ 0 := by simpa [h00] using ha0
    refine Prod.ext rfl (funext fun i => ?_)
    fin_cases i
    · exact le_antisymm this (h0a 0)
    · exact le_antisymm ha1 (h0a 1)
  · rintro ⟨yb, ya⟩ ⟨hb, ha1, ha0⟩ ⟨zb, za⟩ ⟨hzb, hza⟩
    refine ⟨hzb.trans hb, (hza 1).trans ha1, (hza 0).trans (ha0.trans ?_)⟩
    have h0 : (0 : Fin 2 → ℝ) ≤ -yb := fun i => by simpa using hb i
    exact hmono h0 (h0.trans (neg_le_neg hzb)) (neg_le_neg hzb)
  · rintro ⟨yb, ya⟩ ⟨hb, ha1, ha0⟩
    refine ⟨hb, le_rfl, ?_⟩
    have h0 : (0 : Fin 2 → ℝ) ≤ -yb := fun i => by simpa using hb i
    simpa [h00] using hmono (le_refl (0 : Fin 2 → ℝ)) h0 h0

/-- **Example 20.C.3** (MWG, p. 738), the two-sector technology: goods `0` (capacity), `1`
(consumption) and `2` (labor), `Y = {(-k, 0, -l, k', x, 0) : k, l, k' ≥ 0, x ≤ G(k, l, k')}
- ℝ^6_+`. -/
def twoSectorSet (G : ℝ → ℝ → ℝ → ℝ) : Set (ProdPlan (Fin 3)) :=
  {y | ∃ k l k' x : ℝ, 0 ≤ k ∧ 0 ≤ l ∧ 0 ≤ k' ∧ x ≤ G k l k' ∧
    y ≤ (![-k, 0, -l], ![k', x, 0])}

/-- **Example 20.C.2** (MWG, p. 737), the cost-of-adjustment technology:
`Y = {(-k, 0, -l, k', x, 0) : k, l, k' ≥ 0, x ≤ F(k, l) - k' - γ(k' - k)} - ℝ^6_+`. -/
def costAdjustmentSet (F : ℝ → ℝ → ℝ) (γ : ℝ → ℝ) : Set (ProdPlan (Fin 3)) :=
  {y | ∃ k l k' x : ℝ, 0 ≤ k ∧ 0 ≤ l ∧ 0 ≤ k' ∧ x ≤ F k l - k' - γ (k' - k) ∧
    y ≤ (![-k, 0, -l], ![k', x, 0])}

/-- **Example 20.C.3** (MWG, p. 738): the cost-of-adjustment model is the two-sector model with
`G(k, l, k') = F(k, l) - k' - γ(k' - k)`. -/
theorem example_20_C_3_costAdjustment (F : ℝ → ℝ → ℝ) (γ : ℝ → ℝ) :
    costAdjustmentSet F γ = twoSectorSet (fun k l k' => F k l - k' - γ (k' - k)) := rfl

/-- Merging the capacity and consumption goods of the two-sector model into the single
consumption-investment good of the Ramsey-Solow model. -/
def mergeGoods (y : ProdPlan (Fin 3)) : ProdPlan (Fin 2) :=
  (![y.1 0 + y.1 1, y.1 2], ![y.2 0 + y.2 1, y.2 2])

/-- **Example 20.C.3** (MWG, p. 738): with `G(k, l, k') = F(k, l) - k'` (investment and
consumption goods perfect substitutes in production) the two-sector model is the Ramsey-Solow
model: merging the two goods maps the two-sector set exactly onto the Ramsey-Solow set. -/
theorem example_20_C_3_ramseySolow (F : (Fin 2 → ℝ) → ℝ) :
    mergeGoods '' twoSectorSet (fun k l k' => F ![k, l] - k') = ramseySolowSet F := by
  ext z
  constructor
  · rintro ⟨y, ⟨k, l, k', x, hk, hl, hk', hx, hb, ha⟩, rfl⟩
    refine ⟨k, l, x + k', hk, hl, by linarith, fun i => ?_, fun i => ?_⟩
    · have h0 := hb 0; have h1 := hb 1; have h2 := hb 2
      simp at h0 h1 h2
      fin_cases i <;> simp [mergeGoods] <;> linarith
    · have h0 := ha 0; have h1 := ha 1; have h2 := ha 2
      simp at h0 h1 h2
      fin_cases i <;> simp [mergeGoods] <;> linarith
  · rintro ⟨k, l, x, hk, hl, hx, hb, ha⟩
    refine ⟨(![z.1 0, 0, z.1 1], ![0, z.2 0, z.2 1]), ⟨k, l, 0, x, hk, hl, le_rfl,
      by simpa using hx, fun i => ?_, fun i => ?_⟩, ?_⟩
    · have h0 := hb 0; have h1 := hb 1
      simp at h0 h1
      fin_cases i <;> simp <;> linarith
    · have h0 := ha 0; have h1 := ha 1
      simp at h0 h1
      fin_cases i <;> simp <;> linarith
    · refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;>
        fin_cases i <;> simp [mergeGoods]

/-- **Example 20.C.4** (MWG, p. 738), the `(N + 1)`-sector technology: `N` capital goods
(`Sum.inl`), the consumption good (`Sum.inr 0`) and labor (`Sum.inr 1`);
`Y = {(-k, 0, -l, k', x, 0) : (k, l, k') ∈ A, x ≤ G(k, l, k')} - ℝ^{2(N+2)}_+` for an admissible
domain `A`. -/
def multiSectorSet (N : ℕ) (A : Set ((Fin N → ℝ) × ℝ × (Fin N → ℝ)))
    (G : (Fin N → ℝ) → ℝ → (Fin N → ℝ) → ℝ) : Set (ProdPlan (Fin N ⊕ Fin 2)) :=
  {y | ∃ k l k' x, (k, l, k') ∈ A ∧ x ≤ G k l k' ∧
    y ≤ (Sum.elim (fun n => -k n) ![0, -l], Sum.elim k' ![x, 0])}

/-! ### Production paths and prices -/

/-- **Definition 20.C.1** (MWG, p. 738): a production path is a sequence of plans in `Y`. -/
def IsProdPath (Y : Set (ProdPlan ι)) (y : ℕ → ProdPlan ι) : Prop := ∀ t, y t ∈ Y

/-- The net input-output vector `y_{a,t-1} + y_{b,t}` of a path at `t`, with `y_{a,-1} = 0`
(MWG, p. 738). -/
def netOutput (y : ℕ → ProdPlan ι) : ℕ → ι → ℝ
  | 0 => (y 0).1
  | t + 1 => (y t).2 + (y (t + 1)).1

/-- **Definition 20.C.2** (MWG, p. 739): a path is efficient if no other path has net outputs at
least as large at every date and different at some date. -/
def ProdEfficient (Y : Set (ProdPlan ι)) (y : ℕ → ProdPlan ι) : Prop :=
  IsProdPath Y y ∧ ¬ ∃ y', IsProdPath Y y' ∧ (∀ t, netOutput y t ≤ netOutput y' t) ∧
    netOutput y' ≠ netOutput y

/-- The value of a plan at the prices `(p_t, p_{t+1})`. -/
def planValue (pb pa : ι → ℝ) (z : ProdPlan ι) : ℝ := pb ⬝ᵥ z.1 + pa ⬝ᵥ z.2

/-- The profit `p_t · y_{bt} + p_{t+1} · y_{at}` of the plan at `t` (MWG, p. 739). -/
def periodProfit (p : ℕ → ι → ℝ) (y : ℕ → ProdPlan ι) (t : ℕ) : ℝ :=
  planValue (p t) (p (t + 1)) (y t)

/-- **Definition 20.C.3** (MWG, p. 739): `y` is myopically (short-run) profit maximizing for
`p` if every `y_t` maximizes `p_t · y_b + p_{t+1} · y_a` on `Y`; `p` is then a system of
**Malinvaud prices** for `y`. -/
def MyopicProfitMax (Y : Set (ProdPlan ι)) (p : ℕ → ι → ℝ) (y : ℕ → ProdPlan ι) : Prop :=
  IsProdPath Y y ∧ ∀ t, ∀ z ∈ Y, planValue (p t) (p (t + 1)) z ≤ periodProfit p y t

/-- The **transversality condition** `p_{t+1} · y_{at} → 0` (MWG, p. 740). -/
def Transversality (p : ℕ → ι → ℝ) (y : ℕ → ProdPlan ι) : Prop :=
  Tendsto (fun t => p (t + 1) ⬝ᵥ (y t).2) atTop (𝓝 0)

/-- **The rearrangement identity** (MWG, pp. 740 and 744): matching inputs and outputs per period
instead of per plan, `∑_{t ≤ T} p_t · (y_{a,t-1} + y_{bt}) = ∑_{t ≤ T} π_t - p_{T+1} · y_{aT}`. -/
theorem sum_value_netOutput (p : ℕ → ι → ℝ) (y : ℕ → ProdPlan ι) (T : ℕ) :
    ∑ t ∈ Finset.range (T + 1), p t ⬝ᵥ netOutput y t
      = ∑ t ∈ Finset.range (T + 1), periodProfit p y t - p (T + 1) ⬝ᵥ (y T).2 := by
  induction T with
  | zero => simp [netOutput, periodProfit, planValue]
  | succ T ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ (fun t => periodProfit p y t) (T + 1)]
    simp only [netOutput, periodProfit, planValue, dotProduct_add]
    ring

/-- The identity in the form "truncate the last plan":
`∑_{t ≤ T} p_t · n_t = ∑_{t < T} π_t + p_T · y_{bT}`. -/
theorem sum_value_netOutput' (p : ℕ → ι → ℝ) (y : ℕ → ProdPlan ι) (T : ℕ) :
    ∑ t ∈ Finset.range (T + 1), p t ⬝ᵥ netOutput y t
      = ∑ t ∈ Finset.range T, periodProfit p y t + p T ⬝ᵥ (y T).1 := by
  rw [sum_value_netOutput, Finset.sum_range_succ]
  simp only [periodProfit, planValue]
  ring

/-- **The key inequality** of the proof of Proposition 20.C.1 (MWG, p. 740): if `y` is myopically
profit maximizing and `Y` allows truncation, then for any path `y'` and any `T`,
`∑_{t ≤ T} p_t · n'_t ≤ ∑_{t ≤ T} p_t · n_t + p_{T+1} · y_{aT}`. -/
theorem sum_value_le_of_myopic {Y : Set (ProdPlan ι)} {p : ℕ → ι → ℝ}
    {y y' : ℕ → ProdPlan ι} (htr : ∀ z ∈ Y, (z.1, 0) ∈ Y) (hy : MyopicProfitMax Y p y)
    (hy' : IsProdPath Y y') (T : ℕ) :
    ∑ t ∈ Finset.range (T + 1), p t ⬝ᵥ netOutput y' t
      ≤ ∑ t ∈ Finset.range (T + 1), p t ⬝ᵥ netOutput y t + p (T + 1) ⬝ᵥ (y T).2 := by
  rw [sum_value_netOutput' p y', sum_value_netOutput p y, sub_add_cancel,
    Finset.sum_range_succ]
  have h1 : ∑ t ∈ Finset.range T, periodProfit p y' t ≤ ∑ t ∈ Finset.range T, periodProfit p y t :=
    Finset.sum_le_sum fun t _ => hy.2 t _ (hy' t)
  have h2 : p T ⬝ᵥ (y' T).1 ≤ periodProfit p y T := by
    have := hy.2 T _ (htr _ (hy' T))
    simpa [planValue] using this
  linarith

/-- The common core of Proposition 20.C.1 and Exercise 20.C.3: under myopic profit maximization,
truncation and the transversality condition, no path `y'` can have `p_t · n'_t ≥ p_t · n_t` at
every date with strict inequality at some date. -/
theorem no_value_improvement {Y : Set (ProdPlan ι)} {p : ℕ → ι → ℝ}
    {y y' : ℕ → ProdPlan ι} (htr : ∀ z ∈ Y, (z.1, 0) ∈ Y) (hy : MyopicProfitMax Y p y)
    (htc : Transversality p y) (hy' : IsProdPath Y y')
    (hge : ∀ t, p t ⬝ᵥ netOutput y t ≤ p t ⬝ᵥ netOutput y' t) {s : ℕ}
    (hs : p s ⬝ᵥ netOutput y s < p s ⬝ᵥ netOutput y' s) : False := by
  set ε := p s ⬝ᵥ netOutput y' s - p s ⬝ᵥ netOutput y s with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  have hgap : ∀ T, s ≤ T → ε ≤ p (T + 1) ⬝ᵥ (y T).2 := by
    intro T hT
    have hsum : ∑ t ∈ Finset.range (T + 1), p t ⬝ᵥ netOutput y t + ε
        ≤ ∑ t ∈ Finset.range (T + 1), p t ⬝ᵥ netOutput y' t := by
      have hmem : s ∈ Finset.range (T + 1) := Finset.mem_range.2 (Nat.lt_succ_of_le hT)
      rw [← sub_nonneg, ← sub_sub, ← Finset.sum_sub_distrib]
      have := Finset.single_le_sum (f := fun t => p t ⬝ᵥ netOutput y' t - p t ⬝ᵥ netOutput y t)
        (fun t _ => sub_nonneg.2 (hge t)) hmem
      linarith
    have := sum_value_le_of_myopic htr hy hy' T
    linarith
  have hev := (htc.eventually (gt_mem_nhds hεpos))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  have h1 := hN (max N s) (le_max_left _ _)
  have h2 := hgap (max N s) (le_max_right _ _)
  linarith

/-- **Proposition 20.C.1** (MWG, p. 740): a path that is myopically profit maximizing for a price
sequence `p ≫ 0` and satisfies the transversality condition is efficient. Truncation, assumption
(iv), is the only property of `Y` used. -/
theorem proposition_20_C_1 {Y : Set (ProdPlan ι)} {p : ℕ → ι → ℝ} {y : ℕ → ProdPlan ι}
    (htr : ∀ z ∈ Y, (z.1, 0) ∈ Y) (hp : ∀ t, StrictPos (p t)) (hy : MyopicProfitMax Y p y)
    (htc : Transversality p y) : ProdEfficient Y y := by
  refine ⟨hy.1, fun ⟨y', hy', hle, hne⟩ => ?_⟩
  obtain ⟨s, hs⟩ : ∃ s, netOutput y' s ≠ netOutput y s := by
    by_contra h
    push Not at h
    exact hne (funext h)
  refine no_value_improvement htr hy htc hy' (fun t => ?_) (s := s) ?_
  · exact dotProduct_le_dotProduct_of_nonneg_left (hle t) (fun i => (hp t i).le)
  · have := dotProduct_pos_of_strictPos (hp s) (sub_nonneg.2 (hle s)) (sub_ne_zero.2 hs)
    rw [dotProduct_sub] at this
    linarith

omit [Fintype ι] in
/-- Efficient plans lie on the boundary of `Y` (MWG, p. 742): no `y_t` of an efficient path is in
the interior of `Y` (otherwise the output `y_{a,t}` could be raised). -/
theorem prodEfficient_not_mem_interior [Finite ι] [Nonempty ι] {Y : Set (ProdPlan ι)}
    {y : ℕ → ProdPlan ι} (hy : ProdEfficient Y y) (t : ℕ) : y t ∉ interior Y := by
  have := Fintype.ofFinite ι
  intro hint
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior (y t) hint
  set e : ProdPlan ι := (0, fun _ => ε / 2) with he
  have hmem : y t + e ∈ Y := by
    apply interior_subset
    apply hball
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
    have hn : ‖e‖ ≤ ε / 2 := by
      rw [he, Prod.norm_def]
      refine max_le (by simp; linarith) ?_
      refine (pi_norm_le_iff_of_nonneg (by linarith)).2 fun i => ?_
      rw [Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith
  set y' : ℕ → ProdPlan ι := Function.update y t (y t + e) with hy'
  have hpath : IsProdPath Y y' := by
    intro s
    by_cases hs : s = t
    · subst hs; simp [hy', hmem]
    · simp [hy', hs, hy.1 s]
  refine hy.2 ⟨y', hpath, fun s => ?_, fun h => ?_⟩
  · cases s with
    | zero =>
      by_cases h0 : t = 0
      · subst h0; simp [netOutput, hy', he]
      · simp [netOutput, hy', Ne.symm h0]
    | succ s =>
      simp only [netOutput, hy']
      by_cases h1 : s = t
      · subst h1
        intro i
        simp [he]
        linarith
      · by_cases h2 : s + 1 = t
        · subst h2; simp [he]
        · simp [Function.update_of_ne h1, Function.update_of_ne h2]
  · have := congrFun (congrFun h (t + 1)) (Classical.arbitrary ι)
    have ht : t + 1 ≠ t := by omega
    simp [netOutput, hy', he] at this
    linarith

/-! ### Example 20.C.5: storage -/

/-- The storage technology of Example 20.C.5 (MWG, p. 740), `L = 1`:
`Y = {(-k, k') : k ≥ 0, k' ≤ k}`. -/
def storageSet : Set (ProdPlan (Fin 1)) :=
  {y | ∃ k k', 0 ≤ k ∧ k' ≤ k ∧ y = (fun _ => -k, fun _ => k')}

theorem storageSet_eq : storageSet = {y | y.1 0 ≤ 0 ∧ y.2 0 ≤ -y.1 0} := by
  ext ⟨yb, ya⟩
  constructor
  · rintro ⟨k, k', hk, hk', h⟩
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp; constructor <;> linarith
  · rintro ⟨h1, h2⟩
    refine ⟨-yb 0, ya 0, by linarith, by linarith, ?_⟩
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> fin_cases i <;> simp

/-- The storage technology satisfies assumptions (i)-(iv). -/
theorem storageSet_techAssumptions : TechAssumptions storageSet := by
  rw [storageSet_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact IsClosed.inter (isClosed_le ((continuous_apply 0).comp continuous_fst)
      continuous_const) (isClosed_le ((continuous_apply 0).comp continuous_snd)
      ((continuous_apply 0).comp continuous_fst).neg)
  · rintro ⟨yb, ya⟩ ⟨h1, h2⟩ ⟨zb, za⟩ ⟨h1', h2'⟩ a b ha hb hab
    dsimp only at h1 h2 h1' h2'
    refine ⟨?_, ?_⟩
    · change a * yb 0 + b * zb 0 ≤ 0
      nlinarith
    · change a * ya 0 + b * za 0 ≤ -(a * yb 0 + b * zb 0)
      nlinarith
  · exact ⟨le_rfl, by simp⟩
  · rintro ⟨yb, ya⟩ ⟨h1, h2⟩ ⟨h0b, h0a⟩
    have hb : yb 0 = 0 := le_antisymm h1 (h0b 0)
    have ha : ya 0 = 0 := le_antisymm (by linarith) (h0a 0)
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> fin_cases i <;> simp [hb, ha]
  · rintro ⟨yb, ya⟩ ⟨h1, h2⟩ ⟨zb, za⟩ ⟨hzb, hza⟩
    exact ⟨(hzb 0).trans h1, by linarith [hzb 0, hza 0]⟩
  · rintro ⟨yb, ya⟩ ⟨h1, h2⟩
    exact ⟨h1, by simp; linarith⟩

/-- The path of Example 20.C.5: carry one unit forward forever, `y_t = (-1, 1)`. -/
def storagePath : ℕ → ProdPlan (Fin 1) := fun _ => (fun _ => -1, fun _ => 1)

/-- **Example 20.C.5** (MWG, p. 740): the storage path `y_t = (-1, 1)` is a production path with
net outputs `-1` at `t = 0` and `0` afterwards; it is not efficient (the path `y'_t = 0`
dominates it); yet it is myopically profit maximizing for the constant prices `p_t = 1`, and the
transversality condition fails. -/
theorem example_20_C_5 :
    IsProdPath storageSet storagePath ∧
      netOutput storagePath 0 = (fun _ => -1) ∧ (∀ t, netOutput storagePath (t + 1) = 0) ∧
      ¬ ProdEfficient storageSet storagePath ∧
      MyopicProfitMax storageSet (fun _ _ => 1) storagePath ∧
      ¬ Transversality (fun _ _ => 1) storagePath := by
  have hpath : IsProdPath storageSet storagePath := fun t =>
    ⟨1, 1, zero_le_one, le_rfl, rfl⟩
  have h0 : netOutput storagePath 0 = fun _ => -1 := rfl
  have hs : ∀ t, netOutput storagePath (t + 1) = 0 := by
    intro t; funext i; simp [netOutput, storagePath]
  refine ⟨hpath, h0, hs, ?_, ⟨hpath, ?_⟩, ?_⟩
  · rintro ⟨-, hne⟩
    refine hne ⟨fun _ => 0, fun t => ⟨0, 0, le_rfl, le_rfl, by ext <;> simp⟩, fun t => ?_, ?_⟩
    · cases t with
      | zero => intro i; simp [netOutput, storagePath]
      | succ t => rw [hs t]; intro i; simp [netOutput]
    · intro h
      have := congrFun (congrFun h 0) 0
      simp [netOutput, storagePath] at this
  · rintro t z hz
    rw [storageSet_eq] at hz
    obtain ⟨h1, h2⟩ := hz
    simp [periodProfit, planValue, storagePath, dotProduct]
    linarith
  · intro h
    have : (fun t : ℕ => (fun _ : Fin 1 => (1 : ℝ)) ⬝ᵥ (storagePath t).2) = fun _ => 1 := by
      funext t; simp [storagePath, dotProduct]
    unfold Transversality at h
    rw [this] at h
    exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds h)

/-! ### Exercises 20.C.1-20.C.5(a) -/

/-- **Exercise 20.C.1** (MWG, p. 783): the own rate of interest of commodity `l` from `t` to
`t + 1`, defined by `p_{t,l} = (1 + r_{t,l}) p_{t+1,l}`. -/
noncomputable def ownRate (p : ℕ → ι → ℝ) (t : ℕ) (l : ι) : ℝ := p t l / p (t + 1) l - 1

omit [Fintype ι] in
/-- **Exercise 20.C.1** (MWG, p. 783): the own rate satisfies `p_{t,l} = (1 + r_{t,l})
p_{t+1,l}`, and is the unique number doing so. -/
theorem exercise_20_C_1 (p : ℕ → ι → ℝ) (t : ℕ) (l : ι) (hp : p (t + 1) l ≠ 0) :
    p t l = (1 + ownRate p t l) * p (t + 1) l ∧
      ∀ r, p t l = (1 + r) * p (t + 1) l → r = ownRate p t l := by
  refine ⟨by unfold ownRate; field_simp; ring, fun r hr => ?_⟩
  unfold ownRate
  rw [hr]
  field_simp
  ring

/-- **Exercise 20.C.2** (MWG, p. 783): a myopically profit maximizing path is also profit
maximizing over any finite horizon: for any `T`, no path changes the total profits of the first
`T` periods upward. -/
theorem exercise_20_C_2 {Y : Set (ProdPlan ι)} {p : ℕ → ι → ℝ} {y : ℕ → ProdPlan ι}
    (hy : MyopicProfitMax Y p y) {y' : ℕ → ProdPlan ι} (hy' : IsProdPath Y y') (T : ℕ) :
    ∑ t ∈ Finset.range T, periodProfit p y' t ≤ ∑ t ∈ Finset.range T, periodProfit p y t :=
  Finset.sum_le_sum fun t _ => hy.2 t _ (hy' t)

/-- **Exercise 20.C.3** (MWG, p. 783), weak efficiency: no path has net outputs strictly larger
in every commodity at every date. -/
def ProdWeaklyEfficient (Y : Set (ProdPlan ι)) (y : ℕ → ProdPlan ι) : Prop :=
  IsProdPath Y y ∧ ¬ ∃ y', IsProdPath Y y' ∧ ∀ t i, netOutput y t i < netOutput y' t i

/-- **Exercise 20.C.3** (MWG, p. 783): Proposition 20.C.1 with `p ≥ 0` having some nonzero entry
gives weak efficiency. -/
theorem exercise_20_C_3 {Y : Set (ProdPlan ι)} {p : ℕ → ι → ℝ} {y : ℕ → ProdPlan ι}
    (htr : ∀ z ∈ Y, (z.1, 0) ∈ Y) (hp : ∀ t, 0 ≤ p t) {s : ℕ} (hps : p s ≠ 0)
    (hy : MyopicProfitMax Y p y) (htc : Transversality p y) : ProdWeaklyEfficient Y y := by
  refine ⟨hy.1, fun ⟨y', hy', hlt⟩ => ?_⟩
  refine no_value_improvement htr hy htc hy' (fun t => ?_) (s := s) ?_
  · exact dotProduct_le_dotProduct_of_nonneg_left (fun i => (hlt t i).le) (hp t)
  · obtain ⟨i, hi⟩ : ∃ i, p s i ≠ 0 := by
      by_contra h
      push Not at h
      exact hps (funext h)
    have hpi : 0 < p s i := lt_of_le_of_ne (hp s i) (Ne.symm hi)
    have : 0 < p s ⬝ᵥ (netOutput y' s - netOutput y s) := by
      refine Finset.sum_pos' (fun j _ => mul_nonneg (hp s j) (sub_nonneg.2 (hlt s j).le))
        ⟨i, Finset.mem_univ _, mul_pos hpi (sub_pos.2 (hlt s i))⟩
    rw [dotProduct_sub] at this
    linarith

/-- A path is **bounded** (Exercise 20.C.4, MWG, p. 783): `|y_{t}| ≤ α` coordinatewise. -/
def BoundedPath (y : ℕ → ProdPlan ι) : Prop :=
  ∃ α : ℝ, ∀ t i, |(y t).1 i| ≤ α ∧ |(y t).2 i| ≤ α

/-- **Exercise 20.C.4** (MWG, p. 783): `y` is overall profit maximizing for `p` if its profit
series converges and no path with a convergent profit series has a larger total profit. -/
def OverallProfitMax (Y : Set (ProdPlan ι)) (p : ℕ → ι → ℝ) (y : ℕ → ProdPlan ι) : Prop :=
  IsProdPath Y y ∧ Summable (periodProfit p y) ∧
    ∀ y', IsProdPath Y y' → Summable (periodProfit p y') →
      ∑' t, periodProfit p y' t ≤ ∑' t, periodProfit p y t

/-- Summable nonnegative prices tend to zero against a bounded path. -/
theorem tendsto_value_of_bounded {p : ℕ → ι → ℝ} (hp0 : ∀ t, 0 ≤ p t)
    (hps : Summable fun t => ∑ i, p t i) {v : ℕ → ι → ℝ} {α : ℝ} (hv : ∀ t i, |v t i| ≤ α) :
    Tendsto (fun t => p t ⬝ᵥ v t) atTop (𝓝 0) := by
  have hlim := (hps.tendsto_atTop_zero).mul_const α
  rw [zero_mul] at hlim
  refine squeeze_zero_norm (fun t => ?_) hlim
  rw [Real.norm_eq_abs]
  calc |p t ⬝ᵥ v t| ≤ ∑ i, |p t i * v t i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, p t i * α := Finset.sum_le_sum fun i _ => by
        rw [abs_mul, abs_of_nonneg (hp0 t i)]
        exact mul_le_mul_of_nonneg_left (hv t i) (hp0 t i)
    _ = (∑ i, p t i) * α := by rw [Finset.sum_mul]

/-- The path that follows `y'` before `T`, the truncation `((y'_T)_b, 0)` at `T`, and `y` after
`T` (used in Exercise 20.C.4(a)). -/
def splicePath (y y' : ℕ → ProdPlan ι) (T : ℕ) : ℕ → ProdPlan ι :=
  fun t => if t < T then y' t else if t = T then ((y' T).1, 0) else y t

omit [Fintype ι] in
theorem splicePath_lt {y y' : ℕ → ProdPlan ι} {T t : ℕ} (h : t < T) :
    splicePath y y' T t = y' t := by
  simp [splicePath, h]

omit [Fintype ι] in
theorem splicePath_self {y y' : ℕ → ProdPlan ι} {T : ℕ} :
    splicePath y y' T T = ((y' T).1, 0) := by
  simp [splicePath]

omit [Fintype ι] in
theorem splicePath_gt {y y' : ℕ → ProdPlan ι} {T t : ℕ} (h : T < t) :
    splicePath y y' T t = y t := by
  simp [splicePath, show ¬ t < T by omega, show t ≠ T by omega]

/-- **Exercise 20.C.4(a)** (MWG, p. 783): a bounded path that is overall profit maximizing for
`p ≫ 0` with `∑_t p_t < ∞` is efficient (truncation, assumption (iv), is used). -/
theorem exercise_20_C_4a {Y : Set (ProdPlan ι)} {p : ℕ → ι → ℝ} {y : ℕ → ProdPlan ι}
    (htr : ∀ z ∈ Y, (z.1, 0) ∈ Y) (hp : ∀ t, StrictPos (p t))
    (hps : Summable fun t => ∑ i, p t i) (hb : BoundedPath y) (hy : OverallProfitMax Y p y) :
    ProdEfficient Y y := by
  obtain ⟨α, hα⟩ := hb
  refine ⟨hy.1, fun ⟨y', hy', hle, hne⟩ => ?_⟩
  obtain ⟨s, hs⟩ : ∃ s, netOutput y' s ≠ netOutput y s := by
    by_contra h
    push Not at h
    exact hne (funext h)
  have hp0 : ∀ t, 0 ≤ p t := fun t i => (hp t i).le
  set ε := p s ⬝ᵥ netOutput y' s - p s ⬝ᵥ netOutput y s with hε
  have hεpos : 0 < ε := by
    have := dotProduct_pos_of_strictPos (hp s) (sub_nonneg.2 (hle s)) (sub_ne_zero.2 hs)
    rw [dotProduct_sub] at this
    rw [hε]; linarith
  -- the spliced path: `y'` before `T`, the truncation of `y'_T` at `T`, `y` afterwards
  have hgap : ∀ T, s ≤ T → ε ≤ p (T + 1) ⬝ᵥ (y T).2 := by
    intro T hT
    set z := splicePath y y' T with hz
    have hzpath : IsProdPath Y z := by
      intro t
      rcases lt_trichotomy t T with h | rfl | h
      · rw [hz, splicePath_lt h]; exact hy' t
      · rw [hz, splicePath_self]; exact htr _ (hy' t)
      · rw [hz, splicePath_gt h]; exact hy.1 t
    have htail : ∀ t, periodProfit p z (t + (T + 1)) = periodProfit p y (t + (T + 1)) := by
      intro t
      simp only [periodProfit]
      rw [hz, splicePath_gt (by omega)]
    have hzs : Summable (periodProfit p z) := by
      refine (summable_nat_add_iff (T + 1)).1 ?_
      exact ((summable_nat_add_iff (T + 1)).2 hy.2.1).congr fun t => (htail t).symm
    have hle' := hy.2.2 z hzpath hzs
    have htail' : ∑' t, periodProfit p z (t + (T + 1)) = ∑' t, periodProfit p y (t + (T + 1)) :=
      tsum_congr htail
    rw [← hzs.sum_add_tsum_nat_add (T + 1), ← hy.2.1.sum_add_tsum_nat_add (T + 1),
      htail', add_le_add_iff_right] at hle'
    have hzsum : ∑ t ∈ Finset.range (T + 1), periodProfit p z t
        = ∑ t ∈ Finset.range (T + 1), p t ⬝ᵥ netOutput y' t := by
      rw [sum_value_netOutput' p y', Finset.sum_range_succ]
      congr 1
      · refine Finset.sum_congr rfl fun t ht => ?_
        simp only [periodProfit]
        rw [hz, splicePath_lt (Finset.mem_range.1 ht)]
      · simp only [periodProfit, planValue]
        rw [hz, splicePath_self, dotProduct_zero, add_zero]
    rw [hzsum] at hle'
    have hsum : ∑ t ∈ Finset.range (T + 1), p t ⬝ᵥ netOutput y t + ε
        ≤ ∑ t ∈ Finset.range (T + 1), p t ⬝ᵥ netOutput y' t := by
      have hmem : s ∈ Finset.range (T + 1) := Finset.mem_range.2 (Nat.lt_succ_of_le hT)
      rw [← sub_nonneg, ← sub_sub, ← Finset.sum_sub_distrib]
      have := Finset.single_le_sum (f := fun t => p t ⬝ᵥ netOutput y' t - p t ⬝ᵥ netOutput y t)
        (fun t _ => sub_nonneg.2 (dotProduct_le_dotProduct_of_nonneg_left (hle t) (hp0 t))) hmem
      linarith
    rw [sum_value_netOutput p y] at hsum
    linarith
  have hps1 : Summable fun t => ∑ i, p (t + 1) i :=
    (summable_nat_add_iff 1).2 hps
  have htc : Tendsto (fun t => p (t + 1) ⬝ᵥ (y t).2) atTop (𝓝 0) :=
    tendsto_value_of_bounded (p := fun t => p (t + 1)) (v := fun t => (y t).2)
      (fun t => hp0 (t + 1)) hps1 (fun t i => (hα t i).2)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (htc.eventually (gt_mem_nhds hεpos))
  have h1 := hN (max N s) (le_max_left _ _)
  have h2 := hgap (max N s) (le_max_right _ _)
  linarith

/-- **Exercise 20.C.4(b)** (MWG, p. 783): a bounded path that is myopically profit maximizing for
`p ≫ 0` with `∑_t p_t < ∞` is overall profit maximizing. -/
theorem exercise_20_C_4b {Y : Set (ProdPlan ι)} {p : ℕ → ι → ℝ} {y : ℕ → ProdPlan ι}
    (hp : ∀ t, StrictPos (p t)) (hps : Summable fun t => ∑ i, p t i) (hb : BoundedPath y)
    (hy : MyopicProfitMax Y p y) : OverallProfitMax Y p y := by
  obtain ⟨α, hα⟩ := hb
  have hp0 : ∀ t i, 0 ≤ p t i := fun t i => (hp t i).le
  have hsum : Summable (periodProfit p y) := by
    have hps1 : Summable fun t => ∑ i, p (t + 1) i := (summable_nat_add_iff 1).2 hps
    refine Summable.of_norm_bounded ((hps.add hps1).mul_right α) fun t => ?_
    rw [Real.norm_eq_abs]
    have hdot : ∀ (q v : ι → ℝ), 0 ≤ q → (∀ i, |v i| ≤ α) → |q ⬝ᵥ v| ≤ (∑ i, q i) * α := by
      intro q v hq hv
      calc |q ⬝ᵥ v| ≤ ∑ i, |q i * v i| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i, q i * α := Finset.sum_le_sum fun i _ => by
            rw [abs_mul, abs_of_nonneg (hq i)]
            exact mul_le_mul_of_nonneg_left (hv i) (hq i)
        _ = (∑ i, q i) * α := by rw [Finset.sum_mul]
    simp only [periodProfit, planValue]
    calc |p t ⬝ᵥ (y t).1 + p (t + 1) ⬝ᵥ (y t).2|
        ≤ |p t ⬝ᵥ (y t).1| + |p (t + 1) ⬝ᵥ (y t).2| := abs_add_le _ _
      _ ≤ (∑ i, p t i) * α + (∑ i, p (t + 1) i) * α :=
          add_le_add (hdot _ _ (hp0 t) fun i => (hα t i).1)
            (hdot _ _ (hp0 (t + 1)) fun i => (hα t i).2)
      _ = ((∑ i, p t i) + ∑ i, p (t + 1) i) * α := by ring
  exact ⟨hy.1, hsum, fun y' hy' hs' =>
    Summable.tsum_le_tsum (fun t => hy.2 t _ (hy' t)) hs' hsum⟩

/-- **Exercise 20.C.5** (MWG, p. 783): a path is `T`-efficient if no dominating path differs
from it at no more than `T` dates. -/
def TEfficient (Y : Set (ProdPlan ι)) (y : ℕ → ProdPlan ι) (T : ℕ) : Prop :=
  IsProdPath Y y ∧ ¬ ∃ y', IsProdPath Y y' ∧ (∀ t, netOutput y t ≤ netOutput y' t) ∧
    netOutput y' ≠ netOutput y ∧ {t | y' t ≠ y t}.Finite ∧ {t | y' t ≠ y t}.ncard ≤ T

/-- Myopic profit maximization for `p ≫ 0` rules out every dominating path that differs from
`y` at only finitely many dates (no transversality condition is needed). -/
theorem not_finite_change_of_myopic {Y : Set (ProdPlan ι)} {p : ℕ → ι → ℝ}
    {y y' : ℕ → ProdPlan ι} (hp : ∀ t, StrictPos (p t)) (hy : MyopicProfitMax Y p y)
    (hy' : IsProdPath Y y') (hle : ∀ t, netOutput y t ≤ netOutput y' t)
    (hne : netOutput y' ≠ netOutput y) : ¬ {t | y' t ≠ y t}.Finite := by
  intro hfin
  obtain ⟨M, hM⟩ : ∃ M, ∀ t, M ≤ t → y' t = y t := by
    obtain ⟨M, hM⟩ := hfin.bddAbove
    refine ⟨M + 1, fun t ht => ?_⟩
    by_contra h
    have := hM h
    omega
  have hlate : ∀ t, M < t → netOutput y' t = netOutput y t := by
    intro t ht
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    simp only [netOutput, hM s (by omega), hM (s + 1) (by omega)]
  obtain ⟨s, hs⟩ : ∃ s, netOutput y' s ≠ netOutput y s := by
    by_contra h
    push Not at h
    exact hne (funext h)
  have hsM : s ≤ M := by
    by_contra h
    exact hs (hlate s (by omega))
  have hsum : ∑ t ∈ Finset.range (M + 1), p t ⬝ᵥ netOutput y' t
      ≤ ∑ t ∈ Finset.range (M + 1), p t ⬝ᵥ netOutput y t := by
    rw [sum_value_netOutput' p y', sum_value_netOutput' p y, hM M le_rfl]
    have := Finset.sum_le_sum fun t (_ : t ∈ Finset.range M) => hy.2 t _ (hy' t)
    simp only [periodProfit] at this ⊢
    linarith
  have hpos : 0 < ∑ t ∈ Finset.range (M + 1), (p t ⬝ᵥ netOutput y' t - p t ⬝ᵥ netOutput y t) := by
    refine Finset.sum_pos' (fun t _ => ?_) ⟨s, Finset.mem_range.2 (by omega), ?_⟩
    · exact sub_nonneg.2 (dotProduct_le_dotProduct_of_nonneg_left (hle t)
        (fun i => (hp t i).le))
    · have := dotProduct_pos_of_strictPos (hp s) (sub_nonneg.2 (hle s)) (sub_ne_zero.2 hs)
      rwa [dotProduct_sub] at this
  rw [Finset.sum_sub_distrib] at hpos
  linarith

/-- **Exercise 20.C.5(a)** (MWG, p. 783): a path that is myopically profit maximizing for some
`p ≫ 0` is `T`-efficient for every `T < ∞`. -/
theorem exercise_20_C_5a {Y : Set (ProdPlan ι)} {p : ℕ → ι → ℝ} {y : ℕ → ProdPlan ι}
    (hp : ∀ t, StrictPos (p t)) (hy : MyopicProfitMax Y p y) (T : ℕ) : TEfficient Y y T :=
  ⟨hy.1, fun ⟨_, hy', hle, hne, hfin, _⟩ => not_finite_change_of_myopic hp hy hy' hle hne hfin⟩

end MWG.EquilibriumTime
