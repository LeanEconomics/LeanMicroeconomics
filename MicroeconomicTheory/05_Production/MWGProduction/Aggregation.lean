/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGProduction.Profit

/-!
# Aggregation (MWG Section 5.E, pp. 147-149)

For production sets `Y₁, …, Y_J ⊆ ℝ^L`: the aggregate production set `Y = Y₁ + ⋯ + Y_J` and the
aggregate supply correspondence `Σ_j y_j(p)`.

* **Proposition 5.E.1** (i) `π*(p) = Σ_j π_j(p)` (`proposition_5_E_1_i`, in `[-∞, +∞]` for
  nonempty `Y_j`; real form `proposition_5_E_1_i_real`) and (ii) `y*(p) = Σ_j y_j(p)`
  (`proposition_5_E_1_ii`), for every price vector and without convexity (**Exercise 5.E.2**).
* The aggregate law of supply and the symmetry and semidefiniteness of `Σ_j Dy_j(p)` (p. 147).
* **Exercise 5.E.1** (the differentiable proof of (ii)) and **Exercise 5.E.3**, which as printed
  (prices `p ≫ 0`) fails like Proposition 5.C.1(iii); corrected forms are proved.
-/

namespace MWG.Production

open MWG.ClassicalDemand MWG.ConsumerChoice Filter Topology

variable {L J : ℕ}

/-- **Section 5.E** (MWG, p. 147). The aggregate production set `Y₁ + ⋯ + Y_J`. -/
def aggSet (Ys : Fin J → Set (Fin L → ℝ)) : Set (Fin L → ℝ) :=
  {y | ∃ ys : Fin J → Fin L → ℝ, (∀ j, ys j ∈ Ys j) ∧ y = ∑ j, ys j}

/-- **Section 5.E** (MWG, p. 147). The aggregate supply correspondence `Σ_j y_j(p)`. -/
def aggSupply (Ys : Fin J → Set (Fin L → ℝ)) (p : Fin L → ℝ) : Set (Fin L → ℝ) :=
  {y | ∃ ys : Fin J → Fin L → ℝ, (∀ j, ys j ∈ supply (Ys j) p) ∧ y = ∑ j, ys j}

theorem dotProduct_finset_sum (p : Fin L → ℝ) (ys : Fin J → Fin L → ℝ) :
    p ⬝ᵥ ∑ j, ys j = ∑ j, p ⬝ᵥ ys j := by
  simp only [dotProduct, Finset.sum_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.mul_sum _ _ _

/-- **Proposition 5.E.1(ii)** (MWG, p. 148) and **Exercise 5.E.2**. For every `p`, the supply
correspondence of the aggregate production set is the sum of the individual supply
correspondences: `y*(p) = Σ_j y_j(p)`. No convexity is used. -/
theorem proposition_5_E_1_ii (Ys : Fin J → Set (Fin L → ℝ)) (p : Fin L → ℝ) :
    supply (aggSet Ys) p = aggSupply Ys p := by
  classical
  ext y
  constructor
  · rintro ⟨⟨ys, hys, rfl⟩, hmax⟩
    refine ⟨ys, fun k => ⟨hys k, fun y' hy' => ?_⟩, rfl⟩
    set ys' := Function.update ys k y' with hys'
    have hmem : ∑ j, ys' j ∈ aggSet Ys := ⟨ys', fun j => by
      by_cases hj : j = k
      · subst hj; simp [hys', hy']
      · simp [hys', hj, hys j], rfl⟩
    have h1 := hmax _ hmem
    rw [dotProduct_finset_sum, dotProduct_finset_sum] at h1
    have h2 : ∑ j, p ⬝ᵥ ys' j = ∑ j, p ⬝ᵥ ys j - p ⬝ᵥ ys k + p ⬝ᵥ y' := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k),
        ← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
      have : ∑ j ∈ Finset.univ.erase k, p ⬝ᵥ ys' j = ∑ j ∈ Finset.univ.erase k, p ⬝ᵥ ys j :=
        Finset.sum_congr rfl fun j hj => by
          rw [hys', Function.update_of_ne (Finset.ne_of_mem_erase hj)]
      rw [this, hys', Function.update_self]
      ring
    linarith
  · rintro ⟨ys, hys, rfl⟩
    refine ⟨⟨ys, fun j => (hys j).1, rfl⟩, ?_⟩
    rintro _ ⟨ys', hys', rfl⟩
    rw [dotProduct_finset_sum, dotProduct_finset_sum]
    exact Finset.sum_le_sum fun j _ => (hys j).2 _ (hys' j)

/-- **Proposition 5.E.1(i)** (MWG, p. 148), real form: if every `Y_j` is nonempty and profits are
bounded on each at `p`, the aggregate profits are bounded and `π*(p) = Σ_j π_j(p)`. -/
theorem proposition_5_E_1_i_real {Ys : Fin J → Set (Fin L → ℝ)} (hne : ∀ j, (Ys j).Nonempty)
    {p : Fin L → ℝ} (hb : ∀ j, BddAbove ((fun y => p ⬝ᵥ y) '' Ys j)) :
    BddAbove ((fun y => p ⬝ᵥ y) '' aggSet Ys) ∧ profit (aggSet Ys) p = ∑ j, profit (Ys j) p := by
  have hup : ∀ y ∈ aggSet Ys, p ⬝ᵥ y ≤ ∑ j, profit (Ys j) p := by
    rintro _ ⟨ys, hys, rfl⟩
    rw [dotProduct_finset_sum]
    exact Finset.sum_le_sum fun j _ => le_csSup (hb j) ⟨ys j, hys j, rfl⟩
  have hbdd : BddAbove ((fun y => p ⬝ᵥ y) '' aggSet Ys) :=
    ⟨_, by rintro _ ⟨y, hy, rfl⟩; exact hup y hy⟩
  refine ⟨hbdd, le_antisymm ?_ ?_⟩
  · obtain ⟨ys0, hys0⟩ : ∃ ys : Fin J → Fin L → ℝ, ∀ j, ys j ∈ Ys j :=
      ⟨fun j => (hne j).some, fun j => (hne j).some_mem⟩
    exact csSup_le ⟨_, ⟨_, ⟨ys0, hys0, rfl⟩, rfl⟩⟩ (by rintro _ ⟨y, hy, rfl⟩; exact hup y hy)
  · apply le_of_forall_pos_le_add
    intro ε hε
    have hεJ : 0 < ε / (J + 1) := by positivity
    have hex : ∀ j, ∃ y ∈ Ys j, profit (Ys j) p - ε / (J + 1) < p ⬝ᵥ y := by
      intro j
      obtain ⟨_, ⟨y, hy, rfl⟩, hlt⟩ := exists_lt_of_lt_csSup ((hne j).image _)
        (show profit (Ys j) p - ε / (J + 1) < profit (Ys j) p by linarith)
      exact ⟨y, hy, hlt⟩
    choose ys hys hlt using hex
    have hmem : ∑ j, ys j ∈ aggSet Ys := ⟨ys, hys, rfl⟩
    have h1 : p ⬝ᵥ ∑ j, ys j ≤ profit (aggSet Ys) p := le_csSup hbdd ⟨_, hmem, rfl⟩
    rw [dotProduct_finset_sum] at h1
    have h2 : ∑ j, (profit (Ys j) p - ε / (J + 1)) ≤ ∑ j, p ⬝ᵥ ys j :=
      Finset.sum_le_sum fun j _ => (hlt j).le
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at h2
    have h3 : (J : ℝ) * (ε / (J + 1)) ≤ ε := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith
    linarith

theorem ereal_coe_sum (a : Fin J → ℝ) : ((∑ j, a j : ℝ) : EReal) = ∑ j, (a j : EReal) := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, EReal.coe_add, ih]

theorem ereal_sum_ne_bot {x : Fin J → EReal} (h : ∀ j, x j ≠ ⊥) : ∑ j, x j ≠ ⊥ := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Fin.sum_univ_succ]
    exact EReal.add_ne_bot_iff.mpr ⟨h 0, ih fun j => h j.succ⟩

theorem ereal_sum_eq_top {x : Fin J → EReal} (h : ∀ j, x j ≠ ⊥) {k : Fin J} (hk : x k = ⊤) :
    ∑ j, x j = ⊤ := by
  classical
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k), hk]
  apply EReal.top_add_of_ne_bot
  induction (Finset.univ.erase k) using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact EReal.add_ne_bot_iff.mpr ⟨h a, ih⟩

theorem profitFn_ne_bot {Y : Set (Fin L → ℝ)} (hne : Y.Nonempty) (p : Fin L → ℝ) :
    profitFn Y p ≠ ⊥ := by
  obtain ⟨y, hy⟩ := hne
  exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (le_profitFn (p := p) hy)

/-- **Proposition 5.E.1(i)** (MWG, p. 148). For nonempty `Y_j` and every `p`, the aggregate
profit function is the sum of the individual ones: `π*(p) = Σ_j π_j(p)` in `(-∞, +∞]`. -/
theorem proposition_5_E_1_i {Ys : Fin J → Set (Fin L → ℝ)} (hne : ∀ j, (Ys j).Nonempty)
    (p : Fin L → ℝ) : profitFn (aggSet Ys) p = ∑ j, profitFn (Ys j) p := by
  have hneagg : (aggSet Ys).Nonempty :=
    ⟨_, ⟨fun j => (hne j).some, fun j => (hne j).some_mem, rfl⟩⟩
  by_cases hb : ∀ j, BddAbove ((fun y => p ⬝ᵥ y) '' Ys j)
  · obtain ⟨hbagg, heq⟩ := proposition_5_E_1_i_real hne hb
    rw [profitFn_eq_coe hneagg hbagg, heq, ereal_coe_sum]
    exact Finset.sum_congr rfl fun j _ => (profitFn_eq_coe (hne j) (hb j)).symm
  · push Not at hb
    obtain ⟨k, hk⟩ := hb
    have htop : profitFn (Ys k) p = ⊤ := profitFn_eq_top hk
    rw [ereal_sum_eq_top (fun j => profitFn_ne_bot (hne j) p) htop]
    apply profitFn_eq_top
    intro ⟨m, hm⟩
    apply hk
    refine ⟨m - ∑ j ∈ Finset.univ.erase k, p ⬝ᵥ (hne j).some, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    classical
    set ys := Function.update (fun j => (hne j).some) k y with hys
    have hmem : ∑ j, ys j ∈ aggSet Ys := ⟨ys, fun j => by
      by_cases hj : j = k
      · subst hj; simp [hys, hy]
      · simp [hys, hj, (hne j).some_mem], rfl⟩
    have h1 := hm ⟨_, hmem, rfl⟩
    simp only at h1
    rw [dotProduct_finset_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ k)] at h1
    have : ∑ j ∈ Finset.univ.erase k, p ⬝ᵥ ys j =
        ∑ j ∈ Finset.univ.erase k, p ⬝ᵥ (hne j).some :=
      Finset.sum_congr rfl fun j hj => by
        rw [hys, Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    rw [this, hys, Function.update_self] at h1
    simp only
    linarith

/-- **Section 5.E** (MWG, p. 147), the aggregate law of supply:
`(p - p')·[y(p) - y(p')] ≥ 0` for `y ∈ Σ_j y_j(p)` and `y' ∈ Σ_j y_j(p')`. -/
theorem aggregate_law_of_supply {Ys : Fin J → Set (Fin L → ℝ)} {p p' y y' : Fin L → ℝ}
    (hy : y ∈ aggSupply Ys p) (hy' : y' ∈ aggSupply Ys p') : 0 ≤ (p - p') ⬝ᵥ (y - y') := by
  rw [← proposition_5_E_1_ii] at hy hy'
  exact law_of_supply hy hy'

/-- **Section 5.E** (MWG, p. 147). Symmetry and positive semidefiniteness are preserved by
sums: if each `Dy_j(p)` is symmetric and positive semidefinite, so is `Σ_j Dy_j(p)`. -/
theorem sum_symm_psd (Ds : Fin J → Matrix (Fin L) (Fin L) ℝ)
    (hsym : ∀ j, ∀ a b, Ds j a b = Ds j b a) (hpsd : ∀ j, PosSemidefMWG (Ds j)) :
    (∀ a b, (∑ j, Ds j) a b = (∑ j, Ds j) b a) ∧ PosSemidefMWG (∑ j, Ds j) := by
  refine ⟨fun a b => ?_, fun z => ?_⟩
  · simp only [Matrix.sum_apply]
    exact Finset.sum_congr rfl fun j _ => hsym j a b
  · rw [Matrix.sum_mulVec, dotProduct_finset_sum]
    exact Finset.sum_nonneg fun j _ => hpsd j z

/-- If profits are finite near `p̄` and `π` has derivative `D` at `p̄`, every
profit-maximizing plan `ȳ` at `p̄` is the gradient: `D = (q ↦ ȳ·q)`. -/
theorem profit_fderiv_eq_of_mem_supply {Y : Set (Fin L → ℝ)} {p y : Fin L → ℝ}
    (hb : ∀ᶠ q in 𝓝 p, BddAbove ((fun y => q ⬝ᵥ y) '' Y))
    {D : (Fin L → ℝ) →L[ℝ] ℝ} (hD : HasFDerivAt (profit Y) D p) (hy : y ∈ supply Y p) :
    D = dualityDotCLM y := by
  have hmax : IsLocalMin (fun q => profit Y q - q ⬝ᵥ y) p := by
    filter_upwards [hb] with q hq
    rw [profit_eq_of_mem_supply hy, sub_self]
    exact sub_nonneg.mpr (le_csSup hq ⟨y, hy.1, rfl⟩)
  have hd := hD.sub (duality_hasFDerivAt_dot_left y p)
  have := hmax.hasFDerivAt_eq_zero hd
  have h2 : D = dualityDotCLM y := sub_eq_zero.mp this
  exact h2

/-- **Exercise 5.E.1** (MWG, p. 163). Assume each `π_j` is differentiable at `p̄` (finite nearby)
with gradient `g_j`, and `π* = Σ_j π_j` near `p̄`. Then every aggregate profit maximizer at `p̄`
is `Σ_j g_j`; with Hotelling's lemma `g_j = y_j(p̄)` this gives `y*(p̄) = Σ_j y_j(p̄)`. -/
theorem exercise_5_E_1 {Ys : Fin J → Set (Fin L → ℝ)} {p : Fin L → ℝ}
    {g : Fin J → Fin L → ℝ}
    (hd : ∀ j, HasFDerivAt (profit (Ys j)) (dualityDotCLM (g j)) p)
    (hsum : ∀ᶠ q in 𝓝 p, profit (aggSet Ys) q = ∑ j, profit (Ys j) q)
    (hb : ∀ᶠ q in 𝓝 p, BddAbove ((fun y => q ⬝ᵥ y) '' aggSet Ys))
    {y : Fin L → ℝ} (hy : y ∈ supply (aggSet Ys) p) : y = ∑ j, g j := by
  have hD : HasFDerivAt (profit (aggSet Ys)) (∑ j, dualityDotCLM (g j)) p := by
    have := HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ => hd j)
    exact this.congr_of_eventuallyEq hsum
  have h1 := profit_fderiv_eq_of_mem_supply hb hD hy
  have h2 : (∑ j, dualityDotCLM (g j)) = dualityDotCLM (L := L) (∑ j, g j) := by
    ext q
    simp only [FunLike.coe_sum, Finset.sum_apply, dualityDotCLM_apply]
    rw [dotProduct_comm, dotProduct_finset_sum]
    exact Finset.sum_congr rfl fun j _ => dotProduct_comm _ _
  rw [h2] at h1
  exact (dualityDotCLM_injective h1).symm

/-- Free disposal and convexity pass to the aggregate production set. -/
theorem aggSet_convex_freeDisposal {Ys : Fin J → Set (Fin L → ℝ)} (hc : ∀ j, Convex ℝ (Ys j))
    (hfd : ∀ j, FreeDisposal (Ys j)) (hJ : 0 < J) :
    Convex ℝ (aggSet Ys) ∧ FreeDisposal (aggSet Ys) := by
  classical
  constructor
  · rintro _ ⟨ys, hys, rfl⟩ _ ⟨ys', hys', rfl⟩ a b ha hb hab
    refine ⟨fun j => a • ys j + b • ys' j, fun j => hc j (hys j) (hys' j) ha hb hab, ?_⟩
    rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  · rintro _ ⟨ys, hys, rfl⟩ y' hy'
    set k : Fin J := ⟨0, hJ⟩
    refine ⟨Function.update ys k (ys k - (∑ j, ys j - y')), fun j => ?_, ?_⟩
    · by_cases hj : j = k
      · subst hj
        simp only [Function.update_self]
        exact hfd _ _ (hys _) _ (sub_le_self _ (sub_nonneg.mpr hy'))
      · simp only [Function.update_of_ne hj]
        exact hys j
    · rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k), Function.update_self]
      have : ∑ j ∈ Finset.univ.erase k, Function.update ys k (ys k - (∑ j, ys j - y')) j =
          ∑ j ∈ Finset.univ.erase k, ys j :=
        Finset.sum_congr rfl fun j hj => Function.update_of_ne (Finset.ne_of_mem_erase hj) _ _
      rw [this, ← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
      abel

/-- **Exercise 5.E.3** (MWG, p. 163), corrected: if the `Y_j` are nonempty, convex, with free
disposal, and `Σ_j Y_j` is closed, then `Σ_j Y_j = {y : p·y ≤ Σ_j π_j(p) for all p ≥ 0}`. -/
theorem exercise_5_E_3 {Ys : Fin J → Set (Fin L → ℝ)} (hne : ∀ j, (Ys j).Nonempty)
    (hc : ∀ j, Convex ℝ (Ys j)) (hfd : ∀ j, FreeDisposal (Ys j)) (hJ : 0 < J)
    (hcl : IsClosed (aggSet Ys)) :
    aggSet Ys = {y | ∀ p : Fin L → ℝ, 0 ≤ p →
      ((p ⬝ᵥ y : ℝ) : EReal) ≤ ∑ j, profitFn (Ys j) p} := by
  obtain ⟨hcagg, hfdagg⟩ := aggSet_convex_freeDisposal hc hfd hJ
  rw [proposition_5_C_1_iii_nonneg hcl hcagg hfdagg]
  ext y
  simp only [Set.mem_ofPred_eq, proposition_5_E_1_i hne]

/-- **Exercise 5.E.3** (MWG, p. 163) with prices `p ≫ 0` as printed, under the extra hypothesis
that aggregate profits are bounded at some `p₀ ≫ 0`. -/
theorem exercise_5_E_3_pos {Ys : Fin J → Set (Fin L → ℝ)} (hne : ∀ j, (Ys j).Nonempty)
    (hc : ∀ j, Convex ℝ (Ys j)) (hfd : ∀ j, FreeDisposal (Ys j)) (hJ : 0 < J)
    (hcl : IsClosed (aggSet Ys)) {p₀ : Fin L → ℝ} (hp₀ : StrictlyPositive p₀)
    (hb₀ : BddAbove ((fun y => p₀ ⬝ᵥ y) '' aggSet Ys)) :
    aggSet Ys = {y | ∀ p : Fin L → ℝ, StrictlyPositive p →
      ((p ⬝ᵥ y : ℝ) : EReal) ≤ ∑ j, profitFn (Ys j) p} := by
  obtain ⟨hcagg, hfdagg⟩ := aggSet_convex_freeDisposal hc hfd hJ
  rw [proposition_5_C_1_iii hcl hcagg hfdagg hp₀ hb₀]
  ext y
  simp only [Set.mem_ofPred_eq, proposition_5_E_1_i hne]

/-- **Exercise 5.E.3** is false as printed (correction): for `J = 1` and `Y₁ = {y ∈ ℝ² : y₂ ≤ 0}`
(nonempty, convex, closed, free disposal), `(0, 1) ∉ Y₁` but `p·(0, 1) ≤ π₁(p) = +∞` for every
`p ≫ 0`. -/
theorem exercise_5_E_3_counterexample :
    let Ys : Fin 1 → Set (Fin 2 → ℝ) := fun _ => {y | y 1 ≤ 0}
    ![0, 1] ∉ aggSet Ys ∧ ∀ p : Fin 2 → ℝ, StrictlyPositive p →
      ((p ⬝ᵥ ![0, 1] : ℝ) : EReal) ≤ ∑ j, profitFn (Ys j) p := by
  intro Ys
  obtain ⟨-, -, -, -, htop, hnot, -⟩ := proposition_5_C_1_iii_counterexample
  refine ⟨?_, fun p hp => ?_⟩
  · rintro ⟨ys, hys, hsum⟩
    apply hnot
    rw [hsum, Fin.sum_univ_one]
    exact hys 0
  · rw [Fin.sum_univ_one]
    have := htop p hp
    simp only [Ys] at this ⊢
    rw [this]
    exact le_top

end MWG.Production
