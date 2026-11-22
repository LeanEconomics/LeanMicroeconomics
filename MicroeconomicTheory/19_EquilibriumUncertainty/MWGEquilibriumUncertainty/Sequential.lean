/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGEquilibriumUncertainty.RiskSharing

/-!
# Sequential trade and Radner equilibrium (MWG Section 19.D, pp. 694-699)

Two dates, uncertainty resolved at `t = 1`, no consumption at `t = 0`. The physical good in which
contingent trade (and later asset returns) is denominated is a parameter `g : Fin L` (the book's
"good 1").

* The Radner budget set and Radner equilibrium for an asset structure with `S × K` return matrix
  `R` (`radnerFeasible`, `IsRadnerEqm`): this is Definition 19.E.2; **Definition 19.D.1** is the
  case `K = S`, `R = I` of contingent trade in good `g` (`IsRadnerEqmD`, `definition_19_D_1`).
* Homogeneity of the budget constraints (p. 696): budget sets are unchanged when each spot price
  vector and the date-0 prices are rescaled (`radnerFeasible_rescale`).
* **Proposition 19.D.1**: (i) Arrow-Debreu equilibria are Radner equilibria with `q_s = p_{gs}`;
  (ii) Radner equilibria with `q ≫ 0`, `p_{gs} > 0` give Arrow-Debreu budget sets for the prices
  `μ_s p_s`, `μ_s = q_s / p_{gs}`. As printed, (ii) concludes an Arrow-Debreu equilibrium, whose
  definition (19.C.1(iii)) requires market clearing with *equality*, while a Radner equilibrium
  only requires `∑ᵢ x*ᵢ ≤ ∑ᵢ ωᵢ`. Without monotonicity this fails
  (`proposition_19_D_1_ii_counterexample`); it holds with strongly monotone utilities
  (`proposition_19_D_1_ii`), and in general with the inequality (`proposition_19_D_1_ii_le`).
  Correction 2.
* **p. 694 and footnote 5**: at an Arrow-Debreu equilibrium there is no incentive to retrade
  ex post (`no_expost_trade`), and the state-`s` contingent prices are equilibrium spot prices
  (`footnote_19_5`).
* **Footnote 7** (initial endowments of contingent commodities), **footnote 8** and **Exercise
  19.D.1** (contingent commodities paying dollars, and the normalizations).
* **Example 19.D.1** and **Exercise 19.D.2**: the symmetric two-state, two-good economy.
* **Exercise 19.D.3** (consumption at `t = 0`) and **Exercise 19.D.4** (three dates, binary tree):
  Proposition 19.D.1 remains valid.
-/

namespace MWG.EquilibriumUncertainty

open Matrix

variable {S L K : ℕ} {ι : Type*} [Fintype ι]

/-- **Definition 19.E.2(i)** (MWG, p. 701; Definition 19.D.1 with `R = I`). The plan `(x, z)` is in
consumer's budget set: `x ≥ 0`, (a) `q·z ≤ 0`, (b) `p_s·x_s ≤ p_s·ω_s + p_{gs} ∑_k r_{sk} z_k` in
every state. -/
def radnerFeasible (g : Fin L) (R : Matrix (Fin S) (Fin K) ℝ) (q : Fin K → ℝ) (p ω : CVec S L)
    (x : CVec S L) (z : Fin K → ℝ) : Prop :=
  NonnegC x ∧ q ⬝ᵥ z ≤ 0 ∧ ∀ s, p s ⬝ᵥ x s ≤ p s ⬝ᵥ ω s + p s g * (R *ᵥ z) s

/-- **Definition 19.E.2** (MWG, p. 701). `(q, p, z*, x*)` is a Radner equilibrium: (i) every
`(z*ᵢ, x*ᵢ)` solves consumer `i`'s problem; (ii) `∑ᵢ z*_{ki} ≤ 0` and `∑ᵢ x*_{si} ≤ ∑ᵢ ω_{si}`. -/
def IsRadnerEqm (g : Fin L) (R : Matrix (Fin S) (Fin K) ℝ) (U : ι → CVec S L → ℝ)
    (ω : ι → CVec S L) (q : Fin K → ℝ) (p : CVec S L) (x : ι → CVec S L) (z : ι → Fin K → ℝ) :
    Prop :=
  (∀ i, radnerFeasible g R q p (ω i) (x i) (z i) ∧
    ∀ x' z', radnerFeasible g R q p (ω i) x' z' → U i x' ≤ U i (x i)) ∧
    (∀ k, ∑ i, z i k ≤ 0) ∧ ∑ i, x i ≤ ∑ i, ω i

/-- **Definition 19.D.1** (MWG, p. 696). A Radner equilibrium with contingent trade in good `g`
only: the asset structure of the `S` contingent commodities `gs` (`R = I`). -/
def IsRadnerEqmD (g : Fin L) (U : ι → CVec S L → ℝ) (ω : ι → CVec S L) (q : Fin S → ℝ)
    (p : CVec S L) (x : ι → CVec S L) (z : ι → Fin S → ℝ) : Prop :=
  IsRadnerEqm g (1 : Matrix (Fin S) (Fin S) ℝ) U ω q p x z

/-- **Definition 19.D.1** (MWG, p. 696), unfolded: problem (19.D.1) with constraints
(i) `∑_s q_s z_s ≤ 0` and (ii) `p_s·x_s ≤ p_s·ω_s + p_{gs} z_s`, and market clearing. -/
theorem definition_19_D_1 (g : Fin L) (U : ι → CVec S L → ℝ) (ω : ι → CVec S L)
    (q : Fin S → ℝ) (p : CVec S L) (x : ι → CVec S L) (z : ι → Fin S → ℝ) :
    IsRadnerEqmD g U ω q p x z ↔
      (∀ i, (NonnegC (x i) ∧ q ⬝ᵥ z i ≤ 0 ∧ ∀ s, p s ⬝ᵥ x i s ≤ p s ⬝ᵥ ω i s + p s g * z i s) ∧
        ∀ x' z', (NonnegC x' ∧ q ⬝ᵥ z' ≤ 0 ∧ ∀ s, p s ⬝ᵥ x' s ≤ p s ⬝ᵥ ω i s + p s g * z' s) →
          U i x' ≤ U i (x i)) ∧
      (∀ s, ∑ i, z i s ≤ 0) ∧ ∑ i, x i ≤ ∑ i, ω i := by
  simp [IsRadnerEqmD, IsRadnerEqm, radnerFeasible, one_mulVec]

/-- **p. 696**. All budget constraints are homogeneous of degree zero: rescaling the date-0 prices
by `c > 0` and the spot prices of state `s` by `d_s > 0` leaves the budget set unchanged (so one
can put `p_{gs} = 1` in every state and, say, `q₁ = 1`). -/
theorem radnerFeasible_rescale (g : Fin L) (R : Matrix (Fin S) (Fin K) ℝ) (q : Fin K → ℝ)
    (p ω x : CVec S L) (z : Fin K → ℝ) {c : ℝ} (hc : 0 < c) {d : Fin S → ℝ} (hd : ∀ s, 0 < d s) :
    radnerFeasible g R (c • q) (fun s => d s • p s) ω x z ↔ radnerFeasible g R q p ω x z := by
  unfold radnerFeasible
  simp only [smul_dotProduct, smul_eq_mul, Pi.smul_apply]
  refine and_congr Iff.rfl (and_congr ⟨fun h => ?_, fun h => mul_nonpos_of_nonneg_of_nonpos
    hc.le h⟩ (forall_congr' fun s => ?_))
  · exact nonpos_of_mul_nonpos_right h hc
  · constructor
    · intro h
      have : d s * (p s ⬝ᵥ x s) ≤ d s * (p s ⬝ᵥ ω s + p s g * (R *ᵥ z) s) := by linarith
      exact le_of_mul_le_mul_left this (hd s)
    · intro h
      nlinarith [hd s]

/-! ## Proposition 19.D.1 -/

/-- The Arrow-Debreu budget set `{x ≥ 0 : ∑_s p_s·(x_s - ω_s) ≤ 0}` (proof of Proposition
19.D.1). -/
def adBudget (p ω : CVec S L) : Set (CVec S L) := {x | NonnegC x ∧ cval p x ≤ cval p ω}

/-- **Proposition 19.D.1, proof of (i)** (MWG, p. 697). With `q_s = p_{gs} > 0`, the Arrow-Debreu
budget set equals the Radner budget set `B_i^R`. -/
theorem adBudget_eq_radner (g : Fin L) {p : CVec S L} (hp : ∀ s, 0 < p s g) (ω x : CVec S L) :
    x ∈ adBudget p ω ↔ ∃ z, radnerFeasible g 1 (fun s => p s g) p ω x z := by
  constructor
  · rintro ⟨hx, hb⟩
    refine ⟨fun s => p s ⬝ᵥ (x s - ω s) / p s g, hx, ?_, fun s => ?_⟩
    · simp only [dotProduct, mul_div_cancel₀ _ (hp _).ne']
      have : cval p x - cval p ω = ∑ s, p s ⬝ᵥ (x s - ω s) := by
        simp [cval, dotProduct_sub, Finset.sum_sub_distrib]
      simp only [dotProduct] at this
      linarith
    · simp only [one_mulVec, mul_div_cancel₀ _ (hp s).ne', dotProduct_sub]
      linarith
  · rintro ⟨z, hx, hq, hs⟩
    refine ⟨hx, ?_⟩
    simp only [one_mulVec] at hs
    have h1 : ∑ s, (p s ⬝ᵥ x s - p s ⬝ᵥ ω s) ≤ ∑ s, p s g * z s :=
      Finset.sum_le_sum fun s _ => by linarith [hs s]
    simp only [dotProduct] at hq
    rw [Finset.sum_sub_distrib] at h1
    unfold cval
    linarith

/-- **Proposition 19.D.1(i)** (MWG, p. 697). If `x*` and `p` with `p_{gs} > 0` form an Arrow-Debreu
equilibrium, then `q_s = p_{gs}`, the spot prices `p_s` and the contingent trades
`z*_{si} = p_s·(x*_{si} - ω_{si}) / p_{gs}` form, with `x*`, a Radner equilibrium. -/
theorem proposition_19_D_1_i (g : Fin L) {U : ι → CVec S L → ℝ} {ω x : ι → CVec S L}
    {p : CVec S L} (hp : ∀ s, 0 < p s g) (h : IsADEqmU U ω x p) :
    IsRadnerEqmD g U ω (fun s => p s g) p x
      (fun i s => p s ⬝ᵥ (x i s - ω i s) / p s g) := by
  refine ⟨fun i => ⟨?_, fun x' z' hf => ?_⟩, fun s => ?_, h.2.le⟩
  · obtain ⟨z, hz⟩ := (adBudget_eq_radner g hp (ω i) (x i)).mp (h.1 i).1
    refine ⟨hz.1, ?_, fun s => ?_⟩
    · simp only [dotProduct, mul_div_cancel₀ _ (hp _).ne']
      have : cval p (x i) - cval p (ω i) = ∑ s, p s ⬝ᵥ (x i s - ω i s) := by
        simp [cval, dotProduct_sub, Finset.sum_sub_distrib]
      simp only [dotProduct] at this
      linarith [(h.1 i).1.2]
    · simp only [one_mulVec, mul_div_cancel₀ _ (hp s).ne', dotProduct_sub]
      linarith
  · exact (h.1 i).2 x' ((adBudget_eq_radner g hp (ω i) x').mpr ⟨z', hf⟩).1
      ((adBudget_eq_radner g hp (ω i) x').mpr ⟨z', hf⟩).2
  · rw [← Finset.sum_div, ← dotProduct_sum, Finset.sum_sub_distrib]
    have : ∑ i, x i s = ∑ i, ω i s := by
      have := congrFun h.2 s; simpa [Finset.sum_apply] using this
    rw [this, sub_self, dotProduct_zero, zero_div]

/-- **Proposition 19.D.1, proof of (ii)** (MWG, p. 697). With `q ≥ 0` and `p_{gs} > 0`, put
`μ_s = q_s / p_{gs}`; the Radner budget set equals the Arrow-Debreu budget set at the prices
`μ_s p_s`. -/
theorem radner_eq_adBudget (g : Fin L) {q : Fin S → ℝ} (hq : ∀ s, 0 ≤ q s) {p : CVec S L}
    (hp : ∀ s, 0 < p s g) (ω x : CVec S L) :
    (∃ z, radnerFeasible g 1 q p ω x z) ↔
      x ∈ adBudget (fun s => (q s / p s g) • p s) ω := by
  constructor
  · rintro ⟨z, hx, hqz, hs⟩
    refine ⟨hx, ?_⟩
    simp only [one_mulVec] at hs
    simp only [cval, smul_dotProduct, smul_eq_mul]
    have h1 : ∀ s, q s / p s g * (p s ⬝ᵥ x s) ≤ q s / p s g * (p s ⬝ᵥ ω s) + q s * z s := by
      intro s
      have hμ : 0 ≤ q s / p s g := div_nonneg (hq s) (hp s).le
      have := mul_le_mul_of_nonneg_left (hs s) hμ
      rw [mul_add, ← mul_assoc, div_mul_cancel₀ _ (hp s).ne'] at this
      exact this
    have h2 := Finset.sum_le_sum fun s (_ : s ∈ Finset.univ) => h1 s
    rw [Finset.sum_add_distrib] at h2
    simp only [dotProduct] at hqz
    linarith
  · rintro ⟨hx, hb⟩
    refine ⟨fun s => p s ⬝ᵥ (x s - ω s) / p s g, hx, ?_, fun s => ?_⟩
    · simp only [cval, smul_dotProduct, smul_eq_mul] at hb
      have e : q ⬝ᵥ (fun s => p s ⬝ᵥ (x s - ω s) / p s g) =
          ∑ s, q s / p s g * (p s ⬝ᵥ x s) - ∑ s, q s / p s g * (p s ⬝ᵥ ω s) := by
        simp only [dotProduct_sub]
        rw [dotProduct, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun s _ => by field_simp
      rw [e]; linarith
    · simp only [one_mulVec, mul_div_cancel₀ _ (hp s).ne', dotProduct_sub]
      linarith

/-- An allocation that clears with `≤` and has binding budgets at prices `c ≫ 0` clears exactly. -/
theorem clear_eq_of_binding {c : CVec S L} (hc : ∀ s l, 0 < c s l) {ω x : ι → CVec S L}
    (hle : ∑ i, x i ≤ ∑ i, ω i) (hbind : ∀ i, cval c (x i) = cval c (ω i)) :
    ∑ i, x i = ∑ i, ω i := by
  have hsum : cval c (∑ i, ω i - ∑ i, x i) = 0 := by
    rw [cval_sub, cval_sum, cval_sum, Finset.sum_congr rfl fun i _ => (hbind i).symm, sub_self]
  have hnn : ∀ s l, 0 ≤ (∑ i, ω i - ∑ i, x i) s l := fun s l => by
    have := hle s l; simp only [Pi.sub_apply]; linarith
  have hz : ∀ s l, (∑ i, ω i - ∑ i, x i) s l = 0 := by
    intro s l
    unfold cval dotProduct at hsum
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun s _ => Finset.sum_nonneg fun l _ =>
      mul_nonneg (hc s l).le (hnn s l)).mp hsum s (Finset.mem_univ _)
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg fun l _ =>
      mul_nonneg (hc s l).le (hnn s l)).mp h1 l (Finset.mem_univ _)
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h (hc s l).ne'
    · exact h
  funext s l
  have := hz s l
  simp only [Pi.sub_apply] at this
  linarith

/-- **Proposition 19.D.1(ii)**, the part that holds as stated for any utilities: if
`(q, p, z*, x*)` is a Radner equilibrium with `q ≥ 0` and `p_{gs} > 0`, then with
`μ_s = q_s / p_{gs}` every `x*ᵢ` is utility maximizing in the Arrow-Debreu budget set at the
prices `(μ_s p_s)`, and `∑ᵢ x*ᵢ ≤ ∑ᵢ ωᵢ`. -/
theorem proposition_19_D_1_ii_le (g : Fin L) {U : ι → CVec S L → ℝ} {ω x : ι → CVec S L}
    {q : Fin S → ℝ} (hq : ∀ s, 0 ≤ q s) {p : CVec S L} (hp : ∀ s, 0 < p s g)
    {z : ι → Fin S → ℝ} (h : IsRadnerEqmD g U ω q p x z) :
    (∀ i, (NonnegC (x i) ∧ cval (fun s => (q s / p s g) • p s) (x i) ≤
        cval (fun s => (q s / p s g) • p s) (ω i)) ∧
      ∀ x', NonnegC x' → cval (fun s => (q s / p s g) • p s) x' ≤
        cval (fun s => (q s / p s g) • p s) (ω i) → U i x' ≤ U i (x i)) ∧
      ∑ i, x i ≤ ∑ i, ω i := by
  refine ⟨fun i => ⟨(radner_eq_adBudget g hq hp (ω i) (x i)).mp ⟨z i, (h.1 i).1⟩,
    fun x' hx' hb => ?_⟩, h.2.2⟩
  obtain ⟨z', hz'⟩ := (radner_eq_adBudget g hq hp (ω i) x').mpr ⟨hx', hb⟩
  exact (h.1 i).2 x' z' hz'

/-- **Proposition 19.D.1(ii)** (MWG, p. 697), with strongly monotone utilities (and `S, L ≥ 1`):
a Radner equilibrium with `q ≫ 0` and `p ≫ 0` gives the Arrow-Debreu equilibrium `x*` at the
contingent prices `(μ₁ p₁, …, μ_S p_S)`, `μ_s = q_s / p_{gs} > 0`. -/
theorem proposition_19_D_1_ii [NeZero S] [NeZero L] (g : Fin L) {U : ι → CVec S L → ℝ}
    (hU : ∀ i, StronglyMonotoneC (U i)) {ω x : ι → CVec S L} {q : Fin S → ℝ}
    (hq : ∀ s, 0 < q s) {p : CVec S L} (hp : ∀ s l, 0 < p s l) {z : ι → Fin S → ℝ}
    (h : IsRadnerEqmD g U ω q p x z) :
    IsADEqmU U ω x (fun s => (q s / p s g) • p s) := by
  obtain ⟨hopt, hle⟩ := proposition_19_D_1_ii_le g (fun s => (hq s).le) (fun s => hp s g) h
  have hbind : ∀ i, cval (fun s => (q s / p s g) • p s) (x i) =
      cval (fun s => (q s / p s g) • p s) (ω i) := by
    intro i
    refine le_antisymm (hopt i).1.2 (not_lt.mp fun hlt => ?_)
    obtain ⟨x', hle', hne, hc⟩ := exists_larger_cheap (fun s => (q s / p s g) • p s) (x i)
      (sub_pos.mpr hlt)
    have hx := (hopt i).1.1
    have := (hopt i).2 x' (fun s l => (hx s l).trans (hle' s l)) (by linarith)
    linarith [hU i _ _ hx hle' hne]
  refine ⟨hopt, clear_eq_of_binding (fun s l => ?_) hle hbind⟩
  simp only [Pi.smul_apply, smul_eq_mul]
  exact mul_pos (div_pos (hq s) (hp s g)) (hp s l)

/-- **Proposition 19.D.1(ii)** as printed fails without monotonicity (correction 2): one state,
one good, one consumer with endowment `1` and constant utility. `x* = 0`, `z* = 0` with `q = 1`,
`p = 1` is a Radner equilibrium, but no contingent price vector makes `x*` an Arrow-Debreu
equilibrium, since Definition 19.C.1(iii) requires `∑ᵢ x*ᵢ = ∑ᵢ ωᵢ`. -/
theorem proposition_19_D_1_ii_counterexample :
    IsRadnerEqmD (S := 1) (L := 1) (ι := Fin 1) 0 (fun _ _ => 0) (fun _ _ _ => 1) (fun _ => 1)
        (fun _ _ => 1) (fun _ _ _ => 0) (fun _ _ => 0) ∧
      ∀ c : CVec 1 1,
        ¬ IsADEqmU (ι := Fin 1) (fun _ _ => 0) (fun _ _ _ => 1) (fun _ _ _ => 0) c := by
  refine ⟨⟨fun _ => ⟨⟨fun _ _ => le_rfl, by simp, fun _ => by simp [dotProduct]⟩,
    fun _ _ _ => le_rfl⟩,
    fun _ => by simp, fun _ _ => by simp⟩, fun c hc => ?_⟩
  have := congrFun (congrFun hc.2 0) 0
  simp at this

/-! ## No ex post trade (p. 694) and footnote 5 -/

/-- **p. 694**. If the allocation `x*` is Pareto optimal (as Arrow-Debreu equilibrium allocations
are, `adEqmU_paretoOptimal`), then after any state `s` is revealed no reallocation of the state-`s`
endowments makes every consumer at least as well off and some consumer better off: ex ante Pareto
optimality implies ex post Pareto optimality. -/
theorem no_expost_trade {U : ι → CVec S L → ℝ} {ω x : ι → CVec S L}
    (hpo : IsParetoOptimalU U ω x) (s : Fin S) :
    ¬ ∃ y : ι → Fin L → ℝ, (∀ i l, 0 ≤ y i l) ∧ ∑ i, y i ≤ ∑ i, ω i s ∧
      (∀ i, U i (x i) ≤ U i (Function.update (x i) s (y i))) ∧
      ∃ i, U i (x i) < U i (Function.update (x i) s (y i)) := by
  classical
  rintro ⟨y, hy, hys, hge, k, hk⟩
  refine hpo.2 ⟨fun i => Function.update (x i) s (y i), ⟨fun i s' l => ?_, fun s' l => ?_⟩,
    hge, k, hk⟩
  · by_cases hs : s' = s
    · subst hs; simp [hy i l]
    · have e : Function.update (x i) s (y i) s' = x i s' := Function.update_of_ne hs _ _
      simp only [e]; exact hpo.1.1 i s' l
  · by_cases hs : s' = s
    · subst hs
      have := hys l
      simpa [Finset.sum_apply] using this
    · have := hpo.1.2 s' l
      simpa [Finset.sum_apply, Function.update_of_ne hs] using this

/-- **Footnote 5** (MWG, p. 694). If `x*` maximizes `U` on the Arrow-Debreu budget set, then for
every state `s`, `x*_s` maximizes `U(x*₁, …, x_s, …, x*_S)` subject to
`p_s·(x_s - ω_s) ≤ p_s·(x*_s - ω_s)`: the state-`s` contingent prices are spot prices at which the
initial vector `(x*_{s1}, …, x*_{sI})` is an equilibrium with null excess demand. -/
theorem footnote_19_5 {U : CVec S L → ℝ} {p ω x : CVec S L} (hx : x ∈ adBudget p ω)
    (hmax : ∀ x' ∈ adBudget p ω, U x' ≤ U x) (s : Fin S) (y : Fin L → ℝ) (hy : ∀ l, 0 ≤ y l)
    (hb : p s ⬝ᵥ (y - ω s) ≤ p s ⬝ᵥ (x s - ω s)) : U (Function.update x s y) ≤ U x := by
  classical
  refine hmax _ ⟨fun s' l => ?_, ?_⟩
  · by_cases hs : s' = s
    · subst hs; simp [hy l]
    · rw [Function.update_of_ne hs]; exact hx.1 s' l
  · have h1 : cval p (Function.update x s y) = cval p x + p s ⬝ᵥ (y - x s) := by
      unfold cval
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ s),
        ← Finset.add_sum_erase _ _ (Finset.mem_univ s)]
      have : ∑ s' ∈ Finset.univ.erase s, p s' ⬝ᵥ Function.update x s y s' =
          ∑ s' ∈ Finset.univ.erase s, p s' ⬝ᵥ x s' :=
        Finset.sum_congr rfl fun s' hs' => by
          rw [Function.update_of_ne (Finset.ne_of_mem_erase hs')]
      rw [this, Function.update_self, dotProduct_sub]; ring
    rw [h1]
    rw [dotProduct_sub, dotProduct_sub] at hb
    rw [dotProduct_sub]
    linarith [hx.2]

/-! ## Footnotes 7-8 and Exercise 19.D.1 -/

/-- **Footnote 7** (MWG, p. 696). If good `g` available at `t = 1` in state `s` is regarded as an
initial endowment of the `s`-contingent commodity, the constraints become
(i') `∑_s q_s(z'_s - ω_{gs}) ≤ 0` and (ii') `p_s·x_s ≤ ∑_{l ≠ g} p_{ls} ω_{ls} + p_{gs} z'_s`; with
`z'_s = z_s + ω_{gs}` they are exactly the constraints of (19.D.1). -/
theorem footnote_19_7 (g : Fin L) (q : Fin S → ℝ) (p ω x : CVec S L) (z : Fin S → ℝ) :
    (q ⬝ᵥ (fun s => (z s + ω s g) - ω s g) ≤ 0 ∧
      ∀ s, p s ⬝ᵥ x s ≤ (p s ⬝ᵥ ω s - p s g * ω s g) + p s g * (z s + ω s g)) ↔
      (q ⬝ᵥ z ≤ 0 ∧ ∀ s, p s ⬝ᵥ x s ≤ p s ⬝ᵥ ω s + p s g * z s) := by
  have e1 : (fun s => (z s + ω s g) - ω s g) = z := by funext s; ring
  have e2 : ∀ s, (p s ⬝ᵥ ω s - p s g * ω s g) + p s g * (z s + ω s g) =
      p s ⬝ᵥ ω s + p s g * z s := fun s => by ring
  simp only [e1, e2]

/-- **Exercise 19.D.1** (MWG, p. 726; footnote 8). If the `s`-contingent commodity pays one
dollar (instead of one unit of good `g`), the budget constraints are `∑_s q_s z_s ≤ 0` and
`p_s·x_s ≤ p_s·ω_s + z_s`. -/
def dollarFeasible (q : Fin S → ℝ) (p ω x : CVec S L) (z : Fin S → ℝ) : Prop :=
  NonnegC x ∧ q ⬝ᵥ z ≤ 0 ∧ ∀ s, p s ⬝ᵥ x s ≤ p s ⬝ᵥ ω s + z s

/-- **Exercise 19.D.1** (MWG, p. 726), the normalizations. The budget set is unchanged when
`q` is scaled by `c > 0` and, state by state, the spot prices are scaled by `d_s > 0` and `q_s` by
`1 / d_s` (the dollar claims are rescaled to `d_s z_s`). Hence one can normalize one price in
every spot market and one date-0 price, as in Section 19.D. -/
theorem exercise_19_D_1 (q : Fin S → ℝ) (p ω x : CVec S L) {c : ℝ} (hc : 0 < c)
    {d : Fin S → ℝ} (hd : ∀ s, 0 < d s) :
    (∃ z, dollarFeasible (fun s => c * q s / d s) (fun s => d s • p s) ω x z) ↔
      ∃ z, dollarFeasible q p ω x z := by
  constructor
  · rintro ⟨z, hx, hq, hs⟩
    refine ⟨fun s => z s / d s, hx, ?_, fun s => ?_⟩
    · simp only [dotProduct] at hq ⊢
      have : ∑ s, c * q s / d s * z s = c * ∑ s, q s * (z s / d s) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun s _ => by field_simp
      rw [this] at hq
      exact nonpos_of_mul_nonpos_right hq hc
    · have := hs s
      simp only [smul_dotProduct, smul_eq_mul] at this
      have h2 : d s * (p s ⬝ᵥ x s) ≤ d s * (p s ⬝ᵥ ω s + z s / d s) := by
        rw [mul_add, mul_div_cancel₀ _ (hd s).ne']; exact this
      exact le_of_mul_le_mul_left h2 (hd s)
  · rintro ⟨z, hx, hq, hs⟩
    refine ⟨fun s => d s * z s, hx, ?_, fun s => ?_⟩
    · simp only [dotProduct] at hq ⊢
      have : ∑ s, c * q s / d s * (d s * z s) = c * ∑ s, q s * z s := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun s _ => by field_simp [(hd s).ne']
      rw [this]
      exact mul_nonpos_of_nonneg_of_nonpos hc.le hq
    · simp only [smul_dotProduct, smul_eq_mul]
      nlinarith [hs s, hd s]

/-- **Exercise 19.D.1** (MWG, p. 726). With `p_{gs} > 0`, dollar-paying contingent commodities at
prices `q_s` give the same budget sets as good-`g`-paying ones at prices `q_s p_{gs}`. -/
theorem exercise_19_D_1_dollars_goods (g : Fin L) (q : Fin S → ℝ) {p : CVec S L}
    (hp : ∀ s, 0 < p s g) (ω x : CVec S L) :
    (∃ z, dollarFeasible q p ω x z) ↔
      ∃ z, radnerFeasible g 1 (fun s => q s * p s g) p ω x z := by
  constructor
  · rintro ⟨z, hx, hq, hs⟩
    refine ⟨fun s => z s / p s g, hx, ?_, fun s => ?_⟩
    · simp only [dotProduct] at hq ⊢
      have : ∑ s, q s * p s g * (z s / p s g) = ∑ s, q s * z s :=
        Finset.sum_congr rfl fun s _ => by field_simp [(hp s).ne']
      rw [this]; exact hq
    · simp only [one_mulVec, mul_div_cancel₀ _ (hp s).ne']; exact hs s
  · rintro ⟨z, hx, hq, hs⟩
    refine ⟨fun s => p s g * z s, hx, ?_, fun s => ?_⟩
    · simp only [dotProduct] at hq ⊢
      have : ∑ s, q s * (p s g * z s) = ∑ s, q s * p s g * z s :=
        Finset.sum_congr rfl fun s _ => by ring
      rw [this]; exact hq
    · have := hs s; simp only [one_mulVec] at this; exact this

end MWG.EquilibriumUncertainty
