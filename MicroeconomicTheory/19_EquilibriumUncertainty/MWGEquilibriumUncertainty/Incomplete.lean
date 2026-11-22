/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGEquilibriumUncertainty.LongLived

/-!
# Incomplete markets (MWG Section 19.F, pp. 709-713, Exercises 19.F.1-19.F.2)

* **Example 19.F.1 (sunspots)**: with common probabilities `π ≫ 0`, state-uniform strictly concave
  Bernoulli utilities and uniform endowments, Pareto optimal allocations are state independent
  (`example_19_F_1_po`); the printed argument needs `π_s > 0` (`example_19_F_1_needs_pos`,
  correction 7). Hence complete markets give sunspot-free equilibria (`example_19_F_1_complete`).
  With no assets (`K = 0`) a Radner equilibrium is exactly a choice of spot Walrasian equilibrium
  in each state (`radner_noAssets_iff`); selecting different spot equilibria gives a sunspot
  equilibrium (`sunspot_radnerEqm`), which is Pareto inefficient (`sunspot_not_po`). The spot
  economy with Leontief consumers has a continuum of equilibria (`leontief_spot_eqm`).
* **Exercise 19.F.1**: a sunspot-free Radner equilibrium exists for every asset structure, given a
  spot Walrasian equilibrium (`exercise_19_F_1`), and it is Pareto optimal when the spot
  equilibrium allocation is (`exercise_19_F_1_po`).
* **Definition 19.F.1** (constrained Pareto optimality, `L = 1`), footnote 26 and
  **Proposition 19.F.1**: Radner equilibria with one good are constrained Pareto optimal
  (`proposition_19_F_1`), assuming strongly monotone utilities and nonnegative nonzero returns.
* **Example 19.F.2 (Hart)**: Pareto-ranked Radner equilibria (`example_19_F_2`).
* **Exercise 19.F.2**: continuity, concavity and monotonicity of the induced utility `U*ᵢ`.
-/

namespace MWG.EquilibriumUncertainty

open Matrix

variable {S L K : ℕ} {ι : Type*} [Fintype ι]

/-! ## Example 19.F.1: sunspots -/

/-- **Example 19.F.1** (MWG, pp. 709-710). A sunspot set: common probabilities `π ≫ 0`, a state
uniform strictly concave Bernoulli utility `uᵢ` and endowments `ω_{si} = ωᵢ`. Every Pareto
optimal allocation is state independent. -/
theorem example_19_F_1_po {π : Fin S → ℝ} (hπ : ∀ s, 0 < π s) (hπ1 : ∑ s, π s = 1)
    {u : ι → (Fin L → ℝ) → ℝ} (hu : ∀ i, StrictConcaveOn ℝ {a | ∀ l, 0 ≤ a l} (u i))
    {ω₀ : ι → Fin L → ℝ} {x : ι → CVec S L}
    (hpo : IsParetoOptimalU (fun i => expUtil π fun _ => u i) (fun i _ => ω₀ i) x) :
    ∀ i s s', x i s = x i s' :=
  po_stateIndependent hπ hπ1 hu (fun _ _ => rfl) hpo

/-- **Example 19.F.1** (correction 7). The argument needs `π_s > 0`: with `π = (1, 0)`, one
consumer, one good, `u = √·` and `ω = (1, 1)`, the allocation `x = (1, 0)` is Pareto optimal but
not state independent. -/
theorem example_19_F_1_needs_pos :
    IsParetoOptimalU (ι := Fin 1) (fun _ => expUtil ![1, 0] fun _ (v : Fin 1 → ℝ) => √(v 0))
        (fun _ _ _ => 1) (fun _ => ![fun _ => 1, fun _ => 0]) ∧
      (fun (_ : Fin 1) => (![fun _ => 1, fun _ => 0] : CVec 2 1)) 0 0 ≠
        (fun (_ : Fin 1) => (![fun _ => 1, fun _ => 0] : CVec 2 1)) 0 1 := by
  refine ⟨⟨⟨fun _ s l => ?_, fun s l => ?_⟩, ?_⟩, ?_⟩
  · fin_cases s <;> simp
  · fin_cases s <;> simp
  · rintro ⟨x', ⟨hx', hf⟩, -, k, hk⟩
    fin_cases k
    have h1 : x' 0 0 0 ≤ 1 := by simpa using hf 0 0
    have hk' : 1 < √(x' 0 0 0) := by simpa [expUtil, Fin.sum_univ_two] using hk
    have : √(x' 0 0 0) ≤ 1 := by rw [Real.sqrt_le_one]; exact h1
    linarith
  · intro h
    have := congrFun h 0
    simp at this

/-- **Example 19.F.1** (MWG, p. 710). With complete markets (an Arrow-Debreu equilibrium, strongly
monotone utilities) the equilibria in a sunspot set are sunspot free. -/
theorem example_19_F_1_complete [NeZero S] [NeZero L] {π : Fin S → ℝ} (hπ : ∀ s, 0 < π s)
    (hπ1 : ∑ s, π s = 1) {u : ι → (Fin L → ℝ) → ℝ}
    (hu : ∀ i, StrictConcaveOn ℝ {a | ∀ l, 0 ≤ a l} (u i)) (hm : ∀ i, StronglyMonotoneL (u i))
    {ω₀ : ι → Fin L → ℝ} {x : ι → CVec S L} {p : CVec S L}
    (h : IsADEqmU (fun i => expUtil π fun _ => u i) (fun i _ => ω₀ i) x p) :
    ∀ i s s', x i s = x i s' :=
  example_19_F_1_po hπ hπ1 hu
    (adEqmU_paretoOptimal (fun i => expUtil_stronglyMonotone hπ fun _ => hm i) h)

/-- A spot Walrasian equilibrium (with the clearing condition `∑ yᵢ ≤ ∑ ωᵢ` of Definition 19.E.2)
of the exchange economy `{(uᵢ, ωᵢ)}` with `L` goods, at prices `p`. -/
def IsSpotEqm (u : ι → (Fin L → ℝ) → ℝ) (ω₀ : ι → Fin L → ℝ) (p : Fin L → ℝ)
    (y : ι → Fin L → ℝ) : Prop :=
  (∀ i, ((∀ l, 0 ≤ y i l) ∧ p ⬝ᵥ y i ≤ p ⬝ᵥ ω₀ i) ∧
    ∀ y' : Fin L → ℝ, (∀ l, 0 ≤ y' l) → p ⬝ᵥ y' ≤ p ⬝ᵥ ω₀ i → u i y' ≤ u i (y i)) ∧
    ∑ i, y i ≤ ∑ i, ω₀ i

/-- **Example 19.F.1** (MWG, p. 710). With no assets (`K = 0`), `(p₁, …, p_S)` and `x` form a Radner
equilibrium if and only if every `p_s` is a Walrasian equilibrium price vector, with allocation
`(x_{s1}, …, x_{sI})`, of the spot economy `{(uᵢ, ωᵢ)}` (probabilities `π ≫ 0`). -/
theorem radner_noAssets_iff (g : Fin L) {π : Fin S → ℝ} (hπ : ∀ s, 0 < π s)
    {u : ι → (Fin L → ℝ) → ℝ} {ω₀ : ι → Fin L → ℝ} {p : CVec S L} {x : ι → CVec S L}
    {q : Fin 0 → ℝ} {z : ι → Fin 0 → ℝ} (R : Matrix (Fin S) (Fin 0) ℝ) :
    IsRadnerEqm g R (fun i => expUtil π fun _ => u i) (fun i _ => ω₀ i) q p x z ↔
      ∀ s, IsSpotEqm u ω₀ (p s) (fun i => x i s) := by
  classical
  have hR : ∀ w : Fin 0 → ℝ, R *ᵥ w = 0 := fun w => by funext s; simp [mulVec, dotProduct]
  have hfeas : ∀ i x' (z' : Fin 0 → ℝ), radnerFeasible g R q p (fun _ => ω₀ i) x' z' ↔
      NonnegC x' ∧ ∀ s, p s ⬝ᵥ x' s ≤ p s ⬝ᵥ ω₀ i := by
    intro i x' z'
    simp [radnerFeasible, hR, dotProduct]
  constructor
  · intro h s
    refine ⟨fun i => ⟨⟨fun l => (h.1 i).1.1 s l, ((hfeas i _ _).mp (h.1 i).1).2 s⟩,
      fun y' hy' hb => ?_⟩, fun l => ?_⟩
    · have hf : radnerFeasible g R q p (fun _ => ω₀ i) (Function.update (x i) s y') (z i) := by
        rw [hfeas]
        refine ⟨fun s' l => ?_, fun s' => ?_⟩
        · by_cases hs : s' = s
          · subst hs; simp [hy' l]
          · rw [Function.update_of_ne hs]; exact (h.1 i).1.1 s' l
        · by_cases hs : s' = s
          · subst hs; simpa using hb
          · rw [Function.update_of_ne hs]; exact ((hfeas i _ _).mp (h.1 i).1).2 s'
      have := (h.1 i).2 _ _ hf
      simp only [expUtil] at this
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ s),
        ← Finset.add_sum_erase _ _ (Finset.mem_univ s), Function.update_self] at this
      have e : ∑ t ∈ Finset.univ.erase s, π t * u i (Function.update (x i) s y' t) =
          ∑ t ∈ Finset.univ.erase s, π t * u i (x i t) :=
        Finset.sum_congr rfl fun t ht => by rw [Function.update_of_ne (Finset.ne_of_mem_erase ht)]
      rw [e] at this
      exact le_of_mul_le_mul_left (by linarith) (hπ s)
    · have := h.2.2 s l
      simpa [Finset.sum_apply] using this
  · intro h
    refine ⟨fun i => ⟨(hfeas i _ _).mpr ⟨fun s l => ((h s).1 i).1.1 l,
      fun s => ((h s).1 i).1.2⟩, fun x' z' hf => ?_⟩, fun k => Fin.elim0 k, fun s l => ?_⟩
    · obtain ⟨hx', hb⟩ := (hfeas i _ _).mp hf
      exact Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left
        (((h s).1 i).2 (x' s) (hx' s) (hb s)) (hπ s).le
    · have := (h s).2 l
      simpa [Finset.sum_apply] using this

/-- **Example 19.F.1** (MWG, p. 710). Selecting a spot equilibrium in every state (possibly a
different one in different states) gives a Radner equilibrium without assets: a sunspot
equilibrium when the selected allocations differ. -/
theorem sunspot_radnerEqm (g : Fin L) {π : Fin S → ℝ} (hπ : ∀ s, 0 < π s)
    {u : ι → (Fin L → ℝ) → ℝ} {ω₀ : ι → Fin L → ℝ} {P : Fin S → Fin L → ℝ}
    {Y : Fin S → ι → Fin L → ℝ} (h : ∀ s, IsSpotEqm u ω₀ (P s) (Y s)) :
    IsRadnerEqm g (0 : Matrix (Fin S) (Fin 0) ℝ) (fun i => expUtil π fun _ => u i)
      (fun i _ => ω₀ i) Fin.elim0 P (fun i s => Y s i) fun _ => Fin.elim0 :=
  (radner_noAssets_iff g hπ _).mpr h

/-- **Example 19.F.1** (MWG, p. 710). A sunspot equilibrium allocation (state dependent) is not
Pareto optimal (common `π ≫ 0`, strictly concave `uᵢ`, uniform endowments). -/
theorem sunspot_not_po {π : Fin S → ℝ} (hπ : ∀ s, 0 < π s) (hπ1 : ∑ s, π s = 1)
    {u : ι → (Fin L → ℝ) → ℝ} (hu : ∀ i, StrictConcaveOn ℝ {a | ∀ l, 0 ≤ a l} (u i))
    {ω₀ : ι → Fin L → ℝ} {x : ι → CVec S L} {i : ι} {s s' : Fin S} (hne : x i s ≠ x i s') :
    ¬ IsParetoOptimalU (fun i => expUtil π fun _ => u i) (fun i _ => ω₀ i) x :=
  fun hpo => hne (example_19_F_1_po hπ hπ1 hu hpo i s s')

/-- A spot economy with a continuum of equilibria (the possibility invoked in Example 19.F.1):
two consumers with `u(y) = min(y₁, y₂)`, endowments `(1, 0)` and `(0, 1)`; for every `a ∈ [0, 1]`
the prices `(a, 1 - a)` with allocation `((a, a), (1 - a, 1 - a))` are an equilibrium. -/
theorem leontief_spot_eqm {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    IsSpotEqm (fun (_ : Fin 2) (y : Fin 2 → ℝ) => min (y 0) (y 1)) ![![1, 0], ![0, 1]] ![a, 1 - a]
      ![![a, a], ![1 - a, 1 - a]] := by
  refine ⟨fun i => ⟨⟨fun l => ?_, ?_⟩, fun y' hy' hb => ?_⟩, fun l => ?_⟩
  · fin_cases i <;> fin_cases l <;> simp <;> linarith
  · fin_cases i <;> simp [dotProduct, Fin.sum_univ_two] <;> nlinarith
  · fin_cases i
    · have hb' : a * y' 0 + (1 - a) * y' 1 ≤ a := by
        simpa [dotProduct, Fin.sum_univ_two] using hb
      change min (y' 0) (y' 1) ≤ min a a
      rw [min_self]
      rcases le_total (y' 0) (y' 1) with h | h
      · exact (min_le_left _ _).trans (by nlinarith)
      · exact (min_le_right _ _).trans (by nlinarith)
    · have hb' : a * y' 0 + (1 - a) * y' 1 ≤ 1 - a := by
        simpa [dotProduct, Fin.sum_univ_two] using hb
      change min (y' 0) (y' 1) ≤ min (1 - a) (1 - a)
      rw [min_self]
      rcases le_total (y' 0) (y' 1) with h | h
      · exact (min_le_left _ _).trans (by nlinarith)
      · exact (min_le_right _ _).trans (by nlinarith)
  · fin_cases l <;> simp [Fin.sum_univ_two]

/-! ## Exercise 19.F.1 -/

/-- **Exercise 19.F.1** (MWG, p. 728). In the sunspot model (common `π ≥ 0` summing to one,
state-uniform concave `uᵢ`, uniform endowments), for any asset structure `R` and any spot Walrasian
equilibrium `(p̂, ŷ)`, there is a sunspot-free Radner equilibrium: spot prices `p̂` in every state,
consumption `ŷᵢ` in every state, no trade in assets, and asset prices
`q_k = p̂_g ∑_s π_s r_{sk}` (the market "does not pay attention" to the sunspot). -/
theorem exercise_19_F_1 (g : Fin L) {π : Fin S → ℝ} (hπ : ∀ s, 0 ≤ π s) (hπ1 : ∑ s, π s = 1)
    {u : ι → (Fin L → ℝ) → ℝ} (hc : ∀ i, ConcaveOn ℝ {a | ∀ l, 0 ≤ a l} (u i))
    {ω₀ : ι → Fin L → ℝ} {phat : Fin L → ℝ} {yhat : ι → Fin L → ℝ}
    (h : IsSpotEqm u ω₀ phat yhat) (R : Matrix (Fin S) (Fin K) ℝ) :
    IsRadnerEqm g R (fun i => expUtil π fun _ => u i) (fun i _ => ω₀ i)
      (fun k => ∑ s, (phat g * π s) * R s k) (fun _ => phat) (fun i _ => yhat i) (fun _ => 0) := by
  have hdot := dot_eq_of_pricing (R := R) (ν := fun s => phat g * π s)
    (q := fun k => ∑ s, (phat g * π s) * R s k) (fun k => rfl)
  refine ⟨fun i => ⟨⟨fun _ l => ((h.1 i).1.1 l), by simp, fun s => ?_⟩, fun x' z' hf => ?_⟩,
    fun k => by simp, fun s l => ?_⟩
  · simpa using (h.1 i).1.2
  · obtain ⟨hx', hqz, hs⟩ := hf
    set xbar := ∑ s, π s • x' s with hxbar
    have hxbar0 : ∀ l, 0 ≤ xbar l := fun l => by
      simp only [hxbar, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_nonneg fun s _ => mul_nonneg (hπ s) (hx' s l)
    have hbud : phat ⬝ᵥ xbar ≤ phat ⬝ᵥ ω₀ i := by
      have h1 : phat ⬝ᵥ xbar = ∑ s, π s * (phat ⬝ᵥ x' s) := by
        simp [hxbar, dotProduct_sum, dotProduct_smul]
      have h2 : ∀ s, π s * (phat ⬝ᵥ x' s) ≤ π s * (phat ⬝ᵥ ω₀ i) + π s * (phat g * (R *ᵥ z') s) :=
        fun s => by rw [← mul_add]; exact mul_le_mul_of_nonneg_left (hs s) (hπ s)
      have h3 := Finset.sum_le_sum fun s (_ : s ∈ Finset.univ) => h2 s
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, hπ1, one_mul] at h3
      rw [hdot] at hqz
      have h4 : ∑ s, π s * (phat g * (R *ᵥ z') s) = (fun s => phat g * π s) ⬝ᵥ (R *ᵥ z') := by
        simp only [dotProduct]; exact Finset.sum_congr rfl fun s _ => by ring
      linarith
    have hjen := (hc i).le_map_sum (t := Finset.univ) (w := π) (p := x') (fun s _ => hπ s) hπ1
      (fun s _ => hx' s)
    have hconst : expUtil π (fun _ => u i) (fun _ => yhat i) = u i (yhat i) := by
      simp [expUtil, ← Finset.sum_mul, hπ1]
    simp only [smul_eq_mul] at hjen
    change expUtil π (fun _ => u i) x' ≤ expUtil π (fun _ => u i) (fun _ => yhat i)
    rw [hconst]
    exact hjen.trans ((h.1 i).2 xbar hxbar0 hbud)
  · have := h.2 l
    simpa [Finset.sum_apply] using this

/-- **Exercise 19.F.1** (MWG, p. 710): the sunspot-free equilibrium is Pareto optimal when the spot
equilibrium allocation is Pareto optimal in the spot economy (as it is under local nonsatiation,
by the first welfare theorem). -/
theorem exercise_19_F_1_po {π : Fin S → ℝ} (hπ : ∀ s, 0 ≤ π s) (hπ1 : ∑ s, π s = 1)
    {u : ι → (Fin L → ℝ) → ℝ} (hc : ∀ i, ConcaveOn ℝ {a | ∀ l, 0 ≤ a l} (u i))
    {ω₀ yhat : ι → Fin L → ℝ}
    (hpo : IsParetoOptimalU (S := 1) (fun i v => u i (v 0)) (fun i _ => ω₀ i)
      (fun i _ => yhat i)) :
    IsParetoOptimalU (fun i => expUtil π fun _ => u i) (fun i _ => ω₀ i)
      (fun i _ => yhat i) := by
  obtain ⟨⟨hy, hf⟩, hno⟩ := hpo
  refine ⟨⟨fun i s l => hy i 0 l, fun s l => by simpa using hf 0 l⟩, ?_⟩
  rintro ⟨x', ⟨hx', hf'⟩, hge, k, hk⟩
  set xbar : ι → Fin L → ℝ := fun i => ∑ s, π s • x' i s with hxbar
  have hjen : ∀ i, expUtil π (fun _ => u i) (x' i) ≤ u i (xbar i) := fun i => by
    have := (hc i).le_map_sum (t := Finset.univ) (w := π) (p := x' i) (fun s _ => hπ s) hπ1
      (fun s _ => hx' i s)
    simpa [expUtil, smul_eq_mul] using this
  have hconst : ∀ i, expUtil π (fun _ => u i) (fun _ => yhat i) = u i (yhat i) := fun i => by
    simp [expUtil, ← Finset.sum_mul, hπ1]
  refine hno ⟨fun i _ => xbar i, ⟨fun i _ l => ?_, fun _ l => ?_⟩, fun i => ?_, k, ?_⟩
  · simp only [hxbar, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_nonneg fun s _ => mul_nonneg (hπ s) (hx' i s l)
  · have : ∀ s, ∑ i, x' i s l ≤ ∑ i, ω₀ i l := fun s => by
      have := hf' s l; simpa [Finset.sum_apply] using this
    simp only [Finset.sum_apply, hxbar, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_comm]
    calc ∑ s, ∑ i, π s * x' i s l = ∑ s, π s * ∑ i, x' i s l := by
          simp [Finset.mul_sum]
      _ ≤ ∑ s, π s * ∑ i, ω₀ i l :=
          Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (this s) (hπ s)
      _ = ∑ i, ω₀ i l := by rw [← Finset.sum_mul, hπ1, one_mul]
  · have := hge i; dsimp only at this ⊢; rw [hconst] at this; exact this.trans (hjen i)
  · have := hk; dsimp only at this ⊢; rw [hconst] at this; exact this.trans_le (hjen k)

/-! ## Constrained Pareto optimality: Definition 19.F.1 and Proposition 19.F.1 -/

/-- **p. 711**. With one good (`L = 1`) the portfolio `zᵢ` determines consumption
`x_{si} = ∑_k z_{ki} r_{sk} + ω_{si}`; the induced utility is `U*ᵢ(zᵢ) = Uᵢ(ωᵢ + R zᵢ)`. -/
def inducedConsumption (R : Matrix (Fin S) (Fin K) ℝ) (ω : CVec S 1) (z : Fin K → ℝ) : CVec S 1 :=
  fun s _ => ω s 0 + (R *ᵥ z) s

/-- **Definition 19.F.1** (MWG, p. 711). The asset allocation `(z₁, …, z_I)` is constrained Pareto
optimal if it is feasible (`∑ᵢ zᵢ ≤ 0`, with nonnegative induced consumption) and no feasible asset
allocation gives every consumer at least the induced utility `U*ᵢ` and some consumer more. -/
def IsConstrainedPO (R : Matrix (Fin S) (Fin K) ℝ) (U : ι → CVec S 1 → ℝ) (ω : ι → CVec S 1)
    (z : ι → Fin K → ℝ) : Prop :=
  ((∀ i, NonnegC (inducedConsumption R (ω i) (z i))) ∧ ∀ k, ∑ i, z i k ≤ 0) ∧
    ¬ ∃ z' : ι → Fin K → ℝ, ((∀ i, NonnegC (inducedConsumption R (ω i) (z' i))) ∧
      ∀ k, ∑ i, z' i k ≤ 0) ∧
      (∀ i, U i (inducedConsumption R (ω i) (z i)) ≤ U i (inducedConsumption R (ω i) (z' i))) ∧
      ∃ i, U i (inducedConsumption R (ω i) (z i)) < U i (inducedConsumption R (ω i) (z' i))

/-- **Footnote 26** (MWG, p. 711). With one good and strongly monotone utility, at a Radner optimum
consumption is the portfolio-induced consumption: `x*ᵢ = ωᵢ + R z*ᵢ` (spot price `1`). -/
theorem radner_consumption_induced {R : Matrix (Fin S) (Fin K) ℝ} {U : ι → CVec S 1 → ℝ}
    {ω x : ι → CVec S 1} {q : Fin K → ℝ} {z : ι → Fin K → ℝ}
    (h : IsRadnerEqm 0 R U ω q (fun _ _ => 1) x z) (i : ι) (hU : StronglyMonotoneC (U i)) :
    x i = inducedConsumption R (ω i) (z i) := by
  obtain ⟨⟨hx, hqz, hsp⟩, hopt⟩ := h.1 i
  have hle : x i ≤ inducedConsumption R (ω i) (z i) := fun s l => by
    rw [Subsingleton.elim l 0]; simpa [inducedConsumption, dotProduct] using hsp s
  by_contra hne
  have hf : radnerFeasible 0 R q (fun _ _ => 1) (ω i) (inducedConsumption R (ω i) (z i)) (z i) :=
    ⟨fun s l => (hx s l).trans (hle s l), hqz, fun s => by
      simp [inducedConsumption, dotProduct]⟩
  linarith [hopt _ _ hf, hU _ _ hx hle hne]

/-- **Proposition 19.F.1** (MWG, p. 711). Two periods and one consumption good: with strongly
monotone utilities and nonnegative nonzero returns, every Radner equilibrium asset allocation is
constrained Pareto optimal: no redistribution of assets in the first period leaves every consumer
as well off and someone strictly better off. (The book's proof applies the first welfare
theorem to the economy with `K` commodities; here it is carried out directly.) -/
theorem proposition_19_F_1 [Nonempty ι] {R : Matrix (Fin S) (Fin K) ℝ}
    (hRn : NonnegNonzeroReturns R) {U : ι → CVec S 1 → ℝ} (hU : ∀ i, StronglyMonotoneC (U i))
    {ω x : ι → CVec S 1} {q : Fin K → ℝ} {z : ι → Fin K → ℝ}
    (h : IsRadnerEqm 0 R U ω q (fun _ _ => 1) x z) : IsConstrainedPO R U ω z := by
  classical
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hqpos := (radner_arbitrageFree 0 h i₀ (hU i₀)).pos hRn
  have hind := fun i => radner_consumption_induced h i (hU i)
  refine ⟨⟨fun i => hind i ▸ (h.1 i).1.1, h.2.1⟩, ?_⟩
  rintro ⟨z', ⟨hx', hsum⟩, hge, k, hk⟩
  have hfeas : ∀ i w, NonnegC (inducedConsumption R (ω i) w) → q ⬝ᵥ w ≤ 0 →
      radnerFeasible 0 R q (fun _ _ => 1) (ω i) (inducedConsumption R (ω i) w) w :=
    fun i w hw hq => ⟨hw, hq, fun s => by simp [inducedConsumption, dotProduct]⟩
  -- strictly better consumers spend more than their (zero) budget
  have hstrict : 0 < q ⬝ᵥ z' k := by
    by_contra hle
    push Not at hle
    have := (h.1 k).2 _ _ (hfeas k (z' k) (hx' k) hle)
    rw [hind k] at this
    linarith
  -- weakly better consumers spend at least zero
  have hweak : ∀ i, 0 ≤ q ⬝ᵥ z' i := by
    intro i
    by_contra hlt
    push Not at hlt
    obtain ⟨k₀⟩ : Nonempty (Fin K) := by
      by_contra hK
      rw [not_nonempty_iff] at hK
      simp [dotProduct] at hlt
    set ε := -(q ⬝ᵥ z' i) / q k₀ with hε
    have hεpos : 0 < ε := div_pos (by linarith) (hqpos k₀)
    set w := z' i + ε • Pi.single k₀ 1 with hw
    have hle : inducedConsumption R (ω i) (z' i) ≤ inducedConsumption R (ω i) w := by
      intro s l
      simp only [inducedConsumption, hw, mulVec_add, mulVec_smul, Pi.add_apply, Pi.smul_apply,
        mulVec_single, smul_eq_mul]
      nlinarith [hRn.1 s k₀]
    have hne : inducedConsumption R (ω i) (z' i) ≠ inducedConsumption R (ω i) w := by
      intro h0
      obtain ⟨s, hs⟩ := hRn.2 k₀
      have := congrFun (congrFun h0 s) 0
      simp only [inducedConsumption, hw, mulVec_add, mulVec_smul, Pi.add_apply, Pi.smul_apply,
        mulVec_single, smul_eq_mul] at this
      have : ε * R s k₀ = 0 := by linarith
      rcases mul_eq_zero.mp this with h' | h'
      · exact hεpos.ne' h'
      · exact hs h'
    have hqw : q ⬝ᵥ w ≤ 0 := by
      rw [hw, dotProduct_add, dotProduct_smul, dotProduct_single, smul_eq_mul, mul_one, hε]
      field_simp [(hqpos k₀).ne']
      linarith
    have h1 := (h.1 i).2 _ _ (hfeas i w (fun s l => (hx' i s l).trans (hle s l)) hqw)
    have h2 := hU i _ _ (hx' i) hle hne
    rw [hind i] at h1
    linarith [hge i]
  have hpos : 0 < q ⬝ᵥ ∑ i, z' i := by
    rw [dotProduct_sum]
    exact Finset.sum_pos' (fun i _ => hweak i) ⟨k, Finset.mem_univ _, hstrict⟩
  have hnp : q ⬝ᵥ ∑ i, z' i ≤ 0 := Finset.sum_nonpos fun k' _ =>
    mul_nonpos_of_nonneg_of_nonpos (hqpos k').le (by simpa [Finset.sum_apply] using hsum k')
  linarith

/-! ## Example 19.F.2 (Hart) -/

/-- **Example 19.F.2** (MWG, p. 712). Two spot equilibria with prices `p'`, `p''` and spot utilities
`vᵢ(p')`, `vᵢ(p'')`. (1) If the `p''` allocation is Pareto optimal in the spot market (the
`p'` allocation does not Pareto dominate it) and `v₁(p') > v₁(p'')`, then `v₂(p') < v₂(p'')`.
(2) With no assets, `(p', p'')` and `(p'', p')` are
Radner equilibrium price systems for any probabilities (`radner_noAssets_iff`); if `π₁₁ > 1/2` and
`π₂₂ > 1/2`, the first Pareto dominates the second. -/
theorem example_19_F_2 {v1' v1'' v2' v2'' : ℝ}
    (hpo'' : ¬ (v1'' ≤ v1' ∧ v2'' ≤ v2' ∧ (v1'' < v1' ∨ v2'' < v2'))) (h1 : v1'' < v1')
    {π11 π21 π12 π22 : ℝ} (hπ1 : π11 + π21 = 1) (hπ2 : π12 + π22 = 1) (h11 : 1 / 2 < π11)
    (h22 : 1 / 2 < π22) :
    v2' < v2'' ∧ π11 * v1'' + π21 * v1' < π11 * v1' + π21 * v1'' ∧
      π12 * v2'' + π22 * v2' < π12 * v2' + π22 * v2'' := by
  have hv2 : v2' < v2'' := by
    by_contra hle
    push Not at hle
    exact hpo'' ⟨h1.le, hle, Or.inl h1⟩
  refine ⟨hv2, by nlinarith, by nlinarith⟩

/-! ## Exercise 19.F.2 -/

/-- **Exercise 19.F.2** (MWG, p. 728). Sufficient conditions on `U*ᵢ(z) = Uᵢ(ωᵢ + Rz)`: if `Uᵢ` is
continuous (concave) on `ℝ^S_+`, then `U*ᵢ` is continuous (concave) on the convex set of portfolios
with nonnegative induced consumption. -/
theorem exercise_19_F_2_concave {R : Matrix (Fin S) (Fin K) ℝ} {ω : CVec S 1}
    {U : CVec S 1 → ℝ} (hc : ConcaveOn ℝ {x | NonnegC x} U) :
    ConcaveOn ℝ {z | NonnegC (inducedConsumption R ω z)}
      (fun z => U (inducedConsumption R ω z)) := by
  have hlin : ∀ (a b : ℝ) (z z' : Fin K → ℝ), a + b = 1 →
      inducedConsumption R ω (a • z + b • z') =
        a • inducedConsumption R ω z + b • inducedConsumption R ω z' := by
    intro a b z z' hab
    funext s l
    simp only [inducedConsumption, mulVec_add, mulVec_smul, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    have : ω s 0 = a * ω s 0 + b * ω s 0 := by rw [← add_mul, hab, one_mul]
    linarith
  refine ⟨fun z hz z' hz' a b ha hb hab => ?_, fun z hz z' hz' a b ha hb hab => ?_⟩
  · change NonnegC (inducedConsumption R ω (a • z + b • z'))
    rw [hlin a b z z' hab]
    intro s l
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hz s l)) (mul_nonneg hb (hz' s l))
  · simp only [smul_eq_mul]
    rw [hlin a b z z' hab]
    exact hc.2 hz hz' ha hb hab

/-- **Exercise 19.F.2** (MWG, p. 728), continuity. -/
theorem exercise_19_F_2_continuous {R : Matrix (Fin S) (Fin K) ℝ} {ω : CVec S 1}
    {U : CVec S 1 → ℝ} (hU : Continuous U) :
    Continuous fun z => U (inducedConsumption R ω z) := by
  refine hU.comp (continuous_pi fun s => continuous_pi fun _ => ?_)
  exact continuous_const.add ((continuous_apply s).comp
    (continuous_const.matrix_mulVec continuous_id))

/-- **Exercise 19.F.2** (MWG, p. 728). If all returns are strictly positive and `Uᵢ` is strongly
monotone, then `U*ᵢ` is strictly increasing: `z ≤ z'`, `z ≠ z'` imply `U*ᵢ(z) < U*ᵢ(z')` (for
`z` with nonnegative induced consumption). -/
theorem exercise_19_F_2_increasing {R : Matrix (Fin S) (Fin K) ℝ} (hR : ∀ s k, 0 < R s k)
    [NeZero S] {ω : CVec S 1} {U : CVec S 1 → ℝ} (hU : StronglyMonotoneC U) {z z' : Fin K → ℝ}
    (hz : NonnegC (inducedConsumption R ω z)) (hle : z ≤ z') (hne : z ≠ z') :
    U (inducedConsumption R ω z) < U (inducedConsumption R ω z') := by
  obtain ⟨k, hk⟩ : ∃ k, z k ≠ z' k := by
    by_contra h; push Not at h; exact hne (funext h)
  have hlt : z k < z' k := lt_of_le_of_ne (hle k) hk
  refine hU _ _ hz (fun s l => ?_) (fun h0 => ?_)
  · simp only [inducedConsumption, mulVec, dotProduct]
    have := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) =>
      mul_le_mul_of_nonneg_left (hle k) (hR s k).le
    linarith
  · have h1 := congrFun (congrFun h0 ⟨0, NeZero.pos S⟩) 0
    simp only [inducedConsumption, mulVec, dotProduct, add_right_inj] at h1
    have h2 : ∑ k, R ⟨0, NeZero.pos S⟩ k * z k < ∑ k, R ⟨0, NeZero.pos S⟩ k * z' k :=
      Finset.sum_lt_sum (fun k _ => mul_le_mul_of_nonneg_left (hle k) (hR _ k).le)
        ⟨k, Finset.mem_univ _, mul_lt_mul_of_pos_left hlt (hR _ k)⟩
    linarith

end MWG.EquilibriumUncertainty
