/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGEquilibriumUncertainty.Exchange

/-!
# Risk sharing (MWG Section 19.C, Examples 19.C.1-19.C.2, Exercises 19.C.2-19.C.5)

One physical good (`L = 1`), contingent vectors `x : CVec S 1`, one-good expected utility `eu1`.

* **Example 19.C.1(a)**: no aggregate risk and common probabilities: every Arrow-Debreu
  equilibrium insures both consumers completely, and the Pareto set is the diagonal of the box
  (`example_19_C_1a`, `example_19_C_1a_diagonal`).
* **Example 19.C.1(b)**: different probabilities (`π₁₁ < π₁₂`): at an interior equilibrium each
  consumer consumes more in the state he thinks comparatively more likely (`example_19_C_1b`).
* **Example 19.C.2** and **Exercise 19.C.2**: aggregate endowment `(2, 1)`: along the interior
  Pareto set the marginal rate of substitution is below the probability ratio, so at an interior
  equilibrium `p₁/p₂ < π₁/π₂`, and `p₁ < p₂` when `π₁ = π₂` (`exercise_19_C_2`,
  `example_19_C_2`).
* **Exercise 19.C.3**: `∑_s (π_{si} p̄ - p_s) x_{si} ≥ 0` (revealed preference and Jensen).
* **Exercise 19.C.4(a)-(b)**: a risk-neutral and a risk-averse consumer.
* **Exercise 19.C.5**: with nonstochastic aggregate endowment, consuming the expected value of
  one's endowment in every state is an equilibrium allocation.
-/

namespace MWG.EquilibriumUncertainty

variable {S : ℕ}

/-- A strictly concave Bernoulli utility of one good gives a strictly concave function on
`ℝ^1_+`. -/
theorem strictConcaveOn_fin1 {u : ℝ → ℝ} (hu : StrictConcaveOn ℝ (Set.Ici 0) u) :
    StrictConcaveOn ℝ {a : Fin 1 → ℝ | ∀ l, 0 ≤ a l} (fun v => u (v 0)) := by
  refine ⟨?_, ?_⟩
  · intro a ha b hb α β hα hβ _ l
    have := ha l; have := hb l
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; positivity
  · intro a ha b hb hab α β hα hβ hαβ
    have h0 : a 0 ≠ b 0 := fun h => hab (funext fun l => by rw [Subsingleton.elim l 0]; exact h)
    exact hu.2 (Set.mem_Ici.mpr (ha 0)) (Set.mem_Ici.mpr (hb 0)) h0 hα hβ hαβ

/-- The endowments of Example 19.C.1: `ω₁ = (1, 0)`, `ω₂ = (0, 1)`. -/
def omega19C1 : Fin 2 → CVec 2 1 := ![dirC ![1, 0], dirC ![0, 1]]

/-- **Example 19.C.1(a)** (MWG, pp. 692-693). With no aggregate risk (`ω₁ + ω₂ = (1, 1)`),
common strictly positive probabilities and state-independent, strictly concave, strictly
increasing Bernoulli utilities, every Arrow-Debreu equilibrium insures both consumers completely:
consumption does not vary across the two states. -/
theorem example_19_C_1a {π : Fin 2 → ℝ} (hπ : ∀ s, 0 < π s) (hπ1 : ∑ s, π s = 1)
    {u : Fin 2 → ℝ → ℝ} (hc : ∀ i, StrictConcaveOn ℝ (Set.Ici 0) (u i))
    (hm : ∀ i, StrictMonoOn (u i) (Set.Ici 0)) {x : Fin 2 → CVec 2 1} {p : CVec 2 1}
    (h : IsADEqmU (fun i => eu1 π fun _ => u i) omega19C1 x p) : ∀ i, x i 0 = x i 1 := by
  have hpo := adEqmU_paretoOptimal (fun i => eu1_stronglyMonotone hπ fun _ => hm i) h
  have := po_stateIndependent (u := fun i v => u i (v 0)) hπ hπ1
    (fun i => strictConcaveOn_fin1 (hc i)) (ω := omega19C1) (fun s s' => by
      fin_cases s <;> fin_cases s' <;> funext l <;> simp [omega19C1, dirC]) hpo
  exact fun i => this i 0 1

/-- **Example 19.C.1(a)** (MWG, p. 692, Figure 19.C.1(a)): the Pareto set is the diagonal. Every
full-insurance allocation `x₁ = (c, c)`, `x₂ = (1 - c, 1 - c)`, `0 ≤ c ≤ 1`, is Pareto optimal
(the converse is `po_stateIndependent`). -/
theorem example_19_C_1a_diagonal {π : Fin 2 → ℝ} (hπ : ∀ s, 0 ≤ π s) (hπ1 : ∑ s, π s = 1)
    {u : Fin 2 → ℝ → ℝ} (hc : ∀ i, ConcaveOn ℝ (Set.Ici 0) (u i))
    (hm : ∀ i, StrictMonoOn (u i) (Set.Ici 0)) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    IsParetoOptimalU (fun i => eu1 π fun _ => u i) omega19C1
      ![fun _ _ => c, fun _ _ => 1 - c] := by
  refine ⟨⟨fun i => ?_, fun s l => ?_⟩, ?_⟩
  · fin_cases i <;> intro s l <;> simp <;> linarith
  · rw [Subsingleton.elim l 0]
    fin_cases s <;> simp [omega19C1, dirC]
  · rintro ⟨x', ⟨hx', hf⟩, hge, k, hk⟩
    set m : Fin 2 → ℝ := fun i => ∑ s, π s * x' i s 0 with hm'
    have hjen : ∀ i, eu1 π (fun _ => u i) (x' i) ≤ u i (m i) := by
      intro i
      have := (hc i).le_map_sum (t := Finset.univ) (w := π) (p := fun s => x' i s 0)
        (fun s _ => hπ s) hπ1 (fun s _ => Set.mem_Ici.mpr (hx' i s 0))
      simp only [smul_eq_mul] at this
      exact this
    have hm0 : ∀ i, 0 ≤ m i := fun i =>
      Finset.sum_nonneg fun s _ => mul_nonneg (hπ s) (hx' i s 0)
    have hconst : ∀ i (a : ℝ), eu1 π (fun _ => u i) (fun _ _ => a) = u i a := by
      intro i a; simp [eu1, ← Finset.sum_mul, hπ1]
    have hsum : m 0 + m 1 ≤ 1 := by
      have h0 := hf 0 0; have h1 := hf 1 0
      simp [Fin.sum_univ_two, omega19C1, dirC] at h0 h1
      simp only [hm', Fin.sum_univ_two] at *
      have hπ1' : π 0 + π 1 = 1 := by simpa [Fin.sum_univ_two] using hπ1
      nlinarith [hπ 0, hπ 1]
    have hle : ∀ i (a : ℝ), 0 ≤ a → u i a ≤ u i (m i) → a ≤ m i := fun i a ha h =>
      (hm i).le_iff_le (Set.mem_Ici.mpr ha) (Set.mem_Ici.mpr (hm0 i)) |>.mp h
    have hlt : ∀ i (a : ℝ), 0 ≤ a → u i a < u i (m i) → a < m i := fun i a ha h =>
      (hm i).lt_iff_lt (Set.mem_Ici.mpr ha) (Set.mem_Ici.mpr (hm0 i)) |>.mp h
    have h0 := hge 0; have h1 := hge 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hconst] at h0 h1
    have hc0' := hle 0 c hc0 (h0.trans (hjen 0))
    have hc1' := hle 1 (1 - c) (by linarith) (h1.trans (hjen 1))
    fin_cases k
    · simp only [Fin.zero_eta, Matrix.cons_val_zero, hconst] at hk
      linarith [hlt 0 c hc0 (hk.trans_le (hjen 0))]
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, hconst] at hk
      linarith [hlt 1 (1 - c) (by linarith) (hk.trans_le (hjen 1))]

/-- **Example 19.C.1(b)** (MWG, p. 693, Figure 19.C.1(b)). No aggregate risk, but different
subjective probabilities with `π₁₁ < π₁₂` (consumer 2 gives more probability to state 1; indices
`π i s`, consumers and states counted from `0`). At an interior Arrow-Debreu equilibrium, with
good Bernoulli utilities, each consumer's consumption is higher in the state he thinks
comparatively more likely: consumer 1 consumes more in state 2, consumer 2 more in state 1. -/
theorem example_19_C_1b {π : Fin 2 → Fin 2 → ℝ} (hπ : ∀ i s, 0 < π i s)
    (hπ1 : ∀ i, π i 0 + π i 1 = 1) (hlt : π 0 0 < π 1 0) {u u' : Fin 2 → ℝ → ℝ}
    (hu : ∀ i, GoodBernoulli (u i) (u' i)) {x : Fin 2 → CVec 2 1} {p : CVec 2 1}
    (h : IsADEqmU (fun i => eu1 (π i) fun _ => u i) omega19C1 x p) (hx : ∀ i s, 0 < x i s 0) :
    x 0 0 0 < x 0 1 0 ∧ x 1 1 0 < x 1 0 0 := by
  have hfoc : ∀ i, ∃ lam : ℝ, 0 ≤ lam ∧ ∀ s, π i s * u' i (x i s 0) = lam * p s 0 := fun i =>
    foc_eu1 (hx i) (h.1 i).1.2 (h.1 i).2 (fun s => (hu i).2.2 _ (hx i s))
  obtain ⟨l0, _, f0⟩ := hfoc 0
  obtain ⟨l1, _, f1⟩ := hfoc 1
  have hd : ∀ i s, 0 < u' i (x i s 0) := fun i s => (hu i).deriv_pos (hx i s)
  have hfeas : ∀ s, x 0 s 0 + x 1 s 0 = 1 := by
    intro s
    have := congrFun (congrFun h.2 s) 0
    fin_cases s <;> simpa [Fin.sum_univ_two, omega19C1, dirC] using this
  have key : π 0 0 * u' 0 (x 0 0 0) * (π 1 1 * u' 1 (x 1 1 0)) =
      π 0 1 * u' 0 (x 0 1 0) * (π 1 0 * u' 1 (x 1 0 0)) := by
    rw [f0 0, f0 1, f1 0, f1 1]; ring
  have hmain : x 0 0 0 < x 0 1 0 := by
    by_contra hge
    push Not at hge
    have hd0 : u' 0 (x 0 0 0) ≤ u' 0 (x 0 1 0) := by
      rcases hge.lt_or_eq with hlt' | heq
      · exact ((hu 0).deriv_lt (hx 0 1) hlt').le
      · rw [heq]
    have hd1 : u' 1 (x 1 1 0) ≤ u' 1 (x 1 0 0) := by
      have : x 1 0 0 ≤ x 1 1 0 := by linarith [hfeas 0, hfeas 1]
      rcases this.lt_or_eq with hlt' | heq
      · exact ((hu 1).deriv_lt (hx 1 0) hlt').le
      · rw [heq]
    have hA := hd 0 0; have hB := hd 0 1; have hC := hd 1 0; have hD := hd 1 1
    have hπ' : π 0 1 * π 1 0 ≤ π 0 0 * π 1 1 := by
      by_contra hc
      push Not at hc
      have h1 : π 0 0 * π 1 1 * (u' 0 (x 0 0 0) * u' 1 (x 1 1 0)) <
          π 0 1 * π 1 0 * (u' 0 (x 0 1 0) * u' 1 (x 1 0 0)) := by
        calc π 0 0 * π 1 1 * (u' 0 (x 0 0 0) * u' 1 (x 1 1 0))
            ≤ π 0 0 * π 1 1 * (u' 0 (x 0 1 0) * u' 1 (x 1 0 0)) := by
              apply mul_le_mul_of_nonneg_left _ (by nlinarith [hπ 0 0, hπ 1 1])
              exact mul_le_mul hd0 hd1 hD.le hB.le
          _ < π 0 1 * π 1 0 * (u' 0 (x 0 1 0) * u' 1 (x 1 0 0)) :=
              mul_lt_mul_of_pos_right hc (mul_pos hB hC)
      nlinarith [key]
    have e1 : π 0 1 = 1 - π 0 0 := by linarith [hπ1 0]
    have e2 : π 1 1 = 1 - π 1 0 := by linarith [hπ1 1]
    rw [e1, e2] at hπ'
    nlinarith
  exact ⟨hmain, by linarith [hfeas 0, hfeas 1]⟩

/-- Pareto optimal allocations of strongly monotone consumers exhaust the resources. -/
theorem po_exhausts {ι : Type*} [Fintype ι] {L : ℕ} {U : ι → CVec S L → ℝ}
    (hU : ∀ i, StronglyMonotoneC (U i)) {ω x : ι → CVec S L} (hpo : IsParetoOptimalU U ω x)
    (i₀ : ι) : ∑ i, x i = ∑ i, ω i := by
  classical
  obtain ⟨⟨hx, hf⟩, hno⟩ := hpo
  by_contra hne
  set g := ∑ i, ω i - ∑ i, x i with hg
  have hg0 : ∀ s l, 0 ≤ g s l := fun s l => by
    have := hf s l
    simp only [Finset.sum_apply] at this
    simp only [hg, Pi.sub_apply, Finset.sum_apply]
    linarith
  refine hno ⟨Function.update x i₀ (x i₀ + g), ⟨fun i => ?_, ?_⟩, fun i => ?_, i₀, ?_⟩
  · by_cases hi : i = i₀
    · subst hi; intro s l; simp; linarith [hx i s l, hg0 s l]
    · rw [Function.update_of_ne hi]; exact hx i
  · rw [Finset.sum_update_of_mem (Finset.mem_univ _)]
    intro s l
    have : ∑ i ∈ Finset.univ \ {i₀}, x i + x i₀ = ∑ i, x i := by
      rw [← Finset.sum_sdiff (Finset.subset_univ {i₀}), Finset.sum_singleton]
    simp only [Pi.add_apply, hg, Pi.sub_apply]
    have h2 := congrFun (congrFun this s) l
    simp only [Pi.add_apply, Finset.sum_apply] at h2 ⊢
    linarith
  · by_cases hi : i = i₀
    · subst hi; rw [Function.update_self]
      by_cases hz : g = 0
      · rw [hz, add_zero]
      · exact (hU i _ _ (hx i) (fun s l => by simp [hg0 s l]) (fun h => hz (by
          funext s l; have := congrFun (congrFun h s) l; simpa using this))).le
    · rw [Function.update_of_ne hi]
  · rw [Function.update_self]
    refine hU i₀ _ _ (hx i₀) (fun s l => by simp [hg0 s l]) (fun h => hne ?_)
    funext s l
    have := congrFun (congrFun h s) l
    simp [hg] at this
    simp only [Finset.sum_apply]
    linarith

/-- The endowments of Example 19.C.2 have aggregate `(2, 1)`. -/
def AggregateTwoOne (ω : Fin 2 → CVec 2 1) : Prop :=
  ω 0 0 0 + ω 1 0 0 = 2 ∧ ω 0 1 0 + ω 1 1 0 = 1

/-- **Exercise 19.C.2** (MWG, p. 725), for Example 19.C.2. With aggregate risk `ω₁ + ω₂ = (2, 1)`,
common probabilities and state-independent good Bernoulli utilities, at every interior point of
the Pareto set both consumers' marginal rates of substitution
`π₁ uᵢ'(x₁ᵢ) / (π₂ uᵢ'(x₂ᵢ))` are below the probability ratio `π₁/π₂`, i.e.
`uᵢ'(x₁ᵢ) < uᵢ'(x₂ᵢ)`, and they are equal. -/
theorem exercise_19_C_2 {π : Fin 2 → ℝ} (hπ : ∀ s, 0 < π s) {u u' : Fin 2 → ℝ → ℝ}
    (hu : ∀ i, GoodBernoulli (u i) (u' i)) {ω x : Fin 2 → CVec 2 1} (hω : AggregateTwoOne ω)
    (hpo : IsParetoOptimalU (fun i => eu1 π fun _ => u i) ω x) (hx : ∀ i s, 0 < x i s 0) :
    (∀ i, u' i (x i 0 0) < u' i (x i 1 0)) ∧
      π 0 * u' 0 (x 0 0 0) * (π 1 * u' 1 (x 1 1 0)) =
        π 0 * u' 1 (x 1 0 0) * (π 1 * u' 0 (x 0 1 0)) := by
  have htan := po_tangency hpo hx (fun i s => (hu i).2.2 _ (hx i s))
  have hex := po_exhausts (fun i => eu1_stronglyMonotone hπ fun _ => (hu i).2.1) hpo 0
  have h0 := congrFun (congrFun hex 0) 0
  have h1 := congrFun (congrFun hex 1) 0
  simp only [Fin.sum_univ_two, Pi.add_apply] at h0 h1
  have hd : ∀ i s, 0 < u' i (x i s 0) := fun i s => (hu i).deriv_pos (hx i s)
  have hπ0 := hπ 0; have hπ1 := hπ 1
  have hA := hd 0 0; have hB := hd 0 1; have hC := hd 1 0; have hD := hd 1 1
  refine ⟨?_, htan⟩
  rcases lt_or_ge (x 0 1 0) (x 0 0 0) with h00 | h00
  · have hlt0 := (hu 0).deriv_lt (hx 0 1) h00
    intro i; fin_cases i
    · exact hlt0
    · simp only [Fin.mk_one]
      by_contra hc
      push Not at hc
      have : π 0 * u' 0 (x 0 0 0) * (π 1 * u' 1 (x 1 1 0)) <
          π 0 * u' 1 (x 1 0 0) * (π 1 * u' 0 (x 0 1 0)) := by
        have e1 : u' 0 (x 0 0 0) * u' 1 (x 1 1 0) < u' 0 (x 0 1 0) * u' 1 (x 1 0 0) :=
          calc u' 0 (x 0 0 0) * u' 1 (x 1 1 0) < u' 0 (x 0 1 0) * u' 1 (x 1 1 0) :=
                mul_lt_mul_of_pos_right hlt0 hD
            _ ≤ u' 0 (x 0 1 0) * u' 1 (x 1 0 0) := mul_le_mul_of_nonneg_left hc hB.le
        nlinarith [mul_pos hπ0 hπ1]
      linarith
  · have hlt1 : x 1 1 0 < x 1 0 0 := by
      have : x 0 0 0 + x 1 0 0 = ω 0 0 0 + ω 1 0 0 := h0
      have : x 0 1 0 + x 1 1 0 = ω 0 1 0 + ω 1 1 0 := h1
      linarith [hω.1, hω.2]
    have hlt1' := (hu 1).deriv_lt (hx 1 1) hlt1
    intro i; fin_cases i
    · simp only [Fin.zero_eta]
      by_contra hc
      push Not at hc
      have : π 0 * u' 1 (x 1 0 0) * (π 1 * u' 0 (x 0 1 0)) <
          π 0 * u' 0 (x 0 0 0) * (π 1 * u' 1 (x 1 1 0)) := by
        have e1 : u' 1 (x 1 0 0) * u' 0 (x 0 1 0) < u' 1 (x 1 1 0) * u' 0 (x 0 0 0) :=
          calc u' 1 (x 1 0 0) * u' 0 (x 0 1 0) < u' 1 (x 1 1 0) * u' 0 (x 0 1 0) :=
                mul_lt_mul_of_pos_right hlt1' hB
            _ ≤ u' 1 (x 1 1 0) * u' 0 (x 0 0 0) := mul_le_mul_of_nonneg_left hc hD.le
        nlinarith [mul_pos hπ0 hπ1]
      linarith
    · exact hlt1'

/-- **Example 19.C.2** (MWG, p. 693). With aggregate risk `(2, 1)`, at every interior Arrow-Debreu
equilibrium `p₁/p₂ < π₁/π₂` (written `p₁ π₂ < p₂ π₁`): the contingent commodity is dearer, relative
to its probability, in the state where the good is scarcer. -/
theorem example_19_C_2 {π : Fin 2 → ℝ} (hπ : ∀ s, 0 < π s) {u u' : Fin 2 → ℝ → ℝ}
    (hu : ∀ i, GoodBernoulli (u i) (u' i)) {ω x : Fin 2 → CVec 2 1} (hω : AggregateTwoOne ω)
    {p : CVec 2 1} (h : IsADEqmU (fun i => eu1 π fun _ => u i) ω x p)
    (hx : ∀ i s, 0 < x i s 0) : p 0 0 * π 1 < p 1 0 * π 0 := by
  have hpo := adEqmU_paretoOptimal (fun i => eu1_stronglyMonotone hπ fun _ => (hu i).2.1) h
  have hmrs := (exercise_19_C_2 hπ hu hω hpo hx).1 0
  obtain ⟨lam, hlam, hf⟩ := foc_eu1 (hx 0) (h.1 0).1.2 (h.1 0).2
    (fun s => (hu 0).2.2 _ (hx 0 s))
  have hA := (hu 0).deriv_pos (hx 0 0)
  have h0 := hf 0; have h1 := hf 1
  have hlam0 : 0 < lam := by
    rcases hlam.lt_or_eq with h' | h'
    · exact h'
    · rw [← h', zero_mul] at h0; nlinarith [hπ 0]
  have e0 : lam * (p 0 0 * π 1) = π 1 * (π 0 * u' 0 (x 0 0 0)) := by rw [h0]; ring
  have e1 : lam * (p 1 0 * π 0) = π 0 * (π 1 * u' 0 (x 0 1 0)) := by rw [h1]; ring
  have : lam * (p 0 0 * π 1) < lam * (p 1 0 * π 0) := by
    rw [e0, e1]
    have := mul_lt_mul_of_pos_left hmrs (mul_pos (hπ 0) (hπ 1))
    linarith
  exact lt_of_mul_lt_mul_left this hlam0.le

/-- **Example 19.C.2** (MWG, p. 693). If `π₁ = π₂ = 1/2`, then `p₁ < p₂`. -/
theorem example_19_C_2_equal {u u' : Fin 2 → ℝ → ℝ} (hu : ∀ i, GoodBernoulli (u i) (u' i))
    {ω x : Fin 2 → CVec 2 1} (hω : AggregateTwoOne ω) {p : CVec 2 1}
    (h : IsADEqmU (fun i => eu1 (fun _ => 1 / 2) fun _ => u i) ω x p)
    (hx : ∀ i s, 0 < x i s 0) : p 0 0 < p 1 0 := by
  have := example_19_C_2 (π := fun _ => 1 / 2) (fun _ => by norm_num) hu hω h hx
  linarith

/-- **Exercise 19.C.3** (MWG, p. 726). At an Arrow-Debreu equilibrium with one good, a consumer
with strictly positive probabilities `πᵢ` (summing to one) and a state-independent, concave,
strictly increasing Bernoulli utility satisfies `∑_s (π_{si} p̄ - p_s) x_{si} ≥ 0`, where
`p̄ = ∑_s p_s` is the price of sure delivery of one unit. (Concavity suffices; the book assumes
strict concavity and continuity.) Interpretation: valued at the consumer's own probabilities and
the riskless price, his consumption is worth at least its market cost. -/
theorem exercise_19_C_3 [NeZero S] {ι : Type*} [Fintype ι] {π : ι → Fin S → ℝ}
    {u : ι → ℝ → ℝ} {ω x : ι → CVec S 1} {p : CVec S 1}
    (h : IsADEqmU (fun i => eu1 (π i) fun _ => u i) ω x p) (i : ι) (hπ : ∀ s, 0 < π i s)
    (hπ1 : ∑ s, π i s = 1) (hc : ConcaveOn ℝ (Set.Ici 0) (u i))
    (hm : StrictMonoOn (u i) (Set.Ici 0)) :
    0 ≤ ∑ s, (π i s * (∑ s', p s' 0) - p s 0) * x i s 0 := by
  have hsm : StronglyMonotoneC (eu1 (π i) fun _ => u i) := eu1_stronglyMonotone hπ fun _ => hm
  have hp : ∀ s, 0 ≤ p s 0 := by
    intro s
    by_contra hneg
    push Not at hneg
    have hx := (h.1 i).1.1
    have hle : x i ≤ x i + contingentUnit 0 s := fun s' l' => by
      simp only [Pi.add_apply, contingentUnit]; split_ifs <;> simp
    have hne : x i ≠ x i + contingentUnit 0 s := fun h' => by
      have := congrFun (congrFun h' s) 0
      simp [contingentUnit] at this
    have := (h.1 i).2 (x i + contingentUnit 0 s) (fun s' l' => (hx s' l').trans (hle s' l'))
      (by rw [cval_add, cval_unit]; linarith [(h.1 i).1.2])
    linarith [hsm _ _ hx hle hne]
  set pbar := ∑ s', p s' 0 with hpbar
  have hx := (h.1 i).1.1
  have hcost : cval p (x i) = ∑ s, p s 0 * x i s 0 := by simp [cval, dotProduct]
  have hpbar0 : 0 < pbar := by
    rcases (Finset.sum_nonneg fun s (_ : s ∈ Finset.univ) => hp s).lt_or_eq with h' | h'
    · exact h'
    · exfalso
      have hz : ∀ s, p s 0 = 0 := fun s =>
        (Finset.sum_eq_zero_iff_of_nonneg fun s _ => hp s).mp h'.symm s (Finset.mem_univ _)
      have hle : x i ≤ x i + fun _ _ => 1 := fun s l => by simp
      have hne : x i ≠ x i + fun _ _ => 1 := fun h' => by
        have := congrFun (congrFun h' ⟨0, NeZero.pos S⟩) 0; simp at this
      have := (h.1 i).2 (x i + fun _ _ => 1) (fun s l => by simp; linarith [hx s l])
        (by simp [cval, dotProduct, hz])
      linarith [hsm _ _ hx hle hne]
  set c := (∑ s, p s 0 * x i s 0) / pbar with hcdef
  have hc0 : 0 ≤ c := div_nonneg (Finset.sum_nonneg fun s _ => mul_nonneg (hp s) (hx s 0))
    hpbar0.le
  have haff : cval p (fun _ _ => c) ≤ cval p (ω i) := by
    have : cval p (fun _ _ => c) = cval p (x i) := by
      rw [hcost]
      have e : cval p (fun _ _ => c) = pbar * c := by
        simp only [cval, dotProduct, Finset.univ_unique, Fin.default_eq_zero,
          Finset.sum_singleton]
        rw [hpbar, Finset.sum_mul]
      rw [e, hcdef, mul_div_cancel₀ _ hpbar0.ne']
    rw [this]; exact (h.1 i).1.2
  have hrp := (h.1 i).2 (fun _ _ => c) (fun _ _ => hc0) haff
  have hconst : eu1 (π i) (fun _ => u i) (fun _ _ => c) = u i c := by
    simp [eu1, ← Finset.sum_mul, hπ1]
  set m := ∑ s, π i s * x i s 0 with hmdef
  have hm0 : 0 ≤ m := Finset.sum_nonneg fun s _ => mul_nonneg (hπ s).le (hx s 0)
  have hjen : eu1 (π i) (fun _ => u i) (x i) ≤ u i m := by
    have := hc.le_map_sum (t := Finset.univ) (w := π i) (p := fun s => x i s 0)
      (fun s _ => (hπ s).le) hπ1 (fun s _ => Set.mem_Ici.mpr (hx s 0))
    simpa [eu1, smul_eq_mul] using this
  have hrp' : u i c ≤ eu1 (π i) (fun _ => u i) (x i) := by rw [← hconst]; exact hrp
  have hcm : c ≤ m := (hm.le_iff_le (Set.mem_Ici.mpr hc0) (Set.mem_Ici.mpr hm0)).mp
    (hrp'.trans hjen)
  have : ∑ s, p s 0 * x i s 0 ≤ pbar * m := by
    have := mul_le_mul_of_nonneg_left hcm hpbar0.le
    rwa [hcdef, mul_div_cancel₀ _ hpbar0.ne'] at this
  have hexp : ∑ s, (π i s * pbar - p s 0) * x i s 0 = pbar * m - ∑ s, p s 0 * x i s 0 := by
    rw [hmdef, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun s _ => by ring
  rw [hexp]; linarith

/-- The endowments of Exercise 19.C.4: each consumer has half of the aggregate `ω̄ ≫ 0`. -/
noncomputable def halfEndow (ωbar : Fin 2 → ℝ) : Fin 2 → CVec 2 1 :=
  fun _ => dirC fun s => ωbar s / 2

/-- **Exercise 19.C.4(a)** (MWG, p. 726). Consumer 1 is risk neutral (`u₁(x) = a x + b`, `a > 0`),
consumer 2 has a strictly concave Bernoulli utility, and the probabilities are common and strictly
positive. At an interior Arrow-Debreu equilibrium consumer 2 insures completely. (Only strict
concavity and differentiability of `u₂` at the equilibrium are used.) -/
theorem exercise_19_C_4a {π : Fin 2 → ℝ} (hπ : ∀ s, 0 < π s) {a b : ℝ} (ha : 0 < a)
    {u₂ : ℝ → ℝ} (hc : StrictConcaveOn ℝ (Set.Ici 0) u₂) {ωbar : Fin 2 → ℝ}
    {x : Fin 2 → CVec 2 1} {p : CVec 2 1}
    (h : IsADEqmU ![eu1 π fun _ t => a * t + b, eu1 π fun _ => u₂] (halfEndow ωbar) x p)
    (hx : ∀ i s, 0 < x i s 0) {D : Fin 2 → ℝ} (hD : ∀ s, HasDerivAt u₂ (D s) (x 1 s 0)) :
    x 1 0 0 = x 1 1 0 := by
  obtain ⟨l1, _, f1⟩ := foc_eu1 (u := fun _ t => a * t + b) (D := fun _ => a) (hx 0)
    (h.1 0).1.2 (h.1 0).2 (fun s => by simpa using ((hasDerivAt_id _).const_mul a).add_const b)
  obtain ⟨l2, _, f2⟩ := foc_eu1 (u := fun _ => u₂) (hx 1) (h.1 1).1.2 (h.1 1).2 hD
  have hl1 : 0 < l1 := by
    rcases (show (0 : ℝ) ≤ l1 by assumption).lt_or_eq with h' | h'
    · exact h'
    · have := f1 0; rw [← h', zero_mul] at this; nlinarith [hπ 0]
  have hDeq : D 0 = D 1 := by
    have e0 := f2 0; have e1 := f2 1; have g0 := f1 0; have g1 := f1 1
    have hp0 : p 0 0 = π 0 * a / l1 := by field_simp; linarith
    have hp1 : p 1 0 = π 1 * a / l1 := by field_simp; linarith
    rw [hp0] at e0; rw [hp1] at e1
    have h0' : D 0 = l2 * a / l1 := by
      have := hπ 0; field_simp at e0 ⊢; nlinarith
    have h1' : D 1 = l2 * a / l1 := by
      have := hπ 1; field_simp at e1 ⊢; nlinarith
    rw [h0', h1']
  exact eq_of_hasDerivAt_eq_of_strictConcaveOn hc (Set.mem_Ici.mpr (hx 1 0).le)
    (Set.mem_Ici.mpr (hx 1 1).le) (hD 0) (hDeq ▸ hD 1)

/-- **Exercise 19.C.4(b)** (MWG, p. 726). Consumer 1 risk neutral, consumer 2 with a good
Bernoulli utility, and different subjective probabilities. At an interior Arrow-Debreu equilibrium
consumer 2 does not insure completely: he consumes more in the state to which he gives relatively
more probability than consumer 1 does (`π₂₁/π₂₂ > π₁₁/π₁₂` gives `x₁₂ > x₂₂`); and consumer 1, the
risk-neutral agent, does not gain from trade (`U₁(x₁) = U₁(ω₁)`). -/
theorem exercise_19_C_4b {π : Fin 2 → Fin 2 → ℝ} (hπ : ∀ i s, 0 < π i s) {a b : ℝ}
    (ha : 0 < a) {u₂ u₂' : ℝ → ℝ} (hu : GoodBernoulli u₂ u₂') {ωbar : Fin 2 → ℝ}
    {x : Fin 2 → CVec 2 1} {p : CVec 2 1}
    (h : IsADEqmU ![eu1 (π 0) fun _ t => a * t + b, eu1 (π 1) fun _ => u₂] (halfEndow ωbar) x p)
    (hx : ∀ i s, 0 < x i s 0) (hbias : π 0 0 * π 1 1 < π 1 0 * π 0 1) :
    x 1 1 0 < x 1 0 0 ∧
      eu1 (π 0) (fun _ t => a * t + b) (x 0) = eu1 (π 0) (fun _ t => a * t + b) (halfEndow ωbar 0)
    := by
  obtain ⟨l1, _, f1⟩ := foc_eu1 (u := fun _ t => a * t + b) (D := fun _ => a) (hx 0)
    (h.1 0).1.2 (h.1 0).2 (fun s => by simpa using ((hasDerivAt_id _).const_mul a).add_const b)
  obtain ⟨l2, hl2, f2⟩ := foc_eu1 (u := fun _ => u₂) (hx 1) (h.1 1).1.2 (h.1 1).2
    (fun s => hu.2.2 _ (hx 1 s))
  have hl1 : 0 < l1 := by
    rcases (show (0 : ℝ) ≤ l1 by assumption).lt_or_eq with h' | h'
    · exact h'
    · have := f1 0; rw [← h', zero_mul] at this; nlinarith [hπ 0 0]
  have hd0 := hu.deriv_pos (hx 1 0)
  have hd1 := hu.deriv_pos (hx 1 1)
  have g0 := f1 0; have g1 := f1 1; have e0 := f2 0; have e1 := f2 1
  refine ⟨?_, ?_⟩
  · by_contra hge
    push Not at hge
    have hle : u₂' (x 1 1 0) ≤ u₂' (x 1 0 0) := by
      rcases hge.lt_or_eq with h' | h'
      · exact (hu.deriv_lt (hx 1 0) h').le
      · rw [h']
    have k1 : π 1 0 * u₂' (x 1 0 0) * π 0 1 = π 1 1 * u₂' (x 1 1 0) * π 0 0 := by
      have : (π 1 0 * u₂' (x 1 0 0) * π 0 1) * a = (π 1 1 * u₂' (x 1 1 0) * π 0 0) * a := by
        calc (π 1 0 * u₂' (x 1 0 0) * π 0 1) * a = (π 1 0 * u₂' (x 1 0 0)) * (π 0 1 * a) := by
              ring
          _ = (l2 * p 0 0) * (l1 * p 1 0) := by rw [e0, g1]
          _ = (l2 * p 1 0) * (l1 * p 0 0) := by ring
          _ = (π 1 1 * u₂' (x 1 1 0)) * (π 0 0 * a) := by rw [e1, g0]
          _ = (π 1 1 * u₂' (x 1 1 0) * π 0 0) * a := by ring
      exact mul_right_cancel₀ ha.ne' this
    have h3 : π 1 0 * π 0 1 * u₂' (x 1 0 0) ≤ π 1 1 * π 0 0 * u₂' (x 1 0 0) := by
      have h4 := mul_le_mul_of_nonneg_left hle (mul_pos (hπ 1 1) (hπ 0 0)).le
      nlinarith [k1]
    have := le_of_mul_le_mul_right h3 hd0
    linarith
  · have hsm : ∀ i, StronglyMonotoneC
        (![eu1 (π 0) fun _ t => a * t + b, eu1 (π 1) fun _ => u₂] i) := by
      intro i; fin_cases i
      · simp only [Fin.zero_eta, Matrix.cons_val_zero]
        exact eu1_stronglyMonotone (hπ 0) fun _ _ _ _ _ hxy =>
          add_lt_add_left (mul_lt_mul_of_pos_left hxy ha) b
      · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
        exact eu1_stronglyMonotone (hπ 1) fun _ => hu.2.1
    have hbind := adEqmU_budget_binds hsm h 0
    simp only [cval, dotProduct, Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton,
      Fin.sum_univ_two] at hbind
    have hU : a * (π 0 0 * x 0 0 0 + π 0 1 * x 0 1 0) =
        a * (π 0 0 * halfEndow ωbar 0 0 0 + π 0 1 * halfEndow ωbar 0 1 0) := by
      have e : l1 * (p 0 0 * x 0 0 0 + p 1 0 * x 0 1 0) =
          l1 * (p 0 0 * halfEndow ωbar 0 0 0 + p 1 0 * halfEndow ωbar 0 1 0) := by rw [hbind]
      linear_combination e + (x 0 0 0 - halfEndow ωbar 0 0 0) * g0 +
        (x 0 1 0 - halfEndow ωbar 0 1 0) * g1
    simp only [eu1, Fin.sum_univ_two]
    linear_combination hU

/-- **Exercise 19.C.5** (MWG, p. 726). One good, risk-averse consumers (concave, nondecreasing
state-independent Bernoulli utilities), common probabilities and a nonstochastic aggregate
endowment. Then the allocation in which every consumer consumes, in every state, the expected
value `∑_s π_s ω_{si}` of his endowment is an Arrow-Debreu equilibrium allocation, supported by
the prices `p_s = π_s`. -/
theorem exercise_19_C_5 {ι : Type*} [Fintype ι] {π : Fin S → ℝ} (hπ : ∀ s, 0 ≤ π s)
    (hπ1 : ∑ s, π s = 1) {u : ι → ℝ → ℝ} (hc : ∀ i, ConcaveOn ℝ (Set.Ici 0) (u i))
    (hm : ∀ i, MonotoneOn (u i) (Set.Ici 0)) {ω : ι → CVec S 1} (hω0 : ∀ i, NonnegC (ω i))
    (hagg : ∀ s s', ∑ i, ω i s 0 = ∑ i, ω i s' 0) :
    IsADEqmU (fun i => eu1 π fun _ => u i) ω (fun i _ _ => ∑ s, π s * ω i s 0)
      (fun s _ => π s) := by
  have hm0 : ∀ i, 0 ≤ ∑ s, π s * ω i s 0 := fun i =>
    Finset.sum_nonneg fun s _ => mul_nonneg (hπ s) (hω0 i s 0)
  have hval : ∀ y : CVec S 1, cval (fun s _ => π s) y = ∑ s, π s * y s 0 := fun y => by
    simp [cval, dotProduct]
  refine ⟨fun i => ⟨⟨fun _ _ => hm0 i, ?_⟩, fun x' hx' hb => ?_⟩, ?_⟩
  · rw [hval, hval, ← Finset.sum_mul, hπ1, one_mul]
  · rw [hval, hval] at hb
    have hjen := (hc i).le_map_sum (t := Finset.univ) (w := π) (p := fun s => x' s 0)
      (fun s _ => hπ s) hπ1 (fun s _ => Set.mem_Ici.mpr (hx' s 0))
    simp only [smul_eq_mul] at hjen
    have hconst : eu1 π (fun _ => u i) (fun _ _ => ∑ s, π s * ω i s 0) =
        u i (∑ s, π s * ω i s 0) := by simp [eu1, ← Finset.sum_mul, hπ1]
    dsimp only
    rw [hconst]
    exact hjen.trans (hm i (Set.mem_Ici.mpr (Finset.sum_nonneg fun s _ =>
      mul_nonneg (hπ s) (hx' s 0))) (Set.mem_Ici.mpr (hm0 i)) hb)
  · funext s l
    rw [Subsingleton.elim l 0]
    simp only [Finset.sum_apply]
    rw [Finset.sum_comm]
    calc ∑ s', ∑ i, π s' * ω i s' 0 = ∑ s', π s' * ∑ i, ω i s 0 :=
          Finset.sum_congr rfl fun s' _ => by rw [← Finset.mul_sum, hagg s' s]
      _ = ∑ i, ω i s 0 := by rw [← Finset.sum_mul, hπ1, one_mul]

end MWG.EquilibriumUncertainty
