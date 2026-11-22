/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGWelfareBargaining.Invariance
import MWGClassicalDemand.UtilityRepresentation
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Strict
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.Algebra.Order.Field

/-!
# Social welfare functions and social optima

MWG, Section 22.C, pp. 825-831: the social planner's problem (22.C.1), the properties of social
welfare functions (nonpaternalism, Pareto, symmetry, concavity), Examples 22.C.1-22.C.3,
footnote 11 (leximin) and the compensation principle; Exercises 22.C.1, 22.C.4(a)-(c) (`I = 2`;
any `I` in `Leximin`) and 22.C.8. Exercises 22.C.2-22.C.3 are in `Harsanyi`, 22.C.5 in
`CESWelfare`, 22.C.6-22.C.7 in `CompensationExercises`.

Agents are `Fin n`. A social optimum of `W` on `U` is a maximizer (22.C.1). Exercise 22.C.1 is
proved by a swapping argument: if an optimum `u` has `uᵢ ≠ uⱼ`, the midpoint of `u` and `u` with
`i, j` swapped is feasible (symmetric convex `U`) and strictly better (strictly concave `W`), or,
for strictly convex `U` and concave increasing `W`, interior and hence improvable.
-/

namespace MWG.WelfareBargaining

open Kreps.ChoicePreferenceUtility

variable {n : ℕ}

/-- **Section 22.C** (MWG, p. 825). A social optimum: a maximizer of `W` on `U` (22.C.1). -/
def IsSocialOptimum (W : (Fin n → ℝ) → ℝ) (U : Set (Fin n → ℝ)) (u : Fin n → ℝ) : Prop :=
  u ∈ U ∧ ∀ u' ∈ U, W u' ≤ W u

/-- **Definition 22.B.1** (MWG, p. 818). `u` is on the Pareto frontier of `U`. -/
def IsParetoFrontier (U : Set (Fin n → ℝ)) (u : Fin n → ℝ) : Prop :=
  u ∈ U ∧ ¬∃ u' ∈ U, (∀ i, u i ≤ u' i) ∧ ∃ i, u i < u' i

/-- **Section 22.C, property (ii)** (MWG, p. 825). `W` is strictly Paretian. -/
def IsStrictlyParetian (W : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ u u' : Fin n → ℝ, (∀ i, u i ≤ u' i) → (∃ i, u i < u' i) → W u < W u'

/-- **Section 22.C, property (iii)** (MWG, p. 826). `W` is symmetric. -/
def IsSymmetricSWF (W : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)) (u : Fin n → ℝ), W (u ∘ σ) = W u

/-- **Section 22.C, property (ii)** (MWG, p. 825). A solution of (22.C.1) for a strictly
Paretian `W` is a Pareto optimum. -/
theorem socialOptimum_pareto {W : (Fin n → ℝ) → ℝ} {U : Set (Fin n → ℝ)} {u : Fin n → ℝ}
    (hW : IsStrictlyParetian W) (h : IsSocialOptimum W U u) : IsParetoFrontier U u :=
  ⟨h.1, fun ⟨u', hu', hle, hlt⟩ => absurd (h.2 u' hu') (not_le.2 (hW u u' hle hlt))⟩

/-- **Section 22.C, property (iv)** (MWG, p. 826). For a concave `W`, `W(u) = W(u')` implies
`W(αu + (1-α)u') ≥ W(u)`, strictly if `W` is strictly concave and `u ≠ u'`, `α ∈ (0,1)`. -/
theorem concave_inequality_aversion {W : (Fin n → ℝ) → ℝ} {u u' : Fin n → ℝ}
    (heq : W u = W u') {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1) :
    (ConcaveOn ℝ Set.univ W → W u ≤ W (α • u + (1 - α) • u')) ∧
      (StrictConcaveOn ℝ Set.univ W → u ≠ u' → 0 < α → α < 1 →
        W u < W (α • u + (1 - α) • u')) := by
  refine ⟨fun hc => ?_, fun hc hne ha0 ha1 => ?_⟩
  · have := hc.2 (Set.mem_univ u) (Set.mem_univ u') h0 (by linarith)
      (show α + (1 - α) = 1 by ring)
    simp only [smul_eq_mul] at this
    rw [← heq] at this
    linarith [show α * W u + (1 - α) * W u = W u by ring]
  · have := hc.2 (Set.mem_univ u) (Set.mem_univ u') hne ha0 (by linarith)
      (show α + (1 - α) = 1 by ring)
    simp only [smul_eq_mul] at this
    rw [← heq] at this
    linarith [show α * W u + (1 - α) * W u = W u by ring]

/-- `u` with the entries `i` and `j` exchanged. -/
theorem swap_ne_of_ne {u : Fin n → ℝ} {i j : Fin n} (h : u i ≠ u j) :
    u ∘ Equiv.swap i j ≠ u := by
  intro e
  have := congrFun e i
  simp only [Function.comp, Equiv.swap_apply_left] at this
  exact h this.symm

/-- **Exercise 22.C.1** (MWG, pp. 826, 850). If `U` is symmetric and convex and `W` is
symmetric and strictly concave, every social optimum assigns the same utility to every agent. -/
theorem exercise_22_C_1 {W : (Fin n → ℝ) → ℝ} {U : Set (Fin n → ℝ)}
    (hUs : ∀ σ : Equiv.Perm (Fin n), ∀ u ∈ U, u ∘ σ ∈ U) (hUc : Convex ℝ U)
    (hWs : IsSymmetricSWF W) (hWc : StrictConcaveOn ℝ Set.univ W) {u : Fin n → ℝ}
    (h : IsSocialOptimum W U u) (i j : Fin n) : u i = u j := by
  by_contra hne
  set u' := u ∘ Equiv.swap i j
  have hmem : (1 / 2 : ℝ) • u + (1 - 1 / 2 : ℝ) • u' ∈ U :=
    hUc h.1 (hUs _ _ h.1) (by norm_num) (by norm_num) (by norm_num)
  have := (concave_inequality_aversion (α := 1 / 2) (hWs (Equiv.swap i j) u).symm (by norm_num)
    (by norm_num)).2 hWc (swap_ne_of_ne hne).symm (by norm_num) (by norm_num)
  exact absurd (h.2 _ hmem) (not_le.2 this)

/-- **Exercise 22.C.1, second part** (MWG, p. 850). The same conclusion holds for a merely
concave, symmetric and increasing `W` (e.g. utilitarian) when `U` is symmetric and strictly
convex. -/
theorem exercise_22_C_1_strictConvex {W : (Fin n → ℝ) → ℝ} {U : Set (Fin n → ℝ)}
    (hUs : ∀ σ : Equiv.Perm (Fin n), ∀ u ∈ U, u ∘ σ ∈ U) (hUc : StrictConvex ℝ U)
    (hWs : IsSymmetricSWF W) (hWc : ConcaveOn ℝ Set.univ W) (hWi : IsIncreasingSWF W)
    {u : Fin n → ℝ} (h : IsSocialOptimum W U u) (i j : Fin n) : u i = u j := by
  by_contra hne
  set u' := u ∘ Equiv.swap i j
  have hint := hUc h.1 (hUs _ _ h.1) (swap_ne_of_ne hne).symm (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (0 : ℝ) < 1 - 1 / 2) (by norm_num)
  set m := (1 / 2 : ℝ) • u + (1 - 1 / 2 : ℝ) • u'
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hint)
  have hmε : (fun k => m k + ε / 2) ∈ U := hball (by
    rw [Metric.mem_ball, dist_pi_lt_iff hε]
    intro k; rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos (by positivity)]; linarith)
  have h1 := (concave_inequality_aversion (α := 1 / 2) (hWs (Equiv.swap i j) u).symm
    (by norm_num) (by norm_num)).1 hWc
  have h2 : W m < W (fun k => m k + ε / 2) := hWi.2 _ _ fun k => by linarith
  exact absurd (h.2 _ hmε) (not_le.2 (lt_of_le_of_lt h1 h2))

/-- **Example 22.C.1** (MWG, p. 827). The (nonsymmetric) utilitarian `∑ bᵢuᵢ` with `b ≫ 0` is
strictly Paretian; the generalized utilitarian `∑ g(uᵢ)` (Example 22.C.3) is strictly Paretian
for strictly increasing `g` and concave for concave `g`. -/
theorem example_22_C_1_3 {b : Fin n → ℝ} (hb : ∀ i, 0 < b i) {g : ℝ → ℝ} (hg : StrictMono g) :
    IsStrictlyParetian (fun u : Fin n → ℝ => ∑ i, b i * u i) ∧
      IsStrictlyParetian (fun u : Fin n → ℝ => ∑ i, g (u i)) ∧
      (ConcaveOn ℝ Set.univ g → ConcaveOn ℝ Set.univ fun u : Fin n → ℝ => ∑ i, g (u i)) := by
  refine ⟨fun u u' hle ⟨i, hi⟩ => ?_, fun u u' hle ⟨i, hi⟩ => ?_, fun hc => ?_⟩
  · exact Finset.sum_lt_sum (fun j _ => mul_le_mul_of_nonneg_left (hle j) (hb j).le)
      ⟨i, Finset.mem_univ i, mul_lt_mul_of_pos_left hi (hb i)⟩
  · exact Finset.sum_lt_sum (fun j _ => hg.monotone (hle j)) ⟨i, Finset.mem_univ i, hg hi⟩
  · refine ⟨convex_univ, fun x _ y _ a c ha hc' hac => ?_⟩
    simp only [smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => by
      have := hc.2 (Set.mem_univ (x i)) (Set.mem_univ (y i)) ha hc' hac
      simpa using this

/-- **Example 22.C.1** (MWG, p. 827). Dividing a fixed amount of wealth among agents with the
same strictly concave utility for wealth, the purely utilitarian optimum is the equal split:
any maximizer of `∑ φ(wᵢ)` over `{w : ∑ wᵢ = ω}` has all entries equal. -/
theorem example_22_C_1_equal_split {φ : ℝ → ℝ} (hφ : StrictConcaveOn ℝ Set.univ φ) {ω : ℝ}
    {w : Fin n → ℝ} (hw : ∑ i, w i = ω)
    (hmax : ∀ w' : Fin n → ℝ, ∑ i, w' i = ω → ∑ i, φ (w' i) ≤ ∑ i, φ (w i)) (i j : Fin n) :
    w i = w j := by
  by_contra hne
  set w' := w ∘ Equiv.swap i j
  have hsum' : ∑ k, w' k = ω := by
    rw [← hw]; exact Equiv.sum_comp (Equiv.swap i j) w
  set m : Fin n → ℝ := fun k => (w k + w' k) / 2
  have hm : ∑ k, m k = ω := by
    simp only [m, ← Finset.sum_div, Finset.sum_add_distrib, hw, hsum']; ring
  have hφ' : ∑ k, φ (w' k) = ∑ k, φ (w k) := Equiv.sum_comp (Equiv.swap i j) (fun k => φ (w k))
  have hlt : (∑ k, φ (w k) + ∑ k, φ (w' k)) / 2 < ∑ k, φ (m k) := by
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    apply Finset.sum_lt_sum
    · intro k _
      have := hφ.concaveOn.2 (Set.mem_univ (w k)) (Set.mem_univ (w' k))
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
      simp only [smul_eq_mul, m] at this ⊢
      rw [show 1 / 2 * w k + 1 / 2 * w' k = (w k + w' k) / 2 by ring] at this
      linarith
    · refine ⟨i, Finset.mem_univ i, ?_⟩
      have hne' : w i ≠ w' i := by
        simp only [w', Function.comp, Equiv.swap_apply_left]; exact hne
      have := hφ.2 (Set.mem_univ (w i)) (Set.mem_univ (w' i)) hne'
        (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
      simp only [smul_eq_mul, m] at this ⊢
      rw [show 1 / 2 * w i + 1 / 2 * w' i = (w i + w' i) / 2 by ring] at this
      linarith
  have := hmax m hm
  linarith

/-- **Example 22.C.2** (MWG, p. 828). The maximin function is Paretian (increasing) but not
strictly Paretian. -/
theorem example_22_C_2_paretian [NeZero n] :
    IsIncreasingSWF (fun u : Fin n → ℝ => Finset.univ.inf' Finset.univ_nonempty u) ∧
      (1 < n → ¬IsStrictlyParetian (fun u : Fin n → ℝ =>
        Finset.univ.inf' Finset.univ_nonempty u)) := by
  refine ⟨⟨fun u u' h => Finset.le_inf' _ _ fun i hi => (Finset.inf'_le u hi).trans (h i),
    fun u u' h => ?_⟩, fun hn hsp => ?_⟩
  · obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty u'
    simp only; rw [hj]
    exact lt_of_le_of_lt (Finset.inf'_le u (Finset.mem_univ j)) (h j)
  · have h1 : (⟨1, hn⟩ : Fin n) ≠ 0 := fun e => by simp [Fin.ext_iff] at e
    have := hsp 0 (fun k => if k = ⟨1, hn⟩ then 1 else 0) (fun k => by split_ifs <;> norm_num)
      ⟨⟨1, hn⟩, by simp⟩
    have hle : Finset.univ.inf' Finset.univ_nonempty (fun k : Fin n => if k = ⟨1, hn⟩ then
        (1 : ℝ) else 0) ≤ 0 := (Finset.inf'_le _ (Finset.mem_univ 0)).trans (by simp [h1.symm])
    have hz : Finset.univ.inf' Finset.univ_nonempty (0 : Fin n → ℝ) = 0 := by simp
    dsimp only at this
    rw [hz] at this
    linarith

/-- **Example 22.C.2** (MWG, p. 828). A point of `U` with all coordinates equal that is (even
weakly) Pareto optimal is a maximin optimum. -/
theorem example_22_C_2_equal [NeZero n] {U : Set (Fin n → ℝ)} {c : ℝ}
    (hc : (fun _ => c) ∈ U) (hpo : ¬∃ u ∈ U, ∀ i, c < u i) :
    IsSocialOptimum (fun u : Fin n → ℝ => Finset.univ.inf' Finset.univ_nonempty u) U
      (fun _ => c) := by
  refine ⟨hc, fun u hu => ?_⟩
  simp only [Finset.inf'_const]
  by_contra h
  push Not at h
  exact hpo ⟨u, hu, fun i => lt_of_lt_of_le h (Finset.inf'_le u (Finset.mem_univ i))⟩

/-- **Footnote 11** (MWG, pp. 827-828). The equal-coordinate boundary point `(1, 1)` of
`U = {u ≤ (1, 2)}` is a maximin optimum but not a Pareto optimum. -/
theorem footnote_22_11_example :
    IsSocialOptimum (fun u : Fin 2 → ℝ => Finset.univ.inf' Finset.univ_nonempty u)
      {u | u ≤ ![1, 2]} (fun _ => 1) ∧ ¬IsParetoFrontier {u | u ≤ ![1, 2]} (fun _ => 1) := by
  refine ⟨example_22_C_2_equal (fun i => by fin_cases i <;> norm_num) ?_, fun ⟨_, h⟩ => h ?_⟩
  · rintro ⟨u, hu, hlt⟩
    have := hu 0; have := hlt 0; simp at *; linarith
  · exact ⟨![1, 2], by simp, fun i => by fin_cases i <;> norm_num, ⟨1, by norm_num⟩⟩

/-- **Footnote 11 and Exercise 22.C.4** (MWG, pp. 827, 851), two agents. The leximin ordering:
compare the worst-off utilities, then the best-off. -/
def leximin2 (u u' : Fin 2 → ℝ) : Prop :=
  min (u' 0) (u' 1) < min (u 0) (u 1) ∨
    (min (u 0) (u 1) = min (u' 0) (u' 1) ∧ max (u' 0) (u' 1) ≤ max (u 0) (u 1))

/-- **Exercise 22.C.4(a)** (MWG, p. 851). Leximin refines the Rawlsian (maximin) preference:
a strictly higher minimum is leximin-better, and leximin-weakly-better implies a weakly higher
minimum. -/
theorem exercise_22_C_4a (u u' : Fin 2 → ℝ) :
    (min (u' 0) (u' 1) < min (u 0) (u 1) → leximin2 u u') ∧
      (leximin2 u u' → min (u' 0) (u' 1) ≤ min (u 0) (u 1)) :=
  ⟨Or.inl, fun h => h.elim le_of_lt fun h => h.1.ge⟩

/-- **Exercise 22.C.4(b)** (MWG, p. 851). The leximin ordering on `ℝ²` cannot be represented by
a utility function: it would represent the lexicographic order of Example 3.C.1 through the
embedding `(x₀, x₁) ↦ (x₀, x₀ + 1 + x₁)`. -/
theorem exercise_22_C_4b : ¬∃ W : (Fin 2 → ℝ) → ℝ, ∀ u u', leximin2 u u' ↔ W u' ≤ W u := by
  rintro ⟨W, hW⟩
  let e : (Fin 2 → ℝ) → Fin 2 → ℝ := fun x => ![x 0, x 0 + 1 + x 1]
  apply MWG.ClassicalDemand.example_3_C_1_not_representable
  refine ⟨fun x => W (e x), fun x hx y hy => ?_⟩
  rw [← hW]
  have hx1 := hx 1; have hy1 := hy 1
  simp only [MWG.ConsumerChoice.nonnegOrthant, Set.mem_ofPred_eq] at *
  have mx : min (e x 0) (e x 1) = x 0 := by simp [e]; linarith
  have Mx : max (e x 0) (e x 1) = x 0 + 1 + x 1 := by simp [e]; linarith
  have my : min (e y 0) (e y 1) = y 0 := by simp [e]; linarith
  have My : max (e y 0) (e y 1) = y 0 + 1 + y 1 := by simp [e]; linarith
  simp only [leximin2, mx, Mx, my, My, MWG.ClassicalDemand.lexPref]
  constructor
  · rintro (h | ⟨h, h'⟩)
    · exact Or.inl h
    · exact Or.inr ⟨h, by linarith⟩
  · rintro (h | ⟨h, h'⟩)
    · exact Or.inl h
    · exact Or.inr ⟨h, by linarith⟩

/-- **Exercise 22.C.4(c)** (MWG, p. 851), two agents. A leximin optimum is a Pareto optimum:
a Pareto improvement is strictly leximin-better. -/
theorem exercise_22_C_4c {U : Set (Fin 2 → ℝ)} {u : Fin 2 → ℝ} (hu : u ∈ U)
    (hopt : ∀ u' ∈ U, leximin2 u u') : IsParetoFrontier U u := by
  refine ⟨hu, fun ⟨v, hv, hle, i, hi⟩ => ?_⟩
  have h := hopt v hv
  have hmin : min (u 0) (u 1) ≤ min (v 0) (v 1) := min_le_min (hle 0) (hle 1)
  have hsum : u 0 + u 1 < v 0 + v 1 := by
    fin_cases i
    · simp at hi; linarith [hle 1]
    · simp at hi; linarith [hle 0]
  rcases h with h | ⟨h1, h2⟩
  · linarith
  · have e1 := min_add_max (u 0) (u 1)
    have e2 := min_add_max (v 0) (v 1)
    linarith

/-! ### The compensation principle -/

/-- **Section 22.C** (MWG, p. 830). `U'` passes the strong compensation test over `U`: every
`u ∈ U` is weakly dominated by some `u' ∈ U'`. -/
def StrongCompensation (U U' : Set (Fin n → ℝ)) : Prop := ∀ u ∈ U, ∃ u' ∈ U', u ≤ u'

/-- **Section 22.C** (MWG, p. 830). `U'` passes the weak compensation test over `(U, u)`. -/
def WeakCompensation (U' : Set (Fin n → ℝ)) (u : Fin n → ℝ) : Prop := ∃ u' ∈ U', u ≤ u'

/-- **Section 22.C** (MWG, p. 831, Figure 22.C.7). The paradox: two sets with outcomes, each
passing the weak compensation test over the other. -/
theorem compensation_paradox :
    let U : Set (Fin 2 → ℝ) := {v | v ≤ ![2, 0]} ∪ {v | v ≤ ![0, 2]}
    let U' : Set (Fin 2 → ℝ) := {v | v ≤ ![2, 0]} ∪ {v | v ≤ ![0, 2]}
    ![2, 0] ∈ U ∧ ![0, 2] ∈ U' ∧ WeakCompensation U' ![2, 0] ∧ WeakCompensation U ![0, 2] :=
  ⟨Or.inl (by simp), Or.inr (by simp), ⟨![2, 0], Or.inl (by simp), le_rfl⟩,
    ⟨![0, 2], Or.inr (by simp), le_rfl⟩⟩

/-- **Exercise 22.C.8** (MWG, p. 852). `(U', u')` passes the Kaldor test over `(U, u)`: `U'`
passes the weak test over `(U, u)` and `U` does not pass it over `(U', u')`. -/
def Kaldor (U : Set (Fin n → ℝ)) (u : Fin n → ℝ) (U' : Set (Fin n → ℝ)) (u' : Fin n → ℝ) :
    Prop :=
  WeakCompensation U' u ∧ ¬WeakCompensation U u'

/-- **Exercise 22.C.8(b)** (MWG, p. 852). Kaldor comparability is asymmetric. -/
theorem exercise_22_C_8b (U U' : Set (Fin n → ℝ)) (u u' : Fin n → ℝ) :
    Kaldor U u U' u' → ¬Kaldor U' u' U u := fun h h' => h.2 h'.1

/-- **Exercise 22.C.8(c)** (MWG, p. 852). Kaldor comparability is not transitive. With
`U₁ = {v ≤ (0,0)}`, `U₂ = {v ≤ (-1,5)} ∪ {v ≤ (0,0)}`, `U₃ = {v ≤ (5,-1)} ∪ {v ≤ (-1,5)}` and
outcomes `(0,0)`, `(-1,5)`, `(5,-1)`: `(U₂, ·)` Kaldor-beats `(U₁, ·)` and `(U₃, ·)` beats
`(U₂, ·)`, but `(U₃, ·)` does not beat `(U₁, ·)`. -/
theorem exercise_22_C_8c :
    let U₁ : Set (Fin 2 → ℝ) := {v | v ≤ ![0, 0]}
    let U₂ : Set (Fin 2 → ℝ) := {v | v ≤ ![-1, 5]} ∪ {v | v ≤ ![0, 0]}
    let U₃ : Set (Fin 2 → ℝ) := {v | v ≤ ![5, -1]} ∪ {v | v ≤ ![-1, 5]}
    Kaldor U₁ ![0, 0] U₂ ![-1, 5] ∧ Kaldor U₂ ![-1, 5] U₃ ![5, -1] ∧
      ¬Kaldor U₁ ![0, 0] U₃ ![5, -1] := by
  intro U₁ U₂ U₃
  refine ⟨⟨⟨![0, 0], Or.inr (by simp), le_rfl⟩, ?_⟩, ⟨⟨![-1, 5], Or.inr (by simp), le_rfl⟩, ?_⟩, ?_⟩
  · rintro ⟨w, hw, hle⟩
    have := (hle 1).trans (hw 1); norm_num at this
  · rintro ⟨w, hw | hw, hle⟩
    · have := (hle 0).trans (hw 0); norm_num at this
    · have := (hle 0).trans (hw 0); norm_num at this
  · rintro ⟨⟨w, hw | hw, hle⟩, -⟩
    · have := (hle 1).trans (hw 1); norm_num at this
    · have := (hle 0).trans (hw 0); norm_num at this

end MWG.WelfareBargaining
