/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGCoreFoundations.CoopGames

/-!
# The Shapley value (MWG Appendix A, pp. 679-682; Exercises 18.AA.4-18.AA.6)

TU games are Chapter 22's `Game n = Finset (Fin n) → ℝ` (with `v(∅) = 0`), and the Shapley value
(18.AA.3), the average marginal contribution over orderings, is Chapter 22's `shapley`. Here:

* (18.AA.1) for every two-player subgame (`egalitarian_pair`), and the two-player game
  (`formula_18_AA_1`);
* subgames `(S, v)` and the preservation-of-differences system (18.AA.2)
  (`IsEgalitarianSolution`): it has at most one solution (`egalitarian_unique`, strong induction
  on `|S|`, as in the book), with the displayed recursion for `Sh₁(I, v)`
  (`egalitarian_recursion`); a solution is `Shᵢ(S, v) = ∑_{T ⊆ S, i ∈ T} d_T(v)/|T|` with
  Chapter 22's Harsanyi dividends (`shapleyFamily`, `shapleyFamily_isEgalitarian`), so
  **Definition 18.AA.7** is well posed (`definition_18_AA_7`);
* (18.AA.3): the value of Definition 18.AA.7 is Chapter 22's `shapley` (`formula_18_AA_3`), also
  for every subgame (`shapley_subgame`); footnote 31 and the claim `∑ᵢ m(S(π, i), i) = v(I)`;
* (18.AA.4) (footnote 32): the subset formula equals the solution of (18.AA.2) on every subgame
  (`subsetFormula_eq_shapleyFamily`, via the identity
  `∑_{U ⊆ T ⊆ S} (|S|-|T|)!(|T|-1)!/|S|! = 1/|U|`), hence (18.AA.4) = (18.AA.3)
  (`formula_18_AA_4`); **Exercise 18.AA.4** (`exercise_18_AA_4`);
* properties (a)-(d) with footnote 33 (`shapley_symmetry_footnote_33`) and the characterization
  (`shapley_characterization`); **Exercises 18.AA.5-18.AA.6**.
-/

namespace MWG.CoreFoundations

variable {n : ℕ}

/-! ### Preservation of differences: (18.AA.1)-(18.AA.2), Definition 18.AA.7 -/

/-- **Appendix A** (MWG, p. 680). The subgame `(S, v)`: the restriction of `v` to the subsets of
`S` (represented as the game `T ↦ v(T ∩ S)` on all players, in which players outside `S` are
dummies). -/
def subgame (v : WelfareBargaining.Game n) (S : Finset (Fin n)) : WelfareBargaining.Game n :=
  fun T => v (T ∩ S)

/-- **Appendix A** (MWG, p. 681), (18.AA.2). A family `{Shᵢ(S, v)}_{S ⊆ I, i ∈ S}` is an
egalitarian solution: differences are preserved,
`Shᵢ(S, v) - Shᵢ(S \ {h}, v) = Sh_h(S, v) - Sh_h(S \ {i}, v)` for `i, h ∈ S`, and
`∑_{i∈S} Shᵢ(S, v) = v(S)` for every coalition `S`. -/
def IsEgalitarianSolution (v : WelfareBargaining.Game n)
    (φ : Finset (Fin n) → Fin n → ℝ) : Prop :=
  (∀ S : Finset (Fin n), ∀ i ∈ S, ∀ h ∈ S,
      φ S i - φ (S.erase h) i = φ S h - φ (S.erase i) h) ∧
    ∀ S : Finset (Fin n), S.Nonempty → ∑ i ∈ S, φ S i = v S

/-- **Appendix A** (MWG, p. 681). (18.AA.2) only involves the values `Shᵢ(S, v)` with `i ∈ S`. -/
theorem isEgalitarianSolution_congr {v : WelfareBargaining.Game n}
    {φ ψ : Finset (Fin n) → Fin n → ℝ} (h : ∀ S, ∀ i ∈ S, φ S i = ψ S i)
    (hφ : IsEgalitarianSolution v φ) : IsEgalitarianSolution v ψ := by
  classical
  refine ⟨fun S i hi j hj => ?_, fun S hS => ?_⟩
  · rcases eq_or_ne i j with rfl | hij
    · ring
    · have h1 := hφ.1 S i hi j hj
      rw [h S i hi, h S j hj, h (S.erase j) i (Finset.mem_erase.2 ⟨hij, hi⟩),
        h (S.erase i) j (Finset.mem_erase.2 ⟨hij.symm, hj⟩)] at h1
      exact h1
  · rw [← hφ.2 S hS]
    exact Finset.sum_congr rfl fun i hi => (h S i hi).symm

/-- **Appendix A** (MWG, p. 681). (18.AA.2) determines the numbers `Shᵢ(S, v)`, `i ∈ S`,
uniquely (induction on the size of `S`). -/
theorem egalitarian_unique {v : WelfareBargaining.Game n} {φ ψ : Finset (Fin n) → Fin n → ℝ}
    (hφ : IsEgalitarianSolution v φ) (hψ : IsEgalitarianSolution v ψ) :
    ∀ S : Finset (Fin n), ∀ i ∈ S, φ S i = ψ S i := by
  classical
  intro S
  induction S using Finset.strongInduction with
  | H S ih =>
    intro i hi
    have hconst : ∀ j ∈ S, φ S j - ψ S j = φ S i - ψ S i := by
      intro j hj
      rcases eq_or_ne i j with rfl | hij
      · rfl
      · have h1 := hφ.1 S i hi j hj
        have h2 := hψ.1 S i hi j hj
        have e1 := ih (S.erase j) (Finset.erase_ssubset hj) i (Finset.mem_erase.2 ⟨hij, hi⟩)
        have e2 := ih (S.erase i) (Finset.erase_ssubset hi) j
          (Finset.mem_erase.2 ⟨hij.symm, hj⟩)
        linarith
    have hsum : ∑ j ∈ S, (φ S j - ψ S j) = 0 := by
      rw [Finset.sum_sub_distrib, hφ.2 S ⟨i, hi⟩, hψ.2 S ⟨i, hi⟩, sub_self]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul] at hsum
    have hc : (S.card : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Finset.card_ne_zero_of_mem hi)
    have := (mul_eq_zero.1 hsum).resolve_left hc
    linarith

/-- **Appendix A** (MWG, p. 681). The recursion used in the uniqueness argument:
`Sh_j(S, v) = (1/|S|) [v(S) - ∑_{i ≠ j} Shᵢ(S \ {j}, v) + ∑_{i ≠ j} Sh_j(S \ {i}, v)]`
(the book's display for `j = 1`, `S = I`). -/
theorem egalitarian_recursion {v : WelfareBargaining.Game n}
    {φ : Finset (Fin n) → Fin n → ℝ} (hφ : IsEgalitarianSolution v φ)
    {S : Finset (Fin n)} {j : Fin n} (hj : j ∈ S) :
    φ S j = (1 / S.card) * (v S - ∑ i ∈ S.erase j, φ (S.erase j) i +
      ∑ i ∈ S.erase j, φ (S.erase i) j) := by
  classical
  have hi : ∀ i ∈ S.erase j, φ S i = φ S j + φ (S.erase j) i - φ (S.erase i) j := by
    intro i hi'
    have := hφ.1 S i (Finset.mem_of_mem_erase hi') j hj
    linarith
  have hsum := hφ.2 S ⟨j, hj⟩
  rw [← Finset.add_sum_erase S _ hj, Finset.sum_congr rfl hi, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_erase_of_mem hj, nsmul_eq_mul] at hsum
  have hc : (1 : ℝ) ≤ S.card := by exact_mod_cast Finset.card_pos.2 ⟨j, hj⟩
  have hcast : ((S.card - 1 : ℕ) : ℝ) = S.card - 1 := by
    rw [Nat.cast_sub (by exact_mod_cast hc)]; simp
  rw [hcast] at hsum
  field_simp
  linarith

/-- **Appendix A** (MWG, p. 680), (18.AA.1) for every two-player subgame `{a, b}`:
`Sh_a({a, b}, v) = v({a}) + (v({a, b}) - v({a}) - v({b}))/2`. -/
theorem egalitarian_pair {v : WelfareBargaining.Game n} {φ : Finset (Fin n) → Fin n → ℝ}
    (hφ : IsEgalitarianSolution v φ) {a b : Fin n} (hab : a ≠ b) :
    φ {a, b} a = v {a} + (v {a, b} - v {a} - v {b}) / 2 := by
  classical
  have h1 := hφ.1 {a, b} a (by simp) b (by simp)
  have ea : ({a, b} : Finset (Fin n)).erase b = {a} := by
    ext x; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hx, rfl | rfl⟩ <;> simp_all
    · rintro rfl; exact ⟨hab, Or.inl rfl⟩
  have eb : ({a, b} : Finset (Fin n)).erase a = {b} := by
    ext x; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hx, rfl | rfl⟩ <;> simp_all
    · rintro rfl; exact ⟨fun h => hab h.symm, Or.inr rfl⟩
  rw [ea, eb] at h1
  have hsa := hφ.2 {a} (Finset.singleton_nonempty a)
  have hsb := hφ.2 {b} (Finset.singleton_nonempty b)
  have hsab := hφ.2 {a, b} (by simp)
  rw [Finset.sum_singleton] at hsa hsb
  rw [Finset.sum_pair hab] at hsab
  linarith

/-- **Appendix A** (MWG, p. 681). The family `Shᵢ(S, v) = ∑_{T ⊆ S, i ∈ T} d_T(v)/|T|` built from
Chapter 22's Harsanyi dividends `d_T(v)`. -/
noncomputable def shapleyFamily (v : WelfareBargaining.Game n) (S : Finset (Fin n))
    (i : Fin n) : ℝ := by
  classical
  exact ∑ T ∈ S.powerset, if i ∈ T then WelfareBargaining.dividend v T / T.card else 0

/-- **Appendix A** (MWG, p. 681). The subsets of `S` not containing `h` are the subsets of
`S \\ {h}`. -/
theorem powerset_filter_not_mem (S : Finset (Fin n)) (h : Fin n) :
    S.powerset.filter (fun T => h ∉ T) = (S.erase h).powerset := by
  classical
  ext T; simp [Finset.subset_erase]

/-- **Appendix A** (MWG, p. 681). The dividend family satisfies (18.AA.2) (for `v(∅) = 0`). -/
theorem shapleyFamily_isEgalitarian (v : WelfareBargaining.Game n) (hv : v ∅ = 0) :
    IsEgalitarianSolution v (shapleyFamily v) := by
  classical
  refine ⟨fun S i _ h _ => ?_, fun S _ => ?_⟩
  · have key : ∀ i h : Fin n, shapleyFamily v S i - shapleyFamily v (S.erase h) i =
        ∑ T ∈ S.powerset, if h ∈ T ∧ i ∈ T then WelfareBargaining.dividend v T / T.card
          else 0 := by
      intro i h
      simp only [shapleyFamily]
      rw [← Finset.sum_filter_add_sum_filter_not S.powerset (fun T => h ∈ T),
        powerset_filter_not_mem, add_sub_cancel_right, Finset.sum_filter]
      refine Finset.sum_congr rfl fun T _ => ?_
      by_cases hh : h ∈ T <;> simp [hh]
    rw [key i h, key h i]
    exact Finset.sum_congr rfl fun T _ => by simp only [and_comm]
  · simp only [shapleyFamily]
    rw [Finset.sum_comm, ← WelfareBargaining.sum_dividend v S]
    refine Finset.sum_congr rfl fun T hT => ?_
    have hTS : S ∩ T = T := Finset.inter_eq_right.2 (Finset.mem_powerset.1 hT)
    rw [Finset.sum_ite_mem, hTS, Finset.sum_const, nsmul_eq_mul]
    rcases Finset.eq_empty_or_nonempty T with rfl | hne
    · simp [WelfareBargaining.dividend, hv]
    · exact mul_div_cancel₀ _ (Nat.cast_ne_zero.2 hne.card_pos.ne')

/-- **Definition 18.AA.7** (MWG, p. 681). The Shapley value `Sh(I, v)`: the outcome of the
solution of (18.AA.2) on the grand coalition. -/
noncomputable def shapleyMWG (v : WelfareBargaining.Game n) (i : Fin n) : ℝ :=
  shapleyFamily v Finset.univ i

/-- **Definition 18.AA.7** (MWG, p. 681). The Shapley value is well defined: there is exactly
one outcome `Sh(I, v)` consistent with (18.AA.2), namely `shapleyMWG v`. -/
theorem definition_18_AA_7 (v : WelfareBargaining.Game n) (hv : v ∅ = 0) :
    ∃! x : Fin n → ℝ, ∃ φ, IsEgalitarianSolution v φ ∧ ∀ i, φ Finset.univ i = x i := by
  refine ⟨shapleyMWG v, ⟨shapleyFamily v, shapleyFamily_isEgalitarian v hv, fun _ => rfl⟩, ?_⟩
  rintro x ⟨φ, hφ, hx⟩
  funext i
  rw [← hx i]
  exact egalitarian_unique hφ (shapleyFamily_isEgalitarian v hv) _ i (Finset.mem_univ i)

/-- **Appendix A** (MWG, p. 680), (18.AA.1). For two players the Shapley value is the
egalitarian solution `Shᵢ(I, v) = v({i}) + (v(I) - v({1}) - v({2}))/2`. -/
theorem formula_18_AA_1 (v : WelfareBargaining.Game 2) (hv : v ∅ = 0) :
    shapleyMWG v 0 = v {0} + (v Finset.univ - v {0} - v {1}) / 2 ∧
      shapleyMWG v 1 = v {1} + (v Finset.univ - v {0} - v {1}) / 2 := by
  have hu : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide
  have hu' : (Finset.univ : Finset (Fin 2)) = {1, 0} := by decide
  have h := shapleyFamily_isEgalitarian v hv
  constructor
  · simp only [shapleyMWG]
    rw [hu, egalitarian_pair h (by decide)]
  · simp only [shapleyMWG]
    rw [hu', egalitarian_pair h (by decide), Finset.pair_comm]
    ring

/-! ### (18.AA.3): the Shapley value is the average marginal contribution -/

/-- **Appendix A** (MWG, p. 681), (18.AA.3). The Shapley value of Definition 18.AA.7 is the
average over all orderings of the marginal contributions (Chapter 22's `shapley`). -/
theorem formula_18_AA_3 (v : WelfareBargaining.Game n) (hv : v ∅ = 0) :
    shapleyMWG v = WelfareBargaining.shapley v := by
  classical
  rw [WelfareBargaining.value_eq_dividendValue WelfareBargaining.shapley_pareto
    WelfareBargaining.shapley_symmetric WelfareBargaining.shapley_dummy
    (fun v w _ _ => WelfareBargaining.exercise_22_F_3a v w) v hv]
  funext i
  simp only [shapleyMWG, shapleyFamily, WelfareBargaining.dividendValue]
  rw [Finset.sum_filter_of_ne]
  intro T _ hT
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty] at hne
  subst hne
  simp at hT

/-- **Appendix A** (MWG, p. 681), footnote 31: with the convention `v(∅) = 0`, the marginal
contribution `m(S, i) = v(S ∪ {i}) - v(S)` to the empty coalition is `v({i})`. -/
theorem footnote_18_31 (v : WelfareBargaining.Game n) (hv : v ∅ = 0) (i : Fin n) :
    v (insert i ∅) - v ∅ = v {i} := by
  simp [hv]

/-- **Appendix A** (MWG, p. 681). Along every ordering `π`, the marginal contributions of the
players to their predecessors `S(π, i) = {h : π(h) < π(i)}` exhaust `v(I)`:
`∑ᵢ m(S(π, i), i) = v(I)` (Chapter 22's `sum_margContrib`). -/
theorem sum_marginal_contributions (v : WelfareBargaining.Game n) (hv : v ∅ = 0)
    (σ : Equiv.Perm (Fin n)) :
    ∑ i, (v (insert i (WelfareBargaining.preds σ i)) - v (WelfareBargaining.preds σ i)) =
      v Finset.univ :=
  WelfareBargaining.sum_margContrib v hv σ

/-- **Appendix A** (MWG, p. 681). The dividends of a subgame: `d_T((S, v)) = d_T(v)` if `T ⊆ S`, and
`0` otherwise. -/
theorem dividend_subgame (v : WelfareBargaining.Game n) (S T : Finset (Fin n)) :
    WelfareBargaining.dividend (subgame v S) T =
      if T ⊆ S then WelfareBargaining.dividend v T else 0 := by
  classical
  split_ifs with hTS
  · simp only [WelfareBargaining.dividend, subgame]
    refine Finset.sum_congr rfl fun R hR => ?_
    rw [Finset.inter_eq_left.2 ((Finset.mem_powerset.1 hR).trans hTS)]
  · obtain ⟨j, hjT, hjS⟩ := Finset.not_subset.1 hTS
    simp only [WelfareBargaining.dividend, subgame]
    rw [← Finset.insert_erase hjT, Finset.sum_powerset_insert (Finset.notMem_erase j T)]
    have hcard : (insert j (T.erase j)).card = (T.erase j).card + 1 :=
      Finset.card_insert_of_notMem (Finset.notMem_erase j T)
    rw [hcard, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun R hR => ?_
    have hRsub := Finset.mem_powerset.1 hR
    have hjR : j ∉ R := fun h => Finset.notMem_erase j T (hRsub h)
    have hRc : R.card ≤ (T.erase j).card := Finset.card_le_card hRsub
    rw [Finset.card_insert_of_notMem hjR, Finset.insert_inter_of_notMem hjS]
    have e : (T.erase j).card + 1 - R.card = ((T.erase j).card - R.card) + 1 := by omega
    have e' : (T.erase j).card + 1 - (R.card + 1) = (T.erase j).card - R.card := by omega
    rw [e, e', pow_succ]
    ring

/-- **Appendix A** (MWG, p. 681), (18.AA.3) for subgames: the Shapley value of the subgame
`(S, v)` (the average marginal contribution in the restricted game) is `Shᵢ(S, v)` of (18.AA.2),
for `i ∈ S`. -/
theorem shapley_subgame (v : WelfareBargaining.Game n) (hv : v ∅ = 0) (S : Finset (Fin n))
    (i : Fin n) : WelfareBargaining.shapley (subgame v S) i = shapleyFamily v S i := by
  classical
  have hv' : subgame v S ∅ = 0 := by simp [subgame, hv]
  rw [← formula_18_AA_3 _ hv']
  simp only [shapleyMWG, shapleyFamily, dividend_subgame]
  rw [← Finset.sum_subset (Finset.powerset_mono.2 (Finset.subset_univ S)) (fun T _ hT => ?_)]
  · refine Finset.sum_congr rfl fun T hT => ?_
    rw [Finset.mem_powerset] at hT
    simp [hT]
  · rw [Finset.mem_powerset] at hT
    simp [hT]

/-! ### (18.AA.4): the subset formula -/

/-- **Appendix A** (MWG, p. 682), (18.AA.4) for the subgame `(S, v)`:
`∑_{T ⊆ S, i ∈ T} (|S| - |T|)!(|T| - 1)!/|S|! · (v(T) - v(T \ {i}))` (footnote 32: `#T` is the
number of players in `T`). -/
noncomputable def subsetFormula (v : WelfareBargaining.Game n) (S : Finset (Fin n))
    (i : Fin n) : ℝ := by
  classical
  exact ∑ T ∈ S.powerset, if i ∈ T then
    ((S.card - T.card).factorial * (T.card - 1).factorial / S.card.factorial : ℝ) *
      (v T - v (T.erase i)) else 0

/-- **Appendix A** (MWG, p. 682). The hockey-stick identity
`∑_{j ≤ m} C(k + j, k) = C(k + m + 1, k + 1)`, used for (18.AA.4). -/
theorem hockey_stick (k m : ℕ) :
    ∑ j ∈ Finset.range (m + 1), (k + j).choose k = (k + m + 1).choose (k + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h := Nat.choose_succ_succ (k + m + 1) k
    rw [Finset.sum_range_succ, ih, show k + (m + 1) + 1 = (k + m + 1) + 1 by ring,
      show k + (m + 1) = k + m + 1 by ring, h]
    ring

/-- **Appendix A** (MWG, p. 682). `(k + 1) ∑_{j ≤ m} C(m, j)(m - j)!(k + j)! = (k + m + 1)!`, the
counting identity behind (18.AA.4). -/
theorem shapley_weight_sum_nat (k m : ℕ) :
    (k + 1) * ∑ j ∈ Finset.range (m + 1),
      m.choose j * (m - j).factorial * (k + j).factorial = (k + m + 1).factorial := by
  have hterm : ∀ j ∈ Finset.range (m + 1), m.choose j * (m - j).factorial * (k + j).factorial =
      m.factorial * k.factorial * (k + j).choose k := by
    intro j hj
    have hjm : j ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    have h1 := Nat.choose_mul_factorial_mul_factorial hjm
    have h2 := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right k j)
    rw [show k + j - k = j by omega] at h2
    rw [← h2, ← h1]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hockey_stick]
  have h3 := Nat.choose_mul_factorial_mul_factorial (show k + 1 ≤ k + m + 1 by omega)
  rw [show k + m + 1 - (k + 1) = m by omega, Nat.factorial_succ] at h3
  rw [← h3]
  ring

/-- **Appendix A** (MWG, p. 682). The weights of (18.AA.4) of the coalitions between `U` and `S` add
up to `1/|U|`. -/
theorem shapley_weight_sum {U S : Finset (Fin n)} (hU : U.Nonempty) (hUS : U ⊆ S) :
    ∑ T ∈ S.powerset.filter (fun T => U ⊆ T),
      ((S.card - T.card).factorial * (T.card - 1).factorial / S.card.factorial : ℝ) =
      1 / U.card := by
  classical
  set c : ℕ → ℝ := fun t =>
    ((S.card - t).factorial * (t - 1).factorial / S.card.factorial : ℝ) with hc
  have hbij : ∑ W ∈ (S \ U).powerset, c (U.card + W.card) =
      ∑ T ∈ S.powerset.filter (fun T => U ⊆ T), c T.card := by
    refine Finset.sum_nbij' (fun W => W ∪ U) (fun T => T \ U) ?_ ?_ ?_ ?_ ?_
    · intro W hW
      simp only [Finset.mem_powerset] at hW
      simp only [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨Finset.union_subset (hW.trans Finset.sdiff_subset) hUS, Finset.subset_union_right⟩
    · intro T hT
      simp only [Finset.mem_filter, Finset.mem_powerset] at hT
      simp only [Finset.mem_powerset]
      exact Finset.sdiff_subset_sdiff hT.1 le_rfl
    · intro W hW
      simp only [Finset.mem_powerset] at hW
      exact Finset.union_sdiff_cancel_right
        (Finset.disjoint_of_subset_left hW disjoint_sdiff_self_left)
    · intro T hT
      simp only [Finset.mem_filter, Finset.mem_powerset] at hT
      exact Finset.sdiff_union_of_subset hT.2
    · intro W hW
      simp only [Finset.mem_powerset] at hW
      rw [Finset.card_union_of_disjoint
        (Finset.disjoint_of_subset_left hW disjoint_sdiff_self_left), add_comm]
  rw [← hbij, Finset.sum_powerset_apply_card (fun w => c (U.card + w))]
  obtain ⟨k, hk⟩ : ∃ k, U.card = k + 1 := ⟨U.card - 1, by have := hU.card_pos; omega⟩
  have hsd : (S \ U).card = S.card - U.card := Finset.card_sdiff_of_subset hUS
  have hSU : U.card ≤ S.card := Finset.card_le_card hUS
  set m := (S \ U).card with hm
  have hS : S.card = k + m + 1 := by omega
  have hnat := shapley_weight_sum_nat k m
  have hreal : ((k + 1 : ℕ) : ℝ) * ∑ j ∈ Finset.range (m + 1),
      ((m.choose j * (m - j).factorial * (k + j).factorial : ℕ) : ℝ) =
      ((k + m + 1).factorial : ℝ) := by
    rw [← Nat.cast_sum, ← Nat.cast_mul, hnat]
  have hterm : ∀ j ∈ Finset.range (m + 1), (m.choose j) • c (U.card + j) =
      ((m.choose j * (m - j).factorial * (k + j).factorial : ℕ) : ℝ) /
        ((k + m + 1).factorial : ℝ) := by
    intro j hj
    have hjm : j ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    simp only [hc, nsmul_eq_mul]
    rw [hk, hS, show k + m + 1 - (k + 1 + j) = m - j by omega,
      show k + 1 + j - 1 = k + j by omega]
    push_cast
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div, hk]
  have hfac : ((k + m + 1).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have hk1 : ((k + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.succ_ne_zero k)
  rw [div_eq_div_iff hfac hk1]
  rw [← hreal]
  push_cast
  ring

/-- **Appendix A** (MWG, p. 682). `v(T) - v(T \ {i}) = ∑_{U ⊆ T, i ∈ U} d_U(v)`. -/
theorem sub_erase_eq_sum_dividend (v : WelfareBargaining.Game n) (T : Finset (Fin n))
    (i : Fin n) :
    v T - v (T.erase i) =
      ∑ U ∈ T.powerset, if i ∈ U then WelfareBargaining.dividend v U else 0 := by
  classical
  rw [← WelfareBargaining.sum_dividend v T, ← WelfareBargaining.sum_dividend v (T.erase i),
    ← Finset.sum_filter_add_sum_filter_not T.powerset (fun U => i ∈ U),
    powerset_filter_not_mem, add_sub_cancel_right, Finset.sum_filter]

/-- **Appendix A** (MWG, p. 682), (18.AA.4) on every subgame: the subset formula equals the
solution of (18.AA.2). -/
theorem subsetFormula_eq_shapleyFamily (v : WelfareBargaining.Game n) (S : Finset (Fin n))
    (i : Fin n) : subsetFormula v S i = shapleyFamily v S i := by
  classical
  set c : Finset (Fin n) → ℝ := fun T =>
    ((S.card - T.card).factorial * (T.card - 1).factorial / S.card.factorial : ℝ) with hc
  have h1 : subsetFormula v S i = ∑ T ∈ S.powerset, ∑ U ∈ T.powerset,
      (if i ∈ U then c T * WelfareBargaining.dividend v U else 0) := by
    simp only [subsetFormula]
    refine Finset.sum_congr rfl fun T _ => ?_
    by_cases hi : i ∈ T
    · simp only [hi, ↓reduceIte]
      rw [sub_erase_eq_sum_dividend v T i, Finset.mul_sum]
      refine Finset.sum_congr rfl fun U _ => ?_
      split_ifs <;> simp [hc]
    · simp only [hi, ↓reduceIte]
      refine (Finset.sum_eq_zero fun U hU => ?_).symm
      have : i ∉ U := fun h => hi (Finset.mem_powerset.1 hU h)
      simp [this]
  rw [h1, Finset.sum_comm' (t' := S.powerset) (s' := fun U => S.powerset.filter (fun T => U ⊆ T))
    (fun T U => by
      simp only [Finset.mem_powerset, Finset.mem_filter]
      exact ⟨fun h => ⟨⟨h.1, h.2⟩, h.2.trans h.1⟩, fun h => ⟨h.1.1, h.1.2⟩⟩)]
  simp only [shapleyFamily]
  refine Finset.sum_congr rfl fun U hU => ?_
  by_cases hi : i ∈ U
  · simp only [hi, ↓reduceIte]
    rw [← Finset.sum_mul, hc]
    rw [shapley_weight_sum ⟨i, hi⟩ (Finset.mem_powerset.1 hU)]
    ring
  · simp [hi]

/-- **Appendix A** (MWG, p. 682), (18.AA.4) = (18.AA.3): the subset formula on the grand
coalition is the Shapley value. -/
theorem formula_18_AA_4 (v : WelfareBargaining.Game n) (hv : v ∅ = 0) (i : Fin n) :
    subsetFormula v Finset.univ i = WelfareBargaining.shapley v i := by
  rw [subsetFormula_eq_shapleyFamily, ← formula_18_AA_3 v hv]
  rfl

/-- **Exercise 18.AA.4** (MWG, p. 685). If the Shapley value of every subgame is defined by
(18.AA.4), or equivalently by (18.AA.3) (the average marginal contribution in the subgame), then
the preservation-of-differences system (18.AA.2) is satisfied. -/
theorem exercise_18_AA_4 (v : WelfareBargaining.Game n) (hv : v ∅ = 0) :
    IsEgalitarianSolution v (subsetFormula v) ∧
      IsEgalitarianSolution v (fun S i => WelfareBargaining.shapley (subgame v S) i) := by
  have h := shapleyFamily_isEgalitarian v hv
  refine ⟨isEgalitarianSolution_congr (fun S i _ => ?_) h,
    isEgalitarianSolution_congr (fun S i _ => ?_) h⟩
  · exact (subsetFormula_eq_shapleyFamily v S i).symm
  · exact (shapley_subgame v hv S i).symm

/-! ### Properties (a)-(d) and the characterization (pp. 682-683; Exercises 18.AA.5-18.AA.6) -/

/-- **Appendix A** (MWG, p. 682), property (a), efficiency: `∑ᵢ Shᵢ(I, v) = v(I)`. -/
theorem shapley_efficiency (v : WelfareBargaining.Game n) (hv : v ∅ = 0) :
    ∑ i, WelfareBargaining.shapley v i = v Finset.univ :=
  WelfareBargaining.shapley_pareto v hv

/-- **Appendix A** (MWG, p. 682), footnote 33: the games `v` and `v'` are identical except that
the roles of players `i` and `h` are permuted. -/
def RolesPermuted (v v' : WelfareBargaining.Game n) (i h : Fin n) : Prop :=
  ∀ S : Finset (Fin n), (i ∈ S → h ∈ S → v S = v' S) ∧ (i ∉ S → h ∉ S → v S = v' S) ∧
    (i ∈ S → h ∉ S → v S = v' (insert h (S.erase i))) ∧
    (h ∈ S → i ∉ S → v S = v' (insert i (S.erase h)))

/-- **Appendix A** (MWG, p. 682), footnote 33. The transposition of `i` and `h` fixes a coalition
containing both or neither. -/
theorem map_swap_of_iff {i h : Fin n} {S : Finset (Fin n)} (hS : i ∈ S ↔ h ∈ S) :
    S.map (Equiv.swap i h).toEmbedding = S := by
  ext x
  rw [Finset.mem_map_equiv, Equiv.symm_swap]
  rcases eq_or_ne x i with rfl | hxi
  · rw [Equiv.swap_apply_left]; exact hS.symm
  rcases eq_or_ne x h with rfl | hxh
  · rw [Equiv.swap_apply_right]; exact hS
  rw [Equiv.swap_apply_of_ne_of_ne hxi hxh]

/-- **Appendix A** (MWG, p. 682), footnote 33. The transposition of `i ∈ S` and `h ∉ S` maps `S` to
`(S \\ {i}) ∪ {h}`. -/
theorem map_swap_of_mem_notMem {i h : Fin n} {S : Finset (Fin n)} (hi : i ∈ S) (hh : h ∉ S) :
    S.map (Equiv.swap i h).toEmbedding = insert h (S.erase i) := by
  have hih : i ≠ h := fun e => hh (e ▸ hi)
  ext x
  rw [Finset.mem_map_equiv, Equiv.symm_swap, Finset.mem_insert, Finset.mem_erase]
  rcases eq_or_ne x i with rfl | hxi
  · rw [Equiv.swap_apply_left]; simp [hh, hih]
  rcases eq_or_ne x h with rfl | hxh
  · rw [Equiv.swap_apply_right]; simp [hi]
  rw [Equiv.swap_apply_of_ne_of_ne hxi hxh]; simp [hxi, hxh]

/-- **Appendix A** (MWG, p. 682), footnote 33: the roles of `i` and `h` are permuted iff
`v(S) = v'(τ(S))` for the transposition `τ` of `i` and `h` (Chapter 22's formulation). -/
theorem rolesPermuted_iff (v v' : WelfareBargaining.Game n) (i h : Fin n) :
    RolesPermuted v v' i h ↔ ∀ S, v S = v' (S.map (Equiv.swap i h).toEmbedding) := by
  constructor
  · intro hp S
    by_cases hi : i ∈ S <;> by_cases hh : h ∈ S
    · rw [map_swap_of_iff (iff_of_true hi hh)]; exact (hp S).1 hi hh
    · rw [map_swap_of_mem_notMem hi hh]; exact (hp S).2.2.1 hi hh
    · rw [Equiv.swap_comm, map_swap_of_mem_notMem hh hi]; exact (hp S).2.2.2 hh hi
    · rw [map_swap_of_iff (iff_of_false hi hh)]; exact (hp S).2.1 hi hh
  · intro hm S
    refine ⟨fun hi hh => ?_, fun hi hh => ?_, fun hi hh => ?_, fun hh hi => ?_⟩
    · rw [hm, map_swap_of_iff (iff_of_true hi hh)]
    · rw [hm, map_swap_of_iff (iff_of_false hi hh)]
    · rw [hm, map_swap_of_mem_notMem hi hh]
    · rw [hm, Equiv.swap_comm, map_swap_of_mem_notMem hh hi]

/-- **Appendix A** (MWG, p. 682), property (b), symmetry in the sense of footnote 33: if `v'` is
`v` with the roles of `i` and `h` permuted then `Shᵢ(I, v) = Sh_h(I, v')`. -/
theorem shapley_symmetry_footnote_33 {v v' : WelfareBargaining.Game n} (hv : v ∅ = 0)
    {i h : Fin n} (hp : RolesPermuted v v' i h) :
    WelfareBargaining.shapley v i = WelfareBargaining.shapley v' h := by
  have hv' : v' ∅ = 0 := by rw [← ((hp ∅).2.1 (by simp) (by simp)), hv]
  have hm : v = fun S => v' (S.map (Equiv.swap i h).toEmbedding) :=
    funext ((rolesPermuted_iff v v' i h).1 hp)
  rw [hm, WelfareBargaining.shapley_symmetric v' (Equiv.swap i h) hv' i,
    Equiv.swap_apply_left]

/-- **Appendix A** (MWG, p. 682), property (c), linearity:
`Sh(I, αv + βw) = α Sh(I, v) + β Sh(I, w)`. -/
theorem shapley_linearity (a b : ℝ) (v w : WelfareBargaining.Game n) :
    WelfareBargaining.shapley (a • v + b • w) =
      a • WelfareBargaining.shapley v + b • WelfareBargaining.shapley w := by
  rw [WelfareBargaining.exercise_22_F_3a, WelfareBargaining.shapley_smul,
    WelfareBargaining.shapley_smul]

/-- **Appendix A** (MWG, p. 682), property (d), the dummy axiom: if
`v(S ∪ {i}) - v(S) = 0` for all `S` then `Shᵢ(I, v) = 0`. -/
theorem shapley_dummy_axiom {v : WelfareBargaining.Game n} (hv : v ∅ = 0) {i : Fin n}
    (hd : ∀ S, v (insert i S) - v S = 0) : WelfareBargaining.shapley v i = 0 :=
  WelfareBargaining.shapley_dummy v i hv fun S => sub_eq_zero.1 (hd S)

/-- **Appendix A** (MWG, p. 682). Symmetry of a solution `f` in the sense of property (b) and
footnote 33. -/
def MWGSymmetric (f : WelfareBargaining.Game n → Fin n → ℝ) : Prop :=
  ∀ (v v' : WelfareBargaining.Game n) (i h : Fin n), v ∅ = 0 → RolesPermuted v v' i h →
    f v i = f v' h

/-- **Appendix A** (MWG, p. 682). The Shapley value is symmetric in the sense of footnote 33. -/
theorem shapley_mwgSymmetric : MWGSymmetric (WelfareBargaining.shapley (n := n)) :=
  fun _ _ _ _ hv hp => shapley_symmetry_footnote_33 hv hp

/-- **Exercise 18.AA.5** (MWG, p. 686). A unanimity game: there is a coalition `S` with
`v(T) = v(S)` if `S ⊆ T` and `v(T) = 0` otherwise. -/
def IsUnanimityGame (v : WelfareBargaining.Game n) (S : Finset (Fin n)) : Prop :=
  S.Nonempty ∧ ∀ T, v T = if S ⊆ T then v S else 0

/-- **Exercise 18.AA.5** (MWG, p. 686). Chapter 22's `unanimity S c` is a unanimity game. -/
theorem isUnanimityGame_unanimity {S : Finset (Fin n)} (hS : S.Nonempty) (c : ℝ) :
    IsUnanimityGame (WelfareBargaining.unanimity S c) S := by
  classical
  refine ⟨hS, fun T => ?_⟩
  simp [WelfareBargaining.unanimity]

/-- **Exercise 18.AA.5** (MWG, p. 686). Efficiency, symmetry (footnote 33) and the dummy axiom
force a solution to distribute `v(S)` equally among the members of `S` in a unanimity game. -/
theorem exercise_18_AA_5 {f : WelfareBargaining.Game n → Fin n → ℝ}
    (hP : WelfareBargaining.CoopPareto f) (hS : MWGSymmetric f)
    (hD : WelfareBargaining.CoopDummy f) {v : WelfareBargaining.Game n} {S : Finset (Fin n)}
    (hu : IsUnanimityGame v S) (i : Fin n) :
    f v i = if i ∈ S then v S / S.card else 0 := by
  classical
  obtain ⟨hSne, hv⟩ := hu
  have h0 : v ∅ = 0 := by
    rw [hv ∅]; simp [Finset.subset_empty, hSne.ne_empty]
  have hdummy : ∀ j ∉ S, f v j = 0 := by
    intro j hj
    refine hD v j h0 fun T => ?_
    rw [hv (insert j T), hv T]
    have : S ⊆ insert j T ↔ S ⊆ T :=
      ⟨fun h x hx => (Finset.mem_insert.1 (h hx)).resolve_left fun e => hj (e ▸ hx),
        fun h => h.trans (Finset.subset_insert _ _)⟩
    simp only [this]
  have hequal : ∀ j ∈ S, ∀ k ∈ S, f v j = f v k := by
    intro j hj k hk
    refine hS v v j k h0 ((rolesPermuted_iff v v j k).2 fun T => ?_)
    rw [hv T, hv (T.map _)]
    have hS' : S.map (Equiv.swap j k).toEmbedding = S := map_swap_of_iff (iff_of_true hj hk)
    have : S ⊆ T.map (Equiv.swap j k).toEmbedding ↔ S ⊆ T := by
      conv_lhs => rw [← hS']
      exact Finset.map_subset_map
    simp only [this]
  have hsum := hP v h0
  obtain ⟨t, ht⟩ := hSne
  have hsplit : ∑ j, f v j = S.card * f v t := by
    rw [← Finset.sum_subset (Finset.subset_univ S) fun j _ hj => hdummy j hj,
      Finset.sum_congr rfl fun j hj => hequal j hj t ht]
    simp
  have hvS : v Finset.univ = v S := by rw [hv]; simp
  have hcard : (0 : ℝ) < S.card := Nat.cast_pos.2 (Finset.card_pos.2 ⟨t, ht⟩)
  split_ifs with hi
  · rw [hequal i hi t ht]
    rw [hsplit, hvS] at hsum
    rw [eq_div_iff hcard.ne']
    linarith
  · exact hdummy i hi

/-- **Exercise 18.AA.6** (MWG, p. 686). Every TU game (`v(∅) = 0`) is a linear combination of
unanimity games, with the Harsanyi dividends as coefficients (Chapter 22's
`eq_sum_unanimity`). -/
theorem exercise_18_AA_6_decomposition (v : WelfareBargaining.Game n) (hv : v ∅ = 0) :
    v = fun S => ∑ T ∈ (Finset.univ.powerset.filter fun T : Finset (Fin n) => T.Nonempty),
      WelfareBargaining.unanimity T (WelfareBargaining.dividend v T) S :=
  WelfareBargaining.eq_sum_unanimity v hv

/-- **Exercise 18.AA.6** (MWG, p. 686). The coefficients of the decomposition are unique: if
`v = ∑_{T ≠ ∅} c_T u_T` then `c_T = d_T(v)` for every coalition `T`. -/
theorem exercise_18_AA_6_unique (v : WelfareBargaining.Game n) (c : Finset (Fin n) → ℝ)
    (hc : ∀ S, v S = ∑ T ∈ (Finset.univ.powerset.filter fun T : Finset (Fin n) => T.Nonempty),
      WelfareBargaining.unanimity T (c T) S) :
    ∀ T : Finset (Fin n), T.Nonempty → c T = WelfareBargaining.dividend v T := by
  classical
  set c' : Finset (Fin n) → ℝ := fun T => if T.Nonempty then c T else 0 with hc'
  have hv : ∀ S, v S = ∑ T ∈ S.powerset, c' T := by
    intro S
    rw [hc S]
    simp only [WelfareBargaining.unanimity, hc']
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.filter_filter]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
    apply Finset.sum_congr
    · ext T; simp [and_comm]
    · intro _ _; rfl
  set e : Finset (Fin n) → ℝ := fun T => c' T - WelfareBargaining.dividend v T with he
  have hsum : ∀ S : Finset (Fin n), ∑ T ∈ S.powerset, e T = 0 := by
    intro S
    simp only [he, Finset.sum_sub_distrib, ← hv S, WelfareBargaining.sum_dividend, sub_self]
  have hzero : ∀ S : Finset (Fin n), e S = 0 := by
    intro S
    induction S using Finset.strongInduction with
    | H S ih =>
      have h := hsum S
      rw [← Finset.add_sum_erase _ _ (Finset.mem_powerset_self S)] at h
      rw [Finset.sum_eq_zero fun T hT => ih T ?_] at h
      · simpa using h
      · obtain ⟨hne, hsub⟩ := Finset.mem_erase.1 hT
        exact Finset.ssubset_iff_subset_ne.2 ⟨Finset.mem_powerset.1 hsub, hne⟩
  intro T hT
  have := hzero T
  simp only [he, hc', hT, ↓reduceIte] at this
  linarith

/-- **Exercise 18.AA.6** (MWG, p. 686), and the characterization claim of p. 682: a solution
satisfying efficiency, symmetry (footnote 33), the dummy axiom and linearity is the Shapley value
(via Exercise 18.AA.5 and the decomposition into unanimity games). -/
theorem exercise_18_AA_6 {f : WelfareBargaining.Game n → Fin n → ℝ}
    (hP : WelfareBargaining.CoopPareto f) (hS : MWGSymmetric f)
    (hD : WelfareBargaining.CoopDummy f) (hL : WelfareBargaining.CoopLinear f)
    (v : WelfareBargaining.Game n) (hv : v ∅ = 0) : f v = WelfareBargaining.shapley v := by
  classical
  have hzero : f 0 = 0 := by
    have := hL 0 0 rfl rfl
    simp only [add_zero] at this
    have h2 : f 0 + f 0 = f 0 + 0 := by rw [← this, add_zero]
    exact add_left_cancel h2
  have key : ∀ A ⊆ (Finset.univ.powerset.filter fun T : Finset (Fin n) => T.Nonempty),
      f (fun S => ∑ T ∈ A, WelfareBargaining.unanimity T (WelfareBargaining.dividend v T) S) =
        ∑ T ∈ A, f (WelfareBargaining.unanimity T (WelfareBargaining.dividend v T)) := by
    intro A
    induction A using Finset.induction_on with
    | empty => intro _; simp only [Finset.sum_empty]; exact hzero
    | insert T A hTA ih =>
      intro hsub
      have hT : T.Nonempty := (Finset.mem_filter.1 (hsub (Finset.mem_insert_self T A))).2
      have hA : A ⊆ _ := (Finset.subset_insert T A).trans hsub
      have hsplit : (fun S => ∑ T' ∈ insert T A,
          WelfareBargaining.unanimity T' (WelfareBargaining.dividend v T') S) =
          WelfareBargaining.unanimity T (WelfareBargaining.dividend v T) +
            fun S => ∑ T' ∈ A,
              WelfareBargaining.unanimity T' (WelfareBargaining.dividend v T') S := by
        funext S; simp [Finset.sum_insert hTA]
      have h0 : (fun S => ∑ T' ∈ A,
          WelfareBargaining.unanimity T' (WelfareBargaining.dividend v T') S) ∅ = 0 :=
        Finset.sum_eq_zero fun T' hT' =>
          WelfareBargaining.unanimity_empty (Finset.mem_filter.1 (hA hT')).2 _
      rw [hsplit, hL _ _ (WelfareBargaining.unanimity_empty hT _) h0, ih hA,
        Finset.sum_insert hTA]
  rw [WelfareBargaining.value_eq_dividendValue WelfareBargaining.shapley_pareto
    WelfareBargaining.shapley_symmetric WelfareBargaining.shapley_dummy
    (fun v w _ _ => WelfareBargaining.exercise_22_F_3a v w) v hv]
  conv_lhs => rw [WelfareBargaining.eq_sum_unanimity v hv]
  rw [key _ subset_rfl]
  funext i
  simp only [Finset.sum_apply, WelfareBargaining.dividendValue]
  refine Finset.sum_congr rfl fun T hT => ?_
  have hu := isUnanimityGame_unanimity (Finset.mem_filter.1 hT).2 (WelfareBargaining.dividend v T)
  rw [exercise_18_AA_5 hP hS hD hu i]
  classical
  simp [WelfareBargaining.unanimity]

/-- **Appendix A** (MWG, p. 682). The four properties (a)-(d) characterize the Shapley value: the
Shapley value has them, and any solution with them is the Shapley value. -/
theorem shapley_characterization :
    (WelfareBargaining.CoopPareto (WelfareBargaining.shapley (n := n)) ∧
      MWGSymmetric (WelfareBargaining.shapley (n := n)) ∧
      WelfareBargaining.CoopLinear (WelfareBargaining.shapley (n := n)) ∧
      WelfareBargaining.CoopDummy (WelfareBargaining.shapley (n := n))) ∧
    ∀ f : WelfareBargaining.Game n → Fin n → ℝ, WelfareBargaining.CoopPareto f →
      MWGSymmetric f → WelfareBargaining.CoopDummy f → WelfareBargaining.CoopLinear f →
      ∀ v, v ∅ = 0 → f v = WelfareBargaining.shapley v :=
  ⟨⟨WelfareBargaining.shapley_pareto, shapley_mwgSymmetric,
    fun v w _ _ => WelfareBargaining.exercise_22_F_3a v w, WelfareBargaining.shapley_dummy⟩,
    fun _ hP hS hD hL v hv => exercise_18_AA_6 hP hS hD hL v hv⟩

end MWG.CoreFoundations
