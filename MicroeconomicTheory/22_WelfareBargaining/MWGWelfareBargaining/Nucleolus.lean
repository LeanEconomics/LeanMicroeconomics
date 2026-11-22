/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGWelfareBargaining.Shapley
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# Three-agent computations: the cost-allocation example and the nucleolus

MWG, Example 22.F.1 (p. 849) and Exercise 22.F.5 (pp. 855-856).

* `shapley3`: the Shapley value of a three-agent game as an explicit sum over the six orderings.
* `example_22_F_1`: the air fare `C(B) = C(S) = C(G) = 800`, `C(BS) = C(BG) = 1000`,
  `C(SG) = 1400`, `C(BSG) = 1600` is split `400, 600, 600` by the Shapley value.
* Exercise 22.F.5: `I = 3`, `v(i) = 0`, `0 ≤ v(S) ≤ v(I)` for two-agent `S`. Writing
  `cₖ = v(I) - v(I \ {k})`, the excess of the coalition `I \ {k}` at an exactly feasible `u` is
  `uₖ - cₖ` (`pairEx_eq`), and the three excesses always add up to `v(I) - ∑ cₖ`. With
  `t = (v(I) - ∑ cₖ)/3`, the nucleolus is `c + t𝟙` if this is nonnegative; otherwise exactly one
  `k` has `cₖ + t < 0`, `uₖ = 0` and the other two equalize their excesses.
  `nucleolus_of_equal`, `nucleolus_of_corner`: these points are nucleoli and the only ones;
  `exercise_22_F_5a`, `exercise_22_F_5b` (existence and uniqueness), `exercise_22_F_5c`
  (symmetry), `exercise_22_F_5d` (dummy), `exercise_22_F_5e`, `exercise_22_F_5f`
  (nucleolus `(4/3, 7/3, 7/3)` vs Shapley `(5/3, 13/6, 13/6)`), `exercise_22_F_5g` (core).
  The second maximum excess is defined as `∑ eₖ - max - min`; `m2_eq_book` shows it is the
  book's `max {e(u, S') : S' ≠ S}` for any `S` attaining the first maximum.
-/

namespace MWG.WelfareBargaining

/-- The six orderings of three agents. -/
theorem univ_perm3 : (Finset.univ : Finset (Equiv.Perm (Fin 3))) =
    {1, Equiv.swap 0 1, Equiv.swap 0 2, Equiv.swap 1 2,
      Equiv.swap 0 1 * Equiv.swap 0 2, Equiv.swap 0 2 * Equiv.swap 0 1} := by decide

/-- **Definition 22.F.6** (MWG, p. 848) for three agents: `fₛ,ᵢ(v) = (1/6) ∑_π g_{v,π}(i)`. -/
theorem shapley3 (v : Game 3) (i : Fin 3) : shapley v i = (1 / 6) * ∑ π' ∈
    ({1, Equiv.swap 0 1, Equiv.swap 0 2, Equiv.swap 1 2,
      Equiv.swap 0 1 * Equiv.swap 0 2, Equiv.swap 0 2 * Equiv.swap 0 1} :
      Finset (Equiv.Perm (Fin 3))), margContrib v π' i := by
  simp only [shapley, ← univ_perm3]
  norm_num [Nat.factorial]

theorem shapley3_expand (v : Game 3) (i : Fin 3) : shapley v i = (1 / 6) *
    (margContrib v 1 i + margContrib v (Equiv.swap 0 1) i + margContrib v (Equiv.swap 0 2) i +
      margContrib v (Equiv.swap 1 2) i + margContrib v (Equiv.swap 0 1 * Equiv.swap 0 2) i +
      margContrib v (Equiv.swap 0 2 * Equiv.swap 0 1) i) := by
  rw [shapley3, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

/-- The cost game of Example 22.F.1: Britain `0`, Spain `1`, Germany `2`. -/
noncomputable def tourCost : Game 3 := fun S =>
  if S.card = 0 then 0 else if S.card = 1 then 800 else if S.card = 3 then 1600
  else if 0 ∈ S then 1000 else 1400

/-- **Example 22.F.1** (MWG, p. 849). The Shapley value splits the `1600` air fare as `400` for
Britain and `600` each for Spain and Germany. -/
theorem example_22_F_1 : shapley tourCost 0 = 400 ∧ shapley tourCost 1 = 600 ∧
    shapley tourCost 2 = 600 := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · rw [shapley3_expand]
    simp +decide only [margContrib, tourCost]
    norm_num

/-! ### Exercise 22.F.5: the nucleolus -/

/-- The worth of the two-agent coalition `I \ {k}` used in `cₖ = v(I) - v(I \ {k})`. -/
def nucC (v : Game 3) (k : Fin 3) : ℝ := v Finset.univ - v (Finset.univ.erase k)

/-- The excess `e(u, I \ {k}) = v(I \ {k}) - ∑_{i ≠ k} uᵢ` of a two-agent coalition. -/
def pairEx (v : Game 3) (u : Fin 3 → ℝ) (k : Fin 3) : ℝ :=
  v (Finset.univ.erase k) - ∑ i ∈ Finset.univ.erase k, u i

/-- Exactly feasible utility profiles: `u ≥ 0`, `∑ uᵢ = v(I)`. -/
def Feas3 (v : Game 3) (u : Fin 3 → ℝ) : Prop := (∀ i, 0 ≤ u i) ∧ ∑ i, u i = v Finset.univ

/-- The largest of three numbers. -/
noncomputable def max3 (e : Fin 3 → ℝ) : ℝ := Finset.univ.sup' Finset.univ_nonempty e

/-- The smallest of three numbers. -/
noncomputable def min3 (e : Fin 3 → ℝ) : ℝ := Finset.univ.inf' Finset.univ_nonempty e

/-- **Exercise 22.F.5** (MWG, p. 855). The first maximum excess `m₁(u)`. -/
noncomputable def nucM1 (v : Game 3) (u : Fin 3 → ℝ) : ℝ := max3 (pairEx v u)

/-- **Exercise 22.F.5** (MWG, p. 855). The second maximum excess `m₂(u)`: the middle value of
the three excesses (`m2_eq_book`). -/
noncomputable def nucM2 (v : Game 3) (u : Fin 3 → ℝ) : ℝ :=
  ∑ k, pairEx v u k - max3 (pairEx v u) - min3 (pairEx v u)

/-- **Exercise 22.F.5** (MWG, p. 855). `u` is in the nucleolus: it is exactly feasible and
lexicographically minimizes `(m₁, m₂)` among exactly feasible profiles. -/
def IsNucleolus (v : Game 3) (u : Fin 3 → ℝ) : Prop :=
  Feas3 v u ∧ ∀ u', Feas3 v u' →
    nucM1 v u < nucM1 v u' ∨ (nucM1 v u = nucM1 v u' ∧ nucM2 v u ≤ nucM2 v u')

/-- The standing assumptions of Exercise 22.F.5. -/
def NucGame (v : Game 3) : Prop :=
  v ∅ = 0 ∧ (∀ i, v {i} = 0) ∧ ∀ k, 0 ≤ v (Finset.univ.erase k) ∧
    v (Finset.univ.erase k) ≤ v Finset.univ

theorem le_max3 (e : Fin 3 → ℝ) (l : Fin 3) : e l ≤ max3 e :=
  Finset.le_sup' e (Finset.mem_univ l)

theorem min3_le (e : Fin 3 → ℝ) (l : Fin 3) : min3 e ≤ e l :=
  Finset.inf'_le e (Finset.mem_univ l)

theorem max3_attained (e : Fin 3 → ℝ) : ∃ l, max3 e = e l := by
  obtain ⟨l, -, h⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty e
  exact ⟨l, h⟩

theorem min3_attained (e : Fin 3 → ℝ) : ∃ l, min3 e = e l := by
  obtain ⟨l, -, h⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty e
  exact ⟨l, h⟩

/-- At an exactly feasible profile the excess of `I \ {k}` is `uₖ - cₖ`. -/
theorem pairEx_eq {v : Game 3} {u : Fin 3 → ℝ} (hu : ∑ i, u i = v Finset.univ) (k : Fin 3) :
    pairEx v u k = u k - nucC v k := by
  have := Finset.add_sum_erase Finset.univ u (Finset.mem_univ k)
  unfold pairEx nucC
  linarith

theorem sum3 (e : Fin 3 → ℝ) : ∑ l, e l = e 0 + e 1 + e 2 := Fin.sum_univ_three e

/-- The largest excess is at least their mean, with equality only if they are all equal. -/
theorem max3_ge_mean (e : Fin 3 → ℝ) : (∑ l, e l) / 3 ≤ max3 e := by
  have := le_max3 e 0; have := le_max3 e 1; have := le_max3 e 2
  rw [sum3]; linarith

theorem eq_of_max3_eq_mean {e : Fin 3 → ℝ} (h : max3 e = (∑ l, e l) / 3) (l : Fin 3) :
    e l = (∑ k, e k) / 3 := by
  have h0 := le_max3 e 0; have h1 := le_max3 e 1; have h2 := le_max3 e 2
  rw [sum3] at h ⊢
  fin_cases l <;> simp <;> linarith

/-- The excesses determine the profile: `uₖ = eₖ + cₖ`. -/
theorem eq_of_pairEx_eq {v : Game 3} {u u' : Fin 3 → ℝ} (hu : Feas3 v u) (hu' : Feas3 v u')
    (h : ∀ k, pairEx v u k = pairEx v u' k) : u = u' := by
  funext k
  have := h k
  rw [pairEx_eq hu.2, pairEx_eq hu'.2] at this
  linarith

/-- **Exercise 22.F.5(a)-(b)**, first case. If an exactly feasible `u*` has three equal excesses
it is the unique nucleolus. -/
theorem nucleolus_of_equal {v : Game 3} {u : Fin 3 → ℝ} (hu : Feas3 v u)
    (heq : ∀ k, pairEx v u k = pairEx v u 0) :
    IsNucleolus v u ∧ ∀ w, IsNucleolus v w → w = u := by
  set t := pairEx v u 0
  have hsum : ∀ w, Feas3 v w → ∑ k, pairEx v w k = ∑ k, pairEx v u k := by
    intro w hw
    simp only [pairEx_eq hw.2, pairEx_eq hu.2, Finset.sum_sub_distrib, hw.2, hu.2]
  have hm1u : nucM1 v u = t := by
    obtain ⟨l, hl⟩ := max3_attained (pairEx v u)
    simp only [nucM1, hl, heq l]
  have hsumu : ∑ k, pairEx v u k = 3 * t := by rw [sum3, heq 1, heq 2]; ring
  have hlow : ∀ w, Feas3 v w → t ≤ nucM1 v w := by
    intro w hw
    have := max3_ge_mean (pairEx v w)
    rw [hsum w hw, hsumu] at this
    simp only [nucM1]; linarith
  have heqw : ∀ w, Feas3 v w → nucM1 v w = t → w = u := by
    intro w hw hm
    refine eq_of_pairEx_eq hw hu fun k => ?_
    have h1 := eq_of_max3_eq_mean (e := pairEx v w) (by
      rw [hsum w hw, hsumu]; simp only [nucM1] at hm; rw [hm]; ring) k
    rw [h1, hsum w hw, hsumu, heq k]; ring
  refine ⟨⟨hu, fun w hw => ?_⟩, fun w hw => ?_⟩
  · rcases (hlow w hw).lt_or_eq with h | h
    · exact Or.inl (hm1u ▸ h)
    · rw [heqw w hw h.symm]; exact Or.inr ⟨rfl, le_rfl⟩
  · rcases hw.2 u hu with h | ⟨h, -⟩
    · exact absurd (hlow w hw.1) (not_le.2 (hm1u ▸ h))
    · exact heqw w hw.1 (h.trans hm1u)

/-- **Exercise 22.F.5(a)-(b)**, second case. If an exactly feasible `u*` has `u*ₖ = 0`, the
excesses of the two coalitions containing `k` equal and below that of `I \ {k}`, it is the
unique nucleolus. -/
theorem nucleolus_of_corner {v : Game 3} {u : Fin 3 → ℝ} (hu : Feas3 v u) {k i j : Fin 3}
    (hcov : ∀ l, l = k ∨ l = i ∨ l = j) (hs : ∀ e : Fin 3 → ℝ, ∑ l, e l = e k + e i + e j)
    (huk : u k = 0) (hij : pairEx v u i = pairEx v u j) (hlt : pairEx v u i < pairEx v u k) :
    IsNucleolus v u ∧ ∀ w, IsNucleolus v w → w = u := by
  have hsum : ∀ w, Feas3 v w → ∑ l, pairEx v w l = ∑ l, pairEx v u l := by
    intro w hw
    simp only [pairEx_eq hw.2, pairEx_eq hu.2, Finset.sum_sub_distrib, hw.2, hu.2]
  have hm1u : nucM1 v u = pairEx v u k := by
    obtain ⟨l, hl⟩ := max3_attained (pairEx v u)
    simp only [nucM1, hl]
    rcases hcov l with rfl | rfl | rfl
    · rfl
    · exact absurd (hl ▸ le_max3 (pairEx v u) k) (not_le.2 hlt)
    · exact absurd (hl ▸ le_max3 (pairEx v u) k) (not_le.2 (hij ▸ hlt))
  have hmin : min3 (pairEx v u) = pairEx v u i := by
    obtain ⟨l, hl⟩ := min3_attained (pairEx v u)
    have := min3_le (pairEx v u) i
    rcases hcov l with rfl | rfl | rfl <;> rw [hl] at this ⊢ <;> linarith
  have hm2u : nucM2 v u = pairEx v u i := by
    have hm1u' : max3 (pairEx v u) = pairEx v u k := hm1u
    simp only [nucM2, hs, hm1u', hmin]
    linarith
  -- the excess of `I \ {k}` cannot fall below `-cₖ`
  have hk : ∀ w, Feas3 v w → pairEx v u k ≤ pairEx v w k := by
    intro w hw
    rw [pairEx_eq hw.2, pairEx_eq hu.2, huk]; linarith [hw.1 k]
  have hlow : ∀ w, Feas3 v w → nucM1 v u ≤ nucM1 v w := fun w hw => by
    rw [hm1u]; exact (hk w hw).trans (le_max3 _ k)
  -- with equal first maxima, the second is at least that of `u`
  have hsecond : ∀ w, Feas3 v w → nucM1 v w = nucM1 v u →
      pairEx v w k = pairEx v u k ∧ pairEx v u i ≤ nucM2 v w ∧
        (nucM2 v w = pairEx v u i → w = u) := by
    intro w hw hm
    have hwk : pairEx v w k = pairEx v u k := by
      refine le_antisymm ?_ (hk w hw)
      have := le_max3 (pairEx v w) k
      simp only [nucM1] at hm hm1u
      linarith
    have hsw := hsum w hw
    rw [hs, hs, hwk, ← hij] at hsw
    have hm2 : nucM2 v w = pairEx v w i + pairEx v w j - min3 (pairEx v w) := by
      have hmw : max3 (pairEx v w) = pairEx v u k := by
        have h' : max3 (pairEx v w) = max3 (pairEx v u) := hm
        rw [h']; exact hm1u
      simp only [nucM2, hs, hmw]
      linarith
    have hmi := min3_le (pairEx v w) i
    have hmj := min3_le (pairEx v w) j
    refine ⟨hwk, by rw [hm2]; linarith, fun h2 => ?_⟩
    have hwi : pairEx v w i = pairEx v u i := by
      rw [hm2] at h2; linarith
    have hwj : pairEx v w j = pairEx v u j := by rw [← hij]; linarith
    refine eq_of_pairEx_eq hw hu fun l => ?_
    rcases hcov l with rfl | rfl | rfl
    · exact hwk
    · exact hwi
    · exact hwj
  refine ⟨⟨hu, fun w hw => ?_⟩, fun w hw => ?_⟩
  · rcases (hlow w hw).lt_or_eq with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, hm2u ▸ (hsecond w hw h.symm).2.1⟩
  · rcases hw.2 u hu with h | ⟨h, h2⟩
    · exact absurd (hlow w hw.1) (not_le.2 h)
    · have hh := hsecond w hw.1 h
      exact hh.2.2 (le_antisymm (hm2u ▸ h2) hh.2.1)

/-- The book's second maximum excess (MWG, p. 855): if `I \ {k}` attains the first maximum
and `i, j` are the other two agents, `m₂(u) = max {e(u, I \ {i}), e(u, I \ {j})}`, the largest
excess of the coalitions other than `I \ {k}`. -/
theorem m2_eq_book (v : Game 3) (u : Fin 3 → ℝ) {k i j : Fin 3}
    (hcov : ∀ l, l = k ∨ l = i ∨ l = j) (hs : ∀ e : Fin 3 → ℝ, ∑ l, e l = e k + e i + e j)
    (hk : pairEx v u k = nucM1 v u) :
    nucM2 v u = max (pairEx v u i) (pairEx v u j) := by
  have hk' : max3 (pairEx v u) = pairEx v u k := hk.symm
  have hi := le_max3 (pairEx v u) i
  have hj := le_max3 (pairEx v u) j
  have mi := min3_le (pairEx v u) i
  have mj := min3_le (pairEx v u) j
  obtain ⟨l, hl⟩ := min3_attained (pairEx v u)
  simp only [nucM2, hs, hk']
  rw [hk'] at hi hj
  rcases le_total (pairEx v u i) (pairEx v u j) with h | h
  · rw [max_eq_right h]
    rcases hcov l with rfl | rfl | rfl <;> rw [hl] at mi mj ⊢ <;> linarith
  · rw [max_eq_left h]
    rcases hcov l with rfl | rfl | rfl <;> rw [hl] at mi mj ⊢ <;> linarith

/-- `0 ≤ cₖ ≤ v(I)` under the standing assumptions. -/
theorem nucC_bounds {v : Game 3} (hv : NucGame v) (k : Fin 3) :
    0 ≤ nucC v k ∧ nucC v k ≤ v Finset.univ := by
  have := hv.2.2 k; unfold nucC; constructor <;> linarith

/-- The equal-excess candidate `c + t𝟙`, `t = (v(I) - ∑ cₖ)/3`. -/
noncomputable def nucEqual (v : Game 3) : Fin 3 → ℝ :=
  fun k => nucC v k + (v Finset.univ - ∑ l, nucC v l) / 3

/-- The corner candidate: `uₖ = 0` and the other two agents equalize their excesses. -/
noncomputable def nucCorner (v : Game 3) (k i j : Fin 3) : Fin 3 → ℝ := fun l =>
  if l = k then 0 else if l = i then (v Finset.univ + nucC v i - nucC v j) / 2
  else (v Finset.univ + nucC v j - nucC v i) / 2

theorem nucEqual_spec {v : Game 3} (hA : ∀ k, 0 ≤ nucEqual v k) :
    Feas3 v (nucEqual v) ∧ ∀ k, pairEx v (nucEqual v) k = pairEx v (nucEqual v) 0 := by
  have hs : ∑ k, nucEqual v k = v Finset.univ := by
    simp only [nucEqual, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    push_cast; ring
  refine ⟨⟨hA, hs⟩, fun k => ?_⟩
  rw [pairEx_eq hs, pairEx_eq hs]
  simp [nucEqual]

theorem nucCorner_spec {v : Game 3} (hv : NucGame v) {k i j : Fin 3} (hik : i ≠ k) (hjk : j ≠ k)
    (hij : i ≠ j) (hs : ∀ e : Fin 3 → ℝ, ∑ l, e l = e k + e i + e j)
    (hB : nucC v k + (v Finset.univ - ∑ l, nucC v l) / 3 < 0) :
    Feas3 v (nucCorner v k i j) ∧ nucCorner v k i j k = 0 ∧
      pairEx v (nucCorner v k i j) i = pairEx v (nucCorner v k i j) j ∧
      pairEx v (nucCorner v k i j) i < pairEx v (nucCorner v k i j) k := by
  have ek : nucCorner v k i j k = 0 := by simp [nucCorner]
  have ei : nucCorner v k i j i = (v Finset.univ + nucC v i - nucC v j) / 2 := by
    simp [nucCorner, hik]
  have ej : nucCorner v k i j j = (v Finset.univ + nucC v j - nucC v i) / 2 := by
    simp [nucCorner, hjk, Ne.symm hij]
  have bi := nucC_bounds hv i
  have bj := nucC_bounds hv j
  have bk := nucC_bounds hv k
  have hsum : ∑ l, nucCorner v k i j l = v Finset.univ := by rw [hs, ek, ei, ej]; ring
  refine ⟨⟨fun l => ?_, hsum⟩, ek, ?_, ?_⟩
  · simp only [nucCorner]
    split_ifs <;> linarith
  · rw [pairEx_eq hsum, pairEx_eq hsum, ei, ej]; ring
  · rw [pairEx_eq hsum, pairEx_eq hsum, ei, ek]
    rw [hs (nucC v)] at hB
    linarith

/-- Coverage data for the three choices of the distinguished agent. -/
theorem fin3_data (k : Fin 3) : ∃ i j : Fin 3, i ≠ k ∧ j ≠ k ∧ i ≠ j ∧
    (∀ l, l = k ∨ l = i ∨ l = j) ∧ ∀ e : Fin 3 → ℝ, ∑ l, e l = e k + e i + e j := by
  fin_cases k
  · exact ⟨1, 2, by decide, by decide, by decide, by decide, fun e => by rw [sum3]; rfl⟩
  · exact ⟨0, 2, by decide, by decide, by decide, by decide, fun e => by
      rw [sum3]; change e 0 + e 1 + e 2 = e 1 + e 0 + e 2; ring⟩
  · exact ⟨0, 1, by decide, by decide, by decide, by decide, fun e => by
      rw [sum3]; change e 0 + e 1 + e 2 = e 2 + e 0 + e 1; ring⟩

/-- **Exercise 22.F.5(b)** (MWG, p. 855). There is one and only one utility profile in the
nucleolus: `c + t𝟙` if it is nonnegative, otherwise the corner profile of the (unique) agent `k`
with `cₖ + t < 0`. -/
theorem exercise_22_F_5b {v : Game 3} (hv : NucGame v) :
    ∃ u, IsNucleolus v u ∧ ∀ w, IsNucleolus v w → w = u := by
  by_cases hA : ∀ k, 0 ≤ nucEqual v k
  · obtain ⟨hf, heq⟩ := nucEqual_spec hA
    exact ⟨_, nucleolus_of_equal hf heq⟩
  · push Not at hA
    obtain ⟨k, hk⟩ := hA
    obtain ⟨i, j, hik, hjk, hij, hcov, hs⟩ := fin3_data k
    obtain ⟨hf, h0, heq, hlt⟩ := nucCorner_spec hv hik hjk hij hs hk
    exact ⟨_, nucleolus_of_corner hf hcov hs h0 heq hlt⟩

/-- **Exercise 22.F.5(a)** (MWG, p. 855). At the nucleolus the three excesses of the two-agent
coalitions are identical, or two are identical and the third is larger. -/
theorem exercise_22_F_5a {v : Game 3} (hv : NucGame v) {u : Fin 3 → ℝ} (hu : IsNucleolus v u) :
    (∀ k, pairEx v u k = pairEx v u 0) ∨
      ∃ k i j : Fin 3, (∀ l, l = k ∨ l = i ∨ l = j) ∧ pairEx v u i = pairEx v u j ∧
        pairEx v u i < pairEx v u k := by
  by_cases hA : ∀ k, 0 ≤ nucEqual v k
  · obtain ⟨hf, heq⟩ := nucEqual_spec hA
    rw [(nucleolus_of_equal hf heq).2 u hu]
    exact Or.inl heq
  · push Not at hA
    obtain ⟨k, hk⟩ := hA
    obtain ⟨i, j, hik, hjk, hij, hcov, hs⟩ := fin3_data k
    obtain ⟨hf, h0, heq, hlt⟩ := nucCorner_spec hv hik hjk hij hs hk
    rw [(nucleolus_of_corner hf hcov hs h0 heq hlt).2 u hu]
    exact Or.inr ⟨k, i, j, hcov, heq, hlt⟩

theorem max3_comp (e : Fin 3 → ℝ) (σ : Equiv.Perm (Fin 3)) : max3 (e ∘ σ) = max3 e := by
  obtain ⟨a, ha⟩ := max3_attained (e ∘ σ)
  obtain ⟨b, hb⟩ := max3_attained e
  apply le_antisymm
  · rw [ha]; exact le_max3 e _
  · rw [hb, show b = σ (σ.symm b) by simp]; exact le_max3 (e ∘ σ) _

theorem min3_comp (e : Fin 3 → ℝ) (σ : Equiv.Perm (Fin 3)) : min3 (e ∘ σ) = min3 e := by
  obtain ⟨a, ha⟩ := min3_attained (e ∘ σ)
  obtain ⟨b, hb⟩ := min3_attained e
  apply le_antisymm
  · rw [hb, show b = σ (σ.symm b) by simp]; exact min3_le (e ∘ σ) _
  · rw [ha]; exact min3_le e _

/-- **Exercise 22.F.5(c)** (MWG, p. 855). The nucleolus solution is symmetric: if the game is
invariant under exchanging agents `i` and `j` (Definition 22.F.4), they get the same utility. -/
theorem exercise_22_F_5c {v : Game 3} (hv : NucGame v) {i j : Fin 3}
    (hsym : ∀ S, v (S.map (Equiv.swap i j).toEmbedding) = v S) {u : Fin 3 → ℝ}
    (hu : IsNucleolus v u) : u i = u j := by
  obtain ⟨u₀, -, huniq⟩ := exercise_22_F_5b hv
  set σ := Equiv.swap i j
  have hc : ∀ l, nucC v (σ l) = nucC v l := by
    intro l
    simp only [nucC]
    have e : (Finset.univ.erase l).map σ.toEmbedding = Finset.univ.erase (σ l) := by
      rw [Finset.map_erase, Finset.map_univ_equiv]; rfl
    rw [← e, hsym]
  set u' := u ∘ σ
  have hf' : Feas3 v u' := ⟨fun l => hu.1.1 _, by
    rw [← hu.1.2]; exact Equiv.sum_comp σ u⟩
  have hex : pairEx v u' = pairEx v u ∘ σ := by
    funext l
    simp only [Function.comp, pairEx_eq hf'.2, pairEx_eq hu.1.2, u', hc]
  have hm1 : nucM1 v u' = nucM1 v u := by simp only [nucM1, hex, max3_comp]
  have hm2 : nucM2 v u' = nucM2 v u := by
    simp only [nucM2, hex, max3_comp, min3_comp, Function.comp]
    rw [Equiv.sum_comp σ (pairEx v u)]
  have hu' : IsNucleolus v u' := ⟨hf', fun w hw => by rw [hm1, hm2]; exact hu.2 w hw⟩
  have h1 := huniq u hu
  have h2 := huniq u' hu'
  have := congrFun (h2.trans h1.symm) i
  simpa [u', σ] using this.symm

/-- **Exercise 22.F.5(d)** (MWG, p. 856). If agent `1` (index `0`) is a dummy
(`v(S ∪ {1}) = v(S)`), then `u₁ = 0` at the nucleolus solution. -/
theorem exercise_22_F_5d {v : Game 3} (hv : NucGame v) (hd : ∀ S, v (insert 0 S) = v S)
    {u : Fin 3 → ℝ} (hu : IsNucleolus v u) : u 0 = 0 := by
  have hV : v Finset.univ = v {1, 2} := by
    rw [show (Finset.univ : Finset (Fin 3)) = insert 0 {1, 2} by decide, hd]
  have c0 : nucC v 0 = 0 := by
    simp only [nucC, hV, show Finset.univ.erase (0 : Fin 3) = {1, 2} by decide, sub_self]
  have c1 : nucC v 1 = v Finset.univ := by
    simp only [nucC, show Finset.univ.erase (1 : Fin 3) = insert 0 {2} by decide, hd,
      hv.2.1 2, sub_zero]
  have c2 : nucC v 2 = v Finset.univ := by
    simp only [nucC, show Finset.univ.erase (2 : Fin 3) = insert 0 {1} by decide, hd,
      hv.2.1 1, sub_zero]
  have hVnn : 0 ≤ v Finset.univ := by have := nucC_bounds hv 0; linarith
  obtain ⟨u₀, -, huniq⟩ := exercise_22_F_5b hv
  rcases hVnn.lt_or_eq with hpos | hzero
  · -- the corner profile at agent `0`
    have hB : nucC v 0 + (v Finset.univ - ∑ l, nucC v l) / 3 < 0 := by
      rw [sum3, c0, c1, c2]; linarith
    obtain ⟨hf, h0, heq, hlt⟩ := nucCorner_spec hv (k := 0) (i := 1) (j := 2) (by decide)
      (by decide) (by decide) (fun e => by rw [sum3]) hB
    rw [(nucleolus_of_corner hf (by decide) (fun e => by rw [sum3]) h0 heq hlt).2 u hu]
    exact h0
  · -- `v(I) = 0`: everything is zero
    have hA : ∀ k, 0 ≤ nucEqual v k := fun k => by
      fin_cases k <;> simp [nucEqual, sum3, c0, c1, c2, ← hzero]
    obtain ⟨hf, heq⟩ := nucEqual_spec hA
    rw [(nucleolus_of_equal hf heq).2 u hu]
    simp [nucEqual, sum3, c0, c1, c2, ← hzero]

/-- **Exercise 22.F.5(e)** (MWG, p. 856). If `v(I)/2 ≤ v(S)` for every two-agent coalition, the
three excesses are identical at the nucleolus. -/
theorem exercise_22_F_5e {v : Game 3} (hv : NucGame v)
    (hhalf : ∀ k, v Finset.univ / 2 ≤ v (Finset.univ.erase k)) {u : Fin 3 → ℝ}
    (hu : IsNucleolus v u) : ∀ k, pairEx v u k = pairEx v u 0 := by
  have hc : ∀ k, nucC v k ≤ v Finset.univ / 2 := fun k => by
    have := hhalf k; unfold nucC; linarith
  have hA : ∀ k, 0 ≤ nucEqual v k := by
    intro k
    obtain ⟨i, j, -, -, -, -, hs⟩ := fin3_data k
    simp only [nucEqual, hs]
    have := nucC_bounds hv k
    linarith [hc i, hc j]
  obtain ⟨hf, heq⟩ := nucEqual_spec hA
  rw [(nucleolus_of_equal hf heq).2 u hu]
  exact heq

/-- The game of Exercise 22.F.5(f): `v(i) = 0`, `v({1,2}) = v({1,3}) = 4`, `v({2,3}) = 5`,
`v(I) = 6` (agents `0, 1, 2`). -/
noncomputable def game5f : Game 3 := fun S =>
  if S.card ≤ 1 then 0 else if S.card = 3 then 6 else if 0 ∈ S then 4 else 5

theorem nucGame_game5f : NucGame game5f := by
  refine ⟨by simp +decide [game5f], fun i => by fin_cases i <;> simp +decide [game5f],
    fun k => ?_⟩
  fin_cases k <;> simp +decide [game5f] <;> norm_num

/-- **Exercise 22.F.5(f)** (MWG, p. 856). For `v(1,2) = v(1,3) = 4`, `v(2,3) = 5`, `v(I) = 6` the
Shapley value is `(5/3, 13/6, 13/6)` and the nucleolus is `(4/3, 7/3, 7/3)`. -/
theorem exercise_22_F_5f :
    (shapley game5f 0 = 5 / 3 ∧ shapley game5f 1 = 13 / 6 ∧ shapley game5f 2 = 13 / 6) ∧
      IsNucleolus game5f ![4 / 3, 7 / 3, 7 / 3] := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [shapley3_expand]; simp +decide only [margContrib, game5f]; norm_num
  · rw [shapley3_expand]; simp +decide only [margContrib, game5f]; norm_num
  · rw [shapley3_expand]; simp +decide only [margContrib, game5f]; norm_num
  · have hs : ∑ k, (![4 / 3, 7 / 3, 7 / 3] : Fin 3 → ℝ) k = game5f Finset.univ := by
      rw [sum3]; simp +decide [game5f]; norm_num
    have hf : Feas3 game5f ![4 / 3, 7 / 3, 7 / 3] :=
      ⟨fun k => by fin_cases k <;> norm_num, hs⟩
    refine (nucleolus_of_equal hf fun k => ?_).1
    rw [pairEx_eq hs, pairEx_eq hs]
    fin_cases k <;> simp +decide [nucC, game5f] <;> norm_num

/-- The core of the three-agent game (MWG, Appendix A of Chapter 18): exactly feasible profiles
that no coalition can improve upon. -/
def IsCore3 (v : Game 3) (u : Fin 3 → ℝ) : Prop :=
  Feas3 v u ∧ ∀ S : Finset (Fin 3), v S ≤ ∑ i ∈ S, u i

theorem finset_fin3 (S : Finset (Fin 3)) : S = ∅ ∨ S = {0} ∨ S = {1} ∨ S = {2} ∨
    S = Finset.univ.erase 2 ∨ S = Finset.univ.erase 1 ∨ S = Finset.univ.erase 0 ∨
    S = Finset.univ := by
  revert S; decide

/-- **Exercise 22.F.5(g)** (MWG, p. 856). If the core is nonempty, the nucleolus profile belongs
to the core: its largest excess is at most that of a core profile, which is `≤ 0`. -/
theorem exercise_22_F_5g {v : Game 3} (hv : NucGame v) (hcore : ∃ w, IsCore3 v w)
    {u : Fin 3 → ℝ} (hu : IsNucleolus v u) : IsCore3 v u := by
  obtain ⟨w, hw⟩ := hcore
  have hwex : ∀ k, pairEx v w k ≤ 0 := fun k => by
    have := hw.2 (Finset.univ.erase k); unfold pairEx; linarith
  have hm1w : nucM1 v w ≤ 0 := by
    obtain ⟨l, hl⟩ := max3_attained (pairEx v w)
    simp only [nucM1, hl]; exact hwex l
  have hm1u : nucM1 v u ≤ nucM1 v w := by
    rcases hu.2 w hw.1 with h | ⟨h, -⟩
    · exact h.le
    · exact h.le
  have hpair : ∀ k, v (Finset.univ.erase k) ≤ ∑ i ∈ Finset.univ.erase k, u i := fun k => by
    have := le_max3 (pairEx v u) k
    have : pairEx v u k ≤ 0 := by simp only [nucM1] at hm1u hm1w; linarith
    unfold pairEx at this; linarith
  refine ⟨hu.1, fun S => ?_⟩
  rcases finset_fin3 S with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp [hv.1]
  · simp [hv.2.1 0, hu.1.1 0]
  · simp [hv.2.1 1, hu.1.1 1]
  · simp [hv.2.1 2, hu.1.1 2]
  · exact hpair 2
  · exact hpair 1
  · exact hpair 0
  · rw [hu.1.2]

end MWG.WelfareBargaining
