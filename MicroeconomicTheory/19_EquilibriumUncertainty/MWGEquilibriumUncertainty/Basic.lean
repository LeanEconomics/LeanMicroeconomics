/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGWelfareTheorems.Basic
import MWGChoiceUnderUncertainty.StateDependent

/-!
# A market economy with contingent commodities (MWG Section 19.B, pp. 688-691)

States of the world are `Fin S`, physical commodities `Fin L`. A contingent commodity vector
`x ∈ ℝ^{LS}` (**Definition 19.B.1**) is `x : Fin S → Fin L → ℝ`, `x s l = x_{ls}`; the
state-`s` bundle `x s ∈ ℝ^L` is what is delivered if `s` occurs, and the value of `x` at
contingent prices `p` is `p·x = ∑_s p_s·x_s` (`cval`). The book's ordering
`(x₁₁, …, x_{L1}, …, x_{1S}, …, x_{LS})` is the state-major ordering used by `flat` in
`ArrowDebreu`.

* **Definition 19.B.1**: `contingentUnit`, the decomposition of a contingent vector into units,
  and the random-variable view of a contingent vector (`randomVar`).
* **Example 19.B.1**: expected-utility preferences over contingent vectors are rational; for
  `L = 1` they are Chapter 6's extended expected utility (Definition 6.E.2, footnote 2).
* **Example 19.B.2**: the seeds-and-crops technology; `(-1, 1, -1, 0)` is feasible and
  `(-1, 1, 0, 0)` is not.
* **Footnote 3**: commodities consumed before the resolution of uncertainty.
* **Shares (p. 689)**: the printed normalization `∑ⱼ θⱼᵢ = 1` for every consumer `i` is a
  misprint for `∑ᵢ θⱼᵢ = 1` for every firm `j` (correction 1, `shares_printed_normalization_fails`).
* **Small type, pp. 690-691**: information structures (partitions), increasingly fine families,
  **Example 19.B.3**, unique predecessors of date-events, and measurability with respect to a
  family of information partitions.
-/

namespace MWG.EquilibriumUncertainty

open MWG.ClassicalDemand

/-- **Definition 19.B.1** (MWG, p. 688). A contingent commodity vector `x ∈ ℝ^{LS}`:
`x s l = x_{ls}` is the amount of physical good `l` received if state `s` occurs. -/
abbrev CVec (S L : ℕ) := Fin S → Fin L → ℝ

variable {S L : ℕ}

/-- The value `p·x = ∑_s ∑_l p_{ls} x_{ls}` of a contingent commodity vector. -/
def cval (p x : CVec S L) : ℝ := ∑ s, p s ⬝ᵥ x s

/-- **Definition 19.B.1** (MWG, p. 688). One unit of the contingent commodity `ls`: a title to
one unit of good `l` if and only if state `s` occurs. -/
def contingentUnit (l : Fin L) (s : Fin S) : CVec S L :=
  fun s' l' => if s' = s ∧ l' = l then 1 else 0

/-- **Definition 19.B.1** (MWG, p. 688). A contingent commodity vector is the bundle of its
contingent commodities: `x = ∑_{l,s} x_{ls} · (unit ls)`. -/
theorem definition_19_B_1 (x : CVec S L) :
    x = ∑ s, ∑ l, x s l • contingentUnit l s := by
  funext s' l'
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, contingentUnit]
  rw [Finset.sum_eq_single s']
  · rw [Finset.sum_eq_single l']
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  · intro b _ hb
    refine Finset.sum_eq_zero fun l _ => ?_
    simp [Ne.symm hb]
  · simp

/-- **p. 688**. The `l`-th random variable `(x_{l1}, …, x_{lS})` of a contingent vector. -/
def randomVar (x : CVec S L) (l : Fin L) : Fin S → ℝ := fun s => x s l

/-- **p. 688**. A contingent vector is the collection of its `L` random variables. -/
theorem randomVar_ext {x x' : CVec S L} (h : ∀ l, randomVar x l = randomVar x' l) : x = x' :=
  funext fun s => funext fun l => congrFun (h l) s

/-- The nonnegative orthant `ℝ^{LS}_+`. -/
def NonnegC (x : CVec S L) : Prop := ∀ s l, 0 ≤ x s l

/-- The expected utility `∑_s π_s u_s(x_s)` of a contingent vector (Example 19.B.1). -/
def expUtil (π : Fin S → ℝ) (u : Fin S → (Fin L → ℝ) → ℝ) (x : CVec S L) : ℝ :=
  ∑ s, π s * u s (x s)

/-- **Example 19.B.1** (MWG, p. 689). The ex ante preference `x ≿ x'` iff
`∑_s π_s u_s(x_s) ≥ ∑_s π_s u_s(x'_s)`. -/
def euPref (π : Fin S → ℝ) (u : Fin S → (Fin L → ℝ) → ℝ) (x x' : CVec S L) : Prop :=
  expUtil π u x' ≤ expUtil π u x

/-- **Example 19.B.1** (MWG, p. 689). Expected-utility preferences over contingent commodity
vectors are complete and transitive (a rational preference relation). -/
theorem example_19_B_1 (π : Fin S → ℝ) (u : Fin S → (Fin L → ℝ) → ℝ) :
    (∀ x x', euPref π u x x' ∨ euPref π u x' x) ∧
      ∀ x x' x'', euPref π u x x' → euPref π u x' x'' → euPref π u x x'' :=
  ⟨fun _ _ => le_total _ _, fun _ _ _ h1 h2 => le_trans h2 h1⟩

/-- **Footnote 2** (MWG, p. 689). For `L = 1` the preference of Example 19.B.1 is Chapter 6's
extended expected utility representation (Definition 6.E.2) on `ℝ^S_+`. -/
theorem footnote_19_2 (π : Fin S → ℝ) (u : Fin S → (Fin 1 → ℝ) → ℝ) :
    MWG.ChoiceUnderUncertainty.HasExtendedEU π
      (fun a b => euPref π u (fun s _ => a s) (fun s _ => b s)) :=
  ⟨fun s t => u s (fun _ => t), fun _ _ _ _ => Iff.rfl⟩

/-! ## Example 19.B.2: seeds and crops -/

/-- **Example 19.B.2** (MWG, p. 689). With states `s₁` (good weather, index `0`) and `s₂`
(bad, index `1`) and goods seeds (index `0`) and crops (index `1`), the plans of the
technology plant `a ≥ 0` seeds in both states and harvest `a` crops in the good state only. -/
def seedsTech : Set (CVec 2 2) :=
  {y | ∃ a : ℝ, 0 ≤ a ∧ y = fun s l => if l = 0 then -a else if s = 0 then a else 0}

/-- The plan `(y₁₁, y₂₁, y₁₂, y₂₂)` as a contingent vector. -/
def plan2 (a b c d : ℝ) : CVec 2 2 := fun s l => if s = 0 then (if l = 0 then a else b)
  else (if l = 0 then c else d)

/-- **Example 19.B.2** (MWG, p. 689). `(-1, 1, -1, 0)` is a feasible plan, while
`(-1, 1, 0, 0)` is not: seeds are planted before the weather is known. -/
theorem example_19_B_2 : plan2 (-1) 1 (-1) 0 ∈ seedsTech ∧ plan2 (-1) 1 0 0 ∉ seedsTech := by
  refine ⟨⟨1, zero_le_one, ?_⟩, ?_⟩
  · funext s l
    fin_cases s <;> fin_cases l <;> simp [plan2]
  · rintro ⟨a, _, h⟩
    have h1 := congrFun (congrFun h 0) 0
    have h2 := congrFun (congrFun h 1) 0
    simp [plan2] at h1 h2
    linarith

/-- **Footnote 3** (MWG, p. 689). Good `l` is consumed before the resolution of uncertainty
when every `x ∈ X` has equal entries `x_{ls}` across states. -/
def ConsumedExAnte (X : Set (CVec S L)) (l : Fin L) : Prop :=
  ∀ x ∈ X, ∀ s s', x s l = x s' l

/-! ## Ownership shares -/

/-- **p. 689**, corrected. Shares `θ j i ≥ 0` of firm `j` owned by consumer `i`: every firm is
fully owned, `∑ᵢ θⱼᵢ = 1` for every `j`. -/
def SharesValid {ι κ : Type*} [Fintype ι] (θ : κ → ι → ℝ) : Prop :=
  (∀ j i, 0 ≤ θ j i) ∧ ∀ j, ∑ i, θ j i = 1

/-- **p. 689** (correction 1). The printed normalization `∑ⱼ θⱼᵢ = 1` for every `i` fails for
valid shares: one firm owned half-and-half by two consumers. -/
theorem shares_printed_normalization_fails :
    SharesValid (fun (_ : Fin 1) (_ : Fin 2) => (1 / 2 : ℝ)) ∧
      ∃ i : Fin 2, ∑ j : Fin 1, (fun (_ : Fin 1) (_ : Fin 2) => (1 / 2 : ℝ)) j i ≠ 1 := by
  refine ⟨⟨fun _ _ => by norm_num, fun _ => by simp⟩, 0, by simp⟩

/-! ## Information structures (small type, pp. 690-691) -/

/-- **p. 690**. An information structure: a partition of the states into events (every state is
in some event, and distinct events are disjoint). -/
def IsInfoStructure {Ω : Type*} [DecidableEq Ω] (P : Finset (Finset Ω)) : Prop :=
  (∀ s, ∃ E ∈ P, s ∈ E) ∧ ∀ E ∈ P, ∀ E' ∈ P, E ≠ E' → Disjoint E E'

/-- **p. 690**. `P'` is at least as fine as `P`: every nonempty event of `P'` lies in an event
of `P` (information is not forgotten). -/
def Refines {Ω : Type*} (P' P : Finset (Finset Ω)) : Prop :=
  ∀ E' ∈ P', E'.Nonempty → ∃ E ∈ P, E' ⊆ E

/-- **p. 690**. A family of information structures `(𝒮₀, …, 𝒮_T)` that becomes increasingly
fine. -/
def IsInfoFamily {Ω : Type*} [DecidableEq Ω] {T : ℕ} (F : Fin (T + 1) → Finset (Finset Ω)) :
    Prop :=
  (∀ t, IsInfoStructure (F t)) ∧ ∀ t : Fin T, Refines (F t.succ) (F t.castSucc)

/-- **Example 19.B.3** (MWG, p. 691), states `1, …, 6` as `0, …, 5`: the partitions of the tree
of Figure 19.B.2. -/
def example19B3 : Fin 3 → Finset (Finset (Fin 6)) :=
  ![{Finset.univ}, {{0, 1}, {2}, {3, 4, 5}}, {{0}, {1}, {2}, {3}, {4}, {5}}]

set_option maxRecDepth 100000 in
/-- **Example 19.B.3** (MWG, p. 691). The three partitions form an increasingly fine family of
information structures. -/
theorem example_19_B_3 : IsInfoFamily (T := 2) example19B3 := by
  refine ⟨fun t => ?_, fun t => ?_⟩
  · unfold IsInfoStructure
    fin_cases t <;> decide
  · unfold Refines
    fin_cases t <;> decide

/-- **p. 691**. Each date-event other than the first has a unique predecessor: a nonempty
event of a finer information structure lies in exactly one event of the coarser one. -/
theorem unique_predecessor {Ω : Type*} [DecidableEq Ω] {P P' : Finset (Finset Ω)}
    (hP : IsInfoStructure P) (href : Refines P' P) {E' : Finset Ω} (hE' : E' ∈ P')
    (hne : E'.Nonempty) : ∃! E, E ∈ P ∧ E' ⊆ E := by
  obtain ⟨E, hE, hsub⟩ := href E' hE' hne
  refine ⟨E, ⟨hE, hsub⟩, fun E2 ⟨hE2, hsub2⟩ => ?_⟩
  by_contra hne2
  obtain ⟨s, hs⟩ := hne
  exact Finset.disjoint_left.mp (hP.2 E2 hE2 E hE hne2) (hsub2 hs) (hsub hs)

/-- **p. 691**. A double-indexed vector `z_{(ht)s}` (`H` basic goods, dates `0, …, T`) is
measurable with respect to the family `(𝒮₀, …, 𝒮_T)`: amounts at date `t` agree across states
that cannot be distinguished at `t`. -/
def IsMeasurable {Ω : Type*} {H T : ℕ} (F : Fin (T + 1) → Finset (Finset Ω))
    (z : Fin H → Fin (T + 1) → Ω → ℝ) : Prop :=
  ∀ h t s s', (∃ E ∈ F t, s ∈ E ∧ s' ∈ E) → z h t s = z h t s'

/-- **p. 691**. In the tree of Example 19.B.3, a measurable vector cannot assign different
date-0 amounts to two states, nor different date-1 amounts to states 1 and 2. -/
theorem example_19_B_3_measurable {H : ℕ} {z : Fin H → Fin 3 → Fin 6 → ℝ}
    (hz : IsMeasurable (T := 2) example19B3 z) (h : Fin H) :
    (∀ s s', z h 0 s = z h 0 s') ∧ z h 1 0 = z h 1 1 :=
  ⟨fun s s' => hz h 0 s s' ⟨Finset.univ, by simp [example19B3]⟩,
    hz h 1 0 1 ⟨{0, 1}, by simp [example19B3], by simp⟩⟩

/-! ## Monotonicity on contingent vectors -/

/-- Strong monotonicity of a utility on `ℝ^{LS}_+`: `x ≤ x'`, `x ≠ x'` imply `U(x) < U(x')`. -/
def StronglyMonotoneC (U : CVec S L → ℝ) : Prop :=
  ∀ x x', NonnegC x → x ≤ x' → x ≠ x' → U x < U x'

/-- Strong monotonicity on `ℝ^L_+`. -/
def StronglyMonotoneL (u : (Fin L → ℝ) → ℝ) : Prop :=
  ∀ a b : Fin L → ℝ, (∀ l, 0 ≤ a l) → a ≤ b → a ≠ b → u a < u b

/-- **p. 703**. Expected utility with strictly positive probabilities and strongly monotone
Bernoulli utilities is strongly monotone (the example of strongly monotone preferences given
after Lemma 19.E.1). -/
theorem expUtil_stronglyMonotone {π : Fin S → ℝ} (hπ : ∀ s, 0 < π s)
    {u : Fin S → (Fin L → ℝ) → ℝ} (hu : ∀ s, StronglyMonotoneL (u s)) :
    StronglyMonotoneC (expUtil π u) := by
  intro x x' hx hle hne
  have hle' : ∀ s, u s (x s) ≤ u s (x' s) := by
    intro s
    by_cases h : x s = x' s
    · rw [h]
    · exact (hu s (x s) (x' s) (hx s) (hle s) h).le
  obtain ⟨s0, hs0⟩ : ∃ s, x s ≠ x' s := by
    by_contra hall
    push Not at hall
    exact hne (funext hall)
  unfold expUtil
  exact Finset.sum_lt_sum (fun s _ => mul_le_mul_of_nonneg_left (hle' s) (hπ s).le)
    ⟨s0, Finset.mem_univ _, mul_lt_mul_of_pos_left (hu s0 _ _ (hx s0) (hle s0) hs0) (hπ s0)⟩

end MWG.EquilibriumUncertainty
