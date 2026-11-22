/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGWelfareBargaining.NashSolution

/-!
# The egalitarian, utilitarian and Kalai-Smorodinsky solutions

MWG, Examples 22.E.1, 22.E.2 and 22.E.4 (pp. 841-844), footnote 29, and the computations on
half-space and box problems used in the examples and exercises of Section 22.E.

Both the egalitarian and the Kalai-Smorodinsky solutions move from the threat point along a
ray: `rayPoint P w = u* + c* w` with `c* = max {c ≥ 0 : u* + c w ∈ U}` (`rayLevel`). The
egalitarian solution uses `w = (1, …, 1)`; the Kalai-Smorodinsky solution uses
`w = u^∘(U) - u*`, the gap to the ideal point `u^i(U) = max {uᵢ : u ∈ U, u ≥ u*}`. The
utilitarian solution is a maximizer of `∑ (uᵢ - u*ᵢ)` over `{u ∈ U : u ≥ u*}`; since the
maximizer need not be unique (footnote 30), `utilSol` is a selection, made on the normalised
problem so that it is independent of utility origins.

Results: all three are individually rational and Paretian and independent of utility origins
(Exercise 22.E.1); the egalitarian and Kalai-Smorodinsky solutions are symmetric, and the
utilitarian solution is symmetric and satisfies IIA where the maximizer is unique (e.g. for
strictly convex `U`). The egalitarian solution satisfies IIA, maximizes the Rawlsian function
`min (uᵢ - u*ᵢ)` and is monotone; the Kalai-Smorodinsky solution satisfies IUU.
-/

namespace MWG.WelfareBargaining

open Set

variable {ι : Type*} [Fintype ι]

namespace BargainingProblem

/-- The admissible levels along the ray `u* + c w`. -/
def raySet (P : BargainingProblem ι) (w : ι → ℝ) : Set ℝ :=
  {c | 0 ≤ c ∧ (fun i => P.d i + c * w i) ∈ P.U}

/-- The largest admissible level along the ray `u* + c w`. -/
noncomputable def rayLevel (P : BargainingProblem ι) (w : ι → ℝ) : ℝ := sSup (P.raySet w)

/-- The point `u* + c* w`. -/
noncomputable def rayPoint (P : BargainingProblem ι) (w : ι → ℝ) : ι → ℝ :=
  fun i => P.d i + P.rayLevel w * w i

variable (P : BargainingProblem ι) {w : ι → ℝ}

omit [Fintype ι] in
theorem zero_mem_raySet : (0 : ℝ) ∈ P.raySet w := ⟨le_rfl, by simpa using P.d_mem⟩

omit [Fintype ι] in
theorem raySet_bddAbove [Nonempty ι] (hw : ∀ i, 0 < w i) : BddAbove (P.raySet w) := by
  obtain ⟨B, hB⟩ := P.bdd
  obtain ⟨i⟩ := ‹Nonempty ι›
  refine ⟨(B - P.d i) / w i, fun c hc => ?_⟩
  have := hB _ hc.2 (fun j => by
    have : 0 ≤ c * w j := mul_nonneg hc.1 (hw j).le
    simp only; linarith) i
  rw [le_div_iff₀ (hw i)]
  linarith

omit [Fintype ι] in
theorem raySet_closed : IsClosed (P.raySet w) :=
  (isClosed_le continuous_const continuous_id).inter (P.closed.preimage (continuous_pi
    fun _ => continuous_const.add (continuous_id.mul continuous_const)))

omit [Fintype ι] in
theorem rayLevel_mem [Nonempty ι] (hw : ∀ i, 0 < w i) : P.rayLevel w ∈ P.raySet w :=
  P.raySet_closed.csSup_mem ⟨0, P.zero_mem_raySet⟩ (P.raySet_bddAbove hw)

omit [Fintype ι] in
theorem le_rayLevel [Nonempty ι] (hw : ∀ i, 0 < w i) {c : ℝ} (hc : c ∈ P.raySet w) :
    c ≤ P.rayLevel w :=
  le_csSup (P.raySet_bddAbove hw) hc

omit [Fintype ι] in
theorem rayLevel_eq [Nonempty ι] (hw : ∀ i, 0 < w i) {c : ℝ} (hc : c ∈ P.raySet w)
    (hmax : ∀ c' ∈ P.raySet w, c' ≤ c) : P.rayLevel w = c :=
  le_antisymm (csSup_le ⟨0, P.zero_mem_raySet⟩ hmax) (P.le_rayLevel hw hc)

omit [Fintype ι] in
theorem rayLevel_pos [Finite ι] [Nonempty ι] (hw : ∀ i, 0 < w i) : 0 < P.rayLevel w := by
  cases nonempty_fintype ι
  obtain ⟨ε, hε, hp⟩ := P.exists_gt
  have hW : 0 < ∑ i, w i := Finset.sum_pos (fun i _ => hw i) Finset.univ_nonempty
  have hc : ε / (∑ i, w i) ∈ P.raySet w := by
    refine ⟨(div_pos hε hW).le, P.comprehensive _ hp _ fun i => ?_⟩
    have h1 : w i ≤ ∑ j, w j :=
      Finset.single_le_sum (f := w) (fun j _ => (hw j).le) (Finset.mem_univ i)
    have h2 : ε / (∑ j, w j) * w i ≤ ε := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hW]; nlinarith
    simp only; linarith
  exact lt_of_lt_of_le (div_pos hε hW) (P.le_rayLevel hw hc)

omit [Fintype ι] in
theorem rayPoint_mem [Nonempty ι] (hw : ∀ i, 0 < w i) : P.rayPoint w ∈ P.U :=
  (P.rayLevel_mem hw).2

omit [Fintype ι] in
theorem rayPoint_ge [Finite ι] [Nonempty ι] (hw : ∀ i, 0 < w i) (i : ι) :
    P.d i ≤ P.rayPoint w i := by
  cases nonempty_fintype ι
  have := mul_nonneg (P.rayLevel_pos hw).le (hw i).le
  simp only [rayPoint]; linarith

omit [Fintype ι] in
/-- The ray point is weakly Pareto optimal. -/
theorem rayPoint_pareto [Finite ι] [Nonempty ι] (hw : ∀ i, 0 < w i) :
    ¬∃ v ∈ P.U, ∀ i, P.rayPoint w i < v i := by
  cases nonempty_fintype ι
  rintro ⟨v, hv, hlt⟩
  set δ := Finset.univ.inf' Finset.univ_nonempty fun i => (v i - P.rayPoint w i) / w i
  have hδ : 0 < δ := by
    obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
      fun i => (v i - P.rayPoint w i) / w i
    rw [show δ = _ from hj]; exact div_pos (sub_pos.2 (hlt j)) (hw j)
  have hc : P.rayLevel w + δ ∈ P.raySet w := by
    refine ⟨by linarith [P.rayLevel_pos hw], P.comprehensive _ hv _ fun i => ?_⟩
    have hδi : δ ≤ (v i - P.rayPoint w i) / w i := Finset.inf'_le _ (Finset.mem_univ i)
    rw [le_div_iff₀ (hw i)] at hδi
    simp only [rayPoint] at hδi ⊢
    nlinarith
  linarith [P.le_rayLevel hw hc]

theorem raySet_translate (a : ι → ℝ) : (P.translate a).raySet w = P.raySet w := by
  ext c
  simp only [raySet, mem_ofPred_eq, translate_U, translate_d]
  have : (fun i => (P.d + a) i + c * w i) - a = fun i => P.d i + c * w i := by
    funext i; simp only [Pi.sub_apply, Pi.add_apply]; ring
  rw [this]

theorem raySet_scale (β : ι → ℝ) (hβ : ∀ i, 0 < β i) :
    (P.scale β hβ).raySet (fun i => β i * w i) = P.raySet w := by
  ext c
  simp only [raySet, mem_ofPred_eq, scale_U, scale_d]
  have : (fun i => (β i * P.d i + c * (β i * w i)) / β i) = fun i => P.d i + c * w i := by
    funext i; field_simp [(hβ i).ne']
  rw [this]

omit [Fintype ι] in
theorem raySet_mono {P' : BargainingProblem ι} (hsub : P'.U ⊆ P.U) (hd : P'.d = P.d) :
    P'.raySet w ⊆ P.raySet w := fun c hc => ⟨hc.1, by rw [← hd]; exact hsub hc.2⟩

/-- The ideal value `u^i(U) = max {uᵢ : u ∈ U, u ≥ u*}` (MWG, p. 844). -/
noncomputable def ideal (i : ι) : ℝ := sSup ((fun u : ι → ℝ => u i) '' {u ∈ P.U | P.d ≤ u})

omit [Fintype ι] in
theorem ideal_spec [Finite ι] (i : ι) :
    (∃ u ∈ P.U, P.d ≤ u ∧ u i = P.ideal i) ∧ ∀ u ∈ P.U, P.d ≤ u → u i ≤ P.ideal i := by
  cases nonempty_fintype ι
  have hK : IsCompact {u ∈ P.U | P.d ≤ u} := Metric.isCompact_of_isClosed_isBounded
    (P.closed.inter (isClosed_le continuous_const continuous_id)) P.isBounded
  have hI : IsCompact ((fun u : ι → ℝ => u i) '' {u ∈ P.U | P.d ≤ u}) :=
    hK.image (continuous_apply i)
  have hne : ((fun u : ι → ℝ => u i) '' {u ∈ P.U | P.d ≤ u}).Nonempty :=
    ⟨_, ⟨P.d, ⟨P.d_mem, le_rfl⟩, rfl⟩⟩
  obtain ⟨u, hu, hui⟩ := hI.sSup_mem hne
  exact ⟨⟨u, hu.1, hu.2, hui⟩, fun v hv hdv => le_csSup hI.bddAbove ⟨v, ⟨hv, hdv⟩, rfl⟩⟩

omit [Fintype ι] in
theorem ideal_eq [Finite ι] (i : ι) {m : ℝ} (hm : ∃ u ∈ P.U, P.d ≤ u ∧ u i = m)
    (hmax : ∀ u ∈ P.U, P.d ≤ u → u i ≤ m) : P.ideal i = m := by
  cases nonempty_fintype ι
  obtain ⟨u, hu, hdu, rfl⟩ := hm
  obtain ⟨⟨v, hv, hdv, hvi⟩, hall⟩ := P.ideal_spec i
  exact le_antisymm (hvi ▸ hmax v hv hdv) (hall u hu hdu)

/-- The gap `u^i(U) - u*ᵢ` to the ideal point; it is positive. -/
noncomputable def idealGap (i : ι) : ℝ := P.ideal i - P.d i

omit [Fintype ι] in
theorem idealGap_pos [Finite ι] [Nonempty ι] (i : ι) : 0 < P.idealGap i := by
  cases nonempty_fintype ι
  obtain ⟨ε, hε, hp⟩ := P.exists_gt
  have := (P.ideal_spec i).2 _ hp fun j => by simp only; linarith
  simp only [idealGap]; linarith

theorem ideal_translate (a : ι → ℝ) (i : ι) : (P.translate a).ideal i = P.ideal i + a i := by
  obtain ⟨⟨u, hu, hdu, hui⟩, hall⟩ := P.ideal_spec i
  apply ideal_eq
  · refine ⟨u + a, by simpa using hu, fun j => ?_, by simp [hui]⟩
    simp only [translate_d, Pi.add_apply]; linarith [hdu j]
  · intro v hv hdv
    have := hall _ hv fun j => by
      have := hdv j; simp only [translate_d, Pi.add_apply] at this; simp; linarith
    simp only [Pi.sub_apply] at this; linarith

theorem ideal_scale (β : ι → ℝ) (hβ : ∀ i, 0 < β i) (i : ι) :
    (P.scale β hβ).ideal i = β i * P.ideal i := by
  obtain ⟨⟨u, hu, hdu, hui⟩, hall⟩ := P.ideal_spec i
  apply ideal_eq
  · refine ⟨fun j => β j * u j, P.mem_scale β hβ hu, fun j => ?_, by simp [hui]⟩
    rw [scale_d]; exact mul_le_mul_of_nonneg_left (hdu j) (hβ j).le
  · intro v hv hdv
    have := hall _ hv fun j => by
      have := hdv j; rw [scale_d] at this
      rw [le_div_iff₀ (hβ j), mul_comm]; exact this
    rw [div_le_iff₀ (hβ i)] at this; linarith

end BargainingProblem

open BargainingProblem

/-! ### The egalitarian solution -/

/-- **Example 22.E.1** (MWG, p. 841). The egalitarian solution: the point of the frontier of
`U` with all gains from cooperation `uᵢ - u*ᵢ` equal. -/
noncomputable def egal (P : BargainingProblem ι) : ι → ℝ := P.rayPoint fun _ => 1

theorem egal_IUO [Nonempty ι] : IUO (egal (ι := ι)) := by
  intro P a
  funext i
  simp only [egal, rayPoint, rayLevel, raySet_translate, translate_d, Pi.add_apply]
  ring

omit [Fintype ι] in
theorem egal_IIA [Finite ι] [Nonempty ι] : IIA (egal (ι := ι)) := by
  cases nonempty_fintype ι
  intro P P' hsub hd hmem
  have h1 : P'.rayLevel (fun _ => 1) = P.rayLevel (fun _ => 1) := by
    apply le_antisymm
    · exact csSup_le_csSup (P.raySet_bddAbove fun _ => one_pos) ⟨0, P'.zero_mem_raySet⟩
        (raySet_mono P hsub hd)
    · refine P'.le_rayLevel (fun _ => one_pos) ⟨(P.rayLevel_pos fun _ => one_pos).le, ?_⟩
      rw [hd]; exact hmem
  funext i
  simp only [egal, rayPoint, h1, hd]

/-- **Example 22.E.1 and Exercise 22.E.1** (MWG, pp. 841, 853). The egalitarian solution is a
bargaining solution that is independent of utility origins, Paretian, symmetric, individually
rational and satisfies IIA. -/
theorem example_22_E_1 [Nonempty ι] :
    IsBargainingSolution (egal (ι := ι)) ∧ IUO (egal (ι := ι)) ∧ ParetoBS (egal (ι := ι)) ∧
      SymmetricBS (egal (ι := ι)) ∧ IndivRational (egal (ι := ι)) ∧ IIA (egal (ι := ι)) :=
  ⟨fun P => P.rayPoint_mem fun _ => one_pos, egal_IUO, fun P => P.rayPoint_pareto fun _ => one_pos,
    fun P _ hd i j => by simp only [egal, rayPoint, hd i j],
    fun P i => P.rayPoint_ge (fun _ => one_pos) i, egal_IIA⟩

/-- **Example 22.E.1** (MWG, p. 841). The egalitarian solution maximizes the Rawlsian social
welfare function `min (uᵢ - u*ᵢ)` on `U`. -/
theorem egal_maximin [Nonempty ι] (P : BargainingProblem ι) (u : ι → ℝ) (hu : u ∈ P.U) :
    Finset.univ.inf' Finset.univ_nonempty (fun i => u i - P.d i) ≤
      Finset.univ.inf' Finset.univ_nonempty (fun i => egal P i - P.d i) := by
  have he : ∀ i, egal P i - P.d i = P.rayLevel fun _ => 1 := fun i => by
    simp [egal, rayPoint]
  simp only [he, Finset.inf'_const]
  set m := Finset.univ.inf' Finset.univ_nonempty fun i => u i - P.d i
  rcases le_or_gt m 0 with hm | hm
  · exact hm.trans (P.rayLevel_pos fun _ => one_pos).le
  · refine P.le_rayLevel (fun _ => one_pos) ⟨hm.le, P.comprehensive _ hu _ fun i => ?_⟩
    have : m ≤ u i - P.d i := Finset.inf'_le _ (Finset.mem_univ i)
    simp only [mul_one]; linarith

omit [Fintype ι] in
/-- **Section 22.E, monotonicity** (MWG, p. 845). The egalitarian solution is monotone: if
`U ⊆ U'` (same threat point) then `f(U) ≤ f(U')`. -/
theorem egal_monotone [Nonempty ι] {P P' : BargainingProblem ι} (hsub : P.U ⊆ P'.U)
    (hd : P.d = P'.d) (i : ι) : egal P i ≤ egal P' i := by
  have : P.rayLevel (fun _ => 1) ≤ P'.rayLevel (fun _ => 1) :=
    csSup_le_csSup (P'.raySet_bddAbove fun _ => one_pos) ⟨0, P.zero_mem_raySet⟩
      (raySet_mono P' hsub hd)
  simp only [egal, rayPoint, hd]; linarith

/-! ### The Kalai-Smorodinsky solution -/

/-- **Example 22.E.4** (MWG, p. 844). The Kalai-Smorodinsky solution: the maximal point of `U`
on the segment from `u*` to the ideal point `(u^1(U), …, u^I(U))`. -/
noncomputable def ks (P : BargainingProblem ι) : ι → ℝ := P.rayPoint P.idealGap

theorem ks_IUO [Nonempty ι] : IUO (ks (ι := ι)) := by
  intro P a
  have hg : (P.translate a).idealGap = P.idealGap := by
    funext i; simp only [idealGap, ideal_translate, translate_d, Pi.add_apply]; ring
  funext i
  simp only [ks, rayPoint, rayLevel, hg, raySet_translate, translate_d, Pi.add_apply]
  ring

theorem ks_IUU [Nonempty ι] : IUU (ks (ι := ι)) := by
  intro P β hβ
  have hg : (P.scale β hβ).idealGap = fun i => β i * P.idealGap i := by
    funext i; simp only [idealGap, ideal_scale, scale_d]; ring
  funext i
  simp only [ks, rayPoint, rayLevel, hg, raySet_scale, scale_d]
  ring

omit [Fintype ι] in
theorem ks_symmetric [Finite ι] [Nonempty ι] : SymmetricBS (ks (ι := ι)) := by
  cases nonempty_fintype ι
  classical
  intro P hsym hd i j
  have hideal : P.ideal i = P.ideal j := by
    have key : ∀ a b : ι, P.ideal a ≤ P.ideal b := by
      intro a b
      obtain ⟨⟨u, hu, hdu, hua⟩, -⟩ := P.ideal_spec a
      have hmem := hsym (Equiv.swap a b) u hu
      have := (P.ideal_spec b).2 _ hmem fun k => by
        simp only [Function.comp]
        rw [hd k (Equiv.swap a b k)]; exact hdu _
      simpa [Function.comp, Equiv.swap_apply_right, hua] using this
    exact le_antisymm (key i j) (key j i)
  simp only [ks, rayPoint, idealGap, hideal, hd i j]

/-- **Example 22.E.4 and Exercises 22.E.1, 22.E.4** (MWG, pp. 844, 853). The Kalai-Smorodinsky
solution is a bargaining solution that is independent of utility origins and units, Paretian,
symmetric and individually rational. -/
theorem example_22_E_4 [Nonempty ι] :
    IsBargainingSolution (ks (ι := ι)) ∧ IUO (ks (ι := ι)) ∧ IUU (ks (ι := ι)) ∧
      ParetoBS (ks (ι := ι)) ∧ SymmetricBS (ks (ι := ι)) ∧ IndivRational (ks (ι := ι)) :=
  ⟨fun P => P.rayPoint_mem P.idealGap_pos, ks_IUO, ks_IUU,
    fun P => P.rayPoint_pareto P.idealGap_pos, ks_symmetric,
    fun P i => P.rayPoint_ge P.idealGap_pos i⟩

/-! ### The utilitarian solution -/

/-- `û` maximizes `∑ (uᵢ - u*ᵢ)` over `{u ∈ U : u ≥ u*}` (MWG, Example 22.E.2). -/
def IsUtilPoint (P : BargainingProblem ι) (û : ι → ℝ) : Prop :=
  û ∈ P.U ∧ P.d ≤ û ∧ ∀ u ∈ P.U, P.d ≤ u → ∑ i, (u i - P.d i) ≤ ∑ i, (û i - P.d i)

theorem exists_utilPoint (P : BargainingProblem ι) : ∃ û, IsUtilPoint P û := by
  have hK : IsCompact {u ∈ P.U | P.d ≤ u} := Metric.isCompact_of_isClosed_isBounded
    (P.closed.inter (isClosed_le continuous_const continuous_id)) P.isBounded
  obtain ⟨û, hû, hmax⟩ := hK.exists_isMaxOn ⟨P.d, P.d_mem, le_rfl⟩
    (f := fun u => ∑ i, (u i - P.d i))
    (continuous_finsetSum _ fun i _ => (continuous_apply i).sub continuous_const).continuousOn
  exact ⟨û, hû.1, hû.2, fun u hu hdu => hmax ⟨hu, hdu⟩⟩

theorem normalize_translate_eq (P : BargainingProblem ι) (a : ι → ℝ) :
    (P.translate a).normalize = P.normalize := by
  ext v
  · change v - -(P.d + a) - a ∈ P.U ↔ v - -P.d ∈ P.U
    rw [show v - -(P.d + a) - a = v - -P.d by abel]
  · simp [BargainingProblem.normalize]

/-- **Example 22.E.2** (MWG, p. 841). A utilitarian solution: a maximizer of `∑ uᵢ` on
`U ∩ ℝ^I₊` for the normalised problem, translated back. -/
noncomputable def utilSol (P : BargainingProblem ι) : ι → ℝ :=
  (exists_utilPoint P.normalize).choose + P.d

theorem isUtilPoint_translate {P : BargainingProblem ι} {û : ι → ℝ} (h : IsUtilPoint P û)
    (a : ι → ℝ) : IsUtilPoint (P.translate a) (û + a) := by
  refine ⟨by simpa using h.1, fun i => by simpa using h.2.1 i, fun u hu hdu => ?_⟩
  have := h.2.2 (u - a) hu fun i => by have := hdu i; simp at this ⊢; linarith
  simp only [translate_d, Pi.add_apply, Pi.sub_apply] at this ⊢
  convert this using 2 <;> ring

theorem utilSol_spec (P : BargainingProblem ι) : IsUtilPoint P (utilSol P) := by
  have h := isUtilPoint_translate (exists_utilPoint P.normalize).choose_spec P.d
  rwa [normalize_translate] at h

theorem utilSol_IUO : IUO (utilSol (ι := ι)) := by
  intro P a
  simp only [utilSol, normalize_translate_eq, translate_d]
  abel

/-- **Exercise 22.E.1** (MWG, p. 853). The utilitarian solution is a bargaining solution that is
independent of utility origins, Paretian and individually rational. -/
theorem example_22_E_2 [Nonempty ι] :
    IsBargainingSolution (utilSol (ι := ι)) ∧ IUO (utilSol (ι := ι)) ∧
      ParetoBS (utilSol (ι := ι)) ∧ IndivRational (utilSol (ι := ι)) := by
  refine ⟨fun P => (utilSol_spec P).1, utilSol_IUO, fun P ⟨v, hv, hlt⟩ => ?_,
    fun P => (utilSol_spec P).2.1⟩
  have h := utilSol_spec P
  have hdv : P.d ≤ v := fun i => (h.2.1 i).trans (hlt i).le
  have := h.2.2 v hv hdv
  have : ∑ i, (utilSol P i - P.d i) < ∑ i, (v i - P.d i) :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _ => by linarith [hlt i]
  linarith

/-- **Example 22.E.2** (MWG, p. 841). If `U` is strictly convex the utilitarian point is
unique. -/
theorem utilPoint_unique_of_strictConvex [Nonempty ι] {P : BargainingProblem ι}
    (hsc : StrictConvex ℝ P.U) {û û' : ι → ℝ} (h : IsUtilPoint P û) (h' : IsUtilPoint P û') :
    û = û' := by
  by_contra hne
  have hint := hsc h.1 h'.1 hne (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num)
  set m := (1 / 2 : ℝ) • û + (1 / 2 : ℝ) • û'
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hint)
  have hmε : (fun i => m i + ε / 2) ∈ P.U := hball (by
    rw [Metric.mem_ball, dist_pi_lt_iff hε]
    intro i; rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos (by positivity)]; linarith)
  have hmi : ∀ i, m i = (û i + û' i) / 2 := fun i => by
    simp only [m, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have heq := le_antisymm (h'.2.2 _ h.1 h.2.1) (h.2.2 _ h'.1 h'.2.1)
  have := h.2.2 _ hmε fun i => by rw [hmi]; linarith [h.2.1 i, h'.2.1 i]
  have hsum : ∑ i, (m i + ε / 2 - P.d i) = (∑ i, (û i - P.d i) + ∑ i, (û' i - P.d i)) / 2 +
      ∑ _i : ι, ε / 2 := by
    simp only [hmi, ← Finset.sum_add_distrib, Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hpos : 0 < ∑ _i : ι, ε / 2 := Finset.sum_pos (fun _ _ => by positivity)
    Finset.univ_nonempty
  linarith

/-- **Example 22.E.2** (MWG, p. 841). On problems with a unique utilitarian point (for instance
strictly convex ones), the utilitarian solution satisfies IIA. -/
theorem utilSol_IIA_of_unique {P P' : BargainingProblem ι} (hsub : P'.U ⊆ P.U)
    (hd : P'.d = P.d) (hmem : utilSol P ∈ P'.U)
    (huniq : ∀ û û', IsUtilPoint P' û → IsUtilPoint P' û' → û = û') :
    utilSol P' = utilSol P := by
  have h := utilSol_spec P
  refine huniq _ _ (utilSol_spec P') ⟨hmem, hd ▸ h.2.1, fun u hu hdu => ?_⟩
  rw [hd] at hdu ⊢
  exact h.2.2 u (hsub hu) hdu

/-- **Exercise 22.E.1** (MWG, p. 853), symmetry of the utilitarian solution where the
maximizer is unique. -/
theorem utilSol_symmetric_of_unique {P : BargainingProblem ι} (hsym : IsSymmetricSet P.U)
    (hd : ∀ i j, P.d i = P.d j)
    (huniq : ∀ û û', IsUtilPoint P û → IsUtilPoint P û' → û = û') (i j : ι) :
    utilSol P i = utilSol P j := by
  classical
  have h := utilSol_spec P
  have hσ : IsUtilPoint P (utilSol P ∘ Equiv.swap i j) := by
    refine ⟨hsym _ _ h.1, fun k => ?_, fun u hu hdu => ?_⟩
    · simp only [Function.comp]; rw [hd k (Equiv.swap i j k)]; exact h.2.1 _
    · have e : ∑ k, ((utilSol P ∘ Equiv.swap i j) k - P.d k) = ∑ k, (utilSol P k - P.d k) := by
        simp only [Function.comp]
        rw [← Equiv.sum_comp (Equiv.swap i j) (fun k => utilSol P k - P.d k)]
        exact Finset.sum_congr rfl fun k _ => by rw [hd k (Equiv.swap i j k)]
      rw [e]; exact h.2.2 u hu hdu
  have := congrFun (huniq _ _ hσ h) i
  simpa [Function.comp, Equiv.swap_apply_left] using this.symm

end MWG.WelfareBargaining
