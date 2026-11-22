/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGCompetitiveMarkets.FOCTools
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Tools: quasilinear Pareto optimality, take-it-or-leave-it offers, Kuhn-Tucker on `ℝ₊`

MWG, Chapter 11 (pp. 350-382) uses three arguments repeatedly; they are proved here once.

* **Quasilinear Pareto optimality** (footnote 4, p. 353; Sections 11.C-11.D). In an economy whose
  agents have utilities `Vᵢ(x) + mᵢ`, where `x` is a common "level" (of an externality, of a public
  good, a vector of externality levels, ...) chosen from a set `D` at numeraire cost `C(x)` and
  the numeraire is freely transferable (`∑ mᵢ = W - C(x)`), a feasible allocation is Pareto optimal
  if and only if `x` maximizes the aggregate surplus `∑ Vᵢ(x) - C(x)` on `D`
  (`ql_pareto_iff`). The numeraire is unrestricted in sign, as in MWG's quasilinear models.
* **Take-it-or-leave-it offers** (pp. 356-357): a proposer who chooses `(h, T)` to maximize
  `g(h) + T` subject to the responder's acceptance constraint `r(h) - T ≥ ρ` chooses exactly the
  joint-surplus maximizing `h` and leaves the responder at `ρ` (`tioli_iff`).
* **Kuhn-Tucker on `ℝ₊`** for concave functions: Chapter 10's `foc_max_iff` restated for functions
  differentiable on all of `ℝ` with strictly decreasing derivative (`kt_max_iff`), uniqueness of the
  maximizer (`kt_max_unique`), and monotonicity up to the maximizer (`kt_strictMonoOn`).
-/

namespace MWG.ExternalitiesPublicGoods

open MWG.CompetitiveMarkets

/-! ## Quasilinear Pareto optimality -/

variable {ι X : Type*} [Fintype ι]

/-- An allocation of a quasilinear economy with a common level: a level `x` and numeraire
holdings `mᵢ`. -/
structure QLAlloc (ι X : Type*) where
  /-- The common level. -/
  x : X
  /-- The numeraire holding of each agent. -/
  m : ι → ℝ

/-- Feasibility: the level lies in `D` and the numeraire holdings exhaust `W - C(x)`. -/
def QLFeasible (D : Set X) (C : X → ℝ) (W : ℝ) (a : QLAlloc ι X) : Prop :=
  a.x ∈ D ∧ ∑ i, a.m i = W - C a.x

/-- Pareto optimality (Definition 10.B.2) for utilities `Vᵢ(x) + mᵢ`. -/
def QLPareto (V : ι → X → ℝ) (D : Set X) (C : X → ℝ) (W : ℝ) (a : QLAlloc ι X) : Prop :=
  QLFeasible D C W a ∧ ¬ ∃ b : QLAlloc ι X, QLFeasible D C W b ∧
    (∀ i, V i a.x + a.m i ≤ V i b.x + b.m i) ∧ ∃ i, V i a.x + a.m i < V i b.x + b.m i

/-- The aggregate (Marshallian) surplus `∑ᵢ Vᵢ(x) - C(x)`. -/
def qlSurplus' (V : ι → X → ℝ) (C : X → ℝ) (x : X) : ℝ := ∑ i, V i x - C x

/-- **Footnote 4** (MWG, p. 353), in general form. A feasible allocation of a quasilinear
economy is Pareto optimal if and only if its level maximizes the aggregate surplus on `D`. -/
theorem ql_pareto_iff [Nonempty ι] (V : ι → X → ℝ) (D : Set X) (C : X → ℝ) (W : ℝ)
    (a : QLAlloc ι X) (ha : QLFeasible D C W a) :
    QLPareto V D C W a ↔ ∀ y ∈ D, qlSurplus' V C y ≤ qlSurplus' V C a.x := by
  constructor
  · rintro ⟨-, hno⟩ y hy
    by_contra hlt
    push Not at hlt
    have hcard : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
    set δ := (qlSurplus' V C y - qlSurplus' V C a.x) / Fintype.card ι with hδ
    have hδpos : 0 < δ := div_pos (by linarith) hcard
    refine hno ⟨⟨y, fun i => V i a.x + a.m i - V i y + δ⟩, ⟨hy, ?_⟩, fun i => ?_, ?_⟩
    · simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
      rw [ha.2, hδ, mul_div_cancel₀ _ hcard.ne']
      simp only [qlSurplus']
      ring
    · simp only
      linarith
    · obtain ⟨i⟩ := ‹Nonempty ι›
      exact ⟨i, by simp only; linarith⟩
  · intro hmax
    refine ⟨ha, ?_⟩
    rintro ⟨b, hb, hle, i, hlt⟩
    have hsum : ∑ j, (V j a.x + a.m j) < ∑ j, (V j b.x + b.m j) :=
      Finset.sum_lt_sum (fun j _ => hle j) ⟨i, Finset.mem_univ _, hlt⟩
    simp only [Finset.sum_add_distrib, ha.2, hb.2] at hsum
    have := hmax b.x hb.1
    simp only [qlSurplus'] at this
    linarith

/-- A Pareto optimal allocation exists at any surplus-maximizing level (give the remaining
numeraire to anyone). -/
theorem ql_pareto_exists [Nonempty ι] (V : ι → X → ℝ) (D : Set X) (C : X → ℝ)
    (W : ℝ) {x : X} (hx : x ∈ D) (hmax : ∀ y ∈ D, qlSurplus' V C y ≤ qlSurplus' V C x) :
    ∃ a : QLAlloc ι X, a.x = x ∧ QLPareto V D C W a := by
  classical
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hfeas : QLFeasible D C W (⟨x, Pi.single i (W - C x)⟩ : QLAlloc ι X) :=
    ⟨hx, by simp⟩
  exact ⟨_, rfl, (ql_pareto_iff V D C W _ hfeas).2 hmax⟩

/-! ## Take-it-or-leave-it offers -/

/-- The proposer's problem: `(h, T)` maximizes `g(h) + T` over `h ∈ D` subject to the
responder's acceptance constraint `r(h) - T ≥ ρ`. -/
def IsTIOLIOffer (D : Set X) (g r : X → ℝ) (ρ : ℝ) (h : X) (T : ℝ) : Prop :=
  h ∈ D ∧ ρ ≤ r h - T ∧ ∀ h' ∈ D, ∀ T' : ℝ, ρ ≤ r h' - T' → g h' + T' ≤ g h + T

/-- **Take-it-or-leave-it offers** (MWG, pp. 356-357). `(h, T)` solves the proposer's problem if
and only if `h` maximizes the joint surplus `g + r` on `D` and the responder is held to her
reservation utility: `T = r(h) - ρ`. -/
theorem tioli_iff (D : Set X) (g r : X → ℝ) (ρ : ℝ) (h : X) (T : ℝ) :
    IsTIOLIOffer D g r ρ h T ↔
      h ∈ D ∧ (∀ h' ∈ D, g h' + r h' ≤ g h + r h) ∧ T = r h - ρ := by
  constructor
  · rintro ⟨hD, hc, hmax⟩
    have hT : T = r h - ρ := by
      have := hmax h hD (r h - ρ) (by linarith)
      linarith
    refine ⟨hD, fun h' hh' => ?_, hT⟩
    have := hmax h' hh' (r h' - ρ) (by linarith)
    linarith
  · rintro ⟨hD, hmax, hT⟩
    refine ⟨hD, by linarith, fun h' hh' T' hT' => ?_⟩
    have := hmax h' hh'
    linarith

/-! ## Kuhn-Tucker conditions on `ℝ₊` -/

/-- **Kuhn-Tucker on `ℝ₊`** (the form of (11.B.1)-(11.B.4)). For `f` differentiable on `ℝ` with
derivative `f'` decreasing on `[0, ∞)`, `a ≥ 0` maximizes `f` on `[0, ∞)` iff
`f'(a) ≤ 0`, with equality if `a > 0` (Chapter 10's `foc_max_iff`). -/
theorem kt_max_iff {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hanti : AntitoneOn f' (Set.Ici 0)) {a : ℝ} (ha : 0 ≤ a) :
    (∀ y, 0 ≤ y → f y ≤ f a) ↔ IsFOCSol f' 0 a := by
  rw [foc_max_iff (fun x _ => (hf x).hasDerivWithinAt) hanti ha]
  exact ⟨fun h => ⟨ha, h⟩, fun h => h.2⟩

/-- The same statement with the maximization stated with the nonnegativity of `a` included. -/
theorem kt_isMax_iff {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hanti : AntitoneOn f' (Set.Ici 0)) {a : ℝ} :
    (0 ≤ a ∧ ∀ y, 0 ≤ y → f y ≤ f a) ↔ IsFOCSol f' 0 a := by
  constructor
  · rintro ⟨ha, h⟩
    exact (kt_max_iff hf hanti ha).1 h
  · intro h
    exact ⟨h.1, (kt_max_iff hf hanti h.1).2 h⟩

/-- With a strictly decreasing derivative the maximizer on `[0, ∞)` is unique. -/
theorem kt_max_unique {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hanti : StrictAntiOn f' (Set.Ici 0)) {a b : ℝ} (ha : 0 ≤ a)
    (hamax : ∀ y, 0 ≤ y → f y ≤ f a) (hb : 0 ≤ b) (hbmax : ∀ y, 0 ≤ y → f y ≤ f b) :
    a = b :=
  isFOCSol_unique hanti ((kt_max_iff hf hanti.antitoneOn ha).1 hamax)
    ((kt_max_iff hf hanti.antitoneOn hb).1 hbmax)

/-- A Kuhn-Tucker point of a function with strictly decreasing derivative is the unique
maximizer: every other `y ≥ 0` gives a strictly lower value. -/
theorem kt_strict_max {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hanti : StrictAntiOn f' (Set.Ici 0)) {a : ℝ} (ha : IsFOCSol f' 0 a) {y : ℝ} (hy : 0 ≤ y)
    (hya : y ≠ a) : f y < f a := by
  have hmax := (kt_max_iff hf hanti.antitoneOn ha.1).2 ha
  refine lt_of_le_of_ne (hmax y hy) fun heq => hya ?_
  refine kt_max_unique hf hanti hy (fun z hz => ?_) ha.1 hmax
  rw [heq]
  exact hmax z hz

/-- A function whose derivative is positive on `[a, b)` is strictly increasing on `[a, b]`. -/
theorem strictMonoOn_Icc_of_deriv_pos {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    {a b : ℝ} (hpos : ∀ x, a ≤ x → x < b → 0 < f' x) : StrictMonoOn f (Set.Icc a b) := by
  refine strictMonoOn_of_deriv_pos (convex_Icc a b)
    (fun x _ => (hf x).continuousAt.continuousWithinAt) fun x hx => ?_
  rw [interior_Icc] at hx
  rw [(hf x).deriv]
  exact hpos x hx.1.le hx.2

/-- **Concave functions increase up to their maximizer.** If `f'` is strictly decreasing on
`[0, ∞)` and `a` is the Kuhn-Tucker point, `f` is strictly increasing on `[0, a]`. -/
theorem kt_strictMonoOn {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hanti : StrictAntiOn f' (Set.Ici 0)) {a : ℝ} (ha : IsFOCSol f' 0 a) :
    StrictMonoOn f (Set.Icc 0 a) := by
  refine strictMonoOn_Icc_of_deriv_pos hf fun x hx hxa => ?_
  have hapos : 0 < a := lt_of_le_of_lt hx hxa
  have := hanti hx ha.1 hxa
  rw [ha.2.2 hapos] at this
  exact this

/-- `φ'' < 0` (MWG's assumption, p. 353) gives a strictly decreasing derivative. -/
theorem strictAntiOn_of_second_deriv_neg {f' f'' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f' (f'' x) x)
    (hneg : ∀ x, 0 ≤ x → f'' x < 0) : StrictAntiOn f' (Set.Ici 0) := by
  refine strictAntiOn_of_deriv_neg (convex_Ici 0)
    (fun x _ => (hf x).continuousAt.continuousWithinAt) fun x hx => ?_
  rw [interior_Ici] at hx
  rw [(hf x).deriv]
  exact hneg x (le_of_lt hx)

end MWG.ExternalitiesPublicGoods
