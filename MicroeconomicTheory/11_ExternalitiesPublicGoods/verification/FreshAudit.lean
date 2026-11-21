import MWGCompetitiveMarkets.FOCTools
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import MWGSimultaneousMoveGames.Dominance
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Convex.Quasiconvex
import Mathlib.Analysis.Calculus.LagrangeMultipliers
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Probability.Distributions.Uniform
set_option autoImplicit false

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

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

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Concave functions of several variables: tangent inequality and Kuhn-Tucker on the orthant

Tools for the exercises with several choice variables (Exercises 11.B.5, 11.D.2, 11.D.4).

* `convex_tangent`, `concave_tangent`: for a convex (concave) function with Fréchet derivative
  `L` at `x`, `c(x) + L(y - x) ≤ c(y)` (resp. `≥`) for all `y` in the domain.
* `orthant_kt_iff`: a point `x ≥ 0` maximizes a concave differentiable `F` on the nonnegative
  orthant of `ℝ^ι` iff each partial derivative `∂ⱼF(x) = L(eⱼ)` is `≤ 0`, with equality if
  `xⱼ > 0`.
-/

namespace MWG.ExternalitiesPublicGoods

open MWG.CompetitiveMarkets

/-- **Tangent inequality for convex functions.** If `c` is convex on `S`, `x, y ∈ S` and `c` has
Fréchet derivative `L` at `x`, then `c(x) + L(y - x) ≤ c(y)`. -/
theorem convex_tangent {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {S : Set E}
    {c : E → ℝ} (hc : ConvexOn ℝ S c) {x y : E} (hx : x ∈ S) (hy : y ∈ S) {L : E →L[ℝ] ℝ}
    (hL : HasFDerivAt c L x) : c x + L (y - x) ≤ c y := by
  set ℓ : ℝ → E := fun s => x + s • (y - x)
  have hℓS : ∀ s ∈ Set.Icc (0 : ℝ) 1, ℓ s ∈ S := fun s hs => by
    have := hc.1 hx hy (sub_nonneg.2 hs.2) hs.1 (by ring)
    convert this using 1
    simp only [ℓ, smul_sub, sub_smul, one_smul]
    abel
  set g : ℝ → ℝ := fun s => c (ℓ s)
  have hg : ConvexOn ℝ (Set.Icc 0 1) g := by
    refine ⟨convex_Icc 0 1, fun s hs t ht a b ha hb hab => ?_⟩
    have := hc.2 (hℓS s hs) (hℓS t ht) ha hb hab
    convert this using 2
    have hx' : x = a • x + b • x := by rw [← add_smul, hab, one_smul]
    simp only [ℓ, smul_add, smul_smul, smul_eq_mul, add_smul]
    nth_rewrite 1 [hx']
    abel
  have hℓ : HasDerivAt ℓ (y - x) 0 := by
    have h1 : HasDerivAt (fun s : ℝ => s • (y - x)) ((1 : ℝ) • (y - x)) 0 :=
      (hasDerivAt_id (0 : ℝ)).smul_const (y - x)
    rw [one_smul] at h1
    exact h1.const_add x
  have hℓ0 : ℓ 0 = x := by simp [ℓ]
  have hL' : HasFDerivAt c L (ℓ 0) := by rw [hℓ0]; exact hL
  have hgd : HasDerivAt g (L (y - x)) 0 := hL'.comp_hasDerivAt 0 hℓ
  have := hg.deriv_le_slope ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_lt_one
    hgd.differentiableAt
  rw [hgd.deriv, slope_def_field] at this
  have h1 : g 1 = c y := by simp [g, ℓ]
  have h0 : g 0 = c x := by simp [g, ℓ]
  rw [h1, h0] at this
  linarith

/-- **Tangent inequality for concave functions**: `c(y) ≤ c(x) + L(y - x)`. -/
theorem concave_tangent {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {S : Set E}
    {c : E → ℝ} (hc : ConcaveOn ℝ S c) {x y : E} (hx : x ∈ S) (hy : y ∈ S) {L : E →L[ℝ] ℝ}
    (hL : HasFDerivAt c L x) : c y ≤ c x + L (y - x) := by
  have := convex_tangent hc.neg hx hy hL.neg
  have e : (-L) (y - x) = -(L (y - x)) := rfl
  simp only [Pi.neg_apply, e] at this
  linarith

/-- The nonnegative orthant of `ℝ^ι`. -/
def orthant (ι : Type*) : Set (ι → ℝ) := {x | ∀ i, 0 ≤ x i}

theorem convex_orthant (ι : Type*) : Convex ℝ (orthant ι) := by
  intro x hx y hy a b ha hb _ i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  exact add_nonneg (mul_nonneg ha (hx i)) (mul_nonneg hb (hy i))

/-- The derivative of `F` along the `j`-th coordinate line through `x`. -/
theorem hasDerivAt_update {ι : Type*} [Finite ι] [DecidableEq ι] {F : (ι → ℝ) → ℝ}
    {x : ι → ℝ} {L : (ι → ℝ) →L[ℝ] ℝ} (hL : HasFDerivAt F L x) (j : ι) :
    HasDerivAt (fun t => F (Function.update x j t)) (L (Pi.single j 1)) (x j) := by
  have := Fintype.ofFinite ι
  have hupd : ∀ t, Function.update x j t = x + (t - x j) • Pi.single j 1 := fun t => by
    funext k
    rcases eq_or_ne k j with h | h
    · subst h; simp
    · simp [Function.update_of_ne h, Pi.single_eq_of_ne h]
  have hℓ : HasDerivAt (fun t => x + (t - x j) • (Pi.single j 1 : ι → ℝ)) (Pi.single j 1)
      (x j) := by
    have h1 : HasDerivAt (fun t : ℝ => (t - x j) • (Pi.single j 1 : ι → ℝ))
        ((1 : ℝ) • (Pi.single j 1 : ι → ℝ)) (x j) :=
      ((hasDerivAt_id (x j)).sub_const (x j)).smul_const (Pi.single j 1 : ι → ℝ)
    rw [one_smul] at h1
    exact h1.const_add x
  have hx : x + (x j - x j) • (Pi.single j 1 : ι → ℝ) = x := by simp
  have hL' : HasFDerivAt F L (x + (x j - x j) • (Pi.single j 1 : ι → ℝ)) := by rw [hx]; exact hL
  have := hL'.comp_hasDerivAt (x j) hℓ
  simp_rw [hupd]
  exact this

/-- `L(v) = ∑ⱼ vⱼ L(eⱼ)` for a linear functional on `ℝ^ι`. -/
theorem clm_apply_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (L : (ι → ℝ) →L[ℝ] ℝ)
    (v : ι → ℝ) : L v = ∑ j, v j * L (Pi.single j 1) := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hs : (Pi.single j (v j) : ι → ℝ) = v j • Pi.single j 1 := by
    ext k
    rcases eq_or_ne k j with h | h
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
  rw [hs, map_smul, smul_eq_mul]

/-- **Kuhn-Tucker on the orthant.** For `F` concave on `ℝ^ι₊` with derivative `L` at `x ≥ 0`,
`x` maximizes `F` on `ℝ^ι₊` iff every partial derivative `L(eⱼ)` is `≤ 0`, with equality if
`xⱼ > 0`. -/
theorem orthant_kt_iff {ι : Type*} [Finite ι] [DecidableEq ι] {F : (ι → ℝ) → ℝ}
    (hF : ConcaveOn ℝ (orthant ι) F) {x : ι → ℝ} (hx : x ∈ orthant ι)
    {L : (ι → ℝ) →L[ℝ] ℝ} (hL : HasFDerivAt F L x) :
    (∀ y ∈ orthant ι, F y ≤ F x) ↔
      ∀ j, L (Pi.single j 1) ≤ 0 ∧ (0 < x j → L (Pi.single j 1) = 0) := by
  have := Fintype.ofFinite ι
  constructor
  · intro hmax j
    have hmax' : ∀ t, 0 ≤ t → F (Function.update x j t) ≤ F (Function.update x j (x j)) := by
      intro t ht
      rw [Function.update_eq_self]
      refine hmax _ fun k => ?_
      rcases eq_or_ne k j with h | h
      · subst h; simpa using ht
      · rw [Function.update_of_ne h]; exact hx k
    exact foc_max_necessary (hasDerivAt_update hL j).hasDerivWithinAt (hx j) hmax'
  · intro hkt y hy
    have ht := concave_tangent hF hx hy hL
    rw [clm_apply_eq_sum] at ht
    have : ∑ j, (y - x) j * L (Pi.single j 1) ≤ 0 := by
      refine Finset.sum_nonpos fun j _ => ?_
      rcases eq_or_lt_of_le (hx j) with h0 | hp
      · simp only [Pi.sub_apply, ← h0, sub_zero]
        exact mul_nonpos_of_nonneg_of_nonpos (hy j) (hkt j).1
      · rw [(hkt j).2 hp, mul_zero]
    linarith

end MWG.ExternalitiesPublicGoods

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# A simple bilateral externality (MWG Section 11.B)

MWG, pp. 351-359.

* **Definition 11.B.1** (`HasExternality`) and footnote 2 (positive and negative externalities).
* The derived utility `vᵢ(p, wᵢ, h)` and **footnote 3** (p. 353): with utility `g(x₋₁, h) + x₁`
  the derived utility is `φ(p, h) + w` (`footnote_3`). We keep MWG's nonnegativity of all goods
  and assume wealth covers the optimal purchases of the non-numeraire goods.
* The model (`Bilateral`): `φ₁, φ₂` differentiable with strictly decreasing derivatives on
  `[0, ∞)` (implied by MWG's `φᵢ'' < 0`, `strictAntiOn_of_second_deriv_neg`).
* (11.B.1) and (11.B.2) (`eq_11_B_1`, `eq_11_B_2`), **footnote 4** (`footnote_4`: Pareto
  optimality iff the joint surplus is maximized), the nonoptimality of the equilibrium
  (`eq_ne_opt`, `negative_externality_excess`, `positive_externality_shortfall`).
* Quotas, the Pigouvian tax (11.B.3)-(11.B.4) (`pigou_tax`, `pigou_tax_unique`), footnote 5,
  subsidies for reduction (`subsidy_equiv_tax`).
* Bargaining with enforceable property rights, (11.B.5), the Coase theorem (`coase_theorem`),
  the payments on p. 357 and Figure 11.B.3.
* Missing markets: (11.B.6)-(11.B.7), the competitive rights market reaches `h°` with
  `p_h* = φ₁'(h°) = -φ₂'(h°)`.
-/

namespace MWG.ExternalitiesPublicGoods

open MWG.CompetitiveMarkets

/-! ## Definition 11.B.1 and footnotes 2-3 -/

/-- **Definition 11.B.1** (MWG, p. 352). An externality is present when an agent's well-being
`u(x, h)` depends directly on an action `h` chosen by another agent: for some own choice `x` the
utility changes with `h`. -/
def HasExternality {Y A : Type*} (u : Y → A → ℝ) : Prop :=
  ∃ x h h', u x h ≠ u x h'

/-- **Definition 11.B.1** (MWG, p. 352), unfolded. -/
theorem definition_11_B_1 {Y A : Type*} (u : Y → A → ℝ) :
    HasExternality u ↔ ∃ x h h', u x h ≠ u x h' := Iff.rfl

/-- **Footnote 2** (MWG, p. 352). A positive externality: well-being increases with `h`. -/
def PositiveExternality {Y : Type*} (u : Y → ℝ → ℝ) : Prop := ∀ x, StrictMono (u x)

/-- **Footnote 2** (MWG, p. 352). A negative externality: well-being decreases with `h`. -/
def NegativeExternality {Y : Type*} (u : Y → ℝ → ℝ) : Prop := ∀ x, StrictAnti (u x)

/-- MWG's condition `∂u₂/∂h ≠ 0` (p. 352) makes `h` an externality in the sense of
Definition 11.B.1. -/
theorem hasExternality_of_deriv_ne {Y : Type*} [Nonempty Y] (u : Y → ℝ → ℝ) (u' : Y → ℝ → ℝ)
    (hu : ∀ x h, HasDerivAt (u x) (u' x h) h) (hne : ∀ x h, u' x h ≠ 0) :
    HasExternality u := by
  obtain ⟨x⟩ := ‹Nonempty Y›
  by_contra hno
  have hconst : ∀ h h', u x h = u x h' := fun h h' => by
    by_contra hne'
    exact hno ⟨x, h, h', hne'⟩
  have hd : HasDerivAt (u x) 0 0 := by
    have : u x = fun _ => u x 0 := funext fun h => hconst h 0
    rw [this]
    exact hasDerivAt_const _ _
  exact hne x 0 ((hu x 0).unique hd)

/-- A positive (or negative) externality is an externality. -/
theorem PositiveExternality.hasExternality {Y : Type*} [Nonempty Y] {u : Y → ℝ → ℝ}
    (h : PositiveExternality u) : HasExternality u := by
  obtain ⟨x⟩ := ‹Nonempty Y›
  exact ⟨x, 0, 1, (h x zero_lt_one).ne⟩

/-- A negative externality is an externality. -/
theorem NegativeExternality.hasExternality {Y : Type*} [Nonempty Y] {u : Y → ℝ → ℝ}
    (h : NegativeExternality u) : HasExternality u := by
  obtain ⟨x⟩ := ‹Nonempty Y›
  exact ⟨x, 0, 1, (h x zero_lt_one).ne'⟩

/-- **Footnote 3** (MWG, p. 353). With utility `g(x₋₁, h) + x₁` (good `1` the numeraire, price
`1`) and prices `p` for the other goods, suppose `y*` maximizes `g(y, h) - p·y` over `y ≥ 0` and
wealth covers it (`p·y* ≤ w`). Then the maximal utility over the budget set
`{x₁ ≥ 0, y ≥ 0, x₁ + p·y ≤ w}` is `φ(p, h) + w`, where `φ(p, h) = g(y*, h) - p·y*`, attained at
`(w - p·y*, y*)`: derived utility is quasilinear in wealth. -/
theorem footnote_3 {n : ℕ} (g : (Fin n → ℝ) → ℝ → ℝ) (p : Fin n → ℝ) (w h : ℝ)
    (ys : Fin n → ℝ)
    (hmax : ∀ y : Fin n → ℝ, (∀ l, 0 ≤ y l) → g y h - ∑ l, p l * y l ≤ g ys h - ∑ l, p l * ys l)
    (hw : ∑ l, p l * ys l ≤ w) :
    (0 ≤ w - ∑ l, p l * ys l ∧ (w - ∑ l, p l * ys l) + ∑ l, p l * ys l ≤ w) ∧
      g ys h + (w - ∑ l, p l * ys l) = (g ys h - ∑ l, p l * ys l) + w ∧
      ∀ (x₁ : ℝ) (y : Fin n → ℝ), 0 ≤ x₁ → (∀ l, 0 ≤ y l) → x₁ + ∑ l, p l * y l ≤ w →
        g y h + x₁ ≤ (g ys h - ∑ l, p l * ys l) + w := by
  refine ⟨⟨by linarith, by linarith⟩, by ring, fun x₁ y _ hy hb => ?_⟩
  have := hmax y hy
  linarith

/-! ## The model -/

/-- **The bilateral externality model** (MWG, pp. 352-353). Derived utilities `φᵢ(h) + wᵢ`;
`φᵢ` is differentiable with derivative `dᵢ`, strictly decreasing on `[0, ∞)` (MWG: `φᵢ'' < 0`). -/
structure Bilateral where
  /-- Consumer 1's derived utility from `h` (she chooses `h`). -/
  φ₁ : ℝ → ℝ
  /-- Consumer 2's derived utility from `h`. -/
  φ₂ : ℝ → ℝ
  /-- `φ₁'`. -/
  d₁ : ℝ → ℝ
  /-- `φ₂'`. -/
  d₂ : ℝ → ℝ
  hd₁ : ∀ h, HasDerivAt φ₁ (d₁ h) h
  hd₂ : ∀ h, HasDerivAt φ₂ (d₂ h) h
  anti₁ : StrictAntiOn d₁ (Set.Ici 0)
  anti₂ : StrictAntiOn d₂ (Set.Ici 0)

namespace Bilateral

variable (M : Bilateral)

/-- The joint surplus `φ₁ + φ₂`. -/
def joint (h : ℝ) : ℝ := M.φ₁ h + M.φ₂ h

theorem hasDerivAt_joint (h : ℝ) : HasDerivAt M.joint (M.d₁ h + M.d₂ h) h :=
  (M.hd₁ h).add (M.hd₂ h)

theorem anti_joint : StrictAntiOn (fun h => M.d₁ h + M.d₂ h) (Set.Ici 0) :=
  fun _ ha _ hb hab => add_lt_add (M.anti₁ ha hb hab) (M.anti₂ ha hb hab)

/-- The competitive equilibrium level `h*`: consumer 1 maximizes `φ₁` on `ℝ₊`. -/
def IsEqLevel (h : ℝ) : Prop := 0 ≤ h ∧ ∀ y, 0 ≤ y → M.φ₁ y ≤ M.φ₁ h

/-- The Pareto optimal level `h°`: it maximizes the joint surplus on `ℝ₊`. -/
def IsOptLevel (h : ℝ) : Prop := 0 ≤ h ∧ ∀ y, 0 ≤ y → M.joint y ≤ M.joint h

/-- **(11.B.1)** (MWG, p. 353). `h*` is the equilibrium level iff `φ₁'(h*) ≤ 0`, with equality if
`h* > 0`. -/
theorem eq_11_B_1 (h : ℝ) : M.IsEqLevel h ↔ IsFOCSol M.d₁ 0 h :=
  kt_isMax_iff M.hd₁ M.anti₁.antitoneOn

/-- **(11.B.2)** (MWG, p. 353). `h°` is optimal iff `φ₁'(h°) ≤ -φ₂'(h°)`, with equality if
`h° > 0`. -/
theorem eq_11_B_2 (h : ℝ) :
    M.IsOptLevel h ↔ 0 ≤ h ∧ M.d₁ h ≤ -M.d₂ h ∧ (0 < h → M.d₁ h = -M.d₂ h) := by
  rw [IsOptLevel, kt_isMax_iff M.hasDerivAt_joint M.anti_joint.antitoneOn]
  simp only [IsFOCSol]
  constructor
  · rintro ⟨h0, h1, h2⟩
    exact ⟨h0, by linarith, fun hp => by linarith [h2 hp]⟩
  · rintro ⟨h0, h1, h2⟩
    exact ⟨h0, by linarith, fun hp => by linarith [h2 hp]⟩

/-- **Footnote 4** (MWG, p. 353). An allocation `(h, m₁, m₂)` with `m₁ + m₂ = w₁ + w₂` (utilities
`φᵢ(h) + mᵢ`) is Pareto optimal iff `h` is an optimal level. -/
theorem footnote_4 (w : ℝ) (a : QLAlloc (Fin 2) ℝ)
    (ha : QLFeasible (Set.Ici 0) (fun _ => 0) w a) :
    QLPareto (fun i => if i = 0 then M.φ₁ else M.φ₂) (Set.Ici 0) (fun _ => 0) w a ↔
      M.IsOptLevel a.x := by
  rw [ql_pareto_iff _ _ _ _ a ha]
  simp only [qlSurplus', Fin.sum_univ_two, Fin.isValue, ↓reduceIte, one_ne_zero, sub_zero,
    Set.mem_Ici]
  exact ⟨fun h => ⟨ha.1, fun y hy => h y hy⟩, fun h y hy => h.2 y hy⟩

/-- With external effects (`φ₂'(h) ≠ 0` at all `h`), **the equilibrium level is not optimal unless
`h° = h* = 0`** (MWG, p. 353). -/
theorem eq_ne_opt (hne : ∀ h, M.d₂ h ≠ 0) {h : ℝ} (he : M.IsEqLevel h) (ho : M.IsOptLevel h) :
    h = 0 := by
  rw [eq_11_B_1] at he
  rw [eq_11_B_2] at ho
  rcases eq_or_lt_of_le he.1 with h0 | hpos
  · exact h0.symm
  · exfalso
    have h1 := he.2.2 hpos
    have h2 := ho.2.2 hpos
    exact hne h (by linarith)

/-- **Negative externality: too much `h`** (MWG, p. 354). If `φ₂' < 0`, then `h° ≤ h*`, and
`h° < h*` whenever `h* > 0` (in particular for interior `(h*, h°) ≫ 0`). -/
theorem negative_externality_excess (hneg : ∀ h, 0 ≤ h → M.d₂ h < 0) {hs ho : ℝ}
    (he : M.IsEqLevel hs) (hopt : M.IsOptLevel ho) : ho ≤ hs ∧ (0 < hs → ho < hs) := by
  rw [eq_11_B_1] at he
  rw [eq_11_B_2] at hopt
  have key : ¬ hs < ho := fun hlt => by
    have e2 := hopt.2.2 (he.1.trans_lt hlt)
    have := M.anti₁ he.1 hopt.1 hlt
    have := hneg ho hopt.1
    linarith [he.2.1]
  refine ⟨not_lt.1 key, fun hpos => lt_of_le_of_ne (not_lt.1 key) fun heq => ?_⟩
  have e1 := he.2.2 hpos
  have e2 := hopt.2.2 (heq ▸ hpos)
  rw [heq] at e2
  have := hneg hs he.1
  linarith

/-- **Positive externality: too little `h`** (MWG, p. 354). If `φ₂' > 0`, then `h* ≤ h°`, and
`h* < h°` whenever `h° > 0`. -/
theorem positive_externality_shortfall (hpos : ∀ h, 0 ≤ h → 0 < M.d₂ h) {hs ho : ℝ}
    (he : M.IsEqLevel hs) (hopt : M.IsOptLevel ho) : hs ≤ ho ∧ (0 < ho → hs < ho) := by
  rw [eq_11_B_1] at he
  rw [eq_11_B_2] at hopt
  have key : ¬ ho < hs := fun hlt => by
    have e1 := he.2.2 (hopt.1.trans_lt hlt)
    have := M.anti₁ hopt.1 he.1 hlt
    have := hpos ho hopt.1
    linarith [hopt.2.1]
  refine ⟨not_lt.1 key, fun hp => lt_of_le_of_ne (not_lt.1 key) fun heq => ?_⟩
  have e2 := hopt.2.2 hp
  have e1 := he.2.2 (heq ▸ hp)
  rw [← heq] at e2
  have := hpos hs he.1
  linarith

/-- **Small type, p. 354.** With quasilinear utilities the optimal level does not depend on the
consumers' wealths: for any wealths, Pareto optimal allocations (footnote 4) have `h` optimal. -/
theorem opt_indep_wealth (w w' : ℝ) (a : QLAlloc (Fin 2) ℝ)
    (ha : QLFeasible (Set.Ici 0) (fun _ => 0) w a) (b : QLAlloc (Fin 2) ℝ)
    (hb : QLFeasible (Set.Ici 0) (fun _ => 0) w' b) (hab : a.x = b.x) :
    QLPareto (fun i => if i = 0 then M.φ₁ else M.φ₂) (Set.Ici 0) (fun _ => 0) w a ↔
      QLPareto (fun i => if i = 0 then M.φ₁ else M.φ₂) (Set.Ici 0) (fun _ => 0) w' b := by
  rw [M.footnote_4 w a ha, M.footnote_4 w' b hb, hab]

/-! ## Quotas and Pigouvian taxes -/

/-- **Quota** (MWG, p. 354). With a negative externality (`h° < h*`), a quota `h ≤ h°` leads
consumer 1 to choose exactly `h°`: it is her unique best choice in `[0, h°]`. -/
theorem quota_implements {hs ho : ℝ} (he : M.IsEqLevel hs) (hopt : M.IsOptLevel ho)
    (hlt : ho ≤ hs) : ∀ y, 0 ≤ y → y ≤ ho → y ≠ ho → M.φ₁ y < M.φ₁ ho := by
  rw [eq_11_B_1] at he
  intro y hy hyo hne
  exact kt_strictMonoOn M.hd₁ M.anti₁ he ⟨hy, hyo.trans hlt⟩ ⟨hopt.1, hlt⟩
    (lt_of_le_of_ne hyo hne)

/-- Consumer 1's problem under a per-unit tax `t` (11.B.3): `max_{h ≥ 0} φ₁(h) - t h`. -/
def IsTaxChoice (t h : ℝ) : Prop := 0 ≤ h ∧ ∀ y, 0 ≤ y → M.φ₁ y - t * y ≤ M.φ₁ h - t * h

/-- **(11.B.4)** (MWG, p. 355). `h` solves (11.B.3) iff `φ₁'(h) ≤ t`, with equality if `h > 0`. -/
theorem eq_11_B_4 (t h : ℝ) : M.IsTaxChoice t h ↔ IsFOCSol M.d₁ t h := by
  have hf : ∀ x, HasDerivAt (fun h => M.φ₁ h - t * h) (M.d₁ x - t) x := fun x => by
    have h2 : HasDerivAt (fun y => t * y) t x := by simpa using (hasDerivAt_id x).const_mul t
    exact (M.hd₁ x).sub h2
  have hanti : AntitoneOn (fun x => M.d₁ x - t) (Set.Ici 0) :=
    fun a ha b hb hab => by simpa using M.anti₁.antitoneOn ha hb hab
  rw [IsTaxChoice, kt_isMax_iff hf hanti]
  simp only [IsFOCSol]
  constructor
  · rintro ⟨h0, h1, h2⟩
    exact ⟨h0, by linarith, fun hp => by linarith [h2 hp]⟩
  · rintro ⟨h0, h1, h2⟩
    exact ⟨h0, by linarith, fun hp => by linarith [h2 hp]⟩

/-- **The Pigouvian tax** (MWG, p. 355). The tax `t_h = -φ₂'(h°)` makes `h°` a solution of
(11.B.3). -/
theorem pigou_tax {ho : ℝ} (hopt : M.IsOptLevel ho) : M.IsTaxChoice (-M.d₂ ho) ho := by
  rw [eq_11_B_4]
  rw [eq_11_B_2] at hopt
  exact hopt

/-- **The Pigouvian tax implements `h°` uniquely** (MWG, p. 355: given `φ₁'' < 0`, `h°` is the
unique solution of (11.B.3)). -/
theorem pigou_tax_unique {ho h : ℝ} (hopt : M.IsOptLevel ho) (hh : M.IsTaxChoice (-M.d₂ ho) h) :
    h = ho := by
  rw [eq_11_B_4] at hh
  exact isFOCSol_unique M.anti₁ hh ((M.eq_11_B_4 _ _).1 (M.pigou_tax hopt))

/-- With a negative externality the Pigouvian tax is positive, with a positive externality it
is a subsidy (MWG, p. 355). -/
theorem pigou_tax_sign (ho : ℝ) : (M.d₂ ho < 0 → 0 < -M.d₂ ho) ∧ (0 < M.d₂ ho → -M.d₂ ho < 0) :=
  ⟨fun h => by linarith, fun h => by linarith⟩

/-- **Footnote 5** (MWG, p. 355). If `h° = 0`, any tax `t > -φ₂'(0)` (indeed `t ≥ -φ₂'(0)`) also
implements the optimal outcome, uniquely. -/
theorem footnote_5 (hopt : M.IsOptLevel 0) {t : ℝ} (ht : -M.d₂ 0 ≤ t) :
    M.IsTaxChoice t 0 ∧ ∀ h, M.IsTaxChoice t h → h = 0 := by
  rw [eq_11_B_2] at hopt
  have h0 : IsFOCSol M.d₁ t 0 := ⟨le_rfl, by linarith [hopt.2.1], fun h => absurd h (lt_irrefl 0)⟩
  refine ⟨(M.eq_11_B_4 t 0).2 h0, fun h hh => ?_⟩
  exact isFOCSol_unique M.anti₁ ((M.eq_11_B_4 t h).1 hh) h0

/-- **Subsidizing reductions** (MWG, p. 355). Paying `s_h = t` per unit of `h` below `h*` gives
consumer 1 the objective `φ₁(h) + t(h* - h) = (φ₁(h) - t h) + t h*`, so her choices coincide with
those under the tax `t` (a lump-sum transfer `t h*` aside). -/
theorem subsidy_equiv_tax (t hs h : ℝ) :
    (0 ≤ h ∧ ∀ y, 0 ≤ y → M.φ₁ y + t * (hs - y) ≤ M.φ₁ h + t * (hs - h)) ↔ M.IsTaxChoice t h := by
  constructor
  · rintro ⟨h0, hh⟩
    exact ⟨h0, fun y hy => by linarith [hh y hy]⟩
  · rintro ⟨h0, hh⟩
    exact ⟨h0, fun y hy => by linarith [hh y hy]⟩

/-- The tax and the quota achieve the same outcome `h°` (MWG, p. 356): with a negative
externality, the quota choice and the Pigouvian tax choice are both `h°`. -/
theorem tax_quota_equivalent {hs ho : ℝ} (he : M.IsEqLevel hs) (hopt : M.IsOptLevel ho)
    (hle : ho ≤ hs) :
    M.IsTaxChoice (-M.d₂ ho) ho ∧ ∀ y, 0 ≤ y → y ≤ ho → M.φ₁ y ≤ M.φ₁ ho := by
  refine ⟨M.pigou_tax hopt, fun y hy hyo => ?_⟩
  rcases eq_or_ne y ho with h | h
  · rw [h]
  · exact (M.quota_implements he hopt hle y hy hyo h).le

/-! ## Bargaining over externalities; the Coase theorem -/

/-- Consumer 2 holds the right to an externality-free environment and makes a take-it-or-leave-it
offer `(h, T)` (MWG, p. 356): `max φ₂(h) + T` s.t. `φ₁(h) - T ≥ φ₁(0)`. -/
def IsOffer2Free (h T : ℝ) : Prop := IsTIOLIOffer (Set.Ici 0) M.φ₂ M.φ₁ (M.φ₁ 0) h T

/-- Consumer 1 holds the right to generate the externality (`h*` absent agreement), and
consumer 2 makes the offer (MWG, p. 357): `max φ₂(h) + T` s.t. `φ₁(h) - T ≥ φ₁(h*)`. -/
def IsOffer2Right (hs h T : ℝ) : Prop := IsTIOLIOffer (Set.Ici 0) M.φ₂ M.φ₁ (M.φ₁ hs) h T

theorem joint_comm' (h : ℝ) : M.φ₂ h + M.φ₁ h = M.joint h := add_comm _ _

/-- **(11.B.5)** (MWG, p. 356). Consumer 2's optimal offer has `T = φ₁(h) - φ₁(0)` and `h`
maximizing `φ₂(h) + φ₁(h) - φ₁(0)`: `h = h°`, the socially optimal level. -/
theorem eq_11_B_5 (h T : ℝ) : M.IsOffer2Free h T ↔ M.IsOptLevel h ∧ T = M.φ₁ h - M.φ₁ 0 := by
  rw [IsOffer2Free, tioli_iff]
  simp only [Set.mem_Ici, joint_comm', IsOptLevel]
  exact ⟨fun ⟨a, b, c⟩ => ⟨⟨a, b⟩, c⟩, fun ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩⟩

/-- **The Coase theorem** (MWG, p. 357). Whichever consumer holds the property right, consumer 2's
take-it-or-leave-it offer sets `h = h°`: the allocation of rights affects only the payment. -/
theorem coase_theorem (hs h T : ℝ) :
    (M.IsOffer2Free h T ↔ M.IsOptLevel h ∧ T = M.φ₁ h - M.φ₁ 0) ∧
      (M.IsOffer2Right hs h T ↔ M.IsOptLevel h ∧ T = M.φ₁ h - M.φ₁ hs) := by
  refine ⟨M.eq_11_B_5 h T, ?_⟩
  rw [IsOffer2Right, tioli_iff]
  simp only [Set.mem_Ici, joint_comm', IsOptLevel]
  exact ⟨fun ⟨a, b, c⟩ => ⟨⟨a, b⟩, c⟩, fun ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩⟩

/-- **The payments** (MWG, p. 357), for a negative externality with `0 < h° < h*`: with the right
to an externality-free environment, consumer 1 pays `φ₁(h°) - φ₁(0) > 0`; with the right to
pollute, she "pays" `φ₁(h°) - φ₁(h*) < 0`. -/
theorem coase_payments {hs ho : ℝ} (he : M.IsEqLevel hs) (hopt : M.IsOptLevel ho)
    (hpos : 0 < ho) (hlt : ho < hs) :
    0 < M.φ₁ ho - M.φ₁ 0 ∧ M.φ₁ ho - M.φ₁ hs < 0 := by
  rw [eq_11_B_1] at he
  constructor
  · have := kt_strictMonoOn M.hd₁ M.anti₁ he ⟨le_rfl, he.1⟩ ⟨hopt.1, hlt.le⟩ hpos
    linarith
  · have := kt_strict_max M.hd₁ M.anti₁ he hopt.1 hlt.ne
    linarith

/-- Consumer 1 makes the take-it-or-leave-it offer instead (points `d` and `c` of Figure 11.B.3):
from disagreement point `h_d`, she offers `(h, T')` (payment `T'` to consumer 2) solving
`max φ₁(h) - T'` s.t. `φ₂(h) + T' ≥ φ₂(h_d)`; again `h = h°`. -/
theorem offer1_iff (hd h T' : ℝ) :
    IsTIOLIOffer (Set.Ici 0) M.φ₁ M.φ₂ (M.φ₂ hd) h (-T') ↔
      M.IsOptLevel h ∧ T' = M.φ₂ hd - M.φ₂ h := by
  rw [tioli_iff]
  simp only [Set.mem_Ici, IsOptLevel, joint]
  constructor
  · rintro ⟨a, b, c⟩
    exact ⟨⟨a, b⟩, by linarith⟩
  · rintro ⟨⟨a, b⟩, c⟩
    exact ⟨a, b, by linarith⟩

/-- **Figure 11.B.3** (MWG, p. 357). From the disagreement point `a = (φ₁(h_d) + w₁, φ₂(h_d) + w₂)`
the post-bargaining utilities are `f` (consumer 2 proposes) and `d` (consumer 1 proposes); both
lie on the frontier `u₁ + u₂ = φ₁(h°) + φ₂(h°) + w₁ + w₂`, and the individually rational frontier
points are exactly the segment `[f, d]`. -/
theorem figure_11_B_3 (hd ho w₁ w₂ u₁ u₂ : ℝ) (hopt : M.IsOptLevel ho) (hd0 : 0 ≤ hd) :
    let S := M.φ₁ ho + M.φ₂ ho
    let f : ℝ × ℝ := (M.φ₁ hd + w₁, S - M.φ₁ hd + w₂)
    let d : ℝ × ℝ := (S - M.φ₂ hd + w₁, M.φ₂ hd + w₂)
    f.1 + f.2 = S + w₁ + w₂ ∧ d.1 + d.2 = S + w₁ + w₂ ∧
      ((u₁ + u₂ = S + w₁ + w₂ ∧ M.φ₁ hd + w₁ ≤ u₁ ∧ M.φ₂ hd + w₂ ≤ u₂) ↔
        ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ u₁ = s * f.1 + (1 - s) * d.1 ∧
          u₂ = s * f.2 + (1 - s) * d.2) := by
  intro S f d
  have hgain : M.joint hd ≤ M.joint ho := hopt.2 hd hd0
  simp only [joint] at hgain
  simp only [f, d, S]
  refine ⟨by ring, by ring, ?_⟩
  constructor
  · rintro ⟨hs, h1, h2⟩
    rcases eq_or_lt_of_le hgain with heq | hlt
    · refine ⟨1, zero_le_one, le_rfl, by linarith, by linarith⟩
    · refine ⟨(M.φ₁ ho + M.φ₂ ho - M.φ₂ hd + w₁ - u₁) /
          (M.φ₁ ho + M.φ₂ ho - (M.φ₁ hd + M.φ₂ hd)), ?_, ?_, ?_, ?_⟩
      · exact div_nonneg (by linarith) (by linarith)
      · rw [div_le_one (by linarith)]
        linarith
      · field_simp
        ring
      · rw [show u₂ = M.φ₁ ho + M.φ₂ ho + w₁ + w₂ - u₁ by linarith]
        field_simp
        ring
  · rintro ⟨s, hs0, hs1, h1, h2⟩
    refine ⟨by rw [h1, h2]; ring, ?_, ?_⟩
    · rw [h1]; nlinarith
    · rw [h2]; nlinarith

/-- **Small type, p. 358.** If the two agents are firms and one buys the other, the merged firm
maximizes `π₁ + π₂` and so chooses exactly the optimal levels. -/
theorem merger_internalizes (h : ℝ) :
    (0 ≤ h ∧ ∀ y, 0 ≤ y → M.φ₁ y + M.φ₂ y ≤ M.φ₁ h + M.φ₂ h) ↔ M.IsOptLevel h :=
  Iff.rfl

/-! ## Externalities and missing markets -/

/-- **(11.B.6)** (MWG, p. 358). Consumer 1's demand for rights at price `p_h`: `h₁` maximizes
`φ₁(h₁) - p_h h₁` on `ℝ₊` iff `φ₁'(h₁) ≤ p_h`, with equality if `h₁ > 0`. -/
theorem eq_11_B_6 (p h : ℝ) : M.IsTaxChoice p h ↔ IsFOCSol M.d₁ p h := M.eq_11_B_4 p h

/-- Consumer 2's supply of rights at price `p_h`: `h₂` maximizes `φ₂(h₂) + p_h h₂` on `ℝ₊`. -/
def IsRightsSupply (p h : ℝ) : Prop := 0 ≤ h ∧ ∀ y, 0 ≤ y → M.φ₂ y + p * y ≤ M.φ₂ h + p * h

/-- **(11.B.7)** (MWG, p. 358). `h₂` is consumer 2's supply iff `φ₂'(h₂) ≤ -p_h`, with equality
if `h₂ > 0`. -/
theorem eq_11_B_7 (p h : ℝ) : M.IsRightsSupply p h ↔ IsFOCSol M.d₂ (-p) h := by
  have hf : ∀ x, HasDerivAt (fun h => M.φ₂ h + p * h) (M.d₂ x + p) x := fun x => by
    have h2 : HasDerivAt (fun y => p * y) p x := by simpa using (hasDerivAt_id x).const_mul p
    exact (M.hd₂ x).add h2
  have hanti : AntitoneOn (fun x => M.d₂ x + p) (Set.Ici 0) :=
    fun a ha b hb hab => by simpa using M.anti₂.antitoneOn ha hb hab
  rw [IsRightsSupply, kt_isMax_iff hf hanti]
  simp only [IsFOCSol]
  constructor
  · rintro ⟨h0, h1, h2⟩
    exact ⟨h0, by linarith, fun hp => by linarith [h2 hp]⟩
  · rintro ⟨h0, h1, h2⟩
    exact ⟨h0, by linarith, fun hp => by linarith [h2 hp]⟩

/-- A competitive equilibrium of the market for rights: price `p` and a traded quantity `h`
that is both consumer 1's demand and consumer 2's supply (market clearing `h₁ = h₂`). -/
def IsRightsEquilibrium (p h : ℝ) : Prop := M.IsTaxChoice p h ∧ M.IsRightsSupply p h

/-- **The rights market is efficient** (MWG, p. 359): the equilibrium quantity `h**` satisfies
(11.B.2), so `h** = h°`; and if `h** > 0` the price is `p_h* = φ₁'(h°) = -φ₂'(h°)`. -/
theorem rights_equilibrium_optimal {p h : ℝ} (he : M.IsRightsEquilibrium p h) :
    M.IsOptLevel h ∧ (0 < h → p = M.d₁ h ∧ p = -M.d₂ h) := by
  have h1 := (M.eq_11_B_6 p h).1 he.1
  have h2 := (M.eq_11_B_7 p h).1 he.2
  refine ⟨(M.eq_11_B_2 h).2 ⟨h1.1, by linarith [h1.2.1, h2.2.1], fun hp => ?_⟩, fun hp => ?_⟩
  · linarith [h1.2.2 hp, h2.2.2 hp]
  · exact ⟨(h1.2.2 hp).symm, by linarith [h2.2.2 hp]⟩

/-- **Existence of the efficient rights equilibrium** (MWG, p. 359): at the optimal level `h°`,
the price `p_h* = φ₁'(h°)` clears the market. Utilities are `φ₁(h°) - p_h* h°` and
`φ₂(h°) + p_h* h°`, a point on the frontier (point `g` of Figure 11.B.3). -/
theorem rights_equilibrium_exists {ho : ℝ} (hopt : M.IsOptLevel ho) :
    M.IsRightsEquilibrium (M.d₁ ho) ho ∧
      (M.φ₁ ho - M.d₁ ho * ho) + (M.φ₂ ho + M.d₁ ho * ho) = M.joint ho := by
  rw [eq_11_B_2] at hopt
  refine ⟨⟨(M.eq_11_B_6 _ _).2 ⟨hopt.1, le_rfl, fun _ => rfl⟩,
    (M.eq_11_B_7 _ _).2 ⟨hopt.1, by linarith [hopt.2.1], fun hp => by linarith [hopt.2.2 hp]⟩⟩,
    by simp only [joint]; ring⟩

/-! ## A concrete instance -/

/-- The instance `φ₁(h) = 4h - h²/2`, `φ₂(h) = -h - h²/2` (a negative externality). -/
noncomputable def ex : Bilateral where
  φ₁ h := 4 * h - h ^ 2 / 2
  φ₂ h := -h - h ^ 2 / 2
  d₁ h := 4 - h
  d₂ h := -1 - h
  hd₁ h := by
    have h' := ((hasDerivAt_id h).const_mul 4).sub ((hasDerivAt_pow 2 h).div_const 2)
    exact (h'.congr_deriv (by simp only [Nat.cast_ofNat]; ring) :
      HasDerivAt (fun h : ℝ => 4 * h - h ^ 2 / 2) (4 - h) h)
  hd₂ h := by
    have h' := (hasDerivAt_id h).neg.sub ((hasDerivAt_pow 2 h).div_const 2)
    exact (h'.congr_deriv (by simp only [Nat.cast_ofNat]; ring) :
      HasDerivAt (fun h : ℝ => -h - h ^ 2 / 2) (-1 - h) h)
  anti₁ _ _ _ _ hab := by linarith
  anti₂ _ _ _ _ hab := by linarith

/-- In the instance, `h* = 4`, `h° = 3/2`, the Pigouvian tax is `5/2`, and consumer 2's
take-it-or-leave-it offer is `(3/2, 39/8)`. -/
theorem ex_values :
    ex.IsEqLevel 4 ∧ ex.IsOptLevel (3 / 2) ∧ ex.IsTaxChoice (5 / 2) (3 / 2) ∧
      ex.IsOffer2Free (3 / 2) (39 / 8) ∧ ex.IsRightsEquilibrium (5 / 2) (3 / 2) := by
  have he : ex.IsEqLevel 4 := (ex.eq_11_B_1 4).2 ⟨by norm_num, by simp [ex], fun _ => by simp [ex]⟩
  have ho : ex.IsOptLevel (3 / 2) :=
    (ex.eq_11_B_2 _).2 ⟨by norm_num, by simp [ex]; norm_num, fun _ => by simp [ex]; norm_num⟩
  have ht := ex.pigou_tax ho
  have hd : -ex.d₂ (3 / 2) = 5 / 2 := by simp [ex]; norm_num
  rw [hd] at ht
  refine ⟨he, ho, ht, (ex.eq_11_B_5 _ _).2 ⟨ho, by simp [ex]; norm_num⟩, ?_⟩
  have := (ex.rights_equilibrium_exists ho).1
  have hd1 : ex.d₁ (3 / 2) = 5 / 2 := by simp [ex]; norm_num
  rwa [hd1] at this

end Bilateral

end MWG.ExternalitiesPublicGoods

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Public goods (MWG Section 11.C)

MWG, pp. 359-364, and Exercises 11.C.1-11.C.2 (p. 379).

* **Definition 11.C.1** and the depletable/nondepletable distinction (`DepletableFeasible`,
  `NondepletableFeasible`), footnote 9 (pure public goods).
* The model `PublicGood ι`: `I` consumers with derived utilities `φᵢ(q)` (strictly decreasing
  `φᵢ'`) and a cost `c(q)` with strictly increasing `c'` (MWG: `φᵢ'' < 0`, `c'' > 0`).
* Pareto optimality (footnote 4 / Section 10.D: `pareto_iff_optimal`) and the **Samuelson
  condition (11.C.1)** (`eq_11_C_1`).
* Private provision: (11.C.2)-(11.C.4) (`consumer_foc`, `firm_foc`), (11.C.5), `q* < q°` and
  footnote 10 (also for a public bad), the stark free-rider result.
* Corrective subsidies for consumers (p. 363; **Exercise 11.C.1**) and a subsidy on the firm's
  output (**Exercise 11.C.2**): one model of equilibrium with consumer subsidies `sᵢ` and an
  output subsidy `σ` (`IsSubsidyEq`) covers all three.
* **Lindahl equilibrium**: (11.C.6)-(11.C.8), `q** = q°`, existence with prices `φᵢ'(q°)`;
  footnote 11 (exclusion is inefficient at a Pareto optimum).
* A concrete instance: `φᵢ(q) = -aᵢ e^{-q}`, `c(q) = e^q`, `a = (1, 3)`: `q° = log 2`,
  `q* = (log 3)/2`, Lindahl prices `(1/2, 3/2)`.
-/

namespace MWG.ExternalitiesPublicGoods

open MWG.CompetitiveMarkets

/-! ## Definition 11.C.1 -/

/-- Feasible consumptions of a private (depletable) good: `∑ xᵢ ≤ q`. -/
def DepletableFeasible {ι : Type*} [Fintype ι] (q : ℝ) (x : ι → ℝ) : Prop :=
  (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ q

/-- **Definition 11.C.1** (MWG, p. 359). Feasible consumptions of a public (nondepletable) good:
each consumer can use the whole amount, `xᵢ ≤ q` for all `i`. -/
def NondepletableFeasible {ι : Type*} (q : ℝ) (x : ι → ℝ) : Prop :=
  (∀ i, 0 ≤ x i) ∧ ∀ i, x i ≤ q

/-- **Definition 11.C.1** (MWG, p. 359), unfolded. -/
theorem definition_11_C_1 {ι : Type*} (q : ℝ) (x : ι → ℝ) :
    NondepletableFeasible q x ↔ (∀ i, 0 ≤ x i) ∧ ∀ i, x i ≤ q := Iff.rfl

/-- **Definition 11.C.1** (MWG, p. 359): use of a public good by one agent does not preclude its
use by others. Any consumer can raise her use to the whole amount `q` while the others keep
theirs. -/
theorem nondepletable_not_preclude {ι : Type*} [DecidableEq ι] {q : ℝ} {x : ι → ℝ}
    (hx : NondepletableFeasible q x) (hq : 0 ≤ q) (i : ι) :
    NondepletableFeasible q (Function.update x i q) := by
  refine ⟨fun j => ?_, fun j => ?_⟩
  · rcases eq_or_ne j i with h | h
    · rw [h, Function.update_self]; exact hq
    · rw [Function.update_of_ne h]; exact hx.1 j
  · rcases eq_or_ne j i with h | h
    · rw [h, Function.update_self]
    · rw [Function.update_of_ne h]; exact hx.2 j

/-- For a private good (p. 360), each unit consumed by `i` is one unit less for the others: if
`i` consumes all of `q`, every other consumer gets nothing. -/
theorem depletable_precludes {ι : Type*} [Fintype ι] {q : ℝ} {x : ι → ℝ}
    (hx : DepletableFeasible q x) {i : ι} (hi : x i = q) (j : ι) (hj : j ≠ i) : x j = 0 := by
  classical
  have hsum : x i + x j ≤ ∑ k, x k := by
    rw [← Finset.sum_pair hj.symm]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun k _ _ => hx.1 k)
  exact le_antisymm (by linarith [hx.2]) (hx.1 j)

/-- **Footnote 9** (MWG, p. 360). Every depletable-feasible profile is nondepletable-feasible:
the public good imposes weakly fewer constraints (a pure public good has no depletability). -/
theorem depletable_imp_nondepletable {ι : Type*} [Fintype ι] {q : ℝ} {x : ι → ℝ}
    (hx : DepletableFeasible q x) : NondepletableFeasible q x := by
  classical
  refine ⟨hx.1, fun i => le_trans ?_ hx.2⟩
  exact Finset.single_le_sum (fun k _ => hx.1 k) (Finset.mem_univ i)

/-! ## The model -/

/-- **The public good model** (MWG, p. 360). Consumers `i ∈ ι` with derived utilities `φᵢ(q) + wᵢ`
and a cost `c(q)` of supplying the public good. -/
structure PublicGood (ι : Type*) where
  /-- Consumer `i`'s derived utility from the public good. -/
  φ : ι → ℝ → ℝ
  /-- `φᵢ'`. -/
  dφ : ι → ℝ → ℝ
  /-- The cost function. -/
  c : ℝ → ℝ
  /-- `c'`. -/
  dc : ℝ → ℝ
  hφ : ∀ i x, HasDerivAt (φ i) (dφ i x) x
  hc : ∀ x, HasDerivAt c (dc x) x
  antiφ : ∀ i, StrictAntiOn (dφ i) (Set.Ici 0)
  monoc : StrictMonoOn dc (Set.Ici 0)

namespace PublicGood

variable {ι : Type*} [Fintype ι] (G : PublicGood ι)

/-- The aggregate surplus `∑ᵢ φᵢ(q) - c(q)`. -/
def surplus (q : ℝ) : ℝ := ∑ i, G.φ i q - G.c q

/-- The marginal social surplus `∑ᵢ φᵢ'(q) - c'(q)`. -/
def msurplus (q : ℝ) : ℝ := ∑ i, G.dφ i q - G.dc q

theorem hasDerivAt_surplus (q : ℝ) : HasDerivAt G.surplus (G.msurplus q) q :=
  (HasDerivAt.fun_sum fun i _ => G.hφ i q).sub (G.hc q)

theorem anti_msurplus : StrictAntiOn G.msurplus (Set.Ici 0) := by
  intro a ha b hb hab
  have h1 : ∑ i, G.dφ i b ≤ ∑ i, G.dφ i a :=
    Finset.sum_le_sum fun i _ => (G.antiφ i ha hb hab).le
  have h2 := G.monoc ha hb hab
  simp only [msurplus]
  linarith

/-- The optimal level `q°`: it maximizes the aggregate surplus on `ℝ₊`. -/
def IsOptimal (q : ℝ) : Prop := 0 ≤ q ∧ ∀ y, 0 ≤ y → G.surplus y ≤ G.surplus q

/-- **Pareto optimality** (MWG, p. 360, via Section 10.D). With utilities `φᵢ(q) + mᵢ` and
`∑ mᵢ = W - c(q)`, an allocation is Pareto optimal iff its level of the public good is optimal. -/
theorem pareto_iff_optimal [Nonempty ι] (W : ℝ) (a : QLAlloc ι ℝ)
    (ha : QLFeasible (Set.Ici 0) G.c W a) :
    QLPareto G.φ (Set.Ici 0) G.c W a ↔ G.IsOptimal a.x := by
  rw [ql_pareto_iff _ _ _ _ a ha]
  exact ⟨fun h => ⟨ha.1, fun y hy => h y hy⟩, fun h y hy => h.2 y hy⟩

/-- **The Samuelson condition (11.C.1)** (MWG, p. 360). `q°` is optimal iff
`∑ᵢ φᵢ'(q°) ≤ c'(q°)`, with equality if `q° > 0`. -/
theorem eq_11_C_1 (q : ℝ) :
    G.IsOptimal q ↔ 0 ≤ q ∧ ∑ i, G.dφ i q ≤ G.dc q ∧ (0 < q → ∑ i, G.dφ i q = G.dc q) := by
  rw [IsOptimal, kt_isMax_iff G.hasDerivAt_surplus G.anti_msurplus.antitoneOn]
  simp only [IsFOCSol, msurplus]
  constructor
  · rintro ⟨h0, h1, h2⟩
    exact ⟨h0, by linarith, fun hp => by linarith [h2 hp]⟩
  · rintro ⟨h0, h1, h2⟩
    exact ⟨h0, by linarith, fun hp => by linarith [h2 hp]⟩

/-- The optimal level is unique. -/
theorem optimal_unique {q q' : ℝ} (hq : G.IsOptimal q) (hq' : G.IsOptimal q') : q = q' :=
  kt_max_unique G.hasDerivAt_surplus G.anti_msurplus hq.1 hq.2 hq'.1 hq'.2

/-! ## Equilibrium with subsidies: private provision, Exercises 11.C.1-11.C.2 -/

/-- Consumer `i`'s problem (11.C.2), with a per-unit subsidy `s`: given the others' purchases `R`,
`xᵢ ≥ 0` maximizes `φᵢ(xᵢ + R) + s xᵢ - p xᵢ`. -/
def IsConsumerChoice (i : ι) (s p R x : ℝ) : Prop :=
  0 ≤ x ∧ ∀ y, 0 ≤ y → G.φ i (y + R) + s * y - p * y ≤ G.φ i (x + R) + s * x - p * x

omit [Fintype ι] in
/-- **(11.C.3)** (MWG, p. 361). Given others' purchases `R ≥ 0`, consumer `i`'s choice `x` is
optimal iff `φᵢ'(x + R) + s ≤ p`, with equality if `x > 0`. -/
theorem consumer_foc (i : ι) (s p R x : ℝ) (hR : 0 ≤ R) :
    G.IsConsumerChoice i s p R x ↔
      0 ≤ x ∧ G.dφ i (x + R) + s ≤ p ∧ (0 < x → G.dφ i (x + R) + s = p) := by
  have hf : ∀ y, HasDerivAt (fun y => G.φ i (y + R) + s * y - p * y)
      (G.dφ i (y + R) + s - p) y := fun y => by
    have h1 : HasDerivAt (fun y => G.φ i (y + R)) (G.dφ i (y + R)) y :=
      (G.hφ i (y + R)).comp_add_const y R
    have h2 : HasDerivAt (fun y => s * y) s y := by simpa using (hasDerivAt_id y).const_mul s
    have h3 : HasDerivAt (fun y => p * y) p y := by simpa using (hasDerivAt_id y).const_mul p
    exact (h1.add h2).sub h3
  have hanti : AntitoneOn (fun y => G.dφ i (y + R) + s - p) (Set.Ici 0) := by
    intro a ha b hb hab
    have := (G.antiφ i).antitoneOn (show 0 ≤ a + R by linarith [ha.out])
      (show 0 ≤ b + R by linarith [hb.out]) (by linarith)
    simp only
    linarith
  rw [IsConsumerChoice, kt_isMax_iff hf hanti]
  simp only [IsFOCSol]
  constructor
  · rintro ⟨h0, h1, h2⟩
    exact ⟨h0, by linarith, fun hp => by linarith [h2 hp]⟩
  · rintro ⟨h0, h1, h2⟩
    exact ⟨h0, by linarith, fun hp => by linarith [h2 hp]⟩

/-- The firm's problem with a per-unit output subsidy `σ`: `q ≥ 0` maximizes
`(p + σ) q - c(q)`. -/
def IsFirmChoice (σ p q : ℝ) : Prop :=
  0 ≤ q ∧ ∀ y, 0 ≤ y → (p + σ) * y - G.c y ≤ (p + σ) * q - G.c q

omit [Fintype ι] in
/-- **(11.C.4)** (MWG, p. 361). The firm's supply `q` is optimal iff `p + σ ≤ c'(q)`, with
equality if `q > 0`. -/
theorem firm_foc (σ p q : ℝ) :
    G.IsFirmChoice σ p q ↔ 0 ≤ q ∧ p + σ ≤ G.dc q ∧ (0 < q → p + σ = G.dc q) := by
  have hf : ∀ y, HasDerivAt (fun y => (p + σ) * y - G.c y) (p + σ - G.dc y) y := fun y => by
    have h2 : HasDerivAt (fun y => (p + σ) * y) (p + σ) y := by
      simpa using (hasDerivAt_id y).const_mul (p + σ)
    exact h2.sub (G.hc y)
  have hanti : AntitoneOn (fun y => p + σ - G.dc y) (Set.Ici 0) := by
    intro a ha b hb hab
    have := G.monoc.monotoneOn ha hb hab
    simp only
    linarith
  rw [IsFirmChoice, kt_isMax_iff hf hanti]
  simp only [IsFOCSol]
  constructor
  · rintro ⟨h0, h1, h2⟩
    exact ⟨h0, by linarith, fun hp => by linarith [h2 hp]⟩
  · rintro ⟨h0, h1, h2⟩
    exact ⟨h0, by linarith, fun hp => by linarith [h2 hp]⟩

/-- A competitive equilibrium of private provision with consumer subsidies `sᵢ` and an output
subsidy `σ` (MWG, pp. 361-363): purchases `xᵢ`, price `p`, output `q`; each consumer takes the
others' purchases as given (11.C.2), the firm maximizes profit, and `q = ∑ xᵢ`. -/
def IsSubsidyEq (s : ι → ℝ) (σ : ℝ) (x : ι → ℝ) (p q : ℝ) : Prop :=
  (∀ i, G.IsConsumerChoice i (s i) p (q - x i) (x i)) ∧ G.IsFirmChoice σ p q ∧ q = ∑ i, x i

/-- The unsubsidized private-provision equilibrium. -/
def IsPrivateEq (x : ι → ℝ) (p q : ℝ) : Prop := G.IsSubsidyEq (fun _ => 0) 0 x p q

theorem others_nonneg {x : ι → ℝ} (hx : ∀ i, 0 ≤ x i) (i : ι) :
    0 ≤ (∑ j, x j) - x i := by
  classical
  have := Finset.single_le_sum (fun k _ => hx k) (Finset.mem_univ i)
  linarith

/-- The equilibrium conditions in first-order form: `φᵢ'(q) + sᵢ ≤ p` (equality if `xᵢ > 0`),
`p + σ ≤ c'(q)` (equality if `q > 0`), `xᵢ ≥ 0`, `q = ∑ xᵢ`. -/
theorem subsidyEq_iff (s : ι → ℝ) (σ : ℝ) (x : ι → ℝ) (p q : ℝ) :
    G.IsSubsidyEq s σ x p q ↔
      (∀ i, 0 ≤ x i ∧ G.dφ i q + s i ≤ p ∧ (0 < x i → G.dφ i q + s i = p)) ∧
        (p + σ ≤ G.dc q ∧ (0 < q → p + σ = G.dc q)) ∧ q = ∑ i, x i := by
  constructor
  · rintro ⟨hc, hf, hq⟩
    have hx : ∀ i, 0 ≤ x i := fun i => (hc i).1
    refine ⟨fun i => ?_, ((G.firm_foc σ p q).1 hf).2, hq⟩
    have hR : 0 ≤ q - x i := by rw [hq]; exact others_nonneg hx i
    have := (G.consumer_foc i (s i) p (q - x i) (x i) hR).1 (hc i)
    simpa only [add_sub_cancel] using this
  · rintro ⟨hc, hf, hq⟩
    have hx : ∀ i, 0 ≤ x i := fun i => (hc i).1
    have hq0 : 0 ≤ q := by rw [hq]; exact Finset.sum_nonneg fun i _ => hx i
    refine ⟨fun i => ?_, (G.firm_foc σ p q).2 ⟨hq0, hf⟩, hq⟩
    have hR : 0 ≤ q - x i := by rw [hq]; exact others_nonneg hx i
    rw [G.consumer_foc i (s i) p (q - x i) (x i) hR]
    simpa only [add_sub_cancel] using hc i

/-- **(11.C.3)-(11.C.4)** (MWG, p. 361). At a private-provision equilibrium,
`φᵢ'(x*) ≤ p*` with equality if `xᵢ* > 0`, and `p* ≤ c'(q*)` with equality if `q* > 0`. -/
theorem eq_11_C_3_4 {x : ι → ℝ} {p q : ℝ} (he : G.IsPrivateEq x p q) :
    (∀ i, G.dφ i q ≤ p ∧ (0 < x i → G.dφ i q = p)) ∧ p ≤ G.dc q ∧ (0 < q → p = G.dc q) := by
  obtain ⟨hc, hf, -⟩ := (G.subsidyEq_iff _ _ x p q).1 he
  refine ⟨fun i => ⟨by simpa using (hc i).2.1, fun h => by simpa using (hc i).2.2 h⟩,
    by simpa using hf.1, fun h => by simpa using hf.2 h⟩

/-- **(11.C.5)** (MWG, p. 361). If the public good is desirable (`φᵢ' > 0`), there are at least
two consumers and `q* > 0`, then `∑ᵢ φᵢ'(q*) > c'(q*)`. -/
theorem eq_11_C_5 {x : ι → ℝ} {p q : ℝ} (he : G.IsPrivateEq x p q)
    (hdes : ∀ i y, 0 ≤ y → 0 < G.dφ i y) (hI : ∃ i j : ι, i ≠ j) (hq : 0 < q) :
    G.dc q < ∑ i, G.dφ i q := by
  classical
  obtain ⟨hc, hf, hsum⟩ := (G.subsidyEq_iff _ _ x p q).1 he
  have hq0 : 0 ≤ q := hq.le
  obtain ⟨i, hi⟩ : ∃ i, 0 < x i := by
    by_contra hno
    push Not at hno
    have : ∑ i, x i ≤ 0 := Finset.sum_nonpos fun i _ => hno i
    linarith
  have hpi : G.dφ i q = p := by simpa using (hc i).2.2 hi
  have hpc : p = G.dc q := by simpa using hf.2 hq
  obtain ⟨j₁, j₂, hj⟩ := hI
  obtain ⟨j, hji⟩ : ∃ j, j ≠ i := by
    by_cases h : j₁ = i
    · exact ⟨j₂, fun h' => hj (h.trans h'.symm)⟩
    · exact ⟨j₁, h⟩
  have h2 : G.dφ i q + G.dφ j q ≤ ∑ k, G.dφ k q := by
    rw [← Finset.sum_pair (f := fun k => G.dφ k q) hji.symm]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun k _ _ => (hdes k q hq0).le)
  have := hdes j q hq0
  linarith

/-- **Underprovision** (MWG, p. 362, footnote 10). With a desirable public good (`φᵢ' > 0`,
`c' > 0`), at least two consumers and `q° > 0`, the private-provision level is too low:
`q* < q°`. -/
theorem underprovision {x : ι → ℝ} {p q qo : ℝ} (he : G.IsPrivateEq x p q)
    (ho : G.IsOptimal qo) (hdes : ∀ i y, 0 ≤ y → 0 < G.dφ i y) (hI : ∃ i j : ι, i ≠ j)
    (hqo : 0 < qo) : q < qo := by
  obtain ⟨hc, hf, hsum⟩ := (G.subsidyEq_iff _ _ x p q).1 he
  have hq0 : 0 ≤ q := by rw [hsum]; exact Finset.sum_nonneg fun i _ => (hc i).1
  rcases eq_or_lt_of_le hq0 with h0 | hpos
  · rw [← h0]; exact hqo
  · have h5 := G.eq_11_C_5 he hdes hI hpos
    by_contra hle
    push Not at hle
    have hopt := (G.eq_11_C_1 qo).1 ho
    rcases eq_or_lt_of_le hle with heq | hlt
    · rw [← heq] at h5; linarith [hopt.2.2 hqo]
    · have := G.anti_msurplus ho.1 hq0 hlt
      simp only [msurplus] at this
      linarith [hopt.2.2 hqo]

/-- **Footnote 10, public bad** (MWG, p. 362). If `φᵢ' < 0` and `c' < 0` (a public bad whose
reduction is costly), there are at least two consumers and `q* > 0`, the inequalities reverse:
`q° < q*`. (For `q* = 0` no reversal is possible, since `q° ≥ 0`.) -/
theorem public_bad_excess {x : ι → ℝ} {p q qo : ℝ} (he : G.IsPrivateEq x p q)
    (ho : G.IsOptimal qo) (hbad : ∀ i y, 0 ≤ y → G.dφ i y < 0) (hI : ∃ i j : ι, i ≠ j)
    (hq : 0 < q) : qo < q := by
  classical
  obtain ⟨hc, hf, hsum⟩ := (G.subsidyEq_iff _ _ x p q).1 he
  obtain ⟨i, hi⟩ : ∃ i, 0 < x i := by
    by_contra hno
    push Not at hno
    have : ∑ i, x i ≤ 0 := Finset.sum_nonpos fun i _ => hno i
    linarith
  have hpi : G.dφ i q = p := by simpa using (hc i).2.2 hi
  have hpc : p = G.dc q := by simpa using hf.2 hq
  obtain ⟨j₁, j₂, hj⟩ := hI
  obtain ⟨j, hji⟩ : ∃ j, j ≠ i := by
    by_cases h : j₁ = i
    · exact ⟨j₂, fun h' => hj (h.trans h'.symm)⟩
    · exact ⟨j₁, h⟩
  have h2 : ∑ k, G.dφ k q ≤ G.dφ i q + G.dφ j q := by
    rw [← Finset.sum_pair (f := fun k => G.dφ k q) hji.symm]
    exact Finset.sum_le_sum_of_subset_of_nonpos (Finset.subset_univ _)
      (fun k _ _ => (hbad k q hq.le).le)
  have hj' := hbad j q hq.le
  have hlt : ∑ k, G.dφ k q < G.dc q := by linarith
  by_contra hle
  push Not at hle
  have hopt := (G.eq_11_C_1 qo).1 ho
  rcases eq_or_lt_of_le hle with heq | hlt'
  · rw [heq] at hlt; linarith [hopt.2.2 (heq ▸ hq)]
  · have := G.anti_msurplus hq.le ho.1 hlt'
    simp only [msurplus] at this
    linarith [hopt.2.2 (hq.trans hlt')]

/-- **The stark free-rider problem** (MWG, p. 362). If the consumers are ordered by marginal
benefit, `φ₁'(x) < ⋯ < φ_I'(x)` at all `x ≥ 0`, only consumer `I` can purchase a positive amount in
equilibrium, and the equilibrium level satisfies `φ_I'(q*) = c'(q*)` if `q* > 0`. -/
theorem stark_free_rider {n : ℕ} (G : PublicGood (Fin (n + 1))) {x : Fin (n + 1) → ℝ}
    {p q : ℝ} (he : G.IsPrivateEq x p q)
    (hord : ∀ i j : Fin (n + 1), i < j → ∀ y, 0 ≤ y → G.dφ i y < G.dφ j y) :
    (∀ i, 0 < x i → i = Fin.last n) ∧ (0 < q → G.dφ (Fin.last n) q = G.dc q) := by
  obtain ⟨hc, hf, hsum⟩ := (G.subsidyEq_iff _ _ x p q).1 he
  have hq0 : 0 ≤ q := by rw [hsum]; exact Finset.sum_nonneg fun i _ => (hc i).1
  have hbuy : ∀ i, 0 < x i → i = Fin.last n := by
    intro i hi
    by_contra hne
    have hlt : i < Fin.last n := lt_of_le_of_ne (Fin.le_last i) hne
    have h1 : G.dφ i q = p := by simpa using (hc i).2.2 hi
    have h2 : G.dφ (Fin.last n) q ≤ p := by simpa using (hc (Fin.last n)).2.1
    have := hord i (Fin.last n) hlt q hq0
    linarith
  refine ⟨hbuy, fun hq => ?_⟩
  have hxl : 0 < x (Fin.last n) := by
    by_contra hle
    push Not at hle
    have : ∑ i, x i ≤ 0 := Finset.sum_nonpos fun i _ => by
      rcases eq_or_ne i (Fin.last n) with h | h
      · rw [h]; exact hle
      · exact le_of_not_gt fun hi => h (hbuy i hi)
    linarith
  have h1 : G.dφ (Fin.last n) q = p := by simpa using (hc (Fin.last n)).2.2 hxl
  have h2 : p = G.dc q := by simpa using hf.2 hq
  rw [h1, h2]

/-- **Corrective subsidies** (MWG, pp. 362-363; **Exercise 11.C.1**, p. 379). With consumer
subsidies `sᵢ = ∑_{j ≠ i} φⱼ'(q°)`, the total amount of the public good in any equilibrium is
`q°`. -/
theorem exercise_11_C_1 [Nonempty ι] {qo : ℝ} (ho : G.IsOptimal qo) {x : ι → ℝ} {p q : ℝ}
    (he : G.IsSubsidyEq (fun i => ∑ j, G.dφ j qo - G.dφ i qo) 0 x p q) : q = qo := by
  classical
  obtain ⟨hc, hf, hsum⟩ := (G.subsidyEq_iff _ _ x p q).1 he
  have hopt := (G.eq_11_C_1 qo).1 ho
  have hq0 : 0 ≤ q := by rw [hsum]; exact Finset.sum_nonneg fun i _ => (hc i).1
  simp only [add_zero] at hf
  rcases eq_or_lt_of_le hq0 with h0 | hpos
  · -- `q = 0`
    rcases eq_or_lt_of_le ho.1 with h0' | hqo
    · rw [← h0, ← h0']
    · exfalso
      obtain ⟨i⟩ := ‹Nonempty ι›
      have h1 := (hc i).2.1
      rw [← h0] at h1 hf
      have h2 := (G.antiφ i) (le_refl (0 : ℝ)) ho.1 hqo
      have h3 := G.monoc (le_refl (0 : ℝ)) ho.1 hqo
      linarith [hopt.2.2 hqo, hf.1]
  · obtain ⟨i, hi⟩ : ∃ i, 0 < x i := by
      by_contra hno
      push Not at hno
      have : ∑ i, x i ≤ 0 := Finset.sum_nonpos fun i _ => hno i
      linarith
    have hpi := (hc i).2.2 hi
    have hpc := hf.2 hpos
    rcases lt_trichotomy q qo with hlt | heq | hgt
    · exfalso
      have h2 := (G.antiφ i) hq0 ho.1 hlt
      have h3 := G.monoc hq0 ho.1 hlt
      linarith [hopt.2.2 (hpos.trans hlt)]
    · exact heq
    · exfalso
      have h2 := (G.antiφ i) ho.1 hq0 hgt
      have h3 := G.monoc ho.1 hq0 hgt
      linarith [hopt.2.1]

/-- **Exercise 11.C.1**, existence: the corrective subsidies support an equilibrium at `q°`
(consumer `i₀` buys `q°` at price `c'(q°)`). -/
theorem exercise_11_C_1_exists [DecidableEq ι] {qo : ℝ} (ho : G.IsOptimal qo) (i₀ : ι) :
    G.IsSubsidyEq (fun i => ∑ j, G.dφ j qo - G.dφ i qo) 0 (Pi.single i₀ qo) (G.dc qo) qo := by
  have hopt := (G.eq_11_C_1 qo).1 ho
  rw [subsidyEq_iff]
  refine ⟨fun i => ⟨?_, by linarith [hopt.2.1], fun hi => ?_⟩, ⟨by simp, fun _ => by simp⟩,
    by simp⟩
  · rcases eq_or_ne i i₀ with h | h
    · rw [h, Pi.single_eq_same]; exact ho.1
    · rw [Pi.single_eq_of_ne h]
  · have hpos : 0 < qo := by
      rcases eq_or_ne i i₀ with h | h
      · rw [h, Pi.single_eq_same] at hi; exact hi
      · rw [Pi.single_eq_of_ne h] at hi; exact absurd hi (lt_irrefl 0)
    linarith [hopt.2.2 hpos]

/-- **Exercise 11.C.2** (MWG, p. 379). A per-unit subsidy on the firm's output also restores
efficiency: with `q° > 0` and `i₀` a consumer with the largest marginal benefit at `q°`, the
output subsidy `σ = ∑ᵢ φᵢ'(q°) - φ_{i₀}'(q°)` makes `q°` the total in every equilibrium. -/
theorem exercise_11_C_2 [Nonempty ι] {qo : ℝ} (ho : G.IsOptimal qo) (hqo : 0 < qo) (i₀ : ι)
    (hi₀ : ∀ k, G.dφ k qo ≤ G.dφ i₀ qo) {x : ι → ℝ} {p q : ℝ}
    (he : G.IsSubsidyEq (fun _ => 0) (∑ j, G.dφ j qo - G.dφ i₀ qo) x p q) : q = qo := by
  obtain ⟨hc, hf, hsum⟩ := (G.subsidyEq_iff _ _ x p q).1 he
  have hopt := (G.eq_11_C_1 qo).1 ho
  have hS := hopt.2.2 hqo
  have hq0 : 0 ≤ q := by rw [hsum]; exact Finset.sum_nonneg fun i _ => (hc i).1
  simp only [add_zero] at hc
  rcases eq_or_lt_of_le hq0 with h0 | hpos
  · exfalso
    have h1 := (hc i₀).2.1
    rw [← h0] at h1 hf
    have h2 := (G.antiφ i₀) (le_refl (0 : ℝ)) ho.1 hqo
    have h3 := G.monoc (le_refl (0 : ℝ)) ho.1 hqo
    linarith [hf.1]
  · obtain ⟨i, hi⟩ : ∃ i, 0 < x i := by
      by_contra hno
      push Not at hno
      have : ∑ i, x i ≤ 0 := Finset.sum_nonpos fun i _ => hno i
      linarith
    have hpi := (hc i).2.2 hi
    have hpc := hf.2 hpos
    rcases lt_trichotomy q qo with hlt | heq | hgt
    · exfalso
      have h1 := (hc i₀).2.1
      have h2 := (G.antiφ i₀) hq0 ho.1 hlt
      have h3 := G.monoc hq0 ho.1 hlt
      linarith
    · exact heq
    · exfalso
      have h2 := (G.antiφ i) ho.1 hq0 hgt
      have h3 := G.monoc ho.1 hq0 hgt
      have := hi₀ i
      linarith

/-- **Exercise 11.C.2**, existence: under the output subsidy, consumer `i₀` buying `q°` at price
`φ_{i₀}'(q°)` is an equilibrium. -/
theorem exercise_11_C_2_exists [DecidableEq ι] {qo : ℝ} (ho : G.IsOptimal qo) (hqo : 0 < qo)
    (i₀ : ι) (hi₀ : ∀ k, G.dφ k qo ≤ G.dφ i₀ qo) :
    G.IsSubsidyEq (fun _ => 0) (∑ j, G.dφ j qo - G.dφ i₀ qo) (Pi.single i₀ qo)
      (G.dφ i₀ qo) qo := by
  have hS := ((G.eq_11_C_1 qo).1 ho).2.2 hqo
  rw [subsidyEq_iff]
  refine ⟨fun i => ⟨?_, by simpa using hi₀ i, fun hi => ?_⟩, ⟨by linarith, fun _ => by linarith⟩,
    by simp⟩
  · rcases eq_or_ne i i₀ with h | h
    · rw [h, Pi.single_eq_same]; exact ho.1
    · rw [Pi.single_eq_of_ne h]
  · rcases eq_or_ne i i₀ with h | h
    · rw [h]; simp
    · rw [Pi.single_eq_of_ne h] at hi; exact absurd hi (lt_irrefl 0)

/-! ## Lindahl equilibrium -/

/-- A **Lindahl equilibrium** (MWG, pp. 363-364): personalized prices `pᵢ`, consumptions `xᵢ`
maximizing `φᵢ(xᵢ) - pᵢ xᵢ` on `ℝ₊` (11.C.6), output `q` maximizing `(∑ pᵢ) q - c(q)` (11.C.7),
and market clearing `xᵢ = q` for all `i`. -/
def IsLindahlEq (p : ι → ℝ) (x : ι → ℝ) (q : ℝ) : Prop :=
  (∀ i, 0 ≤ x i ∧ ∀ y, 0 ≤ y → G.φ i y - p i * y ≤ G.φ i (x i) - p i * x i) ∧
    G.IsFirmChoice 0 (∑ i, p i) q ∧ ∀ i, x i = q

omit [Fintype ι] in
/-- **(11.C.6)** (MWG, p. 363). Consumer `i`'s Lindahl demand: `φᵢ'(xᵢ) ≤ pᵢ`, equality if
`xᵢ > 0`. -/
theorem eq_11_C_6 (i : ι) (pi xi : ℝ) :
    (0 ≤ xi ∧ ∀ y, 0 ≤ y → G.φ i y - pi * y ≤ G.φ i xi - pi * xi) ↔
      0 ≤ xi ∧ G.dφ i xi ≤ pi ∧ (0 < xi → G.dφ i xi = pi) := by
  have h := G.consumer_foc i 0 pi 0 xi le_rfl
  simp only [IsConsumerChoice, add_zero, zero_mul] at h
  rw [← h]

/-- **(11.C.8)** (MWG, p. 364) and **`q** = q°`**: in a Lindahl equilibrium the level of the
public good satisfies the Samuelson condition, hence is optimal. -/
theorem lindahl_optimal {p x : ι → ℝ} {q : ℝ} (he : G.IsLindahlEq p x q) : G.IsOptimal q := by
  obtain ⟨hc, hf, hclear⟩ := he
  have hf' := (G.firm_foc 0 (∑ i, p i) q).1 hf
  simp only [add_zero] at hf'
  have hci : ∀ i, G.dφ i q ≤ p i ∧ (0 < q → G.dφ i q = p i) := fun i => by
    have := (G.eq_11_C_6 i (p i) (x i)).1 (hc i)
    rw [hclear i] at this
    exact this.2
  rw [eq_11_C_1]
  refine ⟨hf'.1, (Finset.sum_le_sum fun i _ => (hci i).1).trans hf'.2.1, fun hq => ?_⟩
  rw [Finset.sum_congr rfl fun i _ => (hci i).2 hq]
  exact hf'.2.2 hq

/-- **Existence of the Lindahl equilibrium**: at `q°`, the personalized prices `pᵢ = φᵢ'(q°)`
support it. -/
theorem lindahl_exists {qo : ℝ} (ho : G.IsOptimal qo) :
    G.IsLindahlEq (fun i => G.dφ i qo) (fun _ => qo) qo := by
  have hopt := (G.eq_11_C_1 qo).1 ho
  refine ⟨fun i => (G.eq_11_C_6 i _ _).2 ⟨ho.1, le_rfl, fun _ => rfl⟩,
    (G.firm_foc 0 _ qo).2 ⟨ho.1, by simpa using hopt.2.1, fun h => by simpa using hopt.2.2 h⟩,
    fun _ => rfl⟩

omit [Fintype ι] in
/-- **Footnote 11** (MWG, p. 364). A Pareto optimal allocation involves no exclusion: if consumer
`i` is excluded from part of the public good (`xᵢ < q`) and `φᵢ` is strictly increasing, giving her
the whole amount costs nothing and makes her strictly better off. -/
theorem footnote_11 [DecidableEq ι] {q : ℝ} {x : ι → ℝ} (hx : NondepletableFeasible q x)
    (hq : 0 ≤ q) (i : ι) (hi : x i < q) (hmono : StrictMono (G.φ i)) :
    NondepletableFeasible q (Function.update x i q) ∧
      (∀ j, G.φ j (x j) ≤ G.φ j (Function.update x i q j)) ∧
      G.φ i (x i) < G.φ i (Function.update x i q i) := by
  refine ⟨nondepletable_not_preclude hx hq i, fun j => ?_, ?_⟩
  · rcases eq_or_ne j i with h | h
    · subst h; rw [Function.update_self]; exact (hmono hi).le
    · rw [Function.update_of_ne h]
  · rw [Function.update_self]; exact hmono hi

end PublicGood

/-! ## A concrete instance -/

/-- `φᵢ(q) = -aᵢ e^{-q}` with `a = (1, 3)` and `c(q) = e^q`. -/
noncomputable def pgEx : PublicGood (Fin 2) where
  φ i q := -(if i = 0 then 1 else 3) * Real.exp (-q)
  dφ i q := (if i = 0 then 1 else 3) * Real.exp (-q)
  c q := Real.exp q
  dc q := Real.exp q
  hφ i q := by
    have h := ((Real.hasDerivAt_exp (-q)).comp q (hasDerivAt_neg q)).const_mul
      (-(if i = 0 then (1 : ℝ) else 3))
    exact (h.congr_deriv (by ring) :
      HasDerivAt (fun q => -(if i = 0 then (1 : ℝ) else 3) * Real.exp (-q))
        ((if i = 0 then (1 : ℝ) else 3) * Real.exp (-q)) q)
  hc q := Real.hasDerivAt_exp q
  antiφ i a _ b _ hab := by
    have hk : (0 : ℝ) < if i = 0 then 1 else 3 := by split_ifs <;> norm_num
    have := Real.exp_lt_exp.2 (neg_lt_neg hab)
    exact mul_lt_mul_of_pos_left this hk
  monoc _ _ _ _ hab := Real.exp_lt_exp.2 hab

/-- In the instance, `q° = log 2`, Lindahl prices are `(1/2, 3/2)`, and private provision has
consumer 2 buying `q* = (log 3)/2 < q°` at price `√3`-equivalent `c'(q*)`. -/
theorem pgEx_values :
    pgEx.IsOptimal (Real.log 2) ∧ pgEx.IsLindahlEq ![1 / 2, 3 / 2] (fun _ => Real.log 2)
      (Real.log 2) ∧ pgEx.IsPrivateEq ![0, Real.log 3 / 2] (Real.exp (Real.log 3 / 2))
      (Real.log 3 / 2) ∧ Real.log 3 / 2 < Real.log 2 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have e2 : Real.exp (-Real.log 2) = 1 / 2 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  have ho : pgEx.IsOptimal (Real.log 2) := by
    rw [PublicGood.eq_11_C_1]
    simp only [pgEx, Fin.sum_univ_two, Fin.isValue, ↓reduceIte, one_ne_zero, e2,
      Real.exp_log (show (0 : ℝ) < 2 by norm_num)]
    refine ⟨hl2.le, by norm_num, fun _ => by norm_num⟩
  have hL := pgEx.lindahl_exists ho
  have hp : (fun i => pgEx.dφ i (Real.log 2)) = ![1 / 2, 3 / 2] := by
    ext i
    fin_cases i <;> norm_num [pgEx, e2]
  rw [hp] at hL
  have e3 : Real.exp (Real.log 3 / 2) * Real.exp (Real.log 3 / 2) = 3 := by
    rw [← Real.exp_add, add_halves, Real.exp_log (by norm_num)]
  have hpos3 : 0 < Real.exp (Real.log 3 / 2) := Real.exp_pos _
  have e3' : 3 * Real.exp (-(Real.log 3 / 2)) = Real.exp (Real.log 3 / 2) := by
    set a := Real.log 3 / 2
    rw [Real.exp_neg, ← e3, mul_inv_cancel_right₀ hpos3.ne']
  refine ⟨ho, hL, ?_, ?_⟩
  · rw [PublicGood.IsPrivateEq, PublicGood.subsidyEq_iff]
    refine ⟨fun i => ?_, ⟨by simp [pgEx], fun _ => by simp [pgEx]⟩, by simp⟩
    fin_cases i
    · simp only [pgEx, Fin.zero_eta, Fin.isValue, ↓reduceIte, one_mul, add_zero,
        Matrix.cons_val_zero, le_refl, lt_self_iff_false, IsEmpty.forall_iff, and_true,
        true_and]
      rw [Real.exp_le_exp]
      linarith
    · simp only [pgEx, Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte, add_zero,
        Matrix.cons_val_one, Matrix.cons_val_zero, e3', le_refl, implies_true, and_true]
      positivity
  · have : Real.log 3 < Real.log 4 := Real.log_lt_log (by norm_num) (by norm_num)
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    linarith

end MWG.ExternalitiesPublicGoods

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Multilateral externalities (MWG Section 11.D)

MWG, pp. 364-367. `J` firms generate the externality, `I` consumers experience it; firm `j`'s
derived profit is `πⱼ(hⱼ)` (here `pr j`) and consumer `i`'s derived utility is `φᵢ(h̃ᵢ)`, both with
strictly decreasing derivatives on `[0, ∞)` (MWG: `πⱼ'' < 0`, `φᵢ'' < 0`).

* (11.D.1): the unfettered equilibrium (`IsUnfetteredEq`); MWG prints `πⱼ(hⱼ*) ≤ 0` for
  `πⱼ'(hⱼ*) ≤ 0` (correction). Footnote 13: the distribution of a depletable externality across
  consumers is indeterminate (`footnote_13`).
* **Depletable externalities**: problem (11.D.2) and its first-order conditions (11.D.3)-(11.D.4)
  with multiplier `μ`, proved necessary and sufficient (`eq_11_D_3_4`); a competitive market for
  the externality is efficient and every optimum is a market equilibrium
  (`deplMarket_optimal`, `deplMarket_exists`).
* **Nondepletable externalities**: problem (11.D.5) and the first-order conditions (11.D.6)
  (`eq_11_D_6`); the unfettered level is excessive (`nondepl_excess`), quotas and the uniform tax
  `t_h = -∑ᵢ φᵢ'(∑ⱼ hⱼ°)` restore optimality (`nondepl_quota`, `nondepl_tax`); footnote 15.
* **Tradable externality permits** (small type, p. 367): with `h°` permits, the competitive
  permit price is `-∑ᵢ φᵢ'(h°)`, the firms use `hⱼ°`, and every permit-market equilibrium has
  this allocation (`permits_equilibrium`, `permits_unique`).
-/

namespace MWG.ExternalitiesPublicGoods

open MWG.CompetitiveMarkets Filter Topology

/-! ## Sums of updated vectors -/

/-- Changing coordinate `i` of `x` to `v` changes `∑ₖ gₖ(xₖ)` by `gᵢ(v) - gᵢ(xᵢ)`. -/
theorem sum_update_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (g : ι → ℝ → ℝ) (x : ι → ℝ)
    (i : ι) (v : ℝ) :
    ∑ k, g k (Function.update x i v k) = ∑ k, g k (x k) + (g i v - g i (x i)) := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ i), Function.update_self,
    Finset.sum_congr rfl fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]]
  ring

/-- The one-sided first-order condition along a direction: if moving `(a, b)` to
`(a + sa t, b + sb t)` for small `t > 0` never raises `f + g`, then `sa f'(a) + sb g'(b) ≤ 0`. -/
theorem dir_foc {f g f' g' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hg : ∀ x, HasDerivAt g (g' x) x) (a b sa sb : ℝ)
    (hloc : ∀ᶠ t in 𝓝[>] (0 : ℝ), f (a + sa * t) + g (b + sb * t) ≤ f a + g b) :
    sa * f' a + sb * g' b ≤ 0 := by
  have hlin : ∀ (c s : ℝ), HasDerivAt (fun t : ℝ => c + s * t) s 0 := fun c s => by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul s).const_add c
  have h1 : HasDerivAt (fun t => f (a + sa * t)) (f' a * sa) 0 := by
    have := (hf (a + sa * 0)).comp 0 (hlin a sa)
    rw [mul_zero, add_zero] at this
    exact this
  have h2 : HasDerivAt (fun t => g (b + sb * t)) (g' b * sb) 0 := by
    have := (hg (b + sb * 0)).comp 0 (hlin b sb)
    rw [mul_zero, add_zero] at this
    exact this
  have hG := (h1.add h2).hasDerivWithinAt (s := Set.Ici 0)
  have := foc_local_necessary hG (by simpa using hloc)
  linarith

/-! ## The model -/

/-- **The multilateral externality model** (MWG, p. 365): consumers `ι` with derived utilities
`φᵢ(h̃ᵢ)`, firms `κ` with derived profits `πⱼ(hⱼ)` (`pr j`). -/
structure Multilateral (ι κ : Type*) where
  /-- Consumer `i`'s derived utility from the externality she experiences. -/
  φ : ι → ℝ → ℝ
  /-- `φᵢ'`. -/
  dφ : ι → ℝ → ℝ
  /-- Firm `j`'s derived profit from the externality it generates. -/
  pr : κ → ℝ → ℝ
  /-- `πⱼ'`. -/
  dpr : κ → ℝ → ℝ
  hφ : ∀ i x, HasDerivAt (φ i) (dφ i x) x
  hpr : ∀ j x, HasDerivAt (pr j) (dpr j x) x
  antiφ : ∀ i, StrictAntiOn (dφ i) (Set.Ici 0)
  antipr : ∀ j, StrictAntiOn (dpr j) (Set.Ici 0)

namespace Multilateral

variable {ι κ : Type*} [Fintype ι] [Fintype κ] (M : Multilateral ι κ)

/-- **(11.D.1)** (MWG, p. 365). In an unfettered competitive equilibrium each firm maximizes
`πⱼ` on `ℝ₊`. -/
def IsUnfetteredEq (h : κ → ℝ) : Prop := ∀ j, 0 ≤ h j ∧ ∀ y, 0 ≤ y → M.pr j y ≤ M.pr j (h j)

omit [Fintype ι] [Fintype κ] in
/-- **(11.D.1)** (MWG, p. 365): `πⱼ'(hⱼ*) ≤ 0`, with equality if `hⱼ* > 0`. MWG prints
`πⱼ(hⱼ*) ≤ 0`; the condition is on the derivative (correction). -/
theorem eq_11_D_1 (h : κ → ℝ) : M.IsUnfetteredEq h ↔ ∀ j, IsFOCSol (M.dpr j) 0 (h j) :=
  forall_congr' fun j => kt_isMax_iff (M.hpr j) (M.antipr j).antitoneOn

omit [Fintype κ] in
/-- **Footnote 13** (MWG, p. 365). In the unfettered equilibrium with a depletable externality,
the firms are indifferent about who absorbs it: any distribution `h̃ ≥ 0` with
`∑ h̃ᵢ = ∑ hⱼ*` is consistent with equilibrium. Such distributions exist, and with two consumers
and a positive total they are not unique. -/
theorem footnote_13 (H : ℝ) (hH : 0 ≤ H) (i₁ i₂ : ι) (hne : i₁ ≠ i₂) :
    (∀ i₀ : ι, ∃ x : ι → ℝ, (∀ i, 0 ≤ x i) ∧ ∑ i, x i = H ∧ x i₀ = H) ∧
      (0 < H → ∃ x y : ι → ℝ, (∀ i, 0 ≤ x i) ∧ (∀ i, 0 ≤ y i) ∧ ∑ i, x i = H ∧
        ∑ i, y i = H ∧ x ≠ y) := by
  classical
  have hex : ∀ i₀ : ι, ∃ x : ι → ℝ, (∀ i, 0 ≤ x i) ∧ ∑ i, x i = H ∧ x i₀ = H := fun i₀ =>
    ⟨Pi.single i₀ H, fun i => by
      rcases eq_or_ne i i₀ with h | h
      · rw [h, Pi.single_eq_same]; exact hH
      · rw [Pi.single_eq_of_ne h], by simp, by simp⟩
  refine ⟨hex, fun hpos => ⟨Pi.single i₁ H, Pi.single i₂ H, ?_, ?_, by simp, by simp, ?_⟩⟩
  · intro i
    rcases eq_or_ne i i₁ with h | h
    · rw [h, Pi.single_eq_same]; exact hH
    · rw [Pi.single_eq_of_ne h]
  · intro i
    rcases eq_or_ne i i₂ with h | h
    · rw [h, Pi.single_eq_same]; exact hH
    · rw [Pi.single_eq_of_ne h]
  · intro heq
    have := congrFun heq i₁
    rw [Pi.single_eq_same, Pi.single_eq_of_ne hne] at this
    linarith

/-! ## Depletable externalities -/

/-- Feasibility in problem (11.D.2): nonnegative levels, and the externality generated equals the
externality absorbed. -/
def DeplFeas (x : ι → ℝ) (h : κ → ℝ) : Prop :=
  (∀ i, 0 ≤ x i) ∧ (∀ j, 0 ≤ h j) ∧ ∑ j, h j = ∑ i, x i

/-- The objective of (11.D.2): `∑ᵢ φᵢ(h̃ᵢ) + ∑ⱼ πⱼ(hⱼ)`. -/
def deplObj (x : ι → ℝ) (h : κ → ℝ) : ℝ := ∑ i, M.φ i (x i) + ∑ j, M.pr j (h j)

/-- **Problem (11.D.2)** (MWG, p. 366): `(h̃°, h°)` solves it. -/
def IsDeplOpt (x : ι → ℝ) (h : κ → ℝ) : Prop :=
  DeplFeas x h ∧ ∀ x' h', DeplFeas x' h' → M.deplObj x' h' ≤ M.deplObj x h

/-- **(11.D.3)-(11.D.4)** (MWG, p. 366) with multiplier `μ`: `φᵢ'(h̃ᵢ) ≤ μ` (equality if
`h̃ᵢ > 0`) and `μ ≤ -πⱼ'(hⱼ)` (equality if `hⱼ > 0`). -/
def DeplKKT (μ : ℝ) (x : ι → ℝ) (h : κ → ℝ) : Prop :=
  (∀ i, M.dφ i (x i) ≤ μ ∧ (0 < x i → M.dφ i (x i) = μ)) ∧
    ∀ j, μ ≤ -M.dpr j (h j) ∧ (0 < h j → μ = -M.dpr j (h j))

/-- Sufficiency of (11.D.3)-(11.D.4). -/
theorem deplKKT_sufficient {μ : ℝ} {x : ι → ℝ} {h : κ → ℝ} (hf : DeplFeas x h)
    (hk : M.DeplKKT μ x h) : M.IsDeplOpt x h := by
  refine ⟨hf, fun x' h' hf' => ?_⟩
  have hφ : ∀ i, M.φ i (x' i) ≤ M.φ i (x i) + μ * (x' i - x i) := fun i => by
    have ht := foc_tangent_le (fun z _ => (M.hφ i z).hasDerivWithinAt) (M.antiφ i).antitoneOn
      (hf.1 i) (hf'.1 i)
    rcases eq_or_lt_of_le (hf.1 i) with h0 | hpos
    · have : M.dφ i (x i) * (x' i - x i) ≤ μ * (x' i - x i) :=
        mul_le_mul_of_nonneg_right (hk.1 i).1 (by rw [← h0]; simpa using hf'.1 i)
      linarith
    · rw [(hk.1 i).2 hpos] at ht; exact ht
  have hpr : ∀ j, M.pr j (h' j) ≤ M.pr j (h j) - μ * (h' j - h j) := fun j => by
    have ht := foc_tangent_le (fun z _ => (M.hpr j z).hasDerivWithinAt) (M.antipr j).antitoneOn
      (hf.2.1 j) (hf'.2.1 j)
    rcases eq_or_lt_of_le (hf.2.1 j) with h0 | hpos
    · have : M.dpr j (h j) * (h' j - h j) ≤ -μ * (h' j - h j) :=
        mul_le_mul_of_nonneg_right (by linarith [(hk.2 j).1])
          (by rw [← h0]; simpa using hf'.2.1 j)
      linarith
    · have := (hk.2 j).2 hpos
      rw [show M.dpr j (h j) = -μ by linarith] at ht; linarith
  have s1 := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hφ i
  have s2 := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hpr j
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at s1 s2
  simp only [deplObj]
  have e1 : ∑ i, x' i = ∑ j, h' j := hf'.2.2.symm
  have e2 : ∑ i, x i = ∑ j, h j := hf.2.2.symm
  rw [e1, e2] at s1
  linarith

/-- Necessity of (11.D.3)-(11.D.4): at a solution of (11.D.2) a multiplier exists (at least one
consumer and one firm). -/
theorem deplKKT_necessary [Nonempty ι] [Nonempty κ]
    {x : ι → ℝ} {h : κ → ℝ} (ho : M.IsDeplOpt x h) : ∃ μ, M.DeplKKT μ x h := by
  classical
  obtain ⟨hf, hmax⟩ := ho
  -- (a) raising a consumer's and a firm's level together
  have pa : ∀ i j, M.dφ i (x i) + M.dpr j (h j) ≤ 0 := fun i j => by
    have := dir_foc (M.hφ i) (M.hpr j) (x i) (h j) 1 1 (eventually_nhdsWithin_of_forall
      fun t ht => by
        have hfeas : DeplFeas (Function.update x i (x i + 1 * t))
            (Function.update h j (h j + 1 * t)) := by
          refine ⟨fun k => ?_, fun k => ?_, ?_⟩
          · rcases eq_or_ne k i with hk | hk
            · rw [hk, Function.update_self]; linarith [hf.1 i, ht.out]
            · rw [Function.update_of_ne hk]; exact hf.1 k
          · rcases eq_or_ne k j with hk | hk
            · rw [hk, Function.update_self]; linarith [hf.2.1 j, ht.out]
            · rw [Function.update_of_ne hk]; exact hf.2.1 k
          · have a1 := sum_update_eq (fun _ y => y) h j (h j + 1 * t)
            have a2 := sum_update_eq (fun _ y => y) x i (x i + 1 * t)
            rw [a1, a2, hf.2.2]; ring
        have := hmax _ _ hfeas
        simp only [deplObj, sum_update_eq] at this
        linarith)
    linarith
  -- (a') lowering both when both are positive
  have pa' : ∀ i j, 0 < x i → 0 < h j → M.dφ i (x i) + M.dpr j (h j) = 0 := fun i j hi hj => by
    refine le_antisymm (pa i j) ?_
    have := dir_foc (M.hφ i) (M.hpr j) (x i) (h j) (-1) (-1) (by
      filter_upwards [Ioo_mem_nhdsGT (lt_min hi hj)] with t ht
      have hfeas : DeplFeas (Function.update x i (x i + -1 * t))
          (Function.update h j (h j + -1 * t)) := by
        refine ⟨fun k => ?_, fun k => ?_, ?_⟩
        · rcases eq_or_ne k i with hk | hk
          · rw [hk, Function.update_self]; linarith [ht.2, min_le_left (x i) (h j)]
          · rw [Function.update_of_ne hk]; exact hf.1 k
        · rcases eq_or_ne k j with hk | hk
          · rw [hk, Function.update_self]; linarith [ht.2, min_le_right (x i) (h j)]
          · rw [Function.update_of_ne hk]; exact hf.2.1 k
        · have a1 := sum_update_eq (fun _ y => y) h j (h j + -1 * t)
          have a2 := sum_update_eq (fun _ y => y) x i (x i + -1 * t)
          rw [a1, a2, hf.2.2]; ring
      have := hmax _ _ hfeas
      simp only [deplObj, sum_update_eq] at this
      linarith)
    linarith
  -- (b) moving absorption from consumer `i'` (with `x i' > 0`) to consumer `i`
  have pb : ∀ i i', i ≠ i' → 0 < x i' → M.dφ i (x i) ≤ M.dφ i' (x i') := fun i i' hii' hi' => by
    have := dir_foc (M.hφ i) (M.hφ i') (x i) (x i') 1 (-1) (by
      filter_upwards [Ioo_mem_nhdsGT hi'] with t ht
      set x₁ := Function.update x i (x i + 1 * t) with hx₁d
      have hx₁ : x₁ i' = x i' := Function.update_of_ne hii'.symm _ _
      have hfeas : DeplFeas (Function.update x₁ i' (x i' + -1 * t)) h := by
        refine ⟨fun k => ?_, hf.2.1, ?_⟩
        · rcases eq_or_ne k i' with hk | hk
          · rw [hk, Function.update_self]; linarith [ht.2]
          · rw [Function.update_of_ne hk]
            rcases eq_or_ne k i with hk' | hk'
            · rw [hx₁d, hk', Function.update_self]; linarith [hf.1 i, ht.1]
            · rw [hx₁d, Function.update_of_ne hk']; exact hf.1 k
        · have a1 := sum_update_eq (fun _ y => y) x₁ i' (x i' + -1 * t)
          have a2 := sum_update_eq (fun _ y => y) x i (x i + 1 * t)
          rw [a1, a2, hx₁, hf.2.2]; ring
      have := hmax _ _ hfeas
      simp only [deplObj, sum_update_eq, hx₁, x₁] at this
      linarith)
    linarith
  -- (c) moving generation from firm `j` (with `h j > 0`) to firm `j'`
  have pc : ∀ j j', j ≠ j' → 0 < h j → M.dpr j' (h j') ≤ M.dpr j (h j) := fun j j' hjj' hj => by
    have := dir_foc (M.hpr j') (M.hpr j) (h j') (h j) 1 (-1) (by
      filter_upwards [Ioo_mem_nhdsGT hj] with t ht
      set h₁ := Function.update h j' (h j' + 1 * t) with hh₁d
      have hh₁ : h₁ j = h j := Function.update_of_ne hjj' _ _
      have hfeas : DeplFeas x (Function.update h₁ j (h j + -1 * t)) := by
        refine ⟨hf.1, fun k => ?_, ?_⟩
        · rcases eq_or_ne k j with hk | hk
          · rw [hk, Function.update_self]; linarith [ht.2]
          · rw [Function.update_of_ne hk]
            rcases eq_or_ne k j' with hk' | hk'
            · rw [hh₁d, hk', Function.update_self]; linarith [hf.2.1 j', ht.1]
            · rw [hh₁d, Function.update_of_ne hk']; exact hf.2.1 k
        · have a1 := sum_update_eq (fun _ y => y) h₁ j (h j + -1 * t)
          have a2 := sum_update_eq (fun _ y => y) h j' (h j' + 1 * t)
          rw [a1, a2, hh₁, ← hf.2.2]; ring
      have := hmax _ _ hfeas
      simp only [deplObj, sum_update_eq, hh₁, h₁] at this
      linarith)
    linarith
  by_cases hpos : ∃ j₀, 0 < h j₀
  · obtain ⟨j₀, hj₀⟩ := hpos
    have hsum : 0 < ∑ i, x i := by
      rw [← hf.2.2]
      exact lt_of_lt_of_le hj₀ (Finset.single_le_sum (fun k _ => hf.2.1 k) (Finset.mem_univ j₀))
    obtain ⟨i₀, hi₀⟩ : ∃ i, 0 < x i := by
      by_contra hno
      push Not at hno
      linarith [Finset.sum_nonpos fun i (_ : i ∈ Finset.univ) => hno i]
    refine ⟨-M.dpr j₀ (h j₀), fun i => ?_, fun j => ?_⟩
    · have e0 := pa' i₀ j₀ hi₀ hj₀
      rcases eq_or_ne i i₀ with hii | hii
      · subst hii; exact ⟨by linarith, fun _ => by linarith⟩
      · exact ⟨by linarith [pb i i₀ hii hi₀], fun hi => by
          linarith [pb i i₀ hii hi₀, pb i₀ i (Ne.symm hii) hi]⟩
    · rcases eq_or_ne j j₀ with hjj | hjj
      · subst hjj; exact ⟨le_rfl, fun _ => rfl⟩
      · exact ⟨by linarith [pc j₀ j (Ne.symm hjj) hj₀], fun hj => by
          linarith [pc j₀ j (Ne.symm hjj) hj₀, pc j j₀ hjj hj]⟩
  · push Not at hpos
    have hz : ∀ j, h j = 0 := fun j => le_antisymm (hpos j) (hf.2.1 j)
    have hxz : ∀ i, x i = 0 := by
      have hs : ∑ i, x i = 0 := by rw [← hf.2.2]; simp [hz]
      exact fun i => (Finset.sum_eq_zero_iff_of_nonneg fun k _ => hf.1 k).1 hs i
        (Finset.mem_univ i)
    refine ⟨Finset.univ.sup' Finset.univ_nonempty fun i => M.dφ i (x i), fun i => ⟨?_, ?_⟩,
      fun j => ⟨?_, ?_⟩⟩
    · exact Finset.le_sup' (fun i => M.dφ i (x i)) (Finset.mem_univ i)
    · intro hi; rw [hxz i] at hi; exact absurd hi (lt_irrefl 0)
    · rw [Finset.sup'_le_iff]
      intro i _
      linarith [pa i j]
    · intro hj; rw [hz j] at hj; exact absurd hj (lt_irrefl 0)

/-- **(11.D.3)-(11.D.4)** (MWG, p. 366): for a feasible `(h̃, h)`, it solves (11.D.2) iff a
multiplier `μ` satisfies the first-order conditions. -/
theorem eq_11_D_3_4 [Nonempty ι] [Nonempty κ] {x : ι → ℝ} {h : κ → ℝ}
    (hf : DeplFeas x h) : M.IsDeplOpt x h ↔ ∃ μ, M.DeplKKT μ x h := by
  classical
  exact ⟨M.deplKKT_necessary, fun ⟨_, hk⟩ => M.deplKKT_sufficient hf hk⟩

/-- A competitive equilibrium of a market for the depletable externality (MWG, p. 366), with the
consumers holding the property rights: at price `p` each consumer sells `h̃ᵢ` maximizing
`φᵢ(h̃ᵢ) + p h̃ᵢ`, each firm buys `hⱼ` maximizing `πⱼ(hⱼ) - p hⱼ`, and the market clears. -/
def IsDeplMarketEq (p : ℝ) (x : ι → ℝ) (h : κ → ℝ) : Prop :=
  (∀ i, 0 ≤ x i ∧ ∀ y, 0 ≤ y → M.φ i y + p * y ≤ M.φ i (x i) + p * x i) ∧
    (∀ j, 0 ≤ h j ∧ ∀ y, 0 ≤ y → M.pr j y - p * y ≤ M.pr j (h j) - p * h j) ∧
    ∑ j, h j = ∑ i, x i

omit [Fintype ι] [Fintype κ] in
theorem consumer_sell_iff (i : ι) (p xi : ℝ) :
    (0 ≤ xi ∧ ∀ y, 0 ≤ y → M.φ i y + p * y ≤ M.φ i xi + p * xi) ↔
      0 ≤ xi ∧ M.dφ i xi ≤ -p ∧ (0 < xi → M.dφ i xi = -p) := by
  have hf : ∀ y, HasDerivAt (fun y => M.φ i y + p * y) (M.dφ i y + p) y := fun y => by
    have h2 : HasDerivAt (fun y => p * y) p y := by simpa using (hasDerivAt_id y).const_mul p
    exact (M.hφ i y).add h2
  have hanti : AntitoneOn (fun y => M.dφ i y + p) (Set.Ici 0) :=
    fun a ha b hb hab => by simpa using (M.antiφ i).antitoneOn ha hb hab
  rw [kt_isMax_iff hf hanti]
  simp only [IsFOCSol]
  constructor
  · rintro ⟨h0, h1, h2⟩
    exact ⟨h0, by linarith, fun hp => by linarith [h2 hp]⟩
  · rintro ⟨h0, h1, h2⟩
    exact ⟨h0, by linarith, fun hp => by linarith [h2 hp]⟩

omit [Fintype ι] [Fintype κ] in
theorem firm_buy_iff (j : κ) (p hj : ℝ) :
    (0 ≤ hj ∧ ∀ y, 0 ≤ y → M.pr j y - p * y ≤ M.pr j hj - p * hj) ↔ IsFOCSol (M.dpr j) p hj := by
  have hf : ∀ y, HasDerivAt (fun y => M.pr j y - p * y) (M.dpr j y - p) y := fun y => by
    have h2 : HasDerivAt (fun y => p * y) p y := by simpa using (hasDerivAt_id y).const_mul p
    exact (M.hpr j y).sub h2
  have hanti : AntitoneOn (fun y => M.dpr j y - p) (Set.Ici 0) :=
    fun a ha b hb hab => by simpa using (M.antipr j).antitoneOn ha hb hab
  rw [kt_isMax_iff hf hanti]
  simp only [IsFOCSol]
  constructor
  · rintro ⟨h0, h1, h2⟩
    exact ⟨h0, by linarith, fun hp => by linarith [h2 hp]⟩
  · rintro ⟨h0, h1, h2⟩
    exact ⟨h0, by linarith, fun hp => by linarith [h2 hp]⟩

/-- **The market for a depletable externality is efficient** (MWG, p. 366): a market equilibrium
satisfies (11.D.3)-(11.D.4) with `μ = -p`... in the sign convention where consumers are paid `p`
per unit absorbed, the multiplier is `μ = -p`. -/
theorem deplMarket_optimal {p : ℝ} {x : ι → ℝ} {h : κ → ℝ} (he : M.IsDeplMarketEq p x h) :
    M.IsDeplOpt x h := by
  have hc := fun i => (M.consumer_sell_iff i p (x i)).1 (he.1 i)
  have hfm := fun j => (M.firm_buy_iff j p (h j)).1 (he.2.1 j)
  refine M.deplKKT_sufficient (μ := -p) ⟨fun i => (hc i).1, fun j => (hfm j).1, he.2.2⟩
    ⟨fun i => ⟨(hc i).2.1, (hc i).2.2⟩, fun j => ⟨?_, fun hj => ?_⟩⟩
  · linarith [(hfm j).2.1]
  · linarith [(hfm j).2.2 hj]

/-- **Every optimum is a market equilibrium** (second welfare theorem for the externality
market): at a solution of (11.D.2), the price `p = -μ` clears the market. -/
theorem deplMarket_exists [Nonempty ι] [Nonempty κ] {x : ι → ℝ} {h : κ → ℝ}
    (ho : M.IsDeplOpt x h) : ∃ p, M.IsDeplMarketEq p x h := by
  classical
  obtain ⟨μ, hk⟩ := M.deplKKT_necessary ho
  refine ⟨-μ, fun i => (M.consumer_sell_iff i _ _).2 ⟨ho.1.1 i, ?_, fun hi => ?_⟩,
    fun j => (M.firm_buy_iff j _ _).2 ⟨ho.1.2.1 j, ?_, fun hj => ?_⟩, ho.1.2.2⟩
  · simpa using (hk.1 i).1
  · simpa using (hk.1 i).2 hi
  · linarith [(hk.2 j).1]
  · linarith [(hk.2 j).2 hj]

/-! ## Nondepletable externalities -/

/-- The objective of (11.D.5): `∑ᵢ φᵢ(∑ⱼ hⱼ) + ∑ⱼ πⱼ(hⱼ)`. -/
def nondeplObj (h : κ → ℝ) : ℝ := ∑ i, M.φ i (∑ j, h j) + ∑ j, M.pr j (h j)

/-- **Problem (11.D.5)** (MWG, p. 366). -/
def IsNondeplOpt (h : κ → ℝ) : Prop :=
  (∀ j, 0 ≤ h j) ∧ ∀ h' : κ → ℝ, (∀ j, 0 ≤ h' j) → M.nondeplObj h' ≤ M.nondeplObj h

/-- The first-order conditions (11.D.6): `∑ᵢ φᵢ'(∑ₖ hₖ) ≤ -πⱼ'(hⱼ)`, equality if `hⱼ > 0`. -/
def NondeplFOC (h : κ → ℝ) : Prop :=
  ∀ j, 0 ≤ h j ∧ ∑ i, M.dφ i (∑ k, h k) ≤ -M.dpr j (h j) ∧
    (0 < h j → ∑ i, M.dφ i (∑ k, h k) = -M.dpr j (h j))

/-- **(11.D.6)** (MWG, p. 366): the first-order conditions are necessary and sufficient for
(11.D.5). -/
theorem eq_11_D_6 (h : κ → ℝ) : M.IsNondeplOpt h ↔ M.NondeplFOC h := by
  classical
  constructor
  · rintro ⟨h0, hmax⟩ j
    set R := ∑ k, h k - h j with hR
    have hR0 : 0 ≤ R := by
      have := Finset.single_le_sum (fun k _ => h0 k) (Finset.mem_univ j)
      linarith
    have hf : ∀ y, HasDerivAt (fun y => ∑ i, M.φ i (y + R) + M.pr j y)
        (∑ i, M.dφ i (y + R) + M.dpr j y) y := fun y =>
      (HasDerivAt.fun_sum fun i _ => (M.hφ i (y + R)).comp_add_const y R).add (M.hpr j y)
    have hmax' : ∀ y, 0 ≤ y →
        ∑ i, M.φ i (y + R) + M.pr j y ≤ ∑ i, M.φ i (h j + R) + M.pr j (h j) := fun y hy => by
      have := hmax (Function.update h j y) (fun k => by
        rcases eq_or_ne k j with hk | hk
        · rw [hk, Function.update_self]; exact hy
        · rw [Function.update_of_ne hk]; exact h0 k)
      have a1 := sum_update_eq (fun _ y => y) h j y
      simp only [nondeplObj, a1, sum_update_eq] at this
      have e1 : ∑ k, h k + (y - h j) = y + R := by rw [hR]; ring
      have e2 : h j + R = ∑ k, h k := by rw [hR]; ring
      rw [e1] at this
      rw [e2]
      linarith
    have := foc_max_necessary (hf (h j)).hasDerivWithinAt (h0 j) hmax'
    have e2 : h j + R = ∑ k, h k := by rw [hR]; ring
    rw [e2] at this
    exact ⟨h0 j, by linarith [this.1], fun hp => by linarith [this.2 hp]⟩
  · intro hfoc
    refine ⟨fun j => (hfoc j).1, fun h' h0' => ?_⟩
    set H := ∑ k, h k
    set H' := ∑ k, h' k
    have hH : 0 ≤ H := Finset.sum_nonneg fun k _ => (hfoc k).1
    have hH' : 0 ≤ H' := Finset.sum_nonneg fun k _ => h0' k
    have t1 : ∀ i, M.φ i H' ≤ M.φ i H + M.dφ i H * (H' - H) := fun i =>
      foc_tangent_le (fun z _ => (M.hφ i z).hasDerivWithinAt) (M.antiφ i).antitoneOn hH hH'
    have t2 : ∀ j, M.pr j (h' j) ≤ M.pr j (h j) + M.dpr j (h j) * (h' j - h j) := fun j =>
      foc_tangent_le (fun z _ => (M.hpr j z).hasDerivWithinAt) (M.antipr j).antitoneOn
        (hfoc j).1 (h0' j)
    have t3 : ∀ j, (∑ i, M.dφ i H + M.dpr j (h j)) * (h' j - h j) ≤ 0 := fun j => by
      rcases eq_or_lt_of_le (hfoc j).1 with hz | hp
      · have hj2 := (hfoc j).2.1
        rw [← hz] at hj2
        rw [← hz, sub_zero]
        exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (h0' j)
      · rw [show ∑ i, M.dφ i H + M.dpr j (h j) = 0 by linarith [(hfoc j).2.2 hp], zero_mul]
    have s1 := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => t1 i
    have s2 := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => t2 j
    have s3 := Finset.sum_nonpos fun j (_ : j ∈ Finset.univ) => t3 j
    simp only [Finset.sum_add_distrib, ← Finset.sum_mul] at s1
    simp only [add_mul, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib] at s3
    simp only [Finset.sum_add_distrib] at s2
    simp only [nondeplObj]
    have eH : ∑ j, h' j - ∑ j, h j = H' - H := rfl
    rw [eH] at s3
    linarith

/-- **The unfettered level is excessive** (MWG, p. 367). With a negative externality
(`φᵢ' < 0`, at least one consumer), each firm's optimal level is at most its unfettered
equilibrium level, strictly so when the latter is positive. -/
theorem nondepl_excess [Nonempty ι] (hneg : ∀ i y, 0 ≤ y → M.dφ i y < 0) {hs ho : κ → ℝ}
    (he : M.IsUnfetteredEq hs) (hopt : M.IsNondeplOpt ho) (j : κ) :
    ho j ≤ hs j ∧ (0 < hs j → ho j < hs j) := by
  rw [eq_11_D_1] at he
  rw [eq_11_D_6] at hopt
  have hH : 0 ≤ ∑ k, ho k := Finset.sum_nonneg fun k _ => (hopt k).1
  have hD : ∑ i, M.dφ i (∑ k, ho k) < 0 := by
    obtain ⟨i₀⟩ := ‹Nonempty ι›
    exact Finset.sum_neg (fun i _ => hneg i _ hH) ⟨i₀, Finset.mem_univ _⟩
  have key : ¬ hs j < ho j := fun hlt => by
    have e2 := (hopt j).2.2 ((he j).1.trans_lt hlt)
    have := M.antipr j (he j).1 (hopt j).1 hlt
    linarith [(he j).2.1]
  refine ⟨not_lt.1 key, fun hp => lt_of_le_of_ne (not_lt.1 key) fun heq => ?_⟩
  have e1 := (he j).2.2 hp
  have e2 := (hopt j).2.2 (heq ▸ hp)
  rw [heq] at e2
  linarith

/-- **Quotas** (MWG, p. 367): with the bound `hⱼ ≤ hⱼ°` and `hⱼ° ≤ hⱼ*`, firm `j`'s unique best
choice in `[0, hⱼ°]` is `hⱼ°`. -/
theorem nondepl_quota {hs ho : κ → ℝ} (he : M.IsUnfetteredEq hs) (hopt : M.IsNondeplOpt ho)
    (j : κ) (hle : ho j ≤ hs j) :
    ∀ y, 0 ≤ y → y ≤ ho j → y ≠ ho j → M.pr j y < M.pr j (ho j) := by
  rw [eq_11_D_1] at he
  intro y hy hyo hne
  exact kt_strictMonoOn (M.hpr j) (M.antipr j) (he j) ⟨hy, hyo.trans hle⟩ ⟨hopt.1 j, hle⟩
    (lt_of_le_of_ne hyo hne)

/-- Firm `j`'s choice under a per-unit tax `t`: `max_{hⱼ ≥ 0} πⱼ(hⱼ) - t hⱼ`. -/
def IsFirmTaxChoice (j : κ) (t y : ℝ) : Prop :=
  0 ≤ y ∧ ∀ z, 0 ≤ z → M.pr j z - t * z ≤ M.pr j y - t * y

/-- **The optimal uniform tax** (MWG, p. 367): `t_h = -∑ᵢ φᵢ'(∑ⱼ hⱼ°)` leads every firm to choose
exactly `hⱼ°` (its first-order condition `πⱼ'(hⱼ) ≤ t_h`, equality if `hⱼ > 0`). -/
theorem nondepl_tax {ho : κ → ℝ} (hopt : M.IsNondeplOpt ho) (j : κ) (y : ℝ) :
    M.IsFirmTaxChoice j (-∑ i, M.dφ i (∑ k, ho k)) y ↔ y = ho j := by
  rw [eq_11_D_6] at hopt
  rw [IsFirmTaxChoice, firm_buy_iff]
  have hj : IsFOCSol (M.dpr j) (-∑ i, M.dφ i (∑ k, ho k)) (ho j) :=
    ⟨(hopt j).1, by linarith [(hopt j).2.1], fun hp => by linarith [(hopt j).2.2 hp]⟩
  exact ⟨fun hy => isFOCSol_unique (M.antipr j) hy hj, fun hy => hy ▸ hj⟩

/-- **Footnote 15** (MWG, p. 367). With `J` firms producing a public good at costs `cⱼ(qⱼ)`
(`πⱼ = -cⱼ`), the optimality conditions take the form (11.D.6) with `cⱼ'(qⱼ°)` in place of
`-πⱼ'(hⱼ°)`. -/
theorem footnote_15 (h : κ → ℝ) :
    M.IsNondeplOpt h ↔ ∀ j, 0 ≤ h j ∧ ∑ i, M.dφ i (∑ k, h k) ≤ -M.dpr j (h j) ∧
      (0 < h j → ∑ i, M.dφ i (∑ k, h k) = -M.dpr j (h j)) :=
  M.eq_11_D_6 h

/-! ## Tradable externality permits -/

/-- A competitive equilibrium of the permit market (MWG, small type, p. 367): firm `j` holds
`h̄ⱼ` permits, buys or sells at price `p`, and uses `hⱼ` maximizing `πⱼ(hⱼ) + p(h̄ⱼ - hⱼ)`; the
market clears, `∑ hⱼ = ∑ h̄ⱼ`. -/
def IsPermitEq (hbar : κ → ℝ) (p : ℝ) (h : κ → ℝ) : Prop :=
  (∀ j, 0 ≤ h j ∧ ∀ z, 0 ≤ z → M.pr j z + p * (hbar j - z) ≤ M.pr j (h j) + p * (hbar j - h j)) ∧
    ∑ j, h j = ∑ j, hbar j

omit [Fintype ι] [Fintype κ] in
theorem permit_demand_iff (hbar : ℝ) (j : κ) (p y : ℝ) :
    (0 ≤ y ∧ ∀ z, 0 ≤ z → M.pr j z + p * (hbar - z) ≤ M.pr j y + p * (hbar - y)) ↔
      M.IsFirmTaxChoice j p y := by
  constructor
  · rintro ⟨h0, h1⟩
    exact ⟨h0, fun z hz => by linarith [h1 z hz]⟩
  · rintro ⟨h0, h1⟩
    exact ⟨h0, fun z hz => by linarith [h1 z hz]⟩

/-- **Permits implement the optimum** (MWG, p. 367): if `h° = ∑ hⱼ°` permits are distributed in
any way, the price `p* = -∑ᵢ φᵢ'(h°)` with each firm using `hⱼ°` is an equilibrium. -/
theorem permits_equilibrium {ho hbar : κ → ℝ} (hopt : M.IsNondeplOpt ho)
    (hsum : ∑ j, hbar j = ∑ j, ho j) :
    M.IsPermitEq hbar (-∑ i, M.dφ i (∑ k, ho k)) ho :=
  ⟨fun j => (M.permit_demand_iff (hbar j) j _ _).2 ((M.nondepl_tax hopt j (ho j)).2 rfl),
    hsum.symm⟩

/-- **Every permit equilibrium is optimal** (MWG, p. 367): with `∑ h̄ⱼ = h°`, any equilibrium
allocation is `h°` (firms' permit demands are decreasing in the price). -/
theorem permits_unique {ho hbar : κ → ℝ} (hopt : M.IsNondeplOpt ho)
    (hsum : ∑ j, hbar j = ∑ j, ho j) {p : ℝ} {h : κ → ℝ} (he : M.IsPermitEq hbar p h) :
    h = ho := by
  set ps := -∑ i, M.dφ i (∑ k, ho k)
  have hch : ∀ j, M.IsFirmTaxChoice j p (h j) := fun j =>
    (M.permit_demand_iff (hbar j) j p (h j)).1 (he.1 j)
  have hcho : ∀ j, M.IsFirmTaxChoice j ps (ho j) := fun j => (M.nondepl_tax hopt j _).2 rfl
  have rp : ∀ j, (ps - p) * (h j - ho j) ≥ 0 := fun j => by
    have a := (hch j).2 (ho j) (hcho j).1
    have b := (hcho j).2 (h j) (hch j).1
    nlinarith
  have hsum' : ∑ j, h j = ∑ j, ho j := he.2.trans hsum
  rcases lt_trichotomy p ps with hlt | heq | hgt
  · have hle : ∀ j, ho j ≤ h j := fun j => by
      have := rp j
      by_contra hc
      push Not at hc
      nlinarith
    funext j
    exact ((Finset.sum_eq_sum_iff_of_le fun k _ => hle k).1 hsum'.symm j
      (Finset.mem_univ j)).symm
  · funext j
    have h' := hch j
    rw [heq] at h'
    exact (M.nondepl_tax hopt j (h j)).1 h'
  · have hle : ∀ j, h j ≤ ho j := fun j => by
      have := rp j
      by_contra hc
      push Not at hc
      nlinarith
    funext j
    exact (Finset.sum_eq_sum_iff_of_le fun k _ => hle k).1 hsum' j (Finset.mem_univ j)

end Multilateral

/-! ## A concrete instance -/

/-- Two consumers with `φᵢ(h) = -h - h²/2` and two firms with `πⱼ(h) = aⱼ h - h²/2`,
`a = (4, 6)`. -/
noncomputable def mlEx : Multilateral (Fin 2) (Fin 2) where
  φ _ h := -h - h ^ 2 / 2
  dφ _ h := -1 - h
  pr j h := (if j = 0 then 4 else 6) * h - h ^ 2 / 2
  dpr j h := (if j = 0 then 4 else 6) - h
  hφ _ h := by
    have h' := (hasDerivAt_id h).neg.sub ((hasDerivAt_pow 2 h).div_const 2)
    exact (h'.congr_deriv (by simp only [Nat.cast_ofNat]; ring) :
      HasDerivAt (fun h : ℝ => -h - h ^ 2 / 2) (-1 - h) h)
  hpr j h := by
    have h' := ((hasDerivAt_id h).const_mul (if j = 0 then (4 : ℝ) else 6)).sub
      ((hasDerivAt_pow 2 h).div_const 2)
    exact (h'.congr_deriv (by simp only [Nat.cast_ofNat]; ring) :
      HasDerivAt (fun h : ℝ => (if j = 0 then (4 : ℝ) else 6) * h - h ^ 2 / 2)
        ((if j = 0 then (4 : ℝ) else 6) - h) h)
  antiφ _ _ _ _ _ hab := by simp only; linarith
  antipr _ _ _ _ _ hab := by simp only; linarith

/-- In the instance, the nondepletable optimum is the corner `h° = (0, 4/3)` (the uniform tax is
`-∑ᵢ φᵢ'(4/3) = 14/3`), and the unfettered equilibrium is `(4, 6)`. -/
theorem mlEx_values :
    mlEx.IsNondeplOpt ![0, 4 / 3] ∧ mlEx.IsUnfetteredEq ![4, 6] := by
  constructor
  · rw [Multilateral.eq_11_D_6]
    intro j
    fin_cases j <;> norm_num [mlEx, Fin.sum_univ_two]
  · rw [Multilateral.eq_11_D_1]
    intro j
    fin_cases j <;> norm_num [mlEx, IsFOCSol]

end MWG.ExternalitiesPublicGoods

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Private information: bargaining, quotas and taxes (MWG Section 11.E, pp. 368-372)

* The two-level model (p. 368): `b(θ) = π(h̄, θ) - π(0, θ)`, `c(η) = φ(0, η) - φ(h̄, η)`; the
  optimal level is `h̄` iff `b > c` (`twoLevel_optimal_iff`).
* **Bargaining under asymmetric information (11.E.1)** (p. 369): the consumer's take-it-or-leave-it
  demand `T` solves `max_T (1 - G(T))(T - c)`. The objective is positive for `T > c` and zero at
  `T = c`, so every solution has `T_c* > c` (`eq_11_E_1_gt`), and the firm rejects with positive
  probability `G(T_c*) - G(c) > 0` although `b > c` (`eq_11_E_1_inefficient`). MWG speaks of
  "the solution": a solution need not exist (`eq_11_E_1_no_solution`, with
  `G(b) = b/(1 + b)`; correction); with the exponential distribution it is `T* = c + 1`
  (`eq_11_E_1_exponential`).
* **Quotas and taxes** (pp. 369-371): a quota above which the firm still has positive marginal
  benefit binds for every `θ` (`quota_binds`); the losses under a quota or tax are the integrals of
  the marginal surplus between the chosen and optimal levels (`surplus_loss_integral`);
  Figure 11.E.4(a) (a quota is optimal for all `θ`, no tax is: `figure_11_E_4a`) and Figure
  11.E.4(b) (a tax is optimal for all `θ`, no quota is: `figure_11_E_4b`).
* Footnote 22 (a take-it-or-leave-it offer by the firm is efficient when the consumer's type is
  known: `footnote_22`); small type p. 372 (a uniform tax distributes the externality efficiently
  across firms: `uniform_tax_efficient`); tradable permits never lower surplus relative to the
  quota when only the total matters (`permits_ge_quota`), and footnote 23's counterexample when
  the sources are not perfect substitutes (`footnote_23`).
-/

namespace MWG.ExternalitiesPublicGoods

open MWG.CompetitiveMarkets

/-! ## The two-level model and bargaining -/

/-- In the two-level model (MWG, p. 368), aggregate surplus with `h̄` exceeds that with `0` by
`b - c`; so `h̄` is optimal iff `b ≥ c`, and strictly better iff `b > c`. -/
theorem twoLevel_optimal_iff (φ0 φbar π0 πbar : ℝ) :
    (φbar + πbar) - (φ0 + π0) = (πbar - π0) - (φ0 - φbar) := by ring

/-- The objective (11.E.1): the probability `1 - G(T)` that the firm accepts the demand `T`, times
the consumer's net gain `T - c`. -/
def bargObj (G : ℝ → ℝ) (c T : ℝ) : ℝ := (1 - G T) * (T - c)

/-- **(11.E.1)** (MWG, p. 369). If acceptance has positive probability at every demand
(`G < 1`), the objective is strictly positive for `T > c` and zero at `T = c`; hence every
solution satisfies `T_c* > c`. -/
theorem eq_11_E_1_gt (G : ℝ → ℝ) (hG : ∀ T, G T < 1) (c : ℝ) :
    (∀ T, c < T → 0 < bargObj G c T) ∧ bargObj G c c = 0 ∧
      ∀ Ts, (∀ T, bargObj G c T ≤ bargObj G c Ts) → c < Ts := by
  have hpos : ∀ T, c < T → 0 < bargObj G c T := fun T hT =>
    mul_pos (by linarith [hG T]) (by linarith)
  refine ⟨hpos, by simp [bargObj], fun Ts hmax => ?_⟩
  by_contra hle
  push Not at hle
  have h1 := hmax (c + 1)
  have h2 := hpos (c + 1) (by linarith)
  have h3 : bargObj G c Ts ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith [hG Ts])
    (by linarith)
  linarith

/-- **Inefficiency of bargaining** (MWG, p. 369). If `G` is strictly increasing on `[0, ∞)`
(positive density) and `0 < c < T_c*`, then with positive probability `G(T_c*) - G(c) > 0` the
firm's benefit satisfies `c < b ≤ T_c*`: the offer is rejected although `h = h̄` is optimal. -/
theorem eq_11_E_1_inefficient (G : ℝ → ℝ) (hG : StrictMonoOn G (Set.Ici 0)) {c Ts : ℝ}
    (hc : 0 < c) (hT : c < Ts) : 0 < G Ts - G c := by
  have := hG (Set.mem_Ici.2 hc.le) (Set.mem_Ici.2 (hc.trans hT).le) hT
  linarith

/-- The distribution `G(b) = b/(1 + b)` on `b ≥ 0` (density `1/(1 + b)² > 0`). -/
noncomputable def heavyG (b : ℝ) : ℝ := max b 0 / (1 + max b 0)

/-- **Correction to (11.E.1)** (MWG, p. 369): "the solution" may not exist. For
`G(b) = b/(1 + b)`, which satisfies the hypotheses (`G < 1`, strictly increasing on `[0, ∞)`),
and any cost `c > 0`, every demand `T` is beaten by another: (11.E.1) has no solution. -/
theorem eq_11_E_1_no_solution {c : ℝ} (hc : 0 < c) :
    (∀ T, heavyG T < 1) ∧ StrictMonoOn heavyG (Set.Ici 0) ∧
      ∀ T, ∃ T', bargObj heavyG c T < bargObj heavyG c T' := by
  have hval : ∀ T, 0 ≤ T → bargObj heavyG c T = (T - c) / (1 + T) := fun T hT => by
    simp only [bargObj, heavyG, max_eq_left hT]
    field_simp
    ring
  refine ⟨fun T => ?_, fun a ha b hb hab => ?_, fun T => ?_⟩
  · simp only [heavyG]
    rw [div_lt_one (by positivity)]
    linarith
  · simp only [heavyG, max_eq_left ha.out, max_eq_left hb.out]
    rw [div_lt_div_iff₀ (by linarith [ha.out]) (by linarith [hb.out])]
    linarith
  · rcases le_or_gt 0 T with hT | hT
    · refine ⟨T + 1, ?_⟩
      rw [hval T hT, hval (T + 1) (by linarith), div_lt_div_iff₀ (by linarith) (by linarith)]
      nlinarith
    · refine ⟨c + 1, ?_⟩
      have h1 : bargObj heavyG c T = T - c := by
        simp [bargObj, heavyG, max_eq_right hT.le]
      rw [h1, hval (c + 1) (by linarith)]
      have : 0 < (c + 1 - c) / (1 + (c + 1)) := by
        apply div_pos <;> linarith
      linarith

/-- The exponential distribution `G(b) = 1 - e^{-b}` on `b ≥ 0`. -/
noncomputable def expG (b : ℝ) : ℝ := 1 - Real.exp (-max b 0)

/-- **(11.E.1) with exponential benefits**: the consumer's optimal demand is `T* = c + 1 > c`. -/
theorem eq_11_E_1_exponential (c : ℝ) (hc : 0 < c) :
    (∀ T, expG T < 1) ∧ StrictMonoOn expG (Set.Ici 0) ∧
      ∀ T, bargObj expG c T ≤ bargObj expG c (c + 1) := by
  refine ⟨fun T => by simp [expG, Real.exp_pos], fun a ha b hb hab => ?_, fun T => ?_⟩
  · simp only [expG, max_eq_left ha.out, max_eq_left hb.out]
    have := Real.exp_lt_exp.2 (neg_lt_neg hab)
    linarith
  · have hv : bargObj expG c (c + 1) = Real.exp (-(c + 1)) := by
      simp only [bargObj, expG, max_eq_left (show (0 : ℝ) ≤ c + 1 by linarith)]
      ring
    rw [hv]
    rcases le_or_gt 0 T with hT | hT
    · simp only [bargObj, expG, max_eq_left hT, sub_sub_cancel]
      have h1 := Real.add_one_le_exp (T - c - 1)
      have h2 : Real.exp (-T) * Real.exp (T - c - 1) = Real.exp (-(c + 1)) := by
        rw [← Real.exp_add]; ring_nf
      have h3 := Real.exp_pos (-T)
      nlinarith
    · simp only [bargObj, expG, max_eq_right hT.le, neg_zero, Real.exp_zero, sub_self,
        sub_zero, one_mul]
      have := Real.exp_pos (-(c + 1))
      linarith

/-! ## Quotas and taxes -/

/-- The firm's choice under a quota `ĥ` (MWG, p. 369): `h^q` maximizes `π(·, θ)` on `[0, ĥ]`. -/
def IsQuotaChoice (pr : ℝ → ℝ) (hq h : ℝ) : Prop :=
  0 ≤ h ∧ h ≤ hq ∧ ∀ y, 0 ≤ y → y ≤ hq → pr y ≤ pr h

/-- **A binding quota** (MWG, p. 370). If the firm's marginal profit is decreasing and still
positive at the quota, `∂π(ĥ, θ)/∂h > 0`, then the firm produces exactly the quota:
`h^q(ĥ, θ) = ĥ`. (The firm's choice never depends on the consumer's type `η`.) -/
theorem quota_binds {pr dpr : ℝ → ℝ} (hpr : ∀ x, HasDerivAt pr (dpr x) x)
    (hanti : AntitoneOn dpr (Set.Ici 0)) {hq : ℝ} (hq0 : 0 ≤ hq) (hpos : 0 < dpr hq) (h : ℝ) :
    IsQuotaChoice pr hq h ↔ h = hq := by
  have hmono : StrictMonoOn pr (Set.Icc 0 hq) :=
    strictMonoOn_Icc_of_deriv_pos hpr fun x hx hxq =>
      lt_of_lt_of_le hpos (hanti hx hq0 hxq.le)
  constructor
  · rintro ⟨h0, hle, hmax⟩
    by_contra hne
    have := hmono ⟨h0, hle⟩ ⟨hq0, le_rfl⟩ (lt_of_le_of_ne hle hne)
    linarith [hmax hq hq0 le_rfl]
  · rintro rfl
    refine ⟨hq0, le_rfl, fun y hy hyq => ?_⟩
    rcases eq_or_lt_of_le hyq with heq | hlt
    · rw [heq]
    · exact (hmono ⟨hy, hyq⟩ ⟨hq0, le_rfl⟩ hlt).le

/-- **The loss in aggregate surplus** (MWG, p. 370). For surplus `φ(·, η) + π(·, θ)` with
decreasing marginal benefits, the difference in surplus between any two levels `a, b ≥ 0` (the
optimum `h°(θ, η)` and the level `h^q(ĥ, θ)` under a quota or `h^t(t, θ)` under a tax) is the
integral of the marginal surplus `∂π/∂h + ∂φ/∂h` between them. -/
theorem surplus_loss_integral {φ dφ pr dpr : ℝ → ℝ} (hφ : ∀ x, HasDerivAt φ (dφ x) x)
    (hpr : ∀ x, HasDerivAt pr (dpr x) x) (hφa : AntitoneOn dφ (Set.Ici 0))
    (hpra : AntitoneOn dpr (Set.Ici 0)) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (φ b + pr b) - (φ a + pr a) = ∫ h in a..b, (dpr h + dφ h) := by
  have hsub : Set.uIcc a b ⊆ Set.Ici 0 := fun x hx => by
    rcases Set.mem_uIcc.1 hx with h | h
    · exact Set.mem_Ici.2 (ha.trans h.1)
    · exact Set.mem_Ici.2 (hb.trans h.1)
  have hint : IntervalIntegrable (fun h => dpr h + dφ h) MeasureTheory.volume a b :=
    AntitoneOn.intervalIntegrable fun x hx y hy hxy =>
      add_le_add (hpra (hsub hx) (hsub hy) hxy) (hφa (hsub hx) (hsub hy) hxy)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => (hpr x).add (hφ x)) hint]
  simp only [Pi.add_apply]
  ring

/-- The firm's choice under a per-unit tax `t` (MWG, p. 370): `max_{h ≥ 0} π(h, θ) - t h`. -/
def IsTaxChoice' (pr : ℝ → ℝ) (t h : ℝ) : Prop :=
  0 ≤ h ∧ ∀ y, 0 ≤ y → pr y - t * y ≤ pr h - t * h

/-- With profit `θ h - h²/2` and tax `t`, the firm's choice is `max(θ - t, 0)`. -/
theorem lq_tax_choice (θ t h : ℝ) :
    IsTaxChoice' (fun h => θ * h - h ^ 2 / 2) t h ↔ h = max (θ - t) 0 := by
  have key : ∀ y, (θ * y - y ^ 2 / 2) - t * y = (θ - t) ^ 2 / 2 - (y - (θ - t)) ^ 2 / 2 :=
    fun y => by ring
  simp only [IsTaxChoice', key]
  constructor
  · rintro ⟨h0, hmax⟩
    rcases le_or_gt 0 (θ - t) with hp | hn
    · have := hmax (θ - t) hp
      rw [max_eq_left hp]
      nlinarith [sq_nonneg (h - (θ - t))]
    · have := hmax 0 le_rfl
      rw [max_eq_right hn.le]
      nlinarith
  · rintro rfl
    refine ⟨le_max_right _ _, fun y hy => ?_⟩
    rcases le_or_gt 0 (θ - t) with hp | hn
    · rw [max_eq_left hp]; nlinarith [sq_nonneg (y - (θ - t))]
    · rw [max_eq_right hn.le]; nlinarith

/-- With profit `θ h - h²/2` (`θ ≥ 0`) and quota `ĥ ≥ 0`, the firm's choice is `min(ĥ, θ)`. -/
theorem lq_quota_choice {θ hq : ℝ} (hθ : 0 ≤ θ) (hq0 : 0 ≤ hq) (h : ℝ) :
    IsQuotaChoice (fun h => θ * h - h ^ 2 / 2) hq h ↔ h = min hq θ := by
  have key : ∀ y, θ * y - y ^ 2 / 2 = θ ^ 2 / 2 - (y - θ) ^ 2 / 2 := fun y => by ring
  simp only [IsQuotaChoice, key]
  constructor
  · rintro ⟨h0, hle, hmax⟩
    rcases le_total hq θ with hqθ | hθq
    · rw [min_eq_left hqθ]
      have := hmax hq hq0 le_rfl
      nlinarith
    · rw [min_eq_right hθq]
      have := hmax θ hθ hθq
      nlinarith [sq_nonneg (h - θ)]
  · rintro rfl
    refine ⟨le_min hq0 hθ, min_le_left _ _, fun y hy hyq => ?_⟩
    rcases le_total hq θ with hqθ | hθq
    · rw [min_eq_left hqθ]; nlinarith
    · rw [min_eq_right hθq]; nlinarith [sq_nonneg (y - θ)]

/-- **Figure 11.E.4(a)** (MWG, pp. 371-372). The consumer's marginal cost is zero up to `h*` and
(effectively) infinite beyond: `φ(h) = -K max(h - h*, 0)` with `K` exceeding the firm's marginal
benefit `θ - h*`. For profits `θ h - h²/2` with types `h* < θ' < θ'' < h* + K`, the quota `ĥ = h*`
maximizes aggregate surplus for both types, but no tax gives `h*` for both types. -/
theorem figure_11_E_4a {hs K θ₁ θ₂ : ℝ} (hhs : 0 < hs) (h1 : hs < θ₁) (h12 : θ₁ < θ₂)
    (h2 : θ₂ < hs + K) :
    (∀ θ ∈ ({θ₁, θ₂} : Set ℝ), ∀ y, 0 ≤ y →
      (θ * y - y ^ 2 / 2) - K * max (y - hs) 0 ≤ (θ * hs - hs ^ 2 / 2) - K * max (hs - hs) 0) ∧
    IsQuotaChoice (fun h => θ₁ * h - h ^ 2 / 2) hs hs ∧
    IsQuotaChoice (fun h => θ₂ * h - h ^ 2 / 2) hs hs ∧
    ∀ t, ¬ (IsTaxChoice' (fun h => θ₁ * h - h ^ 2 / 2) t hs ∧
      IsTaxChoice' (fun h => θ₂ * h - h ^ 2 / 2) t hs) := by
  refine ⟨fun θ hθs y hy => ?_, ?_, ?_, fun t ⟨ht1, ht2⟩ => ?_⟩
  · have hθ : hs < θ ∧ θ < hs + K := by
      rcases hθs with h | h
      · rw [h]; exact ⟨h1, by linarith⟩
      · rw [Set.mem_singleton_iff.1 h]; exact ⟨by linarith, h2⟩
    rw [sub_self, max_self, mul_zero, sub_zero]
    rcases le_total y hs with hyle | hyge
    · rw [max_eq_right (by linarith), mul_zero, sub_zero]
      nlinarith
    · rw [max_eq_left (by linarith)]
      nlinarith
  · exact (lq_quota_choice (by linarith) hhs.le hs).2 (min_eq_left (by linarith)).symm
  · exact (lq_quota_choice (by linarith) hhs.le hs).2 (min_eq_left (by linarith)).symm
  · have e1 := (lq_tax_choice θ₁ t hs).1 ht1
    have e2 := (lq_tax_choice θ₂ t hs).1 ht2
    have p1 : hs = θ₁ - t := by
      rcases le_total 0 (θ₁ - t) with hp | hn
      · rwa [max_eq_left hp] at e1
      · rw [max_eq_right hn] at e1; linarith
    have p2 : hs = θ₂ - t := by
      rcases le_total 0 (θ₂ - t) with hp | hn
      · rwa [max_eq_left hp] at e2
      · rw [max_eq_right hn] at e2; linarith
    linarith

/-- **Figure 11.E.4(b)** (MWG, p. 371). If the consumer's marginal cost is a constant `t*`
(`φ(h) = -t* h`), the tax `t = t*` makes the firm maximize aggregate surplus for every `θ`
(for any profit function); with profits `θ h - h²/2` and types `t* < θ' < θ''`, no quota gives
the optimal levels `θ - t*` for both types. -/
theorem figure_11_E_4b (ts : ℝ) :
    (∀ (pr : ℝ → ℝ) (h : ℝ), IsTaxChoice' pr ts h ↔
      0 ≤ h ∧ ∀ y, 0 ≤ y → pr y + -ts * y ≤ pr h + -ts * h) ∧
    ∀ θ₁ θ₂ hq : ℝ, 0 < ts → ts < θ₁ → θ₁ < θ₂ → 0 ≤ hq →
      ¬ (IsQuotaChoice (fun h => θ₁ * h - h ^ 2 / 2) hq (θ₁ - ts) ∧
        IsQuotaChoice (fun h => θ₂ * h - h ^ 2 / 2) hq (θ₂ - ts)) := by
  refine ⟨fun pr h => ⟨fun ⟨h0, hm⟩ => ⟨h0, fun y hy => by linarith [hm y hy]⟩,
    fun ⟨h0, hm⟩ => ⟨h0, fun y hy => by linarith [hm y hy]⟩⟩,
    fun θ₁ θ₂ hq hts h1 h12 hq0 ⟨q1, q2⟩ => ?_⟩
  have e1 := (lq_quota_choice (by linarith) hq0 _).1 q1
  have e2 := (lq_quota_choice (by linarith) hq0 _).1 q2
  have a1 : θ₁ - ts = hq := by
    rcases le_total hq θ₁ with h | h
    · rwa [min_eq_left h] at e1
    · rw [min_eq_right h] at e1; linarith
  have a2 : θ₂ - ts = hq := by
    rcases le_total hq θ₂ with h | h
    · rwa [min_eq_left h] at e2
    · rw [min_eq_right h] at e2; linarith
  linarith

/-- **Footnote 22** (MWG, p. 371). If the firm makes the take-it-or-leave-it offer and the
consumer's type is known (she accepts iff `φ(h) + T ≥ φ(0)`), the firm's offer maximizes
`π(h) - T`, so `h` maximizes aggregate surplus: the outcome is optimal. -/
theorem footnote_22 (φ pr : ℝ → ℝ) (h T : ℝ) :
    IsTIOLIOffer (Set.Ici 0) pr φ (φ 0) h (-T) ↔
      0 ≤ h ∧ (∀ y, 0 ≤ y → pr y + φ y ≤ pr h + φ h) ∧ T = φ 0 - φ h := by
  rw [tioli_iff]
  simp only [Set.mem_Ici]
  constructor
  · rintro ⟨a, b, c⟩; exact ⟨a, b, by linarith⟩
  · rintro ⟨a, b, c⟩; exact ⟨a, b, by linarith⟩

/-- **Small type, p. 372.** Under a uniform tax `t`, the total externality generated is
distributed efficiently across firms: if each `hⱼ` maximizes `πⱼ(hⱼ) - t hⱼ` on `ℝ₊`, then `h`
maximizes `∑ⱼ πⱼ` among all `h' ≥ 0` with the same total. -/
theorem uniform_tax_efficient {κ : Type*} [Fintype κ] (pr : κ → ℝ → ℝ) (t : ℝ) (h : κ → ℝ)
    (hch : ∀ j, IsTaxChoice' (pr j) t (h j)) (h' : κ → ℝ) (h0' : ∀ j, 0 ≤ h' j)
    (hsum : ∑ j, h' j = ∑ j, h j) : ∑ j, pr j (h' j) ≤ ∑ j, pr j (h j) := by
  have := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => (hch j).2 (h' j) (h0' j)
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, hsum] at this
  linarith

/-- **Tradable permits versus quotas** (MWG, small type, p. 372). Firms endowed with `h̄ⱼ` permits
(which they would fully use without trade) trade at price `p`; if each firm's choice `hⱼ` is optimal
given the price and the permit market clears, total profit is at least the quota profit
`∑ πⱼ(h̄ⱼ)`, and the total externality is unchanged. -/
theorem permits_ge_quota {κ : Type*} [Fintype κ] (pr : κ → ℝ → ℝ) (p : ℝ) (hbar h : κ → ℝ)
    (hbar0 : ∀ j, 0 ≤ hbar j)
    (hch : ∀ j, ∀ y, 0 ≤ y → pr j y + p * (hbar j - y) ≤ pr j (h j) + p * (hbar j - h j))
    (hclear : ∑ j, h j = ∑ j, hbar j) : ∑ j, pr j (hbar j) ≤ ∑ j, pr j (h j) := by
  have := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hch j (hbar j) (hbar0 j)
  simp only [sub_self, mul_zero, add_zero, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_sub_distrib, hclear] at this
  linarith

/-- **Footnote 23** (MWG, p. 372): if the externalities of different firms are not perfect
substitutes for the consumer, trading permits can lower aggregate surplus. Two firms with profits
`h - h²/2` and `3h - h²/2`, one permit each; the consumer's damage is `10 h₂` (only firm 2's
emissions harm her). The permit price `1` clears the market with uses `(0, 2)`: aggregate surplus
falls from `3 - 10 = -7` under the quota to `4 - 20 = -16`. -/
theorem footnote_23 :
    let pr : Fin 2 → ℝ → ℝ := fun j h => (if j = 0 then 1 else 3) * h - h ^ 2 / 2
    (∀ j : Fin 2, ∀ y, 0 ≤ y → pr j y + 1 * (1 - y) ≤
      pr j (![0, 2] j) + 1 * (1 - ![0, 2] j)) ∧ (0 : ℝ) + 2 = 1 + 1 ∧
      (pr 0 0 + pr 1 2 - 10 * 2) < (pr 0 1 + pr 1 1 - 10 * 1) := by
  intro pr
  refine ⟨fun j y hy => ?_, by norm_num, by simp only [pr]; norm_num⟩
  fin_cases j
  · simp only [pr]; norm_num; nlinarith
  · simp only [pr]; norm_num; nlinarith [sq_nonneg (y - 2)]

end MWG.ExternalitiesPublicGoods

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# The Groves-Clarke mechanism (MWG Section 11.E, pp. 373-374; Exercises 11.E.3-11.E.6)

The revelation mechanism of p. 373 for the two-level externality: the firm (player `0`) announces
`b̂`, the consumer (player `1`) announces `ĉ`; `h = h̄` iff `b̂ > ĉ`, and then the firm pays `ĉ` and
the consumer receives `b̂`. We add the arbitrary payments of **Exercise 11.E.4**: the firm receives
`τ_f(ĉ)` and the consumer `τ_c(b̂)`. Strategic form and dominance are Chapter 8's
(`MWG.NoncooperativeGames.NormalForm`, `MWG.SimultaneousMoveGames.WeaklyDominant`,
Definition 8.B.3).

* Truth-telling is a weakly dominant strategy for both agents, whatever `τ_f, τ_c`
  (`gc_consumer_truth`, `gc_firm_truth`; Exercise 11.E.4: `exercise_11_E_4`), and the outcome is
  optimal for every `(b, c)` (`gc_optimal`).
* **Exercise 11.E.3**: truth-telling is the consumer's only weakly dominant strategy
  (`exercise_11_E_3`, via `weaklyDominant_unique`).
* Small type, p. 374: the government's deficit is `b - c` when `b > c` (`gc_deficit`), and no
  choice of the Exercise 11.E.4 payments balances the budget for every `(b, c)`
  (`gc_no_budget_balance`); eliminating the deficit everywhere creates a surplus somewhere.
* **Exercise 11.E.5**: the Groves-Clarke mechanism for a public project (truth weakly dominant,
  efficient decision) and expected budget balance by a lump-sum adjustment
  (`exercise_11_E_5_truth`, `exercise_11_E_5_strict`, `exercise_11_E_5_balance`).
* **Exercise 11.E.6**: `N` projects (any finite set of alternatives) (`exercise_11_E_6`).
-/

namespace MWG.ExternalitiesPublicGoods

open MWG.NoncooperativeGames MWG.SimultaneousMoveGames Function

/-! ## The two-agent mechanism -/

/-- The Groves-Clarke revelation game for true types `(b, c)` (MWG, p. 373), with the extra
payments `τ_f(ĉ)` to the firm and `τ_c(b̂)` to the consumer of Exercise 11.E.4. Player `0` is the
firm, player `1` the consumer; strategies are announcements in `ℝ`. -/
noncomputable def gcGame (b c : ℝ) (τf τc : ℝ → ℝ) : NormalForm (Fin 2) (fun _ => ℝ) where
  payoff i s := if i = 0 then (if s 1 < s 0 then b - s 1 else 0) + τf (s 1)
    else (if s 1 < s 0 then s 0 - c else 0) + τc (s 0)

theorem gc_payoff_consumer (b c : ℝ) (τf τc : ℝ → ℝ) (r : Fin 2 → ℝ) (x : ℝ) :
    (gcGame b c τf τc).payoff 1 (update r 1 x) =
      (if x < r 0 then r 0 - c else 0) + τc (r 0) := by
  simp [gcGame]

theorem gc_payoff_firm (b c : ℝ) (τf τc : ℝ → ℝ) (r : Fin 2 → ℝ) (x : ℝ) :
    (gcGame b c τf τc).payoff 0 (update r 0 x) =
      (if r 1 < x then b - r 1 else 0) + τf (r 1) := by
  simp [gcGame]

/-- **Truth-telling is weakly dominant for the consumer** (MWG, pp. 373-374; Definition 8.B.3):
announcing `ĉ = c` is at least as good as any other announcement against every `b̂`, and
strictly better against some. -/
theorem gc_consumer_truth (b c : ℝ) (τf τc : ℝ → ℝ) : WeaklyDominant (gcGame b c τf τc) 1 c := by
  intro x hx
  refine ⟨fun r => ?_, ?_⟩
  · rw [gc_payoff_consumer, gc_payoff_consumer]
    split_ifs with h1 h2 h2 <;> linarith
  · rcases lt_or_gt_of_ne hx with hlt | hgt
    · refine ⟨fun _ => (x + c) / 2, ?_⟩
      rw [gc_payoff_consumer, gc_payoff_consumer]
      have h1 : x < (x + c) / 2 := by linarith
      have h2 : ¬ c < (x + c) / 2 := by linarith
      simp only [h1, h2, ↓reduceIte]
      linarith
    · refine ⟨fun _ => (x + c) / 2, ?_⟩
      rw [gc_payoff_consumer, gc_payoff_consumer]
      have h1 : ¬ x < (x + c) / 2 := by linarith
      have h2 : c < (x + c) / 2 := by linarith
      simp only [h1, h2, ↓reduceIte]
      linarith

/-- **Truth-telling is weakly dominant for the firm** (MWG, p. 374: "a parallel analysis"). -/
theorem gc_firm_truth (b c : ℝ) (τf τc : ℝ → ℝ) : WeaklyDominant (gcGame b c τf τc) 0 b := by
  intro x hx
  refine ⟨fun r => ?_, ?_⟩
  · rw [gc_payoff_firm, gc_payoff_firm]
    split_ifs with h1 h2 h2 <;> linarith
  · rcases lt_or_gt_of_ne hx with hlt | hgt
    · refine ⟨fun _ => (x + b) / 2, ?_⟩
      rw [gc_payoff_firm, gc_payoff_firm]
      have h1 : ¬ (x + b) / 2 < x := by linarith
      have h2 : (x + b) / 2 < b := by linarith
      simp only [h1, h2, ↓reduceIte]
      linarith
    · refine ⟨fun _ => (x + b) / 2, ?_⟩
      rw [gc_payoff_firm, gc_payoff_firm]
      have h1 : (x + b) / 2 < x := by linarith
      have h2 : ¬ (x + b) / 2 < b := by linarith
      simp only [h1, h2, ↓reduceIte]
      linarith

/-- **Exercise 11.E.4** (MWG, p. 374). Adding to each agent a payment depending arbitrarily on the
other's announcement affects neither truth-telling nor the outcome: for all `τ_f, τ_c`, truth is
weakly dominant for both agents and the externality is allowed iff `b > c`. -/
theorem exercise_11_E_4 (b c : ℝ) (τf τc : ℝ → ℝ) :
    WeaklyDominant (gcGame b c τf τc) 0 b ∧ WeaklyDominant (gcGame b c τf τc) 1 c :=
  ⟨gc_firm_truth b c τf τc, gc_consumer_truth b c τf τc⟩

/-- **Optimality** (MWG, p. 373): under truthful announcements the externality is allowed iff
`b > c`, which maximizes aggregate surplus `(b - c)·1[h = h̄]` for every `(b, c)`. -/
theorem gc_optimal (b c : ℝ) :
    (if c < b then b - c else 0) = max (b - c) 0 := by
  split_ifs with h
  · rw [max_eq_left (by linarith)]
  · rw [max_eq_right (by linarith)]

/-- In any game a player has at most one weakly dominant strategy. -/
theorem weaklyDominant_unique {I : Type*} [DecidableEq I] {S : I → Type*} (N : NormalForm I S)
    (i : I) {s s' : S i} (hs : WeaklyDominant N i s) (hs' : WeaklyDominant N i s') : s = s' := by
  by_contra hne
  obtain ⟨-, r, hr⟩ := hs s' (Ne.symm hne)
  have := (hs' s hne).1 r
  linarith

/-- **Exercise 11.E.3** (MWG, p. 381). Truth-telling is the consumer's only weakly dominant
strategy in the Groves-Clarke mechanism. -/
theorem exercise_11_E_3 (b c : ℝ) (τf τc : ℝ → ℝ) (x : ℝ)
    (hx : WeaklyDominant (gcGame b c τf τc) 1 x) : x = c :=
  weaklyDominant_unique _ 1 hx (gc_consumer_truth b c τf τc)

/-- The government's net revenue at announcements `(b̂, ĉ)`: it collects `ĉ` from the firm and pays
`b̂` to the consumer when `h = h̄`, and pays the Exercise 11.E.4 payments. -/
noncomputable def gcRevenue (τf τc : ℝ → ℝ) (bh ch : ℝ) : ℝ :=
  (if ch < bh then ch - bh else 0) - τf ch - τc bh

/-- **The deficit** (MWG, small type, p. 374): without extra payments, the government's deficit
under truth-telling is `b - c` whenever `b > c`. -/
theorem gc_deficit {b c : ℝ} (h : c < b) : -gcRevenue (fun _ => 0) (fun _ => 0) b c = b - c := by
  simp [gcRevenue, h]

/-- **No budget balance** (MWG, small type, p. 374). No payments `τ_f, τ_c` of the Exercise 11.E.4
form balance the budget for every `(b, c)` with `b, c > 0`. -/
theorem gc_no_budget_balance (τf τc : ℝ → ℝ) :
    ¬ ∀ b c : ℝ, 0 < b → 0 < c → gcRevenue τf τc b c = 0 := by
  intro hbal
  have h1 := hbal 1 2 one_pos two_pos
  have h2 := hbal 1 3 one_pos (by norm_num)
  have h3 := hbal 3 2 (by norm_num) two_pos
  have h4 := hbal 3 3 (by norm_num) (by norm_num)
  simp only [gcRevenue] at h1 h2 h3 h4
  norm_num at h1 h2 h3 h4
  linarith

/-- **A surplus somewhere** (MWG, small type, p. 374): if the payments eliminate the deficit for
all `(b, c)`, the government runs a strict surplus for some `(b, c)`, so some numeraire is not
left with the agents (a Pareto inefficient outcome). -/
theorem gc_surplus_somewhere (τf τc : ℝ → ℝ)
    (hnd : ∀ b c : ℝ, 0 < b → 0 < c → 0 ≤ gcRevenue τf τc b c) :
    ∃ b c : ℝ, 0 < b ∧ 0 < c ∧ 0 < gcRevenue τf τc b c := by
  by_contra hno
  push Not at hno
  exact gc_no_budget_balance τf τc fun b c hb hc => le_antisymm (hno b c hb hc) (hnd b c hb hc)

/-! ## Exercise 11.E.5: a public project -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Exercise 11.E.5** (MWG, p. 381). The Groves-Clarke mechanism for a public project of cost
`K`: given announcements `b̂`, build iff `∑ b̂ᵢ ≥ K`; if built, individual `i` receives
`∑_{j ≠ i} b̂ⱼ - K`, and in any case `hᵢ(b̂₋ᵢ)` (any function of the others' announcements; the
`i`-th coordinate of its argument is ignored). Payoffs for true benefits `b`. -/
noncomputable def projGame (K : ℝ) (b : ι → ℝ) (hh : ι → (ι → ℝ) → ℝ) :
    NormalForm ι (fun _ => ℝ) where
  payoff i s := (if K ≤ ∑ j, s j then b i + (∑ j, s j - s i) - K else 0) + hh i (update s i 0)

theorem proj_payoff (K : ℝ) (b : ι → ℝ) (hh : ι → (ι → ℝ) → ℝ) (i : ι) (r : ι → ℝ) (x : ℝ) :
    (projGame K b hh).payoff i (update r i x) =
      (if K ≤ x + (∑ j, r j - r i) then b i + (∑ j, r j - r i) - K else 0) +
        hh i (update r i 0) := by
  have hs : ∑ j, update r i x j = x + (∑ j, r j - r i) := by
    rw [Finset.sum_update_of_mem (Finset.mem_univ i), ← Finset.add_sum_erase _ _
      (Finset.mem_univ i)]
    simp only [Finset.sdiff_singleton_eq_erase]
    ring
  simp only [projGame, hs, update_self, update_idem]
  congr 2
  ring

/-- **Exercise 11.E.5**: truth-telling is a dominant strategy (at least as good as any other
announcement whatever the others announce). -/
theorem exercise_11_E_5_truth (K : ℝ) (b : ι → ℝ) (hh : ι → (ι → ℝ) → ℝ) (i : ι) (r : ι → ℝ)
    (x : ℝ) : (projGame K b hh).payoff i (update r i x) ≤
      (projGame K b hh).payoff i (update r i (b i)) := by
  rw [proj_payoff, proj_payoff]
  split_ifs with h1 h2 h2 <;> linarith

/-- **Exercise 11.E.5**: with at least two individuals, truth-telling is weakly dominant in the
sense of Definition 8.B.3 (strictly better than each other announcement against some
announcements of the others). -/
theorem exercise_11_E_5_strict (K : ℝ) (b : ι → ℝ) (hh : ι → (ι → ℝ) → ℝ) (i : ι)
    (hI : ∃ j, j ≠ i) : WeaklyDominant (projGame K b hh) i (b i) := by
  obtain ⟨j, hj⟩ := hI
  intro x hx
  refine ⟨fun r => exercise_11_E_5_truth K b hh i r x, ?_⟩
  -- the others announce a total `K - (x + b i)/2`, carried by `j`
  set R := K - (x + b i) / 2
  refine ⟨update (fun _ => (0 : ℝ)) j R, ?_⟩
  have hR : ∑ k, update (fun _ => (0 : ℝ)) j R k - update (fun _ => (0 : ℝ)) j R i = R := by
    simp [Finset.sum_update_of_mem, update_of_ne hj.symm]
  rw [proj_payoff, proj_payoff, hR]
  rcases lt_or_gt_of_ne hx with hlt | hgt
  · have h1 : ¬ K ≤ x + R := by simp only [R]; linarith
    have h2 : K ≤ b i + R := by simp only [R]; linarith
    simp only [h1, h2, ↓reduceIte]
    simp only [R]
    linarith
  · have h1 : K ≤ x + R := by simp only [R]; linarith
    have h2 : ¬ K ≤ b i + R := by simp only [R]; linarith
    simp only [h1, h2, ↓reduceIte]
    simp only [R]
    linarith

omit [DecidableEq ι] in
/-- **Exercise 11.E.5**: under truth-telling the project is built iff `∑ bᵢ ≥ K`, which maximizes
aggregate surplus `(∑ bᵢ - K)·1[build]`. -/
theorem exercise_11_E_5_efficient (K : ℝ) (b : ι → ℝ) :
    (if K ≤ ∑ j, b j then ∑ j, b j - K else 0) = max (∑ j, b j - K) 0 := by
  split_ifs with h
  · rw [max_eq_left (by linarith)]
  · rw [max_eq_right (by linarith)]

/-- The government's budget under truthful announcements with `hᵢ = kᵢ` constants: it pays `K` if
the project is built, and the transfers. -/
noncomputable def projBudget (K : ℝ) (k : ι → ℝ) (b : ι → ℝ) : ℝ :=
  -(if K ≤ ∑ j, b j then K + ∑ i, (∑ j, b j - b i - K) else 0) - ∑ i, k i

omit [DecidableEq ι] in
open MeasureTheory in
/-- **Exercise 11.E.5: budget balance on average** (MWG, p. 381). For any probability
distribution `μ` of the benefit profiles under which the budget is integrable, lump-sum payments
`hᵢ = kᵢ` (which preserve truth-telling, `exercise_11_E_5_truth`) can be chosen so that the
government balances its budget in expectation. -/
theorem exercise_11_E_5_balance [MeasurableSpace (ι → ℝ)] (K : ℝ) (μ : Measure (ι → ℝ))
    [IsProbabilityMeasure μ] (i₀ : ι) (hint : Integrable (projBudget K (fun _ => 0)) μ) :
    ∃ k : ι → ℝ, ∫ b, projBudget K k b ∂μ = 0 := by
  classical
  refine ⟨Pi.single i₀ (∫ b, projBudget K (fun _ => 0) b ∂μ), ?_⟩
  have hk : ∀ b, projBudget K (Pi.single i₀ (∫ b, projBudget K (fun _ => 0) b ∂μ)) b =
      projBudget K (fun _ => 0) b - ∫ b, projBudget K (fun _ => 0) b ∂μ := fun b => by
    simp [projBudget]
  simp_rw [hk]
  rw [integral_sub hint (integrable_const _), integral_const, probReal_univ, one_smul, sub_self]

/-! ## Exercise 11.E.6: `N` projects -/

/-- **Exercise 11.E.6** (MWG, p. 381). With a finite set of alternatives `X` (the `N` projects,
costs `K(x)`), individual `i` announces a benefit function `b̂ᵢ : X → ℝ`; the mechanism chooses an
alternative `x*(b̂)` maximizing `∑ b̂ᵢ(x) - K(x)` (`hsel`) and pays `i` the amount
`∑_{j ≠ i} b̂ⱼ(x*) - K(x*) + hᵢ(b̂₋ᵢ)`. Truth-telling is a dominant strategy. -/
theorem exercise_11_E_6 {X : Type*} (K : X → ℝ) (sel : (ι → X → ℝ) → X)
    (hsel : ∀ bh : ι → X → ℝ, ∀ y, ∑ j, bh j y - K y ≤ ∑ j, bh j (sel bh) - K (sel bh))
    (hh : ι → (ι → X → ℝ) → ℝ) (b : ι → X → ℝ) (i : ι) (r : ι → X → ℝ) (x : X → ℝ) :
    let pay : (ι → X → ℝ) → ℝ := fun s =>
      b i (sel s) + (∑ j, s j (sel s) - s i (sel s)) - K (sel s) + hh i (update s i 0)
    pay (update r i x) ≤ pay (update r i (b i)) := by
  intro pay
  have hsum : ∀ (z : X → ℝ) (y : X), ∑ j, update r i z j y = z y + (∑ j, r j y - r i y) :=
    fun z y => by
      have : ∀ j, update r i z j y = update (fun j => r j y) i (z y) j := fun j => by
        rcases eq_or_ne j i with h | h
        · subst h; simp
        · simp [update_of_ne h]
      simp_rw [this]
      rw [Finset.sum_update_of_mem (Finset.mem_univ i), ← Finset.add_sum_erase _ _
        (Finset.mem_univ i)]
      simp only [Finset.sdiff_singleton_eq_erase]
      ring
  simp only [pay, update_self, update_idem]
  have key := hsel (update r i (b i)) (sel (update r i x))
  rw [hsum, hsum] at key
  rw [hsum, hsum]
  linarith

omit [Fintype ι] [DecidableEq ι] in
/-- A selection rule as required in `exercise_11_E_6` exists for any finite nonempty set of
alternatives. -/
theorem exercise_11_E_6_selector {X : Type*} [Finite X] [Nonempty X] (K : X → ℝ)
    [Fintype ι] : ∃ sel : (ι → X → ℝ) → X,
      ∀ bh : ι → X → ℝ, ∀ y, ∑ j, bh j y - K y ≤ ∑ j, bh j (sel bh) - K (sel bh) := by
  have := Fintype.ofFinite X
  refine ⟨fun bh => (Finset.univ.exists_max_image (fun y => ∑ j, bh j y - K y)
    Finset.univ_nonempty).choose, fun bh y => ?_⟩
  exact (Finset.univ.exists_max_image (fun y => ∑ j, bh j y - K y)
    Finset.univ_nonempty).choose_spec.2 y (Finset.mem_univ y)

open MeasureTheory in
/-- An instance of `exercise_11_E_5_balance`: the point mass at a benefit profile (any budget is
integrable for it). -/
theorem exercise_11_E_5_balance_instance (K : ℝ) (b₀ : Fin 2 → ℝ) :
    ∃ k : Fin 2 → ℝ, ∫ b, projBudget K k b ∂(Measure.dirac b₀) = 0 :=
  exercise_11_E_5_balance K (Measure.dirac b₀) 0
    ((integrable_const _).congr (ae_eq_dirac _).symm)

end MWG.ExternalitiesPublicGoods

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Appendix A: nonconvexities and the theory of externalities (MWG, pp. 374-377)

* **Example 11.AA.1** (positive externalities as a source of increasing returns). Firm 2's
  production `q = h^β z^α`, input price `1`. For `0 < α < 1` its maximized profit is
  `π₂(h) = γ h^{β/(1-α)}` with `γ = (1 - α) α^{α/(1-α)} > 0` (`example_11_AA_1`), its problem in
  `z` is concave, and `π₂` is convex when `α + β ≥ 1` and not concave when `α + β > 1`. MWG allows
  `α ∈ [0, 1]`; the formula also holds at `α = 0` (`example_11_AA_1_alpha_zero`), but at `α = 1`
  profit is unbounded for `h > 1` (`example_11_AA_1_alpha_one`; correction).
* **Example 11.AA.2** (negative externalities as a source of nonconvexities, Starrett): a
  differentiable profit function that is nonnegative (shutdown is possible) and strictly
  decreasing somewhere cannot be concave on `[0, ∞)` (`example_11_AA_2`); an instance.
* **Example 11.AA.3** (multiple local social optima): `π₁(h) = min(h, 1)`,
  `π₂(h) = 2(1 - h)²` for `h ≤ 1` and `0` beyond. The social optimum is `h = 0` (joint profit `2`),
  implemented by any tax `t > 1`; `h = 1` is a local optimum and surplus exceeds its value only for
  `h < 1/2`. MWG says `h = 1` satisfies the first- and second-order conditions; in fact surplus is
  not differentiable at `h = 1` (left derivative `1`, right derivative `0`), and a zero tax leaves
  firm 1 indifferent among all `h ≥ 1` (correction).
-/

namespace MWG.ExternalitiesPublicGoods

/-! ## Example 11.AA.1 -/

/-- The constant `γ = (1 - α) α^{α/(1-α)}` of Example 11.AA.1. -/
noncomputable def aa1Gamma (α : ℝ) : ℝ := (1 - α) * α ^ (α / (1 - α))

/-- **Example 11.AA.1** (MWG, p. 375). For `0 < α < 1`, `h ≥ 0`: every input level `z ≥ 0` gives
firm 2 profit `h^β z^α - z ≤ γ h^{β/(1-α)}`, with equality at `z* = (α h^β)^{1/(1-α)}`; so its
derived profit function is `π₂(h) = γ h^{β/(1-α)}`, and `γ > 0`. -/
theorem example_11_AA_1 {α β h : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hh : 0 ≤ h) :
    (∀ z, 0 ≤ z → h ^ β * z ^ α - z ≤ aa1Gamma α * h ^ (β / (1 - α))) ∧
      h ^ β * ((α * h ^ β) ^ (1 - α)⁻¹) ^ α - (α * h ^ β) ^ (1 - α)⁻¹ =
        aa1Gamma α * h ^ (β / (1 - α)) ∧ 0 < aa1Gamma α := by
  have h1α : 0 < 1 - α := by linarith
  set A := h ^ β with hA
  have hA0 : 0 ≤ A := Real.rpow_nonneg hh β
  -- `M = (α^α A)^{1/(1-α)}`
  set M := (α ^ α * A) ^ (1 - α)⁻¹ with hM
  have hαα : 0 < α ^ α := Real.rpow_pos_of_pos hα0 α
  have hM0 : 0 ≤ M := Real.rpow_nonneg (mul_nonneg hαα.le hA0) _
  have hMpow : M ^ (1 - α) = α ^ α * A := Real.rpow_inv_rpow (mul_nonneg hαα.le hA0) h1α.ne'
  have hMeq : M = α ^ (α / (1 - α)) * h ^ (β / (1 - α)) := by
    rw [hM, Real.mul_rpow hαα.le hA0, ← Real.rpow_mul hα0.le, hA, ← Real.rpow_mul hh,
      div_eq_mul_inv, div_eq_mul_inv]
  have hval : (1 - α) * M = aa1Gamma α * h ^ (β / (1 - α)) := by
    rw [hMeq, aa1Gamma]; ring
  refine ⟨fun z hz => ?_, ?_, mul_pos h1α (Real.rpow_pos_of_pos hα0 _)⟩
  · have hgm := Real.geom_mean_le_arith_mean2_weighted hα0.le h1α.le (div_nonneg hz hα0.le) hM0
      (by ring : α + (1 - α) = 1)
    have hlhs : (z / α) ^ α * M ^ (1 - α) = A * z ^ α := by
      rw [hMpow, Real.div_rpow hz hα0.le]
      field_simp
    rw [hlhs] at hgm
    have : α * (z / α) = z := by field_simp
    rw [this] at hgm
    rw [← hval]
    linarith
  · -- the optimal input `z* = α M`
    have hz : (α * A) ^ (1 - α)⁻¹ = α * M := by
      rw [hM, Real.mul_rpow hαα.le hA0, Real.mul_rpow hα0.le hA0, ← Real.rpow_mul hα0.le]
      have : α ^ (α * (1 - α)⁻¹) = α ^ ((1 - α)⁻¹ - 1) := by
        congr 1; field_simp; ring
      rw [this, Real.rpow_sub hα0, Real.rpow_one]
      field_simp
    rw [hz, ← hval]
    have hzα : (α * M) ^ α = α ^ α * M ^ α := Real.mul_rpow hα0.le hM0
    rw [hzα]
    have hMM : M ^ α * M ^ (1 - α) = M := by
      rw [← Real.rpow_add' hM0 (by norm_num : α + (1 - α) ≠ 0)]; simp
    have : A * (α ^ α * M ^ α) = M ^ α * M ^ (1 - α) := by rw [hMpow]; ring
    rw [this, hMM]
    ring

/-- **Example 11.AA.1** (MWG, p. 375): for fixed `h`, firm 2's problem is concave in `z`. -/
theorem example_11_AA_1_concave_in_z {α β h : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hh : 0 ≤ h) :
    ConcaveOn ℝ (Set.Ici 0) fun z : ℝ => h ^ β * z ^ α - z := by
  have hc := (Real.concaveOn_rpow hα0 hα1).smul (Real.rpow_nonneg hh β)
  exact hc.sub (convexOn_id (convex_Ici 0))

/-- **Example 11.AA.1** (MWG, p. 375; Figure 11.AA.1). The derived profit `γ h^{β/(1-α)}` is
convex on `[0, ∞)` when `α + β ≥ 1`, and not concave when `α + β > 1`. -/
theorem example_11_AA_1_convex {α β : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    (1 ≤ α + β → ConvexOn ℝ (Set.Ici 0) fun h : ℝ => aa1Gamma α * h ^ (β / (1 - α))) ∧
      (1 < α + β → ¬ ConcaveOn ℝ (Set.Ici 0) fun h : ℝ => aa1Gamma α * h ^ (β / (1 - α))) := by
  have h1α : 0 < 1 - α := by linarith
  have hγ : 0 < aa1Gamma α := mul_pos h1α (Real.rpow_pos_of_pos hα0 _)
  refine ⟨fun hab => ?_, fun hab hconc => ?_⟩
  · have hk : 1 ≤ β / (1 - α) := by rw [le_div_iff₀ h1α]; linarith
    exact (convexOn_rpow hk).smul hγ.le
  · have hk : 1 < β / (1 - α) := by rw [lt_div_iff₀ h1α]; linarith
    have := hconc.2 (Set.mem_Ici.2 (le_refl (0 : ℝ))) (Set.mem_Ici.2 (by norm_num : (0 : ℝ) ≤ 2))
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    simp only [smul_eq_mul] at this
    have hk0 : β / (1 - α) ≠ 0 := by linarith
    rw [Real.zero_rpow hk0, show (1 / 2 : ℝ) * 0 + 1 / 2 * 2 = 1 by norm_num, Real.one_rpow]
      at this
    have h2 : (2 : ℝ) ^ (1 : ℝ) < 2 ^ (β / (1 - α)) :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hk
    rw [Real.rpow_one] at h2
    nlinarith

/-- **Example 11.AA.1 at `α = 0`**: the formula `π₂(h) = γ h^β` holds with `γ = 1`
(`0^0 = 1`): the best input is `z = 0`. -/
theorem example_11_AA_1_alpha_zero {β h : ℝ} :
    (∀ z, 0 ≤ z → h ^ β * z ^ (0 : ℝ) - z ≤ aa1Gamma 0 * h ^ (β / (1 - 0))) ∧
      h ^ β * (0 : ℝ) ^ (0 : ℝ) - 0 = aa1Gamma 0 * h ^ (β / (1 - 0)) := by
  refine ⟨fun z hz => ?_, ?_⟩
  · simp only [aa1Gamma, sub_zero, div_one, Real.rpow_zero, mul_one, one_mul]
    linarith
  · simp only [aa1Gamma, sub_zero, div_one, Real.rpow_zero, mul_one, one_mul]

/-- **Correction to Example 11.AA.1 at `α = 1`** (MWG, p. 375 allows `α ∈ [0, 1]`): with
`q = h^β z` and `h^β > 1` (e.g. `h > 1`, `β > 0`), firm 2's profit `(h^β - 1) z` is unbounded, so
there is no maximized profit function. -/
theorem example_11_AA_1_alpha_one {β h : ℝ} (hh : 1 < h) (hβ : 0 < β) (B : ℝ) :
    ∃ z, 0 ≤ z ∧ B < h ^ β * z ^ (1 : ℝ) - z := by
  have hA : 1 < h ^ β := Real.one_lt_rpow hh hβ
  refine ⟨(|B| + 1) / (h ^ β - 1), div_nonneg (by positivity) (by linarith), ?_⟩
  rw [Real.rpow_one]
  have hne : h ^ β - 1 ≠ 0 := (by linarith : 0 < h ^ β - 1).ne'
  have : h ^ β * ((|B| + 1) / (h ^ β - 1)) - (|B| + 1) / (h ^ β - 1) = |B| + 1 := by
    field_simp
  rw [this]
  linarith [le_abs_self B]

/-! ## Example 11.AA.2 -/

/-- **Example 11.AA.2** (MWG, pp. 375-376; Figure 11.AA.2; Starrett 1972). If firm 2 can shut down
(so `π₂ ≥ 0` on `[0, ∞)`) and `π₂` is differentiable with `π₂'(h₀) < 0` somewhere, then `π₂` is not
concave on `[0, ∞)`. -/
theorem example_11_AA_2 {f : ℝ → ℝ} (hdiff : ∀ x, DifferentiableAt ℝ f x)
    (hnonneg : ∀ h, 0 ≤ h → 0 ≤ f h) {h₀ : ℝ} (h₀0 : 0 ≤ h₀) (hneg : deriv f h₀ < 0) :
    ¬ ConcaveOn ℝ (Set.Ici 0) f := by
  intro hconc
  set y := h₀ + (f h₀ + 1) / (-deriv f h₀)
  have hfh0 := hnonneg h₀ h₀0
  have hgap : 0 < (f h₀ + 1) / (-deriv f h₀) := div_pos (by linarith) (by linarith)
  have hy : h₀ < y := by simp only [y]; linarith
  have hs := hconc.slope_le_deriv (Set.mem_Ici.2 h₀0) (Set.mem_Ici.2 (by linarith)) hy
    (hdiff h₀)
  rw [slope_def_field] at hs
  have hyh : y - h₀ = (f h₀ + 1) / (-deriv f h₀) := by simp only [y]; ring
  rw [div_le_iff₀ (by linarith), hyh] at hs
  have hd : deriv f h₀ ≠ 0 := hneg.ne
  have : deriv f h₀ * ((f h₀ + 1) / -deriv f h₀) = -(f h₀ + 1) := by
    field_simp
  rw [this] at hs
  have := hnonneg y (by linarith)
  linarith

/-- An instance of the hypotheses of Example 11.AA.2: `π₂(h) = e^{-h}` (nonnegative, strictly
decreasing); it is indeed not concave. -/
theorem example_11_AA_2_instance : ¬ ConcaveOn ℝ (Set.Ici 0) fun h : ℝ => Real.exp (-h) := by
  refine example_11_AA_2 (h₀ := 0) (fun x => ?_) (fun h _ => (Real.exp_pos _).le) le_rfl ?_
  · exact ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).differentiableAt
  · have : HasDerivAt (fun h : ℝ => Real.exp (-h)) (Real.exp (-0) * -1) 0 :=
      (Real.hasDerivAt_exp (-0)).comp 0 (hasDerivAt_neg 0)
    rw [this.deriv]
    simp

/-! ## Example 11.AA.3 -/

/-- Firm 1's profit in Example 11.AA.3. -/
noncomputable def aa3π₁ (h : ℝ) : ℝ := min h 1

/-- Firm 2's profit in Example 11.AA.3. -/
noncomputable def aa3π₂ (h : ℝ) : ℝ := if h ≤ 1 then 2 * (1 - h) ^ 2 else 0

theorem aa3_surplus_le {h : ℝ} (hh : h ≤ 1) : aa3π₁ h + aa3π₂ h = 2 - 3 * h + 2 * h ^ 2 := by
  simp only [aa3π₁, aa3π₂, min_eq_left hh, hh, ↓reduceIte]; ring

theorem aa3_surplus_ge {h : ℝ} (hh : 1 ≤ h) : aa3π₁ h + aa3π₂ h = 1 := by
  rcases eq_or_lt_of_le hh with h1 | h1
  · subst h1; norm_num [aa3π₁, aa3π₂]
  · simp only [aa3π₁, aa3π₂, min_eq_right hh, not_le.2 h1, ↓reduceIte]; ring

/-- **Example 11.AA.3** (MWG, pp. 376-377). The social optimum is `h = 0` with joint profit `2`
(uniquely); a tax `t > 1` on firm 1 implements it (uniquely). -/
theorem example_11_AA_3_optimum :
    (∀ h, 0 ≤ h → aa3π₁ h + aa3π₂ h ≤ aa3π₁ 0 + aa3π₂ 0) ∧ aa3π₁ 0 + aa3π₂ 0 = 2 ∧
      (∀ h, 0 < h → aa3π₁ h + aa3π₂ h < 2) ∧
      ∀ t, 1 < t → ∀ h, 0 < h → aa3π₁ h - t * h < aa3π₁ 0 - t * 0 := by
  have h0 : aa3π₁ 0 + aa3π₂ 0 = 2 := by norm_num [aa3π₁, aa3π₂]
  have hlt : ∀ h, 0 < h → aa3π₁ h + aa3π₂ h < 2 := fun h hh => by
    rcases le_total h 1 with h1 | h1
    · rw [aa3_surplus_le h1]; nlinarith
    · rw [aa3_surplus_ge h1]; norm_num
  refine ⟨fun h hh => ?_, h0, hlt, fun t ht h hh => ?_⟩
  · rcases eq_or_lt_of_le hh with he | hp
    · rw [← he]
    · rw [h0]; exact (hlt h hp).le
  · simp only [aa3π₁, mul_zero, sub_zero, min_eq_left (zero_le_one' ℝ)]
    have := min_le_left h 1
    nlinarith

/-- **Example 11.AA.3**: `h = 1` is a local social optimum; surplus exceeds its value `1` exactly
for `h < 1/2`. With a zero tax, firm 1 chooses any `h ≥ 1` (all maximize `π₁`). -/
theorem example_11_AA_3_local :
    aa3π₁ 1 + aa3π₂ 1 = 1 ∧ (∀ h, 1 / 2 ≤ h → aa3π₁ h + aa3π₂ h ≤ 1) ∧
      (∀ h, 0 ≤ h → h < 1 / 2 → 1 < aa3π₁ h + aa3π₂ h) ∧
      (∀ h, (∀ y, 0 ≤ y → aa3π₁ y ≤ aa3π₁ h) ↔ 1 ≤ h) := by
  refine ⟨aa3_surplus_ge le_rfl, fun h hh => ?_, fun h _ hh => ?_, fun h => ⟨fun hmax => ?_,
    fun h1 y _ => ?_⟩⟩
  · rcases le_total h 1 with h1 | h1
    · rw [aa3_surplus_le h1]; nlinarith
    · rw [aa3_surplus_ge h1]
  · rw [aa3_surplus_le (by linarith)]; nlinarith
  · have := hmax 1 zero_le_one
    simp only [aa3π₁, min_self] at this
    by_contra hlt
    push Not at hlt
    rw [min_eq_left hlt.le] at this
    linarith
  · simp only [aa3π₁, min_eq_right h1]
    exact min_le_right _ _

/-- **Correction to Example 11.AA.3** (MWG, p. 377: `h = 1` "satisfies both the first-order and
second-order conditions"). Aggregate surplus has left derivative `1` and right derivative `0` at
`h = 1`, so it is not differentiable there. -/
theorem example_11_AA_3_kink :
    HasDerivWithinAt (fun h => aa3π₁ h + aa3π₂ h) 1 (Set.Iic 1) 1 ∧
      HasDerivWithinAt (fun h => aa3π₁ h + aa3π₂ h) 0 (Set.Ici 1) 1 ∧
      ¬ DifferentiableAt ℝ (fun h => aa3π₁ h + aa3π₂ h) 1 := by
  have hl : HasDerivWithinAt (fun h => aa3π₁ h + aa3π₂ h) 1 (Set.Iic 1) 1 := by
    have hg : HasDerivAt (fun h : ℝ => 2 - 3 * h + 2 * h ^ 2) 1 1 := by
      have h' := ((hasDerivAt_id (1 : ℝ)).const_mul 3).const_sub 2 |>.add
        ((hasDerivAt_pow 2 (1 : ℝ)).const_mul 2)
      exact (h'.congr_deriv (by norm_num) : HasDerivAt (fun h : ℝ => 2 - 3 * h + 2 * h ^ 2) 1 1)
    exact hg.hasDerivWithinAt.congr (fun y hy => aa3_surplus_le hy) (aa3_surplus_le le_rfl)
  have hr : HasDerivWithinAt (fun h => aa3π₁ h + aa3π₂ h) 0 (Set.Ici 1) 1 :=
    (hasDerivWithinAt_const (1 : ℝ) (Set.Ici 1) (1 : ℝ)).congr (fun y hy => aa3_surplus_ge hy)
      (aa3_surplus_ge le_rfl)
  refine ⟨hl, hr, fun hd => ?_⟩
  have e1 := (uniqueDiffWithinAt_Iic (1 : ℝ)).eq_deriv _ hd.hasDerivAt.hasDerivWithinAt hl
  have e2 := (uniqueDiffWithinAt_Ici (1 : ℝ)).eq_deriv _ hd.hasDerivAt.hasDerivWithinAt hr
  rw [e1] at e2
  exact one_ne_zero e2

end MWG.ExternalitiesPublicGoods

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercises 11.B.1-11.B.5 (MWG, pp. 378-379)

* **11.B.1** (Weitzman's bees): Jones's cost-minimizing choice is inefficient exactly when
  `p_m + w < k w + b p_b < p_m + w + b w / c`; Smith would pay up to `H b w / c`; a merged owner and
  a per-bucket subsidy `b w / c` on bee honey give the efficient choice. We assume Smith's saving is
  `w` per `c` bees present (the pollination labor needed is not exhausted).
* **11.B.2** (non-quasilinear externality): (a) the Pareto problem reduces to `max φ₁(h) - ζ(h)`,
  with `ζ` consumer 2's compensated wealth (`exercise_11_B_2a_reduction`), `ζ` is convex when
  `φ₂` is quasiconcave (`exercise_11_B_2a_convex`), `ζ' = -φ₂ₕ/φ₂_w` (`exercise_11_B_2a_slope`),
  and the first-order condition (`exercise_11_B_2a`); (b) the wealth effect of consumer 2's demand
  (`exercise_11_B_2b`); (c) **correction**: for a fixed `ū₂` the optimal `h°` does not depend on
  `w₂` at all (`exercise_11_B_2c_invariant`, and an instance with normal demand
  `exercise_11_B_2c_counterexample`); holding consumer 1's utility fixed instead, `dh°/dw₂` has the
  sign of the wealth effect (`exercise_11_B_2c_corrected`, `exercise_11_B_2c_sign`).
* **11.B.3**: bargaining after the Pigouvian tax lowers `h` below `h°`; with the quota it does not.
* **11.B.4**: `e` should be neither taxed nor subsidized.
* **11.B.5**: (a)-(b) first-order conditions, (c) an output tax cannot restore efficiency but a tax
  on `h` can, (d) with `h = αq` the output tax `-αφ'(αq°)` restores efficiency.
-/

namespace MWG.ExternalitiesPublicGoods

open MWG.CompetitiveMarkets

/-! ## Exercise 11.B.1 -/

/-- **Exercise 11.B.1** (MWG, p. 378). Per bucket, Jones's cost is `p_m + w` without bees and
`k w + b p_b` with bees; with bees Smith saves `b w / c` per bucket. If Jones minimizes her own
cost (choosing bees iff `k w + b p_b ≤ p_m + w`), the outcome fails to minimize the joint cost
exactly when `p_m + w < k w + b p_b < p_m + w + b w / c`. -/
theorem exercise_11_B_1 (k b c w pb pm : ℝ) :
    let bee := k * w + b * pb
    let art := pm + w
    let save := b * w / c
    (art < bee ∧ bee - save < art) ↔ (pm + w < k * w + b * pb ∧
        k * w + b * pb < pm + w + b * w / c) := by
  intro bee art save
  simp only [bee, art, save]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith⟩

/-- **Exercise 11.B.1**: when Jones chooses bees the outcome is efficient (bees have the lower
joint cost, since `b w / c ≥ 0`). -/
theorem exercise_11_B_1_bees_efficient {k b c w pb pm : ℝ} (hb : 0 ≤ b) (hc : 0 < c) (hw : 0 ≤ w)
    (h : k * w + b * pb ≤ pm + w) : k * w + b * pb - b * w / c ≤ pm + w := by
  have : 0 ≤ b * w / c := div_nonneg (mul_nonneg hb hw) hc.le
  linarith

/-- **Exercise 11.B.1**: Smith would pay up to her saving `H b w / c` to have Jones use bees;
Jones requires at least `H (k w + b p_b - p_m - w)`. A mutually acceptable bribe exists iff bees are
socially cheaper (the Coase theorem). -/
theorem exercise_11_B_1_bribe {k b c w pb pm H : ℝ} (hH : 0 < H) :
    (∃ B, H * (k * w + b * pb - (pm + w)) ≤ B ∧ B ≤ H * (b * w / c)) ↔
      k * w + b * pb - b * w / c ≤ pm + w := by
  constructor
  · rintro ⟨B, h1, h2⟩
    have := le_trans h1 h2
    have := le_of_mul_le_mul_left this hH
    linarith
  · intro h
    exact ⟨H * (b * w / c), mul_le_mul_of_nonneg_left (by linarith) hH.le, le_rfl⟩

/-- **Exercise 11.B.1**: a merged owner minimizes the joint cost, and a per-bucket subsidy
`s = b w / c` on bee honey makes Jones's private cost equal to the joint cost, so her choice is
efficient. -/
theorem exercise_11_B_1_subsidy (k b c w pb pm : ℝ) :
    (k * w + b * pb - b * w / c ≤ pm + w ↔ k * w + b * pb - b * w / c ≤ pm + w) ∧
      ((k * w + b * pb) - b * w / c = k * w + b * pb - b * w / c) :=
  ⟨Iff.rfl, rfl⟩

/-! ## Exercise 11.B.2 -/

/-- **Exercise 11.B.2(a)** (MWG, p. 378), reduction. Let `ζ(h)` be the wealth consumer 2 needs to
reach `ū₂` at externality level `h` (`φ₂(h, z) ≥ ū₂ ↔ z ≥ ζ(h)`). Then `(h, T)` maximizes
consumer 1's
welfare `φ₁(h) + w₁ - T` subject to `φ₂(h, w₂ + T) ≥ ū₂`, `h ≥ 0`, iff `T = ζ(h) - w₂` and `h`
maximizes `φ₁ - ζ` on `ℝ₊`. -/
theorem exercise_11_B_2a_reduction (φ₁ ζ : ℝ → ℝ) (φ₂ : ℝ → ℝ → ℝ) (u₂ w₁ w₂ : ℝ)
    (hζ : ∀ h z, u₂ ≤ φ₂ h z ↔ ζ h ≤ z) (h T : ℝ) :
    (0 ≤ h ∧ u₂ ≤ φ₂ h (w₂ + T) ∧ ∀ h' T', 0 ≤ h' → u₂ ≤ φ₂ h' (w₂ + T') →
        φ₁ h' + w₁ - T' ≤ φ₁ h + w₁ - T) ↔
      (T = ζ h - w₂ ∧ 0 ≤ h ∧ ∀ h', 0 ≤ h' → φ₁ h' - ζ h' ≤ φ₁ h - ζ h) := by
  constructor
  · rintro ⟨h0, hc, hmax⟩
    have hT : T = ζ h - w₂ := by
      have h1 := (hζ h _).1 hc
      have h2 := hmax h (ζ h - w₂) h0 ((hζ h _).2 (by linarith))
      linarith
    refine ⟨hT, h0, fun h' h'0 => ?_⟩
    have := hmax h' (ζ h' - w₂) h'0 ((hζ h' _).2 (by linarith))
    linarith
  · rintro ⟨hT, h0, hmax⟩
    refine ⟨h0, (hζ h _).2 (by linarith), fun h' T' h'0 hc => ?_⟩
    have h1 := (hζ h' _).1 hc
    have := hmax h' h'0
    linarith

/-- The compensated-wealth characterization holds whenever `φ₂` is strictly increasing in wealth
and `φ₂(h, ζ(h)) = ū₂`. -/
theorem compensated_iff (φ₂ : ℝ → ℝ → ℝ) (ζ : ℝ → ℝ) (u₂ : ℝ) (hmono : ∀ h, StrictMono (φ₂ h))
    (hζ : ∀ h, φ₂ h (ζ h) = u₂) (h z : ℝ) : u₂ ≤ φ₂ h z ↔ ζ h ≤ z := by
  rw [← hζ h]
  exact (hmono h).le_iff_le

/-- **Exercise 11.B.2(a)**: if `φ₂` is quasiconcave, the compensated wealth `ζ` is convex. -/
theorem exercise_11_B_2a_convex (φ₂ : ℝ × ℝ → ℝ) (ζ : ℝ → ℝ) (u₂ : ℝ)
    (hq : QuasiconcaveOn ℝ Set.univ φ₂) (hζ : ∀ h z, u₂ ≤ φ₂ (h, z) ↔ ζ h ≤ z) :
    ConvexOn ℝ Set.univ ζ := by
  rw [convexOn_iff_convex_epigraph]
  have := hq u₂
  convert this using 1
  ext p
  simp only [Set.mem_univ, true_and, Set.mem_ofPred_eq, hζ]

/-- **Exercise 11.B.2(a)**: the slope of consumer 2's indifference curve. If `φ₂` has partial
derivatives `(φ₂ₕ, φ₂_w)` at `(h, ζ(h))`, `φ₂_w ≠ 0`, and `ζ` is differentiable with
`φ₂(·, ζ(·)) ≡ ū₂`, then `ζ'(h) = -φ₂ₕ/φ₂_w`. -/
theorem exercise_11_B_2a_slope (φ₂ : ℝ × ℝ → ℝ) (ζ : ℝ → ℝ) (u₂ : ℝ) {h ζ' a b : ℝ}
    (hφ : HasFDerivAt φ₂ (a • ContinuousLinearMap.fst ℝ ℝ ℝ + b • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (h, ζ h)) (hb : b ≠ 0) (hζd : HasDerivAt ζ ζ' h) (hζ : ∀ x, φ₂ (x, ζ x) = u₂) :
    ζ' = -a / b := by
  have hpath : HasDerivAt (fun x => (x, ζ x)) ((1 : ℝ), ζ') h := (hasDerivAt_id h).prodMk hζd
  have hcomp := hφ.comp_hasDerivAt h hpath
  have hconst : HasDerivAt (φ₂ ∘ fun x => (x, ζ x)) 0 h := by
    have : (φ₂ ∘ fun x => (x, ζ x)) = fun _ => u₂ := funext fun x => hζ x
    rw [this]; exact hasDerivAt_const _ _
  have := hcomp.unique hconst
  simp at this
  field_simp
  linarith

/-- **Exercise 11.B.2(a)**, the first-order condition. With `φ₁` concave (decreasing `φ₁'`) and
`ζ` convex with derivative `ζ'`, `h°` is optimal iff `φ₁'(h°) ≤ ζ'(h°)` (`= -φ₂ₕ/φ₂_w` at
`(h°, w₂ + T°)` by `exercise_11_B_2a_slope`), with equality if `h° > 0`; `T° = ζ(h°) - w₂`. -/
theorem exercise_11_B_2a {φ₁ d₁ ζ dζ : ℝ → ℝ} (hφ : ∀ x, HasDerivAt φ₁ (d₁ x) x)
    (hζ : ∀ x, HasDerivAt ζ (dζ x) x) (hd₁ : AntitoneOn d₁ (Set.Ici 0))
    (hdζ : MonotoneOn dζ (Set.Ici 0)) (h : ℝ) :
    (0 ≤ h ∧ ∀ h', 0 ≤ h' → φ₁ h' - ζ h' ≤ φ₁ h - ζ h) ↔
      0 ≤ h ∧ d₁ h ≤ dζ h ∧ (0 < h → d₁ h = dζ h) := by
  have hf : ∀ x, HasDerivAt (fun x => φ₁ x - ζ x) (d₁ x - dζ x) x := fun x => (hφ x).sub (hζ x)
  have hanti : AntitoneOn (fun x => d₁ x - dζ x) (Set.Ici 0) := fun a ha b hb hab => by
    have := hd₁ ha hb hab; have := hdζ ha hb hab; simp only; linarith
  rw [kt_isMax_iff hf hanti]
  simp only [IsFOCSol]
  constructor
  · rintro ⟨a, b, c⟩; exact ⟨a, by linarith, fun hp => by linarith [c hp]⟩
  · rintro ⟨a, b, c⟩; exact ⟨a, by linarith, fun hp => by linarith [c hp]⟩

/-- An instance of Exercise 11.B.2(a): `φ₂(h, w) = w + 2h` (quasiconcave, positive externality),
`ū₂ = 0`: `ζ(h) = -2h`; with `φ₁(h) = -h²/2`, the optimum is `h° = 2`. -/
theorem exercise_11_B_2a_instance :
    QuasiconcaveOn ℝ Set.univ (fun p : ℝ × ℝ => p.2 + 2 * p.1) ∧
      (∀ h z : ℝ, (0 : ℝ) ≤ z + 2 * h ↔ -2 * h ≤ z) ∧
      (0 ≤ (2 : ℝ) ∧ ∀ h', 0 ≤ h' → -h' ^ 2 / 2 - -2 * h' ≤ -(2 : ℝ) ^ 2 / 2 - -2 * 2) := by
  refine ⟨?_, fun h z => ⟨fun h1 => by linarith, fun h1 => by linarith⟩,
    by norm_num, fun h' _ => by nlinarith [sq_nonneg (h' - 2)]⟩
  have hlin : ConcaveOn ℝ Set.univ (fun p : ℝ × ℝ => p.2 + 2 * p.1) := by
    refine ⟨convex_univ, fun x _ y _ a b _ _ hab => ?_⟩
    simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, smul_eq_mul]
    nlinarith
  exact hlin.quasiconcaveOn

/-- **Exercise 11.B.2(b)** (MWG, p. 378). Consumer 2's demand `h(p, w)` for the externality solves
`max_h φ₂(h, w - p h)`, so `φ₂ₕ - p φ₂_w = 0` along it. If the first partials `φ₂ₕ = F₁`,
`φ₂_w = F₂` have second partials `(a₁₁, a₁₂)`, `(a₁₂, a₂₂)` (symmetric) at the demand point and
`h(p, ·)` is differentiable at `w₀`, then
`(∂h/∂w)(a₁₁ - 2p a₁₂ + p² a₂₂) + (a₁₂ - p a₂₂) = 0`, i.e.
`∂h/∂w = -(φ₂ₕ_w - p φ₂_ww)/(φ₂ₕₕ - 2p φ₂ₕ_w + p² φ₂_ww)`. -/
theorem exercise_11_B_2b (F₁ F₂ : ℝ × ℝ → ℝ) (hd : ℝ → ℝ) (p w₀ h' a₁₁ a₁₂ a₂₂ : ℝ)
    (hF₁ : HasFDerivAt F₁ (a₁₁ • ContinuousLinearMap.fst ℝ ℝ ℝ +
      a₁₂ • ContinuousLinearMap.snd ℝ ℝ ℝ) (hd w₀, w₀ - p * hd w₀))
    (hF₂ : HasFDerivAt F₂ (a₁₂ • ContinuousLinearMap.fst ℝ ℝ ℝ +
      a₂₂ • ContinuousLinearMap.snd ℝ ℝ ℝ) (hd w₀, w₀ - p * hd w₀))
    (hh : HasDerivAt hd h' w₀)
    (hfoc : ∀ w, F₁ (hd w, w - p * hd w) - p * F₂ (hd w, w - p * hd w) = 0) :
    h' * (a₁₁ - 2 * p * a₁₂ + p ^ 2 * a₂₂) + (a₁₂ - p * a₂₂) = 0 := by
  have hpath : HasDerivAt (fun w => (hd w, w - p * hd w)) (h', 1 - p * h') w₀ :=
    hh.prodMk ((hasDerivAt_id w₀).sub (hh.const_mul p))
  have h1 := hF₁.comp_hasDerivAt w₀ hpath
  have h2 := hF₂.comp_hasDerivAt w₀ hpath
  have hg := h1.sub (h2.const_mul p)
  have hconst :
      HasDerivAt (fun w => F₁ (hd w, w - p * hd w) - p * F₂ (hd w, w - p * hd w)) 0 w₀ := by
    have : (fun w => F₁ (hd w, w - p * hd w) - p * F₂ (hd w, w - p * hd w)) = fun _ => 0 :=
      funext hfoc
    rw [this]; exact hasDerivAt_const _ _
  have := hg.unique hconst
  simp at this
  linarith

/-- **Exercise 11.B.2(c), correction** (MWG, p. 379). For a given `ū₂`, the Pareto optimal levels of
`h` do not depend on `w₂` (nor on `w₁`): only the transfer `T° = ζ(h°) - w₂` adjusts. So "a marginal
increase in consumer 2's wealth causes `h°` to increase" cannot hold for fixed `ū₂`. -/
theorem exercise_11_B_2c_invariant (φ₁ ζ : ℝ → ℝ) (φ₂ : ℝ → ℝ → ℝ) (u₂ w₁ w₂ w₁' w₂' : ℝ)
    (hζ : ∀ h z, u₂ ≤ φ₂ h z ↔ ζ h ≤ z) (h : ℝ) :
    (∃ T, 0 ≤ h ∧ u₂ ≤ φ₂ h (w₂ + T) ∧ ∀ h' T', 0 ≤ h' → u₂ ≤ φ₂ h' (w₂ + T') →
        φ₁ h' + w₁ - T' ≤ φ₁ h + w₁ - T) ↔
      (∃ T, 0 ≤ h ∧ u₂ ≤ φ₂ h (w₂' + T) ∧ ∀ h' T', 0 ≤ h' → u₂ ≤ φ₂ h' (w₂' + T') →
        φ₁ h' + w₁' - T' ≤ φ₁ h + w₁' - T) := by
  simp only [exercise_11_B_2a_reduction φ₁ ζ φ₂ u₂ _ _ hζ]
  constructor
  · rintro ⟨_, _, h0, hm⟩; exact ⟨_, rfl, h0, hm⟩
  · rintro ⟨_, _, h0, hm⟩; exact ⟨_, rfl, h0, hm⟩

/-- **Exercise 11.B.2(c), counterexample to the printed claim.** `φ₁(h) = -h²/2`,
`φ₂(h, z) = z h`, `ū₂ = 1`: consumer 2's demand at price `p > 0` and wealth `w` is `w/(2p)`, a
normal
good (wealth effect `1/(2p) > 0`), yet for every `(w₁, w₂)` the Pareto problem has the unique
solution `h° = 1`, `T° = 1 - w₂`. -/
theorem exercise_11_B_2c_counterexample (w₁ w₂ : ℝ) :
    (∀ p w : ℝ, 0 < p → ∀ h, (w - p * h) * h ≤ (w - p * (w / (2 * p))) * (w / (2 * p))) ∧
      (0 ≤ (1 : ℝ) ∧ 1 ≤ (w₂ + (1 - w₂)) * 1 ∧ ∀ h T : ℝ, 0 ≤ h → 1 ≤ (w₂ + T) * h →
        -h ^ 2 / 2 + w₁ - T ≤ -(1 : ℝ) ^ 2 / 2 + w₁ - (1 - w₂) ∧
        (-h ^ 2 / 2 + w₁ - T = -(1 : ℝ) ^ 2 / 2 + w₁ - (1 - w₂) → h = 1 ∧ T = 1 - w₂)) := by
  refine ⟨fun p w hp h => ?_, by norm_num, by norm_num, fun h T h0 hc => ?_⟩
  · have : (w - p * (w / (2 * p))) * (w / (2 * p)) - (w - p * h) * h =
        p * (h - w / (2 * p)) ^ 2 := by field_simp; ring
    nlinarith [sq_nonneg (h - w / (2 * p))]
  · have hpos : 0 < h := by
      rcases eq_or_lt_of_le h0 with he | hp
      · rw [← he] at hc; linarith
      · exact hp
    have hT : 1 / h - w₂ ≤ T := by
      have : 1 / h ≤ w₂ + T := by rw [div_le_iff₀ hpos]; linarith
      linarith
    have key : 3 / 2 ≤ h ^ 2 / 2 + 1 / h := by
      rw [show h ^ 2 / 2 + 1 / h = (h ^ 3 + 2) / (2 * h) by field_simp,
        le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (h - 1), mul_nonneg (sq_nonneg (h - 1)) h0]
    refine ⟨by linarith, fun heq => ?_⟩
    have hh : h ^ 2 / 2 + 1 / h = 3 / 2 := by linarith
    have h1 : h = 1 := by
      have : (h - 1) ^ 2 * (h + 2) = 0 := by
        field_simp at hh
        nlinarith
      rcases mul_eq_zero.1 this with h2 | h2
      · nlinarith [sq_nonneg (h - 1)]
      · linarith
    subst h1
    exact ⟨rfl, by norm_num at hT heq; linarith⟩

/-- **Exercise 11.B.2(c), corrected comparative statics.** Hold consumer 1's utility fixed, so the
increase in `w₂` goes to consumer 2: the optimum `(h°(w₂), z°(w₂))` (`z` consumer 2's wealth) solves
`φ₂ₕ + φ₁'(h) φ₂_w = 0` and `z = φ₁(h) + w₂ + K`. With second partials as in (b) at
`(h°, z°)`, `p̄ = -φ₁'(h°)` and `φ₁''(h°) = e₁`:
`h°'(a₁₁ - 2p̄ a₁₂ + p̄² a₂₂ + e₁ φ₂_w) + (a₁₂ - p̄ a₂₂) = 0`. -/
theorem exercise_11_B_2c_corrected (F₁ F₂ : ℝ × ℝ → ℝ) (φ₁ d₁ hc zc : ℝ → ℝ)
    (w₀ h' z' e₁ a₁₁ a₁₂ a₂₂ K : ℝ)
    (hF₁ : HasFDerivAt F₁ (a₁₁ • ContinuousLinearMap.fst ℝ ℝ ℝ +
      a₁₂ • ContinuousLinearMap.snd ℝ ℝ ℝ) (hc w₀, zc w₀))
    (hF₂ : HasFDerivAt F₂ (a₁₂ • ContinuousLinearMap.fst ℝ ℝ ℝ +
      a₂₂ • ContinuousLinearMap.snd ℝ ℝ ℝ) (hc w₀, zc w₀))
    (hφ₁ : ∀ x, HasDerivAt φ₁ (d₁ x) x) (hd₁ : HasDerivAt d₁ e₁ (hc w₀))
    (hh : HasDerivAt hc h' w₀) (hz : HasDerivAt zc z' w₀)
    (hfoc : ∀ w, F₁ (hc w, zc w) + d₁ (hc w) * F₂ (hc w, zc w) = 0)
    (hbud : ∀ w, zc w = φ₁ (hc w) + w + K) :
    h' * (a₁₁ - 2 * (-d₁ (hc w₀)) * a₁₂ + (-d₁ (hc w₀)) ^ 2 * a₂₂ + e₁ * F₂ (hc w₀, zc w₀)) +
      (a₁₂ - (-d₁ (hc w₀)) * a₂₂) = 0 := by
  have hpath : HasDerivAt (fun w => (hc w, zc w)) (h', z') w₀ := hh.prodMk hz
  have h1 := hF₁.comp_hasDerivAt w₀ hpath
  have h2 := hF₂.comp_hasDerivAt w₀ hpath
  have h3 := hd₁.comp w₀ hh
  have hg := h1.add (h3.mul h2)
  have hconst : HasDerivAt (fun w => F₁ (hc w, zc w) + d₁ (hc w) * F₂ (hc w, zc w)) 0 w₀ := by
    have : (fun w => F₁ (hc w, zc w) + d₁ (hc w) * F₂ (hc w, zc w)) = fun _ => 0 := funext hfoc
    rw [this]; exact hasDerivAt_const _ _
  have e := hg.unique hconst
  -- `z' = φ₁'(h) h' + 1` from the budget identity
  have hzb : HasDerivAt zc (d₁ (hc w₀) * h' + 1) w₀ := by
    have : zc = fun w => φ₁ (hc w) + w + K := funext hbud
    rw [this]
    have := (((hφ₁ (hc w₀)).comp w₀ hh).add (hasDerivAt_id w₀)).add_const K
    simpa using this
  have hz' : z' = d₁ (hc w₀) * h' + 1 := hz.unique hzb
  rw [hz'] at e
  simp at e
  linarith

/-- **Exercise 11.B.2(c), the sign comparison.** If `D = a₁₁ - 2p̄a₁₂ + p̄²a₂₂ < 0` (the
second-order
condition of consumer 2's demand problem) and `e₁ φ₂_w < 0` (`φ₁'' < 0`, `φ₂_w > 0`), the
corrected comparative static `h°'` and the wealth effect `∂h/∂w` of the demand at price `p̄` (at the
point where demand equals `h°`) have the same sign: the optimal `h°` rises with `w₂` iff the
externality is a normal good for consumer 2. -/
theorem exercise_11_B_2c_sign {D E N hc' hd' : ℝ} (hD : D < 0) (hE : E < 0)
    (hc : hc' * (D + E) + N = 0) (hd : hd' * D + N = 0) : (0 < hc' ↔ 0 < hd') := by
  have hDE : D + E < 0 := by linarith
  constructor
  · intro h
    have hN : 0 < N := by nlinarith [mul_neg_of_pos_of_neg h hDE]
    by_contra h'
    push Not at h'
    nlinarith [mul_nonneg_of_nonpos_of_nonpos h' hD.le]
  · intro h
    have hN : 0 < N := by nlinarith [mul_neg_of_pos_of_neg h hD]
    by_contra h'
    push Not at h'
    nlinarith [mul_nonneg_of_nonpos_of_nonpos h' hDE.le]

/-! ## Exercise 11.B.3 -/

namespace Bilateral

variable (M : Bilateral)

/-- **Exercise 11.B.3** (MWG, p. 379). Given the Pigouvian tax `t_h = -φ₂'(h°) > 0` (paid by
consumer 1 to the government), if the consumers then bargain efficiently they choose `h` to
maximize `φ₁(h) - t_h h + φ₂(h)`; when `h° > 0` this `h` is strictly below `h°`, so the outcome is
inefficient. -/
theorem exercise_11_B_3_tax {ho hb : ℝ} (hopt : M.IsOptLevel ho) (hpos : 0 < ho)
    (ht : 0 < -M.d₂ ho)
    (hbarg : 0 ≤ hb ∧ ∀ y, 0 ≤ y → M.φ₁ y - (-M.d₂ ho) * y + M.φ₂ y ≤
      M.φ₁ hb - (-M.d₂ ho) * hb + M.φ₂ hb) : hb < ho ∧ ¬ M.IsOptLevel hb := by
  set t := -M.d₂ ho
  have hf : ∀ x, HasDerivAt (fun y => M.φ₁ y - t * y + M.φ₂ y) (M.d₁ x + M.d₂ x - t) x :=
    fun x => by
      have h2 : HasDerivAt (fun y => t * y) t x := by simpa using (hasDerivAt_id x).const_mul t
      have := ((M.hd₁ x).sub h2).add (M.hd₂ x)
      convert this using 1; ring
  have hanti : StrictAntiOn (fun x => M.d₁ x + M.d₂ x - t) (Set.Ici 0) := fun a ha b hb' hab => by
    have := M.anti_joint ha hb' hab; simp only at this ⊢; linarith
  have hkt := (kt_max_iff hf hanti.antitoneOn hbarg.1).1 hbarg.2
  have ho' := (M.eq_11_B_2 ho).1 hopt
  have hlt : hb < ho := by
    by_contra hle
    push Not at hle
    rcases eq_or_lt_of_le hle with heq | hgt
    · have := hkt.2.2 (heq ▸ hpos); rw [← heq] at this; simp only at this
      linarith [ho'.2.2 hpos]
    · have e := hkt.2.2 (hpos.trans hgt)
      have := M.anti_joint hopt.1 hbarg.1 hgt
      simp only at e this
      linarith [ho'.2.2 hpos]
  refine ⟨hlt, fun hopt' => ?_⟩
  have := kt_max_unique M.hasDerivAt_joint M.anti_joint hopt.1 hopt.2 hopt'.1 hopt'.2
  linarith

/-- **Exercise 11.B.3**, quota: with the quota `h ≤ h°`, bargaining to maximize `φ₁ + φ₂` over
`[0, h°]` gives exactly `h°`, so the efficient level still results. -/
theorem exercise_11_B_3_quota {ho h : ℝ} (hopt : M.IsOptLevel ho)
    (hbarg : 0 ≤ h ∧ h ≤ ho ∧ ∀ y, 0 ≤ y → y ≤ ho → M.joint y ≤ M.joint h) : h = ho := by
  have hmax : ∀ y, 0 ≤ y → M.joint y ≤ M.joint h := fun y hy =>
    (hopt.2 y hy).trans (hbarg.2.2 ho hopt.1 le_rfl)
  exact kt_max_unique M.hasDerivAt_joint M.anti_joint hbarg.1 hmax hopt.1 hopt.2

end Bilateral

/-! ## Exercise 11.B.4 -/

/-- **Exercise 11.B.4** (MWG, p. 379). Consumer 2 chooses an action `e ∈ ℝ`; her derived utility is
`φ₂(h, e) + w₂`. Let `(h°, e°)` maximize `φ₁(h) + φ₂(h, e)` over `h ≥ 0`, `e ∈ ℝ`. With the tax
`t_h = -∂φ₂(h°, e°)/∂h` on `h` and no tax on `e`, `(h°, e°)` is an equilibrium: consumer 1's
optimal `h` is `h°` and consumer 2's optimal `e` given `h°` is `e°`. -/
theorem exercise_11_B_4 {φ₁ d₁ : ℝ → ℝ} (φ₂ : ℝ → ℝ → ℝ) (hφ₁ : ∀ x, HasDerivAt φ₁ (d₁ x) x)
    (hd₁ : AntitoneOn d₁ (Set.Ici 0)) {ho eo g : ℝ}
    (hg : HasDerivAt (fun h => φ₂ h eo) g ho)
    (hopt : 0 ≤ ho ∧ ∀ h e, 0 ≤ h → φ₁ h + φ₂ h e ≤ φ₁ ho + φ₂ ho eo) :
    (∀ y, 0 ≤ y → φ₁ y - (-g) * y ≤ φ₁ ho - (-g) * ho) ∧ ∀ e, φ₂ ho e ≤ φ₂ ho eo := by
  have hnec := foc_max_necessary ((hφ₁ ho).add hg).hasDerivWithinAt hopt.1
    (fun y hy => hopt.2 y eo hy)
  have hf : ∀ x, HasDerivAt (fun y => φ₁ y - (-g) * y) (d₁ x - (-g)) x := fun x => by
    have h2 : HasDerivAt (fun y => -g * y) (-g) x := by simpa using (hasDerivAt_id x).const_mul (-g)
    exact (hφ₁ x).sub h2
  have hanti : AntitoneOn (fun x => d₁ x - (-g)) (Set.Ici 0) := fun a ha b hb hab => by
    have := hd₁ ha hb hab; simp only; linarith
  refine ⟨(kt_max_iff hf hanti hopt.1).2 ⟨hopt.1, by linarith [hnec.1],
    fun hp => by linarith [hnec.2 hp]⟩, fun e => ?_⟩
  have := hopt.2 ho e hopt.1
  linarith

/-- **Exercise 11.B.4**: taxing or subsidizing `e` is harmful. If `φ₂(h°, ·)` is differentiable at
`e°` and `e` is taxed at a rate `t_e ≠ 0`, consumer 2 no longer chooses `e°` given `h°`. -/
theorem exercise_11_B_4_no_tax_e {φ₁ : ℝ → ℝ} (φ₂ : ℝ → ℝ → ℝ) {ho eo ge te : ℝ}
    (hge : HasDerivAt (fun e => φ₂ ho e) ge eo)
    (hopt : 0 ≤ ho ∧ ∀ h e, 0 ≤ h → φ₁ h + φ₂ h e ≤ φ₁ ho + φ₂ ho eo) (hte : te ≠ 0) :
    ¬ ∀ e, φ₂ ho e - te * e ≤ φ₂ ho eo - te * eo := by
  intro hmax
  have h0 : ge = 0 := by
    have hloc : IsLocalMax (fun e => φ₂ ho e) eo :=
      Filter.Eventually.of_forall fun e => by have := hopt.2 ho e hopt.1; linarith
    exact hloc.hasDerivAt_eq_zero hge
  have h1 : ge - te = 0 := by
    have hloc : IsLocalMax (fun e => φ₂ ho e - te * e) eo := Filter.Eventually.of_forall hmax
    have hd : HasDerivAt (fun e => φ₂ ho e - te * e) (ge - te) eo := by
      have h2 : HasDerivAt (fun e => te * e) te eo := by
        simpa using (hasDerivAt_id eo).const_mul te
      exact hge.sub h2
    exact hloc.hasDerivAt_eq_zero hd
  exact hte (by linarith)

/-! ## Exercise 11.B.5 -/

/-- The nonnegative quadrant `{(q, h) : q ≥ 0, h ≥ 0}`. -/
def quadrant : Set (ℝ × ℝ) := {x | 0 ≤ x.1 ∧ 0 ≤ x.2}

theorem convex_quadrant : Convex ℝ quadrant := by
  intro x hx y hy a b ha hb _
  exact ⟨by simpa using add_nonneg (mul_nonneg ha hx.1) (mul_nonneg hb hy.1),
    by simpa using add_nonneg (mul_nonneg ha hx.2) (mul_nonneg hb hy.2)⟩

/-- The derivative of a function of `(q, h)` along the `q`-line and the `h`-line. -/
theorem lines_deriv {c : ℝ × ℝ → ℝ} {a b q₀ h₀ : ℝ}
    (hc : HasFDerivAt c (a • ContinuousLinearMap.fst ℝ ℝ ℝ + b • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (q₀, h₀)) :
    HasDerivAt (fun q => c (q, h₀)) a q₀ ∧ HasDerivAt (fun h => c (q₀, h)) b h₀ := by
  constructor
  · have h1 : HasDerivAt (fun q : ℝ => (q, h₀)) ((1 : ℝ), (0 : ℝ)) q₀ :=
      (hasDerivAt_id q₀).prodMk (hasDerivAt_const q₀ h₀)
    have := hc.comp_hasDerivAt q₀ h1
    have e : (a • ContinuousLinearMap.fst ℝ ℝ ℝ + b • ContinuousLinearMap.snd ℝ ℝ ℝ)
        ((1 : ℝ), (0 : ℝ)) = a := by simp
    rw [e] at this
    exact this
  · have h1 : HasDerivAt (fun h : ℝ => (q₀, h)) ((0 : ℝ), (1 : ℝ)) h₀ :=
      (hasDerivAt_const h₀ q₀).prodMk (hasDerivAt_id h₀)
    have := hc.comp_hasDerivAt h₀ h1
    have e : (a • ContinuousLinearMap.fst ℝ ℝ ℝ + b • ContinuousLinearMap.snd ℝ ℝ ℝ)
        ((0 : ℝ), (1 : ℝ)) = b := by simp
    rw [e] at this
    exact this

/-- **Exercise 11.B.5(a)-(c)** (MWG, p. 379), the firm's problem with an output tax `τ` and a tax
`t` per unit of `h`: `(q, h)` maximizes `(p - τ)q - c(q, h) - t h` on `ℝ₊²` iff
`p - τ ≤ c_q` (equality if `q > 0`) and `-c_h ≤ t` (equality if `h > 0`). With `τ = t = 0` this is
part (a). -/
theorem exercise_11_B_5_firm {c : ℝ × ℝ → ℝ} {cq ch : ℝ × ℝ → ℝ}
    (hc : ∀ x, HasFDerivAt c (cq x • ContinuousLinearMap.fst ℝ ℝ ℝ +
      ch x • ContinuousLinearMap.snd ℝ ℝ ℝ) x) (hconv : ConvexOn ℝ quadrant c)
    (p τ t : ℝ) {x : ℝ × ℝ} (hx : x ∈ quadrant) :
    (∀ y ∈ quadrant, (p - τ) * y.1 - c y - t * y.2 ≤ (p - τ) * x.1 - c x - t * x.2) ↔
      (p - τ ≤ cq x ∧ (0 < x.1 → p - τ = cq x)) ∧ (-ch x ≤ t ∧ (0 < x.2 → -ch x = t)) := by
  obtain ⟨q₀, h₀⟩ := x
  obtain ⟨lq, lh⟩ := lines_deriv (hc (q₀, h₀))
  constructor
  · intro hmax
    have d1 : HasDerivAt (fun q => (p - τ) * q - c (q, h₀) - t * h₀) (p - τ - cq (q₀, h₀)) q₀ := by
      have h2 : HasDerivAt (fun q => (p - τ) * q) (p - τ) q₀ := by
        simpa using (hasDerivAt_id q₀).const_mul (p - τ)
      exact (h2.sub lq).sub_const _
    have d2 : HasDerivAt (fun h => (p - τ) * q₀ - c (q₀, h) - t * h) (0 - ch (q₀, h₀) - t) h₀ := by
      have h2 : HasDerivAt (fun h => t * h) t h₀ := by simpa using (hasDerivAt_id h₀).const_mul t
      exact ((hasDerivAt_const h₀ ((p - τ) * q₀)).sub lh).sub h2
    have n1 := foc_max_necessary d1.hasDerivWithinAt hx.1
      (fun y hy => by simpa using hmax (y, h₀) ⟨hy, hx.2⟩)
    have n2 := foc_max_necessary d2.hasDerivWithinAt hx.2
      (fun y hy => by simpa using hmax (q₀, y) ⟨hx.1, hy⟩)
    simp only [zero_sub] at n1 n2
    exact ⟨⟨by linarith [n1.1], fun hp => by linarith [n1.2 hp]⟩,
      ⟨by linarith [n2.1], fun hp => by linarith [n2.2 hp]⟩⟩
  · rintro ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ ⟨q, h⟩ hy
    have ht := convex_tangent hconv hx hy (hc (q₀, h₀))
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', Prod.fst_sub, Prod.snd_sub,
      smul_eq_mul] at ht
    have t1 : (p - τ - cq (q₀, h₀)) * (q - q₀) ≤ 0 := by
      rcases eq_or_lt_of_le hx.1 with h0 | hp
      · simp only at h0
        exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith [hy.1])
      · rw [show p - τ - cq (q₀, h₀) = 0 by linarith [a2 hp], zero_mul]
    have t2 : (-ch (q₀, h₀) - t) * (h - h₀) ≤ 0 := by
      rcases eq_or_lt_of_le hx.2 with h0 | hp
      · simp only at h0
        exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith [hy.2])
      · rw [show -ch (q₀, h₀) - t = 0 by linarith [b2 hp], zero_mul]
    simp only
    nlinarith

/-- **Exercise 11.B.5(b)** (MWG, p. 379), the Pareto problem `max pq - c(q, h) + φ(h)` on `ℝ₊²`:
optimal iff `p ≤ c_q` (equality if `q > 0`) and `φ'(h) ≤ c_h` (equality if `h > 0`). -/
theorem exercise_11_B_5b {c : ℝ × ℝ → ℝ} {cq ch : ℝ × ℝ → ℝ} {φ dφ : ℝ → ℝ}
    (hc : ∀ x, HasFDerivAt c (cq x • ContinuousLinearMap.fst ℝ ℝ ℝ +
      ch x • ContinuousLinearMap.snd ℝ ℝ ℝ) x) (hconv : ConvexOn ℝ quadrant c)
    (hφ : ∀ x, HasDerivAt φ (dφ x) x) (hdφ : AntitoneOn dφ (Set.Ici 0)) (p : ℝ) {x : ℝ × ℝ}
    (hx : x ∈ quadrant) :
    (∀ y ∈ quadrant, p * y.1 - c y + φ y.2 ≤ p * x.1 - c x + φ x.2) ↔
      (p ≤ cq x ∧ (0 < x.1 → p = cq x)) ∧ (dφ x.2 ≤ ch x ∧ (0 < x.2 → dφ x.2 = ch x)) := by
  obtain ⟨q₀, h₀⟩ := x
  obtain ⟨lq, lh⟩ := lines_deriv (hc (q₀, h₀))
  constructor
  · intro hmax
    have d1 : HasDerivAt (fun q => p * q - c (q, h₀) + φ h₀) (p - cq (q₀, h₀)) q₀ := by
      have h2 : HasDerivAt (fun q => p * q) p q₀ := by simpa using (hasDerivAt_id q₀).const_mul p
      exact (h2.sub lq).add_const _
    have d2 : HasDerivAt (fun h => p * q₀ - c (q₀, h) + φ h) (0 - ch (q₀, h₀) + dφ h₀) h₀ :=
      ((hasDerivAt_const h₀ (p * q₀)).sub lh).add (hφ h₀)
    have n1 := foc_max_necessary d1.hasDerivWithinAt hx.1
      (fun y hy => by simpa using hmax (y, h₀) ⟨hy, hx.2⟩)
    have n2 := foc_max_necessary d2.hasDerivWithinAt hx.2
      (fun y hy => by simpa using hmax (q₀, y) ⟨hx.1, hy⟩)
    simp only [zero_sub] at n1 n2
    exact ⟨⟨by linarith [n1.1], fun hp => by linarith [n1.2 hp]⟩,
      ⟨by linarith [n2.1], fun hp => by linarith [n2.2 hp]⟩⟩
  · rintro ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ ⟨q, h⟩ hy
    have ht := convex_tangent hconv hx hy (hc (q₀, h₀))
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', Prod.fst_sub, Prod.snd_sub,
      smul_eq_mul] at ht
    have hφt := foc_tangent_le (fun z _ => (hφ z).hasDerivWithinAt) hdφ hx.2 hy.2
    have t1 : (p - cq (q₀, h₀)) * (q - q₀) ≤ 0 := by
      rcases eq_or_lt_of_le hx.1 with h0 | hp
      · simp only at h0
        exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith [hy.1])
      · rw [show p - cq (q₀, h₀) = 0 by linarith [a2 hp], zero_mul]
    have t2 : (dφ h₀ - ch (q₀, h₀)) * (h - h₀) ≤ 0 := by
      rcases eq_or_lt_of_le hx.2 with h0 | hp
      · simp only at h0
        exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith [hy.2])
      · rw [show dφ h₀ - ch (q₀, h₀) = 0 by linarith [b2 hp], zero_mul]
    simp only at hφt ⊢
    nlinarith

/-- **Exercise 11.B.5(c)** (MWG, p. 379). An output tax cannot restore efficiency: if the Pareto
optimum has `h° > 0` and `φ'(h°) < 0`, then for no output tax `τ` is `(q°, h°)` the firm's choice.
A direct tax `t = -φ'(h°)` on the externality makes `(q°, h°)` the firm's choice. -/
theorem exercise_11_B_5c {c : ℝ × ℝ → ℝ} {cq ch : ℝ × ℝ → ℝ} {φ dφ : ℝ → ℝ}
    (hc : ∀ x, HasFDerivAt c (cq x • ContinuousLinearMap.fst ℝ ℝ ℝ +
      ch x • ContinuousLinearMap.snd ℝ ℝ ℝ) x) (hconv : ConvexOn ℝ quadrant c)
    (hφ : ∀ x, HasDerivAt φ (dφ x) x) (hdφ : AntitoneOn dφ (Set.Ici 0)) (p : ℝ) {x : ℝ × ℝ}
    (hx : x ∈ quadrant)
    (hopt : ∀ y ∈ quadrant, p * y.1 - c y + φ y.2 ≤ p * x.1 - c x + φ x.2) :
    (0 < x.2 → dφ x.2 < 0 → ∀ τ,
      ¬ ∀ y ∈ quadrant, (p - τ) * y.1 - c y - 0 * y.2 ≤ (p - τ) * x.1 - c x - 0 * x.2) ∧
      ∀ y ∈ quadrant, (p - 0) * y.1 - c y - (-dφ x.2) * y.2 ≤
        (p - 0) * x.1 - c x - (-dφ x.2) * x.2 := by
  have hb := (exercise_11_B_5b hc hconv hφ hdφ p hx).1 hopt
  refine ⟨fun hpos hneg τ hmax => ?_, ?_⟩
  · have hf := (exercise_11_B_5_firm hc hconv p τ 0 hx).1 hmax
    have := hb.2.2 hpos
    linarith [hf.2.1]
  · refine (exercise_11_B_5_firm hc hconv p 0 _ hx).2 ⟨⟨by linarith [hb.1.1],
      fun hp => by linarith [hb.1.2 hp]⟩, ⟨by linarith [hb.2.1], fun hp => by linarith [hb.2.2 hp]⟩⟩

/-- **Exercise 11.B.5(d)** (MWG, p. 379). With fixed proportions `h = αq` (`α > 0`), the firm's cost
is `C(q) = c(q, αq)` (convex, derivative `C'`). If `q°` maximizes `pq - C(q) + φ(αq)` on `ℝ₊`, the
output tax `τ = -α φ'(αq°)` makes `q°` the firm's choice: `max (p - τ)q - C(q)`. -/
theorem exercise_11_B_5d {C dC φ dφ : ℝ → ℝ} {α : ℝ} (hα : 0 < α)
    (hC : ∀ x, HasDerivAt C (dC x) x) (hCm : MonotoneOn dC (Set.Ici 0))
    (hφ : ∀ x, HasDerivAt φ (dφ x) x) (hdφ : AntitoneOn dφ (Set.Ici 0)) (p : ℝ) {qo : ℝ}
    (hopt : 0 ≤ qo ∧ ∀ q, 0 ≤ q → p * q - C q + φ (α * q) ≤ p * qo - C qo + φ (α * qo)) :
    ∀ q, 0 ≤ q → (p - -(α * dφ (α * qo))) * q - C q ≤ (p - -(α * dφ (α * qo))) * qo - C qo := by
  have hP : ∀ x, HasDerivAt (fun q => p * q - C q + φ (α * q)) (p - dC x + α * dφ (α * x)) x :=
    fun x => by
      have h1 : HasDerivAt (fun q => φ (α * q)) (dφ (α * x) * α) x :=
        (hφ (α * x)).comp x (by simpa using (hasDerivAt_id x).const_mul α)
      have h2 : HasDerivAt (fun q => p * q) p x := by simpa using (hasDerivAt_id x).const_mul p
      have := (h2.sub (hC x)).add h1
      convert this using 1; ring
  have hPa : AntitoneOn (fun x => p - dC x + α * dφ (α * x)) (Set.Ici 0) := by
    intro a ha b hb hab
    have h1 := hCm ha hb hab
    have h2 := hdφ (show 0 ≤ α * a from mul_nonneg hα.le ha) (show 0 ≤ α * b from
      mul_nonneg hα.le hb) (mul_le_mul_of_nonneg_left hab hα.le)
    simp only
    nlinarith
  have hkt := (kt_max_iff hP hPa hopt.1).1 hopt.2
  set τ := -(α * dφ (α * qo))
  have hF : ∀ x, HasDerivAt (fun q => (p - τ) * q - C q) (p - τ - dC x) x := fun x => by
    have h2 : HasDerivAt (fun q => (p - τ) * q) (p - τ) x := by
      simpa using (hasDerivAt_id x).const_mul (p - τ)
    exact h2.sub (hC x)
  have hFa : AntitoneOn (fun x => p - τ - dC x) (Set.Ici 0) := fun a ha b hb hab => by
    have := hCm ha hb hab; simp only; linarith
  refine (kt_max_iff hF hFa hopt.1).2 ⟨hopt.1, ?_, fun hp => ?_⟩
  · have := hkt.2.1; simp only [τ] at this ⊢; linarith
  · have := hkt.2.2 hp; simp only [τ] at this ⊢; linarith

/-- An instance of Exercise 11.B.5: `c(q, h) = q²/2 + (h - q)²/2`, `φ(h) = -h`, `p = 4`. The Pareto
optimum is `(q°, h°) = (3, 2)`; the unregulated firm chooses `(4, 4)`. -/
theorem exercise_11_B_5_instance :
    ConvexOn ℝ quadrant (fun x : ℝ × ℝ => x.1 ^ 2 / 2 + (x.2 - x.1) ^ 2 / 2) ∧
      (∀ y ∈ quadrant, 4 * y.1 - (y.1 ^ 2 / 2 + (y.2 - y.1) ^ 2 / 2) + -y.2 ≤
        4 * 3 - ((3 : ℝ) ^ 2 / 2 + (2 - 3) ^ 2 / 2) + -2) ∧
      (∀ y ∈ quadrant, 4 * y.1 - (y.1 ^ 2 / 2 + (y.2 - y.1) ^ 2 / 2) ≤
        4 * 4 - ((4 : ℝ) ^ 2 / 2 + (4 - 4) ^ 2 / 2)) := by
  refine ⟨⟨convex_quadrant, fun x _ y _ a b ha hb hab => ?_⟩, fun y _ => ?_, fun y _ => ?_⟩
  · simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, smul_eq_mul]
    have hb' : b = 1 - a := by linarith
    subst hb'
    nlinarith [mul_nonneg ha hb, sq_nonneg (x.1 - y.1), sq_nonneg (x.2 - x.1 - (y.2 - y.1)),
      mul_nonneg (mul_nonneg ha hb) (sq_nonneg (x.1 - y.1)),
      mul_nonneg (mul_nonneg ha hb) (sq_nonneg (x.2 - x.1 - (y.2 - y.1)))]
  · nlinarith [sq_nonneg (y.1 - 3), sq_nonneg (y.2 - y.1 + 1)]
  · nlinarith [sq_nonneg (y.1 - 4), sq_nonneg (y.2 - y.1)]

end MWG.ExternalitiesPublicGoods

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercise 11.C.3: Ramsey taxation with a public good (MWG, p. 379)

The government chooses commodity taxes `t = (t₂, …, t_L)` (here `t : Fin n → ℝ`) and the level
`x₀` of a public good produced at cost `c(x₀)`, maximizing aggregate surplus `W(t, x₀)` subject to
budget balance `G(t, x₀) = ∑ₗ tₗ xₗ - c(x₀) = 0` (Exercise 10.E.3 with a public good). With
quasilinear utilities `x₁ᵢ + ∑ₗ φₗᵢ(xₗᵢ, x₀)`, consumers equate `∂φₗᵢ/∂xₗᵢ` to the consumer price,
so (envelope argument, as in Exercise 10.E.3, Chapter 10's `exercise_10_E_3b_marginal`)
`∂W/∂tₗ = tₗ ∂xₗ/∂tₗ` and `∂W/∂x₀ = MB + ∑ₗ tₗ ∂xₗ/∂x₀ - c'(x₀)` with `MB = ∑ᵢ∑ₗ ∂φₗᵢ/∂x₀`;
and `∂G/∂tₗ = xₗ + tₗ ∂xₗ/∂tₗ`, `∂G/∂x₀ = ∑ₗ tₗ ∂xₗ/∂x₀ - c'(x₀)`. We take these derivatives as the
data and derive the optimality conditions from Mathlib's Lagrange multiplier theorem:

* the **Ramsey conditions** `tₗ ∂xₗ/∂tₗ = λ (xₗ + tₗ ∂xₗ/∂tₗ)` (so `(1 - λ) tₗ ∂xₗ/∂tₗ = λ xₗ`, the
  inverse-elasticity rule of Exercise 10.E.3), and
* the **modified Samuelson condition** `MB = (1 - λ)(c'(x₀) - ∑ₗ tₗ ∂xₗ/∂x₀)`: the marginal benefit
  of the public good equals its marginal cost, net of the extra tax revenue it generates through
  complementarity with taxed goods, scaled by the marginal cost of public funds `1 - λ`
  (`exercise_11_C_3`). The two problems interact through `λ` and the revenue terms
  `∑ₗ tₗ ∂xₗ/∂x₀`.
-/

namespace MWG.ExternalitiesPublicGoods

/-- The linear functional `∑ₗ uₗ dtₗ + w dx₀` on `(t, x₀)`. -/
noncomputable def taxPGForm {n : ℕ} (u : Fin n → ℝ) (w : ℝ) :
    (Fin n → ℝ) × ℝ →L[ℝ] ℝ :=
  ∑ l, u l • (ContinuousLinearMap.proj l).comp (ContinuousLinearMap.fst ℝ (Fin n → ℝ) ℝ) +
    w • ContinuousLinearMap.snd ℝ (Fin n → ℝ) ℝ

theorem taxPGForm_single {n : ℕ} (u : Fin n → ℝ) (w : ℝ) (l : Fin n) :
    taxPGForm u w (Pi.single l 1, 0) = u l := by
  simp [taxPGForm, Pi.single_apply]

theorem taxPGForm_snd {n : ℕ} (u : Fin n → ℝ) (w : ℝ) : taxPGForm u w (0, 1) = w := by
  simp [taxPGForm]

/-- **Exercise 11.C.3** (MWG, p. 379). At a local maximum of `W` on the budget-balance set, if
the budget constraint is qualified (its gradient is not zero), there is a multiplier `λ` with the
Ramsey conditions for every taxed good and the modified Samuelson condition for the public good. -/
theorem exercise_11_C_3 {n : ℕ} (W G : (Fin n → ℝ) × ℝ → ℝ) (v₀ : (Fin n → ℝ) × ℝ)
    (t X sX xX : Fin n → ℝ) (MB dc : ℝ)
    (hW : HasStrictFDerivAt W (taxPGForm (fun l => t l * sX l) (MB + ∑ l, t l * xX l - dc)) v₀)
    (hG : HasStrictFDerivAt G (taxPGForm (fun l => X l + t l * sX l)
      (∑ l, t l * xX l - dc)) v₀)
    (hmax : IsLocalMaxOn W {v | G v = G v₀} v₀)
    (hqual : (∃ l, X l + t l * sX l ≠ 0) ∨ ∑ l, t l * xX l - dc ≠ 0) :
    ∃ lam : ℝ, (∀ l, t l * sX l = lam * (X l + t l * sX l)) ∧
      MB + ∑ l, t l * xX l - dc = lam * (∑ l, t l * xX l - dc) ∧
      (∀ l, (1 - lam) * (t l * sX l) = lam * X l) ∧
      MB = (1 - lam) * (dc - ∑ l, t l * xX l) := by
  obtain ⟨a, b, hab, hlin⟩ :=
    IsLocalExtrOn.exists_multipliers_of_hasStrictFDerivAt_1d (Or.inr hmax) hG hW
  have hcoord : ∀ l, a * (X l + t l * sX l) + b * (t l * sX l) = 0 := fun l => by
    have := congrArg (fun L => L (Pi.single l 1, 0)) hlin
    simpa [taxPGForm_single] using this
  have hsnd : a * (∑ l, t l * xX l - dc) + b * (MB + ∑ l, t l * xX l - dc) = 0 := by
    have := congrArg (fun L => L (0, 1)) hlin
    simpa [taxPGForm_snd] using this
  have hb : b ≠ 0 := by
    intro hb0
    have ha : a ≠ 0 := fun ha0 => hab (by rw [ha0, hb0]; rfl)
    rcases hqual with ⟨l, hl⟩ | h
    · have := hcoord l
      rw [hb0, zero_mul, add_zero] at this
      exact hl ((mul_eq_zero.1 this).resolve_left ha)
    · rw [hb0, zero_mul, add_zero] at hsnd
      exact h ((mul_eq_zero.1 hsnd).resolve_left ha)
  refine ⟨-a / b, fun l => ?_, ?_, fun l => ?_, ?_⟩
  · have := hcoord l; field_simp; linarith
  · field_simp; linarith
  · have := hcoord l; field_simp; linarith
  · field_simp; linarith

/-- A (degenerate) instance of the hypotheses of `exercise_11_C_3`: one taxed good with zero tax,
demand `1`, welfare locally constant, budget `G(t, x₀) = t`. -/
theorem exercise_11_C_3_instance :
    ∃ lam : ℝ, (∀ _l : Fin 1, (0 : ℝ) * 0 = lam * (1 + 0 * 0)) ∧
      (0 : ℝ) + ∑ _l : Fin 1, (0 : ℝ) * 0 - 0 = lam * (∑ _l : Fin 1, (0 : ℝ) * 0 - 0) ∧
      (∀ _l : Fin 1, (1 - lam) * ((0 : ℝ) * 0) = lam * 1) ∧
      (0 : ℝ) = (1 - lam) * (0 - ∑ _l : Fin 1, (0 : ℝ) * 0) := by
  have hG : HasStrictFDerivAt (taxPGForm (fun _ : Fin 1 => (1 : ℝ)) 0)
      (taxPGForm (fun l => (fun _ : Fin 1 => (1 : ℝ)) l + (fun _ => (0 : ℝ)) l *
        (fun _ => (0 : ℝ)) l) (∑ l, (fun _ : Fin 1 => (0 : ℝ)) l * (fun _ => (0 : ℝ)) l - 0))
      (0 : (Fin 1 → ℝ) × ℝ) := by
    simpa using (taxPGForm (fun _ : Fin 1 => (1 : ℝ)) 0).hasStrictFDerivAt
  have hW : HasStrictFDerivAt (fun _ : (Fin 1 → ℝ) × ℝ => (0 : ℝ))
      (taxPGForm (fun l => (fun _ : Fin 1 => (0 : ℝ)) l * (fun _ => (0 : ℝ)) l)
        (0 + ∑ l, (fun _ : Fin 1 => (0 : ℝ)) l * (fun _ => (0 : ℝ)) l - 0))
      (0 : (Fin 1 → ℝ) × ℝ) := by
    have h0 : taxPGForm (fun l => (fun _ : Fin 1 => (0 : ℝ)) l * (fun _ => (0 : ℝ)) l)
        (0 + ∑ l, (fun _ : Fin 1 => (0 : ℝ)) l * (fun _ => (0 : ℝ)) l - 0) = 0 := by
      ext v <;> simp [taxPGForm]
    rw [h0]
    exact hasStrictFDerivAt_const _ _
  exact exercise_11_C_3 _ _ 0 (fun _ => 0) (fun _ => 1) (fun _ => 0) (fun _ => 0) 0 0 hW hG
    (Filter.Eventually.of_forall fun _ => le_rfl) (Or.inl ⟨0, by norm_num⟩)

end MWG.ExternalitiesPublicGoods

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercises 11.D.1-11.D.2 (MWG, p. 379-380)

* **Exercise 11.D.1** (Weitzman's students). `n ≥ 2` students choose hours `hᵢ > 0`; payoffs
  `φ(hᵢ/h̄) - hᵢ²/2` with `h̄` the class average, `φ` concave with `φ' > 0`. The game is a Chapter 7
  normal form and equilibrium is Chapter 8's `IsNashEquilibrium`. A symmetric profile `(h, …, h)`
  is a Nash equilibrium iff `h² = φ'(1)(n - 1)/n` (`exercise_11_D_1`); every symmetric profile,
  in particular the equilibrium, is Pareto dominated by the symmetric profile with half the hours
  (`exercise_11_D_1_pareto`): there is no Pareto optimal symmetric outcome with `h > 0`, the
  symmetric payoff `φ(1) - h²/2` increasing as `h ↓ 0`. The assumption `φ'(0+) = ∞` is not needed.
* **Exercise 11.D.2** (agents who both generate and experience the externality). Utilities
  `φᵢ(hᵢ, ∑ₖ hₖ) + wᵢ`, `φᵢ` concave and differentiable with partials `aᵢ = ∂₁φᵢ`, `bᵢ = ∂₂φᵢ`.
  Optimal levels: `aⱼ + ∑ᵢ bᵢ ≤ 0`, equality if `hⱼ > 0` (`exercise_11_D_2_opt`); equilibrium:
  `aᵢ + bᵢ ≤ tᵢ` (`exercise_11_D_2_eq`); the per-unit tax `tᵢ = -∑_{k ≠ i} bₖ` makes the optimum
  an equilibrium (`exercise_11_D_2_tax`).
-/

namespace MWG.ExternalitiesPublicGoods

open MWG.CompetitiveMarkets MWG.NoncooperativeGames MWG.SimultaneousMoveGames Function

/-! ## Exercise 11.D.1 -/

/-- **Exercise 11.D.1** (MWG, p. 379). The students' game: student `i` chooses hours `hᵢ > 0`
and receives `φ(hᵢ/h̄) - hᵢ²/2`, `h̄ = (1/n) ∑ⱼ hⱼ`. -/
noncomputable def studentGame (n : ℕ) (φ : ℝ → ℝ) :
    NormalForm (Fin n) (fun _ => {h : ℝ // 0 < h}) where
  payoff i s := φ ((s i : ℝ) / ((∑ j, (s j : ℝ)) / n)) - (s i : ℝ) ^ 2 / 2

/-- The payoff of a student who deviates to `x` when all others work `h`. -/
theorem student_dev {n : ℕ} (hn : 1 ≤ n) (φ : ℝ → ℝ) {h x : ℝ} (hh : 0 < h) (hx : 0 < x)
    (i : Fin n) :
    (studentGame n φ).payoff i (update (fun _ => ⟨h, hh⟩) i ⟨x, hx⟩) =
      φ (n * x / (x + (n - 1) * h)) - x ^ 2 / 2 := by
  have hs : ∑ j, ((update (fun _ : Fin n => (⟨h, hh⟩ : {h : ℝ // 0 < h})) i ⟨x, hx⟩ j : ℝ)) =
      x + (n - 1) * h := by
    have : ∀ j, ((update (fun _ : Fin n => (⟨h, hh⟩ : {h : ℝ // 0 < h})) i ⟨x, hx⟩ j : ℝ)) =
        update (fun _ : Fin n => h) i x j := fun j => by
      rcases eq_or_ne j i with hj | hj
      · subst hj; simp
      · simp [update_of_ne hj]
    simp_rw [this]
    rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
    simp only [Finset.sum_const, Finset.card_sdiff, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    rw [Finset.inter_univ, Finset.card_singleton, Nat.cast_sub hn, Nat.cast_one]
  simp only [studentGame, update_self, hs]
  congr 2
  have hpos : 0 < x + (n - 1) * h := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  field_simp

/-- **Exercise 11.D.1** (MWG, pp. 379-380). With `n ≥ 2` students, `φ` differentiable with
decreasing `φ'` on `[0, ∞)` and `φ'(1) > 0`, the symmetric profile `(h, …, h)`, `h > 0`, is a Nash
equilibrium iff `h² = φ'(1)(n - 1)/n`. -/
theorem exercise_11_D_1 {n : ℕ} (hn : 2 ≤ n) {φ dφ : ℝ → ℝ} (hφ : ∀ x, HasDerivAt φ (dφ x) x)
    (hanti : AntitoneOn dφ (Set.Ici 0)) (hpos : 0 < dφ 1) {h : ℝ} (hh : 0 < h) :
    IsNashEquilibrium (studentGame n φ) (fun _ => ⟨h, hh⟩) ↔ h ^ 2 = dφ 1 * (n - 1) / n := by
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := (by linarith : (0 : ℝ) < n).ne'
  set f : ℝ → ℝ := fun x => φ (n * x / (x + (n - 1) * h)) - x ^ 2 / 2 with hf
  have hr1 : (n : ℝ) * h / (h + (n - 1) * h) = 1 := by
    rw [div_eq_one_iff_eq (by nlinarith)]; ring
  have hfh : f h = φ 1 - h ^ 2 / 2 := by
    simp only [f, hr1]
  have hself : ∀ i : Fin n, (studentGame n φ).payoff i (fun _ => ⟨h, hh⟩) = f h := fun i => by
    have := student_dev hn1 φ hh hh i
    rw [update_eq_self_iff.2 rfl] at this
    rw [this]
  constructor
  · intro hne
    have i : Fin n := ⟨0, by omega⟩
    have hle : ∀ x, 0 < x → f x ≤ f h := fun x hx => by
      have := hne i ⟨x, hx⟩
      rw [student_dev hn1 φ hh hx, hself] at this
      exact this
    -- the derivative of `f` at `h`
    have hden : HasDerivAt (fun x => x + (n - 1) * h) 1 h := by
      simpa using (hasDerivAt_id h).add_const ((n - 1) * h)
    have hnum : HasDerivAt (fun x => (n : ℝ) * x) n h := by
      simpa using (hasDerivAt_id h).const_mul (n : ℝ)
    have hpos' : h + (n - 1) * h ≠ 0 := by nlinarith
    have hr := hnum.div hden hpos'
    have hφ1 : HasDerivAt φ (dφ 1) ((n : ℝ) * h / (h + (n - 1) * h)) := by rw [hr1]; exact hφ 1
    have hcomp := hφ1.comp h hr
    have hfd := hcomp.sub ((hasDerivAt_pow 2 h).div_const 2)
    have hloc : IsLocalMax f h := by
      filter_upwards [Ioi_mem_nhds hh] with x hx using hle x hx
    have h0 := hloc.hasDerivAt_eq_zero hfd
    have hden2 : h + (n - 1) * h = n * h := by ring
    have hq : ((n : ℝ) * (h + (n - 1) * h) - n * h * 1) / (h + (n - 1) * h) ^ 2 =
        (n - 1) / (n * h) := by
      rw [hden2, div_eq_div_iff (by positivity) (by positivity)]; ring
    rw [hq] at h0
    norm_num at h0
    have h1 : dφ 1 * (n - 1) = h ^ 2 * n := by
      have : dφ 1 * ((n - 1) / (n * h)) = h := by linarith
      field_simp at this
      linarith
    rw [eq_div_iff hn0]
    linarith
  · intro hfoc i t
    obtain ⟨x, hx⟩ := t
    rw [student_dev hn1 φ hh hx, hself]
    have hn0 : (0 : ℝ) < n := by linarith
    have hden : 0 < x + (n - 1) * h := by nlinarith
    have hr0 : 0 ≤ n * x / (x + (n - 1) * h) := by positivity
    have htan := foc_tangent_le (fun z _ => (hφ z).hasDerivWithinAt) hanti zero_le_one hr0
    -- the ratio lies below its tangent at `x = h`
    have hrat : n * x / (x + (n - 1) * h) - 1 ≤ (n - 1) * (x - h) / (n * h) := by
      rw [div_sub_one hden.ne', div_le_div_iff₀ hden (by positivity)]
      nlinarith [sq_nonneg (x - h), mul_nonneg (by linarith : (0 : ℝ) ≤ n - 1)
        (sq_nonneg (x - h))]
    have hkey : dφ 1 * ((n - 1) * (x - h) / (n * h)) = h * (x - h) := by
      have : dφ 1 * (n - 1) = h ^ 2 * n := by
        rw [hfoc]; field_simp
      field_simp
      nlinarith
    have : dφ 1 * (n * x / (x + (n - 1) * h) - 1) ≤ h * (x - h) := by
      rw [← hkey]; exact mul_le_mul_of_nonneg_left hrat hpos.le
    nlinarith [sq_nonneg (x - h)]

/-- **Exercise 11.D.1**, the comparison with Pareto optimality. At a symmetric profile every
student gets `φ(1) - h²/2`; halving the hours makes every student strictly better off. So the
equilibrium is inefficient (too much work), and no symmetric profile with `h > 0` is Pareto
optimal. -/
theorem exercise_11_D_1_pareto {n : ℕ} (hn : 1 ≤ n) (φ : ℝ → ℝ) {h : ℝ} (hh : 0 < h)
    (i : Fin n) :
    (studentGame n φ).payoff i (fun _ => ⟨h, hh⟩) = φ 1 - h ^ 2 / 2 ∧
      (studentGame n φ).payoff i (fun _ => ⟨h, hh⟩) <
        (studentGame n φ).payoff i (fun _ => ⟨h / 2, half_pos hh⟩) := by
  have hsym : ∀ (y : ℝ) (hy : 0 < y),
      (studentGame n φ).payoff i (fun _ => ⟨y, hy⟩) = φ 1 - y ^ 2 / 2 := fun y hy => by
    simp only [studentGame, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hn0 : (n : ℝ) ≠ 0 := by have : (1 : ℝ) ≤ n := by exact_mod_cast hn
                                 positivity
    congr 2
    field_simp
  rw [hsym, hsym]
  exact ⟨rfl, by nlinarith⟩

/-- An instance of Exercise 11.D.1: `φ(x) = 2x - x²/4` is concave with `φ'(1) = 3/2 > 0`; with
`n = 3` students the symmetric equilibrium has `h = 1` (`1 = (3/2)(2/3)`). -/
theorem exercise_11_D_1_instance :
    IsNashEquilibrium (studentGame 3 fun x => 2 * x - x ^ 2 / 4) (fun _ => ⟨1, one_pos⟩) := by
  have hφ : ∀ x : ℝ, HasDerivAt (fun x => 2 * x - x ^ 2 / 4) (2 - x / 2) x := fun x => by
    have h' := ((hasDerivAt_id x).const_mul 2).sub ((hasDerivAt_pow 2 x).div_const 4)
    exact (h'.congr_deriv (by simp only [Nat.cast_ofNat]; ring) :
      HasDerivAt (fun x : ℝ => 2 * x - x ^ 2 / 4) (2 - x / 2) x)
  refine (exercise_11_D_1 (by norm_num) hφ (fun a _ b _ hab => by linarith) (by norm_num)
    one_pos).2 ?_
  norm_num

/-! ## Exercise 11.D.2 -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The aggregate surplus of Exercise 11.D.2: `∑ᵢ φᵢ(hᵢ, ∑ₖ hₖ)`. -/
def d2Obj (φ : ι → ℝ × ℝ → ℝ) (h : ι → ℝ) : ℝ := ∑ i, φ i (h i, ∑ k, h k)

omit [DecidableEq ι] in
theorem d2Obj_concave (φ : ι → ℝ × ℝ → ℝ) (hconc : ∀ i, ConcaveOn ℝ Set.univ (φ i)) :
    ConcaveOn ℝ (orthant ι) (d2Obj φ) := by
  refine ⟨convex_orthant ι, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [d2Obj, smul_eq_mul]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have := (hconc i).2 (Set.mem_univ (x i, ∑ k, x k)) (Set.mem_univ (y i, ∑ k, y k)) ha hb hab
  simp only [smul_eq_mul, Prod.smul_mk, Prod.mk_add_mk] at this
  convert this using 2
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, Finset.mul_sum]

/-- The derivative of the aggregate surplus: its `j`-th partial is `aⱼ + ∑ᵢ bᵢ`. -/
theorem d2Obj_hasFDerivAt (φ : ι → ℝ × ℝ → ℝ) (a b : ι → ℝ × ℝ → ℝ)
    (hφ : ∀ i x, HasFDerivAt (φ i) (a i x • ContinuousLinearMap.fst ℝ ℝ ℝ +
      b i x • ContinuousLinearMap.snd ℝ ℝ ℝ) x) (h : ι → ℝ) :
    ∃ L : (ι → ℝ) →L[ℝ] ℝ, HasFDerivAt (d2Obj φ) L h ∧
      ∀ j, L (Pi.single j 1) = a j (h j, ∑ k, h k) + ∑ i, b i (h i, ∑ k, h k) := by
  set Li : ι → (ι → ℝ) →L[ℝ] ℝ × ℝ := fun i =>
    (ContinuousLinearMap.proj i).prod (∑ k, ContinuousLinearMap.proj k)
  have hLi : ∀ i (g : ι → ℝ), Li i g = (g i, ∑ k, g k) := fun i g => by
    simp [Li]
  set L := ∑ i, (a i (Li i h) • ContinuousLinearMap.fst ℝ ℝ ℝ +
    b i (Li i h) • ContinuousLinearMap.snd ℝ ℝ ℝ).comp (Li i)
  refine ⟨L, ?_, fun j => ?_⟩
  · have hterm : ∀ i ∈ (Finset.univ : Finset ι), HasFDerivAt (fun g => φ i (Li i g))
        ((a i (Li i h) • ContinuousLinearMap.fst ℝ ℝ ℝ +
          b i (Li i h) • ContinuousLinearMap.snd ℝ ℝ ℝ).comp (Li i)) h := fun i _ =>
      (hφ i (Li i h)).comp h (Li i).hasFDerivAt
    have := HasFDerivAt.fun_sum hterm
    have e : (fun g => ∑ i, φ i (Li i g)) = d2Obj φ := funext fun g => by simp only [hLi, d2Obj]
    rw [e] at this
    exact this
  · simp [L, hLi, Pi.single_apply, Finset.sum_add_distrib]

omit [DecidableEq ι] in
/-- **Exercise 11.D.2** (MWG, p. 380), optimal levels: `h ≥ 0` maximizes `∑ᵢ φᵢ(hᵢ, ∑ₖ hₖ)` iff for
every `j`, `∂₁φⱼ + ∑ᵢ ∂₂φᵢ ≤ 0`, with equality if `hⱼ > 0`. -/
theorem exercise_11_D_2_opt (φ : ι → ℝ × ℝ → ℝ) (a b : ι → ℝ × ℝ → ℝ)
    (hφ : ∀ i x, HasFDerivAt (φ i) (a i x • ContinuousLinearMap.fst ℝ ℝ ℝ +
      b i x • ContinuousLinearMap.snd ℝ ℝ ℝ) x) (hconc : ∀ i, ConcaveOn ℝ Set.univ (φ i))
    {h : ι → ℝ} (hh : h ∈ orthant ι) :
    (∀ y ∈ orthant ι, d2Obj φ y ≤ d2Obj φ h) ↔
      ∀ j, a j (h j, ∑ k, h k) + ∑ i, b i (h i, ∑ k, h k) ≤ 0 ∧
        (0 < h j → a j (h j, ∑ k, h k) + ∑ i, b i (h i, ∑ k, h k) = 0) := by
  classical
  obtain ⟨L, hL, hLe⟩ := d2Obj_hasFDerivAt φ a b hφ h
  rw [orthant_kt_iff (d2Obj_concave φ hconc) hh hL]
  simp only [hLe]

/-- One-variable Kuhn-Tucker for a concave function on `[0, ∞)`. -/
theorem concave1_kt_iff {g : ℝ → ℝ} (hg : ConcaveOn ℝ (Set.Ici 0) g) {d x : ℝ}
    (hd : HasDerivAt g d x) (hx : 0 ≤ x) :
    (∀ y, 0 ≤ y → g y ≤ g x) ↔ d ≤ 0 ∧ (0 < x → d = 0) := by
  constructor
  · intro hmax
    exact foc_max_necessary hd.hasDerivWithinAt hx hmax
  · rintro ⟨h1, h2⟩ y hy
    have ht := concave_tangent hg (Set.mem_Ici.2 hx) (Set.mem_Ici.2 hy) hd.hasFDerivAt
    have e : (ContinuousLinearMap.toSpanSingleton ℝ d) (y - x) = (y - x) * d := by simp
    rw [e] at ht
    rcases eq_or_lt_of_le hx with h0 | hp
    · rw [← h0] at ht ⊢
      nlinarith
    · rw [h2 hp] at ht; linarith

omit [Fintype ι] [DecidableEq ι] in
/-- Consumer `i`'s own payoff `x ↦ φᵢ(x, x + R) - t x` is concave with derivative
`∂₁φᵢ + ∂₂φᵢ - t`. -/
theorem d2_own (φ : ℝ × ℝ → ℝ) (a b : ℝ × ℝ → ℝ)
    (hφ : ∀ x, HasFDerivAt φ (a x • ContinuousLinearMap.fst ℝ ℝ ℝ +
      b x • ContinuousLinearMap.snd ℝ ℝ ℝ) x) (hconc : ConcaveOn ℝ Set.univ φ) (R t x : ℝ) :
    ConcaveOn ℝ (Set.Ici 0) (fun y => φ (y, y + R) - t * y) ∧
      HasDerivAt (fun y => φ (y, y + R) - t * y) (a (x, x + R) + b (x, x + R) - t) x := by
  constructor
  · refine ⟨convex_Ici 0, fun y _ z _ α β hα hβ hαβ => ?_⟩
    have := hconc.2 (Set.mem_univ (y, y + R)) (Set.mem_univ (z, z + R)) hα hβ hαβ
    simp only [smul_eq_mul, Prod.smul_mk, Prod.mk_add_mk] at this ⊢
    have e : α * (y + R) + β * (z + R) = α * y + β * z + R := by
      linear_combination R * hαβ
    rw [e] at this
    nlinarith
  · have hpath : HasDerivAt (fun y => (y, y + R)) ((1 : ℝ), (1 : ℝ)) x :=
      (hasDerivAt_id x).prodMk ((hasDerivAt_id x).add_const R)
    have h1 := (hφ (x, x + R)).comp_hasDerivAt x hpath
    have h2 : HasDerivAt (fun y => t * y) t x := by simpa using (hasDerivAt_id x).const_mul t
    have := h1.sub h2
    simp only [add_apply, smul_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', smul_eq_mul, mul_one] at this
    exact this

/-- An equilibrium with per-unit taxes `tᵢ` (Exercise 11.D.2): each consumer chooses `hᵢ ≥ 0` to
maximize `φᵢ(hᵢ, hᵢ + ∑_{k ≠ i} hₖ) - tᵢ hᵢ` given the others' choices. -/
def IsD2Eq (φ : ι → ℝ × ℝ → ℝ) (t : ι → ℝ) (h : ι → ℝ) : Prop :=
  ∀ i, 0 ≤ h i ∧ ∀ y, 0 ≤ y → φ i (y, y + (∑ k, h k - h i)) - t i * y ≤
    φ i (h i, h i + (∑ k, h k - h i)) - t i * h i

omit [DecidableEq ι] in
/-- **Exercise 11.D.2**, equilibrium levels: `h ≥ 0` is an equilibrium with taxes `t` iff
`∂₁φᵢ + ∂₂φᵢ ≤ tᵢ` at `(hᵢ, ∑ₖ hₖ)`, with equality if `hᵢ > 0` (with `t = 0`: the unfettered
equilibrium, which ignores the effect `∑_{k ≠ i} ∂₂φₖ` on others). -/
theorem exercise_11_D_2_eq (φ : ι → ℝ × ℝ → ℝ) (a b : ι → ℝ × ℝ → ℝ)
    (hφ : ∀ i x, HasFDerivAt (φ i) (a i x • ContinuousLinearMap.fst ℝ ℝ ℝ +
      b i x • ContinuousLinearMap.snd ℝ ℝ ℝ) x) (hconc : ∀ i, ConcaveOn ℝ Set.univ (φ i))
    (t : ι → ℝ) {h : ι → ℝ} (hh : h ∈ orthant ι) :
    IsD2Eq φ t h ↔ ∀ i, a i (h i, ∑ k, h k) + b i (h i, ∑ k, h k) - t i ≤ 0 ∧
      (0 < h i → a i (h i, ∑ k, h k) + b i (h i, ∑ k, h k) - t i = 0) := by
  refine forall_congr' fun i => ?_
  obtain ⟨hc, hd⟩ := d2_own (φ i) (a i) (b i) (hφ i) (hconc i) (∑ k, h k - h i) (t i) (h i)
  have key := concave1_kt_iff hc hd (hh i)
  have e : h i + (∑ k, h k - h i) = ∑ k, h k := by ring
  rw [e] at key
  constructor
  · rintro ⟨_, hmax⟩
    exact key.1 (by simpa only [e] using hmax)
  · intro hk
    exact ⟨hh i, by simpa only [e] using key.2 hk⟩

omit [DecidableEq ι] in
/-- **Exercise 11.D.2**, the corrective tax: `tᵢ = -∑_{k ≠ i} ∂₂φₖ(hₖ°, ∑ h°)` makes the optimum
`h°` an equilibrium. -/
theorem exercise_11_D_2_tax (φ : ι → ℝ × ℝ → ℝ) (a b : ι → ℝ × ℝ → ℝ)
    (hφ : ∀ i x, HasFDerivAt (φ i) (a i x • ContinuousLinearMap.fst ℝ ℝ ℝ +
      b i x • ContinuousLinearMap.snd ℝ ℝ ℝ) x) (hconc : ∀ i, ConcaveOn ℝ Set.univ (φ i))
    {h : ι → ℝ} (hh : h ∈ orthant ι) (hopt : ∀ y ∈ orthant ι, d2Obj φ y ≤ d2Obj φ h) :
    IsD2Eq φ (fun i => -(∑ k, b k (h k, ∑ m, h m) - b i (h i, ∑ m, h m))) h := by
  have hfoc := (exercise_11_D_2_opt φ a b hφ hconc hh).1 hopt
  rw [exercise_11_D_2_eq φ a b hφ hconc _ hh]
  intro i
  exact ⟨by linarith [(hfoc i).1], fun hp => by linarith [(hfoc i).2 hp]⟩

end MWG.ExternalitiesPublicGoods

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercises 11.D.3-11.D.4 (MWG, p. 380)

* **Exercise 11.D.3** (learning by doing). `J > 1` identical price-taking firms with cost
  `c(qⱼ, Q)`, `Q = ∑ qⱼ`, `c_Q < 0`. With partial derivatives `c_q, c_Q` and second partials
  `c_qq, c_qQ, c_QQ`, the industry cost `C(Q) = J c(Q/J, Q)` has marginal social cost
  `MSC(Q) = c_q + J c_Q` (`exercise_11_D_3_msc`), whose derivative is
  `(1/J) c_qq + 2 c_qQ + J c_QQ`, positive by MWG's condition for `n = J`
  (`exercise_11_D_3_msc_deriv`). The symmetric equilibrium output `Q*` (price = private marginal
  cost `c_q(Q*/J, Q*)`) is below the optimal `Q°` (price = `MSC(Q°)`) (`exercise_11_D_3`); the
  per-unit subsidy `s = -J c_Q(Q°/J, Q°) > 0` makes `Q°` an equilibrium
  (`exercise_11_D_3_subsidy`); welfare `∫₀^Q P - C(Q)` is maximized at `Q°`
  (`exercise_11_D_3_optimal`). The conditions `c_q + J c_Q > 0` and the `n = 1` second-order
  condition are not needed for these conclusions.
* **Exercise 11.D.4** (nonhomogeneous externalities). Consumer utilities `φᵢ(h₁, …, h_J)`,
  concave and differentiable: `h°` is optimal iff `∑ᵢ ∂φᵢ/∂hⱼ ≤ -πⱼ'(hⱼ)`, equality if `hⱼ > 0`
  (`exercise_11_D_4_opt`); firm-specific taxes `tⱼ = -∑ᵢ ∂φᵢ/∂hⱼ(h°)` restore efficiency
  (`exercise_11_D_4_tax`); a uniform rate suffices (at an interior optimum) iff the marginal
  damages `∑ᵢ ∂φᵢ/∂hⱼ(h°)` are equal across firms (`exercise_11_D_4_uniform`), as in the
  homogeneous case of Section 11.D.
-/

namespace MWG.ExternalitiesPublicGoods

open MWG.CompetitiveMarkets

/-! ## Exercise 11.D.3 -/

/-- Evaluating `u • fst + v • snd` on `ℝ × ℝ`. -/
theorem clm2_apply (u v : ℝ) (w : ℝ × ℝ) :
    (u • ContinuousLinearMap.fst ℝ ℝ ℝ + v • ContinuousLinearMap.snd ℝ ℝ ℝ) w =
      u * w.1 + v * w.2 := by
  simp

/-- **Exercise 11.D.3**: the industry cost `C(Q) = J c(Q/J, Q)` of producing `Q` symmetrically
has derivative `c_q(Q/J, Q) + J c_Q(Q/J, Q)`, the marginal social cost. -/
theorem exercise_11_D_3_msc {c cq cQ : ℝ × ℝ → ℝ} {J : ℝ} (hJ : J ≠ 0)
    (hc : ∀ x, HasFDerivAt c (cq x • ContinuousLinearMap.fst ℝ ℝ ℝ +
      cQ x • ContinuousLinearMap.snd ℝ ℝ ℝ) x) (Q : ℝ) :
    HasDerivAt (fun Q => J * c (Q / J, Q)) (cq (Q / J, Q) + J * cQ (Q / J, Q)) Q := by
  have hpath : HasDerivAt (fun Q : ℝ => (Q / J, Q)) (1 / J, (1 : ℝ)) Q :=
    ((hasDerivAt_id Q).div_const J).prodMk (hasDerivAt_id Q)
  have h' := ((hc (Q / J, Q)).comp_hasDerivAt (f := fun Q : ℝ => (Q / J, Q)) Q hpath).const_mul J
  rw [clm2_apply] at h'
  exact (h'.congr_deriv (by field_simp) :
    HasDerivAt (fun Q => J * c (Q / J, Q)) (cq (Q / J, Q) + J * cQ (Q / J, Q)) Q)

/-- **Exercise 11.D.3**: the derivative of the marginal social cost is
`(1/J) c_qq + 2 c_qQ + J c_QQ` (with symmetric second partials). -/
theorem exercise_11_D_3_msc_deriv {cq cQ cqq cqQ cQQ : ℝ × ℝ → ℝ} {J : ℝ} (hJ : J ≠ 0)
    (hcq : ∀ x, HasFDerivAt cq (cqq x • ContinuousLinearMap.fst ℝ ℝ ℝ +
      cqQ x • ContinuousLinearMap.snd ℝ ℝ ℝ) x)
    (hcQ : ∀ x, HasFDerivAt cQ (cqQ x • ContinuousLinearMap.fst ℝ ℝ ℝ +
      cQQ x • ContinuousLinearMap.snd ℝ ℝ ℝ) x) (Q : ℝ) :
    HasDerivAt (fun Q => cq (Q / J, Q) + J * cQ (Q / J, Q))
      ((1 / J) * cqq (Q / J, Q) + 2 * cqQ (Q / J, Q) + J * cQQ (Q / J, Q)) Q := by
  have hpath : HasDerivAt (fun Q : ℝ => (Q / J, Q)) (1 / J, (1 : ℝ)) Q :=
    ((hasDerivAt_id Q).div_const J).prodMk (hasDerivAt_id Q)
  have h' := ((hcq (Q / J, Q)).comp_hasDerivAt (f := fun Q : ℝ => (Q / J, Q)) Q hpath).add
    (((hcQ (Q / J, Q)).comp_hasDerivAt (f := fun Q : ℝ => (Q / J, Q)) Q hpath).const_mul J)
  rw [clm2_apply, clm2_apply] at h'
  exact (h'.congr_deriv (by field_simp; ring) :
    HasDerivAt (fun Q => cq (Q / J, Q) + J * cQ (Q / J, Q))
      ((1 / J) * cqq (Q / J, Q) + 2 * cqQ (Q / J, Q) + J * cQQ (Q / J, Q)) Q)

/-- **Exercise 11.D.3** (MWG, p. 380), the comparison. Let `P` (inverse demand) be strictly
decreasing, `MSC = c_q + J c_Q` strictly increasing (MWG's second-order condition for `n = J`),
and `c_Q < 0`. If `Q*` is a symmetric competitive equilibrium (`P(Q*) = c_q(Q*/J, Q*)`) and `Q°`
satisfies `P(Q°) = MSC(Q°)`, then `Q* < Q°`: learning by doing is underexploited. -/
theorem exercise_11_D_3 {P : ℝ → ℝ} {cq cQ : ℝ × ℝ → ℝ} {J Qs Qo : ℝ}
    (hP : StrictAnti P) (hmsc : StrictMono fun Q => cq (Q / J, Q) + J * cQ (Q / J, Q))
    (hJ : 0 < J) (hcQ : ∀ x, cQ x < 0) (heq : P Qs = cq (Qs / J, Qs))
    (hopt : P Qo = cq (Qo / J, Qo) + J * cQ (Qo / J, Qo)) : Qs < Qo := by
  by_contra hle
  push Not at hle
  rcases eq_or_lt_of_le hle with h | h
  · rw [h] at hopt
    have := mul_neg_of_pos_of_neg hJ (hcQ (Qs / J, Qs))
    linarith
  · have h1 := hP h
    have h2 := hmsc h
    have := mul_neg_of_pos_of_neg hJ (hcQ (Qs / J, Qs))
    simp only at h2
    linarith

/-- **Exercise 11.D.3**: the per-unit subsidy `s = -J c_Q(Q°/J, Q°) > 0` restores efficiency: at
`Q°` the subsidized equilibrium condition `P(Q°) + s = c_q(Q°/J, Q°)` holds. -/
theorem exercise_11_D_3_subsidy {P : ℝ → ℝ} {cq cQ : ℝ × ℝ → ℝ} {J Qo : ℝ} (hJ : 0 < J)
    (hcQ : cQ (Qo / J, Qo) < 0) (hopt : P Qo = cq (Qo / J, Qo) + J * cQ (Qo / J, Qo)) :
    0 < -(J * cQ (Qo / J, Qo)) ∧ P Qo + -(J * cQ (Qo / J, Qo)) = cq (Qo / J, Qo) := by
  have := mul_neg_of_pos_of_neg hJ hcQ
  exact ⟨by linarith, by linarith⟩

/-- **Exercise 11.D.3**: with continuous strictly decreasing inverse demand `P` and convex
industry cost (increasing `MSC`), `Q° ≥ 0` with `P(Q°) ≤ MSC(Q°)` (equality if `Q° > 0`)
maximizes the aggregate surplus `∫₀^Q P - J c(Q/J, Q)` over `Q ≥ 0`. -/
theorem exercise_11_D_3_optimal {P : ℝ → ℝ} {c cq cQ : ℝ × ℝ → ℝ} {J Qo : ℝ} (hJ : J ≠ 0)
    (hPc : Continuous P) (hP : Antitone P)
    (hc : ∀ x, HasFDerivAt c (cq x • ContinuousLinearMap.fst ℝ ℝ ℝ +
      cQ x • ContinuousLinearMap.snd ℝ ℝ ℝ) x)
    (hmsc : Monotone fun Q => cq (Q / J, Q) + J * cQ (Q / J, Q))
    (hfoc : IsFOCSol (fun Q => P Q - (cq (Q / J, Q) + J * cQ (Q / J, Q))) 0 Qo) :
    ∀ Q, 0 ≤ Q → (∫ x in (0 : ℝ)..Q, P x) - J * c (Q / J, Q) ≤
      (∫ x in (0 : ℝ)..Qo, P x) - J * c (Qo / J, Qo) := by
  have hW : ∀ Q, HasDerivAt (fun Q => (∫ x in (0 : ℝ)..Q, P x) - J * c (Q / J, Q))
      (P Q - (cq (Q / J, Q) + J * cQ (Q / J, Q))) Q := fun Q =>
    (intervalIntegral.integral_hasDerivAt_right (hPc.intervalIntegrable _ _)
      hPc.aestronglyMeasurable.stronglyMeasurableAtFilter hPc.continuousAt).sub
      (exercise_11_D_3_msc hJ hc Q)
  have hanti : AntitoneOn (fun Q => P Q - (cq (Q / J, Q) + J * cQ (Q / J, Q))) (Set.Ici 0) :=
    fun a _ b _ hab => by
      have := hP hab; have := hmsc hab; simp only at *; linarith
  exact (kt_max_iff hW hanti hfoc.1).2 hfoc

/-! ## Exercise 11.D.4 -/

variable {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι]

/-- The aggregate surplus of Exercise 11.D.4: `∑ᵢ φᵢ(h) + ∑ⱼ πⱼ(hⱼ)`. -/
def d4Obj (φ : ι → (κ → ℝ) → ℝ) (pr : κ → ℝ → ℝ) (h : κ → ℝ) : ℝ :=
  ∑ i, φ i h + ∑ j, pr j (h j)

omit [DecidableEq κ] in
theorem d4Obj_concave (φ : ι → (κ → ℝ) → ℝ) (pr dpr : κ → ℝ → ℝ)
    (hconc : ∀ i, ConcaveOn ℝ (orthant κ) (φ i)) (hpr : ∀ j x, HasDerivAt (pr j) (dpr j x) x)
    (hdpr : ∀ j, AntitoneOn (dpr j) (Set.Ici 0)) : ConcaveOn ℝ (orthant κ) (d4Obj φ pr) := by
  refine ⟨convex_orthant κ, fun x hx y hy a b ha hb hab => ?_⟩
  simp only [d4Obj, smul_eq_mul]
  have h1 : ∀ i, a * φ i x + b * φ i y ≤ φ i (a • x + b • y) := fun i =>
    (hconc i).2 hx hy ha hb hab
  have h2 : ∀ j, a * pr j (x j) + b * pr j (y j) ≤ pr j (a * x j + b * y j) := fun j => by
    have hcj : ConcaveOn ℝ (Set.Ici 0) (pr j) := by
      refine ⟨convex_Ici 0, fun u hu v hv α β hα hβ hαβ => ?_⟩
      have t1 := foc_tangent_le (fun z _ => (hpr j z).hasDerivWithinAt) (hdpr j)
        (show 0 ≤ α * u + β * v by have := hu.out; have := hv.out; positivity) hu
      have t2 := foc_tangent_le (fun z _ => (hpr j z).hasDerivWithinAt) (hdpr j)
        (show 0 ≤ α * u + β * v by have := hu.out; have := hv.out; positivity) hv
      simp only [smul_eq_mul]
      have hb' : β = 1 - α := by linarith
      subst hb'
      nlinarith
    exact hcj.2 (Set.mem_Ici.2 (hx j)) (Set.mem_Ici.2 (hy j)) ha hb hab
  have s1 := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => h1 i
  have s2 := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => h2 j
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at s1 s2
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [mul_add, mul_add]
  linarith

/-- **Exercise 11.D.4** (MWG, p. 380). With consumer utilities `φᵢ(h₁, …, h_J)` concave on the
orthant with derivatives `Dφᵢ(h)` and concave profits, `h ≥ 0` is optimal iff for every firm `j`,
`∑ᵢ ∂φᵢ/∂hⱼ(h) ≤ -πⱼ'(hⱼ)`, with equality if `hⱼ > 0`. -/
theorem exercise_11_D_4_opt (φ : ι → (κ → ℝ) → ℝ) (Dφ : ι → (κ → ℝ) →L[ℝ] ℝ)
    (pr dpr : κ → ℝ → ℝ) {h : κ → ℝ} (hφ : ∀ i, HasFDerivAt (φ i) (Dφ i) h)
    (hconc : ∀ i, ConcaveOn ℝ (orthant κ) (φ i)) (hpr : ∀ j x, HasDerivAt (pr j) (dpr j x) x)
    (hdpr : ∀ j, AntitoneOn (dpr j) (Set.Ici 0)) (hh : h ∈ orthant κ) :
    (∀ y ∈ orthant κ, d4Obj φ pr y ≤ d4Obj φ pr h) ↔
      ∀ j, ∑ i, Dφ i (Pi.single j 1) ≤ -dpr j (h j) ∧
        (0 < h j → ∑ i, Dφ i (Pi.single j 1) = -dpr j (h j)) := by
  set L : (κ → ℝ) →L[ℝ] ℝ :=
    ∑ i, Dφ i + ∑ j, dpr j (h j) • ContinuousLinearMap.proj (R := ℝ) j with hLdef
  have hL : HasFDerivAt (d4Obj φ pr) L h := by
    have h1 := HasFDerivAt.fun_sum (u := Finset.univ) fun i _ => hφ i
    have h2 := HasFDerivAt.fun_sum (u := Finset.univ) fun j (_ : j ∈ Finset.univ) =>
      ((hpr j (h j)).hasFDerivAt.comp h (hasFDerivAt_apply j h) :
        HasFDerivAt (fun g : κ → ℝ => pr j (g j)) _ h)
    have := h1.add h2
    convert this using 1
    · rfl
    · rw [hLdef]
      ext v
      simp [mul_comm]
  rw [orthant_kt_iff (d4Obj_concave φ pr dpr hconc hpr hdpr) hh hL]
  refine forall_congr' fun j => ?_
  have hLj : L (Pi.single j 1) = ∑ i, Dφ i (Pi.single j 1) + dpr j (h j) := by
    simp [L, Pi.single_apply]
  rw [hLj]
  constructor
  · rintro ⟨a, b⟩; exact ⟨by linarith, fun hp => by linarith [b hp]⟩
  · rintro ⟨a, b⟩; exact ⟨by linarith, fun hp => by linarith [b hp]⟩

omit [Fintype κ] [DecidableEq κ] [Fintype ι] in
/-- **Exercise 11.D.4**: firm `j` facing the per-unit tax `tⱼ` chooses `hⱼ` with `πⱼ'(hⱼ) ≤ tⱼ`
(equality if `hⱼ > 0`); this is the only choice when `πⱼ'` is strictly decreasing. -/
theorem firm_tax_iff {pr dpr : ℝ → ℝ} (hpr : ∀ x, HasDerivAt pr (dpr x) x)
    (hdpr : StrictAntiOn dpr (Set.Ici 0)) (t y : ℝ) :
    (0 ≤ y ∧ ∀ z, 0 ≤ z → pr z - t * z ≤ pr y - t * y) ↔ IsFOCSol dpr t y := by
  have hf : ∀ x, HasDerivAt (fun y => pr y - t * y) (dpr x - t) x := fun x => by
    have h2 : HasDerivAt (fun y => t * y) t x := by simpa using (hasDerivAt_id x).const_mul t
    exact (hpr x).sub h2
  have hanti : AntitoneOn (fun x => dpr x - t) (Set.Ici 0) := fun a ha b hb hab => by
    have := hdpr.antitoneOn ha hb hab; simp only; linarith
  rw [kt_isMax_iff hf hanti]
  simp only [IsFOCSol]
  constructor
  · rintro ⟨a, b, c⟩; exact ⟨a, by linarith, fun hp => by linarith [c hp]⟩
  · rintro ⟨a, b, c⟩; exact ⟨a, by linarith, fun hp => by linarith [c hp]⟩

/-- **Exercise 11.D.4**: the firm-specific taxes `tⱼ = -∑ᵢ ∂φᵢ/∂hⱼ(h°)` make `h°ⱼ` each firm's
(unique) choice. -/
theorem exercise_11_D_4_tax (φ : ι → (κ → ℝ) → ℝ) (Dφ : ι → (κ → ℝ) →L[ℝ] ℝ)
    (pr dpr : κ → ℝ → ℝ) {h : κ → ℝ} (hφ : ∀ i, HasFDerivAt (φ i) (Dφ i) h)
    (hconc : ∀ i, ConcaveOn ℝ (orthant κ) (φ i)) (hpr : ∀ j x, HasDerivAt (pr j) (dpr j x) x)
    (hdpr : ∀ j, StrictAntiOn (dpr j) (Set.Ici 0)) (hh : h ∈ orthant κ)
    (hopt : ∀ y ∈ orthant κ, d4Obj φ pr y ≤ d4Obj φ pr h) (j : κ) (y : ℝ) :
    (0 ≤ y ∧ ∀ z, 0 ≤ z → pr j z - (-∑ i, Dφ i (Pi.single j 1)) * z ≤
      pr j y - (-∑ i, Dφ i (Pi.single j 1)) * y) ↔ y = h j := by
  have hfoc := ((exercise_11_D_4_opt φ Dφ pr dpr hφ hconc hpr
    (fun j => (hdpr j).antitoneOn) hh).1 hopt) j
  have hj : IsFOCSol (dpr j) (-∑ i, Dφ i (Pi.single j 1)) (h j) :=
    ⟨hh j, by linarith [hfoc.1], fun hp => by linarith [hfoc.2 hp]⟩
  rw [firm_tax_iff (hpr j) (hdpr j)]
  exact ⟨fun hy => isFOCSol_unique (hdpr j) hy hj, fun hy => hy ▸ hj⟩

/-- **Exercise 11.D.4**: when should every firm face the same rate? At an optimum with all
`hⱼ° > 0`, a uniform tax `t` implements `h°` (each firm's choice is `hⱼ°`) iff the marginal
damages `-∑ᵢ ∂φᵢ/∂hⱼ(h°)` all equal `t`. -/
theorem exercise_11_D_4_uniform (φ : ι → (κ → ℝ) → ℝ) (Dφ : ι → (κ → ℝ) →L[ℝ] ℝ)
    (pr dpr : κ → ℝ → ℝ) {h : κ → ℝ} (hφ : ∀ i, HasFDerivAt (φ i) (Dφ i) h)
    (hconc : ∀ i, ConcaveOn ℝ (orthant κ) (φ i)) (hpr : ∀ j x, HasDerivAt (pr j) (dpr j x) x)
    (hdpr : ∀ j, StrictAntiOn (dpr j) (Set.Ici 0)) (hh : ∀ j, 0 < h j)
    (hopt : ∀ y ∈ orthant κ, d4Obj φ pr y ≤ d4Obj φ pr h) (t : ℝ) :
    (∀ j, IsFOCSol (dpr j) t (h j)) ↔ ∀ j, -∑ i, Dφ i (Pi.single j 1) = t := by
  have hfoc := (exercise_11_D_4_opt φ Dφ pr dpr hφ hconc hpr
    (fun j => (hdpr j).antitoneOn) (fun j => (hh j).le)).1 hopt
  constructor
  · intro ht j
    have := (ht j).2.2 (hh j)
    linarith [(hfoc j).2 (hh j)]
  · intro ht j
    exact ⟨(hh j).le, by linarith [ht j, (hfoc j).2 (hh j)], fun _ => by
      linarith [ht j, (hfoc j).2 (hh j)]⟩

end MWG.ExternalitiesPublicGoods

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercises 11.D.5-11.D.7 (MWG, pp. 380-381)

* **Exercise 11.D.5** (the problem of the commons). `f(b)` fish from `b` boats, `f' > 0`, `f'`
  strictly decreasing, and `f(0) = 0` (no boats, no fish; assumed, MWG leaves it implicit).
  (a) Free entry: `p f(b*)/b* = r` (`IsCommonsEq`); (b) the optimum: `p f'(b°) ≤ r`, equality if
  `b° > 0` (`exercise_11_D_5b`), and `b° < b*` (`exercise_11_D_5_compare`); (c) the per-boat tax
  `τ = p f(b°)/b° - r` makes `b°` the unique entry equilibrium (`exercise_11_D_5c`); (d) a single
  owner chooses `b°` (`exercise_11_D_5d`). An instance with `f(b) = 1 - e^{-b}`.
* **Exercise 11.D.6** (bargaining coalitions). `π(h) = α + βh - μh²`, `φ(h) = γ - ηh`, `I` consumers
  with `φ(h)/I + w` each. A coalition of `k` consumers (fraction `θ = k/I`) offers the firm
  `h(θ) = (β - θη)/(2μ)` and the payment that leaves it at `π(β/(2μ))` (`exercise_11_D_6_offer`).
  Staying in is optimal iff `k ≤ 2` and staying out iff `k ≥ 1` (`exercise_11_D_6_stay`,
  `exercise_11_D_6_join`). So with `I = 1` the coalition forms and `h° = h(1)` results; for `I ≥ 2`
  the equilibria are `k ∈ {1, 2}`, `θ ∈ {1/I, 2/I}`. **Correction**: for `I = 2`, `θ = 1` is an
  equilibrium, so "`θ < 1` when `I > 1`" fails at `I = 2`; it holds for `I ≥ 3`, where too much of
  the externality results (`exercise_11_D_6a`). (b) Equilibrium `θ ≤ 2/I → 0` (`exercise_11_D_6b`).
* **Exercise 11.D.7** (neighborhood prestige). (a) Everyone in `A` is never an equilibrium; everyone
  in `B` is not an equilibrium when a lone mover to `A` gets her own prestige, but is one if the
  empty neighborhood is assigned prestige `0` (correction: the claim depends on that convention).
  (b) With different prestige levels the richer-prestige neighborhood is `A` and the allocation is a
  cutoff; the cutoff equilibrium has `θ̂ = 2(c_A - c_B) - 1`. (c) Raising the cutoff slightly makes
  every type strictly better off.
-/

namespace MWG.ExternalitiesPublicGoods

open MWG.CompetitiveMarkets

/-! ## Exercise 11.D.5 -/

/-- Average product exceeds marginal product: for `b > 0`, `f(b)/b > f'(b)` (`f(0) = 0`, `f'`
strictly decreasing). -/
theorem avg_gt_marginal {f df : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (df x) x)
    (hanti : StrictAntiOn df (Set.Ici 0)) (h0 : f 0 = 0) {b : ℝ} (hb : 0 < b) :
    df b < f b / b ∧ f b / b < df 0 := by
  obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope f df hb
    (fun x _ => (hf x).continuousAt.continuousWithinAt) (fun x _ => hf x)
  rw [h0, sub_zero, sub_zero] at hξeq
  rw [← hξeq]
  exact ⟨hanti (Set.mem_Ici.2 hξ.1.le) (Set.mem_Ici.2 hb.le) hξ.2,
    hanti (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hξ.1.le) hξ.1⟩

/-- The average product `f(b)/b` is strictly decreasing on `(0, ∞)`. -/
theorem avg_strictAnti {f df : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (df x) x)
    (hanti : StrictAntiOn df (Set.Ici 0)) (h0 : f 0 = 0) :
    StrictAntiOn (fun b => f b / b) (Set.Ioi 0) := by
  intro a ha b hb hab
  have ha' : (0 : ℝ) < a := ha
  have hb' : (0 : ℝ) < b := hb
  -- `f(b) - f(a) = f'(ξ)(b - a)` with `f'(ξ) < f'(a) < f(a)/a`
  obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope f df hab
    (fun x _ => (hf x).continuousAt.continuousWithinAt) (fun x _ => hf x)
  have h1 : df ξ < df a := hanti (Set.mem_Ici.2 ha'.le) (Set.mem_Ici.2 (ha'.le.trans hξ.1.le)) hξ.1
  have h2 := (avg_gt_marginal hf hanti h0 ha').1
  have hfb : f b = f a + df ξ * (b - a) := by
    rw [hξeq]; field_simp [(sub_pos.2 hab).ne']; ring
  simp only
  rw [div_lt_div_iff₀ hb' ha', hfb]
  rw [lt_div_iff₀ ha'] at h2
  nlinarith [mul_lt_mul_of_pos_right h1 (sub_pos.2 hab)]

/-- **Exercise 11.D.5(a)** (MWG, p. 380). A free-entry equilibrium number of boats: either
`b* > 0` and each boat's catch value equals its cost, `p f(b*)/b* = r`, or no boat would earn
`r`: `b* = 0` and `p f'(0) ≤ r`. -/
def IsCommonsEq (f df : ℝ → ℝ) (p r b : ℝ) : Prop :=
  (0 < b ∧ p * (f b / b) = r) ∨ (b = 0 ∧ p * df 0 ≤ r)

/-- **Exercise 11.D.5(b)** (MWG, p. 380). The optimal number of boats maximizes `p f(b) - r b` on
`b ≥ 0`: iff `p f'(b°) ≤ r`, with equality if `b° > 0`. -/
theorem exercise_11_D_5b {f df : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (df x) x)
    (hanti : StrictAntiOn df (Set.Ici 0)) {p r : ℝ} (hp : 0 < p) (b : ℝ) :
    (0 ≤ b ∧ ∀ y, 0 ≤ y → p * f y - r * y ≤ p * f b - r * b) ↔
      0 ≤ b ∧ p * df b ≤ r ∧ (0 < b → p * df b = r) := by
  have hg : ∀ x, HasDerivAt (fun y => p * f y - r * y) (p * df x - r) x := fun x => by
    have h2 : HasDerivAt (fun y => r * y) r x := by simpa using (hasDerivAt_id x).const_mul r
    exact ((hf x).const_mul p).sub h2
  have hga : AntitoneOn (fun x => p * df x - r) (Set.Ici 0) := fun a ha b hb hab => by
    have := hanti.antitoneOn ha hb hab; simp only; nlinarith
  rw [kt_isMax_iff hg hga]
  simp only [IsFOCSol]
  constructor
  · rintro ⟨a, b, c⟩; exact ⟨a, by linarith, fun h => by linarith [c h]⟩
  · rintro ⟨a, b, c⟩; exact ⟨a, by linarith, fun h => by linarith [c h]⟩

/-- **Exercise 11.D.5(a)-(b), the comparison.** At an interior free-entry equilibrium too many
boats are sent out: `b° < b*` (the entrant ignores the catch she takes from the others). -/
theorem exercise_11_D_5_compare {f df : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (df x) x)
    (hanti : StrictAntiOn df (Set.Ici 0)) (h0 : f 0 = 0) {p r bs bo : ℝ} (hp : 0 < p)
    (hbs : 0 < bs) (heq : p * (f bs / bs) = r)
    (hopt : 0 ≤ bo ∧ p * df bo ≤ r ∧ (0 < bo → p * df bo = r)) : bo < bs := by
  rcases eq_or_lt_of_le hopt.1 with h | hbo
  · rw [← h]; exact hbs
  · by_contra hle
    push Not at hle
    have h1 := (avg_gt_marginal hf hanti h0 hbs).1
    have h2 : df bo ≤ df bs := hanti.antitoneOn (Set.mem_Ici.2 hbs.le) (Set.mem_Ici.2 hbo.le) hle
    have := hopt.2.2 hbo
    nlinarith

/-- **Exercise 11.D.5(c)** (MWG, p. 380). With `b° > 0`, the per-boat tax
`τ = p f(b°)/b° - r > 0` makes `b°` the unique interior free-entry equilibrium:
`p f(b)/b = r + τ` iff `b = b°`. -/
theorem exercise_11_D_5c {f df : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (df x) x)
    (hanti : StrictAntiOn df (Set.Ici 0)) (h0 : f 0 = 0) {p r bo : ℝ} (hp : 0 < p)
    (hbo : 0 < bo) (hfoc : p * df bo = r) :
    0 < p * (f bo / bo) - r ∧
      ∀ b, 0 < b → (p * (f b / b) = r + (p * (f bo / bo) - r) ↔ b = bo) := by
  refine ⟨by have := (avg_gt_marginal hf hanti h0 hbo).1; nlinarith, fun b hb => ⟨fun h => ?_,
    fun h => by rw [h]; ring⟩⟩
  have hav : f b / b = f bo / bo := by
    have : p * (f b / b) = p * (f bo / bo) := by linarith
    exact mul_left_cancel₀ hp.ne' this
  exact (avg_strictAnti hf hanti h0).injOn hb hbo hav

/-- **Exercise 11.D.5(d)** (MWG, p. 380). A single owner of the lake chooses `b` to maximize her
profit `p f(b) - r b`, i.e. exactly the optimal number of boats. -/
theorem exercise_11_D_5d (f : ℝ → ℝ) (p r b : ℝ) :
    (0 ≤ b ∧ ∀ y, 0 ≤ y → p * f y - r * y ≤ p * f b - r * b) ↔
      (0 ≤ b ∧ ∀ y, 0 ≤ y → p * f y - r * y ≤ p * f b - r * b) := Iff.rfl

/-- An instance of Exercise 11.D.5: `f(b) = 1 - e^{-b}`, `p = 2`, `r = 1`. The optimum is
`b° = log 2`, and a free-entry equilibrium `b* ∈ (1, 2)` exists. -/
theorem exercise_11_D_5_instance :
    (∀ x, HasDerivAt (fun b => 1 - Real.exp (-b)) (Real.exp (-x)) x) ∧
      StrictAntiOn (fun x => Real.exp (-x)) (Set.Ici 0) ∧ (1 - Real.exp (-0) = 0) ∧
      (0 ≤ Real.log 2 ∧ 2 * Real.exp (-Real.log 2) ≤ 1 ∧
        (0 < Real.log 2 → 2 * Real.exp (-Real.log 2) = 1)) ∧
      ∃ bs, 1 < bs ∧ bs < 2 ∧ 2 * ((1 - Real.exp (-bs)) / bs) = 1 := by
  have hd : ∀ x, HasDerivAt (fun b => 1 - Real.exp (-b)) (Real.exp (-x)) x := fun x => by
    have := ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).const_sub 1
    simpa using this
  have e2 : 2 * Real.exp (-Real.log 2) = 1 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  refine ⟨hd, fun a _ b _ hab => Real.exp_lt_exp.2 (by linarith), by simp,
    ⟨(Real.log_pos (by norm_num)).le, e2.le, fun _ => e2⟩, ?_⟩
  -- intermediate value theorem for `g(b) = 2(1 - e^{-b}) - b` on `[1, 2]`
  have hcont : ContinuousOn (fun b : ℝ => 2 * (1 - Real.exp (-b)) - b) (Set.Icc 1 2) :=
    ((continuous_const.mul (continuous_const.sub (Real.continuous_exp.comp
      continuous_neg))).sub continuous_id).continuousOn
  have hg1 : 0 < 2 * (1 - Real.exp (-1)) - 1 := by
    have : Real.exp (-1) < 1 / 2 := by
      rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos 1) (by norm_num)]
      have := Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)
      linarith
    linarith
  have hg2 : 2 * (1 - Real.exp (-2)) - 2 < 0 := by
    have := Real.exp_pos (-2); linarith
  obtain ⟨bs, hbs, hbs0⟩ := intermediate_value_Icc' (by norm_num : (1 : ℝ) ≤ 2) hcont
    ⟨hg2.le, hg1.le⟩
  have hne1 : bs ≠ 1 := fun h => by rw [h] at hbs0; linarith
  have hne2 : bs ≠ 2 := fun h => by rw [h] at hbs0; linarith
  refine ⟨bs, lt_of_le_of_ne hbs.1 (Ne.symm hne1), lt_of_le_of_ne hbs.2 hne2, ?_⟩
  have hpos : 0 < bs := by linarith [hbs.1]
  simp only at hbs0
  field_simp
  linarith

/-! ## Exercise 11.D.6 -/

/-- The data of Exercise 11.D.6: `π(h) = α + βh - μh²`, `φ(h) = γ - ηh`. -/
structure LandModel where
  α : ℝ
  β : ℝ
  μ : ℝ
  γ : ℝ
  η : ℝ
  hμ : 0 < μ
  hη : 0 < η
  hβη : η ≤ β

namespace LandModel

variable (L : LandModel)

/-- The firm's profit. -/
def prof (h : ℝ) : ℝ := L.α + L.β * h - L.μ * h ^ 2

/-- The total land yield. -/
def yld (h : ℝ) : ℝ := L.γ - L.η * h

/-- The coalition's choice of `h` when it holds the fraction `θ`. -/
noncomputable def hθ (θ : ℝ) : ℝ := (L.β - θ * L.η) / (2 * L.μ)

/-- The payment to the firm: its loss relative to its unconstrained choice `β/(2μ)`. -/
noncomputable def pay (θ : ℝ) : ℝ := L.prof (L.β / (2 * L.μ)) - L.prof (L.hθ θ)

/-- **Exercise 11.D.6** (MWG, p. 380), the subgame after membership. A coalition holding the
fraction `θ ∈ [0, 1]` offers `(h, T)` maximizing `θφ(h) - T` subject to the firm's acceptance
`π(h) + T ≥ π(β/(2μ))`: the offer is `h = h(θ) = (β - θη)/(2μ)`, `T = π(β/(2μ)) - π(h(θ))`. -/
theorem exercise_11_D_6_offer {θ : ℝ} (hθ1 : θ ≤ 1) (h T : ℝ) :
    IsTIOLIOffer (Set.Ici 0) (fun h => θ * L.yld h) L.prof (L.prof (L.β / (2 * L.μ))) h (-T) ↔
      h = L.hθ θ ∧ T = L.pay θ := by
  rw [tioli_iff]
  have hθpos : 0 ≤ L.hθ θ := by
    simp only [hθ]
    apply div_nonneg _ (by linarith [L.hμ])
    nlinarith [L.hη, L.hβη]
  have key : ∀ y, θ * L.yld y + L.prof y =
      θ * L.γ + L.α - L.μ * (y - L.hθ θ) ^ 2 + L.μ * L.hθ θ ^ 2 := fun y => by
    simp only [yld, prof, hθ]; field_simp [L.hμ.ne']; ring
  simp only [Set.mem_Ici, key]
  constructor
  · rintro ⟨h0, hmax, hT⟩
    have := hmax (L.hθ θ) hθpos
    have hh : h = L.hθ θ := by
      have : L.μ * (h - L.hθ θ) ^ 2 ≤ 0 := by nlinarith
      have h2 : (h - L.hθ θ) ^ 2 = 0 := le_antisymm (by
        by_contra hc; push Not at hc; nlinarith [L.hμ]) (sq_nonneg _)
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h2
      linarith
    refine ⟨hh, ?_⟩
    rw [pay, ← hh]; linarith
  · rintro ⟨rfl, hT⟩
    refine ⟨hθpos, fun y _ => by nlinarith [sq_nonneg (y - L.hθ θ), L.hμ], ?_⟩
    rw [hT, pay]; ring

/-- A member's payoff in a coalition of `k ≥ 1` of the `I` consumers: her share `φ(h)/I` of the
yield less her share `T/k` of the payment. -/
noncomputable def memberPay (I k : ℕ) : ℝ := L.yld (L.hθ (k / I)) / I - L.pay (k / I) / k

/-- A non-member's payoff when the coalition has `k` members. -/
noncomputable def outPay (I k : ℕ) : ℝ := L.yld (L.hθ (k / I)) / I

/-- **Exercise 11.D.6**: a member of a `k`-coalition gains `(η²/(4μI²))(2 - k)` by staying in
rather than leaving (so the coalition shrinks to `k - 1`). -/
theorem exercise_11_D_6_stay (I k : ℕ) (hI : 0 < I) (hk : 1 ≤ k) :
    L.memberPay I k - L.outPay I (k - 1) = L.η ^ 2 / (4 * L.μ * I ^ 2) * (2 - k) := by
  have hI' : (I : ℝ) ≠ 0 := by positivity
  have hk' : (k : ℝ) ≠ 0 := (by exact_mod_cast (show 0 < k by omega) : (0 : ℝ) < k).ne'
  simp only [memberPay, outPay, pay, prof, yld, hθ, Nat.cast_sub hk, Nat.cast_one]
  field_simp [L.hμ.ne']
  ring

/-- **Exercise 11.D.6**: a non-member of a `k`-coalition gains `(η²/(4μI²))(1 - k)` by joining. -/
theorem exercise_11_D_6_join (I k : ℕ) (hI : 0 < I) :
    L.memberPay I (k + 1) - L.outPay I k = L.η ^ 2 / (4 * L.μ * I ^ 2) * (1 - k) := by
  have := L.exercise_11_D_6_stay I (k + 1) hI (by omega)
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] at this
  rw [this]; ring

/-- A subgame-perfect equilibrium membership size `k ∈ {0, …, I}`: no member wants to leave and
no non-member wants to join. -/
def IsMembershipEq (I k : ℕ) : Prop :=
  k ≤ I ∧ (1 ≤ k → L.outPay I (k - 1) ≤ L.memberPay I k) ∧
    (k < I → L.memberPay I (k + 1) ≤ L.outPay I k)

/-- The equilibrium membership sizes are `k ∈ {1, 2}` (intersected with `{0, …, I}`). -/
theorem membershipEq_iff (I k : ℕ) (hI : 0 < I) :
    L.IsMembershipEq I k ↔ k ≤ I ∧ (1 ≤ k → k ≤ 2) ∧ (k < I → 1 ≤ k) := by
  have hc : 0 < L.η ^ 2 / (4 * L.μ * I ^ 2) := by
    have := L.hμ; have := L.hη; positivity
  simp only [IsMembershipEq]
  refine and_congr Iff.rfl (and_congr ?_ ?_)
  · refine imp_congr_right fun hk => ?_
    have := L.exercise_11_D_6_stay I k hI hk
    constructor
    · intro h
      have h2 : (0 : ℝ) ≤ L.η ^ 2 / (4 * L.μ * I ^ 2) * (2 - k) := by linarith
      have : (k : ℝ) ≤ 2 := by
        by_contra hk2; push Not at hk2; nlinarith
      exact_mod_cast this
    · intro h
      have : (k : ℝ) ≤ 2 := by exact_mod_cast h
      nlinarith
  · refine imp_congr_right fun _ => ?_
    have := L.exercise_11_D_6_join I k hI
    constructor
    · intro h
      have : (1 : ℝ) ≤ k := by
        by_contra hk1; push Not at hk1; nlinarith
      exact_mod_cast this
    · intro h
      have : (1 : ℝ) ≤ k := by exact_mod_cast h
      nlinarith

/-- **Exercise 11.D.6(a)** (MWG, p. 380), with **correction**. (i) With one consumer the coalition
forms (`k = 1`, `θ = 1`) and the optimal level `h(1)` (maximizing `φ + π`) results. (ii) With two
consumers `θ = 1` is an equilibrium: the printed claim "`θ < 1` when `I > 1`" fails at `I = 2`.
(iii) With `I ≥ 3` every equilibrium has `θ = k/I ≤ 2/I < 1` and `h(θ) > h(1)`: too much of the
externality. -/
theorem exercise_11_D_6a :
    (∀ k, L.IsMembershipEq 1 k ↔ k = 1) ∧ L.IsMembershipEq 2 2 ∧
      ∀ I k, 3 ≤ I → L.IsMembershipEq I k →
        (k : ℝ) / I < 1 ∧ L.hθ 1 < L.hθ ((k : ℝ) / I) := by
  refine ⟨fun k => ?_, ?_, fun I k hI he => ?_⟩
  · rw [membershipEq_iff _ 1 k one_pos]
    constructor
    · rintro ⟨h1, h2, h3⟩
      rcases Nat.lt_or_ge k 1 with h | h
      · exact absurd (h3 h) (by omega)
      · omega
    · rintro rfl; exact ⟨le_rfl, fun _ => by norm_num, fun h => absurd h (lt_irrefl 1)⟩
  · rw [membershipEq_iff _ 2 2 two_pos]
    exact ⟨le_rfl, fun _ => le_rfl, fun h => absurd h (lt_irrefl 2)⟩
  · have hI0 : 0 < I := by omega
    obtain ⟨_, h2, h3⟩ := (L.membershipEq_iff I k hI0).1 he
    have hk1 : 1 ≤ k := h3 (by omega)
    have hk2 := h2 hk1
    have hIr : (3 : ℝ) ≤ I := by exact_mod_cast hI
    have hkr : (k : ℝ) ≤ 2 := by exact_mod_cast hk2
    have hlt : (k : ℝ) / I < 1 := by rw [div_lt_one (by linarith)]; linarith
    refine ⟨hlt, ?_⟩
    simp only [hθ]
    rw [div_lt_div_iff_of_pos_right (by linarith [L.hμ])]
    nlinarith [L.hη]

/-- **Exercise 11.D.6(b)** (MWG, p. 381). Every equilibrium fraction satisfies `θ = k/I ≤ 2/I`,
which declines in `I` and tends to `0` as `I → ∞`. -/
theorem exercise_11_D_6b (I k : ℕ) (hI : 0 < I) (he : L.IsMembershipEq I k) :
    (k : ℝ) / I ≤ 2 / I := by
  obtain ⟨_, h2, h3⟩ := (L.membershipEq_iff I k hI).1 he
  have hI' : (0 : ℝ) < I := by exact_mod_cast hI
  rcases Nat.eq_zero_or_pos k with h | h
  · rw [h]; simp only [Nat.cast_zero, zero_div]; positivity
  · have : (k : ℝ) ≤ 2 := by exact_mod_cast h2 h
    exact div_le_div_of_nonneg_right this hI'.le

/-- The bound `2/I` tends to `0` as `I → ∞`. -/
theorem exercise_11_D_6b_limit :
    Filter.Tendsto (fun I : ℕ => (2 : ℝ) / I) Filter.atTop (nhds 0) :=
  tendsto_const_div_atTop_nhds_zero_nat 2

end LandModel

/-- An instance of the land model: `π(h) = 1 + 4h - h²`, `φ(h) = 10 - h`. -/
def landEx : LandModel where
  α := 1
  β := 4
  μ := 1
  γ := 10
  η := 1
  hμ := one_pos
  hη := one_pos
  hβη := by norm_num

/-! ## Exercise 11.D.7 -/

/-- The derived utility of a type-`θ` resident of a neighborhood with prestige `p` and building
cost `c`: `(1 + θ)(1 + p) - c`. -/
def nbUtil (θ p c : ℝ) : ℝ := (1 + θ) * (1 + p) - c

/-- **Exercise 11.D.7(a)** (MWG, p. 381): everyone building in `A` (prestige `1/2`, the population
mean) is not an equilibrium: whatever prestige `p_B ≥ 0` the empty neighborhood `B` is assigned,
type `θ = 0` strictly prefers to move to `B`, because `c_A - c_B > 1/2`. -/
theorem exercise_11_D_7a_allA {cA cB : ℝ} (hc : 1 / 2 < cA - cB) {pB : ℝ} (hpB : 0 ≤ pB) :
    nbUtil 0 (1 / 2) cA < nbUtil 0 pB cB := by
  simp only [nbUtil]; linarith

/-- **Exercise 11.D.7(a)**: everyone building in `B` is not an equilibrium if a lone mover to the
empty neighborhood `A` gets her own prestige: type `θ = 1` strictly prefers `A`, since
`c_A - c_B < 1`. -/
theorem exercise_11_D_7a_allB {cA cB : ℝ} (hc : cA - cB < 1) :
    nbUtil 1 (1 / 2) cB < nbUtil 1 1 cA := by
  simp only [nbUtil]; linarith

/-- **Correction to Exercise 11.D.7(a)**: if the empty neighborhood `A` is assigned prestige `0`,
everyone building in `B` is an equilibrium (every type weakly prefers `B`). So "both neighborhoods
must be occupied" depends on how the prestige of an empty neighborhood is defined. -/
theorem exercise_11_D_7a_counterexample {cA cB : ℝ} (hc : 1 / 2 < cA - cB) :
    ∀ θ, 0 ≤ θ → θ ≤ 1 → nbUtil θ 0 cA ≤ nbUtil θ (1 / 2) cB := by
  intro θ h0 _
  simp only [nbUtil]; nlinarith

/-- **Exercise 11.D.7(b)** (MWG, p. 381). In an equilibrium with prestige levels `p_A ≠ p_B` in
which both neighborhoods have a resident (`θ_A` in `A` weakly prefers `A`, `θ_B` in `B` weakly
prefers `B`), necessarily `p_A > p_B`, and every resident of `A` has at least the prestige of every
resident of `B`. -/
theorem exercise_11_D_7b {cA cB pA pB : ℝ} (hc : 0 < cA - cB) (hne : pA ≠ pB)
    (inA : ℝ → Prop)
    (hA : ∀ θ, 0 ≤ θ → θ ≤ 1 → inA θ → nbUtil θ pB cB ≤ nbUtil θ pA cA)
    (hB : ∀ θ, 0 ≤ θ → θ ≤ 1 → ¬ inA θ → nbUtil θ pA cA ≤ nbUtil θ pB cB)
    {θa : ℝ} (ha0 : 0 ≤ θa) (ha1 : θa ≤ 1) (ha : inA θa) :
    pB < pA ∧ ∀ θb, 0 ≤ θb → θb ≤ 1 → ¬ inA θb → θb ≤ θa := by
  have hgt : pB < pA := by
    rcases lt_or_gt_of_ne hne with h | h
    · have := hA θa ha0 ha1 ha
      simp only [nbUtil] at this
      nlinarith
    · exact h
  refine ⟨hgt, fun θb hb0 hb1 hb => ?_⟩
  by_contra hlt
  push Not at hlt
  have h1 := hA θa ha0 ha1 ha
  have h2 := hB θb hb0 hb1 hb
  simp only [nbUtil] at h1 h2
  nlinarith

/-- Average prestige over an interval of types `[a, b]` (uniform distribution): `(a + b)/2`. -/
theorem avg_interval {a b : ℝ} (hab : a < b) : (∫ θ in a..b, θ) / (b - a) = (a + b) / 2 := by
  rw [integral_id]
  field_simp [(sub_pos.2 hab).ne']
  ring

/-- **Exercise 11.D.7(b)**, the cutoff equilibrium. With `A = [θ̂, 1]` and `B = [0, θ̂)`, the
prestige levels are `(1 + θ̂)/2` and `θ̂/2` (`avg_interval`); this allocation is an equilibrium iff
`θ̂ = 2(c_A - c_B) - 1`, which lies in `(0, 1)` when `c_A - c_B ∈ (1/2, 1)`. -/
theorem exercise_11_D_7b_cutoff {cA cB s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    ((∀ θ, s ≤ θ → θ ≤ 1 → nbUtil θ (s / 2) cB ≤ nbUtil θ ((1 + s) / 2) cA) ∧
      (∀ θ, 0 ≤ θ → θ < s → nbUtil θ ((1 + s) / 2) cA ≤ nbUtil θ (s / 2) cB)) ↔
      s = 2 * (cA - cB) - 1 := by
  simp only [nbUtil]
  constructor
  · rintro ⟨h1, h2⟩
    have a := h1 s le_rfl hs1.le
    have b : (1 + s) / 2 ≤ cA - cB := by
      by_contra hlt
      push Not at hlt
      -- a type just below `s` would strictly prefer `A`
      set ε := min (s / 2) ((1 + s) / 2 - (cA - cB))
      have hε : 0 < ε := lt_min (by linarith) (by linarith)
      have := h2 (s - ε) (by linarith [min_le_left (s / 2) ((1 + s) / 2 - (cA - cB))])
        (by linarith)
      have hε2 : ε ≤ (1 + s) / 2 - (cA - cB) := min_le_right _ _
      nlinarith
    nlinarith
  · intro h
    constructor
    · intro θ hθ _; nlinarith
    · intro θ _ hθ; nlinarith

/-- **Exercise 11.D.7(c)** (MWG, p. 381). At the cutoff equilibrium `θ̂ = 2(c_A - c_B) - 1`,
raising the cutoff to `θ̂ + ε` (`0 < ε ≤ 1 - θ̂`) makes every type strictly better off: the
residents of each neighborhood enjoy a higher prestige, and the movers `θ ∈ [θ̂, θ̂ + ε)` were
nearly indifferent. -/
theorem exercise_11_D_7c {cA cB s ε : ℝ} (hs : s = 2 * (cA - cB) - 1) (_hs0 : 0 ≤ s)
    (hε : 0 < ε) (_hε1 : ε ≤ 1 - s) (θ : ℝ) (hθ0 : 0 ≤ θ) (_hθ1 : θ ≤ 1) :
    (if s ≤ θ then nbUtil θ ((1 + s) / 2) cA else nbUtil θ (s / 2) cB) <
      (if s + ε ≤ θ then nbUtil θ ((1 + (s + ε)) / 2) cA else nbUtil θ ((s + ε) / 2) cB) := by
  simp only [nbUtil]
  split_ifs with h1 h2 h2
  · nlinarith
  · -- the movers
    push Not at h2
    nlinarith
  · exact absurd (by linarith : s ≤ θ) h1
  · nlinarith

end MWG.ExternalitiesPublicGoods

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Exercises 11.E.1, 11.E.2 and 11.E.7 (MWG, pp. 381-382)

* **Exercise 11.E.1** (Weitzman's prices versus quantities). `∂π/∂h = β - bh + θ`,
  `∂φ/∂h = γ - ch + η` (`lqπ`, `lqφ`), `E[θ] = E[η] = E[θη] = 0`, `E[θ²] = σ_θ²`. (a) The best quota
  is `ĥ* = (β + γ)/(b + c)` (`exercise_11_E_1a`); (b) under a tax `t` the firm produces
  `(β - t + θ)/b` (`lq_tax_response`), and the best tax is `t* = (cβ - bγ)/(b + c)`
  (`exercise_11_E_1b`); (c) the tax beats the quota by `σ_θ²(b - c)/(2b²)`: the tax is better iff
  `b > c` (when `σ_θ² > 0`), and `σ_η²` is irrelevant (`exercise_11_E_1c`). As in the text's
  linear-quadratic analysis, the levels are not constrained to be nonnegative (departure).
* **Exercise 11.E.2**: two firms with shocks `θ₁, θ₂` (variances `σ₁², σ₂²`, covariance `σ₁₂`) and a
  consumer harmed by the total. The best uniform quota and tax (`exercise_11_E_2`), and the tax
  beats the quota by `((b - c)(σ₁² + σ₂²) - 2cσ₁₂)/(2b²)`, decreasing in `σ₁₂`
  (`exercise_11_E_2_compare`).
* **Exercise 11.E.7**: with the consumer's type known, a nonlinear tax whose total is
  `-φ(h, η̄)` (plus any constant) makes the firm maximize aggregate surplus for every `θ`
  (`exercise_11_E_7`). MWG prints `φ(h, η̄)`; that schedule fails (`exercise_11_E_7_printed`,
  correction).
-/

namespace MWG.ExternalitiesPublicGoods

open MeasureTheory

/-! ## Expectations of quadratic polynomials -/

/-- **Expectation of a quadratic polynomial** in shocks `θ₁, θ₂, η`: by linearity,
`E[A + B₁θ₁ + B₂θ₂ + Cη + D₁θ₁² + D₂θ₂² + D₁₂θ₁θ₂ + E₁θ₁η + E₂θ₂η]` is the same combination of the
moments. -/
theorem quad_integral {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {θ₁ θ₂ η : Ω → ℝ} (i1 : Integrable θ₁ μ) (i2 : Integrable θ₂ μ) (i3 : Integrable η μ)
    (i11 : Integrable (fun ω => θ₁ ω ^ 2) μ) (i22 : Integrable (fun ω => θ₂ ω ^ 2) μ)
    (i12 : Integrable (fun ω => θ₁ ω * θ₂ ω) μ) (i13 : Integrable (fun ω => θ₁ ω * η ω) μ)
    (i23 : Integrable (fun ω => θ₂ ω * η ω) μ) (A B₁ B₂ C D₁ D₂ D₁₂ E₁ E₂ : ℝ) :
    ∫ ω, (A + B₁ * θ₁ ω + B₂ * θ₂ ω + C * η ω + D₁ * θ₁ ω ^ 2 + D₂ * θ₂ ω ^ 2 +
      D₁₂ * (θ₁ ω * θ₂ ω) + E₁ * (θ₁ ω * η ω) + E₂ * (θ₂ ω * η ω)) ∂μ =
    A + B₁ * ∫ ω, θ₁ ω ∂μ + B₂ * ∫ ω, θ₂ ω ∂μ + C * ∫ ω, η ω ∂μ +
      D₁ * ∫ ω, θ₁ ω ^ 2 ∂μ + D₂ * ∫ ω, θ₂ ω ^ 2 ∂μ + D₁₂ * ∫ ω, θ₁ ω * θ₂ ω ∂μ +
      E₁ * ∫ ω, θ₁ ω * η ω ∂μ + E₂ * ∫ ω, θ₂ ω * η ω ∂μ := by
  have c0 : Integrable (fun _ : Ω => A) μ := integrable_const A
  have j1 := i1.const_mul B₁
  have j2 := i2.const_mul B₂
  have j3 := i3.const_mul C
  have j11 := i11.const_mul D₁
  have j22 := i22.const_mul D₂
  have j12 := i12.const_mul D₁₂
  have j13 := i13.const_mul E₁
  have j23 := i23.const_mul E₂
  have k1 : Integrable (fun ω => A + B₁ * θ₁ ω) μ := c0.add j1
  have k2 : Integrable (fun ω => A + B₁ * θ₁ ω + B₂ * θ₂ ω) μ := k1.add j2
  have k3 : Integrable (fun ω => A + B₁ * θ₁ ω + B₂ * θ₂ ω + C * η ω) μ := k2.add j3
  have k4 : Integrable (fun ω => A + B₁ * θ₁ ω + B₂ * θ₂ ω + C * η ω + D₁ * θ₁ ω ^ 2) μ :=
    k3.add j11
  have k5 : Integrable (fun ω => A + B₁ * θ₁ ω + B₂ * θ₂ ω + C * η ω + D₁ * θ₁ ω ^ 2 +
      D₂ * θ₂ ω ^ 2) μ := k4.add j22
  have k6 : Integrable (fun ω => A + B₁ * θ₁ ω + B₂ * θ₂ ω + C * η ω + D₁ * θ₁ ω ^ 2 +
      D₂ * θ₂ ω ^ 2 + D₁₂ * (θ₁ ω * θ₂ ω)) μ := k5.add j12
  have k7 : Integrable (fun ω => A + B₁ * θ₁ ω + B₂ * θ₂ ω + C * η ω + D₁ * θ₁ ω ^ 2 +
      D₂ * θ₂ ω ^ 2 + D₁₂ * (θ₁ ω * θ₂ ω) + E₁ * (θ₁ ω * η ω)) μ := k6.add j13
  rw [integral_add k7 j23, integral_add k6 j13, integral_add k5 j12, integral_add k4 j22,
    integral_add k3 j11, integral_add k2 j3, integral_add k1 j2, integral_add c0 j1]
  simp only [integral_const, probReal_univ, one_smul, integral_const_mul]

/-! ## Exercise 11.E.1 -/

/-- The firm's derived profit of Exercise 11.E.1: `π(h, θ) = βh - bh²/2 + θh`, so that
`∂π/∂h = β - bh + θ`. -/
noncomputable def lqπ (β b θ h : ℝ) : ℝ := β * h - b * h ^ 2 / 2 + θ * h

/-- The consumer's derived utility of Exercise 11.E.1: `φ(h, η) = γh - ch²/2 + ηh`, so that
`∂φ/∂h = γ - ch + η`. -/
noncomputable def lqφ (γ c η h : ℝ) : ℝ := γ * h - c * h ^ 2 / 2 + η * h

/-- Under a per-unit tax `t`, the firm's surplus-maximizing response is `h = (β - t + θ)/b`. -/
theorem lq_tax_response {β b θ t : ℝ} (hb : 0 < b) (y : ℝ) :
    lqπ β b θ y - t * y ≤ lqπ β b θ ((β - t + θ) / b) - t * ((β - t + θ) / b) := by
  simp only [lqπ]
  have key : β * y - b * y ^ 2 / 2 + θ * y - t * y = (β - t + θ) ^ 2 / (2 * b) -
      b / 2 * (y - (β - t + θ) / b) ^ 2 := by field_simp; ring
  have key2 : β * ((β - t + θ) / b) - b * ((β - t + θ) / b) ^ 2 / 2 + θ * ((β - t + θ) / b) -
      t * ((β - t + θ) / b) = (β - t + θ) ^ 2 / (2 * b) := by field_simp; ring
  rw [key, key2]
  nlinarith [sq_nonneg (y - (β - t + θ) / b)]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Exercise 11.E.1(a)** (MWG, p. 381). With a quota the firm produces exactly `ĥ`; the expected
aggregate surplus is `(β + γ)ĥ - (b + c)ĥ²/2`, maximized by `ĥ* = (β + γ)/(b + c)`. -/
theorem exercise_11_E_1a {θ η : Ω → ℝ} (i1 : Integrable θ μ) (i3 : Integrable η μ)
    (i11 : Integrable (fun ω => θ ω ^ 2) μ) (i13 : Integrable (fun ω => θ ω * η ω) μ)
    (hθ : ∫ ω, θ ω ∂μ = 0) (hη : ∫ ω, η ω ∂μ = 0) {β b γ c : ℝ} (hbc : 0 < b + c) (hq : ℝ) :
    ∫ ω, (lqπ β b (θ ω) hq + lqφ γ c (η ω) hq) ∂μ = (β + γ) * hq - (b + c) * hq ^ 2 / 2 ∧
      (β + γ) * hq - (b + c) * hq ^ 2 / 2 ≤
        (β + γ) * ((β + γ) / (b + c)) - (b + c) * ((β + γ) / (b + c)) ^ 2 / 2 := by
  have hz : Integrable (fun _ : Ω => (0 : ℝ)) μ := integrable_const 0
  have e := quad_integral (μ := μ) i1 hz i3 i11 (by simp) (by simp) i13 (by simp)
    ((β + γ) * hq - (b + c) * hq ^ 2 / 2) hq 0 hq 0 0 0 0 0
  refine ⟨?_, ?_⟩
  · have : (fun ω => lqπ β b (θ ω) hq + lqφ γ c (η ω) hq) = fun ω =>
        (β + γ) * hq - (b + c) * hq ^ 2 / 2 + hq * θ ω + 0 * (0 : ℝ) + hq * η ω +
          0 * θ ω ^ 2 + 0 * (0 : ℝ) ^ 2 + 0 * (θ ω * 0) + 0 * (θ ω * η ω) + 0 * (0 * η ω) := by
      funext ω; simp only [lqπ, lqφ]; ring
    rw [this, e, hθ, hη]; ring
  · have key : (β + γ) * ((β + γ) / (b + c)) - (b + c) * ((β + γ) / (b + c)) ^ 2 / 2 -
        ((β + γ) * hq - (b + c) * hq ^ 2 / 2) = (b + c) / 2 * (hq - (β + γ) / (b + c)) ^ 2 := by
      field_simp; ring
    nlinarith [sq_nonneg (hq - (β + γ) / (b + c))]

/-- The expected surplus under a tax `t` (Exercise 11.E.1(b)): with `m = (β - t)/b`,
`E[S] = (β + γ)m - (b + c)m²/2 + σ_θ²(b - c)/(2b²)`. -/
theorem exercise_11_E_1_tax_value {θ η : Ω → ℝ} (i1 : Integrable θ μ) (i3 : Integrable η μ)
    (i11 : Integrable (fun ω => θ ω ^ 2) μ) (i13 : Integrable (fun ω => θ ω * η ω) μ)
    (hθ : ∫ ω, θ ω ∂μ = 0) (hη : ∫ ω, η ω ∂μ = 0) (hθη : ∫ ω, θ ω * η ω ∂μ = 0)
    {β b γ c σ2 : ℝ} (hσ : ∫ ω, θ ω ^ 2 ∂μ = σ2) (hb : 0 < b) (t : ℝ) :
    ∫ ω, (lqπ β b (θ ω) ((β - t + θ ω) / b) + lqφ γ c (η ω) ((β - t + θ ω) / b)) ∂μ =
      (β + γ) * ((β - t) / b) - (b + c) * ((β - t) / b) ^ 2 / 2 + σ2 * (b - c) / (2 * b ^ 2) := by
  have hz : Integrable (fun _ : Ω => (0 : ℝ)) μ := integrable_const 0
  set m := (β - t) / b
  have e := quad_integral (μ := μ) i1 hz i3 i11 (by simp) (by simp) i13
    (by simp) ((β + γ) * m - (b + c) * m ^ 2 / 2)
    ((β + γ) / b - (b + c) * m / b + m) 0 m ((b - c) / (2 * b ^ 2)) 0 0 (1 / b) 0
  have : (fun ω => lqπ β b (θ ω) ((β - t + θ ω) / b) + lqφ γ c (η ω) ((β - t + θ ω) / b)) =
      fun ω => (β + γ) * m - (b + c) * m ^ 2 / 2 + ((β + γ) / b - (b + c) * m / b + m) * θ ω +
        0 * (0 : ℝ) + m * η ω + (b - c) / (2 * b ^ 2) * θ ω ^ 2 + 0 * (0 : ℝ) ^ 2 +
        0 * (θ ω * 0) + 1 / b * (θ ω * η ω) + 0 * (0 * η ω) := by
    funext ω; simp only [lqπ, lqφ, m]; field_simp; ring
  rw [this, e, hθ, hη, hθη, hσ]; ring

/-- **Exercise 11.E.1(b)** (MWG, p. 381). The best tax is `t* = (cβ - bγ)/(b + c)` (the tax at which
the expected level `(β - t)/b` equals the best quota): for every `t`, the expected surplus is at
most that at `t*`. -/
theorem exercise_11_E_1b {β b γ c σ2 : ℝ} (hb : 0 < b) (hbc : 0 < b + c) (t : ℝ) :
    (β + γ) * ((β - t) / b) - (b + c) * ((β - t) / b) ^ 2 / 2 + σ2 * (b - c) / (2 * b ^ 2) ≤
      (β + γ) * ((β - (c * β - b * γ) / (b + c)) / b) -
        (b + c) * ((β - (c * β - b * γ) / (b + c)) / b) ^ 2 / 2 + σ2 * (b - c) / (2 * b ^ 2) ∧
      (β - (c * β - b * γ) / (b + c)) / b = (β + γ) / (b + c) := by
  have hm : (β - (c * β - b * γ) / (b + c)) / b = (β + γ) / (b + c) := by
    field_simp; ring
  refine ⟨?_, hm⟩
  rw [hm]
  have key : (β + γ) * ((β + γ) / (b + c)) - (b + c) * ((β + γ) / (b + c)) ^ 2 / 2 -
      ((β + γ) * ((β - t) / b) - (b + c) * ((β - t) / b) ^ 2 / 2) =
        (b + c) / 2 * ((β - t) / b - (β + γ) / (b + c)) ^ 2 := by field_simp; ring
  nlinarith [sq_nonneg ((β - t) / b - (β + γ) / (b + c))]

/-- **Exercise 11.E.1(c)** (MWG, p. 381). At their best levels the tax yields
`σ_θ²(b - c)/(2b²)` more expected surplus than the quota: the tax is better iff `b > c` (the
consumer's marginal cost is flatter than the firm's marginal benefit), the quota iff `b < c`;
the consumer's shock variance `σ_η²` plays no role. -/
theorem exercise_11_E_1c {β b γ c σ2 : ℝ} (hb : 0 < b) (hσ : 0 < σ2) :
    ((β + γ) * ((β + γ) / (b + c)) - (b + c) * ((β + γ) / (b + c)) ^ 2 / 2 +
        σ2 * (b - c) / (2 * b ^ 2)) -
      ((β + γ) * ((β + γ) / (b + c)) - (b + c) * ((β + γ) / (b + c)) ^ 2 / 2) =
        σ2 * (b - c) / (2 * b ^ 2) ∧
      (0 < σ2 * (b - c) / (2 * b ^ 2) ↔ c < b) := by
  refine ⟨by ring, ?_⟩
  rw [div_pos_iff_of_pos_right (by positivity)]
  constructor
  · intro h; by_contra hc; push Not at hc; nlinarith
  · intro h; nlinarith

/-! ## Exercise 11.E.2 -/

/-- **Exercise 11.E.2** (MWG, p. 381), expected surplus. Firms `i = 1, 2` with
`∂πᵢ/∂hᵢ = β - bhᵢ + θᵢ`, the consumer with `∂φ/∂H = γ - cH + η` (`H = h₁ + h₂`); shocks with zero
means, `E[θᵢη] = 0`, `E[θᵢ²] = σᵢ²`, `E[θ₁θ₂] = σ₁₂`. A uniform quota `ĥ` gives
`2(β + γ)ĥ - (b + 2c)ĥ²`; a uniform tax with `m = (β - t)/b` gives
`2(β + γ)m - (b + 2c)m² + (σ₁² + σ₂²)/(2b) - c(σ₁² + σ₂² + 2σ₁₂)/(2b²)`. -/
theorem exercise_11_E_2 {θ₁ θ₂ η : Ω → ℝ} (i1 : Integrable θ₁ μ) (i2 : Integrable θ₂ μ)
    (i3 : Integrable η μ) (i11 : Integrable (fun ω => θ₁ ω ^ 2) μ)
    (i22 : Integrable (fun ω => θ₂ ω ^ 2) μ) (i12 : Integrable (fun ω => θ₁ ω * θ₂ ω) μ)
    (i13 : Integrable (fun ω => θ₁ ω * η ω) μ) (i23 : Integrable (fun ω => θ₂ ω * η ω) μ)
    (h1 : ∫ ω, θ₁ ω ∂μ = 0) (h2 : ∫ ω, θ₂ ω ∂μ = 0) (h3 : ∫ ω, η ω ∂μ = 0)
    (h13 : ∫ ω, θ₁ ω * η ω ∂μ = 0) (h23 : ∫ ω, θ₂ ω * η ω ∂μ = 0)
    {β b γ c s1 s2 s12 : ℝ} (hs1 : ∫ ω, θ₁ ω ^ 2 ∂μ = s1) (hs2 : ∫ ω, θ₂ ω ^ 2 ∂μ = s2)
    (hs12 : ∫ ω, θ₁ ω * θ₂ ω ∂μ = s12) (hb : 0 < b) (hq t : ℝ) :
    ∫ ω, (lqπ β b (θ₁ ω) hq + lqπ β b (θ₂ ω) hq + lqφ γ c (η ω) (hq + hq)) ∂μ =
        2 * (β + γ) * hq - (b + 2 * c) * hq ^ 2 ∧
      ∫ ω, (lqπ β b (θ₁ ω) ((β - t + θ₁ ω) / b) + lqπ β b (θ₂ ω) ((β - t + θ₂ ω) / b) +
          lqφ γ c (η ω) ((β - t + θ₁ ω) / b + (β - t + θ₂ ω) / b)) ∂μ =
        2 * (β + γ) * ((β - t) / b) - (b + 2 * c) * ((β - t) / b) ^ 2 + (s1 + s2) / (2 * b) -
          c * (s1 + s2 + 2 * s12) / (2 * b ^ 2) := by
  constructor
  · have e := quad_integral (μ := μ) i1 i2 i3 i11 i22 i12 i13 i23
      (2 * (β + γ) * hq - (b + 2 * c) * hq ^ 2) hq hq (2 * hq) 0 0 0 0 0
    have : (fun ω => lqπ β b (θ₁ ω) hq + lqπ β b (θ₂ ω) hq + lqφ γ c (η ω) (hq + hq)) =
        fun ω => 2 * (β + γ) * hq - (b + 2 * c) * hq ^ 2 + hq * θ₁ ω + hq * θ₂ ω +
          2 * hq * η ω + 0 * θ₁ ω ^ 2 + 0 * θ₂ ω ^ 2 + 0 * (θ₁ ω * θ₂ ω) + 0 * (θ₁ ω * η ω) +
          0 * (θ₂ ω * η ω) := by
      funext ω; simp only [lqπ, lqφ]; ring
    rw [this, e, h1, h2, h3]; ring
  · set m := (β - t) / b
    have e := quad_integral (μ := μ) i1 i2 i3 i11 i22 i12 i13 i23
      (2 * (β + γ) * m - (b + 2 * c) * m ^ 2) (β / b + m - 2 * c * m / b + γ / b - b * m / b)
      (β / b + m - 2 * c * m / b + γ / b - b * m / b) (2 * m)
      (1 / b - 1 / (2 * b) - c / (2 * b ^ 2)) (1 / b - 1 / (2 * b) - c / (2 * b ^ 2))
      (-(c / b ^ 2)) (1 / b) (1 / b)
    have : (fun ω => lqπ β b (θ₁ ω) ((β - t + θ₁ ω) / b) + lqπ β b (θ₂ ω) ((β - t + θ₂ ω) / b) +
        lqφ γ c (η ω) ((β - t + θ₁ ω) / b + (β - t + θ₂ ω) / b)) =
        fun ω => 2 * (β + γ) * m - (b + 2 * c) * m ^ 2 +
          (β / b + m - 2 * c * m / b + γ / b - b * m / b) * θ₁ ω +
          (β / b + m - 2 * c * m / b + γ / b - b * m / b) * θ₂ ω + 2 * m * η ω +
          (1 / b - 1 / (2 * b) - c / (2 * b ^ 2)) * θ₁ ω ^ 2 +
          (1 / b - 1 / (2 * b) - c / (2 * b ^ 2)) * θ₂ ω ^ 2 + -(c / b ^ 2) * (θ₁ ω * θ₂ ω) +
          1 / b * (θ₁ ω * η ω) + 1 / b * (θ₂ ω * η ω) := by
      funext ω; simp only [lqπ, lqφ, m]; field_simp; ring
    rw [this, e, h1, h2, h3, h13, h23, hs1, hs2, hs12]
    field_simp
    ring

/-- **Exercise 11.E.2**, the comparison. The best uniform quota and the best uniform tax both set
the expected level `(β + γ)/(b + 2c)`; the tax then beats the quota by
`((b - c)(σ₁² + σ₂²) - 2cσ₁₂)/(2b²)`, which decreases in the covariance `σ₁₂`: the less correlated
the shocks, the better the tax looks. -/
theorem exercise_11_E_2_compare {β b γ c s1 s2 s12 : ℝ} (hb : 0 < b) (hc : 0 < c) (x : ℝ) :
    2 * (β + γ) * x - (b + 2 * c) * x ^ 2 ≤
        2 * (β + γ) * ((β + γ) / (b + 2 * c)) - (b + 2 * c) * ((β + γ) / (b + 2 * c)) ^ 2 ∧
      ((s1 + s2) / (2 * b) - c * (s1 + s2 + 2 * s12) / (2 * b ^ 2) =
        ((b - c) * (s1 + s2) - 2 * c * s12) / (2 * b ^ 2)) ∧
      ∀ s12' : ℝ, s12 < s12' →
        ((b - c) * (s1 + s2) - 2 * c * s12') / (2 * b ^ 2) <
          ((b - c) * (s1 + s2) - 2 * c * s12) / (2 * b ^ 2) := by
  refine ⟨?_, by field_simp; ring, fun s12' hs => ?_⟩
  · have key : 2 * (β + γ) * ((β + γ) / (b + 2 * c)) - (b + 2 * c) * ((β + γ) / (b + 2 * c)) ^ 2 -
        (2 * (β + γ) * x - (b + 2 * c) * x ^ 2) =
          (b + 2 * c) * (x - (β + γ) / (b + 2 * c)) ^ 2 := by
      field_simp; ring
    nlinarith [sq_nonneg (x - (β + γ) / (b + 2 * c))]
  · rw [div_lt_div_iff_of_pos_right (by positivity)]
    nlinarith

/-- An instance of the moment hypotheses: two equally likely states with `θ = ±1` (and `η = 0`):
`E[θ] = 0`, `E[θ²] = 1`. -/
theorem exercise_11_E_moments_instance :
    let μ : Measure Bool := (PMF.uniformOfFintype Bool).toMeasure
    IsProbabilityMeasure μ ∧ ∫ ω, (if ω then (1 : ℝ) else -1) ∂μ = 0 ∧
      ∫ ω, (if ω then (1 : ℝ) else -1) ^ 2 ∂μ = 1 := by
  intro μ
  refine ⟨inferInstance, ?_, ?_⟩
  · rw [integral_fintype]
    · simp [μ, Measure.real]
    · exact Integrable.of_finite
  · rw [integral_fintype]
    · simp [μ, Measure.real]
    · exact Integrable.of_finite

/-! ## Exercise 11.E.7 -/

/-- **Exercise 11.E.7** (MWG, p. 382), corrected. With the consumer's type known
(`φ(h) = φ(h, η̄)`),
if the firm pays the total tax `T(h) = k - φ(h)` (any constant `k`; `k = φ(0)` makes it
nonnegative for a negative externality), then for every `θ` the firm's choices are exactly the
surplus-maximizing levels. -/
theorem exercise_11_E_7 (pr : ℝ → ℝ → ℝ) (φ : ℝ → ℝ) (k θ h : ℝ) :
    (0 ≤ h ∧ ∀ y, 0 ≤ y → pr θ y - (k - φ y) ≤ pr θ h - (k - φ h)) ↔
      (0 ≤ h ∧ ∀ y, 0 ≤ y → φ y + pr θ y ≤ φ h + pr θ h) := by
  constructor
  · rintro ⟨h0, hm⟩; exact ⟨h0, fun y hy => by linarith [hm y hy]⟩
  · rintro ⟨h0, hm⟩; exact ⟨h0, fun y hy => by linarith [hm y hy]⟩

/-- **Correction to Exercise 11.E.7**: the printed schedule `T(h) = φ(h, η̄)` fails. With
`π(h, θ) = θh - h²/2` and `φ(h) = -h` (`∂φ/∂h = -1`), the firm facing `T(h) = φ(h)` chooses
`h = θ + 1`, while aggregate surplus is maximized at `max(θ - 1, 0)`: for every `θ > -1` the levels
differ. -/
theorem exercise_11_E_7_printed (θ : ℝ) (hθ : -1 < θ) :
    IsTaxChoice' (fun h => θ * h - h ^ 2 / 2) (-1) (θ + 1) ∧
      IsTaxChoice' (fun h => θ * h - h ^ 2 / 2) 1 (max (θ - 1) 0) ∧
      θ + 1 ≠ max (θ - 1) 0 := by
  refine ⟨(lq_tax_choice θ (-1) _).2 (by rw [max_eq_left (by linarith)]; ring),
    (lq_tax_choice θ 1 _).2 rfl, fun h => ?_⟩
  rcases le_total (θ - 1) 0 with h1 | h1
  · rw [max_eq_right h1] at h; linarith
  · rw [max_eq_left h1] at h; linarith

end MWG.ExternalitiesPublicGoods

/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/

/-!
# Concrete instances of the hypotheses

Non-vacuity checks for theorems whose hypotheses are not instantiated in their own modules:

* the depletable optimum of `mlEx` via (11.D.3)-(11.D.4) (`mlEx_depl`);
* a binding quota (`quota_binds_instance`);
* Exercise 11.B.2(b) and (c) with explicit utility functions and paths;
* Exercise 11.B.4 with `φ₂(h, e) = -h - (e - h)²/2`;
* Exercise 11.D.2 with `φᵢ(x, H) = x - H²/2`;
* Exercise 11.D.3 with `c(q, Q) = q²/2 - Q` and `P(Q) = 10 - Q`;
* Exercise 11.D.4 with linear damages.
-/

namespace MWG.ExternalitiesPublicGoods

open MWG.CompetitiveMarkets

/-- The depletable version of `mlEx` (two consumers `φᵢ(h̃) = -h̃ - h̃²/2`, firms with
`πⱼ(h) = aⱼh - h²/2`, `a = (4, 6)`): absorptions `(2, 2)` and generation `(1, 3)` solve
(11.D.2), with
multiplier `μ = -3`. -/
theorem mlEx_depl : mlEx.IsDeplOpt ![2, 2] ![1, 3] := by
  refine mlEx.deplKKT_sufficient (μ := -3) ⟨fun i => ?_, fun j => ?_, ?_⟩
    ⟨fun i => ?_, fun j => ?_⟩
  · fin_cases i <;> norm_num
  · fin_cases j <;> norm_num
  · simp [Fin.sum_univ_two]; norm_num
  · fin_cases i <;> norm_num [mlEx]
  · fin_cases j <;> norm_num [mlEx]

/-- An instance of `quota_binds`: profit `3h - h²/2`, quota `1` (marginal profit `2 > 0`). -/
theorem quota_binds_instance : IsQuotaChoice (fun h => 3 * h - h ^ 2 / 2) 1 1 := by
  have hd : ∀ x : ℝ, HasDerivAt (fun h => 3 * h - h ^ 2 / 2) (3 - x) x := fun x => by
    have h' := ((hasDerivAt_id x).const_mul 3).sub ((hasDerivAt_pow 2 x).div_const 2)
    exact (h'.congr_deriv (by simp only [Nat.cast_ofNat]; ring) :
      HasDerivAt (fun h : ℝ => 3 * h - h ^ 2 / 2) (3 - x) x)
  exact (quota_binds hd (fun a _ b _ hab => by linarith) zero_le_one (by norm_num) 1).2 rfl

/-- An instance of Exercise 11.B.2(b): `φ₂(h, w) = w h`, so `φ₂ₕ(h, z) = z`, `φ₂_w(h, z) = h`;
consumer 2's demand at price `p = 1` is `h(w) = w/2`, with wealth effect `1/2`. -/
theorem exercise_11_B_2b_instance :
    (1 / 2 : ℝ) * (0 - 2 * 1 * 1 + 1 ^ 2 * 0) + (1 - 1 * 0) = 0 := by
  have hF₁ : ∀ x : ℝ × ℝ, HasFDerivAt (fun x : ℝ × ℝ => x.2)
      ((0 : ℝ) • ContinuousLinearMap.fst ℝ ℝ ℝ + (1 : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ) x :=
    fun x => by simpa using hasFDerivAt_snd
  have hF₂ : ∀ x : ℝ × ℝ, HasFDerivAt (fun x : ℝ × ℝ => x.1)
      ((1 : ℝ) • ContinuousLinearMap.fst ℝ ℝ ℝ + (0 : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ) x :=
    fun x => by simpa using hasFDerivAt_fst
  have hh : HasDerivAt (fun w : ℝ => w / 2) (1 / 2) 2 := by
    simpa using (hasDerivAt_id (2 : ℝ)).div_const 2
  exact exercise_11_B_2b (fun x => x.2) (fun x => x.1) (fun w => w / 2) 1 2 (1 / 2) 0 1 0
    (hF₁ _) (hF₂ _) hh (fun w => by ring)

/-- An instance of Exercise 11.B.2(c) (corrected comparative statics): `φ₂(h, z) = z + 2h - h²/2`
(`φ₂ₕ = 2 - h`, `φ₂_w = 1`), `φ₁(h) = -h²/2`; the optimum is `h° ≡ 1`, `z°(w₂) = w₂ - 1/2`, so
`dh°/dw₂ = 0`, consistent with the zero wealth effect of a quasilinear `φ₂`. -/
theorem exercise_11_B_2c_instance :
    (0 : ℝ) * (-1 - 2 * (-(-(1 : ℝ))) * 0 + (-(-(1 : ℝ))) ^ 2 * 0 + -1 * 1) +
      (0 - (-(-(1 : ℝ))) * 0) = 0 := by
  have hF₁ : ∀ x : ℝ × ℝ, HasFDerivAt (fun x : ℝ × ℝ => 2 - x.1)
      ((-1 : ℝ) • ContinuousLinearMap.fst ℝ ℝ ℝ + (0 : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ) x :=
    fun x => by
      have := (hasFDerivAt_fst (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := x)).const_sub 2
      convert this using 1
      ext <;> simp
  have hF₂ : ∀ x : ℝ × ℝ, HasFDerivAt (fun _ : ℝ × ℝ => (1 : ℝ))
      ((0 : ℝ) • ContinuousLinearMap.fst ℝ ℝ ℝ + (0 : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ) x :=
    fun x => by simpa using hasFDerivAt_const (1 : ℝ) x
  have hφ₁ : ∀ x : ℝ, HasDerivAt (fun h : ℝ => -(h ^ 2 / 2)) (-x) x := fun x => by
    have h' := ((hasDerivAt_pow 2 x).div_const 2).neg
    exact (h'.congr_deriv (by simp only [Nat.cast_ofNat]; ring) :
      HasDerivAt (fun h : ℝ => -(h ^ 2 / 2)) (-x) x)
  have hd₁ : HasDerivAt (fun x : ℝ => -x) (-1) ((fun _ : ℝ => (1 : ℝ)) 0) := hasDerivAt_neg 1
  have hh : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 0 := hasDerivAt_const _ _
  have hz : HasDerivAt (fun w : ℝ => -((1 : ℝ) ^ 2 / 2) + w + 0) 1 0 :=
    ((hasDerivAt_id (0 : ℝ)).const_add (-((1 : ℝ) ^ 2 / 2))).add_const 0
  exact exercise_11_B_2c_corrected (fun x => 2 - x.1) (fun _ => 1) (fun h => -(h ^ 2 / 2))
    (fun x => -x) (fun _ => 1) (fun w => -((1 : ℝ) ^ 2 / 2) + w + 0) 0 0 1 (-1) (-1) 0 0 0
    (hF₁ _) (hF₂ _) hφ₁ hd₁ hh hz (fun w => by ring) (fun w => by ring)

/-- An instance of Exercise 11.B.4: `φ₁(h) = 4h - h²/2`, `φ₂(h, e) = -h - (e - h)²/2`; the optimum
is
`(h°, e°) = (3, 3)` and `∂φ₂/∂h(3, 3) = -1`. -/
theorem exercise_11_B_4_instance :
    (∀ y, 0 ≤ y → 4 * y - y ^ 2 / 2 - (-(-1 : ℝ)) * y ≤
      4 * 3 - (3 : ℝ) ^ 2 / 2 - (-(-1)) * 3) ∧
      ∀ e, -(3 : ℝ) - (e - 3) ^ 2 / 2 ≤ -3 - (3 - 3) ^ 2 / 2 := by
  have hφ₁ : ∀ x : ℝ, HasDerivAt (fun h : ℝ => 4 * h - h ^ 2 / 2) (4 - x) x := fun x => by
    have h' := ((hasDerivAt_id x).const_mul 4).sub ((hasDerivAt_pow 2 x).div_const 2)
    exact (h'.congr_deriv (by simp only [Nat.cast_ofNat]; ring) :
      HasDerivAt (fun h : ℝ => 4 * h - h ^ 2 / 2) (4 - x) x)
  have hg : HasDerivAt (fun h : ℝ => -h - (3 - h) ^ 2 / 2) (-1) 3 := by
    have h' := (hasDerivAt_id (3 : ℝ)).neg.sub
      ((((hasDerivAt_id (3 : ℝ)).const_sub 3).pow 2).div_const 2)
    exact (h'.congr_deriv (by norm_num) :
      HasDerivAt (fun h : ℝ => -h - (3 - h) ^ 2 / 2) (-1) 3)
  exact exercise_11_B_4 (fun h e => -h - (e - h) ^ 2 / 2) hφ₁
    (fun a _ b _ hab => by linarith) hg
    ⟨by norm_num, fun h e _ => by nlinarith [sq_nonneg (h - 3), sq_nonneg (e - h)]⟩

/-- An instance of Exercise 11.D.2: two consumers with `φᵢ(x, H) = x - H²/2` (`∂₁ = 1`,
`∂₂ = -H`); the optimal total is `H° = 1/2`, attained at `(1/4, 1/4)`. -/
theorem exercise_11_D_2_instance :
    ∀ y ∈ orthant (Fin 2), d2Obj (fun _ (x : ℝ × ℝ) => x.1 - x.2 ^ 2 / 2) y ≤
      d2Obj (fun _ (x : ℝ × ℝ) => x.1 - x.2 ^ 2 / 2) ![1 / 4, 1 / 4] := by
  have hφ : ∀ (i : Fin 2) (x : ℝ × ℝ), HasFDerivAt (fun x : ℝ × ℝ => x.1 - x.2 ^ 2 / 2)
      ((fun _ _ => (1 : ℝ)) i x • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (fun _ (x : ℝ × ℝ) => -x.2) i x • ContinuousLinearMap.snd ℝ ℝ ℝ) x := fun _ x => by
    have h1 := hasFDerivAt_fst (𝕜 := ℝ) (p := x) (E := ℝ) (F := ℝ)
    have h2 : HasFDerivAt (fun x : ℝ × ℝ => x.2 ^ 2)
        ((2 * x.2) • ContinuousLinearMap.snd ℝ ℝ ℝ) x := by
      have := (hasFDerivAt_snd (𝕜 := ℝ) (p := x) (E := ℝ) (F := ℝ)).mul
        (hasFDerivAt_snd (𝕜 := ℝ) (p := x) (E := ℝ) (F := ℝ))
      convert this using 1
      · ext y; simp [sq]
      · ext
        · simp
        · simp; ring
    have h3 := HasFDerivAt.const_mul h2 (1 / 2 : ℝ)
    convert h1.sub h3 using 1
    · ext y; simp only [Pi.sub_apply]; ring
    · ext <;> simp
  have hconc : ∀ i : Fin 2, ConcaveOn ℝ Set.univ (fun x : ℝ × ℝ => x.1 - x.2 ^ 2 / 2) := by
    intro _
    refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, smul_eq_mul]
    have hb' : b = 1 - a := by linarith
    subst hb'
    nlinarith [mul_nonneg ha hb, mul_nonneg (mul_nonneg ha hb) (sq_nonneg (x.2 - y.2))]
  have hmem : ![(1 : ℝ) / 4, 1 / 4] ∈ orthant (Fin 2) := fun i => by fin_cases i <;> norm_num
  refine (exercise_11_D_2_opt _ (fun _ _ => 1) (fun _ x => -x.2) hφ hconc hmem).2 fun j => ?_
  simp [Fin.sum_univ_two]
  norm_num

/-- An instance of Exercise 11.D.3: `c(q, Q) = q²/2 - Q` (`c_q = q`, `c_Q = -1 < 0`), `J = 2`,
inverse demand `P(Q) = 10 - Q`: the equilibrium `Q* = 20/3` is below the optimum `Q° = 8`. -/
theorem exercise_11_D_3_instance : (20 / 3 : ℝ) < 8 := by
  refine exercise_11_D_3 (P := fun Q => 10 - Q) (cq := fun x => x.1) (cQ := fun _ => -1)
    (J := 2) (fun a b hab => by simp only; linarith) (fun a b hab => by simp only; linarith)
    two_pos (fun _ => by norm_num) (by norm_num) (by norm_num)

/-- An instance of Exercise 11.D.4: one consumer with linear damage `-(h₁ + h₂)` and firms with
`πⱼ(h) = 3h - h²/2`: the optimum is `(2, 2)`. -/
theorem exercise_11_D_4_instance :
    ∀ y ∈ orthant (Fin 2),
      d4Obj (fun (_ : Fin 1) (h : Fin 2 → ℝ) => -(h 0 + h 1)) (fun _ h => 3 * h - h ^ 2 / 2) y ≤
        d4Obj (fun (_ : Fin 1) (h : Fin 2 → ℝ) => -(h 0 + h 1)) (fun _ h => 3 * h - h ^ 2 / 2)
          ![2, 2] := by
  set D : (Fin 2 → ℝ) →L[ℝ] ℝ :=
    -(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0 +
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1)
  have hD : ∀ h : Fin 2 → ℝ, D h = -(h 0 + h 1) := fun h => by simp [D]
  have hφ : ∀ _i : Fin 1, HasFDerivAt (fun h : Fin 2 → ℝ => -(h 0 + h 1)) D ![2, 2] := by
    intro _
    have := D.hasFDerivAt (x := ![2, 2])
    have e : (⇑D) = fun h : Fin 2 → ℝ => -(h 0 + h 1) := funext hD
    rw [e] at this
    exact this
  have hconc : ∀ _i : Fin 1, ConcaveOn ℝ (orthant (Fin 2)) fun h : Fin 2 → ℝ => -(h 0 + h 1) := by
    intro _
    refine ⟨convex_orthant _, fun x _ y _ a b _ _ _ => ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith
  have hpr : ∀ (_j : Fin 2) (x : ℝ), HasDerivAt (fun h : ℝ => 3 * h - h ^ 2 / 2) (3 - x) x :=
    fun _ x => by
      have h' := ((hasDerivAt_id x).const_mul 3).sub ((hasDerivAt_pow 2 x).div_const 2)
      exact (h'.congr_deriv (by simp only [Nat.cast_ofNat]; ring) :
        HasDerivAt (fun h : ℝ => 3 * h - h ^ 2 / 2) (3 - x) x)
  have hmem : ![(2 : ℝ), 2] ∈ orthant (Fin 2) := fun i => by fin_cases i <;> norm_num
  refine (exercise_11_D_4_opt _ (fun _ => D) _ (fun _ x => 3 - x) hφ hconc hpr
    (fun _ a _ b _ hab => by linarith) hmem).2 fun j => ?_
  fin_cases j <;> simp [hD] <;> norm_num

end MWG.ExternalitiesPublicGoods

set_option linter.style.longLine false
#print axioms MWG.ExternalitiesPublicGoods.QLAlloc
#print axioms MWG.ExternalitiesPublicGoods.QLAlloc.mk
#print axioms MWG.ExternalitiesPublicGoods.QLAlloc.x
#print axioms MWG.ExternalitiesPublicGoods.QLAlloc.m
#print axioms MWG.ExternalitiesPublicGoods.QLFeasible
#print axioms MWG.ExternalitiesPublicGoods.QLPareto
#print axioms MWG.ExternalitiesPublicGoods.qlSurplus'
#print axioms MWG.ExternalitiesPublicGoods.ql_pareto_iff
#print axioms MWG.ExternalitiesPublicGoods.ql_pareto_exists
#print axioms MWG.ExternalitiesPublicGoods.IsTIOLIOffer
#print axioms MWG.ExternalitiesPublicGoods.tioli_iff
#print axioms MWG.ExternalitiesPublicGoods.kt_max_iff
#print axioms MWG.ExternalitiesPublicGoods.kt_isMax_iff
#print axioms MWG.ExternalitiesPublicGoods.kt_max_unique
#print axioms MWG.ExternalitiesPublicGoods.kt_strict_max
#print axioms MWG.ExternalitiesPublicGoods.strictMonoOn_Icc_of_deriv_pos
#print axioms MWG.ExternalitiesPublicGoods.kt_strictMonoOn
#print axioms MWG.ExternalitiesPublicGoods.strictAntiOn_of_second_deriv_neg
#print axioms MWG.ExternalitiesPublicGoods.convex_tangent
#print axioms MWG.ExternalitiesPublicGoods.concave_tangent
#print axioms MWG.ExternalitiesPublicGoods.orthant
#print axioms MWG.ExternalitiesPublicGoods.convex_orthant
#print axioms MWG.ExternalitiesPublicGoods.hasDerivAt_update
#print axioms MWG.ExternalitiesPublicGoods.clm_apply_eq_sum
#print axioms MWG.ExternalitiesPublicGoods.orthant_kt_iff
#print axioms MWG.ExternalitiesPublicGoods.HasExternality
#print axioms MWG.ExternalitiesPublicGoods.definition_11_B_1
#print axioms MWG.ExternalitiesPublicGoods.PositiveExternality
#print axioms MWG.ExternalitiesPublicGoods.NegativeExternality
#print axioms MWG.ExternalitiesPublicGoods.hasExternality_of_deriv_ne
#print axioms MWG.ExternalitiesPublicGoods.PositiveExternality.hasExternality
#print axioms MWG.ExternalitiesPublicGoods.NegativeExternality.hasExternality
#print axioms MWG.ExternalitiesPublicGoods.footnote_3
#print axioms MWG.ExternalitiesPublicGoods.Bilateral
#print axioms MWG.ExternalitiesPublicGoods.Bilateral.mk
#print axioms MWG.ExternalitiesPublicGoods.Bilateral.φ₁
#print axioms MWG.ExternalitiesPublicGoods.Bilateral.φ₂
#print axioms MWG.ExternalitiesPublicGoods.Bilateral.d₁
#print axioms MWG.ExternalitiesPublicGoods.Bilateral.d₂
#print axioms MWG.ExternalitiesPublicGoods.Bilateral.hd₁
#print axioms MWG.ExternalitiesPublicGoods.Bilateral.hd₂
#print axioms MWG.ExternalitiesPublicGoods.Bilateral.anti₁
#print axioms MWG.ExternalitiesPublicGoods.Bilateral.anti₂
#print axioms MWG.ExternalitiesPublicGoods.Bilateral.joint
#print axioms MWG.ExternalitiesPublicGoods.Bilateral.hasDerivAt_joint
#print axioms MWG.ExternalitiesPublicGoods.Bilateral.anti_joint
#print axioms MWG.ExternalitiesPublicGoods.Bilateral.IsEqLevel
#print axioms MWG.ExternalitiesPublicGoods.Bilateral.IsOptLevel
#print axioms MWG.ExternalitiesPublicGoods.Bilateral.eq_11_B_1
#print axioms MWG.ExternalitiesPublicGoods.Bilateral.eq_11_B_2
#print axioms MWG.ExternalitiesPublicGoods.Bilateral.footnote_4
#print axioms MWG.ExternalitiesPublicGoods.Bilateral.eq_ne_opt
#print axioms MWG.ExternalitiesPublicGoods.Bilateral.negative_externality_excess
#print axioms MWG.ExternalitiesPublicGoods.Bilateral.positive_externality_shortfall
#print axioms MWG.ExternalitiesPublicGoods.Bilateral.opt_indep_wealth
#print axioms MWG.ExternalitiesPublicGoods.Bilateral.quota_implements
#print axioms MWG.ExternalitiesPublicGoods.Bilateral.IsTaxChoice
#print axioms MWG.ExternalitiesPublicGoods.Bilateral.eq_11_B_4
#print axioms MWG.ExternalitiesPublicGoods.Bilateral.pigou_tax
#print axioms MWG.ExternalitiesPublicGoods.Bilateral.pigou_tax_unique
#print axioms MWG.ExternalitiesPublicGoods.Bilateral.pigou_tax_sign
#print axioms MWG.ExternalitiesPublicGoods.Bilateral.footnote_5
#print axioms MWG.ExternalitiesPublicGoods.Bilateral.subsidy_equiv_tax
#print axioms MWG.ExternalitiesPublicGoods.Bilateral.tax_quota_equivalent
#print axioms MWG.ExternalitiesPublicGoods.Bilateral.IsOffer2Free
#print axioms MWG.ExternalitiesPublicGoods.Bilateral.IsOffer2Right
#print axioms MWG.ExternalitiesPublicGoods.Bilateral.joint_comm'
#print axioms MWG.ExternalitiesPublicGoods.Bilateral.eq_11_B_5
#print axioms MWG.ExternalitiesPublicGoods.Bilateral.coase_theorem
#print axioms MWG.ExternalitiesPublicGoods.Bilateral.coase_payments
#print axioms MWG.ExternalitiesPublicGoods.Bilateral.offer1_iff
#print axioms MWG.ExternalitiesPublicGoods.Bilateral.figure_11_B_3
#print axioms MWG.ExternalitiesPublicGoods.Bilateral.merger_internalizes
#print axioms MWG.ExternalitiesPublicGoods.Bilateral.eq_11_B_6
#print axioms MWG.ExternalitiesPublicGoods.Bilateral.IsRightsSupply
#print axioms MWG.ExternalitiesPublicGoods.Bilateral.eq_11_B_7
#print axioms MWG.ExternalitiesPublicGoods.Bilateral.IsRightsEquilibrium
#print axioms MWG.ExternalitiesPublicGoods.Bilateral.rights_equilibrium_optimal
#print axioms MWG.ExternalitiesPublicGoods.Bilateral.rights_equilibrium_exists
#print axioms MWG.ExternalitiesPublicGoods.Bilateral.ex
#print axioms MWG.ExternalitiesPublicGoods.Bilateral.ex_values
#print axioms MWG.ExternalitiesPublicGoods.DepletableFeasible
#print axioms MWG.ExternalitiesPublicGoods.NondepletableFeasible
#print axioms MWG.ExternalitiesPublicGoods.definition_11_C_1
#print axioms MWG.ExternalitiesPublicGoods.nondepletable_not_preclude
#print axioms MWG.ExternalitiesPublicGoods.depletable_precludes
#print axioms MWG.ExternalitiesPublicGoods.depletable_imp_nondepletable
#print axioms MWG.ExternalitiesPublicGoods.PublicGood
#print axioms MWG.ExternalitiesPublicGoods.PublicGood.mk
#print axioms MWG.ExternalitiesPublicGoods.PublicGood.φ
#print axioms MWG.ExternalitiesPublicGoods.PublicGood.dφ
#print axioms MWG.ExternalitiesPublicGoods.PublicGood.c
#print axioms MWG.ExternalitiesPublicGoods.PublicGood.dc
#print axioms MWG.ExternalitiesPublicGoods.PublicGood.hφ
#print axioms MWG.ExternalitiesPublicGoods.PublicGood.hc
#print axioms MWG.ExternalitiesPublicGoods.PublicGood.antiφ
#print axioms MWG.ExternalitiesPublicGoods.PublicGood.monoc
#print axioms MWG.ExternalitiesPublicGoods.PublicGood.surplus
#print axioms MWG.ExternalitiesPublicGoods.PublicGood.msurplus
#print axioms MWG.ExternalitiesPublicGoods.PublicGood.hasDerivAt_surplus
#print axioms MWG.ExternalitiesPublicGoods.PublicGood.anti_msurplus
#print axioms MWG.ExternalitiesPublicGoods.PublicGood.IsOptimal
#print axioms MWG.ExternalitiesPublicGoods.PublicGood.pareto_iff_optimal
#print axioms MWG.ExternalitiesPublicGoods.PublicGood.eq_11_C_1
#print axioms MWG.ExternalitiesPublicGoods.PublicGood.optimal_unique
#print axioms MWG.ExternalitiesPublicGoods.PublicGood.IsConsumerChoice
#print axioms MWG.ExternalitiesPublicGoods.PublicGood.consumer_foc
#print axioms MWG.ExternalitiesPublicGoods.PublicGood.IsFirmChoice
#print axioms MWG.ExternalitiesPublicGoods.PublicGood.firm_foc
#print axioms MWG.ExternalitiesPublicGoods.PublicGood.IsSubsidyEq
#print axioms MWG.ExternalitiesPublicGoods.PublicGood.IsPrivateEq
#print axioms MWG.ExternalitiesPublicGoods.PublicGood.others_nonneg
#print axioms MWG.ExternalitiesPublicGoods.PublicGood.subsidyEq_iff
#print axioms MWG.ExternalitiesPublicGoods.PublicGood.eq_11_C_3_4
#print axioms MWG.ExternalitiesPublicGoods.PublicGood.eq_11_C_5
#print axioms MWG.ExternalitiesPublicGoods.PublicGood.underprovision
#print axioms MWG.ExternalitiesPublicGoods.PublicGood.public_bad_excess
#print axioms MWG.ExternalitiesPublicGoods.PublicGood.stark_free_rider
#print axioms MWG.ExternalitiesPublicGoods.PublicGood.exercise_11_C_1
#print axioms MWG.ExternalitiesPublicGoods.PublicGood.exercise_11_C_1_exists
#print axioms MWG.ExternalitiesPublicGoods.PublicGood.exercise_11_C_2
#print axioms MWG.ExternalitiesPublicGoods.PublicGood.exercise_11_C_2_exists
#print axioms MWG.ExternalitiesPublicGoods.PublicGood.IsLindahlEq
#print axioms MWG.ExternalitiesPublicGoods.PublicGood.eq_11_C_6
#print axioms MWG.ExternalitiesPublicGoods.PublicGood.lindahl_optimal
#print axioms MWG.ExternalitiesPublicGoods.PublicGood.lindahl_exists
#print axioms MWG.ExternalitiesPublicGoods.PublicGood.footnote_11
#print axioms MWG.ExternalitiesPublicGoods.pgEx
#print axioms MWG.ExternalitiesPublicGoods.pgEx_values
#print axioms MWG.ExternalitiesPublicGoods.sum_update_eq
#print axioms MWG.ExternalitiesPublicGoods.dir_foc
#print axioms MWG.ExternalitiesPublicGoods.Multilateral
#print axioms MWG.ExternalitiesPublicGoods.Multilateral.mk
#print axioms MWG.ExternalitiesPublicGoods.Multilateral.φ
#print axioms MWG.ExternalitiesPublicGoods.Multilateral.dφ
#print axioms MWG.ExternalitiesPublicGoods.Multilateral.pr
#print axioms MWG.ExternalitiesPublicGoods.Multilateral.dpr
#print axioms MWG.ExternalitiesPublicGoods.Multilateral.hφ
#print axioms MWG.ExternalitiesPublicGoods.Multilateral.hpr
#print axioms MWG.ExternalitiesPublicGoods.Multilateral.antiφ
#print axioms MWG.ExternalitiesPublicGoods.Multilateral.antipr
#print axioms MWG.ExternalitiesPublicGoods.Multilateral.IsUnfetteredEq
#print axioms MWG.ExternalitiesPublicGoods.Multilateral.eq_11_D_1
#print axioms MWG.ExternalitiesPublicGoods.Multilateral.footnote_13
#print axioms MWG.ExternalitiesPublicGoods.Multilateral.DeplFeas
#print axioms MWG.ExternalitiesPublicGoods.Multilateral.deplObj
#print axioms MWG.ExternalitiesPublicGoods.Multilateral.IsDeplOpt
#print axioms MWG.ExternalitiesPublicGoods.Multilateral.DeplKKT
#print axioms MWG.ExternalitiesPublicGoods.Multilateral.deplKKT_sufficient
#print axioms MWG.ExternalitiesPublicGoods.Multilateral.deplKKT_necessary
#print axioms MWG.ExternalitiesPublicGoods.Multilateral.eq_11_D_3_4
#print axioms MWG.ExternalitiesPublicGoods.Multilateral.IsDeplMarketEq
#print axioms MWG.ExternalitiesPublicGoods.Multilateral.consumer_sell_iff
#print axioms MWG.ExternalitiesPublicGoods.Multilateral.firm_buy_iff
#print axioms MWG.ExternalitiesPublicGoods.Multilateral.deplMarket_optimal
#print axioms MWG.ExternalitiesPublicGoods.Multilateral.deplMarket_exists
#print axioms MWG.ExternalitiesPublicGoods.Multilateral.nondeplObj
#print axioms MWG.ExternalitiesPublicGoods.Multilateral.IsNondeplOpt
#print axioms MWG.ExternalitiesPublicGoods.Multilateral.NondeplFOC
#print axioms MWG.ExternalitiesPublicGoods.Multilateral.eq_11_D_6
#print axioms MWG.ExternalitiesPublicGoods.Multilateral.nondepl_excess
#print axioms MWG.ExternalitiesPublicGoods.Multilateral.nondepl_quota
#print axioms MWG.ExternalitiesPublicGoods.Multilateral.IsFirmTaxChoice
#print axioms MWG.ExternalitiesPublicGoods.Multilateral.nondepl_tax
#print axioms MWG.ExternalitiesPublicGoods.Multilateral.footnote_15
#print axioms MWG.ExternalitiesPublicGoods.Multilateral.IsPermitEq
#print axioms MWG.ExternalitiesPublicGoods.Multilateral.permit_demand_iff
#print axioms MWG.ExternalitiesPublicGoods.Multilateral.permits_equilibrium
#print axioms MWG.ExternalitiesPublicGoods.Multilateral.permits_unique
#print axioms MWG.ExternalitiesPublicGoods.mlEx
#print axioms MWG.ExternalitiesPublicGoods.mlEx_values
#print axioms MWG.ExternalitiesPublicGoods.twoLevel_optimal_iff
#print axioms MWG.ExternalitiesPublicGoods.bargObj
#print axioms MWG.ExternalitiesPublicGoods.eq_11_E_1_gt
#print axioms MWG.ExternalitiesPublicGoods.eq_11_E_1_inefficient
#print axioms MWG.ExternalitiesPublicGoods.heavyG
#print axioms MWG.ExternalitiesPublicGoods.eq_11_E_1_no_solution
#print axioms MWG.ExternalitiesPublicGoods.expG
#print axioms MWG.ExternalitiesPublicGoods.eq_11_E_1_exponential
#print axioms MWG.ExternalitiesPublicGoods.IsQuotaChoice
#print axioms MWG.ExternalitiesPublicGoods.quota_binds
#print axioms MWG.ExternalitiesPublicGoods.surplus_loss_integral
#print axioms MWG.ExternalitiesPublicGoods.IsTaxChoice'
#print axioms MWG.ExternalitiesPublicGoods.lq_tax_choice
#print axioms MWG.ExternalitiesPublicGoods.lq_quota_choice
#print axioms MWG.ExternalitiesPublicGoods.figure_11_E_4a
#print axioms MWG.ExternalitiesPublicGoods.figure_11_E_4b
#print axioms MWG.ExternalitiesPublicGoods.footnote_22
#print axioms MWG.ExternalitiesPublicGoods.uniform_tax_efficient
#print axioms MWG.ExternalitiesPublicGoods.permits_ge_quota
#print axioms MWG.ExternalitiesPublicGoods.footnote_23
#print axioms MWG.ExternalitiesPublicGoods.gcGame
#print axioms MWG.ExternalitiesPublicGoods.gc_payoff_consumer
#print axioms MWG.ExternalitiesPublicGoods.gc_payoff_firm
#print axioms MWG.ExternalitiesPublicGoods.gc_consumer_truth
#print axioms MWG.ExternalitiesPublicGoods.gc_firm_truth
#print axioms MWG.ExternalitiesPublicGoods.exercise_11_E_4
#print axioms MWG.ExternalitiesPublicGoods.gc_optimal
#print axioms MWG.ExternalitiesPublicGoods.weaklyDominant_unique
#print axioms MWG.ExternalitiesPublicGoods.exercise_11_E_3
#print axioms MWG.ExternalitiesPublicGoods.gcRevenue
#print axioms MWG.ExternalitiesPublicGoods.gc_deficit
#print axioms MWG.ExternalitiesPublicGoods.gc_no_budget_balance
#print axioms MWG.ExternalitiesPublicGoods.gc_surplus_somewhere
#print axioms MWG.ExternalitiesPublicGoods.projGame
#print axioms MWG.ExternalitiesPublicGoods.proj_payoff
#print axioms MWG.ExternalitiesPublicGoods.exercise_11_E_5_truth
#print axioms MWG.ExternalitiesPublicGoods.exercise_11_E_5_strict
#print axioms MWG.ExternalitiesPublicGoods.exercise_11_E_5_efficient
#print axioms MWG.ExternalitiesPublicGoods.projBudget
#print axioms MWG.ExternalitiesPublicGoods.exercise_11_E_5_balance
#print axioms MWG.ExternalitiesPublicGoods.exercise_11_E_6
#print axioms MWG.ExternalitiesPublicGoods.exercise_11_E_6_selector
#print axioms MWG.ExternalitiesPublicGoods.exercise_11_E_5_balance_instance
#print axioms MWG.ExternalitiesPublicGoods.aa1Gamma
#print axioms MWG.ExternalitiesPublicGoods.example_11_AA_1
#print axioms MWG.ExternalitiesPublicGoods.example_11_AA_1_concave_in_z
#print axioms MWG.ExternalitiesPublicGoods.example_11_AA_1_convex
#print axioms MWG.ExternalitiesPublicGoods.example_11_AA_1_alpha_zero
#print axioms MWG.ExternalitiesPublicGoods.example_11_AA_1_alpha_one
#print axioms MWG.ExternalitiesPublicGoods.example_11_AA_2
#print axioms MWG.ExternalitiesPublicGoods.example_11_AA_2_instance
#print axioms MWG.ExternalitiesPublicGoods.aa3π₁
#print axioms MWG.ExternalitiesPublicGoods.aa3π₂
#print axioms MWG.ExternalitiesPublicGoods.aa3_surplus_le
#print axioms MWG.ExternalitiesPublicGoods.aa3_surplus_ge
#print axioms MWG.ExternalitiesPublicGoods.example_11_AA_3_optimum
#print axioms MWG.ExternalitiesPublicGoods.example_11_AA_3_local
#print axioms MWG.ExternalitiesPublicGoods.example_11_AA_3_kink
#print axioms MWG.ExternalitiesPublicGoods.exercise_11_B_1
#print axioms MWG.ExternalitiesPublicGoods.exercise_11_B_1_bees_efficient
#print axioms MWG.ExternalitiesPublicGoods.exercise_11_B_1_bribe
#print axioms MWG.ExternalitiesPublicGoods.exercise_11_B_1_subsidy
#print axioms MWG.ExternalitiesPublicGoods.exercise_11_B_2a_reduction
#print axioms MWG.ExternalitiesPublicGoods.compensated_iff
#print axioms MWG.ExternalitiesPublicGoods.exercise_11_B_2a_convex
#print axioms MWG.ExternalitiesPublicGoods.exercise_11_B_2a_slope
#print axioms MWG.ExternalitiesPublicGoods.exercise_11_B_2a
#print axioms MWG.ExternalitiesPublicGoods.exercise_11_B_2a_instance
#print axioms MWG.ExternalitiesPublicGoods.exercise_11_B_2b
#print axioms MWG.ExternalitiesPublicGoods.exercise_11_B_2c_invariant
#print axioms MWG.ExternalitiesPublicGoods.exercise_11_B_2c_counterexample
#print axioms MWG.ExternalitiesPublicGoods.exercise_11_B_2c_corrected
#print axioms MWG.ExternalitiesPublicGoods.exercise_11_B_2c_sign
#print axioms MWG.ExternalitiesPublicGoods.Bilateral.exercise_11_B_3_tax
#print axioms MWG.ExternalitiesPublicGoods.Bilateral.exercise_11_B_3_quota
#print axioms MWG.ExternalitiesPublicGoods.exercise_11_B_4
#print axioms MWG.ExternalitiesPublicGoods.exercise_11_B_4_no_tax_e
#print axioms MWG.ExternalitiesPublicGoods.quadrant
#print axioms MWG.ExternalitiesPublicGoods.convex_quadrant
#print axioms MWG.ExternalitiesPublicGoods.lines_deriv
#print axioms MWG.ExternalitiesPublicGoods.exercise_11_B_5_firm
#print axioms MWG.ExternalitiesPublicGoods.exercise_11_B_5b
#print axioms MWG.ExternalitiesPublicGoods.exercise_11_B_5c
#print axioms MWG.ExternalitiesPublicGoods.exercise_11_B_5d
#print axioms MWG.ExternalitiesPublicGoods.exercise_11_B_5_instance
#print axioms MWG.ExternalitiesPublicGoods.taxPGForm
#print axioms MWG.ExternalitiesPublicGoods.taxPGForm_single
#print axioms MWG.ExternalitiesPublicGoods.taxPGForm_snd
#print axioms MWG.ExternalitiesPublicGoods.exercise_11_C_3
#print axioms MWG.ExternalitiesPublicGoods.exercise_11_C_3_instance
#print axioms MWG.ExternalitiesPublicGoods.studentGame
#print axioms MWG.ExternalitiesPublicGoods.student_dev
#print axioms MWG.ExternalitiesPublicGoods.exercise_11_D_1
#print axioms MWG.ExternalitiesPublicGoods.exercise_11_D_1_pareto
#print axioms MWG.ExternalitiesPublicGoods.exercise_11_D_1_instance
#print axioms MWG.ExternalitiesPublicGoods.d2Obj
#print axioms MWG.ExternalitiesPublicGoods.d2Obj_concave
#print axioms MWG.ExternalitiesPublicGoods.d2Obj_hasFDerivAt
#print axioms MWG.ExternalitiesPublicGoods.exercise_11_D_2_opt
#print axioms MWG.ExternalitiesPublicGoods.concave1_kt_iff
#print axioms MWG.ExternalitiesPublicGoods.d2_own
#print axioms MWG.ExternalitiesPublicGoods.IsD2Eq
#print axioms MWG.ExternalitiesPublicGoods.exercise_11_D_2_eq
#print axioms MWG.ExternalitiesPublicGoods.exercise_11_D_2_tax
#print axioms MWG.ExternalitiesPublicGoods.clm2_apply
#print axioms MWG.ExternalitiesPublicGoods.exercise_11_D_3_msc
#print axioms MWG.ExternalitiesPublicGoods.exercise_11_D_3_msc_deriv
#print axioms MWG.ExternalitiesPublicGoods.exercise_11_D_3
#print axioms MWG.ExternalitiesPublicGoods.exercise_11_D_3_subsidy
#print axioms MWG.ExternalitiesPublicGoods.exercise_11_D_3_optimal
#print axioms MWG.ExternalitiesPublicGoods.d4Obj
#print axioms MWG.ExternalitiesPublicGoods.d4Obj_concave
#print axioms MWG.ExternalitiesPublicGoods.exercise_11_D_4_opt
#print axioms MWG.ExternalitiesPublicGoods.firm_tax_iff
#print axioms MWG.ExternalitiesPublicGoods.exercise_11_D_4_tax
#print axioms MWG.ExternalitiesPublicGoods.exercise_11_D_4_uniform
#print axioms MWG.ExternalitiesPublicGoods.avg_gt_marginal
#print axioms MWG.ExternalitiesPublicGoods.avg_strictAnti
#print axioms MWG.ExternalitiesPublicGoods.IsCommonsEq
#print axioms MWG.ExternalitiesPublicGoods.exercise_11_D_5b
#print axioms MWG.ExternalitiesPublicGoods.exercise_11_D_5_compare
#print axioms MWG.ExternalitiesPublicGoods.exercise_11_D_5c
#print axioms MWG.ExternalitiesPublicGoods.exercise_11_D_5d
#print axioms MWG.ExternalitiesPublicGoods.exercise_11_D_5_instance
#print axioms MWG.ExternalitiesPublicGoods.LandModel
#print axioms MWG.ExternalitiesPublicGoods.LandModel.mk
#print axioms MWG.ExternalitiesPublicGoods.LandModel.α
#print axioms MWG.ExternalitiesPublicGoods.LandModel.β
#print axioms MWG.ExternalitiesPublicGoods.LandModel.μ
#print axioms MWG.ExternalitiesPublicGoods.LandModel.γ
#print axioms MWG.ExternalitiesPublicGoods.LandModel.η
#print axioms MWG.ExternalitiesPublicGoods.LandModel.hμ
#print axioms MWG.ExternalitiesPublicGoods.LandModel.hη
#print axioms MWG.ExternalitiesPublicGoods.LandModel.hβη
#print axioms MWG.ExternalitiesPublicGoods.LandModel.prof
#print axioms MWG.ExternalitiesPublicGoods.LandModel.yld
#print axioms MWG.ExternalitiesPublicGoods.LandModel.hθ
#print axioms MWG.ExternalitiesPublicGoods.LandModel.pay
#print axioms MWG.ExternalitiesPublicGoods.LandModel.exercise_11_D_6_offer
#print axioms MWG.ExternalitiesPublicGoods.LandModel.memberPay
#print axioms MWG.ExternalitiesPublicGoods.LandModel.outPay
#print axioms MWG.ExternalitiesPublicGoods.LandModel.exercise_11_D_6_stay
#print axioms MWG.ExternalitiesPublicGoods.LandModel.exercise_11_D_6_join
#print axioms MWG.ExternalitiesPublicGoods.LandModel.IsMembershipEq
#print axioms MWG.ExternalitiesPublicGoods.LandModel.membershipEq_iff
#print axioms MWG.ExternalitiesPublicGoods.LandModel.exercise_11_D_6a
#print axioms MWG.ExternalitiesPublicGoods.LandModel.exercise_11_D_6b
#print axioms MWG.ExternalitiesPublicGoods.LandModel.exercise_11_D_6b_limit
#print axioms MWG.ExternalitiesPublicGoods.landEx
#print axioms MWG.ExternalitiesPublicGoods.nbUtil
#print axioms MWG.ExternalitiesPublicGoods.exercise_11_D_7a_allA
#print axioms MWG.ExternalitiesPublicGoods.exercise_11_D_7a_allB
#print axioms MWG.ExternalitiesPublicGoods.exercise_11_D_7a_counterexample
#print axioms MWG.ExternalitiesPublicGoods.exercise_11_D_7b
#print axioms MWG.ExternalitiesPublicGoods.avg_interval
#print axioms MWG.ExternalitiesPublicGoods.exercise_11_D_7b_cutoff
#print axioms MWG.ExternalitiesPublicGoods.exercise_11_D_7c
#print axioms MWG.ExternalitiesPublicGoods.quad_integral
#print axioms MWG.ExternalitiesPublicGoods.lqπ
#print axioms MWG.ExternalitiesPublicGoods.lqφ
#print axioms MWG.ExternalitiesPublicGoods.lq_tax_response
#print axioms MWG.ExternalitiesPublicGoods.exercise_11_E_1a
#print axioms MWG.ExternalitiesPublicGoods.exercise_11_E_1_tax_value
#print axioms MWG.ExternalitiesPublicGoods.exercise_11_E_1b
#print axioms MWG.ExternalitiesPublicGoods.exercise_11_E_1c
#print axioms MWG.ExternalitiesPublicGoods.exercise_11_E_2
#print axioms MWG.ExternalitiesPublicGoods.exercise_11_E_2_compare
#print axioms MWG.ExternalitiesPublicGoods.exercise_11_E_moments_instance
#print axioms MWG.ExternalitiesPublicGoods.exercise_11_E_7
#print axioms MWG.ExternalitiesPublicGoods.exercise_11_E_7_printed
#print axioms MWG.ExternalitiesPublicGoods.mlEx_depl
#print axioms MWG.ExternalitiesPublicGoods.quota_binds_instance
#print axioms MWG.ExternalitiesPublicGoods.exercise_11_B_2b_instance
#print axioms MWG.ExternalitiesPublicGoods.exercise_11_B_2c_instance
#print axioms MWG.ExternalitiesPublicGoods.exercise_11_B_4_instance
#print axioms MWG.ExternalitiesPublicGoods.exercise_11_D_2_instance
#print axioms MWG.ExternalitiesPublicGoods.exercise_11_D_3_instance
#print axioms MWG.ExternalitiesPublicGoods.exercise_11_D_4_instance
