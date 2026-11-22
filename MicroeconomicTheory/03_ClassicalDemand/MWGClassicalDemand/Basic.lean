/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGConsumerChoice.DemandBasics
import PreferenceProperties.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Order.Basic

/-!
# Classical demand theory: the shared foundation

MWG, Sections 3.B-3.D, pp. 40-57. This module fixes the objects used throughout Chapter 3.

* The commodity space is `Fin L → ℝ` with the consumption set `X` a subset of it; the
  default consumption set is MWG Chapter 2's `nonnegOrthant L` (`ℝ^L_+`).
* A preference relation is a relation `r : (Fin L → ℝ) → (Fin L → ℝ) → Prop` (`r x y` reads
  `x ≿ y`). Every property is stated *on a consumption set* `X`, i.e. quantified over the
  bundles in `X` only, so one relation can be studied on `ℝ^L_+` or on the quasilinear domain
  `(-∞, ∞) × ℝ^{L-1}_+` (Definition 3.B.7). Strict preference and indifference are Kreps
  Chapter 2's `Strict` and `Indifferent` (they are the derived relations of MWG Chapter 1).
* Definitions 3.B.1-3.B.7 and 3.C.1: rationality, monotonicity, strong monotonicity, local
  nonsatiation (with the book's Euclidean distance, footnote 3), contour and indifference
  sets, convexity, strict convexity, homotheticity, quasilinearity and continuity.
* Section 3.D: the utility maximization problem on a consumption set, the Walrasian demand
  correspondence `x(p, w)` (from a utility or directly from a preference), and the indirect
  utility function `v(p, w) = sup {u(x) : x ∈ B_{p,w}}`.

Representation of a preference by a utility on a consumption set is `RepresentsOn`.
-/

namespace MWG.ClassicalDemand

open MWG.ConsumerChoice Kreps.PreferenceProperties

variable {L : ℕ}

/-- **Footnote 3** (MWG, p. 42). The Euclidean distance `‖x - y‖ = (∑ (x_l - y_l)^2)^{1/2}`
between two commodity bundles. -/
noncomputable def euclidDist (x y : Fin L → ℝ) : ℝ := Real.sqrt (∑ l, (x l - y l) ^ 2)

/-- The Euclidean distance is nonnegative. -/
theorem euclidDist_nonneg (x y : Fin L → ℝ) : 0 ≤ euclidDist x y := Real.sqrt_nonneg _

/-- The Euclidean distance is symmetric. -/
theorem euclidDist_comm (x y : Fin L → ℝ) : euclidDist x y = euclidDist y x := by
  unfold euclidDist
  congr 1
  exact Finset.sum_congr rfl fun l _ => by ring

/-- Each coordinate difference is bounded by the Euclidean distance. -/
theorem abs_sub_le_euclidDist (x y : Fin L → ℝ) (l : Fin L) : |x l - y l| ≤ euclidDist x y := by
  unfold euclidDist
  rw [← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  exact Finset.single_le_sum (f := fun l => (x l - y l) ^ 2) (fun _ _ => sq_nonneg _)
    (Finset.mem_univ l)

/-- The sup-norm distance of Mathlib's `Fin L → ℝ` is at most the Euclidean distance. -/
theorem dist_le_euclidDist (x y : Fin L → ℝ) : dist x y ≤ euclidDist x y := by
  rw [dist_pi_le_iff (euclidDist_nonneg x y)]
  intro l
  rw [Real.dist_eq]
  exact abs_sub_le_euclidDist x y l

/-- The Euclidean distance is at most `√L` times the sup-norm distance. -/
theorem euclidDist_le_sqrt_mul_dist (x y : Fin L → ℝ) :
    euclidDist x y ≤ Real.sqrt L * dist x y := by
  unfold euclidDist
  rw [← Real.sqrt_sq dist_nonneg, ← Real.sqrt_mul (Nat.cast_nonneg L)]
  apply Real.sqrt_le_sqrt
  have h : ∀ l, (x l - y l) ^ 2 ≤ dist x y ^ 2 := by
    intro l
    rw [← sq_abs]
    have := dist_le_pi_dist x y l
    rw [Real.dist_eq] at this
    exact pow_le_pow_left₀ (abs_nonneg _) this 2
  calc ∑ l, (x l - y l) ^ 2 ≤ ∑ _l : Fin L, dist x y ^ 2 := Finset.sum_le_sum fun l _ => h l
    _ = L * dist x y ^ 2 := by simp

/-- Translating a bundle by `c` in every coordinate moves it Euclidean distance `√L |c|`. -/
theorem euclidDist_add_const (x : Fin L → ℝ) (c : ℝ) :
    euclidDist (x + fun _ => c) x = Real.sqrt L * |c| := by
  unfold euclidDist
  rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (Nat.cast_nonneg L)]
  congr 1
  simp

/-- A finite family of positive numbers has a common positive lower bound. -/
theorem exists_pos_le_of_pos (f : Fin L → ℝ) (hf : ∀ l, 0 < f l) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ l, ε ≤ f l := by
  classical
  refine ⟨(insert 1 (Finset.univ.image f)).min' (Finset.insert_nonempty _ _), ?_, ?_⟩
  · rw [Finset.lt_min'_iff]
    intro y hy
    rcases Finset.mem_insert.mp hy with h | h
    · rw [h]
      exact one_pos
    · obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp h
      exact hf l
  · intro l
    exact Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem f
      (Finset.mem_univ l)))

/-- **Definition 3.B.1** (MWG, p. 42). A preference relation is rational on the consumption set
`X` if it is complete and transitive on `X`. -/
def RationalOn (X : Set (Fin L → ℝ)) (r : (Fin L → ℝ) → (Fin L → ℝ) → Prop) : Prop :=
  (∀ x ∈ X, ∀ y ∈ X, r x y ∨ r y x) ∧
    (∀ x ∈ X, ∀ y ∈ X, ∀ z ∈ X, r x y → r y z → r x z)

/-- The restriction of a relation on commodity vectors to the bundles of `X`. -/
def restrictPref (X : Set (Fin L → ℝ)) (r : (Fin L → ℝ) → (Fin L → ℝ) → Prop) :
    X → X → Prop := fun a b => r a.1 b.1

/-- A utility function `u` represents `r` on `X`: `x ≿ y ⟺ u(x) ≥ u(y)` for `x, y ∈ X`
(MWG, Definition 1.B.2, used on the consumption set throughout Chapter 3). -/
def RepresentsOn (X : Set (Fin L → ℝ)) (u : (Fin L → ℝ) → ℝ)
    (r : (Fin L → ℝ) → (Fin L → ℝ) → Prop) : Prop :=
  ∀ x ∈ X, ∀ y ∈ X, r x y ↔ u y ≤ u x

/-- The preference relation represented by a utility function: `x ≿ y ⟺ u(x) ≥ u(y)`. -/
def utilityPref (u : (Fin L → ℝ) → ℝ) (x y : Fin L → ℝ) : Prop := u y ≤ u x

/-- **Definition 3.B.2** (MWG, p. 42). `≿` is monotone on `X` if `x ∈ X` and `y ≫ x` imply
`y ≻ x`. (The book also assumes free disposal of `X`; the definition asks for `y ∈ X`.) -/
def PrefMonotone (X : Set (Fin L → ℝ)) (r : (Fin L → ℝ) → (Fin L → ℝ) → Prop) : Prop :=
  ∀ x ∈ X, ∀ y ∈ X, (∀ l, x l < y l) → Strict r y x

/-- **Definition 3.B.2** (MWG, p. 42). `≿` is strongly monotone on `X` if `y ≥ x` and `y ≠ x`
imply `y ≻ x`. -/
def PrefStronglyMonotone (X : Set (Fin L → ℝ)) (r : (Fin L → ℝ) → (Fin L → ℝ) → Prop) :
    Prop :=
  ∀ x ∈ X, ∀ y ∈ X, x ≤ y → y ≠ x → Strict r y x

/-- **Definition 3.B.3** (MWG, p. 42). `≿` is locally nonsatiated on `X` if for every `x ∈ X`
and `ε > 0` there is `y ∈ X` with `‖y - x‖ ≤ ε` (Euclidean distance) and `y ≻ x`. -/
def LocallyNonsatiated (X : Set (Fin L → ℝ)) (r : (Fin L → ℝ) → (Fin L → ℝ) → Prop) :
    Prop :=
  ∀ x ∈ X, ∀ ε : ℝ, 0 < ε → ∃ y ∈ X, euclidDist y x ≤ ε ∧ Strict r y x

/-- **Section 3.B** (MWG, p. 43). The upper contour set `{y ∈ X : y ≿ x}`. -/
def upperContour (X : Set (Fin L → ℝ)) (r : (Fin L → ℝ) → (Fin L → ℝ) → Prop)
    (x : Fin L → ℝ) : Set (Fin L → ℝ) := {y | y ∈ X ∧ r y x}

/-- **Section 3.B** (MWG, p. 43). The lower contour set `{y ∈ X : x ≿ y}`. -/
def lowerContour (X : Set (Fin L → ℝ)) (r : (Fin L → ℝ) → (Fin L → ℝ) → Prop)
    (x : Fin L → ℝ) : Set (Fin L → ℝ) := {y | y ∈ X ∧ r x y}

/-- **Section 3.B** (MWG, p. 43). The indifference set `{y ∈ X : y ∼ x}`. -/
def indifferenceSet (X : Set (Fin L → ℝ)) (r : (Fin L → ℝ) → (Fin L → ℝ) → Prop)
    (x : Fin L → ℝ) : Set (Fin L → ℝ) := {y | y ∈ X ∧ Indifferent r y x}

/-- **Definition 3.B.4** (MWG, p. 44). `≿` is convex on `X` if every upper contour set
`{y ∈ X : y ≿ x}`, `x ∈ X`, is convex. -/
def PrefConvex (X : Set (Fin L → ℝ)) (r : (Fin L → ℝ) → (Fin L → ℝ) → Prop) : Prop :=
  ∀ x ∈ X, Convex ℝ (upperContour X r x)

/-- **Definition 3.B.5** (MWG, p. 44). `≿` is strictly convex on `X` if `y ≿ x`, `z ≿ x` and
`y ≠ z` imply `αy + (1 - α)z ≻ x` for all `α ∈ (0, 1)`. -/
def PrefStrictlyConvex (X : Set (Fin L → ℝ)) (r : (Fin L → ℝ) → (Fin L → ℝ) → Prop) :
    Prop :=
  ∀ x ∈ X, ∀ y ∈ X, ∀ z ∈ X, r y x → r z x → y ≠ z → ∀ α : ℝ, 0 < α → α < 1 →
    Strict r (α • y + (1 - α) • z) x

/-- **Definition 3.B.6** (MWG, p. 45). `≿` is homothetic on `X` if `x ∼ y` implies
`αx ∼ αy` for every `α ≥ 0`. (The book defines homotheticity for monotone `≿` on `ℝ^L_+`;
monotonicity is a separate hypothesis wherever it is used.) -/
def Homothetic (X : Set (Fin L → ℝ)) (r : (Fin L → ℝ) → (Fin L → ℝ) → Prop) : Prop :=
  ∀ x ∈ X, ∀ y ∈ X, Indifferent r x y → ∀ α : ℝ, 0 ≤ α → Indifferent r (α • x) (α • y)

/-- **Definition 3.B.7** (MWG, p. 45). The quasilinear consumption set
`(-∞, ∞) × ℝ^{L-1}_+` with numeraire commodity `k`: every other coordinate is nonnegative
(footnote 5 allows any commodity as numeraire; the book's case is `k = 1`). -/
def quasilinearDomain (k : Fin L) : Set (Fin L → ℝ) := {x | ∀ l, l ≠ k → 0 ≤ x l}

/-- The unit vector `e_k`. -/
def unitVec (k : Fin L) : Fin L → ℝ := Pi.single k 1

/-- **Definition 3.B.7** (MWG, p. 45). `≿` on `(-∞, ∞) × ℝ^{L-1}_+` is quasilinear with
respect to commodity `k`: (i) `x ∼ y` implies `x + αe_k ∼ y + αe_k` for all `α ∈ ℝ`, and
(ii) good `k` is desirable, `x + αe_k ≻ x` for all `x` and `α > 0`. -/
def QuasilinearWrt (k : Fin L) (r : (Fin L → ℝ) → (Fin L → ℝ) → Prop) : Prop :=
  (∀ x ∈ quasilinearDomain k, ∀ y ∈ quasilinearDomain k, Indifferent r x y →
      ∀ α : ℝ, Indifferent r (x + α • unitVec k) (y + α • unitVec k)) ∧
    ∀ x ∈ quasilinearDomain k, ∀ α : ℝ, 0 < α → Strict r (x + α • unitVec k) x

/-- **Definition 3.C.1** (MWG, p. 46). `≿` is continuous on `X` if it is preserved under
limits: whenever `xⁿ ≿ yⁿ` for all `n` with `xⁿ → x`, `yⁿ → y` (all in `X`), `x ≿ y`. -/
def PrefContinuous (X : Set (Fin L → ℝ)) (r : (Fin L → ℝ) → (Fin L → ℝ) → Prop) : Prop :=
  ∀ (xs ys : ℕ → Fin L → ℝ) (x y : Fin L → ℝ), (∀ n, xs n ∈ X) → (∀ n, ys n ∈ X) →
    x ∈ X → y ∈ X → (∀ n, r (xs n) (ys n)) →
    Filter.Tendsto xs Filter.atTop (nhds x) → Filter.Tendsto ys Filter.atTop (nhds y) → r x y

/-- **Section 3.D** (MWG, p. 50). The solution set of the utility maximization problem on the
consumption set `X`: `max u(x)` subject to `x ∈ X`, `p·x ≤ w`. -/
def walrasianDemandOn (X : Set (Fin L → ℝ)) (u : (Fin L → ℝ) → ℝ) (p : Fin L → ℝ)
    (w : ℝ) : Set (Fin L → ℝ) :=
  {x | x ∈ budgetSetOn X p w ∧ ∀ y ∈ budgetSetOn X p w, u y ≤ u x}

/-- **Section 3.D** (MWG, p. 51). The Walrasian demand correspondence `x(p, w)`: the solution
set of the UMP `max_{x ≥ 0} u(x)` subject to `p·x ≤ w`. -/
def walrasianDemand (u : (Fin L → ℝ) → ℝ) : DemandCorrespondence L :=
  fun p w => walrasianDemandOn (nonnegOrthant L) u p w

/-- **Section 3.D** (MWG, p. 51). The Walrasian demand correspondence of a preference
relation: the `≿`-best elements of `B_{p,w}`. -/
def walrasianDemandPref (r : (Fin L → ℝ) → (Fin L → ℝ) → Prop) : DemandCorrespondence L :=
  fun p w => {x | x ∈ budgetSet p w ∧ ∀ y ∈ budgetSet p w, r x y}

/-- **Section 3.D** (MWG, p. 56). The value function of the UMP on `X`,
`sup {u(x) : x ∈ X, p·x ≤ w}`; it equals `u(x*)` at every solution `x*`. -/
noncomputable def indirectUtilityOn (X : Set (Fin L → ℝ)) (u : (Fin L → ℝ) → ℝ)
    (p : Fin L → ℝ) (w : ℝ) : ℝ := sSup (u '' budgetSetOn X p w)

/-- **Section 3.D** (MWG, p. 56). The indirect utility function `v(p, w)`. -/
noncomputable def indirectUtility (u : (Fin L → ℝ) → ℝ) (p : Fin L → ℝ) (w : ℝ) : ℝ :=
  indirectUtilityOn (nonnegOrthant L) u p w

/-- Membership in the Walrasian demand correspondence, unfolded. -/
theorem mem_walrasianDemand_iff (u : (Fin L → ℝ) → ℝ) (p : Fin L → ℝ) (w : ℝ)
    (x : Fin L → ℝ) :
    x ∈ walrasianDemand u p w ↔ x ∈ budgetSet p w ∧ ∀ y ∈ budgetSet p w, u y ≤ u x :=
  Iff.rfl

/-- The demand of a utility function is the demand of the preference it induces. -/
theorem walrasianDemand_eq_pref (u : (Fin L → ℝ) → ℝ) :
    walrasianDemand u = walrasianDemandPref (utilityPref u) := rfl

/-- If `u` represents `≿` on `ℝ^L_+`, the utility and preference demands coincide. -/
theorem walrasianDemand_eq_pref_of_represents {u : (Fin L → ℝ) → ℝ}
    {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop} (hu : RepresentsOn (nonnegOrthant L) u r)
    (p : Fin L → ℝ) (w : ℝ) : walrasianDemand u p w = walrasianDemandPref r p w := by
  ext x
  constructor
  · rintro ⟨hx, hmax⟩
    exact ⟨hx, fun y hy => (hu x hx.1 y hy.1).mpr (hmax y hy)⟩
  · rintro ⟨hx, hmax⟩
    exact ⟨hx, fun y hy => (hu x hx.1 y hy.1).mp (hmax y hy)⟩

/-- The indirect utility equals the utility of any demanded bundle. -/
theorem indirectUtilityOn_eq_of_mem {X : Set (Fin L → ℝ)} {u : (Fin L → ℝ) → ℝ}
    {p : Fin L → ℝ} {w : ℝ} {x : Fin L → ℝ} (hx : x ∈ walrasianDemandOn X u p w) :
    indirectUtilityOn X u p w = u x := by
  apply IsGreatest.csSup_eq
  refine ⟨⟨x, hx.1, rfl⟩, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  exact hx.2 y hy

/-- **Section 3.D** (MWG, p. 56). `v(p, w) = u(x*)` for any `x* ∈ x(p, w)`. -/
theorem indirectUtility_eq_of_mem {u : (Fin L → ℝ) → ℝ} {p : Fin L → ℝ} {w : ℝ}
    {x : Fin L → ℝ} (hx : x ∈ walrasianDemand u p w) : indirectUtility u p w = u x :=
  indirectUtilityOn_eq_of_mem hx

/-- Rationality on `X` is Kreps's rationality of the restricted relation. -/
theorem rationalOn_iff_rational (X : Set (Fin L → ℝ))
    (r : (Fin L → ℝ) → (Fin L → ℝ) → Prop) :
    RationalOn X r ↔ Rational (restrictPref X r) := by
  constructor
  · rintro ⟨hc, ht⟩
    exact ⟨fun a b => hc a.1 a.2 b.1 b.2, fun a b c => ht a.1 a.2 b.1 b.2 c.1 c.2⟩
  · rintro ⟨hc, ht⟩
    exact ⟨fun x hx y hy => hc ⟨x, hx⟩ ⟨y, hy⟩,
      fun x hx y hy z hz => ht ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩⟩

/-- Representation on `X` is Kreps's representation of the restricted relation. -/
theorem representsOn_iff_represents (X : Set (Fin L → ℝ)) (u : (Fin L → ℝ) → ℝ)
    (r : (Fin L → ℝ) → (Fin L → ℝ) → Prop) :
    RepresentsOn X u r ↔ Represents (fun a : X => u a.1) (restrictPref X r) := by
  constructor
  · intro h a b
    exact h a.1 a.2 b.1 b.2
  · intro h x hx y hy
    exact h ⟨x, hx⟩ ⟨y, hy⟩

/-- A relation represented by a utility on `X` is rational on `X`. -/
theorem RepresentsOn.rationalOn {X : Set (Fin L → ℝ)} {u : (Fin L → ℝ) → ℝ}
    {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop} (hu : RepresentsOn X u r) : RationalOn X r := by
  refine ⟨fun x hx y hy => ?_, fun x hx y hy z hz hxy hyz => ?_⟩
  · rcases le_total (u y) (u x) with h | h
    · exact Or.inl ((hu x hx y hy).mpr h)
    · exact Or.inr ((hu y hy x hx).mpr h)
  · exact (hu x hx z hz).mpr (((hu y hy z hz).mp hyz).trans ((hu x hx y hy).mp hxy))

/-- Strict preference through a representation: `x ≻ y ⟺ u(x) > u(y)`. -/
theorem RepresentsOn.strict_iff {X : Set (Fin L → ℝ)} {u : (Fin L → ℝ) → ℝ}
    {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop} (hu : RepresentsOn X u r) {x y : Fin L → ℝ}
    (hx : x ∈ X) (hy : y ∈ X) : Strict r x y ↔ u y < u x := by
  rw [Strict, hu x hx y hy, hu y hy x hx, not_le]
  exact ⟨fun h => h.2, fun h => ⟨h.le, h⟩⟩

/-- Indifference through a representation: `x ∼ y ⟺ u(x) = u(y)`. -/
theorem RepresentsOn.indifferent_iff {X : Set (Fin L → ℝ)} {u : (Fin L → ℝ) → ℝ}
    {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop} (hu : RepresentsOn X u r) {x y : Fin L → ℝ}
    (hx : x ∈ X) (hy : y ∈ X) : Indifferent r x y ↔ u x = u y := by
  rw [Indifferent, hu x hx y hy, hu y hy x hx]
  exact ⟨fun h => le_antisymm h.2 h.1, fun h => ⟨h.ge, h.le⟩⟩

/-- A utility function represents the preference it induces, on every consumption set. -/
theorem representsOn_utilityPref (X : Set (Fin L → ℝ)) (u : (Fin L → ℝ) → ℝ) :
    RepresentsOn X u (utilityPref u) := fun _ _ _ _ => Iff.rfl

end MWG.ClassicalDemand
