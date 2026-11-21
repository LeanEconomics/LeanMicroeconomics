/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGCompetitiveMarkets.ExercisesE

/-!
# Concluding remarks on partial equilibrium analysis (MWG Section 10.G, pp. 341-343)

A group of `M` interrelated goods with quasilinear utilities `mᵢ + φᵢ(xᵢ)`, `xᵢ ∈ ℝ^M_+`, and
costs `cⱼ(qⱼ)` (p. 342).

* `group_ump_iff`: with quasilinear utility the budget binds and `xᵢ` maximizes `φᵢ(x) - p·x`;
  wealth does not enter.
* **Exercise 10.G.1**: the equilibrium conditions (`IsGroupEqm`), their first-order form
  (`group_consumer_foc`, `group_firm_foc`), independence of wealth, maximization of aggregate
  surplus, uniqueness of individual consumptions and aggregate production, and of individual
  production with strictly convex costs.
* **Exercise 10.G.2** and footnote 31: with separable utilities and costs, the market for good
  `ℓ` decouples from the rest of the group, and aggregate surplus splits.
* **Exercises 10.G.3-10.G.5**: welfare effects of taxes with interrelated demands (cross-market
  terms, substitutes and complements, the bias of single-market measures).
* Footnote 32: a backward-bending demand when consumers are endowed with good `ℓ`.
-/

namespace MWG.CompetitiveMarkets

open Filter Topology MWG.ConsumerChoice

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {M : ℕ}

/-- **(MWG, p. 342)** With quasilinear utility `m + φ(x)` on `ℝ × ℝ^M_+` and budget
`m + p·x ≤ w`, `(m, x)` solves the UMP iff the budget binds and `x` maximizes `φ(x) - p·x` on
`ℝ^M_+`: wealth only affects the numeraire. -/
theorem group_ump_iff (φ : (Fin M → ℝ) → ℝ) (p : Fin M → ℝ) (w m : ℝ) (x : Fin M → ℝ) :
    ((x ∈ nonnegOrthant M ∧ m + p ⬝ᵥ x ≤ w) ∧
      ∀ m' x', x' ∈ nonnegOrthant M → m' + p ⬝ᵥ x' ≤ w → m' + φ x' ≤ m + φ x) ↔
      x ∈ nonnegOrthant M ∧ m = w - p ⬝ᵥ x ∧
        ∀ y ∈ nonnegOrthant M, φ y - p ⬝ᵥ y ≤ φ x - p ⬝ᵥ x := by
  constructor
  · rintro ⟨⟨hx, hb⟩, hmax⟩
    have hm : m = w - p ⬝ᵥ x := by
      have := hmax (w - p ⬝ᵥ x) x hx (by linarith)
      linarith
    refine ⟨hx, hm, fun y hy => ?_⟩
    have := hmax (w - p ⬝ᵥ y) y hy (by linarith)
    linarith
  · rintro ⟨hx, hm, hmax⟩
    refine ⟨⟨hx, by linarith⟩, fun m' x' hx' hb => ?_⟩
    have := hmax x' hx'
    linarith

/-- **Exercise 10.G.1** (MWG, p. 348). Equilibrium conditions for the group of `M` goods (prices
`p`, numeraire price `1`): every `xᵢ` maximizes `φᵢ(x) - p·x` and every `qⱼ` maximizes
`p·q - cⱼ(q)` on `ℝ^M_+`, and the `M` markets clear. They do not involve wealth. -/
def IsGroupEqm (φ : ι → (Fin M → ℝ) → ℝ) (c : κ → (Fin M → ℝ) → ℝ) (x : ι → Fin M → ℝ)
    (q : κ → Fin M → ℝ) (p : Fin M → ℝ) : Prop :=
  (∀ i, x i ∈ nonnegOrthant M ∧ ∀ y ∈ nonnegOrthant M, φ i y - p ⬝ᵥ y ≤ φ i (x i) - p ⬝ᵥ x i) ∧
  (∀ j, q j ∈ nonnegOrthant M ∧ ∀ y ∈ nonnegOrthant M, p ⬝ᵥ y - c j y ≤ p ⬝ᵥ q j - c j (q j)) ∧
  ∑ i, x i = ∑ j, q j

/-- The aggregate surplus of the group, `∑ φᵢ(xᵢ) - ∑ cⱼ(qⱼ)`. -/
def groupSurplus (φ : ι → (Fin M → ℝ) → ℝ) (c : κ → (Fin M → ℝ) → ℝ) (x : ι → Fin M → ℝ)
    (q : κ → Fin M → ℝ) : ℝ :=
  ∑ i, φ i (x i) - ∑ j, c j (q j)

/-- **(MWG, p. 342; Exercise 10.G.1)** An equilibrium of the group maximizes aggregate surplus
among nonnegative allocations with `∑ xᵢ = ∑ qⱼ` (the first welfare theorem for the group). -/
theorem IsGroupEqm.maximizes {φ : ι → (Fin M → ℝ) → ℝ} {c : κ → (Fin M → ℝ) → ℝ}
    {x : ι → Fin M → ℝ} {q : κ → Fin M → ℝ} {p : Fin M → ℝ} (h : IsGroupEqm φ c x q p)
    {x' : ι → Fin M → ℝ} {q' : κ → Fin M → ℝ} (hx' : ∀ i, x' i ∈ nonnegOrthant M)
    (hq' : ∀ j, q' j ∈ nonnegOrthant M) (hs : ∑ i, x' i = ∑ j, q' j) :
    groupSurplus φ c x' q' ≤ groupSurplus φ c x q := by
  have e1 := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => (h.1 i).2 (x' i) (hx' i)
  have e2 := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => (h.2.1 j).2 (q' j) (hq' j)
  simp only [Finset.sum_sub_distrib, ← dotProduct_sum] at e1 e2
  rw [hs, h.2.2] at e1
  simp only [groupSurplus]
  linarith

/-- **Exercise 10.G.1** (MWG, pp. 348-349): uniqueness. If every `φᵢ` is strictly concave and
every `cⱼ` convex on `ℝ^M_+`, any two equilibria (at possibly different prices) have the same
individual consumptions and the same aggregate production. -/
theorem exercise_10_G_1_unique {φ : ι → (Fin M → ℝ) → ℝ} {c : κ → (Fin M → ℝ) → ℝ}
    (hφ : ∀ i, StrictConcaveOn ℝ (nonnegOrthant M) (φ i))
    (hc : ∀ j, ConvexOn ℝ (nonnegOrthant M) (c j)) {x x' : ι → Fin M → ℝ}
    {q q' : κ → Fin M → ℝ} {p p' : Fin M → ℝ} (h : IsGroupEqm φ c x q p)
    (h' : IsGroupEqm φ c x' q' p') : x = x' ∧ ∑ j, q j = ∑ j, q' j := by
  have hS : groupSurplus φ c x q = groupSurplus φ c x' q' :=
    le_antisymm (h'.maximizes (fun i => (h.1 i).1) (fun j => (h.2.1 j).1) h.2.2)
      (h.maximizes (fun i => (h'.1 i).1) (fun j => (h'.2.1 j).1) h'.2.2)
  have hconv : ∀ i, (1 / 2 : ℝ) • x i + (1 / 2 : ℝ) • x' i ∈ nonnegOrthant M := fun i =>
    (hφ i).1 (h.1 i).1 (h'.1 i).1 (by norm_num) (by norm_num) (by norm_num)
  have hconvq : ∀ j, (1 / 2 : ℝ) • q j + (1 / 2 : ℝ) • q' j ∈ nonnegOrthant M := fun j =>
    (hc j).1 (h.2.1 j).1 (h'.2.1 j).1 (by norm_num) (by norm_num) (by norm_num)
  have hsm : ∑ i, ((1 / 2 : ℝ) • x i + (1 / 2 : ℝ) • x' i) =
      ∑ j, ((1 / 2 : ℝ) • q j + (1 / 2 : ℝ) • q' j) := by
    simp only [Finset.sum_add_distrib, ← Finset.smul_sum, h.2.2, h'.2.2]
  have hle := h.maximizes hconv hconvq hsm
  have hcost : ∑ j, c j ((1 / 2 : ℝ) • q j + (1 / 2 : ℝ) • q' j) ≤
      ∑ j, ((1 / 2 : ℝ) * c j (q j) + (1 / 2 : ℝ) * c j (q' j)) :=
    Finset.sum_le_sum fun j _ => by
      simpa [smul_eq_mul] using (hc j).2 (h.2.1 j).1 (h'.2.1 j).1
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  have hben : ∀ i, (1 / 2 : ℝ) * φ i (x i) + (1 / 2 : ℝ) * φ i (x' i) ≤
      φ i ((1 / 2 : ℝ) • x i + (1 / 2 : ℝ) • x' i) := fun i => by
    simpa [smul_eq_mul] using (hφ i).concaveOn.2 (h.1 i).1 (h'.1 i).1
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  have hxx : x = x' := by
    by_contra hne
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hne
    have hstrict : (1 / 2 : ℝ) * φ i (x i) + (1 / 2 : ℝ) * φ i (x' i) <
        φ i ((1 / 2 : ℝ) • x i + (1 / 2 : ℝ) • x' i) := by
      simpa [smul_eq_mul] using (hφ i).2 (h.1 i).1 (h'.1 i).1 hi
        (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
    have := Finset.sum_lt_sum (fun k (_ : k ∈ Finset.univ) => hben k)
      ⟨i, Finset.mem_univ i, hstrict⟩
    simp only [groupSurplus, Finset.sum_add_distrib, ← Finset.mul_sum] at hle hS this hcost
    linarith
  exact ⟨hxx, by rw [← h.2.2, ← h'.2.2, hxx]⟩

/-- **Exercise 10.G.1** (MWG, p. 349): with strictly convex costs individual production levels
are unique as well. -/
theorem exercise_10_G_1_unique_strict {φ : ι → (Fin M → ℝ) → ℝ} {c : κ → (Fin M → ℝ) → ℝ}
    (hφ : ∀ i, StrictConcaveOn ℝ (nonnegOrthant M) (φ i))
    (hc : ∀ j, StrictConvexOn ℝ (nonnegOrthant M) (c j)) {x x' : ι → Fin M → ℝ}
    {q q' : κ → Fin M → ℝ} {p p' : Fin M → ℝ} (h : IsGroupEqm φ c x q p)
    (h' : IsGroupEqm φ c x' q' p') : x = x' ∧ q = q' := by
  obtain ⟨hxx, -⟩ := exercise_10_G_1_unique hφ (fun j => (hc j).convexOn) h h'
  subst hxx
  refine ⟨rfl, ?_⟩
  have hS : groupSurplus φ c x q = groupSurplus φ c x q' :=
    le_antisymm (h'.maximizes (fun i => (h.1 i).1) (fun j => (h.2.1 j).1) h.2.2)
      (h.maximizes (fun i => (h'.1 i).1) (fun j => (h'.2.1 j).1) h'.2.2)
  by_contra hne
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hne
  have hconvq : ∀ j, (1 / 2 : ℝ) • q j + (1 / 2 : ℝ) • q' j ∈ nonnegOrthant M := fun j =>
    (hc j).1 (h.2.1 j).1 (h'.2.1 j).1 (by norm_num) (by norm_num) (by norm_num)
  have hsm : ∑ i, x i = ∑ k, ((1 / 2 : ℝ) • q k + (1 / 2 : ℝ) • q' k) := by
    simp only [Finset.sum_add_distrib, ← Finset.smul_sum, ← h.2.2, ← h'.2.2, ← add_smul]
    norm_num
  have hle := h.maximizes (fun i => (h.1 i).1) hconvq hsm
  have hcost : ∑ k, c k ((1 / 2 : ℝ) • q k + (1 / 2 : ℝ) • q' k) <
      ∑ k, ((1 / 2 : ℝ) * c k (q k) + (1 / 2 : ℝ) * c k (q' k)) :=
    Finset.sum_lt_sum (fun k _ => by
      simpa [smul_eq_mul] using (hc k).convexOn.2 (h.2.1 k).1 (h'.2.1 k).1
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
      ⟨j, Finset.mem_univ j, by
        simpa [smul_eq_mul] using (hc j).2 (h.2.1 j).1 (h'.2.1 j).1 hj
          (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)⟩
  simp only [groupSurplus, Finset.sum_add_distrib, ← Finset.mul_sum] at hle hS hcost
  linarith

/-- Moving along coordinate `l` from a bundle of the orthant. -/
theorem orthant_shift [DecidableEq (Fin M)] {x : Fin M → ℝ} (hx : x ∈ nonnegOrthant M)
    (l : Fin M) {t : ℝ} (ht : -x l ≤ t) : x + t • Pi.single l 1 ∈ nonnegOrthant M := by
  intro k
  simp only [Pi.add_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  by_cases hk : k = l
  · subst hk
    simp only [↓reduceIte, mul_one]
    linarith
  · simp only [hk, ↓reduceIte, mul_zero, add_zero]
    exact hx k

/-- First-order conditions on `ℝ^M_+` along a coordinate: if `x` maximizes `F` on the orthant
and `F` has partial derivative `d` in direction `l` at `x`, then `d ≤ 0`, with equality if
`x_l > 0`. -/
theorem orthant_coord_foc {F : (Fin M → ℝ) → ℝ} {x : Fin M → ℝ} (hx : x ∈ nonnegOrthant M)
    (hmax : ∀ y ∈ nonnegOrthant M, F y ≤ F x) (l : Fin M) {d : ℝ}
    (hd : HasDerivAt (fun t : ℝ => F (x + t • Pi.single l 1)) d 0) : d ≤ 0 ∧ (0 < x l → d = 0) := by
  classical
  refine ⟨?_, fun hpos => ?_⟩
  · refine (foc_max_necessary hd.hasDerivWithinAt le_rfl fun t ht => ?_).1
    rw [zero_smul, add_zero]
    exact hmax _ (orthant_shift hx l (by linarith [hx l]))
  · have hloc : IsLocalMax (fun t : ℝ => F (x + t • Pi.single l 1)) 0 := by
      filter_upwards [Ioi_mem_nhds (neg_lt_zero.2 hpos)] with t ht
      rw [zero_smul, add_zero]
      exact hmax _ (orthant_shift hx l (le_of_lt ht))
    exact hloc.hasDerivAt_eq_zero hd

theorem dot_shift [DecidableEq (Fin M)] (p x : Fin M → ℝ) (l : Fin M) (t : ℝ) :
    p ⬝ᵥ (x + t • Pi.single l 1) = p ⬝ᵥ x + t * p l := by
  rw [dotProduct_add, dotProduct_smul, dotProduct_single, mul_one, smul_eq_mul]

/-- **Exercise 10.G.1** (MWG, p. 348): the consumers' first-order conditions. If `xᵢ` is an
equilibrium bundle and `φᵢ` has partial derivative `∂φᵢ/∂x_l` at `xᵢ`, then
`∂φᵢ/∂x_l ≤ p_l`, with equality if `x_{li} > 0`. -/
theorem group_consumer_foc {φ : (Fin M → ℝ) → ℝ} {p x : Fin M → ℝ} (hx : x ∈ nonnegOrthant M)
    (hmax : ∀ y ∈ nonnegOrthant M, φ y - p ⬝ᵥ y ≤ φ x - p ⬝ᵥ x) (l : Fin M) {dl : ℝ}
    (hd : HasDerivAt (fun t : ℝ => φ (x + t • Pi.single l 1)) dl 0) :
    dl ≤ p l ∧ (0 < x l → dl = p l) := by
  classical
  have hF : HasDerivAt (fun t : ℝ => φ (x + t • Pi.single l 1) - p ⬝ᵥ (x + t • Pi.single l 1))
      (dl - p l) 0 := by
    have h2 : HasDerivAt (fun t : ℝ => p ⬝ᵥ x + t * p l) (p l) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (p l)).const_add (p ⬝ᵥ x)
    refine (hd.sub h2).congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
    simp only [dot_shift, Pi.sub_apply]
  obtain ⟨h1, h2⟩ := orthant_coord_foc (F := fun y => φ y - p ⬝ᵥ y) hx hmax l hF
  exact ⟨by linarith, fun h => by linarith [h2 h]⟩

/-- **Exercise 10.G.1** (MWG, p. 348): the firms' first-order conditions,
`p_l ≤ ∂cⱼ/∂q_l` with equality if `q_{lj} > 0`. -/
theorem group_firm_foc {c : (Fin M → ℝ) → ℝ} {p q : Fin M → ℝ} (hq : q ∈ nonnegOrthant M)
    (hmax : ∀ y ∈ nonnegOrthant M, p ⬝ᵥ y - c y ≤ p ⬝ᵥ q - c q) (l : Fin M) {dl : ℝ}
    (hd : HasDerivAt (fun t : ℝ => c (q + t • Pi.single l 1)) dl 0) :
    p l ≤ dl ∧ (0 < q l → p l = dl) := by
  classical
  have hF : HasDerivAt (fun t : ℝ => p ⬝ᵥ (q + t • Pi.single l 1) - c (q + t • Pi.single l 1))
      (p l - dl) 0 := by
    have h2 : HasDerivAt (fun t : ℝ => p ⬝ᵥ q + t * p l) (p l) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (p l)).const_add (p ⬝ᵥ q)
    refine (h2.sub hd).congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
    simp only [dot_shift, Pi.sub_apply]
  obtain ⟨h1, h2⟩ := orthant_coord_foc (F := fun y => p ⬝ᵥ y - c y) hq hmax l hF
  exact ⟨by linarith, fun h => by linarith [h2 h]⟩

/-! ## Exercise 10.G.2 and footnote 31: separable utilities and costs -/

/-- Splitting a bundle into good `l` and the others: `p·x = p_l x_l + p·x_{-l}` with
`x_{-l} = x` with `x_l` set to `0`. -/
theorem dot_split [DecidableEq (Fin M)] (p x : Fin M → ℝ) (l : Fin M) :
    p ⬝ᵥ x = p l * x l + p ⬝ᵥ Function.update x l 0 := by
  have hx : x = Function.update x l 0 + x l • Pi.single l 1 := by
    ext k
    by_cases hk : k = l
    · subst hk; simp
    · simp [hk]
  conv_lhs => rw [hx]
  rw [dotProduct_add, dotProduct_smul, dotProduct_single, mul_one, smul_eq_mul]
  ring

/-- **Exercise 10.G.2** (MWG, p. 349; footnote 31, p. 343). If `φ(x) = f(x_l) + g(x_{-l})`, then
`x` maximizes `φ(x) - p·x` on `ℝ^M_+` iff `x_l` maximizes `f(a) - p_l a` on `a ≥ 0` and `x_{-l}`
maximizes `g(y) - p·y` over bundles with `y_l = 0`: the demand for good `l` depends only on
`p_l`. -/
theorem exercise_10_G_2_consumer [DecidableEq (Fin M)] (f : ℝ → ℝ) (g : (Fin M → ℝ) → ℝ)
    (p x : Fin M → ℝ) (l : Fin M) (hx : x ∈ nonnegOrthant M) :
    (∀ y ∈ nonnegOrthant M, f (y l) + g (Function.update y l 0) - p ⬝ᵥ y ≤
        f (x l) + g (Function.update x l 0) - p ⬝ᵥ x) ↔
      (∀ a, 0 ≤ a → f a - p l * a ≤ f (x l) - p l * x l) ∧
      (∀ y ∈ nonnegOrthant M, y l = 0 →
        g y - p ⬝ᵥ y ≤ g (Function.update x l 0) - p ⬝ᵥ Function.update x l 0) := by
  constructor
  · intro h
    refine ⟨fun a ha => ?_, fun y hy hyl => ?_⟩
    · have hmem : Function.update x l a ∈ nonnegOrthant M := by
        intro k; by_cases hk : k = l
        · subst hk; simp [ha]
        · simp [hk, hx k]
      have := h _ hmem
      rw [dot_split p (Function.update x l a) l, dot_split p x l] at this
      simp only [Function.update_self, Function.update_idem] at this
      linarith
    · have hmem : Function.update y l (x l) ∈ nonnegOrthant M := by
        intro k; by_cases hk : k = l
        · subst hk; simp [hx k]
        · simp [hk, hy k]
      have := h _ hmem
      rw [dot_split p (Function.update y l (x l)) l, dot_split p x l] at this
      simp only [Function.update_self, Function.update_idem] at this
      have hyy : Function.update y l 0 = y := by
        rw [← hyl]; exact Function.update_eq_self l y
      rw [hyy] at this
      linarith
  · rintro ⟨h1, h2⟩ y hy
    have hy0 : Function.update y l 0 ∈ nonnegOrthant M := by
      intro k; by_cases hk : k = l
      · subst hk; simp
      · simp [hk, hy k]
    have e1 := h1 (y l) (hy l)
    have e2 := h2 _ hy0 (by simp)
    rw [dot_split p y l, dot_split p x l]
    linarith

/-- **Exercise 10.G.2** (MWG, p. 349): with separable utilities and costs the aggregate surplus
of the group is the surplus `∑ fᵢ(x_{li}) - ∑ c_{lj}(q_{lj})` of market `l` plus a term not
depending on good `l`; with full separability it is the sum of the single-market surpluses. -/
theorem exercise_10_G_2_surplus [DecidableEq (Fin M)] (f : ι → ℝ → ℝ)
    (g : ι → (Fin M → ℝ) → ℝ) (cl : κ → ℝ → ℝ) (d : κ → (Fin M → ℝ) → ℝ) (l : Fin M)
    (x : ι → Fin M → ℝ) (q : κ → Fin M → ℝ) :
    groupSurplus (fun i y => f i (y l) + g i (Function.update y l 0))
        (fun j y => cl j (y l) + d j (Function.update y l 0)) x q =
      (∑ i, f i (x i l) - ∑ j, cl j (q j l)) +
        (∑ i, g i (Function.update (x i) l 0) - ∑ j, d j (Function.update (q j) l 0)) := by
  simp only [groupSurplus, Finset.sum_add_distrib]
  ring

/-- Full separability (MWG, p. 349): `φᵢ(x) = ∑ₗ φ_{li}(x_l)`, `cⱼ(q) = ∑ₗ c_{lj}(q_l)` give
aggregate surplus `∑ₗ [∑ᵢ φ_{li}(x_{li}) - ∑ⱼ c_{lj}(q_{lj})]`. -/
theorem exercise_10_G_2_full (f : ι → Fin M → ℝ → ℝ) (cl : κ → Fin M → ℝ → ℝ)
    (x : ι → Fin M → ℝ) (q : κ → Fin M → ℝ) :
    groupSurplus (fun i y => ∑ l, f i l (y l)) (fun j y => ∑ l, cl j l (y l)) x q =
      ∑ l, (∑ i, f i l (x i l) - ∑ j, cl j l (q j l)) := by
  simp only [groupSurplus, Finset.sum_sub_distrib]
  rw [Finset.sum_comm (f := fun i l => f i l (x i l)),
    Finset.sum_comm (f := fun j l => cl j l (q j l))]

/-! ## Exercises 10.G.3-10.G.5 -/

/-- **Exercises 10.G.3-10.G.4** (MWG, p. 349): the welfare effect of price changes in a
three-good economy with `u = x₁ + φ(x₂, x₃)` and constant unit costs `c₂, c₃`. Along a path of
consumer prices `(p₂, p₃)` with demands `(x₂(s), x₃(s))` satisfying the consumer's first-order
condition `∇φ = (p₂, p₃)`, aggregate surplus `φ(x₂, x₃) - c₂x₂ - c₃x₃` changes at rate
`t₂ x₂' + t₃ x₃'`, where `t_k = p_k - c_k` are the taxes. -/
theorem exercise_10_G_3_4 {φ : ℝ × ℝ → ℝ} {x₂ x₃ : ℝ → ℝ} {s₀ c₂ c₃ p₂ p₃ x₂' x₃' : ℝ}
    (hφ : HasFDerivAt φ (p₂ • ContinuousLinearMap.fst ℝ ℝ ℝ + p₃ • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (x₂ s₀, x₃ s₀))
    (h₂ : HasDerivAt x₂ x₂' s₀) (h₃ : HasDerivAt x₃ x₃' s₀) :
    HasDerivAt (fun s => φ (x₂ s, x₃ s) - c₂ * x₂ s - c₃ * x₃ s)
      ((p₂ - c₂) * x₂' + (p₃ - c₃) * x₃') s₀ := by
  have h := ((hasDerivAt_comp_two hφ h₂ h₃).sub (h₂.const_mul c₂)).sub (h₃.const_mul c₃)
  exact h.congr_deriv (by ring)

/-- **Exercise 10.G.3(a)** (MWG, p. 349). If market 3 is undistorted (`t₃ = 0`), the welfare
change from a tax change in market 2 is `t₂ x₂'`, the change in the area between market 2's
demand (at the initial `p₃`) and supply curves. **(b)** If `t₃ > 0`, the single-market measure
`t₂ x₂'` differs from the true change `t₂ x₂' + t₃ x₃'` by `t₃ x₃'`: when good 3 is a substitute
(`x₃' > 0` as `p₂` rises) the single-market measure overstates the welfare loss; when it is a
complement (`x₃' < 0`) it understates it. -/
theorem exercise_10_G_3 {t₂ t₃ x₂' x₃' : ℝ} :
    (t₃ = 0 → t₂ * x₂' + t₃ * x₃' = t₂ * x₂') ∧
    (0 < t₃ → 0 < x₃' → t₂ * x₂' < t₂ * x₂' + t₃ * x₃') ∧
    (0 < t₃ → x₃' < 0 → t₂ * x₂' + t₃ * x₃' < t₂ * x₂') := by
  refine ⟨fun h => by rw [h]; ring, fun h1 h2 => ?_, fun h1 h2 => ?_⟩
  · nlinarith
  · nlinarith

/-- **Exercise 10.G.4** (MWG, p. 349). Raising both taxes along `(dt₂, dt₃)` with demand
derivatives `x_{kl} = ∂x_k/∂p_l`, the welfare change is
`t₂(x₂₂dt₂ + x₂₃dt₃) + t₃(x₃₂dt₂ + x₃₃dt₃)`. -/
theorem exercise_10_G_4 {φ : ℝ × ℝ → ℝ} {x₂ x₃ : ℝ → ℝ} {s₀ c₂ c₃ p₂ p₃ : ℝ}
    {x22 x23 x32 x33 dt₂ dt₃ : ℝ}
    (hφ : HasFDerivAt φ (p₂ • ContinuousLinearMap.fst ℝ ℝ ℝ + p₃ • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (x₂ s₀, x₃ s₀))
    (h₂ : HasDerivAt x₂ (x22 * dt₂ + x23 * dt₃) s₀)
    (h₃ : HasDerivAt x₃ (x32 * dt₂ + x33 * dt₃) s₀) :
    HasDerivAt (fun s => φ (x₂ s, x₃ s) - c₂ * x₂ s - c₃ * x₃ s)
      ((p₂ - c₂) * (x22 * dt₂ + x23 * dt₃) + (p₃ - c₃) * (x32 * dt₂ + x33 * dt₃)) s₀ :=
  exercise_10_G_3_4 hφ h₂ h₃

/-- **Exercise 10.G.5(a)** (MWG, p. 349). With upward-sloping supply in market 3
(`q₃' ≥ 0`, strictly convex `c₃`) and `∂x₃/∂p₃ < 0`, differentiating market-3 clearing
`x₃(p₂, p₃) = q₃(p₃)` gives `dp₃ = x₃₂ dp₂/(q₃' - x₃₃)`; so if the tax raises `p₂`, the price of
good 3 rises when goods 2 and 3 are substitutes (`x₃₂ > 0`) and falls when they are complements. -/
theorem exercise_10_G_5a {x32 x33 q3' dp₂ dp₃ : ℝ} (hx33 : x33 < 0) (hq : 0 ≤ q3')
    (hclear : x32 * dp₂ + x33 * dp₃ = q3' * dp₃) (hdp : 0 < dp₂) :
    dp₃ = x32 * dp₂ / (q3' - x33) ∧ (0 < x32 → 0 < dp₃) ∧ (x32 < 0 → dp₃ < 0) := by
  have hden : 0 < q3' - x33 := by linarith
  have h : dp₃ = x32 * dp₂ / (q3' - x33) := by rw [eq_div_iff hden.ne']; linarith
  refine ⟨h, fun hs => ?_, fun hc => ?_⟩
  · rw [h]; positivity
  · rw [h]; exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hc hdp) hden

/-- **Exercise 10.G.5(b)** (MWG, p. 349). Evaluating the welfare change from the tax on good 2
with the demand for good 2 at the pre-change price of good 3 omits `t₂ x₂₃ dp₃`. With symmetric
cross effects (`x₂₃ = x₃₂`, quasilinear demand), `t₂ > 0` and `dp₂ > 0`, this omitted term is
nonnegative for substitutes and for complements alike: the fixed-`p₃` formula overstates the
welfare loss in both cases. -/
theorem exercise_10_G_5b {x22 x23 x32 x33 q3' t₂ dp₂ dp₃ : ℝ} (hx33 : x33 < 0) (hq : 0 ≤ q3')
    (hsym : x23 = x32) (ht : 0 < t₂) (hdp : 0 < dp₂)
    (hclear : x32 * dp₂ + x33 * dp₃ = q3' * dp₃) :
    t₂ * (x22 * dp₂ + x23 * dp₃) - t₂ * (x22 * dp₂) = t₂ * x32 ^ 2 * dp₂ / (q3' - x33) ∧
      0 ≤ t₂ * (x22 * dp₂ + x23 * dp₃) - t₂ * (x22 * dp₂) := by
  obtain ⟨h, -, -⟩ := exercise_10_G_5a hx33 hq hclear hdp
  have hden : 0 < q3' - x33 := by linarith
  have e : t₂ * (x22 * dp₂ + x23 * dp₃) - t₂ * (x22 * dp₂) = t₂ * x32 ^ 2 * dp₂ / (q3' - x33) := by
    rw [hsym, h]; field_simp; ring
  exact ⟨e, by rw [e]; positivity⟩

/-! ## Footnote 32: backward-bending demand -/

/-- **Footnote 32** (MWG, p. 343). With Leontief preferences `min(m, x)` on `ℝ²₊`, the demand
at price `p > 0` and wealth `w ≥ 0` is `m = x = w/(1 + p)` (good `ℓ` is normal). If the consumer
owns `e` units of good `ℓ` and `m₀ < e` of the numeraire, her wealth is `m₀ + pe` and her demand
`(m₀ + pe)/(1 + p)` is strictly increasing in the price `p`. -/
theorem footnote_10_G_32 {p w : ℝ} (hp : 0 < p) :
    (∀ m x : ℝ, 0 ≤ m → 0 ≤ x → m + p * x ≤ w → min m x ≤ min (w / (1 + p)) (w / (1 + p))) ∧
    (w / (1 + p) + p * (w / (1 + p)) = w) := by
  have h1 : 0 < 1 + p := by linarith
  refine ⟨fun m x hm hx hb => ?_, by field_simp⟩
  rw [min_self, le_div_iff₀ h1]
  have := min_le_left m x
  have := min_le_right m x
  nlinarith [min_le_left m x, min_le_right m x]

/-- **Footnote 32** (MWG, p. 343): the demand `(m₀ + pe)/(1 + p)` has derivative
`(e - m₀)/(1 + p)² > 0` when `e > m₀`. -/
theorem footnote_10_G_32_increasing {m₀ e p : ℝ} (hp : 0 < p) (he : m₀ < e) :
    HasDerivAt (fun p => (m₀ + p * e) / (1 + p)) ((e - m₀) / (1 + p) ^ 2) p ∧
      0 < (e - m₀) / (1 + p) ^ 2 := by
  have h1 : (1 + p) ≠ 0 := by linarith
  refine ⟨?_, by have : 0 < e - m₀ := by linarith
                 positivity⟩
  have h := (((hasDerivAt_id p).mul_const e).const_add m₀).div ((hasDerivAt_id p).const_add 1) h1
  exact h.congr_deriv (by simp only [id]; field_simp; ring)

end MWG.CompetitiveMarkets
