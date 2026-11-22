/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPositiveEquilibriumTheory.ExistenceGeneral

/-!
# Exercises 17.BB.1-17.BB.3 (MWG, pp. 649-650)

* **Exercise 17.BB.1** (`exercise_17_BB_1`): an economy with `L = 2` satisfying (i)
  `Yⱼ = -ℝ²₊`, (ii) `Xᵢ` nonempty, closed, convex, `Xᵢ + ℝ²₊ ⊆ Xᵢ`, (iii) continuous, convex,
  strongly monotone preferences, (iv) `ωᵢ ∈ Xᵢ` (`ex17BB1_hyp`), with a Walrasian
  quasiequilibrium at `p = (1, 1) ≫ 0` that is not a Walrasian equilibrium. Consumer 0 has
  `X₀ = {x ≥ 0 : x₁ + x₂ ≥ 1}` and `ω₀ = (1, 0)` on its lower boundary, so the only `x̂₀ ∈ X₀`
  with `x̂₀ ≤ ω₀` is `ω₀` itself: neither situation (a) nor (b) of the small type after
  Proposition 17.BB.1 applies, and the cheaper consumption condition fails
  (`exercise_17_BB_1_why`). No contradiction.
* **Exercise 17.BB.2** (`exercise_17_BB_2`): in a pure exchange economy on `ℝ^L₊` where each
  consumer desires only the goods of a set `Dᵢ` (strongly monotone in them,
  `PrefStronglyMonotoneIn`), `ωᵢ ≥ 0`, `∑ᵢ ωᵢ ≫ 0`, and the economy is indecomposable
  (`Indecomposable`), every Walrasian quasiequilibrium is an equilibrium. Instance:
  `ex17BB2_instance` (two consumers each desiring the other's good).
* **Exercise 17.BB.3**, second claim (`exercise_17_BB_3_not_both_negative`): with `Xᵢ = ℝ^L₊`
  and rational, continuous, locally nonsatiated preferences, no consumer has a demand at a
  price vector `p ≪ 0` (whatever his wealth): the upper contour set of a demanded bundle would
  be compact, so `≿ᵢ` would have a global maximum. Hence at an equilibrium the prices cannot
  all be negative (`exercise_17_BB_3_eqm`).
-/

namespace MWG.PositiveEquilibriumTheory

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.Production MWG.WelfareTheorems
open Kreps.PreferenceProperties
open MWG.CompetitiveMarkets (Allocation)
open Filter Topology

/-! ### Exercise 17.BB.1 -/

/-- Consumer 0's consumption set `X₀ = {x ∈ ℝ²₊ : x₁ + x₂ ≥ 1}`. -/
def ex17BB1X0 : Set (Fin 2 → ℝ) := {x | 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ 1 ≤ x 0 + x 1}

/-- The utility `u(x) = x₁ + 2x₂` of both consumers. -/
def ex17BB1u (x : Fin 2 → ℝ) : ℝ := x 0 + 2 * x 1

/-- **Exercise 17.BB.1** (MWG, pp. 649-650). The economy: `X₀ = ex17BB1X0`, `X₁ = ℝ²₊`,
`u₀ = u₁ = x₁ + 2x₂`, `Y = -ℝ²₊`, `ω₀ = (1, 0)`, `ω₁ = (0, 1)`. -/
noncomputable def ex17BB1Economy : PrivPrefEconomy (Fin 2) Unit 2 where
  X := fun i => if i = 0 then ex17BB1X0 else nonnegOrthant 2
  pref := fun _ => utilityPref ex17BB1u
  Y := fun _ => nonposOrthant 2
  ωi := fun i => if i = 0 then ![1, 0] else ![0, 1]
  θ := fun _ _ => 1 / 2

/-- The allocation `x₀ = (1, 0)`, `x₁ = (0, 1)`, `y = 0` (no trade). -/
def ex17BB1Alloc : Allocation (Fin 2) Unit 2 :=
  ⟨fun i => if i = 0 then ![1, 0] else ![0, 1], fun _ => 0⟩

/-- Membership in `X₀`. -/
theorem ex17BB1_X0 (x : Fin 2 → ℝ) : x ∈ ex17BB1Economy.X 0 ↔ x ∈ ex17BB1X0 := by
  simp [ex17BB1Economy]

/-- Membership in `X₁`. -/
theorem ex17BB1_X1 (x : Fin 2 → ℝ) : x ∈ ex17BB1Economy.X 1 ↔ x ∈ nonnegOrthant 2 := by
  simp [ex17BB1Economy]

/-- The economy of Exercise 17.BB.1 satisfies (i)-(iv). -/
theorem ex17BB1_hyp : (∀ j, ex17BB1Economy.Y j = nonposOrthant 2) ∧
    (∀ i, (ex17BB1Economy.X i).Nonempty ∧ IsClosed (ex17BB1Economy.X i) ∧
      Convex ℝ (ex17BB1Economy.X i) ∧
      ∀ x ∈ ex17BB1Economy.X i, ∀ v : Fin 2 → ℝ, 0 ≤ v → x + v ∈ ex17BB1Economy.X i) ∧
    (∀ i, PrefContinuous (ex17BB1Economy.X i) (ex17BB1Economy.pref i) ∧
      PrefConvex (ex17BB1Economy.X i) (ex17BB1Economy.pref i) ∧
      PrefStronglyMonotone (ex17BB1Economy.X i) (ex17BB1Economy.pref i)) ∧
    ∀ i, ex17BB1Economy.ωi i ∈ ex17BB1Economy.X i := by
  have hX0c : IsClosed ex17BB1X0 :=
    (isClosed_le continuous_const (continuous_apply 0)).inter
      ((isClosed_le continuous_const (continuous_apply 1)).inter
        (isClosed_le continuous_const ((continuous_apply 0).add (continuous_apply 1))))
  have hX0v : Convex ℝ ex17BB1X0 := by
    intro x hx y hy a b ha hb hab
    obtain ⟨h1, h2, h3⟩ := hx
    obtain ⟨k1, k2, k3⟩ := hy
    refine ⟨?_, ?_, ?_⟩ <;> simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    · nlinarith [mul_nonneg ha h1, mul_nonneg hb k1]
    · nlinarith [mul_nonneg ha h2, mul_nonneg hb k2]
    · nlinarith [mul_le_mul_of_nonneg_left h3 ha, mul_le_mul_of_nonneg_left k3 hb]
  have hXv : ∀ i, Convex ℝ (ex17BB1Economy.X i) := fun i => by
    fin_cases i
    · simpa [ex17BB1Economy] using hX0v
    · simpa [ex17BB1Economy] using convex_nonnegOrthant 2
  refine ⟨fun _ => rfl, fun i => ?_, fun i => ⟨prefContinuous_utilityPref
    (by unfold ex17BB1u; fun_prop : Continuous ex17BB1u).continuousOn, ?_, ?_⟩, fun i => ?_⟩
  · have c0 : (ex17BB1Economy.X 0).Nonempty ∧ IsClosed (ex17BB1Economy.X 0) ∧
        Convex ℝ (ex17BB1Economy.X 0) ∧
        ∀ x ∈ ex17BB1Economy.X 0, ∀ v : Fin 2 → ℝ, 0 ≤ v → x + v ∈ ex17BB1Economy.X 0 := by
      refine ⟨⟨![1, 0], by simp [ex17BB1Economy, ex17BB1X0]⟩,
        by simpa [ex17BB1Economy] using hX0c, hXv 0, fun x hx v hv => ?_⟩
      rw [ex17BB1_X0] at hx ⊢
      obtain ⟨h1, h2, h3⟩ := hx
      have e0 : 0 ≤ v 0 := hv 0
      have e1 : 0 ≤ v 1 := hv 1
      refine ⟨?_, ?_, ?_⟩ <;> simp only [Pi.add_apply] <;> linarith
    have c1 : (ex17BB1Economy.X 1).Nonempty ∧ IsClosed (ex17BB1Economy.X 1) ∧
        Convex ℝ (ex17BB1Economy.X 1) ∧
        ∀ x ∈ ex17BB1Economy.X 1, ∀ v : Fin 2 → ℝ, 0 ≤ v → x + v ∈ ex17BB1Economy.X 1 := by
      refine ⟨⟨0, by simp [ex17BB1Economy, nonnegOrthant]⟩,
        by simpa [ex17BB1Economy] using isClosed_nonnegOrthant, hXv 1, fun x hx v hv => ?_⟩
      rw [ex17BB1_X1] at hx ⊢
      exact fun l => add_nonneg (hx l) (hv l)
    fin_cases i
    · exact c0
    · exact c1
  · intro z _ x hx y hy a b ha hb hab
    refine ⟨hXv i hx.1 hy.1 ha hb hab, ?_⟩
    have h1 := hx.2
    have h2 := hy.2
    simp only [ex17BB1Economy, utilityPref, ex17BB1u, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul] at h1 h2 ⊢
    have e : a * (z 0 + 2 * z 1) + b * (z 0 + 2 * z 1) = z 0 + 2 * z 1 := by
      rw [← add_mul, hab, one_mul]
    nlinarith
  · intro x _ y _ hxy hne
    obtain ⟨l, hl⟩ : ∃ l, x l < y l := by
      by_contra h
      push Not at h
      exact hne (funext fun l => le_antisymm (h l) (hxy l))
    have h0 := hxy 0
    have h1 := hxy 1
    have hlt : ex17BB1u x < ex17BB1u y := by
      unfold ex17BB1u
      fin_cases l
      · simp at hl; linarith
      · simp at hl; linarith
    exact ⟨hlt.le, not_le.mpr hlt⟩
  · fin_cases i
    · simp [ex17BB1Economy, ex17BB1X0]
    · simp [ex17BB1Economy, nonnegOrthant]

/-- **Exercise 17.BB.1** (MWG, p. 649). The no-trade allocation with `p = (1, 1) ≫ 0` is a
Walrasian quasiequilibrium but not a Walrasian equilibrium: consumer 0 can afford `(0, 1)`,
which he strictly prefers to `(1, 0)`. -/
theorem exercise_17_BB_1 : IsWalrasQuasiEqm ex17BB1Economy ex17BB1Alloc (fun _ => 1) ∧
    (∀ l : Fin 2, (0 : ℝ) < (fun _ : Fin 2 => (1 : ℝ)) l) ∧
    ¬ ex17BB1Economy.IsWalrasEqm ex17BB1Alloc (fun _ => 1) := by
  have hw : ∀ i, ex17BB1Economy.wealth ex17BB1Alloc (fun _ => 1) i = 1 := fun i => by
    fin_cases i <;> simp [PrivPrefEconomy.wealth, ex17BB1Economy, ex17BB1Alloc, dotProduct,
      Fin.sum_univ_two]
  refine ⟨⟨fun h => by simpa using congrFun h 0, fun _ => ⟨fun _ => le_refl 0, fun y hy => ?_⟩,
    fun i => ?_, ?_⟩, fun _ => one_pos, ?_⟩
  · simp only [ex17BB1Alloc, dotProduct_zero]
    have := hy 0
    have := hy 1
    simp only [dotProduct, Fin.sum_univ_two, one_mul]
    linarith
  · rw [hw]
    have c0 : ex17BB1Alloc.x 0 ∈ ex17BB1Economy.X 0 ∧
        (fun _ => (1 : ℝ)) ⬝ᵥ ex17BB1Alloc.x 0 ≤ 1 ∧ ∀ x ∈ ex17BB1Economy.X 0,
          Strict (ex17BB1Economy.pref 0) x (ex17BB1Alloc.x 0) → 1 ≤ (fun _ => (1 : ℝ)) ⬝ᵥ x := by
      refine ⟨by simp [ex17BB1Economy, ex17BB1Alloc, ex17BB1X0], by
        simp [ex17BB1Alloc, dotProduct, Fin.sum_univ_two], fun x hx _ => ?_⟩
      rw [ex17BB1_X0] at hx
      simp only [dotProduct, Fin.sum_univ_two, one_mul]
      exact hx.2.2
    have c1 : ex17BB1Alloc.x 1 ∈ ex17BB1Economy.X 1 ∧
        (fun _ => (1 : ℝ)) ⬝ᵥ ex17BB1Alloc.x 1 ≤ 1 ∧ ∀ x ∈ ex17BB1Economy.X 1,
          Strict (ex17BB1Economy.pref 1) x (ex17BB1Alloc.x 1) → 1 ≤ (fun _ => (1 : ℝ)) ⬝ᵥ x := by
      refine ⟨by simp [ex17BB1Economy, ex17BB1Alloc, nonnegOrthant], by
        simp [ex17BB1Alloc, dotProduct, Fin.sum_univ_two], fun x hx hs => ?_⟩
      rw [ex17BB1_X1] at hx
      have h := hs.1
      simp only [ex17BB1Economy, utilityPref, ex17BB1u, ex17BB1Alloc] at h
      simp only [dotProduct, Fin.sum_univ_two, one_mul]
      norm_num at h
      linarith [hx 0]
    fin_cases i
    · exact c0
    · exact c1
  · funext l
    fin_cases l <;> simp [ex17BB1Economy, ex17BB1Alloc, Fin.sum_univ_two]
  · rintro ⟨-, hmax, -⟩
    have hb : (![0, 1] : Fin 2 → ℝ) ∈ budgetSetOn (ex17BB1Economy.X 0) (fun _ => 1)
        (ex17BB1Economy.wealth ex17BB1Alloc (fun _ => 1) 0) := by
      rw [hw]
      refine ⟨by simp [ex17BB1Economy, ex17BB1X0], by simp [dotProduct, Fin.sum_univ_two]⟩
    have := (hmax 0).2 _ hb
    simp [ex17BB1Economy, utilityPref, ex17BB1u, ex17BB1Alloc] at this

/-- **Exercise 17.BB.1** (MWG, p. 650), "why does this not contradict...": for consumer 0 the
only `x̂₀ ∈ X₀` with `x̂₀ ≤ ω₀` is `ω₀` (so neither `ω₀ ≫ x̂₀`, situation (a), nor
`ω₀ ≠ x̂₀`, situation (b), is available), and the cheaper consumption condition fails. -/
theorem exercise_17_BB_1_why :
    (∀ x ∈ ex17BB1Economy.X 0, x ≤ ex17BB1Economy.ωi 0 → x = ex17BB1Economy.ωi 0) ∧
    ¬ CheaperConsumption ex17BB1Economy ex17BB1Alloc (fun _ => 1) 0 := by
  constructor
  · intro x hx hle
    rw [ex17BB1_X0] at hx
    obtain ⟨h1, h2, h3⟩ := hx
    have k0 := hle 0
    have k1 := hle 1
    simp [ex17BB1Economy] at k0 k1
    funext l
    fin_cases l
    · simp [ex17BB1Economy]; linarith
    · simp [ex17BB1Economy]; linarith
  · rintro ⟨x, hx, hlt⟩
    rw [ex17BB1_X0] at hx
    have hw : ex17BB1Economy.wealth ex17BB1Alloc (fun _ => 1) 0 = 1 := by
      simp [PrivPrefEconomy.wealth, ex17BB1Economy, ex17BB1Alloc, dotProduct, Fin.sum_univ_two]
    rw [hw] at hlt
    simp only [dotProduct, Fin.sum_univ_two, one_mul] at hlt
    linarith [hx.2.2]

/-! ### Exercise 17.BB.2 -/

/-- **Exercise 17.BB.2** (MWG, p. 650). The consumer desires only the goods in `D` and is
strongly monotone in them on `ℝ^L₊`: if `y ≥ x` on `D` with a strict inequality for some good
of `D`, then `y ≻ x` (whatever the other coordinates). -/
def PrefStronglyMonotoneIn {L : ℕ} (D : Set (Fin L)) (r : (Fin L → ℝ) → (Fin L → ℝ) → Prop) :
    Prop :=
  ∀ x ∈ nonnegOrthant L, ∀ y ∈ nonnegOrthant L, (∀ l ∈ D, x l ≤ y l) → (∃ l ∈ D, x l < y l) →
    Strict r y x

/-- **Exercise 17.BB.2** (MWG, p. 650). Indecomposability: consumers cannot be divided into two
nonempty groups such that the consumers of one group desire none of the commodities owned by
the other group (for every split `G`, `Gᶜ`, some `i ∈ G` desires a good some `k ∉ G` owns;
quantifying over all `G` covers both groups). -/
def Indecomposable {ι : Type*} {L : ℕ} (D : ι → Set (Fin L)) (ω : ι → Fin L → ℝ) : Prop :=
  ∀ G : Set ι, (∃ i, i ∈ G) → (∃ k, k ∉ G) → ∃ i ∈ G, ∃ k, k ∉ G ∧ ∃ l ∈ D i, 0 < ω k l

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {L : ℕ}

/-- **Exercise 17.BB.2** (MWG, p. 650). In a pure exchange economy (`Xᵢ = ℝ^L₊`, every firm the
free disposal technology, at least one firm) with rational continuous preferences, each
strongly monotone in its desired goods `Dᵢ`, endowments `ωᵢ ≥ 0` with `∑ᵢ ωᵢ ≫ 0`, and
indecomposability, every Walrasian quasiequilibrium is a Walrasian equilibrium. -/
theorem exercise_17_BB_2 [Nonempty κ] {E : PrivPrefEconomy ι κ L}
    (hX : ∀ i, E.X i = nonnegOrthant L) (hY : ∀ j, E.Y j = nonposOrthant L)
    (hr : ∀ i, RationalOn (E.X i) (E.pref i)) (hc : ∀ i, PrefContinuous (E.X i) (E.pref i))
    {D : ι → Set (Fin L)} (hmono : ∀ i, PrefStronglyMonotoneIn (D i) (E.pref i))
    (hω : ∀ i, 0 ≤ E.ωi i) (hωpos : ∀ l, 0 < (∑ i, E.ωi i) l) (hind : Indecomposable D E.ωi)
    {a : Allocation ι κ L} {p : Fin L → ℝ} (hq : IsWalrasQuasiEqm E a p) :
    E.IsWalrasEqm a p := by
  have hXc : ∀ i, Convex ℝ (E.X i) := fun i => (hX i) ▸ convex_nonnegOrthant L
  obtain ⟨j₀⟩ := (inferInstance : Nonempty κ)
  have hp : ∀ l, 0 ≤ p l := footnote_9 ((hY j₀) ▸ hq.2.1 j₀)
  -- profits vanish, so wealth is `p·ωᵢ`
  have hprof : ∀ j, p ⬝ᵥ a.y j = 0 := fun j => by
    have hy := hq.2.1 j
    rw [hY j] at hy
    refine le_antisymm ?_ (by simpa using hy.2 0 fun _ => le_refl 0)
    exact Finset.sum_nonpos fun l _ => mul_nonpos_of_nonneg_of_nonpos (hp l) (hy.1 l)
  have hw : ∀ i, E.wealth a p i = p ⬝ᵥ E.ωi i := fun i => by
    simp [PrivPrefEconomy.wealth, hprof]
  -- consumers with positive wealth maximize, and price every good they desire positively
  have hcheap : ∀ i, 0 < p ⬝ᵥ E.ωi i → CheaperConsumption E a p i := fun i hi =>
    ⟨0, (hX i) ▸ fun _ => le_refl 0, by rw [hw]; simpa using hi⟩
  have hdes : ∀ i, 0 < p ⬝ᵥ E.ωi i → ∀ l ∈ D i, 0 < p l := by
    intro i hi l hl
    have hmax := proposition_17_BB_1 hq (hXc i) (hr i) (hc i) (hcheap i hi)
    by_contra hpl
    have hpl0 : p l = 0 := le_antisymm (not_lt.mp hpl) (hp l)
    have hxX : a.x i ∈ nonnegOrthant L := (hX i) ▸ hmax.1.1
    have hmem : a.x i + Pi.single l 1 ∈ nonnegOrthant L := fun k => by
      by_cases hk : k = l
      · subst hk
        simp only [Pi.add_apply, Pi.single_eq_same]
        linarith [hxX k]
      · simp only [Pi.add_apply, Pi.single_eq_of_ne hk, add_zero]
        exact hxX k
    have hs := hmono i _ hxX _ hmem (fun k _ => by
      by_cases hk : k = l
      · subst hk; simp
      · simp [hk]) ⟨l, hl, by simp⟩
    have hb : a.x i + Pi.single l 1 ∈ budgetSetOn (E.X i) p (E.wealth a p i) := by
      refine ⟨(hX i) ▸ hmem, ?_⟩
      rw [dotProduct_add, dotProduct_single, hpl0, zero_mul, add_zero]
      exact hmax.1.2
    exact hs.2 (hmax.2 _ hb)
  -- everybody has positive wealth, by indecomposability
  have hall : ∀ k, 0 < p ⬝ᵥ E.ωi k := by
    by_contra hcon
    push Not at hcon
    obtain ⟨k, hk⟩ := hcon
    have htot : 0 < ∑ i, p ⬝ᵥ E.ωi i := by
      rw [← dotProduct_finset_sum]
      exact dotProduct_pos_of_nonneg_ne_zero hp hq.1 hωpos
    obtain ⟨i, -, hi⟩ := Finset.exists_lt_of_sum_lt (s := Finset.univ)
      (f := fun _ : ι => (0 : ℝ)) (g := fun i => p ⬝ᵥ E.ωi i) (by simpa using htot)
    obtain ⟨i', hi'G, k', hk'G, l, hl, hωl⟩ :=
      hind {i | 0 < p ⬝ᵥ E.ωi i} ⟨i, hi⟩ ⟨k, not_lt.mpr hk⟩
    have hpl := hdes i' hi'G l hl
    have : p l * E.ωi k' l ≤ p ⬝ᵥ E.ωi k' :=
      Finset.single_le_sum (f := fun m => p m * E.ωi k' m)
        (fun m _ => mul_nonneg (hp m) (hω k' m)) (Finset.mem_univ l)
    exact hk'G (lt_of_lt_of_le (mul_pos hpl hωl) this)
  exact proposition_17_BB_1_eqm hq hXc hr hc fun i => hcheap i (hall i)

/-- **Exercise 17.BB.2**, instance: two consumers on `ℝ²₊`, consumer 0 desiring only good 1
(`u₀ = x₂`) and owning `ω₀ = (1, 0)`, consumer 1 desiring only good 0 (`u₁ = x₁`) and owning
`ω₁ = (0, 1)`, one disposal firm. -/
noncomputable def ex17BB2Economy : PrivPrefEconomy (Fin 2) Unit 2 where
  X := fun _ => nonnegOrthant 2
  pref := fun i => utilityPref (if i = 0 then fun x => x 1 else fun x => x 0)
  Y := fun _ => nonposOrthant 2
  ωi := fun i => if i = 0 then ![1, 0] else ![0, 1]
  θ := fun _ _ => 1 / 2

/-- The desired goods of the instance: `D₀ = {1}`, `D₁ = {0}`. -/
def ex17BB2D (i : Fin 2) : Set (Fin 2) := if i = 0 then {1} else {0}

/-- **Exercise 17.BB.2**, instance: the hypotheses hold (in particular the economy is
indecomposable), so every Walrasian quasiequilibrium of it is a Walrasian equilibrium. -/
theorem ex17BB2_instance {a : Allocation (Fin 2) Unit 2} {p : Fin 2 → ℝ}
    (hq : IsWalrasQuasiEqm ex17BB2Economy a p) : ex17BB2Economy.IsWalrasEqm a p := by
  refine exercise_17_BB_2 (D := ex17BB2D) (fun _ => rfl) (fun _ => rfl)
    (fun _ => rationalOn_utilityPref _ _) (fun i => ?_) (fun i => ?_) (fun i => ?_) ?_ ?_ hq
  · have h0 : PrefContinuous (ex17BB2Economy.X 0) (ex17BB2Economy.pref 0) :=
      prefContinuous_utilityPref (continuous_apply 1).continuousOn
    have h1 : PrefContinuous (ex17BB2Economy.X 1) (ex17BB2Economy.pref 1) :=
      prefContinuous_utilityPref (continuous_apply 0).continuousOn
    fin_cases i
    · exact h0
    · exact h1
  · have h0 : PrefStronglyMonotoneIn (ex17BB2D 0) (ex17BB2Economy.pref 0) := by
      rintro x - y - - ⟨l, hl, hlt⟩
      simp only [ex17BB2D, ↓reduceIte, Set.mem_singleton_iff] at hl
      subst hl
      exact ⟨hlt.le, not_le.mpr hlt⟩
    have h1 : PrefStronglyMonotoneIn (ex17BB2D 1) (ex17BB2Economy.pref 1) := by
      rintro x - y - - ⟨l, hl, hlt⟩
      simp only [ex17BB2D, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, ↓reduceIte,
        Set.mem_singleton_iff] at hl
      subst hl
      exact ⟨hlt.le, not_le.mpr hlt⟩
    fin_cases i
    · exact h0
    · exact h1
  · intro l
    fin_cases i <;> fin_cases l <;> simp [ex17BB2Economy]
  · intro l
    fin_cases l <;> simp [ex17BB2Economy, Fin.sum_univ_two]
  · rintro G ⟨i, hi⟩ ⟨k, hk⟩
    have hik : i ≠ k := fun h => hk (h ▸ hi)
    fin_cases i <;> fin_cases k
    · exact absurd rfl hik
    · exact ⟨0, hi, 1, hk, 1, by simp [ex17BB2D], by simp [ex17BB2Economy]⟩
    · exact ⟨1, hi, 0, hk, 0, by simp [ex17BB2D], by simp [ex17BB2Economy]⟩
    · exact absurd rfl hik

/-! ### Exercise 17.BB.3 -/

/-- **Exercise 17.BB.3** (MWG, p. 650), "the two prices cannot be negative", for any number of
goods: on `Xᵢ = ℝ^L₊` with rational, continuous, locally nonsatiated preferences, there is no
preference maximizing bundle in the budget set at prices `p ≪ 0`, whatever the wealth `w`.
(Any `z ≿ x` must satisfy `p·z ≥ w`, otherwise local nonsatiation contradicts maximality, so
`{z ∈ ℝ^L₊ : z ≿ x}` lies in the box `0 ≤ z_ℓ ≤ w/p_ℓ`; a maximal element of `≿` on this
compact set would be a global maximum, contradicting local nonsatiation.) -/
theorem exercise_17_BB_3_not_both_negative {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hr : RationalOn (nonnegOrthant L) r) (hc : PrefContinuous (nonnegOrthant L) r)
    (hlns : LocallyNonsatiated (nonnegOrthant L) r) {p : Fin L → ℝ} (hp : ∀ l, p l < 0)
    (w : ℝ) : ¬ ∃ x, IsMaximalFor r (budgetSetOn (nonnegOrthant L) p w) x := by
  rintro ⟨x, ⟨hxX, -⟩, hmax⟩
  set U : Set (Fin L → ℝ) := {z | z ∈ nonnegOrthant L ∧ r z x} with hUdef
  have hU : ∀ z ∈ U, w ≤ p ⬝ᵥ z := by
    intro z hz
    by_contra hlt
    push Not at hlt
    obtain ⟨z', hz'X, hz'c, hz's, -⟩ := bb_lns_near hlns p hz.1 hlt one_pos
    exact (bb_strict_trans hr hz'X hz.1 hxX hz's hz.2).2 (hmax z' ⟨hz'X, hz'c.le⟩)
  have hUsub : U ⊆ Set.Icc 0 (fun l => w / p l) := by
    intro z hz
    refine ⟨fun l => hz.1 l, fun l => ?_⟩
    have hle : p ⬝ᵥ z ≤ p l * z l := by
      have := Finset.single_le_sum (f := fun k => -(p k * z k))
        (fun k _ => by nlinarith [hp k, hz.1 k]) (Finset.mem_univ l)
      simp only [Finset.sum_neg_distrib] at this
      change -(p l * z l) ≤ -(∑ k, p k * z k) at this
      simp only [dotProduct]
      linarith
    change z l ≤ w / p l
    rw [le_div_iff_of_neg (hp l)]
    linarith [hU z hz]
  have hUcl : IsClosed U := by
    refine IsSeqClosed.isClosed fun {zs} {z} hzs hlim => ?_
    have hzX : z ∈ nonnegOrthant L := isClosed_nonnegOrthant.mem_of_tendsto hlim
      (Eventually.of_forall fun n => (hzs n).1)
    exact ⟨hzX, hc zs (fun _ => x) z x (fun n => (hzs n).1) (fun _ => hxX) hzX hxX
      (fun n => (hzs n).2) hlim tendsto_const_nhds⟩
  obtain ⟨m, hmU, hm⟩ := bb_exists_maximal hr hc (isCompact_Icc.of_isClosed_subset hUcl hUsub)
    (fun z hz => hz.1) ⟨x, hxX, bb_refl hr hxX⟩
  obtain ⟨z, hzX, -, hzs⟩ := hlns m hmU.1 1 one_pos
  exact hzs.2 (hm z ⟨hzX, hr.2 _ hzX _ hmU.1 _ hxX hzs.1 hmU.2⟩)

/-- **Exercise 17.BB.3** (MWG, p. 650). In an economy (at least one consumer) whose consumers
have `Xᵢ = ℝ^L₊` and rational, continuous, locally nonsatiated preferences, the prices of a
Walrasian equilibrium cannot all be negative. -/
theorem exercise_17_BB_3_eqm [Nonempty ι] {E : PrivPrefEconomy ι κ L}
    (hX : ∀ i, E.X i = nonnegOrthant L) (hr : ∀ i, RationalOn (E.X i) (E.pref i))
    (hc : ∀ i, PrefContinuous (E.X i) (E.pref i))
    (hlns : ∀ i, LocallyNonsatiated (E.X i) (E.pref i)) {a : Allocation ι κ L}
    {p : Fin L → ℝ} (heq : E.IsWalrasEqm a p) : ¬ ∀ l, p l < 0 := by
  intro hp
  obtain ⟨i⟩ := (inferInstance : Nonempty ι)
  have h := heq.2.1 i
  have h1 := hr i
  have h2 := hc i
  have h3 := hlns i
  rw [hX i] at h1 h2 h3 h
  exact exercise_17_BB_3_not_both_negative h1 h2 h3 hp _ ⟨_, h⟩

end MWG.PositiveEquilibriumTheory
