/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPositiveEquilibriumTheory.Production

/-!
# Constant returns: linear activities, unit costs, and household production (MWG Section 17.B,
pp. 583-584; Exercises 17.B.5-17.B.6, p. 642)

* **Linear activities** (small type, p. 583): `Y = {y : y ≤ ∑ⱼ αⱼ aⱼ for some α ≥ 0}`
  (`linActTech`). With strongly monotone consumers, every equilibrium has `p ≫ 0`, `y = ∑ⱼ αⱼ aⱼ`
  and consumers on their demand functions (`linAct_eqm_structure`), and `(p, α)` is an
  equilibrium iff **(17.B.4)** `z(p) - ∑ⱼ αⱼ aⱼ = 0` and **(17.B.5)** `p·aⱼ ≤ 0`,
  `αⱼ (p·aⱼ) = 0` (`linAct_eqm_iff`). The remark that (17.B.5) can be written as the equations
  `αⱼ p·aⱼ + Max {0, p·aⱼ} = 0` is `complementarity_iff_max`.
* **Exercise 17.B.5**: single-output constant returns firms with differentiable unit cost
  functions `cⱼ(p)`. The equation system is (17.B.4)-(17.B.5) with activity vectors
  `aⱼ(p) = e_{o(j)} - ∇cⱼ(p)`; by Euler's formula `p·∇cⱼ(p) = cⱼ(p)` (`euler_unitCost`),
  (17.B.5) becomes `p_{o(j)} ≤ cⱼ(p)`, `αⱼ (p_{o(j)} - cⱼ(p)) = 0` (`exercise_17_B_5`).
* **Exercise 17.B.6** (Rader): with a convex cone technology `Y` freely available to consumers,
  an equilibrium of the two-stage exchange problem is a Walrasian equilibrium of the production
  economy (`exercise_17_B_6`).
-/

namespace MWG.PositiveEquilibriumTheory

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.GeneralEquilibriumExamples MWG.Production
open MWG.WelfareTheorems
open MWG.CompetitiveMarkets (Allocation)

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {L : ℕ}

/-! ### Linear activities -/

/-- **Section 17.B, small type** (MWG, p. 583). The linear activity technology with basic
activities `a₁, ..., a_J` and free disposal: `Y = {y : y ≤ ∑ⱼ αⱼ aⱼ for some α ≥ 0}`. -/
def linActTech (a : κ → Fin L → ℝ) : Set (Fin L → ℝ) :=
  {y | ∃ α : κ → ℝ, (∀ j, 0 ≤ α j) ∧ y ≤ ∑ j, α j • a j}

/-- The pure exchange economy `E` with one firm operating the linear activity technology, owned
by consumers in shares `θᵢ`. -/
def linActEconomy (E : ExchangeEconomy ι L) (a : κ → Fin L → ℝ) (θ : ι → ℝ) :
    PrivPrefEconomy ι Unit L where
  X := E.X
  pref := fun i => utilityPref (E.u i)
  Y := fun _ => linActTech a
  ωi := E.ω
  θ := fun i _ => θ i

/-- Every basic activity is in `Y`. -/
theorem activity_mem_linActTech (a : κ → Fin L → ℝ) (j : κ) :
    a j ∈ linActTech a := by
  classical
  refine ⟨Pi.single j 1, fun k => ?_, le_of_eq ?_⟩
  · by_cases h : k = j
    · subst h; simp
    · simp [h]
  · simp [Pi.single_apply]

/-- Values `p·(∑ⱼ αⱼ aⱼ) = ∑ⱼ αⱼ (p·aⱼ)`. -/
theorem dotProduct_activities (p : Fin L → ℝ) (α : κ → ℝ) (a : κ → Fin L → ℝ) :
    p ⬝ᵥ ∑ j, α j • a j = ∑ j, α j * (p ⬝ᵥ a j) := by
  simp [dotProduct_sum, dotProduct_smul]

/-- A nonnegative price vector values a smaller vector less. -/
theorem dotProduct_le_of_le {p y y' : Fin L → ℝ} (hp : ∀ l, 0 ≤ p l) (h : y ≤ y') :
    p ⬝ᵥ y ≤ p ⬝ᵥ y' :=
  Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (h l) (hp l)

/-- **Section 17.B** (MWG, p. 583). With constant returns, maximum profits are zero: a profit
maximizing `y` has `p·y = 0` (`0 ∈ Y` and `2y ∈ Y`). -/
theorem linAct_profit_zero {a : κ → Fin L → ℝ} {p y : Fin L → ℝ}
    (hy : y ∈ supply (linActTech a) p) : p ⬝ᵥ y = 0 := by
  obtain ⟨⟨α, hα, hle⟩, hmax⟩ := hy
  have h0 : p ⬝ᵥ (0 : Fin L → ℝ) ≤ p ⬝ᵥ y := hmax 0 ⟨0, fun _ => le_rfl, by simp⟩
  have h2 : p ⬝ᵥ ((2 : ℝ) • y) ≤ p ⬝ᵥ y := hmax _ ⟨fun j => 2 * α j,
    fun j => by linarith [hα j], fun l => by
      have := hle l
      simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply] at this ⊢
      rw [show ∑ j, (2 * α j) * a j l = 2 * ∑ j, α j * a j l by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring]
      linarith⟩
  rw [dotProduct_smul, smul_eq_mul] at h2
  simp at h0
  linarith

/-- **Section 17.B** (MWG, pp. 583-584). In a linear activity economy with strongly monotone
consumers (`Xᵢ = ℝ^L₊`, continuous, strictly convex, `ωᵢ ∈ ℝ^L₊`), every Walrasian equilibrium
`(x, y)` at `p` has `p ≫ 0`, `y = ∑ⱼ αⱼ aⱼ` for some `α ≥ 0`, and `xᵢ = xᵢ(p, p·ωᵢ)`. -/
theorem linAct_eqm_structure [Nonempty ι] {E : ExchangeEconomy ι L}
    (hX : ∀ i, E.X i = nonnegOrthant L) (hu : ∀ i, StandardUtility (E.u i))
    (a : κ → Fin L → ℝ) (θ : ι → ℝ) {p : Fin L → ℝ} {x : ι → Fin L → ℝ} {y : Fin L → ℝ}
    (h : (linActEconomy E a θ).IsWalrasEqm ⟨x, fun _ => y⟩ p) :
    p ∈ posOrthant L ∧ (∃ α : κ → ℝ, (∀ j, 0 ≤ α j) ∧ y = ∑ j, α j • a j) ∧
      ∀ i, x i = demandFn E i p := by
  obtain ⟨hy, hx, -⟩ := h
  have hpy := linAct_profit_zero (hy ())
  have hw : ∀ i, (linActEconomy E a θ).wealth ⟨x, fun _ => y⟩ p i = p ⬝ᵥ E.ω i := fun i => by
    simp [PrivPrefEconomy.wealth, linActEconomy, hpy]
  have hxd : ∀ i, x i ∈ E.demand i p := fun i => by
    have := hx i
    rw [hw i] at this
    exact this
  have hp : p ∈ posOrthant L := by
    intro l
    by_contra hl
    rw [not_lt] at hl
    let i : ι := Classical.arbitrary ι
    have hmem := hxd i
    simp only [ExchangeEconomy.demand, hX i] at hmem
    exact (Set.eq_empty_iff_forall_notMem.1 (walrasianDemand_eq_empty (hu i).2.2 hl _)) _ hmem
  obtain ⟨⟨α, hα, hle⟩, hmax⟩ := hy ()
  classical
  have hpa : ∀ j, p ⬝ᵥ a j ≤ 0 := fun j => by
    have := hmax _ (activity_mem_linActTech a j)
    simpa [linActEconomy, hpy] using this
  have hdiff : p ⬝ᵥ (∑ j, α j • a j - y) = 0 := by
    have h1 : p ⬝ᵥ (∑ j, α j • a j - y) ≤ 0 := by
      rw [dotProduct_sub, dotProduct_activities, hpy, sub_zero]
      exact Finset.sum_nonpos fun j _ => mul_nonpos_of_nonneg_of_nonpos (hα j) (hpa j)
    have h2 : 0 ≤ p ⬝ᵥ (∑ j, α j • a j - y) :=
      Finset.sum_nonneg fun l _ => mul_nonneg (hp l).le (by
        have := hle l
        simp only [Pi.sub_apply]
        linarith)
    linarith
  have hy' : ∑ j, α j • a j - y = 0 :=
    eq_zero_of_dotProduct_nonpos hp (fun l => by have := hle l; simp only [Pi.sub_apply]; linarith)
      hdiff.le
  refine ⟨hp, ⟨α, hα, (sub_eq_zero.1 hy').symm⟩, fun i => ?_⟩
  have hne : (E.demand i p).Nonempty := ⟨x i, hxd i⟩
  exact demand_subsingleton hX (hu i).2.1 p (hxd i) (demandFn_mem E hne)

/-- **(17.B.4)-(17.B.5)** (MWG, p. 583). In a linear activity economy with strongly monotone
consumers, `(p, α)` with `α ≥ 0` is an equilibrium (consumers at their demands `xᵢ(p, p·ωᵢ)`,
production `∑ⱼ αⱼ aⱼ`) iff `p ≫ 0`, `z(p) - ∑ⱼ αⱼ aⱼ = 0` (17.B.4), and `p·aⱼ ≤ 0`,
`αⱼ (p·aⱼ) = 0` for all `j` (17.B.5). -/
theorem linAct_eqm_iff [Nonempty ι] {E : ExchangeEconomy ι L}
    (hX : ∀ i, E.X i = nonnegOrthant L) (hu : ∀ i, StandardUtility (E.u i))
    (hω : ∀ i, E.ω i ∈ nonnegOrthant L) (a : κ → Fin L → ℝ) (θ : ι → ℝ) {α : κ → ℝ}
    (hα : ∀ j, 0 ≤ α j) (p : Fin L → ℝ) :
    (linActEconomy E a θ).IsWalrasEqm ⟨fun i => demandFn E i p, fun _ => ∑ j, α j • a j⟩ p ↔
      p ∈ posOrthant L ∧ excessDemand E p - ∑ j, α j • a j = 0 ∧
        ∀ j, p ⬝ᵥ a j ≤ 0 ∧ α j * (p ⬝ᵥ a j) = 0 := by
  classical
  constructor
  · intro h
    obtain ⟨hp, -, -⟩ := linAct_eqm_structure hX hu a θ h
    obtain ⟨hy, -, hc⟩ := h
    have hpy := linAct_profit_zero (hy ())
    have hpa : ∀ j, p ⬝ᵥ a j ≤ 0 := fun j => by
      have := (hy ()).2 _ (activity_mem_linActTech a j)
      simpa [linActEconomy, hpy] using this
    rw [dotProduct_activities] at hpy
    have hterms := (Finset.sum_eq_zero_iff_of_nonpos fun j _ =>
      mul_nonpos_of_nonneg_of_nonpos (hα j) (hpa j)).1 hpy
    refine ⟨hp, ?_, fun j => ⟨hpa j, hterms j (Finset.mem_univ j)⟩⟩
    rw [excessDemand_eq]
    simp only [linActEconomy, Finset.univ_unique, Finset.sum_singleton] at hc
    rw [hc, ExchangeEconomy.totalEndowment]
    abel
  · rintro ⟨hp, hz, hpa⟩
    have hval : p ⬝ᵥ ∑ j, α j • a j = 0 := by
      rw [dotProduct_activities]
      exact Finset.sum_eq_zero fun j _ => (hpa j).2
    have hw : ∀ i, (linActEconomy E a θ).wealth ⟨fun i => demandFn E i p,
        fun _ => ∑ j, α j • a j⟩ p i = p ⬝ᵥ E.ω i := fun i => by
      simp [PrivPrefEconomy.wealth, linActEconomy, hval]
    refine ⟨fun _ => ⟨⟨α, hα, le_rfl⟩, fun y' ⟨β, hβ, hle⟩ => ?_⟩, fun i => ?_, ?_⟩
    · rw [hval]
      calc p ⬝ᵥ y' ≤ p ⬝ᵥ ∑ j, β j • a j := dotProduct_le_of_le (fun l => (hp l).le) hle
        _ = ∑ j, β j * (p ⬝ᵥ a j) := dotProduct_activities p β a
        _ ≤ 0 := Finset.sum_nonpos fun j _ => mul_nonpos_of_nonneg_of_nonpos (hβ j) (hpa j).1
    · rw [hw i]
      exact demandFn_mem E (demand_nonempty hX (hu i).1 (hω i) hp)
    · rw [excessDemand_eq, ExchangeEconomy.totalEndowment, sub_sub, sub_eq_zero] at hz
      simp only [linActEconomy, Finset.univ_unique, Finset.sum_singleton]
      rw [hz]

/-- **Section 17.B, small type** (MWG, p. 583). For `αⱼ ≥ 0`, the complementarity conditions
"`p·aⱼ ≤ 0`, `αⱼ(p·aⱼ) = 0`" are the single equation `αⱼ p·aⱼ + Max {0, p·aⱼ} = 0`. -/
theorem complementarity_iff_max {α r : ℝ} (hα : 0 ≤ α) :
    (r ≤ 0 ∧ α * r = 0) ↔ α * r + max 0 r = 0 := by
  constructor
  · rintro ⟨hr, h⟩
    rw [h, max_eq_left hr, add_zero]
  · intro h
    rcases le_or_gt r 0 with hr | hr
    · rw [max_eq_left hr, add_zero] at h
      exact ⟨hr, h⟩
    · rw [max_eq_right hr.le] at h
      nlinarith

/-! ### Exercise 17.B.5: unit cost functions -/

/-- **Euler's formula** for a unit cost function: if `c` is homogeneous of degree one and
differentiable at `p` with derivative `D`, then `D p = c(p)`. -/
theorem euler_unitCost {c : (Fin L → ℝ) → ℝ} {p : Fin L → ℝ}
    (hhom : ∀ t : ℝ, 0 < t → c (t • p) = t * c p) {D : (Fin L → ℝ) →L[ℝ] ℝ}
    (hd : HasFDerivAt c D p) : D p = c p := by
  have hd1 : HasFDerivAt c D ((fun t : ℝ => t • p) 1) := by simpa using hd
  have hsm : HasDerivAt (fun t : ℝ => t • p) p 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).smul_const p
  have hcomp := hd1.comp_hasDerivAt 1 hsm
  have hlin : HasDerivAt (fun t : ℝ => t * c p) (c p) 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).mul_const (c p)
  have heq : (c ∘ fun t : ℝ => t • p) =ᶠ[nhds 1] fun t => t * c p := by
    filter_upwards [lt_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with t ht
    exact hhom t ht
  exact (hcomp.congr_of_eventuallyEq heq.symm).unique hlin

/-- The input requirement vector `∇c(p)`: the partial derivatives `D(eₗ)`. -/
def gradVec (D : (Fin L → ℝ) →L[ℝ] ℝ) : Fin L → ℝ := fun l => D (Pi.single l 1)

/-- `p·∇c(p) = D p`. -/
theorem dotProduct_gradVec (D : (Fin L → ℝ) →L[ℝ] ℝ) (p : Fin L → ℝ) :
    p ⬝ᵥ gradVec D = D p := by
  have hp : p = ∑ l, p l • Pi.single l (1 : ℝ) := by
    ext k
    simp [Pi.single_apply]
  conv_rhs => rw [hp]
  rw [map_sum]
  simp [dotProduct, gradVec, map_smul]

omit [Fintype κ] in
/-- **Exercise 17.B.5** (MWG, p. 642). Firm `j` produces good `o(j)` with constant returns and a
unit cost function `cⱼ`, homogeneous of degree one and differentiable at `p` with derivative
`Dⱼ`. Its activity vector at `p` is `aⱼ(p) = e_{o(j)} - ∇cⱼ(p)` (Shephard's lemma), and the
equilibrium system, like (17.B.4)-(17.B.5), is: `z(p) = ∑ⱼ αⱼ aⱼ(p)`, `p_{o(j)} ≤ cⱼ(p)`,
`αⱼ (p_{o(j)} - cⱼ(p)) = 0`. Precisely, by Euler's formula `p·aⱼ(p) = p_{o(j)} - cⱼ(p)`, so
(17.B.5) for the activities `aⱼ(p)` is the price-equals-unit-cost condition. -/
theorem exercise_17_B_5 (o : κ → Fin L) {c : κ → (Fin L → ℝ) → ℝ} {p : Fin L → ℝ}
    (hhom : ∀ j, ∀ t : ℝ, 0 < t → c j (t • p) = t * c j p)
    {D : κ → (Fin L → ℝ) →L[ℝ] ℝ} (hd : ∀ j, HasFDerivAt (c j) (D j) p) (α : κ → ℝ) (j : κ) :
    (p ⬝ᵥ (Pi.single (o j) 1 - gradVec (D j)) ≤ 0 ∧
        α j * (p ⬝ᵥ (Pi.single (o j) 1 - gradVec (D j))) = 0) ↔
      (p (o j) ≤ c j p ∧ α j * (p (o j) - c j p) = 0) := by
  have h : p ⬝ᵥ (Pi.single (o j) 1 - gradVec (D j)) = p (o j) - c j p := by
    rw [dotProduct_sub, dotProduct_gradVec, euler_unitCost (hhom j) (hd j), dotProduct_single,
      mul_one]
  rw [h, sub_nonpos]

/-! ### Exercise 17.B.6: household production (Rader) -/

/-- **Exercise 17.B.6** (MWG, p. 642). Consumer `i`'s two-stage problem at prices `p`: choose
`vᵢ` with `p·vᵢ ≤ p·ωᵢ` and `yᵢ ∈ Y` with `vᵢ + yᵢ ∈ ℝ^L₊`, to maximize `uᵢ(vᵢ + yᵢ)`. -/
def RaderOptimal (u : (Fin L → ℝ) → ℝ) (Y : Set (Fin L → ℝ)) (p ω v y : Fin L → ℝ) : Prop :=
  y ∈ Y ∧ v + y ∈ nonnegOrthant L ∧ p ⬝ᵥ v ≤ p ⬝ᵥ ω ∧
    ∀ v' y', y' ∈ Y → v' + y' ∈ nonnegOrthant L → p ⬝ᵥ v' ≤ p ⬝ᵥ ω → u (v' + y') ≤ u (v + y)

/-- A closed under addition and nonnegative scaling set containing `0` contains every finite sum
of its elements. -/
theorem cone_sum_mem {Y : Set (Fin L → ℝ)} (hY0 : (0 : Fin L → ℝ) ∈ Y)
    (hYadd : ∀ y ∈ Y, ∀ y' ∈ Y, y + y' ∈ Y) {y : ι → Fin L → ℝ} (hy : ∀ i, y i ∈ Y) :
    ∑ i, y i ∈ Y := by
  classical
  have : ∀ s : Finset ι, ∑ i ∈ s, y i ∈ Y := fun s => by
    induction s using Finset.induction_on with
    | empty => simpa using hY0
    | insert i s hi ih => rw [Finset.sum_insert hi]; exact hYadd _ (hy i) _ ih
  exact this Finset.univ

/-- **Exercise 17.B.6** (MWG, p. 642; Rader 1972). Let `Y` be a convex cone (`0 ∈ Y`, closed
under addition and nonnegative scaling) available to every consumer, and let consumers on
`ℝ^L₊` have locally nonsatiated preferences. If every consumer's choice `(vᵢ*, yᵢ*)` solves the
two-stage problem at `p` and `∑ᵢ vᵢ* = ∑ᵢ ωᵢ`, then `p`, the consumptions `xᵢ = vᵢ* + yᵢ*` and the
production `y = ∑ᵢ yᵢ*` form a Walrasian equilibrium of the production economy with technology
`Y` (for any shares). Interpretation (verbal): household production makes firms dispensable. -/
theorem exercise_17_B_6 [Nonempty ι] {u : ι → (Fin L → ℝ) → ℝ} (hlns : ∀ i, UtilityLNS (u i))
    {Y : Set (Fin L → ℝ)} (hY0 : (0 : Fin L → ℝ) ∈ Y)
    (hYadd : ∀ y ∈ Y, ∀ y' ∈ Y, y + y' ∈ Y) (hYsmul : ∀ y ∈ Y, ∀ t : ℝ, 0 ≤ t → t • y ∈ Y)
    {ω : ι → Fin L → ℝ} (θ : ι → ℝ) {p : Fin L → ℝ} {v yv : ι → Fin L → ℝ}
    (hopt : ∀ i, RaderOptimal (u i) Y p (ω i) (v i) (yv i)) (hclear : ∑ i, v i = ∑ i, ω i) :
    PrivPrefEconomy.IsWalrasEqm
      ({ X := fun _ => nonnegOrthant L, pref := fun i => utilityPref (u i), Y := fun _ => Y,
         ωi := ω, θ := fun i _ => θ i } : PrivPrefEconomy ι Unit L)
      ⟨fun i => v i + yv i, fun _ => ∑ i, yv i⟩ p := by
  -- no production plan is profitable
  have hnp : ∀ yh ∈ Y, p ⬝ᵥ yh ≤ 0 := by
    intro yh hyh
    by_contra hpos
    rw [not_le] at hpos
    let i : ι := Classical.arbitrary ι
    obtain ⟨hyi, hxi, hbi, hmax⟩ := hopt i
    obtain ⟨x'', hx''X, -, hx''⟩ := (hlns i) (v i + yv i) hxi 1 one_pos
    set d := x'' - (v i + yv i)
    set t := max 0 ((p ⬝ᵥ d) / (p ⬝ᵥ yh))
    have ht0 : 0 ≤ t := le_max_left _ _
    have htd : p ⬝ᵥ d ≤ t * (p ⬝ᵥ yh) := by
      have := le_max_right 0 ((p ⬝ᵥ d) / (p ⬝ᵥ yh))
      rw [div_le_iff₀ hpos] at this
      exact this
    have hy' : yv i + t • yh ∈ Y := hYadd _ hyi _ (hYsmul _ hyh t ht0)
    have hsum : x'' - (yv i + t • yh) + (yv i + t • yh) = x'' := by abel
    have hb' : p ⬝ᵥ (x'' - (yv i + t • yh)) ≤ p ⬝ᵥ ω i := by
      have hd : x'' - (yv i + t • yh) = v i + d - t • yh := by simp only [d]; abel
      rw [hd, dotProduct_sub, dotProduct_add, dotProduct_smul, smul_eq_mul]
      linarith
    have := hmax _ _ hy' (by rw [hsum]; exact hx''X) hb'
    rw [hsum] at this
    exact hx''.2 this
  -- every consumer's production plan makes zero profit
  have hzero : ∀ i, p ⬝ᵥ yv i = 0 := by
    intro i
    obtain ⟨hyi, hxi, hbi, hmax⟩ := hopt i
    refine le_antisymm (hnp _ hyi) (not_lt.1 fun hneg => ?_)
    obtain ⟨x'', hx''X, hx''b, hx''⟩ := (hlns i).exists_better p hxi
      (w := p ⬝ᵥ ω i) (by rw [dotProduct_add]; linarith)
    have := hmax x'' 0 hY0 (by simpa using hx''X) (by simpa using hx''b.le)
    simp only [add_zero] at this
    linarith
  have hYsum : ∑ i, yv i ∈ Y := cone_sum_mem hY0 hYadd fun i => (hopt i).1
  have hval : p ⬝ᵥ ∑ i, yv i = 0 := by
    rw [dotProduct_sum]
    exact Finset.sum_eq_zero fun i _ => hzero i
  refine ⟨fun _ => ⟨hYsum, fun y' hy' => by rw [hval]; exact hnp y' hy'⟩, fun i => ?_, ?_⟩
  · obtain ⟨hyi, hxi, hbi, hmax⟩ := hopt i
    have hw : p ⬝ᵥ ω i + ∑ j : Unit, θ i * (p ⬝ᵥ ∑ i, yv i) = p ⬝ᵥ ω i := by simp [hval]
    refine ⟨⟨hxi, ?_⟩, fun x' hx' => ?_⟩
    · simp only [PrivPrefEconomy.wealth]
      rw [hw, dotProduct_add, hzero i, add_zero]
      exact hbi
    · simp only [PrivPrefEconomy.wealth] at hx'
      rw [hw] at hx'
      have := hmax x' 0 hY0 (by simpa using hx'.1) hx'.2
      simpa [utilityPref] using this
  · simp only [Finset.univ_unique, Finset.sum_singleton]
    rw [Finset.sum_add_distrib, hclear]

end MWG.PositiveEquilibriumTheory
