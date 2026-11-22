/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGGeneralEquilibriumExamples.Welfare

/-!
# The one-consumer, one-producer economy (MWG Section 15.C, pp. 525-529)

Goods are leisure (good 1, index `0`) and a consumption good (good 2, index `1`). The consumer has
utility `u` on `ℝ²₊` and `L̄` units of time; the firm turns labor `z ≥ 0` into `f(z)` units of the
consumption good; the consumer owns the firm.

* (15.C.1): profit maximization (`RCEconomy.IsProfitMax`); (15.C.2): the consumer's problem with
  budget `p x₂ ≤ w(L̄ - x₁) + π` (`RCEconomy.IsConsumerOpt`); the Walrasian equilibrium
  (15.C.3)-(15.C.4) (`RCEconomy.IsWalrasEqm`).
* p. 527: the budget line is the firm's isoprofit line (`budgetLine_eq_isoprofit`).
* p. 528 (Figure 15.C.2, Figure 15.C.3(b)): **first welfare theorem**: every Walrasian equilibrium
  allocation maximizes utility over the feasible set, with no convexity assumption
  (`rc_first_welfare`); footnote 7: in a one-consumer economy Pareto optimality (Definition 10.B.2)
  is utility maximization over the feasible set (`pareto_one_consumer_iff`).
* p. 528: **second welfare theorem**: with a concave production function, differentiable at the
  optimum, and continuous, convex, strongly monotone preferences, the welfare optimum is a Walrasian
  equilibrium allocation at `w/p = f'(z*)` (`rc_second_welfare`; differentiability at the optimum is
  an assumption we add, see `docs/corrections.md`).
* Footnote 7: with convex, strongly monotone preferences and a strictly concave production
  function the optimal consumption vector is unique, hence so is the equilibrium allocation
  (`footnote_7_unique`).
-/

namespace MWG.GeneralEquilibriumExamples

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.CompetitiveMarkets Kreps.PreferenceProperties

/-- **Section 15.C** (MWG, p. 526). The one-consumer, one-producer (Robinson Crusoe) economy:
utility `u` over (leisure, consumption), time endowment `L̄`, production function `f`. -/
structure RCEconomy where
  /-- The consumer's utility over (leisure, consumption good). -/
  u : (Fin 2 → ℝ) → ℝ
  /-- The time endowment `L̄`. -/
  Lbar : ℝ
  /-- The production function `f(z)`. -/
  f : ℝ → ℝ

/-- **(15.C.1)** (MWG, p. 526). `z` maximizes the firm's profit `p f(z) - w z` over `z ≥ 0`. -/
def RCEconomy.IsProfitMax (E : RCEconomy) (p w z : ℝ) : Prop :=
  0 ≤ z ∧ ∀ z', 0 ≤ z' → p * E.f z' - w * z' ≤ p * E.f z - w * z

/-- **(15.C.2)** (MWG, p. 526). The consumer's budget set at prices `(p, w)` and profit income `π`:
`x ∈ ℝ²₊` with `p x₂ ≤ w(L̄ - x₁) + π`. -/
def RCEconomy.budget (E : RCEconomy) (p w π₀ : ℝ) : Set (Fin 2 → ℝ) :=
  {x | x ∈ nonnegOrthant 2 ∧ p * x 1 ≤ w * (E.Lbar - x 0) + π₀}

/-- **(15.C.2)** (MWG, p. 526). `x` solves the consumer's problem. -/
def RCEconomy.IsConsumerOpt (E : RCEconomy) (p w π₀ : ℝ) (x : Fin 2 → ℝ) : Prop :=
  x ∈ E.budget p w π₀ ∧ ∀ y ∈ E.budget p w π₀, E.u y ≤ E.u x

/-- **Section 15.C** (MWG, p. 527, (15.C.3)-(15.C.4)). A Walrasian equilibrium: prices `(p, w)`, the
firm's labor demand `z` (profit maximizing), the consumer's bundle `x` (utility maximizing with
profit income `π = p f(z) - w z`), and market clearing `x₂ = f(z)`, `z = L̄ - x₁`. -/
def RCEconomy.IsWalrasEqm (E : RCEconomy) (p w : ℝ) (x : Fin 2 → ℝ) (z : ℝ) : Prop :=
  E.IsProfitMax p w z ∧ E.IsConsumerOpt p w (p * E.f z - w * z) x ∧ x 1 = E.f z ∧
    z = E.Lbar - x 0

/-- **Section 15.C** (MWG, p. 528). The bundles feasible given the technology and the endowment:
`x ∈ ℝ²₊`, `x₁ ≤ L̄`, `x₂ ≤ f(L̄ - x₁)`. -/
def RCEconomy.feasible (E : RCEconomy) : Set (Fin 2 → ℝ) :=
  {x | x ∈ nonnegOrthant 2 ∧ x 0 ≤ E.Lbar ∧ x 1 ≤ E.f (E.Lbar - x 0)}

/-- **Section 15.C** (MWG, p. 528 and footnote 7). `x` maximizes the consumer's utility subject to
the technological and endowment constraints (the planner's problem). -/
def RCEconomy.IsOptimal (E : RCEconomy) (x : Fin 2 → ℝ) : Prop :=
  x ∈ E.feasible ∧ ∀ y ∈ E.feasible, E.u y ≤ E.u x

/-- **Section 15.C** (MWG, p. 527). The consumer's budget line is the firm's isoprofit line: with
`z = L̄ - x₁` and `q = x₂`, `p x₂ = w(L̄ - x₁) + π` if and only if `p q - w z = π`. -/
theorem budgetLine_eq_isoprofit (E : RCEconomy) (p w π₀ : ℝ) (x : Fin 2 → ℝ) :
    p * x 1 = w * (E.Lbar - x 0) + π₀ ↔ p * x 1 - w * (E.Lbar - x 0) = π₀ := by
  constructor <;> intro h <;> linarith

/-- **Section 15.C** (MWG, p. 527). The budget line cuts the consumption axis at `π/p` (when the
consumer consumes all his time as leisure) and has slope `-w/p`. -/
theorem budgetLine_intercept_slope (E : RCEconomy) {p : ℝ} (hp : p ≠ 0) (w π₀ x₁ : ℝ) :
    (w * (E.Lbar - E.Lbar) + π₀) / p = π₀ / p ∧
      (w * (E.Lbar - (x₁ + 1)) + π₀) / p - (w * (E.Lbar - x₁) + π₀) / p = -(w / p) := by
  constructor
  · simp
  · field_simp
    ring

/-- **First welfare theorem in the one-consumer economy** (MWG, p. 528, Figure 15.C.2 and
Figure 15.C.3(b)). If `(p, w)` with `p ≥ 0` is a Walrasian equilibrium with allocation `(x, z)`,
then `x` maximizes utility over the feasible set; no convexity of the technology is needed. -/
theorem rc_first_welfare {E : RCEconomy} {p w : ℝ} {x : Fin 2 → ℝ} {z : ℝ}
    (h : E.IsWalrasEqm p w x z) (hp : 0 ≤ p) : E.IsOptimal x := by
  obtain ⟨hz, hx, h1, h2⟩ := h
  refine ⟨⟨hx.1.1, by linarith [hz.1], by rw [h1, ← h2]⟩, fun y hy => ?_⟩
  refine hx.2 y ⟨hy.1, ?_⟩
  -- a feasible bundle is affordable: its cost is the profit of the plan producing it
  have hz' : 0 ≤ E.Lbar - y 0 := by linarith [hy.2.1]
  have hprof := hz.2 _ hz'
  have : p * y 1 ≤ p * E.f (E.Lbar - y 0) := mul_le_mul_of_nonneg_left hy.2.2 hp
  linarith

/-- In a Walrasian equilibrium of the one-consumer economy with strongly monotone preferences the
price of the consumption good is positive (otherwise more of it is free). -/
theorem rc_eqm_price_pos {E : RCEconomy} (hmono : UtilityStronglyMonotone E.u) {p w : ℝ}
    {x : Fin 2 → ℝ} {z : ℝ} (h : E.IsWalrasEqm p w x z) : 0 < p := by
  by_contra hp
  rw [not_lt] at hp
  obtain ⟨-, hx, -, -⟩ := h
  have hmem : x + Pi.single 1 1 ∈ E.budget p w (p * E.f z - w * z) := by
    refine ⟨fun l => ?_, ?_⟩
    · fin_cases l
      · simpa using hx.1.1 0
      · simp; linarith [hx.1.1 1]
    · have := hx.1.2
      simp only [Pi.add_apply, Pi.single_eq_same]
      simp only [ne_eq, zero_ne_one, not_false_eq_true, Pi.single_eq_of_ne, add_zero]
      nlinarith
  have h1 := hx.2 _ hmem
  have h2 := hmono.lt hx.1.1 (y := x + Pi.single 1 1) (fun l => by
    fin_cases l <;> simp) (fun he => by simpa using congrFun he 1)
  linarith

/-- **Footnote 7** (MWG, p. 528). In a one-consumer economy (Chapter 10's `Economy` with a single
consumer), an allocation is Pareto optimal (Definition 10.B.2) if and only if it is feasible and
maximizes the consumer's utility among feasible allocations. -/
theorem pareto_one_consumer_iff {ι κ : Type*} [Fintype ι] [Unique ι] [Fintype κ] {L : ℕ}
    (E : Economy ι κ L) (a : Allocation ι κ L) :
    E.IsParetoOptimal a ↔ E.IsFeasible a ∧ ∀ a', E.IsFeasible a' →
      E.u default (a'.x default) ≤ E.u default (a.x default) := by
  rw [definition_10_B_2]
  constructor
  · rintro ⟨ha, h⟩
    refine ⟨ha, fun a' ha' => ?_⟩
    by_contra hlt
    rw [not_le] at hlt
    have := h a' ha' (fun i => by rw [Unique.eq_default i]; exact hlt.le) default
    linarith
  · rintro ⟨ha, h⟩
    refine ⟨ha, fun a' ha' _ i => ?_⟩
    rw [Unique.eq_default i]
    exact h a' ha'

/-- **Second welfare theorem in the one-consumer economy** (MWG, p. 528, Figure 15.C.2). Suppose
`u` is continuous, quasiconcave (convex preferences) and strongly monotone on `ℝ²₊`, `f` is concave
and strictly increasing on `[0, ∞)` and differentiable at `z* = L̄ - x*₁ > 0`, and `x*` maximizes
utility over the feasible set. Then `x*` with `z*` is a Walrasian equilibrium at `p = 1`,
`w = f'(z*) > 0`. -/
theorem rc_second_welfare {E : RCEconomy} (hcont : ContinuousOn E.u (nonnegOrthant 2))
    (hconv : PrefConvex (nonnegOrthant 2) (utilityPref E.u))
    (hmono : UtilityStronglyMonotone E.u) (hfc : ConcaveOn ℝ (Set.Ici 0) E.f)
    (hfm : StrictMonoOn E.f (Set.Ici 0)) {x : Fin 2 → ℝ} (hopt : E.IsOptimal x)
    (hz : 0 < E.Lbar - x 0) {f' : ℝ} (hf' : HasDerivAt E.f f' (E.Lbar - x 0)) :
    0 < f' ∧ E.IsWalrasEqm 1 f' x (E.Lbar - x 0) := by
  set zs := E.Lbar - x 0 with hzs
  have hx := hopt.1
  have hxm : x ∈ nonnegOrthant 2 := hx.1
  have hzs0 : zs ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.2 hz.le
  have htan : ∀ z, 0 ≤ z → E.f z ≤ E.f zs + f' * (z - zs) := fun z hz0 =>
    concave_le_tangent hfc hzs0 (Set.mem_Ici.2 hz0) hf'
  -- `f' > 0`
  have hf'pos : 0 < f' := by
    have h1 := hfm hzs0 (Set.mem_Ici.2 (by linarith : (0 : ℝ) ≤ zs + 1)) (by linarith)
    have h2 := htan (zs + 1) (by linarith)
    linarith
  -- the optimum lies on the frontier: `x₂ = f(z*)`
  have hx1 : x 1 = E.f zs := by
    by_contra hne
    have hlt : x 1 < E.f zs := lt_of_le_of_ne hx.2.2 hne
    set y : Fin 2 → ℝ := x + Pi.single 1 (E.f zs - x 1) with hy
    have hyx : x ≤ y := fun l => by
      fin_cases l <;> simp [hy] ; linarith
    have hyf : y ∈ E.feasible := by
      refine ⟨fun l => (hxm l).trans (hyx l), by simpa [hy] using hx.2.1, ?_⟩
      simp [hy, hzs]
    have hne' : y ≠ x := fun he => by
      have := congrFun he 1
      simp [hy] at this
      linarith
    have := hopt.2 y hyf
    have := hmono.lt hxm hyx hne'
    linarith
  set π₀ := 1 * E.f zs - f' * zs with hπ
  -- the consumer's budget line passes through `x`
  have hxline : 1 * x 1 = f' * (E.Lbar - x 0) + π₀ := by rw [hπ, hx1]; ring
  refine ⟨hf'pos, ⟨hz.le, fun z hz0 => ?_⟩, ⟨⟨hxm, hxline.le⟩, fun y hy => ?_⟩, by
    rw [hx1], rfl⟩
  · have := htan z hz0
    linarith
  -- the consumer: a strictly better affordable bundle leads to a strictly better feasible one
  by_contra hlt
  rw [not_le] at hlt
  -- Step A: a strictly better bundle strictly inside the budget set
  obtain ⟨y', hy'm, hy'in, hy'u⟩ : ∃ y' ∈ nonnegOrthant 2,
      1 * y' 1 < f' * (E.Lbar - y' 0) + π₀ ∧ E.u x < E.u y' := by
    by_cases hin : 1 * y 1 < f' * (E.Lbar - y 0) + π₀
    · exact ⟨y, hy.1, hin, hlt⟩
    by_cases hy1 : 0 < y 1
    · set g : ℝ → Fin 2 → ℝ := fun t => y - (t * y 1) • Pi.single 1 1
      have hgc : Continuous g := by fun_prop
      have hgm : ∀ t ∈ Set.Icc (0 : ℝ) 1, g t ∈ nonnegOrthant 2 := by
        intro t ht l
        fin_cases l
        · simpa [g] using hy.1 0
        · simp [g]; nlinarith [ht.2, hy.1 1]
      obtain ⟨t, ht0, ht1, ht⟩ := exists_pos_continuous_lt hcont hgc hgm (by simpa [g] using hlt)
      refine ⟨g t, hgm t ⟨ht0.le, ht1⟩, ?_, ht⟩
      have hb := hy.2
      simp [g]
      nlinarith [mul_pos ht0 hy1]
    by_cases hy0 : 0 < y 0
    · set g : ℝ → Fin 2 → ℝ := fun t => y - (t * y 0) • Pi.single 0 1
      have hgc : Continuous g := by fun_prop
      have hgm : ∀ t ∈ Set.Icc (0 : ℝ) 1, g t ∈ nonnegOrthant 2 := by
        intro t ht l
        fin_cases l
        · simp [g]; nlinarith [ht.2, hy.1 0]
        · simpa [g] using hy.1 1
      obtain ⟨t, ht0, ht1, ht⟩ := exists_pos_continuous_lt hcont hgc hgm (by simpa [g] using hlt)
      refine ⟨g t, hgm t ⟨ht0.le, ht1⟩, ?_, ht⟩
      have hb := hy.2
      simp [g]
      rw [not_lt] at hin
      nlinarith [mul_pos (mul_pos ht0 hy0) hf'pos]
    · exfalso
      have hy00 : y = 0 := funext fun l => by
        fin_cases l
        · exact le_antisymm (not_lt.1 hy0) (hy.1 0)
        · exact le_antisymm (not_lt.1 hy1) (hy.1 1)
      have := hmono.le (x := 0) (y := x) (fun l => le_refl _) hxm
      rw [hy00] at hlt
      linarith
  -- Step B: move from `x` towards `y'`; nearby points are feasible and inside the frontier
  set c := f' * (E.Lbar - y' 0) + π₀ - 1 * y' 1 with hc
  have hc0 : 0 < c := by linarith
  set d := x 0 - y' 0 with hd
  have hline : HasDerivAt (fun t : ℝ => zs + t * d) d 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const d).const_add zs
  have hcomp : HasDerivAt (fun t : ℝ => E.f (zs + t * d)) (f' * d) 0 := by
    have := HasDerivAt.comp (0 : ℝ) (by simpa using hf') hline
    simpa [Function.comp_def] using this
  have hgap : HasDerivAt (fun t : ℝ => E.f (zs + t * d) - (E.f zs + f' * (t * d)) + t * c) c 0 := by
    have h1 := (hcomp.sub ((hasDerivAt_id (0 : ℝ)).mul_const d |>.const_mul f' |>.const_add
      (E.f zs))).add ((hasDerivAt_id (0 : ℝ)).mul_const c)
    convert h1 using 1
    · funext t; simp
    · ring
  have hev : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      t ≤ 1 ∧ 0 ≤ zs + t * d := by
    have h1 : ∀ᶠ t in nhds (0 : ℝ), t < 1 := gt_mem_nhds one_pos
    have h2 : ∀ᶠ t in nhds (0 : ℝ), 0 < zs + t * d := by
      have hc : Continuous fun t : ℝ => zs + t * d := by fun_prop
      exact hc.continuousAt.eventually (lt_mem_nhds (by simpa using hz))
    filter_upwards [nhdsWithin_le_nhds h1, nhdsWithin_le_nhds h2] with t ht1 ht2
    exact ⟨ht1.le, ht2.le⟩
  obtain ⟨t, ht0, ⟨ht1, htz⟩, hpos⟩ := exists_pos_deriv_pos hgap hc0 hev
  simp only [zero_mul, add_zero, mul_zero, sub_self] at hpos
  set xt : Fin 2 → ℝ := x + t • (y' - x) with hxt
  have hxtm : xt ∈ nonnegOrthant 2 := by
    have := convex_nonnegOrthant 2 hxm hy'm (by linarith : (0 : ℝ) ≤ 1 - t) ht0.le
      (by ring : 1 - t + t = 1)
    convert this using 1
    rw [hxt]
    funext l
    simp
    ring
  have hxtu : E.u x ≤ E.u xt := by
    have := quasiconcave_of_prefConvex hconv hxm hy'm (by linarith : (0 : ℝ) ≤ 1 - t) ht0.le
      (by ring : 1 - t + t = 1)
    have e : (1 - t) • x + t • y' = xt := by
      rw [hxt]; funext l; simp; ring
    rw [e, min_eq_left hy'u.le] at this
    exact this
  have hxt0 : E.Lbar - xt 0 = zs + t * d := by simp [hxt, hd, hzs]; ring
  have hxt1 : xt 1 < E.f (E.Lbar - xt 0) := by
    rw [hxt0]
    have : xt 1 = E.f zs + f' * (t * d) - t * c := by
      simp only [hxt, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hc, hd]
      have := hxline
      rw [hx1] at this ⊢
      nlinarith
    linarith
  set y'' : Fin 2 → ℝ := xt + Pi.single 1 (E.f (E.Lbar - xt 0) - xt 1) with hy''
  have hle : xt ≤ y'' := fun l => by
    fin_cases l <;> simp [hy''] ; linarith
  have hne : y'' ≠ xt := fun he => by
    have := congrFun he 1
    simp [hy''] at this
    linarith
  have hfeas : y'' ∈ E.feasible := by
    refine ⟨fun l => (hxtm l).trans (hle l), ?_, ?_⟩
    · simp [hy'']; linarith
    · simp [hy'']
  have h1 := hopt.2 y'' hfeas
  have h2 := hmono.lt hxtm hle hne
  linarith

/-- With strongly monotone preferences an optimum lies on the production frontier:
`x₂ = f(L̄ - x₁)`. -/
theorem rc_optimal_frontier {E : RCEconomy} (hmono : UtilityStronglyMonotone E.u)
    {x : Fin 2 → ℝ} (hopt : E.IsOptimal x) : x 1 = E.f (E.Lbar - x 0) := by
  have hx := hopt.1
  by_contra hne
  have hlt : x 1 < E.f (E.Lbar - x 0) := lt_of_le_of_ne hx.2.2 hne
  set y : Fin 2 → ℝ := x + Pi.single 1 (E.f (E.Lbar - x 0) - x 1) with hy
  have hyx : x ≤ y := fun l => by
    fin_cases l <;> simp [hy] ; linarith
  have hyf : y ∈ E.feasible := by
    refine ⟨fun l => (hx.1 l).trans (hyx l), by simpa [hy] using hx.2.1, ?_⟩
    simp [hy]
  have hne' : y ≠ x := fun he => by
    have := congrFun he 1
    simp [hy] at this
    linarith
  have := hopt.2 y hyf
  have := hmono.lt hx.1 hyx hne'
  linarith

/-- **Footnote 7** (MWG, p. 528). With convex, strongly monotone preferences and a strictly concave
production function there is a unique optimal consumption vector. -/
theorem footnote_7_unique {E : RCEconomy}
    (hconv : PrefConvex (nonnegOrthant 2) (utilityPref E.u))
    (hmono : UtilityStronglyMonotone E.u) (hfc : StrictConcaveOn ℝ (Set.Ici 0) E.f)
    {x y : Fin 2 → ℝ} (hx : E.IsOptimal x) (hy : E.IsOptimal y) : x = y := by
  by_contra hne
  have hxy : E.u x = E.u y := le_antisymm (hy.2 x hx.1) (hx.2 y hy.1)
  have hfx := rc_optimal_frontier hmono hx
  have hfy := rc_optimal_frontier hmono hy
  have h0 : x 0 ≠ y 0 := by
    intro h0
    apply hne
    funext l
    fin_cases l
    · exact h0
    · change x 1 = y 1
      rw [hfx, hfy, h0]
  set m : Fin 2 → ℝ := (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y with hm
  have hmm : m ∈ nonnegOrthant 2 :=
    convex_nonnegOrthant 2 hx.1.1 hy.1.1 (by norm_num) (by norm_num) (by norm_num)
  have hmu : E.u x ≤ E.u m := by
    have := quasiconcave_of_prefConvex hconv hx.1.1 hy.1.1 (a := 1 / 2) (b := 1 / 2)
      (by norm_num) (by norm_num) (by norm_num)
    rw [← hxy, min_self] at this
    exact this
  have hzx : E.Lbar - x 0 ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.2 (by linarith [hx.1.2.1])
  have hzy : E.Lbar - y 0 ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.2 (by linarith [hy.1.2.1])
  have hstrict := hfc.2 hzx hzy (fun h => h0 (by linarith)) (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have hm0 : E.Lbar - m 0 = (1 / 2 : ℝ) • (E.Lbar - x 0) + (1 / 2 : ℝ) • (E.Lbar - y 0) := by
    simp [hm]; ring
  have hm1 : m 1 = 1 / 2 * x 1 + 1 / 2 * y 1 := by simp [hm]
  have hlt : m 1 < E.f (E.Lbar - m 0) := by
    rw [hm0, hm1, hfx, hfy]
    simpa using hstrict
  have hmf : m ∈ E.feasible := ⟨hmm, by
    simp [hm]; linarith [hx.1.2.1, hy.1.2.1], hlt.le⟩
  have hmopt : E.IsOptimal m := ⟨hmf, fun z hz => (hx.2 z hz).trans hmu⟩
  have := rc_optimal_frontier hmono hmopt
  linarith

/-- **Exercise 15.C.1(a)** (MWG, p. 542). In the one-consumer, one-firm economy with strictly convex
(and, as throughout Section 15.C, strongly monotone) preferences and a strictly concave production
function, the equilibrium allocation, and so the equilibrium level of production, is unique. -/
theorem exercise_15_C_1a {E : RCEconomy}
    (hsc : PrefStrictlyConvex (nonnegOrthant 2) (utilityPref E.u))
    (hmono : UtilityStronglyMonotone E.u) (hfc : StrictConcaveOn ℝ (Set.Ici 0) E.f)
    {p w p' w' z z' : ℝ} {x x' : Fin 2 → ℝ} (h : E.IsWalrasEqm p w x z)
    (h' : E.IsWalrasEqm p' w' x' z') : x = x' ∧ z = z' ∧ E.f z = E.f z' := by
  have hconv := hsc.prefConvex (convex_nonnegOrthant 2)
  have hx := rc_first_welfare h (rc_eqm_price_pos hmono h).le
  have hx' := rc_first_welfare h' (rc_eqm_price_pos hmono h').le
  have heq := footnote_7_unique hconv hmono hfc hx hx'
  have hz : z = z' := by rw [h.2.2.2, h'.2.2.2, heq]
  exact ⟨heq, hz, by rw [hz]⟩

/-! ### Figure 15.C.3(a): failure of the second welfare theorem with a nonconvex technology -/

/-- **Figure 15.C.3(a)** (MWG, p. 529): `u = √x₁ + √x₂`, `L̄ = 1`, and the increasing-returns
production function `f(z) = z²` (a nonconvex production set). -/
noncomputable def fig15C3aEconomy : RCEconomy where
  u := fun x => Real.sqrt (x 0) + Real.sqrt (x 1)
  Lbar := 1
  f := fun z => z ^ 2

/-- `√a ≤ (a + c²)/(2c)` for `c > 0` (the tangent line of `√` at `c²`). -/
theorem sqrt_le_tangent {a c : ℝ} (ha : 0 ≤ a) (hc : 0 < c) :
    Real.sqrt a ≤ (a + c ^ 2) / (2 * c) := by
  rw [le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (Real.sqrt a - c), Real.sq_sqrt ha]

/-- **Figure 15.C.3(a)** (MWG, p. 529): `x* = (1/4, 9/16)` (`z* = 3/4`) maximizes the consumer's
utility over the feasible set. -/
theorem fig_15_C_3a_optimal : fig15C3aEconomy.IsOptimal ![1 / 4, 9 / 16] := by
  refine ⟨⟨fun l => by fin_cases l <;> norm_num, by norm_num [fig15C3aEconomy],
    by norm_num [fig15C3aEconomy]⟩, fun y hy => ?_⟩
  obtain ⟨hy0, hyL, hyf⟩ := hy
  simp only [fig15C3aEconomy] at hyL hyf ⊢
  have h1 : Real.sqrt (y 1) ≤ 1 - y 0 := by
    rw [Real.sqrt_le_left (by linarith)]
    exact hyf
  have h2 := sqrt_le_tangent (hy0 0) (by norm_num : (0 : ℝ) < 1 / 2)
  have e1 : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by
    rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have e2 : Real.sqrt (9 / 16 : ℝ) = 3 / 4 := by
    rw [show (9 / 16 : ℝ) = (3 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, e1, e2]
  have : (y 0 + (1 / 2) ^ 2) / (2 * (1 / 2)) = y 0 + 1 / 4 := by ring
  linarith

/-- **Figure 15.C.3(a)** (MWG, p. 529): the economy has no Walrasian equilibrium, so the optimum is
not supportable: with `p > 0` profits `p z² - w z` are unbounded, and with `p ≤ 0` the consumption
good is free. -/
theorem fig_15_C_3a_no_eqm (p w : ℝ) (x : Fin 2 → ℝ) (z : ℝ) :
    ¬ fig15C3aEconomy.IsWalrasEqm p w x z := by
  rintro ⟨hz, hx, -, -⟩
  by_cases hp : 0 < p
  · -- unbounded profits
    set M := (|w| + |p * z ^ 2 - w * z| + 1) / p + 1 with hM
    have hM1 : 1 ≤ M := by
      have : 0 ≤ (|w| + |p * z ^ 2 - w * z| + 1) / p := by positivity
      linarith
    have h := hz.2 M (by linarith)
    simp only [fig15C3aEconomy] at h
    have hpM : p * M ^ 2 ≥ p * M * M := by nlinarith
    have hkey : p * M ≥ |w| + |p * z ^ 2 - w * z| + 1 := by
      have : p * ((|w| + |p * z ^ 2 - w * z| + 1) / p) = |w| + |p * z ^ 2 - w * z| + 1 := by
        field_simp
      nlinarith
    have hw : w * M ≤ |w| * M := mul_le_mul_of_nonneg_right (le_abs_self w) (by linarith)
    have habs := le_abs_self (p * z ^ 2 - w * z)
    nlinarith [abs_nonneg w, abs_nonneg (p * z ^ 2 - w * z)]
  · rw [not_lt] at hp
    have hmem : x + Pi.single 1 1 ∈ fig15C3aEconomy.budget p w
        (p * fig15C3aEconomy.f z - w * z) := by
      refine ⟨fun l => ?_, ?_⟩
      · fin_cases l
        · simpa using hx.1.1 0
        · simp; linarith [hx.1.1 1]
      · have := hx.1.2
        simp only [Pi.add_apply, Pi.single_eq_same]
        simp only [ne_eq, zero_ne_one, not_false_eq_true, Pi.single_eq_of_ne, add_zero]
        nlinarith
    have h1 := hx.2 _ hmem
    simp only [fig15C3aEconomy, Pi.add_apply, Pi.single_eq_same] at h1
    simp only [ne_eq, zero_ne_one, not_false_eq_true, Pi.single_eq_of_ne, add_zero] at h1
    have : Real.sqrt (x 1) < Real.sqrt (x 1 + 1) :=
      Real.sqrt_lt_sqrt (hx.1.1 1) (by linarith)
    linarith

/-- **Figure 15.C.3(a)** (MWG, p. 529): at the relative price `w/p = 3/2` the optimum `x*` maximizes
utility on the budget set through it (profit income `π = (3/4)² - (3/2)(3/4)`), but `z* = 3/4`
does not maximize profit even locally: it is the minimizer of `z² - (3/2) z`, and every other
input level gives higher profit. -/
theorem fig_15_C_3a_prices :
    fig15C3aEconomy.IsConsumerOpt 1 (3 / 2) (1 * fig15C3aEconomy.f (3 / 4) - 3 / 2 * (3 / 4))
        ![1 / 4, 9 / 16] ∧
      ∀ z, z ≠ 3 / 4 → 1 * fig15C3aEconomy.f (3 / 4) - 3 / 2 * (3 / 4) <
        1 * fig15C3aEconomy.f z - 3 / 2 * z := by
  have e1 : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by
    rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have e2 : Real.sqrt (9 / 16 : ℝ) = 3 / 4 := by
    rw [show (9 / 16 : ℝ) = (3 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  refine ⟨⟨⟨fun l => by fin_cases l <;> norm_num, by norm_num [fig15C3aEconomy]⟩,
    fun y hy => ?_⟩, fun z hz => ?_⟩
  · obtain ⟨hy0, hb⟩ := hy
    simp only [fig15C3aEconomy] at hb ⊢
    have h1 := sqrt_le_tangent (hy0 0) (by norm_num : (0 : ℝ) < 1 / 2)
    have h2 := sqrt_le_tangent (hy0 1) (by norm_num : (0 : ℝ) < 3 / 4)
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, e1, e2]
    have : (y 0 + (1 / 2) ^ 2) / (2 * (1 / 2)) = y 0 + 1 / 4 := by ring
    have : (y 1 + (3 / 4) ^ 2) / (2 * (3 / 4)) = 2 / 3 * (y 1 + 9 / 16) := by ring
    nlinarith
  · simp only [fig15C3aEconomy]
    have : 0 < (z - 3 / 4) ^ 2 := by
      have : z - 3 / 4 ≠ 0 := sub_ne_zero.2 hz
      positivity
    nlinarith

end MWG.GeneralEquilibriumExamples
