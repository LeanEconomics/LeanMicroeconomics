/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGGeneralEquilibriumExamples.Welfare
import Mathlib.Analysis.Convex.Extrema
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-!
# Quasilinear Edgeworth boxes (MWG Exercises 15.B.8 and 15.B.10, pp. 541-542)

* **Exercise 15.B.8**: with continuous, strictly convex preferences quasilinear in good 1
  (`uᵢ = x₁ᵢ + φᵢ(x₂ᵢ)`, `φᵢ` strictly concave, `quasilinear_strictConcave` derives this from strict
  convexity of the preferences), all interior Pareto optimal allocations give each consumer the
  same amount of good 2: it maximizes `φ₁(t) + φ₂(ω̄₂ - t)` (`exercise_15_B_8`), as in Chapter 10
  (the Pareto optimal allocation of the non-numeraire good is independent of the distribution of
  the numeraire).
* **Exercise 15.B.10(a)**: with quasilinear preferences (same numeraire) an increase of consumer
  1's endowment can lower his equilibrium utility (`exercise_15_B_10a`; an example with the
  inelastic demand of `φ(x) = -α/x`).
* **Exercise 15.B.10(b)**: for a transfer `z ≥ 0` from consumer 2 to consumer 1, every equilibrium
  before the transfer gives, at the same prices, an equilibrium after it in which consumer 1 is
  better off by `p·z/p₂` (`exercise_15_B_10b`, with the numeraire unrestricted in sign as in
  Definition 3.B.7). The printed claim that consumer 1's utility cannot decrease is false when the
  equilibrium price is not unique (`exercise_15_B_10b_counterexample`, kinked `φ`).
-/

namespace MWG.GeneralEquilibriumExamples

open MWG.ConsumerChoice MWG.ClassicalDemand Kreps.PreferenceProperties Filter Topology

/-! ### Exercise 15.B.8 -/

/-- **Exercise 15.B.8** (MWG, p. 541). If preferences on `ℝ²₊` represented by `x₁ + φ(x₂)` are
strictly convex (Definition 3.B.5), then `φ` is strictly concave on `[0, ∞)`. -/
theorem quasilinear_strictConcave {φ : ℝ → ℝ}
    (h : PrefStrictlyConvex (nonnegOrthant 2) (utilityPref fun x => x 0 + φ (x 1))) :
    StrictConcaveOn ℝ (Set.Ici 0) φ := by
  refine ⟨convex_Ici 0, fun a ha b hb hab θ η hθ hη hθη => ?_⟩
  set c := max (φ a) (φ b) with hc
  set y : Fin 2 → ℝ := ![c - φ a, a] with hy
  set z : Fin 2 → ℝ := ![c - φ b, b] with hz
  have hym : y ∈ nonnegOrthant 2 := fun l => by
    fin_cases l
    · simp [hy, hc]
    · simpa [hy] using ha
  have hzm : z ∈ nonnegOrthant 2 := fun l => by
    fin_cases l
    · simp [hz, hc]
    · simpa [hz] using hb
  have hyz : y ≠ z := fun he => hab (by simpa [hy, hz] using congrFun he 1)
  have huy : y 0 + φ (y 1) = c := by simp [hy]
  have huz : z 0 + φ (z 1) = c := by simp [hz]
  have := (h y hym y hym z hzm (le_refl _) (by simp only [utilityPref]; rw [huy, huz]) hyz θ hθ
    (by linarith)).2
  simp only [utilityPref, not_le] at this
  have hη' : η = 1 - θ := by linarith
  subst hη'
  simp only [hy, hz, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
    Matrix.cons_val_one] at this
  simp only [smul_eq_mul]
  linarith

/-- **Exercise 15.B.8** (MWG, p. 541). Let `uᵢ(x) = x₁ + φᵢ(x₂)` on `ℝ²₊` with `φᵢ` continuous and
strictly concave on `[0, ∞)`. If `x` and `x'` are Pareto optimal allocations in the interior of the
Edgeworth box, then both consumers consume the same amount of good 2 in `x` and `x'`. -/
theorem exercise_15_B_8 {E : EdgeworthEconomy} (hX : ∀ i, E.X i = nonnegOrthant 2)
    {φ : Fin 2 → ℝ → ℝ} (hu : ∀ i, E.u i = fun x => x 0 + φ i (x 1))
    (hφc : ∀ i, Continuous (φ i)) (hφ : ∀ i, StrictConcaveOn ℝ (Set.Ici 0) (φ i))
    {x x' : Fin 2 → Fin 2 → ℝ} (hx : E.IsParetoOptimal x) (hx' : E.IsParetoOptimal x')
    (hint : ∀ i l, 0 < x i l) (hint' : ∀ i l, 0 < x' i l) : ∀ i, x i 1 = x' i 1 := by
  set W := E.totalEndowment with hW
  -- the surplus from good 2 when consumer 1 gets `t`
  set S : ℝ → ℝ := fun t => φ 0 t + φ 1 (W 1 - t) with hS
  have hSc : StrictConcaveOn ℝ (Set.Icc 0 (W 1)) S := by
    refine ⟨convex_Icc 0 (W 1), fun a ha b hb hab θ η hθ hη hθη => ?_⟩
    have h0 := (hφ 0).2 (Set.mem_Ici.2 ha.1) (Set.mem_Ici.2 hb.1) hab hθ hη hθη
    have h1 := (hφ 1).concaveOn.2 (Set.mem_Ici.2 (by linarith [ha.2] : (0 : ℝ) ≤ W 1 - a))
      (Set.mem_Ici.2 (by linarith [hb.2] : (0 : ℝ) ≤ W 1 - b)) hθ.le hη.le hθη
    have e : θ • (W 1 - a) + η • (W 1 - b) = W 1 - (θ • a + η • b) := by
      simp only [smul_eq_mul]
      have : W 1 = θ * W 1 + η * W 1 := by rw [← add_mul, hθη, one_mul]
      linarith
    rw [e] at h1
    simp only [hS, smul_eq_mul] at h0 h1 ⊢
    linarith
  -- an interior Pareto optimum maximizes `S`
  have hmax : ∀ y : Fin 2 → Fin 2 → ℝ, E.IsParetoOptimal y → (∀ i l, 0 < y i l) →
      IsMaxOn S (Set.Icc 0 (W 1)) (y 0 1) := by
    intro y hy hyint
    have hs0 : y 0 0 + y 1 0 = W 0 := by
      have := congrFun hy.1.2 0; simpa [Fin.sum_univ_two] using this
    have hs1 : y 0 1 + y 1 1 = W 1 := by
      have := congrFun hy.1.2 1; simpa [Fin.sum_univ_two] using this
    have hmem : y 0 1 ∈ Set.Icc 0 (W 1) := ⟨(hyint 0 1).le, by linarith [hyint 1 1]⟩
    refine IsMaxOn.of_isLocalMaxOn_of_concaveOn hmem ?_ hSc.concaveOn
    -- reallocate good 2 to `(t, W₂ - t)` keeping consumer 2's utility constant
    set g : ℝ → ℝ := fun t => y 1 0 + φ 1 (y 1 1) - φ 1 (W 1 - t) with hg
    have hgc : Continuous g := by fun_prop
    have hg0 : g (y 0 1) = y 1 0 := by simp [hg, ← hs1]
    have hev1 : ∀ᶠ t in 𝓝 (y 0 1), 0 < g t :=
      hgc.continuousAt.eventually (lt_mem_nhds (by rw [hg0]; exact hyint 1 0))
    have hev2 : ∀ᶠ t in 𝓝 (y 0 1), g t < W 0 :=
      hgc.continuousAt.eventually (gt_mem_nhds (by rw [hg0]; linarith [hyint 0 0]))
    filter_upwards [nhdsWithin_le_nhds hev1, nhdsWithin_le_nhds hev2, self_mem_nhdsWithin]
      with t ht1 ht2 htm
    by_contra hlt
    rw [not_le] at hlt
    set y' : Fin 2 → Fin 2 → ℝ := ![![W 0 - g t, t], ![g t, W 1 - t]] with hy'
    apply hy.2
    refine ⟨y', ⟨fun i => ?_, ?_⟩, fun i => ?_, 0, ?_⟩
    · rw [hX i]
      intro l
      fin_cases i <;> fin_cases l <;> simp [hy'] <;> linarith [htm.1, htm.2]
    · funext l
      fin_cases l <;> simp [hy', Fin.sum_univ_two, hW]
    · fin_cases i
      · change E.u 0 (y 0) ≤ E.u 0 (y' 0)
        rw [hu 0]
        simp only [hy', Matrix.cons_val_zero, Matrix.cons_val_one, hg]
        simp only [hS] at hlt
        linarith
      · change E.u 1 (y 1) ≤ E.u 1 (y' 1)
        rw [hu 1]
        simp [hy', hg]
    · rw [hu 0]
      simp only [hy', Matrix.cons_val_zero, Matrix.cons_val_one, hg]
      simp only [hS] at hlt
      linarith
  have h1 := hmax x hx hint
  have h2 := hmax x' hx' hint'
  have hm1 : x 0 1 ∈ Set.Icc 0 (W 1) := ⟨(hint 0 1).le, by
    have := congrFun hx.1.2 1; simp [Fin.sum_univ_two] at this; linarith [hint 1 1]⟩
  have hm2 : x' 0 1 ∈ Set.Icc 0 (W 1) := ⟨(hint' 0 1).le, by
    have := congrFun hx'.1.2 1; simp [Fin.sum_univ_two] at this; linarith [hint' 1 1]⟩
  -- a strictly concave function has at most one maximizer
  have heq : x 0 1 = x' 0 1 := by
    by_contra hne
    have := hSc.2 hm1 hm2 hne (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num)
    have hmid := h1 (hSc.1 hm1 hm2 (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
    have hle : S (x 0 1) ≤ S (x' 0 1) := h2 hm1
    have hle' : S (x' 0 1) ≤ S (x 0 1) := h1 hm2
    have hmid' : S (1 / 2 * x 0 1 + 1 / 2 * x' 0 1) ≤ S (x 0 1) := by
      simpa [smul_eq_mul] using hmid
    simp only [smul_eq_mul] at this
    linarith
  intro i
  fin_cases i
  · exact heq
  · have a := congrFun hx.1.2 1
    have b := congrFun hx'.1.2 1
    simp [Fin.sum_univ_two] at a b
    simp only [Fin.mk_one]
    linarith

/-- An instance of the hypotheses of `exercise_15_B_8`: `uᵢ = x₁ + √x₂`, endowments `(1, 1)` each;
the allocation `((1, 1), (1, 1))` is Pareto optimal and interior. -/
noncomputable def sqrtQLEconomy : EdgeworthEconomy :=
  ExchangeEconomy.ofOrthant (fun _ x => x 0 + Real.sqrt (x 1)) (fun _ => ![1, 1])

theorem sqrtQLEconomy_instance : sqrtQLEconomy.IsParetoOptimal (fun _ => ![1, 1]) ∧
    StrictConcaveOn ℝ (Set.Ici 0) Real.sqrt ∧ Continuous Real.sqrt := by
  refine ⟨⟨⟨fun i l => by fin_cases l <;> simp, ?_⟩,
    ?_⟩, Real.strictConcaveOn_sqrt, Real.continuous_sqrt⟩
  · rfl
  · rintro ⟨x', hx', hle, i, hi⟩
    have hs0 := congrFun hx'.2 0
    have hs1 := congrFun hx'.2 1
    simp [ExchangeEconomy.totalEndowment, sqrtQLEconomy, ExchangeEconomy.ofOrthant,
      Fin.sum_univ_two] at hs0 hs1
    have hm : ∀ j l, 0 ≤ x' j l := fun j l => hx'.1 j l
    have h0 := hle 0
    have h1 := hle 1
    simp only [sqrtQLEconomy, ExchangeEconomy.ofOrthant, Matrix.cons_val_zero,
      Matrix.cons_val_one, Real.sqrt_one] at h0 h1 hi
    -- `√t + √(2 - t) ≤ 2`
    have hsq := Real.sq_sqrt (hm 0 1)
    have hsq' := Real.sq_sqrt (hm 1 1)
    have hkey : Real.sqrt (x' 0 1) + Real.sqrt (x' 1 1) ≤ 2 := by
      nlinarith [sq_nonneg (Real.sqrt (x' 0 1) - Real.sqrt (x' 1 1)),
        Real.sqrt_nonneg (x' 0 1), Real.sqrt_nonneg (x' 1 1)]
    fin_cases i <;> simp at hi <;> linarith

/-! ### Exercise 15.B.10 -/

/-- Demand of the quasilinear consumer `u = -α/x₁ + x₂` on `{x₁ > 0, x₂ ≥ 0}` at prices `(p, 1)`:
if `c > 0` solves `p c² = α` and `w ≥ p c`, the unique demanded bundle is `(c, w - p c)`. -/
theorem invQL_demand {α p w c : ℝ} (hp : 0 < p) (hc : 0 < c) (hfoc : p * c ^ 2 = α)
    (hw : p * c ≤ w) :
    walrasianDemandOn {x : Fin 2 → ℝ | 0 < x 0 ∧ 0 ≤ x 1} (fun x => -(α / x 0) + x 1) ![p, 1] w =
      {![c, w - p * c]} := by
  have hα : 0 < α := by rw [← hfoc]; positivity
  have hdot : ∀ y : Fin 2 → ℝ, (![p, 1] : Fin 2 → ℝ) ⬝ᵥ y = p * y 0 + y 1 := fun y => by
    simp [dotProduct, Fin.sum_univ_two]
  -- `α/y + p y ≥ α/c + p c`, with equality only at `y = c`
  have key : ∀ y : ℝ, 0 < y → α / c + p * c ≤ α / y + p * y ∧
      (α / y + p * y = α / c + p * c → y = c) := by
    intro y hy
    have e : α / y + p * y - (α / c + p * c) = p * (c - y) ^ 2 / y := by
      rw [← hfoc]; field_simp; ring
    refine ⟨by have : 0 ≤ p * (c - y) ^ 2 / y := by positivity
               linarith, fun heq => ?_⟩
    have : p * (c - y) ^ 2 / y = 0 := by linarith
    rw [div_eq_zero_iff] at this
    rcases this with h | h
    · have := (mul_eq_zero.1 h).resolve_left hp.ne'
      nlinarith [sq_nonneg (c - y)]
    · linarith
  ext y
  simp only [Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨hy, hb⟩, hmax⟩
    rw [hdot] at hb
    have hmem : (![c, w - p * c] : Fin 2 → ℝ) ∈ budgetSetOn {x : Fin 2 → ℝ | 0 < x 0 ∧ 0 ≤ x 1}
        ![p, 1] w := ⟨⟨by simpa using hc, by simp; linarith⟩, by rw [hdot]; simp⟩
    have h1 := hmax _ hmem
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h1
    obtain ⟨k1, k2⟩ := key (y 0) hy.1
    have e0 : y 0 = c := k2 (by linarith)
    have e1 : y 1 = w - p * c := by
      rw [e0] at hb h1; linarith
    funext l
    fin_cases l
    · simpa using e0
    · simpa using e1
  · rintro rfl
    refine ⟨⟨⟨by simpa using hc, by simp; linarith⟩, by rw [hdot]; simp⟩, fun z hz => ?_⟩
    have hb := hz.2
    rw [hdot] at hb
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    linarith [(key (z 0) hz.1.1).1]

/-- Membership form of `invQL_demand` with endowment `(e₀, e₁)`. -/
theorem invQL_mem {α p e0 e1 c : ℝ} (hp : 0 < p) (hc : 0 < c) (hfoc : p * c ^ 2 = α)
    (hw : p * c ≤ p * e0 + e1) :
    (![c, e1 + p * (e0 - c)] : Fin 2 → ℝ) ∈ walrasianDemandOn {x : Fin 2 → ℝ | 0 < x 0 ∧ 0 ≤ x 1}
      (fun x => -(α / x 0) + x 1) ![p, 1] ((![p, 1] : Fin 2 → ℝ) ⬝ᵥ ![e0, e1]) := by
  have hdot : (![p, 1] : Fin 2 → ℝ) ⬝ᵥ ![e0, e1] = p * e0 + e1 := by
    simp [dotProduct, Fin.sum_univ_two]
  rw [hdot, invQL_demand hp hc hfoc hw, Set.mem_singleton_iff]
  funext l
  fin_cases l
  · rfl
  · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
    ring

/-- The economy of `exercise_15_B_10a`: utilities `-α/x₁ + x₂` with `α₁ = 1/16`, `α₂ = 1`
(quasilinear with the same numeraire, good 2), consumption sets `{x₁ > 0, x₂ ≥ 0}`, and
endowments `ω`. -/
noncomputable def ex15B10aEconomy (ω : Fin 2 → Fin 2 → ℝ) : EdgeworthEconomy where
  X := fun _ => {x | 0 < x 0 ∧ 0 ≤ x 1}
  u := ![fun x => -(1 / 16 / x 0) + x 1, fun x => -(1 / x 0) + x 1]
  ω := ω

/-- **Exercise 15.B.10(a)** (MWG, p. 542). With quasilinear preferences (same numeraire) an increase
in consumer 1's endowments from `ω₁ = (1, 1)` to `ω'₁ = (2, 101/100) ≫ ω₁` (consumer 2 keeps
`(1/10, 10)`) lowers consumer 1's equilibrium utility, from `-(1/16)/(11/50) + x₂₁` to a smaller
value: the equilibrium price of good 1 falls from `625/484` to `625/1764`, and consumer 1, a seller
of good 1 facing inelastic demand, loses (as a quantity-setting monopolist would by selling
more). -/
theorem exercise_15_B_10a :
    (ex15B10aEconomy ![![1, 1], ![1 / 10, 10]]).IsDemandEqm ![625 / 484, 1]
      ![![11 / 50, 1 + 625 / 484 * (1 - 11 / 50)],
        ![22 / 25, 10 + 625 / 484 * (1 / 10 - 22 / 25)]] ∧
    (ex15B10aEconomy ![![2, 101 / 100], ![1 / 10, 10]]).IsDemandEqm ![625 / 1764, 1]
      ![![21 / 50, 101 / 100 + 625 / 1764 * (2 - 21 / 50)],
        ![42 / 25, 10 + 625 / 1764 * (1 / 10 - 42 / 25)]] ∧
    -(1 / 16 / (21 / 50)) + (101 / 100 + 625 / 1764 * (2 - 21 / 50)) <
      -(1 / 16 / (11 / 50)) + (1 + 625 / 484 * (1 - 11 / 50) : ℝ) := by
  refine ⟨⟨⟨fun i => ?_, ?_⟩, fun i => ?_⟩, ⟨⟨fun i => ?_, ?_⟩, fun i => ?_⟩, by norm_num⟩
  · fin_cases i <;> norm_num [ex15B10aEconomy]
  · funext l
    fin_cases l <;> norm_num [ex15B10aEconomy, ExchangeEconomy.totalEndowment, Fin.sum_univ_two]
  · fin_cases i
    · exact invQL_mem (α := 1 / 16) (e0 := 1) (e1 := 1) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num)
    · exact invQL_mem (α := 1) (e0 := 1 / 10) (e1 := 10) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
  · fin_cases i <;> norm_num [ex15B10aEconomy]
  · funext l
    fin_cases l <;> norm_num [ex15B10aEconomy, ExchangeEconomy.totalEndowment, Fin.sum_univ_two]
  · fin_cases i
    · exact invQL_mem (α := 1 / 16) (e0 := 2) (e1 := 101 / 100) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
    · exact invQL_mem (α := 1) (e0 := 1 / 10) (e1 := 10) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)

/-- With a numeraire whose consumption may be of either sign (Definition 3.B.7's domain
`quasilinearDomain`), quasilinear demand shifts with wealth along the numeraire:
`x ∈ x(p, w)` implies `x + (Δ/p₂) e₂ ∈ x(p, w + Δ)` for every `Δ` (`p₂ > 0`). -/
theorem quasilinear_demand_shift {φ : ℝ → ℝ} {p : Fin 2 → ℝ} (hp : 0 < p 1) {w Δ : ℝ}
    {x : Fin 2 → ℝ}
    (hx : x ∈ walrasianDemandOn (quasilinearDomain 1) (fun y => φ (y 0) + y 1) p w) :
    x + (Δ / p 1) • Pi.single 1 1 ∈
      walrasianDemandOn (quasilinearDomain 1) (fun y => φ (y 0) + y 1) p (w + Δ) := by
  have hcost : ∀ y : Fin 2 → ℝ, p ⬝ᵥ (y + (Δ / p 1) • Pi.single 1 1) = p ⬝ᵥ y + Δ := by
    intro y
    rw [dotProduct_add, dotProduct_smul, dotProduct_single, smul_eq_mul, mul_one,
      div_mul_cancel₀ _ hp.ne']
  have hdom : ∀ y : Fin 2 → ℝ, y ∈ quasilinearDomain 1 → ∀ c : ℝ,
      y + c • Pi.single 1 1 ∈ quasilinearDomain 1 := by
    intro y hy c l hl
    simp [hl, hy l hl]
  refine ⟨⟨hdom x hx.1.1 _, by rw [hcost]; linarith [hx.1.2]⟩, fun y hy => ?_⟩
  have hy' : y + (-(Δ / p 1)) • Pi.single 1 1 ∈ budgetSetOn (quasilinearDomain 1) p w := by
    refine ⟨hdom y hy.1 _, ?_⟩
    rw [dotProduct_add, dotProduct_smul, dotProduct_single, smul_eq_mul, mul_one, neg_mul,
      div_mul_cancel₀ _ hp.ne']
    linarith [hy.2]
  have h := hx.2 _ hy'
  simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at h ⊢
  simp only [ne_eq, zero_ne_one, not_false_eq_true, Pi.single_eq_of_ne, mul_zero,
    add_zero] at h ⊢
  linarith

/-- **Exercise 15.B.10(b)** (MWG, p. 542), corrected. Quasilinear preferences with the same
numeraire (good 2, unrestricted in sign as in Definition 3.B.7). If `(p, x)` is a Walrasian
equilibrium (`p₂ > 0`) and consumer 2 transfers `z` to consumer 1, then at the same prices the
allocation in which consumer 1 gets `p·z/p₂` more and consumer 2 `p·z/p₂` less of the numeraire
is an equilibrium of the new economy, and consumer 1's utility rises by `p·z/p₂ ≥ 0` (`p, z ≥ 0`).
(With several equilibrium prices the printed claim fails: `exercise_15_B_10b_counterexample`.) -/
theorem exercise_15_B_10b {φ : Fin 2 → ℝ → ℝ} {ω : Fin 2 → Fin 2 → ℝ} {z p : Fin 2 → ℝ}
    (hp1 : 0 < p 1) {x : Fin 2 → Fin 2 → ℝ}
    (h : (⟨fun _ => quasilinearDomain 1, fun i y => φ i (y 0) + y 1, ω⟩ :
      EdgeworthEconomy).IsDemandEqm p x) :
    (⟨fun _ => quasilinearDomain 1, fun i y => φ i (y 0) + y 1, ![ω 0 + z, ω 1 - z]⟩ :
      EdgeworthEconomy).IsDemandEqm p
        ![x 0 + (p ⬝ᵥ z / p 1) • Pi.single 1 1, x 1 + (-(p ⬝ᵥ z / p 1)) • Pi.single 1 1] ∧
      φ 0 ((x 0 + (p ⬝ᵥ z / p 1) • Pi.single 1 1 : Fin 2 → ℝ) 0) +
        (x 0 + (p ⬝ᵥ z / p 1) • Pi.single 1 1 : Fin 2 → ℝ) 1 =
        φ 0 (x 0 0) + x 0 1 + p ⬝ᵥ z / p 1 := by
  obtain ⟨hbox, hd⟩ := h
  refine ⟨⟨⟨fun i => ?_, ?_⟩, fun i => ?_⟩, ?_⟩
  · fin_cases i
    · intro l hl; simp [hl, (hd 0).1.1 l hl]
    · intro l hl; simp [hl, (hd 1).1.1 l hl]
  · have h2 := hbox.2
    simp only [ExchangeEconomy.totalEndowment, Fin.sum_univ_two] at h2 ⊢
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    funext l
    have := congrFun h2 l
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at this ⊢
    linarith
  · fin_cases i
    · have := quasilinear_demand_shift (φ := φ 0) (Δ := p ⬝ᵥ z) hp1 (hd 0)
      change _ ∈ walrasianDemandOn _ _ p (p ⬝ᵥ (ω 0 + z))
      rw [dotProduct_add]
      exact this
    · have := quasilinear_demand_shift (φ := φ 1) (Δ := -(p ⬝ᵥ z)) hp1 (hd 1)
      change _ ∈ walrasianDemandOn _ _ p (p ⬝ᵥ (ω 1 - z))
      rw [dotProduct_sub, sub_eq_add_neg, ← neg_div]
      exact this
  · simp
    ring

/-- The kinked, strictly concave and strictly increasing `φ(x) = min(2x, x + 1) + √x` of
`exercise_15_B_10b_counterexample`. -/
noncomputable def kinkedPhi (x : ℝ) : ℝ := min (2 * x) (x + 1) + Real.sqrt x

/-- `φ(y) - q y ≤ φ(1) - q - (√y - 1)²/2` for `q ∈ [3/2, 5/2]`, `y ≥ 0`: the superdifferential of
`φ` at `1` is `[3/2, 5/2]`. -/
theorem kinkedPhi_le {q y : ℝ} (hq1 : 3 / 2 ≤ q) (hq2 : q ≤ 5 / 2) (hy : 0 ≤ y) :
    kinkedPhi y - q * y ≤ kinkedPhi 1 - q - (Real.sqrt y - 1) ^ 2 / 2 := by
  have hs := Real.sq_sqrt hy
  have hs0 := Real.sqrt_nonneg y
  have h1 : kinkedPhi 1 = 3 := by norm_num [kinkedPhi]
  rw [h1, kinkedPhi]
  rcases le_total y 1 with h | h
  · rw [min_eq_left (by linarith)]
    nlinarith
  · rw [min_eq_right (by linarith)]
    nlinarith

/-- The kinked quasilinear consumer's demand at prices `(q, 1)` with `q ∈ [3/2, 5/2]` and wealth
`w ≥ q` is the single bundle `(1, w - q)`. -/
theorem kinked_demand {q w : ℝ} (hq1 : 3 / 2 ≤ q) (hq2 : q ≤ 5 / 2) (hw : q ≤ w) :
    walrasianDemand (fun y => kinkedPhi (y 0) + y 1) ![q, 1] w = {![1, w - q]} := by
  have hdot : ∀ y : Fin 2 → ℝ, (![q, 1] : Fin 2 → ℝ) ⬝ᵥ y = q * y 0 + y 1 := fun y => by
    simp [dotProduct, Fin.sum_univ_two]
  have hmem : (![1, w - q] : Fin 2 → ℝ) ∈ budgetSet ![q, 1] w :=
    ⟨fun l => by
      fin_cases l
      · norm_num
      · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
        linarith, by rw [hdot]; simp⟩
  ext y
  simp only [Set.mem_singleton_iff]
  constructor
  · rintro ⟨hy, hmax⟩
    have hb := hy.2
    rw [hdot] at hb
    have h1 := hmax _ hmem
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h1
    have h2 := kinkedPhi_le hq1 hq2 (hy.1 0)
    have hsq : (Real.sqrt (y 0) - 1) ^ 2 = 0 := by
      nlinarith [sq_nonneg (Real.sqrt (y 0) - 1)]
    have hs1 : Real.sqrt (y 0) = 1 := by nlinarith [sq_nonneg (Real.sqrt (y 0) - 1)]
    have e0 : y 0 = 1 := by rw [← Real.sq_sqrt (hy.1 0), hs1]; norm_num
    have e1 : y 1 = w - q := by
      rw [e0] at hb h1 h2
      linarith
    funext l
    fin_cases l
    · simpa using e0
    · simpa using e1
  · rintro rfl
    refine ⟨hmem, fun y hy => ?_⟩
    have hb := hy.2
    rw [hdot] at hb
    have h2 := kinkedPhi_le hq1 hq2 (hy.1 0)
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    nlinarith [sq_nonneg (Real.sqrt (y 0) - 1)]

/-- The kinked `φ` is strictly concave and strictly increasing on `[0, ∞)`. -/
theorem kinkedPhi_props : StrictConcaveOn ℝ (Set.Ici 0) kinkedPhi ∧
    StrictMonoOn kinkedPhi (Set.Ici 0) := by
  constructor
  · refine ⟨convex_Ici 0, fun a ha b hb hab θ η hθ hη hθη => ?_⟩
    have hs := Real.strictConcaveOn_sqrt.2 ha hb hab hθ hη hθη
    simp only [smul_eq_mul] at hs ⊢
    simp only [kinkedPhi]
    have hmin : θ * min (2 * a) (a + 1) + η * min (2 * b) (b + 1) ≤
        min (2 * (θ * a + η * b)) (θ * a + η * b + 1) := by
      refine le_min ?_ ?_
      · nlinarith [min_le_left (2 * a) (a + 1), min_le_left (2 * b) (b + 1)]
      · nlinarith [min_le_right (2 * a) (a + 1), min_le_right (2 * b) (b + 1)]
    linarith
  · intro a ha b hb hab
    simp only [kinkedPhi]
    have := Real.sqrt_lt_sqrt ha hab
    have : min (2 * a) (a + 1) ≤ min (2 * b) (b + 1) :=
      min_le_min (by linarith) (by linarith)
    linarith

/-- The equilibria of the kinked quasilinear Edgeworth box with endowments `e₁, e₂` (total of
good 1 equal to `2`): at any `q ∈ [3/2, 5/2]`, each consumer consumes one unit of good 1. -/
theorem kinked_isDemandEqm {e₁ e₂ : Fin 2 → ℝ} {q : ℝ} (hq1 : 3 / 2 ≤ q) (hq2 : q ≤ 5 / 2)
    (hw₁ : q ≤ q * e₁ 0 + e₁ 1) (hw₂ : q ≤ q * e₂ 0 + e₂ 1) (htot : e₁ 0 + e₂ 0 = 2) :
    (ExchangeEconomy.ofOrthant (fun _ y => kinkedPhi (y 0) + y 1) ![e₁, e₂] :
      EdgeworthEconomy).IsDemandEqm ![q, 1]
      ![![1, q * e₁ 0 + e₁ 1 - q], ![1, q * e₂ 0 + e₂ 1 - q]] := by
  have hd : ∀ e : Fin 2 → ℝ, q ≤ q * e 0 + e 1 →
      (![1, q * e 0 + e 1 - q] : Fin 2 → ℝ) ∈ walrasianDemand (fun y => kinkedPhi (y 0) + y 1)
        ![q, 1] ((![q, 1] : Fin 2 → ℝ) ⬝ᵥ e) := by
    intro e hw
    have h : (![q, 1] : Fin 2 → ℝ) ⬝ᵥ e = q * e 0 + e 1 := by
      simp [dotProduct, Fin.sum_univ_two]
    rw [h, kinked_demand hq1 hq2 hw]
    rfl
  refine ⟨⟨fun i => ?_, ?_⟩, fun i => ?_⟩
  · fin_cases i
    · exact (hd e₁ hw₁).1.1
    · exact (hd e₂ hw₂).1.1
  · funext l
    fin_cases l
    · simp [ExchangeEconomy.totalEndowment, ExchangeEconomy.ofOrthant, Fin.sum_univ_two]
      linarith
    · simp [ExchangeEconomy.totalEndowment, ExchangeEconomy.ofOrthant, Fin.sum_univ_two]
      nlinarith
  · fin_cases i
    · exact hd e₁ hw₁
    · exact hd e₂ hw₂

/-- **Exercise 15.B.10(b)** (MWG, p. 542): the claim as printed is false. Both consumers have the
continuous, strictly convex, strongly monotone quasilinear utility `φ(x₁) + x₂` with the kinked
`φ = kinkedPhi` (same numeraire). Before the transfer, endowments `(3/2, 10)` and `(1/2, 10)`:
`p = (5/2, 1)` with `x₁ = (1, 45/4)` is an equilibrium. After consumer 2 transfers `z = (1/10, 0)`
to consumer 1 (endowments `(8/5, 10)`, `(2/5, 10)`): `p = (3/2, 1)` with `x'₁ = (1, 109/10)` is an
equilibrium, and consumer 1 is worse off. (Every price in `[3/2, 5/2]` is an equilibrium price in
both economies; consistently with Exercise 15.B.10(d), before the transfer `p = (3/2, 1)` gives
consumer 1 the even lower utility `φ(1) + 43/4`.) -/
theorem exercise_15_B_10b_counterexample :
    (ExchangeEconomy.ofOrthant (fun _ y => kinkedPhi (y 0) + y 1)
        ![![3 / 2, 10], ![1 / 2, 10]] : EdgeworthEconomy).IsDemandEqm ![5 / 2, 1]
      ![![1, 45 / 4], ![1, 35 / 4]] ∧
    (ExchangeEconomy.ofOrthant (fun _ y => kinkedPhi (y 0) + y 1)
        ![![8 / 5, 10], ![2 / 5, 10]] : EdgeworthEconomy).IsDemandEqm ![3 / 2, 1]
      ![![1, 109 / 10], ![1, 91 / 10]] ∧
    kinkedPhi 1 + 109 / 10 < kinkedPhi 1 + 45 / 4 ∧
    (ExchangeEconomy.ofOrthant (fun _ y => kinkedPhi (y 0) + y 1)
        ![![3 / 2, 10], ![1 / 2, 10]] : EdgeworthEconomy).IsDemandEqm ![3 / 2, 1]
      ![![1, 43 / 4], ![1, 37 / 4]] ∧ kinkedPhi 1 + 43 / 4 < kinkedPhi 1 + 109 / 10 := by
  refine ⟨?_, ?_, by norm_num, ?_, by norm_num⟩
  · convert kinked_isDemandEqm (e₁ := ![3 / 2, 10]) (e₂ := ![1 / 2, 10]) (q := 5 / 2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) using 1
    funext i l
    fin_cases i <;> fin_cases l <;> norm_num
  · convert kinked_isDemandEqm (e₁ := ![8 / 5, 10]) (e₂ := ![2 / 5, 10]) (q := 3 / 2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) using 1
    funext i l
    fin_cases i <;> fin_cases l <;> norm_num
  · convert kinked_isDemandEqm (e₁ := ![3 / 2, 10]) (e₂ := ![1 / 2, 10]) (q := 3 / 2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) using 1
    funext i l
    fin_cases i <;> fin_cases l <;> norm_num

end MWG.GeneralEquilibriumExamples
