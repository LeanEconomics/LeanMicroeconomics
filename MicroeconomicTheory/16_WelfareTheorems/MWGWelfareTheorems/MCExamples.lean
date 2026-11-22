/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGWelfareTheorems.MarginalCost

/-!
# Marginal cost pricing: examples and exercises (MWG Section 16.G, pp. 571-572, 576)

* **Figure 16.G.1**: one consumer (`u = x₁x₂`), the increasing-returns technology `q ≤ z²` and
  `ω̄ = (3/2, 0)`. The optimum `x* = (1/2, 1)` is a marginal cost price equilibrium only at prices
  proportional to `(2, 1)`, at which the firm makes a loss and would rather shut down.
* **Figure 16.G.2**: with `u = x₁ + x₂` and `ω̄ = (1, 0)`, `x* = (1/2, 1/4)` is a marginal cost
  price equilibrium at `p = (1, 1)` that is not Pareto optimal.
* **Exercise 16.G.3**: a one-consumer, one-firm economy with two inputs and one output and a
  non-quasiconcave production function in which the marginal cost price equilibrium (with
  efficient production) is unique and the inputs are not chosen at minimum cost.
* **Exercise 16.G.4**: with a single consumer, an optimum is a marginal cost price equilibrium
  (Proposition 16.G.1), and an optimum exists when the set of feasible allocations is compact.
  The book's "under the general conditions of Section 16.G" does not guarantee an optimum: in
  `noOptimumEconomy` every assumption of Section 16.F holds and no allocation is Pareto optimal
  (correction 5).
-/

namespace MWG.WelfareTheorems

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.Production Kreps.PreferenceProperties
open MWG.CompetitiveMarkets (Allocation)
open Filter Topology

/-- The technology `q ≤ z²` of Figures 16.G.1-16.G.2 as `F(y) = y₂ - y₁²` on `y₁ ≤ 0`. -/
def sqTechF (y : Fin 2 → ℝ) : ℝ := y 1 - y 0 ^ 2

/-- The production set `{y : y₁ ≤ 0, F(y) ≤ 0}` of Figures 16.G.1-16.G.2 (nonconvex). -/
def sqTechY : Set (Fin 2 → ℝ) := {y | y 0 ≤ 0 ∧ sqTechF y ≤ 0}

/-- The derivative of `sqTechF` at `y`: `∂F/∂y₁ = -2y₁`, `∂F/∂y₂ = 1`. -/
theorem sqTechF_hasFDerivAt (y : Fin 2 → ℝ) :
    ∃ F' : (Fin 2 → ℝ) →L[ℝ] ℝ, HasFDerivAt sqTechF F' y ∧
      F' (Pi.single 0 1) = -2 * y 0 ∧ F' (Pi.single 1 1) = 1 := by
  have h0 := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0).hasFDerivAt (x := y)
  have h1 := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1).hasFDerivAt (x := y)
  have key := h1.sub (h0.mul h0)
  refine ⟨_, key.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => ?_), ?_, ?_⟩
  · simp [sqTechF, sq]
  · simp; ring
  · simp

/-- **Figure 16.G.1** (MWG, p. 571). One consumer with `u(x) = x₁x₂`, the technology `sqTechY`,
`ω̄ = (3/2, 0)`. -/
noncomputable def fig16G1Economy : PrefEconomy Unit Unit 2 :=
  PrefEconomy.ofUtility (fun _ => nonnegOrthant 2) (fun _ x => x 0 * x 1) (fun _ => sqTechY)
    ![3 / 2, 0]

/-- The optimum of Figure 16.G.1: `x* = (1/2, 1)`, `y* = (-1, 1)`. -/
noncomputable def fig16G1Alloc : Allocation Unit Unit 2 := ⟨fun _ => ![1 / 2, 1], fun _ => ![-1, 1]⟩

/-- **Figure 16.G.1** (MWG, p. 571). The allocation `x* = (1/2, 1)` is Pareto optimal (it maximizes
the consumer's utility) and is a marginal cost price equilibrium at `p = (2, 1)`; every marginal
cost price equilibrium supporting it has `p₁ = 2p₂` (the only supporting relative prices); at these
prices the firm makes a loss, and shutting down (`0 ∈ Y`) is more profitable. -/
theorem figure_16_G_1 :
    fig16G1Economy.IsParetoOptimal fig16G1Alloc ∧
      fig16G1Economy.IsMCPriceEqm (fun _ => sqTechF) fig16G1Alloc ![2, 1] (fun _ => 2) ∧
      (∀ p w, fig16G1Economy.IsMCPriceEqm (fun _ => sqTechF) fig16G1Alloc p w →
        p 0 = 2 * p 1 ∧ 0 < p 1 ∧ p ⬝ᵥ fig16G1Alloc.y () < p ⬝ᵥ (0 : Fin 2 → ℝ) ∧
          (0 : Fin 2 → ℝ) ∈ sqTechY) := by
  have hfeas : fig16G1Economy.IsFeasible fig16G1Alloc := by
    refine ⟨⟨fun _ l => ?_, fun _ => ⟨by simp [fig16G1Alloc], by
      simp [fig16G1Alloc, sqTechF]⟩⟩, ?_⟩
    · fin_cases l <;> norm_num [fig16G1Alloc]
    · funext l; fin_cases l <;> norm_num [fig16G1Economy, PrefEconomy.ofUtility, fig16G1Alloc]
  refine ⟨⟨hfeas, ?_⟩, ⟨?_, fun _ => ⟨hfeas.1.2 (), ?_⟩, fun _ => ⟨⟨hfeas.1.1 (), ?_⟩,
    fun x hx => ?_⟩, hfeas.2⟩, fun p w h => ?_⟩
  · rintro ⟨a', ⟨⟨hx', hy'⟩, hc'⟩, -, k, hk⟩
    apply hk.2
    have h0 := congrFun hc' 0
    have h1 := congrFun hc' 1
    simp only [Finset.univ_unique, PUnit.default_eq_unit, Fin.isValue, Finset.sum_apply,
      Finset.sum_singleton, fig16G1Economy, PrefEconomy.ofUtility, Pi.add_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, zero_add] at h0 h1
    obtain ⟨hy0, hy1⟩ := hy' ()
    simp only [sqTechF] at hy1
    have hx0 := hx' () 0
    have hx1 := hx' () 1
    change a'.x () 0 * a'.x () 1 ≤ (fig16G1Alloc.x ()) 0 * (fig16G1Alloc.x ()) 1
    simp only [fig16G1Alloc, Matrix.cons_val_zero, Matrix.cons_val_one]
    have hle : a'.x () 1 ≤ a'.y () 0 ^ 2 := by linarith
    have hcub : (3 / 2 + a'.y () 0) * a'.y () 0 ^ 2 ≤ 1 / 2 := by
      nlinarith [sq_nonneg (a'.y () 0 + 1), sq_nonneg (a'.y () 0)]
    calc a'.x () 0 * a'.x () 1 ≤ a'.x () 0 * a'.y () 0 ^ 2 :=
          mul_le_mul_of_nonneg_left hle hx0
      _ = (3 / 2 + a'.y () 0) * a'.y () 0 ^ 2 := by rw [h0]
      _ ≤ 1 / 2 * 1 := by linarith
  · simp [fig16G1Economy, PrefEconomy.ofUtility, fig16G1Alloc]
    norm_num
  · obtain ⟨F', hF', h0, h1⟩ := sqTechF_hasFDerivAt (fig16G1Alloc.y ())
    refine ⟨F', hF', 1, one_pos, fun l => ?_⟩
    fin_cases l
    · simp [h0, fig16G1Alloc]
    · simp [h1]
  · simp [fig16G1Alloc]
    norm_num
  · change x 0 * x 1 ≤ (fig16G1Alloc.x ()) 0 * (fig16G1Alloc.x ()) 1
    have hb := hx.2
    rw [dot_two] at hb
    simp only [fig16G1Alloc, Matrix.cons_val_zero, Matrix.cons_val_one] at hb ⊢
    have := hx.1 0
    have := hx.1 1
    nlinarith [sq_nonneg (2 * x 0 - x 1)]
  · obtain ⟨-, F', hF', γ, hγ, hp⟩ := h.2.1 ()
    obtain ⟨G', hG', hG0, hG1⟩ := sqTechF_hasFDerivAt (fig16G1Alloc.y ())
    have huniq := hF'.unique hG'
    have hp0 := hp 0
    have hp1 := hp 1
    rw [huniq, hG0] at hp0
    rw [huniq, hG1] at hp1
    simp only [Fin.isValue, fig16G1Alloc, one_div, Matrix.cons_val_zero, mul_neg, mul_one,
      neg_neg] at hp0
    refine ⟨by rw [hp0, hp1]; ring, by rw [hp1]; linarith, ?_, ⟨le_rfl, by simp [sqTechF]⟩⟩
    rw [dot_two, dot_two]
    simp [fig16G1Alloc, hp0, hp1]
    linarith

/-- **Figure 16.G.2** (MWG, p. 572). One consumer with `u(x) = x₁ + x₂`, the technology `sqTechY`,
`ω̄ = (1, 0)`. -/
def fig16G2Economy : PrefEconomy Unit Unit 2 :=
  PrefEconomy.ofUtility (fun _ => nonnegOrthant 2) (fun _ x => x 0 + x 1) (fun _ => sqTechY)
    ![1, 0]

/-- The allocation of Figure 16.G.2: `x* = (1/2, 1/4)`, `y* = (-1/2, 1/4)`. -/
noncomputable def fig16G2Alloc : Allocation Unit Unit 2 :=
  ⟨fun _ => ![1 / 2, 1 / 4], fun _ => ![-1 / 2, 1 / 4]⟩

/-- **Figure 16.G.2** (MWG, p. 572). `x*` is a marginal cost price equilibrium with transfers at
`p = (1, 1)` but is not Pareto optimal: `x' = (0, 1)` (produced with `y' = (-1, 1)`) is better. -/
theorem figure_16_G_2 :
    fig16G2Economy.IsMCPriceEqm (fun _ => sqTechF) fig16G2Alloc ![1, 1] (fun _ => 3 / 4) ∧
      ¬ fig16G2Economy.IsParetoOptimal fig16G2Alloc := by
  have hfeasY : fig16G2Alloc.y () ∈ sqTechY :=
    ⟨by norm_num [fig16G2Alloc], by norm_num [fig16G2Alloc, sqTechF]⟩
  refine ⟨⟨?_, fun _ => ⟨hfeasY, ?_⟩, fun _ => ⟨⟨fun l => ?_, ?_⟩, fun x hx => ?_⟩, ?_⟩, ?_⟩
  · simp [fig16G2Economy, PrefEconomy.ofUtility, fig16G2Alloc]
    norm_num
  · obtain ⟨F', hF', h0, h1⟩ := sqTechF_hasFDerivAt (fig16G2Alloc.y ())
    refine ⟨F', hF', 1, one_pos, fun l => ?_⟩
    fin_cases l
    · simp [h0, fig16G2Alloc]; norm_num
    · simp [h1]
  · fin_cases l <;> norm_num [fig16G2Alloc]
  · simp [fig16G2Alloc]
    norm_num
  · change x 0 + x 1 ≤ (fig16G2Alloc.x ()) 0 + (fig16G2Alloc.x ()) 1
    have hb := hx.2
    rw [dot_two] at hb
    simp only [fig16G2Alloc, Matrix.cons_val_zero, Matrix.cons_val_one] at hb ⊢
    linarith
  · funext l; fin_cases l <;> norm_num [fig16G2Economy, PrefEconomy.ofUtility, fig16G2Alloc]
  · rintro ⟨-, hno⟩
    refine hno ⟨⟨fun _ => ![0, 1], fun _ => ![-1, 1]⟩, ⟨⟨fun _ l => ?_, fun _ => ⟨?_, ?_⟩⟩, ?_⟩,
      fun _ => ?_, (), ?_⟩
    · fin_cases l <;> norm_num
    · norm_num
    · norm_num [sqTechF]
    · funext l; fin_cases l <;> norm_num [fig16G2Economy, PrefEconomy.ofUtility]
    · simp only [fig16G2Economy, PrefEconomy.ofUtility, utilityPref, fig16G2Alloc]
      norm_num
    · simp only [fig16G2Economy, PrefEconomy.ofUtility, utilityPref, fig16G2Alloc, Strict]
      norm_num

/-! ## Exercise 16.G.3 -/

/-- **Exercise 16.G.3** (MWG, p. 576). Inputs `z₁, z₂`, output `q ≤ f(z) = z₁ + z₂ + z₁² + z₂²`
(not quasiconcave), written as `F(y) = y₃ + y₁ + y₂ - y₁² - y₂²` on `y₁, y₂ ≤ 0`. -/
def ex16G3F (y : Fin 3 → ℝ) : ℝ := y 2 + y 0 + y 1 - y 0 ^ 2 - y 1 ^ 2

/-- The production set of Exercise 16.G.3. -/
def ex16G3Y : Set (Fin 3 → ℝ) := {y | y 0 ≤ 0 ∧ y 1 ≤ 0 ∧ ex16G3F y ≤ 0}

/-- The economy of Exercise 16.G.3: one consumer who values only the output (`u(x) = x₃`), the
endowment `ω̄ = (1, 1, 0)` of inputs, one firm. -/
def ex16G3Economy : PrefEconomy Unit Unit 3 :=
  PrefEconomy.ofUtility (fun _ => nonnegOrthant 3) (fun _ x => x 2) (fun _ => ex16G3Y) ![1, 1, 0]

/-- The derivative of `ex16G3F`. -/
theorem ex16G3F_hasFDerivAt (y : Fin 3 → ℝ) :
    ∃ F' : (Fin 3 → ℝ) →L[ℝ] ℝ, HasFDerivAt ex16G3F F' y ∧ F' (Pi.single 0 1) = 1 - 2 * y 0 ∧
      F' (Pi.single 1 1) = 1 - 2 * y 1 ∧ F' (Pi.single 2 1) = 1 := by
  have h0 := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 0).hasFDerivAt (x := y)
  have h1 := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 1).hasFDerivAt (x := y)
  have h2 := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 2).hasFDerivAt (x := y)
  have key := (((h2.add h0).add h1).sub (h0.mul h0)).sub (h1.mul h1)
  refine ⟨_, key.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => ?_), ?_, ?_, ?_⟩
  · simp [ex16G3F, sq]
  · simp; ring
  · simp; ring
  · simp

/-- **Exercise 16.G.3** (MWG, p. 576). In `ex16G3Economy`, `x* = (0, 0, 4)`, `y* = (-1, -1, 4)`,
`p = (3, 3, 1)` form a marginal cost price equilibrium; it is the only one with efficient
production (`F(y*) = 0`), up to the scale of `p`; the production function is not quasiconcave;
and the input bundle `(1, 1)` does not minimize the cost of producing `4` at input prices `(3, 3)`
(the bundle `(8/5, 0)` produces more at cost `24/5 < 6`). -/
theorem exercise_16_G_3 :
    ex16G3Economy.IsMCPriceEqm (fun _ => ex16G3F) ⟨fun _ => ![0, 0, 4], fun _ => ![-1, -1, 4]⟩
        ![3, 3, 1] (fun _ => 4) ∧
      (∀ (a : Allocation Unit Unit 3) p w, ex16G3Economy.IsMCPriceEqm (fun _ => ex16G3F) a p w →
        ex16G3F (a.y ()) = 0 →
        a.x () = ![0, 0, 4] ∧ a.y () = ![-1, -1, 4] ∧ ∃ γ : ℝ, 0 < γ ∧ p = γ • ![3, 3, 1]) ∧
      (1 + 1 + 1 ^ 2 + 1 ^ 2 : ℝ) < min (2 + 0 + 2 ^ 2 + 0 ^ 2) (0 + 2 + 0 ^ 2 + 2 ^ 2) ∧
      (![-8 / 5, 0, 4] : Fin 3 → ℝ) ∈ ex16G3Y ∧ (3 * (8 / 5) + 3 * 0 : ℝ) < 3 * 1 + 3 * 1 := by
  have hdot : ∀ p x : Fin 3 → ℝ, p ⬝ᵥ x = p 0 * x 0 + p 1 * x 1 + p 2 * x 2 := fun p x => by
    simp [dotProduct, Fin.sum_univ_three]
  refine ⟨⟨?_, fun _ => ⟨⟨by norm_num, by norm_num, by norm_num [ex16G3F]⟩, ?_⟩,
    fun _ => ⟨⟨fun l => ?_, ?_⟩, fun x hx => ?_⟩, ?_⟩, fun a p w h hF0 => ?_, by norm_num,
    ⟨by norm_num, by norm_num, by norm_num [ex16G3F]⟩, by norm_num⟩
  · simp [ex16G3Economy, PrefEconomy.ofUtility, hdot]
    norm_num
  · obtain ⟨F', hF', h0, h1, h2⟩ := ex16G3F_hasFDerivAt ![-1, -1, 4]
    refine ⟨F', hF', 1, one_pos, fun l => ?_⟩
    fin_cases l
    · simp [h0]; norm_num
    · simp [h1]; norm_num
    · simp [h2]
  · fin_cases l <;> norm_num
  · simp [hdot]
  · change x 2 ≤ (![0, 0, 4] : Fin 3 → ℝ) 2
    have hb := hx.2
    rw [hdot] at hb
    have := hx.1 0
    have := hx.1 1
    simp at hb ⊢
    linarith
  · funext l; fin_cases l <;> norm_num [ex16G3Economy, PrefEconomy.ofUtility]
  · -- uniqueness
    obtain ⟨⟨hy0, hy1, -⟩, F', hF', γ, hγ, hp⟩ := h.2.1 ()
    obtain ⟨G', hG', hG0, hG1, hG2⟩ := ex16G3F_hasFDerivAt (a.y ())
    have huniq := hF'.unique hG'
    have hp0 : p 0 = γ * (1 - 2 * a.y () 0) := by rw [hp 0, huniq, hG0]
    have hp1 : p 1 = γ * (1 - 2 * a.y () 1) := by rw [hp 1, huniq, hG1]
    have hp2 : p 2 = γ := by rw [hp 2, huniq, hG2, mul_one]
    have hp0pos : 0 < p 0 := by rw [hp0]; nlinarith
    have hp1pos : 0 < p 1 := by rw [hp1]; nlinarith
    have hp2pos : 0 < p 2 := by rw [hp2]; exact hγ
    have hclear : a.x () = ![1, 1, 0] + a.y () := by
      have := h.2.2.2
      simpa [ex16G3Economy, PrefEconomy.ofUtility] using this
    have hmax := h.2.2.1 ()
    have hxX : ∀ l, 0 ≤ a.x () l := hmax.1.1
    have hxb : p ⬝ᵥ a.x () ≤ w () := hmax.1.2
    -- the consumer buys no inputs
    have hin : ∀ l : Fin 3, l ≠ 2 → a.x () l = 0 := by
      intro l hl
      by_contra hne
      have hpos : 0 < a.x () l := lt_of_le_of_ne (hxX l) (Ne.symm hne)
      have hpl : 0 < p l := by
        fin_cases l
        · exact hp0pos
        · exact hp1pos
        · exact absurd rfl hl
      set z : Fin 3 → ℝ := a.x () - Pi.single l (a.x () l) +
        Pi.single 2 (p l * a.x () l / p 2) with hz
      have hzl : z l = 0 := by
        simp [hz, hl]
      have hz2 : z 2 = a.x () 2 + p l * a.x () l / p 2 := by
        simp [hz, Ne.symm hl]
      have hzX : ∀ m, 0 ≤ z m := fun m => by
        by_cases hm : m = l
        · rw [hm, hzl]
        · by_cases hm2 : m = 2
          · rw [hm2, hz2]
            have : 0 ≤ p l * a.x () l / p 2 :=
              div_nonneg (mul_nonneg hpl.le (hxX l)) hp2pos.le
            linarith [hxX 2]
          · simp [hz, hm, hm2, hxX m]
      have hcost : p ⬝ᵥ z = p ⬝ᵥ a.x () := by
        simp only [hz, dotProduct_add, dotProduct_sub, dotProduct_single]
        field_simp
        ring
      have := hmax.2 z ⟨hzX, by rw [hcost]; exact hxb⟩
      change z 2 ≤ a.x () 2 at this
      rw [hz2] at this
      have : 0 < p l * a.x () l / p 2 := div_pos (mul_pos hpl hpos) hp2pos
      linarith
    have hx0 := hin 0 (by decide)
    have hx1 := hin 1 (by decide)
    have hya0 : a.y () 0 = -1 := by
      have := congrFun hclear 0; simp at this; linarith
    have hya1 : a.y () 1 = -1 := by
      have := congrFun hclear 1; simp at this; linarith
    have hya2 : a.y () 2 = 4 := by
      simp only [ex16G3F, hya0, hya1] at hF0; linarith
    have hyeq : a.y () = ![-1, -1, 4] := by
      funext l; fin_cases l
      · simpa using hya0
      · simpa using hya1
      · simpa using hya2
    refine ⟨?_, hyeq, γ, hγ, ?_⟩
    · rw [hclear, hyeq]
      funext l; fin_cases l <;> norm_num
    · funext l
      fin_cases l
      · simp [hp0, hya0]; norm_num
      · simp [hp1, hya1]; norm_num
      · simp [hp2]

/-! ## Exercise 16.G.4 -/

/-- **Exercise 16.G.4** (MWG, p. 576). With a single consumer and the assumptions of Section 16.F
(quasiconcave utility; no convexity of production), if the set of feasible allocations is
nonempty and compact, there is an optimum, and it is a marginal cost price equilibrium. -/
theorem exercise_16_G_4 {L : ℕ} {κ : Type*} [Fintype κ] [Nonempty κ] (hL : 0 < L)
    {u : Unit → (Fin L → ℝ) → ℝ} {u' : Unit → (Fin L → ℝ) → (Fin L → ℝ) →L[ℝ] ℝ}
    {F : κ → (Fin L → ℝ) → ℝ} {F' : κ → (Fin L → ℝ) → (Fin L → ℝ) →L[ℝ] ℝ} {ω : Fin L → ℝ}
    (hu : ∀ i x, HasFDerivAt (u i) (u' i x) x) (hupos : ∀ i x l, 0 < u' i x (Pi.single l 1))
    (hF : ∀ j y, HasFDerivAt (F j) (F' j y) y) (hFpos : ∀ j y l, 0 < F' j y (Pi.single l 1))
    (hq : ∀ i, QuasiconcaveOn ℝ (nonnegOrthant L) (u i))
    (hA : IsCompact (economy16F u F ω).feasiblePairs)
    (hne : (economy16F u F ω).feasiblePairs.Nonempty) :
    ∃ a : Allocation Unit κ L, (economy16F u F ω).IsParetoOptimal a ∧
      ∃ p, StrictlyPositive p ∧ (economy16F u F ω).IsMCPriceEqm F a p (fun i => p ⬝ᵥ a.x i) := by
  have hcont : ContinuousOn (fun z : (Unit → Fin L → ℝ) × (κ → Fin L → ℝ) => u () (z.1 ()))
      (economy16F u F ω).feasiblePairs := by
    have : Continuous (u ()) := continuous_iff_continuousAt.mpr fun x => (hu () x).continuousAt
    exact (this.comp ((continuous_apply ()).comp continuous_fst)).continuousOn
  obtain ⟨z, hz, hmax⟩ := hA.exists_isMaxOn hne hcont
  have hpo : (economy16F u F ω).IsParetoOptimal ⟨z.1, z.2⟩ := by
    refine ⟨hz, ?_⟩
    rintro ⟨a', ha', -, k, hk⟩
    have h1 : u () (a'.x ()) ≤ u () (z.1 ()) := hmax (show (a'.x, a'.y) ∈ _ from ha')
    exact hk.2 h1
  exact ⟨_, hpo, proposition_16_G_1 hL hu hupos hF hFpos hq () hpo⟩

/-- The utility and technologies of `noOptimumEconomy`: `u(x) = x₁ + x₂`,
`F₁(y) = y₁ + 2y₂`, `F₂(y) = 2y₁ + y₂`. -/
def noOptimumF : Fin 2 → (Fin 2 → ℝ) → ℝ := ![fun y => y 0 + 2 * y 1, fun y => 2 * y 0 + y 1]

/-- **Exercise 16.G.4** (MWG, p. 576), correction 5: the assumptions of Section 16.F do not
guarantee an optimum. With one consumer, `u(x) = x₁ + x₂`, two firms `F₁(y) = y₁ + 2y₂`,
`F₂(y) = 2y₁ + y₂` (gradients `≫ 0`, `Fⱼ(0) = 0`) and `ω̄ = 0`, the plans `(2, -1)` and `(-1, 2)`
together produce `(1, 1)` from nothing, so no feasible allocation is Pareto optimal (and there is
no marginal cost price equilibrium that is an optimum). -/
theorem exercise_16_G_4_needs_optimum :
    (∀ j y, ∃ F' : (Fin 2 → ℝ) →L[ℝ] ℝ, HasFDerivAt (noOptimumF j) F' y ∧
      ∀ l, 0 < F' (Pi.single l 1)) ∧ (∀ j, noOptimumF j 0 = 0) ∧
    ∀ a : Allocation Unit (Fin 2) 2,
      ¬ (economy16F (fun _ x => x 0 + x 1) noOptimumF 0).IsParetoOptimal a := by
  refine ⟨fun j y => ?_, fun j => by fin_cases j <;> simp [noOptimumF], fun a hpo => ?_⟩
  · have h0 := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0).hasFDerivAt (x := y)
    have h1 := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1).hasFDerivAt (x := y)
    fin_cases j
    · refine ⟨_, (h0.add (h1.const_smul (2 : ℝ))).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun z => ?_), fun l => ?_⟩
      · simp [noOptimumF]
      · fin_cases l <;> simp
    · refine ⟨_, ((h0.const_smul (2 : ℝ)).add h1).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun z => ?_), fun l => ?_⟩
      · simp [noOptimumF]
      · fin_cases l <;> simp
  obtain ⟨⟨hx, hy⟩, hc⟩ := hpo.1
  apply hpo.2
  refine ⟨⟨fun _ => a.x () + ![1, 1], ![a.y 0 + ![2, -1], a.y 1 + ![-1, 2]]⟩,
    ⟨⟨fun _ l => ?_, fun j => ?_⟩, ?_⟩, fun _ => ?_, (), ?_⟩
  · have := hx () l; fin_cases l <;> simp at this ⊢ <;> linarith
  · have := hy j
    fin_cases j <;>
      simp [economy16F, PrefEconomy.ofUtility, noOptimumF, Matrix.vecHead, Matrix.vecTail]
        at this ⊢ <;>
      linarith
  · have := hc
    simp only [economy16F, PrefEconomy.ofUtility] at this ⊢
    rw [Fin.sum_univ_two] at this ⊢
    funext l
    have := congrFun this l
    fin_cases l <;> simp [Matrix.vecHead, Matrix.vecTail] at this ⊢ <;> linarith
  · simp only [economy16F, PrefEconomy.ofUtility, utilityPref]
    simp; linarith
  · simp only [economy16F, PrefEconomy.ofUtility, utilityPref, Strict]
    simp; constructor <;> linarith

end MWG.WelfareTheorems
