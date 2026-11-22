/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGWelfareTheorems.MCExamples

/-!
# Interpretations of the commodity space (MWG Section 16.G, pp. 566-570)

* **Example 16.G.1** (contingent commodities), footnote 20: with `I` consumers who may each be
  sick or healthy there are `2^I` states, and a consumer buying medical care when sick buys
  `2^{I-1}` contingent commodities.
* **Example 16.G.2** (occupational choice): the consumption set
  `Xᵢ = {(cᵢ, t_{ci}, t_{ei}) : cᵢ ≥ 0, t_{ci} ≤ 0, t_{ei} ≤ 0, T̄ᵢ + t_{ei} + αᵢ t_{ci} ≥ 0}` is
  nonempty, closed and convex; a preference increasing in consumption is locally nonsatiated on
  it; the production set of a concave production function is convex. So the first welfare theorem
  applies to every price equilibrium with transfers of such an economy.
* **Example 16.G.3** (public goods), **Definition 16.G.1** (Lindahl equilibrium). As printed, the
  wealth condition `∑ᵢ wᵢ = ∑ᵢ p₁x*₁ᵢ + (∑ᵢ p₂ᵢ)q* - p₁z*` is not the condition
  `∑ᵢ wᵢ = p·ω̄ + p·y*` of a price equilibrium with transfers of the artificial economy, which reads
  `∑ᵢ wᵢ = p₁ω̄₁ + (∑ᵢ p₂ᵢ)q* - p₁z*` (correction 6): with the printed condition and locally
  nonsatiated consumers, `p₁z* = 0`; and the artificial economy's equilibrium of
  `definition_16_G_1_printed_counterexample` satisfies the corrected but not the printed
  definition. With the corrected definition, every Lindahl equilibrium is Pareto optimal (the
  first welfare theorem). Footnote 23: at an interior Lindahl equilibrium with differentiable
  utilities and production function, `∑ᵢ MRSᵢ = MRT` (the Samuelson condition).
-/

namespace MWG.WelfareTheorems

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.Production Kreps.PreferenceProperties
open MWG.CompetitiveMarkets (Allocation)
open Filter Topology

/-! ## Example 16.G.1: contingent commodities -/

/-- **Example 16.G.1, footnote 20** (MWG, p. 567). With `I` consumers, each sick (`true`) or
healthy (`false`), there are `2^I` states, and the states in which a given consumer is sick are
`2^{I-1}` (`I ≥ 1`): the number of contingent medical care commodities she buys. -/
theorem footnote_20 {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) :
    Fintype.card (ι → Bool) = 2 ^ Fintype.card ι ∧
      Fintype.card {s : ι → Bool // s i = true} = 2 ^ (Fintype.card ι - 1) := by
  refine ⟨by simp, ?_⟩
  have e : {s : ι → Bool // s i = true} ≃ ({k // k ≠ i} → Bool) :=
    { toFun := fun s k => s.1 k.1
      invFun := fun g => ⟨fun k => if h : k = i then true else g ⟨k, h⟩, by simp⟩
      left_inv := fun s => by
        ext k
        by_cases h : k = i
        · subst h; simp [s.2]
        · simp [h]
      right_inv := fun g => by
        funext k
        simp [k.2] }
  rw [Fintype.card_congr e, Fintype.card_fun, Fintype.card_bool, Fintype.card_subtype_compl,
    Fintype.card_subtype_eq]

/-! ## Example 16.G.2: occupational choice -/

/-- **Example 16.G.2** (MWG, p. 568). The consumption set of an individual with `T̄` professorial
hours and comparative advantage `α`: bundles `(c, t_c, t_e)` with `c ≥ 0`, `t_c ≤ 0`, `t_e ≤ 0`
and leisure `T̄ + t_e + α t_c ≥ 0`. -/
def occupationalX (T α : ℝ) : Set (Fin 3 → ℝ) :=
  {x | 0 ≤ x 0 ∧ x 1 ≤ 0 ∧ x 2 ≤ 0 ∧ 0 ≤ T + x 2 + α * x 1}

/-- **Example 16.G.2** (MWG, p. 568). The occupational consumption set is nonempty (for `T̄ ≥ 0`),
closed and convex. -/
theorem example_16_G_2_X {T α : ℝ} (hT : 0 ≤ T) :
    (0 : Fin 3 → ℝ) ∈ occupationalX T α ∧ IsClosed (occupationalX T α) ∧
      Convex ℝ (occupationalX T α) := by
  refine ⟨⟨le_rfl, le_rfl, le_rfl, by simpa using hT⟩, ?_, ?_⟩
  · have hc0 : Continuous fun x : Fin 3 → ℝ => x 0 := continuous_apply 0
    have hc1 : Continuous fun x : Fin 3 → ℝ => x 1 := continuous_apply 1
    have hc2 : Continuous fun x : Fin 3 → ℝ => x 2 := continuous_apply 2
    exact (isClosed_le continuous_const hc0).inter ((isClosed_le hc1 continuous_const).inter
      ((isClosed_le hc2 continuous_const).inter (isClosed_le continuous_const
        ((continuous_const.add hc2).add (continuous_const.mul hc1)))))
  · intro x hx y hy a b ha hb hab
    obtain ⟨hx0, hx1, hx2, hx3⟩ := hx
    obtain ⟨hy0, hy1, hy2, hy3⟩ := hy
    simp only [occupationalX, Set.mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    refine ⟨by positivity, by nlinarith, by nlinarith, ?_⟩
    have : T = a * T + b * T := by rw [← add_mul, hab, one_mul]
    nlinarith [mul_nonneg ha hx3, mul_nonneg hb hy3]

/-- **Example 16.G.2** (MWG, p. 568). "Because the consumption good is desirable, the local
nonsatiation condition is satisfied": a utility strictly increasing in consumption `c` is locally
nonsatiated on the occupational consumption set. -/
theorem example_16_G_2_lns {T α : ℝ} {u : (Fin 3 → ℝ) → ℝ}
    (hu : ∀ x ∈ occupationalX T α, ∀ c : ℝ, 0 < c → u x < u (x + Pi.single 0 c)) :
    LocallyNonsatiated (occupationalX T α) (utilityPref u) := by
  intro x hx ε hε
  refine ⟨x + Pi.single 0 ε, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · simp; linarith [hx.1]
  · simpa using hx.2.1
  · simpa using hx.2.2.1
  · simpa using hx.2.2.2
  · rw [euclidDist_add_single, abs_of_pos hε]
  · exact (hu x hx ε hε).le
  · exact not_le.mpr (hu x hx ε hε)

/-- **Example 16.G.2** (MWG, p. 568). The production set
`{(q, -z_c, -z_e) : z ≥ 0, q ≤ f(z_c, z_e)}` of a concave production function is convex. -/
theorem example_16_G_2_Y {f : ℝ → ℝ → ℝ}
    (hf : ConcaveOn ℝ {z : Fin 2 → ℝ | ∀ l, 0 ≤ z l} (fun z => f (z 0) (z 1))) :
    Convex ℝ {y : Fin 3 → ℝ | y 1 ≤ 0 ∧ y 2 ≤ 0 ∧ y 0 ≤ f (-y 1) (-y 2)} := by
  intro x hx y hy a b ha hb hab
  obtain ⟨hx1, hx2, hx3⟩ := hx
  obtain ⟨hy1, hy2, hy3⟩ := hy
  simp only [Set.mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  refine ⟨by nlinarith, by nlinarith, ?_⟩
  have hzx : (![-x 1, -x 2] : Fin 2 → ℝ) ∈ {z : Fin 2 → ℝ | ∀ l, 0 ≤ z l} := fun l => by
    fin_cases l <;> simp <;> linarith
  have hzy : (![-y 1, -y 2] : Fin 2 → ℝ) ∈ {z : Fin 2 → ℝ | ∀ l, 0 ≤ z l} := fun l => by
    fin_cases l <;> simp <;> linarith
  have := hf.2 hzx hzy ha hb hab
  simp only [smul_eq_mul, Pi.add_apply, Pi.smul_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one] at this
  have e1 : -(a * x 1 + b * y 1) = a * -x 1 + b * -y 1 := by ring
  have e2 : -(a * x 2 + b * y 2) = a * -x 2 + b * -y 2 := by ring
  rw [e1, e2]
  nlinarith [mul_le_mul_of_nonneg_left hx3 ha, mul_le_mul_of_nonneg_left hy3 hb]

/-! ## Example 16.G.3: public goods and Lindahl equilibrium -/

variable {ι : Type*} [Fintype ι]

/-- **Example 16.G.3** (MWG, p. 569). A feasible allocation of the public goods economy: private
consumptions `x₁ᵢ ≥ 0`, public good `q ≥ 0`, input `z ≥ 0` with `q ≤ f(z)` and
`∑ᵢ x₁ᵢ + z = ω̄₁`. Consumer `i` consumes the pair `(x₁ᵢ, q)`. -/
def PublicFeasible (ω₁ : ℝ) (f : ℝ → ℝ) (x : ι → ℝ) (q z : ℝ) : Prop :=
  (∀ i, 0 ≤ x i) ∧ 0 ≤ q ∧ 0 ≤ z ∧ q ≤ f z ∧ ∑ i, x i + z = ω₁

/-- **Example 16.G.3** (MWG, p. 569). Pareto optimality in the public goods economy, for
preferences `≿ᵢ` on pairs `(x₁ᵢ, x₂)`. -/
def PublicParetoOptimal (pref : ι → (Fin 2 → ℝ) → (Fin 2 → ℝ) → Prop) (ω₁ : ℝ)
    (f : ℝ → ℝ) (x : ι → ℝ) (q z : ℝ) : Prop :=
  PublicFeasible ω₁ f x q z ∧ ¬ ∃ x' q' z', PublicFeasible ω₁ f x' q' z' ∧
    (∀ i, pref i ![x' i, q'] ![x i, q]) ∧ ∃ i, Strict (pref i) ![x' i, q'] ![x i, q]

/-- **Definition 16.G.1** (MWG, pp. 569-570), corrected (correction 6). A Lindahl equilibrium (with
transfers): wealth levels with `∑ᵢ wᵢ = p₁ω̄₁ + (∑ᵢ p₂ᵢ)q* - p₁z*` (the condition
`∑ᵢ wᵢ = p·ω̄ + p·y*` of the artificial economy), (i) `q* ≤ f(z*)`, `z* ≥ 0` and profit
maximization at the personalized prices, (ii) every `(x*₁ᵢ, q*)` maximal in
`{(x₁ᵢ, x₂ᵢ) ≥ 0 : p₁x₁ᵢ + p₂ᵢx₂ᵢ ≤ wᵢ}`, (iii) `∑ᵢ x*₁ᵢ + z* = ω̄₁` (and `x*₂ᵢ = q*`). -/
def IsLindahlEqm (pref : ι → (Fin 2 → ℝ) → (Fin 2 → ℝ) → Prop) (ω₁ : ℝ) (f : ℝ → ℝ)
    (x : ι → ℝ) (q z p₁ : ℝ) (p₂ w : ι → ℝ) : Prop :=
  ∑ i, w i = p₁ * ω₁ + (∑ i, p₂ i) * q - p₁ * z ∧
    (q ≤ f z ∧ 0 ≤ z ∧ ∀ q' z', 0 ≤ z' → q' ≤ f z' →
      (∑ i, p₂ i) * q' - p₁ * z' ≤ (∑ i, p₂ i) * q - p₁ * z) ∧
    (∀ i, IsMaximalFor (pref i) {v | (∀ l, 0 ≤ v l) ∧ p₁ * v 0 + p₂ i * v 1 ≤ w i}
      ![x i, q]) ∧
    ∑ i, x i + z = ω₁

/-- **Definition 16.G.1** (MWG, pp. 569-570) as printed: the wealth condition reads
`∑ᵢ wᵢ = ∑ᵢ p₁x*₁ᵢ + (∑ᵢ p₂ᵢ)q* - p₁z*`. -/
def IsLindahlEqmPrinted (pref : ι → (Fin 2 → ℝ) → (Fin 2 → ℝ) → Prop) (ω₁ : ℝ) (f : ℝ → ℝ)
    (x : ι → ℝ) (q z p₁ : ℝ) (p₂ w : ι → ℝ) : Prop :=
  ∑ i, w i = ∑ i, p₁ * x i + (∑ i, p₂ i) * q - p₁ * z ∧
    (q ≤ f z ∧ 0 ≤ z ∧ ∀ q' z', 0 ≤ z' → q' ≤ f z' →
      (∑ i, p₂ i) * q' - p₁ * z' ≤ (∑ i, p₂ i) * q - p₁ * z) ∧
    (∀ i, IsMaximalFor (pref i) {v | (∀ l, 0 ≤ v l) ∧ p₁ * v 0 + p₂ i * v 1 ≤ w i}
      ![x i, q]) ∧
    ∑ i, x i + z = ω₁

/-- **Definition 16.G.1**, correction 6. Given market clearing, the printed wealth condition is
the corrected one minus `p₁z*`: the two agree only when `p₁z* = 0`. -/
theorem definition_16_G_1_wealth_gap {ω₁ p₁ q z : ℝ} {x p₂ : ι → ℝ}
    (hc : ∑ i, x i + z = ω₁) :
    ∑ i, p₁ * x i + (∑ i, p₂ i) * q - p₁ * z =
      (p₁ * ω₁ + (∑ i, p₂ i) * q - p₁ * z) - p₁ * z := by
  rw [← Finset.mul_sum, ← hc]
  ring

/-- **Definition 16.G.1**, correction 6. Under the printed definition, if every consumer is locally
nonsatiated (on `ℝ²₊`, transitive preferences), then `p₁z* = 0`: the printed definition excludes
every equilibrium that uses a positive amount of a valued input. -/
theorem definition_16_G_1_printed_forces {pref : ι → (Fin 2 → ℝ) → (Fin 2 → ℝ) → Prop}
    (hlns : ∀ i, LocallyNonsatiated (nonnegOrthant 2) (pref i)) {ω₁ : ℝ} {f : ℝ → ℝ}
    {x : ι → ℝ} {q z p₁ : ℝ} {p₂ w : ι → ℝ}
    (h : IsLindahlEqmPrinted pref ω₁ f x q z p₁ p₂ w) : p₁ * z = 0 := by
  -- every consumer spends her wealth
  have hspend : ∀ i, p₁ * x i + p₂ i * q = w i := by
    intro i
    have hmax := h.2.2.1 i
    refine le_antisymm hmax.1.2 ?_
    by_contra hlt
    push Not at hlt
    have hmem : (![x i, q] : Fin 2 → ℝ) ∈ nonnegOrthant 2 := fun l => hmax.1.1 l
    have hpd : (![p₁, p₂ i] : Fin 2 → ℝ) ⬝ᵥ ![x i, q] < w i := by
      rw [dot_two]; simpa using hlt
    obtain ⟨v, hv, hpv, hs⟩ := lns_exists_better_cheaper (hlns i) _ hmem hpd
    rw [dot_two] at hpv
    exact hs.2 (hmax.2 v ⟨hv, by simpa using hpv.le⟩)
  have h1 := h.1
  have h2 : ∑ i, w i = ∑ i, p₁ * x i + (∑ i, p₂ i) * q := by
    rw [← Finset.sum_congr rfl fun i _ => hspend i, Finset.sum_add_distrib, Finset.sum_mul]
  linarith

/-- The utility `u(x₁, x₂) = x₁ + x₂` of the one-consumer example. -/
def lindahlExampleU : (Fin 2 → ℝ) → ℝ := fun v => v 0 + v 1

/-- **Definition 16.G.1**, correction 6. One consumer with `u = x₁ + x₂`, `ω̄₁ = 1`, `f(z) = z`:
`x*₁ = q* = z* = 1/2`, `p₁ = p₂ = 1`, `w = 1` is a Lindahl equilibrium (the price equilibrium of the
artificial economy), but there is no wealth level for which it satisfies the printed
definition. -/
theorem definition_16_G_1_printed_counterexample :
    IsLindahlEqm (fun _ : Unit => utilityPref lindahlExampleU) 1 id (fun _ => 1 / 2) (1 / 2)
        (1 / 2) 1 (fun _ => 1) (fun _ => 1) ∧
      ∀ w, ¬ IsLindahlEqmPrinted (fun _ : Unit => utilityPref lindahlExampleU) 1 id
        (fun _ => 1 / 2) (1 / 2) (1 / 2) 1 (fun _ => 1) w := by
  refine ⟨⟨by norm_num, ⟨by simp, by norm_num, fun q' z' _ hq => ?_⟩, fun _ => ⟨⟨fun l => ?_,
    by norm_num⟩, fun v hv => ?_⟩, by norm_num⟩, fun w h => ?_⟩
  · simp only [Finset.univ_unique, Finset.sum_singleton, id] at hq ⊢
    linarith
  · fin_cases l <;> norm_num
  · change v 0 + v 1 ≤ (![1 / 2, 1 / 2] : Fin 2 → ℝ) 0 + (![1 / 2, 1 / 2] : Fin 2 → ℝ) 1
    have := hv.2
    norm_num at this ⊢
    linarith
  · have h1 := h.1
    have h2 := (h.2.2.1 ()).1.2
    simp only [Finset.univ_unique, Finset.sum_singleton] at h1 h2
    norm_num at h1 h2
    linarith

/-- **Example 16.G.3** (MWG, p. 570): "every Lindahl equilibrium is Pareto optimal". With locally
nonsatiated, transitive preferences on `ℝ²₊`, every Lindahl equilibrium (Definition 16.G.1,
corrected) is a Pareto optimum of the public goods economy. -/
theorem lindahl_isParetoOptimal {pref : ι → (Fin 2 → ℝ) → (Fin 2 → ℝ) → Prop}
    (hr : ∀ i, RationalOn (nonnegOrthant 2) (pref i))
    (hlns : ∀ i, LocallyNonsatiated (nonnegOrthant 2) (pref i)) {ω₁ : ℝ} {f : ℝ → ℝ}
    {x : ι → ℝ} {q z p₁ : ℝ} {p₂ w : ι → ℝ} [Nonempty ι]
    (h : IsLindahlEqm pref ω₁ f x q z p₁ p₂ w) : PublicParetoOptimal pref ω₁ f x q z := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hmax := h.2.2.1
  have hbud : ∀ i v, v ∈ nonnegOrthant 2 → p₁ * v 0 + p₂ i * v 1 =
      (![p₁, p₂ i] : Fin 2 → ℝ) ⬝ᵥ v := fun i v _ => by rw [dot_two]; simp
  have hfeas : PublicFeasible ω₁ f x q z :=
    ⟨fun i => by simpa using (hmax i).1.1 0, by simpa using (hmax i₀).1.1 1, h.2.1.2.1,
      h.2.1.1, h.2.2.2⟩
  refine ⟨hfeas, ?_⟩
  rintro ⟨x', q', z', ⟨hx', hq', hz', hf', hc'⟩, hle, k, hk⟩
  -- the budget-set form of (16.C.1)-(16.C.2) for each consumer
  have hX : ∀ i, (![x' i, q'] : Fin 2 → ℝ) ∈ nonnegOrthant 2 := fun i l => by
    fin_cases l
    · simpa using hx' i
    · simpa using hq'
  have hbudget : ∀ i, budgetSetOn (nonnegOrthant 2) ![p₁, p₂ i] (w i) =
      {v | (∀ l, 0 ≤ v l) ∧ p₁ * v 0 + p₂ i * v 1 ≤ w i} := fun i => by
    ext v
    simp only [budgetSetOn, Set.mem_ofPred_eq, dot_two, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    rfl
  have hge : ∀ i, w i ≤ p₁ * x' i + p₂ i * q' := fun i => by
    have := exercise_16_C_2 (hlns i) (hr i).2 (by rw [hbudget]; exact hmax i) (hX i) (hle i)
    rw [dot_two] at this
    simpa using this
  have hgt : w k < p₁ * x' k + p₂ k * q' := by
    have := equation_16_C_1 (by rw [hbudget]; exact hmax k) (hX k) hk
    rw [dot_two] at this
    simpa using this
  have h1 : ∑ i, w i < ∑ i, (p₁ * x' i + p₂ i * q') :=
    Finset.sum_lt_sum (fun i _ => hge i) ⟨k, Finset.mem_univ k, hgt⟩
  have h2 := h.2.1.2.2 q' z' hz' hf'
  have h3 : ∑ i, (p₁ * x' i + p₂ i * q') = p₁ * ω₁ - p₁ * z' + (∑ i, p₂ i) * q' := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, ← hc']
    ring
  linarith [h.1]

/-- **Footnote 23** (MWG, p. 570), the Samuelson condition. At a Lindahl equilibrium with
`p₁ > 0` and an interior input choice `z* > 0`, if `f` is differentiable at `z*` with `f'(z*) > 0`
and each consumer's utility `uᵢ`, differentiable at her interior bundle `(x*₁ᵢ, q*) ≫ 0` with
`∂uᵢ/∂x₁ > 0`, represents `≿ᵢ`, then `p₂ᵢ/p₁ = MRSᵢ = (∂uᵢ/∂x₂)/(∂uᵢ/∂x₁)` for every `i` and
`∑ᵢ p₂ᵢ/p₁ = MRT = 1/f'(z*)`; hence `∑ᵢ MRSᵢ = MRT`. -/
theorem footnote_23 {u : ι → (Fin 2 → ℝ) → ℝ} {ω₁ : ℝ} {f : ℝ → ℝ} {x : ι → ℝ}
    {q z p₁ : ℝ} {p₂ w : ι → ℝ}
    (h : IsLindahlEqm (fun i => utilityPref (u i)) ω₁ f x q z p₁ p₂ w) (hp₁ : 0 < p₁)
    {u' : ι → (Fin 2 → ℝ) →L[ℝ] ℝ} (hu : ∀ i, HasFDerivAt (u i) (u' i) ![x i, q])
    (hu1 : ∀ i, 0 < u' i (Pi.single 0 1)) (hx : ∀ i, 0 < x i) (hq : 0 < q)
    {f' : ℝ} (hf : HasDerivAt f f' z) (hf' : 0 < f') (hz : 0 < z) (hqf : q = f z) :
    (∀ i, p₂ i / p₁ = u' i (Pi.single 1 1) / u' i (Pi.single 0 1)) ∧
      ∑ i, p₂ i / p₁ = 1 / f' ∧
      ∑ i, u' i (Pi.single 1 1) / u' i (Pi.single 0 1) = 1 / f' := by
  -- the consumer's first-order condition along the budget line
  have hmrs : ∀ i, p₂ i / p₁ = u' i (Pi.single 1 1) / u' i (Pi.single 0 1) := by
    intro i
    set d : Fin 2 → ℝ := ![-(p₂ i / p₁), 1] with hd
    have hline : HasDerivAt (fun t : ℝ => u i (![x i, q] + t • d)) (u' i d) 0 := by
      have h1 : HasDerivAt (fun t : ℝ => ![x i, q] + t • d) d 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const d).const_add (![x i, q] : Fin 2 → ℝ)
      have h2 : HasFDerivAt (u i) (u' i) (![x i, q] + (0 : ℝ) • d) := by simpa using hu i
      exact h2.comp_hasDerivAt 0 h1
    -- the line stays in the budget set near `t = 0`, so `t = 0` is a local maximum
    have hloc : IsLocalMax (fun t : ℝ => u i (![x i, q] + t • d)) 0 := by
      have hcont : Continuous fun t : ℝ => (![x i, q] + t • d : Fin 2 → ℝ) := by fun_prop
      have hpos : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ l, 0 < (![x i, q] + t • d) l := by
        rw [eventually_all]
        intro l
        have := (continuous_apply l |>.comp hcont).continuousAt (x := 0)
        refine this.eventually (lt_mem_nhds ?_)
        fin_cases l
        · simpa using hx i
        · simpa using hq
      filter_upwards [hpos] with t ht
      have hmem : (![x i, q] + t • d : Fin 2 → ℝ) ∈ {v | (∀ l, 0 ≤ v l) ∧
          p₁ * v 0 + p₂ i * v 1 ≤ w i} := by
        refine ⟨fun l => (ht l).le, ?_⟩
        have hb := (h.2.2.1 i).1.2
        simp only [hd, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
          Matrix.cons_val_one] at hb ⊢
        have : p₁ * (x i + t * -(p₂ i / p₁)) + p₂ i * (q + t * 1) =
            p₁ * x i + p₂ i * q := by field_simp; ring
        linarith
      have h3 : u i (![x i, q] + t • d) ≤ u i ![x i, q] := (h.2.2.1 i).2 _ hmem
      simpa using h3
    have hzero := hloc.hasDerivAt_eq_zero hline
    have hlin : u' i d = -(p₂ i / p₁) * u' i (Pi.single 0 1) + u' i (Pi.single 1 1) := by
      rw [clm_apply_eq_sum_partials, Fin.sum_univ_two]
      simp [hd]
      ring
    rw [hlin] at hzero
    have hu0 := hu1 i
    have e : u' i (Pi.single 1 1) = p₂ i / p₁ * u' i (Pi.single 0 1) := by linarith
    rw [e]
    field_simp
  -- the firm's first-order condition
  have hmrt : (∑ i, p₂ i) * f' = p₁ := by
    set P := ∑ i, p₂ i
    have hline : HasDerivAt (fun t : ℝ => P * f t - p₁ * t) (P * f' - p₁) z :=
      (hf.const_mul P).sub ((hasDerivAt_id z).const_mul p₁ |>.congr_deriv (by simp))
    have hloc : IsLocalMax (fun t : ℝ => P * f t - p₁ * t) z := by
      filter_upwards [lt_mem_nhds hz] with t ht
      have := h.2.1.2.2 (f t) t ht.le le_rfl
      rw [hqf] at this
      exact this
    have := hloc.hasDerivAt_eq_zero hline
    linarith
  have hsum : ∑ i, p₂ i / p₁ = 1 / f' := by
    rw [← Finset.sum_div, div_eq_div_iff hp₁.ne' hf'.ne']
    linarith
  exact ⟨hmrs, hsum, by rw [← hsum]; exact Finset.sum_congr rfl fun i _ => (hmrs i).symm⟩

end MWG.WelfareTheorems
