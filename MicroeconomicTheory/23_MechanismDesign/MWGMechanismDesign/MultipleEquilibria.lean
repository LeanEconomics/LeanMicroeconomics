/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGMechanismDesign.ExpectedExternality

/-!
# Two-type beliefs and Example 23.AA.1

MWG, Appendix A, pp. 911-912, Example 23.AA.1 (multiple equilibria in the expected externality
mechanism), with Section 23.D's expected externality mechanism.

Two agents decide on a public project (`k = true` done); each has valuation `θ_L` (type
`false`) or `θ_H` (type `true`) with `θ_H > 0 > θ_L`, `θ_L + θ_H > 0`, independently with
`Prob(θᵢ = θ_L) = λ ∈ (0, 1)`. The project is done unless both valuations are `θ_L`.

* `example_23_AA_1_truth`: truth telling is a Bayesian Nash equilibrium of the expected
  externality mechanism (any `hᵢ(θ₋ᵢ)`).
* **Correction.** MWG claim that "both agents always announce `θ_H`" is a second Bayesian Nash
  equilibrium. It is not: against an opponent who always announces `θ_H`, announcing `θ_L`
  raises the expected transfer by `-λθ_L > 0` and leaves the (certain) project unchanged
  (`example_23_AA_1_alwaysHigh_not_BNE`); MWG's comparison of the expected transfers
  `(λθ_L + (1-λ)θ_H) + hᵢ(θ_H)` and `(1-λ)θ_H + hᵢ(θ_H)` has the wrong sign. In fact truth
  telling is the unique pure strategy Bayesian Nash equilibrium of this mechanism
  (`example_23_AA_1_unique`).
-/

namespace MWG.MechanismDesign

open Function MeasureTheory Finset

/-- The two-point distribution on `Bool` with `Prob(false) = λ`. -/
noncomputable def bern (lam : ℝ) : Measure Bool :=
  ENNReal.ofReal lam • Measure.dirac false + ENNReal.ofReal (1 - lam) • Measure.dirac true

/-- `bern λ` is a probability measure for `λ ∈ [0, 1]`. -/
theorem bern_isProb {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) : IsProbabilityMeasure (bern lam) :=
  ⟨by
    simp only [bern, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
      measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add h0 (by linarith)]
    simp⟩

/-- Expectations under `bern λ`. -/
theorem integral_bern (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (g : Bool → ℝ) :
    ∫ x, g x ∂bern lam = lam * g false + (1 - lam) * g true := by
  have hi : ∀ (c : ENNReal) (b : Bool), c ≠ ⊤ → Integrable g (c • Measure.dirac b) :=
    fun c b hc => (integrable_dirac (by simp)).smul_measure hc
  rw [bern, integral_add_measure (hi _ _ ENNReal.ofReal_ne_top) (hi _ _ ENNReal.ofReal_ne_top),
    integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac,
    ENNReal.toReal_ofReal h0, ENNReal.toReal_ofReal (by linarith)]
  simp [smul_eq_mul]

/-- The valuation of type `b`: `θ_H` for `true`, `θ_L` for `false`. -/
def typeVal (θL θH : ℝ) : Bool → ℝ := fun b => if b then θH else θL

/-- Example 23.AA.1's valuations `vᵢ(k, θᵢ) = θᵢk`. -/
def aaV (θL θH : ℝ) : Fin 2 → Bool → Bool → ℝ := fun _ k b => if k then typeVal θL θH b else 0

/-- Example 23.AA.1's efficient project rule: done unless both valuations are `θ_L`. -/
def aaK (θ : Fin 2 → Bool) : Bool := θ 0 || θ 1

/-- The project rule of Example 23.AA.1 satisfies (23.D.6) when `θ_L < 0` and `θ_L + θ_H > 0`. -/
theorem aaK_efficient {θL θH : ℝ} (hL : θL < 0) (hLH : 0 < θL + θH) :
    EfficientProject (Θ := fun _ => Bool) (aaV θL θH) aaK := by
  intro θ k'
  simp only [Fin.sum_univ_two, aaV, aaK, typeVal]
  obtain ⟨b0, hb0⟩ : ∃ b : Bool, θ 0 = b := ⟨_, rfl⟩
  obtain ⟨b1, hb1⟩ : ∃ b : Bool, θ 1 = b := ⟨_, rfl⟩
  simp only [hb0, hb1]
  cases b0 <;> cases b1 <;> cases k' <;> simp <;> linarith

/-- The two-agent profile `(a, x)` for agent `0` and `(x, a)` for agent `1`. -/
theorem update_fin_two (θ' : Fin 2 → Bool) (i : Fin 2) (a : Bool) :
    update θ' i a = if i = 0 then ![a, θ' 1] else ![θ' 0, a] := by
  funext j
  fin_cases i <;> fin_cases j <;> simp

/-- The prior of Example 23.AA.1. -/
noncomputable def aaP (lam : ℝ) : Measure (Fin 2 → Bool) := Measure.pi fun _ => bern lam

/-- Agent `i`'s conditional expectation of a function of the profile `(a, θ₋ᵢ)` in
Example 23.AA.1. -/
theorem integral_aaP (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (i : Fin 2) (a : Bool)
    (G : (Fin 2 → Bool) → ℝ) :
    ∫ θ', G (update θ' i a) ∂aaP lam =
      lam * G (update ![false, false] i a) + (1 - lam) * G (update ![true, true] i a) := by
  have := bern_isProb h0 h1
  set c : Fin 2 := if i = 0 then 1 else 0
  have hG : (fun θ' => G (update θ' i a)) =
      fun θ' => (fun x => G (update ![x, x] i a)) (θ' c) := by
    funext θ'
    congr 1
    funext j
    fin_cases i <;> fin_cases j <;> simp [c]
  rw [hG, aaP]
  exact (integral_comp_eval (μ := fun _ : Fin 2 => bern lam) (i := c)
    (f := fun x => G (update ![x, x] i a)) (by fun_prop)).trans (integral_bern lam h0 h1 _)

/-- The other agent. -/
def other (i : Fin 2) : Fin 2 := if i = 0 then 1 else 0

/-- The expected externality `ξᵢ(a)` in Example 23.AA.1: `ξᵢ(θ_L) = (1-λ)θ_H` and
`ξᵢ(θ_H) = λθ_L + (1-λ)θ_H`. -/
theorem xi_aa (lam θL θH : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (i : Fin 2) (a : Bool) :
    expectedExternality (aaP lam) (aaV θL θH) aaK i a =
      lam * (if a then θL else 0) + (1 - lam) * θH := by
  have e : (fun θ' : Fin 2 → Bool => ∑ j ∈ univ.erase i, aaV θL θH j (aaK (update θ' i a)) (θ' j))
      = fun θ' => (fun σ : Fin 2 → Bool => ∑ j ∈ univ.erase i, aaV θL θH j (aaK σ) (σ j))
        (update θ' i a) := by
    funext θ'
    exact sum_congr rfl fun j hj => by rw [update_of_ne (ne_of_mem_erase hj)]
  unfold expectedExternality
  rw [e, integral_aaP lam h0 h1 i a
    (fun σ : Fin 2 → Bool => ∑ j ∈ univ.erase i, aaV θL θH j (aaK σ) (σ j))]
  fin_cases i <;> cases a <;> simp [aaV, aaK, typeVal, sum_erase_eq_sub, Fin.sum_univ_two]

/-- The direct mechanism of Example 23.AA.1: the efficient project with the expected externality
transfers `ξᵢ(θᵢ) + hᵢ(θ₋ᵢ)`. -/
noncomputable def aaMech (lam θL θH : ℝ) (h : Fin 2 → (Fin 2 → Bool) → ℝ) :
    Mechanism (fun _ : Fin 2 => Bool) (Bool × (Fin 2 → ℝ)) :=
  directMechanism (Θ := fun _ => Bool)
    fun θ => (aaK θ, agvTransfer (aaP lam) (aaV θL θH) aaK h θ)

/-- Agent `i`'s gain from announcing `θ_H` rather than `θ_L` in Example 23.AA.1, when the other
agent uses the strategy `s_j`: `θᵢ(1 - q) + λθ_L`, with `q` the probability that the other
announces `θ_H`. -/
theorem aa_gain (lam θL θH : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    {h : Fin 2 → (Fin 2 → Bool) → ℝ} (hh : IndepOwn (Θ := fun _ => Bool) h)
    (s : Fin 2 → Bool → Bool) (i : Fin 2) (θi : Bool) :
    interimUtility (indepBeliefs (aaP lam)) (qlU (aaV θL θH) 0) (aaMech lam θL θH h) s i θi true -
      interimUtility (indepBeliefs (aaP lam)) (qlU (aaV θL θH) 0) (aaMech lam θL θH h) s i θi
        false =
      typeVal θL θH θi * (lam * (if s (other i) false then 0 else 1) +
        (1 - lam) * (if s (other i) true then 0 else 1)) + lam * θL := by
  have hform : ∀ a, interimUtility (indepBeliefs (aaP lam)) (qlU (aaV θL θH) 0)
      (aaMech lam θL θH h) s i θi a =
      lam * (fun σ : Fin 2 → Bool => qlU (aaV θL θH) 0 i (aaK (update (play s σ) i a),
        agvTransfer (aaP lam) (aaV θL θH) aaK h (update (play s σ) i a)) θi)
          (update ![false, false] i a) +
      (1 - lam) * (fun σ : Fin 2 → Bool => qlU (aaV θL θH) 0 i (aaK (update (play s σ) i a),
        agvTransfer (aaP lam) (aaV θL θH) aaK h (update (play s σ) i a)) θi)
          (update ![true, true] i a) := by
    intro a
    rw [← integral_aaP lam h0 h1 i a (fun σ : Fin 2 → Bool => qlU (aaV θL θH) 0 i
      (aaK (update (play s σ) i a), agvTransfer (aaP lam) (aaV θL θH) aaK h
        (update (play s σ) i a)) θi)]
    unfold interimUtility indepBeliefs aaMech directMechanism
    congr 1
    funext θ'
    have : update (play s (update θ' i a)) i a = update (play s θ') i a := by
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [play, update_of_ne hj]
    simp only [this]
  rw [hform true, hform false]
  simp only [qlU, agvTransfer, update_self, Pi.zero_apply, xi_aa lam θL θH h0 h1]
  have hcancel : ∀ b : Bool, h i (update (play s (update ![b, b] i true)) i true) =
      h i (update (play s (update ![b, b] i false)) i false) := by
    intro b
    have e : update (play s (update ![b, b] i true)) i true =
        update (update (play s (update ![b, b] i false)) i false) i true := by
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [play, update_of_ne hj]
    rw [e, hh]
  rw [hcancel false, hcancel true]
  fin_cases i <;> cases θi <;> cases h0' : s 0 false <;> cases h1' : s 0 true <;>
    cases h2' : s 1 false <;> cases h3' : s 1 true <;>
    simp [aaV, aaK, typeVal, other, play, h0', h1', h2', h3'] <;> ring

/-- **Example 23.AA.1** (MWG, pp. 911-912). Truth telling is a Bayesian Nash equilibrium of the
expected externality mechanism (Section 23.D), for any `hᵢ(θ₋ᵢ)`. -/
theorem example_23_AA_1_truth {lam θL θH : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (hL : θL < 0)
    (hLH : 0 < θL + θH) {h : Fin 2 → (Fin 2 → Bool) → ℝ}
    (hh : IndepOwn (Θ := fun _ => Bool) h) :
    IsBayesianNash (indepBeliefs (aaP lam)) (qlU (aaV θL θH) 0) (aaMech lam θL θH h)
      truthful := by
  have : IsProbabilityMeasure (bern lam) := bern_isProb h0 h1
  have hP : IsProbabilityMeasure (aaP lam) := by unfold aaP; infer_instance
  exact agv_bayesianIC (aaP lam) 0 (aaK_efficient hL hLH) hh
    (fun _ _ _ _ => Integrable.of_finite) fun _ => Integrable.of_finite

/-- **Example 23.AA.1**, correction (MWG, p. 912). "Both agents always announce `θ_H`" is *not* a
Bayesian Nash equilibrium of the expected externality mechanism: against it, announcing `θ_L`
gains `-λθ_L > 0`. -/
theorem example_23_AA_1_alwaysHigh_not_BNE {lam θL θH : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1)
    (hL : θL < 0) {h : Fin 2 → (Fin 2 → Bool) → ℝ} (hh : IndepOwn (Θ := fun _ => Bool) h) :
    ¬IsBayesianNash (indepBeliefs (aaP lam)) (qlU (aaV θL θH) 0) (aaMech lam θL θH h)
      (fun _ _ => true) := by
  intro hB
  have hg := aa_gain lam θL θH h0.le h1 hh (fun _ _ => true) 0 false
  have := hB 0 false false
  simp only [ite_true, mul_zero, add_zero, zero_add] at hg
  have : lam * θL < 0 := mul_neg_of_pos_of_neg h0 hL
  linarith

/-- **Example 23.AA.1**, correction (MWG, p. 912). Truth telling is the *unique* pure strategy
Bayesian Nash equilibrium of the expected externality mechanism in this example (for
`λ ∈ (0, 1)`, `θ_L < 0`, `θ_L + θ_H > 0` and any `hᵢ(θ₋ᵢ)`). -/
theorem example_23_AA_1_unique {lam θL θH : ℝ} (h0 : 0 < lam) (h1 : lam < 1) (hL : θL < 0)
    (hLH : 0 < θL + θH) {h : Fin 2 → (Fin 2 → Bool) → ℝ}
    (hh : IndepOwn (Θ := fun _ => Bool) h) (s : Fin 2 → Bool → Bool)
    (hB : IsBayesianNash (indepBeliefs (aaP lam)) (qlU (aaV θL θH) 0) (aaMech lam θL θH h) s) :
    s = truthful := by
  -- low types announce `θ_L`
  have hlow : ∀ i, s i false = false := by
    intro i
    by_contra hne
    have hs : s i false = true := by simpa using hne
    have hg := aa_gain lam θL θH h0.le h1.le hh s i false
    have hdev := hB i false false
    rw [hs] at hdev
    simp only [typeVal, Bool.false_eq_true, ite_false] at hg
    have hq : 0 ≤ lam * (if s (other i) false then 0 else 1) +
        (1 - lam) * (if s (other i) true then (0 : ℝ) else 1) := by
      split_ifs <;> nlinarith
    have : θL * (lam * (if s (other i) false then 0 else 1) +
        (1 - lam) * (if s (other i) true then (0 : ℝ) else 1)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hL.le hq
    have : lam * θL < 0 := mul_neg_of_pos_of_neg h0 hL
    linarith
  -- high types announce `θ_H`
  have hhigh : ∀ i, s i true = true := by
    intro i
    by_contra hne
    have hs : s i true = false := by simpa using hne
    have hg := aa_gain lam θL θH h0.le h1.le hh s i true
    have hdev := hB i true true
    rw [hs] at hdev
    rw [hlow (other i)] at hg
    simp only [typeVal, Bool.false_eq_true, ite_true, ite_false, mul_one] at hg
    have hq : 0 ≤ (1 - lam) * (if s (other i) true then (0 : ℝ) else 1) := by
      split_ifs <;> nlinarith
    have hH : 0 < θH := by linarith
    have : 0 ≤ θH * ((1 - lam) * (if s (other i) true then (0 : ℝ) else 1)) :=
      mul_nonneg hH.le hq
    nlinarith
  funext i b
  cases b
  · exact hlow i
  · exact hhigh i

end MWG.MechanismDesign
