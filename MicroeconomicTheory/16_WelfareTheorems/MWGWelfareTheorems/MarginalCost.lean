/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGWelfareTheorems.FirstOrderWelfare

/-!
# Nonconvex production and marginal cost pricing (MWG Section 16.G, pp. 570-572)

* The marginal cost price equilibrium with transfers (conditions (i)-(iii) of Proposition 16.G.1,
  `PrefEconomy.IsMCPriceEqm`).
* **Proposition 16.G.1** (= **Exercise 16.G.1**): under the assumptions of Section 16.F (no
  convexity of production) and quasiconcave utilities, every Pareto optimum is a marginal cost
  price equilibrium with transfers, with `p ≫ 0`.
* **Exercise 16.G.2**: with one input and one output, (16.G.1) says that the input price is the
  output price times the marginal product, i.e. the output price is marginal cost.
* **Figure 16.G.1**: a Pareto optimum whose only supporting (marginal cost) prices make the firm
  incur a loss, so that shutting down is more profitable.
* **Figure 16.G.2**: a marginal cost price equilibrium that is not Pareto optimal.
-/

namespace MWG.WelfareTheorems

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.Production Kreps.PreferenceProperties
open MWG.CompetitiveMarkets (Allocation)
open Filter Topology

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {L : ℕ}

/-- **Proposition 16.G.1** (MWG, p. 571). A marginal cost price equilibrium with transfers for
production sets `Yⱼ = {Fⱼ ≤ 0}`: wealth levels summing to `p·ω̄ + ∑ⱼ p·yⱼ`, (i) every `yⱼ ∈ Yⱼ`
has `p = γⱼ ∇Fⱼ(yⱼ)` for some `γⱼ > 0` (16.G.1), (ii) every `xᵢ` is maximal in her budget set,
(iii) markets clear. -/
def PrefEconomy.IsMCPriceEqm (E : PrefEconomy ι κ L) (F : κ → (Fin L → ℝ) → ℝ)
    (a : Allocation ι κ L) (p : Fin L → ℝ) (w : ι → ℝ) : Prop :=
  ∑ i, w i = p ⬝ᵥ E.ω + ∑ j, p ⬝ᵥ a.y j ∧
    (∀ j, a.y j ∈ E.Y j ∧ ∃ F' : (Fin L → ℝ) →L[ℝ] ℝ, HasFDerivAt (F j) F' (a.y j) ∧
      ∃ γ : ℝ, 0 < γ ∧ ∀ l, p l = γ * F' (Pi.single l 1)) ∧
    (∀ i, IsMaximalFor (E.pref i) (budgetSetOn (E.X i) p (w i)) (a.x i)) ∧
    ∑ i, a.x i = E.ω + ∑ j, a.y j

/-- **Proposition 16.G.1** (MWG, p. 571). In the economy of Section 16.F (`J ≥ 1`, `L ≥ 1`,
`∇uᵢ ≫ 0`, `∇Fⱼ ≫ 0` everywhere; no convexity of the `Fⱼ`), with quasiconcave utilities, every
Pareto optimal allocation is a marginal cost price equilibrium with transfers with `p ≫ 0` and
wealth levels `wᵢ = p·xᵢ`. -/
theorem proposition_16_G_1 [Nonempty κ] (hL : 0 < L) {u : ι → (Fin L → ℝ) → ℝ}
    {u' : ι → (Fin L → ℝ) → (Fin L → ℝ) →L[ℝ] ℝ} {F : κ → (Fin L → ℝ) → ℝ}
    {F' : κ → (Fin L → ℝ) → (Fin L → ℝ) →L[ℝ] ℝ} {ω : Fin L → ℝ}
    (hu : ∀ i x, HasFDerivAt (u i) (u' i x) x) (hupos : ∀ i x l, 0 < u' i x (Pi.single l 1))
    (hF : ∀ j y, HasFDerivAt (F j) (F' j y) y) (hFpos : ∀ j y l, 0 < F' j y (Pi.single l 1))
    (hq : ∀ i, QuasiconcaveOn ℝ (nonnegOrthant L) (u i)) (i₀ : ι) {a : Allocation ι κ L}
    (hpo : (economy16F u F ω).IsParetoOptimal a) :
    ∃ p, StrictlyPositive p ∧ (economy16F u F ω).IsMCPriceEqm F a p (fun i => p ⬝ᵥ a.x i) := by
  have hFmono : ∀ j x y, x ≤ y → F j x ≤ F j y := fun j x y hxy =>
    mono_of_grad_pos (hF j) (hFpos j) hxy
  have hsol := exercise_16_F_1_ii (i₀ := i₀) hFmono hpo
  obtain ⟨δ, μ, γ, hδ1, hδ0, hμ0, hγ0, hfoc, hfoc_eq, hfoc_y, -, -, -⟩ :=
    exercise_16_F_2 hL hsol (fun i => hu i (a.x i)) (fun j => hF j (a.y j))
      (fun i l => hupos i _ l) (fun j l => hFpos j _ l)
  have hμpos : ∀ l, 0 < μ l := fun l => by
    have := hfoc i₀ l; rw [hδ1, one_mul] at this; linarith [hupos i₀ (a.x i₀) l]
  obtain ⟨⟨hx, hy⟩, hc⟩ := hpo.1
  refine ⟨μ, hμpos, ?_, fun j => ⟨hy j, F' j (a.y j), hF j _, γ j, ?_, fun l => ?_⟩,
    fun i => ?_, hc⟩
  · change ∑ i, μ ⬝ᵥ a.x i = μ ⬝ᵥ ω + ∑ j, μ ⬝ᵥ a.y j
    have hc' : ∑ i, a.x i = ω + ∑ j, a.y j := hc
    rw [← dotProduct_finset_sum, hc', dotProduct_add, dotProduct_finset_sum]
  · by_contra h
    have h0 : γ j = 0 := le_antisymm (not_lt.mp h) (hγ0 j)
    have := hfoc_y j ⟨0, hL⟩
    rw [h0, zero_mul, sub_zero] at this
    linarith [hμpos ⟨0, hL⟩]
  · linarith [hfoc_y j l]
  · rcases (hδ0 i).lt_or_eq with hpos | hzero
    · exact consumer_max_of_foc (hq i) (fun x _ => (hu i x).continuousAt.continuousWithinAt)
        (fun x _ y hxy => by
          by_cases h : x = y
          · rw [h]
          · exact (strictMono_of_grad_pos (hu i) (hupos i) hxy h).le)
        (hx i) (hu i (a.x i)) hμpos hpos (hfoc i) (hfoc_eq i)
    · have hx0 : a.x i = 0 := funext fun l => by
        by_contra hne
        have hxl : 0 < a.x i l := lt_of_le_of_ne (hx i l) (Ne.symm hne)
        have := hfoc_eq i l hxl
        rw [← hzero, zero_mul, zero_sub, neg_eq_zero] at this
        exact absurd this (hμpos l).ne'
      refine ⟨⟨hx i, le_rfl⟩, fun y hy => ?_⟩
      have hy0 : y = 0 := by
        by_contra hne
        have := dotProduct_pos_of_nonneg_ne_zero hy.1 hne hμpos
        rw [dotProduct_comm] at this
        have h2 : μ ⬝ᵥ y ≤ μ ⬝ᵥ a.x i := hy.2
        rw [hx0, dotProduct_zero] at h2
        linarith
      rw [hy0, hx0]
      exact le_rfl

/-- **Exercise 16.G.1** (MWG, p. 576): Proposition 16.G.1 proved from the first-order conditions
(16.F.2)-(16.F.3) (this is how `proposition_16_G_1` is proved). -/
theorem exercise_16_G_1 [Nonempty κ] (hL : 0 < L) {u : ι → (Fin L → ℝ) → ℝ}
    {u' : ι → (Fin L → ℝ) → (Fin L → ℝ) →L[ℝ] ℝ} {F : κ → (Fin L → ℝ) → ℝ}
    {F' : κ → (Fin L → ℝ) → (Fin L → ℝ) →L[ℝ] ℝ} {ω : Fin L → ℝ}
    (hu : ∀ i x, HasFDerivAt (u i) (u' i x) x) (hupos : ∀ i x l, 0 < u' i x (Pi.single l 1))
    (hF : ∀ j y, HasFDerivAt (F j) (F' j y) y) (hFpos : ∀ j y l, 0 < F' j y (Pi.single l 1))
    (hq : ∀ i, QuasiconcaveOn ℝ (nonnegOrthant L) (u i)) (i₀ : ι) {a : Allocation ι κ L}
    (hpo : (economy16F u F ω).IsParetoOptimal a) :
    ∃ p, StrictlyPositive p ∧ (economy16F u F ω).IsMCPriceEqm F a p (fun i => p ⬝ᵥ a.x i) :=
  proposition_16_G_1 hL hu hupos hF hFpos hq i₀ hpo

/-- **Exercise 16.G.2** (MWG, p. 576). Two goods, an input (good 1) and an output (good 2), and
the technology `q ≤ φ(z)`, i.e. `F(y) = y₂ - φ(-y₁)`, at a plan using `z` units of input with
marginal product `φ'(z) > 0`. Condition (16.G.1), `p = γ ∇F(y)` with `γ > 0`, says that the input
price equals the output price times the marginal product, equivalently that the output price
equals marginal cost `p₁/φ'(z)`. -/
theorem exercise_16_G_2 {φ : ℝ → ℝ} {m z q : ℝ} (hφ : HasDerivAt φ m z) (hm : 0 < m)
    {F' : (Fin 2 → ℝ) →L[ℝ] ℝ} (hF : HasFDerivAt (fun y : Fin 2 → ℝ => y 1 - φ (-y 0)) F' ![-z, q])
    {p : Fin 2 → ℝ} {γ : ℝ} (hp : ∀ l, p l = γ * F' (Pi.single l 1)) :
    p 0 = p 1 * m ∧ p 1 = p 0 / m := by
  -- the derivative of `F` is `y ↦ y₂ + φ'(z) y₁`
  have hinner : HasFDerivAt (fun y : Fin 2 → ℝ => -y 0)
      (-(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0)) ![-z, q] :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0).hasFDerivAt.neg
  have hval : -(![-z, q] : Fin 2 → ℝ) 0 = z := by simp
  have hφ' : HasDerivAt φ m (-(![-z, q] : Fin 2 → ℝ) 0) := by rw [hval]; exact hφ
  have hcomp := hφ'.comp_hasFDerivAt (![-z, q] : Fin 2 → ℝ) hinner
  have hG := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1).hasFDerivAt.sub
    hcomp
  have huniq := hF.unique hG
  have h0 : F' (Pi.single 0 1) = m := by rw [huniq]; simp
  have h1 : F' (Pi.single 1 1) = 1 := by rw [huniq]; simp
  have hp0 := hp 0
  have hp1 := hp 1
  rw [h0] at hp0
  rw [h1, mul_one] at hp1
  refine ⟨by rw [hp0, hp1], ?_⟩
  rw [hp0, hp1]
  field_simp

end MWG.WelfareTheorems
