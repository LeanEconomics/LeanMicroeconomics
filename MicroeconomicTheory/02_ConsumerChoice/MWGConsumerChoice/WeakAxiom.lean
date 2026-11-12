/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGConsumerChoice.DemandBasics

/-!
# The weak axiom of revealed preference and the compensated law of demand

MWG, Section 2.F, pp. 28–33.

* Definition 2.F.1 (the weak axiom for Walrasian demand functions) and Slutsky compensated
  price changes (p. 30).
* The fact used in the proof of Proposition 2.F.1(ii) (small type, pp. 31–32): with Walras'
  law, the weak axiom holds if and only if it holds for all compensated price changes.
* Proposition 2.F.1 (p. 30–31): with Walras' law, the weak axiom is equivalent to the
  compensated law of demand (2.F.1). Direction (i) uses only Walras' law; direction (ii) also
  uses that demand lies in `ℝ^L_+` (the book's consumption set). Homogeneity of degree zero,
  assumed in the book, is not needed.
* The own-price consequence (p. 32): a compensated rise in `p_ℓ` gives `Δx_ℓ ≤ 0`, with
  `Δx_ℓ < 0` when demand changes. The book's unqualified `Δx_ℓ < 0` fails when demand does not
  move: Leontief demand is a counterexample.
* Figure 2.F.4 (compensated price fall) and Figure 2.F.5 (the weak axiom does not give the law
  of demand for uncompensated changes: a two-observation witness).
-/

namespace MWG.ConsumerChoice

/-- **Definition 2.F.1** (MWG, p. 29). The weak axiom of revealed preference for a Walrasian
demand function: if `p·x(p', w') ≤ w` and `x(p', w') ≠ x(p, w)` then `p'·x(p, w) > w'`. -/
def WeakAxiom {L : ℕ} (x : DemandFunction L) : Prop :=
  ∀ p w p' w', PWDomain p w → PWDomain p' w' → p ⬝ᵥ x p' w' ≤ w → x p' w' ≠ x p w →
    w' < p' ⬝ᵥ x p w

/-- **Section 2.D–2.E** (MWG, pp. 21, 23). Demand takes values in the consumption set
`ℝ^L_+`. -/
def ValuesInOrthant {L : ℕ} (x : DemandFunction L) : Prop :=
  ∀ p w, PWDomain p w → x p w ∈ nonnegOrthant L

/-- **Section 2.F** (MWG, p. 30). Slutsky wealth compensation: the new wealth
`w' = p'·x(p, w)` that keeps the old bundle just affordable. -/
def compensatedWealth {L : ℕ} (x : DemandFunction L) (p : Fin L → ℝ) (w : ℝ)
    (p' : Fin L → ℝ) : ℝ :=
  p' ⬝ᵥ x p w

/-- **Proposition 2.F.1** (MWG, p. 31), property (2.F.1): the compensated law of demand. For
every compensated price change from `(p, w)` to `(p', p'·x(p, w))` in the domain,
`(p' - p)·[x(p', w') - x(p, w)] ≤ 0`, strictly when `x(p', w') ≠ x(p, w)`. -/
def CompensatedLawOfDemand {L : ℕ} (x : DemandFunction L) : Prop :=
  ∀ p w p', PWDomain p w → StrictlyPositive p' → 0 < compensatedWealth x p w p' →
    (p' - p) ⬝ᵥ (x p' (compensatedWealth x p w p') - x p w) ≤ 0 ∧
      (x p w ≠ x p' (compensatedWealth x p w p') →
        (p' - p) ⬝ᵥ (x p' (compensatedWealth x p w p') - x p w) < 0)

/-- With Walras' law and values in `ℝ^L_+`, compensated wealth is positive at any `p' ≫ 0`,
so every compensated price change stays in the domain. -/
theorem compensatedWealth_pos {L : ℕ} {x : DemandFunction L} (hW : WalrasLaw x)
    (hX : ValuesInOrthant x) {p : Fin L → ℝ} {w : ℝ} (hd : PWDomain p w) {p' : Fin L → ℝ}
    (hp' : StrictlyPositive p') : 0 < compensatedWealth x p w p' := by
  have hx := hX p w hd
  have hw := hW p w hd
  by_contra hneg
  push Not at hneg
  have hzero : ∀ l, x p w l = 0 := by
    have hsum : ∀ l ∈ Finset.univ, 0 ≤ p' l * x p w l :=
      fun l _ => mul_nonneg (hp' l).le (hx l)
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg hsum).mp
      (le_antisymm hneg (Finset.sum_nonneg hsum))
    intro l
    rcases mul_eq_zero.mp (h0 l (Finset.mem_univ l)) with h | h
    · exact absurd h (hp' l).ne'
    · exact h
  have : p ⬝ᵥ x p w = 0 := by simp [dotProduct, hzero]
  linarith [hd.2]

/-- **Section 2.F** (MWG, pp. 31–32, small type). With Walras' law (and demand in `ℝ^L_+`),
the weak axiom holds if and only if it holds for all compensated price changes: whenever
`p·x(p', w') = w` and `x(p', w') ≠ x(p, w)`, then `p'·x(p, w) > w'`. -/
theorem weakAxiom_iff_compensated {L : ℕ} {x : DemandFunction L} (hW : WalrasLaw x)
    (hX : ValuesInOrthant x) :
    WeakAxiom x ↔ ∀ p w p' w', PWDomain p w → PWDomain p' w' → p ⬝ᵥ x p' w' = w →
      x p' w' ≠ x p w → w' < p' ⬝ᵥ x p w := by
  constructor
  · intro h p w p' w' hd hd' heq hne
    exact h p w p' w' hd hd' heq.le hne
  · intro h p w p' w' hd hd' hle hne
    by_contra hcon
    push Not at hcon
    rcases eq_or_lt_of_le hle with heq | hlt
    · exact absurd (h p w p' w' hd hd' heq hne) (not_lt.mpr hcon)
    rcases eq_or_lt_of_le hcon with heq' | hlt'
    · have := h p' w' p w hd' hd heq' (Ne.symm hne)
      linarith
    -- both inequalities strict: interpolate the prices
    set xv := x p w
    set xv' := x p' w'
    have hWp : p ⬝ᵥ xv = w := hW p w hd
    have hWp' : p' ⬝ᵥ xv' = w' := hW p' w' hd'
    set a := p ⬝ᵥ (xv' - xv) with ha
    set b := p' ⬝ᵥ (xv' - xv) with hb
    have ha0 : a < 0 := by rw [ha, dotProduct_sub]; linarith
    have hb0 : 0 < b := by rw [hb, dotProduct_sub]; linarith
    set α := b / (b - a) with hα
    have hba : 0 < b - a := by linarith
    have hα0 : 0 < α := div_pos hb0 hba
    have hα1 : α < 1 := (div_lt_one hba).mpr (by linarith)
    set q := α • p + (1 - α) • p' with hq
    have hqpos : StrictlyPositive q := fun l => by
      simp only [hq, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have := hd.1 l
      have := hd'.1 l
      nlinarith
    have hqeq : q ⬝ᵥ xv' = q ⬝ᵥ xv := by
      have : q ⬝ᵥ (xv' - xv) = 0 := by
        rw [hq, add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul,
          ← ha, ← hb, hα]
        field_simp
        ring
      rw [dotProduct_sub, sub_eq_zero] at this
      exact this
    set wq := q ⬝ᵥ xv with hwq
    have hwq0 : 0 < wq := compensatedWealth_pos hW hX hd hqpos
    have hdq : PWDomain q wq := ⟨hqpos, hwq0⟩
    set xq := x q wq
    have hWq : q ⬝ᵥ xq = wq := hW q wq hdq
    have hsplit : α * (p ⬝ᵥ xq) + (1 - α) * (p' ⬝ᵥ xq) = wq := by
      rw [← hWq, hq, add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul]
    have hlt2 : wq < α * w + (1 - α) * w' := by
      have e : wq = α * (p ⬝ᵥ xv') + (1 - α) * (p' ⬝ᵥ xv') := by
        rw [← hqeq, hq, add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul,
          smul_eq_mul]
      rw [e]
      have h1 := mul_lt_mul_of_pos_left hlt hα0
      have h2 : (1 - α) * (p' ⬝ᵥ xv') = (1 - α) * w' := by rw [hWp']
      linarith
    by_cases hc : p ⬝ᵥ xq < w
    · -- compensated change from (q, wq) to (p, w), using x(p, w)
      have hne' : xq ≠ xv := by
        intro h'
        rw [h'] at hc
        linarith
      have := h q wq p w hdq hd hwq.symm (Ne.symm hne')
      linarith
    · push Not at hc
      have hc' : p' ⬝ᵥ xq < w' := by
        by_contra hc'
        push Not at hc'
        have := mul_le_mul_of_nonneg_left hc hα0.le
        have := mul_le_mul_of_nonneg_left hc' (by linarith : (0 : ℝ) ≤ 1 - α)
        linarith
      have hne' : xq ≠ xv' := by
        intro h'
        rw [h'] at hc'
        linarith
      have := h q wq p' w' hdq hd' (by rw [hqeq]) (Ne.symm hne')
      linarith

/-- **Proposition 2.F.1(i)** (MWG, p. 31). With Walras' law, the weak axiom implies the
compensated law of demand (2.F.1), strictly when demand changes. -/
theorem proposition_2_F_1_i {L : ℕ} {x : DemandFunction L} (hW : WalrasLaw x)
    (hWA : WeakAxiom x) : CompensatedLawOfDemand x := by
  intro p w p' hd hp' hw'
  set w' := compensatedWealth x p w p' with hw'def
  have hd' : PWDomain p' w' := ⟨hp', hw'⟩
  have h1 : p' ⬝ᵥ (x p' w' - x p w) = 0 := by
    rw [dotProduct_sub, hW p' w' hd', hw'def, compensatedWealth, sub_self]
  have hsplit : (p' - p) ⬝ᵥ (x p' w' - x p w) = -(p ⬝ᵥ (x p' w' - x p w)) := by
    rw [sub_dotProduct, h1, zero_sub]
  by_cases hne : x p w = x p' w'
  · refine ⟨by rw [hne, sub_self, dotProduct_zero], fun h => absurd hne h⟩
  · have hgt : w < p ⬝ᵥ x p' w' := by
      by_contra hle
      push Not at hle
      have := hWA p w p' w' hd hd' hle (Ne.symm hne)
      rw [hw'def, compensatedWealth] at this
      exact lt_irrefl _ this
    have hpos : 0 < p ⬝ᵥ (x p' w' - x p w) := by
      rw [dotProduct_sub, hW p w hd]
      linarith
    have hneg : (p' - p) ⬝ᵥ (x p' w' - x p w) < 0 := by rw [hsplit]; linarith
    exact ⟨hneg.le, fun _ => hneg⟩

/-- **Proposition 2.F.1(ii)** (MWG, pp. 31–32). With Walras' law and demand in `ℝ^L_+`, the
compensated law of demand (with its strict part) implies the weak axiom. -/
theorem proposition_2_F_1_ii {L : ℕ} {x : DemandFunction L} (hW : WalrasLaw x)
    (hX : ValuesInOrthant x) (hC : CompensatedLawOfDemand x) : WeakAxiom x := by
  rw [weakAxiom_iff_compensated hW hX]
  intro p w p' w' hd hd' heq hne
  by_contra hle
  push Not at hle
  -- compensated change from (p', w') to (p, p·x(p', w')) = (p, w)
  have hcw : compensatedWealth x p' w' p = w := heq
  have hpos : 0 < compensatedWealth x p' w' p := by rw [hcw]; exact hd.2
  obtain ⟨_, hstrict⟩ := hC p' w' p hd' hd.1 hpos
  rw [hcw] at hstrict
  have hlt := hstrict hne
  have e1 : p ⬝ᵥ (x p w - x p' w') = 0 := by rw [dotProduct_sub, hW p w hd, heq, sub_self]
  have e2 : 0 ≤ p' ⬝ᵥ (x p' w' - x p w) := by rw [dotProduct_sub, hW p' w' hd']; linarith
  have : (p - p') ⬝ᵥ (x p w - x p' w') = p' ⬝ᵥ (x p' w' - x p w) := by
    rw [sub_dotProduct, e1, zero_sub, ← neg_sub (x p' w') (x p w), dotProduct_neg, neg_neg]
  linarith

/-- **Proposition 2.F.1** (MWG, pp. 30–31). Suppose `x` satisfies Walras' law and takes values
in `ℝ^L_+`. Then `x` satisfies the weak axiom if and only if the compensated law of demand
(2.F.1) holds, strictly whenever demand changes. (The book also assumes homogeneity of degree
zero; it is not needed.) This is also summary conclusion (i) on p. 36. -/
theorem proposition_2_F_1 {L : ℕ} {x : DemandFunction L} (hW : WalrasLaw x)
    (hX : ValuesInOrthant x) : WeakAxiom x ↔ CompensatedLawOfDemand x :=
  ⟨proposition_2_F_1_i hW, proposition_2_F_1_ii hW hX⟩

/-- **Section 2.F** (MWG, p. 32), corrected. For a compensated change in the own price only,
`Δp = Δp_ℓ e_ℓ`, the weak axiom gives `Δp_ℓ Δx_ℓ ≤ 0`, strictly when demand changes. Hence
`Δp_ℓ > 0` implies `Δx_ℓ ≤ 0` (and `Δx_ℓ < 0` if `x(p', w') ≠ x(p, w)`). -/
theorem own_price_compensated_law {L : ℕ} {x : DemandFunction L} (hW : WalrasLaw x)
    (hWA : WeakAxiom x) {p : Fin L → ℝ} {w : ℝ} (hd : PWDomain p w) (l : Fin L) {δ : ℝ}
    (hp' : StrictlyPositive (p + Pi.single l δ))
    (hw' : 0 < compensatedWealth x p w (p + Pi.single l δ)) :
    δ * (x (p + Pi.single l δ) (compensatedWealth x p w (p + Pi.single l δ)) l - x p w l) ≤ 0 ∧
      (x p w ≠ x (p + Pi.single l δ) (compensatedWealth x p w (p + Pi.single l δ)) →
        δ * (x (p + Pi.single l δ) (compensatedWealth x p w (p + Pi.single l δ)) l -
          x p w l) < 0) := by
  obtain ⟨h1, h2⟩ := proposition_2_F_1_i hW hWA p w _ hd hp' hw'
  simp only [add_sub_cancel_left, single_dotProduct, Pi.sub_apply] at h1 h2
  exact ⟨h1, h2⟩

/-- **Figure 2.F.4** (MWG, p. 33). A compensated fall in the price of good `ℓ` cannot lower the
demand for good `ℓ`. -/
theorem figure_2_F_4 {L : ℕ} {x : DemandFunction L} (hW : WalrasLaw x) (hWA : WeakAxiom x)
    {p : Fin L → ℝ} {w : ℝ} (hd : PWDomain p w) (l : Fin L) {δ : ℝ} (hδ : δ < 0)
    (hp' : StrictlyPositive (p + Pi.single l δ))
    (hw' : 0 < compensatedWealth x p w (p + Pi.single l δ)) :
    x p w l ≤ x (p + Pi.single l δ) (compensatedWealth x p w (p + Pi.single l δ)) l := by
  have := (own_price_compensated_law hW hWA hd l hp' hw').1
  nlinarith

/-! ### The book's strict own-price claim fails without a change in demand -/

/-- Leontief demand for two goods, `x(p, w) = (w/(p₁+p₂), w/(p₁+p₂))`. -/
noncomputable def leontiefDemand : DemandFunction 2 := fun p w _ => w / (p 0 + p 1)

/-- Leontief demand satisfies Walras' law. -/
theorem leontiefDemand_walras : WalrasLaw leontiefDemand := by
  intro p w hd
  have : p 0 + p 1 ≠ 0 := by have := hd.1 0; have := hd.1 1; positivity
  simp only [leontiefDemand, dotProduct, Fin.sum_univ_two]
  field_simp

/-- Leontief demand is homogeneous of degree zero. -/
theorem leontiefDemand_homogeneous : HomogeneousZero leontiefDemand := by
  intro p w a hd ha
  have : p 0 + p 1 ≠ 0 := by have := hd.1 0; have := hd.1 1; positivity
  funext l
  simp only [leontiefDemand, Pi.smul_apply, smul_eq_mul]
  rw [← mul_add, mul_div_mul_left _ _ ha.ne']

/-- Leontief demand takes values in `ℝ²_+`. -/
theorem leontiefDemand_orthant : ValuesInOrthant leontiefDemand := by
  intro p w hd l
  have := hd.1 0
  have := hd.1 1
  exact div_nonneg hd.2.le (by positivity)

/-- Leontief demand satisfies the weak axiom. -/
theorem leontiefDemand_weakAxiom : WeakAxiom leontiefDemand := by
  intro p w p' w' hd hd' hle hne
  have hs : 0 < p 0 + p 1 := by have := hd.1 0; have := hd.1 1; positivity
  have hs' : 0 < p' 0 + p' 1 := by have := hd'.1 0; have := hd'.1 1; positivity
  simp only [leontiefDemand, dotProduct, Fin.sum_univ_two] at hle ⊢
  have hne' : w' / (p' 0 + p' 1) ≠ w / (p 0 + p 1) := by
    intro h
    apply hne
    funext l
    simp [leontiefDemand, h]
  have hle' : w' / (p' 0 + p' 1) ≤ w / (p 0 + p 1) := by
    rw [← add_mul, ← le_div_iff₀' hs] at hle
    exact hle
  have hlt := lt_of_le_of_ne hle' hne'
  rw [div_lt_div_iff₀ hs' hs] at hlt
  rw [← add_mul, mul_div_assoc', lt_div_iff₀ hs]
  linarith

/-- **Section 2.F** (MWG, p. 32), counterexample. The book states that a compensated rise in
the own price `p_ℓ` gives `Δx_ℓ < 0`. For Leontief demand (which satisfies the weak axiom,
Walras' law and homogeneity) at `p = (1, 1)`, `w = 2`, a compensated rise of `p₁` to 2 leaves
demand unchanged, so `Δx₁ = 0`. -/
theorem own_price_strict_counterexample :
    WeakAxiom leontiefDemand ∧ WalrasLaw leontiefDemand ∧ HomogeneousZero leontiefDemand ∧
      leontiefDemand (![1, 1] + Pi.single 0 1)
          (compensatedWealth leontiefDemand ![1, 1] 2 (![1, 1] + Pi.single 0 1)) 0 =
        leontiefDemand ![1, 1] 2 0 := by
  refine ⟨leontiefDemand_weakAxiom, leontiefDemand_walras, leontiefDemand_homogeneous, ?_⟩
  simp [leontiefDemand, compensatedWealth, dotProduct, Fin.sum_univ_two]
  norm_num

end MWG.ConsumerChoice
