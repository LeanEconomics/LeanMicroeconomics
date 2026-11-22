/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGEquilibriumUncertainty.Complete

/-!
# Long-lived assets in a tree (MWG pp. 707-708, Example 19.E.7, Exercise 19.E.5)

* **Small type, pp. 707-708**: with short-lived assets at every date-event `tE`, completeness means
  `rank R(tE) = S(tE)` at every node (`IsCompleteTree`).
* **Example 19.E.7**: the tree of Figure 19.B.2 with `T = 2` (nodes `a`, `b`, `c` and terminal
  states `1-4`), two long-lived assets `r₁ = (1, 1, 1, 1)`, `r₂ = (0, 1, 0, 1)` traded at `a`,
  `b`, `c`.
  Arbitrage at `b`, `c` and `a` (Lemma 19.E.1) gives `μ`, `λ ≥ 0` with `μ₁ + μ₂ = 1`, `μ₂ = q_b`,
  `μ₃ + μ₄ = 1`, `μ₄ = q_c`, `λ_b + λ_c = 1`, `q_a = λ_b q_b + λ_c q_c` (`example_19_E_7`), and
  Arrow-Debreu prices `p = (λ_b μ₁, λ_b μ₂, λ_c μ₃, λ_c μ₄)`.
* **Exercise 19.E.5**: if `q_b ≠ q_c`, the final consumptions reachable by sequential trade in the
  two assets are exactly those affordable at the Arrow-Debreu prices `p` (`exercise_19_E_5`).
* **Footnote 21**: the martingale property: each asset price is the conditional expectation of the
  final returns under the Arrow-Debreu prices (`footnote_19_21`).
-/

namespace MWG.EquilibriumUncertainty

open Matrix

/-- **pp. 707-708**. A tree asset structure with short-lived assets: at each admissible
date-event `n` the return matrix `R n` has one row per successor; it is complete when
`rank R(tE) = S(tE)` at every node (Definition 19.E.3 node by node). -/
def IsCompleteTree {N : Type*} {succ : N → ℕ} {K : N → ℕ}
    (R : ∀ n, Matrix (Fin (succ n)) (Fin (K n)) ℝ) : Prop :=
  ∀ n, IsComplete (R n)

/-- The return matrix at node `b` (states 1, 2) or `c` (states 3, 4): asset 1 pays `(1, 1)` and
asset 2 pays `(0, 1)`. -/
def nodeMatrix19E7 : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 1, 1]

/-- The values at `t = 1` of the two assets seen from node `a`: `(1, q_b)` at `b`, `(1, q_c)` at
`c`. -/
def rootMatrix19E7 (qb qc : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, qb; 1, qc]

/-- **Example 19.E.7** (MWG, p. 708). If asset prices are arbitrage free at `b` (prices `(1, q_b)`),
at `c` (prices `(1, q_c)`) and at `a` (prices `(1, q_a)`, with `q_b, q_c ≥ 0` not both zero), there
are `μ, λ ≥ 0` with `μ₁ + μ₂ = 1`, `μ₂ = q_b`, `μ₃ + μ₄ = 1`, `μ₄ = q_c`, `λ_b + λ_c = 1` and
`q_a = λ_b q_b + λ_c q_c` (Proposition 19.E.1 at each node). -/
theorem example_19_E_7 {qa qb qc : ℝ} (hb : ArbitrageFree nodeMatrix19E7 ![1, qb])
    (hc : ArbitrageFree nodeMatrix19E7 ![1, qc])
    (hRa : NonnegNonzeroReturns (rootMatrix19E7 qb qc))
    (ha : ArbitrageFree (rootMatrix19E7 qb qc) ![1, qa]) :
    ∃ μ : Fin 4 → ℝ, ∃ lam : Fin 2 → ℝ, (∀ s, 0 ≤ μ s) ∧ (∀ n, 0 ≤ lam n) ∧
      μ 0 + μ 1 = 1 ∧ μ 1 = qb ∧ μ 2 + μ 3 = 1 ∧ μ 3 = qc ∧ lam 0 + lam 1 = 1 ∧
      qa = lam 0 * qb + lam 1 * qc := by
  have hN : NonnegNonzeroReturns nodeMatrix19E7 := by
    refine ⟨fun s k => ?_, fun k => ⟨1, ?_⟩⟩
    · fin_cases s <;> fin_cases k <;> simp [nodeMatrix19E7]
    · fin_cases k <;> simp [nodeMatrix19E7]
  obtain ⟨μb, hμb, hqb⟩ := lemma_19_E_1 hN hb
  obtain ⟨μc, hμc, hqc⟩ := lemma_19_E_1 hN hc
  obtain ⟨lam, hlam, hqa⟩ := lemma_19_E_1 hRa ha
  have b0 := hqb 0; have b1 := hqb 1; have c0 := hqc 0; have c1 := hqc 1
  have a0 := hqa 0; have a1 := hqa 1
  simp [nodeMatrix19E7, rootMatrix19E7, Fin.sum_univ_two] at b0 b1 c0 c1 a0 a1
  refine ⟨![μb 0, μb 1, μc 0, μc 1], lam, fun s => ?_, hlam, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · fin_cases s <;> simp [hμb, hμc]
  all_goals first | linarith | (simp; linarith)

/-- The Arrow-Debreu prices of Example 19.E.7: `p = (λ_b μ₁, λ_b μ₂, λ_c μ₃, λ_c μ₄)`. -/
def adPrices19E7 (μ : Fin 4 → ℝ) (lam : Fin 2 → ℝ) : Fin 4 → ℝ :=
  ![lam 0 * μ 0, lam 0 * μ 1, lam 1 * μ 2, lam 1 * μ 3]

/-- **Exercise 19.E.5** (MWG, p. 727). The net trades `m ∈ ℝ⁴` in final consumption reachable by
sequential trade: at `a` buy `y_a` units of asset 1 and `z_a` of asset 2 with
`y_a + q_a z_a ≤ 0`; at `b` rebalance to `(y_b, z_b)` with `y_b + q_b z_b ≤ y_a + q_b z_a`, and
similarly at `c`; then `m₁ ≤ y_b`, `m₂ ≤ y_b + z_b`, `m₃ ≤ y_c`, `m₄ ≤ y_c + z_c`. -/
def SeqReachable19E7 (qa qb qc : ℝ) (m : Fin 4 → ℝ) : Prop :=
  ∃ ya za yb zb yc zc : ℝ, ya + qa * za ≤ 0 ∧ yb + qb * zb ≤ ya + qb * za ∧
    yc + qc * zc ≤ ya + qc * za ∧ m 0 ≤ yb ∧ m 1 ≤ yb + zb ∧ m 2 ≤ yc ∧ m 3 ≤ yc + zc

/-- **Exercise 19.E.5** (MWG, p. 727). Under the weak condition `q_b ≠ q_c`, the net trades in
final consumption achievable through sequential trade at the prices `(q_a, q_b, q_c)` are exactly
those affordable with the four Arrow-Debreu contingent commodities at prices `p` (so the sets of
achievable final consumptions `ω + m`, `x ≥ 0`, coincide). -/
theorem exercise_19_E_5 {qa qb qc : ℝ} (hbc : qb ≠ qc) {μ : Fin 4 → ℝ} {lam : Fin 2 → ℝ}
    (hμ : ∀ s, 0 ≤ μ s) (hlam : ∀ n, 0 ≤ lam n) (h01 : μ 0 + μ 1 = 1) (h1 : μ 1 = qb)
    (h23 : μ 2 + μ 3 = 1) (h3 : μ 3 = qc) (hl : lam 0 + lam 1 = 1)
    (hqa : qa = lam 0 * qb + lam 1 * qc) (m : Fin 4 → ℝ) :
    SeqReachable19E7 qa qb qc m ↔ adPrices19E7 μ lam ⬝ᵥ m ≤ 0 := by
  have hval : adPrices19E7 μ lam ⬝ᵥ m =
      lam 0 * (μ 0 * m 0 + μ 1 * m 1) + lam 1 * (μ 2 * m 2 + μ 3 * m 3) := by
    simp [adPrices19E7, dotProduct, Fin.sum_univ_four]; ring
  rw [hval]
  constructor
  · rintro ⟨ya, za, yb, zb, yc, zc, ha, hb, hc, m0, m1, m2, m3⟩
    have kb : μ 0 * m 0 + μ 1 * m 1 ≤ ya + qb * za := by
      have := mul_le_mul_of_nonneg_left m0 (hμ 0)
      have := mul_le_mul_of_nonneg_left m1 (hμ 1)
      have e : μ 0 * yb + μ 1 * (yb + zb) = yb + qb * zb := by
        rw [← h1]; linear_combination yb * h01
      linarith
    have kc : μ 2 * m 2 + μ 3 * m 3 ≤ ya + qc * za := by
      have := mul_le_mul_of_nonneg_left m2 (hμ 2)
      have := mul_le_mul_of_nonneg_left m3 (hμ 3)
      have e : μ 2 * yc + μ 3 * (yc + zc) = yc + qc * zc := by
        rw [← h3]; linear_combination yc * h23
      linarith
    have := mul_le_mul_of_nonneg_left kb (hlam 0)
    have := mul_le_mul_of_nonneg_left kc (hlam 1)
    have e : lam 0 * (ya + qb * za) + lam 1 * (ya + qc * za) = ya + qa * za := by
      rw [hqa]; linear_combination ya * hl
    linarith
  · intro hle
    set Vb := μ 0 * m 0 + μ 1 * m 1 with hVb
    set Vc := μ 2 * m 2 + μ 3 * m 3 with hVc
    have hd : qb - qc ≠ 0 := sub_ne_zero.mpr hbc
    set za := (Vb - Vc) / (qb - qc) with hza
    set ya := Vb - qb * za with hya
    refine ⟨ya, za, m 0, m 1 - m 0, m 2, m 3 - m 2, ?_, ?_, ?_, le_rfl, by linarith, le_rfl,
      by linarith⟩
    · have e1 : ya + qb * za = Vb := by rw [hya]; ring
      have e2 : ya + qc * za = Vc := by
        rw [hya, hza]; field_simp; ring
      have e : ya + qa * za = lam 0 * Vb + lam 1 * Vc := by
        linear_combination lam 0 * e1 + lam 1 * e2 + za * hqa - ya * hl
      linarith
    · have e1 : ya + qb * za = Vb := by rw [hya]; ring
      have e3 : m 0 + qb * (m 1 - m 0) = Vb := by
        rw [hVb, ← h1]; linear_combination (-(m 0)) * h01
      rw [e1]; linarith
    · have e2 : ya + qc * za = Vc := by rw [hya, hza]; field_simp; ring
      have e3 : m 2 + qc * (m 3 - m 2) = Vc := by
        rw [hVc, ← h3]; linear_combination (-(m 2)) * h23
      rw [e2]; linarith

/-- **Footnote 21** (MWG, p. 708). The martingale property of asset prices: at node `b` the price
`q_b` of asset 2 is the conditional expectation of its final returns `(0, 1)` under the
Arrow-Debreu prices (normalized on the event `{1, 2}`), and similarly at `c`; at `a`, `q_a` is the
expectation of the final returns under `p` (which sums to one). -/
theorem footnote_19_21 {qa qb qc : ℝ} {μ : Fin 4 → ℝ} {lam : Fin 2 → ℝ}
    (hlb : 0 < lam 0) (hlc : 0 < lam 1) (h01 : μ 0 + μ 1 = 1) (h1 : μ 1 = qb)
    (h23 : μ 2 + μ 3 = 1) (h3 : μ 3 = qc) (hl : lam 0 + lam 1 = 1)
    (hqa : qa = lam 0 * qb + lam 1 * qc) :
    let p := adPrices19E7 μ lam
    qb = (p 0 * 0 + p 1 * 1) / (p 0 + p 1) ∧ qc = (p 2 * 0 + p 3 * 1) / (p 2 + p 3) ∧
      ∑ s, p s = 1 ∧ qa = ∑ s, p s * ![0, 1, 0, 1] s := by
  intro p
  have e0 : p 0 = lam 0 * μ 0 := rfl
  have e1 : p 1 = lam 0 * μ 1 := rfl
  have e2 : p 2 = lam 1 * μ 2 := rfl
  have e3 : p 3 = lam 1 * μ 3 := rfl
  have v0 : (![0, 1, 0, 1] : Fin 4 → ℝ) 0 = 0 := rfl
  have v1 : (![0, 1, 0, 1] : Fin 4 → ℝ) 1 = 1 := rfl
  have v2 : (![0, 1, 0, 1] : Fin 4 → ℝ) 2 = 0 := rfl
  have v3 : (![0, 1, 0, 1] : Fin 4 → ℝ) 3 = 1 := rfl
  rw [Fin.sum_univ_four, Fin.sum_univ_four, e0, e1, e2, e3, v0, v1, v2, v3]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [mul_zero, mul_one, zero_add, ← mul_add, h01, mul_one, ← h1]; field_simp
  · rw [mul_zero, mul_one, zero_add, ← mul_add, h23, mul_one, ← h3]; field_simp
  · linear_combination lam 0 * h01 + lam 1 * h23 + hl
  · rw [hqa, h1, h3]; ring

end MWG.EquilibriumUncertainty
