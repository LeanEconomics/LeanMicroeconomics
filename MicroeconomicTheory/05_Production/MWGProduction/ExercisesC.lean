/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGProduction.CobbDouglas
import MWGProduction.AppendixMM
import MWGClassicalDemand.CloserCES
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Exercises 5.C.6-5.C.13 and the necessity of (5.C.4) (MWG, pp. 140, 161-162)

* (5.C.4) necessity (p. 140): with a constraint qualification, a cost-minimizing `z*` satisfies
  `w ≥ λ∇f(z*)`, `[w - λ∇f(z*)]·z* = 0` for some `λ ≥ 0` (`foc_5_C_4`, via Farkas' lemma); the
  qualification is needed (`foc_5_C_4_needs_cq`).
* **Exercise 5.C.6** (a)-(c), from the first-order conditions differentiated along price changes
  (the implicit function theorem supplies the differentiable demand).
* **Exercise 5.C.7**: false as printed with `∂²f/∂z_ℓ∂z_k < 0`; true (two inputs) with `> 0`.
* **Exercise 5.C.8**: the two observations violate profit maximization (weak axiom of profit
  maximization).
* **Exercise 5.C.9(a)-(b)** and **5.C.10(a)-(c)**: profit and cost functions; (c) via Chapter 3's
  CES expenditure function (Exercise 3.E.6).
* **Exercise 5.C.11**: `∂z_ℓ/∂q = ∂(∂c/∂q)/∂w_ℓ` (symmetry of the second derivative).
* **Exercise 5.C.12**: profit maximization in `Y` and in its constant-returns extension `Y'`.
* **Exercise 5.C.13**: `z₁ = αC/w₁`.
-/

namespace MWG.Production

open MWG.ClassicalDemand MWG.ConsumerChoice Filter Topology

variable {n : ℕ}

/-! ### Necessity of (5.C.4) -/

/-- **Section 5.C** (MWG, p. 140), condition (5.C.4), with a constraint qualification: let `z*`
solve the CMP with `f(z*) = q`, `f` differentiable at `z*`, and suppose some direction `d` with
`d_ℓ ≥ 0` whenever `z*_ℓ = 0` has `∇f(z*)·d > 0`. Then `w ≥ λ∇f(z*)` and
`[w - λ∇f(z*)]·z* = 0` for some `λ ≥ 0`. -/
theorem foc_5_C_4 {f : (Fin n → ℝ) → ℝ} {w z : Fin n → ℝ} {q : ℝ}
    (hz : z ∈ condDemand f w q) (hbind : f z = q) (hf : DifferentiableAt ℝ f z)
    (hcq : ∃ d : Fin n → ℝ, (∀ l, z l = 0 → 0 ≤ d l) ∧ 0 < (fun l => partialF f z l) ⬝ᵥ d) :
    ∃ lam : ℝ, 0 ≤ lam ∧ (∀ l, lam * partialF f z l ≤ w l) ∧
      (fun l => w l - lam * partialF f z l) ⬝ᵥ z = 0 := by
  classical
  set g : Fin n → ℝ := fun l => partialF f z l with hg
  have hgrad : ∀ v, fderiv ℝ f z v = g ⬝ᵥ v := fun v => by
    rw [fderiv_apply_eq_gradient_dot]; rfl
  -- generators: `g` and the unit vectors of the binding nonnegativity constraints
  let gen : Unit ⊕ {l // z l = 0} → Fin n → ℝ := Sum.elim (fun _ => g) fun l => Pi.single l.1 1
  have hcone : ∃ μ : Unit ⊕ {l // z l = 0} → ℝ, 0 ≤ μ ∧ w = ∑ i, μ i • gen i := by
    rw [farkas]
    rintro ⟨y, hy, hyw⟩
    obtain ⟨d0, hd0, hgd0⟩ := hcq
    set d := -y with hd
    have hgd : 0 ≤ g ⬝ᵥ d := by
      have := hy (Sum.inl ())
      simp only [gen, Sum.elim_inl] at this
      rw [hd, dotProduct_neg, dotProduct_comm]; linarith
    have hdl : ∀ l, z l = 0 → 0 ≤ d l := by
      intro l hl
      have := hy (Sum.inr ⟨l, hl⟩)
      simp only [gen, Sum.elim_inr, dotProduct_single, mul_one] at this
      simp only [hd, Pi.neg_apply]; linarith
    have hwd : w ⬝ᵥ d < 0 := by rw [hd, dotProduct_neg, dotProduct_comm]; linarith
    -- perturb by the qualification direction
    set ε := -(w ⬝ᵥ d) / (2 * (|w ⬝ᵥ d0| + 1)) with hε
    have hεpos : 0 < ε := div_pos (by linarith) (by positivity)
    set e := d + ε • d0 with he
    have hge : 0 < g ⬝ᵥ e := by
      rw [he, dotProduct_add, dotProduct_smul, smul_eq_mul]; nlinarith
    have hwe : w ⬝ᵥ e < 0 := by
      rw [he, dotProduct_add, dotProduct_smul, smul_eq_mul]
      have h1 : ε * (w ⬝ᵥ d0) ≤ ε * |w ⬝ᵥ d0| := mul_le_mul_of_nonneg_left (le_abs_self _)
        hεpos.le
      have h2 : ε * (|w ⬝ᵥ d0| + 1) = -(w ⬝ᵥ d) / 2 := by rw [hε]; field_simp
      nlinarith
    have hel : ∀ l, z l = 0 → 0 ≤ e l := fun l hl => by
      simp only [he, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact add_nonneg (hdl l hl) (mul_nonneg hεpos.le (hd0 l hl))
    -- feasibility along `z + t e` for small `t > 0`
    have hline := mc_line_hasDerivAt hf.hasFDerivAt e
    rw [hgrad] at hline
    have hfup := eventually_lt_of_hasDerivAt_neg hline.neg (neg_lt_zero.mpr hge)
    have hpos : ∀ l, ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 ≤ z l + t * e l := by
      intro l
      by_cases hl : z l = 0
      · filter_upwards [self_mem_nhdsWithin] with t ht
        rw [hl, zero_add]; exact mul_nonneg (le_of_lt ht) (hel l hl)
      · have hzl : 0 < z l := lt_of_le_of_ne (hz.1.1 l) (Ne.symm hl)
        have hc : Continuous fun t : ℝ => z l + t * e l := by fun_prop
        have := hc.continuousAt (x := 0) |>.eventually (eventually_gt_nhds (by simpa using hzl))
        exact (Filter.Eventually.filter_mono nhdsWithin_le_nhds this).mono fun t ht => ht.le
    obtain ⟨t, ⟨htf, htpos⟩, ht⟩ := ((hfup.and (eventually_all.mpr hpos)).and
      self_mem_nhdsWithin).exists
    simp only [Pi.neg_apply, zero_smul, add_zero, neg_lt_neg_iff] at htf
    have htz : (0 : ℝ) < t := ht
    have hmem : z + t • e ∈ inputReq f q := by
      refine ⟨fun l => ?_, by rw [← hbind]; exact htf.le⟩
      simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using htpos l
    have := hz.2 _ hmem
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul] at this
    nlinarith
  obtain ⟨μ, hμ, hwμ⟩ := hcone
  set lam := μ (Sum.inl ())
  have hwsplit : ∀ l, w l = lam * partialF f z l + ∑ i : {l // z l = 0}, μ (Sum.inr i) *
      (Pi.single i.1 1 : Fin n → ℝ) l := by
    intro l
    have := congrFun hwμ l
    rw [Fintype.sum_sum_type] at this
    simpa [gen, Finset.sum_apply, lam] using this
  refine ⟨lam, hμ _, fun l => ?_, ?_⟩
  · rw [hwsplit l]
    have : 0 ≤ ∑ i : {l // z l = 0}, μ (Sum.inr i) * (Pi.single i.1 1 : Fin n → ℝ) l :=
      Finset.sum_nonneg fun i _ => mul_nonneg (hμ _)
        ((Pi.single_nonneg.mpr zero_le_one : (0 : Fin n → ℝ) ≤ Pi.single i.1 1) l)
    linarith
  · apply Finset.sum_eq_zero
    intro l _
    change (w l - lam * partialF f z l) * z l = 0
    rw [hwsplit l, add_sub_cancel_left, Finset.sum_mul]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hil : i.1 = l
    · rw [← hil, i.2, mul_zero]
    · simp [Ne.symm hil]

/-- **(5.C.4)** needs a constraint qualification (correction): for `f(z) = (z - 1)³ + 1` (one
input, increasing), `w = 1` and `q = 1`, the CMP is solved by `z* = 1`, where `f'(1) = 0`, and no
`λ` satisfies `w ≥ λf'(z*)` with `[w - λf'(z*)]z* = 0`. -/
theorem foc_5_C_4_needs_cq :
    let f : (Fin 1 → ℝ) → ℝ := fun z => (z 0 - 1) ^ 3 + 1
    (1 : Fin 1 → ℝ) ∈ condDemand f 1 1 ∧ partialF f 1 0 = 0 ∧
      ¬ ∃ lam : ℝ, (fun l => (1 : Fin 1 → ℝ) l - lam * partialF f 1 l) ⬝ᵥ 1 = 0 := by
  intro f
  have hpart : partialF f 1 0 = 0 := by
    have hd : DifferentiableAt ℝ f 1 := by fun_prop
    have h1 := mc_line_hasDerivAt hd.hasFDerivAt (Pi.single 0 1)
    have heq : (fun t : ℝ => f (1 + t • Pi.single 0 1)) = fun t => t ^ 3 + 1 := by
      funext t; simp [f]
    rw [heq] at h1
    have h2 : HasDerivAt (fun t : ℝ => t ^ 3 + 1) (↑3 * (0 : ℝ) ^ 2) 0 :=
      (hasDerivAt_pow 3 (0 : ℝ)).add_const 1
    have := h1.unique h2
    simpa [partialF] using this
  refine ⟨⟨⟨fun _ => zero_le_one, by simp [f]⟩, fun z hz => ?_⟩, hpart, ?_⟩
  · have h1 : (1 : ℝ) ≤ (z 0 - 1) ^ 3 + 1 := hz.2
    have h2 : 0 ≤ (z 0 - 1) ^ 3 := by linarith
    have h3 : 1 ≤ z 0 := by
      by_contra h
      have : (z 0 - 1) ^ 3 < 0 := Odd.pow_neg (by decide) (by linarith)
      linarith
    simp [dotProduct]; linarith
  · rintro ⟨lam, h⟩
    simp [dotProduct, hpart] at h

/-! ### Exercise 5.C.6 -/

/-- **Exercise 5.C.6(a)-(b)** (MWG, p. 161). Let `z(p)` be the profit-maximizing input vector as a
differentiable function of the output price near `p̄ > 0` (the implicit function theorem gives
it when `D²f(z̄)` is invertible), satisfying the first-order conditions `p∇f(z(p)) = w̄`, with
`∇f` differentiable at `z̄ = z(p̄)` with negative definite Hessian `H`, and `w̄ ≫ 0`. Then
(a) output rises with the price, `dq/dp = ∇f(z̄)·z'(p̄) > 0`, and (b) some input demand rises. -/
theorem exercise_5_C_6_ab (hn : 0 < n) {G : (Fin n → ℝ) → (Fin n → ℝ)}
    {H : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)} {zf : ℝ → Fin n → ℝ} {zp w : Fin n → ℝ} {p : ℝ}
    (hp : 0 < p) (hw : StrictlyPositive w) (hfoc : ∀ᶠ t in 𝓝 p, t • G (zf t) = w)
    (hzd : HasDerivAt zf zp p) (hG : HasFDerivAt G H (zf p)) (hneg : NegDef (jacobian H)) :
    0 < G (zf p) ⬝ᵥ zp ∧ ∃ l, 0 < zp l := by
  have hcomp : HasDerivAt (fun t => G (zf t)) (H zp) p := hG.comp_hasDerivAt p hzd
  have hprod : HasDerivAt (fun t => t • G (zf t)) (p • H zp + (1 : ℝ) • G (zf p)) p :=
    (hasDerivAt_id p).smul hcomp
  have hconst : HasDerivAt (fun t => t • G (zf t)) 0 p :=
    (hasDerivAt_const p w).congr_of_eventuallyEq hfoc
  have hid : p • H zp + G (zf p) = 0 := by
    have := hprod.unique hconst
    rwa [one_smul] at this
  have hgpos : ∀ l, 0 < G (zf p) l := by
    intro l
    have h1 := congrFun hfoc.self_of_nhds l
    simp only [Pi.smul_apply, smul_eq_mul] at h1
    have := hw l
    rw [← h1] at this
    exact pos_of_mul_pos_right this hp.le
  have hzp0 : zp ≠ 0 := by
    intro h0
    rw [h0, map_zero, smul_zero, zero_add] at hid
    have := hgpos ⟨0, hn⟩
    rw [hid] at this
    exact lt_irrefl 0 this
  have hq := hneg zp hzp0
  rw [jacobian_mulVec] at hq
  have hG' : G (zf p) = -(p • H zp) := by
    rw [add_comm] at hid
    exact eq_neg_of_add_eq_zero_left hid
  have hdot : G (zf p) ⬝ᵥ zp = -p * (zp ⬝ᵥ H zp) := by
    rw [hG', neg_dotProduct, smul_dotProduct, smul_eq_mul, dotProduct_comm]; ring
  have ha : 0 < G (zf p) ⬝ᵥ zp := by rw [hdot]; nlinarith
  refine ⟨ha, ?_⟩
  by_contra hall
  push Not at hall
  have : G (zf p) ⬝ᵥ zp ≤ 0 :=
    Finset.sum_nonpos fun l _ => mul_nonpos_of_nonneg_of_nonpos (hgpos l).le (hall l)
  linarith

/-- **Exercise 5.C.6(c)** (MWG, p. 161). Under the same hypotheses, with `z(w_ℓ)` the
profit-maximizing input vector as a differentiable function of the `ℓ`-th input price
(`p̄∇f(z) = w̄ + t e_ℓ`), the demand for input `ℓ` falls: `∂z_ℓ/∂w_ℓ < 0`. -/
theorem exercise_5_C_6_c {G : (Fin n → ℝ) → (Fin n → ℝ)} {H : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)}
    {zf : ℝ → Fin n → ℝ} {zl w : Fin n → ℝ} {p : ℝ} (hp : 0 < p) (l : Fin n)
    (hfoc : ∀ᶠ t in 𝓝 0, p • G (zf t) = w + t • Pi.single l 1) (hzd : HasDerivAt zf zl 0)
    (hG : HasFDerivAt G H (zf 0)) (hneg : NegDef (jacobian H)) :
    p • H zl = Pi.single l 1 ∧ zl l < 0 := by
  have hcomp : HasDerivAt (fun t => p • G (zf t)) (p • H zl) 0 :=
    (hG.comp_hasDerivAt 0 hzd).const_smul p
  have hrhs : HasDerivAt (fun t : ℝ => w + t • (Pi.single l 1 : Fin n → ℝ)) (Pi.single l 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single l 1 : Fin n → ℝ)).const_add w
  have hid : p • H zl = Pi.single l 1 := hcomp.unique (hrhs.congr_of_eventuallyEq hfoc)
  refine ⟨hid, ?_⟩
  have hzl0 : zl ≠ 0 := by
    intro h0
    rw [h0, map_zero, smul_zero] at hid
    have := congrFun hid l
    simp at this
  have hq := hneg zl hzl0
  rw [jacobian_mulVec] at hq
  have hH : H zl = p⁻¹ • Pi.single l 1 := by
    rw [← hid, smul_smul, inv_mul_cancel₀ hp.ne', one_smul]
  rw [hH, dotProduct_smul, dotProduct_single, mul_one, smul_eq_mul] at hq
  have := mul_neg_iff.mp hq
  rcases this with ⟨h1, h2⟩ | ⟨h1, _⟩
  · exact h2
  · exact absurd h1 (not_lt.mpr (inv_nonneg.mpr hp.le))

/-! ### Exercise 5.C.7 -/

open Matrix in
/-- **Exercise 5.C.7** (MWG, p. 161), corrected (two inputs): if the Hessian `H` is negative
definite with positive cross partials (`∂²f/∂z₁∂z₂ > 0`, complementary inputs), then the solution
`v` of `pHv = e_k` (the derivative of the input demands in `w_k`) has `v_ℓ < 0` for `ℓ ≠ k`, and the
solution of `pHv = -∇f` (the derivative in `p`) is `≫ 0` when `∇f ≫ 0`. -/
theorem exercise_5_C_7_corrected {H : Matrix (Fin 2) (Fin 2) ℝ} (hneg : NegDef H)
    (h01 : 0 < H 0 1) (h10 : 0 < H 1 0) {p : ℝ} (hp : 0 < p) :
    (∀ v : Fin 2 → ℝ, p • H *ᵥ v = Pi.single 1 1 → v 0 < 0) ∧
      (∀ v : Fin 2 → ℝ, p • H *ᵥ v = Pi.single 0 1 → v 1 < 0) ∧
      (∀ g v : Fin 2 → ℝ, StrictlyPositive g → p • H *ᵥ v = -g → 0 < v 0 ∧ 0 < v 1) := by
  have ha : H 0 0 < 0 := by
    have := hneg ![1, 0] (by intro h; simpa using congrFun h 0)
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have hd : H 1 1 < 0 := by
    have := hneg ![0, 1] (by intro h; simpa using congrFun h 1)
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have hdet : 0 < H 0 0 * H 1 1 - H 0 1 * H 1 0 := by
    have := hneg ![H 1 1 - H 1 0, H 0 0 - H 0 1] ?_
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at this
      nlinarith
    · intro h
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      simp at h0 h1
      linarith
  have hsolve : ∀ v r : Fin 2 → ℝ, p • H *ᵥ v = r →
      p * (H 0 0 * v 0 + H 0 1 * v 1) = r 0 ∧ p * (H 1 0 * v 0 + H 1 1 * v 1) = r 1 := by
    intro v r h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
    constructor <;> linarith
  have hdp := mul_pos hdet hp
  refine ⟨fun v hv => ?_, fun v hv => ?_, fun g v hg hv => ?_⟩
  · obtain ⟨e0, e1⟩ := hsolve v _ hv
    simp only [Fin.isValue, ne_eq, zero_ne_one, not_false_eq_true, Pi.single_eq_of_ne,
      Pi.single_eq_same] at e0 e1
    have key : (H 0 0 * H 1 1 - H 0 1 * H 1 0) * p * v 0 = -H 0 1 := by
      linear_combination H 1 1 * e0 - H 0 1 * e1
    by_contra hv0
    push Not at hv0
    nlinarith
  · obtain ⟨e0, e1⟩ := hsolve v _ hv
    simp only [Fin.isValue, ne_eq, one_ne_zero, not_false_eq_true, Pi.single_eq_of_ne,
      Pi.single_eq_same] at e0 e1
    have key : (H 0 0 * H 1 1 - H 0 1 * H 1 0) * p * v 1 = -H 1 0 := by
      linear_combination H 0 0 * e1 - H 1 0 * e0
    by_contra hv1
    push Not at hv1
    nlinarith
  · obtain ⟨e0, e1⟩ := hsolve v _ hv
    have g0 := hg 0
    have g1 := hg 1
    simp only [Pi.neg_apply] at e0 e1
    have key0 : (H 0 0 * H 1 1 - H 0 1 * H 1 0) * p * v 0 = -H 1 1 * g 0 + H 0 1 * g 1 := by
      linear_combination H 1 1 * e0 - H 0 1 * e1
    have key1 : (H 0 0 * H 1 1 - H 0 1 * H 1 0) * p * v 1 = -H 0 0 * g 1 + H 1 0 * g 0 := by
      linear_combination H 0 0 * e1 - H 1 0 * e0
    constructor
    · by_contra h; push Not at h; nlinarith
    · by_contra h; push Not at h; nlinarith

open Matrix in
/-- **Exercise 5.C.7** (MWG, p. 161) is false as printed (correction): with negative cross
partials the cross-price effects are positive. For the negative definite Hessian
`H = [[-3/4, -1/4], [-1/4, -3/4]]` (that of `f(z) = -e^{-z₁} - e^{-z₂} - e^{-z₁-z₂}` at
`z₁ = z₂ = ln 2`, an increasing, strictly concave `f` with `∂²f/∂z₁∂z₂ < 0`) and `p = 1`, any
differentiable input demand satisfying the first-order conditions has `∂z₁/∂w₂ = 1/2 > 0`. -/
theorem exercise_5_C_7_counterexample :
    let H : Matrix (Fin 2) (Fin 2) ℝ := !![-3 / 4, -1 / 4; -1 / 4, -3 / 4]
    NegDef H ∧ H 0 1 < 0 ∧ ∀ v : Fin 2 → ℝ, (1 : ℝ) • H *ᵥ v = Pi.single 1 1 → v 0 = 1 / 2 := by
  intro H
  refine ⟨fun z hz => ?_, by simp [H]; norm_num, fun v hv => ?_⟩
  · have : z 0 ≠ 0 ∨ z 1 ≠ 0 := by
      by_contra h
      push Not at h
      exact hz (funext fun i => by fin_cases i <;> simp [h.1, h.2])
    have hform : z ⬝ᵥ H *ᵥ z = -(3 / 4) * z 0 ^ 2 - (1 / 2) * z 0 * z 1 - (3 / 4) * z 1 ^ 2 := by
      simp [H, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      ring
    rw [hform]
    rcases this with h | h
    · have := sq_pos_of_ne_zero h; nlinarith [sq_nonneg (z 0 + z 1), sq_nonneg (z 1)]
    · have := sq_pos_of_ne_zero h; nlinarith [sq_nonneg (z 0 + z 1), sq_nonneg (z 0)]
  · have h0 := congrFun hv 0
    have h1 := congrFun hv 1
    simp [H, dotProduct, Fin.sum_univ_two] at h0 h1
    linarith

/-! ### Exercise 5.C.8 -/

/-- **Exercise 5.C.8** (MWG, p. 161). The observations of months 3 and 95 (both producing
`q = 60` at output price `4`; month 3 inputs `(40, 50)` at prices `(3, 1)`, month 95 inputs
`(55, 40)` at prices `(2, 2)`) cannot both be profit maximizing for any fixed technology: at
month-95 prices the month-3 plan is more profitable (`60 > 50`); the month-95 inputs are not
cost minimizing. -/
theorem exercise_5_C_8 (Y : Set (Fin 3 → ℝ)) :
    ¬ ((![-40, -50, 60] : Fin 3 → ℝ) ∈ supply Y ![3, 1, 4] ∧
      (![-55, -40, 60] : Fin 3 → ℝ) ∈ supply Y ![2, 2, 4]) := by
  rintro ⟨h3, h95⟩
  have := h95.2 _ h3.1
  simp [dotProduct, Fin.sum_univ_three] at this
  norm_num at this

/-! ### Exercises 5.C.9 and 5.C.10 -/

/-- **Exercise 5.C.10(a)** (MWG, p. 162). For `f(z) = z₁ + z₂` (perfect substitutes), `w ≫ 0` and
`q ≥ 0`: `c(w, q) = q min{w₁, w₂}`. -/
theorem exercise_5_C_10a {w : Fin 2 → ℝ} (hw : StrictlyPositive w) {q : ℝ} (hq : 0 ≤ q) :
    costFn (fun z => z 0 + z 1) w q = q * min (w 0) (w 1) := by
  apply le_antisymm
  · rcases le_total (w 0) (w 1) with h | h
    · rw [min_eq_left h]
      have hm : (![q, 0] : Fin 2 → ℝ) ∈ inputReq (fun z => z 0 + z 1) q :=
        ⟨fun i => by fin_cases i <;> simp [hq], by simp⟩
      calc costFn (fun z => z 0 + z 1) w q ≤ w ⬝ᵥ ![q, 0] :=
            supportFn_le (bddBelow_of_subset_nonneg (inputReq_subset_nonneg _ q)
              (fun i => (hw i).le)) hm
        _ = q * w 0 := by simp [dotProduct, Fin.sum_univ_two]; ring
    · rw [min_eq_right h]
      have hm : (![0, q] : Fin 2 → ℝ) ∈ inputReq (fun z => z 0 + z 1) q :=
        ⟨fun i => by fin_cases i <;> simp [hq], by simp⟩
      calc costFn (fun z => z 0 + z 1) w q ≤ w ⬝ᵥ ![0, q] :=
            supportFn_le (bddBelow_of_subset_nonneg (inputReq_subset_nonneg _ q)
              (fun i => (hw i).le)) hm
        _ = q * w 1 := by simp [dotProduct, Fin.sum_univ_two]; ring
  · have hne : (inputReq (fun z : Fin 2 → ℝ => z 0 + z 1) q).Nonempty :=
      ⟨![q, 0], fun i => by fin_cases i <;> simp [hq], by simp⟩
    apply le_supportFn hne
    intro z hz
    have h0 : 0 ≤ z 0 := hz.1 0
    have h1 : 0 ≤ z 1 := hz.1 1
    have hq' : q ≤ z 0 + z 1 := hz.2
    simp only [dotProduct, Fin.sum_univ_two]
    have m0 := min_le_left (w 0) (w 1)
    have m1 := min_le_right (w 0) (w 1)
    have hmin : 0 ≤ min (w 0) (w 1) := le_min (hw 0).le (hw 1).le
    nlinarith

/-- **Exercise 5.C.10(b)** (MWG, p. 162). For the Leontief technology `f(z) = min{z₁, z₂}`,
`w ≫ 0` and `q ≥ 0`: `c(w, q) = q(w₁ + w₂)` and `z(w, q) = {(q, q)}`. -/
theorem exercise_5_C_10b {w : Fin 2 → ℝ} (hw : StrictlyPositive w) {q : ℝ} (hq : 0 ≤ q) :
    condDemand (fun z => min (z 0) (z 1)) w q = {![q, q]} ∧
      costFn (fun z => min (z 0) (z 1)) w q = q * (w 0 + w 1) := by
  have hmem : (![q, q] : Fin 2 → ℝ) ∈ inputReq (fun z => min (z 0) (z 1)) q :=
    ⟨fun i => by fin_cases i <;> simp [hq], by simp⟩
  have hdem : condDemand (fun z => min (z 0) (z 1)) w q = {![q, q]} := by
    ext z
    simp only [Set.mem_singleton_iff]
    constructor
    · rintro ⟨hz, hmin⟩
      have h1 := hmin _ hmem
      have a0 : q ≤ z 0 := (le_min_iff.mp hz.2).1
      have a1 : q ≤ z 1 := (le_min_iff.mp hz.2).2
      simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h1
      have e0 : z 0 = q := by nlinarith [hw 0, hw 1]
      have e1 : z 1 = q := by nlinarith [hw 0, hw 1]
      funext i; fin_cases i <;> simp [e0, e1]
    · rintro rfl
      refine ⟨hmem, fun z hz => ?_⟩
      have a0 : q ≤ z 0 := (le_min_iff.mp hz.2).1
      have a1 : q ≤ z 1 := (le_min_iff.mp hz.2).2
      simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      nlinarith [hw 0, hw 1]
  refine ⟨hdem, ?_⟩
  have hx : (![q, q] : Fin 2 → ℝ) ∈ condDemand (fun z => min (z 0) (z 1)) w q := by
    rw [hdem]; rfl
  rw [costFn, supportFn_eq_of_mem_argmin hx]
  simp [dotProduct, Fin.sum_univ_two]; ring

/-- **Exercise 5.C.10(c)** (MWG, p. 162). For the CES technology `f(z) = (z₁^ρ + z₂^ρ)^{1/ρ}`
(`ρ < 1`, `ρ ≠ 0`), the CMP is the EMP of Exercise 3.E.6: `c(w, q) = q(w₁^r + w₂^r)^{1/r}` with
`r = ρ/(ρ-1)`, and `z(w, q)` is the CES Hicksian demand. (`ρ = 1` is part (a).) -/
theorem exercise_5_C_10c {ρ : ℝ} (hρ1 : ρ < 1) (hρ0 : ρ ≠ 0) {w : Fin 2 → ℝ}
    (hw : StrictlyPositive w) {q : ℝ} (hq : 0 ≤ q) :
    costFn (cesUtility ρ) w q = q * cesSum ρ w ^ (1 / cesR ρ) ∧
      condDemand (cesUtility ρ) w q = {cesHicks ρ w q} := by
  have hV : inputReq (cesUtility ρ) q = empConstraintSet (cesUtility ρ) q := by
    ext z; exact ⟨fun h => ⟨fun l => h.1 l, h.2⟩, fun h => ⟨fun l => h.1 l, h.2⟩⟩
  constructor
  · rw [costFn, hV, ← expenditure_eq_supportFn, exercise_3_E_6_expenditure hρ1 hρ0 hw hq]
    rfl
  · rw [condDemand, hV]
    exact exercise_3_E_6_hicksian hρ1 hρ0 hw hq

/-- **Exercise 5.C.9(a)** (MWG, p. 161). For `f(z) = √(z₁ + z₂)`, `w ≫ 0`, `p > 0`, with
`m = min{w₁, w₂}`: profits satisfy `pf(z) - w·z ≤ p²/(4m)` for every `z ≥ 0`, with equality at
`q = p/(2m)` using only the cheaper input; so `π(p, w) = p²/(4m)`. -/
theorem exercise_5_C_9a {w : Fin 2 → ℝ} (hw : StrictlyPositive w) {p : ℝ} (hp : 0 < p) :
    (∀ z : Fin 2 → ℝ, 0 ≤ z →
      p * Real.sqrt (z 0 + z 1) - w ⬝ᵥ z ≤ p ^ 2 / (4 * min (w 0) (w 1))) ∧
    ∃ z : Fin 2 → ℝ, 0 ≤ z ∧
      p * Real.sqrt (z 0 + z 1) - w ⬝ᵥ z = p ^ 2 / (4 * min (w 0) (w 1)) := by
  set m := min (w 0) (w 1) with hm
  have hm0 : 0 < m := lt_min (hw 0) (hw 1)
  constructor
  · intro z hz
    have h0 : 0 ≤ z 0 := hz 0
    have h1 : 0 ≤ z 1 := hz 1
    set s := Real.sqrt (z 0 + z 1)
    have hs : s ^ 2 = z 0 + z 1 := Real.sq_sqrt (by linarith)
    have hwz : m * (z 0 + z 1) ≤ w ⬝ᵥ z := by
      simp only [dotProduct, Fin.sum_univ_two]
      nlinarith [min_le_left (w 0) (w 1), min_le_right (w 0) (w 1)]
    rw [le_div_iff₀ (by positivity)]
    have h4 := mul_le_mul_of_nonneg_left hwz (by positivity : (0 : ℝ) ≤ 4 * m)
    have h5 : 4 * m * (m * s ^ 2) ≤ 4 * m * (w ⬝ᵥ z) := by rw [hs]; exact h4
    nlinarith [sq_nonneg (2 * m * s - p), h5]
  · set q := p / (2 * m)
    have hq : 0 ≤ q := by positivity
    rcases le_total (w 0) (w 1) with h | h
    · refine ⟨![q ^ 2, 0], fun i => by fin_cases i <;> simp [sq_nonneg], ?_⟩
      have hmw : m = w 0 := min_eq_left h
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, add_zero, Real.sqrt_sq hq,
        dotProduct, Fin.sum_univ_two, mul_zero]
      simp only [q, hmw]
      have := hw 0
      field_simp
      ring
    · refine ⟨![0, q ^ 2], fun i => by fin_cases i <;> simp [sq_nonneg], ?_⟩
      have hmw : m = w 1 := min_eq_right h
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zero_add, Real.sqrt_sq hq,
        dotProduct, Fin.sum_univ_two, mul_zero]
      simp only [q, hmw]
      have := hw 1
      field_simp
      ring

/-- **Exercise 5.C.9(b)** (MWG, p. 162). For `f(z) = √(min{z₁, z₂})`, `w ≫ 0`, `p > 0`: profits
are at most `p²/(4(w₁ + w₂))`, attained at `z₁ = z₂ = (p/(2(w₁ + w₂)))²`. -/
theorem exercise_5_C_9b {w : Fin 2 → ℝ} (hw : StrictlyPositive w) {p : ℝ} (hp : 0 < p) :
    (∀ z : Fin 2 → ℝ, 0 ≤ z →
      p * Real.sqrt (min (z 0) (z 1)) - w ⬝ᵥ z ≤ p ^ 2 / (4 * (w 0 + w 1))) ∧
    p * Real.sqrt (min ((p / (2 * (w 0 + w 1))) ^ 2) ((p / (2 * (w 0 + w 1))) ^ 2)) -
      w ⬝ᵥ ![(p / (2 * (w 0 + w 1))) ^ 2, (p / (2 * (w 0 + w 1))) ^ 2] =
        p ^ 2 / (4 * (w 0 + w 1)) := by
  have hW : 0 < w 0 + w 1 := add_pos (hw 0) (hw 1)
  constructor
  · intro z hz
    have h0 : 0 ≤ z 0 := hz 0
    have h1 : 0 ≤ z 1 := hz 1
    set mz := min (z 0) (z 1)
    have hmz : 0 ≤ mz := le_min h0 h1
    set s := Real.sqrt mz
    have hs : s ^ 2 = mz := Real.sq_sqrt hmz
    have hwz : (w 0 + w 1) * mz ≤ w ⬝ᵥ z := by
      simp only [dotProduct, Fin.sum_univ_two]
      nlinarith [min_le_left (z 0) (z 1), min_le_right (z 0) (z 1), hw 0, hw 1]
    rw [le_div_iff₀ (by positivity)]
    have h4 := mul_le_mul_of_nonneg_left hwz (by positivity : (0 : ℝ) ≤ 4 * (w 0 + w 1))
    have h5 : 4 * (w 0 + w 1) * ((w 0 + w 1) * s ^ 2) ≤ 4 * (w 0 + w 1) * (w ⬝ᵥ z) := by
      rw [hs]; exact h4
    nlinarith [sq_nonneg (2 * (w 0 + w 1) * s - p), h5]
  · rw [min_self, Real.sqrt_sq (by positivity)]
    simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp
    ring

/-! ### Exercises 5.C.11-5.C.13 -/

/-- **Exercise 5.C.11** (MWG, p. 162). If `c` is twice differentiable near `(w̄, q̄)` (with
derivative `c'` and second derivative `c''`), then by Shephard's lemma `z_ℓ = ∂c/∂w_ℓ`, and
`∂z_ℓ/∂q = ∂(∂c/∂q)/∂w_ℓ` (symmetry of the second derivative); hence `∂z_ℓ/∂q > 0` iff marginal cost
is increasing in `w_ℓ`. -/
theorem exercise_5_C_11 {c : (Fin n → ℝ) × ℝ → ℝ} {c' : (Fin n → ℝ) × ℝ → (Fin n → ℝ) × ℝ →L[ℝ] ℝ}
    {c'' : (Fin n → ℝ) × ℝ →L[ℝ] (Fin n → ℝ) × ℝ →L[ℝ] ℝ} {x : (Fin n → ℝ) × ℝ}
    (hc : ∀ᶠ y in 𝓝 x, HasFDerivAt c (c' y) y) (hc' : HasFDerivAt c' c'' x) (l : Fin n) :
    c'' (0, 1) (Pi.single l 1, 0) = c'' (Pi.single l 1, 0) (0, 1) ∧
      (0 < c'' (0, 1) (Pi.single l 1, 0) ↔ 0 < c'' (Pi.single l 1, 0) (0, 1)) := by
  have := second_derivative_symmetric_of_eventually hc hc' (0, 1) (Pi.single l 1, 0)
  exact ⟨this, by rw [this]⟩

/-- **Exercise 5.C.12** (MWG, p. 162). Let `Y' = {α(y, -1) : y ∈ Y, α ≥ 0}` (Proposition 5.B.2).
If `y ∈ y(p)`, then `(y, -1)` maximizes profits on `Y'` at prices `(p, π(p))`; conversely, if
`(y, -1)` maximizes profits on `Y'` at `(p, p_{L+1})`, then `y ∈ y(p)` and `π(p) = p_{L+1}`. -/
theorem exercise_5_C_12 {L : ℕ} (Y : Set (Fin L → ℝ)) (p y : Fin L → ℝ) (pL : ℝ) :
    let Y' : Set (Fin (L + 1) → ℝ) := {v | ∃ y ∈ Y, ∃ α : ℝ, 0 ≤ α ∧ v = α • extendVec y (-1)}
    (y ∈ supply Y p → extendVec y (-1) ∈ supply Y' (extendVec p (p ⬝ᵥ y))) ∧
      (y ∈ Y → extendVec y (-1) ∈ supply Y' (extendVec p pL) → y ∈ supply Y p ∧ p ⬝ᵥ y = pL) := by
  intro Y'
  have hdot : ∀ (u : Fin L → ℝ) (a b : ℝ) (v : Fin L → ℝ),
      extendVec u a ⬝ᵥ extendVec v b = u ⬝ᵥ v + a * b := by
    intro u a b v
    simp only [extendVec, dotProduct, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
  constructor
  · intro hy
    refine ⟨⟨y, hy.1, 1, zero_le_one, by rw [one_smul]⟩, ?_⟩
    rintro _ ⟨y', hy', α, hα, rfl⟩
    rw [dotProduct_smul, hdot, hdot, smul_eq_mul]
    have := hy.2 y' hy'
    nlinarith
  · intro hyY hy
    have h0 : (0 : Fin (L + 1) → ℝ) ∈ Y' := ⟨y, hyY, 0, le_rfl, by rw [zero_smul]⟩
    have hmax0 := hy.2 0 h0
    rw [dotProduct_zero, hdot] at hmax0
    have hle : ∀ y' ∈ Y, p ⬝ᵥ y' - pL ≤ p ⬝ᵥ y - pL := by
      intro y' hy'
      have := hy.2 _ ⟨y', hy', 1, zero_le_one, rfl⟩
      rw [one_smul, hdot, hdot] at this
      linarith
    have hge : 0 ≤ p ⬝ᵥ y - pL := by linarith
    have hle0 : p ⬝ᵥ y - pL ≤ 0 := by
      have := hy.2 (2 • extendVec y (-1)) ⟨y, hyY, 2, by norm_num, rfl⟩
      rw [dotProduct_smul, hdot, smul_eq_mul] at this
      linarith
    exact ⟨⟨hyY, fun y' hy' => by linarith [hle y' hy']⟩, by linarith⟩

/-- **Exercise 5.C.13** (MWG, p. 162). A revenue-maximizing firm with cash constraint `w·z ≤ C`
and maximal output `f*(w, C)` with `pf*(w, C) = R(p, w, C) = p[γ + ln C - α ln w₁ - (1-α) ln w₂]`:
at its choice `z ≫ 0` (on the budget line, `f(z) = f*(w̄, C̄)`) the use of input 1 is
`z₁ = αC̄/w̄₁` (Roy's identity: `z` remains affordable when prices move along `C = w·z`, so
`w ↦ f*(w, w·z)` is minimized at `w̄`). -/
theorem exercise_5_C_13 {γ α : ℝ} {f : (Fin 2 → ℝ) → ℝ} {w z : Fin 2 → ℝ} {C : ℝ}
    (hw : StrictlyPositive w) (hC : 0 < C) (hz : StrictlyPositive z) (hbud : w ⬝ᵥ z = C)
    (hval : f z = γ + Real.log C - α * Real.log (w 0) - (1 - α) * Real.log (w 1))
    (hbound : ∀ (w' : Fin 2 → ℝ) (C' : ℝ), StrictlyPositive w' → 0 < C' → w' ⬝ᵥ z ≤ C' →
      f z ≤ γ + Real.log C' - α * Real.log (w' 0) - (1 - α) * Real.log (w' 1)) :
    z 0 = α * C / w 0 := by
  -- `g(t) = value at prices (w₁ + t, w₂) and budget (w₁ + t)z₁ + w₂z₂` is minimized at `t = 0`
  set g : ℝ → ℝ := fun t => γ + Real.log ((w 0 + t) * z 0 + w 1 * z 1) - α * Real.log (w 0 + t)
    - (1 - α) * Real.log (w 1)
  have hCe : w 0 * z 0 + w 1 * z 1 = C := by rw [← hbud]; simp [dotProduct, Fin.sum_univ_two]
  have hmin : IsLocalMin g 0 := by
    have hev : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < w 0 + t :=
      (continuous_const.add continuous_id).continuousAt.eventually
        (eventually_gt_nhds (by simpa using hw 0))
    filter_upwards [hev] with t ht
    have hw' : StrictlyPositive ![w 0 + t, w 1] := fun i => by fin_cases i <;> simp [ht, hw 1]
    have hC' : 0 < (w 0 + t) * z 0 + w 1 * z 1 := by nlinarith [hz 0, hz 1, hw 1]
    have := hbound ![w 0 + t, w 1] _ hw' hC' (by simp [dotProduct, Fin.sum_univ_two])
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
    simp only [g, add_zero, hCe]
    linarith
  have hd : HasDerivAt g (z 0 / C - α / w 0) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => (w 0 + t) * z 0 + w 1 * z 1) (z 0) 0 := by
      simpa using (((hasDerivAt_id (0 : ℝ)).const_add (w 0)).mul_const (z 0)).add_const
        (w 1 * z 1)
    have h2 := h1.log (by simp [hCe, hC.ne'])
    have h3 : HasDerivAt (fun t : ℝ => w 0 + t) 1 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_add (w 0)
    have h4 := (h3.log (by simp [(hw 0).ne'])).const_mul α
    have h5 := ((h2.const_add γ).sub h4).sub_const ((1 - α) * Real.log (w 1))
    simp only [add_zero, hCe] at h5
    convert h5 using 1
    ring
  have := hmin.hasDerivAt_eq_zero hd
  have hw0 := (hw 0).ne'
  field_simp at this ⊢
  linarith

end MWG.Production
