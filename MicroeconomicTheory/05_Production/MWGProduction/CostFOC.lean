/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGProduction.Cost

/-!
# Cost minimization: first-order conditions, marginal cost, multiple outputs

MWG Section 5.C, pp. 139-141.

* Footnote 8: the first-order conditions (5.C.4) are sufficient when `f` is quasiconcave
  (`foc_5_C_4_sufficient`), with the complementary-slackness condition `λ(f(z*) - q) = 0`
  that (5.C.4) leaves implicit.
* p. 140: the multiplier `λ` is the marginal cost `∂c(w, q)/∂q` (`lambda_eq_marginal_cost`, for
  concave `f`, via the subgradient inequality `cost_lambda_subgradient`).
* Footnote 9: (5.C.4) with `λ = p` is (5.C.2) (`footnote_5_C_9`).
* (5.C.5)-(5.C.6): the output choice `max_{q ≥ 0} pq - c(w, q)` (`foc_5_C_6`), sufficient for
  convex `c(w, ·)` (`foc_5_C_6_sufficient`).
* **Exercise 5.C.4**: properties (i)-(vii) of Proposition 5.C.2 for multiple outputs.
-/

namespace MWG.Production

open MWG.ClassicalDemand MWG.ConsumerChoice Filter Topology

variable {n : ℕ}

/-- For `f` quasiconcave on `ℝ^n_+` and differentiable at `z* ≥ 0`, `f(z) ≥ f(z*)` with `z ≥ 0`
implies `∇f(z*)·(z - z*) ≥ 0`. -/
theorem quasiconcave_grad_nonneg {f : (Fin n → ℝ) → ℝ}
    (hq : QuasiconcaveOn ℝ {z : Fin n → ℝ | 0 ≤ z} f) {x z : Fin n → ℝ} (hx : 0 ≤ x)
    (hz : 0 ≤ z) (hf : DifferentiableAt ℝ f x) (hfz : f x ≤ f z) :
    0 ≤ fderiv ℝ f x (z - x) := by
  have hd := mc_line_hasDerivAt hf.hasFDerivAt (z - x)
  apply mc_le_deriv_of_slope hd
  intro t ht0 ht1
  have hmem := hq (f x) ⟨hx, le_rfl⟩ ⟨hz, hfz⟩ (by linarith : (0 : ℝ) ≤ 1 - t) ht0.le
    (by ring)
  have heq : (1 - t) • x + t • z = x + t • (z - x) := by module
  rw [heq] at hmem
  simp only [zero_smul, add_zero]
  exact div_nonneg (by linarith [hmem.2]) ht0.le

/-- **Section 5.C** (MWG, p. 140, footnote 8). Sufficiency of the first-order conditions (5.C.4)
for quasiconcave `f`: if `z* ≥ 0`, `f(z*) ≥ q`, `λ ≥ 0` with `λ(f(z*) - q) = 0`,
`w ≥ λ∇f(z*)` and `[w - λ∇f(z*)]·z* = 0`, then `z*` solves the CMP. -/
theorem foc_5_C_4_sufficient {f : (Fin n → ℝ) → ℝ}
    (hq : QuasiconcaveOn ℝ {z : Fin n → ℝ | 0 ≤ z} f) {w z : Fin n → ℝ} {q lam : ℝ}
    (hz : 0 ≤ z) (hfz : q ≤ f z) (hf : DifferentiableAt ℝ f z) (hlam : 0 ≤ lam)
    (hcs : lam * (f z - q) = 0) (hw : ∀ l, lam * partialF f z l ≤ w l)
    (hcs' : (fun l => w l - lam * partialF f z l) ⬝ᵥ z = 0) :
    z ∈ condDemand f w q := by
  refine ⟨⟨hz, hfz⟩, fun z' hz' => ?_⟩
  have hgrad : ∀ v, fderiv ℝ f z v = (fun l => partialF f z l) ⬝ᵥ v := fun v => by
    rw [fderiv_apply_eq_gradient_dot]
    rfl
  have h1 : (fun l => lam * partialF f z l) ⬝ᵥ z' ≤ w ⬝ᵥ z' := by
    apply Finset.sum_le_sum
    intro l _
    exact mul_le_mul_of_nonneg_right (hw l) (hz'.1 l)
  have h2 : w ⬝ᵥ z = (fun l => lam * partialF f z l) ⬝ᵥ z := by
    have : (fun l => w l - lam * partialF f z l) ⬝ᵥ z =
        w ⬝ᵥ z - (fun l => lam * partialF f z l) ⬝ᵥ z := by
      simp only [dotProduct, ← Finset.sum_sub_distrib, sub_mul]
    linarith
  have hsm : ∀ v, (fun l => lam * partialF f z l) ⬝ᵥ v = lam * fderiv ℝ f z v := fun v => by
    rw [hgrad]
    simp only [dotProduct, Finset.mul_sum, mul_assoc]
  rcases hlam.lt_or_eq with hpos | hzero
  · have hbind : f z = q := by
      rcases mul_eq_zero.mp hcs with h | h
      · exact absurd h hpos.ne'
      · linarith
    have h3 := quasiconcave_grad_nonneg hq hz hz'.1 hf (hbind ▸ hz'.2)
    have h4 : (fun l => lam * partialF f z l) ⬝ᵥ (z' - z) ≥ 0 := by
      rw [hsm]
      exact mul_nonneg hpos.le h3
    rw [dotProduct_sub] at h4
    linarith
  · subst hzero
    have : (fun l => (0 : ℝ) * partialF f z l) = 0 := by funext l; simp
    rw [this, zero_dotProduct] at h1 h2
    linarith

/-- **Section 5.C** (MWG, p. 140). For concave `f`, the multiplier `λ` of (5.C.4) at a binding
solution is a subgradient of `c(w, ·)` at `q̄`: `c(w, q) ≥ c(w, q̄) + λ(q - q̄)`. -/
theorem cost_lambda_subgradient {f : (Fin n → ℝ) → ℝ}
    (hc : ConcaveOn ℝ {z : Fin n → ℝ | 0 ≤ z} f) {w z : Fin n → ℝ} {qb lam : ℝ}
    (hz : z ∈ condDemand f w qb) (hbind : f z = qb) (hf : DifferentiableAt ℝ f z)
    (hlam : 0 ≤ lam) (hw : ∀ l, lam * partialF f z l ≤ w l)
    (hcs' : (fun l => w l - lam * partialF f z l) ⬝ᵥ z = 0) {q : ℝ}
    (hne : (inputReq f q).Nonempty) :
    costFn f w qb + lam * (q - qb) ≤ costFn f w q := by
  apply le_csInf (hne.image _)
  rintro _ ⟨z', hz', rfl⟩
  have hcost : costFn f w qb = w ⬝ᵥ z := supportFn_eq_of_mem_argmin hz
  rw [hcost]
  have htan := concave_le_tangent hc hz.1.1 hz'.1 hf
  have hgrad : fderiv ℝ f z (z' - z) = (fun l => partialF f z l) ⬝ᵥ (z' - z) := by
    rw [fderiv_apply_eq_gradient_dot]
    rfl
  rw [hgrad, hbind] at htan
  have h1 : (fun l => lam * partialF f z l) ⬝ᵥ z' ≤ w ⬝ᵥ z' := by
    apply Finset.sum_le_sum
    intro l _
    exact mul_le_mul_of_nonneg_right (hw l) (hz'.1 l)
  have h2 : w ⬝ᵥ z = (fun l => lam * partialF f z l) ⬝ᵥ z := by
    have : (fun l => w l - lam * partialF f z l) ⬝ᵥ z =
        w ⬝ᵥ z - (fun l => lam * partialF f z l) ⬝ᵥ z := by
      simp only [dotProduct, ← Finset.sum_sub_distrib, sub_mul]
    linarith
  have hsm : ∀ v, (fun l => lam * partialF f z l) ⬝ᵥ v =
      lam * ((fun l => partialF f z l) ⬝ᵥ v) := fun v => by
    simp only [dotProduct, Finset.mul_sum, mul_assoc]
  rw [hsm] at h1 h2
  change w ⬝ᵥ z + lam * (q - qb) ≤ w ⬝ᵥ z'
  have h3 : q - qb ≤ (fun l => partialF f z l) ⬝ᵥ (z' - z) := by linarith [hz'.2]
  rw [dotProduct_sub] at h3
  nlinarith [mul_le_mul_of_nonneg_left h3 hlam]

/-- **Section 5.C** (MWG, p. 140). "`λ` equals `∂c(w, q)/∂q`, the marginal cost of production":
for concave `f`, if `c(w, ·)` has derivative `d` at `q̄` (with nearby outputs producible), then
`d = λ`. -/
theorem lambda_eq_marginal_cost {f : (Fin n → ℝ) → ℝ}
    (hc : ConcaveOn ℝ {z : Fin n → ℝ | 0 ≤ z} f) {w z : Fin n → ℝ} {qb lam : ℝ}
    (hz : z ∈ condDemand f w qb) (hbind : f z = qb) (hf : DifferentiableAt ℝ f z)
    (hlam : 0 ≤ lam) (hw : ∀ l, lam * partialF f z l ≤ w l)
    (hcs' : (fun l => w l - lam * partialF f z l) ⬝ᵥ z = 0)
    (hnear : ∀ᶠ q in 𝓝 qb, (inputReq f q).Nonempty) {d : ℝ}
    (hd : HasDerivAt (fun q => costFn f w q) d qb) : d = lam := by
  have hmin : IsLocalMin (fun q => costFn f w q - lam * q) qb := by
    filter_upwards [hnear] with q hq
    have := cost_lambda_subgradient hc hz hbind hf hlam hw hcs' hq
    linarith
  have hd' : HasDerivAt (fun q => costFn f w q - lam * q) (d - lam) qb := by
    have h := hd.fun_sub ((hasDerivAt_id qb).const_mul lam)
    simp only [id, mul_one] at h
    exact h
  have := hmin.hasDerivAt_eq_zero hd'
  linarith

/-- **Footnote 9** (MWG, p. 141). The first-order conditions (5.C.4) of the CMP with `λ = p`
are the conditions (5.C.2) of the PMP. -/
theorem footnote_5_C_9 (f : (Fin n → ℝ) → ℝ) (w z : Fin n → ℝ) (p : ℝ) :
    ((∀ l, p * partialF f z l ≤ w l) ∧ (fun l => p * partialF f z l - w l) ⬝ᵥ z = 0) ↔
      ((∀ l, p * partialF f z l ≤ w l) ∧ (fun l => w l - p * partialF f z l) ⬝ᵥ z = 0) := by
  have : (fun l => w l - p * partialF f z l) ⬝ᵥ z =
      -((fun l => p * partialF f z l - w l) ⬝ᵥ z) := by
    simp only [dotProduct, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [this, neg_eq_zero]

/-- The tangent inequality for a convex function of one variable at a point of
differentiability. -/
theorem convex_tangent_le {S : Set ℝ} {C : ℝ → ℝ} (hC : ConvexOn ℝ S C) {x y d : ℝ}
    (hx : x ∈ S) (hy : y ∈ S) (hd : HasDerivAt C d x) : C x + d * (y - x) ≤ C y := by
  have hline : HasDerivAt (fun t : ℝ => C (x + t * (y - x)) - t * (C y - C x))
      (d * (y - x) - (C y - C x)) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => x + t * (y - x)) (y - x) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (y - x)).const_add x
    have hd' : HasDerivAt C d (x + 0 * (y - x)) := by simpa using hd
    have h2 := hd'.comp (0 : ℝ) h1
    have h3 := (hasDerivAt_id (0 : ℝ)).mul_const (C y - C x)
    have h4 := h2.fun_sub h3
    simp only [Function.comp_apply, id, one_mul] at h4
    exact h4
  have := hasDerivAt_nonpos_of_right_le hline ?_
  · linarith
  have hI : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < 1 := nhdsWithin_le_nhds (eventually_lt_nhds one_pos)
  filter_upwards [self_mem_nhdsWithin, hI] with t ht ht1
  have ht0 : (0 : ℝ) < t := ht
  have hconv := hC.2 hx hy (by linarith : (0 : ℝ) ≤ 1 - t) ht0.le (by ring)
  simp only [smul_eq_mul] at hconv
  have heq : (1 - t) * x + t * y = x + t * (y - x) := by ring
  rw [heq] at hconv
  simp only [zero_mul, add_zero, sub_zero]
  linarith

/-- **Section 5.C** (MWG, p. 141), condition (5.C.6). If `q* ≥ 0` solves (5.C.5),
`max_{q ≥ 0} pq - C(q)`, and `C` is differentiable at `q*`, then `p - C'(q*) ≤ 0`, with equality
if `q* > 0`: at an interior optimum, price equals marginal cost. -/
theorem foc_5_C_6 {C : ℝ → ℝ} {p q d : ℝ} (hq : 0 ≤ q)
    (hopt : ∀ q', 0 ≤ q' → p * q' - C q' ≤ p * q - C q) (hd : HasDerivAt C d q) :
    p - d ≤ 0 ∧ (0 < q → p = d) := by
  have hline : HasDerivAt (fun t : ℝ => p * (q + t) - C (q + t)) (p - d) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => q + t) 1 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_add q
    have hd' : HasDerivAt C d (q + 0) := by simpa using hd
    have h2 := hd'.comp (0 : ℝ) h1
    have h3 := h1.const_mul p
    have h4 := h3.fun_sub h2
    simp only [Function.comp_apply, mul_one] at h4
    exact h4
  have hle : p - d ≤ 0 := by
    apply hasDerivAt_nonpos_of_right_le hline
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : (0 : ℝ) < t := ht
    simpa using hopt (q + t) (by linarith)
  refine ⟨hle, fun hqpos => ?_⟩
  have hl' := hline
  rw [← neg_zero] at hl'
  have hneg := hl'.comp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))
  have := hasDerivAt_nonpos_of_right_le hneg ?_
  · simp only [mul_neg, mul_one] at this
    linarith
  have hI : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < q := nhdsWithin_le_nhds (eventually_lt_nhds hqpos)
  filter_upwards [hI] with t ht
  simp only [Function.comp_apply, neg_zero, add_zero]
  have := hopt (q + -t) (by linarith)
  exact this

/-- **Section 5.C** (MWG, p. 141). If `C` is convex on `[0, ∞)`, the condition (5.C.6) is
sufficient for `q* ≥ 0` to solve (5.C.5). -/
theorem foc_5_C_6_sufficient {C : ℝ → ℝ} (hC : ConvexOn ℝ (Set.Ici 0) C) {p q d : ℝ}
    (hq : 0 ≤ q) (hd : HasDerivAt C d q) (hle : p - d ≤ 0) (heq : 0 < q → p = d) :
    ∀ q', 0 ≤ q' → p * q' - C q' ≤ p * q - C q := by
  intro q' hq'
  have htan := convex_tangent_le hC (Set.mem_Ici.mpr hq) (Set.mem_Ici.mpr hq') hd
  rcases hq.lt_or_eq with hpos | hzero
  · rw [heq hpos] at *
    linarith
  · subst hzero
    nlinarith

/-! ### Exercise 5.C.4: multiple outputs -/

/-- The input requirement set of a multiple-output technology `T` (pairs `(z, q)` of inputs and
outputs): `V(q) = {z ≥ 0 : (z, q) ∈ T}`. -/
def inputReqMulti {m : ℕ} (T : Set ((Fin n → ℝ) × (Fin m → ℝ))) (q : Fin m → ℝ) :
    Set (Fin n → ℝ) :=
  {z | 0 ≤ z ∧ (z, q) ∈ T}

/-- The cost function `c(w, q)` of a multiple-output technology. -/
noncomputable def costMulti {m : ℕ} (T : Set ((Fin n → ℝ) × (Fin m → ℝ))) (w : Fin n → ℝ)
    (q : Fin m → ℝ) : ℝ :=
  supportFn (inputReqMulti T q) w

/-- The conditional factor demand of a multiple-output technology. -/
def condDemandMulti {m : ℕ} (T : Set ((Fin n → ℝ) × (Fin m → ℝ))) (w : Fin n → ℝ)
    (q : Fin m → ℝ) : Set (Fin n → ℝ) :=
  supportArgmin (inputReqMulti T q) w

theorem inputReqMulti_subset {m : ℕ} (T : Set ((Fin n → ℝ) × (Fin m → ℝ))) (q : Fin m → ℝ) :
    inputReqMulti T q ⊆ {z | 0 ≤ z} := fun _ hz => hz.1

/-- **Exercise 5.C.4(i)** (MWG, p. 161). For multiple outputs, `c(·, q)` is homogeneous of degree
one in `w`, and nondecreasing in `q` under free disposal of outputs. -/
theorem exercise_5_C_4_i {m : ℕ} (T : Set ((Fin n → ℝ) × (Fin m → ℝ))) :
    (∀ (w : Fin n → ℝ) q (α : ℝ), 0 ≤ α → costMulti T (α • w) q = α * costMulti T w q) ∧
      ((∀ z q q', q ≤ q' → (z, q') ∈ T → (z, q) ∈ T) → ∀ (w : Fin n → ℝ), 0 ≤ w →
        ∀ q q', q ≤ q' → (inputReqMulti T q').Nonempty → costMulti T w q ≤ costMulti T w q') :=
  ⟨fun _ _ _ hα => vcost_smul _ _ hα, fun hfd _ hw q q' hqq hne =>
    vcost_mono (inputReqMulti_subset T q) (fun _ hz => ⟨hz.1, hfd _ q q' hqq hz.2⟩) hne hw⟩

/-- **Exercise 5.C.4(ii)** (MWG, p. 161): `c(·, q)` is concave in `w`. -/
theorem exercise_5_C_4_ii {m : ℕ} (T : Set ((Fin n → ℝ) × (Fin m → ℝ))) {q : Fin m → ℝ}
    (hne : (inputReqMulti T q).Nonempty) :
    ConcaveOn ℝ {w : Fin n → ℝ | 0 ≤ w} (fun w => costMulti T w q) :=
  vcost_concaveOn (inputReqMulti_subset T q) hne

/-- **Exercise 5.C.4(iii)** (MWG, p. 161): if every `V(q)` is closed, convex and has free
disposal of inputs, then `(z, q) ∈ T` with `z ≥ 0` iff `w·z ≥ c(w, q)` for all `w ≫ 0`. -/
theorem exercise_5_C_4_iii {m : ℕ} (T : Set ((Fin n → ℝ) × (Fin m → ℝ)))
    (hcl : ∀ q, IsClosed (inputReqMulti T q)) (hc : ∀ q, Convex ℝ (inputReqMulti T q))
    (hup : ∀ q, ∀ z ∈ inputReqMulti T q, ∀ z', z ≤ z' → z' ∈ inputReqMulti T q)
    (z : Fin n → ℝ) (q : Fin m → ℝ) :
    z ∈ inputReqMulti T q ↔ ∀ w : Fin n → ℝ, StrictlyPositive w →
      supportFnE (inputReqMulti T q) w ≤ ((w ⬝ᵥ z : ℝ) : EReal) :=
  vcost_iii (hcl q) (hc q) (hup q) (inputReqMulti_subset T q) z

/-- **Exercise 5.C.4(iv)** (MWG, p. 161): `z(·, q)` is homogeneous of degree zero in `w`. -/
theorem exercise_5_C_4_iv {m : ℕ} (T : Set ((Fin n → ℝ) × (Fin m → ℝ))) (w : Fin n → ℝ)
    (q : Fin m → ℝ) {α : ℝ} (hα : 0 < α) : condDemandMulti T (α • w) q = condDemandMulti T w q :=
  vdemand_smul _ w hα

/-- **Exercise 5.C.4(v)** (MWG, p. 161): convex `V(q)` gives convex `z(w, q)`; strictly convex
`V(q)` gives at most one element (`w ≠ 0`). -/
theorem exercise_5_C_4_v {m : ℕ} (T : Set ((Fin n → ℝ) × (Fin m → ℝ))) (q : Fin m → ℝ)
    (w : Fin n → ℝ) :
    (Convex ℝ (inputReqMulti T q) → Convex ℝ (condDemandMulti T w q)) ∧
      (StrictConvex ℝ (inputReqMulti T q) → w ≠ 0 → (condDemandMulti T w q).Subsingleton) :=
  ⟨fun hc => vdemand_convex hc w, fun hsc hw => vdemand_strict hsc hw⟩

/-- **Exercise 5.C.4(vi)** (MWG, p. 161), Shephard's lemma for multiple outputs. -/
theorem exercise_5_C_4_vi {m : ℕ} (T : Set ((Fin n → ℝ) × (Fin m → ℝ))) {q : Fin m → ℝ}
    (hcl : IsClosed (inputReqMulti T q)) {w z : Fin n → ℝ} (hw : StrictlyPositive w)
    (hz : condDemandMulti T w q = {z}) :
    HasFDerivAt (fun w => costMulti T w q) (dualityDotCLM z) w :=
  vcost_shephard hcl (inputReqMulti_subset T q) hw hz

/-- **Exercise 5.C.4(vii)** (MWG, p. 161): `D_w z(w̄, q) = D²_w c(w̄, q)`, symmetric and negative
semidefinite, with `D_w z(w̄, q) w̄ = 0`. -/
theorem exercise_5_C_4_vii {m : ℕ} (T : Set ((Fin n → ℝ) × (Fin m → ℝ))) {q : Fin m → ℝ}
    (hcl : IsClosed (inputReqMulti T q)) {zs : (Fin n → ℝ) → (Fin n → ℝ)} {w : Fin n → ℝ}
    (hw : StrictlyPositive w) (hzs : ∀ᶠ v in 𝓝 w, condDemandMulti T v q = {zs v})
    {D : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)} (hD : HasFDerivAt zs D w) :
    hessianMatrix (fun w => costMulti T w q) w = jacobian D ∧
      (∀ i j, jacobian D i j = jacobian D j i) ∧ NegSemidef (jacobian D) ∧ D w = 0 :=
  vdemand_derivative hcl (inputReqMulti_subset T q) hw hzs hD

end MWG.Production
