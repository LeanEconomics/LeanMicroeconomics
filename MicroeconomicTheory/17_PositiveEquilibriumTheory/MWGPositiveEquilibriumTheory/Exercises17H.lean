/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPositiveEquilibriumTheory.Regularity
import MWGPositiveEquilibriumTheory.CobbDouglasEconomy
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Complex.Basic

/-!
# Exercises 17.H.2-17.H.3 and Figure 17.H.2 (MWG pp. 622-623, 648)

* The two-dimensional stability criterion (`rh2`): both roots of `μ² - Tμ + D` (the eigenvalues
  of a `2 × 2` matrix with trace `T` and determinant `D`) have negative real parts iff `T < 0` and
  `D > 0`; both have positive real parts iff `T > 0` and `D > 0` (`rh2_pos`); for `D < 0` they are
  real of opposite signs, a saddle (`saddle2`).
* **Figure 17.H.2** (`figure_17_H_2_index`): with `L = 3`, the index of a regular equilibrium is
  `sign |Dẑ| = sign |CDẑ|`: `+1` for a locally stable or locally totally unstable linearization,
  `-1` for a saddle, as labelled in the figure.
* **Exercise 17.H.2**: Walras price dynamics `dp/dt = z(p) - s(p)` and Marshall quantity dynamics
  `dq/dt = z⁻¹(q) - p(q)` (`ex17H2Walras`, `ex17H2Marshall`, part (a)); (b) with nearly constant
  returns the Walrasian slope `z'(1) - 1/ε` is negative while the Marshallian slope `1/z'(1) - ε`
  is negative iff `z'(1) < 0` (`exercise_17_H_2b`); (c) the joint dynamics
  `(dp/dt, dq/dt) = (z(p) - q, p - P(q))` have Jacobian `[[z'(1), -1], [1, -ε]]` and spiral
  (complex eigenvalues) when `|z'(1) + ε| < 2` (`exercise_17_H_2c`); (d) for small `ε` the joint
  system is locally stable iff the equilibrium is Marshallian stable (`exercise_17_H_2d`), which
  fails for larger `ε` (`exercise_17_H_2d_small_needed`); (e) with constant returns and constant
  excess demand the orbits are circles (`exercise_17_H_2e_circles`), and letting quantities also
  respond to the excess demand is stabilizing (`exercise_17_H_2e_stabilizing`).
* **Exercise 17.H.3**: drawing; a saddle has index `-1` (`figure_17_H_2_index`), so by the index
  theorem a unique equilibrium (index `+1`) cannot be a saddle (`exercise_17_H_3`, with the
  Cobb-Douglas instance `exercise_17_H_3_cd`). Stability here is read off the linearization.
-/

namespace MWG.PositiveEquilibriumTheory

open Filter Topology Set

/-! ### The two-dimensional criterion -/

/-- Both roots of `μ² - Tμ + D` have negative real parts iff `T < 0` and `D > 0`. -/
theorem rh2 (T D : ℝ) :
    (∀ μ : ℂ, μ ^ 2 - T * μ + D = 0 → μ.re < 0) ↔ (T < 0 ∧ 0 < D) := by
  constructor
  · intro h
    by_cases hΔ : 0 ≤ T ^ 2 - 4 * D
    · set r := Real.sqrt (T ^ 2 - 4 * D) with hrdef
      have hr : r ^ 2 = T ^ 2 - 4 * D := Real.sq_sqrt hΔ
      have hr0 : 0 ≤ r := Real.sqrt_nonneg _
      have hreal : ((T + r) / 2) ^ 2 - T * ((T + r) / 2) + D = 0 := by nlinarith
      have h1 := h (((T + r) / 2 : ℝ) : ℂ) (by exact_mod_cast hreal)
      rw [Complex.ofReal_re] at h1
      refine ⟨by linarith, ?_⟩
      nlinarith
    · push Not at hΔ
      set s := Real.sqrt (4 * D - T ^ 2) with hsdef
      have hs : s ^ 2 = 4 * D - T ^ 2 := Real.sq_sqrt (by linarith)
      have h1 := h ⟨T / 2, s / 2⟩ (by
        apply Complex.ext
        · simp [pow_two]
          nlinarith
        · simp [pow_two]
          ring)
      simp only at h1
      refine ⟨by linarith, by nlinarith [sq_nonneg T]⟩
  · rintro ⟨hT, hD⟩ μ hμ
    have hre : μ.re * μ.re - μ.im * μ.im - T * μ.re + D = 0 := by
      have := congrArg Complex.re hμ
      simpa [pow_two] using this
    have him : μ.re * μ.im + μ.im * μ.re - T * μ.im = 0 := by
      have := congrArg Complex.im hμ
      simpa [pow_two] using this
    by_cases hy : μ.im = 0
    · rw [hy] at hre
      by_contra hx
      push Not at hx
      nlinarith
    · have h2 : (2 * μ.re - T) * μ.im = 0 := by linarith
      have := (mul_eq_zero.1 h2).resolve_right hy
      linarith

/-- Both roots of `μ² - Tμ + D` have positive real parts iff `T > 0` and `D > 0`. -/
theorem rh2_pos (T D : ℝ) :
    (∀ μ : ℂ, μ ^ 2 - T * μ + D = 0 → 0 < μ.re) ↔ (0 < T ∧ 0 < D) := by
  have key : (∀ μ : ℂ, μ ^ 2 - T * μ + D = 0 → 0 < μ.re) ↔
      (∀ ν : ℂ, ν ^ 2 - ((-T : ℝ) : ℂ) * ν + D = 0 → ν.re < 0) := by
    constructor
    · intro h ν hν
      have := h (-ν) (by rw [← hν]; push_cast; ring)
      simpa using this
    · intro h μ hμ
      have := h (-μ) (by rw [← hμ]; push_cast; ring)
      simpa using this
  rw [key, rh2 (-T) D]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, h2⟩

/-- For `D < 0` the roots of `μ² - Tμ + D` are real, one negative and one positive: a saddle. -/
theorem saddle2 {T D : ℝ} (hD : D < 0) :
    ∃ μ₁ μ₂ : ℝ, μ₁ < 0 ∧ 0 < μ₂ ∧ μ₁ ^ 2 - T * μ₁ + D = 0 ∧ μ₂ ^ 2 - T * μ₂ + D = 0 := by
  set r := Real.sqrt (T ^ 2 - 4 * D) with hrdef
  have hr : r ^ 2 = T ^ 2 - 4 * D := Real.sq_sqrt (by nlinarith [sq_nonneg T])
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hrT : |T| < r := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) (by linarith)
  refine ⟨(T - r) / 2, (T + r) / 2, ?_, ?_, by nlinarith, by nlinarith⟩
  · linarith [le_abs_self T]
  · linarith [neg_abs_le T]

/-! ### Figure 17.H.2: the indices of stable, unstable and saddle equilibria -/

/-- **Figure 17.H.2** (MWG, p. 623). With `L = 3` and speeds `c ≫ 0`, let `M = C Dẑ(p̂)` be the
linearization of the normalized dynamics at a regular equilibrium. Its eigenvalues are the roots of
`μ² - (tr M)μ + |M|`. If both have negative real parts (locally stable) or both positive real
parts (locally totally unstable), the index is `+1`; if `|M| < 0` (a saddle), it is `-1`. -/
theorem figure_17_H_2_index (z : (Fin 3 → ℝ) → Fin 3 → ℝ) (q : Fin 2 → ℝ) {c : Fin 2 → ℝ}
    (hc : ∀ l, 0 < c l) :
    let M := Matrix.diagonal c * LinearMap.toMatrix' (fderiv ℝ (normED z) q).toLinearMap
    M.charpoly = Polynomial.X ^ 2 - Polynomial.C M.trace * Polynomial.X +
        Polynomial.C M.det ∧
      ((∀ μ : ℂ, μ ^ 2 - M.trace * μ + M.det = 0 → μ.re < 0) → eqmIndex z q = 1) ∧
      ((∀ μ : ℂ, μ ^ 2 - M.trace * μ + M.det = 0 → 0 < μ.re) → eqmIndex z q = 1) ∧
      (M.det < 0 → eqmIndex z q = -1) := by
  intro M
  have hdetM : M.det = c 0 * c 1 * (fderiv ℝ (normED z) q).det := by
    simp only [M, Matrix.det_mul, Matrix.det_diagonal, Fin.prod_univ_two,
      LinearMap.det_toMatrix']
  have hc01 : 0 < c 0 * c 1 := mul_pos (hc 0) (hc 1)
  have hidx_pos : 0 < M.det → eqmIndex z q = 1 := fun h => by
    have : 0 < (fderiv ℝ (normED z) q).det := by
      rw [hdetM] at h; exact pos_of_mul_pos_right h hc01.le
    simp [eqmIndex, sign_pos this]
  refine ⟨?_, fun h => hidx_pos ((rh2 _ _).1 h).2, fun h => hidx_pos ((rh2_pos _ _).1 h).2,
    fun h => ?_⟩
  · rw [Matrix.charpoly_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two]
  · have : (fderiv ℝ (normED z) q).det < 0 := by
      rw [hdetM] at h
      exact neg_of_mul_neg_right h hc01.le
    simp [eqmIndex, sign_neg this]

/-! ### Exercise 17.H.2 -/

/-- **Exercise 17.H.2(a)** (MWG, p. 648). Walras price dynamics: `dp/dt = z(p) - s(p)`, excess
demand of the consumers minus the (direct) supply at `p`. -/
def ex17H2Walras (z s : ℝ → ℝ) (p : ℝ) : ℝ := z p - s p

/-- **Exercise 17.H.2(a)** (MWG, p. 648). Marshall quantity dynamics: `dq/dt = D(q) - P(q)`, the
demand price `D = z⁻¹` minus the supply price `P` at the quantity `q`. -/
def ex17H2Marshall (D P : ℝ → ℝ) (q : ℝ) : ℝ := D q - P q

/-- **Exercise 17.H.2(b)** (MWG, p. 648). Near constant returns (`P'(1) = ε` small), around the
equilibrium `(1, 1)` the Walras dynamics are stable (slope `z'(1) - 1/ε < 0`), while the Marshall
dynamics are stable (slope `1/z'(1) - ε < 0`) iff the excess demand slopes down (`z'(1) < 0`).
The slopes are those of the inverse functions `s = P⁻¹`, `D = z⁻¹`. -/
theorem exercise_17_H_2b {a : ℝ} (ha : a ≠ 0) :
    ∃ ε₀ > 0, ∀ ε, 0 < ε → ε < ε₀ → ∀ z s D P : ℝ → ℝ, HasDerivAt z a 1 →
      HasDerivAt P ε 1 → s 1 = 1 → ContinuousAt s 1 → (∀ᶠ y in 𝓝 1, P (s y) = y) →
      D 1 = 1 → ContinuousAt D 1 → (∀ᶠ y in 𝓝 1, z (D y) = y) →
      (HasDerivAt (ex17H2Walras z s) (a - ε⁻¹) 1 ∧ a - ε⁻¹ < 0) ∧
        (HasDerivAt (ex17H2Marshall D P) (a⁻¹ - ε) 1 ∧ (a⁻¹ - ε < 0 ↔ a < 0)) := by
  refine ⟨|a|⁻¹, inv_pos.2 (abs_pos.2 ha), fun ε hε hεa z s D P hz hP hs1 hsc hsP hD1 hDc hzD =>
    ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩⟩
  · have hs : HasDerivAt s ε⁻¹ 1 :=
      HasDerivAt.of_local_left_inverse hsc (by rw [hs1]; exact hP) hε.ne' hsP
    exact hz.sub hs
  · have h1 : ε * |a| < 1 := by
      rw [inv_eq_one_div, lt_div_iff₀ (abs_pos.2 ha)] at hεa; linarith
    have h2 : a * ε < 1 := by nlinarith [le_abs_self a]
    have h3 : a < ε⁻¹ := by rw [inv_eq_one_div, lt_div_iff₀ hε]; exact h2
    linarith
  · have hDd : HasDerivAt D a⁻¹ 1 :=
      HasDerivAt.of_local_left_inverse hDc (by rw [hD1]; exact hz) ha hzD
    exact hDd.sub hP
  · have h1 : ε * |a| < 1 := by
      rw [inv_eq_one_div, lt_div_iff₀ (abs_pos.2 ha)] at hεa; linarith
    constructor
    · intro h
      by_contra hpos
      push Not at hpos
      have hapos : 0 < a := lt_of_le_of_ne hpos (Ne.symm ha)
      rw [abs_of_pos hapos] at h1
      have : ε < a⁻¹ := by rw [inv_eq_one_div, lt_div_iff₀ hapos]; linarith
      linarith
    · intro h
      have := inv_lt_zero.2 h
      linarith


/-- The Jacobian `[[z'(1), -1], [1, -ε]]` of the joint dynamics of Exercise 17.H.2(c). -/
def ex17H2J (a ε : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![a, -1; 1, -ε]

/-- **Exercise 17.H.2(c)** (MWG, p. 648). Prices move à la Walras and quantities à la Marshall:
`dp/dt = z(p) - q`, `dq/dt = p - P(q)`. At `(1, 1)` the Jacobian is `[[z'(1), -1], [1, -ε]]`
(trace `z'(1) - ε`, determinant `1 - z'(1)ε`), and when `|z'(1) + ε| < 2` (the typical case of
small slopes) it has no real eigenvalue: the trajectories spiral around the equilibrium. -/
theorem exercise_17_H_2c {z P : ℝ → ℝ} {a ε : ℝ} (hz : HasDerivAt z a 1)
    (hP : HasDerivAt P ε 1) :
    HasFDerivAt (fun v : Fin 2 → ℝ => ![z (v 0) - v 1, v 0 - P (v 1)])
      (LinearMap.toContinuousLinearMap (Matrix.toLin' (ex17H2J a ε))) ![1, 1] ∧
      (ex17H2J a ε).trace = a - ε ∧ (ex17H2J a ε).det = 1 - a * ε ∧
      (|a + ε| < 2 → ∀ μ : ℝ, μ ^ 2 - (a - ε) * μ + (1 - a * ε) ≠ 0) := by
  refine ⟨?_, by simp [ex17H2J, Matrix.trace_fin_two]; ring,
    by simp [ex17H2J, Matrix.det_fin_two]; ring, fun h μ hμ => ?_⟩
  · rw [hasFDerivAt_pi']
    have hp0 := hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 2 => ℝ) (0 : Fin 2) ![(1 : ℝ), 1]
    have hp1 := hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 2 => ℝ) (1 : Fin 2) ![(1 : ℝ), 1]
    have hz' : HasDerivAt z a ((fun v : Fin 2 → ℝ => v 0) ![1, 1]) := by simpa using hz
    have hP' : HasDerivAt P ε ((fun v : Fin 2 → ℝ => v 1) ![1, 1]) := by simpa using hP
    intro i
    fin_cases i
    · have h := (hz'.comp_hasFDerivAt (x := ![(1 : ℝ), 1]) hp0).sub hp1
      have hfun : (fun v : Fin 2 → ℝ => (![z (v 0) - v 1, v 0 - P (v 1)] : Fin 2 → ℝ)
          ((fun i => i) ⟨0, by norm_num⟩)) = (z ∘ fun v : Fin 2 → ℝ => v 0) - fun v => v 1 := by
        funext v; simp
      rw [hfun]
      refine h.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
      simp [ex17H2J, dotProduct, Fin.sum_univ_two]
      ring
    · have h := hp0.sub (hP'.comp_hasFDerivAt (x := ![(1 : ℝ), 1]) hp1)
      have hfun : (fun v : Fin 2 → ℝ => (![z (v 0) - v 1, v 0 - P (v 1)] : Fin 2 → ℝ)
          ((fun i => i) ⟨1, by norm_num⟩)) = (fun v : Fin 2 → ℝ => v 0) - P ∘ fun v => v 1 := by
        funext v; simp
      rw [hfun]
      refine h.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
      simp [ex17H2J, dotProduct, Fin.sum_univ_two]
      ring
  · have h2 : (a + ε) ^ 2 < 4 := by
      have := abs_lt.1 h
      nlinarith
    nlinarith [sq_nonneg (2 * μ - (a - ε))]

/-- **Exercise 17.H.2(d)** (MWG, p. 648). With the technology of (b) (`ε` small), the joint system
of (c) is locally stable (both eigenvalues of the Jacobian with negative real part) iff the
equilibrium is Marshallian stable (`1/z'(1) - ε < 0`). -/
theorem exercise_17_H_2d {a : ℝ} (ha : a ≠ 0) :
    ∃ ε₀ > 0, ∀ ε, 0 < ε → ε < ε₀ →
      ((∀ μ : ℂ, μ ^ 2 - ((a - ε : ℝ) : ℂ) * μ + ((1 - a * ε : ℝ) : ℂ) = 0 → μ.re < 0) ↔
        a⁻¹ - ε < 0) := by
  have hpos : 0 < |a| := abs_pos.2 ha
  refine ⟨min |a| |a|⁻¹, lt_min hpos (inv_pos.2 hpos), fun ε hε hεa => ?_⟩
  rw [rh2]
  have h1 : ε < |a| := lt_of_lt_of_le hεa (min_le_left _ _)
  have h2 : ε * |a| < 1 := by
    have := lt_of_lt_of_le hεa (min_le_right _ _)
    rw [inv_eq_one_div, lt_div_iff₀ hpos] at this; linarith
  rcases lt_or_gt_of_ne ha with hneg | hapos
  · have hi := inv_lt_zero.2 hneg
    constructor
    · intro _; linarith
    · intro _; exact ⟨by linarith, by nlinarith⟩
  · rw [abs_of_pos hapos] at h1 h2
    have hi : ε < a⁻¹ := by rw [inv_eq_one_div, lt_div_iff₀ hapos]; linarith
    constructor
    · rintro ⟨h, _⟩; linarith
    · intro h; linarith

/-- **Exercise 17.H.2(d)**, the smallness of `ε` is needed: with `z'(1) = 1/4` and `ε = 1/2` the
joint system is locally stable but the equilibrium is not Marshallian stable. -/
theorem exercise_17_H_2d_small_needed :
    (∀ μ : ℂ, μ ^ 2 - ((1 / 4 - 1 / 2 : ℝ) : ℂ) * μ + ((1 - 1 / 4 * (1 / 2) : ℝ) : ℂ) = 0 →
      μ.re < 0) ∧ ¬ ((1 / 4 : ℝ)⁻¹ - 1 / 2 < 0) := by
  refine ⟨(rh2 _ _).2 ⟨by norm_num, by norm_num⟩, by norm_num⟩

/-- **Exercise 17.H.2(e)** (MWG, p. 648). Constant returns (`P ≡ 1`) and constant excess demand
(`z ≡ 1`): the joint dynamics are `dp/dt = 1 - q`, `dq/dt = p - 1`, and every trajectory stays on
a circle `(p - 1)² + (q - 1)² = const` around the equilibrium (the phase diagram). -/
theorem exercise_17_H_2e_circles {p q : ℝ → ℝ} (hp : ∀ t, HasDerivAt p (1 - q t) t)
    (hq : ∀ t, HasDerivAt q (p t - 1) t) (t : ℝ) :
    (p t - 1) ^ 2 + (q t - 1) ^ 2 = (p 0 - 1) ^ 2 + (q 0 - 1) ^ 2 := by
  have hd : ∀ s, HasDerivAt (fun s => (p s - 1) ^ 2 + (q s - 1) ^ 2) 0 s := fun s => by
    have := (((hp s).sub_const 1).pow 2).add (((hq s).sub_const 1).pow 2)
    convert this using 1
    simp only [Nat.cast_ofNat]
    ring
  exact is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) t 0

/-- **Exercise 17.H.2(e)** (MWG, p. 648). If quantities also respond to the expected sales, i.e.
to the excess demand (`dq/dt = p - 1 + β(1 - q)`, `β > 0`), the distance to the equilibrium is
nonincreasing along every trajectory (`d/dt = -2β(q - 1)² ≤ 0`) and the linearization
`[[0, -1], [1, -β]]` has both eigenvalues with negative real part: a stabilizing effect. -/
theorem exercise_17_H_2e_stabilizing {β : ℝ} (hβ : 0 < β) {p q : ℝ → ℝ}
    (hp : ∀ t, HasDerivAt p (1 - q t) t) (hq : ∀ t, HasDerivAt q (p t - 1 + β * (1 - q t)) t) :
    Antitone (fun t => (p t - 1) ^ 2 + (q t - 1) ^ 2) ∧
      ∀ μ : ℂ, μ ^ 2 - ((-β : ℝ) : ℂ) * μ + ((1 : ℝ) : ℂ) = 0 → μ.re < 0 := by
  refine ⟨?_, (rh2 _ _).2 ⟨by linarith, one_pos⟩⟩
  have hd : ∀ s, HasDerivAt (fun s => (p s - 1) ^ 2 + (q s - 1) ^ 2)
      (-(2 * β * (q s - 1) ^ 2)) s := fun s => by
    have := (((hp s).sub_const 1).pow 2).add (((hq s).sub_const 1).pow 2)
    convert this using 1
    simp only [Nat.cast_ofNat]
    ring
  exact antitone_of_deriv_nonpos (fun s => (hd s).differentiableAt) fun s => by
    rw [(hd s).deriv]
    have := sq_nonneg (q s - 1)
    nlinarith

/-! ### Exercise 17.H.3 -/

/-- **Exercise 17.H.3** (MWG, p. 648). A regular equilibrium of index `+1` (with `L = 3`) is never
a saddle of the tâtonnement linearization `C Dẑ`, for any speeds `c ≫ 0`. By the index theorem
(Proposition 17.D.2), a unique equilibrium has index `+1`; so a single locally totally unstable
equilibrium is possible (index `+1`) but it cannot be made a saddle (index `-1`). -/
theorem exercise_17_H_3 (z : (Fin 3 → ℝ) → Fin 3 → ℝ) (q : Fin 2 → ℝ) (hidx : eqmIndex z q = 1)
    {c : Fin 2 → ℝ} (hc : ∀ l, 0 < c l) :
    ¬ (Matrix.diagonal c * LinearMap.toMatrix' (fderiv ℝ (normED z) q).toLinearMap).det < 0 :=
  fun h => by
    have := (figure_17_H_2_index z q hc).2.2.2 h
    rw [hidx] at this
    norm_num at this

/-- **Exercise 17.H.3**, instance: in a one-consumer Cobb-Douglas economy with three goods the
unique equilibrium (index `+1`, Exercise 17.D.8) is not a saddle for any speeds of adjustment. -/
theorem exercise_17_H_3_cd {a ω : Fin 3 → ℝ} (ha : ∀ l, 0 < a l) (hω : ∀ l, 0 < ω l) :
    ∃! q, IsNormEqm (cd1ED a ω) q ∧ ∀ c : Fin 2 → ℝ, (∀ l, 0 < c l) →
      ¬ (Matrix.diagonal c *
        LinearMap.toMatrix' (fderiv ℝ (normED (cd1ED a ω)) q).toLinearMap).det < 0 := by
  obtain ⟨q, ⟨hq, -, hidx⟩, huniq⟩ := exercise_17_D_8 ha hω
  refine ⟨q, ⟨hq, fun c hc => exercise_17_H_3 _ q hidx hc⟩, fun q' ⟨hq', _⟩ => ?_⟩
  have := (cd1_eqm_iff ha hω).1 hq'
  have h2 := (cd1_eqm_iff ha hω).1 hq
  exact funext fun l => by rw [this l, h2 l]

end MWG.PositiveEquilibriumTheory
