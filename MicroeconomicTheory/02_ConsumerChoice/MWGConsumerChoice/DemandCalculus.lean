/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGConsumerChoice.DemandBasics
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Topology.Order.OrderClosed

/-!
# Calculus along price–wealth lines

Supporting lemmas for the differential results of MWG, Sections 2.E–2.F (pp. 27–35). The
book differentiates identities such as `x(αp, αw) - x(p, w) = 0` or `p·x(p, w) = w` "with
respect to" a parameter. Here this is made rigorous: if `(p, w) ↦ x(p, w)` has Fréchet
derivative `D` at `(p, w)`, then along the line `t ↦ (p + t v, w + t c)` the demand has
derivative `D(v, c)`; and an identity holding on the open domain `p ≫ 0, w > 0` holds for all
`t` near `0`, so its derivative vanishes.
-/

namespace MWG.ConsumerChoice

open Filter Topology

/-- Demand along a line `t ↦ (p + t v, w + t c)` has derivative `D(v, c)` at `t₀`, when `D`
is the derivative of `x` at the point `(p + t₀ v, w + t₀ c)`. -/
theorem hasDerivAt_line {L : ℕ} {x : DemandFunction L} {p v : Fin L → ℝ} {w c t₀ : ℝ}
    {D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)}
    (hD : HasFDerivAt (Function.uncurry x) D (p + t₀ • v, w + t₀ * c)) :
    HasDerivAt (fun t : ℝ => x (p + t • v) (w + t * c)) (D (v, c)) t₀ := by
  have hγ : HasDerivAt (fun t : ℝ => ((p, w) : (Fin L → ℝ) × ℝ) + t • (v, c)) (v, c) t₀ := by
    simpa using ((hasDerivAt_id t₀).smul_const ((v, c) : (Fin L → ℝ) × ℝ)).const_add
      ((p, w) : (Fin L → ℝ) × ℝ)
  have hy : ((p + t₀ • v, w + t₀ * c) : (Fin L → ℝ) × ℝ) = (p, w) + t₀ • (v, c) := by
    simp [smul_eq_mul]
  have := hD.comp_hasDerivAt_of_eq t₀ hγ hy
  convert this using 1
  funext t
  simp [Function.uncurry, smul_eq_mul]


/-- The case `t₀ = 0`: the derivative of demand in direction `(v, c)` at `(p, w)`. -/
theorem hasDerivAt_path {L : ℕ} {x : DemandFunction L} {p : Fin L → ℝ} {w : ℝ}
    {D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)} (hD : HasFDerivAt (Function.uncurry x) D (p, w))
    (v : Fin L → ℝ) (c : ℝ) :
    HasDerivAt (fun t : ℝ => x (p + t • v) (w + t * c)) (D (v, c)) 0 :=
  hasDerivAt_line (by simpa using hD)

/-- Componentwise form of `hasDerivAt_path`. -/
theorem hasDerivAt_path_apply {L : ℕ} {x : DemandFunction L} {p : Fin L → ℝ} {w : ℝ}
    {D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)} (hD : HasFDerivAt (Function.uncurry x) D (p, w))
    (v : Fin L → ℝ) (c : ℝ) (l : Fin L) :
    HasDerivAt (fun t : ℝ => x (p + t • v) (w + t * c) l) (D (v, c) l) 0 :=
  hasDerivAt_pi.mp (hasDerivAt_path hD v c) l

/-- A line through a domain point stays in the domain for `t` near `0`. -/
theorem eventually_pwDomain {L : ℕ} {p : Fin L → ℝ} {w : ℝ} (hd : PWDomain p w)
    (v : Fin L → ℝ) (c : ℝ) : ∀ᶠ t in 𝓝 (0 : ℝ), PWDomain (p + t • v) (w + t * c) := by
  have hcont : ∀ a b : ℝ, Tendsto (fun t : ℝ => a + t * b) (𝓝 0) (𝓝 a) := by
    intro a b
    have : Continuous (fun t : ℝ => a + t * b) := by fun_prop
    simpa using this.tendsto 0
  have hp : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ l, 0 < (p + t • v) l := by
    rw [Filter.eventually_all]
    intro l
    simpa [smul_eq_mul] using (hcont (p l) (v l)).eventually_const_lt (hd.1 l)
  have hw : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < w + t * c := (hcont w c).eventually_const_lt hd.2
  filter_upwards [hp, hw] with t h1 h2
  exact ⟨h1, h2⟩

/-- A function with a derivative at `a` that is eventually constant near `a` has zero
derivative. -/
theorem hasDerivAt_eq_zero_of_eventually_const {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℝ → E} {f' : E} {a : ℝ} (hf : HasDerivAt f f' a) (c : E)
    (h : ∀ᶠ t in 𝓝 a, f t = c) : f' = 0 :=
  hf.unique ((hasDerivAt_const a c).congr_of_eventuallyEq h)

/-- If `x` satisfies Walras' law and has derivative `D` at a domain point, then for every
direction `(v, c)`: `v·x(p, w) + p·D(v, c) = c`. This is the derivative of
`p·x(p, w) = w` along `(v, c)`. -/
theorem walras_deriv_identity {L : ℕ} {x : DemandFunction L} (hW : WalrasLaw x)
    {p : Fin L → ℝ} {w : ℝ} (hd : PWDomain p w) {D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)}
    (hD : HasFDerivAt (Function.uncurry x) D (p, w)) (v : Fin L → ℝ) (c : ℝ) :
    v ⬝ᵥ x p w + p ⬝ᵥ D (v, c) = c := by
  have hterm : ∀ l ∈ (Finset.univ : Finset (Fin L)),
      HasDerivAt (fun t : ℝ => (p l + t * v l) * x (p + t • v) (w + t * c) l)
        (v l * x p w l + p l * D (v, c) l) 0 := by
    intro l _
    have h1 : HasDerivAt (fun t : ℝ => p l + t * v l) (v l) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v l)).const_add (p l)
    have h2 := hasDerivAt_path_apply hD v c l
    have := h1.fun_mul h2
    simpa using this
  have hsum := HasDerivAt.fun_sum hterm
  have hc : HasDerivAt (fun t : ℝ => w + t * c) c 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const c).const_add w
  have hg := hsum.sub hc
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ),
      (∑ l, (p l + t * v l) * x (p + t • v) (w + t * c) l) - (w + t * c) = 0 := by
    filter_upwards [eventually_pwDomain hd v c] with t ht
    have := hW _ _ ht
    simp only [dotProduct, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    rw [this, sub_self]
  have h0 := hasDerivAt_eq_zero_of_eventually_const hg 0 hev
  rw [Finset.sum_add_distrib, sub_eq_zero] at h0
  simpa [dotProduct] using h0

/-- If `x` is homogeneous of degree zero and has derivative `D` at a domain point `(p, w)`,
then `D(p, w) = 0`: the derivative of `α ↦ x(αp, αw)` at `α = 1`. -/
theorem homogeneous_deriv_identity {L : ℕ} {x : DemandFunction L} (hH : HomogeneousZero x)
    {p : Fin L → ℝ} {w : ℝ} (hd : PWDomain p w) {D : ((Fin L → ℝ) × ℝ) →L[ℝ] (Fin L → ℝ)}
    (hD : HasFDerivAt (Function.uncurry x) D (p, w)) : D (p, w) = 0 := by
  have h := hasDerivAt_path hD p w
  apply hasDerivAt_eq_zero_of_eventually_const h (x p w)
  have hpos : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < 1 + t := by
    have : Tendsto (fun t : ℝ => 1 + t) (𝓝 0) (𝓝 1) := by
      have hc : Continuous (fun t : ℝ => 1 + t) := by fun_prop
      simpa using hc.tendsto (0 : ℝ)
    exact this.eventually_const_lt one_pos
  filter_upwards [hpos] with t ht
  have e1 : p + t • p = (1 + t) • p := by rw [add_smul, one_smul]
  have e2 : w + t * w = (1 + t) * w := by ring
  rw [e1, e2]
  exact hH p w _ hd ht

end MWG.ConsumerChoice
