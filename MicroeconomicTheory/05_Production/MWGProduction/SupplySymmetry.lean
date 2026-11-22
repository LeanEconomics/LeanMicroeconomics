/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGProduction.Profit
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Topology.MetricSpace.Sequences

/-!
# Proposition 5.C.1(vii) without convexity (MWG, p. 138)

`Profit` proves Proposition 5.C.1(vii) for closed convex `Y` (via Hotelling's lemma, which
needs convexity, correction 4). Here the symmetry of `Dy(p̄)` is proved for an arbitrary
production set `Y`, under the book's hypothesis that `y(·)` is a function (indeed any selection
from the supply correspondence near `p̄`) differentiable at `p̄`.

The proof does not go through `π`. A selection `y(·)` from the supply correspondence is
*cyclically monotone*: around any closed cycle of prices `p⁰, …, p^N = p⁰`,
`Σ (p^{i+1} - p^i)·y(p^i) ≤ 0` (`supply_cyclic`). Rescaling a cycle around `p̄` and letting the
scale tend to zero, the derivative `D = Dy(p̄)` inherits cyclic monotonicity
(`deriv_cyclic`). Along a long thin rectangle (`n` steps along `a`, one step along `b`) this
gives `b·Da - a·Db ≤ a·Da/n + b·Db`, and rescaling `a`, `b` and letting `n → ∞` gives
`b·Da = a·Db` (`cyclic_symm`).

`Dy(p̄) = D²π(p̄)` also holds: Hotelling's lemma holds at every price where the selection is
continuous (`hotelling_of_continuousAt`, no convexity), so `∇π(p̄) = y(p̄)`; when `y(·)` is
continuous near `p̄` the Hessian of `π` at `p̄` is `Dy(p̄)` (`proposition_5_C_1_vii_general`).
-/

namespace MWG.Production

open MWG.ClassicalDemand MWG.ConsumerChoice Filter Topology

variable {L : ℕ}

/-- A selection from the supply correspondence is cyclically monotone: for prices
`P 0, …, P N` with `P N = P 0`, `Σ_{i<N} (P(i+1) - P i)·y(P i) ≤ 0`. -/
theorem supply_cyclic {Y : Set (Fin L → ℝ)} {ys : (Fin L → ℝ) → (Fin L → ℝ)} {N : ℕ}
    (P : ℕ → Fin L → ℝ) (hP : ∀ i ≤ N, ys (P i) ∈ supply Y (P i)) (hcyc : P N = P 0) :
    ∑ i ∈ Finset.range N, (P (i + 1) - P i) ⬝ᵥ ys (P i) ≤ 0 := by
  have key : ∀ i < N, (P (i + 1) - P i) ⬝ᵥ ys (P i) ≤
      P (i + 1) ⬝ᵥ ys (P (i + 1)) - P i ⬝ᵥ ys (P i) := by
    intro i hi
    have := (hP (i + 1) hi).2 _ (hP i hi.le).1
    rw [sub_dotProduct]
    linarith
  calc _ ≤ ∑ i ∈ Finset.range N, (P (i + 1) ⬝ᵥ ys (P (i + 1)) - P i ⬝ᵥ ys (P i)) :=
        Finset.sum_le_sum fun i hi => key i (Finset.mem_range.mp hi)
    _ = P N ⬝ᵥ ys (P N) - P 0 ⬝ᵥ ys (P 0) :=
        Finset.sum_range_sub (fun i => P i ⬝ᵥ ys (P i)) N
    _ = 0 := by rw [hcyc, sub_self]

/-- The derivative of a supply selection at `p̄` is cyclically monotone: for any cycle
`Q 0, …, Q N = Q 0`, `Σ_{i<N} (Q(i+1) - Q i)·D(Q i) ≤ 0`. -/
theorem deriv_cyclic {Y : Set (Fin L → ℝ)} {ys : (Fin L → ℝ) → (Fin L → ℝ)} {p : Fin L → ℝ}
    (hys : ∀ᶠ q in 𝓝 p, ys q ∈ supply Y q) {D : (Fin L → ℝ) →L[ℝ] (Fin L → ℝ)}
    (hD : HasFDerivAt ys D p) (N : ℕ) (Q : ℕ → Fin L → ℝ) (hcyc : Q N = Q 0) :
    ∑ i ∈ Finset.range N, (Q (i + 1) - Q i) ⬝ᵥ D (Q i) ≤ 0 := by
  have hline : ∀ v : Fin L → ℝ, HasDerivAt (fun t : ℝ => p + t • v) v 0 := by
    intro v
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add p
    simp only [id, one_smul] at h
    exact h
  have hlim : ∀ i, Tendsto (fun t : ℝ => t⁻¹ • (ys (p + t • Q i) - ys p)) (𝓝[>] 0)
      (𝓝 (D (Q i))) := by
    intro i
    have hD' := hD
    rw [← show p + (0 : ℝ) • Q i = p by simp] at hD'
    have hc := (hD'.comp_hasDerivAt (0 : ℝ) (hline (Q i))).tendsto_slope_zero_right
    simpa only [zero_add, zero_smul, add_zero, Function.comp_def] using hc
  have hsum : Tendsto (fun t : ℝ => ∑ i ∈ Finset.range N,
      (Q (i + 1) - Q i) ⬝ᵥ (t⁻¹ • (ys (p + t • Q i) - ys p))) (𝓝[>] 0)
      (𝓝 (∑ i ∈ Finset.range N, (Q (i + 1) - Q i) ⬝ᵥ D (Q i))) :=
    tendsto_finsetSum _ fun i _ =>
      ((continuous_const.dotProduct continuous_id).tendsto _).comp (hlim i)
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i ∈ Finset.range (N + 1),
      ys (p + t • Q i) ∈ supply Y (p + t • Q i) := by
    rw [Finset.eventually_all]
    intro i _
    have hc : Tendsto (fun t : ℝ => p + t • Q i) (𝓝[>] 0) (𝓝 p) := by
      have := (hline (Q i)).continuousAt.tendsto
      simp only [zero_smul, add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    exact hc.eventually hys
  refine le_of_tendsto hsum ?_
  filter_upwards [hev, self_mem_nhdsWithin] with t ht htpos
  have htpos' : (0 : ℝ) < t := htpos
  have hcyc' := supply_cyclic (Y := Y) (ys := ys) (N := N) (fun i => p + t • Q i)
    (fun i hi => ht i (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))) (by simp [hcyc])
  have hzero : ∑ i ∈ Finset.range N, (Q (i + 1) - Q i) ⬝ᵥ ys p = 0 := by
    simp only [sub_dotProduct]
    rw [Finset.sum_range_sub (fun i => Q i ⬝ᵥ ys p) N, hcyc, sub_self]
  have hterm : ∀ i ∈ Finset.range N, (Q (i + 1) - Q i) ⬝ᵥ (t⁻¹ • (ys (p + t • Q i) - ys p)) =
      t⁻¹ * t⁻¹ * ((p + t • Q (i + 1) - (p + t • Q i)) ⬝ᵥ ys (p + t • Q i)) -
        t⁻¹ * ((Q (i + 1) - Q i) ⬝ᵥ ys p) := by
    intro i _
    have e : p + t • Q (i + 1) - (p + t • Q i) = t • (Q (i + 1) - Q i) := by
      rw [smul_sub]; abel
    rw [e, dotProduct_smul, smul_dotProduct, dotProduct_sub, smul_eq_mul, smul_eq_mul]
    field_simp
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    hzero, mul_zero, sub_zero]
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hcyc'

/-- `Σ_{i<n} i = n(n-1)/2` in `ℝ`. -/
theorem sum_range_cast_id (n : ℕ) : ∑ i ∈ Finset.range n, (i : ℝ) = n * (n - 1) / 2 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- The thin-rectangle cycle: `n` steps from `0` to `a`, one step to `a + b`, `n` steps back to
`b`, one step back to `0`. -/
noncomputable def thinCycle (n : ℕ) (a b : Fin L → ℝ) (i : ℕ) : Fin L → ℝ :=
  if i ≤ n then ((i : ℝ) / n) • a
  else if i ≤ 2 * n + 1 then (1 - ((i : ℝ) - n - 1) / n) • a + b else 0

/-- Along the thin rectangle, a cyclically monotone linear map satisfies
`b·Da - a·Db ≤ a·Da/n + b·Db`. -/
theorem thinCycle_bound (D : (Fin L → ℝ) →L[ℝ] (Fin L → ℝ))
    (hD : ∀ (N : ℕ) (Q : ℕ → Fin L → ℝ), Q N = Q 0 →
      ∑ i ∈ Finset.range N, (Q (i + 1) - Q i) ⬝ᵥ D (Q i) ≤ 0)
    (a b : Fin L → ℝ) {n : ℕ} (hn : 1 ≤ n) :
    b ⬝ᵥ D a - a ⬝ᵥ D b ≤ a ⬝ᵥ D a / n + b ⬝ᵥ D b := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  set Q := thinCycle n a b with hQdef
  have hQ0 : Q 0 = 0 := by simp [hQdef, thinCycle]
  have hQN : Q (2 * n + 2) = 0 := by
    simp only [hQdef, thinCycle]
    simp only [show ¬ (2 * n + 2 ≤ n) by omega, show ¬ (2 * n + 2 ≤ 2 * n + 1) by omega,
      ↓reduceIte]
  have h := hD (2 * n + 2) Q (by rw [hQN, hQ0])
  set f := fun i => (Q (i + 1) - Q i) ⬝ᵥ D (Q i) with hf
  -- the four pieces of the cycle
  have h1 : ∀ i ∈ Finset.range n, f i = (i : ℝ) * (a ⬝ᵥ D a / (n * n)) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    simp only [hf, hQdef, thinCycle]
    simp only [show i + 1 ≤ n by omega, show i ≤ n by omega, ↓reduceIte]
    rw [← sub_smul, map_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    push_cast
    field_simp
    ring
  have h2 : f n = b ⬝ᵥ D a := by
    simp only [hf, hQdef, thinCycle]
    simp only [le_refl, show ¬ (n + 1 ≤ n) by omega, show n + 1 ≤ 2 * n + 1 by omega,
      ↓reduceIte]
    rw [div_self hn0, one_smul]
    push_cast
    simp
  have h3 : ∀ j ∈ Finset.range n, f (n + 1 + j) =
      -(1 / n) * ((1 - (j : ℝ) / n) * (a ⬝ᵥ D a) + a ⬝ᵥ D b) := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    simp only [hf, hQdef, thinCycle]
    simp only [show ¬ (n + 1 + j + 1 ≤ n) by omega, show n + 1 + j + 1 ≤ 2 * n + 1 by omega,
      show ¬ (n + 1 + j ≤ n) by omega, show n + 1 + j ≤ 2 * n + 1 by omega, ↓reduceIte]
    have e : (1 - ((↑(n + 1 + j + 1) : ℝ) - n - 1) / n) • a + b -
        ((1 - ((↑(n + 1 + j) : ℝ) - n - 1) / n) • a + b) = (-(1 / n) : ℝ) • a := by
      rw [add_sub_add_right_eq_sub, ← sub_smul]
      congr 1
      push_cast
      field_simp
      ring
    rw [e, map_add, map_smul, smul_dotProduct, dotProduct_add, dotProduct_smul, smul_eq_mul,
      smul_eq_mul]
    have e2 : (1 - ((↑(n + 1 + j) : ℝ) - n - 1) / n) = 1 - (j : ℝ) / n := by
      push_cast; ring
    rw [e2]
  have h4 : f (2 * n + 1) = -(b ⬝ᵥ D b) := by
    simp only [hf, hQdef, thinCycle]
    simp only [show ¬ (2 * n + 1 + 1 ≤ n) by omega, show ¬ (2 * n + 1 + 1 ≤ 2 * n + 1) by omega,
      show ¬ (2 * n + 1 ≤ n) by omega, le_refl, ↓reduceIte]
    have e2 : (1 - ((↑(2 * n + 1) : ℝ) - n - 1) / n) = 0 := by
      push_cast
      field_simp
      ring
    rw [e2, zero_smul, zero_add, zero_sub, neg_dotProduct]
  have hsplit : ∑ i ∈ Finset.range (2 * n + 2), f i =
      (∑ i ∈ Finset.range n, f i) + f n + (∑ j ∈ Finset.range n, f (n + 1 + j)) +
        f (2 * n + 1) := by
    rw [show 2 * n + 2 = (n + 1 + n) + 1 by omega, Finset.sum_range_succ,
      Finset.sum_range_add, Finset.sum_range_succ]
    congr 2
    omega
  have hs1 : ∑ i ∈ Finset.range n, f i = (n * (n - 1) / 2) * (a ⬝ᵥ D a / (n * n)) := by
    rw [Finset.sum_congr rfl h1, ← Finset.sum_mul, sum_range_cast_id]
  have hs3 : ∑ j ∈ Finset.range n, f (n + 1 + j) =
      -(1 / n) * ((n - n * (n - 1) / (2 * n)) * (a ⬝ᵥ D a) + n * (a ⬝ᵥ D b)) := by
    rw [Finset.sum_congr rfl h3, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_mul,
      Finset.sum_sub_distrib, ← Finset.sum_div, sum_range_cast_id]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    field_simp
  have htot : ∑ i ∈ Finset.range (2 * n + 2), f i =
      -(a ⬝ᵥ D a) / n + b ⬝ᵥ D a - a ⬝ᵥ D b - b ⬝ᵥ D b := by
    rw [hsplit, hs1, h2, hs3, h4]
    field_simp
    ring
  have h' : ∑ i ∈ Finset.range (2 * n + 2), f i ≤ 0 := h
  rw [htot] at h'
  have : a ⬝ᵥ D a / n = (a ⬝ᵥ D a) / n := rfl
  rw [neg_div] at h'
  linarith

/-- A cyclically monotone linear map is symmetric: `b·Da = a·Db`. -/
theorem cyclic_symm (D : (Fin L → ℝ) →L[ℝ] (Fin L → ℝ))
    (hD : ∀ (N : ℕ) (Q : ℕ → Fin L → ℝ), Q N = Q 0 →
      ∑ i ∈ Finset.range N, (Q (i + 1) - Q i) ⬝ᵥ D (Q i) ≤ 0)
    (a b : Fin L → ℝ) : b ⬝ᵥ D a = a ⬝ᵥ D b := by
  have half : ∀ a b : Fin L → ℝ, b ⬝ᵥ D a - a ⬝ᵥ D b ≤ 0 := by
    intro a b
    set X := b ⬝ᵥ D a - a ⬝ᵥ D b
    set A := a ⬝ᵥ D a
    set B := b ⬝ᵥ D b
    -- rescaled bound: `X ≤ s A / n + B / s` for `s > 0`, `n ≥ 1`
    have hres : ∀ s : ℝ, 0 < s → ∀ n : ℕ, 1 ≤ n → X ≤ s * A / n + B / s := by
      intro s hs n hn
      set μ := Real.sqrt s
      have hμ : 0 < μ := Real.sqrt_pos.mpr hs
      have hμ2 : μ * μ = s := Real.mul_self_sqrt hs.le
      have h := thinCycle_bound D hD (μ • a) (μ⁻¹ • b) hn
      simp only [map_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul] at h
      have e1 : μ * (μ⁻¹ * (b ⬝ᵥ D a)) = b ⬝ᵥ D a := by field_simp
      have e2 : μ⁻¹ * (μ * (a ⬝ᵥ D b)) = a ⬝ᵥ D b := by field_simp
      have e3 : μ * (μ * A) = s * A := by rw [← hμ2]; ring
      have e4 : μ⁻¹ * (μ⁻¹ * B) = B / s := by rw [← hμ2]; field_simp
      rw [e1, e2, e3, e4] at h
      exact h
    by_contra hX
    push Not at hX
    set s := 2 * (|B| + 1) / X with hs
    have hs0 : 0 < s := by positivity
    obtain ⟨n, hn⟩ := exists_nat_gt (2 * s * |A| / X + 1)
    have hn1 : 1 ≤ n := by
      have : (1 : ℝ) < n := by
        have : 0 ≤ 2 * s * |A| / X := by positivity
        linarith
      exact_mod_cast this.le
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    have h := hres s hs0 n hn1
    have hB : B / s < X / 2 := by
      rw [div_lt_iff₀ hs0, hs]
      field_simp
      nlinarith [le_abs_self B, abs_nonneg B]
    have hA : s * A / n < X / 2 := by
      rw [div_lt_iff₀ hnpos]
      have h1 : s * A ≤ s * |A| := mul_le_mul_of_nonneg_left (le_abs_self A) hs0.le
      have h2 : 2 * s * |A| < X * n := by
        have h3 : 2 * s * |A| / X < n := by linarith
        rw [div_lt_iff₀ hX] at h3; linarith
      nlinarith
    linarith
  have h1 := half a b
  have h2 := half b a
  linarith

/-- **Proposition 5.C.1(vii)** (MWG, p. 138), symmetry, for an arbitrary production set `Y`: if
`y(·)` is a selection from the supply correspondence near `p̄` (in particular if `y(·)` is a
function) and is differentiable at `p̄`, then `Dy(p̄)` is symmetric. No closedness, free
disposal or convexity is needed. -/
theorem proposition_5_C_1_vii_symm {Y : Set (Fin L → ℝ)} {ys : (Fin L → ℝ) → (Fin L → ℝ)}
    {p : Fin L → ℝ} (hys : ∀ᶠ q in 𝓝 p, ys q ∈ supply Y q)
    {D : (Fin L → ℝ) →L[ℝ] (Fin L → ℝ)} (hD : HasFDerivAt ys D p) :
    ∀ i j, jacobian D i j = jacobian D j i := by
  intro i j
  have h := cyclic_symm D (deriv_cyclic hys hD) (Pi.single j 1) (Pi.single i 1)
  simpa [jacobian] using h

/-- `|h·v| ≤ L‖h‖‖v‖` for the sup norm. -/
theorem abs_dotProduct_le_norm (h v : Fin L → ℝ) : |h ⬝ᵥ v| ≤ L * (‖h‖ * ‖v‖) := by
  calc |h ⬝ᵥ v| ≤ ∑ l, |h l * v l| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _l : Fin L, ‖h‖ * ‖v‖ := Finset.sum_le_sum fun l _ => by
        rw [abs_mul]
        exact mul_le_mul (norm_le_pi_norm h l) (norm_le_pi_norm v l) (abs_nonneg _)
          (norm_nonneg _)
    _ = L * (‖h‖ * ‖v‖) := by simp

/-- **Hotelling's lemma** (Proposition 5.C.1(vi), MWG, p. 138) without convexity, at a price
where a supply selection is continuous: if `y(q) ∈ y(q)` for `q` near `p̄` and `y(·)` is
continuous at `p̄`, then `π` is differentiable at `p̄` with `∇π(p̄) = y(p̄)`. -/
theorem hotelling_of_continuousAt {Y : Set (Fin L → ℝ)} {ys : (Fin L → ℝ) → (Fin L → ℝ)}
    {p : Fin L → ℝ} (hys : ∀ᶠ q in 𝓝 p, ys q ∈ supply Y q) (hc : ContinuousAt ys p) :
    HasFDerivAt (profit Y) (dualityDotCLM (ys p)) p := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc0
  have hp := hys.self_of_nhds
  have hshift : Tendsto (fun h : Fin L → ℝ => p + h) (𝓝 0) (𝓝 p) := by
    have := (tendsto_const_nhds (x := p)).add (tendsto_id (x := 𝓝 (0 : Fin L → ℝ)))
    simpa using this
  have hcl : ∀ᶠ h in 𝓝 (0 : Fin L → ℝ), ‖ys (p + h) - ys p‖ ≤ c / (L + 1) := by
    have := (hc.tendsto.comp hshift)
    have hball := Metric.tendsto_nhds.mp this (c / (L + 1)) (by positivity)
    filter_upwards [hball] with h hh
    rw [dist_eq_norm] at hh
    exact hh.le
  filter_upwards [hshift.eventually hys, hcl] with h hh hcl'
  rw [profit_eq_of_mem_supply hh, profit_eq_of_mem_supply hp, dualityDotCLM_apply]
  have hup := hh.2 _ hp.1
  have hlow := hp.2 _ hh.1
  have hb := abs_dotProduct_le_norm h (ys (p + h) - ys p)
  rw [Real.norm_eq_abs, abs_le]
  have hL : (L : ℝ) * (‖h‖ * ‖ys (p + h) - ys p‖) ≤ c * ‖h‖ := by
    have h1 : ‖h‖ * ‖ys (p + h) - ys p‖ ≤ ‖h‖ * (c / (L + 1)) :=
      mul_le_mul_of_nonneg_left hcl' (norm_nonneg h)
    have h2 : (L : ℝ) * (‖h‖ * (c / (L + 1))) ≤ c * ‖h‖ := by
      rw [show (L : ℝ) * (‖h‖ * (c / (L + 1))) = (L / (L + 1)) * (c * ‖h‖) by ring]
      have : (L : ℝ) / (L + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith
      exact mul_le_of_le_one_left (by positivity) this
    calc _ ≤ (L : ℝ) * (‖h‖ * (c / (L + 1))) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ _ := h2
  rw [abs_le] at hb
  simp only [add_dotProduct, dotProduct_sub, dotProduct_comm (ys p) h] at hup hlow hb ⊢
  constructor <;> nlinarith [norm_nonneg h]

/-- If `Y` is closed and the supply correspondence is single-valued, `y(q) = {ys q}`, for `q`
near `p̄`, then `ys` is continuous near `p̄`. Proof: `π` is convex and finite near `p̄`, hence
locally Lipschitz (Mathlib), which bounds `ys` locally; a limit point of `ys(q_n)` along
`q_n → q` lies in `Y` (closed) and maximizes profit at `q`, so it is `ys q`. -/
theorem supply_continuousAt_of_single {Y : Set (Fin L → ℝ)} (hcl : IsClosed Y)
    {ys : (Fin L → ℝ) → (Fin L → ℝ)} {p : Fin L → ℝ}
    (hys : ∀ᶠ q in 𝓝 p, supply Y q = {ys q}) : ∀ᶠ q in 𝓝 p, ContinuousAt ys q := by
  obtain ⟨U, hU, hUo, hpU⟩ := eventually_nhds_iff.mp hys
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hUo p hpU
  set C := Metric.ball p r with hC
  have hmem : ∀ q ∈ C, ys q ∈ supply Y q := fun q hq => by rw [hU q (hball hq)]; rfl
  have hprof : ∀ q ∈ C, profit Y q = q ⬝ᵥ ys q := fun q hq => profit_eq_of_mem_supply (hmem q hq)
  have hconv : ConvexOn ℝ C (profit Y) := by
    refine ⟨convex_ball p r, fun x hx y hy a b ha hb hab => ?_⟩
    have hz : a • x + b • y ∈ C := convex_ball p r hx hy ha hb hab
    rw [hprof _ hz, hprof x hx, hprof y hy, add_dotProduct, smul_dotProduct, smul_dotProduct,
      smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul]
    have h1 := (hmem x hx).2 _ (hmem _ hz).1
    have h2 := (hmem y hy).2 _ (hmem _ hz).1
    nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]
  have hlip := hconv.locallyLipschitzOn Metric.isOpen_ball
  filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr)] with q hq
  -- local bound on `ys`
  obtain ⟨K, t, ht, hK⟩ := hlip hq
  rw [nhdsWithin_eq_nhds.mpr (Metric.isOpen_ball.mem_nhds hq)] at ht
  obtain ⟨δ, hδ, hδt⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem ht
    (Metric.isOpen_ball.mem_nhds hq))
  have hbound : ∀ q' ∈ Metric.ball q (δ / 2), ‖ys q'‖ ≤ K := by
    intro q' hq'
    have hq'C : q' ∈ C := (hδt (Metric.ball_subset_ball (by linarith) hq')).2
    refine (pi_norm_le_iff_of_nonneg K.coe_nonneg).mpr fun i => ?_
    have hdir : ∀ c : ℝ, |c| ≤ δ / 4 → c * ys q' i ≤ K * |c| := by
      intro c hc
      set h : Fin L → ℝ := Pi.single i c with hh
      have hnh : ‖h‖ = |c| := by rw [hh, Pi.norm_single, Real.norm_eq_abs]
      have hin : q' + h ∈ Metric.ball q δ := by
        rw [Metric.mem_ball, dist_eq_norm] at hq' ⊢
        calc ‖q' + h - q‖ ≤ ‖q' - q‖ + ‖h‖ := by
              rw [show q' + h - q = (q' - q) + h by abel]; exact norm_add_le _ _
          _ < δ := by rw [hnh]; linarith
      have hin' := hδt hin
      have hq'in := hδt (Metric.ball_subset_ball (by linarith) hq')
      have hle := (hmem _ hin'.2).2 _ (hmem q' hq'C).1
      have hl := hK.dist_le_mul _ hin'.1 _ hq'in.1
      rw [hprof _ hin'.2, hprof _ hq'C, Real.dist_eq, dist_eq_norm,
        show q' + h - q' = h by abel, hnh] at hl
      have : (q' + h) ⬝ᵥ ys q' = q' ⬝ᵥ ys q' + c * ys q' i := by
        rw [add_dotProduct, hh, single_dotProduct]
      rw [abs_le] at hl
      linarith [hl.2]
    have hpos := hdir (δ / 4) (by rw [abs_of_pos (by positivity)])
    have hneg := hdir (-(δ / 4)) (by rw [abs_neg, abs_of_pos (by positivity)])
    rw [abs_of_pos (by positivity)] at hpos
    rw [abs_neg, abs_of_pos (by positivity)] at hneg
    have hδ4 : 0 < δ / 4 := by positivity
    have u1 : ys q' i ≤ K := (mul_le_mul_iff_of_pos_left hδ4).mp (by linarith)
    have u2 : -ys q' i ≤ K := (mul_le_mul_iff_of_pos_left hδ4).mp (by linarith)
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  -- sequential continuity
  rw [ContinuousAt, tendsto_nhds_iff_seq_tendsto]
  intro u hu
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  set v := u ∘ ns with hv
  have hvt : Tendsto v atTop (𝓝 q) := hu.comp hns
  have hevC : ∀ᶠ n in atTop, v n ∈ Metric.ball q (δ / 2) ∧ v n ∈ C :=
    hvt.eventually_mem (Filter.inter_mem (Metric.ball_mem_nhds q (by linarith : (0 : ℝ) < δ / 2))
      (Metric.isOpen_ball.mem_nhds hq))
  have hfreq : ∃ᶠ n in atTop, ys (v n) ∈ Metric.closedBall (0 : Fin L → ℝ) K :=
    (hevC.mono fun n hn => by
      rw [mem_closedBall_zero_iff]; exact hbound _ hn.1).frequently
  obtain ⟨a, -, φ, hφ, hlim⟩ := tendsto_subseq_of_frequently_bounded
    Metric.isBounded_closedBall hfreq
  have hvφ : Tendsto (v ∘ φ) atTop (𝓝 q) := hvt.comp hφ.tendsto_atTop
  have hevφ : ∀ᶠ n in atTop, v (φ n) ∈ C := (hφ.tendsto_atTop.eventually hevC).mono
    fun n hn => hn.2
  have haY : a ∈ Y := hcl.mem_of_tendsto hlim (hevφ.mono fun n hn => (hmem _ hn).1)
  have hdotlim : ∀ (x : ℕ → Fin L → ℝ) (y : ℕ → Fin L → ℝ) (x₀ y₀ : Fin L → ℝ),
      Tendsto x atTop (𝓝 x₀) → Tendsto y atTop (𝓝 y₀) →
      Tendsto (fun n => x n ⬝ᵥ y n) atTop (𝓝 (x₀ ⬝ᵥ y₀)) := by
    intro x y x₀ y₀ hx hy
    exact ((continuous_fst.dotProduct continuous_snd).tendsto (x₀, y₀)).comp (hx.prodMk_nhds hy)
  have hsup : a ∈ supply Y q := by
    refine ⟨haY, fun y hy => ?_⟩
    refine le_of_tendsto_of_tendsto (hdotlim _ _ _ _ hvφ tendsto_const_nhds)
      (hdotlim _ _ _ _ hvφ hlim) ?_
    filter_upwards [hevφ] with n hn
    exact (hmem _ hn).2 y hy
  have hqU : supply Y q = {ys q} := hU q (hball hq)
  rw [hqU, Set.mem_singleton_iff] at hsup
  rw [← hsup]
  exact ⟨φ, hlim⟩

/-- **Proposition 5.C.1(vii)** (MWG, p. 138) for a closed, not necessarily convex, production set
`Y`: if `y(·)` is a function near `p̄` (`y(q) = {ys q}`) differentiable at `p̄`, then `∇π = ys`
near `p̄` (`ys` is continuous there, `supply_continuousAt_of_single`, and Hotelling's lemma holds,
`hotelling_of_continuousAt`), `D²π(p̄) = Dy(p̄)`, and this matrix is symmetric and positive
semidefinite with `Dy(p̄)p̄ = 0`. Free disposal is not needed; symmetry and semidefiniteness need
neither closedness nor single-valuedness (`proposition_5_C_1_vii_symm`,
`proposition_5_C_1_vii_psd`). -/
theorem proposition_5_C_1_vii_general {Y : Set (Fin L → ℝ)} (hcl : IsClosed Y)
    {ys : (Fin L → ℝ) → (Fin L → ℝ)} {p : Fin L → ℝ} (hys : ∀ᶠ q in 𝓝 p, supply Y q = {ys q})
    {D : (Fin L → ℝ) →L[ℝ] (Fin L → ℝ)} (hD : HasFDerivAt ys D p) :
    (∀ᶠ q in 𝓝 p, HasFDerivAt (profit Y) (dualityDotCLM (ys q)) q) ∧
      hessianMatrix (profit Y) p = jacobian D ∧
      (∀ i j, jacobian D i j = jacobian D j i) ∧ PosSemidefMWG (jacobian D) ∧ D p = 0 := by
  have hcont := supply_continuousAt_of_single hcl hys
  have hsel : ∀ᶠ q in 𝓝 p, ys q ∈ supply Y q := hys.mono fun q hq => by rw [hq]; rfl
  have hgrad : ∀ᶠ q in 𝓝 p, HasFDerivAt (profit Y) (dualityDotCLM (ys q)) q := by
    filter_upwards [hsel.eventually_nhds, hcont] with q hq hcq
    exact hotelling_of_continuousAt hq hcq
  refine ⟨hgrad, ?_, proposition_5_C_1_vii_symm hsel hD, proposition_5_C_1_vii_psd hsel hD,
    proposition_5_C_1_vii_euler hys hD⟩
  have heq : (fun q => gradientVec (fderiv ℝ (profit Y) q)) =ᶠ[𝓝 p] ys := by
    filter_upwards [hgrad] with q hq
    rw [hq.fderiv, gradientVec_dualityDotCLM]
  rw [hessianMatrix, (hD.congr_of_eventuallyEq heq).fderiv]

/-- A nonconvex production set: the decreasing-returns technology `{y₁ ≤ 0, y₂ ≤ √(-y₁)}`
together with the isolated plan `(-4, 5/2)`. -/
def ssY : Set (Fin 2 → ℝ) :=
  {y | y 0 ≤ 0 ∧ y 1 ≤ Real.sqrt (-y 0)} ∪ {![-4, 5 / 2]}

/-- The supply function `y(p) = (-(p₂/2p₁)², p₂/2p₁)` of `ssY` near `p̄ = (1, 1)`. -/
noncomputable def ssSupply (p : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![-(p 1 / (2 * p 0)) ^ 2, p 1 / (2 * p 0)]

/-- For `0 < q₂ < 2q₁`, `ssSupply q` maximizes profit on `ssY` at `q`. -/
theorem ssSupply_mem_supply {q : Fin 2 → ℝ} (h0 : 0 < q 0) (h1 : 0 < q 1) (h2 : q 1 < 2 * q 0) :
    ssSupply q ∈ supply ssY q := by
  have hdot : ∀ y : Fin 2 → ℝ, q ⬝ᵥ y = q 0 * y 0 + q 1 * y 1 := fun y => by
    simp [dotProduct, Fin.sum_univ_two]
  have hval : q ⬝ᵥ ssSupply q = q 1 ^ 2 / (4 * q 0) := by
    rw [hdot]
    simp only [ssSupply, Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp
    ring
  refine ⟨Or.inl ⟨?_, ?_⟩, fun y hy => ?_⟩
  · simp only [ssSupply, Matrix.cons_val_zero]
    nlinarith [sq_nonneg (q 1 / (2 * q 0))]
  · simp only [ssSupply, Matrix.cons_val_zero, Matrix.cons_val_one, neg_neg]
    rw [Real.sqrt_sq (by positivity)]
  · rw [hval, hdot]
    rcases hy with ⟨hy0, hy1⟩ | hy
    · set x := Real.sqrt (-y 0) with hx
      have hx2 : x ^ 2 = -y 0 := Real.sq_sqrt (by linarith)
      have hx0 : 0 ≤ x := Real.sqrt_nonneg _
      rw [le_div_iff₀ (by positivity)]
      have h3 : q 1 * y 1 ≤ q 1 * x := mul_le_mul_of_nonneg_left hy1 h1.le
      have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 4 * q 0)
      have hy0' : y 0 = -x ^ 2 := by linarith
      rw [hy0']
      nlinarith [sq_nonneg (2 * q 0 * x - q 1)]
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [le_div_iff₀ (by positivity)]
      nlinarith [mul_pos (by linarith : (0 : ℝ) < 2 * q 0 - q 1)
        (by linarith : (0 : ℝ) < 8 * q 0 - q 1)]

/-- **Proposition 5.C.1(vii)** (MWG, p. 138): the hypotheses of `proposition_5_C_1_vii_symm`
hold for the nonconvex production set `ssY`: `ssY` is not convex, `y(p) = ssSupply p` is
profit maximizing for `p` near `(1, 1)` and is differentiable at `(1, 1)`; so `Dy(1, 1)` is
symmetric. -/
theorem proposition_5_C_1_vii_symm_instance :
    ¬ Convex ℝ ssY ∧ (∀ᶠ q in 𝓝 (![1, 1] : Fin 2 → ℝ), ssSupply q ∈ supply ssY q) ∧
      DifferentiableAt ℝ ssSupply ![1, 1] ∧
      ∀ i j, jacobian (fderiv ℝ ssSupply ![1, 1]) i j =
        jacobian (fderiv ℝ ssSupply ![1, 1]) j i := by
  have hsel : ∀ᶠ q in 𝓝 (![1, 1] : Fin 2 → ℝ), ssSupply q ∈ supply ssY q := by
    have hopen : IsOpen {q : Fin 2 → ℝ | 0 < q 0 ∧ 0 < q 1 ∧ q 1 < 2 * q 0} :=
      (isOpen_lt continuous_const (continuous_apply 0)).inter
        ((isOpen_lt continuous_const (continuous_apply 1)).inter
          (isOpen_lt (continuous_apply 1) (continuous_const.mul (continuous_apply 0))))
    filter_upwards [hopen.mem_nhds (by simp)] with q hq
    exact ssSupply_mem_supply hq.1 hq.2.1 hq.2.2
  have hdiff : DifferentiableAt ℝ ssSupply ![1, 1] := by
    rw [differentiableAt_pi]
    intro i
    fin_cases i
    · change DifferentiableAt ℝ (fun p : Fin 2 → ℝ => -(p 1 / (2 * p 0)) ^ 2) _
      fun_prop (disch := simp)
    · change DifferentiableAt ℝ (fun p : Fin 2 → ℝ => p 1 / (2 * p 0)) _
      fun_prop (disch := simp)
  refine ⟨fun hc => ?_, hsel, hdiff,
    proposition_5_C_1_vii_symm hsel hdiff.hasFDerivAt⟩
  have ha : (![-4, 5 / 2] : Fin 2 → ℝ) ∈ ssY := Or.inr rfl
  have hb : (![-25 / 4, 5 / 2] : Fin 2 → ℝ) ∈ ssY := by
    refine Or.inl ⟨by simp; norm_num, ?_⟩
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [show -(-25 / 4 : ℝ) = (5 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hmid := hc ha hb (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)
  rcases hmid with ⟨_, h⟩ | h
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
      Matrix.cons_val_one] at h
    have hlt : Real.sqrt (-(1 / 2 * -4 + 1 / 2 * (-25 / 4))) < 5 / 2 := by
      rw [Real.sqrt_lt' (by norm_num)]; norm_num
    linarith
  · have := congrFun (Set.mem_singleton_iff.mp h) 0
    simp at this
    norm_num at this

/-- For `0 < q₂ < 2q₁` the supply of `ssY` is single-valued: `y(q) = {ssSupply q}`. -/
theorem ss_supply_eq {q : Fin 2 → ℝ} (h0 : 0 < q 0) (h1 : 0 < q 1) (h2 : q 1 < 2 * q 0) :
    supply ssY q = {ssSupply q} := by
  have hm := ssSupply_mem_supply h0 h1 h2
  ext y
  refine ⟨fun hy => ?_, fun hy => by rw [Set.mem_singleton_iff.mp hy]; exact hm⟩
  have hge := hy.2 _ hm.1
  have hdot : ∀ y : Fin 2 → ℝ, q ⬝ᵥ y = q 0 * y 0 + q 1 * y 1 := fun y => by
    simp [dotProduct, Fin.sum_univ_two]
  have hval : q ⬝ᵥ ssSupply q = q 1 ^ 2 / (4 * q 0) := by
    rw [hdot]
    simp only [ssSupply, Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp
    ring
  rw [hval, hdot, div_le_iff₀ (by positivity)] at hge
  rw [Set.mem_singleton_iff]
  rcases hy.1 with ⟨hy0, hy1⟩ | hpt
  · set x := Real.sqrt (-y 0) with hx
    have hx2 : x ^ 2 = -y 0 := Real.sq_sqrt (by linarith)
    have hx0 : 0 ≤ x := Real.sqrt_nonneg _
    have h3 : q 1 * y 1 ≤ q 1 * x := mul_le_mul_of_nonneg_left hy1 h1.le
    have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 4 * q 0)
    have hy0' : y 0 = -x ^ 2 := by linarith
    rw [hy0'] at hge
    have hA : (2 * q 0 * x - q 1) ^ 2 = 0 := by
      nlinarith [sq_nonneg (2 * q 0 * x - q 1)]
    have hxr : x = q 1 / (2 * q 0) := by
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hA
      field_simp
      linarith
    have hB : 4 * q 0 * (q 1 * y 1) = 4 * q 0 * (q 1 * x) := by
      nlinarith [sq_nonneg (2 * q 0 * x - q 1)]
    have hy1x : y 1 = x := by
      have h40 : (4 * q 0 * q 1) ≠ 0 := by positivity
      have : 4 * q 0 * q 1 * y 1 = 4 * q 0 * q 1 * x := by linarith
      exact mul_left_cancel₀ h40 this
    funext i
    fin_cases i
    · simp only [ssSupply, Fin.zero_eta, Matrix.cons_val_zero]
      rw [hy0', hxr]
    · simp only [ssSupply, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [hy1x, hxr]
  · rw [Set.mem_singleton_iff] at hpt
    subst hpt
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hge
    nlinarith [mul_pos (by linarith : (0 : ℝ) < 2 * q 0 - q 1)
      (by linarith : (0 : ℝ) < 8 * q 0 - q 1)]

/-- **Proposition 5.C.1(vii)** (MWG, p. 138): the hypotheses of `proposition_5_C_1_vii_general`
hold for the closed nonconvex production set `ssY` at `p̄ = (1, 1)`, so `D²π(1, 1) = Dy(1, 1)`,
symmetric. -/
theorem proposition_5_C_1_vii_general_instance :
    IsClosed ssY ∧ (∀ᶠ q in 𝓝 (![1, 1] : Fin 2 → ℝ), supply ssY q = {ssSupply q}) ∧
      hessianMatrix (profit ssY) ![1, 1] = jacobian (fderiv ℝ ssSupply ![1, 1]) ∧
      ∀ i j, jacobian (fderiv ℝ ssSupply ![1, 1]) i j =
        jacobian (fderiv ℝ ssSupply ![1, 1]) j i := by
  have hcl : IsClosed ssY := by
    refine IsClosed.union ?_ isClosed_singleton
    exact (isClosed_le (continuous_apply 0) continuous_const).inter
      (isClosed_le (continuous_apply 1) (Real.continuous_sqrt.comp (continuous_apply 0).neg))
  have hopen : IsOpen {q : Fin 2 → ℝ | 0 < q 0 ∧ 0 < q 1 ∧ q 1 < 2 * q 0} :=
    (isOpen_lt continuous_const (continuous_apply 0)).inter
      ((isOpen_lt continuous_const (continuous_apply 1)).inter
        (isOpen_lt (continuous_apply 1) (continuous_const.mul (continuous_apply 0))))
  have hys : ∀ᶠ q in 𝓝 (![1, 1] : Fin 2 → ℝ), supply ssY q = {ssSupply q} := by
    filter_upwards [hopen.mem_nhds (by simp)] with q hq
    exact ss_supply_eq hq.1 hq.2.1 hq.2.2
  have hdiff := proposition_5_C_1_vii_symm_instance.2.2.1
  have h := proposition_5_C_1_vii_general hcl hys hdiff.hasFDerivAt
  exact ⟨hcl, hys, h.2.1, h.2.2.1⟩

end MWG.Production
