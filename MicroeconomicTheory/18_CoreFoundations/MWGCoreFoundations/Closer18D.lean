/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGCoreFoundations.Redistribution
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Proposition 18.D.1 for a continuum of types (MWG Section 18.D, p. 669)

Proposition 18.D.1: in an exchange economy with a continuum of consumer types whose
characteristics present cannot be split into two disconnected classes, a Pareto optimal,
self-selective, interior allocation with differentiable utilities is Walrasian. The book's proof
is "far from rigorous" and "limited to `L = 2`". `Redistribution` proves the main step assuming
that the net-trade path `z(t)` is continuous on `[0, 1]` and differentiable inside, with
aggregate feasibility a finite convex combination. Here the types are `t ∈ [0, 1]` with
characteristics `(u(·; t), ω(t))`, the population is a finite measure `ν` on the types, and:

* `c18_planar_flat_const`: (pure analysis, `L = 2`) if `z` is continuous on `[0, 1]` with values
  in `ℝ²` and `p·(z s - z t) = o(‖z s - z t‖)` uniformly, then `p·z` is constant on `[0, 1]`.
  The proof: locally `p·z` is a function of the orthogonal coordinate `q·z` with arbitrarily
  small Lipschitz constant (intermediate value theorem plus a partition of the `q·z` range), and
  `[0, 1]` is chained by short intervals.
* `c18_flat_of_noEnvy`: (any `L`) no envy among all types, differentiable utilities whose
  derivatives are uniformly equicontinuous near the bundles, and gradients `λ(t) p` with
  `λ(t) ≥ λ₀ > 0` (the first-order condition of the supporting price) give exactly that
  uniform flatness (mean value theorem on the segment from `x(t)` to `ω(t) + z(s)`).
* `c18_continuousOn_of_noEnvy`: the continuity of `z(t)`, which the book asserts informally, is
  DERIVED: from no envy, a common supporting price (each `x(t)` is best in its budget at `p`),
  utilities jointly continuous in `(t, x)` and strictly quasiconcave, continuous endowments,
  bounded net trades and interior bundles (a uniform margin `η`).
* `proposition_18_D_1_continuum`: for `L = 2`, with the measure-theoretic feasibility
  `∫_{[0,1]} z dν = 0` and `ν([0, 1]) ≠ 0`, every type's net trade has value `p·z(t) = 0` and
  every bundle is the type's Walrasian demand at `p`: the allocation is Walrasian.
* Definitions: `c18IsMeasureFeasible`, `c18IsMeasurePareto` (measure-theoretic Pareto
  optimality), `c18IsSelfSelective` (the book's anonymity: one generalized budget set `B` for
  all types present), with `c18_isSelfSelective_iff_noEnvy`.
* `c18_isMeasurePareto_of_supported`: the hypothesis "`p` supports `x`" (with local
  nonsatiation) implies measure-theoretic Pareto optimality, so the theorem applies to the
  price-supported Pareto optima.
* `proposition_18_D_1_continuum_instance`: all hypotheses hold in a concrete economy
  (quadratic utilities, `ω(t) = (1/2 + t, 3/2 - t)`, Lebesgue measure on `[0, 1]`).

Not formalised (see the source map, OPEN): the second welfare theorem for the continuum (that a
measure-theoretic Pareto optimum is supported by a common `p` with gradients `λ(t) p`), and the
case `L ≥ 3`, where the flatness step fails.
-/

namespace MWG.CoreFoundations

open MWG.ConsumerChoice

/-- A coordinate bound in `ℝ²`: with `q = (-p₂, p₁)`,
`(p₁² + p₂²) |Δ_l| ≤ (|p₁| + |p₂|)(|p·Δ| + |q·Δ|)`. -/
theorem c18_abs_coord_le (p Δ : Fin 2 → ℝ) (l : Fin 2) :
    (p 0 ^ 2 + p 1 ^ 2) * |Δ l| ≤
      (|p 0| + |p 1|) * (|p 0 * Δ 0 + p 1 * Δ 1| + |-p 1 * Δ 0 + p 0 * Δ 1|) := by
  have hP : 0 ≤ p 0 ^ 2 + p 1 ^ 2 := by positivity
  set a := p 0 * Δ 0 + p 1 * Δ 1
  set b := -p 1 * Δ 0 + p 0 * Δ 1
  have key : ∀ (j : Fin 2) (c d : ℝ), (p 0 ^ 2 + p 1 ^ 2) * Δ j = c * a + d * b →
      |c| ≤ |p 0| + |p 1| → |d| ≤ |p 0| + |p 1| →
      (p 0 ^ 2 + p 1 ^ 2) * |Δ j| ≤ (|p 0| + |p 1|) * (|a| + |b|) := by
    intro j c d e hc hd
    rw [← abs_of_nonneg hP, ← abs_mul, e]
    calc |c * a + d * b| ≤ |c * a| + |d * b| := abs_add_le _ _
      _ = |c| * |a| + |d| * |b| := by rw [abs_mul, abs_mul]
      _ ≤ (|p 0| + |p 1|) * |a| + (|p 0| + |p 1|) * |b| :=
          add_le_add (mul_le_mul_of_nonneg_right hc (abs_nonneg a))
            (mul_le_mul_of_nonneg_right hd (abs_nonneg b))
      _ = (|p 0| + |p 1|) * (|a| + |b|) := by ring
  fin_cases l
  · refine key 0 (p 0) (-p 1) (by simp only [a, b]; ring) ?_ ?_
    · linarith [abs_nonneg (p 1)]
    · rw [abs_neg]; linarith [abs_nonneg (p 0)]
  · refine key 1 (p 1) (p 0) (by simp only [a, b]; ring) ?_ ?_
    · linarith [abs_nonneg (p 0)]
    · linarith [abs_nonneg (p 1)]

/-- The dot product in `ℝ²`. -/
theorem c18_dot_two (p v : Fin 2 → ℝ) : p ⬝ᵥ v = p 0 * v 0 + p 1 * v 1 := by
  simp [dotProduct, Fin.sum_univ_two]

/-- Two points of `[[s, t]]` are at most `|s - t|` apart. -/
theorem c18_abs_sub_le_of_mem_uIcc {s t x y : ℝ} (hx : x ∈ Set.uIcc s t)
    (hy : y ∈ Set.uIcc s t) : |x - y| ≤ |s - t| := by
  rw [Set.mem_uIcc] at hx hy
  rw [abs_sub_le_iff]
  rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hy with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
    constructor <;> cases abs_cases (s - t) <;> linarith

/-- `a + θ (b - a) ∈ [[a, b]]` for `θ ∈ [0, 1]`. -/
theorem c18_mem_uIcc_affine {a b θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    a + θ * (b - a) ∈ Set.uIcc a b := by
  rw [Set.mem_uIcc]
  rcases le_total a b with h | h
  · left; constructor <;> nlinarith
  · right; constructor <;> nlinarith

/-- **Proposition 18.D.1**, the key analytic step for `L = 2` (MWG, p. 669: "the portion `M` of
the frontier of `B` containing all the net trades present ... is a straight segment with normal
`p`"). If `z : [0, 1] → ℝ²` is continuous, `p ≠ 0`, and `p·(z s - z t) = o(‖z s - z t‖)`
uniformly in `s, t`, then `p·z` is constant on `[0, 1]`. -/
theorem c18_planar_flat_const {z : ℝ → Fin 2 → ℝ} {p : Fin 2 → ℝ} (hp : p ≠ 0)
    (hz : ContinuousOn z (Set.Icc 0 1))
    (hflat : ∀ ε > 0, ∃ r > 0, ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖z s - z t‖ < r → |p ⬝ᵥ (z s - z t)| ≤ ε * ‖z s - z t‖) :
    ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1, p ⬝ᵥ z s = p ⬝ᵥ z t := by
  set P := p 0 ^ 2 + p 1 ^ 2 with hP
  set A := |p 0| + |p 1| with hA
  have hPpos : 0 < P := by
    by_contra h
    have h0 : p 0 = 0 := by nlinarith [sq_nonneg (p 0), sq_nonneg (p 1)]
    have h1 : p 1 = 0 := by nlinarith [sq_nonneg (p 0), sq_nonneg (p 1)]
    exact hp (by funext l; fin_cases l <;> simp [h0, h1])
  have hApos : 0 < A := by
    have h1 : P ≤ A ^ 2 := by
      rw [hP, hA, add_sq, sq_abs, sq_abs]
      nlinarith [mul_nonneg (abs_nonneg (p 0)) (abs_nonneg (p 1))]
    nlinarith [abs_nonneg (p 0), abs_nonneg (p 1)]
  -- the orthogonal coordinate `q·z`
  have hgd : ∀ s t, p ⬝ᵥ (z s - z t) = p ⬝ᵥ z s - p ⬝ᵥ z t := fun s t => dotProduct_sub _ _ _
  have hnorm : ∀ s t, P * ‖z s - z t‖ ≤ A * (|p ⬝ᵥ z s - p ⬝ᵥ z t| +
      |(-p 1 * z s 0 + p 0 * z s 1) - (-p 1 * z t 0 + p 0 * z t 1)|) := by
    intro s t
    have hle : ‖z s - z t‖ ≤ A * (|p ⬝ᵥ z s - p ⬝ᵥ z t| +
        |(-p 1 * z s 0 + p 0 * z s 1) - (-p 1 * z t 0 + p 0 * z t 1)|) / P := by
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun l => ?_
      rw [Real.norm_eq_abs, le_div_iff₀ hPpos, mul_comm]
      have e1 : p ⬝ᵥ z s - p ⬝ᵥ z t = p 0 * (z s - z t) 0 + p 1 * (z s - z t) 1 := by
        rw [c18_dot_two, c18_dot_two, Pi.sub_apply, Pi.sub_apply]; ring
      have e2 : (-p 1 * z s 0 + p 0 * z s 1) - (-p 1 * z t 0 + p 0 * z t 1) =
          -p 1 * (z s - z t) 0 + p 0 * (z s - z t) 1 := by
        rw [Pi.sub_apply, Pi.sub_apply]; ring
      rw [e1, e2]
      exact c18_abs_coord_le p (z s - z t) l
    rwa [le_div_iff₀ hPpos, mul_comm] at hle
  -- (1) `|Δ(p·z)| ≤ ε' |Δ(q·z)|` for close values
  have hstar : ∀ ε' > 0, ∃ r > 0, ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖z s - z t‖ < r → |p ⬝ᵥ z s - p ⬝ᵥ z t| ≤
        ε' * |(-p 1 * z s 0 + p 0 * z s 1) - (-p 1 * z t 0 + p 0 * z t 1)| := by
    intro ε' hε'
    set m := min (1 / 2 : ℝ) (ε' / 2) with hm
    have hm0 : 0 < m := lt_min (by norm_num) (by linarith)
    have hm1 : m ≤ 1 / 2 := min_le_left _ _
    have hm2 : m ≤ ε' / 2 := min_le_right _ _
    obtain ⟨r, hr, hfl⟩ := hflat (P / A * m) (by positivity)
    refine ⟨r, hr, fun s hs t ht hst => ?_⟩
    have h1 := hfl s hs t ht hst
    rw [hgd] at h1
    have h2 := hnorm s t
    set g := |p ⬝ᵥ z s - p ⬝ᵥ z t|
    set a := |(-p 1 * z s 0 + p 0 * z s 1) - (-p 1 * z t 0 + p 0 * z t 1)|
    have h3 : P * g ≤ P * (m * (g + a)) := by
      calc P * g ≤ P * (P / A * m * ‖z s - z t‖) := mul_le_mul_of_nonneg_left h1 hPpos.le
        _ = P / A * m * (P * ‖z s - z t‖) := by ring
        _ ≤ P / A * m * (A * (g + a)) := mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = P * (m * (g + a)) := by field_simp
    have h4 : g ≤ m * (g + a) := le_of_mul_le_mul_left h3 hPpos
    have hg0 : 0 ≤ g := abs_nonneg _
    have ha0 : 0 ≤ a := abs_nonneg _
    nlinarith [mul_le_mul_of_nonneg_right hm1 hg0, mul_le_mul_of_nonneg_right hm2 ha0]
  -- (2) a window on which `z` moves little
  obtain ⟨r₁, hr₁, hst₁⟩ := hstar 1 one_pos
  obtain ⟨δ, hδ, hδz⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hz) r₁ hr₁
  have hwin : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1, |s - t| < δ →
      |p ⬝ᵥ z s - p ⬝ᵥ z t| ≤ |(-p 1 * z s 0 + p 0 * z s 1) - (-p 1 * z t 0 + p 0 * z t 1)| ∧
      P * ‖z s - z t‖ ≤
        A * (2 * |(-p 1 * z s 0 + p 0 * z s 1) - (-p 1 * z t 0 + p 0 * z t 1)|) := by
    intro s hs t ht hst
    have hd : ‖z s - z t‖ < r₁ := by
      have := hδz s hs t ht (by rwa [Real.dist_eq])
      rwa [dist_eq_norm] at this
    have h1 := hst₁ s hs t ht hd
    rw [one_mul] at h1
    refine ⟨h1, (hnorm s t).trans ?_⟩
    have := mul_le_mul_of_nonneg_left (add_le_add_left h1
      |(-p 1 * z s 0 + p 0 * z s 1) - (-p 1 * z t 0 + p 0 * z t 1)|) hApos.le
    linarith
  -- the coordinate `q·z` is continuous
  have hac : ContinuousOn (fun u => -p 1 * z u 0 + p 0 * z u 1) (Set.Icc 0 1) :=
    (continuousOn_const.mul ((continuous_apply 0).comp_continuousOn hz)).add
      (continuousOn_const.mul ((continuous_apply 1).comp_continuousOn hz))
  -- (3) local constancy
  have hloc : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1, |s - t| < δ →
      p ⬝ᵥ z s = p ⬝ᵥ z t := by
    intro s hs t ht hst
    by_contra hne
    set D := |(-p 1 * z t 0 + p 0 * z t 1) - (-p 1 * z s 0 + p 0 * z s 1)| with hD
    set G := |p ⬝ᵥ z t - p ⬝ᵥ z s| with hG
    have hGpos : 0 < G := abs_pos.2 (sub_ne_zero.2 (Ne.symm hne))
    have hD0 : 0 ≤ D := abs_nonneg _
    set ε' := G / (2 * (D + 1)) with hε'
    have hε'pos : 0 < ε' := by positivity
    obtain ⟨r, hr, hstr⟩ := hstar ε' hε'pos
    obtain ⟨N₀, hN₀⟩ := exists_nat_gt (2 * A * D / (P * r))
    set N := N₀ + 1 with hN
    have hNpos : (0 : ℝ) < N := by positivity
    have hNbig : 2 * A * D / (P * r) < N := by
      have : (N₀ : ℝ) < N := by rw [hN]; push_cast; linarith
      linarith
    have hsub : Set.uIcc s t ⊆ Set.Icc 0 1 := Set.uIcc_subset_Icc hs ht
    have hivt := intermediate_value_uIcc (hac.mono hsub)
    have hval : ∀ k : ℕ, ∃ c ∈ Set.uIcc s t, -p 1 * z c 0 + p 0 * z c 1 =
        (-p 1 * z s 0 + p 0 * z s 1) + (min k N : ℕ) / (N : ℝ) *
          ((-p 1 * z t 0 + p 0 * z t 1) - (-p 1 * z s 0 + p 0 * z s 1)) := by
      intro k
      have h0 : (0 : ℝ) ≤ (min k N : ℕ) / (N : ℝ) := by positivity
      have h1 : (min k N : ℕ) / (N : ℝ) ≤ 1 := by
        rw [div_le_one hNpos]; exact_mod_cast min_le_right k N
      exact hivt (c18_mem_uIcc_affine h0 h1)
    choose c hc hca using hval
    have hcI : ∀ k, c k ∈ Set.Icc (0 : ℝ) 1 := fun k => hsub (hc k)
    have hcδ : ∀ j k, |c j - c k| < δ := fun j k =>
      (c18_abs_sub_le_of_mem_uIcc (hc j) (hc k)).trans_lt hst
    -- the endpoints
    have hend : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, |x - y| < δ →
        -p 1 * z x 0 + p 0 * z x 1 = -p 1 * z y 0 + p 0 * z y 1 → p ⬝ᵥ z x = p ⬝ᵥ z y := by
      intro x hx y hy hxy he
      have := (hwin x hx y hy hxy).1
      rw [he, sub_self, abs_zero] at this
      exact sub_eq_zero.1 (abs_nonpos_iff.1 this)
    have hs0 : p ⬝ᵥ z (c 0) = p ⬝ᵥ z s := by
      refine hend _ (hcI 0) s hs ?_ ?_
      · exact (c18_abs_sub_le_of_mem_uIcc (hc 0) Set.left_mem_uIcc).trans_lt hst
      · rw [hca 0]; simp
    have htN : p ⬝ᵥ z (c N) = p ⬝ᵥ z t := by
      refine hend _ (hcI N) t ht ?_ ?_
      · exact (c18_abs_sub_le_of_mem_uIcc (hc N) Set.right_mem_uIcc).trans_lt hst
      · rw [hca N, min_self, div_self hNpos.ne']; ring
    -- consecutive points
    have hstep : ∀ k ∈ Finset.range N, |p ⬝ᵥ z (c (k + 1)) - p ⬝ᵥ z (c k)| ≤ ε' * (D / N) := by
      intro k hk
      rw [Finset.mem_range] at hk
      have hda : (-p 1 * z (c (k + 1)) 0 + p 0 * z (c (k + 1)) 1) -
          (-p 1 * z (c k) 0 + p 0 * z (c k) 1) =
          ((-p 1 * z t 0 + p 0 * z t 1) - (-p 1 * z s 0 + p 0 * z s 1)) / N := by
        rw [hca, hca, min_eq_left (by omega : k + 1 ≤ N), min_eq_left hk.le]
        push_cast
        field_simp
        ring
      have hdaabs : |(-p 1 * z (c (k + 1)) 0 + p 0 * z (c (k + 1)) 1) -
          (-p 1 * z (c k) 0 + p 0 * z (c k) 1)| = D / N := by
        rw [hda, abs_div, abs_of_pos hNpos]
      have hw := (hwin _ (hcI (k + 1)) _ (hcI k) (hcδ (k + 1) k)).2
      rw [hdaabs] at hw
      have hzr : ‖z (c (k + 1)) - z (c k)‖ < r := by
        have h1 : ‖z (c (k + 1)) - z (c k)‖ ≤ A * (2 * (D / N)) / P := by
          rw [le_div_iff₀ hPpos, mul_comm]; exact hw
        refine h1.trans_lt ?_
        rw [div_lt_iff₀ hPpos]
        have h2 : 2 * A * D < N * (P * r) := by
          rwa [div_lt_iff₀ (by positivity)] at hNbig
        rw [show A * (2 * (D / N)) = 2 * A * D / N by ring, div_lt_iff₀ hNpos]
        linarith
      have := hstr _ (hcI (k + 1)) _ (hcI k) hzr
      rwa [hdaabs] at this
    have htel : p ⬝ᵥ z (c N) - p ⬝ᵥ z (c 0) =
        ∑ k ∈ Finset.range N, (p ⬝ᵥ z (c (k + 1)) - p ⬝ᵥ z (c k)) :=
      (Finset.sum_range_sub (fun k => p ⬝ᵥ z (c k)) N).symm
    have hbound : G ≤ ε' * D := by
      rw [hG, ← htN, ← hs0, htel]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_sum hstep).trans ?_
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp
      rfl
    have : ε' * D < G := by
      rw [hε']
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  -- (4) chaining along `[0, 1]`
  intro s hs t ht
  obtain ⟨M₀, hM₀⟩ := exists_nat_gt (1 / δ)
  set M := M₀ + 1 with hM
  have hMpos : (0 : ℝ) < M := by positivity
  have hMδ : 1 / (M : ℝ) < δ := by
    have : (M₀ : ℝ) < M := by rw [hM]; push_cast; linarith
    rw [div_lt_iff₀ hMpos]
    rw [div_lt_iff₀ hδ] at hM₀
    nlinarith
  have hy : ∀ j : ℕ, j ≤ M → s + (j : ℝ) / M * (t - s) ∈ Set.Icc (0 : ℝ) 1 := by
    intro j hj
    have h0 : (0 : ℝ) ≤ (j : ℝ) / M := by positivity
    have h1 : (j : ℝ) / M ≤ 1 := by rw [div_le_one hMpos]; exact_mod_cast hj
    have := c18_mem_uIcc_affine (a := s) (b := t) h0 h1
    exact Set.uIcc_subset_Icc hs ht this
  have hchain : ∀ j : ℕ, j ≤ M → p ⬝ᵥ z (s + (j : ℝ) / M * (t - s)) = p ⬝ᵥ z s := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      rw [← ih (by omega)]
      refine hloc _ (hy _ hj) _ (hy _ (by omega)) ?_
      have hts : |t - s| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
      have e : s + ((j + 1 : ℕ) : ℝ) / M * (t - s) - (s + (j : ℝ) / M * (t - s)) =
          (t - s) / M := by push_cast; ring
      rw [e, abs_div, abs_of_pos hMpos]
      refine lt_of_le_of_lt ?_ hMδ
      exact div_le_div_of_nonneg_right hts hMpos.le
  have := hchain M le_rfl
  rw [div_self hMpos.ne', one_mul, add_sub_cancel] at this
  exact this.symm

/-- **Proposition 18.D.1**, the flatness step for any `L` (MWG, p. 669: "if envy is to be
prevented, then similar individuals must be treated similarly"). If no type envies another type's
net trade, the bundles `x(t) = ω(t) + z(t)` are interior with a uniform margin `η`, every `u(·; t)`
is differentiable near the bundles with derivatives `D(t, y)` that are uniformly equicontinuous
(uniformly in `t`), and the derivative at `x(t)` is `λ(t) p` with `λ(t) ≥ λ₀ > 0`, then
`p·(z s - z t) = o(‖z s - z t‖)` uniformly in `s, t`. -/
theorem c18_flat_of_noEnvy {L : ℕ} {u : ℝ → (Fin L → ℝ) → ℝ} {ω z : ℝ → Fin L → ℝ}
    {p : Fin L → ℝ} {D : ℝ → (Fin L → ℝ) → (Fin L → ℝ) →L[ℝ] ℝ} {lam : ℝ → ℝ} {η lam₀ : ℝ}
    (hη : 0 < η) (hlam₀ : 0 < lam₀)
    (hint : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ l, η ≤ ω t l + z t l)
    (henvy : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1, ω t + z s ∈ nonnegOrthant L →
      u t (ω t + z s) ≤ u t (ω t + z t))
    (hD : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y : Fin L → ℝ, (∀ l, η / 2 ≤ y l) →
      HasFDerivAt (u t) (D t y) y)
    (hDuc : ∀ ε > 0, ∃ ρ > 0, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y y' : Fin L → ℝ,
      (∀ l, η / 2 ≤ y l) → (∀ l, η / 2 ≤ y' l) → ‖y - y'‖ < ρ → ‖D t y - D t y'‖ ≤ ε)
    (hgrad : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ v, D t (ω t + z t) v = lam t * (p ⬝ᵥ v))
    (hlam : ∀ t ∈ Set.Icc (0 : ℝ) 1, lam₀ ≤ lam t) :
    ∀ ε > 0, ∃ r > 0, ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖z s - z t‖ < r → |p ⬝ᵥ (z s - z t)| ≤ ε * ‖z s - z t‖ := by
  intro ε hε
  obtain ⟨ρ, hρ, hρD⟩ := hDuc (ε * lam₀) (by positivity)
  have hone : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖z s - z t‖ < min ρ (η / 2) →
      lam t * (p ⬝ᵥ (z s - z t)) ≤ ε * lam₀ * ‖z s - z t‖ := by
    intro s hs t ht hst
    set x := ω t + z t with hx
    set Δ := z s - z t with hΔdef
    have hΔ : ‖Δ‖ < η / 2 := lt_of_lt_of_le hst (min_le_right _ _)
    have hseg : ∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ l, η / 2 ≤ (x + θ • Δ) l := by
      intro θ hθ l
      have h1 : |Δ l| ≤ ‖Δ‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm Δ l
      have h2 : |θ * Δ l| ≤ ‖Δ‖ := by
        rw [abs_mul, abs_of_nonneg hθ.1]
        nlinarith [abs_nonneg (Δ l), hθ.2]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have := hint t ht l
      simp only [hx, Pi.add_apply]
      linarith [neg_abs_le (θ * Δ l)]
    have hderiv : ∀ θ ∈ Set.Icc (0 : ℝ) 1,
        HasDerivAt (fun θ : ℝ => u t (x + θ • Δ)) (D t (x + θ • Δ) Δ) θ := by
      intro θ hθ
      have hγ : HasDerivAt (fun θ : ℝ => x + θ • Δ) Δ θ := by
        simpa using ((hasDerivAt_id θ).smul_const Δ).const_add x
      exact (hD t ht _ (hseg θ hθ)).comp_hasDerivAt θ hγ
    obtain ⟨θ, hθ, hmv⟩ := exists_hasDerivAt_eq_slope (fun θ : ℝ => u t (x + θ • Δ))
      (fun θ => D t (x + θ • Δ) Δ) zero_lt_one
      (fun θ hθ => (hderiv θ hθ).continuousAt.continuousWithinAt)
      (fun θ hθ => hderiv θ (Set.Ioo_subset_Icc_self hθ))
    have hx1 : x + (1 : ℝ) • Δ = ω t + z s := by
      rw [one_smul, hx, hΔdef]; abel
    have hfeas : ω t + z s ∈ nonnegOrthant L := fun l => by
      have := hseg 1 ⟨zero_le_one, le_rfl⟩ l
      rw [hx1] at this
      linarith
    have henv := henvy t ht s hs hfeas
    rw [hx1, zero_smul, add_zero, sub_zero, div_one] at hmv
    have hθI : θ ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hθ
    have hclose : ‖x + θ • Δ - x‖ < ρ := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hθI.1]
      calc θ * ‖Δ‖ ≤ ‖Δ‖ := by nlinarith [norm_nonneg Δ, hθI.2]
        _ < ρ := lt_of_lt_of_le hst (min_le_left _ _)
    have hx0 : ∀ l, η / 2 ≤ x l := fun l => by
      have := hseg 0 ⟨le_rfl, zero_le_one⟩ l
      rwa [zero_smul, add_zero] at this
    have hdiff := hρD t ht (x + θ • Δ) x (hseg θ hθI) hx0 hclose
    have hop : (D t x - D t (x + θ • Δ)) Δ ≤ ε * lam₀ * ‖Δ‖ := by
      calc (D t x - D t (x + θ • Δ)) Δ ≤ ‖(D t x - D t (x + θ • Δ)) Δ‖ := Real.le_norm_self _
        _ ≤ ‖D t x - D t (x + θ • Δ)‖ * ‖Δ‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ ε * lam₀ * ‖Δ‖ := by
          rw [norm_sub_rev]; exact mul_le_mul_of_nonneg_right hdiff (norm_nonneg _)
    rw [← hgrad t ht]
    have e : D t x Δ = D t (x + θ • Δ) Δ + (D t x - D t (x + θ • Δ)) Δ := by simp
    rw [e, hmv]
    linarith
  refine ⟨min ρ (η / 2), lt_min hρ (by positivity), fun s hs t ht hst => ?_⟩
  have h1 := hone s hs t ht hst
  have h2 := hone t ht s hs (by rwa [norm_sub_rev])
  rw [norm_sub_rev] at h2
  have e : p ⬝ᵥ (z t - z s) = -(p ⬝ᵥ (z s - z t)) := by rw [← dotProduct_neg, neg_sub]
  rw [e] at h2
  have hl1 := hlam t ht
  have hl2 := hlam s hs
  have hn := norm_nonneg (z s - z t)
  rw [abs_le]
  constructor
  · by_contra hc
    rw [not_le] at hc
    have h3 : lam s * (ε * ‖z s - z t‖) < lam s * -(p ⬝ᵥ (z s - z t)) :=
      mul_lt_mul_of_pos_left (by linarith) (by linarith)
    nlinarith [mul_le_mul_of_nonneg_right hl2 (mul_nonneg hε.le hn)]
  · by_contra hc
    rw [not_le] at hc
    have h3 : lam t * (ε * ‖z s - z t‖) < lam t * (p ⬝ᵥ (z s - z t)) :=
      mul_lt_mul_of_pos_left hc (by linarith)
    nlinarith [mul_le_mul_of_nonneg_right hl1 (mul_nonneg hε.le hn)]

open Filter Topology in
/-- **Proposition 18.D.1**, the continuity of `z(t)` (MWG, p. 669: "A key fact is that `z(t)` is
continuous as a function of `t`. This is intuitive."), DERIVED. Assume: no envy among the types
`t ∈ [0, 1]`; a common price `p` supports every bundle `x(t) = ω(t) + z(t)` (each is best in its
budget `{y ≥ 0 : p·y ≤ p·x(t)}`); interior bundles with a uniform margin `η > 0`; bounded net
trades; continuous endowments; utilities jointly continuous in `(t, x)` and strictly
quasiconcave (strictly convex preferences). Then `t ↦ z(t)` is continuous on `[0, 1]`. -/
theorem c18_continuousOn_of_noEnvy {L : ℕ} {u : ℝ → (Fin L → ℝ) → ℝ} {ω z : ℝ → Fin L → ℝ}
    {p : Fin L → ℝ} {η M : ℝ} (hη : 0 < η)
    (hint : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ l, η ≤ ω t l + z t l)
    (hzb : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖z t‖ ≤ M) (hω : ContinuousOn ω (Set.Icc 0 1))
    (hu : ContinuousOn (fun q : ℝ × (Fin L → ℝ) => u q.1 q.2)
      (Set.Icc 0 1 ×ˢ {y | ∀ l, η / 2 ≤ y l}))
    (hsq : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x y : Fin L → ℝ, (∀ l, η / 2 ≤ x l) →
      (∀ l, η / 2 ≤ y l) → x ≠ y → min (u t x) (u t y) < u t ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y))
    (henvy : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1, ω t + z s ∈ nonnegOrthant L →
      u t (ω t + z s) ≤ u t (ω t + z t))
    (hsupp : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ nonnegOrthant L, p ⬝ᵥ y ≤ p ⬝ᵥ (ω t + z t) →
      u t y ≤ u t (ω t + z t)) :
    ContinuousOn z (Set.Icc 0 1) := by
  intro t ht
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨hns1, hns2⟩ := tendsto_nhdsWithin_iff.1 hns
  obtain ⟨zb, -, φ, hφ, hlim⟩ := tendsto_subseq_of_frequently_bounded
    (Metric.isBounded_closedBall (x := (0 : Fin L → ℝ)) (r := M))
    (hns2.mono fun k hk => mem_closedBall_zero_iff.2 (hzb _ hk)).frequently
  refine ⟨φ, ?_⟩
  set sk : ℕ → ℝ := fun k => ns (φ k) with hskdef
  have hsk : Tendsto sk atTop (𝓝 t) := hns1.comp hφ.tendsto_atTop
  have hskI : ∀ᶠ k in atTop, sk k ∈ Set.Icc (0 : ℝ) 1 := hφ.tendsto_atTop.eventually hns2
  have hzk : Tendsto (fun k => z (sk k)) atTop (𝓝 zb) := hlim
  have hωk : Tendsto (fun k => ω (sk k)) atTop (𝓝 (ω t)) :=
    (hω t ht).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hsk, hskI⟩)
  set R : Set (Fin L → ℝ) := {y | ∀ l, η / 2 ≤ y l} with hR
  have hRc : IsClosed R := by
    rw [hR, Set.ofPred_forall]
    exact isClosed_iInter fun l => isClosed_le continuous_const (continuous_apply l)
  have hjl : ∀ (y : ℕ → Fin L → ℝ) (yb : Fin L → ℝ), Tendsto y atTop (𝓝 yb) → yb ∈ R →
      (∀ᶠ k in atTop, y k ∈ R) → Tendsto (fun k => u (sk k) (y k)) atTop (𝓝 (u t yb)) := by
    intro y yb hy hyb hyR
    exact (hu (t, yb) ⟨ht, hyb⟩).tendsto.comp (tendsto_nhdsWithin_iff.2
      ⟨hsk.prodMk_nhds hy, (hskI.and hyR).mono fun k hk => ⟨hk.1, hk.2⟩⟩)
  have hjl' : ∀ (y : ℕ → Fin L → ℝ) (yb : Fin L → ℝ), Tendsto y atTop (𝓝 yb) → yb ∈ R →
      (∀ᶠ k in atTop, y k ∈ R) → Tendsto (fun k => u t (y k)) atTop (𝓝 (u t yb)) := by
    intro y yb hy hyb hyR
    exact (hu (t, yb) ⟨ht, hyb⟩).tendsto.comp (tendsto_nhdsWithin_iff.2
      ⟨tendsto_const_nhds.prodMk_nhds hy, hyR.mono fun k hk => ⟨ht, hk⟩⟩)
  set xb := ω t + zb with hxb
  set xt := ω t + z t with hxt
  have hxk : Tendsto (fun k => ω (sk k) + z (sk k)) atTop (𝓝 xb) := hωk.add hzk
  have hxbη : ∀ l, η ≤ xb l := fun l =>
    ge_of_tendsto (((continuous_apply l).tendsto _).comp hxk)
      (hskI.mono fun k hk => hint _ hk l)
  have hxbR : xb ∈ R := fun l => by linarith [hxbη l]
  have hxtR : xt ∈ R := fun l => by
    change η / 2 ≤ ω t l + z t l
    linarith [hint t ht l]
  have hωclose : ∀ᶠ k in atTop, dist (ω (sk k)) (ω t) < η / 2 :=
    Metric.tendsto_nhds.1 hωk (η / 2) (by positivity)
  have hcoord : ∀ k, dist (ω (sk k)) (ω t) < η / 2 → ∀ l, |ω (sk k) l - ω t l| < η / 2 :=
    fun k hk l => lt_of_le_of_lt (by rw [← Real.dist_eq]; exact dist_le_pi_dist _ _ l) hk
  have hxkR : ∀ᶠ k in atTop, ω (sk k) + z (sk k) ∈ R :=
    hskI.mono fun k hk l => by
      change η / 2 ≤ ω (sk k) l + z (sk k) l
      linarith [hint _ hk l]
  have hA : ∀ᶠ k in atTop, ω t + z (sk k) ∈ R := (hskI.and hωclose).mono fun k hk l => by
    have h1 := hint _ hk.1 l
    have h2 := hcoord k hk.2 l
    simp only [Pi.add_apply]
    linarith [le_abs_self (ω (sk k) l - ω t l)]
  have hB : ∀ᶠ k in atTop, ω (sk k) + z t ∈ R := hωclose.mono fun k hk l => by
    have h1 := hint t ht l
    have h2 := hcoord k hk l
    simp only [Pi.add_apply]
    linarith [neg_abs_le (ω (sk k) l - ω t l)]
  -- type `t` does not envy `z(s_k)`, type `s_k` does not envy `z(t)`
  have hF1 : u t xb ≤ u t xt := by
    refine le_of_tendsto (hjl' _ xb (tendsto_const_nhds.add hzk) hxbR hA) ?_
    exact (hskI.and hA).mono fun k hk => henvy t ht _ hk.1 fun l => by
      linarith [hk.2 l]
  have hF2 : u t xt ≤ u t xb := by
    refine le_of_tendsto_of_tendsto (hjl _ xt (hωk.add tendsto_const_nhds) hxtR hB)
      (hjl _ xb hxk hxbR hxkR) ?_
    exact (hskI.and hB).mono fun k hk => henvy _ hk.1 t ht fun l => by linarith [hk.2 l]
  have hzbt : zb = z t := by
    by_contra hne
    have hne' : xt ≠ xb := fun h => hne (add_left_cancel h).symm
    set m := (1 / 2 : ℝ) • xt + (1 / 2 : ℝ) • xb with hm
    have hstrict := hsq t ht xt xb hxtR hxbR hne'
    rw [min_eq_left hF2] at hstrict
    have hmR : m ∈ R := fun l => by
      simp only [hm, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linarith [hxtR l, hxbR l]
    have hm0 : m ∈ nonnegOrthant L := fun l => by linarith [hmR l]
    have hpm : p ⬝ᵥ m = (p ⬝ᵥ xt + p ⬝ᵥ xb) / 2 := by
      rw [hm, dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
      ring
    rcases le_or_gt (p ⬝ᵥ xb) (p ⬝ᵥ xt) with h | h
    · have := hsupp t ht m hm0 (by rw [hpm]; linarith)
      linarith
    · have hdotc : Continuous fun x : Fin L → ℝ => p ⬝ᵥ x := by
        unfold dotProduct; fun_prop
      have hev : ∀ᶠ k in atTop, p ⬝ᵥ m < p ⬝ᵥ (ω (sk k) + z (sk k)) :=
        ((hdotc.tendsto xb).comp hxk).eventually (lt_mem_nhds (by rw [hpm]; linarith))
      have hle : u t m ≤ u t xb := by
        refine le_of_tendsto_of_tendsto (hjl _ m tendsto_const_nhds hmR
          (Eventually.of_forall fun _ => hmR)) (hjl _ xb hxk hxbR hxkR) ?_
        exact (hskI.and hev).mono fun k hk => hsupp _ hk.1 m hm0 hk.2.le
      linarith
  rw [← hzbt]
  exact hlim

open MeasureTheory in
/-- **Proposition 18.D.1** (MWG, p. 669), continuum form for `L = 2`. Types `t ∈ [0, 1]` with
utilities `u(·; t)` and endowments `ω(t)`, a population measure `ν` (finite on compacts, e.g.
Lebesgue measure) with `ν([0, 1]) ≠ 0`, and net trades `z(t)` that are feasible in the measure
sense, `∫_{[0,1]} z dν = 0`. Assume the allocation is self-selective (no type envies another
type's net trade, `c18_isSelfSelective_iff_noEnvy`), interior (uniform margin `η`), bounded,
and supported by a price `p ≠ 0` with first-order conditions `Du(x(t); t) = λ(t) p`,
`λ(t) ≥ λ₀ > 0`, as a Pareto optimum is (`c18_isMeasurePareto_of_supported`), with endowments
continuous in `t`, utilities jointly continuous, strictly quasiconcave and differentiable with
uniformly equicontinuous derivatives near the bundles. Then `z` is continuous (derived),
`p·z(t) = 0` for every type and every bundle is the type's Walrasian demand at `p`: the
allocation is a Walrasian equilibrium allocation. -/
theorem proposition_18_D_1_continuum {u : ℝ → (Fin 2 → ℝ) → ℝ} {ω z : ℝ → Fin 2 → ℝ}
    {p : Fin 2 → ℝ} {D : ℝ → (Fin 2 → ℝ) → (Fin 2 → ℝ) →L[ℝ] ℝ} {lam : ℝ → ℝ}
    {η lam₀ M : ℝ} (ν : Measure ℝ) [IsFiniteMeasureOnCompacts ν] (hp : p ≠ 0) (hη : 0 < η)
    (hlam₀ : 0 < lam₀)
    (hint : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ l, η ≤ ω t l + z t l)
    (hzb : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖z t‖ ≤ M) (hω : ContinuousOn ω (Set.Icc 0 1))
    (hu : ContinuousOn (fun q : ℝ × (Fin 2 → ℝ) => u q.1 q.2)
      (Set.Icc 0 1 ×ˢ {y | ∀ l, η / 2 ≤ y l}))
    (hsq : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x y : Fin 2 → ℝ, (∀ l, η / 2 ≤ x l) →
      (∀ l, η / 2 ≤ y l) → x ≠ y → min (u t x) (u t y) < u t ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y))
    (henvy : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1, ω t + z s ∈ nonnegOrthant 2 →
      u t (ω t + z s) ≤ u t (ω t + z t))
    (hsupp : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ nonnegOrthant 2, p ⬝ᵥ y ≤ p ⬝ᵥ (ω t + z t) →
      u t y ≤ u t (ω t + z t))
    (hD : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y : Fin 2 → ℝ, (∀ l, η / 2 ≤ y l) →
      HasFDerivAt (u t) (D t y) y)
    (hDuc : ∀ ε > 0, ∃ ρ > 0, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y y' : Fin 2 → ℝ,
      (∀ l, η / 2 ≤ y l) → (∀ l, η / 2 ≤ y' l) → ‖y - y'‖ < ρ → ‖D t y - D t y'‖ ≤ ε)
    (hgrad : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ v, D t (ω t + z t) v = lam t * (p ⬝ᵥ v))
    (hlam : ∀ t ∈ Set.Icc (0 : ℝ) 1, lam₀ ≤ lam t)
    (hν : ν (Set.Icc 0 1) ≠ 0) (hfeas : ∀ l, ∫ t in Set.Icc 0 1, z t l ∂ν = 0) :
    ContinuousOn z (Set.Icc 0 1) ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1, p ⬝ᵥ z t = 0 ∧
      ∀ y ∈ nonnegOrthant 2, p ⬝ᵥ y ≤ p ⬝ᵥ ω t → u t y ≤ u t (ω t + z t) := by
  have hzc := c18_continuousOn_of_noEnvy hη hint hzb hω hu hsq henvy hsupp
  have hflat := c18_flat_of_noEnvy hη hlam₀ hint henvy hD hDuc hgrad hlam
  have hconst := c18_planar_flat_const hp hzc hflat
  have h0I : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hintl : ∀ l, IntegrableOn (fun t => z t l) (Set.Icc 0 1) ν := fun l =>
    ((continuous_apply l).comp_continuousOn hzc).integrableOn_compact isCompact_Icc
  have hI1 : ∫ t in Set.Icc 0 1, p ⬝ᵥ z t ∂ν = 0 := by
    calc ∫ t in Set.Icc 0 1, p ⬝ᵥ z t ∂ν = ∫ t in Set.Icc 0 1, ∑ l, p l * z t l ∂ν := rfl
      _ = ∑ l, ∫ t in Set.Icc 0 1, p l * z t l ∂ν :=
          integral_finsetSum _ fun l _ => (hintl l).const_mul (p l)
      _ = ∑ l, p l * ∫ t in Set.Icc 0 1, z t l ∂ν := by
          simp only [integral_const_mul]
      _ = 0 := by simp [hfeas]
  have hI2 : ∫ t in Set.Icc 0 1, p ⬝ᵥ z t ∂ν = ν.real (Set.Icc 0 1) * (p ⬝ᵥ z 0) := by
    rw [setIntegral_congr_fun measurableSet_Icc (fun t ht => hconst t ht 0 h0I),
      setIntegral_const, smul_eq_mul]
  have hreal : ν.real (Set.Icc 0 1) ≠ 0 := by
    rw [measureReal_def]
    exact ENNReal.toReal_ne_zero.2 ⟨hν, isCompact_Icc.measure_lt_top.ne⟩
  have hc : p ⬝ᵥ z 0 = 0 := by
    rw [hI1] at hI2
    exact (mul_eq_zero.1 hI2.symm).resolve_left hreal
  refine ⟨hzc, fun t ht => ?_⟩
  have hzt : p ⬝ᵥ z t = 0 := by rw [hconst t ht 0 h0I, hc]
  have he : p ⬝ᵥ (ω t + z t) = p ⬝ᵥ ω t := by rw [dotProduct_add, hzt, add_zero]
  exact ⟨hzt, fun y hy hpy => hsupp t ht y hy (he ▸ hpy)⟩

/-! ### Definitions: self-selectivity, measure feasibility, measure-theoretic Pareto optimality -/

/-- **Definition 18.D.1** for a continuum of types (MWG, p. 666): the allocation with net trades
`z(t)` is self-selective (anonymous) if one generalized budget set `B` serves all types present:
`z(t) ∈ B` and `z(t)` is best for type `t` among the net trades `b ∈ B` with `ω(t) + b ≥ 0`. -/
def c18IsSelfSelective {L : ℕ} (u : ℝ → (Fin L → ℝ) → ℝ) (ω z : ℝ → Fin L → ℝ) : Prop :=
  ∃ B : Set (Fin L → ℝ), ∀ t ∈ Set.Icc (0 : ℝ) 1, z t ∈ B ∧
    ∀ b ∈ B, ω t + b ∈ nonnegOrthant L → u t (ω t + b) ≤ u t (ω t + z t)

/-- **Definition 18.D.1** for a continuum of types (MWG, p. 666): self-selective iff no type
envies another type's net trade (take `B = {z(s) : s ∈ [0, 1]}`). -/
theorem c18_isSelfSelective_iff_noEnvy {L : ℕ} {u : ℝ → (Fin L → ℝ) → ℝ}
    {ω z : ℝ → Fin L → ℝ} :
    c18IsSelfSelective u ω z ↔ ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ω t + z s ∈ nonnegOrthant L → u t (ω t + z s) ≤ u t (ω t + z t) := by
  constructor
  · rintro ⟨B, hB⟩ t ht s hs h
    exact (hB t ht).2 (z s) (hB s hs).1 h
  · intro h
    refine ⟨z '' Set.Icc 0 1, fun t ht => ⟨⟨t, ht, rfl⟩, ?_⟩⟩
    rintro b ⟨s, hs, rfl⟩ hb
    exact h t ht s hs hb

open MeasureTheory in
/-- **Section 18.D** for a continuum of types: the net trades `z(t)`, `t ∈ [0, 1]`, are feasible
for the population measure `ν` if they are integrable and `∫_{[0,1]} z dν = 0`. -/
def c18IsMeasureFeasible {L : ℕ} (ν : Measure ℝ) (z : ℝ → Fin L → ℝ) : Prop :=
  ∀ l, IntegrableOn (fun t => z t l) (Set.Icc 0 1) ν ∧ ∫ t in Set.Icc 0 1, z t l ∂ν = 0

open MeasureTheory in
/-- **Proposition 18.D.1** for a continuum of types: measure-theoretic Pareto optimality. The net
trades `z` are feasible and no feasible `z'` makes `ν`-almost every type weakly better off (with
`ω(t) + z'(t) ≥ 0`) and a set of types of positive measure strictly better off. -/
def c18IsMeasurePareto {L : ℕ} (ν : Measure ℝ) (u : ℝ → (Fin L → ℝ) → ℝ)
    (ω z : ℝ → Fin L → ℝ) : Prop :=
  c18IsMeasureFeasible ν z ∧ ¬ ∃ z' : ℝ → Fin L → ℝ, c18IsMeasureFeasible ν z' ∧
    (∀ᵐ t ∂(ν.restrict (Set.Icc 0 1)), ω t + z' t ∈ nonnegOrthant L ∧
      u t (ω t + z t) ≤ u t (ω t + z' t)) ∧
    ν.restrict (Set.Icc 0 1) {t | u t (ω t + z t) < u t (ω t + z' t)} ≠ 0

open MeasureTheory in
/-- The value of feasible net trades is zero: `∫_{[0,1]} p·z dν = 0`, with `p·z` integrable. -/
theorem c18_integral_dot_eq_zero {L : ℕ} {ν : Measure ℝ} {z : ℝ → Fin L → ℝ}
    (hf : c18IsMeasureFeasible ν z) (p : Fin L → ℝ) :
    IntegrableOn (fun t => p ⬝ᵥ z t) (Set.Icc 0 1) ν ∧
      ∫ t in Set.Icc 0 1, p ⬝ᵥ z t ∂ν = 0 := by
  have hi : ∀ l ∈ Finset.univ, Integrable (fun t => p l * z t l) (ν.restrict (Set.Icc 0 1)) :=
    fun l _ => (hf l).1.const_mul (p l)
  refine ⟨integrable_finsetSum _ hi, ?_⟩
  calc ∫ t in Set.Icc 0 1, p ⬝ᵥ z t ∂ν = ∫ t in Set.Icc 0 1, ∑ l, p l * z t l ∂ν := rfl
    _ = ∑ l, ∫ t in Set.Icc 0 1, p l * z t l ∂ν := integral_finsetSum _ hi
    _ = ∑ l, p l * ∫ t in Set.Icc 0 1, z t l ∂ν := by simp only [integral_const_mul]
    _ = 0 := by simp [fun l => (hf l).2]

open MeasureTheory in
/-- **Proposition 18.D.1**, the hypothesis "`p` supports `x`" (MWG, p. 669: "Let `p` be the price
vector supporting `x*` as a Pareto optimal allocation") is consistent with, and yields,
measure-theoretic Pareto optimality: if `p ≥ 0`, `p ≠ 0`, every type's bundle is best in its
budget at `p` and utilities are strictly increasing along the diagonal, then a feasible
allocation is Pareto optimal in the measure sense (the first welfare theorem for the
continuum). -/
theorem c18_isMeasurePareto_of_supported {L : ℕ} {u : ℝ → (Fin L → ℝ) → ℝ}
    {ω z : ℝ → Fin L → ℝ} {p : Fin L → ℝ} (ν : Measure ℝ) (hfeas : c18IsMeasureFeasible ν z)
    (hpsum : 0 < ∑ l, p l)
    (hsupp : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ nonnegOrthant L, p ⬝ᵥ y ≤ p ⬝ᵥ (ω t + z t) →
      u t y ≤ u t (ω t + z t))
    (hmono : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ nonnegOrthant L, ∀ δ : ℝ, 0 < δ →
      u t y < u t (y + fun _ => δ)) :
    c18IsMeasurePareto ν u ω z := by
  refine ⟨hfeas, ?_⟩
  rintro ⟨z', hf', hae, hS⟩
  have hcheap : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ nonnegOrthant L,
      p ⬝ᵥ y < p ⬝ᵥ (ω t + z t) → u t y < u t (ω t + z t) := by
    intro t ht y hy hpy
    set δ := (p ⬝ᵥ (ω t + z t) - p ⬝ᵥ y) / ∑ l, p l with hδ
    have hδpos : 0 < δ := div_pos (by linarith) hpsum
    have hyδ : y + (fun _ => δ) ∈ nonnegOrthant L := fun l => by
      simp only [Pi.add_apply]; linarith [hy l]
    have hpδ : p ⬝ᵥ (y + fun _ => δ) = p ⬝ᵥ (ω t + z t) := by
      rw [dotProduct_add]
      have : p ⬝ᵥ (fun _ : Fin L => δ) = δ * ∑ l, p l := by
        simp only [dotProduct, Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _ => mul_comm _ _
      rw [this, hδ, div_mul_cancel₀ _ hpsum.ne']
      ring
    exact (hmono t ht y hy δ hδpos).trans_le (hsupp t ht _ hyδ hpδ.le)
  set μ := ν.restrict (Set.Icc (0 : ℝ) 1) with hμ
  have hmem : ∀ᵐ t ∂μ, t ∈ Set.Icc (0 : ℝ) 1 := ae_restrict_mem measurableSet_Icc
  have hle : ∀ᵐ t ∂μ, p ⬝ᵥ z t ≤ p ⬝ᵥ z' t := by
    filter_upwards [hae, hmem] with t ht hti
    by_contra hc
    rw [not_le] at hc
    have := hcheap t hti _ ht.1 (by rw [dotProduct_add, dotProduct_add]; linarith)
    linarith [ht.2]
  have hlt : {t | u t (ω t + z t) < u t (ω t + z' t)} ≤ᵐ[μ] {t | p ⬝ᵥ z t < p ⬝ᵥ z' t} := by
    filter_upwards [hae, hmem] with t ht hti
    intro h
    by_contra hc
    have hc' : p ⬝ᵥ z' t ≤ p ⬝ᵥ z t := not_lt.1 hc
    have := hsupp t hti _ ht.1 (by rw [dotProduct_add, dotProduct_add]; linarith)
    exact absurd h (not_lt.2 this)
  obtain ⟨hi, hz0⟩ := c18_integral_dot_eq_zero hfeas p
  obtain ⟨hi', hz0'⟩ := c18_integral_dot_eq_zero hf' p
  have hg0 : 0 ≤ᵐ[μ] fun t => p ⬝ᵥ z' t - p ⬝ᵥ z t := hle.mono fun t ht => by
    simp only [Pi.zero_apply]; linarith
  have hpos : 0 < ∫ t, (p ⬝ᵥ z' t - p ⬝ᵥ z t) ∂μ := by
    rw [integral_pos_iff_support_of_nonneg_ae hg0 (hi'.sub hi)]
    refine lt_of_lt_of_le (pos_iff_ne_zero.2 hS) ((measure_mono_ae hlt).trans
      (measure_mono fun t ht => ?_))
    rw [Function.mem_support]
    rw [Set.mem_ofPred_eq] at ht
    linarith
  rw [integral_sub hi' hi, hz0, hz0', sub_zero] at hpos
  exact lt_irrefl _ hpos

/-! ### An instance of all the hypotheses -/

/-- Instance data: the quadratic utility `u(y) = y₁ - y₁²/4 + y₂ - y₂²/4` (the same for all
types). -/
noncomputable def c18InstU : ℝ → (Fin 2 → ℝ) → ℝ :=
  fun _ y => y 0 - y 0 ^ 2 / 4 + (y 1 - y 1 ^ 2 / 4)

/-- Instance data: endowments `ω(t) = (1/2 + t, 3/2 - t)`. -/
noncomputable def c18InstOmega : ℝ → Fin 2 → ℝ := fun t => ![1 / 2 + t, 3 / 2 - t]

/-- Instance data: net trades `z(t) = (1/2 - t, t - 1/2)` (every type consumes `(1, 1)`). -/
noncomputable def c18InstZ : ℝ → Fin 2 → ℝ := fun t => ![1 / 2 - t, t - 1 / 2]

/-- Instance data: the derivative `Du(y) v = (1 - y₁/2) v₁ + (1 - y₂/2) v₂`. -/
noncomputable def c18InstD : ℝ → (Fin 2 → ℝ) → (Fin 2 → ℝ) →L[ℝ] ℝ := fun _ y =>
  (1 - y 0 / 2) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0 +
    (1 - y 1 / 2) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1

theorem c18InstD_apply (t : ℝ) (y v : Fin 2 → ℝ) :
    c18InstD t y v = (1 - y 0 / 2) * v 0 + (1 - y 1 / 2) * v 1 := by
  simp [c18InstD]

theorem c18InstU_mid (x y : Fin 2 → ℝ) :
    c18InstU 0 ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) =
      (c18InstU 0 x + c18InstU 0 y) / 2 + ((x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2) / 16 := by
  simp only [c18InstU, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

open MeasureTheory in
/-- **Proposition 18.D.1** (MWG, p. 669), an instance of every hypothesis of
`proposition_18_D_1_continuum`: types `t ∈ [0, 1]` with Lebesgue measure, the quadratic utility
`c18InstU`, endowments `(1/2 + t, 3/2 - t)`, net trades `(1/2 - t, t - 1/2)`, `p = (1, 1)`,
`λ = 1/2`, margin `η = 1`; the conclusion (every type's bundle `(1, 1)` is her Walrasian demand)
follows. -/
theorem proposition_18_D_1_continuum_instance :
    ContinuousOn c18InstZ (Set.Icc 0 1) ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1, ![1, 1] ⬝ᵥ c18InstZ t = 0 ∧
      ∀ y ∈ nonnegOrthant 2, ![1, 1] ⬝ᵥ y ≤ ![1, 1] ⬝ᵥ c18InstOmega t →
        c18InstU t y ≤ c18InstU t (c18InstOmega t + c18InstZ t) := by
  have hx : ∀ t, c18InstOmega t + c18InstZ t = ![1, 1] := fun t => by
    funext l; fin_cases l <;> simp [c18InstOmega, c18InstZ] <;> ring
  have hu1 : ∀ t, c18InstU t ![1, 1] = 3 / 2 := fun t => by
    simp [c18InstU]; norm_num
  have hzc : Continuous c18InstZ := by
    refine continuous_pi fun l => ?_
    fin_cases l
    · exact continuous_const.sub continuous_id
    · exact continuous_id.sub continuous_const
  refine proposition_18_D_1_continuum (D := c18InstD) (lam := fun _ => 1 / 2) (η := 1)
    (lam₀ := 1 / 2) (M := 1 / 2) (volume : Measure ℝ) (by
      intro h; have := congrFun h 0; simp at this) one_pos (by norm_num) ?_ ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro t _ l
    rw [← Pi.add_apply, hx]
    fin_cases l <;> simp
  · intro t ht
    refine (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun l => ?_
    rw [Real.norm_eq_abs, abs_le]
    fin_cases l <;> simp [c18InstZ] <;> constructor <;> linarith [ht.1, ht.2]
  · refine Continuous.continuousOn (continuous_pi fun l => ?_)
    fin_cases l
    · exact continuous_const.add continuous_id
    · exact continuous_const.sub continuous_id
  · refine Continuous.continuousOn ?_
    simp only [c18InstU]
    fun_prop
  · intro t _ x y _ _ hxy
    have hm := c18InstU_mid x y
    simp only [c18InstU] at hm ⊢
    have hpos : 0 < (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
      by_contra hc
      have h0 : x 0 = y 0 := by nlinarith [sq_nonneg (x 0 - y 0), sq_nonneg (x 1 - y 1)]
      have h1 : x 1 = y 1 := by nlinarith [sq_nonneg (x 0 - y 0), sq_nonneg (x 1 - y 1)]
      exact hxy (by funext l; fin_cases l <;> simp [h0, h1])
    rw [hm]
    have := min_le_left (x 0 - x 0 ^ 2 / 4 + (x 1 - x 1 ^ 2 / 4))
      (y 0 - y 0 ^ 2 / 4 + (y 1 - y 1 ^ 2 / 4))
    have := min_le_right (x 0 - x 0 ^ 2 / 4 + (x 1 - x 1 ^ 2 / 4))
      (y 0 - y 0 ^ 2 / 4 + (y 1 - y 1 ^ 2 / 4))
    linarith
  · intro t _ s _ _
    rw [hx, hu1]
    simp only [c18InstU, c18InstOmega, c18InstZ, Pi.add_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    nlinarith [sq_nonneg (1 / 2 + t + (1 / 2 - s) - (3 / 2 - t + (s - 1 / 2)))]
  · intro t _ y hy hpy
    rw [hx, hu1]
    rw [hx, c18_dot_two, c18_dot_two] at hpy
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_mul] at hpy
    simp only [c18InstU]
    have h0 := hy 0
    have h1 := hy 1
    nlinarith [sq_nonneg (y 0 - y 1), mul_nonneg (by linarith : (0 : ℝ) ≤ 2 - (y 0 + y 1))
      (by linarith : (0 : ℝ) ≤ 6 - (y 0 + y 1))]
  · intro t _ y _
    have ha : ∀ j : Fin 2, HasFDerivAt (fun x : Fin 2 → ℝ => x j)
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) j) y := fun j =>
      hasFDerivAt_apply j y
    have h1 := (ha 0).sub (((ha 0).mul (ha 0)).const_smul (1 / 4 : ℝ))
    have h2 := (ha 1).sub (((ha 1).mul (ha 1)).const_smul (1 / 4 : ℝ))
    have h := h1.add h2
    have e : c18InstU t = fun x : Fin 2 → ℝ =>
        x 0 - (1 / 4 : ℝ) • (x 0 * x 0) + (x 1 - (1 / 4 : ℝ) • (x 1 * x 1)) := by
      funext x; simp only [c18InstU, smul_eq_mul]; ring
    rw [e]
    refine h.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
    rw [c18InstD_apply]
    simp
    ring
  · intro ε hε
    refine ⟨ε, hε, fun t _ y y' _ _ hyy => ?_⟩
    refine (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_).trans hyy.le
    rw [show (c18InstD t y - c18InstD t y') v = c18InstD t y v - c18InstD t y' v from rfl,
      c18InstD_apply, c18InstD_apply, Real.norm_eq_abs]
    have h0 : |y 0 - y' 0| ≤ ‖y - y'‖ := by
      rw [← Real.norm_eq_abs, ← Pi.sub_apply]; exact norm_le_pi_norm _ 0
    have h1 : |y 1 - y' 1| ≤ ‖y - y'‖ := by
      rw [← Real.norm_eq_abs, ← Pi.sub_apply]; exact norm_le_pi_norm _ 1
    have v0 : |v 0| ≤ ‖v‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm _ 0
    have v1 : |v 1| ≤ ‖v‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm _ 1
    have e : (1 - y 0 / 2) * v 0 + (1 - y 1 / 2) * v 1 -
        ((1 - y' 0 / 2) * v 0 + (1 - y' 1 / 2) * v 1) =
        -((y 0 - y' 0) * v 0) / 2 - (y 1 - y' 1) * v 1 / 2 := by ring
    rw [e]
    calc |-((y 0 - y' 0) * v 0) / 2 - (y 1 - y' 1) * v 1 / 2|
        ≤ |y 0 - y' 0| * |v 0| / 2 + |y 1 - y' 1| * |v 1| / 2 := by
          refine (abs_sub _ _).trans (le_of_eq ?_)
          rw [abs_div, abs_div, abs_neg, abs_mul, abs_mul, abs_two]
      _ ≤ ‖y - y'‖ * ‖v‖ / 2 + ‖y - y'‖ * ‖v‖ / 2 := by
          gcongr
      _ = ‖y - y'‖ * ‖v‖ := by ring
  · intro t _ v
    rw [hx, c18InstD_apply, c18_dot_two]
    simp
    ring
  · intro t _
    exact le_rfl
  · simp [Real.volume_Icc]
  · intro l
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
    fin_cases l
    · simp only [c18InstZ, Fin.zero_eta, Matrix.cons_val_zero]
      rw [intervalIntegral.integral_sub intervalIntegrable_const
        intervalIntegral.intervalIntegrable_id]
      simp [integral_id]
    · simp only [c18InstZ, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [intervalIntegral.integral_sub intervalIntegral.intervalIntegrable_id
        intervalIntegrable_const]
      simp [integral_id]

end MWG.CoreFoundations
