/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGEquilibriumTime.SteadyStates

/-!
# Efficiency of the golden rule in the multisector model (MWG Section 20.E, p. 758)

MWG, Chapter 20, p. 758: in the `(N + 1)`-sector technology of Example 20.C.4, consumption
`G(k, k')` from capital `k ∈ ℝ^N` and investment `k'`, "we could also prove that the golden
rule path is efficient". At the golden rule `k̂` the interest rate is zero, so the supporting
prices of capital are constant: `∇₁G(k̂, k̂) = q = -∇₂G(k̂, k̂)` (`golden_rule_multisector`,
(20.E.1)).

`golden_rule_multisector_efficient`: if `G` lies below its tangent plane at `(k̂, k̂)` with this
zero-interest gradient `(q, -q)` by a quadratic margin `μ ‖k - k̂‖²` (strong concavity in the
current capital stock), then no bounded feasible capital path starting at `k̂` gives consumption
at least `Ĝ = G(k̂, k̂)` in every period and more in some period: the golden rule path is
efficient. Telescoping the tangent-plane inequality gives
`∑_{t < T} (c_t - Ĝ) + μ ∑_{t < T} ‖k_t - k̂‖² ≤ q · (k̂ - k_T)`; a gain `ε > 0` forces
`‖k_T - k̂‖² ≥ ε² / (q · q)` for all later `T`, so the left side grows without bound while the
right side stays bounded.

Some strict concavity is needed: for a linear `G` the golden rule is inefficient
(`golden_rule_linear_inefficient`). A proved instance of the hypotheses:
`golden_rule_quadratic_instance`.
-/

namespace MWG.EquilibriumTime

variable {N : ℕ}

/-- **The golden rule is efficient in the multisector model** (MWG, p. 758). Let `G` be the
consumption available from capital `k` and investment `k'` on a set `A` of feasible pairs, and
let `k̂` be a golden rule with zero-interest supporting gradient `(q, -q)` and a quadratic
margin: `G(k, k') ≤ G(k̂, k̂) + q · (k - k') - μ ‖k - k̂‖²` on `A`, `μ > 0`. If a bounded capital
path with `k_0 = k̂` and `(k_t, k_{t+1}) ∈ A` gives consumption `G(k_t, k_{t+1}) ≥ G(k̂, k̂)` in
every period, then it gives exactly `G(k̂, k̂)` in every period. -/
theorem golden_rule_multisector_efficient {G : (Fin N → ℝ) → (Fin N → ℝ) → ℝ}
    {A : Set ((Fin N → ℝ) × (Fin N → ℝ))} {khat q : Fin N → ℝ} {μ B : ℝ} (hμ : 0 < μ)
    (hsupp : ∀ x ∈ A, G x.1 x.2 ≤ G khat khat + q ⬝ᵥ (x.1 - x.2)
      - μ * ((x.1 - khat) ⬝ᵥ (x.1 - khat)))
    {k : ℕ → Fin N → ℝ} (hk0 : k 0 = khat) (hA : ∀ t, (k t, k (t + 1)) ∈ A)
    (hB : ∀ t i, |k t i| ≤ B) (hge : ∀ t, G khat khat ≤ G (k t) (k (t + 1))) :
    ∀ t, G (k t) (k (t + 1)) = G khat khat := by
  by_contra hne
  push Not at hne
  obtain ⟨s, hs⟩ := hne
  set ε := G (k s) (k (s + 1)) - G khat khat with hε
  have hεpos : 0 < ε := by have := hge s; rw [hε]; exact sub_pos.2 (lt_of_le_of_ne this hs.symm)
  set d : ℕ → ℝ := fun t => (k t - khat) ⬝ᵥ (k t - khat) with hd
  have hd0 : ∀ t, 0 ≤ d t := fun t => by
    simp only [hd, dotProduct, ← sq]; exact Finset.sum_nonneg fun i _ => sq_nonneg _
  -- telescoping
  have htel : ∀ T, ∑ t ∈ Finset.range T, (G (k t) (k (t + 1)) - G khat khat)
      + μ * ∑ t ∈ Finset.range T, d t ≤ q ⬝ᵥ (khat - k T) := by
    intro T
    induction T with
    | zero => simp [hk0]
    | succ T ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, mul_add]
      have h := hsupp _ (hA T)
      simp only at h
      have e : q ⬝ᵥ (khat - k (T + 1)) = q ⬝ᵥ (khat - k T) + q ⬝ᵥ (k T - k (T + 1)) := by
        rw [← dotProduct_add]; congr 1; abel
      rw [e]
      simp only [hd] at ih ⊢
      linarith
  -- the gain forces the capital stock to stay away from `k̂`
  have hgain : ∀ T, s < T → ε ≤ q ⬝ᵥ (khat - k T) - μ * ∑ t ∈ Finset.range T, d t := by
    intro T hT
    have h := htel T
    have hsum : ε ≤ ∑ t ∈ Finset.range T, (G (k t) (k (t + 1)) - G khat khat) := by
      rw [hε]
      exact Finset.single_le_sum (f := fun t => G (k t) (k (t + 1)) - G khat khat)
        (fun t _ => sub_nonneg.2 (hge t)) (Finset.mem_range.2 hT)
    linarith
  have hqq : 0 < q ⬝ᵥ q := by
    have h := hgain (s + 1) (by omega)
    have hS : 0 ≤ μ * ∑ t ∈ Finset.range (s + 1), d t :=
      mul_nonneg hμ.le (Finset.sum_nonneg fun t _ => hd0 t)
    by_contra hle
    push Not at hle
    have hq0 : q = 0 := by
      funext i
      have : q i ^ 2 ≤ q ⬝ᵥ q := by
        simp only [dotProduct, ← sq]
        exact Finset.single_le_sum (fun j _ => sq_nonneg (q j)) (Finset.mem_univ i)
      have : q i ^ 2 = 0 := le_antisymm (by linarith) (sq_nonneg _)
      simpa using this
    rw [hq0, zero_dotProduct] at h
    linarith
  set a := ε ^ 2 / (q ⬝ᵥ q) with ha
  have hapos : 0 < a := by rw [ha]; positivity
  have hdlow : ∀ T, s < T → a ≤ d T := by
    intro T hT
    have h1 : ε ≤ q ⬝ᵥ (khat - k T) := by
      have := hgain T hT
      have : 0 ≤ μ * ∑ t ∈ Finset.range T, d t :=
        mul_nonneg hμ.le (Finset.sum_nonneg fun t _ => hd0 t)
      linarith
    -- Cauchy-Schwarz: `(q · v)² ≤ (q · q)(v · v)` with `v = k̂ - k_T`
    have hcs : (q ⬝ᵥ (khat - k T)) ^ 2 ≤ (q ⬝ᵥ q) * d T := by
      have e : d T = (khat - k T) ⬝ᵥ (khat - k T) := by
        simp only [hd, dotProduct, Pi.sub_apply]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [e]
      have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ q (khat - k T)
      simpa only [dotProduct, ← sq] using this
    rw [ha, div_le_iff₀ hqq]
    nlinarith
  -- the right side is bounded
  set C := ∑ i, |q i| * (|khat i| + B) with hC
  have hbd : ∀ T, q ⬝ᵥ (khat - k T) ≤ C := by
    intro T
    simp only [dotProduct, hC, Pi.sub_apply]
    refine Finset.sum_le_sum fun i _ => ?_
    calc q i * (khat i - k T i) ≤ |q i * (khat i - k T i)| := le_abs_self _
      _ = |q i| * |khat i - k T i| := abs_mul _ _
      _ ≤ |q i| * (|khat i| + B) := mul_le_mul_of_nonneg_left
          ((abs_sub _ _).trans (by linarith [hB T i])) (abs_nonneg _)
  -- the sum of the `d_t` grows without bound
  obtain ⟨n, hn⟩ := exists_nat_gt (C / (μ * a))
  have hgrow : ∀ m : ℕ, (m : ℝ) * a ≤ ∑ t ∈ Finset.range (s + 1 + m), d t := by
    intro m
    induction m with
    | zero =>
      rw [Nat.cast_zero, zero_mul, add_zero]
      exact Finset.sum_nonneg fun t _ => hd0 t
    | succ m ih =>
      rw [show s + 1 + (m + 1) = s + 1 + m + 1 by omega, Finset.sum_range_succ]
      have := hdlow (s + 1 + m) (by omega)
      push_cast
      linarith
  have h := hgain (s + 1 + n) (by omega)
  have hb := hbd (s + 1 + n)
  have hg := hgrow n
  have : C < μ * ((n : ℝ) * a) := by
    rw [div_lt_iff₀ (mul_pos hμ hapos)] at hn
    nlinarith
  nlinarith

/-- Some strict concavity is needed (MWG, p. 758): for the linear technology
`G(k, k') = k - k'` (one capital good) the golden rule `k̂ = 1` is inefficient: investing `1/2`
less in period 0 gives consumption `1/2` instead of `0` then and `0` afterwards. -/
theorem golden_rule_linear_inefficient :
    let k : ℕ → ℝ := fun t => if t = 0 then 1 else 1 / 2
    k 0 = 1 ∧ (∀ t, (1 : ℝ) - 1 ≤ k t - k (t + 1)) ∧ (1 : ℝ) - 1 < k 0 - k 1 := by
  intro k
  refine ⟨rfl, fun t => ?_, by simp [k]; norm_num⟩
  rcases t with _ | t
  · simp [k]; norm_num
  · simp [k]

/-- A proved instance of the hypotheses of `golden_rule_multisector_efficient`:
`G(k, k') = 1 · (k - k') - ‖k - 1‖²` with golden rule `k̂ = 1`, `q = 1`, `μ = 1`. -/
theorem golden_rule_quadratic_instance :
    ∀ x ∈ (Set.univ : Set ((Fin N → ℝ) × (Fin N → ℝ))),
      (fun k k' : Fin N → ℝ => (fun _ => (1 : ℝ)) ⬝ᵥ (k - k') - (k - fun _ => 1) ⬝ᵥ
          (k - fun _ => 1)) x.1 x.2
        ≤ (fun k k' : Fin N → ℝ => (fun _ => (1 : ℝ)) ⬝ᵥ (k - k') - (k - fun _ => 1) ⬝ᵥ
          (k - fun _ => 1)) (fun _ => 1) (fun _ => 1)
          + (fun _ => (1 : ℝ)) ⬝ᵥ (x.1 - x.2) - 1 * ((x.1 - fun _ => 1) ⬝ᵥ (x.1 - fun _ => 1)) :=
  fun x _ => by simp

end MWG.EquilibriumTime
