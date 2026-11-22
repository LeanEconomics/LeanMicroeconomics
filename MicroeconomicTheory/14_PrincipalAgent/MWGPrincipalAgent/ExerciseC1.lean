/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPrincipalAgent.Screen
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Exercise 14.C.1 (finitely many states)

MWG, Exercise 14.C.1, p. 508, and footnote 16, p. 497.

States `θ₀ < θ₁ < ⋯ < θ_{N-1}` with probabilities `p_i`, an infinitely risk-averse manager with
reservation level `c = v⁻¹(ū)`, and contracts `(w_i, e_i)`, `e_i ≥ 0`. The single-crossing
property: for `i < j`, `e ↦ g(e, θ_i) - g(e, θ_j)` is strictly increasing on `[0, ∞)`, and
`g(0, θ) = 0`. Write `x_i = w_i - g(e_i, θ_i)` for the manager's utility (money) in state `θ_i`
and `D_k(e) = g(e, θ_k) - g(e, θ_{k+1})`.

* `exercise_14_C_1_mono`: incentive compatibility forces nondecreasing efforts.
* `exercise_14_C_1_IR`: the reservation constraint of the lowest state and the incentive
  constraints imply all reservation constraints (Lemma 14.C.1).
* `exercise_14_C_1_rent`: the local downward incentive constraints give the rent
  `x_i ≥ c + Σ_{k<i} D_k(e_k)`; `exercise_14_C_1_bound`: hence the owner earns at most
  `Σ_i p_i (π(e_i) - g(e_i, θ_i)) - c - Σ_i p_i Σ_{k<i} D_k(e_k)`.
* `exercise_14_C_1_local`: footnote 16: with nondecreasing efforts, if the local downward
  constraints bind, all the incentive constraints hold. So the bound is attained by the contract
  in which `x_0 = c` and the local downward constraints bind, and an optimal contract maximizes
  the virtual surplus over nondecreasing efforts; the top state's effort enters only its own term
  (no distortion at the top), and every other effort is weighed against its rent
  `(Σ_{i>k} p_i) D_k(e_k)` (downward distortion).
-/

namespace MWG.PrincipalAgent

open Finset Set

/-- The incentive constraint: in state `θ_i` the manager prefers `(w_i, e_i)` to `(w_j, e_j)`. -/
def C1IC (g : ℝ → ℝ → ℝ) (θ w e : ℕ → ℝ) (i j : ℕ) : Prop :=
  w j - g (e j) (θ i) ≤ w i - g (e i) (θ i)

/-- **Exercise 14.C.1** (MWG, p. 508). With single crossing, the incentive constraints between
`i < j` force `e_i ≤ e_j`. -/
theorem exercise_14_C_1_mono {g : ℝ → ℝ → ℝ} {θ w e : ℕ → ℝ} {i j : ℕ}
    (hsc : StrictMonoOn (fun x => g x (θ i) - g x (θ j)) (Ici 0)) (hei : 0 ≤ e i)
    (hej : 0 ≤ e j) (h1 : C1IC g θ w e i j) (h2 : C1IC g θ w e j i) : e i ≤ e j := by
  unfold C1IC at h1 h2
  have : g (e i) (θ i) - g (e i) (θ j) ≤ g (e j) (θ i) - g (e j) (θ j) := by linarith
  exact (hsc.le_iff_le hei hej).1 this

/-- **Exercise 14.C.1**, Lemma 14.C.1 for `N` states: the reservation constraint of the lowest
state and the incentive constraint of state `i` towards state `0` give state `i`'s reservation
constraint. -/
theorem exercise_14_C_1_IR {g : ℝ → ℝ → ℝ} {θ w e : ℕ → ℝ} {c : ℝ} {i : ℕ}
    (hsc : StrictMonoOn (fun x => g x (θ 0) - g x (θ i)) (Ici 0)) (hg0 : ∀ t, g 0 t = 0)
    (he0 : 0 ≤ e 0) (hIR : c ≤ w 0 - g (e 0) (θ 0)) (hIC : C1IC g θ w e i 0) :
    c ≤ w i - g (e i) (θ i) := by
  have hD : g 0 (θ 0) - g 0 (θ i) ≤ g (e 0) (θ 0) - g (e 0) (θ i) :=
    hsc.monotoneOn (mem_Ici.2 le_rfl) (mem_Ici.2 he0) he0
  rw [hg0, hg0] at hD
  unfold C1IC at hIC
  linarith

/-- `D_k(e) = g(e, θ_k) - g(e, θ_{k+1})`. -/
def c1D (g : ℝ → ℝ → ℝ) (θ : ℕ → ℝ) (k : ℕ) (e : ℝ) : ℝ := g e (θ k) - g e (θ (k + 1))

/-- **Exercise 14.C.1**, the rents: the local downward constraints and the lowest state's
reservation constraint give `x_i ≥ c + Σ_{k<i} D_k(e_k)`. -/
theorem exercise_14_C_1_rent {g : ℝ → ℝ → ℝ} {θ w e : ℕ → ℝ} {c : ℝ}
    (hIR : c ≤ w 0 - g (e 0) (θ 0)) (hloc : ∀ k, C1IC g θ w e (k + 1) k) :
    ∀ i, c + ∑ k ∈ range i, c1D g θ k (e k) ≤ w i - g (e i) (θ i) := by
  intro i
  induction i with
  | zero => simpa using hIR
  | succ n ih =>
    rw [sum_range_succ]
    have := hloc n
    have hD : c1D g θ n (e n) = g (e n) (θ n) - g (e n) (θ (n + 1)) := rfl
    unfold C1IC at this
    linarith

/-- **Exercise 14.C.1**, the bound on the owner's profit (MWG, p. 508): with probabilities
`p_i ≥ 0`, every contract satisfying the lowest reservation constraint and the local downward
incentive constraints earns at most
`Σ_{i<N} p_i [π(e_i) - g(e_i, θ_i)] - c Σ p_i - Σ_{i<N} p_i Σ_{k<i} D_k(e_k)`. -/
theorem exercise_14_C_1_bound {g : ℝ → ℝ → ℝ} {θ w e p : ℕ → ℝ} {prof : ℝ → ℝ} {c : ℝ}
    {N : ℕ} (hp : ∀ i, 0 ≤ p i) (hIR : c ≤ w 0 - g (e 0) (θ 0))
    (hloc : ∀ k, C1IC g θ w e (k + 1) k) :
    ∑ i ∈ range N, p i * (prof (e i) - w i) ≤
      ∑ i ∈ range N, p i * (prof (e i) - g (e i) (θ i)) - c * ∑ i ∈ range N, p i -
        ∑ i ∈ range N, p i * ∑ k ∈ range i, c1D g θ k (e k) := by
  have hr := exercise_14_C_1_rent hIR hloc
  rw [mul_sum, ← sum_sub_distrib, ← sum_sub_distrib]
  refine sum_le_sum fun i _ => ?_
  have := mul_le_mul_of_nonneg_left (hr i) (hp i)
  nlinarith

/-- **Footnote 16 / Exercise 14.C.1**: with nondecreasing efforts and single crossing between
adjacent states, if every local downward incentive constraint binds then every incentive
constraint holds (downward and upward). -/
theorem exercise_14_C_1_local {g : ℝ → ℝ → ℝ} {θ w e : ℕ → ℝ}
    (hsc : ∀ k, MonotoneOn (c1D g θ k) (Ici 0)) (he : ∀ k, 0 ≤ e k) (hmono : Monotone e)
    (hbind : ∀ k, w (k + 1) - g (e (k + 1)) (θ (k + 1)) = w k - g (e k) (θ (k + 1))) :
    ∀ i j, C1IC g θ w e i j := by
  -- utilities: `x i = w i - g (e i) (θ i)`
  have step : ∀ k, (w (k + 1) - g (e (k + 1)) (θ (k + 1))) = (w k - g (e k) (θ k)) +
      c1D g θ k (e k) := fun k => by rw [hbind]; unfold c1D; ring
  -- downward: for `j ≤ i`, by induction on `i - j`
  have down : ∀ j d, C1IC g θ w e (j + d) j := by
    intro j d
    induction d with
    | zero => unfold C1IC; simp
    | succ d ih =>
      unfold C1IC at ih ⊢
      have hs := step (j + d)
      have hDm : c1D g θ (j + d) (e j) ≤ c1D g θ (j + d) (e (j + d)) :=
        hsc (j + d) (he j) (he _) (hmono (by omega))
      unfold c1D at hDm hs
      rw [show j + (d + 1) = j + d + 1 by omega]
      linarith
  -- upward: for `i ≤ j`
  have up : ∀ i d, C1IC g θ w e i (i + d) := by
    intro i d
    induction d with
    | zero => unfold C1IC; simp
    | succ d ih =>
      unfold C1IC at ih ⊢
      have hs := step (i + d)
      have hDm : c1D g θ (i + d) (e (i + d)) ≤ c1D g θ (i + d) (e (i + d + 1)) :=
        hsc (i + d) (he _) (he _) (hmono (by omega))
      -- single crossing between `i` and `i + d`: `g(·, θ_i) - g(·, θ_{i+d})` is nondecreasing
      have hcross : ∀ m, ∀ x y, 0 ≤ x → x ≤ y →
          g x (θ i) - g x (θ (i + m)) ≤ g y (θ i) - g y (θ (i + m)) := by
        intro m
        induction m with
        | zero => intro x y _ _; simp
        | succ m ihm =>
          intro x y hx hxy
          have h1 := ihm x y hx hxy
          have h2 : c1D g θ (i + m) x ≤ c1D g θ (i + m) y := hsc (i + m) hx (hx.trans hxy) hxy
          unfold c1D at h2
          rw [show i + (m + 1) = i + m + 1 by omega]
          linarith
      have hc := hcross d (e (i + d)) (e (i + d + 1)) (he _) (hmono (by omega))
      unfold c1D at hDm hs
      rw [show i + (d + 1) = i + d + 1 by omega]
      linarith
  intro i j
  rcases le_total j i with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    exact down j d
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    exact up i d

end MWG.PrincipalAgent
