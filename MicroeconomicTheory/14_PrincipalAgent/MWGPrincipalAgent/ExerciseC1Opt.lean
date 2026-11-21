/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPrincipalAgent.ExerciseC1

/-!
# Exercise 14.C.1: the optimal contract with `N` states

MWG, Exercise 14.C.1, p. 508, with the model of `ExerciseC1` (an infinitely risk-averse manager,
reservation level `c`, states `θ₀, …, θ_{N-1}` with probabilities `p_i > 0`).

* `C1Feas`, `c1Prof`: feasible contracts (nonnegative efforts, all reservation and all incentive
  constraints among the `N` states) and the owner's expected profit.
* `c1Rent`, `c1Wage`, `c1VS`: the minimal rents `Σ_{k<i} D_k(e_k)`, the wages that pay exactly
  these rents, and the virtual surplus `Σ_i p_i [π(e_i) - g(e_i, θ_i) - c - Σ_{k<i} D_k(e_k)]`.
* `c1_prof_le_VS`: every feasible contract earns at most the virtual surplus of its efforts;
  `c1_wage_feasible`, `c1_prof_wage`: for nondecreasing efforts the minimal-rent wages are feasible
  and earn exactly the virtual surplus.
* `exercise_14_C_1_opt`: **the characterization**. In every optimal contract efforts are
  nondecreasing, the reservation constraint of the lowest state binds, every local downward
  incentive constraint binds, and the efforts maximize the virtual surplus among nondecreasing
  effort profiles; `exercise_14_C_1_suff` is the converse.
* `exercise_14_C_1_distortion`: if `e*_i` uniquely maximizes `π(e) - g(e, θ_i)` and the `e*_i` are
  nondecreasing, then every optimal contract has `e_i ≤ e*_i` (downward distortion) and
  `e_{N-1} = e*_{N-1}` (no distortion at the top).
* `exercise_14_C_1_instance`: two states, `π(e) = e`, `g(e, θ) = e²/(2θ)`, `θ_i = i + 1`,
  `p = (1/2, 1/2)`, `c = 0`: efforts `(2/3, 2)` against first-best efforts `(1, 2)`.
-/

namespace MWG.PrincipalAgent

open Finset Set

/-- Feasible contracts with `N` states: nonnegative efforts and all reservation and incentive
constraints among states `0, …, N-1`. -/
def C1Feas (g : ℝ → ℝ → ℝ) (θ : ℕ → ℝ) (c : ℝ) (N : ℕ) (w e : ℕ → ℝ) : Prop :=
  (∀ i < N, 0 ≤ e i) ∧ (∀ i < N, c ≤ w i - g (e i) (θ i)) ∧
    ∀ i < N, ∀ j < N, C1IC g θ w e i j

/-- The owner's expected profit `Σ_i p_i (π(e_i) - w_i)`. -/
def c1Prof (p : ℕ → ℝ) (prof : ℝ → ℝ) (N : ℕ) (w e : ℕ → ℝ) : ℝ :=
  ∑ i ∈ range N, p i * (prof (e i) - w i)

/-- The minimal rent of state `i`: `Σ_{k<i} D_k(e_k)`. -/
def c1Rent (g : ℝ → ℝ → ℝ) (θ : ℕ → ℝ) (e : ℕ → ℝ) (i : ℕ) : ℝ :=
  ∑ k ∈ range i, c1D g θ k (e k)

/-- The wages paying exactly the minimal rents: `w_i = g(e_i, θ_i) + c + Σ_{k<i} D_k(e_k)`. -/
def c1Wage (g : ℝ → ℝ → ℝ) (θ : ℕ → ℝ) (c : ℝ) (e : ℕ → ℝ) (i : ℕ) : ℝ :=
  g (e i) (θ i) + c + c1Rent g θ e i

/-- The virtual surplus `Σ_i p_i [π(e_i) - g(e_i, θ_i) - c - Σ_{k<i} D_k(e_k)]`. -/
def c1VS (g : ℝ → ℝ → ℝ) (θ p : ℕ → ℝ) (prof : ℝ → ℝ) (c : ℝ) (N : ℕ) (e : ℕ → ℝ) : ℝ :=
  ∑ i ∈ range N, p i * (prof (e i) - g (e i) (θ i) - c - c1Rent g θ e i)

/-- Single crossing gives `D_k(e) ≥ D_k(0) = 0` for `e ≥ 0`, and `D_k` nondecreasing. -/
theorem c1_D_mono {g : ℝ → ℝ → ℝ} {θ : ℕ → ℝ}
    (hsc : ∀ i j, i < j → StrictMonoOn (fun x => g x (θ i) - g x (θ j)) (Ici 0)) (k : ℕ) :
    MonotoneOn (c1D g θ k) (Ici 0) :=
  (hsc k (k + 1) (Nat.lt_succ_self k)).monotoneOn

/-- `D_k(e) ≥ 0` for `e ≥ 0`. -/
theorem c1_D_nonneg {g : ℝ → ℝ → ℝ} {θ : ℕ → ℝ} (hg0 : ∀ t, g 0 t = 0)
    (hsc : ∀ i j, i < j → StrictMonoOn (fun x => g x (θ i) - g x (θ j)) (Ici 0)) (k : ℕ)
    {x : ℝ} (hx : 0 ≤ x) : 0 ≤ c1D g θ k x := by
  have := c1_D_mono hsc k (mem_Ici.2 le_rfl) (mem_Ici.2 hx) hx
  simpa [c1D, hg0] using this

/-- The rents of a feasible contract: `x_i ≥ c + Σ_{k<i} D_k(e_k)` for `i < N`. -/
theorem c1_rent_le {g : ℝ → ℝ → ℝ} {θ w e : ℕ → ℝ} {c : ℝ} {N : ℕ}
    (hf : C1Feas g θ c N w e) : ∀ i < N, c + c1Rent g θ e i ≤ w i - g (e i) (θ i) := by
  intro i
  induction i with
  | zero => intro h; simpa [c1Rent] using hf.2.1 0 h
  | succ n ih =>
    intro h
    have h1 := ih (by omega)
    have h2 := hf.2.2 (n + 1) h n (by omega)
    unfold C1IC at h2
    unfold c1Rent at h1 ⊢
    rw [sum_range_succ]
    simp only [c1D] at h1 ⊢
    linarith

/-- Every feasible contract earns at most the virtual surplus of its efforts. -/
theorem c1_prof_le_VS {g : ℝ → ℝ → ℝ} {θ p w e : ℕ → ℝ} {prof : ℝ → ℝ} {c : ℝ} {N : ℕ}
    (hp : ∀ i < N, 0 < p i) (hf : C1Feas g θ c N w e) :
    c1Prof p prof N w e ≤ c1VS g θ p prof c N e := by
  unfold c1Prof c1VS
  refine sum_le_sum fun i hi => ?_
  have hi' := mem_range.1 hi
  have := mul_le_mul_of_nonneg_left (c1_rent_le hf i hi') (hp i hi').le
  nlinarith

/-- The extension `e (min i (N - 1))` of an effort profile on `0, …, N-1`. -/
def c1Ext (N : ℕ) (e : ℕ → ℝ) (i : ℕ) : ℝ := e (min i (N - 1))

/-- **Exercise 14.C.1**: for nonnegative nondecreasing efforts on `0, …, N-1`, the minimal-rent
wages (for the extended profile) form a feasible contract. -/
theorem c1_wage_feasible {g : ℝ → ℝ → ℝ} {θ e : ℕ → ℝ} {c : ℝ} {N : ℕ} (hN : 0 < N)
    (hg0 : ∀ t, g 0 t = 0)
    (hsc : ∀ i j, i < j → StrictMonoOn (fun x => g x (θ i) - g x (θ j)) (Ici 0))
    (he : ∀ i < N, 0 ≤ e i) (hmono : ∀ i j, i ≤ j → j < N → e i ≤ e j) :
    C1Feas g θ c N (c1Wage g θ c (c1Ext N e)) (c1Ext N e) := by
  have hE : ∀ k, 0 ≤ c1Ext N e k := fun k => he _ (by omega)
  have hM : Monotone (c1Ext N e) := fun i j hij => hmono _ _ (by omega) (by omega)
  have hIC := exercise_14_C_1_local (w := c1Wage g θ c (c1Ext N e)) (c1_D_mono hsc) hE hM
    (fun k => by
      unfold c1Wage c1Rent
      rw [sum_range_succ]
      unfold c1D
      ring)
  refine ⟨fun i _ => hE i, fun i _ => ?_, fun i _ j _ => hIC i j⟩
  unfold c1Wage c1Rent
  have : 0 ≤ ∑ k ∈ range i, c1D g θ k (c1Ext N e k) :=
    sum_nonneg fun k _ => c1_D_nonneg hg0 hsc k (hE k)
  linarith

/-- The minimal-rent contract earns exactly the virtual surplus. -/
theorem c1_prof_wage {g : ℝ → ℝ → ℝ} {θ p e : ℕ → ℝ} {prof : ℝ → ℝ} {c : ℝ} {N : ℕ} :
    c1Prof p prof N (c1Wage g θ c (c1Ext N e)) (c1Ext N e) =
      c1VS g θ p prof c N (c1Ext N e) := by
  unfold c1Prof c1VS c1Wage
  refine sum_congr rfl fun i _ => ?_
  ring

/-- The virtual surplus depends only on the efforts in states `0, …, N-1`. -/
theorem c1_VS_ext {g : ℝ → ℝ → ℝ} {θ p e : ℕ → ℝ} {prof : ℝ → ℝ} {c : ℝ} {N : ℕ} :
    c1VS g θ p prof c N (c1Ext N e) = c1VS g θ p prof c N e := by
  unfold c1VS c1Rent
  refine sum_congr rfl fun i hi => ?_
  have hi' := mem_range.1 hi
  have h1 : c1Ext N e i = e i := by unfold c1Ext; congr 1; omega
  have h2 : ∑ k ∈ range i, c1D g θ k (c1Ext N e k) = ∑ k ∈ range i, c1D g θ k (e k) :=
    sum_congr rfl fun k hk => by
      have := mem_range.1 hk
      unfold c1Ext; congr 2; omega
  rw [h1, h2]

/-- **Exercise 14.C.1** (MWG, p. 508), the optimal contract with `N` states. With single crossing,
`g(0, θ) = 0` and positive probabilities, every optimal contract `(w, e)` has: (i) nondecreasing
efforts; (ii) a binding reservation constraint in the lowest state; (iii) binding local downward
incentive constraints `w_{k+1} - g(e_{k+1}, θ_{k+1}) = w_k - g(e_k, θ_{k+1})`; (iv) efforts that
maximize the virtual surplus among nonnegative nondecreasing effort profiles. -/
theorem exercise_14_C_1_opt {g : ℝ → ℝ → ℝ} {θ p w e : ℕ → ℝ} {prof : ℝ → ℝ} {c : ℝ} {N : ℕ}
    (hN : 0 < N) (hp : ∀ i < N, 0 < p i) (hg0 : ∀ t, g 0 t = 0)
    (hsc : ∀ i j, i < j → StrictMonoOn (fun x => g x (θ i) - g x (θ j)) (Ici 0))
    (hf : C1Feas g θ c N w e)
    (hopt : ∀ w' e', C1Feas g θ c N w' e' → c1Prof p prof N w' e' ≤ c1Prof p prof N w e) :
    (∀ i j, i ≤ j → j < N → e i ≤ e j) ∧ w 0 - g (e 0) (θ 0) = c ∧
      (∀ k, k + 1 < N → w (k + 1) - g (e (k + 1)) (θ (k + 1)) = w k - g (e k) (θ (k + 1))) ∧
      ∀ e' : ℕ → ℝ, (∀ i < N, 0 ≤ e' i) → (∀ i j, i ≤ j → j < N → e' i ≤ e' j) →
        c1VS g θ p prof c N e' ≤ c1VS g θ p prof c N e := by
  have hmono : ∀ i j, i ≤ j → j < N → e i ≤ e j := by
    intro i j hij hj
    rcases hij.lt_or_eq with h | rfl
    · exact exercise_14_C_1_mono (hsc i j h) (hf.1 i (by omega)) (hf.1 j hj)
        (hf.2.2 i (by omega) j hj) (hf.2.2 j hj i (by omega))
    · exact le_rfl
  have hVSle : ∀ e' : ℕ → ℝ, (∀ i < N, 0 ≤ e' i) → (∀ i j, i ≤ j → j < N → e' i ≤ e' j) →
      c1VS g θ p prof c N e' ≤ c1Prof p prof N w e := by
    intro e' he' hm'
    have := hopt _ _ (c1_wage_feasible (c := c) hN hg0 hsc he' hm')
    rwa [c1_prof_wage, c1_VS_ext] at this
  have heq : c1Prof p prof N w e = c1VS g θ p prof c N e :=
    le_antisymm (c1_prof_le_VS hp hf) (hVSle e hf.1 hmono)
  -- every rent is minimal
  have hrent : ∀ i < N, w i - g (e i) (θ i) = c + c1Rent g θ e i := by
    have hterm : ∀ i ∈ range N, 0 ≤ p i * (w i - g (e i) (θ i) - (c + c1Rent g θ e i)) :=
      fun i hi => mul_nonneg (hp i (mem_range.1 hi)).le
        (by linarith [c1_rent_le hf i (mem_range.1 hi)])
    have hsum : ∑ i ∈ range N, p i * (w i - g (e i) (θ i) - (c + c1Rent g θ e i)) = 0 := by
      have : ∑ i ∈ range N, p i * (w i - g (e i) (θ i) - (c + c1Rent g θ e i)) =
          c1VS g θ p prof c N e - c1Prof p prof N w e := by
        unfold c1VS c1Prof
        rw [← sum_sub_distrib]
        exact sum_congr rfl fun i _ => by ring
      rw [this, heq, sub_self]
    intro i hi
    have := (sum_eq_zero_iff_of_nonneg hterm).1 hsum i (mem_range.2 hi)
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h (hp i hi).ne'
    · linarith
  refine ⟨hmono, by simpa [c1Rent] using hrent 0 hN, fun k hk => ?_, fun e' he' hm' => ?_⟩
  · have h1 := hrent (k + 1) hk
    have h2 := hrent k (by omega)
    unfold c1Rent at h1 h2
    rw [sum_range_succ] at h1
    simp only [c1D] at h1 h2
    linarith
  · rw [← heq]; exact hVSle e' he' hm'

/-- **Exercise 14.C.1**, the converse: if `e` is nonnegative, nondecreasing and maximizes the
virtual surplus among such profiles, then the minimal-rent contract is optimal. -/
theorem exercise_14_C_1_suff {g : ℝ → ℝ → ℝ} {θ p e : ℕ → ℝ} {prof : ℝ → ℝ} {c : ℝ} {N : ℕ}
    (hN : 0 < N) (hp : ∀ i < N, 0 < p i) (hg0 : ∀ t, g 0 t = 0)
    (hsc : ∀ i j, i < j → StrictMonoOn (fun x => g x (θ i) - g x (θ j)) (Ici 0))
    (he : ∀ i < N, 0 ≤ e i) (hm : ∀ i j, i ≤ j → j < N → e i ≤ e j)
    (hmax : ∀ e' : ℕ → ℝ, (∀ i < N, 0 ≤ e' i) → (∀ i j, i ≤ j → j < N → e' i ≤ e' j) →
        c1VS g θ p prof c N e' ≤ c1VS g θ p prof c N e) :
    C1Feas g θ c N (c1Wage g θ c (c1Ext N e)) (c1Ext N e) ∧
      ∀ w' e', C1Feas g θ c N w' e' →
        c1Prof p prof N w' e' ≤ c1Prof p prof N (c1Wage g θ c (c1Ext N e)) (c1Ext N e) := by
  refine ⟨c1_wage_feasible hN hg0 hsc he hm, fun w' e' hf' => ?_⟩
  rw [c1_prof_wage, c1_VS_ext]
  have hm' : ∀ i j, i ≤ j → j < N → e' i ≤ e' j := by
    intro i j hij hj
    rcases hij.lt_or_eq with h | rfl
    · exact exercise_14_C_1_mono (hsc i j h) (hf'.1 i (by omega)) (hf'.1 j hj)
        (hf'.2.2 i (by omega) j hj) (hf'.2.2 j hj i (by omega))
    · exact le_rfl
  exact (c1_prof_le_VS hp hf').trans (hmax e' hf'.1 hm')

/-- **Exercise 14.C.1**, distortions. Suppose each `e*_i ≥ 0` is the unique maximizer of
`π(e) - g(e, θ_i)` on `[0, ∞)` and `e*` is nondecreasing. In every optimal contract
`e_i ≤ e*_i` for every state (downward distortion) and `e_{N-1} = e*_{N-1}` (no distortion at the
top). -/
theorem exercise_14_C_1_distortion {g : ℝ → ℝ → ℝ} {θ p w e estar : ℕ → ℝ} {prof : ℝ → ℝ}
    {c : ℝ} {N : ℕ} (hN : 0 < N) (hp : ∀ i < N, 0 < p i) (hg0 : ∀ t, g 0 t = 0)
    (hsc : ∀ i j, i < j → StrictMonoOn (fun x => g x (θ i) - g x (θ j)) (Ici 0))
    (hs0 : ∀ i < N, 0 ≤ estar i)
    (hsmax : ∀ i < N, ∀ x, 0 ≤ x → x ≠ estar i →
      prof x - g x (θ i) < prof (estar i) - g (estar i) (θ i))
    (hsm : ∀ i j, i ≤ j → j < N → estar i ≤ estar j)
    (hf : C1Feas g θ c N w e)
    (hopt : ∀ w' e', C1Feas g θ c N w' e' → c1Prof p prof N w' e' ≤ c1Prof p prof N w e) :
    (∀ i < N, e i ≤ estar i) ∧ e (N - 1) = estar (N - 1) := by
  obtain ⟨hmono, -, -, hmax⟩ := exercise_14_C_1_opt hN hp hg0 hsc hf hopt
  have hD := c1_D_mono hsc
  -- downward distortion: compare with `min e e*`
  have hdown : ∀ i < N, e i ≤ estar i := by
    by_contra hc
    push Not at hc
    obtain ⟨i0, hi0, hlt⟩ := hc
    set e' : ℕ → ℝ := fun i => min (e i) (estar i)
    have he' : ∀ i < N, 0 ≤ e' i := fun i hi => le_min (hf.1 i hi) (hs0 i hi)
    have hm' : ∀ i j, i ≤ j → j < N → e' i ≤ e' j := fun i j hij hj =>
      min_le_min (hmono i j hij hj) (hsm i j hij hj)
    have hgt : c1VS g θ p prof c N e < c1VS g θ p prof c N e' := by
      unfold c1VS
      have hS : ∀ i ∈ range N, prof (e i) - g (e i) (θ i) ≤ prof (e' i) - g (e' i) (θ i) := by
        intro i hi
        have hi' := mem_range.1 hi
        by_cases h : e i ≤ estar i
        · simp only [e', min_eq_left h]; exact le_rfl
        · push Not at h
          simp only [e', min_eq_right h.le]
          exact (hsmax i hi' (e i) (hf.1 i hi') h.ne').le
      have hR : ∀ i ∈ range N, c1Rent g θ e' i ≤ c1Rent g θ e i := by
        intro i hi
        unfold c1Rent
        refine sum_le_sum fun k hk => ?_
        have hk' : k < N := by have := mem_range.1 hk; have := mem_range.1 hi; omega
        exact hD k (mem_Ici.2 (he' k hk')) (mem_Ici.2 (hf.1 k hk')) (min_le_left _ _)
      refine sum_lt_sum (fun i hi => ?_) ⟨i0, mem_range.2 hi0, ?_⟩
      · have := hp i (mem_range.1 hi)
        nlinarith [hS i hi, hR i hi]
      · have h1 := hp i0 hi0
        have hS0 : prof (e i0) - g (e i0) (θ i0) < prof (e' i0) - g (e' i0) (θ i0) := by
          simp only [e', min_eq_right hlt.le]
          exact hsmax i0 hi0 (e i0) (hf.1 i0 hi0) hlt.ne'
        nlinarith [hR i0 (mem_range.2 hi0)]
    linarith [hmax e' he' hm']
  refine ⟨hdown, ?_⟩
  -- no distortion at the top
  by_contra hne
  have htop : N - 1 < N := by omega
  have hlt : e (N - 1) < estar (N - 1) := lt_of_le_of_ne (hdown _ htop) hne
  set e' : ℕ → ℝ := Function.update e (N - 1) (estar (N - 1))
  have he'N : ∀ i < N - 1, e' i = e i := fun i hi => Function.update_of_ne (by omega) _ _
  have he' : ∀ i < N, 0 ≤ e' i := by
    intro i hi
    by_cases h : i = N - 1
    · subst h; simp only [e', Function.update_self]; exact hs0 _ htop
    · rw [he'N i (by omega)]; exact hf.1 i hi
  have hm' : ∀ i j, i ≤ j → j < N → e' i ≤ e' j := by
    intro i j hij hj
    by_cases hjN : j = N - 1
    · subst hjN
      by_cases hiN : i = N - 1
      · subst hiN; exact le_rfl
      · rw [he'N i (by omega)]
        simp only [e', Function.update_self]
        exact (hmono i (N - 1) hij htop).trans hlt.le
    · rw [he'N i (by omega), he'N j (by omega)]
      exact hmono i j hij hj
  have hgt : c1VS g θ p prof c N e < c1VS g θ p prof c N e' := by
    unfold c1VS
    have hR : ∀ i ∈ range N, c1Rent g θ e' i = c1Rent g θ e i := by
      intro i hi
      unfold c1Rent
      refine sum_congr rfl fun k hk => ?_
      have : k < N - 1 := by have := mem_range.1 hk; have := mem_range.1 hi; omega
      rw [he'N k this]
    refine sum_lt_sum (fun i hi => ?_) ⟨N - 1, mem_range.2 htop, ?_⟩
    · rw [hR i hi]
      by_cases h : i = N - 1
      · subst h
        have := hp _ htop
        have h2 := hsmax _ htop (e (N - 1)) (hf.1 _ htop) hlt.ne
        simp only [e', Function.update_self]
        nlinarith
      · rw [he'N i (by have := mem_range.1 hi; omega)]
    · rw [hR _ (mem_range.2 htop)]
      have := hp _ htop
      have h2 := hsmax _ htop (e (N - 1)) (hf.1 _ htop) hlt.ne
      simp only [e', Function.update_self]
      nlinarith
  linarith [hmax e' he' hm']

/-- **Exercise 14.C.1, an instance** (MWG, p. 508). Two states, `π(e) = e`, `g(e, θ) = e²/(2θ)`
with `θ_i = i + 1`, `p = (1/2, 1/2)`, `c = 0`. The efforts `(2/3, 2)` maximize the virtual
surplus, so the minimal-rent contract is optimal; its efforts are `e_0 = 2/3 < e*_0 = 1` and
`e_1 = e*_1 = 2`, as `exercise_14_C_1_opt` and `exercise_14_C_1_distortion` require. -/
theorem exercise_14_C_1_instance :
    let g : ℝ → ℝ → ℝ := fun x t => x ^ 2 / (2 * t)
    let θ : ℕ → ℝ := fun i => (i : ℝ) + 1
    let e : ℕ → ℝ := fun i => if i = 0 then 2 / 3 else 2
    C1Feas g θ 0 2 (c1Wage g θ 0 (c1Ext 2 e)) (c1Ext 2 e) ∧
      (∀ w' e', C1Feas g θ 0 2 w' e' →
        c1Prof (fun _ => 1 / 2) id 2 w' e' ≤
          c1Prof (fun _ => 1 / 2) id 2 (c1Wage g θ 0 (c1Ext 2 e)) (c1Ext 2 e)) ∧
      c1Ext 2 e 0 = 2 / 3 ∧ c1Ext 2 e 1 = 2 := by
  intro g θ e
  have hg0 : ∀ t, g 0 t = 0 := fun t => by simp [g]
  have hsc : ∀ i j, i < j → StrictMonoOn (fun x => g x (θ i) - g x (θ j)) (Ici 0) := by
    intro i j hij x hx y hy hxy
    have hij' : (i : ℝ) < j := by exact_mod_cast hij
    have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    simp only [g, θ, Set.mem_Ici] at hx hy ⊢
    have hk : 1 / (2 * ((j : ℝ) + 1)) < 1 / (2 * ((i : ℝ) + 1)) :=
      one_div_lt_one_div_of_lt (by positivity) (by linarith)
    have hxy2 : x ^ 2 < y ^ 2 := by nlinarith
    rw [div_eq_mul_one_div (x ^ 2), div_eq_mul_one_div (x ^ 2), div_eq_mul_one_div (y ^ 2),
      div_eq_mul_one_div (y ^ 2)]
    nlinarith
  have hsuff := exercise_14_C_1_suff (prof := id) (p := fun _ => 1 / 2) (c := 0) (N := 2)
    (e := e) (by norm_num) (fun _ _ => by norm_num) hg0 hsc
    (fun i _ => by simp only [e]; split_ifs <;> norm_num)
    (fun i j hij hj => by
      simp only [e]
      split_ifs <;> try norm_num
      omega)
    (fun e' _ _ => by
      simp only [c1VS, c1Rent, c1D, sum_range_succ, sum_range_zero, g, θ, e, id]
      norm_num
      nlinarith [sq_nonneg (e' 0 - 2 / 3), sq_nonneg (e' 1 - 2)])
  exact ⟨hsuff.1, hsuff.2, by simp [c1Ext, e], by simp [c1Ext, e]⟩

end MWG.PrincipalAgent
