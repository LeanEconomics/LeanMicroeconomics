/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGWelfareBargaining.SocialWelfare
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Algebra.BigOperators.Fin

/-!
# The veil of ignorance and Harsanyi's theorem

MWG, Exercises 22.C.2(b) and 22.C.3 (pp. 850-851).

* `exercise_22_C_2b`: a symmetric additive utility `∑ᵢ uᵢ(xᵢ)` on `X₀^I` has
  `uᵢ = u_{i₀} + cᵢ`: up to constants all identities are evaluated by the same function.
* `exercise_22_C_3a`: with two outcomes and a symmetric expected-utility social preference,
  all lotteries are socially indifferent.
* `exercise_22_C_3c_unique`, `exercise_22_C_3c_any`, `exercise_22_C_3c_not_unique`: the Paretian
  condition determines the social indifference map when individual preferences coincide; it is
  vacuous when they are opposed; in general it does not determine the map.
* `exercise_22_C_3d` (Harsanyi's theorem, `I = 2`, any `N`): if `U` is Paretian and some pair of
  lotteries is strictly preferred by both individuals, then `U = β₁U₁ + β₂U₂ + c` on the simplex
  with `β ≥ 0`, `β ≠ 0`.

**Correction (Exercise 22.C.3(d)).** As printed, "`U = β₁U₁ + ⋯ + β_IU_I` with `β ≥ 0`,
`β ≠ 0`" is false: (i) a constant is needed (`U = U₁ + 1` is Paretian when `U₁ = U₂`, but is no
nonnegative combination of `U₁, U₂` at the outcome where both are `0`;
`exercise_22_C_3d_constant`); (ii) some agreement among individuals is needed: when `U₂ = -U₁`
every `U` is Paretian (part (c) of the exercise itself) and `U(p) = p₂` is no combination
`β₁U₁ + β₂U₂ + c` (`exercise_22_C_3d_opposed`). The corrected statement is
`exercise_22_C_3d`. The proof is for `I = 2`, as the exercise allows; the general case needs
Farkas's lemma for finitely generated cones, which is not in Mathlib.
-/

namespace MWG.WelfareBargaining

/-! ### Exercise 22.C.2(b) -/

/-- **Exercise 22.C.2(b)** (MWG, p. 850). Let `X₁ = ⋯ = X_I = X₀` and suppose the preference
defined by `U(x) = ∑ᵢ uᵢ(xᵢ)` is symmetric (permuting the identities' outcomes gives an
indifferent outcome). Then `uᵢ(a) - u_{i₀}(a)` does not depend on `a`: all identities' utility
functions agree up to additive constants, so `U(x) = ∑ᵢ u_{i₀}(xᵢ) + constant`. -/
theorem exercise_22_C_2b {ι X₀ : Type*} [Fintype ι] (u : ι → X₀ → ℝ)
    (hsym : ∀ (σ : Equiv.Perm ι) (x : ι → X₀), ∑ i, u i (x (σ i)) = ∑ i, u i (x i))
    (i₀ i : ι) (a b : X₀) : u i a - u i₀ a = u i b - u i₀ b := by
  classical
  by_cases hi : i = i₀
  · subst hi; simp
  set x : ι → X₀ := fun k => if k = i then a else b with hx
  have h := hsym (Equiv.swap i i₀) x
  have hd : ∑ k, u k (x (Equiv.swap i i₀ k)) - ∑ k, u k (x k) =
      (u i (x i₀) - u i (x i)) + (u i₀ (x i) - u i₀ (x i₀)) := by
    rw [← Finset.sum_sub_distrib, Fintype.sum_eq_add i i₀ hi fun k ⟨h1, h2⟩ => by
      rw [Equiv.swap_apply_of_ne_of_ne h1 h2, sub_self]]
    simp
  have hxi : x i = a := by simp [hx]
  have hxi₀ : x i₀ = b := by simp [hx, Ne.symm hi]
  rw [hxi, hxi₀, h, sub_self] at hd
  linarith

/-- **Exercise 22.C.2(b)**, instance (MWG, p. 850): identical utility functions give a symmetric
preference. -/
theorem exercise_22_C_2b_instance {ι X₀ : Type*} [Fintype ι] (v : X₀ → ℝ) :
    ∀ (σ : Equiv.Perm ι) (x : ι → X₀), ∑ i, (fun _ : ι => v) i (x (σ i)) =
      ∑ i, (fun _ : ι => v) i (x i) :=
  fun σ x => Equiv.sum_comp σ (fun i => v (x i))

/-! ### Exercise 22.C.3 -/

/-- Expected utility `∑ₙ aₙpₙ` of the lottery `p` for the outcome utilities `a`. -/
def eu {N : ℕ} (a p : Fin N → ℝ) : ℝ := ∑ n, a n * p n

/-- The simplex of lotteries over `N` outcomes. -/
def lotteries (N : ℕ) : Set (Fin N → ℝ) := {p | (∀ n, 0 ≤ p n) ∧ ∑ n, p n = 1}

/-- **Exercise 22.C.3** (MWG, p. 851). `U` is Paretian with respect to `U₁, …, U_I`:
`Uᵢ(p) > Uᵢ(p')` for every `i` implies `U(p) > U(p')`. -/
def HarsanyiParetian {N : ℕ} {ι : Type*} (u : Fin N → ℝ) (us : ι → Fin N → ℝ) : Prop :=
  ∀ p ∈ lotteries N, ∀ p' ∈ lotteries N, (∀ i, eu (us i) p' < eu (us i) p) → eu u p' < eu u p

theorem eu_add {N : ℕ} (a p q : Fin N → ℝ) : eu a (p + q) = eu a p + eu a q := by
  simp [eu, mul_add, Finset.sum_add_distrib]

theorem eu_smul {N : ℕ} (a p : Fin N → ℝ) (c : ℝ) : eu a (c • p) = c * eu a p := by
  simp only [eu, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun n _ => by ring

theorem eu_sub {N : ℕ} (a p q : Fin N → ℝ) : eu a (p - q) = eu a p - eu a q := by
  simp [eu, mul_sub, Finset.sum_sub_distrib]

/-- **Exercise 22.C.3(a)** (MWG, pp. 850-851). Two outcomes (the object goes to individual 1 or
to individual 2); if society is indifferent between the two sure outcomes, `u₁ = u₂`, then all
lotteries are socially indifferent. -/
theorem exercise_22_C_3a (u : Fin 2 → ℝ) (hsym : u 0 = u 1) (p p' : Fin 2 → ℝ)
    (hp : p ∈ lotteries 2) (hp' : p' ∈ lotteries 2) : eu u p = eu u p' := by
  obtain ⟨-, hs⟩ := hp
  obtain ⟨-, hs'⟩ := hp'
  simp only [eu, Fin.sum_univ_two] at hs hs' ⊢
  rw [hsym, ← mul_add, ← mul_add, hs, hs']

/-- A convex combination of lotteries is a lottery. -/
theorem lotteries_comb {N : ℕ} {p q : Fin N → ℝ} (hp : p ∈ lotteries N) (hq : q ∈ lotteries N)
    {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) : (1 - ε) • p + ε • q ∈ lotteries N := by
  refine ⟨fun n => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [hp.1 n, hq.1 n]
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hp.2, hq.2]
    ring

/-- **Exercise 22.C.3(c)** (MWG, p. 851), the determined case. If both individuals have the same
nonconstant expected utility `V`, a Paretian expected-utility social preference has exactly the
indifference map of `V`: `U(p) ≤ U(p') ↔ V(p) ≤ V(p')` on the simplex. -/
theorem exercise_22_C_3c_unique {N : ℕ} {u v : Fin N → ℝ}
    (hP : HarsanyiParetian u fun _ : Fin 2 => v)
    (hV : ∃ q ∈ lotteries N, ∃ q' ∈ lotteries N, eu v q ≠ eu v q') :
    ∀ p ∈ lotteries N, ∀ p' ∈ lotteries N, (eu u p ≤ eu u p' ↔ eu v p ≤ eu v p') := by
  have strict : ∀ p ∈ lotteries N, ∀ p' ∈ lotteries N, eu v p' < eu v p → eu u p' < eu u p :=
    fun p hp p' hp' h => hP p hp p' hp' fun _ => h
  -- `V(p) = V(p')` forces `U(p) = U(p')`
  have hind : ∀ p ∈ lotteries N, ∀ p' ∈ lotteries N, eu v p = eu v p' → eu u p ≤ eu u p' := by
    intro p hp p' hp' heq
    by_contra hlt
    have hlt : eu u p' < eu u p := not_le.1 hlt
    obtain ⟨q, hq, q', hq', hne⟩ := hV
    -- some lottery `r` has `V(r) ≠ V(p)`
    obtain ⟨r, hr, hrne⟩ : ∃ r ∈ lotteries N, eu v r ≠ eu v p := by
      by_cases h : eu v q = eu v p
      · exact ⟨q', hq', fun h' => hne (h.trans h'.symm)⟩
      · exact ⟨q, hq, h⟩
    set D := eu u p - eu u p' with hD
    have hDpos : 0 < D := by linarith
    set ε := D / (2 * (|eu u r - eu u p| + |eu u r - eu u p'| + D)) with hε
    have hden : 0 < 2 * (|eu u r - eu u p| + |eu u r - eu u p'| + D) := by positivity
    have hε0 : 0 < ε := div_pos hDpos hden
    have hε1 : ε ≤ 1 := by
      rw [hε, div_le_one hden]
      nlinarith [abs_nonneg (eu u r - eu u p), abs_nonneg (eu u r - eu u p')]
    have hεD : ε * |eu u r - eu u p| < D ∧ ε * |eu u r - eu u p'| < D := by
      have key : ε * (|eu u r - eu u p| + |eu u r - eu u p'| + D) = D / 2 := by
        rw [hε]; field_simp
      constructor <;> nlinarith [abs_nonneg (eu u r - eu u p), abs_nonneg (eu u r - eu u p')]
    rcases lt_or_gt_of_ne hrne with hlow | hhigh
    · -- move `p` toward `r`: `V` falls below `V(p')`, so `U` must fall below `U(p')`
      have hm := lotteries_comb hp hr hε0.le hε1
      have hV' : eu v ((1 - ε) • p + ε • r) < eu v p' := by
        rw [eu_add, eu_smul, eu_smul, ← heq]; nlinarith
      have hU := strict p' hp' _ hm hV'
      rw [eu_add, eu_smul, eu_smul] at hU
      have := neg_abs_le (eu u r - eu u p)
      nlinarith [hεD.1]
    · -- move `p'` toward `r`: `V` rises above `V(p)`, so `U` must rise above `U(p)`
      have hm := lotteries_comb hp' hr hε0.le hε1
      have hV' : eu v p < eu v ((1 - ε) • p' + ε • r) := by
        rw [eu_add, eu_smul, eu_smul, ← heq]; nlinarith
      have hU := strict _ hm p hp hV'
      rw [eu_add, eu_smul, eu_smul] at hU
      have := le_abs_self (eu u r - eu u p')
      nlinarith [hεD.2]
  intro p hp p' hp'
  constructor
  · intro h
    by_contra hlt
    exact absurd h (not_le.2 (strict p hp p' hp' (not_le.1 hlt)))
  · intro h
    rcases h.lt_or_eq with hlt | heq
    · exact (strict p' hp' p hp hlt).le
    · exact hind p hp p' hp' heq

/-- **Exercise 22.C.3(c)**, instance of the determined case (MWG, p. 851): `N = 3`, both
individuals and society evaluate lotteries by the probability of the first outcome. -/
theorem exercise_22_C_3c_unique_instance :
    HarsanyiParetian (![1, 0, 0] : Fin 3 → ℝ) (fun _ : Fin 2 => (![1, 0, 0] : Fin 3 → ℝ)) ∧
      ∃ q ∈ lotteries 3, ∃ q' ∈ lotteries 3,
        eu (![1, 0, 0] : Fin 3 → ℝ) q ≠ eu (![1, 0, 0] : Fin 3 → ℝ) q' := by
  refine ⟨fun p _ p' _ h => h 0, ![1, 0, 0], ⟨fun n => by fin_cases n <;> simp, by
    simp [Fin.sum_univ_three]⟩, ![0, 1, 0], ⟨fun n => by fin_cases n <;> simp, by
    simp [Fin.sum_univ_three]⟩, by simp [eu, Fin.sum_univ_three]⟩

/-- **Exercise 22.C.3(c)** (MWG, p. 851). When the two individuals' preferences are opposed
(`U₂ = -U₁`) no pair of lotteries is strictly preferred by both, so every social utility
function is Paretian. -/
theorem exercise_22_C_3c_any {N : ℕ} (a u : Fin N → ℝ) :
    HarsanyiParetian u ![a, -a] := by
  intro p _ p' _ h
  have h0 := h 0
  have h1 := h 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, eu,
    Pi.neg_apply, neg_mul, Finset.sum_neg_distrib] at h0 h1
  linarith

/-- **Exercise 22.C.3(c)** (MWG, p. 851). In general the Paretian condition does not determine
the social indifference map: with `U₁(p) = p₁`, `U₂(p) = p₂` (`N = 3`), both `U₁ + U₂` and
`U₁ + 2U₂` are Paretian, but the first is indifferent between the first two sure outcomes and
the second is not. -/
theorem exercise_22_C_3c_not_unique :
    HarsanyiParetian (![1, 1, 0] : Fin 3 → ℝ) ![![1, 0, 0], ![0, 1, 0]] ∧
      HarsanyiParetian (![1, 2, 0] : Fin 3 → ℝ) ![![1, 0, 0], ![0, 1, 0]] ∧
      eu (![1, 1, 0] : Fin 3 → ℝ) ![1, 0, 0] = eu ![1, 1, 0] ![0, 1, 0] ∧
      eu (![1, 2, 0] : Fin 3 → ℝ) ![1, 0, 0] ≠ eu ![1, 2, 0] ![0, 1, 0] := by
  refine ⟨fun p _ p' _ h => ?_, fun p _ p' _ h => ?_, by simp [eu, Fin.sum_univ_three],
    by simp [eu, Fin.sum_univ_three]⟩
  · have h0 := h 0; have h1 := h 1
    simp [eu, Fin.sum_univ_three] at h0 h1 ⊢; linarith
  · have h0 := h 0; have h1 := h 1
    simp [eu, Fin.sum_univ_three] at h0 h1 ⊢; linarith

/-- Expected utility as a linear functional on `ℝ^N`. -/
def euLin {N : ℕ} (a : Fin N → ℝ) : (Fin N → ℝ) →ₗ[ℝ] ℝ where
  toFun p := eu a p
  map_add' p q := eu_add a p q
  map_smul' c p := eu_smul a p c

/-- Every direction `d` with `∑ dₙ = 0` is, up to a positive factor, the difference of two
lotteries: `q + εd` and the uniform lottery `q`. -/
theorem lottery_direction {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ) (hd : ∑ n, d n = 0) :
    ∃ q ∈ lotteries N, ∃ ε : ℝ, 0 < ε ∧ q + ε • d ∈ lotteries N := by
  set q : Fin N → ℝ := fun _ => 1 / N
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set S := ∑ n, |d n| with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun n _ => abs_nonneg _
  refine ⟨q, ⟨fun n => by positivity, by simp [q]; field_simp⟩, 1 / (N * (S + 1)),
    by positivity, fun n => ?_, ?_⟩
  · have hdn : |d n| ≤ S := Finset.single_le_sum (f := fun n => |d n|)
      (fun n _ => abs_nonneg _) (Finset.mem_univ n)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, q]
    have h1 : -(1 / (N * (S + 1)) * |d n|) ≤ 1 / (N * (S + 1)) * d n := by
      have := neg_abs_le (d n)
      have hp : 0 < 1 / ((N : ℝ) * (S + 1)) := by positivity
      nlinarith
    have h2 : 1 / (N * (S + 1)) * |d n| ≤ 1 / N := by
      rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) hNr]
      nlinarith
    linarith
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, q,
      ← Finset.mul_sum, hd, mul_zero, add_zero]
    simp; field_simp

/-- The Paretian condition in terms of directions: if `∑ dₙ = 0` and `aᵢ·d > 0` for both
individuals then `u·d > 0`. -/
theorem harsanyi_direction {N : ℕ} {u : Fin N → ℝ} {us : Fin 2 → Fin N → ℝ}
    (hP : HarsanyiParetian u us) (hN : 0 < N) {d : Fin N → ℝ} (hd : ∑ n, d n = 0)
    (hpos : ∀ i, 0 < eu (us i) d) : 0 < eu u d := by
  obtain ⟨q, hq, ε, hε, hqd⟩ := lottery_direction hN d hd
  have h := hP _ hqd q hq fun i => by
    rw [eu_add, eu_smul]; nlinarith [hpos i]
  rw [eu_add, eu_smul] at h
  nlinarith

/-- The kernel step of Harsanyi's theorem: from the agreement direction `d₀`, `u` vanishes on
the directions where both individuals and `∑ₙ` vanish, so `u = c₀a₀ + c₁a₁ + c₂𝟙`. -/
theorem harsanyi_span {N : ℕ} {u : Fin N → ℝ} {us : Fin 2 → Fin N → ℝ}
    (hP : HarsanyiParetian u us) (hN : 0 < N) {d₀ : Fin N → ℝ} (hd₀ : ∑ n, d₀ n = 0)
    (hpos : ∀ i, 0 < eu (us i) d₀) :
    ∃ c : Fin 3 → ℝ, ∀ p, eu u p = c 0 * eu (us 0) p + c 1 * eu (us 1) p + c 2 * ∑ n, p n := by
  have hker : ⨅ k, LinearMap.ker (![euLin (us 0), euLin (us 1), euLin fun _ => 1] k) ≤
      LinearMap.ker (euLin u) := by
    intro d hd
    simp only [Submodule.mem_iInf, LinearMap.mem_ker] at hd
    have h0 : eu (us 0) d = 0 := hd 0
    have h1 : eu (us 1) d = 0 := hd 1
    have h2 : ∑ n, d n = 0 := by simpa [euLin, eu] using hd 2
    rw [LinearMap.mem_ker]
    change eu u d = 0
    by_contra hne
    -- along `d₀ + t d` both individuals gain, so `u` must too, for every `t`
    set t := -(eu u d₀ + 1) / eu u d with ht
    have hdir : ∑ n, (d₀ + t • d) n = 0 := by
      simp [Finset.sum_add_distrib, ← Finset.mul_sum, hd₀, h2]
    have := harsanyi_direction hP hN hdir fun i => by
      rw [eu_add, eu_smul]
      fin_cases i
      · simp only [Fin.zero_eta, Fin.isValue, h0, mul_zero, add_zero]; exact hpos 0
      · simp only [Fin.mk_one, Fin.isValue, h1, mul_zero, add_zero]; exact hpos 1
    rw [eu_add, eu_smul, ht, div_mul_cancel₀ _ hne] at this
    linarith
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 (mem_span_of_iInf_ker_le_ker hker)
  refine ⟨c, fun p => ?_⟩
  rw [Fin.sum_univ_three] at hc
  have := LinearMap.congr_fun hc p
  simp [euLin, eu] at this
  simp only [eu]
  linarith

/-- The sign step of Harsanyi's theorem: if `u = c₀a₀ + c₁a₁ + c₂𝟙` with `c₀ < 0`, then on the
directions `∑ dₙ = 0` the functional `a₀` is a multiple of `a₁`, and `u = β a₁ + c` on the
simplex with `β > 0`. -/
theorem harsanyi_neg {N : ℕ} {u a₀ a₁ : Fin N → ℝ} {c₀ c₁ c₂ : ℝ}
    (hP : HarsanyiParetian u ![a₀, a₁]) (hN : 0 < N) {d₀ : Fin N → ℝ} (hd₀ : ∑ n, d₀ n = 0)
    (h₀ : 0 < eu a₀ d₀) (h₁ : 0 < eu a₁ d₀)
    (hc : ∀ p, eu u p = c₀ * eu a₀ p + c₁ * eu a₁ p + c₂ * ∑ n, p n) (hc₀ : c₀ < 0) :
    ∃ β c : ℝ, 0 < β ∧ ∀ p ∈ lotteries N, eu u p = β * eu a₁ p + c := by
  -- `a₀` vanishes on the directions where `a₁` and `∑ₙ` vanish
  have hker : ⨅ k, LinearMap.ker (![euLin a₁, euLin fun _ => 1] k) ≤ LinearMap.ker (euLin a₀) := by
    intro e he
    simp only [Submodule.mem_iInf, LinearMap.mem_ker] at he
    have he1 : eu a₁ e = 0 := he 0
    have he2 : ∑ n, e n = 0 := by simpa [euLin, eu] using he 1
    rw [LinearMap.mem_ker]
    change eu a₀ e = 0
    by_contra hne
    -- push along `±e`, where `a₀` grows without bound and `a₁` is constant
    set s : ℝ := if 0 < eu a₀ e then 1 else -1 with hs
    have hse : 0 < s * eu a₀ e := by
      simp only [hs]; split_ifs with h
      · linarith
      · have : eu a₀ e < 0 := lt_of_le_of_ne (not_lt.1 h) hne; linarith
    set M := (|c₀ * eu a₀ d₀ + c₁ * eu a₁ d₀| + 1) / (-c₀ * (s * eu a₀ e)) with hM
    have hMpos : 0 < M := div_pos (by positivity) (mul_pos (by linarith) hse)
    have hdir : ∑ n, (d₀ + (M * s) • e) n = 0 := by
      simp [Finset.sum_add_distrib, ← Finset.mul_sum, hd₀, he2]
    have hu := harsanyi_direction hP hN hdir fun i => by
      rw [eu_add, eu_smul]
      fin_cases i
      · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
        nlinarith [mul_pos hMpos hse]
      · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one, he1,
          mul_zero, add_zero]
        exact h₁
    rw [hc, eu_add, eu_add, eu_smul, eu_smul, he1] at hu
    simp only [Finset.sum_add_distrib, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      ← Finset.mul_sum, hd₀, he2, mul_zero, add_zero] at hu
    have hden : -c₀ * (s * eu a₀ e) ≠ 0 := (mul_pos (by linarith) hse).ne'
    have key : -c₀ * (s * eu a₀ e) * M = |c₀ * eu a₀ d₀ + c₁ * eu a₁ d₀| + 1 := by
      rw [hM, mul_div_cancel₀ _ hden]
    have := le_abs_self (c₀ * eu a₀ d₀ + c₁ * eu a₁ d₀)
    nlinarith
  obtain ⟨κ, hκ⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 (mem_span_of_iInf_ker_le_ker hker)
  have hκp : ∀ p, eu a₀ p = κ 0 * eu a₁ p + κ 1 * ∑ n, p n := by
    intro p
    rw [Fin.sum_univ_two] at hκ
    have := LinearMap.congr_fun hκ p
    simp [euLin, eu] at this
    simp only [eu]
    linarith
  refine ⟨c₀ * κ 0 + c₁, c₀ * κ 1 + c₂, ?_, fun p hp => ?_⟩
  · have e₀ := hκp d₀
    have e := hc d₀
    rw [hd₀, mul_zero, add_zero] at e₀
    rw [hd₀, mul_zero, add_zero, e₀] at e
    have hu := harsanyi_direction hP hN hd₀ fun i => by fin_cases i <;> simp [h₀, h₁]
    nlinarith
  · rw [hc, hκp, hp.2]; ring

/-- **Exercise 22.C.3(d)**, corrected (Harsanyi's theorem, MWG, p. 851; `I = 2`, any number `N`
of outcomes). Let `U, U₁, U₂` be expected utility functions on the simplex of lotteries, `U`
Paretian, and suppose some pair of lotteries is strictly preferred by both individuals. Then
`U = β₁U₁ + β₂U₂ + c` on the simplex with `β₁, β₂ ≥ 0`, not both zero. -/
theorem exercise_22_C_3d {N : ℕ} {u a₀ a₁ : Fin N → ℝ} (hP : HarsanyiParetian u ![a₀, a₁])
    (hagree : ∃ p ∈ lotteries N, ∃ p' ∈ lotteries N, eu a₀ p' < eu a₀ p ∧ eu a₁ p' < eu a₁ p) :
    ∃ β₀ β₁ c : ℝ, 0 ≤ β₀ ∧ 0 ≤ β₁ ∧ (β₀ ≠ 0 ∨ β₁ ≠ 0) ∧
      ∀ p ∈ lotteries N, eu u p = β₀ * eu a₀ p + β₁ * eu a₁ p + c := by
  obtain ⟨p, hp, p', hp', hlt₀, hlt₁⟩ := hagree
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; simp [lotteries] at hp
    · exact h
  set d₀ := p - p'
  have hd₀ : ∑ n, d₀ n = 0 := by simp [d₀, Finset.sum_sub_distrib, hp.2, hp'.2]
  have h₀ : 0 < eu a₀ d₀ := by rw [eu_sub]; linarith
  have h₁ : 0 < eu a₁ d₀ := by rw [eu_sub]; linarith
  obtain ⟨c, hc⟩ := harsanyi_span hP hN hd₀ fun i => by fin_cases i <;> simp [h₀, h₁]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at hc
  have hu := harsanyi_direction hP hN hd₀ fun i => by fin_cases i <;> simp [h₀, h₁]
  have hud : eu u d₀ = c 0 * eu a₀ d₀ + c 1 * eu a₁ d₀ := by rw [hc, hd₀]; ring
  by_cases hc0 : c 0 < 0
  · obtain ⟨β, k, hβ, h⟩ := harsanyi_neg hP hN hd₀ h₀ h₁ hc hc0
    exact ⟨0, β, k, le_rfl, hβ.le, Or.inr hβ.ne', fun q hq => by rw [h q hq]; ring⟩
  by_cases hc1 : c 1 < 0
  · -- swap the roles of the two individuals
    have hP' : HarsanyiParetian u ![a₁, a₀] := fun q hq q' hq' h =>
      hP q hq q' hq' fun i => by fin_cases i; exacts [h 1, h 0]
    obtain ⟨β, k, hβ, h⟩ := harsanyi_neg hP' hN hd₀ h₁ h₀ (c₀ := c 1) (c₁ := c 0) (c₂ := c 2)
      (fun q => by rw [hc]; ring) hc1
    exact ⟨β, 0, k, hβ.le, le_rfl, Or.inl hβ.ne', fun q hq => by rw [h q hq]; ring⟩
  have hc0 : 0 ≤ c 0 := not_lt.1 hc0
  have hc1 : 0 ≤ c 1 := not_lt.1 hc1
  refine ⟨c 0, c 1, c 2, hc0, hc1, ?_, fun q hq => by rw [hc, hq.2, mul_one]⟩
  by_contra h
  rw [not_or, not_not, not_not] at h
  rw [h.1, h.2] at hud
  linarith

/-- **Exercise 22.C.3(d)**, instance (MWG, p. 851): `U = U₁ + U₂` with `U₁(p) = p₁`,
`U₂(p) = p₂` is Paretian, and both prefer `(1/2, 1/2, 0)` to `(0, 0, 1)`. -/
theorem exercise_22_C_3d_instance :
    HarsanyiParetian (![1, 1, 0] : Fin 3 → ℝ) ![![1, 0, 0], ![0, 1, 0]] ∧
      ∃ p ∈ lotteries 3, ∃ p' ∈ lotteries 3,
        eu ![1, 0, 0] p' < eu ![1, 0, 0] p ∧ eu ![0, 1, 0] p' < eu ![0, 1, 0] p := by
  refine ⟨exercise_22_C_3c_not_unique.1, ![1 / 2, 1 / 2, 0], ⟨fun n => by fin_cases n <;> norm_num,
    by simp [Fin.sum_univ_three]; norm_num⟩, ![0, 0, 1], ⟨fun n => by fin_cases n <;> norm_num,
    by simp [Fin.sum_univ_three]⟩, by simp [eu, Fin.sum_univ_three],
    by simp [eu, Fin.sum_univ_three]⟩

/-- **Correction, Exercise 22.C.3(d)** (MWG, p. 851): a constant is needed. With
`U₁ = U₂ = p₁`, `U(p) = p₁ + 1` is Paretian but `U ≠ β₀U₁ + β₁U₂` at the second sure
outcome. -/
theorem exercise_22_C_3d_constant :
    HarsanyiParetian (![2, 1, 1] : Fin 3 → ℝ) ![![1, 0, 0], ![1, 0, 0]] ∧
      ¬∃ β₀ β₁ : ℝ, ∀ p ∈ lotteries 3, eu (![2, 1, 1] : Fin 3 → ℝ) p =
        β₀ * eu ![1, 0, 0] p + β₁ * eu ![1, 0, 0] p := by
  refine ⟨fun p hp p' hp' h => ?_, fun ⟨β₀, β₁, h⟩ => ?_⟩
  · have h0 := h 0
    simp only [Matrix.cons_val_zero, eu, Fin.sum_univ_three] at h0 ⊢
    have := hp.2; have := hp'.2
    simp only [Fin.sum_univ_three] at *
    simp at h0 ⊢
    linarith
  · have := h ![0, 1, 0] ⟨fun n => by fin_cases n <;> simp, by simp [Fin.sum_univ_three]⟩
    simp [eu, Fin.sum_univ_three] at this

/-- **Correction, Exercise 22.C.3(d)** (MWG, p. 851): agreement is needed. With opposed
individuals `U₁(p) = p₁`, `U₂(p) = -p₁`, the Paretian `U(p) = p₂` (`exercise_22_C_3c_any`) is
no combination `β₀U₁ + β₁U₂ + c`. -/
theorem exercise_22_C_3d_opposed :
    HarsanyiParetian (![0, 1, 0] : Fin 3 → ℝ) ![![1, 0, 0], -![1, 0, 0]] ∧
      ¬∃ β₀ β₁ c : ℝ, ∀ p ∈ lotteries 3, eu (![0, 1, 0] : Fin 3 → ℝ) p =
        β₀ * eu ![1, 0, 0] p + β₁ * eu (-![1, 0, 0]) p + c := by
  refine ⟨exercise_22_C_3c_any _ _, fun ⟨β₀, β₁, c, h⟩ => ?_⟩
  have h2 := h ![0, 1, 0] ⟨fun n => by fin_cases n <;> simp, by simp [Fin.sum_univ_three]⟩
  have h3 := h ![0, 0, 1] ⟨fun n => by fin_cases n <;> simp, by simp [Fin.sum_univ_three]⟩
  simp [eu, Fin.sum_univ_three] at h2 h3
  linarith

end MWG.WelfareBargaining
