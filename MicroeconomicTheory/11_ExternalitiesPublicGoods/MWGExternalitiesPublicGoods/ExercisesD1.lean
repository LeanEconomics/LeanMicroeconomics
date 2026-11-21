/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGExternalitiesPublicGoods.Concavity
import MWGSimultaneousMoveGames.Dominance
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Exercises 11.D.1-11.D.2 (MWG, p. 379-380)

* **Exercise 11.D.1** (Weitzman's students). `n ≥ 2` students choose hours `hᵢ > 0`; payoffs
  `φ(hᵢ/h̄) - hᵢ²/2` with `h̄` the class average, `φ` concave with `φ' > 0`. The game is a Chapter 7
  normal form and equilibrium is Chapter 8's `IsNashEquilibrium`. A symmetric profile `(h, …, h)`
  is a Nash equilibrium iff `h² = φ'(1)(n - 1)/n` (`exercise_11_D_1`); every symmetric profile,
  in particular the equilibrium, is Pareto dominated by the symmetric profile with half the hours
  (`exercise_11_D_1_pareto`): there is no Pareto optimal symmetric outcome with `h > 0`, the
  symmetric payoff `φ(1) - h²/2` increasing as `h ↓ 0`. The assumption `φ'(0+) = ∞` is not needed.
* **Exercise 11.D.2** (agents who both generate and experience the externality). Utilities
  `φᵢ(hᵢ, ∑ₖ hₖ) + wᵢ`, `φᵢ` concave and differentiable with partials `aᵢ = ∂₁φᵢ`, `bᵢ = ∂₂φᵢ`.
  Optimal levels: `aⱼ + ∑ᵢ bᵢ ≤ 0`, equality if `hⱼ > 0` (`exercise_11_D_2_opt`); equilibrium:
  `aᵢ + bᵢ ≤ tᵢ` (`exercise_11_D_2_eq`); the per-unit tax `tᵢ = -∑_{k ≠ i} bₖ` makes the optimum
  an equilibrium (`exercise_11_D_2_tax`).
-/

namespace MWG.ExternalitiesPublicGoods

open MWG.CompetitiveMarkets MWG.NoncooperativeGames MWG.SimultaneousMoveGames Function

/-! ## Exercise 11.D.1 -/

/-- **Exercise 11.D.1** (MWG, p. 379). The students' game: student `i` chooses hours `hᵢ > 0`
and receives `φ(hᵢ/h̄) - hᵢ²/2`, `h̄ = (1/n) ∑ⱼ hⱼ`. -/
noncomputable def studentGame (n : ℕ) (φ : ℝ → ℝ) :
    NormalForm (Fin n) (fun _ => {h : ℝ // 0 < h}) where
  payoff i s := φ ((s i : ℝ) / ((∑ j, (s j : ℝ)) / n)) - (s i : ℝ) ^ 2 / 2

/-- The payoff of a student who deviates to `x` when all others work `h`. -/
theorem student_dev {n : ℕ} (hn : 1 ≤ n) (φ : ℝ → ℝ) {h x : ℝ} (hh : 0 < h) (hx : 0 < x)
    (i : Fin n) :
    (studentGame n φ).payoff i (update (fun _ => ⟨h, hh⟩) i ⟨x, hx⟩) =
      φ (n * x / (x + (n - 1) * h)) - x ^ 2 / 2 := by
  have hs : ∑ j, ((update (fun _ : Fin n => (⟨h, hh⟩ : {h : ℝ // 0 < h})) i ⟨x, hx⟩ j : ℝ)) =
      x + (n - 1) * h := by
    have : ∀ j, ((update (fun _ : Fin n => (⟨h, hh⟩ : {h : ℝ // 0 < h})) i ⟨x, hx⟩ j : ℝ)) =
        update (fun _ : Fin n => h) i x j := fun j => by
      rcases eq_or_ne j i with hj | hj
      · subst hj; simp
      · simp [update_of_ne hj]
    simp_rw [this]
    rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
    simp only [Finset.sum_const, Finset.card_sdiff, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    rw [Finset.inter_univ, Finset.card_singleton, Nat.cast_sub hn, Nat.cast_one]
  simp only [studentGame, update_self, hs]
  congr 2
  have hpos : 0 < x + (n - 1) * h := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  field_simp

/-- **Exercise 11.D.1** (MWG, pp. 379-380). With `n ≥ 2` students, `φ` differentiable with
decreasing `φ'` on `[0, ∞)` and `φ'(1) > 0`, the symmetric profile `(h, …, h)`, `h > 0`, is a Nash
equilibrium iff `h² = φ'(1)(n - 1)/n`. -/
theorem exercise_11_D_1 {n : ℕ} (hn : 2 ≤ n) {φ dφ : ℝ → ℝ} (hφ : ∀ x, HasDerivAt φ (dφ x) x)
    (hanti : AntitoneOn dφ (Set.Ici 0)) (hpos : 0 < dφ 1) {h : ℝ} (hh : 0 < h) :
    IsNashEquilibrium (studentGame n φ) (fun _ => ⟨h, hh⟩) ↔ h ^ 2 = dφ 1 * (n - 1) / n := by
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := (by linarith : (0 : ℝ) < n).ne'
  set f : ℝ → ℝ := fun x => φ (n * x / (x + (n - 1) * h)) - x ^ 2 / 2 with hf
  have hr1 : (n : ℝ) * h / (h + (n - 1) * h) = 1 := by
    rw [div_eq_one_iff_eq (by nlinarith)]; ring
  have hfh : f h = φ 1 - h ^ 2 / 2 := by
    simp only [f, hr1]
  have hself : ∀ i : Fin n, (studentGame n φ).payoff i (fun _ => ⟨h, hh⟩) = f h := fun i => by
    have := student_dev hn1 φ hh hh i
    rw [update_eq_self_iff.2 rfl] at this
    rw [this]
  constructor
  · intro hne
    have i : Fin n := ⟨0, by omega⟩
    have hle : ∀ x, 0 < x → f x ≤ f h := fun x hx => by
      have := hne i ⟨x, hx⟩
      rw [student_dev hn1 φ hh hx, hself] at this
      exact this
    -- the derivative of `f` at `h`
    have hden : HasDerivAt (fun x => x + (n - 1) * h) 1 h := by
      simpa using (hasDerivAt_id h).add_const ((n - 1) * h)
    have hnum : HasDerivAt (fun x => (n : ℝ) * x) n h := by
      simpa using (hasDerivAt_id h).const_mul (n : ℝ)
    have hpos' : h + (n - 1) * h ≠ 0 := by nlinarith
    have hr := hnum.div hden hpos'
    have hφ1 : HasDerivAt φ (dφ 1) ((n : ℝ) * h / (h + (n - 1) * h)) := by rw [hr1]; exact hφ 1
    have hcomp := hφ1.comp h hr
    have hfd := hcomp.sub ((hasDerivAt_pow 2 h).div_const 2)
    have hloc : IsLocalMax f h := by
      filter_upwards [Ioi_mem_nhds hh] with x hx using hle x hx
    have h0 := hloc.hasDerivAt_eq_zero hfd
    have hden2 : h + (n - 1) * h = n * h := by ring
    have hq : ((n : ℝ) * (h + (n - 1) * h) - n * h * 1) / (h + (n - 1) * h) ^ 2 =
        (n - 1) / (n * h) := by
      rw [hden2, div_eq_div_iff (by positivity) (by positivity)]; ring
    rw [hq] at h0
    norm_num at h0
    have h1 : dφ 1 * (n - 1) = h ^ 2 * n := by
      have : dφ 1 * ((n - 1) / (n * h)) = h := by linarith
      field_simp at this
      linarith
    rw [eq_div_iff hn0]
    linarith
  · intro hfoc i t
    obtain ⟨x, hx⟩ := t
    rw [student_dev hn1 φ hh hx, hself]
    have hn0 : (0 : ℝ) < n := by linarith
    have hden : 0 < x + (n - 1) * h := by nlinarith
    have hr0 : 0 ≤ n * x / (x + (n - 1) * h) := by positivity
    have htan := foc_tangent_le (fun z _ => (hφ z).hasDerivWithinAt) hanti zero_le_one hr0
    -- the ratio lies below its tangent at `x = h`
    have hrat : n * x / (x + (n - 1) * h) - 1 ≤ (n - 1) * (x - h) / (n * h) := by
      rw [div_sub_one hden.ne', div_le_div_iff₀ hden (by positivity)]
      nlinarith [sq_nonneg (x - h), mul_nonneg (by linarith : (0 : ℝ) ≤ n - 1)
        (sq_nonneg (x - h))]
    have hkey : dφ 1 * ((n - 1) * (x - h) / (n * h)) = h * (x - h) := by
      have : dφ 1 * (n - 1) = h ^ 2 * n := by
        rw [hfoc]; field_simp
      field_simp
      nlinarith
    have : dφ 1 * (n * x / (x + (n - 1) * h) - 1) ≤ h * (x - h) := by
      rw [← hkey]; exact mul_le_mul_of_nonneg_left hrat hpos.le
    nlinarith [sq_nonneg (x - h)]

/-- **Exercise 11.D.1**, the comparison with Pareto optimality. At a symmetric profile every
student gets `φ(1) - h²/2`; halving the hours makes every student strictly better off. So the
equilibrium is inefficient (too much work), and no symmetric profile with `h > 0` is Pareto
optimal. -/
theorem exercise_11_D_1_pareto {n : ℕ} (hn : 1 ≤ n) (φ : ℝ → ℝ) {h : ℝ} (hh : 0 < h)
    (i : Fin n) :
    (studentGame n φ).payoff i (fun _ => ⟨h, hh⟩) = φ 1 - h ^ 2 / 2 ∧
      (studentGame n φ).payoff i (fun _ => ⟨h, hh⟩) <
        (studentGame n φ).payoff i (fun _ => ⟨h / 2, half_pos hh⟩) := by
  have hsym : ∀ (y : ℝ) (hy : 0 < y),
      (studentGame n φ).payoff i (fun _ => ⟨y, hy⟩) = φ 1 - y ^ 2 / 2 := fun y hy => by
    simp only [studentGame, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hn0 : (n : ℝ) ≠ 0 := by have : (1 : ℝ) ≤ n := by exact_mod_cast hn
                                 positivity
    congr 2
    field_simp
  rw [hsym, hsym]
  exact ⟨rfl, by nlinarith⟩

/-- An instance of Exercise 11.D.1: `φ(x) = 2x - x²/4` is concave with `φ'(1) = 3/2 > 0`; with
`n = 3` students the symmetric equilibrium has `h = 1` (`1 = (3/2)(2/3)`). -/
theorem exercise_11_D_1_instance :
    IsNashEquilibrium (studentGame 3 fun x => 2 * x - x ^ 2 / 4) (fun _ => ⟨1, one_pos⟩) := by
  have hφ : ∀ x : ℝ, HasDerivAt (fun x => 2 * x - x ^ 2 / 4) (2 - x / 2) x := fun x => by
    have h' := ((hasDerivAt_id x).const_mul 2).sub ((hasDerivAt_pow 2 x).div_const 4)
    exact (h'.congr_deriv (by simp only [Nat.cast_ofNat]; ring) :
      HasDerivAt (fun x : ℝ => 2 * x - x ^ 2 / 4) (2 - x / 2) x)
  refine (exercise_11_D_1 (by norm_num) hφ (fun a _ b _ hab => by linarith) (by norm_num)
    one_pos).2 ?_
  norm_num

/-! ## Exercise 11.D.2 -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The aggregate surplus of Exercise 11.D.2: `∑ᵢ φᵢ(hᵢ, ∑ₖ hₖ)`. -/
def d2Obj (φ : ι → ℝ × ℝ → ℝ) (h : ι → ℝ) : ℝ := ∑ i, φ i (h i, ∑ k, h k)

omit [DecidableEq ι] in
theorem d2Obj_concave (φ : ι → ℝ × ℝ → ℝ) (hconc : ∀ i, ConcaveOn ℝ Set.univ (φ i)) :
    ConcaveOn ℝ (orthant ι) (d2Obj φ) := by
  refine ⟨convex_orthant ι, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [d2Obj, smul_eq_mul]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have := (hconc i).2 (Set.mem_univ (x i, ∑ k, x k)) (Set.mem_univ (y i, ∑ k, y k)) ha hb hab
  simp only [smul_eq_mul, Prod.smul_mk, Prod.mk_add_mk] at this
  convert this using 2
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, Finset.mul_sum]

/-- The derivative of the aggregate surplus: its `j`-th partial is `aⱼ + ∑ᵢ bᵢ`. -/
theorem d2Obj_hasFDerivAt (φ : ι → ℝ × ℝ → ℝ) (a b : ι → ℝ × ℝ → ℝ)
    (hφ : ∀ i x, HasFDerivAt (φ i) (a i x • ContinuousLinearMap.fst ℝ ℝ ℝ +
      b i x • ContinuousLinearMap.snd ℝ ℝ ℝ) x) (h : ι → ℝ) :
    ∃ L : (ι → ℝ) →L[ℝ] ℝ, HasFDerivAt (d2Obj φ) L h ∧
      ∀ j, L (Pi.single j 1) = a j (h j, ∑ k, h k) + ∑ i, b i (h i, ∑ k, h k) := by
  set Li : ι → (ι → ℝ) →L[ℝ] ℝ × ℝ := fun i =>
    (ContinuousLinearMap.proj i).prod (∑ k, ContinuousLinearMap.proj k)
  have hLi : ∀ i (g : ι → ℝ), Li i g = (g i, ∑ k, g k) := fun i g => by
    simp [Li]
  set L := ∑ i, (a i (Li i h) • ContinuousLinearMap.fst ℝ ℝ ℝ +
    b i (Li i h) • ContinuousLinearMap.snd ℝ ℝ ℝ).comp (Li i)
  refine ⟨L, ?_, fun j => ?_⟩
  · have hterm : ∀ i ∈ (Finset.univ : Finset ι), HasFDerivAt (fun g => φ i (Li i g))
        ((a i (Li i h) • ContinuousLinearMap.fst ℝ ℝ ℝ +
          b i (Li i h) • ContinuousLinearMap.snd ℝ ℝ ℝ).comp (Li i)) h := fun i _ =>
      (hφ i (Li i h)).comp h (Li i).hasFDerivAt
    have := HasFDerivAt.fun_sum hterm
    have e : (fun g => ∑ i, φ i (Li i g)) = d2Obj φ := funext fun g => by simp only [hLi, d2Obj]
    rw [e] at this
    exact this
  · simp [L, hLi, Pi.single_apply, Finset.sum_add_distrib]

omit [DecidableEq ι] in
/-- **Exercise 11.D.2** (MWG, p. 380), optimal levels: `h ≥ 0` maximizes `∑ᵢ φᵢ(hᵢ, ∑ₖ hₖ)` iff for
every `j`, `∂₁φⱼ + ∑ᵢ ∂₂φᵢ ≤ 0`, with equality if `hⱼ > 0`. -/
theorem exercise_11_D_2_opt (φ : ι → ℝ × ℝ → ℝ) (a b : ι → ℝ × ℝ → ℝ)
    (hφ : ∀ i x, HasFDerivAt (φ i) (a i x • ContinuousLinearMap.fst ℝ ℝ ℝ +
      b i x • ContinuousLinearMap.snd ℝ ℝ ℝ) x) (hconc : ∀ i, ConcaveOn ℝ Set.univ (φ i))
    {h : ι → ℝ} (hh : h ∈ orthant ι) :
    (∀ y ∈ orthant ι, d2Obj φ y ≤ d2Obj φ h) ↔
      ∀ j, a j (h j, ∑ k, h k) + ∑ i, b i (h i, ∑ k, h k) ≤ 0 ∧
        (0 < h j → a j (h j, ∑ k, h k) + ∑ i, b i (h i, ∑ k, h k) = 0) := by
  classical
  obtain ⟨L, hL, hLe⟩ := d2Obj_hasFDerivAt φ a b hφ h
  rw [orthant_kt_iff (d2Obj_concave φ hconc) hh hL]
  simp only [hLe]

/-- One-variable Kuhn-Tucker for a concave function on `[0, ∞)`. -/
theorem concave1_kt_iff {g : ℝ → ℝ} (hg : ConcaveOn ℝ (Set.Ici 0) g) {d x : ℝ}
    (hd : HasDerivAt g d x) (hx : 0 ≤ x) :
    (∀ y, 0 ≤ y → g y ≤ g x) ↔ d ≤ 0 ∧ (0 < x → d = 0) := by
  constructor
  · intro hmax
    exact foc_max_necessary hd.hasDerivWithinAt hx hmax
  · rintro ⟨h1, h2⟩ y hy
    have ht := concave_tangent hg (Set.mem_Ici.2 hx) (Set.mem_Ici.2 hy) hd.hasFDerivAt
    have e : (ContinuousLinearMap.toSpanSingleton ℝ d) (y - x) = (y - x) * d := by simp
    rw [e] at ht
    rcases eq_or_lt_of_le hx with h0 | hp
    · rw [← h0] at ht ⊢
      nlinarith
    · rw [h2 hp] at ht; linarith

omit [Fintype ι] [DecidableEq ι] in
/-- Consumer `i`'s own payoff `x ↦ φᵢ(x, x + R) - t x` is concave with derivative
`∂₁φᵢ + ∂₂φᵢ - t`. -/
theorem d2_own (φ : ℝ × ℝ → ℝ) (a b : ℝ × ℝ → ℝ)
    (hφ : ∀ x, HasFDerivAt φ (a x • ContinuousLinearMap.fst ℝ ℝ ℝ +
      b x • ContinuousLinearMap.snd ℝ ℝ ℝ) x) (hconc : ConcaveOn ℝ Set.univ φ) (R t x : ℝ) :
    ConcaveOn ℝ (Set.Ici 0) (fun y => φ (y, y + R) - t * y) ∧
      HasDerivAt (fun y => φ (y, y + R) - t * y) (a (x, x + R) + b (x, x + R) - t) x := by
  constructor
  · refine ⟨convex_Ici 0, fun y _ z _ α β hα hβ hαβ => ?_⟩
    have := hconc.2 (Set.mem_univ (y, y + R)) (Set.mem_univ (z, z + R)) hα hβ hαβ
    simp only [smul_eq_mul, Prod.smul_mk, Prod.mk_add_mk] at this ⊢
    have e : α * (y + R) + β * (z + R) = α * y + β * z + R := by
      linear_combination R * hαβ
    rw [e] at this
    nlinarith
  · have hpath : HasDerivAt (fun y => (y, y + R)) ((1 : ℝ), (1 : ℝ)) x :=
      (hasDerivAt_id x).prodMk ((hasDerivAt_id x).add_const R)
    have h1 := (hφ (x, x + R)).comp_hasDerivAt x hpath
    have h2 : HasDerivAt (fun y => t * y) t x := by simpa using (hasDerivAt_id x).const_mul t
    have := h1.sub h2
    simp only [add_apply, smul_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', smul_eq_mul, mul_one] at this
    exact this

/-- An equilibrium with per-unit taxes `tᵢ` (Exercise 11.D.2): each consumer chooses `hᵢ ≥ 0` to
maximize `φᵢ(hᵢ, hᵢ + ∑_{k ≠ i} hₖ) - tᵢ hᵢ` given the others' choices. -/
def IsD2Eq (φ : ι → ℝ × ℝ → ℝ) (t : ι → ℝ) (h : ι → ℝ) : Prop :=
  ∀ i, 0 ≤ h i ∧ ∀ y, 0 ≤ y → φ i (y, y + (∑ k, h k - h i)) - t i * y ≤
    φ i (h i, h i + (∑ k, h k - h i)) - t i * h i

omit [DecidableEq ι] in
/-- **Exercise 11.D.2**, equilibrium levels: `h ≥ 0` is an equilibrium with taxes `t` iff
`∂₁φᵢ + ∂₂φᵢ ≤ tᵢ` at `(hᵢ, ∑ₖ hₖ)`, with equality if `hᵢ > 0` (with `t = 0`: the unfettered
equilibrium, which ignores the effect `∑_{k ≠ i} ∂₂φₖ` on others). -/
theorem exercise_11_D_2_eq (φ : ι → ℝ × ℝ → ℝ) (a b : ι → ℝ × ℝ → ℝ)
    (hφ : ∀ i x, HasFDerivAt (φ i) (a i x • ContinuousLinearMap.fst ℝ ℝ ℝ +
      b i x • ContinuousLinearMap.snd ℝ ℝ ℝ) x) (hconc : ∀ i, ConcaveOn ℝ Set.univ (φ i))
    (t : ι → ℝ) {h : ι → ℝ} (hh : h ∈ orthant ι) :
    IsD2Eq φ t h ↔ ∀ i, a i (h i, ∑ k, h k) + b i (h i, ∑ k, h k) - t i ≤ 0 ∧
      (0 < h i → a i (h i, ∑ k, h k) + b i (h i, ∑ k, h k) - t i = 0) := by
  refine forall_congr' fun i => ?_
  obtain ⟨hc, hd⟩ := d2_own (φ i) (a i) (b i) (hφ i) (hconc i) (∑ k, h k - h i) (t i) (h i)
  have key := concave1_kt_iff hc hd (hh i)
  have e : h i + (∑ k, h k - h i) = ∑ k, h k := by ring
  rw [e] at key
  constructor
  · rintro ⟨_, hmax⟩
    exact key.1 (by simpa only [e] using hmax)
  · intro hk
    exact ⟨hh i, by simpa only [e] using key.2 hk⟩

omit [DecidableEq ι] in
/-- **Exercise 11.D.2**, the corrective tax: `tᵢ = -∑_{k ≠ i} ∂₂φₖ(hₖ°, ∑ h°)` makes the optimum
`h°` an equilibrium. -/
theorem exercise_11_D_2_tax (φ : ι → ℝ × ℝ → ℝ) (a b : ι → ℝ × ℝ → ℝ)
    (hφ : ∀ i x, HasFDerivAt (φ i) (a i x • ContinuousLinearMap.fst ℝ ℝ ℝ +
      b i x • ContinuousLinearMap.snd ℝ ℝ ℝ) x) (hconc : ∀ i, ConcaveOn ℝ Set.univ (φ i))
    {h : ι → ℝ} (hh : h ∈ orthant ι) (hopt : ∀ y ∈ orthant ι, d2Obj φ y ≤ d2Obj φ h) :
    IsD2Eq φ (fun i => -(∑ k, b k (h k, ∑ m, h m) - b i (h i, ∑ m, h m))) h := by
  have hfoc := (exercise_11_D_2_opt φ a b hφ hconc hh).1 hopt
  rw [exercise_11_D_2_eq φ a b hφ hconc _ hh]
  intro i
  exact ⟨by linarith [(hfoc i).1], fun hp => by linarith [(hfoc i).2 hp]⟩

end MWG.ExternalitiesPublicGoods
