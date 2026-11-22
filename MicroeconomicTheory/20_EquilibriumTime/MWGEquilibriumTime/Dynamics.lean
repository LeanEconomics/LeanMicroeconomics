/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGEquilibriumTime.Euler
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Dynamics (MWG Section 20.F, pp. 759-765)

MWG, Chapter 20, Section 20.F and Exercises 20.F.1-20.F.5 (p. 785). One capital good.

* Steady states are the fixed points of the policy function (`steady_state_iff_fixed`).
* Figures 20.F.1-20.F.2: an increasing continuous policy function on an interval drives every path
  to a steady state, and to the unique one if it is unique (`monotone_policy_converges`,
  `monotone_policy_converges_unique`); Figure 20.F.3, a two-cycle (`two_cycle_example`);
  Figure 20.F.4, a three-cycle (`three_cycle_example`).
* Low discount of time: the derivative of the policy function (`policy_deriv`), and the
  correction that the printed bound on `|ψ'|` goes the other way
  (`policy_deriv_bound_printed_false`, `policy_deriv_lower_bound`); **Exercise 20.F.2**
  (`exercise_20_F_2`, true on `ℝ_+`, false on `ℝ_{++}`: `exercise_20_F_2_false`); footnote 26
  (`footnote_20_26`); the turnpike intuition that a cycle is beaten by its mean
  (`cycle_beaten_by_mean`).
* Cross derivatives of uniform sign: increasing differences make the policy increasing
  (`policy_mono_of_increasing_differences`, `increasing_differences_of_cross_pos`) and decreasing
  for the opposite sign (`policy_anti_of_decreasing_differences`); **Exercise 20.F.3**
  (`exercise_20_F_3_rs`, `exercise_20_F_3_adjustment`).
* **Example 20.F.1** and **Exercises 20.F.4-20.F.5** (`example_20_F_1`, `exercise_20_F_4`,
  `exercise_20_F_5`).
* **Exercise 20.F.1**: the Engel-curve property of the hinted utility (`exercise_20_F_1_engel`).

OPEN: the period-three-implies-chaos theorem, the Boldrin-Montrucchio theorem and the turnpike
theorem (cited, not stated precisely in MWG), and the monotonicity and concavity parts of
Exercise 20.F.1.
-/

open Filter Topology

namespace MWG.EquilibriumTime

/-! ### Steady states and monotone dynamics -/

/-- **Steady states are fixed points of the policy function** (MWG, p. 760): if `ψ` is the policy
function (the first-period choice of every optimal path) and an optimal path from `k` exists, the
constant path at `k` is optimal if and only if `ψ(k) = k`. -/
theorem steady_state_iff_fixed {A : Set (ℝ × ℝ)} {δ : ℝ} (hδ : 0 < δ) {u : ℝ × ℝ → ℝ} {ψ : ℝ → ℝ}
    (hψ : ∀ a k', OptimalFrom A δ u a k' → k' 1 = ψ a) {k : ℝ} {kp : ℕ → ℝ}
    (hopt : OptimalFrom A δ u k kp) :
    OptimalFrom A δ u k (fun _ => k) ↔ ψ k = k := by
  constructor
  · intro h; exact (hψ k _ h).symm
  · intro hfix
    have hpath : ∀ t, kp t = k := by
      intro t
      induction t with
      | zero => exact hopt.1.1
      | succ t ih => rw [policy_20_D_10 hδ hopt hψ t, ih, hfix]
    have : kp = fun _ => k := funext hpath
    rw [← this]; exact hopt

/-- **Figure 20.F.2** (MWG, p. 760): if the policy function is nondecreasing and continuous and
maps `[a, b]` into itself, the path `k_{t+1} = ψ(k_t)` from any `k₀ ∈ [a, b]` converges
(monotonically) to a steady state. -/
theorem monotone_policy_converges {ψ : ℝ → ℝ} {a b : ℝ} (hmono : MonotoneOn ψ (Set.Icc a b))
    (hcont : ContinuousOn ψ (Set.Icc a b)) (hmaps : Set.MapsTo ψ (Set.Icc a b) (Set.Icc a b))
    {k₀ : ℝ} (hk₀ : k₀ ∈ Set.Icc a b) :
    ∃ ks ∈ Set.Icc a b, ψ ks = ks ∧ Tendsto (fun t => ψ^[t] k₀) atTop (𝓝 ks) := by
  set k : ℕ → ℝ := fun t => ψ^[t] k₀ with hk
  have hmem : ∀ t, k t ∈ Set.Icc a b := by
    intro t
    induction t with
    | zero => exact hk₀
    | succ t ih =>
      simp only [hk, Function.iterate_succ_apply'] at ih ⊢
      exact hmaps ih
  have hsucc : ∀ t, k (t + 1) = ψ (k t) := fun t => by
    simp only [hk, Function.iterate_succ_apply']
  -- the path is monotone
  have hlim : ∃ ks, Tendsto k atTop (𝓝 ks) := by
    rcases le_total (k 0) (k 1) with h01 | h10
    · have hm : Monotone k := by
        refine monotone_nat_of_le_succ fun t => ?_
        induction t with
        | zero => exact h01
        | succ t ih =>
          calc k (t + 1) = ψ (k t) := hsucc t
            _ ≤ ψ (k (t + 1)) := hmono (hmem t) (hmem (t + 1)) ih
            _ = k (t + 1 + 1) := (hsucc (t + 1)).symm
      exact ⟨_, tendsto_atTop_ciSup hm ⟨b, by rintro _ ⟨t, rfl⟩; exact (hmem t).2⟩⟩
    · have ha : Antitone k := by
        refine antitone_nat_of_succ_le fun t => ?_
        induction t with
        | zero => exact h10
        | succ t ih =>
          calc k (t + 1 + 1) = ψ (k (t + 1)) := hsucc (t + 1)
            _ ≤ ψ (k t) := hmono (hmem (t + 1)) (hmem t) ih
            _ = k (t + 1) := (hsucc t).symm
      exact ⟨_, tendsto_atTop_ciInf ha ⟨a, by rintro _ ⟨t, rfl⟩; exact (hmem t).1⟩⟩
  obtain ⟨ks, hks⟩ := hlim
  have hksmem : ks ∈ Set.Icc a b :=
    isClosed_Icc.mem_of_tendsto hks (Eventually.of_forall hmem)
  refine ⟨ks, hksmem, ?_, hks⟩
  have h1 : Tendsto (fun t => k (t + 1)) atTop (𝓝 ks) := hks.comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun t => ψ (k t)) atTop (𝓝 (ψ ks)) :=
    ((hcont ks hksmem).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hks, Eventually.of_forall hmem⟩))
  exact (tendsto_nhds_unique (h1.congr hsucc) h2).symm

/-- **Figure 20.F.1** (MWG, p. 760): with a single steady state, it is globally stable. -/
theorem monotone_policy_converges_unique {ψ : ℝ → ℝ} {a b ks : ℝ}
    (hmono : MonotoneOn ψ (Set.Icc a b)) (hcont : ContinuousOn ψ (Set.Icc a b))
    (hmaps : Set.MapsTo ψ (Set.Icc a b) (Set.Icc a b))
    (huniq : ∀ x ∈ Set.Icc a b, ψ x = x → x = ks) {k₀ : ℝ} (hk₀ : k₀ ∈ Set.Icc a b) :
    Tendsto (fun t => ψ^[t] k₀) atTop (𝓝 ks) := by
  obtain ⟨k', hk', hfix, hlim⟩ := monotone_policy_converges hmono hcont hmaps hk₀
  rwa [huniq k' hk' hfix] at hlim

/-- **Figure 20.F.3** (MWG, p. 760): a decreasing policy function with a single steady state and a
cycle of period two: `ψ(k) = 1 - k` on `[0, 1]`, steady state `1/2`, cycle `0 → 1 → 0`. -/
theorem two_cycle_example :
    let ψ : ℝ → ℝ := fun k => 1 - k
    (∀ k, ψ k = k ↔ k = 1 / 2) ∧ ψ 0 = 1 ∧ ψ 1 = 0 := by
  intro ψ
  refine ⟨fun k => ⟨fun h => by simp only [ψ] at h; linarith, fun h => by
    simp only [ψ, h]; norm_num⟩, by simp [ψ], by simp [ψ]⟩

/-- **Figure 20.F.4** (MWG, p. 760): a continuous policy function with a cycle of period three:
`ψ(k) = 1 + k` on `[0, 1]`, `ψ(k) = 4 - 2k` on `[1, 2]`, with `0 → 1 → 2 → 0`. (That a cycle of
period three implies chaos is a cited theorem, OPEN here.) -/
theorem three_cycle_example :
    let ψ : ℝ → ℝ := fun k => if k ≤ 1 then 1 + k else 4 - 2 * k
    Continuous ψ ∧ ψ 0 = 1 ∧ ψ 1 = 2 ∧ ψ 2 = 0 := by
  intro ψ
  refine ⟨?_, by norm_num [ψ], by norm_num [ψ], by norm_num [ψ]⟩
  exact Continuous.if_le (by fun_prop) (by fun_prop) continuous_id continuous_const
    (fun x hx => by rw [hx]; norm_num)

/-! ### Low discount of time -/

/-- **The derivative of the policy function** (MWG, p. 762): differentiating the first-order
condition (20.F.3) `∇₂u(k, ψ(k)) + δ V'(ψ(k)) = 0`: if `∇₂u(k, ψ(k)) + δ V'(ψ(k))` vanishes
identically near `k` and its total derivative is `∇²₂₁u + (∇²₂₂u + δ V'') ψ'(k)`, then
`ψ'(k) = -∇²₂₁u / (∇²₂₂u + δ V'')`. -/
theorem policy_deriv {u21 u22 V2 δ dψ : ℝ} (hden : u22 + δ * V2 ≠ 0)
    (hfoc : u21 + (u22 + δ * V2) * dψ = 0) : dψ = -u21 / (u22 + δ * V2) := by
  field_simp; linarith

/-- **Correction to the bound on `|ψ'|`** (MWG, p. 762): from `∇²₂₂u ≤ 0` and
`δ ∇²₁₁u ≤ δ V'' ≤ 0` it does **not** follow that `|ψ'| ≤ |∇²₂₁u / (∇²₂₂u + δ∇²₁₁u)|`: with
`∇²₂₁u = 1`, `∇²₂₂u = -1`, `∇²₁₁u = -4` (so that `(∇²₂₁u)² ≤ ∇²₁₁u ∇²₂₂u`), `V'' = 0` and
`δ = 1/2`, `ψ' = 1` while the printed bound is `1/3`. -/
theorem policy_deriv_bound_printed_false :
    let u21 : ℝ := 1
    let u22 : ℝ := -1
    let u11 : ℝ := -4
    let V2 : ℝ := 0
    let δ : ℝ := 1 / 2
    u22 ≤ 0 ∧ δ * u11 ≤ δ * V2 ∧ δ * V2 ≤ 0 ∧ u21 ^ 2 ≤ u11 * u22 ∧
      ¬ |-u21 / (u22 + δ * V2)| ≤ |u21 / (u22 + δ * u11)| := by
  intro u21 u22 u11 V2 δ
  norm_num [u21, u22, u11, V2, δ, abs_of_pos, abs_of_neg]

/-- **The correct direction** (MWG, p. 762): under `∇²₂₂u ≤ 0` and `δ∇²₁₁u ≤ δ V'' ≤ 0` (with
nonzero denominators), `|ψ'| ≥ |∇²₂₁u / (∇²₂₂u + δ∇²₁₁u)|`, and `|ψ'| ≤ |∇²₂₁u / ∇²₂₂u|`. -/
theorem policy_deriv_lower_bound {u21 u22 u11 V2 δ : ℝ} (h22 : u22 < 0) (h1 : δ * u11 ≤ δ * V2)
    (h2 : δ * V2 ≤ 0) :
    |u21 / (u22 + δ * u11)| ≤ |-u21 / (u22 + δ * V2)| ∧
      |-u21 / (u22 + δ * V2)| ≤ |u21 / u22| := by
  have hd1 : u22 + δ * u11 < 0 := by linarith
  have hd2 : u22 + δ * V2 < 0 := by linarith
  rw [abs_div, abs_div, abs_div, abs_neg, abs_of_neg hd1, abs_of_neg hd2, abs_of_neg h22]
  constructor
  · exact div_le_div_of_nonneg_left (abs_nonneg _) (by linarith) (by linarith)
  · exact div_le_div_of_nonneg_left (abs_nonneg _) (by linarith) (by linarith)

/-- **Exercise 20.F.2** (MWG, p. 785), on `ℝ_+`: a contraction `ψ : ℝ_+ → ℝ_+` has a unique steady
state, and every path `k_{t+1} = ψ(k_t)` converges to it (global stability). -/
theorem exercise_20_F_2 {ψ : ℝ → ℝ} (hmaps : ∀ k, 0 ≤ k → 0 ≤ ψ k) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1) (hlip : ∀ x y, 0 ≤ x → 0 ≤ y → |ψ x - ψ y| ≤ θ * |x - y|) :
    ∃ ks, 0 ≤ ks ∧ ψ ks = ks ∧ (∀ x, 0 ≤ x → ψ x = x → x = ks) ∧
      ∀ k₀, 0 ≤ k₀ → Tendsto (fun t => ψ^[t] k₀) atTop (𝓝 ks) := by
  -- the restriction to the complete space `ℝ_+`
  set g : Set.Ici (0 : ℝ) → Set.Ici (0 : ℝ) := fun x => ⟨ψ x, hmaps x x.2⟩ with hg
  have hcon : ContractingWith ⟨θ, hθ0⟩ g := by
    refine ⟨by exact_mod_cast hθ1, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
    simp only [hg, Subtype.dist_eq, Real.dist_eq]
    exact hlip x y x.2 y.2
  have : CompleteSpace (Set.Ici (0 : ℝ)) := isClosed_Ici.completeSpace_coe
  set ks := ContractingWith.fixedPoint g hcon with hks
  have hfix : g ks = ks := ContractingWith.fixedPoint_isFixedPt hcon
  refine ⟨ks, ks.2, congrArg Subtype.val hfix, fun x hx hxfix => ?_, fun k₀ hk₀ => ?_⟩
  · have : g ⟨x, hx⟩ = ⟨x, hx⟩ := Subtype.ext hxfix
    exact congrArg Subtype.val (ContractingWith.fixedPoint_unique hcon this)
  · have h := ContractingWith.tendsto_iterate_fixedPoint hcon ⟨k₀, hk₀⟩
    have hiter : ∀ t, ((g^[t] ⟨k₀, hk₀⟩ : Set.Ici (0 : ℝ)) : ℝ) = ψ^[t] k₀ := by
      intro t
      induction t with
      | zero => rfl
      | succ t ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
    have := (continuous_subtype_val.tendsto _).comp h
    exact this.congr fun t => hiter t

/-- **Correction to Exercise 20.F.2** (MWG, p. 785): on `ℝ_{++}` a contraction need not have a
steady state: `ψ(k) = k/2` maps `(0, ∞)` into itself with Lipschitz constant `1/2` and has no
fixed point there. -/
theorem exercise_20_F_2_false :
    (∀ k : ℝ, 0 < k → 0 < k / 2) ∧ (∀ x y : ℝ, |x / 2 - y / 2| ≤ 1 / 2 * |x - y|) ∧
      ∀ k : ℝ, 0 < k → k / 2 ≠ k := by
  refine ⟨fun k hk => by positivity, fun x y => ?_, fun k hk h => by linarith⟩
  rw [← sub_div, abs_div, abs_two]; linarith [abs_nonneg (x - y)]

/-- **Footnote 26** (MWG, p. 763): a contraction need not be monotone and convergence may be
cyclical: `ψ(k) = 1 - k/2` on `[0, 2]` is decreasing with Lipschitz constant `1/2`; the deviations
from the steady state `2/3` alternate in sign and dampen. -/
theorem footnote_20_26 (k : ℝ) (t : ℕ) :
    (fun x : ℝ => 1 - x / 2)^[t] k - 2 / 3 = (-1 / 2) ^ t * (k - 2 / 3) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply', pow_succ]
    have : (fun x : ℝ => 1 - x / 2)^[t] k = (-1 / 2) ^ t * (k - 2 / 3) + 2 / 3 := by linarith
    rw [this]
    ring

/-- **The turnpike intuition** (MWG, p. 763): for a strictly concave `u` on a convex `A`, a
nonconstant cyclical path of period `P` has average utility over the cycle strictly below
`u(k̄, k̄)`, where `k̄` is the mean capital over the cycle. -/
theorem cycle_beaten_by_mean {A : Set (ℝ × ℝ)} {u : ℝ × ℝ → ℝ} (hu : StrictConcaveOn ℝ A u)
    {P : ℕ} (hP : 0 < P) {k : ℕ → ℝ} (hper : k P = k 0) (hA : ∀ t < P, (k t, k (t + 1)) ∈ A)
    (hnc : ∃ s < P, ∃ r < P, (k s, k (s + 1)) ≠ (k r, k (r + 1))) :
    (1 / P : ℝ) * ∑ t ∈ Finset.range P, u (k t, k (t + 1))
      < u ((1 / P : ℝ) * ∑ t ∈ Finset.range P, k t, (1 / P : ℝ) * ∑ t ∈ Finset.range P, k t) := by
  have hPr : (0 : ℝ) < P := by exact_mod_cast hP
  have hshift : ∑ t ∈ Finset.range P, k (t + 1) = ∑ t ∈ Finset.range P, k t := by
    obtain ⟨P', rfl⟩ : ∃ P', P = P' + 1 := ⟨P - 1, by omega⟩
    rw [Finset.sum_range_succ, Finset.sum_range_succ' (fun t => k t), hper]
  have hj := hu.lt_map_sum (t := Finset.range P) (w := fun _ => (1 / P : ℝ))
    (p := fun t => (k t, k (t + 1))) (fun _ _ => by positivity)
    (by simp; field_simp) (fun t ht => hA t (Finset.mem_range.1 ht))
    (by obtain ⟨s, hs, r, hr, hne⟩ := hnc
        exact ⟨s, Finset.mem_range.2 hs, r, Finset.mem_range.2 hr, hne⟩)
  have hsum : ∑ t ∈ Finset.range P, (1 / P : ℝ) • (k t, k (t + 1))
      = ((1 / P : ℝ) * ∑ t ∈ Finset.range P, k t, (1 / P : ℝ) * ∑ t ∈ Finset.range P, k t) := by
    rw [← Finset.smul_sum]
    refine Prod.ext ?_ ?_
    · simp only [Prod.smul_fst, Prod.fst_sum, smul_eq_mul]
    · simp only [Prod.smul_snd, Prod.snd_sum, smul_eq_mul, hshift]
  rw [hsum] at hj
  simpa [Finset.mul_sum, smul_eq_mul] using hj

/-! ### Cross derivatives of uniform sign -/

/-- `u` has **strictly increasing differences**: `u(k₂, ·) - u(k₁, ·)` is strictly increasing for
`k₁ < k₂` (the integrated form of `∇²₁₂u > 0`). -/
def StrictIncDiff (u : ℝ → ℝ → ℝ) : Prop :=
  ∀ k₁ k₂ a₁ a₂, k₁ < k₂ → a₁ < a₂ → u k₂ a₁ - u k₁ a₁ < u k₂ a₂ - u k₁ a₂

/-- **The cross-derivative condition implies increasing differences**: if `∇₂u(k, k')` exists
everywhere and `k ↦ ∇₂u(k, k')` has derivative `∇²₁₂u(k, k') > 0`, then `u` has strictly
increasing differences. -/
theorem increasing_differences_of_cross_pos {u u2 u12 : ℝ → ℝ → ℝ}
    (h2 : ∀ k a, HasDerivAt (fun a' => u k a') (u2 k a) a)
    (h12 : ∀ k a, HasDerivAt (fun k' => u2 k' a) (u12 k a) k) (hpos : ∀ k a, 0 < u12 k a) :
    StrictIncDiff u := by
  intro k₁ k₂ a₁ a₂ hk ha
  -- `a ↦ u k₂ a - u k₁ a` has derivative `u2 k₂ a - u2 k₁ a > 0`
  have hder : ∀ a, 0 < u2 k₂ a - u2 k₁ a := by
    intro a
    obtain ⟨c, _, hc⟩ := exists_hasDerivAt_eq_slope (fun k' => u2 k' a) (fun k' => u12 k' a) hk
      (fun x _ => (h12 x a).continuousAt.continuousWithinAt) (fun x _ => h12 x a)
    have := hpos c a
    rw [hc] at this
    exact (div_pos_iff_of_pos_right (by linarith)).1 this |> fun h => by linarith
  obtain ⟨c, _, hc⟩ := exists_hasDerivAt_eq_slope (fun a => u k₂ a - u k₁ a)
    (fun a => u2 k₂ a - u2 k₁ a) ha
    (fun x _ => ((h2 k₂ x).sub (h2 k₁ x)).continuousAt.continuousWithinAt)
    (fun x _ => (h2 k₂ x).sub (h2 k₁ x))
  have := hder c
  rw [hc] at this
  have h' := (div_pos_iff_of_pos_right (by linarith : (0 : ℝ) < a₂ - a₁)).1 this
  linarith

/-- **Under strictly increasing differences the policy function is increasing** (MWG, pp. 763-764,
Figure 20.F.6): if `ψ(k)` maximizes `u(k, k') + δ V(k')` over a common feasible set, then
`k₁ < k₂` implies `ψ(k₁) ≤ ψ(k₂)`. -/
theorem policy_mono_of_increasing_differences {u : ℝ → ℝ → ℝ} (hu : StrictIncDiff u)
    {δ : ℝ} {V : ℝ → ℝ} {S : Set ℝ} {ψ : ℝ → ℝ}
    (hψ : ∀ k, ψ k ∈ S ∧ ∀ a ∈ S, u k a + δ * V a ≤ u k (ψ k) + δ * V (ψ k))
    {k₁ k₂ : ℝ} (hk : k₁ < k₂) : ψ k₁ ≤ ψ k₂ := by
  by_contra hlt
  push Not at hlt
  have h1 := (hψ k₁).2 (ψ k₂) (hψ k₂).1
  have h2 := (hψ k₂).2 (ψ k₁) (hψ k₁).1
  have := hu k₁ k₂ (ψ k₂) (ψ k₁) hk hlt
  linarith

/-- **Cross derivative of uniform negative sign** (MWG, p. 764): with strictly decreasing
differences the policy function is decreasing. -/
theorem policy_anti_of_decreasing_differences {u : ℝ → ℝ → ℝ}
    (hu : StrictIncDiff (fun k a => -u k a)) {δ : ℝ} {V : ℝ → ℝ} {S : Set ℝ} {ψ : ℝ → ℝ}
    (hψ : ∀ k, ψ k ∈ S ∧ ∀ a ∈ S, u k a + δ * V a ≤ u k (ψ k) + δ * V (ψ k))
    {k₁ k₂ : ℝ} (hk : k₁ < k₂) : ψ k₂ ≤ ψ k₁ := by
  by_contra hlt
  push Not at hlt
  have h1 := (hψ k₁).2 (ψ k₂) (hψ k₂).1
  have h2 := (hψ k₂).2 (ψ k₁) (hψ k₁).1
  have := hu k₁ k₂ (ψ k₁) (ψ k₂) hk hlt
  simp only at this
  linarith

/-- **Exercise 20.F.3**, Ramsey-Solow (MWG, p. 785): for `u(k, k') = û(F(k) - k')`,
`∇₂u = -û'(c)` and `∇²₁₂u = -û''(c) F'(k) > 0` when `û'' < 0 < F'`. -/
theorem exercise_20_F_3_rs {uh' uh'' F F' : ℝ → ℝ} {k a : ℝ}
    (huh : HasDerivAt uh' (uh'' (F k - a)) (F k - a)) (hF : HasDerivAt F (F' k) k)
    (hneg : uh'' (F k - a) < 0) (hpos : 0 < F' k) :
    HasDerivAt (fun k' => -uh' (F k' - a)) (-(uh'' (F k - a) * F' k)) k ∧
      0 < -(uh'' (F k - a) * F' k) := by
  refine ⟨?_, by nlinarith⟩
  exact (huh.comp k (hF.sub_const a)).neg

/-- **Exercise 20.F.3**, cost of adjustment (MWG, p. 785): for
`u(k, k') = û(F(k) - k' - γ(k' - k))`, `∇₂u = -û'(c)(1 + γ'(k' - k))` and
`∇²₁₂u = -û''(c)(F'(k) + γ'(k' - k))(1 + γ'(k' - k)) + û'(c) γ''(k' - k) > 0` when `û'' < 0 < û'`,
`F' + γ' > 0`, `1 + γ' > 0` and `γ'' ≥ 0`. -/
theorem exercise_20_F_3_adjustment {uh' uh'' F F' γ γ' γ'' : ℝ → ℝ} {k a : ℝ}
    (huh : HasDerivAt uh' (uh'' (F k - a - γ (a - k))) (F k - a - γ (a - k)))
    (hF : HasDerivAt F (F' k) k) (hγ : HasDerivAt γ (γ' (a - k)) (a - k))
    (hγ' : HasDerivAt γ' (γ'' (a - k)) (a - k))
    (hneg : uh'' (F k - a - γ (a - k)) < 0) (hpos : 0 < uh' (F k - a - γ (a - k)))
    (h1 : 0 < F' k + γ' (a - k)) (h2 : 0 < 1 + γ' (a - k)) (h3 : 0 ≤ γ'' (a - k)) :
    HasDerivAt (fun k' => -uh' (F k' - a - γ (a - k')) * (1 + γ' (a - k')))
      (-(uh'' (F k - a - γ (a - k)) * (F' k + γ' (a - k))) * (1 + γ' (a - k))
        + uh' (F k - a - γ (a - k)) * γ'' (a - k)) k ∧
      0 < -(uh'' (F k - a - γ (a - k)) * (F' k + γ' (a - k))) * (1 + γ' (a - k))
        + uh' (F k - a - γ (a - k)) * γ'' (a - k) := by
  refine ⟨?_, by nlinarith [mul_nonneg hpos.le h3, mul_pos (mul_pos (neg_pos.2 hneg) h1) h2]⟩
  have hc : HasDerivAt (fun k' => F k' - a - γ (a - k')) (F' k + γ' (a - k)) k := by
    have := (hF.sub_const a).sub (hγ.comp_const_sub a k)
    convert this using 1
    ring
  have hd1 : HasDerivAt (fun k' => -uh' (F k' - a - γ (a - k')))
      (-(uh'' (F k - a - γ (a - k)) * (F' k + γ' (a - k)))) k := (huh.comp k hc).neg
  have hd2 : HasDerivAt (fun k' => 1 + γ' (a - k')) (-γ'' (a - k)) k := by
    have := (hγ'.comp_const_sub a k).const_add 1
    simpa using this
  convert hd1.mul hd2 using 1
  ring

/-! ### Example 20.F.1 and Exercises 20.F.4-20.F.5 -/

/-- **Example 20.F.1** (MWG, p. 765): with separable utility `u(k, k') = g(k) + h(k')` the
maximizer of `u(k, k') + δ V(k')` does not depend on `k` (the policy function is constant), and
any value function satisfying the Bellman equation is `g` plus a constant. -/
theorem example_20_F_1 {g h V : ℝ → ℝ} {δ : ℝ} {S : Set ℝ} {kb : ℝ}
    (hmax : ∀ a ∈ S, h a + δ * V a ≤ h kb + δ * V kb) :
    (∀ k, ∀ a ∈ S, g k + h a + δ * V a ≤ g k + h kb + δ * V kb) ∧
      ((∀ k, V k = g k + h kb + δ * V kb) → ∀ k, V k = g k + (h kb + δ * V kb)) := by
  refine ⟨fun k a ha => by linarith [hmax a ha], fun hV k => by rw [hV k]; ring⟩

/-- **Exercise 20.F.4** (MWG, p. 785), a transitory shock: with the old continuation value `V`,
the new choice `k₁` maximizes `h(k', θ) + δ V(k')`; if `h` has strictly increasing differences in
`(k', θ)` (the sign of `∂²h/∂k'∂θ` is positive), then `k₁ ≥ k̄` for `θ > 0`; with strictly
decreasing differences `k₁ ≤ k̄`. -/
theorem exercise_20_F_4 {h : ℝ → ℝ → ℝ} {V : ℝ → ℝ} {δ θ kb k₁ : ℝ} {S : Set ℝ} (hθ : 0 < θ)
    (hkb : kb ∈ S) (hk₁ : k₁ ∈ S)
    (hmax0 : ∀ a ∈ S, h a 0 + δ * V a ≤ h kb 0 + δ * V kb)
    (hmaxθ : ∀ a ∈ S, h a θ + δ * V a ≤ h k₁ θ + δ * V k₁) :
    (StrictIncDiff (fun θ' a => h a θ') → kb ≤ k₁) ∧
      (StrictIncDiff (fun θ' a => -h a θ') → k₁ ≤ kb) := by
  constructor
  · intro hd
    by_contra hlt; push Not at hlt
    have e1 := hmax0 k₁ hk₁
    have e2 := hmaxθ kb hkb
    have := hd 0 θ k₁ kb hθ hlt
    linarith
  · intro hd
    by_contra hlt; push Not at hlt
    have e1 := hmax0 k₁ hk₁
    have e2 := hmaxθ kb hkb
    have := hd 0 θ kb k₁ hθ hlt
    simp only at this
    linarith

/-- **Exercise 20.F.5** (MWG, p. 785), a permanent shock: the new value function is
`V_θ(k) = g(k, θ) + C_θ` (Example 20.F.1). If `g` has strictly increasing differences in
`(k, θ)`, then `V_θ - V` is strictly increasing, so (by increasing differences in the
continuation value) the choice under the permanent shock `k₁ᴾ` is at least the choice under the
transitory shock `k₁ᵀ`. Together with Exercise 20.F.4, `k₁ᴾ ≥ k₁ᵀ ≥ k̄`. -/
theorem exercise_20_F_5 {g h : ℝ → ℝ → ℝ} {δ θ Cθ C₀ kT kP : ℝ} (hδ : 0 < δ) (hθ : 0 < θ)
    {S : Set ℝ} (hkT : kT ∈ S) (hkP : kP ∈ S) (hg : StrictIncDiff (fun θ' k => g k θ'))
    (hmaxT : ∀ a ∈ S, h a θ + δ * (g a 0 + C₀) ≤ h kT θ + δ * (g kT 0 + C₀))
    (hmaxP : ∀ a ∈ S, h a θ + δ * (g a θ + Cθ) ≤ h kP θ + δ * (g kP θ + Cθ)) :
    kT ≤ kP := by
  by_contra hlt; push Not at hlt
  have e1 := hmaxT kP hkP
  have e2 := hmaxP kT hkT
  have := hg 0 θ kP kT hθ hlt
  nlinarith

/-! ### Exercise 20.F.1 -/

/-- **Exercise 20.F.1** (MWG, p. 785), the Engel-curve part: for
`u(x₁, x₂) = (x₁ + x₂)^{1/2} - ε[(x₁ - γ₁(x₁ + x₂))² + (x₂ - γ₂(x₁ + x₂))²]` with
`γ₁(w) + γ₂(w) = w` and `ε > 0`, on the budget line `x₁ + x₂ = w` the unique maximizer of `u` is
`(γ₁(w), γ₂(w))`. (Monotonicity and concavity for small `ε` are OPEN.) -/
theorem exercise_20_F_1_engel {γ₁ γ₂ : ℝ → ℝ} {w ε : ℝ} (hε : 0 < ε)
    (hγ : γ₁ w + γ₂ w = w) {x₁ x₂ : ℝ} (hx : x₁ + x₂ = w) :
    let u : ℝ → ℝ → ℝ := fun x₁ x₂ => Real.sqrt (x₁ + x₂)
      - ε * ((x₁ - γ₁ (x₁ + x₂)) ^ 2 + (x₂ - γ₂ (x₁ + x₂)) ^ 2)
    u x₁ x₂ ≤ u (γ₁ w) (γ₂ w) ∧ (u x₁ x₂ = u (γ₁ w) (γ₂ w) → x₁ = γ₁ w ∧ x₂ = γ₂ w) := by
  intro u
  simp only [u, hx, hγ, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    add_zero, mul_zero, sub_zero]
  refine ⟨by nlinarith [sq_nonneg (x₁ - γ₁ w), sq_nonneg (x₂ - γ₂ w)], fun h => ?_⟩
  have h0 : (x₁ - γ₁ w) ^ 2 + (x₂ - γ₂ w) ^ 2 = 0 := by
    have : ε * ((x₁ - γ₁ w) ^ 2 + (x₂ - γ₂ w) ^ 2) = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_left hε.ne'
  have h1 : (x₁ - γ₁ w) ^ 2 = 0 := by nlinarith [sq_nonneg (x₁ - γ₁ w), sq_nonneg (x₂ - γ₂ w)]
  have h2 : (x₂ - γ₂ w) ^ 2 = 0 := by nlinarith [sq_nonneg (x₁ - γ₁ w), sq_nonneg (x₂ - γ₂ w)]
  exact ⟨by nlinarith [pow_eq_zero_iff (n := 2) (two_ne_zero) |>.1 h1],
    by nlinarith [pow_eq_zero_iff (n := 2) (two_ne_zero) |>.1 h2]⟩

end MWG.EquilibriumTime
