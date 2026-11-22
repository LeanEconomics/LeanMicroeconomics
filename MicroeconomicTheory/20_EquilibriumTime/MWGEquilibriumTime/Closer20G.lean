/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGEquilibriumTime.Several

/-!
# Several consumers: Pareto optima and marginal utilities of wealth (MWG Section 20.G)

MWG, Chapter 20, Exercise 20.G.2 (p. 785), footnote 32 (p. 768) and Exercise 20.G.4 (p. 786).

An exchange economy with consumers `i ∈ ι`, `L` goods per period, a common discount factor and
utilities `∑_t δ^t u_i(c_{it})`. A feasible allocation is Pareto optimal
(`ParetoOptimalExchange`) if no feasible allocation with convergent utility series makes every
consumer at least as well off and one strictly better off.

* **Exercise 20.G.2** (`exercise_20_G_2`): at an interior Pareto optimum with differentiable
  one-period utilities, for any two consumers `i ≠ j` the ratio
  `∂_ℓ u_i(c_{it}) / ∂_ℓ u_j(c_{jt})` is the same for every period `t` and every good `ℓ`
  (cross-multiplied). With strictly positive marginal utilities (`exercise_20_G_2_ratio`)
  there is `κ > 0` with
  `∇u_i(c_{it}) = κ ∇u_j(c_{jt})` for all `t`: measured in any common unit of account the
  in-period marginal utilities of wealth stand in a ratio independent of the period, so with the
  supporting prices `p_t = δ^t ∇u_j(c_{jt})` each consumer's in-period marginal utility of wealth
  is the same in every period. The proof is the perturbation argument: if the ratios differed,
  a two-date transfer between `i` and `j` would improve both to the first order.
* A proved instance of the Pareto optimality hypothesis (`paretoOptimalExchange_linear`): linear
  utilities with a common gradient, at any allocation exhausting the endowments.
* **Footnote 32 / Exercise 20.G.4**: with constant endowments, a common discount factor and no
  production, the intertemporal equilibria are exactly the constant repetitions of the static
  Walrasian equilibria (`StaticWalrasEq`, instance `staticWalrasEq_noTrade`), with price
  sequences `p_t = δ^t p̄`. The repetition of an interior static equilibrium is an equilibrium
  in the sense of Definition 20.G.1 (`exercise_20_G_4_repetition`, using the static first-order
  conditions `static_foc`); conversely, with strictly concave utilities every equilibrium
  satisfying the first-order conditions (20.D.6) with binding budgets has constant consumption,
  prices `δ^t p_0` and a static equilibrium at date 0 (`exercise_20_G_4_static`, via the strict
  gradient inequality `strictConcave_lt_fderiv`). The footnote's `L = 2`, `I = 2` is the special
  case `Fin 2`, `ι = Fin 2`.
-/

open Filter Topology

namespace MWG.EquilibriumTime

variable {L : ℕ} {ι : Type*} [Fintype ι]

/-- A **Pareto optimal** allocation of the exchange economy with aggregate endowments `ω`
(MWG, Section 20.G, Exercise 20.G.2): nonnegative, feasible, and not Pareto dominated by any
nonnegative feasible allocation whose utility series converge. -/
def ParetoOptimalExchange (δ : ℝ) (u : ι → (Fin L → ℝ) → ℝ) (ω : ℕ → Fin L → ℝ)
    (c : ι → ℕ → Fin L → ℝ) : Prop :=
  (∀ i t, 0 ≤ c i t) ∧ (∀ t, ∑ i, c i t ≤ ω t) ∧
    ¬ ∃ c' : ι → ℕ → Fin L → ℝ, (∀ i t, 0 ≤ c' i t) ∧ (∀ t, ∑ i, c' i t ≤ ω t) ∧
      (∀ i, Summable fun t => δ ^ t * u i (c' i t)) ∧
      (∀ i, discountedUtility δ (u i) (c i) ≤ discountedUtility δ (u i) (c' i)) ∧
      ∃ j, discountedUtility δ (u j) (c j) < discountedUtility δ (u j) (c' j)

/-- Changing a stream at finitely many dates changes discounted utility by the finite sum of
the discounted one-period changes. -/
theorem discountedUtility_finite_change {δ : ℝ} {u : (Fin L → ℝ) → ℝ} {c c' : ℕ → Fin L → ℝ}
    {N : ℕ} (hcc : ∀ τ, N ≤ τ → c' τ = c τ) (hs : Summable fun t => δ ^ t * u (c t)) :
    Summable (fun t => δ ^ t * u (c' t)) ∧ discountedUtility δ u c' =
      discountedUtility δ u c + ∑ τ ∈ Finset.range N, δ ^ τ * (u (c' τ) - u (c τ)) := by
  set h : ℕ → ℝ := fun τ => δ ^ τ * (u (c' τ) - u (c τ)) with hh
  have hzero : ∀ τ ∉ Finset.range N, h τ = 0 := fun τ hτ => by
    simp only [Finset.mem_range, not_lt] at hτ
    simp [hh, hcc τ hτ]
  have hsh : Summable h := summable_of_ne_finset_zero hzero
  have heq : (fun t => δ ^ t * u (c' t)) = fun t => δ ^ t * u (c t) + h t := by
    funext t; simp only [hh]; ring
  refine ⟨heq ▸ hs.add hsh, ?_⟩
  unfold discountedUtility
  rw [heq, hs.tsum_add hsh, tsum_eq_sum hzero]

/-- The core of Exercise 20.G.2: at an interior Pareto optimum,
`∂_ℓ u_j(c_{jt}) ∂_{ℓ'} u_i(c_{it'}) ≥ ∂_ℓ u_i(c_{it}) ∂_{ℓ'} u_j(c_{jt'})` fails to be strict
in the other direction: otherwise a transfer from `j` to `i` of good `ℓ` at `t` against good `ℓ'`
at `t'` raises both utilities. -/
theorem pareto_ratio_core {δ : ℝ} (hδ : 0 < δ) {u : ι → (Fin L → ℝ) → ℝ}
    {ω : ℕ → Fin L → ℝ} {c : ι → ℕ → Fin L → ℝ} (hpo : ParetoOptimalExchange δ u ω c)
    (hs : ∀ i, Summable fun t => δ ^ t * u i (c i t)) (hint : ∀ i t l, 0 < c i t l)
    {D : ι → ℕ → (Fin L → ℝ) →L[ℝ] ℝ} (hD : ∀ i t, HasFDerivAt (u i) (D i t) (c i t))
    {i j : ι} (hij : i ≠ j) (t t' : ℕ) (l l' : Fin L) :
    ¬ D j t (Pi.single l 1) * D i t' (Pi.single l' 1)
      < D i t (Pi.single l 1) * D j t' (Pi.single l' 1) := by
  classical
  intro hlt
  obtain ⟨hc0, hfeas, hno⟩ := hpo
  set ai := δ ^ t * D i t (Pi.single l 1) with hai
  set aj := δ ^ t * D j t (Pi.single l 1) with haj
  set bi := δ ^ t' * D i t' (Pi.single l' 1) with hbi
  set bj := δ ^ t' * D j t' (Pi.single l' 1) with hbj
  have hgap : 0 < ai * bj - aj * bi := by
    have : ai * bj - aj * bi = δ ^ t * δ ^ t' * (D i t (Pi.single l 1) * D j t' (Pi.single l' 1)
        - D j t (Pi.single l 1) * D i t' (Pi.single l' 1)) := by
      simp only [hai, haj, hbi, hbj]; ring
    rw [this]
    exact mul_pos (mul_pos (pow_pos hδ t) (pow_pos hδ t')) (by linarith)
  set x := bi + bj with hx
  set y := ai + aj with hy
  -- the transfer: consumer `i` gains `x` of good `l` at `t` and loses `y` of good `l'` at `t'`
  set v : ℕ → Fin L → ℝ := fun τ =>
    (if τ = t then x • Pi.single l 1 else 0) - (if τ = t' then y • Pi.single l' 1 else 0) with hv
  set κ : ι → ℝ := Pi.single i 1 - Pi.single j 1 with hκ
  have hκsum : ∑ k, κ k = 0 := by simp [hκ, Finset.sum_sub_distrib]
  have hκi : κ i = 1 := by simp [hκ, hij]
  have hκj : κ j = -1 := by simp [hκ, Ne.symm hij]
  set N := max t t' + 1 with hN
  have htN : t ∈ Finset.range N := Finset.mem_range.2 (by omega)
  have ht'N : t' ∈ Finset.range N := Finset.mem_range.2 (by omega)
  have hvN : ∀ τ, N ≤ τ → v τ = 0 := fun τ hτ => by
    simp [hv, show τ ≠ t by omega, show τ ≠ t' by omega]
  -- the utility gain of consumer `k` as a function of the size `s` of the transfer
  set φ : ι → ℝ → ℝ := fun k s =>
    ∑ τ ∈ Finset.range N, δ ^ τ * (u k (c k τ + (s * κ k) • v τ) - u k (c k τ)) with hφ
  have hderiv : ∀ k, HasDerivAt (φ k)
      (∑ τ ∈ Finset.range N, δ ^ τ * D k τ (κ k • v τ)) 0 := by
    intro k
    have hterm : ∀ τ ∈ Finset.range N, HasDerivAt
        (fun s : ℝ => δ ^ τ * (u k (c k τ + (s * κ k) • v τ) - u k (c k τ)))
        (δ ^ τ * D k τ (κ k • v τ)) 0 := fun τ _ => by
      have hline : HasDerivAt (fun s : ℝ => c k τ + (s * κ k) • v τ) (κ k • v τ) 0 := by
        have := ((hasDerivAt_id (0 : ℝ)).mul_const (κ k)).smul_const (v τ)
        simpa using this.const_add (c k τ)
      have hc := (hD k τ).comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
      exact (hc.sub_const (u k (c k τ))).const_mul (δ ^ τ)
    convert HasDerivAt.sum hterm using 1
    funext s
    simp only [hφ, Finset.sum_apply]
  have hDv : ∀ k, ∑ τ ∈ Finset.range N, δ ^ τ * D k τ (κ k • v τ)
      = κ k * (x * (δ ^ t * D k t (Pi.single l 1)) - y * (δ ^ t' * D k t' (Pi.single l' 1))) := by
    intro k
    have e : ∀ τ, δ ^ τ * D k τ (κ k • v τ) =
        κ k * ((if τ = t then x * (δ ^ t * D k t (Pi.single l 1)) else 0) -
          (if τ = t' then y * (δ ^ t' * D k t' (Pi.single l' 1)) else 0)) := fun τ => by
      simp only [hv, map_smul, map_sub, smul_eq_mul]
      split_ifs with h1 h2 h2 <;> subst_vars <;> simp <;> ring
    rw [Finset.sum_congr rfl fun τ _ => e τ, ← Finset.mul_sum, Finset.sum_sub_distrib,
      Finset.sum_ite_eq' _ _ _, Finset.sum_ite_eq' _ _ _]
    simp only [htN, ht'N, ↓reduceIte]
  have hφ0 : ∀ k, φ k 0 = 0 := fun k => by simp [hφ]
  -- both `i` and `j` gain to the first order
  have hdi : 0 < ∑ τ ∈ Finset.range N, δ ^ τ * D i τ (κ i • v τ) := by
    rw [hDv i, hκi, one_mul, ← hai, ← hbi, hx, hy]; nlinarith
  have hdj : 0 < ∑ τ ∈ Finset.range N, δ ^ τ * D j τ (κ j • v τ) := by
    rw [hDv j, hκj, ← haj, ← hbj, hx, hy]; nlinarith
  have hevi := eventually_pos_of_hasDerivAt (hderiv i) (hφ0 i) hdi
  have hevj := eventually_pos_of_hasDerivAt (hderiv j) (hφ0 j) hdj
  -- the perturbed allocation stays nonnegative for small `s`
  have hnn : ∀ τ, ∀ᶠ s in 𝓝 (0 : ℝ), ∀ k l₀, 0 ≤ c k τ l₀ + (s * κ k) * v τ l₀ := by
    intro τ
    rw [eventually_all]; intro k
    rw [eventually_all]; intro l₀
    have hcont : Continuous fun s : ℝ => c k τ l₀ + (s * κ k) * v τ l₀ := by fun_prop
    exact (hcont.continuousAt.eventually (lt_mem_nhds (by simpa using hint k τ l₀))).mono
      fun _ h => h.le
  have hnn' : ∀ᶠ s in 𝓝[>] (0 : ℝ), (∀ k l₀, 0 ≤ c k t l₀ + (s * κ k) * v t l₀) ∧
      ∀ k l₀, 0 ≤ c k t' l₀ + (s * κ k) * v t' l₀ :=
    nhdsWithin_le_nhds ((hnn t).and (hnn t'))
  obtain ⟨s, ⟨hφi, hφj⟩, hnt, hnt'⟩ := ((hevi.and hevj).and hnn').exists
  set c' : ι → ℕ → Fin L → ℝ := fun k τ => c k τ + (s * κ k) • v τ with hc'
  have hchg : ∀ k τ, N ≤ τ → c' k τ = c k τ := fun k τ hτ => by simp [hc', hvN τ hτ]
  have hfc : ∀ k, Summable (fun τ => δ ^ τ * u k (c' k τ)) ∧ discountedUtility δ (u k) (c' k) =
      discountedUtility δ (u k) (c k) + φ k s := fun k =>
    discountedUtility_finite_change (hchg k) (hs k)
  refine hno ⟨c', fun k τ l₀ => ?_, fun τ => ?_, fun k => (hfc k).1, fun k => ?_, i, ?_⟩
  · simp only [hc', Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    by_cases h1 : τ = t
    · subst h1; exact hnt k l₀
    by_cases h2 : τ = t'
    · subst h2; exact hnt' k l₀
    simp only [hv, h1, h2, ↓reduceIte, sub_self, Pi.zero_apply, mul_zero, add_zero]
    exact hc0 k τ l₀
  · have : ∑ k, c' k τ = ∑ k, c k τ := by
      simp only [hc', Finset.sum_add_distrib, mul_smul]
      simp [← Finset.sum_smul, ← smul_assoc, hκsum, ← Finset.mul_sum]
    rw [this]; exact hfeas τ
  · rw [(hfc k).2]
    by_cases hk1 : k = i
    · subst hk1; linarith
    by_cases hk2 : k = j
    · subst hk2; linarith
    have : κ k = 0 := by simp [hκ, hk1, hk2]
    have : φ k s = 0 := by simp [hφ, this]
    linarith
  · rw [(hfc i).2]; linarith

/-- **Exercise 20.G.2** (MWG, p. 785): at an interior Pareto optimum of the exchange economy
(common discount factor `0 < δ`, differentiable one-period utilities, convergent utility
series), for any two consumers `i ≠ j`, all periods
`t, t'` and goods `ℓ, ℓ'`,
`∂_ℓ u_i(c_{it}) ∂_{ℓ'} u_j(c_{jt'}) = ∂_ℓ u_j(c_{jt}) ∂_{ℓ'} u_i(c_{it'})`. -/
theorem exercise_20_G_2 {δ : ℝ} (hδ : 0 < δ) {u : ι → (Fin L → ℝ) → ℝ}
    {ω : ℕ → Fin L → ℝ} {c : ι → ℕ → Fin L → ℝ} (hpo : ParetoOptimalExchange δ u ω c)
    (hs : ∀ i, Summable fun t => δ ^ t * u i (c i t)) (hint : ∀ i t l, 0 < c i t l)
    {D : ι → ℕ → (Fin L → ℝ) →L[ℝ] ℝ} (hD : ∀ i t, HasFDerivAt (u i) (D i t) (c i t))
    {i j : ι} (hij : i ≠ j) (t t' : ℕ) (l l' : Fin L) :
    D i t (Pi.single l 1) * D j t' (Pi.single l' 1)
      = D j t (Pi.single l 1) * D i t' (Pi.single l' 1) := by
  rcases lt_trichotomy (D j t (Pi.single l 1) * D i t' (Pi.single l' 1))
    (D i t (Pi.single l 1) * D j t' (Pi.single l' 1)) with h | h | h
  · exact absurd h (pareto_ratio_core hδ hpo hs hint hD hij t t' l l')
  · exact h.symm
  · exact absurd h (pareto_ratio_core hδ hpo hs hint hD (Ne.symm hij) t t' l l')

/-- **Exercise 20.G.2**, ratio form (MWG, p. 785): with `L ≥ 1`, there is `κ > 0` such that
`∇u_i(c_{it}) = κ ∇u_j(c_{jt})` in every period `t`. With the supporting prices
`p_t = δ^t ∇u_j(c_{jt})` the first-order conditions `δ^t ∇u_i(c_{it}) = λ_{it} p_t` hold with
`λ_{it} = κ` and `λ_{jt} = 1` for all `t`: each consumer's in-period marginal utility of wealth is
the same in every period. -/
theorem exercise_20_G_2_ratio [NeZero L] {δ : ℝ} (hδ : 0 < δ)
    {u : ι → (Fin L → ℝ) → ℝ} {ω : ℕ → Fin L → ℝ} {c : ι → ℕ → Fin L → ℝ}
    (hpo : ParetoOptimalExchange δ u ω c) (hs : ∀ i, Summable fun t => δ ^ t * u i (c i t))
    (hint : ∀ i t l, 0 < c i t l) {D : ι → ℕ → (Fin L → ℝ) →L[ℝ] ℝ}
    (hD : ∀ i t, HasFDerivAt (u i) (D i t) (c i t)) (hpos : ∀ i t l, 0 < D i t (Pi.single l 1))
    {i j : ι} (hij : i ≠ j) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ t, D i t = κ • D j t := by
  set κ := D i 0 (Pi.single 0 1) / D j 0 (Pi.single 0 1) with hκ
  refine ⟨κ, div_pos (hpos i 0 0) (hpos j 0 0), fun t => ?_⟩
  refine ContinuousLinearMap.ext fun z => ?_
  change D i t z = κ • D j t z
  have hz : z = ∑ l, z l • (Pi.single l (1 : ℝ) : Fin L → ℝ) := by
    funext m; simp [Finset.sum_apply, Pi.single_apply]
  rw [hz]
  simp only [map_sum, map_smul, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  have e := exercise_20_G_2 hδ hpo hs hint hD hij t 0 l 0
  have hj0 := hpos j 0 0
  rw [hκ, div_mul_eq_mul_div, eq_div_iff hj0.ne']
  linear_combination (z l) * e

/-- A proved instance of `ParetoOptimalExchange`: if every consumer has the linear one-period
utility `u_i(x) = ∑_ℓ x_ℓ`, `0 ≤ δ < 1` and the aggregate endowment is bounded, any nonnegative
allocation with `∑_i c_{it} = ω_t` is Pareto optimal. -/
theorem paretoOptimalExchange_linear {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    {ω : ℕ → Fin L → ℝ} {B : ℝ} (hωB : ∀ t l, ω t l ≤ B) {c : ι → ℕ → Fin L → ℝ}
    (hc0 : ∀ i t, 0 ≤ c i t) (hcω : ∀ t, ∑ i, c i t = ω t) :
    ParetoOptimalExchange δ (fun _ x => ∑ l, x l) ω c := by
  refine ⟨hc0, fun t => (hcω t).le, ?_⟩
  rintro ⟨c', hc'0, hfeas', hs', hge, j, hj⟩
  -- total utility is bounded by the discounted value of the endowments
  have hbd : ∀ (d : ι → ℕ → Fin L → ℝ), (∀ i t, 0 ≤ d i t) → (∀ t, ∑ i, d i t ≤ ω t) →
      ∀ i t, |δ ^ t * ∑ l, d i t l| ≤ δ ^ t * (Fintype.card (Fin L) * B) := by
    intro d hd hdω i t
    have hδt := pow_nonneg hδ0 t
    rw [abs_mul, abs_of_nonneg hδt]
    refine mul_le_mul_of_nonneg_left ?_ hδt
    rw [abs_of_nonneg (Finset.sum_nonneg fun l _ => hd i t l)]
    calc ∑ l, d i t l ≤ ∑ l, ω t l := Finset.sum_le_sum fun l _ =>
            (Finset.single_le_sum (fun k _ => hd k t l) (Finset.mem_univ i)).trans
              (by simpa [Finset.sum_apply] using hdω t l)
      _ ≤ ∑ _l : Fin L, B := Finset.sum_le_sum fun l _ => hωB t l
      _ = Fintype.card (Fin L) * B := by simp
  have hgeo : Summable fun t => δ ^ t * (Fintype.card (Fin L) * B) :=
    (summable_geometric_of_lt_one hδ0 hδ1).mul_right _
  have hsc : ∀ i, Summable fun t => δ ^ t * ∑ l, c i t l := fun i =>
    Summable.of_norm_bounded hgeo fun t =>
      hbd c hc0 (fun t => (hcω t).le) i t
  -- the sums over consumers
  have htot : ∑ i, discountedUtility δ (fun x => ∑ l, x l) (c' i)
      ≤ ∑ i, discountedUtility δ (fun x => ∑ l, x l) (c i) := by
    unfold discountedUtility
    rw [← Summable.tsum_finsetSum fun i _ => hs' i, ← Summable.tsum_finsetSum fun i _ => hsc i]
    refine Summable.tsum_le_tsum (fun t => ?_) (summable_sum fun i _ => hs' i)
      (summable_sum fun i _ => hsc i)
    simp only [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hδ0 t)
    rw [Finset.sum_comm, Finset.sum_comm (f := fun i l => c i t l)]
    refine Finset.sum_le_sum fun l _ => ?_
    have h1 := hfeas' t l
    have h2 := congrFun (hcω t) l
    simp only [Finset.sum_apply] at h1 h2
    linarith
  have hlt : ∑ i, discountedUtility δ (fun x => ∑ l, x l) (c i)
      < ∑ i, discountedUtility δ (fun x => ∑ l, x l) (c' i) :=
    Finset.sum_lt_sum (fun i _ => hge i) ⟨j, Finset.mem_univ j, hj⟩
  linarith

/-! ### Footnote 32 and Exercise 20.G.4: repetitions of static equilibria -/

/-- The **strict gradient inequality**: for `u` strictly concave on a convex set `S` and
differentiable at `x ∈ S`, `u(y) < u(x) + Du(x)(y - x)` for every `y ∈ S`, `y ≠ x`. -/
theorem strictConcave_lt_fderiv {S : Set (Fin L → ℝ)} {f : (Fin L → ℝ) → ℝ}
    {f' : (Fin L → ℝ) →L[ℝ] ℝ} {x y : Fin L → ℝ} (hfc : StrictConcaveOn ℝ S f) (hx : x ∈ S)
    (hy : y ∈ S) (hxy : x ≠ y) (hf : HasFDerivAt f f' x) : f y < f x + f' (y - x) := by
  set m : Fin L → ℝ := (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y with hm
  have hmS : m ∈ S := hfc.1 hx hy (by norm_num) (by norm_num) (by norm_num)
  have hlt := hfc.2 hx hy hxy (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num)
  have hle := MWG.GeneralEquilibriumExamples.concave_le_fderiv hfc.concaveOn hx hmS hf
  have hmx : m - x = (1 / 2 : ℝ) • (y - x) := by
    simp only [hm, smul_sub]; module
  rw [hmx, map_smul, smul_eq_mul] at hle
  simp only [smul_eq_mul] at hlt
  linarith

/-- A **static (one-period) Walrasian equilibrium** of the exchange economy with endowments
`ω_i` (MWG, footnote 32): consumption bundles `x_i ≥ 0` in the budget sets of the prices `p̄`,
maximizing `u_i` there, and clearing the markets. -/
def StaticWalrasEq (u : ι → (Fin L → ℝ) → ℝ) (ω : ι → Fin L → ℝ) (pbar : Fin L → ℝ)
    (x : ι → Fin L → ℝ) : Prop :=
  (∀ i, 0 ≤ x i) ∧ (∀ i, pbar ⬝ᵥ x i ≤ pbar ⬝ᵥ ω i) ∧
    (∀ i z, 0 ≤ z → pbar ⬝ᵥ z ≤ pbar ⬝ᵥ ω i → u i z ≤ u i (x i)) ∧ ∑ i, x i = ∑ i, ω i

/-- A proved instance of `StaticWalrasEq`: one good, utilities `u_i(z) = z`, price `1`, no
trade. -/
theorem staticWalrasEq_noTrade (ω : ι → Fin 1 → ℝ) (hω : ∀ i, 0 ≤ ω i) :
    StaticWalrasEq (fun _ z => z 0) ω (fun _ => 1) ω := by
  refine ⟨hω, fun i => le_rfl, fun i z _ hz => ?_, rfl⟩
  simpa [dotProduct] using hz

/-- **First-order conditions of a static optimum**: if an interior bundle `x ≫ 0` maximizes `u`
on `{z ≥ 0 : p̄ · z ≤ p̄ · ω}` with `p̄ ≫ 0` and `u` is differentiable at `x`, then
`Du(x) = λ p̄` with `λ = ∂_0 u(x) / p̄_0`; if moreover `∂_0 u(x) > 0`, the budget binds. -/
theorem static_foc [NeZero L] {u : (Fin L → ℝ) → ℝ} {pbar ω x : Fin L → ℝ}
    (hp : ∀ l, 0 < pbar l) (hx : ∀ l, 0 < x l) (hxb : pbar ⬝ᵥ x ≤ pbar ⬝ᵥ ω)
    (hmax : ∀ z, 0 ≤ z → pbar ⬝ᵥ z ≤ pbar ⬝ᵥ ω → u z ≤ u x) {D : (Fin L → ℝ) →L[ℝ] ℝ}
    (hD : HasFDerivAt u D x) :
    (∀ v, D v = D (Pi.single 0 1) / pbar 0 * (pbar ⬝ᵥ v)) ∧
      (0 < D (Pi.single 0 1) → pbar ⬝ᵥ x = pbar ⬝ᵥ ω) := by
  have hcomp : ∀ l, D (Pi.single l 1) * pbar 0 = pbar l * D (Pi.single 0 1) := by
    intro l
    set v : Fin L → ℝ := pbar 0 • Pi.single l 1 - pbar l • Pi.single 0 1 with hv
    have hpv : pbar ⬝ᵥ v = 0 := by
      simp only [hv, dotProduct_sub, dotProduct_smul, smul_eq_mul]
      simp [dotProduct, Pi.single_apply]
      ring
    have hline : HasDerivAt (fun s : ℝ => x + s • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
    have hd := hD.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
    have hloc : IsLocalMax (fun s : ℝ => u (x + s • v)) 0 := by
      have hnn : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ k, 0 ≤ x k + s * v k := by
        rw [eventually_all]; intro k
        have hcont : Continuous fun s : ℝ => x k + s * v k := by fun_prop
        exact (hcont.continuousAt.eventually (lt_mem_nhds (by simpa using hx k))).mono
          fun _ h => h.le
      filter_upwards [hnn] with s hs
      simp only [zero_smul, add_zero]
      refine hmax (x + s • v) (fun k => by simpa using hs k) ?_
      simpa [dotProduct_add, dotProduct_smul, hpv] using hxb
    have := hloc.hasDerivAt_eq_zero hd
    simp only [hv, map_sub, map_smul, smul_eq_mul] at this
    linarith
  refine ⟨fun v => ?_, fun hD0 => ?_⟩
  · rw [clm_apply_eq_sum D v]
    simp only [dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    have := hcomp l
    have hp0 := hp 0
    field_simp
    linear_combination (v l) * this
  · refine le_antisymm hxb (not_lt.1 fun hlt => ?_)
    have hline : HasDerivAt (fun s : ℝ => x + s • Pi.single 0 1) (Pi.single 0 1) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single 0 (1 : ℝ))).const_add x
    have hd := (hD.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)).sub_const (u x)
    have hev := eventually_pos_of_hasDerivAt hd (by simp) hD0
    have hsmall : ∀ᶠ s in 𝓝[>] (0 : ℝ), s * pbar 0 < pbar ⬝ᵥ ω - pbar ⬝ᵥ x :=
      nhdsWithin_le_nhds ((continuous_id.mul continuous_const).continuousAt.eventually
        (gt_mem_nhds (by simpa using sub_pos.2 hlt)))
    obtain ⟨s, hs1, hs2, hs3⟩ := (hev.and (hsmall.and self_mem_nhdsWithin)).exists
    have hz : 0 ≤ x + s • Pi.single 0 (1 : ℝ) := fun k => by
      have := hx k
      have : 0 ≤ s * (Pi.single 0 (1 : ℝ) : Fin L → ℝ) k := by
        rw [Pi.single_apply]; split_ifs <;> simp [hs3.le]
      simpa using by linarith
    have hb : pbar ⬝ᵥ (x + s • Pi.single 0 1) ≤ pbar ⬝ᵥ ω := by
      simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, dotProduct_single, mul_one]
      linarith
    have := hmax _ hz hb
    simp only [Function.comp_apply] at hs1
    linarith

/-- **Footnote 32 and Exercise 20.G.4**, from static to intertemporal (MWG, p. 768, p. 786):
in an exchange economy with constant endowments `ω_i`, common discount factor `0 < δ < 1` and
concave utilities, the infinite constant repetition of an interior static Walrasian
equilibrium `(p̄, x)` (with `p̄ ≫ 0`, differentiable `u_i` and `∂_0 u_i(x_i) > 0`) is a Walrasian
equilibrium (Definition 20.G.1, with the null technology `Y = {0}` and any shares) with price
sequence `p_t = δ^t p̄`. -/
theorem exercise_20_G_4_repetition [NeZero L] {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    {u : ι → (Fin L → ℝ) → ℝ} (hconc : ∀ i, ConcaveOn ℝ (Set.Ici 0) (u i))
    {ω : ι → Fin L → ℝ} (hω : ∀ i, 0 ≤ ω i) {pbar : Fin L → ℝ} {x : ι → Fin L → ℝ}
    (he : StaticWalrasEq u ω pbar x) (hp : ∀ l, 0 < pbar l) (hx : ∀ i l, 0 < x i l)
    {D : ι → (Fin L → ℝ) →L[ℝ] ℝ} (hD : ∀ i, HasFDerivAt (u i) (D i) (x i))
    (hD0 : ∀ i, 0 < D i (Pi.single 0 1)) (θ : ι → ℕ → ℝ) :
    WalrasEqI (Set.Ici 0) {0} δ u (fun i _ => ω i) θ (fun t => δ ^ t • pbar) (fun _ => 0)
      (fun i _ => x i) := by
  obtain ⟨hx0, hbx, hmax, hclear⟩ := he
  have hδt : ∀ t, 0 ≤ δ ^ t := fun t => pow_nonneg hδ0.le t
  have hgeo := summable_geometric_of_lt_one hδ0.le hδ1
  have hpω : ∀ i, 0 ≤ pbar ⬝ᵥ ω i := fun i =>
    dotProduct_nonneg_of_nonneg (fun l => (hp l).le) (hω i)
  refine ⟨⟨0, fun t l => by simp⟩, ⟨∑ l, |pbar l|, fun t l => ?_⟩, fun t l => ?_, fun t => ?_,
    ⟨fun t => rfl, fun t z hz => ?_⟩, ?_, fun i => ?_, fun i => ?_⟩
  · rw [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg (hδt t)]
    calc δ ^ t * |pbar l| ≤ 1 * |pbar l| :=
          mul_le_mul_of_nonneg_right (pow_le_one₀ hδ0.le hδ1.le) (abs_nonneg _)
      _ ≤ ∑ l, |pbar l| := by
          rw [one_mul]
          exact Finset.single_le_sum (fun k _ => abs_nonneg (pbar k)) (Finset.mem_univ l)
  · simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    exact mul_nonneg (hδt t) (hp l).le
  · rcases t with _ | t <;> simp [netOutput, hclear]
  · rw [Set.mem_singleton_iff.1 hz]; simp [planValue, periodProfit]
  · have : periodProfit (fun t => δ ^ t • pbar) (fun _ => (0 : ProdPlan (Fin L))) = fun _ => 0 :=
      funext fun t => by simp [periodProfit, planValue]
    rw [this]; exact summable_zero
  · simpa [smul_dotProduct, smul_eq_mul] using hgeo.mul_right (pbar ⬝ᵥ ω i)
  -- utility maximization
  obtain ⟨hlamD, hbind⟩ := static_foc hp (hx i) (hbx i) (hmax i) (hD i)
  have hbx' := hbind (hD0 i)
  set lam := D i (Pi.single 0 1) / pbar 0 with hlam
  have hlam0 : 0 < lam := div_pos (hD0 i) (hp 0)
  have hW : (∑' t, θ i t * periodProfit (fun t => δ ^ t • pbar) (fun _ => 0) t
      + ∑' t, (δ ^ t • pbar) ⬝ᵥ ω i) = ∑' t, δ ^ t * (pbar ⬝ᵥ x i) := by
    simp [periodProfit, planValue, smul_dotProduct, hbx']
  rw [hW]
  have hsx : Summable fun t => δ ^ t * (pbar ⬝ᵥ x i) := hgeo.mul_right _
  refine ⟨⟨fun t => hx0 i, ⟨∑ l, |x i l|, fun t l =>
    Finset.single_le_sum (fun k _ => abs_nonneg (x i k)) (Finset.mem_univ l)⟩, fun T => ?_⟩,
    hgeo.mul_right _, fun c' hc' hs' => ?_⟩
  · simp only [smul_dotProduct, smul_eq_mul]
    exact hsx.sum_le_tsum _ fun t _ =>
      mul_nonneg (hδt t) (dotProduct_nonneg_of_nonneg (fun l => (hp l).le) (hx0 i))
  obtain ⟨hcs, hcle⟩ := expenditure_summable (p := fun t => δ ^ t • pbar)
    (fun t l => mul_nonneg (hδt t) (hp l).le) (fun t => hc'.1 t) hc'.2.2
  have hpt : ∀ t, δ ^ t * u i (c' t) ≤ δ ^ t * u i (x i)
      + lam * ((δ ^ t • pbar) ⬝ᵥ c' t) - lam * (δ ^ t * (pbar ⬝ᵥ x i)) := by
    intro t
    have g := MWG.GeneralEquilibriumExamples.concave_le_fderiv (hconc i)
      (show x i ∈ Set.Ici 0 from hx0 i) (hc'.1 t) (hD i)
    rw [hlamD, dotProduct_sub] at g
    rw [smul_dotProduct, smul_eq_mul]
    nlinarith [hδt t]
  have hsR : Summable fun t => δ ^ t * u i (x i)
      + lam * ((δ ^ t • pbar) ⬝ᵥ c' t) - lam * (δ ^ t * (pbar ⬝ᵥ x i)) :=
    ((hgeo.mul_right _).add (hcs.mul_left lam)).sub (hsx.mul_left lam)
  unfold discountedUtility
  calc ∑' t, δ ^ t * u i (c' t) ≤ ∑' t, (δ ^ t * u i (x i)
        + lam * ((δ ^ t • pbar) ⬝ᵥ c' t) - lam * (δ ^ t * (pbar ⬝ᵥ x i))) :=
        Summable.tsum_le_tsum hpt hs' hsR
    _ = ∑' t, δ ^ t * u i (x i) + lam * ∑' t, (δ ^ t • pbar) ⬝ᵥ c' t
        - lam * ∑' t, δ ^ t * (pbar ⬝ᵥ x i) := by
        rw [((hgeo.mul_right _).add (hcs.mul_left lam)).tsum_sub (hsx.mul_left lam),
          (hgeo.mul_right _).tsum_add (hcs.mul_left lam), tsum_mul_left, tsum_mul_left]
    _ ≤ ∑' t, δ ^ t * u i (x i) := by nlinarith

/-- **Footnote 32 and Exercise 20.G.4**, from intertemporal to static (MWG, p. 768, p. 786):
in an exchange economy with constant endowments `ω_i`, common discount factor `0 < δ < 1` and
strictly concave differentiable utilities, at an equilibrium whose consumptions satisfy the
first-order conditions (20.D.6) `λ_i p_t = δ^t ∇u_i(c_{it})` (Exercise 20.D.3) and exhaust the
budgets, consumption is constant over time, the price sequence is `p_t = δ^t p_0` (the rate of
interest is `(1 - δ)/δ` in every period), and `(p_0, (c_{i0})_i)` is a static Walrasian
equilibrium. Constancy: `∑_i λ_i⁻¹ (∇u_i(c_{it}) - ∇u_i(c_{i0})) · (c_{i0} - c_{it})` vanishes by
market clearing, while each term is positive unless `c_{it} = c_{i0}`. -/
theorem exercise_20_G_4_static [Nonempty ι] {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    {u : ι → (Fin L → ℝ) → ℝ} (hconc : ∀ i, StrictConcaveOn ℝ (Set.Ici 0) (u i))
    {ω : ι → Fin L → ℝ} {c : ι → ℕ → Fin L → ℝ} (hc0 : ∀ i t, 0 ≤ c i t)
    {D : ι → ℕ → (Fin L → ℝ) →L[ℝ] ℝ} (hD : ∀ i t, HasFDerivAt (u i) (D i t) (c i t))
    {p : ℕ → Fin L → ℝ} (hfoc : ∀ i, Foc20D6 δ p (D i))
    (hfeas : ∀ t, ∑ i, c i t = ∑ i, ω i)
    (hbud : ∀ i, HasSum (fun t => p t ⬝ᵥ c i t) (∑' t, p t ⬝ᵥ ω i)) :
    (∀ i t, c i t = c i 0) ∧ (∀ t, p t = δ ^ t • p 0) ∧
      StaticWalrasEq u ω (p 0) (fun i => c i 0) := by
  choose lam hlam hlamD using hfoc
  have hδt : ∀ t, 0 < δ ^ t := fun t => pow_pos hδ0 t
  have hDp : ∀ i t v, D i t v = lam i * (p t ⬝ᵥ v) / δ ^ t := fun i t v => by
    rw [hlamD i t v]; field_simp
  -- constancy of consumption
  have hconst : ∀ i t, c i t = c i 0 := by
    intro i₀ t
    set g : ι → ℝ := fun i => (lam i)⁻¹ * (D i t (c i 0 - c i t) + D i 0 (c i t - c i 0))
      with hg
    have hgnn : ∀ i, 0 ≤ g i ∧ (c i t ≠ c i 0 → 0 < g i) := by
      intro i
      have hpos : c i t ≠ c i 0 → 0 < D i t (c i 0 - c i t) + D i 0 (c i t - c i 0) := by
        intro hne
        have h1 := strictConcave_lt_fderiv (hconc i) (show c i t ∈ Set.Ici 0 from hc0 i t)
          (show c i 0 ∈ Set.Ici 0 from hc0 i 0) hne (hD i t)
        have h2 := strictConcave_lt_fderiv (hconc i) (show c i 0 ∈ Set.Ici 0 from hc0 i 0)
          (show c i t ∈ Set.Ici 0 from hc0 i t) (Ne.symm hne) (hD i 0)
        linarith
      have hli := inv_pos.2 (hlam i)
      refine ⟨?_, fun hne => mul_pos hli (hpos hne)⟩
      by_cases hne : c i t = c i 0
      · simp [hg, hne]
      · exact (mul_pos hli (hpos hne)).le
    have hsum : ∑ i, g i = 0 := by
      have e : ∀ i, g i = (p t ⬝ᵥ (c i 0 - c i t)) / δ ^ t + p 0 ⬝ᵥ (c i t - c i 0) := by
        intro i
        simp only [hg, hDp, pow_zero, div_one]
        field_simp [(hlam i).ne']
      simp only [e, Finset.sum_add_distrib, ← Finset.sum_div, ← dotProduct_sum,
        Finset.sum_sub_distrib, hfeas, sub_self, dotProduct_zero, zero_div, add_zero]
    have hall := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => (hgnn i).1).1 hsum i₀
      (Finset.mem_univ _)
    by_contra hne
    exact (hgnn i₀).2 hne |>.ne' hall
  -- proportional prices
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hDconst : ∀ i t, D i t = D i 0 := fun i t =>
    (hD i t).unique (by rw [hconst i t]; exact hD i 0)
  have hprice : ∀ t, p t = δ ^ t • p 0 := by
    intro t
    funext l
    have a := hlamD i₀ t (Pi.single l 1)
    have b := hlamD i₀ 0 (Pi.single l 1)
    rw [hDconst i₀ t] at a
    simp only [dotProduct_single, mul_one, pow_zero, one_mul] at a b
    simp only [Pi.smul_apply, smul_eq_mul]
    have : lam i₀ * p t l = lam i₀ * (δ ^ t * p 0 l) := by rw [a, ← b]; ring
    exact mul_left_cancel₀ (hlam i₀).ne' this
  refine ⟨hconst, hprice, fun i => hc0 i 0, fun i => ?_, fun i z hz hzb => ?_, hfeas 0⟩
  -- the static budget binds
  · have hgeo := hasSum_geometric_of_lt_one hδ0.le hδ1
    have h1 : HasSum (fun t => p t ⬝ᵥ c i t) (p 0 ⬝ᵥ c i 0 * (1 - δ)⁻¹) :=
      (hgeo.mul_left (p 0 ⬝ᵥ c i 0)).congr_fun fun t => by
        rw [hprice t, hconst i t, smul_dotProduct, smul_eq_mul]; ring
    have h2 : ∑' t, p t ⬝ᵥ ω i = p 0 ⬝ᵥ ω i * (1 - δ)⁻¹ :=
      ((hgeo.mul_left (p 0 ⬝ᵥ ω i)).congr_fun fun t => by
        rw [hprice t, smul_dotProduct, smul_eq_mul]; ring).tsum_eq
    have := (hbud i).unique h1
    rw [h2] at this
    have hinv : 0 < (1 - δ)⁻¹ := inv_pos.2 (by linarith)
    have := mul_right_cancel₀ hinv.ne' this
    exact this.symm.le
  -- static optimality
  · have g := MWG.GeneralEquilibriumExamples.concave_le_fderiv (hconc i).concaveOn
      (show c i 0 ∈ Set.Ici 0 from hc0 i 0) (show z ∈ Set.Ici 0 from hz) (hD i 0)
    have hb : p 0 ⬝ᵥ c i 0 = p 0 ⬝ᵥ ω i := by
      have hgeo := hasSum_geometric_of_lt_one hδ0.le hδ1
      have h1 : HasSum (fun t => p t ⬝ᵥ c i t) (p 0 ⬝ᵥ c i 0 * (1 - δ)⁻¹) :=
        (hgeo.mul_left (p 0 ⬝ᵥ c i 0)).congr_fun fun t => by
          rw [hprice t, hconst i t, smul_dotProduct, smul_eq_mul]; ring
      have h2 : ∑' t, p t ⬝ᵥ ω i = p 0 ⬝ᵥ ω i * (1 - δ)⁻¹ :=
        ((hgeo.mul_left (p 0 ⬝ᵥ ω i)).congr_fun fun t => by
          rw [hprice t, smul_dotProduct, smul_eq_mul]; ring).tsum_eq
      have := (hbud i).unique h1
      rw [h2] at this
      have hinv : 0 < (1 - δ)⁻¹ := inv_pos.2 (by linarith)
      exact (mul_right_cancel₀ hinv.ne' this).symm
    rw [hDp, pow_zero, div_one, dotProduct_sub] at g
    have := hlam i
    simp only
    nlinarith

/-! ### Exercise 20.G.3: the Negishi parametrization -/

/-- **Exercise 20.G.3(a)** (MWG, p. 786): the Pareto frontier of the two-consumer exchange
economy of Exercise 20.G.2 is parametrized by the ratio `r` of marginal utilities of wealth. An
interior allocation exhausting the aggregate endowment (`c_{0t} + c_{1t} = ω_t`), with concave
differentiable utilities and strictly positive marginal utilities, is Pareto optimal if and only
if `∇u_0(c_{0t}) = r ∇u_1(c_{1t})` in every period for some `r > 0`. -/
theorem exercise_20_G_3a [NeZero L] {δ : ℝ} (hδ : 0 < δ) {u : Fin 2 → (Fin L → ℝ) → ℝ}
    (hconc : ∀ i, ConcaveOn ℝ (Set.Ici 0) (u i)) {ω : ℕ → Fin L → ℝ}
    {c : Fin 2 → ℕ → Fin L → ℝ} (hint : ∀ i t l, 0 < c i t l) (hω : ∀ t, ∑ i, c i t = ω t)
    (hs : ∀ i, Summable fun t => δ ^ t * u i (c i t)) {D : Fin 2 → ℕ → (Fin L → ℝ) →L[ℝ] ℝ}
    (hD : ∀ i t, HasFDerivAt (u i) (D i t) (c i t)) (hpos : ∀ i t l, 0 < D i t (Pi.single l 1)) :
    ParetoOptimalExchange δ u ω c ↔ ∃ r : ℝ, 0 < r ∧ ∀ t, D 0 t = r • D 1 t := by
  constructor
  · intro hpo
    exact exercise_20_G_2_ratio hδ hpo hs hint hD hpos (by decide)
  rintro ⟨r, hr, hDr⟩
  have hc0 : ∀ i t, 0 ≤ c i t := fun i t l => (hint i t l).le
  refine ⟨hc0, fun t => (hω t).le, ?_⟩
  rintro ⟨c', hc'0, hfeas', hs', hge, j, hj⟩
  -- the weighted utility gain is pointwise nonpositive
  have hpt : ∀ t, δ ^ t * (u 0 (c' 0 t) - u 0 (c 0 t)) + r * (δ ^ t * (u 1 (c' 1 t) - u 1 (c 1 t)))
      ≤ 0 := by
    intro t
    have g0 := MWG.GeneralEquilibriumExamples.concave_le_fderiv (hconc 0)
      (show c 0 t ∈ Set.Ici 0 from hc0 0 t) (show c' 0 t ∈ Set.Ici 0 from hc'0 0 t) (hD 0 t)
    have g1 := MWG.GeneralEquilibriumExamples.concave_le_fderiv (hconc 1)
      (show c 1 t ∈ Set.Ici 0 from hc0 1 t) (show c' 1 t ∈ Set.Ici 0 from hc'0 1 t) (hD 1 t)
    have hsum : D 0 t (c' 0 t - c 0 t) + r * D 1 t (c' 1 t - c 1 t) ≤ 0 := by
      have e : D 0 t (c' 0 t - c 0 t) + r * D 1 t (c' 1 t - c 1 t)
          = D 0 t (c' 0 t + c' 1 t - ω t) := by
        rw [← hω t, Fin.sum_univ_two, hDr t]
        simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, map_sub,
          map_add]
        ring
      rw [e, clm_apply_eq_sum]
      refine Finset.sum_nonpos fun l _ => mul_nonpos_of_nonpos_of_nonneg ?_
        (hpos 0 t l).le
      have := hfeas' t l
      simp only [Fin.sum_univ_two, Pi.add_apply] at this
      simp only [Pi.sub_apply, Pi.add_apply]
      linarith
    have hδt := pow_pos hδ t
    have hA : (u 0 (c' 0 t) - u 0 (c 0 t)) + r * (u 1 (c' 1 t) - u 1 (c 1 t)) ≤ 0 := by
      have := mul_le_mul_of_nonneg_left (show u 1 (c' 1 t) - u 1 (c 1 t)
        ≤ D 1 t (c' 1 t - c 1 t) by linarith) hr.le
      linarith
    calc δ ^ t * (u 0 (c' 0 t) - u 0 (c 0 t)) + r * (δ ^ t * (u 1 (c' 1 t) - u 1 (c 1 t)))
        = δ ^ t * ((u 0 (c' 0 t) - u 0 (c 0 t)) + r * (u 1 (c' 1 t) - u 1 (c 1 t))) := by ring
      _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hδt.le hA
  have hsum0 := Summable.tsum_le_tsum hpt
    ((((hs' 0).sub (hs 0)).congr fun t => by ring).add
      ((((hs' 1).sub (hs 1)).congr fun t => by ring).mul_left r)) summable_zero
  rw [tsum_zero, ((((hs' 0).sub (hs 0)).congr fun t => by ring)).tsum_add
      ((((hs' 1).sub (hs 1)).congr fun t => by ring).mul_left r), tsum_mul_left] at hsum0
  have e0 : ∑' t, δ ^ t * (u 0 (c' 0 t) - u 0 (c 0 t))
      = discountedUtility δ (u 0) (c' 0) - discountedUtility δ (u 0) (c 0) := by
    unfold discountedUtility
    rw [← (hs' 0).tsum_sub (hs 0)]; exact tsum_congr fun t => by ring
  have e1 : ∑' t, δ ^ t * (u 1 (c' 1 t) - u 1 (c 1 t))
      = discountedUtility δ (u 1) (c' 1) - discountedUtility δ (u 1) (c 1) := by
    unfold discountedUtility
    rw [← (hs' 1).tsum_sub (hs 1)]; exact tsum_congr fun t => by ring
  rw [e0, e1] at hsum0
  have h0 := hge 0
  have h1 := hge 1
  fin_cases j
  · simp only [Fin.zero_eta, Fin.isValue] at hj
    nlinarith
  · simp only [Fin.mk_one, Fin.isValue] at hj
    nlinarith

/-- The **Negishi prices** of a point of the Pareto frontier: `p_t = δ^t ∇u_0(c_{0t})`. -/
def negishiPrice (δ : ℝ) (D0 : ℕ → (Fin L → ℝ) →L[ℝ] ℝ) (t : ℕ) : Fin L → ℝ :=
  fun l => δ ^ t * D0 t (Pi.single l 1)

/-- **Exercise 20.G.3(b)** (MWG, p. 786), the Negishi equation: let `c` be a point of the Pareto
frontier with parameter `r > 0` (`∇u_0(c_{0t}) = r ∇u_1(c_{1t})`, Exercise 20.G.3(a)), exhausting
the endowments `ω_0 + ω_1`, with bounded consumptions, endowments and marginal utilities,
`0 < δ < 1`, and Negishi prices `p_t = δ^t ∇u_0(c_{0t})`. Then `(p, c)` is a Walrasian
equilibrium (every consumer maximizes utility on the budget set with wealth `∑_t p_t · ω_{it}`)
if and only if the one equation in the one unknown `r`,
`∑_t p_t · c_{0t} - ∑_t p_t · ω_{0t} = 0` (consumer 0's wealth gap), holds. -/
theorem exercise_20_G_3b {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) {u : Fin 2 → (Fin L → ℝ) → ℝ}
    (hconc : ∀ i, ConcaveOn ℝ (Set.Ici 0) (u i)) {ω c : Fin 2 → ℕ → Fin L → ℝ} {B G r : ℝ}
    (hc0 : ∀ i t, 0 ≤ c i t) (hcB : ∀ i t l, c i t l ≤ B) (hω0 : ∀ i t, 0 ≤ ω i t)
    (hωB : ∀ i t l, ω i t l ≤ B) (hclear : ∀ t, c 0 t + c 1 t = ω 0 t + ω 1 t)
    (hs : ∀ i, Summable fun t => δ ^ t * u i (c i t)) {D : Fin 2 → ℕ → (Fin L → ℝ) →L[ℝ] ℝ}
    (hD : ∀ i t, HasFDerivAt (u i) (D i t) (c i t)) (hpos : ∀ t l, 0 ≤ D 0 t (Pi.single l 1))
    (hG : ∀ t l, D 0 t (Pi.single l 1) ≤ G) (hr : 0 < r) (hDr : ∀ t, D 0 t = r • D 1 t) :
    (∀ i, UtilityMax (Set.Ici 0) δ (u i) (negishiPrice δ (D 0))
        (∑' t, negishiPrice δ (D 0) t ⬝ᵥ ω i t) (c i)) ↔
      ∑' t, negishiPrice δ (D 0) t ⬝ᵥ c 0 t - ∑' t, negishiPrice δ (D 0) t ⬝ᵥ ω 0 t = 0 := by
  set p := negishiPrice δ (D 0) with hp
  have hδt : ∀ t, 0 ≤ δ ^ t := fun t => pow_nonneg hδ0.le t
  have hp0 : ∀ t, 0 ≤ p t := fun t l => mul_nonneg (hδt t) (hpos t l)
  -- value series of bounded nonnegative streams converge
  have hsumm : ∀ v : ℕ → Fin L → ℝ, (∀ t, 0 ≤ v t) → (∀ t l, v t l ≤ B) →
      Summable fun t => p t ⬝ᵥ v t := by
    intro v hv0 hvB
    refine Summable.of_nonneg_of_le (fun t => dotProduct_nonneg_of_nonneg (hp0 t) (hv0 t))
      (fun t => ?_) ((summable_geometric_of_lt_one hδ0.le hδ1).mul_right
        (Fintype.card (Fin L) * (G * B)))
    simp only [dotProduct]
    calc ∑ l, p t l * v t l ≤ ∑ _l : Fin L, δ ^ t * (G * B) := Finset.sum_le_sum fun l _ => by
          simp only [hp, negishiPrice]
          have := hpos t l
          have := hG t l
          have h3 : 0 ≤ v t l := hv0 t l
          have := hvB t l
          have := hδt t
          have hGB : D 0 t (Pi.single l 1) * v t l ≤ G * B := by nlinarith
          nlinarith
      _ = δ ^ t * (Fintype.card (Fin L) * (G * B)) := by simp; ring
  have hsc : ∀ i, Summable fun t => p t ⬝ᵥ c i t := fun i => hsumm _ (hc0 i) (hcB i)
  have hsω : ∀ i, Summable fun t => p t ⬝ᵥ ω i t := fun i => hsumm _ (hω0 i) (hωB i)
  -- total value identity
  have htot : ∑' t, p t ⬝ᵥ c 0 t + ∑' t, p t ⬝ᵥ c 1 t
      = ∑' t, p t ⬝ᵥ ω 0 t + ∑' t, p t ⬝ᵥ ω 1 t := by
    rw [← (hsc 0).tsum_add (hsc 1), ← (hsω 0).tsum_add (hsω 1)]
    exact tsum_congr fun t => by rw [← dotProduct_add, ← dotProduct_add, hclear t]
  -- the first-order identities `δ^t ∇u_0 = p_t`, `δ^t ∇u_1 = p_t / r`
  have hfoc0 : ∀ t v, δ ^ t * D 0 t v = p t ⬝ᵥ v := fun t v => by
    rw [clm_apply_eq_sum, Finset.mul_sum]
    simp only [hp, negishiPrice, dotProduct]
    exact Finset.sum_congr rfl fun l _ => by ring
  have hfoc1 : ∀ t v, δ ^ t * D 1 t v = r⁻¹ * (p t ⬝ᵥ v) := fun t v => by
    rw [← hfoc0, hDr t]
    simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
    field_simp
  constructor
  · intro hmax
    have h0 := (expenditure_summable hp0 (fun t => (hmax 0).1.1 t) (hmax 0).1.2.2).2
    have h1 := (expenditure_summable hp0 (fun t => (hmax 1).1.1 t) (hmax 1).1.2.2).2
    linarith
  intro hgap
  -- generic optimality from the gradient inequality, for a weight `κ > 0` with
  -- `δ^t ∇u_i = κ p_t` and binding budget
  have hopt : ∀ i (κ : ℝ), 0 < κ → (∀ t v, δ ^ t * D i t v = κ * (p t ⬝ᵥ v)) →
      ∑' t, p t ⬝ᵥ c i t = ∑' t, p t ⬝ᵥ ω i t →
      UtilityMax (Set.Ici 0) δ (u i) p (∑' t, p t ⬝ᵥ ω i t) (c i) := by
    intro i κ hκ hfi hbi
    refine ⟨⟨fun t => hc0 i t, ⟨max B 0, fun t l => ?_⟩, fun T => ?_⟩, hs i,
      fun c' hc' hs' => ?_⟩
    · rw [abs_of_nonneg (hc0 i t l)]; exact (hcB i t l).trans (le_max_left _ _)
    · rw [← hbi]
      exact (hsc i).sum_le_tsum _ fun t _ => dotProduct_nonneg_of_nonneg (hp0 t) (hc0 i t)
    obtain ⟨hcs, hcle⟩ := expenditure_summable hp0 (fun t => hc'.1 t) hc'.2.2
    have hpt : ∀ t, δ ^ t * u i (c' t)
        ≤ δ ^ t * u i (c i t) + κ * (p t ⬝ᵥ c' t) - κ * (p t ⬝ᵥ c i t) := by
      intro t
      have g := MWG.GeneralEquilibriumExamples.concave_le_fderiv (hconc i)
        (show c i t ∈ Set.Ici 0 from hc0 i t) (hc'.1 t) (hD i t)
      have e := hfi t (c' t - c i t)
      rw [dotProduct_sub] at e
      nlinarith [hδt t]
    have hsR : Summable fun t => δ ^ t * u i (c i t) + κ * (p t ⬝ᵥ c' t)
        - κ * (p t ⬝ᵥ c i t) := (((hs i).add (hcs.mul_left κ))).sub ((hsc i).mul_left κ)
    unfold discountedUtility
    calc ∑' t, δ ^ t * u i (c' t) ≤ ∑' t, (δ ^ t * u i (c i t) + κ * (p t ⬝ᵥ c' t)
          - κ * (p t ⬝ᵥ c i t)) := Summable.tsum_le_tsum hpt hs' hsR
      _ = ∑' t, δ ^ t * u i (c i t) + κ * ∑' t, p t ⬝ᵥ c' t
          - κ * ∑' t, p t ⬝ᵥ c i t := by
          rw [((hs i).add (hcs.mul_left κ)).tsum_sub ((hsc i).mul_left κ),
            (hs i).tsum_add (hcs.mul_left κ), tsum_mul_left, tsum_mul_left]
      _ ≤ ∑' t, δ ^ t * u i (c i t) := by rw [hbi] at *; nlinarith
  intro i
  fin_cases i
  · exact hopt 0 1 one_pos (fun t v => by rw [hfoc0, one_mul]) (by linarith)
  · exact hopt 1 r⁻¹ (inv_pos.2 hr) hfoc1 (by linarith)

end MWG.EquilibriumTime
