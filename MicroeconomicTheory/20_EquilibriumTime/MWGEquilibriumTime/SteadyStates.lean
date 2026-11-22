/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGEquilibriumTime.RamseySolowPrices
import MWGEquilibriumTime.Euler

/-!
# Steady states of the Ramsey-Solow model and golden rules (MWG Section 20.E, pp. 756-759)

MWG, Chapter 20, Section 20.E from p. 756, with Exercises 20.E.3-20.E.8 (pp. 784-785).

Labor is fixed at one unit per period; `f(k) = F(k, 1)` (`F ![k, 1]`). A steady state `k` has
surplus `c(k) = f(k) - k` and rate of interest `r(k) = f'(k) - 1`; the golden rule `k̂` maximizes
`c`, i.e. `f'(k̂) = 1` (`golden_rule_iff`), and the modified golden rule has
`r(k_δ) = (1 - δ)/δ`.

* The interest rate implicit in Malinvaud prices: `q_{t+1}(1 + r_t) = q_t`
  (`rs_interest_rate`); the steady-state supporting prices (`rs_steady_prices`).
* Below the golden rule `r > 0`, above it `r < 0` (`rate_pos_below_golden`,
  `rate_neg_above_golden`); steady states above the golden rule are inefficient
  (`inefficient_above_golden`); **the golden rule is efficient** (`golden_rule_efficient`, from
  the capital-depletion argument `golden_rule_capital`).
* **Exercise 20.E.3**: every path with `k_t ≤ k̂ - ε` is efficient (`exercise_20_E_3`).
* **Exercise 20.E.4**, the neoclassical properties (`exercise_20_E_4_i_mono`,
  `exercise_20_E_4_i_anti`, `exercise_20_E_4_ii`, `exercise_20_E_4_iii`), with Euler's theorem
  for constant returns (`euler_homogeneous`).
* **(20.E.1)** and **Exercises 20.E.5-20.E.7** for the multisector model, and **Exercise
  20.E.8** (growth golden rule `r = n`).

Not formalised: the possibility of several modified golden rules in the two-sector model
(Figure 20.E.3, a graphical claim without explicit data), and the efficiency of the golden rule in
the general `(N+1)`-sector model (asserted without proof, "we could also prove").
-/

open Filter Topology

namespace MWG.EquilibriumTime

/-! ### Concavity tools on the real line -/

/-- The three-chord inequality for a concave function: for `a ≤ b < c` in `S`,
`(f c - f b)/(c - b) ≤ (f c - f a)/(c - a)`. -/
theorem chord_right_le {S : Set ℝ} {f : ℝ → ℝ} (hf : ConcaveOn ℝ S f) {a b c : ℝ} (ha : a ∈ S)
    (hc : c ∈ S) (hab : a ≤ b) (hbc : b < c) :
    (f c - f b) / (c - b) ≤ (f c - f a) / (c - a) := by
  rcases eq_or_lt_of_le hab with rfl | hab'
  · exact le_rfl
  have hca : 0 < c - a := by linarith
  have hcb : 0 < c - b := by linarith
  set lam := (c - b) / (c - a) with hlam
  have hl0 : 0 ≤ lam := div_nonneg hcb.le hca.le
  have hl1 : 0 ≤ 1 - lam := by
    rw [hlam, sub_nonneg, div_le_one hca]; linarith
  have hb : lam • a + (1 - lam) • c = b := by
    simp only [smul_eq_mul, hlam]; field_simp; ring
  have := hf.2 ha hc hl0 hl1 (by ring)
  rw [hb] at this
  simp only [smul_eq_mul] at this
  rw [div_le_div_iff₀ hcb hca]
  have e : (c - b) = lam * (c - a) := by rw [hlam]; field_simp
  rw [e]
  nlinarith

/-- A strictly concave function with derivative `1` at `k̂` lies strictly below its tangent:
`f(k̂ - d) < f(k̂) - d` for `0 < d` with `k̂ - d ∈ S`. -/
theorem strict_tangent_below {S : Set ℝ} {f : ℝ → ℝ} (hf : StrictConcaveOn ℝ S f) {kh d : ℝ}
    (hkh : kh ∈ S) (hd : 0 < d) (hmem : kh - d ∈ S) (hder : HasDerivAt f 1 kh) :
    f (kh - d) < f kh - d := by
  have := hf.lt_slope_of_hasDerivAt hmem hkh (by linarith) hder
  rw [slope_def_field, lt_div_iff₀ (by linarith)] at this
  linarith

/-- A strictly concave function is strictly increasing to the left of a maximizer. -/
theorem strictMonoOn_left_of_max {S : Set ℝ} {g : ℝ → ℝ} (hg : StrictConcaveOn ℝ S g) {m : ℝ}
    (hm : m ∈ S) (hmax : ∀ x ∈ S, g x ≤ g m) :
    StrictMonoOn g (S ∩ Set.Iic m) := by
  intro a ha b hb hab
  rcases eq_or_lt_of_le (Set.mem_Iic.1 hb.2) with rfl | hbm
  · -- `a < m`: the midpoint beats `a`, so `g a < g m`
    have hmid := hg.2 ha.1 hm (ne_of_lt hab) (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
    have hmS : (1 / 2 : ℝ) • a + (1 / 2 : ℝ) • b ∈ S :=
      hg.1 ha.1 hm (by norm_num) (by norm_num) (by norm_num)
    have := hmax _ hmS
    simp only [smul_eq_mul] at hmid this
    linarith
  · have hma : 0 < m - a := by linarith
    set lam := (m - b) / (m - a) with hlam
    have hl0 : 0 < lam := div_pos (by linarith) hma
    have hl1 : 0 < 1 - lam := by rw [hlam, sub_pos, div_lt_one hma]; linarith
    have hcomb : lam • a + (1 - lam) • m = b := by
      simp only [smul_eq_mul, hlam]; field_simp; ring
    have := hg.2 ha.1 hm (ne_of_lt (lt_trans hab hbm)) hl0 hl1 (by ring)
    rw [hcomb] at this
    simp only [smul_eq_mul] at this
    have := hmax a ha.1
    nlinarith

/-- A strictly concave function is strictly decreasing to the right of a maximizer. -/
theorem strictAntiOn_right_of_max {S : Set ℝ} {g : ℝ → ℝ} (hg : StrictConcaveOn ℝ S g) {m : ℝ}
    (hm : m ∈ S) (hmax : ∀ x ∈ S, g x ≤ g m) :
    StrictAntiOn g (S ∩ Set.Ici m) := by
  intro a ha b hb hab
  rcases eq_or_lt_of_le (Set.mem_Ici.1 ha.2) with rfl | ham
  · have hmid := hg.2 hm hb.1 (ne_of_lt hab) (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
    have hmS : (1 / 2 : ℝ) • m + (1 / 2 : ℝ) • b ∈ S :=
      hg.1 hm hb.1 (by norm_num) (by norm_num) (by norm_num)
    have := hmax _ hmS
    simp only [smul_eq_mul] at hmid this
    linarith
  · have hbm : 0 < b - m := by linarith
    set lam := (b - a) / (b - m) with hlam
    have hl0 : 0 < lam := div_pos (by linarith) hbm
    have hl1 : 0 < 1 - lam := by rw [hlam, sub_pos, div_lt_one hbm]; linarith
    have hcomb : lam • m + (1 - lam) • b = a := by
      simp only [smul_eq_mul, hlam]; field_simp; ring
    have := hg.2 hm hb.1 (ne_of_lt (lt_trans ham hab)) hl0 hl1 (by ring)
    rw [hcomb] at this
    simp only [smul_eq_mul] at this
    have := hmax b hb.1
    nlinarith

/-! ### Steady states of the Ramsey-Solow model -/

/-- The capital derivative of `F(·, 1)` is the partial derivative `∇₁F`. -/
theorem hasDerivAt_capital {F : (Fin 2 → ℝ) → ℝ} {k l : ℝ} {DF : (Fin 2 → ℝ) →L[ℝ] ℝ}
    (hDF : HasFDerivAt F DF ![k, l]) :
    HasDerivAt (fun s => F ![s, l]) (DF (Pi.single 0 1)) k := by
  have hline : HasDerivAt (fun s : ℝ => (![s, l] : Fin 2 → ℝ)) (Pi.single 0 1) k := by
    refine hasDerivAt_pi.2 fun i => ?_
    fin_cases i
    · simpa using hasDerivAt_id' k
    · simpa using hasDerivAt_const k l
  exact hDF.comp_hasDerivAt k hline

/-- **The rate of interest is the net marginal productivity of capital** (MWG, p. 756): at an
interior plan `(k_t, 1)` supported by Malinvaud prices, `q_{t+1}(1 + r_t) = q_t` with
`r_t = ∇₁F(k_t, 1) - 1`. -/
theorem rs_interest_rate {F : (Fin 2 → ℝ) → ℝ} {k : ℝ} (hk : 0 < k)
    {DF : (Fin 2 → ℝ) →L[ℝ] ℝ} (hDF : HasFDerivAt F DF ![k, 1]) {q w q' w' : ℝ}
    (hmax : ∀ z ∈ ramseySolowSet F, planValue ![q, w] ![q', w'] z ≤
      planValue ![q, w] ![q', w'] (rsPlan F k 1)) :
    q' * (1 + (DF (Pi.single 0 1) - 1)) = q := by
  obtain ⟨h, -⟩ := rs_foc_of_profitMax hk one_pos hDF hmax
  rw [h]; ring

/-- **The steady-state supporting prices** (MWG, p. 756): for a steady state `k ≥ 0` with
`r = ∇₁F(k, 1) - 1 > -1` and `∇₂F ≥ 0`, the sequence `(q_t, w_t) = (1/(1 + r))^t (q₀, w₀)` with
`w₀ / q₀ = ∇₂F / ∇₁F` (here `q₀ = 1`) myopically supports the stationary path. -/
theorem rs_steady_prices {F : (Fin 2 → ℝ) → ℝ} (hconc : ConcaveOn ℝ (Set.Ici 0) F)
    (hmono : MonotoneOn F (Set.Ici 0)) {k : ℝ} (hk : 0 ≤ k) {DF : (Fin 2 → ℝ) →L[ℝ] ℝ}
    (hDF : HasFDerivAt F DF ![k, 1]) (hpos : 0 < DF (Pi.single 0 1)) :
    MyopicProfitMax (ramseySolowSet F)
      (fun t => ((1 / DF (Pi.single 0 1)) ^ t) • ![1, DF (Pi.single 1 1) / DF (Pi.single 0 1)])
      (fun _ => rsPlan F k 1) := by
  have h := exercise_20_C_6 hconc hmono (k := fun _ => k) (l := fun _ => 1) (fun _ => hk)
    (fun _ => zero_le_one) (DF := fun _ => DF) (fun _ => hDF)
    (q := fun t => (1 / DF (Pi.single 0 1)) ^ t)
    (fun t => pow_pos (by positivity) t) (fun t => by
      rw [pow_succ]; field_simp)
  convert h using 1
  · funext t i
    fin_cases i
    · simp [rsPrices]
    · simp only [rsPrices, Pi.smul_apply, smul_eq_mul, Fin.mk_one, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, pow_succ]
      field_simp
  · rfl

/-- **The golden rule** (MWG, p. 756): for `f` concave on `ℝ_+` and differentiable at `k̂ > 0`,
`k̂` maximizes the steady-state surplus `c(k) = f(k) - k` if and only if
`r(k̂) = f'(k̂) - 1 = 0`. -/
theorem golden_rule_iff {f : ℝ → ℝ} (hf : ConcaveOn ℝ (Set.Ici 0) f) {kh f' : ℝ}
    (hkh : 0 < kh) (hder : HasDerivAt f f' kh) :
    (∀ k, 0 ≤ k → f k - k ≤ f kh - kh) ↔ f' - 1 = 0 := by
  constructor
  · intro h
    have hloc : IsLocalMax (fun k => f k - k) kh := by
      filter_upwards [Ioi_mem_nhds hkh] with k hk using h k (le_of_lt hk)
    have := hloc.hasDerivAt_eq_zero (hder.sub (hasDerivAt_id kh))
    linarith
  · intro h k hk
    have := MWG.GeneralEquilibriumExamples.concave_le_tangent hf (Set.mem_Ici.2 hkh.le)
      (Set.mem_Ici.2 hk) hder
    have hf1 : f' = 1 := by linarith
    rw [hf1] at this
    linarith

/-- **The modified golden rule** (MWG, p. 756): `r(k_δ) = (1 - δ)/δ` exactly when `f'(k_δ) = 1/δ`,
the factor of the proportional prices `δ^t`. -/
theorem modified_golden_rule_iff {δ f' : ℝ} (hδ : δ ≠ 0) : f' - 1 = (1 - δ) / δ ↔ f' = 1 / δ := by
  constructor <;> intro h
  · field_simp at h ⊢; linarith
  · rw [h]; field_simp

/-- **Below the golden rule the rate of interest is positive** (MWG, p. 756): for `f` strictly
concave and `0 ≤ k < k̂`, `f'(k) > f'(k̂) = 1`. -/
theorem rate_pos_below_golden {f : ℝ → ℝ} (hf : StrictConcaveOn ℝ (Set.Ici 0) f) {k kh fk : ℝ}
    (hk : 0 ≤ k) (hkkh : k < kh) (hdk : HasDerivAt f fk k) (hdkh : HasDerivAt f 1 kh) :
    0 < fk - 1 := by
  have h1 := hf.slope_lt_of_hasDerivAt (Set.mem_Ici.2 hk) (Set.mem_Ici.2 (hk.trans hkkh.le))
    hkkh hdk
  have h2 := hf.lt_slope_of_hasDerivAt (Set.mem_Ici.2 hk) (Set.mem_Ici.2 (hk.trans hkkh.le))
    hkkh hdkh
  linarith

/-- **Above the golden rule the rate of interest is negative** (MWG, p. 756). -/
theorem rate_neg_above_golden {f : ℝ → ℝ} (hf : StrictConcaveOn ℝ (Set.Ici 0) f) {k kh fk : ℝ}
    (hkh : 0 ≤ kh) (hkkh : kh < k) (hdk : HasDerivAt f fk k) (hdkh : HasDerivAt f 1 kh) :
    fk - 1 < 0 := by
  have h1 := hf.slope_lt_of_hasDerivAt (Set.mem_Ici.2 hkh) (Set.mem_Ici.2 (hkh.trans hkkh.le))
    hkkh hdkh
  have h2 := hf.lt_slope_of_hasDerivAt (Set.mem_Ici.2 hkh) (Set.mem_Ici.2 (hkh.trans hkkh.le))
    hkkh hdk
  linarith

/-- **Steady states above the golden rule are inefficient** (MWG, p. 756): if `k̂ < k` and `k̂`
maximizes the surplus `F(k, 1) - k` over `k ≥ 0`, the stationary path at `k̂` dominates the
stationary path at `k` (less capital at `t = 0`, at least as much surplus afterwards). -/
theorem inefficient_above_golden {F : (Fin 2 → ℝ) → ℝ} {k kh : ℝ} (hkh : 0 ≤ kh)
    (hkkh : kh < k) (hmax : ∀ x, 0 ≤ x → F ![x, 1] - x ≤ F ![kh, 1] - kh) :
    ¬ ProdEfficient (ramseySolowSet F) (fun _ => rsPlan F k 1) := by
  rintro ⟨-, hno⟩
  refine hno ⟨fun _ => rsPlan F kh 1, fun _ => rsPlan_mem hkh zero_le_one, fun t => ?_, ?_⟩
  · intro i
    cases t with
    | zero =>
      fin_cases i
      · simp [netOutput, rsPlan]; linarith
      · simp [netOutput, rsPlan]
    | succ t =>
      have := hmax k (hkh.trans hkkh.le)
      fin_cases i
      · simp [netOutput, rsPlan]; linarith
      · simp [netOutput, rsPlan]
  · intro h
    have := congrFun (congrFun h 0) 0
    simp [netOutput, rsPlan] at this
    linarith

/-- **The capital-depletion argument** for the golden rule (MWG, pp. 756-757, Figure 20.E.2): if
`f` is strictly concave on `ℝ_+` with `f'(k̂) = 1`, a nonnegative capital path with `k'₀ ≤ k̂` and
surplus `f(k'_t) - k'_{t+1}` at least the golden-rule surplus `f(k̂) - k̂` at every date must stay
at `k̂`: any attempt to use less capital leads to capital depletion in finite time. -/
theorem golden_rule_capital {f : ℝ → ℝ} (hf : StrictConcaveOn ℝ (Set.Ici 0) f) {kh : ℝ}
    (hkh : 0 < kh) (hder : HasDerivAt f 1 kh) {k : ℕ → ℝ} (hk0 : ∀ t, 0 ≤ k t)
    (hstart : k 0 ≤ kh) (hsurplus : ∀ t, f kh - kh ≤ f (k t) - k (t + 1)) (t : ℕ) :
    k t = kh := by
  have hcv := hf.concaveOn
  have htan : ∀ x, 0 ≤ x → f x ≤ f kh + (x - kh) := fun x hx => by
    have := MWG.GeneralEquilibriumExamples.concave_le_tangent hcv (Set.mem_Ici.2 hkh.le)
      (Set.mem_Ici.2 hx) hder
    linarith
  set d : ℕ → ℝ := fun t => kh - k t with hd
  have hstep : ∀ t, f kh - f (k t) ≤ d (t + 1) := fun t => by
    have := hsurplus t; simp only [hd]; linarith
  have hd0 : ∀ t, 0 ≤ d t := by
    intro t
    induction t with
    | zero => simp only [hd]; linarith
    | succ t ih =>
      have h1 := hstep t
      have h2 := htan (k t) (hk0 t)
      simp only [hd] at ih ⊢ h1
      linarith
  have hdle : ∀ t, d t ≤ kh := fun t => by simp only [hd]; linarith [hk0 t]
  by_contra hne
  have hds : 0 < d t := lt_of_le_of_ne (hd0 t) (fun h => hne (by simp only [hd] at h; linarith))
  set g := f kh - f (kh - d t) - d t with hg
  have hgpos : 0 < g := by
    have := strict_tangent_below hf (Set.mem_Ici.2 hkh.le) hds (Set.mem_Ici.2 (by
      simp only [hd]; linarith [hk0 t])) hder
    simp only [hg]; linarith
  -- once the deficit is at least `d_t`, it grows by at least `g` per period
  have hgrow : ∀ D, d t ≤ D → D ≤ kh → D + g ≤ f kh - f (kh - D) := by
    intro D hD hDk
    have hD0 : 0 < D := lt_of_lt_of_le hds hD
    have := chord_right_le hcv (Set.mem_Ici.2 (by linarith : (0 : ℝ) ≤ kh - D))
      (Set.mem_Ici.2 hkh.le) (by linarith : kh - D ≤ kh - d t) (by linarith : kh - d t < kh)
    rw [show kh - (kh - d t) = d t by ring, show kh - (kh - D) = D by ring,
      div_le_div_iff₀ hds hD0] at this
    have hgd : f kh - f (kh - d t) = d t + g := by simp only [hg]; ring
    rw [hgd] at this
    nlinarith
  have hlin : ∀ m : ℕ, d t + m * g ≤ d (t + m) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have h1 := hstep (t + m)
      have h2 := hgrow (d (t + m)) (by nlinarith [hgpos]) (hdle _)
      have hkd : k (t + m) = kh - d (t + m) := by simp only [hd]; ring
      rw [hkd] at h1
      rw [show t + (m + 1) = t + m + 1 by ring]
      push_cast
      linarith
  obtain ⟨m, hm⟩ := exists_nat_gt (kh / g)
  have := hlin m
  have := hdle (t + m)
  rw [div_lt_iff₀ hgpos] at hm
  nlinarith

/-- **The golden rule steady state is efficient** (MWG, pp. 756-757). Hypotheses: `F` is
nondecreasing on `ℝ²_+`, `f = F(·, 1)` is strictly concave on `ℝ_+` with `f'(k̂) = 1`, `k̂ > 0`, and
output at `k̂` strictly increases with labor up to `1` (so that saving labor costs output). -/
theorem golden_rule_efficient {F : (Fin 2 → ℝ) → ℝ} (hmono : MonotoneOn F (Set.Ici 0))
    (hf : StrictConcaveOn ℝ (Set.Ici 0) (fun k => F ![k, 1])) {kh : ℝ} (hkh : 0 < kh)
    (hder : HasDerivAt (fun k => F ![k, 1]) 1 kh)
    (hlab : ∀ l, 0 ≤ l → l < 1 → F ![kh, l] < F ![kh, 1]) :
    ProdEfficient (ramseySolowSet F) (fun _ => rsPlan F kh 1) := by
  refine ⟨fun _ => rsPlan_mem hkh.le zero_le_one, fun ⟨y', hy', hle, hne⟩ => hne ?_⟩
  rw [ramseySolowSet_eq hmono] at hy'
  set k : ℕ → ℝ := fun t => -(y' t).1 0 with hk
  set l : ℕ → ℝ := fun t => -(y' t).1 1 with hl
  have hk0 : ∀ t, 0 ≤ k t := fun t => by have := (hy' t).1 0; simp only [hk]; simp at this; linarith
  have hl0 : ∀ t, 0 ≤ l t := fun t => by have := (hy' t).1 1; simp only [hl]; simp at this; linarith
  have hneg : ∀ t, -(y' t).1 = ![k t, l t] := fun t => by
    funext i; fin_cases i <;> simp [hk, hl]
  -- labor input is at most one
  have hl1 : ∀ t, l t ≤ 1 := by
    intro t
    cases t with
    | zero => have := hle 0 1; simp [netOutput, rsPlan] at this; simp only [hl]; linarith
    | succ t =>
      have := hle (t + 1) 1
      have ha := (hy' t).2.1
      simp [netOutput, rsPlan] at this
      simp only [hl]; linarith
  -- output is at most `f(k_t)`
  have hout : ∀ t, (y' t).2 0 ≤ F ![k t, 1] := by
    intro t
    have h1 := (hy' t).2.2
    rw [hneg] at h1
    have hle' : ![k t, l t] ≤ ![k t, 1] := by
      intro i; fin_cases i <;> simp [hl1 t]
    have h0 : (0 : Fin 2 → ℝ) ≤ ![k t, l t] := by
      intro i; fin_cases i <;> simp [hk0 t, hl0 t]
    exact h1.trans (hmono h0 (h0.trans hle') hle')
  have hsurplus : ∀ t, F ![kh, 1] - kh ≤ F ![k t, 1] - k (t + 1) := by
    intro t
    have := hle (t + 1) 0
    simp [netOutput, rsPlan] at this
    have := hout t
    simp only [hk]; linarith
  have hstart : k 0 ≤ kh := by
    have := hle 0 0; simp [netOutput, rsPlan] at this; simp only [hk]; linarith
  have hkeq : ∀ t, k t = kh :=
    golden_rule_capital (f := fun k => F ![k, 1]) hf hkh hder hk0 hstart hsurplus
  -- output equals `f(k̂)` at every date
  have hx : ∀ t, (y' t).2 0 = F ![kh, 1] := by
    intro t
    refine le_antisymm (by rw [← hkeq t]; exact hout t) ?_
    have := hle (t + 1) 0
    simp [netOutput, rsPlan] at this
    have h2 := hkeq (t + 1)
    simp only [hk] at h2
    linarith
  -- labor input is exactly one
  have hlab1 : ∀ t, l t = 1 := by
    intro t
    by_contra hne1
    have hlt : l t < 1 := lt_of_le_of_ne (hl1 t) hne1
    have h1 := (hy' t).2.2
    rw [hneg, hkeq t] at h1
    have := hlab (l t) (hl0 t) hlt
    linarith [hx t]
  -- hence the net outputs coincide
  have ha1 : ∀ t, (y' t).2 1 = 0 := by
    intro t
    have := hle (t + 1) 1
    have h2 := hlab1 (t + 1)
    simp [netOutput, rsPlan] at this
    simp only [hl] at h2
    linarith [(hy' t).2.1]
  funext t i
  cases t with
  | zero =>
    fin_cases i
    · have := hkeq 0; simp only [hk] at this; simp [netOutput, rsPlan]; linarith
    · have := hlab1 0; simp only [hl] at this; simp [netOutput, rsPlan]; linarith
  | succ t =>
    fin_cases i
    · have := hkeq (t + 1); simp only [hk] at this; simp [netOutput, rsPlan, hx t]; linarith
    · have := hlab1 (t + 1); simp only [hl] at this; simp [netOutput, rsPlan, ha1 t]; linarith

/-! ### Exercises 20.E.3, 20.E.4 and 20.E.8 -/

/-- **Exercise 20.E.3** (MWG, p. 784): in the Ramsey-Solow model with `f = F(·, 1)` strictly concave
and `f'(k̂) = 1`, every capital path with `0 ≤ k_t ≤ k̂ - ε` (`ε > 0`) is efficient. The prices with
`q_t / q_{t+1} = f'(k_t)` fall geometrically, since `f'(k_t) ≥ (f(k̂) - f(k̂ - ε))/ε > 1`, so the
transversality condition holds (hint of the exercise; (20.C.1)-(20.C.2)). Hypotheses: `F` concave
and nondecreasing on `ℝ²_+`, `F(0) = 0`, differentiable along the path with positive marginal
product of labor. -/
theorem exercise_20_E_3 {F : (Fin 2 → ℝ) → ℝ} (hconc : ConcaveOn ℝ (Set.Ici 0) F)
    (hmono : MonotoneOn F (Set.Ici 0)) (h00 : F 0 = 0)
    (hf : StrictConcaveOn ℝ (Set.Ici 0) (fun k => F ![k, 1])) {kh : ℝ} (hkh : 0 < kh)
    (hder : HasDerivAt (fun k => F ![k, 1]) 1 kh) {ε : ℝ} (hε : 0 < ε) (hεk : ε ≤ kh)
    {k : ℕ → ℝ} (hk0 : ∀ t, 0 ≤ k t) (hkε : ∀ t, k t ≤ kh - ε) {DF : ℕ → (Fin 2 → ℝ) →L[ℝ] ℝ}
    (hDF : ∀ t, HasFDerivAt F (DF t) ![k t, 1]) (hmpl : ∀ t, 0 < DF t (Pi.single 1 1)) :
    ProdEfficient (ramseySolowSet F) (rsPath F k fun _ => 1) := by
  set f : ℝ → ℝ := fun k => F ![k, 1] with hfdef
  set ρ := (f kh - f (kh - ε)) / ε with hρ
  have hρ1 : 1 < ρ := by
    have := strict_tangent_below hf (Set.mem_Ici.2 hkh.le) hε (Set.mem_Ici.2 (by linarith)) hder
    rw [hρ, lt_div_iff₀ hε]; linarith
  -- the marginal product of capital along the path is at least `ρ`
  have hmpk : ∀ t, ρ ≤ DF t (Pi.single 0 1) := by
    intro t
    have hd := hasDerivAt_capital (hDF t)
    have h1 := hf.concaveOn.slope_le_of_hasDerivAt (Set.mem_Ici.2 (hk0 t))
      (Set.mem_Ici.2 hkh.le) (by linarith [hkε t]) hd
    have h2 := chord_right_le hf.concaveOn (Set.mem_Ici.2 (hk0 t)) (Set.mem_Ici.2 hkh.le)
      (hkε t) (by linarith)
    rw [show kh - (kh - ε) = ε by ring] at h2
    rw [slope_def_field] at h1
    exact h2.trans h1
  have hDpos : ∀ t, 0 < DF t (Pi.single 0 1) := fun t => by linarith [hmpk t]
  -- output prices
  set q : ℕ → ℝ := fun t => ∏ s ∈ Finset.range t, (DF s (Pi.single 0 1))⁻¹ with hq
  have hqpos : ∀ t, 0 < q t := fun t => Finset.prod_pos fun s _ => inv_pos.2 (hDpos s)
  have hqrec : ∀ t, q t / q (t + 1) = DF t (Pi.single 0 1) := by
    intro t
    have hq1 : q (t + 1) = q t * (DF t (Pi.single 0 1))⁻¹ := by
      simp only [hq, Finset.prod_range_succ]
    rw [hq1, div_mul_eq_div_div, div_self (hqpos t).ne', one_div, inv_inv]
  have hqle : ∀ t, q t ≤ (ρ⁻¹) ^ t := by
    intro t
    induction t with
    | zero => simp [hq]
    | succ t ih =>
      simp only [hq, Finset.prod_range_succ, pow_succ] at ih ⊢
      exact mul_le_mul ih (inv_anti₀ (by linarith) (hmpk t)) (inv_pos.2 (hDpos t)).le
        (pow_nonneg (inv_pos.2 (by linarith)).le t)
  have hqlim : Tendsto q atTop (𝓝 0) := by
    refine squeeze_zero (fun t => (hqpos t).le) hqle ?_
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (inv_pos.2 (by linarith)).le
      (inv_lt_one_of_one_lt₀ hρ1)
  refine efficient_of_20_C_1_20_C_2 hconc hmono h00 hk0 (fun _ => zero_le_one) hDF hmpl
    (B := F ![kh, 1]) (fun t => ?_) hqpos hqrec hqlim
  have h0 : (0 : Fin 2 → ℝ) ≤ ![k t, 1] := by
    intro i; fin_cases i <;> simp [hk0 t]
  have hle : ![k t, (1 : ℝ)] ≤ ![kh, 1] := by
    intro i; fin_cases i <;> simp; linarith [hkε t]
  have hlo := hmono (le_refl (0 : Fin 2 → ℝ)) h0 h0
  have hhi := hmono h0 (h0.trans hle) hle
  rw [h00] at hlo
  rw [abs_of_nonneg hlo]
  exact hhi

/-- **The modified golden rule is efficient** (MWG, p. 756): with `f'(k_δ) = 1/δ > 1` it lies below
the golden rule, so (Exercise 20.E.3) its stationary path is efficient. -/
theorem modified_golden_rule_below {f : ℝ → ℝ} (hf : StrictConcaveOn ℝ (Set.Ici 0) f)
    {kd kh δ : ℝ} (hkd : 0 ≤ kd) (hkh : 0 ≤ kh) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hdd : HasDerivAt f (1 / δ) kd) (hdh : HasDerivAt f 1 kh) : kd < kh := by
  by_contra hle
  push Not at hle
  rcases eq_or_lt_of_le hle with rfl | hlt
  · have := hdd.unique hdh
    rw [div_eq_one_iff_eq hδ0.ne'] at this
    linarith
  · have := rate_neg_above_golden hf hkh hlt hdd hdh
    have : 1 < 1 / δ := by rw [lt_div_iff₀ hδ0]; linarith
    linarith

/-- **Exercise 20.E.4(i)** (MWG, p. 784): the steady-state surplus `c(k) = f(k) - k` increases
strictly up to the golden rule. -/
theorem exercise_20_E_4_i_mono {f : ℝ → ℝ} (hf : StrictConcaveOn ℝ (Set.Ici 0) f) {kh : ℝ}
    (hkh : 0 < kh) (hder : HasDerivAt f 1 kh) :
    StrictMonoOn (fun k => f k - k) (Set.Ici 0 ∩ Set.Iic kh) := by
  have hg : StrictConcaveOn ℝ (Set.Ici 0) (fun k => f k - k) := by
    have hneg : ConcaveOn ℝ (Set.Ici (0 : ℝ)) (fun k => -k) :=
      ⟨convex_Ici 0, fun x _ y _ a b _ _ _ => by simp only [smul_eq_mul]; nlinarith⟩
    convert hf.add_concaveOn hneg using 1
  refine strictMonoOn_left_of_max hg (Set.mem_Ici.2 hkh.le) fun x hx => ?_
  exact (golden_rule_iff hf.concaveOn hkh hder).2 (by ring) x hx

/-- **Exercise 20.E.4(i)** (MWG, p. 784): beyond the golden rule the surplus decreases strictly. -/
theorem exercise_20_E_4_i_anti {f : ℝ → ℝ} (hf : StrictConcaveOn ℝ (Set.Ici 0) f) {kh : ℝ}
    (hkh : 0 < kh) (hder : HasDerivAt f 1 kh) :
    StrictAntiOn (fun k => f k - k) (Set.Ici 0 ∩ Set.Ici kh) := by
  have hg : StrictConcaveOn ℝ (Set.Ici 0) (fun k => f k - k) := by
    have hneg : ConcaveOn ℝ (Set.Ici (0 : ℝ)) (fun k => -k) :=
      ⟨convex_Ici 0, fun x _ y _ a b _ _ _ => by simp only [smul_eq_mul]; nlinarith⟩
    convert hf.add_concaveOn hneg using 1
  refine strictAntiOn_right_of_max hg (Set.mem_Ici.2 hkh.le) fun x hx => ?_
  exact (golden_rule_iff hf.concaveOn hkh hder).2 (by ring) x hx

/-- **Exercise 20.E.4(ii)** (MWG, p. 784): the rate of interest `r(k) = f'(k) - 1` decreases
strictly with the level of capital. -/
theorem exercise_20_E_4_ii {f : ℝ → ℝ} (hf : StrictConcaveOn ℝ (Set.Ici 0) f) {k₁ k₂ d₁ d₂ : ℝ}
    (h₁ : 0 ≤ k₁) (h₁₂ : k₁ < k₂) (hd₁ : HasDerivAt f d₁ k₁) (hd₂ : HasDerivAt f d₂ k₂) :
    d₂ - 1 < d₁ - 1 := by
  have a := hf.slope_lt_of_hasDerivAt (Set.mem_Ici.2 h₁) (Set.mem_Ici.2 (h₁.trans h₁₂.le)) h₁₂
    hd₁
  have b := hf.lt_slope_of_hasDerivAt (Set.mem_Ici.2 h₁) (Set.mem_Ici.2 (h₁.trans h₁₂.le)) h₁₂
    hd₂
  linarith

/-- **Euler's theorem** for a production function homogeneous of degree one (used in Exercise
20.E.4(iii)): `∇F(x) · x = F(x)`. -/
theorem euler_homogeneous {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : E → ℝ}
    (hhom : ∀ c : ℝ, 0 < c → ∀ x, F (c • x) = c * F x) {x : E} {DF : E →L[ℝ] ℝ}
    (hDF : HasFDerivAt F DF x) : DF x = F x := by
  have h1 : HasDerivAt (fun c : ℝ => F (c • x)) (DF x) 1 := by
    have hl : HasDerivAt (fun c : ℝ => c • x) x 1 := by
      simpa using (hasDerivAt_id (1 : ℝ)).smul_const x
    exact hDF.comp_hasDerivAt_of_eq (1 : ℝ) hl (by simp)
  have h2 : HasDerivAt (fun c : ℝ => F (c • x)) (F x) 1 := by
    have : HasDerivAt (fun c : ℝ => c * F x) (F x) 1 := by
      simpa using (hasDerivAt_id (1 : ℝ)).mul_const (F x)
    refine this.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds (one_pos : (0 : ℝ) < 1)] with c hc using hhom c hc x
  exact h1.unique h2

/-- **Exercise 20.E.4(iii)** (MWG, p. 784): with constant returns, the real wage
`w(k) = ∇₂F(k, 1)/∇₁F(k, 1) = (f(k) - k f'(k))/f'(k)` increases strictly with capital (for `f`
strictly concave, nonnegative, with positive marginal product). First, Euler's theorem gives the
wage formula. -/
theorem exercise_20_E_4_iii_wage {F : (Fin 2 → ℝ) → ℝ}
    (hhom : ∀ c : ℝ, 0 < c → ∀ x, F (c • x) = c * F x) {k : ℝ} {DF : (Fin 2 → ℝ) →L[ℝ] ℝ}
    (hDF : HasFDerivAt F DF ![k, 1]) :
    DF (Pi.single 1 1) = F ![k, 1] - k * DF (Pi.single 0 1) := by
  have h := euler_homogeneous hhom hDF
  rw [clm_fin2_apply DF] at h
  simp at h
  linarith

/-- **Exercise 20.E.4(iii)** (MWG, p. 784): the wage-rental expression `f(k)/f'(k) - k` increases
strictly with `k` for `f` strictly concave and nonnegative on `ℝ_+` with positive derivatives. -/
theorem exercise_20_E_4_iii {f : ℝ → ℝ} (hf : StrictConcaveOn ℝ (Set.Ici 0) f)
    (hf0 : ∀ k, 0 ≤ k → 0 ≤ f k) {k₁ k₂ d₁ d₂ : ℝ} (h₁ : 0 ≤ k₁) (h₁₂ : k₁ < k₂)
    (hd₁ : HasDerivAt f d₁ k₁) (hd₂ : HasDerivAt f d₂ k₂) (hpos : 0 < d₂) :
    (f k₁ - k₁ * d₁) / d₁ < (f k₂ - k₂ * d₂) / d₂ := by
  have hd12 : d₂ < d₁ := by
    have := exercise_20_E_4_ii hf h₁ h₁₂ hd₁ hd₂; linarith
  have hd1 : 0 < d₁ := hpos.trans hd12
  -- the strict tangent inequality at `k₂`
  have htan : f k₁ < f k₂ + d₂ * (k₁ - k₂) := by
    have := hf.lt_slope_of_hasDerivAt (Set.mem_Ici.2 h₁) (Set.mem_Ici.2 (h₁.trans h₁₂.le)) h₁₂
      hd₂
    rw [slope_def_field, lt_div_iff₀ (by linarith)] at this
    linarith
  have hfk1 := hf0 k₁ h₁
  rw [div_lt_div_iff₀ hd1 hpos]
  nlinarith [mul_le_mul_of_nonneg_left hd12.le hfk1]

/-- **Exercise 20.E.8** (MWG, p. 785): with constant returns and labor growing at `n`, the
proportional path `k_t = (1 + n)^t k`, `l_t = (1 + n)^t` has surplus
`F(k_t, l_t) - k_{t+1} = (1 + n)^t (f(k) - (1 + n) k)`. -/
theorem exercise_20_E_8_surplus {F : (Fin 2 → ℝ) → ℝ}
    (hhom : ∀ c : ℝ, 0 < c → ∀ x, F (c • x) = c * F x) {n : ℝ} (hn : -1 < n) (k : ℝ) (t : ℕ) :
    F ![(1 + n) ^ t * k, (1 + n) ^ t] - (1 + n) ^ (t + 1) * k
      = (1 + n) ^ t * (F ![k, 1] - (1 + n) * k) := by
  have h : (![(1 + n) ^ t * k, (1 + n) ^ t] : Fin 2 → ℝ) = (1 + n) ^ t • ![k, 1] := by
    funext i; fin_cases i <;> simp
  rw [h, hhom _ (pow_pos (by linarith) t), pow_succ]
  ring

/-- **Exercise 20.E.8** (MWG, p. 785): among the proportional paths with growth `n`, the one
maximizing (normalized) surplus `f(k) - (1 + n) k` is characterized by `r = f'(k) - 1 = n` (the
golden rule with growth), for `f` concave and differentiable at an interior `k*`. -/
theorem exercise_20_E_8 {f : ℝ → ℝ} (hf : ConcaveOn ℝ (Set.Ici 0) f) {n ks f' : ℝ}
    (hks : 0 < ks) (hder : HasDerivAt f f' ks) :
    (∀ k, 0 ≤ k → f k - (1 + n) * k ≤ f ks - (1 + n) * ks) ↔ f' - 1 = n := by
  constructor
  · intro h
    have hloc : IsLocalMax (fun k => f k - (1 + n) * k) ks := by
      filter_upwards [Ioi_mem_nhds hks] with k hk using h k (le_of_lt hk)
    have := hloc.hasDerivAt_eq_zero (hder.sub ((hasDerivAt_id ks).const_mul (1 + n)))
    linarith
  · intro h k hk
    have := MWG.GeneralEquilibriumExamples.concave_le_tangent hf (Set.mem_Ici.2 hks.le)
      (Set.mem_Ici.2 hk) hder
    have hf1 : f' = 1 + n := by linarith
    rw [hf1] at this
    linarith

/-! ### The multisector model: (20.E.1) and Exercises 20.E.5-20.E.7 -/

/-- **(20.E.1)**, **Exercise 20.E.5** (MWG, p. 758): at a steady state `(k, k)` that maximizes the
short-run profit `s G(k_{t-1}, k_t) + q_t(k_t) - q_{t-1}(k_{t-1})` (consumption price `s`, capital
prices `q_{t-1}, q_t` as linear functionals), `∇₁G(k, k) = q_{t-1}/s` and
`∇₂G(k, k) = -q_t/s`. -/
theorem eq_20_E_1 {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K] {G : K × K → ℝ}
    {k : K} {DG : K × K →L[ℝ] ℝ} (hDG : HasFDerivAt G DG (k, k)) {s : ℝ}
    {q₀ q : K →L[ℝ] ℝ}
    (hmax : IsLocalMax (fun p : K × K => s * G p + q p.2 - q₀ p.1) (k, k)) :
    (∀ v, s * DG (v, 0) = q₀ v) ∧ (∀ v, s * DG (0, v) = -q v) := by
  have hd : HasFDerivAt (fun p : K × K => s * G p + q p.2 - q₀ p.1)
      (s • DG + q.comp (ContinuousLinearMap.snd ℝ K K) - q₀.comp (ContinuousLinearMap.fst ℝ K K))
      (k, k) :=
    ((hDG.const_mul s).add (q.hasFDerivAt.comp _ hasFDerivAt_snd)).sub
      (q₀.hasFDerivAt.comp _ hasFDerivAt_fst)
  have h0 := hmax.hasFDerivAt_eq_zero hd
  constructor
  · intro v
    have := congrArg (fun L => L (v, 0)) h0
    simp at this
    linarith
  · intro v
    have := congrArg (fun L => L (0, v)) h0
    simp at this
    linarith

/-- **(20.E.1) continued** (MWG, p. 758): with proportional prices `q_{t-1} = (1 + r) q_t`, the
marginal product of a permanent increase of capital is `∇Ĝ(k) = (r/s) q_t`, where
`Ĝ(k) = G(k, k)`; hence the steady state maximizes consumption (`∇Ĝ = 0`) if and only if `r = 0`
(for `s ≠ 0`, `q_t ≠ 0`): the golden rule property. -/
theorem golden_rule_multisector {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]
    {DG : K × K →L[ℝ] ℝ} {s r : ℝ} (hs : s ≠ 0) {q : K →L[ℝ] ℝ}
    (h1 : ∀ v, s * DG (v, 0) = (1 + r) * q v) (h2 : ∀ v, s * DG (0, v) = -q v) :
    (∀ v, DG (v, v) = r / s * q v) ∧ ((∀ v, DG (v, v) = 0) ↔ (q = 0 ∨ r = 0)) := by
  have hdiag : ∀ v, DG (v, v) = r / s * q v := by
    intro v
    have hsplit : DG (v, v) = DG (v, 0) + DG (0, v) := by
      rw [← map_add, Prod.mk_add_mk, add_zero, zero_add]
    rw [hsplit]
    have e1 := h1 v
    have e2 := h2 v
    field_simp
    linarith
  refine ⟨hdiag, ⟨fun h => ?_, fun h => ?_⟩⟩
  · by_contra hc
    push Not at hc
    obtain ⟨hq, hr⟩ := hc
    obtain ⟨v, hv⟩ : ∃ v, q v ≠ 0 := by
      by_contra h'; push Not at h'; exact hq (ContinuousLinearMap.ext h')
    have := h v
    rw [hdiag v] at this
    rcases mul_eq_zero.1 this with h' | h'
    · exact hr (by rcases div_eq_zero_iff.1 h' with h'' | h'' <;> [exact h''; exact absurd h'' hs])
    · exact hv h'
  · intro v
    rw [hdiag v]
    rcases h with rfl | rfl <;> simp

/-- **Exercise 20.E.6** (MWG, p. 785): in the two-sector model (one capital good), at a supported
steady state the slope `-∇₁G/∇₂G` of the level curve of `G` through `(k, k)` equals
`q_{t-1}/q_t = 1 + r(k)`. -/
theorem exercise_20_E_6 {G1 G2 s q₀ q : ℝ} (hs : s ≠ 0) (hq : q ≠ 0) (h1 : s * G1 = q₀)
    (h2 : s * G2 = -q) : -G1 / G2 = q₀ / q := by
  have hG2 : G2 ≠ 0 := by intro h; rw [h, mul_zero] at h2; exact hq (by linarith)
  rw [div_eq_div_iff hG2 hq]
  have : G1 = q₀ / s := by field_simp; linarith
  have : G2 = -q / s := by field_simp; linarith
  subst_vars
  field_simp

/-- **Exercise 20.E.7** (MWG, p. 785): if consumption and investment goods are perfect substitutes
in production, `G(k, k' + a) = G(k, k') - a`, then `G(k, k') = H(k) - k'` with `H(k) = G(k, 0)`,
the interest rate of a steady state is `r(k) = H'(k) - 1`, and for `H` strictly concave two
different steady states have different rates of interest. -/
theorem exercise_20_E_7 {G : ℝ → ℝ → ℝ} (hsub : ∀ k k' a, G k (k' + a) = G k k' - a)
    (hH : StrictConcaveOn ℝ (Set.Ici 0) (fun k => G k 0)) {k₁ k₂ d₁ d₂ : ℝ} (h₁ : 0 ≤ k₁)
    (h₂ : 0 ≤ k₂) (hne : k₁ ≠ k₂) (hd₁ : HasDerivAt (fun k => G k 0) d₁ k₁)
    (hd₂ : HasDerivAt (fun k => G k 0) d₂ k₂) :
    (∀ k k', G k k' = G k 0 - k') ∧ d₁ - 1 ≠ d₂ - 1 := by
  refine ⟨fun k k' => by simpa using hsub k 0 k', fun h => ?_⟩
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have := exercise_20_E_4_ii hH h₁ hlt hd₁ hd₂; linarith
  · have := exercise_20_E_4_ii hH h₂ hgt hd₂ hd₁; linarith

end MWG.EquilibriumTime
