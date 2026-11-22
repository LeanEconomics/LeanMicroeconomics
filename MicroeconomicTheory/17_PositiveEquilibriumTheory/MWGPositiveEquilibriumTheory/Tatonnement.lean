/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPositiveEquilibriumTheory.GrossSubstitutes
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Topology.MetricSpace.Sequences

/-!
# Price tâtonnement and global stability (MWG Section 17.H, pp. 620-624)

* **(17.H.1)** (`IsTatPath`): a tâtonnement trajectory is a function `p : ℝ → ℝ^L` with
  `p(t) ≫ 0` and `dpₗ/dt = cₗ zₗ(p(t))` (`cₗ > 0`) for all `t ≥ 0` (one-sided at `t = 0`).
* p. 622: by Walras' law `∑ₗ pₗ(t)²/cₗ` is constant along a trajectory (`tat_wNormSq_const`);
  with `c = (1, …, 1)` the trajectory stays on the sphere `S` (`tat_sphere_invariant`).
* **Proposition 17.H.1** (`proposition_17_H_1`): if `z(p*) = 0` and `p*·z(p) > 0` for every
  `p ≫ 0` not proportional to `p*`, every trajectory converges to the point `λp*` of the ray of
  `p*` with the same weighted norm, so relative prices converge (`proposition_17_H_1_relative`).
  The distance `∑ₗ (1/cₗ)(pₗ(t) - αp*ₗ)²` to every point of the ray is nonincreasing
  (`proposition_17_H_1_monotone`). The proof is a Lyapunov argument (`tat_lyapunov_core`):
  the distance decreases at rate `2λ p*·z(p(t))`, and a compactness argument with the boundary
  behaviour of Proposition 17.B.2 bounds `p*·z(p)` below away from the ray (`tat_unif_pos`).
  Departure: the book's proof uses only the displayed hypothesis; the convergence step uses
  continuity, Walras' law and properties (iv)-(v) of Proposition 17.B.2, which excess demand
  functions satisfy (p. 582). The printed derivative drops a factor `2` (it does not affect the
  sign).
* The gross substitute case (`tat_global_stability_gs`) and the weak axiom case with a unique
  equilibrium ray (`tat_global_stability_wa`) (p. 623).
-/

namespace MWG.PositiveEquilibriumTheory

open Filter Topology Set

variable {L : ℕ}

/-! ### The tâtonnement dynamics (17.H.1) -/

/-- **(17.H.1)** (MWG, p. 621). The tâtonnement vector field `(cₗ zₗ(p))ₗ`. -/
def tatField (c : Fin L → ℝ) (z : (Fin L → ℝ) → Fin L → ℝ) (q : Fin L → ℝ) : Fin L → ℝ :=
  fun l => c l * z q l

/-- **(17.H.1)** (MWG, p. 621). `p : ℝ → ℝ^L` is a tâtonnement trajectory for the excess demand
`z` and the speeds of adjustment `c`: for every `t ≥ 0`, `p(t) ≫ 0` (where `z` is defined) and
`dpₗ(t)/dt = cₗ zₗ(p(t))` (the derivative is one-sided at the initial time `t = 0`). -/
def IsTatPath (c : Fin L → ℝ) (z : (Fin L → ℝ) → Fin L → ℝ) (p : ℝ → Fin L → ℝ) : Prop :=
  (∀ t, 0 ≤ t → p t ∈ posOrthant L) ∧
    ∀ t, 0 ≤ t → HasDerivWithinAt p (tatField c z (p t)) (Ici 0) t

/-- The weighted squared norm `∑ₗ qₗ²/cₗ`. -/
noncomputable def wNormSq (c q : Fin L → ℝ) : ℝ := ∑ l, q l ^ 2 / c l

/-- The weighted inner product `∑ₗ rₗ qₗ/cₗ`. -/
noncomputable def wInner (c r q : Fin L → ℝ) : ℝ := ∑ l, r l * q l / c l

theorem wNormSq_nonneg {c : Fin L → ℝ} (hc : ∀ l, 0 < c l) (q : Fin L → ℝ) :
    0 ≤ wNormSq c q :=
  Finset.sum_nonneg fun l _ => div_nonneg (sq_nonneg _) (hc l).le

/-- Each coordinate is bounded by the weighted norm: `qₗ² ≤ cₗ ∑ₖ qₖ²/cₖ`. -/
theorem sq_le_wNormSq {c : Fin L → ℝ} (hc : ∀ l, 0 < c l) (q : Fin L → ℝ) (l : Fin L) :
    q l ^ 2 ≤ c l * wNormSq c q := by
  have h : q l ^ 2 / c l ≤ wNormSq c q :=
    Finset.single_le_sum (f := fun k => q k ^ 2 / c k)
      (fun k _ => div_nonneg (sq_nonneg _) (hc k).le) (Finset.mem_univ l)
  rw [div_le_iff₀ (hc l)] at h
  linarith

theorem wNormSq_smul (c q : Fin L → ℝ) (a : ℝ) : wNormSq c (a • q) = a ^ 2 * wNormSq c q := by
  simp only [wNormSq, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by ring

theorem wInner_smul_left (c r q : Fin L → ℝ) (a : ℝ) :
    wInner c (a • r) q = a * wInner c r q := by
  simp only [wInner, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by ring

/-- `|q - r|²_c = |q|²_c - 2⟨r, q⟩_c + |r|²_c`. -/
theorem wNormSq_sub (c q r : Fin L → ℝ) :
    wNormSq c (q - r) = wNormSq c q - 2 * wInner c r q + wNormSq c r := by
  simp only [wNormSq, wInner, Pi.sub_apply, ← Finset.sum_sub_distrib, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun l _ => by ring

theorem wNormSq_pos {c : Fin L → ℝ} (hc : ∀ l, 0 < c l) {q : Fin L → ℝ} (hq : q ≠ 0) :
    0 < wNormSq c q := by
  obtain ⟨l, hl⟩ : ∃ l, q l ≠ 0 := by
    by_contra h
    push Not at h
    exact hq (funext h)
  exact lt_of_lt_of_le (div_pos (by positivity) (hc l))
    (Finset.single_le_sum (f := fun k => q k ^ 2 / c k)
      (fun k _ => div_nonneg (sq_nonneg _) (hc k).le) (Finset.mem_univ l))

theorem wNormSq_eq_zero {c : Fin L → ℝ} (hc : ∀ l, 0 < c l) {q : Fin L → ℝ}
    (h : wNormSq c q = 0) : q = 0 := by
  by_contra hq
  exact (wNormSq_pos hc hq).ne' h

theorem continuous_wNormSq (c : Fin L → ℝ) : Continuous (wNormSq c) := by
  unfold wNormSq
  fun_prop

/-- A strictly positive vector is nonzero (when `L ≥ 1`). -/
theorem posOrthant_ne_zero [NeZero L] {q : Fin L → ℝ} (hq : q ∈ posOrthant L) : q ≠ 0 :=
  fun h => by simpa [h] using hq 0

/-! ### Derivatives along a trajectory -/

variable {c : Fin L → ℝ} {z : (Fin L → ℝ) → Fin L → ℝ} {p : ℝ → Fin L → ℝ}

/-- Along a trajectory, `dpₗ/dt = cₗ zₗ(p(t))`, coordinatewise. -/
theorem tat_coord (hp : IsTatPath c z p) {t : ℝ} (ht : 0 ≤ t) (l : Fin L) :
    HasDerivWithinAt (fun s => p s l) (c l * z (p t) l) (Ici 0) t :=
  hasDerivWithinAt_pi.1 (hp.2 t ht) l

/-- A trajectory is continuous on `[0, ∞)`. -/
theorem tat_continuousOn (hp : IsTatPath c z p) : ContinuousOn p (Ici 0) :=
  fun t ht => (hp.2 t ht).continuousWithinAt

/-- Along any solution of `dq/dt = (cₗ zₗ(q))ₗ` (within any set of times),
`d⟨r, q(t)⟩_c/dt = r·z(q(t))`. -/
theorem tatField_hasDeriv_wInner (hc : ∀ l, 0 < c l) {α : ℝ → Fin L → ℝ} {s : Set ℝ} {t : ℝ}
    (hα : HasDerivWithinAt α (tatField c z (α t)) s t) (r : Fin L → ℝ) :
    HasDerivWithinAt (fun u => wInner c r (α u)) (r ⬝ᵥ z (α t)) s t := by
  have h := HasDerivWithinAt.fun_sum (u := Finset.univ) (A := fun l u => r l * α u l / c l)
    (A' := fun l => r l * (c l * z (α t) l) / c l)
    fun l _ => ((hasDerivWithinAt_pi.1 hα l).const_mul (r l)).div_const (c l)
  have heq : ∑ l, r l * (c l * z (α t) l) / c l = r ⬝ᵥ z (α t) := by
    simp only [dotProduct]
    exact Finset.sum_congr rfl fun l _ => by field_simp [(hc l).ne']
  rw [heq] at h
  simpa [wInner] using h

/-- Along any solution of `dq/dt = (cₗ zₗ(q))ₗ`, `d|q(t)|²_c/dt = 2 q(t)·z(q(t))`. -/
theorem tatField_hasDeriv_wNormSq (hc : ∀ l, 0 < c l) {α : ℝ → Fin L → ℝ} {s : Set ℝ} {t : ℝ}
    (hα : HasDerivWithinAt α (tatField c z (α t)) s t) :
    HasDerivWithinAt (fun u => wNormSq c (α u)) (2 * (α t ⬝ᵥ z (α t))) s t := by
  have h := HasDerivWithinAt.fun_sum (u := Finset.univ) (A := fun l u => α u l ^ 2 / c l)
    (A' := fun l => (2 * α t l * (c l * z (α t) l)) / c l)
    fun l _ => by
      have := ((hasDerivWithinAt_pi.1 hα l).pow 2).div_const (c l)
      simpa [tatField, mul_comm, mul_assoc, mul_left_comm] using this
  have heq : ∑ l, 2 * α t l * (c l * z (α t) l) / c l = 2 * (α t ⬝ᵥ z (α t)) := by
    simp only [dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by field_simp [(hc l).ne']
  rw [heq] at h
  simpa [wNormSq] using h

/-- `d⟨r, p(t)⟩_c/dt = r·z(p(t))`. -/
theorem tat_hasDeriv_wInner (hc : ∀ l, 0 < c l) (hp : IsTatPath c z p) (r : Fin L → ℝ)
    {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => wInner c r (p s)) (r ⬝ᵥ z (p t)) (Ici 0) t :=
  tatField_hasDeriv_wInner hc (hp.2 t ht) r

/-- `d|p(t)|²_c/dt = 2 p(t)·z(p(t))`. -/
theorem tat_hasDeriv_wNormSq (hc : ∀ l, 0 < c l) (hp : IsTatPath c z p) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => wNormSq c (p s)) (2 * (p t ⬝ᵥ z (p t))) (Ici 0) t :=
  tatField_hasDeriv_wNormSq hc (hp.2 t ht)

/-- A function with nonnegative (one-sided) derivative on `[0, ∞)` is nondecreasing there. -/
theorem tat_monotoneOn {F F' : ℝ → ℝ} (hF : ∀ t, 0 ≤ t → HasDerivWithinAt F (F' t) (Ici 0) t)
    (hF' : ∀ t, 0 ≤ t → 0 ≤ F' t) : MonotoneOn F (Ici 0) := by
  intro a ha b hb hab
  have ha' : (0 : ℝ) ≤ a := ha
  have hcont : ContinuousOn (fun x => -F x) (Icc a b) := fun x hx =>
    ((hF x (ha'.trans hx.1)).continuousWithinAt.mono
      fun y hy => ha'.trans hy.1).neg
  have h := image_le_of_deriv_right_le_deriv_boundary (f := fun x => -F x) (f' := fun x => -F' x)
    (B := fun _ => -F a) (B' := fun _ => 0) hcont
    (fun x hx => ((hF x (ha'.trans hx.1)).mono fun y (hy : x ≤ y) =>
      (show (0 : ℝ) ≤ y from (ha'.trans hx.1).trans hy)).neg)
    le_rfl continuousOn_const (fun _ _ => hasDerivWithinAt_const _ _ _)
    (fun x hx => neg_nonpos.2 (hF' x (ha'.trans hx.1))) ⟨hab, le_rfl⟩
  simpa using h

/-- **Section 17.H** (MWG, p. 622). By Walras' law the weighted norm `∑ₗ pₗ(t)²/cₗ` is constant
along every trajectory. -/
theorem tat_wNormSq_const (hc : ∀ l, 0 < c l) (hW : EDWalrasLaw z) (hp : IsTatPath c z p)
    {t : ℝ} (ht : 0 ≤ t) : wNormSq c (p t) = wNormSq c (p 0) := by
  have hd : ∀ s, 0 ≤ s → HasDerivWithinAt (fun s => wNormSq c (p s)) 0 (Ici 0) s := by
    intro s hs
    have := tat_hasDeriv_wNormSq hc hp hs
    rwa [hW _ (hp.1 s hs), mul_zero] at this
  have h1 := tat_monotoneOn hd (fun _ _ => le_rfl) (Set.mem_Ici.2 le_rfl) ht ht
  have h2 := tat_monotoneOn (F := fun s => -wNormSq c (p s)) (F' := fun _ => 0)
    (fun s hs => by simpa using (hd s hs).fun_neg) (fun _ _ => le_rfl)
    (Set.mem_Ici.2 le_rfl) ht ht
  simp only at h1 h2
  linarith

/-- **Section 17.H** (MWG, p. 622). With `c = (1, …, 1)`, Walras' law gives
`d(∑ₗ pₗ(t)²)/dt = 2 ∑ₗ pₗ(t) zₗ(p(t)) = 0`: if `p(0)` lies on the sphere
`S = {p ≫ 0 : ∑ₗ pₗ² = 1}`, so does `p(t)` for every `t ≥ 0`. -/
theorem tat_sphere_invariant (hW : EDWalrasLaw z) (hp : IsTatPath (fun _ => 1) z p)
    (h0 : ∑ l, p 0 l ^ 2 = 1) {t : ℝ} (ht : 0 ≤ t) :
    p t ∈ posOrthant L ∧ ∑ l, p t l ^ 2 = 1 := by
  refine ⟨hp.1 t ht, ?_⟩
  have := tat_wNormSq_const (fun _ => one_pos) hW hp ht
  simpa [wNormSq, h0] using this


/-! ### The Lyapunov argument of Proposition 17.H.1 -/

/-- **Proposition 17.H.1**, the Lyapunov argument (MWG, pp. 623-624). Let `p̄ = λp*` be the point
of the ray of `p* ≫ 0` with the weighted norm of `p(0)`, and `f(q) = ∑ₗ (1/cₗ)(qₗ - p̄ₗ)²`.
Suppose `p*·z(q) > 0` at every `q ≫ 0 ≠ p̄` of the same weighted norm with `f(q) < ρ'` for some
`ρ' > f(p(0))`, uniformly away from `p̄` on `{f ≤ f(p(0))}`. Then `f(p(t))` is nonincreasing and
`p(t) → p̄`. -/
theorem tat_lyapunov_core (hc : ∀ l, 0 < c l) (hW : EDWalrasLaw z) (hp : IsTatPath c z p)
    {ps : Fin L → ℝ} {lam : ℝ} (hlam : 0 < lam)
    (hN : wNormSq c (lam • ps) = wNormSq c (p 0)) {ρ' : ℝ}
    (hρ' : wNormSq c (p 0 - lam • ps) < ρ')
    (hpos : ∀ q ∈ posOrthant L, wNormSq c q = wNormSq c (p 0) →
      wNormSq c (q - lam • ps) < ρ' → q ≠ lam • ps → 0 < ps ⬝ᵥ z q)
    (hunif : ∀ ε > 0, ∃ δ > 0, ∀ q ∈ posOrthant L, wNormSq c q = wNormSq c (p 0) →
      ε ≤ wNormSq c (q - lam • ps) → wNormSq c (q - lam • ps) ≤ wNormSq c (p 0 - lam • ps) →
      δ ≤ ps ⬝ᵥ z q) :
    AntitoneOn (fun t => wNormSq c (p t - lam • ps)) (Ici 0) ∧
      Tendsto p atTop (𝓝 (lam • ps)) := by
  set N0 := wNormSq c (p 0) with hN0
  set pb := lam • ps with hpb
  set ρ := wNormSq c (p 0 - pb) with hρ
  set F : ℝ → ℝ := fun t => wNormSq c (p t - pb) with hF
  set H : ℝ → ℝ := fun t => wInner c ps (p t) with hH
  have hNt : ∀ t, 0 ≤ t → wNormSq c (p t) = N0 := fun t ht => tat_wNormSq_const hc hW hp ht
  have hFH : ∀ t, 0 ≤ t → F t = 2 * N0 - 2 * lam * H t := by
    intro t ht
    simp only [hF, hH, wNormSq_sub, hNt t ht, hpb, wInner_smul_left]
    rw [← hpb, hN]
    ring
  have hFd : ∀ t, 0 ≤ t →
      HasDerivWithinAt F (-(2 * lam * (ps ⬝ᵥ z (p t)))) (Ici 0) t := by
    intro t ht
    have h := ((tat_hasDeriv_wInner hc hp ps ht).const_mul (2 * lam)).const_sub (2 * N0)
    exact h.congr_of_mem (fun y hy => hFH y hy) ht
  have hFcont : ∀ T, ContinuousOn F (Icc 0 T) := fun T x hx =>
    (hFd x hx.1).continuousWithinAt.mono fun y hy => hy.1
  have hF0 : ∀ t, 0 ≤ F t := fun t => wNormSq_nonneg hc _
  have hρ0 : 0 ≤ ρ := hF0 0
  -- the trajectory never leaves the sublevel set `{f ≤ f(p(0))}`
  have hFle : ∀ t, 0 ≤ t → F t ≤ ρ := by
    intro T hT
    have hε : ∀ ε, 0 < ε → ρ + ε < ρ' → F T ≤ ρ + ε := by
      intro ε hε hερ
      refine image_le_of_deriv_right_lt_deriv_boundary' (f := F)
        (f' := fun t => -(2 * lam * (ps ⬝ᵥ z (p t)))) (B := fun _ => ρ + ε) (B' := fun _ => 0)
        (hFcont T) (fun x hx => (hFd x hx.1).mono fun y (hy : x ≤ y) => hx.1.trans hy)
        (by simp only [hF, hρ]; linarith) continuousOn_const
        (fun _ _ => hasDerivWithinAt_const _ _ _) ?_ ⟨hT, le_rfl⟩
      intro x hx hFx
      have hne : p x ≠ pb := by
        intro h
        have : F x = 0 := by simp [hF, h, wNormSq]
        linarith
      have := hpos (p x) (hp.1 x hx.1) (hNt x hx.1) (by simp only [hF] at hFx; linarith) hne
      nlinarith
    by_contra hcon
    push Not at hcon
    set ε := min (F T - ρ) (ρ' - ρ) / 2 with hεdef
    have hε0 : 0 < ε := by
      have : 0 < min (F T - ρ) (ρ' - ρ) := lt_min (by linarith) (by linarith)
      linarith
    have h1 : ε < F T - ρ := by
      have := min_le_left (F T - ρ) (ρ' - ρ)
      linarith
    have h2 : ρ + ε < ρ' := by
      have := min_le_right (F T - ρ) (ρ' - ρ)
      linarith
    have := hε ε hε0 h2
    linarith
  -- `p*·z(p(t)) ≥ 0` along the trajectory
  have hg : ∀ t, 0 ≤ t → 0 ≤ ps ⬝ᵥ z (p t) := by
    intro t ht
    by_cases h : p t = pb
    · have hw := hW pb (h ▸ hp.1 t ht)
      rw [h]
      rw [hpb, smul_dotProduct, smul_eq_mul] at hw
      exact ((mul_eq_zero.1 hw).resolve_left hlam.ne').ge
    · exact (hpos (p t) (hp.1 t ht) (hNt t ht) (lt_of_le_of_lt (hFle t ht) hρ') h).le
  have hHmono : MonotoneOn H (Ici 0) :=
    tat_monotoneOn (fun t ht => tat_hasDeriv_wInner hc hp ps ht) hg
  have hFanti : AntitoneOn F (Ici 0) := by
    intro a ha b hb hab
    rw [hFH a ha, hFH b hb]
    have := hHmono ha hb hab
    nlinarith
  refine ⟨hFanti, ?_⟩
  -- `f(p(t))` eventually drops below every `ε > 0`
  have hsmall : ∀ ε > 0, ∃ T, 0 ≤ T ∧ F T < ε := by
    intro ε hε
    by_contra hcon
    push Not at hcon
    obtain ⟨δ, hδ, hδq⟩ := hunif ε hε
    have hgδ : ∀ t, 0 ≤ t → δ ≤ ps ⬝ᵥ z (p t) := fun t ht =>
      hδq (p t) (hp.1 t ht) (hNt t ht) (hcon t ht) (hFle t ht)
    have hG : MonotoneOn (fun t => H t - δ * t) (Ici 0) := by
      refine tat_monotoneOn (F' := fun t => ps ⬝ᵥ z (p t) - δ)
        (fun t ht => ?_) (fun t ht => by linarith [hgδ t ht])
      have := (tat_hasDeriv_wInner hc hp ps ht).fun_sub
        ((hasDerivWithinAt_id t (Ici 0)).const_mul δ)
      simpa using this
    have hHb : ∀ t, 0 ≤ t → H t ≤ N0 / lam := by
      intro t ht
      rw [le_div_iff₀ hlam]
      have := hF0 t
      rw [hFH t ht] at this
      nlinarith
    set T := max 0 ((N0 / lam - H 0) / δ + 1) with hT
    have hT0 : 0 ≤ T := le_max_left _ _
    have h1 := hG (Set.mem_Ici.2 le_rfl) hT0 hT0
    have h2 := hHb T hT0
    have h3 : (N0 / lam - H 0) / δ + 1 ≤ T := le_max_right _ _
    have h4 : N0 / lam - H 0 < δ * T := by
      have : (N0 / lam - H 0) / δ < T := by linarith
      rwa [div_lt_iff₀ hδ, mul_comm] at this
    simp only [mul_zero, sub_zero] at h1
    linarith
  refine tendsto_pi_nhds.2 fun l => Metric.tendsto_atTop.2 fun ε hε => ?_
  obtain ⟨T, hT0, hT⟩ := hsmall (ε ^ 2 / c l) (by have := hc l; positivity)
  refine ⟨T, fun t ht => ?_⟩
  have h1 : F t ≤ F T := hFanti hT0 (hT0.trans ht) ht
  have h2 := sq_le_wNormSq hc (p t - pb) l
  have h3 : (p t l - pb l) ^ 2 < ε ^ 2 := by
    have : c l * F t < ε ^ 2 := by
      have := mul_lt_mul_of_pos_left (lt_of_le_of_lt h1 hT) (hc l)
      rwa [mul_div_cancel₀ _ (hc l).ne'] at this
    simp only [hF, Pi.sub_apply] at this h2
    linarith
  rw [Real.dist_eq]
  exact abs_lt_of_sq_lt_sq h3 hε.le


/-- **Proposition 17.H.1**, the compactness step. If `z` is continuous on `ℝ^L_{++}`, bounded
below and satisfies the boundary condition (Proposition 17.B.2(i), (iv), (v)), and `p*·z(q) > 0`
for every `q ≫ 0` of weighted norm `N₀ > 0` other than `p̄`, then `p*·z(q)` is bounded below by a
positive constant on `{q ≫ 0 : |q|²_c = N₀, |q - p̄|²_c ≥ ε}`, for every `ε > 0`. -/
theorem tat_unif_pos (hc : ∀ l, 0 < c l) (hz : EDContinuous z) (hB : EDBoundedBelow z)
    (hBd : EDBoundary z) {ps : Fin L → ℝ} (hps : ps ∈ posOrthant L) {N0 : ℝ} (hN0 : 0 < N0)
    {pb : Fin L → ℝ}
    (hstrict : ∀ q ∈ posOrthant L, wNormSq c q = N0 → q ≠ pb → 0 < ps ⬝ᵥ z q) :
    ∀ ε > 0, ∃ δ > 0, ∀ q ∈ posOrthant L, wNormSq c q = N0 → ε ≤ wNormSq c (q - pb) →
      δ ≤ ps ⬝ᵥ z q := by
  intro ε hε
  by_contra hcon
  push Not at hcon
  have hex : ∀ n : ℕ, ∃ q, q ∈ posOrthant L ∧ wNormSq c q = N0 ∧ ε ≤ wNormSq c (q - pb) ∧
      ps ⬝ᵥ z q < 1 / ((n : ℝ) + 1) := fun n => by
    obtain ⟨q, hq, h1, h2, h3⟩ := hcon (1 / ((n : ℝ) + 1)) (by positivity)
    exact ⟨q, hq, h1, h2, h3⟩
  choose qs hqs hqN hqε hqg using hex
  set K : Set (Fin L → ℝ) := {q | (∀ l, 0 ≤ q l) ∧ wNormSq c q = N0} with hK
  have hKcl : IsClosed K := by
    have : K = (⋂ l, {q : Fin L → ℝ | 0 ≤ q l}) ∩ {q | wNormSq c q = N0} := by
      ext q; simp [hK]
    rw [this]
    exact (isClosed_iInter fun l => isClosed_le continuous_const (continuous_apply l)).inter
      (isClosed_eq (continuous_wNormSq c) continuous_const)
  set R := ∑ l, Real.sqrt (c l * N0) with hR
  have hKb : Bornology.IsBounded K := by
    refine (Metric.isBounded_closedBall (x := (0 : Fin L → ℝ)) (r := R)).subset fun q hq => ?_
    rw [mem_closedBall_zero_iff]
    refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun l _ => Real.sqrt_nonneg _)).2
      fun l => ?_
    have h1 : |q l| ≤ Real.sqrt (c l * N0) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt (hq.2 ▸ sq_le_wNormSq hc q l)
    have h2 : Real.sqrt (c l * N0) ≤ R :=
      Finset.single_le_sum (f := fun k => Real.sqrt (c k * N0)) (fun k _ => Real.sqrt_nonneg _)
        (Finset.mem_univ l)
    rw [Real.norm_eq_abs]
    linarith
  obtain ⟨a, haK, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded hKb
    (fun n => (⟨fun l => (hqs n l).le, hqN n⟩ : qs n ∈ K))
  rw [hKcl.closure_eq] at haK
  have hfa : ε ≤ wNormSq c (a - pb) :=
    ge_of_tendsto (((continuous_wNormSq c).comp (continuous_id.sub continuous_const)).tendsto
      a |>.comp hlim) (Eventually.of_forall fun n => hqε (φ n))
  have hsmall : Tendsto (fun n => 1 / ((φ n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
  by_cases ha : a ∈ posOrthant L
  · have hca : ContinuousAt (fun q => ps ⬝ᵥ z q) a := by
      have := (hz a ha).continuousAt ((isOpen_posOrthant L).mem_nhds ha)
      exact (continuous_const.dotProduct continuous_id).continuousAt.comp this
    have hle : ps ⬝ᵥ z a ≤ 0 :=
      le_of_tendsto_of_tendsto' (hca.tendsto.comp hlim) hsmall fun n => (hqg (φ n)).le
    have hne : a ≠ pb := by
      intro h
      rw [h, sub_self] at hfa
      simp [wNormSq] at hfa
      linarith
    exact absurd (hstrict a ha haK.2 hne) (not_lt.2 hle)
  · obtain ⟨l0, hl0⟩ : ∃ l, a l = 0 := by
      by_contra h
      push Not at h
      exact ha fun l => lt_of_le_of_ne (haK.1 l) (Ne.symm (h l))
    have hane : a ≠ 0 := by
      intro h
      have := haK.2
      rw [h] at this
      simp [wNormSq] at this
      linarith
    obtain ⟨s, hs, hsz⟩ := hB
    have : Nonempty (Fin L) := ⟨l0⟩
    obtain ⟨k0, -, hk0⟩ := Finset.exists_min_image Finset.univ ps Finset.univ_nonempty
    set m := ps k0 with hm
    have hmpos : 0 < m := hps k0
    set S := ∑ k, ps k with hS
    have hSpos : 0 ≤ S := Finset.sum_nonneg fun k _ => (hps k).le
    set M := (s * S + 1) / m with hM
    have hM0 : 0 ≤ M := div_nonneg (by positivity) hmpos.le
    have hev := hBd (qs ∘ φ) a (fun n => hqs (φ n)) hlim hane ⟨l0, hl0⟩ M
    obtain ⟨n, l, hl⟩ := hev.exists
    set q := qs (φ n) with hq
    have hterm : ∀ k, 0 ≤ ps k * (z q k + s) := fun k =>
      mul_nonneg (hps k).le (by linarith [hsz q (hqs (φ n)) k])
    have h1 : ps l * (z q l + s) ≤ ∑ k, ps k * (z q k + s) :=
      Finset.single_le_sum (f := fun k => ps k * (z q k + s)) (fun k _ => hterm k)
        (Finset.mem_univ l)
    have h2 : ∑ k, ps k * (z q k + s) = ps ⬝ᵥ z q + s * S := by
      simp only [dotProduct, mul_add, Finset.sum_add_distrib, hS, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun k _ => by ring
    have h3 : m * M = s * S + 1 := by
      rw [hM]; field_simp
    have h4 : m * M ≤ ps l * M := mul_le_mul_of_nonneg_right (hk0 l (Finset.mem_univ l)) hM0
    have h5 : ps l * M < ps l * (z q l + s) := by
      have := mul_lt_mul_of_pos_left (show M < z q l + s by
        simp only [Function.comp_apply] at hl; linarith) (hps l)
      exact this
    have h6 : ps ⬝ᵥ z q < 1 := lt_of_lt_of_le (hqg (φ n))
      (by rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg (φ n) : (0 : ℝ) ≤ φ n)])
    linarith

/-- Along a trajectory, `p*·z(p(t)) ≥ 0` when `p*·z(q) > 0` off the ray of `p*` (on the ray it
vanishes by Walras' law). -/
theorem tat_g_nonneg (hW : EDWalrasLaw z) (hp : IsTatPath c z p) {ps : Fin L → ℝ}
    (hstab : ∀ q ∈ posOrthant L, (¬ ∃ α : ℝ, 0 < α ∧ q = α • ps) → 0 < ps ⬝ᵥ z q)
    {t : ℝ} (ht : 0 ≤ t) : 0 ≤ ps ⬝ᵥ z (p t) := by
  by_cases h : ∃ α : ℝ, 0 < α ∧ p t = α • ps
  · obtain ⟨α, hα, hpt⟩ := h
    have hw := hW _ (hp.1 t ht)
    rw [hpt, smul_dotProduct, smul_eq_mul] at hw
    rw [hpt]
    exact ((mul_eq_zero.1 hw).resolve_left hα.ne').ge
  · exact (hstab _ (hp.1 t ht) h).le

/-- **Proposition 17.H.1**, the derivative computation (MWG, p. 624). With
`f(p) = ∑ₗ (1/cₗ)(pₗ - p*ₗ)²`, `d f(p(t))/dt = -2 p*·z(p(t))` (the book prints the second line
without the factor `2`), and this is `< 0` iff `p(t)` is not proportional to `p*`. -/
theorem proposition_17_H_1_deriv (hc : ∀ l, 0 < c l) (hW : EDWalrasLaw z)
    (hp : IsTatPath c z p) {ps : Fin L → ℝ}
    (hstab : ∀ q ∈ posOrthant L, (¬ ∃ α : ℝ, 0 < α ∧ q = α • ps) → 0 < ps ⬝ᵥ z q)
    {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => wNormSq c (p s - ps)) (-(2 * (ps ⬝ᵥ z (p t)))) (Ici 0) t ∧
      (-(2 * (ps ⬝ᵥ z (p t))) < 0 ↔ ¬ ∃ α : ℝ, 0 < α ∧ p t = α • ps) := by
  refine ⟨?_, ?_⟩
  · have h := ((tat_hasDeriv_wNormSq hc hp ht).sub
      ((tat_hasDeriv_wInner hc hp ps ht).const_mul 2)).add_const (wNormSq c ps)
    rw [hW _ (hp.1 t ht)] at h
    have hfun : (fun s => wNormSq c (p s - ps)) =
        fun s => wNormSq c (p s) - 2 * wInner c ps (p s) + wNormSq c ps :=
      funext fun s => wNormSq_sub c (p s) ps
    rw [hfun]
    convert h using 1
    ring
  · constructor
    · intro h ⟨α, hα, hpt⟩
      have hw := hW _ (hp.1 t ht)
      rw [hpt, smul_dotProduct, smul_eq_mul] at hw
      rw [hpt, (mul_eq_zero.1 hw).resolve_left hα.ne'] at h
      simp at h
    · intro h
      have := hstab _ (hp.1 t ht) h
      linarith

/-- **Proposition 17.H.1** (MWG, p. 624): "`p(t)` must be monotonically approaching any `αp*`".
The weighted distance `∑ₗ (1/cₗ)(pₗ(t) - αp*ₗ)²` to every point `αp*` (`α > 0`) of the ray is
nonincreasing along a trajectory. -/
theorem proposition_17_H_1_monotone (hc : ∀ l, 0 < c l) (hW : EDWalrasLaw z)
    (hp : IsTatPath c z p) {ps : Fin L → ℝ}
    (hstab : ∀ q ∈ posOrthant L, (¬ ∃ α : ℝ, 0 < α ∧ q = α • ps) → 0 < ps ⬝ᵥ z q)
    {α : ℝ} (hα : 0 < α) : AntitoneOn (fun t => wNormSq c (p t - α • ps)) (Ici 0) := by
  have hH : MonotoneOn (fun t => wInner c ps (p t)) (Ici 0) :=
    tat_monotoneOn (fun t ht => tat_hasDeriv_wInner hc hp ps ht)
      fun t ht => tat_g_nonneg hW hp hstab ht
  intro a ha b hb hab
  simp only [wNormSq_sub, wInner_smul_left, tat_wNormSq_const hc hW hp ha,
    tat_wNormSq_const hc hW hp hb]
  have := hH ha hb hab
  simp only at this
  nlinarith

/-- **Proposition 17.H.1** (MWG, p. 623). Let `z` be an excess demand function (continuous,
Walras' law, bounded below, boundary condition: Proposition 17.B.2(i), (iii)-(v)) and `cₗ > 0`.
Suppose that `z(p*) = 0` and `p*·z(p) > 0` for every `p ≫ 0` not proportional to `p*`. Then every
tâtonnement trajectory converges to a point `λp*` of the ray of `p*` (`λ > 0`: the one with the
weighted norm of `p(0)`). -/
theorem proposition_17_H_1 [NeZero L] (hc : ∀ l, 0 < c l) (hz : EDContinuous z)
    (hW : EDWalrasLaw z) (hB : EDBoundedBelow z) (hBd : EDBoundary z) {ps : Fin L → ℝ}
    (heq : IsEqmPrice z ps)
    (hstab : ∀ q ∈ posOrthant L, (¬ ∃ α : ℝ, 0 < α ∧ q = α • ps) → 0 < ps ⬝ᵥ z q)
    (hp : IsTatPath c z p) : ∃ lam : ℝ, 0 < lam ∧ Tendsto p atTop (𝓝 (lam • ps)) := by
  have hps := heq.1
  set N0 := wNormSq c (p 0) with hN0
  set W := wNormSq c ps with hWdef
  have hN0pos : 0 < N0 := wNormSq_pos hc (posOrthant_ne_zero (hp.1 0 le_rfl))
  have hWpos : 0 < W := wNormSq_pos hc (posOrthant_ne_zero hps)
  set lam := Real.sqrt (N0 / W) with hlam
  have hlampos : 0 < lam := Real.sqrt_pos.2 (div_pos hN0pos hWpos)
  have hN : wNormSq c (lam • ps) = N0 := by
    rw [wNormSq_smul, hlam, Real.sq_sqrt (div_pos hN0pos hWpos).le, ← hWdef]
    field_simp
  have hstrict : ∀ q ∈ posOrthant L, wNormSq c q = N0 → q ≠ lam • ps → 0 < ps ⬝ᵥ z q := by
    intro q hq hqN hne
    refine hstab q hq ?_
    rintro ⟨α, hα, rfl⟩
    apply hne
    have h1 : α ^ 2 * W = lam ^ 2 * W := by
      rw [← wNormSq_smul, ← wNormSq_smul, hqN, hN]
    have h2 : α ^ 2 = lam ^ 2 := mul_right_cancel₀ hWpos.ne' h1
    have h3 : α = lam := by nlinarith
    rw [h3]
  refine ⟨lam, hlampos, (tat_lyapunov_core hc hW hp hlampos hN
    (ρ' := wNormSq c (p 0 - lam • ps) + 1) (by linarith)
    (fun q hq hqN _ hne => hstrict q hq hqN hne) ?_).2⟩
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := tat_unif_pos hc hz hB hBd hps hN0pos hstrict ε hε
  exact ⟨δ, hδ, fun q hq hqN hqε _ => h q hq hqN hqε⟩

/-- **Proposition 17.H.1** (MWG, p. 623), relative prices: `pₖ(t)/pₗ(t) → p*ₖ/p*ₗ`. -/
theorem proposition_17_H_1_relative [NeZero L] (hc : ∀ l, 0 < c l) (hz : EDContinuous z)
    (hW : EDWalrasLaw z) (hB : EDBoundedBelow z) (hBd : EDBoundary z) {ps : Fin L → ℝ}
    (heq : IsEqmPrice z ps)
    (hstab : ∀ q ∈ posOrthant L, (¬ ∃ α : ℝ, 0 < α ∧ q = α • ps) → 0 < ps ⬝ᵥ z q)
    (hp : IsTatPath c z p) (k l : Fin L) :
    Tendsto (fun t => p t k / p t l) atTop (𝓝 (ps k / ps l)) := by
  obtain ⟨lam, hlam, h⟩ := proposition_17_H_1 hc hz hW hB hBd heq hstab hp
  have hk := (continuous_apply k).continuousAt.tendsto.comp h
  have hl := (continuous_apply l).continuousAt.tendsto.comp h
  have hne : (lam • ps) l ≠ 0 := by
    simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_ne_zero hlam.ne' (heq.1 l).ne'
  have := hk.div hl hne
  simp only [Pi.smul_apply, smul_eq_mul, Function.comp_def] at this
  rwa [mul_div_mul_left _ _ hlam.ne'] at this

/-! ### The cases covered: gross substitutes and the weak axiom (p. 623) -/

/-- **Section 17.H** (MWG, p. 623; Exercise 17.H.1). Global stability with gross substitutes:
if `z` satisfies (i)-(v) of Proposition 17.B.2 and the gross substitute property, and `z(p*) = 0`,
every tâtonnement trajectory converges to the ray of `p*`. By Proposition 17.F.3, `z(p) ≠ 0` off
the ray, and (17.F.3) gives `p*·z(p) > 0` there. -/
theorem tat_global_stability_gs [NeZero L] (hc : ∀ l, 0 < c l) (hz : IsStandardExcessDemand z)
    (hGS : GrossSubstitute z) {ps : Fin L → ℝ} (heq : IsEqmPrice z ps) (hp : IsTatPath c z p) :
    ∃ lam : ℝ, 0 < lam ∧ Tendsto p atTop (𝓝 (lam • ps)) := by
  refine proposition_17_H_1 hc hz.continuous hz.walras hz.boundedBelow hz.boundary heq ?_ hp
  intro q hq hnot
  refine eq_17_F_3 hz.homogeneous hz.walras hGS ps heq.1 heq.2 q hq fun h0 => hnot ?_
  exact proposition_17_F_3 hz.homogeneous hGS heq.1 hq (by rw [heq.2, h0])

/-- **Section 17.H** (MWG, p. 623). Global stability under the weak axiom: if `z` satisfies
(i)-(v) of Proposition 17.B.2 and the weak axiom, and the equilibrium price ray is unique (the
book's "unique (normalized) equilibrium"), every tâtonnement trajectory converges to it. -/
theorem tat_global_stability_wa [NeZero L] (hc : ∀ l, 0 < c l) (hz : IsStandardExcessDemand z)
    (hWA : WeakAxiomED z) {ps : Fin L → ℝ} (heq : IsEqmPrice z ps)
    (huniq : ∀ q, IsEqmPrice z q → ∃ α : ℝ, 0 < α ∧ q = α • ps) (hp : IsTatPath c z p) :
    ∃ lam : ℝ, 0 < lam ∧ Tendsto p atTop (𝓝 (lam • ps)) := by
  refine proposition_17_H_1 hc hz.continuous hz.walras hz.boundedBelow hz.boundary heq ?_ hp
  intro q hq hnot
  exact wa_eq_17_F_3 hWA ps heq.1 heq.2 q hq fun h0 => hnot (huniq q ⟨hq, h0⟩)

/-- **Section 17.H** (MWG, p. 623). The common form of the weak axiom, gross substitute and
no-trade cases: if `z` satisfies (i)-(v), `p*` is the unique equilibrium ray and `p*·z(p) > 0`
whenever `z(p) ≠ 0` ((17.F.3) at `p*`; for the no-trade case this is `notrade_eq_17_F_3`), every
tâtonnement trajectory converges to the ray of `p*`. -/
theorem tat_global_stability_revealed [NeZero L] (hc : ∀ l, 0 < c l)
    (hz : IsStandardExcessDemand z) {ps : Fin L → ℝ} (heq : IsEqmPrice z ps)
    (hrev : ∀ q ∈ posOrthant L, z q ≠ 0 → 0 < ps ⬝ᵥ z q)
    (huniq : ∀ q, IsEqmPrice z q → ∃ α : ℝ, 0 < α ∧ q = α • ps) (hp : IsTatPath c z p) :
    ∃ lam : ℝ, 0 < lam ∧ Tendsto p atTop (𝓝 (lam • ps)) :=
  proposition_17_H_1 hc hz.continuous hz.walras hz.boundedBelow hz.boundary heq
    (fun q hq hnot => hrev q hq fun h0 => hnot (huniq q ⟨hq, h0⟩)) hp

end MWG.PositiveEquilibriumTheory
