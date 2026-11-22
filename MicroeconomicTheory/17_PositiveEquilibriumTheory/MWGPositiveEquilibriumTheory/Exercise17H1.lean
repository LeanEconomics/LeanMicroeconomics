/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPositiveEquilibriumTheory.Tatonnement
import MWGPositiveEquilibriumTheory.Regularity
import MWGPositiveEquilibriumTheory.Existence

/-!
# Exercise 17.H.1: gross substitutes and the tâtonnement (MWG, p. 648)

With `cₗ = 1` and gross substitutes, `ψ(p) = max {z₁(p)/p₁, …, z_L(p)/p_L}`.

* (a) (`exercise_17_H_1a`): along every trajectory `ψ(p(t))` is nonincreasing, and it is strictly
  decreasing on every time interval on which `z(p(t)) ≠ 0`. At an index `ℓ` attaining the maximum,
  `d(zₗ/pₗ)/dt ≤ -ψ²`: homogeneity (`Dz(p)p = 0`) and the signs `∂zₗ/∂pₖ ≥ 0` (`k ≠ ℓ`) give
  `Dz(p) z(p)` a nonpositive `ℓ`-th coordinate (`ex17H1_key`); a maximum of finitely many
  functions whose active members decrease is decreasing (`ex17H1_max_strict`). Departure: `z` is
  assumed differentiable (the hint's argument is the derivative computation), and "decreasing" is
  proved while `z(p(t)) ≠ 0` (whether a trajectory starting out of equilibrium can reach an
  equilibrium in finite time is not addressed by the book).
* (b) (`exercise_17_H_1b`): `p(t)` converges to an equilibrium price vector (via Proposition
  17.H.1, which uses `∑ₗ pₗ(t)² = const`, the hint, and Proposition 17.C.1 for existence).
-/

namespace MWG.PositiveEquilibriumTheory

open Filter Topology Set

variable {L : ℕ}

/-- A maximum of finitely many functions decreases where its active members decrease: if every
`f l` has a right derivative on `[0, ∞)` and, at every `t ∈ [a, b]`, every index attaining the
maximum has `f' l t < 0`, then `max_l f l` is strictly decreasing on `[a, b]`. -/
theorem ex17H1_max_strict [NeZero L] {f f' : Fin L → ℝ → ℝ}
    (hd : ∀ l, ∀ t, 0 ≤ t → HasDerivWithinAt (f l) (f' l t) (Ici 0) t) {a b : ℝ} (ha : 0 ≤ a)
    (hact : ∀ t ∈ Icc a b, ∀ l, (∀ k, f k t ≤ f l t) → f' l t < 0) :
    ∀ x y, a ≤ x → x < y → y ≤ b →
      Finset.univ.sup' Finset.univ_nonempty (fun l => f l y) <
        Finset.univ.sup' Finset.univ_nonempty (fun l => f l x) := by
  set F : ℝ → ℝ := fun t => Finset.univ.sup' Finset.univ_nonempty (fun l => f l t) with hF
  have hle : ∀ t l, f l t ≤ F t := fun t l => Finset.le_sup' (fun l => f l t) (Finset.mem_univ l)
  -- local strict decrease to the right
  have hloc : ∀ x ∈ Ico a b, ∀ᶠ y in 𝓝[>] x, F y < F x := by
    intro x hx
    have hx0 : 0 ≤ x := ha.trans hx.1
    have hall : ∀ l, ∀ᶠ y in 𝓝[>] x, f l y < F x := by
      intro l
      by_cases hl : f l x < F x
      · have hc := ((hd l x hx0).continuousWithinAt.mono fun y (hy : x < y) =>
          (show (0 : ℝ) ≤ y from hx0.trans hy.le))
        exact hc.eventually (gt_mem_nhds hl)
      · have hlx : f l x = F x := le_antisymm (hle x l) (not_lt.1 hl)
        have hact' : f' l x < 0 := hact x (Ico_subset_Icc_self hx) l fun k => by
          rw [hlx]; exact hle x k
        have hslope := hasDerivWithinAt_iff_tendsto_slope.1
          ((hd l x hx0).mono (show Ioi x ⊆ Ici 0 from fun y hy => hx0.trans (le_of_lt hy)))
        have hev : ∀ᶠ y in 𝓝[Ioi x \ {x}] x, slope (f l) x y < 0 :=
          hslope.eventually (gt_mem_nhds hact')
        rw [Set.sdiff_singleton_eq_self (show x ∉ Ioi x from lt_irrefl x)] at hev
        filter_upwards [hev, self_mem_nhdsWithin] with y hy hyx
        have hyx' : 0 < y - x := sub_pos.2 hyx
        rw [slope_def_field, div_neg_iff] at hy
        rcases hy with ⟨_, h⟩ | ⟨h, _⟩
        · linarith
        · linarith
    filter_upwards [Filter.eventually_all.2 hall] with y hy
    exact (Finset.sup'_lt_iff _).2 fun l _ => hy l
  have hcont : ContinuousOn F (Icc a b) := by
    have : ∀ l, ContinuousOn (f l) (Icc a b) := fun l t ht =>
      (hd l t (ha.trans ht.1)).continuousWithinAt.mono fun y hy => ha.trans hy.1
    exact ContinuousOn.finset_sup'_apply Finset.univ_nonempty fun l _ => this l
  -- nonincreasing from any `x₀ ∈ [a, b]`
  have hmono : ∀ x0 ∈ Icc a b, ∀ y ∈ Icc x0 b, F y ≤ F x0 := by
    intro x0 hx0
    have hsub := IsClosed.Icc_subset_of_forall_mem_nhdsWithin (a := x0) (b := b)
      (s := {y | F y ≤ F x0}) ?_ (show F x0 ≤ F x0 from le_rfl) ?_
    · exact fun y hy => hsub hy
    · have := (hcont.mono (Icc_subset_Icc_left hx0.1)).preimage_isClosed_of_isClosed isClosed_Icc
        (isClosed_Iic (a := F x0))
      rw [inter_comm]
      exact this
    · intro x hx
      filter_upwards [hloc x ⟨hx0.1.trans hx.2.1, hx.2.2⟩] with y hy
      exact (le_of_lt hy).trans hx.1
  intro x y hx hxy hy
  obtain ⟨w, hw⟩ := ((hloc x ⟨hx, lt_of_lt_of_le hxy hy⟩).and
    (Ioo_mem_nhdsGT hxy)).exists
  exact lt_of_le_of_lt (hmono w ⟨hx.trans hw.2.1.le, hw.2.2.le.trans hy⟩ y ⟨hw.2.2.le, hy⟩) hw.1

/-- The nonstrict version: if active members have `f' l t ≤ 0`, the maximum is nonincreasing. -/
theorem ex17H1_max_anti [NeZero L] {f f' : Fin L → ℝ → ℝ}
    (hd : ∀ l, ∀ t, 0 ≤ t → HasDerivWithinAt (f l) (f' l t) (Ici 0) t)
    (hact : ∀ t, 0 ≤ t → ∀ l, (∀ k, f k t ≤ f l t) → f' l t ≤ 0) :
    AntitoneOn (fun t => Finset.univ.sup' Finset.univ_nonempty (fun l => f l t)) (Ici 0) := by
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hxy with h | h
  · rw [h]
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  set η := ε / (y - x) with hη
  have hη0 : 0 < η := div_pos hε (sub_pos.2 h)
  have hs := ex17H1_max_strict (f := fun l t => f l t - η * t) (f' := fun l t => f' l t - η)
    (fun l t ht => ((hd l t ht).sub ((hasDerivWithinAt_id t _).const_mul η)).congr_deriv
      (by rw [mul_one])) (a := x) (b := y) hx (fun t ht l hl => by
        have : ∀ k, f k t ≤ f l t := fun k => by have := hl k; linarith
        linarith [hact t (hx.trans ht.1) l this]) x y le_rfl h le_rfl
  have hshift : ∀ t, Finset.univ.sup' Finset.univ_nonempty (fun l => f l t - η * t) =
      Finset.univ.sup' Finset.univ_nonempty (fun l => f l t) - η * t := fun t => by
    refine le_antisymm ?_ ?_
    · exact Finset.sup'_le _ _ fun l _ =>
        sub_le_sub_right (Finset.le_sup' (fun l => f l t) (Finset.mem_univ l)) _
    · rw [sub_le_iff_le_add]
      exact Finset.sup'_le _ _ fun l _ => by
        have := Finset.le_sup' (fun l => f l t - η * t) (Finset.mem_univ l)
        linarith
  rw [hshift, hshift] at hs
  have : η * (y - x) = ε := by rw [hη]; field_simp
  simp only
  nlinarith

/-- `ψ(p) = max {z₁(p)/p₁, …, z_L(p)/p_L}`. -/
noncomputable def ex17H1Psi [NeZero L] (z : (Fin L → ℝ) → Fin L → ℝ) (q : Fin L → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun l => z q l / q l)

/-- **Exercise 17.H.1(a)**, the key inequality. If `z` is homogeneous, differentiable at `q ≫ 0`
with derivative `D`, has the (weak) gross substitute property, and `ℓ` maximizes `zₖ(q)/qₖ`,
then `(D z(q))ₗ ≤ 0`. -/
theorem ex17H1_key {z : (Fin L → ℝ) → Fin L → ℝ} (hH : EDHomogeneous z)
    (hGS : WeakGrossSubstitute z) {q : Fin L → ℝ} (hq : q ∈ posOrthant L)
    {D : (Fin L → ℝ) →L[ℝ] (Fin L → ℝ)} (hD : HasFDerivAt z D q) {l : Fin L}
    (hmax : ∀ k, z q k / q k ≤ z q l / q l) : D (z q) l ≤ 0 := by
  set F := z q l / q l with hFdef
  have hexp : ∀ v : Fin L → ℝ, D v l = ∑ k, v k * D (Pi.single k 1) l := by
    intro v
    have hv : v = ∑ k, v k • (Pi.single k (1 : ℝ) : Fin L → ℝ) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hv]
    simp [map_sum, Finset.sum_apply]
  have heuler : D q l = 0 := by rw [euler_fderiv hH hq hD]; rfl
  have h1 : D (z q) l = D (z q) l - F * D q l := by rw [heuler]; ring
  rw [h1, hexp (z q), hexp q, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_nonpos fun k _ => ?_
  have hfac : z q k * D (Pi.single k 1) l - F * (q k * D (Pi.single k 1) l) =
      (z q k - F * q k) * D (Pi.single k 1) l := by ring
  rw [hfac]
  by_cases hkl : k = l
  · subst hkl
    have : z q k - F * q k = 0 := by rw [hFdef]; field_simp [(hq k).ne']; ring
    rw [this, zero_mul]
  · have hpart : 0 ≤ D (Pi.single k 1) l := gs_partial_nonneg hGS hq hD (Ne.symm hkl)
    have hk : z q k - F * q k ≤ 0 := by
      have := hmax k
      rw [div_le_iff₀ (hq k)] at this
      linarith
    exact mul_nonpos_of_nonpos_of_nonneg hk hpart

/-- **Exercise 17.H.1(a)** (MWG, p. 648). With `cₗ = 1`, `z` homogeneous, differentiable on
`ℝ^L_{++}`, satisfying Walras' law and (weak) gross substitution, `ψ(p(t))` is nonincreasing
along every tâtonnement trajectory, and strictly decreasing on every time interval `[a, b]` on
which `z(p(t)) ≠ 0`. -/
theorem exercise_17_H_1a [NeZero L] {z : (Fin L → ℝ) → Fin L → ℝ} (hH : EDHomogeneous z)
    (hW : EDWalrasLaw z) (hGS : WeakGrossSubstitute z)
    (hdiff : ∀ q ∈ posOrthant L, DifferentiableAt ℝ z q) {p : ℝ → Fin L → ℝ}
    (hp : IsTatPath (fun _ => 1) z p) :
    AntitoneOn (fun t => ex17H1Psi z (p t)) (Ici 0) ∧
      ∀ a b, 0 ≤ a → a < b → (∀ t ∈ Icc a b, z (p t) ≠ 0) →
        ex17H1Psi z (p b) < ex17H1Psi z (p a) := by
  set f : Fin L → ℝ → ℝ := fun l t => z (p t) l / p t l with hf
  set f' : Fin L → ℝ → ℝ := fun l t =>
    (fderiv ℝ z (p t) (z (p t)) l * p t l - z (p t) l * z (p t) l) / p t l ^ 2 with hf'
  have hd : ∀ l, ∀ t, 0 ≤ t → HasDerivWithinAt (f l) (f' l t) (Ici 0) t := by
    intro l t ht
    have hq := hp.1 t ht
    have hzt := hasDerivWithinAt_pi.1
      ((hdiff _ hq).hasFDerivAt.comp_hasDerivWithinAt t (hp.2 t ht)) l
    have hpl := tat_coord hp ht l
    have := hzt.div hpl (hq l).ne'
    have htf : tatField (fun _ => (1 : ℝ)) z (p t) = z (p t) := by
      funext k; simp [tatField]
    simp only [htf, one_mul] at this
    exact this
  have hactle : ∀ t, 0 ≤ t → ∀ l, (∀ k, f k t ≤ f l t) →
      f' l t ≤ -(z (p t) l / p t l) ^ 2 := by
    intro t ht l hl
    have hq := hp.1 t ht
    have hkey := ex17H1_key hH hGS hq (hdiff _ hq).hasFDerivAt hl
    have hpl := hq l
    simp only [hf']
    rw [div_pow, div_le_iff₀ (by positivity), neg_mul, div_mul_cancel₀ _ (by positivity)]
    nlinarith
  have hfF : ∀ t, ex17H1Psi z (p t) = Finset.univ.sup' Finset.univ_nonempty (fun l => f l t) :=
    fun _ => rfl
  refine ⟨?_, fun a b ha hab hne => ?_⟩
  · have := ex17H1_max_anti hd fun t ht l hl => (hactle t ht l hl).trans
      (neg_nonpos.2 (sq_nonneg _))
    intro x hx y hy hxy
    exact this hx hy hxy
  · rw [hfF, hfF]
    refine ex17H1_max_strict hd ha (fun t ht l hl => ?_) a b le_rfl hab le_rfl
    have ht0 : 0 ≤ t := ha.trans ht.1
    have hq := hp.1 t ht0
    -- some excess demand is positive (Walras' law, `z ≠ 0`)
    obtain ⟨k, hk⟩ : ∃ k, 0 < z (p t) k := by
      by_contra hcon
      push Not at hcon
      apply hne t ht
      have hw := hW _ hq
      have hterm : ∀ k, p t k * z (p t) k ≤ 0 := fun k =>
        mul_nonpos_of_nonneg_of_nonpos (hq k).le (hcon k)
      have hzero := (Finset.sum_eq_zero_iff_of_nonpos fun k _ => hterm k).1 hw
      funext k
      have := hzero k (Finset.mem_univ k)
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h (hq k).ne'
      · exact h
    have hFpos : 0 < z (p t) l / p t l :=
      lt_of_lt_of_le (div_pos hk (hq k)) (hl k)
    have := hactle t ht0 l hl
    nlinarith [pow_pos hFpos 2]

/-- **Exercise 17.H.1(b)** (MWG, p. 648). With `cₗ = 1` and `z` satisfying (i)-(v) of
Proposition 17.B.2 and the gross substitute property, every tâtonnement trajectory converges to an
equilibrium price vector. (Walras' law keeps `∑ₗ pₗ(t)²` constant; Proposition 17.H.1 applies.) -/
theorem exercise_17_H_1b [NeZero L] {z : (Fin L → ℝ) → Fin L → ℝ}
    (hz : IsStandardExcessDemand z) (hGS : GrossSubstitute z) {p : ℝ → Fin L → ℝ}
    (hp : IsTatPath (fun _ => 1) z p) :
    ∃ pb, IsEqmPrice z pb ∧ Tendsto p atTop (𝓝 pb) := by
  obtain ⟨ps, hps⟩ := proposition_17_C_1 hz
  obtain ⟨lam, hlam, hlim⟩ := tat_global_stability_gs (fun _ => one_pos) hz hGS hps hp
  exact ⟨lam • ps, hps.smul hz.homogeneous hlam, hlim⟩

end MWG.PositiveEquilibriumTheory
