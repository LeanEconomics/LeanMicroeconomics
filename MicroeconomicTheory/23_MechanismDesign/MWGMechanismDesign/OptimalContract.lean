/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGMechanismDesign.OptimalAuction
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# A principal-agent problem with hidden information

MWG, Section 23.F, Example 23.F.1 (pp. 900-903).

The agent's type `θ ∈ [θ̲, θ̄]` (`θ̄ < 0`) has a density `φ > 0` (`TypeDensity`); he chooses effort
`e ≥ 0` and receives `t`, with utility `t + θg(e)`; the principal's utility is `v(e) - t`. A
contract is `(e(·), t(·))`; `U(θ) = t(θ) + θg(e(θ))`; reservation utility `ū`;
`J(θ) = θ - (1 - Φ(θ))/φ(θ)`.

* (23.F.3): Bayesian incentive compatibility ⇔ (i) `g(e(·))` nondecreasing (⇔ `e(·)`
  nondecreasing, as `g` is increasing) and (ii) `U(θ) = U(θ̲) + ∫_{θ̲}^{θ} g(e(s)) ds`
  (`eq_23_F_3`, `oc_monotone_comp_iff`); (iii) ⇔ (iii') (`eq_23_F_iii_iff`).
* (23.F.4): `E[v(e(θ)) - t(θ)] = E[v(e(θ)) + g(e(θ))J(θ)] - U(θ̲)` (`eq_23_F_4`), by the Fubini
  form of the integration by parts.
* `U(θ̲) = ū` in any optimal contract (`eq_23_F_5`).
* `example_23_F_1`: if `e*(θ)` maximises `v(e) + g(e)J(θ)` over `e ≥ 0` for every `θ` (the relaxed
  problem), and `(e*, t*)` is incentive compatible with `U*(θ̲) = ū`, it is optimal among all
  incentive compatible and individually rational contracts.
* (23.F.6): at an interior optimum `v'(e) + g'(e)J(θ) = 0` (`eq_23_F_6`). MWG's implicit
  function theorem argument for monotonicity of `e(·)` is replaced by monotone comparative
  statics (`oc_maximizer_mono`, `oc_maximizer_monotoneOn`): with `g` strictly increasing, `J`
  nondecreasing and unique maximisers, `e(·)` is nondecreasing.
* p. 903: `e(θ) ≤ e^*(θ)` (first best) everywhere, `= ` at `θ̄`, and `<` for `θ < θ̄` given
  differentiability, `g' > 0` on `e > 0`, `g'(0) = 0`, `v'(0) > 0` (`example_23_F_1_le_firstBest`,
  `example_23_F_1_eq_firstBest_hi`, `example_23_F_1_lt_firstBest`).
* Instance: `θ` uniform on `[-2, -1]` (`J(θ) = 2θ + 1`), `g(e) = e²`, `v(e) = 2e - e²`:
  `e*(θ) = -1/(2θ)`, `t*(θ) = -1/(2θ) - 1/8`, `ū = 0`, first best `1/(1 - θ)`
  (`example_23_F_1_instance`).

Departures: the derivative hypotheses on `v`, `g` are replaced where possible by their
consequences (strict monotonicity of `g` on `e ≥ 0`, uniqueness of maximisers); integrability of
the payoffs is assumed explicitly; the "heuristic" perturbation argument (footnote 49) is verbal.
-/

namespace MWG.MechanismDesign

open MeasureTheory

/-- **Example 23.F.1** (MWG, p. 901). The agent's utility from truth telling,
`U(θ) = t(θ) + θg(e(θ))`. -/
def ocU (g e t : ℝ → ℝ) (θ : ℝ) : ℝ := t θ + θ * g (e θ)

/-- **Example 23.F.1** (MWG, pp. 901-902). A feasible contract: effort `e(θ) ≥ 0`, Bayesian
incentive compatible (truth telling optimal for every type), individually rational
(`U(θ) ≥ ū`), and with the expectations involved existing. -/
def OCFeasible (D : TypeDensity) (v g : ℝ → ℝ) (ubar : ℝ) (e t : ℝ → ℝ) : Prop :=
  (∀ θ, 0 ≤ e θ) ∧ LinearIC (fun θ => g (e θ)) t D.lo D.hi ∧
    (∀ θ ∈ Set.Icc D.lo D.hi, ubar ≤ ocU g e t θ) ∧ Integrable (fun θ => v (e θ)) D.measure ∧
    Integrable t D.measure ∧ Integrable (fun θ => θ * g (e θ)) D.measure ∧
    Integrable (fun θ => g (e θ) * ((1 - D.cdf θ) / D.dens θ)) D.measure

/-- The principal's expected payoff `E[v(e(θ)) - t(θ)]`. -/
noncomputable def ocPayoff (D : TypeDensity) (v : ℝ → ℝ) (e t : ℝ → ℝ) : ℝ :=
  ∫ θ, (v (e θ) - t θ) ∂D.measure

/-- **(23.F.3)** (MWG, p. 902), constraints (i)-(ii): the contract is Bayesian incentive
compatible iff `g(e(·))` is nondecreasing and `U(θ) = U(θ̲) + ∫_{θ̲}^{θ} g(e(s)) ds`
(Proposition 23.D.2 with `k = e`, `v₁(k) = g(e)`). -/
theorem eq_23_F_3 {g e t : ℝ → ℝ} {lo hi : ℝ} :
    LinearIC (fun θ => g (e θ)) t lo hi ↔ MonotoneOn (fun θ => g (e θ)) (Set.Icc lo hi) ∧
      ∀ θ ∈ Set.Icc lo hi, ocU g e t θ = ocU g e t lo + ∫ s in lo..θ, g (e s) := by
  rw [linearIC_iff]
  simp only [ocU]
  constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨h1, fun θ hθ => ?_⟩ <;> have := h2 θ hθ <;>
    linarith

/-- **(23.F.3)** (MWG, p. 902), "constraint (i) follows because `g` is increasing": when `g` is
strictly increasing on `e ≥ 0` and efforts are nonnegative, `g(e(·))` is nondecreasing iff `e(·)`
is. -/
theorem oc_monotone_comp_iff {g e : ℝ → ℝ} {S : Set ℝ} (hg : StrictMonoOn g (Set.Ici 0))
    (he : ∀ θ, 0 ≤ e θ) : MonotoneOn (fun θ => g (e θ)) S ↔ MonotoneOn e S := by
  constructor
  · intro h x hx y hy hxy
    by_contra hlt
    rw [not_le] at hlt
    have := hg (Set.mem_Ici.2 (he y)) (Set.mem_Ici.2 (he x)) hlt
    have := h hx hy hxy
    simp only at this
    linarith
  · intro h x hx y hy hxy
    exact hg.monotoneOn (Set.mem_Ici.2 (he x)) (Set.mem_Ici.2 (he y)) (h hx hy hxy)

/-- **(23.F.3)** (MWG, p. 902), (iii) ⇔ (iii'): given (ii) and `g ≥ 0` on effort levels used,
`U(θ) ≥ ū` for all `θ` iff `U(θ̲) ≥ ū`. -/
theorem eq_23_F_iii_iff {g e t : ℝ → ℝ} {lo hi ubar : ℝ} (hle : lo ≤ hi)
    (hg0 : ∀ θ, 0 ≤ g (e θ))
    (hii : ∀ θ ∈ Set.Icc lo hi, ocU g e t θ = ocU g e t lo + ∫ s in lo..θ, g (e s)) :
    (∀ θ ∈ Set.Icc lo hi, ubar ≤ ocU g e t θ) ↔ ubar ≤ ocU g e t lo := by
  refine ⟨fun h => h lo ⟨le_rfl, hle⟩, fun h θ hθ => ?_⟩
  rw [hii θ hθ]
  have := intervalIntegral.integral_nonneg (μ := volume) hθ.1 fun s _ => hg0 s
  linarith

/-- For `s ∈ [θ̲, θ̄]`, `1 - Φ(s) ≥ 0`. -/
theorem oc_one_sub_cdf_nonneg (D : TypeDensity) {s : ℝ} (hs : s ∈ Set.Icc D.lo D.hi) :
    0 ≤ 1 - D.cdf s := by
  rw [← D.measureReal_Ici hs]; exact measureReal_nonneg

/-- For `s ∈ [θ̲, θ̄)`, `1 - Φ(s) > 0`. -/
theorem oc_one_sub_cdf_pos (D : TypeDensity) {s : ℝ} (hs : s ∈ Set.Icc D.lo D.hi) (hlt : s < D.hi) :
    0 < 1 - D.cdf s := by
  have := D.isProbabilityMeasure
  rw [← D.measureReal_Ici hs, measureReal_def]
  refine ENNReal.toReal_pos ?_ (measure_ne_top _ _)
  exact (lt_of_lt_of_le (D.measure_Ioo_pos hs.1 hlt le_rfl)
    (measure_mono fun x hx => Set.mem_Ici.2 hx.1.le)).ne'

/-- **(23.F.4)** (MWG, p. 902). For an incentive compatible contract (with the expectations
existing), `E[v(e(θ)) - t(θ)] = E[v(e(θ)) + g(e(θ))J(θ)] - U(θ̲)`, `J(θ) = θ - (1 - Φ(θ))/φ(θ)`. -/
theorem eq_23_F_4 (D : TypeDensity) {v g e t : ℝ → ℝ}
    (hIC : LinearIC (fun θ => g (e θ)) t D.lo D.hi)
    (hv : Integrable (fun θ => v (e θ)) D.measure) (ht : Integrable t D.measure)
    (hθg : Integrable (fun θ => θ * g (e θ)) D.measure)
    (hgr : Integrable (fun θ => g (e θ) * ((1 - D.cdf θ) / D.dens θ)) D.measure) :
    ocPayoff D v e t = ∫ θ, (v (e θ) + g (e θ) * D.virtualValue θ) ∂D.measure -
      ocU g e t D.lo := by
  have := D.isProbabilityMeasure
  have hle : D.lo ≤ D.hi := D.lo_lt_hi.le
  obtain ⟨hmono, hii⟩ := eq_23_F_3.1 hIC
  set P : ℝ → ℝ := fun θ => ∫ s in D.lo..θ, g (e s) with hP
  have hw : IntervalIntegrable (fun s => g (e s)) volume D.lo D.hi := by
    apply MonotoneOn.intervalIntegrable; rw [Set.uIcc_of_le hle]; exact hmono
  have hae : ∀ᵐ θ ∂D.measure, θ ∈ Set.Icc D.lo D.hi := mem_ae_iff.2 D.measure_compl_Icc
  have htP : t =ᵐ[D.measure] fun θ => ocU g e t D.lo + P θ - θ * g (e θ) := by
    filter_upwards [hae] with θ hθ
    have := hii θ hθ
    simp only [ocU] at this ⊢
    simp only [hP]
    linarith
  have hPint : Integrable P D.measure := by
    have h1 : Integrable (fun θ => t θ + θ * g (e θ) - ocU g e t D.lo) D.measure :=
      (ht.add hθg).sub (integrable_const _)
    refine h1.congr ?_
    filter_upwards [htP] with θ hθ
    rw [hθ]; ring
  have hEP : ∫ θ, P θ ∂D.measure = ∫ s in D.lo..D.hi, g (e s) * (1 - D.cdf s) := by
    rw [hP, td_integral_integral_eq D.measure hle D.measure_compl_Icc hw]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le hle] at hs
    simp only [D.measureReal_Ici hs]
  have hEr : ∫ θ, g (e θ) * ((1 - D.cdf θ) / D.dens θ) ∂D.measure =
      ∫ s in D.lo..D.hi, g (e s) * (1 - D.cdf s) := by
    rw [D.integral_eq]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le hle] at hs
    have := (D.dens_pos s hs).ne'
    field_simp
  have hEt : ∫ θ, t θ ∂D.measure =
      ocU g e t D.lo + ∫ θ, P θ ∂D.measure - ∫ θ, θ * g (e θ) ∂D.measure := by
    have h1 : Integrable (fun θ => ocU g e t D.lo + P θ) D.measure :=
      (integrable_const _).add hPint
    have e1 : ∫ θ, (ocU g e t D.lo + P θ - θ * g (e θ)) ∂D.measure =
        ∫ θ, (ocU g e t D.lo + P θ) ∂D.measure - ∫ θ, θ * g (e θ) ∂D.measure :=
      integral_sub h1 hθg
    have e2 : ∫ θ, (ocU g e t D.lo + P θ) ∂D.measure =
        ∫ _θ, ocU g e t D.lo ∂D.measure + ∫ θ, P θ ∂D.measure :=
      integral_add (integrable_const _) hPint
    rw [integral_congr_ae htP, e1, e2, integral_const, probReal_univ, one_smul]
  have hEJ : ∫ θ, (v (e θ) + g (e θ) * D.virtualValue θ) ∂D.measure =
      ∫ θ, v (e θ) ∂D.measure + ∫ θ, θ * g (e θ) ∂D.measure -
        ∫ θ, g (e θ) * ((1 - D.cdf θ) / D.dens θ) ∂D.measure := by
    have e1 : ∫ θ, (v (e θ) + θ * g (e θ)) ∂D.measure =
        ∫ θ, v (e θ) ∂D.measure + ∫ θ, θ * g (e θ) ∂D.measure := integral_add hv hθg
    have e2 : ∫ θ, (v (e θ) + θ * g (e θ) - g (e θ) * ((1 - D.cdf θ) / D.dens θ)) ∂D.measure =
        ∫ θ, (v (e θ) + θ * g (e θ)) ∂D.measure -
          ∫ θ, g (e θ) * ((1 - D.cdf θ) / D.dens θ) ∂D.measure := integral_sub (hv.add hθg) hgr
    rw [← e1, ← e2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    simp only [TypeDensity.virtualValue]
    ring
  rw [ocPayoff, integral_sub hv ht, hEt, hEJ, hEP, hEr]
  ring

/-- **Example 23.F.1** (MWG, p. 902). "In any solution we must have `U(θ̲) = ū`": a feasible
contract that maximises the principal's expected payoff among feasible contracts leaves the lowest
type exactly his reservation utility (otherwise lower all transfers by `U(θ̲) - ū`); here
`g ≥ 0` on `e ≥ 0` (MWG: `g(0) = 0`, `g(e) > 0` for `e > 0`). -/
theorem eq_23_F_5 (D : TypeDensity) {v g : ℝ → ℝ} {ubar : ℝ} {e t : ℝ → ℝ}
    (hg0 : ∀ x, 0 ≤ x → 0 ≤ g x) (hf : OCFeasible D v g ubar e t)
    (hopt : ∀ e' t', OCFeasible D v g ubar e' t' → ocPayoff D v e' t' ≤ ocPayoff D v e t) :
    ocU g e t D.lo = ubar := by
  have := D.isProbabilityMeasure
  obtain ⟨he, hIC, hIR, hv, ht, hθg, hgr⟩ := hf
  by_contra hne
  have hlt : ubar < ocU g e t D.lo := lt_of_le_of_ne (hIR _ ⟨le_rfl, D.lo_lt_hi.le⟩) (Ne.symm hne)
  set δ := ocU g e t D.lo - ubar with hδ
  have hfeas : OCFeasible D v g ubar e (fun θ => t θ - δ) := by
    refine ⟨he, fun θ hθ θh hθh => ?_, fun θ hθ => ?_, hv, ht.sub (integrable_const _), hθg, hgr⟩
    · have := hIC θ hθ θh hθh; simp only at this ⊢; linarith
    · have hlo : D.lo ∈ Set.Icc D.lo D.hi := ⟨le_rfl, D.lo_lt_hi.le⟩
      have h1 := hIC θ hθ D.lo hlo
      have h2 := mul_nonneg (sub_nonneg.2 hθ.1) (hg0 (e D.lo) (he D.lo))
      simp only [ocU, hδ] at h1 h2 ⊢
      nlinarith
  have := hopt e _ hfeas
  rw [ocPayoff, ocPayoff] at this
  have he2 : ∫ θ, (v (e θ) - (t θ - δ)) ∂D.measure = ∫ θ, (v (e θ) - t θ) ∂D.measure + δ := by
    have e : ∫ θ, ((v (e θ) - t θ) + δ) ∂D.measure =
        ∫ θ, (v (e θ) - t θ) ∂D.measure + ∫ _θ, δ ∂D.measure :=
      integral_add (hv.sub ht) (integrable_const δ)
    rw [integral_const, probReal_univ, one_smul] at e
    rw [← e]
    congr 1; funext θ; ring
  rw [he2] at this
  linarith

/-- `x ≥ 0` maximises `h` over effort levels `e ≥ 0`. -/
def OCArgmax (h : ℝ → ℝ) (x : ℝ) : Prop := 0 ≤ x ∧ ∀ e, 0 ≤ e → h e ≤ h x

/-- With incentive compatibility, `v(e) + g(e)J` is integrable when the payoffs are. -/
theorem oc_integrable_vJ (D : TypeDensity) {v g e : ℝ → ℝ}
    (hv : Integrable (fun θ => v (e θ)) D.measure)
    (hθg : Integrable (fun θ => θ * g (e θ)) D.measure)
    (hgr : Integrable (fun θ => g (e θ) * ((1 - D.cdf θ) / D.dens θ)) D.measure) :
    Integrable (fun θ => v (e θ) + g (e θ) * D.virtualValue θ) D.measure := by
  refine ((hv.add hθg).sub hgr).congr (Filter.Eventually.of_forall fun θ => ?_)
  simp only [TypeDensity.virtualValue, Pi.add_apply, Pi.sub_apply]
  ring

/-- **Example 23.F.1** (MWG, pp. 902-903). If `e*(θ)` maximises `v(e) + g(e)J(θ)` over `e ≥ 0`
for every `θ ∈ [θ̲, θ̄]` (the relaxed problem (23.F.5) without constraint (i)), and `(e*, t*)` is a
feasible contract with `U*(θ̲) = ū` (so `t*` is given by (ii)), then `(e*, t*)` maximises the
principal's expected payoff among all feasible contracts. -/
theorem example_23_F_1 (D : TypeDensity) {v g : ℝ → ℝ} {ubar : ℝ} {es ts : ℝ → ℝ}
    (hs : OCFeasible D v g ubar es ts) (hU : ocU g es ts D.lo = ubar)
    (hmax : ∀ θ ∈ Set.Icc D.lo D.hi, OCArgmax (fun x => v x + g x * D.virtualValue θ) (es θ))
    {e t : ℝ → ℝ} (h : OCFeasible D v g ubar e t) :
    ocPayoff D v e t ≤ ocPayoff D v es ts := by
  obtain ⟨he, hIC, hIR, hv, ht, hθg, hgr⟩ := h
  obtain ⟨-, hIC', -, hv', ht', hθg', hgr'⟩ := hs
  rw [eq_23_F_4 D hIC hv ht hθg hgr, eq_23_F_4 D hIC' hv' ht' hθg' hgr', hU]
  have hlo := hIR D.lo ⟨le_rfl, D.lo_lt_hi.le⟩
  have hle := integral_mono_ae (oc_integrable_vJ D hv hθg hgr) (oc_integrable_vJ D hv' hθg' hgr')
    (by
      filter_upwards [mem_ae_iff.2 D.measure_compl_Icc] with θ hθ
      exact (hmax θ hθ).2 (e θ) (he θ))
  linarith

/-- **(23.F.6)** (MWG, p. 902). At an interior solution `e > 0` of `max_{e ≥ 0} v(e) + g(e)c`
(with `c = J(θ)`), the first-order condition `v'(e) + g'(e)c = 0` holds. -/
theorem eq_23_F_6 {v g : ℝ → ℝ} {v' g' c x : ℝ} (hv : HasDerivAt v v' x) (hg : HasDerivAt g g' x)
    (hx : 0 < x) (hmax : OCArgmax (fun e => v e + g e * c) x) : v' + g' * c = 0 := by
  have hloc : IsLocalMax (fun e => v e + g e * c) x :=
    Filter.mem_of_superset (Ioi_mem_nhds hx) fun e he => hmax.2 e (le_of_lt he)
  exact hloc.hasDerivAt_eq_zero (hv.add (hg.mul_const c))

/-- Monotone comparative statics (replacing MWG's implicit function theorem argument, p. 902):
with `g` strictly increasing on `e ≥ 0`, a maximiser of `v(e) + g(e)c₁` is at most any maximiser
of `v(e) + g(e)c₂` when `c₁ < c₂`. -/
theorem oc_maximizer_mono {v g : ℝ → ℝ} (hg : StrictMonoOn g (Set.Ici 0)) {c1 c2 x1 x2 : ℝ}
    (hc : c1 < c2) (h1 : OCArgmax (fun e => v e + g e * c1) x1)
    (h2 : OCArgmax (fun e => v e + g e * c2) x2) : x1 ≤ x2 := by
  by_contra hlt
  rw [not_le] at hlt
  have hgx := hg (Set.mem_Ici.2 h2.1) (Set.mem_Ici.2 h1.1) hlt
  have a1 := h1.2 x2 h2.1
  have a2 := h2.2 x1 h1.1
  simp only at a1 a2
  nlinarith

/-- A strictly concave function has at most one maximiser on `e ≥ 0`. -/
theorem oc_argmax_unique {h : ℝ → ℝ} (hc : StrictConcaveOn ℝ (Set.Ici 0) h) {x y : ℝ}
    (hx : OCArgmax h x) (hy : OCArgmax h y) : x = y := by
  by_contra hne
  have hmid := hc.2 (Set.mem_Ici.2 hx.1) (Set.mem_Ici.2 hy.1) hne (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at hmid
  have h1 := hx.2 (1 / 2 * x + 1 / 2 * y) (by have := hx.1; have := hy.1; linarith)
  have h2 := hx.2 y hy.1
  have h3 := hy.2 x hx.1
  linarith

/-- With `v` strictly concave, `g` convex and `c ≤ 0` (MWG: `v'' < 0`, `g'' > 0`, and
`J(θ) ≤ θ < 0`), `v(e) + g(e)c` is strictly concave on `e ≥ 0`, so its maximiser is unique. -/
theorem oc_strictConcave {v g : ℝ → ℝ} {c : ℝ} (hv : StrictConcaveOn ℝ (Set.Ici 0) v)
    (hg : ConvexOn ℝ (Set.Ici 0) g) (hc : c ≤ 0) :
    StrictConcaveOn ℝ (Set.Ici 0) (fun e => v e + g e * c) := by
  refine hv.add_concaveOn ⟨convex_Ici 0, fun x hx y hy a b ha hb hab => ?_⟩
  have := hg.2 hx hy ha hb hab
  simp only [smul_eq_mul] at this ⊢
  nlinarith

/-- **Example 23.F.1** (MWG, p. 902). With `g` strictly increasing on `e ≥ 0`, `J` nondecreasing
and a unique maximiser `e(θ)` of `v(e) + g(e)J(θ)` for every `θ`, the solution `e(·)` of the
relaxed problem is nondecreasing, so it satisfies constraint (i). -/
theorem oc_maximizer_monotoneOn {v g J es : ℝ → ℝ} {lo hi : ℝ} (hg : StrictMonoOn g (Set.Ici 0))
    (hJ : MonotoneOn J (Set.Icc lo hi))
    (hmax : ∀ θ ∈ Set.Icc lo hi, OCArgmax (fun x => v x + g x * J θ) (es θ))
    (huniq : ∀ θ ∈ Set.Icc lo hi, ∀ x, OCArgmax (fun x => v x + g x * J θ) x → x = es θ) :
    MonotoneOn es (Set.Icc lo hi) := by
  intro a ha b hb hab
  rcases lt_or_eq_of_le (hJ ha hb hab) with hlt | heq
  · exact oc_maximizer_mono hg hlt (hmax a ha) (hmax b hb)
  · have := huniq a ha (es b) (by rw [heq]; exact hmax b hb)
    rw [this]

/-- `J(θ) ≤ θ` on `[θ̲, θ̄]`, with `J(θ) < θ` for `θ < θ̄`, and `J(θ̄) = θ̄`. -/
theorem oc_virtualValue_facts (D : TypeDensity) :
    (∀ θ ∈ Set.Icc D.lo D.hi, D.virtualValue θ ≤ θ) ∧
      (∀ θ ∈ Set.Icc D.lo D.hi, θ < D.hi → D.virtualValue θ < θ) ∧ D.virtualValue D.hi = D.hi := by
  refine ⟨fun θ hθ => ?_, fun θ hθ hlt => ?_, ?_⟩
  · have := div_nonneg (oc_one_sub_cdf_nonneg D hθ) (D.dens_pos θ hθ).le
    simp only [TypeDensity.virtualValue]; linarith
  · have := div_pos (oc_one_sub_cdf_pos D hθ hlt) (D.dens_pos θ hθ)
    simp only [TypeDensity.virtualValue]; linarith
  · have h1 : D.cdf D.hi = 1 := D.integral_dens
    simp [TypeDensity.virtualValue, h1]

/-- **Example 23.F.1** (MWG, p. 903). With `g` strictly increasing on `e ≥ 0`, the optimal effort
`e(θ)` (maximising `v(e) + g(e)J(θ)`) is at most the first-best (ex post classically efficient)
effort `e*(θ)` (maximising `v(e) + g(e)θ`) for every `θ < θ̄`. -/
theorem example_23_F_1_le_firstBest (D : TypeDensity) {v g : ℝ → ℝ}
    (hg : StrictMonoOn g (Set.Ici 0)) {θ x y : ℝ} (hθ : θ ∈ Set.Icc D.lo D.hi) (hlt : θ < D.hi)
    (hx : OCArgmax (fun e => v e + g e * D.virtualValue θ) x)
    (hy : OCArgmax (fun e => v e + g e * θ) y) : x ≤ y :=
  oc_maximizer_mono hg ((oc_virtualValue_facts D).2.1 θ hθ hlt) hx hy

/-- **Example 23.F.1** (MWG, p. 903). At `θ̄`, `J(θ̄) = θ̄`: the optimal and the first-best effort
problems coincide, so with a unique maximiser `e(θ̄) = e*(θ̄)`. -/
theorem example_23_F_1_eq_firstBest_hi (D : TypeDensity) {v g : ℝ → ℝ} {x y : ℝ}
    (hc : StrictConcaveOn ℝ (Set.Ici 0) (fun e => v e + g e * D.hi))
    (hx : OCArgmax (fun e => v e + g e * D.virtualValue D.hi) x)
    (hy : OCArgmax (fun e => v e + g e * D.hi) y) : x = y := by
  rw [(oc_virtualValue_facts D).2.2] at hx
  exact oc_argmax_unique hc hx hy

/-- If `h'(0) > 0` then `0` does not maximise `h` over `e ≥ 0`. -/
theorem oc_not_argmax_zero {h : ℝ → ℝ} {d : ℝ} (hd : HasDerivAt h d 0) (hpos : 0 < d) :
    ¬ OCArgmax h 0 := by
  rintro ⟨-, hmax⟩
  have ht := hasDerivAt_iff_tendsto_slope.1 hd
  have hev : ∀ᶠ e in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < slope h 0 e :=
    (nhdsWithin_mono _ (fun e (he : 0 < e) => ne_of_gt he) |>.trans le_rfl)
      (ht.eventually (lt_mem_nhds hpos))
  obtain ⟨e, he, hpos'⟩ := (hev.and self_mem_nhdsWithin).exists
  rw [slope_def_field, sub_zero] at he
  have := hmax e (le_of_lt hpos')
  have : (h e - h 0) / e ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hpos'.le
  linarith

/-- **Example 23.F.1** (MWG, p. 903): `e(θ) < e*(θ)` for `θ < θ̄`. Hypotheses as printed: `v`, `g`
differentiable, `g'(0) = 0`, `g'(e) > 0` for `e > 0`, `v' > 0`; `g` strictly increasing on
`e ≥ 0` (which these imply with `g(0) = 0`). -/
theorem example_23_F_1_lt_firstBest (D : TypeDensity) {v g v' g' : ℝ → ℝ}
    (hv : ∀ e, HasDerivAt v (v' e) e) (hgd : ∀ e, HasDerivAt g (g' e) e) (hg'0 : g' 0 = 0)
    (hg'pos : ∀ e, 0 < e → 0 < g' e) (hv'pos : ∀ e, 0 ≤ e → 0 < v' e)
    (hg : StrictMonoOn g (Set.Ici 0)) {θ x y : ℝ} (hθ : θ ∈ Set.Icc D.lo D.hi) (hlt : θ < D.hi)
    (hx : OCArgmax (fun e => v e + g e * D.virtualValue θ) x)
    (hy : OCArgmax (fun e => v e + g e * θ) y) : x < y := by
  have hle := example_23_F_1_le_firstBest D hg hθ hlt hx hy
  rcases lt_or_eq_of_le hle with h | h
  · exact h
  · exfalso
    subst h
    rcases lt_or_eq_of_le hx.1 with hpos | hzero
    · have f1 := eq_23_F_6 (hv x) (hgd x) hpos hx
      have f2 := eq_23_F_6 (hv x) (hgd x) hpos hy
      have hJ := (oc_virtualValue_facts D).2.1 θ hθ hlt
      have := hg'pos x hpos
      nlinarith
    · rw [← hzero] at hy
      refine oc_not_argmax_zero (d := v' 0 + g' 0 * θ) ((hv 0).add ((hgd 0).mul_const θ)) ?_ hy
      rw [hg'0, zero_mul, add_zero]
      exact hv'pos 0 le_rfl

/-- A measurable function bounded on `[θ̲, θ̄]` is integrable for the type distribution. -/
theorem oc_integrable_of_bound (D : TypeDensity) {f : ℝ → ℝ} (hf : Measurable f) (C : ℝ)
    (hC : ∀ x ∈ Set.Icc D.lo D.hi, |f x| ≤ C) : Integrable f D.measure := by
  have := D.isProbabilityMeasure
  refine Integrable.of_bound hf.aestronglyMeasurable C ?_
  filter_upwards [mem_ae_iff.2 D.measure_compl_Icc] with x hx
  rw [Real.norm_eq_abs]
  exact hC x hx

/-- **Example 23.F.1** (MWG, pp. 901-903), instance. Types uniform on `[-2, -1]`
(`J(θ) = 2θ + 1`, nondecreasing), `g(e) = e²`, `v(e) = 2e - e²`, `ū = 0`. The contract
`e(θ) = -1/(2θ)`, `t(θ) = -1/(2θ) - 1/8` (written with `|θ|`) is feasible, gives `U(θ̲) = ū`,
solves the relaxed problem and hence is optimal; the first-best effort is `e*(θ) = 1/(1 - θ)`, and
`e(θ) < e*(θ)` for `θ < θ̄ = -1`, with equality at `θ̄`. -/
theorem example_23_F_1_instance :
    let D := uniformDensity (-2) (-1) (by norm_num)
    let v : ℝ → ℝ := fun e => 2 * e - e ^ 2
    let g : ℝ → ℝ := fun e => e ^ 2
    let es : ℝ → ℝ := fun θ => 1 / (2 * |θ|)
    let ts : ℝ → ℝ := fun θ => 1 / (2 * |θ|) - 1 / 8
    OCFeasible D v g 0 es ts ∧ ocU g es ts D.lo = 0 ∧
      (∀ e t, OCFeasible D v g 0 e t → ocPayoff D v e t ≤ ocPayoff D v es ts) ∧
      (∀ θ ∈ Set.Icc D.lo D.hi, OCArgmax (fun x => v x + g x * θ) (1 / (1 - θ))) ∧
      (∀ θ ∈ Set.Icc D.lo D.hi, θ < D.hi → es θ < 1 / (1 - θ)) ∧ es D.hi = 1 / (1 - D.hi) := by
  intro D v g es ts
  have hlo : D.lo = -2 := rfl
  have hhi : D.hi = -1 := rfl
  -- basic facts about `e(θ)` on `[-2, -1]`
  have hes : ∀ θ ∈ Set.Icc D.lo D.hi, 2 * -θ * es θ = 1 ∧ 1 / 4 ≤ es θ ∧ es θ ≤ 1 / 2 := by
    intro θ hθ
    rw [hlo, hhi] at hθ
    have hθ0 : θ < 0 := by linarith [hθ.2]
    simp only [es, abs_of_neg hθ0]
    refine ⟨by have := hθ0.ne; field_simp, ?_, ?_⟩
    · rw [le_div_iff₀ (by linarith)]; linarith [hθ.1]
    · rw [div_le_iff₀ (by linarith)]; linarith [hθ.2]
  have hesm : Measurable es :=
    measurable_const.div (measurable_const.mul continuous_abs.measurable)
  have hJ : ∀ θ ∈ Set.Icc D.lo D.hi, D.virtualValue θ = 2 * θ + 1 := by
    intro θ hθ
    have h := oa_uniform_virtualValue (a := (-2 : ℝ)) (b := -1) (by norm_num) (x := θ) hθ
    exact h.trans (by ring)
  have hr : ∀ θ ∈ Set.Icc D.lo D.hi, (1 - D.cdf θ) / D.dens θ = -1 - θ := by
    intro θ hθ
    have hd : D.dens θ = ((-1) - (-2) : ℝ)⁻¹ := by
      change (Set.Icc (-2 : ℝ) (-1)).indicator (fun _ => ((-1) - (-2) : ℝ)⁻¹) θ = _
      exact Set.indicator_of_mem hθ _
    have h := oa_uniform_cdf (a := (-2 : ℝ)) (b := -1) (by norm_num) (x := θ) hθ
    change (1 - (uniformDensity (-2) (-1) (by norm_num)).cdf θ) / D.dens θ = _
    rw [h, hd]; norm_num; ring
  have hfeas : OCFeasible D v g 0 es ts := by
    refine ⟨fun θ => by simp only [es]; positivity, fun θ hθ θh hθh => ?_, fun θ hθ => ?_,
      oc_integrable_of_bound D ((measurable_const.mul hesm).sub (hesm.pow_const 2)) 1
        fun θ hθ => ?_,
      oc_integrable_of_bound D (hesm.sub measurable_const) 1 fun θ hθ => ?_,
      oc_integrable_of_bound D (measurable_id.mul (hesm.pow_const 2)) 1 fun θ hθ => ?_,
      oc_integrable_of_bound D ((hesm.pow_const 2).mul ((measurable_const.sub
        D.continuous_cdf.measurable).div D.measurable_dens)) 1 fun θ hθ => ?_⟩
    · obtain ⟨he, -, -⟩ := hes θ hθ
      have key : (θ * es θ ^ 2 + (es θ - 1 / 8)) - (θ * es θh ^ 2 + (es θh - 1 / 8)) =
          (-θ) * (es θh - es θ) ^ 2 := by linear_combination (es θh - es θ) * he
      have hθ0 : 0 ≤ -θ := by rw [hlo, hhi] at hθ; linarith [hθ.2]
      have := mul_nonneg hθ0 (sq_nonneg (es θh - es θ))
      simp only [g, ts]
      change θ * es θh ^ 2 + (es θh - 1 / 8) ≤ θ * es θ ^ 2 + (es θ - 1 / 8)
      linarith
    · obtain ⟨he, h1, -⟩ := hes θ hθ
      simp only [ocU, g, ts]
      change (0 : ℝ) ≤ es θ - 1 / 8 + θ * es θ ^ 2
      nlinarith
    · obtain ⟨-, h1, h2⟩ := hes θ hθ
      rw [abs_le]; constructor <;> nlinarith
    · obtain ⟨-, h1, h2⟩ := hes θ hθ
      simp only [ts]
      change |es θ - 1 / 8| ≤ 1
      rw [abs_le]; constructor <;> linarith
    · obtain ⟨-, h1, h2⟩ := hes θ hθ
      have := hθ; rw [hlo, hhi] at this
      simp only [g]
      rw [abs_le]; constructor <;> nlinarith [this.1, this.2]
    · obtain ⟨-, h1, h2⟩ := hes θ hθ
      have := hθ; rw [hlo, hhi] at this
      simp only [g]
      rw [hr θ hθ, abs_le]; constructor <;> nlinarith [this.1, this.2]
  have hU : ocU g es ts D.lo = 0 := by
    rw [hlo]; simp only [ocU, g, ts, es]; norm_num
  refine ⟨hfeas, hU, fun e t h => example_23_F_1 D hfeas hU (fun θ hθ => ?_) h,
    fun θ hθ => ?_, fun θ hθ hlt => ?_, ?_⟩
  · obtain ⟨he, h1, -⟩ := hes θ hθ
    refine ⟨by linarith, fun x _ => ?_⟩
    have hθ0 : 0 ≤ -θ := by rw [hlo, hhi] at hθ; linarith [hθ.2]
    have key : (v (es θ) + g (es θ) * D.virtualValue θ) - (v x + g x * D.virtualValue θ) =
        2 * (-θ) * (x - es θ) ^ 2 := by
      rw [hJ θ hθ]; simp only [v, g]; linear_combination (2 * (x - es θ)) * he
    have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hθ0) (sq_nonneg (x - es θ))
    linarith
  · have hθ1 : 0 < 1 - θ := by rw [hlo, hhi] at hθ; linarith [hθ.2]
    have hy : (1 - θ) * (1 / (1 - θ)) = 1 := by field_simp
    refine ⟨by positivity, fun x _ => ?_⟩
    have key : (v (1 / (1 - θ)) + g (1 / (1 - θ)) * θ) - (v x + g x * θ) =
        (1 - θ) * (x - 1 / (1 - θ)) ^ 2 := by
      simp only [v, g]; linear_combination (2 * (x - 1 / (1 - θ))) * hy
    have := mul_nonneg hθ1.le (sq_nonneg (x - 1 / (1 - θ)))
    linarith
  · rw [hlo, hhi] at hθ
    rw [hhi] at hlt
    have hθ0 : θ < 0 := by linarith
    simp only [es, abs_of_neg hθ0]
    rw [div_lt_div_iff₀ (by linarith) (by linarith)]
    linarith
  · rw [hhi]; simp only [es]; norm_num

end MWG.MechanismDesign
