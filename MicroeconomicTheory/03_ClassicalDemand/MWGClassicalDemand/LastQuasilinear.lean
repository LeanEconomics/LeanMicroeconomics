/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGClassicalDemand.CloserQuasilinear
import MWGClassicalDemand.WelfareLinearDemand
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Instances.Matrix

/-!
# Exercise 3.I.8(a), "only if": wealth-independent demand comes from quasilinear utility

MWG, Exercise 3.I.8(a), p. 103: the demands for goods 1 and 2 do not depend on wealth; "write
down the most general class of utility functions whose demand has this property". The "if"
direction (quasilinear utility gives wealth-independent demand) is `exercise_3_I_8a`. Here the
converse is proved, with numeraire `k` (the book's good 3, `p₃ = 1`), on the quasilinear
consumption set `X = ℝ^{L-1}_+ × ℝ` of Definition 3.B.7 (on `ℝ^L_+` wealth-independence of a
nonzero demand is impossible at low wealth).

Hypotheses: `u` is continuous on `X` and strictly increasing in good `k`; on the normalized
prices `P = {p ≫ 0, p_k = 1}` the demand for the other goods is a continuous function `y(p)`,
independent of wealth: for every `p ∈ P` and every `w ∈ ℝ`, the bundle
`y(p) + (w - p·y(p)) e_k` solves the UMP on `X`.

Conclusion (`exercise_3_I_8a_only_if`): with `E(p)` the expenditure needed at prices `p` to
reach the utility of the reference bundle `y(1, …, 1)`, the concave function
`φ(x) = inf_{p ∈ P} (p·x - x_k - E(p))` (it does not depend on `x_k`) makes `x_k + φ(x)` a
representation of `u` on all bundles the consumer ever demands, `y(p) + t e_k`. If every bundle
of `X` is demanded at some prices, `x_k + φ(x)` represents `u` on all of `X`
(`exercise_3_I_8a_only_if_all`). An instance satisfying all hypotheses:
`last_3_I_8a_instance` (`u = x₂ + 2√x₁`).

Route (no differentiability is assumed): for a level `Δ` let `τ_Δ(p)` be the numeraire amount on
the demand line at `p` that is indifferent to `y(p⁰) + Δ e_k` (intermediate value theorem).
Revealed preference gives `τ_Δ(p') - τ_Δ(p) ≥ p·(y(p) - y(p'))`, hence
`|D(p') - D(p)| ≤ |(p' - p)·(y(p') - y(p))|` for `D = τ_Δ - τ_0`; by continuity of `y`, `D` has
zero derivative along segments of the convex set `P`, so it is constant: `τ_Δ = τ_0 + Δ`
(the expenditure function is `E(p) + Δ`, the quasilinear form). The utility is then recovered by
duality as `inf_p (p·x - E(p))`.
-/

namespace MWG.ClassicalDemand

open MWG.ConsumerChoice Kreps.PreferenceProperties Filter Topology Asymptotics

variable {L : ℕ}

/-- The normalized prices `P = {p ≫ 0, p_k = 1}`. -/
def lastNormPrices (k : Fin L) : Set (Fin L → ℝ) := {p | StrictlyPositive p ∧ p k = 1}

/-- `P` is convex. -/
theorem lastNormPrices_convex (k : Fin L) : Convex ℝ (lastNormPrices k) := by
  intro p hp q hq a b ha hb hab
  refine ⟨fun l => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have h1 := hp.1 l
    have h2 := hq.1 l
    rcases eq_or_lt_of_le ha with h | h
    · rw [← h, zero_add] at hab
      rw [← h, hab]
      linarith
    · nlinarith
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hp.2, hq.2]
    linarith

/-- A function whose increments are bounded by `|(p' - p)·(y(p') - y(p))|` with `y` continuous
is constant on a convex set. -/
theorem last_const_of_small_variation {P : Set (Fin L → ℝ)} (hP : Convex ℝ P)
    {D : (Fin L → ℝ) → ℝ} {y : (Fin L → ℝ) → Fin L → ℝ} (hy : ContinuousOn y P)
    (hb : ∀ p ∈ P, ∀ p' ∈ P, |D p' - D p| ≤ |(p' - p) ⬝ᵥ (y p' - y p)|) {p q : Fin L → ℝ}
    (hp : p ∈ P) (hq : q ∈ P) : D q = D p := by
  set γ : ℝ → Fin L → ℝ := fun s => p + s • (q - p) with hγ
  have hγP : Set.MapsTo γ (Set.Icc 0 1) P := fun s hs => hP.add_smul_sub_mem hp hq hs
  have hγc : Continuous γ := by
    simp only [hγ]
    fun_prop
  set f : ℝ → ℝ := fun s => D (γ s) with hf
  set h : ℝ → ℝ := fun s => (q - p) ⬝ᵥ y (γ s) with hh
  have hhc : ContinuousOn h (Set.Icc 0 1) :=
    (continuous_const.dotProduct continuous_id).comp_continuousOn
      (hy.comp hγc.continuousOn hγP)
  have hder : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt f 0 (Set.Icc 0 1) s := by
    intro s hs
    rw [hasDerivWithinAt_iff_isLittleO]
    simp only [smul_zero, sub_zero]
    refine isLittleO_iff.mpr fun c hc => ?_
    have hcont := hhc s hs
    rw [Metric.continuousWithinAt_iff] at hcont
    obtain ⟨δ, hδ, hball⟩ := hcont c hc
    have hmem : Set.Icc 0 1 ∩ Metric.ball s δ ∈ 𝓝[Set.Icc 0 1] s :=
      inter_mem_nhdsWithin _ (Metric.ball_mem_nhds s hδ)
    filter_upwards [hmem] with s' hs'
    have hd := hball hs'.1 hs'.2
    rw [Real.dist_eq] at hd
    have hbnd := hb (γ s) (hγP hs) (γ s') (hγP hs'.1)
    have hdiff : γ s' - γ s = (s' - s) • (q - p) := by
      simp only [hγ]
      module
    rw [hdiff, smul_dotProduct, smul_eq_mul, dotProduct_sub, abs_mul] at hbnd
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    calc |f s' - f s| ≤ |s' - s| * |(q - p) ⬝ᵥ y (γ s') - (q - p) ⬝ᵥ y (γ s)| := hbnd
      _ ≤ |s' - s| * c := mul_le_mul_of_nonneg_left hd.le (abs_nonneg _)
      _ = c * |s' - s| := mul_comm _ _
  have hconst := constant_of_derivWithin_zero (f := f) (a := 0) (b := 1)
    (fun s hs => (hder s hs).differentiableWithinAt)
    (fun s hs => (hder s (Set.Ico_subset_Icc_self hs)).derivWithin
      (uniqueDiffOn_Icc zero_lt_one s (Set.Ico_subset_Icc_self hs)))
    1 (Set.right_mem_Icc.mpr zero_le_one)
  simp only [hf, hγ, one_smul, zero_smul, add_zero, add_sub_cancel] at hconst
  exact hconst

/-- **Exercise 3.I.8(a)** (MWG, p. 103), "only if". Let `u` be continuous on the quasilinear
consumption set `X = {x : x_l ≥ 0, l ≠ k}`, strictly increasing in the numeraire `k`, and let the
Walrasian demand at normalized prices `p ∈ P` (`p ≫ 0`, `p_k = 1`) be wealth-independent for the
goods `l ≠ k`: `y(p) + (w - p·y(p)) e_k ∈ x(p, w)` for all `w`, with `y` continuous on `P`,
`y(p) ∈ X`, `y_k(p) = 0`. Then there is `φ`, independent of `x_k`, such that `x_k + φ(x)`
represents `u` on every bundle `y(p) + t e_k` the consumer demands. -/
theorem exercise_3_I_8a_only_if {k : Fin L} {u : (Fin L → ℝ) → ℝ}
    {y : (Fin L → ℝ) → Fin L → ℝ} (hu : ContinuousOn u (quasilinearDomain k))
    (hmono : ∀ x ∈ quasilinearDomain k, ∀ α : ℝ, 0 < α → u x < u (x + α • unitVec k))
    (hyX : ∀ p ∈ lastNormPrices k, y p ∈ quasilinearDomain k ∧ y p k = 0)
    (hd : ∀ p ∈ lastNormPrices k, ∀ w : ℝ,
      y p + (w - p ⬝ᵥ y p) • unitVec k ∈ walrasianDemandOn (quasilinearDomain k) u p w)
    (hy : ContinuousOn y (lastNormPrices k)) :
    ∃ φ : (Fin L → ℝ) → ℝ, (∀ x : Fin L → ℝ, ∀ t : ℝ, φ (x + t • unitVec k) = φ x) ∧
      ∀ p ∈ lastNormPrices k, ∀ s : ℝ, ∀ p' ∈ lastNormPrices k, ∀ s' : ℝ,
        (u (y p + s • unitVec k) ≤ u (y p' + s' • unitVec k) ↔
          (y p + s • unitVec k) k + φ (y p + s • unitVec k) ≤
            (y p' + s' • unitVec k) k + φ (y p' + s' • unitVec k)) := by
  classical
  set X := quasilinearDomain k with hX
  set e : Fin L → ℝ := unitVec k with he
  set P := lastNormPrices k with hP
  set p0 : Fin L → ℝ := fun _ => 1 with hp0
  have hp0P : p0 ∈ P := ⟨fun _ => one_pos, rfl⟩
  have hdot : ∀ p ∈ P, ∀ z : Fin L → ℝ, ∀ t : ℝ, p ⬝ᵥ (z + t • e) = p ⬝ᵥ z + t := by
    intro p hp z t
    rw [dotProduct_add, dotProduct_smul, he, unitVec, dotProduct_single, hp.2]
    simp
  have hek : e k = 1 := by simp [he, unitVec]
  have hlineX : ∀ p ∈ P, ∀ t : ℝ, y p + t • e ∈ X := fun p hp t =>
    quasilinearDomain_shift (hyX p hp).1 t
  have hlinek : ∀ p ∈ P, ∀ t : ℝ, (y p + t • e) k = t := by
    intro p hp t
    simp [(hyX p hp).2, hek]
  -- revealed preference along the demand line
  have hA : ∀ p ∈ P, ∀ z ∈ X, ∀ t : ℝ, p ⬝ᵥ z ≤ p ⬝ᵥ y p + t → u z ≤ u (y p + t • e) := by
    intro p hp z hz t hzt
    have hdem := hd p hp (p ⬝ᵥ y p + t)
    rw [add_sub_cancel_left] at hdem
    exact hdem.2 z ⟨hz, hzt⟩
  have hstrict : ∀ p ∈ P, ∀ t t' : ℝ, t < t' → u (y p + t • e) < u (y p + t' • e) := by
    intro p hp t t' htt
    have := hmono _ (hlineX p hp t) (t' - t) (sub_pos.mpr htt)
    rwa [add_assoc, ← add_smul, add_sub_cancel] at this
  have hB : ∀ p ∈ P, ∀ z ∈ X, ∀ t : ℝ, p ⬝ᵥ z < p ⬝ᵥ y p + t → u z < u (y p + t • e) := by
    intro p hp z hz t hzt
    have h1 := hA p hp z hz (p ⬝ᵥ z - p ⬝ᵥ y p) (by linarith)
    exact h1.trans_lt (hstrict p hp _ _ (by linarith))
  -- every level `y(p⁰) + Δ e_k` is crossed by every demand line
  have hcross : ∀ Δ : ℝ, ∀ p : Fin L → ℝ, ∃ τ : ℝ, p ∈ P →
      u (y p + τ • e) = u (y p0 + Δ • e) := by
    intro Δ p
    by_cases hp : p ∈ P
    · set t₁ := p ⬝ᵥ (y p0 + Δ • e) - p ⬝ᵥ y p
      set t₀ := p0 ⬝ᵥ y p0 + Δ - p0 ⬝ᵥ y p
      have h1 : u (y p0 + Δ • e) ≤ u (y p + t₁ • e) :=
        hA p hp _ (hlineX p0 hp0P Δ) t₁ (by simp only [t₁]; linarith)
      have h0 : u (y p + t₀ • e) ≤ u (y p0 + Δ • e) :=
        hA p0 hp0P _ (hlineX p hp t₀) Δ (by rw [hdot p0 hp0P]; simp only [t₀]; linarith)
      have hle : t₀ ≤ t₁ := by
        by_contra hlt
        rw [not_le] at hlt
        have := hstrict p hp _ _ hlt
        linarith
      have hc : ContinuousOn (fun t => u (y p + t • e)) (Set.Icc t₀ t₁) :=
        hu.comp (by fun_prop) fun t _ => hlineX p hp t
      obtain ⟨τ, -, hτ⟩ := intermediate_value_Icc hle hc ⟨h0, h1⟩
      exact ⟨τ, fun _ => hτ⟩
    · exact ⟨0, fun h => absurd h hp⟩
  choose τ hτ using hcross
  -- the key inequality
  have hstar : ∀ Δ : ℝ, ∀ p ∈ P, ∀ p' ∈ P, p ⬝ᵥ (y p - y p') ≤ τ Δ p' - τ Δ p := by
    intro Δ p hp p' hp'
    by_contra hlt
    rw [not_le] at hlt
    have hc : p ⬝ᵥ (y p' + τ Δ p' • e) < p ⬝ᵥ y p + τ Δ p := by
      rw [hdot p hp, dotProduct_sub] at *
      linarith
    have := hB p hp _ (hlineX p' hp' _) _ hc
    rw [hτ Δ p hp, hτ Δ p' hp'] at this
    exact lt_irrefl _ this
  -- `τ_Δ - τ_0` is constant
  have hτ0 : ∀ Δ : ℝ, τ Δ p0 = Δ := by
    intro Δ
    have h := hτ Δ p0 hp0P
    rcases lt_trichotomy (τ Δ p0) Δ with hlt | heq | hgt
    · exact absurd h (hstrict p0 hp0P _ _ hlt).ne
    · exact heq
    · exact absurd h (hstrict p0 hp0P _ _ hgt).ne'
  have hshift : ∀ Δ : ℝ, ∀ p ∈ P, τ Δ p = τ 0 p + Δ := by
    intro Δ p hp
    have hb : ∀ q ∈ P, ∀ q' ∈ P, |(τ Δ q' - τ 0 q') - (τ Δ q - τ 0 q)| ≤
        |(q' - q) ⬝ᵥ (y q' - y q)| := by
      intro q hq q' hq'
      have h1 := hstar Δ q hq q' hq'
      have h2 := hstar Δ q' hq' q hq
      have h3 := hstar 0 q hq q' hq'
      have h4 := hstar 0 q' hq' q hq
      have hexp : (q' - q) ⬝ᵥ (y q' - y q) =
          q' ⬝ᵥ (y q' - y q) - q ⬝ᵥ (y q' - y q) := by
        rw [sub_dotProduct]
      have hneg : q ⬝ᵥ (y q - y q') = -(q ⬝ᵥ (y q' - y q)) := by
        rw [← dotProduct_neg, neg_sub]
      rw [hneg] at h1 h3
      rw [hexp, abs_le]
      constructor
      · linarith [neg_abs_le (q' ⬝ᵥ (y q' - y q) - q ⬝ᵥ (y q' - y q))]
      · linarith [neg_le_abs (q' ⬝ᵥ (y q' - y q) - q ⬝ᵥ (y q' - y q))]
    have hc := last_const_of_small_variation (lastNormPrices_convex k) hy hb hp0P hp
    rw [hτ0, hτ0] at hc
    linarith
  -- the expenditure function at the reference level and the dual utility
  set E : (Fin L → ℝ) → ℝ := fun p => p ⬝ᵥ y p + τ 0 p with hE
  set φ : (Fin L → ℝ) → ℝ := fun x => ⨅ p : P, ((p : Fin L → ℝ) ⬝ᵥ x - x k - E p) with hφ
  have hφinv : ∀ x : Fin L → ℝ, ∀ t : ℝ, φ (x + t • e) = φ x := by
    intro x t
    simp only [hφ]
    congr 1
    funext p
    rw [hdot p p.2, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hek]
    ring
  -- on a demanded bundle `y(p') + s e_k`, `x_k + φ(x) = s - τ_0(p')`
  have hU : ∀ p' ∈ P, ∀ s : ℝ, (y p' + s • e) k + φ (y p' + s • e) = s - τ 0 p' := by
    intro p' hp' s
    rw [hlinek p' hp' s]
    have hterm : ∀ p : P, ((p : Fin L → ℝ) ⬝ᵥ (y p' + s • e) - (y p' + s • e) k - E p) =
        (p : Fin L → ℝ) ⬝ᵥ (y p' - y p) - τ 0 p := by
      intro p
      rw [hdot p p.2, hlinek p' hp' s, dotProduct_sub]
      simp only [hE]
      ring
    have hleast : IsLeast (Set.range fun p : P => (p : Fin L → ℝ) ⬝ᵥ (y p' - y p) - τ 0 p)
        (-τ 0 p') := by
      refine ⟨⟨⟨p', hp'⟩, by simp⟩, ?_⟩
      rintro _ ⟨p, rfl⟩
      have := hstar 0 p p.2 p' hp'
      have hneg : (p : Fin L → ℝ) ⬝ᵥ (y p - y p') = -((p : Fin L → ℝ) ⬝ᵥ (y p' - y p)) := by
        rw [← dotProduct_neg, neg_sub]
      rw [hneg] at this
      simp only
      linarith
    have hφx : φ (y p' + s • e) = -τ 0 p' := by
      simp only [hφ]
      rw [show (fun p : P => (p : Fin L → ℝ) ⬝ᵥ (y p' + s • e) - (y p' + s • e) k - E p) =
        fun p : P => (p : Fin L → ℝ) ⬝ᵥ (y p' - y p) - τ 0 p from funext hterm]
      exact hleast.csInf_eq
    rw [hφx]
    ring
  -- every demanded bundle is indifferent to `y(p⁰) + (s - τ_0(p')) e_k`
  have hlev : ∀ p' ∈ P, ∀ s : ℝ, u (y p' + s • e) = u (y p0 + (s - τ 0 p') • e) := by
    intro p' hp' s
    have := hτ (s - τ 0 p') p' hp'
    rwa [hshift _ p' hp', add_sub_cancel] at this
  refine ⟨φ, hφinv, fun p hp s p' hp' s' => ?_⟩
  rw [hU p hp s, hU p' hp' s', hlev p hp s, hlev p' hp' s']
  constructor
  · intro hle
    by_contra hlt
    rw [not_le] at hlt
    exact absurd hle (not_le.mpr (hstrict p0 hp0P _ _ hlt))
  · intro hle
    rcases eq_or_lt_of_le hle with heq | hlt
    · rw [heq]
    · exact (hstrict p0 hp0P _ _ hlt).le

/-- **Exercise 3.I.8(a)** (MWG, p. 103), "only if", when every bundle of `X` is demanded at some
normalized prices: then `u` is represented on all of `X` by the quasilinear `x_k + φ(x)`. -/
theorem exercise_3_I_8a_only_if_all {k : Fin L} {u : (Fin L → ℝ) → ℝ}
    {y : (Fin L → ℝ) → Fin L → ℝ} (hu : ContinuousOn u (quasilinearDomain k))
    (hmono : ∀ x ∈ quasilinearDomain k, ∀ α : ℝ, 0 < α → u x < u (x + α • unitVec k))
    (hyX : ∀ p ∈ lastNormPrices k, y p ∈ quasilinearDomain k ∧ y p k = 0)
    (hd : ∀ p ∈ lastNormPrices k, ∀ w : ℝ,
      y p + (w - p ⬝ᵥ y p) • unitVec k ∈ walrasianDemandOn (quasilinearDomain k) u p w)
    (hy : ContinuousOn y (lastNormPrices k))
    (hall : ∀ x ∈ quasilinearDomain k, ∃ p ∈ lastNormPrices k, ∃ t : ℝ,
      x = y p + t • unitVec k) :
    ∃ φ : (Fin L → ℝ) → ℝ, (∀ x : Fin L → ℝ, ∀ t : ℝ, φ (x + t • unitVec k) = φ x) ∧
      RepresentsOn (quasilinearDomain k) (fun x => x k + φ x) (utilityPref u) := by
  obtain ⟨φ, hinv, hrep⟩ := exercise_3_I_8a_only_if hu hmono hyX hd hy
  refine ⟨φ, hinv, fun x hx x' hx' => ?_⟩
  obtain ⟨p, hp, s, rfl⟩ := hall x hx
  obtain ⟨p', hp', s', rfl⟩ := hall x' hx'
  exact hrep p' hp' s' p hp s

/-- The instance `u(x) = x₂ + 2√x₁` (two goods, numeraire `k = 2`). -/
noncomputable def lastSqrtUtility (x : Fin 2 → ℝ) : ℝ := x 1 + 2 * Real.sqrt (x 0)

/-- Its wealth-independent demand for good 1, `y(p) = (1/p₁², 0)`. -/
noncomputable def lastSqrtDemand (p : Fin 2 → ℝ) : Fin 2 → ℝ := ![1 / p 0 ^ 2, 0]

/-- **Exercise 3.I.8(a)** (MWG, p. 103): the hypotheses of `exercise_3_I_8a_only_if` are
consistent. For `u(x) = x₂ + 2√x₁` on `ℝ_+ × ℝ` and `y(p) = (1/p₁², 0)`, all five hold. -/
theorem last_3_I_8a_instance :
    ContinuousOn lastSqrtUtility (quasilinearDomain (1 : Fin 2)) ∧
    (∀ x ∈ quasilinearDomain (1 : Fin 2), ∀ α : ℝ, 0 < α →
      lastSqrtUtility x < lastSqrtUtility (x + α • unitVec 1)) ∧
    (∀ p ∈ lastNormPrices (1 : Fin 2),
      lastSqrtDemand p ∈ quasilinearDomain (1 : Fin 2) ∧ lastSqrtDemand p 1 = 0) ∧
    (∀ p ∈ lastNormPrices (1 : Fin 2), ∀ w : ℝ,
      lastSqrtDemand p + (w - p ⬝ᵥ lastSqrtDemand p) • unitVec 1 ∈
        walrasianDemandOn (quasilinearDomain (1 : Fin 2)) lastSqrtUtility p w) ∧
    ContinuousOn lastSqrtDemand (lastNormPrices (1 : Fin 2)) := by
  have he0 : (unitVec (1 : Fin 2)) 0 = 0 := by simp [unitVec]
  have he1 : (unitVec (1 : Fin 2)) 1 = 1 := by simp [unitVec]
  have hdot : ∀ p z : Fin 2 → ℝ, p ⬝ᵥ z = p 0 * z 0 + p 1 * z 1 := fun p z => by
    simp [dotProduct, Fin.sum_univ_two]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold lastSqrtUtility
    exact Continuous.continuousOn (by fun_prop)
  · intro x _ α hα
    simp only [lastSqrtUtility, Pi.add_apply, Pi.smul_apply, smul_eq_mul, he0, he1]
    simp only [mul_zero, add_zero, mul_one]
    linarith
  · intro p _
    refine ⟨fun l hl => ?_, by simp [lastSqrtDemand]⟩
    fin_cases l
    · simp only [lastSqrtDemand, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      positivity
    · exact absurd rfl hl
  · intro p hp w
    have hp0 := hp.1 0
    have hp1 : p 1 = 1 := hp.2
    set b := lastSqrtDemand p + (w - p ⬝ᵥ lastSqrtDemand p) • unitVec (1 : Fin 2) with hb
    have hyd : p ⬝ᵥ lastSqrtDemand p = 1 / p 0 := by
      rw [hdot]
      simp only [lastSqrtDemand, Matrix.cons_val_zero, Matrix.cons_val_one, hp1]
      field_simp
      ring
    have hb0 : b 0 = 1 / p 0 ^ 2 := by
      rw [hb, Pi.add_apply, Pi.smul_apply, he0, smul_eq_mul, mul_zero, add_zero]
      simp [lastSqrtDemand]
    have hb1 : b 1 = w - 1 / p 0 := by
      rw [hb, Pi.add_apply, Pi.smul_apply, he1, hyd, smul_eq_mul, mul_one]
      simp [lastSqrtDemand]
    have hsq : Real.sqrt (1 / p 0 ^ 2) = 1 / p 0 := by
      rw [Real.sqrt_div' _ (sq_nonneg _), Real.sqrt_sq hp0.le, Real.sqrt_one]
    refine ⟨⟨fun l hl => ?_, ?_⟩, fun z hz => ?_⟩
    · fin_cases l
      · rw [Fin.zero_eta, hb0]; positivity
      · exact absurd rfl hl
    · rw [hdot, hb0, hb1, hp1]
      field_simp
      ring_nf
      exact le_rfl
    · have hz0 : 0 ≤ z 0 := hz.1 0 (by decide)
      have hz2 := hz.2
      rw [hdot, hp1] at hz2
      simp only [lastSqrtUtility, hb0, hb1, hsq]
      have hs := Real.sq_sqrt hz0
      have hs0 := Real.sqrt_nonneg (z 0)
      have key : 2 * Real.sqrt (z 0) - p 0 * z 0 ≤ 1 / p 0 := by
        rw [le_div_iff₀ hp0]
        nlinarith [sq_nonneg (p 0 * Real.sqrt (z 0) - 1)]
      have : 2 * (1 / p 0) = 1 / p 0 + 1 / p 0 := by ring
      linarith
  · refine continuousOn_pi.mpr fun i => ?_
    fin_cases i
    · simp only [lastSqrtDemand, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      exact ContinuousOn.div continuousOn_const ((continuous_apply 0).continuousOn.pow 2)
        fun p hp => pow_ne_zero 2 (hp.1 0).ne'
    · simp only [lastSqrtDemand, Fin.mk_one, Fin.isValue, Matrix.cons_val_one]
      exact continuousOn_const

end MWG.ClassicalDemand
