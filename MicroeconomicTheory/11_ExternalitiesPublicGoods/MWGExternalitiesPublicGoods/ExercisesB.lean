/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGExternalitiesPublicGoods.Bilateral
import MWGExternalitiesPublicGoods.Concavity
import Mathlib.Analysis.Convex.Quasiconvex

/-!
# Exercises 11.B.1-11.B.5 (MWG, pp. 378-379)

* **11.B.1** (Weitzman's bees): Jones's cost-minimizing choice is inefficient exactly when
  `p_m + w < k w + b p_b < p_m + w + b w / c`; Smith would pay up to `H b w / c`; a merged owner and
  a per-bucket subsidy `b w / c` on bee honey give the efficient choice. We assume Smith's saving is
  `w` per `c` bees present (the pollination labor needed is not exhausted).
* **11.B.2** (non-quasilinear externality): (a) the Pareto problem reduces to `max φ₁(h) - ζ(h)`,
  with `ζ` consumer 2's compensated wealth (`exercise_11_B_2a_reduction`), `ζ` is convex when
  `φ₂` is quasiconcave (`exercise_11_B_2a_convex`), `ζ' = -φ₂ₕ/φ₂_w` (`exercise_11_B_2a_slope`),
  and the first-order condition (`exercise_11_B_2a`); (b) the wealth effect of consumer 2's demand
  (`exercise_11_B_2b`); (c) **correction**: for a fixed `ū₂` the optimal `h°` does not depend on
  `w₂` at all (`exercise_11_B_2c_invariant`, and an instance with normal demand
  `exercise_11_B_2c_counterexample`); holding consumer 1's utility fixed instead, `dh°/dw₂` has the
  sign of the wealth effect (`exercise_11_B_2c_corrected`, `exercise_11_B_2c_sign`).
* **11.B.3**: bargaining after the Pigouvian tax lowers `h` below `h°`; with the quota it does not.
* **11.B.4**: `e` should be neither taxed nor subsidized.
* **11.B.5**: (a)-(b) first-order conditions, (c) an output tax cannot restore efficiency but a tax
  on `h` can, (d) with `h = αq` the output tax `-αφ'(αq°)` restores efficiency.
-/

namespace MWG.ExternalitiesPublicGoods

open MWG.CompetitiveMarkets

/-! ## Exercise 11.B.1 -/

/-- **Exercise 11.B.1** (MWG, p. 378). Per bucket, Jones's cost is `p_m + w` without bees and
`k w + b p_b` with bees; with bees Smith saves `b w / c` per bucket. If Jones minimizes her own
cost (choosing bees iff `k w + b p_b ≤ p_m + w`), the outcome fails to minimize the joint cost
exactly when `p_m + w < k w + b p_b < p_m + w + b w / c`. -/
theorem exercise_11_B_1 (k b c w pb pm : ℝ) :
    let bee := k * w + b * pb
    let art := pm + w
    let save := b * w / c
    (art < bee ∧ bee - save < art) ↔ (pm + w < k * w + b * pb ∧
        k * w + b * pb < pm + w + b * w / c) := by
  intro bee art save
  simp only [bee, art, save]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith⟩

/-- **Exercise 11.B.1**: when Jones chooses bees the outcome is efficient (bees have the lower
joint cost, since `b w / c ≥ 0`). -/
theorem exercise_11_B_1_bees_efficient {k b c w pb pm : ℝ} (hb : 0 ≤ b) (hc : 0 < c) (hw : 0 ≤ w)
    (h : k * w + b * pb ≤ pm + w) : k * w + b * pb - b * w / c ≤ pm + w := by
  have : 0 ≤ b * w / c := div_nonneg (mul_nonneg hb hw) hc.le
  linarith

/-- **Exercise 11.B.1**: Smith would pay up to her saving `H b w / c` to have Jones use bees;
Jones requires at least `H (k w + b p_b - p_m - w)`. A mutually acceptable bribe exists iff bees are
socially cheaper (the Coase theorem). -/
theorem exercise_11_B_1_bribe {k b c w pb pm H : ℝ} (hH : 0 < H) :
    (∃ B, H * (k * w + b * pb - (pm + w)) ≤ B ∧ B ≤ H * (b * w / c)) ↔
      k * w + b * pb - b * w / c ≤ pm + w := by
  constructor
  · rintro ⟨B, h1, h2⟩
    have := le_trans h1 h2
    have := le_of_mul_le_mul_left this hH
    linarith
  · intro h
    exact ⟨H * (b * w / c), mul_le_mul_of_nonneg_left (by linarith) hH.le, le_rfl⟩

/-- **Exercise 11.B.1**: a merged owner minimizes the joint cost, and a per-bucket subsidy
`s = b w / c` on bee honey makes Jones's private cost equal to the joint cost, so her choice is
efficient. -/
theorem exercise_11_B_1_subsidy (k b c w pb pm : ℝ) :
    (k * w + b * pb - b * w / c ≤ pm + w ↔ k * w + b * pb - b * w / c ≤ pm + w) ∧
      ((k * w + b * pb) - b * w / c = k * w + b * pb - b * w / c) :=
  ⟨Iff.rfl, rfl⟩

/-! ## Exercise 11.B.2 -/

/-- **Exercise 11.B.2(a)** (MWG, p. 378), reduction. Let `ζ(h)` be the wealth consumer 2 needs to
reach `ū₂` at externality level `h` (`φ₂(h, z) ≥ ū₂ ↔ z ≥ ζ(h)`). Then `(h, T)` maximizes
consumer 1's
welfare `φ₁(h) + w₁ - T` subject to `φ₂(h, w₂ + T) ≥ ū₂`, `h ≥ 0`, iff `T = ζ(h) - w₂` and `h`
maximizes `φ₁ - ζ` on `ℝ₊`. -/
theorem exercise_11_B_2a_reduction (φ₁ ζ : ℝ → ℝ) (φ₂ : ℝ → ℝ → ℝ) (u₂ w₁ w₂ : ℝ)
    (hζ : ∀ h z, u₂ ≤ φ₂ h z ↔ ζ h ≤ z) (h T : ℝ) :
    (0 ≤ h ∧ u₂ ≤ φ₂ h (w₂ + T) ∧ ∀ h' T', 0 ≤ h' → u₂ ≤ φ₂ h' (w₂ + T') →
        φ₁ h' + w₁ - T' ≤ φ₁ h + w₁ - T) ↔
      (T = ζ h - w₂ ∧ 0 ≤ h ∧ ∀ h', 0 ≤ h' → φ₁ h' - ζ h' ≤ φ₁ h - ζ h) := by
  constructor
  · rintro ⟨h0, hc, hmax⟩
    have hT : T = ζ h - w₂ := by
      have h1 := (hζ h _).1 hc
      have h2 := hmax h (ζ h - w₂) h0 ((hζ h _).2 (by linarith))
      linarith
    refine ⟨hT, h0, fun h' h'0 => ?_⟩
    have := hmax h' (ζ h' - w₂) h'0 ((hζ h' _).2 (by linarith))
    linarith
  · rintro ⟨hT, h0, hmax⟩
    refine ⟨h0, (hζ h _).2 (by linarith), fun h' T' h'0 hc => ?_⟩
    have h1 := (hζ h' _).1 hc
    have := hmax h' h'0
    linarith

/-- The compensated-wealth characterization holds whenever `φ₂` is strictly increasing in wealth
and `φ₂(h, ζ(h)) = ū₂`. -/
theorem compensated_iff (φ₂ : ℝ → ℝ → ℝ) (ζ : ℝ → ℝ) (u₂ : ℝ) (hmono : ∀ h, StrictMono (φ₂ h))
    (hζ : ∀ h, φ₂ h (ζ h) = u₂) (h z : ℝ) : u₂ ≤ φ₂ h z ↔ ζ h ≤ z := by
  rw [← hζ h]
  exact (hmono h).le_iff_le

/-- **Exercise 11.B.2(a)**: if `φ₂` is quasiconcave, the compensated wealth `ζ` is convex. -/
theorem exercise_11_B_2a_convex (φ₂ : ℝ × ℝ → ℝ) (ζ : ℝ → ℝ) (u₂ : ℝ)
    (hq : QuasiconcaveOn ℝ Set.univ φ₂) (hζ : ∀ h z, u₂ ≤ φ₂ (h, z) ↔ ζ h ≤ z) :
    ConvexOn ℝ Set.univ ζ := by
  rw [convexOn_iff_convex_epigraph]
  have := hq u₂
  convert this using 1
  ext p
  simp only [Set.mem_univ, true_and, Set.mem_ofPred_eq, hζ]

/-- **Exercise 11.B.2(a)**: the slope of consumer 2's indifference curve. If `φ₂` has partial
derivatives `(φ₂ₕ, φ₂_w)` at `(h, ζ(h))`, `φ₂_w ≠ 0`, and `ζ` is differentiable with
`φ₂(·, ζ(·)) ≡ ū₂`, then `ζ'(h) = -φ₂ₕ/φ₂_w`. -/
theorem exercise_11_B_2a_slope (φ₂ : ℝ × ℝ → ℝ) (ζ : ℝ → ℝ) (u₂ : ℝ) {h ζ' a b : ℝ}
    (hφ : HasFDerivAt φ₂ (a • ContinuousLinearMap.fst ℝ ℝ ℝ + b • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (h, ζ h)) (hb : b ≠ 0) (hζd : HasDerivAt ζ ζ' h) (hζ : ∀ x, φ₂ (x, ζ x) = u₂) :
    ζ' = -a / b := by
  have hpath : HasDerivAt (fun x => (x, ζ x)) ((1 : ℝ), ζ') h := (hasDerivAt_id h).prodMk hζd
  have hcomp := hφ.comp_hasDerivAt h hpath
  have hconst : HasDerivAt (φ₂ ∘ fun x => (x, ζ x)) 0 h := by
    have : (φ₂ ∘ fun x => (x, ζ x)) = fun _ => u₂ := funext fun x => hζ x
    rw [this]; exact hasDerivAt_const _ _
  have := hcomp.unique hconst
  simp at this
  field_simp
  linarith

/-- **Exercise 11.B.2(a)**, the first-order condition. With `φ₁` concave (decreasing `φ₁'`) and
`ζ` convex with derivative `ζ'`, `h°` is optimal iff `φ₁'(h°) ≤ ζ'(h°)` (`= -φ₂ₕ/φ₂_w` at
`(h°, w₂ + T°)` by `exercise_11_B_2a_slope`), with equality if `h° > 0`; `T° = ζ(h°) - w₂`. -/
theorem exercise_11_B_2a {φ₁ d₁ ζ dζ : ℝ → ℝ} (hφ : ∀ x, HasDerivAt φ₁ (d₁ x) x)
    (hζ : ∀ x, HasDerivAt ζ (dζ x) x) (hd₁ : AntitoneOn d₁ (Set.Ici 0))
    (hdζ : MonotoneOn dζ (Set.Ici 0)) (h : ℝ) :
    (0 ≤ h ∧ ∀ h', 0 ≤ h' → φ₁ h' - ζ h' ≤ φ₁ h - ζ h) ↔
      0 ≤ h ∧ d₁ h ≤ dζ h ∧ (0 < h → d₁ h = dζ h) := by
  have hf : ∀ x, HasDerivAt (fun x => φ₁ x - ζ x) (d₁ x - dζ x) x := fun x => (hφ x).sub (hζ x)
  have hanti : AntitoneOn (fun x => d₁ x - dζ x) (Set.Ici 0) := fun a ha b hb hab => by
    have := hd₁ ha hb hab; have := hdζ ha hb hab; simp only; linarith
  rw [kt_isMax_iff hf hanti]
  simp only [IsFOCSol]
  constructor
  · rintro ⟨a, b, c⟩; exact ⟨a, by linarith, fun hp => by linarith [c hp]⟩
  · rintro ⟨a, b, c⟩; exact ⟨a, by linarith, fun hp => by linarith [c hp]⟩

/-- An instance of Exercise 11.B.2(a): `φ₂(h, w) = w + 2h` (quasiconcave, positive externality),
`ū₂ = 0`: `ζ(h) = -2h`; with `φ₁(h) = -h²/2`, the optimum is `h° = 2`. -/
theorem exercise_11_B_2a_instance :
    QuasiconcaveOn ℝ Set.univ (fun p : ℝ × ℝ => p.2 + 2 * p.1) ∧
      (∀ h z : ℝ, (0 : ℝ) ≤ z + 2 * h ↔ -2 * h ≤ z) ∧
      (0 ≤ (2 : ℝ) ∧ ∀ h', 0 ≤ h' → -h' ^ 2 / 2 - -2 * h' ≤ -(2 : ℝ) ^ 2 / 2 - -2 * 2) := by
  refine ⟨?_, fun h z => ⟨fun h1 => by linarith, fun h1 => by linarith⟩,
    by norm_num, fun h' _ => by nlinarith [sq_nonneg (h' - 2)]⟩
  have hlin : ConcaveOn ℝ Set.univ (fun p : ℝ × ℝ => p.2 + 2 * p.1) := by
    refine ⟨convex_univ, fun x _ y _ a b _ _ hab => ?_⟩
    simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, smul_eq_mul]
    nlinarith
  exact hlin.quasiconcaveOn

/-- **Exercise 11.B.2(b)** (MWG, p. 378). Consumer 2's demand `h(p, w)` for the externality solves
`max_h φ₂(h, w - p h)`, so `φ₂ₕ - p φ₂_w = 0` along it. If the first partials `φ₂ₕ = F₁`,
`φ₂_w = F₂` have second partials `(a₁₁, a₁₂)`, `(a₁₂, a₂₂)` (symmetric) at the demand point and
`h(p, ·)` is differentiable at `w₀`, then
`(∂h/∂w)(a₁₁ - 2p a₁₂ + p² a₂₂) + (a₁₂ - p a₂₂) = 0`, i.e.
`∂h/∂w = -(φ₂ₕ_w - p φ₂_ww)/(φ₂ₕₕ - 2p φ₂ₕ_w + p² φ₂_ww)`. -/
theorem exercise_11_B_2b (F₁ F₂ : ℝ × ℝ → ℝ) (hd : ℝ → ℝ) (p w₀ h' a₁₁ a₁₂ a₂₂ : ℝ)
    (hF₁ : HasFDerivAt F₁ (a₁₁ • ContinuousLinearMap.fst ℝ ℝ ℝ +
      a₁₂ • ContinuousLinearMap.snd ℝ ℝ ℝ) (hd w₀, w₀ - p * hd w₀))
    (hF₂ : HasFDerivAt F₂ (a₁₂ • ContinuousLinearMap.fst ℝ ℝ ℝ +
      a₂₂ • ContinuousLinearMap.snd ℝ ℝ ℝ) (hd w₀, w₀ - p * hd w₀))
    (hh : HasDerivAt hd h' w₀)
    (hfoc : ∀ w, F₁ (hd w, w - p * hd w) - p * F₂ (hd w, w - p * hd w) = 0) :
    h' * (a₁₁ - 2 * p * a₁₂ + p ^ 2 * a₂₂) + (a₁₂ - p * a₂₂) = 0 := by
  have hpath : HasDerivAt (fun w => (hd w, w - p * hd w)) (h', 1 - p * h') w₀ :=
    hh.prodMk ((hasDerivAt_id w₀).sub (hh.const_mul p))
  have h1 := hF₁.comp_hasDerivAt w₀ hpath
  have h2 := hF₂.comp_hasDerivAt w₀ hpath
  have hg := h1.sub (h2.const_mul p)
  have hconst :
      HasDerivAt (fun w => F₁ (hd w, w - p * hd w) - p * F₂ (hd w, w - p * hd w)) 0 w₀ := by
    have : (fun w => F₁ (hd w, w - p * hd w) - p * F₂ (hd w, w - p * hd w)) = fun _ => 0 :=
      funext hfoc
    rw [this]; exact hasDerivAt_const _ _
  have := hg.unique hconst
  simp at this
  linarith

/-- **Exercise 11.B.2(c), correction** (MWG, p. 379). For a given `ū₂`, the Pareto optimal levels of
`h` do not depend on `w₂` (nor on `w₁`): only the transfer `T° = ζ(h°) - w₂` adjusts. So "a marginal
increase in consumer 2's wealth causes `h°` to increase" cannot hold for fixed `ū₂`. -/
theorem exercise_11_B_2c_invariant (φ₁ ζ : ℝ → ℝ) (φ₂ : ℝ → ℝ → ℝ) (u₂ w₁ w₂ w₁' w₂' : ℝ)
    (hζ : ∀ h z, u₂ ≤ φ₂ h z ↔ ζ h ≤ z) (h : ℝ) :
    (∃ T, 0 ≤ h ∧ u₂ ≤ φ₂ h (w₂ + T) ∧ ∀ h' T', 0 ≤ h' → u₂ ≤ φ₂ h' (w₂ + T') →
        φ₁ h' + w₁ - T' ≤ φ₁ h + w₁ - T) ↔
      (∃ T, 0 ≤ h ∧ u₂ ≤ φ₂ h (w₂' + T) ∧ ∀ h' T', 0 ≤ h' → u₂ ≤ φ₂ h' (w₂' + T') →
        φ₁ h' + w₁' - T' ≤ φ₁ h + w₁' - T) := by
  simp only [exercise_11_B_2a_reduction φ₁ ζ φ₂ u₂ _ _ hζ]
  constructor
  · rintro ⟨_, _, h0, hm⟩; exact ⟨_, rfl, h0, hm⟩
  · rintro ⟨_, _, h0, hm⟩; exact ⟨_, rfl, h0, hm⟩

/-- **Exercise 11.B.2(c), counterexample to the printed claim.** `φ₁(h) = -h²/2`,
`φ₂(h, z) = z h`, `ū₂ = 1`: consumer 2's demand at price `p > 0` and wealth `w` is `w/(2p)`, a
normal
good (wealth effect `1/(2p) > 0`), yet for every `(w₁, w₂)` the Pareto problem has the unique
solution `h° = 1`, `T° = 1 - w₂`. -/
theorem exercise_11_B_2c_counterexample (w₁ w₂ : ℝ) :
    (∀ p w : ℝ, 0 < p → ∀ h, (w - p * h) * h ≤ (w - p * (w / (2 * p))) * (w / (2 * p))) ∧
      (0 ≤ (1 : ℝ) ∧ 1 ≤ (w₂ + (1 - w₂)) * 1 ∧ ∀ h T : ℝ, 0 ≤ h → 1 ≤ (w₂ + T) * h →
        -h ^ 2 / 2 + w₁ - T ≤ -(1 : ℝ) ^ 2 / 2 + w₁ - (1 - w₂) ∧
        (-h ^ 2 / 2 + w₁ - T = -(1 : ℝ) ^ 2 / 2 + w₁ - (1 - w₂) → h = 1 ∧ T = 1 - w₂)) := by
  refine ⟨fun p w hp h => ?_, by norm_num, by norm_num, fun h T h0 hc => ?_⟩
  · have : (w - p * (w / (2 * p))) * (w / (2 * p)) - (w - p * h) * h =
        p * (h - w / (2 * p)) ^ 2 := by field_simp; ring
    nlinarith [sq_nonneg (h - w / (2 * p))]
  · have hpos : 0 < h := by
      rcases eq_or_lt_of_le h0 with he | hp
      · rw [← he] at hc; linarith
      · exact hp
    have hT : 1 / h - w₂ ≤ T := by
      have : 1 / h ≤ w₂ + T := by rw [div_le_iff₀ hpos]; linarith
      linarith
    have key : 3 / 2 ≤ h ^ 2 / 2 + 1 / h := by
      rw [show h ^ 2 / 2 + 1 / h = (h ^ 3 + 2) / (2 * h) by field_simp,
        le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (h - 1), mul_nonneg (sq_nonneg (h - 1)) h0]
    refine ⟨by linarith, fun heq => ?_⟩
    have hh : h ^ 2 / 2 + 1 / h = 3 / 2 := by linarith
    have h1 : h = 1 := by
      have : (h - 1) ^ 2 * (h + 2) = 0 := by
        field_simp at hh
        nlinarith
      rcases mul_eq_zero.1 this with h2 | h2
      · nlinarith [sq_nonneg (h - 1)]
      · linarith
    subst h1
    exact ⟨rfl, by norm_num at hT heq; linarith⟩

/-- **Exercise 11.B.2(c), corrected comparative statics.** Hold consumer 1's utility fixed, so the
increase in `w₂` goes to consumer 2: the optimum `(h°(w₂), z°(w₂))` (`z` consumer 2's wealth) solves
`φ₂ₕ + φ₁'(h) φ₂_w = 0` and `z = φ₁(h) + w₂ + K`. With second partials as in (b) at
`(h°, z°)`, `p̄ = -φ₁'(h°)` and `φ₁''(h°) = e₁`:
`h°'(a₁₁ - 2p̄ a₁₂ + p̄² a₂₂ + e₁ φ₂_w) + (a₁₂ - p̄ a₂₂) = 0`. -/
theorem exercise_11_B_2c_corrected (F₁ F₂ : ℝ × ℝ → ℝ) (φ₁ d₁ hc zc : ℝ → ℝ)
    (w₀ h' z' e₁ a₁₁ a₁₂ a₂₂ K : ℝ)
    (hF₁ : HasFDerivAt F₁ (a₁₁ • ContinuousLinearMap.fst ℝ ℝ ℝ +
      a₁₂ • ContinuousLinearMap.snd ℝ ℝ ℝ) (hc w₀, zc w₀))
    (hF₂ : HasFDerivAt F₂ (a₁₂ • ContinuousLinearMap.fst ℝ ℝ ℝ +
      a₂₂ • ContinuousLinearMap.snd ℝ ℝ ℝ) (hc w₀, zc w₀))
    (hφ₁ : ∀ x, HasDerivAt φ₁ (d₁ x) x) (hd₁ : HasDerivAt d₁ e₁ (hc w₀))
    (hh : HasDerivAt hc h' w₀) (hz : HasDerivAt zc z' w₀)
    (hfoc : ∀ w, F₁ (hc w, zc w) + d₁ (hc w) * F₂ (hc w, zc w) = 0)
    (hbud : ∀ w, zc w = φ₁ (hc w) + w + K) :
    h' * (a₁₁ - 2 * (-d₁ (hc w₀)) * a₁₂ + (-d₁ (hc w₀)) ^ 2 * a₂₂ + e₁ * F₂ (hc w₀, zc w₀)) +
      (a₁₂ - (-d₁ (hc w₀)) * a₂₂) = 0 := by
  have hpath : HasDerivAt (fun w => (hc w, zc w)) (h', z') w₀ := hh.prodMk hz
  have h1 := hF₁.comp_hasDerivAt w₀ hpath
  have h2 := hF₂.comp_hasDerivAt w₀ hpath
  have h3 := hd₁.comp w₀ hh
  have hg := h1.add (h3.mul h2)
  have hconst : HasDerivAt (fun w => F₁ (hc w, zc w) + d₁ (hc w) * F₂ (hc w, zc w)) 0 w₀ := by
    have : (fun w => F₁ (hc w, zc w) + d₁ (hc w) * F₂ (hc w, zc w)) = fun _ => 0 := funext hfoc
    rw [this]; exact hasDerivAt_const _ _
  have e := hg.unique hconst
  -- `z' = φ₁'(h) h' + 1` from the budget identity
  have hzb : HasDerivAt zc (d₁ (hc w₀) * h' + 1) w₀ := by
    have : zc = fun w => φ₁ (hc w) + w + K := funext hbud
    rw [this]
    have := (((hφ₁ (hc w₀)).comp w₀ hh).add (hasDerivAt_id w₀)).add_const K
    simpa using this
  have hz' : z' = d₁ (hc w₀) * h' + 1 := hz.unique hzb
  rw [hz'] at e
  simp at e
  linarith

/-- **Exercise 11.B.2(c), the sign comparison.** If `D = a₁₁ - 2p̄a₁₂ + p̄²a₂₂ < 0` (the
second-order
condition of consumer 2's demand problem) and `e₁ φ₂_w < 0` (`φ₁'' < 0`, `φ₂_w > 0`), the
corrected comparative static `h°'` and the wealth effect `∂h/∂w` of the demand at price `p̄` (at the
point where demand equals `h°`) have the same sign: the optimal `h°` rises with `w₂` iff the
externality is a normal good for consumer 2. -/
theorem exercise_11_B_2c_sign {D E N hc' hd' : ℝ} (hD : D < 0) (hE : E < 0)
    (hc : hc' * (D + E) + N = 0) (hd : hd' * D + N = 0) : (0 < hc' ↔ 0 < hd') := by
  have hDE : D + E < 0 := by linarith
  constructor
  · intro h
    have hN : 0 < N := by nlinarith [mul_neg_of_pos_of_neg h hDE]
    by_contra h'
    push Not at h'
    nlinarith [mul_nonneg_of_nonpos_of_nonpos h' hD.le]
  · intro h
    have hN : 0 < N := by nlinarith [mul_neg_of_pos_of_neg h hD]
    by_contra h'
    push Not at h'
    nlinarith [mul_nonneg_of_nonpos_of_nonpos h' hDE.le]

/-! ## Exercise 11.B.3 -/

namespace Bilateral

variable (M : Bilateral)

/-- **Exercise 11.B.3** (MWG, p. 379). Given the Pigouvian tax `t_h = -φ₂'(h°) > 0` (paid by
consumer 1 to the government), if the consumers then bargain efficiently they choose `h` to
maximize `φ₁(h) - t_h h + φ₂(h)`; when `h° > 0` this `h` is strictly below `h°`, so the outcome is
inefficient. -/
theorem exercise_11_B_3_tax {ho hb : ℝ} (hopt : M.IsOptLevel ho) (hpos : 0 < ho)
    (ht : 0 < -M.d₂ ho)
    (hbarg : 0 ≤ hb ∧ ∀ y, 0 ≤ y → M.φ₁ y - (-M.d₂ ho) * y + M.φ₂ y ≤
      M.φ₁ hb - (-M.d₂ ho) * hb + M.φ₂ hb) : hb < ho ∧ ¬ M.IsOptLevel hb := by
  set t := -M.d₂ ho
  have hf : ∀ x, HasDerivAt (fun y => M.φ₁ y - t * y + M.φ₂ y) (M.d₁ x + M.d₂ x - t) x :=
    fun x => by
      have h2 : HasDerivAt (fun y => t * y) t x := by simpa using (hasDerivAt_id x).const_mul t
      have := ((M.hd₁ x).sub h2).add (M.hd₂ x)
      convert this using 1; ring
  have hanti : StrictAntiOn (fun x => M.d₁ x + M.d₂ x - t) (Set.Ici 0) := fun a ha b hb' hab => by
    have := M.anti_joint ha hb' hab; simp only at this ⊢; linarith
  have hkt := (kt_max_iff hf hanti.antitoneOn hbarg.1).1 hbarg.2
  have ho' := (M.eq_11_B_2 ho).1 hopt
  have hlt : hb < ho := by
    by_contra hle
    push Not at hle
    rcases eq_or_lt_of_le hle with heq | hgt
    · have := hkt.2.2 (heq ▸ hpos); rw [← heq] at this; simp only at this
      linarith [ho'.2.2 hpos]
    · have e := hkt.2.2 (hpos.trans hgt)
      have := M.anti_joint hopt.1 hbarg.1 hgt
      simp only at e this
      linarith [ho'.2.2 hpos]
  refine ⟨hlt, fun hopt' => ?_⟩
  have := kt_max_unique M.hasDerivAt_joint M.anti_joint hopt.1 hopt.2 hopt'.1 hopt'.2
  linarith

/-- **Exercise 11.B.3**, quota: with the quota `h ≤ h°`, bargaining to maximize `φ₁ + φ₂` over
`[0, h°]` gives exactly `h°`, so the efficient level still results. -/
theorem exercise_11_B_3_quota {ho h : ℝ} (hopt : M.IsOptLevel ho)
    (hbarg : 0 ≤ h ∧ h ≤ ho ∧ ∀ y, 0 ≤ y → y ≤ ho → M.joint y ≤ M.joint h) : h = ho := by
  have hmax : ∀ y, 0 ≤ y → M.joint y ≤ M.joint h := fun y hy =>
    (hopt.2 y hy).trans (hbarg.2.2 ho hopt.1 le_rfl)
  exact kt_max_unique M.hasDerivAt_joint M.anti_joint hbarg.1 hmax hopt.1 hopt.2

end Bilateral

/-! ## Exercise 11.B.4 -/

/-- **Exercise 11.B.4** (MWG, p. 379). Consumer 2 chooses an action `e ∈ ℝ`; her derived utility is
`φ₂(h, e) + w₂`. Let `(h°, e°)` maximize `φ₁(h) + φ₂(h, e)` over `h ≥ 0`, `e ∈ ℝ`. With the tax
`t_h = -∂φ₂(h°, e°)/∂h` on `h` and no tax on `e`, `(h°, e°)` is an equilibrium: consumer 1's
optimal `h` is `h°` and consumer 2's optimal `e` given `h°` is `e°`. -/
theorem exercise_11_B_4 {φ₁ d₁ : ℝ → ℝ} (φ₂ : ℝ → ℝ → ℝ) (hφ₁ : ∀ x, HasDerivAt φ₁ (d₁ x) x)
    (hd₁ : AntitoneOn d₁ (Set.Ici 0)) {ho eo g : ℝ}
    (hg : HasDerivAt (fun h => φ₂ h eo) g ho)
    (hopt : 0 ≤ ho ∧ ∀ h e, 0 ≤ h → φ₁ h + φ₂ h e ≤ φ₁ ho + φ₂ ho eo) :
    (∀ y, 0 ≤ y → φ₁ y - (-g) * y ≤ φ₁ ho - (-g) * ho) ∧ ∀ e, φ₂ ho e ≤ φ₂ ho eo := by
  have hnec := foc_max_necessary ((hφ₁ ho).add hg).hasDerivWithinAt hopt.1
    (fun y hy => hopt.2 y eo hy)
  have hf : ∀ x, HasDerivAt (fun y => φ₁ y - (-g) * y) (d₁ x - (-g)) x := fun x => by
    have h2 : HasDerivAt (fun y => -g * y) (-g) x := by simpa using (hasDerivAt_id x).const_mul (-g)
    exact (hφ₁ x).sub h2
  have hanti : AntitoneOn (fun x => d₁ x - (-g)) (Set.Ici 0) := fun a ha b hb hab => by
    have := hd₁ ha hb hab; simp only; linarith
  refine ⟨(kt_max_iff hf hanti hopt.1).2 ⟨hopt.1, by linarith [hnec.1],
    fun hp => by linarith [hnec.2 hp]⟩, fun e => ?_⟩
  have := hopt.2 ho e hopt.1
  linarith

/-- **Exercise 11.B.4**: taxing or subsidizing `e` is harmful. If `φ₂(h°, ·)` is differentiable at
`e°` and `e` is taxed at a rate `t_e ≠ 0`, consumer 2 no longer chooses `e°` given `h°`. -/
theorem exercise_11_B_4_no_tax_e {φ₁ : ℝ → ℝ} (φ₂ : ℝ → ℝ → ℝ) {ho eo ge te : ℝ}
    (hge : HasDerivAt (fun e => φ₂ ho e) ge eo)
    (hopt : 0 ≤ ho ∧ ∀ h e, 0 ≤ h → φ₁ h + φ₂ h e ≤ φ₁ ho + φ₂ ho eo) (hte : te ≠ 0) :
    ¬ ∀ e, φ₂ ho e - te * e ≤ φ₂ ho eo - te * eo := by
  intro hmax
  have h0 : ge = 0 := by
    have hloc : IsLocalMax (fun e => φ₂ ho e) eo :=
      Filter.Eventually.of_forall fun e => by have := hopt.2 ho e hopt.1; linarith
    exact hloc.hasDerivAt_eq_zero hge
  have h1 : ge - te = 0 := by
    have hloc : IsLocalMax (fun e => φ₂ ho e - te * e) eo := Filter.Eventually.of_forall hmax
    have hd : HasDerivAt (fun e => φ₂ ho e - te * e) (ge - te) eo := by
      have h2 : HasDerivAt (fun e => te * e) te eo := by
        simpa using (hasDerivAt_id eo).const_mul te
      exact hge.sub h2
    exact hloc.hasDerivAt_eq_zero hd
  exact hte (by linarith)

/-! ## Exercise 11.B.5 -/

/-- The nonnegative quadrant `{(q, h) : q ≥ 0, h ≥ 0}`. -/
def quadrant : Set (ℝ × ℝ) := {x | 0 ≤ x.1 ∧ 0 ≤ x.2}

theorem convex_quadrant : Convex ℝ quadrant := by
  intro x hx y hy a b ha hb _
  exact ⟨by simpa using add_nonneg (mul_nonneg ha hx.1) (mul_nonneg hb hy.1),
    by simpa using add_nonneg (mul_nonneg ha hx.2) (mul_nonneg hb hy.2)⟩

/-- The derivative of a function of `(q, h)` along the `q`-line and the `h`-line. -/
theorem lines_deriv {c : ℝ × ℝ → ℝ} {a b q₀ h₀ : ℝ}
    (hc : HasFDerivAt c (a • ContinuousLinearMap.fst ℝ ℝ ℝ + b • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (q₀, h₀)) :
    HasDerivAt (fun q => c (q, h₀)) a q₀ ∧ HasDerivAt (fun h => c (q₀, h)) b h₀ := by
  constructor
  · have h1 : HasDerivAt (fun q : ℝ => (q, h₀)) ((1 : ℝ), (0 : ℝ)) q₀ :=
      (hasDerivAt_id q₀).prodMk (hasDerivAt_const q₀ h₀)
    have := hc.comp_hasDerivAt q₀ h1
    have e : (a • ContinuousLinearMap.fst ℝ ℝ ℝ + b • ContinuousLinearMap.snd ℝ ℝ ℝ)
        ((1 : ℝ), (0 : ℝ)) = a := by simp
    rw [e] at this
    exact this
  · have h1 : HasDerivAt (fun h : ℝ => (q₀, h)) ((0 : ℝ), (1 : ℝ)) h₀ :=
      (hasDerivAt_const h₀ q₀).prodMk (hasDerivAt_id h₀)
    have := hc.comp_hasDerivAt h₀ h1
    have e : (a • ContinuousLinearMap.fst ℝ ℝ ℝ + b • ContinuousLinearMap.snd ℝ ℝ ℝ)
        ((0 : ℝ), (1 : ℝ)) = b := by simp
    rw [e] at this
    exact this

/-- **Exercise 11.B.5(a)-(c)** (MWG, p. 379), the firm's problem with an output tax `τ` and a tax
`t` per unit of `h`: `(q, h)` maximizes `(p - τ)q - c(q, h) - t h` on `ℝ₊²` iff
`p - τ ≤ c_q` (equality if `q > 0`) and `-c_h ≤ t` (equality if `h > 0`). With `τ = t = 0` this is
part (a). -/
theorem exercise_11_B_5_firm {c : ℝ × ℝ → ℝ} {cq ch : ℝ × ℝ → ℝ}
    (hc : ∀ x, HasFDerivAt c (cq x • ContinuousLinearMap.fst ℝ ℝ ℝ +
      ch x • ContinuousLinearMap.snd ℝ ℝ ℝ) x) (hconv : ConvexOn ℝ quadrant c)
    (p τ t : ℝ) {x : ℝ × ℝ} (hx : x ∈ quadrant) :
    (∀ y ∈ quadrant, (p - τ) * y.1 - c y - t * y.2 ≤ (p - τ) * x.1 - c x - t * x.2) ↔
      (p - τ ≤ cq x ∧ (0 < x.1 → p - τ = cq x)) ∧ (-ch x ≤ t ∧ (0 < x.2 → -ch x = t)) := by
  obtain ⟨q₀, h₀⟩ := x
  obtain ⟨lq, lh⟩ := lines_deriv (hc (q₀, h₀))
  constructor
  · intro hmax
    have d1 : HasDerivAt (fun q => (p - τ) * q - c (q, h₀) - t * h₀) (p - τ - cq (q₀, h₀)) q₀ := by
      have h2 : HasDerivAt (fun q => (p - τ) * q) (p - τ) q₀ := by
        simpa using (hasDerivAt_id q₀).const_mul (p - τ)
      exact (h2.sub lq).sub_const _
    have d2 : HasDerivAt (fun h => (p - τ) * q₀ - c (q₀, h) - t * h) (0 - ch (q₀, h₀) - t) h₀ := by
      have h2 : HasDerivAt (fun h => t * h) t h₀ := by simpa using (hasDerivAt_id h₀).const_mul t
      exact ((hasDerivAt_const h₀ ((p - τ) * q₀)).sub lh).sub h2
    have n1 := foc_max_necessary d1.hasDerivWithinAt hx.1
      (fun y hy => by simpa using hmax (y, h₀) ⟨hy, hx.2⟩)
    have n2 := foc_max_necessary d2.hasDerivWithinAt hx.2
      (fun y hy => by simpa using hmax (q₀, y) ⟨hx.1, hy⟩)
    simp only [zero_sub] at n1 n2
    exact ⟨⟨by linarith [n1.1], fun hp => by linarith [n1.2 hp]⟩,
      ⟨by linarith [n2.1], fun hp => by linarith [n2.2 hp]⟩⟩
  · rintro ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ ⟨q, h⟩ hy
    have ht := convex_tangent hconv hx hy (hc (q₀, h₀))
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', Prod.fst_sub, Prod.snd_sub,
      smul_eq_mul] at ht
    have t1 : (p - τ - cq (q₀, h₀)) * (q - q₀) ≤ 0 := by
      rcases eq_or_lt_of_le hx.1 with h0 | hp
      · simp only at h0
        exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith [hy.1])
      · rw [show p - τ - cq (q₀, h₀) = 0 by linarith [a2 hp], zero_mul]
    have t2 : (-ch (q₀, h₀) - t) * (h - h₀) ≤ 0 := by
      rcases eq_or_lt_of_le hx.2 with h0 | hp
      · simp only at h0
        exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith [hy.2])
      · rw [show -ch (q₀, h₀) - t = 0 by linarith [b2 hp], zero_mul]
    simp only
    nlinarith

/-- **Exercise 11.B.5(b)** (MWG, p. 379), the Pareto problem `max pq - c(q, h) + φ(h)` on `ℝ₊²`:
optimal iff `p ≤ c_q` (equality if `q > 0`) and `φ'(h) ≤ c_h` (equality if `h > 0`). -/
theorem exercise_11_B_5b {c : ℝ × ℝ → ℝ} {cq ch : ℝ × ℝ → ℝ} {φ dφ : ℝ → ℝ}
    (hc : ∀ x, HasFDerivAt c (cq x • ContinuousLinearMap.fst ℝ ℝ ℝ +
      ch x • ContinuousLinearMap.snd ℝ ℝ ℝ) x) (hconv : ConvexOn ℝ quadrant c)
    (hφ : ∀ x, HasDerivAt φ (dφ x) x) (hdφ : AntitoneOn dφ (Set.Ici 0)) (p : ℝ) {x : ℝ × ℝ}
    (hx : x ∈ quadrant) :
    (∀ y ∈ quadrant, p * y.1 - c y + φ y.2 ≤ p * x.1 - c x + φ x.2) ↔
      (p ≤ cq x ∧ (0 < x.1 → p = cq x)) ∧ (dφ x.2 ≤ ch x ∧ (0 < x.2 → dφ x.2 = ch x)) := by
  obtain ⟨q₀, h₀⟩ := x
  obtain ⟨lq, lh⟩ := lines_deriv (hc (q₀, h₀))
  constructor
  · intro hmax
    have d1 : HasDerivAt (fun q => p * q - c (q, h₀) + φ h₀) (p - cq (q₀, h₀)) q₀ := by
      have h2 : HasDerivAt (fun q => p * q) p q₀ := by simpa using (hasDerivAt_id q₀).const_mul p
      exact (h2.sub lq).add_const _
    have d2 : HasDerivAt (fun h => p * q₀ - c (q₀, h) + φ h) (0 - ch (q₀, h₀) + dφ h₀) h₀ :=
      ((hasDerivAt_const h₀ (p * q₀)).sub lh).add (hφ h₀)
    have n1 := foc_max_necessary d1.hasDerivWithinAt hx.1
      (fun y hy => by simpa using hmax (y, h₀) ⟨hy, hx.2⟩)
    have n2 := foc_max_necessary d2.hasDerivWithinAt hx.2
      (fun y hy => by simpa using hmax (q₀, y) ⟨hx.1, hy⟩)
    simp only [zero_sub] at n1 n2
    exact ⟨⟨by linarith [n1.1], fun hp => by linarith [n1.2 hp]⟩,
      ⟨by linarith [n2.1], fun hp => by linarith [n2.2 hp]⟩⟩
  · rintro ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ ⟨q, h⟩ hy
    have ht := convex_tangent hconv hx hy (hc (q₀, h₀))
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', Prod.fst_sub, Prod.snd_sub,
      smul_eq_mul] at ht
    have hφt := foc_tangent_le (fun z _ => (hφ z).hasDerivWithinAt) hdφ hx.2 hy.2
    have t1 : (p - cq (q₀, h₀)) * (q - q₀) ≤ 0 := by
      rcases eq_or_lt_of_le hx.1 with h0 | hp
      · simp only at h0
        exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith [hy.1])
      · rw [show p - cq (q₀, h₀) = 0 by linarith [a2 hp], zero_mul]
    have t2 : (dφ h₀ - ch (q₀, h₀)) * (h - h₀) ≤ 0 := by
      rcases eq_or_lt_of_le hx.2 with h0 | hp
      · simp only at h0
        exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith [hy.2])
      · rw [show dφ h₀ - ch (q₀, h₀) = 0 by linarith [b2 hp], zero_mul]
    simp only at hφt ⊢
    nlinarith

/-- **Exercise 11.B.5(c)** (MWG, p. 379). An output tax cannot restore efficiency: if the Pareto
optimum has `h° > 0` and `φ'(h°) < 0`, then for no output tax `τ` is `(q°, h°)` the firm's choice.
A direct tax `t = -φ'(h°)` on the externality makes `(q°, h°)` the firm's choice. -/
theorem exercise_11_B_5c {c : ℝ × ℝ → ℝ} {cq ch : ℝ × ℝ → ℝ} {φ dφ : ℝ → ℝ}
    (hc : ∀ x, HasFDerivAt c (cq x • ContinuousLinearMap.fst ℝ ℝ ℝ +
      ch x • ContinuousLinearMap.snd ℝ ℝ ℝ) x) (hconv : ConvexOn ℝ quadrant c)
    (hφ : ∀ x, HasDerivAt φ (dφ x) x) (hdφ : AntitoneOn dφ (Set.Ici 0)) (p : ℝ) {x : ℝ × ℝ}
    (hx : x ∈ quadrant)
    (hopt : ∀ y ∈ quadrant, p * y.1 - c y + φ y.2 ≤ p * x.1 - c x + φ x.2) :
    (0 < x.2 → dφ x.2 < 0 → ∀ τ,
      ¬ ∀ y ∈ quadrant, (p - τ) * y.1 - c y - 0 * y.2 ≤ (p - τ) * x.1 - c x - 0 * x.2) ∧
      ∀ y ∈ quadrant, (p - 0) * y.1 - c y - (-dφ x.2) * y.2 ≤
        (p - 0) * x.1 - c x - (-dφ x.2) * x.2 := by
  have hb := (exercise_11_B_5b hc hconv hφ hdφ p hx).1 hopt
  refine ⟨fun hpos hneg τ hmax => ?_, ?_⟩
  · have hf := (exercise_11_B_5_firm hc hconv p τ 0 hx).1 hmax
    have := hb.2.2 hpos
    linarith [hf.2.1]
  · refine (exercise_11_B_5_firm hc hconv p 0 _ hx).2 ⟨⟨by linarith [hb.1.1],
      fun hp => by linarith [hb.1.2 hp]⟩, ⟨by linarith [hb.2.1], fun hp => by linarith [hb.2.2 hp]⟩⟩

/-- **Exercise 11.B.5(d)** (MWG, p. 379). With fixed proportions `h = αq` (`α > 0`), the firm's cost
is `C(q) = c(q, αq)` (convex, derivative `C'`). If `q°` maximizes `pq - C(q) + φ(αq)` on `ℝ₊`, the
output tax `τ = -α φ'(αq°)` makes `q°` the firm's choice: `max (p - τ)q - C(q)`. -/
theorem exercise_11_B_5d {C dC φ dφ : ℝ → ℝ} {α : ℝ} (hα : 0 < α)
    (hC : ∀ x, HasDerivAt C (dC x) x) (hCm : MonotoneOn dC (Set.Ici 0))
    (hφ : ∀ x, HasDerivAt φ (dφ x) x) (hdφ : AntitoneOn dφ (Set.Ici 0)) (p : ℝ) {qo : ℝ}
    (hopt : 0 ≤ qo ∧ ∀ q, 0 ≤ q → p * q - C q + φ (α * q) ≤ p * qo - C qo + φ (α * qo)) :
    ∀ q, 0 ≤ q → (p - -(α * dφ (α * qo))) * q - C q ≤ (p - -(α * dφ (α * qo))) * qo - C qo := by
  have hP : ∀ x, HasDerivAt (fun q => p * q - C q + φ (α * q)) (p - dC x + α * dφ (α * x)) x :=
    fun x => by
      have h1 : HasDerivAt (fun q => φ (α * q)) (dφ (α * x) * α) x :=
        (hφ (α * x)).comp x (by simpa using (hasDerivAt_id x).const_mul α)
      have h2 : HasDerivAt (fun q => p * q) p x := by simpa using (hasDerivAt_id x).const_mul p
      have := (h2.sub (hC x)).add h1
      convert this using 1; ring
  have hPa : AntitoneOn (fun x => p - dC x + α * dφ (α * x)) (Set.Ici 0) := by
    intro a ha b hb hab
    have h1 := hCm ha hb hab
    have h2 := hdφ (show 0 ≤ α * a from mul_nonneg hα.le ha) (show 0 ≤ α * b from
      mul_nonneg hα.le hb) (mul_le_mul_of_nonneg_left hab hα.le)
    simp only
    nlinarith
  have hkt := (kt_max_iff hP hPa hopt.1).1 hopt.2
  set τ := -(α * dφ (α * qo))
  have hF : ∀ x, HasDerivAt (fun q => (p - τ) * q - C q) (p - τ - dC x) x := fun x => by
    have h2 : HasDerivAt (fun q => (p - τ) * q) (p - τ) x := by
      simpa using (hasDerivAt_id x).const_mul (p - τ)
    exact h2.sub (hC x)
  have hFa : AntitoneOn (fun x => p - τ - dC x) (Set.Ici 0) := fun a ha b hb hab => by
    have := hCm ha hb hab; simp only; linarith
  refine (kt_max_iff hF hFa hopt.1).2 ⟨hopt.1, ?_, fun hp => ?_⟩
  · have := hkt.2.1; simp only [τ] at this ⊢; linarith
  · have := hkt.2.2 hp; simp only [τ] at this ⊢; linarith

/-- An instance of Exercise 11.B.5: `c(q, h) = q²/2 + (h - q)²/2`, `φ(h) = -h`, `p = 4`. The Pareto
optimum is `(q°, h°) = (3, 2)`; the unregulated firm chooses `(4, 4)`. -/
theorem exercise_11_B_5_instance :
    ConvexOn ℝ quadrant (fun x : ℝ × ℝ => x.1 ^ 2 / 2 + (x.2 - x.1) ^ 2 / 2) ∧
      (∀ y ∈ quadrant, 4 * y.1 - (y.1 ^ 2 / 2 + (y.2 - y.1) ^ 2 / 2) + -y.2 ≤
        4 * 3 - ((3 : ℝ) ^ 2 / 2 + (2 - 3) ^ 2 / 2) + -2) ∧
      (∀ y ∈ quadrant, 4 * y.1 - (y.1 ^ 2 / 2 + (y.2 - y.1) ^ 2 / 2) ≤
        4 * 4 - ((4 : ℝ) ^ 2 / 2 + (4 - 4) ^ 2 / 2)) := by
  refine ⟨⟨convex_quadrant, fun x _ y _ a b ha hb hab => ?_⟩, fun y _ => ?_, fun y _ => ?_⟩
  · simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, smul_eq_mul]
    have hb' : b = 1 - a := by linarith
    subst hb'
    nlinarith [mul_nonneg ha hb, sq_nonneg (x.1 - y.1), sq_nonneg (x.2 - x.1 - (y.2 - y.1)),
      mul_nonneg (mul_nonneg ha hb) (sq_nonneg (x.1 - y.1)),
      mul_nonneg (mul_nonneg ha hb) (sq_nonneg (x.2 - x.1 - (y.2 - y.1)))]
  · nlinarith [sq_nonneg (y.1 - 3), sq_nonneg (y.2 - y.1 + 1)]
  · nlinarith [sq_nonneg (y.1 - 4), sq_nonneg (y.2 - y.1)]

end MWG.ExternalitiesPublicGoods
