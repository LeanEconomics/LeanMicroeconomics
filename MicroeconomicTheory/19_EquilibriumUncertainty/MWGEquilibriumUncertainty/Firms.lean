/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGEquilibriumUncertainty.Incomplete

/-!
# Firm behavior under uncertainty (MWG Section 19.G, pp. 713-716, Exercises 19.G.1-19.G.4)

A firm chooses a return vector `a ∈ A ⊆ ℝ^S` (in units of the numeraire good `g`); consumer `i`
owns the share `θᵢ ≥ 0`.

* **Definition 19.G.1**: `A` is spanned by `R` (`IsSpanned`). The market value of a spanned plan
  `a = Rα` is `v(a, q) = q·α`; with arbitrage prices it does not depend on the representation
  (`marketValue_wellDefined`).
* **(19.G.1)** and **Exercise 19.G.1**: if the firm is introduced as a new asset priced at its
  arbitrage value, every consumption plan affordable with trade in its shares is affordable
  without purchasing shares, and the budget set is (19.G.1) (`exercise_19_G_1`).
* **Unanimity (p. 715)**: if `v(a, q) ≥ v(a', q)` then `B_{a'i} ⊆ B_{ai}` for every owner, so all
  owners prefer the plan of higher market value (`unanimity`).
* **Exercise 19.G.2**: the printed request (an example where one consumer becomes significantly
  worse off) cannot be met: with `L = 1`, a single initial asset, strongly monotone utilities and
  `εa ≥ 0`, at any Radner equilibrium after the firm is introduced every consumer is at least as
  well off as at any equilibrium before (`exercise_19_G_2_no_one_worse_off`, correction 9).
* **Exercise 19.G.3**: with a spanned firm, trading its shares at `t = 0` or adding `θᵢ a` to the
  endowments gives the same budget sets (`exercise_19_G_3`).
* **Exercise 19.G.4**: without spanning, owners need not be unanimous (`exercise_19_G_4`).
-/

namespace MWG.EquilibriumUncertainty

open Matrix

variable {S L K : ℕ}

/-- **Definition 19.G.1** (MWG, p. 714). A set `A ⊆ ℝ^S` is spanned by the asset structure `R` if
every `a ∈ A` is in the range of `R`. -/
def IsSpanned (R : Matrix (Fin S) (Fin K) ℝ) (A : Set (Fin S → ℝ)) : Prop :=
  ∀ a ∈ A, ∃ α, R *ᵥ α = a

/-- **p. 714**. With arbitrage prices `q = μ·R`, the market value `v(a, q) = ∑_k α_k q_k` of a
spanned plan `a = Rα` does not depend on the representation: it is `μ·a`. -/
theorem marketValue_wellDefined {R : Matrix (Fin S) (Fin K) ℝ} {μ : Fin S → ℝ}
    {q : Fin K → ℝ} (hq : ∀ k, q k = ∑ s, μ s * R s k) {a : Fin S → ℝ} {α : Fin K → ℝ}
    (hα : R *ᵥ α = a) : q ⬝ᵥ α = μ ⬝ᵥ a := by
  rw [dot_eq_of_pricing hq, hα]

/-- **(19.G.1)** (MWG, p. 715). The budget set of consumer `i` with share `θᵢ` when the firm
chooses `a` of market value `v = v(a, q)`: some portfolio `z` has `q·z ≤ θᵢ v` and
`p_s·(x_s - ω_s) ≤ p_{gs} ∑_k r_{sk} z_k` in every state. -/
def firmBudget (g : Fin L) (R : Matrix (Fin S) (Fin K) ℝ) (q : Fin K → ℝ) (p ω : CVec S L)
    (θ v : ℝ) : Set (CVec S L) :=
  {x | NonnegC x ∧ ∃ z : Fin K → ℝ, q ⬝ᵥ z ≤ θ * v ∧
    ∀ s, p s ⬝ᵥ x s ≤ p s ⬝ᵥ ω s + p s g * (R *ᵥ z) s}

/-- **p. 715**. Unanimity: if `v(a, q) ≥ v(a', q)`, every owner (`θᵢ ≥ 0`) has
`B_{a'i} ⊆ B_{ai}`. -/
theorem unanimity (g : Fin L) (R : Matrix (Fin S) (Fin K) ℝ) (q : Fin K → ℝ) (p ω : CVec S L)
    {θ v v' : ℝ} (hθ : 0 ≤ θ) (hv : v' ≤ v) :
    firmBudget g R q p ω θ v' ⊆ firmBudget g R q p ω θ v := by
  rintro x ⟨hx, z, hq, hs⟩
  exact ⟨hx, z, hq.trans (mul_le_mul_of_nonneg_left hv hθ), hs⟩

/-- **p. 715**. Hence every owner prefers the plan with the higher market value: the maximal
attainable utility over `B_{ai}` is at least that over `B_{a'i}`. -/
theorem unanimity_utility (g : Fin L) (R : Matrix (Fin S) (Fin K) ℝ) (q : Fin K → ℝ)
    (p ω : CVec S L) {θ v v' : ℝ} (hθ : 0 ≤ θ) (hv : v' ≤ v) (U : CVec S L → ℝ)
    {x : CVec S L} (hmax : ∀ y ∈ firmBudget g R q p ω θ v, U y ≤ U x) :
    ∀ y ∈ firmBudget g R q p ω θ v', U y ≤ U x :=
  fun y hy => hmax y (unanimity g R q p ω hθ hv hy)

/-- The asset structure with the firm added as asset `K + 1` (return vector `a`). -/
def withFirm (R : Matrix (Fin S) (Fin K) ℝ) (a : Fin S → ℝ) : Matrix (Fin S) (Fin (K + 1)) ℝ :=
  appendAsset R a

/-- **Exercise 19.G.1** (MWG, p. 729). Suppose `a = Rα` is spanned and the firm is added as a new
asset priced at its arbitrage value `v = q·α`, consumer `i` holding `θᵢ` shares initially. The plans
affordable when shares can be traded (holding `y` shares at cost `v(y - θᵢ)`) are exactly the
plans of (19.G.1), which can be reached holding no shares of the firm (`y = 0`), i.e. without
purchasing any. -/
theorem exercise_19_G_1 (g : Fin L) {R : Matrix (Fin S) (Fin K) ℝ} {q : Fin K → ℝ}
    {p ω : CVec S L} {θ : ℝ} {a : Fin S → ℝ} {α : Fin K → ℝ} (hα : R *ᵥ α = a) (x : CVec S L) :
    (NonnegC x ∧ ∃ (z : Fin K → ℝ) (y : ℝ), q ⬝ᵥ z + (q ⬝ᵥ α) * (y - θ) ≤ 0 ∧
      ∀ s, p s ⬝ᵥ x s ≤ p s ⬝ᵥ ω s + p s g * ((R *ᵥ z) s + y * a s)) ↔
      x ∈ firmBudget g R q p ω θ (q ⬝ᵥ α) := by
  constructor
  · rintro ⟨hx, z, y, hq, hs⟩
    refine ⟨hx, z + y • α, ?_, fun s => ?_⟩
    · rw [dotProduct_add, dotProduct_smul, smul_eq_mul]; linarith
    · rw [mulVec_add, mulVec_smul, hα, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; exact hs s
  · rintro ⟨hx, z, hq, hs⟩
    exact ⟨hx, z, 0, by linarith, fun s => by simpa using hs s⟩

/-- **Exercise 19.G.3** (MWG, p. 729). With a spanned plan `a = Rα`, the budget set when the shares
are traded at `t = 0` (19.G.1, value `v = q·α`) equals the budget set when they are not traded and
`θᵢ a` (in good `g`) is added to consumer `i`'s endowment. -/
theorem exercise_19_G_3 (g : Fin L) {R : Matrix (Fin S) (Fin K) ℝ} {q : Fin K → ℝ}
    {p ω : CVec S L} {θ : ℝ} {a : Fin S → ℝ} {α : Fin K → ℝ} (hα : R *ᵥ α = a) (x : CVec S L) :
    x ∈ firmBudget g R q p ω θ (q ⬝ᵥ α) ↔
      (NonnegC x ∧ ∃ z : Fin K → ℝ, q ⬝ᵥ z ≤ 0 ∧
        ∀ s, p s ⬝ᵥ x s ≤ p s ⬝ᵥ ω s + p s g * (θ * a s) + p s g * (R *ᵥ z) s) := by
  constructor
  · rintro ⟨hx, z, hq, hs⟩
    refine ⟨hx, z - θ • α, ?_, fun s => ?_⟩
    · rw [dotProduct_sub, dotProduct_smul, smul_eq_mul]; linarith
    · rw [mulVec_sub, mulVec_smul, hα, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      have := hs s; nlinarith
  · rintro ⟨hx, z, hq, hs⟩
    refine ⟨hx, z + θ • α, ?_, fun s => ?_⟩
    · rw [dotProduct_add, dotProduct_smul, smul_eq_mul]; linarith
    · rw [mulVec_add, mulVec_smul, hα, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have := hs s; nlinarith

/-- A Radner budget with initial asset holdings `e`: `q·(z - e) ≤ 0` and
`p_s·x_s ≤ p_s·ω_s + p_{gs}(Rz)_s` (used when the firm's shares are an endowment). -/
def radnerFeasibleE (g : Fin L) (R : Matrix (Fin S) (Fin K) ℝ) (q : Fin K → ℝ) (p ω : CVec S L)
    (e : Fin K → ℝ) (x : CVec S L) (z : Fin K → ℝ) : Prop :=
  NonnegC x ∧ q ⬝ᵥ (z - e) ≤ 0 ∧ ∀ s, p s ⬝ᵥ x s ≤ p s ⬝ᵥ ω s + p s g * (R *ᵥ z) s

/-- **Exercise 19.G.2** (MWG, p. 729), correction 9. With `L = 1` and a single asset `r ≥ 0`,
`r ≠ 0`, consider consumer `i` with a strongly monotone utility. (1) At any Radner equilibrium
before the firm is introduced, `Uᵢ(x_old) ≤ Uᵢ(ωᵢ)`. (2) After the firm (returns `εa ≥ 0`, share
`θᵢ ≥ 0`) is introduced as a tradeable asset, any utility-maximizing plan in the new budget gives
`Uᵢ(x_new) ≥ Uᵢ(ωᵢ)`: the consumer can keep his shares and not trade. So no consumer is made
worse off, however `a` and `ε` are chosen, and the requested example does not exist. -/
theorem exercise_19_G_2_no_one_worse_off {ι : Type*} [Fintype ι] {r : Fin S → ℝ}
    (hr : NonnegNonzeroReturns (returnMatrix ![r])) {U : ι → CVec S 1 → ℝ}
    {ω x : ι → CVec S 1} {q : Fin 1 → ℝ} {z : ι → Fin 1 → ℝ}
    (hold : IsRadnerEqm 0 (returnMatrix ![r]) U ω q (fun _ _ => 1) x z) (i : ι)
    (hU : StronglyMonotoneC (U i)) (hω : NonnegC (ω i))
    {a : Fin S → ℝ} {ε θ : ℝ} (hεa : ∀ s, 0 ≤ ε * a s) (hθ : 0 ≤ θ) {q' : Fin 2 → ℝ}
    {xnew : CVec S 1}
    (hnew : ∀ x' z', radnerFeasibleE 0 (withFirm (returnMatrix ![r]) (fun s => ε * a s)) q'
      (fun _ _ => 1) (ω i) (Pi.single (Fin.last 1) θ) x' z' → U i x' ≤ U i xnew) :
    U i (x i) ≤ U i (ω i) ∧ U i (ω i) ≤ U i xnew := by
  classical
  have hmono : ∀ y y' : CVec S 1, NonnegC y → y ≤ y' → U i y ≤ U i y' := fun y y' hy hle => by
    by_cases h : y = y'
    · rw [h]
    · exact (hU y y' hy hle h).le
  refine ⟨?_, ?_⟩
  · -- before: `q > 0`, so the budget forces `z ≤ 0` and `x ≤ ω`
    have hq := (radner_arbitrageFree 0 hold i hU).pos hr 0
    obtain ⟨⟨hx, hqz, hsp⟩, -⟩ := hold.1 i
    have hz : z i 0 ≤ 0 := by
      simp only [dotProduct, Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton]
        at hqz
      by_contra h; push Not at h; nlinarith
    refine hmono _ _ hx fun s l => ?_
    rw [Subsingleton.elim l 0]
    have := hsp s
    simp [dotProduct, returnMatrix, mulVec] at this
    nlinarith [hr.1 s 0, (show 0 ≤ r s by simpa [returnMatrix] using hr.1 s 0)]
  · -- after: keeping the shares (`z = θ e_firm`) is affordable
    refine (hmono _ _ hω (fun s l => ?_)).trans (hnew (fun s l => ω i s l + θ * (ε * a s))
      (Pi.single (Fin.last 1) θ) ⟨fun s l => ?_, by simp, fun s => ?_⟩)
    · simp only; nlinarith [hεa s]
    · nlinarith [hω s l, hεa s]
    · have hR : (withFirm (returnMatrix ![r]) (fun s => ε * a s) *ᵥ
          Pi.single (Fin.last 1) θ) s = θ * (ε * a s) := by
        simp only [withFirm, appendAsset, mulVec, dotProduct, Matrix.of_apply,
          Fin.sum_univ_castSucc, Fin.lastCases_castSucc, Fin.lastCases_last, Pi.single_eq_same,
          Finset.univ_unique, Finset.sum_singleton]
        rw [Pi.single_eq_of_ne (Fin.castSucc_lt_last _).ne]
        ring
      rw [hR]
      simp [dotProduct]

/-- **Exercise 19.G.4** (MWG, p. 729). Two consumers, `L = 1`, no assets, a firm with possible plans
`a¹ = (1, 0)` and `a² = (0, 1)`, shares `1/2` each (not traded), added to the endowments `(1, 1)`.
With risk-neutral expected utilities and probabilities `(9/10, 1/10)` for consumer 1 and
`(1/10, 9/10)` for consumer 2, consumer 1 strictly prefers `a¹` and consumer 2 strictly prefers
`a²`: the owners are not unanimous. -/
theorem exercise_19_G_4 :
    let U₁ : (Fin 2 → ℝ) → ℝ := fun c => 9 / 10 * c 0 + 1 / 10 * c 1
    let U₂ : (Fin 2 → ℝ) → ℝ := fun c => 1 / 10 * c 0 + 9 / 10 * c 1
    let endow : (Fin 2 → ℝ) → (Fin 2 → ℝ) := fun a s => 1 + 1 / 2 * a s
    U₁ (endow ![0, 1]) < U₁ (endow ![1, 0]) ∧ U₂ (endow ![1, 0]) < U₂ (endow ![0, 1]) := by
  intro U₁ U₂ endow
  simp only [U₁, U₂, endow]
  norm_num

end MWG.EquilibriumUncertainty
