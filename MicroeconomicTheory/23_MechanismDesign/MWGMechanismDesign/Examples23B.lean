/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGMechanismDesign.NashImplementation

/-!
# Examples 23.B.1-23.B.4 and Exercise 23.B.1

MWG, Section 23.B, pp. 860-864, and Exercise 23.B.1 (p. 918).

* **Example 23.B.1** (p. 860): `X = {x, y, z}` (`0, 1, 2`), agent 1 has the single type `θ̄₁`
  (`Unit`) and ranks `x ≻ y ≻ z`; agent 2 has types `θ₂'` (`true`: `z ≻ y ≻ x`) and `θ₂''`
  (`false`: `y ≻ x ≻ z`). The social choice function `f(θ̄₁, θ₂') = y`, `f(θ̄₁, θ₂'') = x` is
  ex post efficient (`example_23_B_1_efficient`), but agent 2 of type `θ₂''` gains by claiming
  `θ₂'` (`example_23_B_1`). Since agent 1 has a single type, strategy-proofness is exactly
  agent 2's willingness to reveal his type (`b1_strategyProof_iff`).
* **Exercise 23.B.1** (a)-(e): agent 2 reveals truthfully for (a)-(d), not for (e).
* **Example 23.B.2** (pp. 860-861, Figure 23.B.1): made concrete in `WalrasManipulation`.
* **Example 23.B.3** (pp. 861-862), the public project with cost `c` and feasible set
  `X = {(k, t) : k ∈ {0, 1}, ∑ᵢ tᵢ ≤ -ck}`: a social choice function is ex post efficient iff at
  every `θ` the project is built when `∑ᵢ θᵢ > c`, not built when `∑ᵢ θᵢ < c`, and
  `∑ᵢ tᵢ(θ) = -ck(θ)` (`example_23_B_3_efficient_iff`); so (23.B.1)-(23.B.2) are sufficient
  (`example_23_B_3_efficient`), as MWG state ("is ex post efficient if"); at `∑ᵢ θᵢ = c` either
  project level is efficient. With the egalitarian contribution rule, `Θᵢ = {θ̄ᵢ}` (`i ≠ 1`),
  `Θ₁ = [0, ∞)` and `c > ∑_{i≠1} θ̄ᵢ > c(I - 1)/I`, agent 1's type is critical, the others gain
  from the bridge, and agent 1 of type `c - ∑_{i≠1} θ̄ᵢ + ε` (small `ε > 0`) gains by claiming
  `θ₁ = 0` (`example_23_B_3`).
* **Example 23.B.4** (pp. 862-863): with one indivisible good, `X = {(y, t) : yᵢ ∈ {0, 1},
  ∑ᵢ yᵢ = 1, ∑ᵢ tᵢ ≤ 0}` (the winner `k` with `yᵢ = 1` iff `k = i`), ex post efficiency is
  `yᵢ(θ)(θᵢ - max_j θⱼ) = 0` for all `i` together with `∑ᵢ tᵢ(θ) = 0`
  (`example_23_B_4_efficient_iff`); the three bilateral trade cases (`example_23_B_4_bilateral`).
  The auction parts of Example 23.B.4 are in `Auctions23B.lean`.

Departures: types are real numbers (`Θᵢ = ℝ`) in Examples 23.B.3-23.B.4; MWG's type sets are
subsets (`[0, ∞)`, `{θ̄ᵢ}`, `[θ̲ᵢ, θ̄ᵢ]`) and ex post efficiency is a condition profile by profile,
so it restricts to them. No corrections.
-/

namespace MWG.MechanismDesign

open Function

/-! ### Example 23.B.1 and Exercise 23.B.1 -/

/-- **Example 23.B.1** (MWG, p. 860). The type sets: `Θ₁ = {θ̄₁}` (`Unit`) and `Θ₂ = {θ₂', θ₂''}`
(`true`, `false`). -/
abbrev b1Θ : Fin 2 → Type := ![Unit, Bool]

/-- **Example 23.B.1** (MWG, p. 860). Rank utilities on `X = {x, y, z}` (`0, 1, 2`):
`≿₁(θ̄₁)`: `x ≻ y ≻ z`; `≿₂(θ₂')`: `z ≻ y ≻ x`; `≿₂(θ₂'')`: `y ≻ x ≻ z`. -/
noncomputable def b1U : (i : Fin 2) → Fin 3 → b1Θ i → ℝ
  | 0 => fun x _ => ((![2, 1, 0] : Fin 3 → ℕ) x : ℝ)
  | 1 => fun x (b : Bool) => (((if b then ![0, 1, 2] else ![1, 2, 0]) : Fin 3 → ℕ) x : ℝ)

/-- A social choice function of Example 23.B.1, given by `g(θ₂) = f(θ̄₁, θ₂)`. -/
def b1F (g : Bool → Fin 3) : ((i : Fin 2) → b1Θ i) → Fin 3 := fun θ => g (θ 1)

/-- The type profile `(θ̄₁, θ₂)`. -/
def b1Prof (b : Bool) : (i : Fin 2) → b1Θ i := fun i => match i with
  | 0 => ()
  | 1 => b

/-- **Example 23.B.1** (MWG, p. 860). Agent 1 has a single type, so `f` is truthfully
implementable in dominant strategies iff agent 2 is always willing to reveal his type:
`u₂(f(θ̄₁, θ̂₂), θ₂) ≤ u₂(f(θ̄₁, θ₂), θ₂)` for all `θ₂, θ̂₂`. -/
theorem b1_strategyProof_iff (g : Bool → Fin 3) :
    StrategyProof b1U (b1F g) ↔ ∀ b b' : Bool, b1U 1 (g b') b ≤ b1U 1 (g b) b := by
  constructor
  · intro h b b'
    have := h 1 (b1Prof b) b'
    have e : b1F g (update (b1Prof b) 1 b') = g b' := by
      simp only [b1F]; exact congrArg g (update_self (β := b1Θ) 1 b' (b1Prof b))
    rw [e] at this; exact this
  · intro h i θ θh
    fin_cases i
    · have e : update θ 0 θh = θ := by
        funext j
        fin_cases j
        · rfl
        · rfl
      simp [e]
    · simpa [b1F] using h (θ 1) θh

/-- **Example 23.B.1** (MWG, p. 860). `f(θ̄₁, θ₂') = y`, `f(θ̄₁, θ₂'') = x`. -/
def b1Example : Bool → Fin 3 := fun b => if b then 1 else 0

/-- **Example 23.B.1** (MWG, p. 860). The social choice function `f(θ̄₁, θ₂') = y`,
`f(θ̄₁, θ₂'') = x` is ex post efficient: `y` and `x` are Pareto optimal for the respective
profiles. -/
theorem example_23_B_1_efficient : ExPostEfficient b1U (b1F b1Example) := by
  rw [exPostEfficient_iff]
  intro θ x hx i
  have h0 := hx 0
  have h1 := hx 1
  simp only [b1F, b1Example] at h0 h1 ⊢
  generalize θ 1 = b at h0 h1 ⊢
  revert h0 h1
  fin_cases i <;> fin_cases x <;> cases b <;> norm_num [b1U]

/-- **Example 23.B.1** (MWG, p. 860). Agent 2 of type `θ₂''` strictly prefers `y = f(θ̄₁, θ₂')` to
`x = f(θ̄₁, θ₂'')`, so he will claim to be of type `θ₂'`: `f` is not truthfully implementable
in dominant strategies. -/
theorem example_23_B_1 :
    b1U 1 (b1F b1Example (b1Prof false)) false < b1U 1 (b1F b1Example (b1Prof true)) false ∧
      ¬StrategyProof b1U (b1F b1Example) := by
  refine ⟨by norm_num [b1U, b1F, b1Example, b1Prof], fun h => ?_⟩
  have := (b1_strategyProof_iff _).1 h false true
  norm_num [b1U, b1Example] at this

/-- **Exercise 23.B.1(a)** (MWG, p. 918). `f(θ̄₁, θ₂') = y`, `f(θ̄₁, θ₂'') = y`: agent 2 reveals his
type truthfully. -/
theorem exercise_23_B_1a : StrategyProof b1U (b1F fun _ => 1) :=
  (b1_strategyProof_iff _).2 fun b b' => by cases b <;> cases b' <;> norm_num [b1U]

/-- **Exercise 23.B.1(b)** (MWG, p. 918). `f(θ̄₁, θ₂') = z`, `f(θ̄₁, θ₂'') = x`: agent 2 reveals his
type truthfully. -/
theorem exercise_23_B_1b : StrategyProof b1U (b1F fun b => if b then 2 else 0) :=
  (b1_strategyProof_iff _).2 fun b b' => by cases b <;> cases b' <;> norm_num [b1U]

/-- **Exercise 23.B.1(c)** (MWG, p. 918). `f(θ̄₁, θ₂') = z`, `f(θ̄₁, θ₂'') = y`: agent 2 reveals his
type truthfully (he always gets his best alternative). -/
theorem exercise_23_B_1c : StrategyProof b1U (b1F fun b => if b then 2 else 1) :=
  (b1_strategyProof_iff _).2 fun b b' => by cases b <;> cases b' <;> norm_num [b1U]

/-- **Exercise 23.B.1(d)** (MWG, p. 918). `f(θ̄₁, θ₂') = z`, `f(θ̄₁, θ₂'') = z`: agent 2 reveals his
type truthfully (a constant function). -/
theorem exercise_23_B_1d : StrategyProof b1U (b1F fun _ => 2) :=
  (b1_strategyProof_iff _).2 fun b b' => by cases b <;> cases b' <;> norm_num [b1U]

/-- **Exercise 23.B.1(e)** (MWG, p. 918). `f(θ̄₁, θ₂') = y`, `f(θ̄₁, θ₂'') = z`: agent 2 of type
`θ₂'` prefers `z` to `y`, so he claims `θ₂''`; `f` is not truthfully implementable. -/
theorem exercise_23_B_1e : ¬StrategyProof b1U (b1F fun b => if b then 1 else 2) := by
  intro h
  have := (b1_strategyProof_iff _).1 h true false
  norm_num [b1U] at this

/-! ### Example 23.B.3: a public project -/

/-- The project level `k ∈ {0, 1}` (`false`, `true`) as a real number. -/
def ppK (k : Bool) : ℝ := if k then 1 else 0

/-- **Example 23.B.3** (MWG, p. 861). The feasible alternatives with project cost `c`:
`X = {(k, t₁, …, t_I) : k ∈ {0, 1}, ∑ᵢ tᵢ ≤ -ck}`. -/
def PPAlt (ι : Type*) [Fintype ι] (c : ℝ) : Type _ :=
  {x : Bool × (ι → ℝ) // ∑ i, x.2 i ≤ -(c * ppK x.1)}

/-- **Example 23.B.3** (MWG, p. 861). `uᵢ(x, θᵢ) = θᵢk + (m̄ᵢ + tᵢ)`. -/
def ppU {ι : Type*} (m : ι → ℝ) : (i : ι) → Bool × (ι → ℝ) → ℝ → ℝ :=
  fun i x θi => θi * ppK x.1 + (m i + x.2 i)

variable {ι : Type*}

open Finset in
/-- **Example 23.B.3** (MWG, p. 861). If at `θ` the alternative `(k, t)` leaves a surplus
`δ = (∑ᵢ θᵢ - c)(k' - k) - (∑ᵢ tᵢ + ck) > 0` by switching to project level `k'`, then some
feasible alternative makes every agent strictly better off (each gets `δ/I` more). -/
theorem pp_improve [Fintype ι] [Nonempty ι] (c : ℝ) (m : ι → ℝ) (θ : ι → ℝ) (x : PPAlt ι c)
    (k' : Bool)
    (hδ : 0 < (∑ i, θ i - c) * (ppK k' - ppK x.1.1) - (∑ i, x.1.2 i + c * ppK x.1.1)) :
    ∃ x' : PPAlt ι c, ∀ i, ppU m i x.1 (θ i) < ppU m i x'.1 (θ i) := by
  have hI : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  set δ := (∑ i, θ i - c) * (ppK k' - ppK x.1.1) - (∑ i, x.1.2 i + c * ppK x.1.1) with hδdef
  let t' : ι → ℝ := fun i => x.1.2 i + θ i * (ppK x.1.1 - ppK k') + δ / Fintype.card ι
  have hsum : ∑ i, t' i = -(c * ppK k') := by
    simp only [t', sum_add_distrib, ← sum_mul, sum_const, card_univ, nsmul_eq_mul]
    field_simp
    rw [hδdef]
    ring
  refine ⟨⟨(k', t'), hsum.le⟩, fun i => ?_⟩
  simp only [ppU, t']
  have := div_pos hδ hI
  nlinarith

open Finset in
/-- **Example 23.B.3** (MWG, p. 861). With the feasible set `∑ᵢ tᵢ ≤ -ck`, a social choice function
`f(θ) = (k(θ), t(θ))` is ex post efficient iff for all `θ` the project is built when
`∑ᵢ θᵢ > c`, not built when `∑ᵢ θᵢ < c`, and there is no waste: `∑ᵢ tᵢ(θ) = -ck(θ)`. -/
theorem example_23_B_3_efficient_iff [Fintype ι] [Nonempty ι] (c : ℝ) (m : ι → ℝ)
    (f : (ι → ℝ) → PPAlt ι c) :
    ExPostEfficient (Θ := fun _ => ℝ) (fun i (x : PPAlt ι c) θi => ppU m i x.1 θi) f ↔
      ∀ θ, (c < ∑ i, θ i → (f θ).1.1 = true) ∧ (∑ i, θ i < c → (f θ).1.1 = false) ∧
        ∑ i, (f θ).1.2 i = -(c * ppK (f θ).1.1) := by
  constructor
  · intro hE θ
    have no : ∀ k', ¬0 < (∑ i, θ i - c) * (ppK k' - ppK (f θ).1.1) -
        (∑ i, (f θ).1.2 i + c * ppK (f θ).1.1) := by
      intro k' hδ
      obtain ⟨x', hx'⟩ := pp_improve c m θ (f θ) k' hδ
      exact hE ⟨θ, x', fun i => (hx' i).le, Classical.arbitrary ι, hx' _⟩
    have hfeas := (f θ).2
    refine ⟨fun hc => ?_, fun hc => ?_, ?_⟩
    · by_contra hk
      have := no true
      simp only [Bool.not_eq_true] at hk
      simp only [hk, ppK, Bool.false_eq_true, ↓reduceIte] at this hfeas
      apply this; linarith
    · by_contra hk
      have := no false
      simp only [Bool.not_eq_false] at hk
      simp only [hk, ppK, Bool.false_eq_true, ↓reduceIte] at this hfeas
      apply this; linarith
    · by_contra hne
      have := no (f θ).1.1
      apply this
      have := lt_of_le_of_ne hfeas hne
      linarith
  · rintro hf ⟨θ, x, hx, j, hj⟩
    have hsum : ∑ i, ppU m i (f θ).1 (θ i) < ∑ i, ppU m i x.1 (θ i) :=
      sum_lt_sum (fun i _ => hx i) ⟨j, mem_univ j, hj⟩
    simp only [ppU, sum_add_distrib, ← sum_mul] at hsum
    obtain ⟨h1, h2, h3⟩ := hf θ
    have hx2 := x.2
    have key : (∑ i, θ i - c) * ppK x.1.1 ≤ (∑ i, θ i - c) * ppK (f θ).1.1 := by
      have hK : ppK x.1.1 = 0 ∨ ppK x.1.1 = 1 := by
        cases x.1.1 <;> simp [ppK]
      rcases lt_trichotomy (∑ i, θ i) c with hlt | heq | hgt
      · have e : ppK (f θ).1.1 = 0 := by rw [h2 hlt]; simp [ppK]
        rw [e, mul_zero]
        rcases hK with h | h
        · rw [h, mul_zero]
        · rw [h, mul_one]; linarith
      · rw [heq]; simp
      · have e : ppK (f θ).1.1 = 1 := by rw [h1 hgt]; simp [ppK]
        rw [e, mul_one]
        rcases hK with h | h
        · rw [h, mul_zero]; linarith
        · rw [h, mul_one]
    nlinarith

open Finset in
/-- **Example 23.B.3**, (23.B.1)-(23.B.2) (MWG, p. 861). If `k(θ) = 1` iff `∑ᵢ θᵢ ≥ c` and
`∑ᵢ tᵢ(θ) = -ck(θ)` for all `θ`, then `f` is ex post efficient. -/
theorem example_23_B_3_efficient [Fintype ι] [Nonempty ι] (c : ℝ) (m : ι → ℝ)
    (f : (ι → ℝ) → PPAlt ι c) (hk : ∀ θ, (f θ).1.1 = decide (c ≤ ∑ i, θ i))
    (ht : ∀ θ, ∑ i, (f θ).1.2 i = -(c * ppK (f θ).1.1)) :
    ExPostEfficient (Θ := fun _ => ℝ) (fun i (x : PPAlt ι c) θi => ppU m i x.1 θi) f := by
  refine (example_23_B_3_efficient_iff c m f).2 fun θ => ⟨fun h => ?_, fun h => ?_, ht θ⟩
  · rw [hk θ]; exact decide_eq_true h.le
  · rw [hk θ]; exact decide_eq_false (not_le.2 h)

open Finset in
/-- **Example 23.B.3** (MWG, p. 861). The ex post efficient social choice function with the
egalitarian contribution rule: `k(θ) = 1` iff `∑ᵢ θᵢ ≥ c`, `tᵢ(θ) = -(c/I)k(θ)`. -/
noncomputable def ppEgal [Fintype ι] (c : ℝ) (θ : ι → ℝ) : PPAlt ι c :=
  ⟨(decide (c ≤ ∑ i, θ i), fun _ => -(c / Fintype.card ι * ppK (decide (c ≤ ∑ i, θ i)))), by
    by_cases h : Fintype.card ι = 0
    · have : IsEmpty ι := Fintype.card_eq_zero_iff.1 h
      simp only [univ_eq_empty, sum_empty, ppK]
      split_ifs with hc
      · simp only [decide_eq_true_eq] at hc; linarith
      · simp
    · simp only [sum_const, card_univ, nsmul_eq_mul]
      field_simp
      exact le_rfl⟩

open Finset in
/-- **Example 23.B.3** (MWG, p. 861). The egalitarian social choice function is ex post
efficient. -/
theorem ppEgal_efficient [Fintype ι] [Nonempty ι] (c : ℝ) (m : ι → ℝ) :
    ExPostEfficient (Θ := fun _ => ℝ) (fun i (x : PPAlt ι c) θi => ppU m i x.1 θi)
      (ppEgal c) := by
  have hI : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  refine example_23_B_3_efficient c m _ (fun _ => rfl) fun θ => ?_
  simp only [ppEgal, sum_const, card_univ, nsmul_eq_mul]
  field_simp

open Finset in
/-- **Example 23.B.3** (MWG, p. 862). With the egalitarian rule, `Θᵢ = {θ̄ᵢ}` for `i ≠ 1` and
`c > ∑_{i≠1} θ̄ᵢ > c(I - 1)/I`, writing `S = ∑_{i≠1} θ̄ᵢ`:
(i) agent 1's type is critical: the bridge is built iff `θ₁ ≥ c - S`;
(ii) the other agents' total utility gain from the bridge, `∑_{i≠1} (θ̄ᵢ - c/I)`, is positive;
(iii) for `0 < ε < S - c(I - 1)/I`, agent 1 of type `θ₁ = c - S + ε ∈ Θ₁ = [0, ∞)` gets
`(c(I - 1)/I - S + ε) + m̄₁ < m̄₁` by telling the truth, and `m̄₁` by claiming `θ₁ = 0`. -/
theorem example_23_B_3 [Fintype ι] [DecidableEq ι] (c : ℝ) (m : ι → ℝ) (i₀ : ι)
    (θbar : ι → ℝ) (hc1 : ∑ j ∈ univ.erase i₀, θbar j < c)
    (hc2 : c * (Fintype.card ι - 1) / Fintype.card ι < ∑ j ∈ univ.erase i₀, θbar j)
    {ε : ℝ} (hε : 0 < ε)
    (hε' : ε < ∑ j ∈ univ.erase i₀, θbar j - c * (Fintype.card ι - 1) / Fintype.card ι) :
    (∀ a, (ppEgal c (update θbar i₀ a)).1.1 = true ↔ c - ∑ j ∈ univ.erase i₀, θbar j ≤ a) ∧
      0 < ∑ j ∈ univ.erase i₀, (θbar j - c / Fintype.card ι) ∧
      0 ≤ c - ∑ j ∈ univ.erase i₀, θbar j + ε ∧
      ppU m i₀ (ppEgal c (update θbar i₀ (c - ∑ j ∈ univ.erase i₀, θbar j + ε))).1
          (c - ∑ j ∈ univ.erase i₀, θbar j + ε) =
        (c * (Fintype.card ι - 1) / Fintype.card ι - ∑ j ∈ univ.erase i₀, θbar j + ε) + m i₀ ∧
      ppU m i₀ (ppEgal c (update θbar i₀ 0)).1 (c - ∑ j ∈ univ.erase i₀, θbar j + ε) = m i₀ ∧
      ppU m i₀ (ppEgal c (update θbar i₀ (c - ∑ j ∈ univ.erase i₀, θbar j + ε))).1
          (c - ∑ j ∈ univ.erase i₀, θbar j + ε) <
        ppU m i₀ (ppEgal c (update θbar i₀ 0)).1 (c - ∑ j ∈ univ.erase i₀, θbar j + ε) := by
  set S := ∑ j ∈ univ.erase i₀, θbar j with hS
  have hne : Nonempty ι := ⟨i₀⟩
  have hI : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hk : ∀ a, (ppEgal c (update θbar i₀ a)).1.1 = decide (c - S ≤ a) := by
    intro a
    simp only [ppEgal, bb_sum_update, ← hS]
    congr 1
    exact propext ⟨fun h => by linarith, fun h => by linarith⟩
  have hcrit : ∀ a, (ppEgal c (update θbar i₀ a)).1.1 = true ↔ c - S ≤ a := by
    intro a; rw [hk a]; simp
  have hcard : ((univ.erase i₀).card : ℝ) = Fintype.card ι - 1 := by
    rw [card_erase_of_mem (mem_univ i₀), card_univ, Nat.cast_sub Fintype.card_pos]; simp
  have hothers : ∑ j ∈ univ.erase i₀, (θbar j - c / Fintype.card ι) =
      S - c * (Fintype.card ι - 1) / Fintype.card ι := by
    rw [sum_sub_distrib, sum_const, nsmul_eq_mul, hcard]; ring
  have htrue : ppU m i₀ (ppEgal c (update θbar i₀ (c - S + ε))).1 (c - S + ε) =
      (c * (Fintype.card ι - 1) / Fintype.card ι - S + ε) + m i₀ := by
    have h1 := (hcrit (c - S + ε)).2 (by linarith)
    simp only [ppU]
    rw [h1]
    simp only [ppEgal] at h1 ⊢
    rw [h1]
    simp only [ppK, ↓reduceIte]
    field_simp
    ring
  have hlie : ppU m i₀ (ppEgal c (update θbar i₀ 0)).1 (c - S + ε) = m i₀ := by
    have h0 : (ppEgal c (update θbar i₀ 0)).1.1 = false := by
      rw [hk 0]; simp only [decide_eq_false_iff_not, not_le]; linarith
    simp only [ppU]
    rw [h0]
    simp only [ppEgal] at h0 ⊢
    rw [h0]
    simp [ppK]
  refine ⟨hcrit, by rw [hothers]; exact sub_pos.2 hc2, by linarith, htrue, hlie, ?_⟩
  rw [htrue, hlie]
  linarith

/-! ### Example 23.B.4: allocation of a single indivisible good -/

open Finset in
/-- **Example 23.B.4** (MWG, p. 862). With the good going to agent `k` (`yᵢ = 1` iff `k = i`) and
`vᵢ(k, θᵢ) = θᵢyᵢ`, the project rule is efficient (23.C.7) iff it always gives the good to a
highest valuation: `yᵢ(θ)(θᵢ - max_j θⱼ) = 0` for all `i` and `θ`. -/
theorem goodV_efficient_iff [Fintype ι] [DecidableEq ι] [Nonempty ι] (k : (ι → ℝ) → ι) :
    EfficientProject (Θ := fun _ => ℝ) goodV k ↔
      ∀ θ i, (if k θ = i then (1 : ℝ) else 0) * (θ i - univ.sup' univ_nonempty θ) = 0 := by
  have hs : ∀ (θ : ι → ℝ) (w : ι), ∑ i, goodV i w (θ i) = θ w := by
    intro θ w
    simp [goodV]
  constructor
  · intro h θ i
    by_cases hi : k θ = i
    · subst hi
      have hle : univ.sup' univ_nonempty θ ≤ θ (k θ) :=
        sup'_le _ _ fun j _ => by have := h θ j; rwa [hs, hs] at this
      have hge := le_sup' θ (mem_univ (k θ))
      simp only [↓reduceIte, one_mul]
      linarith
    · simp [hi]
  · intro h θ w
    have := h θ (k θ)
    simp only [↓reduceIte, one_mul, sub_eq_zero] at this
    rw [hs, hs, this]
    exact le_sup' θ (mem_univ w)

open Finset in
/-- **Example 23.B.4** (MWG, p. 862). A social choice function `f(θ) = (y(θ), t(θ))` allocating a
single indivisible good, with feasible set `X = {(y, t) : ∑ᵢ yᵢ = 1, ∑ᵢ tᵢ ≤ 0}` (the good goes to
agent `k`), is ex post efficient iff `yᵢ(θ)(θᵢ - max_j θⱼ) = 0` for all `i` and `∑ᵢ tᵢ(θ) = 0`, for
all `θ`. -/
theorem example_23_B_4_efficient_iff [Fintype ι] [DecidableEq ι] [Nonempty ι] (m : ι → ℝ)
    (f : (ι → ℝ) → QLAlt ι ι) :
    ExPostEfficient (Θ := fun _ => ℝ) (fun i (x : QLAlt ι ι) θi => qlU goodV m i x.1 θi) f ↔
      (∀ θ i, (if (f θ).1.1 = i then (1 : ℝ) else 0) * (θ i - univ.sup' univ_nonempty θ) = 0) ∧
        ∀ θ, ∑ i, (f θ).1.2 i = 0 := by
  rw [exPostEfficient_ql_iff (Θ := fun _ => ℝ) goodV m f, goodV_efficient_iff]
  rfl

/-- **Example 23.B.4**, bilateral trade (MWG, p. 863). Seller (agent 1) and buyer (agent 2) with
`θ₁ ∈ [lo₁, hi₁]`, `θ₂ ∈ [lo₂, hi₂]`: if `lo₂ > hi₁` there are certainly gains from trade; if
`lo₁ > hi₂` there are certainly none; if `lo₂ < hi₁` and `lo₁ < hi₂` both can happen. -/
theorem example_23_B_4_bilateral {lo1 hi1 lo2 hi2 : ℝ} (h1 : lo1 ≤ hi1) (h2 : lo2 ≤ hi2) :
    (hi1 < lo2 → ∀ θ1 ∈ Set.Icc lo1 hi1, ∀ θ2 ∈ Set.Icc lo2 hi2, θ1 < θ2) ∧
      (hi2 < lo1 → ∀ θ1 ∈ Set.Icc lo1 hi1, ∀ θ2 ∈ Set.Icc lo2 hi2, θ2 < θ1) ∧
      (lo2 < hi1 → lo1 < hi2 → (∃ θ1 ∈ Set.Icc lo1 hi1, ∃ θ2 ∈ Set.Icc lo2 hi2, θ1 < θ2) ∧
        ∃ θ1 ∈ Set.Icc lo1 hi1, ∃ θ2 ∈ Set.Icc lo2 hi2, θ2 < θ1) := by
  refine ⟨fun h θ1 hθ1 θ2 hθ2 => by linarith [hθ1.2, hθ2.1],
    fun h θ1 hθ1 θ2 hθ2 => by linarith [hθ1.1, hθ2.2], fun ha hb => ⟨?_, ?_⟩⟩
  · exact ⟨lo1, ⟨le_rfl, h1⟩, hi2, ⟨h2, le_rfl⟩, hb⟩
  · exact ⟨hi1, ⟨h1, le_rfl⟩, lo2, ⟨le_rfl, h2⟩, ha⟩

end MWG.MechanismDesign
