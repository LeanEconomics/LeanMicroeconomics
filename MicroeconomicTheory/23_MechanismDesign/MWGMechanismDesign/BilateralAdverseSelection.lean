/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Bilateral trade with adverse selection

MWG, Section 23.F, Example 23.F.3 (pp. 906-910), with Exercises 23.F.8, 23.F.9 and 23.F.10
(p. 924).

A seller (agent 1) of one unit has a type `θ_L` or `θ_H` (`Prob(θ_H) = .2`); the buyer (agent 2)
has no private information. A social choice function is `(y_L, t_L, y_H, t_H)` (trade
probability and transfer to the seller for each seller type), with utilities (23.F.11)
`u₁(y, t | θ_L) = t + 20(1 - y)`, `u₁(y, t | θ_H) = t + 40(1 - y)`, `u₂(y, t | θ_L) = 30y - t`,
`u₂(y, t | θ_H) = 50y - t`. We write `.2 = 1/5` and `.8 = 4/5`.

* The incentive feasible set `F*`: interim IR (23.F.12)-(23.F.14) and BIC (23.F.15)-(23.F.16).
* **Exercise 23.F.8**: an ex post (classically) efficient social choice function has
  `y_L = y_H = 1` (and conversely, for the trade probabilities).
* **Exercise 23.F.9(a)-(c)** = properties (i)-(iii) on p. 907.
* Problem (23.F.17), **Steps 1-4**, the reduced problems (23.F.18), (23.F.19), and the explicit
  solution of (23.F.19) (Figure 23.F.1): `y_H = (8 - ū₁H - ū₂)/14`, `t_H = 40 y_H + ū₁H`.
* The interim incentive efficient social choice functions (Definition 23.F.2 with `F = F*`) are
  exactly `y_L = 1`, `t_L = 20 + t_H - 20 y_H` with `(y_H, t_H)` in the shaded set of
  Figure 23.F.2, `{y_H ∈ [0, 1], t_H ≥ 40 y_H, t_H ≤ 26 y_H + 8}` (`bas_interimIE_iff`); they are
  exactly the solutions of (23.F.17) for some `ū₁H, ū₂ ≥ 0`; and `y_H ≤ 4/7`.
* The ex ante incentive efficient social choice functions (Definition 23.F.1 with `F = F*`) are
  exactly those with, in addition, `t_H = 40 y_H` (the boundary segment of Figure 23.F.3,
  `y_H ∈ [0, 4/7]`); the high-quality seller's IR constraint binds; footnote 54: `y_H ≤ 4/7 < 1`.
* **Exercise 23.F.10** (seller IR not imposed, buyer IR imposed): the interim incentive
  efficient set is `y_L = 1`, `t_L = 20 + t_H - 20 y_H`, `y_H ∈ [0, 1]`, `t_H ≤ 26 y_H + 8`; the ex
  ante incentive efficient set is `y_L = y_H = 1`, `t_L = t_H ≤ 34` (all ex post efficient).

Proof device (ours, not MWG's): on `F*` (indeed whenever (IC_L) holds and `y_L ≤ 1`),
`7 U₁(θ_L) + 3 U₁(θ_H) + 10 U₂ ≤ 340` (`bas_key`), with equality exactly when `y_L = 1` and
(IC_L) binds; the ex ante analogue is `14 U₁ + 16 U₂ ≤ 464` on `F*`.
-/

namespace MWG.MechanismDesign

/-- **Example 23.F.3** (MWG, p. 906). A social choice function `(y_L, t_L, y_H, t_H)`: the
probability of trade and the transfer from the buyer to the seller for each seller type. -/
structure BasSCF where
  /-- Probability of trade when the seller's type is `θ_L`. -/
  yL : ℝ
  /-- Transfer to the seller when his type is `θ_L`. -/
  tL : ℝ
  /-- Probability of trade when the seller's type is `θ_H`. -/
  yH : ℝ
  /-- Transfer to the seller when his type is `θ_H`. -/
  tH : ℝ

namespace BasSCF

/-- **(23.F.11)** (MWG, p. 906). The low-quality seller's utility `t_L + 20(1 - y_L)`. -/
def U1L (f : BasSCF) : ℝ := f.tL + 20 * (1 - f.yL)

/-- **(23.F.11)** (MWG, p. 906). The high-quality seller's utility `t_H + 40(1 - y_H)`. -/
def U1H (f : BasSCF) : ℝ := f.tH + 40 * (1 - f.yH)

/-- **(23.F.14)** (MWG, p. 906). The buyer's (interim = ex ante) expected utility
`.2(50 y_H - t_H) + .8(30 y_L - t_L)`. -/
noncomputable def U2 (f : BasSCF) : ℝ := 1 / 5 * (50 * f.yH - f.tH) + 4 / 5 * (30 * f.yL - f.tL)

/-- The seller's ex ante expected utility (MWG, p. 909),
`U₁ = .8(t_L + 20(1 - y_L)) + .2(t_H + 40(1 - y_H))`. -/
noncomputable def U1 (f : BasSCF) : ℝ := 4 / 5 * f.U1L + 1 / 5 * f.U1H

/-- Trade probabilities lie in `[0, 1]`. -/
def Prob (f : BasSCF) : Prop := 0 ≤ f.yL ∧ f.yL ≤ 1 ∧ 0 ≤ f.yH ∧ f.yH ≤ 1

/-- **(23.F.15)** (MWG, p. 907), `(IC_H)`: `t_H + 40(1 - y_H) ≥ t_L + 40(1 - y_L)`. -/
def ICH (f : BasSCF) : Prop := f.tL + 40 * (1 - f.yL) ≤ f.tH + 40 * (1 - f.yH)

/-- **(23.F.16)** (MWG, p. 907), `(IC_L)`: `t_L + 20(1 - y_L) ≥ t_H + 20(1 - y_H)`. -/
def ICL (f : BasSCF) : Prop := f.tH + 20 * (1 - f.yH) ≤ f.tL + 20 * (1 - f.yL)

/-- **(23.F.12)** (MWG, p. 906), `(IR_1L)`: `t_L + 20(1 - y_L) ≥ 20`. -/
def IR1L (f : BasSCF) : Prop := 20 ≤ f.U1L

/-- **(23.F.13)** (MWG, p. 906), `(IR_1H)`: `t_H + 40(1 - y_H) ≥ 40`. -/
def IR1H (f : BasSCF) : Prop := 40 ≤ f.U1H

/-- **(23.F.14)** (MWG, p. 906), `(IR_2)`: `.2(50 y_H - t_H) + .8(30 y_L - t_L) ≥ 0`. -/
def IR2 (f : BasSCF) : Prop := 0 ≤ f.U2

end BasSCF

/-- **Example 23.F.3** (MWG, pp. 906-907). The incentive feasible set `F*`: trade probabilities in
`[0, 1]`, Bayesian incentive compatibility (23.F.15)-(23.F.16) and interim individual
rationality (23.F.12)-(23.F.14). -/
def basFStar : Set BasSCF :=
  {f | f.Prob ∧ f.ICH ∧ f.ICL ∧ f.IR1L ∧ f.IR1H ∧ f.IR2}

/-- **Exercise 23.F.10** (MWG, p. 924). The feasible set when trade is not voluntary for the
seller (but is for the buyer): BIC and the buyer's IR constraint only. -/
def basFBuyerIR : Set BasSCF :=
  {f | f.Prob ∧ f.ICH ∧ f.ICL ∧ f.IR2}

/-- Interim (weak) dominance with one strict improvement: `U₁(θ_L | g) ≥ U₁(θ_L | f)`,
`U₁(θ_H | g) ≥ U₁(θ_H | f)`, `U₂(g) ≥ U₂(f)`, one of them strict. -/
def basInterimDominates (g f : BasSCF) : Prop :=
  f.U1L ≤ g.U1L ∧ f.U1H ≤ g.U1H ∧ f.U2 ≤ g.U2 ∧ (f.U1L < g.U1L ∨ f.U1H < g.U1H ∨ f.U2 < g.U2)

/-- Ex ante (weak) dominance with one strict improvement: `U₁(g) ≥ U₁(f)`, `U₂(g) ≥ U₂(f)`,
one of them strict. -/
def basExAnteDominates (g f : BasSCF) : Prop :=
  f.U1 ≤ g.U1 ∧ f.U2 ≤ g.U2 ∧ (f.U1 < g.U1 ∨ f.U2 < g.U2)

/-- **Definition 23.F.2** (MWG, p. 898) in Example 23.F.3: `f` is interim efficient in `F`. -/
def BasInterimEfficientIn (F : Set BasSCF) (f : BasSCF) : Prop :=
  f ∈ F ∧ ¬ ∃ g ∈ F, basInterimDominates g f

/-- **Definition 23.F.1** (MWG, p. 898) in Example 23.F.3: `f` is ex ante efficient in `F`. -/
def BasExAnteEfficientIn (F : Set BasSCF) (f : BasSCF) : Prop :=
  f ∈ F ∧ ¬ ∃ g ∈ F, basExAnteDominates g f

/-- Ex post (classical) efficiency of the outcome `(y, t)` for one seller type, whose valuation
is `a` for the seller and `b` for the buyer (Definition 23.B.2 = Definition 23.F.3 with all
social choice functions, p. 900): `y ∈ [0, 1]` and no `(y', t')` with `y' ∈ [0, 1]` makes one
agent better off and neither worse off. -/
def BasPairEfficient (a b y t : ℝ) : Prop :=
  0 ≤ y ∧ y ≤ 1 ∧ ¬ ∃ y' t' : ℝ, 0 ≤ y' ∧ y' ≤ 1 ∧ t + a * (1 - y) ≤ t' + a * (1 - y') ∧
    b * y - t ≤ b * y' - t' ∧ (t + a * (1 - y) < t' + a * (1 - y') ∨ b * y - t < b * y' - t')

/-- **Example 23.F.3** (MWG, p. 906). The social choice function is ex post (classically)
efficient: efficient for each realisation of the seller's type. -/
def BasExPostEfficient (f : BasSCF) : Prop :=
  BasPairEfficient 20 30 f.yL f.tL ∧ BasPairEfficient 40 50 f.yH f.tH

/-- When the buyer values the good more than the seller (`a < b`), an outcome is ex post
efficient iff trade occurs for sure. -/
theorem basPairEfficient_iff {a b y t : ℝ} (hab : a < b) :
    BasPairEfficient a b y t ↔ y = 1 := by
  constructor
  · rintro ⟨h0, h1, hne⟩
    by_contra hy
    have hy' : y < 1 := lt_of_le_of_ne h1 hy
    apply hne
    refine ⟨1, t + a * (1 - y) + (b - a) * (1 - y) / 2, zero_le_one, le_rfl, ?_, ?_, ?_⟩
    · have : 0 < (b - a) * (1 - y) := mul_pos (by linarith) (by linarith)
      linarith
    · have : 0 < (b - a) * (1 - y) := mul_pos (by linarith) (by linarith)
      nlinarith
    · left
      have : 0 < (b - a) * (1 - y) := mul_pos (by linarith) (by linarith)
      linarith
  · rintro rfl
    refine ⟨zero_le_one, le_rfl, ?_⟩
    rintro ⟨y', t', h0, h1, hu1, hu2, hs⟩
    have hp : 0 ≤ (b - a) * (1 - y') := mul_nonneg (by linarith) (by linarith)
    rcases hs with hs | hs <;> nlinarith

/-- **Exercise 23.F.8** (MWG, p. 924). Any ex post classically efficient social choice function in
Example 23.F.3 has `y_L = y_H = 1` (and conversely these trade probabilities make it ex post
efficient, whatever the transfers). -/
theorem exercise_23_F_8 (f : BasSCF) : BasExPostEfficient f ↔ f.yL = 1 ∧ f.yH = 1 := by
  unfold BasExPostEfficient
  rw [basPairEfficient_iff (by norm_num), basPairEfficient_iff (by norm_num)]

/-- **Exercise 23.F.9(a)** (MWG, pp. 907, 924), property (i). No feasible social choice function
(element of `F*`) is ex post (classically) efficient. -/
theorem exercise_23_F_9a (f : BasSCF) (hf : f ∈ basFStar) : ¬ BasExPostEfficient f := by
  rw [exercise_23_F_8]
  rintro ⟨hL, hH⟩
  obtain ⟨-, -, hICL, hIRL, hIRH, hIR2⟩ := hf
  simp only [BasSCF.ICL, BasSCF.IR1L, BasSCF.IR1H, BasSCF.IR2, BasSCF.U1L, BasSCF.U1H,
    BasSCF.U2, hL, hH] at hICL hIRL hIRH hIR2
  linarith

/-- **Exercise 23.F.9(b)** (MWG, pp. 907, 924), property (ii). In any feasible social choice
function `y_H ≤ y_L` and `t_H ≤ t_L` (only incentive compatibility is needed). -/
theorem exercise_23_F_9b (f : BasSCF) (hf : f ∈ basFStar) : f.yH ≤ f.yL ∧ f.tH ≤ f.tL := by
  obtain ⟨-, hICH, hICL, -⟩ := hf
  simp only [BasSCF.ICH, BasSCF.ICL] at hICH hICL
  constructor <;> linarith

/-- **Exercise 23.F.9(c)** (MWG, pp. 907, 924), property (iii). In any feasible social choice
function the low-quality seller's expected gains from trade are at least the high-quality
seller's: `t_L - 20 y_L ≥ t_H - 40 y_H`. -/
theorem exercise_23_F_9c (f : BasSCF) (hf : f ∈ basFStar) :
    f.tH - 40 * f.yH ≤ f.tL - 20 * f.yL := by
  obtain ⟨⟨-, -, hyH, -⟩, -, hICL, -⟩ := hf
  simp only [BasSCF.ICL] at hICL
  linarith

/-! ### Problem (23.F.17) and Steps 1-4 -/

/-- The constraints of problem **(23.F.17)** (MWG, p. 907), for given `ū₁H, ū₂`:
`y_L, y_H ∈ [0, 1]`; (i) `t_H - 40 y_H ≥ t_L - 40 y_L`; (ii) `t_L - 20 y_L ≥ t_H - 20 y_H`;
(iii) `t_H - 40 y_H ≥ ū₁H`; (iv) `.2(50 y_H - t_H) + .8(30 y_L - t_L) ≥ ū₂`. -/
def basC17 (u1H u2 : ℝ) (f : BasSCF) : Prop :=
  f.Prob ∧ f.tL - 40 * f.yL ≤ f.tH - 40 * f.yH ∧ f.tH - 20 * f.yH ≤ f.tL - 20 * f.yL ∧
    u1H ≤ f.tH - 40 * f.yH ∧ u2 ≤ f.U2

/-- `f` solves problem **(23.F.17)** (MWG, p. 907): it maximises `t_L - 20 y_L` subject to the
constraints. -/
def BasSolves17 (u1H u2 : ℝ) (f : BasSCF) : Prop :=
  basC17 u1H u2 f ∧ ∀ g, basC17 u1H u2 g → g.tL - 20 * g.yL ≤ f.tL - 20 * f.yL

/-- **Problem (23.F.17)** (MWG, p. 907): the constraints are the incentive constraints
(23.F.15)-(23.F.16) and the participation constraints `U₁(θ_H) ≥ 40 + ū₁H`, `U₂ ≥ ū₂` with the
constants removed, and the objective is `U₁(θ_L) - 20`. -/
theorem basC17_iff (u1H u2 : ℝ) (f : BasSCF) :
    basC17 u1H u2 f ↔ f.Prob ∧ f.ICH ∧ f.ICL ∧ 40 + u1H ≤ f.U1H ∧ u2 ≤ f.U2 := by
  simp only [basC17, BasSCF.ICH, BasSCF.ICL, BasSCF.U1H]
  constructor
  · rintro ⟨h0, h1, h2, h3, h4⟩
    exact ⟨h0, by linarith, by linarith, by linarith, h4⟩
  · rintro ⟨h0, h1, h2, h3, h4⟩
    exact ⟨h0, by linarith, by linarith, by linarith, h4⟩

/-- **Problem (23.F.17)** (MWG, p. 907). With `ū₁H, ū₂ ≥ 0` its constraints imply membership of
`F*` (the low-quality seller's IR constraint follows from (ii), (iii) and `y_H ≥ 0`). -/
theorem basFStar_of_C17 {u1H u2 : ℝ} (h1 : 0 ≤ u1H) (h2 : 0 ≤ u2) {f : BasSCF}
    (hf : basC17 u1H u2 f) : f ∈ basFStar := by
  obtain ⟨hP, hi, hii, hiii, hiv⟩ := hf
  have hyH := hP.2.2.1
  refine ⟨hP, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [BasSCF.ICH, BasSCF.ICL, BasSCF.IR1L, BasSCF.IR1H, BasSCF.IR2, BasSCF.U1L,
      BasSCF.U1H] <;> linarith

/-- **Step 1** (MWG, pp. 907-908). Any solution to problem (23.F.17) has `y_L = 1`: otherwise
`(y_L + ε, t_L + 30ε, y_H, t_H)` (here with `ε = 1 - y_L`) satisfies all constraints and raises
the objective. -/
theorem bas_step1 {u1H u2 : ℝ} {f : BasSCF} (hf : BasSolves17 u1H u2 f) : f.yL = 1 := by
  obtain ⟨⟨⟨h0L, h1L, h0H, h1H⟩, hi, hii, hiii, hiv⟩, hmax⟩ := hf
  by_contra hne
  have hlt : f.yL < 1 := lt_of_le_of_ne h1L hne
  have hg := hmax ⟨1, f.tL + 30 * (1 - f.yL), f.yH, f.tH⟩
    ⟨⟨zero_le_one, le_rfl, h0H, h1H⟩, by dsimp only; linarith, by dsimp only; linarith,
      hiii, by simp only [BasSCF.U2] at hiv ⊢; linarith⟩
  dsimp only at hg
  linarith

/-- **Step 3** (MWG, p. 908). In any solution to problem (23.F.17), constraint (ii) binds:
otherwise `(y_L, t_L + ε, y_H + ε, t_H + 45ε)` for small `ε > 0` is feasible and raises the
objective. (We take `ε` equal to `1/24` of the slack in (ii); `y_H + ε ≤ 1` then follows from
(i) and `y_L ≤ 1`, so Step 2 is not needed here.) -/
theorem bas_step3 {u1H u2 : ℝ} {f : BasSCF} (hf : BasSolves17 u1H u2 f) :
    f.tL - 20 * f.yL = f.tH - 20 * f.yH := by
  obtain ⟨⟨⟨h0L, h1L, h0H, h1H⟩, hi, hii, hiii, hiv⟩, hmax⟩ := hf
  by_contra hne
  have hs : 0 < (f.tL - 20 * f.yL) - (f.tH - 20 * f.yH) := by
    rcases lt_or_eq_of_le hii with h | h
    · linarith
    · exact absurd h.symm hne
  set ε := ((f.tL - 20 * f.yL) - (f.tH - 20 * f.yH)) / 24 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hg := hmax ⟨f.yL, f.tL + ε, f.yH + ε, f.tH + 45 * ε⟩
    ⟨⟨h0L, h1L, by linarith, by dsimp only; linarith⟩, by dsimp only; linarith,
      by dsimp only; linarith, by dsimp only; linarith,
      by simp only [BasSCF.U2] at hiv ⊢; linarith⟩
  dsimp only at hg
  linarith

/-- **Step 4** (MWG, p. 908). If constraint (ii) binds and `y_L ≥ y_H`, then constraint (i) is
satisfied. -/
theorem bas_step4 {f : BasSCF} (hii : f.tL - 20 * f.yL = f.tH - 20 * f.yH)
    (hy : f.yH ≤ f.yL) : f.tL - 40 * f.yL ≤ f.tH - 40 * f.yH := by
  linarith

/-- The key inequality: whenever (IC_L) holds and `y_L ≤ 1`,
`7 U₁(θ_L) + 3 U₁(θ_H) + 10 U₂ ≤ 340`, and the slack is
`80 (1 - y_L) + ((t_L - 20 y_L) - (t_H - 20 y_H))`. -/
theorem bas_key (f : BasSCF) :
    7 * f.U1L + 3 * f.U1H + 10 * f.U2 =
      340 - 80 * (1 - f.yL) - ((f.tL - 20 * f.yL) - (f.tH - 20 * f.yH)) := by
  simp only [BasSCF.U1L, BasSCF.U1H, BasSCF.U2]
  ring

/-- The constraints of problem **(23.F.19)** (MWG, p. 908): `y_H ∈ [0, 1]`,
(ii) `t_H - 40 y_H ≥ ū₁H`, (iv') `26 y_H - t_H + 8 ≥ ū₂`. -/
def basC19 (u1H u2 yH tH : ℝ) : Prop :=
  0 ≤ yH ∧ yH ≤ 1 ∧ u1H ≤ tH - 40 * yH ∧ u2 ≤ 26 * yH - tH + 8

/-- `(y_H, t_H)` solves problem **(23.F.19)** (MWG, p. 908): it maximises `t_H - 20 y_H` subject
to the constraints. -/
def BasSolves19 (u1H u2 yH tH : ℝ) : Prop :=
  basC19 u1H u2 yH tH ∧ ∀ y t, basC19 u1H u2 y t → t - 20 * y ≤ tH - 20 * yH

/-- **Problem (23.F.19) and Figure 23.F.1** (MWG, pp. 908-909). For `ū₁H, ū₂ ≥ 0`, problem
(23.F.19) has a solution iff `ū₁H + ū₂ ≤ 8`, and its unique solution is the intersection of
`t_H = 40 y_H + ū₁H` and `t_H = 26 y_H + 8 - ū₂`: `y_H = (8 - ū₁H - ū₂)/14`,
`t_H = 40 y_H + ū₁H`. -/
theorem bas_solves19_iff {u1H u2 : ℝ} (h1 : 0 ≤ u1H) (h2 : 0 ≤ u2) (yH tH : ℝ) :
    BasSolves19 u1H u2 yH tH ↔
      u1H + u2 ≤ 8 ∧ yH = (8 - u1H - u2) / 14 ∧ tH = 40 * yH + u1H := by
  constructor
  · rintro ⟨⟨h0, h1', hii, hiv⟩, hmax⟩
    have hs : u1H + u2 ≤ 8 := by linarith
    have hg := hmax ((8 - u1H - u2) / 14) (40 * ((8 - u1H - u2) / 14) + u1H)
      ⟨by linarith, by linarith, by linarith, by linarith⟩
    refine ⟨hs, ?_, ?_⟩ <;> linarith
  · rintro ⟨hs, hy, ht⟩
    refine ⟨⟨by rw [hy]; linarith, by rw [hy]; linarith, by linarith, by rw [ht, hy]; linarith⟩,
      fun y t ⟨_, _, hii, hiv⟩ => ?_⟩
    rw [ht, hy]
    linarith

/-- **Problems (23.F.17)-(23.F.19)** (MWG, p. 908). For `ū₁H, ū₂ ≥ 0`, `f` solves (23.F.17) iff
`y_L = 1`, `t_L = 20 + t_H - 20 y_H` and `(y_H, t_H)` solves (23.F.19). -/
theorem bas_solves17_iff {u1H u2 : ℝ} (h1 : 0 ≤ u1H) (h2 : 0 ≤ u2) (f : BasSCF) :
    BasSolves17 u1H u2 f ↔
      f.yL = 1 ∧ f.tL = 20 + f.tH - 20 * f.yH ∧ BasSolves19 u1H u2 f.yH f.tH := by
  constructor
  · intro hf
    have hL := bas_step1 hf
    have hb := bas_step3 hf
    obtain ⟨⟨⟨h0L, h1L, h0H, h1H⟩, hi, hii, hiii, hiv⟩, hmax⟩ := hf
    simp only [BasSCF.U2] at hiv
    refine ⟨hL, by rw [hL] at hb; linarith,
      ⟨h0H, h1H, hiii, by rw [hL] at hiv; linarith⟩, fun y t ⟨hy0, hy1, hc2, hc4⟩ => ?_⟩
    have hg := hmax ⟨1, 20 + t - 20 * y, y, t⟩
      ⟨⟨zero_le_one, le_rfl, hy0, hy1⟩, by dsimp only; linarith, by dsimp only; linarith,
        hc2, by simp only [BasSCF.U2]; linarith⟩
    dsimp only at hg
    rw [hL] at hb
    linarith
  · rintro ⟨hL, htL, hs⟩
    obtain ⟨hs8, hy, ht⟩ := (bas_solves19_iff h1 h2 _ _).1 hs
    obtain ⟨⟨h0H, h1H, hii, hiv⟩, -⟩ := hs
    refine ⟨⟨⟨by rw [hL]; norm_num, hL.le, h0H, h1H⟩, by rw [hL]; linarith, by rw [hL]; linarith,
      hii, by simp only [BasSCF.U2]; rw [hL]; linarith⟩, fun g ⟨⟨_, hg1, _, _⟩, _, hgii, hgiii,
        hgiv⟩ => ?_⟩
    have hk := bas_key g
    simp only [BasSCF.U1L, BasSCF.U1H] at hk
    rw [hL]
    linarith

/-- **Step 2** (MWG, p. 908). For `ū₁H, ū₂ ≥ 0`, any solution to problem (23.F.17) has
`y_H < 1`: otherwise it would be ex post efficient and in `F*`, contradicting property (i). -/
theorem bas_step2 {u1H u2 : ℝ} (h1 : 0 ≤ u1H) (h2 : 0 ≤ u2) {f : BasSCF}
    (hf : BasSolves17 u1H u2 f) : f.yH < 1 := by
  have hF := basFStar_of_C17 h1 h2 hf.1
  have hL := bas_step1 hf
  by_contra hH
  have hH' : f.yH = 1 := le_antisymm hf.1.1.2.2.2 (not_lt.1 hH)
  exact exercise_23_F_9a f hF ((exercise_23_F_8 f).2 ⟨hL, hH'⟩)

/-- **Example 23.F.3** (MWG, p. 908). In any solution of (23.F.17) (with `ū₁H, ū₂ ≥ 0`),
constraint (i) is implied by the others, as Step 4 shows. -/
theorem bas_solves17_i_redundant {u1H u2 : ℝ} {f : BasSCF} (hf : BasSolves17 u1H u2 f) :
    f.tL - 40 * f.yL ≤ f.tH - 40 * f.yH :=
  bas_step4 (bas_step3 hf) (by rw [bas_step1 hf]; exact hf.1.1.2.2.2)

/-! ### Interim incentive efficiency -/

/-- **Figure 23.F.2** (MWG, p. 909). The shaded set
`{(y_H, t_H) : y_H ∈ [0, 1], t_H ≥ 40 y_H, t_H ≤ 26 y_H + 8}`. -/
def basShaded (yH tH : ℝ) : Prop := 0 ≤ yH ∧ yH ≤ 1 ∧ 40 * yH ≤ tH ∧ tH ≤ 26 * yH + 8

/-- **Figure 23.F.2** (MWG, p. 909). The shaded set is exactly the set of pairs `(y_H, t_H)` that
solve (23.F.19) for some `ū₁H ≥ 0`, `ū₂ ≥ 0`. -/
theorem bas_shaded_iff (yH tH : ℝ) :
    basShaded yH tH ↔ ∃ u1H u2 : ℝ, 0 ≤ u1H ∧ 0 ≤ u2 ∧ BasSolves19 u1H u2 yH tH := by
  constructor
  · rintro ⟨h0, h1, h2, h3⟩
    refine ⟨tH - 40 * yH, 26 * yH + 8 - tH, by linarith, by linarith, ?_⟩
    rw [bas_solves19_iff (by linarith) (by linarith)]
    refine ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨u1H, u2, h1, h2, hs⟩
    obtain ⟨hs8, hy, ht⟩ := (bas_solves19_iff h1 h2 _ _).1 hs
    refine ⟨by rw [hy]; linarith, by rw [hy]; linarith, by linarith, by rw [ht, hy]; linarith⟩

/-- **Example 23.F.3** (MWG, p. 909). On the shaded set, `y_H ≤ 4/7`. -/
theorem bas_shaded_yH_le {yH tH : ℝ} (h : basShaded yH tH) : yH ≤ 4 / 7 := by
  obtain ⟨-, -, h2, h3⟩ := h
  linarith

/-- **Example 23.F.3** (MWG, pp. 908-909). The interim incentive efficient social choice
functions (Definition 23.F.2 with `F = F*`) are exactly those with `y_L = 1`,
`t_L = 20 + t_H - 20 y_H` and `(y_H, t_H)` in the shaded set of Figure 23.F.2. -/
theorem bas_interimIE_iff (f : BasSCF) :
    BasInterimEfficientIn basFStar f ↔
      f.yL = 1 ∧ f.tL = 20 + f.tH - 20 * f.yH ∧ basShaded f.yH f.tH := by
  constructor
  · rintro ⟨hf, hne⟩
    obtain ⟨⟨h0L, h1L, h0H, h1H⟩, hICH, hICL, hIRL, hIRH, hIR2⟩ := hf
    simp only [BasSCF.ICH, BasSCF.ICL, BasSCF.IR1L, BasSCF.IR1H, BasSCF.IR2, BasSCF.U1L,
      BasSCF.U1H, BasSCF.U2] at hICH hICL hIRL hIRH hIR2
    -- Step 1: `y_L = 1`
    have hL : f.yL = 1 := by
      by_contra hne'
      have hlt : f.yL < 1 := lt_of_le_of_ne h1L hne'
      refine hne ⟨⟨1, f.tL + 30 * (1 - f.yL), f.yH, f.tH⟩, ?_, ?_⟩
      · refine ⟨⟨zero_le_one, le_rfl, h0H, h1H⟩, ?_, ?_, ?_, ?_, ?_⟩ <;>
          simp only [BasSCF.ICH, BasSCF.ICL, BasSCF.IR1L, BasSCF.IR1H, BasSCF.IR2, BasSCF.U1L,
            BasSCF.U1H, BasSCF.U2] <;> linarith
      · refine ⟨?_, ?_, ?_, Or.inl ?_⟩ <;>
          simp only [BasSCF.U1L, BasSCF.U1H, BasSCF.U2] <;> linarith
    -- Step 3: (IC_L) binds
    have hb : f.tL - 20 * f.yL = f.tH - 20 * f.yH := by
      by_contra hne'
      have hs : 0 < (f.tL - 20 * f.yL) - (f.tH - 20 * f.yH) := by
        rcases lt_or_eq_of_le (show f.tH - 20 * f.yH ≤ f.tL - 20 * f.yL by linarith) with h | h
        · linarith
        · exact absurd h.symm hne'
      set ε := ((f.tL - 20 * f.yL) - (f.tH - 20 * f.yH)) / 24 with hε
      have hε0 : 0 < ε := by rw [hε]; linarith
      refine hne ⟨⟨f.yL, f.tL + ε, f.yH + ε, f.tH + 45 * ε⟩, ?_, ?_⟩
      · refine ⟨⟨h0L, h1L, by dsimp only; linarith, by dsimp only; linarith⟩, ?_, ?_, ?_, ?_,
          ?_⟩ <;>
          simp only [BasSCF.ICH, BasSCF.ICL, BasSCF.IR1L, BasSCF.IR1H, BasSCF.IR2, BasSCF.U1L,
            BasSCF.U1H, BasSCF.U2] <;> linarith
      · refine ⟨?_, ?_, ?_, Or.inl ?_⟩ <;>
          simp only [BasSCF.U1L, BasSCF.U1H, BasSCF.U2] <;> linarith
    exact ⟨hL, by linarith, h0H, h1H, by linarith, by linarith⟩
  · rintro ⟨hL, htL, h0H, h1H, h2, h3⟩
    refine ⟨?_, ?_⟩
    · refine ⟨⟨by rw [hL]; norm_num, hL.le, h0H, h1H⟩, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp only [BasSCF.ICH, BasSCF.ICL, BasSCF.IR1L, BasSCF.IR1H, BasSCF.IR2, BasSCF.U1L,
          BasSCF.U1H, BasSCF.U2] <;> linarith
    · rintro ⟨g, ⟨⟨_, hg1, _, _⟩, _, hgICL, _⟩, hd1, hd2, hd3, hs⟩
      have hkg := bas_key g
      have hkf := bas_key f
      simp only [BasSCF.ICL] at hgICL
      rw [hL] at hkf
      rcases hs with hs | hs | hs <;> linarith

/-- **Example 23.F.3** (MWG, p. 909). Every interim incentive efficient social choice function
has `y_H ≤ 4/7`. -/
theorem bas_interimIE_yH_le {f : BasSCF} (hf : BasInterimEfficientIn basFStar f) :
    f.yH ≤ 4 / 7 :=
  bas_shaded_yH_le ((bas_interimIE_iff f).1 hf).2.2

/-- **Example 23.F.3** (MWG, pp. 907-908). Problem (23.F.17) characterises the interim
incentive efficient social choice functions: `f` is interim incentive efficient iff it solves
(23.F.17) for some `ū₁H ≥ 0` and `ū₂ ≥ 0`. -/
theorem bas_interimIE_iff_solves17 (f : BasSCF) :
    BasInterimEfficientIn basFStar f ↔
      ∃ u1H u2 : ℝ, 0 ≤ u1H ∧ 0 ≤ u2 ∧ BasSolves17 u1H u2 f := by
  rw [bas_interimIE_iff]
  constructor
  · rintro ⟨hL, htL, hs⟩
    obtain ⟨u1H, u2, h1, h2, h19⟩ := (bas_shaded_iff _ _).1 hs
    exact ⟨u1H, u2, h1, h2, (bas_solves17_iff h1 h2 f).2 ⟨hL, htL, h19⟩⟩
  · rintro ⟨u1H, u2, h1, h2, h17⟩
    obtain ⟨hL, htL, h19⟩ := (bas_solves17_iff h1 h2 f).1 h17
    exact ⟨hL, htL, (bas_shaded_iff _ _).2 ⟨u1H, u2, h1, h2, h19⟩⟩

/-- **Example 23.F.3** (MWG, p. 909). With `y_L = 1` and `t_L = 20 + t_H - 20 y_H`, the ex ante
expected utilities are `U₁ = 24 + t_H - 24 y_H` and `U₂ = 8 + 26 y_H - t_H`. -/
theorem bas_exAnte_utilities {f : BasSCF} (hL : f.yL = 1) (htL : f.tL = 20 + f.tH - 20 * f.yH) :
    f.U1 = 24 + f.tH - 24 * f.yH ∧ f.U2 = 8 + 26 * f.yH - f.tH := by
  simp only [BasSCF.U1, BasSCF.U1L, BasSCF.U1H, BasSCF.U2, hL, htL]
  constructor <;> ring

/-! ### Ex ante incentive efficiency -/

/-- The ex ante key identity: `14 U₁ + 16 U₂ = 464 - 128(1 - y_L) - (8/5)((t_L - 20 y_L) -
(t_H - 20 y_H)) - 2(t_H - 40 y_H)`. -/
theorem bas_key_exAnte (f : BasSCF) :
    14 * f.U1 + 16 * f.U2 = 464 - 128 * (1 - f.yL) -
      8 / 5 * ((f.tL - 20 * f.yL) - (f.tH - 20 * f.yH)) - 2 * (f.tH - 40 * f.yH) := by
  simp only [BasSCF.U1, BasSCF.U1L, BasSCF.U1H, BasSCF.U2]
  ring

/-- **Example 23.F.3** (MWG, pp. 909-910). The ex ante incentive efficient social choice functions
(Definition 23.F.1 with `F = F*`) are exactly those with `y_L = 1`, `t_L = 20 + t_H - 20 y_H`,
`t_H = 40 y_H` and `y_H ∈ [0, 4/7]`: the heavily traced segment of Figure 23.F.3. -/
theorem bas_exAnteIE_iff (f : BasSCF) :
    BasExAnteEfficientIn basFStar f ↔
      f.yL = 1 ∧ f.tL = 20 + f.tH - 20 * f.yH ∧ f.tH = 40 * f.yH ∧ 0 ≤ f.yH ∧ f.yH ≤ 4 / 7 := by
  constructor
  · rintro ⟨hf, hne⟩
    have hk := bas_key_exAnte f
    have hk' := bas_key f
    obtain ⟨⟨h0L, h1L, h0H, h1H⟩, hICH, hICL, hIRL, hIRH, hIR2⟩ := hf
    simp only [BasSCF.ICH, BasSCF.ICL, BasSCF.IR1L, BasSCF.IR1H, BasSCF.IR2, BasSCF.U1L,
      BasSCF.U1H] at hICH hICL hIRL hIRH hIR2
    simp only [BasSCF.U1L, BasSCF.U1H] at hk'
    have hU2 : f.U2 ≤ 8 := by linarith
    have heq : 14 * f.U1 + 16 * f.U2 = 464 := by
      by_contra hne'
      have hlt : 14 * f.U1 + 16 * f.U2 < 464 := lt_of_le_of_ne (by linarith) hne'
      set s := (8 - f.U2) / 14 with hs
      refine hne ⟨⟨1, 20 + 20 * s, s, 40 * s⟩, ?_, ?_⟩
      · refine ⟨⟨zero_le_one, le_rfl, by rw [hs]; linarith, by rw [hs]; linarith⟩, ?_, ?_, ?_, ?_,
          ?_⟩ <;>
          simp only [BasSCF.ICH, BasSCF.ICL, BasSCF.IR1L, BasSCF.IR1H, BasSCF.IR2, BasSCF.U1L,
            BasSCF.U1H, BasSCF.U2] <;> rw [hs] <;> linarith
      · have e1 : (⟨1, 20 + 20 * s, s, 40 * s⟩ : BasSCF).U1 = 24 + 16 * s := by
          simp only [BasSCF.U1, BasSCF.U1L, BasSCF.U1H]; ring
        have e2 : (⟨1, 20 + 20 * s, s, 40 * s⟩ : BasSCF).U2 = 8 - 14 * s := by
          simp only [BasSCF.U2]; ring
        rw [basExAnteDominates, e1, e2, hs]
        refine ⟨by linarith, by linarith, Or.inl (by linarith)⟩
    have hL : f.yL = 1 := by linarith
    have hb : f.tH = 40 * f.yH := by linarith
    have hc : f.tL = 20 + f.tH - 20 * f.yH := by linarith
    refine ⟨hL, hc, hb, h0H, ?_⟩
    simp only [BasSCF.U2] at hIR2
    rw [hL, hc, hb] at hIR2
    linarith
  · rintro ⟨hL, htL, hb, h0H, h1H⟩
    refine ⟨(bas_interimIE_iff f).2 ⟨hL, htL, h0H, by linarith, hb.ge, by linarith⟩ |>.1, ?_⟩
    rintro ⟨g, ⟨⟨_, hg1, _, _⟩, _, hgICL, _, hgIRH, _⟩, hd1, hd2, hs⟩
    have hkg := bas_key_exAnte g
    have hkf := bas_key_exAnte f
    simp only [BasSCF.ICL] at hgICL
    simp only [BasSCF.IR1H, BasSCF.U1H] at hgIRH
    rw [hL, htL, hb] at hkf
    rcases hs with hs | hs <;> linarith

/-- **Example 23.F.3** (MWG, p. 909). Every ex ante incentive efficient social choice function is
interim incentive efficient. -/
theorem bas_interimIE_of_exAnteIE {f : BasSCF} (hf : BasExAnteEfficientIn basFStar f) :
    BasInterimEfficientIn basFStar f := by
  obtain ⟨hL, htL, hb, h0, h1⟩ := (bas_exAnteIE_iff f).1 hf
  exact (bas_interimIE_iff f).2 ⟨hL, htL, h0, by linarith, hb.ge, by linarith⟩

/-- **Example 23.F.3** (MWG, p. 910). In every ex ante incentive efficient social choice function
the high-quality seller's interim IR constraint binds: he receives no gains from trade,
`U₁(θ_H) = 40`. -/
theorem bas_exAnteIE_IR1H_binds {f : BasSCF} (hf : BasExAnteEfficientIn basFStar f) :
    f.U1H = 40 := by
  obtain ⟨-, -, hb, -, -⟩ := (bas_exAnteIE_iff f).1 hf
  simp only [BasSCF.U1H, hb]
  ring

/-- **Footnote 54** (MWG, p. 910). In any ex ante incentive efficient social choice function
`y_H ≤ 4/7 < 1`. -/
theorem footnote_23_54 {f : BasSCF} (hf : BasExAnteEfficientIn basFStar f) :
    f.yH ≤ 4 / 7 ∧ (4 / 7 : ℝ) < 1 :=
  ⟨((bas_exAnteIE_iff f).1 hf).2.2.2.2, by norm_num⟩

/-- **Example 23.F.3** (MWG, pp. 909-910). Non-vacuity: the interim and the ex ante incentive
efficient sets are nonempty, and the first is strictly larger (`(1, 28, 0, 8)` is interim but not
ex ante incentive efficient; `(1, 20 + 80/7, 4/7, 160/7)` is ex ante incentive efficient). -/
theorem bas_nonvacuous :
    BasExAnteEfficientIn basFStar ⟨1, 20 + 80 / 7, 4 / 7, 160 / 7⟩ ∧
      BasInterimEfficientIn basFStar ⟨1, 28, 0, 8⟩ ∧
      ¬ BasExAnteEfficientIn basFStar ⟨1, 28, 0, 8⟩ := by
  refine ⟨(bas_exAnteIE_iff _).2 ⟨rfl, by norm_num, by norm_num, by norm_num, by norm_num⟩,
    (bas_interimIE_iff _).2 ⟨rfl, by norm_num, by norm_num, by norm_num, by norm_num,
      by norm_num⟩, fun h => ?_⟩
  have := ((bas_exAnteIE_iff _).1 h).2.2.1
  norm_num at this

/-! ### Exercise 23.F.10: no participation constraint for the seller -/

/-- **Exercise 23.F.10** (MWG, p. 924), interim part. When trade is not voluntary for the seller
(but is for the buyer), the interim incentive efficient social choice functions are exactly those
with `y_L = 1`, `t_L = 20 + t_H - 20 y_H`, `y_H ∈ [0, 1]` and `t_H ≤ 26 y_H + 8`. -/
theorem exercise_23_F_10_interim (f : BasSCF) :
    BasInterimEfficientIn basFBuyerIR f ↔
      f.yL = 1 ∧ f.tL = 20 + f.tH - 20 * f.yH ∧ 0 ≤ f.yH ∧ f.yH ≤ 1 ∧ f.tH ≤ 26 * f.yH + 8 := by
  constructor
  · rintro ⟨hf, hne⟩
    obtain ⟨⟨h0L, h1L, h0H, h1H⟩, hICH, hICL, hIR2⟩ := hf
    simp only [BasSCF.ICH, BasSCF.ICL, BasSCF.IR2, BasSCF.U2] at hICH hICL hIR2
    have hL : f.yL = 1 := by
      by_contra hne'
      have hlt : f.yL < 1 := lt_of_le_of_ne h1L hne'
      refine hne ⟨⟨1, f.tL + 30 * (1 - f.yL), f.yH, f.tH⟩, ?_, ?_⟩
      · refine ⟨⟨zero_le_one, le_rfl, h0H, h1H⟩, ?_, ?_, ?_⟩ <;>
          simp only [BasSCF.ICH, BasSCF.ICL, BasSCF.IR2, BasSCF.U2] <;> linarith
      · refine ⟨?_, ?_, ?_, Or.inl ?_⟩ <;>
          simp only [BasSCF.U1L, BasSCF.U1H, BasSCF.U2] <;> linarith
    have hb : f.tL - 20 * f.yL = f.tH - 20 * f.yH := by
      by_contra hne'
      have hs : 0 < (f.tL - 20 * f.yL) - (f.tH - 20 * f.yH) := by
        rcases lt_or_eq_of_le (show f.tH - 20 * f.yH ≤ f.tL - 20 * f.yL by linarith) with h | h
        · linarith
        · exact absurd h.symm hne'
      set ε := ((f.tL - 20 * f.yL) - (f.tH - 20 * f.yH)) / 24 with hε
      have hε0 : 0 < ε := by rw [hε]; linarith
      refine hne ⟨⟨f.yL, f.tL + ε, f.yH + ε, f.tH + 45 * ε⟩, ?_, ?_⟩
      · refine ⟨⟨h0L, h1L, by dsimp only; linarith, by dsimp only; linarith⟩, ?_, ?_, ?_⟩ <;>
          simp only [BasSCF.ICH, BasSCF.ICL, BasSCF.IR2, BasSCF.U2] <;> linarith
      · refine ⟨?_, ?_, ?_, Or.inl ?_⟩ <;>
          simp only [BasSCF.U1L, BasSCF.U1H, BasSCF.U2] <;> linarith
    exact ⟨hL, by linarith, h0H, h1H, by linarith⟩
  · rintro ⟨hL, htL, h0H, h1H, h3⟩
    refine ⟨?_, ?_⟩
    · refine ⟨⟨by rw [hL]; norm_num, hL.le, h0H, h1H⟩, ?_, ?_, ?_⟩ <;>
        simp only [BasSCF.ICH, BasSCF.ICL, BasSCF.IR2, BasSCF.U2] <;> linarith
    · rintro ⟨g, ⟨⟨_, hg1, _, _⟩, _, hgICL, _⟩, hd1, hd2, hd3, hs⟩
      have hkg := bas_key g
      have hkf := bas_key f
      simp only [BasSCF.ICL] at hgICL
      rw [hL] at hkf
      rcases hs with hs | hs | hs <;> linarith

/-- **Exercise 23.F.10** (MWG, p. 924), ex ante part. When trade is not voluntary for the seller
(but is for the buyer), the ex ante incentive efficient social choice functions are exactly those
with `y_L = y_H = 1` and `t_L = t_H ≤ 34`; all of them are ex post efficient (compare
footnote 54 and Section 13.B). -/
theorem exercise_23_F_10_exAnte (f : BasSCF) :
    BasExAnteEfficientIn basFBuyerIR f ↔ f.yL = 1 ∧ f.yH = 1 ∧ f.tL = f.tH ∧ f.tH ≤ 34 := by
  have hsum : ∀ g : BasSCF, g.U1 + g.U2 = 24 + 2 * g.yH + 8 * g.yL := by
    intro g
    simp only [BasSCF.U1, BasSCF.U1L, BasSCF.U1H, BasSCF.U2]
    ring
  constructor
  · rintro ⟨hf, hne⟩
    obtain ⟨⟨h0L, h1L, h0H, h1H⟩, hICH, hICL, hIR2⟩ := hf
    have heq : f.U1 + f.U2 = 34 := by
      by_contra hne'
      have hlt : f.U1 + f.U2 < 34 := lt_of_le_of_ne (by rw [hsum f]; linarith) hne'
      refine hne ⟨⟨1, 34 - f.U2, 1, 34 - f.U2⟩, ?_, ?_⟩
      · simp only [BasSCF.IR2] at hIR2
        refine ⟨⟨zero_le_one, le_rfl, zero_le_one, le_rfl⟩, ?_, ?_, ?_⟩ <;>
          simp only [BasSCF.ICH, BasSCF.ICL, BasSCF.IR2, BasSCF.U2] <;>
          simp only [BasSCF.U2] at hIR2 <;> linarith
      · have h1 : (⟨1, 34 - f.U2, 1, 34 - f.U2⟩ : BasSCF).U1 = 34 - f.U2 := by
          simp only [BasSCF.U1, BasSCF.U1L, BasSCF.U1H]; ring
        have h2 : (⟨1, 34 - f.U2, 1, 34 - f.U2⟩ : BasSCF).U2 = f.U2 := by
          simp only [BasSCF.U2]; ring
        rw [basExAnteDominates, h1, h2]
        exact ⟨by linarith, le_rfl, Or.inl (by linarith)⟩
    rw [hsum f] at heq
    have hL : f.yL = 1 := by linarith
    have hH : f.yH = 1 := by linarith
    simp only [BasSCF.ICH, BasSCF.ICL, BasSCF.IR2, BasSCF.U2, hL, hH] at hICH hICL hIR2
    exact ⟨hL, hH, by linarith, by linarith⟩
  · rintro ⟨hL, hH, ht, h34⟩
    refine ⟨⟨⟨by rw [hL]; norm_num, hL.le, by rw [hH]; norm_num, hH.le⟩, ?_, ?_, ?_⟩, ?_⟩
    · simp only [BasSCF.ICH, hL, hH, ht]; linarith
    · simp only [BasSCF.ICL, hL, hH, ht]; linarith
    · simp only [BasSCF.IR2, BasSCF.U2, hL, hH, ht]; linarith
    · rintro ⟨g, ⟨⟨_, hg1, _, hg2⟩, -⟩, hd1, hd2, hs⟩
      have hg := hsum g
      have hf := hsum f
      rw [hL, hH] at hf
      rcases hs with hs | hs <;> linarith

/-- **Exercise 23.F.10** (MWG, p. 924). Without the seller's participation constraints, ex ante
incentive efficiency still implies interim incentive efficiency, and the interim incentive
efficient set strictly contains the one under `F*`'s constraints (e.g. `(1, 30, 1, 30)` is interim
incentive efficient in the larger set). -/
theorem exercise_23_F_10_compare :
    (∀ f, BasExAnteEfficientIn basFBuyerIR f → BasInterimEfficientIn basFBuyerIR f) ∧
      BasInterimEfficientIn basFBuyerIR ⟨1, 30, 1, 30⟩ ∧
      ¬ BasInterimEfficientIn basFStar ⟨1, 30, 1, 30⟩ := by
  refine ⟨fun f hf => ?_, (exercise_23_F_10_interim _).2 ⟨rfl, by norm_num, by norm_num,
    by norm_num, by norm_num⟩, fun h => ?_⟩
  · obtain ⟨hL, hH, ht, h34⟩ := (exercise_23_F_10_exAnte f).1 hf
    exact (exercise_23_F_10_interim f).2 ⟨hL, by rw [hH, ht]; ring, by rw [hH]; norm_num,
      hH.le, by rw [hH]; linarith⟩
  · have := ((bas_interimIE_iff _).1 h).2.2
    simp only [basShaded] at this
    norm_num at this

end MWG.MechanismDesign
