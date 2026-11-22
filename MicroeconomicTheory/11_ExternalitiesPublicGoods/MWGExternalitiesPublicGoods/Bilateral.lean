/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGExternalitiesPublicGoods.Tools
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# A simple bilateral externality (MWG Section 11.B)

MWG, pp. 351-359.

* **Definition 11.B.1** (`HasExternality`) and footnote 2 (positive and negative externalities).
* The derived utility `vᵢ(p, wᵢ, h)` and **footnote 3** (p. 353): with utility `g(x₋₁, h) + x₁`
  the derived utility is `φ(p, h) + w` (`footnote_3`). We keep MWG's nonnegativity of all goods
  and assume wealth covers the optimal purchases of the non-numeraire goods.
* The model (`Bilateral`): `φ₁, φ₂` differentiable with strictly decreasing derivatives on
  `[0, ∞)` (implied by MWG's `φᵢ'' < 0`, `strictAntiOn_of_second_deriv_neg`).
* (11.B.1) and (11.B.2) (`eq_11_B_1`, `eq_11_B_2`), **footnote 4** (`footnote_4`: Pareto
  optimality iff the joint surplus is maximized), the nonoptimality of the equilibrium
  (`eq_ne_opt`, `negative_externality_excess`, `positive_externality_shortfall`).
* Quotas, the Pigouvian tax (11.B.3)-(11.B.4) (`pigou_tax`, `pigou_tax_unique`), footnote 5,
  subsidies for reduction (`subsidy_equiv_tax`).
* Bargaining with enforceable property rights, (11.B.5), the Coase theorem (`coase_theorem`),
  the payments on p. 357 and Figure 11.B.3.
* Missing markets: (11.B.6)-(11.B.7), the competitive rights market reaches `h°` with
  `p_h* = φ₁'(h°) = -φ₂'(h°)`.
-/

namespace MWG.ExternalitiesPublicGoods

open MWG.CompetitiveMarkets

/-! ## Definition 11.B.1 and footnotes 2-3 -/

/-- **Definition 11.B.1** (MWG, p. 352). An externality is present when an agent's well-being
`u(x, h)` depends directly on an action `h` chosen by another agent: for some own choice `x` the
utility changes with `h`. -/
def HasExternality {Y A : Type*} (u : Y → A → ℝ) : Prop :=
  ∃ x h h', u x h ≠ u x h'

/-- **Definition 11.B.1** (MWG, p. 352), unfolded. -/
theorem definition_11_B_1 {Y A : Type*} (u : Y → A → ℝ) :
    HasExternality u ↔ ∃ x h h', u x h ≠ u x h' := Iff.rfl

/-- **Footnote 2** (MWG, p. 352). A positive externality: well-being increases with `h`. -/
def PositiveExternality {Y : Type*} (u : Y → ℝ → ℝ) : Prop := ∀ x, StrictMono (u x)

/-- **Footnote 2** (MWG, p. 352). A negative externality: well-being decreases with `h`. -/
def NegativeExternality {Y : Type*} (u : Y → ℝ → ℝ) : Prop := ∀ x, StrictAnti (u x)

/-- MWG's condition `∂u₂/∂h ≠ 0` (p. 352) makes `h` an externality in the sense of
Definition 11.B.1. -/
theorem hasExternality_of_deriv_ne {Y : Type*} [Nonempty Y] (u : Y → ℝ → ℝ) (u' : Y → ℝ → ℝ)
    (hu : ∀ x h, HasDerivAt (u x) (u' x h) h) (hne : ∀ x h, u' x h ≠ 0) :
    HasExternality u := by
  obtain ⟨x⟩ := ‹Nonempty Y›
  by_contra hno
  have hconst : ∀ h h', u x h = u x h' := fun h h' => by
    by_contra hne'
    exact hno ⟨x, h, h', hne'⟩
  have hd : HasDerivAt (u x) 0 0 := by
    have : u x = fun _ => u x 0 := funext fun h => hconst h 0
    rw [this]
    exact hasDerivAt_const _ _
  exact hne x 0 ((hu x 0).unique hd)

/-- A positive (or negative) externality is an externality. -/
theorem PositiveExternality.hasExternality {Y : Type*} [Nonempty Y] {u : Y → ℝ → ℝ}
    (h : PositiveExternality u) : HasExternality u := by
  obtain ⟨x⟩ := ‹Nonempty Y›
  exact ⟨x, 0, 1, (h x zero_lt_one).ne⟩

/-- A negative externality is an externality. -/
theorem NegativeExternality.hasExternality {Y : Type*} [Nonempty Y] {u : Y → ℝ → ℝ}
    (h : NegativeExternality u) : HasExternality u := by
  obtain ⟨x⟩ := ‹Nonempty Y›
  exact ⟨x, 0, 1, (h x zero_lt_one).ne'⟩

/-- **Footnote 3** (MWG, p. 353). With utility `g(x₋₁, h) + x₁` (good `1` the numeraire, price
`1`) and prices `p` for the other goods, suppose `y*` maximizes `g(y, h) - p·y` over `y ≥ 0` and
wealth covers it (`p·y* ≤ w`). Then the maximal utility over the budget set
`{x₁ ≥ 0, y ≥ 0, x₁ + p·y ≤ w}` is `φ(p, h) + w`, where `φ(p, h) = g(y*, h) - p·y*`, attained at
`(w - p·y*, y*)`: derived utility is quasilinear in wealth. -/
theorem footnote_3 {n : ℕ} (g : (Fin n → ℝ) → ℝ → ℝ) (p : Fin n → ℝ) (w h : ℝ)
    (ys : Fin n → ℝ)
    (hmax : ∀ y : Fin n → ℝ, (∀ l, 0 ≤ y l) → g y h - ∑ l, p l * y l ≤ g ys h - ∑ l, p l * ys l)
    (hw : ∑ l, p l * ys l ≤ w) :
    (0 ≤ w - ∑ l, p l * ys l ∧ (w - ∑ l, p l * ys l) + ∑ l, p l * ys l ≤ w) ∧
      g ys h + (w - ∑ l, p l * ys l) = (g ys h - ∑ l, p l * ys l) + w ∧
      ∀ (x₁ : ℝ) (y : Fin n → ℝ), 0 ≤ x₁ → (∀ l, 0 ≤ y l) → x₁ + ∑ l, p l * y l ≤ w →
        g y h + x₁ ≤ (g ys h - ∑ l, p l * ys l) + w := by
  refine ⟨⟨by linarith, by linarith⟩, by ring, fun x₁ y _ hy hb => ?_⟩
  have := hmax y hy
  linarith

/-! ## The model -/

/-- **The bilateral externality model** (MWG, pp. 352-353). Derived utilities `φᵢ(h) + wᵢ`;
`φᵢ` is differentiable with derivative `dᵢ`, strictly decreasing on `[0, ∞)` (MWG: `φᵢ'' < 0`). -/
structure Bilateral where
  /-- Consumer 1's derived utility from `h` (she chooses `h`). -/
  φ₁ : ℝ → ℝ
  /-- Consumer 2's derived utility from `h`. -/
  φ₂ : ℝ → ℝ
  /-- `φ₁'`. -/
  d₁ : ℝ → ℝ
  /-- `φ₂'`. -/
  d₂ : ℝ → ℝ
  hd₁ : ∀ h, HasDerivAt φ₁ (d₁ h) h
  hd₂ : ∀ h, HasDerivAt φ₂ (d₂ h) h
  anti₁ : StrictAntiOn d₁ (Set.Ici 0)
  anti₂ : StrictAntiOn d₂ (Set.Ici 0)

namespace Bilateral

variable (M : Bilateral)

/-- The joint surplus `φ₁ + φ₂`. -/
def joint (h : ℝ) : ℝ := M.φ₁ h + M.φ₂ h

theorem hasDerivAt_joint (h : ℝ) : HasDerivAt M.joint (M.d₁ h + M.d₂ h) h :=
  (M.hd₁ h).add (M.hd₂ h)

theorem anti_joint : StrictAntiOn (fun h => M.d₁ h + M.d₂ h) (Set.Ici 0) :=
  fun _ ha _ hb hab => add_lt_add (M.anti₁ ha hb hab) (M.anti₂ ha hb hab)

/-- The competitive equilibrium level `h*`: consumer 1 maximizes `φ₁` on `ℝ₊`. -/
def IsEqLevel (h : ℝ) : Prop := 0 ≤ h ∧ ∀ y, 0 ≤ y → M.φ₁ y ≤ M.φ₁ h

/-- The Pareto optimal level `h°`: it maximizes the joint surplus on `ℝ₊`. -/
def IsOptLevel (h : ℝ) : Prop := 0 ≤ h ∧ ∀ y, 0 ≤ y → M.joint y ≤ M.joint h

/-- **(11.B.1)** (MWG, p. 353). `h*` is the equilibrium level iff `φ₁'(h*) ≤ 0`, with equality if
`h* > 0`. -/
theorem eq_11_B_1 (h : ℝ) : M.IsEqLevel h ↔ IsFOCSol M.d₁ 0 h :=
  kt_isMax_iff M.hd₁ M.anti₁.antitoneOn

/-- **(11.B.2)** (MWG, p. 353). `h°` is optimal iff `φ₁'(h°) ≤ -φ₂'(h°)`, with equality if
`h° > 0`. -/
theorem eq_11_B_2 (h : ℝ) :
    M.IsOptLevel h ↔ 0 ≤ h ∧ M.d₁ h ≤ -M.d₂ h ∧ (0 < h → M.d₁ h = -M.d₂ h) := by
  rw [IsOptLevel, kt_isMax_iff M.hasDerivAt_joint M.anti_joint.antitoneOn]
  simp only [IsFOCSol]
  constructor
  · rintro ⟨h0, h1, h2⟩
    exact ⟨h0, by linarith, fun hp => by linarith [h2 hp]⟩
  · rintro ⟨h0, h1, h2⟩
    exact ⟨h0, by linarith, fun hp => by linarith [h2 hp]⟩

/-- **Footnote 4** (MWG, p. 353). An allocation `(h, m₁, m₂)` with `m₁ + m₂ = w₁ + w₂` (utilities
`φᵢ(h) + mᵢ`) is Pareto optimal iff `h` is an optimal level. -/
theorem footnote_4 (w : ℝ) (a : QLAlloc (Fin 2) ℝ)
    (ha : QLFeasible (Set.Ici 0) (fun _ => 0) w a) :
    QLPareto (fun i => if i = 0 then M.φ₁ else M.φ₂) (Set.Ici 0) (fun _ => 0) w a ↔
      M.IsOptLevel a.x := by
  rw [ql_pareto_iff _ _ _ _ a ha]
  simp only [qlSurplus', Fin.sum_univ_two, Fin.isValue, ↓reduceIte, one_ne_zero, sub_zero,
    Set.mem_Ici]
  exact ⟨fun h => ⟨ha.1, fun y hy => h y hy⟩, fun h y hy => h.2 y hy⟩

/-- With external effects (`φ₂'(h) ≠ 0` at all `h`), **the equilibrium level is not optimal unless
`h° = h* = 0`** (MWG, p. 353). -/
theorem eq_ne_opt (hne : ∀ h, M.d₂ h ≠ 0) {h : ℝ} (he : M.IsEqLevel h) (ho : M.IsOptLevel h) :
    h = 0 := by
  rw [eq_11_B_1] at he
  rw [eq_11_B_2] at ho
  rcases eq_or_lt_of_le he.1 with h0 | hpos
  · exact h0.symm
  · exfalso
    have h1 := he.2.2 hpos
    have h2 := ho.2.2 hpos
    exact hne h (by linarith)

/-- **Negative externality: too much `h`** (MWG, p. 354). If `φ₂' < 0`, then `h° ≤ h*`, and
`h° < h*` whenever `h* > 0` (in particular for interior `(h*, h°) ≫ 0`). -/
theorem negative_externality_excess (hneg : ∀ h, 0 ≤ h → M.d₂ h < 0) {hs ho : ℝ}
    (he : M.IsEqLevel hs) (hopt : M.IsOptLevel ho) : ho ≤ hs ∧ (0 < hs → ho < hs) := by
  rw [eq_11_B_1] at he
  rw [eq_11_B_2] at hopt
  have key : ¬ hs < ho := fun hlt => by
    have e2 := hopt.2.2 (he.1.trans_lt hlt)
    have := M.anti₁ he.1 hopt.1 hlt
    have := hneg ho hopt.1
    linarith [he.2.1]
  refine ⟨not_lt.1 key, fun hpos => lt_of_le_of_ne (not_lt.1 key) fun heq => ?_⟩
  have e1 := he.2.2 hpos
  have e2 := hopt.2.2 (heq ▸ hpos)
  rw [heq] at e2
  have := hneg hs he.1
  linarith

/-- **Positive externality: too little `h`** (MWG, p. 354). If `φ₂' > 0`, then `h* ≤ h°`, and
`h* < h°` whenever `h° > 0`. -/
theorem positive_externality_shortfall (hpos : ∀ h, 0 ≤ h → 0 < M.d₂ h) {hs ho : ℝ}
    (he : M.IsEqLevel hs) (hopt : M.IsOptLevel ho) : hs ≤ ho ∧ (0 < ho → hs < ho) := by
  rw [eq_11_B_1] at he
  rw [eq_11_B_2] at hopt
  have key : ¬ ho < hs := fun hlt => by
    have e1 := he.2.2 (hopt.1.trans_lt hlt)
    have := M.anti₁ hopt.1 he.1 hlt
    have := hpos ho hopt.1
    linarith [hopt.2.1]
  refine ⟨not_lt.1 key, fun hp => lt_of_le_of_ne (not_lt.1 key) fun heq => ?_⟩
  have e2 := hopt.2.2 hp
  have e1 := he.2.2 (heq ▸ hp)
  rw [← heq] at e2
  have := hpos hs he.1
  linarith

/-- **Small type, p. 354.** With quasilinear utilities the optimal level does not depend on the
consumers' wealths: for any wealths, Pareto optimal allocations (footnote 4) have `h` optimal. -/
theorem opt_indep_wealth (w w' : ℝ) (a : QLAlloc (Fin 2) ℝ)
    (ha : QLFeasible (Set.Ici 0) (fun _ => 0) w a) (b : QLAlloc (Fin 2) ℝ)
    (hb : QLFeasible (Set.Ici 0) (fun _ => 0) w' b) (hab : a.x = b.x) :
    QLPareto (fun i => if i = 0 then M.φ₁ else M.φ₂) (Set.Ici 0) (fun _ => 0) w a ↔
      QLPareto (fun i => if i = 0 then M.φ₁ else M.φ₂) (Set.Ici 0) (fun _ => 0) w' b := by
  rw [M.footnote_4 w a ha, M.footnote_4 w' b hb, hab]

/-! ## Quotas and Pigouvian taxes -/

/-- **Quota** (MWG, p. 354). With a negative externality (`h° < h*`), a quota `h ≤ h°` leads
consumer 1 to choose exactly `h°`: it is her unique best choice in `[0, h°]`. -/
theorem quota_implements {hs ho : ℝ} (he : M.IsEqLevel hs) (hopt : M.IsOptLevel ho)
    (hlt : ho ≤ hs) : ∀ y, 0 ≤ y → y ≤ ho → y ≠ ho → M.φ₁ y < M.φ₁ ho := by
  rw [eq_11_B_1] at he
  intro y hy hyo hne
  exact kt_strictMonoOn M.hd₁ M.anti₁ he ⟨hy, hyo.trans hlt⟩ ⟨hopt.1, hlt⟩
    (lt_of_le_of_ne hyo hne)

/-- Consumer 1's problem under a per-unit tax `t` (11.B.3): `max_{h ≥ 0} φ₁(h) - t h`. -/
def IsTaxChoice (t h : ℝ) : Prop := 0 ≤ h ∧ ∀ y, 0 ≤ y → M.φ₁ y - t * y ≤ M.φ₁ h - t * h

/-- **(11.B.4)** (MWG, p. 355). `h` solves (11.B.3) iff `φ₁'(h) ≤ t`, with equality if `h > 0`. -/
theorem eq_11_B_4 (t h : ℝ) : M.IsTaxChoice t h ↔ IsFOCSol M.d₁ t h := by
  have hf : ∀ x, HasDerivAt (fun h => M.φ₁ h - t * h) (M.d₁ x - t) x := fun x => by
    have h2 : HasDerivAt (fun y => t * y) t x := by simpa using (hasDerivAt_id x).const_mul t
    exact (M.hd₁ x).sub h2
  have hanti : AntitoneOn (fun x => M.d₁ x - t) (Set.Ici 0) :=
    fun a ha b hb hab => by simpa using M.anti₁.antitoneOn ha hb hab
  rw [IsTaxChoice, kt_isMax_iff hf hanti]
  simp only [IsFOCSol]
  constructor
  · rintro ⟨h0, h1, h2⟩
    exact ⟨h0, by linarith, fun hp => by linarith [h2 hp]⟩
  · rintro ⟨h0, h1, h2⟩
    exact ⟨h0, by linarith, fun hp => by linarith [h2 hp]⟩

/-- **The Pigouvian tax** (MWG, p. 355). The tax `t_h = -φ₂'(h°)` makes `h°` a solution of
(11.B.3). -/
theorem pigou_tax {ho : ℝ} (hopt : M.IsOptLevel ho) : M.IsTaxChoice (-M.d₂ ho) ho := by
  rw [eq_11_B_4]
  rw [eq_11_B_2] at hopt
  exact hopt

/-- **The Pigouvian tax implements `h°` uniquely** (MWG, p. 355: given `φ₁'' < 0`, `h°` is the
unique solution of (11.B.3)). -/
theorem pigou_tax_unique {ho h : ℝ} (hopt : M.IsOptLevel ho) (hh : M.IsTaxChoice (-M.d₂ ho) h) :
    h = ho := by
  rw [eq_11_B_4] at hh
  exact isFOCSol_unique M.anti₁ hh ((M.eq_11_B_4 _ _).1 (M.pigou_tax hopt))

/-- With a negative externality the Pigouvian tax is positive, with a positive externality it
is a subsidy (MWG, p. 355). -/
theorem pigou_tax_sign (ho : ℝ) : (M.d₂ ho < 0 → 0 < -M.d₂ ho) ∧ (0 < M.d₂ ho → -M.d₂ ho < 0) :=
  ⟨fun h => by linarith, fun h => by linarith⟩

/-- **Footnote 5** (MWG, p. 355). If `h° = 0`, any tax `t > -φ₂'(0)` (indeed `t ≥ -φ₂'(0)`) also
implements the optimal outcome, uniquely. -/
theorem footnote_5 (hopt : M.IsOptLevel 0) {t : ℝ} (ht : -M.d₂ 0 ≤ t) :
    M.IsTaxChoice t 0 ∧ ∀ h, M.IsTaxChoice t h → h = 0 := by
  rw [eq_11_B_2] at hopt
  have h0 : IsFOCSol M.d₁ t 0 := ⟨le_rfl, by linarith [hopt.2.1], fun h => absurd h (lt_irrefl 0)⟩
  refine ⟨(M.eq_11_B_4 t 0).2 h0, fun h hh => ?_⟩
  exact isFOCSol_unique M.anti₁ ((M.eq_11_B_4 t h).1 hh) h0

/-- **Subsidizing reductions** (MWG, p. 355). Paying `s_h = t` per unit of `h` below `h*` gives
consumer 1 the objective `φ₁(h) + t(h* - h) = (φ₁(h) - t h) + t h*`, so her choices coincide with
those under the tax `t` (a lump-sum transfer `t h*` aside). -/
theorem subsidy_equiv_tax (t hs h : ℝ) :
    (0 ≤ h ∧ ∀ y, 0 ≤ y → M.φ₁ y + t * (hs - y) ≤ M.φ₁ h + t * (hs - h)) ↔ M.IsTaxChoice t h := by
  constructor
  · rintro ⟨h0, hh⟩
    exact ⟨h0, fun y hy => by linarith [hh y hy]⟩
  · rintro ⟨h0, hh⟩
    exact ⟨h0, fun y hy => by linarith [hh y hy]⟩

/-- The tax and the quota achieve the same outcome `h°` (MWG, p. 356): with a negative
externality, the quota choice and the Pigouvian tax choice are both `h°`. -/
theorem tax_quota_equivalent {hs ho : ℝ} (he : M.IsEqLevel hs) (hopt : M.IsOptLevel ho)
    (hle : ho ≤ hs) :
    M.IsTaxChoice (-M.d₂ ho) ho ∧ ∀ y, 0 ≤ y → y ≤ ho → M.φ₁ y ≤ M.φ₁ ho := by
  refine ⟨M.pigou_tax hopt, fun y hy hyo => ?_⟩
  rcases eq_or_ne y ho with h | h
  · rw [h]
  · exact (M.quota_implements he hopt hle y hy hyo h).le

/-! ## Bargaining over externalities; the Coase theorem -/

/-- Consumer 2 holds the right to an externality-free environment and makes a take-it-or-leave-it
offer `(h, T)` (MWG, p. 356): `max φ₂(h) + T` s.t. `φ₁(h) - T ≥ φ₁(0)`. -/
def IsOffer2Free (h T : ℝ) : Prop := IsTIOLIOffer (Set.Ici 0) M.φ₂ M.φ₁ (M.φ₁ 0) h T

/-- Consumer 1 holds the right to generate the externality (`h*` absent agreement), and
consumer 2 makes the offer (MWG, p. 357): `max φ₂(h) + T` s.t. `φ₁(h) - T ≥ φ₁(h*)`. -/
def IsOffer2Right (hs h T : ℝ) : Prop := IsTIOLIOffer (Set.Ici 0) M.φ₂ M.φ₁ (M.φ₁ hs) h T

theorem joint_comm' (h : ℝ) : M.φ₂ h + M.φ₁ h = M.joint h := add_comm _ _

/-- **(11.B.5)** (MWG, p. 356). Consumer 2's optimal offer has `T = φ₁(h) - φ₁(0)` and `h`
maximizing `φ₂(h) + φ₁(h) - φ₁(0)`: `h = h°`, the socially optimal level. -/
theorem eq_11_B_5 (h T : ℝ) : M.IsOffer2Free h T ↔ M.IsOptLevel h ∧ T = M.φ₁ h - M.φ₁ 0 := by
  rw [IsOffer2Free, tioli_iff]
  simp only [Set.mem_Ici, joint_comm', IsOptLevel]
  exact ⟨fun ⟨a, b, c⟩ => ⟨⟨a, b⟩, c⟩, fun ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩⟩

/-- **The Coase theorem** (MWG, p. 357). Whichever consumer holds the property right, consumer 2's
take-it-or-leave-it offer sets `h = h°`: the allocation of rights affects only the payment. -/
theorem coase_theorem (hs h T : ℝ) :
    (M.IsOffer2Free h T ↔ M.IsOptLevel h ∧ T = M.φ₁ h - M.φ₁ 0) ∧
      (M.IsOffer2Right hs h T ↔ M.IsOptLevel h ∧ T = M.φ₁ h - M.φ₁ hs) := by
  refine ⟨M.eq_11_B_5 h T, ?_⟩
  rw [IsOffer2Right, tioli_iff]
  simp only [Set.mem_Ici, joint_comm', IsOptLevel]
  exact ⟨fun ⟨a, b, c⟩ => ⟨⟨a, b⟩, c⟩, fun ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩⟩

/-- **The payments** (MWG, p. 357), for a negative externality with `0 < h° < h*`: with the right
to an externality-free environment, consumer 1 pays `φ₁(h°) - φ₁(0) > 0`; with the right to
pollute, she "pays" `φ₁(h°) - φ₁(h*) < 0`. -/
theorem coase_payments {hs ho : ℝ} (he : M.IsEqLevel hs) (hopt : M.IsOptLevel ho)
    (hpos : 0 < ho) (hlt : ho < hs) :
    0 < M.φ₁ ho - M.φ₁ 0 ∧ M.φ₁ ho - M.φ₁ hs < 0 := by
  rw [eq_11_B_1] at he
  constructor
  · have := kt_strictMonoOn M.hd₁ M.anti₁ he ⟨le_rfl, he.1⟩ ⟨hopt.1, hlt.le⟩ hpos
    linarith
  · have := kt_strict_max M.hd₁ M.anti₁ he hopt.1 hlt.ne
    linarith

/-- Consumer 1 makes the take-it-or-leave-it offer instead (points `d` and `c` of Figure 11.B.3):
from disagreement point `h_d`, she offers `(h, T')` (payment `T'` to consumer 2) solving
`max φ₁(h) - T'` s.t. `φ₂(h) + T' ≥ φ₂(h_d)`; again `h = h°`. -/
theorem offer1_iff (hd h T' : ℝ) :
    IsTIOLIOffer (Set.Ici 0) M.φ₁ M.φ₂ (M.φ₂ hd) h (-T') ↔
      M.IsOptLevel h ∧ T' = M.φ₂ hd - M.φ₂ h := by
  rw [tioli_iff]
  simp only [Set.mem_Ici, IsOptLevel, joint]
  constructor
  · rintro ⟨a, b, c⟩
    exact ⟨⟨a, b⟩, by linarith⟩
  · rintro ⟨⟨a, b⟩, c⟩
    exact ⟨a, b, by linarith⟩

/-- **Figure 11.B.3** (MWG, p. 357). From the disagreement point `a = (φ₁(h_d) + w₁, φ₂(h_d) + w₂)`
the post-bargaining utilities are `f` (consumer 2 proposes) and `d` (consumer 1 proposes); both
lie on the frontier `u₁ + u₂ = φ₁(h°) + φ₂(h°) + w₁ + w₂`, and the individually rational frontier
points are exactly the segment `[f, d]`. -/
theorem figure_11_B_3 (hd ho w₁ w₂ u₁ u₂ : ℝ) (hopt : M.IsOptLevel ho) (hd0 : 0 ≤ hd) :
    let S := M.φ₁ ho + M.φ₂ ho
    let f : ℝ × ℝ := (M.φ₁ hd + w₁, S - M.φ₁ hd + w₂)
    let d : ℝ × ℝ := (S - M.φ₂ hd + w₁, M.φ₂ hd + w₂)
    f.1 + f.2 = S + w₁ + w₂ ∧ d.1 + d.2 = S + w₁ + w₂ ∧
      ((u₁ + u₂ = S + w₁ + w₂ ∧ M.φ₁ hd + w₁ ≤ u₁ ∧ M.φ₂ hd + w₂ ≤ u₂) ↔
        ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ u₁ = s * f.1 + (1 - s) * d.1 ∧
          u₂ = s * f.2 + (1 - s) * d.2) := by
  intro S f d
  have hgain : M.joint hd ≤ M.joint ho := hopt.2 hd hd0
  simp only [joint] at hgain
  simp only [f, d, S]
  refine ⟨by ring, by ring, ?_⟩
  constructor
  · rintro ⟨hs, h1, h2⟩
    rcases eq_or_lt_of_le hgain with heq | hlt
    · refine ⟨1, zero_le_one, le_rfl, by linarith, by linarith⟩
    · refine ⟨(M.φ₁ ho + M.φ₂ ho - M.φ₂ hd + w₁ - u₁) /
          (M.φ₁ ho + M.φ₂ ho - (M.φ₁ hd + M.φ₂ hd)), ?_, ?_, ?_, ?_⟩
      · exact div_nonneg (by linarith) (by linarith)
      · rw [div_le_one (by linarith)]
        linarith
      · field_simp
        ring
      · rw [show u₂ = M.φ₁ ho + M.φ₂ ho + w₁ + w₂ - u₁ by linarith]
        field_simp
        ring
  · rintro ⟨s, hs0, hs1, h1, h2⟩
    refine ⟨by rw [h1, h2]; ring, ?_, ?_⟩
    · rw [h1]; nlinarith
    · rw [h2]; nlinarith

/-- **Small type, p. 358.** If the two agents are firms and one buys the other, the merged firm
maximizes `π₁ + π₂` and so chooses exactly the optimal levels. -/
theorem merger_internalizes (h : ℝ) :
    (0 ≤ h ∧ ∀ y, 0 ≤ y → M.φ₁ y + M.φ₂ y ≤ M.φ₁ h + M.φ₂ h) ↔ M.IsOptLevel h :=
  Iff.rfl

/-! ## Externalities and missing markets -/

/-- **(11.B.6)** (MWG, p. 358). Consumer 1's demand for rights at price `p_h`: `h₁` maximizes
`φ₁(h₁) - p_h h₁` on `ℝ₊` iff `φ₁'(h₁) ≤ p_h`, with equality if `h₁ > 0`. -/
theorem eq_11_B_6 (p h : ℝ) : M.IsTaxChoice p h ↔ IsFOCSol M.d₁ p h := M.eq_11_B_4 p h

/-- Consumer 2's supply of rights at price `p_h`: `h₂` maximizes `φ₂(h₂) + p_h h₂` on `ℝ₊`. -/
def IsRightsSupply (p h : ℝ) : Prop := 0 ≤ h ∧ ∀ y, 0 ≤ y → M.φ₂ y + p * y ≤ M.φ₂ h + p * h

/-- **(11.B.7)** (MWG, p. 358). `h₂` is consumer 2's supply iff `φ₂'(h₂) ≤ -p_h`, with equality
if `h₂ > 0`. -/
theorem eq_11_B_7 (p h : ℝ) : M.IsRightsSupply p h ↔ IsFOCSol M.d₂ (-p) h := by
  have hf : ∀ x, HasDerivAt (fun h => M.φ₂ h + p * h) (M.d₂ x + p) x := fun x => by
    have h2 : HasDerivAt (fun y => p * y) p x := by simpa using (hasDerivAt_id x).const_mul p
    exact (M.hd₂ x).add h2
  have hanti : AntitoneOn (fun x => M.d₂ x + p) (Set.Ici 0) :=
    fun a ha b hb hab => by simpa using M.anti₂.antitoneOn ha hb hab
  rw [IsRightsSupply, kt_isMax_iff hf hanti]
  simp only [IsFOCSol]
  constructor
  · rintro ⟨h0, h1, h2⟩
    exact ⟨h0, by linarith, fun hp => by linarith [h2 hp]⟩
  · rintro ⟨h0, h1, h2⟩
    exact ⟨h0, by linarith, fun hp => by linarith [h2 hp]⟩

/-- A competitive equilibrium of the market for rights: price `p` and a traded quantity `h`
that is both consumer 1's demand and consumer 2's supply (market clearing `h₁ = h₂`). -/
def IsRightsEquilibrium (p h : ℝ) : Prop := M.IsTaxChoice p h ∧ M.IsRightsSupply p h

/-- **The rights market is efficient** (MWG, p. 359): the equilibrium quantity `h**` satisfies
(11.B.2), so `h** = h°`; and if `h** > 0` the price is `p_h* = φ₁'(h°) = -φ₂'(h°)`. -/
theorem rights_equilibrium_optimal {p h : ℝ} (he : M.IsRightsEquilibrium p h) :
    M.IsOptLevel h ∧ (0 < h → p = M.d₁ h ∧ p = -M.d₂ h) := by
  have h1 := (M.eq_11_B_6 p h).1 he.1
  have h2 := (M.eq_11_B_7 p h).1 he.2
  refine ⟨(M.eq_11_B_2 h).2 ⟨h1.1, by linarith [h1.2.1, h2.2.1], fun hp => ?_⟩, fun hp => ?_⟩
  · linarith [h1.2.2 hp, h2.2.2 hp]
  · exact ⟨(h1.2.2 hp).symm, by linarith [h2.2.2 hp]⟩

/-- **Existence of the efficient rights equilibrium** (MWG, p. 359): at the optimal level `h°`,
the price `p_h* = φ₁'(h°)` clears the market. Utilities are `φ₁(h°) - p_h* h°` and
`φ₂(h°) + p_h* h°`, a point on the frontier (point `g` of Figure 11.B.3). -/
theorem rights_equilibrium_exists {ho : ℝ} (hopt : M.IsOptLevel ho) :
    M.IsRightsEquilibrium (M.d₁ ho) ho ∧
      (M.φ₁ ho - M.d₁ ho * ho) + (M.φ₂ ho + M.d₁ ho * ho) = M.joint ho := by
  rw [eq_11_B_2] at hopt
  refine ⟨⟨(M.eq_11_B_6 _ _).2 ⟨hopt.1, le_rfl, fun _ => rfl⟩,
    (M.eq_11_B_7 _ _).2 ⟨hopt.1, by linarith [hopt.2.1], fun hp => by linarith [hopt.2.2 hp]⟩⟩,
    by simp only [joint]; ring⟩

/-! ## A concrete instance -/

/-- The instance `φ₁(h) = 4h - h²/2`, `φ₂(h) = -h - h²/2` (a negative externality). -/
noncomputable def ex : Bilateral where
  φ₁ h := 4 * h - h ^ 2 / 2
  φ₂ h := -h - h ^ 2 / 2
  d₁ h := 4 - h
  d₂ h := -1 - h
  hd₁ h := by
    have h' := ((hasDerivAt_id h).const_mul 4).sub ((hasDerivAt_pow 2 h).div_const 2)
    exact (h'.congr_deriv (by simp only [Nat.cast_ofNat]; ring) :
      HasDerivAt (fun h : ℝ => 4 * h - h ^ 2 / 2) (4 - h) h)
  hd₂ h := by
    have h' := (hasDerivAt_id h).neg.sub ((hasDerivAt_pow 2 h).div_const 2)
    exact (h'.congr_deriv (by simp only [Nat.cast_ofNat]; ring) :
      HasDerivAt (fun h : ℝ => -h - h ^ 2 / 2) (-1 - h) h)
  anti₁ _ _ _ _ hab := by linarith
  anti₂ _ _ _ _ hab := by linarith

/-- In the instance, `h* = 4`, `h° = 3/2`, the Pigouvian tax is `5/2`, and consumer 2's
take-it-or-leave-it offer is `(3/2, 39/8)`. -/
theorem ex_values :
    ex.IsEqLevel 4 ∧ ex.IsOptLevel (3 / 2) ∧ ex.IsTaxChoice (5 / 2) (3 / 2) ∧
      ex.IsOffer2Free (3 / 2) (39 / 8) ∧ ex.IsRightsEquilibrium (5 / 2) (3 / 2) := by
  have he : ex.IsEqLevel 4 := (ex.eq_11_B_1 4).2 ⟨by norm_num, by simp [ex], fun _ => by simp [ex]⟩
  have ho : ex.IsOptLevel (3 / 2) :=
    (ex.eq_11_B_2 _).2 ⟨by norm_num, by simp [ex]; norm_num, fun _ => by simp [ex]; norm_num⟩
  have ht := ex.pigou_tax ho
  have hd : -ex.d₂ (3 / 2) = 5 / 2 := by simp [ex]; norm_num
  rw [hd] at ht
  refine ⟨he, ho, ht, (ex.eq_11_B_5 _ _).2 ⟨ho, by simp [ex]; norm_num⟩, ?_⟩
  have := (ex.rights_equilibrium_exists ho).1
  have hd1 : ex.d₁ (3 / 2) = 5 / 2 := by simp [ex]; norm_num
  rwa [hd1] at this

end Bilateral

end MWG.ExternalitiesPublicGoods
