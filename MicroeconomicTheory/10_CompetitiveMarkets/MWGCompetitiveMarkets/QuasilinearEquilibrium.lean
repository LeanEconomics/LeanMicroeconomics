/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGCompetitiveMarkets.ParetoEquilibrium
import MWGCompetitiveMarkets.QuasilinearModel

/-!
# Competitive equilibrium in the two-good quasilinear model (MWG Section 10.C, pp. 317-325)

The quasilinear economy is an instance of Definition 10.B.3 (`qlEconomy`): goods `0` (the
numeraire `m`) and `1` (good `ℓ`), consumption sets `ℝ × ℝ₊`, utilities `m + φᵢ(x)`, production
sets `Yⱼ = {(-z, q) : q ≥ 0, z ≥ cⱼ(q)}`, endowments `(ω_{mi}, 0)` and shares `θᵢⱼ`; prices are
normalized to `(1, p)`.

* `ql_supply_iff`, `ql_demand_iff` (pp. 317-318): profit maximization means `z = c(q)` and `q`
  maximizes `pq - c(q)`; utility maximization means the budget binds and `x` maximizes
  `φ(x) - px`. No assumption on `φ`, `c` is needed.
* Footnote 6 (p. 318): `p* > 0` in every equilibrium (`ql_eqm_price_pos`).
* **(10.C.1)-(10.C.3)** (p. 318): `ql_isCompetitiveEqm_iff` characterizes the equilibria of
  Definition 10.B.3 by the `I + J + 1` conditions `IsQLEqm`; these do not involve endowments or
  shares, so equilibrium allocations and prices are independent of them
  (`ql_isCompetitiveEqm_of_isQLEqm`, p. 318).
* p. 318: aggregate consumption is positive when `maxᵢ φᵢ'(0) > minⱼ cⱼ'(0)`.
* p. 320: existence and uniqueness of equilibrium with strictly convex costs and `c' → ∞`
  (`ql_eqm_exists`, `ql_eqm_unique`), with `p* ∈ (minⱼ cⱼ'(0), maxᵢ φᵢ'(0))`.
* Footnote 10 and Figure 10.C.4 (pp. 320-321): constant returns `cⱼ(q) = cq`: supply is
  infinite above `c`, the equilibrium price is `c` and individual outputs are indeterminate.
* Figure 10.C.8 (p. 324): a nonconvex technology with no competitive equilibrium
  (`figure_10_C_8_no_equilibrium`).
-/

namespace MWG.CompetitiveMarkets

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.Production

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **Section 10.C** (MWG, p. 317). The two-good quasilinear economy as a private ownership
economy. Good `0` is the numeraire, good `1` is good `ℓ`. -/
def qlEconomy (φ : ι → ℝ → ℝ) (c : κ → ℝ → ℝ) (ωm : ι → ℝ) (θ : ι → κ → ℝ) :
    PrivEconomy ι κ 2 where
  X _ := {v | 0 ≤ v 1}
  u i v := v 0 + φ i (v 1)
  Y j := {y | 0 ≤ y 1 ∧ c j (y 1) ≤ -y 0}
  ωi i := ![ωm i, 0]
  θ := θ

/-- Prices with the numeraire normalized to `1` (MWG, p. 317). -/
def qlPrice (p : ℝ) : Fin 2 → ℝ := ![1, p]

theorem qlPrice_dot (p : ℝ) (v : Fin 2 → ℝ) : qlPrice p ⬝ᵥ v = v 0 + p * v 1 := by
  simp [qlPrice, dotProduct, Fin.sum_univ_two]

/-- **Profit maximization in the quasilinear model** (MWG, p. 317). A plan `y` is profit
maximizing at prices `(1, p)` iff `y = (-c(q), q)` with `q ≥ 0` maximizing `pq - c(q)`. -/
theorem ql_supply_iff (c : ℝ → ℝ) (p : ℝ) (y : Fin 2 → ℝ) :
    y ∈ supply {y : Fin 2 → ℝ | 0 ≤ y 1 ∧ c (y 1) ≤ -y 0} (qlPrice p) ↔
      0 ≤ y 1 ∧ y 0 = -c (y 1) ∧ ∀ q, 0 ≤ q → p * q - c q ≤ p * y 1 - c (y 1) := by
  constructor
  · rintro ⟨⟨hq, hz⟩, hmax⟩
    have h1 := hmax ![-c (y 1), y 1] (by simp [hq])
    simp only [qlPrice_dot] at h1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at h1
    have hy0 : y 0 = -c (y 1) := le_antisymm (by linarith) (by linarith)
    refine ⟨hq, hy0, fun q hq' => ?_⟩
    have h2 := hmax ![-c q, q] (by simp [hq'])
    simp only [qlPrice_dot, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one] at h2
    linarith
  · rintro ⟨hq, hy0, hmax⟩
    refine ⟨⟨hq, by rw [hy0, neg_neg]⟩, fun y' hy' => ?_⟩
    simp only [qlPrice_dot]
    have := hmax (y' 1) hy'.1
    linarith [hy'.2]

/-- **Utility maximization in the quasilinear model** (MWG, p. 318). A bundle `v = (m, x)` solves
the UMP at prices `(1, p)` and wealth `w` iff `x ≥ 0`, the budget binds (`m = w - px`), and `x`
maximizes `φ(x) - px` on `x ≥ 0`. -/
theorem ql_demand_iff (φ : ℝ → ℝ) (p w : ℝ) (v : Fin 2 → ℝ) :
    v ∈ walrasianDemandOn {v : Fin 2 → ℝ | 0 ≤ v 1} (fun v => v 0 + φ (v 1)) (qlPrice p) w ↔
      0 ≤ v 1 ∧ v 0 = w - p * v 1 ∧ ∀ x, 0 ≤ x → φ x - p * x ≤ φ (v 1) - p * v 1 := by
  constructor
  · rintro ⟨⟨hx, hb⟩, hmax⟩
    simp only [qlPrice_dot] at hb
    have hbind : v 0 = w - p * v 1 := by
      by_contra hne
      have hlt : v 0 + p * v 1 < w := lt_of_le_of_ne hb fun h => hne (by linarith)
      have := hmax ![w - p * v 1, v 1] ⟨by simpa using hx, by rw [qlPrice_dot]; simp⟩
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at this
      linarith
    refine ⟨hx, hbind, fun x hx' => ?_⟩
    have := hmax ![w - p * x, x] ⟨by simpa using hx', by rw [qlPrice_dot]; simp⟩
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at this
    linarith
  · rintro ⟨hx, hbind, hmax⟩
    refine ⟨⟨hx, by rw [qlPrice_dot, hbind]; linarith⟩, fun v' hv' => ?_⟩
    have hb := hv'.2
    rw [qlPrice_dot] at hb
    have := hmax (v' 1) hv'.1
    simp only
    linarith

omit [Fintype ι] in
/-- Consumer `i`'s wealth in the quasilinear economy:
`ω_{mi} + ∑ⱼ θᵢⱼ (yⱼ₀ + p yⱼ₁)`. -/
theorem ql_wealth (φ : ι → ℝ → ℝ) (c : κ → ℝ → ℝ) (ωm : ι → ℝ) (θ : ι → κ → ℝ)
    (a : Allocation ι κ 2) (p : ℝ) (i : ι) :
    (qlEconomy φ c ωm θ).wealth a (qlPrice p) i =
      ωm i + ∑ j, θ i j * (a.y j 0 + p * a.y j 1) := by
  simp only [PrivEconomy.wealth, qlPrice_dot]
  simp [qlEconomy]

/-- **Footnote 6** (MWG, p. 318). In any competitive equilibrium of the quasilinear model the
price of good `ℓ` is positive (otherwise a consumer with strictly increasing `φᵢ` would demand
an unbounded amount). -/
theorem ql_eqm_price_pos {φ : ι → ℝ → ℝ} {c : κ → ℝ → ℝ} {ωm : ι → ℝ} {θ : ι → κ → ℝ}
    (i₀ : ι) (hφ : StrictMonoOn (φ i₀) (Set.Ici 0)) {a : Allocation ι κ 2} {p : ℝ}
    (h : (qlEconomy φ c ωm θ).IsCompetitiveEqm a (qlPrice p)) : 0 < p := by
  have hd := (ql_demand_iff (φ i₀) p _ (a.x i₀)).1 (h.2.1 i₀)
  by_contra hp
  push Not at hp
  have h1 := hd.2.2 (a.x i₀ 1 + 1) (by linarith [hd.1])
  have h2 := hφ (Set.mem_Ici.2 hd.1) (Set.mem_Ici.2 (by linarith [hd.1]))
    (by linarith : a.x i₀ 1 < a.x i₀ 1 + 1)
  nlinarith

/-- **Conditions (10.C.1)-(10.C.3)** (MWG, p. 318): `p ≤ cⱼ'(qⱼ)` with equality if `qⱼ > 0`;
`φᵢ'(xᵢ) ≤ p` with equality if `xᵢ > 0`; `∑ᵢ xᵢ = ∑ⱼ qⱼ`. -/
def IsQLEqm (C : ι → QLConsumer) (F : κ → QLFirm) (x : ι → ℝ) (q : κ → ℝ) (p : ℝ) : Prop :=
  (∀ j, 0 ≤ q j ∧ p ≤ (F j).dc (q j) ∧ (0 < q j → p = (F j).dc (q j))) ∧
  (∀ i, IsFOCSol (C i).dφ p (x i)) ∧ ∑ i, x i = ∑ j, q j

/-- The quasilinear economy with consumers `C` and firms `F`. -/
def qlEconomyOf (C : ι → QLConsumer) (F : κ → QLFirm) (ωm : ι → ℝ) (θ : ι → κ → ℝ) :
    PrivEconomy ι κ 2 :=
  qlEconomy (fun i => (C i).φ) (fun j => (F j).c) ωm θ

/-- The allocation determined by the levels of good `ℓ` (MWG, p. 318): firm `j` uses
`zⱼ = cⱼ(qⱼ)` of the numeraire, consumer `i` consumes
`mᵢ = ω_{mi} + ∑ⱼ θᵢⱼ (p qⱼ - cⱼ(qⱼ)) - p xᵢ`. -/
noncomputable def qlAllocation (F : κ → QLFirm) (ωm : ι → ℝ) (θ : ι → κ → ℝ) (x : ι → ℝ)
    (q : κ → ℝ) (p : ℝ) : Allocation ι κ 2 where
  x i := ![ωm i + ∑ j, θ i j * (p * q j - (F j).c (q j)) - p * x i, x i]
  y j := ![-(F j).c (q j), q j]

/-- **Characterization (10.C.1)-(10.C.3)** (MWG, p. 318). With shares summing to one, an
allocation and prices `(1, p)` form a competitive equilibrium (Definition 10.B.3) of the
quasilinear economy iff the levels of good `ℓ` satisfy (10.C.1)-(10.C.3) and the numeraire
components are the ones determined by budgets and costs. -/
theorem ql_isCompetitiveEqm_iff (C : ι → QLConsumer) (F : κ → QLFirm) (ωm : ι → ℝ)
    (θ : ι → κ → ℝ) (hθ : ∀ j, ∑ i, θ i j = 1) (a : Allocation ι κ 2) (p : ℝ) :
    (qlEconomyOf C F ωm θ).IsCompetitiveEqm a (qlPrice p) ↔
      IsQLEqm C F (fun i => a.x i 1) (fun j => a.y j 1) p ∧
      a = qlAllocation F ωm θ (fun i => a.x i 1) (fun j => a.y j 1) p := by
  have hext : ∀ v w : Fin 2 → ℝ, v 0 = w 0 → v 1 = w 1 → v = w := fun v w h0 h1 => by
    ext l; fin_cases l <;> simp [h0, h1]
  constructor
  · rintro ⟨hfirm, hcons, hclear⟩
    have hF : ∀ j, 0 ≤ a.y j 1 ∧ a.y j 0 = -(F j).c (a.y j 1) ∧
        ∀ q, 0 ≤ q → p * q - (F j).c q ≤ p * a.y j 1 - (F j).c (a.y j 1) :=
      fun j => (ql_supply_iff (F j).c p (a.y j)).1 (hfirm j)
    have hC := fun i => (ql_demand_iff (C i).φ p _ (a.x i)).1 (hcons i)
    refine ⟨⟨fun j => ?_, fun i => ?_, ?_⟩, ?_⟩
    · exact ⟨(hF j).1, ((F j).max_iff (hF j).1).1 (hF j).2.2⟩
    · exact ((C i).max_iff (hC i).1).1 (hC i).2.2
    · have := hclear 1
      simpa [qlEconomyOf, qlEconomy] using this
    · cases a with
      | mk ax ay =>
        simp only [qlAllocation, Allocation.mk.injEq]
        refine ⟨funext fun i => hext _ _ ?_ (by simp), funext fun j => hext _ _ ?_ (by simp)⟩
        · have h := (hC i).2.1
          rw [qlEconomyOf, ql_wealth] at h
          simp only [Matrix.cons_val_zero]
          dsimp only at h ⊢
          rw [h]
          congr 2
          refine Finset.sum_congr rfl fun j _ => ?_
          have := (hF j).2.1
          dsimp only at this
          rw [this]; ring
        · simpa using (hF j).2.1
  · rintro ⟨⟨hq, hx, hsum⟩, ha⟩
    have hy0 : ∀ j, a.y j 0 = -(F j).c (a.y j 1) := fun j => by rw [ha]; simp [qlAllocation]
    have hm : ∀ i, a.x i 0 = ωm i + ∑ j, θ i j * (p * a.y j 1 - (F j).c (a.y j 1)) -
        p * a.x i 1 := fun i => by rw [ha]; simp [qlAllocation]
    have hw : ∀ i, (qlEconomyOf C F ωm θ).wealth a (qlPrice p) i =
        ωm i + ∑ j, θ i j * (p * a.y j 1 - (F j).c (a.y j 1)) := by
      intro i
      rw [qlEconomyOf, ql_wealth]
      congr 1
      exact Finset.sum_congr rfl fun j _ => by rw [hy0 j]; ring
    have hfirm : ∀ j, a.y j ∈ supply ((qlEconomyOf C F ωm θ).Y j) (qlPrice p) := by
      intro j
      exact (ql_supply_iff (F j).c p (a.y j)).2
        ⟨(hq j).1, hy0 j, ((F j).max_iff (hq j).1).2 (hq j).2⟩
    have hcons : ∀ i, a.x i ∈ walrasianDemandOn ((qlEconomyOf C F ωm θ).X i)
        ((qlEconomyOf C F ωm θ).u i) (qlPrice p)
        ((qlEconomyOf C F ωm θ).wealth a (qlPrice p) i) := by
      intro i
      refine (ql_demand_iff (C i).φ p _ (a.x i)).2 ⟨(hx i).1, ?_, ((C i).max_iff (hx i).1).2 (hx i)⟩
      rw [hw, hm]
    refine ⟨hfirm, hcons, ?_⟩
    have h1 : ∑ i, a.x i 1 = ∑ i, (qlEconomyOf C F ωm θ).ωi i 1 + ∑ j, a.y j 1 := by
      simpa [qlEconomyOf, qlEconomy] using hsum
    intro l
    fin_cases l
    · refine lemma_10_B_1 (qlEconomyOf C F ωm θ) a (qlPrice p) 0 (by simp [qlPrice]) hθ
        (fun i => ?_) (fun l hl => ?_)
      · rw [hw, qlPrice_dot, hm]; ring
      · fin_cases l
        · exact absurd rfl hl
        · exact h1
    · exact h1

/-- **Independence of endowments and shares** (MWG, pp. 318-319). If `(x, q, p)` satisfies
(10.C.1)-(10.C.3), then for every distribution of endowments and of shares (summing to one) the
corresponding allocation and prices `(1, p)` are a competitive equilibrium. -/
theorem ql_isCompetitiveEqm_of_isQLEqm {C : ι → QLConsumer} {F : κ → QLFirm} {x : ι → ℝ}
    {q : κ → ℝ} {p : ℝ} (h : IsQLEqm C F x q p) (ωm : ι → ℝ) (θ : ι → κ → ℝ)
    (hθ : ∀ j, ∑ i, θ i j = 1) :
    (qlEconomyOf C F ωm θ).IsCompetitiveEqm (qlAllocation F ωm θ x q p) (qlPrice p) := by
  rw [ql_isCompetitiveEqm_iff C F ωm θ hθ]
  refine ⟨by simpa [qlAllocation] using h, ?_⟩
  simp [qlAllocation]

/-- In every solution of (10.C.1)-(10.C.3) the price is positive (footnote 6, p. 318). -/
theorem IsQLEqm.price_pos [Nonempty ι] {C : ι → QLConsumer} {F : κ → QLFirm} {x : ι → ℝ}
    {q : κ → ℝ} {p : ℝ} (h : IsQLEqm C F x q p) : 0 < p := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  exact ((C i).dφ_pos _ (h.2.1 i).1).trans_le (h.2.1 i).2.1

/-- **(MWG, p. 318)** If `maxᵢ φᵢ'(0) > minⱼ cⱼ'(0)`, aggregate consumption and production of
good `ℓ` are strictly positive in every competitive equilibrium. -/
theorem IsQLEqm.aggregate_pos {C : ι → QLConsumer} {F : κ → QLFirm} {x : ι → ℝ} {q : κ → ℝ}
    {p : ℝ} (h : IsQLEqm C F x q p) (hgap : ∃ i j, (F j).dc 0 < (C i).dφ 0) :
    0 < ∑ i, x i := by
  obtain ⟨i, j, hij⟩ := hgap
  by_contra hle
  push Not at hle
  have hx0 : ∀ k, x k = 0 := fun k =>
    (Finset.sum_eq_zero_iff_of_nonneg fun k _ => (h.2.1 k).1).1
      (le_antisymm hle (Finset.sum_nonneg fun k _ => (h.2.1 k).1)) k (Finset.mem_univ k)
  have hq0 : q j = 0 := by
    have hs : ∑ k, q k = 0 := by rw [← h.2.2]; exact Finset.sum_eq_zero fun k _ => hx0 k
    exact (Finset.sum_eq_zero_iff_of_nonneg fun k _ => (h.1 k).1).1 hs j (Finset.mem_univ j)
  have h1 := (h.2.1 i).2.1
  have h2 := (h.1 j).2.1
  rw [hx0 i] at h1
  rw [hq0] at h2
  linarith

/-- **Uniqueness of equilibrium** (MWG, p. 320; strictly convex costs). If
`maxᵢ φᵢ'(0) > minⱼ cⱼ'(0)`, any two solutions of (10.C.1)-(10.C.3) coincide. -/
theorem ql_eqm_unique [Nonempty ι] {C : ι → QLConsumer} {F : κ → QLFirmStrict}
    (hgap : ∃ i j, (F j).dc 0 < (C i).dφ 0) {x x' : ι → ℝ} {q q' : κ → ℝ} {p p' : ℝ}
    (h : IsQLEqm C (fun j => (F j).toQLFirm) x q p)
    (h' : IsQLEqm C (fun j => (F j).toQLFirm) x' q' p') : x = x' ∧ q = q' ∧ p = p' := by
  have hp := h.price_pos
  have hp' := h'.price_pos
  have hxd : ∀ p'' x'' q'', IsQLEqm C (fun j => (F j).toQLFirm) x'' q'' p'' →
      x'' = fun i => (C i).demand p'' := fun p'' x'' q'' hh => funext fun i =>
    ((C i).demand_eq (hh.2.1 i)).symm
  have hqd : ∀ p'' x'' q'', IsQLEqm C (fun j => (F j).toQLFirm) x'' q'' p'' →
      q'' = fun j => (F j).supply p'' := fun p'' x'' q'' hh => funext fun j =>
    ((F j).supply_eq (hh.1 j)).symm
  have hclr : ∀ p'' x'' q'', IsQLEqm C (fun j => (F j).toQLFirm) x'' q'' p'' →
      aggDemand C p'' = aggSupply F p'' := fun p'' x'' q'' hh => by
    have := hh.2.2
    rw [hxd p'' x'' q'' hh, hqd p'' x'' q'' hh] at this
    exact this
  have hpp : p = p' := by
    by_contra hne
    -- WLOG-style: treat both orders
    have key : ∀ p₁ p₂, 0 < p₁ → p₁ < p₂ → aggDemand C p₁ = aggSupply F p₁ →
        aggDemand C p₂ = aggSupply F p₂ → False := by
      intro p₁ p₂ hp₁ h₁₂ e₁ e₂
      by_cases hlt : ∃ i, p₁ < (C i).dφ 0
      · have := aggDemand_strictAnti C hp₁ h₁₂ hlt
        have := aggSupply_monotone F h₁₂.le
        linarith
      · push Not at hlt
        have hx₁ := (aggDemand_eq_zero_iff C hp₁).2 hlt
        have hx₂ := (aggDemand_eq_zero_iff C (hp₁.trans h₁₂)).2 fun i => (hlt i).trans h₁₂.le
        have hq₂ := (aggSupply_eq_zero_iff F p₂).1 (by rw [← e₂, hx₂])
        obtain ⟨i, j, hij⟩ := hgap
        linarith [hlt i, hq₂ j]
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact key p p' hp hlt (hclr _ _ _ h) (hclr _ _ _ h')
    · exact key p' p hp' hlt (hclr _ _ _ h') (hclr _ _ _ h)
  subst hpp
  exact ⟨(hxd _ _ _ h).trans (hxd _ _ _ h').symm, (hqd _ _ _ h).trans (hqd _ _ _ h').symm, rfl⟩

/-- **Existence of equilibrium** (MWG, p. 320). With strictly convex costs, `cⱼ' → ∞` and
`maxᵢ φᵢ'(0) > minⱼ cⱼ'(0)`, there is a price `p* ∈ (minⱼ cⱼ'(0), maxᵢ φᵢ'(0))` with
`x(p*) = q(p*)`, and `xᵢ* = xᵢ(p*)`, `qⱼ* = qⱼ(p*)` satisfy (10.C.1)-(10.C.3). -/
theorem ql_eqm_exists [Nonempty ι] [Nonempty κ] (C : ι → QLConsumer) (F : κ → QLFirmStrict)
    (hgap : ∃ i j, (F j).dc 0 < (C i).dφ 0) :
    ∃ p, 0 < p ∧ (∃ j, (F j).dc 0 < p) ∧ (∃ i, p < (C i).dφ 0) ∧
      aggDemand C p = aggSupply F p ∧
      IsQLEqm C (fun j => (F j).toQLFirm) (fun i => (C i).demand p)
        (fun j => (F j).supply p) p := by
  obtain ⟨j₀, -, hj₀⟩ := Finset.exists_min_image Finset.univ (fun j => (F j).dc 0)
    Finset.univ_nonempty
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image Finset.univ (fun i => (C i).dφ 0)
    Finset.univ_nonempty
  set lo := (F j₀).dc 0 with hlo
  set hi := (C i₀).dφ 0 with hhi
  have hlohi : lo < hi := by
    obtain ⟨i, j, hij⟩ := hgap
    exact ((hj₀ j (Finset.mem_univ j)).trans_lt hij).trans_le (hi₀ i (Finset.mem_univ i))
  have hlo0 : 0 < lo := (F j₀).toQLFirm.dc_pos 0 le_rfl
  have hZcont : ContinuousOn (fun p => aggDemand C p - aggSupply F p) (Set.Icc lo hi) :=
    ((aggDemand_continuousOn C).mono fun p hp => hlo0.trans_le hp.1).sub
      (aggSupply_continuous F).continuousOn
  have hZlo : 0 < aggDemand C lo - aggSupply F lo := by
    have hq : aggSupply F lo = 0 :=
      (aggSupply_eq_zero_iff F lo).2 fun j => hj₀ j (Finset.mem_univ j)
    have hx : 0 < aggDemand C lo := by
      refine lt_of_le_of_ne (aggDemand_nonneg C hlo0) fun h0 => ?_
      have := ((aggDemand_eq_zero_iff C hlo0).1 h0.symm) i₀
      linarith
    linarith
  have hZhi : aggDemand C hi - aggSupply F hi < 0 := by
    have hx : aggDemand C hi = 0 :=
      (aggDemand_eq_zero_iff C (hlo0.trans hlohi)).2 fun i => hi₀ i (Finset.mem_univ i)
    have hq : 0 < aggSupply F hi := by
      refine lt_of_le_of_ne (aggSupply_nonneg F hi) fun h0 => ?_
      have := ((aggSupply_eq_zero_iff F hi).1 h0.symm) j₀
      linarith
    linarith
  obtain ⟨p, hp, hpZ⟩ := intermediate_value_Icc' hlohi.le hZcont ⟨hZhi.le, hZlo.le⟩
  have hp0 : 0 < p := hlo0.trans_le hp.1
  have hplo : lo < p := lt_of_le_of_ne hp.1 fun h => by rw [← h] at hpZ; linarith
  have hphi : p < hi := lt_of_le_of_ne hp.2 fun h => by rw [h] at hpZ; linarith
  refine ⟨p, hp0, ⟨j₀, hplo⟩, ⟨i₀, hphi⟩, by linarith [hpZ], ⟨fun j => (F j).supply_foc p,
    fun i => (C i).demand_spec hp0, ?_⟩⟩
  have : aggDemand C p = aggSupply F p := by linarith [hpZ]
  exact this

/-! ## Constant returns to scale (footnote 10 and Figure 10.C.4) -/

/-- **Footnote 10** (MWG, p. 320). With `c(q) = cq` and `p > c`, profit has no maximum
(`q(p) = ∞`). -/
theorem footnote_10_C_10 {c p : ℝ} (hcp : c < p) (q : ℝ) :
    ∃ q', 0 ≤ q' ∧ p * q - c * q < p * q' - c * q' :=
  ⟨|q| + 1, by positivity, by nlinarith [le_abs_self q, abs_nonneg q]⟩

/-- **Figure 10.C.4** (MWG, p. 321). With `cⱼ(q) = cq` for all `j` (at least one firm) and some
`φᵢ'(0) > c`, every equilibrium has `p* = c` and aggregate output `x(c)`. -/
theorem figure_10_C_4_price [Nonempty κ] {C : ι → QLConsumer} {c : ℝ} (hc : 0 < c)
    (hgap : ∃ i, c < (C i).dφ 0) {x : ι → ℝ} {q : κ → ℝ} {p : ℝ}
    (h : IsQLEqm C (fun _ => linearFirm c hc) x q p) :
    p = c ∧ ∑ i, x i = aggDemand C c := by
  have hpc : p ≤ c := (h.1 (Classical.arbitrary κ)).2.1
  have hpeq : p = c := by
    refine le_antisymm hpc (not_lt.1 fun hlt => ?_)
    have hq0 : ∀ j, q j = 0 := fun j => by
      by_contra hne
      have := (h.1 j).2.2 (lt_of_le_of_ne (h.1 j).1 (Ne.symm hne))
      simp only [linearFirm] at this
      linarith
    have hs : ∑ i, x i = 0 := by rw [h.2.2]; exact Finset.sum_eq_zero fun j _ => hq0 j
    obtain ⟨i, hi⟩ := hgap
    have hx0 := (Finset.sum_eq_zero_iff_of_nonneg fun k _ => (h.2.1 k).1).1 hs i
      (Finset.mem_univ i)
    have h1 := (h.2.1 i).2.1
    rw [hx0] at h1
    linarith
  subst hpeq
  exact ⟨rfl, Finset.sum_congr rfl fun i _ => ((C i).demand_eq (h.2.1 i)).symm⟩

/-- **Figure 10.C.4** (MWG, p. 321). With constant returns `cⱼ(q) = cq`, `p* = c` and any
division of the aggregate output `x(c)` among firms is an equilibrium; with two firms
`j₁ ≠ j₂` and `x(c) > 0`, giving all output to `j₁` or all to `j₂` are two different equilibria:
individual outputs are not uniquely determined when `J > 1`. -/
theorem figure_10_C_4_indeterminate [DecidableEq κ] {C : ι → QLConsumer} {c : ℝ} (hc : 0 < c)
    (j₁ j₂ : κ) (hj : j₁ ≠ j₂) (hgap : ∃ i, c < (C i).dφ 0) :
    IsQLEqm C (fun _ => linearFirm c hc) (fun i => (C i).demand c)
      (fun j => if j = j₁ then aggDemand C c else 0) c ∧
    IsQLEqm C (fun _ => linearFirm c hc) (fun i => (C i).demand c)
      (fun j => if j = j₂ then aggDemand C c else 0) c ∧
    (fun j => if j = j₁ then aggDemand C c else 0) ≠
      (fun j => if j = j₂ then aggDemand C c else (0 : ℝ)) := by
  have hX : 0 < aggDemand C c := by
    obtain ⟨i, hi⟩ := hgap
    exact Finset.sum_pos' (fun k _ => (C k).demand_nonneg hc)
      ⟨i, Finset.mem_univ i, ((C i).demand_pos_iff hc).2 hi⟩
  have hgood : ∀ j₀ : κ, IsQLEqm C (fun _ => linearFirm c hc) (fun i => (C i).demand c)
      (fun j => if j = j₀ then aggDemand C c else 0) c := by
    intro j₀
    refine ⟨fun j => ⟨?_, by simp [linearFirm], fun _ => by simp [linearFirm]⟩,
      fun i => (C i).demand_spec hc, ?_⟩
    · dsimp only
      split_ifs <;> simp [hX.le]
    · simp [aggDemand]
  refine ⟨hgood j₁, hgood j₂, fun heq => ?_⟩
  have := congrFun heq j₁
  simp [hj] at this
  linarith

/-! ## Figure 10.C.8: nonexistence with a nonconvex technology -/

/-- The nonconvex cost of Figure 10.C.8: `c(q) = 2q - q² + q³/3`, with marginal cost
`c'(q) = 1 + (q - 1)²` rising, falling, then rising. -/
noncomputable def figure_10_C_8_cost (q : ℝ) : ℝ := 2 * q - q ^ 2 + q ^ 3 / 3

/-- **Figure 10.C.8** (MWG, p. 324). One consumer with `φ(x) = (5/2)(1 - e^{-x})` and one firm
with the continuous, differentiable but nonconvex cost `2q - q² + q³/3`: for any endowment and
shares there is no competitive equilibrium. The supply correspondence jumps from `0` to
`q ≥ 3/2` at `p = 5/4`, while demand at `p ≥ 5/4` is below `log 2 < 3/2`. -/
theorem figure_10_C_8_no_equilibrium (ωm : Fin 1 → ℝ) (θ : Fin 1 → Fin 1 → ℝ)
    (a : Allocation (Fin 1) (Fin 1) 2) (p : ℝ) :
    ¬ (qlEconomy (fun _ => (expConsumer (5 / 2) (by norm_num)).φ)
      (fun _ => figure_10_C_8_cost) ωm θ).IsCompetitiveEqm a (qlPrice p) := by
  intro h
  set C := expConsumer (5 / 2) (by norm_num) with hC
  have hp : 0 < p := ql_eqm_price_pos 0 C.φ_strictMono h
  have hd := (ql_demand_iff C.φ p _ (a.x 0)).1 (h.2.1 0)
  have hfoc := (C.max_iff hd.1).1 hd.2.2
  have hs := (ql_supply_iff figure_10_C_8_cost p (a.y 0)).1 (h.1 0)
  have hclear : a.x 0 1 = a.y 0 1 := by
    have := h.2.2 1
    simpa [qlEconomy] using this
  set q := a.y 0 1 with hq
  have hprofit := hs.2.2
  rcases eq_or_lt_of_le hs.1 with h0 | hpos
  · -- no output: then no consumption, so `p ≥ φ'(0) = 5/2`, but output `3/2` is profitable
    have hx0 : a.x 0 1 = 0 := by rw [hclear, ← h0]
    have h1 := hfoc.2.1
    rw [hx0] at h1
    simp only [hC, expConsumer, neg_zero, Real.exp_zero, mul_one] at h1
    have h2 := hprofit (3 / 2) (by norm_num)
    rw [← h0] at h2
    simp only [figure_10_C_8_cost] at h2
    nlinarith
  · -- positive output: `p = c'(q)` and nonnegative profit force `q ≥ 3/2`
    have hder : HasDerivWithinAt (fun z => p * z - figure_10_C_8_cost z)
        (p - (2 - 2 * q + q ^ 2)) (Set.Ici 0) q := by
      have h1 := ((hasDerivAt_id q).const_mul p).sub
        ((((hasDerivAt_id q).const_mul 2).sub (hasDerivAt_pow 2 q)).add
          ((hasDerivAt_pow 3 q).div_const 3))
      exact (h1.congr_deriv (by simp only [Nat.cast_ofNat]; ring)).hasDerivWithinAt
    have hnec := (foc_max_necessary hder hs.1 hprofit).2 hpos
    have hpq : p = 2 - 2 * q + q ^ 2 := by linarith
    have h0 := hprofit 0 le_rfl
    simp only [figure_10_C_8_cost] at h0
    have h1 : 0 ≤ q ^ 2 * (2 * q / 3 - 1) := by rw [hpq] at h0; nlinarith
    have hq32 : 3 / 2 ≤ q := by
      have := (mul_nonneg_iff_of_pos_left (by positivity : 0 < q ^ 2)).1 h1
      linarith
    have hxpos : 0 < a.x 0 1 := by rw [hclear]; exact hpos
    have he := hfoc.2.2 hxpos
    rw [hclear] at he
    simp only [hC, expConsumer] at he
    have hexp : Real.exp (-q) ≤ Real.exp (-(3 / 2)) := Real.exp_le_exp.2 (by linarith)
    have h52 : (5 / 2 : ℝ) ≤ Real.exp (3 / 2) := by
      have := Real.add_one_le_exp (3 / 2 : ℝ); linarith
    have hinv : Real.exp (-(3 / 2)) * Real.exp (3 / 2) = 1 := by
      rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos (-(3 / 2)), Real.exp_pos (-q), sq_nonneg (q - 1)]

end MWG.CompetitiveMarkets
