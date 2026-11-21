/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGCompetitiveMarkets.WelfareTheorems
import Mathlib.Topology.Order.Compact

/-!
# Existence and uniqueness of equilibrium with merely convex costs (MWG, pp. 320-321, 327)

MWG proves existence of the partial equilibrium on p. 320 for strictly convex costs with
`c' → ∞`, and says that with merely convex costs "the basic features of the analysis do not
change". Here supply is a correspondence, so we argue directly through aggregate surplus:

* `optimalLevels_exist`: problem (10.D.2) has a solution for any consumers and firms of
  Section 10.C (bounded `φᵢ`, `cⱼ' > 0`, `cⱼ'' ≥ 0`), by compactness, since surplus falls below
  its value at zero once aggregate output exceeds `∑ sup φᵢ / minⱼ cⱼ'(0)`.
* `ql_eqm_exists_convex`: by (10.D.3)-(10.D.5) its first-order conditions give a competitive
  equilibrium (10.C.1)-(10.C.3), hence one in the sense of Definition 10.B.3 for every
  distribution of endowments and shares.
* `ql_eqm_unique_convex`: with `maxᵢ φᵢ'(0) > minⱼ cⱼ'(0)` the equilibrium price and individual
  consumptions are unique, and so is aggregate output (individual outputs need not be:
  Figure 10.C.4).
* `proposition_10_D_2_convex`: the second welfare theorem without presupposing an equilibrium.
-/

namespace MWG.CompetitiveMarkets

open Filter Topology

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **Existence of optimal levels** (problem (10.D.2), MWG p. 326) for the consumers and firms of
Section 10.C, with at least one firm. -/
theorem optimalLevels_exist [Nonempty κ] (C : ι → QLConsumer) (F : κ → QLFirm) :
    ∃ x q, IsOptimalLevels (fun i => (C i).φ) (fun j => (F j).c) x q := by
  classical
  choose B hB using fun i => (C i).bddAbove
  have hBφ : ∀ i y, 0 ≤ y → (C i).φ y ≤ B i := fun i y hy => hB i ⟨y, hy, rfl⟩
  have hB0 : ∀ i, 0 ≤ B i := fun i => by have := hBφ i 0 le_rfl; rwa [(C i).φ_zero] at this
  obtain ⟨j₀, -, hj₀⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (fun j => (F j).dc 0)
  set m := Finset.univ.inf' Finset.univ_nonempty (fun j => (F j).dc 0) with hmdef
  have hm : 0 < m := by rw [hj₀]; exact (F j₀).dc_pos 0 le_rfl
  have hmle : ∀ j, m ≤ (F j).dc 0 := fun j => Finset.inf'_le _ (Finset.mem_univ j)
  have hcost : ∀ j q, 0 ≤ q → (F j).c 0 + m * q ≤ (F j).c q := fun j q hq => by
    have := (F j).le_tangent le_rfl hq
    nlinarith [hmle j]
  set Mb := ∑ i, B i
  have hMb : 0 ≤ Mb := Finset.sum_nonneg fun i _ => hB0 i
  set Bd := Mb / m
  have hBd : 0 ≤ Bd := div_nonneg hMb hm.le
  set S : (ι → ℝ) × (κ → ℝ) → ℝ := fun z => ∑ i, (C i).φ (z.1 i) - ∑ j, (F j).c (z.2 j) with hS
  set D : Set ((ι → ℝ) × (κ → ℝ)) :=
    {z | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ ∑ i, z.1 i = ∑ j, z.2 j ∧ ∑ j, z.2 j ≤ Bd} with hD
  have hcs1 : Continuous fun z : (ι → ℝ) × (κ → ℝ) => ∑ i, z.1 i :=
    continuous_finsetSum _ fun i _ => (continuous_apply i).comp continuous_fst
  have hcs2 : Continuous fun z : (ι → ℝ) × (κ → ℝ) => ∑ j, z.2 j :=
    continuous_finsetSum _ fun j _ => (continuous_apply j).comp continuous_snd
  have hclosed : IsClosed D := by
    have e : D = {z : (ι → ℝ) × (κ → ℝ) | 0 ≤ z.1} ∩ ({z | 0 ≤ z.2} ∩
        ({z | ∑ i, z.1 i = ∑ j, z.2 j} ∩ {z | ∑ j, z.2 j ≤ Bd})) := rfl
    rw [e]
    exact (isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_const continuous_snd).inter
        ((isClosed_eq hcs1 hcs2).inter (isClosed_le hcs2 continuous_const)))
  have hsub : D ⊆ Set.Icc 0 (fun _ => Bd) ×ˢ Set.Icc 0 (fun _ => Bd) := by
    rintro ⟨x, q⟩ ⟨hx, hq, hs, hb⟩
    refine ⟨⟨hx, fun i => ?_⟩, ⟨hq, fun j => ?_⟩⟩
    · have := Finset.single_le_sum (f := x) (fun k _ => hx k) (Finset.mem_univ i)
      simp only at hs hb
      linarith
    · have := Finset.single_le_sum (f := q) (fun k _ => hq k) (Finset.mem_univ j)
      simp only at hb
      linarith
  have hcomp : IsCompact D := (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset hclosed hsub
  have h0 : ((0 : ι → ℝ), (0 : κ → ℝ)) ∈ D := ⟨le_rfl, le_rfl, by simp, by simp [hBd]⟩
  have hcont : ContinuousOn S D := by
    refine ContinuousOn.sub (continuousOn_finsetSum _ fun i _ => ?_)
      (continuousOn_finsetSum _ fun j _ => ?_)
    · exact (C i).φ_continuousOn.comp ((continuous_apply i).comp continuous_fst).continuousOn
        fun z hz => Set.mem_Ici.2 (hz.1 i)
    · exact (F j).c_continuousOn.comp ((continuous_apply j).comp continuous_snd).continuousOn
        fun z hz => Set.mem_Ici.2 (hz.2.1 j)
  obtain ⟨z, hz, hmax⟩ := hcomp.exists_isMaxOn ⟨_, h0⟩ hcont
  refine ⟨z.1, z.2, fun i => hz.1 i, fun j => hz.2.1 j, hz.2.2.1, fun x' q' hx' hq' hs => ?_⟩
  have hzS : S z = qlSurplus (fun i => (C i).φ) (fun j => (F j).c) z.1 z.2 := rfl
  rw [← hzS]
  by_cases hb : ∑ j, q' j ≤ Bd
  · exact hmax (a := (x', q')) ⟨hx', hq', hs, hb⟩
  · push Not at hb
    have h1 : ∑ i, (C i).φ (x' i) ≤ Mb := Finset.sum_le_sum fun i _ => hBφ i _ (hx' i)
    have h2 : ∑ j, ((F j).c 0 + m * q' j) ≤ ∑ j, (F j).c (q' j) :=
      Finset.sum_le_sum fun j _ => hcost j _ (hq' j)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum] at h2
    have h3 : Mb < m * ∑ j, q' j := by
      have := mul_lt_mul_of_pos_left hb hm
      rwa [mul_div_cancel₀ _ hm.ne'] at this
    have h4 : S (0, 0) ≤ S z := hmax (a := (0, 0)) h0
    have hS0 : S (0, 0) = -∑ j, (F j).c 0 := by
      simp [hS, QLConsumer.φ_zero]
    rw [hS0] at h4
    simp only [qlSurplus]
    linarith

/-- **Existence of competitive equilibrium with convex costs** (MWG, pp. 320-321): for any
consumers and (at least one) firm of Section 10.C there is a solution of (10.C.1)-(10.C.3). -/
theorem ql_eqm_exists_convex [Nonempty κ] (C : ι → QLConsumer) (F : κ → QLFirm) :
    ∃ x q p, IsQLEqm C F x q p := by
  obtain ⟨x, q, h⟩ := optimalLevels_exist C F
  obtain ⟨p, hp⟩ := optimalLevels_foc h
  exact ⟨x, q, p, hp⟩

/-- Existence in the sense of Definition 10.B.3, for every distribution of endowments and shares
summing to one. -/
theorem ql_competitiveEqm_exists_convex [Nonempty κ] (C : ι → QLConsumer) (F : κ → QLFirm)
    (ωm : ι → ℝ) (θ : ι → κ → ℝ) (hθ : ∀ j, ∑ i, θ i j = 1) :
    ∃ (a : Allocation ι κ 2) (p : ℝ), (qlEconomyOf C F ωm θ).IsCompetitiveEqm a (qlPrice p) := by
  obtain ⟨x, q, p, h⟩ := ql_eqm_exists_convex C F
  exact ⟨_, p, ql_isCompetitiveEqm_of_isQLEqm h ωm θ hθ⟩

/-- **Uniqueness with convex costs** (MWG, p. 320, Figure 10.C.4, footnote 15). If
`maxᵢ φᵢ'(0) > minⱼ cⱼ'(0)`, any two solutions of (10.C.1)-(10.C.3) have the same price, the same
individual consumptions and the same aggregate output. -/
theorem ql_eqm_unique_convex {C : ι → QLConsumer} {F : κ → QLFirm}
    (hgap : ∃ i j, (F j).dc 0 < (C i).dφ 0) {x x' : ι → ℝ} {q q' : κ → ℝ} {p p' : ℝ}
    (h : IsQLEqm C F x q p) (h' : IsQLEqm C F x' q' p') :
    x = x' ∧ ∑ j, q j = ∑ j, q' j ∧ p = p' := by
  obtain ⟨hxx, hqq⟩ := exercise_10_D_1 (fun i => (C i).strictConcave) (fun j => (F j).convex)
    h.isOptimalLevels h'.isOptimalLevels
  refine ⟨hxx, hqq, ?_⟩
  obtain ⟨i, hi⟩ := exists_pos_of_sum_pos (h.aggregate_pos hgap)
  have e1 := (h.2.1 i).2.2 hi
  have e2 := (h'.2.1 i).2.2 (hxx ▸ hi)
  rw [← hxx] at e2
  rw [← e1, e2]

/-- **Proposition 10.D.2** (MWG, p. 327) for the economy of Section 10.C with merely convex costs:
for the utility levels of any Pareto optimal allocation there are transfers `∑ Tᵢ = 0` and a
competitive equilibrium from endowments `ω_{mi} + Tᵢ` attaining them. No equilibrium is
presupposed. -/
theorem proposition_10_D_2_convex [Nonempty ι] [Nonempty κ] (C : ι → QLConsumer)
    (F : κ → QLFirm) (ωm : ι → ℝ) (θ : ι → κ → ℝ) (hθ : ∀ j, ∑ i, θ i j = 1)
    (a : Allocation ι κ 2) (hPO : (qlEconomyOf C F ωm θ).toEconomy.IsParetoOptimal a) :
    ∃ T : ι → ℝ, ∑ i, T i = 0 ∧ ∃ (a' : Allocation ι κ 2) (p : ℝ),
      (qlEconomyOf C F (ωm + T) θ).IsCompetitiveEqm a' (qlPrice p) ∧
      ∀ i, (qlEconomyOf C F (ωm + T) θ).toEconomy.u i (a'.x i) =
        (qlEconomyOf C F ωm θ).toEconomy.u i (a.x i) :=
  proposition_10_D_2_of_exists C F ωm θ hθ a hPO (ql_eqm_exists_convex C F)

/-- **Instance** (constant returns, merely convex): one consumer `φ(x) = 2(1 - e^{-x})` and one
firm `c(q) = q`. An equilibrium exists, with price `1` (unique), it is Pareto optimal, and the
second welfare theorem applies to it. -/
theorem inst_convex_existence :
    ∃ (x : Fin 1 → ℝ) (q : Fin 1 → ℝ),
      IsQLEqm (fun _ => expConsumer 2 two_pos) (fun _ => linearFirm 1 one_pos) x q 1 ∧
      ∀ (x' : Fin 1 → ℝ) (q' : Fin 1 → ℝ) (p' : ℝ),
        IsQLEqm (fun _ => expConsumer 2 two_pos) (fun _ => linearFirm 1 one_pos) x' q' p' →
          p' = 1 ∧ x' = x := by
  have hgap : ∃ i j, ((fun _ : Fin 1 => linearFirm 1 one_pos) j).dc 0 <
      ((fun _ : Fin 1 => expConsumer 2 two_pos) i).dφ 0 :=
    ⟨0, 0, by simp [linearFirm, expConsumer]⟩
  obtain ⟨x, q, p, h⟩ := ql_eqm_exists_convex (fun _ : Fin 1 => expConsumer 2 two_pos)
    (fun _ : Fin 1 => linearFirm 1 one_pos)
  have hp : p = 1 := (figure_10_C_4_price one_pos ⟨0, by simp [expConsumer]⟩ h).1
  subst hp
  refine ⟨x, q, h, fun x' q' p' h' => ?_⟩
  obtain ⟨hxx, -, hpp⟩ := ql_eqm_unique_convex hgap h h'
  exact ⟨hpp.symm, hxx.symm⟩

/-- **Instance of `proposition_10_D_2_convex`** for the constant-returns economy above. -/
theorem inst_proposition_10_D_2_convex :
    ∃ a : Allocation (Fin 1) (Fin 1) 2,
      (qlEconomyOf (fun _ => expConsumer 2 two_pos) (fun _ => linearFirm 1 one_pos) (fun _ => 1)
        (fun _ _ => 1)).toEconomy.IsParetoOptimal a ∧
      ∃ T : Fin 1 → ℝ, ∑ i, T i = 0 ∧ ∃ (a' : Allocation (Fin 1) (Fin 1) 2) (p : ℝ),
        (qlEconomyOf (fun _ => expConsumer 2 two_pos) (fun _ => linearFirm 1 one_pos)
          ((fun _ => 1) + T) (fun _ _ => 1)).IsCompetitiveEqm a' (qlPrice p) := by
  have hθ : ∀ j : Fin 1, ∑ i : Fin 1, (fun _ _ => (1 : ℝ)) i j = 1 := fun _ => by simp
  obtain ⟨a, p, h⟩ := ql_competitiveEqm_exists_convex (fun _ : Fin 1 => expConsumer 2 two_pos)
    (fun _ : Fin 1 => linearFirm 1 one_pos) (fun _ => 1) (fun _ _ => 1) hθ
  have hPO := proposition_10_D_1 _ _ _ _ hθ a p h
  obtain ⟨T, hT, a', p', h', -⟩ := proposition_10_D_2_convex _ _ _ _ hθ a hPO
  exact ⟨a, hPO, T, hT, a', p', h'⟩

end MWG.CompetitiveMarkets
