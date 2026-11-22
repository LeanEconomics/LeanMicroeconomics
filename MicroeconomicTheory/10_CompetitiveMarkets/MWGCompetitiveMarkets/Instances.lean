/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGCompetitiveMarkets.GroupMarkets

/-!
# Concrete instances (non-vacuity of the hypothesis bundles of Chapter 10)

One consumer `φ(x) = 2(1 - e^{-x})` and one firm `c(q) = q + q²/2` satisfy all assumptions of
Section 10.C (`QLConsumer`, `QLFirmStrict`, `maxᵢ φᵢ'(0) = 2 > minⱼ cⱼ'(0) = 1`). For this economy
we exhibit a competitive equilibrium (Definition 10.B.3), check that it is Pareto optimal
(Proposition 10.D.1) and apply the second welfare theorem (Proposition 10.D.2). Further
instances: the strong-monotonicity hypotheses of Exercise 10.B.1(b), the strictly convex cost of
Exercise 10.F.1, the efficient-scale characterization of Figure 10.F.4 with linear demand, and the
utilitarian welfare function for the surplus criterion of Section 10.E.
-/

namespace MWG.CompetitiveMarkets

open MWG.ConsumerChoice MWG.ClassicalDemand

/-- The consumer of the instance economy. -/
noncomputable def instC : Fin 1 → QLConsumer := fun _ => expConsumer 2 two_pos

/-- The firm of the instance economy. -/
noncomputable def instF : Fin 1 → QLFirmStrict := fun _ => quadFirm 1 1 one_pos one_pos

theorem inst_gap : ∃ i j, (instF j).dc 0 < (instC i).dφ 0 :=
  ⟨0, 0, by simp [instF, instC, quadFirm, quadFirmBase, QLFirmStrict.dc, expConsumer]⟩

/-- **Instance of Section 10.C-10.D.** The instance economy has a competitive equilibrium in the
sense of Definition 10.B.3 (endowment `1` of the numeraire, the consumer owning the firm), and
that equilibrium allocation is Pareto optimal (Proposition 10.D.1). -/
theorem inst_equilibrium_pareto :
    ∃ (a : Allocation (Fin 1) (Fin 1) 2) (p : ℝ),
      (qlEconomyOf instC (fun j => (instF j).toQLFirm) (fun _ => 1) (fun _ _ => 1)).IsCompetitiveEqm
        a (qlPrice p) ∧
      (qlEconomyOf instC (fun j => (instF j).toQLFirm) (fun _ => 1)
        (fun _ _ => 1)).toEconomy.IsParetoOptimal a := by
  obtain ⟨p, -, -, -, -, hq⟩ := ql_eqm_exists instC instF inst_gap
  have hθ : ∀ j : Fin 1, ∑ i : Fin 1, (fun _ _ => (1 : ℝ)) i j = 1 := fun _ => by simp
  have h := ql_isCompetitiveEqm_of_isQLEqm hq (fun _ => 1) (fun _ _ => 1) hθ
  exact ⟨_, p, h, proposition_10_D_1 instC _ _ _ hθ _ p h⟩

/-- **Instance of Proposition 10.D.2.** For the Pareto optimal equilibrium allocation of the
instance economy, the transfers of the second welfare theorem exist. -/
theorem inst_second_welfare :
    ∃ a : Allocation (Fin 1) (Fin 1) 2,
      (qlEconomyOf instC (fun j => (instF j).toQLFirm) (fun _ => 1)
        (fun _ _ => 1)).toEconomy.IsParetoOptimal a ∧
      ∃ T : Fin 1 → ℝ, ∑ i, T i = 0 ∧ ∃ (a' : Allocation (Fin 1) (Fin 1) 2) (p : ℝ),
        (qlEconomyOf instC (fun j => (instF j).toQLFirm) ((fun _ => 1) + T)
          (fun _ _ => 1)).IsCompetitiveEqm a' (qlPrice p) := by
  obtain ⟨a, -, -, hPO⟩ := inst_equilibrium_pareto
  obtain ⟨T, hT, a', p, h, -⟩ := proposition_10_D_2 instC instF inst_gap (fun _ => 1)
    (fun _ _ => 1) (fun _ => by simp) a hPO
  exact ⟨a, hPO, T, hT, a', p, h⟩

/-- **Instance of Exercise 10.B.1(b).** One good, `Xᵢ = ℝ₊`, `uᵢ(x) = x`: continuous and strongly
monotone. -/
theorem inst_exercise_10_B_1b :
    ContinuousOn (fun x : Fin 1 → ℝ => x 0) (nonnegOrthant 1) ∧
      PrefStronglyMonotone (nonnegOrthant 1) (utilityPref fun x : Fin 1 → ℝ => x 0) := by
  refine ⟨(continuous_apply 0).continuousOn, fun x _ y _ hxy hne => ?_⟩
  have hlt : x 0 < y 0 := by
    refine lt_of_le_of_ne (hxy 0) fun h => hne ?_
    ext l; fin_cases l; exact h.symm
  exact ⟨hlt.le, not_le.2 hlt⟩

/-- **Instance of Exercise 10.F.1.** `c(q) = q²` (strictly convex, `c(0) = 0`): `π(p) > 0` iff
`p > c'(0) = 0`. -/
theorem inst_exercise_10_F_1 (p : ℝ) : PosProfit (fun q => q ^ 2) p ↔ 0 < p := by
  have h := exercise_10_F_1 (c := fun q => q ^ 2) (dc := fun q => 2 * q) (by simp)
    (fun q _ => by simpa using (hasDerivAt_pow 2 q).hasDerivWithinAt)
    ((strictConvexOn_pow (by norm_num : 1 < 2)).subset (fun _ h => h) (convex_Ici 0)) p
  simpa using h

/-- **Instance of Figure 10.F.4.** Demand `10 - p` and cost `1 + q + q²` (`q > 0`): the unique
long-run equilibria are `(3, 1, 7)`. -/
theorem inst_lr_efficientScale {p q : ℝ} {J : ℕ} :
    IsLREqm (fun p => 10 - p) (quadLumpyCost (1 * 1 ^ 2) 1 1) p q J ↔
      p = 3 ∧ q = 1 ∧ (J : ℝ) = 7 := by
  obtain ⟨hqb, hcb, huniq⟩ := quadLumpy_efficientScale (α := 1) one_pos one_pos
  have hc0 : quadLumpyCost (1 * 1 ^ 2) 1 1 0 = 0 := by simp [quadLumpyCost, lumpyCost]
  have hcb3 : quadLumpyCost (1 * 1 ^ 2) 1 1 1 / 1 = 3 := by rw [hcb]; norm_num
  rw [lr_efficientScale hc0 hqb huniq (by rw [hcb3]; norm_num)
    (fun a _ b _ hab => by linarith), hcb3]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, by linarith⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, by rw [h3]; norm_num⟩

/-- **Instance of the surplus criterion (pp. 328-329).** The utilitarian welfare function is
strictly increasing and attains its maximum under redistribution, so
`welfare_lt_iff_surplus_lt` applies. -/
theorem inst_welfare_lt {s₀ s₁ : ℝ} : s₀ < s₁ ↔ s₀ < s₁ :=
  welfare_lt_iff_surplus_lt (ι := Fin 2) (fun u => ∑ i, u i)
    (fun u v h => Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _ => h i)
    (footnote_10_E_17 s₀ (u := fun _ => s₀ / 2) (by simp; ring))
    (footnote_10_E_17 s₁ (u := fun _ => s₁ / 2) (by simp; ring))

end MWG.CompetitiveMarkets
