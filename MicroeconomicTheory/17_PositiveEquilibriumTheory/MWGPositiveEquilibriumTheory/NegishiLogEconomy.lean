/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPositiveEquilibriumTheory.Exercises17AA

/-!
# An instance of the welfare-equation approach (MWG Appendix A; Exercise 17.AA.2)

The economy `logEconomy`: two consumers and two goods, both with the utility
`u(x) = log(1 + x₁) + log(1 + x₂)` (continuous, strictly concave, strongly monotone on `ℝ²₊`,
`u(0) = 0`), endowments `ω₁ = (3/2, 1/2)` and `ω₂ = (1/2, 3/2)`. Every Pareto optimal allocation
lies on the diagonal of the Edgeworth box (`logEconomy_diag`), so one consumer always holds a
bundle `(c, c)` with `c > 0`, at which the only normalized supporting price is `(1/2, 1/2)`
(`logU_support_diag`): `g(s)` is a function. Hence `NegishiHyp logEconomy`
(`logEconomy_negishiHyp`), the instance of Exercise 17.AA.2's hypotheses, and an equilibrium is
found by the welfare equations (`exercise_17_AA_2_instance`).
-/

namespace MWG.PositiveEquilibriumTheory

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.GeneralEquilibriumExamples MWG.WelfareTheorems

/-- The utility `u(x) = log(1 + x₁) + log(1 + x₂)`. -/
noncomputable def logU (x : Fin 2 → ℝ) : ℝ := Real.log (1 + x 0) + Real.log (1 + x 1)

/-- The two-consumer economy with utilities `logU` and endowments `(3/2, 1/2)`, `(1/2, 3/2)`. -/
noncomputable def logEconomy : ExchangeEconomy (Fin 2) 2 :=
  ExchangeEconomy.ofOrthant (fun _ => logU) ![![3 / 2, 1 / 2], ![1 / 2, 3 / 2]]

/-- Concavity of `t ↦ log(1 + t)` on `[0, ∞)`. -/
theorem log1p_concave {a b α β : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hαβ : α + β = 1) :
    α * Real.log (1 + a) + β * Real.log (1 + b) ≤ Real.log (1 + (α * a + β * b)) := by
  have h := strictConcaveOn_log_Ioi.concaveOn.2 (show 1 + a ∈ Set.Ioi (0 : ℝ) from by
    simp only [Set.mem_Ioi]; linarith) (show 1 + b ∈ Set.Ioi (0 : ℝ) from by
    simp only [Set.mem_Ioi]; linarith) hα hβ hαβ
  simp only [smul_eq_mul] at h
  have heq : α * (1 + a) + β * (1 + b) = 1 + (α * a + β * b) := by linear_combination hαβ
  rwa [heq] at h

/-- Strict concavity of `t ↦ log(1 + t)` on `[0, ∞)`. -/
theorem log1p_strict {a b α β : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ≠ b) (hα : 0 < α)
    (hβ : 0 < β) (hαβ : α + β = 1) :
    α * Real.log (1 + a) + β * Real.log (1 + b) < Real.log (1 + (α * a + β * b)) := by
  have h := strictConcaveOn_log_Ioi.2 (show 1 + a ∈ Set.Ioi (0 : ℝ) from by
    simp only [Set.mem_Ioi]; linarith) (show 1 + b ∈ Set.Ioi (0 : ℝ) from by
    simp only [Set.mem_Ioi]; linarith) (fun h => hab (by linarith)) hα hβ hαβ
  simp only [smul_eq_mul] at h
  have heq : α * (1 + a) + β * (1 + b) = 1 + (α * a + β * b) := by linear_combination hαβ
  rwa [heq] at h

/-- `logU` is concave on `ℝ²₊`. -/
theorem logU_concaveOn : ConcaveOn ℝ (nonnegOrthant 2) logU := by
  refine ⟨convex_nonnegOrthant 2, fun x hx y hy a b ha hb hab => ?_⟩
  simp only [logU, smul_eq_mul, Pi.add_apply, Pi.smul_apply, mul_add]
  linarith [log1p_concave (hx 0) (hy 0) ha hb hab, log1p_concave (hx 1) (hy 1) ha hb hab]

/-- `logU` is strictly concave on `ℝ²₊`. -/
theorem logU_strict {x y : Fin 2 → ℝ} (hx : x ∈ nonnegOrthant 2) (hy : y ∈ nonnegOrthant 2)
    (hne : x ≠ y) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    α * logU x + (1 - α) * logU y < logU (α • x + (1 - α) • y) := by
  have hβ : 0 < 1 - α := by linarith
  have hab : α + (1 - α) = 1 := by ring
  simp only [logU, smul_eq_mul, Pi.add_apply, Pi.smul_apply, mul_add]
  by_cases h0 : x 0 = y 0
  · have h1 : x 1 ≠ y 1 := by
      intro h1
      apply hne
      funext l
      fin_cases l
      · exact h0
      · exact h1
    linarith [log1p_concave (hx 0) (hy 0) hα0.le hβ.le hab,
      log1p_strict (hx 1) (hy 1) h1 hα0 hβ hab]
  · linarith [log1p_strict (hx 0) (hy 0) h0 hα0 hβ hab,
      log1p_concave (hx 1) (hy 1) hα0.le hβ.le hab]

/-- `logU` is continuous on `ℝ²₊`. -/
theorem logU_continuousOn : ContinuousOn logU (nonnegOrthant 2) := by
  have h : ∀ l : Fin 2, ContinuousOn (fun x : Fin 2 → ℝ => Real.log (1 + x l))
      (nonnegOrthant 2) := fun l =>
    Real.continuousOn_log.comp (continuous_const.add (continuous_apply l)).continuousOn
      fun x hx => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        have := hx l
        linarith
  exact (h 0).add (h 1)

/-- `logU` is strongly monotone on `ℝ²₊`. -/
theorem logU_stronglyMonotone : UtilityStronglyMonotone logU := by
  intro x hx y _ hxy hne
  have h0 := hxy 0
  have h1 := hxy 1
  have hx0 := hx 0
  have hx1 := hx 1
  have hlt : x 0 < y 0 ∨ x 1 < y 1 := by
    by_contra h
    push Not at h
    exact hne (funext fun l => by fin_cases l <;> simp <;> linarith [h.1, h.2])
  have hl0 := Real.log_le_log (by linarith) (by linarith : 1 + x 0 ≤ 1 + y 0)
  have hl1 := Real.log_le_log (by linarith) (by linarith : 1 + x 1 ≤ 1 + y 1)
  have : logU x < logU y := by
    unfold logU
    rcases hlt with h | h
    · linarith [Real.log_lt_log (by linarith) (by linarith : 1 + x 0 < 1 + y 0)]
    · linarith [Real.log_lt_log (by linarith) (by linarith : 1 + x 1 < 1 + y 1)]
  exact ⟨this.le, not_le.mpr this⟩

/-- `logU` satisfies the chapter's standing assumptions. -/
theorem logU_standard : StandardUtility logU := by
  refine ⟨logU_continuousOn, ⟨convex_nonnegOrthant 2, fun x hx x' hx' hne α hα0 hα1 t ht ht' =>
    ?_⟩, logU_stronglyMonotone⟩
  have hβ : 0 ≤ 1 - α := by linarith
  have := logU_strict hx hx' hne hα0 hα1
  nlinarith [mul_le_mul_of_nonneg_left ht hα0.le, mul_le_mul_of_nonneg_left ht' hβ]

/-- `logU(0) = 0`. -/
theorem logU_zero : logU 0 = 0 := by simp [logU]

/-- The total endowment is `(2, 2)`. -/
theorem logEconomy_total (l : Fin 2) : logEconomy.totalEndowment l = 2 := by
  fin_cases l <;>
    simp [ExchangeEconomy.totalEndowment, logEconomy, ExchangeEconomy.ofOrthant] <;> norm_num

/-- Every Pareto optimal allocation of `logEconomy` lies on the diagonal of the box:
`x₁ = (a, a)` and `x₂ = (2 - a, 2 - a)`. -/
theorem logEconomy_diag {x : Fin 2 → Fin 2 → ℝ} (hpo : logEconomy.IsParetoOptimal x) :
    x 0 1 = x 0 0 ∧ x 1 0 = 2 - x 0 0 ∧ x 1 1 = 2 - x 0 0 ∧ 0 ≤ x 0 0 := by
  have hbox := hpo.1
  have hxm : ∀ i l, 0 ≤ x i l := fun i l => hbox.1 i l
  have hsum : ∀ l, x 0 l + x 1 l = 2 := fun l => by
    have := congrFun hbox.2 l
    rw [Finset.sum_apply, Fin.sum_univ_two, logEconomy_total] at this
    exact this
  have hdiag : x 0 1 = x 0 0 := by
    by_contra hne
    set a := x 0 0
    set b := x 0 1
    set m := (a + b) / 2 with hm
    have ha := hxm 0 0
    have hb := hxm 0 1
    have ha2 := hxm 1 0
    have hb2 := hxm 1 1
    have h0 := hsum 0
    have h1 := hsum 1
    set x' : Fin 2 → Fin 2 → ℝ := ![![m, m], ![2 - m, 2 - m]] with hx'
    have hbox' : logEconomy.InBox x' := by
      refine ⟨fun i l => ?_, ?_⟩
      · fin_cases i <;> fin_cases l <;> simp [hx', hm] <;> linarith
      · funext l
        rw [Finset.sum_apply, Fin.sum_univ_two, logEconomy_total]
        fin_cases l <;> simp [hx']
    have hu0 : logU (x 0) < logU (x' 0) := by
      have := log1p_strict ha hb (Ne.symm hne) (by norm_num : (0 : ℝ) < 1 / 2)
        (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
      simp only [logU, hx', Matrix.cons_val_zero, Matrix.cons_val_one]
      have e : 1 / 2 * a + 1 / 2 * b = m := by rw [hm]; ring
      rw [e] at this
      linarith
    have hu1 : logU (x 1) < logU (x' 1) := by
      have hne' : 2 - a ≠ 2 - b := fun h => hne (by linarith)
      have := log1p_strict (by linarith : 0 ≤ 2 - a) (by linarith : 0 ≤ 2 - b) hne'
        (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
      have e1 : x 1 0 = 2 - a := by linarith
      have e2 : x 1 1 = 2 - b := by linarith
      simp only [logU, hx', Matrix.cons_val_zero, Matrix.cons_val_one, e1, e2]
      have e : 1 / 2 * (2 - a) + 1 / 2 * (2 - b) = 2 - m := by rw [hm]; ring
      rw [e] at this
      linarith
    refine hpo.2 ⟨x', hbox', fun i => ?_, 0, hu0⟩
    fin_cases i
    · exact hu0.le
    · exact hu1.le
  refine ⟨hdiag, by linarith [hsum 0], by linarith [hsum 1], hxm 0 0⟩

/-- At a diagonal bundle `(c, c)`, `c > 0`, the only normalized price supporting `logU` is
`(1/2, 1/2)`. -/
theorem logU_support_diag {p : Fin 2 → ℝ} (hp : p ∈ priceSimplex 2) {c : ℝ} (hc : 0 < c)
    (hsup : ∀ y ∈ nonnegOrthant 2, logU ![c, c] < logU y → p ⬝ᵥ ![c, c] < p ⬝ᵥ y) :
    p = ![1 / 2, 1 / 2] := by
  have hp0 := hp.1 0
  have hp1 := hp.1 1
  have hs : p 0 + p 1 = 1 := by
    have := hp.2
    rwa [Fin.sum_univ_two] at this
  have hdot : ∀ a b : ℝ, p ⬝ᵥ ![a, b] = p 0 * a + p 1 * b := fun a b => by
    simp [dotProduct, Fin.sum_univ_two]
  have hlog : ∀ a b : ℝ, 0 < 1 + a → 0 < 1 + b →
      (1 + c) * (1 + c) < (1 + a) * (1 + b) → logU ![c, c] < logU ![a, b] := by
    intro a b ha hb hlt
    simp only [logU, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← Real.log_mul (by linarith) (by linarith), ← Real.log_mul ha.ne' hb.ne']
    exact Real.log_lt_log (by positivity) hlt
  have heq : p 0 = p 1 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · set ε := min c ((1 + c) * (p 1 - p 0) / 2) with hε
      have hε0 : 0 < ε := lt_min hc (by nlinarith)
      have hεc : ε ≤ c := min_le_left _ _
      have hε2 : ε ≤ (1 + c) * (p 1 - p 0) / 2 := min_le_right _ _
      have hy : ![c + ε * p 1, c - ε * p 0] ∈ nonnegOrthant 2 := by
        intro l
        fin_cases l <;> simp <;> nlinarith
      have hpp : p 0 * p 1 ≤ 1 := by nlinarith
      have key : ε * (p 0 * p 1) < (1 + c) * (p 1 - p 0) := by
        calc ε * (p 0 * p 1) ≤ ε * 1 := mul_le_mul_of_nonneg_left hpp hε0.le
          _ ≤ (1 + c) * (p 1 - p 0) / 2 := by linarith
          _ < (1 + c) * (p 1 - p 0) := by nlinarith
      have hprod : (1 + c) * (1 + c) < (1 + (c + ε * p 1)) * (1 + (c - ε * p 0)) := by
        nlinarith [mul_lt_mul_of_pos_left key hε0]
      have hlt := hsup _ hy (hlog _ _ (by nlinarith) (by nlinarith) hprod)
      rw [hdot, hdot] at hlt
      nlinarith
    · set ε := min c ((1 + c) * (p 0 - p 1) / 2) with hε
      have hε0 : 0 < ε := lt_min hc (by nlinarith)
      have hεc : ε ≤ c := min_le_left _ _
      have hε2 : ε ≤ (1 + c) * (p 0 - p 1) / 2 := min_le_right _ _
      have hy : ![c - ε * p 1, c + ε * p 0] ∈ nonnegOrthant 2 := by
        intro l
        fin_cases l <;> simp <;> nlinarith
      have hpp : p 0 * p 1 ≤ 1 := by nlinarith
      have key : ε * (p 0 * p 1) < (1 + c) * (p 0 - p 1) := by
        calc ε * (p 0 * p 1) ≤ ε * 1 := mul_le_mul_of_nonneg_left hpp hε0.le
          _ ≤ (1 + c) * (p 0 - p 1) / 2 := by linarith
          _ < (1 + c) * (p 0 - p 1) := by nlinarith
      have hprod : (1 + c) * (1 + c) < (1 + (c - ε * p 1)) * (1 + (c + ε * p 0)) := by
        nlinarith [mul_lt_mul_of_pos_left key hε0]
      have hlt := hsup _ hy (hlog _ _ (by nlinarith) (by nlinarith) hprod)
      rw [hdot, hdot] at hlt
      nlinarith
  funext l
  fin_cases l <;> simp <;> linarith

/-- In `logEconomy`, every Pareto optimal allocation has exactly one normalized supporting
price, `(1/2, 1/2)`. -/
theorem logEconomy_support_unique {x : Fin 2 → Fin 2 → ℝ} (hpo : logEconomy.IsParetoOptimal x)
    {p : Fin 2 → ℝ} (hp : p ∈ priceSimplex 2) (hsup : IsSupportingPrice logEconomy x p) :
    p = ![1 / 2, 1 / 2] := by
  obtain ⟨h01, h10, h11, ha⟩ := logEconomy_diag hpo
  rcases ha.lt_or_eq with ha | ha
  · have hx0 : x 0 = ![x 0 0, x 0 0] := by
      funext l
      fin_cases l
      · rfl
      · exact h01
    refine logU_support_diag hp ha fun y hy hlt => ?_
    rw [← hx0]
    exact hsup 0 y hy (by rw [hx0]; exact hlt)
  · have hx1 : x 1 = ![2, 2] := by
      funext l
      fin_cases l
      · simp [h10, ← ha]
      · simp [h11, ← ha]
    refine logU_support_diag hp two_pos fun y hy hlt => ?_
    rw [← hx1]
    exact hsup 1 y hy (by rw [hx1]; exact hlt)

/-- **Exercise 17.AA.2** (MWG, p. 649): the hypotheses hold for `logEconomy`. -/
theorem logEconomy_negishiHyp : NegishiHyp logEconomy := by
  have hstd : ∀ i, StandardUtility (logEconomy.u i) := fun _ => logU_standard
  refine ⟨two_pos, two_pos, fun _ => rfl, hstd, fun _ => logU_zero, ?_, ?_⟩
  · intro i l
    fin_cases i <;> fin_cases l <;> simp [logEconomy, ExchangeEconomy.ofOrthant]
  · intro s hs p q hp hq hsp hsq
    have hpo := (negishiAlloc_spec (E := logEconomy) (fun _ => rfl) (fun i => (hstd i).1)
      (fun i => (hstd i).2.2) (fun _ => logU_zero)
      (fun i l => by
        fin_cases i <;> fin_cases l <;> simp [logEconomy, ExchangeEconomy.ofOrthant] <;>
          norm_num) hs).1
    rw [logEconomy_support_unique hpo hp hsp, logEconomy_support_unique hpo hq hsq]

/-- **Exercise 17.AA.2(d)** (MWG, p. 649), instance: the welfare equations of `logEconomy` have a
solution `s* ∈ Δ`, and `(x(s*), p(s*))` is a Walrasian equilibrium. -/
theorem exercise_17_AA_2_instance :
    ∃ s ∈ priceSimplex 2, negishiG logEconomy s = 0 ∧
      logEconomy.IsWalrasEqm (negishiPrice logEconomy s) (negishiAlloc logEconomy s) :=
  exercise_17_AA_2d logEconomy_negishiHyp

end MWG.PositiveEquilibriumTheory
