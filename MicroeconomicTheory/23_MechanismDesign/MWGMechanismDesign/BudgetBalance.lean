/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGMechanismDesign.Quasilinear
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-!
# Groves mechanisms and budget balance

MWG, Section 23.C, pp. 880-881, Proposition 23.C.6 (Green and Laffont; proof omitted in MWG),
and Exercise 23.C.10(a)-(b) (Holmstrom, p. 920).

`V*(θ) = ∑ᵢ vᵢ(k*(θ), θᵢ)` is the maximal total valuation.

* **Exercise 23.C.10(a)**: if `V*(θ) = ∑ᵢ Vᵢ(θ₋ᵢ)`, the Groves scheme with
  `hᵢ = -(I - 1)Vᵢ` is efficient, budget balanced and strategy-proof (`exercise_23_C_10a_if`).
  Conversely, under the richness hypothesis of Proposition 23.C.5 and with at least two agents,
  an efficient, budget balanced, strategy-proof `f` forces such a decomposition
  (`exercise_23_C_10a_only_if`). The "only if" needs `I ≥ 2`: with one agent `t = 0` works
  for every `V*` (`exercise_23_C_10a_only_if_false_one_agent`).
* `mixedDifference_eq_zero`: a sum of functions each independent of one coordinate has zero
  `I`-fold mixed difference.
* **Proposition 23.C.6**: with every valuation function possible, at least two agents and at
  least two projects, no strategy-proof social choice function satisfies (23.C.7) and (23.C.12)
  (`proposition_23_C_6`); the proof exhibits types whose maximal total valuation has nonzero
  mixed difference. **Correction**: MWG state it without `I ≥ 2` and `|K| ≥ 2`; with one
  project or one agent, `t = 0` is an efficient, budget balanced, strategy-proof rule
  (`proposition_23_C_6_false_one_project`, `proposition_23_C_6_false_one_agent`).
* **Exercise 23.C.10(b)**: with `I ≥ 3`, `K = ℝ` and `vᵢ(k, θᵢ) = θᵢk - k²/2`, an efficient,
  budget balanced, strategy-proof rule exists (for real types, hence for `Θᵢ = ℝ₊`).
-/

namespace MWG.MechanismDesign

open Function Finset

variable {ι : Type*} {Θ : ι → Type*} {K : Type*}

/-- `∑ᵢ ∑_{j≠i} gⱼ = (I - 1) ∑ⱼ gⱼ`. -/
theorem sum_sum_erase [Fintype ι] [DecidableEq ι] (g : ι → ℝ) :
    ∑ i, ∑ j ∈ univ.erase i, g j = (Fintype.card ι - 1) * ∑ j, g j := by
  simp only [sum_erase_eq_sub (mem_univ _), sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul]
  ring

/-- The total transfer of a Groves scheme: `∑ᵢ tᵢ(θ) = (I - 1)V*(θ) + ∑ᵢ hᵢ(θ)`. -/
theorem sum_grovesTransfer [Fintype ι] [DecidableEq ι] (v : (i : ι) → K → Θ i → ℝ)
    (k : ((i : ι) → Θ i) → K) (h : (i : ι) → ((j : ι) → Θ j) → ℝ) (θ : (i : ι) → Θ i) :
    ∑ i, grovesTransfer v k h θ i =
      (Fintype.card ι - 1) * ∑ j, v j (k θ) (θ j) + ∑ i, h i θ := by
  simp only [grovesTransfer, sum_add_distrib]
  rw [sum_sum_erase (fun j => v j (k θ) (θ j))]

/-- **Exercise 23.C.10(a)** (MWG, p. 920), "if". If `V*(θ) = ∑ᵢ Vᵢ(θ₋ᵢ)`, there is an ex post
efficient (efficient project and budget balanced) social choice function truthfully
implementable in dominant strategies: the Groves scheme with `hᵢ = -(I - 1)Vᵢ`. -/
theorem exercise_23_C_10a_if [Fintype ι] [DecidableEq ι] {v : (i : ι) → K → Θ i → ℝ}
    (m : ι → ℝ) {k : ((i : ι) → Θ i) → K} (hk : EfficientProject v k)
    (V : (i : ι) → ((j : ι) → Θ j) → ℝ) (hV : IndepOwn V)
    (hdec : ∀ θ, ∑ i, v i (k θ) (θ i) = ∑ i, V i θ) :
    ∃ t : ((i : ι) → Θ i) → ι → ℝ,
      StrategyProof (qlU v m) (fun θ => (k θ, t θ)) ∧ BudgetBalanced t := by
  refine ⟨grovesTransfer v k fun i θ => -((Fintype.card ι : ℝ) - 1) * V i θ,
    proposition_23_C_4 m hk fun i θ a => by simp only [hV i θ a], fun θ => ?_⟩
  rw [sum_grovesTransfer, hdec θ, ← mul_sum]
  ring

/-- **Exercise 23.C.10(a)** (MWG, p. 920), "only if", under the richness hypothesis of
Proposition 23.C.5 and with at least two agents: if an efficient project rule is part of a
budget balanced, strategy-proof social choice function, then `V*(θ) = ∑ᵢ Vᵢ(θ₋ᵢ)`. -/
theorem exercise_23_C_10a_only_if [Fintype ι] [DecidableEq ι] (hI : 2 ≤ Fintype.card ι)
    {v : (i : ι) → K → Θ i → ℝ} (m : ι → ℝ)
    (hrich : ∀ i (w : K → ℝ), ∃ θi : Θ i, ∀ k, v i k θi = w k)
    {k : ((i : ι) → Θ i) → K} (hk : EfficientProject v k) {t : ((i : ι) → Θ i) → ι → ℝ}
    (hSP : StrategyProof (qlU v m) (fun θ => (k θ, t θ))) (hBB : BudgetBalanced t) :
    ∃ V : (i : ι) → ((j : ι) → Θ j) → ℝ, IndepOwn V ∧
      ∀ θ, ∑ i, v i (k θ) (θ i) = ∑ i, V i θ := by
  obtain ⟨h, hh, ht⟩ := proposition_23_C_5 m hrich hk hSP
  have hI' : (1 : ℝ) < Fintype.card ι := by exact_mod_cast hI
  refine ⟨fun i θ => -h i θ / ((Fintype.card ι : ℝ) - 1), fun i θ a => by simp [hh i θ a],
    fun θ => ?_⟩
  have h0 := hBB θ
  rw [ht θ, sum_grovesTransfer] at h0
  have hne : ((Fintype.card ι : ℝ) - 1) ≠ 0 := by linarith
  rw [← sum_div, sum_neg_distrib, eq_div_iff hne]
  linarith

/-- **Exercise 23.C.10(a)**, correction: the "only if" fails with one agent. With one agent,
projects `Bool`, every valuation possible, and the efficient rule, `t = 0` is strategy-proof and
budget balanced, while `V*` is not a function of `θ₋₁` (which is trivial). -/
theorem exercise_23_C_10a_only_if_false_one_agent :
    let v : Unit → Bool → (Bool → ℝ) → ℝ := fun _ k θ => θ k
    let k : (Unit → Bool → ℝ) → Bool := fun θ => decide (θ () false ≤ θ () true)
    EfficientProject (ι := Unit) (Θ := fun _ => Bool → ℝ) v k ∧
      StrategyProof (qlU (ι := Unit) (Θ := fun _ => Bool → ℝ) v 0) (fun θ => (k θ, fun _ => 0)) ∧
      BudgetBalanced (ι := Unit) (Θ := fun _ => Bool → ℝ) (fun _ _ => (0 : ℝ)) ∧
      ¬∃ V : Unit → (Unit → Bool → ℝ) → ℝ, IndepOwn (ι := Unit) (Θ := fun _ => Bool → ℝ) V ∧
        ∀ θ, ∑ i, v i (k θ) (θ i) = ∑ i, V i θ := by
  intro v k
  have hk : ∀ (θ : Unit → Bool → ℝ) (b : Bool), θ () b ≤ θ () (k θ) := by
    intro θ b
    by_cases h : θ () false ≤ θ () true
    · cases b <;> simp [k, h]
    · cases b <;> simp [k, h]
      all_goals linarith
  refine ⟨fun θ b => by simpa [v] using hk θ b, fun i θ θh => ?_, fun _ => by simp, ?_⟩
  · simp only [qlU, v, Pi.zero_apply, add_zero]
    exact hk θ _
  · rintro ⟨V, hV, hdec⟩
    have e0 := hdec fun _ _ => 0
    have e1 := hdec fun _ b => if b then 1 else 0
    have hc : V () (fun _ b => if b then 1 else 0) = V () fun _ _ => 0 := by
      have := hV () (fun _ _ => 0) (fun b => if b then 1 else 0)
      rw [show update (fun _ _ => (0 : ℝ)) () (fun b : Bool => if b then (1 : ℝ) else 0) =
        fun _ b => if b then 1 else 0 from funext fun _ => rfl] at this
      exact this
    simp only [v, k, Finset.univ_unique, sum_singleton] at e0 e1
    norm_num at e0 e1
    linarith

/-- The profile using `θ¹` on `S` and `θ⁰` off `S`. -/
def mixProfile [DecidableEq ι] (θ0 θ1 : (i : ι) → Θ i) (S : Finset ι) : (i : ι) → Θ i :=
  fun j => if j ∈ S then θ1 j else θ0 j

/-- A function independent of `θᵢ` has zero alternating sum over the subsets (the `i`-th
difference vanishes). -/
theorem alternating_sum_indepOwn [Fintype ι] [DecidableEq ι] (θ0 θ1 : (i : ι) → Θ i) (i : ι)
    (g : ((j : ι) → Θ j) → ℝ) (hg : ∀ θ (a : Θ i), g (update θ i a) = g θ) :
    ∑ S ∈ (univ : Finset ι).powerset, (-1 : ℝ) ^ S.card * g (mixProfile θ0 θ1 S) = 0 := by
  have hu : (univ : Finset ι) = insert i (univ.erase i) := (insert_erase (mem_univ i)).symm
  rw [hu, sum_powerset_insert (notMem_erase i univ)]
  rw [← sum_add_distrib]
  refine sum_eq_zero fun S hS => ?_
  have hiS : i ∉ S := fun h => (notMem_erase i univ) (mem_powerset.1 hS h)
  have hmix : mixProfile θ0 θ1 (insert i S) = update (mixProfile θ0 θ1 S) i (θ1 i) := by
    funext j
    by_cases hj : j = i
    · subst hj; simp [mixProfile]
    · simp [mixProfile, hj]
  rw [hmix, hg, card_insert_of_notMem hiS, pow_succ]
  ring

/-- The `I`-fold mixed difference of `∑ᵢ Vᵢ(θ₋ᵢ)` vanishes. -/
theorem mixedDifference_eq_zero [Fintype ι] [DecidableEq ι] (θ0 θ1 : (i : ι) → Θ i)
    (V : (i : ι) → ((j : ι) → Θ j) → ℝ) (hV : IndepOwn V) :
    ∑ S ∈ (univ : Finset ι).powerset, (-1 : ℝ) ^ S.card * ∑ i, V i (mixProfile θ0 θ1 S) = 0 := by
  simp only [mul_sum]
  rw [sum_comm]
  exact sum_eq_zero fun i _ => alternating_sum_indepOwn θ0 θ1 i (V i) (hV i)

/-- **Proposition 23.C.6** (Green and Laffont; MWG, p. 880; proof omitted in MWG). Suppose every
valuation function `K → ℝ` arises for some type of each agent. With at least two agents and at
least two projects, no social choice function `f = (k*, t)` truthfully implementable in dominant
strategies satisfies both (23.C.7) and (23.C.12). (The hypotheses `I ≥ 2` and `|K| ≥ 2` are
needed: see `proposition_23_C_6_false_one_project` and `proposition_23_C_6_false_one_agent`.) -/
theorem proposition_23_C_6 [Fintype ι] [DecidableEq ι] (hI : 2 ≤ Fintype.card ι) {a b : K}
    (hab : a ≠ b) {v : (i : ι) → K → Θ i → ℝ} (m : ι → ℝ)
    (hrich : ∀ i (w : K → ℝ), ∃ θi : Θ i, ∀ k, v i k θi = w k)
    {k : ((i : ι) → Θ i) → K} (hk : EfficientProject v k) {t : ((i : ι) → Θ i) → ι → ℝ}
    (hSP : StrategyProof (qlU v m) (fun θ => (k θ, t θ))) : ¬BudgetBalanced t := by
  classical
  intro hBB
  obtain ⟨V, hV, hdec⟩ := exercise_23_C_10a_only_if hI m hrich hk hSP hBB
  set n : ℝ := (Fintype.card ι : ℝ) with hn
  have hn1 : (1 : ℝ) < n := by rw [hn]; exact_mod_cast hI
  -- two types for every agent
  obtain ⟨θ0, hθ0⟩ := (show ∃ θ0 : (i : ι) → Θ i, ∀ i k', v i k' (θ0 i) =
      if k' = a then 0 else if k' = b then -n else -1 from
    ⟨fun i => (hrich i _).choose, fun i => (hrich i _).choose_spec⟩)
  obtain ⟨θ1, hθ1⟩ := (show ∃ θ1 : (i : ι) → Θ i, ∀ i k', v i k' (θ1 i) =
      if k' = a then 0 else if k' = b then 1 else -1 from
    ⟨fun i => (hrich i _).choose, fun i => (hrich i _).choose_spec⟩)
  -- total valuations at the mixed profiles
  have htot : ∀ (S : Finset ι) k', ∑ i, v i k' (mixProfile θ0 θ1 S i) =
      if k' = a then 0 else if k' = b then (n + 1) * S.card - n ^ 2 else -n := by
    intro S k'
    have hcard : ∑ i : ι, (if i ∈ S then (1 : ℝ) else 0) = S.card := by
      rw [sum_boole, filter_mem_eq_inter, univ_inter]
    have e : ∀ i, v i k' (mixProfile θ0 θ1 S i) = if k' = a then 0 else if k' = b then
        (n + 1) * (if i ∈ S then 1 else 0) - n else -1 := by
      intro i
      by_cases hi : i ∈ S
      · simp only [mixProfile, hi, ite_true, hθ1]; split_ifs <;> ring
      · simp only [mixProfile, hi, ite_false, hθ0]; split_ifs <;> ring
    simp only [e]
    by_cases ha : k' = a
    · simp [ha]
    · by_cases hb : k' = b
      · simp only [hb, Ne.symm hab, ite_false, ite_true]
        rw [sum_sub_distrib, ← mul_sum, hcard, sum_const, card_univ, nsmul_eq_mul, ← hn]
        ring
      · simp [ha, hb, hn]
  -- the maximal total valuation
  have hVstar : ∀ S : Finset ι, ∑ i, v i (k (mixProfile θ0 θ1 S)) (mixProfile θ0 θ1 S i) =
      if S = univ then n else 0 := by
    intro S
    have hS : (S.card : ℝ) ≤ n := by rw [hn]; exact_mod_cast card_le_univ S
    have ha := hk (mixProfile θ0 θ1 S) a
    have hb := hk (mixProfile θ0 θ1 S) b
    rw [htot] at ha hb ⊢
    rw [htot] at ha hb
    simp only [ite_true, Ne.symm hab, ite_false] at ha hb
    by_cases hSu : S = univ
    · have hc : (S.card : ℝ) = n := by rw [hSu, hn, card_univ]
      rw [hc] at ha hb
      simp only [hSu, ite_true]
      subst hSu
      split_ifs at ha hb ⊢ with h1 h2 <;> nlinarith
    · have hlt : (S.card : ℝ) ≤ n - 1 := by
        have : S.card < Fintype.card ι := by
          obtain ⟨i, hi⟩ : ∃ i, i ∉ S := by
            by_contra hall
            exact hSu (eq_univ_of_forall fun i => not_not.1 fun h => hall ⟨i, h⟩)
          exact card_lt_univ_of_notMem hi
        have : (S.card : ℝ) + 1 ≤ n := by rw [hn]; exact_mod_cast this
        linarith
      simp only [hSu, ite_false]
      split_ifs at ha hb ⊢ with h1 h2
      · rfl
      · nlinarith
      · linarith
  have hmix := mixedDifference_eq_zero θ0 θ1 V hV
  simp only [← hdec, hVstar] at hmix
  rw [sum_eq_single univ (fun S _ hS => by simp [hS]) (fun h => absurd (mem_powerset_self _) h)]
    at hmix
  simp only [ite_true, card_univ] at hmix
  have : (-1 : ℝ) ^ Fintype.card ι ≠ 0 := pow_ne_zero _ (by norm_num)
  have hn0 : n ≠ 0 := by linarith
  exact (mul_ne_zero this hn0) hmix

/-- **Proposition 23.C.6**, correction: with a single project the conclusion fails. Every
valuation `Unit → ℝ` arises, the constant project is efficient, and `t = 0` is strategy-proof
and budget balanced. -/
theorem proposition_23_C_6_false_one_project :
    let v : Fin 2 → Unit → (Unit → ℝ) → ℝ := fun _ k θ => θ k
    (∀ i (w : Unit → ℝ), ∃ θi : Unit → ℝ, ∀ k, v i k θi = w k) ∧
      EfficientProject (ι := Fin 2) (Θ := fun _ => Unit → ℝ) v (fun _ => ()) ∧
      StrategyProof (qlU (ι := Fin 2) (Θ := fun _ => Unit → ℝ) v 0) (fun _ => ((), fun _ => 0)) ∧
      BudgetBalanced (ι := Fin 2) (Θ := fun _ => Unit → ℝ) (fun _ _ => (0 : ℝ)) := by
  intro v
  exact ⟨fun _ w => ⟨w, fun _ => rfl⟩, fun _ _ => le_rfl, fun _ _ _ => le_rfl,
    fun _ => by simp⟩

/-- **Proposition 23.C.6**, correction: with a single agent the conclusion fails (every valuation
arises, the efficient rule with `t = 0` is strategy-proof and budget balanced). -/
theorem proposition_23_C_6_false_one_agent :
    let v : Unit → Bool → (Bool → ℝ) → ℝ := fun _ k θ => θ k
    let k : (Unit → Bool → ℝ) → Bool := fun θ => decide (θ () false ≤ θ () true)
    (∀ i (w : Bool → ℝ), ∃ θi : Bool → ℝ, ∀ k, v i k θi = w k) ∧
      EfficientProject (ι := Unit) (Θ := fun _ => Bool → ℝ) v k ∧
      StrategyProof (qlU (ι := Unit) (Θ := fun _ => Bool → ℝ) v 0) (fun θ => (k θ, fun _ => 0)) ∧
      BudgetBalanced (ι := Unit) (Θ := fun _ => Bool → ℝ) (fun _ _ => (0 : ℝ)) := by
  intro v k
  obtain ⟨h1, h2, h3, -⟩ := exercise_23_C_10a_only_if_false_one_agent
  exact ⟨fun _ w => ⟨w, fun _ => rfl⟩, h1, h2, h3⟩

/-- The quadratic valuations of Exercise 23.C.10(b): `vᵢ(k, θᵢ) = gᵢ(θᵢ)k - k²/2`, where
`gᵢ(θᵢ) ∈ ℝ` is the real type (the identity for `Θᵢ = ℝ`, the inclusion for `Θᵢ = ℝ₊`). -/
noncomputable def quadV (g : (i : ι) → Θ i → ℝ) : (i : ι) → ℝ → Θ i → ℝ :=
  fun i k θi => g i θi * k - k ^ 2 / 2

/-- **Exercise 23.C.10(b)** (MWG, p. 920). With `I ≥ 3` agents, `K = ℝ` and
`vᵢ(k, θᵢ) = θᵢk - k²/2` (types given by any real-valued `gᵢ`, e.g. `Θᵢ = ℝ` or `Θᵢ = ℝ₊`),
`k*(θ) = ∑ᵢθᵢ/I` is efficient, `V*(θ) = (∑ᵢθᵢ)²/(2I)` decomposes as `∑ᵢ Vᵢ(θ₋ᵢ)`, and hence an
ex post efficient, strategy-proof social choice function exists. MWG ask for `I = 3` and remark
that the result extends to any `I > 2`; both are covered. -/
theorem exercise_23_C_10b [Fintype ι] [DecidableEq ι] (hI : 3 ≤ Fintype.card ι)
    (g : (i : ι) → Θ i → ℝ) (m : ι → ℝ) :
    EfficientProject (quadV g) (fun θ => (∑ i, g i (θ i)) / Fintype.card ι) ∧
      ∃ t : ((i : ι) → Θ i) → ι → ℝ,
        StrategyProof (qlU (quadV g) m)
          (fun θ => ((∑ i, g i (θ i)) / Fintype.card ι, t θ)) ∧ BudgetBalanced t := by
  set n : ℝ := (Fintype.card ι : ℝ) with hn
  have hn3 : (3 : ℝ) ≤ n := by rw [hn]; exact_mod_cast hI
  have hk : EfficientProject (quadV g) (fun θ => (∑ i, g i (θ i)) / n) := by
    intro θ k'
    simp only [quadV, sum_sub_distrib, ← sum_mul, sum_const, card_univ, nsmul_eq_mul, ← hn]
    set s := ∑ i, g i (θ i)
    have : 0 ≤ (n * k' - s) ^ 2 / (2 * n) := by positivity
    have e : s * (s / n) - n * ((s / n) ^ 2 / 2) - (s * k' - n * (k' ^ 2 / 2)) =
        (n * k' - s) ^ 2 / (2 * n) := by field_simp; ring
    linarith
  refine ⟨hk, exercise_23_C_10a_if m hk (fun i θ =>
    ((∑ j ∈ univ.erase i, g j (θ j)) ^ 2 - (∑ j ∈ univ.erase i, g j (θ j) ^ 2) / (n - 1)) /
      (2 * n * (n - 2))) (fun i θ a => ?_) (fun θ => ?_)⟩
  · have e1 : ∑ j ∈ univ.erase i, g j (update θ i a j) = ∑ j ∈ univ.erase i, g j (θ j) :=
      sum_congr rfl fun j hj => by rw [update_of_ne (ne_of_mem_erase hj)]
    have e2 : ∑ j ∈ univ.erase i, g j (update θ i a j) ^ 2 =
        ∑ j ∈ univ.erase i, g j (θ j) ^ 2 :=
      sum_congr rfl fun j hj => by rw [update_of_ne (ne_of_mem_erase hj)]
    simp only [e1, e2]
  · have hn0 : n ≠ 0 := by linarith
    have hn1 : n - 1 ≠ 0 := by intro h; linarith
    have hn2 : n - 2 ≠ 0 := by intro h; linarith
    obtain ⟨s, hsd⟩ : ∃ s, ∑ i, g i (θ i) = s := ⟨_, rfl⟩
    obtain ⟨q, hqd⟩ : ∃ q, ∑ i, g i (θ i) ^ 2 = q := ⟨_, rfl⟩
    have hs : ∀ i, ∑ j ∈ univ.erase i, g j (θ j) = s - g i (θ i) := fun i => by
      rw [sum_erase_eq_sub (mem_univ i), hsd]
    have hq : ∀ i, ∑ j ∈ univ.erase i, g j (θ j) ^ 2 = q - g i (θ i) ^ 2 := fun i => by
      rw [sum_erase_eq_sub (mem_univ i), hqd]
    simp only [quadV, hsd, hs, hq, ← sum_div]
    have h1 : ∑ i, ((s - g i (θ i)) ^ 2 - (q - g i (θ i) ^ 2) / (n - 1)) =
        (n - 2) * s ^ 2 := by
      have : ∀ i, (s - g i (θ i)) ^ 2 - (q - g i (θ i) ^ 2) / (n - 1) =
          s ^ 2 - 2 * s * g i (θ i) + g i (θ i) ^ 2 - q / (n - 1) +
            g i (θ i) ^ 2 / (n - 1) := fun i => by ring
      simp only [this, sum_add_distrib, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul,
        ← hn, ← mul_sum, ← sum_div, hsd, hqd]
      field_simp
      ring
    rw [h1, sum_sub_distrib, ← sum_mul, sum_const, card_univ, nsmul_eq_mul, ← hn, hsd]
    field_simp
    ring

end MWG.MechanismDesign
