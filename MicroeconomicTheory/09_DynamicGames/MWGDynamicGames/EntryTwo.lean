/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGDynamicGames.Entry
import MWGDynamicGames.Beliefs
import Mathlib.Tactic.LinearCombination

/-!
# Entry with two entry strategies

MWG, Examples 9.C.1 and 9.C.3 (Figures 9.C.1 and 9.C.3, pp. 282-288) and Exercise 9.C.2.

The entrant E chooses Out (`0`), In₁ (`1`) or In₂ (`2`); the incumbent I observes entry but not
which entry strategy was used, and chooses Fight (`0`) or Accommodate (`1`) at its single
information set `1` = `{[1], [2]}`. `entryTwo o t` has payoffs `o` after Out and `t e f` after
entry strategy `e` (`0` = In₁, `1` = In₂) and response `f`.

* `example_9_C_1_nash`, `example_9_C_1_spne`: in Figure 9.C.1 both (out, fight) and
  (in₁, accommodate) are Nash equilibria, and as the only subgame is the whole game both are
  subgame perfect.
* `example_9_C_1_weakPBE`: (in₁, accommodate) with belief `1` on the left node is the unique
  weak perfect Bayesian equilibrium, pure or mixed; (out, fight) is part of no weak PBE.
* `example_9_C_3`: in Figure 9.C.3 with `γ > 0` the unique weak PBE has E playing
  `(0, 2/3, 1/3)`, I fighting with probability `1/(γ + 2)` and `μ₁ = 2/3`.
* `exercise_9_C_2`: for `γ ∈ (−1, 0)` every weak PBE has E staying out with I fighting with
  probability at least `max(3/4, 2/(2 − γ))` and `μ₁ ≥ 2/3` (with `μ₁ = 2/3` unless I fights
  for sure), or (for `γ ≥ −2/3`) E entering with In₁ twice as likely as In₂, I fighting with
  probability `1/(γ + 2)` and `μ₁ = 2/3`; each of these is a weak PBE.
-/

namespace MWG.DynamicGames

open MWG.NoncooperativeGames MWG.NoncooperativeGames.ExtensiveForm

/-- Payoffs of the entry game with two entry strategies. -/
def entryTwoPay (o : Fin 2 → ℝ) (t : Fin 2 → Fin 2 → Fin 2 → ℝ) (i : Fin 2)
    (z : List (Fin 3)) : ℝ :=
  if z = [0] then o i else if z = [0, 1] then t 0 0 i else if z = [1, 1] then t 0 1 i
  else if z = [0, 2] then t 1 0 i else if z = [1, 2] then t 1 1 i else 0

/-- The entry game with two entry strategies (Figures 9.C.1, 9.C.3, 9.D.1(a), 9.BB.2). -/
def entryTwo (o : Fin 2 → ℝ) (t : Fin 2 → Fin 2 → Fin 2 → ℝ) :
    ExtensiveForm (Fin 2) (Fin 3) (Fin 2) where
  nodes := {[], [0], [1], [2], [0, 1], [1, 1], [0, 2], [1, 2]}
  nil_mem := by decide
  tail_mem := by decide
  info x := if x = [] then 0 else 1
  avail k := if k = 0 then Finset.univ else {0, 1}
  avail_spec := by decide
  info_surj := by decide
  player k := some k
  natureProb _ _ := 0
  nature_nonneg := fun _ hk => absurd hk (by simp)
  nature_zero := fun _ hk => absurd hk (by simp)
  nature_sum := fun _ hk => absurd hk (by simp)
  payoff := entryTwoPay o t

variable (o : Fin 2 → ℝ) (t : Fin 2 → Fin 2 → Fin 2 → ℝ)

theorem entryTwo_assemble (F : Fin 2 → Fin 2 → Fin 3 → ℝ) (k : Fin 2) :
    (entryTwo o t).assemble F k = F k k := (entryTwo o t).assemble_of_some F rfl

/-- Continuation payoffs in the entry game with two entry strategies. -/
theorem entryTwo_cont (f : Fin 2 → Fin 3 → ℝ) (i : Fin 2) :
    cont (entryTwo o t) f [1] i = f 1 0 * t 0 0 i + f 1 1 * t 0 1 i ∧
    cont (entryTwo o t) f [2] i = f 1 0 * t 1 0 i + f 1 1 * t 1 1 i ∧
    cont (entryTwo o t) f [] i = f 0 0 * o i + f 0 1 * (f 1 0 * t 0 0 i + f 1 1 * t 0 1 i) +
      f 0 2 * (f 1 0 * t 1 0 i + f 1 1 * t 1 1 i) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [cont_unfold, entryTwo, entryTwoPay, Fin.sum_univ_three]

theorem entryTwo_infoSet : (entryTwo o t).infoSet 0 = {[]} ∧
    (entryTwo o t).infoSet 1 = {[1], [2]} :=
  ⟨(by decide : (entryTwo (fun _ => 0) (fun _ _ _ => 0)).infoSet 0 = {[]}),
    (by decide : (entryTwo (fun _ => 0) (fun _ _ _ => 0)).infoSet 1 = {[1], [2]})⟩

/-- Expected payoffs at the two information sets given beliefs `μ`. -/
theorem entryTwo_condPayoff (f : Fin 2 → Fin 3 → ℝ) (μ : List (Fin 3) → ℝ) (i : Fin 2) :
    condPayoff (entryTwo o t) f μ 0 i = μ [] * cont (entryTwo o t) f [] i ∧
    condPayoff (entryTwo o t) f μ 1 i =
      μ [1] * cont (entryTwo o t) f [1] i + μ [2] * cont (entryTwo o t) f [2] i := by
  unfold condPayoff
  rw [(entryTwo_infoSet o t).1, (entryTwo_infoSet o t).2]
  simp

theorem entryTwo_reach (f : Fin 2 → Fin 3 → ℝ) :
    (entryTwo o t).reach f [1] = f 0 1 ∧ (entryTwo o t).reach f [2] = f 0 2 ∧
      probInfo (entryTwo o t) f 1 = f 0 1 + f 0 2 := by
  refine ⟨by simp [entryTwo], by simp [entryTwo], ?_⟩
  unfold probInfo
  rw [(entryTwo_infoSet o t).2]
  simp [entryTwo]

/-- Facts about a behaviour profile of the game. -/
theorem entryTwo_behavior {F : Fin 2 → Fin 2 → Fin 3 → ℝ}
    (hF : IsBehaviorProfile (entryTwo o t) F) :
    (∀ a, 0 ≤ F 0 0 a) ∧ F 0 0 0 + F 0 0 1 + F 0 0 2 = 1 ∧ (∀ a, 0 ≤ F 1 1 a) ∧
      F 1 1 0 + F 1 1 1 = 1 := by
  have h0 := hF 0 0 rfl
  have h1 := hF 1 1 rfl
  exact ⟨h0.1, by simpa [entryTwo, Fin.sum_univ_three] using h0.2.2, h1.1,
    by simpa [entryTwo] using h1.2.2⟩

/-- A behaviour strategy of `E` or `I` sending probability one to `a` at its own information
set. -/
theorem entryTwo_dirac_beh (i : Fin 2) {a : Fin 3} (ha : a ∈ (entryTwo o t).avail i) :
    (entryTwo o t).IsBehaviorStrategy i (fun _ => dirac a) := by
  intro k hk
  have hki : k = i := by simpa [entryTwo] using hk
  subst hki
  refine ⟨fun b => by beta_reduce; unfold dirac; split_ifs <;> norm_num, fun b hb => ?_, ?_⟩
  · have : b ≠ a := fun h => hb (h ▸ ha)
    simp [dirac, this]
  · simp only [dirac]
    rw [Finset.sum_ite_eq']
    simp [ha]

/-- The payoffs of Figure 9.C.1 after entry: `(u_E, u_I)` = (−1, −1), (3, 0), (−1, −1),
(2, 1). -/
abbrev fig9C1 : ExtensiveForm (Fin 2) (Fin 3) (Fin 2) :=
  entryTwo ![0, 2] ![![![-1, -1], ![3, 0]], ![![-1, -1], ![2, 1]]]

theorem entryTwo_beh0 {g : Fin 2 → Fin 3 → ℝ} (hg : (entryTwo o t).IsBehaviorStrategy 0 g) :
    (∀ a, 0 ≤ g 0 a) ∧ g 0 0 + g 0 1 + g 0 2 = 1 :=
  ⟨(hg 0 rfl).1, by simpa [entryTwo, Fin.sum_univ_three] using (hg 0 rfl).2.2⟩

theorem entryTwo_beh1 {g : Fin 2 → Fin 3 → ℝ} (hg : (entryTwo o t).IsBehaviorStrategy 1 g) :
    (∀ a, 0 ≤ g 1 a) ∧ g 1 0 + g 1 1 = 1 :=
  ⟨(hg 1 rfl).1, by simpa [entryTwo] using (hg 1 rfl).2.2⟩

/-- The only subgame of the entry game with two entry strategies is the game itself. -/
theorem entryTwo_subgames {x : List (Fin 3)} (hx : IsSubgameRoot (entryTwo o t) x) : x = [] := by
  have hd := hx.1
  have hmem := (mem_decisionNodes _).2 hd
  rw [show (entryTwo o t).decisionNodes = {[], [1], [2]} from
    (by decide : (entryTwo (fun _ => 0) (fun _ _ _ => 0)).decisionNodes = {[], [1], [2]})] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl
  · rfl
  · exact absurd (hx.2.1 [2] (by unfold IsDecision; simp [entryTwo]) (by simp [entryTwo]))
      (by simp)
  · exact absurd (hx.2.1 [1] (by unfold IsDecision; simp [entryTwo]) (by simp [entryTwo]))
      (by simp)

/-- **Example 9.C.1** (MWG, p. 282). In Figure 9.C.1 both (out, fight if entry occurs) and
(in₁, accommodate if entry occurs) are Nash equilibria. -/
theorem example_9_C_1_nash :
    IsNashB fig9C1 (pureMoves ![0, 0]) ∧ IsNashB fig9C1 (pureMoves ![1, 1]) := by
  have hB : ∀ a b : Fin 3, b ∈ ({0, 1} : Finset (Fin 3)) →
      IsBehaviorProfile fig9C1 (pureMoves (I := Fin 2) ![a, b]) := fun a b hb =>
    isBehaviorProfile_pureMoves fun k => by
      fin_cases k
      · simp [fig9C1, entryTwo]
      · simpa [fig9C1, entryTwo] using hb
  refine ⟨⟨hB 0 0 (by decide), ?_⟩, ⟨hB 1 1 (by decide), ?_⟩⟩ <;>
  · rw [Fin.forall_fin_two]
    constructor <;> intro g hg
    · obtain ⟨h0, h1⟩ := entryTwo_beh0 _ _ hg
      simp [fig9C1, (entryTwo_cont _ _ _ _).2.2, entryTwo_assemble, pureMoves, dirac]
      nlinarith [h0 0, h0 1, h0 2]
    · obtain ⟨h0, h1⟩ := entryTwo_beh1 _ _ hg
      simp [fig9C1, (entryTwo_cont _ _ _ _).2.2, entryTwo_assemble, pureMoves, dirac] <;>
      nlinarith [h0 0, h0 1, h0 2]

/-- **Example 9.C.1** (MWG, p. 282). The only subgame is the game as a whole, so both Nash
equilibria are subgame perfect (Exercise 9.B.2(a)): subgame perfection is of no use here. -/
theorem example_9_C_1_spne :
    IsSPNE fig9C1 (pureMoves ![0, 0]) ∧ IsSPNE fig9C1 (pureMoves ![1, 1]) :=
  ⟨exercise_9_B_2a _ (fun _ hx => entryTwo_subgames _ _ hx) example_9_C_1_nash.1,
    exercise_9_B_2a _ (fun _ hx => entryTwo_subgames _ _ hx) example_9_C_1_nash.2⟩

/-- The beliefs putting probability one on the left node of I's information set. -/
def leftBelief (x : List (Fin 3)) : ℝ := if x = [2] then 0 else 1

/-- **Example 9.C.1 continued** (MWG, p. 286). (in₁, accommodate if entry occurs) with
beliefs `μ(left) = 1` is a weak perfect Bayesian equilibrium, and it is the unique weak PBE
(pure or mixed): in every weak PBE I accommodates, E plays in₁ and `μ(left) = 1`. In
particular the Nash equilibrium (out, fight) is not part of any weak PBE. -/
theorem example_9_C_1_weakPBE :
    IsWeakPBE fig9C1 (pureMoves ![1, 1]) leftBelief ∧
    ∀ F μ, IsWeakPBE fig9C1 F μ → F 1 1 0 = 0 ∧ F 1 1 1 = 1 ∧ F 0 0 0 = 0 ∧ F 0 0 1 = 1 ∧
      F 0 0 2 = 0 ∧ μ [1] = 1 ∧ μ [2] = 0 := by
  have hc := entryTwo_cont ![0, 2] ![![![-1, -1], ![3, 0]], ![![-1, -1], ![2, 1]]]
  have hcp := entryTwo_condPayoff ![0, 2] ![![![-1, -1], ![3, 0]], ![![-1, -1], ![2, 1]]]
  have hr := entryTwo_reach ![0, 2] ![![![-1, -1], ![3, 0]], ![![-1, -1], ![2, 1]]]
  have hI := entryTwo_infoSet ![0, 2] ![![![-1, -1], ![3, 0]], ![![-1, -1], ![2, 1]]]
  constructor
  · refine ⟨example_9_C_1_nash.2.1, ⟨fun x _ => ?_, ?_⟩, ?_, ?_⟩
    · unfold leftBelief; split_ifs <;> norm_num
    · rw [Fin.forall_fin_two]
      exact ⟨by rw [hI.1]; simp [leftBelief], by rw [hI.2]; simp [leftBelief]⟩
    · intro k
      fin_cases k <;> intro i hi g hg <;> have hi' : i = _ := Option.some.inj hi.symm <;>
        subst hi'
      · obtain ⟨h0, h1⟩ := entryTwo_beh0 _ _ hg
        simp [fig9C1, (hcp _ _ _).1, (hc _ _).2.2, entryTwo_assemble, pureMoves, dirac,
          leftBelief]
        nlinarith [h0 0, h0 1, h0 2]
      · obtain ⟨h0, h1⟩ := entryTwo_beh1 _ _ hg
        simp [fig9C1, (hcp _ _ _).2, (hc _ _).1, (hc _ _).2.1, entryTwo_assemble, pureMoves,
          dirac, leftBelief]
        nlinarith [h0 0, h0 1]
    · refine Fin.forall_fin_two.2 ⟨fun hk x hx => ?_, fun hk x hx => ?_⟩
      · rw [hI.1] at hx
        simp only [Finset.mem_singleton] at hx
        subst hx
        simp [probInfo, hI.1, leftBelief]
      · rw [hI.2] at hx
        simp only [fig9C1, (hr _).2.2, entryTwo_assemble, pureMoves, dirac] at hk ⊢
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> simp [(hr _).1, (hr _).2.1, entryTwo_assemble, pureMoves,
          dirac, leftBelief]
  · intro F μ ⟨hF, hμ, hSR, hB⟩
    obtain ⟨hp0, hp1, hq0, hq1⟩ := entryTwo_behavior _ _ hF
    have hμ0 : μ [] = 1 := by simpa [hI.1] using hμ.2 0
    have hμ1 : μ [1] + μ [2] = 1 := by simpa [hI.2] using hμ.2 1
    have hμn1 := (hμ.1 [1] (by unfold IsDecision; simp [fig9C1, entryTwo])).1
    have hμn2 := (hμ.1 [2] (by unfold IsDecision; simp [fig9C1, entryTwo])).1
    -- I accommodates
    have hacc := hSR 1 1 rfl (fun _ => dirac 1) (entryTwo_dirac_beh _ _ 1 (by simp [entryTwo]))
    simp [fig9C1, (hcp _ _ _).2, (hc _ _).1, (hc _ _).2.1, entryTwo_assemble, dirac] at hacc
    have hq : F 1 1 0 = 0 := by nlinarith [hq0 0, hq0 1]
    have hq' : F 1 1 1 = 1 := by linarith
    -- E plays in₁
    have hin := hSR 0 0 rfl (fun _ => dirac 1) (entryTwo_dirac_beh _ _ 0 (by simp [entryTwo]))
    simp [fig9C1, (hcp _ _ _).1, (hc _ _).2.2, entryTwo_assemble, dirac, hμ0, hq, hq'] at hin
    have hp : F 0 0 1 = 1 := by nlinarith [hp0 0, hp0 1, hp0 2]
    have hpz0 : F 0 0 0 = 0 := by nlinarith [hp0 0, hp0 1, hp0 2]
    have hpz2 : F 0 0 2 = 0 := by nlinarith [hp0 0, hp0 1, hp0 2]
    -- Bayes' rule at I's information set
    have hpos : 0 < probInfo fig9C1 (fig9C1.assemble F) 1 := by
      simp only [fig9C1, (hr _).2.2, entryTwo_assemble, hp, hpz2]
      norm_num
    have h1 := hB 1 hpos [1] (by rw [hI.2]; simp)
    have h2 := hB 1 hpos [2] (by rw [hI.2]; simp)
    simp only [fig9C1, (hr _).1, (hr _).2.1, (hr _).2.2, entryTwo_assemble, hp, hpz2] at h1 h2
    norm_num at h1 h2
    exact ⟨hq, hq', hpz0, hp, hpz2, h1, h2⟩

/-- The conditions of a weak perfect Bayesian equilibrium of the entry game with two entry
strategies, written out: E's and I's one-move deviations and Bayes' rule at I's information
set. -/
theorem entryTwo_weakPBE_facts {F : Fin 2 → Fin 2 → Fin 3 → ℝ} {μ : List (Fin 3) → ℝ}
    (hW : IsWeakPBE (entryTwo o t) F μ) :
    (∀ a, 0 ≤ F 0 0 a) ∧ F 0 0 0 + F 0 0 1 + F 0 0 2 = 1 ∧ (∀ a, 0 ≤ F 1 1 a) ∧
    F 1 1 0 + F 1 1 1 = 1 ∧ μ [1] + μ [2] = 1 ∧ 0 ≤ μ [1] ∧ 0 ≤ μ [2] ∧
    (μ [1] * t 0 0 1 + μ [2] * t 1 0 1 ≤
      μ [1] * (F 1 1 0 * t 0 0 1 + F 1 1 1 * t 0 1 1) +
        μ [2] * (F 1 1 0 * t 1 0 1 + F 1 1 1 * t 1 1 1)) ∧
    (μ [1] * t 0 1 1 + μ [2] * t 1 1 1 ≤
      μ [1] * (F 1 1 0 * t 0 0 1 + F 1 1 1 * t 0 1 1) +
        μ [2] * (F 1 1 0 * t 1 0 1 + F 1 1 1 * t 1 1 1)) ∧
    (∀ v ∈ ({o 0, F 1 1 0 * t 0 0 0 + F 1 1 1 * t 0 1 0, F 1 1 0 * t 1 0 0 + F 1 1 1 * t 1 1 0} :
      Set ℝ), v ≤ F 0 0 0 * o 0 + F 0 0 1 * (F 1 1 0 * t 0 0 0 + F 1 1 1 * t 0 1 0) +
        F 0 0 2 * (F 1 1 0 * t 1 0 0 + F 1 1 1 * t 1 1 0)) ∧
    (0 < F 0 0 1 + F 0 0 2 → μ [1] = F 0 0 1 / (F 0 0 1 + F 0 0 2) ∧
      μ [2] = F 0 0 2 / (F 0 0 1 + F 0 0 2)) := by
  obtain ⟨hF, hμ, hSR, hB⟩ := hW
  obtain ⟨hp0, hp1, hq0, hq1⟩ := entryTwo_behavior o t hF
  have hI := entryTwo_infoSet o t
  have hc := entryTwo_cont o t
  have hcp := entryTwo_condPayoff o t
  have hr := entryTwo_reach o t
  have hμ0 : μ [] = 1 := by simpa [hI.1] using hμ.2 0
  have hμ1 : μ [1] + μ [2] = 1 := by simpa [hI.2] using hμ.2 1
  have hd1 : (entryTwo o t).IsDecision [1] := by unfold IsDecision; simp [entryTwo]
  have hd2 : (entryTwo o t).IsDecision [2] := by unfold IsDecision; simp [entryTwo]
  have hIdev : ∀ a : Fin 3, a ∈ ({0, 1} : Finset (Fin 3)) →
      μ [1] * cont (entryTwo o t) (fun _ => dirac a) [1] 1 +
        μ [2] * cont (entryTwo o t) (fun _ => dirac a) [2] 1 ≤
      μ [1] * cont (entryTwo o t) ((entryTwo o t).assemble F) [1] 1 +
        μ [2] * cont (entryTwo o t) ((entryTwo o t).assemble F) [2] 1 := by
    intro a ha
    have h := hSR 1 1 rfl (fun _ => dirac a)
      (entryTwo_dirac_beh o t 1 (by simpa [entryTwo] using ha))
    rw [(hcp _ _ _).2, (hcp _ _ _).2] at h
    refine le_trans (le_of_eq ?_) h
    congr 2
  refine ⟨hp0, hp1, hq0, hq1, hμ1, (hμ.1 _ hd1).1, (hμ.1 _ hd2).1, ?_, ?_, ?_, fun hpos => ?_⟩
  · have h := hIdev 0 (by decide)
    simpa [(hc _ _).1, (hc _ _).2.1, entryTwo_assemble, dirac] using h
  · have h := hIdev 1 (by decide)
    simpa [(hc _ _).1, (hc _ _).2.1, entryTwo_assemble, dirac] using h
  · intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    have key : ∀ a : Fin 3, cont (entryTwo o t) ((entryTwo o t).assemble
        (Function.update F 0 (fun _ => dirac a))) [] 0 ≤
        cont (entryTwo o t) ((entryTwo o t).assemble F) [] 0 := by
      intro a
      have h := hSR 0 0 rfl (fun _ => dirac a) (entryTwo_dirac_beh o t 0 (by simp [entryTwo]))
      rw [(hcp _ _ _).1, (hcp _ _ _).1, hμ0, one_mul, one_mul] at h
      exact h
    rcases hv with rfl | rfl | rfl
    · have := key 0
      simpa [(hc _ _).2.2, entryTwo_assemble, dirac] using this
    · have := key 1
      simpa [(hc _ _).2.2, entryTwo_assemble, dirac] using this
    · have := key 2
      simpa [(hc _ _).2.2, entryTwo_assemble, dirac] using this
  · have hp : 0 < probInfo (entryTwo o t) ((entryTwo o t).assemble F) 1 := by
      rw [(hr _).2.2, entryTwo_assemble]
      exact hpos
    have h1 := hB 1 hp [1] (by rw [hI.2]; simp)
    have h2 := hB 1 hp [2] (by rw [hI.2]; simp)
    rw [(hr _).1, (hr _).2.2, entryTwo_assemble] at h1
    rw [(hr _).2.1, (hr _).2.2, entryTwo_assemble] at h2
    exact ⟨h1, h2⟩

/-- **Example 9.C.3, Figure 9.C.3** (MWG, pp. 287-288): payoffs after entry `(−1, −1)`,
`(3, −2)` (in₁) and `(γ, −1)`, `(2, 1)` (in₂). -/
abbrev fig9C3 (γ : ℝ) : ExtensiveForm (Fin 2) (Fin 3) (Fin 2) :=
  entryTwo ![0, 2] ![![![-1, -1], ![3, -2]], ![![γ, -1], ![2, 1]]]

/-- Example 9.C.3, I's optimality: if `μ₁ < 2/3` I accommodates for sure. -/
theorem fig9C3_acc {μ1 q : ℝ} (hq0 : 0 ≤ q) (hlt : μ1 < 2 / 3)
    (hIa : μ1 * (-2) + (1 - μ1) * 1 ≤ μ1 * (q * (-1) + (1 - q) * (-2)) +
      (1 - μ1) * (q * (-1) + (1 - q) * 1)) : q = 0 := by
  nlinarith [mul_nonneg hq0 (sub_nonneg.2 hlt.le)]

/-- Example 9.C.3, I's optimality: if `μ₁ > 2/3` I fights for sure. -/
theorem fig9C3_fight {μ1 q : ℝ} (hq1 : q ≤ 1) (hgt : 2 / 3 < μ1)
    (hIf : μ1 * (-1) + (1 - μ1) * (-1) ≤ μ1 * (q * (-1) + (1 - q) * (-2)) +
      (1 - μ1) * (q * (-1) + (1 - q) * 1)) : q = 1 := by
  by_contra hne
  have : q < 1 := lt_of_le_of_ne hq1 hne
  nlinarith [mul_pos (sub_pos.2 hgt) (sub_pos.2 this)]

/-- Example 9.C.3, E's optimality: the moves played with positive probability are best. -/
theorem fig9C3_best {p0 p1 p2 v1 v2 : ℝ} (hp0 : 0 ≤ p0) (hp1 : 0 ≤ p1) (hp2 : 0 ≤ p2)
    (hsum : p0 + p1 + p2 = 1) (hE0 : 0 ≤ p1 * v1 + p2 * v2) (hE1 : v1 ≤ p1 * v1 + p2 * v2)
    (hE2 : v2 ≤ p1 * v1 + p2 * v2) :
    (0 < p1 → p1 * v1 + p2 * v2 = v1) ∧ (0 < p2 → p1 * v1 + p2 * v2 = v2) ∧
      (0 < p0 → p1 * v1 + p2 * v2 = 0) := by
  have hz : p1 * (p1 * v1 + p2 * v2 - v1) + p2 * (p1 * v1 + p2 * v2 - v2) +
      p0 * (p1 * v1 + p2 * v2) = 0 := by
    have : p0 = 1 - p1 - p2 := by linarith
    rw [this]
    ring
  have t1 := mul_nonneg hp1 (sub_nonneg.2 hE1)
  have t2 := mul_nonneg hp2 (sub_nonneg.2 hE2)
  have t3 := mul_nonneg hp0 hE0
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have : p1 * (p1 * v1 + p2 * v2 - v1) = 0 := by linarith
    rcases mul_eq_zero.1 this with h' | h'
    · linarith
    · linarith
  · have : p2 * (p1 * v1 + p2 * v2 - v2) = 0 := by linarith
    rcases mul_eq_zero.1 this with h' | h'
    · linarith
    · linarith
  · have : p0 * (p1 * v1 + p2 * v2) = 0 := by linarith
    rcases mul_eq_zero.1 this with h' | h'
    · linarith
    · exact h'

/-- The scalar conditions of a weak PBE of Figure 9.C.3: `p` E's mixed move, `q` the
probability that I fights, `μ1` the belief on the left node. -/
theorem fig9C3_scalar {γ : ℝ} {F : Fin 2 → Fin 2 → Fin 3 → ℝ} {μ : List (Fin 3) → ℝ}
    (hW : IsWeakPBE (fig9C3 γ) F μ) :
    0 ≤ F 0 0 0 ∧ 0 ≤ F 0 0 1 ∧ 0 ≤ F 0 0 2 ∧ F 0 0 0 + F 0 0 1 + F 0 0 2 = 1 ∧
    0 ≤ F 1 1 0 ∧ F 1 1 0 ≤ 1 ∧ 0 ≤ μ [1] ∧ μ [1] ≤ 1 ∧
    μ [1] * (-1) + (1 - μ [1]) * (-1) ≤ μ [1] * (F 1 1 0 * (-1) + (1 - F 1 1 0) * (-2)) +
      (1 - μ [1]) * (F 1 1 0 * (-1) + (1 - F 1 1 0) * 1) ∧
    μ [1] * (-2) + (1 - μ [1]) * 1 ≤ μ [1] * (F 1 1 0 * (-1) + (1 - F 1 1 0) * (-2)) +
      (1 - μ [1]) * (F 1 1 0 * (-1) + (1 - F 1 1 0) * 1) ∧
    0 ≤ F 0 0 1 * (F 1 1 0 * (-1) + (1 - F 1 1 0) * 3) +
      F 0 0 2 * (F 1 1 0 * γ + (1 - F 1 1 0) * 2) ∧
    F 1 1 0 * (-1) + (1 - F 1 1 0) * 3 ≤ F 0 0 1 * (F 1 1 0 * (-1) + (1 - F 1 1 0) * 3) +
      F 0 0 2 * (F 1 1 0 * γ + (1 - F 1 1 0) * 2) ∧
    F 1 1 0 * γ + (1 - F 1 1 0) * 2 ≤ F 0 0 1 * (F 1 1 0 * (-1) + (1 - F 1 1 0) * 3) +
      F 0 0 2 * (F 1 1 0 * γ + (1 - F 1 1 0) * 2) ∧
    (0 < F 0 0 1 + F 0 0 2 → μ [1] = F 0 0 1 / (F 0 0 1 + F 0 0 2)) := by
  obtain ⟨hp, hp1, hq, hq1, hμ1, hμa, hμb, hIf, hIa, hE, hB⟩ := entryTwo_weakPBE_facts _ _ hW
  have hμ2 : μ [2] = 1 - μ [1] := by linarith
  have hr1 : F 1 1 1 = 1 - F 1 1 0 := by linarith
  have hE0 := hE _ (Set.mem_insert _ _)
  have hE1 := hE _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hE2 := hE _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  simp only [hμ2, hr1] at hIf hIa hE0 hE1 hE2
  refine ⟨hp 0, hp 1, hp 2, hp1, hq 0, by linarith [hq 1], hμa, by linarith, ?_, ?_, ?_, ?_, ?_,
    fun h => (hB h).1⟩
  · simpa using hIf
  · simpa using hIa
  · simpa using hE0
  · simpa using hE1
  · simpa using hE2

/-- **Example 9.C.3** (MWG, p. 288). For `γ > 0` every weak PBE has E playing
`(σ₀, σ₁, σ₂) = (0, 2/3, 1/3)`, I fighting with probability `σ_F = 1/(γ + 2)` and
`μ₁ = 2/3`. -/
theorem example_9_C_3_unique {γ : ℝ} (hγ : 0 < γ) {F : Fin 2 → Fin 2 → Fin 3 → ℝ}
    {μ : List (Fin 3) → ℝ} (hW : IsWeakPBE (fig9C3 γ) F μ) :
    F 0 0 0 = 0 ∧ F 0 0 1 = 2 / 3 ∧ F 0 0 2 = 1 / 3 ∧ F 1 1 0 = 1 / (γ + 2) ∧
      μ [1] = 2 / 3 := by
  obtain ⟨hp0, hp1, hp2, hsum, hq0, hq1, hμa, hμb, hIf, hIa, hE0, hE1, hE2, hB⟩ :=
    fig9C3_scalar hW
  obtain ⟨b1, b2, b0⟩ := fig9C3_best hp0 hp1 hp2 hsum hE0 hE1 hE2
  rcases lt_trichotomy (μ [1]) (2 / 3) with hlt | heq | hgt
  · exfalso
    have hq := fig9C3_acc hq0 hlt hIa
    rw [hq] at hE1 hE2 hE0
    have h1 : F 0 0 1 = 1 := by nlinarith
    have := hB (by linarith)
    rw [h1, show F 0 0 2 = 0 by linarith] at this
    norm_num at this
    linarith
  · have hpos : 0 < F 0 0 1 + F 0 0 2 := by
      by_contra hn
      push Not at hn
      have h1 : F 0 0 1 = 0 := by linarith
      have h2 : F 0 0 2 = 0 := by linarith
      rw [h1, h2] at hE1 hE2
      nlinarith
    have hb1 := hB hpos
    have hratio : F 0 0 1 = 2 * F 0 0 2 := by
      rw [heq] at hb1
      field_simp at hb1
      linarith
    have hp2pos : 0 < F 0 0 2 := by linarith
    have e1 := b1 (by linarith)
    have e2 := b2 hp2pos
    have hqv : F 1 1 0 * (γ + 2) = 1 := by linear_combination e1 - e2
    have hγ2 : γ + 2 ≠ 0 := by linarith
    have hqf : F 1 1 0 = 1 / (γ + 2) := by field_simp; linarith
    have hqhalf : F 1 1 0 < 1 / 2 := by
      rw [hqf, div_lt_div_iff₀ (by linarith) (by norm_num)]
      linarith
    have hp00 : F 0 0 0 = 0 := by
      by_contra hne
      have := b0 (lt_of_le_of_ne hp0 (Ne.symm hne))
      linarith
    exact ⟨hp00, by linarith, by linarith, hqf, heq⟩
  · exfalso
    have hq := fig9C3_fight hq1 hgt hIf
    rw [hq] at hE2
    norm_num at hE2
    have hp2le : F 0 0 2 ≤ 1 := by linarith
    have hz1 : F 0 0 1 = 0 := by nlinarith [mul_nonneg hγ.le (sub_nonneg.2 hp2le)]
    have hpin : F 0 0 2 = 1 := by
      by_contra hne
      have : F 0 0 2 < 1 := lt_of_le_of_ne hp2le hne
      nlinarith [mul_pos hγ (sub_pos.2 this)]
    have := hB (by linarith)
    rw [hpin, hz1] at this
    norm_num at this
    linarith

/-- Sufficient conditions for a weak PBE of the entry game with two entry strategies: no
profitable pure deviation at either information set, and Bayes' rule at I's information set
when it is reached. -/
theorem entryTwo_weakPBE_of {F : Fin 2 → Fin 2 → Fin 3 → ℝ} {μ : List (Fin 3) → ℝ}
    (hF : IsBehaviorProfile (entryTwo o t) F) (hμ0 : μ [] = 1) (hμ1 : μ [1] + μ [2] = 1)
    (hμa : 0 ≤ μ [1]) (hμb : 0 ≤ μ [2])
    (hIf : μ [1] * t 0 0 1 + μ [2] * t 1 0 1 ≤
      μ [1] * (F 1 1 0 * t 0 0 1 + F 1 1 1 * t 0 1 1) +
        μ [2] * (F 1 1 0 * t 1 0 1 + F 1 1 1 * t 1 1 1))
    (hIa : μ [1] * t 0 1 1 + μ [2] * t 1 1 1 ≤
      μ [1] * (F 1 1 0 * t 0 0 1 + F 1 1 1 * t 0 1 1) +
        μ [2] * (F 1 1 0 * t 1 0 1 + F 1 1 1 * t 1 1 1))
    (hE : ∀ v ∈ ({o 0, F 1 1 0 * t 0 0 0 + F 1 1 1 * t 0 1 0,
      F 1 1 0 * t 1 0 0 + F 1 1 1 * t 1 1 0} : Set ℝ),
      v ≤ F 0 0 0 * o 0 + F 0 0 1 * (F 1 1 0 * t 0 0 0 + F 1 1 1 * t 0 1 0) +
        F 0 0 2 * (F 1 1 0 * t 1 0 0 + F 1 1 1 * t 1 1 0))
    (hB : 0 < F 0 0 1 + F 0 0 2 → μ [1] = F 0 0 1 / (F 0 0 1 + F 0 0 2) ∧
      μ [2] = F 0 0 2 / (F 0 0 1 + F 0 0 2)) :
    IsWeakPBE (entryTwo o t) F μ := by
  have hI := entryTwo_infoSet o t
  have hc := entryTwo_cont o t
  have hcp := entryTwo_condPayoff o t
  have hr := entryTwo_reach o t
  have hdn : (entryTwo o t).decisionNodes = {[], [1], [2]} :=
    (by decide : (entryTwo (fun _ => 0) (fun _ _ _ => 0)).decisionNodes = {[], [1], [2]})
  refine ⟨hF, ⟨fun x hx => ?_, Fin.forall_fin_two.2 ⟨by simp [hI.1, hμ0], by simp [hI.2, hμ1]⟩⟩,
    Fin.forall_fin_two.2 ⟨fun i hi g hg => ?_, fun i hi g hg => ?_⟩,
    Fin.forall_fin_two.2 ⟨fun hk x hx => ?_, fun hk x hx => ?_⟩⟩
  · have hx' := (mem_decisionNodes _).2 hx
    rw [hdn] at hx'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx'
    rcases hx' with rfl | rfl | rfl
    · rw [hμ0]; norm_num
    · exact ⟨hμa, by linarith⟩
    · exact ⟨hμb, by linarith⟩
  · obtain rfl : i = 0 := (Option.some.inj hi).symm
    obtain ⟨g0, g1⟩ := entryTwo_beh0 o t hg
    rw [(hcp _ _ _).1, (hcp _ _ _).1, (hc _ _).2.2, (hc _ _).2.2]
    simp only [entryTwo_assemble, Function.update_self, hμ0, one_mul]
    rw [Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0)]
    have e0 := hE _ (Set.mem_insert _ _)
    have e1 := hE _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
    have e2 := hE _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
    have hs : ∀ V : ℝ, (g 0 0 + g 0 1 + g 0 2) * V = V := fun V => by rw [g1, one_mul]
    nlinarith [mul_le_mul_of_nonneg_left e0 (g0 0), mul_le_mul_of_nonneg_left e1 (g0 1),
      mul_le_mul_of_nonneg_left e2 (g0 2), hs (F 0 0 0 * o 0 +
        F 0 0 1 * (F 1 1 0 * t 0 0 0 + F 1 1 1 * t 0 1 0) +
        F 0 0 2 * (F 1 1 0 * t 1 0 0 + F 1 1 1 * t 1 1 0))]
  · obtain rfl : i = 1 := (Option.some.inj hi).symm
    obtain ⟨g0, g1⟩ := entryTwo_beh1 o t hg
    rw [(hcp _ _ _).2, (hcp _ _ _).2, (hc _ _).1, (hc _ _).1, (hc _ _).2.1, (hc _ _).2.1]
    simp only [entryTwo_assemble, Function.update_self]
    have hs : ∀ V : ℝ, (g 1 0 + g 1 1) * V = V := fun V => by rw [g1, one_mul]
    nlinarith [mul_le_mul_of_nonneg_left hIf (g0 0), mul_le_mul_of_nonneg_left hIa (g0 1),
      hs (μ [1] * (F 1 1 0 * t 0 0 1 + F 1 1 1 * t 0 1 1) +
        μ [2] * (F 1 1 0 * t 1 0 1 + F 1 1 1 * t 1 1 1))]
  · rw [hI.1] at hx
    simp only [Finset.mem_singleton] at hx
    subst hx
    simp [probInfo, hI.1, hμ0]
  · rw [hI.2] at hx
    rw [(hr _).2.2, entryTwo_assemble] at hk ⊢
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · rw [(hr _).1, entryTwo_assemble]; exact (hB hk).1
    · rw [(hr _).2.1, entryTwo_assemble]; exact (hB hk).2

/-- The profile of Example 9.C.3: E plays `(0, 2/3, 1/3)`, I fights with probability
`1/(γ + 2)`. -/
noncomputable def fig9C3Profile (γ : ℝ) : Fin 2 → Fin 2 → Fin 3 → ℝ :=
  fun i _ => if i = 0 then ![0, 2 / 3, 1 / 3] else ![1 / (γ + 2), (γ + 1) / (γ + 2), 0]

/-- The beliefs of Example 9.C.3: `μ₁ = 2/3`. -/
noncomputable def fig9C3Belief (x : List (Fin 3)) : ℝ :=
  if x = [1] then 2 / 3 else if x = [2] then 1 / 3 else 1

/-- **Example 9.C.3** (MWG, p. 288). For `γ > 0`, `(σ₀, σ₁, σ₂) = (0, 2/3, 1/3)`,
`σ_F = 1/(γ + 2)` and `μ₁ = 2/3` form a weak perfect Bayesian equilibrium (the unique one by
`example_9_C_3_unique`). The same holds for `γ ≥ −2/3` (used in Exercise 9.C.2). -/
theorem example_9_C_3_exists {γ : ℝ} (hγ : -2 / 3 ≤ γ) :
    IsWeakPBE (fig9C3 γ) (fig9C3Profile γ) fig9C3Belief := by
  have hγ2 : γ + 2 ≠ 0 := by linarith
  have hpos : 0 < γ + 2 := by linarith
  have v00 : fig9C3Profile γ 0 0 0 = 0 := rfl
  have v01 : fig9C3Profile γ 0 0 1 = 2 / 3 := rfl
  have v02 : fig9C3Profile γ 0 0 2 = 1 / 3 := rfl
  have v10 : fig9C3Profile γ 1 1 0 = 1 / (γ + 2) := rfl
  have v11 : fig9C3Profile γ 1 1 1 = (γ + 1) / (γ + 2) := rfl
  have v12 : fig9C3Profile γ 1 1 2 = 0 := rfl
  have m0 : fig9C3Belief [] = 1 := rfl
  have m1 : fig9C3Belief [1] = 2 / 3 := rfl
  have m2 : fig9C3Belief [2] = 1 / 3 := rfl
  have hval : (1 / (γ + 2)) * (-1) + (γ + 1) / (γ + 2) * 3 = (3 * γ + 2) / (γ + 2) ∧
      (1 / (γ + 2)) * γ + (γ + 1) / (γ + 2) * 2 = (3 * γ + 2) / (γ + 2) := by
    constructor <;> field_simp <;> ring
  have hV : 0 ≤ (3 * γ + 2) / (γ + 2) := div_nonneg (by linarith) hpos.le
  refine entryTwo_weakPBE_of _ _ ?_ m0 (by rw [m1, m2]; norm_num) (by rw [m1]; norm_num)
    (by rw [m2]; norm_num) ?_ ?_ ?_ ?_
  · refine Fin.forall_fin_two.2 ⟨fun k hk => ?_, fun k hk => ?_⟩
    · obtain rfl : k = 0 := by simpa [entryTwo] using hk
      refine ⟨fun a => ?_, fun a ha => by simp [entryTwo] at ha, ?_⟩
      · fin_cases a <;> norm_num [fig9C3Profile]
      · simp only [entryTwo, ↓reduceIte, Fin.sum_univ_three, v00, v01, v02]
        norm_num
    · obtain rfl : k = 1 := by simpa [entryTwo] using hk
      have hav : (fig9C3 γ).avail 1 = {0, 1} := rfl
      refine ⟨fun a => ?_, fun a ha => ?_, ?_⟩
      · fin_cases a
        · exact v10 ▸ by positivity
        · exact v11 ▸ div_nonneg (by linarith) hpos.le
        · exact v12 ▸ le_rfl
      · fin_cases a <;> simp [hav] at ha
        exact v12
      · rw [hav, Finset.sum_pair (by decide), v10, v11]
        field_simp
        ring
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, m1, m2, v10, v11]
    field_simp
    ring_nf
    exact le_rfl
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, m1, m2, v10, v11]
    field_simp
    ring_nf
    exact le_rfl
  · intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, v00, v01, v02,
      v10, v11, hval.1, hval.2]
    rcases hv with rfl | rfl | rfl
    · simp only [Matrix.cons_val_zero]
      linarith
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, v10, v11, hval.1]
      linarith
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, v10, v11, hval.2]
      linarith
  · intro _
    rw [m1, m2, v01, v02]
    norm_num

/-- **Exercise 9.C.2** (MWG, p. 304). For `γ ∈ (−1, 0)` every weak PBE of the game of
Example 9.C.3 is of one of two kinds: (i) E stays out, and either `μ₁ > 2/3` and I fights for
sure, or `μ₁ = 2/3` and I fights with probability `σ_F ≥ 3/4` and `(2 − γ) σ_F ≥ 2`; or
(ii) `γ ≥ −2/3`, `μ₁ = 2/3`, `σ_F = 1/(γ + 2)` and E enters with In₁ twice as likely as
In₂. -/
theorem exercise_9_C_2 {γ : ℝ} (hγ1 : -1 < γ) (hγ0 : γ < 0) {F : Fin 2 → Fin 2 → Fin 3 → ℝ}
    {μ : List (Fin 3) → ℝ} (hW : IsWeakPBE (fig9C3 γ) F μ) :
    (F 0 0 1 = 0 ∧ F 0 0 2 = 0 ∧ ((2 / 3 < μ [1] ∧ F 1 1 0 = 1) ∨
      (μ [1] = 2 / 3 ∧ 3 / 4 ≤ F 1 1 0 ∧ 2 ≤ (2 - γ) * F 1 1 0))) ∨
    (μ [1] = 2 / 3 ∧ -2 / 3 ≤ γ ∧ F 1 1 0 * (γ + 2) = 1 ∧ F 0 0 1 = 2 * F 0 0 2 ∧
      0 < F 0 0 2) := by
  obtain ⟨hp0, hp1, hp2, hsum, hq0, hq1, hμa, hμb, hIf, hIa, hE0, hE1, hE2, hB⟩ :=
    fig9C3_scalar hW
  obtain ⟨b1, b2, -⟩ := fig9C3_best hp0 hp1 hp2 hsum hE0 hE1 hE2
  rcases lt_trichotomy (μ [1]) (2 / 3) with hlt | heq | hgt
  · exfalso
    have hq := fig9C3_acc hq0 hlt hIa
    rw [hq] at hE1
    have h1 : F 0 0 1 = 1 := by nlinarith
    have := hB (by linarith)
    rw [h1, show F 0 0 2 = 0 by linarith] at this
    norm_num at this
    linarith
  · by_cases hpos : 0 < F 0 0 1 + F 0 0 2
    · right
      have hb1 := hB hpos
      have hratio : F 0 0 1 = 2 * F 0 0 2 := by
        rw [heq] at hb1
        field_simp at hb1
        linarith
      have hp2pos : 0 < F 0 0 2 := by linarith
      have e1 := b1 (by linarith)
      have e2 := b2 hp2pos
      have hqv : F 1 1 0 * (γ + 2) = 1 := by linear_combination e1 - e2
      have hq34 : F 1 1 0 ≤ 3 / 4 := by linarith
      refine ⟨heq, ?_, hqv, hratio, hp2pos⟩
      nlinarith
    · left
      push Not at hpos
      have h1 : F 0 0 1 = 0 := by linarith
      have h2 : F 0 0 2 = 0 := by linarith
      rw [h1, h2] at hE1 hE2
      refine ⟨h1, h2, Or.inr ⟨heq, by linarith, by nlinarith⟩⟩
  · left
    have hq := fig9C3_fight hq1 hgt hIf
    rw [hq] at hE0
    norm_num at hE0
    have h1 : F 0 0 1 = 0 := by nlinarith
    have h2 : F 0 0 2 = 0 := by nlinarith
    exact ⟨h1, h2, Or.inl ⟨hgt, hq⟩⟩

/-- **Exercise 9.C.2** (MWG, p. 304). Both kinds occur: for `γ ∈ (−1, 0)`, E staying out with
I fighting and belief `1` on the left node is a weak PBE; for `γ ∈ [−2/3, 0)` so is the mixed
entry profile of Example 9.C.3. -/
theorem exercise_9_C_2_exists {γ : ℝ} (hγ0 : γ < 0) :
    IsWeakPBE (fig9C3 γ) (pureMoves ![0, 0]) leftBelief ∧
      (-2 / 3 ≤ γ → IsWeakPBE (fig9C3 γ) (fig9C3Profile γ) fig9C3Belief) := by
  refine ⟨?_, fun h => example_9_C_3_exists h⟩
  refine entryTwo_weakPBE_of _ _ (isBehaviorProfile_pureMoves fun k => by
    fin_cases k <;> simp [entryTwo]) (by simp [leftBelief]) (by simp [leftBelief])
    (by simp [leftBelief]) (by simp [leftBelief]) ?_ ?_ ?_ ?_
  · simp [leftBelief, pureMoves, dirac]
  · simp [leftBelief, pureMoves, dirac]
  · intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl | rfl <;> simp [pureMoves, dirac]
    linarith
  · intro h
    simp [pureMoves, dirac] at h

/-- **Figure 9.D.1(a)** (MWG, pp. 292-293): the entry game of Figure 9.C.1 in which I would
fight if E entered with In₁. -/
abbrev fig9D1a : ExtensiveForm (Fin 2) (Fin 3) (Fin 2) :=
  entryTwo ![0, 2] ![![![-3, -1], ![1, -2]], ![![-2, -1], ![3, 1]]]

/-- **Section 9.D, Figure 9.D.1(a)** (MWG, pp. 292-293). E staying out, I fighting after entry
and beliefs `[1]` on In₁ form a weak PBE; but In₁ is strictly dominated by In₂ for E whatever
I does after entry, so these beliefs are unreasonable (forward induction). -/
theorem figure_9_D_1a :
    IsWeakPBE fig9D1a (pureMoves ![0, 0]) leftBelief ∧
      ∀ q : ℝ, 0 ≤ q → q ≤ 1 → q * (-3) + (1 - q) * 1 < q * (-2) + (1 - q) * 3 := by
  refine ⟨?_, fun q _ hq1 => by linarith⟩
  refine entryTwo_weakPBE_of _ _ (isBehaviorProfile_pureMoves fun k => by
    fin_cases k <;> simp [entryTwo]) (by simp [leftBelief]) (by simp [leftBelief])
    (by simp [leftBelief]) (by simp [leftBelief]) ?_ ?_ ?_ ?_
  · simp [leftBelief, pureMoves, dirac]
  · simp [leftBelief, pureMoves, dirac]
  · intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl | rfl <;> simp [pureMoves, dirac]
  · intro h
    simp [pureMoves, dirac] at h

end MWG.DynamicGames
