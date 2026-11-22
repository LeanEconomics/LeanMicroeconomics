/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGDynamicGames.EntryTwo
import MWGDynamicGames.Sequential

/-!
# Entry followed by a simultaneous-move game

MWG, Examples 9.B.3, 9.B.4 and 9.C.5 (Figures 9.B.4-9.B.7, 9.C.5, 9.D.3; pp. 273-279 and
289-295) and Exercise 9.B.6.

E chooses Out (`0`) or In (`1`) at information set `0`; after entry E chooses an action at
information set `1` and I, without observing it, an action at information set `2`
(`{[0, 1], [1, 1]}`). `entrySim o s` has payoffs `o` after Out and `s e f` when E plays `e` and
I plays `f` after entry.

* Example 9.B.3 (actions `0` = Fight, `1` = Accommodate): `example_9_B_3_nash` (the three pure
  Nash equilibria), `example_9_B_3_spne` (((in, accommodate), accommodate) is the unique SPNE:
  in the post-entry subgame accommodating is strictly dominant for E, then optimal for I).
* `example_9_C_5`: ((out, accommodate if in), fight if E plays "in") with beliefs on the
  "fight" node is a weak PBE that is not subgame perfect, and every sequential equilibrium has
  the unique SPNE strategies (Proposition 9.C.2).
* Example 9.B.4 (actions `0` = Small niche, `1` = Large niche): `example_9_B_4` (two pure
  SPNE), `exercise_9_B_6` (the mixed equilibrium of the post-entry subgame, with each firm
  choosing the small niche with probability `2/9`, and the SPNE in which E stays out).
* `figure_9_D_3`: entering to target the small niche is strictly dominated for E by staying
  out (forward induction).
-/

namespace MWG.DynamicGames

open MWG.NoncooperativeGames MWG.NoncooperativeGames.ExtensiveForm

/-- Payoffs of the entry game followed by a simultaneous-move game. -/
def entrySimPay (o : Fin 2 → ℝ) (s : Fin 2 → Fin 2 → Fin 2 → ℝ) (i : Fin 2)
    (z : List (Fin 2)) : ℝ :=
  if z = [0] then o i else if z = [0, 0, 1] then s 0 0 i else if z = [1, 0, 1] then s 0 1 i
  else if z = [0, 1, 1] then s 1 0 i else if z = [1, 1, 1] then s 1 1 i else 0

/-- The information set of a node of the entry game followed by a simultaneous-move game. -/
def entrySimInfo (x : List (Fin 2)) : Fin 3 := if x = [] then 0 else if x = [1] then 1 else 2

/-- **Figures 9.B.4 and 9.B.6** (MWG, pp. 274 and 279). Entry followed by a simultaneous-move
game between E and I. -/
def entrySim (o : Fin 2 → ℝ) (s : Fin 2 → Fin 2 → Fin 2 → ℝ) :
    ExtensiveForm (Fin 2) (Fin 2) (Fin 3) where
  nodes := {[], [0], [1], [0, 1], [1, 1], [0, 0, 1], [1, 0, 1], [0, 1, 1], [1, 1, 1]}
  nil_mem := by decide
  tail_mem := by decide
  info := entrySimInfo
  avail _ := Finset.univ
  avail_spec := by decide
  info_surj := by decide
  player k := if k = 2 then some 1 else some 0
  natureProb _ _ := 0
  nature_nonneg := fun k hk => absurd hk (by split_ifs <;> simp)
  nature_zero := fun k hk => absurd hk (by split_ifs <;> simp)
  nature_sum := fun k hk => absurd hk (by split_ifs <;> simp)
  payoff := entrySimPay o s

variable (o : Fin 2 → ℝ) (s : Fin 2 → Fin 2 → Fin 2 → ℝ)

theorem entrySim_assemble (F : Fin 2 → Fin 3 → Fin 2 → ℝ) :
    (entrySim o s).assemble F 0 = F 0 0 ∧ (entrySim o s).assemble F 1 = F 0 1 ∧
      (entrySim o s).assemble F 2 = F 1 2 :=
  ⟨(entrySim o s).assemble_of_some F rfl, (entrySim o s).assemble_of_some F rfl,
    (entrySim o s).assemble_of_some F rfl⟩

/-- Continuation payoffs of the entry game followed by a simultaneous-move game. -/
theorem entrySim_cont (f : Fin 3 → Fin 2 → ℝ) (i : Fin 2) :
    cont (entrySim o s) f [0, 1] i = f 2 0 * s 0 0 i + f 2 1 * s 0 1 i ∧
    cont (entrySim o s) f [1, 1] i = f 2 0 * s 1 0 i + f 2 1 * s 1 1 i ∧
    cont (entrySim o s) f [1] i = f 1 0 * (f 2 0 * s 0 0 i + f 2 1 * s 0 1 i) +
      f 1 1 * (f 2 0 * s 1 0 i + f 2 1 * s 1 1 i) ∧
    cont (entrySim o s) f [] i = f 0 0 * o i + f 0 1 * (f 1 0 * (f 2 0 * s 0 0 i +
      f 2 1 * s 0 1 i) + f 1 1 * (f 2 0 * s 1 0 i + f 2 1 * s 1 1 i)) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [cont_unfold, entrySim, entrySimPay, entrySimInfo, Fin.sum_univ_two]

theorem entrySim_decisionNodes : (entrySim o s).decisionNodes = {[], [1], [0, 1], [1, 1]} :=
  (by decide : (entrySim (fun _ => 0) (fun _ _ _ => 0)).decisionNodes =
    {[], [1], [0, 1], [1, 1]})

/-- The subgames of the entry game followed by a simultaneous-move game: the whole game and
the post-entry subgame (MWG, p. 275). -/
theorem entrySim_subgames (x : List (Fin 2)) :
    IsSubgameRoot (entrySim o s) x ↔ x = [] ∨ x = [1] := by
  have hdn := entrySim_decisionNodes o s
  have hdec : ∀ y, (entrySim o s).IsDecision y ↔ y = [] ∨ y = [1] ∨ y = [0, 1] ∨ y = [1, 1] :=
    fun y => by rw [← mem_decisionNodes, hdn]; simp
  constructor
  · intro h
    rcases (hdec x).1 h.1 with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd (h.2.1 [1, 1] ((hdec _).2 (by simp)) rfl) (by simp)
    · exact absurd (h.2.1 [0, 1] ((hdec _).2 (by simp)) rfl) (by simp)
  · have hinfo : ∀ y, (entrySim o s).info y = entrySimInfo y := fun _ => rfl
    rintro (rfl | rfl)
    · refine ⟨(hdec _).2 (by simp), fun y hy he => ?_, fun _ _ _ _ _ _ => List.nil_suffix⟩
      rcases (hdec y).1 hy with rfl | rfl | rfl | rfl <;> simp_all [entrySimInfo]
    · refine ⟨(hdec _).2 (by simp), fun y hy he => ?_, fun y hy hxy y' hy' he => ?_⟩
      · rcases (hdec y).1 hy with rfl | rfl | rfl | rfl <;> simp_all [entrySimInfo]
      · rcases (hdec y).1 hy with rfl | rfl | rfl | rfl <;>
        rcases (hdec y').1 hy' with rfl | rfl | rfl | rfl <;>
        simp_all [entrySimInfo]

theorem entrySim_beh (i : Fin 2) {g : Fin 3 → Fin 2 → ℝ}
    (hg : (entrySim o s).IsBehaviorStrategy i g) (k : Fin 3)
    (hk : (if k = 2 then some (1 : Fin 2) else some 0) = some i) :
    0 ≤ g k 0 ∧ 0 ≤ g k 1 ∧ g k 0 + g k 1 = 1 := by
  have h := hg k hk
  exact ⟨h.1 0, h.1 1, by simpa [entrySim] using h.2.2⟩

/-- The payoffs of Example 9.B.3 (`0` = Fight, `1` = Accommodate). -/
abbrev fig9B4 : ExtensiveForm (Fin 2) (Fin 2) (Fin 3) :=
  entrySim ![0, 2] ![![![-3, -1], ![1, -2]], ![![-2, -1], ![3, 1]]]

/-- **Example 9.B.3** (MWG, p. 273). The three pure strategy Nash equilibria:
((out, accommodate if in), fight if E plays "in"), ((out, fight if in), fight if E plays "in")
and ((in, accommodate if in), accommodate if E plays "in"). -/
theorem example_9_B_3_nash :
    IsNashB fig9B4 (pureMoves ![0, 1, 0]) ∧ IsNashB fig9B4 (pureMoves ![0, 0, 0]) ∧
      IsNashB fig9B4 (pureMoves ![1, 1, 1]) := by
  have hc := entrySim_cont ![0, 2] ![![![-3, -1], ![1, -2]], ![![-2, -1], ![3, 1]]]
  have hB : ∀ c : Fin 3 → Fin 2, IsBehaviorProfile fig9B4 (pureMoves (I := Fin 2) c) :=
    fun c => isBehaviorProfile_pureMoves fun _ => Finset.mem_univ _
  refine ⟨⟨hB _, ?_⟩, ⟨hB _, ?_⟩, ⟨hB _, ?_⟩⟩ <;>
  · rw [Fin.forall_fin_two]
    constructor <;> intro g hg
    · obtain ⟨a0, a1, a2⟩ := entrySim_beh _ _ 0 hg 0 (by simp)
      obtain ⟨b0, b1, b2⟩ := entrySim_beh _ _ 0 hg 1 (by simp)
      simp [(hc _ _).2.2.2, entrySim_assemble, pureMoves, dirac]
      nlinarith [mul_nonneg a0 b0, mul_nonneg a1 b0, mul_nonneg a0 b1, mul_nonneg a1 b1]
    · obtain ⟨a0, a1, a2⟩ := entrySim_beh _ _ 1 hg 2 (by simp)
      simp [(hc _ _).2.2.2, entrySim_assemble, pureMoves, dirac] <;>
      nlinarith

/-- **Example 9.B.3** (MWG, pp. 275 and 278). ((in, accommodate if in), accommodate if E plays
"in") is the unique subgame perfect Nash equilibrium: in the post-entry subgame accommodating
is strictly dominant for E, so I accommodates, and then E enters. -/
theorem example_9_B_3_spne :
    IsSPNE fig9B4 (pureMoves ![1, 1, 1]) ∧ ∀ F, IsSPNE fig9B4 F →
      F 0 0 1 = 1 ∧ F 0 1 1 = 1 ∧ F 1 2 1 = 1 := by
  have hc := entrySim_cont ![0, 2] ![![![-3, -1], ![1, -2]], ![![-2, -1], ![3, 1]]]
  have hsub := entrySim_subgames ![0, 2] ![![![-3, -1], ![1, -2]], ![![-2, -1], ![3, 1]]]
  constructor
  · refine ⟨isBehaviorProfile_pureMoves fun _ => Finset.mem_univ _, fun x hx => ?_⟩
    rcases (hsub x).1 hx with rfl | rfl <;> rw [InducesNashAt, Fin.forall_fin_two] <;>
      constructor <;> intro g hg
    · obtain ⟨a0, a1, a2⟩ := entrySim_beh _ _ 0 hg 0 (by simp)
      obtain ⟨b0, b1, b2⟩ := entrySim_beh _ _ 0 hg 1 (by simp)
      simp [(hc _ _).2.2.2, entrySim_assemble, pureMoves, dirac]
      nlinarith [mul_nonneg a0 b0, mul_nonneg a1 b0, mul_nonneg a0 b1, mul_nonneg a1 b1]
    · obtain ⟨a0, a1, a2⟩ := entrySim_beh _ _ 1 hg 2 (by simp)
      simp [(hc _ _).2.2.2, entrySim_assemble, pureMoves, dirac]
      nlinarith
    · obtain ⟨b0, b1, b2⟩ := entrySim_beh _ _ 0 hg 1 (by simp)
      simp [(hc _ _).2.2.1, entrySim_assemble, pureMoves, dirac]
      nlinarith
    · obtain ⟨a0, a1, a2⟩ := entrySim_beh _ _ 1 hg 2 (by simp)
      simp [(hc _ _).2.2.1, entrySim_assemble, pureMoves, dirac]
      nlinarith
  · intro F hF
    have hb0 := entrySim_beh _ _ 0 (hF.1 0) 0 (by simp)
    have hb1 := entrySim_beh _ _ 0 (hF.1 0) 1 (by simp)
    have hb2 := entrySim_beh _ _ 1 (hF.1 1) 2 (by simp)
    have hdev : ∀ (i : Fin 2) (k : Fin 3) (a : Fin 2),
        (if k = 2 then some (1 : Fin 2) else some 0) = some i →
        fig9B4.IsBehaviorStrategy i (Function.update (F i) k (dirac a)) := by
      intro i k a hk k' hk'
      by_cases hkk : k' = k
      · subst hkk
        simp only [Function.update_self]
        exact (isBehaviorProfile_pureMoves (I := Fin 2) (G := fig9B4) (c := fun _ => a)
          fun _ => Finset.mem_univ _) i k' hk'
      · rw [Function.update_of_ne hkk]
        exact hF.1 i k' hk'
    -- in the post-entry subgame E accommodates
    have hE1 := hF.2 [1] ((hsub _).2 (Or.inr rfl)) 0 _ (hdev 0 1 1 (by simp))
    simp [(hc _ _).2.2.1, entrySim_assemble, dirac] at hE1
    have hp : F 0 1 1 = 1 := by nlinarith [mul_nonneg hb1.1 hb2.2.1]
    -- then I accommodates
    have hI1 := hF.2 [1] ((hsub _).2 (Or.inr rfl)) 1 _ (hdev 1 2 1 (by simp))
    simp [(hc _ _).2.2.1, entrySim_assemble, hp, show F 0 1 0 = 0 by linarith, dirac] at hI1
    have hq : F 1 2 1 = 1 := by nlinarith
    -- then E enters
    have hE0 := hF.2 [] ((hsub _).2 (Or.inl rfl)) 0 _ (hdev 0 0 1 (by simp))
    simp [(hc _ _).2.2.2, entrySim_assemble, hp, hq, show F 0 1 0 = 0 by linarith,
      show F 1 2 0 = 0 by linarith, dirac] at hE0
    exact ⟨by nlinarith, hp, hq⟩

theorem entrySim_infoSet : (entrySim o s).infoSet 0 = {[]} ∧ (entrySim o s).infoSet 1 = {[1]} ∧
    (entrySim o s).infoSet 2 = {[0, 1], [1, 1]} :=
  ⟨(by decide : (entrySim (fun _ => 0) (fun _ _ _ => 0)).infoSet 0 = {[]}),
    (by decide : (entrySim (fun _ => 0) (fun _ _ _ => 0)).infoSet 1 = {[1]}),
    (by decide : (entrySim (fun _ => 0) (fun _ _ _ => 0)).infoSet 2 = {[0, 1], [1, 1]})⟩

theorem entrySim_reach (f : Fin 3 → Fin 2 → ℝ) :
    (entrySim o s).reach f [] = 1 ∧ (entrySim o s).reach f [1] = f 0 1 ∧
      (entrySim o s).reach f [0, 1] = f 0 1 * f 1 0 ∧
      (entrySim o s).reach f [1, 1] = f 0 1 * f 1 1 := by
  refine ⟨rfl, ?_, ?_, ?_⟩ <;> simp [entrySim, entrySimInfo]

theorem fin3_cases {P : Fin 3 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) (k : Fin 3) : P k := by
  fin_cases k
  · exact h0
  · exact h1
  · exact h2

theorem entrySim_perfectRecall : (entrySim o s).PerfectRecall := by
  have : (entrySim (fun _ => 0) (fun _ _ _ => 0)).PerfectRecall := by
    refine ⟨by unfold ExtensiveForm.NoAbsentMindedness; decide, fun i => ?_⟩
    unfold ExtensiveForm.RecallFor
    fin_cases i <;> decide
  exact this

/-- The beliefs of Figure 9.C.5: I believes that E fought. -/
def fightBelief (x : List (Fin 2)) : ℝ := if x = [1, 1] then 0 else 1

/-- **Example 9.C.5, Figure 9.C.5** (MWG, pp. 289-291). ((out, accommodate if in), fight if E
plays "in") with I's beliefs putting probability one on E having fought is a weak perfect
Bayesian equilibrium, but it is not subgame perfect. The unique sequential equilibrium
strategies are those of the unique SPNE ((in, accommodate), accommodate) (Proposition 9.C.2),
and a sequential equilibrium exists. -/
theorem example_9_C_5 :
    IsWeakPBE fig9B4 (pureMoves ![0, 1, 0]) fightBelief ∧
    ¬ IsSPNE fig9B4 (pureMoves ![0, 1, 0]) ∧
    (∀ F μ, IsSequentialEq fig9B4 F μ → F 0 0 1 = 1 ∧ F 0 1 1 = 1 ∧ F 1 2 1 = 1) ∧
    ∃ F μ, IsSequentialEq fig9B4 F μ := by
  have hc := entrySim_cont ![0, 2] ![![![-3, -1], ![1, -2]], ![![-2, -1], ![3, 1]]]
  have hI := entrySim_infoSet ![0, 2] ![![![-3, -1], ![1, -2]], ![![-2, -1], ![3, 1]]]
  have hdn := entrySim_decisionNodes ![0, 2] ![![![-3, -1], ![1, -2]], ![![-2, -1], ![3, 1]]]
  have hsub := entrySim_subgames ![0, 2] ![![![-3, -1], ![1, -2]], ![![-2, -1], ![3, 1]]]
  have hPR : fig9B4.PerfectRecall := entrySim_perfectRecall _ _
  have hr := entrySim_reach ![0, 2] ![![![-3, -1], ![1, -2]], ![![-2, -1], ![3, 1]]]
  have hN : NatureFullSupport fig9B4 := fun k hk =>
    absurd hk (by simp only [fig9B4, entrySim]; split_ifs <;> simp)
  have hB := isBehaviorProfile_pureMoves (I := Fin 2) (G := fig9B4) (c := ![0, 1, 0])
    fun _ => Finset.mem_univ _
  refine ⟨⟨hB, ⟨fun x hx => ?_, ?_⟩, ?_, ?_⟩, fun h => ?_, fun F μ hFμ => ?_, ?_⟩
  · unfold fightBelief; split_ifs <;> norm_num
  · exact fin3_cases (by simp [hI.1, fightBelief]) (by simp [hI.2.1, fightBelief])
      (by simp [hI.2.2, fightBelief])
  · intro k i hi g hg
    fin_cases k
    · obtain rfl : i = 0 := (Option.some.inj hi).symm
      obtain ⟨a0, a1, a2⟩ := entrySim_beh _ _ 0 hg 0 (by simp)
      obtain ⟨b0, b1, b2⟩ := entrySim_beh _ _ 0 hg 1 (by simp)
      simp [condPayoff, hI.1, fightBelief, (hc _ _).2.2.2, entrySim_assemble, pureMoves, dirac]
      nlinarith [mul_nonneg a1 b0, mul_nonneg a1 b1]
    · obtain rfl : i = 0 := (Option.some.inj hi).symm
      obtain ⟨b0, b1, b2⟩ := entrySim_beh _ _ 0 hg 1 (by simp)
      simp [condPayoff, hI.2.1, fightBelief, (hc _ _).2.2.1, entrySim_assemble, pureMoves,
        dirac]
      nlinarith
    · obtain rfl : i = 1 := (Option.some.inj hi).symm
      obtain ⟨c0, c1, c2⟩ := entrySim_beh _ _ 1 hg 2 (by simp)
      simp [condPayoff, hI.2.2, fightBelief, (hc _ _).1, entrySim_assemble,
        pureMoves, dirac]
      nlinarith
  · refine fin3_cases (fun hk x hx => ?_) (fun hk x hx => ?_) (fun hk x hx => ?_)
    · rw [hI.1] at hx
      simp only [Finset.mem_singleton] at hx
      subst hx
      simp [probInfo, hI.1, fightBelief]
    · exfalso
      simp [probInfo, hI.2.1, (hr _).2.1, entrySim_assemble, pureMoves, dirac] at hk
    · exfalso
      simp [probInfo, hI.2.2, (hr _).2.2.1, (hr _).2.2.2, entrySim_assemble, pureMoves,
        dirac] at hk
  · have := h.2 [1] ((hsub _).2 (Or.inr rfl)) 1 (fun _ => dirac 1)
      (fun k hk => (isBehaviorProfile_pureMoves (I := Fin 2) (G := fig9B4)
        (c := fun _ => (1 : Fin 2)) fun _ => Finset.mem_univ _) 1 k hk)
    simp [(hc _ _).2.2.1, entrySim_assemble, pureMoves, dirac] at this
    norm_num at this
  · exact (example_9_B_3_spne.2 F (proposition_9_C_2 _ hPR hFμ))
  · exact exists_isSequentialEq _ hPR hN

/-- The payoffs of the Niche Choice game, Example 9.B.4 (`0` = Small niche, `1` = Large
niche). -/
abbrev nicheGame : ExtensiveForm (Fin 2) (Fin 2) (Fin 3) :=
  entrySim ![0, 2] ![![![-6, -6], ![-1, 1]], ![![1, -1], ![-3, -3]]]

/-- **Example 9.B.4, Figures 9.B.6-9.B.7** (MWG, pp. 278-279). The Niche Choice game has the
two pure strategy SPNE ((in, large niche if in), small niche if E plays "in") and ((out, small
niche if in), large niche if E plays "in"). -/
theorem example_9_B_4 :
    IsSPNE nicheGame (pureMoves ![1, 1, 0]) ∧ IsSPNE nicheGame (pureMoves ![0, 0, 1]) := by
  have hc := entrySim_cont ![0, 2] ![![![-6, -6], ![-1, 1]], ![![1, -1], ![-3, -3]]]
  have hsub := entrySim_subgames ![0, 2] ![![![-6, -6], ![-1, 1]], ![![1, -1], ![-3, -3]]]
  constructor <;>
  · refine ⟨isBehaviorProfile_pureMoves fun _ => Finset.mem_univ _, fun x hx => ?_⟩
    rcases (hsub x).1 hx with rfl | rfl <;> rw [InducesNashAt, Fin.forall_fin_two] <;>
      constructor <;> intro g hg
    · obtain ⟨a0, a1, a2⟩ := entrySim_beh _ _ 0 hg 0 (by simp)
      obtain ⟨b0, b1, b2⟩ := entrySim_beh _ _ 0 hg 1 (by simp)
      simp [(hc _ _).2.2.2, entrySim_assemble, pureMoves, dirac]
      nlinarith [mul_nonneg a0 b0, mul_nonneg a1 b0, mul_nonneg a0 b1, mul_nonneg a1 b1]
    · obtain ⟨a0, a1, a2⟩ := entrySim_beh _ _ 1 hg 2 (by simp)
      simp [(hc _ _).2.2.2, entrySim_assemble, pureMoves, dirac] <;>
      nlinarith
    · obtain ⟨b0, b1, b2⟩ := entrySim_beh _ _ 0 hg 1 (by simp)
      simp [(hc _ _).2.2.1, entrySim_assemble, pureMoves, dirac]
      nlinarith
    · obtain ⟨a0, a1, a2⟩ := entrySim_beh _ _ 1 hg 2 (by simp)
      simp [(hc _ _).2.2.1, entrySim_assemble, pureMoves, dirac]
      nlinarith

/-- The profile of Exercise 9.B.6: E stays out; after entry each firm targets the small niche
with probability `2/9`. -/
noncomputable def nicheMixed : Fin 2 → Fin 3 → Fin 2 → ℝ :=
  fun _ k => if k = 0 then ![1, 0] else ![2 / 9, 7 / 9]

/-- **Exercise 9.B.6** (MWG, p. 302). In the post-entry subgame of the Niche Choice game there
is a mixed equilibrium in which each firm chooses the small niche with probability `2/9`; it
gives E the payoff `−19/9 < 0`. Hence there is an SPNE inducing it, in which E stays out, and
in every SPNE that induces this post-entry play E stays out. -/
theorem exercise_9_B_6 :
    cont nicheGame (nicheGame.assemble nicheMixed) [1] 0 = -19 / 9 ∧
    IsSPNE nicheGame nicheMixed ∧
    ∀ F, IsSPNE nicheGame F → F 0 1 = ![2 / 9, 7 / 9] → F 1 2 = ![2 / 9, 7 / 9] →
      F 0 0 0 = 1 := by
  have hc := entrySim_cont ![0, 2] ![![![-6, -6], ![-1, 1]], ![![1, -1], ![-3, -3]]]
  have hsub := entrySim_subgames ![0, 2] ![![![-6, -6], ![-1, 1]], ![![1, -1], ![-3, -3]]]
  have hval : nicheMixed 0 0 = ![1, 0] ∧ nicheMixed 0 1 = ![2 / 9, 7 / 9] ∧
      nicheMixed 1 2 = ![2 / 9, 7 / 9] := ⟨rfl, rfl, rfl⟩
  refine ⟨?_, ⟨fun i k _ => ?_, fun x hx => ?_⟩, fun F hF h1 h2 => ?_⟩
  · simp [(hc _ _).2.2.1, entrySim_assemble, hval]
    norm_num
  · refine ⟨fun a => ?_, fun a ha => absurd (Finset.mem_univ a) ha, ?_⟩
    · fin_cases a <;> simp [nicheMixed] <;> split_ifs <;> norm_num
    · simp [nicheMixed, entrySim, Fin.sum_univ_two]
      split_ifs <;> norm_num
  · rcases (hsub x).1 hx with rfl | rfl <;> rw [InducesNashAt, Fin.forall_fin_two] <;>
      constructor <;> intro g hg
    · obtain ⟨a0, a1, a2⟩ := entrySim_beh _ _ 0 hg 0 (by simp)
      obtain ⟨b0, b1, b2⟩ := entrySim_beh _ _ 0 hg 1 (by simp)
      simp [(hc _ _).2.2.2, entrySim_assemble, hval]
      nlinarith [mul_nonneg a1 b0, mul_nonneg a1 b1]
    · obtain ⟨a0, a1, a2⟩ := entrySim_beh _ _ 1 hg 2 (by simp)
      simp [(hc _ _).2.2.2, entrySim_assemble, hval]
    · obtain ⟨b0, b1, b2⟩ := entrySim_beh _ _ 0 hg 1 (by simp)
      simp [(hc _ _).2.2.1, entrySim_assemble, hval]
      nlinarith
    · obtain ⟨a0, a1, a2⟩ := entrySim_beh _ _ 1 hg 2 (by simp)
      simp [(hc _ _).2.2.1, entrySim_assemble, hval]
      nlinarith
  · have hb0 := entrySim_beh _ _ 0 (hF.1 0) 0 (by simp)
    have hdev : nicheGame.IsBehaviorStrategy 0 (Function.update (F 0) 0 (dirac 0)) := by
      intro k hk
      by_cases hkk : k = 0
      · subst hkk
        simp only [Function.update_self]
        exact (isBehaviorProfile_pureMoves (I := Fin 2) (G := nicheGame) (c := fun _ => 0)
          fun _ => Finset.mem_univ _) 0 0 hk
      · rw [Function.update_of_ne hkk]
        exact hF.1 0 k hk
    have := hF.2 [] ((hsub _).2 (Or.inl rfl)) 0 _ hdev
    simp [(hc _ _).2.2.2, entrySim_assemble, h1, h2, dirac] at this
    nlinarith

/-- **Section 9.D, Figure 9.D.3** (MWG, pp. 294-295). Entering and targeting the small niche
is strictly dominated for E by staying out, whatever I does after entry. -/
theorem figure_9_D_3 (q : ℝ) (hq0 : 0 ≤ q) :
    q * (-6) + (1 - q) * (-1) < 0 := by linarith

end MWG.DynamicGames
