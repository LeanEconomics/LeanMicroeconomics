/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGDynamicGames.EntrySim

/-!
# Entry followed by a coordination game

MWG, Exercise 9.B.10 (p. 303). Example 9.B.3's game (E chooses Out or In; after entry E and I
simultaneously choose Fight (`0`) or Accommodate (`1`)) is changed so that when both
accommodate, instead of receiving `(3, 1)` they play the simultaneous-move game
`[[(3, 1), (0, 0)], [(0, 0), (x, 3)]]` (E chooses `U` = `0` or `D` = `1`, I chooses `ℓ` = `0` or
`r` = `1`).

Nodes: `[]` (E: out/in, information set `0`), `[1]` (E: fight/accommodate, set `1`),
`{[0, 1], [1, 1]}` (I: fight/accommodate, set `2`), `[1, 1, 1]` (E: `U`/`D`, set `3`),
`{[0, 1, 1, 1], [1, 1, 1, 1]}` (I: `ℓ`/`r`, set `4`).

* `ec_subgames`: the subgames start at `[]`, `[1]` and `[1, 1, 1]`.
* `exercise_9_B_10_pure`: for every `x`, the pure strategy SPNE are ((in, accommodate, `U`),
  (accommodate, `ℓ`)), and, exactly when `x ≥ 1`, also ((in, accommodate, `D`),
  (accommodate, `r`)). For `0 ≤ x < 1` the coordination equilibrium `(D, r)` exists but cannot
  be part of a pure SPNE: with `(x, 3)` after (accommodate, accommodate) the post-entry game
  has no pure equilibrium.
* `exercise_9_B_10_neg`: for `x < 0` the SPNE is unique (among all behaviour profiles): `D` is
  strictly dominated in the coordination game, and the game reduces to Example 9.B.3.
* `exercise_9_B_10_mixed`: mixed equilibria of the coordination game matter for `x ≥ 0`: for
  `x = 3`, E entering and accommodating, I accommodating, and the mixed coordination
  equilibrium (`U` with probability `3/4`, `ℓ` with probability `1/2`) is a further SPNE,
  giving E the payoff `3/2`.
* `IsSPNE.pure_dev`, `assemble_pureMoves`: general facts on pure profiles used in the proofs.
-/

namespace MWG.DynamicGames

open MWG.NoncooperativeGames MWG.NoncooperativeGames.ExtensiveForm

/-- Without moves of nature, the moves of `pureMoves c` are the sure moves `c k`. -/
theorem assemble_pureMoves {I A H : Type*} [DecidableEq A] {G : ExtensiveForm I A H}
    (hN : ∀ k, G.player k ≠ none) (c : H → A) :
    G.assemble (pureMoves (I := I) c) = fun k => dirac (c k) := by
  funext k
  obtain ⟨j, hj⟩ := Option.ne_none_iff_exists'.1 (hN k)
  rw [G.assemble_of_some _ hj]
  rfl

/-- In an SPNE given by sure moves `c`, no player gains in a subgame by changing her move at
one of her information sets. -/
theorem IsSPNE.pure_dev {I A H : Type*} [DecidableEq A] [Fintype A] [DecidableEq I]
    [DecidableEq H] {G : ExtensiveForm I A H} {c : H → A} (h : IsSPNE G (pureMoves (I := I) c))
    (hc : ∀ k, c k ∈ G.avail k) {x : List A} (hx : IsSubgameRoot G x) {k : H} {i : I}
    (hk : G.player k = some i) {a : A} (ha : a ∈ G.avail k) :
    cont G (G.assemble (pureMoves (I := I) (Function.update c k a))) x i ≤
      cont G (G.assemble (pureMoves (I := I) c)) x i := by
  classical
  have hc' : ∀ k', Function.update c k a k' ∈ G.avail k' := by
    intro k'
    by_cases hkk : k' = k
    · subst hkk
      simpa using ha
    · simpa [Function.update_of_ne hkk] using hc k'
  have hdev := h.2 x hx i _ ((isBehaviorProfile_pureMoves (G := G) (I := I) hc') i)
  have heq : G.assemble (pureMoves (I := I) (Function.update c k a)) =
      G.assemble (Function.update (pureMoves (I := I) c) i
        (pureMoves (I := I) (Function.update c k a) i)) := by
    funext k'
    cases hk' : G.player k' with
    | none => rw [G.assemble_of_none _ hk', G.assemble_of_none _ hk']
    | some j =>
      rw [G.assemble_of_some _ hk', G.assemble_of_some _ hk']
      by_cases hji : j = i
      · subst hji
        simp
      · rw [Function.update_of_ne hji]
        have hkk : k' ≠ k := by
          rintro rfl
          rw [hk] at hk'
          exact hji (Option.some.inj hk').symm
        simp [pureMoves, Function.update_of_ne hkk]
  rw [heq]
  exact hdev

/-- The information sets of the game of Exercise 9.B.10. -/
def ecInfo (l : List (Fin 2)) : Fin 5 :=
  if l = [] then 0 else if l = [1] then 1 else if l = [0, 1] ∨ l = [1, 1] then 2
  else if l = [1, 1, 1] then 3 else 4

/-- The payoffs `(u_E, u_I)` of the game of Exercise 9.B.10 (Example 9.B.3's payoffs, with
the coordination game after (accommodate, accommodate)). -/
def ecPay (x : ℝ) (i : Fin 2) (l : List (Fin 2)) : ℝ :=
  if l = [0] then (if i = 0 then 0 else 2)
  else if l = [0, 0, 1] then (if i = 0 then -3 else -1)
  else if l = [1, 0, 1] then (if i = 0 then 1 else -2)
  else if l = [0, 1, 1] then (if i = 0 then -2 else -1)
  else if l = [0, 0, 1, 1, 1] then (if i = 0 then 3 else 1)
  else if l = [1, 1, 1, 1, 1] then (if i = 0 then x else 3) else 0

/-- **Exercise 9.B.10** (MWG, p. 303). The entry game of Example 9.B.3 in which (accommodate,
accommodate) is followed by the coordination game `[[(3, 1), (0, 0)], [(0, 0), (x, 3)]]`. -/
def ecGame (x : ℝ) : ExtensiveForm (Fin 2) (Fin 2) (Fin 5) where
  nodes := {[], [0], [1], [0, 1], [1, 1], [0, 0, 1], [1, 0, 1], [0, 1, 1], [1, 1, 1],
    [0, 1, 1, 1], [1, 1, 1, 1], [0, 0, 1, 1, 1], [1, 0, 1, 1, 1], [0, 1, 1, 1, 1],
    [1, 1, 1, 1, 1]}
  nil_mem := by decide
  tail_mem := by decide
  info := ecInfo
  avail _ := Finset.univ
  avail_spec := by decide
  info_surj := by decide
  player k := if k = 2 ∨ k = 4 then some 1 else some 0
  natureProb _ _ := 0
  nature_nonneg := fun k hk => absurd hk (by split_ifs <;> simp)
  nature_zero := fun k hk => absurd hk (by split_ifs <;> simp)
  nature_sum := fun k hk => absurd hk (by split_ifs <;> simp)
  payoff := ecPay x

theorem ec_noNature (x : ℝ) (k : Fin 5) : (ecGame x).player k ≠ none := by
  simp only [ecGame]
  split_ifs <;> simp

theorem ec_assemble (x : ℝ) (F : Fin 2 → Fin 5 → Fin 2 → ℝ) (k : Fin 5) :
    (ecGame x).assemble F k = F (if k = 2 ∨ k = 4 then 1 else 0) k := by
  have : (ecGame x).player k = some (if k = 2 ∨ k = 4 then 1 else 0) := by
    simp only [ecGame]
    split_ifs <;> rfl
  rw [(ecGame x).assemble_of_some F this]

/-- The continuation payoffs of the game of Exercise 9.B.10 at the roots of its subgames. -/
theorem ec_cont (x : ℝ) (f : Fin 5 → Fin 2 → ℝ) (i : Fin 2) :
    cont (ecGame x) f [1, 1, 1] i = f 3 0 * (f 4 0 * ecPay x i [0, 0, 1, 1, 1] +
      f 4 1 * ecPay x i [1, 0, 1, 1, 1]) + f 3 1 * (f 4 0 * ecPay x i [0, 1, 1, 1, 1] +
      f 4 1 * ecPay x i [1, 1, 1, 1, 1]) ∧
    cont (ecGame x) f [1] i = f 1 0 * (f 2 0 * ecPay x i [0, 0, 1] +
      f 2 1 * ecPay x i [1, 0, 1]) + f 1 1 * (f 2 0 * ecPay x i [0, 1, 1] +
      f 2 1 * cont (ecGame x) f [1, 1, 1] i) ∧
    cont (ecGame x) f [] i = f 0 0 * ecPay x i [0] + f 0 1 * cont (ecGame x) f [1] i := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [cont_unfold, ecGame, ecInfo, Fin.sum_univ_two]

theorem ec_cont3 (x : ℝ) (f : Fin 5 → Fin 2 → ℝ) (i : Fin 2) :
    cont (ecGame x) f [1, 1, 1] i = f 3 0 * (f 4 0 * ecPay x i [0, 0, 1, 1, 1] +
      f 4 1 * ecPay x i [1, 0, 1, 1, 1]) + f 3 1 * (f 4 0 * ecPay x i [0, 1, 1, 1, 1] +
      f 4 1 * ecPay x i [1, 1, 1, 1, 1]) := (ec_cont x f i).1

theorem ec_cont1 (x : ℝ) (f : Fin 5 → Fin 2 → ℝ) (i : Fin 2) :
    cont (ecGame x) f [1] i = f 1 0 * (f 2 0 * ecPay x i [0, 0, 1] +
      f 2 1 * ecPay x i [1, 0, 1]) + f 1 1 * (f 2 0 * ecPay x i [0, 1, 1] +
      f 2 1 * cont (ecGame x) f [1, 1, 1] i) := (ec_cont x f i).2.1

theorem ec_cont0 (x : ℝ) (f : Fin 5 → Fin 2 → ℝ) (i : Fin 2) :
    cont (ecGame x) f [] i = f 0 0 * ecPay x i [0] + f 0 1 * cont (ecGame x) f [1] i :=
  (ec_cont x f i).2.2

theorem ec_decisionNodes (x : ℝ) :
    (ecGame x).decisionNodes = {[], [1], [0, 1], [1, 1], [1, 1, 1], [0, 1, 1, 1], [1, 1, 1, 1]} :=
  (by decide : (ecGame 0).decisionNodes =
    {[], [1], [0, 1], [1, 1], [1, 1, 1], [0, 1, 1, 1], [1, 1, 1, 1]})

/-- The subgames of the game of Exercise 9.B.10: the whole game, the post-entry game and the
coordination game. -/
theorem ec_subgames (x : ℝ) (y : List (Fin 2)) :
    IsSubgameRoot (ecGame x) y ↔ y = [] ∨ y = [1] ∨ y = [1, 1, 1] := by
  have hdn := ec_decisionNodes x
  have hdec : ∀ y, (ecGame x).IsDecision y ↔ y = [] ∨ y = [1] ∨ y = [0, 1] ∨ y = [1, 1] ∨
      y = [1, 1, 1] ∨ y = [0, 1, 1, 1] ∨ y = [1, 1, 1, 1] :=
    fun y => by rw [← mem_decisionNodes, hdn]; simp
  have hinfo : ∀ y, (ecGame x).info y = ecInfo y := fun _ => rfl
  constructor
  · intro h
    rcases (hdec y).1 h.1 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact absurd (h.2.1 [1, 1] ((hdec _).2 (by simp)) rfl) (by simp)
    · exact absurd (h.2.1 [0, 1] ((hdec _).2 (by simp)) rfl) (by simp)
    · exact Or.inr (Or.inr rfl)
    · exact absurd (h.2.1 [1, 1, 1, 1] ((hdec _).2 (by simp)) rfl) (by simp)
    · exact absurd (h.2.1 [0, 1, 1, 1] ((hdec _).2 (by simp)) rfl) (by simp)
  · rintro (rfl | rfl | rfl)
    · refine ⟨(hdec _).2 (by simp), fun y hy he => ?_, fun _ _ _ _ _ _ => List.nil_suffix⟩
      rcases (hdec y).1 hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp_all [ecInfo]
    · refine ⟨(hdec _).2 (by simp), fun y hy he => ?_, fun y hy hxy y' hy' he => ?_⟩
      · rcases (hdec y).1 hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp_all [ecInfo]
      · rcases (hdec y).1 hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        rcases (hdec y').1 hy' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        revert he hxy <;> simp only [hinfo] <;> decide
    · refine ⟨(hdec _).2 (by simp), fun y hy he => ?_, fun y hy hxy y' hy' he => ?_⟩
      · rcases (hdec y).1 hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp_all [ecInfo]
      · rcases (hdec y).1 hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        rcases (hdec y').1 hy' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        revert he hxy <;> simp only [hinfo] <;> decide

theorem ec_beh (x : ℝ) (i : Fin 2) {g : Fin 5 → Fin 2 → ℝ}
    (hg : (ecGame x).IsBehaviorStrategy i g) (k : Fin 5)
    (hk : (if k = 2 ∨ k = 4 then some (1 : Fin 2) else some 0) = some i) :
    0 ≤ g k 0 ∧ 0 ≤ g k 1 ∧ g k 0 + g k 1 = 1 := by
  have h := hg k hk
  exact ⟨h.1 0, h.1 1, by simpa [ecGame] using h.2.2⟩

theorem ec_spne_U (x : ℝ) : IsSPNE (ecGame x) (pureMoves ![1, 1, 1, 0, 0]) := by
  refine ⟨isBehaviorProfile_pureMoves fun _ => Finset.mem_univ _, fun y hy => ?_⟩
  rcases (ec_subgames x y).1 hy with rfl | rfl | rfl <;> rw [InducesNashAt, Fin.forall_fin_two] <;>
    constructor <;> intro g hg
  all_goals first
    | (obtain ⟨a0, a1, a2⟩ := ec_beh x 0 hg 0 (by simp)
       obtain ⟨b0, b1, b2⟩ := ec_beh x 0 hg 1 (by simp)
       obtain ⟨d0, d1, d2⟩ := ec_beh x 0 hg 3 (by simp)
       simp [ec_cont0, ec_cont1, ec_cont3, ec_assemble, pureMoves, dirac, ecPay]
       nlinarith [mul_nonneg a1 b0, mul_nonneg a1 b1, mul_nonneg (mul_nonneg a1 b1) d0,
         mul_nonneg (mul_nonneg a1 b1) d1, mul_nonneg b1 d1, mul_nonneg b1 d0])
    | (obtain ⟨e0, e1, e2⟩ := ec_beh x 1 hg 2 (by simp)
       obtain ⟨f0, f1, f2⟩ := ec_beh x 1 hg 4 (by simp)
       simp [ec_cont0, ec_cont1, ec_cont3, ec_assemble, pureMoves, dirac, ecPay]
       nlinarith [mul_nonneg e1 f0, mul_nonneg e1 f1, mul_nonneg e0 f0, mul_nonneg e0 f1])

theorem ec_spne_D (x : ℝ) (hx : 1 ≤ x) : IsSPNE (ecGame x) (pureMoves ![1, 1, 1, 1, 1]) := by
  refine ⟨isBehaviorProfile_pureMoves fun _ => Finset.mem_univ _, fun y hy => ?_⟩
  have hx0 : 0 ≤ x - 1 := by linarith
  rcases (ec_subgames x y).1 hy with rfl | rfl | rfl <;> rw [InducesNashAt, Fin.forall_fin_two] <;>
    constructor <;> intro g hg
  all_goals first
    | (obtain ⟨a0, a1, a2⟩ := ec_beh x 0 hg 0 (by simp)
       obtain ⟨b0, b1, b2⟩ := ec_beh x 0 hg 1 (by simp)
       obtain ⟨d0, d1, d2⟩ := ec_beh x 0 hg 3 (by simp)
       have h3 : x * g 0 1 * g 1 1 * (g 3 0 + g 3 1) = x * g 0 1 * g 1 1 := by rw [d2, mul_one]
       have h4 : x * g 0 1 * (g 1 0 + g 1 1) = x * g 0 1 := by rw [b2, mul_one]
       have h5 : x * g 1 1 * (g 3 0 + g 3 1) = x * g 1 1 := by rw [d2, mul_one]
       simp [ec_cont0, ec_cont1, ec_cont3, ec_assemble, pureMoves, dirac, ecPay]
       nlinarith [h3, h4, h5, mul_nonneg a1 b0, mul_nonneg a1 b1, mul_nonneg (mul_nonneg a1 b1) d0,
         mul_nonneg (mul_nonneg a1 b1) d1, mul_nonneg b1 d1, mul_nonneg b1 d0,
         mul_nonneg hx0 (mul_nonneg a1 b0), mul_nonneg hx0 b0, mul_nonneg hx0 a0,
         mul_nonneg (by linarith : (0 : ℝ) ≤ x) (mul_nonneg (mul_nonneg a1 b1) d0),
         mul_nonneg (by linarith : (0 : ℝ) ≤ x) (mul_nonneg b1 d0),
         mul_nonneg (by linarith : (0 : ℝ) ≤ x) d0, mul_nonneg (by linarith : (0 : ℝ) ≤ x) a0])
    | (obtain ⟨e0, e1, e2⟩ := ec_beh x 1 hg 2 (by simp)
       obtain ⟨f0, f1, f2⟩ := ec_beh x 1 hg 4 (by simp)
       simp [ec_cont0, ec_cont1, ec_cont3, ec_assemble, pureMoves, dirac, ecPay]
       nlinarith [mul_nonneg e1 f0, mul_nonneg e1 f1, mul_nonneg e0 f0, mul_nonneg e0 f1])

/-- **Exercise 9.B.10** (MWG, p. 303). The pure strategy subgame perfect Nash equilibria, for
every `x`: ((in, accommodate, `U`), (accommodate, `ℓ`)) always, and ((in, accommodate, `D`),
(accommodate, `r`)) exactly when `x ≥ 1`. (Moves are listed by information set: E's entry,
E's post-entry move, I's post-entry move, E's and I's moves in the coordination game.) -/
theorem exercise_9_B_10_pure (x : ℝ) (c : Fin 5 → Fin 2) :
    IsSPNE (ecGame x) (pureMoves c) ↔ c = ![1, 1, 1, 0, 0] ∨ (1 ≤ x ∧ c = ![1, 1, 1, 1, 1]) := by
  have hN := ec_noNature x
  have hsub := ec_subgames x
  have hA := fun c' : Fin 5 → Fin 2 => assemble_pureMoves (G := ecGame x) (I := Fin 2) hN c'
  constructor
  · intro h
    have d : ∀ y, y = [] ∨ y = [1] ∨ y = [1, 1, 1] → ∀ (k : Fin 5) (a : Fin 2),
        cont (ecGame x) (fun k' => dirac (Function.update c k a k')) y
            (if k = 2 ∨ k = 4 then 1 else 0) ≤
          cont (ecGame x) (fun k' => dirac (c k')) y (if k = 2 ∨ k = 4 then 1 else 0) := by
      intro y hy k a
      have := h.pure_dev (fun _ => Finset.mem_univ _) ((hsub y).2 hy) (k := k)
        (i := if k = 2 ∨ k = 4 then 1 else 0) (by simp only [ecGame]; split_ifs <;> rfl)
        (Finset.mem_univ a)
      rwa [hA, hA] at this
    have d30 := d [1, 1, 1] (by simp) 3 0
    have d31 := d [1, 1, 1] (by simp) 3 1
    have d40 := d [1, 1, 1] (by simp) 4 0
    have d41 := d [1, 1, 1] (by simp) 4 1
    have d10 := d [1] (by simp) 1 0
    have d11 := d [1] (by simp) 1 1
    have d20 := d [1] (by simp) 2 0
    have d21 := d [1] (by simp) 2 1
    have d00 := d [] (by simp) 0 0
    have d01 := d [] (by simp) 0 1
    clear d
    simp only [ec_cont0, ec_cont1, ec_cont3] at d30 d31 d40 d41 d10 d11 d20 d21 d00 d01
    obtain ⟨c0, c1, c2, c3, c4, rfl⟩ : ∃ c0 c1 c2 c3 c4 : Fin 2, c = ![c0, c1, c2, c3, c4] :=
      ⟨c 0, c 1, c 2, c 3, c 4, by funext k; fin_cases k <;> rfl⟩
    have h2 : ∀ k : Fin 2, k = 0 ∨ k = 1 := by decide
    rcases h2 c0 with rfl | rfl <;> rcases h2 c1 with rfl | rfl <;>
      rcases h2 c2 with rfl | rfl <;> rcases h2 c3 with rfl | rfl <;>
      rcases h2 c4 with rfl | rfl <;>
      norm_num [dirac, Function.update_apply, ecPay] at * <;>
      first | exact Or.inl rfl | linarith
  · rintro (rfl | ⟨hx, rfl⟩)
    · exact ec_spne_U x
    · exact ec_spne_D x hx

/-- **Exercise 9.B.10, `x < 0`** (MWG, p. 303). If `x < 0`, `D` is strictly dominated by `U` in
the coordination game, so its unique equilibrium is `(U, ℓ)` with payoffs `(3, 1)`, and the game
reduces to Example 9.B.3: the unique SPNE (among all behaviour profiles) is ((in, accommodate,
`U`), (accommodate, `ℓ`)). -/
theorem exercise_9_B_10_neg (x : ℝ) (hx : x < 0) :
    IsSPNE (ecGame x) (pureMoves ![1, 1, 1, 0, 0]) ∧ ∀ F, IsSPNE (ecGame x) F →
      F 0 0 1 = 1 ∧ F 0 1 1 = 1 ∧ F 1 2 1 = 1 ∧ F 0 3 0 = 1 ∧ F 1 4 0 = 1 := by
  refine ⟨ec_spne_U x, fun F hF => ?_⟩
  have hsub := ec_subgames x
  have hb0 := ec_beh x 0 (hF.1 0) 0 (by simp)
  have hb1 := ec_beh x 0 (hF.1 0) 1 (by simp)
  have hb2 := ec_beh x 1 (hF.1 1) 2 (by simp)
  have hb3 := ec_beh x 0 (hF.1 0) 3 (by simp)
  have hb4 := ec_beh x 1 (hF.1 1) 4 (by simp)
  have hdev : ∀ (i : Fin 2) (k : Fin 5) (a : Fin 2),
      (if k = 2 ∨ k = 4 then some (1 : Fin 2) else some 0) = some i →
      (ecGame x).IsBehaviorStrategy i (Function.update (F i) k (dirac a)) := by
    intro i k a hk k' hk'
    by_cases hkk : k' = k
    · subst hkk
      simp only [Function.update_self]
      exact (isBehaviorProfile_pureMoves (I := Fin 2) (G := ecGame x) (c := fun _ => a)
        fun _ => Finset.mem_univ _) i k' hk'
    · rw [Function.update_of_ne hkk]
      exact hF.1 i k' hk'
  have hpos : 0 < 3 * F 1 4 0 - x * F 1 4 1 := by
    rcases eq_or_lt_of_le hb4.1 with h | h
    · have h1 : F 1 4 1 = 1 := by linarith [hb4.2.2]
      rw [← h, h1]
      linarith
    · nlinarith [mul_nonneg hb4.2.1 (neg_nonneg.2 hx.le)]
  -- in the coordination game E plays `U`
  have hE3 := hF.2 [1, 1, 1] ((hsub _).2 (by simp)) 0 _ (hdev 0 3 0 (by simp))
  simp [ec_cont3, ec_assemble, dirac, ecPay] at hE3
  have hU : F 0 3 1 = 0 := by
    by_contra hne
    have h1 : 0 < F 0 3 1 := lt_of_le_of_ne hb3.2.1 (Ne.symm hne)
    nlinarith [mul_pos h1 hpos]
  have hU0 : F 0 3 0 = 1 := by linarith [hb3.2.2]
  -- then I plays `ℓ`
  have hI4 := hF.2 [1, 1, 1] ((hsub _).2 (by simp)) 1 _ (hdev 1 4 0 (by simp))
  simp [ec_cont3, ec_assemble, dirac, ecPay, hU, hU0] at hI4
  have hl : F 1 4 0 = 1 := by linarith [hb4.2.2]
  have hl1 : F 1 4 1 = 0 := by linarith [hb4.2.2]
  -- in the post-entry game E accommodates
  have hE1 := hF.2 [1] ((hsub _).2 (by simp)) 0 _ (hdev 0 1 1 (by simp))
  simp [ec_cont1, ec_cont3, ec_assemble, dirac, ecPay, hU, hU0, hl, hl1] at hE1
  have hp : F 0 1 1 = 1 := by nlinarith [mul_nonneg hb1.1 hb2.2.1]
  have hp0 : F 0 1 0 = 0 := by linarith [hb1.2.2]
  -- then I accommodates
  have hI2 := hF.2 [1] ((hsub _).2 (by simp)) 1 _ (hdev 1 2 1 (by simp))
  simp [ec_cont1, ec_cont3, ec_assemble, dirac, ecPay, hU, hU0, hl, hl1, hp, hp0] at hI2
  have hq : F 1 2 1 = 1 := by nlinarith [hb2.2.2]
  have hq0 : F 1 2 0 = 0 := by linarith [hb2.2.2]
  -- then E enters
  have hE0 := hF.2 [] ((hsub _).2 (by simp)) 0 _ (hdev 0 0 1 (by simp))
  simp [ec_cont0, ec_cont1, ec_cont3, ec_assemble, dirac, ecPay, hU, hU0, hl, hl1, hp, hp0, hq,
    hq0] at hE0
  exact ⟨by nlinarith [hb0.2.2], hp, hq, hU0, hl⟩

/-- The profile of `exercise_9_B_10_mixed`: E enters and accommodates, I accommodates, and in
the coordination game E plays `U` with probability `3/4` and I plays `ℓ` with probability
`1/2`. -/
noncomputable def ecMixed : Fin 2 → Fin 5 → Fin 2 → ℝ :=
  fun _ k => if k = 3 then ![3 / 4, 1 / 4] else if k = 4 then ![1 / 2, 1 / 2] else ![0, 1]

/-- **Exercise 9.B.10, mixed equilibria** (MWG, p. 303). The mixed equilibria of the
coordination game matter for the answer when `x ≥ 0`: for `x = 3`, entering and accommodating,
with the mixed coordination equilibrium (`U` with probability `3/4`, `ℓ` with probability
`1/2`) after (accommodate, accommodate), is a further SPNE, giving E the payoff `3/2` (the pure
SPNE give `3` and `x = 3`). -/
theorem exercise_9_B_10_mixed :
    IsSPNE (ecGame 3) ecMixed ∧ cont (ecGame 3) ((ecGame 3).assemble ecMixed) [] 0 = 3 / 2 := by
  have hval : ecMixed 0 0 = ![0, 1] ∧ ecMixed 0 1 = ![0, 1] ∧ ecMixed 1 2 = ![0, 1] ∧
      ecMixed 0 3 = ![3 / 4, 1 / 4] ∧ ecMixed 1 4 = ![1 / 2, 1 / 2] := ⟨rfl, rfl, rfl, rfl, rfl⟩
  refine ⟨⟨fun i k _ => ?_, fun y hy => ?_⟩, ?_⟩
  · refine ⟨fun a => ?_, fun a ha => absurd (Finset.mem_univ a) ha, ?_⟩
    · fin_cases a <;> simp [ecMixed] <;> split_ifs <;> norm_num
    · simp [ecMixed, ecGame, Fin.sum_univ_two]
      split_ifs <;> norm_num
  · rcases (ec_subgames 3 y).1 hy with rfl | rfl | rfl <;>
      rw [InducesNashAt, Fin.forall_fin_two] <;> constructor <;> intro g hg
    all_goals first
      | (obtain ⟨a0, a1, a2⟩ := ec_beh 3 0 hg 0 (by simp)
         obtain ⟨b0, b1, b2⟩ := ec_beh 3 0 hg 1 (by simp)
         obtain ⟨d0, d1, d2⟩ := ec_beh 3 0 hg 3 (by simp)
         simp [ec_cont0, ec_cont1, ec_cont3, ec_assemble, hval, ecPay]
         nlinarith [mul_nonneg a1 b0, mul_nonneg a1 b1, mul_nonneg (mul_nonneg a1 b1) d0,
           mul_nonneg (mul_nonneg a1 b1) d1, mul_nonneg b1 d1, mul_nonneg b1 d0])
      | (obtain ⟨e0, e1, e2⟩ := ec_beh 3 1 hg 2 (by simp)
         obtain ⟨f0, f1, f2⟩ := ec_beh 3 1 hg 4 (by simp)
         simp [ec_cont0, ec_cont1, ec_cont3, ec_assemble, hval, ecPay]
         nlinarith [mul_nonneg e1 f0, mul_nonneg e1 f1, mul_nonneg e0 f0, mul_nonneg e0 f1])
  · simp [ec_cont0, ec_cont1, ec_cont3, ec_assemble, hval, ecPay]
    norm_num

end MWG.DynamicGames
