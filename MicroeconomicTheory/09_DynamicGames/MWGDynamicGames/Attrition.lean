/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGDynamicGames.OfferCosts

/-!
# A war of attrition in a declining market

MWG, Exercise 9.B.11 (p. 303). Two firms, A (index `0`) and B (index `1`), are in a market in
periods `t = 0, 1, 2, …`. At the start of each period each active firm stays in or exits
(simultaneously if both are active); exit is permanent. A firm earns the duopoly profit
`duo i t` in a period in which both firms are in, the monopoly profit `mono i t` in a period in
which it is alone, and `0` once out; payoffs are undiscounted sums.

The model is an infinite-horizon game. A firm's information at a decision node is the date
`t` and the rival's status: `none` (the rival is still in) or `some u` (the rival exited at
the start of period `u < t`); this is the whole history, since before an exit every move was
"stay". A profile (`AttritionProfile`) gives each firm's move at every such node, and
`IsSPNE` is subgame perfection at every node (`t`, both in) and (`t`, alone after the rival's
exit at `u`). A firm that never exits earns `⊥` (`−∞`): its profits eventually fall below
every negative bound in the exercise.

* `jointValue_eq`, `monoValue_eq`: the recursions of the payoffs.
* `monopoly_spne`: in an SPNE a monopolist with profits positive up to `L` and negative after
  stays exactly in the periods `t ≤ L` (the truncation: from `L + 1` on staying is
  dominated, then backward induction over finitely many periods).
* `exercise_9_B_11`: with MWG's profits `105 − 10t`, `10.5 − t` (duopoly) and `510 − 25t`,
  `51 − 2t` (monopoly) there is a unique SPNE. While both are in, A stays exactly in
  periods `t ≤ 10` and B exactly in periods `t ≤ 25`; as a monopolist A stays exactly for
  `t ≤ 20` and B for `t ≤ 25`. The outcome: both stay in periods `0, …, 10`, A exits at the
  start of period 11, B is a monopolist in periods `11, …, 25` and exits at the start of
  period 26. Payoffs: `605` for A and `285.5` for B.
-/

namespace MWG.DynamicGames

/-- A two-firm war of attrition: duopoly and monopoly profits in each period. -/
structure AttritionGame where
  /-- Firm `i`'s profit in period `t` when both firms are in. -/
  duo : Fin 2 → ℕ → ℝ
  /-- Firm `i`'s profit in period `t` when it is alone in the market. -/
  mono : Fin 2 → ℕ → ℝ

/-- A strategy profile of the war of attrition: `stay i t none` is firm `i`'s move (`true` =
stay in) at date `t` when both firms are in; `stay i t (some u)` its move at date `t` when the
rival exited at the start of period `u < t`. -/
structure AttritionProfile where
  /-- The moves. -/
  stay : Fin 2 → ℕ → Option ℕ → Bool

namespace AttritionGame

open BargainingGame (other other_ne ne_other)

variable (A : AttritionGame)

/-- Firm `i`'s payoff from the node at date `t` where it is alone in the market (the rival
exited at `u`): monopoly profits until it exits. -/
noncomputable def monoValue (s : AttritionProfile) (i : Fin 2) (t u : ℕ) : WithBot ℝ :=
  firstStop (fun k => s.stay i (t + k) (some u)) (fun k => A.mono i (t + k)) (fun _ => 0)

/-- Firm `i`'s payoff from the node at date `t` where both firms are in: duopoly profits until
the first exit; if then only the rival exits, monopoly profits from that period on. -/
noncomputable def jointValue (s : AttritionProfile) (i : Fin 2) (t : ℕ) : WithBot ℝ :=
  firstStop (fun k => s.stay 0 (t + k) none && s.stay 1 (t + k) none) (fun k => A.duo i (t + k))
    (fun k => if s.stay i (t + k) none = true then
      ((A.mono i (t + k) : ℝ) : WithBot ℝ) + A.monoValue s i (t + k + 1) (t + k) else 0)

theorem monoValue_eq (s : AttritionProfile) (i : Fin 2) (t u : ℕ) :
    A.monoValue s i t u = if s.stay i t (some u) = true then
      ((A.mono i t : ℝ) : WithBot ℝ) + A.monoValue s i (t + 1) u else 0 := by
  unfold monoValue
  rw [firstStop_eq]
  simp only [add_zero]
  congr 3
  · funext k
    rw [show t + (k + 1) = t + 1 + k by omega]
  · funext k
    rw [show t + (k + 1) = t + 1 + k by omega]

/-- Firm `i`'s payoff from staying in at the date-`t` node where both firms are in. -/
noncomputable def stayValue (s : AttritionProfile) (i : Fin 2) (t : ℕ) : WithBot ℝ :=
  if s.stay (other i) t none = true then ((A.duo i t : ℝ) : WithBot ℝ) + A.jointValue s i (t + 1)
  else ((A.mono i t : ℝ) : WithBot ℝ) + A.monoValue s i (t + 1) t

theorem jointValue_eq (s : AttritionProfile) (i : Fin 2) (t : ℕ) :
    A.jointValue s i t = if s.stay i t none = true then A.stayValue s i t else 0 := by
  unfold stayValue
  conv_lhs => unfold jointValue
  rw [firstStop_eq]
  simp only [add_zero]
  have hj : firstStop (fun k => s.stay 0 (t + (k + 1)) none && s.stay 1 (t + (k + 1)) none)
      (fun k => A.duo i (t + (k + 1))) (fun k => if s.stay i (t + (k + 1)) none = true then
        ((A.mono i (t + (k + 1)) : ℝ) : WithBot ℝ) +
          A.monoValue s i (t + (k + 1) + 1) (t + (k + 1)) else 0) = A.jointValue s i (t + 1) := by
    unfold jointValue
    congr 1
    · funext k
      rw [show t + (k + 1) = t + 1 + k by omega]
    · funext k
      rw [show t + (k + 1) = t + 1 + k by omega]
    · funext k
      rw [show t + (k + 1) = t + 1 + k by omega]
  rw [hj]
  fin_cases i <;> cases h0 : s.stay 0 t none <;> cases h1 : s.stay 1 t none <;>
    simp [h0, h1, other]

/-- **Definition 9.B.2 for the war of attrition** (MWG, pp. 275 and 303). A subgame perfect
Nash equilibrium: at every node where both firms are in (date `t`) and at every node where firm
`i` is alone (date `t`, rival out since `u < t`), no firm gains by changing its strategy. -/
def IsSPNE (s : AttritionProfile) : Prop :=
  ∀ i (s' : AttritionProfile), s'.stay (other i) = s.stay (other i) → ∀ t,
    A.jointValue s' i t ≤ A.jointValue s i t ∧ ∀ u < t, A.monoValue s' i t u ≤ A.monoValue s i t u

/-- Changing firm `i`'s move at the single node `(t₀, e₀)`. -/
def setStay (s : AttritionProfile) (i : Fin 2) (t₀ : ℕ) (e₀ : Option ℕ) (b : Bool) :
    AttritionProfile :=
  ⟨fun j t e => if j = i ∧ t = t₀ ∧ e = e₀ then b else s.stay j t e⟩

theorem setStay_other (s : AttritionProfile) (i : Fin 2) (t₀ : ℕ) (e₀ : Option ℕ) (b : Bool) :
    (setStay s i t₀ e₀ b).stay (other i) = s.stay (other i) := by
  funext t e
  simp [setStay, other_ne]

theorem setStay_self (s : AttritionProfile) (i : Fin 2) (t₀ : ℕ) (e₀ : Option ℕ) (b : Bool) :
    (setStay s i t₀ e₀ b).stay i t₀ e₀ = b := by
  simp [setStay]

theorem monoValue_setStay (s : AttritionProfile) (i : Fin 2) {t₀ : ℕ} {e₀ : Option ℕ}
    (b : Bool) {t u : ℕ} (h : t₀ < t ∨ e₀ ≠ some u) :
    A.monoValue (setStay s i t₀ e₀ b) i t u = A.monoValue s i t u := by
  have hk : ∀ k, (setStay s i t₀ e₀ b).stay i (t + k) (some u) = s.stay i (t + k) (some u) := by
    intro k
    simp only [setStay]
    split_ifs with hc
    · rcases h with h | h
      · omega
      · exact absurd hc.2.2.symm h
    · rfl
  simp only [monoValue, hk]

theorem jointValue_setStay (s : AttritionProfile) (i : Fin 2) {t₀ : ℕ} (b : Bool) {t : ℕ}
    (h : t₀ < t) : A.jointValue (setStay s i t₀ none b) i t = A.jointValue s i t := by
  have hk : ∀ j k, (setStay s i t₀ none b).stay j (t + k) none = s.stay j (t + k) none := by
    intro j k
    simp only [setStay]
    split_ifs with hc
    · omega
    · rfl
  have hm : ∀ r u, A.monoValue (setStay s i t₀ none b) i r u = A.monoValue s i r u :=
    fun r u => A.monoValue_setStay s i b (Or.inr (by simp))
  simp only [jointValue, hk, hm]

theorem stayValue_setStay (s : AttritionProfile) (i : Fin 2) (t : ℕ) (b : Bool) :
    A.stayValue (setStay s i t none b) i t = A.stayValue s i t := by
  unfold stayValue
  rw [setStay_other, A.jointValue_setStay s i b (Nat.lt_succ_self t),
    A.monoValue_setStay s i b (Or.inr (by simp))]

/-- In an SPNE a firm stays in when staying is strictly profitable (both firms in). -/
theorem stay_of_pos {s : AttritionProfile} (hs : A.IsSPNE s) {i : Fin 2} {t : ℕ}
    (h : 0 < A.stayValue s i t) : s.stay i t none = true := by
  by_contra hc
  have hc' : s.stay i t none = false := by simpa using hc
  have := (hs i (setStay s i t none true) (setStay_other s i t none true) t).1
  rw [A.jointValue_eq, A.jointValue_eq, setStay_self, hc', A.stayValue_setStay] at this
  simp only [↓reduceIte, Bool.false_eq_true] at this
  exact absurd this (not_le.2 h)

/-- In an SPNE a firm exits when staying is strictly unprofitable (both firms in). -/
theorem exit_of_neg {s : AttritionProfile} (hs : A.IsSPNE s) {i : Fin 2} {t : ℕ}
    (h : A.stayValue s i t < 0) : s.stay i t none = false := by
  by_contra hc
  have hc' : s.stay i t none = true := by simpa using hc
  have := (hs i (setStay s i t none false) (setStay_other s i t none false) t).1
  rw [A.jointValue_eq, A.jointValue_eq, setStay_self, hc'] at this
  simp only [↓reduceIte, Bool.false_eq_true] at this
  exact absurd this (not_le.2 h)

/-- In an SPNE a monopolist stays in when staying is strictly profitable. -/
theorem monoStay_of_pos {s : AttritionProfile} (hs : A.IsSPNE s) {i : Fin 2} {t u : ℕ}
    (hu : u < t) (h : 0 < ((A.mono i t : ℝ) : WithBot ℝ) + A.monoValue s i (t + 1) u) :
    s.stay i t (some u) = true := by
  by_contra hc
  have hc' : s.stay i t (some u) = false := by simpa using hc
  have := (hs i (setStay s i t (some u) true) (setStay_other s i t (some u) true) t).2 u hu
  rw [A.monoValue_eq (setStay s i t (some u) true) i t u, A.monoValue_eq s i t u, setStay_self,
    hc',
    A.monoValue_setStay s i true (Or.inl (Nat.lt_succ_self t))] at this
  simp only [↓reduceIte, Bool.false_eq_true] at this
  exact absurd this (not_le.2 h)

/-- In an SPNE a monopolist exits when staying is strictly unprofitable. -/
theorem monoExit_of_neg {s : AttritionProfile} (hs : A.IsSPNE s) {i : Fin 2} {t u : ℕ}
    (hu : u < t) (h : ((A.mono i t : ℝ) : WithBot ℝ) + A.monoValue s i (t + 1) u < 0) :
    s.stay i t (some u) = false := by
  by_contra hc
  have hc' : s.stay i t (some u) = true := by simpa using hc
  have := (hs i (setStay s i t (some u) false) (setStay_other s i t (some u) false) t).2 u hu
  rw [A.monoValue_eq (setStay s i t (some u) false) i t u, A.monoValue_eq s i t u, setStay_self,
    hc'] at this
  simp only [↓reduceIte, Bool.false_eq_true] at this
  exact absurd this (not_le.2 h)

/-- An upper bound on a monopolist's payoff by a one-stage condition. -/
theorem monoValue_le (s : AttritionProfile) (i : Fin 2) (t u : ℕ) (M : ℕ → ℝ)
    (hrec : ∀ r, A.mono i r + M (r + 1) ≤ M r) (h0 : ∀ r, 0 ≤ M r) :
    A.monoValue s i t u ≤ (M t : WithBot ℝ) := by
  have := firstStop_le (c := fun k => s.stay i (t + k) (some u)) (f := fun k => A.mono i (t + k))
    (g := fun _ => 0) (fun k => M (t + k)) (fun k _ => by rw [← add_assoc]; exact hrec _)
    (fun k _ => WithBot.coe_le_coe.2 (h0 _))
  unfold monoValue
  simpa using this

/-- **The monopolist's problem** (MWG, Exercise 9.B.11, p. 303). If firm `i`'s monopoly profit
is positive up to date `L` and negative afterwards, and `M` is its value of staying exactly up to
`L` (`M t = mono t + M (t + 1)` for `t ≤ L`, `M t = 0` after `L`), then in every SPNE a
monopolist `i` (rival out since `u`) stays exactly at the dates `t ≤ L` and earns `M t`. From
`L + 1` on, staying is dominated (all later profits are negative); before, backward induction
over the finitely many dates `t ≤ L` applies. -/
theorem monopoly_spne {s : AttritionProfile} (hs : A.IsSPNE s) (i : Fin 2) (L : ℕ)
    (M : ℕ → ℝ) (hpos : ∀ t ≤ L, 0 < A.mono i t) (hneg : ∀ t, L < t → A.mono i t < 0)
    (hM : ∀ t ≤ L, M t = A.mono i t + M (t + 1)) (hM0 : ∀ t, L < t → M t = 0)
    (hnn : ∀ t, 0 ≤ M t) :
    ∀ u t, u < t → s.stay i t (some u) = decide (t ≤ L) ∧ A.monoValue s i t u = (M t : ℝ) := by
  intro u
  have hrec : ∀ r, A.mono i r + M (r + 1) ≤ M r := by
    intro r
    by_cases hr : r ≤ L
    · rw [hM r hr]
    · rw [hM0 r (by omega), hM0 (r + 1) (by omega)]
      linarith [hneg r (by omega)]
  -- after `L`: exit
  have hlate : ∀ t, L < t → u < t →
      s.stay i t (some u) = decide (t ≤ L) ∧ A.monoValue s i t u = (M t : ℝ) := by
    intro t hLt hut
    have hle := A.monoValue_le s i (t + 1) u M hrec hnn
    rw [hM0 (t + 1) (by omega)] at hle
    have hex : s.stay i t (some u) = false := by
      refine A.monoExit_of_neg hs hut (lt_of_le_of_lt (add_le_add le_rfl hle) ?_)
      rw [← WithBot.coe_add, ← WithBot.coe_zero, WithBot.coe_lt_coe]
      linarith [hneg t hLt]
    refine ⟨by rw [hex]; simp [not_le.2 hLt], ?_⟩
    rw [A.monoValue_eq, hex, hM0 t hLt]
    simp
  -- up to `L`: stay, by backward induction
  have key : ∀ d t, t + d = L + 1 → u < t →
      s.stay i t (some u) = decide (t ≤ L) ∧ A.monoValue s i t u = (M t : ℝ) := by
    intro d
    induction d with
    | zero => intro t ht hut; exact hlate t (by omega) hut
    | succ d ih =>
      intro t ht hut
      have hn := (ih (t + 1) (by omega) (by omega)).2
      have htL : t ≤ L := by omega
      have hst : s.stay i t (some u) = true := by
        refine A.monoStay_of_pos hs hut ?_
        rw [hn, ← WithBot.coe_add, ← WithBot.coe_zero, WithBot.coe_lt_coe]
        linarith [hpos t htL, hnn (t + 1)]
      refine ⟨by rw [hst]; simp [htL], ?_⟩
      rw [A.monoValue_eq, hst, hn, hM t htL]
      simp
  intro t hut
  by_cases hLt : L < t
  · exact hlate t hLt hut
  · exact key (L + 1 - t) t (by omega) hut

/-- A monopolist who stays exactly at the dates `t ≤ L` earns `M t`. -/
theorem monoValue_cutoff (s : AttritionProfile) (i : Fin 2) (u L : ℕ) (M : ℕ → ℝ)
    (hstay : ∀ t, s.stay i t (some u) = decide (t ≤ L))
    (hM : ∀ t ≤ L, M t = A.mono i t + M (t + 1)) (hM0 : ∀ t, L < t → M t = 0) :
    ∀ t, A.monoValue s i t u = (M t : ℝ) := by
  have key : ∀ d t, t + d = L + 1 → A.monoValue s i t u = (M t : ℝ) := by
    intro d
    induction d with
    | zero =>
      intro t ht
      rw [A.monoValue_eq, hstay, hM0 t (by omega)]
      simp [show ¬ t ≤ L by omega]
    | succ d ih =>
      intro t ht
      rw [A.monoValue_eq, hstay, ih (t + 1) (by omega), hM t (by omega)]
      simp [show t ≤ L by omega]
  intro t
  by_cases hLt : L < t
  · rw [A.monoValue_eq, hstay, hM0 t hLt]
    simp [not_le.2 hLt]
  · exact key (L + 1 - t) t (by omega)

/-- An upper bound on a firm's payoff from a node where both firms are in, by a one-stage
condition from date `t` on. -/
theorem jointValue_le (s : AttritionProfile) (i : Fin 2) (t : ℕ) (V : ℕ → ℝ)
    (hc : ∀ r, t ≤ r → s.stay 0 r none = true → s.stay 1 r none = true →
      A.duo i r + V (r + 1) ≤ V r)
    (hg : ∀ r, t ≤ r → s.stay i r none = true → s.stay (other i) r none = false →
      ((A.mono i r : ℝ) : WithBot ℝ) + A.monoValue s i (r + 1) r ≤ (V r : WithBot ℝ))
    (h0 : ∀ r, t ≤ r → 0 ≤ V r) : A.jointValue s i t ≤ (V t : WithBot ℝ) := by
  have := firstStop_le (c := fun k => s.stay 0 (t + k) none && s.stay 1 (t + k) none)
    (f := fun k => A.duo i (t + k))
    (g := fun k => if s.stay i (t + k) none = true then
      ((A.mono i (t + k) : ℝ) : WithBot ℝ) + A.monoValue s i (t + k + 1) (t + k) else 0)
    (fun k => V (t + k)) (fun k hk => ?_) (fun k hk => ?_)
  · unfold jointValue
    simpa using this
  · simp only [Bool.and_eq_true] at hk
    rw [← add_assoc]
    exact hc _ (by omega) hk.1 hk.2
  · by_cases hi : s.stay i (t + k) none = true
    · have ho : s.stay (other i) (t + k) none = false := by
        fin_cases i
        · simp_all [other]
        · simp_all [other]
      simp only [hi, ↓reduceIte]
      exact hg _ (by omega) hi ho
    · simp only [hi, Bool.false_eq_true, ↓reduceIte]
      exact WithBot.coe_le_coe.2 (h0 _ (by omega))

end AttritionGame

open BargainingGame (other) in
/-- **The declining market of Exercise 9.B.11** (MWG, p. 303). Duopoly profits `105 − 10t`
(firm A, index `0`) and `10.5 − t` (firm B, index `1`); monopoly profits `510 − 25t` and
`51 − 2t`. -/
noncomputable def declining : AttritionGame where
  duo i t := if i = 0 then 105 - 10 * (t : ℝ) else 21 / 2 - t
  mono i t := if i = 0 then 510 - 25 * (t : ℝ) else 51 - 2 * t

/-- The last date at which monopoly profit is positive: `20` for A, `25` for B. -/
def decL (i : Fin 2) : ℕ := if i = 0 then 20 else 25

/-- A monopolist's value of staying exactly up to `decL i`. -/
noncomputable def decM (i : Fin 2) (t : ℕ) : ℝ :=
  if i = 0 then (if t ≤ 20 then (21 - t) * (520 - 25 * t) / 2 else 0)
  else (if t ≤ 25 then (26 - t) ^ 2 else 0)

/-- A's SPNE value when both firms are in at date `t`. -/
noncomputable def decVA (t : ℕ) : ℝ := if t ≤ 10 then 5 * (11 - t) ^ 2 else 0

/-- B's SPNE value when both firms are in at date `t`. -/
noncomputable def decVB (t : ℕ) : ℝ :=
  if t ≤ 10 then (11 - t) ^ 2 / 2 + 225 else if t ≤ 25 then (26 - t) ^ 2 else 0

/-- The SPNE of Exercise 9.B.11: while both are in, A stays iff `t ≤ 10` and B iff `t ≤ 25`;
alone, A stays iff `t ≤ 20` and B iff `t ≤ 25`. -/
def attritionSPNE : AttritionProfile :=
  ⟨fun i t e => match e with
    | none => decide (t ≤ if i = 0 then 10 else 25)
    | some _ => decide (t ≤ decL i)⟩

theorem decM_rec (i : Fin 2) (t : ℕ) (ht : t ≤ decL i) :
    decM i t = declining.mono i t + decM i (t + 1) := by
  fin_cases i
  · simp only [decL, Fin.zero_eta, Fin.isValue, ↓reduceIte] at ht
    rcases Nat.lt_or_ge t 20 with h | h
    · simp only [decM, declining, Fin.zero_eta, Fin.isValue, ↓reduceIte, ht,
        show t + 1 ≤ 20 by omega]
      push_cast
      ring
    · simp only [decM, declining, Fin.zero_eta, Fin.isValue, ↓reduceIte, show t = 20 by omega]
      norm_num
  · simp only [decL, Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte] at ht
    rcases Nat.lt_or_ge t 25 with h | h
    · simp only [decM, declining, Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte, ht,
        show t + 1 ≤ 25 by omega]
      push_cast
      ring
    · simp only [decM, declining, Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte,
        show t = 25 by omega]
      norm_num

theorem decM_late (i : Fin 2) (t : ℕ) (ht : decL i < t) : decM i t = 0 := by
  fin_cases i
  · simp only [decL, Fin.zero_eta, Fin.isValue, ↓reduceIte] at ht
    simp [decM, show ¬ t ≤ 20 by omega]
  · simp only [decL, Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte] at ht
    simp [decM, show ¬ t ≤ 25 by omega]

theorem decM_nonneg (i : Fin 2) (t : ℕ) : 0 ≤ decM i t := by
  fin_cases i
  · simp only [decM, Fin.zero_eta, Fin.isValue, ↓reduceIte]
    split_ifs with h
    · have : (t : ℝ) ≤ 20 := by exact_mod_cast h
      apply div_nonneg _ (by norm_num)
      apply mul_nonneg <;> linarith
    · exact le_rfl
  · simp only [decM, Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte]
    split_ifs
    · positivity
    · exact le_rfl

theorem decMono_pos (i : Fin 2) (t : ℕ) (ht : t ≤ decL i) : 0 < declining.mono i t := by
  fin_cases i
  · simp only [decL, Fin.zero_eta, Fin.isValue, ↓reduceIte] at ht
    have : (t : ℝ) ≤ 20 := by exact_mod_cast ht
    simp only [declining, Fin.zero_eta, Fin.isValue, ↓reduceIte]
    linarith
  · simp only [decL, Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte] at ht
    have : (t : ℝ) ≤ 25 := by exact_mod_cast ht
    simp only [declining, Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte]
    linarith

theorem decMono_neg (i : Fin 2) (t : ℕ) (ht : decL i < t) : declining.mono i t < 0 := by
  fin_cases i
  · simp only [decL, Fin.zero_eta, Fin.isValue, ↓reduceIte] at ht
    have : (21 : ℝ) ≤ t := by exact_mod_cast ht
    simp only [declining, Fin.zero_eta, Fin.isValue, ↓reduceIte]
    linarith
  · simp only [decL, Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte] at ht
    have : (26 : ℝ) ≤ t := by exact_mod_cast ht
    simp only [declining, Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte]
    linarith

theorem decM_hrec (i : Fin 2) (r : ℕ) : declining.mono i r + decM i (r + 1) ≤ decM i r := by
  by_cases hr : r ≤ decL i
  · rw [decM_rec i r hr]
  · rw [decM_late i r (by omega), decM_late i (r + 1) (by omega)]
    linarith [decMono_neg i r (by omega)]

/-- **Exercise 9.B.11: the monopoly subgames** (MWG, p. 303). In every SPNE, a firm alone in the
market stays exactly while its monopoly profit is positive (A for `t ≤ 20`, B for `t ≤ 25`). -/
theorem exercise_9_B_11_monopoly {s : AttritionProfile} (hs : declining.IsSPNE s) (i : Fin 2) :
    ∀ u t, u < t → s.stay i t (some u) = decide (t ≤ decL i) ∧
      declining.monoValue s i t u = (decM i t : ℝ) :=
  declining.monopoly_spne hs i (decL i) (decM i) (decMono_pos i) (decMono_neg i) (decM_rec i)
    (decM_late i) (decM_nonneg i)

theorem decVA_rec (t : ℕ) (ht : t ≤ 10) : decVA t = declining.duo 0 t + decVA (t + 1) := by
  rcases Nat.lt_or_ge t 10 with h | h
  · simp only [decVA, declining, ↓reduceIte, ht, show t + 1 ≤ 10 by omega]
    push_cast
    ring
  · simp only [decVA, declining, ↓reduceIte, show t = 10 by omega]
    norm_num

theorem decVB_rec (t : ℕ) (ht : t ≤ 10) : decVB t = declining.duo 1 t + decVB (t + 1) := by
  rcases Nat.lt_or_ge t 10 with h | h
  · simp only [decVB, declining, ↓reduceIte, ht, show t + 1 ≤ 10 by omega, one_ne_zero]
    push_cast
    ring
  · simp only [decVB, declining, ↓reduceIte, show t = 10 by omega, one_ne_zero]
    norm_num

theorem decVA_late (t : ℕ) (ht : 10 < t) : decVA t = 0 := by
  simp [decVA, show ¬ t ≤ 10 by omega]

theorem decVB_late (t : ℕ) (ht : 10 < t) : decVB t = decM 1 t := by
  simp [decVB, decM, show ¬ t ≤ 10 by omega]

theorem decVA_pos (t : ℕ) (ht : t ≤ 10) : 0 < decVA t := by
  have : (t : ℝ) ≤ 10 := by exact_mod_cast ht
  simp only [decVA, ht, ↓reduceIte]
  have : 0 < (11 - (t : ℝ)) := by linarith
  positivity

theorem decVB_pos (t : ℕ) (ht : t ≤ 10) : 0 < decVB t := by
  simp only [decVB, ht, ↓reduceIte]
  positivity

theorem decM1_pos (t : ℕ) (ht : t ≤ 25) : 0 < decM 1 t := by
  have : (t : ℝ) ≤ 25 := by exact_mod_cast ht
  simp only [decM, one_ne_zero, ↓reduceIte, ht]
  have : 0 < (26 - (t : ℝ)) := by linarith
  positivity

theorem attr_none (i : Fin 2) (t : ℕ) :
    attritionSPNE.stay i t none = decide (t ≤ if i = 0 then 10 else 25) := rfl

theorem attr_some (i : Fin 2) (t u : ℕ) :
    attritionSPNE.stay i t (some u) = decide (t ≤ decL i) := rfl

/-- The values at a date `t` when both firms use the SPNE moves at `t` and the continuation
values are the SPNE values. -/
theorem dec_jv_step (s : AttritionProfile) (t : ℕ) (h0 : s.stay 0 t none = decide (t ≤ 10))
    (h1 : s.stay 1 t none = decide (t ≤ 25))
    (hA : t ≤ 10 → declining.jointValue s 0 (t + 1) = (decVA (t + 1) : WithBot ℝ))
    (hB : t ≤ 10 → declining.jointValue s 1 (t + 1) = (decVB (t + 1) : WithBot ℝ))
    (hm : 10 < t → t ≤ 25 → declining.monoValue s 1 (t + 1) t = (decM 1 (t + 1) : WithBot ℝ)) :
    declining.jointValue s 0 t = (decVA t : WithBot ℝ) ∧
      declining.jointValue s 1 t = (decVB t : WithBot ℝ) := by
  rw [declining.jointValue_eq, declining.jointValue_eq]
  unfold AttritionGame.stayValue
  have o0 : BargainingGame.other 0 = 1 := rfl
  have o1 : BargainingGame.other 1 = 0 := rfl
  rw [o0, o1, h0, h1]
  by_cases ht10 : t ≤ 10
  · simp only [ht10, show t ≤ 25 by omega, decide_true, ↓reduceIte]
    rw [hA ht10, hB ht10, ← WithBot.coe_add, ← WithBot.coe_add, decVA_rec t ht10,
      decVB_rec t ht10]
    exact ⟨rfl, rfl⟩
  · by_cases ht25 : t ≤ 25
    · simp only [ht10, ht25, decide_true, decide_false, ↓reduceIte, Bool.false_eq_true]
      rw [hm (by omega) ht25, ← WithBot.coe_add, decVA_late t (by omega),
        decVB_late t (by omega), decM_rec 1 t (by simpa [decL] using ht25)]
      exact ⟨rfl, rfl⟩
    · simp only [ht10, ht25, decide_false, ↓reduceIte, Bool.false_eq_true]
      rw [decVA_late t (by omega), decVB_late t (by omega), decM_late 1 t
        (by simp [decL]; omega)]
      exact ⟨rfl, rfl⟩

theorem decDuo_neg (i : Fin 2) (t : ℕ) (ht : 11 ≤ t) : declining.duo i t < 0 := by
  have : (11 : ℝ) ≤ t := by exact_mod_cast ht
  fin_cases i
  · simp only [declining, Fin.zero_eta, Fin.isValue, ↓reduceIte]
    linarith
  · simp only [declining, Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte]
    linarith

theorem decB_mid (t : ℕ) (h11 : 11 ≤ t) (h20 : t ≤ 20) :
    0 < declining.duo 1 t + decVB (t + 1) := by
  rw [decVB_late _ (by omega)]
  have a : (11 : ℝ) ≤ t := by exact_mod_cast h11
  have b : (t : ℝ) ≤ 20 := by exact_mod_cast h20
  simp only [declining, decM, Fin.isValue, one_ne_zero, ↓reduceIte, show t + 1 ≤ 25 by omega]
  push_cast
  nlinarith

/-- The monopoly values in the SPNE profile. -/
theorem attritionSPNE_mono (i : Fin 2) (t u : ℕ) :
    declining.monoValue attritionSPNE i t u = (decM i t : WithBot ℝ) :=
  declining.monoValue_cutoff attritionSPNE i u (decL i) (decM i) (fun _ => rfl) (decM_rec i)
    (decM_late i) t

/-- The values in the SPNE profile at the nodes where both firms are in. -/
theorem attritionSPNE_values (t : ℕ) :
    declining.jointValue attritionSPNE 0 t = (decVA t : WithBot ℝ) ∧
      declining.jointValue attritionSPNE 1 t = (decVB t : WithBot ℝ) := by
  have h0 : ∀ t, attritionSPNE.stay 0 t none = decide (t ≤ 10) := fun t => by simp [attr_none]
  have h1 : ∀ t, attritionSPNE.stay 1 t none = decide (t ≤ 25) := fun t => by simp [attr_none]
  have key : ∀ d t, t + d = 26 → declining.jointValue attritionSPNE 0 t = (decVA t : WithBot ℝ) ∧
      declining.jointValue attritionSPNE 1 t = (decVB t : WithBot ℝ) := by
    intro d
    induction d with
    | zero =>
      intro t ht
      exact dec_jv_step _ t (h0 t) (h1 t) (fun h => by omega) (fun h => by omega)
        (fun _ h => by omega)
    | succ d ih =>
      intro t ht
      exact dec_jv_step _ t (h0 t) (h1 t) (fun _ => (ih (t + 1) (by omega)).1)
        (fun _ => (ih (t + 1) (by omega)).2) (fun _ _ => attritionSPNE_mono 1 (t + 1) t)
  by_cases ht : t ≤ 26
  · exact key (26 - t) t (by omega)
  · exact dec_jv_step _ t (h0 t) (h1 t) (fun h => by omega) (fun h => by omega)
      (fun _ h => by omega)

/-- **Exercise 9.B.11: the SPNE profile is an SPNE** (MWG, p. 303). -/
theorem attritionSPNE_isSPNE : declining.IsSPNE attritionSPNE := by
  intro i s' hs' t
  refine ⟨?_, fun u _ => ?_⟩
  · rcases Fin.exists_fin_two.1 ⟨i, rfl⟩ with rfl | rfl
    · rw [(attritionSPNE_values t).1]
      have ho : s'.stay 1 = attritionSPNE.stay 1 := hs'
      refine declining.jointValue_le s' 0 t decVA (fun r _ _ _ => ?_) (fun r _ _ hr => ?_)
        (fun r _ => ?_)
      · by_cases hr : r ≤ 10
        · rw [decVA_rec r hr]
        · rw [decVA_late r (by omega), decVA_late (r + 1) (by omega)]
          linarith [decDuo_neg 0 r (by omega)]
      · change s'.stay 1 r none = false at hr
        rw [ho, attr_none] at hr
        have hr26 : 25 < r := by simpa using hr
        have hle := declining.monoValue_le s' 0 (r + 1) r (decM 0) (decM_hrec 0)
          (decM_nonneg 0)
        refine (add_le_add le_rfl hle).trans ?_
        rw [← WithBot.coe_add, WithBot.coe_le_coe, decVA_late r (by omega),
          ← decM_late 0 r (by simp [decL]; omega)]
        exact decM_hrec 0 r
      · unfold decVA; split_ifs <;> positivity
    · rw [(attritionSPNE_values t).2]
      have ho : s'.stay 0 = attritionSPNE.stay 0 := hs'
      refine declining.jointValue_le s' 1 t decVB (fun r _ hr _ => ?_) (fun r _ _ hr => ?_)
        (fun r _ => ?_)
      · rw [ho, attr_none] at hr
        have hr10 : r ≤ 10 := by simpa using hr
        rw [decVB_rec r hr10]
      · change s'.stay 0 r none = false at hr
        rw [ho, attr_none] at hr
        have hr10 : 10 < r := by simpa using hr
        have hle := declining.monoValue_le s' 1 (r + 1) r (decM 1) (decM_hrec 1)
          (decM_nonneg 1)
        refine (add_le_add le_rfl hle).trans ?_
        rw [← WithBot.coe_add, WithBot.coe_le_coe, decVB_late r hr10]
        exact decM_hrec 1 r
      · unfold decVB; split_ifs <;> positivity
  · rw [attritionSPNE_mono]
    exact declining.monoValue_le s' i t u (decM i) (decM_hrec i) (decM_nonneg i)

/-- **Exercise 9.B.11: uniqueness** (MWG, p. 303). In every SPNE, while both firms are in, A
stays exactly at the dates `t ≤ 10` and B exactly at the dates `t ≤ 25`, and the payoffs from
date `t` are `decVA t` and `decVB t`. From date 26 on staying is dominated for both firms
(all profits are negative); backward induction over dates `25, …, 0` does the rest: at dates
21-25 staying is dominated for A, so B stays; at dates 11-20 staying is strictly better for B
whatever A does, so A exits; at dates `t ≤ 10` both strictly prefer to stay. -/
theorem exercise_9_B_11_unique {s : AttritionProfile} (hs : declining.IsSPNE s) (t : ℕ) :
    s.stay 0 t none = decide (t ≤ 10) ∧ s.stay 1 t none = decide (t ≤ 25) ∧
      declining.jointValue s 0 t = (decVA t : WithBot ℝ) ∧
      declining.jointValue s 1 t = (decVB t : WithBot ℝ) := by
  have hm : ∀ i t, declining.monoValue s i (t + 1) t = (decM i (t + 1) : WithBot ℝ) :=
    fun i t => (exercise_9_B_11_monopoly hs i t (t + 1) (Nat.lt_succ_self t)).2
  have o0 : BargainingGame.other 0 = 1 := rfl
  have o1 : BargainingGame.other 1 = 0 := rfl
  -- from date 26 on: both exit
  have hle0 : ∀ i r, 26 ≤ r → declining.jointValue s i r ≤ ((0 : ℝ) : WithBot ℝ) := by
    intro i r hr
    refine declining.jointValue_le s i r (fun _ => 0) (fun r' hr' _ _ => ?_)
      (fun r' hr' _ _ => ?_) (fun _ _ => le_rfl)
    · linarith [decDuo_neg i r' (by omega)]
    · have hle := declining.monoValue_le s i (r' + 1) r' (decM i) (decM_hrec i) (decM_nonneg i)
      refine (add_le_add le_rfl hle).trans ?_
      rw [← WithBot.coe_add, WithBot.coe_le_coe, ← decM_late i r' (by fin_cases i <;>
        simp [decL] <;> omega)]
      exact decM_hrec i r'
  have hlate : ∀ t, 26 ≤ t → s.stay 0 t none = decide (t ≤ 10) ∧
      s.stay 1 t none = decide (t ≤ 25) ∧
      declining.jointValue s 0 t = (decVA t : WithBot ℝ) ∧
      declining.jointValue s 1 t = (decVB t : WithBot ℝ) := by
    intro t ht
    have hex : ∀ i, s.stay i t none = false := by
      intro i
      refine declining.exit_of_neg hs ?_
      unfold AttritionGame.stayValue
      split_ifs
      · refine lt_of_le_of_lt (add_le_add le_rfl (hle0 i (t + 1) (by omega))) ?_
        rw [← WithBot.coe_add, ← WithBot.coe_zero, WithBot.coe_lt_coe]
        linarith [decDuo_neg i t (by omega)]
      · rw [hm, ← WithBot.coe_add, ← WithBot.coe_zero, WithBot.coe_lt_coe,
          decM_late i (t + 1) (by fin_cases i <;> simp [decL] <;> omega)]
        linarith [decMono_neg i t (by fin_cases i <;> simp [decL] <;> omega)]
    have e0 : s.stay 0 t none = decide (t ≤ 10) := by rw [hex 0]; simp; omega
    have e1 : s.stay 1 t none = decide (t ≤ 25) := by rw [hex 1]; simp; omega
    exact ⟨e0, e1, dec_jv_step s t e0 e1 (fun h => by omega) (fun h => by omega)
      (fun _ h => by omega)⟩
  -- dates `t ≤ 25`, by backward induction
  have step : ∀ t, t ≤ 25 → declining.jointValue s 0 (t + 1) = (decVA (t + 1) : WithBot ℝ) →
      declining.jointValue s 1 (t + 1) = (decVB (t + 1) : WithBot ℝ) →
      s.stay 0 t none = decide (t ≤ 10) ∧ s.stay 1 t none = decide (t ≤ 25) := by
    intro t ht hA hB
    have hS0 : declining.stayValue s 0 t = if s.stay 1 t none = true then
        ((declining.duo 0 t + decVA (t + 1) : ℝ) : WithBot ℝ)
        else ((declining.mono 0 t + decM 0 (t + 1) : ℝ) : WithBot ℝ) := by
      unfold AttritionGame.stayValue
      rw [o0, hA, hm, WithBot.coe_add, WithBot.coe_add]
    have hS1 : declining.stayValue s 1 t = if s.stay 0 t none = true then
        ((declining.duo 1 t + decVB (t + 1) : ℝ) : WithBot ℝ)
        else ((declining.mono 1 t + decM 1 (t + 1) : ℝ) : WithBot ℝ) := by
      unfold AttritionGame.stayValue
      rw [o1, hB, hm, WithBot.coe_add, WithBot.coe_add]
    have hBmono : 0 < declining.mono 1 t + decM 1 (t + 1) := by
      rw [← decM_rec 1 t (by simp [decL]; omega)]
      exact decM1_pos t ht
    by_cases h20 : 20 < t
    · -- dates 21-25: staying is dominated for A; then B stays
      have eA : s.stay 0 t none = false := by
        refine declining.exit_of_neg hs ?_
        rw [hS0, ← WithBot.coe_zero]
        split_ifs
        · rw [WithBot.coe_lt_coe, decVA_late (t + 1) (by omega)]
          linarith [decDuo_neg 0 t (by omega)]
        · rw [WithBot.coe_lt_coe, decM_late 0 (t + 1) (by simp [decL]; omega)]
          linarith [decMono_neg 0 t (by simp [decL]; omega)]
      have eB : s.stay 1 t none = true := by
        refine declining.stay_of_pos hs ?_
        rw [hS1, eA, ← WithBot.coe_zero]
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact WithBot.coe_lt_coe.2 hBmono
      rw [eA, eB]
      exact ⟨by simp; omega, by simp; omega⟩
    · -- dates up to 20: staying is strictly better for B whatever A does
      have eB : s.stay 1 t none = true := by
        refine declining.stay_of_pos hs ?_
        rw [hS1, ← WithBot.coe_zero]
        split_ifs
        · refine WithBot.coe_lt_coe.2 ?_
          by_cases h10 : t ≤ 10
          · rw [← decVB_rec t h10]; exact decVB_pos t h10
          · exact decB_mid t (by omega) (by omega)
        · exact WithBot.coe_lt_coe.2 hBmono
      by_cases h10 : t ≤ 10
      · have eA : s.stay 0 t none = true := by
          refine declining.stay_of_pos hs ?_
          rw [hS0, eB, ← WithBot.coe_zero]
          simp only [↓reduceIte]
          rw [WithBot.coe_lt_coe, ← decVA_rec t h10]
          exact decVA_pos t h10
        rw [eA, eB]
        exact ⟨by simp [h10], by simp; omega⟩
      · have eA : s.stay 0 t none = false := by
          refine declining.exit_of_neg hs ?_
          rw [hS0, eB, ← WithBot.coe_zero]
          simp only [↓reduceIte]
          rw [WithBot.coe_lt_coe, decVA_late (t + 1) (by omega)]
          linarith [decDuo_neg 0 t (by omega)]
        rw [eA, eB]
        exact ⟨by simp; omega, by simp; omega⟩
  have key : ∀ d t, t + d = 26 → s.stay 0 t none = decide (t ≤ 10) ∧
      s.stay 1 t none = decide (t ≤ 25) ∧
      declining.jointValue s 0 t = (decVA t : WithBot ℝ) ∧
      declining.jointValue s 1 t = (decVB t : WithBot ℝ) := by
    intro d
    induction d with
    | zero => intro t ht; exact hlate t (by omega)
    | succ d ih =>
      intro t ht
      have hn := ih (t + 1) (by omega)
      have hst := step t (by omega) hn.2.2.1 hn.2.2.2
      exact ⟨hst.1, hst.2, dec_jv_step s t hst.1 hst.2 (fun _ => hn.2.2.1)
        (fun _ => hn.2.2.2) (fun _ _ => hm 1 t)⟩
  by_cases ht : t ≤ 26
  · exact key (26 - t) t (by omega)
  · exact hlate t (by omega)

/-- **Exercise 9.B.11** (MWG, p. 303). The declining-market war of attrition has a unique SPNE,
`attritionSPNE`: while both firms are in, A stays exactly in periods `t ≤ 10` and B exactly in
periods `t ≤ 25`; a firm alone stays exactly while its monopoly profit is positive (A for
`t ≤ 20`, B for `t ≤ 25`), whatever the rival's exit date. The SPNE outcome: both firms stay in
periods `0, …, 10`, A exits at the start of period 11, and B is a monopolist in periods
`11, …, 25` and exits at the start of period 26. Payoffs: `605` for A and `285.5` for B. -/
theorem exercise_9_B_11 :
    declining.IsSPNE attritionSPNE ∧
      ∀ s, declining.IsSPNE s →
        (∀ i t e, (∀ u, e = some u → u < t) → s.stay i t e = attritionSPNE.stay i t e) ∧
        declining.jointValue s 0 0 = ((605 : ℝ) : WithBot ℝ) ∧
        declining.jointValue s 1 0 = ((571 / 2 : ℝ) : WithBot ℝ) := by
  refine ⟨attritionSPNE_isSPNE, fun s hs => ⟨fun i t e he => ?_, ?_, ?_⟩⟩
  · rcases e with _ | u
    · have := exercise_9_B_11_unique hs t
      rcases Fin.exists_fin_two.1 ⟨i, rfl⟩ with rfl | rfl
      · rw [this.1, attr_none]; simp
      · rw [this.2.1, attr_none]; simp
    · rw [(exercise_9_B_11_monopoly hs i u t (he u rfl)).1, attr_some]
  · rw [(exercise_9_B_11_unique hs 0).2.2.1]
    norm_num [decVA]
  · rw [(exercise_9_B_11_unique hs 0).2.2.2]
    norm_num [decVB]

end MWG.DynamicGames
