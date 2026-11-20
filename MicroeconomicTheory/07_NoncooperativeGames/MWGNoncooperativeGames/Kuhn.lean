/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGNoncooperativeGames.Mixed
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.BigOperators.Field

/-!
# Kuhn's theorem: mixed and behaviour strategies under perfect recall

MWG, Section 7.E, p. 233 (the result of Kuhn (1953) cited there) and Exercise 7.E.1.

Two randomized strategies of player `i`, a mixed strategy `σ` and a behaviour strategy `β`,
are **realization equivalent** (`RealizationEquivalent`) if they generate the same probability
distribution over the terminal nodes whatever the other players (and nature) do. The rivals'
play is given as arbitrary move probabilities at their information sets, which covers pure and
behaviour strategies; `realizationEquivalent_mixed_rivals` covers mixed strategies of the
rivals.

* `kuhn_behavior_to_mixed`: if no information set is crossed twice on a path (condition (i)
  of perfect recall), every behaviour strategy has a realization-equivalent mixed strategy,
  namely `mixedOfBehavior β`, `σ(s) = ∏_{H ∈ ℋ_i} β(H, s(H))`.
* `kuhn_mixed_to_behavior`: if player `i` satisfies condition (ii) of perfect recall, every
  mixed strategy has a realization-equivalent behaviour strategy, namely `behaviorOfMixed σ`,
  the conditional probability of each action given that `σ` is consistent with reaching the
  information set.
* `kuhn_theorem`: both directions in games of perfect recall (the statement on p. 233).

Both constructions are proved node by node: `mixedWeight σ x = weight β x` for every node `x`
(`mixedWeight_mixedOfBehavior`, `mixedWeight_eq_weight_behaviorOfMixed`), and the
factorisation of `MWGNoncooperativeGames.Mixed` turns this into realization equivalence.
-/

namespace MWG.NoncooperativeGames

namespace ExtensiveForm

variable {I A H : Type*} (G : ExtensiveForm I A H)

/-- A chosen decision node in information set `k`. -/
noncomputable def rep (k : H) : List A := (G.info_surj k).choose

theorem rep_isDecision (k : H) : G.IsDecision (G.rep k) :=
  ⟨(G.info_surj k).choose_spec.1, (G.info_surj k).choose_spec.2.1⟩

theorem info_rep (k : H) : G.info (G.rep k) = k := (G.info_surj k).choose_spec.2.2

variable [DecidableEq I]

theorem weight_cons_of_ne (j : Option I) (f : H → A → ℝ) {a : A} {x : List A}
    (h : G.player (G.info x) ≠ j) : G.weight j f (a :: x) = G.weight j f x := by
  simp [weight_cons, h]

theorem weight_cons_of_eq (j : Option I) (f : H → A → ℝ) {a : A} {x : List A}
    (h : G.player (G.info x) = j) : G.weight j f (a :: x) = G.weight j f x * f (G.info x) a := by
  simp [weight_cons, h]

variable [DecidableEq A]

/-- The weight of a pure strategy is nonnegative. -/
theorem weight_pureBeh_nonneg {i : I} (s : G.PureStrategy i) (x : List A) :
    0 ≤ G.weight (some i) (G.pureBeh s) x := by
  by_cases h : G.Consistent s x
  · rw [G.weight_pureBeh_of_consistent s h]; norm_num
  · rw [G.weight_pureBeh_of_not_consistent s h]

omit [DecidableEq I] [DecidableEq A] in
/-- Under condition (ii) of perfect recall, a pure strategy of `i` is consistent with the path
to `x` iff it is consistent with the path to any `x'` in the same information set of `i`. -/
theorem consistent_iff_of_recall {i : I} (hR : G.RecallFor i) {x x' : List A}
    (hx : G.IsDecision x) (hx' : G.IsDecision x') (hown : G.player (G.info x) = some i)
    (he : G.info x = G.info x') (s : G.PureStrategy i) :
    G.Consistent s x ↔ G.Consistent s x' := by
  have key : ∀ x x', G.IsDecision x → G.IsDecision x' → G.player (G.info x) = some i →
      G.info x = G.info x' → G.Consistent s x' → G.Consistent s x := by
    intro x x' hx hx' hown he hc y b hy hb
    have hown' : G.player (G.info x') = some i := he ▸ hown
    obtain ⟨y', -, hb', hyy⟩ := hR x hx.1 x' hx'.1 hx.2 hx'.2 hown he y
      (G.mem_of_suffix ((List.suffix_cons b y).trans hb) hx.1) b hb hy
    have hy' : G.player (G.info y') = some i := hyy ▸ hy
    have h1 := hc y' b hy' hb'
    have e : (⟨G.info y', hy'⟩ : G.InfoSetOf i) = ⟨G.info y, hy⟩ := Subtype.ext hyy
    rw [e] at h1
    exact h1
  exact ⟨key x' x hx' hx (he ▸ hown) he.symm, key x x' hx hx' hown he⟩

/-- Under condition (ii), pure strategies have equal weights at nodes of one information set
of player `i`. -/
theorem weight_pureBeh_eq_of_recall {i : I} (hR : G.RecallFor i) {x x' : List A}
    (hx : G.IsDecision x) (hx' : G.IsDecision x') (hown : G.player (G.info x) = some i)
    (he : G.info x = G.info x') (s : G.PureStrategy i) :
    G.weight (some i) (G.pureBeh s) x = G.weight (some i) (G.pureBeh s) x' := by
  by_cases hc : G.Consistent s x
  · rw [G.weight_pureBeh_of_consistent s hc, G.weight_pureBeh_of_consistent s
      ((G.consistent_iff_of_recall hR hx hx' hown he s).1 hc)]
  · rw [G.weight_pureBeh_of_not_consistent s hc, G.weight_pureBeh_of_not_consistent s
      (fun h => hc ((G.consistent_iff_of_recall hR hx hx' hown he s).2 h))]

variable [Fintype A] [Fintype H] [DecidableEq H]

omit [Fintype A] in
theorem mixedWeight_nil {i : I} {σ : G.PureStrategy i → ℝ} (hσ : ∑ s, σ s = 1) :
    G.mixedWeight σ [] = 1 := by
  simp [mixedWeight, hσ]

omit [Fintype A] in
theorem mixedWeight_cons_of_ne {i : I} (σ : G.PureStrategy i → ℝ) {a : A} {x : List A}
    (h : G.player (G.info x) ≠ some i) : G.mixedWeight σ (a :: x) = G.mixedWeight σ x := by
  simp only [mixedWeight, G.weight_cons_of_ne _ _ h]

omit [Fintype A] in
theorem mixedWeight_cons_of_eq {i : I} (σ : G.PureStrategy i → ℝ) {a : A} {x : List A}
    (h : G.player (G.info x) = some i) :
    G.mixedWeight σ (a :: x) = ∑ s, σ s * G.weight (some i) (G.pureBeh s) x *
      (if (s ⟨G.info x, h⟩).1 = a then 1 else 0) := by
  simp only [mixedWeight, G.weight_cons_of_eq _ _ h, G.pureBeh_of_mem _ h, mul_assoc]

omit [Fintype A] in
theorem mixedWeight_nonneg {i : I} {σ : G.PureStrategy i → ℝ} (hσ : ∀ s, 0 ≤ σ s)
    (x : List A) : 0 ≤ G.mixedWeight σ x :=
  Finset.sum_nonneg fun s _ => mul_nonneg (hσ s) (G.weight_pureBeh_nonneg s x)

omit [Fintype A] in
theorem mixedWeight_cons_le {i : I} {σ : G.PureStrategy i → ℝ} (hσ : ∀ s, 0 ≤ σ s)
    (a : A) (x : List A) : G.mixedWeight σ (a :: x) ≤ G.mixedWeight σ x := by
  by_cases h : G.player (G.info x) = some i
  · rw [G.mixedWeight_cons_of_eq σ h, mixedWeight]
    refine Finset.sum_le_sum fun s _ => ?_
    have h0 := mul_nonneg (hσ s) (G.weight_pureBeh_nonneg s x)
    split_ifs <;> linarith
  · rw [G.mixedWeight_cons_of_ne σ h]

omit [Fintype A] in
theorem mixedWeight_cons_eq_zero {i : I} {σ : G.PureStrategy i → ℝ} (hσ : ∀ s, 0 ≤ σ s)
    {a : A} {x : List A} (h0 : G.mixedWeight σ x = 0) : G.mixedWeight σ (a :: x) = 0 :=
  le_antisymm (h0 ▸ G.mixedWeight_cons_le hσ a x) (G.mixedWeight_nonneg hσ _)

omit [Fintype A] in
theorem sum_mixedWeight_cons {i : I} (σ : G.PureStrategy i → ℝ) {x : List A}
    (h : G.player (G.info x) = some i) :
    ∑ a ∈ G.avail (G.info x), G.mixedWeight σ (a :: x) = G.mixedWeight σ x := by
  simp_rw [G.mixedWeight_cons_of_eq σ h]
  rw [Finset.sum_comm, mixedWeight]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← Finset.mul_sum, Finset.sum_ite_eq]
  simp [(s ⟨G.info x, h⟩).2]

omit [Fintype A] in
theorem mixedWeight_cons_of_not_mem {i : I} (σ : G.PureStrategy i → ℝ) {a : A} {x : List A}
    (h : G.player (G.info x) = some i) (ha : a ∉ G.avail (G.info x)) :
    G.mixedWeight σ (a :: x) = 0 := by
  rw [G.mixedWeight_cons_of_eq σ h]
  refine Finset.sum_eq_zero fun s _ => ?_
  have : (s ⟨G.info x, h⟩).1 ≠ a := by
    rintro rfl
    exact ha (s ⟨G.info x, h⟩).2
  simp [this]

omit [Fintype A] in
/-- Under condition (ii), mixed weights agree at nodes of one information set of `i`, before
and after any action. -/
theorem mixedWeight_eq_of_recall {i : I} (hR : G.RecallFor i) (σ : G.PureStrategy i → ℝ)
    {x x' : List A} (hx : G.IsDecision x) (hx' : G.IsDecision x')
    (hown : G.player (G.info x) = some i) (he : G.info x = G.info x') (a : A) :
    G.mixedWeight σ x = G.mixedWeight σ x' ∧
      G.mixedWeight σ (a :: x) = G.mixedWeight σ (a :: x') := by
  have hown' : G.player (G.info x') = some i := he ▸ hown
  have hw := G.weight_pureBeh_eq_of_recall hR hx hx' hown he
  refine ⟨Finset.sum_congr rfl fun s _ => by rw [hw s], ?_⟩
  rw [G.mixedWeight_cons_of_eq σ hown, G.mixedWeight_cons_of_eq σ hown']
  have e : (⟨G.info x, hown⟩ : G.InfoSetOf i) = ⟨G.info x', hown'⟩ := Subtype.ext he
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [hw s, e]

/-- The behaviour strategy induced by a mixed strategy `σ`: at information set `k`, the
probability of action `a` conditional on `σ` being consistent with reaching `k` (uniform on
`C(k)` when `σ` never reaches `k`). -/
noncomputable def behaviorOfMixed {i : I} (σ : G.PureStrategy i → ℝ) : H → A → ℝ :=
  fun k a => if G.mixedWeight σ (G.rep k) = 0 then
      (if a ∈ G.avail k then ((G.avail k).card : ℝ)⁻¹ else 0)
    else G.mixedWeight σ (a :: G.rep k) / G.mixedWeight σ (G.rep k)

omit [Fintype A] in
/-- The conditional probabilities of a mixed strategy form a behaviour strategy. -/
theorem isBehaviorStrategy_behaviorOfMixed {i : I} {σ : G.PureStrategy i → ℝ}
    (hσ : IsMixedStrategy σ) : G.IsBehaviorStrategy i (G.behaviorOfMixed σ) := by
  intro k hk
  have hr := G.info_rep k
  have hown : G.player (G.info (G.rep k)) = some i := by rw [hr]; exact hk
  refine ⟨fun a => ?_, fun a ha => ?_, ?_⟩
  · unfold behaviorOfMixed
    split_ifs
    · positivity
    · norm_num
    · exact div_nonneg (G.mixedWeight_nonneg hσ.1 _) (G.mixedWeight_nonneg hσ.1 _)
  · unfold behaviorOfMixed
    have ha' : a ∉ G.avail (G.info (G.rep k)) := by rw [hr]; exact ha
    split_ifs
    · rfl
    · rw [G.mixedWeight_cons_of_not_mem σ hown ha', zero_div]
  · unfold behaviorOfMixed
    split_ifs with h0
    · rw [Finset.sum_const, nsmul_eq_mul]
      have : ((G.avail k).card : ℝ) ≠ 0 := by
        exact_mod_cast (G.avail_nonempty k).card_pos.ne'
      field_simp
    · have hs := G.sum_mixedWeight_cons σ hown
      rw [hr] at hs
      rw [← Finset.sum_div, hs, div_self h0]

omit [Fintype A] in
/-- **Kuhn's theorem, mixed to behaviour** (MWG, p. 233), node by node: under condition (ii) of
perfect recall for player `i`, `behaviorOfMixed σ` reaches every node with the same
`i`-weight as `σ`. -/
theorem mixedWeight_eq_weight_behaviorOfMixed {i : I} (hR : G.RecallFor i)
    {σ : G.PureStrategy i → ℝ} (hσ : IsMixedStrategy σ) :
    ∀ x ∈ G.nodes, G.mixedWeight σ x = G.weight (some i) (G.behaviorOfMixed σ) x := by
  intro x
  induction x with
  | nil => intro _; rw [G.mixedWeight_nil hσ.2]; rfl
  | cons a x ih =>
    intro hax
    have hx := G.mem_of_cons_mem hax
    by_cases hown : G.player (G.info x) = some i
    · rw [G.weight_cons_of_eq _ _ hown, ← ih hx]
      have hxd : G.IsDecision x := G.isDecision_of_cons_mem hax
      obtain ⟨e1, e2⟩ := G.mixedWeight_eq_of_recall hR σ hxd (G.rep_isDecision (G.info x))
        hown (G.info_rep _).symm a
      rw [e1, e2]
      by_cases h0 : G.mixedWeight σ (G.rep (G.info x)) = 0
      · rw [h0, zero_mul]
        exact G.mixedWeight_cons_eq_zero hσ.1 h0
      · have hb : G.behaviorOfMixed σ (G.info x) a =
            G.mixedWeight σ (a :: G.rep (G.info x)) / G.mixedWeight σ (G.rep (G.info x)) := by
          simp [behaviorOfMixed, h0]
        rw [hb]
        field_simp
    · rw [G.mixedWeight_cons_of_ne σ hown, G.weight_cons_of_ne _ _ hown]
      exact ih hx

/-- The mixed strategy induced by a behaviour strategy `β`: pure strategies drawn by
independent randomizations at the information sets, `σ(s) = ∏_{H ∈ ℋ_i} β(H, s(H))`. -/
noncomputable def mixedOfBehavior {i : I} (β : H → A → ℝ) : G.PureStrategy i → ℝ :=
  fun s => ∏ k, β k.1 (s k).1

omit [DecidableEq A] [Fintype A] in
/-- The product of a behaviour strategy over the information sets is a mixed strategy. -/
theorem isMixedStrategy_mixedOfBehavior {i : I} {β : H → A → ℝ}
    (hβ : G.IsBehaviorStrategy i β) : IsMixedStrategy (G.mixedOfBehavior (i := i) β) := by
  refine ⟨fun s => Finset.prod_nonneg fun k _ => (hβ k.1 k.2).1 _, ?_⟩
  have h := Fintype.prod_sum
    (fun (k : G.InfoSetOf i) (b : {a // a ∈ G.avail k.1}) => β k.1 b.1)
  unfold mixedOfBehavior
  rw [← h]
  refine Finset.prod_eq_one fun k _ => ?_
  rw [Finset.sum_coe_sort (G.avail k.1) (β k.1)]
  exact (hβ k.1 k.2).2.2

/-- The path to `x` allows action `b` at player `i`'s information set `k`: whenever the path
crosses `k`, it takes `b` there. -/
def PathAllows {i : I} (x : List A) (k : G.InfoSetOf i) (b : A) : Prop :=
  ∀ y a, a :: y <:+ x → G.info y = k.1 → b = a

open Classical in
/-- The indicator of `PathAllows`. -/
noncomputable def pathFactor {i : I} (x : List A) (k : G.InfoSetOf i) (b : A) : ℝ :=
  if G.PathAllows x k b then 1 else 0

omit [DecidableEq I] [DecidableEq A] [Fintype A] [Fintype H] [DecidableEq H] in
theorem pathFactor_of {i : I} {x : List A} {k : G.InfoSetOf i} {b : A}
    (h : G.PathAllows x k b) : G.pathFactor x k b = 1 := by
  unfold pathFactor
  split_ifs
  rfl

omit [DecidableEq I] [DecidableEq A] [Fintype A] [Fintype H] [DecidableEq H] in
theorem pathFactor_of_not {i : I} {x : List A} {k : G.InfoSetOf i} {b : A}
    (h : ¬ G.PathAllows x k b) : G.pathFactor x k b = 0 := by
  unfold pathFactor
  split_ifs
  rfl

omit [Fintype A] [Fintype H] [DecidableEq H] [DecidableEq I] [DecidableEq A] in
theorem consistent_iff_pathAllows {i : I} (s : G.PureStrategy i) (x : List A) :
    G.Consistent s x ↔ ∀ k, G.PathAllows x k (s k).1 := by
  constructor
  · intro h k y a hya hyk
    have hy : G.player (G.info y) = some i := hyk ▸ k.2
    have h1 := h y a hy hya
    have e : (⟨G.info y, hy⟩ : G.InfoSetOf i) = k := Subtype.ext hyk
    rw [e] at h1
    exact h1
  · intro h y a hy hya
    exact h ⟨G.info y, hy⟩ y a hya rfl

omit [Fintype A] [DecidableEq H] in
/-- The weight of a pure strategy factorises over the information sets. -/
theorem weight_pureBeh_eq_prod {i : I} (s : G.PureStrategy i) (x : List A) :
    G.weight (some i) (G.pureBeh s) x = ∏ k, G.pathFactor x k (s k).1 := by
  by_cases hc : G.Consistent s x
  · rw [G.weight_pureBeh_of_consistent s hc]
    exact (Finset.prod_eq_one fun k _ =>
      G.pathFactor_of ((G.consistent_iff_pathAllows s x).1 hc k)).symm
  · rw [G.weight_pureBeh_of_not_consistent s hc]
    rw [G.consistent_iff_pathAllows] at hc
    push Not at hc
    obtain ⟨k, hk⟩ := hc
    exact (Finset.prod_eq_zero (Finset.mem_univ k) (G.pathFactor_of_not hk)).symm

omit [DecidableEq I] [DecidableEq A] [Fintype A] [Fintype H] [DecidableEq H] in
theorem pathAllows_nil {i : I} (k : G.InfoSetOf i) (b : A) : G.PathAllows [] k b := by
  intro y a h
  have := h.length_le
  simp at this

omit [DecidableEq I] [DecidableEq A] [Fintype A] [Fintype H] [DecidableEq H] in
theorem pathAllows_cons {i : I} (a : A) (x : List A) (k : G.InfoSetOf i) (b : A) :
    G.PathAllows (a :: x) k b ↔ (G.info x = k.1 → b = a) ∧ G.PathAllows x k b := by
  constructor
  · intro h
    exact ⟨fun he => h x a (List.suffix_refl _) he,
      fun y c hy he => h y c (hy.trans (List.suffix_cons a x)) he⟩
  · rintro ⟨h1, h2⟩ y c hy he
    rcases List.suffix_cons_iff.1 hy with heq | hy'
    · simp only [List.cons.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      exact h1 he
    · exact h2 y c hy' he

omit [DecidableEq I] [DecidableEq A] [Fintype A] [Fintype H] [DecidableEq H] in
theorem pathFactor_cons_of_ne {i : I} {a : A} {x : List A} {k : G.InfoSetOf i} {b : A}
    (hne : G.info x ≠ k.1) : G.pathFactor (a :: x) k b = G.pathFactor x k b := by
  have h : G.PathAllows (a :: x) k b ↔ G.PathAllows x k b := by
    rw [G.pathAllows_cons]
    simp [hne]
  by_cases hp : G.PathAllows x k b
  · rw [G.pathFactor_of hp, G.pathFactor_of (h.2 hp)]
  · rw [G.pathFactor_of_not hp, G.pathFactor_of_not (fun h' => hp (h.1 h'))]

omit [Fintype A] in
/-- **Kuhn's theorem, behaviour to mixed** (MWG, p. 233), node by node: if no information set
is crossed twice on a path, the product mixed strategy `mixedOfBehavior β` reaches every node
with the same `i`-weight as `β`. -/
theorem mixedWeight_mixedOfBehavior (hNA : G.NoAbsentMindedness) {i : I} {β : H → A → ℝ}
    (hβ : G.IsBehaviorStrategy i β) :
    ∀ x ∈ G.nodes, G.mixedWeight (G.mixedOfBehavior (i := i) β) x = G.weight (some i) β x := by
  have hprod : ∀ x, G.mixedWeight (G.mixedOfBehavior (i := i) β) x =
      ∏ k : G.InfoSetOf i, ∑ b ∈ G.avail k.1, β k.1 b * G.pathFactor x k b := by
    intro x
    have h := Fintype.prod_sum (fun (k : G.InfoSetOf i) (b : {a // a ∈ G.avail k.1}) =>
      β k.1 b.1 * G.pathFactor x k b.1)
    have h2 : ∀ k : G.InfoSetOf i,
        ∑ b : {a // a ∈ G.avail k.1}, β k.1 b.1 * G.pathFactor x k b.1 =
          ∑ b ∈ G.avail k.1, β k.1 b * G.pathFactor x k b := fun k =>
      Finset.sum_coe_sort (G.avail k.1) (fun b => β k.1 b * G.pathFactor x k b)
    rw [Finset.prod_congr rfl fun k _ => (h2 k).symm, h, mixedWeight]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [mixedOfBehavior, G.weight_pureBeh_eq_prod, ← Finset.prod_mul_distrib]
  intro x
  rw [hprod]
  induction x with
  | nil =>
    intro _
    refine Finset.prod_eq_one fun k _ => ?_
    have h1 : ∀ b, G.pathFactor [] k b = 1 := fun b => G.pathFactor_of (G.pathAllows_nil k b)
    simp_rw [h1, mul_one]
    exact (hβ k.1 k.2).2.2
  | cons a x ih =>
    intro hax
    have hx := G.mem_of_cons_mem hax
    by_cases hown : G.player (G.info x) = some i
    · rw [G.weight_cons_of_eq _ _ hown, ← ih hx]
      have hxd : G.IsDecision x := G.isDecision_of_cons_mem hax
      have hav : a ∈ G.avail (G.info x) := G.mem_avail_of_cons_mem hax
      obtain ⟨k₀, hk₀⟩ : ∃ k₀ : G.InfoSetOf i, k₀ = ⟨G.info x, hown⟩ := ⟨_, rfl⟩
      have hk1 : k₀.1 = G.info x := by rw [hk₀]
      have hstep : ∀ k : G.InfoSetOf i,
          ∑ b ∈ G.avail k.1, β k.1 b * G.pathFactor (a :: x) k b =
            (∑ b ∈ G.avail k.1, β k.1 b * G.pathFactor x k b) *
              if k = k₀ then β (G.info x) a else 1 := by
        intro k
        by_cases hk : k = k₀
        · subst hk
          have hall : ∀ b, G.pathFactor x k b = 1 := by
            intro b
            refine G.pathFactor_of fun y c hyc hye => ?_
            exact absurd (hye.trans hk1) (G.info_ne_of_cons_suffix hNA hxd hyc)
          have hpf : ∀ b, G.pathFactor (a :: x) k b = if b = a then 1 else 0 := by
            intro b
            by_cases hb : b = a
            · rw [ite_eq_left_of_eq_true _ _ (eq_true hb)]
              refine G.pathFactor_of ((G.pathAllows_cons a x k b).2 ⟨fun _ => hb, ?_⟩)
              intro y c hyc hye
              exact absurd (hye.trans hk1) (G.info_ne_of_cons_suffix hNA hxd hyc)
            · rw [ite_eq_right_of_eq_false _ _ (eq_false hb)]
              exact G.pathFactor_of_not fun h =>
                hb (((G.pathAllows_cons a x k b).1 h).1 hk1.symm)
          rw [ite_eq_left_of_eq_true _ _ (eq_self k)]
          simp_rw [hpf, hall, mul_one, mul_ite, mul_one, mul_zero]
          rw [(hβ k.1 k.2).2.2, one_mul, Finset.sum_ite_eq']
          simp [hk1, hav]
        · have hne : G.info x ≠ k.1 := fun he => hk (by rw [hk₀]; exact Subtype.ext he.symm)
          rw [ite_eq_right_of_eq_false _ _ (eq_false hk), mul_one]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [G.pathFactor_cons_of_ne hne]
      rw [Finset.prod_congr rfl fun k _ => hstep k, Finset.prod_mul_distrib, Finset.prod_ite_eq']
      simp [hk₀]
    · rw [G.weight_cons_of_ne _ _ hown, ← ih hx]
      refine Finset.prod_congr rfl fun k _ => Finset.sum_congr rfl fun b _ => ?_
      have hne : G.info x ≠ k.1 := fun he => hown (he ▸ k.2)
      rw [G.pathFactor_cons_of_ne hne]

variable [Fintype I]

/-- **Section 7.E** (MWG, p. 233; Exercise 7.E.1(b)). A mixed strategy `σ` and a behaviour
strategy `β` of player `i` are realization equivalent: whatever the move probabilities `F j`
of the other players (pure or behaviour strategies), they induce the same probability of every
terminal node. -/
def RealizationEquivalent (i : I) (σ : G.PureStrategy i → ℝ) (β : H → A → ℝ) : Prop :=
  ∀ F : I → H → A → ℝ, ∀ z ∈ G.terminals,
    ∑ s, σ s * G.reach (G.assemble (Function.update F i (G.pureBeh s))) z =
      G.reach (G.assemble (Function.update F i β)) z

omit [DecidableEq A] [Fintype A] [Fintype H] [DecidableEq H] in
/-- Isolating player `i`'s weight in a reach probability. -/
theorem reach_update_factor (i : I) (F : I → H → A → ℝ) (g : H → A → ℝ) (x : List A) :
    G.reach (G.assemble (Function.update F i g)) x =
      G.weight (some i) g x * (G.weight none G.natureProb x *
        ∏ j, if j = i then 1 else G.weight (some j) (F j) x) := by
  rw [reach_assemble_factor]
  have : ∀ j, G.weight (some j) (Function.update F i g j) x =
      (if j = i then G.weight (some i) g x else 1) *
        (if j = i then 1 else G.weight (some j) (F j) x) := by
    intro j
    by_cases hj : j = i
    · subst hj
      simp
    · simp [hj]
  simp_rw [this]
  rw [Finset.prod_mul_distrib, Finset.prod_ite_eq']
  simp only [Finset.mem_univ, ite_true]
  ring

omit [Fintype I] in
/-- Equal `i`-weights at the terminal nodes give realization equivalence. -/
theorem realizationEquivalent_of_weight [Finite I] {i : I} {σ : G.PureStrategy i → ℝ}
    {β : H → A → ℝ} (h : ∀ z ∈ G.terminals, G.mixedWeight σ z = G.weight (some i) β z) :
    G.RealizationEquivalent i σ β := by
  have := Fintype.ofFinite I
  intro F z hz
  simp_rw [G.reach_update_factor i F]
  rw [← h z hz, mixedWeight, Finset.sum_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  ring

omit [Fintype I] in
/-- **Kuhn's theorem** (Kuhn 1953, cited on MWG p. 233; Exercise 7.E.1(b)). If no information
set is crossed twice on a path (perfect recall condition (i)), every behaviour strategy of
player `i` has a realization-equivalent mixed strategy. -/
theorem kuhn_behavior_to_mixed [Finite I] (hNA : G.NoAbsentMindedness) {i : I} {β : H → A → ℝ}
    (hβ : G.IsBehaviorStrategy i β) :
    ∃ σ : G.PureStrategy i → ℝ, IsMixedStrategy σ ∧ G.RealizationEquivalent i σ β :=
  ⟨G.mixedOfBehavior β, G.isMixedStrategy_mixedOfBehavior hβ,
    G.realizationEquivalent_of_weight fun z hz =>
      G.mixedWeight_mixedOfBehavior hNA hβ z ((G.mem_terminals).1 hz).1⟩

omit [Fintype I] in
/-- **Kuhn's theorem** (Kuhn 1953, cited on MWG p. 233; Exercise 7.E.1(c)). If player `i`
satisfies perfect recall condition (ii), every mixed strategy of player `i` has a
realization-equivalent behaviour strategy. -/
theorem kuhn_mixed_to_behavior [Finite I] {i : I} (hR : G.RecallFor i) {σ : G.PureStrategy i → ℝ}
    (hσ : IsMixedStrategy σ) :
    ∃ β : H → A → ℝ, G.IsBehaviorStrategy i β ∧ G.RealizationEquivalent i σ β :=
  ⟨G.behaviorOfMixed σ, G.isBehaviorStrategy_behaviorOfMixed hσ,
    G.realizationEquivalent_of_weight fun z hz =>
      G.mixedWeight_eq_weight_behaviorOfMixed hR hσ z ((G.mem_terminals).1 hz).1⟩

omit [Fintype I] in
/-- **Kuhn's theorem** (Kuhn 1953; MWG, Section 7.E, p. 233). In a game of perfect recall, for
any behaviour strategy of player `i` there is a realization-equivalent mixed strategy, and
for any mixed strategy there is a realization-equivalent behaviour strategy. -/
theorem kuhn_theorem [Finite I] (hPR : G.PerfectRecall) (i : I) :
    (∀ β : H → A → ℝ, G.IsBehaviorStrategy i β →
      ∃ σ : G.PureStrategy i → ℝ, IsMixedStrategy σ ∧ G.RealizationEquivalent i σ β) ∧
    (∀ σ : G.PureStrategy i → ℝ, IsMixedStrategy σ →
      ∃ β : H → A → ℝ, G.IsBehaviorStrategy i β ∧ G.RealizationEquivalent i σ β) :=
  ⟨fun _ hβ => G.kuhn_behavior_to_mixed hPR.1 hβ,
    fun _ hσ => G.kuhn_mixed_to_behavior (hPR.2 i) hσ⟩

/-- **Section 7.E** (MWG, p. 233). Realization equivalence also holds against MIXED strategies
of the rivals: if `σ i` and `β` give player `i` the same weights at the terminal nodes, then
the mixed profile `σ` induces the same distribution over terminal nodes as the profile where
`i` plays `β` and the rivals randomize independently according to `σ` (the `i`-th coordinate
of the drawn pure profile is then irrelevant). -/
theorem realizationEquivalent_mixed_rivals {i : I} (σ : (j : I) → G.PureStrategy j → ℝ)
    (hσi : ∑ s, σ i s = 1) {β : H → A → ℝ}
    (h : ∀ z ∈ G.terminals, G.mixedWeight (σ i) z = G.weight (some i) β z) :
    ∀ z ∈ G.terminals, G.mixedOutcome σ z =
      ∑ s : (j : I) → G.PureStrategy j, (∏ j, σ j (s j)) *
        G.reach (G.assemble (Function.update (fun j => G.pureBeh (s j)) i β)) z := by
  intro z hz
  rw [mixedOutcome_factor]
  let c : (j : I) → G.PureStrategy j → ℝ := fun j t =>
    if j = i then G.weight (some i) β z else G.weight (some j) (G.pureBeh t) z
  have hc : ∀ s : (j : I) → G.PureStrategy j,
      G.reach (G.assemble (Function.update (fun j => G.pureBeh (s j)) i β)) z =
        G.weight none G.natureProb z * ∏ j, c j (s j) := by
    intro s
    rw [reach_assemble_factor]
    congr 1
    refine Finset.prod_congr rfl fun j _ => ?_
    by_cases hj : j = i
    · subst hj
      simp [c]
    · simp [c, hj]
  simp_rw [hc]
  have : ∀ s : (j : I) → G.PureStrategy j, (∏ j, σ j (s j)) *
      (G.weight none G.natureProb z * ∏ j, c j (s j)) =
        G.weight none G.natureProb z * ∏ j, σ j (s j) * c j (s j) := by
    intro s
    rw [Finset.prod_mul_distrib]
    ring
  simp_rw [this]
  have hps := Fintype.prod_sum (fun j (t : G.PureStrategy j) => σ j t * c j t)
  rw [← Finset.mul_sum, ← hps]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  by_cases hj : j = i
  · subst hj
    simp only [c, ite_true]
    rw [← Finset.sum_mul, hσi, one_mul, h z hz]
  · simp only [c, hj, ite_false, mixedWeight]

/-- **Kuhn's theorem against mixed rivals** (MWG, p. 233). Under condition (ii) of perfect
recall for player `i`, replacing her mixed strategy `σ i` by `behaviorOfMixed (σ i)` leaves
the distribution over terminal nodes unchanged when the rivals play mixed strategies. -/
theorem kuhn_mixed_rivals {i : I} (hR : G.RecallFor i) (σ : (j : I) → G.PureStrategy j → ℝ)
    (hσ : IsMixedStrategy (σ i)) :
    ∀ z ∈ G.terminals, G.mixedOutcome σ z =
      ∑ s : (j : I) → G.PureStrategy j, (∏ j, σ j (s j)) *
        G.reach (G.assemble
          (Function.update (fun j => G.pureBeh (s j)) i (G.behaviorOfMixed (σ i)))) z :=
  G.realizationEquivalent_mixed_rivals σ hσ.2 fun z hz =>
    G.mixedWeight_eq_weight_behaviorOfMixed hR hσ z ((G.mem_terminals).1 hz).1

end ExtensiveForm

end MWG.NoncooperativeGames
