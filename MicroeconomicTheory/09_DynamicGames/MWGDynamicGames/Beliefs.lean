/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGDynamicGames.Zermelo
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Beliefs, sequential rationality, weak perfect Bayesian and sequential equilibrium

MWG, Section 9.C, pp. 282-292.

* `IsBeliefSystem` is **Definition 9.C.1**; `condPayoff G f μ k i` is
  `E[u_i | H, μ, σ] = ∑_{x ∈ H} μ(x) cont(x)`; `SeqRationalAt` / `SeqRational` are
  **Definition 9.C.2**; `probInfo` is `Prob(H | σ)` and `BayesConsistent` is condition (ii)
  of **Definition 9.C.3** (`IsWeakPBE`).
* `proposition_9_C_1` (**Proposition 9.C.1**, Exercise 9.C.1): in a game with perfect recall, a
  profile is a Nash equilibrium iff there is a system of beliefs, derived from the profile by
  Bayes' rule whenever possible, for which it is sequentially rational at every information
  set reached with positive probability. Hence every weak PBE is a Nash equilibrium
  (`isNashB_of_isWeakPBE`).
* `IsConsistent` and `IsSequentialEq` are **Definition 9.C.4**: beliefs are limits of the
  Bayes beliefs of totally mixed profiles converging to the strategies.
  `isWeakPBE_of_isSequentialEq`: every sequential equilibrium is a weak PBE (p. 290).
* `proposition_9_C_2` (**Proposition 9.C.2**): with perfect recall, the strategies of a
  sequential equilibrium form a subgame perfect Nash equilibrium.

Departures. The propositions are proved for games with perfect recall (MWG does not state the
hypothesis; Chapter 9 works with behaviour strategies, which presupposes it). The assessment
in `IsSequentialEq` includes that `μ` is a system of beliefs (automatic when nature's moves
have full support).
-/

namespace MWG.DynamicGames

open MWG.NoncooperativeGames MWG.NoncooperativeGames.ExtensiveForm Filter Topology

variable {I A H : Type*} (G : ExtensiveForm I A H) [DecidableEq A] [Fintype A] [DecidableEq I]
  [DecidableEq H]

/-- **Definition 9.C.1** (MWG, p. 283). A system of beliefs: a probability `μ(x) ∈ [0, 1]` for
each decision node, summing to one over every information set. -/
def IsBeliefSystem (μ : List A → ℝ) : Prop :=
  (∀ x, G.IsDecision x → 0 ≤ μ x ∧ μ x ≤ 1) ∧ ∀ k, ∑ x ∈ G.infoSet k, μ x = 1

/-- **Section 9.C** (MWG, p. 284). `E[u_i | H, μ, σ]`: player `i`'s expected continuation
payoff at information set `k` when the nodes of `k` have probabilities `μ` and play
continues according to the moves `f`. -/
def condPayoff (f : H → A → ℝ) (μ : List A → ℝ) (k : H) (i : I) : ℝ :=
  ∑ x ∈ G.infoSet k, μ x * cont G f x i

/-- **Definition 9.C.2** (MWG, p. 284). The profile `F` is sequentially rational at
information set `k` given beliefs `μ`: the player moving at `k` cannot raise
`E[u_i | k, μ, ·]` by switching to any other (behaviour) strategy. -/
def SeqRationalAt (F : I → H → A → ℝ) (μ : List A → ℝ) (k : H) : Prop :=
  ∀ i, G.player k = some i → ∀ g, G.IsBehaviorStrategy i g →
    condPayoff G (G.assemble (Function.update F i g)) μ k i ≤ condPayoff G (G.assemble F) μ k i

/-- **Definition 9.C.2** (MWG, p. 284). Sequential rationality at every information set. -/
def SeqRational (F : I → H → A → ℝ) (μ : List A → ℝ) : Prop := ∀ k, SeqRationalAt G F μ k

/-- **Section 9.C** (MWG, p. 284). `Prob(H | σ) = ∑_{x ∈ H} Prob(x | σ)`. -/
def probInfo (f : H → A → ℝ) (k : H) : ℝ := ∑ x ∈ G.infoSet k, G.reach f x

/-- **Definition 9.C.3(ii)** (MWG, p. 285). Beliefs are derived from the profile through Bayes'
rule whenever possible: `μ(x) = Prob(x | σ) / Prob(H | σ)` when `Prob(H | σ) > 0`. -/
def BayesConsistent (F : I → H → A → ℝ) (μ : List A → ℝ) : Prop :=
  ∀ k, 0 < probInfo G (G.assemble F) k →
    ∀ x ∈ G.infoSet k, μ x = G.reach (G.assemble F) x / probInfo G (G.assemble F) k

/-- **Definition 9.C.3** (MWG, p. 285). A weak perfect Bayesian equilibrium `(σ, μ)`. -/
def IsWeakPBE (F : I → H → A → ℝ) (μ : List A → ℝ) : Prop :=
  IsBehaviorProfile G F ∧ IsBeliefSystem G μ ∧ SeqRational G F μ ∧ BayesConsistent G F μ

omit [DecidableEq I] in
/-- Membership in an information set. -/
theorem mem_infoSet {k : H} {x : List A} : x ∈ G.infoSet k ↔ G.IsDecision x ∧ G.info x = k := by
  simp [infoSet, decisionNodes, IsDecision, and_assoc]

omit [DecidableEq A] [Fintype A] [DecidableEq I] [DecidableEq H] in
/-- Perfect recall condition (ii) for decision nodes. -/
theorem recall_pred {i : I} (hR : G.RecallFor i) {x x' y : List A} (hx : G.IsDecision x)
    (hx' : G.IsDecision x') (hi : G.player (G.info x) = some i) (he : G.info x = G.info x')
    {a : A} (hy : a :: y <:+ x) (hyi : G.player (G.info y) = some i) :
    ∃ y', G.IsDecision y' ∧ a :: y' <:+ x' ∧ G.info y' = G.info y := by
  obtain ⟨y', -, hy', hinfo⟩ := hR x hx.1 x' hx'.1 hx.2 hx'.2 hi he y
    (G.mem_of_suffix ((List.suffix_cons a y).trans hy) hx.1) a hy hyi
  exact ⟨y', G.isDecision_of_cons_mem (G.mem_of_suffix hy' hx'.1), hy', hinfo⟩

omit [Fintype A] [DecidableEq I] [DecidableEq H] [DecidableEq A] in
/-- No absent-mindedness: two comparable nodes of one information set coincide. -/
theorem eq_of_absentMinded (hNA : G.NoAbsentMindedness) {w x : List A} (hw : G.IsDecision w)
    (hx : G.IsDecision x) (he : G.info w = G.info x) (hwx : w <:+ x) : w = x := by
  classical
  by_contra hne
  exact hNA w hw.1 x hx.1 hw.2 hx.2 he ⟨hwx, hne⟩

omit [DecidableEq H] in
/-- With perfect recall, the first nodes of player `i` after `y` form a union of information
sets, provided no information set is broken at `y`. -/
theorem entry_closed {i : I} (hR : G.RecallFor i) {y : List A}
    (hbr : ∀ w, G.IsDecision w → y <:+ w → ∀ w', G.IsDecision w' → G.info w' = G.info w →
      y <:+ w')
    {x x' : List A} (hx : x ∈ entryNodes G (fun k => G.player k = some i) y)
    (hx' : G.IsDecision x') (he : G.info x' = G.info x) :
    x' ∈ entryNodes G (fun k => G.player k = some i) y := by
  rw [mem_entryNodes] at hx ⊢
  obtain ⟨hdx, hyx, hDx, hmin⟩ := hx
  refine ⟨hx', hbr x hdx hyx x' hx' he, by rw [he]; exact hDx, fun w hw hyw hwx' hne hDw => ?_⟩
  obtain ⟨b, hb⟩ := exists_cons_suffix hwx' hne
  obtain ⟨y'', hy'', hby'', hinfo⟩ := recall_pred G hR hx' hdx (by rw [he]; exact hDx) he hb hDw
  have hy''x : y'' <:+ x := (List.suffix_cons b y'').trans hby''
  have hne'' : y'' ≠ x := by
    rintro rfl
    have := hby''.length_le
    simp at this
  exact hmin y'' hy'' (hbr w hw hyw y'' hy'' hinfo) hy''x hne'' (by rw [hinfo]; exact hDw)

omit [DecidableEq I] in
/-- Grouping a sum over a union of information sets by information set. -/
theorem sum_eq_sum_infoSet {E : Finset (List A)} (hE : ∀ x ∈ E, G.IsDecision x)
    (hcl : ∀ x ∈ E, ∀ x', G.IsDecision x' → G.info x' = G.info x → x' ∈ E) (φ : List A → ℝ) :
    ∑ x ∈ E, φ x = ∑ k ∈ E.image G.info, ∑ x ∈ G.infoSet k, φ x := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := G.info) (t := E.image G.info)
    (fun x hx => Finset.mem_image_of_mem _ hx)]
  refine Finset.sum_congr rfl fun k hk => ?_
  obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.1 hk
  congr 1
  ext x
  simp only [Finset.mem_filter, mem_infoSet]
  exact ⟨fun ⟨hx, he⟩ => ⟨hE x hx, he⟩, fun ⟨hx, he⟩ => ⟨hcl x₀ hx₀ x hx he, he⟩⟩

omit [DecidableEq A] [Fintype A] [DecidableEq H] in
/-- The moves of `update F i g` agree with those of `F` off player `i`'s information sets. -/
theorem assemble_update_eq_off (F : I → H → A → ℝ) (i : I) (g : H → A → ℝ) (k : H)
    (hk : ¬ G.player k = some i) : G.assemble F k = G.assemble (Function.update F i g) k := by
  cases hk' : G.player k with
  | none => rw [assemble_update_of_none G F i g hk']
  | some j =>
    have hji : j ≠ i := fun h => hk (h ▸ hk')
    rw [assemble_update_of_ne G F g hk' hji]

omit [DecidableEq I] in
/-- Reach probabilities of decision nodes in an information set are at most `Prob(H)`. -/
theorem reach_le_probInfo {f : H → A → ℝ} (hf : ∀ k a, 0 ≤ f k a) {k : H} {x : List A}
    (hx : x ∈ G.infoSet k) : G.reach f x ≤ probInfo G f k :=
  Finset.single_le_sum (fun y _ => G.reach_nonneg hf y) hx

/-- The sum of the player's deviation gains over her first information sets (perfect recall):
`U_i(σ) − U_i(σ̃_i, σ_{-i}) = ∑_{H first} ∑_{x ∈ H} P(x) (cont(x) − cont~(x))`. -/
theorem nash_gap_eq {i : I} (hR : G.RecallFor i) (F : I → H → A → ℝ) (g : H → A → ℝ) :
    cont G (G.assemble F) [] i - cont G (G.assemble (Function.update F i g)) [] i =
      ∑ k ∈ (entryNodes G (fun k => G.player k = some i) []).image G.info,
        ∑ x ∈ G.infoSet k, G.reach (G.assemble F) x *
          (cont G (G.assemble F) x i - cont G (G.assemble (Function.update F i g)) x i) := by
  rw [cont_sub_eq_sum_entry G (fun k => G.player k = some i)
    (fun k hk => assemble_update_eq_off G F i g k hk) G.nil_mem]
  simp_rw [reachFrom_nil]
  exact sum_eq_sum_infoSet G (fun x hx => ((mem_entryNodes G).1 hx).1)
    (fun x hx x' hx' he => entry_closed G hR (fun _ _ _ _ _ _ => List.nil_suffix) hx hx' he) _

/-- The belief system derived from `F` by Bayes' rule where possible and uniform elsewhere. -/
noncomputable def bayesOrUniform (f : H → A → ℝ) (x : List A) : ℝ :=
  if 0 < probInfo G f (G.info x) then G.reach f x / probInfo G f (G.info x)
  else 1 / ((G.infoSet (G.info x)).card : ℝ)

omit [DecidableEq I] in
/-- `bayesOrUniform` is a system of beliefs derived by Bayes' rule whenever possible. -/
theorem bayesOrUniform_spec {F : I → H → A → ℝ} (hF : IsBehaviorProfile G F) :
    IsBeliefSystem G (bayesOrUniform G (G.assemble F)) ∧
      BayesConsistent G F (bayesOrUniform G (G.assemble F)) := by
  have hf := assemble_nonneg G hF
  refine ⟨⟨fun x hx => ?_, fun k => ?_⟩, fun k hk x hx => ?_⟩
  · have hxk : x ∈ G.infoSet (G.info x) := (mem_infoSet G).2 ⟨hx, rfl⟩
    have hcard : (1 : ℝ) ≤ ((G.infoSet (G.info x)).card : ℝ) := by
      exact_mod_cast Finset.card_pos.2 ⟨x, hxk⟩
    unfold bayesOrUniform
    split_ifs with hp
    · exact ⟨div_nonneg (G.reach_nonneg hf x) hp.le,
        (div_le_one hp).2 (reach_le_probInfo G hf hxk)⟩
    · exact ⟨by positivity, (div_le_one (by linarith)).2 hcard⟩
  · have hinfo : ∀ x ∈ G.infoSet k, G.info x = k := fun x hx => ((mem_infoSet G).1 hx).2
    rw [Finset.sum_congr rfl fun x hx => by rw [bayesOrUniform, hinfo x hx]]
    by_cases hp : 0 < probInfo G (G.assemble F) k
    · simp only [hp, ite_true]
      rw [← Finset.sum_div]
      exact div_self hp.ne'
    · simp only [hp, ite_false, Finset.sum_const, nsmul_eq_mul]
      have hne : (G.infoSet k).Nonempty := (G.infoSet_partition).1 k
      have : ((G.infoSet k).card : ℝ) ≠ 0 := by exact_mod_cast hne.card_pos.ne'
      field_simp
  · have hxk : G.info x = k := ((mem_infoSet G).1 hx).2
    simp only [bayesOrUniform, hxk, hk, ite_true]

/-- **Proposition 9.C.1** (MWG, p. 285; Exercise 9.C.1). In a game with perfect recall, a
behaviour profile `σ` is a Nash equilibrium iff there is a system of beliefs `μ` such that
(i) `σ` is sequentially rational given `μ` at every information set `H` with
`Prob(H | σ) > 0`, and (ii) `μ` is derived from `σ` through Bayes' rule whenever possible. -/
theorem proposition_9_C_1 (hPR : G.PerfectRecall) (F : I → H → A → ℝ) :
    IsNashB G F ↔ IsBehaviorProfile G F ∧ ∃ μ, IsBeliefSystem G μ ∧
      (∀ k, 0 < probInfo G (G.assemble F) k → SeqRationalAt G F μ k) ∧ BayesConsistent G F μ := by
  constructor
  · intro hN
    have hF := hN.1
    have hf := assemble_nonneg G hF
    obtain ⟨hμ, hB⟩ := bayesOrUniform_spec G hF
    refine ⟨hF, bayesOrUniform G (G.assemble F), hμ, fun k hk i hi g hg => ?_, hB⟩
    classical
    -- the deviation `g` at and after `k`, `F i` elsewhere
    let Aft : H → Prop := fun k' => ∃ x ∈ G.infoSet k, ∃ w ∈ G.decisionNodes, x <:+ w ∧
      G.info w = k'
    let g' : H → A → ℝ := fun k' => if Aft k' then g k' else F i k'
    have hg' : G.IsBehaviorStrategy i g' := fun k' hk' => by
      simp only [g']
      split_ifs
      · exact hg k' hk'
      · exact hF i k' hk'
    have hdev := hN.2 i g' hg'
    let D : H → Prop := fun k' => G.player k' = some i ∧ Aft k'
    have hoff : ∀ k', ¬ D k' → G.assemble F k' = G.assemble (Function.update F i g') k' := by
      intro k' hk'
      by_cases hpi : G.player k' = some i
      · have hA : ¬ Aft k' := fun h => hk' ⟨hpi, h⟩
        rw [assemble_update_self G F g' hpi, G.assemble_of_some _ hpi]
        simp only [g', hA, ite_false]
      · exact assemble_update_eq_off G F i g' k' hpi
    have hdec := cont_sub_eq_sum_entry G D hoff G.nil_mem i
    -- the entry nodes of `D` are exactly the nodes of `k`
    have hE : entryNodes G D [] = G.infoSet k := by
      ext x
      rw [mem_entryNodes, mem_infoSet]
      constructor
      · rintro ⟨hx, -, ⟨hpx, x₀, hx₀, w₁, hw₁, hx₀w, hwinfo⟩, hmin⟩
        rw [mem_infoSet] at hx₀
        rw [mem_decisionNodes] at hw₁
        refine ⟨hx, ?_⟩
        by_cases h01 : x₀ = w₁
        · subst h01
          rw [← hwinfo, hx₀.2]
        · exfalso
          obtain ⟨b, hb⟩ := exists_cons_suffix hx₀w h01
          obtain ⟨y', hy', hby', hinfo⟩ := recall_pred G (hPR.2 i) hw₁ hx
            (by rw [hwinfo]; exact hpx) hwinfo hb (by rw [hx₀.2]; exact hi)
          have hy'x : y' <:+ x := (List.suffix_cons b y').trans hby'
          have hne : y' ≠ x := by
            rintro rfl
            have := hby'.length_le
            simp at this
          refine hmin y' hy' List.nil_suffix hy'x hne ⟨by rw [hinfo, hx₀.2]; exact hi, ?_⟩
          exact ⟨y', (mem_infoSet G).2 ⟨hy', by rw [hinfo, hx₀.2]⟩, y',
            (mem_decisionNodes G).2 hy', List.suffix_refl _, rfl⟩
      · rintro ⟨hx, hxk⟩
        refine ⟨hx, List.nil_suffix, ⟨by rw [hxk]; exact hi, x, (mem_infoSet G).2 ⟨hx, hxk⟩, x,
          (mem_decisionNodes G).2 hx, List.suffix_refl _, rfl⟩, ?_⟩
        rintro w hw - hwx hne ⟨hpw, x₀, hx₀, w₁, hw₁, hx₀w, hwinfo⟩
        rw [mem_infoSet] at hx₀
        rw [mem_decisionNodes] at hw₁
        by_cases h01 : x₀ = w₁
        · subst h01
          exact hne (eq_of_absentMinded G hPR.1 hw hx (by rw [← hwinfo, hx₀.2, hxk]) hwx)
        · obtain ⟨b, hb⟩ := exists_cons_suffix hx₀w h01
          obtain ⟨y', hy', hby', hinfo⟩ := recall_pred G (hPR.2 i) hw₁ hw
            (by rw [hwinfo]; exact hpw) hwinfo hb (by rw [hx₀.2]; exact hi)
          have hy'x : y' <:+ x := ((List.suffix_cons b y').trans hby').trans hwx
          have := eq_of_absentMinded G hPR.1 hy' hx (by rw [hinfo, hx₀.2, hxk]) hy'x
          subst this
          have := hby'.length_le
          have := hwx.length_le
          simp at *
          omega
    -- after `k`, `g'` coincides with `g`
    have hafter : ∀ x ∈ G.infoSet k, cont G (G.assemble (Function.update F i g')) x i =
        cont G (G.assemble (Function.update F i g)) x i := by
      intro x hx
      refine cont_congr G (fun w hw hxw => ?_) i
      have hA : Aft (G.info w) := ⟨x, hx, w, (mem_decisionNodes G).2 hw, hxw, rfl⟩
      by_cases hpi : G.player (G.info w) = some i
      · rw [assemble_update_self G F g' hpi, assemble_update_self G F g hpi]
        simp only [g', hA, ite_true]
      · rw [← assemble_update_eq_off G F i g' _ hpi, ← assemble_update_eq_off G F i g _ hpi]
    rw [hE] at hdec
    have hsum : 0 ≤ ∑ x ∈ G.infoSet k, G.reach (G.assemble F) x *
        (cont G (G.assemble F) x i - cont G (G.assemble (Function.update F i g)) x i) := by
      have := sub_nonneg.2 hdev
      rw [hdec] at this
      simp_rw [reachFrom_nil] at this
      rwa [Finset.sum_congr rfl fun x hx => by rw [← hafter x hx]]
    have hreach : ∀ x ∈ G.infoSet k, G.reach (G.assemble F) x =
        probInfo G (G.assemble F) k * bayesOrUniform G (G.assemble F) x := by
      intro x hx
      rw [hB k hk x hx]
      field_simp
    rw [Finset.sum_congr rfl fun x hx => by rw [hreach x hx]] at hsum
    simp_rw [mul_assoc] at hsum
    rw [← Finset.mul_sum] at hsum
    have h2 := nonneg_of_mul_nonneg_right hsum hk
    simp_rw [mul_sub] at h2
    rw [Finset.sum_sub_distrib] at h2
    unfold condPayoff
    linarith
  · rintro ⟨hF, μ, hμ, hSR, hB⟩
    refine ⟨hF, fun i g hg => ?_⟩
    have hf := assemble_nonneg G hF
    rw [← sub_nonneg, nash_gap_eq G (hPR.2 i)]
    refine Finset.sum_nonneg fun k hk => ?_
    obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.1 hk
    have hpi : G.player (G.info x₀) = some i := ((mem_entryNodes G).1 hx₀).2.2.1
    by_cases hp : 0 < probInfo G (G.assemble F) (G.info x₀)
    · have hreach : ∀ x ∈ G.infoSet (G.info x₀), G.reach (G.assemble F) x =
          probInfo G (G.assemble F) (G.info x₀) * μ x := by
        intro x hx
        rw [hB _ hp x hx]
        field_simp
      rw [Finset.sum_congr rfl fun x hx => by rw [hreach x hx]]
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum]
      refine mul_nonneg hp.le ?_
      have := hSR _ hp i hpi g hg
      unfold condPayoff at this
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib]
      linarith
    · have hzero : ∀ x ∈ G.infoSet (G.info x₀), G.reach (G.assemble F) x = 0 := by
        intro x hx
        have h0 : probInfo G (G.assemble F) (G.info x₀) = 0 :=
          le_antisymm (not_lt.1 hp) (Finset.sum_nonneg fun y _ => G.reach_nonneg hf y)
        exact le_antisymm (h0 ▸ reach_le_probInfo G hf hx) (G.reach_nonneg hf x)
      rw [Finset.sum_eq_zero fun x hx => by rw [hzero x hx, zero_mul]]

/-- **Section 9.C** (MWG, p. 286). With perfect recall, a weak perfect Bayesian equilibrium is a
Nash equilibrium. -/
theorem isNashB_of_isWeakPBE (hPR : G.PerfectRecall) {F : I → H → A → ℝ} {μ : List A → ℝ}
    (h : IsWeakPBE G F μ) : IsNashB G F :=
  (proposition_9_C_1 G hPR F).2 ⟨h.1, μ, h.2.1, fun k _ => h.2.2.1 k, h.2.2.2⟩

/-- A totally mixed behaviour profile: every player puts positive probability on every
available action at each of her information sets (MWG, p. 284). -/
def IsTotallyMixedB (F : I → H → A → ℝ) : Prop :=
  IsBehaviorProfile G F ∧ ∀ i k, G.player k = some i → ∀ a ∈ G.avail k, 0 < F i k a

/-- The beliefs derived from the moves `f` by Bayes' rule: `Prob(x | σ) / Prob(H(x) | σ)`. -/
noncomputable def bayesBelief (f : H → A → ℝ) (x : List A) : ℝ :=
  G.reach f x / probInfo G f (G.info x)

/-- **Definition 9.C.4(ii)** (MWG, p. 290). The assessment `(σ, μ)` is consistent: there are
totally mixed profiles `σᵏ → σ` whose Bayes beliefs converge to `μ`. -/
def IsConsistent (F : I → H → A → ℝ) (μ : List A → ℝ) : Prop :=
  ∃ Fs : ℕ → I → H → A → ℝ, (∀ n, IsTotallyMixedB G (Fs n)) ∧ Tendsto Fs atTop (𝓝 F) ∧
    ∀ x, G.IsDecision x → Tendsto (fun n => bayesBelief G (G.assemble (Fs n)) x) atTop (𝓝 (μ x))

/-- **Definition 9.C.4** (MWG, p. 290). A sequential equilibrium: a behaviour profile and a
system of beliefs such that (i) the profile is sequentially rational given the beliefs and
(ii) the assessment is consistent. -/
def IsSequentialEq (F : I → H → A → ℝ) (μ : List A → ℝ) : Prop :=
  IsBehaviorProfile G F ∧ IsBeliefSystem G μ ∧ SeqRational G F μ ∧ IsConsistent G F μ

omit [DecidableEq A] [Fintype A] [DecidableEq I] [DecidableEq H] in
/-- The moves of a profile depend continuously on the profile. -/
theorem tendsto_assemble {Fs : ℕ → I → H → A → ℝ} {F : I → H → A → ℝ}
    (h : Tendsto Fs atTop (𝓝 F)) (k : H) (a : A) :
    Tendsto (fun n => G.assemble (Fs n) k a) atTop (𝓝 (G.assemble F k a)) := by
  cases hk : G.player k with
  | none =>
    simp only [G.assemble_of_none _ hk]
    exact tendsto_const_nhds
  | some j =>
    simp only [G.assemble_of_some _ hk]
    exact tendsto_pi_nhds.1 (tendsto_pi_nhds.1 (tendsto_pi_nhds.1 h j) k) a

omit [Fintype A] [DecidableEq I] [DecidableEq H] in
/-- Reach probabilities depend continuously on the profile. -/
theorem tendsto_reachFrom {Fs : ℕ → I → H → A → ℝ} {F : I → H → A → ℝ}
    (h : Tendsto Fs atTop (𝓝 F)) (x z : List A) :
    Tendsto (fun n => reachFrom G (G.assemble (Fs n)) x z) atTop
      (𝓝 (reachFrom G (G.assemble F) x z)) := by
  induction z with
  | nil =>
    simp only [reachFrom]
    exact tendsto_const_nhds
  | cons a z ih =>
    simp only [reachFrom]
    split_ifs
    · exact tendsto_const_nhds
    · exact ih.mul (tendsto_assemble G h _ _)

omit [Fintype A] [DecidableEq I] [DecidableEq H] [DecidableEq A] in
/-- Reach probabilities depend continuously on the profile. -/
theorem tendsto_reach {Fs : ℕ → I → H → A → ℝ} {F : I → H → A → ℝ}
    (h : Tendsto Fs atTop (𝓝 F)) (z : List A) :
    Tendsto (fun n => G.reach (G.assemble (Fs n)) z) atTop (𝓝 (G.reach (G.assemble F) z)) := by
  classical
  simp_rw [← reachFrom_nil]
  exact tendsto_reachFrom G h [] z

/-- **Section 9.C** (MWG, p. 290). Every sequential equilibrium is a weak perfect Bayesian
equilibrium: the limiting beliefs coincide with the Bayes beliefs on the equilibrium path. -/
theorem isWeakPBE_of_isSequentialEq {F : I → H → A → ℝ} {μ : List A → ℝ}
    (h : IsSequentialEq G F μ) : IsWeakPBE G F μ := by
  obtain ⟨hF, hμ, hSR, Fs, -, hlim, hbel⟩ := h
  refine ⟨hF, hμ, hSR, fun k hk x hx => ?_⟩
  obtain ⟨hxd, hxk⟩ := (mem_infoSet G).1 hx
  have h1 := hbel x hxd
  have h2 : Tendsto (fun n => bayesBelief G (G.assemble (Fs n)) x) atTop
      (𝓝 (G.reach (G.assemble F) x / probInfo G (G.assemble F) k)) := by
    unfold bayesBelief
    rw [hxk]
    exact (tendsto_reach G hlim x).div
      (tendsto_finsetSum _ fun y _ => tendsto_reach G hlim y) hk.ne'
  exact tendsto_nhds_unique h1 h2

omit [DecidableEq I] in
/-- Consistent beliefs inside a subgame: on an information set `k` lying after the subgame
root `x₀`, the probabilities `P(x | x₀)` are proportional to the beliefs. -/
theorem reachFrom_prop_of_consistent {F : I → H → A → ℝ} {μ : List A → ℝ}
    (hμ : IsBeliefSystem G μ) (hc : IsConsistent G F μ) {x₀ : List A} {k : H}
    (hk : ∀ x ∈ G.infoSet k, x₀ <:+ x) :
    ∃ c, 0 ≤ c ∧ ∀ x ∈ G.infoSet k, reachFrom G (G.assemble F) x₀ x = c * μ x := by
  obtain ⟨Fs, hFs, hlim, hbel⟩ := hc
  set R : ℕ → ℝ := fun n => ∑ x ∈ G.infoSet k, reachFrom G (G.assemble (Fs n)) x₀ x
  have hR : Tendsto R atTop (𝓝 (∑ x ∈ G.infoSet k, reachFrom G (G.assemble F) x₀ x)) :=
    tendsto_finsetSum _ fun x _ => tendsto_reachFrom G hlim x₀ x
  have hprob : ∀ n, probInfo G (G.assemble (Fs n)) k =
      G.reach (G.assemble (Fs n)) x₀ * R n := by
    intro n
    simp only [probInfo, R, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x hx => reach_eq_mul_reachFrom G _ (hk x hx)
  have hf : ∀ n, ∀ x ∈ G.infoSet k, bayesBelief G (G.assemble (Fs n)) x =
      G.reach (G.assemble (Fs n)) x / probInfo G (G.assemble (Fs n)) k := fun n x hx => by
    rw [bayesBelief, ((mem_infoSet G).1 hx).2]
  have hfB := fun n => assemble_nonneg G (hFs n).1
  have hfF : ∀ k a, 0 ≤ G.assemble F k a := fun k a =>
    ge_of_tendsto' (tendsto_assemble G hlim k a) fun n => hfB n k a
  refine ⟨∑ x ∈ G.infoSet k, reachFrom G (G.assemble F) x₀ x,
    Finset.sum_nonneg fun x _ => reachFrom_nonneg G hfF _ _, fun x hx => ?_⟩
  by_cases hfreq : ∃ᶠ n in atTop, probInfo G (G.assemble (Fs n)) k = 0
  · exfalso
    have hz : ∀ y ∈ G.infoSet k, μ y = 0 := by
      intro y hy
      refine tendsto_nhds_unique_of_frequently_eq (hbel y ((mem_infoSet G).1 hy).1)
        tendsto_const_nhds (hfreq.mono fun n hn => ?_)
      rw [hf n y hy, hn, div_zero]
    have := hμ.2 k
    rw [Finset.sum_eq_zero hz] at this
    norm_num at this
  · rw [not_frequently] at hfreq
    have hev : ∀ᶠ n in atTop, reachFrom G (G.assemble (Fs n)) x₀ x =
        R n * bayesBelief G (G.assemble (Fs n)) x := by
      filter_upwards [hfreq] with n hn
      rw [hf n x hx, hprob n, reach_eq_mul_reachFrom G _ (hk x hx)]
      have h0 : G.reach (G.assemble (Fs n)) x₀ ≠ 0 := fun h0 => hn (by rw [hprob n, h0, zero_mul])
      have h1 : R n ≠ 0 := fun h1 => hn (by rw [hprob n, h1, mul_zero])
      field_simp
    exact tendsto_nhds_unique (tendsto_reachFrom G hlim x₀ x)
      ((hR.mul (hbel x ((mem_infoSet G).1 hx).1)).congr' (hev.mono fun n hn => hn.symm))

/-- **Proposition 9.C.2** (MWG, p. 291). In a game with perfect recall, in every sequential
equilibrium `(σ, μ)` the strategy profile `σ` is a subgame perfect Nash equilibrium. -/
theorem proposition_9_C_2 (hPR : G.PerfectRecall) {F : I → H → A → ℝ} {μ : List A → ℝ}
    (h : IsSequentialEq G F μ) : IsSPNE G F := by
  obtain ⟨hF, hμ, hSR, hc⟩ := h
  refine ⟨hF, fun x₀ hx₀ i g hg => ?_⟩
  rw [← sub_nonneg, cont_sub_eq_sum_entry G (fun k => G.player k = some i)
    (fun k hk => assemble_update_eq_off G F i g k hk) hx₀.1.1 i]
  have hbr := hx₀.2.2
  rw [sum_eq_sum_infoSet G (fun x hx => ((mem_entryNodes G).1 hx).1)
    (fun x hx x' hx' he => entry_closed G (hPR.2 i) hbr hx hx' he)]
  refine Finset.sum_nonneg fun k hk => ?_
  obtain ⟨x₁, hx₁, rfl⟩ := Finset.mem_image.1 hk
  have hpi : G.player (G.info x₁) = some i := ((mem_entryNodes G).1 hx₁).2.2.1
  have hin : ∀ x ∈ G.infoSet (G.info x₁), x₀ <:+ x := fun x hx =>
    hbr x₁ ((mem_entryNodes G).1 hx₁).1 ((mem_entryNodes G).1 hx₁).2.1 x
      ((mem_infoSet G).1 hx).1 ((mem_infoSet G).1 hx).2
  obtain ⟨c, hc0, hcμ⟩ := reachFrom_prop_of_consistent G hμ hc hin
  rw [Finset.sum_congr rfl fun x hx => by rw [hcμ x hx]]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  refine mul_nonneg hc0 ?_
  have := hSR _ i hpi g hg
  unfold condPayoff at this
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  linarith

/-- **Section 9.C** (MWG, p. 291). With perfect recall, every sequential equilibrium is both a
weak perfect Bayesian equilibrium and a subgame perfect Nash equilibrium. -/
theorem isSequentialEq_strengthens (hPR : G.PerfectRecall) {F : I → H → A → ℝ}
    {μ : List A → ℝ} (h : IsSequentialEq G F μ) : IsWeakPBE G F μ ∧ IsSPNE G F :=
  ⟨isWeakPBE_of_isSequentialEq G h, proposition_9_C_2 G hPR h⟩

end MWG.DynamicGames
