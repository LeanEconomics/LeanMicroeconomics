/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGDynamicGames.Beliefs

/-!
# The one-shot deviation principle for consistent assessments

MWG, Section 9.C and Appendix B (pp. 290-292 and 300). To verify sequential rationality
(Definition 9.C.2) it suffices, for a consistent assessment in a game with perfect recall, to
rule out deviations at a single information set followed by the equilibrium continuation:
`oneShot_consistent`. This is the step behind MWG's claim (p. 300) that every extensive form
trembling-hand perfect equilibrium is a sequential equilibrium.

* `NatureFullSupport`: nature puts positive probability on every available move (Kreps and
  Wilson's standing assumption; then totally mixed profiles reach every node,
  `reach_pos_of_totallyMixed`).
* `entry_cons_closed`, `entry_cons_unique`: with perfect recall, player `i`'s first nodes after
  the move `b` at her information set `k` form whole information sets, each node being reached
  from a unique node of `k`.
* `propagate_consistent`: consistent beliefs at a later information set of player `i` are
  derived from the beliefs at `k` by Bayes' rule (the limit of the Bayes relation along the
  totally mixed sequence).
* `oneShot_consistent`: with perfect recall, nature's full support and a consistent assessment,
  if no player can gain by changing her move at one information set (keeping the rest of the
  profile), then the profile is sequentially rational.
-/

namespace MWG.DynamicGames

open MWG.NoncooperativeGames MWG.NoncooperativeGames.ExtensiveForm Filter Topology

variable {I A H : Type*} (G : ExtensiveForm I A H) [DecidableEq A] [Fintype A] [DecidableEq I]
  [DecidableEq H]

/-- Nature puts positive probability on every available move. -/
def NatureFullSupport : Prop :=
  ∀ k, G.player k = none → ∀ a ∈ G.avail k, 0 < G.natureProb k a

omit [DecidableEq A] [Fintype A] [DecidableEq I] [DecidableEq H] in
/-- Under a totally mixed profile, with nature's full support, every node is reached with
positive probability. -/
theorem reach_pos_of_totallyMixed (hN : NatureFullSupport G) {F : I → H → A → ℝ}
    (hF : IsTotallyMixedB G F) {x : List A} (hx : x ∈ G.nodes) :
    0 < G.reach (G.assemble F) x := by
  induction x with
  | nil => simp
  | cons a x ih =>
    rw [reach_cons]
    have ha : a ∈ G.avail (G.info x) := G.mem_avail_of_cons_mem hx
    refine mul_pos (ih (G.mem_of_cons_mem hx)) ?_
    cases hk : G.player (G.info x) with
    | none => rw [G.assemble_of_none _ hk]; exact hN _ hk a ha
    | some j => rw [G.assemble_of_some _ hk]; exact hF.2 j _ hk a ha

omit [DecidableEq I] in
/-- Under a totally mixed profile, with nature's full support, every information set is
reached with positive probability. -/
theorem probInfo_pos (hN : NatureFullSupport G) {F : I → H → A → ℝ}
    (hF : IsTotallyMixedB G F) (k : H) : 0 < probInfo G (G.assemble F) k := by
  obtain ⟨x, hx⟩ := (G.infoSet_partition).1 k
  exact lt_of_lt_of_le (reach_pos_of_totallyMixed G hN hF ((mem_infoSet G).1 hx).1.1)
    (reach_le_probInfo G (assemble_nonneg G hF.1) hx)

omit [DecidableEq I] in
/-- Bayes beliefs at a reached information set sum to one. -/
theorem sum_bayesBelief {f : H → A → ℝ} {k : H} (hk : 0 < probInfo G f k) :
    ∑ x ∈ G.infoSet k, bayesBelief G f x = 1 := by
  rw [Finset.sum_congr rfl fun x hx => by rw [bayesBelief, ((mem_infoSet G).1 hx).2],
    ← Finset.sum_div]
  exact div_self hk.ne'

/-- The set of first nodes of player `i` after the move `b` at node `x`. -/
abbrev iEntry (i : I) (b : A) (x : List A) : Finset (List A) :=
  entryNodes G (fun k => G.player k = some i) (b :: x)

omit [DecidableEq I] in
/-- With perfect recall, a node of `k` preceding a node `x'` is unique. -/
theorem entry_cons_unique (hNA : G.NoAbsentMindedness) {k : H} {x x₁ x' : List A} {b b₁ : A}
    (hx : x ∈ G.infoSet k) (hx₁ : x₁ ∈ G.infoSet k) (h : b :: x <:+ x')
    (h₁ : b₁ :: x₁ <:+ x') : x = x₁ := by
  rw [mem_infoSet] at hx hx₁
  have hs : x <:+ x' := (List.suffix_cons b x).trans h
  have hs₁ : x₁ <:+ x' := (List.suffix_cons b₁ x₁).trans h₁
  rcases le_total x.length x₁.length with hl | hl
  · exact eq_of_absentMinded G hNA hx.1 hx₁.1 (by rw [hx.2, hx₁.2])
      (List.suffix_of_suffix_length_le hs hs₁ hl)
  · exact (eq_of_absentMinded G hNA hx₁.1 hx.1 (by rw [hx.2, hx₁.2])
      (List.suffix_of_suffix_length_le hs₁ hs hl)).symm

/-- **Perfect recall closure.** If `x'` is a first node of player `i` after the move `b` at a
node of her information set `k`, then so is every node of `H(x')`. -/
theorem entry_cons_closed (hPR : G.PerfectRecall) {i : I} {k : H} (hk : G.player k = some i)
    {b : A} {x x' x'' : List A} (hx : x ∈ G.infoSet k) (hx' : x' ∈ iEntry G i b x)
    (hx'' : G.IsDecision x'') (he : G.info x'' = G.info x') :
    ∃ x₁ ∈ G.infoSet k, x'' ∈ iEntry G i b x₁ := by
  rw [mem_infoSet] at hx
  rw [mem_entryNodes] at hx'
  obtain ⟨hdx', hbx', hDx', hmin⟩ := hx'
  obtain ⟨x₁, hx₁, hbx₁, hinfo⟩ := recall_pred G (hPR.2 i) hdx' hx'' hDx' he.symm hbx'
    (by rw [hx.2]; exact hk)
  refine ⟨x₁, (mem_infoSet G).2 ⟨hx₁, by rw [hinfo, hx.2]⟩, ?_⟩
  rw [mem_entryNodes]
  refine ⟨hx'', hbx₁, by rw [he]; exact hDx', fun w hw hbw hwx hne hDw => ?_⟩
  obtain ⟨a', ha'⟩ := exists_cons_suffix hwx hne
  obtain ⟨w', hw', haw', hinfo'⟩ := recall_pred G (hPR.2 i) hx'' hdx' (by rw [he]; exact hDx')
    he ha' hDw
  have hw'x' : w' <:+ x' := (List.suffix_cons a' w').trans haw'
  have hw'ne : w' ≠ x' := by
    rintro rfl
    have := haw'.length_le
    simp at this
  -- `w'` and `b :: x` are both predecessors of `x'`
  rcases le_or_gt (b :: x).length w'.length with hl | hl
  · exact hmin w' hw' (List.suffix_of_suffix_length_le hbx' hw'x' hl) hw'x' hw'ne
      (by rw [hinfo']; exact hDw)
  · have hw'x0 : w' <:+ x := by
      have hw'x : w' <:+ b :: x := List.suffix_of_suffix_length_le hw'x' hbx' hl.le
      rcases List.suffix_cons_iff.1 hw'x with h | h
      · rw [h] at hl
        exact absurd hl (lt_irrefl _)
      · exact h
    by_cases hwx0 : w' = x
    · subst hwx0
      -- `w` lies strictly after `x₁` in `k`: absent-mindedness
      have : x₁ = w := eq_of_absentMinded G hPR.1 hx₁ hw (by rw [hinfo, ← hinfo', hx.2])
        ((List.suffix_cons b x₁).trans hbw)
      subst this
      have := hbw.length_le
      simp at this
    · obtain ⟨a'', ha''⟩ := exists_cons_suffix hw'x0 hwx0
      obtain ⟨ŵ, hŵ, haŵ, hinfoŵ⟩ := recall_pred G (hPR.2 i) hx.1 hx₁
        (by rw [hx.2]; exact hk) (by rw [hinfo, hx.2]) ha'' (by rw [hinfo']; exact hDw)
      have hŵw : ŵ <:+ w :=
        ((List.suffix_cons a'' ŵ).trans haŵ).trans ((List.suffix_cons b x₁).trans hbw)
      have := eq_of_absentMinded G hPR.1 hŵ hw (by rw [hinfoŵ, hinfo']) hŵw
      subst this
      have h1 := haŵ.length_le
      have h2 := hbw.length_le
      simp at h1 h2
      omega

/-- The weight that the beliefs `μ` at player `i`'s information set `k`, followed by the move
`b` and then by the moves `f`, put on a first later node `x'` of player `i`. -/
noncomputable def propW (f : H → A → ℝ) (μ : List A → ℝ) (i : I) (k : H) (b : A)
    (x' : List A) : ℝ :=
  ∑ x ∈ G.infoSet k, if x' ∈ iEntry G i b x then μ x * reachFrom G f (b :: x) x' else 0

/-- **Bayes propagation for consistent beliefs.** With perfect recall and nature's full
support, for a consistent assessment the weight `propW` that the beliefs at `k` and the move
`b` put on a later information set `k'` of the same player is proportional to the beliefs at
`k'`; and when it is not zero, every node of `k'` follows a node of `k` by the move `b`. -/
theorem propagate_consistent (hPR : G.PerfectRecall) (hN : NatureFullSupport G)
    {F : I → H → A → ℝ} {μ : List A → ℝ} (hc : IsConsistent G F μ) {i : I} {k : H}
    (hk : G.player k = some i) {b : A} (hb : b ∈ G.avail k) (k' : H) :
    ∃ c, 0 ≤ c ∧ (∀ x' ∈ G.infoSet k', propW G (G.assemble F) μ i k b x' = c * μ x') ∧
      (c ≠ 0 → ∀ x'' ∈ G.infoSet k', ∃ x ∈ G.infoSet k, b :: x <:+ x'') := by
  obtain ⟨Fs, hFs, hlim, hbel⟩ := hc
  have hFnn : ∀ k a, 0 ≤ G.assemble F k a := fun k a =>
    ge_of_tendsto' (tendsto_assemble G hlim k a) fun n => assemble_nonneg G (hFs n).1 k a
  have hμnn : ∀ x, G.IsDecision x → 0 ≤ μ x := fun x hx =>
    ge_of_tendsto' (hbel x hx) fun n => div_nonneg
      (G.reach_nonneg (assemble_nonneg G (hFs n).1) x)
      (Finset.sum_nonneg fun y _ => G.reach_nonneg (assemble_nonneg G (hFs n).1) y)
  by_cases hR : ∃ x' ∈ G.infoSet k', ∃ x ∈ G.infoSet k, x' ∈ iEntry G i b x
  · obtain ⟨x'₀, hx'₀, x₀, hx₀, hE₀⟩ := hR
    have hall : ∀ x'' ∈ G.infoSet k', ∃ x ∈ G.infoSet k, x'' ∈ iEntry G i b x :=
      fun x'' hx'' => entry_cons_closed G hPR hk hx₀ hE₀ ((mem_infoSet G).1 hx'').1
        (by rw [((mem_infoSet G).1 hx'').2, ((mem_infoSet G).1 hx'₀).2])
    set fn : ℕ → H → A → ℝ := fun n => G.assemble (Fs n)
    have hP : ∀ n k, 0 < probInfo G (fn n) k := fun n k => probInfo_pos G hN (hFs n) k
    have hfb : ∀ n, 0 < fn n k b := fun n => by
      simp only [fn]
      rw [G.assemble_of_some _ hk]
      exact (hFs n).2 i k hk b hb
    -- the exact Bayes relation along the sequence
    have hWn : ∀ n, ∀ x' ∈ G.infoSet k', propW G (fn n) (bayesBelief G (fn n)) i k b x' =
        probInfo G (fn n) k' / (probInfo G (fn n) k * fn n k b) * bayesBelief G (fn n) x' := by
      intro n x' hx'
      obtain ⟨x₁, hx₁, hE₁⟩ := hall x' hx'
      unfold propW
      rw [Finset.sum_eq_single x₁ (fun x hx hne => by
        split_ifs with h
        · exact absurd (entry_cons_unique G hPR.1 hx hx₁ ((mem_entryNodes G).1 h).2.1
            ((mem_entryNodes G).1 hE₁).2.1) hne
        · rfl) (fun h => absurd hx₁ h)]
      simp only [hE₁, ↓reduceIte]
      obtain ⟨hx₁d, hx₁k⟩ := (mem_infoSet G).1 hx₁
      have hbx' := ((mem_entryNodes G).1 hE₁).2.1
      have hreach : G.reach (fn n) x' = G.reach (fn n) x₁ * fn n k b *
          reachFrom G (fn n) (b :: x₁) x' := by
        rw [reach_eq_mul_reachFrom G _ ((List.suffix_cons b x₁).trans hbx'),
          reachFrom_trans G _ (List.suffix_cons b x₁) hbx', reachFrom_cons_self, hx₁k]
        ring
      unfold bayesBelief
      rw [hx₁k, ((mem_infoSet G).1 hx').2, hreach]
      have h1 := (hP n k).ne'
      have h2 := (hP n k').ne'
      have h3 := (hfb n).ne'
      field_simp
    have hconv : ∀ x', Tendsto (fun n => propW G (fn n) (bayesBelief G (fn n)) i k b x') atTop
        (𝓝 (propW G (G.assemble F) μ i k b x')) := by
      intro x'
      unfold propW
      refine tendsto_finsetSum _ fun x hx => ?_
      by_cases h : x' ∈ iEntry G i b x
      · simp only [h, ↓reduceIte]
        exact (hbel x ((mem_infoSet G).1 hx).1).mul (tendsto_reachFrom G hlim _ _)
      · simp only [h, ↓reduceIte]
        exact tendsto_const_nhds
    set c := ∑ x' ∈ G.infoSet k', propW G (G.assemble F) μ i k b x'
    have hsum : ∀ n, ∑ x' ∈ G.infoSet k', propW G (fn n) (bayesBelief G (fn n)) i k b x' =
        probInfo G (fn n) k' / (probInfo G (fn n) k * fn n k b) := by
      intro n
      rw [Finset.sum_congr rfl (hWn n), ← Finset.mul_sum, sum_bayesBelief G (hP n k'), mul_one]
    have hκ : Tendsto (fun n => probInfo G (fn n) k' / (probInfo G (fn n) k * fn n k b)) atTop
        (𝓝 c) := (tendsto_finsetSum _ fun x' _ => hconv x').congr hsum
    have hWnn : ∀ x', 0 ≤ propW G (G.assemble F) μ i k b x' := fun x' =>
      Finset.sum_nonneg fun x hx => by
        split_ifs
        · exact mul_nonneg (hμnn x ((mem_infoSet G).1 hx).1) (reachFrom_nonneg G hFnn _ _)
        · exact le_rfl
    refine ⟨c, Finset.sum_nonneg fun x' _ => hWnn x', fun x' hx' => ?_, fun _ x'' hx'' => ?_⟩
    · exact tendsto_nhds_unique (hconv x')
        ((hκ.mul (hbel x' ((mem_infoSet G).1 hx').1)).congr fun n => (hWn n x' hx').symm)
    · obtain ⟨x, hx, hE⟩ := hall x'' hx''
      exact ⟨x, hx, ((mem_entryNodes G).1 hE).2.1⟩
  · push Not at hR
    refine ⟨0, le_rfl, fun x' hx' => ?_, fun h => absurd rfl h⟩
    rw [zero_mul]
    exact Finset.sum_eq_zero fun x hx => by simp [hR x' hx' x hx]

/-- **One-shot deviation principle for consistent assessments** (MWG, pp. 290 and 300). In a
game with perfect recall in which nature's moves have full support, let `(σ, μ)` be a
consistent assessment such that at each information set `k` of player `i` no move `b` followed
by `σ` gives `i` a higher expected payoff under `μ` than `σ` itself. Then `σ` is sequentially
rational for player `i`: no deviation to any behaviour strategy raises `E[u_i | k, μ, ·]`. -/
theorem oneShot_consistent (hPR : G.PerfectRecall) (hN : NatureFullSupport G)
    {F : I → H → A → ℝ} {μ : List A → ℝ} (hc : IsConsistent G F μ) {i : I}
    (hone : ∀ k, G.player k = some i → ∀ b ∈ G.avail k,
      ∑ x ∈ G.infoSet k, μ x * cont G (G.assemble F) (b :: x) i ≤
        condPayoff G (G.assemble F) μ k i)
    {g : H → A → ℝ} (hg : G.IsBehaviorStrategy i g) {k : H} (hk : G.player k = some i) :
    condPayoff G (G.assemble (Function.update F i g)) μ k i ≤
      condPayoff G (G.assemble F) μ k i := by
  set f := G.assemble F
  set f' := G.assemble (Function.update F i g)
  have hoff : ∀ k, ¬ (fun k => G.player k = some i) k → f k = f' k := fun k hk =>
    assemble_update_eq_off G F i g k hk
  set Xi := G.decisionNodes.filter fun x => G.player (G.info x) = some i
  set Dm := G.nodes.sup List.length
  suffices key : ∀ n, ∀ k, G.player k = some i → (∀ x ∈ G.infoSet k, Dm - x.length ≤ n) →
      condPayoff G f' μ k i ≤ condPayoff G f μ k i from
    key Dm k hk fun x _ => Nat.sub_le _ _
  intro n
  induction n with
  | zero =>
    intro k _ hd
    obtain ⟨x, hx⟩ := (G.infoSet_partition).1 k
    obtain ⟨⟨_, b, hb⟩, -⟩ := (mem_infoSet G).1 hx
    have h1 := G.length_le_sup hb
    have h2 := hd x hx
    simp only [List.length_cons] at h1
    omega
  | succ n ih =>
    intro k hk hd
    -- the continuation after the first move, decomposed at the next nodes of player `i`
    have hT : ∀ b ∈ G.avail k, 0 ≤ ∑ x ∈ G.infoSet k, μ x * ∑ x' ∈ iEntry G i b x,
        reachFrom G f (b :: x) x' * (cont G f x' i - cont G f' x' i) := by
      intro b hb
      have hsub : ∀ x, iEntry G i b x ⊆ Xi := fun x x' hx' => by
        rw [mem_entryNodes] at hx'
        simp only [Xi, Finset.mem_filter, mem_decisionNodes]
        exact ⟨hx'.1, hx'.2.2.1⟩
      have h1 : ∀ x ∈ G.infoSet k, μ x * ∑ x' ∈ iEntry G i b x,
          reachFrom G f (b :: x) x' * (cont G f x' i - cont G f' x' i) =
          ∑ x' ∈ Xi, (if x' ∈ iEntry G i b x then μ x * reachFrom G f (b :: x) x' else 0) *
            (cont G f x' i - cont G f' x' i) := by
        intro x _
        rw [Finset.mul_sum]
        rw [Finset.sum_congr rfl fun x' hx' => by
          rw [show μ x * (reachFrom G f (b :: x) x' * (cont G f x' i - cont G f' x' i)) =
            (if x' ∈ iEntry G i b x then μ x * reachFrom G f (b :: x) x' else 0) *
            (cont G f x' i - cont G f' x' i) by simp only [hx', ↓reduceIte]; ring]]
        exact Finset.sum_subset (hsub x) fun x' _ hx' => by simp [hx']
      rw [Finset.sum_congr rfl h1, Finset.sum_comm]
      simp_rw [← Finset.sum_mul]
      change 0 ≤ ∑ x' ∈ Xi, propW G f μ i k b x' * (cont G f x' i - cont G f' x' i)
      rw [sum_eq_sum_infoSet G (E := Xi)
        (fun x hx => (mem_decisionNodes G).1 (Finset.mem_filter.1 hx).1)
        (fun x hx x' hx' he => by
          simp only [Xi, Finset.mem_filter, mem_decisionNodes] at hx ⊢
          exact ⟨hx', by rw [he]; exact hx.2⟩)]
      refine Finset.sum_nonneg fun k' hk' => ?_
      obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.1 hk'
      have hk'i : G.player (G.info x₀) = some i := (Finset.mem_filter.1 hx₀).2
      obtain ⟨c, hc0, hcμ, hdeep⟩ := propagate_consistent G hPR hN hc hk hb (G.info x₀)
      rw [Finset.sum_congr rfl fun x' hx' => by rw [hcμ x' hx']]
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum]
      by_cases hc' : c = 0
      · rw [hc', zero_mul]
      · refine mul_nonneg hc0 ?_
        have hdepth : ∀ x'' ∈ G.infoSet (G.info x₀), Dm - x''.length ≤ n := by
          intro x'' hx''
          obtain ⟨x, hx, hbx⟩ := hdeep hc' x'' hx''
          have := hd x hx
          have := hbx.length_le
          simp only [List.length_cons] at this
          omega
        have := ih _ hk'i hdepth
        unfold condPayoff at this
        simp_rw [mul_sub]
        rw [Finset.sum_sub_distrib]
        linarith
    have hcf' : ∀ x ∈ G.infoSet k, cont G f' x i = ∑ b ∈ G.avail k, g k b *
        (cont G f (b :: x) i - ∑ x' ∈ iEntry G i b x,
          reachFrom G f (b :: x) x' * (cont G f x' i - cont G f' x' i)) := by
      intro x hx
      obtain ⟨hxd, hxk⟩ := (mem_infoSet G).1 hx
      have hf'k : f' k = g k := assemble_update_self G F g hk
      rw [cont_decision G f' hxd, hxk, hf'k]
      refine Finset.sum_congr rfl fun b hb => ?_
      have hbx : b :: x ∈ G.nodes := G.cons_mem_of_mem_avail hxd (by rw [hxk]; exact hb)
      have := cont_sub_eq_sum_entry G (fun k => G.player k = some i) hoff hbx i
      rw [← this]
      ring
    have hlhs : condPayoff G f' μ k i = ∑ b ∈ G.avail k, g k b *
        (∑ x ∈ G.infoSet k, μ x * cont G f (b :: x) i - ∑ x ∈ G.infoSet k, μ x *
          ∑ x' ∈ iEntry G i b x, reachFrom G f (b :: x) x' * (cont G f x' i - cont G f' x' i)) := by
      unfold condPayoff
      rw [Finset.sum_congr rfl fun x hx => by rw [hcf' x hx, Finset.mul_sum], Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [hlhs]
    calc ∑ b ∈ G.avail k, g k b * (∑ x ∈ G.infoSet k, μ x * cont G f (b :: x) i -
          ∑ x ∈ G.infoSet k, μ x * ∑ x' ∈ iEntry G i b x,
            reachFrom G f (b :: x) x' * (cont G f x' i - cont G f' x' i))
        ≤ ∑ b ∈ G.avail k, g k b * condPayoff G f μ k i :=
          Finset.sum_le_sum fun b hb => mul_le_mul_of_nonneg_left
            (by linarith [hT b hb, hone k hk b hb]) ((hg k hk).1 b)
      _ = condPayoff G f μ k i := by rw [← Finset.sum_mul, (hg k hk).2.2, one_mul]

end MWG.DynamicGames
