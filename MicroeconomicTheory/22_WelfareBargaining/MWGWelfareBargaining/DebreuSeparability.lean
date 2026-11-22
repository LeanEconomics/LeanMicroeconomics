/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGWelfareBargaining.OrdinalClassification
import MWGWelfareBargaining.AczelAssociativity

/-!
# Debreu's separability theorem (MWG, Section 22.D, small type, p. 838)

MWG (p. 838): "a social welfare function for `I > 2` agents that is continuous, increasing, and
independent of irrelevant individuals has, up to an increasing transformation, the additively
separable form `W(u) = ∑ᵢ gᵢ(uᵢ)`". The converse is `additive_independent_irrelevant`.

* `debreu_separability`: for at least three agents, a continuous `W`, strictly increasing in each
  agent's utility, independent of irrelevant individuals and (unrestrictedly) solvable has an
  additive representation `W u ≤ W u' ↔ ∑ gᵢ(uᵢ) ≤ ∑ gᵢ(u'ᵢ)` with every `gᵢ` continuous and
  strictly increasing; `debreu_separability_transform` writes `W = h ∘ ∑ gᵢ` with `h` strictly
  increasing on the range of `∑ gᵢ`.
* `debreu_counterexample_null_agent`: as printed (with MWG's "increasing", which allows an agent
  who never matters) the claim is false for `I = 3`: `W(u) = u₁ + u₂ + min(u₁, u₂)` is
  continuous, increasing and independent of irrelevant individuals, but has no additive
  representation (it violates the Thomsen condition in agents 1 and 2).
* `debreu_fails_two_agents`: why `I > 2` matters: on `ℝ²` the same function satisfies every
  hypothesis of `debreu_separability` except `I > 2` (independence of irrelevant individuals is
  automatic for `I = 2`, `indepIrrelevant_two`), and has no additive representation.

Proof of `debreu_separability` (the route of Debreu and Gorman for `I ≥ 3`). Measure welfare by
the level `L(u)` of agent `i₀` alone (`u ∼ L(u) e_{i₀}`, by solvability), and recalibrate every
agent so that `t eᵢ ∼ t e_{i₀}`. For agents `i ≠ j` let `a ⊕ᵢⱼ b = L(a eᵢ + b eⱼ)`. Independence of
the pair `{i, j}` lets one merge agent `j` into agent `i` (`deb_merge`); merging a three-agent
vector in two orders gives `a ⊕ᵢⱼ (b ⊕ⱼₖ c) = (a ⊕ᵢⱼ b) ⊕ᵢₖ c`, from which all the operations
coincide, are commutative and associative (`debOp_triple`). The common operation is continuous,
strictly increasing and solvable, so `aczel_associativity` gives `g` with
`g(a ⊕ b) = g(a) + g(b)`, and merging all agents into `i₀` shows `g(L(u)) = ∑ g(uᵢ)`.

Departures (see `docs/corrections.md`). The book's "increasing" (MWG p. 825: weakly increasing,
strictly on `≫`) is replaced by strict increase in each agent's utility; the counterexample shows
some essentiality of every agent is needed. Unrestricted solvability (`IsSolvableSWF`: any
welfare level can be reached by changing one agent's utility) is an added hypothesis; Debreu's
theorem without it (each `gᵢ` possibly bounded, e.g. `∑ arctan uᵢ`) needs a local construction
and patching that is not formalized.
-/

namespace MWG.WelfareBargaining

variable {ι : Type*} [DecidableEq ι]

/-- **Section 22.D, small type** (MWG, p. 838), strengthened Paretian property: `W` is strictly
increasing in each agent's utility. -/
def IsStrictlyIncreasingEach (W : (ι → ℝ) → ℝ) : Prop :=
  ∀ (u : ι → ℝ) (i : ι), StrictMono fun t => W (Function.update u i t)

/-- **Section 22.D, small type** (MWG, p. 838), added hypothesis: unrestricted solvability. Any
welfare level `W v` can be reached from any `u` by changing the utility of any one agent. -/
def IsSolvableSWF (W : (ι → ℝ) → ℝ) : Prop :=
  ∀ (i : ι) (u v : ι → ℝ), ∃ t, W (Function.update u i t) = W v

/-- **Section 22.D, small type** (MWG, p. 838). For a continuous `W`, unrestricted solvability
follows when each agent's utility alone can push welfare above and below any level. -/
theorem isSolvableSWF_of_unbounded {W : (ι → ℝ) → ℝ} (hc : Continuous W)
    (hub : ∀ (i : ι) (u : ι → ℝ) (M : ℝ),
      (∃ t, M < W (Function.update u i t)) ∧ ∃ t, W (Function.update u i t) < M) :
    IsSolvableSWF W := by
  intro i u v
  obtain ⟨t₂, ht₂⟩ := (hub i u (W v)).1
  obtain ⟨t₁, ht₁⟩ := (hub i u (W v)).2
  have hf : Continuous fun t => W (Function.update u i t) :=
    hc.comp (continuous_const.update i continuous_id)
  obtain ⟨t, -, ht⟩ := intermediate_value_uIcc (a := t₁) (b := t₂) hf.continuousOn
    (Set.mem_uIcc.2 (Or.inl ⟨ht₁.le, ht₂.le⟩))
  exact ⟨t, ht⟩

/-- The welfare level of `x` measured by agent `i₀` alone: the `s` with `s e_{i₀} ∼ x`. -/
noncomputable def debLevel (W : (ι → ℝ) → ℝ) (i₀ : ι) (x : ι → ℝ) : ℝ := by
  classical
  exact if h : ∃ s, W (Function.update 0 i₀ s) = W x then h.choose else 0

variable {W : (ι → ℝ) → ℝ}

theorem debLevel_spec (hs : IsSolvableSWF W) (i₀ : ι) (x : ι → ℝ) :
    W (Function.update 0 i₀ (debLevel W i₀ x)) = W x := by
  have hex : ∃ s, W (Function.update 0 i₀ s) = W x := hs i₀ 0 x
  unfold debLevel
  simp only [hex, ↓reduceDIte]
  exact hex.choose_spec

theorem debLevel_eq (hm : IsStrictlyIncreasingEach W) (hs : IsSolvableSWF W) {i₀ : ι}
    {x : ι → ℝ} {s : ℝ} (h : W (Function.update 0 i₀ s) = W x) : debLevel W i₀ x = s :=
  (hm 0 i₀).injective ((debLevel_spec hs i₀ x).trans h.symm)

theorem debLevel_le_iff (hm : IsStrictlyIncreasingEach W) (hs : IsSolvableSWF W) (i₀ : ι)
    (x y : ι → ℝ) : W x ≤ W y ↔ debLevel W i₀ x ≤ debLevel W i₀ y := by
  rw [← debLevel_spec hs i₀ x, ← debLevel_spec hs i₀ y]
  exact (hm 0 i₀).le_iff_le

theorem debLevel_lt_iff (hm : IsStrictlyIncreasingEach W) (hs : IsSolvableSWF W) (i₀ : ι)
    (x y : ι → ℝ) : W x < W y ↔ debLevel W i₀ x < debLevel W i₀ y := by
  rw [← debLevel_spec hs i₀ x, ← debLevel_spec hs i₀ y]
  exact (hm 0 i₀).lt_iff_lt

theorem debLevel_congr (hm : IsStrictlyIncreasingEach W) (hs : IsSolvableSWF W) (i₀ : ι)
    {x y : ι → ℝ} (h : W x = W y) : debLevel W i₀ x = debLevel W i₀ y :=
  le_antisymm ((debLevel_le_iff hm hs i₀ x y).1 h.le) ((debLevel_le_iff hm hs i₀ y x).1 h.ge)

open Filter Topology in
theorem debLevel_continuous (hc : Continuous W) (hm : IsStrictlyIncreasingEach W)
    (hs : IsSolvableSWF W) (i₀ : ι) : Continuous (debLevel W i₀) := by
  refine continuous_iff_continuousAt.2 fun x => tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · have h1 : W (Function.update 0 i₀ a) < W x := by
      rw [← debLevel_spec hs i₀ x]
      exact hm 0 i₀ ha
    filter_upwards [(hc.tendsto x).eventually (lt_mem_nhds h1)] with y hy
    rw [← debLevel_spec hs i₀ y] at hy
    exact (hm 0 i₀).lt_iff_lt.1 hy
  · have h1 : W x < W (Function.update 0 i₀ b) := by
      rw [← debLevel_spec hs i₀ x]
      exact hm 0 i₀ hb
    filter_upwards [(hc.tendsto x).eventually (gt_mem_nhds h1)] with y hy
    rw [← debLevel_spec hs i₀ y] at hy
    exact (hm 0 i₀).lt_iff_lt.1 hy

/-- Merging agent `j` into agent `i`: if `(xᵢ, xⱼ)` is as good as `(c, 0)` for the pair alone,
then `x` is as good as `x` with `c` for `i` and `0` for `j` (independence of irrelevant
individuals applied to the group `{i, j}`). -/
theorem deb_merge (hind : IndepIrrelevantIndividuals W) {i j : ι} (hij : i ≠ j) (x : ι → ℝ)
    (c : ℝ) (hc : W (Function.update (Function.update (0 : ι → ℝ) i (x i)) j (x j)) =
      W (Function.update 0 i c)) :
    W x = W (Function.update (Function.update x i c) j 0) := by
  have hin : ∀ k ∈ ({i, j} : Set ι),
      Function.update (Function.update (0 : ι → ℝ) i (x i)) j (x j) k = x k ∧
        Function.update (0 : ι → ℝ) i c k =
          Function.update (Function.update x i c) j 0 k := by
    intro k hk
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk
    rcases hk with rfl | rfl <;> simp [hij, hij.symm]
  have hout : ∀ k ∉ ({i, j} : Set ι),
      Function.update (Function.update (0 : ι → ℝ) i (x i)) j (x j) k =
        Function.update (0 : ι → ℝ) i c k ∧
        x k = Function.update (Function.update x i c) j 0 k := by
    intro k hk
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hk
    simp [hk.1, hk.2]
  have k1 := hind {i, j} _ _ _ _ hin hout
  have k2 := hind {i, j} _ _ _ _ (fun k hk => ⟨(hin k hk).2, (hin k hk).1⟩)
    (fun k hk => ⟨(hout k hk).1.symm, (hout k hk).2.symm⟩)
  exact le_antisymm (k2.1 hc.le) (k1.1 hc.ge)

/-- The operation `a ⊕ᵢⱼ b = L(a eᵢ + b eⱼ)`. -/
noncomputable def debOp (W : (ι → ℝ) → ℝ) (i₀ i j : ι) (a b : ℝ) : ℝ :=
  debLevel W i₀ (Function.update (Function.update (0 : ι → ℝ) i a) j b)

theorem debLevel_single (hm : IsStrictlyIncreasingEach W) (hs : IsSolvableSWF W) {i₀ : ι}
    (hcal : ∀ i t, W (Function.update 0 i t) = W (Function.update 0 i₀ t)) (i : ι) (t : ℝ) :
    debLevel W i₀ (Function.update 0 i t) = t :=
  debLevel_eq hm hs (hcal i t).symm

theorem debOp_merge (hind : IndepIrrelevantIndividuals W)
    (hs : IsSolvableSWF W) {i₀ : ι}
    (hcal : ∀ i t, W (Function.update 0 i t) = W (Function.update 0 i₀ t)) {i j : ι}
    (hij : i ≠ j) (x : ι → ℝ) :
    W x = W (Function.update (Function.update x i (debOp W i₀ i j (x i) (x j))) j 0) :=
  deb_merge hind hij x _ (by rw [hcal, debOp, debLevel_spec hs])

theorem debOp_zero (hm : IsStrictlyIncreasingEach W) (hs : IsSolvableSWF W) {i₀ : ι}
    (hcal : ∀ i t, W (Function.update 0 i t) = W (Function.update 0 i₀ t)) {i j : ι}
    (hij : i ≠ j) (a : ℝ) : debOp W i₀ i j a 0 = a := by
  have e : Function.update (Function.update (0 : ι → ℝ) i a) j 0 =
      Function.update (0 : ι → ℝ) i a := by
    ext k
    simp only [Function.update_apply]
    split_ifs <;> simp_all
  rw [debOp, e, debLevel_single hm hs hcal]

theorem debOp_swap {i₀ i j : ι} (hij : i ≠ j) (a b : ℝ) :
    debOp W i₀ i j a b = debOp W i₀ j i b a := by
  rw [debOp, debOp, Function.update_comm hij]

/-- Merging a three-agent vector in two orders. -/
theorem debOp_triple (hm : IsStrictlyIncreasingEach W) (hind : IndepIrrelevantIndividuals W)
    (hs : IsSolvableSWF W) {i₀ : ι}
    (hcal : ∀ i t, W (Function.update 0 i t) = W (Function.update 0 i₀ t)) {i j k : ι}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (a b c : ℝ) :
    debOp W i₀ i j a (debOp W i₀ j k b c) = debOp W i₀ i k (debOp W i₀ i j a b) c := by
  set x := Function.update (Function.update (Function.update (0 : ι → ℝ) i a) j b) k c
  have xi : x i = a := by simp [x, hij, hik]
  have xj : x j = b := by simp [x, hjk]
  have xk : x k = c := by simp [x]
  have m1 := debOp_merge hind hs hcal hjk x
  have m2 := debOp_merge hind hs hcal hij x
  rw [xj, xk] at m1
  rw [xi, xj] at m2
  have e1 : Function.update (Function.update x j (debOp W i₀ j k b c)) k 0 =
      Function.update (Function.update (0 : ι → ℝ) i a) j (debOp W i₀ j k b c) := by
    ext l
    simp only [x, Function.update_apply]
    split_ifs <;> simp_all
  have e2 : Function.update (Function.update x i (debOp W i₀ i j a b)) j 0 =
      Function.update (Function.update (0 : ι → ℝ) i (debOp W i₀ i j a b)) k c := by
    ext l
    simp only [x, Function.update_apply]
    split_ifs <;> simp_all
  rw [e1] at m1
  rw [e2] at m2
  exact (debLevel_congr hm hs i₀ m1).symm.trans (debLevel_congr hm hs i₀ m2)

theorem debOp_change (hm : IsStrictlyIncreasingEach W) (hind : IndepIrrelevantIndividuals W)
    (hs : IsSolvableSWF W) {i₀ : ι}
    (hcal : ∀ i t, W (Function.update 0 i t) = W (Function.update 0 i₀ t)) {i j k : ι}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (a c : ℝ) :
    debOp W i₀ i j a c = debOp W i₀ i k a c := by
  have t := debOp_triple hm hind hs hcal hij hik hjk a 0 c
  rwa [debOp_swap hjk, debOp_zero hm hs hcal hjk.symm, debOp_zero hm hs hcal hij] at t

theorem continuous_update_update (i j : ι) :
    Continuous fun p : ℝ × ℝ => Function.update (Function.update (0 : ι → ℝ) i p.1) j p.2 :=
  ((continuous_const : Continuous fun _ : ℝ × ℝ => (0 : ι → ℝ)).update i
    continuous_fst).update j continuous_snd

/-- **Debreu's theorem, calibrated form** (MWG, p. 838). If moreover every agent is calibrated
to agent `i₀` (`t eᵢ ∼ t e_{i₀}`), a single `g` represents `W` additively. -/
theorem debreu_calibrated [Fintype ι] (hc : Continuous W) (hm : IsStrictlyIncreasingEach W)
    (hind : IndepIrrelevantIndividuals W) (hs : IsSolvableSWF W) {i₀ j₀ k₀ : ι}
    (h01 : i₀ ≠ j₀) (h02 : i₀ ≠ k₀) (h12 : j₀ ≠ k₀)
    (hcal : ∀ i t, W (Function.update 0 i t) = W (Function.update 0 i₀ t)) :
    ∃ g : ℝ → ℝ, StrictMono g ∧ Continuous g ∧
      ∀ u u' : ι → ℝ, W u ≤ W u' ↔ ∑ i, g (u i) ≤ ∑ i, g (u' i) := by
  set op := debOp W i₀ i₀ j₀ with hop
  have hopi : ∀ i, i ≠ i₀ → debOp W i₀ i₀ i = op := by
    intro i hi
    by_cases hij : i = j₀
    · rw [hij]
    · funext a b
      exact (debOp_change hm hind hs hcal h01 (Ne.symm hi) (Ne.symm hij) a b).symm
  have hcomm : ∀ a b, op a b = op b a := by
    intro a b
    calc debOp W i₀ i₀ j₀ a b = debOp W i₀ j₀ i₀ b a := debOp_swap h01 a b
      _ = debOp W i₀ j₀ k₀ b a := debOp_change hm hind hs hcal h01.symm h12 h02 b a
      _ = debOp W i₀ k₀ j₀ a b := debOp_swap h12 b a
      _ = debOp W i₀ k₀ i₀ a b := debOp_change hm hind hs hcal h12.symm h02.symm h01.symm a b
      _ = debOp W i₀ i₀ k₀ b a := debOp_swap h02.symm a b
      _ = debOp W i₀ i₀ j₀ b a := (debOp_change hm hind hs hcal h01 h02 h12 b a).symm
  have hassoc : ∀ a b c, op (op a b) c = op a (op b c) := by
    intro a b c
    have t := debOp_triple hm hind hs hcal h01 h02 h12 a b c
    rw [debOp_change hm hind hs hcal h12 h01.symm h02.symm,
      debOp_change hm hind hs hcal h02 h01 h12.symm, debOp_swap h01.symm] at t
    rw [← hop, hcomm c b] at t
    exact t.symm
  have hzero : ∀ a, op a 0 = a := debOp_zero hm hs hcal h01
  have hmono : ∀ a, StrictMono (op a) := fun a s t hst =>
    (debLevel_lt_iff hm hs i₀ _ _).1 (hm _ j₀ hst)
  have hsolv : ∀ a c, ∃ b, op a b = c := fun a c => by
    obtain ⟨t, ht⟩ := hs j₀ (Function.update 0 i₀ a) (Function.update 0 i₀ c)
    exact ⟨t, (debLevel_congr hm hs i₀ ht).trans (debLevel_single hm hs hcal i₀ c)⟩
  have hcont : Continuous fun p : ℝ × ℝ => op p.1 p.2 :=
    (debLevel_continuous hc hm hs i₀).comp (continuous_update_update i₀ j₀)
  obtain ⟨g, hgm, hgc, hgadd⟩ := aczel_associativity
    (⟨hcont, hcomm, hassoc, hzero, hmono, hsolv⟩ : IsAczelOp op)
  have hg0 : g 0 = 0 := by
    have := hgadd 0 0
    rw [hzero] at this
    linarith
  have claim : ∀ (s : Finset ι) (x : ι → ℝ), (∀ k, k ∉ s → k ≠ i₀ → x k = 0) →
      g (debLevel W i₀ x) = ∑ k, g (x k) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro x hx
      have e : x = Function.update (0 : ι → ℝ) i₀ (x i₀) := by
        ext k
        by_cases hk : k = i₀
        · subst hk
          simp
        · simp [hk, hx k (Finset.notMem_empty k) hk]
      rw [debLevel_congr hm hs i₀ (congrArg W e), debLevel_single hm hs hcal,
        Finset.sum_eq_single i₀ (fun k _ hk => by rw [hx k (Finset.notMem_empty k) hk, hg0])
          (by simp)]
    | insert j s hj ih =>
      intro x hx
      by_cases hji : j = i₀
      · exact ih x fun k hk hk0 => hx k
          (fun h => (Finset.mem_insert.1 h).elim (fun e => hk0 (e.trans hji)) hk) hk0
      · set x' := Function.update (Function.update x i₀ (op (x i₀) (x j))) j 0 with hx'def
        have hW : W x = W x' := by
          have := debOp_merge hind hs hcal (Ne.symm hji) x
          rwa [hopi j hji] at this
        have hx' : ∀ k, k ∉ s → k ≠ i₀ → x' k = 0 := by
          intro k hk hk0
          by_cases hkj : k = j
          · subst hkj
            simp [x']
          · simp [x', hkj, hk0, hx k (by simp [hkj, hk]) hk0]
        rw [debLevel_congr hm hs i₀ hW, ih x' hx']
        have split : ∀ f : ι → ℝ,
            ∑ k, f k = f i₀ + f j + ∑ k ∈ (Finset.univ.erase i₀).erase j, f k := by
          intro f
          rw [add_assoc, Finset.add_sum_erase _ _ (Finset.mem_erase.2 ⟨hji, Finset.mem_univ j⟩),
            Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
        rw [split (fun k => g (x' k)), split (fun k => g (x k))]
        have e1 : x' i₀ = op (x i₀) (x j) := by simp [x', Ne.symm hji]
        have e2 : x' j = 0 := by simp [x']
        have e3 : ∑ k ∈ (Finset.univ.erase i₀).erase j, g (x' k) =
            ∑ k ∈ (Finset.univ.erase i₀).erase j, g (x k) := Finset.sum_congr rfl fun k hk => by
          simp only [Finset.mem_erase] at hk
          simp [x', hk.1, hk.2.1]
        rw [e1, e2, e3, hgadd, hg0]
        ring
  refine ⟨g, hgm, hgc, fun u u' => ?_⟩
  rw [debLevel_le_iff hm hs i₀, ← hgm.le_iff_le,
    claim Finset.univ u (fun k hk => absurd (Finset.mem_univ k) hk),
    claim Finset.univ u' (fun k hk => absurd (Finset.mem_univ k) hk)]

/-- **Debreu's theorem** (MWG, p. 838, small type; corrected). Let `I ≥ 3` and let the social
welfare function `W` be continuous, strictly increasing in each agent's utility, independent of
irrelevant individuals and unrestrictedly solvable. Then `W` is additively separable up to an
increasing transformation: there are continuous strictly increasing `gᵢ` with
`W(u) ≤ W(u') ↔ ∑ᵢ gᵢ(uᵢ) ≤ ∑ᵢ gᵢ(u'ᵢ)`. -/
theorem debreu_separability [Fintype ι] (hI : 2 < Fintype.card ι) (hc : Continuous W)
    (hm : IsStrictlyIncreasingEach W) (hind : IndepIrrelevantIndividuals W)
    (hs : IsSolvableSWF W) :
    ∃ g : ι → ℝ → ℝ, (∀ i, StrictMono (g i) ∧ Continuous (g i)) ∧
      ∀ u u' : ι → ℝ, W u ≤ W u' ↔ ∑ i, g i (u i) ≤ ∑ i, g i (u' i) := by
  obtain ⟨i₀, j₀, k₀, h01, h02, h12⟩ := Fintype.two_lt_card_iff.1 hI
  set σ : ι → ℝ → ℝ := fun i t => debLevel W i₀ (Function.update 0 i t) with hσ
  have hσm : ∀ i, StrictMono (σ i) := fun i s t hst =>
    (debLevel_lt_iff hm hs i₀ _ _).1 (hm 0 i hst)
  have hσs : ∀ i, Function.Surjective (σ i) := fun i s => by
    obtain ⟨t, ht⟩ := hs i 0 (Function.update 0 i₀ s)
    exact ⟨t, debLevel_eq hm hs ht.symm⟩
  set iso : ι → ℝ ≃o ℝ := fun i => (hσm i).orderIsoOfSurjective (σ i) (hσs i)
  set τ : ι → ℝ ≃o ℝ := fun i => (iso i).symm
  have hστ : ∀ i t, σ i (τ i t) = t := fun i t => (iso i).apply_symm_apply t
  have hτσ : ∀ i t, τ i (σ i t) = t := fun i t => (iso i).symm_apply_apply t
  have hz : ∀ i, Function.update (0 : ι → ℝ) i 0 = 0 := fun i => by
    ext k
    simp [Function.update_apply]
  have hσ0 : ∀ i, σ i 0 = 0 := fun i => by
    simp only [σ, hz]
    exact debLevel_eq hm hs (by rw [hz])
  have hτ0 : ∀ i, τ i 0 = 0 := fun i => by
    calc τ i 0 = τ i (σ i 0) := by rw [hσ0]
      _ = 0 := hτσ i 0
  have hσi₀ : ∀ t, σ i₀ t = t := fun t => debLevel_eq hm hs rfl
  have hτi₀ : ∀ t, τ i₀ t = t := fun t => by
    calc τ i₀ t = τ i₀ (σ i₀ t) := by rw [hσi₀]
      _ = t := hτσ _ _
  set W' : (ι → ℝ) → ℝ := fun y => W fun i => τ i (y i) with hW'
  have hupd : ∀ (y : ι → ℝ) (i : ι) (t : ℝ), (fun k => τ k (Function.update y i t k)) =
      Function.update (fun k => τ k (y k)) i (τ i t) := by
    intro y i t
    ext k
    by_cases hk : k = i
    · subst hk
      simp
    · simp [hk]
  have hc' : Continuous W' :=
    hc.comp (continuous_pi fun i => (τ i).continuous.comp (continuous_apply i))
  have hm' : IsStrictlyIncreasingEach W' := fun y i s t hst => by
    simp only [hW', hupd]
    exact hm _ i ((τ i).strictMono hst)
  have hind' : IndepIrrelevantIndividuals W' := fun S a b c d h1 h2 =>
    hind S _ _ _ _ (fun i hi => ⟨by simp only [(h1 i hi).1], by simp only [(h1 i hi).2]⟩)
      (fun i hi => ⟨by simp only [(h2 i hi).1], by simp only [(h2 i hi).2]⟩)
  have hs' : IsSolvableSWF W' := fun i y v => by
    obtain ⟨t, ht⟩ := hs i (fun k => τ k (y k)) (fun k => τ k (v k))
    refine ⟨σ i t, ?_⟩
    simp only [hW', hupd, hτσ]
    exact ht
  have h0τ : (fun k => τ k ((0 : ι → ℝ) k)) = 0 := by
    ext k
    simp [hτ0]
  have hcal' : ∀ i t, W' (Function.update 0 i t) = W' (Function.update 0 i₀ t) := by
    intro i t
    simp only [hW', hupd, h0τ, hτi₀]
    have := debLevel_spec hs i₀ (Function.update 0 i (τ i t))
    rw [show debLevel W i₀ (Function.update 0 i (τ i t)) = t from hστ i t] at this
    exact this.symm
  obtain ⟨g, hgm, hgc, hrep⟩ := debreu_calibrated hc' hm' hind' hs' h01 h02 h12 hcal'
  refine ⟨fun i t => g (σ i t), fun i => ⟨hgm.comp (hσm i), hgc.comp (iso i).continuous⟩,
    fun u u' => ?_⟩
  have e : ∀ v : ι → ℝ, W v = W' fun i => σ i (v i) := fun v => by
    simp only [hW', hτσ]
  rw [e u, e u']
  exact hrep _ _

/-- **Debreu's theorem, transformation form** (MWG, p. 838). Under the hypotheses of
`debreu_separability`, `W(u) = h(∑ᵢ gᵢ(uᵢ))` with `h` strictly increasing on the range of
`∑ᵢ gᵢ`. -/
theorem debreu_separability_transform [Fintype ι] (hI : 2 < Fintype.card ι)
    (hc : Continuous W) (hm : IsStrictlyIncreasingEach W) (hind : IndepIrrelevantIndividuals W)
    (hs : IsSolvableSWF W) :
    ∃ (g : ι → ℝ → ℝ) (h : ℝ → ℝ), (∀ i, StrictMono (g i) ∧ Continuous (g i)) ∧
      StrictMonoOn h (Set.range fun u : ι → ℝ => ∑ i, g i (u i)) ∧
      ∀ u, W u = h (∑ i, g i (u i)) := by
  classical
  obtain ⟨g, hg, hrep⟩ := debreu_separability hI hc hm hind hs
  set h : ℝ → ℝ := fun s => if hs : ∃ u : ι → ℝ, ∑ i, g i (u i) = s then W hs.choose else 0
  have key : ∀ u, h (∑ i, g i (u i)) = W u := by
    intro u
    have hex : ∃ v : ι → ℝ, ∑ i, g i (v i) = ∑ i, g i (u i) := ⟨u, rfl⟩
    simp only [h, hex, ↓reduceDIte]
    exact le_antisymm ((hrep _ _).2 hex.choose_spec.le) ((hrep _ _).2 hex.choose_spec.ge)
  refine ⟨g, h, hg, ?_, fun u => (key u).symm⟩
  rintro _ ⟨u, rfl⟩ _ ⟨u', rfl⟩ hlt
  simp only [key]
  exact lt_of_not_ge fun hle => absurd ((hrep _ _).1 hle) (not_le.2 hlt)

/-- The hypotheses of `debreu_calibrated` and `debreu_separability` hold for the utilitarian
`W(u) = ∑ᵢ uᵢ` (calibrated to any agent). -/
theorem debreu_hypotheses_utilitarian [Fintype ι] (i₀ : ι) :
    Continuous (fun u : ι → ℝ => ∑ i, u i) ∧
      IsStrictlyIncreasingEach (fun u : ι → ℝ => ∑ i, u i) ∧
      IndepIrrelevantIndividuals (fun u : ι → ℝ => ∑ i, u i) ∧
      IsSolvableSWF (fun u : ι → ℝ => ∑ i, u i) ∧
      ∀ i t, ∑ k, Function.update (0 : ι → ℝ) i t k = ∑ k, Function.update (0 : ι → ℝ) i₀ t k := by
  have hsum : ∀ (u : ι → ℝ) i t, ∑ k, Function.update u i t k =
      t + (∑ k, u k - u i) := by
    intro u i t
    rw [Finset.sum_update_of_mem (Finset.mem_univ i),
      Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ i) u]
    ring
  refine ⟨continuous_finsetSum _ fun i _ => continuous_apply i, fun u i s t hst => ?_,
    additive_independent_irrelevant (fun _ t => t), fun i u v => ⟨u i + (∑ k, v k - ∑ k, u k),
      ?_⟩, fun i t => ?_⟩
  · simp only [hsum]
    linarith
  · simp only [hsum]
    ring
  · simp [hsum]

/-- The hypothesis of `isSolvableSWF_of_unbounded` holds for the utilitarian `W(u) = ∑ᵢ uᵢ`. -/
theorem unbounded_utilitarian [Fintype ι] (i : ι) (u : ι → ℝ) (M : ℝ) :
    (∃ t, M < ∑ k, Function.update u i t k) ∧ ∃ t, ∑ k, Function.update u i t k < M := by
  have hsum : ∀ t, ∑ k, Function.update u i t k = t + (∑ k, u k - u i) := by
    intro t
    rw [Finset.sum_update_of_mem (Finset.mem_univ i),
      Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ i) u]
    ring
  refine ⟨⟨M - (∑ k, u k - u i) + 1, ?_⟩, ⟨M - (∑ k, u k - u i) - 1, ?_⟩⟩ <;>
    rw [hsum] <;> linarith

/-! ### Why the hypotheses matter -/

/-- If `a` and `b` differ only in agent `i`, a `W` strictly increasing in each agent's utility
ranks them as agent `i` does. -/
theorem le_iff_of_eq_off {W : (ι → ℝ) → ℝ} (hm : IsStrictlyIncreasingEach W) {i : ι}
    {a b : ι → ℝ} (hab : ∀ k, k ≠ i → a k = b k) : W b ≤ W a ↔ b i ≤ a i := by
  have eb : b = Function.update a i (b i) := by
    ext k
    by_cases hk : k = i
    · subst hk
      simp
    · simp [hk, hab k hk]
  calc W b ≤ W a ↔ W (Function.update a i (b i)) ≤ W (Function.update a i (a i)) := by
        rw [← eb, Function.update_eq_self]
    _ ↔ b i ≤ a i := (hm a i).le_iff_le

theorem fin_two_eq_one {k : Fin 2} (hk : k ≠ 0) : k = 1 := by
  fin_cases k
  · exact absurd rfl hk
  · rfl

theorem fin_two_eq_zero {k : Fin 2} (hk : k ≠ 1) : k = 0 := by
  fin_cases k
  · rfl
  · exact absurd rfl hk

/-- **Section 22.D, small type** (MWG, p. 838). With two agents, independence of irrelevant
individuals is automatic for a `W` strictly increasing in each agent's utility. -/
theorem indepIrrelevant_two {W : (Fin 2 → ℝ) → ℝ} (hm : IsStrictlyIncreasingEach W) :
    IndepIrrelevantIndividuals W := by
  intro S a b c d hin hout
  by_cases h0 : (0 : Fin 2) ∈ S <;> by_cases h1 : (1 : Fin 2) ∈ S
  · have ea : a = c := by
      ext k
      fin_cases k
      exacts [(hin 0 h0).1, (hin 1 h1).1]
    have eb : b = d := by
      ext k
      fin_cases k
      exacts [(hin 0 h0).2, (hin 1 h1).2]
    rw [ea, eb]
  · rw [le_iff_of_eq_off hm (i := 0) fun k hk => (fin_two_eq_one hk ▸ (hout 1 h1).1),
      le_iff_of_eq_off hm (i := 0) fun k hk => (fin_two_eq_one hk ▸ (hout 1 h1).2),
      (hin 0 h0).1, (hin 0 h0).2]
  · rw [le_iff_of_eq_off hm (i := 1) fun k hk => (fin_two_eq_zero hk ▸ (hout 0 h0).1),
      le_iff_of_eq_off hm (i := 1) fun k hk => (fin_two_eq_zero hk ▸ (hout 0 h0).2),
      (hin 1 h1).1, (hin 1 h1).2]
  · have ea : a = b := by
      ext k
      fin_cases k
      exacts [(hout 0 h0).1, (hout 1 h1).1]
    have ec : c = d := by
      ext k
      fin_cases k
      exacts [(hout 0 h0).2, (hout 1 h1).2]
    rw [ea, ec]
    exact iff_of_true le_rfl le_rfl

/-- The two-agent social welfare function `W(u) = u₁ + u₂ + min(u₁, u₂)`. -/
noncomputable def thomsenSWF (u : Fin 2 → ℝ) : ℝ := u 0 + u 1 + min (u 0) (u 1)

/-- `thomsenSWF` has no additive representation: `(0, 3) ∼ (1, 1)` and `(1, 5) ∼ (2, 3)` but
`(0, 5) ≻ (2, 1)`, against the Thomsen condition. -/
theorem thomsenSWF_not_additive :
    ¬∃ g : Fin 2 → ℝ → ℝ, ∀ u u' : Fin 2 → ℝ,
      thomsenSWF u ≤ thomsenSWF u' ↔ ∑ i, g i (u i) ≤ ∑ i, g i (u' i) := by
  rintro ⟨g, hg⟩
  have h1 := (hg ![1, 1] ![0, 3]).1 (by norm_num [thomsenSWF, min_def])
  have h2 := (hg ![0, 3] ![1, 1]).1 (by norm_num [thomsenSWF, min_def])
  have h3 := (hg ![2, 3] ![1, 5]).1 (by norm_num [thomsenSWF, min_def])
  have h4 := (hg ![1, 5] ![2, 3]).1 (by norm_num [thomsenSWF, min_def])
  have h5 := mt (hg ![0, 5] ![2, 1]).2 (by norm_num [thomsenSWF, min_def])
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h1 h2 h3 h4 h5
  linarith

theorem thomsenSWF_strict : IsStrictlyIncreasingEach thomsenSWF := by
  intro u i s t hst
  fin_cases i
  · have := min_le_min_right (u 1) hst.le
    simp only [thomsenSWF]
    simp
    linarith
  · have := min_le_min_left (u 0) hst.le
    simp only [thomsenSWF]
    simp
    linarith

theorem thomsenSWF_solvable : IsSolvableSWF thomsenSWF := by
  intro i u v
  set c := thomsenSWF v
  fin_cases i
  · refine ⟨if c ≤ 3 * u 1 then (c - u 1) / 2 else c - 2 * u 1, ?_⟩
    simp only [thomsenSWF, Fin.zero_eta, Fin.isValue, Function.update_self, ne_eq, one_ne_zero,
      not_false_eq_true, Function.update_of_ne]
    split_ifs with h
    · rw [min_eq_left (by linarith)]
      ring
    · rw [min_eq_right (by linarith)]
      ring
  · refine ⟨if c ≤ 3 * u 0 then (c - u 0) / 2 else c - 2 * u 0, ?_⟩
    simp only [thomsenSWF, Fin.mk_one, Fin.isValue, ne_eq, zero_ne_one, not_false_eq_true,
      Function.update_of_ne, Function.update_self]
    split_ifs with h
    · rw [min_eq_right (by linarith)]
      ring
    · rw [min_eq_left (by linarith)]
      ring

/-- **Section 22.D, small type** (MWG, p. 838): why `I > 2` matters. With two agents,
`W(u) = u₁ + u₂ + min(u₁, u₂)` is continuous, strictly increasing in each agent's utility,
solvable and (automatically) independent of irrelevant individuals, but no functions `gᵢ`
whatever give `W(u) ≤ W(u') ↔ ∑ gᵢ(uᵢ) ≤ ∑ gᵢ(u'ᵢ)`. -/
theorem debreu_fails_two_agents :
    Continuous thomsenSWF ∧ IsStrictlyIncreasingEach thomsenSWF ∧
      IndepIrrelevantIndividuals thomsenSWF ∧ IsSolvableSWF thomsenSWF ∧
      ¬∃ g : Fin 2 → ℝ → ℝ, ∀ u u' : Fin 2 → ℝ,
        thomsenSWF u ≤ thomsenSWF u' ↔ ∑ i, g i (u i) ≤ ∑ i, g i (u' i) :=
  ⟨((continuous_apply 0).add (continuous_apply 1)).add
      ((continuous_apply 0).min (continuous_apply 1)),
    thomsenSWF_strict, indepIrrelevant_two thomsenSWF_strict, thomsenSWF_solvable,
    thomsenSWF_not_additive⟩

/-- The three-agent social welfare function `W(u) = u₁ + u₂ + min(u₁, u₂)` (agent 3 never
matters). -/
noncomputable def nullAgentSWF (u : Fin 3 → ℝ) : ℝ := u 0 + u 1 + min (u 0) (u 1)

theorem nullAgentSWF_eq (u : Fin 3 → ℝ) :
    nullAgentSWF u = thomsenSWF fun k => u (Fin.castSucc k) := rfl

/-- **Section 22.D, small type** (MWG, p. 838): the claim as printed is false. For `I = 3`,
`W(u) = u₁ + u₂ + min(u₁, u₂)` is continuous, increasing in MWG's sense (p. 825: weakly
increasing, strictly increasing on `≫`) and independent of irrelevant individuals, but no
functions `gᵢ` give `W(u) ≤ W(u') ↔ ∑ gᵢ(uᵢ) ≤ ∑ gᵢ(u'ᵢ)`. Debreu's theorem needs every agent
to matter (here: strict increase in each agent's utility). -/
theorem debreu_counterexample_null_agent :
    Continuous nullAgentSWF ∧ IsIncreasingSWF nullAgentSWF ∧
      IndepIrrelevantIndividuals nullAgentSWF ∧
      ¬∃ g : Fin 3 → ℝ → ℝ, ∀ u u' : Fin 3 → ℝ,
        nullAgentSWF u ≤ nullAgentSWF u' ↔ ∑ i, g i (u i) ≤ ∑ i, g i (u' i) := by
  refine ⟨((continuous_apply 0).add (continuous_apply 1)).add
      ((continuous_apply 0).min (continuous_apply 1)),
    ⟨fun u u' h => ?_, fun u u' h => ?_⟩, fun S a b c d hin hout => ?_, ?_⟩
  · have := min_le_min (h 0) (h 1)
    simp only [nullAgentSWF]
    linarith [h 0, h 1]
  · have := min_lt_min (h 0) (h 1)
    simp only [nullAgentSWF]
    linarith [h 0, h 1]
  · simp only [nullAgentSWF_eq]
    exact indepIrrelevant_two thomsenSWF_strict (Fin.castSucc ⁻¹' S) _ _ _ _
      (fun k hk => hin _ hk) (fun k hk => hout _ hk)
  · rintro ⟨g, hg⟩
    have h1 := (hg ![1, 1, 0] ![0, 3, 0]).1 (by norm_num [nullAgentSWF, min_def])
    have h2 := (hg ![0, 3, 0] ![1, 1, 0]).1 (by norm_num [nullAgentSWF, min_def])
    have h3 := (hg ![2, 3, 0] ![1, 5, 0]).1 (by norm_num [nullAgentSWF, min_def])
    have h4 := (hg ![1, 5, 0] ![2, 3, 0]).1 (by norm_num [nullAgentSWF, min_def])
    have h5 := mt (hg ![0, 5, 0] ![2, 1, 0]).2 (by norm_num [nullAgentSWF, min_def])
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two] at h1 h2 h3 h4 h5
    linarith

end MWG.WelfareBargaining
