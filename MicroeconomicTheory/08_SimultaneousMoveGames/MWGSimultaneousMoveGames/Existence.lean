/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGSimultaneousMoveGames.MixedStrategies
import MWGSimultaneousMoveGames.AppendixMI
import Mathlib.Analysis.Convex.Quasiconvex
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Topology.Order.Compact

/-!
# Existence of Nash equilibrium

MWG, Section 8.D (pp. 252-253) and Appendix A of Chapter 8 (pp. 260-261).

The strategy sets are subsets `S_i` of real normed spaces `E_i` (MWG: Euclidean spaces
`ℝ^{M_i}`, which are instances; `proposition_8_D_3` is the Euclidean statement) and the
payoffs are functions `u_i` on profiles in `∏_i E_i`. The best-response correspondence
`b_i(s_{-i})` is `bestResp u S i s` (the `i`-th coordinate of `s` is ignored).

* **Lemma 8.AA.1** (`lemma_8_AA_1`): nonempty compact convex `S_i` and `u_i` continuous and
  quasiconcave in `s_i` make `b_i` nonempty, convex-valued and upper hemicontinuous
  (Definition M.H.3, `UpperHemicontinuousMWG`).
* **Proposition 8.D.3** (`nash_exists_of_quasiconcave`, `proposition_8_D_3`): the proof of
  p. 261, applying Kakutani's theorem (`kakutani_mwg`, Theorem M.I.2) to
  `b(s) = b_1(s_{-1}) × ⋯ × b_I(s_{-I})`. The equilibrium is a Nash equilibrium of the normal
  form `[I, {S_i}, {u_i}]` (`restrictGame`, `isNashEquilibrium_restrictGame`).
* **Proposition 8.D.2** (`proposition_8_D_2`): with finitely many pure strategies, a mixed
  strategy Nash equilibrium exists; as on p. 261 it is Proposition 8.D.3 for the game with
  strategy sets `Δ(S_i)` and the multilinear payoffs `u_i(σ)`. The strategy sets must be
  nonempty (`no_mixedProfile_of_isEmpty`, correction 2).
* **Footnote 5** (p. 253): a finite strategy set is convex only if it has at most one element
  (`footnote_8_5`), so a singleton is the exception to the printed claim (correction 3).
-/

namespace MWG.SimultaneousMoveGames

open MWG.NoncooperativeGames MWG.ClassicalDemand Function Filter Topology

variable {I : Type*} [Fintype I] [DecidableEq I] {E : I → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]

/-- **Section 8.D** (MWG, p. 247), for strategy sets `S_i ⊆ E_i`: player `i`'s best responses
`b_i(s_{-i}) = {t ∈ S_i : u_i(t, s_{-i}) ≥ u_i(t', s_{-i}) for all t' ∈ S_i}`. -/
def bestResp (u : I → ((i : I) → E i) → ℝ) (S : (i : I) → Set (E i)) (i : I)
    (s : (i : I) → E i) : Set (E i) :=
  {t | t ∈ S i ∧ ∀ t' ∈ S i, u i (update s i t') ≤ u i (update s i t)}

omit [Fintype I] [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)] in
/-- Replacing a coordinate of a profile in `∏ S_j` by a point of `S_i` stays in `∏ S_j`. -/
theorem update_mem_pi {S : (i : I) → Set (E i)} {s : (i : I) → E i}
    (hs : s ∈ Set.pi Set.univ S) (i : I) {t : E i} (ht : t ∈ S i) :
    update s i t ∈ Set.pi Set.univ S := by
  intro j _
  by_cases hj : j = i
  · subst hj; simpa using ht
  · simpa [update_of_ne hj] using hs j (Set.mem_univ j)

/-- **Lemma 8.AA.1** (MWG, p. 260). If the sets `S_j` are nonempty, `S_i` is compact and
convex, and `u_i` is continuous on `S = S_1 × ⋯ × S_I` and quasiconcave in `s_i`, then player
`i`'s best-response correspondence is nonempty, convex-valued and upper hemicontinuous. -/
theorem lemma_8_AA_1 {u : I → ((i : I) → E i) → ℝ} {S : (i : I) → Set (E i)} (i : I)
    (hSne : ∀ j, (S j).Nonempty) (hcpt : IsCompact (S i)) (_hconv : Convex ℝ (S i))
    (hcont : ContinuousOn (u i) (Set.pi Set.univ S))
    (hqc : ∀ s ∈ Set.pi Set.univ S, QuasiconcaveOn ℝ (S i) fun t => u i (update s i t)) :
    (∀ s ∈ Set.pi Set.univ S, (bestResp u S i s).Nonempty) ∧
      (∀ s ∈ Set.pi Set.univ S, Convex ℝ (bestResp u S i s)) ∧
      UpperHemicontinuousMWG (Set.pi Set.univ S) (bestResp u S i) := by
  have hcomp : ∀ s ∈ Set.pi Set.univ S, ContinuousOn (fun t => u i (update s i t)) (S i) :=
    fun s hs => hcont.comp (continuous_const.update i continuous_id).continuousOn
      fun t ht => update_mem_pi hs i ht
  refine ⟨fun s hs => ?_, fun s hs => ?_, ?_, ?_⟩
  · -- the set of maximizers of a continuous function on a compact set is nonempty
    obtain ⟨t, ht, hmax⟩ := hcpt.exists_isMaxOn (hSne i) (hcomp s hs)
    exact ⟨t, ht, fun t' ht' => hmax ht'⟩
  · -- the maximizers of a quasiconcave function on a convex set form an upper level set
    obtain ⟨t₀, ht₀, hmax⟩ := hcpt.exists_isMaxOn (hSne i) (hcomp s hs)
    have heq : bestResp u S i s = {t | t ∈ S i ∧ u i (update s i t₀) ≤ u i (update s i t)} := by
      ext t
      constructor
      · rintro ⟨ht, hbr⟩; exact ⟨ht, hbr t₀ ht₀⟩
      · rintro ⟨ht, hge⟩; exact ⟨ht, fun t' ht' => (hmax ht').trans hge⟩
    rw [heq]
    exact hqc s hs _
  · -- closed graph: pass to the limit in `u_i(sⁿ_i, sⁿ_{-i}) ≥ u_i(s'_i, sⁿ_{-i})`
    intro xs ys x y hxs hx hys hxl hyl
    have hyS : y ∈ S i :=
      hcpt.isClosed.mem_of_tendsto hyl (Eventually.of_forall fun n => (hys n).1)
    refine ⟨hyS, fun t' ht' => ?_⟩
    have h1 : Tendsto (fun n => update (xs n) i t') atTop (𝓝 (update x i t')) :=
      ((continuous_id.update i continuous_const).tendsto x).comp hxl
    have h2 : Tendsto (fun n => update (xs n) i (ys n)) atTop (𝓝 (update x i y)) :=
      ((continuous_fst.update i continuous_snd).tendsto (x, y)).comp (hxl.prodMk_nhds hyl)
    have hc1 := ((hcont _ (update_mem_pi hx i ht')).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨h1, Eventually.of_forall fun n => update_mem_pi (hxs n) i ht'⟩))
    have hc2 := ((hcont _ (update_mem_pi hx i hyS)).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨h2, Eventually.of_forall fun n =>
        update_mem_pi (hxs n) i (hys n).1⟩))
    exact le_of_tendsto_of_tendsto' hc1 hc2 fun n => (hys n).2 t' ht'
  · -- images lie in the compact, hence bounded, set `S_i`
    intro B _ _
    exact hcpt.isBounded.subset (Set.iUnion₂_subset fun x _ t ht => ht.1)

omit [Fintype I] in
/-- **Proposition 8.D.3 in real normed spaces** (MWG, pp. 253 and 261). If every `S_i` is a
nonempty, convex and compact subset of a real normed space and every `u_i` is continuous on
`S_1 × ⋯ × S_I` and quasiconcave in `s_i`, there is a profile `s ∈ S` with
`u_i(s_i, s_{-i}) ≥ u_i(s_i', s_{-i})` for all `s_i' ∈ S_i` and all `i`. -/
theorem nash_exists_of_quasiconcave [Finite I] {u : I → ((i : I) → E i) → ℝ}
    {S : (i : I) → Set (E i)}
    (hSne : ∀ i, (S i).Nonempty) (hcpt : ∀ i, IsCompact (S i)) (hconv : ∀ i, Convex ℝ (S i))
    (hcont : ∀ i, ContinuousOn (u i) (Set.pi Set.univ S))
    (hqc : ∀ i, ∀ s ∈ Set.pi Set.univ S, QuasiconcaveOn ℝ (S i) fun t => u i (update s i t)) :
    ∃ s ∈ Set.pi Set.univ S, ∀ i, ∀ t ∈ S i, u i (update s i t) ≤ u i s := by
  have := Fintype.ofFinite I
  have hL := fun i => lemma_8_AA_1 i hSne (hcpt i) (hconv i) (hcont i) (hqc i)
  set K : Set ((i : I) → E i) := Set.pi Set.univ S
  set F : ((i : I) → E i) → Set ((i : I) → E i) :=
    fun s => Set.pi Set.univ fun i => bestResp u S i s
  have hKc : IsCompact K := isCompact_univ_pi hcpt
  have hFK : CorrMapsInto K K F := fun s _ t ht i _ => (ht i (Set.mem_univ i)).1
  have huhc : UpperHemicontinuousMWG K F := by
    refine ⟨fun xs ys x y hxs hx hys hxl hyl i _ => ?_, fun B hBK _ => ?_⟩
    · exact (hL i).2.2.1 xs (fun n => ys n i) x (y i) hxs hx (fun n => hys n i (Set.mem_univ i))
        hxl ((continuous_apply i).tendsto y |>.comp hyl)
    · exact hKc.isBounded.subset (Set.iUnion₂_subset fun x hx => hFK x (hBK hx))
  obtain ⟨s, hs, hsF⟩ := kakutani_mwg (Set.univ_pi_nonempty_iff.2 hSne) hKc
    (convex_pi fun i _ => hconv i) huhc hFK
    (fun s hs => Set.univ_pi_nonempty_iff.2 fun i => (hL i).1 s hs)
    (fun s hs => convex_pi fun i _ => (hL i).2.1 s hs)
  refine ⟨s, hs, fun i t ht => ?_⟩
  have := (hsF i (Set.mem_univ i)).2 t ht
  rwa [update_eq_self] at this

omit [Fintype I] in
/-- **Proposition 8.D.3** (MWG, p. 253). A Nash equilibrium exists in `Γ_N = [I, {S_i}, {u_i}]`
if for every `i`, (i) `S_i` is a nonempty, convex and compact subset of a Euclidean space
`ℝ^{M_i}`, and (ii) `u_i(s_1, …, s_I)` is continuous in `(s_1, …, s_I)` and quasiconcave in
`s_i`. -/
theorem proposition_8_D_3 [Finite I] {M : I → ℕ} {u : I → ((i : I) → Fin (M i) → ℝ) → ℝ}
    {S : (i : I) → Set (Fin (M i) → ℝ)} (hSne : ∀ i, (S i).Nonempty)
    (hconv : ∀ i, Convex ℝ (S i)) (hcpt : ∀ i, IsCompact (S i))
    (hcont : ∀ i, ContinuousOn (u i) (Set.pi Set.univ S))
    (hqc : ∀ i, ∀ s ∈ Set.pi Set.univ S, QuasiconcaveOn ℝ (S i) fun t => u i (update s i t)) :
    ∃ s ∈ Set.pi Set.univ S, ∀ i, ∀ t ∈ S i, u i (update s i t) ≤ u i s :=
  nash_exists_of_quasiconcave hSne hcpt hconv hcont hqc

/-- The normal form `[I, {S_i}, {u_i(·)}]` whose strategy sets are the subsets `S_i ⊆ E_i`. -/
def restrictGame (u : I → ((i : I) → E i) → ℝ) (S : (i : I) → Set (E i)) :
    NormalForm I (fun i => S i) where
  payoff i s := u i fun j => (s j : E j)

omit [Fintype I] [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)] in
/-- A profile as in Proposition 8.D.3 is a Nash equilibrium (Definition 8.D.1) of the normal form
`[I, {S_i}, {u_i(·)}]`. -/
theorem isNashEquilibrium_restrictGame {u : I → ((i : I) → E i) → ℝ}
    {S : (i : I) → Set (E i)} {s : (i : I) → E i} (hs : s ∈ Set.pi Set.univ S)
    (hne : ∀ i, ∀ t ∈ S i, u i (update s i t) ≤ u i s) :
    IsNashEquilibrium (restrictGame u S) (fun i => ⟨s i, hs i (Set.mem_univ i)⟩) := by
  intro i t
  have hval : (fun j => ((update (fun i => (⟨s i, hs i (Set.mem_univ i)⟩ : S i)) i t j : S j) :
      E j)) = update s i (t : E i) := by
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [update_of_ne hj]
  simp only [restrictGame]
  rw [hval]
  exact hne i t t.2

/-- The hypotheses of Proposition 8.D.3 are satisfiable: one player choosing `x ∈ [0, 1]` with
payoff `x`. -/
theorem proposition_8_D_3_instance :
    let S : (i : Unit) → Set (Fin 1 → ℝ) := fun _ => Set.pi Set.univ fun _ => Set.Icc 0 1
    let u : Unit → ((i : Unit) → Fin 1 → ℝ) → ℝ := fun _ s => s () 0
    (∀ i, (S i).Nonempty) ∧ (∀ i, Convex ℝ (S i)) ∧ (∀ i, IsCompact (S i)) ∧
      (∀ i, ContinuousOn (u i) (Set.pi Set.univ S)) ∧
      ∀ i, ∀ s ∈ Set.pi Set.univ S, QuasiconcaveOn ℝ (S i) fun t => u i (update s i t) := by
  intro S u
  refine ⟨fun _ => ⟨0, fun k _ => by simp⟩, fun _ => convex_pi fun _ _ => convex_Icc 0 1,
    fun _ => isCompact_univ_pi fun _ => isCompact_Icc,
    fun _ => ((continuous_apply 0).comp (continuous_apply ())).continuousOn,
    fun i s _ => ?_⟩
  have h : (fun t : Fin 1 → ℝ => u i (update s i t)) = fun t => t 0 := by
    funext t
    simp [u]
  rw [h]
  exact (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).concaveOn
    (convex_pi fun _ _ => convex_Icc 0 1) |>.quasiconcaveOn

/-! ### Proposition 8.D.2 -/

variable {S : I → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]

omit [∀ i, DecidableEq (S i)] in
/-- The mixed payoff is continuous in the mixed profile. -/
theorem continuous_mixedPayoff (N : NormalForm I S) (k : I) :
    Continuous fun σ : (i : I) → S i → ℝ => N.mixedPayoff σ k := by
  unfold NormalForm.mixedPayoff
  refine continuous_finsetSum _ fun s _ => ?_
  refine Continuous.mul (continuous_finsetProd _ fun j _ => ?_) continuous_const
  exact (continuous_apply (s j)).comp (continuous_apply j)

omit [∀ i, DecidableEq (S i)] in
/-- A player's mixed payoff is affine, hence concave, in his own mixed strategy. -/
theorem concaveOn_mixedPayoff_update (N : NormalForm I S) (σ : (i : I) → S i → ℝ) (i : I)
    {K : Set (S i → ℝ)} (hK : Convex ℝ K) :
    ConcaveOn ℝ K fun τ => N.mixedPayoff (update σ i τ) i := by
  refine ⟨hK, fun x _ y _ a b _ _ _ => le_of_eq ?_⟩
  simp only [mixedPayoff_update, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  ring

omit [Fintype I] [DecidableEq I] [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] in
/-- The set `Δ(T)` of mixed strategies is convex. -/
theorem convex_mixedExtension (T : Type*) [Fintype T] : Convex ℝ (mixedExtension T) := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun t => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [hx.1 t, hy.1 t]
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hx.2, hy.2, mul_one, hab]

omit [Fintype I] [DecidableEq I] [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] in
/-- The set `Δ(T)` of mixed strategies is compact. -/
theorem isCompact_mixedExtension (T : Type*) [Fintype T] : IsCompact (mixedExtension T) := by
  have hcube : IsCompact (Set.pi Set.univ fun _ : T => Set.Icc (0 : ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  refine hcube.of_isClosed_subset ?_ fun σ hσ t _ => ⟨hσ.1 t, ?_⟩
  · have h1 : IsClosed {σ : T → ℝ | ∀ t, 0 ≤ σ t} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun t => isClosed_le continuous_const (continuous_apply t)
    have h2 : IsClosed {σ : T → ℝ | ∑ t, σ t = 1} :=
      isClosed_eq (continuous_finsetSum _ fun t _ => continuous_apply t) continuous_const
    exact h1.inter h2
  · rw [← hσ.2]
    exact Finset.single_le_sum (fun t _ => hσ.1 t) (Finset.mem_univ t)

omit [∀ i, DecidableEq (S i)] in
/-- **Proposition 8.D.2** (MWG, pp. 252 and 261). Every game `Γ_N = [I, {Δ(S_i)}, {u_i(·)}]` in
which the sets `S_1, …, S_I` are finite (and nonempty) has a mixed strategy Nash equilibrium.
As in the text, this is Proposition 8.D.3 for strategy sets `Δ(S_i)` and the payoffs
`u_i(σ) = ∑_s [∏_k σ_k(s_k)] u_i(s)`. -/
theorem proposition_8_D_2 [∀ i, Nonempty (S i)] (N : NormalForm I S) :
    ∃ σ, IsMixedNash N σ := by
  obtain ⟨σ, hσ, hne⟩ := nash_exists_of_quasiconcave (E := fun i => S i → ℝ)
    (u := fun i σ => N.mixedPayoff σ i) (S := fun i => mixedExtension (S i))
    (fun i => ⟨_, isMixedStrategy_uniformMixed (S i)⟩)
    (fun i => isCompact_mixedExtension (S i)) (fun i => convex_mixedExtension (S i))
    (fun i => (continuous_mixedPayoff N i).continuousOn)
    (fun i σ _ => (concaveOn_mixedPayoff_update N σ i (convex_mixedExtension (S i))).quasiconcaveOn)
  exact ⟨σ, fun i => hσ i (Set.mem_univ i), fun i τ hτ => hne i τ hτ⟩

omit [Fintype I] [DecidableEq I] [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] in
/-- **Proposition 8.D.2 needs nonempty strategy sets** (correction 2). If some `S_i` is empty there
is no mixed strategy for player `i`, so no mixed profile and no mixed Nash equilibrium. -/
theorem no_mixedProfile_of_isEmpty [∀ i, Fintype (S i)] (i : I) [IsEmpty (S i)]
    (σ : (i : I) → S i → ℝ) : ¬ IsMixedProfile σ := by
  intro h
  have := (h i).2
  simp at this

/-- **Footnote 5** (MWG, p. 253). A finite convex subset of a real vector space has at most one
element. -/
theorem footnote_8_5 {V : Type*} [AddCommGroup V] [Module ℝ V] {T : Set V} (hfin : T.Finite)
    (hconv : Convex ℝ T) : T.Subsingleton := by
  intro x hx y hy
  by_contra hxy
  have hsub : segment ℝ x y ⊆ T := hconv.segment_subset hx hy
  rw [segment_eq_image_lineMap] at hsub
  have hinf : (AffineMap.lineMap x y '' Set.Icc (0 : ℝ) 1).Infinite :=
    (Set.Icc_infinite zero_lt_one).image (AffineMap.lineMap_injective ℝ hxy).injOn
  exact hinf (hfin.subset hsub)

/-- **Footnote 5 as printed is false for one-point sets** (correction 3): a singleton strategy set
is finite and convex. -/
theorem footnote_8_5_singleton {V : Type*} [AddCommGroup V] [Module ℝ V] (v : V) :
    ({v} : Set V).Finite ∧ Convex ℝ ({v} : Set V) :=
  ⟨Set.finite_singleton v, convex_singleton v⟩

end MWG.SimultaneousMoveGames
