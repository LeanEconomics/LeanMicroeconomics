/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPositiveEquilibriumTheory.ExistenceBrouwer
import MWGWelfareTheorems.CheaperPoint
import MWGGeneralEquilibriumExamples.ParetoCurve

/-!
# Characterizing equilibrium through welfare equations (MWG Appendix A to Chapter 17,
pp. 630-631; Exercise 17.AA.1)

The Negishi approach. A pure exchange economy with consumers `i = 1, …, I`, `Xᵢ = ℝ^L₊`,
continuous, strongly monotone, strictly convex preferences represented by continuous utilities
with `uᵢ(0) = 0`, `ωᵢ ≥ 0` and `∑ᵢ ωᵢ ≫ 0`.

* `IsNegishiAlloc E s x`: `x` is Pareto optimal and `(u₁(x₁), …, u_I(x_I))` is proportional to
  `s` (p. 630). For every `s ∈ Δ` such an allocation exists (`negishiAlloc_exists`: maximize
  `minᵢ uᵢ(xᵢ)/sᵢ` over the compact set of feasible allocations, then redistribute,
  `negishi_redistribute`) and it is unique (`negishiAlloc_unique`; **Exercise 17.AA.1**,
  `exercise_17_AA_1`); `negishiAlloc E s` is it (Figure 17.AA.1).
* Supporting prices (p. 631): `IsSupportingPrice E x p` (`x'ᵢ ≻ᵢ xᵢ` implies `p·x'ᵢ > p·xᵢ`);
  they exist, normalized in `Δ` and `≫ 0`, at every Pareto optimum
  (`supportingPrice_exists`, from the second welfare theorem as in Chapter 17's
  `secondWelfare_of_existence`). The weak form `IsQuasiSupportingPrice` (`≥`) is equivalent for
  normalized prices (`quasiSupport_isSupporting`, a cheaper-point argument).
* **(17.AA.1)** (p. 631): with `x` feasible and `p` supporting it, `(x, p)` is a Walrasian
  equilibrium iff `gᵢ = p·(ωᵢ - xᵢ) = 0` for every `i` (`appendix_A_walras_iff`; Figure 17.AA.2).
  `walras_budget_eq` is its "only if" half without the support hypothesis.
-/

namespace MWG.PositiveEquilibriumTheory

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.GeneralEquilibriumExamples MWG.WelfareTheorems
open Filter Topology

variable {I L : ℕ}

/-- **Appendix A** (MWG, pp. 630-631; Figure 17.AA.1). `x` is a Pareto optimal allocation whose
utility vector `(u₁(x₁), …, u_I(x_I))` is proportional to `s`: `uᵢ(xᵢ) = t sᵢ` for one `t`. -/
def IsNegishiAlloc (E : ExchangeEconomy (Fin I) L) (s : Fin I → ℝ)
    (x : Fin I → Fin L → ℝ) : Prop :=
  E.IsParetoOptimal x ∧ ∃ t : ℝ, ∀ i, E.u i (x i) = t * s i

/-- **Appendix A** (MWG, p. 631). `p` supports the allocation `x`: for every `i`, `x'ᵢ ≻ᵢ xᵢ`
(`x'ᵢ ∈ Xᵢ`) implies `p·x'ᵢ > p·xᵢ`. -/
def IsSupportingPrice (E : ExchangeEconomy (Fin I) L) (x : Fin I → Fin L → ℝ)
    (p : Fin L → ℝ) : Prop :=
  ∀ i, ∀ y ∈ E.X i, E.u i (x i) < E.u i y → p ⬝ᵥ x i < p ⬝ᵥ y

/-- The weak (quasiequilibrium) form of support: `x'ᵢ ≻ᵢ xᵢ` implies `p·x'ᵢ ≥ p·xᵢ`. -/
def IsQuasiSupportingPrice (E : ExchangeEconomy (Fin I) L) (x : Fin I → Fin L → ℝ)
    (p : Fin L → ℝ) : Prop :=
  ∀ i, ∀ y ∈ E.X i, E.u i (x i) < E.u i y → p ⬝ᵥ x i ≤ p ⬝ᵥ y

/-! ### Uniqueness (Exercise 17.AA.1) -/

/-- **Appendix A** (MWG, p. 630) and **Exercise 17.AA.1**. With strictly convex preferences
(`uᵢ` strictly quasiconcave on the convex `Xᵢ`), for `s ≥ 0`, `s ≠ 0` there is at most one Pareto
optimal allocation with utilities proportional to `s`. -/
theorem negishiAlloc_unique {E : ExchangeEconomy (Fin I) L}
    (hsq : ∀ i, StrictlyQuasiconcaveOn (E.X i) (E.u i)) {s : Fin I → ℝ}
    (hs0 : ∀ i, 0 ≤ s i) (hs : s ≠ 0) {x x' : Fin I → Fin L → ℝ}
    (hx : IsNegishiAlloc E s x) (hx' : IsNegishiAlloc E s x') : x = x' := by
  obtain ⟨hpo, t, ht⟩ := hx
  obtain ⟨hpo', t', ht'⟩ := hx'
  obtain ⟨i₀, hi₀⟩ : ∃ i, 0 < s i := by
    by_contra h
    push Not at h
    exact hs (funext fun i => le_antisymm (h i) (hs0 i))
  have htt : t = t' := by
    rcases lt_trichotomy t t' with h | h | h
    · exfalso
      refine hpo.2 ⟨x', hpo'.1, fun i => ?_, i₀, ?_⟩
      · rw [ht i, ht' i]
        exact mul_le_mul_of_nonneg_right h.le (hs0 i)
      · rw [ht i₀, ht' i₀]
        exact mul_lt_mul_of_pos_right h hi₀
    · exact h
    · exfalso
      refine hpo'.2 ⟨x, hpo.1, fun i => ?_, i₀, ?_⟩
      · rw [ht i, ht' i]
        exact mul_le_mul_of_nonneg_right h.le (hs0 i)
      · rw [ht i₀, ht' i₀]
        exact mul_lt_mul_of_pos_right h hi₀
  have hu : ∀ i, E.u i (x i) = E.u i (x' i) := fun i => by rw [ht i, ht' i, htt]
  by_contra hne
  obtain ⟨i₁, hi₁⟩ : ∃ i, x i ≠ x' i := by
    by_contra h
    push Not at h
    exact hne (funext h)
  set m : Fin I → Fin L → ℝ := fun i => (1 / 2 : ℝ) • x i + (1 - 1 / 2 : ℝ) • x' i with hm
  have hmbox : E.InBox m := by
    refine ⟨fun i => (hsq i).1 (hpo.1.1 i) (hpo'.1.1 i) (by norm_num) (by norm_num)
      (by norm_num), ?_⟩
    simp only [hm, Finset.sum_add_distrib, ← Finset.smul_sum, hpo.1.2, hpo'.1.2]
    rw [← add_smul]
    norm_num
  have hstrict : ∀ i, x i ≠ x' i → E.u i (x i) < E.u i (m i) := fun i h =>
    (hsq i).2 (x i) (hpo.1.1 i) (x' i) (hpo'.1.1 i) h (1 / 2) (by norm_num) (by norm_num)
      (E.u i (x i)) le_rfl (hu i).le
  have hge : ∀ i, E.u i (x i) ≤ E.u i (m i) := by
    intro i
    by_cases h : x i = x' i
    · have hmi : m i = x i := by
        simp only [hm, h]
        rw [← add_smul]
        norm_num
      rw [hmi]
    · exact (hstrict i h).le
  exact hpo.2 ⟨m, hmbox, hge, i₁, hstrict i₁ hi₁⟩

/-- **Exercise 17.AA.1** (MWG, p. 649). In an exchange economy whose consumers have strictly
convex preferences represented by `uᵢ`, for any `s ≫ 0` there is at most one Pareto optimal
allocation `x` with `(u₁(x₁), …, u_I(x_I))` proportional to `s`. (Monotonicity is not needed.) -/
theorem exercise_17_AA_1 {E : ExchangeEconomy (Fin I) L}
    (hsq : ∀ i, StrictlyQuasiconcaveOn (E.X i) (E.u i)) {s : Fin I → ℝ} (hs : ∀ i, 0 < s i)
    {x x' : Fin I → Fin L → ℝ} (hx : IsNegishiAlloc E s x) (hx' : IsNegishiAlloc E s x') :
    x = x' := by
  rcases Nat.eq_zero_or_pos I with h0 | hI
  · subst h0
    funext i
    exact i.elim0
  · refine negishiAlloc_unique hsq (fun i => (hs i).le) (fun h => ?_) hx hx'
    have := hs ⟨0, hI⟩
    rw [h] at this
    exact lt_irrefl 0 this

/-! ### Existence -/

/-- With `Xᵢ = ℝ^L₊`, the set of feasible (nonwasteful) allocations is compact. -/
theorem isCompact_inBox {E : ExchangeEconomy (Fin I) L} (hX : ∀ i, E.X i = nonnegOrthant L) :
    IsCompact {x : Fin I → Fin L → ℝ | E.InBox x} := by
  have hxm : ∀ x : Fin I → Fin L → ℝ, E.InBox x → ∀ i, x i ∈ nonnegOrthant L :=
    fun x hx i => hX i ▸ hx.1 i
  apply Metric.isCompact_of_isClosed_isBounded
  · have : {x : Fin I → Fin L → ℝ | E.InBox x} =
        (⋂ i, ⋂ l, {x : Fin I → Fin L → ℝ | 0 ≤ x i l}) ∩
          {x | ∑ i, x i = E.totalEndowment} := by
      ext x
      constructor
      · intro hx
        exact ⟨Set.mem_iInter.2 fun i => Set.mem_iInter.2 fun l => hxm x hx i l, hx.2⟩
      · rintro ⟨h1, h2⟩
        refine ⟨fun i => ?_, h2⟩
        rw [hX i]
        exact fun l => Set.mem_iInter.1 (Set.mem_iInter.1 h1 i) l
    rw [this]
    exact (isClosed_iInter fun i => isClosed_iInter fun l =>
      isClosed_le continuous_const (by fun_prop)).inter
      (isClosed_eq (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const)
  · refine (Metric.isBounded_Icc (0 : Fin I → Fin L → ℝ) fun _ => E.totalEndowment).subset ?_
    intro x hx
    refine ⟨fun i l => hxm x hx i l, fun i l => ?_⟩
    change x i l ≤ E.totalEndowment l
    have h := congrFun hx.2 l
    rw [Finset.sum_apply] at h
    rw [← h]
    exact Finset.single_le_sum (f := fun j => x j l) (fun j _ => hxm x hx j l) (Finset.mem_univ i)

/-- **Appendix A** (MWG, p. 630), the redistribution step. If consumer `k` has a nonzero bundle
and `uₖ(xₖ) > c`, a little of `xₖ` can be spread over all consumers so that `k` still has more
than `c` and every other consumer is strictly better off (continuity and strong
monotonicity). -/
theorem negishi_redistribute {E : ExchangeEconomy (Fin I) L}
    (hX : ∀ i, E.X i = nonnegOrthant L) (hc : ∀ i, ContinuousOn (E.u i) (nonnegOrthant L))
    (hm : ∀ i, UtilityStronglyMonotone (E.u i)) {x : Fin I → Fin L → ℝ} (hx : E.InBox x)
    {k : Fin I} (hk : x k ≠ 0) {c : ℝ} (hck : c < E.u k (x k)) :
    ∃ x'', E.InBox x'' ∧ c < E.u k (x'' k) ∧ ∀ j, j ≠ k → E.u j (x j) < E.u j (x'' j) := by
  classical
  have hxm : ∀ i, x i ∈ nonnegOrthant L := fun i => hX i ▸ hx.1 i
  obtain ⟨t, ht0, ht1, htc⟩ := pc_exists_shrink (hc k) (hxm k) hck
  have hI : (0 : ℝ) < I := by exact_mod_cast k.pos
  set d : Fin L → ℝ := (t / I) • x k with hd
  have hd0 : ∀ l, 0 ≤ d l := fun l => by
    simp only [hd, Pi.smul_apply, smul_eq_mul]
    exact mul_nonneg (div_nonneg ht0.le hI.le) (hxm k l)
  have hdne : d ≠ 0 := by
    intro h0
    exact hk ((smul_eq_zero.1 h0).resolve_left (div_pos ht0 hI).ne')
  set x'' : Fin I → Fin L → ℝ := fun j => x j + d - (if j = k then t • x k else 0) with hx''
  have hk'' : x'' k = (1 - t + t / I) • x k := by
    simp only [hx'', ↓reduceIte, hd]
    module
  have hj'' : ∀ j, j ≠ k → x'' j = x j + d := fun j hj => by simp [hx'', hj]
  have hsum : ∑ j, x'' j = ∑ j, x j := by
    simp only [hx'', Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    rw [hd, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_div_cancel₀ t hI.ne']
    abel
  have hcoef : 1 - t ≤ 1 - t + t / I := by
    have : 0 ≤ t / I := div_nonneg ht0.le hI.le
    linarith
  refine ⟨x'', ⟨fun j => ?_, hsum.trans hx.2⟩, ?_, fun j hj => ?_⟩
  · rw [hX j]
    by_cases hj : j = k
    · rw [hj, hk'']
      intro l
      simp only [Pi.smul_apply, smul_eq_mul]
      exact mul_nonneg (by linarith) (hxm k l)
    · rw [hj'' j hj]
      intro l
      simp only [Pi.add_apply]
      exact add_nonneg (hxm j l) (hd0 l)
  · rw [hk'']
    have hmem : (1 - t) • x k ∈ nonnegOrthant L := fun l => by
      simp only [Pi.smul_apply, smul_eq_mul]
      exact mul_nonneg (by linarith) (hxm k l)
    refine lt_of_lt_of_le htc ((hm k).le hmem fun l => ?_)
    simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_le_mul_of_nonneg_right hcoef (hxm k l)
  · rw [hj'' j hj]
    refine (hm j).lt (hxm j) (fun l => ?_) fun h => hdne ?_
    · simp only [Pi.add_apply]
      linarith [hd0 l]
    · have := congrArg (fun v => v - x j) h
      simpa using this

/-- **Appendix A** (MWG, p. 630). For every `s ∈ Δ` there is a Pareto optimal allocation `x(s)`
with `(u₁(x₁(s)), …, u_I(x_I(s)))` proportional to `s`, for `Xᵢ = ℝ^L₊`, continuous, strongly
monotone utilities with `uᵢ(0) = 0` and `ωᵢ ≥ 0`. -/
theorem negishiAlloc_exists {E : ExchangeEconomy (Fin I) L}
    (hX : ∀ i, E.X i = nonnegOrthant L) (hc : ∀ i, ContinuousOn (E.u i) (nonnegOrthant L))
    (hm : ∀ i, UtilityStronglyMonotone (E.u i)) (hu0 : ∀ i, E.u i 0 = 0)
    (hω : ∀ i, E.ω i ∈ nonnegOrthant L) {s : Fin I → ℝ} (hs : s ∈ priceSimplex I) :
    ∃ x, IsNegishiAlloc E s x := by
  classical
  set K : Set (Fin I → Fin L → ℝ) := {x | E.InBox x} with hK
  have hxm : ∀ x ∈ K, ∀ i, x i ∈ nonnegOrthant L := fun x hx i => hX i ▸ hx.1 i
  have hKc : IsCompact K := isCompact_inBox hX
  obtain ⟨hs0, hs1⟩ := hs
  set P : Finset (Fin I) := Finset.univ.filter fun i => 0 < s i with hP
  have hPne : P.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have hz : ∀ i, s i = 0 := fun i => by
      refine le_antisymm ?_ (hs0 i)
      by_contra hi
      push Not at hi
      have hiP : i ∈ P := Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩
      rw [h] at hiP
      exact Finset.notMem_empty i hiP
    simp [hz] at hs1
  set f : (Fin I → Fin L → ℝ) → ℝ := fun x => P.inf' hPne fun i => E.u i (x i) / s i with hf
  have hfc : ContinuousOn f K := ContinuousOn.finset_inf'_apply hPne fun i _ =>
    ((hc i).comp (continuous_apply i).continuousOn fun x hx => hxm x hx i).div_const _
  have hKne : K.Nonempty := ⟨E.ω, fun i => (hX i).symm ▸ hω i, rfl⟩
  obtain ⟨xs, hxsK, hmax⟩ := hKc.exists_isMaxOn hKne hfc
  set ts := f xs with hts
  have hu_nonneg : ∀ x ∈ K, ∀ i, 0 ≤ E.u i (x i) := fun x hx i => by
    have := (hm i).le (x := (0 : Fin L → ℝ)) (fun _ => le_refl (0 : ℝ)) (hxm x hx i)
    rwa [hu0 i] at this
  have hts0 : 0 ≤ ts := Finset.le_inf' hPne _ fun i hi =>
    div_nonneg (hu_nonneg xs hxsK i) (Finset.mem_filter.1 hi).2.le
  have hge : ∀ i, ts * s i ≤ E.u i (xs i) := by
    intro i
    rcases (hs0 i).lt_or_eq with h | h
    · have hiP : i ∈ P := Finset.mem_filter.2 ⟨Finset.mem_univ i, h⟩
      have := Finset.inf'_le (fun i => E.u i (xs i) / s i) hiP
      have h2 : ts ≤ E.u i (xs i) / s i := this
      rwa [le_div_iff₀ h] at h2
    · rw [← h, mul_zero]
      exact hu_nonneg xs hxsK i
  have hno : ∀ x'' ∈ K, ¬ ∀ i, ts * s i < E.u i (x'' i) := by
    intro x'' hx'' hall
    have hlt : ts < f x'' := (Finset.lt_inf'_iff hPne).2 fun i hi => by
      rw [lt_div_iff₀ (Finset.mem_filter.1 hi).2]
      exact hall i
    exact absurd (hmax hx'') (not_le.2 hlt)
  have hnz : ∀ x ∈ K, ∀ i, 0 < E.u i (x i) → x i ≠ 0 := fun x _ i h h0 => by
    rw [h0, hu0] at h
    exact lt_irrefl 0 h
  have heq : ∀ i, E.u i (xs i) = ts * s i := by
    by_contra h
    push Not at h
    obtain ⟨i₀, hi₀⟩ := h
    have hlt : ts * s i₀ < E.u i₀ (xs i₀) := lt_of_le_of_ne (hge i₀) (Ne.symm hi₀)
    have hne0 : xs i₀ ≠ 0 := hnz xs hxsK i₀ (lt_of_le_of_lt (mul_nonneg hts0 (hs0 i₀)) hlt)
    obtain ⟨x'', hx'', hk, hj⟩ := negishi_redistribute hX hc hm hxsK hne0 hlt
    refine hno x'' hx'' fun i => ?_
    by_cases hi : i = i₀
    · rw [hi]
      exact hk
    · exact lt_of_le_of_lt (hge i) (hj i hi)
  refine ⟨xs, ⟨hxsK, ?_⟩, ts, heq⟩
  rintro ⟨x', hx', hdom, k, hk⟩
  have hne0 : x' k ≠ 0 := hnz x' hx' k (lt_of_le_of_lt (hu_nonneg xs hxsK k) hk)
  obtain ⟨x'', hx'', hk'', hj''⟩ := negishi_redistribute hX hc hm hx' hne0 hk
  refine hno x'' hx'' fun i => ?_
  by_cases hi : i = k
  · rw [hi, ← heq]
    exact hk''
  · rw [← heq i]
    exact lt_of_le_of_lt (hdom i) (hj'' i hi)

/-- **Appendix A** (MWG, p. 630). The Pareto optimal allocation `x(s)` associated with `s ∈ Δ`
(chosen; unique by `negishiAlloc_unique`), and the endowment allocation for other `s`. -/
noncomputable def negishiAlloc (E : ExchangeEconomy (Fin I) L) (s : Fin I → ℝ) :
    Fin I → Fin L → ℝ :=
  open Classical in if h : ∃ x, IsNegishiAlloc E s x then h.choose else E.ω

/-- `x(s)` is the Pareto optimal allocation with utilities proportional to `s`. -/
theorem negishiAlloc_spec {E : ExchangeEconomy (Fin I) L}
    (hX : ∀ i, E.X i = nonnegOrthant L) (hc : ∀ i, ContinuousOn (E.u i) (nonnegOrthant L))
    (hm : ∀ i, UtilityStronglyMonotone (E.u i)) (hu0 : ∀ i, E.u i 0 = 0)
    (hω : ∀ i, E.ω i ∈ nonnegOrthant L) {s : Fin I → ℝ} (hs : s ∈ priceSimplex I) :
    IsNegishiAlloc E s (negishiAlloc E s) := by
  have h := negishiAlloc_exists hX hc hm hu0 hω hs
  unfold negishiAlloc
  simp only [h, ↓reduceDIte]
  exact h.choose_spec

/-- `x(s)` is always a feasible (nonwasteful) allocation. -/
theorem negishiAlloc_inBox {E : ExchangeEconomy (Fin I) L} (hω : ∀ i, E.ω i ∈ E.X i)
    (s : Fin I → ℝ) : E.InBox (negishiAlloc E s) := by
  unfold negishiAlloc
  by_cases h : ∃ x, IsNegishiAlloc E s x
  · simp only [h, ↓reduceDIte]
    exact h.choose_spec.1.1
  · simp only [h, ↓reduceDIte]
    exact ⟨hω, rfl⟩

/-- The proportionality factor is total utility: `uᵢ(xᵢ) = (∑ⱼ uⱼ(xⱼ)) sᵢ` for `s ∈ Δ`. -/
theorem IsNegishiAlloc.u_eq {E : ExchangeEconomy (Fin I) L} {s : Fin I → ℝ}
    {x : Fin I → Fin L → ℝ} (h : IsNegishiAlloc E s x) (hs : s ∈ priceSimplex I) (i : Fin I) :
    E.u i (x i) = (∑ j, E.u j (x j)) * s i := by
  obtain ⟨-, t, ht⟩ := h
  have : ∑ j, E.u j (x j) = t := by
    simp only [ht, ← Finset.mul_sum, hs.2, mul_one]
  rw [this, ht i]

/-! ### Supporting prices -/

/-- **Appendix A** (MWG, p. 631; Proposition 16.D.1 and the small type after Proposition
16.D.3). Every Pareto optimal allocation of the economy (`L ≥ 1`, `Xᵢ = ℝ^L₊`, continuous,
strictly convex, strongly monotone preferences, `∑ᵢ ωᵢ ≫ 0`) has a supporting price vector
`p ≫ 0`, which can be normalized to lie in the simplex. -/
theorem supportingPrice_exists {E : ExchangeEconomy (Fin I) L} (hL : 0 < L)
    (hX : ∀ i, E.X i = nonnegOrthant L) (hu : ∀ i, StandardUtility (E.u i))
    (hpos : ∀ l, 0 < E.totalEndowment l) {x : Fin I → Fin L → ℝ} (hpo : E.IsParetoOptimal x) :
    ∃ p ∈ priceSimplex L, p ∈ posOrthant L ∧ IsSupportingPrice E x p := by
  obtain ⟨p, hp, heq⟩ := secondWelfare_of_existence hL hX hu hpos hpo
  set σ := ∑ l, p l with hσdef
  have hσ : 0 < σ := Finset.sum_pos (fun l _ => hp l) ⟨⟨0, hL⟩, Finset.mem_univ _⟩
  refine ⟨σ⁻¹ • p, ⟨fun l => ?_, ?_⟩, fun l => ?_, fun i y hy hlt => ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.2 hσ.le) (hp l).le
  · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, ← hσdef]
    exact inv_mul_cancel₀ hσ.ne'
  · simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_pos (inv_pos.2 hσ) (hp l)
  · have hnot : ¬ p ⬝ᵥ y ≤ p ⬝ᵥ x i := fun hle =>
      not_le.2 hlt (heq.2.2 i y hy (by linarith))
    rw [smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul]
    exact mul_lt_mul_of_pos_left (not_le.1 hnot) (inv_pos.2 hσ)

/-- **Appendix A** (MWG, p. 631). For a feasible allocation and a normalized price `p ∈ Δ`, weak
support implies `p ≫ 0` and (strict) support, under `Xᵢ = ℝ^L₊`, continuous strongly monotone
utilities and `∑ᵢ ωᵢ ≫ 0` (a cheaper-point argument, as in Proposition 16.D.2). -/
theorem quasiSupport_isSupporting {E : ExchangeEconomy (Fin I) L}
    (hX : ∀ i, E.X i = nonnegOrthant L) (hc : ∀ i, ContinuousOn (E.u i) (nonnegOrthant L))
    (hm : ∀ i, UtilityStronglyMonotone (E.u i)) (hpos : ∀ l, 0 < E.totalEndowment l)
    {x : Fin I → Fin L → ℝ} (hbox : E.InBox x) {p : Fin L → ℝ} (hp : p ∈ priceSimplex L)
    (hq : IsQuasiSupportingPrice E x p) : p ∈ posOrthant L ∧ IsSupportingPrice E x p := by
  have hxm : ∀ i, x i ∈ nonnegOrthant L := fun i => hX i ▸ hbox.1 i
  have hp0 : p ≠ 0 := fun h => by
    have := hp.2
    simp [h] at this
  have hstrict : ∀ i, 0 < p ⬝ᵥ x i → ∀ y ∈ nonnegOrthant L, E.u i (x i) < E.u i y →
      p ⬝ᵥ x i < p ⬝ᵥ y := by
    intro i hpx y hy hlt
    by_contra hle
    push Not at hle
    obtain ⟨t, ht0, ht1, htu⟩ := pc_exists_shrink (hc i) hy hlt
    have hmem : (1 - t) • y ∈ E.X i := by
      rw [hX i]
      intro l
      simp only [Pi.smul_apply, smul_eq_mul]
      exact mul_nonneg (by linarith) (hy l)
    have h1 := hq i _ hmem htu
    have h2 := hq i y (hX i ▸ hy) hlt
    rw [dotProduct_smul, smul_eq_mul] at h1
    nlinarith [mul_pos ht0 hpx]
  obtain ⟨j, hj⟩ : ∃ j, 0 < p ⬝ᵥ x j := by
    by_contra h
    push Not at h
    have hsum : p ⬝ᵥ E.totalEndowment ≤ 0 := by
      rw [← hbox.2, dotProduct_sum]
      exact Finset.sum_nonpos fun j _ => h j
    exact absurd hsum (not_le.2 (dotProduct_pos_of_nonneg_ne_zero hp.1 hp0 hpos))
  have hppos : ∀ l, 0 < p l := by
    intro l
    by_contra hl
    push Not at hl
    have hl0 : p l = 0 := le_antisymm hl (hp.1 l)
    have hsingle : ∀ k, 0 ≤ (Pi.single l (1 : ℝ) : Fin L → ℝ) k := fun k => by
      rw [Pi.single_apply]
      split_ifs <;> norm_num
    have hy : x j + Pi.single l 1 ∈ nonnegOrthant L := fun k =>
      add_nonneg (hxm j k) (hsingle k)
    have hlt : E.u j (x j) < E.u j (x j + Pi.single l 1) := by
      refine (hm j).lt (hxm j) (fun k => ?_) fun h => ?_
      · simp only [Pi.add_apply]
        linarith [hsingle k]
      · have := congrFun h l
        simp at this
    have := hstrict j hj _ hy hlt
    rw [dotProduct_add, dotProduct_single, hl0, zero_mul, add_zero] at this
    exact lt_irrefl _ this
  refine ⟨hppos, fun i y hy hlt => ?_⟩
  rw [hX i] at hy
  by_cases hpx : 0 < p ⬝ᵥ x i
  · exact hstrict i hpx y hy hlt
  · have hnn : ∀ k ∈ Finset.univ, 0 ≤ p k * x i k := fun k _ => mul_nonneg (hp.1 k) (hxm i k)
    have hpx0 : p ⬝ᵥ x i = 0 := le_antisymm (not_lt.1 hpx) (Finset.sum_nonneg hnn)
    have hxi : x i = 0 := by
      funext l
      have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hpx0 l (Finset.mem_univ l)
      exact (mul_eq_zero.1 this).resolve_left (hppos l).ne'
    rw [hpx0]
    have hy0 : y ≠ 0 := fun h => by
      rw [h, ← hxi] at hlt
      exact lt_irrefl _ hlt
    obtain ⟨l, hl⟩ : ∃ l, y l ≠ 0 := by
      by_contra h
      push Not at h
      exact hy0 (funext h)
    exact Finset.sum_pos' (fun k _ => mul_nonneg (hppos k).le (hy k))
      ⟨l, Finset.mem_univ _, mul_pos (hppos l) (lt_of_le_of_ne (hy l) (Ne.symm hl))⟩

/-! ### The equation system (17.AA.1) -/

/-- **Appendix A** (MWG, p. 631). At a Walrasian equilibrium (Definition 15.B.1) of an exchange
economy with `Xᵢ = ℝ^L₊`, `L ≥ 1` and strongly monotone utilities, every consumer spends his whole
wealth: `p·xᵢ = p·ωᵢ`. -/
theorem walras_budget_eq {E : ExchangeEconomy (Fin I) L} (hL : 0 < L)
    (hX : ∀ i, E.X i = nonnegOrthant L) (hm : ∀ i, UtilityStronglyMonotone (E.u i))
    {p : Fin L → ℝ} {x : Fin I → Fin L → ℝ} (h : E.IsWalrasEqm p x) (i : Fin I) :
    p ⬝ᵥ x i = p ⬝ᵥ E.ω i := by
  have hxm : ∀ i, x i ∈ nonnegOrthant L := fun i => hX i ▸ h.1.1 i
  have hge : ∀ i, p ⬝ᵥ E.ω i ≤ p ⬝ᵥ x i := by
    intro i
    by_contra hlt
    push Not at hlt
    obtain ⟨y, hy, hpy, huy⟩ := ((hm i).lns hL).exists_better p (hxm i) hlt
    exact absurd (h.2 i y ⟨(hX i).symm ▸ hy, hpy.le⟩) (not_le.2 huy)
  have hsum : ∑ j, (p ⬝ᵥ x j - p ⬝ᵥ E.ω j) = 0 := by
    rw [Finset.sum_sub_distrib, ← dotProduct_sum, ← dotProduct_sum, h.1.2]
    simp [ExchangeEconomy.totalEndowment]
  have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sub_nonneg.2 (hge j)).1 hsum i
    (Finset.mem_univ i)
  linarith

/-- **(17.AA.1)** (MWG, p. 631; Figure 17.AA.2). Let `x` be a feasible allocation supported by
`p` (in the economy of Appendix A: `Xᵢ = ℝ^L₊`, `L ≥ 1`, strongly monotone utilities). Then
`(x, p)` is a Walrasian equilibrium iff `gᵢ = p·[ωᵢ - xᵢ] = 0` for every `i = 1, …, I`. -/
theorem appendix_A_walras_iff {E : ExchangeEconomy (Fin I) L} (hL : 0 < L)
    (hX : ∀ i, E.X i = nonnegOrthant L) (hm : ∀ i, UtilityStronglyMonotone (E.u i))
    {x : Fin I → Fin L → ℝ} {p : Fin L → ℝ} (hbox : E.InBox x)
    (hsup : IsSupportingPrice E x p) :
    E.IsWalrasEqm p x ↔ ∀ i, p ⬝ᵥ (E.ω i - x i) = 0 := by
  constructor
  · intro h i
    rw [dotProduct_sub, walras_budget_eq hL hX hm h i, sub_self]
  · intro hg
    refine ⟨hbox, fun i y hy => ?_⟩
    by_contra hlt
    push Not at hlt
    have h1 := hsup i y hy.1 hlt
    have h2 := hg i
    rw [dotProduct_sub] at h2
    have h3 := hy.2
    linarith

end MWG.PositiveEquilibriumTheory
