/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGCoreFoundations.CoreWalras

/-!
# Equal treatment in replica economies (MWG Section 18.B, pp. 655-657, 685)

* **Proposition 18.B.2** (`proposition_18_B_2`): under the standing assumptions every core
  allocation of the `N`-replica has the equal-treatment property. The proof is the book's: the
  worst-treated member of each type (`exists_worst`), the type averages, strict convexity
  (18.B.1) (`avg_pref`, `avg_strict`), **footnote 5** (`footnote_18_5`, continuity and strong
  monotonicity turn "weakly better for all, strictly for one" into blocking) and the constant
  returns fact `(1/N) y ∈ Y`.
* p. 657: the equal-treatment allocation of a feasible type allocation is feasible in every
  replica (`replica_isFeasible_typeAlloc`); `C_{N+1} ⊆ C_N` (`CN_succ_subset`); a type
  allocation is Walrasian in the economy of types iff it is Walrasian in the `N`-replica, `N ≥ 1`
  (`isWalrasEqm_typeAlloc_iff`), so the set of Walrasian type allocations does not depend on `N`
  (`walrasTypeAllocs_eq`) and lies in every `C_N` (`walras_mem_CN`); the core allocations of the
  `N`-replica are the equal-treatment allocations of `C_N` (`core_replica_eq_typeAlloc`).
* **Exercise 18.B.3** (`exercise_18_B_3`): directly, consumers with the same (rational, strictly
  convex) preferences and endowments get the same bundle in a Walrasian equilibrium; continuity is
  not needed. Hence Walrasian allocations of replicas have equal treatment.
* **Exercise 18.B.2**: (i) `exercise_18_B_2a`: a three-consumer exchange economy (`u = 2√x + m`,
  consumers 1 and 2 identical with endowment `(0, 2)`, consumer 3 with `(3, 2)`; preferences
  continuous, strictly convex and strongly monotone, `ex18B2Economy_standing`) whose core
  contains the allocation `(1, 1), (1, 1/2), (1, 9/2)`, which does not have equal treatment. No
  coalition blocks it by the transferable-utility bound `2√a ≤ a/c + c` (`ex18B2_tu_bound`).
  (ii) `exercise_18_B_2b`: no example with two consumers exists: if the two consumers have the
  same preferences and endowments, every core allocation gives them the same bundle.
-/

namespace MWG.CoreFoundations

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.Production MWG.WelfareTheorems
open Kreps.PreferenceProperties

variable {L : ℕ}

/-! ### Convexity facts -/

/-- With strictly convex preferences on `ℝ^L₊` the upper contour set `{y ≥ 0 : y ≿ x}` is
convex. -/
theorem convex_upper_of_strictlyConvex {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hsc : PrefStrictlyConvex (nonnegOrthant L) r) {x : Fin L → ℝ}
    (hx : x ∈ nonnegOrthant L) : Convex ℝ {y | y ∈ nonnegOrthant L ∧ r y x} := by
  intro y hy z hz a b ha hb hab
  refine ⟨convex_nonnegOrthant L hy.1 hz.1 ha hb hab, ?_⟩
  rcases ha.lt_or_eq with ha' | ha'
  · rcases hb.lt_or_eq with hb' | hb'
    · by_cases hyz : y = z
      · subst hyz
        rw [← add_smul, hab, one_smul]
        exact hy.2
      · have hb1 : b = 1 - a := by linarith
        subst hb1
        exact (hsc x hx y hy.1 z hz.1 hy.2 hz.2 hyz a ha' (by linarith)).1
    · subst hb'
      have ha1 : a = 1 := by linarith
      subst ha1
      simpa using hy.2
  · subst ha'
    have hb1 : b = 1 := by linarith
    subst hb1
    simpa using hz.2

/-- A worst element: for a rational preference, finitely many bundles have a worst one. -/
theorem exists_worst {κ : Type*} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hr : RationalOn (nonnegOrthant L) r) (s : Finset κ) (hs : s.Nonempty)
    (f : κ → Fin L → ℝ) (hf : ∀ k ∈ s, f k ∈ nonnegOrthant L) :
    ∃ k ∈ s, ∀ j ∈ s, r (f j) (f k) := by
  classical
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a =>
    refine ⟨a, Finset.mem_singleton_self a, fun j hj => ?_⟩
    rw [Finset.mem_singleton] at hj
    subst hj
    have ha := hf j (Finset.mem_singleton_self j)
    exact (hr.1 _ ha _ ha).elim id id
  | cons a s ha hs ih =>
    have hf' : ∀ k ∈ s, f k ∈ nonnegOrthant L := fun k hk => hf k (Finset.mem_cons_of_mem hk)
    obtain ⟨k, hk, hkw⟩ := ih hf'
    have hfa := hf a (Finset.mem_cons_self a s)
    have hfk := hf' k hk
    rcases hr.1 (f k) hfk (f a) hfa with h | h
    · refine ⟨a, Finset.mem_cons_self a s, fun j hj => ?_⟩
      rcases Finset.mem_cons.mp hj with rfl | hj
      · exact (hr.1 _ hfa _ hfa).elim id id
      · exact hr.2 _ (hf' j hj) _ hfk _ hfa (hkw j hj) h
    · refine ⟨k, Finset.mem_cons_of_mem hk, fun j hj => ?_⟩
      rcases Finset.mem_cons.mp hj with rfl | hj
      · exact h
      · exact hkw j hj

/-- The average of finitely many bundles each weakly preferred to `w` is weakly preferred to `w`
(strictly convex, hence convex, preferences). -/
theorem avg_pref {κ : Type*} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hsc : PrefStrictlyConvex (nonnegOrthant L) r) {w : Fin L → ℝ}
    (hw : w ∈ nonnegOrthant L) (s : Finset κ) (hs : s.Nonempty) (f : κ → Fin L → ℝ)
    (hf : ∀ k ∈ s, f k ∈ nonnegOrthant L ∧ r (f k) w) :
    (s.card : ℝ)⁻¹ • ∑ k ∈ s, f k ∈ nonnegOrthant L ∧
      r ((s.card : ℝ)⁻¹ • ∑ k ∈ s, f k) w := by
  have hc : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have := (convex_upper_of_strictlyConvex hsc hw).sum_mem (t := s) (w := fun _ => (s.card : ℝ)⁻¹)
    (z := f) (fun _ _ => inv_nonneg.mpr hc.le) (by
      rw [Finset.sum_const, nsmul_eq_mul, mul_inv_cancel₀ hc.ne']) hf
  rwa [← Finset.smul_sum] at this

/-- **Section 18.B** (MWG, p. 656, (18.B.1)). If finitely many bundles are weakly preferred to `w`
and two of them differ, their average is strictly preferred to `w` (strict convexity). -/
theorem avg_strict {κ : Type*} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hsc : PrefStrictlyConvex (nonnegOrthant L) r) {w : Fin L → ℝ}
    (hw : w ∈ nonnegOrthant L) (s : Finset κ) (f : κ → Fin L → ℝ)
    (hf : ∀ k ∈ s, f k ∈ nonnegOrthant L ∧ r (f k) w) {a b : κ} (ha : a ∈ s) (hb : b ∈ s)
    (hab : f a ≠ f b) : Strict r ((s.card : ℝ)⁻¹ • ∑ k ∈ s, f k) w := by
  classical
  set c := (s.card : ℝ)⁻¹ • ∑ k ∈ s, f k with hcdef
  -- a member different from the average
  obtain ⟨k₀, hk₀, hne⟩ : ∃ k₀ ∈ s, f k₀ ≠ c := by
    by_contra hall
    push Not at hall
    exact hab ((hall a ha).trans (hall b hb).symm)
  have hab' : a ≠ b := fun h => hab (h ▸ rfl)
  set s' := s.erase k₀ with hs'
  have hs'ne : s'.Nonempty := by
    by_cases hk : k₀ = a
    · exact ⟨b, Finset.mem_erase.mpr ⟨fun h => hab' (hk.symm.trans h.symm), hb⟩⟩
    · exact ⟨a, Finset.mem_erase.mpr ⟨fun h => hk h.symm, ha⟩⟩
  have hm : (0 : ℝ) < s'.card := by exact_mod_cast hs'ne.card_pos
  have hcard : (s.card : ℝ) = s'.card + 1 := by
    have := Finset.card_erase_add_one hk₀
    rw [hs']
    exact_mod_cast this.symm
  set d := (s'.card : ℝ)⁻¹ • ∑ k ∈ s', f k with hd
  obtain ⟨hdX, hdR⟩ := avg_pref hsc hw s' hs'ne f fun k hk => hf k (Finset.mem_of_mem_erase hk)
  have hcd : c = (s.card : ℝ)⁻¹ • f k₀ + (1 - (s.card : ℝ)⁻¹) • d := by
    rw [hcdef, hd, ← Finset.add_sum_erase s f hk₀, smul_add, smul_smul, ← hs']
    congr 2
    rw [hcard]
    field_simp
    ring
  have hfd : f k₀ ≠ d := by
    intro h
    apply hne
    rw [hcd, ← h, ← add_smul, add_sub_cancel, one_smul]
  have hn2 : (1 : ℝ) < s.card := by rw [hcard]; linarith
  rw [hcd]
  exact hsc w hw (f k₀) (hf k₀ hk₀).1 d hdX (hf k₀ hk₀).2 hdR hfd _ (by positivity)
    (inv_lt_one_of_one_lt₀ hn2)

/-! ### Proposition 18.B.2 -/

/-- **Footnote 5** (MWG, p. 656). With continuous and strongly monotone preferences, if the
coalition `S` can achieve consumptions that make all its members at least as well off as under
`x` and one of them strictly better off, then `S` blocks `x`. -/
theorem footnote_18_5 {ι : Type*} (E : CoreEconomy ι L)
    (hr : ∀ i, RationalOn (nonnegOrthant L) (E.pref i))
    (hc : ∀ i, PrefContinuous (nonnegOrthant L) (E.pref i))
    (hm : ∀ i, PrefStronglyMonotone (nonnegOrthant L) (E.pref i)) {S : Finset ι}
    {x x' : ι → Fin L → ℝ} (hx : ∀ i ∈ S, x i ∈ nonnegOrthant L)
    (hx' : ∀ i ∈ S, x' i ∈ nonnegOrthant L) (hweak : ∀ i ∈ S, E.pref i (x' i) (x i)) {k : ι}
    (hk : k ∈ S) (hstrict : Strict (E.pref k) (x' k) (x k))
    (hfeas : ∃ y ∈ E.Y, ∑ i ∈ S, x' i = y + ∑ i ∈ S, E.ω i) : E.Blocks S x := by
  classical
  obtain ⟨x'', hx'', hsum⟩ := exists_strict_all_of_weak hr hc hm S hx' hx hweak hk hstrict
  obtain ⟨y, hy, hs⟩ := hfeas
  exact ⟨⟨k, hk⟩, x'', hx'', y, hy, by rw [hsum, hs]⟩

/-- **Proposition 18.B.2** (MWG, p. 656). Under the standing assumptions of Section 18.B, every
allocation in the core of the `N`-replica economy has the equal-treatment property. -/
theorem proposition_18_B_2 {H : Type*} [Fintype H] (E : CoreEconomy H L) (hst : E.Standing)
    {N : ℕ} {x : H × Fin N → Fin L → ℝ} (hx : x ∈ (E.replica N).core) : EqualTreatment x := by
  classical
  intro h₀ m n
  by_contra hne
  obtain ⟨⟨hxX, y, hy, hsum⟩, hcore⟩ := hx
  have hr := fun h => (hst.2 h).2.1
  have hc := fun h => (hst.2 h).2.2.1
  have hsc := fun h => (hst.2 h).2.2.2.1
  have hm := fun h => (hst.2 h).2.2.2.2
  have hN : (0 : ℝ) < N := by exact_mod_cast (Fin.pos m)
  have huniv : (Finset.univ : Finset (Fin N)).Nonempty := ⟨m, Finset.mem_univ m⟩
  have hcardN : ((Finset.univ : Finset (Fin N)).card : ℝ) = N := by simp
  -- the worst-treated member of every type
  have hworst : ∀ h, ∃ k : Fin N, ∀ j, E.pref h (x (h, j)) (x (h, k)) := by
    intro h
    obtain ⟨k, -, hk⟩ :=
      exists_worst (hr h) Finset.univ huniv (fun j => x (h, j)) fun j _ => hxX (h, j)
    exact ⟨k, fun j => hk j (Finset.mem_univ j)⟩
  choose w hw using hworst
  -- the averages
  set xhat : H → Fin L → ℝ := fun h => (N : ℝ)⁻¹ • ∑ j, x (h, j) with hxhat
  have hweak : ∀ h, xhat h ∈ nonnegOrthant L ∧ E.pref h (xhat h) (x (h, w h)) := by
    intro h
    have := avg_pref (hsc h) (hxX (h, w h)) Finset.univ huniv (fun j => x (h, j))
      fun j _ => ⟨hxX (h, j), hw h j⟩
    rwa [hcardN] at this
  have hstrict : Strict (E.pref h₀) (xhat h₀) (x (h₀, w h₀)) := by
    have := avg_strict (hsc h₀) (hxX (h₀, w h₀)) Finset.univ (fun j => x (h₀, j))
      (fun j _ => ⟨hxX (h₀, j), hw h₀ j⟩) (Finset.mem_univ m)
      (Finset.mem_univ n) hne
    rwa [hcardN] at this
  -- the coalition of the worst-treated members
  set e : H ↪ H × Fin N := ⟨fun h => (h, w h), fun a b hab => (Prod.ext_iff.mp hab).1⟩ with he
  set S : Finset (H × Fin N) := Finset.univ.map e with hS
  apply hcore S
  have hmem : ∀ h, (h, w h) ∈ S := fun h => Finset.mem_map_of_mem e (Finset.mem_univ h)
  have hS' : ∀ i ∈ S, i = (i.1, w i.1) := by
    intro i hi
    obtain ⟨h, -, rfl⟩ := Finset.mem_map.mp hi
    rfl
  refine footnote_18_5 (E.replica N) (fun i => hr i.1) (fun i => hc i.1) (fun i => hm i.1)
    (x' := fun i => xhat i.1) (fun i _ => hxX i) (fun i _ => (hweak i.1).1) ?_ (hmem h₀)
    hstrict ?_
  · intro i hi
    rw [hS' i hi]
    exact (hweak i.1).2
  · refine ⟨(N : ℝ)⁻¹ • y, hst.1.2.2 y hy _ (inv_nonneg.mpr hN.le), ?_⟩
    simp only [hS, Finset.sum_map, he]
    change ∑ h, xhat h = (N : ℝ)⁻¹ • y + ∑ h, E.ω h
    have htot : ∑ h, ∑ j, x (h, j) = y + ∑ h, (N : ℝ) • E.ω h := by
      rw [← Fintype.sum_prod_type', hsum]
      congr 1
      rw [Fintype.sum_prod_type]
      simp only [CoreEconomy.replica, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        Nat.cast_smul_eq_nsmul]
    simp only [hxhat]
    rw [← Finset.smul_sum, htot, smul_add, ← Finset.smul_sum, smul_smul,
      inv_mul_cancel₀ hN.ne', one_smul]

/-! ### Type allocations (p. 657) -/

/-- **Section 18.B** (MWG, p. 657). If the type allocation `x` is feasible (`∑ₕ xₕ = y + ∑ₕ ωₕ`),
the induced equal-treatment allocation is feasible in every replica:
`∑ₕ N xₕ = N y + N ∑ₕ ωₕ` with `N y ∈ Y` by constant returns. -/
theorem replica_isFeasible_typeAlloc {H : Type*} [Fintype H] (E : CoreEconomy H L)
    (hY : IsCRSTechnology E.Y) {x : H → Fin L → ℝ} (hx : E.IsFeasible x) (N : ℕ) :
    (E.replica N).IsFeasible (typeAlloc x N) := by
  obtain ⟨hxX, y, hy, hsum⟩ := hx
  refine ⟨fun i => hxX i.1, (N : ℝ) • y, hY.2.2 y hy _ (Nat.cast_nonneg N), ?_⟩
  simp only [typeAlloc, CoreEconomy.replica, Fintype.sum_prod_type, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin]
  rw [← Finset.smul_sum, ← Finset.smul_sum, hsum, smul_add, Nat.cast_smul_eq_nsmul]

/-- **Section 18.B** (MWG, p. 657). By Proposition 18.B.2 the core allocations of the `N`-replica
(`N ≥ 1`) are the equal-treatment allocations of the type allocations in `C_N`. -/
theorem core_replica_eq_typeAlloc {H : Type*} [Fintype H] (E : CoreEconomy H L) (hst : E.Standing)
    {N : ℕ} (hN : 1 ≤ N) {x : H × Fin N → Fin L → ℝ} (hx : x ∈ (E.replica N).core) :
    ∃ xbar ∈ E.CN N, x = typeAlloc xbar N := by
  have het := proposition_18_B_2 E hst hx
  set xbar : H → Fin L → ℝ := fun h => x (h, ⟨0, hN⟩) with hxbar
  have hxe : x = typeAlloc xbar N := funext fun i => het i.1 i.2 ⟨0, hN⟩
  refine ⟨xbar, ⟨⟨fun h => hx.1.1 (h, ⟨0, hN⟩), ?_⟩, hxe ▸ hx⟩, hxe⟩
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨-, y, hy, hsum⟩ := hx.1
  have hsumT : ∑ i : H × Fin N, x i = (N : ℝ) • ∑ h, xbar h := by
    rw [hxe]
    simp only [typeAlloc, Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ, Finset.smul_sum]
  have hsumω : ∑ i : H × Fin N, (E.replica N).ω i = (N : ℝ) • ∑ h, E.ω h := by
    simp only [CoreEconomy.replica, Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ, Finset.smul_sum]
  refine ⟨(N : ℝ)⁻¹ • y, hst.1.2.2 y hy _ (inv_nonneg.mpr hN'.le), ?_⟩
  rw [hsumT, hsumω] at hsum
  have := congrArg (fun v => (N : ℝ)⁻¹ • v) hsum
  simp only [smul_add, smul_smul, inv_mul_cancel₀ hN'.ne', one_smul] at this
  exact this

/-- **Section 18.B** (MWG, p. 657). `C_{N+1} ⊆ C_N`: a type allocation blocked in the `N`-replica
is blocked in the `(N+1)`-replica by a coalition of the same composition. -/
theorem CN_succ_subset {H : Type*} [Fintype H] (E : CoreEconomy H L) (hY : IsCRSTechnology E.Y)
    (N : ℕ) : E.CN (N + 1) ⊆ E.CN N := by
  classical
  rintro x ⟨hx, -, hcore⟩
  refine ⟨hx, replica_isFeasible_typeAlloc E hY hx N, ?_⟩
  rintro S ⟨hS, x', hx', y, hy, hsum⟩
  set e : H × Fin N ↪ H × Fin (N + 1) :=
    ⟨fun i => (i.1, i.2.castSucc), fun a b hab => by
      obtain ⟨h1, h2⟩ := Prod.ext_iff.mp hab
      exact Prod.ext h1 (Fin.castSucc_injective N h2)⟩ with he
  set x'' : H × Fin (N + 1) → Fin L → ℝ :=
    fun i => if hi : (i.2 : ℕ) < N then x' (i.1, ⟨i.2, hi⟩) else 0 with hx''
  have hx''e : ∀ j, x'' (e j) = x' j := by
    intro j
    change (if hi : ((j.2.castSucc : Fin (N + 1)) : ℕ) < N then
      x' (j.1, ⟨(j.2.castSucc : ℕ), hi⟩) else 0) = x' j
    simp
  apply hcore (S.map e)
  refine ⟨hS.map, x'', fun i hi => ?_, y, hy, ?_⟩
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
    rw [hx''e]
    exact hx' j hj
  · rw [Finset.sum_map, Finset.sum_map]
    simp only [hx''e]
    exact hsum

/-- **Section 18.B** (MWG, p. 657; Exercise 18.B.3). For `N ≥ 1`, the type allocation `x` with
prices `p` is a Walrasian equilibrium of the economy of types iff the induced equal-treatment
allocation is a Walrasian equilibrium of the `N`-replica with the same prices. -/
theorem isWalrasEqm_typeAlloc_iff {H : Type*} [Fintype H] (E : CoreEconomy H L)
    (hY : IsCRSTechnology E.Y) {N : ℕ} (hN : 1 ≤ N) (x : H → Fin L → ℝ) (p : Fin L → ℝ) :
    E.IsWalrasEqm x p ↔ (E.replica N).IsWalrasEqm (typeAlloc x N) p := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hsumT : ∑ i : H × Fin N, typeAlloc x N i = (N : ℝ) • ∑ h, x h := by
    simp only [typeAlloc, Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ, Finset.smul_sum]
  have hsumω : ∑ i : H × Fin N, (E.replica N).ω i = (N : ℝ) • ∑ h, E.ω h := by
    simp only [CoreEconomy.replica, Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ, Finset.smul_sum]
  constructor
  · rintro ⟨⟨y, hy, hsum, hmax⟩, hx⟩
    have h0 := profit_eq_zero_of_max hY hy hmax
    refine ⟨⟨(N : ℝ) • y, hY.2.2 y hy _ hN'.le, ?_, fun y' hy' => ?_⟩, fun i => hx i.1⟩
    · rw [hsumT, hsumω, hsum, smul_add]
    · rw [dotProduct_smul, smul_eq_mul, h0, mul_zero]
      exact (hmax y' hy').trans h0.le
  · rintro ⟨⟨y, hy, hsum, hmax⟩, hx⟩
    have h0 := profit_eq_zero_of_max hY hy hmax
    refine ⟨⟨(N : ℝ)⁻¹ • y, hY.2.2 y hy _ (inv_nonneg.mpr hN'.le), ?_, fun y' hy' => ?_⟩,
      fun h => hx (h, ⟨0, hN⟩)⟩
    · rw [hsumT, hsumω] at hsum
      have := congrArg (fun v => (N : ℝ)⁻¹ • v) hsum
      simp only [smul_add, smul_smul, inv_mul_cancel₀ hN'.ne', one_smul] at this
      exact this
    · rw [dotProduct_smul, smul_eq_mul, h0, mul_zero]
      exact (hmax y' hy').trans h0.le

/-- **Section 18.B** (MWG, p. 657; Exercise 18.B.3). The set of Walrasian type allocations does
not depend on `N ≥ 1`: it is the set of Walrasian allocations of the economy of types. -/
theorem walrasTypeAllocs_eq {H : Type*} [Fintype H] (E : CoreEconomy H L)
    (hY : IsCRSTechnology E.Y) {N : ℕ} (hN : 1 ≤ N) :
    {x | (E.replica N).IsWalrasAlloc (typeAlloc x N)} = {x | E.IsWalrasAlloc x} := by
  ext x
  exact ⟨fun ⟨p, hp⟩ => ⟨p, (isWalrasEqm_typeAlloc_iff E hY hN x p).2 hp⟩,
    fun ⟨p, hp⟩ => ⟨p, (isWalrasEqm_typeAlloc_iff E hY hN x p).1 hp⟩⟩

/-- **Section 18.B** (MWG, p. 657). Walrasian type allocations belong to `C_N` for every `N`
(Proposition 18.B.1 in each replica). -/
theorem walras_mem_CN {H : Type*} [Fintype H] (E : CoreEconomy H L) (hY : IsCRSTechnology E.Y)
    {x : H → Fin L → ℝ} (hx : E.IsWalrasAlloc x) (N : ℕ) : x ∈ E.CN N := by
  obtain ⟨p, hp⟩ := hx
  have hfe : E.IsFeasible x := (proposition_18_B_1 E hY hp).1
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · refine ⟨hfe, replica_isFeasible_typeAlloc E hY hfe 0, fun S hS => ?_⟩
    obtain ⟨i, -⟩ := hS.1
    exact i.2.elim0
  · exact ⟨hfe, proposition_18_B_1 (E.replica N) hY
      ((isWalrasEqm_typeAlloc_iff E hY hN x p).1 hp)⟩

/-! ### Exercise 18.B.3 -/

/-- **Exercise 18.B.3** (MWG, p. 685). Directly (without core arguments): in a Walrasian
equilibrium, two consumers with the same rational, strictly convex preferences on `ℝ^L₊` and the
same endowments get the same bundle (if they differed, the midpoint would be affordable and
strictly preferred). Continuity is not needed. -/
theorem exercise_18_B_3 {ι : Type*} [Fintype ι] (E : CoreEconomy ι L) {x : ι → Fin L → ℝ}
    {p : Fin L → ℝ} (h : E.IsWalrasEqm x p) {i j : ι}
    (hr : RationalOn (nonnegOrthant L) (E.pref i))
    (hsc : PrefStrictlyConvex (nonnegOrthant L) (E.pref i)) (hpref : E.pref i = E.pref j)
    (hω : E.ω i = E.ω j) : x i = x j := by
  by_contra hne
  have hi := h.2 i
  have hj := h.2 j
  rw [← hpref, ← hω] at hj
  have hmid : (1 / 2 : ℝ) • x i + (1 - 1 / 2 : ℝ) • x j ∈
      budgetSetOn (nonnegOrthant L) p (p ⬝ᵥ E.ω i) := by
    refine ⟨convex_nonnegOrthant L hi.1.1 hj.1.1 (by norm_num) (by norm_num) (by norm_num), ?_⟩
    rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    nlinarith [hi.1.2, hj.1.2]
  have hrefl : E.pref i (x i) (x i) := (hr.1 _ hi.1.1 _ hi.1.1).elim id id
  have hs := hsc (x i) hi.1.1 (x i) hi.1.1 (x j) hj.1.1 hrefl (hj.2 (x i) hi.1) hne (1 / 2)
    (by norm_num) (by norm_num)
  exact hs.2 (hi.2 _ hmid)

/-- **Exercise 18.B.3** (MWG, p. 685). Walrasian allocations of a replica economy (rational,
strictly convex preferences) have the equal-treatment property. -/
theorem replica_walras_equalTreatment {H : Type*} [Fintype H] (E : CoreEconomy H L)
    (hr : ∀ h, RationalOn (nonnegOrthant L) (E.pref h))
    (hsc : ∀ h, PrefStrictlyConvex (nonnegOrthant L) (E.pref h)) {N : ℕ}
    {x : H × Fin N → Fin L → ℝ} (hx : (E.replica N).IsWalrasAlloc x) : EqualTreatment x := by
  obtain ⟨p, hp⟩ := hx
  intro h m n
  exact exercise_18_B_3 (E.replica N) hp (hr h) (hsc h) rfl rfl

/-! ### Exercise 18.B.2 -/

/-- The quasilinear utility `u(x, m) = 2√x + m` of Exercise 18.B.2. -/
noncomputable def ex18B2U (x : Fin 2 → ℝ) : ℝ := 2 * Real.sqrt (x 0) + x 1

/-- `u(a, b) = 2√a + b`. -/
theorem ex18B2U_vec (a b : ℝ) : ex18B2U ![a, b] = 2 * Real.sqrt a + b := rfl

/-- The economy of Exercise 18.B.2: three consumers with `u = 2√x + m` on `ℝ²₊`, endowments
`(0, 2)`, `(0, 2)`, `(3, 2)`, pure exchange. -/
noncomputable def ex18B2Economy : CoreEconomy (Fin 3) 2 where
  pref := fun _ => utilityPref ex18B2U
  ω := ![![0, 2], ![0, 2], ![3, 2]]
  Y := nonposOrthant 2

/-- The allocation `(1, 1)`, `(1, 1/2)`, `(1, 9/2)`. -/
noncomputable def ex18B2Alloc : Fin 3 → Fin 2 → ℝ := ![![1, 1], ![1, 1 / 2], ![1, 9 / 2]]

/-- `u = 2√x + m` is strictly increasing on `ℝ²₊` for the strong order. -/
theorem ex18B2U_lt_of_le_of_ne {x y : Fin 2 → ℝ} (hx : x ∈ nonnegOrthant 2) (hxy : x ≤ y)
    (hne : y ≠ x) : ex18B2U x < ex18B2U y := by
  unfold ex18B2U
  have h0 := Real.sqrt_le_sqrt (hxy 0)
  rcases (hxy 0).lt_or_eq with h | h
  · have := Real.sqrt_lt_sqrt (hx 0) h
    linarith [hxy 1]
  · have h1 : x 1 < y 1 := by
      refine lt_of_le_of_ne (hxy 1) fun h1 => hne (funext fun l => ?_)
      fin_cases l
      · exact h.symm
      · exact h1.symm
    rw [h]
    linarith

/-- The economy of Exercise 18.B.2 satisfies the standing assumptions of Section 18.B:
preferences are rational, continuous, strictly convex and strongly monotone. -/
theorem ex18B2Economy_standing : ex18B2Economy.Standing := by
  refine ⟨isCRSTechnology_nonposOrthant, fun i => ⟨fun l => ?_, rationalOn_utilityPref _ _,
    prefContinuous_utilityPref (by unfold ex18B2U; fun_prop), ?_, ?_⟩⟩
  · fin_cases i <;> fin_cases l <;> norm_num [ex18B2Economy]
  · intro x _ y hy z hz hyx hzx hne α h0 h1
    change ex18B2U x ≤ ex18B2U y at hyx
    change ex18B2U x ≤ ex18B2U z at hzx
    have hb : (0 : ℝ) < 1 - α := by linarith
    have hlt : ex18B2U x < ex18B2U (α • y + (1 - α) • z) := by
      unfold ex18B2U at hyx hzx ⊢
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      by_cases h00 : y 0 = z 0
      · have h11 : y 1 ≠ z 1 := fun h11 => hne (funext fun l => by
          fin_cases l
          · exact h00
          · exact h11)
        rw [← h00, ← add_mul, add_sub_cancel, one_mul]
        rw [← h00] at hzx
        rcases lt_or_gt_of_ne h11 with h | h
        · nlinarith [mul_pos hb (sub_pos.mpr h)]
        · nlinarith [mul_pos h0 (sub_pos.mpr h)]
      · have hc := Real.strictConcaveOn_sqrt.2 (Set.mem_Ici.mpr (hy 0)) (Set.mem_Ici.mpr (hz 0))
          h00 h0 hb (by ring)
        simp only [smul_eq_mul] at hc
        nlinarith
    exact ⟨hlt.le, fun h => absurd h (not_le.mpr hlt)⟩
  · intro x hx y _ hxy hne
    have hlt := ex18B2U_lt_of_le_of_ne hx hxy hne
    exact ⟨hlt.le, fun h => absurd h (not_le.mpr hlt)⟩

/-- **Exercise 18.B.2** (MWG, p. 685), the transferable-utility bound: if the coalition `S` blocks
`x` in the economy of Exercise 18.B.2, then for every `c > 0`,
`∑_{i∈S} uᵢ(xᵢ) < ∑_{i∈S} (ωᵢ₁/c + c + ωᵢ₂)` (from `2√a ≤ a/c + c` and free disposal). -/
theorem ex18B2_tu_bound {S : Finset (Fin 3)} {x : Fin 3 → Fin 2 → ℝ}
    (hb : ex18B2Economy.Blocks S x) {c : ℝ} (hc : 0 < c) :
    ∑ i ∈ S, ex18B2U (x i) <
      ∑ i ∈ S, (ex18B2Economy.ω i 0 / c + c + ex18B2Economy.ω i 1) := by
  obtain ⟨hS, x', hx', y, hy, hsum⟩ := hb
  have hlt : ∑ i ∈ S, ex18B2U (x i) < ∑ i ∈ S, ex18B2U (x' i) :=
    Finset.sum_lt_sum_of_nonempty hS fun i hi => lt_of_not_ge (hx' i hi).2.2
  have hle : ∀ i ∈ S, ex18B2U (x' i) ≤ x' i 0 / c + c + x' i 1 := by
    intro i hi
    have h := two_mul_sqrt_le (x' i 0) c ((hx' i hi).1 0)
    unfold ex18B2U
    have : 2 * Real.sqrt (x' i 0) ≤ x' i 0 / c + c := by
      rw [div_add' _ _ _ hc.ne', le_div_iff₀ hc]
      nlinarith
    linarith
  have e0 := congrFun hsum 0
  have e1 := congrFun hsum 1
  simp only [Finset.sum_apply, Pi.add_apply] at e0 e1
  have hy0 : y 0 ≤ 0 := hy 0
  have hy1 : y 1 ≤ 0 := hy 1
  have h2 : ∑ i ∈ S, (x' i 0 / c + c + x' i 1) ≤
      ∑ i ∈ S, (ex18B2Economy.ω i 0 / c + c + ex18B2Economy.ω i 1) := by
    simp only [Finset.sum_add_distrib, ← Finset.sum_div]
    rw [e0, e1]
    have : (y 0 + ∑ i ∈ S, ex18B2Economy.ω i 0) / c ≤ (∑ i ∈ S, ex18B2Economy.ω i 0) / c :=
      div_le_div_of_nonneg_right (by linarith) hc.le
    linarith
  linarith [Finset.sum_le_sum hle]

/-- The utilities of the allocation of Exercise 18.B.2: `3`, `5/2`, `13/2`. -/
theorem ex18B2_util (i : Fin 3) : ex18B2U (ex18B2Alloc i) = ![3, 5 / 2, 13 / 2] i := by
  fin_cases i
  · change ex18B2U ![1, 1] = 3
    rw [ex18B2U_vec, Real.sqrt_one]; norm_num
  · change ex18B2U ![1, 1 / 2] = 5 / 2
    rw [ex18B2U_vec, Real.sqrt_one]; norm_num
  · change ex18B2U ![1, 9 / 2] = 13 / 2
    rw [ex18B2U_vec, Real.sqrt_one]; norm_num

/-- **Exercise 18.B.2(i)** (MWG, p. 685). In the three-consumer exchange economy
`ex18B2Economy` (continuous, strictly convex, strongly monotone preferences), the allocation
`(1, 1)`, `(1, 1/2)`, `(1, 9/2)` is in the core, but consumers 1 and 2, who have the same
preferences and endowments, get different bundles: the core need not have the equal-treatment
property outside replica economies. -/
theorem exercise_18_B_2a :
    ex18B2Economy.Standing ∧ ex18B2Alloc ∈ ex18B2Economy.core ∧
      ex18B2Economy.pref 0 = ex18B2Economy.pref 1 ∧ ex18B2Economy.ω 0 = ex18B2Economy.ω 1 ∧
      ex18B2Alloc 0 ≠ ex18B2Alloc 1 := by
  classical
  refine ⟨ex18B2Economy_standing, ⟨⟨fun i l => ?_, 0, fun _ => le_rfl, ?_⟩, fun S hb => ?_⟩,
    rfl, rfl, fun h => ?_⟩
  · fin_cases i <;> fin_cases l <;> norm_num [ex18B2Alloc]
  · funext l
    fin_cases l <;> simp [ex18B2Alloc, ex18B2Economy, Fin.sum_univ_three] <;> norm_num
  · -- for every coalition, a tangent point `c` for which the bound fails
    have key : ∃ c : ℝ, 0 < c ∧ ∑ i ∈ S, (ex18B2Economy.ω i 0 / c + c + ex18B2Economy.ω i 1) ≤
        ∑ i ∈ S, ex18B2U (ex18B2Alloc i) := by
      simp only [ex18B2_util]
      simp only [← Finset.sum_ite_mem_eq S, Fin.sum_univ_three]
      by_cases h2 : (2 : Fin 3) ∈ S
      · by_cases h0 : (0 : Fin 3) ∈ S
        · by_cases h1 : (1 : Fin 3) ∈ S
          · exact ⟨1, by norm_num, by simp [h0, h1, h2, ex18B2Economy]; norm_num⟩
          · exact ⟨5 / 4, by norm_num, by simp [h0, h1, h2, ex18B2Economy]; norm_num⟩
        · by_cases h1 : (1 : Fin 3) ∈ S
          · exact ⟨5 / 4, by norm_num, by simp [h0, h1, h2, ex18B2Economy]; norm_num⟩
          · exact ⟨2, by norm_num, by simp [h0, h1, h2, ex18B2Economy]; norm_num⟩
      · refine ⟨1 / 2, by norm_num, ?_⟩
        by_cases h0 : (0 : Fin 3) ∈ S <;> by_cases h1 : (1 : Fin 3) ∈ S <;>
          simp [h0, h1, h2, ex18B2Economy] <;> norm_num
    obtain ⟨c, hc, hle⟩ := key
    exact absurd (ex18B2_tu_bound hb hc) (not_lt.mpr hle)
  · have := congrFun h 1
    norm_num [ex18B2Alloc] at this

/-- **Exercise 18.B.2(ii)** (MWG, p. 685). No such example exists with only two consumers: in a
two-consumer economy with a constant returns technology, if the consumers have the same rational,
strictly convex preferences and the same endowments, every core allocation gives them the same
bundle (otherwise the less well-off consumer alone could produce the average bundle
`(xᵢ + xⱼ)/2 = y/2 + ω`). -/
theorem exercise_18_B_2b {ι : Type*} [Fintype ι] (hcard : Fintype.card ι = 2)
    (E : CoreEconomy ι L) (hY : IsCRSTechnology E.Y) {i j : ι} (hij : i ≠ j)
    (hr : RationalOn (nonnegOrthant L) (E.pref i))
    (hsc : PrefStrictlyConvex (nonnegOrthant L) (E.pref i)) (hpref : E.pref i = E.pref j)
    (hω : E.ω i = E.ω j) {x : ι → Fin L → ℝ} (hx : x ∈ E.core) : x i = x j := by
  classical
  by_contra hne
  obtain ⟨⟨hxX, y, hy, hsum⟩, hcore⟩ := hx
  have huniv : (Finset.univ : Finset ι) = {i, j} := by
    symm
    apply Finset.eq_univ_of_card
    rw [Finset.card_pair hij, hcard]
  rw [huniv, Finset.sum_pair hij, Finset.sum_pair hij, ← hω] at hsum
  set a : Fin L → ℝ := (1 / 2 : ℝ) • x i + (1 - 1 / 2 : ℝ) • x j with ha
  have haX : a ∈ nonnegOrthant L :=
    convex_nonnegOrthant L (hxX i) (hxX j) (by norm_num) (by norm_num) (by norm_num)
  have hay : a = (1 / 2 : ℝ) • y + E.ω i := by
    rw [ha, show (1 - 1 / 2 : ℝ) = 1 / 2 by norm_num, ← smul_add, hsum, smul_add, ← two_smul ℝ,
      smul_smul]
    norm_num
  have hrefl : ∀ k, E.pref i (x k) (x k) := fun k => (hr.1 _ (hxX k) _ (hxX k)).elim id id
  -- the consumer who is (weakly) worse off blocks on her own
  have hblock : ∀ k, E.ω k = E.ω i → E.pref k = E.pref i → Strict (E.pref i) a (x k) →
      E.Blocks {k} x := by
    intro k hωk hpk hs
    refine ⟨Finset.singleton_nonempty k, fun _ => a, fun l hl => ?_,
      (1 / 2 : ℝ) • y, hY.2.2 y hy _ (by norm_num), ?_⟩
    · rw [Finset.mem_singleton] at hl
      subst hl
      rw [hpk]
      exact ⟨haX, hs⟩
    · rw [Finset.sum_singleton, Finset.sum_singleton, hωk, hay]
  rcases hr.1 (x i) (hxX i) (x j) (hxX j) with h | h
  · have hs := hsc (x j) (hxX j) (x i) (hxX i) (x j) (hxX j) h (hrefl j) hne (1 / 2)
      (by norm_num) (by norm_num)
    exact hcore {j} (hblock j hω.symm hpref.symm hs)
  · have hs := hsc (x i) (hxX i) (x i) (hxX i) (x j) (hxX j) (hrefl i) h hne (1 / 2)
      (by norm_num) (by norm_num)
    exact hcore {i} (hblock i rfl rfl hs)

end MWG.CoreFoundations
