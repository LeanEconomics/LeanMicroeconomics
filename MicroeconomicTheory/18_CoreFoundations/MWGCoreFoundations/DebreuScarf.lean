/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGCoreFoundations.EqualTreatment

/-!
# The Debreu-Scarf core convergence theorem (MWG Section 18.B, pp. 657-659)

**Proposition 18.B.3** (p. 657) states: if the feasible type allocation `x*` is in `C_N` for every
`N = 1, 2, ...`, then `x*` is a Walrasian equilibrium allocation, under the standing assumptions of
Section 18.B, which only ask `ωₕ ≥ 0`.

* As printed the proposition is false (`proposition_18_B_3_false`): with one type, two goods,
  `ω = (1, 0)`, `u = √x₁ + √x₂` and `Y = -ℝ²₊` (standing assumptions hold), the no-trade
  allocation `x* = ω` lies in every `C_N` (`oneZero_mem_core`: nobody can do better than `(1, 0)`
  with only good 1 available) but is not Walrasian at any price vector (`not_maximal_one_zero`:
  the marginal utility of good 2 at `x₂ = 0` is infinite, so a small trade always pays when good 2
  is not free, and when it is free `(1, 1)` is affordable).
* The corrected statement `proposition_18_B_3` adds `ωₕ ≫ 0` for every type (the assumption of
  Debreu and Scarf; the book's special-case proof assumes it in a stronger form) and is proved in
  the full generality of Section 18.B (any convex constant returns `Y`, continuous, strictly
  convex, strongly monotone preferences, any number of goods and types). The proof: the convex
  hull `Γ` of the improving net trades `{z : z + ωₕ ≻ₕ x*ₕ}` does not meet `Y - ℝ^L₊₊`, because
  a point of the intersection, after grouping by type (`exists_type_combination`) and rounding the
  weights down (`exists_rounding`), gives a blocking coalition of a large replica
  (`disjoint_improving_trades`); separating the two convex sets gives prices `p ≥ 0`, `p ≠ 0`,
  with `p·y ≤ 0` on `Y` and `p·z ≥ 0` on `Γ`, hence a quasi-equilibrium, and `p·ωₕ > 0` turns it
  into an equilibrium (cheaper point argument).
-/

namespace MWG.CoreFoundations

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.Production MWG.WelfareTheorems
open Kreps.PreferenceProperties

variable {L : ℕ}

/-! ### The counterexample to Proposition 18.B.3 as printed -/

/-- At any prices `p`, the bundle `(1, 0)` is not maximal for `√x₁ + √x₂` in the budget set
`{x ≥ 0 : p·x ≤ p·(1, 0)}`. -/
theorem not_maximal_one_zero (p : Fin 2 → ℝ) :
    ¬ IsMaximalFor (utilityPref sqrtU) (budgetSetOn (nonnegOrthant 2) p (p ⬝ᵥ ![1, 0]))
      ![1, 0] := by
  intro h
  have hu : sqrtU ![1, 0] = 1 := by rw [sqrtU_vec, Real.sqrt_one, Real.sqrt_zero, add_zero]
  have hw : p ⬝ᵥ ![1, 0] = p 0 := by rw [dot_two]; simp
  -- any affordable bundle with utility above `1` contradicts maximality
  have key : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → p 0 * a + p 1 * b ≤ p 0 →
      1 < Real.sqrt a + Real.sqrt b → False := by
    intro a b ha hb hab hgt
    have hmem : (![a, b] : Fin 2 → ℝ) ∈ budgetSetOn (nonnegOrthant 2) p (p ⬝ᵥ ![1, 0]) := by
      refine ⟨fun l => by fin_cases l <;> simpa, ?_⟩
      rw [hw, dot_two]
      simpa using hab
    have := h.2 _ hmem
    change sqrtU ![a, b] ≤ sqrtU ![1, 0] at this
    rw [hu, sqrtU_vec] at this
    linarith
  rcases le_or_gt (p 1) 0 with hp1 | hp1
  · refine key 1 1 zero_le_one zero_le_one (by linarith) ?_
    rw [Real.sqrt_one]
    norm_num
  rcases le_or_gt (p 0) 0 with hp0 | hp0
  · refine key 2 0 (by norm_num) le_rfl (by linarith) ?_
    rw [Real.sqrt_zero, add_zero]
    exact Real.lt_sqrt_of_sq_lt (by norm_num)
  · -- a small trade: give up `t` of good 1 for `t·p₁/p₂` of good 2
    set r := p 0 / p 1 with hr
    have hr0 : 0 < r := div_pos hp0 hp1
    set t := min (1 / 2) (r / 2) with ht
    have ht0 : 0 < t := lt_min (by norm_num) (by linarith)
    have ht1 : t ≤ 1 / 2 := min_le_left _ _
    have ht2 : t ≤ r / 2 := min_le_right _ _
    refine key (1 - t) (t * r) (by linarith) (by positivity) ?_ ?_
    · have : p 1 * (t * r) = t * p 0 := by
        rw [hr]
        field_simp
      nlinarith
    · have h1 : 1 - t ≤ Real.sqrt (1 - t) := by
        rw [Real.le_sqrt (by linarith) (by linarith)]
        nlinarith
      have h2 : t < Real.sqrt (t * r) := by
        rw [Real.lt_sqrt ht0.le]
        nlinarith
      linarith

/-- If every consumer has utility `√x₁ + √x₂` and endowment `(1, 0)` and `Y = -ℝ²₊`, the no-trade
allocation is in the core: a blocking coalition would need more than one unit of good 1 per
member, as good 2 is not available. -/
theorem oneZero_mem_core {ι : Type*} [Fintype ι] (E : CoreEconomy ι 2)
    (hpref : ∀ i, E.pref i = utilityPref sqrtU) (hω : ∀ i, E.ω i = ![1, 0])
    (hY : E.Y = nonposOrthant 2) : (fun _ => ![1, 0]) ∈ E.core := by
  refine ⟨⟨fun _ l => by fin_cases l <;> norm_num, 0, hY ▸ fun _ => le_rfl, ?_⟩, ?_⟩
  · simp [hω]
  rintro S ⟨hS, x', hx', y, hy, hsum⟩
  rw [hY] at hy
  have e0 := congrFun hsum 0
  have e1 := congrFun hsum 1
  simp only [Finset.sum_apply, Pi.add_apply, hω] at e0 e1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Finset.sum_const_zero,
    add_zero] at e0 e1
  -- nobody in `S` gets good 2
  have h1 : ∀ i ∈ S, x' i 1 = 0 := by
    have hle : ∑ i ∈ S, x' i 1 ≤ 0 := by rw [e1]; exact hy 1
    have := (Finset.sum_eq_zero_iff_of_nonneg fun i hi => (hx' i hi).1 1).mp
      (le_antisymm hle (Finset.sum_nonneg fun i hi => (hx' i hi).1 1))
    exact this
  have hgt : ∀ i ∈ S, (1 : ℝ) < x' i 0 := by
    intro i hi
    have hs := (hx' i hi).2.2
    rw [hpref] at hs
    change ¬ sqrtU (x' i) ≤ sqrtU ![1, 0] at hs
    rw [sqrtU_two, sqrtU_vec, h1 i hi, Real.sqrt_one, Real.sqrt_zero, add_zero,
      add_zero] at hs
    by_contra hle
    push Not at hle
    exact hs (Real.sqrt_le_one.mpr hle)
  have := Finset.sum_lt_sum_of_nonempty hS hgt
  rw [e0] at this
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at this
  linarith [hy 0]

/-- The economy of types of the counterexample: one type, `u = √x₁ + √x₂`, `ω = (1, 0)`,
`Y = -ℝ²₊`. -/
noncomputable def dsEconomy : CoreEconomy (Fin 1) 2 := sqrtEconomy fun _ => ![1, 0]

/-- **Proposition 18.B.3** (MWG, p. 657) is false as printed (with `ωₕ ≥ 0` only): the economy
`dsEconomy` satisfies the standing assumptions of Section 18.B, the type allocation `x* = ω`
(no trade) belongs to `C_N` for every `N`, but it is not a Walrasian equilibrium allocation. -/
theorem proposition_18_B_3_false :
    dsEconomy.Standing ∧ (∀ N, (fun _ => ![1, 0]) ∈ dsEconomy.CN N) ∧
      ¬ dsEconomy.IsWalrasAlloc (fun _ => ![1, 0]) := by
  refine ⟨sqrtEconomy_standing fun _ l => by fin_cases l <;> norm_num, fun N => ⟨?_, ?_⟩, ?_⟩
  · exact (oneZero_mem_core dsEconomy (fun _ => rfl) (fun _ => rfl) rfl).1
  · exact oneZero_mem_core (dsEconomy.replica N) (fun _ => rfl) (fun _ => rfl) rfl
  · rintro ⟨p, -, hx⟩
    exact not_maximal_one_zero p (hx 0)

/-! ### Lemmas for the proof of the corrected Proposition 18.B.3 -/

/-- With strictly convex preferences, the strictly preferred set `{u ≥ 0 : u ≻ x}` is convex. -/
theorem convex_strictUpper {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hsc : PrefStrictlyConvex (nonnegOrthant L) r) {x : Fin L → ℝ}
    (hx : x ∈ nonnegOrthant L) : Convex ℝ {u | u ∈ nonnegOrthant L ∧ Strict r u x} := by
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
        exact hsc x hx y hy.1 z hz.1 hy.2.1 hz.2.1 hyz a ha' (by linarith)
    · subst hb'
      have ha1 : a = 1 := by linarith
      subst ha1
      simpa using hy.2
  · subst ha'
    have hb1 : b = 1 := by linarith
    subst hb1
    simpa using hz.2

/-- Grouping a convex combination by type: a point of the convex hull of `⋃ₕ Pₕ` (each `Pₕ`
convex, finitely many types) is `∑ₕ aₕ zₕ` with `a ≥ 0`, `∑ₕ aₕ = 1` and `zₕ ∈ Pₕ` whenever
`aₕ > 0`. -/
theorem exists_type_combination {H : Type*} [Fintype H] {P : H → Set (Fin L → ℝ)}
    (hP : ∀ h, Convex ℝ (P h)) {g : Fin L → ℝ} (hg : g ∈ convexHull ℝ (⋃ h, P h)) :
    ∃ a : H → ℝ, ∃ z : H → Fin L → ℝ, (∀ h, 0 ≤ a h) ∧ ∑ h, a h = 1 ∧
      (∀ h, 0 < a h → z h ∈ P h) ∧ ∑ h, a h • z h = g := by
  classical
  obtain ⟨K, hK, zk, w, hzB, -, hw, hw1, hcomb⟩ := eq_pos_convex_span_of_mem_convexHull hg
  have hmem : ∀ k, ∃ h, zk k ∈ P h := fun k => Set.mem_iUnion.mp (hzB ⟨k, rfl⟩)
  choose typ htyp using hmem
  set a : H → ℝ := fun h => ∑ k ∈ Finset.univ.filter (fun k => typ k = h), w k with ha
  set z : H → Fin L → ℝ :=
    fun h => (a h)⁻¹ • ∑ k ∈ Finset.univ.filter (fun k => typ k = h), w k • zk k with hz
  have ha0 : ∀ h, 0 ≤ a h := fun h => Finset.sum_nonneg fun k _ => (hw k).le
  -- `aₕ zₕ` is the sum of the terms of type `h`
  have haz : ∀ h, a h • z h = ∑ k ∈ Finset.univ.filter (fun k => typ k = h), w k • zk k := by
    intro h
    rcases (ha0 h).lt_or_eq with hpos | hzero
    · rw [hz, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
    · have hempty : Finset.univ.filter (fun k => typ k = h) = ∅ := by
        by_contra hne
        obtain ⟨k, hk⟩ := Finset.nonempty_iff_ne_empty.mpr hne
        have : 0 < a h := Finset.sum_pos (fun k _ => hw k) ⟨k, hk⟩
        linarith
      rw [hempty, Finset.sum_empty, ← hzero, zero_smul]
  refine ⟨a, z, ha0, ?_, fun h hpos => ?_, ?_⟩
  · rw [← hw1]
    exact Finset.sum_fiberwise Finset.univ typ w
  · -- `zₕ` is a convex combination of points of `Pₕ`
    have := (hP h).sum_mem (t := Finset.univ.filter (fun k => typ k = h))
      (w := fun k => (a h)⁻¹ * w k) (z := zk)
      (fun k _ => mul_nonneg (inv_nonneg.mpr (ha0 h)) (hw k).le)
      (by rw [← Finset.mul_sum, inv_mul_cancel₀ hpos.ne'])
      (fun k hk => by
        have := htyp k
        rwa [(Finset.mem_filter.mp hk).2] at this)
    simpa [hz, Finset.smul_sum, smul_smul] using this
  · simp only [haz]
    rw [Finset.sum_fiberwise Finset.univ typ (fun k => w k • zk k)]
    exact hcomb

/-- Rounding: given weights `a ≥ 0` with `∑ aₕ = 1`, vectors `zₕ` and `n ≪ 0`, there are `N ≥ 1`
and integers `kₕ = ⌊N aₕ⌋ ≤ N`, at least one of them positive, `kₕ > 0` only if `aₕ > 0`, such that
`N (∑ₕ aₕ zₕ - n) - ∑ₕ kₕ zₕ ≫ 0`. -/
theorem exists_rounding {H : Type*} [Fintype H] (a : H → ℝ) (z : H → Fin L → ℝ)
    (ha0 : ∀ h, 0 ≤ a h) (ha1 : ∑ h, a h = 1) {n : Fin L → ℝ} (hn : ∀ l, n l < 0) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ k : H → ℕ, (∀ h, k h ≤ N) ∧ (∀ h, 0 < k h → 0 < a h) ∧
      (∃ h₀, 0 < k h₀) ∧ ∀ l, 0 < ((N : ℝ) • (∑ h, a h • z h - n) - ∑ h, (k h : ℝ) • z h) l := by
  classical
  obtain ⟨h₀, hh₀⟩ : ∃ h₀, 0 < a h₀ := by
    by_contra hall
    push Not at hall
    have : ∑ h, a h ≤ 0 := Finset.sum_nonpos fun h _ => hall h
    linarith
  -- a scale making `-N n` dominate the rounding errors, with `N a_{h₀} ≥ 1`
  obtain ⟨N₁, hN₁⟩ : ∃ N₁ : ℕ, ∀ l, ∑ h, |z h l| < (N₁ : ℝ) * -n l := by
    have hex : ∀ l, ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∑ h, |z h l| < (m : ℝ) * -n l := by
      intro l
      obtain ⟨N, hN⟩ := exists_nat_gt ((∑ h, |z h l|) / -n l)
      refine ⟨N, fun m hm => ?_⟩
      have hm' : (∑ h, |z h l|) / -n l < m := lt_of_lt_of_le hN (by exact_mod_cast hm)
      rwa [div_lt_iff₀ (by linarith [hn l])] at hm'
    choose Nl hNl using hex
    exact ⟨Finset.univ.sup Nl, fun l => hNl l _ (Finset.le_sup (Finset.mem_univ l))⟩
  obtain ⟨N₂, hN₂⟩ := exists_nat_gt (1 / a h₀)
  set N := max (max N₁ N₂) 1 with hN
  have hN1 : 1 ≤ N := le_max_right _ _
  have hNN₁ : (N₁ : ℝ) ≤ N := by exact_mod_cast le_trans (le_max_left _ _) (le_max_left _ _)
  have hNN₂ : (N₂ : ℝ) ≤ N := by exact_mod_cast le_trans (le_max_right _ _) (le_max_left _ _)
  have hale : ∀ h, a h ≤ 1 := fun h => by
    rw [← ha1]
    exact Finset.single_le_sum (fun h _ => ha0 h) (Finset.mem_univ h)
  refine ⟨N, hN1, fun h => ⌊(N : ℝ) * a h⌋₊, fun h => ?_, fun h hk => ?_, ⟨h₀, ?_⟩, fun l => ?_⟩
  · apply Nat.floor_le_of_le
    calc (N : ℝ) * a h ≤ N * 1 := mul_le_mul_of_nonneg_left (hale h) (Nat.cast_nonneg N)
      _ = N := mul_one _
  · rcases (ha0 h).lt_or_eq with hpos | hzero
    · exact hpos
    · have : a h = 0 := hzero.symm
      simp [this] at hk
  · apply Nat.floor_pos.mpr
    rw [div_lt_iff₀ hh₀] at hN₂
    nlinarith
  · have hterm : ∀ h, -|z h l| ≤ ((N : ℝ) * a h - ⌊(N : ℝ) * a h⌋₊) * z h l := by
      intro h
      have h1 := Nat.floor_le (mul_nonneg (Nat.cast_nonneg N) (ha0 h))
      have h2 := Nat.lt_floor_add_one ((N : ℝ) * a h)
      have h3 : 0 ≤ (N : ℝ) * a h - ⌊(N : ℝ) * a h⌋₊ := by linarith
      have h4 : (N : ℝ) * a h - ⌊(N : ℝ) * a h⌋₊ ≤ 1 := by linarith
      have h5 := neg_abs_le (z h l)
      have h6 := le_abs_self (z h l)
      nlinarith [abs_nonneg (z h l)]
    have hsum : -∑ h, |z h l| ≤ ∑ h, ((N : ℝ) * a h - ⌊(N : ℝ) * a h⌋₊) * z h l := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_le_sum fun h _ => hterm h
    have heq : ((N : ℝ) • (∑ h, a h • z h - n) - ∑ h, (⌊(N : ℝ) * a h⌋₊ : ℝ) • z h) l =
        ∑ h, ((N : ℝ) * a h - ⌊(N : ℝ) * a h⌋₊) * z h l - N * n l := by
      simp only [Pi.sub_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, mul_sub,
        Finset.mul_sum, sub_mul, Finset.sum_sub_distrib, mul_assoc]
      ring
    rw [heq]
    have := hN₁ l
    have : (N₁ : ℝ) * -n l ≤ N * -n l := mul_le_mul_of_nonneg_right hNN₁ (by linarith [hn l])
    linarith

/-- In the `N`-replica, the coalition with the first `kₕ ≤ N` members of every type `h`: summing
a function of the type over it gives `∑ₕ kₕ fₕ`. -/
theorem sum_replica_filter {H : Type*} [Fintype H] {N : ℕ} (k : H → ℕ) (hk : ∀ h, k h ≤ N)
    (f : H → Fin L → ℝ) :
    ∑ i ∈ Finset.univ.filter (fun i : H × Fin N => (i.2 : ℕ) < k i.1), f i.1 =
      ∑ h, (k h : ℝ) • f h := by
  classical
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun h _ => ?_
  dsimp only
  rw [← Finset.sum_filter, Finset.sum_const, Fin.card_filter_val_lt, min_eq_right (hk h),
    Nat.cast_smul_eq_nsmul]

/-! ### Proposition 18.B.3, corrected -/

open scoped Pointwise in
/-- Step (a) of the proof of Proposition 18.B.3: if `x*` is in `C_N` for all `N ≥ 1`, the convex
hull of the improving net trades `⋃ₕ {z : z + ωₕ ≥ 0, z + ωₕ ≻ₕ x*ₕ}` does not meet `Y - ℝ^L₊₊`
(otherwise rounding a convex combination gives a blocking coalition of a large replica). -/
theorem disjoint_improving_trades {H : Type*} [Fintype H] (E : CoreEconomy H L)
    (hst : E.Standing) {x : H → Fin L → ℝ} (hx : ∀ N, 1 ≤ N → x ∈ E.CN N) :
    Disjoint (E.Y + {n | ∀ l, n l < 0})
      (convexHull ℝ (⋃ h, (fun z => z + E.ω h) ⁻¹'
        {u | u ∈ nonnegOrthant L ∧ Strict (E.pref h) u (x h)})) := by
  classical
  have hxX : ∀ h, x h ∈ nonnegOrthant L := (hx 1 le_rfl).1.1
  have hr := fun h => (hst.2 h).2.1
  have hm := fun h => (hst.2 h).2.2.2.2
  rw [Set.disjoint_left]
  rintro g ⟨y, hy, n, hn, rfl⟩ hg
  obtain ⟨a, z, ha0, ha1, hzP, hcomb⟩ := exists_type_combination
    (fun h => ((convex_strictUpper (hst.2 h).2.2.2.1 (hxX h)).translate_preimage_left
      (E.ω h))) hg
  obtain ⟨N, hN1, k, hkN, hka, ⟨h₀, hh₀⟩, hd⟩ := exists_rounding a z ha0 ha1 hn
  set d : Fin L → ℝ := (N : ℝ) • (∑ h, a h • z h - n) - ∑ h, (k h : ℝ) • z h with hddef
  have hy' : ∑ h, a h • z h - n = y := by rw [hcomb]; simp
  set S := Finset.univ.filter (fun i : H × Fin N => (i.2 : ℕ) < k i.1) with hS
  set i₀ : H × Fin N := (h₀, ⟨0, hN1⟩) with hi₀
  have hi₀S : i₀ ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh₀⟩
  set x' : H × Fin N → Fin L → ℝ := fun i => z i.1 + E.ω i.1 + if i = i₀ then d else 0
    with hx'
  apply (hx N hN1).2.2 S
  refine ⟨⟨i₀, hi₀S⟩, x', fun i hi => ?_, (N : ℝ) • y, hst.1.2.2 y hy _ (Nat.cast_nonneg N), ?_⟩
  · have hki : 0 < k i.1 := lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_filter.mp hi).2
    have hP := hzP i.1 (hka i.1 hki)
    by_cases hii : i = i₀
    · by_cases hd0 : d = 0
      · have : x' i = z i.1 + E.ω i.1 := by simp only [hx', hii, ↓reduceIte, hd0, add_zero]
        rw [this]
        exact hP
      · have hle : z i.1 + E.ω i.1 ≤ x' i := fun l => by
          simp only [hx', hii, ↓reduceIte, Pi.add_apply]
          linarith [hd l]
        have hne : x' i ≠ z i.1 + E.ω i.1 := by
          intro h
          apply hd0
          simpa only [hx', hii, ↓reduceIte, add_eq_left] using h
        have hX : x' i ∈ nonnegOrthant L := fun l => le_trans (hP.1 l) (hle l)
        refine ⟨hX, ?_⟩
        exact strict_of_strict_of_pref (hr i.1).2 hX hP.1 (hxX i.1)
          (hm i.1 _ hP.1 _ hX hle hne) hP.2.1
    · have : x' i = z i.1 + E.ω i.1 := by simp only [hx', hii, ↓reduceIte, add_zero]
      rw [this]
      exact hP
  · change ∑ i ∈ S, x' i = (N : ℝ) • y + ∑ i ∈ S, E.ω i.1
    simp only [hx', Finset.sum_add_distrib, Finset.sum_ite_eq', hi₀S, ↓reduceIte]
    rw [hS, sum_replica_filter k hkN z, hddef, hy']
    abel

/-- **Proposition 18.B.3** (MWG, p. 657), corrected: under the standing assumptions of Section 18.B
(any convex constant returns technology `Y`; continuous, strictly convex, strongly monotone
preferences on `ℝ^L₊`) and **strictly positive endowments** `ωₕ ≫ 0`, a type allocation `x*` that
belongs to `C_N` for every `N ≥ 1` is a Walrasian equilibrium allocation. (Without `ωₕ ≫ 0` the
statement fails: `proposition_18_B_3_false`.) -/
theorem proposition_18_B_3 {H : Type*} [Fintype H] (E : CoreEconomy H L) (hst : E.Standing)
    (hω : ∀ h l, 0 < E.ω h l) {x : H → Fin L → ℝ} (hx : ∀ N, 1 ≤ N → x ∈ E.CN N) :
    E.IsWalrasAlloc x := by
  classical
  obtain ⟨hxX, yf, hyf, hsumf⟩ := (hx 1 le_rfl).1
  have hY := hst.1
  have hr := fun h => (hst.2 h).2.1
  have hc := fun h => (hst.2 h).2.2.1
  have hm := fun h => (hst.2 h).2.2.2.2
  rcases Nat.eq_zero_or_pos L with hL | hL
  · -- no goods: every price vector works
    subst hL
    refine ⟨0, ⟨yf, hyf, hsumf, fun y' _ => by simp⟩, fun h => ⟨⟨hxX h, by simp⟩,
      fun x' _ => ?_⟩⟩
    rw [Subsingleton.elim x' (x h)]
    exact ((hr h).1 _ (hxX h) _ (hxX h)).elim id id
  set Nn : Set (Fin L → ℝ) := {n | ∀ l, n l < 0} with hNn
  have hNopen : IsOpen Nn := by
    have : Nn = ⋂ l, {n : Fin L → ℝ | n l < 0} := by ext n; simp [hNn]
    rw [this]
    exact isOpen_iInter_of_finite fun l => isOpen_lt (continuous_apply l) continuous_const
  have hNconv : Convex ℝ Nn := by
    intro a ha b hb s t hs ht hst' l
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have := ha l
    have := hb l
    rcases hs.lt_or_eq with hs' | hs'
    · nlinarith [mul_neg_of_pos_of_neg hs' (ha l), mul_nonpos_of_nonneg_of_nonpos ht (hb l).le]
    · subst hs'
      have ht1 : t = 1 := by linarith
      subst ht1
      simpa using hb l
  have hdisj := disjoint_improving_trades E hst hx
  obtain ⟨f, u, hfO, hfΓ⟩ := geometric_hahn_banach_open (hY.1.add hNconv)
    (hNopen.add_left) (convex_convexHull ℝ _) hdisj
  obtain ⟨q, hq⟩ := duality_exists_dot_of_clm f
  have hO : ∀ y ∈ E.Y, ∀ n : Fin L → ℝ, (∀ l, n l < 0) → q ⬝ᵥ y + q ⬝ᵥ n < u := by
    intro y hy n hn
    have := hfO (y + n) (Set.add_mem_add hy hn)
    rwa [hq, dotProduct_add] at this
  have hP : ∀ h, ∀ z : Fin L → ℝ, z + E.ω h ∈ nonnegOrthant L →
      Strict (E.pref h) (z + E.ω h) (x h) → u ≤ q ⬝ᵥ z := by
    intro h z h1 h2
    have := hfΓ z (subset_convexHull ℝ _ (Set.mem_iUnion.mpr ⟨h, h1, h2⟩))
    rwa [hq] at this
  have hone : q ⬝ᵥ (fun _ => (1 : ℝ)) = ∑ l, q l := by simp [dotProduct]
  have h0Y : (0 : Fin L → ℝ) ∈ E.Y := hY.2.1
  -- `q ≥ 0`
  have hq0 : ∀ l, 0 ≤ q l := by
    intro l
    by_contra hneg
    push Not at hneg
    set t := max 0 ((u + ∑ k, q k) / -q l) + 1 with ht
    have ht1 : 1 ≤ t := by linarith [le_max_left 0 ((u + ∑ k, q k) / -q l)]
    have ht2 : (u + ∑ k, q k) / -q l ≤ t - 1 := by
      linarith [le_max_right 0 ((u + ∑ k, q k) / -q l)]
    have hmem : ∀ k, ((-(Pi.single l t) - fun _ => (1 : ℝ)) : Fin L → ℝ) k < 0 := by
      intro k
      by_cases hk : k = l
      · subst hk; simp; linarith
      · simp [hk]
    have := hO 0 h0Y _ hmem
    rw [dotProduct_zero, zero_add, dotProduct_sub, dotProduct_neg, hone] at this
    have hdot1 : q ⬝ᵥ (Pi.single l t : Fin L → ℝ) = q l * t := by simp
    rw [hdot1] at this
    have hql : 0 < -q l := by linarith
    rw [div_le_iff₀ hql] at ht2
    nlinarith
  have hS0 : 0 ≤ ∑ l, q l := Finset.sum_nonneg fun l _ => hq0 l
  -- `u ≥ 0`
  have hu0 : 0 ≤ u := by
    by_contra hneg
    push Not at hneg
    set ε := -u / (∑ k, q k + 1) with hε
    have hε0 : 0 < ε := div_pos (by linarith) (by linarith)
    have := hO 0 h0Y (fun _ => -ε) (fun _ => by linarith)
    rw [dotProduct_zero, zero_add] at this
    have hdot : q ⬝ᵥ (fun _ => -ε) = -ε * ∑ k, q k := by
      simp [dotProduct, Finset.sum_mul, mul_comm]
    rw [hdot] at this
    have : -ε * ∑ k, q k ≥ u := by
      rw [hε, ge_iff_le, neg_div, neg_mul, neg_mul, neg_neg, div_mul_eq_mul_div,
        le_div_iff₀ (by linarith)]
      nlinarith
    linarith
  -- `q·y ≤ 0` on `Y`
  have hqY : ∀ y ∈ E.Y, q ⬝ᵥ y ≤ 0 := by
    intro y hy
    by_contra hpos
    push Not at hpos
    set t := max 0 ((u + ∑ k, q k) / (q ⬝ᵥ y)) + 1 with ht
    have ht0 : 0 ≤ t := by linarith [le_max_left 0 ((u + ∑ k, q k) / (q ⬝ᵥ y))]
    have ht2 : (u + ∑ k, q k) / (q ⬝ᵥ y) ≤ t - 1 := by
      linarith [le_max_right 0 ((u + ∑ k, q k) / (q ⬝ᵥ y))]
    have := hO (t • y) (hY.2.2 y hy t ht0) (fun _ => -1) (fun _ => by norm_num)
    have hdot : q ⬝ᵥ (fun _ => (-1 : ℝ)) = -∑ k, q k := by simp [dotProduct]
    rw [dotProduct_smul, smul_eq_mul, hdot] at this
    rw [div_le_iff₀ hpos] at ht2
    nlinarith
  -- `q·x*ₕ ≥ q·ωₕ`: bundles slightly above `x*ₕ` are improving
  have hL0 : (⟨0, hL⟩ : Fin L) = ⟨0, hL⟩ := rfl
  have hup : ∀ h, ∀ ε : ℝ, 0 < ε → x h + (fun _ => ε) ∈ nonnegOrthant L ∧
      Strict (E.pref h) (x h + fun _ => ε) (x h) := by
    intro h ε hε
    have hX : x h + (fun _ => ε) ∈ nonnegOrthant L := fun l => by
      simp only [Pi.add_apply]; linarith [hxX h l]
    refine ⟨hX, hm h (x h) (hxX h) _ hX (fun l => ?_) fun heq => ?_⟩
    · simp only [Pi.add_apply]; linarith
    · have := congrFun heq ⟨0, hL⟩
      simp only [Pi.add_apply, add_eq_left] at this
      linarith
  have hxω : ∀ h, q ⬝ᵥ E.ω h ≤ q ⬝ᵥ x h := by
    intro h
    refine le_of_forall_pos_le_add fun ε' hε' => ?_
    set ε := ε' / (∑ k, q k + 1) with hε
    have hε0 : 0 < ε := div_pos hε' (by linarith)
    obtain ⟨hX, hs⟩ := hup h ε hε0
    have := hP h (x h + (fun _ => ε) - E.ω h) (by simpa using hX) (by simpa using hs)
    rw [dotProduct_sub, dotProduct_add] at this
    have hdot : q ⬝ᵥ (fun _ => ε) = ε * ∑ k, q k := by
      simp only [dotProduct]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    rw [hdot] at this
    have hεS : ε * ∑ k, q k ≤ ε' := by
      rw [hε, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  -- budgets balance and the production plan maximizes profit
  have hsumq : ∑ h, (q ⬝ᵥ x h - q ⬝ᵥ E.ω h) = q ⬝ᵥ yf := by
    rw [Finset.sum_sub_distrib, ← dotProduct_sum, ← dotProduct_sum, hsumf, dotProduct_add]
    ring
  have hbal : ∀ h, q ⬝ᵥ x h - q ⬝ᵥ E.ω h = 0 := by
    have hle : ∑ h, (q ⬝ᵥ x h - q ⬝ᵥ E.ω h) ≤ 0 := by rw [hsumq]; exact hqY yf hyf
    have := (Finset.sum_eq_zero_iff_of_nonneg fun h _ => sub_nonneg.mpr (hxω h)).mp
      (le_antisymm hle (Finset.sum_nonneg fun h _ => sub_nonneg.mpr (hxω h)))
    exact fun h => this h (Finset.mem_univ h)
  have hyf0 : q ⬝ᵥ yf = 0 := by
    rw [← hsumq]
    exact Finset.sum_eq_zero fun h _ => hbal h
  refine ⟨q, ⟨yf, hyf, hsumf, fun y' hy' => by rw [hyf0]; exact hqY y' hy'⟩, fun h => ?_⟩
  -- `q ≠ 0`, hence `q·ωₕ > 0`
  have hqne : q ≠ 0 := by
    intro hq0'
    obtain ⟨hX, hs⟩ := hup h 1 one_pos
    have h1 := hP h (x h + (fun _ => 1) - E.ω h) (by simpa using hX) (by simpa using hs)
    have h2 := hO 0 h0Y (fun _ => -1) (fun _ => by norm_num)
    rw [hq0'] at h1 h2
    simp only [zero_dotProduct, add_zero] at h1 h2
    linarith
  have hqω : 0 < q ⬝ᵥ E.ω h := dotProduct_pos_of_nonneg_ne_zero hq0 hqne (hω h)
  refine isMaximalFor_of_strict_gt (hr h) (hxX h) (by linarith [hbal h]) fun x' hx' hs => ?_
  have h1 := hP h (x' - E.ω h) (by simpa using hx') (by simpa using hs)
  rw [dotProduct_sub] at h1
  rcases (show q ⬝ᵥ E.ω h ≤ q ⬝ᵥ x' by linarith).lt_or_eq with h3 | h3
  · exact h3
  exfalso
  -- the cheaper point: reduce a good with positive price held in positive quantity
  obtain ⟨m, hmpos⟩ : ∃ m, 0 < q m * x' m := by
    by_contra hall
    push Not at hall
    have : q ⬝ᵥ x' ≤ 0 := Finset.sum_nonpos fun m _ => hall m
    linarith
  have hxm : 0 < x' m := by
    by_contra hle
    push Not at hle
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (hq0 m) hle]
  have hqm : 0 < q m := by
    by_contra hle
    push Not at hle
    have : q m = 0 := le_antisymm hle (hq0 m)
    rw [this, zero_mul] at hmpos
    exact lt_irrefl 0 hmpos
  obtain ⟨δ, hδ, hmem, hs'⟩ := exists_strict_sub_single (hr h) (hc h) hx' (hxX h) hs hxm
  have h4 := hP h (x' - Pi.single m δ - E.ω h) (by simpa using hmem) (by simpa using hs')
  rw [dotProduct_sub, dotProduct_sub, ← h3] at h4
  simp only [dotProduct_single, sub_sub_cancel_left] at h4
  nlinarith

end MWG.CoreFoundations
