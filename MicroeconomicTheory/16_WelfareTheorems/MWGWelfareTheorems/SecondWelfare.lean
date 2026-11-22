/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGWelfareTheorems.FirstWelfare
import MWGClassicalDemand.AppendixMG

/-!
# The second fundamental theorem of welfare economics (MWG Section 16.D, pp. 551-554)

* **Proposition 16.D.1** (second welfare theorem): with convex production sets and convex,
  locally nonsatiated (rational) preferences, every Pareto optimal allocation is a price
  quasiequilibrium with transfers for some `p ≠ 0`, with wealth levels `wᵢ = p·x*ᵢ`. The proof
  follows the book's nine steps: the preferred sets `Vᵢ` are convex (Step 1), so are
  `V = ∑ Vᵢ` and `Y + {ω̄}` (Step 2), they are disjoint (Step 3), the separating hyperplane
  theorem (Theorem M.G.2, Chapter 3's `theorem_M_G_2_ii`) gives `p ≠ 0` and `r` (Step 4), and
  Steps 5-9 derive profit maximization and condition (ii) of Definition 16.D.1. The book's
  standing assumptions `I > 0` and the existence of the allocation give `L ≥ 1` (local
  nonsatiation fails in `ℝ⁰`), which Theorem M.G.2 needs.
* **Exercise 16.D.1** (and the small type of p. 552): under local nonsatiation, condition (ii')
  is expenditure minimization on the upper contour set.
* **Exercise 16.D.2**: local nonsatiation cannot be dropped from Proposition 16.D.1.
-/

namespace MWG.WelfareTheorems

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.Production Kreps.PreferenceProperties
open MWG.CompetitiveMarkets (Allocation)

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {L : ℕ}

/-- Transitivity through a strict preference: `z ≻ x` and `x ≿ x*` give `z ≻ x*`. -/
theorem strict_of_strict_of_pref {X : Set (Fin L → ℝ)} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (htr : ∀ x ∈ X, ∀ y ∈ X, ∀ z ∈ X, r x y → r y z → r x z) {z x xs : Fin L → ℝ}
    (hz : z ∈ X) (hx : x ∈ X) (hxs : xs ∈ X) (hzx : Strict r z x) (hxxs : r x xs) :
    Strict r z xs :=
  ⟨htr z hz x hx xs hxs hzx.1 hxxs, fun h => hzx.2 (htr x hx xs hxs z hz hxxs h)⟩

/-- Transitivity through a strict preference: `z ≿ x` and `x ≻ x*` give `z ≻ x*`. -/
theorem strict_of_pref_of_strict {X : Set (Fin L → ℝ)} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (htr : ∀ x ∈ X, ∀ y ∈ X, ∀ z ∈ X, r x y → r y z → r x z) {z x xs : Fin L → ℝ}
    (hz : z ∈ X) (hx : x ∈ X) (hxs : xs ∈ X) (hzx : r z x) (hxxs : Strict r x xs) :
    Strict r z xs :=
  ⟨htr z hz x hx xs hxs hzx hxxs.1, fun h => hxxs.2 (htr xs hxs z hz x hx h hzx)⟩

/-- The set `Vᵢ = {xᵢ ∈ Xᵢ : xᵢ ≻ᵢ x*ᵢ}` of the proof of Proposition 16.D.1. -/
def preferredSet (X : Set (Fin L → ℝ)) (r : (Fin L → ℝ) → (Fin L → ℝ) → Prop)
    (xs : Fin L → ℝ) : Set (Fin L → ℝ) :=
  {x | x ∈ X ∧ Strict r x xs}

/-- The set `V = ∑ᵢ Vᵢ` of the proof of Proposition 16.D.1. -/
def PrefEconomy.aggPreferredSet (E : PrefEconomy ι κ L) (a : Allocation ι κ L) :
    Set (Fin L → ℝ) :=
  {v | ∃ x : ι → Fin L → ℝ, (∀ i, x i ∈ preferredSet (E.X i) (E.pref i) (a.x i)) ∧
    v = ∑ i, x i}

/-- The set `Y + {ω̄}` of aggregate bundles available for consumption. -/
def PrefEconomy.availableSet (E : PrefEconomy ι κ L) : Set (Fin L → ℝ) :=
  {z | ∃ y : κ → Fin L → ℝ, (∀ j, y j ∈ E.Y j) ∧ z = E.ω + ∑ j, y j}

/-- **Proposition 16.D.1, Step 1** (MWG, p. 553). With a rational and convex preference, every
set `Vᵢ` of bundles preferred to `x*ᵢ ∈ Xᵢ` is convex. -/
theorem proposition_16_D_1_step1 {X : Set (Fin L → ℝ)} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hr : RationalOn X r) (hc : PrefConvex X r) {xs : Fin L → ℝ} (hxs : xs ∈ X) :
    Convex ℝ (preferredSet X r xs) := by
  intro x hx x' hx' α β hα hβ hαβ
  rcases hr.1 x hx.1 x' hx'.1 with hxx' | hx'x
  · -- `x ≿ x'`: the combination is in the upper contour set of `x'`
    have hrefl : r x' x' := (hr.1 x' hx'.1 x' hx'.1).elim id id
    have hm := hc x' hx'.1 ⟨hx.1, hxx'⟩ ⟨hx'.1, hrefl⟩ hα hβ hαβ
    exact ⟨hm.1, strict_of_pref_of_strict hr.2 hm.1 hx'.1 hxs hm.2 hx'.2⟩
  · have hrefl : r x x := (hr.1 x hx.1 x hx.1).elim id id
    have hm := hc x hx.1 ⟨hx.1, hrefl⟩ ⟨hx'.1, hx'x⟩ hα hβ hαβ
    exact ⟨hm.1, strict_of_pref_of_strict hr.2 hm.1 hx.1 hxs hm.2 hx.2⟩

omit [Fintype κ] in
/-- **Proposition 16.D.1, Step 2** (MWG, p. 553), for `V`: a sum of convex sets is convex. -/
theorem proposition_16_D_1_step2_V {E : PrefEconomy ι κ L} {a : Allocation ι κ L}
    (h : ∀ i, Convex ℝ (preferredSet (E.X i) (E.pref i) (a.x i))) :
    Convex ℝ (E.aggPreferredSet a) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩ α β hα hβ hαβ
  refine ⟨fun i => α • x i + β • x' i, fun i => h i (hx i) (hx' i) hα hβ hαβ, ?_⟩
  rw [Finset.sum_add_distrib, Finset.smul_sum, Finset.smul_sum]

omit [Fintype ι] in
/-- **Proposition 16.D.1, Step 2** (MWG, p. 553), for `Y + {ω̄}`. -/
theorem proposition_16_D_1_step2_Y {E : PrefEconomy ι κ L} (h : ∀ j, Convex ℝ (E.Y j)) :
    Convex ℝ E.availableSet := by
  rintro _ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩ α β hα hβ hαβ
  refine ⟨fun j => α • y j + β • y' j, fun j => h j (hy j) (hy' j) hα hβ hαβ, ?_⟩
  have : α • E.ω + β • E.ω = E.ω := by rw [← add_smul, hαβ, one_smul]
  rw [Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.smul_sum, smul_add, smul_add]
  rw [show E.ω + (α • ∑ j, y j + β • ∑ j, y' j) =
    (α • E.ω + β • E.ω) + (α • ∑ j, y j + β • ∑ j, y' j) by rw [this]]
  abel

/-- **Proposition 16.D.1, Step 3** (MWG, p. 553). At a Pareto optimum (with `I > 0`),
`V ∩ (Y + {ω̄}) = ∅`. -/
theorem proposition_16_D_1_step3 [Nonempty ι] {E : PrefEconomy ι κ L} {a : Allocation ι κ L}
    (hpo : E.IsParetoOptimal a) : Disjoint (E.aggPreferredSet a) E.availableSet := by
  rw [Set.disjoint_left]
  rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, heq⟩
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  exact hpo.2 ⟨⟨x, y⟩, ⟨⟨fun i => (hx i).1, hy⟩, heq⟩, fun i => (hx i).2.1, i₀, (hx i₀).2⟩

omit [Fintype κ] in
/-- **Proposition 16.D.1, Step 5** (MWG, p. 554). If `p·v ≥ r` on `V` and preferences are locally
nonsatiated and transitive, then `xᵢ ≿ᵢ x*ᵢ` for every `i` implies `p·(∑ᵢ xᵢ) ≥ r` (footnote 5:
`∑ᵢ {xᵢ : xᵢ ≿ᵢ x*ᵢ}` lies in the closure of `V`). -/
theorem proposition_16_D_1_step5 {E : PrefEconomy ι κ L} {a : Allocation ι κ L}
    (htr : ∀ i, ∀ x ∈ E.X i, ∀ y ∈ E.X i, ∀ z ∈ E.X i, E.pref i x y → E.pref i y z →
      E.pref i x z)
    (hlns : ∀ i, LocallyNonsatiated (E.X i) (E.pref i)) (hax : ∀ i, a.x i ∈ E.X i)
    {p : Fin L → ℝ} {r : ℝ} (hV : ∀ v ∈ E.aggPreferredSet a, r ≤ p ⬝ᵥ v)
    {x : ι → Fin L → ℝ} (hx : ∀ i, x i ∈ E.X i) (hpref : ∀ i, E.pref i (x i) (a.x i)) :
    r ≤ p ⬝ᵥ ∑ i, x i := by
  by_contra hlt
  push Not at hlt
  set δ := r - p ⬝ᵥ ∑ i, x i with hδ
  have hδ0 : 0 < δ := by linarith
  set c := ∑ l, |p l| with hc
  have hc0 : 0 ≤ c := Finset.sum_nonneg fun l _ => abs_nonneg _
  set n := (Fintype.card ι : ℝ) with hn
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  set ε := δ / ((c + 1) * (n + 1)) with hε
  have hε0 : 0 < ε := div_pos hδ0 (by positivity)
  have hex : ∀ i, ∃ z ∈ E.X i, euclidDist z (x i) ≤ ε ∧ Strict (E.pref i) z (x i) :=
    fun i => hlns i (x i) (hx i) ε hε0
  choose z hz hzd hzs using hex
  have hzV : ∑ i, z i ∈ E.aggPreferredSet a :=
    ⟨z, fun i => ⟨hz i, strict_of_strict_of_pref (htr i) (hz i) (hx i) (hax i) (hzs i)
      (hpref i)⟩, rfl⟩
  have h1 := hV _ hzV
  have h2 : p ⬝ᵥ ∑ i, z i - p ⬝ᵥ ∑ i, x i ≤ n * (c * ε) := by
    rw [dotProduct_finset_sum, dotProduct_finset_sum, ← Finset.sum_sub_distrib, hn,
      ← nsmul_eq_mul, ← Finset.card_univ, ← Finset.sum_const]
    refine Finset.sum_le_sum fun i _ => ?_
    have := (abs_le.mp (abs_dotProduct_sub_le p (x i) (z i))).2
    have h3 : c * euclidDist (z i) (x i) ≤ c * ε := mul_le_mul_of_nonneg_left (hzd i) hc0
    linarith
  have h4 : n * (c * ε) < δ := by
    have : n * (c * ε) = δ * (n * c / ((c + 1) * (n + 1))) := by
      rw [hε]; field_simp
    rw [this]
    have hfrac : n * c / ((c + 1) * (n + 1)) < 1 := by
      rw [div_lt_one (by positivity)]
      nlinarith
    nlinarith
  linarith

/-- **Proposition 16.D.1 (second fundamental theorem of welfare economics)** (MWG, p. 552).
Suppose every `Yⱼ` is convex and every `≿ᵢ` is rational, convex and locally nonsatiated (and
`I > 0`). Then for every Pareto optimal allocation `(x*, y*)` there is `p ≠ 0` such that
`(x*, y*, p)` is a price quasiequilibrium with transfers, with wealth levels `wᵢ = p·x*ᵢ`
(Step 9). -/
theorem proposition_16_D_1 [Nonempty ι] {E : PrefEconomy ι κ L} (hY : ∀ j, Convex ℝ (E.Y j))
    (hr : ∀ i, RationalOn (E.X i) (E.pref i)) (hc : ∀ i, PrefConvex (E.X i) (E.pref i))
    (hlns : ∀ i, LocallyNonsatiated (E.X i) (E.pref i)) {a : Allocation ι κ L}
    (hpo : E.IsParetoOptimal a) :
    ∃ p : Fin L → ℝ, p ≠ 0 ∧ E.IsPriceQuasiEqmWithTransfers a p (fun i => p ⬝ᵥ a.x i) := by
  classical
  obtain ⟨⟨hax, hay⟩, hclear⟩ := hpo.1
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  -- `L ≥ 1`: local nonsatiation fails in `ℝ⁰`
  have hL : 0 < L := by
    rcases Nat.eq_zero_or_pos L with h0 | h0
    · subst h0
      obtain ⟨z, -, -, hz⟩ := hlns i₀ (a.x i₀) (hax i₀) 1 one_pos
      have : z = a.x i₀ := funext fun l => l.elim0
      exact absurd (this ▸ hz.1) hz.2
    · exact h0
  -- Steps 1-3
  have hVconv := proposition_16_D_1_step2_V (E := E) (a := a)
    fun i => proposition_16_D_1_step1 (hr i) (hc i) (hax i)
  have hYconv := proposition_16_D_1_step2_Y hY
  have hdisj := proposition_16_D_1_step3 hpo
  have hVne : (E.aggPreferredSet a).Nonempty := by
    have hex : ∀ i, ∃ z ∈ E.X i, euclidDist z (a.x i) ≤ 1 ∧ Strict (E.pref i) z (a.x i) :=
      fun i => hlns i (a.x i) (hax i) 1 one_pos
    choose z hz _ hzs using hex
    exact ⟨_, z, fun i => ⟨hz i, hzs i⟩, rfl⟩
  have hYne : E.availableSet.Nonempty := ⟨_, a.y, hay, rfl⟩
  -- Step 4: the separating hyperplane
  obtain ⟨p, hp, rr, hpV, hpY⟩ := theorem_M_G_2_ii hL hVconv hYconv hVne hYne hdisj
  -- Step 5
  have step5 := fun x hx hpref => proposition_16_D_1_step5 (fun i => (hr i).2) hlns hax hpV
    (x := x) hx hpref
  have hrefl : ∀ i, E.pref i (a.x i) (a.x i) := fun i => ((hr i).1 _ (hax i) _ (hax i)).elim id id
  -- Step 6: `p·(∑ x*ᵢ) = r`
  have hstar : p ⬝ᵥ ∑ i, a.x i = rr :=
    le_antisymm (hpY _ ⟨a.y, hay, hclear⟩) (step5 a.x hax hrefl)
  refine ⟨p, hp, hp, ?_, fun j => ⟨hay j, fun yj hyj => ?_⟩, fun i => ⟨hax i, fun xi hxi hs => ?_⟩,
    hclear⟩
  · rw [← dotProduct_finset_sum, hclear, dotProduct_add, dotProduct_finset_sum]
  · -- Step 7: profit maximization
    have hmem : E.ω + ∑ k, Function.update a.y j yj k ∈ E.availableSet :=
      ⟨Function.update a.y j yj, fun k => by
        by_cases hk : k = j
        · subst hk; simpa using hyj
        · rw [Function.update_of_ne hk]; exact hay k, rfl⟩
    have h1 := hpY _ hmem
    rw [← hstar, hclear, dotProduct_add, dotProduct_add, dotProduct_finset_sum,
      dotProduct_finset_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ j),
      ← Finset.add_sum_erase _ (fun k => p ⬝ᵥ a.y k) (Finset.mem_univ j)] at h1
    have h2 : ∑ k ∈ Finset.univ.erase j, p ⬝ᵥ Function.update a.y j yj k =
        ∑ k ∈ Finset.univ.erase j, p ⬝ᵥ a.y k :=
      Finset.sum_congr rfl fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
    simp only [Function.update_self] at h1
    linarith
  · -- Step 8: anything preferred costs at least `p·x*ᵢ`
    have h1 := step5 (Function.update a.x i xi) (fun k => by
        by_cases hk : k = i
        · subst hk; simpa using hxi
        · rw [Function.update_of_ne hk]; exact hax k)
      (fun k => by
        by_cases hk : k = i
        · subst hk; simpa using hs.1
        · rw [Function.update_of_ne hk]; exact hrefl k)
    rw [← hstar, dotProduct_finset_sum, dotProduct_finset_sum,
      ← Finset.add_sum_erase _ (fun k => p ⬝ᵥ Function.update a.x i xi k) (Finset.mem_univ i),
      ← Finset.add_sum_erase _ (fun k => p ⬝ᵥ a.x k) (Finset.mem_univ i)] at h1
    have h2 : ∑ k ∈ Finset.univ.erase i, p ⬝ᵥ Function.update a.x i xi k =
        ∑ k ∈ Finset.univ.erase i, p ⬝ᵥ a.x k :=
      Finset.sum_congr rfl fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
    simp only [Function.update_self] at h1
    linarith

/-! ## Exercise 16.D.1 -/

/-- **Exercise 16.D.1** (MWG, p. 575; p. 552). If `≿` is locally nonsatiated and transitive on
`X` and `x* ∈ X`, then "`x ≻ x*` implies `p·x ≥ p·x*`" holds if and only if `x*` minimizes
expenditure at prices `p` on `{x ∈ X : x ≿ x*}`. -/
theorem exercise_16_D_1 {X : Set (Fin L → ℝ)} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hlns : LocallyNonsatiated X r) (htr : ∀ x ∈ X, ∀ y ∈ X, ∀ z ∈ X, r x y → r y z → r x z)
    {xs : Fin L → ℝ} (hxs : xs ∈ X) (p : Fin L → ℝ) :
    (∀ x ∈ X, Strict r x xs → p ⬝ᵥ xs ≤ p ⬝ᵥ x) ↔ (∀ x ∈ X, r x xs → p ⬝ᵥ xs ≤ p ⬝ᵥ x) := by
  constructor
  · intro h x hx hpref
    by_contra hlt
    obtain ⟨z, hz, hpz, hs⟩ := lns_exists_better_cheaper hlns p hx (not_le.mp hlt)
    have := h z hz (strict_of_strict_of_pref htr hz hx hxs hs hpref)
    linarith
  · exact fun h x hx hs => h x hx hs.1

/-! ## Exercise 16.D.2 -/

/-- The utility of Exercise 16.D.2: `u(x) = x` for `x ≤ 1`, `1` on `[1, 2]`, `x - 1` beyond (a
thick indifference interval). -/
noncomputable def ex16D2u (x : Fin 1 → ℝ) : ℝ := min (x 0) (max 1 (x 0 - 1))

/-- **Exercise 16.D.2** (MWG, p. 575). The one-consumer, one-firm economy: `X = ℝ₊`, utility
`ex16D2u` (continuous, nondecreasing, hence convex preferences), the convex free disposal
technology `Y = -ℝ₊` and endowment `ω̄ = 3/2`. -/
noncomputable def ex16D2Economy : PrefEconomy Unit Unit 1 :=
  PrefEconomy.ofUtility (fun _ => nonnegOrthant 1) (fun _ => ex16D2u) (fun _ => nonposOrthant 1)
    ![3 / 2]

/-- **Exercise 16.D.2** (MWG, p. 575). In `ex16D2Economy` the allocation `x* = 1`, `y* = -1/2` is
Pareto optimal, but it is neither a price equilibrium with transfers (for any `p`, including
`p = 0`) nor a price quasiequilibrium with transfers (for any `p`). The preference is continuous
and convex and `Y` is convex; the condition of Proposition 16.D.1 that fails is local
nonsatiation (at `x* = 1`). -/
theorem exercise_16_D_2 :
    ex16D2Economy.IsParetoOptimal ⟨fun _ => ![1], fun _ => ![-1 / 2]⟩ ∧
      (∀ p w, ¬ ex16D2Economy.IsPriceEqmWithTransfers ⟨fun _ => ![1], fun _ => ![-1 / 2]⟩ p w) ∧
      (∀ p w, ¬ ex16D2Economy.IsPriceQuasiEqmWithTransfers
        ⟨fun _ => ![1], fun _ => ![-1 / 2]⟩ p w) ∧
      Convex ℝ (nonposOrthant 1) ∧ ContinuousOn ex16D2u (nonnegOrthant 1) ∧
      PrefConvex (nonnegOrthant 1) (utilityPref ex16D2u) ∧
      ¬ LocallyNonsatiated (nonnegOrthant 1) (utilityPref ex16D2u) := by
  have hle1 : ∀ t : ℝ, t ≤ 3 / 2 → min t (max 1 (t - 1)) ≤ 1 := fun t ht =>
    (min_le_right _ _).trans (max_le le_rfl (by linarith))
  have hval1 : ex16D2u ![1] = 1 := by norm_num [ex16D2u]
  have hmono : Monotone fun t : ℝ => min t (max 1 (t - 1)) := fun s t hst =>
    min_le_min hst (max_le_max le_rfl (by linarith))
  -- profit maximization on `-ℝ₊` at `y* = -1/2` is impossible for `p ≠ 0`
  have hprofit : ∀ p : Fin 1 → ℝ, (![-1 / 2] : Fin 1 → ℝ) ∈ supply (nonposOrthant 1) p →
      p = 0 := by
    intro p hp
    have h0 := hp.2 0 (fun _ => le_rfl)
    have h1 := hp.2 ![-1] (fun l => by fin_cases l; norm_num)
    simp [dotProduct] at h0 h1
    funext l
    fin_cases l
    simp only [Fin.zero_eta, Fin.isValue, Pi.zero_apply]
    linarith
  refine ⟨⟨⟨⟨fun _ l => ?_, fun _ l => ?_⟩, ?_⟩, ?_⟩, fun p w h => ?_, fun p w h => ?_,
    ?_, ?_, ?_, ?_⟩
  · fin_cases l; norm_num
  · fin_cases l; norm_num
  · funext l; fin_cases l; simp [ex16D2Economy, PrefEconomy.ofUtility]; norm_num
  · rintro ⟨a', ⟨⟨hx', hy'⟩, hc'⟩, -, k, hk⟩
    apply hk.2
    have hx'le : a'.x k 0 ≤ 3 / 2 := by
      have h1 := congrFun hc' 0
      have h2 : a'.y () 0 ≤ 0 := hy' () 0
      simp only [ex16D2Economy, PrefEconomy.ofUtility, Finset.univ_unique, Finset.sum_singleton,
        Pi.add_apply, Matrix.cons_val_zero] at h1
      have : k = () := rfl
      subst this
      linarith
    change ex16D2u (a'.x k) ≤ ex16D2u ![1]
    rw [hval1]
    exact hle1 _ hx'le
  · have := hprofit p (h.2.1 ())
    subst this
    have hw : w () = 0 := by
      simpa [ex16D2Economy, PrefEconomy.ofUtility] using h.1
    have hb : (![3] : Fin 1 → ℝ) ∈ budgetSetOn (nonnegOrthant 1) 0 (w ()) :=
      ⟨fun l => by fin_cases l; norm_num, by rw [hw, zero_dotProduct]⟩
    have := (h.2.2.1 ()).2 _ hb
    simp only [ex16D2Economy, PrefEconomy.ofUtility, utilityPref, ex16D2u] at this
    norm_num at this
  · exact h.1 (hprofit p (h.2.2.1 ()))
  · intro y hy z hz α β hα hβ _ l
    have := hy l; have := hz l
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith
  · refine Continuous.continuousOn ?_
    unfold ex16D2u
    fun_prop
  · intro x _ y hy z hz α β hα hβ hαβ
    refine ⟨?_, ?_⟩
    · intro l
      have := hy.1 l; have := hz.1 l
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      nlinarith
    · have hyx : ex16D2u x ≤ ex16D2u y := hy.2
      have hzx : ex16D2u x ≤ ex16D2u z := hz.2
      change ex16D2u x ≤ ex16D2u (α • y + β • z)
      have hcomb : min (y 0) (z 0) ≤ (α • y + β • z) 0 := by
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        have hy' : y 0 = α * y 0 + β * y 0 := by rw [← add_mul, hαβ, one_mul]
        have hz' : z 0 = α * z 0 + β * z 0 := by rw [← add_mul, hαβ, one_mul]
        rcases le_total (y 0) (z 0) with h | h
        · rw [min_eq_left h]; nlinarith [mul_le_mul_of_nonneg_left h hβ]
        · rw [min_eq_right h]; nlinarith [mul_le_mul_of_nonneg_left h hα]
      rcases le_total (y 0) (z 0) with h | h
      · rw [min_eq_left h] at hcomb
        exact hyx.trans (hmono hcomb)
      · rw [min_eq_right h] at hcomb
        exact hzx.trans (hmono hcomb)
  · intro hlns
    obtain ⟨y, -, hd, hs⟩ := hlns ![1] (fun l => by fin_cases l; norm_num) (1 / 2)
      (by norm_num)
    apply hs.2
    have hy0 : y 0 ≤ 3 / 2 := by
      have := abs_sub_le_euclidDist y ![1] 0
      have h2 := (abs_le.mp (this.trans hd)).2
      simp only [Matrix.cons_val_zero] at h2
      linarith
    change ex16D2u y ≤ ex16D2u ![1]
    rw [hval1]
    exact hle1 _ hy0

end MWG.WelfareTheorems
