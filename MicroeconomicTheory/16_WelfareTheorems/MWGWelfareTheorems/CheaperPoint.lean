/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGWelfareTheorems.SecondWelfare

/-!
# When is a quasiequilibrium an equilibrium? (MWG Section 16.D, pp. 554-556)

* **Proposition 16.D.2** (the cheaper consumption argument) and footnotes 6-8.
* **Proposition 16.D.3**: with convex consumption sets containing `0`, continuous preferences and
  wealth levels `w ≫ 0`, a price quasiequilibrium with transfers is a price equilibrium with
  transfers. The proof uses the standing local nonsatiation assumption of p. 552 (through
  footnote 3, `p·x*ᵢ = wᵢ`); without it the proposition is false
  (`proposition_16_D_3_needs_lns`, correction 2).
* **Figure 16.D.2** (Figure 15.B.10(a)): a Pareto optimal allocation of an Edgeworth box that is a
  price quasiequilibrium with transfers only at `p = (1, 0)`, where consumer 1's wealth is `0`,
  and is not a price equilibrium with transfers for any prices.
* The small type of p. 556: free disposal forces `p ≥ 0` (footnote 9); in a pure exchange economy
  with `X_i = ℝ^L₊` and continuous locally nonsatiated preferences, a quasiequilibrium with
  `x*ᵢ ≫ 0` for all `i` is an equilibrium; with strongly monotone preferences and `ω̄ ≫ 0`, every
  quasiequilibrium has `p ≫ 0` and is an equilibrium.
* **Exercise 16.D.3**: the same with production, when `∑ⱼ ŷⱼ + ω̄ ≫ 0` for some `ŷⱼ ∈ Yⱼ`.
-/

namespace MWG.WelfareTheorems

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.Production Kreps.PreferenceProperties
open MWG.CompetitiveMarkets (Allocation)
open Filter Topology

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {L : ℕ}

/-- **Proposition 16.D.2** (MWG, p. 555). Let `X` be convex and `≿` rational and continuous on
`X`, `x* ∈ X`, and suppose `x ≻ x*` implies `p·x ≥ w`. If there is a cheaper consumption
`x' ∈ X` with `p·x' < w`, then `x ≻ x*` implies `p·x > w`. -/
theorem proposition_16_D_2 {X : Set (Fin L → ℝ)} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hX : Convex ℝ X) (hr : RationalOn X r) (hc : PrefContinuous X r) {xs : Fin L → ℝ}
    (hxs : xs ∈ X) {p : Fin L → ℝ} {w : ℝ} (h : ∀ x ∈ X, Strict r x xs → w ≤ p ⬝ᵥ x)
    {x' : Fin L → ℝ} (hx' : x' ∈ X) (hcheap : p ⬝ᵥ x' < w) :
    ∀ x ∈ X, Strict r x xs → w < p ⬝ᵥ x := by
  intro x hx hs
  rcases (h x hx hs).lt_or_eq with hlt | heq
  · exact hlt
  exfalso
  -- the points `zₙ = (1 - tₙ)x + tₙx'`, `tₙ = 1/(n+1)`, are cheaper than `w` and tend to `x`
  set t : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with ht
  have ht0 : ∀ n, 0 < t n := fun n => by positivity
  have ht1 : ∀ n, t n ≤ 1 := fun n => by
    rw [ht, div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  set z : ℕ → Fin L → ℝ := fun n => (1 - t n) • x + t n • x' with hz
  have hzX : ∀ n, z n ∈ X := fun n => hX hx hx' (by linarith [ht1 n]) (ht0 n).le (by ring)
  have hzp : ∀ n, p ⬝ᵥ z n < w := by
    intro n
    simp only [hz, dotProduct_add, dotProduct_smul, smul_eq_mul]
    rw [← heq]
    nlinarith [ht0 n]
  have hznot : ∀ n, r xs (z n) := by
    intro n
    rcases hr.1 xs hxs (z n) (hzX n) with h1 | h1
    · exact h1
    · by_contra h2
      have := h (z n) (hzX n) ⟨h1, h2⟩
      linarith [hzp n]
  have htt : Tendsto t atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hzt : Tendsto z atTop (𝓝 x) := by
    have hcont : Continuous fun s : ℝ => (1 - s) • x + s • x' := by fun_prop
    have := (hcont.tendsto 0).comp htt
    have h2 : (1 - 0 : ℝ) • x + (0 : ℝ) • x' = x := by simp
    rw [h2] at this
    exact this
  have := hc (fun _ => xs) z xs x (fun _ => hxs) hzX hxs hx hznot tendsto_const_nhds hzt
  exact hs.2 this

/-- A bundle that is affordable and such that everything strictly preferred costs more than the
wealth is maximal in the budget set (completeness is used). -/
theorem isMaximalFor_of_strict_gt {X : Set (Fin L → ℝ)} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hr : RationalOn X r) {p xs : Fin L → ℝ} {w : ℝ} (hxs : xs ∈ X) (hb : p ⬝ᵥ xs ≤ w)
    (h : ∀ x ∈ X, Strict r x xs → w < p ⬝ᵥ x) : IsMaximalFor r (budgetSetOn X p w) xs := by
  refine ⟨⟨hxs, hb⟩, fun x hx => ?_⟩
  rcases hr.1 xs hxs x hx.1 with h1 | h1
  · exact h1
  · by_contra h2
    exact absurd hx.2 (not_le.mpr (h x hx.1 ⟨h1, h2⟩))

/-- **Footnote 6** (MWG, p. 555). If `≿` is locally nonsatiated, rational and continuous on the
convex set `X` and there is a cheaper consumption (`p·x' < p·x*`), then `x*` minimizes expenditure
on `{x ∈ X : x ≿ x*}` if and only if it is maximal for `≿` in `{x ∈ X : p·x ≤ p·x*}`. -/
theorem footnote_6 {X : Set (Fin L → ℝ)} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hX : Convex ℝ X) (hr : RationalOn X r) (hc : PrefContinuous X r)
    (hlns : LocallyNonsatiated X r) {xs : Fin L → ℝ} (hxs : xs ∈ X) {p x' : Fin L → ℝ}
    (hx' : x' ∈ X) (hcheap : p ⬝ᵥ x' < p ⬝ᵥ xs) :
    (∀ x ∈ X, r x xs → p ⬝ᵥ xs ≤ p ⬝ᵥ x) ↔ IsMaximalFor r (budgetSetOn X p (p ⬝ᵥ xs)) xs := by
  constructor
  · intro h
    refine isMaximalFor_of_strict_gt hr hxs le_rfl ?_
    exact proposition_16_D_2 hX hr hc hxs (fun x hx hs => h x hx hs.1) hx' hcheap
  · intro h x hx hpref
    exact exercise_16_C_2 hlns hr.2 h hx hpref

/-- **Footnote 7** (MWG, p. 555). On a convex `X`, for a bundle `x* ∈ X` with `p·x* ≤ w` (for
instance the Walrasian demand `x(p, w)`), there is a cheaper consumption for `(p, w)` if and only
if there are cheaper consumptions arbitrarily close to `x*` (the locally cheaper consumption
condition of Appendix A of Chapter 3). -/
theorem footnote_7 {X : Set (Fin L → ℝ)} (hX : Convex ℝ X) {p xs : Fin L → ℝ} {w : ℝ}
    (hxs : xs ∈ X) (hb : p ⬝ᵥ xs ≤ w) :
    (∃ x' ∈ X, p ⬝ᵥ x' < w) ↔
      ∀ ε : ℝ, 0 < ε → ∃ x' ∈ X, euclidDist x' xs ≤ ε ∧ p ⬝ᵥ x' < w := by
  constructor
  · rintro ⟨x', hx', hlt⟩ ε hε
    set α := min (1 / 2) (ε / (euclidDist x' xs + 1)) with hα
    have hd0 := euclidDist_nonneg x' xs
    have hα0 : 0 < α := lt_min (by norm_num) (div_pos hε (by linarith))
    have hα1 : α ≤ 1 := (min_le_left _ _).trans (by norm_num)
    refine ⟨α • x' + (1 - α) • xs, hX hx' hxs hα0.le (by linarith) (by ring), ?_, ?_⟩
    · rw [euclidDist_segment hα0.le]
      calc α * euclidDist x' xs ≤ ε / (euclidDist x' xs + 1) * (euclidDist x' xs + 1) :=
            mul_le_mul (min_le_right _ _) (by linarith) hd0 (by positivity)
        _ = ε := div_mul_cancel₀ ε (by linarith)
    · simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]
      nlinarith
  · intro h
    obtain ⟨x', hx', -, hlt⟩ := h 1 one_pos
    exact ⟨x', hx', hlt⟩

/-- **Footnote 8** (MWG, p. 555). Proposition 16.D.2 generalizes Proposition 3.E.1(ii): on
`X = ℝ^L₊` with wealth `w > 0` the bundle `0` is a cheaper consumption, so (without local
nonsatiation and without `w = p·x*`) "`x ≻ x*` implies `p·x ≥ w`" gives "`x ≻ x*` implies
`p·x > w`". -/
theorem footnote_8 {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop} (hr : RationalOn (nonnegOrthant L) r)
    (hc : PrefContinuous (nonnegOrthant L) r) {xs : Fin L → ℝ} (hxs : xs ∈ nonnegOrthant L)
    {p : Fin L → ℝ} {w : ℝ} (hw : 0 < w)
    (h : ∀ x ∈ nonnegOrthant L, Strict r x xs → w ≤ p ⬝ᵥ x) :
    ∀ x ∈ nonnegOrthant L, Strict r x xs → w < p ⬝ᵥ x :=
  proposition_16_D_2 (convex_nonnegOrthant L) hr hc hxs h (x' := 0) (fun _ => le_rfl)
    (by rw [dotProduct_zero]; exact hw)

/-- **Proposition 16.D.3** (MWG, p. 555). Suppose every `Xᵢ` is convex with `0 ∈ Xᵢ` and every
`≿ᵢ` is rational, continuous and (the standing assumption of p. 552) locally nonsatiated. Then
any price quasiequilibrium with transfers with wealth levels `w ≫ 0` is a price equilibrium with
transfers. -/
theorem proposition_16_D_3 {E : PrefEconomy ι κ L} (hX : ∀ i, Convex ℝ (E.X i))
    (h0 : ∀ i, (0 : Fin L → ℝ) ∈ E.X i) (hr : ∀ i, RationalOn (E.X i) (E.pref i))
    (hc : ∀ i, PrefContinuous (E.X i) (E.pref i))
    (hlns : ∀ i, LocallyNonsatiated (E.X i) (E.pref i)) {a : Allocation ι κ L}
    {p : Fin L → ℝ} {w : ι → ℝ} (h : E.IsPriceQuasiEqmWithTransfers a p w)
    (hw : ∀ i, 0 < w i) : E.IsPriceEqmWithTransfers a p w := by
  have hweq := h.wealth_eq hlns
  refine ⟨h.2.1, h.2.2.1, fun i => ?_, h.2.2.2.2⟩
  refine isMaximalFor_of_strict_gt (hr i) (h.2.2.2.1 i).1 (hweq i).le ?_
  exact proposition_16_D_2 (hX i) (hr i) (hc i) (h.2.2.2.1 i).1 (h.2.2.2.1 i).2 (h0 i)
    (by rw [dotProduct_zero]; exact hw i)

/-- The economy of the counterexample to Proposition 16.D.3 without local nonsatiation: two
consumers on `ℝ₊` indifferent between all bundles, one disposal firm, `ω̄ = 2`. -/
def satiatedEconomy : PrefEconomy (Fin 2) Unit 1 where
  X := fun _ => nonnegOrthant 1
  pref := fun _ _ _ => True
  Y := fun _ => nonposOrthant 1
  ω := ![2]

/-- **Proposition 16.D.3** (MWG, p. 555), correction 2: the standing assumption of local
nonsatiation (footnote 3, p. 552) is needed. In `satiatedEconomy` (convex consumption sets
containing `0`, rational continuous preferences), `x* = (1, 1)`, `y* = 0`, `p = 1` and wealth
levels `w = (1/2, 3/2) ≫ 0` form a price quasiequilibrium with transfers that is not a price
equilibrium with transfers (consumer 1 cannot afford `x*₁`). -/
theorem proposition_16_D_3_needs_lns :
    (∀ i, Convex ℝ (satiatedEconomy.X i)) ∧ (∀ i, (0 : Fin 1 → ℝ) ∈ satiatedEconomy.X i) ∧
      (∀ i, RationalOn (satiatedEconomy.X i) (satiatedEconomy.pref i)) ∧
      (∀ i, PrefContinuous (satiatedEconomy.X i) (satiatedEconomy.pref i)) ∧
      satiatedEconomy.IsPriceQuasiEqmWithTransfers ⟨fun _ => ![1], fun _ => 0⟩ ![1]
        ![1 / 2, 3 / 2] ∧
      ¬ satiatedEconomy.IsPriceEqmWithTransfers ⟨fun _ => ![1], fun _ => 0⟩ ![1]
        ![1 / 2, 3 / 2] := by
  refine ⟨fun _ => convex_nonnegOrthant 1, fun _ _ => le_rfl,
    fun _ => ⟨fun _ _ _ _ => Or.inl trivial, fun _ _ _ _ _ _ _ _ => trivial⟩,
    fun _ => fun _ _ _ _ _ _ _ _ _ _ _ => trivial, ⟨?_, ?_, fun _ => ?_, fun i => ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · intro h
    have := congrFun h 0
    simp at this
  · simp [satiatedEconomy, Fin.sum_univ_two, dotProduct]
    norm_num
  · exact zero_mem_supply_nonpos (fun l => by fin_cases l; norm_num)
  · intro l; fin_cases l; norm_num
  · exact fun _ _ hs => absurd trivial hs.2
  · funext l
    fin_cases l
    simp [satiatedEconomy]
  · intro h
    have := (h.2.2.1 0).1.2
    simp [dotProduct] at this
    norm_num at this

/-- **Footnote 9** (MWG, p. 556). With the free disposal technology, profit maximization forces
`p ≥ 0` (otherwise disposing of a good with negative price raises profits). -/
theorem footnote_9 {p y : Fin L → ℝ} (h : y ∈ supply (nonposOrthant L) p) : ∀ l, 0 ≤ p l := by
  intro l
  by_contra hneg
  push Not at hneg
  have hmem : y - Pi.single l 1 ∈ nonposOrthant L := by
    intro k
    have := h.1 k
    by_cases hk : k = l
    · subst hk; simp; linarith
    · simp [hk]; linarith
  have := h.2 _ hmem
  rw [dotProduct_sub] at this
  simp at this
  linarith

/-- A nonnegative nonzero price vector gives positive value to a strictly positive bundle. -/
theorem dotProduct_pos_of_nonneg_ne_zero {p x : Fin L → ℝ} (hp : ∀ l, 0 ≤ p l) (hp0 : p ≠ 0)
    (hx : ∀ l, 0 < x l) : 0 < p ⬝ᵥ x := by
  obtain ⟨l, hl⟩ : ∃ l, p l ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hp0 (funext hall)
  have hpos : 0 < p l * x l := mul_pos (lt_of_le_of_ne (hp l) (Ne.symm hl)) (hx l)
  exact lt_of_lt_of_le hpos (Finset.single_le_sum (f := fun k => p k * x k)
    (fun k _ => mul_nonneg (hp k) (hx k).le) (Finset.mem_univ l))

/-- **Section 16.D** (MWG, p. 556). In a pure exchange economy (with at least one firm) where
`Xᵢ = ℝ^L₊` and preferences are rational, continuous and locally nonsatiated, every price
quasiequilibrium with transfers in which `x*ᵢ ≫ 0` for all `i` is a price equilibrium with
transfers (`p ≥ 0` by free disposal, so `wᵢ = p·x*ᵢ > 0`). -/
theorem pureExchange_quasiEqm_isPriceEqm_of_interior [Nonempty κ] {E : PrefEconomy ι κ L}
    (hpe : E.IsPureExchange) (hX : ∀ i, E.X i = nonnegOrthant L)
    (hr : ∀ i, RationalOn (E.X i) (E.pref i)) (hc : ∀ i, PrefContinuous (E.X i) (E.pref i))
    (hlns : ∀ i, LocallyNonsatiated (E.X i) (E.pref i)) {a : Allocation ι κ L}
    {p : Fin L → ℝ} {w : ι → ℝ} (h : E.IsPriceQuasiEqmWithTransfers a p w)
    (hint : ∀ i l, 0 < a.x i l) : E.IsPriceEqmWithTransfers a p w := by
  obtain ⟨j⟩ := ‹Nonempty κ›
  have hp : ∀ l, 0 ≤ p l := footnote_9 (hpe j ▸ h.2.2.1 j)
  refine proposition_16_D_3 (fun i => hX i ▸ convex_nonnegOrthant L)
    (fun i => by rw [hX i]; exact fun _ => le_rfl) hr hc hlns h fun i => ?_
  rw [← h.wealth_eq hlns i]
  exact dotProduct_pos_of_nonneg_ne_zero hp h.1 (hint i)

/-- **Exercise 16.D.3** (MWG, p. 575). Suppose `Xᵢ = ℝ^L₊` and preferences are rational,
continuous and strongly monotone (`I > 0`), and a strictly positive aggregate production is
possible: `∑ⱼ ŷⱼ + ω̄ ≫ 0` for some `ŷⱼ ∈ Yⱼ`. Then every price quasiequilibrium with transfers is
a price equilibrium with transfers, and its prices are strictly positive. -/
theorem exercise_16_D_3 [Nonempty ι] {E : PrefEconomy ι κ L}
    (hX : ∀ i, E.X i = nonnegOrthant L) (hr : ∀ i, RationalOn (E.X i) (E.pref i))
    (hc : ∀ i, PrefContinuous (E.X i) (E.pref i))
    (hmono : ∀ i, PrefStronglyMonotone (nonnegOrthant L) (E.pref i))
    {yh : κ → Fin L → ℝ} (hyh : ∀ j, yh j ∈ E.Y j) (hpos : ∀ l, 0 < (∑ j, yh j + E.ω) l)
    {a : Allocation ι κ L} {p : Fin L → ℝ} {w : ι → ℝ}
    (h : E.IsPriceQuasiEqmWithTransfers a p w) :
    E.IsPriceEqmWithTransfers a p w ∧ StrictlyPositive p := by
  classical
  have hL : 0 < L := by
    rcases Nat.eq_zero_or_pos L with h0 | h0
    · subst h0
      exact absurd (funext fun l => l.elim0) h.1
    · exact h0
  have hlns : ∀ i, LocallyNonsatiated (E.X i) (E.pref i) := fun i =>
    hX i ▸ exercise_3_B_1b_orthant hL (exercise_3_B_1a hL (hmono i))
  have hweq := h.wealth_eq hlns
  have hxX : ∀ i, a.x i ∈ nonnegOrthant L := fun i => hX i ▸ (h.2.2.2.1 i).1
  -- adding one unit of good `l` is strictly better
  have hbetter : ∀ i l, Strict (E.pref i) (a.x i + Pi.single l 1) (a.x i) ∧
      a.x i + Pi.single l 1 ∈ E.X i := by
    intro i l
    have hmem : a.x i + Pi.single l 1 ∈ nonnegOrthant L := fun k => by
      have := hxX i k
      by_cases hk : k = l
      · subst hk; simp; linarith
      · simp [hk]; linarith
    refine ⟨hmono i _ (hxX i) _ hmem (fun k => ?_) ?_, hX i ▸ hmem⟩
    · by_cases hk : k = l
      · subst hk; simp
      · simp [hk]
    · intro heq
      have := congrFun heq l
      simp at this
  have hcost : ∀ i l, p ⬝ᵥ (a.x i + Pi.single l 1) = w i + p l := by
    intro i l
    rw [dotProduct_add, hweq i]
    simp
  -- `p ≥ 0`
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hp : ∀ l, 0 ≤ p l := by
    intro l
    have := (h.2.2.2.1 i₀).2 _ (hbetter i₀ l).2 (hbetter i₀ l).1
    rw [hcost] at this
    linarith
  -- some consumer has positive wealth
  have hsum : 0 < ∑ i, w i := by
    rw [h.2.1]
    have h1 : ∑ j, p ⬝ᵥ yh j ≤ ∑ j, p ⬝ᵥ a.y j :=
      Finset.sum_le_sum fun j _ => (h.2.2.1 j).2 (yh j) (hyh j)
    have h2 := dotProduct_pos_of_nonneg_ne_zero hp h.1 hpos
    rw [dotProduct_add, dotProduct_finset_sum] at h2
    linarith
  obtain ⟨i₁, hi₁⟩ : ∃ i, 0 < w i := by
    by_contra hall
    push Not at hall
    exact absurd (Finset.sum_nonpos fun i _ => hall i) (not_le.mpr hsum)
  have hstrict : ∀ i, 0 < w i → ∀ x ∈ E.X i, Strict (E.pref i) x (a.x i) → w i < p ⬝ᵥ x :=
    fun i hwi => proposition_16_D_2 (hX i ▸ convex_nonnegOrthant L) (hr i) (hc i)
      (h.2.2.2.1 i).1 (h.2.2.2.1 i).2 (x' := 0) (by rw [hX i]; exact fun _ => le_rfl)
      (by rw [dotProduct_zero]; exact hwi)
  -- `p ≫ 0`
  have hpp : StrictlyPositive p := by
    intro l
    rcases (hp l).lt_or_eq with hl | hl
    · exact hl
    · exfalso
      have := hstrict i₁ hi₁ _ (hbetter i₁ l).2 (hbetter i₁ l).1
      rw [hcost, ← hl] at this
      linarith
  refine ⟨⟨h.2.1, h.2.2.1, fun i => ?_, h.2.2.2.2⟩, hpp⟩
  refine isMaximalFor_of_strict_gt (hr i) (h.2.2.2.1 i).1 (hweq i).le ?_
  rcases lt_or_ge 0 (w i) with hwi | hwi
  · exact hstrict i hwi
  · -- zero wealth: `x*ᵢ = 0`, and everything strictly preferred is nonzero
    have hnn : 0 ≤ p ⬝ᵥ a.x i := Finset.sum_nonneg fun l _ => mul_nonneg (hp l) (hxX i l)
    have hw0 : w i = 0 := le_antisymm hwi (hweq i ▸ hnn)
    have hx0 : a.x i = 0 := by
      have h1 : p ⬝ᵥ a.x i = 0 := by rw [hweq i, hw0]
      funext l
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => mul_nonneg (hp k) (hxX i k))).mp
        h1 l (Finset.mem_univ l)
      rcases mul_eq_zero.mp this with h2 | h2
      · exact absurd h2 (hpp l).ne'
      · simpa using h2
    intro x hx hs
    rw [hw0]
    have hxn : x ∈ nonnegOrthant L := hX i ▸ hx
    have hne : x ≠ 0 := by
      rintro rfl
      rw [hx0] at hs
      exact hs.2 hs.1
    rw [dotProduct_comm]
    exact dotProduct_pos_of_nonneg_ne_zero hxn hne hpp

end MWG.WelfareTheorems
