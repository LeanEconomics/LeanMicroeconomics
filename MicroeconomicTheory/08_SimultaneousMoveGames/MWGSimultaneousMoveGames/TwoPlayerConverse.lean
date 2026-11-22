/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGSimultaneousMoveGames.TremblingHand
import MWGProduction.AppendixMM

/-!
# Two-player converses: rationalizability and trembling-hand perfection

MWG, Section 8.C, p. 245 (small type), and Section 8.F, p. 259 (small type).

Both converses rest on a theorem of the alternative, derived here from Farkas' lemma and its
strictly positive form (Stiemke) of Chapter 5's Appendix M.M (`MWG.Production.farkas`,
`MWG.Production.exists_pos_of_cone_inter_nonneg`, which use the closedness of finitely
generated cones, `MWG.Production.isClosed_coneOf`):

* `gordan_alternative`: either some nonnegative combination of the rows of a table is
  strictly positive on a set `R` of columns, or some nonzero probability vector supported on
  `R` makes every row nonpositive;
* `stiemke_alternative`: either some nonnegative combination of the rows is nonnegative and
  nonzero, or some strictly positive vector makes every row nonpositive.

**Trembling-hand perfection (p. 259).** In a two-player game, a strategy that is not weakly
dominated is a best response to a totally mixed strategy of the opponent
(`exists_totallyMixed_bestResponse`, by Stiemke). Hence a Nash equilibrium in which neither
player uses a weakly dominated strategy is trembling-hand perfect
(`isTHP_of_not_weaklyDominated_two`): the profiles `σ + t (y - σ)` with `t → 0` are totally
mixed, converge to `σ`, and each `σ_i` is a best response to them (Proposition 8.F.1).

**Rationalizability (p. 245).** The text says that with two players the rationalizable
strategies are exactly the survivors of iterated deletion of strictly dominated strategies.
With Definition 8.C.2 read literally (a conjecture is a profile of the rivals' *remaining*
mixed strategies) this is false (`Converses` module, correction 9): a mixture of two
surviving strategies can be deleted, and a strategy that is a best response only to that
mixture is then deleted too. It is true with the probabilistic conjectures of footnote 1
(p. 243), whose compound profiles are the convex combinations of remaining strategies
(`RationalizableConv`):

* `exists_ratIterConv_support_subset`: rationalizable strategies (in this sense, for any
  number of players) put no weight on strategies removed by iterated strict dominance;
* `exists_max_mem_of_msdChain`: along any process of iterated strict dominance, every
  conjecture supported on the remaining strategies has a best reply among the remaining
  strategies;
* `exists_belief_of_msdTerminal`: in a two-player game, a strategy that survives a complete
  process is a best response (among all of `Δ(S_i)`) to a mixed strategy of the opponent
  supported on the survivors (Gordan's alternative applied to the remaining game);
* `rationalizableConv_iff_two`: for two players, a pure strategy is rationalizable iff it
  survives a complete process of iterated deletion of strictly dominated strategies.
-/

namespace MWG.SimultaneousMoveGames

open MWG.NoncooperativeGames Function Finset Filter Topology

/-! ### Theorems of the alternative from Farkas' lemma -/

/-- **Gordan's alternative** (from Farkas' lemma, `MWG.Production.farkas`). If no nonnegative
combination of the rows `g a` is strictly positive on every column in `R`, then some nonnegative
`y`, zero off `R` and with positive sum, makes every row nonpositive: `∑_b y_b g(a, b) ≤ 0`. -/
theorem gordan_alternative {A B : Type*} [Fintype A] [Fintype B] (g : A → B → ℝ)
    (R : Set B) (hno : ¬ ∃ τ : A → ℝ, (∀ a, 0 ≤ τ a) ∧ ∀ b ∈ R, 0 < ∑ a, τ a * g a b) :
    ∃ y : B → ℝ, (∀ b, 0 ≤ y b) ∧ (∀ b ∉ R, y b = 0) ∧ 0 < ∑ b, y b ∧
      ∀ a, ∑ b, y b * g a b ≤ 0 := by
  classical
  set e := Fintype.equivFin B with he
  set gen : A ⊕ B ⊕ B → Fin (Fintype.card B) → ℝ :=
    Sum.elim (fun a k => g a (e.symm k))
      (Sum.elim (fun c => -Pi.single (e c) 1)
        (fun c => if c ∈ R then 0 else Pi.single (e c) 1)) with hgen
  set tgt : Fin (Fintype.card B) → ℝ := fun k => if e.symm k ∈ R then 1 else 0 with htgt
  have hsingle : ∀ (c b : B), (Pi.single (e c) (1 : ℝ) : Fin (Fintype.card B) → ℝ) (e b) =
      if b = c then 1 else 0 := by
    intro c b
    simp [Pi.single_apply, e.apply_eq_iff_eq]
  have hnotL : ¬ ∃ lam : A ⊕ B ⊕ B → ℝ, 0 ≤ lam ∧ tgt = ∑ x, lam x • gen x := by
    rintro ⟨lam, hlam, heq⟩
    apply hno
    refine ⟨fun a => lam (Sum.inl a), fun a => hlam _, fun b hb => ?_⟩
    have h1 := congrFun heq (e b)
    rw [Finset.sum_apply, Fintype.sum_sum_type, Fintype.sum_sum_type] at h1
    simp only [htgt, Equiv.symm_apply_apply, hb, ite_true, Pi.smul_apply, smul_eq_mul, hgen,
      Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, hsingle] at h1
    have h2 : ∑ x : B, lam (Sum.inr (Sum.inl x)) * -(if b = x then (1 : ℝ) else 0) =
        -lam (Sum.inr (Sum.inl b)) := by
      simp [mul_ite]
    have h3 : ∑ x : B, lam (Sum.inr (Sum.inr x)) *
        (if x ∈ R then (0 : Fin (Fintype.card B) → ℝ) else Pi.single (e x) 1) (e b) = 0 := by
      refine Finset.sum_eq_zero fun x _ => ?_
      by_cases hx : x ∈ R
      · simp [hx]
      · have hxb : b ≠ x := fun h => hx (h ▸ hb)
        simp [hx, hxb]
    rw [h2, h3] at h1
    have := hlam (Sum.inr (Sum.inl b))
    simp only [Pi.zero_apply] at this
    linarith
  have hy : ∃ y : Fin (Fintype.card B) → ℝ, (∀ x, y ⬝ᵥ gen x ≤ 0) ∧ 0 < y ⬝ᵥ tgt := by
    by_contra hno'
    exact hnotL ((MWG.Production.farkas gen tgt).2 hno')
  obtain ⟨y, hyg, hyt⟩ := hy
  have hdot : ∀ v : Fin (Fintype.card B) → ℝ, y ⬝ᵥ v = ∑ b, y (e b) * v (e b) := by
    intro v
    rw [dotProduct]
    exact (e.sum_comp (fun k => y k * v k)).symm
  have hnn : ∀ b, 0 ≤ y (e b) := by
    intro b
    have := hyg (Sum.inr (Sum.inl b))
    rw [hdot] at this
    simp only [hgen, Sum.elim_inr, Sum.elim_inl, Pi.neg_apply, hsingle] at this
    simp [mul_ite] at this
    linarith
  have hzero : ∀ b ∉ R, y (e b) = 0 := by
    intro b hb
    have := hyg (Sum.inr (Sum.inr b))
    rw [hdot] at this
    simp only [hgen, Sum.elim_inr, hb, ite_false, hsingle] at this
    have h2 : y (e b) ≤ 0 := by simpa [mul_ite] using this
    exact le_antisymm h2 (hnn b)
  refine ⟨fun b => y (e b), hnn, hzero, ?_, fun a => ?_⟩
  · rw [hdot] at hyt
    refine hyt.trans_le (Finset.sum_le_sum fun b _ => ?_)
    simp only [htgt, Equiv.symm_apply_apply]
    split_ifs
    · rw [mul_one]
    · rw [mul_zero]; exact hnn b
  · have := hyg (Sum.inl a)
    rw [hdot] at this
    simpa [hgen] using this

/-- **Stiemke's alternative** (from `MWG.Production.exists_pos_of_cone_inter_nonneg`). If every
nonnegative combination of the rows `g a` that is nonnegative in every column is zero, then some
strictly positive `y` makes every row nonpositive: `∑_b y_b g(a, b) ≤ 0`. -/
theorem stiemke_alternative {A B : Type*} [Fintype A] [Fintype B] (g : A → B → ℝ)
    (hno : ∀ τ : A → ℝ, (∀ a, 0 ≤ τ a) → (∀ b, 0 ≤ ∑ a, τ a * g a b) →
      ∀ b, ∑ a, τ a * g a b = 0) :
    ∃ y : B → ℝ, (∀ b, 0 < y b) ∧ ∀ a, ∑ b, y b * g a b ≤ 0 := by
  classical
  set e := Fintype.equivFin B with he
  set gen : A → Fin (Fintype.card B) → ℝ := fun a k => g a (e.symm k) with hgen
  have hcone : ∀ x ∈ MWG.Production.coneOf gen, 0 ≤ x → x = 0 := by
    rintro x ⟨lam, hlam, rfl⟩ hx
    have hx' : ∀ b, 0 ≤ ∑ a, lam a * g a b := by
      intro b
      have := hx (e b)
      simpa [Finset.sum_apply, hgen] using this
    have h0 := hno lam hlam hx'
    funext k
    have := h0 (e.symm k)
    simpa [Finset.sum_apply, hgen] using this
  obtain ⟨p, hp, hpa⟩ := MWG.Production.exists_pos_of_cone_inter_nonneg gen hcone
  refine ⟨fun b => p (e b), fun b => hp (e b), fun a => ?_⟩
  have := hpa a
  rw [dotProduct, ← e.sum_comp] at this
  simpa [hgen] using this

/-! ### Two-player games -/

variable {I : Type*} {S : I → Type*} [Fintype I] [DecidableEq I] [∀ i, Fintype (S i)]
  [∀ i, DecidableEq (S i)]

omit [Fintype I] [DecidableEq I] [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] in
/-- In a two-player game a profile is determined by its two coordinates. -/
theorem two_profile_ext {T : I → Type*} {i j : I} (htwo : ∀ k, k = i ∨ k = j)
    {f g : (k : I) → T k} (hi : f i = g i) (hj : f j = g j) : f = g := by
  funext k
  rcases htwo k with rfl | rfl
  · exact hi
  · exact hj

omit [Fintype I] [DecidableEq I] [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] in
/-- In a two-player game the other player of `k` exists. -/
theorem two_other {i j : I} (hij : i ≠ j) (htwo : ∀ k, k = i ∨ k = j) (k : I) :
    ∃ o, k ≠ o ∧ ∀ l, l = k ∨ l = o := by
  rcases htwo k with rfl | rfl
  · exact ⟨j, hij, htwo⟩
  · exact ⟨i, hij.symm, fun l => (htwo l).symm⟩

omit [Fintype I] [DecidableEq I] [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] in
/-- In a two-player game a pure profile exists as soon as both strategy sets are nonempty. -/
theorem two_nonempty {i j : I} (htwo : ∀ k, k = i ∨ k = j) (a : S i) (b : S j) :
    Nonempty ((k : I) → S k) := by
  have h : ∀ k, Nonempty (S k) := by
    intro k
    rcases htwo k with rfl | rfl
    · exact ⟨a⟩
    · exact ⟨b⟩
  exact ⟨fun k => Classical.choice (h k)⟩

/-- Two players: the payoff of the mixed strategy `τ` against the pure profile `s` is
`∑_a τ(a) u_i(a, s_j)`, where `u_i(a, b)` is computed at `(a, b)` on top of any fixed profile
`r`. -/
theorem two_mixedPayoff_pure (N : NormalForm I S) {i j : I} (hij : i ≠ j)
    (htwo : ∀ k, k = i ∨ k = j) (r s : (k : I) → S k) (τ : S i → ℝ) :
    N.mixedPayoff (update (pureProfile s) i τ) i =
      ∑ a, τ a * N.payoff i (update (update r j (s j)) i a) := by
  rw [mixedPayoff_pureProfile_update_mixed]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 2
  exact two_profile_ext htwo (by simp) (by simp [update_of_ne hij.symm])

omit [∀ i, DecidableEq (S i)] in
/-- Two players: `u_i(τ, σ_j) = ∑_b σ_j(b) ∑_a τ(a) u_i(a, b)`. -/
theorem two_mixedPayoff_eq (N : NormalForm I S) {i j : I} (hij : i ≠ j)
    (htwo : ∀ k, k = i ∨ k = j) (r : (k : I) → S k) (σ : (k : I) → S k → ℝ)
    (τ : S i → ℝ) :
    N.mixedPayoff (update σ i τ) i =
      ∑ b, σ j b * ∑ a, τ a * N.payoff i (update (update r j b) i a) := by
  classical
  have h1 : update (update σ i τ) j (σ j) = update σ i τ := by
    have := update_eq_self j (update σ i τ)
    rwa [update_of_ne hij.symm] at this
  rw [← h1, mixedPayoff_update_eq_sum_pure]
  refine Finset.sum_congr rfl fun b _ => ?_
  have h2 : update (update σ i τ) j (pureMixed b) = update (pureProfile (update r j b)) i τ :=
    two_profile_ext htwo (by simp [update_of_ne hij]) (by simp [update_of_ne hij.symm, pureProfile])
  rw [h2, two_mixedPayoff_pure N hij htwo r]
  simp

omit [∀ i, DecidableEq (S i)] in
/-- Two players: a best response to two profiles of the opponent is a best response to every
convex combination of them. -/
theorem isBestResponse_two_mix (N : NormalForm I S) {i j : I} (hij : i ≠ j)
    (htwo : ∀ k, k = i ∨ k = j) (r : (k : I) → S k) {τ : S i → ℝ}
    {σ y ρ : (k : I) → S k → ℝ} (h1 : IsBestResponse N i τ σ) (h2 : IsBestResponse N i τ y)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hρ : ρ j = σ j + t • (y j - σ j)) :
    IsBestResponse N i τ ρ := by
  classical
  have key : ∀ τ'' : S i → ℝ, N.mixedPayoff (update ρ i τ'') i =
      N.mixedPayoff (update σ i τ'') i + t * (N.mixedPayoff (update y i τ'') i -
        N.mixedPayoff (update σ i τ'') i) := by
    intro τ''
    rw [two_mixedPayoff_eq N hij htwo r ρ, two_mixedPayoff_eq N hij htwo r σ,
      two_mixedPayoff_eq N hij htwo r y, hρ, ← Finset.sum_sub_distrib, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  refine ⟨h1.1, fun τ' hτ' => ?_⟩
  rw [key, key]
  have a1 := h1.2 τ' hτ'
  have a2 := h2.2 τ' hτ'
  nlinarith

/-! ### Trembling-hand perfection: the two-player converse of Proposition 8.F.2 -/

omit [∀ i, DecidableEq (S i)] in
/-- **Section 8.F** (MWG, p. 259, small type), the key step. In a two-player game, a mixed
strategy `τ` of player `i` that is not weakly dominated is a best response to some totally mixed
strategy `y` of the opponent `j` (Stiemke's alternative). -/
theorem exists_totallyMixed_bestResponse (N : NormalForm I S) {i j : I} (hij : i ≠ j)
    (htwo : ∀ k, k = i ∨ k = j) {τ : S i → ℝ} (hτ : IsMixedStrategy τ)
    (hnd : ¬ MixedWeaklyDominated N i τ) (r : (k : I) → S k) :
    ∃ y : S j → ℝ, IsTotallyMixed y ∧
      ∀ σ : (k : I) → S k → ℝ, σ j = y → IsBestResponse N i τ σ := by
  classical
  set U : S i → S j → ℝ := fun a b => N.payoff i (update (update r j b) i a) with hU
  set V : S j → ℝ := fun b => ∑ a, τ a * U a b with hV
  have hpure : ∀ (τ' : S i → ℝ) (s : (k : I) → S k),
      N.mixedPayoff (update (pureProfile s) i τ') i = ∑ a, τ' a * U a (s j) :=
    fun τ' s => two_mixedPayoff_pure N hij htwo r s τ'
  have hno : ∀ τ' : S i → ℝ, (∀ a, 0 ≤ τ' a) → (∀ b, 0 ≤ ∑ a, τ' a * (U a b - V b)) →
      ∀ b, ∑ a, τ' a * (U a b - V b) = 0 := by
    intro τ' hτ'0 hge b₀
    by_contra hne
    have hpos : 0 < ∑ a, τ' a * (U a b₀ - V b₀) := (hge b₀).lt_of_ne (Ne.symm hne)
    set t := ∑ a, τ' a with ht
    have hexp : ∀ b, ∑ a, τ' a * (U a b - V b) = ∑ a, τ' a * U a b - t * V b := by
      intro b
      rw [ht, Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun a _ => by ring
    have htpos : 0 < t := by
      rcases (Finset.sum_nonneg fun a (_ : a ∈ univ) => hτ'0 a).eq_or_lt with h0 | h0
      · have hz : ∀ a, τ' a = 0 := fun a =>
          (Finset.sum_eq_zero_iff_of_nonneg fun a _ => hτ'0 a).1 h0.symm a (mem_univ a)
        simp [hz] at hpos
      · exact h0
    set τ'' : S i → ℝ := fun a => τ' a / t with hτ''
    have hτ''m : IsMixedStrategy τ'' := by
      refine ⟨fun a => div_nonneg (hτ'0 a) htpos.le, ?_⟩
      rw [hτ'', ← Finset.sum_div, ← ht, div_self htpos.ne']
    have hcmp : ∀ b, ∑ a, τ'' a * U a b - V b = (∑ a, τ' a * (U a b - V b)) / t := by
      intro b
      rw [hexp, sub_div, mul_div_cancel_left₀ _ htpos.ne', hτ'', Finset.sum_div]
      congr 1
      exact Finset.sum_congr rfl fun a _ => by ring
    apply hnd
    refine ⟨τ'', hτ''m, (mixedWeaklyDominates_iff_pure N i τ'' τ).2 ⟨fun s => ?_, ?_⟩⟩
    · rw [hpure, hpure]
      have := hcmp (s j)
      have h0 : 0 ≤ (∑ a, τ' a * (U a (s j) - V (s j))) / t := div_nonneg (hge _) htpos.le
      linarith
    · refine ⟨update r j b₀, ?_⟩
      rw [hpure, hpure, update_self]
      have := hcmp b₀
      have h0 : 0 < (∑ a, τ' a * (U a b₀ - V b₀)) / t := div_pos hpos htpos
      linarith
  obtain ⟨y, hypos, hya⟩ := stiemke_alternative (fun a b => U a b - V b) hno
  set Y := ∑ b, y b with hY
  have hYpos : 0 < Y := Finset.sum_pos (fun b _ => hypos b) ⟨r j, mem_univ _⟩
  refine ⟨fun b => y b / Y, ⟨⟨fun b => div_nonneg (hypos b).le hYpos.le, ?_⟩,
    fun b => div_pos (hypos b) hYpos⟩, fun σ hσ => ⟨hτ, fun τ' hτ' => ?_⟩⟩
  · rw [← Finset.sum_div, ← hY, div_self hYpos.ne']
  · rw [two_mixedPayoff_eq N hij htwo r σ, two_mixedPayoff_eq N hij htwo r σ, hσ]
    have hrow : ∀ a, ∑ b, y b / Y * U a b ≤ ∑ b, y b / Y * V b := by
      intro a
      have := hya a
      have h2 : ∑ b, y b / Y * U a b - ∑ b, y b / Y * V b =
          (∑ b, y b * (U a b - V b)) / Y := by
        rw [← Finset.sum_sub_distrib, Finset.sum_div]
        exact Finset.sum_congr rfl fun b _ => by ring
      have h3 : (∑ b, y b * (U a b - V b)) / Y ≤ 0 := div_nonpos_of_nonpos_of_nonneg this hYpos.le
      linarith
    have hswap : ∀ τ₀ : S i → ℝ, ∑ b, y b / Y * ∑ a, τ₀ a * U a b =
        ∑ a, τ₀ a * ∑ b, y b / Y * U a b := by
      intro τ₀
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    have hVeq : ∑ b, y b / Y * ∑ a, τ a * U a b = ∑ b, y b / Y * V b := rfl
    rw [hswap τ', hVeq]
    calc ∑ a, τ' a * ∑ b, y b / Y * U a b ≤ ∑ a, τ' a * ∑ b, y b / Y * V b :=
          Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hrow a) (hτ'.1 a)
      _ = ∑ b, y b / Y * V b := by rw [← Finset.sum_mul, hτ'.2, one_mul]

omit [∀ i, DecidableEq (S i)] in
/-- **Section 8.F** (MWG, p. 259, small type). The converse of Proposition 8.F.2 for two players:
a Nash equilibrium `σ` of `[I, {Δ(S_i)}, {u_i(·)}]` with two players in which no `σ_i` is a weakly
dominated strategy is (normal form) trembling-hand perfect. (It fails with three players:
`exercise_8_F_2`.) -/
theorem isTHP_of_not_weaklyDominated_two (N : NormalForm I S) {i j : I} (hij : i ≠ j)
    (htwo : ∀ k, k = i ∨ k = j) {σ : (k : I) → S k → ℝ} (hσ : IsMixedNash N σ)
    (hnd : ∀ k, ¬ MixedWeaklyDominated N k (σ k)) : IsTHP N σ := by
  classical
  obtain ⟨ai, -⟩ := mixed_exists_pos (hσ.1 i)
  obtain ⟨bj, -⟩ := mixed_exists_pos (hσ.1 j)
  obtain ⟨r⟩ := two_nonempty htwo ai bj
  have htwo' : ∀ k, k = j ∨ k = i := fun k => (htwo k).symm
  obtain ⟨yj, hyj, hbri⟩ := exists_totallyMixed_bestResponse N hij htwo (hσ.1 i) (hnd i) r
  obtain ⟨yi, hyi, hbrj⟩ :=
    exists_totallyMixed_bestResponse N hij.symm htwo' (hσ.1 j) (hnd j) r
  set y : (k : I) → S k → ℝ := update (update σ i yi) j yj with hy
  have hyi' : y i = yi := by rw [hy, update_of_ne hij, update_self]
  have hyj' : y j = yj := by rw [hy, update_self]
  have hytm : ∀ k, IsTotallyMixed (y k) := by
    intro k
    rcases htwo k with rfl | rfl
    · rw [hyi']; exact hyi
    · rw [hyj']; exact hyj
  set t : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 2) with ht
  have ht0 : ∀ n, 0 < t n := fun n => by positivity
  have ht1 : ∀ n, t n ≤ 1 / 2 := by
    intro n
    simp only [ht]
    gcongr
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have htlim : Tendsto t atTop (𝓝 0) := by
    have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    refine squeeze_zero (fun n => (ht0 n).le) (fun n => ?_) this
    simp only [ht]
    gcongr
    linarith
  set ρ : ℕ → (k : I) → S k → ℝ := fun n => σ + t n • (y - σ) with hρ
  have hρk : ∀ n k, ρ n k = σ k + t n • (y k - σ k) := fun n k => rfl
  refine (proposition_8_F_1 N hσ).2 ⟨ρ, fun n k => ⟨⟨fun a => ?_, ?_⟩, fun a => ?_⟩, ?_,
    fun n k => ?_⟩
  · rw [hρk]
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    have := (hσ.1 k).1 a
    have := (hytm k).2 a
    nlinarith [ht0 n, ht1 n]
  · rw [hρk]
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, Finset.sum_sub_distrib, (hσ.1 k).2, (hytm k).1.2]
    ring
  · rw [hρk]
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    have := (hσ.1 k).1 a
    have := (hytm k).2 a
    nlinarith [ht0 n, ht1 n]
  · have : Tendsto (fun n => σ + t n • (y - σ)) atTop (𝓝 (σ + (0 : ℝ) • (y - σ))) :=
      (htlim.smul_const (y - σ)).const_add σ
    simpa using this
  · have hnash : ∀ l, IsBestResponse N l (σ l) σ := ((isMixedNash_iff_bestResponse N σ).1 hσ).2
    rcases htwo k with rfl | rfl
    · exact isBestResponse_two_mix N hij htwo r (hnash _) (hbri y hyj') (ht0 n).le
        ((ht1 n).trans (by norm_num)) (hρk n j)
    · exact isBestResponse_two_mix N hij.symm htwo' r (hnash _) (hbrj y hyi') (ht0 n).le
        ((ht1 n).trans (by norm_num)) (hρk n i)

/-! ### Rationalizability with probabilistic conjectures -/

/-- A process of iterated deletion of strictly dominated strategies (with mixed dominators,
`MSDStep`) is complete when no remaining pure strategy is strictly dominated, against the
remaining rival profiles, by a mixture of remaining strategies. -/
def MSDTerminal (N : NormalForm I S) (Q : (i : I) → Set (S i)) : Prop :=
  ∀ i, ∀ a ∈ Q i, ¬ ∃ τ' : S i → ℝ, IsMixedStrategy τ' ∧ (∀ b, 0 < τ' b → b ∈ Q i) ∧
    ∀ r : (j : I) → S j, (∀ j, j ≠ i → r j ∈ Q j) →
      N.payoff i (update r i a) < N.mixedPayoff (update (pureProfile r) i τ') i

/-- **Footnote 1** (MWG, p. 243). `τ` is a best response to a probabilistic conjecture over the
rivals' remaining strategies `T`: its compound profile gives each rival `j` a convex combination
of strategies in `T_j`. -/
def BRToSomeConv (N : NormalForm I S) (T : (i : I) → Set (S i → ℝ)) (i : I) (τ : S i → ℝ) :
    Prop :=
  ∃ σ : (j : I) → S j → ℝ, IsMixedProfile σ ∧ (∀ j, j ≠ i → σ j ∈ convexHull ℝ (T j)) ∧
    IsBestResponse N i τ σ

/-- One round of removal of the strategies that are never a best response to a probabilistic
conjecture over the remaining strategies. -/
def ratStepConv (N : NormalForm I S) (T : (i : I) → Set (S i → ℝ)) :
    (i : I) → Set (S i → ℝ) :=
  fun i => {τ | τ ∈ T i ∧ BRToSomeConv N T i τ}

/-- The strategies surviving `n` rounds with probabilistic conjectures, from `Δ(S_i)`. -/
def ratIterConv (N : NormalForm I S) : ℕ → (i : I) → Set (S i → ℝ)
  | 0 => fun i => mixedExtension (S i)
  | n + 1 => ratStepConv N (ratIterConv N n)

/-- **Definition 8.C.2 with the probabilistic conjectures of footnote 1** (MWG, pp. 243-245).
The strategies in `Δ(S_i)` that survive iterated removal of strategies that are never a best
response to a probabilistic conjecture over the remaining strategies. -/
def RationalizableConv (N : NormalForm I S) (i : I) (τ : S i → ℝ) : Prop :=
  ∀ n, τ ∈ ratIterConv N n i

omit [∀ i, DecidableEq (S i)] in
/-- Every round lies in `Δ(S_i)`. -/
theorem ratIterConv_subset (N : NormalForm I S) : ∀ n i, ratIterConv N n i ⊆ mixedExtension (S i)
  | 0 => fun _ => le_rfl
  | n + 1 => fun i _ hτ => ratIterConv_subset N n i hτ.1

omit [∀ i, DecidableEq (S i)] in
/-- A set of strategies each of which is a best response to a probabilistic conjecture over the
set is never reduced, so it consists of rationalizable strategies (in the sense of
`RationalizableConv`). -/
theorem rationalizableConv_of_bestResponseSet {N : NormalForm I S}
    {T : (i : I) → Set (S i → ℝ)} (hTΔ : ∀ i, T i ⊆ mixedExtension (S i))
    (hT : ∀ i, ∀ τ ∈ T i, BRToSomeConv N T i τ) {i : I} {τ : S i → ℝ} (hτ : τ ∈ T i) :
    RationalizableConv N i τ := by
  have key : ∀ n i, T i ⊆ ratIterConv N n i := by
    intro n
    induction n with
    | zero => exact hTΔ
    | succ n ih =>
      intro i τ hτ
      obtain ⟨σ, hσ, hσT, hbr⟩ := hT i τ hτ
      exact ⟨ih i hτ, σ, hσ, fun j hj => convexHull_mono (ih j) (hσT j hj), hbr⟩
  exact fun n => key n i hτ

omit [Fintype I] [DecidableEq I] [∀ i, DecidableEq (S i)] in
/-- A convex combination of vectors that vanish off `P` vanishes off `P`. -/
theorem eq_zero_of_mem_convexHull {T : Type*} {C : Set (T → ℝ)} {P : Set T}
    (hC : ∀ τ ∈ C, ∀ b ∉ P, τ b = 0) {ρ : T → ℝ} (hρ : ρ ∈ convexHull ℝ C) :
    ∀ b ∉ P, ρ b = 0 := by
  have hconv : Convex ℝ {f : T → ℝ | ∀ b ∉ P, f b = 0} := by
    intro x hx y hy a c _ _ _ b hb
    simp [hx b hb, hy b hb]
  exact convexHull_min hC hconv hρ

/-- **Section 8.C** (MWG, p. 243), with probabilistic conjectures. Along any process of iterated
deletion of strictly dominated strategies, some round of the removal of never-best responses
keeps only strategies supported on the remaining pure strategies. -/
theorem exists_ratIterConv_support_subset {N : NormalForm I S} {Q : (i : I) → Set (S i)}
    (h : Relation.ReflTransGen (MSDStep N) (fullSets S) Q) :
    ∃ n, ∀ i, ∀ τ ∈ ratIterConv N n i, ∀ a, 0 < τ a → a ∈ Q i := by
  induction h with
  | refl => exact ⟨0, fun _ _ _ _ _ => Set.mem_univ _⟩
  | @tail P Q _ hstep ih =>
    obtain ⟨n, hn⟩ := ih
    refine ⟨n + 1, fun i τ hτ a ha => ?_⟩
    have haP : a ∈ P i := hn i τ hτ.1 a ha
    by_contra haQ
    obtain ⟨τ', hτ', -, hdom⟩ := hstep.2 i a haP haQ
    obtain ⟨σ, hσ, hσT, hbr⟩ := hτ.2
    have hC : ∀ j, ∀ ρ ∈ ratIterConv N n j, ∀ c ∉ P j, ρ c = 0 := by
      intro j ρ hρ c hc
      rcases ((ratIterConv_subset N n j hρ).1 c).eq_or_lt with h0 | h0
      · exact h0.symm
      · exact absurd (hn j ρ hρ c h0) hc
    have hsuppσ : ∀ j, j ≠ i → ∀ b, 0 < σ j b → b ∈ P j := by
      intro j hj b hb
      by_contra hbP
      have := eq_zero_of_mem_convexHull (hC j) (hσT j hj) b hbP
      linarith
    have hlt := msd_dominated_lt hdom hσ hsuppσ
    have hsupp := (isBestResponse_iff_support N i hbr.1 σ).1 hbr a ha
    have h1 := mixedPayoff_le_of_pure_le N σ i hτ' i hsupp
    linarith

/-- Along any process of iterated strict dominance, a conjecture supported on the remaining
strategies of the rivals has a best reply (among all pure strategies) that remains: a best
reply is never strictly dominated against such a conjecture. -/
theorem exists_max_mem_of_msdChain {N : NormalForm I S} {P : (i : I) → Set (S i)}
    (h : Relation.ReflTransGen (MSDStep N) (fullSets S) P) (k : I) {σ : (j : I) → S j → ℝ}
    (hσ : IsMixedProfile σ) (hsupp : ∀ l, l ≠ k → ∀ b, 0 < σ l b → b ∈ P l) :
    ∃ a ∈ P k, ∀ c, N.mixedPayoff (update σ k (pureMixed c)) k ≤
      N.mixedPayoff (update σ k (pureMixed a)) k := by
  revert hsupp
  induction h with
  | refl =>
    intro _
    obtain ⟨a₀, -⟩ := mixed_exists_pos (hσ k)
    obtain ⟨a, -, hmax⟩ := Finset.exists_max_image univ
      (fun c => N.mixedPayoff (update σ k (pureMixed c)) k) ⟨a₀, mem_univ _⟩
    exact ⟨a, Set.mem_univ _, fun c => hmax c (mem_univ c)⟩
  | @tail P Q _ hstep ih =>
    intro hsupp
    have hsuppP : ∀ l, l ≠ k → ∀ b, 0 < σ l b → b ∈ P l :=
      fun l hl b hb => hstep.1 l (hsupp l hl b hb)
    obtain ⟨a, haP, hmax⟩ := ih hsuppP
    refine ⟨a, ?_, hmax⟩
    by_contra haQ
    obtain ⟨τ', hτ', -, hdom⟩ := hstep.2 k a haP haQ
    have hlt := msd_dominated_lt hdom hσ hsuppP
    have h1 := mixedPayoff_le_of_pure_le N σ k hτ' k hmax
    linarith

/-- **Section 8.C** (MWG, p. 245, small type), the key step. In a two-player game, a pure
strategy that survives a complete process of iterated strict dominance is a best response, among
all of `Δ(S_k)`, to a mixed strategy of the opponent supported on the opponent's survivors
(Gordan's alternative in the remaining game, then `exists_max_mem_of_msdChain`). -/
theorem exists_belief_of_msdTerminal (N : NormalForm I S) {k o : I} (hko : k ≠ o)
    (htwo : ∀ l, l = k ∨ l = o) {Q : (i : I) → Set (S i)}
    (hQ : Relation.ReflTransGen (MSDStep N) (fullSets S) Q) (ht : MSDTerminal N Q)
    {b : S k} (hb : b ∈ Q k) :
    ∃ σ : (l : I) → S l → ℝ, IsMixedProfile σ ∧ (∀ d, 0 < σ o d → d ∈ Q o) ∧
      IsBestResponse N k (pureMixed b) σ := by
  classical
  -- the opponent has a surviving strategy
  obtain ⟨d₀, hd₀⟩ : (Q o).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    refine ht k b hb ⟨pureMixed b, isMixedStrategy_pureMixed b, fun c hc => ?_,
      fun r hr => absurd (hr o hko.symm) (by rw [hemp]; exact Set.notMem_empty _)⟩
    have : c = b := by
      by_contra hne
      simp [pureMixed, hne] at hc
    rwa [this]
  obtain ⟨r⟩ := two_nonempty htwo b d₀
  set U : S k → S o → ℝ := fun c d => N.payoff k (update (update r o d) k c) with hU
  have hpay : ∀ (τ : S k → ℝ) (s : (l : I) → S l),
      N.mixedPayoff (update (pureProfile s) k τ) k = ∑ c, τ c * U c (s o) :=
    fun τ s => two_mixedPayoff_pure N hko htwo r s τ
  have hpayb : ∀ s : (l : I) → S l, N.payoff k (update s k b) = U b (s o) := by
    intro s
    rw [← mixedPayoff_pureProfile_update, hpay]
    simp [pureMixed]
  set g : S k → S o → ℝ := fun c d => if c ∈ Q k then U c d - U b d else 0 with hg
  have hno : ¬ ∃ τ : S k → ℝ, (∀ c, 0 ≤ τ c) ∧ ∀ d ∈ Q o, 0 < ∑ c, τ c * g c d := by
    rintro ⟨τ, hτ0, hpos⟩
    set τ₀ : S k → ℝ := fun c => if c ∈ Q k then τ c else 0 with hτ₀
    have hτ₀0 : ∀ c, 0 ≤ τ₀ c := fun c => by
      simp only [hτ₀]; split_ifs
      · exact hτ0 c
      · exact le_rfl
    set t := ∑ c, τ₀ c with ht'
    have hsum : ∀ d, ∑ c, τ c * g c d = ∑ c, τ₀ c * U c d - t * U b d := by
      intro d
      rw [ht', Finset.sum_mul, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      simp only [hg, hτ₀]
      split_ifs <;> ring
    have htpos : 0 < t := by
      rcases (Finset.sum_nonneg fun c (_ : c ∈ univ) => hτ₀0 c).eq_or_lt with h0 | h0
      · have hz : ∀ c, τ₀ c = 0 := fun c =>
          (Finset.sum_eq_zero_iff_of_nonneg fun c _ => hτ₀0 c).1 h0.symm c (mem_univ c)
        have := hpos d₀ hd₀
        rw [hsum] at this
        have ht0 : t = 0 := h0.symm
        simp [hz, ht0] at this
      · exact h0
    set τ' : S k → ℝ := fun c => τ₀ c / t with hτ'
    refine ht k b hb ⟨τ', ⟨fun c => div_nonneg (hτ₀0 c) htpos.le, ?_⟩, fun c hc => ?_,
      fun r' hr' => ?_⟩
    · rw [hτ', ← Finset.sum_div, ← ht', div_self htpos.ne']
    · by_contra hcQ
      simp [hτ', hτ₀, hcQ] at hc
    · rw [hpayb, hpay]
      have h1 := hpos (r' o) (hr' o hko.symm)
      rw [hsum] at h1
      have h2 : ∑ c, τ' c * U c (r' o) = (∑ c, τ₀ c * U c (r' o)) / t := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl fun c _ => by rw [hτ']; ring
      rw [h2, lt_div_iff₀ htpos]
      linarith
  obtain ⟨y, hy0, hyQ, hYpos, hya⟩ := gordan_alternative g (Q o) hno
  set Y := ∑ d, y d with hY
  set y' : S o → ℝ := fun d => y d / Y with hy'
  have hy'm : IsMixedStrategy y' := by
    refine ⟨fun d => div_nonneg (hy0 d) hYpos.le, ?_⟩
    rw [hy', ← Finset.sum_div, ← hY, div_self hYpos.ne']
  set σ : (l : I) → S l → ℝ := update (pureProfile r) o y' with hσdef
  have hσo : σ o = y' := by rw [hσdef, update_self]
  have hσm : IsMixedProfile σ := by
    intro l
    rcases htwo l with rfl | rfl
    · rw [hσdef, update_of_ne hko]; exact isMixedProfile_pureProfile r l
    · rw [hσo]; exact hy'm
  have hsuppo : ∀ d, 0 < σ o d → d ∈ Q o := by
    intro d hd
    by_contra hdQ
    rw [hσo, hy'] at hd
    simp [hyQ d hdQ] at hd
  have hpayσ : ∀ c, N.mixedPayoff (update σ k (pureMixed c)) k = ∑ d, y' d * U c d := by
    intro c
    rw [two_mixedPayoff_eq N hko htwo r σ, hσo]
    simp [pureMixed]
    rfl
  obtain ⟨a, haQ, hmax⟩ := exists_max_mem_of_msdChain hQ k hσm (fun l hl d hd => by
    rcases htwo l with rfl | rfl
    · exact absurd rfl hl
    · exact hsuppo d hd)
  refine ⟨σ, hσm, hsuppo, isBestResponse_pureMixed_of_max N k σ fun c => ?_⟩
  refine (hmax c).trans ?_
  rw [hpayσ, hpayσ]
  have h1 := hya a
  have h2 : ∑ d, y' d * U a d - ∑ d, y' d * U b d = (∑ d, y d * g a d) / Y := by
    rw [← Finset.sum_sub_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun d _ => ?_
    simp only [hg, haQ, ite_true, hy']
    ring
  have h3 : (∑ d, y d * g a d) / Y ≤ 0 := div_nonpos_of_nonpos_of_nonneg h1 hYpos.le
  linarith

/-- **Section 8.C** (MWG, p. 245, small type), the reverse inclusion. In a two-player game, every
pure strategy that survives a complete process of iterated deletion of strictly dominated
strategies is rationalizable with probabilistic conjectures: the set of strategies that are best
responses to conjectures supported on the survivors is closed under best responses to mixtures of
its members. -/
theorem rationalizableConv_of_msdTerminal_two (N : NormalForm I S) {i j : I} (hij : i ≠ j)
    (htwo : ∀ k, k = i ∨ k = j) {Q : (i : I) → Set (S i)}
    (hQ : Relation.ReflTransGen (MSDStep N) (fullSets S) Q) (ht : MSDTerminal N Q) (k : I)
    {a : S k} (ha : a ∈ Q k) : RationalizableConv N k (pureMixed a) := by
  classical
  set T : (l : I) → Set (S l → ℝ) := fun l => {τ | IsMixedStrategy τ ∧
    ∃ σ : (m : I) → S m → ℝ, IsMixedProfile σ ∧ (∀ m, m ≠ l → ∀ d, 0 < σ m d → d ∈ Q m) ∧
      IsBestResponse N l τ σ} with hT
  have hpure : ∀ l (b : S l), b ∈ Q l → pureMixed b ∈ T l := by
    intro l b hb
    obtain ⟨o, hlo, htwo'⟩ := two_other hij htwo l
    obtain ⟨σ, hσ, hsupp, hbr⟩ := exists_belief_of_msdTerminal N hlo htwo' hQ ht hb
    refine ⟨isMixedStrategy_pureMixed b, σ, hσ, fun m hm d hd => ?_, hbr⟩
    rcases htwo' m with rfl | rfl
    · exact absurd rfl hm
    · exact hsupp d hd
  refine rationalizableConv_of_bestResponseSet (T := T) (fun l τ hτ => hτ.1)
    (fun l τ hτ => ?_) (hpure k a ha)
  obtain ⟨-, σ, hσ, hsupp, hbr⟩ := hτ
  refine ⟨σ, hσ, fun m hm => ?_, hbr⟩
  have hdecomp : σ m = ∑ d ∈ univ.filter (fun d => 0 < σ m d), σ m d • pureMixed d := by
    funext c
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, pureMixed, mul_ite, mul_one,
      mul_zero]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs with hc
    · rfl
    · exact le_antisymm (not_lt.1 hc) ((hσ m).1 c)
  rw [hdecomp]
  refine (convex_convexHull ℝ (T m)).sum_mem (fun d _ => (hσ m).1 d) ?_
    (fun d hd => subset_convexHull ℝ _ (hpure m d (hsupp m hm d (Finset.mem_filter.1 hd).2)))
  rw [Finset.sum_filter_of_ne fun d _ hd => ((hσ m).1 d).lt_of_ne (Ne.symm hd)]
  exact (hσ m).2

/-- **Section 8.C** (MWG, p. 245, small type), corrected. In a two-player game, a pure strategy
is rationalizable with probabilistic conjectures (footnote 1) iff it survives a complete process
of iterated deletion of strictly dominated strategies. -/
theorem rationalizableConv_iff_two (N : NormalForm I S) {i j : I} (hij : i ≠ j)
    (htwo : ∀ k, k = i ∨ k = j) {Q : (i : I) → Set (S i)}
    (hQ : Relation.ReflTransGen (MSDStep N) (fullSets S) Q) (ht : MSDTerminal N Q) (k : I)
    (a : S k) : RationalizableConv N k (pureMixed a) ↔ a ∈ Q k := by
  refine ⟨fun h => ?_, rationalizableConv_of_msdTerminal_two N hij htwo hQ ht k⟩
  obtain ⟨n, hn⟩ := exists_ratIterConv_support_subset hQ
  exact hn k _ (h n) a (by simp [pureMixed])

end MWG.SimultaneousMoveGames
