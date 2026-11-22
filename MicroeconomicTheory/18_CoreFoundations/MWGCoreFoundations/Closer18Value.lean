/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGCoreFoundations.ShapleyValue

/-!
# The hypergeometric-average formula for the Shapley value (MWG Section 18.E, p. 673)

MWG (p. 673) describe the Shapley value of an economy with type profile `(I₁, ..., I_H)` as an
average of marginal utilities `Δ_h v(I')` over profiles `I' ≤ I`, with weight `1/I` (the sample
size) times the probability of the profile `I'` when sampling `|I'|` consumers from the
population. Here players are `i : Fin n` with types `τ i`, and the game depends only on the type
profile of a coalition, `v(S) = w(I(S))` (`c18TypeGame`).

* `c18_card_profile_fiber`: the number of subsets `R ⊆ A` with type profile `m` is
  `∏_k C(I_k(A), m_k)` (a bijection with families of subsets of the type classes);
  `c18_sum_powerset_profile`: hence `∑_{R ⊆ A} G(I(R)) = ∑_m ∏_k C(I_k(A), m_k) G(m)`.
* `c18_shapley_types`, `c18_shapley_hypergeometric`: the exact formula. For a player `i` of type
  `h`, with `J = I - e_h` the profile of the other players,
  `Sh_i = ∑_{m ≤ J} (1/I) · [∏_k C(J_k, m_k) / C(I - 1, |m|)] · (w(m + e_h) - w(m))`:
  the sample size `|m|` of the OTHER players is uniform on `{0, ..., I - 1}` and, given the size,
  the profile is hypergeometric from the population `J` (not `I`), and the marginal utility is
  that of adding a type-`h` consumer to the sample.
* `c18_hypergeometric_weights_sum`: the weights sum to `1`.
* `c18_book_formula_counterexample` (correction): read literally (weights `1/I` times the
  hypergeometric probability of `I'` in samples from the population `I`, marginal utility
  `Δ_h v(I') = v(I') - v(I' - e_h)` for `I'_h ≥ 1`), the formula is not the Shapley value: with
  one consumer of each of two types and the additive `v(I') = I'₁ + I'₂` the Shapley value of type
  `1` is `1` and the literal formula gives `3/4`. The printed formula is the large-economy
  approximation of the exact one.

The value equivalence theorem itself (p. 673, "too advanced to be given here") is not formalised.
-/

namespace MWG.CoreFoundations

variable {H : Type*} [Fintype H] [DecidableEq H] {n : ℕ}

/-- **Section 18.E** (MWG, p. 673). The type profile `I(R)` of a set of consumers `R`:
`I_k(R) = #{i ∈ R : τ i = k}`. -/
def c18Profile (τ : Fin n → H) (R : Finset (Fin n)) : H → ℕ :=
  fun k => (R.filter fun i => τ i = k).card

/-- **Section 18.E** (MWG, p. 673). The TU game of an economy with types: the worth of a
coalition depends only on its type profile, `v(S) = w(I(S))`. -/
def c18TypeGame (w : (H → ℕ) → ℝ) (τ : Fin n → H) : WelfareBargaining.Game n :=
  fun S => w (c18Profile τ S)

/-- The profiles `m ≤ I(A)`, as a finite set. -/
def c18Box (c : H → ℕ) : Finset (H → ℕ) :=
  Fintype.piFinset fun k => Finset.range (c k + 1)

/-- **Section 18.E** (MWG, p. 673). The number of subsets `R ⊆ A` with type profile `m` is
`∏_k C(I_k(A), m_k)`. -/
theorem c18_card_profile_fiber (τ : Fin n → H) (A : Finset (Fin n)) (m : H → ℕ) :
    (A.powerset.filter fun R => c18Profile τ R = m).card =
      ∏ k, (c18Profile τ A k).choose (m k) := by
  have hpi : (Fintype.piFinset fun k =>
      (A.filter fun i => τ i = k).powersetCard (m k)).card =
      ∏ k, (c18Profile τ A k).choose (m k) := by
    rw [Fintype.card_piFinset]
    exact Finset.prod_congr rfl fun k _ => Finset.card_powersetCard _ _
  rw [← hpi]
  have key : ∀ F : H → Finset (Fin n), (∀ k, F k ⊆ A.filter fun i => τ i = k) →
      ∀ k, (Finset.univ.biUnion F).filter (fun i => τ i = k) = F k := by
    intro F hF k
    ext x
    simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨j, hj⟩, hx⟩
      have := (Finset.mem_filter.1 (hF j hj)).2
      rw [this] at hx
      subst hx
      exact hj
    · intro hx
      exact ⟨⟨k, hx⟩, (Finset.mem_filter.1 (hF k hx)).2⟩
  refine Finset.card_bij' (fun R _ => fun k => R.filter fun i => τ i = k)
    (fun F _ => Finset.univ.biUnion F) (fun R hR => ?_) (fun F hF => ?_) (fun R _ => ?_)
    (fun F hF => ?_)
  · rw [Finset.mem_filter, Finset.mem_powerset] at hR
    rw [Fintype.mem_piFinset]
    intro k
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.filter_subset_filter _ hR.1, congrFun hR.2 k⟩
  · rw [Fintype.mem_piFinset] at hF
    have hF' : ∀ k, F k ⊆ A.filter fun i => τ i = k := fun k =>
      (Finset.mem_powersetCard.1 (hF k)).1
    rw [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨Finset.biUnion_subset.2 fun k _ => (hF' k).trans (Finset.filter_subset _ _), ?_⟩
    funext k
    simp only [c18Profile]
    rw [key F hF' k]
    exact (Finset.mem_powersetCard.1 (hF k)).2
  · ext x
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter]
    exact ⟨fun ⟨_, hx, _⟩ => hx, fun hx => ⟨τ x, hx, rfl⟩⟩
  · rw [Fintype.mem_piFinset] at hF
    funext k
    exact key F (fun k => (Finset.mem_powersetCard.1 (hF k)).1) k

omit [Fintype H] in
/-- The profile of a subset is bounded by the profile of the set. -/
theorem c18_profile_mono (τ : Fin n → H) {R A : Finset (Fin n)} (h : R ⊆ A) (k : H) :
    c18Profile τ R k ≤ c18Profile τ A k :=
  Finset.card_le_card (Finset.filter_subset_filter _ h)

/-- **Section 18.E** (MWG, p. 673). Summing a function of the type profile over the subsets of
`A`: `∑_{R ⊆ A} G(I(R)) = ∑_{m ≤ I(A)} ∏_k C(I_k(A), m_k) G(m)`. -/
theorem c18_sum_powerset_profile (τ : Fin n → H) (A : Finset (Fin n)) (G : (H → ℕ) → ℝ) :
    ∑ R ∈ A.powerset, G (c18Profile τ R) =
      ∑ m ∈ c18Box (c18Profile τ A), (∏ k, ((c18Profile τ A k).choose (m k) : ℝ)) * G m := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := A.powerset) (t := c18Box (c18Profile τ A))
    (g := c18Profile τ)]
  · refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.sum_congr rfl fun R hR => by rw [(Finset.mem_filter.1 hR).2], Finset.sum_const,
      c18_card_profile_fiber, nsmul_eq_mul]
    push_cast
    rfl
  · intro R hR
    rw [c18Box, Fintype.mem_piFinset]
    intro k
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact c18_profile_mono τ (Finset.mem_powerset.1 hR) k

omit [Fintype H] in
/-- Adding a consumer `i ∉ R` adds `e_{τ i}` to the profile. -/
theorem c18_profile_insert (τ : Fin n → H) {R : Finset (Fin n)} {i : Fin n} (hi : i ∉ R) :
    c18Profile τ (insert i R) = c18Profile τ R + Pi.single (τ i) 1 := by
  funext k
  simp only [c18Profile, Finset.filter_insert, Pi.add_apply, Pi.single_apply]
  by_cases h : τ i = k
  · simp only [h, ↓reduceIte]
    exact Finset.card_insert_of_notMem fun hm => hi (Finset.mem_filter.1 hm).1
  · simp only [h, Ne.symm h, ↓reduceIte, add_zero]

/-- The size of a set is the sum of its profile. -/
theorem c18_card_eq_sum_profile (τ : Fin n → H) (R : Finset (Fin n)) :
    R.card = ∑ k, c18Profile τ R k :=
  Finset.card_eq_sum_card_fiberwise fun _ _ => Finset.mem_univ _

omit [Fintype H] in
/-- The profile of the other players: `I(I \ {i}) = I - e_{τ i}`. -/
theorem c18_profile_erase (τ : Fin n → H) (i : Fin n) :
    c18Profile τ (Finset.univ.erase i) = c18Profile τ Finset.univ - Pi.single (τ i) 1 := by
  have h := c18_profile_insert τ (Finset.notMem_erase i Finset.univ)
  rw [Finset.insert_erase (Finset.mem_univ i)] at h
  rw [h]
  funext k
  simp only [Pi.sub_apply, Pi.add_apply, add_tsub_cancel_right]

/-- The Shapley value does not depend on `v(∅)`. -/
theorem c18_shapley_sub_const (v : WelfareBargaining.Game n) (c : ℝ) (i : Fin n) :
    WelfareBargaining.shapley (fun S => v S - c) i = WelfareBargaining.shapley v i := by
  simp only [WelfareBargaining.shapley, WelfareBargaining.margContrib]
  congr 1
  exact Finset.sum_congr rfl fun _ _ => by ring

omit [Fintype H] in
/-- **Section 18.E** (MWG, p. 673), the Shapley value of an economy with types as a sum over the
sets `R` of other players: `Sh_i = ∑_{R ⊆ I \ {i}} (I - 1 - |R|)! |R|! / I! · (w(I(R) + e_{τ i}) -
w(I(R)))` (from (18.AA.4)). -/
theorem c18_shapley_types (w : (H → ℕ) → ℝ) (τ : Fin n → H) (i : Fin n) :
    WelfareBargaining.shapley (c18TypeGame w τ) i =
      ∑ R ∈ (Finset.univ.erase i).powerset,
        ((n - 1 - R.card).factorial * R.card.factorial / n.factorial : ℝ) *
          (w (c18Profile τ R + Pi.single (τ i) 1) - w (c18Profile τ R)) := by
  classical
  have h0 : c18Profile τ (∅ : Finset (Fin n)) = 0 := by
    funext k; simp [c18Profile]
  have hshift : WelfareBargaining.shapley (c18TypeGame w τ) i =
      WelfareBargaining.shapley (c18TypeGame (fun m => w m - w 0) τ) i :=
    (c18_shapley_sub_const (c18TypeGame w τ) (w 0) i).symm
  rw [hshift, ← formula_18_AA_4 _ (by simp [c18TypeGame, h0])]
  unfold subsetFormula
  rw [Finset.card_univ, Fintype.card_fin]
  conv_lhs => rw [← Finset.insert_erase (Finset.mem_univ i),
    Finset.sum_powerset_insert (Finset.notMem_erase i Finset.univ)]
  rw [Finset.sum_eq_zero fun T hT => by
    have hT' : i ∉ T := fun h => Finset.notMem_erase i Finset.univ (Finset.mem_powerset.1 hT h)
    simp only [hT', ↓reduceIte], zero_add]
  refine Finset.sum_congr rfl fun R hR => ?_
  have hiR : i ∉ R := fun h => Finset.notMem_erase i Finset.univ (Finset.mem_powerset.1 hR h)
  have e : n - (R.card + 1) = n - 1 - R.card := by omega
  simp only [Finset.mem_insert_self, ↓reduceIte]
  rw [Finset.card_insert_of_notMem hiR, Finset.erase_insert hiR, Nat.add_sub_cancel, e,
    c18TypeGame, c18TypeGame, c18_profile_insert τ hiR]
  ring

/-- **Section 18.E** (MWG, p. 673), the hypergeometric-average formula, corrected. For a player
`i` of type `h = τ i`, with `J = I - e_h` the profile of the other players
(`c18_profile_erase`),
`Sh_i = ∑_{m ≤ J} (1/I) · [∏_k C(J_k, m_k) / C(I - 1, |m|)] · (w(m + e_h) - w(m))`: the weight is
`1/I` for the sample size `|m| ∈ {0, ..., I - 1}` times the hypergeometric probability of the
profile `m` in a sample of that size from the other players. -/
theorem c18_shapley_hypergeometric (w : (H → ℕ) → ℝ) (τ : Fin n → H) (i : Fin n) :
    WelfareBargaining.shapley (c18TypeGame w τ) i =
      ∑ m ∈ c18Box (c18Profile τ (Finset.univ.erase i)),
        (1 / n : ℝ) * ((∏ k, ((c18Profile τ (Finset.univ.erase i) k).choose (m k) : ℝ)) /
          ((n - 1).choose (∑ k, m k) : ℝ)) * (w (m + Pi.single (τ i) 1) - w m) := by
  rw [c18_shapley_types]
  simp_rw [c18_card_eq_sum_profile τ]
  refine (c18_sum_powerset_profile τ (Finset.univ.erase i) (fun m =>
    ((n - 1 - ∑ k, m k).factorial * (∑ k, m k).factorial / n.factorial : ℝ) *
      (w (m + Pi.single (τ i) 1) - w m))).trans ?_
  refine Finset.sum_congr rfl fun m hm => ?_
  have hn : 0 < n := Fin.pos i
  have hJ : ∑ k, c18Profile τ (Finset.univ.erase i) k = n - 1 := by
    rw [← c18_card_eq_sum_profile, Finset.card_erase_of_mem (Finset.mem_univ i),
      Finset.card_univ, Fintype.card_fin]
  have hs : ∑ k, m k ≤ n - 1 := by
    rw [← hJ]
    refine Finset.sum_le_sum fun k _ => ?_
    have := (Fintype.mem_piFinset.1 hm) k
    rw [Finset.mem_range] at this
    omega
  have hc := Nat.choose_mul_factorial_mul_factorial hs
  have hf : n * (n - 1).factorial = n.factorial := Nat.mul_factorial_pred hn.ne'
  have hc' : ((n - 1).choose (∑ k, m k) : ℝ) * (∑ k, m k).factorial *
      (n - 1 - ∑ k, m k).factorial = (n - 1).factorial := by exact_mod_cast hc
  have hf' : (n : ℝ) * (n - 1).factorial = n.factorial := by exact_mod_cast hf
  have hpos : (0 : ℝ) < ((n - 1).choose (∑ k, m k) : ℝ) := by
    exact_mod_cast Nat.choose_pos hs
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hw : ((n - 1 - ∑ k, m k).factorial * (∑ k, m k).factorial / n.factorial : ℝ) =
      1 / n / ((n - 1).choose (∑ k, m k) : ℝ) := by
    rw [← hf', ← hc']
    field_simp
  rw [hw]
  ring

/-- **Section 18.E** (MWG, p. 673). The weights of the hypergeometric-average formula form a
probability distribution: `∑_{m ≤ J} (1/I) ∏_k C(J_k, m_k) / C(I - 1, |m|) = 1` (apply the formula
to the additive game `w(m) = |m|`, whose Shapley value is `1` by Chapter 22). -/
theorem c18_hypergeometric_weights_sum (τ : Fin n → H) (i : Fin n) :
    ∑ m ∈ c18Box (c18Profile τ (Finset.univ.erase i)),
      (1 / n : ℝ) * ((∏ k, ((c18Profile τ (Finset.univ.erase i) k).choose (m k) : ℝ)) /
        ((n - 1).choose (∑ k, m k) : ℝ)) = 1 := by
  have hgame : c18TypeGame (fun m => ((∑ k, m k : ℕ) : ℝ)) τ =
      fun S => ∑ _j ∈ S, (1 : ℝ) := by
    funext S
    simp only [c18TypeGame, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [← c18_card_eq_sum_profile]
  have h := c18_shapley_hypergeometric (fun m => ((∑ k, m k : ℕ) : ℝ)) τ i
  rw [hgame, WelfareBargaining.shapley_additive] at h
  have h' : (1 : ℝ) = _ := h
  refine Eq.trans (Finset.sum_congr rfl fun m _ => ?_) h'.symm
  have : ((∑ k, (m + Pi.single (τ i) (1 : ℕ) : H → ℕ) k : ℕ) : ℝ) - ((∑ k, m k : ℕ) : ℝ) =
      1 := by
    simp only [Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single', Finset.mem_univ,
      ↓reduceIte]
    push_cast
    ring
  rw [this, mul_one]

/-- **Section 18.E** (MWG, p. 673), the formula as printed: weight `1/I` times the hypergeometric
probability `∏_k C(I_k, I'_k) / C(I, |I'|)` of the profile `I'` in a sample of size `|I'|` from the
population `I`, times `Δ_h v(I') = v(I') - v(I' - e_h)`, summed over `I' ≤ I` with `I'_h ≥ 1`. -/
noncomputable def c18BookFormula (w : (H → ℕ) → ℝ) (I : H → ℕ) (h : H) : ℝ :=
  ∑ m ∈ c18Box I, if 1 ≤ m h then
    (1 / (∑ k, I k : ℕ) : ℝ) * ((∏ k, ((I k).choose (m k) : ℝ)) /
      ((∑ k, I k).choose (∑ k, m k) : ℝ)) * (w m - w (m - Pi.single h 1)) else 0

/-- **Section 18.E** (MWG, p. 673), correction: the formula as printed (`c18BookFormula`) is not
the Shapley value. With two types, one consumer of each (`τ = id` on `Fin 2`), and the additive
`v(I') = I'₁ + I'₂`, the Shapley value of the type-`1` consumer is `1`, while the printed formula
gives `3/4` (its weights over profiles with `I'_h ≥ 1` add up to `3/4`). The exact formula is
`c18_shapley_hypergeometric`. -/
theorem c18_book_formula_counterexample :
    WelfareBargaining.shapley
        (c18TypeGame (fun m : Fin 2 → ℕ => ((m 0 + m 1 : ℕ) : ℝ)) (id : Fin 2 → Fin 2)) 0 = 1 ∧
      c18Profile (id : Fin 2 → Fin 2) Finset.univ = (fun _ => 1) ∧
      c18BookFormula (fun m : Fin 2 → ℕ => ((m 0 + m 1 : ℕ) : ℝ)) (fun _ => 1) 0 = 3 / 4 := by
  refine ⟨?_, ?_, ?_⟩
  · have hgame : c18TypeGame (fun m : Fin 2 → ℕ => ((m 0 + m 1 : ℕ) : ℝ)) (id : Fin 2 → Fin 2) =
        fun S => ∑ _j ∈ S, (1 : ℝ) := by
      funext S
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      rw [c18_card_eq_sum_profile (id : Fin 2 → Fin 2) S, Fin.sum_univ_two]
      rfl
    rw [hgame, WelfareBargaining.shapley_additive]
  · funext k
    simp only [c18Profile, id]
    rw [Finset.filter_eq' Finset.univ k]
    simp
  · have hbox : c18Box (fun _ : Fin 2 => 1) = {![0, 0], ![0, 1], ![1, 0], ![1, 1]} := by
      decide
    rw [c18BookFormula, hbox]
    simp [Finset.sum_insert, Fin.sum_univ_two, Fin.prod_univ_two]
    norm_num

end MWG.CoreFoundations
