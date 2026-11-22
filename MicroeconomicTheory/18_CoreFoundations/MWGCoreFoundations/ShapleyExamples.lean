/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGCoreFoundations.ShapleyValue
import Mathlib.Analysis.Convex.Deriv

/-!
# The glove market, convex games and production games (MWG Appendix A, pp. 681-684;
Exercises 18.AA.7-18.AA.8)

* **Example 18.AA.7** (glove market): the six orderings give player 3 the marginal contributions
  `1, 1, 1, 1, 0, 0` (`example_18_AA_7_orderings`), `Sh = (1/6, 1/6, 2/3)`
  (`example_18_AA_7`), the displayed instance of (18.AA.2) (`example_18_AA_7_check`), and the
  continuation of p. 683: the core is `{(0, 0, 1)}` (`example_18_AA_7_core`), with the book's
  blocking construction (`example_18_AA_7_block`); the Shapley value is not in the core
  (`example_18_AA_7_shapley_not_core`), as it trivially is not when the core is empty
  (`shapley_not_core_majority`).
* **Definition 18.AA.8** (`IsConvexGame`) and **Proposition 18.AA.1** (`proposition_18_AA_1`):
  the Shapley value of a convex game is in the core. Departure in the route only: we prove that
  every marginal-contribution vector is in the core (`marginal_vector_mem_core`), and the Shapley
  value is their average (18.AA.3), instead of the book's comparison `Shᵢ(S, v) ≤ Shᵢ(T, v)`.
* **Example 18.AA.8 / Exercise 18.AA.7** (`exercise_18_AA_7`): production games with
  complementary inputs are convex. Departure: the hypothesis `∂²f/∂z_h∂z_k ≥ 0` is stated as the
  increasing-differences property `f(z + a) - f(z) ≤ f(z' + a) - f(z')` for `0 ≤ z ≤ z'`, `a ≥ 0`
  (`IncreasingDifferences`, which it implies for `C²` functions on the orthant: proved in
  `Closer18AA`, `example_18_AA_8_increasingDifferences`). The text's "Exercise 18.AA.8" on
  p. 683 is Exercise 18.AA.7 (correction).
  For `N = 1` convexity of `f` suffices (`example_18_AA_8_one_input`, with the second-derivative
  form `example_18_AA_8_one_input_deriv`); for `N > 1` the condition is neither sufficient
  (`z₁z₂`) nor necessary (`(z₁ - z₂)²`) for convexity of `f` (`example_18_AA_8_not_sufficient`,
  `example_18_AA_8_not_necessary`).
* **Exercise 18.AA.8** (`exercise_18_AA_8`): `f(z) = max(z₁, z₂)` is convex, but the game with
  `ω₁ = (1, 0)`, `ω₂ = (0, 1)` has an empty core and is not convex.
-/

namespace MWG.CoreFoundations

variable {n : ℕ}

/-! ### Example 18.AA.7: the glove market -/

/-- **Example 18.AA.7** (MWG, p. 681). The glove market of Example 18.AA.7 with integer worths:
players `1, 2` (here `0, 1`) own a right glove, player `3` (here `2`) a left glove; a coalition is
worth `1` iff it holds a pair. -/
def gloveInt (S : Finset (Fin 3)) : ℤ := if 2 ∈ S ∧ (0 ∈ S ∨ 1 ∈ S) then 1 else 0

/-- **Example 18.AA.7** (MWG, p. 681). The glove market game. -/
def gloveGame : WelfareBargaining.Game 3 := fun S => (gloveInt S : ℝ)

/-- **Example 18.AA.7** (MWG, p. 681). The worths: `v({1,2,3}) = v({1,3}) = v({2,3}) = 1`,
`v({1,2}) = 0` and `v({i}) = 0`. -/
theorem example_18_AA_7_values :
    gloveGame Finset.univ = 1 ∧ gloveGame {0, 2} = 1 ∧ gloveGame {1, 2} = 1 ∧
      gloveGame {0, 1} = 0 ∧ ∀ i, gloveGame {i} = 0 := by
  refine ⟨by simp [gloveGame, gloveInt], by simp [gloveGame, gloveInt],
    by simp [gloveGame, gloveInt], by simp [gloveGame, gloveInt], fun i => ?_⟩
  fin_cases i <;> simp [gloveGame, gloveInt]

/-- **Example 18.AA.7** (MWG, p. 682). Player 3's marginal contribution in the ordering `π` (integer
version). -/
def gloveMarg (σ : Equiv.Perm (Fin 3)) : ℤ :=
  gloveInt (insert 2 (WelfareBargaining.preds σ 2)) - gloveInt (WelfareBargaining.preds σ 2)

/-- **Example 18.AA.7** (MWG, p. 682). Over the six orderings, player 3's marginal contributions
are `1, 1, 1, 1, 0, 0`: four orderings give `1`, two give `0`, and they add up to `4`. -/
theorem example_18_AA_7_orderings :
    (Finset.univ.filter fun σ : Equiv.Perm (Fin 3) => gloveMarg σ = 1).card = 4 ∧
      (Finset.univ.filter fun σ : Equiv.Perm (Fin 3) => gloveMarg σ = 0).card = 2 ∧
      ∑ σ : Equiv.Perm (Fin 3), gloveMarg σ = 4 := by
  decide

/-- **Example 18.AA.7** (MWG, p. 681). `v(∅) = 0` (footnote 31). -/
theorem gloveGame_empty : gloveGame ∅ = 0 := by simp [gloveGame, gloveInt]

/-- **Example 18.AA.7** (MWG, p. 682). Players 1 and 2 play symmetric roles. -/
theorem gloveGame_swap : ∀ S : Finset (Fin 3),
    gloveGame S = gloveGame (S.map (Equiv.swap (0 : Fin 3) 1).toEmbedding) := by
  have h : ∀ S : Finset (Fin 3),
      gloveInt S = gloveInt (S.map (Equiv.swap (0 : Fin 3) 1).toEmbedding) := by decide
  intro S
  simp only [gloveGame]
  rw [h S]

/-- **Example 18.AA.7** (MWG, p. 682). The Shapley value of the glove market is
`(1/6, 1/6, 2/3)`. -/
theorem example_18_AA_7 :
    WelfareBargaining.shapley gloveGame = ![1 / 6, 1 / 6, 2 / 3] := by
  have h2 : WelfareBargaining.shapley gloveGame 2 = 2 / 3 := by
    have hm : ∀ σ : Equiv.Perm (Fin 3),
        WelfareBargaining.margContrib gloveGame σ 2 = ((gloveMarg σ : ℤ) : ℝ) := by
      intro σ
      simp [WelfareBargaining.margContrib, gloveMarg, gloveGame]
    simp only [WelfareBargaining.shapley, hm]
    rw [← Int.cast_sum, example_18_AA_7_orderings.2.2]
    simp [Nat.factorial]
    norm_num
  have h01 : WelfareBargaining.shapley gloveGame 0 = WelfareBargaining.shapley gloveGame 1 :=
    shapley_symmetry_footnote_33 gloveGame_empty
      ((rolesPermuted_iff gloveGame gloveGame 0 1).2 gloveGame_swap)
  have hsum := shapley_efficiency gloveGame gloveGame_empty
  rw [Fin.sum_univ_three, h2, ← h01, example_18_AA_7_values.1] at hsum
  funext i
  fin_cases i
  · simp; linarith
  · simp; linarith
  · simpa using h2

/-- **Example 18.AA.7** (MWG, p. 682). The numbers satisfy (18.AA.2), e.g.
`Sh₃(I, v) - Sh₃(I \ {1}, v) = 2/3 - 1/2 = 1/6 - 0 = Sh₁(I, v) - Sh₁(I \ {3}, v)`. -/
theorem example_18_AA_7_check :
    shapleyFamily gloveGame Finset.univ 2 = 2 / 3 ∧
      shapleyFamily gloveGame (Finset.univ.erase 0) 2 = 1 / 2 ∧
      shapleyFamily gloveGame Finset.univ 0 = 1 / 6 ∧
      shapleyFamily gloveGame (Finset.univ.erase 2) 0 = 0 ∧
      shapleyFamily gloveGame Finset.univ 2 - shapleyFamily gloveGame (Finset.univ.erase 0) 2 =
        shapleyFamily gloveGame Finset.univ 0 -
          shapleyFamily gloveGame (Finset.univ.erase 2) 0 := by
  have hφ := shapleyFamily_isEgalitarian gloveGame gloveGame_empty
  have hI : ∀ i, shapleyFamily gloveGame Finset.univ i = WelfareBargaining.shapley gloveGame i :=
    fun i => congrFun (formula_18_AA_3 gloveGame gloveGame_empty) i
  have e0 : (Finset.univ.erase (0 : Fin 3)) = {2, 1} := by decide
  have e2 : (Finset.univ.erase (2 : Fin 3)) = {0, 1} := by decide
  have a : shapleyFamily gloveGame Finset.univ 2 = 2 / 3 := by
    rw [hI, example_18_AA_7]; simp
  have b : shapleyFamily gloveGame (Finset.univ.erase 0) 2 = 1 / 2 := by
    rw [e0, egalitarian_pair hφ (by decide)]
    simp [gloveGame, gloveInt]
  have c : shapleyFamily gloveGame Finset.univ 0 = 1 / 6 := by
    rw [hI, example_18_AA_7]; simp
  have d : shapleyFamily gloveGame (Finset.univ.erase 2) 0 = 0 := by
    rw [e2, egalitarian_pair hφ (by decide)]
    simp [gloveGame, gloveInt]
  refine ⟨a, b, c, d, ?_⟩
  rw [a, b, c, d]; norm_num

/-- **Example 18.AA.7 continued** (MWG, p. 683). The total payoff of a coalition at `(0, 0, 1)`. -/
theorem sum_glove_core (S : Finset (Fin 3)) :
    ∑ i ∈ S, (![0, 0, 1] : Fin 3 → ℝ) i = if 2 ∈ S then 1 else 0 := by
  have h : ∀ S : Finset (Fin 3), S = ∅ ∨ S = {0} ∨ S = {1} ∨ S = {2} ∨ S = {0, 1} ∨
      S = {0, 2} ∨ S = {1, 2} ∨ S = Finset.univ := by decide
  rcases h S with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Fin.sum_univ_three]

/-- **Example 18.AA.7 continued** (MWG, p. 683). The core of the glove market consists of the
single outcome `(0, 0, 1)`. -/
theorem example_18_AA_7_core : tuCore gloveGame = {![0, 0, 1]} := by
  ext u
  simp only [Set.mem_singleton_iff]
  constructor
  · rintro ⟨hS, htot⟩
    have h0 := hS {0} (by simp)
    have h1 := hS {1} (by simp)
    have h2 := hS {2} (by simp)
    have h02 := hS {0, 2} (by simp)
    have h12 := hS {1, 2} (by simp)
    simp [gloveGame, gloveInt, Fin.sum_univ_three] at h0 h1 h2 h02 h12 htot
    funext i
    fin_cases i <;> simp <;> linarith
  · rintro rfl
    refine ⟨fun S _ => ?_, ?_⟩
    · rw [sum_glove_core]
      simp only [gloveGame, gloveInt]
      split_ifs <;> simp_all
    · rw [sum_glove_core]; simp [gloveGame, gloveInt]

/-- **Example 18.AA.7 continued** (MWG, p. 683). If `u₁ + u₂ + u₃ = 1` and `u₁ > 0`, the
coalition `{2, 3}` blocks `u` by means of `(0, u₂ + u₁/2, u₃ + u₁/2)`. -/
theorem example_18_AA_7_block {u : Fin 3 → ℝ} (hsum : u 0 + u 1 + u 2 = 1) (hu : 0 < u 0) :
    ntuBlocks (tuSet gloveGame) {1, 2} u ∧
      ![0, u 1 + u 0 / 2, u 2 + u 0 / 2] ∈ tuSet gloveGame {1, 2} := by
  have hmem : ![0, u 1 + u 0 / 2, u 2 + u 0 / 2] ∈ tuSet gloveGame {1, 2} := by
    simp only [tuSet, Set.mem_ofPred_eq]
    simp [gloveGame, gloveInt]
    linarith
  refine ⟨⟨by simp, _, hmem, fun i hi => ?_⟩, hmem⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl <;> simp <;> linarith

/-- **Example 18.AA.7 continued** (MWG, p. 683). The Shapley value, although skewed towards
player 3, is not in the core: it leaves `1/6` to each owner of a right glove. -/
theorem example_18_AA_7_shapley_not_core :
    WelfareBargaining.shapley gloveGame ∉ tuCore gloveGame := by
  rw [example_18_AA_7_core, example_18_AA_7, Set.mem_singleton_iff]
  intro h
  have := congrFun h 0
  simp at this

/-- **Appendix A** (MWG, pp. 682-683). The Shapley value is defined for every game, so it need not
be in the core when the core is empty: e.g. the TU majority voting game of Example 18.AA.3. -/
theorem shapley_not_core_majority :
    WelfareBargaining.shapley tuMajority ∉ tuCore tuMajority := by
  rw [example_18_AA_4_tu]
  exact Set.notMem_empty _

/-! ### Convex games: Definition 18.AA.8 and Proposition 18.AA.1 -/

/-- **Definition 18.AA.8** (MWG, p. 683). A convex game: marginal contributions increase with
the coalition, `v(S ∪ {i}) - v(S) ≤ v(T ∪ {i}) - v(T)` for `S ⊆ T` and `i ∉ T`. -/
def IsConvexGame (v : WelfareBargaining.Game n) : Prop :=
  ∀ S T : Finset (Fin n), S ⊆ T → ∀ i, i ∉ T → v (insert i S) - v S ≤ v (insert i T) - v T

/-- **Proposition 18.AA.1** (MWG, p. 683), key step: in a convex game every vector of marginal
contributions along an ordering gives every coalition at least its worth. -/
theorem marginal_vector_mem_core {v : WelfareBargaining.Game n} (hc : IsConvexGame v)
    (hv : v ∅ = 0) (σ : Equiv.Perm (Fin n)) :
    ∀ S : Finset (Fin n), v S ≤ ∑ i ∈ S, WelfareBargaining.margContrib v σ i := by
  classical
  intro S
  induction S using Finset.strongInduction with
  | H S ih =>
    rcases S.eq_empty_or_nonempty with rfl | hne
    · simp [hv]
    obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image S (fun k => σ k) hne
    have hsub : S.erase j ⊆ WelfareBargaining.preds σ j := by
      intro k hk
      obtain ⟨hkj, hkS⟩ := Finset.mem_erase.1 hk
      simp only [WelfareBargaining.preds, Finset.mem_filter, Finset.mem_univ, true_and]
      exact lt_of_le_of_ne (hmax k hkS) fun e => hkj (σ.injective e)
    have hjp : j ∉ WelfareBargaining.preds σ j := by simp [WelfareBargaining.preds]
    have hconv := hc _ _ hsub j hjp
    rw [Finset.insert_erase hj] at hconv
    have hih := ih _ (Finset.erase_ssubset hj)
    rw [← Finset.add_sum_erase S _ hj]
    simp only [WelfareBargaining.margContrib] at hconv hih ⊢
    linarith

/-- **Proposition 18.AA.1** (MWG, p. 683). If the game is convex then its Shapley value is in the
core (in particular, the core is nonempty). -/
theorem proposition_18_AA_1 {v : WelfareBargaining.Game n} (hc : IsConvexGame v)
    (hv : v ∅ = 0) : WelfareBargaining.shapley v ∈ tuCore v := by
  refine ⟨fun S _ => ?_, (shapley_efficiency v hv).le⟩
  simp only [WelfareBargaining.shapley]
  rw [← Finset.mul_sum, Finset.sum_comm]
  have hfac : (0 : ℝ) < (n.factorial : ℝ) := Nat.cast_pos.2 (Nat.factorial_pos n)
  have hle : ∑ _σ : Equiv.Perm (Fin n), v S ≤
      ∑ σ : Equiv.Perm (Fin n), ∑ i ∈ S, WelfareBargaining.margContrib v σ i :=
    Finset.sum_le_sum fun σ _ => marginal_vector_mem_core hc hv σ S
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    nsmul_eq_mul] at hle
  rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hfac]
  linarith

/-! ### Example 18.AA.8 and Exercises 18.AA.7-18.AA.8: production games -/

/-- **Example 18.AA.8** (MWG, p. 683). Increasing marginal productivities, stated as increasing
differences on `ℝ^N₊`: `f(z + a) - f(z) ≤ f(z' + a) - f(z')` for `0 ≤ z ≤ z'` and `a ≥ 0` (for
`C²` functions this is the condition `∂²f/∂z_h∂z_k ≥ 0` for all `h, k`). -/
def IncreasingDifferences {N : ℕ} (f : (Fin N → ℝ) → ℝ) : Prop :=
  ∀ z z' a : Fin N → ℝ, 0 ≤ z → z ≤ z' → 0 ≤ a → f (z + a) - f z ≤ f (z' + a) - f z'

/-- **Example 18.AA.8** (MWG, p. 683). The TU game of an `N`-input technology `f` with input
endowments `ωᵢ ∈ ℝ^N₊`: `v(S) = f(∑_{i∈S} ωᵢ)`. -/
def inputGame {N : ℕ} (f : (Fin N → ℝ) → ℝ) (ω : Fin n → Fin N → ℝ) :
    WelfareBargaining.Game n := fun S => f (∑ i ∈ S, ω i)

/-- **Exercise 18.AA.7** (MWG, p. 686; called "Exercise 18.AA.8" on p. 683). The production game
of Example 18.AA.8 is convex. -/
theorem exercise_18_AA_7 {N : ℕ} {f : (Fin N → ℝ) → ℝ} (hf : IncreasingDifferences f)
    {ω : Fin n → Fin N → ℝ} (hω : ∀ i, 0 ≤ ω i) : IsConvexGame (inputGame f ω) := by
  classical
  intro S T hST i hiT
  have hiS : i ∉ S := fun h => hiT (hST h)
  simp only [inputGame]
  rw [Finset.sum_insert hiS, Finset.sum_insert hiT, add_comm (ω i), add_comm (ω i)]
  exact hf _ _ _ (Finset.sum_nonneg fun j _ => hω j)
    (Finset.sum_le_sum_of_subset_of_nonneg hST fun j _ _ => hω j) (hω i)

/-- **Example 18.AA.8** (MWG, p. 683). A convex function on `ℝ₊` has increasing differences. -/
theorem convexOn_increasing_differences {f : ℝ → ℝ} (hf : ConvexOn ℝ (Set.Ici 0) f)
    {z z' a : ℝ} (hz : 0 ≤ z) (hzz : z ≤ z') (ha : 0 ≤ a) :
    f (z + a) - f z ≤ f (z' + a) - f z' := by
  rcases eq_or_lt_of_le ha with rfl | ha'
  · simp
  have h1 := hf.slope_mono (x := z) (Set.mem_Ici.2 hz)
    (show z + a ∈ Set.Ici 0 \ {z} by simp; constructor <;> linarith)
    (show z' + a ∈ Set.Ici 0 \ {z} by simp; constructor <;> linarith) (by linarith)
  have h2 := hf.slope_mono (x := z' + a) (show z' + a ∈ Set.Ici 0 by simp; linarith)
    (show z ∈ Set.Ici 0 \ {z' + a} by simp; constructor <;> linarith)
    (show z' ∈ Set.Ici 0 \ {z' + a} by simp; constructor <;> linarith) hzz
  rw [slope_comm f (z' + a) z, slope_comm f (z' + a) z'] at h2
  have h3 := h1.trans h2
  simp only [slope_def_field] at h3
  rw [show z + a - z = a by ring, show z' + a - z' = a by ring] at h3
  exact (div_le_div_iff_of_pos_right ha').1 h3

/-- **Example 18.AA.8** (MWG, p. 683). With one input (`N = 1`), convexity of `f` suffices for the
convexity of the game `v(S) = f(∑_{i∈S} ωᵢ)`. -/
theorem example_18_AA_8_one_input {f : ℝ → ℝ} (hf : ConvexOn ℝ (Set.Ici 0) f)
    {ω : Fin n → ℝ} (hω : ∀ i, 0 ≤ ω i) : IsConvexGame (prodGame f ω) := by
  classical
  intro S T hST i hiT
  have hiS : i ∉ S := fun h => hiT (hST h)
  simp only [prodGame]
  rw [Finset.sum_insert hiS, Finset.sum_insert hiT, add_comm (ω i), add_comm (ω i)]
  exact convexOn_increasing_differences hf (Finset.sum_nonneg fun j _ => hω j)
    (Finset.sum_le_sum_of_subset_of_nonneg hST fun j _ _ => hω j) (hω i)

/-- **Example 18.AA.8** (MWG, p. 683). For `N = 1` the condition `f'' ≥ 0` (on `ℝ₊`) says that `f`
is convex, hence the game is convex. -/
theorem example_18_AA_8_one_input_deriv {f : ℝ → ℝ}
    (hf' : DifferentiableOn ℝ f (Set.Ici 0)) (hf'' : DifferentiableOn ℝ (deriv f) (Set.Ici 0))
    (hpos : ∀ x ∈ Set.Ici (0 : ℝ), 0 ≤ (deriv^[2] f) x) {ω : Fin n → ℝ}
    (hω : ∀ i, 0 ≤ ω i) : IsConvexGame (prodGame f ω) :=
  example_18_AA_8_one_input (convexOn_of_deriv2_nonneg' (convex_Ici 0) hf' hf'' hpos) hω

/-- **Example 18.AA.8** (MWG, p. 683). For `N > 1` the complementarity condition is not
sufficient for convexity of `f`: `f(z) = z₁z₂` (cross partial `1`, own partials `0`) has
increasing differences but is not convex on `ℝ²₊`. -/
theorem example_18_AA_8_not_sufficient :
    IncreasingDifferences (fun z : Fin 2 → ℝ => z 0 * z 1) ∧
      ¬ ConvexOn ℝ (MWG.ConsumerChoice.nonnegOrthant 2) (fun z : Fin 2 → ℝ => z 0 * z 1) := by
  refine ⟨fun z z' a hz hzz ha => ?_, fun hc => ?_⟩
  · simp only [Pi.add_apply]
    have h0 := hzz 0
    have h1 := hzz 1
    have a0 := ha 0
    have a1 := ha 1
    nlinarith [mul_le_mul_of_nonneg_left h1 a0, mul_le_mul_of_nonneg_left h0 a1]
  · have hx : (![1, 0] : Fin 2 → ℝ) ∈ MWG.ConsumerChoice.nonnegOrthant 2 := by
      intro l; fin_cases l <;> simp
    have hy : (![0, 1] : Fin 2 → ℝ) ∈ MWG.ConsumerChoice.nonnegOrthant 2 := by
      intro l; fin_cases l <;> simp
    have := hc.2 hx hy (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)
    simp at this
    norm_num at this

/-- **Example 18.AA.8** (MWG, p. 683). For `N > 1` the complementarity condition is not necessary
for convexity of `f`: `f(z) = (z₁ - z₂)²` is convex (cross partial `-2`) but does not have
increasing differences. -/
theorem example_18_AA_8_not_necessary :
    ConvexOn ℝ Set.univ (fun z : Fin 2 → ℝ => (z 0 - z 1) ^ 2) ∧
      ¬ IncreasingDifferences (fun z : Fin 2 → ℝ => (z 0 - z 1) ^ 2) := by
  refine ⟨⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩, fun h => ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hb' : b = 1 - a := by linarith
    subst hb'
    nlinarith [sq_nonneg ((x 0 - x 1) - (y 0 - y 1)), mul_nonneg ha hb]
  · have := h 0 ![0, 1] ![1, 0] le_rfl (fun l => by fin_cases l <;> simp)
      (fun l => by fin_cases l <;> simp)
    simp at this
    norm_num at this

/-- **Exercise 18.AA.8** (MWG, p. 686). The technology `f(z) = max(z₁, z₂)` of Exercise 18.AA.8. -/
def maxTech (z : Fin 2 → ℝ) : ℝ := max (z 0) (z 1)

/-- **Exercise 18.AA.8** (MWG, p. 686). The two-player game of Exercise 18.AA.8: `ω₁ = (1, 0)`,
`ω₂ = (0, 1)`, `f = maxTech`. -/
def maxGame : WelfareBargaining.Game 2 := inputGame maxTech ![![1, 0], ![0, 1]]

/-- **Exercise 18.AA.8** (MWG, p. 686). The two-input technology `f(z) = max(z₁, z₂)` is convex
(and nondecreasing, with `f(0) = 0`), but its production game with `ω₁ = (1, 0)`, `ω₂ = (0, 1)`
has an empty core; hence (Proposition 18.AA.1) the game is not convex. -/
theorem exercise_18_AA_8 :
    ConvexOn ℝ Set.univ maxTech ∧ Monotone maxTech ∧ maxTech 0 = 0 ∧
      tuCore maxGame = ∅ ∧ ¬ IsConvexGame maxGame := by
  have hcore : tuCore maxGame = ∅ := by
    ext u
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨hS, htot⟩
    have h0 := hS {0} (by simp)
    have h1 := hS {1} (by simp)
    simp [maxGame, inputGame, maxTech, Fin.sum_univ_two] at h0 h1 htot
    linarith
  refine ⟨⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩, fun x y hxy => ?_, by simp [maxTech],
    hcore, fun hconv => ?_⟩
  · simp only [maxTech, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    refine max_le ?_ ?_
    · nlinarith [mul_le_mul_of_nonneg_left (le_max_left (x 0) (x 1)) ha,
        mul_le_mul_of_nonneg_left (le_max_left (y 0) (y 1)) hb]
    · nlinarith [mul_le_mul_of_nonneg_left (le_max_right (x 0) (x 1)) ha,
        mul_le_mul_of_nonneg_left (le_max_right (y 0) (y 1)) hb]
  · exact max_le_max (hxy 0) (hxy 1)
  · have h0 : maxGame ∅ = 0 := by simp [maxGame, inputGame, maxTech]
    have := proposition_18_AA_1 hconv h0
    rw [hcore] at this
    exact this

end MWG.CoreFoundations
