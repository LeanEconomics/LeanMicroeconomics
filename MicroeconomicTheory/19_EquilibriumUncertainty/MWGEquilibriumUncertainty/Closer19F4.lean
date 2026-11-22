/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGEquilibriumUncertainty.Closer19H6

/-!
# Exercise 19.F.4: nonexistence of Radner equilibrium with real assets (MWG p. 728)

* Real assets (returns are bundles of goods, valued at the spot prices) and the corresponding
  Radner equilibrium with unlimited short sales (`radnerFeasibleReal`, `IsRadnerEqmReal`); with
  returns in a single good this is Definition 19.E.2 (`radnerFeasibleReal_single`,
  `isRadnerEqmReal_single`).
* The maximizer of `∑ⱼ cⱼ √yⱼ` on a budget set is unique and explicit (`sqrtDemand`).
* Hart's example (`A19F4`, `U19F4`, `omega19F4`): two equally likely states, two goods, consumers
  with Bernoulli utilities `2√x₁ + √x₂` and `√x₁ + 2√x₂`, endowments `(2, 1), (0, 1)` and
  `(0, 1), (2, 1)`, and two real assets, asset `k` paying one unit of good `k` in each state.
  The Arrow-Debreu equilibrium (all prices `1`) makes the two assets' values equal
  (`exercise_19_F_4_AD`); at any Arrow-Debreu prices the relative price of good 2 is the same in
  both states (`ad19F4_det`), while at any spot-market equilibrium without transfers it differs
  (`spot19F4_det`). Hence no Radner equilibrium exists (`exercise_19_F_4`): with independent
  asset values markets are complete and the equilibrium would be Arrow-Debreu, whose prices make
  the values dependent; with dependent values the assets allow no transfer that no-arbitrage
  leaves profitable, and the spot equilibrium prices make the values independent.
-/

namespace MWG.EquilibriumUncertainty

open Matrix

/-! ## Real assets -/

/-- **Exercise 19.F.4** (MWG, p. 728): the Radner budget with real assets. Asset `k` pays the
bundle `A s k ∈ ℝ^L` in state `s`, worth `p_s·A_{sk}` at the spot prices; short sales are
unlimited. -/
def radnerFeasibleReal {S L K : ℕ} (A : Fin S → Fin K → Fin L → ℝ) (q : Fin K → ℝ)
    (p ω x : CVec S L) (z : Fin K → ℝ) : Prop :=
  NonnegC x ∧ q ⬝ᵥ z ≤ 0 ∧ ∀ s, p s ⬝ᵥ x s ≤ p s ⬝ᵥ ω s + ∑ k, (p s ⬝ᵥ A s k) * z k

/-- **Exercise 19.F.4** (MWG, p. 728): Radner equilibrium with real assets (Definition 19.E.2 with
returns valued at the spot prices). -/
def IsRadnerEqmReal {S L K : ℕ} {ι : Type*} [Fintype ι] (A : Fin S → Fin K → Fin L → ℝ)
    (U : ι → CVec S L → ℝ) (ω : ι → CVec S L) (q : Fin K → ℝ) (p : CVec S L)
    (x : ι → CVec S L) (z : ι → Fin K → ℝ) : Prop :=
  (∀ i, radnerFeasibleReal A q p (ω i) (x i) (z i) ∧
    ∀ x' z', radnerFeasibleReal A q p (ω i) x' z' → U i x' ≤ U i (x i)) ∧
    (∀ k, ∑ i, z i k ≤ 0) ∧ ∑ i, x i ≤ ∑ i, ω i

/-- Returns denominated in one good `g` are the case `A_{sk} = r_{sk} e_g`: the real-asset budget
is then the budget of Definition 19.E.2. -/
theorem radnerFeasibleReal_single {S L K : ℕ} (g : Fin L) (R : Matrix (Fin S) (Fin K) ℝ)
    (q : Fin K → ℝ) (p ω x : CVec S L) (z : Fin K → ℝ) :
    radnerFeasibleReal (fun s k => Pi.single g (R s k)) q p ω x z ↔
      radnerFeasible g R q p ω x z := by
  have h : ∀ s, ∑ k, (p s ⬝ᵥ Pi.single g (R s k)) * z k = p s g * (R *ᵥ z) s := by
    intro s
    simp only [dotProduct_single]
    simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  simp only [radnerFeasibleReal, radnerFeasible, h]

/-- With returns in one good, `IsRadnerEqmReal` is `IsRadnerEqm` (Definition 19.E.2). -/
theorem isRadnerEqmReal_single {S L K : ℕ} {ι : Type*} [Fintype ι] (g : Fin L)
    (R : Matrix (Fin S) (Fin K) ℝ) (U : ι → CVec S L → ℝ) (ω : ι → CVec S L) (q : Fin K → ℝ)
    (p : CVec S L) (x : ι → CVec S L) (z : ι → Fin K → ℝ) :
    IsRadnerEqmReal (fun s k => Pi.single g (R s k)) U ω q p x z ↔
      IsRadnerEqm g R U ω q p x z := by
  simp only [IsRadnerEqmReal, IsRadnerEqm, radnerFeasibleReal_single]

/-! ## Demand for `∑ⱼ cⱼ √yⱼ` -/

/-- The unique maximizer of `∑ⱼ cⱼ √yⱼ` on `{y ≥ 0 : ∑ⱼ Pⱼ yⱼ ≤ W}` (`c, P ≫ 0`, `W > 0`):
every maximizer satisfies `yⱼ Pⱼ² C = W cⱼ²` with `C = ∑ₖ cₖ²/Pₖ`, and spends `W`. -/
theorem sqrtDemand {n : Type*} [Fintype n] [Nonempty n] {c P y : n → ℝ} {W : ℝ}
    (hc : ∀ j, 0 < c j) (hP : ∀ j, 0 < P j) (hW : 0 < W) (hy : ∀ j, 0 ≤ y j)
    (hb : ∑ j, P j * y j ≤ W)
    (hopt : ∀ y' : n → ℝ, (∀ j, 0 ≤ y' j) → ∑ j, P j * y' j ≤ W →
      ∑ j, c j * √(y' j) ≤ ∑ j, c j * √(y j)) :
    (∀ j, y j * P j ^ 2 * (∑ k, c k ^ 2 / P k) = W * c j ^ 2) ∧ ∑ j, P j * y j = W := by
  set C := ∑ k, c k ^ 2 / P k with hCdef
  have hC : 0 < C := Finset.sum_pos (fun k _ => div_pos (pow_pos (hc k) 2) (hP k))
    Finset.univ_nonempty
  have hsC := Real.sqrt_pos.mpr hC
  have hsW := Real.sqrt_pos.mpr hW
  have hC2 := Real.sq_sqrt hC.le
  have hW2 := Real.sq_sqrt hW.le
  -- the candidate
  set ys : n → ℝ := fun j => (√W * c j / (√C * P j)) ^ 2 with hys
  have hys_sqrt : ∀ j, √(ys j) = √W * c j / (√C * P j) := fun j =>
    Real.sqrt_sq (div_nonneg (mul_nonneg hsW.le (hc j).le) (mul_nonneg hsC.le (hP j).le))
  have hys_budget : ∑ j, P j * ys j = W := by
    have : ∀ j, P j * ys j = W / C * (c j ^ 2 / P j) := by
      intro j
      simp only [hys]
      have := hP j
      field_simp
      rw [hC2, hW2]
      ring
    rw [Finset.sum_congr rfl fun j _ => this j, ← Finset.mul_sum, ← hCdef]
    field_simp
  have hys_val : ∑ j, c j * √(ys j) = √W * √C := by
    have : ∀ j, c j * √(ys j) = √W / √C * (c j ^ 2 / P j) := by
      intro j
      rw [hys_sqrt]
      have := hP j
      field_simp
    rw [Finset.sum_congr rfl fun j _ => this j, ← Finset.mul_sum, ← hCdef]
    field_simp
    rw [hC2]
  have hlow : √W * √C ≤ ∑ j, c j * √(y j) := by
    rw [← hys_val]
    refine hopt ys (fun j => sq_nonneg _) hys_budget.le
  -- the gaps
  set θ := √C / (2 * √W) with hθ
  have hθpos : 0 < θ := by positivity
  have gap : ∀ j, θ * P j * (√(y j) - c j / (2 * θ * P j)) ^ 2 =
      θ * (P j * y j) - c j * √(y j) + c j ^ 2 / P j / (4 * θ) := by
    intro j
    have := hP j
    have hsq := Real.sq_sqrt (hy j)
    field_simp
    linear_combination 16 * θ ^ 2 * P j ^ 2 * hsq
  have hsum : ∑ j, θ * P j * (√(y j) - c j / (2 * θ * P j)) ^ 2 =
      θ * ∑ j, P j * y j - ∑ j, c j * √(y j) + C / (4 * θ) := by
    rw [Finset.sum_congr rfl fun j _ => gap j, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, hCdef, Finset.sum_div]
  have hCθ : C / (4 * θ) = √W * √C / 2 := by
    rw [hθ]
    field_simp
    rw [hC2]
    ring
  have hθW : θ * W = √W * √C / 2 := by
    rw [hθ]
    field_simp
    rw [hW2]
  have hnn : ∀ j, 0 ≤ θ * P j * (√(y j) - c j / (2 * θ * P j)) ^ 2 := fun j =>
    mul_nonneg (mul_nonneg hθpos.le (hP j).le) (sq_nonneg _)
  have hle0 : ∑ j, θ * P j * (√(y j) - c j / (2 * θ * P j)) ^ 2 ≤ 0 := by
    rw [hsum, hCθ]
    nlinarith [mul_le_mul_of_nonneg_left hb hθpos.le]
  have hzero : ∀ j, θ * P j * (√(y j) - c j / (2 * θ * P j)) ^ 2 = 0 := by
    intro j
    have h0 := Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnn j) |>.mp
      (le_antisymm hle0 (Finset.sum_nonneg fun j _ => hnn j))
    exact h0 j (Finset.mem_univ j)
  refine ⟨fun j => ?_, ?_⟩
  · have hj := hzero j
    have hPj := hP j
    have hsq0 : √(y j) - c j / (2 * θ * P j) = 0 := by
      rcases mul_eq_zero.mp hj with h | h
      · exact absurd h (by positivity)
      · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
    have hrt : √(y j) = c j / (2 * θ * P j) := by linarith
    have hyj : y j = (c j / (2 * θ * P j)) ^ 2 := by
      rw [← hrt, Real.sq_sqrt (hy j)]
    rw [hyj, hθ]
    field_simp
    rw [hC2, hW2]
    ring
  · have := Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => hnn j
    rw [hsum, hCθ] at this
    nlinarith [mul_le_mul_of_nonneg_left hb hθpos.le]

/-! ## The economy -/

/-- Exercise 19.F.4: two real assets; asset `k` pays one unit of good `k` in every state. -/
def A19F4 : Fin 2 → Fin 2 → Fin 2 → ℝ := fun _ k => Pi.single k 1

/-- Exercise 19.F.4: expected-utility coefficients, two equally likely states: consumer 1 has
Bernoulli utility `2√x₁ + √x₂`, consumer 2 has `√x₁ + 2√x₂` (times the probability `1/2`). -/
noncomputable def c19F4 : Fin 2 → Fin 2 → ℝ := ![![1, 1 / 2], ![1 / 2, 1]]

/-- Exercise 19.F.4: `Uᵢ(x) = ∑_s ∑_l c_{il} √x_{sl}`. -/
noncomputable def U19F4 (i : Fin 2) (x : CVec 2 2) : ℝ := ∑ s, ∑ l, c19F4 i l * √(x s l)

/-- Exercise 19.F.4: endowments. Both consumers own one unit of good 2 in each state; consumer 1
owns two units of good 1 in state 1, consumer 2 two units in state 2. The aggregate endowment is
`(2, 2)` in both states. -/
def omega19F4 : Fin 2 → CVec 2 2 := ![![![2, 1], ![0, 1]], ![![0, 1], ![2, 1]]]

theorem c19F4_pos (i l : Fin 2) : 0 < c19F4 i l := by
  fin_cases i <;> fin_cases l <;> norm_num [c19F4]

theorem ret19F4 (p : CVec 2 2) (s : Fin 2) (z : Fin 2 → ℝ) :
    ∑ k, (p s ⬝ᵥ A19F4 s k) * z k = p s 0 * z 0 + p s 1 * z 1 := by
  simp [A19F4, dotProduct_single, Fin.sum_univ_two]

/-- **Exercise 19.F.4**, the complete-markets benchmark: with all contingent prices `1`, each
consumer consuming his preferred good `8/5` and the other `2/5` in every state is an
Arrow-Debreu equilibrium. At these prices the two real assets have the same value `(1, 1)`:
the return matrix `(p_s·A_{sk})` has rank `1`. -/
theorem exercise_19_F_4_AD :
    IsADEqmU U19F4 omega19F4 ![fun _ => ![8 / 5, 2 / 5], fun _ => ![2 / 5, 8 / 5]]
      (fun _ _ => 1) ∧ ∀ s k, (fun _ _ => (1 : ℝ)) s ⬝ᵥ A19F4 s k = 1 := by
  refine ⟨?_, fun s k => by simp [A19F4, dotProduct_single]⟩
  set r := √(2 / 5 : ℝ) with hrdef
  have hr0 : 0 < r := Real.sqrt_pos.mpr (by norm_num)
  have hr2 : r ^ 2 = 2 / 5 := Real.sq_sqrt (by norm_num)
  have h8 : √(8 / 5 : ℝ) = 2 * r := by
    rw [show (8 / 5 : ℝ) = (2 * r) ^ 2 by rw [mul_pow, hr2]; norm_num]
    exact Real.sqrt_sq (by positivity)
  have bound : ∀ (a y : ℝ), 0 ≤ y → a * √y ≤ y / (4 * r) + a ^ 2 * r := by
    intro a y hy
    have h1 := sq_nonneg (√y - 2 * a * r)
    have h2 := Real.sq_sqrt hy
    rw [div_add' _ _ _ (by positivity), le_div_iff₀ (by positivity)]
    nlinarith
  have hr' : √(2 : ℝ) / √5 = r := by rw [hrdef, Real.sqrt_div (by norm_num)]
  have hinv : 1 / r = 5 * r / 2 := by
    field_simp
    nlinarith
  refine ⟨fun i => ⟨⟨fun s l => ?_, ?_⟩, fun x' hx' hb => ?_⟩, ?_⟩
  · fin_cases i <;> fin_cases l <;> norm_num
  · fin_cases i <;> norm_num [cval, omega19F4, dotProduct, Fin.sum_univ_two]
  · have hb' : x' 0 0 + x' 0 1 + (x' 1 0 + x' 1 1) ≤ 4 := by
      fin_cases i <;> norm_num [cval, omega19F4, dotProduct, Fin.sum_univ_two] at hb <;>
        linarith
    have b00 := bound (c19F4 i 0) (x' 0 0) (hx' 0 0)
    have b01 := bound (c19F4 i 1) (x' 0 1) (hx' 0 1)
    have b10 := bound (c19F4 i 0) (x' 1 0) (hx' 1 0)
    have b11 := bound (c19F4 i 1) (x' 1 1) (hx' 1 1)
    have hsum : x' 0 0 / (4 * r) + x' 0 1 / (4 * r) + (x' 1 0 / (4 * r) + x' 1 1 / (4 * r)) ≤
        1 / r := by
      rw [show x' 0 0 / (4 * r) + x' 0 1 / (4 * r) + (x' 1 0 / (4 * r) + x' 1 1 / (4 * r)) =
        (x' 0 0 + x' 0 1 + (x' 1 0 + x' 1 1)) / (4 * r) by ring, div_le_div_iff₀ (by positivity)
        hr0]
      nlinarith
    fin_cases i <;>
    · simp only [c19F4, one_div, Fin.zero_eta, Fin.isValue, cons_val', cons_val_zero,
        cons_val_fin_one, one_mul, one_pow, cons_val_one, inv_pow, U19F4, Fin.sum_univ_two,
        Nat.succ_eq_add_one, Nat.reduceAdd, h8, Nat.ofNat_nonneg, Real.sqrt_div, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, smul_add, nsmul_eq_mul, Nat.cast_ofNat, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, mul_inv_cancel_left₀, ge_iff_le, Fin.mk_one]
        at b00 b01 b10 b11 ⊢
      rw [hr']
      linarith
  · funext s l
    fin_cases s <;> fin_cases l <;> simp [omega19F4, Fin.sum_univ_two] <;> norm_num

/-- **Exercise 19.F.4**, complete markets: at any Arrow-Debreu prices `Π ≫ 0` (optimal demands,
`∑ᵢ xᵢ ≤ ∑ᵢ ωᵢ`), good 2's relative price is the same in both states, `Π₁₁Π₂₂ = Π₁₂Π₂₁`.
So at the Arrow-Debreu spot prices the two real assets have proportional values: the return
matrix drops rank. -/
theorem ad19F4_det {Pr : CVec 2 2} (hP : ∀ s l, 0 < Pr s l) {x : Fin 2 → CVec 2 2}
    (hx : ∀ i, NonnegC (x i) ∧ cval Pr (x i) ≤ cval Pr (omega19F4 i))
    (hopt : ∀ i x', NonnegC x' → cval Pr x' ≤ cval Pr (omega19F4 i) →
      U19F4 i x' ≤ U19F4 i (x i))
    (hcl : ∑ i, x i ≤ ∑ i, omega19F4 i) :
    Pr 0 0 * Pr 1 1 = Pr 0 1 * Pr 1 0 := by
  have hcv : ∀ y : CVec 2 2, cval Pr y = ∑ j : Fin 2 × Fin 2, Pr j.1 j.2 * y j.1 j.2 := by
    intro y; simp [cval, dotProduct, Fintype.sum_prod_type]
  have hU : ∀ i y, U19F4 i y = ∑ j : Fin 2 × Fin 2, c19F4 i j.2 * √(y j.1 j.2) := by
    intro i y; simp [U19F4, Fintype.sum_prod_type]
  have hW : ∀ i, 0 < cval Pr (omega19F4 i) := by
    intro i
    have := hP 0 0; have := hP 0 1; have := hP 1 0; have := hP 1 1
    fin_cases i <;> simp [cval, omega19F4, dotProduct, Fin.sum_univ_two] <;> linarith
  have hd : ∀ i, (∀ j : Fin 2 × Fin 2, x i j.1 j.2 * Pr j.1 j.2 ^ 2 *
      (∑ k : Fin 2 × Fin 2, c19F4 i k.2 ^ 2 / Pr k.1 k.2) = cval Pr (omega19F4 i) *
        c19F4 i j.2 ^ 2) ∧
      ∑ j : Fin 2 × Fin 2, Pr j.1 j.2 * x i j.1 j.2 = cval Pr (omega19F4 i) := by
    intro i
    refine sqrtDemand (c := fun j : Fin 2 × Fin 2 => c19F4 i j.2)
      (P := fun j : Fin 2 × Fin 2 => Pr j.1 j.2) (y := fun j : Fin 2 × Fin 2 => x i j.1 j.2)
      (fun j => c19F4_pos _ _) (fun j => hP _ _) (hW i)
      (fun j => (hx i).1 _ _) (by rw [← hcv]; exact (hx i).2) fun y' hy' hb' => ?_
    have := hopt i (fun s l => y' (s, l)) (fun s l => hy' _) (by simpa [hcv] using hb')
    simpa [hU] using this
  have hC : ∀ i, 0 < ∑ k : Fin 2 × Fin 2, c19F4 i k.2 ^ 2 / Pr k.1 k.2 := fun i =>
    Finset.sum_pos (fun k _ => div_pos (pow_pos (c19F4_pos _ _) 2) (hP _ _))
      Finset.univ_nonempty
  -- market clearing holds with equality
  have hcl' : ∀ s l, x 0 s l + x 1 s l ≤ omega19F4 0 s l + omega19F4 1 s l := by
    intro s l; simpa [Fin.sum_univ_two] using hcl s l
  have hb0 := (hd 0).2
  have hb1 := (hd 1).2
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two] at hb0 hb1
  simp only [cval, dotProduct, Fin.sum_univ_two] at hb0 hb1
  have m00 := mul_nonpos_of_nonneg_of_nonpos (hP 0 0).le (sub_nonpos.mpr (hcl' 0 0))
  have m01 := mul_nonpos_of_nonneg_of_nonpos (hP 0 1).le (sub_nonpos.mpr (hcl' 0 1))
  have m10 := mul_nonpos_of_nonneg_of_nonpos (hP 1 0).le (sub_nonpos.mpr (hcl' 1 0))
  have m11 := mul_nonpos_of_nonneg_of_nonpos (hP 1 1).le (sub_nonpos.mpr (hcl' 1 1))
  have z00 : Pr 0 0 * (x 0 0 0 + x 1 0 0 - (omega19F4 0 0 0 + omega19F4 1 0 0)) = 0 := by
    linarith
  have z01 : Pr 0 1 * (x 0 0 1 + x 1 0 1 - (omega19F4 0 0 1 + omega19F4 1 0 1)) = 0 := by
    linarith
  have z10 : Pr 1 0 * (x 0 1 0 + x 1 1 0 - (omega19F4 0 1 0 + omega19F4 1 1 0)) = 0 := by
    linarith
  have z11 : Pr 1 1 * (x 0 1 1 + x 1 1 1 - (omega19F4 0 1 1 + omega19F4 1 1 1)) = 0 := by
    linarith
  have e00 : x 0 0 0 + x 1 0 0 = 2 := by
    have := (mul_eq_zero.mp z00).resolve_left (hP 0 0).ne'
    simp [omega19F4] at this; linarith
  have e01 : x 0 0 1 + x 1 0 1 = 2 := by
    have := (mul_eq_zero.mp z01).resolve_left (hP 0 1).ne'
    simp [omega19F4] at this; norm_num at this; linarith
  have e10 : x 0 1 0 + x 1 1 0 = 2 := by
    have := (mul_eq_zero.mp z10).resolve_left (hP 1 0).ne'
    simp [omega19F4] at this; linarith
  have e11 : x 0 1 1 + x 1 1 1 = 2 := by
    have := (mul_eq_zero.mp z11).resolve_left (hP 1 1).ne'
    simp [omega19F4] at this; norm_num at this; linarith
  -- the demands: `x_{isl} Π_{sl}²` does not depend on `s`
  have st : ∀ i l, x i 0 l * Pr 0 l ^ 2 = x i 1 l * Pr 1 l ^ 2 := by
    intro i l
    have h0 := (hd i).1 (0, l)
    have h1 := (hd i).1 (1, l)
    have : (x i 0 l * Pr 0 l ^ 2) * (∑ k : Fin 2 × Fin 2, c19F4 i k.2 ^ 2 / Pr k.1 k.2) =
        (x i 1 l * Pr 1 l ^ 2) * (∑ k : Fin 2 × Fin 2, c19F4 i k.2 ^ 2 / Pr k.1 k.2) := by
      simp only at h0 h1; rw [h0, h1]
    exact mul_right_cancel₀ (hC i).ne' this
  have sq0 : Pr 0 0 ^ 2 = Pr 1 0 ^ 2 := by
    have := st 0 0; have := st 1 0
    nlinarith
  have sq1 : Pr 0 1 ^ 2 = Pr 1 1 ^ 2 := by
    have := st 0 1; have := st 1 1
    nlinarith
  have q0 : Pr 0 0 = Pr 1 0 := (pow_left_inj₀ (hP 0 0).le (hP 1 0).le two_ne_zero).mp sq0
  have q1 : Pr 0 1 = Pr 1 1 := (pow_left_inj₀ (hP 0 1).le (hP 1 1).le two_ne_zero).mp sq1
  rw [q0, q1, mul_comm]

/-- **Exercise 19.F.4**, spot markets only: at any spot prices `p ≫ 0` with optimal spot
demands in every state and `∑ᵢ xᵢ ≤ ∑ᵢ ωᵢ`, good 2's relative price differs between the
states, `p₁₁p₂₂ ≠ p₁₂p₂₁`: the asset values are linearly independent. -/
theorem spot19F4_det {p : CVec 2 2} (hp : ∀ s l, 0 < p s l) {x : Fin 2 → CVec 2 2}
    (hx : ∀ i s, (∀ l, 0 ≤ x i s l) ∧ p s ⬝ᵥ x i s ≤ p s ⬝ᵥ omega19F4 i s)
    (hopt : ∀ i s (y : Fin 2 → ℝ), (∀ l, 0 ≤ y l) → p s ⬝ᵥ y ≤ p s ⬝ᵥ omega19F4 i s →
      ∑ l, c19F4 i l * √(y l) ≤ ∑ l, c19F4 i l * √(x i s l))
    (hcl : ∑ i, x i ≤ ∑ i, omega19F4 i) :
    p 0 0 * p 1 1 ≠ p 0 1 * p 1 0 := by
  intro hdet
  have hW : ∀ i s, 0 < p s ⬝ᵥ omega19F4 i s := by
    intro i s
    fin_cases i <;> fin_cases s <;> simp [omega19F4, dotProduct, Fin.sum_univ_two] <;>
      linarith [hp 0 0, hp 0 1, hp 1 0, hp 1 1]
  have hd : ∀ i s, (∀ l, x i s l * p s l ^ 2 * (∑ k, c19F4 i k ^ 2 / p s k) =
      p s ⬝ᵥ omega19F4 i s * c19F4 i l ^ 2) ∧ ∑ l, p s l * x i s l = p s ⬝ᵥ omega19F4 i s :=
    fun i s => sqrtDemand (fun l => c19F4_pos i l) (fun l => hp s l) (hW i s) (hx i s).1
      (hx i s).2 (hopt i s)
  have hcl' : ∀ s l, x 0 s l + x 1 s l ≤ omega19F4 0 s l + omega19F4 1 s l := by
    intro s l; simpa [Fin.sum_univ_two] using hcl s l
  have eq0 : ∀ s, x 0 s 0 + x 1 s 0 = omega19F4 0 s 0 + omega19F4 1 s 0 := by
    intro s
    have b0 := (hd 0 s).2
    have b1 := (hd 1 s).2
    simp only [dotProduct, Fin.sum_univ_two] at b0 b1
    have m0 := mul_nonpos_of_nonneg_of_nonpos (hp s 0).le (sub_nonpos.mpr (hcl' s 0))
    have m1 := mul_nonpos_of_nonneg_of_nonpos (hp s 1).le (sub_nonpos.mpr (hcl' s 1))
    have z0 : p s 0 * (x 0 s 0 + x 1 s 0 - (omega19F4 0 s 0 + omega19F4 1 s 0)) = 0 := by
      linarith
    have := (mul_eq_zero.mp z0).resolve_left (hp s 0).ne'
    linarith
  have f1 := (hd 0 0).1 0
  have f2 := (hd 1 0).1 0
  have f3 := (hd 0 1).1 0
  have f4 := (hd 1 1).1 0
  have c0 := eq0 0
  have c1 := eq0 1
  simp only [Fin.isValue, c19F4, one_div, cons_val', cons_val_fin_one, cons_val_zero,
      Fin.sum_univ_two, one_pow, cons_val_one, inv_pow, dotProduct, omega19F4, mul_one, mul_zero,
      zero_add, add_zero] at f1 f2 f3 f4 c0 c1
  set P := p 0 1 / p 0 0 with hPdef
  have hu := hp 0 0
  have hu' := hp 1 0
  have hPpos : 0 < P := div_pos (hp 0 1) hu
  have hv : p 0 1 = P * p 0 0 := by rw [hPdef]; field_simp
  have hv' : p 1 1 = P * p 1 0 := by
    rw [hPdef]; field_simp; linarith
  rw [hv] at f1 f2
  rw [hv'] at f3 f4
  field_simp at f1 f2 f3 f4
  have h30 : 30 * P = 0 := by
    linear_combination (-(P + 4)) * f1 + (P + 4) * f3 - (4 * P + 1) * f2 + (4 * P + 1) * f4 +
      (P + 4) * (4 * P + 1) * c0 - (P + 4) * (4 * P + 1) * c1
  linarith

theorem U19F4_lt_bump (i : Fin 2) {x : CVec 2 2} (hx : NonnegC x) (s l : Fin 2) {δ : ℝ}
    (hδ : 0 < δ) : U19F4 i x < U19F4 i (x + δ • contingentUnit l s) := by
  have hu : ∀ s' l', 0 ≤ (δ • contingentUnit l s) s' l' := by
    intro s' l'
    simp only [Pi.smul_apply, smul_eq_mul, contingentUnit]
    split_ifs <;> simp [hδ.le]
  unfold U19F4
  refine Finset.sum_lt_sum (fun s' _ => Finset.sum_le_sum fun l' _ => ?_)
    ⟨s, Finset.mem_univ _, Finset.sum_lt_sum (fun l' _ => ?_) ⟨l, Finset.mem_univ _, ?_⟩⟩
  · refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (c19F4_pos i l').le
    simp only [Pi.add_apply]; linarith [hu s' l']
  · refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (c19F4_pos i l').le
    simp only [Pi.add_apply]; linarith [hu s l']
  · refine mul_lt_mul_of_pos_left (Real.sqrt_lt_sqrt (hx s l) ?_) (c19F4_pos i l)
    simp [contingentUnit, hδ]

theorem dot_bump19F4 (p x : CVec 2 2) (s l s' : Fin 2) (δ : ℝ) :
    p s' ⬝ᵥ (x + δ • contingentUnit l s) s' =
      p s' ⬝ᵥ x s' + if s' = s then p s l * δ else 0 := by
  fin_cases s <;> fin_cases l <;> fin_cases s' <;>
    simp [contingentUnit, dotProduct, Fin.sum_univ_two] <;> ring

/-- **Exercise 19.F.4** (MWG, p. 728). With unlimited short sales and returns denominated in more
than one good, a Radner equilibrium may fail to exist: in the economy `omega19F4`, `U19F4`
(strictly increasing, strictly concave in each good) with the two real assets `A19F4` (asset `k`
pays one unit of good `k` in each state), there is no Radner equilibrium. If the asset values
`(p_{sk})` are linearly independent, the structure is complete, so the equilibrium is an
Arrow-Debreu equilibrium (no-arbitrage gives state prices `ν ≫ 0`) and its spot prices make the
values dependent (`ad19F4_det`); if they are dependent, the assets only transfer wealth along
`(p₁₁, p₂₁)` and no-arbitrage leaves only the spot budgets, whose equilibria make the values
independent (`spot19F4_det`). -/
theorem exercise_19_F_4 :
    ¬ ∃ (q : Fin 2 → ℝ) (p : CVec 2 2) (x : Fin 2 → CVec 2 2) (z : Fin 2 → Fin 2 → ℝ),
      IsRadnerEqmReal A19F4 U19F4 omega19F4 q p x z := by
  rintro ⟨q, p, x, z, hopt, -, hcl⟩
  have hfe : ∀ i, NonnegC (x i) ∧ q ⬝ᵥ z i ≤ 0 ∧ ∀ s, p s ⬝ᵥ x i s ≤
      p s ⬝ᵥ omega19F4 i s + (p s 0 * z i 0 + p s 1 * z i 1) := by
    intro i
    obtain ⟨⟨h1, h2, h3⟩, -⟩ := hopt i
    exact ⟨h1, h2, fun s => by rw [← ret19F4]; exact h3 s⟩
  have hbest : ∀ i x' (z' : Fin 2 → ℝ), NonnegC x' → q ⬝ᵥ z' ≤ 0 →
      (∀ s, p s ⬝ᵥ x' s ≤ p s ⬝ᵥ omega19F4 i s + (p s 0 * z' 0 + p s 1 * z' 1)) →
      U19F4 i x' ≤ U19F4 i (x i) := fun i x' z' h1 h2 h3 =>
    (hopt i).2 x' z' ⟨h1, h2, fun s => by rw [ret19F4]; exact h3 s⟩
  -- consumer 1 cannot gain `δ` of good `l` in state `s` with an extra portfolio `z'`
  have nodev : ∀ (s l : Fin 2) (δ : ℝ) (z' : Fin 2 → ℝ), 0 < δ → q ⬝ᵥ (z 0 + z') ≤ 0 →
      (∀ s', (if s' = s then p s l * δ else 0) ≤ p s' 0 * z' 0 + p s' 1 * z' 1) → False := by
    intro s l δ z' hδ hq hs
    have hnn : NonnegC (x 0 + δ • contingentUnit l s) := by
      intro s' l'
      have h1 := (hfe 0).1 s' l'
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, contingentUnit]
      split_ifs <;> simp <;> linarith
    have := hbest 0 (x 0 + δ • contingentUnit l s) (z 0 + z') hnn hq fun s' => by
      rw [dot_bump19F4]
      have h1 := (hfe 0).2.2 s'
      have h2 := hs s'
      simp only [Pi.add_apply]
      linarith
    exact absurd this (not_le.mpr (U19F4_lt_bump 0 (hfe 0).1 s l hδ))
  have hp : ∀ s l, 0 < p s l := by
    intro s l
    by_contra h
    push Not at h
    refine nodev s l 1 0 one_pos (by simpa using (hfe 0).2.1) fun s' => ?_
    split_ifs <;> simp [h]
  by_cases hdet : p 0 0 * p 1 1 = p 0 1 * p 1 0
  · -- the asset values are dependent
    set P := p 0 1 / p 0 0 with hPdef
    have hu := hp 0 0
    have hv : p 0 1 = P * p 0 0 := by rw [hPdef]; field_simp
    have hv' : p 1 1 = P * p 1 0 := by
      rw [hPdef]; field_simp; linarith
    have hc : ∀ z' : Fin 2 → ℝ, q ⬝ᵥ z' ≤ 0 → z' 0 + P * z' 1 ≤ 0 := by
      intro z' hq'
      by_contra h
      push Not at h
      refine nodev 0 0 (z' 0 + P * z' 1) z' h
        (by rw [dotProduct_add]; linarith [(hfe 0).2.1]) fun s' => ?_
      fin_cases s'
      · simp only [Fin.zero_eta, Fin.isValue, ↓reduceIte]
        rw [hv]; nlinarith
      · simp only [Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte]
        rw [hv']; nlinarith [hp 1 0]
    have hsp : ∀ i s, p s ⬝ᵥ x i s ≤ p s ⬝ᵥ omega19F4 i s := by
      intro i s
      have h1 := (hfe i).2.2 s
      have h2 := hc (z i) (hfe i).2.1
      fin_cases s
      · simp only [Fin.zero_eta, Fin.isValue] at h1 ⊢
        rw [hv] at h1; nlinarith
      · simp only [Fin.mk_one, Fin.isValue] at h1 ⊢
        rw [hv'] at h1; nlinarith [hp 1 0]
    refine spot19F4_det hp (fun i s => ⟨fun l => (hfe i).1 s l, hsp i s⟩)
      (fun i s y hy hb => ?_) hcl hdet
    have hnn : NonnegC (Function.update (x i) s y) := by
      intro s' l
      by_cases h : s' = s
      · subst h; simp [hy l]
      · simp [h, (hfe i).1 s' l]
    have := hbest i (Function.update (x i) s y) 0 hnn (by simp) fun s' => by
      by_cases h : s' = s
      · subst h; rw [Function.update_self]; simpa using hb
      · rw [Function.update_of_ne h]; simpa using hsp i s'
    unfold U19F4 at this
    fin_cases s <;> simp [Function.update, Fin.sum_univ_two] at this ⊢ <;> linarith
  · -- the asset values are independent: complete markets
    set D := p 0 0 * p 1 1 - p 0 1 * p 1 0 with hD
    have hD0 : D ≠ 0 := sub_ne_zero.mpr hdet
    set ν0 := (p 1 1 * q 0 - p 1 0 * q 1) / D with hν0
    set ν1 := (p 0 0 * q 1 - p 0 1 * q 0) / D with hν1
    have solve : ∀ m0 m1 : ℝ, ∃ z' : Fin 2 → ℝ, p 0 0 * z' 0 + p 0 1 * z' 1 = m0 ∧
        p 1 0 * z' 0 + p 1 1 * z' 1 = m1 := by
      intro m0 m1
      refine ⟨![(p 1 1 * m0 - p 0 1 * m1) / D, (p 0 0 * m1 - p 1 0 * m0) / D], ?_, ?_⟩ <;>
      · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        field_simp
        rw [hD]
        ring
    have hq : ∀ z' : Fin 2 → ℝ, q ⬝ᵥ z' =
        ν0 * (p 0 0 * z' 0 + p 0 1 * z' 1) + ν1 * (p 1 0 * z' 0 + p 1 1 * z' 1) := by
      intro z'
      simp only [dotProduct, Fin.sum_univ_two, hν0, hν1]
      field_simp
      rw [hD]
      ring
    have hpos0 : 0 < ν0 := by
      by_contra h
      push Not at h
      obtain ⟨z', h0, h1⟩ := solve (p 0 0) 0
      refine nodev 0 0 1 z' one_pos ?_ fun s' => ?_
      · rw [dotProduct_add, hq z', h0, h1]
        nlinarith [(hfe 0).2.1, hp 0 0]
      · fin_cases s' <;> simp [h0, h1]
    have hpos1 : 0 < ν1 := by
      by_contra h
      push Not at h
      obtain ⟨z', h0, h1⟩ := solve 0 (p 1 0)
      refine nodev 1 0 1 z' one_pos ?_ fun s' => ?_
      · rw [dotProduct_add, hq z', h0, h1]
        nlinarith [(hfe 0).2.1, hp 1 0]
      · fin_cases s' <;> simp [h0, h1]
    set Pr : CVec 2 2 := fun s l => ![ν0, ν1] s * p s l with hPr
    have hcv : ∀ y : CVec 2 2, cval Pr y = ν0 * (p 0 ⬝ᵥ y 0) + ν1 * (p 1 ⬝ᵥ y 1) := by
      intro y
      simp [hPr, cval, dotProduct, Fin.sum_univ_two]
      ring
    have hPpos : ∀ s l, 0 < Pr s l := by
      intro s l
      fin_cases s
      · exact mul_pos hpos0 (hp 0 l)
      · exact mul_pos hpos1 (hp 1 l)
    have key := ad19F4_det hPpos (x := x) (fun i => ⟨(hfe i).1, ?_⟩) (fun i x' hx' hb => ?_) hcl
    · have : ν0 * ν1 * D = 0 := by
        simp only [hPr, Matrix.cons_val_zero, Matrix.cons_val_one] at key
        rw [hD]
        linear_combination key
      rcases mul_eq_zero.mp this with h | h
      · exact (mul_pos hpos0 hpos1).ne' h
      · exact hD0 h
    · rw [hcv, hcv]
      have h0 := mul_le_mul_of_nonneg_left ((hfe i).2.2 0) hpos0.le
      have h1 := mul_le_mul_of_nonneg_left ((hfe i).2.2 1) hpos1.le
      have h2 := (hfe i).2.1
      rw [hq] at h2
      nlinarith
    · obtain ⟨z', h0, h1⟩ := solve (p 0 ⬝ᵥ x' 0 - p 0 ⬝ᵥ omega19F4 i 0)
        (p 1 ⬝ᵥ x' 1 - p 1 ⬝ᵥ omega19F4 i 1)
      refine hbest i x' z' hx' ?_ fun s => ?_
      · rw [hq, h0, h1]
        rw [hcv, hcv] at hb
        linarith
      · fin_cases s
        · simp only [Fin.zero_eta, Fin.isValue]; rw [h0]; linarith
        · simp only [Fin.mk_one, Fin.isValue]; rw [h1]; linarith

end MWG.EquilibriumUncertainty
