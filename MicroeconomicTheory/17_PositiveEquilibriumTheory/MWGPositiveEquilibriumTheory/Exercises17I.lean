/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPositiveEquilibriumTheory.LargeEconomies

/-!
# Exercises 17.I.1 and 17.I.2 (MWG, p. 649)

* **Exercise 17.I.1**: unequal numbers of consumers per type. `typeEconomy E k` has `kᵢ`
  consumers of type `i`. The economy with `kᵢr` consumers of type `i` has the same equilibrium
  price set as the `r`-replica of `typeEconomy E k` (`exercise_17_I_1`; relabelling consumers
  does not change equilibrium prices, `eqmPriceSet_eq_of_equiv`), and rational proportions
  `qᵢ` are proportions `kᵢ/∑ⱼkⱼ` of integers (`exercise_17_I_1_rational`): redefining the size
  of the original economy to `kᵢ` consumers of type `i`, the replica procedure covers it.
* **Exercise 17.I.2**: `q = v²`, `Y = {(-v, q) : v ≥ 0, q ≤ v²}` (`ex17I2Y`). `Y` is additive
  (`exercise_17_I_2_additive`); the smallest cone containing `Y` (`ex17I2Cone`, characterized by
  `ex17I2Cone_eq`, minimal by `ex17I2Cone_minimal`) is not closed
  (`exercise_17_I_2_not_closed`). The nonconvexity is large: `conv Y` is that cone
  (`ex17I2_convexHull_eq`) and contains points at any distance from `Y`
  (`exercise_17_I_2_large`). Profits are unbounded at every price with a positive output price,
  whatever the number of consumers (`exercise_17_I_2_profit_unbounded`).
-/

namespace MWG.PositiveEquilibriumTheory

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.GeneralEquilibriumExamples

variable {ι : Type*} {L : ℕ}

/-! ### Exercise 17.I.1 -/

/-- **Exercise 17.I.1** (MWG, p. 649). The economy with `kᵢ` consumers of type `i`. -/
def typeEconomy (E : ExchangeEconomy ι L) (k : ι → ℕ) : ExchangeEconomy (Σ i, Fin (k i)) L where
  X c := E.X c.1
  u c := E.u c.1
  ω c := E.ω c.1

/-- Relabelling consumers does not change the equilibrium price set (one inclusion). -/
theorem eqmPriceSet_subset_of_equiv {κ κ' : Type*} [Fintype κ] [Fintype κ']
    (E : ExchangeEconomy κ L) (E' : ExchangeEconomy κ' L) (e : κ ≃ κ')
    (hX : ∀ c, E'.X (e c) = E.X c) (hu : ∀ c, E'.u (e c) = E.u c)
    (hω : ∀ c, E'.ω (e c) = E.ω c) : eqmPriceSet E ⊆ eqmPriceSet E' := by
  rintro p ⟨x, ⟨hx, hsum⟩, hd⟩
  have hdem : ∀ c, E'.demand (e c) p = E.demand c p := fun c => by
    simp only [ExchangeEconomy.demand, hX, hu, hω]
  refine ⟨fun c' => x (e.symm c'), ⟨fun c' => ?_, ?_⟩, fun c' => ?_⟩
  · have := hx (e.symm c')
    rwa [← hX, e.apply_symm_apply] at this
  · rw [Equiv.sum_comp e.symm x, hsum]
    simp only [ExchangeEconomy.totalEndowment]
    rw [← Equiv.sum_comp e (fun c' => E'.ω c')]
    exact Finset.sum_congr rfl fun c _ => (hω c).symm
  · have := hd (e.symm c')
    rwa [← hdem, e.apply_symm_apply] at this

/-- Relabelling consumers does not change the equilibrium price set. -/
theorem eqmPriceSet_eq_of_equiv {κ κ' : Type*} [Fintype κ] [Fintype κ']
    (E : ExchangeEconomy κ L) (E' : ExchangeEconomy κ' L) (e : κ ≃ κ')
    (hX : ∀ c, E'.X (e c) = E.X c) (hu : ∀ c, E'.u (e c) = E.u c)
    (hω : ∀ c, E'.ω (e c) = E.ω c) : eqmPriceSet E = eqmPriceSet E' := by
  refine (eqmPriceSet_subset_of_equiv E E' e hX hu hω).antisymm
    (eqmPriceSet_subset_of_equiv E' E e.symm (fun c => ?_) (fun c => ?_) fun c => ?_)
  · rw [← hX, e.apply_symm_apply]
  · rw [← hu, e.apply_symm_apply]
  · rw [← hω, e.apply_symm_apply]

/-- **Exercise 17.I.1** (MWG, p. 649). The economy with `kᵢr` consumers of type `i` has the
same equilibrium price vectors as the `r`-replica of the economy with `kᵢ` consumers of type
`i`: with the size of the original economy redefined, the replica procedure covers unequal
numbers of consumers per type. -/
theorem exercise_17_I_1 [Fintype ι] (E : ExchangeEconomy ι L) (k : ι → ℕ) (r : ℕ) :
    eqmPriceSet (replica (typeEconomy E k) r) =
      eqmPriceSet (typeEconomy E fun i => k i * r) := by
  refine eqmPriceSet_eq_of_equiv _ _
    ((Equiv.sigmaProdDistrib (fun i => Fin (k i)) (Fin r)).trans
      (Equiv.sigmaCongrRight fun _ => finProdFinEquiv)) ?_ ?_ ?_ <;>
  · rintro ⟨⟨i, a⟩, b⟩
    rfl

/-- **Exercise 17.I.1** (MWG, p. 649). Rational proportions are proportions of integers:
if `qᵢ ≥ 0` are rationals with `∑ᵢ qᵢ = 1`, there are integers `kᵢ` with `∑ᵢ kᵢ > 0` and
`qᵢ = kᵢ/∑ⱼ kⱼ`. -/
theorem exercise_17_I_1_rational [Fintype ι] (q : ι → ℚ) (hq : ∀ i, 0 ≤ q i)
    (hsum : ∑ i, q i = 1) :
    ∃ k : ι → ℕ, 0 < ∑ i, k i ∧ ∀ i, q i = k i / ∑ j, (k j : ℚ) := by
  classical
  set D : ℕ := ∏ j, (q j).den with hD
  have hDpos : (0 : ℚ) < D := by
    rw [hD]
    exact_mod_cast Finset.prod_pos fun j _ => (q j).den_pos
  set k : ι → ℕ := fun i => (q i).num.toNat * ∏ j ∈ Finset.univ.erase i, (q j).den with hk
  have hkq : ∀ i, (k i : ℚ) = q i * D := by
    intro i
    have hnum : (((q i).num.toNat : ℕ) : ℚ) = ((q i).num : ℚ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (Rat.num_nonneg.2 (hq i))]
    simp only [hk, Nat.cast_mul, Nat.cast_prod, hnum, hD]
    rw [← Finset.mul_prod_erase Finset.univ (fun j => ((q j).den : ℚ)) (Finset.mem_univ i),
      ← mul_assoc, Rat.mul_den_eq_num]
  have hksum : ∑ j, (k j : ℚ) = D := by
    simp only [hkq, ← Finset.sum_mul, hsum, one_mul]
  refine ⟨k, ?_, fun i => ?_⟩
  · have : (0 : ℚ) < ∑ j, (k j : ℚ) := hksum ▸ hDpos
    exact_mod_cast this
  · rw [hksum, hkq, mul_div_cancel_right₀ _ hDpos.ne']

/-! ### Exercise 17.I.2 -/

/-- **Exercise 17.I.2** (MWG, p. 649). The production set of `q = v²` (good `0` the input, good
`1` the output): `Y = {(-v, q) : v ≥ 0, q ≤ v²}`. -/
def ex17I2Y : Set (Fin 2 → ℝ) := {y | y 0 ≤ 0 ∧ y 1 ≤ y 0 ^ 2}

/-- **Exercise 17.I.2** (MWG, p. 649). `Y` is additive: `Y + Y ⊆ Y`. -/
theorem exercise_17_I_2_additive {y y' : Fin 2 → ℝ} (hy : y ∈ ex17I2Y) (hy' : y' ∈ ex17I2Y) :
    y + y' ∈ ex17I2Y := by
  obtain ⟨h0, h1⟩ := hy
  obtain ⟨h0', h1'⟩ := hy'
  refine ⟨by simp only [Pi.add_apply]; linarith, ?_⟩
  simp only [Pi.add_apply]
  nlinarith [mul_nonneg_of_nonpos_of_nonpos h0 h0']

/-- **Exercise 17.I.2** (MWG, p. 649). The cone generated by `Y`: `{t y : t ≥ 0, y ∈ Y}`. -/
def ex17I2Cone : Set (Fin 2 → ℝ) := {z | ∃ t : ℝ, 0 ≤ t ∧ ∃ y ∈ ex17I2Y, z = t • y}

/-- **Exercise 17.I.2** (MWG, p. 649). The cone generated by `Y` is the smallest cone
containing `Y`: it contains `Y`, is a cone, and lies in every cone containing `Y`. -/
theorem ex17I2Cone_minimal :
    ex17I2Y ⊆ ex17I2Cone ∧ (∀ z ∈ ex17I2Cone, ∀ s : ℝ, 0 ≤ s → s • z ∈ ex17I2Cone) ∧
      ∀ C : Set (Fin 2 → ℝ), ex17I2Y ⊆ C → (∀ z ∈ C, ∀ s : ℝ, 0 ≤ s → s • z ∈ C) →
        ex17I2Cone ⊆ C := by
  refine ⟨fun y hy => ⟨1, zero_le_one, y, hy, (one_smul ℝ y).symm⟩, ?_, ?_⟩
  · rintro z ⟨t, ht, y, hy, rfl⟩ s hs
    exact ⟨s * t, mul_nonneg hs ht, y, hy, by rw [smul_smul]⟩
  · rintro C hYC hC z ⟨t, ht, y, hy, rfl⟩
    exact hC y (hYC hy) t ht

/-- **Exercise 17.I.2** (MWG, p. 649). `Y* = {z : z₀ < 0} ∪ {z : z₀ = 0, z₁ ≤ 0}`. -/
theorem ex17I2Cone_eq :
    ex17I2Cone = {z | z 0 < 0} ∪ {z | z 0 = 0 ∧ z 1 ≤ 0} := by
  ext z
  constructor
  · rintro ⟨t, ht, y, ⟨hy0, hy1⟩, rfl⟩
    simp only [Pi.smul_apply, smul_eq_mul, Set.mem_union, Set.mem_ofPred_eq]
    rcases (mul_nonpos_of_nonneg_of_nonpos ht hy0).lt_or_eq with h | h
    · exact Or.inl h
    · right
      refine ⟨h, ?_⟩
      rcases mul_eq_zero.1 h with h' | h'
      · rw [h', zero_mul]
      · rw [h'] at hy1
        exact mul_nonpos_of_nonneg_of_nonpos ht (by simpa using hy1)
  · rintro (h | ⟨h0, h1⟩)
    · simp only [Set.mem_ofPred_eq] at h
      set v : ℝ := |z 1| / (-z 0) + 1 with hv
      have hz0 : 0 < -z 0 := by linarith
      have hv0 : 0 < v := by positivity
      refine ⟨-z 0 / v, div_nonneg hz0.le hv0.le, ![-v, z 1 * v / (-z 0)], ⟨?_, ?_⟩, ?_⟩
      · simp only [Matrix.cons_val_zero]
        linarith
      · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        rw [div_le_iff₀ hz0]
        have : z 1 ≤ |z 1| := le_abs_self _
        have hv' : |z 1| = (v - 1) * (-z 0) := by
          rw [hv, add_sub_cancel_right, div_mul_cancel₀ _ hz0.ne']
        nlinarith
      · have hz0ne : z 0 ≠ 0 := (by linarith : z 0 < 0).ne
        funext l
        fin_cases l
        · simp
          field_simp
        · simp
          field_simp
    · exact ⟨1, zero_le_one, z, ⟨h0.le, by rw [h0]; simpa using h1⟩, (one_smul ℝ z).symm⟩

/-- **Exercise 17.I.2** (MWG, p. 649). The smallest cone `Y*` containing `Y` is not closed:
`(0, 1) ∉ Y*` is the limit of `(-ε/2, 1) ∈ Y*`. -/
theorem exercise_17_I_2_not_closed : ¬ IsClosed ex17I2Cone := by
  intro hc
  have hmem : (![0, 1] : Fin 2 → ℝ) ∈ closure ex17I2Cone := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    refine ⟨![-(ε / 2), 1], ?_, ?_⟩
    · rw [ex17I2Cone_eq]
      left
      simp only [Set.mem_ofPred_eq, Matrix.cons_val_zero]
      linarith
    · rw [dist_pi_lt_iff hε]
      intro l
      fin_cases l
      · simp [Real.dist_eq, abs_of_pos (half_pos hε)]
        linarith
      · simp [hε]
  rw [hc.closure_eq, ex17I2Cone_eq] at hmem
  simp only [Set.mem_union, Set.mem_ofPred_eq, Matrix.cons_val_zero, Matrix.cons_val_one]
    at hmem
  norm_num at hmem

/-- **Exercise 17.I.2** (MWG, p. 649). The convex hull of `Y` is `Y*`. -/
theorem ex17I2_convexHull_eq : convexHull ℝ ex17I2Y = ex17I2Cone := by
  apply le_antisymm
  · refine convexHull_min (ex17I2Cone_minimal.1) ?_
    rw [ex17I2Cone_eq]
    intro a ha b hb s t hs ht hst
    simp only [Set.mem_union, Set.mem_ofPred_eq, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul] at ha hb ⊢
    rcases ha with ha | ⟨ha0, ha1⟩ <;> rcases hb with hb | ⟨hb0, hb1⟩
    · left
      rcases hs.lt_or_eq with hs' | hs'
      · nlinarith [mul_nonpos_of_nonneg_of_nonpos ht hb.le]
      · rw [← hs'] at hst ⊢
        rw [zero_add] at hst
        rw [hst]
        linarith
    · rcases hs.lt_or_eq with hs' | hs'
      · left
        rw [hb0]
        nlinarith
      · right
        rw [← hs'] at hst ⊢
        rw [zero_add] at hst
        rw [hst, hb0]
        constructor <;> linarith
    · rcases ht.lt_or_eq with ht' | ht'
      · left
        rw [ha0]
        nlinarith
      · right
        rw [← ht'] at hst ⊢
        rw [add_zero] at hst
        rw [hst, ha0]
        constructor <;> linarith
    · right
      rw [ha0, hb0]
      constructor
      · ring
      · nlinarith [mul_nonpos_of_nonneg_of_nonpos hs ha1, mul_nonpos_of_nonneg_of_nonpos ht hb1]
  · rw [ex17I2Cone_eq]
    rintro z (h | ⟨h0, h1⟩)
    · simp only [Set.mem_ofPred_eq] at h
      set a : ℝ := -z 0 with ha
      have ha0 : 0 < a := by linarith
      set V : ℝ := a + |z 1| / a + 1 with hV
      have hV0 : 0 < V := by positivity
      have haV : a < V := by
        have : 0 ≤ |z 1| / a := by positivity
        linarith
      set lam : ℝ := a / V with hlam
      have hlam0 : 0 < lam := div_pos ha0 hV0
      have hlam1 : lam < 1 := (div_lt_one hV0).2 haV
      set wv : ℝ := (z 1 - lam * V ^ 2) / (1 - lam) with hwv
      have hlamV : lam * V = a := by rw [hlam]; field_simp
      have hbig : z 1 ≤ lam * V ^ 2 := by
        have h1 : lam * V ^ 2 = a * V := by rw [sq, ← mul_assoc, hlamV]
        rw [h1]
        have h2 : a * V = a * a + |z 1| + a := by rw [hV]; field_simp
        rw [h2]
        have := le_abs_self (z 1)
        nlinarith
      have hw0 : wv ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
      have hA : ![-V, V ^ 2] ∈ ex17I2Y := ⟨by simp; linarith, by simp⟩
      have hB : ![0, wv] ∈ ex17I2Y := ⟨by simp, by simp [hw0]⟩
      refine segment_subset_convexHull hA hB ⟨lam, 1 - lam, hlam0.le, by linarith, by ring, ?_⟩
      funext l
      fin_cases l
      · simp
        linarith
      · have h1l : 1 - lam ≠ 0 := (by linarith : (0 : ℝ) < 1 - lam).ne'
        change lam * V ^ 2 + (1 - lam) * wv = z 1
        rw [hwv]
        field_simp
        ring
    · exact subset_convexHull ℝ _ ⟨h0.le, by rw [h0]; simpa using h1⟩

/-- **Exercise 17.I.2** (MWG, p. 649). The nonconvexity of `Y` is large: for every `M ≥ 0`
some point of `conv Y` is at distance at least `M` from `Y`. -/
theorem exercise_17_I_2_large {M : ℝ} (hM : 0 ≤ M) :
    ∃ z ∈ convexHull ℝ ex17I2Y, ∀ y ∈ ex17I2Y, M ≤ dist z y := by
  refine ⟨![-1, (1 + M) ^ 2 + M], ?_, fun y ⟨hy0, hy1⟩ => ?_⟩
  · rw [ex17I2_convexHull_eq, ex17I2Cone_eq]
    left
    simp
  · have d0 := dist_le_pi_dist (![-1, (1 + M) ^ 2 + M] : Fin 2 → ℝ) y 0
    have d1 := dist_le_pi_dist (![-1, (1 + M) ^ 2 + M] : Fin 2 → ℝ) y 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Real.dist_eq] at d0 d1
    by_cases h : M ≤ |-1 - y 0|
    · linarith
    · push Not at h
      rw [abs_lt] at h
      have hsq : y 0 ^ 2 ≤ (1 + M) ^ 2 := by nlinarith
      have : M ≤ |(1 + M) ^ 2 + M - y 1| := by
        rw [abs_of_nonneg (by linarith)]
        linarith
      linarith

/-- **Exercise 17.I.2** (MWG, p. 649). At any price vector with a positive output price, the
firm's profit `p·y` is unbounded on `Y` (`y = (-v, v²)`, `v → ∞`), whatever the number of
consumers: there is no profit-maximizing production plan, and no sense in which a near
equilibrium exists. -/
theorem exercise_17_I_2_profit_unbounded {p : Fin 2 → ℝ} (hp : 0 < p 1) (M : ℝ) :
    ∃ y ∈ ex17I2Y, M < p ⬝ᵥ y := by
  set v : ℝ := (|p 0| + |M| + 1) / p 1 + 1 with hv
  have hv0 : 1 ≤ v := by
    have : 0 ≤ (|p 0| + |M| + 1) / p 1 := by positivity
    linarith
  refine ⟨![-v, v ^ 2], ⟨by simp; linarith, by simp⟩, ?_⟩
  simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  have h1 : |p 0| + |M| + 1 ≤ p 1 * v := by
    have : p 1 * ((|p 0| + |M| + 1) / p 1) = |p 0| + |M| + 1 := by field_simp
    rw [hv, mul_add, this, mul_one]
    linarith
  have h2 : (|p 0| + |M| + 1) * v ≤ p 1 * v ^ 2 := by
    rw [sq, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right h1 (by linarith)
  have h3 : -(|p 0| * v) ≤ -(p 0 * v) := by
    have := le_abs_self (p 0)
    nlinarith
  have h4 : M ≤ |M| := le_abs_self M
  have h5 : (|M| + 1) * 1 ≤ (|M| + 1) * v := mul_le_mul_of_nonneg_left hv0 (by positivity)
  nlinarith

end MWG.PositiveEquilibriumTheory
