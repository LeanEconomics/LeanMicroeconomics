/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGClassicalDemand.CloserComposite
import MWGClassicalDemand.RelationsBasic

/-!
# Exercise 3.G.5(b)-(c): the composite commodity utility `ũ`

MWG, Exercise 3.G.5, pp. 99-100. Goods `x ∈ ℝ^A_+` (prices `p`) and `y ∈ ℝ^B_+` (prices
`q = α q₀`, `q₀ ≫ 0`); `ũ(x, z) = max {u(x, y) : y ≥ 0, q₀·y ≤ z}` (`compositeUtility`).

The bridge: a composite bundle `(x, z) ∈ ℝ^A × ℝ` is the vector `Fin.snoc x z ∈ ℝ^{A+1}` (last
coordinate `z`), with inverse `v ↦ (Fin.init v, v_{A+1})`; composite prices `(p, α)` are
`Fin.snoc p α`, and `(p, α)·(x, z) = p·x + αz` (`last_snoc_dot`). The composite utility on
`ℝ^{A+1}` is `lastCompositeVec u q₀ v = ũ(Fin.init v, v_{A+1})`.

Properties of `ũ` proved here, for `u` continuous on `ℝ^A_+ × ℝ^B_+`, strictly increasing in `y`
(the `y` goods are desirable), and `q₀ ≫ 0`:
* the maximum defining `ũ` is attained (`last_composite_attained`), and at a maximizer the
  budget for `y` is exhausted (`last_composite_exhausts`);
* `ũ` is continuous on `ℝ^{A+1}_+` (`last_composite_continuousOn`): on the orthant
  `ũ(x, z) = max_{y' ∈ K} u(x, z y')` over the fixed compact `K = {y' ≥ 0, q₀·y' ≤ 1}`, and the
  maximum of a continuous function over a fixed compact set is continuous (Berge's theorem in the
  form `IsCompact.continuous_sSup`);
* the preference of `ũ` is locally nonsatiated (`last_composite_lns`);
* if `u` is strictly quasiconcave on `ℝ^{A+B}_+`, `ũ` is strictly quasiconcave on `ℝ^{A+1}_+`
  (`last_composite_strictlyQuasiconcave`).

With these, every result of Sections 3.D, 3.E and 3.G proved in this project for a utility on
`ℝ^L_+` applies to `ũ` with `L = A + 1`: module `LastCompositeApps`.
-/

namespace MWG.ClassicalDemand

open MWG.ConsumerChoice Kreps.PreferenceProperties

variable {A B : ℕ}

/-- **Exercise 3.G.5** (MWG, p. 99). The composite utility `ũ` as a function on `ℝ^{A+1}`:
`v ↦ ũ(Fin.init v, v_{A+1})`. -/
noncomputable def lastCompositeVec (u : (Fin A → ℝ) → (Fin B → ℝ) → ℝ) (q0 : Fin B → ℝ)
    (v : Fin (A + 1) → ℝ) : ℝ :=
  compositeUtility u q0 (Fin.init v) (v (Fin.last A))

/-- The bridge `(x, z) ↦ Fin.snoc x z`. -/
def lastSnoc (x : Fin A → ℝ) (z : ℝ) : Fin (A + 1) → ℝ := Fin.snoc x z

/-- `ũ` on `ℝ^{A+1}` at `(x, z)` is `ũ(x, z)`. -/
theorem lastCompositeVec_snoc (u : (Fin A → ℝ) → (Fin B → ℝ) → ℝ) (q0 : Fin B → ℝ)
    (x : Fin A → ℝ) (z : ℝ) : lastCompositeVec u q0 (lastSnoc x z) = compositeUtility u q0 x z := by
  simp [lastCompositeVec, lastSnoc, Fin.init_snoc, Fin.snoc_last]

/-- The bridge is onto: `v = (Fin.init v, v_{A+1})`. -/
theorem lastSnoc_init (v : Fin (A + 1) → ℝ) : lastSnoc (Fin.init v) (v (Fin.last A)) = v :=
  Fin.snoc_init_self v

/-- Coordinates of the bridge. -/
theorem lastSnoc_castSucc (x : Fin A → ℝ) (z : ℝ) (i : Fin A) :
    lastSnoc x z (Fin.castSucc i) = x i := by
  simp [lastSnoc]

/-- The last coordinate of the bridge. -/
theorem lastSnoc_last (x : Fin A → ℝ) (z : ℝ) : lastSnoc x z (Fin.last A) = z := by
  simp [lastSnoc]

/-- `(p, α)·(x, z) = p·x + αz`. -/
theorem last_snoc_dot (p : Fin A → ℝ) (α : ℝ) (x : Fin A → ℝ) (z : ℝ) :
    lastSnoc p α ⬝ᵥ lastSnoc x z = p ⬝ᵥ x + α * z := by
  simp [dotProduct, Fin.sum_univ_castSucc, lastSnoc_castSucc, lastSnoc_last]

/-- `(x, z) ∈ ℝ^{A+1}_+ ⟺ x ∈ ℝ^A_+ ∧ z ≥ 0`. -/
theorem last_snoc_mem (x : Fin A → ℝ) (z : ℝ) :
    lastSnoc x z ∈ nonnegOrthant (A + 1) ↔ x ∈ nonnegOrthant A ∧ 0 ≤ z := by
  constructor
  · intro h
    exact ⟨fun i => by simpa [lastSnoc_castSucc] using h (Fin.castSucc i),
      by simpa [lastSnoc_last] using h (Fin.last A)⟩
  · rintro ⟨hx, hz⟩ i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [lastSnoc_last]; exact hz
    · rw [lastSnoc_castSucc]; exact hx j

/-- `(p, α) ≫ 0 ⟺ p ≫ 0 ∧ α > 0`. -/
theorem last_snoc_pos (p : Fin A → ℝ) (α : ℝ) :
    StrictlyPositive (lastSnoc p α) ↔ StrictlyPositive p ∧ 0 < α := by
  constructor
  · intro h
    exact ⟨fun i => by simpa [lastSnoc_castSucc] using h (Fin.castSucc i),
      by simpa [lastSnoc_last] using h (Fin.last A)⟩
  · rintro ⟨hp, hα⟩ i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [lastSnoc_last]; exact hα
    · rw [lastSnoc_castSucc]; exact hp j

/-- The `y`-budget `{y ≥ 0, q₀·y ≤ z}` is the budget set `B_{q₀, z}`. -/
theorem last_composite_set_eq (q0 : Fin B → ℝ) (z : ℝ) :
    {y | y ∈ nonnegOrthant B ∧ q0 ⬝ᵥ y ≤ z} = budgetSet q0 z := rfl

/-- The maximum defining `ũ(x, z)` is attained, for `u(x, ·)` continuous on `ℝ^B_+`. -/
theorem last_composite_attained {u : (Fin A → ℝ) → (Fin B → ℝ) → ℝ} {q0 : Fin B → ℝ}
    (hq0 : StrictlyPositive q0) {x : Fin A → ℝ} (hux : ContinuousOn (u x) (nonnegOrthant B))
    {z : ℝ} (hz : 0 ≤ z) :
    ∃ y ∈ budgetSet q0 z, compositeUtility u q0 x z = u x y ∧
      ∀ y' ∈ budgetSet q0 z, u x y' ≤ u x y := by
  obtain ⟨y, hy, hmax⟩ := (isCompact_budgetSet hq0 z).exists_isMaxOn
    ⟨0, zero_mem_budgetSet q0 hz⟩ (hux.mono fun _ hy => hy.1)
  refine ⟨y, hy, ?_, fun y' hy' => hmax hy'⟩
  unfold compositeUtility
  rw [last_composite_set_eq]
  exact IsGreatest.csSup_eq ⟨⟨y, hy, rfl⟩, by rintro _ ⟨y', hy', rfl⟩; exact hmax hy'⟩

/-- At a maximizer the `y`-budget is exhausted, when `u` is strictly increasing in `y`. -/
theorem last_composite_exhausts {u : (Fin A → ℝ) → (Fin B → ℝ) → ℝ} {q0 : Fin B → ℝ}
    (hq0 : StrictlyPositive q0) {x : Fin A → ℝ}
    (hmono : ∀ y ∈ nonnegOrthant B, ∀ y' : Fin B → ℝ, (∀ j, y j < y' j) → u x y < u x y')
    {z : ℝ} {y : Fin B → ℝ} (hy : y ∈ budgetSet q0 z)
    (hmax : ∀ y' ∈ budgetSet q0 z, u x y' ≤ u x y) : q0 ⬝ᵥ y = z := by
  by_contra hne
  have hlt : q0 ⬝ᵥ y < z := lt_of_le_of_ne hy.2 hne
  set c := ∑ j, q0 j with hc
  have hc0 : 0 ≤ c := Finset.sum_nonneg fun j _ => (hq0 j).le
  set η := (z - q0 ⬝ᵥ y) / (c + 1) with hη
  have hη0 : 0 < η := div_pos (by linarith) (by linarith)
  have hmem : (y + fun _ => η) ∈ budgetSet q0 z := by
    refine ⟨fun j => by simp only [Pi.add_apply]; linarith [hy.1 j], ?_⟩
    have : q0 ⬝ᵥ (y + fun _ => η) = q0 ⬝ᵥ y + η * c := by
      rw [dotProduct_add, hc, Finset.mul_sum]
      simp [dotProduct, mul_comm]
    rw [this]
    have : η * c ≤ η * (c + 1) := by nlinarith
    have h2 : η * (c + 1) = z - q0 ⬝ᵥ y := by rw [hη]; field_simp
    linarith
  have := hmax _ hmem
  have hgt := hmono y hy.1 (y + fun _ => η) fun j => by simp only [Pi.add_apply]; linarith
  linarith

/-- **Exercise 3.G.5(c)** (MWG, p. 100), continuity of `ũ`: if `u` is continuous on
`ℝ^A_+ × ℝ^B_+` and `q₀ ≫ 0`, then `ũ` is continuous on `ℝ^{A+1}_+` (Berge's maximum theorem;
on the orthant `{y ≥ 0, q₀·y ≤ z} = z K` with the fixed compact `K = B_{q₀, 1}`). -/
theorem last_composite_continuousOn {u : (Fin A → ℝ) → (Fin B → ℝ) → ℝ} {q0 : Fin B → ℝ}
    (hq0 : StrictlyPositive q0)
    (hu : ContinuousOn (Function.uncurry u) (nonnegOrthant A ×ˢ nonnegOrthant B)) :
    ContinuousOn (lastCompositeVec u q0) (nonnegOrthant (A + 1)) := by
  set K := budgetSet q0 1 with hK
  have hKc : IsCompact K := isCompact_budgetSet hq0 1
  set clA : (Fin A → ℝ) → Fin A → ℝ := fun x i => max (x i) 0 with hclA
  set clB : (Fin B → ℝ) → Fin B → ℝ := fun y j => max (y j) 0 with hclB
  set g : (Fin (A + 1) → ℝ) × (Fin B → ℝ) → (Fin A → ℝ) × (Fin B → ℝ) :=
    fun vy => (clA (Fin.init vy.1), clB (vy.1 (Fin.last A) • vy.2)) with hg
  have hgc : Continuous g := by
    simp only [hg, hclA, hclB, Fin.init]
    fun_prop
  have hgm : ∀ vy, g vy ∈ nonnegOrthant A ×ˢ nonnegOrthant B := fun vy =>
    ⟨fun i => le_max_right _ _, fun j => le_max_right _ _⟩
  set G : (Fin (A + 1) → ℝ) → (Fin B → ℝ) → ℝ := fun v y => Function.uncurry u (g (v, y))
    with hG
  have hGc : Continuous (Function.uncurry G) := hu.comp_continuous hgc hgm
  have hc := hKc.continuous_sSup (f := G) hGc
  refine hc.continuousOn.congr fun v hv => ?_
  have hx : Fin.init v ∈ nonnegOrthant A := fun i => hv (Fin.castSucc i)
  have hz : 0 ≤ v (Fin.last A) := hv (Fin.last A)
  have hclx : clA (Fin.init v) = Fin.init v := funext fun i => max_eq_left (hx i)
  unfold lastCompositeVec compositeUtility
  rw [last_composite_set_eq]
  congr 1
  ext t
  constructor
  · rintro ⟨y, hy, rfl⟩
    rcases eq_or_lt_of_le hz with h0 | hpos
    · -- `z = 0`: the only affordable `y` is `0`
      have hy0 : y = 0 := by
        funext j
        have hsum : q0 ⬝ᵥ y = 0 := le_antisymm (h0 ▸ hy.2)
          (Finset.sum_nonneg fun j _ => mul_nonneg (hq0 j).le (hy.1 j))
        have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ =>
          mul_nonneg (hq0 j).le (hy.1 j)).mp hsum j (Finset.mem_univ j)
        exact (mul_eq_zero.mp this).resolve_left (hq0 j).ne'
      refine ⟨0, zero_mem_budgetSet q0 zero_le_one, ?_⟩
      simp only [hG, hg, Function.uncurry_apply_pair, hclx, smul_zero, ← h0, hy0]
      congr 1
      funext j
      simp [hclB]
    · refine ⟨(v (Fin.last A))⁻¹ • y, ⟨fun j => ?_, ?_⟩, ?_⟩
      · simp only [Pi.smul_apply, smul_eq_mul]
        exact mul_nonneg (inv_nonneg.mpr hz) (hy.1 j)
      · rw [dotProduct_smul, smul_eq_mul, inv_mul_le_iff₀ hpos, mul_one]
        exact hy.2
      · simp only [hG, hg, Function.uncurry_apply_pair, hclx, smul_smul,
          mul_inv_cancel₀ hpos.ne', one_smul]
        congr 1
        funext j
        exact max_eq_left (hy.1 j)
  · rintro ⟨y, hy, rfl⟩
    refine ⟨v (Fin.last A) • y, ⟨fun j => ?_, ?_⟩, ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul]
      exact mul_nonneg hz (hy.1 j)
    · rw [dotProduct_smul, smul_eq_mul]
      have := mul_le_mul_of_nonneg_left hy.2 hz
      linarith
    · simp only [hG, hg, Function.uncurry_apply_pair, hclx]
      congr 1
      funext j
      simp only [hclB, Pi.smul_apply, smul_eq_mul]
      exact (max_eq_left (mul_nonneg hz (hy.1 j))).symm

/-- `u(x, ·)` is continuous on `ℝ^B_+` when `u` is jointly continuous on the orthant. -/
theorem last_composite_section {u : (Fin A → ℝ) → (Fin B → ℝ) → ℝ}
    (hu : ContinuousOn (Function.uncurry u) (nonnegOrthant A ×ˢ nonnegOrthant B))
    {x : Fin A → ℝ} (hx : x ∈ nonnegOrthant A) : ContinuousOn (u x) (nonnegOrthant B) :=
  hu.comp (f := fun y => (x, y)) (Continuous.continuousOn (by fun_prop)) fun _ hy => ⟨hx, hy⟩

/-- **Exercise 3.G.5(c)** (MWG, p. 100): the preference of `ũ` on `ℝ^{A+1}_+` is locally
nonsatiated when the `y` goods are desirable (`u` strictly increasing in `y`). -/
theorem last_composite_lns {u : (Fin A → ℝ) → (Fin B → ℝ) → ℝ} {q0 : Fin B → ℝ}
    (hq0 : StrictlyPositive q0)
    (hu : ContinuousOn (Function.uncurry u) (nonnegOrthant A ×ˢ nonnegOrthant B))
    (hmono : ∀ x ∈ nonnegOrthant A, ∀ y ∈ nonnegOrthant B, ∀ y' : Fin B → ℝ,
      (∀ j, y j < y' j) → u x y < u x y') :
    LocallyNonsatiated (nonnegOrthant (A + 1)) (utilityPref (lastCompositeVec u q0)) := by
  intro v hv ε hε
  set x := Fin.init v with hxdef
  set z := v (Fin.last A) with hzdef
  have hx : x ∈ nonnegOrthant A := fun i => hv (Fin.castSucc i)
  have hz : 0 ≤ z := hv (Fin.last A)
  have hv' : v = lastSnoc x z := (lastSnoc_init v).symm
  obtain ⟨y, hy, hval, -⟩ := last_composite_attained hq0 (last_composite_section hu hx) hz
  obtain ⟨Y, -, hval', hmax'⟩ := last_composite_attained hq0 (last_composite_section hu hx)
    (by linarith : 0 ≤ z + ε)
  refine ⟨lastSnoc x (z + ε), (last_snoc_mem x _).mpr ⟨hx, by linarith⟩, ?_, ?_⟩
  · rw [hv']
    unfold euclidDist
    rw [Fin.sum_univ_castSucc]
    simp only [lastSnoc_castSucc, lastSnoc_last, sub_self, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, Finset.sum_const_zero, zero_add, add_sub_cancel_left]
    rw [Real.sqrt_sq hε.le]
  · -- `y` plus a little of every `y` good is affordable at `z + ε` and strictly better
    set c := ∑ j, q0 j with hc
    have hc0 : 0 ≤ c := Finset.sum_nonneg fun j _ => (hq0 j).le
    set η := ε / (c + 1) with hη
    have hη0 : 0 < η := div_pos hε (by linarith)
    have hmem : (y + fun _ => η) ∈ budgetSet q0 (z + ε) := by
      refine ⟨fun j => by simp only [Pi.add_apply]; linarith [hy.1 j], ?_⟩
      have : q0 ⬝ᵥ (y + fun _ => η) = q0 ⬝ᵥ y + η * c := by
        rw [dotProduct_add, hc, Finset.mul_sum]
        simp [dotProduct, mul_comm]
      rw [this]
      have : η * c ≤ η * (c + 1) := by nlinarith
      have h2 : η * (c + 1) = ε := by rw [hη]; field_simp
      linarith [hy.2]
    have hlt : lastCompositeVec u q0 v < lastCompositeVec u q0 (lastSnoc x (z + ε)) := by
      rw [lastCompositeVec_snoc, hval', hv', lastCompositeVec_snoc, hval]
      exact (hmono x hx y hy.1 (y + fun _ => η) fun j => by
        simp only [Pi.add_apply]; linarith).trans_le
        (hmax' _ hmem)
    exact ⟨hlt.le, not_le.mpr hlt⟩

/-- **Exercise 3.G.5(c)** (MWG, p. 100): if `u` is strictly quasiconcave on `ℝ^A_+ × ℝ^B_+`
(strictly convex preferences over `(x, y)`) and strictly increasing in `y`, then `ũ` is strictly
quasiconcave on `ℝ^{A+1}_+`. -/
theorem last_composite_strictlyQuasiconcave {u : (Fin A → ℝ) → (Fin B → ℝ) → ℝ}
    {q0 : Fin B → ℝ} (hq0 : StrictlyPositive q0)
    (hu : ContinuousOn (Function.uncurry u) (nonnegOrthant A ×ˢ nonnegOrthant B))
    (hmono : ∀ x ∈ nonnegOrthant A, ∀ y ∈ nonnegOrthant B, ∀ y' : Fin B → ℝ,
      (∀ j, y j < y' j) → u x y < u x y')
    (hsq : ∀ x ∈ nonnegOrthant A, ∀ x' ∈ nonnegOrthant A, ∀ y ∈ nonnegOrthant B,
      ∀ y' ∈ nonnegOrthant B, (x, y) ≠ (x', y') → ∀ a : ℝ, 0 < a → a < 1 →
        min (u x y) (u x' y') < u (a • x + (1 - a) • x') (a • y + (1 - a) • y')) :
    StrictlyQuasiconcaveOn (nonnegOrthant (A + 1)) (lastCompositeVec u q0) := by
  refine ⟨convex_nonnegOrthant (A + 1), fun v hv v' hv' hne a ha0 ha1 t ht ht' => ?_⟩
  have hx : Fin.init v ∈ nonnegOrthant A := fun i => hv (Fin.castSucc i)
  have hz : 0 ≤ v (Fin.last A) := hv (Fin.last A)
  have hx' : Fin.init v' ∈ nonnegOrthant A := fun i => hv' (Fin.castSucc i)
  have hz' : 0 ≤ v' (Fin.last A) := hv' (Fin.last A)
  obtain ⟨y, hy, hval, hmax⟩ := last_composite_attained hq0 (last_composite_section hu hx) hz
  obtain ⟨y', hy', hval', hmax'⟩ := last_composite_attained hq0 (last_composite_section hu hx') hz'
  have hex := last_composite_exhausts hq0 (hmono _ hx) hy hmax
  have hex' := last_composite_exhausts hq0 (hmono _ hx') hy' hmax'
  have hpair : (Fin.init v, y) ≠ (Fin.init v', y') := by
    intro heq
    obtain ⟨h1, h2⟩ := Prod.mk.inj heq
    apply hne
    rw [← lastSnoc_init v, ← lastSnoc_init v', h1, ← hex, ← hex', h2]
  set w := a • v + (1 - a) • v' with hw
  have hwx : Fin.init w = a • Fin.init v + (1 - a) • Fin.init v' := by
    funext i
    simp [hw, Fin.init]
  have hwz : w (Fin.last A) = a * v (Fin.last A) + (1 - a) * v' (Fin.last A) := by
    simp [hw]
  have hwm : w ∈ nonnegOrthant (A + 1) :=
    convex_nonnegOrthant (A + 1) hv hv' ha0.le (by linarith) (by ring)
  have hwxm : Fin.init w ∈ nonnegOrthant A := fun i => hwm (Fin.castSucc i)
  obtain ⟨Y, -, hvalw, hmaxw⟩ := last_composite_attained hq0 (last_composite_section hu hwxm)
    (hwm (Fin.last A))
  have hcomb : a • y + (1 - a) • y' ∈ budgetSet q0 (w (Fin.last A)) := by
    refine ⟨fun j => ?_, ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have := hy.1 j
      have := hy'.1 j
      have : 0 ≤ 1 - a := by linarith
      positivity
    · rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul, hwz,
        hex, hex']
  have hstrict := hsq _ hx _ hx' _ hy.1 _ hy'.1 hpair a ha0 ha1
  unfold lastCompositeVec at ht ht' ⊢
  rw [hval] at ht
  rw [hval'] at ht'
  rw [hvalw]
  calc t ≤ min (u (Fin.init v) y) (u (Fin.init v') y') := le_min ht ht'
    _ < u (a • Fin.init v + (1 - a) • Fin.init v') (a • y + (1 - a) • y') := hstrict
    _ = u (Fin.init w) (a • y + (1 - a) • y') := by rw [hwx]
    _ ≤ u (Fin.init w) Y := hmaxw _ hcomb

end MWG.ClassicalDemand
