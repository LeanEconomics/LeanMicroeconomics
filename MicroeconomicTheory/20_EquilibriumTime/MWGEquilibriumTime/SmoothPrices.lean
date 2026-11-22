/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGEquilibriumTime.Production

/-!
# Malinvaud prices in the smooth case (MWG Section 20.C, small type; Exercise 20.C.5(b))

MWG, Chapter 20, the small-type discussion at the end of Section 20.C, pp. 742-743, and
Exercise 20.C.5(b), p. 783.

A technology is smooth at `y ∈ Y` with normal `q` (`SmoothAt`) if `q` supports `Y` at `y` and every
supporting vector is a positive multiple of `q` (the marginal rates of transformation at `y` are
uniquely defined).

* The inductive construction of Malinvaud prices from normals satisfying
  `q_{a,t-1} = β_t q_{b,t}` (`malinvaud_of_proportional_normals`).
* MWG's claim that (short-run) efficiency forces `q_{a,t} ∝ q_{b,t+1}`, proved from
  `2`-efficiency (changes at two consecutive dates only) by the second fundamental theorem of
  Chapter 5 (`MWG.Production.proposition_5_F_2`) applied to the stacked two-date technology
  (`proportional_normals_of_twoEfficient`).
* **Exercise 20.C.5(b)**: with a smooth convex technology and strictly positive normals,
  `2`-efficiency implies `T`-efficiency for every `T` (`exercise_20_C_5b`), and in fact yields
  strictly positive Malinvaud prices (`malinvaud_of_twoEfficient`).
-/

open Filter Topology

namespace MWG.EquilibriumTime

variable {ι : Type*} [Fintype ι]

/-- `q ≠ 0` **supports** `Y` at `y`: `y` maximizes `q_b · z_b + q_a · z_a` over `Y`. -/
def SupportsAt (Y : Set (ProdPlan ι)) (y q : ProdPlan ι) : Prop :=
  q ≠ 0 ∧ ∀ z ∈ Y, planValue q.1 q.2 z ≤ planValue q.1 q.2 y

/-- **Smoothness** (MWG, p. 742): `Y` has a single outward normal `q` at `y`, up to positive
scaling. -/
def SmoothAt (Y : Set (ProdPlan ι)) (y q : ProdPlan ι) : Prop :=
  SupportsAt Y y q ∧ ∀ q', SupportsAt Y y q' → ∃ c : ℝ, 0 < c ∧ q' = c • q

theorem planValue_smul (c : ℝ) (a b : ι → ℝ) (z : ProdPlan ι) :
    planValue (c • a) (c • b) z = c * planValue a b z := by
  simp only [planValue, smul_dotProduct, smul_eq_mul]
  ring

/-- The cumulative scale factors `c_t = β_0 ⋯ β_{t-1}` of the construction (MWG, p. 743). -/
noncomputable def normalScale (β : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | t + 1 => normalScale β t * β t

theorem normalScale_pos {β : ℕ → ℝ} (hβ : ∀ t, 0 < β t) (t : ℕ) : 0 < normalScale β t := by
  induction t with
  | zero => exact one_pos
  | succ t ih => exact mul_pos ih (hβ t)

/-- The prices built from the normals: `p_t = c_t q_{b,t}` (MWG, p. 743, `p_0 = q_{b0}`). -/
noncomputable def normalPrices (β : ℕ → ℝ) (q : ℕ → ProdPlan ι) (t : ℕ) : ι → ℝ :=
  normalScale β t • (q t).1

/-- **The construction of Malinvaud prices** in the smooth case (MWG, pp. 742-743): if `q_t`
supports `Y` at `y_t` and `q_{a,t} = β_t q_{b,t+1}` with `β_t > 0`, then `p_t = c_t q_{b,t}` makes
the path myopically profit maximizing, because `(p_t, p_{t+1}) = c_t q_t`. -/
theorem malinvaud_of_proportional_normals {Y : Set (ProdPlan ι)} {y : ℕ → ProdPlan ι}
    (hpath : IsProdPath Y y) {q : ℕ → ProdPlan ι} (hq : ∀ t, SupportsAt Y (y t) (q t))
    {β : ℕ → ℝ} (hβ : ∀ t, 0 < β t) (hprop : ∀ t, (q t).2 = β t • (q (t + 1)).1) :
    MyopicProfitMax Y (normalPrices β q) y := by
  refine ⟨hpath, fun t z hz => ?_⟩
  have hpair : normalPrices β q (t + 1) = normalScale β t • (q t).2 := by
    rw [normalPrices, normalScale, hprop t, smul_smul]
  have h := (hq t).2 z hz
  simp only [periodProfit]
  rw [hpair, normalPrices, planValue_smul, planValue_smul]
  exact mul_le_mul_of_nonneg_left h (normalScale_pos hβ t).le

omit [Fintype ι] in
/-- The constructed prices are strictly positive when the normals' initial parts are. -/
theorem normalPrices_strictPos {β : ℕ → ℝ} (hβ : ∀ t, 0 < β t) {q : ℕ → ProdPlan ι}
    (hq : ∀ t, StrictPos (q t).1) (t : ℕ) : StrictPos (normalPrices β q t) := fun i => by
  simp only [normalPrices, Pi.smul_apply, smul_eq_mul]
  exact mul_pos (normalScale_pos hβ t) (hq t i)

/-! ### The stacked two-date technology -/

variable {L : ℕ}

/-- Stacking three blocks of `ℝ^L` into `ℝ^{3L}`. -/
def tripleVec (a b c : Fin L → ℝ) : Fin (L + L + L) → ℝ := Fin.append (Fin.append a b) c

theorem tripleVec_le_iff (a b c a' b' c' : Fin L → ℝ) :
    tripleVec a b c ≤ tripleVec a' b' c' ↔ a ≤ a' ∧ b ≤ b' ∧ c ≤ c' := by
  constructor
  · intro h
    refine ⟨fun i => ?_, fun i => ?_, fun i => ?_⟩
    · have := h (Fin.castAdd L (Fin.castAdd L i))
      simp only [tripleVec, Fin.append_left] at this
      exact this
    · have := h (Fin.castAdd L (Fin.natAdd L i))
      simp only [tripleVec, Fin.append_left, Fin.append_right] at this
      exact this
    · have := h (Fin.natAdd (L + L) i)
      simp only [tripleVec, Fin.append_right] at this
      exact this
  · rintro ⟨ha, hb, hc⟩ k
    refine Fin.addCases (fun j => ?_) (fun j => ?_) k
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simp only [tripleVec, Fin.append_left]; exact ha i
      · simp only [tripleVec, Fin.append_left, Fin.append_right]; exact hb i
    · simp only [tripleVec, Fin.append_right]; exact hc j

theorem tripleVec_injective {a b c a' b' c' : Fin L → ℝ}
    (h : tripleVec a b c = tripleVec a' b' c') : a = a' ∧ b = b' ∧ c = c' := by
  have h1 := (tripleVec_le_iff a b c a' b' c').1 h.le
  have h2 := (tripleVec_le_iff a' b' c' a b c).1 h.ge
  exact ⟨le_antisymm h1.1 h2.1, le_antisymm h1.2.1 h2.2.1, le_antisymm h1.2.2 h2.2.2⟩

theorem dotProduct_tripleVec (p : Fin (L + L + L) → ℝ) (a b c : Fin L → ℝ) :
    p ⬝ᵥ tripleVec a b c = (fun i => p (Fin.castAdd L (Fin.castAdd L i))) ⬝ᵥ a
      + (fun i => p (Fin.castAdd L (Fin.natAdd L i))) ⬝ᵥ b
      + (fun i => p (Fin.natAdd (L + L) i)) ⬝ᵥ c := by
  simp only [dotProduct, tripleVec]
  rw [Fin.sum_univ_add, Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]

/-- The two-date technology of dates `t, t+1`: the net vectors
`(z_b, z_a + z'_b, z'_a)` for `z, z' ∈ Y`, stacked in `ℝ^{3L}`. -/
def twoDateSet (Y : Set (ProdPlan (Fin L))) : Set (Fin (L + L + L) → ℝ) :=
  {v | ∃ z ∈ Y, ∃ z' ∈ Y, v = tripleVec z.1 (z.2 + z'.1) z'.2}

theorem convex_twoDateSet {Y : Set (ProdPlan (Fin L))} (hY : Convex ℝ Y) :
    Convex ℝ (twoDateSet Y) := by
  have hlin : IsLinearMap ℝ (fun w : ProdPlan (Fin L) × ProdPlan (Fin L) =>
      tripleVec w.1.1 (w.1.2 + w.2.1) w.2.2) := by
    constructor
    · intro w w'
      funext k
      refine Fin.addCases (fun j => ?_) (fun j => ?_) k
      · refine Fin.addCases (fun i => ?_) (fun i => ?_) j
        · simp only [tripleVec, Fin.append_left, Pi.add_apply, Prod.fst_add, Prod.snd_add]
        · simp only [tripleVec, Fin.append_left, Fin.append_right, Pi.add_apply, Prod.fst_add,
            Prod.snd_add]
          ring
      · simp only [tripleVec, Fin.append_right, Pi.add_apply, Prod.snd_add]
    · intro c w
      funext k
      refine Fin.addCases (fun j => ?_) (fun j => ?_) k
      · refine Fin.addCases (fun i => ?_) (fun i => ?_) j
        · simp only [tripleVec, Fin.append_left, Pi.smul_apply, Prod.smul_fst]
        · simp only [tripleVec, Fin.append_left, Fin.append_right, Pi.add_apply,
            Pi.smul_apply, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
          ring
      · simp only [tripleVec, Fin.append_right, Pi.smul_apply, Prod.smul_snd]
  have h := (hY.prod hY).is_linear_image hlin
  convert h using 1
  ext v
  constructor
  · rintro ⟨z, hz, z', hz', rfl⟩
    exact ⟨(z, z'), ⟨hz, hz'⟩, rfl⟩
  · rintro ⟨⟨z, z'⟩, ⟨hz, hz'⟩, rfl⟩
    exact ⟨z, hz, z', hz', rfl⟩

/-- Changing the plans of a path at the dates `t` and `t + 1`. -/
def updateTwo (y : ℕ → ProdPlan ι) (t : ℕ) (z z' : ProdPlan ι) : ℕ → ProdPlan ι :=
  fun s => if s = t then z else if s = t + 1 then z' else y s

omit [Fintype ι] in
theorem updateTwo_changes (y : ℕ → ProdPlan ι) (t : ℕ) (z z' : ProdPlan ι) :
    {s | updateTwo y t z z' s ≠ y s} ⊆ {t, t + 1} := by
  intro s hs
  by_contra h
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at h
  exact hs (by simp [updateTwo, h.1, h.2])

/-- Two-efficiency at the consecutive dates `t, t+1` makes the stacked point efficient in the
two-date technology. -/
theorem efficient_twoDateSet {Y : Set (ProdPlan (Fin L))} {y : ℕ → ProdPlan (Fin L)}
    (hy : TEfficient Y y 2) (t : ℕ) :
    MWG.Production.Efficient (twoDateSet Y)
      (tripleVec (y t).1 ((y t).2 + (y (t + 1)).1) (y (t + 1)).2) := by
  refine ⟨⟨y t, hy.1 t, y (t + 1), hy.1 (t + 1), rfl⟩, ?_⟩
  rintro ⟨v, ⟨z, hz, z', hz', rfl⟩, hle, hne⟩
  obtain ⟨h1, h2, h3⟩ := (tripleVec_le_iff _ _ _ _ _ _).1 hle
  set y' := updateTwo y t z z' with hy'
  have hpath : IsProdPath Y y' := by
    intro s
    simp only [hy', updateTwo]
    split_ifs
    · exact hz
    · exact hz'
    · exact hy.1 s
  have hfin : {s | y' s ≠ y s}.Finite :=
    (Set.toFinite {t, t + 1}).subset (updateTwo_changes _ _ _ _)
  have hcard : {s | y' s ≠ y s}.ncard ≤ 2 := by
    calc {s | y' s ≠ y s}.ncard ≤ ({t, t + 1} : Set ℕ).ncard :=
          Set.ncard_le_ncard (updateTwo_changes _ _ _ _) (Set.toFinite _)
      _ = 2 := Set.ncard_pair (by omega)
  have hnet : ∀ s, netOutput y s ≤ netOutput y' s := by
    intro s
    rcases s with _ | s
    · by_cases h0 : t = 0
      · subst h0; simpa [netOutput, hy', updateTwo] using h1
      · simp [netOutput, hy', updateTwo, Ne.symm h0]
    · simp only [netOutput, hy', updateTwo]
      by_cases ha : s = t
      · subst ha
        simp only [ite_true, show s + 1 ≠ s by omega]
        simpa using h2
      · by_cases hb : s = t + 1
        · subst hb
          simp only [show t + 1 ≠ t by omega, show t + 1 + 1 ≠ t by omega,
            show t + 1 + 1 ≠ t + 1 by omega]
          simp only [↓reduceIte]
          exact add_le_add h3 le_rfl
        · by_cases hc : s + 1 = t
          · subst hc
            simp only [ha, hb]
            simp only [↓reduceIte]
            exact add_le_add le_rfl h1
          · simp [ha, hb, hc]
  refine hy.2 ⟨y', hpath, hnet, fun heq => hne ?_, hfin, hcard⟩
  -- equal net outputs force equal stacked vectors
  have e1 := congrFun heq t
  have e2 := congrFun heq (t + 1)
  have e3 := congrFun heq (t + 2)
  have ht1 : t + 1 ≠ t := by omega
  have ht2 : t + 2 ≠ t := by omega
  have ht3 : t + 2 ≠ t + 1 := by omega
  have hb : z.1 = (y t).1 := by
    rcases t with _ | t
    · simpa [netOutput, hy', updateTwo] using e1
    · simp only [netOutput, hy', updateTwo, show t ≠ t + 1 by omega, ite_true,
        show t ≠ t + 1 + 1 by omega] at e1
      simpa using e1
  have hm : z.2 + z'.1 = (y t).2 + (y (t + 1)).1 := by
    simpa [netOutput, hy', updateTwo, ht1] using e2
  have ha : z'.2 = (y (t + 1)).2 := by
    have : z'.2 + (y (t + 2)).1 = (y (t + 1)).2 + (y (t + 2)).1 := by
      simpa [netOutput, hy', updateTwo, ht2, ht3, show t + 1 + 1 = t + 2 by omega] using e3
    exact add_right_cancel this
  rw [hb, hm, ha]

/-- Splitting a price vector of `ℝ^{3L}` into its three blocks. -/
def block1 (p : Fin (L + L + L) → ℝ) : Fin L → ℝ := fun i => p (Fin.castAdd L (Fin.castAdd L i))
/-- The middle block. -/
def block2 (p : Fin (L + L + L) → ℝ) : Fin L → ℝ := fun i => p (Fin.castAdd L (Fin.natAdd L i))
/-- The last block. -/
def block3 (p : Fin (L + L + L) → ℝ) : Fin L → ℝ := fun i => p (Fin.natAdd (L + L) i)

theorem tripleVec_blocks (p : Fin (L + L + L) → ℝ) :
    tripleVec (block1 p) (block2 p) (block3 p) = p := by
  funext k
  refine Fin.addCases (fun j => ?_) (fun j => ?_) k
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp [tripleVec, block1]
    · simp only [tripleVec, Fin.append_left, Fin.append_right, block2]
  · simp only [tripleVec, Fin.append_right, block3]

/-- **MWG's claim** (p. 742): in the smooth case, short-run efficiency forces the normals at
consecutive dates to be compatible: `q_{a,t} = β q_{b,t+1}` for some `β > 0`. Proved from
`2`-efficiency, convexity, smoothness at `y_t` and `y_{t+1}`, and nonzero `q_{a,t}`,
`q_{b,t+1}`, by the second fundamental theorem of Chapter 5 on the two-date technology. -/
theorem proportional_normals_of_twoEfficient (hL : 0 < L) {Y : Set (ProdPlan (Fin L))}
    (hY : Convex ℝ Y) {y : ℕ → ProdPlan (Fin L)} (hy : TEfficient Y y 2) {q : ℕ → ProdPlan (Fin L)}
    (t : ℕ) (hs0 : SmoothAt Y (y t) (q t)) (hs1 : SmoothAt Y (y (t + 1)) (q (t + 1)))
    (ha0 : (q t).2 ≠ 0) (hb1 : (q (t + 1)).1 ≠ 0) :
    ∃ β : ℝ, 0 < β ∧ (q t).2 = β • (q (t + 1)).1 := by
  obtain ⟨p, -, hp0, -, hmax⟩ := MWG.Production.proposition_5_F_2 (by omega)
    (convex_twoDateSet hY) (efficient_twoDateSet hy t)
  set p1 := block1 p
  set p2 := block2 p
  set p3 := block3 p
  have hval : ∀ a b c : Fin L → ℝ, p ⬝ᵥ tripleVec a b c = p1 ⬝ᵥ a + p2 ⬝ᵥ b + p3 ⬝ᵥ c :=
    fun a b c => dotProduct_tripleVec p a b c
  -- `(p1, p2)` supports `Y` at `y_t`, `(p2, p3)` supports `Y` at `y_{t+1}`
  have hsup0 : ∀ z ∈ Y, planValue p1 p2 z ≤ planValue p1 p2 (y t) := by
    intro z hz
    have := hmax _ ⟨z, hz, y (t + 1), hy.1 (t + 1), rfl⟩
    rw [hval, hval] at this
    simp only [planValue, dotProduct_add] at this ⊢
    linarith
  have hsup1 : ∀ z ∈ Y, planValue p2 p3 z ≤ planValue p2 p3 (y (t + 1)) := by
    intro z hz
    have := hmax _ ⟨y t, hy.1 t, z, hz, rfl⟩
    rw [hval, hval] at this
    simp only [planValue, dotProduct_add] at this ⊢
    linarith
  have hp : p = tripleVec p1 p2 p3 := (tripleVec_blocks p).symm
  have h12 : ((p1, p2) : ProdPlan (Fin L)) ≠ 0 := by
    intro h
    have hp1 : p1 = 0 := congrArg Prod.fst h
    have hp2 : p2 = 0 := congrArg Prod.snd h
    have hp3 : p3 ≠ 0 := by
      intro hp3
      apply hp0
      rw [hp, hp1, hp2, hp3]
      funext k
      refine Fin.addCases (fun j => ?_) (fun j => ?_) k
      · refine Fin.addCases (fun i => ?_) (fun i => ?_) j
        · simp [tripleVec]
        · simp only [tripleVec, Fin.append_left, Fin.append_right, Pi.zero_apply]
      · simp only [tripleVec, Fin.append_right, Pi.zero_apply]
    obtain ⟨c, hc, hceq⟩ := hs1.2 (p2, p3) ⟨by
      intro h0; exact hp3 (congrArg Prod.snd h0), hsup1⟩
    have := congrArg Prod.fst hceq
    simp only [Prod.smul_fst] at this
    rw [hp2] at this
    exact hb1 (smul_eq_zero.1 this.symm |>.resolve_left hc.ne')
  have h23 : ((p2, p3) : ProdPlan (Fin L)) ≠ 0 := by
    intro h
    have hp2 : p2 = 0 := congrArg Prod.fst h
    have hp3 : p3 = 0 := congrArg Prod.snd h
    have hp1 : p1 ≠ 0 := by
      intro hp1
      apply hp0
      rw [hp, hp1, hp2, hp3]
      funext k
      refine Fin.addCases (fun j => ?_) (fun j => ?_) k
      · refine Fin.addCases (fun i => ?_) (fun i => ?_) j
        · simp [tripleVec]
        · simp only [tripleVec, Fin.append_left, Fin.append_right, Pi.zero_apply]
      · simp only [tripleVec, Fin.append_right, Pi.zero_apply]
    obtain ⟨c, hc, hceq⟩ := hs0.2 (p1, p2) ⟨by
      intro h0; exact hp1 (congrArg Prod.fst h0), hsup0⟩
    have := congrArg Prod.snd hceq
    simp only [Prod.smul_snd] at this
    rw [hp2] at this
    exact ha0 (smul_eq_zero.1 this.symm |>.resolve_left hc.ne')
  obtain ⟨c0, hc0, hc0eq⟩ := hs0.2 (p1, p2) ⟨h12, hsup0⟩
  obtain ⟨c1, hc1, hc1eq⟩ := hs1.2 (p2, p3) ⟨h23, hsup1⟩
  have e0 : p2 = c0 • (q t).2 := by
    have := congrArg Prod.snd hc0eq; simpa using this
  have e1 : p2 = c1 • (q (t + 1)).1 := by
    have := congrArg Prod.fst hc1eq; simpa using this
  refine ⟨c1 / c0, div_pos hc1 hc0, ?_⟩
  have : c0 • (q t).2 = c1 • (q (t + 1)).1 := e0.symm.trans e1
  calc (q t).2 = c0⁻¹ • (c0 • (q t).2) := by rw [smul_smul, inv_mul_cancel₀ hc0.ne', one_smul]
    _ = c0⁻¹ • (c1 • (q (t + 1)).1) := by rw [this]
    _ = (c1 / c0) • (q (t + 1)).1 := by rw [smul_smul, div_eq_inv_mul]

/-- **Existence of Malinvaud prices** in the smooth case (MWG, pp. 742-743): a `2`-efficient path
of a convex technology that is smooth along the path with strictly positive normals has a
strictly positive system of Malinvaud prices. -/
theorem malinvaud_of_twoEfficient (hL : 0 < L) {Y : Set (ProdPlan (Fin L))} (hY : Convex ℝ Y)
    {y : ℕ → ProdPlan (Fin L)} (hy : TEfficient Y y 2) {q : ℕ → ProdPlan (Fin L)}
    (hs : ∀ t, SmoothAt Y (y t) (q t)) (hqb : ∀ t, StrictPos (q t).1)
    (hqa : ∀ t, StrictPos (q t).2) :
    ∃ p : ℕ → Fin L → ℝ, (∀ t, StrictPos (p t)) ∧ MyopicProfitMax Y p y := by
  have hne : ∀ v : Fin L → ℝ, StrictPos v → v ≠ 0 := by
    intro v hv h
    have := hv ⟨0, hL⟩
    rw [h] at this
    exact lt_irrefl _ this
  have hβ : ∀ t, ∃ β : ℝ, 0 < β ∧ (q t).2 = β • (q (t + 1)).1 := fun t =>
    proportional_normals_of_twoEfficient hL hY hy t (hs t) (hs (t + 1)) (hne _ (hqa t))
      (hne _ (hqb (t + 1)))
  choose β hβpos hβeq using hβ
  exact ⟨normalPrices β q, normalPrices_strictPos hβpos hqb,
    malinvaud_of_proportional_normals hy.1 (fun t => (hs t).1) hβpos hβeq⟩

/-- **Exercise 20.C.5(b)** (MWG, p. 783): for a convex technology that is smooth along the path
with strictly positive outward normals, `2`-efficiency implies `T`-efficiency for all `T < ∞`. -/
theorem exercise_20_C_5b (hL : 0 < L) {Y : Set (ProdPlan (Fin L))} (hY : Convex ℝ Y)
    {y : ℕ → ProdPlan (Fin L)} (hy : TEfficient Y y 2) {q : ℕ → ProdPlan (Fin L)}
    (hs : ∀ t, SmoothAt Y (y t) (q t)) (hqb : ∀ t, StrictPos (q t).1)
    (hqa : ∀ t, StrictPos (q t).2) (T : ℕ) : TEfficient Y y T := by
  obtain ⟨p, hp, hmyopic⟩ := malinvaud_of_twoEfficient hL hY hy hs hqb hqa
  exact exercise_20_C_5a hp hmyopic T

end MWG.EquilibriumTime
