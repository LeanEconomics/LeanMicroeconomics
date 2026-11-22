/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGEquilibriumUncertainty.SequentialExamples
import MWGClassicalDemand.AppendixMG
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Asset markets and arbitrage (MWG Section 19.E, pp. 699-704)

* **Definition 19.E.1**: an asset is a return vector `r ∈ ℝ^S`; an asset structure is an `S × K`
  return matrix `R` whose `k`-th column is `r_k` (`returnMatrix`).
* **Example 19.E.1**: the riskless asset, Arrow securities (whose return matrix is the identity,
  as in Example 19.E.4) and the asset paying `1` and an extra unit in even-labelled states.
* **Example 19.E.2**: call options `r(c)_s = max{0, r_s - c}` and the three printed return vectors.
* **Definition 19.E.2** (in `Sequential`), with the normalization `p_{gs} = 1` the budget set
  `B_i(p, q, R)` of p. 701 (`budgetSet_normalized`).
* **Proposition 19.E.1, Proof 1**: arbitrage-free prices (`ArbitrageFree`), their positivity
  (p. 702), **Lemma 19.E.1** by the separating hyperplane theorem (M.G.2, from Chapter 3) applied
  as in the book to `V = {Rz : q·z = 0}` and `ℝ^S_+ \ {0}`, restricted to the states with a nonzero
  row of `R` (footnote 17); equilibrium prices are arbitrage free when some consumer has strongly
  monotone preferences (`radner_arbitrageFree`, `proposition_19_E_1`).
* **Example 19.E.3**: with a riskless asset of price 1, `min_s r_{sk} ≤ q_k ≤ max_s r_{sk}`.
* **Definition 19.E.3** (`IsComplete`: `rank R = S`), **Example 19.E.4** (the identity and a
  triangular `3 × 3` matrix), **Example 19.E.5** (spanning through options on `r = (4, 3, 2, 1)`;
  if `r_s = r_{s'}` no option structure on `r` is complete), and **Exercise 19.E.2** (a primary
  asset with distinct positive returns generates a complete structure by options).
-/

namespace MWG.EquilibriumUncertainty

open Matrix

variable {S L K : ℕ}

/-- **Definition 19.E.1** (MWG, p. 699). A unit of an asset is a title to `r_s` units of good `g`
(the numeraire) at `t = 1` if state `s` occurs; the asset is its return vector `r ∈ ℝ^S`. -/
abbrev ReturnVector (S : ℕ) := Fin S → ℝ

/-- **p. 701**. The `S × K` return matrix whose `k`-th column is the return vector `r_k`. -/
def returnMatrix (r : Fin K → ReturnVector S) : Matrix (Fin S) (Fin K) ℝ :=
  Matrix.of fun s k => r k s

/-- **Example 19.E.1(ii)** (MWG, p. 700). The Arrow security for state `s`: one unit of good `g` if
and only if `s` occurs. -/
def arrowSecurity (s : Fin S) : ReturnVector S := Pi.single s 1

/-- **Examples 19.E.1(ii) and 19.E.4** (MWG, pp. 700, 704). The return matrix of the `S` Arrow
securities is the `S × S` identity matrix; it has rank `S` (the canonical complete structure). -/
theorem example_19_E_1_arrow : returnMatrix (arrowSecurity (S := S)) = 1 := by
  ext s k
  simp only [returnMatrix, arrowSecurity, Matrix.of_apply, Matrix.one_apply, Pi.single_apply]

/-- **Example 19.E.1** (MWG, p. 700). (i) The riskless asset `(1, …, 1)`; (iii) the asset paying one
unit unconditionally and another unit in even-labelled states (states are counted from `0`, so the
book's even labels `2, 4, …` are the odd indices). -/
def example19E1iii : ReturnVector S := fun s => if s.val % 2 = 1 then 2 else 1

/-- **Example 19.E.1(iii)** (MWG, p. 700): it is the riskless asset plus the sum of the Arrow
securities of the even-labelled states. -/
theorem example_19_E_1_iii (s : Fin S) :
    example19E1iii s = 1 + ∑ t ∈ Finset.univ.filter (fun t : Fin S => t.val % 2 = 1),
      arrowSecurity t s := by
  have hsum : ∑ t ∈ Finset.univ.filter (fun t : Fin S => t.val % 2 = 1), arrowSecurity t s =
      if s.val % 2 = 1 then 1 else 0 := by
    rw [Finset.sum_filter, Finset.sum_eq_single s]
    · simp [arrowSecurity]
    · intro b _ hb; simp [arrowSecurity, Ne.symm hb]
    · simp
  rw [hsum]; unfold example19E1iii; split_ifs <;> norm_num

/-- **Example 19.E.2** (MWG, p. 700). The European call option with strike price `c` on the primary
asset `r`: `r(c)_s = max{0, r_s - c}`. -/
def callOption (r : ReturnVector S) (c : ℝ) : ReturnVector S := fun s => max 0 (r s - c)

/-- The primary asset `r = (4, 3, 2, 1)` of Examples 19.E.2 and 19.E.5. -/
def primary4321 : ReturnVector 4 := ![4, 3, 2, 1]

/-- **Example 19.E.2** (MWG, p. 700). For `r = (4, 3, 2, 1)`: `r(3.5) = (.5, 0, 0, 0)`,
`r(2.5) = (1.5, .5, 0, 0)` and `r(1.5) = (2.5, 1.5, .5, 0)`. -/
theorem example_19_E_2 :
    callOption primary4321 3.5 = ![0.5, 0, 0, 0] ∧ callOption primary4321 2.5 = ![1.5, 0.5, 0, 0] ∧
      callOption primary4321 1.5 = ![2.5, 1.5, 0.5, 0] := by
  refine ⟨?_, ?_, ?_⟩ <;> funext s <;> fin_cases s <;>
    simp [callOption, primary4321] <;> norm_num

/-- **p. 701**. With the normalization `p_{gs} = 1`, the budget set of Definition 19.E.2 is
`B_i(p, q, R) = {x ≥ 0 : ∃ z, q·z ≤ 0 and (p_s·(x_s - ω_s))_s ≤ R z}`. -/
theorem budgetSet_normalized (g : Fin L) (R : Matrix (Fin S) (Fin K) ℝ) (q : Fin K → ℝ)
    {p : CVec S L} (hp : ∀ s, p s g = 1) (ω x : CVec S L) (z : Fin K → ℝ) :
    radnerFeasible g R q p ω x z ↔
      NonnegC x ∧ q ⬝ᵥ z ≤ 0 ∧ ∀ s, p s ⬝ᵥ (x s - ω s) ≤ (R *ᵥ z) s := by
  unfold radnerFeasible
  refine and_congr Iff.rfl (and_congr Iff.rfl (forall_congr' fun s => ?_))
  rw [hp s, one_mul, dotProduct_sub]
  constructor <;> intro h <;> linarith

/-! ## Arbitrage and Lemma 19.E.1 -/

/-- **Proof 1 of Proposition 19.E.1** (MWG, p. 702). Asset prices `q` are arbitrage free if no
portfolio `z` has `q·z ≤ 0`, `Rz ≥ 0` and `Rz ≠ 0`. -/
def ArbitrageFree (R : Matrix (Fin S) (Fin K) ℝ) (q : Fin K → ℝ) : Prop :=
  ¬ ∃ z : Fin K → ℝ, q ⬝ᵥ z ≤ 0 ∧ (∀ s, 0 ≤ (R *ᵥ z) s) ∧ R *ᵥ z ≠ 0

/-- The standing assumption of Proposition 19.E.1: every return vector is nonnegative and
nonzero. -/
def NonnegNonzeroReturns (R : Matrix (Fin S) (Fin K) ℝ) : Prop :=
  (∀ s k, 0 ≤ R s k) ∧ ∀ k, ∃ s, R s k ≠ 0

theorem mulVec_single (R : Matrix (Fin S) (Fin K) ℝ) (k : Fin K) (s : Fin S) :
    (R *ᵥ Pi.single k 1) s = R s k := by
  simp [mulVec, dotProduct, Pi.single_apply]

/-- **Proof of Lemma 19.E.1** (MWG, p. 702). With nonnegative nonzero returns, an arbitrage-free
price vector is strictly positive. -/
theorem ArbitrageFree.pos {R : Matrix (Fin S) (Fin K) ℝ} (hR : NonnegNonzeroReturns R)
    {q : Fin K → ℝ} (h : ArbitrageFree R q) (k : Fin K) : 0 < q k := by
  by_contra hle
  push Not at hle
  refine h ⟨Pi.single k 1, by simpa [dotProduct_single] using hle, fun s => ?_, fun h0 => ?_⟩
  · rw [mulVec_single]; exact hR.1 s k
  · obtain ⟨s, hs⟩ := hR.2 k
    have := congrFun h0 s
    rw [mulVec_single] at this
    exact hs this

/-- If `q ≠ 0` and `a·d = 0` whenever `q·d = 0`, then `a` is a multiple of `q`. -/
theorem eq_smul_of_ker_le {n : Type*} [Fintype n] {a q : n → ℝ} (hq : q ≠ 0)
    (h : ∀ d, q ⬝ᵥ d = 0 → a ⬝ᵥ d = 0) : a = ((a ⬝ᵥ q) / (q ⬝ᵥ q)) • q := by
  classical
  have hqq : q ⬝ᵥ q ≠ 0 := fun h0 => hq (dotProduct_self_eq_zero.mp h0)
  have hd : ∀ d, a ⬝ᵥ d = (a ⬝ᵥ q) / (q ⬝ᵥ q) * (q ⬝ᵥ d) := by
    intro d
    have h0 := h (d - ((q ⬝ᵥ d) / (q ⬝ᵥ q)) • q) (by
      rw [dotProduct_sub, dotProduct_smul, smul_eq_mul, div_mul_cancel₀ _ hqq, sub_self])
    rw [dotProduct_sub, dotProduct_smul, smul_eq_mul, sub_eq_zero] at h0
    rw [h0, dotProduct_comm a q]
    field_simp
  funext k
  have := hd (Pi.single k 1)
  simpa [dotProduct_single] using this

/-- The separating hyperplane theorem (Theorem M.G.2(ii), Chapter 3) for vectors indexed by a
nonempty finite type. -/
theorem separation_fintype {T : Type*} [Fintype T] [Nonempty T] {A B : Set (T → ℝ)}
    (hA : Convex ℝ A) (hB : Convex ℝ B) (hAne : A.Nonempty) (hBne : B.Nonempty)
    (hdisj : Disjoint A B) :
    ∃ p : T → ℝ, p ≠ 0 ∧ ∃ c : ℝ, (∀ x ∈ A, c ≤ p ⬝ᵥ x) ∧ ∀ y ∈ B, p ⬝ᵥ y ≤ c := by
  set e := Fintype.equivFin T
  have hN : 0 < Fintype.card T := Fintype.card_pos
  let φ : (T → ℝ) → (Fin (Fintype.card T) → ℝ) := fun v j => v (e.symm j)
  have hφlin : ∀ (a b : ℝ) (v w : T → ℝ), φ (a • v + b • w) = a • φ v + b • φ w :=
    fun _ _ _ _ => rfl
  have hφinj : Function.Injective φ := fun v w h => funext fun t => by
    have := congrFun h (e t); simpa [φ] using this
  have hconv : ∀ C : Set (T → ℝ), Convex ℝ C → Convex ℝ (φ '' C) := by
    rintro C hC _ ⟨v, hv, rfl⟩ _ ⟨w, hw, rfl⟩ a b ha hb hab
    exact ⟨a • v + b • w, hC hv hw ha hb hab, hφlin a b v w⟩
  obtain ⟨p, hp, c, hcA, hcB⟩ := MWG.ClassicalDemand.theorem_M_G_2_ii hN (hconv A hA)
    (hconv B hB) (hAne.image φ) (hBne.image φ) (by
      rw [Set.disjoint_left]
      rintro _ ⟨v, hv, rfl⟩ ⟨w, hw, hvw⟩
      exact Set.disjoint_left.mp hdisj hv (hφinj hvw ▸ hw))
  have hdot : ∀ v : T → ℝ, p ⬝ᵥ φ v = (fun t => p (e t)) ⬝ᵥ v := by
    intro v
    simp only [dotProduct, φ]
    exact (e.sum_comp fun j => p j * v (e.symm j)).symm.trans
      (Finset.sum_congr rfl fun t _ => by simp)
  refine ⟨fun t => p (e t), fun h0 => hp (funext fun j => ?_), c, fun x hx => ?_,
    fun y hy => ?_⟩
  · have := congrFun h0 (e.symm j); simpa using this
  · rw [← hdot]; exact hcA _ ⟨x, hx, rfl⟩
  · rw [← hdot]; exact hcB _ ⟨y, hy, rfl⟩

/-- **Lemma 19.E.1** (MWG, p. 702), with the standing assumption of Proposition 19.E.1 (returns
nonnegative and nonzero). If `q` is arbitrage free, there are multipliers `μ ≥ 0` with
`q_k = ∑_s μ_s r_{sk}` (`qᵀ = μ·R`). The proof is the book's: separate `V = {Rz : q·z = 0}` from
`ℝ^S_+ \ {0}`, on the states whose row of `R` is nonzero (footnote 17); the normal `μ'` is
nonnegative, vanishes on `V`, and `q` is proportional to `μ'·R`. -/
theorem lemma_19_E_1 {R : Matrix (Fin S) (Fin K) ℝ} (hR : NonnegNonzeroReturns R)
    {q : Fin K → ℝ} (h : ArbitrageFree R q) :
    ∃ μ : Fin S → ℝ, (∀ s, 0 ≤ μ s) ∧ ∀ k, q k = ∑ s, μ s * R s k := by
  classical
  rcases isEmpty_or_nonempty (Fin K) with hK | ⟨⟨k₀⟩⟩
  · exact ⟨0, fun _ => le_rfl, fun k => isEmptyElim k⟩
  have hqpos := h.pos hR
  -- the states with a nonzero row
  set T := {s : Fin S // ∃ k, R s k ≠ 0} with hT
  obtain ⟨s₀, hs₀⟩ := hR.2 k₀
  have hTne : Nonempty T := ⟨⟨s₀, k₀, hs₀⟩⟩
  have hzero : ∀ s, (¬ ∃ k, R s k ≠ 0) → ∀ z : Fin K → ℝ, (R *ᵥ z) s = 0 := by
    intro s hs z
    push Not at hs
    simp [mulVec, dotProduct, hs]
  set V : Set (T → ℝ) := {v | ∃ z, q ⬝ᵥ z = 0 ∧ ∀ t : T, v t = (R *ᵥ z) t.1} with hV
  set P : Set (T → ℝ) := {y | (∀ t, 0 ≤ y t) ∧ y ≠ 0} with hP
  have hVconv : Convex ℝ V := by
    intro v hv w hw a b _ _ _
    obtain ⟨z, hz, hvz⟩ := hv
    obtain ⟨z', hz', hwz⟩ := hw
    refine ⟨a • z + b • z', ?_, fun t => ?_⟩
    · rw [dotProduct_add, dotProduct_smul, dotProduct_smul, hz, hz']; simp
    · simp [hvz, hwz, mulVec_add, mulVec_smul]
  have hPconv : Convex ℝ P := by
    intro y hy w hw a b ha hb hab
    obtain ⟨hy, hy0⟩ := hy
    obtain ⟨hw, hw0⟩ := hw
    refine ⟨fun t => ?_, fun h0 => ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact add_nonneg (mul_nonneg ha (hy t)) (mul_nonneg hb (hw t))
    · rcases ha.lt_or_eq with ha' | ha'
      · apply hy0
        funext t
        have h1 := congrFun h0 t
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1
        have := mul_nonneg hb (hw t)
        have h2 : a * y t = 0 := by linarith [mul_nonneg ha (hy t)]
        rcases mul_eq_zero.mp h2 with h3 | h3
        · exact absurd h3 ha'.ne'
        · simpa using h3
      · subst ha'
        have hb1 : b = 1 := by linarith
        subst hb1
        apply hw0; simpa using h0
  have hdisj : Disjoint P V := by
    rw [Set.disjoint_left]
    rintro y ⟨hy, hy0⟩ ⟨z, hz, hzy⟩
    refine h ⟨z, hz.le, fun s => ?_, fun h0 => hy0 (funext fun t => by
      rw [hzy t, h0]; rfl)⟩
    by_cases hs : ∃ k, R s k ≠ 0
    · have := hy ⟨s, hs⟩; rwa [hzy] at this
    · rw [hzero s hs]
  obtain ⟨μ', hμ'0, c, hcP, hcV⟩ := separation_fintype hPconv hVconv
    ⟨fun _ => 1, fun _ => zero_le_one, fun h0 => by
      have := congrFun h0 (Classical.arbitrary T); simp at this⟩
    ⟨0, 0, by simp, fun t => by simp⟩ hdisj
  -- `c ≥ 0` since `0 ∈ V`, and `μ'` vanishes on `V`
  have hc0 : 0 ≤ c := by simpa using hcV 0 ⟨0, by simp, fun t => by simp⟩
  have hVzero : ∀ z, q ⬝ᵥ z = 0 → μ' ⬝ᵥ (fun t : T => (R *ᵥ z) t.1) = 0 := by
    intro z hz
    have hmem : ∀ a : ℝ, (fun t : T => (R *ᵥ (a • z)) t.1) ∈ V :=
      fun a => ⟨a • z, by rw [dotProduct_smul, hz, smul_zero], fun t => rfl⟩
    have hlin : ∀ a : ℝ, μ' ⬝ᵥ (fun t : T => (R *ᵥ (a • z)) t.1) =
        a * μ' ⬝ᵥ (fun t : T => (R *ᵥ z) t.1) := fun a => by
      simp [mulVec_smul, dotProduct, Finset.mul_sum, mul_left_comm]
    by_contra hne
    have h1 := hcV _ (hmem ((c + 1) / μ' ⬝ᵥ (fun t : T => (R *ᵥ z) t.1)))
    rw [hlin, div_mul_cancel₀ _ hne] at h1
    linarith
  -- `μ' ≥ 0`
  have hμ'nn : ∀ t, 0 ≤ μ' t := by
    intro t
    by_contra hneg
    push Not at hneg
    have := hcP (Pi.single t 1) ⟨fun t' => by simp [Pi.single_apply]; split_ifs <;> norm_num,
      fun h0 => by have := congrFun h0 t; simp at this⟩
    simp [dotProduct_single] at this
    linarith
  -- `a = μ'·R`
  set μ'' : Fin S → ℝ := fun s => if hs : ∃ k, R s k ≠ 0 then μ' ⟨s, hs⟩ else 0 with hμ''
  have hμ''nn : ∀ s, 0 ≤ μ'' s := fun s => by
    simp only [hμ'']; split_ifs <;> simp [hμ'nn]
  set a : Fin K → ℝ := fun k => ∑ s, μ'' s * R s k with ha
  have hadot : ∀ z, a ⬝ᵥ z = μ' ⬝ᵥ (fun t : T => (R *ᵥ z) t.1) := by
    intro z
    have e1 : a ⬝ᵥ z = ∑ s, μ'' s * (R *ᵥ z) s := by
      simp only [ha, dotProduct, mulVec, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun k _ => by ring
    rw [e1, ← Fintype.sum_subtype_add_sum_subtype (fun s => ∃ k, R s k ≠ 0)]
    have h2 : ∑ s : {s // ¬ ∃ k, R s k ≠ 0}, μ'' s.1 * (R *ᵥ z) s.1 = 0 :=
      Finset.sum_eq_zero fun s _ => by simp [hμ'', s.2]
    rw [h2, add_zero]
    simp only [dotProduct]
    exact Finset.sum_congr rfl fun t _ => by simp [hμ'', t.2]
  have hker : ∀ d, q ⬝ᵥ d = 0 → a ⬝ᵥ d = 0 := fun d hd => by rw [hadot]; exact hVzero d hd
  have hq0 : q ≠ 0 := fun h0 => by have := hqpos k₀; rw [h0] at this; simp at this
  have hprop := eq_smul_of_ker_le hq0 hker
  set β := (a ⬝ᵥ q) / (q ⬝ᵥ q) with hβ
  -- `a ≠ 0`, so `β > 0`
  obtain ⟨t₁, ht₁⟩ : ∃ t, 0 < μ' t := by
    by_contra hall
    push Not at hall
    exact hμ'0 (funext fun t => le_antisymm (hall t) (hμ'nn t))
  obtain ⟨k₁, hk₁⟩ := t₁.2
  have hak : 0 < a k₁ := by
    have hpos : 0 < μ'' t₁.1 * R t₁.1 k₁ := by
      have hR1 : 0 < R t₁.1 k₁ := lt_of_le_of_ne (hR.1 _ _) (Ne.symm hk₁)
      have e : μ'' t₁.1 = μ' t₁ := by simp [hμ'', t₁.2]
      rw [e]
      exact mul_pos ht₁ hR1
    calc 0 < μ'' t₁.1 * R t₁.1 k₁ := hpos
      _ ≤ ∑ s, μ'' s * R s k₁ := Finset.single_le_sum (f := fun s => μ'' s * R s k₁)
          (fun s _ => mul_nonneg (hμ''nn s) (hR.1 s k₁)) (Finset.mem_univ _)
  have hβpos : 0 < β := by
    have := congrFun hprop k₁
    simp only [Pi.smul_apply, smul_eq_mul] at this
    by_contra hb
    push Not at hb
    have : a k₁ ≤ 0 := by rw [this]; exact mul_nonpos_of_nonpos_of_nonneg hb (hqpos k₁).le
    linarith
  refine ⟨fun s => μ'' s / β, fun s => div_nonneg (hμ''nn s) hβpos.le, fun k => ?_⟩
  have := congrFun hprop k
  simp only [Pi.smul_apply, smul_eq_mul, ha] at this
  have e : ∑ s, μ'' s / β * R s k = (∑ s, μ'' s * R s k) / β := by
    rw [Finset.sum_div]; exact Finset.sum_congr rfl fun s _ => by ring
  rw [e, this]; field_simp

/-! ## Proposition 19.E.1 -/

/-- **Proof 1 of Proposition 19.E.1** (MWG, p. 702). If some consumer's preferences are strongly
monotone, equilibrium asset prices are arbitrage free: adding an arbitrage portfolio to his
portfolio and consuming the extra returns in good `g` would be affordable and strictly better. -/
theorem radner_arbitrageFree {ι : Type*} [Fintype ι] (g : Fin L) {R : Matrix (Fin S) (Fin K) ℝ}
    {U : ι → CVec S L → ℝ} {ω x : ι → CVec S L} {q : Fin K → ℝ} {p : CVec S L}
    {z : ι → Fin K → ℝ} (h : IsRadnerEqm g R U ω q p x z) (i : ι)
    (hU : StronglyMonotoneC (U i)) : ArbitrageFree R q := by
  classical
  rintro ⟨w, hqw, hnn, hne⟩
  set δ : CVec S L := fun s l => if l = g then (R *ᵥ w) s else 0 with hδ
  have hδdot : ∀ s, p s ⬝ᵥ δ s = p s g * (R *ᵥ w) s := fun s => by
    simp [hδ, dotProduct]
  obtain ⟨⟨hx, hqz, hsp⟩, hopt⟩ := h.1 i
  have hle : x i ≤ x i + δ := fun s l => by
    simp only [Pi.add_apply, hδ]; split_ifs <;> linarith [hnn s]
  have hne' : x i ≠ x i + δ := by
    intro h0
    apply hne
    funext s
    have := congrFun (congrFun h0 s) g
    simp [hδ] at this
    simpa using this
  have hfeas : radnerFeasible g R q p (ω i) (x i + δ) (z i + w) := by
    refine ⟨fun s l => (hx s l).trans (hle s l), ?_, fun s => ?_⟩
    · rw [dotProduct_add]; linarith
    · rw [Pi.add_apply, dotProduct_add, hδdot, mulVec_add, Pi.add_apply, mul_add]
      linarith [hsp s]
  linarith [hopt _ _ hfeas, hU _ _ hx hle hne']

/-- **Proposition 19.E.1** (MWG, p. 701). Suppose every return vector is nonnegative and nonzero,
and some consumer's preferences are strongly monotone. Then for the asset prices `q` of any Radner
equilibrium there are multipliers `μ ≥ 0` with `q_k = ∑_s μ_s r_{sk}` for every asset (Proof 1:
`radner_arbitrageFree` and `lemma_19_E_1`). -/
theorem proposition_19_E_1 {ι : Type*} [Fintype ι] (g : Fin L) {R : Matrix (Fin S) (Fin K) ℝ}
    (hR : NonnegNonzeroReturns R) {U : ι → CVec S L → ℝ} {ω x : ι → CVec S L} {q : Fin K → ℝ}
    {p : CVec S L} {z : ι → Fin K → ℝ} (h : IsRadnerEqm g R U ω q p x z) (i : ι)
    (hU : StronglyMonotoneC (U i)) :
    ∃ μ : Fin S → ℝ, (∀ s, 0 ≤ μ s) ∧ ∀ k, q k = ∑ s, μ s * R s k :=
  lemma_19_E_1 hR (radner_arbitrageFree g h i hU)

/-- **Example 19.E.3** (MWG, p. 704). If asset `k₁` is riskless (`r_{k₁} = (1, …, 1)`) with price
`1`, the multipliers of Proposition 19.E.1 sum to one, and every asset price lies between the
smallest and the largest return of the asset: `min_s r_{sk} ≤ q_k ≤ max_s r_{sk}`. -/
theorem example_19_E_3 {R : Matrix (Fin S) (Fin K) ℝ} {q : Fin K → ℝ} {μ : Fin S → ℝ}
    (hμ : ∀ s, 0 ≤ μ s) (hq : ∀ k, q k = ∑ s, μ s * R s k) {k₁ : Fin K} (hsafe : ∀ s, R s k₁ = 1)
    (hq1 : q k₁ = 1) (k : Fin K) :
    ∑ s, μ s = 1 ∧ (∀ m, (∀ s, m ≤ R s k) → m ≤ q k) ∧ ∀ M, (∀ s, R s k ≤ M) → q k ≤ M := by
  have hsum : ∑ s, μ s = 1 := by
    have := hq k₁; simp only [hsafe, mul_one] at this; linarith
  refine ⟨hsum, fun m hm => ?_, fun M hM => ?_⟩
  · rw [hq k]
    calc m = ∑ s, μ s * m := by rw [← Finset.sum_mul, hsum, one_mul]
      _ ≤ ∑ s, μ s * R s k := Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hm s) (hμ s)
  · rw [hq k]
    calc ∑ s, μ s * R s k ≤ ∑ s, μ s * M :=
          Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hM s) (hμ s)
      _ = M := by rw [← Finset.sum_mul, hsum, one_mul]

/-! ## Complete asset structures -/

/-- **Definition 19.E.3** (MWG, p. 704). An asset structure with return matrix `R` is complete if
`rank R = S`. -/
def IsComplete (R : Matrix (Fin S) (Fin K) ℝ) : Prop := R.rank = S

/-- **p. 704**. An asset structure is complete iff every wealth transfer `v ∈ ℝ^S` across states is
spanned: `v = Rz` for some portfolio `z`. -/
theorem isComplete_iff_surjective (R : Matrix (Fin S) (Fin K) ℝ) :
    IsComplete R ↔ ∀ v : Fin S → ℝ, ∃ z, R *ᵥ z = v := by
  unfold IsComplete Matrix.rank
  have hS : Module.finrank ℝ (Fin S → ℝ) = S := Module.finrank_fin_fun ℝ
  constructor
  · intro h v
    have htop : LinearMap.range R.mulVecLin = ⊤ :=
      Submodule.eq_top_iff_finrank_eq.mpr (by rw [h, hS])
    obtain ⟨z, hz⟩ := LinearMap.range_eq_top.mp htop v
    exact ⟨z, by simpa [Matrix.mulVecLin_apply] using hz⟩
  · intro h
    have htop : LinearMap.range R.mulVecLin = ⊤ := LinearMap.range_eq_top.mpr fun v => by
      obtain ⟨z, hz⟩ := h v; exact ⟨z, by simpa [Matrix.mulVecLin_apply] using hz⟩
    rw [htop, finrank_top, hS]

/-- **Example 19.E.4** (MWG, p. 704). The `S × S` identity (the Arrow securities) is complete. -/
theorem example_19_E_4_identity : IsComplete (1 : Matrix (Fin S) (Fin S) ℝ) := by
  unfold IsComplete
  rw [Matrix.rank_one, Fintype.card_fin]

/-- **Example 19.E.4** (MWG, p. 704). The return matrix with rows `(1, 0, 0)`, `(1, 1, 0)`,
`(1, 1, 1)` has rank `3`, the number of states. -/
theorem example_19_E_4 : IsComplete !![(1 : ℝ), 0, 0; 1, 1, 0; 1, 1, 1] := by
  unfold IsComplete
  rw [Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).mpr ?_), Fintype.card_fin]
  rw [Matrix.det_fin_three]
  simp

/-- **Example 19.E.5** (MWG, p. 704). The primary asset `r = (4, 3, 2, 1)` with the options of
strike prices `3.5`, `2.5`, `1.5`: the return matrix (columns `r(3.5), r(2.5), r(1.5), r`). -/
def optionStructure19E5 : Matrix (Fin 4) (Fin 4) ℝ :=
  returnMatrix ![callOption primary4321 3.5, callOption primary4321 2.5,
    callOption primary4321 1.5, primary4321]

/-- **Example 19.E.5** (MWG, p. 704). All entries of the return matrix below the diagonal are
zero, and the structure is complete. -/
theorem example_19_E_5 :
    optionStructure19E5.IsUpperTriangular ∧ IsComplete optionStructure19E5 := by
  have hM : optionStructure19E5 =
      !![0.5, 1.5, 2.5, 4; 0, 0.5, 1.5, 3; 0, 0, 0.5, 2; 0, 0, 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [optionStructure19E5, returnMatrix, callOption, primary4321] <;> norm_num
  have hut : optionStructure19E5.IsUpperTriangular := by
    rw [hM]
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  refine ⟨hut, ?_⟩
  unfold IsComplete
  rw [Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).mpr ?_), Fintype.card_fin]
  rw [Matrix.det_of_isUpperTriangular hut, hM]
  simp [Fin.prod_univ_four]
  norm_num

/-- **Example 19.E.5** (MWG, p. 704). If two distinct states `s ≠ s'` are not distinguished by any
asset (`r_{sk} = r_{s'k}` for every column), the asset structure is not complete. -/
theorem not_complete_of_eq_rows {R : Matrix (Fin S) (Fin K) ℝ} {s s' : Fin S} (hss : s ≠ s')
    (h : ∀ k, R s k = R s' k) : ¬ IsComplete R := by
  classical
  rw [isComplete_iff_surjective]
  intro hsurj
  obtain ⟨z, hz⟩ := hsurj (Pi.single s 1)
  have h1 := congrFun hz s
  have h2 := congrFun hz s'
  simp only [mulVec, dotProduct, h] at h1 h2
  rw [h1] at h2
  simp [hss.symm] at h2

/-- **Example 19.E.5** (MWG, p. 704). If the primary asset has `r_s = r_{s'}` for some `s ≠ s'`, no
asset structure made of `r` and options on `r` is complete. -/
theorem example_19_E_5_not_separating {r : ReturnVector S} {s s' : Fin S} (hss : s ≠ s')
    (hr : r s = r s') {c : Fin K → ℝ} :
    ¬ IsComplete (returnMatrix (Fin.cons r fun k => callOption r (c k))) :=
  not_complete_of_eq_rows hss fun k => by
    refine Fin.cases ?_ (fun k => ?_) k
    · simp [returnMatrix, hr]
    · simp [returnMatrix, callOption, hr]

/-- Piecewise-linear interpolation by options: on a finite set `A` of positive reals, every
function is a combination of the identity and the call payoffs `max{0, · - c}`, `c ∈ A`. -/
theorem interpolate_by_options (A : Finset ℝ) (hA : ∀ x ∈ A, 0 < x) (f : ℝ → ℝ) :
    ∃ (a₀ : ℝ) (a : ℝ → ℝ), ∀ x ∈ A, f x = a₀ * x + ∑ c ∈ A, a c * max 0 (x - c) := by
  classical
  induction A using Finset.induction_on_max generalizing f with
  | empty => exact ⟨0, 0, fun x hx => absurd hx (Finset.notMem_empty x)⟩
  | insert M A hlt ih =>
    have hM : 0 < M := hA M (Finset.mem_insert_self _ _)
    have hMA : M ∉ A := fun h => lt_irrefl M (hlt M h)
    obtain ⟨a₀, a, ha⟩ := ih (fun x hx => hA x (Finset.mem_insert_of_mem hx)) f
    rcases A.eq_empty_or_nonempty with hAe | hne
    · subst hAe
      refine ⟨f M / M, 0, fun x hx => ?_⟩
      simp only [Finset.mem_insert, Finset.notMem_empty, or_false] at hx
      subst hx
      simp; field_simp
    · set c := A.max' hne with hc
      have hcA : c ∈ A := A.max'_mem hne
      have hcM : c < M := hlt c hcA
      set gM := a₀ * M + ∑ d ∈ A, a d * max 0 (M - d) with hgM
      set δ := (f M - gM) / (M - c) with hδ
      have key : ∀ y, ∑ d ∈ A, Function.update a c (a c + δ) d * max 0 (y - d) =
          ∑ d ∈ A, a d * max 0 (y - d) + δ * max 0 (y - c) := by
        intro y
        rw [← Finset.add_sum_erase _ _ hcA, ← Finset.add_sum_erase _ _ hcA,
          Function.update_self]
        rw [Finset.sum_congr rfl fun d hd => by
          rw [Function.update_of_ne (Finset.ne_of_mem_erase hd)]]
        ring
      refine ⟨a₀, Function.update a c (a c + δ), fun x hx => ?_⟩
      rw [Finset.sum_insert hMA, key]
      rcases Finset.mem_insert.mp hx with rfl | hxA
      · have hmax : max 0 (x - c) = x - c := max_eq_right (by linarith)
        simp only [sub_self, max_self, mul_zero, zero_add, hmax]
        rw [hδ]
        field_simp [(sub_pos.mpr hcM).ne']
        rw [hgM]; ring
      · have hxc : x ≤ c := A.le_max' x hxA
        have hxM : x < M := hlt x hxA
        have h1 : max 0 (x - M) = 0 := max_eq_left (by linarith)
        have h2 : max 0 (x - c) = 0 := max_eq_left (by linarith)
        rw [h1, h2, ha x hxA]
        ring

/-- **Exercise 19.E.2** (MWG, p. 727). If the primary asset `r` separates states (`r_s ≠ r_{s'}`
for `s ≠ s'`) and `r_s > 0`, the structure made of `r` and the call options on `r` with strike
prices `r_1, …, r_S` is complete. -/
theorem exercise_19_E_2 {r : ReturnVector S} (hsep : Function.Injective r) (hpos : ∀ s, 0 < r s) :
    IsComplete (returnMatrix (Fin.cons r fun t => callOption r (r t))) := by
  classical
  rw [isComplete_iff_surjective]
  intro v
  rcases isEmpty_or_nonempty (Fin S) with hS | hS
  · exact ⟨0, funext fun s => isEmptyElim s⟩
  obtain ⟨a₀, a, ha⟩ := interpolate_by_options (Finset.univ.image r)
    (fun x hx => by obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hx; exact hpos s)
    (fun y => v (Function.invFun r y))
  refine ⟨Fin.cons a₀ fun t => a (r t), funext fun s => ?_⟩
  have := ha (r s) (Finset.mem_image_of_mem _ (Finset.mem_univ s))
  rw [Function.leftInverse_invFun hsep s, Finset.sum_image fun x _ y _ h => hsep h] at this
  rw [this]
  simp only [mulVec, dotProduct, Fin.sum_univ_succ, returnMatrix, Matrix.of_apply,
    Fin.cons_zero, Fin.cons_succ, callOption]
  rw [Finset.sum_congr rfl fun t _ => mul_comm (max 0 (r s - r t)) (a (r t))]
  ring

end MWG.EquilibriumUncertainty
