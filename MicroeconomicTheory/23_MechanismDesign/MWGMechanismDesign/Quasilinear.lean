/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGMechanismDesign.GibbardSatterthwaite
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Quasilinear environments: Groves-Clarke mechanisms

MWG, Section 23.C, pp. 876-881.

An alternative is `x = (k, t₁, …, t_I)` with a project `k ∈ K` and transfers `tᵢ ∈ ℝ`; agent
`i` of type `θᵢ` has utility `uᵢ(x, θᵢ) = vᵢ(k, θᵢ) + (m̄ᵢ + tᵢ)`; the feasible alternatives have
`∑ᵢ tᵢ ≤ 0`. A social choice function is `f(θ) = (k(θ), t₁(θ), …, t_I(θ))`.

* `exPostEfficient_ql_iff`: `f` is ex post efficient (within the feasible alternatives) iff its
  project rule satisfies (23.C.7) and it is budget balanced (23.C.12) (with at least one
  agent); in particular (23.C.7) is necessary (p. 877).
* **Proposition 23.C.4** (Groves): a project rule satisfying (23.C.7) with transfers (23.C.8)
  is strategy-proof.
* The Clarke (pivotal) mechanism and its properties (p. 878): transfers are `0` when agent `i`
  is not pivotal and `≤ 0` always. **Correction**: MWG say the transfer "is negative" when the
  announcement changes the project decision; with ties it can be `0`
  (`clarke_pivotal_zero_tax`). Footnote 23: `hᵢ(θ₋ᵢ) ≤ -∑_{j≠i} vⱼ(k₋ᵢ*(θ₋ᵢ), θⱼ)` is sufficient
  but not necessary for `∑ᵢ tᵢ(θ) ≤ 0`.
* The single-good case: the Clarke transfer is minus the highest other valuation for the winner
  and `0` for the others (the second-price auction, p. 879).
* **Proposition 23.C.5** (Green-Laffont): if every valuation function `K → ℝ` arises for some
  type, every strategy-proof `f` with an efficient project rule is a Groves mechanism. MWG's
  type `θᵢ'` in (23.C.10) has valuation `-∞` off two projects, which is not a real-valued
  function (not in `𝒱`); we use `-∑_{j≠i} vⱼ(k, θⱼ) - 1` there instead (correction).
* Footnote 20: with at least two agents no social choice function is dictatorial, since no
  agent has a best feasible alternative.
* Exercise 23.C.11: Proposition 23.C.4 survives a strictly increasing transformation
  `uᵢ(vᵢ(k, θᵢ) + m̄ᵢ + tᵢ)`.
-/

namespace MWG.MechanismDesign

open Function Finset

variable {ι : Type*} {Θ : ι → Type*} {K : Type*}

/-- **Section 23.C** (MWG, p. 876). Quasilinear utility `uᵢ(x, θᵢ) = vᵢ(k, θᵢ) + (m̄ᵢ + tᵢ)` of
the alternative `x = (k, t)`. -/
def qlU (v : (i : ι) → K → Θ i → ℝ) (m : ι → ℝ) : (i : ι) → K × (ι → ℝ) → Θ i → ℝ :=
  fun i x θi => v i x.1 θi + (m i + x.2 i)

/-- **Section 23.C** (MWG, p. 877). The feasible alternatives `X = {(k, t) : ∑ᵢ tᵢ ≤ 0}`. -/
def QLAlt (ι : Type*) [Fintype ι] (K : Type*) : Type _ :=
  {x : K × (ι → ℝ) // ∑ i, x.2 i ≤ 0}

/-- **(23.C.7)** (MWG, p. 877). The project rule `k(·)` is efficient:
`∑ᵢ vᵢ(k(θ), θᵢ) ≥ ∑ᵢ vᵢ(k, θᵢ)` for all `k ∈ K` and `θ`. -/
def EfficientProject [Fintype ι] (v : (i : ι) → K → Θ i → ℝ) (k : ((i : ι) → Θ i) → K) :
    Prop :=
  ∀ θ k', ∑ i, v i k' (θ i) ≤ ∑ i, v i (k θ) (θ i)

/-- **(23.C.12)** (MWG, p. 880). Budget balance: `∑ᵢ tᵢ(θ) = 0` for all `θ`. -/
def BudgetBalanced [Fintype ι] (t : ((i : ι) → Θ i) → ι → ℝ) : Prop :=
  ∀ θ, ∑ i, t θ i = 0

/-- **Section 23.C** (MWG, pp. 877, 880). A feasible quasilinear social choice function is ex post
efficient (Definition 23.B.2, among the feasible alternatives) iff its project rule satisfies
(23.C.7) and it is budget balanced (23.C.12). -/
theorem exPostEfficient_ql_iff [Fintype ι] [Nonempty ι] (v : (i : ι) → K → Θ i → ℝ)
    (m : ι → ℝ) (f : ((i : ι) → Θ i) → QLAlt ι K) :
    ExPostEfficient (fun i (x : QLAlt ι K) θi => qlU v m i x.1 θi) f ↔
      EfficientProject v (fun θ => (f θ).1.1) ∧ BudgetBalanced (fun θ => (f θ).1.2) := by
  classical
  have hI : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  constructor
  · intro hE
    refine ⟨fun θ k' => ?_, fun θ => ?_⟩
    · by_contra hlt
      rw [not_le] at hlt
      set δ := ∑ i, v i k' (θ i) - ∑ i, v i (f θ).1.1 (θ i) with hδ
      have hδpos : 0 < δ := by linarith
      let t' : ι → ℝ := fun i => (f θ).1.2 i + v i (f θ).1.1 (θ i) - v i k' (θ i) +
        δ / Fintype.card ι
      have hfeas : ∑ i, t' i ≤ 0 := by
        have : ∑ i, t' i = ∑ i, (f θ).1.2 i := by
          simp only [t', sum_add_distrib, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul]
          field_simp
          ring
        rw [this]; exact (f θ).2
      apply hE
      refine ⟨θ, ⟨(k', t'), hfeas⟩, fun i => ?_, Classical.arbitrary ι, ?_⟩
      · simp only [qlU, t']
        have := div_pos hδpos hI
        linarith
      · simp only [qlU, t']
        have := div_pos hδpos hI
        linarith
    · by_contra hne
      have hlt : ∑ i, (f θ).1.2 i < 0 := lt_of_le_of_ne (f θ).2 hne
      set δ := -∑ i, (f θ).1.2 i
      let t' : ι → ℝ := fun i => (f θ).1.2 i + δ / Fintype.card ι
      have hfeas : ∑ i, t' i ≤ 0 := by
        have : ∑ i, t' i = 0 := by
          simp only [t', sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, δ]
          field_simp
          ring
        rw [this]
      apply hE
      have hd : 0 < δ / Fintype.card ι := div_pos (by simp only [δ]; linarith) hI
      refine ⟨θ, ⟨((f θ).1.1, t'), hfeas⟩, fun i => ?_, Classical.arbitrary ι, ?_⟩
      · simp only [qlU, t']; linarith
      · simp only [qlU, t']; linarith
  · rintro ⟨hk, hb⟩ ⟨θ, x, hx, j, hj⟩
    have hsum : ∑ i, qlU v m i (f θ).1 (θ i) < ∑ i, qlU v m i x.1 (θ i) :=
      sum_lt_sum (fun i _ => hx i) ⟨j, mem_univ j, hj⟩
    simp only [qlU, sum_add_distrib] at hsum
    have h1 := hk θ x.1.1
    have h2 := hb θ
    have h3 := x.2
    simp only at h1 h2
    linarith

/-- The transfer function of a Groves mechanism, (23.C.8):
`tᵢ(θ) = ∑_{j≠i} vⱼ(k*(θ), θⱼ) + hᵢ(θ₋ᵢ)`. -/
def grovesTransfer [Fintype ι] [DecidableEq ι] (v : (i : ι) → K → Θ i → ℝ)
    (k : ((i : ι) → Θ i) → K) (h : (i : ι) → ((j : ι) → Θ j) → ℝ) :
    ((i : ι) → Θ i) → ι → ℝ :=
  fun θ i => ∑ j ∈ univ.erase i, v j (k θ) (θ j) + h i θ

/-- `hᵢ` depends only on `θ₋ᵢ`: changing `θᵢ` does not change `hᵢ(θ)`. -/
def IndepOwn [DecidableEq ι] {Y : Type*} (h : (i : ι) → ((j : ι) → Θ j) → Y) : Prop :=
  ∀ i θ (a : Θ i), h i (update θ i a) = h i θ

/-- **Proposition 23.C.4** (MWG, p. 877). If `k*(·)` satisfies (23.C.7) and the transfers have the
form (23.C.8) with `hᵢ` a function of `θ₋ᵢ` only, then `f = (k*, t)` is truthfully implementable
in dominant strategies. -/
theorem proposition_23_C_4 [Fintype ι] [DecidableEq ι] {v : (i : ι) → K → Θ i → ℝ}
    (m : ι → ℝ) {k : ((i : ι) → Θ i) → K} (hk : EfficientProject v k)
    {h : (i : ι) → ((j : ι) → Θ j) → ℝ} (hh : IndepOwn h) :
    StrategyProof (qlU v m) (fun θ => (k θ, grovesTransfer v k h θ)) := by
  intro i θ θh
  simp only [qlU, grovesTransfer, hh i θ θh]
  have e : ∀ θ' : (j : ι) → Θ j, (∀ j ≠ i, θ' j = θ j) →
      v i (k θ') (θ i) + ∑ j ∈ univ.erase i, v j (k θ') (θ' j) = ∑ j, v j (k θ') (θ j) := by
    intro θ' hθ'
    rw [← add_sum_erase _ _ (mem_univ i)]
    congr 1
    exact sum_congr rfl fun j hj => by rw [hθ' j (ne_of_mem_erase hj)]
  have e1 := e (update θ i θh) fun j hj => update_of_ne hj _ _
  have e2 := e θ fun _ _ => rfl
  have := hk θ (k (update θ i θh))
  linarith

/-- The Clarke (pivotal) transfer: `hᵢ(θ₋ᵢ) = -∑_{j≠i} vⱼ(k₋ᵢ*(θ₋ᵢ), θⱼ)`, where `k₋ᵢ*(θ₋ᵢ)` is
efficient for the agents `j ≠ i` alone (MWG, p. 878). -/
def clarkeH [Fintype ι] [DecidableEq ι] (v : (i : ι) → K → Θ i → ℝ)
    (kminus : ι → ((j : ι) → Θ j) → K) : (i : ι) → ((j : ι) → Θ j) → ℝ :=
  fun i θ => -∑ j ∈ univ.erase i, v j (kminus i θ) (θ j)

/-- `k₋ᵢ*(θ₋ᵢ)` is efficient for the agents other than `i` (MWG, p. 878). -/
def EfficientForOthers [Fintype ι] [DecidableEq ι] (v : (i : ι) → K → Θ i → ℝ)
    (kminus : ι → ((j : ι) → Θ j) → K) : Prop :=
  IndepOwn kminus ∧ ∀ i θ k', ∑ j ∈ univ.erase i, v j k' (θ j) ≤
    ∑ j ∈ univ.erase i, v j (kminus i θ) (θ j)

/-- **Clarke mechanism** (MWG, p. 878). The Clarke `hᵢ` depends only on `θ₋ᵢ`, so the Clarke
mechanism is a Groves mechanism and is strategy-proof. -/
theorem clarke_strategyProof [Fintype ι] [DecidableEq ι] {v : (i : ι) → K → Θ i → ℝ}
    (m : ι → ℝ) {k : ((i : ι) → Θ i) → K} (hk : EfficientProject v k)
    {kminus : ι → ((j : ι) → Θ j) → K} (hkm : EfficientForOthers v kminus) :
    StrategyProof (qlU v m) (fun θ => (k θ, grovesTransfer v k (clarkeH v kminus) θ)) := by
  refine proposition_23_C_4 m hk fun i θ a => ?_
  simp only [clarkeH, hkm.1 i θ a]
  congr 1
  exact sum_congr rfl fun j hj => by rw [update_of_ne (ne_of_mem_erase hj)]

/-- **Clarke mechanism** (MWG, p. 878). Agent `i`'s Clarke transfer is `0` if his announcement does
not change the project decision relative to `k₋ᵢ*(θ₋ᵢ)`, and is never positive. -/
theorem clarke_transfer_props [Fintype ι] [DecidableEq ι] {v : (i : ι) → K → Θ i → ℝ}
    {k : ((i : ι) → Θ i) → K} {kminus : ι → ((j : ι) → Θ j) → K}
    (hkm : EfficientForOthers v kminus) (θ : (i : ι) → Θ i) (i : ι) :
    (k θ = kminus i θ → grovesTransfer v k (clarkeH v kminus) θ i = 0) ∧
      grovesTransfer v k (clarkeH v kminus) θ i ≤ 0 := by
  refine ⟨fun he => ?_, ?_⟩
  · simp [grovesTransfer, clarkeH, he]
  · have := hkm.2 i θ (k θ)
    simp only [grovesTransfer, clarkeH]
    linarith

/-- **Footnote 23** (MWG, p. 878). The Clarke mechanism is feasible: `∑ᵢ tᵢ(θ) ≤ 0`; more
generally `hᵢ(θ₋ᵢ) ≤ -∑_{j≠i} vⱼ(k₋ᵢ*(θ₋ᵢ), θⱼ)` for all `i` is sufficient for a Groves scheme to
be feasible. -/
theorem footnote_23_23 [Fintype ι] [DecidableEq ι] {v : (i : ι) → K → Θ i → ℝ}
    {k : ((i : ι) → Θ i) → K} {kminus : ι → ((j : ι) → Θ j) → K}
    (hkm : EfficientForOthers v kminus) {h : (i : ι) → ((j : ι) → Θ j) → ℝ}
    (hle : ∀ i θ, h i θ ≤ clarkeH v kminus i θ) (θ : (i : ι) → Θ i) :
    ∑ i, grovesTransfer v k h θ i ≤ 0 := by
  refine sum_nonpos fun i _ => ?_
  have h1 := hkm.2 i θ (k θ)
  have h2 := hle i θ
  simp only [grovesTransfer, clarkeH] at h2 ⊢
  linarith

/-- **Footnote 23** (MWG, p. 878), "sufficient (but not necessary)": a feasible Groves scheme with
`h₁ > -∑_{j≠1} vⱼ(k₋₁*, θⱼ)` (one project, `h = (1, -1)`). -/
theorem footnote_23_23_not_necessary :
    let v : Fin 2 → Unit → Unit → ℝ := fun _ _ _ => 0
    let h : Fin 2 → (Fin 2 → Unit) → ℝ := fun i _ => if i = 0 then 1 else -1
    (∑ i, grovesTransfer (Θ := fun _ => Unit) v (fun _ => ()) h (fun _ => ()) i ≤ 0) ∧
      clarkeH (Θ := fun _ => Unit) v (fun _ _ => ()) 0 (fun _ => ()) < h 0 (fun _ => ()) := by
  intro v h
  simp [v, h, grovesTransfer, clarkeH, Fin.sum_univ_two]

/-- **Correction** (MWG, p. 878). A pivotal agent's Clarke tax can be `0`: with two agents,
projects `Bool`, agent 0 valuing `true` at `1`, agent 1 indifferent, and `k₋₀* = false`, the
efficient decision is `true ≠ k₋₀*` but agent 0's transfer is `0`, not negative. -/
theorem clarke_pivotal_zero_tax :
    let v : Fin 2 → Bool → Unit → ℝ := fun i k _ => if i = 0 ∧ k = true then 1 else 0
    (fun (_ : Fin 2 → Unit) => true) ≠ (fun _ => false) ∧
      grovesTransfer v (fun _ => true) (clarkeH v fun _ _ => false) (fun _ => ()) 0 = 0 := by
  refine ⟨fun h => absurd (congrFun h fun _ => ()) (by decide), ?_⟩
  simp [grovesTransfer, clarkeH]

/-- **Single indivisible good** (MWG, pp. 877, 879). The project is the winner `k ∈ ι`, and
`vᵢ(k, θᵢ) = θᵢ` if `k = i`, `0` otherwise. -/
def goodV [DecidableEq ι] : ι → ι → ℝ → ℝ := fun i k θi => if k = i then θi else 0

/-- **Single indivisible good** (MWG, p. 879): with an efficient allocation (the good goes to a
highest valuation) and `k₋ᵢ*(θ₋ᵢ)` a highest valuation among the others, the Clarke transfer of
the winner is minus the highest other valuation (the second-highest valuation) and every other
agent's transfer is `0`: the Clarke mechanism is the second-price sealed-bid auction. -/
theorem clarke_single_good [Fintype ι] [DecidableEq ι] {k : (ι → ℝ) → ι}
    (hk : ∀ (θ : ι → ℝ) j, θ j ≤ θ (k θ)) {kminus : ι → (ι → ℝ) → ι}
    (hkm1 : ∀ i (θ : ι → ℝ), kminus i θ ≠ i)
    (hkm2 : ∀ i (θ : ι → ℝ) j, j ≠ i → θ j ≤ θ (kminus i θ)) (θ : ι → ℝ) (i : ι) :
    grovesTransfer (Θ := fun _ => ℝ) goodV k (clarkeH (Θ := fun _ => ℝ) goodV kminus) θ i =
      if k θ = i then -θ (kminus i θ) else 0 := by
  have hsum : ∀ w : ι, ∑ j ∈ univ.erase i, goodV j w (θ j) = if w = i then 0 else θ w := by
    intro w
    by_cases hw : w = i
    · subst hw
      refine (sum_eq_zero fun j hj => ?_).trans (by simp)
      simp [goodV, Ne.symm (ne_of_mem_erase hj)]
    · rw [sum_eq_single w]
      · simp [goodV, hw]
      · intro j _ hj; simp [goodV, Ne.symm hj]
      · intro h; exact absurd (mem_erase.2 ⟨hw, mem_univ w⟩) h
  simp only [grovesTransfer, clarkeH, hsum, hkm1 i θ, ite_false]
  by_cases hw : k θ = i
  · simp [hw]
  · simp only [hw, ite_false]
    have h1 := hk θ (kminus i θ)
    have h2 := hkm2 i θ (k θ) hw
    linarith

/-- **Proposition 23.C.5** (Green and Laffont; MWG, p. 879). Suppose every valuation function
`K → ℝ` arises for some type of each agent (`{vᵢ(·, θᵢ) : θᵢ ∈ Θᵢ} = 𝒱`). If `f = (k*, t)` with
`k*` satisfying (23.C.7) is truthfully implementable in dominant strategies, then the transfers
have the Groves form (23.C.8): `tᵢ(θ) = ∑_{j≠i} vⱼ(k*(θ), θⱼ) + hᵢ(θ₋ᵢ)`. -/
theorem proposition_23_C_5 [Fintype ι] [DecidableEq ι] {v : (i : ι) → K → Θ i → ℝ}
    (m : ι → ℝ) (hrich : ∀ i (w : K → ℝ), ∃ θi : Θ i, ∀ k, v i k θi = w k)
    {k : ((i : ι) → Θ i) → K} (hk : EfficientProject v k) {t : ((i : ι) → Θ i) → ι → ℝ}
    (hSP : StrategyProof (qlU v m) (fun θ => (k θ, t θ))) :
    ∃ h : (i : ι) → ((j : ι) → Θ j) → ℝ, IndepOwn h ∧ ∀ θ, t θ = grovesTransfer v k h θ := by
  classical
  -- (23.C.9)
  let h : (i : ι) → ((j : ι) → Θ j) → ℝ := fun i θ => t θ i - ∑ j ∈ univ.erase i, v j (k θ) (θ j)
  refine ⟨h, ?_, fun θ => funext fun i => by simp [grovesTransfer, h]⟩
  -- the others' total valuation of a project, at the others' types in `θ`
  let W : ι → ((j : ι) → Θ j) → K → ℝ := fun i θ k' => ∑ j ∈ univ.erase i, v j k' (θ j)
  have hW : ∀ i θ (a : Θ i) k', W i (update θ i a) k' = W i θ k' := fun i θ a k' =>
    sum_congr rfl fun j hj => by rw [update_of_ne (ne_of_mem_erase hj)]
  have hsplit : ∀ i θ k', ∑ j, v j k' (θ j) = v i k' (θ i) + W i θ k' := fun i θ k' =>
    (add_sum_erase _ _ (mem_univ i)).symm
  -- SP, rewritten: type `a` of agent `i` reporting `b`, with the others at `θ`
  have hsp : ∀ i θ (a b : Θ i), v i (k (update θ i b)) a + t (update θ i b) i ≤
      v i (k (update θ i a)) a + t (update θ i a) i := by
    intro i θ a b
    have := hSP i (update θ i a) b
    simp only [qlU, update_idem, update_self] at this
    linarith
  -- (i): equal projects give equal transfers
  have case_i : ∀ i θ (a b : Θ i), k (update θ i a) = k (update θ i b) →
      t (update θ i a) i = t (update θ i b) i := by
    intro i θ a b he
    have h1 := hsp i θ a b
    have h2 := hsp i θ b a
    rw [he] at h1 h2
    linarith
  -- the key inequality: `hᵢ(a, θ₋ᵢ) ≤ hᵢ(b, θ₋ᵢ)` for all `a`, `b`
  have key : ∀ i θ (a b : Θ i), h i (update θ i a) ≤ h i (update θ i b) := by
    intro i θ a b
    by_cases he : k (update θ i a) = k (update θ i b)
    · have e1 := hW i θ a (k (update θ i b))
      have e2 := hW i θ b (k (update θ i b))
      simp only [h, W] at e1 e2 ⊢
      rw [case_i i θ a b he, he, e1, e2]
    · -- (23.C.10) with `-∞` replaced by `-W - 1`
      refine le_of_forall_pos_le_add fun ε hε => ?_
      obtain ⟨k1, hk1⟩ : ∃ k1, k (update θ i a) = k1 := ⟨_, rfl⟩
      obtain ⟨k2, hk2'⟩ : ∃ k2, k (update θ i b) = k2 := ⟨_, rfl⟩
      rw [hk1, hk2'] at he
      obtain ⟨c, hc⟩ := hrich i fun k' =>
        if k' = k1 then -W i θ k1 else if k' = k2 then -W i θ k2 + ε else -W i θ k' - 1
      have hv1 : v i k1 c = -W i θ k1 := by rw [hc]; simp
      have hv2 : v i k2 c = -W i θ k2 + ε := by rw [hc]; simp [Ne.symm he]
      have hvo : ∀ k', k' ≠ k1 → k' ≠ k2 → v i k' c = -W i θ k' - 1 := by
        intro k' h1 h2; rw [hc]; simp [h1, h2]
      -- the efficient project at type `c` is `k2`
      have hk2 : k (update θ i c) = k2 := by
        by_contra hne
        have hmax := hk (update θ i c) k2
        rw [hsplit i _ k2, hsplit i _ (k (update θ i c)), hW, hW] at hmax
        simp only [update_self] at hmax
        rw [hv2] at hmax
        by_cases h1 : k (update θ i c) = k1
        · rw [h1, hv1] at hmax; linarith
        · rw [hvo _ h1 hne] at hmax; linarith
      have hti := case_i i θ c b (by rw [hk2, hk2'])
      have hsp' := hsp i θ c a
      rw [hk2, hk1, hv1, hv2, hti] at hsp'
      have e1 := hW i θ a k1
      have e2 := hW i θ b k2
      simp only [h, W] at hsp' e1 e2 ⊢
      rw [hk1, hk2', e1, e2]
      linarith
  intro i θ a
  have h1 := key i θ a (θ i)
  have h2 := key i θ (θ i) a
  rw [update_eq_self] at h1 h2
  exact le_antisymm h1 h2

/-- **Footnote 20** (MWG, p. 877). The quasilinear set of alternatives is not compact; with at
least two agents no social choice function is dictatorial, since every feasible alternative can
be improved for any agent by a transfer from another agent. -/
theorem footnote_23_20 [Fintype ι] {v : (i : ι) → K → Θ i → ℝ} (m : ι → ℝ)
    (h2 : ∀ i : ι, ∃ j, j ≠ i) (θ0 : (i : ι) → Θ i) (f : ((i : ι) → Θ i) → QLAlt ι K) :
    ¬Dictatorial (fun i (x : QLAlt ι K) θi => qlU v m i x.1 θi) f := by
  classical
  rintro ⟨h, hh⟩
  obtain ⟨j, hj⟩ := h2 h
  let x := f θ0
  let t' : ι → ℝ := fun i => x.1.2 i + (if i = h then 1 else 0) - (if i = j then 1 else 0)
  have hfeas : ∑ i, t' i ≤ 0 := by
    have : ∑ i, t' i = ∑ i, x.1.2 i := by
      simp only [t', sum_add_distrib, sum_sub_distrib, sum_ite_eq', mem_univ, ite_true]
      ring
    rw [this]; exact x.2
  have := hh θ0 ⟨(x.1.1, t'), hfeas⟩
  simp only [qlU, t', ite_true, Ne.symm hj, ite_false] at this
  linarith

/-- **Exercise 23.C.11** (MWG, p. 920). With utilities `uᵢ(vᵢ(k, θᵢ) + m̄ᵢ + tᵢ)` for strictly
increasing `uᵢ` (arbitrary risk preferences over money), Proposition 23.C.4 is unaffected:
Groves schemes remain strategy-proof. -/
theorem exercise_23_C_11 [Fintype ι] [DecidableEq ι] {v : (i : ι) → K → Θ i → ℝ}
    (m : ι → ℝ) {k : ((i : ι) → Θ i) → K} (hk : EfficientProject v k)
    {h : (i : ι) → ((j : ι) → Θ j) → ℝ} (hh : IndepOwn h) (U : ι → ℝ → ℝ)
    (hU : ∀ i, StrictMono (U i)) :
    StrategyProof (fun i x θi => U i (qlU v m i x θi))
      (fun θ => (k θ, grovesTransfer v k h θ)) :=
  fun i θ θh => (hU i).monotone (proposition_23_C_4 m hk hh i θ θh)

/-- **Outside agent** (MWG, p. 881). With an agent 0 who has no private information and utility
`m̄₀ + t₀`, a Groves scheme for agents `1, …, I` with `t₀(θ) = -∑_{i≠0} tᵢ(θ)` is budget balanced
for all `I + 1` agents, keeps (23.C.7) (agent 0 values all projects at `0`), and remains
strategy-proof for the agents with private types. -/
theorem outside_agent [Fintype ι] [DecidableEq ι] {v : (i : ι) → K → Θ i → ℝ} (m : ι → ℝ)
    {k : ((i : ι) → Θ i) → K} (hk : EfficientProject v k)
    {h : (i : ι) → ((j : ι) → Θ j) → ℝ} (hh : IndepOwn h) (θ : (i : ι) → Θ i) :
    (-∑ i, grovesTransfer v k h θ i) + ∑ i, grovesTransfer v k h θ i = 0 ∧
      (∀ k', (0 : ℝ) + ∑ i, v i k' (θ i) ≤ 0 + ∑ i, v i (k θ) (θ i)) ∧
      StrategyProof (qlU v m) (fun θ => (k θ, grovesTransfer v k h θ)) :=
  ⟨by ring, fun k' => by linarith [hk θ k'], proposition_23_C_4 m hk hh⟩

end MWG.MechanismDesign
