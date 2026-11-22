/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGAdverseSelection.Signaling
import Mathlib.Order.Filter.Basic

/-!
# The screening model

MWG, Section 13.D, pp. 460-465.

Same types, prior and cost function as in Section 13.C (a `SigModel` with `r = 0`); the task
level `t ≥ 0` plays the role of education. A contract is a pair `(w, t)`. In stage 1 two firms
announce finite sets of contracts (`ValidMenu`); in stage 2 each worker type chooses a contract
from the union of the menus (`Chooses`): one maximizing `w - c(t, θ)`, the lower task level among
equally good ones, accepting when indifferent between it and staying home (utility `0`); a firm
gets the worker if it offers her chosen contract, half the time if both do (`share`). Given this
stage-2 behaviour, the pure SPNE are the pairs of menus that are best replies to each other
(`IsScreenEq`, the Nash condition of Definition 8.D.1 written out).

* `chooses_unique`, `exists_chooses`: the worker's choice is well defined.
* `proposition_13_D_1` (observable types): type `θ` accepts `(θ, 0)` and firms earn zero.
* `lemma_13_D_1`-`lemma_13_D_5`, `proposition_13_D_2` (unobservable types, in module `ScreeningEq`):
  zero profits, no pooling equilibrium, `(θ_L, 0)` and `(θ_H, t̂_H)` with
  `θ_H - c(t̂_H, θ_L) = θ_L - c(0, θ_L)`.
-/

namespace MWG.AdverseSelection

namespace SigModel

/-- A worker's utility from contract `k = (w, t)`. -/
def util (M : SigModel) (θ : ℝ) (k : ℝ × ℝ) : ℝ := k.1 - M.c k.2 θ

/-- **Section 13.D** (MWG, p. 461). A menu: a finite set of contracts with task levels `t ≥ 0`. -/
def ValidMenu (A : Finset (ℝ × ℝ)) : Prop := ∀ k ∈ A, 0 ≤ k.2

/-- **Section 13.D** (MWG, p. 461). Type `θ` chooses contract `k` from the offered set `U`: `k`
maximizes utility, has the lowest task level among the best contracts, and is accepted
(utility at least `0`, the value of not working). -/
def Chooses (M : SigModel) (θ : ℝ) (U : Finset (ℝ × ℝ)) (k : ℝ × ℝ) : Prop :=
  k ∈ U ∧ 0 ≤ M.util θ k ∧ (∀ k' ∈ U, M.util θ k' ≤ M.util θ k) ∧
    ∀ k' ∈ U, M.util θ k' = M.util θ k → k.2 ≤ k'.2

/-- **Section 13.D** (MWG, p. 461). The share of a worker choosing `k` that goes to the firm
offering `own` when the other offers `other`. -/
noncomputable def share (own other : Finset (ℝ × ℝ)) (k : ℝ × ℝ) : ℝ :=
  if k ∈ own then (if k ∈ other then 1 / 2 else 1) else 0

open Classical in
/-- The firm's expected profit from a worker of type `θ`. -/
noncomputable def typeProfit (M : SigModel) (θ : ℝ) (own other : Finset (ℝ × ℝ)) : ℝ :=
  if h : ∃ k, M.Chooses θ (own ∪ other) k then share own other h.choose * (θ - h.choose.1)
  else 0

/-- **Section 13.D** (MWG, p. 461). A firm's expected profit. -/
noncomputable def screenProfit (M : SigModel) (own other : Finset (ℝ × ℝ)) : ℝ :=
  (1 - M.lam) * M.typeProfit M.θL own other + M.lam * M.typeProfit M.θH own other

/-- **Section 13.D** (MWG, p. 461). A pure strategy SPNE of the screening game. -/
def IsScreenEq (M : SigModel) (A₁ A₂ : Finset (ℝ × ℝ)) : Prop :=
  ValidMenu A₁ ∧ ValidMenu A₂ ∧ (∀ B, ValidMenu B → M.screenProfit B A₂ ≤ M.screenProfit A₁ A₂) ∧
    ∀ B, ValidMenu B → M.screenProfit B A₁ ≤ M.screenProfit A₂ A₁

variable {M : SigModel}

/-- The worker's choice is unique. -/
theorem chooses_unique {θ : ℝ} {U : Finset (ℝ × ℝ)} {k k' : ℝ × ℝ} (h : M.Chooses θ U k)
    (h' : M.Chooses θ U k') : k = k' := by
  have hu : M.util θ k = M.util θ k' := le_antisymm (h'.2.2.1 k h.1) (h.2.2.1 k' h'.1)
  have ht : k.2 = k'.2 := le_antisymm (h.2.2.2 k' h'.1 hu.symm) (h'.2.2.2 k h.1 hu)
  have hw : k.1 = k'.1 := by unfold util at hu; rw [ht] at hu; linarith
  exact Prod.ext hw ht

/-- If some offered contract gives utility at least `0`, the worker chooses a contract. -/
theorem exists_chooses (θ : ℝ) {U : Finset (ℝ × ℝ)} (h : ∃ k ∈ U, 0 ≤ M.util θ k) :
    ∃ k, M.Chooses θ U k := by
  obtain ⟨k0, hk0, hu0⟩ := h
  obtain ⟨k1, hk1, hmax⟩ := U.exists_max_image (M.util θ) ⟨k0, hk0⟩
  set V := U.filter (fun k => M.util θ k = M.util θ k1)
  obtain ⟨k, hk, hmin⟩ := V.exists_min_image (fun k => k.2) ⟨k1, by simp [V, hk1]⟩
  simp only [V, Finset.mem_filter] at hk
  refine ⟨k, hk.1, by rw [hk.2]; exact hu0.trans (hmax k0 hk0), fun k' hk' => ?_,
    fun k' hk' he => hmin k' (by simp [V, hk', he.trans hk.2])⟩
  rw [hk.2]; exact hmax k' hk'

/-- The firm's profit from type `θ` when `θ` chooses `k`. -/
theorem typeProfit_of_chooses {θ : ℝ} {own other : Finset (ℝ × ℝ)} {k : ℝ × ℝ}
    (h : M.Chooses θ (own ∪ other) k) :
    M.typeProfit θ own other = share own other k * (θ - k.1) := by
  have hex : ∃ k, M.Chooses θ (own ∪ other) k := ⟨k, h⟩
  rw [typeProfit, dite_eq_left_of_eq_true (eq_true hex), chooses_unique hex.choose_spec h]

/-- The profit from type `θ` is `0` if she does not work. -/
theorem typeProfit_of_not {θ : ℝ} {own other : Finset (ℝ × ℝ)}
    (h : ¬ ∃ k, M.Chooses θ (own ∪ other) k) : M.typeProfit θ own other = 0 := by
  rw [typeProfit, dite_eq_right_of_eq_false (eq_false h)]

/-- The firms' shares of a chosen contract add up to `1`. -/
theorem share_add {own other : Finset (ℝ × ℝ)} {k : ℝ × ℝ} (hk : k ∈ own ∪ other) :
    share own other k + share other own k = 1 := by
  rcases Finset.mem_union.1 hk with h | h <;> unfold share <;> split_ifs <;> norm_num

theorem share_nonneg (own other : Finset (ℝ × ℝ)) (k : ℝ × ℝ) : 0 ≤ share own other k := by
  unfold share; split_ifs <;> norm_num

theorem share_le_one (own other : Finset (ℝ × ℝ)) (k : ℝ × ℝ) : share own other k ≤ 1 := by
  unfold share; split_ifs <;> norm_num

/-- A firm offering nothing earns nothing. -/
theorem screenProfit_empty (other : Finset (ℝ × ℝ)) : M.screenProfit ∅ other = 0 := by
  have : ∀ θ, M.typeProfit θ ∅ other = 0 := by
    intro θ
    by_cases h : ∃ k, M.Chooses θ (∅ ∪ other) k
    · obtain ⟨k, hk⟩ := h
      rw [typeProfit_of_chooses hk]; simp [share]
    · exact typeProfit_of_not h
  simp [screenProfit, this]

/-- A contract that type `θ` strictly prefers to everything else on offer, with utility
`≥ 0`, is her choice. -/
theorem chooses_of_strict {θ : ℝ} {U : Finset (ℝ × ℝ)} {k : ℝ × ℝ} (hk : k ∈ U)
    (h0 : 0 ≤ M.util θ k) (hs : ∀ k' ∈ U, k' ≠ k → M.util θ k' < M.util θ k) :
    M.Chooses θ U k := by
  refine ⟨hk, h0, fun k' hk' => ?_, fun k' hk' he => ?_⟩
  · by_cases h : k' = k
    · rw [h]
    · exact (hs k' hk' h).le
  · by_cases h : k' = k
    · rw [h]
    · exact absurd he (hs k' hk' h).ne

/-- A firm offering nothing earns nothing from any type. -/
theorem typeProfit_empty (θ : ℝ) (other : Finset (ℝ × ℝ)) : M.typeProfit θ ∅ other = 0 := by
  by_cases h : ∃ k, M.Chooses θ (∅ ∪ other) k
  · obtain ⟨k, hk⟩ := h
    rw [typeProfit_of_chooses hk]; simp [share]
  · exact typeProfit_of_not h

/-- A deviation `B` containing a contract `k` that type `θ` strictly prefers to everything else
on offer captures type `θ`: the deviator's profit from her is `θ - w`. -/
theorem typeProfit_capture {θ : ℝ} {other B : Finset (ℝ × ℝ)} {k : ℝ × ℝ} (hk : k ∈ B)
    (h0 : 0 ≤ M.util θ k) (hs : ∀ k' ∈ other, M.util θ k' < M.util θ k)
    (hB : ∀ k' ∈ B, k' ≠ k → M.util θ k' < M.util θ k) :
    M.typeProfit θ B other = θ - k.1 := by
  have hch : M.Chooses θ (B ∪ other) k := by
    refine chooses_of_strict (Finset.mem_union_left _ hk) h0 fun k' hk' hne => ?_
    rcases Finset.mem_union.1 hk' with h | h
    · exact hB k' h hne
    · exact hs k' h
  have hno : k ∉ other := fun h => lt_irrefl _ (hs k h)
  rw [typeProfit_of_chooses hch]
  simp [share, hk, hno]

/-- The two firms' profits from type `θ` add up to `θ - w` of her chosen contract. -/
theorem typeProfit_add {θ : ℝ} {A₁ A₂ : Finset (ℝ × ℝ)} {k : ℝ × ℝ}
    (h : M.Chooses θ (A₁ ∪ A₂) k) :
    M.typeProfit θ A₁ A₂ + M.typeProfit θ A₂ A₁ = θ - k.1 := by
  have h' : M.Chooses θ (A₂ ∪ A₁) k := by rwa [Finset.union_comm]
  rw [typeProfit_of_chooses h, typeProfit_of_chooses h', ← add_mul, share_add h.1, one_mul]

/-- **Section 13.D** (MWG, p. 461). With observable types, the competition for type `θ` workers
alone: a pure SPNE of the game in which firms offer menus to type `θ`. -/
def IsTypeEq (M : SigModel) (θ : ℝ) (A₁ A₂ : Finset (ℝ × ℝ)) : Prop :=
  ValidMenu A₁ ∧ ValidMenu A₂ ∧ (∀ B, ValidMenu B → M.typeProfit θ B A₂ ≤ M.typeProfit θ A₁ A₂) ∧
    ∀ B, ValidMenu B → M.typeProfit θ B A₁ ≤ M.typeProfit θ A₂ A₁

theorem IsTypeEq.symm {θ : ℝ} {A₁ A₂ : Finset (ℝ × ℝ)} (h : M.IsTypeEq θ A₁ A₂) :
    M.IsTypeEq θ A₂ A₁ := ⟨h.2.1, h.1, h.2.2.2, h.2.2.1⟩

/-- **Proposition 13.D.1** (MWG, p. 461). With observable types, in any SPNE a type-`θ` worker
accepts the contract `(θ, 0)` and both firms earn zero profits. -/
theorem proposition_13_D_1 (hM : M.Valid) (b : Bool) {A₁ A₂ : Finset (ℝ × ℝ)}
    (h : M.IsTypeEq (M.θ b) A₁ A₂) :
    M.Chooses (M.θ b) (A₁ ∪ A₂) (M.θ b, 0) ∧ M.typeProfit (M.θ b) A₁ A₂ = 0 ∧
      M.typeProfit (M.θ b) A₂ A₁ = 0 := by
  set θ := M.θ b
  have hθ : 0 < θ := by
    cases b
    · exact hM.θL_pos
    · exact hM.θL_pos.trans hM.lt
  have hval1 : ValidMenu A₁ := h.1
  have hval2 : ValidMenu A₂ := h.2.1
  have hnn1 : 0 ≤ M.typeProfit θ A₁ A₂ := by
    have := h.2.2.1 ∅ (fun _ h => absurd h (Finset.notMem_empty _))
    rwa [typeProfit_empty] at this
  have hnn2 : 0 ≤ M.typeProfit θ A₂ A₁ := by
    have := h.2.2.2 ∅ (fun _ h => absurd h (Finset.notMem_empty _))
    rwa [typeProfit_empty] at this
  have hvs : ∀ w t, 0 ≤ t → ValidMenu {(w, t)} := fun w t ht k hk => by
    rw [Finset.mem_singleton] at hk; rw [hk]; exact ht
  have hsing : ∀ k k' : ℝ × ℝ, k' ∈ ({k} : Finset (ℝ × ℝ)) → k' ≠ k →
      M.util θ k' < M.util θ k := fun k k' hk' hne =>
    absurd (Finset.mem_singleton.1 hk') hne
  -- some contract is chosen
  obtain ⟨k, hk⟩ : ∃ k, M.Chooses θ (A₁ ∪ A₂) k := by
    by_contra hno
    have hneg : ∀ k' ∈ A₂, M.util θ k' < M.util θ (θ / 2, 0) := by
      intro k' hk'
      by_contra hle
      exact hno (exists_chooses θ ⟨k', Finset.mem_union_right _ hk', by
        simp only [util, hM.c_zero] at hle ⊢; linarith⟩)
    have hcap := typeProfit_capture (M := M) (other := A₂) (Finset.mem_singleton_self _)
      (by simp only [util, hM.c_zero]; linarith) hneg (hsing _)
    have := h.2.2.1 {(θ / 2, 0)} (hvs _ _ le_rfl)
    rw [hcap, typeProfit_of_not hno] at this
    linarith
  have hsum := typeProfit_add hk
  -- undercutting: a firm with at most half the market gains by raising the wage slightly
  have hundercut : ∀ own other, M.IsTypeEq θ own other → M.Chooses θ (own ∪ other) k →
      share own other k ≤ 1 / 2 → θ - k.1 ≤ 0 := by
    intro own other he hkc hsh
    by_contra hpos
    rw [not_le] at hpos
    set ε := (θ - k.1) / 4
    have hε : 0 < ε := by simp only [ε]; linarith
    have hval : 0 ≤ k.2 := by
      rcases Finset.mem_union.1 hkc.1 with h' | h'
      · exact he.1 k h'
      · exact he.2.1 k h'
    have hbetter : ∀ k' ∈ other, M.util θ k' < M.util θ (k.1 + ε, k.2) := fun k' hk' => by
      have := hkc.2.2.1 k' (Finset.mem_union_right _ hk')
      simp only [util] at this ⊢; linarith
    have hcap := typeProfit_capture (M := M) (Finset.mem_singleton_self (k.1 + ε, k.2))
      (by have := hkc.2.1; simp only [util] at this ⊢; linarith) hbetter (hsing _)
    have := he.2.2.1 {(k.1 + ε, k.2)} (hvs _ _ hval)
    rw [hcap, typeProfit_of_chooses hkc] at this
    simp only at this
    have hhalf : share own other k * (θ - k.1) ≤ 1 / 2 * (θ - k.1) :=
      mul_le_mul_of_nonneg_right hsh hpos.le
    simp only [ε] at this
    linarith
  have hPi : θ - k.1 ≤ 0 := by
    have hsa := share_add (own := A₁) (other := A₂) hk.1
    by_cases h1 : share A₁ A₂ k ≤ 1 / 2
    · exact hundercut A₁ A₂ h hk h1
    · have h2 : share A₂ A₁ k ≤ 1 / 2 := by linarith
      exact hundercut A₂ A₁ h.symm (by rwa [Finset.union_comm]) h2
  have hw : k.1 = θ := by linarith
  have hP1 : M.typeProfit θ A₁ A₂ = 0 := by linarith
  have hP2 : M.typeProfit θ A₂ A₁ = 0 := by linarith
  refine ⟨?_, hP1, hP2⟩
  -- the task level is zero
  have ht : k.2 = 0 := by
    have hval : 0 ≤ k.2 := by
      rcases Finset.mem_union.1 hk.1 with h' | h'
      · exact hval1 k h'
      · exact hval2 k h'
    by_contra hne
    have htpos : 0 < k.2 := lt_of_le_of_ne hval (Ne.symm hne)
    have hc : 0 < M.c k.2 θ := hM.c_pos b htpos
    set δ := min (M.c k.2 θ) θ / 2
    have hδ : 0 < δ := by simp only [δ]; exact half_pos (lt_min hc hθ)
    have hδc : δ < M.c k.2 θ := by
      simp only [δ]; linarith [min_le_left (M.c k.2 θ) θ]
    have hδθ : δ < θ := by simp only [δ]; linarith [min_le_right (M.c k.2 θ) θ]
    have hbetter : ∀ k' ∈ A₂, M.util θ k' < M.util θ (θ - δ, 0) := fun k' hk' => by
      have := hk.2.2.1 k' (Finset.mem_union_right _ hk')
      simp only [util, hM.c_zero] at this ⊢; rw [hw] at this; linarith
    have hcap := typeProfit_capture (M := M) (Finset.mem_singleton_self (θ - δ, 0))
      (by simp only [util, hM.c_zero]; linarith) hbetter (hsing _)
    have := h.2.2.1 {(θ - δ, 0)} (hvs _ _ le_rfl)
    rw [hcap, hP1] at this
    simp only at this
    linarith
  have hkeq : k = (θ, 0) := Prod.ext hw ht
  rwa [hkeq] at hk

/-- **Proposition 13.D.1** (MWG, p. 461), existence: both firms offering only `(θ, 0)` is an
SPNE of the observable-types game. -/
theorem proposition_13_D_1_exists (hM : M.Valid) (b : Bool) :
    M.IsTypeEq (M.θ b) {(M.θ b, 0)} {(M.θ b, 0)} := by
  have hθ : 0 < M.θ b := by
    cases b
    · exact hM.θL_pos
    · exact hM.θL_pos.trans hM.lt
  have hv : ValidMenu {(M.θ b, 0)} := fun k hk => by rw [Finset.mem_singleton.1 hk]
  have hzero : M.typeProfit (M.θ b) {(M.θ b, 0)} {(M.θ b, 0)} = 0 := by
    have hch : M.Chooses (M.θ b) ({(M.θ b, 0)} ∪ {(M.θ b, 0)}) (M.θ b, 0) := by
      refine chooses_of_strict (by simp) (by simp only [util, hM.c_zero, sub_zero]; exact hθ.le) ?_
      intro k' hk' hne
      rw [Finset.union_self, Finset.mem_singleton] at hk'
      exact absurd hk' hne
    rw [typeProfit_of_chooses hch]; simp
  have hdev : ∀ B, ValidMenu B →
      M.typeProfit (M.θ b) B {(M.θ b, 0)} ≤ M.typeProfit (M.θ b) {(M.θ b, 0)} {(M.θ b, 0)} := by
    intro B hB
    rw [hzero]
    by_cases hex : ∃ k, M.Chooses (M.θ b) (B ∪ {(M.θ b, 0)}) k
    · obtain ⟨k, hk⟩ := hex
      rw [typeProfit_of_chooses hk]
      have hge := hk.2.2.1 (M.θ b, 0) (by simp)
      simp only [util, hM.c_zero, sub_zero] at hge
      have hk2 : 0 ≤ k.2 := by
        rcases Finset.mem_union.1 hk.1 with h' | h'
        · exact hB k h'
        · rw [Finset.mem_singleton.1 h']
      have hc := hM.c_nonneg b hk2
      exact mul_nonpos_of_nonneg_of_nonpos (share_nonneg _ _ _) (by linarith)
    · rw [typeProfit_of_not hex]
  exact ⟨hv, hv, hdev, hdev⟩

end SigModel

end MWG.AdverseSelection
