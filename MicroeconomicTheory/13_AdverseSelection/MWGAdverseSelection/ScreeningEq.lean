/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGAdverseSelection.Screening
import MWGAdverseSelection.CrossSubsidy

/-!
# Equilibria of the screening game with unobservable types

MWG, Section 13.D, pp. 462-466.

Throughout, `(A₁, A₂)` is a pure SPNE; `kL`, `kH` are the contracts chosen by the low and high
types. Both types accept some contract in every SPNE (p. 462, `IsScreenEq.exists_bothEmployed`),
so `BothEmployed` only names the chosen contracts.

* `lemma_13_D_1`: both firms earn zero profits.
* `lemma_13_D_2`: no pooling equilibrium exists.
* `lemma_13_D_3`: in a separating equilibrium `w_L = θ_L` and `w_H = θ_H`.
* `lemma_13_D_4`: the low type accepts `(θ_L, 0)`.
* `lemma_13_D_5`: the high type accepts `(θ_H, t̂_H)`, `θ_H - c(t̂_H, θ_L) = θ_L - c(0, θ_L)`.
* `proposition_13_D_2`: the two together.
* `no_eq_of_pooling_deviation`, `no_eq_of_pair_deviation` (pp. 465-466, Figures 13.D.7(b) and
  13.D.8): an SPNE cannot exist if a single pooling contract, or a pair of contracts, attracts the
  workers away from the Proposition 13.D.2 contracts at a profit; instances
  `nonexistence_pooling_instance` and `nonexistence_pair_instance`.
-/

namespace MWG.AdverseSelection

namespace SigModel

variable {M : SigModel}

/-- Both types accept a contract in the SPNE. -/
def BothEmployed (M : SigModel) (A₁ A₂ : Finset (ℝ × ℝ)) (kL kH : ℝ × ℝ) : Prop :=
  M.Chooses M.θL (A₁ ∪ A₂) kL ∧ M.Chooses M.θH (A₁ ∪ A₂) kH

theorem IsScreenEq.symm {A₁ A₂ : Finset (ℝ × ℝ)} (h : M.IsScreenEq A₁ A₂) :
    M.IsScreenEq A₂ A₁ := ⟨h.2.1, h.1, h.2.2.2, h.2.2.1⟩

theorem BothEmployed.symm {A₁ A₂ : Finset (ℝ × ℝ)} {kL kH : ℝ × ℝ}
    (h : M.BothEmployed A₁ A₂ kL kH) : M.BothEmployed A₂ A₁ kL kH := by
  unfold BothEmployed; rwa [Finset.union_comm]

/-- Equilibrium profits are nonnegative (a firm can offer nothing). -/
theorem IsScreenEq.nonneg {A₁ A₂ : Finset (ℝ × ℝ)} (h : M.IsScreenEq A₁ A₂) :
    0 ≤ M.screenProfit A₁ A₂ := by
  have := h.2.2.1 ∅ (fun _ h => absurd h (Finset.notMem_empty _))
  rwa [screenProfit_empty] at this

/-- The firms' profits add up to the total `(1 - λ)(θ_L - w_L) + λ(θ_H - w_H)`. -/
theorem screenProfit_add {A₁ A₂ : Finset (ℝ × ℝ)} {kL kH : ℝ × ℝ}
    (h : M.BothEmployed A₁ A₂ kL kH) :
    M.screenProfit A₁ A₂ + M.screenProfit A₂ A₁ =
      (1 - M.lam) * (M.θL - kL.1) + M.lam * (M.θH - kH.1) := by
  have h1 := typeProfit_add h.1
  have h2 := typeProfit_add h.2
  unfold screenProfit
  rw [← h1, ← h2]; ring

/-- Chosen contracts in a valid pair of menus have `t ≥ 0`. -/
theorem chosen_valid {θ : ℝ} {A₁ A₂ : Finset (ℝ × ℝ)} (h1 : ValidMenu A₁) (h2 : ValidMenu A₂)
    {k : ℝ × ℝ} (hk : M.Chooses θ (A₁ ∪ A₂) k) : 0 ≤ k.2 := by
  rcases Finset.mem_union.1 hk.1 with h | h
  · exact h1 k h
  · exact h2 k h

/-- A deviation `{k̃}` that type `θ_H` strictly prefers to every contract of the other firm while
type `θ_L` strictly prefers one of them to `k̃` earns `λ(θ_H - w̃)`. -/
theorem screenProfit_capture_high {other : Finset (ℝ × ℝ)} {k k0 : ℝ × ℝ} (hk0 : k0 ∈ other)
    (hL : M.util M.θL k < M.util M.θL k0) (h0 : 0 ≤ M.util M.θH k)
    (hH : ∀ k' ∈ other, M.util M.θH k' < M.util M.θH k) :
    M.screenProfit {k} other = M.lam * (M.θH - k.1) := by
  have hcapH := typeProfit_capture (M := M) (Finset.mem_singleton_self k) h0 hH
    (fun k' hk' hne => absurd (Finset.mem_singleton.1 hk') hne)
  have hL0 : M.typeProfit M.θL {k} other = 0 := by
    by_cases hex : ∃ k', M.Chooses M.θL ({k} ∪ other) k'
    · obtain ⟨k', hk'⟩ := hex
      have hne : k' ≠ k := by
        rintro rfl
        exact absurd (hk'.2.2.1 k0 (Finset.mem_union_right _ hk0)) (not_le.2 hL)
      rw [typeProfit_of_chooses hk']
      simp [share, hne]
    · exact typeProfit_of_not hex
  simp [screenProfit, hcapH, hL0]

/-- A deviation `{k̃}` that type `θ_L` strictly prefers to every contract of the other firm, with
`w̃ < θ_L`, is profitable. -/
theorem screenProfit_capture_low_pos (hM : M.Valid) {other : Finset (ℝ × ℝ)} {k : ℝ × ℝ}
    (h0 : 0 ≤ M.util M.θL k) (hL : ∀ k' ∈ other, M.util M.θL k' < M.util M.θL k)
    (hw : k.1 < M.θL) : 0 < M.screenProfit {k} other := by
  have hcapL := typeProfit_capture (M := M) (Finset.mem_singleton_self k) h0 hL
    (fun k' hk' hne => absurd (Finset.mem_singleton.1 hk') hne)
  have hH0 : 0 ≤ M.typeProfit M.θH {k} other := by
    by_cases hex : ∃ k', M.Chooses M.θH ({k} ∪ other) k'
    · obtain ⟨k', hk'⟩ := hex
      rw [typeProfit_of_chooses hk']
      by_cases hk'k : k' = k
      · subst hk'k
        exact mul_nonneg (share_nonneg _ _ _) (by linarith [hM.lt])
      · simp [share, hk'k]
    · exact (typeProfit_of_not hex).ge
  unfold screenProfit
  rw [hcapL]
  have := hM.lam_lt
  have := hM.lam_pos
  nlinarith

/-- **Section 13.D** (MWG, p. 462). In any SPNE both types accept some contract ("it is not
difficult to see"). If the high type works nowhere, neither does the low type and the contract
`(θ_L/2, 0)` is profitable; if only the low type is idle, a firm gains by raising the high
type's contract by a small `ε` and adding `(ε/2, 0)`. -/
theorem IsScreenEq.exists_bothEmployed (hM : M.Valid) {A₁ A₂ : Finset (ℝ × ℝ)}
    (h : M.IsScreenEq A₁ A₂) : ∃ kL kH, M.BothEmployed A₁ A₂ kL kH := by
  have hlam0 := hM.lam_pos
  have hlam1 := hM.lam_lt
  have hθL := hM.θL_pos
  have hθ := hM.lt
  have hval : ∀ k ∈ A₁ ∪ A₂, 0 ≤ k.2 := fun k hk => by
    rcases Finset.mem_union.1 hk with hk | hk
    · exact h.1 k hk
    · exact h.2.1 k hk
  have hneg : ∀ θ, (¬ ∃ k, M.Chooses θ (A₁ ∪ A₂) k) → ∀ k ∈ A₁ ∪ A₂, M.util θ k < 0 := by
    intro θ hno k hk
    by_contra hle
    exact hno (exists_chooses θ ⟨k, hk, not_lt.1 hle⟩)
  have hu0 : ∀ θ w, M.util θ (w, 0) = w := fun θ w => by simp [util, hM.c_zero]
  -- the high type works
  obtain ⟨kH, hkH⟩ : ∃ kH, M.Chooses M.θH (A₁ ∪ A₂) kH := by
    by_contra hnoH
    have hnH := hneg _ hnoH
    have hnL : ∀ k ∈ A₁ ∪ A₂, M.util M.θL k < 0 := fun k hk => by
      have h1 := hnH k hk
      have h2 := hM.c_le (hval k hk)
      simp only [util] at h1 ⊢
      linarith
    have hnoL : ¬ ∃ k, M.Chooses M.θL (A₁ ∪ A₂) k := fun ⟨k, hk⟩ =>
      absurd hk.2.1 (not_le.2 (hnL k hk.1))
    have hp0 : M.screenProfit A₁ A₂ = 0 := by
      simp [screenProfit, typeProfit_of_not hnoL, typeProfit_of_not hnoH]
    have hcap : ∀ θ, (∀ k' ∈ A₁ ∪ A₂, M.util θ k' < 0) →
        M.typeProfit θ {(M.θL / 2, 0)} A₂ = θ - M.θL / 2 := by
      intro θ hn
      have := typeProfit_capture (M := M) (θ := θ) (other := A₂)
        (Finset.mem_singleton_self (M.θL / 2, (0 : ℝ))) (by rw [hu0]; linarith)
        (fun k' hk' => (hn k' (Finset.mem_union_right _ hk')).trans (by rw [hu0]; linarith))
        (fun k' hk' hne => absurd (Finset.mem_singleton.1 hk') hne)
      simpa using this
    have hd := h.2.2.1 {(M.θL / 2, 0)} (fun k' hk' => by rw [Finset.mem_singleton.1 hk'])
    rw [hp0] at hd
    simp only [screenProfit, hcap _ hnL, hcap _ hnH] at hd
    nlinarith [mul_pos (sub_pos.2 hlam1) hθL, mul_pos hlam0 (by linarith : 0 < M.θH - M.θL / 2)]
  -- the low type works
  obtain ⟨kL, hkL⟩ : ∃ kL, M.Chooses M.θL (A₁ ∪ A₂) kL := by
    by_contra hnoL
    have hnL := hneg _ hnoL
    have hLkH : M.util M.θL kH < 0 := hnL kH hkH.1
    set ε := min (-(M.util M.θL kH) / 2) ((1 - M.lam) * M.θL / 2) with hεdef
    have hεa : ε ≤ -(M.util M.θL kH) / 2 := min_le_left _ _
    have hεb : ε ≤ (1 - M.lam) * M.θL / 2 := min_le_right _ _
    have hε : 0 < ε := lt_min (by linarith) (by nlinarith)
    have hutil : ∀ θ, M.util θ (kH.1 + ε, kH.2) = M.util θ kH + ε := fun θ => by
      simp only [util]; ring
    have hpH : M.typeProfit M.θH {(ε / 2, 0), (kH.1 + ε, kH.2)} A₂ = M.θH - (kH.1 + ε) := by
      refine typeProfit_capture (θ := M.θH) (other := A₂)
        (B := {(ε / 2, 0), (kH.1 + ε, kH.2)}) (k := (kH.1 + ε, kH.2)) (by simp)
        (by rw [hutil]; linarith [hkH.2.1])
        (fun k' hk' => by rw [hutil]; linarith [hkH.2.2.1 k' (Finset.mem_union_right _ hk')])
        (fun k' hk' hne' => ?_)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk'
      rcases hk' with hk' | hk'
      · rw [hk', hu0, hutil]; linarith [hkH.2.1]
      · exact absurd hk' hne'
    have hpL : M.typeProfit M.θL {(ε / 2, 0), (kH.1 + ε, kH.2)} A₂ = M.θL - ε / 2 := by
      refine typeProfit_capture (θ := M.θL) (other := A₂)
        (B := {(ε / 2, 0), (kH.1 + ε, kH.2)}) (k := (ε / 2, 0)) (by simp)
        (by rw [hu0]; linarith)
        (fun k' hk' => by rw [hu0]; linarith [hnL k' (Finset.mem_union_right _ hk')])
        (fun k' hk' hne' => ?_)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk'
      rcases hk' with hk' | hk'
      · exact absurd hk' hne'
      · rw [hk', hu0, hutil]; linarith
    have hnoL' : ¬ ∃ k, M.Chooses M.θL (A₂ ∪ A₁) k := by rwa [Finset.union_comm]
    have htot : M.screenProfit A₁ A₂ + M.screenProfit A₂ A₁ = M.lam * (M.θH - kH.1) := by
      have := typeProfit_add hkH
      unfold screenProfit
      rw [typeProfit_of_not hnoL, typeProfit_of_not hnoL', ← this]
      ring
    have h2nn := h.symm.nonneg
    have hB : ValidMenu {(ε / 2, 0), (kH.1 + ε, kH.2)} := by
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with hk | hk <;> rw [hk]
      exact hval kH hkH.1
    have hd := h.2.2.1 _ hB
    have hdev : M.screenProfit {(ε / 2, 0), (kH.1 + ε, kH.2)} A₂ =
        (1 - M.lam) * (M.θL - ε / 2) + M.lam * (M.θH - (kH.1 + ε)) := by
      unfold screenProfit; rw [hpH, hpL]
    rw [hdev] at hd
    nlinarith [mul_le_mul_of_nonneg_left hεb (by linarith : (0 : ℝ) ≤ 1 + M.lam),
      mul_pos (mul_pos (sub_pos.2 hlam1) hθL) (by linarith : (0 : ℝ) < 3 - M.lam)]
  exact ⟨kL, kH, hkL, hkH⟩

/-- Lemma 13.D.1 for given chosen contracts `kL`, `kH`. -/
theorem zero_profits_of_employed {A₁ A₂ : Finset (ℝ × ℝ)} {kL kH : ℝ × ℝ}
    (h : M.IsScreenEq A₁ A₂) (he : M.BothEmployed A₁ A₂ kL kH) :
    M.screenProfit A₁ A₂ = 0 ∧ M.screenProfit A₂ A₁ = 0 := by
  have hsum := screenProfit_add he
  have hn1 := h.nonneg
  have hn2 := h.symm.nonneg
  -- raising both chosen contracts' wages by `ε` captures everybody
  have hdev : ∀ own other, M.IsScreenEq own other → M.BothEmployed own other kL kH →
      ∀ ε, 0 < ε → (1 - M.lam) * (M.θL - kL.1) + M.lam * (M.θH - kH.1) - ε ≤
        M.screenProfit own other := by
    intro own other heq hem ε hε
    set kL' : ℝ × ℝ := (kL.1 + ε, kL.2)
    set kH' : ℝ × ℝ := (kH.1 + ε, kH.2)
    set B : Finset (ℝ × ℝ) := {kL', kH'}
    have hB : ValidMenu B := by
      intro k hk
      simp only [B, Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with hk | hk <;> rw [hk]
      · change 0 ≤ kL.2; exact chosen_valid heq.1 heq.2.1 hem.1
      · change 0 ≤ kH.2; exact chosen_valid heq.1 heq.2.1 hem.2
    have hutil : ∀ θ k, M.util θ (k.1 + ε, k.2) = M.util θ k + ε := fun θ k => by
      simp only [util]; ring
    -- type `θ` with chosen contract `k` chooses `k + ε`
    have hcap : ∀ θ k k2, M.Chooses θ (own ∪ other) k → k2 ∈ own ∪ other →
        M.typeProfit θ {(k.1 + ε, k.2), (k2.1 + ε, k2.2)} other = θ - (k.1 + ε) := by
      intro θ k k2 hk hk2
      have hch : M.Chooses θ ({(k.1 + ε, k.2), (k2.1 + ε, k2.2)} ∪ other) (k.1 + ε, k.2) := by
        refine ⟨by simp, by rw [hutil]; linarith [hk.2.1], fun k' hk' => ?_, fun k' hk' hu => ?_⟩
        · rw [hutil]
          simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hk'
          rcases hk' with (rfl | rfl) | h'
          · rw [hutil]
          · rw [hutil]; linarith [hk.2.2.1 k2 hk2]
          · linarith [hk.2.2.1 k' (Finset.mem_union_right _ h')]
        · rw [hutil] at hu
          simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hk'
          rcases hk' with (rfl | rfl) | h'
          · exact le_rfl
          · rw [hutil] at hu
            exact hk.2.2.2 k2 hk2 (by linarith)
          · exfalso
            linarith [hk.2.2.1 k' (Finset.mem_union_right _ h')]
      have hno : (k.1 + ε, k.2) ∉ other := fun hm => by
        have := hk.2.2.1 _ (Finset.mem_union_right _ hm)
        rw [hutil] at this; linarith
      rw [typeProfit_of_chooses hch]
      simp [share, hno]
    have hpL := hcap M.θL kL kH hem.1 hem.2.1
    have hpH := hcap M.θH kH kL hem.2 hem.1.1
    rw [Finset.pair_comm] at hpH
    have := heq.2.2.1 B hB
    simp only [screenProfit, B, kL', kH', hpL, hpH] at this ⊢
    linarith
  set tot := (1 - M.lam) * (M.θL - kL.1) + M.lam * (M.θH - kH.1)
  have htot : tot ≤ 0 := by
    by_contra hpos
    rw [not_le] at hpos
    rcases le_total (M.screenProfit A₁ A₂) (M.screenProfit A₂ A₁) with hle | hle
    · have := hdev A₁ A₂ h he (tot / 4) (by linarith)
      linarith
    · have := hdev A₂ A₁ h.symm he.symm (tot / 4) (by linarith)
      linarith
  constructor <;> linarith

/-- **Lemma 13.D.1** (MWG, pp. 462-463). In any SPNE both firms earn zero profits. (The book
assumes both types accept a contract; `IsScreenEq.exists_bothEmployed` proves it.) -/
theorem lemma_13_D_1 (hM : M.Valid) {A₁ A₂ : Finset (ℝ × ℝ)} (h : M.IsScreenEq A₁ A₂) :
    M.screenProfit A₁ A₂ = 0 ∧ M.screenProfit A₂ A₁ = 0 := by
  obtain ⟨kL, kH, he⟩ := h.exists_bothEmployed hM
  exact zero_profits_of_employed h he

/-- A contract `k̃` near `k` that the high type strictly prefers and the low type strictly
dislikes, with wage below `w + gap` (single crossing). -/
theorem exists_high_dev (hM : M.Valid) {k : ℝ × ℝ} (hk : 0 ≤ k.2) {gap : ℝ} (hgap : 0 < gap) :
    ∃ k' : ℝ × ℝ, 0 ≤ k'.2 ∧ M.util M.θH k < M.util M.θH k' ∧ M.util M.θL k' < M.util M.θL k ∧
      k'.1 < k.1 + gap := by
  have hc : ContinuousWithinAt (fun x => M.c x (M.θ false)) (Set.Ioi k.2) k.2 :=
    ((hM.c_cont false) k.2 hk).mono fun x hx => hk.trans (le_of_lt hx)
  have hev : ∀ᶠ x in nhdsWithin k.2 (Set.Ioi k.2), M.c x M.θL < M.c k.2 M.θL + gap :=
    hc.eventually (gt_mem_nhds (by simp only [θ_false]; linarith))
  obtain ⟨x, hx, hxk⟩ := (hev.and self_mem_nhdsWithin).exists
  have hsc := hM.sc k.2 x hk hxk
  have hL := hM.c_mono false hk (hk.trans (le_of_lt hxk)) hxk
  simp only [θ_false] at hL
  set Δ := ((M.c x M.θL - M.c k.2 M.θL) + (M.c x M.θH - M.c k.2 M.θH)) / 2
  refine ⟨(k.1 + Δ, x), hk.trans (le_of_lt hxk), ?_, ?_, ?_⟩
  · simp only [util, Δ]; linarith
  · simp only [util, Δ]; linarith
  · simp only [Δ]; linarith

/-- **Lemma 13.D.2** (MWG, p. 463). No pooling equilibrium exists. -/
theorem lemma_13_D_2 (hM : M.Valid) {A₁ A₂ : Finset (ℝ × ℝ)} {kL kH : ℝ × ℝ}
    (h : M.IsScreenEq A₁ A₂) (he : M.BothEmployed A₁ A₂ kL kH) : kL ≠ kH := by
  intro hpool
  subst hpool
  obtain ⟨h1, h2⟩ := zero_profits_of_employed h he
  have hsum := screenProfit_add he
  rw [h1, h2] at hsum
  have hp1 : kL.1 = M.Eθ := by unfold Eθ; linarith
  have hgap : 0 < M.θH - M.Eθ := by linarith [hM.Eθ_mem.2]
  obtain ⟨k', hk'0, hH, hL, hw⟩ :=
    exists_high_dev hM (chosen_valid h.1 h.2.1 he.1) hgap
  -- the firm not offering the pooling contract deviates
  have key : ∀ own other, M.IsScreenEq own other → M.BothEmployed own other kL kL →
      M.screenProfit own other = 0 → kL ∈ other → False := by
    intro own other heq hem hz hmem
    have hprof := screenProfit_capture_high (M := M) hmem hL
      (hem.2.2.1.trans hH.le) (fun k'' hk'' =>
        lt_of_le_of_lt (hem.2.2.2.1 k'' (Finset.mem_union_right _ hk'')) hH)
    have := heq.2.2.1 {k'} (fun k hk => by rw [Finset.mem_singleton.1 hk]; exact hk'0)
    rw [hprof, hz] at this
    nlinarith [hM.lam_pos]
  rcases Finset.mem_union.1 he.1.1 with hm | hm
  · exact key A₂ A₁ h.symm he.symm h2 hm
  · exact key A₁ A₂ h he h1 hm

/-- In equilibrium no single-contract deviation captures the low type at a wage below `θ_L`. -/
theorem no_low_capture (hM : M.Valid) {A₁ A₂ : Finset (ℝ × ℝ)} {kL kH : ℝ × ℝ}
    (h : M.IsScreenEq A₁ A₂) (he : M.BothEmployed A₁ A₂ kL kH) {k : ℝ × ℝ} (hk : 0 ≤ k.2)
    (hu : M.util M.θL kL < M.util M.θL k) (hw : k.1 < M.θL) : False := by
  have h1 := (zero_profits_of_employed h he).1
  have hpos := screenProfit_capture_low_pos hM (other := A₂) (k := k)
    (he.1.2.1.trans hu.le) (fun k' hk' => lt_of_le_of_lt
      (he.1.2.2.1 k' (Finset.mem_union_right _ hk')) hu) hw
  have := h.2.2.1 {k} (fun k' hk' => by rw [Finset.mem_singleton.1 hk']; exact hk)
  linarith

/-- **Lemma 13.D.3** (MWG, pp. 463-464). In a separating equilibrium the contracts make zero
profits: `w_L = θ_L` and `w_H = θ_H`. -/
theorem lemma_13_D_3 (hM : M.Valid) {A₁ A₂ : Finset (ℝ × ℝ)} {kL kH : ℝ × ℝ}
    (h : M.IsScreenEq A₁ A₂) (he : M.BothEmployed A₁ A₂ kL kH) :
    kL.1 = M.θL ∧ kH.1 = M.θH := by
  obtain ⟨h1, h2⟩ := zero_profits_of_employed h he
  have hsum := screenProfit_add he
  rw [h1, h2] at hsum
  have hLv := chosen_valid h.1 h.2.1 he.1
  have hHv := chosen_valid h.1 h.2.1 he.2
  have hwL : M.θL ≤ kL.1 := by
    by_contra hlt
    rw [not_le] at hlt
    refine no_low_capture hM h he (k := ((kL.1 + M.θL) / 2, kL.2)) hLv ?_ (by simp; linarith)
    simp only [util]; linarith
  have hwH : M.θH ≤ kH.1 := by
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨k', hk'0, hH, hL, hw⟩ := exists_high_dev hM hHv (sub_pos.2 hlt)
    have hLk : M.util M.θL k' < M.util M.θL kL := hL.trans_le (he.1.2.2.1 kH he.2.1)
    have key : ∀ own other, M.IsScreenEq own other → M.BothEmployed own other kL kH →
        M.screenProfit own other = 0 → kL ∈ other → False := by
      intro own other heq hem hz hmem
      have hprof := screenProfit_capture_high (M := M) hmem hLk (hem.2.2.1.trans hH.le)
        (fun k'' hk'' => lt_of_le_of_lt (hem.2.2.2.1 k'' (Finset.mem_union_right _ hk'')) hH)
      have := heq.2.2.1 {k'} (fun k hk => by rw [Finset.mem_singleton.1 hk]; exact hk'0)
      rw [hprof, hz] at this
      nlinarith [hM.lam_pos]
    rcases Finset.mem_union.1 he.1.1 with hm | hm
    · exact key A₂ A₁ h.symm he.symm h2 hm
    · exact key A₁ A₂ h he h1 hm
  have := hM.lam_pos
  have := hM.lam_lt
  constructor <;> nlinarith

/-- **Lemma 13.D.4** (MWG, p. 464). The low type accepts `(θ_L, 0)`. -/
theorem lemma_13_D_4 (hM : M.Valid) {A₁ A₂ : Finset (ℝ × ℝ)} {kL kH : ℝ × ℝ}
    (h : M.IsScreenEq A₁ A₂) (he : M.BothEmployed A₁ A₂ kL kH) : kL = (M.θL, 0) := by
  have hw := (lemma_13_D_3 hM h he).1
  have hLv := chosen_valid h.1 h.2.1 he.1
  refine Prod.ext hw ?_
  by_contra hne
  have htpos : 0 < kL.2 := lt_of_le_of_ne hLv (Ne.symm hne)
  have hc : 0 < M.c kL.2 M.θL := by have := hM.c_pos false htpos; simpa only [θ_false] using this
  set w := M.θL - min (M.c kL.2 M.θL) M.θL / 2
  have hm1 := min_le_left (M.c kL.2 M.θL) M.θL
  have hm0 : 0 < min (M.c kL.2 M.θL) M.θL := lt_min hc hM.θL_pos
  refine no_low_capture hM h he (k := (w, 0)) le_rfl ?_ (by simp only [w]; linarith)
  simp only [util, hM.c_zero, sub_zero, w, hw]
  linarith

/-- **Lemma 13.D.5** (MWG, pp. 464-465). The high type accepts `(θ_H, t̂_H)` where
`θ_H - c(t̂_H, θ_L) = θ_L - c(0, θ_L)`. -/
theorem lemma_13_D_5 (hM : M.Valid) {A₁ A₂ : Finset (ℝ × ℝ)} {kL kH : ℝ × ℝ}
    (h : M.IsScreenEq A₁ A₂) (he : M.BothEmployed A₁ A₂ kL kH) {th : ℝ} (hth : 0 ≤ th)
    (hcth : M.θH - M.c th M.θL = M.θL - M.c 0 M.θL) : kH = (M.θH, th) := by
  have hwH := (lemma_13_D_3 hM h he).2
  have hkL := lemma_13_D_4 hM h he
  have hHv := chosen_valid h.1 h.2.1 he.2
  rw [hM.c_zero, sub_zero] at hcth
  have hLmono := (hM.c_mono false).le_iff_le hth hHv
  simp only [θ_false] at hLmono
  have hge : th ≤ kH.2 := by
    have := he.1.2.2.1 kH he.2.1
    simp only [util, hkL, hM.c_zero, sub_zero, hwH] at this
    exact hLmono.1 (by linarith)
  refine Prod.ext hwH ?_
  by_contra hne
  have hgt : th < kH.2 := lt_of_le_of_ne hge (Ne.symm hne)
  set t' := (th + kH.2) / 2
  have ht1 : th < t' := by simp only [t']; linarith
  have ht2 : t' < kH.2 := by simp only [t']; linarith
  have hcH := hM.c_mono true (hth.trans ht1.le) hHv ht2
  have hcL := hM.c_mono false hth (hth.trans ht1.le) ht1
  simp only [θ_true, θ_false] at hcH hcL
  set η := (M.c kH.2 M.θH - M.c t' M.θH) / 2
  have hη : 0 < η := by simp only [η]; linarith
  set k' : ℝ × ℝ := (M.θH - η, t')
  have hk'L : M.util M.θL k' < M.util M.θL kL := by
    simp only [util, k', hkL, hM.c_zero, sub_zero]; linarith
  have hk'H : M.util M.θH kH < M.util M.θH k' := by
    simp only [util, k', hwH]; simp only [η]; linarith
  have h1 := (zero_profits_of_employed h he).1
  have hB : ValidMenu (A₁ ∪ {k'}) := by
    intro k hk
    rcases Finset.mem_union.1 hk with hk | hk
    · exact h.1 k hk
    · rw [Finset.mem_singleton.1 hk]; exact hth.trans ht1.le
  -- the low type still chooses `kL`
  have hchL : M.Chooses M.θL ((A₁ ∪ {k'}) ∪ A₂) kL := by
    have hmem : kL ∈ (A₁ ∪ {k'}) ∪ A₂ := by
      rcases Finset.mem_union.1 he.1.1 with hm | hm
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ hm)
      · exact Finset.mem_union_right _ hm
    refine ⟨hmem, he.1.2.1, fun k hk => ?_, fun k hk hu => ?_⟩
    · rcases Finset.mem_union.1 hk with hk | hk
      · rcases Finset.mem_union.1 hk with hk | hk
        · exact he.1.2.2.1 k (Finset.mem_union_left _ hk)
        · rw [Finset.mem_singleton.1 hk]; exact hk'L.le
      · exact he.1.2.2.1 k (Finset.mem_union_right _ hk)
    · rcases Finset.mem_union.1 hk with hk | hk
      · rcases Finset.mem_union.1 hk with hk | hk
        · exact he.1.2.2.2 k (Finset.mem_union_left _ hk) hu
        · rw [Finset.mem_singleton.1 hk] at hu; exact absurd hu hk'L.ne
      · exact he.1.2.2.2 k (Finset.mem_union_right _ hk) hu
  have hpL : M.typeProfit M.θL (A₁ ∪ {k'}) A₂ = 0 := by
    rw [typeProfit_of_chooses hchL, hkL]; simp
  have hpH : M.typeProfit M.θH (A₁ ∪ {k'}) A₂ = M.θH - k'.1 := by
    refine typeProfit_capture (Finset.mem_union_right _ (Finset.mem_singleton_self _))
      (he.2.2.1.trans hk'H.le) (fun k hk => lt_of_le_of_lt
        (he.2.2.2.1 k (Finset.mem_union_right _ hk)) hk'H) fun k hk hne => ?_
    rcases Finset.mem_union.1 hk with hk | hk
    · exact lt_of_le_of_lt (he.2.2.2.1 k (Finset.mem_union_left _ hk)) hk'H
    · exact absurd (Finset.mem_singleton.1 hk) hne
  have := h.2.2.1 _ hB
  rw [h1] at this
  simp only [screenProfit, hpL, hpH, k'] at this
  nlinarith [hM.lam_pos]

/-- **Proposition 13.D.2** (MWG, p. 465). In any SPNE of the screening game the low type
accepts `(θ_L, 0)` and the high type `(θ_H, t̂_H)`, where `θ_H - c(t̂_H, θ_L) = θ_L - c(0, θ_L)`.
(Both types work by `IsScreenEq.exists_bothEmployed`.) -/
theorem proposition_13_D_2 (hM : M.Valid) {A₁ A₂ : Finset (ℝ × ℝ)}
    (h : M.IsScreenEq A₁ A₂) {th : ℝ} (hth : 0 ≤ th)
    (hcth : M.θH - M.c th M.θL = M.θL - M.c 0 M.θL) :
    M.Chooses M.θL (A₁ ∪ A₂) (M.θL, 0) ∧ M.Chooses M.θH (A₁ ∪ A₂) (M.θH, th) := by
  obtain ⟨kL, kH, he⟩ := h.exists_bothEmployed hM
  have h1 := lemma_13_D_4 hM h he
  have h2 := lemma_13_D_5 hM h he hth hcth
  exact ⟨h1 ▸ he.1, h2 ▸ he.2⟩

/-- **Section 13.D** (MWG, pp. 465-466, Figure 13.D.8). If a pair of contracts `(q_L, q_H)` that
each type strictly prefers (to the other one and to her Proposition 13.D.2 contract) yields a
positive profit, no SPNE exists. A single pooling contract is the case
`q_L = q_H` (Figure 13.D.7(b), `no_eq_of_pooling_deviation`). -/
theorem no_eq_of_pair_deviation (hM : M.Valid) {th : ℝ} (hth : 0 ≤ th)
    (hcth : M.θH - M.c th M.θL = M.θL - M.c 0 M.θL) {qL qH : ℝ × ℝ} (hqL : 0 ≤ qL.2)
    (hqH : 0 ≤ qH.2) (hLL : M.θL < M.util M.θL qL) (hLH : M.util M.θL qH ≤ M.util M.θL qL)
    (hHH : M.θH - M.c th M.θH < M.util M.θH qH) (hHL : M.util M.θH qL ≤ M.util M.θH qH)
    (htie : M.util M.θL qH = M.util M.θL qL → qL.2 ≤ qH.2)
    (htie' : M.util M.θH qL = M.util M.θH qH → qH.2 ≤ qL.2)
    (hprof : 0 < (1 - M.lam) * (M.θL - qL.1) + M.lam * (M.θH - qH.1)) :
    ¬ ∃ A₁ A₂, M.IsScreenEq A₁ A₂ := by
  rintro ⟨A₁, A₂, h⟩
  obtain ⟨kL, kH, he⟩ := h.exists_bothEmployed hM
  have hkL := lemma_13_D_4 hM h he
  have hkH := lemma_13_D_5 hM h he hth hcth
  have h1 := (zero_profits_of_employed h he).1
  have huL : ∀ k ∈ A₂, M.util M.θL k < M.util M.θL qL := fun k hk => by
    have := he.1.2.2.1 k (Finset.mem_union_right _ hk)
    have hu0 : M.util M.θL (M.θL, 0) = M.θL := by simp [util, hM.c_zero]
    rw [hkL, hu0] at this; linarith
  have huH : ∀ k ∈ A₂, M.util M.θH k < M.util M.θH qH := fun k hk => by
    have := he.2.2.2.1 k (Finset.mem_union_right _ hk)
    have hu0 : M.util M.θH (M.θH, th) = M.θH - M.c th M.θH := rfl
    rw [hkH, hu0] at this; linarith
  -- each type chooses her contract of the pair
  have hcL : M.Chooses M.θL ({qL, qH} ∪ A₂) qL := by
    refine ⟨by simp, by linarith [hM.θL_pos], fun k hk => ?_, fun k hk hu => ?_⟩
    · simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with (rfl | rfl) | hk
      · exact le_rfl
      · exact hLH
      · exact (huL k hk).le
    · simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with (rfl | rfl) | hk
      · exact le_rfl
      · exact htie hu
      · exact absurd hu (huL k hk).ne
  have hcH : M.Chooses M.θH ({qL, qH} ∪ A₂) qH := by
    have h0 : 0 ≤ M.θH - M.c th M.θH := by
      have := hM.c_le hth
      have hc' := hcth
      rw [hM.c_zero, sub_zero] at hc'
      linarith [hM.θL_pos]
    refine ⟨by simp, by linarith, fun k hk => ?_, fun k hk hu => ?_⟩
    · simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with (rfl | rfl) | hk
      · exact hHL
      · exact le_rfl
      · exact (huH k hk).le
    · simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with (rfl | rfl) | hk
      · exact htie' hu
      · exact le_rfl
      · exact absurd hu (huH k hk).ne
  have hnL : qL ∉ A₂ := fun hm => lt_irrefl _ (huL qL hm)
  have hnH : qH ∉ A₂ := fun hm => lt_irrefl _ (huH qH hm)
  have hpL : M.typeProfit M.θL {qL, qH} A₂ = M.θL - qL.1 := by
    rw [typeProfit_of_chooses hcL]; simp [share, hnL]
  have hpH : M.typeProfit M.θH {qL, qH} A₂ = M.θH - qH.1 := by
    rw [typeProfit_of_chooses hcH]; simp [share, hnH]
  have hB : ValidMenu {qL, qH} := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl <;> assumption
  have := h.2.2.1 _ hB
  rw [h1] at this
  simp only [screenProfit, hpL, hpH] at this
  linarith

/-- **Section 13.D** (MWG, p. 465, Figure 13.D.7(b)). If a pooling contract `(w̃, t̃)` with
`w̃ < E[θ]` gives both types more than their Proposition 13.D.2 contracts, no SPNE exists. -/
theorem no_eq_of_pooling_deviation (hM : M.Valid) {th : ℝ} (hth : 0 ≤ th)
    (hcth : M.θH - M.c th M.θL = M.θL - M.c 0 M.θL) {p : ℝ × ℝ} (hp : 0 ≤ p.2)
    (hL : M.θL < M.util M.θL p) (hH : M.θH - M.c th M.θH < M.util M.θH p) (hw : p.1 < M.Eθ) :
    ¬ ∃ A₁ A₂, M.IsScreenEq A₁ A₂ :=
  no_eq_of_pair_deviation hM hth hcth hp hp hL le_rfl hH le_rfl (fun _ => le_rfl)
    (fun _ => le_rfl) (by unfold Eθ at hw; nlinarith)

/-- The model of Exercise 13.C.3 with `λ = l`. -/
noncomputable def screenModel (l : ℝ) : SigModel := { crossModel with lam := l }

theorem screenModel_valid {l : ℝ} (h0 : 0 < l) (h1 : l < 1) : (screenModel l).Valid where
  θL_pos := crossModel_valid.θL_pos
  lt := crossModel_valid.lt
  lam_pos := h0
  lam_lt := h1
  r_nonneg := crossModel_valid.r_nonneg
  r_lt := crossModel_valid.r_lt
  c_zero := crossModel_valid.c_zero
  c_mono := crossModel_valid.c_mono
  c_cont := crossModel_valid.c_cont
  sc := crossModel_valid.sc

/-- **Section 13.D** (MWG, p. 465, Figure 13.D.7(b)), an instance: with `θ_L = 1`, `θ_H = 2`,
`c(t, θ_L) = t`, `c(t, θ_H) = t²/(1 + t)` (`t̂_H = 1`) and `λ = 3/4`, the pooling contract
`(8/5, 0)` breaks the separating contracts: no SPNE exists. -/
theorem nonexistence_pooling_instance :
    ¬ ∃ A₁ A₂, (screenModel (3 / 4)).IsScreenEq A₁ A₂ := by
  have hv := screenModel_valid (l := 3 / 4) (by norm_num) (by norm_num)
  refine no_eq_of_pooling_deviation hv (th := 1) zero_le_one ?_ (p := (8 / 5, 0)) le_rfl ?_ ?_ ?_
  all_goals simp [screenModel, crossModel, util, Eθ]
  all_goals norm_num

/-- **Section 13.D** (MWG, pp. 465-466, Figure 13.D.8), an instance: with the same costs and
`λ = 2/5` no single pooling contract breaks the separating contracts (`E[θ] = 7/5` is below the
high type's utility `3/2`), but the pair `(11/10, 0)`, `(46/25, 3/4)` does: no SPNE exists. -/
theorem nonexistence_pair_instance :
    (screenModel (2 / 5)).Eθ < (screenModel (2 / 5)).θH - (screenModel (2 / 5)).c 1
      (screenModel (2 / 5)).θH ∧
    ¬ ∃ A₁ A₂, (screenModel (2 / 5)).IsScreenEq A₁ A₂ := by
  have hv := screenModel_valid (l := 2 / 5) (by norm_num) (by norm_num)
  refine ⟨by simp [screenModel, crossModel, Eθ]; norm_num, ?_⟩
  refine no_eq_of_pair_deviation hv (th := 1) zero_le_one ?_ (qL := (11 / 10, 0))
    (qH := (46 / 25, 3 / 4)) le_rfl (by norm_num) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals simp [screenModel, crossModel, util]
  all_goals norm_num

end SigModel

end MWG.AdverseSelection
