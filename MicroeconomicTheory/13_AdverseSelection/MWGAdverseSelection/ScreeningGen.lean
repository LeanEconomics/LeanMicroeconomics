/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGAdverseSelection.Screening
import Mathlib.Topology.Algebra.Order.Field

/-!
# A general two-type screening game

MWG, Section 13.D, pp. 460-465, and Exercises 13.D.1-13.D.3 (p. 476).

The screening game of Section 13.D with a general space of contracts `k ∈ ℝ × ℝ`: type `b`
(`true` with probability `λ`, `false` with probability `1 - λ`) gets utility `U b k` from
contract `k`, and the firm that employs (or insures) her gets `P b k`. Two firms announce finite
menus of admissible contracts (`Menu`); each type chooses from the union of the menus
(`Chooses`): a utility maximizing contract with the lowest tie-breaking key `key k` among the
best ones, accepted iff its utility is at least the reservation utility `ρ b` (otherwise she
takes her outside option, which yields no profit). A firm gets a type if it offers her chosen
contract, half of the time if both firms offer it (`SigModel.share`). `IsEq` is the pure SPNE
(the Nash condition of Definition 8.D.1 given the stage-2 choices), as in `SigModel.IsScreenEq`.

The model of Section 13.D is the case `U b (w, t) = w - c(t, θ_b)`, `P b (w, t) = θ_b - w`,
`key (w, t) = t`; Exercises 13.D.1-13.D.3 are other cases.

* `IsEq.zero`: Lemma 13.D.1 in this generality. If raising every contract's utility uniformly
  (`sw δ`) keeps contracts admissible and tie-breaking keys, and changes profits continuously,
  then in every SPNE both firms earn zero profits.
* `typeProfit_capture`, `no_capture_of_other`, `typeProfit_nonneg_of`: profits of deviations.
-/

namespace MWG.AdverseSelection

/-- **Section 13.D** (MWG, pp. 460-461). A two-type screening game: utilities `U`, profits `P`,
reservation utilities `ρ`, the tie-breaking key, the probability `λ` of type `true`, and the
admissible contracts. -/
structure ScrGame where
  U : Bool → ℝ × ℝ → ℝ
  P : Bool → ℝ × ℝ → ℝ
  ρ : Bool → ℝ
  key : ℝ × ℝ → ℝ
  lam : ℝ
  adm : ℝ × ℝ → Prop

namespace ScrGame

variable (G : ScrGame)

/-- A menu: a finite set of admissible contracts. -/
def Menu (A : Finset (ℝ × ℝ)) : Prop := ∀ k ∈ A, G.adm k

/-- **Section 13.D** (MWG, p. 461). Type `b` chooses contract `k` from the offered set `V`. -/
def Chooses (b : Bool) (V : Finset (ℝ × ℝ)) (k : ℝ × ℝ) : Prop :=
  k ∈ V ∧ G.ρ b ≤ G.U b k ∧ (∀ k' ∈ V, G.U b k' ≤ G.U b k) ∧
    ∀ k' ∈ V, G.U b k' = G.U b k → G.key k ≤ G.key k'

/-- Contracts are identified by any type's utility and the tie-breaking key. -/
def Inj : Prop := ∀ b k k', G.U b k = G.U b k' → G.key k = G.key k' → k = k'

open Classical in
/-- The firm's expected profit from a worker of type `b`. -/
noncomputable def typeProfit (b : Bool) (own other : Finset (ℝ × ℝ)) : ℝ :=
  if h : ∃ k, G.Chooses b (own ∪ other) k then
    SigModel.share own other h.choose * G.P b h.choose else 0

/-- **Section 13.D** (MWG, p. 461). A firm's expected profit. -/
noncomputable def profit (own other : Finset (ℝ × ℝ)) : ℝ :=
  (1 - G.lam) * G.typeProfit false own other + G.lam * G.typeProfit true own other

/-- **Section 13.D** (MWG, p. 461). A pure strategy SPNE of the screening game. -/
def IsEq (A₁ A₂ : Finset (ℝ × ℝ)) : Prop :=
  G.Menu A₁ ∧ G.Menu A₂ ∧ (∀ B, G.Menu B → G.profit B A₂ ≤ G.profit A₁ A₂) ∧
    ∀ B, G.Menu B → G.profit B A₁ ≤ G.profit A₂ A₁

variable {G}

theorem chooses_unique (hI : G.Inj) {b : Bool} {V : Finset (ℝ × ℝ)} {k k' : ℝ × ℝ}
    (h : G.Chooses b V k) (h' : G.Chooses b V k') : k = k' := by
  have hu : G.U b k = G.U b k' := le_antisymm (h'.2.2.1 k h.1) (h.2.2.1 k' h'.1)
  exact hI b k k' hu (le_antisymm (h.2.2.2 k' h'.1 hu.symm) (h'.2.2.2 k h.1 hu))

theorem exists_chooses (b : Bool) {V : Finset (ℝ × ℝ)} (h : ∃ k ∈ V, G.ρ b ≤ G.U b k) :
    ∃ k, G.Chooses b V k := by
  obtain ⟨k0, hk0, hu0⟩ := h
  obtain ⟨k1, hk1, hmax⟩ := V.exists_max_image (G.U b) ⟨k0, hk0⟩
  set W := V.filter (fun k => G.U b k = G.U b k1)
  obtain ⟨k, hk, hmin⟩ := W.exists_min_image G.key ⟨k1, by simp [W, hk1]⟩
  simp only [W, Finset.mem_filter] at hk
  refine ⟨k, hk.1, by rw [hk.2]; exact hu0.trans (hmax k0 hk0), fun k' hk' => ?_,
    fun k' hk' he => hmin k' (by simp [W, hk', he.trans hk.2])⟩
  rw [hk.2]; exact hmax k' hk'

theorem chooses_of_strict {b : Bool} {V : Finset (ℝ × ℝ)} {k : ℝ × ℝ} (hk : k ∈ V)
    (h0 : G.ρ b ≤ G.U b k) (hs : ∀ k' ∈ V, k' ≠ k → G.U b k' < G.U b k) :
    G.Chooses b V k := by
  refine ⟨hk, h0, fun k' hk' => ?_, fun k' hk' he => ?_⟩
  · by_cases h : k' = k
    · rw [h]
    · exact (hs k' hk' h).le
  · by_cases h : k' = k
    · rw [h]
    · exact absurd he (hs k' hk' h).ne

theorem typeProfit_of_chooses (hI : G.Inj) {b : Bool} {own other : Finset (ℝ × ℝ)}
    {k : ℝ × ℝ} (h : G.Chooses b (own ∪ other) k) :
    G.typeProfit b own other = SigModel.share own other k * G.P b k := by
  have hex : ∃ k, G.Chooses b (own ∪ other) k := ⟨k, h⟩
  rw [typeProfit, dite_eq_left_of_eq_true (eq_true hex), chooses_unique hI hex.choose_spec h]

theorem typeProfit_of_not {b : Bool} {own other : Finset (ℝ × ℝ)}
    (h : ¬ ∃ k, G.Chooses b (own ∪ other) k) : G.typeProfit b own other = 0 := by
  rw [typeProfit, dite_eq_right_of_eq_false (eq_false h)]

/-- The firms' profits from type `b` add up to the profit on her chosen contract. -/
theorem typeProfit_add (hI : G.Inj) {b : Bool} {A₁ A₂ : Finset (ℝ × ℝ)} {k : ℝ × ℝ}
    (h : G.Chooses b (A₁ ∪ A₂) k) :
    G.typeProfit b A₁ A₂ + G.typeProfit b A₂ A₁ = G.P b k := by
  have h' : G.Chooses b (A₂ ∪ A₁) k := by rwa [Finset.union_comm]
  rw [typeProfit_of_chooses hI h, typeProfit_of_chooses hI h', ← add_mul,
    SigModel.share_add h.1, one_mul]

theorem typeProfit_add_not {b : Bool} {A₁ A₂ : Finset (ℝ × ℝ)}
    (h : ¬ ∃ k, G.Chooses b (A₁ ∪ A₂) k) :
    G.typeProfit b A₁ A₂ + G.typeProfit b A₂ A₁ = 0 := by
  have h' : ¬ ∃ k, G.Chooses b (A₂ ∪ A₁) k := by rwa [Finset.union_comm]
  rw [typeProfit_of_not h, typeProfit_of_not h', add_zero]

theorem typeProfit_empty (hI : G.Inj) (b : Bool) (other : Finset (ℝ × ℝ)) :
    G.typeProfit b ∅ other = 0 := by
  by_cases h : ∃ k, G.Chooses b (∅ ∪ other) k
  · obtain ⟨k, hk⟩ := h
    rw [typeProfit_of_chooses hI hk]; simp [SigModel.share]
  · exact typeProfit_of_not h

theorem profit_empty (hI : G.Inj) (other : Finset (ℝ × ℝ)) : G.profit ∅ other = 0 := by
  simp [profit, typeProfit_empty hI]

theorem IsEq.symm {A₁ A₂ : Finset (ℝ × ℝ)} (h : G.IsEq A₁ A₂) : G.IsEq A₂ A₁ :=
  ⟨h.2.1, h.1, h.2.2.2, h.2.2.1⟩

theorem menu_empty : G.Menu ∅ := fun _ h => absurd h (Finset.notMem_empty _)

/-- Equilibrium profits are nonnegative (a firm can offer nothing). -/
theorem IsEq.nonneg (hI : G.Inj) {A₁ A₂ : Finset (ℝ × ℝ)} (h : G.IsEq A₁ A₂) :
    0 ≤ G.profit A₁ A₂ := by
  have := h.2.2.1 ∅ menu_empty
  rwa [profit_empty hI] at this

/-- A deviation `B` containing a contract `k` that type `b` strictly prefers to everything else
on offer, with utility at least `ρ b`, gets `P b k` from her. -/
theorem typeProfit_capture (hI : G.Inj) {b : Bool} {other B : Finset (ℝ × ℝ)} {k : ℝ × ℝ}
    (hk : k ∈ B) (h0 : G.ρ b ≤ G.U b k) (hs : ∀ k' ∈ other, G.U b k' < G.U b k)
    (hB : ∀ k' ∈ B, k' ≠ k → G.U b k' < G.U b k) :
    G.typeProfit b B other = G.P b k := by
  have hch : G.Chooses b (B ∪ other) k := by
    refine chooses_of_strict (Finset.mem_union_left _ hk) h0 fun k' hk' hne => ?_
    rcases Finset.mem_union.1 hk' with h | h
    · exact hB k' h hne
    · exact hs k' h
  have hno : k ∉ other := fun h => lt_irrefl _ (hs k h)
  rw [typeProfit_of_chooses hI hch]
  simp [SigModel.share, hk, hno]

/-- A single-contract deviation `{k}` gets nothing from type `b` if some contract of the other
firm gives `b` strictly more than `k`. -/
theorem no_capture_of_other (hI : G.Inj) {b : Bool} {other : Finset (ℝ × ℝ)} {k k0 : ℝ × ℝ}
    (hk0 : k0 ∈ other) (h : G.U b k < G.U b k0) : G.typeProfit b {k} other = 0 := by
  by_cases hex : ∃ k', G.Chooses b ({k} ∪ other) k'
  · obtain ⟨k', hk'⟩ := hex
    have hne : k' ≠ k := by
      rintro rfl
      exact absurd (hk'.2.2.1 k0 (Finset.mem_union_right _ hk0)) (not_le.2 h)
    rw [typeProfit_of_chooses hI hk']
    simp [SigModel.share, hne]
  · exact typeProfit_of_not hex

/-- A deviation whose contracts all make a nonnegative profit on type `b` earns a nonnegative
profit from her. -/
theorem typeProfit_nonneg_of (hI : G.Inj) {b : Bool} {other B : Finset (ℝ × ℝ)}
    (hB : ∀ k ∈ B, 0 ≤ G.P b k) : 0 ≤ G.typeProfit b B other := by
  by_cases hex : ∃ k', G.Chooses b (B ∪ other) k'
  · obtain ⟨k', hk'⟩ := hex
    rw [typeProfit_of_chooses hI hk']
    by_cases hm : k' ∈ B
    · exact mul_nonneg (SigModel.share_nonneg _ _ _) (hB k' hm)
    · simp [SigModel.share, hm]
  · exact (typeProfit_of_not hex).ge

/-- The firms' profits add up to the expected profit on the chosen contracts. -/
theorem profit_add (A₁ A₂ : Finset (ℝ × ℝ)) :
    G.profit A₁ A₂ + G.profit A₂ A₁ =
      (1 - G.lam) * (G.typeProfit false A₁ A₂ + G.typeProfit false A₂ A₁) +
        G.lam * (G.typeProfit true A₁ A₂ + G.typeProfit true A₂ A₁) := by
  unfold profit; ring

/-- A uniform positive margin below finitely many strict inequalities. -/
theorem exists_gap {X : Type*} (S : Finset X) (f : X → ℝ) (hf : ∀ x ∈ S, 0 < f x) :
    ∃ δ, 0 < δ ∧ ∀ x ∈ S, δ < f x := by
  rcases S.eq_empty_or_nonempty with hS | hS
  · exact ⟨1, one_pos, fun x hx => by simp [hS] at hx⟩
  · obtain ⟨x0, hx0, hmin⟩ := S.exists_min_image f hS
    exact ⟨f x0 / 2, half_pos (hf x0 hx0), fun x hx => by linarith [hmin x hx, hf x0 hx0]⟩

/-- The Bertrand deviation for one type: offering every contract on the market, sweetened by a
small `δ`, keeps (up to `η`) the profit both firms together make on type `b`. -/
theorem dev_type (hI : G.Inj) (sw : ℝ → ℝ × ℝ → ℝ × ℝ)
    (hswU : ∀ δ b k, G.U b (sw δ k) = G.U b k + δ) (hswkey : ∀ δ k, G.key (sw δ k) = G.key k)
    (hswP : ∀ b k η, 0 < η → ∃ δ₀, 0 < δ₀ ∧ ∀ δ, 0 < δ → δ ≤ δ₀ → G.P b k - η < G.P b (sw δ k))
    (b : Bool) (own other : Finset (ℝ × ℝ)) {η : ℝ} (hη : 0 < η) :
    ∃ δ₀, 0 < δ₀ ∧ ∀ δ, 0 < δ → δ ≤ δ₀ →
      G.typeProfit b own other + G.typeProfit b other own - η ≤
        G.typeProfit b ((own ∪ other).image (sw δ)) other := by
  by_cases hex : ∃ k, G.Chooses b (own ∪ other) k
  · obtain ⟨k, hk⟩ := hex
    obtain ⟨δ₀, hδ₀, hP⟩ := hswP b k η hη
    refine ⟨δ₀, hδ₀, fun δ hδ hδle => ?_⟩
    rw [typeProfit_add hI hk]
    set B := (own ∪ other).image (sw δ)
    have hch : G.Chooses b (B ∪ other) (sw δ k) := by
      refine ⟨Finset.mem_union_left _ (Finset.mem_image_of_mem _ hk.1), ?_, fun k' hk' => ?_,
        fun k' hk' hu => ?_⟩
      · rw [hswU]; linarith [hk.2.1]
      · rcases Finset.mem_union.1 hk' with h' | h'
        · obtain ⟨k'', hk'', rfl⟩ := Finset.mem_image.1 h'
          rw [hswU, hswU]; linarith [hk.2.2.1 k'' hk'']
        · rw [hswU]; linarith [hk.2.2.1 k' (Finset.mem_union_right _ h')]
      · rcases Finset.mem_union.1 hk' with h' | h'
        · obtain ⟨k'', hk'', rfl⟩ := Finset.mem_image.1 h'
          rw [hswU, hswU] at hu
          rw [hswkey, hswkey]
          exact hk.2.2.2 k'' hk'' (by linarith)
        · rw [hswU] at hu
          linarith [hk.2.2.1 k' (Finset.mem_union_right _ h')]
    have hno : sw δ k ∉ other := fun hm => by
      have := hk.2.2.1 _ (Finset.mem_union_right _ hm)
      rw [hswU] at this; linarith
    have hmem : sw δ k ∈ B := Finset.mem_image_of_mem _ hk.1
    rw [typeProfit_of_chooses hI hch]
    simp only [SigModel.share, hmem, hno, ↓reduceIte, one_mul]
    linarith [hP δ hδ hδle]
  · have hlt : ∀ k ∈ own ∪ other, G.U b k < G.ρ b := fun k hk => by
      by_contra hle
      exact hex (exists_chooses b ⟨k, hk, not_lt.1 hle⟩)
    obtain ⟨δ₀, hδ₀, hgap⟩ := exists_gap (own ∪ other) (fun k => G.ρ b - G.U b k)
      (fun k hk => by have := hlt k hk; linarith)
    refine ⟨δ₀, hδ₀, fun δ hδ hδle => ?_⟩
    rw [typeProfit_add_not hex]
    have hno : ¬ ∃ k, G.Chooses b ((own ∪ other).image (sw δ) ∪ other) k := by
      rintro ⟨k, hk⟩
      rcases Finset.mem_union.1 hk.1 with h' | h'
      · obtain ⟨k'', hk'', rfl⟩ := Finset.mem_image.1 h'
        have := hk.2.1
        rw [hswU] at this
        have := hgap k'' hk''
        linarith
      · linarith [hk.2.1, hlt k (Finset.mem_union_right _ h')]
    rw [typeProfit_of_not hno]
    linarith

/-- **Lemma 13.D.1** (MWG, pp. 462-463), for a general screening game. If contracts can be
sweetened uniformly (`sw δ` raises every type's utility by `δ`, keeps admissibility and the
tie-breaking key, and changes each profit continuously), both firms earn zero profits in every
SPNE. -/
theorem IsEq.zero (hI : G.Inj) (hl0 : 0 ≤ G.lam) (hl1 : G.lam ≤ 1)
    (sw : ℝ → ℝ × ℝ → ℝ × ℝ) (hswA : ∀ δ k, 0 < δ → G.adm k → G.adm (sw δ k))
    (hswU : ∀ δ b k, G.U b (sw δ k) = G.U b k + δ) (hswkey : ∀ δ k, G.key (sw δ k) = G.key k)
    (hswP : ∀ b k η, 0 < η → ∃ δ₀, 0 < δ₀ ∧ ∀ δ, 0 < δ → δ ≤ δ₀ → G.P b k - η < G.P b (sw δ k))
    {A₁ A₂ : Finset (ℝ × ℝ)} (h : G.IsEq A₁ A₂) :
    G.profit A₁ A₂ = 0 ∧ G.profit A₂ A₁ = 0 := by
  set T := G.profit A₁ A₂ + G.profit A₂ A₁ with hT
  have key : ∀ own other, G.IsEq own other → ∀ η, 0 < η →
      G.profit own other + G.profit other own - η ≤ G.profit own other := by
    intro own other he η hη
    obtain ⟨δf, hδf, hf⟩ := dev_type hI sw hswU hswkey hswP false own other hη
    obtain ⟨δt, hδt, ht⟩ := dev_type hI sw hswU hswkey hswP true own other hη
    set δ := min δf δt
    have hδ : 0 < δ := lt_min hδf hδt
    have hB : G.Menu ((own ∪ other).image (sw δ)) := by
      intro k hk
      obtain ⟨k', hk', rfl⟩ := Finset.mem_image.1 hk
      rcases Finset.mem_union.1 hk' with h' | h'
      · exact hswA δ k' hδ (he.1 k' h')
      · exact hswA δ k' hδ (he.2.1 k' h')
    have hdev := he.2.2.1 _ hB
    have h1 := hf δ hδ (min_le_left _ _)
    have h2 := ht δ hδ (min_le_right _ _)
    rw [profit_add]
    unfold profit at hdev ⊢
    nlinarith [mul_le_mul_of_nonneg_left h1 (sub_nonneg.2 hl1), mul_le_mul_of_nonneg_left h2 hl0]
  have hle : ∀ own other, G.IsEq own other →
      G.profit own other + G.profit other own ≤ G.profit own other := by
    intro own other he
    refine le_of_forall_pos_lt_add fun η hη => ?_
    have := key own other he (η / 2) (half_pos hη)
    linarith
  have h1 := hle A₁ A₂ h
  have h2 := hle A₂ A₁ h.symm
  have n1 := h.nonneg hI
  have n2 := h.symm.nonneg hI
  constructor <;> linarith

/-- A profitable single-contract deviation is impossible in an SPNE with zero profits: the
deviation `{k'}` attracts type `true` (who strictly prefers it to her chosen contract) at a
positive profit, while type `false` strictly prefers her chosen contract `kL`. -/
theorem IsEq.dev_true (hI : G.Inj) (hl : 0 < G.lam) {A₁ A₂ : Finset (ℝ × ℝ)} (h : G.IsEq A₁ A₂)
    (hz : G.profit A₁ A₂ = 0 ∧ G.profit A₂ A₁ = 0) {kL kH k' : ℝ × ℝ}
    (hkL : G.Chooses false (A₁ ∪ A₂) kL) (hkH : G.Chooses true (A₁ ∪ A₂) kH) (hadm : G.adm k')
    (hH : G.U true kH < G.U true k') (hL : G.U false k' < G.U false kL)
    (hP : 0 < G.P true k') : False := by
  have key : ∀ own other, G.IsEq own other → G.profit own other = 0 →
      (∀ k ∈ other, G.U true k ≤ G.U true kH) → kL ∈ other → False := by
    intro own other he hz' hle hmem
    have hc := typeProfit_capture hI (b := true) (other := other) (Finset.mem_singleton_self k')
      (hkH.2.1.trans hH.le) (fun k hk => (hle k hk).trans_lt hH)
      (fun k hk hne => absurd (Finset.mem_singleton.1 hk) hne)
    have h0 := no_capture_of_other hI (b := false) (k := k') hmem hL
    have := he.2.2.1 {k'} (fun k hk => by rw [Finset.mem_singleton.1 hk]; exact hadm)
    rw [hz'] at this
    simp only [profit, hc, h0] at this
    nlinarith
  rcases Finset.mem_union.1 hkL.1 with hm | hm
  · exact key A₂ A₁ h.symm hz.2
      (fun k hk => hkH.2.2.1 k (Finset.mem_union_left _ hk)) hm
  · exact key A₁ A₂ h hz.1 (fun k hk => hkH.2.2.1 k (Finset.mem_union_right _ hk)) hm

/-- A variant of `IsEq.dev_true`: the deviation `{k'}` gives type `true` strictly more than every
offered contract and at least `ρ true`, makes a positive profit on her, and type `false` strictly
prefers her chosen contract `kL`. -/
theorem IsEq.dev_true' (hI : G.Inj) (hl : 0 < G.lam) {A₁ A₂ : Finset (ℝ × ℝ)} (h : G.IsEq A₁ A₂)
    (hz : G.profit A₁ A₂ = 0 ∧ G.profit A₂ A₁ = 0) {kL k' : ℝ × ℝ}
    (hkL : G.Chooses false (A₁ ∪ A₂) kL) (hadm : G.adm k') (h0 : G.ρ true ≤ G.U true k')
    (hs : ∀ k ∈ A₁ ∪ A₂, G.U true k < G.U true k') (hL : G.U false k' < G.U false kL)
    (hP : 0 < G.P true k') : False := by
  have key : ∀ own other, G.IsEq own other → G.profit own other = 0 →
      other ⊆ A₁ ∪ A₂ → kL ∈ other → False := by
    intro own other he hz' hsub hmem
    have hc := typeProfit_capture hI (b := true) (other := other) (Finset.mem_singleton_self k')
      h0 (fun k hk => hs k (hsub hk)) (fun k hk hne => absurd (Finset.mem_singleton.1 hk) hne)
    have h0' := no_capture_of_other hI (b := false) (k := k') hmem hL
    have := he.2.2.1 {k'} (fun k hk => by rw [Finset.mem_singleton.1 hk]; exact hadm)
    rw [hz'] at this
    simp only [profit, hc, h0'] at this
    nlinarith
  rcases Finset.mem_union.1 hkL.1 with hm | hm
  · exact key A₂ A₁ h.symm hz.2 Finset.subset_union_left hm
  · exact key A₁ A₂ h hz.1 Finset.subset_union_right hm

/-- A single contract `k'` that type `false` strictly prefers to everything firm 2 offers, at a
positive profit on her and a nonnegative profit on type `true`, is a profitable deviation for
firm 1 when its equilibrium profit is zero. -/
theorem IsEq.dev_false (hI : G.Inj) (hl1 : G.lam < 1) (hl0 : 0 ≤ G.lam)
    {A₁ A₂ : Finset (ℝ × ℝ)} (h : G.IsEq A₁ A₂) (hz : G.profit A₁ A₂ = 0) {k' : ℝ × ℝ}
    (hadm : G.adm k') (h0 : G.ρ false ≤ G.U false k') (hs : ∀ k ∈ A₂, G.U false k < G.U false k')
    (hP : 0 < G.P false k') (hPt : 0 ≤ G.P true k') : False := by
  have hc := typeProfit_capture hI (b := false) (other := A₂) (Finset.mem_singleton_self k') h0
    hs (fun k hk hne => absurd (Finset.mem_singleton.1 hk) hne)
  have ht := typeProfit_nonneg_of hI (b := true) (other := A₂) (B := {k'})
    (fun k hk => by rw [Finset.mem_singleton.1 hk]; exact hPt)
  have := h.2.2.1 {k'} (fun k hk => by rw [Finset.mem_singleton.1 hk]; exact hadm)
  rw [hz] at this
  simp only [profit, hc] at this
  nlinarith [mul_nonneg hl0 ht]

/-- The analogue of `IsEq.dev_false` for type `true`. -/
theorem IsEq.dev_true_pos (hI : G.Inj) (hl0 : 0 < G.lam) (hl1 : G.lam ≤ 1)
    {A₁ A₂ : Finset (ℝ × ℝ)} (h : G.IsEq A₁ A₂) (hz : G.profit A₁ A₂ = 0) {k' : ℝ × ℝ}
    (hadm : G.adm k') (h0 : G.ρ true ≤ G.U true k') (hs : ∀ k ∈ A₂, G.U true k < G.U true k')
    (hP : 0 < G.P true k') (hPf : 0 ≤ G.P false k') : False := by
  have hc := typeProfit_capture hI (b := true) (other := A₂) (Finset.mem_singleton_self k') h0
    hs (fun k hk hne => absurd (Finset.mem_singleton.1 hk) hne)
  have hf := typeProfit_nonneg_of hI (b := false) (other := A₂) (B := {k'})
    (fun k hk => by rw [Finset.mem_singleton.1 hk]; exact hPf)
  have := h.2.2.1 {k'} (fun k hk => by rw [Finset.mem_singleton.1 hk]; exact hadm)
  rw [hz] at this
  simp only [profit, hc] at this
  nlinarith [mul_nonneg (sub_nonneg.2 hl1) hf]

/-- A single contract that both types strictly prefer to everything firm 2 offers, with a
positive expected profit, is a profitable deviation for firm 1 when its profit is zero. -/
theorem IsEq.dev_both (hI : G.Inj) {A₁ A₂ : Finset (ℝ × ℝ)} (h : G.IsEq A₁ A₂)
    (hz : G.profit A₁ A₂ = 0) {k' : ℝ × ℝ} (hadm : G.adm k') (h0 : ∀ b, G.ρ b ≤ G.U b k')
    (hs : ∀ b, ∀ k ∈ A₂, G.U b k < G.U b k')
    (hP : 0 < (1 - G.lam) * G.P false k' + G.lam * G.P true k') : False := by
  have hc : ∀ b, G.typeProfit b {k'} A₂ = G.P b k' := fun b =>
    typeProfit_capture hI (Finset.mem_singleton_self k') (h0 b) (hs b)
      (fun k hk hne => absurd (Finset.mem_singleton.1 hk) hne)
  have := h.2.2.1 {k'} (fun k hk => by rw [Finset.mem_singleton.1 hk]; exact hadm)
  rw [hz] at this
  simp only [profit, hc] at this
  linarith

end ScrGame

end MWG.AdverseSelection
