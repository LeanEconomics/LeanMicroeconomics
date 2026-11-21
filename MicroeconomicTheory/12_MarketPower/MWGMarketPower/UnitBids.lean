/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGMarketPower.Bertrand
import Mathlib.Order.Interval.Finset.Fin

/-!
# Bidding for a limited number of units

MWG, Exercise 12.C.5, p. 431.

There are `I` buyers `0, …, I − 1` (buyer `i` is MWG's buyer `i + 1`), each wanting one unit;
buyer `i` values it at `vᵢ`, with `v₀ > v₁ > ⋯` (`StrictAnti v`). There are `q < I` units.
Buyers submit bids `bᵢ`; the units go to the `q` highest bidders, who pay their bids. Ties are
broken in favour of the buyer with the smaller index (the higher valuation): this is the reading
under which, as MWG states, the profile with every bid equal to `v_{q+1}` assigns the units to
buyers `1, …, q`. Buyer `i` wins iff fewer than `q` buyers rank above it (`ubAbove`), where `k`
ranks above `i` if `bₖ > bᵢ`, or `bₖ = bᵢ` and `k < i`.

* `exercise_12_C_5a`: every buyer bidding `v_{q+1}` (index `q`), with the units going to buyers
  `1, …, q`, is a Nash equilibrium.
* `exercise_12_C_5_competitive`: at the price `v_{q+1}` exactly `q` buyers strictly want a unit,
  buyer `q + 1` is indifferent and the others do not want one: a competitive equilibrium price.
* `exercise_12_C_5b`: in any pure-strategy Nash equilibrium, buyers `1, …, q` receive a unit and
  buyers `q + 1, …, I` do not. The proof: a losing buyer could outbid any winner `i` by `ε`, so
  its value is at most `bᵢ ≤ vᵢ`; and exactly `q` buyers win (`ub_card_winners`).
-/

namespace MWG.MarketPower

open Finset Function

variable {I : ℕ}

/-- The buyers ranked above buyer `i` at the bid profile `b`. -/
noncomputable def ubAbove (b : Fin I → ℝ) (i : Fin I) : Finset (Fin I) :=
  univ.filter fun k => b i < b k ∨ (b k = b i ∧ k < i)

/-- Buyer `i`'s payoff: `vᵢ − bᵢ` if it is among the `q` highest-ranked bidders, else `0`. -/
noncomputable def ubPayoff (v : Fin I → ℝ) (q : ℕ) (b : Fin I → ℝ) (i : Fin I) : ℝ :=
  if (ubAbove b i).card < q then v i - b i else 0

/-- A pure-strategy Nash equilibrium of the bidding game. -/
def IsUBNash (v : Fin I → ℝ) (q : ℕ) (b : Fin I → ℝ) : Prop :=
  ∀ i y, ubPayoff v q (update b i y) i ≤ ubPayoff v q b i

theorem ubAbove_irrefl (b : Fin I → ℝ) (i : Fin I) : i ∉ ubAbove b i := by
  simp [ubAbove]

theorem ubAbove_total (b : Fin I → ℝ) {i k : Fin I} (h : k ≠ i) :
    k ∈ ubAbove b i ∨ i ∈ ubAbove b k := by
  simp only [ubAbove, mem_filter, mem_univ, true_and]
  rcases lt_trichotomy (b i) (b k) with h1 | h1 | h1
  · exact Or.inl (Or.inl h1)
  · rcases lt_or_gt_of_ne h with h2 | h2
    · exact Or.inl (Or.inr ⟨h1.symm, h2⟩)
    · exact Or.inr (Or.inr ⟨h1, h2⟩)
  · exact Or.inr (Or.inl h1)

theorem ubAbove_ssubset (b : Fin I → ℝ) {i k : Fin I} (h : k ∈ ubAbove b i) :
    ubAbove b k ⊂ ubAbove b i := by
  simp only [ubAbove, mem_filter, mem_univ, true_and] at h
  refine Finset.ssubset_iff_subset_ne.2 ⟨fun l hl => ?_, fun he => ?_⟩
  · simp only [ubAbove, mem_filter, mem_univ, true_and] at hl ⊢
    rcases h with h | ⟨h1, h2⟩ <;> rcases hl with hl | ⟨hl1, hl2⟩
    · exact Or.inl (h.trans hl)
    · exact Or.inl (hl1 ▸ h)
    · exact Or.inl (h1 ▸ hl)
    · exact Or.inr ⟨hl1.trans h1, hl2.trans h2⟩
  · have hk : k ∈ ubAbove b i := by simpa [ubAbove] using h
    rw [← he] at hk
    exact ubAbove_irrefl b k hk

theorem ubAbove_card_injective (b : Fin I → ℝ) : Injective fun i => (ubAbove b i).card := by
  intro i k hik
  have hik' : (ubAbove b i).card = (ubAbove b k).card := hik
  by_contra hne
  rcases ubAbove_total b hne with h | h
  · exact absurd hik' (Finset.card_lt_card (ubAbove_ssubset b h)).ne
  · exact absurd hik' (Finset.card_lt_card (ubAbove_ssubset b h)).ne'

theorem ubAbove_card_lt (b : Fin I → ℝ) (i : Fin I) : (ubAbove b i).card < I := by
  have : ubAbove b i ⊆ univ.erase i := fun k hk =>
    mem_erase.2 ⟨fun h => ubAbove_irrefl b i (h ▸ hk), mem_univ _⟩
  have h1 := Finset.card_le_card this
  rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin] at h1
  have := i.2
  omega

/-- Exactly `min q I` buyers win; with `q ≤ I`, exactly `q`. -/
theorem ub_card_winners (b : Fin I → ℝ) {q : ℕ} (hq : q ≤ I) :
    (univ.filter fun i => (ubAbove b i).card < q).card = q := by
  set r : Fin I → ℕ := fun i => (ubAbove b i).card with hr
  have hinj : Injective r := ubAbove_card_injective b
  have himg : univ.image r = range I := by
    apply Finset.eq_of_subset_of_card_le
    · intro m hm
      obtain ⟨i, -, rfl⟩ := mem_image.1 hm
      exact mem_range.2 (ubAbove_card_lt b i)
    · rw [card_image_of_injective _ hinj, card_univ, Fintype.card_fin, card_range]
  have h1 : (univ.filter fun i => r i < q).card =
      ((univ.filter fun i => r i < q).image r).card :=
    (card_image_of_injective _ hinj).symm
  have h2 : (univ.filter fun i => r i < q).image r = (univ.image r).filter (· < q) := by
    rw [Finset.filter_image]
  change (univ.filter fun i => r i < q).card = q
  rw [h1, h2, himg]
  have : (range I).filter (· < q) = range q := by
    ext m; simp only [mem_filter, mem_range]; omega
  rw [this, card_range]

/-- Ranks at the constant bid profile: buyer `i` has exactly `i` buyers above it. -/
theorem ubAbove_const (w : ℝ) (i : Fin I) : (ubAbove (fun _ => w) i).card = i := by
  have : ubAbove (fun _ => w) i = Finset.Iio i := by
    ext k; simp [ubAbove]
  rw [this, Fin.card_Iio]

theorem ubAbove_update_lt {w y : ℝ} (h : y < w) (i : Fin I) :
    (ubAbove (update (fun _ => w) i y) i).card = I - 1 := by
  have : ubAbove (update (fun _ => w) i y) i = univ.erase i := by
    ext k
    by_cases hk : k = i
    · subst hk; simp [ubAbove]
    · simp [ubAbove, hk, h]
  rw [this, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]

theorem ubAbove_update_gt {w y : ℝ} (h : w < y) (i : Fin I) :
    ubAbove (update (fun _ => w) i y) i = ∅ := by
  ext k
  by_cases hk : k = i
  · subst hk; simp [ubAbove]
  · simp [ubAbove, hk, h.not_gt, h.ne]

/-- **Exercise 12.C.5, first part** (MWG, p. 431). With `v₀ > v₁ > ⋯` and `q < I`, every buyer
bidding `v_q` (MWG's `v_{q+1}`) is a Nash equilibrium, and in it the units go to the buyers
`i < q` (MWG's buyers `1, …, q`). -/
theorem exercise_12_C_5a {v : Fin I → ℝ} (hv : StrictAnti v) {q : ℕ} (hq : q < I) :
    IsUBNash v q (fun _ => v ⟨q, hq⟩) ∧
      ∀ i : Fin I, (ubAbove (fun _ => v ⟨q, hq⟩) i).card < q ↔ (i : ℕ) < q := by
  set w := v ⟨q, hq⟩ with hw
  refine ⟨fun i y => ?_, fun i => by rw [ubAbove_const]⟩
  have hpay : ubPayoff v q (fun _ => w) i = if (i : ℕ) < q then v i - w else 0 := by
    unfold ubPayoff; rw [ubAbove_const]
  rw [hpay]
  -- the equilibrium payoff is nonnegative, and at least `v i − w`
  have hge0 : 0 ≤ if (i : ℕ) < q then v i - w else 0 := by
    split_ifs with h
    · have : v ⟨q, hq⟩ < v i := hv (Fin.mk_lt_mk.2 h |>.trans_eq' rfl)
      linarith
    · exact le_rfl
  have hge : v i - w ≤ if (i : ℕ) < q then v i - w else 0 := by
    split_ifs with h
    · exact le_rfl
    · push Not at h
      have : v i ≤ v ⟨q, hq⟩ := hv.antitone (show (⟨q, hq⟩ : Fin I) ≤ i from h)
      linarith
  unfold ubPayoff
  rcases lt_trichotomy y w with h | h | h
  · rw [ubAbove_update_lt h, ite_eq_right (by omega)]
    exact hge0
  · subst h
    have : update (fun _ : Fin I => w) i w = fun _ => w := by
      funext k; by_cases hk : k = i <;> simp [hk]
    rw [this, ← hpay]
    rfl
  · rw [ubAbove_update_gt h, card_empty]
    by_cases h1 : 0 < q
    · rw [ite_eq_left h1, update_self]; linarith
    · rw [ite_eq_right h1]; exact hge0

/-- **Exercise 12.C.5, `v_{q+1}` is a competitive price** (MWG, p. 431). At the price `v_q`
(MWG's `v_{q+1}`) the buyers `i < q` strictly want a unit, the buyers `i > q` strictly do not,
and buyer `q` is indifferent; exactly `q` buyers strictly want a unit, which equals supply. -/
theorem exercise_12_C_5_competitive {v : Fin I → ℝ} (hv : StrictAnti v) {q : ℕ} (hq : q < I) :
    (∀ i : Fin I, (i : ℕ) < q → v ⟨q, hq⟩ < v i) ∧
    (∀ i : Fin I, q < (i : ℕ) → v i < v ⟨q, hq⟩) ∧
    (univ.filter fun i => v ⟨q, hq⟩ < v i).card = q := by
  refine ⟨fun i h => hv (Fin.mk_lt_mk.2 h |>.trans_eq' rfl), fun i h => hv
    (show (⟨q, hq⟩ : Fin I) < i from h), ?_⟩
  have : (univ.filter fun i => v ⟨q, hq⟩ < v i) = Finset.Iio ⟨q, hq⟩ := by
    ext i
    simp only [mem_filter, mem_univ, true_and, Finset.mem_Iio]
    exact hv.lt_iff_gt
  rw [this, Fin.card_Iio]

/-- A bid below every other bid loses. -/
theorem ub_lose_bid (b : Fin I → ℝ) (i : Fin I) {q : ℕ} (hq : q < I) :
    q ≤ (ubAbove (update b i (-(∑ k, |b k|) - 1)) i).card := by
  have hlow : ∀ k, -(∑ k, |b k|) - 1 < b k := by
    intro k
    have h1 : |b k| ≤ ∑ k, |b k| :=
      Finset.single_le_sum (f := fun k => |b k|) (fun k _ => abs_nonneg _) (mem_univ k)
    have h2 := neg_abs_le (b k)
    linarith
  have : ubAbove (update b i (-(∑ k, |b k|) - 1)) i = univ.erase i := by
    ext k
    by_cases hk : k = i
    · subst hk; simp [ubAbove]
    · simp [ubAbove, hk, hlow k]
  rw [this, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
  omega

/-- **Exercise 12.C.5, second part** (MWG, p. 431). In any pure-strategy Nash equilibrium of
the bidding game (`v₀ > v₁ > ⋯`, `q < I` units), buyers `i < q` (MWG's `1, …, q`) receive a unit
and buyers `i ≥ q` (MWG's `q + 1, …, I`) do not. -/
theorem exercise_12_C_5b {v : Fin I → ℝ} (hv : StrictAnti v) {q : ℕ} (hq : q < I)
    {b : Fin I → ℝ} (hb : IsUBNash v q b) (i : Fin I) :
    (ubAbove b i).card < q ↔ (i : ℕ) < q := by
  -- winners bid at most their value
  have hwin : ∀ i, (ubAbove b i).card < q → b i ≤ v i := by
    intro i hi
    have := hb i (-(∑ k, |b k|) - 1)
    unfold ubPayoff at this
    rw [ite_eq_right (not_lt.2 (ub_lose_bid b i hq)), ite_eq_left hi] at this
    linarith
  -- a loser's value is below every winner's value
  have hpair : ∀ i j, (ubAbove b i).card < q → ¬ (ubAbove b j).card < q → v j < v i := by
    intro i j hi hj
    have hle : v j ≤ b i := by
      by_contra hlt
      push Not at hlt
      set y := (b i + v j) / 2 with hy
      have hsub : ubAbove (update b j y) j ⊆ ubAbove b i := by
        intro k hk
        simp only [ubAbove, mem_filter, mem_univ, true_and] at hk ⊢
        by_cases hkj : k = j
        · subst hkj; simp at hk
        · simp only [update_self, update_of_ne hkj] at hk
          rcases hk with hk | ⟨hk, -⟩
          · left; linarith
          · left; linarith
      have hwins : (ubAbove (update b j y) j).card < q :=
        lt_of_le_of_lt (Finset.card_le_card hsub) hi
      have := hb j y
      unfold ubPayoff at this
      rw [ite_eq_left hwins, ite_eq_right hj, update_self] at this
      linarith
    have hne : j ≠ i := by rintro rfl; exact hj hi
    rcases lt_or_gt_of_ne (hv.injective.ne hne) with h | h
    · exact h
    · linarith [hwin i hi]
  have hW := ub_card_winners b hq.le
  constructor
  · intro hi
    by_contra hiq
    push Not at hiq
    -- every loser has a larger index than the winner `i`
    have hsub : (univ.filter fun j => ¬ (ubAbove b j).card < q) ⊆ Finset.Ioi i := by
      intro j hj
      simp only [mem_filter, mem_univ, true_and] at hj
      exact Finset.mem_Ioi.2 (hv.lt_iff_gt.1 (hpair i j hi hj))
    have h1 := Finset.card_le_card hsub
    rw [Fin.card_Ioi] at h1
    have h2 := Finset.card_filter_add_card_filter_not
      (s := (univ : Finset (Fin I))) (fun j => (ubAbove b j).card < q)
    rw [hW, card_univ, Fintype.card_fin] at h2
    omega
  · intro hi
    by_contra hlose
    -- every winner has a smaller index than the loser `i`
    have hsub : (univ.filter fun j => (ubAbove b j).card < q) ⊆ Finset.Iio i := by
      intro j hj
      simp only [mem_filter, mem_univ, true_and] at hj
      exact Finset.mem_Iio.2 (hv.lt_iff_gt.1 (hpair j i hj hlose))
    have h1 := Finset.card_le_card hsub
    rw [hW, Fin.card_Iio] at h1
    omega

end MWG.MarketPower
