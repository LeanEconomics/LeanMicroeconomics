/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGWelfareTheorems.QuasiExample
import Mathlib.Analysis.Convex.Caratheodory

/-!
# Nonconvex preferences and replication (MWG Section 16.D, pp. 557-558; Exercise 16.D.4)

* **Figures 16.D.4 and 16.D.5**: with the nonconvex preference `u(x) = x₁² + x₂²` and
  `ω = (2, 2)`, the endowment of a one-consumer economy is (trivially) Pareto optimal but not
  supportable by prices; in the two-consumer replica the symmetric allocation is Pareto dominated
  by `x'₁ = ω + (1, -1)`, `x'₂ = ω + (-1, 1)`.
* **Exercise 16.D.4**: in the `r`-fold replica of a pure exchange economy with identical
  consumers (`X = ℝ^L₊`, continuous, strongly monotone, possibly nonconvex preferences,
  endowment `ω ≫ 0`), the symmetric allocation in which every consumer keeps `ω` is either a
  Walrasian equilibrium allocation (for some `p`, for every `r`) or, for all `r` large enough, not
  Pareto optimal. The book has two goods; the proof works for any `L ≥ 1`, without
  differentiability. It separates the convex hull of the strictly preferred trades from the
  open negative orthant; if they meet, a convex combination of preferred trades is `≪ 0`, and
  rounding its weights gives integer multiplicities, i.e. a Pareto improvement in a large replica.
-/

namespace MWG.WelfareTheorems

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.Production Kreps.PreferenceProperties
open MWG.CompetitiveMarkets (Allocation)
open Filter Topology

variable {L : ℕ}

/-- **Exercise 16.D.4** (MWG, p. 575). The `r`-fold replica of a pure exchange economy with
identical consumers: consumption sets `ℝ^L₊`, preference `≿`, one disposal firm and total
endowment `r ω`. -/
def replicaEconomy (R : (Fin L → ℝ) → (Fin L → ℝ) → Prop) (ω : Fin L → ℝ) (r : ℕ) :
    PrefEconomy (Fin r) Unit L where
  X := fun _ => nonnegOrthant L
  pref := fun _ => R
  Y := fun _ => nonposOrthant L
  ω := (r : ℝ) • ω

/-- The symmetric allocation in which every consumer consumes her endowment `ω`. -/
def symmetricAlloc (ω : Fin L → ℝ) (r : ℕ) : Allocation (Fin r) Unit L :=
  ⟨fun _ => ω, fun _ => 0⟩

/-- A strictly preferred bundle stays strictly preferred along any sequence converging to it
(continuity and completeness of `≿`): some term of the sequence is strictly preferred. -/
theorem exists_strict_of_tendsto {X : Set (Fin L → ℝ)} {R : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hr : RationalOn X R) (hc : PrefContinuous X R) {x z : Fin L → ℝ} (hx : x ∈ X) (hz : z ∈ X)
    (hs : Strict R x z) {zs : ℕ → Fin L → ℝ} (hzs : ∀ n, zs n ∈ X)
    (ht : Tendsto zs atTop (𝓝 x)) : ∃ n, Strict R (zs n) z := by
  by_contra hall
  push Not at hall
  have hle : ∀ n, R z (zs n) := fun n => by
    rcases hr.1 z hz (zs n) (hzs n) with h | h
    · exact h
    · by_contra h'
      exact hall n ⟨h, h'⟩
  exact hs.2 (hc (fun _ => z) zs z x (fun _ => hz) hzs hz hx hle tendsto_const_nhds ht)

/-- Removing a small amount `δ/(n+1)` of a good held in positive quantity keeps a strictly
preferred bundle strictly preferred for some `n`. -/
theorem exists_strict_sub_single {R : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hr : RationalOn (nonnegOrthant L) R) (hc : PrefContinuous (nonnegOrthant L) R)
    {x z : Fin L → ℝ} (hx : x ∈ nonnegOrthant L) (hz : z ∈ nonnegOrthant L) (hs : Strict R x z)
    {m : Fin L} (hm : 0 < x m) :
    ∃ δ : ℝ, 0 < δ ∧ x - Pi.single m δ ∈ nonnegOrthant L ∧ Strict R (x - Pi.single m δ) z := by
  have hmem : ∀ n : ℕ, x - Pi.single m (x m / ((n : ℝ) + 1)) ∈ nonnegOrthant L := by
    intro n k
    by_cases hk : k = m
    · subst hk
      rw [Pi.sub_apply, Pi.single_eq_same]
      have : x k / ((n : ℝ) + 1) ≤ x k := div_le_self hm.le (by
        linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
      linarith
    · rw [Pi.sub_apply, Pi.single_eq_of_ne hk, sub_zero]
      exact hx k
  have ht : Tendsto (fun n : ℕ => x - Pi.single m (x m / ((n : ℝ) + 1))) atTop (𝓝 x) := by
    have h1 : Tendsto (fun n : ℕ => x m / ((n : ℝ) + 1)) atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (x m)
      rw [mul_zero] at this
      refine this.congr fun n => ?_
      rw [mul_one_div]
    have hsc : Continuous fun s : ℝ => (Pi.single m s : Fin L → ℝ) :=
      continuous_pi fun k => by
        simp only [Pi.single_apply]
        split_ifs <;> fun_prop
    have hcont : Continuous fun s : ℝ => x - Pi.single m s := continuous_const.sub hsc
    have := (hcont.tendsto 0).comp h1
    rw [Pi.single_zero, sub_zero] at this
    exact this
  obtain ⟨n, hn⟩ := exists_strict_of_tendsto hr hc hx hz hs hmem ht
  exact ⟨x m / ((n : ℝ) + 1), by positivity, hmem n, hn⟩

/-- Rounding the weights of a nonnegative combination that is `≪ 0` down to integers (after
scaling) keeps it `≪ 0`. -/
theorem exists_nat_combination_neg {K : Type*} [Fintype K] (b : K → Fin L → ℝ) (w : K → ℝ)
    (hw : ∀ k, 0 ≤ w k) (hneg : ∀ l, (∑ k, w k • b k) l < 0) :
    ∃ m : K → ℕ, ∀ l, (∑ k, (m k : ℝ) • b k) l < 0 := by
  -- a scale `N` with `N · (∑ wₖbₖ)_l + ∑ₖ |b_{kl}| < 0` for every good
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ l, (N : ℝ) * (∑ k, w k • b k) l + ∑ k, |b k l| < 0 := by
    have hex : ∀ l, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        (n : ℝ) * (∑ k, w k • b k) l + ∑ k, |b k l| < 0 := by
      intro l
      obtain ⟨N, hN⟩ := exists_nat_gt ((∑ k, |b k l|) / -(∑ k, w k • b k) l)
      refine ⟨N, fun n hn => ?_⟩
      have hn' : (∑ k, |b k l|) / -(∑ k, w k • b k) l < n :=
        lt_of_lt_of_le hN (by exact_mod_cast hn)
      rw [div_lt_iff₀ (by linarith [hneg l])] at hn'
      linarith
    choose Nl hNl using hex
    refine ⟨Finset.univ.sup Nl, fun l => hNl l _ (Finset.le_sup (Finset.mem_univ l))⟩
  refine ⟨fun k => ⌊(N : ℝ) * w k⌋₊, fun l => ?_⟩
  have hterm : ∀ k, (⌊(N : ℝ) * w k⌋₊ : ℝ) * b k l ≤ (N : ℝ) * w k * b k l + |b k l| := by
    intro k
    have h1 := Nat.floor_le (mul_nonneg (Nat.cast_nonneg N) (hw k))
    have h2 := Nat.lt_floor_add_one ((N : ℝ) * w k)
    have h3 : 0 ≤ (N : ℝ) * w k - ⌊(N : ℝ) * w k⌋₊ := by linarith
    have h4 : (N : ℝ) * w k - ⌊(N : ℝ) * w k⌋₊ ≤ 1 := by linarith
    have : ((N : ℝ) * w k - ⌊(N : ℝ) * w k⌋₊) * (-b k l) ≤ |b k l| := by
      calc ((N : ℝ) * w k - ⌊(N : ℝ) * w k⌋₊) * (-b k l)
          ≤ ((N : ℝ) * w k - ⌊(N : ℝ) * w k⌋₊) * |b k l| :=
            mul_le_mul_of_nonneg_left (neg_le_abs _) h3
        _ ≤ 1 * |b k l| := mul_le_mul_of_nonneg_right h4 (abs_nonneg _)
        _ = |b k l| := one_mul _
    nlinarith
  have hsum : (∑ k, (⌊(N : ℝ) * w k⌋₊ : ℝ) • b k) l ≤
      (N : ℝ) * (∑ k, w k • b k) l + ∑ k, |b k l| := by
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← mul_assoc,
      ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun k _ => hterm k
  linarith [hN l]

/-- **Exercise 16.D.4** (MWG, pp. 575-576). In the `r`-fold replica of a pure exchange economy
with identical consumers whose preference on `ℝ^L₊` (`L ≥ 1`) is rational, continuous and strongly
monotone (not necessarily convex), and endowment `ω ≫ 0`: either there is a price vector `p` such
that the symmetric allocation is a price equilibrium with transfers with wealth levels `p·ω` (that
is, a Walrasian equilibrium of the replica in which each consumer owns `ω`) for every `r`, or
there is `r₀` such that the symmetric allocation is not Pareto optimal in every replica with
`r ≥ r₀` consumers. -/
theorem exercise_16_D_4 (hL : 0 < L) {R : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hr : RationalOn (nonnegOrthant L) R) (hc : PrefContinuous (nonnegOrthant L) R)
    (hmono : PrefStronglyMonotone (nonnegOrthant L) R) {ω : Fin L → ℝ} (hω : ∀ l, 0 < ω l) :
    (∃ p : Fin L → ℝ, ∀ r, (replicaEconomy R ω r).IsPriceEqmWithTransfers (symmetricAlloc ω r) p
      (fun _ => p ⬝ᵥ ω)) ∨
    ∃ r₀ : ℕ, ∀ r, r₀ ≤ r → ¬ (replicaEconomy R ω r).IsParetoOptimal (symmetricAlloc ω r) := by
  classical
  have hωX : ω ∈ nonnegOrthant L := fun l => (hω l).le
  -- the strictly preferred trades
  set B : Set (Fin L → ℝ) := {b | ω + b ∈ nonnegOrthant L ∧ Strict R (ω + b) ω} with hB
  set N : Set (Fin L → ℝ) := {n | ∀ l, n l < 0} with hN
  have hNopen : IsOpen N := by
    have : N = ⋂ l, {n : Fin L → ℝ | n l < 0} := by ext n; simp [hN]
    rw [this]
    exact isOpen_iInter_of_finite fun l => isOpen_lt (continuous_apply l) continuous_const
  have hNconv : Convex ℝ N := by
    intro x hx y hy a b ha hb hab l
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have := hx l; have := hy l
    rcases ha.lt_or_eq with ha' | ha'
    · nlinarith [mul_neg_of_pos_of_neg ha' (hx l), mul_nonpos_of_nonneg_of_nonpos hb (hy l).le]
    · subst ha'
      have hb1 : b = 1 := by linarith
      subst hb1
      simpa using hy l
  have hsingle_mem : ∀ (x : Fin L → ℝ) (l : Fin L), x ∈ nonnegOrthant L →
      x + Pi.single l 1 ∈ nonnegOrthant L := by
    intro x l hx k
    by_cases hk : k = l
    · subst hk; simp; linarith [hx k]
    · simpa [hk] using hx k
  have hsingle_strict : ∀ (x : Fin L → ℝ) (l : Fin L), x ∈ nonnegOrthant L →
      Strict R (x + Pi.single l 1) x := by
    intro x l hx
    refine hmono x hx _ (hsingle_mem x l hx) (fun k => ?_) ?_
    · by_cases hk : k = l
      · subst hk; simp
      · simp [hk]
    · intro heq
      have := congrFun heq l
      simp at this
  by_cases hdisj : Disjoint N (convexHull ℝ B)
  · -- separation: a price vector `q ≥ 0`, `q ≠ 0`, with `q·b ≥ 0` on the preferred trades
    left
    obtain ⟨f, u, hfN, hfC⟩ := geometric_hahn_banach_open hNconv hNopen (convex_convexHull ℝ B)
      hdisj
    obtain ⟨q, hq⟩ := duality_exists_dot_of_clm f
    have hBne : (Pi.single ⟨0, hL⟩ 1 : Fin L → ℝ) ∈ B :=
      ⟨hsingle_mem ω _ hωX, hsingle_strict ω _ hωX⟩
    have hq0 : ∀ l, 0 ≤ q l := by
      intro l
      by_contra hneg
      push Not at hneg
      set t := max 0 ((u + ∑ k, q k) / -q l) + 1 with ht
      have ht1 : 1 ≤ t := by linarith [le_max_left 0 ((u + ∑ k, q k) / -q l)]
      have ht2 : (u + ∑ k, q k) / -q l ≤ t - 1 := by
        linarith [le_max_right 0 ((u + ∑ k, q k) / -q l)]
      have hmem : -Pi.single l t - (fun _ => (1 : ℝ)) ∈ N := by
        intro k
        by_cases hk : k = l
        · subst hk; simp; linarith
        · simp [hk]
      have := hfN _ hmem
      rw [hq, dotProduct_sub, dotProduct_neg] at this
      have hdot1 : q ⬝ᵥ (Pi.single l t : Fin L → ℝ) = q l * t := by simp
      have hdot2 : q ⬝ᵥ (fun _ => (1 : ℝ)) = ∑ k, q k := by simp [dotProduct]
      rw [hdot1, hdot2] at this
      have hql : 0 < -q l := by linarith
      rw [div_le_iff₀ hql] at ht2
      nlinarith
    have hu0 : 0 ≤ u := by
      by_contra hneg
      push Not at hneg
      have hS : 0 ≤ ∑ k, q k := Finset.sum_nonneg fun k _ => hq0 k
      set ε := -u / (∑ k, q k + 1) with hε
      have hε0 : 0 < ε := div_pos (by linarith) (by linarith)
      have := hfN (fun _ => -ε) (fun _ => by linarith)
      rw [hq] at this
      have hdot : q ⬝ᵥ (fun _ => -ε) = -ε * ∑ k, q k := by
        simp [dotProduct, Finset.sum_mul, mul_comm]
      rw [hdot] at this
      have : -ε * ∑ k, q k ≥ u := by
        rw [hε]
        rw [ge_iff_le, neg_div, neg_mul, neg_mul, neg_neg, div_mul_eq_mul_div]
        rw [le_div_iff₀ (by linarith)]
        nlinarith
      linarith
    have hqB : ∀ b ∈ B, 0 ≤ q ⬝ᵥ b := fun b hb => by
      have := hfC b (subset_convexHull ℝ B hb)
      rw [hq] at this
      linarith
    have hqne : q ≠ 0 := by
      rintro rfl
      have := hfC _ (subset_convexHull ℝ B hBne)
      have h2 := hfN (fun _ => -1) (fun _ => by norm_num)
      rw [hq] at this h2
      simp at this h2
      linarith
    -- `q ≫ 0`
    have hqpos : ∀ l, 0 < q l := by
      intro l
      rcases (hq0 l).lt_or_eq with h | h
      · exact h
      exfalso
      obtain ⟨m, hm⟩ : ∃ m, q m ≠ 0 := by
        by_contra hall
        push Not at hall
        exact hqne (funext hall)
      have hqm : 0 < q m := lt_of_le_of_ne (hq0 m) (Ne.symm hm)
      have hxpos : 0 < (ω + (Pi.single l 1 : Fin L → ℝ)) m := by
        have := hsingle_mem ω l hωX m
        by_cases hml : m = l
        · subst hml; simp; linarith [hω m]
        · simpa [hml] using hω m
      obtain ⟨δ, hδ, hmem, hs⟩ := exists_strict_sub_single hr hc (hsingle_mem ω l hωX) hωX
        (hsingle_strict ω l hωX) hxpos
      have hb : ω + Pi.single l 1 - Pi.single m δ - ω ∈ B :=
        ⟨by simpa using hmem, by simpa using hs⟩
      have := hqB _ hb
      have hcalc : q ⬝ᵥ (ω + Pi.single l 1 - Pi.single m δ - ω) = q l - q m * δ := by
        simp [dotProduct_sub, dotProduct_add]
        ring
      rw [hcalc, ← h] at this
      nlinarith
    refine ⟨q, fun r => ⟨?_, fun _ => ?_, fun i => ?_, ?_⟩⟩
    · simp [replicaEconomy, symmetricAlloc, dotProduct_smul]
    · exact zero_mem_supply_nonpos hq0
    · refine isMaximalFor_of_strict_gt hr hωX le_rfl fun x hx hs => ?_
      have hb : x - ω ∈ B := ⟨by simpa using hx, by simpa [symmetricAlloc] using hs⟩
      have h1 := hqB _ hb
      rw [dotProduct_sub] at h1
      rcases (sub_nonneg.mp h1).lt_or_eq with h2 | h2
      · exact h2
      exfalso
      -- `x` has a good in positive quantity, which can be reduced
      obtain ⟨m, hm⟩ : ∃ m, 0 < x m := by
        by_contra hall
        push Not at hall
        have hx0 : x = 0 := funext fun m => le_antisymm (hall m) (hx m)
        have : 0 < q ⬝ᵥ ω := dotProduct_pos_of_nonneg_ne_zero hq0 hqne hω
        rw [h2, hx0, dotProduct_zero] at this
        exact lt_irrefl 0 this
      obtain ⟨δ, hδ, hmem, hs'⟩ := exists_strict_sub_single hr hc hx hωX hs hm
      have hb' : x - Pi.single m δ - ω ∈ B :=
        ⟨by simpa using hmem, by simpa [symmetricAlloc] using hs'⟩
      have := hqB _ hb'
      rw [dotProduct_sub, dotProduct_sub, ← h2] at this
      simp at this
      nlinarith [hqpos m]
    · funext l
      simp [replicaEconomy, symmetricAlloc]
  · -- a convex combination of preferred trades is `≪ 0`: integer multiplicities
    right
    rw [Set.not_disjoint_iff] at hdisj
    obtain ⟨c, hcN, hcC⟩ := hdisj
    obtain ⟨K, hK, z, w, hzB, -, hw, -, hcomb⟩ := eq_pos_convex_span_of_mem_convexHull hcC
    obtain ⟨m, hm⟩ := exists_nat_combination_neg z w (fun k => (hw k).le)
      (fun l => by rw [hcomb]; exact hcN l)
    set M := ∑ k, m k with hM
    refine ⟨M, fun r hr0 hpo => ?_⟩
    -- an enumeration of the `M` copies
    have hcard : Fintype.card (Σ k, Fin (m k)) = M := by simp [hM]
    set e : Fin M ≃ Σ k, Fin (m k) := (Fintype.equivFinOfCardEq hcard).symm with he
    set d : Fin L → ℝ := -∑ k, (m k : ℝ) • z k with hd
    have hdpos : ∀ l, 0 < d l := fun l => by
      simp only [hd, Pi.neg_apply]; linarith [hm l]
    have hMpos : 0 < M := by
      by_contra h0
      push Not at h0
      have hm0 : ∀ k, m k = 0 := fun k => by
        have := Finset.single_le_sum (f := m) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
        omega
      have := hm ⟨0, hL⟩
      simp [hm0] at this
    have hr1 : 0 < r := lt_of_lt_of_le hMpos hr0
    set φ : ℕ → Fin L → ℝ := fun n => if h : n < M then z (e ⟨n, h⟩).1 else 0 with hφ
    set x' : Fin r → Fin L → ℝ := fun i => ω + φ i + if (i : ℕ) = 0 then d else 0 with hx'
    have hzX : ∀ k, ω + z k ∈ nonnegOrthant L := fun k => (hzB ⟨k, rfl⟩).1
    have hzS : ∀ k, Strict R (ω + z k) ω := fun k => (hzB ⟨k, rfl⟩).2
    have hφX : ∀ n, ω + φ n ∈ nonnegOrthant L := fun n => by
      by_cases h : n < M
      · simp only [hφ, h, ↓reduceDIte]; exact hzX _
      · simp only [hφ, h, ↓reduceDIte, add_zero]; exact hωX
    have hsumφ : ∑ i : Fin r, φ i = -d := by
      rw [Fin.sum_univ_eq_sum_range (fun n => φ n), ← Finset.sum_range_add_sum_Ico _ hr0]
      have h2 : ∑ n ∈ Finset.Ico M r, φ n = 0 :=
        Finset.sum_eq_zero fun n hn => by
          simp only [hφ, not_lt.mpr (Finset.mem_Ico.mp hn).1, ↓reduceDIte]
      rw [h2, add_zero, ← Fin.sum_univ_eq_sum_range (fun n => φ n)]
      have h3 : ∑ i : Fin M, φ i = ∑ i : Fin M, z (e i).1 :=
        Finset.sum_congr rfl fun i _ => by simp [hφ, i.isLt]
      rw [h3, hd, neg_neg, Equiv.sum_comp e (fun σ => z σ.1), Fintype.sum_sigma]
      simp [Nat.cast_smul_eq_nsmul]
    have hx'X : ∀ i, x' i ∈ nonnegOrthant L := by
      intro i l
      have := hφX i l
      simp only [hx', Pi.add_apply] at this ⊢
      split_ifs
      · linarith [hdpos l]
      · simpa using this
    have hφS : ∀ n, n < M → Strict R (ω + φ n) ω := by
      intro n hn
      simp only [hφ, hn, ↓reduceDIte]
      exact hzS _
    have hxR : ∀ i : Fin r, R (x' i) (ω + φ i) := by
      intro i
      by_cases h0 : (i : ℕ) = 0
      · refine (hmono (ω + φ i) (hφX i) (x' i) (hx'X i) (fun l => ?_) ?_).1
        · simp only [hx', h0, ↓reduceIte, Pi.add_apply]
          linarith [hdpos l]
        · intro heq
          have := congrFun heq ⟨0, hL⟩
          simp only [hx', h0, ↓reduceIte, Pi.add_apply] at this
          linarith [hdpos ⟨0, hL⟩]
      · have : x' i = ω + φ i := by simp only [hx', h0, ↓reduceIte, add_zero]
        rw [this]
        exact (hr.1 _ (hφX i) _ (hφX i)).elim id id
    apply hpo.2
    refine ⟨⟨x', fun _ => 0⟩, ⟨⟨hx'X, fun _ => fun _ => le_rfl⟩, ?_⟩, fun i => ?_,
      ⟨0, hr1⟩, ?_⟩
    · change ∑ i, x' i = (r : ℝ) • ω + ∑ _j : Unit, (0 : Fin L → ℝ)
      simp only [hx', Finset.sum_add_distrib, hsumφ, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, Fintype.card_unit, one_smul, add_zero]
      have : (∑ x : Fin r, if (x : ℕ) = 0 then d else 0) = d := by
        rw [Finset.sum_eq_single (⟨0, hr1⟩ : Fin r)]
        · simp
        · intro i _ hi
          have : (i : ℕ) ≠ 0 := fun h => hi (Fin.ext h)
          simp [this]
        · simp
      rw [this, neg_add_cancel_right, Nat.cast_smul_eq_nsmul]
    · change R (x' i) ω
      by_cases h : (i : ℕ) < M
      · exact (strict_of_pref_of_strict hr.2 (hx'X i) (hφX i) hωX (hxR i) (hφS i h)).1
      · have hφ0 : φ i = 0 := by simp only [hφ, h, ↓reduceDIte]
        have := hxR i
        rwa [hφ0, add_zero] at this
    · change Strict R (x' ⟨0, hr1⟩) ω
      exact strict_of_pref_of_strict hr.2 (hx'X _) (hφX 0) hωX (hxR ⟨0, hr1⟩) (hφS 0 hMpos)

/-- A preference represented by a utility function is rational. -/
theorem rationalOn_utilityPref (X : Set (Fin L → ℝ)) (u : (Fin L → ℝ) → ℝ) :
    RationalOn X (utilityPref u) :=
  ⟨fun x _ y _ => le_total (u y) (u x), fun _ _ _ _ _ _ hxy hyz => le_trans hyz hxy⟩

/-- A preference represented by a utility function continuous on `X` is continuous on `X`
(Definition 3.C.1). -/
theorem prefContinuous_utilityPref {X : Set (Fin L → ℝ)} {u : (Fin L → ℝ) → ℝ}
    (hu : ContinuousOn u X) : PrefContinuous X (utilityPref u) := by
  intro xs ys x y hxs hys hx hy hle htx hty
  have h1 : Tendsto (fun n => u (xs n)) atTop (𝓝 (u x)) :=
    (hu x hx).tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨htx, Eventually.of_forall hxs⟩)
  have h2 : Tendsto (fun n => u (ys n)) atTop (𝓝 (u y)) :=
    (hu y hy).tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨hty, Eventually.of_forall hys⟩)
  exact le_of_tendsto_of_tendsto' h2 h1 hle

/-- The nonconvex preference of Figures 16.D.4-16.D.6: `u(x) = x₁² + x₂²`. -/
def sqNormU (x : Fin 2 → ℝ) : ℝ := x 0 ^ 2 + x 1 ^ 2

/-- `u(x) = x₁² + x₂²` is strongly monotone on `ℝ²₊`. -/
theorem sqNormU_stronglyMonotone :
    PrefStronglyMonotone (nonnegOrthant 2) (utilityPref sqNormU) := by
  intro x hx y _ hxy hne
  have h0 := hxy 0
  have h1 := hxy 1
  have hx0 := hx 0
  have hx1 := hx 1
  have hlt : x 0 < y 0 ∨ x 1 < y 1 := by
    by_contra h
    push Not at h
    exact hne (funext fun l => by fin_cases l <;> simp <;> linarith [h.1, h.2])
  have : sqNormU x < sqNormU y := by
    unfold sqNormU
    rcases hlt with h | h <;> nlinarith
  exact ⟨this.le, not_le.mpr this⟩

/-- **Figure 16.D.4** (MWG, p. 558). In the one-consumer economy with `u(x) = x₁² + x₂²`,
`ω = (2, 2)` and free disposal, consuming the endowment is (trivially) Pareto optimal, but it is
not a price equilibrium with transfers for any prices: at any `p ≥ 0` one of the corners
`(4, 0)`, `(0, 4)` is affordable and better. -/
theorem figure_16_D_4 :
    (replicaEconomy (utilityPref sqNormU) ![2, 2] 1).IsParetoOptimal (symmetricAlloc ![2, 2] 1) ∧
      ∀ p w, ¬ (replicaEconomy (utilityPref sqNormU) ![2, 2] 1).IsPriceEqmWithTransfers
        (symmetricAlloc ![2, 2] 1) p w := by
  refine ⟨⟨⟨⟨fun _ l => ?_, fun _ _ => le_rfl⟩, ?_⟩, ?_⟩, fun p w h => ?_⟩
  · fin_cases l <;> norm_num [symmetricAlloc]
  · simp [replicaEconomy, symmetricAlloc]
  · rintro ⟨a', ⟨⟨hx', hy'⟩, hc'⟩, -, k, hk⟩
    apply hk.2
    have hk0 : k = 0 := Subsingleton.elim _ _
    subst hk0
    have h0 := congrFun hc' 0
    have h1 := congrFun hc' 1
    simp [replicaEconomy] at h0 h1
    have hy0 := hy' () 0
    have hy1 := hy' () 1
    have hx0 := hx' 0 0
    have hx1 := hx' 0 1
    change sqNormU (a'.x 0) ≤ sqNormU ![2, 2]
    unfold sqNormU
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    nlinarith
  · have hp : ∀ l, 0 ≤ p l := footnote_9 (h.2.1 ())
    have hw : w 0 = 2 * p 0 + 2 * p 1 := by
      have := h.1
      simp [replicaEconomy, symmetricAlloc, dotProduct, Fin.sum_univ_two] at this
      linarith
    rcases le_total (p 1) (p 0) with hle | hle
    · have hb : (![0, 4] : Fin 2 → ℝ) ∈ budgetSetOn (nonnegOrthant 2) p (w 0) :=
        ⟨fun l => by fin_cases l <;> norm_num, by rw [dot_two, hw]; simp; linarith⟩
      have := (h.2.2.1 0).2 _ hb
      change sqNormU ![0, 4] ≤ sqNormU ![2, 2] at this
      norm_num [sqNormU] at this
    · have hb : (![4, 0] : Fin 2 → ℝ) ∈ budgetSetOn (nonnegOrthant 2) p (w 0) :=
        ⟨fun l => by fin_cases l <;> norm_num, by rw [dot_two, hw]; simp; linarith⟩
      have := (h.2.2.1 0).2 _ hb
      change sqNormU ![4, 0] ≤ sqNormU ![2, 2] at this
      norm_num [sqNormU] at this

/-- **Figure 16.D.5** (MWG, pp. 557-558). In the two-consumer replica (endowments doubled to
`2ω`), `x'₁ = ω + (1, -1)`, `x'₂ = ω + (-1, 1)` Pareto dominates the symmetric allocation, which is
therefore no longer Pareto optimal. The preference satisfies the hypotheses of Exercise 16.D.4. -/
theorem figure_16_D_5 :
    RationalOn (nonnegOrthant 2) (utilityPref sqNormU) ∧
      PrefContinuous (nonnegOrthant 2) (utilityPref sqNormU) ∧
      PrefStronglyMonotone (nonnegOrthant 2) (utilityPref sqNormU) ∧
      (replicaEconomy (utilityPref sqNormU) ![2, 2] 2).ParetoDominates
        ⟨![![3, 1], ![1, 3]], fun _ => 0⟩ (symmetricAlloc ![2, 2] 2) ∧
      (replicaEconomy (utilityPref sqNormU) ![2, 2] 2).IsFeasible
        ⟨![![3, 1], ![1, 3]], fun _ => 0⟩ ∧
      ¬ (replicaEconomy (utilityPref sqNormU) ![2, 2] 2).IsParetoOptimal
        (symmetricAlloc ![2, 2] 2) := by
  have hdom : (replicaEconomy (utilityPref sqNormU) ![2, 2] 2).ParetoDominates
      ⟨![![3, 1], ![1, 3]], fun _ => 0⟩ (symmetricAlloc ![2, 2] 2) := by
    refine ⟨fun i => ?_, 0, ?_, ?_⟩
    · fin_cases i <;> norm_num [replicaEconomy, utilityPref, symmetricAlloc, sqNormU]
    · norm_num [replicaEconomy, utilityPref, symmetricAlloc, sqNormU]
    · norm_num [replicaEconomy, utilityPref, symmetricAlloc, sqNormU]
  have hfeas : (replicaEconomy (utilityPref sqNormU) ![2, 2] 2).IsFeasible
      ⟨![![3, 1], ![1, 3]], fun _ => 0⟩ := by
    refine ⟨⟨fun i l => ?_, fun _ _ => le_rfl⟩, ?_⟩
    · fin_cases i <;> fin_cases l <;> norm_num [replicaEconomy]
    · funext l
      fin_cases l <;> norm_num [replicaEconomy, Fin.sum_univ_two]
  refine ⟨rationalOn_utilityPref _ _, prefContinuous_utilityPref (by unfold sqNormU; fun_prop),
    sqNormU_stronglyMonotone, hdom, hfeas, fun h => h.2 ⟨_, hfeas, hdom⟩⟩

end MWG.WelfareTheorems
