/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGCoreFoundations.CoopGames
import MWGProduction.AppendixMM

/-!
# Balanced games and the Bondareva-Shapley theorem (MWG Exercise 18.AA.1, p. 685)

* Generalized partitions `S₁, ..., S_N` with weights `δₙ ∈ [0, 1]` and
  `∑_{n : i ∈ Sₙ} δₙ = 1` for every player (indexed by `Fin N`, as in the book):
  `IsGeneralizedPartition`, with the examples asked for (`exercise_18_AA_1_singletons`: an
  ordinary partition with unit weights; `exercise_18_AA_1_pairs`: the three pairs of a
  three-player game with weights `1/2`).
* Balanced TU games (`IsBalanced`), and the theorem: the core is nonempty iff the game is balanced
  (`exercise_18_AA_1`). The hard direction is proved with Chapter 5's Farkas lemma
  (`MWG.Production.farkas`, the theorem of the alternative behind the duality theorem of
  Section M.M): a homogenised system in `ℝ^{I+1}` whose alternative is a balanced family violating
  balancedness.
-/

namespace MWG.CoreFoundations

variable {n : ℕ}

/-- **Exercise 18.AA.1** (MWG, p. 685). `S₁, ..., S_N` (coalitions) form a generalized partition
with weights `δₙ ∈ [0, 1]`: `∑_{n : i ∈ Sₙ} δₙ = 1` for every player `i`. -/
def IsGeneralizedPartition {N : ℕ} (S : Fin N → Finset (Fin n)) (δ : Fin N → ℝ) : Prop :=
  (∀ k, (S k).Nonempty) ∧ (∀ k, 0 ≤ δ k ∧ δ k ≤ 1) ∧
    ∀ i, ∑ k ∈ Finset.univ.filter (fun k => i ∈ S k), δ k = 1

/-- **Exercise 18.AA.1** (MWG, p. 685). The TU game `v` is balanced: `∑ₙ δₙ v(Sₙ) ≤ v(I)` for every
generalized partition. -/
def IsBalanced (v : WelfareBargaining.Game n) : Prop :=
  ∀ (N : ℕ) (S : Fin N → Finset (Fin n)) (δ : Fin N → ℝ), IsGeneralizedPartition S δ →
    ∑ k, δ k * v (S k) ≤ v Finset.univ

/-- **Exercise 18.AA.1** (MWG, p. 685), example: an ordinary partition (here into singletons)
with unit weights is a generalized partition. -/
theorem exercise_18_AA_1_singletons :
    IsGeneralizedPartition (n := n) (N := n) (fun k => {k}) (fun _ => 1) := by
  refine ⟨fun k => Finset.singleton_nonempty k, fun _ => ⟨zero_le_one, le_rfl⟩, fun i => ?_⟩
  have : Finset.univ.filter (fun k : Fin n => i ∈ ({k} : Finset (Fin n))) = {i} := by
    ext k; simp [eq_comm]
  rw [this]; simp

/-- **Exercise 18.AA.1** (MWG, p. 685), example: with three players, the three pairs
`{1, 2}, {1, 3}, {2, 3}` with weights `1/2` form a generalized partition. -/
theorem exercise_18_AA_1_pairs :
    IsGeneralizedPartition (n := 3) (N := 3) ![{0, 1}, {0, 2}, {1, 2}] (fun _ => 1 / 2) := by
  refine ⟨fun k => ?_, fun _ => ⟨by norm_num, by norm_num⟩, fun i => ?_⟩
  · fin_cases k <;> simp
  · rw [Finset.sum_filter]
    fin_cases i <;> simp [Fin.sum_univ_three] <;> norm_num

/-- **Exercise 18.AA.1** (MWG, p. 685), easy direction: a TU game with a nonempty core is
balanced. -/
theorem isBalanced_of_core {v : WelfareBargaining.Game n} (h : (tuCore v).Nonempty) :
    IsBalanced v := by
  obtain ⟨u, hS, htot⟩ := h
  intro N S δ ⟨hne, hδ, hsum⟩
  have hswap : ∀ k, δ k * ∑ i ∈ S k, u i = ∑ i, if i ∈ S k then δ k * u i else 0 := by
    intro k
    rw [Finset.mul_sum, ← Finset.sum_filter, Finset.filter_univ_mem]
  calc ∑ k, δ k * v (S k) ≤ ∑ k, δ k * ∑ i ∈ S k, u i :=
        Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hS _ (hne k)) (hδ k).1
    _ = ∑ i, u i * ∑ k ∈ Finset.univ.filter (fun k => i ∈ S k), δ k := by
        simp only [hswap]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_filter, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        split_ifs <;> ring
    _ = ∑ i, u i := by simp [hsum]
    _ ≤ v Finset.univ := htot

/-- **Exercise 18.AA.1** (MWG, p. 685). The generators of the cone used in the proof of the
Bondareva-Shapley theorem, in `ℝ^{I+1}`: `(1, ..., 1, -v(I))` and, for every coalition `S`,
`(-𝟙_S, v(S))`. -/
noncomputable def bsGen (v : WelfareBargaining.Game n) :
    Option {S : Finset (Fin n) // S.Nonempty} → Fin (n + 1) → ℝ := fun o => by
  classical
  exact match o with
  | none => Fin.snoc (α := fun _ => ℝ) (fun _ => 1) (-(v Finset.univ))
  | some S => Fin.snoc (α := fun _ => ℝ) (fun i => -(if i ∈ S.1 then 1 else 0)) (v S.1)

/-- **Exercise 18.AA.1** (MWG, p. 685). Dot products with vectors of `ℝ^{I+1}` written as `(p, x)`.
-/
theorem dotProduct_snoc (y : Fin (n + 1) → ℝ) (p : Fin n → ℝ) (x : ℝ) :
    y ⬝ᵥ (Fin.snoc (α := fun _ => ℝ) p x) =
      ∑ i : Fin n, y i.castSucc * p i + y (Fin.last n) * x := by
  simp [dotProduct, Fin.sum_univ_castSucc]

/-- **Exercise 18.AA.1** (MWG, p. 685). The first `I` coordinates of `(p, x)`. -/
theorem snoc_apply_castSucc (p : Fin n → ℝ) (x : ℝ) (i : Fin n) :
    (Fin.snoc (α := fun _ => ℝ) p x : Fin (n + 1) → ℝ) i.castSucc = p i := by simp

/-- **Exercise 18.AA.1** (MWG, p. 685). The last coordinate of `(p, x)`. -/
theorem snoc_apply_last (p : Fin n → ℝ) (x : ℝ) :
    (Fin.snoc (α := fun _ => ℝ) p x : Fin (n + 1) → ℝ) (Fin.last n) = x := by simp

/-- **Exercise 18.AA.1** (MWG, p. 685), hard direction (Bondareva-Shapley): a balanced TU game
has a nonempty core. Proof by Farkas' lemma (LP duality, Section M.M). -/
theorem core_nonempty_of_isBalanced {v : WelfareBargaining.Game n} (hb : IsBalanced v) :
    (tuCore v).Nonempty := by
  classical
  set b : Fin (n + 1) → ℝ := Fin.snoc (α := fun _ => ℝ) (fun _ => 0) 1 with hbdef
  have hnot : ¬ ∃ lam : Option {S : Finset (Fin n) // S.Nonempty} → ℝ, 0 ≤ lam ∧
      b = ∑ o, lam o • bsGen v o := by
    rintro ⟨lam, hlam, hbeq⟩
    set μ := lam none with hμ
    -- coordinate equations
    have hcoord : ∀ i : Fin n,
        ∑ S : {S : Finset (Fin n) // S.Nonempty}, (if i ∈ S.1 then lam (some S) else 0) = μ := by
      intro i
      have h := congrFun hbeq i.castSucc
      simp only [hbdef, snoc_apply_castSucc, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        Fintype.sum_option, bsGen] at h
      have e : ∀ S : {S : Finset (Fin n) // S.Nonempty},
          lam (some S) * -(if i ∈ S.1 then (1 : ℝ) else 0) =
            -(if i ∈ S.1 then lam (some S) else 0) := fun S => by split_ifs <;> ring
      simp only [e, Finset.sum_neg_distrib, mul_one] at h
      linarith
    have hlast : ∑ S : {S : Finset (Fin n) // S.Nonempty}, lam (some S) * v S.1 =
        1 + μ * v Finset.univ := by
      have h := congrFun hbeq (Fin.last n)
      simp only [hbdef, snoc_apply_last, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        Fintype.sum_option, bsGen] at h
      linarith
    have hlam0 : ∀ o, 0 ≤ lam o := fun o => hlam o
    rcases eq_or_lt_of_le (hlam0 none) with hμ0 | hμpos
    · -- μ = 0: all weights vanish
      have hμz : μ = 0 := by rw [hμ]; exact hμ0.symm
      have hz : ∀ S : {S : Finset (Fin n) // S.Nonempty}, lam (some S) = 0 := by
        intro S
        obtain ⟨i, hi⟩ := S.2
        have h := hcoord i
        rw [hμz] at h
        have := (Finset.sum_eq_zero_iff_of_nonneg fun S' _ => by
          split_ifs
          · exact hlam0 _
          · exact le_rfl).1 h S (Finset.mem_univ S)
        simpa [hi] using this
      simp only [hz, zero_mul, Finset.sum_const_zero] at hlast
      rw [hμz] at hlast
      linarith
    · -- μ > 0: a balanced family violating balancedness
      have hμ' : 0 < μ := hμpos
      set e := Fintype.equivFin {S : Finset (Fin n) // S.Nonempty}
      set N := Fintype.card {S : Finset (Fin n) // S.Nonempty}
      set Sk : Fin N → Finset (Fin n) := fun k => (e.symm k).1
      set δ : Fin N → ℝ := fun k => lam (some (e.symm k)) / μ
      have hsumδ : ∀ i, ∑ k ∈ Finset.univ.filter (fun k => i ∈ Sk k), δ k = 1 := by
        intro i
        rw [Finset.sum_filter]
        have := Equiv.sum_comp e.symm
          (fun S : {S : Finset (Fin n) // S.Nonempty} => if i ∈ S.1 then lam (some S) / μ else 0)
        simp only [Sk, δ]
        rw [this]
        have e2 : ∀ S : {S : Finset (Fin n) // S.Nonempty},
            (if i ∈ S.1 then lam (some S) / μ else 0) = (if i ∈ S.1 then lam (some S) else 0) / μ :=
          fun S => by split_ifs <;> simp
        simp only [e2, ← Finset.sum_div, hcoord i]
        exact div_self hμ'.ne'
      have hδnn : ∀ k, 0 ≤ δ k := fun k => div_nonneg (hlam0 _) hμ'.le
      have hpart : IsGeneralizedPartition Sk δ := by
        refine ⟨fun k => (e.symm k).2, fun k => ⟨hδnn k, ?_⟩, hsumδ⟩
        obtain ⟨i, hi⟩ := (e.symm k).2
        rw [← hsumδ i]
        exact Finset.single_le_sum (fun k' _ => hδnn k')
          (Finset.mem_filter.2 ⟨Finset.mem_univ k, hi⟩)
      have hval := hb N Sk δ hpart
      have hrew : ∑ k, δ k * v (Sk k) = (1 + μ * v Finset.univ) / μ := by
        rw [← hlast, Finset.sum_div]
        have := Equiv.sum_comp e.symm
          (fun S : {S : Finset (Fin n) // S.Nonempty} => lam (some S) * v S.1 / μ)
        rw [← this]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [δ, Sk]; ring
      rw [hrew, div_le_iff₀ hμ'] at hval
      linarith
  have hy := (not_not.1 (mt (MWG.Production.farkas (bsGen v) b).2 hnot))
  obtain ⟨y, hya, hyb⟩ := hy
  set t := y (Fin.last n) with ht
  have htpos : 0 < t := by
    rw [hbdef, dotProduct_snoc] at hyb
    simpa using hyb
  refine ⟨fun i => y i.castSucc / t, fun S hS => ?_, ?_⟩
  · have h := hya (some ⟨S, hS⟩)
    simp only [bsGen, dotProduct_snoc] at h
    have e : ∀ i : Fin n, y i.castSucc * -(if i ∈ S then (1 : ℝ) else 0) =
        -(if i ∈ S then y i.castSucc else 0) := fun i => by split_ifs <;> ring
    simp only [e, Finset.sum_neg_distrib, ← Finset.sum_filter, Finset.filter_univ_mem] at h
    rw [← Finset.sum_div, le_div_iff₀ htpos]
    linarith
  · have h := hya none
    simp only [bsGen, dotProduct_snoc, mul_one] at h
    rw [← Finset.sum_div, div_le_iff₀ htpos]
    linarith

/-- **Exercise 18.AA.1** (MWG, p. 685), the Bondareva-Shapley theorem: a TU game has a nonempty
core if and only if it is balanced. -/
theorem exercise_18_AA_1 (v : WelfareBargaining.Game n) :
    (tuCore v).Nonempty ↔ IsBalanced v :=
  ⟨isBalanced_of_core, core_nonempty_of_isBalanced⟩

end MWG.CoreFoundations
