/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGWelfareBargaining.BargainingAxioms
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Characterizations by monotonicity: the egalitarian solution

MWG, Section 22.E, small type (ii) (p. 845) and Exercise 22.E.5(a) (p. 854).

* `MonotoneBS`: `U ⊆ U'` (same threat point) implies `f(U) ≤ f(U')`; `egal_monotoneBS`.
* `exercise_22_E_5a`: the egalitarian solution is the only bargaining solution that is
  independent of utility origins, (weakly) Paretian, symmetric and monotone. The lower bound
  `f(U) ≥ e` uses the symmetric box `{u ≤ e}` inside `U`. The upper bound uses, for every
  `δ > 0`, a half-space `{c·u ≤ c·(e + δ𝟙)}` with `c ≫ 0` containing `U`
  (`exists_pos_supporting`): `f` of that half-space is `e + δ𝟙`, by the box argument and
  `c ≫ 0`. The supporting half-space comes from the Hahn-Banach separation of `U` from an open
  convex cone around `e + δ/2 𝟙` slightly wider than the positive orthant, which forces the
  normal to be strictly positive.
-/

namespace MWG.WelfareBargaining

open BargainingProblem

variable {ι : Type*} [Fintype ι]

/-- **Section 22.E, small type (ii)** (MWG, p. 845). A bargaining solution is monotone if
`U ⊆ U'` (same threat point) implies `f(U) ≤ f(U')`. -/
def MonotoneBS (f : BargainingProblem ι → ι → ℝ) : Prop :=
  ∀ P P' : BargainingProblem ι, P.U ⊆ P'.U → P.d = P'.d → f P ≤ f P'

omit [Fintype ι] in
theorem egal_monotoneBS [Finite ι] [Nonempty ι] : MonotoneBS (egal (ι := ι)) := by
  cases nonempty_fintype ι
  exact fun P P' hsub hd i => egal_monotone hsub hd i

/-- A symmetric, weakly Paretian bargaining solution selects the corner of a symmetric box. -/
theorem sym_box [Nonempty ι] {f : BargainingProblem ι → ι → ℝ} (hf : IsBargainingSolution f)
    (hP : ParetoBS f) (hS : SymmetricBS f) {a : ℝ} (ha : 0 < a) :
    f (boxProblem (fun _ => a) fun _ => ha) = fun _ => a := by
  set B := boxProblem (fun _ : ι => a) fun _ => ha
  have hsym : IsSymmetricSet B.U := fun σ u hu i => hu (σ i)
  have heq := hS B hsym (fun _ _ => rfl)
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hle : f B i₀ ≤ a := hf B i₀
  have hge : a ≤ f B i₀ := by
    by_contra hlt
    exact hP B ⟨fun _ => a, show (fun _ => a) ≤ fun _ => a from le_rfl,
      fun i => by rw [heq i i₀]; exact not_le.1 hlt⟩
  funext i
  rw [heq i i₀]; linarith

/-- A linear functional on `ℝ^ι` is `u ↦ ∑ uᵢ f(eᵢ)`. -/
theorem clm_apply_eq_sum [DecidableEq ι] (f : (ι → ℝ) →L[ℝ] ℝ) (u : ι → ℝ) :
    f u = ∑ i, u i * f (Pi.single i 1) := by
  conv_lhs => rw [show u = ∑ i, u i • Pi.single i (1 : ℝ) by
    funext j; simp [Finset.sum_apply, Pi.single_apply]]
  simp [map_sum, map_smul]

/-- **Exercise 22.E.5(a)**, the supporting half-space (MWG, p. 854). For a normalized problem
with egalitarian level `m` and any `δ > 0` there is `c ≫ 0` with `c·u ≤ c·((m + δ)𝟙)` on `U`. -/
theorem exists_pos_supporting [Nonempty ι] (Q : BargainingProblem ι) (hd : Q.d = 0) {δ : ℝ}
    (hδ : 0 < δ) : ∃ c : ι → ℝ, (∀ i, 0 < c i) ∧
      ∀ u ∈ Q.U, ∑ i, c i * u i ≤ ∑ i, c i * (Q.rayLevel (fun _ => 1) + δ) := by
  classical
  set m := Q.rayLevel (fun _ => 1) with hm
  have hm0 : 0 < m := Q.rayLevel_pos fun _ => one_pos
  -- no point of `U` is `≥ (m + η)𝟙` with `η > 0`
  have hnot : ∀ η, 0 < η → ∀ u ∈ Q.U, ¬∀ i, m + η ≤ u i := by
    intro η hη u hu hall
    have hmem : m + η ∈ Q.raySet (fun _ => 1) :=
      ⟨by linarith, Q.comprehensive _ hu _ fun i => by simp [hd, hall i]⟩
    linarith [Q.le_rayLevel (fun _ => one_pos) hmem]
  obtain ⟨ρ, hρ, hρmem⟩ := Q.exists_gt
  have hρU : (fun _ : ι => ρ) ∈ Q.U := by simpa [hd] using hρmem
  obtain ⟨B, hB⟩ := Q.bdd
  set B' := |B| + 1 with hB'
  have hB'pos : 0 < B' := by positivity
  set n : ℝ := ((Fintype.card ι : ℕ) : ℝ) with hn
  have hnpos : 0 < n := by rw [hn]; exact_mod_cast Fintype.card_pos
  set ε := ρ * δ / (4 * n * B' * (ρ + δ)) with hε
  have hεpos : 0 < ε := by positivity
  set y : ι → ℝ := fun _ => m + δ / 2 with hy
  set O : Set (ι → ℝ) := {a | ∀ i, 0 < (a i - y i) + ε * ∑ j, (a j - y j)} with hO
  -- `O` and `U` are disjoint
  have hdisj : Disjoint O Q.U := by
    rw [Set.disjoint_left]
    intro u hu huU
    set S := ∑ j, (u j - y j) with hS
    have hui : ∀ i, y i - ε * S < u i := fun i => by have := hu i; linarith
    by_cases hcase : ε * S ≤ δ / 4
    · exact hnot (δ / 4) (by linarith) u huU fun i => by
        have := hui i; simp only [hy] at this; linarith
    · have hcase : δ / 4 < ε * S := not_le.1 hcase
      have hSpos : 0 < S := by
        by_contra h; have : ε * S ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hεpos.le (not_lt.1 h)
        linarith
      set lam := ρ / (ρ + 4 * ε * S) with hlam
      have hlam0 : 0 < lam := by positivity
      have hlam1 : lam < 1 := by rw [hlam, div_lt_one (by positivity)]; nlinarith
      have hw : lam • u + (1 - lam) • (fun _ : ι => ρ) ∈ Q.U :=
        Q.convex huU hρU hlam0.le (by linarith) (by ring)
      -- the mixture is positive
      have hlamS : lam * (ε * S) = ρ * (ε * S) / (ρ + 4 * ε * S) := by rw [hlam]; ring
      have e1 : (1 - lam) * ρ = 4 * (lam * (ε * S)) := by
        rw [hlam]; field_simp; ring
      have hlεS : 0 < lam * (ε * S) := by positivity
      have hwpos : ∀ i, 0 ≤ (lam • u + (1 - lam) • (fun _ : ι => ρ)) i := by
        intro i
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        have h1 := hui i
        simp only [hy] at h1
        have h2 : lam * (m + δ / 2 - ε * S) < lam * u i := mul_lt_mul_of_pos_left h1 hlam0
        nlinarith [mul_pos hlam0 hm0, mul_pos hlam0 hδ]
      -- its coordinates are bounded by `B`, but its total is at least `λS > n B'`
      have hbound := fun i => hB _ hw (fun j => by rw [hd]; exact hwpos j) i
      have hsum_le : ∑ i, (lam • u + (1 - lam) • (fun _ : ι => ρ)) i ≤ n * B' := by
        calc ∑ i, (lam • u + (1 - lam) • (fun _ : ι => ρ)) i ≤ ∑ _i : ι, B' :=
              Finset.sum_le_sum fun i _ => (hbound i).trans (by rw [hB']; linarith [le_abs_self B])
          _ = n * B' := by simp [hn]
      have hsum_ge : lam * S < ∑ i, (lam • u + (1 - lam) • (fun _ : ι => ρ)) i := by
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
          ← Finset.mul_sum]
        have : ∑ i, u i = S + n * (m + δ / 2) := by
          simp only [hS, hy, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
            nsmul_eq_mul, hn]; ring
        rw [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        have : 0 < 1 - lam := by linarith
        nlinarith [mul_pos hlam0 (mul_pos hnpos (by linarith : 0 < m + δ / 2)),
          mul_pos this (mul_pos (by exact_mod_cast Fintype.card_pos : (0 : ℝ) < Fintype.card ι)
            hρ)]
      have hlamS' : n * B' ≤ lam * S := by
        -- `λS = ρS/(ρ + 4εS) ≥ ρδ/(4ε(ρ + δ)) = nB'`
        have hεe : ε * (4 * n * B' * (ρ + δ)) = ρ * δ := by rw [hε]; field_simp
        have e : n * B' * (4 * ε * (ρ + δ)) = ρ * δ := by linear_combination hεe
        have hden : 0 < 4 * ε * (ρ + δ) := by positivity
        have key : n * B' * (ρ + 4 * ε * S) * (4 * ε * (ρ + δ)) ≤
            ρ * S * (4 * ε * (ρ + δ)) := by
          calc n * B' * (ρ + 4 * ε * S) * (4 * ε * (ρ + δ)) = ρ * δ * (ρ + 4 * ε * S) := by
                linear_combination (ρ + 4 * ε * S) * e
            _ ≤ ρ * S * (4 * ε * (ρ + δ)) := by nlinarith [mul_pos hρ hρ]
        have key' := le_of_mul_le_mul_right key hden
        rw [hlam, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        linarith
      linarith
  -- separate the open convex set `O` from `U`
  have hOconv : Convex ℝ O := by
    intro a ha b hb s t hs ht hst i
    have e : ∀ j, (s • a + t • b) j - y j = s * (a j - y j) + t * (b j - y j) := fun j => by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have : y j = (s + t) * y j := by rw [hst, one_mul]
      linarith [this]
    simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum]
    rcases hs.lt_or_eq with hs' | hs'
    · nlinarith [ha i, hb i, mul_pos hs' (ha i), mul_nonneg ht (hb i).le]
    · subst hs'
      have ht1 : t = 1 := by linarith
      subst ht1
      simpa using hb i
  have hOopen : IsOpen O := by
    simp only [hO, Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const
      (((continuous_apply i).sub continuous_const).add (continuous_const.mul
        (continuous_finsetSum _ fun j _ => (continuous_apply j).sub continuous_const)))
  obtain ⟨f, s, hfO, hfU⟩ := geometric_hahn_banach_open hOconv hOopen Q.convex hdisj
  set c : ι → ℝ := fun i => -f (Pi.single i 1) with hc
  have hfeq : ∀ v, f v = -∑ i, c i * v i := fun v => by
    rw [clm_apply_eq_sum f v]; simp [hc, mul_comm]
  -- `O` is stable under adding elements of the cone `K`, so `f ≤ 0` on `K`
  have hcone : ∀ a ∈ O, ∀ k : ι → ℝ, (∀ i, 0 < k i + ε * ∑ j, k j) → f k ≤ 0 := by
    intro a ha k hk
    by_contra hpos
    have hpos : 0 < f k := not_le.1 hpos
    have hsa : 0 < s - f a := by linarith [hfO a ha]
    set t := (s - f a) / f k + 1 with ht
    have htpos : 0 < t := by have := div_pos hsa hpos; linarith
    have hmem : a + t • k ∈ O := by
      intro i
      have e : ∀ j, (a + t • k) j - y j = (a j - y j) + t * k j := fun j => by
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
      simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum]
      nlinarith [ha i, hk i, mul_pos htpos (hk i)]
    have h1 := hfO _ hmem
    rw [map_add, map_smul, smul_eq_mul, ht, add_mul, div_mul_cancel₀ _ hpos.ne', one_mul] at h1
    linarith
  have hyO : (fun _ : ι => m + δ) ∈ O := by
    intro i
    simp only [hy]
    have : ∑ j : ι, (m + δ - (m + δ / 2)) = n * (δ / 2) := by simp [hn]; ring
    rw [this]
    have : 0 < ε * (n * (δ / 2)) := by positivity
    linarith
  -- `c ≥ 0`, `c ≠ 0`, `cᵢ ≥ a cⱼ`
  have hsingle_mem : ∀ i, ∀ k : ι → ℝ, k = Pi.single i 1 →
      ∀ l, 0 < k l + ε * ∑ j, k j := by
    intro i k hk l
    subst hk
    have : ∑ j, (Pi.single i (1 : ℝ) : ι → ℝ) j = 1 := by simp
    rw [this]
    by_cases hl : l = i
    · have e : (Pi.single i (1 : ℝ) : ι → ℝ) l = 1 := by subst hl; simp
      rw [e]; linarith
    · have e : (Pi.single i (1 : ℝ) : ι → ℝ) l = 0 := by simp [hl]
      rw [e]; linarith
  have hc0 : ∀ i, 0 ≤ c i := fun i => by
    have := hcone _ hyO _ (hsingle_mem i _ rfl)
    simp only [hc]; linarith
  set a₀ := ε / (2 * (1 + ε)) with ha₀
  have ha₀pos : 0 < a₀ := by positivity
  have ha₀lt : a₀ < ε / (1 + ε) := by
    rw [ha₀, div_lt_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have ha₀1 : a₀ < 1 := lt_of_lt_of_le ha₀lt (by rw [div_le_one (by positivity)]; linarith)
  have hcij : ∀ i j, i ≠ j → a₀ * c j ≤ c i := by
    intro i j hij
    set k : ι → ℝ := Pi.single i 1 - a₀ • Pi.single j 1 with hk
    have hsum : ∑ l, k l = 1 - a₀ := by
      simp [hk, Finset.sum_sub_distrib, ← Finset.mul_sum]
    have hkK : ∀ l, 0 < k l + ε * ∑ j, k j := by
      intro l
      rw [hsum]
      by_cases hl : l = i
      · have e : k l = 1 := by subst hl; simp [hk, Ne.symm hij]
        rw [e]; nlinarith
      by_cases hl' : l = j
      · have e : k l = -a₀ := by subst hl'; simp [hk, hl]
        rw [e]
        have : a₀ * (1 + ε) < ε := by rwa [lt_div_iff₀ (by positivity)] at ha₀lt
        nlinarith
      · have e : k l = 0 := by simp [hk, hl, hl']
        rw [e]; nlinarith
    have := hcone _ hyO k hkK
    simp only [hk, map_sub, map_smul, smul_eq_mul] at this
    simp only [hc]; linarith
  have hcne : ∃ j, 0 < c j := by
    by_contra hall
    have hall : ∀ j, c j = 0 := fun j => le_antisymm (not_lt.1 fun h => hall ⟨j, h⟩) (hc0 j)
    have h1 := hfO _ hyO
    have h2 := hfU _ Q.d_mem
    rw [hfeq] at h1 h2
    simp [hall] at h1 h2
    linarith
  obtain ⟨j₀, hj₀⟩ := hcne
  have hcpos : ∀ i, 0 < c i := fun i => by
    by_cases h : i = j₀
    · rw [h]; exact hj₀
    · exact lt_of_lt_of_le (mul_pos ha₀pos hj₀) (hcij i j₀ h)
  refine ⟨c, hcpos, fun u hu => ?_⟩
  have h1 := hfO _ hyO
  have h2 := hfU u hu
  rw [hfeq] at h1 h2
  linarith

/-- **Exercise 22.E.5(a)** (MWG, p. 854). The egalitarian solution is the only bargaining
solution that is independent of utility origins, Paretian (weak Pareto, Definition 22.E.4),
symmetric and monotone. -/
theorem exercise_22_E_5a [Nonempty ι] {f : BargainingProblem ι → ι → ℝ}
    (hf : IsBargainingSolution f) (hIUO : IUO f) (hP : ParetoBS f) (hS : SymmetricBS f)
    (hM : MonotoneBS f) : f = egal := by
  -- reduce to normalized problems
  have key : ∀ Q : BargainingProblem ι, Q.d = 0 → f Q = egal Q := by
    intro Q hd
    set m := Q.rayLevel (fun _ => 1) with hm
    have hm0 : 0 < m := Q.rayLevel_pos fun _ => one_pos
    have he : egal Q = fun _ => m := by funext i; simp [egal, rayPoint, hd, hm]
    have hmem : (fun _ : ι => m) ∈ Q.U := he ▸ Q.rayPoint_mem fun _ => one_pos
    rw [he]
    funext i
    apply le_antisymm
    · -- upper bound through the supporting half-spaces
      refine le_of_forall_pos_lt_add fun δ hδ => ?_
      obtain ⟨c, hc, hsupp⟩ := exists_pos_supporting Q hd (half_pos hδ)
      set r := ∑ j, c j * (m + δ / 2) with hr
      have hrpos : 0 < r := Finset.sum_pos (fun j _ => mul_pos (hc j) (by linarith))
        Finset.univ_nonempty
      set H := halfSpace c hc r hrpos
      have hsub : Q.U ⊆ H.U := fun u hu => (halfSpace_U c hc r hrpos u).2 (hsupp u hu)
      have hHd : Q.d = H.d := by rw [hd]; rfl
      have hbox : (boxProblem (fun _ : ι => m + δ / 2) fun _ => by linarith).U ⊆ H.U :=
        fun u hu => (halfSpace_U c hc r hrpos u).2 (Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (hu j) (hc j).le)
      have hfH : f H = fun _ => m + δ / 2 := by
        have hlow := hM _ H hbox rfl
        rw [sym_box hf hP hS (by linarith)] at hlow
        have hin := (halfSpace_U c hc r hrpos _).1 (hf H)
        funext j
        by_contra hne
        have hlt : m + δ / 2 < f H j := lt_of_le_of_ne (hlow j) (Ne.symm hne)
        have : r < ∑ k, c k * f H k := Finset.sum_lt_sum
          (fun k _ => mul_le_mul_of_nonneg_left (hlow k) (hc k).le)
          ⟨j, Finset.mem_univ j, mul_lt_mul_of_pos_left hlt (hc j)⟩
        linarith
      have := hM Q H hsub hHd i
      rw [hfH] at this
      linarith
    · -- lower bound through the box `{u ≤ m𝟙}`
      have hbox : (boxProblem (fun _ : ι => m) fun _ => hm0).U ⊆ Q.U :=
        fun u hu => Q.comprehensive _ hmem _ hu
      have := hM _ Q hbox (by rw [hd]; rfl) i
      rwa [sym_box hf hP hS hm0] at this
  funext P
  rw [normalize_eq hIUO P, normalize_eq egal_IUO P, key _ P.normalize_d]

/-- **Exercise 22.E.5(a)**, the hypotheses hold (MWG, p. 854): the egalitarian solution is a
bargaining solution that is IUO, Paretian, symmetric and monotone. -/
theorem exercise_22_E_5a_instance [Nonempty ι] :
    IsBargainingSolution (egal (ι := ι)) ∧ IUO (egal (ι := ι)) ∧ ParetoBS (egal (ι := ι)) ∧
      SymmetricBS (egal (ι := ι)) ∧ MonotoneBS (egal (ι := ι)) :=
  ⟨example_22_E_1.1, example_22_E_1.2.1, example_22_E_1.2.2.1, example_22_E_1.2.2.2.1,
    egal_monotoneBS⟩

end MWG.WelfareBargaining
