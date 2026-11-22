/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGWelfareBargaining.BargainingSolutions

/-!
# Computations and counterexamples for Section 22.E

MWG, Examples 22.E.1-22.E.4, the monotonicity remarks of p. 845 (Figure 22.E.9) and Exercises
22.E.4, 22.E.9, 22.E.10 and 22.F.1.

We compute the Nash, Kalai-Smorodinsky, egalitarian and utilitarian solutions of half-space
problems `{∑ cᵢuᵢ ≤ r}` and of box problems `{u ≤ b}` (threat point `0`), and obtain:
the egalitarian and utilitarian solutions violate IUU; the Kalai-Smorodinsky solution violates
IIA and differs from the Nash solution; the utilitarian, Nash and Kalai-Smorodinsky solutions are
not monotone; a utilitarian solution can violate IIA on convex, not strictly convex problems;
the five axioms of Proposition 22.E.1 are independent; and in the transferable utility case
every IUO, Paretian, symmetric solution splits the gains equally.
-/

namespace MWG.WelfareBargaining

open Set BargainingProblem

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
theorem halfSpace_d [Fintype ι] (c : ι → ℝ) (hc : ∀ i, 0 < c i) (r : ℝ) (hr : 0 < r) :
    (halfSpace c hc r hr).d = 0 := rfl

/-- The Nash solution of a half-space problem: `ûᵢ = r/(I cᵢ)`. -/
theorem nash_halfSpace [Nonempty ι] (c : ι → ℝ) (hc : ∀ i, 0 < c i) (r : ℝ) (hr : 0 < r) :
    nash (halfSpace c hc r hr) = fun i => r / (Fintype.card ι * c i) := by
  have hn : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 Fintype.card_pos
  have key : ∀ i, c i * (r / (Fintype.card ι * c i) - 0) = r / Fintype.card ι := fun i => by
    rw [sub_zero]; field_simp [(hc i).ne']
  have e : ∑ i, c i * (r / (Fintype.card ι * c i) - 0) = r := by
    rw [Finset.sum_congr rfl fun i _ => key i, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    field_simp
  apply nash_of_utilitarian_egalitarian (η := c) (γ := r / Fintype.card ι) (div_pos hr hn) hc
  · rw [halfSpace_U]; simpa using e.le
  · intro u hu
    rw [halfSpace_U] at hu
    simp only [halfSpace_d, Pi.zero_apply]
    rw [e]; simpa using hu
  · intro i; simp only [halfSpace_d, Pi.zero_apply]; exact key i

/-- The ideal point of a half-space problem: `u^i = r/cᵢ`. -/
theorem ideal_halfSpace (c : ι → ℝ) (hc : ∀ i, 0 < c i) (r : ℝ) (hr : 0 < r) (i : ι) :
    (halfSpace c hc r hr).ideal i = r / c i := by
  classical
  apply ideal_eq
  · refine ⟨fun j => if j = i then r / c i else 0, ?_, fun j => ?_, by simp⟩
    · rw [halfSpace_U]
      simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      field_simp [(hc i).ne']; rfl
    · simp only [halfSpace_d, Pi.zero_apply]; split_ifs
      · exact (div_pos hr (hc i)).le
      · exact le_rfl
  · intro u hu hdu
    rw [halfSpace_U] at hu
    have hdu' : ∀ j, 0 ≤ u j := fun j => by have := hdu j; rwa [halfSpace_d] at this
    have := le_trans (Finset.single_le_sum (f := fun j => c j * u j)
      (fun j _ => mul_nonneg (hc j).le (hdu' j)) (Finset.mem_univ i)) hu
    rw [le_div_iff₀ (hc i)]; linarith

/-- The Kalai-Smorodinsky solution of a half-space problem coincides with its Nash solution. -/
theorem ks_halfSpace [Nonempty ι] (c : ι → ℝ) (hc : ∀ i, 0 < c i) (r : ℝ) (hr : 0 < r) :
    ks (halfSpace c hc r hr) = fun i => r / (Fintype.card ι * c i) := by
  set P := halfSpace c hc r hr
  have hPd : P.d = 0 := rfl
  have hn : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 Fintype.card_pos
  have hgap : P.idealGap = fun i => r / c i := by
    funext i; simp only [idealGap, ideal_halfSpace, P, halfSpace_d, Pi.zero_apply, sub_zero]
  have hw : ∀ i, 0 < P.idealGap i := P.idealGap_pos
  have hlev : P.rayLevel P.idealGap = 1 / Fintype.card ι := by
    apply P.rayLevel_eq hw
    · refine ⟨by positivity, ?_⟩
      rw [halfSpace_U, hgap]
      simp only [hPd, Pi.zero_apply, zero_add]
      have : ∀ i, c i * (1 / (Fintype.card ι : ℝ) * (r / c i)) = r / Fintype.card ι :=
        fun i => by field_simp [(hc i).ne']
      simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp; rfl
    · rintro t ⟨-, ht⟩
      rw [halfSpace_U, hgap] at ht
      simp only [hPd, Pi.zero_apply, zero_add] at ht
      have : ∀ i, c i * (t * (r / c i)) = t * r := fun i => by field_simp [(hc i).ne']
      simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at ht
      rw [le_div_iff₀ hn]
      nlinarith
  rw [hgap] at hlev
  funext i
  simp only [ks, rayPoint, hgap, hlev, hPd, Pi.zero_apply, zero_add]
  field_simp

/-- The box problem `{u ≤ b}` with threat point `0`, `b ≫ 0`. -/
def boxProblem (b : ι → ℝ) (hb : ∀ i, 0 < b i) : BargainingProblem ι where
  U := {u | u ≤ b}
  d := 0
  convex := convex_Iic b
  closed := isClosed_Iic
  comprehensive := fun _ hu _ hv => hv.trans hu
  interior_d := by
    have hopen : IsOpen {u : ι → ℝ | ∀ i, u i < b i} := by
      simp only [ofPred_forall]
      exact isOpen_iInter_of_finite fun i => isOpen_lt (continuous_apply i) continuous_const
    exact mem_interior.2 ⟨_, fun u hu i => (hu i).le, hopen, fun i => hb i⟩
  bdd := ⟨∑ i, b i, fun u hu _ i => (hu i).trans (Finset.single_le_sum (f := b)
    (fun j _ => (hb j).le) (Finset.mem_univ i))⟩

/-- The Nash solution of a box is its corner. -/
theorem nash_box [Nonempty ι] (b : ι → ℝ) (hb : ∀ i, 0 < b i) : nash (boxProblem b hb) = b := by
  apply nash_of_utilitarian_egalitarian (η := fun i => 1 / b i) (γ := 1) one_pos
    (fun i => one_div_pos.2 (hb i)) (show b ∈ (boxProblem b hb).U from le_refl b)
  · intro u hu
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (by
      simp only [boxProblem, Pi.zero_apply, sub_zero]; exact hu i) (one_div_pos.2 (hb i)).le
  · intro i; simp only [boxProblem, Pi.zero_apply, sub_zero]; field_simp [(hb i).ne']

/-- The utilitarian solution of a box is its corner. -/
theorem utilSol_box (b : ι → ℝ) (hb : ∀ i, 0 < b i) : utilSol (boxProblem b hb) = b := by
  have h := utilSol_spec (boxProblem b hb)
  have hle : utilSol (boxProblem b hb) ≤ b := h.1
  have hsum : ∑ i, (b i - 0) ≤ ∑ i, (utilSol (boxProblem b hb) i - 0) :=
    h.2.2 b (show b ∈ (boxProblem b hb).U from le_refl b) (fun i => (hb i).le)
  simp only [sub_zero] at hsum
  funext i
  by_contra hne
  have hlt : utilSol (boxProblem b hb) i < b i := lt_of_le_of_ne (hle i) hne
  have : ∑ j, utilSol (boxProblem b hb) j < ∑ j, b j :=
    Finset.sum_lt_sum (fun j _ => hle j) ⟨i, Finset.mem_univ i, hlt⟩
  linarith

/-- The Kalai-Smorodinsky solution of a box is its corner. -/
theorem ks_box [Nonempty ι] (b : ι → ℝ) (hb : ∀ i, 0 < b i) : ks (boxProblem b hb) = b := by
  set P := boxProblem b hb
  have hideal : ∀ i, P.ideal i = b i := fun i => P.ideal_eq i ⟨b, le_refl b,
    fun j => (hb j).le, rfl⟩ fun u hu _ => hu i
  have hPd : P.d = 0 := rfl
  have hgap : P.idealGap = b := by
    funext i; simp only [idealGap, hideal, hPd, Pi.zero_apply, sub_zero]
  have hlev : P.rayLevel P.idealGap = 1 := by
    rw [hgap]
    apply P.rayLevel_eq hb ⟨zero_le_one, fun i => by simp [P, boxProblem]⟩
    rintro t ⟨-, ht⟩
    obtain ⟨i⟩ := ‹Nonempty ι›
    have := ht i
    simp only [P, boxProblem, Pi.zero_apply, zero_add] at this
    nlinarith [hb i]
  rw [hgap] at hlev
  funext i
  simp only [ks, rayPoint, hgap, hlev, one_mul, hPd, Pi.zero_apply, zero_add]

/-- `{u ≤ (1, 1)} ⊆ {u₁ + 3u₂ ≤ 4}`. -/
theorem box_sub_halfSpace :
    (boxProblem (ι := Fin 2) ![1, 1] (fun i => by fin_cases i <;> norm_num)).U ⊆
      (halfSpace ![1, 3] (fun i => by fin_cases i <;> norm_num) 4 (by norm_num)).U := by
  intro u hu
  rw [halfSpace_U, Fin.sum_univ_two]
  have h0 := hu 0; have h1 := hu 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1 ⊢
  linarith

/-- **Section 22.E, monotonicity** (MWG, p. 845, Figure 22.E.9). The Nash, Kalai-Smorodinsky and
utilitarian solutions are not monotone: enlarging `U = {u ≤ (1,1)}` to `U' = {u₁ + 3u₂ ≤ 4}` (same
threat point) lowers agent 2's payoff from `1` to `2/3`, `2/3` and `0` respectively. -/
theorem not_monotone_nash_ks_util :
    let B := boxProblem (ι := Fin 2) ![1, 1] (fun i => by fin_cases i <;> norm_num)
    let H := halfSpace ![1, 3] (fun i => by fin_cases i <;> norm_num) 4 (by norm_num)
    B.U ⊆ H.U ∧ B.d = H.d ∧ nash H 1 < nash B 1 ∧ ks H 1 < ks B 1 ∧
      utilSol H 1 < utilSol B 1 := by
  intro B H
  refine ⟨box_sub_halfSpace, rfl, ?_, ?_, ?_⟩
  · rw [nash_box, nash_halfSpace]; norm_num
  · rw [ks_box, ks_halfSpace]; norm_num
  · rw [utilSol_box]
    have h := utilSol_spec H
    have hu : (![4, 0] : Fin 2 → ℝ) ∈ H.U := by
      rw [halfSpace_U, Fin.sum_univ_two]; norm_num
    have hle := h.2.2 _ hu (fun i => by fin_cases i <;> simp [halfSpace_d, H])
    have hmem := h.1
    rw [halfSpace_U, Fin.sum_univ_two] at hmem
    have h0 := h.2.1 0; have h1 := h.2.1 1
    simp only [halfSpace_d, Pi.zero_apply, sub_zero, Fin.sum_univ_two, H] at hle h0 h1 hmem
    norm_num at hle hmem ⊢
    linarith

/-- **Example 22.E.1** (MWG, p. 841). The egalitarian solution violates IUU. -/
theorem egal_not_IUU : ¬IUU (egal (ι := Fin 2)) := by
  intro h
  set P := halfSpace (ι := Fin 2) (fun _ => 1) (fun _ => one_pos) 2 two_pos
  have hβ : ∀ i, (0 : ℝ) < ![2, 1] i := fun i => by fin_cases i <;> norm_num
  have e := h P ![2, 1] hβ
  have hsym : egal P 0 = egal P 1 := (example_22_E_1.2.2.2.1) P
    (halfSpace_symmetric 1 one_pos 2 two_pos) (fun _ _ => rfl) 0 1
  have h0 := congrFun e 0
  have h1 := congrFun e 1
  have hs : egal (P.scale ![2, 1] hβ) 0 = egal (P.scale ![2, 1] hβ) 1 := by
    simp [egal, rayPoint, scale_d, P, halfSpace_d]
  have hpos := P.rayPoint_ge (fun _ => one_pos) 0
  simp only [halfSpace_d, Pi.zero_apply, P] at hpos
  have hpos' : 0 < egal P 0 := lt_of_le_of_ne hpos (by
    intro h0'
    exact (P.rayLevel_pos (fun _ => one_pos)).ne' (by
      simpa [egal, rayPoint, P, halfSpace_d] using h0'.symm))
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  rw [hs, h1, hsym] at h0
  linarith

/-- **Example 22.E.2** (MWG, p. 841). The utilitarian solution violates IUU: on
`U = {u₁ + 2u₂ ≤ 2}` it is `(2, 0)`, but after rescaling by `β = (1, 4)` the point `(0, 4)`
gives a larger sum than `β(2, 0)`. -/
theorem utilSol_not_IUU : ¬IUU (utilSol (ι := Fin 2)) := by
  intro h
  set P := halfSpace (ι := Fin 2) ![1, 2] (fun i => by fin_cases i <;> norm_num) 2 two_pos
  have hβ : ∀ i, (0 : ℝ) < ![1, 4] i := fun i => by fin_cases i <;> norm_num
  have hP : utilSol P = ![2, 0] := by
    have hs := utilSol_spec P
    have hmem := hs.1
    rw [halfSpace_U, Fin.sum_univ_two] at hmem
    have hle := hs.2.2 ![2, 0] (by rw [halfSpace_U, Fin.sum_univ_two]; norm_num)
      (fun i => by fin_cases i <;> simp [halfSpace_d, P])
    have h0 := hs.2.1 0; have h1 := hs.2.1 1
    simp only [halfSpace_d, Pi.zero_apply, sub_zero, Fin.sum_univ_two, P] at hle h0 h1 hmem
    norm_num at hle hmem
    funext i; fin_cases i <;> simp <;> linarith
  have e := h P ![1, 4] hβ
  have hs := utilSol_spec (P.scale ![1, 4] hβ)
  have hmem : (![0, 4] : Fin 2 → ℝ) ∈ (P.scale ![1, 4] hβ).U := by
    rw [scale_U, halfSpace_U, Fin.sum_univ_two]; norm_num
  have hle := hs.2.2 _ hmem (fun i => by fin_cases i <;> simp [scale_d, P, halfSpace_d])
  rw [e, hP] at hle
  simp [Fin.sum_univ_two, scale_d, P, halfSpace_d] at hle
  norm_num at hle

/-- Intersection of a problem with a half-space `{∑ cᵢuᵢ ≤ r}` (`c ≥ 0`) containing the threat
point in its interior. -/
def interHalf (P : BargainingProblem ι) (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i) (r : ℝ)
    (hd : ∑ i, c i * P.d i < r) : BargainingProblem ι where
  U := P.U ∩ {u | ∑ i, c i * u i ≤ r}
  d := P.d
  convex := by
    refine P.convex.inter fun x hx y hy a b ha hb hab => ?_
    simp only [mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hx hy ⊢
    have : ∑ i, c i * (a * x i + b * y i) = a * ∑ i, c i * x i + b * ∑ i, c i * y i := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [this]
    calc a * ∑ i, c i * x i + b * ∑ i, c i * y i ≤ a * r + b * r :=
          add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
      _ = r := by rw [← add_mul, hab, one_mul]
  closed := P.closed.inter (isClosed_le (continuous_finsetSum _ fun i _ =>
    continuous_const.mul (continuous_apply i)) continuous_const)
  comprehensive := fun u hu v hv => ⟨P.comprehensive _ hu.1 _ hv, le_trans
    (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hv i) (hc i)) hu.2⟩
  interior_d := by
    rw [interior_inter]
    refine ⟨P.interior_d, ?_⟩
    have hopen : IsOpen {u : ι → ℝ | ∑ i, c i * u i < r} := isOpen_lt
      (continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_apply i))
      continuous_const
    exact interior_mono (fun u (hu : _ < r) => hu.le) (hopen.interior_eq.symm ▸ hd)
  bdd := by
    obtain ⟨B, hB⟩ := P.bdd
    exact ⟨B, fun u hu => hB u hu.1⟩

/-- The two problems of the Kalai-Smorodinsky counterexample: `U = {u₁ + u₂ ≤ 2}` and
`U' = U ∩ {u₂ ≤ 1}`. -/
noncomputable def ksBig : BargainingProblem (Fin 2) :=
  halfSpace (fun _ => 1) (fun _ => one_pos) 2 two_pos

noncomputable def ksSmall : BargainingProblem (Fin 2) :=
  interHalf ksBig ![0, 1] (fun i => by fin_cases i <;> norm_num) 1 (by
    simp [ksBig, halfSpace_d])

theorem mem_ksSmall (u : Fin 2 → ℝ) : u ∈ ksSmall.U ↔ u 0 + u 1 ≤ 2 ∧ u 1 ≤ 1 := by
  simp [ksSmall, interHalf, ksBig, halfSpace_U, Fin.sum_univ_two]

theorem ks_ksSmall : ks ksSmall = ![4 / 3, 2 / 3] := by
  have hd : ksSmall.d = 0 := rfl
  have hi0 : ksSmall.ideal 0 = 2 := ksSmall.ideal_eq 0 ⟨![2, 0], by rw [mem_ksSmall]; norm_num,
    fun i => by fin_cases i <;> simp [hd], rfl⟩ fun u hu hdu => by
      rw [mem_ksSmall] at hu; have := hdu 1; simp [hd] at this; linarith
  have hi1 : ksSmall.ideal 1 = 1 := ksSmall.ideal_eq 1 ⟨![0, 1], by rw [mem_ksSmall]; norm_num,
    fun i => by fin_cases i <;> simp [hd], rfl⟩ fun u hu _ => by
      rw [mem_ksSmall] at hu; exact hu.2
  have hgap : ksSmall.idealGap = ![2, 1] := by
    funext i; fin_cases i <;> simp [idealGap, hi0, hi1, hd]
  have hw : ∀ i, (0 : ℝ) < ![2, 1] i := fun i => by fin_cases i <;> norm_num
  have hlev : ksSmall.rayLevel ![2, 1] = 2 / 3 := by
    apply ksSmall.rayLevel_eq hw ⟨by norm_num, by rw [mem_ksSmall]; simp [hd]; norm_num⟩
    rintro t ⟨-, ht⟩
    rw [mem_ksSmall] at ht
    simp [hd] at ht
    linarith [ht.1]
  funext i
  fin_cases i <;> norm_num [ks, rayPoint, hgap, hlev, hd]

/-- **Example 22.E.4 and Exercise 22.E.4** (MWG, pp. 844, 853). The Kalai-Smorodinsky solution
violates IIA: `f(U) = (1, 1) ∈ U' ⊆ U` but `f(U') = (4/3, 2/3)`; on `U'` it differs from the
Nash solution `(1, 1)`. -/
theorem ks_not_IIA : ¬IIA (ks (ι := Fin 2)) ∧ ks ksSmall ≠ nash ksSmall := by
  have hbig : ks ksBig = fun _ => 1 := by
    rw [ksBig, ks_halfSpace]; funext i; norm_num
  have hnbig : nash ksBig = fun _ => 1 := by
    rw [ksBig, nash_halfSpace]; funext i; norm_num
  have hsub : ksSmall.U ⊆ ksBig.U := fun u hu => hu.1
  have hmem : (fun _ : Fin 2 => (1 : ℝ)) ∈ ksSmall.U := by rw [mem_ksSmall]; norm_num
  have hne : (![4 / 3, 2 / 3] : Fin 2 → ℝ) ≠ fun _ => 1 := by
    intro h; have := congrFun h 0; norm_num at this
  have hnsmall : nash ksSmall = fun _ => 1 := by
    rw [show nash ksSmall = nashSol (fun _ => 1) ksSmall from rfl,
      (nashSol_IIA (fun _ => one_pos)) ksBig ksSmall hsub rfl (by
      rw [show nashSol (fun _ => (1 : ℝ)) ksBig = nash ksBig from rfl, hnbig]; exact hmem)]
    exact hnbig
  refine ⟨fun h => ?_, ?_⟩
  · have := h ksBig ksSmall hsub rfl (by rw [hbig]; exact hmem)
    rw [ks_ksSmall, hbig] at this
    exact hne this
  · rw [ks_ksSmall, hnsmall]; exact hne

/-- **Exercise 22.E.10** (MWG, p. 854). Some utilitarian bargaining solution (one selecting a
maximizer of `∑ uᵢ` on `U ∩ ℝ^I₊` in every problem) violates IIA; the problems involved are
convex but not strictly convex. -/
theorem exercise_22_E_10 : ∃ f : BargainingProblem (Fin 2) → Fin 2 → ℝ,
    (∀ P, IsUtilPoint P (f P)) ∧ ¬IIA f := by
  classical
  set A := ksBig
  set B := interHalf ksBig ![1, 0] (fun i => by fin_cases i <;> norm_num) (3 / 2) (by
    simp [ksBig, halfSpace_d])
  have hmemB : ∀ u, u ∈ B.U ↔ u 0 + u 1 ≤ 2 ∧ u 0 ≤ 3 / 2 := fun u => by
    simp [B, interHalf, ksBig, halfSpace_U, Fin.sum_univ_two]
  have hAB : A ≠ B := by
    intro h
    have : (![2, 0] : Fin 2 → ℝ) ∈ B.U := by
      rw [← h]; simp [A, ksBig, halfSpace_U, Fin.sum_univ_two]
    rw [hmemB] at this; norm_num at this
  have hA : ∀ u ∈ A.U, A.d ≤ u → ∑ i, (u i - A.d i) ≤ 2 := fun u hu _ => by
    simpa [A, ksBig, halfSpace_U, halfSpace_d] using hu
  have hutilA : IsUtilPoint A (fun _ => 1) := ⟨by simp [A, ksBig, halfSpace_U],
    fun i => by simp [A, ksBig, halfSpace_d], fun u hu hdu => by
      have := hA u hu hdu; simp [A, ksBig, halfSpace_d, Fin.sum_univ_two] at this ⊢
      linarith⟩
  have hutilB : IsUtilPoint B ![1 / 2, 3 / 2] := ⟨by rw [hmemB]; norm_num,
    fun i => by fin_cases i <;> norm_num [B, interHalf, ksBig, halfSpace_d],
    fun u hu hdu => by
      rw [hmemB] at hu
      simp [B, interHalf, ksBig, halfSpace_d, Fin.sum_univ_two]
      norm_num; linarith [hu.1]⟩
  refine ⟨fun P => if P = A then fun _ => 1 else if P = B then ![1 / 2, 3 / 2]
    else Classical.choose (exists_utilPoint P), fun P => ?_, fun h => ?_⟩
  · dsimp only
    split_ifs with h1 h2
    · rw [h1]; exact hutilA
    · rw [h2]; exact hutilB
    · exact Classical.choose_spec (exists_utilPoint P)
  · have := h A B (fun u hu => hu.1) rfl (by
      simp only [↓reduceIte]; rw [hmemB]; norm_num)
    simp only [↓reduceIte, Ne.symm hAB] at this
    have := congrFun this 0
    norm_num at this

/-- **Exercise 22.F.1** (MWG, p. 855). In the transferable utility case `U = {∑ uᵢ ≤ s}` with
threat point `0` (after normalisation), any symmetric, Paretian bargaining solution divides the
gains equally: `fᵢ = s/I`. With independence of utility origins this gives
`fᵢ(v) = v(i) + (v(I) - ∑ₕ v(h))/I` for any threat point. -/
theorem exercise_22_F_1 [Nonempty ι] {f : BargainingProblem ι → ι → ℝ}
    (hB : IsBargainingSolution f) (hP : ParetoBS f) (hS : SymmetricBS f) (s : ℝ) (hs : 0 < s) :
    f (halfSpace (fun _ => 1) (fun _ => one_pos) s hs) = fun _ => s / Fintype.card ι := by
  set P := halfSpace (ι := ι) (fun _ => 1) (fun _ => one_pos) s hs
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hsym : ∀ i, f P i = f P i₀ := fun i =>
    hS _ (halfSpace_symmetric 1 one_pos _ _) (fun _ _ => rfl) i i₀
  set t := f P i₀
  have hn : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 Fintype.card_pos
  have hmem : (Fintype.card ι : ℝ) * t ≤ s := by
    have : ∑ i, (1 : ℝ) * f P i ≤ s := hB P
    simpa only [one_mul, hsym, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using this
  have ht : t = s / Fintype.card ι := by
    by_contra hne
    have hlt : t < s / Fintype.card ι := lt_of_le_of_ne (by rw [le_div_iff₀ hn]; linarith) hne
    apply hP P
    refine ⟨fun _ => (t + s / Fintype.card ι) / 2, ?_, fun i => by rw [hsym]; linarith⟩
    change ∑ i, (1 : ℝ) * ((t + s / Fintype.card ι) / 2) ≤ s
    simp only [one_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have : (Fintype.card ι : ℝ) * (s / Fintype.card ι) = s := by field_simp
    nlinarith
  funext i
  rw [hsym, ht]

/-- **Exercise 22.F.1**, with the threat point: under IUO the solution of the transferable
utility problem `(U + v, v)` is `vᵢ + s/I`. -/
theorem exercise_22_F_1_threat [Nonempty ι] {f : BargainingProblem ι → ι → ℝ}
    (hB : IsBargainingSolution f) (hO : IUO f) (hP : ParetoBS f) (hS : SymmetricBS f) (s : ℝ)
    (hs : 0 < s) (v : ι → ℝ) :
    f ((halfSpace (fun _ => 1) (fun _ => one_pos) s hs).translate v) =
      fun i => v i + s / Fintype.card ι := by
  rw [hO, exercise_22_F_1 hB hP hS s hs]
  funext i; simp [add_comm]

end MWG.WelfareBargaining
