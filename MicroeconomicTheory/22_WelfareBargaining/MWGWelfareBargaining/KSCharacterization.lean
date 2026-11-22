/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGWelfareBargaining.Characterizations

/-!
# The Kalai-Smorodinsky solution characterized by partial monotonicity

MWG, Section 22.E, small type (ii) (p. 845) and Exercise 22.E.6 (p. 854), two agents.

`f` is partially monotone if `U ⊆ U'` (same threat point) and `u^i(U) = u^i(U')` imply
`f_j(U') ≥ f_j(U)` for `j ≠ i`.

* `ks_partiallyMonotone`: the Kalai-Smorodinsky solution is partially monotone.
* `exercise_22_E_6`: it is the only bargaining solution that is independent of utility origins
  and units, Paretian, symmetric and partially monotone. After normalizing (`u* = 0`, ideal
  point `(1, 1)`) the solution `(t, t)` is also the solution of the symmetric quadrilateral `T`
  with vertices `0`-dominated by `(1, 0)`, `(t, t)`, `(0, 1)`, which lies in `U` and has the
  same ideal point; partial monotonicity gives `f(U) ≥ (t, t)`, and since the ideal values are
  attained, a point above `(t, t)` other than `(t, t)` would let a convex combination strictly
  dominate `(t, t)`.
-/

namespace MWG.WelfareBargaining

open BargainingProblem

/-- **Exercise 22.E.6** (MWG, p. 854). Partial monotonicity (two agents). -/
def PartiallyMonotoneBS (f : BargainingProblem (Fin 2) → Fin 2 → ℝ) : Prop :=
  ∀ P P' : BargainingProblem (Fin 2), P.U ⊆ P'.U → P.d = P'.d → ∀ i, P.ideal i = P'.ideal i →
    ∀ j, j ≠ i → f P j ≤ f P' j

theorem ideal_mono {P P' : BargainingProblem (Fin 2)} (hsub : P.U ⊆ P'.U) (hd : P.d = P'.d)
    (j : Fin 2) : P.ideal j ≤ P'.ideal j := by
  obtain ⟨⟨u, hu, hdu, huj⟩, -⟩ := P.ideal_spec j
  rw [← huj]
  exact (P'.ideal_spec j).2 u (hsub hu) (hd ▸ hdu)

/-- **Exercise 22.E.6** (MWG, p. 854). The Kalai-Smorodinsky solution is partially monotone:
with `g, g'` the gaps to the ideal points (`gᵢ = g'ᵢ`, `gⱼ ≤ g'ⱼ`) and levels `t, t'`, if
`t'g'ⱼ < tgⱼ` then `u* + s g' ≤ u* + t g ∈ U'` for `s = min(t, tgⱼ/g'ⱼ) > t'`. -/
theorem ks_partiallyMonotone : PartiallyMonotoneBS ks := by
  intro P P' hsub hd i hi j hji
  have hgi : P.idealGap i = P'.idealGap i := by simp [idealGap, hi, hd]
  have hgj : P.idealGap j ≤ P'.idealGap j := by
    simp only [idealGap, hd]; linarith [ideal_mono hsub hd j]
  have hg : ∀ k, 0 < P.idealGap k := P.idealGap_pos
  have hg' : ∀ k, 0 < P'.idealGap k := P'.idealGap_pos
  set t := P.rayLevel P.idealGap
  set t' := P'.rayLevel P'.idealGap
  have ht : 0 < t := P.rayLevel_pos hg
  simp only [ks, rayPoint, hd]
  by_contra hlt
  have hlt : t' * P'.idealGap j < t * P.idealGap j := by
    have := not_le.1 hlt; linarith
  have htt : t' < t := by
    by_contra h
    have h : t ≤ t' := not_lt.1 h
    nlinarith [hg' j, hg j, mul_le_mul_of_nonneg_right h (hg' j).le,
      mul_le_mul_of_nonneg_left hgj ht.le]
  set s := min t (t * P.idealGap j / P'.idealGap j)
  have hs : t' < s := lt_min htt (by rw [lt_div_iff₀ (hg' j)]; linarith)
  have hsle : s ≤ t := min_le_left _ _
  have hsle2 : s * P'.idealGap j ≤ t * P.idealGap j := by
    have := min_le_right t (t * P.idealGap j / P'.idealGap j)
    rw [le_div_iff₀ (hg' j)] at this; exact this
  have hsle1 : s * P'.idealGap i ≤ t * P.idealGap i := by
    rw [hgi]; exact mul_le_mul_of_nonneg_right hsle (hg' i).le
  have hmem : s ∈ P'.raySet P'.idealGap := by
    refine ⟨le_trans (P'.rayLevel_pos hg').le hs.le, P'.comprehensive _ (hsub (P.rayPoint_mem hg))
      _ fun k => ?_⟩
    simp only [rayPoint, ← hd]
    have hk : k = i ∨ k = j := by
      rcases i with ⟨i, hi'⟩; rcases j with ⟨j, hj'⟩; rcases k with ⟨k, hk'⟩
      simp only [ne_eq, Fin.mk.injEq] at hji ⊢
      omega
    rcases hk with rfl | rfl
    · linarith
    · linarith
  linarith [P'.le_rayLevel hg' hmem]

/-- The quadrilateral `{tu₁ + (1-t)u₂ ≤ t, (1-t)u₁ + tu₂ ≤ t, u₁ ≤ 1, u₂ ≤ 1}`, `0 < t < 1`:
the comprehensive convex hull of `(1, 0)`, `(t, t)`, `(0, 1)`. -/
noncomputable def ksQuad (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) : BargainingProblem (Fin 2) :=
  interHalf (interHalf (interHalf (halfSpace ![t, 1 - t]
    (fun i => by fin_cases i <;> simp [ht0, ht1]) t ht0) ![1 - t, t]
    (fun i => by fin_cases i <;> simp [ht0.le, ht1.le]) t (by simp [halfSpace_d, ht0]))
    ![1, 0] (fun i => by fin_cases i <;> simp) 1 (by simp [interHalf, halfSpace_d]))
    ![0, 1] (fun i => by fin_cases i <;> simp) 1 (by simp [interHalf, halfSpace_d])

theorem mem_ksQuad {t : ℝ} {ht0 : 0 < t} {ht1 : t < 1} (u : Fin 2 → ℝ) :
    u ∈ (ksQuad t ht0 ht1).U ↔ t * u 0 + (1 - t) * u 1 ≤ t ∧ (1 - t) * u 0 + t * u 1 ≤ t ∧
      u 0 ≤ 1 ∧ u 1 ≤ 1 := by
  simp [ksQuad, interHalf, halfSpace_U, Fin.sum_univ_two, and_assoc]

theorem ksQuad_d {t : ℝ} {ht0 : 0 < t} {ht1 : t < 1} : (ksQuad t ht0 ht1).d = 0 := rfl

theorem fin2_cases (a : Fin 2) : a = 0 ∨ a = 1 := by fin_cases a <;> simp

/-- **Exercise 22.E.6** (MWG, p. 854). Partial monotonicity together with IUO, IUU, P and S
characterizes the Kalai-Smorodinsky solution for two agents. -/
theorem exercise_22_E_6 {f : BargainingProblem (Fin 2) → Fin 2 → ℝ}
    (hf : IsBargainingSolution f) (hIUO : IUO f) (hIUU : IUU f) (hP : ParetoBS f)
    (hS : SymmetricBS f) (hM : PartiallyMonotoneBS f) : f = ks := by
  -- Step A: normalized problems (`u* = 0`, ideal point `(1, 1)`)
  have keyA : ∀ Q : BargainingProblem (Fin 2), Q.d = 0 → (∀ i, Q.ideal i = 1) → f Q = ks Q := by
    intro Q hd hid
    have hgap : Q.idealGap = fun _ => 1 := by funext i; simp [idealGap, hid, hd]
    set t := Q.rayLevel (fun _ => (1 : ℝ)) with htdef
    have ht0 : 0 < t := Q.rayLevel_pos fun _ => one_pos
    have hks : ks Q = fun _ => t := by funext i; simp [ks, rayPoint, hgap, hd, htdef]
    have hkmem : (fun _ : Fin 2 => t) ∈ Q.U := hks ▸ Q.rayPoint_mem Q.idealGap_pos
    have hkpar : ¬∃ v ∈ Q.U, ∀ i, t < v i := by
      have := Q.rayPoint_pareto (w := fun _ => (1 : ℝ)) fun _ => one_pos
      simpa [rayPoint, hd, htdef] using this
    -- points attaining the ideal values
    obtain ⟨⟨E₀, hE₀, hdE₀, hE₀0⟩, hall₀⟩ := Q.ideal_spec 0
    obtain ⟨⟨E₁, hE₁, hdE₁, hE₁1⟩, hall₁⟩ := Q.ideal_spec 1
    rw [hid] at hE₀0 hE₁1 hall₀ hall₁
    have hE₀1 : 0 ≤ E₀ 1 := by simpa [hd] using hdE₀ 1
    have hE₁0 : 0 ≤ E₁ 0 := by simpa [hd] using hdE₁ 0
    have ht1 : t ≤ 1 := by
      have := hall₀ _ hkmem fun i => by simp [hd, ht0.le]
      simpa using this
    have hfQ : f Q ∈ Q.U := hf Q
    have hthalf : 1 / 2 ≤ t := by
      refine Q.le_rayLevel (fun _ => one_pos) ⟨by norm_num, Q.comprehensive _
        (Q.convex hE₀ hE₁ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num)) _ fun k => ?_⟩
      simp only [hd, Pi.zero_apply, zero_add, mul_one, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      fin_cases k
      · simp only [Fin.zero_eta, Fin.isValue, hE₀0]; linarith
      · simp only [Fin.mk_one, Fin.isValue, hE₁1]; linarith
    -- the final step: `f Q ≥ (t, t)` forces `f Q = (t, t)` when `t < 1`, by convexity
    have finish : (∀ i, t ≤ f Q i) → t < 1 → f Q = fun _ => t := by
      intro hge ht1'
      funext i
      by_contra hne
      have hgt : t < f Q i := lt_of_le_of_ne (hge i) (Ne.symm hne)
      set a := f Q i
      set lam := (a - t) / (2 * a) with hlam
      have ha : 0 < a := by linarith
      have hlam0 : 0 < lam := div_pos (by linarith) (by linarith)
      have hlam1 : lam ≤ 1 / 2 := by
        rw [hlam, div_le_iff₀ (by linarith)]; linarith
      -- combine `f Q` with the point attaining the other agent's ideal value
      have hcomb : ∀ E ∈ Q.U, (∀ k, 0 ≤ E k) → (∀ k, k ≠ i → E k = 1) →
          ∃ v ∈ Q.U, ∀ k, t < v k := by
        intro E hE hEnn hE1
        refine ⟨lam • E + (1 - lam) • f Q, Q.convex hE hfQ hlam0.le (by linarith) (by ring),
          fun k => ?_⟩
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        by_cases hk : k = i
        · subst hk
          have : lam * a ≤ (a - t) / 2 := by
            rw [hlam, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]; nlinarith
          nlinarith [hEnn k, mul_nonneg hlam0.le (hEnn k)]
        · rw [hE1 k hk]
          nlinarith [hge k, mul_le_mul_of_nonneg_left (hge k) (by linarith : (0 : ℝ) ≤ 1 - lam)]
      have hE : ∃ E ∈ Q.U, (∀ k, 0 ≤ E k) ∧ ∀ k, k ≠ i → E k = 1 := by
        fin_cases i
        · exact ⟨E₁, hE₁, fun k => by simpa [hd] using hdE₁ k, fun k hk => by
            fin_cases k
            · exact absurd rfl hk
            · exact hE₁1⟩
        · exact ⟨E₀, hE₀, fun k => by simpa [hd] using hdE₀ k, fun k hk => by
            fin_cases k
            · exact hE₀0
            · exact absurd rfl hk⟩
      obtain ⟨E, hE, hEnn, hE1⟩ := hE
      exact hkpar (hcomb E hE hEnn hE1)
    rw [hks]
    rcases ht1.lt_or_eq with ht1' | ht1'
    · -- the quadrilateral `T`
      set T := ksQuad t ht0 ht1'
      have hsub : T.U ⊆ Q.U := by
        intro u hu
        rw [mem_ksQuad] at hu
        obtain ⟨h1, h2, h3, h4⟩ := hu
        have h10 : (![1, 0] : Fin 2 → ℝ) ∈ Q.U :=
          Q.comprehensive _ hE₀ _ fun k => by fin_cases k <;> simp [hE₀0, hE₀1]
        have h01 : (![0, 1] : Fin 2 → ℝ) ∈ Q.U :=
          Q.comprehensive _ hE₁ _ fun k => by fin_cases k <;> simp [hE₁1, hE₁0]
        by_cases hu0 : t < u 0
        · set σ := (u 0 - t) / (1 - t)
          have hσ0 : 0 ≤ σ := div_nonneg (by linarith) (by linarith)
          have hσ1 : σ ≤ 1 := by rw [div_le_one (by linarith)]; linarith
          refine Q.comprehensive _ (Q.convex hkmem h10 (by linarith : 0 ≤ 1 - σ) hσ0
            (by ring)) _ fun k => ?_
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          have h1t : (1 - t) ≠ 0 := by linarith
          have e : σ * (1 - t) = u 0 - t := div_mul_cancel₀ _ h1t
          fin_cases k
          · simp; nlinarith
          · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one,
              mul_zero, add_zero, ge_iff_le]
            have : (1 - t) * u 1 ≤ t * (1 - u 0) := by linarith
            nlinarith
        by_cases hu1 : t < u 1
        · set σ := (u 1 - t) / (1 - t)
          have hσ0 : 0 ≤ σ := div_nonneg (by linarith) (by linarith)
          have hσ1 : σ ≤ 1 := by rw [div_le_one (by linarith)]; linarith
          refine Q.comprehensive _ (Q.convex hkmem h01 (by linarith : 0 ≤ 1 - σ) hσ0
            (by ring)) _ fun k => ?_
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          have h1t : (1 - t) ≠ 0 := by linarith
          have e : σ * (1 - t) = u 1 - t := div_mul_cancel₀ _ h1t
          fin_cases k
          · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, mul_zero, add_zero,
              ge_iff_le]
            have : (1 - t) * u 0 ≤ t * (1 - u 1) := by linarith
            nlinarith
          · simp; nlinarith
        · exact Q.comprehensive _ hkmem _ fun k => by
            fin_cases k
            · exact not_lt.1 hu0
            · exact not_lt.1 hu1
      have hTsym : IsSymmetricSet T.U := by
        intro σ u hu
        rw [mem_ksQuad] at hu ⊢
        have hne : σ 0 ≠ σ 1 := σ.injective.ne (by decide)
        simp only [Function.comp]
        rcases fin2_cases (σ 0) with h0 | h0 <;> rcases fin2_cases (σ 1) with h1 | h1
        · exact absurd (h0.trans h1.symm) hne
        · rw [h0, h1]; exact hu
        · rw [h0, h1]
          exact ⟨by linarith [hu.2.1], by linarith [hu.1], hu.2.2.2, hu.2.2.1⟩
        · exact absurd (h0.trans h1.symm) hne
      have hfT : f T = fun _ => t := by
        have heq := hS T hTsym (fun _ _ => rfl)
        have hin := (mem_ksQuad _).1 (hf T)
        have hle : f T 0 ≤ t := by
          have := hin.1
          rw [heq 1 0, show t * f T 0 + (1 - t) * f T 0 = f T 0 by ring] at this
          exact this
        have hge : t ≤ f T 0 := by
          by_contra hlt
          exact hP T ⟨fun _ => t, by rw [mem_ksQuad]; refine ⟨by linarith, by linarith,
            ht1'.le, ht1'.le⟩, fun k => by rw [heq k 0]; exact not_le.1 hlt⟩
        funext k; rw [heq k 0]; linarith
      have hTd0 : T.d = 0 := ksQuad_d
      have hTid : ∀ k, T.ideal k = 1 := by
        intro k
        fin_cases k
        · exact T.ideal_eq 0 ⟨![1, 0], by rw [mem_ksQuad]; norm_num; linarith,
            fun k => by rw [hTd0]; fin_cases k <;> simp, rfl⟩
            fun u hu _ => ((mem_ksQuad u).1 hu).2.2.1
        · exact T.ideal_eq 1 ⟨![0, 1], by rw [mem_ksQuad]; norm_num; linarith,
            fun k => by rw [hTd0]; fin_cases k <;> simp, rfl⟩
            fun u hu _ => ((mem_ksQuad u).1 hu).2.2.2
      have hTd : T.d = Q.d := by rw [hd]; rfl
      have h1 := hM T Q hsub hTd 0 (by rw [hTid, hid]) 1 (by decide)
      have h0 := hM T Q hsub hTd 1 (by rw [hTid, hid]) 0 (by decide)
      rw [hfT] at h0 h1
      exact finish (fun k => by fin_cases k <;> assumption) ht1'
    · -- `t = 1`: the box `{u ≤ (1, 1)}`
      rw [ht1'] at hkmem ⊢
      set T := boxProblem (fun _ : Fin 2 => (1 : ℝ)) fun _ => one_pos
      have hsub : T.U ⊆ Q.U := fun u hu => Q.comprehensive _ hkmem _ hu
      have hTid : ∀ k, T.ideal k = 1 := fun k => T.ideal_eq k
        ⟨fun _ => 1, show (fun _ => (1 : ℝ)) ≤ fun _ => 1 from le_rfl, fun _ => by
          simp [T, boxProblem], rfl⟩ fun u hu _ => hu k
      have hfT := sym_box hf hP hS (ι := Fin 2) one_pos
      have hTd : T.d = Q.d := by rw [hd]; rfl
      have h1 := hM T Q hsub hTd 0 (by rw [hTid, hid]) 1 (by decide)
      have h0 := hM T Q hsub hTd 1 (by rw [hTid, hid]) 0 (by decide)
      rw [hfT] at h0 h1
      funext k
      have hnn : Q.d ≤ f Q := fun i => by
        rw [hd]; fin_cases i
        · simp; linarith
        · simp; linarith
      apply le_antisymm
      · fin_cases k
        · exact hall₀ _ hfQ hnn
        · exact hall₁ _ hfQ hnn
      · fin_cases k
        · exact h0
        · exact h1
  -- Step B: normalize by translation and rescaling
  funext P
  set N := P.normalize
  have hNd : N.d = 0 := P.normalize_d
  have hg := N.idealGap_pos
  set β : Fin 2 → ℝ := fun i => (N.idealGap i)⁻¹
  have hβ : ∀ i, 0 < β i := fun i => inv_pos.2 (hg i)
  set Q := N.scale β hβ
  have hQd : Q.d = 0 := by funext i; simp [Q, scale_d, hNd]
  have hQid : ∀ i, Q.ideal i = 1 := fun i => by
    rw [ideal_scale]
    have : N.ideal i = N.idealGap i := by simp [idealGap, hNd]
    rw [this]; exact inv_mul_cancel₀ (hg i).ne'
  have hfQ := keyA Q hQd hQid
  rw [hIUU N β hβ, ks_IUU N β hβ] at hfQ
  have hfN : f N = ks N := by
    funext i
    have := congrFun hfQ i
    exact mul_left_cancel₀ (hβ i).ne' this
  rw [normalize_eq hIUO P, normalize_eq ks_IUO P, hfN]

/-- **Exercise 22.E.6**, the hypotheses hold (MWG, p. 854): the Kalai-Smorodinsky solution is a
bargaining solution satisfying IUO, IUU, P, S and partial monotonicity. -/
theorem exercise_22_E_6_instance :
    IsBargainingSolution (ks (ι := Fin 2)) ∧ IUO (ks (ι := Fin 2)) ∧ IUU (ks (ι := Fin 2)) ∧
      ParetoBS (ks (ι := Fin 2)) ∧ SymmetricBS (ks (ι := Fin 2)) ∧ PartiallyMonotoneBS ks :=
  ⟨example_22_E_4.1, example_22_E_4.2.1, example_22_E_4.2.2.1, example_22_E_4.2.2.2.1,
    example_22_E_4.2.2.2.2.1, ks_partiallyMonotone⟩

end MWG.WelfareBargaining
