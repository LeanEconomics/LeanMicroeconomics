/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGWelfareBargaining.Characterizations
import Mathlib.Topology.Algebra.Group.Pointwise

/-!
# Strong monotonicity and monotone-path solutions

MWG, Exercise 22.E.5(b) (p. 854), two agents.

A bargaining solution is *strongly monotonic* (`StrongMonotoneBS`) if it is monotone and, when
`U ⊆ U'` (same threat point) and `f(U)` is interior to `U'`, `f(U) ≪ f(U')`. The exercise
claims that an independent-of-origins, Paretian, strongly monotonic solution selects, on every
problem, the intersection of its boundary with a strictly increasing curve starting at the
origin. With the curve `C = {f(U) : u* = 0}` (`solutionCurve`):

* `exercise_22_E_5b_needs_IR`: as stated the claim is false. Shifting the threat point of the
  egalitarian solution to `(-1, 0)` gives an IUO, Paretian, strongly monotonic solution whose
  values on normalized problems lie on the line `u₂ = u₁ + 1`: no value is within `1/2` of the
  origin, and the box `{u ≤ (1/2, 1/2)}` gets a negative first coordinate.
* `exercise_22_E_5b`: with individual rationality (Definition 22.E.6) added, `C ⊆ ℝ²₊₊`, any two
  points of `C` are equal or strictly ordered (`≪`), `C` has points arbitrarily close to the
  origin, on every normalized problem `f(U)` is the unique point of `C` on the (weak Pareto)
  boundary of `U`, and in general `f(U) - u* ∈ C` (by IUO). `exercise_22_E_5b_instance`: the
  egalitarian solution satisfies all hypotheses.

Proof. The key step is `mp_box_fixed`: if `x = f(S) ≫ 0` then `f({u ≤ x}) = x`. Otherwise
`k = f({u ≤ x})` lies on a face of the box, say `kᵢ = xᵢ`, `kⱼ < xⱼ`. Strong monotonicity
forbids points of `S` strictly above `k`, so `S` is flat at height `xᵢ` beyond `kⱼ`. For
`ρ ∈ (kⱼ, xⱼ)` and `s > 0` the box `D = {u ≤ c}`, `cᵢ = xᵢ + s`, `cⱼ = ρ`, lies in
`S + [0, 1]v` (`addSeg`, `v` pointing left-up from the far end of the flat), whose value is
`≥ x`, but which has no point `≥ (xᵢ + s, xⱼ)`; so `f(D)` is on the right face `uⱼ = ρ`, with
`f(D)ᵢ > xᵢ` by strong monotonicity. Two such boxes, `ρ < ρ'` with the second lower than
`f(D)ᵢ`, have values that no point of the convex comprehensive hull of the two boxes dominates
jointly: a contradiction. Given `mp_box_fixed`, incomparable values `x, y` contradict
monotonicity on the hull of `{u ≤ x}` and `{u ≤ y}` (`mp_incomparable`), and `x ≤ y` with a
common coordinate contradicts strong monotonicity on the hull of `{u ≤ x + eᵢ}` and `{u ≤ y}`
(`mp_strict`). Individual rationality and strong monotonicity give `f(U) ≫ 0` (`mp_pos`).
-/

namespace MWG.WelfareBargaining

open BargainingProblem

variable {ι : Type*} [Fintype ι]

/-- **Exercise 22.E.5(b)** (MWG, p. 854). Strong monotonicity: monotone, and if `U ⊆ U'` (same
threat point) and `f(U)` is interior to `U'`, then `f(U) ≪ f(U')`. -/
def StrongMonotoneBS (f : BargainingProblem ι → ι → ℝ) : Prop :=
  MonotoneBS f ∧ ∀ P P' : BargainingProblem ι, P.U ⊆ P'.U → P.d = P'.d → f P ∈ interior P'.U →
    ∀ i, f P i < f P' i

/-- **Exercise 22.E.5(b)** (MWG, p. 854). The curve of solution values on normalized problems
(`u* = 0`). -/
def solutionCurve (f : BargainingProblem ι → ι → ℝ) : Set (ι → ℝ) :=
  {c | ∃ P : BargainingProblem ι, P.d = 0 ∧ f P = c}

namespace BargainingProblem

omit [Fintype ι] in
/-- A point strictly below a point of `U` is interior to `U`. -/
theorem mem_interior_of_lt [Finite ι] (P : BargainingProblem ι) {u v : ι → ℝ} (hu : u ∈ P.U)
    (h : ∀ i, v i < u i) : v ∈ interior P.U := by
  have hopen : IsOpen {x : ι → ℝ | ∀ i, x i < u i} := by
    simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_lt (continuous_apply i) continuous_const
  exact mem_interior.2 ⟨_, fun x hx => P.comprehensive _ hu _ fun i => (hx i).le, hopen, h⟩

omit [Fintype ι] in
/-- A point below an interior point of `U` is interior to `U`. -/
theorem mem_interior_of_le (P : BargainingProblem ι) {u v : ι → ℝ} (hu : u ∈ interior P.U)
    (h : v ≤ u) : v ∈ interior P.U := by
  have hopen : IsOpen ((fun x => x + (u - v)) ⁻¹' interior P.U) :=
    isOpen_interior.preimage (continuous_id.add continuous_const)
  refine mem_interior.2 ⟨(fun x => x + (u - v)) ⁻¹' interior P.U,
    fun x hx => P.comprehensive _ (interior_subset hx) _ fun i => ?_, hopen, ?_⟩
  · simp only [Pi.add_apply, Pi.sub_apply]
    linarith [h i]
  · change v + (u - v) ∈ interior P.U
    rwa [add_sub_cancel]

omit [Fintype ι] in
/-- The points of `U` with `u ≥ u* - c𝟙` are bounded above. -/
theorem bdd_sub [Finite ι] [Nonempty ι] (P : BargainingProblem ι) {c : ℝ} (hc : 0 ≤ c) :
    ∃ B, ∀ u ∈ P.U, (∀ i, P.d i - c ≤ u i) → ∀ i, u i ≤ B := by
  cases nonempty_fintype ι
  obtain ⟨ε, hε, hp⟩ := P.exists_gt
  obtain ⟨B, hB⟩ := P.bdd
  set l := ε / (ε + c) with hl
  have hl0 : 0 < l := by positivity
  have hl1 : l ≤ 1 := by rw [hl, div_le_one (by positivity)]; linarith
  have hlc : l * (ε + c) = ε := by rw [hl]; field_simp
  refine ⟨(|B| + ∑ j, |P.d j| + ε) / l, fun u hu hge i => ?_⟩
  have hz := P.convex hu hp hl0.le (by linarith : 0 ≤ 1 - l) (by ring)
  have hzge : P.d ≤ l • u + (1 - l) • (fun j => P.d j + ε) := fun j => by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [mul_le_mul_of_nonneg_left (hge j) hl0.le]
  have h1 := hB _ hz hzge i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1
  have h2 : |P.d i| ≤ ∑ j, |P.d j| := Finset.single_le_sum (f := fun j => |P.d j|)
    (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  have h3 : 0 ≤ 1 - l := by linarith
  rw [le_div_iff₀ hl0]
  nlinarith [le_abs_self B, mul_le_mul_of_nonneg_left (neg_abs_le (P.d i)) h3,
    mul_nonneg hl0.le (abs_nonneg (P.d i)), mul_nonneg h3 hε.le]

open Pointwise in
/-- The problem `U + [0, 1]v`, same threat point: `U` together with its translates by `tv`,
`0 ≤ t ≤ 1`. -/
def addSeg [Nonempty ι] (P : BargainingProblem ι) (v : ι → ℝ) : BargainingProblem ι where
  U := {u | ∃ t ∈ Set.Icc (0 : ℝ) 1, u - t • v ∈ P.U}
  d := P.d
  convex := by
    rintro x ⟨t, ht, hx⟩ y ⟨t', ht', hy⟩ a b ha hb hab
    refine ⟨a * t + b * t', ⟨by nlinarith [ht.1, ht'.1], by nlinarith [ht.2, ht'.2]⟩, ?_⟩
    have := P.convex hx hy ha hb hab
    convert this using 1
    funext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  closed := by
    have hK : IsCompact ((fun t : ℝ => t • v) '' Set.Icc (0 : ℝ) 1) :=
      isCompact_Icc.image (continuous_id.smul continuous_const)
    have heq : {u | ∃ t ∈ Set.Icc (0 : ℝ) 1, u - t • v ∈ P.U} =
        (fun t : ℝ => t • v) '' Set.Icc (0 : ℝ) 1 + P.U := by
      ext u
      simp only [Set.mem_ofPred_eq, Set.mem_add, Set.mem_image]
      constructor
      · rintro ⟨t, ht, hu⟩
        exact ⟨t • v, ⟨t, ht, rfl⟩, u - t • v, hu, by abel⟩
      · rintro ⟨_, ⟨t, ht, rfl⟩, w, hw, rfl⟩
        exact ⟨t, ht, by rwa [add_sub_cancel_left]⟩
    rw [heq]
    exact P.closed.add_left_of_isCompact hK
  comprehensive := by
    rintro u ⟨t, ht, hu⟩ w hw
    exact ⟨t, ht, P.comprehensive _ hu _ fun i => by
      simp only [Pi.sub_apply]; linarith [hw i]⟩
  interior_d := interior_mono (fun u (hu : u ∈ P.U) =>
    (⟨0, Set.left_mem_Icc.2 zero_le_one, by simpa using hu⟩ :
      ∃ t ∈ Set.Icc (0 : ℝ) 1, u - t • v ∈ P.U)) P.interior_d
  bdd := by
    obtain ⟨B, hB⟩ := P.bdd_sub (c := ∑ j, |v j|) (Finset.sum_nonneg fun j _ => abs_nonneg _)
    refine ⟨B + ∑ j, |v j|, fun u hu' hdu i => ?_⟩
    obtain ⟨t, ht, hu⟩ := hu'
    have key : ∀ j, |t * v j| ≤ ∑ k, |v k| := fun j => by
      rw [abs_mul, abs_of_nonneg ht.1]
      have : |v j| ≤ ∑ k, |v k| := Finset.single_le_sum (f := fun k => |v k|)
        (fun k _ => abs_nonneg _) (Finset.mem_univ j)
      nlinarith [ht.2, abs_nonneg (v j)]
    have := hB _ hu (fun j => by
      have h1 := hdu j
      have h2 := key j
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      linarith [le_abs_self (t * v j)]) i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this
    linarith [le_abs_self (t * v i), key i]

/-- The threat point lowered to `u* + e` (`-1 ≤ e ≤ 0`), same utility possibility set. -/
def shiftThreat [Nonempty ι] (P : BargainingProblem ι) (e : ι → ℝ) (he0 : ∀ i, e i ≤ 0)
    (he1 : ∀ i, -1 ≤ e i) : BargainingProblem ι where
  U := P.U
  d := P.d + e
  convex := P.convex
  closed := P.closed
  comprehensive := P.comprehensive
  interior_d := P.mem_interior_of_le P.interior_d fun i => by
    simp only [Pi.add_apply]; linarith [he0 i]
  bdd := by
    obtain ⟨B, hB⟩ := P.bdd_sub zero_le_one
    exact ⟨B, fun u hu hdu i => hB u hu (fun j => by
      have h1 := hdu j
      have h2 := he1 j
      simp only [Pi.add_apply] at h1
      linarith) i⟩

theorem shiftThreat_d [Nonempty ι] (P : BargainingProblem ι) (e : ι → ℝ) (he0 : ∀ i, e i ≤ 0)
    (he1 : ∀ i, -1 ≤ e i) : (P.shiftThreat e he0 he1).d = P.d + e := rfl

end BargainingProblem

omit [Fintype ι] in
/-- The egalitarian solution is strongly monotonic. -/
theorem egal_strongMonotone [Finite ι] [Nonempty ι] : StrongMonotoneBS (egal (ι := ι)) := by
  cases nonempty_fintype ι
  refine ⟨egal_monotoneBS, fun P P' hsub hd hint i => ?_⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hint)
  have hmem : (fun l => egal P l + δ / 2) ∈ P'.U := hball (by
    rw [Metric.mem_ball, dist_pi_lt_iff hδ]
    intro l
    rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos (by positivity)]
    linarith)
  have hlev : P.rayLevel (fun _ => 1) + δ / 2 ∈ P'.raySet (fun _ => 1) := by
    refine ⟨by linarith [P.rayLevel_pos (w := fun _ => 1) fun _ => one_pos], ?_⟩
    convert hmem using 1
    funext l
    simp only [egal, rayPoint, hd, mul_one]
    ring
  have := P'.le_rayLevel (fun _ => one_pos) hlev
  simp only [egal, rayPoint, hd, mul_one]
  linarith

theorem mp_fin2_split {i j : Fin 2} (hij : i ≠ j) (l : Fin 2) : l = i ∨ l = j := by
  fin_cases i <;> fin_cases j <;> fin_cases l <;> simp_all

/-- **Exercise 22.E.5(b)**, key step (MWG, p. 854), the contradiction: the value `k` of the box
`{u ≤ x}`, `x = f(S)`, cannot lie on a face of the box with `kᵢ = xᵢ`, `kⱼ < xⱼ`. -/
theorem mp_box_fixed_aux {f : BargainingProblem (Fin 2) → Fin 2 → ℝ}
    (hf : IsBargainingSolution f) (hP : ParetoBS f) (hSM : StrongMonotoneBS f)
    (S : BargainingProblem (Fin 2)) (hS : S.d = 0) (hx : ∀ l, 0 < f S l) {i j : Fin 2}
    (hij : i ≠ j) (hki : f (boxProblem (f S) hx) i = f S i)
    (hkj : f (boxProblem (f S) hx) j < f S j) : False := by
  have hsp := mp_fin2_split hij
  have hji : j ≠ i := hij.symm
  have hxS : f S ∈ S.U := hf S
  set x := f S with hxdef
  set k := f (boxProblem x hx) with hkdef
  have hboxS : (boxProblem x hx).U ⊆ S.U := fun u hu => S.comprehensive _ hxS _ hu
  -- no point of `S` lies strictly above `k`
  have hflat : ∀ w ∈ S.U, k j < w j → w i ≤ x i := by
    intro w hw hwj
    by_contra hwi
    push Not at hwi
    have hint : k ∈ interior S.U := S.mem_interior_of_lt hw fun l => by
      rcases hsp l with h | h
      · rw [h, hki]; exact hwi
      · rw [h]; exact hwj
    have h' : k i < x i := hSM.2 _ S hboxS (by rw [hS]; rfl) hint i
    rw [hki] at h'
    exact lt_irrefl _ h'
  -- the far end `R` of the flat of `S` at height `xᵢ`
  set pt : ℝ → Fin 2 → ℝ := fun a l => if l = i then x i else a with hpt
  have hpti : ∀ a, pt a i = x i := fun a => by simp [hpt]
  have hptj : ∀ a, pt a j = a := fun a => by simp [hpt, hji]
  set A : Set ℝ := {a | pt a ∈ S.U} with hA
  have hxA : x j ∈ A := by
    change pt (x j) ∈ S.U
    convert hxS using 1
    funext l
    rcases hsp l with h | h
    · rw [h, hpti]
    · rw [h, hptj]
  obtain ⟨Bd, hBd⟩ := S.bdd
  have hAb : BddAbove A := ⟨max Bd 0, fun a ha => by
    rcases le_or_gt a 0 with ha0 | ha0
    · exact ha0.trans (le_max_right _ _)
    · have := hBd _ ha (fun l => by
        rw [hS, Pi.zero_apply]
        rcases hsp l with h | h
        · rw [h, hpti]; exact (hx i).le
        · rw [h, hptj]; exact ha0.le) j
      rw [hptj] at this
      exact this.trans (le_max_left _ _)⟩
  set R := sSup A with hR
  have hxR : x j ≤ R := le_csSup hAb hxA
  have hAR : ∀ a ∈ A, a ≤ R := fun a ha => le_csSup hAb ha
  -- the boxes `{u ≤ c ρ s}` with `cᵢ = xᵢ + s`, `cⱼ = ρ`
  set c : ℝ → ℝ → Fin 2 → ℝ := fun ρ s l => if l = i then x i + s else ρ with hc
  have hci : ∀ ρ s, c ρ s i = x i + s := fun ρ s => by simp [hc]
  have hcj : ∀ ρ s, c ρ s j = ρ := fun ρ s => by simp [hc, hji]
  have hcpos : ∀ ρ s, 0 < ρ → 0 ≤ s → ∀ l, 0 < c ρ s l := fun ρ s hρ hs l => by
    rcases hsp l with h | h
    · rw [h, hci]; linarith [hx i]
    · rw [h, hcj]; exact hρ
  -- the value of such a box lies on its right face, strictly above height `xᵢ`
  have claimB : ∀ ρ s (hρ0 : 0 < ρ) (hs : 0 < s), k j < ρ → ρ < x j →
      f (boxProblem (c ρ s) (hcpos ρ s hρ0 hs.le)) j = ρ ∧
      x i < f (boxProblem (c ρ s) (hcpos ρ s hρ0 hs.le)) i ∧
      f (boxProblem (c ρ s) (hcpos ρ s hρ0 hs.le)) i < x i + s := by
    intro ρ s hρ0 hs hkρ hρx
    set D := boxProblem (c ρ s) (hcpos ρ s hρ0 hs.le) with hD
    obtain ⟨a₀, ha₀A, ha₀⟩ := exists_lt_of_lt_csSup ⟨x j, hxA⟩
      (show R - (x j - ρ) < R by linarith)
    have ha₀ρ : ρ < a₀ := by linarith
    set v : Fin 2 → ℝ := fun l => if l = i then s else ρ - a₀ with hv
    have hvi : v i = s := by simp [hv]
    have hvj : v j = ρ - a₀ := by simp [hv, hji]
    set Bg := S.addSeg v with hBg
    have hSB : S.U ⊆ Bg.U := fun u hu =>
      ⟨0, Set.left_mem_Icc.2 zero_le_one, by rwa [zero_smul, sub_zero]⟩
    have hDB : D.U ⊆ Bg.U := fun u hu => ⟨1, Set.right_mem_Icc.2 zero_le_one,
      S.comprehensive _ ha₀A _ fun l => by
        have hul : u l ≤ c ρ s l := hu l
        rcases hsp l with h | h
        · rw [h] at hul ⊢
          rw [hci] at hul
          rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hvi, hpti]
          linarith
        · rw [h] at hul ⊢
          rw [hcj] at hul
          rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hvj, hptj]
          linarith⟩
    have hxB : x ≤ f Bg := hSM.1 S Bg hSB rfl
    have hDBf : f D ≤ f Bg := hSM.1 D Bg hDB (by rw [hBg]; exact hS.symm)
    have hDi : f D i < x i + s := by
      by_contra hge
      push Not at hge
      obtain ⟨t, ht, hw⟩ := hf Bg
      set w := f Bg - t • v with hw'
      have hwi : w i = f Bg i - t * s := by rw [hw', Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hvi]
      have hwj : w j = f Bg j - t * (ρ - a₀) := by
        rw [hw', Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hvj]
      have h1 : x i + s ≤ f Bg i := by
        have := hDBf i
        linarith
      have h2 : x j ≤ f Bg j := hxB j
      have hwj' : k j < w j := by
        rw [hwj]
        nlinarith [mul_nonneg ht.1 (sub_nonneg.2 ha₀ρ.le)]
      have hwi' := hflat w hw hwj'
      have ht1 : 1 ≤ t := by
        by_contra hlt
        push Not at hlt
        rw [hwi] at hwi'
        nlinarith [mul_pos hs (sub_pos.2 hlt)]
      have ht1' : t = 1 := le_antisymm ht.2 ht1
      have hwix : w i = x i := le_antisymm hwi' (by rw [hwi, ht1']; linarith)
      have hwA : w j ∈ A := by
        change pt (w j) ∈ S.U
        convert hw using 1
        funext l
        rcases hsp l with h | h
        · rw [h, hpti, hwix]
        · rw [h, hptj]
      have := hAR _ hwA
      rw [hwj, ht1'] at this
      linarith
    have hfD : f D ∈ D.U := hf D
    have hDj : f D j = ρ := by
      by_contra hne
      have hlt : f D j < ρ := lt_of_le_of_ne (by have := hfD j; rwa [hcj] at this) hne
      exact hP D ⟨c ρ s, show c ρ s ≤ c ρ s from le_rfl, fun l => by
        rcases hsp l with h | h
        · rw [h, hci]; exact hDi
        · rw [h, hcj]; exact hlt⟩
    -- strict monotonicity from the box `{u ≤ c ρ 0}`
    set M := boxProblem (c ρ 0) (hcpos ρ 0 hρ0 le_rfl) with hM
    have hMK : M.U ⊆ (boxProblem x hx).U := fun u hu l => by
      have hul : u l ≤ c ρ 0 l := hu l
      rcases hsp l with h | h
      · rw [h] at hul ⊢; rw [hci, add_zero] at hul; exact hul
      · rw [h] at hul ⊢; rw [hcj] at hul; linarith
    have hMk : f M ≤ k := hSM.1 M _ hMK rfl
    have hMj : f M j < ρ := lt_of_le_of_lt (hMk j) hkρ
    have hfM : f M ∈ M.U := hf M
    have hMi : f M i = x i := by
      apply le_antisymm (by have := hfM i; rwa [hci, add_zero] at this)
      by_contra hlt
      push Not at hlt
      exact hP M ⟨c ρ 0, show c ρ 0 ≤ c ρ 0 from le_rfl, fun l => by
        rcases hsp l with h | h
        · rw [h, hci, add_zero]; exact hlt
        · rw [h, hcj]; exact hMj⟩
    have hMD : M.U ⊆ D.U := fun u hu l => by
      have hul : u l ≤ c ρ 0 l := hu l
      rcases hsp l with h | h
      · rw [h] at hul ⊢; rw [hci] at hul ⊢; linarith
      · rw [h] at hul ⊢; rw [hcj] at hul ⊢; exact hul
    have hint : f M ∈ interior D.U := D.mem_interior_of_lt (show c ρ s ≤ c ρ s from le_rfl)
      fun l => by
        rcases hsp l with h | h
        · rw [h, hMi, hci]; linarith
        · rw [h, hcj]; exact hMj
    have := hSM.2 M D hMD rfl hint i
    rw [hMi] at this
    exact ⟨hDj, this, hDi⟩
  -- two such boxes contradict monotonicity on their comprehensive convex hull
  set lo := max (k j) 0 with hlo
  have hlox : lo < x j := max_lt hkj (hx j)
  have hlo0 : 0 ≤ lo := le_max_right _ _
  have hklo : k j ≤ lo := le_max_left _ _
  set r := lo + (x j - lo) / 3 with hr
  set r' := lo + 2 * (x j - lo) / 3 with hr'
  have hr0 : 0 < r := by rw [hr]; linarith
  have hr'0 : 0 < r' := by rw [hr']; linarith
  have hkr : k j < r := by rw [hr]; linarith
  have hkr' : k j < r' := by rw [hr']; linarith
  have hrx : r < x j := by rw [hr]; linarith
  have hr'x : r' < x j := by rw [hr']; linarith
  have hrr' : r < r' := by rw [hr, hr']; linarith
  obtain ⟨-, hD1i, -⟩ := claimB r 1 hr0 one_pos hkr hrx
  set D1 := boxProblem (c r 1) (hcpos r 1 hr0 zero_le_one) with hD1
  set y := f D1 i with hy
  set s' := (y - x i) / 2 with hs'
  have hs'0 : 0 < s' := by rw [hs']; linarith
  obtain ⟨hD2j, -, hD2i⟩ := claimB r' s' hr'0 hs'0 hkr' hr'x
  set D2 := boxProblem (c r' s') (hcpos r' s' hr'0 hs'0.le) with hD2
  set T := D2.addSeg (c r 1 - c r' s') with hT
  have h1 : D1.U ⊆ T.U := fun u hu => ⟨1, Set.right_mem_Icc.2 zero_le_one, fun l => by
    have hul : u l ≤ c r 1 l := hu l
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, one_mul]
    linarith⟩
  have h2 : D2.U ⊆ T.U := fun u hu =>
    ⟨0, Set.left_mem_Icc.2 zero_le_one, by rwa [zero_smul, sub_zero]⟩
  have hT1 : f D1 ≤ f T := hSM.1 D1 T h1 rfl
  have hT2 : f D2 ≤ f T := hSM.1 D2 T h2 rfl
  obtain ⟨t, ht, hTm⟩ := hf T
  have hTj : (f T - t • (c r 1 - c r' s')) j ≤ c r' s' j := hTm j
  have hTi : (f T - t • (c r 1 - c r' s')) i ≤ c r' s' i := hTm i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hcj, hci] at hTj hTi
  have h3 := hT2 j
  rw [hD2j] at h3
  have ht0 : t = 0 := by
    refine le_antisymm ?_ ht.1
    by_contra hpos
    push Not at hpos
    nlinarith [mul_pos hpos (sub_pos.2 hrr')]
  rw [ht0, zero_mul, sub_zero] at hTi
  have h4 := hT1 i
  rw [hs'] at hTi hD2i
  linarith

/-- **Exercise 22.E.5(b)**, key step (MWG, p. 854). For an IUO-free, Paretian, strongly
monotonic solution, if `x = f(S) ≫ 0` (`S` normalized) then the box `{u ≤ x}` also has value
`x`. -/
theorem mp_box_fixed {f : BargainingProblem (Fin 2) → Fin 2 → ℝ}
    (hf : IsBargainingSolution f) (hP : ParetoBS f) (hSM : StrongMonotoneBS f)
    (S : BargainingProblem (Fin 2)) (hS : S.d = 0) (hx : ∀ l, 0 < f S l) :
    f (boxProblem (f S) hx) = f S := by
  have hle : f (boxProblem (f S) hx) ≤ f S := hf (boxProblem (f S) hx)
  obtain ⟨i, hi⟩ : ∃ i, f (boxProblem (f S) hx) i = f S i := by
    by_contra h
    push Not at h
    exact hP (boxProblem (f S) hx) ⟨f S, show f S ≤ f S from le_rfl,
      fun l => lt_of_le_of_ne (hle l) (h l)⟩
  by_contra hne
  obtain ⟨j, hj⟩ : ∃ j, f (boxProblem (f S) hx) j ≠ f S j := by
    by_contra h
    push Not at h
    exact hne (funext h)
  have hij : i ≠ j := fun h => hj (h ▸ hi)
  exact mp_box_fixed_aux hf hP hSM S hS hx hij hi (lt_of_le_of_ne (hle j) hj)

/-- Two box-fixed values cannot be incomparable: the comprehensive convex hull of the two boxes
has no point above both. -/
theorem mp_incomparable {f : BargainingProblem (Fin 2) → Fin 2 → ℝ}
    (hf : IsBargainingSolution f) (hM : MonotoneBS f) {x y : Fin 2 → ℝ} (hx : ∀ l, 0 < x l)
    (hy : ∀ l, 0 < y l) (hfx : f (boxProblem x hx) = x) (hfy : f (boxProblem y hy) = y)
    {i j : Fin 2} (hi : y i < x i) (hj : x j < y j) : False := by
  set T := (boxProblem y hy).addSeg (x - y) with hT
  have h1 : (boxProblem x hx).U ⊆ T.U := fun u hu => ⟨1, Set.right_mem_Icc.2 zero_le_one,
    fun l => by
      have hul : u l ≤ x l := hu l
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, one_mul]
      linarith⟩
  have h2 : (boxProblem y hy).U ⊆ T.U := fun u hu =>
    ⟨0, Set.left_mem_Icc.2 zero_le_one, by rwa [zero_smul, sub_zero]⟩
  have hxT := hM _ T h1 rfl
  have hyT := hM _ T h2 rfl
  rw [hfx] at hxT
  rw [hfy] at hyT
  obtain ⟨t, ht, hTm⟩ := hf T
  have hTj : (f T - t • (x - y)) j ≤ y j := hTm j
  have hTi : (f T - t • (x - y)) i ≤ y i := hTm i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hTj hTi
  have h3 := hyT j
  have h4 := hxT i
  have ht0 : t = 0 := by
    refine le_antisymm ?_ ht.1
    by_contra hpos
    push Not at hpos
    nlinarith [mul_pos hpos (sub_pos.2 hj)]
  rw [ht0, zero_mul, sub_zero] at hTi
  linarith

/-- Two box-fixed values `x ≤ y` with a common coordinate must be equal: otherwise `x` is
interior to the hull of `{u ≤ x + eᵢ}` and `{u ≤ y}`, whose value is then `≫ x` and `≥ y`. -/
theorem mp_strict {f : BargainingProblem (Fin 2) → Fin 2 → ℝ}
    (hf : IsBargainingSolution f) (hSM : StrongMonotoneBS f) {x y : Fin 2 → ℝ}
    (hx : ∀ l, 0 < x l) (hy : ∀ l, 0 < y l) (hfx : f (boxProblem x hx) = x)
    (hfy : f (boxProblem y hy) = y) {i j : Fin 2} (hij : i ≠ j) (hi : x i = y i)
    (hj : x j < y j) : False := by
  have hsp := mp_fin2_split hij
  have hji : j ≠ i := hij.symm
  set e : Fin 2 → ℝ := fun l => if l = i then 1 else 0 with he
  have hei : e i = 1 := by simp [he]
  have hej : e j = 0 := by simp [he, hji]
  set T := (boxProblem y hy).addSeg (x + e - y) with hT
  set z : Fin 2 → ℝ := fun l => (x l + y l + e l) / 2 with hz
  have hzT : z ∈ T.U := ⟨1 / 2, ⟨by norm_num, by norm_num⟩, fun l => by
    simp only [hz, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linarith⟩
  have hxz : ∀ l, x l < z l := fun l => by
    rcases hsp l with h | h
    · rw [h]; simp only [hz]; rw [hei]; linarith
    · rw [h]; simp only [hz]; rw [hej]; linarith
  have hint : x ∈ interior T.U := T.mem_interior_of_lt hzT hxz
  have h1 : (boxProblem x hx).U ⊆ T.U := fun u hu =>
    T.comprehensive _ hzT _ fun l => ((hu l).trans (hxz l).le)
  have h2 : (boxProblem y hy).U ⊆ T.U := fun u hu =>
    ⟨0, Set.left_mem_Icc.2 zero_le_one, by rwa [zero_smul, sub_zero]⟩
  have hxT := hSM.2 _ T h1 rfl (by rw [hfx]; exact hint)
  have hyT := hSM.1 _ T h2 rfl
  rw [hfx] at hxT
  rw [hfy] at hyT
  obtain ⟨t, ht, hTm⟩ := hf T
  have hTj : (f T - t • (x + e - y)) j ≤ y j := hTm j
  have hTi : (f T - t • (x + e - y)) i ≤ y i := hTm i
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hTj hTi
  rw [hej] at hTj
  have h3 := hyT j
  have h4 := hxT i
  have ht0 : t = 0 := by
    refine le_antisymm ?_ ht.1
    by_contra hpos
    push Not at hpos
    nlinarith [mul_pos hpos (sub_pos.2 hj)]
  rw [ht0, zero_mul, sub_zero] at hTi
  linarith

/-- **Exercise 22.E.5(b)**, the chain property (MWG, p. 854). Two strictly positive values of a
Paretian, strongly monotonic solution on normalized problems are equal or strictly ordered. -/
theorem exercise_22_E_5b_chain {f : BargainingProblem (Fin 2) → Fin 2 → ℝ}
    (hf : IsBargainingSolution f) (hP : ParetoBS f) (hSM : StrongMonotoneBS f)
    {P Q : BargainingProblem (Fin 2)} (hPd : P.d = 0) (hQd : Q.d = 0) (hxP : ∀ l, 0 < f P l)
    (hxQ : ∀ l, 0 < f Q l) : f P = f Q ∨ (∀ l, f P l < f Q l) ∨ ∀ l, f Q l < f P l := by
  have hbP := mp_box_fixed hf hP hSM P hPd hxP
  have hbQ := mp_box_fixed hf hP hSM Q hQd hxQ
  by_cases heq : f P = f Q
  · exact Or.inl heq
  obtain ⟨j, hj⟩ : ∃ j, f P j ≠ f Q j := by
    by_contra h
    push Not at h
    exact heq (funext h)
  by_cases h1 : f P ≤ f Q
  · refine Or.inr (Or.inl fun l => lt_of_le_of_ne (h1 l) fun hl => ?_)
    have hij : l ≠ j := fun h => hj (h ▸ hl)
    exact mp_strict hf hSM hxP hxQ hbP hbQ hij hl (lt_of_le_of_ne (h1 j) hj)
  by_cases h2 : f Q ≤ f P
  · refine Or.inr (Or.inr fun l => lt_of_le_of_ne (h2 l) fun hl => ?_)
    have hij : l ≠ j := fun h => hj (h ▸ hl.symm)
    exact mp_strict hf hSM hxQ hxP hbQ hbP hij hl (lt_of_le_of_ne (h2 j) (Ne.symm hj))
  exfalso
  obtain ⟨i, hi⟩ : ∃ i, f Q i < f P i := by
    by_contra h
    push Not at h
    exact h1 h
  obtain ⟨k, hk⟩ : ∃ k, f P k < f Q k := by
    by_contra h
    push Not at h
    exact h2 h
  exact mp_incomparable hf hSM.1 hxP hxQ hbP hbQ hi hk

omit [Fintype ι] in
/-- **Exercise 22.E.5(b)** with individual rationality (MWG, p. 854). An individually rational,
strongly monotonic solution gives every agent strictly more than the threat point. -/
theorem mp_pos [Finite ι] [Nonempty ι] {f : BargainingProblem ι → ι → ℝ}
    (hf : IsBargainingSolution f) (hSM : StrongMonotoneBS f) (hIR : IndivRational f)
    (P : BargainingProblem ι) (hPd : P.d = 0) (l : ι) : 0 < f P l := by
  cases nonempty_fintype ι
  obtain ⟨ε, hε, hp⟩ := P.exists_gt
  have hb : ∀ _ : ι, (0 : ℝ) < ε / 2 := fun _ => by positivity
  set Bx := boxProblem (fun _ : ι => ε / 2) hb with hBx
  have hsub : Bx.U ⊆ P.U := fun u hu => P.comprehensive _ hp _ fun i => (hu i).trans (by
    change ε / 2 ≤ P.d i + ε
    rw [hPd, Pi.zero_apply]
    linarith)
  have hint : f Bx ∈ interior P.U := P.mem_interior_of_lt hp fun i => by
    have h1 : f Bx i ≤ ε / 2 := hf Bx i
    change f Bx i < P.d i + ε
    rw [hPd, Pi.zero_apply]
    linarith
  have h := hSM.2 Bx P hsub (by rw [hPd]; rfl) hint l
  have h0 : Bx.d l ≤ f Bx l := hIR Bx l
  have h00 : Bx.d l = 0 := rfl
  linarith

/-- **Exercise 22.E.5(b)** (MWG, p. 854), corrected: with individual rationality added
(Definition 22.E.6), the values `C` of an independent-of-origins, Paretian, strongly monotonic
solution on normalized two-person problems form a strictly increasing chain in `ℝ²₊₊` with
points arbitrarily close to the origin; on each normalized problem `f(U)` is the unique point
of `C` on the (weak Pareto) boundary of `U`; and in general `f(U) - u* ∈ C`. -/
theorem exercise_22_E_5b {f : BargainingProblem (Fin 2) → Fin 2 → ℝ}
    (hf : IsBargainingSolution f) (hIUO : IUO f) (hP : ParetoBS f) (hSM : StrongMonotoneBS f)
    (hIR : IndivRational f) :
    (∀ c ∈ solutionCurve f, ∀ l, 0 < c l) ∧
    (∀ c ∈ solutionCurve f, ∀ c' ∈ solutionCurve f,
      c = c' ∨ (∀ l, c l < c' l) ∨ ∀ l, c' l < c l) ∧
    (∀ ε > 0, ∃ c ∈ solutionCurve f, ∀ l, c l < ε) ∧
    (∀ P : BargainingProblem (Fin 2), P.d = 0 → ∀ c ∈ solutionCurve f,
      (c ∈ P.U ∧ ¬∃ v ∈ P.U, ∀ l, c l < v l) ↔ c = f P) ∧
    ∀ P : BargainingProblem (Fin 2), f P - P.d ∈ solutionCurve f := by
  have hpos : ∀ c ∈ solutionCurve f, ∀ l, 0 < c l := by
    rintro c ⟨P, hPd, rfl⟩ l
    exact mp_pos hf hSM hIR P hPd l
  have hchain : ∀ c ∈ solutionCurve f, ∀ c' ∈ solutionCurve f,
      c = c' ∨ (∀ l, c l < c' l) ∨ ∀ l, c' l < c l := by
    rintro c ⟨P, hPd, rfl⟩ c' ⟨Q, hQd, rfl⟩
    exact exercise_22_E_5b_chain hf hP hSM hPd hQd (mp_pos hf hSM hIR P hPd)
      (mp_pos hf hSM hIR Q hQd)
  refine ⟨hpos, hchain, fun ε hε => ?_, fun P hPd c hc => ?_, fun P => ?_⟩
  · have hb : ∀ _ : Fin 2, (0 : ℝ) < ε / 2 := fun _ => by positivity
    refine ⟨f (boxProblem (fun _ => ε / 2) hb), ⟨_, rfl, rfl⟩, fun l => ?_⟩
    have hm : f (boxProblem (fun _ => ε / 2) hb) ≤ fun _ => ε / 2 :=
      hf (boxProblem (fun _ => ε / 2) hb)
    have : f (boxProblem (fun _ => ε / 2) hb) l ≤ ε / 2 := hm l
    linarith
  · have hfP : f P ∈ solutionCurve f := ⟨P, hPd, rfl⟩
    constructor
    · rintro ⟨hcU, hbd⟩
      rcases hchain c hc (f P) hfP with h | h | h
      · exact h
      · exact absurd ⟨f P, hf P, h⟩ hbd
      · exact absurd ⟨c, hcU, h⟩ (hP P)
    · rintro rfl
      exact ⟨hf P, hP P⟩
  · refine ⟨P.normalize, P.normalize_d, ?_⟩
    rw [normalize_eq hIUO P, add_sub_cancel_right]

/-- **Exercise 22.E.5(b)**, instance (MWG, p. 854): the egalitarian solution satisfies all the
hypotheses of `exercise_22_E_5b`. -/
theorem exercise_22_E_5b_instance :
    IsBargainingSolution (egal (ι := Fin 2)) ∧ IUO (egal (ι := Fin 2)) ∧
      ParetoBS (egal (ι := Fin 2)) ∧ StrongMonotoneBS (egal (ι := Fin 2)) ∧
      IndivRational (egal (ι := Fin 2)) :=
  ⟨example_22_E_1.1, example_22_E_1.2.1, example_22_E_1.2.2.1, egal_strongMonotone,
    example_22_E_1.2.2.2.2.1⟩

/-- The egalitarian solution measured from the lowered threat point `u* + e`. -/
noncomputable def shiftEgal [Nonempty ι] (e : ι → ℝ) (he0 : ∀ i, e i ≤ 0) (he1 : ∀ i, -1 ≤ e i)
    (P : BargainingProblem ι) : ι → ℝ :=
  egal (P.shiftThreat e he0 he1)

/-- The shifted egalitarian solution is a bargaining solution, independent of utility origins,
Paretian and strongly monotonic. -/
theorem shiftEgal_props [Nonempty ι] (e : ι → ℝ) (he0 : ∀ i, e i ≤ 0) (he1 : ∀ i, -1 ≤ e i) :
    IsBargainingSolution (shiftEgal e he0 he1) ∧ IUO (shiftEgal e he0 he1) ∧
      ParetoBS (shiftEgal e he0 he1) ∧ StrongMonotoneBS (shiftEgal e he0 he1) := by
  refine ⟨fun P => (P.shiftThreat e he0 he1).rayPoint_mem fun _ => one_pos, fun P a => ?_,
    fun P => (P.shiftThreat e he0 he1).rayPoint_pareto fun _ => one_pos,
    fun P P' hsub hd => egal_monotoneBS _ _ hsub (by rw [shiftThreat_d, shiftThreat_d, hd]),
    fun P P' hsub hd hint => egal_strongMonotone.2 _ _ hsub
      (by rw [shiftThreat_d, shiftThreat_d, hd]) hint⟩
  have : (P.translate a).shiftThreat e he0 he1 = (P.shiftThreat e he0 he1).translate a := by
    ext v
    · exact Iff.rfl
    · change P.d v + a v + e v = P.d v + e v + a v
      ring
  simp only [shiftEgal]
  rw [this, egal_IUO]

/-- **Exercise 22.E.5(b)** (MWG, p. 854): the claim fails without individual rationality. The
egalitarian solution measured from `(-1, 0)` is IUO, Paretian and strongly monotonic, but its
values on normalized problems lie on the line `u₂ = u₁ + 1`, so none is within `1/2` of the
origin, and some has a negative coordinate: there is no strictly increasing curve starting at
the origin through all of them. -/
theorem exercise_22_E_5b_needs_IR : ∃ f : BargainingProblem (Fin 2) → Fin 2 → ℝ,
    IsBargainingSolution f ∧ IUO f ∧ ParetoBS f ∧ StrongMonotoneBS f ∧
    (∀ P : BargainingProblem (Fin 2), P.d = 0 → f P 1 = f P 0 + 1) ∧
    (∀ P : BargainingProblem (Fin 2), P.d = 0 → 1 / 2 ≤ |f P 0| ∨ 1 / 2 ≤ |f P 1|) ∧
    ∃ P : BargainingProblem (Fin 2), P.d = 0 ∧ f P 0 < 0 := by
  have he0 : ∀ i, (![-1, 0] : Fin 2 → ℝ) i ≤ 0 := fun i => by fin_cases i <;> norm_num
  have he1 : ∀ i, -1 ≤ (![-1, 0] : Fin 2 → ℝ) i := fun i => by fin_cases i <;> norm_num
  have hline : ∀ P : BargainingProblem (Fin 2), P.d = 0 →
      shiftEgal ![-1, 0] he0 he1 P 1 = shiftEgal ![-1, 0] he0 he1 P 0 + 1 := by
    intro P hPd
    simp only [shiftEgal, egal, rayPoint, shiftThreat_d, hPd, Pi.add_apply, Pi.zero_apply,
      mul_one]
    norm_num
  obtain ⟨h1, h2, h3, h4⟩ := shiftEgal_props ![-1, 0] he0 he1
  refine ⟨shiftEgal ![-1, 0] he0 he1, h1, h2, h3, h4, hline, fun P hPd => ?_, ?_⟩
  · have hl := hline P hPd
    by_cases h : shiftEgal ![-1, 0] he0 he1 P 0 ≤ -1 / 2
    · left
      have := neg_abs_le (shiftEgal ![-1, 0] he0 he1 P 0)
      linarith
    · right
      have := le_abs_self (shiftEgal ![-1, 0] he0 he1 P 1)
      linarith
  · have hb : ∀ _ : Fin 2, (0 : ℝ) < 1 / 2 := fun _ => by norm_num
    refine ⟨boxProblem (fun _ => 1 / 2) hb, rfl, ?_⟩
    have hl := hline (boxProblem (fun _ => 1 / 2) hb) rfl
    have hm : shiftEgal ![-1, 0] he0 he1 (boxProblem (fun _ => 1 / 2) hb) ≤ fun _ => 1 / 2 :=
      h1 (boxProblem (fun _ => 1 / 2) hb)
    have hmem : shiftEgal ![-1, 0] he0 he1 (boxProblem (fun _ => 1 / 2) hb) 1 ≤ 1 / 2 := hm 1
    linarith

end MWG.WelfareBargaining
