/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGClassicalDemand.UtilityExercises
import MWGClassicalDemand.UtilityRepresentation

/-!
# Exercise 3.C.5(b), "only if": quasilinear representations

MWG, Exercise 3.C.5(b), p. 96: a continuous rational `≿` on `(-∞, ∞) × ℝ^{L-1}_+` that is
quasilinear with respect to good `k` admits a utility `u(x) = x_k + φ(x_{-k})`.

Following the book's hint, take a continuous representation `v` (Proposition 3.C.1 on the
convex consumption set, `proposition_3_C_1_convex`) and let `g(t) = v(t e_k)`, continuous and
strictly increasing. The key step (`closer_quasilinear_axis`) is that every `x` is indifferent
to some `t e_k`. If not, `v(x)` lies above (or below) the whole range of `g`; then the supremum
`M` of that range is a value `v(z)` (the image of the connected consumption set is an
interval), `z - e_k` is again off the axis classes and so lies below them all, and the
intermediate value theorem on `s ↦ v(z - s e_k)` puts some `z - s e_k` in the class of `0`,
whence `z ∼ s e_k` and `M = g(s) < g(s + 1) ≤ M`. Then `u(x) = t(x)`, the unique `t` with
`x ∼ t e_k`, satisfies `u(x + α e_k) = u(x) + α` (`exercise_3_C_5b_only_if`).
-/

namespace MWG.ClassicalDemand

open Filter Topology MWG.ConsumerChoice Kreps.PreferenceProperties

variable {L : ℕ}

/-- The quasilinear consumption set is convex. -/
theorem convex_quasilinearDomain (k : Fin L) : Convex ℝ (quasilinearDomain k) := by
  intro x hx y hy a b ha hb _ l hl
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  exact add_nonneg (mul_nonneg ha (hx l hl)) (mul_nonneg hb (hy l hl))

/-- Shifting the numeraire keeps a bundle in the quasilinear consumption set. -/
theorem quasilinearDomain_shift {k : Fin L} {x : Fin L → ℝ} (hx : x ∈ quasilinearDomain k)
    (α : ℝ) : x + α • unitVec k ∈ quasilinearDomain k := by
  intro l hl
  simp only [Pi.add_apply, Pi.smul_apply, unitVec, Pi.single_eq_of_ne hl, smul_eq_mul, mul_zero,
    add_zero]
  exact hx l hl

/-- The numeraire axis `t e_k` lies in the quasilinear consumption set. -/
theorem quasilinearDomain_axis (k : Fin L) (t : ℝ) : t • unitVec k ∈ quasilinearDomain k := by
  intro l hl
  simp [unitVec, Pi.single_eq_of_ne hl]

/-- **Exercise 3.C.5(b)** (MWG, p. 96), the key step: under the hypotheses of the exercise and a
continuous representation `v`, every bundle `x` has the utility of some point `t e_k` of the
numeraire axis. -/
theorem closer_quasilinear_axis {k : Fin L} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hq : QuasilinearWrt k r) {v : (Fin L → ℝ) → ℝ}
    (hvc : ContinuousOn v (quasilinearDomain k)) (hv : RepresentsOn (quasilinearDomain k) v r)
    {x : Fin L → ℝ} (hx : x ∈ quasilinearDomain k) : ∃ t : ℝ, v x = v (t • unitVec k) := by
  set D := quasilinearDomain k with hD
  set e : Fin L → ℝ := unitVec k with he
  set g : ℝ → ℝ := fun t => v (t • e) with hg
  -- strict increase along the numeraire
  have hstrict : ∀ y ∈ D, ∀ α : ℝ, 0 < α → v y < v (y + α • e) := by
    intro y hy α hα
    have hs := hq.2 y hy α hα
    have h1 := (hv _ (quasilinearDomain_shift hy α) y hy).1 hs.1
    have h2 : ¬ v (y + α • e) ≤ v y := fun h =>
      hs.2 ((hv y hy _ (quasilinearDomain_shift hy α)).2 h)
    exact lt_of_le_of_ne h1 fun heq => h2 heq.ge
  -- translation of indifference
  have htrans : ∀ y ∈ D, ∀ y' ∈ D, v y = v y' → ∀ α : ℝ, v (y + α • e) = v (y' + α • e) := by
    intro y hy y' hy' heq α
    have hind : Indifferent r y y' :=
      ⟨(hv y hy y' hy').2 heq.ge, (hv y' hy' y hy).2 heq.le⟩
    have := hq.1 y hy y' hy' hind α
    exact le_antisymm ((hv _ (quasilinearDomain_shift hy' α) _ (quasilinearDomain_shift hy α)).1
      this.2) ((hv _ (quasilinearDomain_shift hy α) _ (quasilinearDomain_shift hy' α)).1 this.1)
  have haxis : ∀ t s : ℝ, t • e + s • e = (t + s) • e := fun t s => (add_smul t s e).symm
  have hgmono : StrictMono g := by
    intro t s hts
    have := hstrict _ (quasilinearDomain_axis k t) (s - t) (sub_pos.2 hts)
    simp only [hg]
    rwa [haxis, add_sub_cancel] at this
  have hgcont : Continuous g := by
    have hpath : Continuous fun t : ℝ => t • e := continuous_id.smul continuous_const
    exact hvc.comp_continuous hpath fun t => quasilinearDomain_axis k t
  -- a value off the range of `g` is above or below all of it
  have hdich : ∀ c : ℝ, (∀ t, g t ≠ c) → (∀ t, g t < c) ∨ ∀ t, c < g t := by
    intro c hc
    by_contra hcon
    push Not at hcon
    obtain ⟨⟨t1, ht1⟩, ⟨t2, ht2⟩⟩ := hcon
    have hmem : c ∈ Set.uIcc (g t2) (g t1) := Set.mem_uIcc.2 (Or.inl ⟨ht2, ht1⟩)
    obtain ⟨t, -, ht⟩ := intermediate_value_uIcc hgcont.continuousOn hmem
    exact hc t ht
  -- the image of `D` is preconnected
  have hJ : IsPreconnected (v '' D) :=
    ((convex_quasilinearDomain k).isPreconnected).image v hvc
  -- a bundle with the utility of an axis point shifts along the axis
  have hshiftaxis : ∀ y ∈ D, ∀ t α : ℝ, v y = g t → v (y + α • e) = g (t + α) := by
    intro y hy t α hyt
    rw [htrans y hy _ (quasilinearDomain_axis k t) hyt α, haxis]
  by_contra hcon
  push Not at hcon
  have hcon' : ∀ t, g t ≠ v x := fun t h => hcon t h.symm
  rcases hdich (v x) hcon' with hbelow | habove
  · -- `v(x)` lies above the whole axis
    have hbdd : BddAbove (Set.range g) := ⟨v x, by rintro _ ⟨t, rfl⟩; exact (hbelow t).le⟩
    set M := sSup (Set.range g) with hM
    have hgM : ∀ t, g t < M := fun t =>
      lt_of_lt_of_le (hgmono (lt_add_one t)) (le_csSup hbdd ⟨t + 1, rfl⟩)
    have hMx : M ≤ v x := csSup_le ⟨g 0, 0, rfl⟩ fun _ ⟨t, ht⟩ => ht ▸ (hbelow t).le
    obtain ⟨z, hz, hzM⟩ : ∃ z ∈ D, v z = M :=
      hJ.Icc_subset ⟨0 • e, quasilinearDomain_axis k 0, rfl⟩ ⟨x, hx, rfl⟩
        ⟨(hgM 0).le, hMx⟩
    have hz1 : z + (-1 : ℝ) • e ∈ D := quasilinearDomain_shift hz (-1)
    have hoff : ∀ t, g t ≠ v (z + (-1 : ℝ) • e) := by
      intro t ht
      have := hshiftaxis _ hz1 t 1 ht.symm
      rw [add_assoc, ← add_smul, neg_add_cancel, zero_smul, add_zero, hzM] at this
      exact absurd this (hgM (t + 1)).ne'
    have hlow : ∀ t, v (z + (-1 : ℝ) • e) < g t := by
      rcases hdich _ hoff with hb | ha
      · exfalso
        have h1 : v z ≤ v (z + (-1 : ℝ) • e) := by
          rw [hzM]; exact csSup_le ⟨g 0, 0, rfl⟩ fun _ ⟨t, ht⟩ => ht ▸ (hb t).le
        have h2 := hstrict _ hz1 1 one_pos
        rw [add_assoc, ← add_smul, neg_add_cancel, zero_smul, add_zero] at h2
        linarith
      · exact ha
    set f : ℝ → ℝ := fun s => v (z + (-s) • e) with hf
    have hfc : ContinuousOn f (Set.Icc 0 1) := by
      refine hvc.comp (Continuous.continuousOn (by fun_prop)) fun s _ =>
        quasilinearDomain_shift hz (-s)
    have hf0 : f 0 = M := by simp [hf, hzM]
    have hmem : g 0 ∈ Set.Icc (f 1) (f 0) := ⟨(hlow 0).le, hf0 ▸ (hgM 0).le⟩
    obtain ⟨s, -, hs⟩ := intermediate_value_Icc' zero_le_one hfc hmem
    have := hshiftaxis _ (quasilinearDomain_shift hz (-s)) 0 s hs
    rw [add_assoc, ← add_smul, neg_add_cancel, zero_smul, add_zero, hzM, zero_add] at this
    exact absurd this (hgM s).ne'
  · -- `v(x)` lies below the whole axis
    have hbdd : BddBelow (Set.range g) := ⟨v x, by rintro _ ⟨t, rfl⟩; exact (habove t).le⟩
    set m := sInf (Set.range g) with hm
    have hgm : ∀ t, m < g t := fun t =>
      lt_of_le_of_lt (csInf_le hbdd ⟨t - 1, rfl⟩) (hgmono (sub_one_lt t))
    have hmx : v x ≤ m := le_csInf ⟨g 0, 0, rfl⟩ fun _ ⟨t, ht⟩ => ht ▸ (habove t).le
    obtain ⟨z, hz, hzm⟩ : ∃ z ∈ D, v z = m :=
      hJ.Icc_subset ⟨x, hx, rfl⟩ ⟨0 • e, quasilinearDomain_axis k 0, rfl⟩
        ⟨hmx, (hgm 0).le⟩
    have hz1 : z + (1 : ℝ) • e ∈ D := quasilinearDomain_shift hz 1
    have hoff : ∀ t, g t ≠ v (z + (1 : ℝ) • e) := by
      intro t ht
      have := hshiftaxis _ hz1 t (-1) ht.symm
      rw [add_assoc, ← add_smul, add_neg_cancel, zero_smul, add_zero, hzm] at this
      exact absurd this (hgm (t + -1)).ne
    have hhigh : ∀ t, g t < v (z + (1 : ℝ) • e) := by
      rcases hdich _ hoff with hb | ha
      · exact hb
      · exfalso
        have h1 : v (z + (1 : ℝ) • e) ≤ v z := by
          rw [hzm]; exact le_csInf ⟨g 0, 0, rfl⟩ fun _ ⟨t, ht⟩ => ht ▸ (ha t).le
        have h2 := hstrict _ hz 1 one_pos
        linarith
    set f : ℝ → ℝ := fun s => v (z + s • e) with hf
    have hfc : ContinuousOn f (Set.Icc 0 1) := by
      refine hvc.comp (Continuous.continuousOn (by fun_prop)) fun s _ =>
        quasilinearDomain_shift hz s
    have hf0 : f 0 = m := by simp [hf, hzm]
    have hmem : g 0 ∈ Set.Icc (f 0) (f 1) := ⟨hf0 ▸ (hgm 0).le, (hhigh 0).le⟩
    obtain ⟨s, -, hs⟩ := intermediate_value_Icc zero_le_one hfc hmem
    have := hshiftaxis _ (quasilinearDomain_shift hz s) 0 (-s) hs
    rw [add_assoc, ← add_smul, add_neg_cancel, zero_smul, add_zero, hzm, zero_add] at this
    exact absurd this (hgm (-s)).ne

/-- **Exercise 3.C.5(b)** (MWG, p. 96), "only if". A continuous rational `≿` on
`(-∞, ∞) × ℝ^{L-1}_+` (numeraire `k`) that is quasilinear with respect to good `k` admits a
utility function `u(x) = x_k + φ(x)` with `φ` independent of `x_k`. -/
theorem exercise_3_C_5b_only_if {k : Fin L} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hr : RationalOn (quasilinearDomain k) r) (hc : PrefContinuous (quasilinearDomain k) r)
    (hq : QuasilinearWrt k r) :
    ∃ φ : (Fin L → ℝ) → ℝ, (∀ x : Fin L → ℝ, ∀ t : ℝ, φ (x + t • unitVec k) = φ x) ∧
      RepresentsOn (quasilinearDomain k) (fun x => x k + φ x) r := by
  classical
  set D := quasilinearDomain k with hD
  set e : Fin L → ℝ := unitVec k with he
  obtain ⟨v, hvc, hv⟩ := proposition_3_C_1_convex (convex_quasilinearDomain k) hr hc
  have haxis := fun {x} (hx : x ∈ D) => closer_quasilinear_axis hq hvc hv hx
  -- strict monotonicity along the axis, as in the key step
  have hgmono : StrictMono fun t : ℝ => v (t • e) := by
    intro t s hts
    have hs := hq.2 _ (quasilinearDomain_axis k t) (s - t) (sub_pos.2 hts)
    rw [← add_smul, add_sub_cancel] at hs
    have h1 := (hv _ (quasilinearDomain_axis k s) _ (quasilinearDomain_axis k t)).1 hs.1
    have h2 : ¬ v (s • e) ≤ v (t • e) := fun h =>
      hs.2 ((hv _ (quasilinearDomain_axis k t) _ (quasilinearDomain_axis k s)).2 h)
    exact lt_of_le_of_ne h1 fun heq => h2 heq.ge
  set τ : (Fin L → ℝ) → ℝ := fun x => if h : x ∈ D then Classical.choose (haxis h) else 0
    with hτ
  have hτspec : ∀ x (hx : x ∈ D), v x = v (τ x • e) := by
    intro x hx
    simp only [hτ, hx, ↓reduceDIte]
    exact Classical.choose_spec (haxis hx)
  have hτshift : ∀ x ∈ D, ∀ α : ℝ, τ (x + α • e) = τ x + α := by
    intro x hx α
    have hx' := quasilinearDomain_shift hx α
    apply hgmono.injective
    simp only
    rw [← hτspec _ hx', add_smul]
    have hind : Indifferent r x (τ x • e) :=
      ⟨(hv x hx _ (quasilinearDomain_axis k _)).2 (hτspec x hx).ge,
        (hv _ (quasilinearDomain_axis k _) x hx).2 (hτspec x hx).le⟩
    have := hq.1 x hx _ (quasilinearDomain_axis k _) hind α
    exact le_antisymm
      ((hv _ (quasilinearDomain_shift (quasilinearDomain_axis k _) α) _ hx').1 this.2)
      ((hv _ hx' _ (quasilinearDomain_shift (quasilinearDomain_axis k _) α)).1 this.1)
  have hDshift : ∀ (x : Fin L → ℝ) (t : ℝ), x + t • e ∈ D ↔ x ∈ D := by
    intro x t
    refine ⟨fun h => ?_, fun h => quasilinearDomain_shift h t⟩
    have := quasilinearDomain_shift h (-t)
    rwa [add_assoc, ← add_smul, add_neg_cancel, zero_smul, add_zero] at this
  refine ⟨fun x => if x ∈ D then τ x - x k else 0, fun x t => ?_, fun x hx y hy => ?_⟩
  · by_cases hx : x ∈ D
    · simp only [(hDshift x t).2 hx, hx, ↓reduceIte]
      rw [hτshift x hx t]
      simp only [he, unitVec, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul,
        mul_one]
      ring
    · have hx' : x + t • e ∉ D := fun h => hx ((hDshift x t).1 h)
      simp only [hx, hx', ↓reduceIte]
  · simp only [hx, hy, ↓reduceIte, add_sub_cancel]
    rw [hv x hx y hy, hτspec x hx, hτspec y hy]
    exact hgmono.le_iff_le

end MWG.ClassicalDemand
