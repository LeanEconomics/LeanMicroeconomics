/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPositiveEquilibriumTheory.Exercises17G
import Mathlib.Order.FixedPoints

/-!
# Strong gross substitutes and lattices of equilibria (MWG Exercises 17.F.16 and 17.G.3)

A function `g : [0, r]^N → ℝ^N` (`sgsBox N r`) with `g(0) ≫ 0`, `g(r, …, r) ≪ 0`; no Walras' law,
homogeneity or continuity is assumed.

* `BoxGrossSubstitute`: the gross substitute property on the box. `StrongGrossSubstitute` (SGS):
  for some `α > 0`, `αg(p) + p ∈ [0, r]^N` and every coordinate of `αg(p) + p` is strictly
  increasing in `p` (`p ≤ p'`, `p ≠ p'`).
* **(a)** SGS implies GS (`exercise_17_F_16a`). **(b)** GS does not imply SGS
  (`exercise_17_F_16b_counter`, a discontinuous example); a `C¹` gross substitute `g` is SGS
  (`exercise_17_F_16b`; `g` is assumed `C¹` on all of `ℝ^N`).
* **(c)** Under SGS there is an equilibrium (`exercise_17_F_16c`): Tarski's fixed point theorem
  for the monotone self-map `p ↦ αg(p) + p` of the complete lattice `[0, r]^N` (`sgs_tarski`,
  Mathlib's `OrderHom.lfp`/`gfp`).
* **(d)** An example with `N = 2` and three equilibria (`exercise_17_F_16d`).
* **(e)** Two equilibria have a common upper and a common lower equilibrium
  (`exercise_17_F_16e`). **(f)** There are a least and a greatest equilibrium
  (`exercise_17_F_16f`).
* **(g)** For `N = 1`: if `g' < 0` at every equilibrium, the equilibrium is unique
  (`exercise_17_F_16g_one`). For `N ≥ 2` the book's argument is an index argument
  ("perhaps nonrigorously"); not formalised (OPEN).
* **(h)** For the first `N` excess demands of an `(N + 1)`-good economy with gross substitutes
  (`p_{N+1} = 1`): `Dĝ(p̂)p̂ ≪ 0` at an equilibrium when the cross effects of the numeraire are
  positive (the dominant diagonal of (g)), and the equilibrium is unique
  (`exercise_17_F_16h`, via Proposition 17.F.3).
* **Exercise 17.G.3** (`exercise_17_G_3`): if `ĝ ≥ g` and both are SGS, the least and greatest
  equilibria move up.
-/

namespace MWG.PositiveEquilibriumTheory

open Filter Topology

variable {N : ℕ}

/-- **Exercise 17.F.16** (MWG, p. 646). The domain `[0, r]^N`. -/
def sgsBox (N : ℕ) (r : ℝ) : Set (Fin N → ℝ) := Set.Icc 0 (fun _ => r)

/-- **Exercise 17.F.16** (MWG, p. 646). The gross substitute property (Definition 17.F.2) for `g`
on `[0, r]^N`. -/
def BoxGrossSubstitute (r : ℝ) (g : (Fin N → ℝ) → Fin N → ℝ) : Prop :=
  ∀ p ∈ sgsBox N r, ∀ p' ∈ sgsBox N r, ∀ l, p l < p' l → (∀ k, k ≠ l → p' k = p k) →
    ∀ k, k ≠ l → g p k < g p' k

/-- **Exercise 17.F.16(a)** (MWG, p. 647). The strong gross substitute property: for some `α > 0`,
`αg(p) + p ∈ [0, r]^N` for every `p ∈ [0, r]^N`, and every coordinate of `αg(p) + p` is strictly
increasing in `p`. -/
def StrongGrossSubstitute (r : ℝ) (g : (Fin N → ℝ) → Fin N → ℝ) : Prop :=
  ∃ α : ℝ, 0 < α ∧ (∀ p ∈ sgsBox N r, α • g p + p ∈ sgsBox N r) ∧
    ∀ p ∈ sgsBox N r, ∀ p' ∈ sgsBox N r, p ≤ p' → p ≠ p' → ∀ k,
      (α • g p + p) k < (α • g p' + p') k

/-- **Exercise 17.F.16(a)** (MWG, p. 647). SGS implies GS. -/
theorem exercise_17_F_16a {r : ℝ} {g : (Fin N → ℝ) → Fin N → ℝ}
    (h : StrongGrossSubstitute r g) : BoxGrossSubstitute r g := by
  obtain ⟨α, hα, -, hinc⟩ := h
  intro p hp p' hp' l hl he k hk
  have hle : p ≤ p' := fun i => by
    by_cases hi : i = l
    · subst hi; exact hl.le
    · exact (he i hi).ge
  have hne : p ≠ p' := fun h => by rw [h] at hl; exact lt_irrefl _ hl
  have := hinc p hp p' hp' hle hne k
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, he k hk] at this
  exact lt_of_mul_lt_mul_left (by linarith) hα.le

/-! ### Tarski -/

/-- **Theorem M.I.1 (Tarski)**, for boxes of `ℝ^N` (MWG, used in Exercise 17.F.16(c)): a monotone
self-map `f` of `[a, b]` has a least fixed point, below every `y` with `f(y) ≤ y`, and a greatest
fixed point, above every `y` with `y ≤ f(y)`. -/
theorem sgs_tarski {a b : Fin N → ℝ} (hab : a ≤ b) {f : (Fin N → ℝ) → Fin N → ℝ}
    (hmap : ∀ x ∈ Set.Icc a b, f x ∈ Set.Icc a b) (hmono : MonotoneOn f (Set.Icc a b)) :
    (∃ x ∈ Set.Icc a b, f x = x ∧ ∀ y ∈ Set.Icc a b, f y ≤ y → x ≤ y) ∧
      ∃ x ∈ Set.Icc a b, f x = x ∧ ∀ y ∈ Set.Icc a b, y ≤ f y → y ≤ x := by
  have : Fact (a ≤ b) := ⟨hab⟩
  let F : Set.Icc a b →o Set.Icc a b :=
    ⟨fun x => ⟨f x, hmap x x.2⟩, fun x y h => hmono x.2 y.2 h⟩
  set x0 : Set.Icc a b := OrderHom.lfp F
  set x1 : Set.Icc a b := OrderHom.gfp F
  refine ⟨⟨x0.1, x0.2, congrArg Subtype.val F.map_lfp, fun y hy hfy => ?_⟩,
    ⟨x1.1, x1.2, congrArg Subtype.val F.map_gfp, fun y hy hfy => ?_⟩⟩
  · exact OrderHom.lfp_le F (a := ⟨y, hy⟩) hfy
  · exact OrderHom.le_gfp F (a := ⟨y, hy⟩) hfy

/-- Under SGS, `p ↦ αg(p) + p` is a monotone self-map of the box whose fixed points are the
equilibria. -/
theorem sgs_map {r : ℝ} {g : (Fin N → ℝ) → Fin N → ℝ} {α : ℝ}
    (hinc : ∀ p ∈ sgsBox N r, ∀ p' ∈ sgsBox N r, p ≤ p' → p ≠ p' → ∀ k,
      (α • g p + p) k < (α • g p' + p') k) :
    MonotoneOn (fun p => α • g p + p) (sgsBox N r) := by
  intro p hp p' hp' hle
  by_cases he : p = p'
  · subst he; exact le_refl _
  · exact fun k => (hinc p hp p' hp' hle he k).le

theorem sgs_fixed_iff {g : (Fin N → ℝ) → Fin N → ℝ} {α : ℝ} (hα : 0 < α) (p : Fin N → ℝ) :
    α • g p + p = p ↔ g p = 0 := by
  constructor
  · intro h
    have : α • g p = 0 := by
      have := congrArg (fun x => x - p) h; simpa using this
    exact (smul_eq_zero.1 this).resolve_left hα.ne'
  · intro h; rw [h, smul_zero, zero_add]

theorem sgs_le_iff {g : (Fin N → ℝ) → Fin N → ℝ} {α : ℝ} (hα : 0 < α) (p : Fin N → ℝ) :
    α • g p + p ≤ p ↔ g p ≤ 0 := by
  constructor
  · intro h k
    have := h k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    have : α * g p k ≤ 0 := by linarith
    exact nonpos_of_mul_nonpos_right this hα
  · intro h k
    have := mul_nonpos_of_nonneg_of_nonpos hα.le (h k)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linarith

theorem sgs_ge_iff {g : (Fin N → ℝ) → Fin N → ℝ} {α : ℝ} (hα : 0 < α) (p : Fin N → ℝ) :
    p ≤ α • g p + p ↔ 0 ≤ g p := by
  constructor
  · intro h k
    have := h k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    have : 0 ≤ α * g p k := by linarith
    exact nonneg_of_mul_nonneg_right (by linarith) hα
  · intro h k
    have := mul_nonneg hα.le (h k)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linarith

theorem sgsBox_nonneg {r : ℝ} (hr : 0 ≤ r) : (0 : Fin N → ℝ) ≤ fun _ => r := fun _ => hr

/-- Equilibria are fixed points; the least fixed point lies below every `p` with `g(p) ≤ 0`, the
greatest above every `p` with `g(p) ≥ 0` (Exercise 17.F.16(c), (f)). -/
theorem sgs_extremal {r : ℝ} (hr : 0 ≤ r) {g : (Fin N → ℝ) → Fin N → ℝ}
    (h : StrongGrossSubstitute r g) :
    (∃ x ∈ sgsBox N r, g x = 0 ∧ ∀ y ∈ sgsBox N r, g y ≤ 0 → x ≤ y) ∧
      ∃ x ∈ sgsBox N r, g x = 0 ∧ ∀ y ∈ sgsBox N r, 0 ≤ g y → y ≤ x := by
  obtain ⟨α, hα, hmap, hinc⟩ := h
  obtain ⟨⟨x, hx, hfx, hlx⟩, ⟨y, hy, hfy, hly⟩⟩ :=
    sgs_tarski (sgsBox_nonneg hr) hmap (sgs_map hinc)
  exact ⟨⟨x, hx, (sgs_fixed_iff hα x).1 hfx, fun z hz hgz => hlx z hz ((sgs_le_iff hα z).2 hgz)⟩,
    ⟨y, hy, (sgs_fixed_iff hα y).1 hfy, fun z hz hgz => hly z hz ((sgs_ge_iff hα z).2 hgz)⟩⟩

/-- **Exercise 17.F.16(c)** (MWG, p. 647). Under SGS there is an equilibrium `p ∈ [0, r]^N`,
`g(p) = 0` (Tarski's fixed point theorem). -/
theorem exercise_17_F_16c {r : ℝ} (hr : 0 ≤ r) {g : (Fin N → ℝ) → Fin N → ℝ}
    (h : StrongGrossSubstitute r g) : ∃ p ∈ sgsBox N r, g p = 0 := by
  obtain ⟨⟨x, hx, hgx, -⟩, -⟩ := sgs_extremal hr h
  exact ⟨x, hx, hgx⟩

/-- **Exercise 17.F.16(f)** (MWG, p. 647). Under SGS the equilibrium set has a least element `p^min`
and a greatest element `p^max`: `p^min ≤ p ≤ p^max` whenever `g(p) = 0`. -/
theorem exercise_17_F_16f {r : ℝ} (hr : 0 ≤ r) {g : (Fin N → ℝ) → Fin N → ℝ}
    (h : StrongGrossSubstitute r g) :
    ∃ pmin ∈ sgsBox N r, ∃ pmax ∈ sgsBox N r, g pmin = 0 ∧ g pmax = 0 ∧
      ∀ p ∈ sgsBox N r, g p = 0 → pmin ≤ p ∧ p ≤ pmax := by
  obtain ⟨⟨x, hx, hgx, hlx⟩, ⟨y, hy, hgy, hly⟩⟩ := sgs_extremal hr h
  exact ⟨x, hx, y, hy, hgx, hgy, fun p hp hgp => ⟨hlx p hp hgp.le, hly p hp hgp.ge⟩⟩

/-- **Exercise 17.F.16(e)** (MWG, p. 647). If `g(p) = g(p') = 0` there is an equilibrium
`p'' ≥ p, p'` and an equilibrium `p''' ≤ p, p'` (Tarski on `[max(p, p'), r]` and
`[0, min(p, p')]`). -/
theorem exercise_17_F_16e {r : ℝ} {g : (Fin N → ℝ) → Fin N → ℝ}
    (h : StrongGrossSubstitute r g) {p p' : Fin N → ℝ} (hp : p ∈ sgsBox N r)
    (hp' : p' ∈ sgsBox N r) (hgp : g p = 0) (hgp' : g p' = 0) :
    (∃ q ∈ sgsBox N r, g q = 0 ∧ p ≤ q ∧ p' ≤ q) ∧
      ∃ q ∈ sgsBox N r, g q = 0 ∧ q ≤ p ∧ q ≤ p' := by
  obtain ⟨α, hα, hmap, hinc⟩ := h
  have hmono := sgs_map hinc
  have hfp : α • g p + p = p := (sgs_fixed_iff hα p).2 hgp
  have hfp' : α • g p' + p' = p' := (sgs_fixed_iff hα p').2 hgp'
  constructor
  · have hab : p ⊔ p' ≤ fun _ => r := sup_le hp.2 hp'.2
    have hsub : Set.Icc (p ⊔ p') (fun _ => r) ⊆ sgsBox N r := fun x hx =>
      ⟨le_trans (le_trans hp.1 le_sup_left) hx.1, hx.2⟩
    have hmap' : ∀ x ∈ Set.Icc (p ⊔ p') (fun _ => r), α • g x + x ∈
        Set.Icc (p ⊔ p') (fun _ => r) := fun x hx => by
      refine ⟨sup_le ?_ ?_, (hmap x (hsub hx)).2⟩
      · rw [← hfp]; exact hmono hp (hsub hx) (le_trans le_sup_left hx.1)
      · rw [← hfp']; exact hmono hp' (hsub hx) (le_trans le_sup_right hx.1)
    obtain ⟨⟨x, hx, hfx, -⟩, -⟩ := sgs_tarski hab hmap' (hmono.mono hsub)
    exact ⟨x, hsub hx, (sgs_fixed_iff hα x).1 hfx, le_trans le_sup_left hx.1,
      le_trans le_sup_right hx.1⟩
  · have hab : (0 : Fin N → ℝ) ≤ p ⊓ p' := le_inf hp.1 hp'.1
    have hsub : Set.Icc 0 (p ⊓ p') ⊆ sgsBox N r := fun x hx =>
      ⟨hx.1, le_trans hx.2 (le_trans inf_le_left hp.2)⟩
    have hmap' : ∀ x ∈ Set.Icc (0 : Fin N → ℝ) (p ⊓ p'), α • g x + x ∈
        Set.Icc (0 : Fin N → ℝ) (p ⊓ p') := fun x hx => by
      refine ⟨(hmap x (hsub hx)).1, le_inf ?_ ?_⟩
      · rw [← hfp]; exact hmono (hsub hx) hp (le_trans hx.2 inf_le_left)
      · rw [← hfp']; exact hmono (hsub hx) hp' (le_trans hx.2 inf_le_right)
    obtain ⟨⟨x, hx, hfx, -⟩, -⟩ := sgs_tarski hab hmap' (hmono.mono hsub)
    exact ⟨x, hsub hx, (sgs_fixed_iff hα x).1 hfx, le_trans hx.2 inf_le_left,
      le_trans hx.2 inf_le_right⟩

/-- **Exercise 17.G.3** (MWG, p. 648). Let `g` and `ĝ` both satisfy SGS on `[0, r]^N`, with `ĝ` an
upward shift of `g` (`ĝ(p) ≥ g(p)`). If `(p^min, p^max)` and `(p̂^min, p̂^max)` are the least and
greatest equilibria of `g` and `ĝ`, then `p̂^min ≥ p^min` and `p̂^max ≥ p^max`. -/
theorem exercise_17_G_3 {r : ℝ} (hr : 0 ≤ r) {g gh : (Fin N → ℝ) → Fin N → ℝ}
    (hg : StrongGrossSubstitute r g) (hgh : StrongGrossSubstitute r gh)
    (hshift : ∀ p ∈ sgsBox N r, g p ≤ gh p) {pmin pmax qmin qmax : Fin N → ℝ}
    (hpmin : pmin ∈ sgsBox N r ∧ g pmin = 0 ∧ ∀ p ∈ sgsBox N r, g p = 0 → pmin ≤ p)
    (hpmax : pmax ∈ sgsBox N r ∧ g pmax = 0 ∧ ∀ p ∈ sgsBox N r, g p = 0 → p ≤ pmax)
    (hqmin : qmin ∈ sgsBox N r ∧ gh qmin = 0 ∧ ∀ p ∈ sgsBox N r, gh p = 0 → qmin ≤ p)
    (hqmax : qmax ∈ sgsBox N r ∧ gh qmax = 0 ∧ ∀ p ∈ sgsBox N r, gh p = 0 → p ≤ qmax) :
    pmin ≤ qmin ∧ pmax ≤ qmax := by
  obtain ⟨⟨x, hx, hgx, hlx⟩, -⟩ := sgs_extremal hr hg
  obtain ⟨-, ⟨y, hy, hgy, hly⟩⟩ := sgs_extremal hr hgh
  constructor
  · -- `p^min ≤ x ≤ p̂^min`, as `g(p̂^min) ≤ ĝ(p̂^min) = 0`
    refine le_trans (hpmin.2.2 x hx hgx) (hlx qmin hqmin.1 ?_)
    have := hshift qmin hqmin.1
    rw [hqmin.2.1] at this
    exact this
  · -- `p^max ≤ y ≤ p̂^max`, as `ĝ(p^max) ≥ g(p^max) = 0`
    refine le_trans (hly pmax hpmax.1 ?_) (hqmax.2.2 y hy hgy)
    have := hshift pmax hpmax.1
    rw [hpmax.2.1] at this
    exact this

/-! ### (b): GS does not imply SGS -/

/-- The step function `s(t) = 1` for `t < 1/2`, `s(t) = -3` otherwise. -/
noncomputable def sgsStep (t : ℝ) : ℝ := if t < 1 / 2 then 1 else -3

/-- The two-good function `g(p) = (s(p₁) + p₂, s(p₂) + p₁)` on `[0, 1]²`. -/
noncomputable def sgsCounter (p : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![sgsStep (p 0) + p 1, sgsStep (p 1) + p 0]

/-- **Exercise 17.F.16(b)** (MWG, p. 647). The GS property does not imply SGS:
`g(p) = (s(p₁) + p₂, s(p₂) + p₁)` on `[0, 1]²` (`s` a downward step at `1/2`) has `g(0) ≫ 0`,
`g(1, 1) ≪ 0` and gross substitutes, but `αg₁ + p₁` jumps down at `p₁ = 1/2` for every `α > 0`. -/
theorem exercise_17_F_16b_counter :
    (∀ k, 0 < sgsCounter 0 k) ∧ (∀ k, sgsCounter (fun _ => 1) k < 0) ∧
      BoxGrossSubstitute 1 sgsCounter ∧ ¬ StrongGrossSubstitute 1 sgsCounter := by
  refine ⟨fun k => ?_, fun k => ?_, ?_, ?_⟩
  · fin_cases k <;> simp [sgsCounter, sgsStep]
  · fin_cases k <;> norm_num [sgsCounter, sgsStep]
  · intro p hp p' hp' l hl he k hk
    have h01 : (0 : Fin 2) ≠ 1 := by decide
    have hg0 : ∀ x : Fin 2 → ℝ, sgsCounter x 0 = sgsStep (x 0) + x 1 := fun x => rfl
    have hg1 : ∀ x : Fin 2 → ℝ, sgsCounter x 1 = sgsStep (x 1) + x 0 := fun x => rfl
    fin_cases l <;> fin_cases k <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue] at hl he hk ⊢
    · exact absurd rfl hk
    · rw [hg1, hg1, he 1 h01.symm]; linarith
    · rw [hg0, hg0, he 0 h01]; linarith
    · exact absurd rfl hk
  · rintro ⟨α, hα, -, hinc⟩
    set ε := min α (1 / 4) with hε
    have hε0 : 0 < ε := lt_min hα (by norm_num)
    have hε1 : ε ≤ 1 / 4 := min_le_right _ _
    have hεα : ε ≤ α := min_le_left _ _
    set p : Fin 2 → ℝ := ![1 / 2 - ε, 0] with hpd
    set p' : Fin 2 → ℝ := ![1 / 2, 0] with hp'd
    have hp : p ∈ sgsBox 2 1 := ⟨fun i => by fin_cases i <;> simp [p]; linarith,
      fun i => by fin_cases i <;> simp [p]; linarith⟩
    have hp' : p' ∈ sgsBox 2 1 := ⟨fun i => by fin_cases i <;> norm_num [p'],
      fun i => by fin_cases i <;> norm_num [p']⟩
    have hle : p ≤ p' := fun i => by fin_cases i <;> simp [p, p']; linarith
    have hne : p ≠ p' := fun h => by
      have := congrFun h 0; simp [p, p'] at this; linarith
    have := hinc p hp p' hp' hle hne 0
    have hs1 : sgsStep (1 / 2 - ε) = 1 := by
      unfold sgsStep
      split_ifs with h
      · rfl
      · exact absurd (by linarith) h
    have hs2 : sgsStep (1 / 2) = -3 := by simp [sgsStep]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, sgsCounter, p, p',
      Matrix.cons_val_zero, Matrix.cons_val_one, hs1, hs2] at this
    linarith

/-! ### (d): several equilibria -/

/-- `ψ(s) = (1 - s)(2 - s)(3 - s)`. -/
def sgsPsi (s : ℝ) : ℝ := (1 - s) * (2 - s) * (3 - s)

/-- The example of Exercise 17.F.16(d): `gₖ(p) = ψ(pₖ) - pₖ + p_{-k}` on `[0, 4]²`. -/
def sgsTwo (p : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![sgsPsi (p 0) - p 0 + p 1, sgsPsi (p 1) - p 1 + p 0]

/-- `s ↦ s + (ψ(s) - s)/24` is strictly increasing on `[0, 4]`. -/
theorem sgsPsi_mono {s t : ℝ} (hs : 0 ≤ s) (ht : t ≤ 4) (hst : s < t) :
    s + (sgsPsi s - s) / 24 < t + (sgsPsi t - t) / 24 := by
  have hs4 : s ≤ 4 := by linarith
  have ht0 : 0 ≤ t := by linarith
  have key : sgsPsi t - sgsPsi s = -(t - s) * (t ^ 2 + t * s + s ^ 2 - 6 * (t + s) + 11) := by
    simp only [sgsPsi]; ring
  have hq : t ^ 2 + t * s + s ^ 2 - 6 * (t + s) + 11 ≤ 11 := by
    nlinarith [mul_nonneg ht0 (by linarith : (0 : ℝ) ≤ 4 - t),
      mul_nonneg hs (by linarith : (0 : ℝ) ≤ 4 - s), sq_nonneg (t - s)]
  have hd : 0 < t - s := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hq hd.le]

/-- **Exercise 17.F.16(d)** (MWG, p. 647). An example with `N = 2` (`r = 4`) satisfying SGS
(`α = 1/24`), `g(0) ≫ 0`, `g(4, 4) ≪ 0`, with the three equilibria `(1, 1)`, `(2, 2)`,
`(3, 3)`. -/
theorem exercise_17_F_16d :
    StrongGrossSubstitute 4 sgsTwo ∧ (∀ k, 0 < sgsTwo 0 k) ∧ (∀ k, sgsTwo (fun _ => 4) k < 0) ∧
      sgsTwo ![1, 1] = 0 ∧ sgsTwo ![2, 2] = 0 ∧ sgsTwo ![3, 3] = 0 := by
  have hF : ∀ p : Fin 2 → ℝ, ∀ k : Fin 2, ((1 / 24 : ℝ) • sgsTwo p + p) k =
      p k + (sgsPsi (p k) - p k) / 24 + p (1 - k) / 24 := fun p k => by
    fin_cases k <;> simp [sgsTwo] <;> ring
  refine ⟨⟨1 / 24, by norm_num, fun p hp => ⟨fun k => ?_, fun k => ?_⟩, ?_⟩,
    fun k => ?_, fun k => ?_, ?_, ?_, ?_⟩
  · rw [hF, Pi.zero_apply]
    have h1 := hp.1 k
    have h2 := hp.1 (1 - k)
    have h3 := hp.2 k
    simp only [Pi.zero_apply] at h1 h2 h3
    rcases h1.lt_or_eq with h | h
    · have := sgsPsi_mono (le_refl 0) h3 h
      simp only [sgsPsi] at this ⊢
      linarith
    · rw [← h]; simp [sgsPsi]; linarith
  · rw [hF]
    change _ ≤ (4 : ℝ)
    have h1 := hp.1 k
    have h2 := hp.2 (1 - k)
    have h3 := hp.2 k
    simp only [Pi.zero_apply] at h1
    rcases h3.lt_or_eq with h | h
    · have := sgsPsi_mono h1 (le_refl 4) h
      simp only [sgsPsi] at this ⊢
      linarith
    · rw [h]; simp [sgsPsi]; linarith
  · intro p hp p' hp' hle hne k
    rw [hF, hF]
    have hk := hle k
    have hk' := hle (1 - k)
    obtain ⟨j, hj⟩ : ∃ j, p j < p' j := by
      by_contra hcon
      push Not at hcon
      exact hne (funext fun i => le_antisymm (hle i) (hcon i))
    rcases hk.lt_or_eq with h | h
    · have := sgsPsi_mono (hp.1 k) (hp'.2 k) h
      linarith
    · have hjk : j = 1 - k := by
        by_contra hjk
        have : j = k := by fin_cases j <;> fin_cases k <;> simp_all
        rw [this, h] at hj; exact lt_irrefl _ hj
      rw [hjk] at hj
      rw [h]
      linarith
  · fin_cases k <;> simp [sgsTwo, sgsPsi]
  · fin_cases k <;> simp [sgsTwo, sgsPsi] <;> norm_num
  · funext k; fin_cases k <;> simp [sgsTwo, sgsPsi]
  · funext k; fin_cases k <;> simp [sgsTwo, sgsPsi]
  · funext k; fin_cases k <;> simp [sgsTwo, sgsPsi]

/-! ### (g) for `N = 1` -/

/-- **Exercise 17.F.16(g)**, `N = 1` (MWG, p. 647). Let `g` be continuous on `[0, r]` and
differentiable with `g'(p) < 0` at every equilibrium `p ∈ [0, r]`. Then there is at most one
equilibrium. (For `N ≥ 2` the book's argument is the index theorem: OPEN.) -/
theorem exercise_17_F_16g_one {r : ℝ} {g : ℝ → ℝ} (hc : ContinuousOn g (Set.Icc 0 r))
    (hd : ∀ p ∈ Set.Icc 0 r, g p = 0 → ∃ d < 0, HasDerivAt g d p) {a b : ℝ}
    (ha : a ∈ Set.Icc 0 r) (hb : b ∈ Set.Icc 0 r) (hga : g a = 0) (hgb : g b = 0) : a = b := by
  wlog hab : a < b generalizing a b
  · rcases (not_lt.1 hab).lt_or_eq with h | h
    · exact (this hb ha hgb hga h).symm
    · exact h.symm
  obtain ⟨da, hda, hga'⟩ := hd a ha hga
  obtain ⟨db, hdb, hgb'⟩ := hd b hb hgb
  -- `g < 0` just right of `a`, `g > 0` just left of `b`
  have h1 : ∀ᶠ t in 𝓝[>] a, g t < 0 := by
    have := (wad_deriv_neg hga' hda).1; rwa [hga] at this
  have h2 : ∀ᶠ t in 𝓝[<] b, 0 < g t := by
    have := (wad_deriv_neg hgb' hdb).2; rwa [hgb] at this
  obtain ⟨u, hu, hu'⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1 h1
  obtain ⟨l, hl, hl'⟩ := (mem_nhdsLT_iff_exists_Ioo_subset).1 h2
  set a1 := (a + min u b) / 2 with ha1
  have hmin : a < min u b := lt_min hu hab
  have ha1a : a < a1 := by linarith
  have ha1u : a1 < min u b := by linarith
  have hga1 : g a1 < 0 := hu' ⟨ha1a, lt_of_lt_of_le ha1u (min_le_left _ _)⟩
  have ha1b : a1 < b := lt_of_lt_of_le ha1u (min_le_right _ _)
  set b1 := (max l a1 + b) / 2 with hb1
  have hmax : max l a1 < b := max_lt (Set.mem_Iio.1 hl) ha1b
  have hb1b : b1 < b := by linarith
  have hb1l : max l a1 < b1 := by linarith
  have hgb1 : 0 < g b1 := hl' ⟨lt_of_le_of_lt (le_max_left _ _) hb1l, hb1b⟩
  have ha1b1 : a1 < b1 := lt_of_le_of_lt (le_max_right _ _) hb1l
  have hsubr : Set.Icc a1 b1 ⊆ Set.Icc 0 r := fun x hx =>
    ⟨le_trans ha.1 (by linarith [hx.1]), le_trans (by linarith [hx.2]) hb.2⟩
  -- the first point of `[a₁, b₁]` where `g ≥ 0`
  set S := Set.Icc a1 b1 ∩ {x | 0 ≤ g x} with hS
  have hSc : IsClosed S :=
    (hc.mono hsubr).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hSne : S.Nonempty := ⟨b1, ⟨ha1b1.le, le_refl _⟩, hgb1.le⟩
  have hSb : BddBelow S := ⟨a1, fun x hx => hx.1.1⟩
  set c := sInf S with hcdef
  have hcS : c ∈ S := hSc.csInf_mem hSne hSb
  have hneg : ∀ t ∈ Set.Icc a1 b1, t < c → g t < 0 := fun t ht htc => by
    by_contra h
    push Not at h
    exact absurd (csInf_le hSb ⟨ht, h⟩) (not_le.2 htc)
  have hca1 : a1 < c := by
    rcases hcS.1.1.lt_or_eq with h | h
    · exact h
    · exfalso; have h0 : 0 ≤ g c := hcS.2; rw [← h] at h0; linarith
  have hgc : g c = 0 := by
    by_contra hne
    have hpos : 0 < g c := lt_of_le_of_ne hcS.2 (Ne.symm hne)
    obtain ⟨t, ht, hgt⟩ := intermediate_value_Icc hca1.le ((hc.mono hsubr).mono
      (Set.Icc_subset_Icc le_rfl hcS.1.2)) ⟨hga1.le, hpos.le⟩
    rcases ht.2.lt_or_eq with htc | htc
    · have := hneg t ⟨ht.1, le_trans ht.2 hcS.1.2⟩ htc; linarith
    · rw [htc] at hgt; exact hne hgt
  obtain ⟨dc, hdc, hgc'⟩ := hd c (hsubr hcS.1) hgc
  have h3 : ∀ᶠ t in 𝓝[<] c, 0 < g t := by
    have := (wad_deriv_neg hgc' hdc).2; rwa [hgc] at this
  have h4 : ∀ᶠ t in 𝓝[<] c, a1 < t := Ioo_mem_nhdsLT hca1 |> fun h =>
    Filter.mem_of_superset h fun t ht => ht.1
  obtain ⟨t, ⟨ht3, ht4⟩, htc⟩ := ((h3.and h4).and self_mem_nhdsWithin).exists
  have := hneg t ⟨ht4.le, le_trans (le_of_lt htc) hcS.1.2⟩ htc
  linarith

/-! ### (h) -/

/-- **Exercise 17.F.16(h)** (MWG, p. 647). Let `z` be the excess demand of an `(N + 1)`-good
economy (homogeneous, Walras' law) with the gross substitute property, and `g(p̂) = ẑ(p̂, 1)`.
At a normalized equilibrium where `z` is differentiable with positive cross effects
`∂zₖ/∂p_{N+1} > 0`, `Dg(p̂) p̂ ≪ 0` (the negative dominant diagonal of (g), weights `p̂ ≫ 0`); and
the normalized equilibrium is unique (Proposition 17.F.3). -/
theorem exercise_17_F_16h {z : (Fin (N + 1) → ℝ) → Fin (N + 1) → ℝ} (hH : EDHomogeneous z)
    (hGS : GrossSubstitute z) {q : Fin N → ℝ} (heq : IsNormEqm z q)
    {D : (Fin (N + 1) → ℝ) →L[ℝ] (Fin (N + 1) → ℝ)} (hd : HasFDerivAt z D (normPrice q))
    (hcross : ∀ k, k ≠ Fin.last N → 0 < D (Pi.single (Fin.last N) 1) k) :
    (∀ i, ((truncCLM N).comp (D.comp (inclCLM N))) q i < 0) ∧
      ∀ q', IsNormEqm z q' → q' = q := by
  refine ⟨fun i => ?_, fun q' hq' => proposition_17_F_3_norm hH hGS hq' heq⟩
  have h0 := euler_fderiv hH heq.1 hd
  have hsplit : normPrice q = inclCLM N q + Pi.single (Fin.last N) 1 := by
    funext k
    refine Fin.lastCases ?_ (fun l => ?_) k
    · simp
    · simp [Fin.castSucc_ne_last]
  rw [hsplit, map_add] at h0
  have := congrFun h0 (Fin.castSucc i)
  simp only [Pi.add_apply, Pi.zero_apply] at this
  have hc := hcross (Fin.castSucc i) (Fin.castSucc_ne_last i)
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, truncCLM,
    ContinuousLinearMap.pi_apply, ContinuousLinearMap.proj_apply]
  linarith

end MWG.PositiveEquilibriumTheory
