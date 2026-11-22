/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPositiveEquilibriumTheory.Exercises17BB

/-!
# Exercise 17.BB.3: at least one price is positive (MWG, p. 650)

Without free disposal prices may be negative. Exercise 17.BB.3 asks to show that at an
equilibrium (of an Edgeworth box with continuous, strictly convex, locally nonsatiated
preferences) at least one price is positive. We prove the consumer-level statement for any
number of goods: on `ℝ^L₊`, with rational, continuous, locally nonsatiated and strictly convex
preferences, there is no preference maximizing bundle in the budget set at any `p ≤ 0`,
`p ≠ 0` (`exercise_17_BB_3_no_demand`). Let `x` be maximal and `U = {z ∈ ℝ^L₊ : z ≿ x}`.

1. every `z ∈ U` has `p·z ≥ w` (local nonsatiation);
2. `x` is the only point of `U` in the budget set (strict convexity);
3. `U` is bounded: otherwise (`U` closed and convex) it contains a ray `x + t d`, `d ≠ 0`;
   staying in `ℝ^L₊` forces `d ≥ 0`, so `p·d ≤ 0` and `x + d` is in the budget set,
   contradicting 2;
4. so `U` is compact, `≿` has a maximal element on it, which is a global maximum, contradicting
   local nonsatiation.

Hence some price is positive at every Walrasian equilibrium (`exercise_17_BB_3_pos_price`).
-/

namespace MWG.PositiveEquilibriumTheory

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.Production MWG.WelfareTheorems
open Kreps.PreferenceProperties
open MWG.CompetitiveMarkets (Allocation)
open Filter Topology

variable {L : ℕ}

/-- Strictly convex rational preferences have convex upper contour sets. -/
theorem bb_convex_upper_of_strict {X : Set (Fin L → ℝ)} {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hX : Convex ℝ X) (hsc : PrefStrictlyConvex X r) {x : Fin L → ℝ} (hx : x ∈ X) :
    Convex ℝ (upperContour X r x) := by
  intro y hy z hz a b ha hb hab
  refine ⟨hX hy.1 hz.1 ha hb hab, ?_⟩
  rcases eq_or_ne y z with rfl | hne
  · rw [← add_smul, hab, one_smul]
    exact hy.2
  rcases ha.lt_or_eq with ha' | ha'
  · rcases hb.lt_or_eq with hb' | hb'
    · have := hsc x hx y hy.1 z hz.1 hy.2 hz.2 hne a ha' (by linarith)
      rw [show 1 - a = b by linarith] at this
      exact this.1
    · subst hb'
      rw [show a = 1 by linarith, one_smul, zero_smul, add_zero]
      exact hy.2
  · subst ha'
    rw [show b = 1 by linarith, one_smul, zero_smul, zero_add]
    exact hz.2

/-- **Exercise 17.BB.3** (MWG, p. 650), "at least one price must be positive", at the level of a
consumer: on `ℝ^L₊`, with rational, continuous, locally nonsatiated and strictly convex
preferences, no bundle is preference maximizing in the budget set at prices `p ≤ 0`
(including `p = 0`), whatever the wealth. -/
theorem exercise_17_BB_3_no_demand {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop}
    (hr : RationalOn (nonnegOrthant L) r) (hc : PrefContinuous (nonnegOrthant L) r)
    (hlns : LocallyNonsatiated (nonnegOrthant L) r)
    (hsc : PrefStrictlyConvex (nonnegOrthant L) r) {p : Fin L → ℝ} (hp : ∀ l, p l ≤ 0)
    (w : ℝ) : ¬ ∃ x, IsMaximalFor r (budgetSetOn (nonnegOrthant L) p w) x := by
  rintro ⟨x, ⟨hxX, hxb⟩, hmax⟩
  set U : Set (Fin L → ℝ) := upperContour (nonnegOrthant L) r x with hUdef
  have hxU : x ∈ U := ⟨hxX, bb_refl hr hxX⟩
  -- 1. every point of `U` costs at least `w`
  have hU : ∀ z ∈ U, w ≤ p ⬝ᵥ z := by
    intro z hz
    by_contra hlt
    push Not at hlt
    obtain ⟨z', hz'X, hz'c, hz's, -⟩ := bb_lns_near hlns p hz.1 hlt one_pos
    exact (bb_strict_trans hr hz'X hz.1 hxX hz's hz.2).2 (hmax z' ⟨hz'X, hz'c.le⟩)
  -- 2. `x` is the only point of `U` in the budget set
  have hU2 : ∀ z ∈ U, p ⬝ᵥ z ≤ w → z = x := by
    intro z hz hzw
    by_contra hne
    have hs := hsc x hxX z hz.1 x hxX hz.2 (bb_refl hr hxX) hne (1 / 2) (by norm_num)
      (by norm_num)
    have hm : (1 / 2 : ℝ) • z + (1 - 1 / 2 : ℝ) • x ∈ budgetSetOn (nonnegOrthant L) p w := by
      refine ⟨convex_nonnegOrthant L hz.1 hxX (by norm_num) (by norm_num) (by norm_num), ?_⟩
      have e : p ⬝ᵥ ((1 / 2 : ℝ) • z + (1 - 1 / 2 : ℝ) • x) =
          (1 / 2) * (p ⬝ᵥ z) + (1 - 1 / 2) * (p ⬝ᵥ x) := by
        rw [dotProduct_add, dotProduct_smul, dotProduct_smul]
        rfl
      rw [e]
      linarith
    exact hs.2 (hmax _ hm)
  have hUconv : Convex ℝ U := bb_convex_upper_of_strict (convex_nonnegOrthant L) hsc hxX
  have hUcl : IsClosed U := by
    refine IsSeqClosed.isClosed fun {zs} {z} hzs hlim => ?_
    have hzX : z ∈ nonnegOrthant L := isClosed_nonnegOrthant.mem_of_tendsto hlim
      (Eventually.of_forall fun n => (hzs n).1)
    exact ⟨hzX, hc zs (fun _ => x) z x (fun n => (hzs n).1) (fun _ => hxX) hzX hxX
      (fun n => (hzs n).2) hlim tendsto_const_nhds⟩
  -- 3. `U` is bounded
  have hUb : Bornology.IsBounded U := by
    by_contra hnb
    rw [Metric.isBounded_iff_subset_closedBall x] at hnb
    push Not at hnb
    have hex : ∀ n : ℕ, ∃ z ∈ U, (n : ℝ) + 1 < dist z x := by
      intro n
      obtain ⟨z, hzU, hz⟩ := Set.not_subset.mp (hnb ((n : ℝ) + 1))
      exact ⟨z, hzU, by simpa [Metric.mem_closedBall, not_le] using hz⟩
    choose zs hzsU hzsd using hex
    have hD : ∀ n, 0 < dist (zs n) x := fun n => by linarith [hzsd n, (n.cast_nonneg : (0 : ℝ) ≤ n)]
    set ds : ℕ → Fin L → ℝ := fun n => (dist (zs n) x)⁻¹ • (zs n - x) with hds
    have hdsS : ∀ n, ds n ∈ Metric.sphere (0 : Fin L → ℝ) 1 := fun n => by
      rw [mem_sphere_zero_iff_norm, hds, norm_smul, norm_inv, Real.norm_eq_abs,
        abs_of_pos (hD n), ← dist_eq_norm, inv_mul_cancel₀ (hD n).ne']
    obtain ⟨d, hdS, φ, hφ, hlim⟩ := (isCompact_sphere (0 : Fin L → ℝ) 1).tendsto_subseq hdsS
    have hd0 : d ≠ 0 := by
      intro h
      rw [h, mem_sphere_zero_iff_norm, norm_zero] at hdS
      exact zero_ne_one hdS
    -- the ray `x + t d` lies in `U`
    have hray : ∀ t : ℝ, 0 ≤ t → x + t • d ∈ U := by
      intro t ht
      have hl : Tendsto (fun n => x + t • ds (φ n)) atTop (𝓝 (x + t • d)) :=
        (hlim.const_smul t).const_add x
      refine hUcl.mem_of_tendsto hl ?_
      filter_upwards [eventually_ge_atTop (⌈t⌉₊)] with n hn
      have htn : t ≤ dist (zs (φ n)) x := by
        have h1 : t ≤ (⌈t⌉₊ : ℝ) := Nat.le_ceil t
        have h2 : ((⌈t⌉₊ : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        have h3 : (n : ℝ) ≤ (φ n : ℝ) := by exact_mod_cast hφ.id_le n
        linarith [hzsd (φ n)]
      have heq : x + t • ds (φ n) = x + (t / dist (zs (φ n)) x) • (zs (φ n) - x) := by
        simp only [hds, smul_smul]
        congr 2
      rw [heq]
      exact hUconv.add_smul_sub_mem hxU (hzsU (φ n))
        ⟨div_nonneg ht (hD _).le, (div_le_one (hD _)).mpr htn⟩
    -- `d ≥ 0`
    have hdnn : ∀ l, 0 ≤ d l := by
      intro l
      by_contra hneg
      push Not at hneg
      have hmem := (hray ((x l + 1) / (-d l)) (div_nonneg (by linarith [hxX l]) (by linarith))).1
      have := hmem l
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
      have hdl : d l ≠ 0 := hneg.ne
      have e : (x l + 1) / -d l * d l = -(x l + 1) := by field_simp
      linarith
    -- so `x + d` is in the budget set and in `U`, hence equals `x`
    have hpd : p ⬝ᵥ d ≤ 0 :=
      Finset.sum_nonpos fun l _ => mul_nonpos_of_nonpos_of_nonneg (hp l) (hdnn l)
    have h1 := hray 1 zero_le_one
    have := hU2 _ h1 (by rw [one_smul, dotProduct_add]; linarith)
    rw [one_smul, add_eq_left] at this
    exact hd0 this
  -- 4. a maximal element of `U` is a global maximum
  obtain ⟨m, hmU, hm⟩ := bb_exists_maximal hr hc (Metric.isCompact_of_isClosed_isBounded hUcl hUb)
    (fun z hz => hz.1) ⟨x, hxU⟩
  obtain ⟨z, hzX, -, hzs⟩ := hlns m hmU.1 1 one_pos
  exact hzs.2 (hm z ⟨hzX, hr.2 _ hzX _ hmU.1 _ hxX hzs.1 hmU.2⟩)

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **Exercise 17.BB.3** (MWG, p. 650). In an economy (at least one consumer) whose consumers
have `Xᵢ = ℝ^L₊` and rational, continuous, locally nonsatiated, strictly convex preferences,
at every Walrasian equilibrium at least one price is positive. -/
theorem exercise_17_BB_3_pos_price [Nonempty ι] {E : PrivPrefEconomy ι κ L}
    (hX : ∀ i, E.X i = nonnegOrthant L) (hr : ∀ i, RationalOn (E.X i) (E.pref i))
    (hc : ∀ i, PrefContinuous (E.X i) (E.pref i))
    (hlns : ∀ i, LocallyNonsatiated (E.X i) (E.pref i))
    (hsc : ∀ i, PrefStrictlyConvex (E.X i) (E.pref i)) {a : Allocation ι κ L}
    {p : Fin L → ℝ} (heq : E.IsWalrasEqm a p) : ∃ l, 0 < p l := by
  by_contra hall
  push Not at hall
  obtain ⟨i⟩ := (inferInstance : Nonempty ι)
  have h := heq.2.1 i
  have h1 := hr i
  have h2 := hc i
  have h3 := hlns i
  have h4 := hsc i
  rw [hX i] at h1 h2 h3 h4 h
  exact exercise_17_BB_3_no_demand h1 h2 h3 h4 hall _ ⟨_, h⟩

end MWG.PositiveEquilibriumTheory
