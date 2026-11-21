/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGExternalitiesPublicGoods.Tools
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Multilateral externalities (MWG Section 11.D)

MWG, pp. 364-367. `J` firms generate the externality, `I` consumers experience it; firm `j`'s
derived profit is `πⱼ(hⱼ)` (here `pr j`) and consumer `i`'s derived utility is `φᵢ(h̃ᵢ)`, both with
strictly decreasing derivatives on `[0, ∞)` (MWG: `πⱼ'' < 0`, `φᵢ'' < 0`).

* (11.D.1): the unfettered equilibrium (`IsUnfetteredEq`); MWG prints `πⱼ(hⱼ*) ≤ 0` for
  `πⱼ'(hⱼ*) ≤ 0` (correction). Footnote 13: the distribution of a depletable externality across
  consumers is indeterminate (`footnote_13`).
* **Depletable externalities**: problem (11.D.2) and its first-order conditions (11.D.3)-(11.D.4)
  with multiplier `μ`, proved necessary and sufficient (`eq_11_D_3_4`); a competitive market for
  the externality is efficient and every optimum is a market equilibrium
  (`deplMarket_optimal`, `deplMarket_exists`).
* **Nondepletable externalities**: problem (11.D.5) and the first-order conditions (11.D.6)
  (`eq_11_D_6`); the unfettered level is excessive (`nondepl_excess`), quotas and the uniform tax
  `t_h = -∑ᵢ φᵢ'(∑ⱼ hⱼ°)` restore optimality (`nondepl_quota`, `nondepl_tax`); footnote 15.
* **Tradable externality permits** (small type, p. 367): with `h°` permits, the competitive
  permit price is `-∑ᵢ φᵢ'(h°)`, the firms use `hⱼ°`, and every permit-market equilibrium has
  this allocation (`permits_equilibrium`, `permits_unique`).
-/

namespace MWG.ExternalitiesPublicGoods

open MWG.CompetitiveMarkets Filter Topology

/-! ## Sums of updated vectors -/

/-- Changing coordinate `i` of `x` to `v` changes `∑ₖ gₖ(xₖ)` by `gᵢ(v) - gᵢ(xᵢ)`. -/
theorem sum_update_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (g : ι → ℝ → ℝ) (x : ι → ℝ)
    (i : ι) (v : ℝ) :
    ∑ k, g k (Function.update x i v k) = ∑ k, g k (x k) + (g i v - g i (x i)) := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ i), Function.update_self,
    Finset.sum_congr rfl fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]]
  ring

/-- The one-sided first-order condition along a direction: if moving `(a, b)` to
`(a + sa t, b + sb t)` for small `t > 0` never raises `f + g`, then `sa f'(a) + sb g'(b) ≤ 0`. -/
theorem dir_foc {f g f' g' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hg : ∀ x, HasDerivAt g (g' x) x) (a b sa sb : ℝ)
    (hloc : ∀ᶠ t in 𝓝[>] (0 : ℝ), f (a + sa * t) + g (b + sb * t) ≤ f a + g b) :
    sa * f' a + sb * g' b ≤ 0 := by
  have hlin : ∀ (c s : ℝ), HasDerivAt (fun t : ℝ => c + s * t) s 0 := fun c s => by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul s).const_add c
  have h1 : HasDerivAt (fun t => f (a + sa * t)) (f' a * sa) 0 := by
    have := (hf (a + sa * 0)).comp 0 (hlin a sa)
    rw [mul_zero, add_zero] at this
    exact this
  have h2 : HasDerivAt (fun t => g (b + sb * t)) (g' b * sb) 0 := by
    have := (hg (b + sb * 0)).comp 0 (hlin b sb)
    rw [mul_zero, add_zero] at this
    exact this
  have hG := (h1.add h2).hasDerivWithinAt (s := Set.Ici 0)
  have := foc_local_necessary hG (by simpa using hloc)
  linarith

/-! ## The model -/

/-- **The multilateral externality model** (MWG, p. 365): consumers `ι` with derived utilities
`φᵢ(h̃ᵢ)`, firms `κ` with derived profits `πⱼ(hⱼ)` (`pr j`). -/
structure Multilateral (ι κ : Type*) where
  /-- Consumer `i`'s derived utility from the externality she experiences. -/
  φ : ι → ℝ → ℝ
  /-- `φᵢ'`. -/
  dφ : ι → ℝ → ℝ
  /-- Firm `j`'s derived profit from the externality it generates. -/
  pr : κ → ℝ → ℝ
  /-- `πⱼ'`. -/
  dpr : κ → ℝ → ℝ
  hφ : ∀ i x, HasDerivAt (φ i) (dφ i x) x
  hpr : ∀ j x, HasDerivAt (pr j) (dpr j x) x
  antiφ : ∀ i, StrictAntiOn (dφ i) (Set.Ici 0)
  antipr : ∀ j, StrictAntiOn (dpr j) (Set.Ici 0)

namespace Multilateral

variable {ι κ : Type*} [Fintype ι] [Fintype κ] (M : Multilateral ι κ)

/-- **(11.D.1)** (MWG, p. 365). In an unfettered competitive equilibrium each firm maximizes
`πⱼ` on `ℝ₊`. -/
def IsUnfetteredEq (h : κ → ℝ) : Prop := ∀ j, 0 ≤ h j ∧ ∀ y, 0 ≤ y → M.pr j y ≤ M.pr j (h j)

omit [Fintype ι] [Fintype κ] in
/-- **(11.D.1)** (MWG, p. 365): `πⱼ'(hⱼ*) ≤ 0`, with equality if `hⱼ* > 0`. MWG prints
`πⱼ(hⱼ*) ≤ 0`; the condition is on the derivative (correction). -/
theorem eq_11_D_1 (h : κ → ℝ) : M.IsUnfetteredEq h ↔ ∀ j, IsFOCSol (M.dpr j) 0 (h j) :=
  forall_congr' fun j => kt_isMax_iff (M.hpr j) (M.antipr j).antitoneOn

omit [Fintype κ] in
/-- **Footnote 13** (MWG, p. 365). In the unfettered equilibrium with a depletable externality,
the firms are indifferent about who absorbs it: any distribution `h̃ ≥ 0` with
`∑ h̃ᵢ = ∑ hⱼ*` is consistent with equilibrium. Such distributions exist, and with two consumers
and a positive total they are not unique. -/
theorem footnote_13 (H : ℝ) (hH : 0 ≤ H) (i₁ i₂ : ι) (hne : i₁ ≠ i₂) :
    (∀ i₀ : ι, ∃ x : ι → ℝ, (∀ i, 0 ≤ x i) ∧ ∑ i, x i = H ∧ x i₀ = H) ∧
      (0 < H → ∃ x y : ι → ℝ, (∀ i, 0 ≤ x i) ∧ (∀ i, 0 ≤ y i) ∧ ∑ i, x i = H ∧
        ∑ i, y i = H ∧ x ≠ y) := by
  classical
  have hex : ∀ i₀ : ι, ∃ x : ι → ℝ, (∀ i, 0 ≤ x i) ∧ ∑ i, x i = H ∧ x i₀ = H := fun i₀ =>
    ⟨Pi.single i₀ H, fun i => by
      rcases eq_or_ne i i₀ with h | h
      · rw [h, Pi.single_eq_same]; exact hH
      · rw [Pi.single_eq_of_ne h], by simp, by simp⟩
  refine ⟨hex, fun hpos => ⟨Pi.single i₁ H, Pi.single i₂ H, ?_, ?_, by simp, by simp, ?_⟩⟩
  · intro i
    rcases eq_or_ne i i₁ with h | h
    · rw [h, Pi.single_eq_same]; exact hH
    · rw [Pi.single_eq_of_ne h]
  · intro i
    rcases eq_or_ne i i₂ with h | h
    · rw [h, Pi.single_eq_same]; exact hH
    · rw [Pi.single_eq_of_ne h]
  · intro heq
    have := congrFun heq i₁
    rw [Pi.single_eq_same, Pi.single_eq_of_ne hne] at this
    linarith

/-! ## Depletable externalities -/

/-- Feasibility in problem (11.D.2): nonnegative levels, and the externality generated equals the
externality absorbed. -/
def DeplFeas (x : ι → ℝ) (h : κ → ℝ) : Prop :=
  (∀ i, 0 ≤ x i) ∧ (∀ j, 0 ≤ h j) ∧ ∑ j, h j = ∑ i, x i

/-- The objective of (11.D.2): `∑ᵢ φᵢ(h̃ᵢ) + ∑ⱼ πⱼ(hⱼ)`. -/
def deplObj (x : ι → ℝ) (h : κ → ℝ) : ℝ := ∑ i, M.φ i (x i) + ∑ j, M.pr j (h j)

/-- **Problem (11.D.2)** (MWG, p. 366): `(h̃°, h°)` solves it. -/
def IsDeplOpt (x : ι → ℝ) (h : κ → ℝ) : Prop :=
  DeplFeas x h ∧ ∀ x' h', DeplFeas x' h' → M.deplObj x' h' ≤ M.deplObj x h

/-- **(11.D.3)-(11.D.4)** (MWG, p. 366) with multiplier `μ`: `φᵢ'(h̃ᵢ) ≤ μ` (equality if
`h̃ᵢ > 0`) and `μ ≤ -πⱼ'(hⱼ)` (equality if `hⱼ > 0`). -/
def DeplKKT (μ : ℝ) (x : ι → ℝ) (h : κ → ℝ) : Prop :=
  (∀ i, M.dφ i (x i) ≤ μ ∧ (0 < x i → M.dφ i (x i) = μ)) ∧
    ∀ j, μ ≤ -M.dpr j (h j) ∧ (0 < h j → μ = -M.dpr j (h j))

/-- Sufficiency of (11.D.3)-(11.D.4). -/
theorem deplKKT_sufficient {μ : ℝ} {x : ι → ℝ} {h : κ → ℝ} (hf : DeplFeas x h)
    (hk : M.DeplKKT μ x h) : M.IsDeplOpt x h := by
  refine ⟨hf, fun x' h' hf' => ?_⟩
  have hφ : ∀ i, M.φ i (x' i) ≤ M.φ i (x i) + μ * (x' i - x i) := fun i => by
    have ht := foc_tangent_le (fun z _ => (M.hφ i z).hasDerivWithinAt) (M.antiφ i).antitoneOn
      (hf.1 i) (hf'.1 i)
    rcases eq_or_lt_of_le (hf.1 i) with h0 | hpos
    · have : M.dφ i (x i) * (x' i - x i) ≤ μ * (x' i - x i) :=
        mul_le_mul_of_nonneg_right (hk.1 i).1 (by rw [← h0]; simpa using hf'.1 i)
      linarith
    · rw [(hk.1 i).2 hpos] at ht; exact ht
  have hpr : ∀ j, M.pr j (h' j) ≤ M.pr j (h j) - μ * (h' j - h j) := fun j => by
    have ht := foc_tangent_le (fun z _ => (M.hpr j z).hasDerivWithinAt) (M.antipr j).antitoneOn
      (hf.2.1 j) (hf'.2.1 j)
    rcases eq_or_lt_of_le (hf.2.1 j) with h0 | hpos
    · have : M.dpr j (h j) * (h' j - h j) ≤ -μ * (h' j - h j) :=
        mul_le_mul_of_nonneg_right (by linarith [(hk.2 j).1])
          (by rw [← h0]; simpa using hf'.2.1 j)
      linarith
    · have := (hk.2 j).2 hpos
      rw [show M.dpr j (h j) = -μ by linarith] at ht; linarith
  have s1 := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hφ i
  have s2 := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hpr j
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at s1 s2
  simp only [deplObj]
  have e1 : ∑ i, x' i = ∑ j, h' j := hf'.2.2.symm
  have e2 : ∑ i, x i = ∑ j, h j := hf.2.2.symm
  rw [e1, e2] at s1
  linarith

/-- Necessity of (11.D.3)-(11.D.4): at a solution of (11.D.2) a multiplier exists (at least one
consumer and one firm). -/
theorem deplKKT_necessary [Nonempty ι] [Nonempty κ]
    {x : ι → ℝ} {h : κ → ℝ} (ho : M.IsDeplOpt x h) : ∃ μ, M.DeplKKT μ x h := by
  classical
  obtain ⟨hf, hmax⟩ := ho
  -- (a) raising a consumer's and a firm's level together
  have pa : ∀ i j, M.dφ i (x i) + M.dpr j (h j) ≤ 0 := fun i j => by
    have := dir_foc (M.hφ i) (M.hpr j) (x i) (h j) 1 1 (eventually_nhdsWithin_of_forall
      fun t ht => by
        have hfeas : DeplFeas (Function.update x i (x i + 1 * t))
            (Function.update h j (h j + 1 * t)) := by
          refine ⟨fun k => ?_, fun k => ?_, ?_⟩
          · rcases eq_or_ne k i with hk | hk
            · rw [hk, Function.update_self]; linarith [hf.1 i, ht.out]
            · rw [Function.update_of_ne hk]; exact hf.1 k
          · rcases eq_or_ne k j with hk | hk
            · rw [hk, Function.update_self]; linarith [hf.2.1 j, ht.out]
            · rw [Function.update_of_ne hk]; exact hf.2.1 k
          · have a1 := sum_update_eq (fun _ y => y) h j (h j + 1 * t)
            have a2 := sum_update_eq (fun _ y => y) x i (x i + 1 * t)
            rw [a1, a2, hf.2.2]; ring
        have := hmax _ _ hfeas
        simp only [deplObj, sum_update_eq] at this
        linarith)
    linarith
  -- (a') lowering both when both are positive
  have pa' : ∀ i j, 0 < x i → 0 < h j → M.dφ i (x i) + M.dpr j (h j) = 0 := fun i j hi hj => by
    refine le_antisymm (pa i j) ?_
    have := dir_foc (M.hφ i) (M.hpr j) (x i) (h j) (-1) (-1) (by
      filter_upwards [Ioo_mem_nhdsGT (lt_min hi hj)] with t ht
      have hfeas : DeplFeas (Function.update x i (x i + -1 * t))
          (Function.update h j (h j + -1 * t)) := by
        refine ⟨fun k => ?_, fun k => ?_, ?_⟩
        · rcases eq_or_ne k i with hk | hk
          · rw [hk, Function.update_self]; linarith [ht.2, min_le_left (x i) (h j)]
          · rw [Function.update_of_ne hk]; exact hf.1 k
        · rcases eq_or_ne k j with hk | hk
          · rw [hk, Function.update_self]; linarith [ht.2, min_le_right (x i) (h j)]
          · rw [Function.update_of_ne hk]; exact hf.2.1 k
        · have a1 := sum_update_eq (fun _ y => y) h j (h j + -1 * t)
          have a2 := sum_update_eq (fun _ y => y) x i (x i + -1 * t)
          rw [a1, a2, hf.2.2]; ring
      have := hmax _ _ hfeas
      simp only [deplObj, sum_update_eq] at this
      linarith)
    linarith
  -- (b) moving absorption from consumer `i'` (with `x i' > 0`) to consumer `i`
  have pb : ∀ i i', i ≠ i' → 0 < x i' → M.dφ i (x i) ≤ M.dφ i' (x i') := fun i i' hii' hi' => by
    have := dir_foc (M.hφ i) (M.hφ i') (x i) (x i') 1 (-1) (by
      filter_upwards [Ioo_mem_nhdsGT hi'] with t ht
      set x₁ := Function.update x i (x i + 1 * t) with hx₁d
      have hx₁ : x₁ i' = x i' := Function.update_of_ne hii'.symm _ _
      have hfeas : DeplFeas (Function.update x₁ i' (x i' + -1 * t)) h := by
        refine ⟨fun k => ?_, hf.2.1, ?_⟩
        · rcases eq_or_ne k i' with hk | hk
          · rw [hk, Function.update_self]; linarith [ht.2]
          · rw [Function.update_of_ne hk]
            rcases eq_or_ne k i with hk' | hk'
            · rw [hx₁d, hk', Function.update_self]; linarith [hf.1 i, ht.1]
            · rw [hx₁d, Function.update_of_ne hk']; exact hf.1 k
        · have a1 := sum_update_eq (fun _ y => y) x₁ i' (x i' + -1 * t)
          have a2 := sum_update_eq (fun _ y => y) x i (x i + 1 * t)
          rw [a1, a2, hx₁, hf.2.2]; ring
      have := hmax _ _ hfeas
      simp only [deplObj, sum_update_eq, hx₁, x₁] at this
      linarith)
    linarith
  -- (c) moving generation from firm `j` (with `h j > 0`) to firm `j'`
  have pc : ∀ j j', j ≠ j' → 0 < h j → M.dpr j' (h j') ≤ M.dpr j (h j) := fun j j' hjj' hj => by
    have := dir_foc (M.hpr j') (M.hpr j) (h j') (h j) 1 (-1) (by
      filter_upwards [Ioo_mem_nhdsGT hj] with t ht
      set h₁ := Function.update h j' (h j' + 1 * t) with hh₁d
      have hh₁ : h₁ j = h j := Function.update_of_ne hjj' _ _
      have hfeas : DeplFeas x (Function.update h₁ j (h j + -1 * t)) := by
        refine ⟨hf.1, fun k => ?_, ?_⟩
        · rcases eq_or_ne k j with hk | hk
          · rw [hk, Function.update_self]; linarith [ht.2]
          · rw [Function.update_of_ne hk]
            rcases eq_or_ne k j' with hk' | hk'
            · rw [hh₁d, hk', Function.update_self]; linarith [hf.2.1 j', ht.1]
            · rw [hh₁d, Function.update_of_ne hk']; exact hf.2.1 k
        · have a1 := sum_update_eq (fun _ y => y) h₁ j (h j + -1 * t)
          have a2 := sum_update_eq (fun _ y => y) h j' (h j' + 1 * t)
          rw [a1, a2, hh₁, ← hf.2.2]; ring
      have := hmax _ _ hfeas
      simp only [deplObj, sum_update_eq, hh₁, h₁] at this
      linarith)
    linarith
  by_cases hpos : ∃ j₀, 0 < h j₀
  · obtain ⟨j₀, hj₀⟩ := hpos
    have hsum : 0 < ∑ i, x i := by
      rw [← hf.2.2]
      exact lt_of_lt_of_le hj₀ (Finset.single_le_sum (fun k _ => hf.2.1 k) (Finset.mem_univ j₀))
    obtain ⟨i₀, hi₀⟩ : ∃ i, 0 < x i := by
      by_contra hno
      push Not at hno
      linarith [Finset.sum_nonpos fun i (_ : i ∈ Finset.univ) => hno i]
    refine ⟨-M.dpr j₀ (h j₀), fun i => ?_, fun j => ?_⟩
    · have e0 := pa' i₀ j₀ hi₀ hj₀
      rcases eq_or_ne i i₀ with hii | hii
      · subst hii; exact ⟨by linarith, fun _ => by linarith⟩
      · exact ⟨by linarith [pb i i₀ hii hi₀], fun hi => by
          linarith [pb i i₀ hii hi₀, pb i₀ i (Ne.symm hii) hi]⟩
    · rcases eq_or_ne j j₀ with hjj | hjj
      · subst hjj; exact ⟨le_rfl, fun _ => rfl⟩
      · exact ⟨by linarith [pc j₀ j (Ne.symm hjj) hj₀], fun hj => by
          linarith [pc j₀ j (Ne.symm hjj) hj₀, pc j j₀ hjj hj]⟩
  · push Not at hpos
    have hz : ∀ j, h j = 0 := fun j => le_antisymm (hpos j) (hf.2.1 j)
    have hxz : ∀ i, x i = 0 := by
      have hs : ∑ i, x i = 0 := by rw [← hf.2.2]; simp [hz]
      exact fun i => (Finset.sum_eq_zero_iff_of_nonneg fun k _ => hf.1 k).1 hs i
        (Finset.mem_univ i)
    refine ⟨Finset.univ.sup' Finset.univ_nonempty fun i => M.dφ i (x i), fun i => ⟨?_, ?_⟩,
      fun j => ⟨?_, ?_⟩⟩
    · exact Finset.le_sup' (fun i => M.dφ i (x i)) (Finset.mem_univ i)
    · intro hi; rw [hxz i] at hi; exact absurd hi (lt_irrefl 0)
    · rw [Finset.sup'_le_iff]
      intro i _
      linarith [pa i j]
    · intro hj; rw [hz j] at hj; exact absurd hj (lt_irrefl 0)

/-- **(11.D.3)-(11.D.4)** (MWG, p. 366): for a feasible `(h̃, h)`, it solves (11.D.2) iff a
multiplier `μ` satisfies the first-order conditions. -/
theorem eq_11_D_3_4 [Nonempty ι] [Nonempty κ] {x : ι → ℝ} {h : κ → ℝ}
    (hf : DeplFeas x h) : M.IsDeplOpt x h ↔ ∃ μ, M.DeplKKT μ x h := by
  classical
  exact ⟨M.deplKKT_necessary, fun ⟨_, hk⟩ => M.deplKKT_sufficient hf hk⟩

/-- A competitive equilibrium of a market for the depletable externality (MWG, p. 366), with the
consumers holding the property rights: at price `p` each consumer sells `h̃ᵢ` maximizing
`φᵢ(h̃ᵢ) + p h̃ᵢ`, each firm buys `hⱼ` maximizing `πⱼ(hⱼ) - p hⱼ`, and the market clears. -/
def IsDeplMarketEq (p : ℝ) (x : ι → ℝ) (h : κ → ℝ) : Prop :=
  (∀ i, 0 ≤ x i ∧ ∀ y, 0 ≤ y → M.φ i y + p * y ≤ M.φ i (x i) + p * x i) ∧
    (∀ j, 0 ≤ h j ∧ ∀ y, 0 ≤ y → M.pr j y - p * y ≤ M.pr j (h j) - p * h j) ∧
    ∑ j, h j = ∑ i, x i

omit [Fintype ι] [Fintype κ] in
theorem consumer_sell_iff (i : ι) (p xi : ℝ) :
    (0 ≤ xi ∧ ∀ y, 0 ≤ y → M.φ i y + p * y ≤ M.φ i xi + p * xi) ↔
      0 ≤ xi ∧ M.dφ i xi ≤ -p ∧ (0 < xi → M.dφ i xi = -p) := by
  have hf : ∀ y, HasDerivAt (fun y => M.φ i y + p * y) (M.dφ i y + p) y := fun y => by
    have h2 : HasDerivAt (fun y => p * y) p y := by simpa using (hasDerivAt_id y).const_mul p
    exact (M.hφ i y).add h2
  have hanti : AntitoneOn (fun y => M.dφ i y + p) (Set.Ici 0) :=
    fun a ha b hb hab => by simpa using (M.antiφ i).antitoneOn ha hb hab
  rw [kt_isMax_iff hf hanti]
  simp only [IsFOCSol]
  constructor
  · rintro ⟨h0, h1, h2⟩
    exact ⟨h0, by linarith, fun hp => by linarith [h2 hp]⟩
  · rintro ⟨h0, h1, h2⟩
    exact ⟨h0, by linarith, fun hp => by linarith [h2 hp]⟩

omit [Fintype ι] [Fintype κ] in
theorem firm_buy_iff (j : κ) (p hj : ℝ) :
    (0 ≤ hj ∧ ∀ y, 0 ≤ y → M.pr j y - p * y ≤ M.pr j hj - p * hj) ↔ IsFOCSol (M.dpr j) p hj := by
  have hf : ∀ y, HasDerivAt (fun y => M.pr j y - p * y) (M.dpr j y - p) y := fun y => by
    have h2 : HasDerivAt (fun y => p * y) p y := by simpa using (hasDerivAt_id y).const_mul p
    exact (M.hpr j y).sub h2
  have hanti : AntitoneOn (fun y => M.dpr j y - p) (Set.Ici 0) :=
    fun a ha b hb hab => by simpa using (M.antipr j).antitoneOn ha hb hab
  rw [kt_isMax_iff hf hanti]
  simp only [IsFOCSol]
  constructor
  · rintro ⟨h0, h1, h2⟩
    exact ⟨h0, by linarith, fun hp => by linarith [h2 hp]⟩
  · rintro ⟨h0, h1, h2⟩
    exact ⟨h0, by linarith, fun hp => by linarith [h2 hp]⟩

/-- **The market for a depletable externality is efficient** (MWG, p. 366): a market equilibrium
satisfies (11.D.3)-(11.D.4) with `μ = -p`... in the sign convention where consumers are paid `p`
per unit absorbed, the multiplier is `μ = -p`. -/
theorem deplMarket_optimal {p : ℝ} {x : ι → ℝ} {h : κ → ℝ} (he : M.IsDeplMarketEq p x h) :
    M.IsDeplOpt x h := by
  have hc := fun i => (M.consumer_sell_iff i p (x i)).1 (he.1 i)
  have hfm := fun j => (M.firm_buy_iff j p (h j)).1 (he.2.1 j)
  refine M.deplKKT_sufficient (μ := -p) ⟨fun i => (hc i).1, fun j => (hfm j).1, he.2.2⟩
    ⟨fun i => ⟨(hc i).2.1, (hc i).2.2⟩, fun j => ⟨?_, fun hj => ?_⟩⟩
  · linarith [(hfm j).2.1]
  · linarith [(hfm j).2.2 hj]

/-- **Every optimum is a market equilibrium** (second welfare theorem for the externality
market): at a solution of (11.D.2), the price `p = -μ` clears the market. -/
theorem deplMarket_exists [Nonempty ι] [Nonempty κ] {x : ι → ℝ} {h : κ → ℝ}
    (ho : M.IsDeplOpt x h) : ∃ p, M.IsDeplMarketEq p x h := by
  classical
  obtain ⟨μ, hk⟩ := M.deplKKT_necessary ho
  refine ⟨-μ, fun i => (M.consumer_sell_iff i _ _).2 ⟨ho.1.1 i, ?_, fun hi => ?_⟩,
    fun j => (M.firm_buy_iff j _ _).2 ⟨ho.1.2.1 j, ?_, fun hj => ?_⟩, ho.1.2.2⟩
  · simpa using (hk.1 i).1
  · simpa using (hk.1 i).2 hi
  · linarith [(hk.2 j).1]
  · linarith [(hk.2 j).2 hj]

/-! ## Nondepletable externalities -/

/-- The objective of (11.D.5): `∑ᵢ φᵢ(∑ⱼ hⱼ) + ∑ⱼ πⱼ(hⱼ)`. -/
def nondeplObj (h : κ → ℝ) : ℝ := ∑ i, M.φ i (∑ j, h j) + ∑ j, M.pr j (h j)

/-- **Problem (11.D.5)** (MWG, p. 366). -/
def IsNondeplOpt (h : κ → ℝ) : Prop :=
  (∀ j, 0 ≤ h j) ∧ ∀ h' : κ → ℝ, (∀ j, 0 ≤ h' j) → M.nondeplObj h' ≤ M.nondeplObj h

/-- The first-order conditions (11.D.6): `∑ᵢ φᵢ'(∑ₖ hₖ) ≤ -πⱼ'(hⱼ)`, equality if `hⱼ > 0`. -/
def NondeplFOC (h : κ → ℝ) : Prop :=
  ∀ j, 0 ≤ h j ∧ ∑ i, M.dφ i (∑ k, h k) ≤ -M.dpr j (h j) ∧
    (0 < h j → ∑ i, M.dφ i (∑ k, h k) = -M.dpr j (h j))

/-- **(11.D.6)** (MWG, p. 366): the first-order conditions are necessary and sufficient for
(11.D.5). -/
theorem eq_11_D_6 (h : κ → ℝ) : M.IsNondeplOpt h ↔ M.NondeplFOC h := by
  classical
  constructor
  · rintro ⟨h0, hmax⟩ j
    set R := ∑ k, h k - h j with hR
    have hR0 : 0 ≤ R := by
      have := Finset.single_le_sum (fun k _ => h0 k) (Finset.mem_univ j)
      linarith
    have hf : ∀ y, HasDerivAt (fun y => ∑ i, M.φ i (y + R) + M.pr j y)
        (∑ i, M.dφ i (y + R) + M.dpr j y) y := fun y =>
      (HasDerivAt.fun_sum fun i _ => (M.hφ i (y + R)).comp_add_const y R).add (M.hpr j y)
    have hmax' : ∀ y, 0 ≤ y →
        ∑ i, M.φ i (y + R) + M.pr j y ≤ ∑ i, M.φ i (h j + R) + M.pr j (h j) := fun y hy => by
      have := hmax (Function.update h j y) (fun k => by
        rcases eq_or_ne k j with hk | hk
        · rw [hk, Function.update_self]; exact hy
        · rw [Function.update_of_ne hk]; exact h0 k)
      have a1 := sum_update_eq (fun _ y => y) h j y
      simp only [nondeplObj, a1, sum_update_eq] at this
      have e1 : ∑ k, h k + (y - h j) = y + R := by rw [hR]; ring
      have e2 : h j + R = ∑ k, h k := by rw [hR]; ring
      rw [e1] at this
      rw [e2]
      linarith
    have := foc_max_necessary (hf (h j)).hasDerivWithinAt (h0 j) hmax'
    have e2 : h j + R = ∑ k, h k := by rw [hR]; ring
    rw [e2] at this
    exact ⟨h0 j, by linarith [this.1], fun hp => by linarith [this.2 hp]⟩
  · intro hfoc
    refine ⟨fun j => (hfoc j).1, fun h' h0' => ?_⟩
    set H := ∑ k, h k
    set H' := ∑ k, h' k
    have hH : 0 ≤ H := Finset.sum_nonneg fun k _ => (hfoc k).1
    have hH' : 0 ≤ H' := Finset.sum_nonneg fun k _ => h0' k
    have t1 : ∀ i, M.φ i H' ≤ M.φ i H + M.dφ i H * (H' - H) := fun i =>
      foc_tangent_le (fun z _ => (M.hφ i z).hasDerivWithinAt) (M.antiφ i).antitoneOn hH hH'
    have t2 : ∀ j, M.pr j (h' j) ≤ M.pr j (h j) + M.dpr j (h j) * (h' j - h j) := fun j =>
      foc_tangent_le (fun z _ => (M.hpr j z).hasDerivWithinAt) (M.antipr j).antitoneOn
        (hfoc j).1 (h0' j)
    have t3 : ∀ j, (∑ i, M.dφ i H + M.dpr j (h j)) * (h' j - h j) ≤ 0 := fun j => by
      rcases eq_or_lt_of_le (hfoc j).1 with hz | hp
      · have hj2 := (hfoc j).2.1
        rw [← hz] at hj2
        rw [← hz, sub_zero]
        exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (h0' j)
      · rw [show ∑ i, M.dφ i H + M.dpr j (h j) = 0 by linarith [(hfoc j).2.2 hp], zero_mul]
    have s1 := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => t1 i
    have s2 := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => t2 j
    have s3 := Finset.sum_nonpos fun j (_ : j ∈ Finset.univ) => t3 j
    simp only [Finset.sum_add_distrib, ← Finset.sum_mul] at s1
    simp only [add_mul, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib] at s3
    simp only [Finset.sum_add_distrib] at s2
    simp only [nondeplObj]
    have eH : ∑ j, h' j - ∑ j, h j = H' - H := rfl
    rw [eH] at s3
    linarith

/-- **The unfettered level is excessive** (MWG, p. 367). With a negative externality
(`φᵢ' < 0`, at least one consumer), each firm's optimal level is at most its unfettered
equilibrium level, strictly so when the latter is positive. -/
theorem nondepl_excess [Nonempty ι] (hneg : ∀ i y, 0 ≤ y → M.dφ i y < 0) {hs ho : κ → ℝ}
    (he : M.IsUnfetteredEq hs) (hopt : M.IsNondeplOpt ho) (j : κ) :
    ho j ≤ hs j ∧ (0 < hs j → ho j < hs j) := by
  rw [eq_11_D_1] at he
  rw [eq_11_D_6] at hopt
  have hH : 0 ≤ ∑ k, ho k := Finset.sum_nonneg fun k _ => (hopt k).1
  have hD : ∑ i, M.dφ i (∑ k, ho k) < 0 := by
    obtain ⟨i₀⟩ := ‹Nonempty ι›
    exact Finset.sum_neg (fun i _ => hneg i _ hH) ⟨i₀, Finset.mem_univ _⟩
  have key : ¬ hs j < ho j := fun hlt => by
    have e2 := (hopt j).2.2 ((he j).1.trans_lt hlt)
    have := M.antipr j (he j).1 (hopt j).1 hlt
    linarith [(he j).2.1]
  refine ⟨not_lt.1 key, fun hp => lt_of_le_of_ne (not_lt.1 key) fun heq => ?_⟩
  have e1 := (he j).2.2 hp
  have e2 := (hopt j).2.2 (heq ▸ hp)
  rw [heq] at e2
  linarith

/-- **Quotas** (MWG, p. 367): with the bound `hⱼ ≤ hⱼ°` and `hⱼ° ≤ hⱼ*`, firm `j`'s unique best
choice in `[0, hⱼ°]` is `hⱼ°`. -/
theorem nondepl_quota {hs ho : κ → ℝ} (he : M.IsUnfetteredEq hs) (hopt : M.IsNondeplOpt ho)
    (j : κ) (hle : ho j ≤ hs j) :
    ∀ y, 0 ≤ y → y ≤ ho j → y ≠ ho j → M.pr j y < M.pr j (ho j) := by
  rw [eq_11_D_1] at he
  intro y hy hyo hne
  exact kt_strictMonoOn (M.hpr j) (M.antipr j) (he j) ⟨hy, hyo.trans hle⟩ ⟨hopt.1 j, hle⟩
    (lt_of_le_of_ne hyo hne)

/-- Firm `j`'s choice under a per-unit tax `t`: `max_{hⱼ ≥ 0} πⱼ(hⱼ) - t hⱼ`. -/
def IsFirmTaxChoice (j : κ) (t y : ℝ) : Prop :=
  0 ≤ y ∧ ∀ z, 0 ≤ z → M.pr j z - t * z ≤ M.pr j y - t * y

/-- **The optimal uniform tax** (MWG, p. 367): `t_h = -∑ᵢ φᵢ'(∑ⱼ hⱼ°)` leads every firm to choose
exactly `hⱼ°` (its first-order condition `πⱼ'(hⱼ) ≤ t_h`, equality if `hⱼ > 0`). -/
theorem nondepl_tax {ho : κ → ℝ} (hopt : M.IsNondeplOpt ho) (j : κ) (y : ℝ) :
    M.IsFirmTaxChoice j (-∑ i, M.dφ i (∑ k, ho k)) y ↔ y = ho j := by
  rw [eq_11_D_6] at hopt
  rw [IsFirmTaxChoice, firm_buy_iff]
  have hj : IsFOCSol (M.dpr j) (-∑ i, M.dφ i (∑ k, ho k)) (ho j) :=
    ⟨(hopt j).1, by linarith [(hopt j).2.1], fun hp => by linarith [(hopt j).2.2 hp]⟩
  exact ⟨fun hy => isFOCSol_unique (M.antipr j) hy hj, fun hy => hy ▸ hj⟩

/-- **Footnote 15** (MWG, p. 367). With `J` firms producing a public good at costs `cⱼ(qⱼ)`
(`πⱼ = -cⱼ`), the optimality conditions take the form (11.D.6) with `cⱼ'(qⱼ°)` in place of
`-πⱼ'(hⱼ°)`. -/
theorem footnote_15 (h : κ → ℝ) :
    M.IsNondeplOpt h ↔ ∀ j, 0 ≤ h j ∧ ∑ i, M.dφ i (∑ k, h k) ≤ -M.dpr j (h j) ∧
      (0 < h j → ∑ i, M.dφ i (∑ k, h k) = -M.dpr j (h j)) :=
  M.eq_11_D_6 h

/-! ## Tradable externality permits -/

/-- A competitive equilibrium of the permit market (MWG, small type, p. 367): firm `j` holds
`h̄ⱼ` permits, buys or sells at price `p`, and uses `hⱼ` maximizing `πⱼ(hⱼ) + p(h̄ⱼ - hⱼ)`; the
market clears, `∑ hⱼ = ∑ h̄ⱼ`. -/
def IsPermitEq (hbar : κ → ℝ) (p : ℝ) (h : κ → ℝ) : Prop :=
  (∀ j, 0 ≤ h j ∧ ∀ z, 0 ≤ z → M.pr j z + p * (hbar j - z) ≤ M.pr j (h j) + p * (hbar j - h j)) ∧
    ∑ j, h j = ∑ j, hbar j

omit [Fintype ι] [Fintype κ] in
theorem permit_demand_iff (hbar : ℝ) (j : κ) (p y : ℝ) :
    (0 ≤ y ∧ ∀ z, 0 ≤ z → M.pr j z + p * (hbar - z) ≤ M.pr j y + p * (hbar - y)) ↔
      M.IsFirmTaxChoice j p y := by
  constructor
  · rintro ⟨h0, h1⟩
    exact ⟨h0, fun z hz => by linarith [h1 z hz]⟩
  · rintro ⟨h0, h1⟩
    exact ⟨h0, fun z hz => by linarith [h1 z hz]⟩

/-- **Permits implement the optimum** (MWG, p. 367): if `h° = ∑ hⱼ°` permits are distributed in
any way, the price `p* = -∑ᵢ φᵢ'(h°)` with each firm using `hⱼ°` is an equilibrium. -/
theorem permits_equilibrium {ho hbar : κ → ℝ} (hopt : M.IsNondeplOpt ho)
    (hsum : ∑ j, hbar j = ∑ j, ho j) :
    M.IsPermitEq hbar (-∑ i, M.dφ i (∑ k, ho k)) ho :=
  ⟨fun j => (M.permit_demand_iff (hbar j) j _ _).2 ((M.nondepl_tax hopt j (ho j)).2 rfl),
    hsum.symm⟩

/-- **Every permit equilibrium is optimal** (MWG, p. 367): with `∑ h̄ⱼ = h°`, any equilibrium
allocation is `h°` (firms' permit demands are decreasing in the price). -/
theorem permits_unique {ho hbar : κ → ℝ} (hopt : M.IsNondeplOpt ho)
    (hsum : ∑ j, hbar j = ∑ j, ho j) {p : ℝ} {h : κ → ℝ} (he : M.IsPermitEq hbar p h) :
    h = ho := by
  set ps := -∑ i, M.dφ i (∑ k, ho k)
  have hch : ∀ j, M.IsFirmTaxChoice j p (h j) := fun j =>
    (M.permit_demand_iff (hbar j) j p (h j)).1 (he.1 j)
  have hcho : ∀ j, M.IsFirmTaxChoice j ps (ho j) := fun j => (M.nondepl_tax hopt j _).2 rfl
  have rp : ∀ j, (ps - p) * (h j - ho j) ≥ 0 := fun j => by
    have a := (hch j).2 (ho j) (hcho j).1
    have b := (hcho j).2 (h j) (hch j).1
    nlinarith
  have hsum' : ∑ j, h j = ∑ j, ho j := he.2.trans hsum
  rcases lt_trichotomy p ps with hlt | heq | hgt
  · have hle : ∀ j, ho j ≤ h j := fun j => by
      have := rp j
      by_contra hc
      push Not at hc
      nlinarith
    funext j
    exact ((Finset.sum_eq_sum_iff_of_le fun k _ => hle k).1 hsum'.symm j
      (Finset.mem_univ j)).symm
  · funext j
    have h' := hch j
    rw [heq] at h'
    exact (M.nondepl_tax hopt j (h j)).1 h'
  · have hle : ∀ j, h j ≤ ho j := fun j => by
      have := rp j
      by_contra hc
      push Not at hc
      nlinarith
    funext j
    exact (Finset.sum_eq_sum_iff_of_le fun k _ => hle k).1 hsum' j (Finset.mem_univ j)

end Multilateral

/-! ## A concrete instance -/

/-- Two consumers with `φᵢ(h) = -h - h²/2` and two firms with `πⱼ(h) = aⱼ h - h²/2`,
`a = (4, 6)`. -/
noncomputable def mlEx : Multilateral (Fin 2) (Fin 2) where
  φ _ h := -h - h ^ 2 / 2
  dφ _ h := -1 - h
  pr j h := (if j = 0 then 4 else 6) * h - h ^ 2 / 2
  dpr j h := (if j = 0 then 4 else 6) - h
  hφ _ h := by
    have h' := (hasDerivAt_id h).neg.sub ((hasDerivAt_pow 2 h).div_const 2)
    exact (h'.congr_deriv (by simp only [Nat.cast_ofNat]; ring) :
      HasDerivAt (fun h : ℝ => -h - h ^ 2 / 2) (-1 - h) h)
  hpr j h := by
    have h' := ((hasDerivAt_id h).const_mul (if j = 0 then (4 : ℝ) else 6)).sub
      ((hasDerivAt_pow 2 h).div_const 2)
    exact (h'.congr_deriv (by simp only [Nat.cast_ofNat]; ring) :
      HasDerivAt (fun h : ℝ => (if j = 0 then (4 : ℝ) else 6) * h - h ^ 2 / 2)
        ((if j = 0 then (4 : ℝ) else 6) - h) h)
  antiφ _ _ _ _ _ hab := by simp only; linarith
  antipr _ _ _ _ _ hab := by simp only; linarith

/-- In the instance, the nondepletable optimum is the corner `h° = (0, 4/3)` (the uniform tax is
`-∑ᵢ φᵢ'(4/3) = 14/3`), and the unfettered equilibrium is `(4, 6)`. -/
theorem mlEx_values :
    mlEx.IsNondeplOpt ![0, 4 / 3] ∧ mlEx.IsUnfetteredEq ![4, 6] := by
  constructor
  · rw [Multilateral.eq_11_D_6]
    intro j
    fin_cases j <;> norm_num [mlEx, Fin.sum_univ_two]
  · rw [Multilateral.eq_11_D_1]
    intro j
    fin_cases j <;> norm_num [mlEx, IsFOCSol]

end MWG.ExternalitiesPublicGoods
