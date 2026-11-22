/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPositiveEquilibriumTheory.SMDDebreuBasic
import Mathlib.Topology.TietzeExtension
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The Sonnenschein-Mantel-Debreu theorem (MWG Proposition 17.E.3, pp. 602-606)

**Proposition 17.E.3** for any number `L` of goods (`proposition_17_E_3`): a function `z`
continuous on `P_ε`, homogeneous of degree zero and satisfying Walras' law is the aggregate
excess demand on `P_ε` of an exchange economy with `L` consumers (consumption sets `ℝ^L_+`,
endowments `≫ 0`, continuous, convex and strongly monotone preferences, single-valued demand on
`P_ε`). This is Debreu's (1974) proof, as sketched in small type on pp. 604-606:

* With `r` such that `αᵢ(p) = zᵢ(p) + r pᵢ ≥ 1` on the normalized prices `K` of `P_ε`,
  `z(p) = ∑ᵢ αᵢ(p) (eⁱ - pᵢ p)` (`debreu_decomposition`).
* Consumer `i` must have excess demand `αᵢ(p)(eⁱ - pᵢ p)`; the book appeals to the strong
  axiom (Exercises 17.E.6-17.E.7) and to "SA ⟹ rationalizable" (footnote 34). We construct the
  preferences directly with the rationalization lemma `smd_rationalize`: utility levels are
  `pᵢ` (lower is better; `p·zⁱ(p') ≤ 0` forces `pᵢ < p'ᵢ`, `debreuZ_revPref_lt`), and offer points
  of lower level are reached by rotating `p` towards the other axes (`debreuRho`), keeping
  `p_{-i}` bounded away from `0`. `αᵢ` is extended continuously from `K` by the Tietze extension
  theorem (values `≥ 1`).

**Footnote 30** (`footnote_17_30`): `L + k` consumers also suffice, adding `k` consumers with no
endowment.
-/

namespace MWG.PositiveEquilibriumTheory

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.GeneralEquilibriumExamples Filter Topology

variable {L : ℕ}

/-- The generator domain for consumer `i`: unit vectors `p ≥ 0` with `pₗ ≥ η` for `ℓ ≠ i`. -/
def debreuDom (i : Fin L) (η : ℝ) : Set (Fin L → ℝ) :=
  {p | (∀ l, 0 ≤ p l) ∧ p ⬝ᵥ p = 1 ∧ ∀ l, l ≠ i → η ≤ p l}

/-- Rotation of `p` towards the axes `ℓ ≠ i`, down to the level `pᵢ = min(pᵢ, max(c, 0))`. -/
noncomputable def debreuRho (i : Fin L) (c : ℝ) (p : Fin L → ℝ) : Fin L → ℝ :=
  min (p i) (max c 0) • Pi.single i 1 +
    Real.sqrt ((1 - min (p i) (max c 0) ^ 2) / (1 - p i ^ 2)) • (p - p i • Pi.single i 1)

theorem debreuRho_apply_self (i : Fin L) (c : ℝ) (p : Fin L → ℝ) :
    debreuRho i c p i = min (p i) (max c 0) := by
  simp [debreuRho]

theorem debreuRho_apply_ne {i l : Fin L} (h : l ≠ i) (c : ℝ) (p : Fin L → ℝ) :
    debreuRho i c p l = Real.sqrt ((1 - min (p i) (max c 0) ^ 2) / (1 - p i ^ 2)) * p l := by
  simp [debreuRho, h]

/-- On `debreuDom`, `1 - pᵢ² ≥ η²`. -/
theorem debreuDom_gap (hL : 1 < L) {i : Fin L} {η : ℝ} (hη : 0 < η) {p : Fin L → ℝ}
    (hp : p ∈ debreuDom i η) : η ^ 2 ≤ 1 - p i ^ 2 := by
  obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card (by simpa using hL) i
  have hsub : ({i, j} : Finset (Fin L)) ⊆ Finset.univ := Finset.subset_univ _
  have h2 := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (f := fun l => p l * p l) fun l _ _ => mul_self_nonneg _
  rw [Finset.sum_pair hj.symm] at h2
  have h1 : p ⬝ᵥ p = ∑ l, p l * p l := rfl
  have hpj := hp.2.2 j hj
  have : η * η ≤ p j * p j := mul_self_le_mul_self hη.le hpj
  nlinarith [hp.2.1]

/-- The rotation stays in `debreuDom` and lands at level `min(pᵢ, max(c, 0))`. -/
theorem debreuRho_mem (hL : 1 < L) {i : Fin L} {η : ℝ} (hη : 0 < η) {p : Fin L → ℝ}
    (hp : p ∈ debreuDom i η) (c : ℝ) : debreuRho i c p ∈ debreuDom i η := by
  have hgap := debreuDom_gap hL hη hp
  have hηsq : 0 < η ^ 2 := by positivity
  set m := min (p i) (max c 0) with hm
  have hm0 : 0 ≤ m := le_min (hp.1 i) (le_max_right _ _)
  have hmp : m ≤ p i := min_le_left _ _
  have hpi1 : p i ^ 2 < 1 := by linarith
  have hden : 0 < 1 - p i ^ 2 := by linarith
  have hm2 : m ^ 2 ≤ p i ^ 2 := pow_le_pow_left₀ hm0 hmp 2
  set s := Real.sqrt ((1 - m ^ 2) / (1 - p i ^ 2)) with hs
  have hs1 : 1 ≤ s := by
    rw [hs, Real.one_le_sqrt, one_le_div hden]
    linarith
  have hsq : s ^ 2 = (1 - m ^ 2) / (1 - p i ^ 2) :=
    Real.sq_sqrt (div_nonneg (by linarith) hden.le)
  refine ⟨fun l => ?_, ?_, fun l hl => ?_⟩
  · by_cases hl : l = i
    · subst hl; rw [debreuRho_apply_self]; exact hm0
    · rw [debreuRho_apply_ne hl]; exact mul_nonneg (by linarith) (hp.1 l)
  · have hq : debreuRho i c p = m • Pi.single i 1 + s • (p - p i • Pi.single i 1) := rfl
    have hv : (p - p i • Pi.single i 1) ⬝ᵥ (p - p i • Pi.single i 1) = 1 - p i ^ 2 := by
      simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
        dotProduct_single, single_dotProduct, hp.2.1, smul_eq_mul, Pi.sub_apply, Pi.smul_apply,
        Pi.single_eq_same, mul_one, sub_self, mul_zero]
      ring
    have hev : (Pi.single i (1 : ℝ) : Fin L → ℝ) ⬝ᵥ (p - p i • Pi.single i 1) = 0 := by
      simp [dotProduct_sub, single_dotProduct]
    rw [hq]
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      hv, hev, dotProduct_comm (p - p i • Pi.single i 1) (Pi.single i 1),
      single_dotProduct, Pi.single_eq_same]
    have hsq' : s ^ 2 * (1 - p i ^ 2) = 1 - m ^ 2 := by rw [hsq]; field_simp
    linear_combination hsq'
  · rw [debreuRho_apply_ne hl]
    have := hp.2.2 l hl
    nlinarith [hp.1 l]

/-- The rotation fixes `p` when `pᵢ ≤ c` and `c ≥ 0`. -/
theorem debreuRho_of_le {i : Fin L} {c : ℝ} {p : Fin L → ℝ} (hpc : p i ≤ c)
    (hden : 1 - p i ^ 2 ≠ 0) : debreuRho i c p = p := by
  have hm : min (p i) (max c 0) = p i := min_eq_left (hpc.trans (le_max_left _ _))
  simp only [debreuRho, hm, div_self hden, Real.sqrt_one, one_smul]
  abel

/-- Continuity of the rotation on `ℝ × debreuDom`. -/
theorem debreuRho_continuous (hL : 1 < L) {i : Fin L} {η : ℝ} (hη : 0 < η) :
    Continuous fun x : ℝ × debreuDom i η => debreuRho i x.1 x.2.1 := by
  have hpi : Continuous fun x : ℝ × debreuDom i η => x.2.1 i :=
    (continuous_apply i).comp (continuous_subtype_val.comp continuous_snd)
  have hm : Continuous fun x : ℝ × debreuDom i η => min (x.2.1 i) (max x.1 0) :=
    hpi.min (continuous_fst.max continuous_const)
  have hden : ∀ x : ℝ × debreuDom i η, 1 - x.2.1 i ^ 2 ≠ 0 := fun x => by
    have := debreuDom_gap hL hη x.2.2
    have : 0 < η ^ 2 := by positivity
    linarith
  unfold debreuRho
  refine (hm.smul continuous_const).add ?_
  refine (((continuous_const.sub (hm.pow 2)).div (continuous_const.sub (hpi.pow 2))
    hden).sqrt).smul ?_
  exact (continuous_subtype_val.comp continuous_snd).sub (hpi.smul continuous_const)

/-- `debreuDom` is compact. -/
theorem debreuDom_isCompact (i : Fin L) (η : ℝ) : IsCompact (debreuDom i η) := by
  have hcl : IsClosed (debreuDom i η) := by
    have h2 : IsClosed {p : Fin L → ℝ | p ⬝ᵥ p = 1} :=
      isClosed_eq (by unfold dotProduct; fun_prop) continuous_const
    have e : debreuDom i η = (⋂ l, {p : Fin L → ℝ | 0 ≤ p l}) ∩ {p | p ⬝ᵥ p = 1} ∩
        ⋂ l, ⋂ (_ : l ≠ i), {p : Fin L → ℝ | η ≤ p l} := by
      ext p; simp [debreuDom, and_assoc]
    rw [e]
    exact ((isClosed_iInter fun l => isClosed_le continuous_const (continuous_apply l)).inter
      h2).inter (isClosed_iInter fun l => isClosed_iInter fun _ =>
        isClosed_le continuous_const (continuous_apply l))
  refine (isCompact_Icc (a := (fun _ => (-1 : ℝ))) (b := fun _ => 1)).of_isClosed_subset hcl ?_
  intro p hp
  have hle : ∀ l, p l * p l ≤ 1 := by
    intro l
    have := Finset.single_le_sum (f := fun l => p l * p l) (fun l _ => mul_self_nonneg (p l))
      (Finset.mem_univ l)
    rw [← hp.2.1]
    exact this
  refine ⟨fun l => ?_, fun l => ?_⟩ <;> nlinarith [hle l, hp.1 l]

/-- `unitPEps` is compact. -/
theorem unitPEps_isCompact (L : ℕ) (ε : ℝ) : IsCompact (unitPEps L ε) := by
  have hcl : IsClosed (unitPEps L ε) := by
    have h2 : IsClosed {p : Fin L → ℝ | p ⬝ᵥ p = 1} :=
      isClosed_eq (by unfold dotProduct; fun_prop) continuous_const
    have e : unitPEps L ε = (⋂ l, {p : Fin L → ℝ | 0 ≤ p l}) ∩ {p | p ⬝ᵥ p = 1} ∩
        ⋂ l, ⋂ l', {p : Fin L → ℝ | ε * p l' ≤ p l} := by
      ext p; simp [unitPEps, and_assoc]
    rw [e]
    exact ((isClosed_iInter fun l => isClosed_le continuous_const (continuous_apply l)).inter
      h2).inter (isClosed_iInter fun l => isClosed_iInter fun l' =>
        isClosed_le (continuous_const.mul (continuous_apply l')) (continuous_apply l))
  refine (isCompact_Icc (a := (fun _ => (-1 : ℝ))) (b := fun _ => 1)).of_isClosed_subset hcl ?_
  intro p hp
  have hle : ∀ l, p l * p l ≤ 1 := by
    intro l
    have := Finset.single_le_sum (f := fun l => p l * p l) (fun l _ => mul_self_nonneg (p l))
      (Finset.mem_univ l)
    rw [← hp.2.1]
    exact this
  refine ⟨fun l => ?_, fun l => ?_⟩ <;> nlinarith [hle l, hp.1 l]

/-- Normalized prices of `P_ε` have every coordinate `≥ ε/L` and `≤ 1`. -/
theorem unitPEps_bounds {ε : ℝ} (hε : 0 < ε) {p : Fin L → ℝ} (hp : p ∈ unitPEps L ε)
    (l : Fin L) : ε / L ≤ p l ∧ p l ≤ 1 := by
  have hL : (0 : ℝ) < L := by
    have : 0 < L := Fin.pos l
    exact_mod_cast this
  have hsq : ∀ k, ε ^ 2 * (p k * p k) ≤ p l * p l := by
    intro k
    have h := hp.2.2 l k
    have h0 : 0 ≤ ε * p k := mul_nonneg hε.le (hp.1 k)
    nlinarith
  have hsum : ε ^ 2 ≤ L * (p l * p l) := by
    have := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) => hsq k
    rw [← Finset.mul_sum] at this
    have h1 : ∑ k, p k * p k = 1 := hp.2.1
    rw [h1] at this
    simpa using this
  have hle : p l * p l ≤ 1 := by
    have := Finset.single_le_sum (f := fun l => p l * p l) (fun l _ => mul_self_nonneg (p l))
      (Finset.mem_univ l)
    rw [← hp.2.1]
    exact this
  have hL1 : (1 : ℝ) ≤ L := by
    have : 1 ≤ L := Fin.pos l
    exact_mod_cast this
  refine ⟨?_, by nlinarith [hp.1 l]⟩
  rw [div_le_iff₀ hL]
  by_contra hlt
  push Not at hlt
  have h0 := hp.1 l
  have : (p l * L) ^ 2 < ε ^ 2 := by
    have : 0 ≤ p l * L := by positivity
    nlinarith
  nlinarith

/-- Normalized prices of `P_ε` are in `P_ε`. -/
theorem unitPEps_subset {ε : ℝ} (hε : 0 < ε) : unitPEps L ε ⊆ pEps L ε := by
  intro p hp
  refine ⟨hp.1, fun l l' => ?_⟩
  have hpos : 0 < p l' := by
    have := (unitPEps_bounds hε hp l').1
    have hL : (0 : ℝ) < L := by have : 0 < L := Fin.pos l'; exact_mod_cast this
    exact lt_of_lt_of_le (by positivity) this
  rw [le_div_iff₀ hpos]
  linarith [hp.2.2 l l']

/-- Every `p ∈ P_ε` is `‖p‖ p̂` with `p̂ = p/‖p‖` normalized. -/
theorem pEps_normalize (hL : 0 < L) {ε : ℝ} (hε : 0 < ε) {p : Fin L → ℝ}
    (hp : p ∈ pEps L ε) :
    0 < Real.sqrt (p ⬝ᵥ p) ∧ (Real.sqrt (p ⬝ᵥ p))⁻¹ • p ∈ unitPEps L ε ∧
      p = Real.sqrt (p ⬝ᵥ p) • ((Real.sqrt (p ⬝ᵥ p))⁻¹ • p) := by
  have hp0 := pEps_pos hε hp ⟨0, hL⟩
  have hpp : 0 < p ⬝ᵥ p := by
    have h1 := Finset.single_le_sum (f := fun l => p l * p l) (fun l _ => mul_self_nonneg (p l))
      (Finset.mem_univ ⟨0, hL⟩)
    have h2 : 0 < p ⟨0, hL⟩ * p ⟨0, hL⟩ := mul_pos hp0 hp0
    exact lt_of_lt_of_le h2 h1
  set t := Real.sqrt (p ⬝ᵥ p) with ht
  have htpos : 0 < t := Real.sqrt_pos.2 hpp
  have ht2 : t * t = p ⬝ᵥ p := Real.mul_self_sqrt hpp.le
  refine ⟨htpos, ⟨fun l => ?_, ?_, fun l l' => ?_⟩, ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_nonneg (inv_pos.2 htpos).le (hp.1 l)
  · rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← ht2]
    field_simp
  · have h := hp.2 l l'
    have hl' := pEps_pos hε hp l'
    rw [le_div_iff₀ hl'] at h
    simp only [Pi.smul_apply, smul_eq_mul]
    have hti := inv_pos.2 htpos
    nlinarith
  · rw [smul_smul, mul_inv_cancel₀ htpos.ne', one_smul]

theorem debreuZ_continuous (i : Fin L) : Continuous (debreuZ i) := by
  unfold debreuZ
  exact continuous_const.sub ((continuous_apply i).smul continuous_id)

theorem dot_debreuZ (i : Fin L) (p q : Fin L → ℝ) :
    p ⬝ᵥ debreuZ i q = p i - q i * (p ⬝ᵥ q) := by
  simp [debreuZ, dotProduct_sub, dotProduct_smul]

/-- **Proposition 17.E.3** (MWG, pp. 605-606), consumer `i` of Debreu's construction: for any
continuous `α ≥ 1` on `ℝ^L` (`L ≥ 2`, `0 < ε ≤ 1`) there are continuous, quasiconcave, strongly
monotone preferences whose unique choice on `{z : p·z ≤ 0}`, at each normalized `p ∈ P_ε`, is
`α(p) (eⁱ - pᵢ p)`. -/
theorem debreu_consumer (hL : 1 < L) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (i : Fin L)
    {α : (Fin L → ℝ) → ℝ} (hαc : Continuous α) (hα1 : ∀ p, 1 ≤ α p) :
    ∃ u : (Fin L → ℝ) → ℝ, Continuous u ∧ (∀ c, Convex ℝ {z | c ≤ u z}) ∧
      (∀ z z', z ≤ z' → z ≠ z' → u z < u z') ∧
      ∀ p ∈ unitPEps L ε, ∀ z, p ⬝ᵥ z ≤ 0 →
        u z ≤ u (α p • debreuZ i p) ∧ (u (α p • debreuZ i p) ≤ u z → z = α p • debreuZ i p) := by
  have hLr : (0 : ℝ) < L := by exact_mod_cast (zero_lt_one.trans hL)
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL.le
  set η := ε / L with hη
  have hη0 : 0 < η := by positivity
  have : CompactSpace (debreuDom i η) :=
    isCompact_iff_compactSpace.mp (debreuDom_isCompact i η)
  -- an element of the domain: `𝟙/√L`
  have hsL : 0 < Real.sqrt L := Real.sqrt_pos.2 hLr
  have hsL2 : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hLr.le
  have hsLle : Real.sqrt L ≤ L := by nlinarith
  have hne : Nonempty (debreuDom i η) := by
    refine ⟨⟨fun _ => (Real.sqrt L)⁻¹, fun _ => (inv_pos.2 hsL).le, ?_, fun l _ => ?_⟩⟩
    · simp only [dotProduct, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
      linarith
    · rw [hη, div_le_iff₀ hLr]
      calc ε ≤ 1 := hε1
        _ = (Real.sqrt L)⁻¹ * Real.sqrt L := (inv_mul_cancel₀ hsL.ne').symm
        _ ≤ (Real.sqrt L)⁻¹ * L := mul_le_mul_of_nonneg_left hsLle (inv_pos.2 hsL).le
  have hKD : ∀ p ∈ unitPEps L ε, p ∈ debreuDom i η :=
    fun p hp => ⟨hp.1, hp.2.1, fun l _ => (unitPEps_bounds hε hp l).1⟩
  have hden : ∀ p ∈ debreuDom i η, 1 - p i ^ 2 ≠ 0 := by
    intro p hp
    have := debreuDom_gap hL hη0 hp
    have : 0 < η ^ 2 := by positivity
    linarith
  have hρc := debreuRho_continuous hL hη0 (i := i)
  have hρm : ∀ c (d : debreuDom i η), debreuRho i c d.1 ∈ debreuDom i η :=
    fun c d => debreuRho_mem hL hη0 d.2 c
  have hρi : ∀ c ∈ Set.Icc (0 : ℝ) 1, ∀ d : debreuDom i η,
      debreuRho i c d.1 i = min (d.1 i) c := by
    intro c hc d
    rw [debreuRho_apply_self, max_eq_left hc.1]
  obtain ⟨u, hu1, hu2, hu3, hu4⟩ := smd_rationalize (D := debreuDom i η)
    (zero_lt_one.trans hL) (K := unitPEps L ε) (ζ := fun p => α p • debreuZ i p)
    (lev := fun p => p i)
    (g := fun c d => α (debreuRho i c d.1) • debreuZ i (debreuRho i c d.1))
    (ℓ := fun c d => debreuRho i c d.1 i) (lo := 0) (hi := 1) (θ := ε / (2 * L)) (Θ := 2)
    (m := 1)
    ((hαc.comp hρc).smul ((debreuZ_continuous i).comp hρc))
    ((continuous_apply i).comp hρc) zero_le_one (by positivity)
    (by
      rw [div_le_iff₀ (by positivity)]
      nlinarith)
    one_pos
    (by
      intro p hp l
      have hb := unitPEps_bounds hε hp l
      refine ⟨lt_of_lt_of_le ?_ hb.1, by linarith [hb.2]⟩
      rw [div_lt_div_iff₀ (by positivity) hLr]
      nlinarith)
    (fun p hp => ⟨hp.1 i, (unitPEps_bounds hε hp i).2⟩)
    (fun c hc d => by
      rw [hρi c hc d]
      exact min_le_right _ _)
    (by
      intro p hp c hc hcp d
      set q := debreuRho i c d.1
      have hq := hρm c d
      have hqi : q i ≤ p i := (hρi c hc d).trans_le ((min_le_right _ _).trans hcp)
      have hdot := (unit_dot_le hp.2.1 hq.2.1).1
      have hq0 := hq.1 i
      rw [dotProduct_smul, dot_debreuZ, smul_eq_mul, one_mul]
      have h1 : p i - q i ≤ p i - q i * (p ⬝ᵥ q) := by nlinarith
      have h2 := hα1 q
      nlinarith)
    (by
      intro p hp d hdot hℓ
      set q := debreuRho i (p i) d.1
      have hq := hρm (p i) d
      rw [dotProduct_smul, dot_debreuZ, smul_eq_mul, hℓ] at hdot
      have hpi : 0 < p i := lt_of_lt_of_le (by positivity) (unitPEps_bounds hε hp i).1
      have hαq : α q ≠ 0 := (lt_of_lt_of_le one_pos (hα1 q)).ne'
      have h1 : p i * (1 - p ⬝ᵥ q) = 0 := by
        have := (mul_eq_zero.1 hdot).resolve_left hαq
        linarith
      have h2 : p ⬝ᵥ q = 1 := by
        have := (mul_eq_zero.1 h1).resolve_left hpi.ne'
        linarith
      have h3 : q = p := ((unit_dot_le hp.2.1 hq.2.1).2 h2).symm
      rw [h3])
    (by
      intro p hp
      refine ⟨⟨p, hKD p hp⟩, ?_⟩
      have hρ : debreuRho i (p i) p = p := debreuRho_of_le le_rfl (hden p (hKD p hp))
      simp only [hρ, and_self])
    (fun p hp => by
      rw [dotProduct_smul, debreuZ_walras i hp.2.1, smul_zero])
    (by
      intro c hc c' hc' hcc d
      refine ⟨⟨debreuRho i c d.1, hρm c d⟩, ?_⟩
      have hle : debreuRho i c d.1 i ≤ c' := by
        rw [hρi c hc d]; exact (min_le_right _ _).trans hcc
      have hρ : debreuRho i c' (debreuRho i c d.1) = debreuRho i c d.1 :=
        debreuRho_of_le hle (hden _ (hρm c d))
      simp only [hρ, and_self])
  exact ⟨u, hu1, hu2, hu3, hu4⟩

end MWG.PositiveEquilibriumTheory
