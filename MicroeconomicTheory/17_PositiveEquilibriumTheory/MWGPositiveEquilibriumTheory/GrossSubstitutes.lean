/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPositiveEquilibriumTheory.WeakAxiomDifferential

/-!
# Gross substitutes and uniqueness (MWG Section 17.F, pp. 611-614)

* **Definition 17.F.2** (`GrossSubstitute`, and `WeakGrossSubstitute` with weak inequalities):
  raising one price `pₗ` strictly raises every other excess demand `zₖ`, `k ≠ ℓ`.
* Raising several other prices raises `zₗ` (`gs_path`); with homogeneity, raising `pₗ` lowers
  `zₗ` (`gs_own_price`, p. 611, Figure 17.F.2; it needs `L ≥ 2`, `gs_own_price_one_good`).
  The property is additive (`GrossSubstitute.add`, `GrossSubstitute.sum`, p. 612).
* The differential version (p. 612): gross substitution gives `∂zₖ/∂pₗ ≥ 0` (`gs_partial_nonneg`);
  `∂zₖ/∂pₗ > 0` for `k ≠ ℓ` implies gross substitution (`gs_of_partial_pos`); with homogeneity
  the diagonal is then negative (`gs_diag_neg`).
* **Proposition 17.F.3** (`proposition_17_F_3`): with homogeneity, `z(p) = z(p')` only for
  proportional `p, p'`; at most one normalized equilibrium (`proposition_17_F_3_norm`). The key
  inequality of the proof is `zₗ(p) < zₗ(p')` (`gs_path`); the printed `zₗ(p) > zₗ(p')` is
  reversed (`proposition_17_F_3_printed_sign`).
* **(17.F.3)** (`eq_17_F_3`), for every `L`: if `z(p) = 0` and `z(p') ≠ 0` then `p·z(p') > 0`
  (Arrow-Block-Hurwicz; the book omits the proof). The weak axiom also implies it
  (`wa_eq_17_F_3`). Exercises 17.F.7 (`exercise_17_F_7`), 17.F.8 (`exercise_17_F_8`), 17.F.10
  (`exercise_17_F_10`).
* **Proposition 17.F.4** (`proposition_17_F_4`): at an equilibrium with the gross substitute sign
  pattern, `dp·Dz(p) dp < 0` for `dp` not proportional to `p`, from the identity
  `v·Av = -½ ∑ₖₗ aₖₗ pₖ pₗ (vₖ/pₖ - vₗ/pₗ)²` (`gs_quad_identity`); with weak signs `Dz(p)` is
  negative semidefinite (`gs_nsd_at_eqm`, p. 615).
* Instance: one Cobb-Douglas consumer with `ω ≫ 0` (`cd1_grossSubstitute`).
-/

namespace MWG.PositiveEquilibriumTheory

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.GeneralEquilibriumExamples Filter Topology

variable {L : ℕ}

/-! ### Definition 17.F.2 -/

/-- **Definition 17.F.2** (MWG, p. 611). `z` has the gross substitute property: whenever
`p, p' ≫ 0` satisfy `p'ₗ > pₗ` and `p'ₖ = pₖ` for `k ≠ ℓ`, then `zₖ(p') > zₖ(p)` for `k ≠ ℓ`. -/
def GrossSubstitute (z : (Fin L → ℝ) → Fin L → ℝ) : Prop :=
  ∀ p ∈ posOrthant L, ∀ p' ∈ posOrthant L, ∀ l, p l < p' l → (∀ k, k ≠ l → p' k = p k) →
    ∀ k, k ≠ l → z p k < z p' k

/-- **Section 17.F** (MWG, p. 612). The weak gross substitute property: the inequalities of
Definition 17.F.2 are weak. -/
def WeakGrossSubstitute (z : (Fin L → ℝ) → Fin L → ℝ) : Prop :=
  ∀ p ∈ posOrthant L, ∀ p' ∈ posOrthant L, ∀ l, p l < p' l → (∀ k, k ≠ l → p' k = p k) →
    ∀ k, k ≠ l → z p k ≤ z p' k

/-- Gross substitutes are weak gross substitutes. -/
theorem GrossSubstitute.weak {z : (Fin L → ℝ) → Fin L → ℝ} (h : GrossSubstitute z) :
    WeakGrossSubstitute z :=
  fun p hp p' hp' l hl he k hk => (h p hp p' hp' l hl he k hk).le

/-- **Section 17.F** (MWG, p. 612). The gross substitute property is additive. -/
theorem GrossSubstitute.add {z z' : (Fin L → ℝ) → Fin L → ℝ} (h : GrossSubstitute z)
    (h' : WeakGrossSubstitute z') : GrossSubstitute (z + z') :=
  fun p hp p' hp' l hl he k hk => by
    simp only [Pi.add_apply]
    exact add_lt_add_of_lt_of_le (h p hp p' hp' l hl he k hk) (h' p hp p' hp' l hl he k hk)

/-- **Section 17.F** (MWG, p. 612). The weak gross substitute property is additive. -/
theorem WeakGrossSubstitute.add {z z' : (Fin L → ℝ) → Fin L → ℝ} (h : WeakGrossSubstitute z)
    (h' : WeakGrossSubstitute z') : WeakGrossSubstitute (z + z') :=
  fun p hp p' hp' l hl he k hk => by
    simp only [Pi.add_apply]
    exact add_le_add (h p hp p' hp' l hl he k hk) (h' p hp p' hp' l hl he k hk)

/-- **Section 17.F** (MWG, p. 612). If every individual excess demand has the gross substitute
property, so does the aggregate (at least one consumer). -/
theorem GrossSubstitute.sum {ι : Type*} [Fintype ι] [Nonempty ι]
    {z : ι → (Fin L → ℝ) → Fin L → ℝ} (h : ∀ i, GrossSubstitute (z i)) :
    GrossSubstitute (fun p => ∑ i, z i p) :=
  fun p hp p' hp' l hl he k hk => by
    simp only [Finset.sum_apply]
    exact Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
      fun i _ => h i p hp p' hp' l hl he k hk

/-! ### Raising several prices -/

/-- **Section 17.F** (MWG, pp. 612-613). Under gross substitution, if `p ≤ p'` (both `≫ 0`), with
`pₗ = p'ₗ` and `p ≠ p'`, then `zₗ(p) < zₗ(p')`: raise the other prices one at a time. -/
theorem gs_path {z : (Fin L → ℝ) → Fin L → ℝ} (hGS : GrossSubstitute z) {p p' : Fin L → ℝ}
    (hp : p ∈ posOrthant L) (hp' : p' ∈ posOrthant L) (hle : ∀ k, p k ≤ p' k) {l : Fin L}
    (hl : p l = p' l) (hne : p ≠ p') : z p l < z p' l := by
  classical
  let mix : Finset (Fin L) → Fin L → ℝ := fun s k => if k ∈ s then p' k else p k
  have hmix : ∀ s, mix s ∈ posOrthant L := fun s k => by
    simp only [mix]
    split_ifs
    · exact hp' k
    · exact hp k
  have key : ∀ s : Finset (Fin L), l ∉ s → z p l ≤ z (mix s) l ∧
      ((∃ k ∈ s, p k < p' k) → z p l < z (mix s) l) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      have : mix ∅ = p := by funext k; simp [mix]
      rw [this]
      exact ⟨le_rfl, fun ⟨k, hk, _⟩ => absurd hk (Finset.notMem_empty k)⟩
    | insert a s has ih =>
      intro hls
      have hla : l ≠ a := fun h => hls (h ▸ Finset.mem_insert_self l s)
      have hls' : l ∉ s := fun h => hls (Finset.mem_insert_of_mem h)
      obtain ⟨ih1, ih2⟩ := ih hls'
      have hstep : z (mix s) l ≤ z (mix (insert a s)) l ∧
          (p a < p' a → z (mix s) l < z (mix (insert a s)) l) := by
        rcases eq_or_lt_of_le (hle a) with heq | hlt
        · have : mix (insert a s) = mix s := by
            funext k
            by_cases hk : k = a
            · subst hk; simp [mix, has, heq]
            · simp [mix, hk]
          rw [this]
          exact ⟨le_rfl, fun h => absurd heq h.ne⟩
        · have h := hGS (mix s) (hmix s) (mix (insert a s)) (hmix _) a
            (by simp [mix, has, hlt]) (fun k hk => by simp [mix, hk]) l hla
          exact ⟨h.le, fun _ => h⟩
      refine ⟨ih1.trans hstep.1, fun ⟨k, hk, hpk⟩ => ?_⟩
      rcases Finset.mem_insert.1 hk with rfl | hks
      · exact lt_of_le_of_lt ih1 (hstep.2 hpk)
      · exact lt_of_lt_of_le (ih2 ⟨k, hks, hpk⟩) hstep.1
  have hs : l ∉ Finset.univ.erase l := Finset.notMem_erase l _
  have hfull : mix (Finset.univ.erase l) = p' := by
    funext k
    by_cases hk : k = l
    · subst hk; simp [mix, hl]
    · simp [mix, hk]
  obtain ⟨k, hk⟩ : ∃ k, p k ≠ p' k := Function.ne_iff.1 hne
  have hkl : k ≠ l := fun h => hk (h ▸ hl)
  have := (key _ hs).2 ⟨k, Finset.mem_erase.2 ⟨hkl, Finset.mem_univ k⟩,
    lt_of_le_of_ne (hle k) hk⟩
  rwa [hfull] at this

/-- The weak form of `gs_path`: `p ≤ p'` and `pₗ = p'ₗ` imply `zₗ(p) ≤ zₗ(p')`. -/
theorem gs_path_le {z : (Fin L → ℝ) → Fin L → ℝ} (hGS : GrossSubstitute z) {p p' : Fin L → ℝ}
    (hp : p ∈ posOrthant L) (hp' : p' ∈ posOrthant L) (hle : ∀ k, p k ≤ p' k) {l : Fin L}
    (hl : p l = p' l) : z p l ≤ z p' l := by
  by_cases hne : p = p'
  · rw [hne]
  · exact (gs_path hGS hp hp' hle hl hne).le

/-- **Section 17.F** (MWG, pp. 611-612, Figure 17.F.2). With homogeneity of degree zero and at
least two goods, gross substitution implies that raising `pₗ` (other prices fixed) lowers `zₗ`:
`zₗ(p') < zₗ(p)`. -/
theorem gs_own_price {z : (Fin L → ℝ) → Fin L → ℝ} (hH : EDHomogeneous z)
    (hGS : GrossSubstitute z) {p p' : Fin L → ℝ} (hp : p ∈ posOrthant L)
    (hp' : p' ∈ posOrthant L) {l : Fin L} (hl : p l < p' l) (he : ∀ k, k ≠ l → p' k = p k)
    (h2 : ∃ k, k ≠ l) : z p' l < z p l := by
  set α := p' l / p l with hα
  have hα1 : 1 < α := by rw [hα, lt_div_iff₀ (hp l)]; linarith
  have hαp : α • p ∈ posOrthant L := smul_mem_posOrthant hp (by linarith)
  have hle : ∀ k, p' k ≤ (α • p) k := fun k => by
    by_cases hk : k = l
    · subst hk; simp only [Pi.smul_apply, smul_eq_mul, hα]; rw [div_mul_cancel₀ _ (hp _).ne']
    · rw [he k hk]; simp only [Pi.smul_apply, smul_eq_mul]; nlinarith [hp k]
  have hl' : p' l = (α • p) l := by
    simp only [Pi.smul_apply, smul_eq_mul, hα]; rw [div_mul_cancel₀ _ (hp l).ne']
  obtain ⟨k, hk⟩ := h2
  have hne : p' ≠ α • p := fun h => by
    have := congrFun h k
    rw [he k hk] at this
    simp only [Pi.smul_apply, smul_eq_mul] at this
    nlinarith [hp k]
  have := gs_path hGS hp' hαp hle hl' hne
  rwa [hH p hp α (by linarith)] at this

/-- **Section 17.F** (MWG, p. 611), the case `L ≥ 2` is needed: with one good the zero function is
(vacuously) a gross substitute, homogeneous excess demand, and raising `p₁` does not lower `z₁`. -/
theorem gs_own_price_one_good :
    GrossSubstitute (fun (_ : Fin 1 → ℝ) => (0 : Fin 1 → ℝ)) ∧
      EDHomogeneous (fun (_ : Fin 1 → ℝ) => (0 : Fin 1 → ℝ)) ∧
      ¬ ((fun (_ : Fin 1 → ℝ) => (0 : Fin 1 → ℝ)) ![2] 0 <
        (fun (_ : Fin 1 → ℝ) => (0 : Fin 1 → ℝ)) ![1] 0) := by
  refine ⟨fun p _ p' _ l _ _ k hk => absurd (Subsingleton.elim k l) hk,
    fun _ _ _ _ => rfl, by simp⟩

/-! ### The differential version (p. 612) -/

/-- **Section 17.F** (MWG, p. 612). Under (weak) gross substitution, if `z` is differentiable at
`p ≫ 0` then `∂zₖ/∂pₗ ≥ 0` for `k ≠ ℓ`. -/
theorem gs_partial_nonneg {z : (Fin L → ℝ) → Fin L → ℝ} (hGS : WeakGrossSubstitute z)
    {p : Fin L → ℝ} (hp : p ∈ posOrthant L) {D : (Fin L → ℝ) →L[ℝ] (Fin L → ℝ)}
    (hd : HasFDerivAt z D p) {k l : Fin L} (hkl : k ≠ l) : 0 ≤ D (Pi.single l 1) k := by
  have hline : HasDerivAt (fun t : ℝ => p + t • Pi.single l (1 : ℝ)) (Pi.single l 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single l (1 : ℝ))).const_add p
  have hz := hasDerivAt_pi.1 (hd.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)) k
  have hneg := hz.neg
  have h := wad_deriv_nonpos hneg ?_
  · linarith
  have hcont : Continuous fun t : ℝ => p + t • Pi.single l (1 : ℝ) := by fun_prop
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), p + t • Pi.single l (1 : ℝ) ∈ posOrthant L :=
    hcont.continuousAt.preimage_mem_nhds (by simpa using (isOpen_posOrthant L).mem_nhds hp)
  filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with t ht htpos
  have htpos' : (0 : ℝ) < t := htpos
  change -(z (p + t • Pi.single l 1) k) ≤ -(z (p + (0 : ℝ) • Pi.single l 1) k)
  rw [zero_smul, add_zero, neg_le_neg_iff]
  exact hGS p hp _ ht l (by simp [htpos']) (fun j hj => by simp [hj]) k hkl

/-- **Section 17.F** (MWG, p. 612). The differential gross substitute condition is sufficient: if
`z` is differentiable on `ℝ^L_{++}` and `∂zₖ/∂pₗ > 0` for all `k ≠ ℓ` everywhere, then `z` has
the gross substitute property. -/
theorem gs_of_partial_pos {z : (Fin L → ℝ) → Fin L → ℝ}
    {D : (Fin L → ℝ) → (Fin L → ℝ) →L[ℝ] (Fin L → ℝ)}
    (hd : ∀ q ∈ posOrthant L, HasFDerivAt z (D q) q)
    (hpos : ∀ q ∈ posOrthant L, ∀ k l, k ≠ l → 0 < D q (Pi.single l 1) k) :
    GrossSubstitute z := by
  intro p hp p' hp' l hl he k hkl
  set δ := p' l - p l with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  have hdir : p' - p = δ • Pi.single l (1 : ℝ) := by
    funext j
    by_cases hj : j = l
    · subst hj; simp [hδ]
    · simp [hj, he j hj]
  set c : ℝ → Fin L → ℝ := fun t => p + t • (p' - p) with hc
  have hcmem : ∀ t ∈ Set.Icc (0 : ℝ) 1, c t ∈ posOrthant L := fun t ht => by
    have := convex_posOrthant L hp hp' (a := 1 - t) (b := t) (by linarith [ht.2]) ht.1 (by ring)
    convert this using 1
    simp only [hc]
    module
  have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun s => z (c s) k) (D (c t) (p' - p) k) t := by
    intro t ht
    have hline : HasDerivAt c (p' - p) t := by
      change HasDerivAt (fun s => p + s • (p' - p)) (p' - p) t
      simpa only [id_eq, one_smul] using ((hasDerivAt_id t).smul_const (p' - p)).const_add p
    exact hasDerivAt_pi.1 ((hd _ (hcmem t ht)).comp_hasDerivAt t hline) k
  obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope (fun s => z (c s) k)
    (fun t => D (c t) (p' - p) k) zero_lt_one
    (fun t ht => (hderiv t ht).continuousAt.continuousWithinAt)
    (fun t ht => hderiv t ⟨ht.1.le, ht.2.le⟩)
  have hξpos : 0 < D (c ξ) (p' - p) k := by
    rw [hdir, map_smul, Pi.smul_apply, smul_eq_mul]
    exact mul_pos hδpos (hpos _ (hcmem ξ ⟨hξ.1.le, hξ.2.le⟩) k l hkl)
  have h1 : c 1 = p' := by simp [hc]
  have h0 : c 0 = p := by simp [hc]
  rw [hξeq, h1, h0, sub_zero, div_one] at hξpos
  linarith

/-- **Section 17.F** (MWG, p. 612). With homogeneity of degree zero, if `∂zₗ/∂pₖ > 0` for all
`k ≠ ℓ` (at least one such `k`), then `∂zₗ/∂pₗ < 0`: `Dz(p) p = 0`. -/
theorem gs_diag_neg {z : (Fin L → ℝ) → Fin L → ℝ} (hH : EDHomogeneous z) {p : Fin L → ℝ}
    (hp : p ∈ posOrthant L) {D : (Fin L → ℝ) →L[ℝ] (Fin L → ℝ)} (hd : HasFDerivAt z D p)
    {l : Fin L} (hoff : ∀ k, k ≠ l → 0 < D (Pi.single k 1) l) (h2 : ∃ k, k ≠ l) :
    D (Pi.single l 1) l < 0 := by
  have he := congrFun (euler_fderiv hH hp hd) l
  rw [pe_clm_apply_eq_sum, Pi.zero_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ l)] at he
  obtain ⟨k, hk⟩ := h2
  have hsum : 0 < ∑ j ∈ Finset.univ.erase l, D (Pi.single j 1) l * p j :=
    Finset.sum_pos (fun j hj => mul_pos (hoff j (Finset.ne_of_mem_erase hj)) (hp j))
      ⟨k, Finset.mem_erase.2 ⟨hk, Finset.mem_univ k⟩⟩
  have : D (Pi.single l 1) l * p l < 0 := by linarith
  exact neg_of_mul_neg_left this (hp l).le

/-! ### Proposition 17.F.3 -/

/-- **Proposition 17.F.3** (MWG, p. 613). If `z` is homogeneous of degree zero and has the gross
substitute property, then `z(p) = z(p')` (`p, p' ≫ 0`) only if `p'` is a positive multiple of `p`;
in particular `z(p) = 0` has at most one normalized solution. -/
theorem proposition_17_F_3 {z : (Fin L → ℝ) → Fin L → ℝ} (hH : EDHomogeneous z)
    (hGS : GrossSubstitute z) {p p' : Fin L → ℝ} (hp : p ∈ posOrthant L)
    (hp' : p' ∈ posOrthant L) (heq : z p = z p') : ∃ α : ℝ, 0 < α ∧ p' = α • p := by
  rcases isEmpty_or_nonempty (Fin L) with hL | hL
  · exact ⟨1, one_pos, funext fun l => isEmptyElim l⟩
  obtain ⟨l, -, hmax⟩ := Finset.exists_max_image Finset.univ (fun k => p k / p' k)
    Finset.univ_nonempty
  set α := p l / p' l with hα
  have hαpos : 0 < α := div_pos (hp l) (hp' l)
  have hαp' : α • p' ∈ posOrthant L := smul_mem_posOrthant hp' hαpos
  have hle : ∀ k, p k ≤ (α • p') k := fun k => by
    have := hmax k (Finset.mem_univ k)
    simp only [Pi.smul_apply, smul_eq_mul]
    rwa [div_le_iff₀ (hp' k)] at this
  have hl : p l = (α • p') l := by
    simp only [Pi.smul_apply, smul_eq_mul, hα]; rw [div_mul_cancel₀ _ (hp' l).ne']
  by_cases hne : p = α • p'
  · refine ⟨α⁻¹, inv_pos.2 hαpos, ?_⟩
    rw [hne, smul_smul, inv_mul_cancel₀ hαpos.ne', one_smul]
  · have h := gs_path hGS hp hαp' hle hl hne
    rw [hH p' hp' α hαpos, ← heq] at h
    exact absurd h (lt_irrefl _)

/-- **Proposition 17.F.3** (MWG, p. 613), normalized form (`L = n + 1`, `p_L = 1`): the excess
demand has at most one normalized equilibrium price vector. -/
theorem proposition_17_F_3_norm {n : ℕ} {z : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ}
    (hH : EDHomogeneous z) (hGS : GrossSubstitute z) :
    {q : Fin n → ℝ | IsNormEqm z q}.Subsingleton := by
  intro q hq q' hq'
  obtain ⟨α, -, hα⟩ := proposition_17_F_3 hH hGS hq.1 hq'.1 (by rw [hq.2, hq'.2])
  have hα1 : α = 1 := by
    have := congrFun hα (Fin.last n)
    simpa using this.symm
  funext l
  have := congrFun hα (Fin.castSucc l)
  simpa [hα1] using this.symm

/-! ### Instance: one Cobb-Douglas consumer -/

/-- **Example 17.F.2** (MWG, pp. 612-613), Cobb-Douglas: the excess demand of one Cobb-Douglas
consumer with `ω ≫ 0` has the gross substitute property (`zₗ(p) = αₗ (p·ω)/pₗ - ωₗ` responds
positively to every other price because every `ωₖ > 0`). -/
theorem cd1_grossSubstitute {a ω : Fin L → ℝ} (ha : ∀ l, 0 < a l) (hω : ∀ l, 0 < ω l) :
    GrossSubstitute (cd1ED a ω) := by
  intro p hp p' hp' l hl he k hk
  have hA : 0 < ∑ j, a j :=
    Finset.sum_pos (fun j _ => ha j) ⟨l, Finset.mem_univ l⟩
  have hw : p ⬝ᵥ ω < p' ⬝ᵥ ω := by
    refine Finset.sum_lt_sum (fun j _ => ?_) ⟨l, Finset.mem_univ l, ?_⟩
    · by_cases hj : j = l
      · subst hj; exact mul_le_mul_of_nonneg_right hl.le (hω j).le
      · rw [he j hj]
    · exact mul_lt_mul_of_pos_right hl (hω l)
  simp only [cd1ED, cdDemand, Pi.sub_apply, he k hk, sub_lt_sub_iff_right]
  have hpk := hp k
  refine mul_lt_mul_of_pos_left ?_ (div_pos (ha k) hA)
  exact div_lt_div_of_pos_right hw hpk

/-- **Proposition 17.F.3** (MWG, p. 613), the inequality of the proof as printed, "`zₗ(p) >
zₗ(p')`" (for `p' ≥ p`, `pₗ = p'ₗ`), is reversed: for one Cobb-Douglas consumer
(`a = ω = (1, 1)`), `p = (1, 1)`, `p' = (1, 2)`, `ℓ = 1`: `z₁(p) = 0 < 1/2 = z₁(p')`. -/
theorem proposition_17_F_3_printed_sign :
    cd1ED ![1, 1] ![1, 1] ![1, 1] 0 < cd1ED ![1, 1] ![1, 1] ![1, 2] 0 := by
  simp [cd1ED, cdDemand, dotProduct, Fin.sum_univ_two]
  norm_num

/-! ### (17.F.3) -/

/-- **(17.F.3)** (MWG, p. 613), as a property of `z`: if `z(p) = 0` and `z(p') ≠ 0` (`p, p' ≫ 0`)
then `p·z(p') > 0`. -/
def RevealedEqmProperty (z : (Fin L → ℝ) → Fin L → ℝ) : Prop :=
  ∀ p ∈ posOrthant L, z p = 0 → ∀ p' ∈ posOrthant L, z p' ≠ 0 → 0 < p ⬝ᵥ z p'

/-- **(17.F.3)**, first step. Under homogeneity and gross substitution, at a price vector
`p' ≫ 0` the good `k` with the largest ratio `p'ₖ/pₖ` to an equilibrium `p` has `zₖ(p') ≤ 0`. -/
theorem gs_max_ratio_nonpos {z : (Fin L → ℝ) → Fin L → ℝ} (hH : EDHomogeneous z)
    (hGS : GrossSubstitute z) {p : Fin L → ℝ} (hp : IsEqmPrice z p) {p' : Fin L → ℝ}
    (hp' : p' ∈ posOrthant L) {k : Fin L} (hk : ∀ j, p' j / p j ≤ p' k / p k) :
    z p' k ≤ 0 := by
  set M := p' k / p k with hM
  have hMpos : 0 < M := div_pos (hp' k) (hp.1 k)
  have hle : ∀ j, p' j ≤ (M • p) j := fun j => by
    have := hk j
    simp only [Pi.smul_apply, smul_eq_mul]
    rwa [div_le_iff₀ (hp.1 j)] at this
  have hkk : p' k = (M • p) k := by
    simp only [Pi.smul_apply, smul_eq_mul, hM]; field_simp [(hp.1 k).ne']
  have h := gs_path_le hGS hp' (smul_mem_posOrthant hp.1 hMpos) hle hkk
  rw [hH p hp.1 M hMpos, hp.2] at h
  exact h

/-- **(17.F.3)**, second step. For an equilibrium `p`, `p' ≫ 0` and a threshold `s` splitting the
goods into `T = {k : p'ₖ/pₖ ≥ s}` and its nonempty complement, the value at `p'` of the excess
demand for the goods in `T` is negative: `∑_{k ∈ T} p'ₖ zₖ(p') < 0`. -/
theorem gs_top_value_neg {z : (Fin L → ℝ) → Fin L → ℝ} (hH : EDHomogeneous z)
    (hW : EDWalrasLaw z) (hGS : GrossSubstitute z) {p : Fin L → ℝ} (hp : IsEqmPrice z p)
    {p' : Fin L → ℝ} (hp' : p' ∈ posOrthant L) (s : ℝ) (hlo : ∃ k, p' k / p k < s)
    (hhi : ∃ k, s ≤ p' k / p k) :
    ∑ k ∈ Finset.univ.filter (fun k => s ≤ p' k / p k), p' k * z p' k < 0 := by
  classical
  set T := Finset.univ.filter (fun k => s ≤ p' k / p k) with hT
  set C := Finset.univ.filter (fun k => ¬ s ≤ p' k / p k) with hC
  have hCne : C.Nonempty := by
    obtain ⟨k, hk⟩ := hlo
    exact ⟨k, Finset.mem_filter.2 ⟨Finset.mem_univ k, not_le.2 hk⟩⟩
  obtain ⟨kC, hkC, hmaxC⟩ := Finset.exists_max_image C (fun k => p' k / p k) hCne
  set ν := p' kC / p kC with hν
  have hνs : ν < s := not_le.1 (Finset.mem_filter.1 hkC).2
  have hνpos : 0 < ν := div_pos (hp' kC) (hp.1 kC)
  set R : Fin L → ℝ := fun k => if s ≤ p' k / p k then ν * p k else p' k with hR
  have hRpos : R ∈ posOrthant L := fun k => by
    simp only [hR]; split_ifs
    · exact mul_pos hνpos (hp.1 k)
    · exact hp' k
  have hTlt : ∀ k, s ≤ p' k / p k → ν * p k < p' k := fun k hk => by
    have : ν < p' k / p k := lt_of_lt_of_le hνs hk
    rwa [lt_div_iff₀ (hp.1 k)] at this
  have hRle : ∀ k, R k ≤ p' k := fun k => by
    simp only [hR]; split_ifs with h
    · exact (hTlt k h).le
    · exact le_rfl
  have hRne : R ≠ p' := by
    obtain ⟨k, hk⟩ := hhi
    intro h
    have := congrFun h k
    simp only [hR, hk, ↓reduceIte] at this
    exact (hTlt k hk).ne this
  -- on `C`, `zₖ(R) < zₖ(p')`
  have hCstep : ∀ k ∈ C, R k * z R k < p' k * z p' k := fun k hk => by
    have hkn : ¬ s ≤ p' k / p k := (Finset.mem_filter.1 hk).2
    have hRk : R k = p' k := by simp only [hR, hkn, ↓reduceIte]
    rw [hRk]
    exact mul_lt_mul_of_pos_left (gs_path hGS hRpos hp' hRle hRk hRne) (hp' k)
  -- on `T`, `zₖ(R) ≤ 0` (largest ratio)
  have hTnonpos : ∀ k ∈ T, R k * z R k ≤ 0 := fun k hk => by
    have hks : s ≤ p' k / p k := (Finset.mem_filter.1 hk).2
    have hratio : ∀ j, R j / p j ≤ R k / p k := fun j => by
      have hRk : R k / p k = ν := by
        simp only [hR, hks, ↓reduceIte]; field_simp [(hp.1 k).ne']
      rw [hRk]
      by_cases hj : s ≤ p' j / p j
      · simp only [hR, hj, ↓reduceIte]; field_simp [(hp.1 j).ne']; rfl
      · simp only [hR, hj, ↓reduceIte]
        exact hmaxC j (Finset.mem_filter.2 ⟨Finset.mem_univ j, hj⟩)
    exact mul_nonpos_of_nonneg_of_nonpos (hRpos k).le
      (gs_max_ratio_nonpos hH hGS hp hRpos hratio)
  have hWR := hW R hRpos
  have hWp := hW p' hp'
  rw [dotProduct, ← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun k => s ≤ p' k / p k)] at hWR hWp
  have h1 : ∑ k ∈ T, R k * z R k ≤ 0 := Finset.sum_nonpos hTnonpos
  have h2 : ∑ k ∈ C, R k * z R k < ∑ k ∈ C, p' k * z p' k :=
    Finset.sum_lt_sum_of_nonempty hCne hCstep
  rw [← hT, ← hC] at hWR hWp
  linarith

/-- **(17.F.3)**, an Abel summation lemma. Let `λₖ > 0`, `∑ₖ bₖ = 0`, and suppose that for every
threshold `s` separating the values of `λ`, `∑_{λₖ ≥ s} bₖ < 0`. Then `∑ₖ bₖ/λₖ ≥ 0`, with
strict inequality unless `λ` is constant. -/
theorem gs_abel (b : Fin L → ℝ) (hb : ∑ k, b k = 0) :
    ∀ (lam : Fin L → ℝ), (∀ k, 0 < lam k) → (∀ s : ℝ, (∃ k, lam k < s) → (∃ k, s ≤ lam k) →
      ∑ k ∈ Finset.univ.filter (fun k => s ≤ lam k), b k < 0) →
      0 ≤ ∑ k, b k / lam k ∧ ((∃ k k', lam k ≠ lam k') → 0 < ∑ k, b k / lam k) := by
  classical
  intro lam
  induction hN : (Finset.univ.image lam).card using Nat.strong_induction_on generalizing lam with
  | _ N ih =>
  intro hlam hT
  by_cases hc : ∃ k k', lam k ≠ lam k'
  · have : Nonempty (Fin L) := ⟨hc.choose⟩
    obtain ⟨k0, -, hmin⟩ := Finset.exists_min_image Finset.univ lam Finset.univ_nonempty
    set μ := lam k0 with hμ
    have hS2 : (Finset.univ.filter (fun k => μ < lam k)).Nonempty := by
      obtain ⟨k, k', hkk⟩ := hc
      by_cases h : lam k = μ
      · refine ⟨k', Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩⟩
        exact lt_of_le_of_ne (hmin k' (Finset.mem_univ _)) (h ▸ hkk)
      · exact ⟨k, Finset.mem_filter.2 ⟨Finset.mem_univ _,
          lt_of_le_of_ne (hmin k (Finset.mem_univ _)) (Ne.symm h)⟩⟩
    obtain ⟨k2, hk2, hmin2⟩ := Finset.exists_min_image _ lam hS2
    set μ2 := lam k2 with hμ2
    have hμμ2 : μ < μ2 := (Finset.mem_filter.1 hk2).2
    have hlow : ∀ k, lam k < μ2 → lam k = μ := fun k hk => by
      by_contra hne
      have : μ < lam k := lt_of_le_of_ne (hmin k (Finset.mem_univ _)) (Ne.symm hne)
      have := hmin2 k (Finset.mem_filter.2 ⟨Finset.mem_univ _, this⟩)
      linarith
    set lam' : Fin L → ℝ := fun k => max (lam k) μ2 with hlam'
    have hlam'pos : ∀ k, 0 < lam' k := fun k => lt_of_lt_of_le (hlam k) (le_max_left _ _)
    have hfilt : ∀ s, μ2 < s →
        Finset.univ.filter (fun k => s ≤ lam' k) = Finset.univ.filter (fun k => s ≤ lam k) := by
      intro s hs
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hlam', le_max_iff]
      constructor
      · rintro (h | h)
        · exact h
        · linarith
      · exact Or.inl
    have hT' : ∀ s : ℝ, (∃ k, lam' k < s) → (∃ k, s ≤ lam' k) →
        ∑ k ∈ Finset.univ.filter (fun k => s ≤ lam' k), b k < 0 := by
      intro s ⟨k1, hk1⟩ ⟨k3, hk3⟩
      have hs : μ2 < s := lt_of_le_of_lt (le_max_right _ _) hk1
      rw [hfilt s hs]
      refine hT s ⟨k0, by linarith⟩ ⟨k3, ?_⟩
      have := (Finset.ext_iff.1 (hfilt s hs) k3).1 (by simpa using hk3)
      simpa using this
    have hcard : (Finset.univ.image lam').card < N := by
      rw [← hN]
      refine Finset.card_lt_card ⟨fun v hv => ?_, fun hsub => ?_⟩
      · obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hv
        rcases le_total (lam k) μ2 with h | h
        · simp only [hlam', max_eq_right h]
          exact Finset.mem_image.2 ⟨k2, Finset.mem_univ _, rfl⟩
        · simp only [hlam', max_eq_left h]
          exact Finset.mem_image.2 ⟨k, Finset.mem_univ _, rfl⟩
      · obtain ⟨k, -, hk⟩ := Finset.mem_image.1 (hsub (Finset.mem_image.2
          ⟨k0, Finset.mem_univ _, rfl⟩))
        have : μ2 ≤ lam' k := le_max_right _ _
        rw [hk] at this
        linarith
    have hIH := (ih _ hcard lam' rfl hlam'pos hT').1
    have hdiff : ∀ k, b k / lam k - b k / lam' k =
        if lam k < μ2 then b k * (1 / μ - 1 / μ2) else 0 := fun k => by
      split_ifs with h
      · simp only [hlam', max_eq_right h.le]
        rw [hlow k h]
        ring
      · simp only [hlam', max_eq_left (not_lt.1 h), sub_self]
    have hsumdiff : ∑ k, b k / lam k - ∑ k, b k / lam' k =
        (1 / μ - 1 / μ2) * ∑ k ∈ Finset.univ.filter (fun k => lam k < μ2), b k := by
      rw [← Finset.sum_sub_distrib, Finset.sum_congr rfl fun k _ => hdiff k,
        ← Finset.sum_filter, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    have hlowsum : 0 < ∑ k ∈ Finset.univ.filter (fun k => lam k < μ2), b k := by
      have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ (fun k => μ2 ≤ lam k) b
      have htop := hT μ2 ⟨k0, hμμ2⟩ ⟨k2, le_rfl⟩
      have hfeq : Finset.univ.filter (fun k => ¬ μ2 ≤ lam k) =
          Finset.univ.filter (fun k => lam k < μ2) := by
        ext k; simp
      rw [hfeq, hb] at hsplit
      linarith
    have hcoef : 0 < 1 / μ - 1 / μ2 := by
      have := hlam k0
      rw [sub_pos]
      exact one_div_lt_one_div_of_lt this hμμ2
    have hpos : 0 < ∑ k, b k / lam k := by nlinarith
    exact ⟨hpos.le, fun _ => hpos⟩
  · push Not at hc
    refine ⟨le_of_eq ?_, fun h => absurd h (by push Not; exact hc)⟩
    rcases isEmpty_or_nonempty (Fin L) with hL | ⟨⟨k0⟩⟩
    · simp
    · rw [Finset.sum_congr rfl fun k _ => by rw [hc k k0], ← Finset.sum_div, hb, zero_div]

/-- **(17.F.3)** (MWG, p. 613). If `z` is homogeneous of degree zero, satisfies Walras' law and has
the gross substitute property, then `z(p) = 0` and `z(p') ≠ 0` imply `p·z(p') > 0`, for any
number of goods. (The book does not prove it; Exercise 17.F.7 asks for `L = 2`.) -/
theorem eq_17_F_3 {z : (Fin L → ℝ) → Fin L → ℝ} (hH : EDHomogeneous z) (hW : EDWalrasLaw z)
    (hGS : GrossSubstitute z) : RevealedEqmProperty z := by
  intro p hp hz p' hp' hz'
  have heq : IsEqmPrice z p := ⟨hp, hz⟩
  have key := gs_abel (fun k => p' k * z p' k) (hW p' hp') (fun k => p' k / p k)
    (fun k => div_pos (hp' k) (hp k))
    (fun s hlo hhi => gs_top_value_neg hH hW hGS heq hp' s hlo hhi)
  have hval : ∑ k, p' k * z p' k / (p' k / p k) = p ⬝ᵥ z p' := by
    refine Finset.sum_congr rfl fun k _ => ?_
    have := (hp' k).ne'
    have := (hp k).ne'
    field_simp
  rw [← hval]
  refine key.2 ?_
  by_contra hcon
  push Not at hcon
  rcases isEmpty_or_nonempty (Fin L) with hL | ⟨⟨k0⟩⟩
  · exact hz' (funext fun l => isEmptyElim l)
  have hprop : p' = (p' k0 / p k0) • p := by
    funext k
    have := hcon k k0
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← this]
    field_simp [(hp k).ne']
  apply hz'
  rw [hprop, hH p hp _ (div_pos (hp' k0) (hp k0)), hz]

/-- **Section 17.F** (MWG, p. 614). The weak axiom implies (17.F.3): no
equilibrium price vector is revealed preferred to a nonequilibrium price vector. -/
theorem wa_eq_17_F_3 {z : (Fin L → ℝ) → Fin L → ℝ} (hWA : WeakAxiomED z) :
    RevealedEqmProperty z := by
  intro p hp hz p' hp' hz'
  exact hWA p' hp' p hp (by rw [hz]; exact hz') (by rw [hz, dotProduct_zero])

/-- **Exercise 17.F.7** (MWG, p. 646). Expression (17.F.3) for `L = 2`. -/
theorem exercise_17_F_7 {z : (Fin 2 → ℝ) → Fin 2 → ℝ} (hH : EDHomogeneous z)
    (hW : EDWalrasLaw z) (hGS : GrossSubstitute z) : RevealedEqmProperty z :=
  eq_17_F_3 hH hW hGS

/-- **Exercise 17.F.8** (MWG, p. 646). With Walras' law, (17.F.3) implies that the set of
solutions of `z(p) = 0` (`p ≫ 0`) is convex. -/
theorem exercise_17_F_8 {z : (Fin L → ℝ) → Fin L → ℝ} (hW : EDWalrasLaw z)
    (h : RevealedEqmProperty z) : Convex ℝ {p | IsEqmPrice z p} := by
  intro p hp p' hp' a b ha hb hab
  have hq := convex_posOrthant L hp.1 hp'.1 ha hb hab
  refine ⟨hq, ?_⟩
  by_contra hne
  have h1 := h p hp.1 hp.2 _ hq hne
  have h2 := h p' hp'.1 hp'.2 _ hq hne
  have hw := hW _ hq
  rw [add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul] at hw
  rcases eq_or_lt_of_le ha with ha0 | ha0
  · subst ha0
    have : b = 1 := by linarith
    subst this
    linarith
  · nlinarith

/-- **Exercise 17.F.10** (MWG, p. 646). With Walras' law, (17.F.3) implies that `Dz(p)` is
negative semidefinite at an equilibrium `p`. -/
theorem exercise_17_F_10 {z : (Fin L → ℝ) → Fin L → ℝ} (hW : EDWalrasLaw z)
    (h : RevealedEqmProperty z) {p : Fin L → ℝ} (hp : IsEqmPrice z p)
    {D : (Fin L → ℝ) →L[ℝ] (Fin L → ℝ)} (hd : HasFDerivAt z D p) (v : Fin L → ℝ) :
    v ⬝ᵥ D v ≤ 0 := by
  have hline : HasDerivAt (fun t : ℝ => p + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add p
  have hz : HasDerivAt (fun t : ℝ => z (p + t • v)) (D v) 0 :=
    hd.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
  refine wad_deriv_nonpos (wad_hasDerivAt_dot v hz) ?_
  have hcont : Continuous fun t : ℝ => p + t • v := by fun_prop
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), p + t • v ∈ posOrthant L :=
    hcont.continuousAt.preimage_mem_nhds (by simpa using (isOpen_posOrthant L).mem_nhds hp.1)
  filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with t ht htpos
  have htpos' : (0 : ℝ) < t := htpos
  simp only [zero_smul, add_zero, hp.2, dotProduct_zero]
  by_cases hz0 : z (p + t • v) = 0
  · rw [hz0, dotProduct_zero]
  · have h1 := h p hp.1 hp.2 _ ht hz0
    have h2 := hW _ ht
    rw [add_dotProduct, smul_dotProduct, smul_eq_mul] at h2
    nlinarith

/-! ### Proposition 17.F.4 -/

/-- **Proposition 17.F.4**, the quadratic form identity: if `A p = 0` and `pᵀA = 0` with `pₖ ≠ 0`,
then `v·Av = -½ ∑ₖ ∑ₗ aₖₗ pₖ pₗ (vₖ/pₖ - vₗ/pₗ)²`. -/
theorem gs_quad_identity (A : Fin L → Fin L → ℝ) {p : Fin L → ℝ} (hp : ∀ k, p k ≠ 0)
    (hrow : ∀ k, ∑ l, A k l * p l = 0) (hcol : ∀ l, ∑ k, p k * A k l = 0) (v : Fin L → ℝ) :
    ∑ k, ∑ l, v k * A k l * v l =
      -(1 / 2) * ∑ k, ∑ l, A k l * p k * p l * (v k / p k - v l / p l) ^ 2 := by
  have hterm : ∀ k l, A k l * p k * p l * (v k / p k - v l / p l) ^ 2 =
      v k ^ 2 / p k * (A k l * p l) - 2 * (v k * A k l * v l) +
        v l ^ 2 / p l * (p k * A k l) := fun k l => by
    have := hp k
    have := hp l
    field_simp
    ring
  simp only [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hrow,
    mul_zero, zero_sub]
  rw [Finset.sum_comm (f := fun k l => v l ^ 2 / p l * (p k * A k l))]
  simp only [← Finset.mul_sum, hcol, mul_zero, Finset.sum_const_zero, add_zero]
  rw [Finset.sum_neg_distrib, ← Finset.mul_sum]
  ring

/-- `v·Dv` in coordinates, `aₖₗ = (D eˡ)ₖ = ∂zₖ/∂pₗ`. -/
theorem gs_dot_apply (D : (Fin L → ℝ) →L[ℝ] (Fin L → ℝ)) (v : Fin L → ℝ) :
    v ⬝ᵥ D v = ∑ k, ∑ l, v k * D (Pi.single l 1) k * v l := by
  simp only [dotProduct]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [pe_clm_apply_eq_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by ring

/-- At an equilibrium of a homogeneous `z` with Walras' law, `Dz(p)p = 0` and `pᵀDz(p) = 0` in
coordinates. -/
theorem gs_row_col {z : (Fin L → ℝ) → Fin L → ℝ} (hH : EDHomogeneous z) (hW : EDWalrasLaw z)
    {p : Fin L → ℝ} (hp : IsEqmPrice z p) {D : (Fin L → ℝ) →L[ℝ] (Fin L → ℝ)}
    (hd : HasFDerivAt z D p) :
    (∀ k, ∑ l, D (Pi.single l 1) k * p l = 0) ∧ ∀ l, ∑ k, p k * D (Pi.single l 1) k = 0 := by
  refine ⟨fun k => ?_, fun l => ?_⟩
  · rw [← pe_clm_apply_eq_sum, euler_fderiv hH hp.1 hd, Pi.zero_apply]
  · have := walras_fderiv hW hp.1 hd (Pi.single l 1)
    rw [hp.2, dotProduct_zero, zero_add] at this
    exact this

/-- **Proposition 17.F.4** (MWG, p. 614). If `z` is an aggregate excess demand function
(homogeneous of degree zero, Walras' law), `z(p) = 0`, and `Dz(p)` has the gross substitute sign
pattern (`∂zₖ/∂pₗ > 0` for `k ≠ ℓ`), then `dp·Dz(p) dp < 0` whenever `dp` is not proportional to
`p` (in particular `dp ≠ 0`). -/
theorem proposition_17_F_4 {z : (Fin L → ℝ) → Fin L → ℝ} (hH : EDHomogeneous z)
    (hW : EDWalrasLaw z) {p : Fin L → ℝ} (hp : IsEqmPrice z p)
    {D : (Fin L → ℝ) →L[ℝ] (Fin L → ℝ)} (hd : HasFDerivAt z D p)
    (hsign : ∀ k l, k ≠ l → 0 < D (Pi.single l 1) k) {dp : Fin L → ℝ}
    (hprop : ∀ α : ℝ, dp ≠ α • p) : dp ⬝ᵥ D dp < 0 := by
  obtain ⟨hrow, hcol⟩ := gs_row_col hH hW hp hd
  rw [gs_dot_apply, gs_quad_identity _ (fun k => (hp.1 k).ne') hrow hcol]
  rcases isEmpty_or_nonempty (Fin L) with hL | ⟨⟨k0⟩⟩
  · exact absurd (funext fun l => isEmptyElim l) (hprop 0)
  obtain ⟨k1, hk1⟩ : ∃ k, dp k / p k ≠ dp k0 / p k0 := by
    by_contra hcon
    push Not at hcon
    apply hprop (dp k0 / p k0)
    funext k
    have := hcon k
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← this]
    field_simp [(hp.1 k).ne']
  have hk10 : k1 ≠ k0 := fun h => hk1 (by rw [h])
  have hnn : ∀ k l, 0 ≤ D (Pi.single l 1) k * p k * p l * (dp k / p k - dp l / p l) ^ 2 :=
    fun k l => by
      by_cases hkl : k = l
      · subst hkl; simp
      · exact mul_nonneg (mul_nonneg (mul_nonneg (hsign k l hkl).le (hp.1 k).le) (hp.1 l).le)
          (sq_nonneg _)
  have hpos : 0 < ∑ k, ∑ l, D (Pi.single l 1) k * p k * p l * (dp k / p k - dp l / p l) ^ 2 := by
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun k _ => Finset.sum_nonneg
      fun l _ => hnn k l) (Finset.mem_univ k1))
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun l _ => hnn k1 l) (Finset.mem_univ k0))
    exact mul_pos (mul_pos (mul_pos (hsign k1 k0 hk10) (hp.1 k1)) (hp.1 k0))
      (sq_pos_of_ne_zero (sub_ne_zero.2 hk1))
  linarith

/-- **Section 17.F** (MWG, p. 615). If `z` (homogeneous of degree zero, Walras' law) has the weak
gross substitute property and is differentiable at an equilibrium `p`, then `Dz(p)` is negative
semidefinite. -/
theorem gs_nsd_at_eqm {z : (Fin L → ℝ) → Fin L → ℝ} (hH : EDHomogeneous z) (hW : EDWalrasLaw z)
    (hGS : WeakGrossSubstitute z) {p : Fin L → ℝ} (hp : IsEqmPrice z p)
    {D : (Fin L → ℝ) →L[ℝ] (Fin L → ℝ)} (hd : HasFDerivAt z D p) (v : Fin L → ℝ) :
    v ⬝ᵥ D v ≤ 0 := by
  obtain ⟨hrow, hcol⟩ := gs_row_col hH hW hp hd
  rw [gs_dot_apply, gs_quad_identity _ (fun k => (hp.1 k).ne') hrow hcol]
  have hnn : ∀ k l, 0 ≤ D (Pi.single l 1) k * p k * p l * (v k / p k - v l / p l) ^ 2 :=
    fun k l => by
      by_cases hkl : k = l
      · subst hkl; simp
      · exact mul_nonneg (mul_nonneg (mul_nonneg (gs_partial_nonneg hGS hp.1 hd hkl)
          (hp.1 k).le) (hp.1 l).le) (sq_nonneg _)
  have := Finset.sum_nonneg fun k (_ : k ∈ Finset.univ) =>
    Finset.sum_nonneg fun l (_ : l ∈ Finset.univ) => hnn k l
  linarith

end MWG.PositiveEquilibriumTheory
