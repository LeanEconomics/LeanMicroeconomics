/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPositiveEquilibriumTheory.GenericRegularity
import MWGPositiveEquilibriumTheory.IndexTwoGoods

/-!
# Exercise 17.D.4: fixed total endowment (MWG p. 644)

Two goods, two consumers with `C¹` demand functions `xᵢ(p, w)`, total endowment `ω̄` fixed and
`ω₁ ≪ ω̄`, `ω₂ = ω̄ - ω₁`. Only the distribution of endowments varies (2 parameters), so
Proposition 17.D.4 does not apply directly: `D_{ω₁}ẑ₁ = (∂_w x₁₁ - ∂_w x₁₂) pᵀ` vanishes when the
wealth effects coincide. The hint: then `∂ẑ₁/∂p₁ = s₁ + s₂ < 0` by the Slutsky decomposition
(`∂x₁ᵢ/∂p₁ = sᵢ - x₁ᵢ ∂x₁ᵢ/∂w`, with negative own substitution effects `sᵢ`). So
`Dẑ₁(p₁; ω₁)` always has full rank 1 at equilibrium (`d4_rank`), and by the transversality
theorem, for almost every `ω₁ ≪ ω̄` the economy is regular (`exercise_17_D_4`), hence has
finitely many equilibria (Proposition 17.D.1). Instance: Cobb-Douglas consumers
(`exercise_17_D_4_cobbDouglas`).
-/

namespace MWG.PositiveEquilibriumTheory

open Filter Topology MeasureTheory MWG.ClassicalDemand

/-- `(p̂, 1)` with one relative price. -/
theorem normPrice_one (v : Fin 1 → ℝ) : normPrice v = ![v 0, 1] := by
  rw [← vec1_apply_zero v, normPrice_vec1]
  rfl

/-- **Exercise 17.D.4**: the excess demand for good 1 with endowments `(ω₁, ω̄ - ω₁)`, as a
function of `(p̂₁; ω₁)`. -/
noncomputable def d4Sys (x : Fin 2 → (Fin 2 → ℝ) → ℝ → Fin 2 → ℝ) (ωb : Fin 2 → ℝ)
    (z : (Fin 1 → ℝ) × (Fin 2 → ℝ)) : Fin 1 → ℝ :=
  normED (demandED x ![z.2, ωb - z.2]) z.1

variable {x : Fin 2 → (Fin 2 → ℝ) → ℝ → Fin 2 → ℝ} {ωb : Fin 2 → ℝ}

theorem d4Sys_apply (z : (Fin 1 → ℝ) × (Fin 2 → ℝ)) :
    d4Sys x ωb z 0 = x 0 ![z.1 0, 1] (![z.1 0, 1] ⬝ᵥ z.2) 0 +
      x 1 ![z.1 0, 1] (![z.1 0, 1] ⬝ᵥ (ωb - z.2)) 0 - ωb 0 := by
  simp only [d4Sys, normED, truncExcessDemand, demandED, normPrice_one, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.add_apply,
    Pi.sub_apply]
  simp only [Fin.castSucc_zero]
  ring

/-- The uncurried demand `(p, w) ↦ xᵢ(p, w)`. -/
def d4X (x : Fin 2 → (Fin 2 → ℝ) → ℝ → Fin 2 → ℝ) (i : Fin 2) : (Fin 2 → ℝ) × ℝ → Fin 2 → ℝ :=
  fun r => x i r.1 r.2

/-- **Exercise 17.D.4**, the full rank condition. At an equilibrium `(p₁, 1)` (`p₁ > 0`) of the
economy with endowments `(ω₁, ω̄ - ω₁)`, if the demands are differentiable with negative own
substitution effects `sᵢ = ∂x₁ᵢ/∂p₁ + x₁ᵢ ∂x₁ᵢ/∂w < 0`, then `Dẑ₁(p₁; ω₁)` has rank 1. -/
theorem d4_rank {v : Fin 1 → ℝ} {q : Fin 2 → ℝ} (hd : DifferentiableAt ℝ (d4Sys x ωb) (v, q))
    (hv : 0 < v 0) (h0 : d4Sys x ωb (v, q) = 0)
    {D₀ D₁ : (Fin 2 → ℝ) × ℝ →L[ℝ] (Fin 2 → ℝ)}
    (hx₀ : HasFDerivAt (d4X x 0) D₀ (![v 0, 1], ![v 0, 1] ⬝ᵥ q))
    (hx₁ : HasFDerivAt (d4X x 1) D₁ (![v 0, 1], ![v 0, 1] ⬝ᵥ (ωb - q)))
    (hS₀ : D₀ (Pi.single 0 1, 0) 0 + x 0 ![v 0, 1] (![v 0, 1] ⬝ᵥ q) 0 * D₀ (0, 1) 0 < 0)
    (hS₁ : D₁ (Pi.single 0 1, 0) 0 +
      x 1 ![v 0, 1] (![v 0, 1] ⬝ᵥ (ωb - q)) 0 * D₁ (0, 1) 0 < 0) :
    (fderiv ℝ (d4Sys x ωb) (v, q)).range = ⊤ := by
  set D := fderiv ℝ (d4Sys x ωb) (v, q)
  set P : Fin 2 → ℝ := ![v 0, 1]
  set e : Fin 2 → ℝ := Pi.single 0 1
  have hPe : ∀ (y : Fin 2 → ℝ) (s : ℝ), P ⬝ᵥ (y + s • e) = P ⬝ᵥ y + s * v 0 := by
    intro y s
    simp [P, e, dotProduct, Fin.sum_univ_two]
    ring
  -- direction in `ω₁`
  have hA : D (0, e) 0 = v 0 * (D₀ (0, 1) 0 - D₁ (0, 1) 0) := by
    have hline : HasDerivAt (fun s : ℝ => (v, q + s • e)) ((0 : Fin 1 → ℝ), e) 0 := by
      refine (hasDerivAt_const (0 : ℝ) v).prodMk ?_
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add q
    have h1 := hasDerivAt_pi.1 (hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)) 0
    have hl0 : HasDerivAt (fun s : ℝ => (P, P ⬝ᵥ q + s * v 0)) ((0 : Fin 2 → ℝ), v 0) 0 := by
      refine (hasDerivAt_const (0 : ℝ) P).prodMk ?_
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v 0)).const_add (P ⬝ᵥ q)
    have hl1 : HasDerivAt (fun s : ℝ => (P, P ⬝ᵥ (ωb - q) - s * v 0))
        ((0 : Fin 2 → ℝ), -v 0) 0 := by
      refine (hasDerivAt_const (0 : ℝ) P).prodMk ?_
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v 0)).const_sub (P ⬝ᵥ (ωb - q))
    have g0 := hasDerivAt_pi.1 (hx₀.comp_hasDerivAt_of_eq (0 : ℝ) hl0 (by simp)) 0
    have g1 := hasDerivAt_pi.1 (hx₁.comp_hasDerivAt_of_eq (0 : ℝ) hl1 (by simp)) 0
    have h2 := (g0.add g1).sub_const (ωb 0)
    have heq := h1.unique (by
      convert h2 using 2 with s
      change d4Sys x ωb (v, q + s • e) 0 = d4X x 0 (P, P ⬝ᵥ q + s * v 0) 0 +
        d4X x 1 (P, P ⬝ᵥ (ωb - q) - s * v 0) 0 - ωb 0
      rw [d4Sys_apply]
      have h3 : P ⬝ᵥ (ωb - (q + s • e)) = P ⬝ᵥ (ωb - q) - s * v 0 := by
        rw [show ωb - (q + s • e) = (ωb - q) + (-s) • e by rw [neg_smul]; abel, hPe]
        ring
      simp only [d4X]
      rw [hPe, h3])
    rw [heq]
    have e0 : ((0 : Fin 2 → ℝ), v 0) = v 0 • ((0 : Fin 2 → ℝ), (1 : ℝ)) := by simp
    have e1 : ((0 : Fin 2 → ℝ), -v 0) = (-v 0) • ((0 : Fin 2 → ℝ), (1 : ℝ)) := by simp
    rw [e0, e1, map_smul, map_smul]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  -- direction in `p₁`
  have hB : D ((fun _ => 1), 0) 0 = D₀ (e, q 0) 0 + D₁ (e, ωb 0 - q 0) 0 := by
    have hline : HasDerivAt (fun s : ℝ => (v + s • (fun _ => (1 : ℝ)), q))
        ((fun _ => (1 : ℝ)), (0 : Fin 2 → ℝ)) 0 := by
      refine HasDerivAt.prodMk ?_ (hasDerivAt_const (0 : ℝ) q)
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (fun _ => (1 : ℝ))).const_add v
    have h1 := hasDerivAt_pi.1 (hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)) 0
    have hP : ∀ s : ℝ, (![(v + s • (fun _ => (1 : ℝ)) : Fin 1 → ℝ) 0, 1] : Fin 2 → ℝ) =
        P + s • e := by
      intro s
      funext k
      fin_cases k <;> simp [P, e]
    have hl0 : HasDerivAt (fun s : ℝ => (P + s • e, (P + s • e) ⬝ᵥ q)) (e, q 0) 0 := by
      have hPl : HasDerivAt (fun s : ℝ => P + s • e) e 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add P
      refine hPl.prodMk ?_
      have : (fun s : ℝ => (P + s • e) ⬝ᵥ q) = fun s => P ⬝ᵥ q + s * q 0 := by
        funext s; simp [e, add_dotProduct, smul_dotProduct]
      rw [this]
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (q 0)).const_add (P ⬝ᵥ q)
    have hl1 : HasDerivAt (fun s : ℝ => (P + s • e, (P + s • e) ⬝ᵥ (ωb - q)))
        (e, ωb 0 - q 0) 0 := by
      have hPl : HasDerivAt (fun s : ℝ => P + s • e) e 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add P
      refine hPl.prodMk ?_
      have : (fun s : ℝ => (P + s • e) ⬝ᵥ (ωb - q)) =
          fun s => P ⬝ᵥ (ωb - q) + s * (ωb 0 - q 0) := by
        funext s; simp [e, add_dotProduct, smul_dotProduct]; ring
      rw [this]
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (ωb 0 - q 0)).const_add (P ⬝ᵥ (ωb - q))
    have g0 := hasDerivAt_pi.1 (hx₀.comp_hasDerivAt_of_eq (0 : ℝ) hl0 (by simp)) 0
    have g1 := hasDerivAt_pi.1 (hx₁.comp_hasDerivAt_of_eq (0 : ℝ) hl1 (by simp)) 0
    have h2 := (g0.add g1).sub_const (ωb 0)
    have heq := h1.unique (by
      convert h2 using 2 with s
      change d4Sys x ωb (v + s • (fun _ => (1 : ℝ)), q) 0 =
        d4X x 0 (P + s • e, (P + s • e) ⬝ᵥ q) 0 +
          d4X x 1 (P + s • e, (P + s • e) ⬝ᵥ (ωb - q)) 0 - ωb 0
      rw [d4Sys_apply]
      simp only [d4X]
      rw [hP s])
    rw [heq]
  -- the equilibrium condition and the Slutsky decomposition
  have hz : x 0 P (P ⬝ᵥ q) 0 + x 1 P (P ⬝ᵥ (ωb - q)) 0 - ωb 0 = 0 := by
    have := congrFun h0 0
    rw [d4Sys_apply] at this
    exact this
  have hsplit : ∀ (Dd : (Fin 2 → ℝ) × ℝ →L[ℝ] (Fin 2 → ℝ)) (c : ℝ),
      Dd (e, c) 0 = Dd (e, 0) 0 + c * Dd (0, 1) 0 := by
    intro Dd c
    rw [show (e, c) = (e, (0 : ℝ)) + c • ((0 : Fin 2 → ℝ), (1 : ℝ)) by simp, map_add, map_smul]
    simp
  have hdir : ∃ y, D y 0 ≠ 0 := by
    by_cases ha : D₀ (0, 1) 0 = D₁ (0, 1) 0
    · refine ⟨((fun _ => 1), 0), ?_⟩
      rw [hB, hsplit D₀, hsplit D₁]
      intro h
      have : D₀ (e, 0) 0 + D₁ (e, 0) 0 + q 0 * D₀ (0, 1) 0 + (ωb 0 - q 0) * D₁ (0, 1) 0 = 0 := by
        linarith
      rw [ha] at this hS₀
      have hx : x 0 P (P ⬝ᵥ q) 0 * D₁ (0, 1) 0 +
          x 1 P (P ⬝ᵥ (ωb - q)) 0 * D₁ (0, 1) 0 = ωb 0 * D₁ (0, 1) 0 := by
        rw [← add_mul]
        congr 1
        linarith
      linarith
    · refine ⟨(0, e), ?_⟩
      rw [hA]
      exact mul_ne_zero hv.ne' (sub_ne_zero.2 ha)
  obtain ⟨y, hy⟩ := hdir
  refine LinearMap.range_eq_top.2 fun T => ⟨(T 0 / D y 0) • y, ?_⟩
  funext k
  rw [Subsingleton.elim k 0]
  change D ((T 0 / D y 0) • y) 0 = T 0
  rw [map_smul, Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ _ hy]

/-- The endowments of consumer 1 with `0 ≪ ω₁ ≪ ω̄`. -/
def d4Region (ωb : Fin 2 → ℝ) : Set (Fin 2 → ℝ) :=
  {q | q ∈ posOrthant 2 ∧ ωb - q ∈ posOrthant 2}

theorem isOpen_d4Region (ωb : Fin 2 → ℝ) : IsOpen (d4Region ωb) :=
  (isOpen_posOrthant 2).inter ((isOpen_posOrthant 2).preimage (continuous_const.sub continuous_id))

/-- The system is `C¹` on `{p₁ > 0} × {0 ≪ ω₁ ≪ ω̄}` when the demands are `C¹`. -/
theorem contDiffOn_d4Sys (hx : ∀ i, ContDiffOn ℝ 1 (d4X x i) (posOrthant 2 ×ˢ Set.Ioi 0)) :
    ContDiffOn ℝ 1 (d4Sys x ωb) (posOrthant 1 ×ˢ d4Region ωb) := by
  have hvec : ContDiff ℝ 1 fun z : (Fin 1 → ℝ) × (Fin 2 → ℝ) => (![z.1 0, 1] : Fin 2 → ℝ) := by
    refine contDiff_pi.2 fun j => ?_
    fin_cases j
    · change ContDiff ℝ 1 fun z : (Fin 1 → ℝ) × (Fin 2 → ℝ) => z.1 0
      exact (contDiff_apply ℝ ℝ 0).comp contDiff_fst
    · change ContDiff ℝ 1 fun _ : (Fin 1 → ℝ) × (Fin 2 → ℝ) => (1 : ℝ)
      exact contDiff_const
  have hdot : ∀ g : (Fin 1 → ℝ) × (Fin 2 → ℝ) → Fin 2 → ℝ, ContDiff ℝ 1 g →
      ContDiff ℝ 1 fun z => (![z.1 0, 1] : Fin 2 → ℝ) ⬝ᵥ g z := by
    intro g hg
    simp only [dotProduct]
    exact ContDiff.sum fun l _ => ((contDiff_apply ℝ ℝ l).comp hvec).mul
      ((contDiff_apply ℝ ℝ l).comp hg)
  have hmaps : ∀ g : (Fin 1 → ℝ) × (Fin 2 → ℝ) → Fin 2 → ℝ,
      (∀ z ∈ posOrthant 1 ×ˢ d4Region ωb, g z ∈ posOrthant 2) →
      Set.MapsTo (fun z : (Fin 1 → ℝ) × (Fin 2 → ℝ) => ((![z.1 0, 1] : Fin 2 → ℝ),
        (![z.1 0, 1] : Fin 2 → ℝ) ⬝ᵥ g z)) (posOrthant 1 ×ˢ d4Region ωb)
        (posOrthant 2 ×ˢ Set.Ioi 0) := by
    intro g hg z hz
    have hp : (![z.1 0, 1] : Fin 2 → ℝ) ∈ posOrthant 2 := vec2_mem_posOrthant (hz.1 0) one_pos
    exact ⟨hp, Finset.sum_pos (fun l _ => mul_pos (hp l) (hg z hz l)) Finset.univ_nonempty⟩
  refine contDiffOn_pi.2 fun k => ?_
  have hk : (fun z => d4Sys x ωb z k) = fun z => x 0 ![z.1 0, 1] (![z.1 0, 1] ⬝ᵥ z.2) 0 +
      x 1 ![z.1 0, 1] (![z.1 0, 1] ⬝ᵥ (ωb - z.2)) 0 - ωb 0 := by
    funext z
    rw [Subsingleton.elim k 0, d4Sys_apply]
  rw [hk]
  refine ContDiffOn.sub (ContDiffOn.add ?_ ?_) contDiffOn_const
  · exact (contDiffOn_pi.1 (hx 0) 0).comp ((hvec.prodMk (hdot _ contDiff_snd)).contDiffOn)
      (hmaps _ fun z hz => hz.2.1)
  · exact (contDiffOn_pi.1 (hx 1) 0).comp ((hvec.prodMk
      (hdot _ (contDiff_const.sub contDiff_snd))).contDiffOn) (hmaps _ fun z hz => hz.2.2)

/-- **Exercise 17.D.4** (MWG, p. 644). Two goods, two consumers with `C¹` demand functions whose
own substitution effects `∂x₁ᵢ/∂p₁ + x₁ᵢ ∂x₁ᵢ/∂w` are negative, and a fixed total endowment
`ω̄`. For almost every `ω₁` with `0 ≪ ω₁ ≪ ω̄`, the economy with endowments `(ω₁, ω̄ - ω₁)` is
regular. -/
theorem exercise_17_D_4 (hx : ∀ i, ContDiffOn ℝ 1 (d4X x i) (posOrthant 2 ×ˢ Set.Ioi 0))
    (hS : ∀ i p w, p ∈ posOrthant 2 → 0 < w →
      (fderiv ℝ (d4X x i) (p, w)) (Pi.single 0 1, 0) 0 +
        x i p w 0 * (fderiv ℝ (d4X x i) (p, w)) (0, 1) 0 < 0) :
    volume {q | q ∈ d4Region ωb ∧ ¬ IsRegularEconomy (demandED x ![q, ωb - q])} = 0 := by
  have hA := isOpen_posOrthant 1
  have hB := isOpen_d4Region ωb
  have hf := contDiffOn_d4Sys hx (ωb := ωb)
  have hdiff : ∀ z ∈ posOrthant 1 ×ˢ d4Region ωb, DifferentiableAt ℝ (d4Sys x ωb) z :=
    fun z hz => (hf.contDiffAt ((hA.prod hB).mem_nhds hz)).differentiableAt one_ne_zero
  have hxd : ∀ i p w, p ∈ posOrthant 2 → 0 < w → HasFDerivAt (d4X x i)
      (fderiv ℝ (d4X x i) (p, w)) (p, w) := fun i p w hp hw =>
    ((hx i).contDiffAt (((isOpen_posOrthant 2).prod isOpen_Ioi).mem_nhds
      (show (p, w) ∈ posOrthant 2 ×ˢ Set.Ioi (0 : ℝ) from ⟨hp, hw⟩))).differentiableAt
        one_ne_zero |>.hasFDerivAt
  refine measure_mono_null (fun q hq => ?_) (theorem_M_E_2 hA hB hf fun z hz hz0 => ?_)
  · obtain ⟨hqB, hnot⟩ := hq
    simp only [IsRegularEconomy, not_forall] at hnot
    obtain ⟨v, hv, hnreg⟩ := hnot
    have hvA : v ∈ posOrthant 1 := normPrice_mem_posOrthant.1 hv.1
    have hd := hdiff (v, q) ⟨hvA, hqB⟩
    have hpart := fderiv_partial_left hd
    refine ⟨hqB, v, hvA, hv.normED_eq_zero, fun hinv => hnreg ⟨hv, hpart.differentiableAt, ?_⟩⟩
    have : fderiv ℝ (normED (demandED x ![q, ωb - q])) v =
        (fderiv ℝ (d4Sys x ωb) (v, q)).comp (ContinuousLinearMap.inl ℝ _ _) := hpart.fderiv
    rw [this]
    exact (isInvertible_iff_det_ne_zero _).1 hinv
  · obtain ⟨v, q⟩ := z
    have hp : (![v 0, 1] : Fin 2 → ℝ) ∈ posOrthant 2 := vec2_mem_posOrthant (hz.1 0) one_pos
    have hw0 : 0 < (![v 0, 1] : Fin 2 → ℝ) ⬝ᵥ q :=
      Finset.sum_pos (fun l _ => mul_pos (hp l) (hz.2.1 l)) Finset.univ_nonempty
    have hw1 : 0 < (![v 0, 1] : Fin 2 → ℝ) ⬝ᵥ (ωb - q) :=
      Finset.sum_pos (fun l _ => mul_pos (hp l) (hz.2.2 l)) Finset.univ_nonempty
    exact d4_rank (hdiff _ hz) (hz.1 0) hz0 (hxd 0 _ _ hp hw0) (hxd 1 _ _ hp hw1)
      (hS 0 _ _ hp hw0) (hS 1 _ _ hp hw1)

/-- **Exercise 17.D.4**: with (i)-(v) for every such economy (e.g. strongly monotone preferences,
Proposition 17.B.2), for almost every `0 ≪ ω₁ ≪ ω̄` the economy has finitely many normalized
equilibria (Proposition 17.D.1). -/
theorem exercise_17_D_4_finite (hx : ∀ i, ContDiffOn ℝ 1 (d4X x i) (posOrthant 2 ×ˢ Set.Ioi 0))
    (hS : ∀ i p w, p ∈ posOrthant 2 → 0 < w →
      (fderiv ℝ (d4X x i) (p, w)) (Pi.single 0 1, 0) 0 +
        x i p w 0 * (fderiv ℝ (d4X x i) (p, w)) (0, 1) 0 < 0)
    (hstd : ∀ q ∈ d4Region ωb, IsStandardExcessDemand (demandED x ![q, ωb - q])) :
    ∀ᵐ q, q ∈ d4Region ωb → {v | IsNormEqm (demandED x ![q, ωb - q]) v}.Finite := by
  rw [ae_iff]
  refine measure_mono_null (fun q hq => ?_) (exercise_17_D_4 hx hS (ωb := ωb))
  simp only [Set.mem_ofPred_eq, Classical.not_imp] at hq
  exact ⟨hq.1, fun hreg => hq.2 (proposition_17_D_1_finite (hstd q hq.1) hreg)⟩

/-- Cobb-Douglas own substitution effects are negative: with `α = a₀/(a₀ + a₁)`,
`∂x₀/∂p₀ + x₀ ∂x₀/∂w = -α(1-α)w/p₀² < 0`. -/
theorem cd_slutsky_neg {a : Fin 2 → ℝ} (ha : ∀ l, 0 < a l) {p : Fin 2 → ℝ}
    (hp : p ∈ posOrthant 2) {w : ℝ} (hw : 0 < w) :
    (fderiv ℝ (fun r : (Fin 2 → ℝ) × ℝ => cdDemand a r.1 r.2) (p, w)) (Pi.single 0 1, 0) 0 +
      cdDemand a p w 0 *
        (fderiv ℝ (fun r : (Fin 2 → ℝ) × ℝ => cdDemand a r.1 r.2) (p, w)) (0, 1) 0 < 0 := by
  set F := fun r : (Fin 2 → ℝ) × ℝ => cdDemand a r.1 r.2
  have hd : DifferentiableAt ℝ F (p, w) :=
    ((contDiffOn_cdDemand a).contDiffAt (((isOpen_posOrthant 2).prod isOpen_Ioi).mem_nhds
      (show (p, w) ∈ posOrthant 2 ×ˢ Set.Ioi (0 : ℝ) from ⟨hp, hw⟩))).differentiableAt
        one_ne_zero
  set α := a 0 / ∑ k, a k
  have hA : 0 < ∑ k, a k := Finset.sum_pos (fun k _ => ha k) Finset.univ_nonempty
  have hα1 : α < 1 := by
    rw [div_lt_one hA, Fin.sum_univ_two]
    linarith [ha 1]
  have hα0 : 0 < α := div_pos (ha 0) hA
  have hp0 := hp 0
  -- the derivative in `p₀`
  have h1 : (fderiv ℝ F (p, w)) (Pi.single 0 1, 0) 0 = -(α * w / p 0 ^ 2) := by
    have hline : HasDerivAt (fun s : ℝ => (p + s • Pi.single 0 1, w))
        ((Pi.single 0 1 : Fin 2 → ℝ), (0 : ℝ)) 0 := by
      refine HasDerivAt.prodMk ?_ (hasDerivAt_const (0 : ℝ) w)
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single 0 1 : Fin 2 → ℝ)).const_add p
    have h := hasDerivAt_pi.1 (hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)) 0
    have hl : HasDerivAt (fun s : ℝ => p 0 + s) 1 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_add (p 0)
    have hg : HasDerivAt (fun s : ℝ => α * (w / (p 0 + s))) (α * (-(w * 1) / (p 0 + 0) ^ 2)) 0 :=
      ((hasDerivAt_const (0 : ℝ) w).div hl (by simpa using hp0.ne')).const_mul α |>.congr_deriv
        (by ring)
    have := h.unique (by
      convert hg using 2 with s
      simp [F, cdDemand, α])
    rw [this]
    ring
  -- the derivative in `w`
  have h2 : (fderiv ℝ F (p, w)) (0, 1) 0 = α / p 0 := by
    have hline : HasDerivAt (fun s : ℝ => (p, w + s)) ((0 : Fin 2 → ℝ), (1 : ℝ)) 0 := by
      refine (hasDerivAt_const (0 : ℝ) p).prodMk ?_
      simpa using (hasDerivAt_id (0 : ℝ)).const_add w
    have h := hasDerivAt_pi.1 (hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)) 0
    have hg : HasDerivAt (fun s : ℝ => α * ((w + s) / p 0)) (α * (1 / p 0)) 0 := by
      have : HasDerivAt (fun s : ℝ => (w + s) / p 0) (1 / p 0) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).const_add w).div_const (p 0)
      exact this.const_mul α
    have := h.unique (by
      convert hg using 2 with s
      simp [F, cdDemand, α])
    rw [this]
    ring
  rw [h1, h2]
  have hx0 : cdDemand a p w 0 = α * (w / p 0) := rfl
  rw [hx0]
  have : -(α * w / p 0 ^ 2) + α * (w / p 0) * (α / p 0) = -(α * (1 - α) * w / p 0 ^ 2) := by
    field_simp
    ring
  rw [this, neg_lt_zero]
  have : 0 < 1 - α := by linarith
  positivity

/-- **Exercise 17.D.4**, instance: two Cobb-Douglas consumers (exponents `aᵢ ≫ 0`) and any
`ω̄ ≫ 0`. For almost every `0 ≪ ω₁ ≪ ω̄` the economy is regular and has finitely many
equilibria. -/
theorem exercise_17_D_4_cobbDouglas {a : Fin 2 → Fin 2 → ℝ} (ha : ∀ i l, 0 < a i l)
    {ωb : Fin 2 → ℝ} :
    ∀ᵐ q, q ∈ d4Region ωb →
      {v | IsNormEqm (demandED (fun i => cdDemand (a i)) ![q, ωb - q]) v}.Finite := by
  refine exercise_17_D_4_finite (fun i => contDiffOn_cdDemand (a i))
    (fun i p w hp hw => cd_slutsky_neg (ha i) hp hw) fun q hq => ?_
  refine cdED_isStandard ha (fun i => ?_) fun l => ?_
  · fin_cases i
    · exact fun l => (hq.1 l).le
    · exact fun l => (hq.2 l).le
  · have h1 := hq.1 l
    have h2 := hq.2 l
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Pi.sub_apply] at h2 ⊢
    linarith

end MWG.PositiveEquilibriumTheory
