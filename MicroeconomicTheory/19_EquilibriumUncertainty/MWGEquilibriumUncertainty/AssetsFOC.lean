/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGEquilibriumUncertainty.Assets

/-!
# Proof 2 of Proposition 19.E.1 and Exercise 19.E.1 (MWG pp. 703, 727)

* `foc_halfspace`: if `y` maximizes `F` near `y` on the half-space `{q·y' ≤ c}` and `F` has
  directional derivatives `a·d`, then `a = α q` with `α ≥ 0`.
* **Proof 2 of Proposition 19.E.1** for the reduced portfolio problem of footnote 18,
  `max ∑_s π_s v_s(p_s·ω_s + ∑_k r_{sk} z_k)` s.t. `q·z ≤ 0`, with `v_s` differentiable at the
  optimal wealth with positive derivative: `α q_k = ∑_s π_s v_s'(w*_s) r_{sk}` with `α > 0`, so
  `μ_s = π_s v_s'(w*_s) / α` (`proposition_19_E_1_proof2`). The book assumes the indirect
  utilities `v_s(p_s, ·)` differentiable; this is a hypothesis here (correction 4 records it).
* For one good (`L = 1`, `v_s = u_s`) the Radner problem reduces to footnote 18's
  (`proposition_19_E_1_proof2_radner`), with no differentiability assumption beyond `u_s`.
* **Exercise 19.E.1(a)-(b)**: consumption also at `t = 0` (utility `u₀(x₀) + ∑_s π_s v_s`): the
  conclusion holds, and with one good `μ_s = π_s u₁'(x_{1s}) / u₀'(x₀)`.
-/

namespace MWG.EquilibriumUncertainty

open Filter Topology Matrix

variable {S L K : ℕ}

/-- **Lagrange condition on a half-space.** If `y` maximizes `F` on `N ∩ {q·y' ≤ c}` for a
neighborhood `N` of `y`, and the derivative of `F` at `y` in every direction `d` is `a·d`, then
`a = α q` for some `α ≥ 0`. -/
theorem foc_halfspace {n : Type*} [Fintype n] {F : (n → ℝ) → ℝ} {y q a : n → ℝ} {c : ℝ}
    {N : Set (n → ℝ)} (hN : N ∈ 𝓝 y) (hmax : ∀ y' ∈ N, q ⬝ᵥ y' ≤ c → F y' ≤ F y)
    (hy : q ⬝ᵥ y ≤ c) (hder : ∀ d, HasDerivAt (fun t : ℝ => F (y + t • d)) (a ⬝ᵥ d) 0) :
    ∃ α : ℝ, 0 ≤ α ∧ a = α • q := by
  refine exists_nonneg_smul_of_dot_nonpos fun d hd => hasDerivAt_nonpos_of_eventually_le
    (hder d) ?_
  have hc : Tendsto (fun t : ℝ => y + t • d) (𝓝 0) (𝓝 y) := by
    have := (tendsto_const_nhds (x := y)).add ((tendsto_id (x := 𝓝 (0 : ℝ))).smul_const d)
    simpa using this
  have h1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), y + t • d ∈ N :=
    (hc.eventually (Filter.eventually_of_mem hN fun _ h => h)).filter_mono nhdsWithin_le_nhds
  filter_upwards [h1, self_mem_nhdsWithin] with t ht htpos
  simp only [zero_smul, add_zero]
  refine hmax _ ht ?_
  rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
  have : t * (q ⬝ᵥ d) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt htpos) hd
  linarith

/-- The reduced portfolio objective of footnote 18: `∑_s π_s v_s(w₀_s + (Rz)_s)`. -/
def portfolioObjective (π : Fin S → ℝ) (v : Fin S → ℝ → ℝ) (w₀ : Fin S → ℝ)
    (R : Matrix (Fin S) (Fin K) ℝ) (z : Fin K → ℝ) : ℝ :=
  ∑ s, π s * v s (w₀ s + (R *ᵥ z) s)

/-- The directional derivative of the portfolio objective. -/
theorem hasDerivAt_portfolioObjective {π : Fin S → ℝ} {v : Fin S → ℝ → ℝ} {w₀ : Fin S → ℝ}
    {R : Matrix (Fin S) (Fin K) ℝ} {z : Fin K → ℝ} {dv : Fin S → ℝ}
    (hdv : ∀ s, HasDerivAt (v s) (dv s) (w₀ s + (R *ᵥ z) s)) (d : Fin K → ℝ) :
    HasDerivAt (fun t : ℝ => portfolioObjective π v w₀ R (z + t • d))
      ((fun k => ∑ s, π s * dv s * R s k) ⬝ᵥ d) 0 := by
  have hval : (fun k => ∑ s, π s * dv s * R s k) ⬝ᵥ d = ∑ s, π s * (dv s * (R *ᵥ d) s) := by
    simp only [dotProduct, mulVec, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun k _ => by ring
  rw [hval]
  have hfun : (fun t : ℝ => portfolioObjective π v w₀ R (z + t • d)) =
      fun t => ∑ s, π s * v s (w₀ s + (R *ᵥ z) s + t * (R *ᵥ d) s) := by
    funext t
    simp only [portfolioObjective, mulVec_add, mulVec_smul, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, add_assoc]
  rw [hfun]
  refine HasDerivAt.fun_sum fun s _ => HasDerivAt.const_mul _ ?_
  have hin : HasDerivAt (fun t : ℝ => w₀ s + (R *ᵥ z) s + t * (R *ᵥ d) s) ((R *ᵥ d) s) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).mul_const ((R *ᵥ d) s)).const_add (w₀ s + (R *ᵥ z) s)
    simpa using this
  have hout : HasDerivAt (v s) (dv s) (w₀ s + (R *ᵥ z) s + 0 * (R *ᵥ d) s) := by
    simpa using hdv s
  exact hout.comp (0 : ℝ) hin

/-- **Proposition 19.E.1, Proof 2** (MWG, p. 703), for the reduced problem of footnote 18. Let the
portfolio `z*` maximize `∑_s π_s v_s(w₀_s + (Rz)_s)` subject to `q·z ≤ 0` near `z*` (short sales
are unlimited, so `z*` is interior), with `π ≫ 0`, nonnegative nonzero returns and `v_s`
differentiable at `w*_s` with `v_s'(w*_s) > 0`. Then for some `α > 0`,
`α q_k = ∑_s π_s v_s'(w*_s) r_{sk}` (the first-order conditions), and with
`μ_s = π_s v_s'(w*_s) / α ≥ 0`, `q_k = ∑_s μ_s r_{sk}`. -/
theorem proposition_19_E_1_proof2 {π : Fin S → ℝ} (hπ : ∀ s, 0 < π s) {v : Fin S → ℝ → ℝ}
    {w₀ : Fin S → ℝ} {R : Matrix (Fin S) (Fin K) ℝ} (hR : NonnegNonzeroReturns R)
    {q z : Fin K → ℝ} {N : Set (Fin K → ℝ)} (hN : N ∈ 𝓝 z)
    (hmax : ∀ z' ∈ N, q ⬝ᵥ z' ≤ 0 →
      portfolioObjective π v w₀ R z' ≤ portfolioObjective π v w₀ R z) (hz : q ⬝ᵥ z ≤ 0)
    {dv : Fin S → ℝ} (hdv : ∀ s, HasDerivAt (v s) (dv s) (w₀ s + (R *ᵥ z) s))
    (hpos : ∀ s, 0 < dv s) :
    ∃ α : ℝ, 0 < α ∧ (∀ k, α * q k = ∑ s, π s * dv s * R s k) ∧
      ∀ k, q k = ∑ s, (π s * dv s / α) * R s k := by
  obtain ⟨α, hα, ha⟩ := foc_halfspace hN hmax hz (hasDerivAt_portfolioObjective hdv)
  have hfoc : ∀ k, α * q k = ∑ s, π s * dv s * R s k := fun k => by
    have := congrFun ha k; simp only [Pi.smul_apply, smul_eq_mul] at this; linarith
  have hαpos : 0 < α ∨ IsEmpty (Fin K) := by
    rcases isEmpty_or_nonempty (Fin K) with hK | ⟨⟨k⟩⟩
    · exact Or.inr hK
    · left
      obtain ⟨s, hs⟩ := hR.2 k
      have hRs : 0 < R s k := lt_of_le_of_ne (hR.1 s k) (Ne.symm hs)
      have hsum : 0 < ∑ s, π s * dv s * R s k :=
        lt_of_lt_of_le (mul_pos (mul_pos (hπ s) (hpos s)) hRs)
          (Finset.single_le_sum (f := fun s => π s * dv s * R s k)
            (fun s _ => mul_nonneg (mul_nonneg (hπ s).le (hpos s).le) (hR.1 s k))
            (Finset.mem_univ s))
      rcases hα.lt_or_eq with h' | h'
      · exact h'
      · have := hfoc k; rw [← h', zero_mul] at this; linarith
  rcases hαpos with hαpos | hK
  · refine ⟨α, hαpos, hfoc, fun k => ?_⟩
    have : ∑ s, π s * dv s / α * R s k = (∑ s, π s * dv s * R s k) / α := by
      rw [Finset.sum_div]; exact Finset.sum_congr rfl fun s _ => by ring
    rw [this, ← hfoc k]; field_simp
  · exact ⟨1, one_pos, fun k => isEmptyElim k, fun k => isEmptyElim k⟩

/-- **Proposition 19.E.1, Proof 2** (MWG, p. 703), from a Radner equilibrium with one good
(`L = 1`, spot price `p_s = 1`, so `v_s = u_s`). A consumer with expected utility
`∑_s π_s u_s(x_s)`, `π ≫ 0`, strictly increasing `u_s` differentiable at `x*_s` with
`u_s'(x*_s) > 0`, and interior consumption `x* ≫ 0` solves the reduced portfolio problem;
hence `q_k = ∑_s μ_s r_{sk}` with `μ_s = π_s u_s'(x*_s) / α`. -/
theorem proposition_19_E_1_proof2_radner {ι : Type*} [Fintype ι] {R : Matrix (Fin S) (Fin K) ℝ}
    (hR : NonnegNonzeroReturns R) {U : ι → CVec S 1 → ℝ} {ω x : ι → CVec S 1} {q : Fin K → ℝ}
    {z : ι → Fin K → ℝ} (h : IsRadnerEqm 0 R U ω q (fun _ _ => 1) x z) (i : ι)
    {π : Fin S → ℝ} (hπ : ∀ s, 0 < π s) {u : Fin S → ℝ → ℝ} (hU : U i = eu1 π u)
    (hsm : ∀ s, StrictMonoOn (u s) (Set.Ici 0)) (hx : ∀ s, 0 < x i s 0) {du : Fin S → ℝ}
    (hdu : ∀ s, HasDerivAt (u s) (du s) (x i s 0)) (hpos : ∀ s, 0 < du s) :
    ∃ α : ℝ, 0 < α ∧ ∀ k, q k = ∑ s, (π s * du s / α) * R s k := by
  -- the spot budgets bind, since every `u_s` is strictly increasing
  have hbind : ∀ s, x i s 0 = ω i s 0 + (R *ᵥ z i) s := by
    intro s
    obtain ⟨⟨hx0, hqz, hsp⟩, hopt⟩ := h.1 i
    have hle : x i s 0 ≤ ω i s 0 + (R *ᵥ z i) s := by simpa [dotProduct] using hsp s
    by_contra hne
    have hlt : x i s 0 < ω i s 0 + (R *ᵥ z i) s := lt_of_le_of_ne hle hne
    set x' : CVec S 1 := Function.update (x i) s fun _ => ω i s 0 + (R *ᵥ z i) s
    have hfeas : radnerFeasible 0 R q (fun _ _ => 1) (ω i) x' (z i) := by
      refine ⟨fun s' l => ?_, hqz, fun s' => ?_⟩
      · by_cases hs : s' = s
        · subst hs; simp only [x', Function.update_self]; linarith [hx0 s' 0, hle]
        · simp only [x', Function.update_of_ne hs]; exact hx0 s' l
      · by_cases hs : s' = s
        · subst hs; simp [x', dotProduct]
        · simp only [x', Function.update_of_ne hs]; exact hsp s'
    have h1 := (h.1 i).2 _ _ hfeas
    rw [hU] at h1
    have h2 : eu1 π u (x i) < eu1 π u x' := by
      unfold eu1
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ s),
        ← Finset.add_sum_erase _ _ (Finset.mem_univ s)]
      have e : ∑ t ∈ Finset.univ.erase s, π t * u t (x' t 0) =
          ∑ t ∈ Finset.univ.erase s, π t * u t (x i t 0) :=
        Finset.sum_congr rfl fun t ht => by
          simp only [x', Function.update_of_ne (Finset.ne_of_mem_erase ht)]
      rw [e]
      simp only [x', Function.update_self]
      have := hsm s (Set.mem_Ici.mpr (hx s).le) (Set.mem_Ici.mpr ((hx s).le.trans hle)) hlt
      nlinarith [hπ s]
    linarith
  have hcs : ∀ s, Continuous fun z' : Fin K → ℝ => ω i s 0 + (R *ᵥ z') s := fun s =>
    continuous_const.add ((continuous_apply s).comp
      (continuous_const.matrix_mulVec continuous_id))
  set N : Set (Fin K → ℝ) := {z' | ∀ s, 0 < ω i s 0 + (R *ᵥ z') s} with hNdef
  have hNopen : IsOpen N := by
    have : N = ⋂ s, {z' | 0 < ω i s 0 + (R *ᵥ z') s} := by ext; simp [hNdef]
    rw [this]
    exact isOpen_iInter_of_finite fun s => isOpen_lt continuous_const (hcs s)
  have hzN : z i ∈ N := fun s => by rw [← hbind s]; exact hx s
  have hmax : ∀ z' ∈ N, q ⬝ᵥ z' ≤ 0 → portfolioObjective π u (fun s => ω i s 0) R z' ≤
      portfolioObjective π u (fun s => ω i s 0) R (z i) := by
    intro z' hz' hq
    -- the plan `x' = ω + R z'` is Radner feasible
    have hfeas : radnerFeasible 0 R q (fun _ _ => 1) (ω i)
        (fun s _ => ω i s 0 + (R *ᵥ z') s) z' := by
      refine ⟨fun s l => (hz' s).le, hq, fun s => ?_⟩
      simp [dotProduct]
    have h1 := (h.1 i).2 _ _ hfeas
    rw [hU] at h1
    have h2 : eu1 π u (x i) = portfolioObjective π u (fun s => ω i s 0) R (z i) := by
      simp only [eu1, portfolioObjective, hbind]
    have h3 : eu1 π u (fun s _ => ω i s 0 + (R *ᵥ z') s) =
        portfolioObjective π u (fun s => ω i s 0) R z' := rfl
    rw [← h2, ← h3]
    exact h1
  obtain ⟨α, hα, -, hμ⟩ := proposition_19_E_1_proof2 (v := u) (w₀ := fun s => ω i s 0) hπ hR
    (hNopen.mem_nhds hzN) hmax (h.1 i).1.2.1 (fun s => by rw [← hbind s]; exact hdu s) hpos
  exact ⟨α, hα, hμ⟩

/-! ## Exercise 19.E.1: consumption at `t = 0` -/

/-- **Exercise 19.E.1(a)** (MWG, p. 727). With consumption also at `t = 0` and utility
`u₀(x₀) + ∑_s π_s v_s(w_s)`, let `(x₀*, z*)` maximize it near `(x₀*, z*)` subject to
`p₀·x₀ + q·z ≤ p₀·ω₀`, with `u₀` having gradient `∇u₀` (directional derivatives `∇u₀·d`) and the
hypotheses of Proof 2. Then `∇u₀(x₀*) = α p₀` and `α q_k = ∑_s π_s v_s' r_{sk}` for one `α ≥ 0`;
if `α > 0` (e.g. `u₀` strictly increasing in a good with positive price), the conclusion of
Proposition 19.E.1 holds with `μ_s = π_s v_s' / α`. -/
theorem exercise_19_E_1a {π : Fin S → ℝ} {v : Fin S → ℝ → ℝ} {w₀ : Fin S → ℝ}
    {R : Matrix (Fin S) (Fin K) ℝ} {u₀ : (Fin L → ℝ) → ℝ} {p₀ ω₀ x₀ : Fin L → ℝ} {q z : Fin K → ℝ}
    {N : Set ((Fin L ⊕ Fin K) → ℝ)} (hN : N ∈ 𝓝 (Sum.elim x₀ z))
    (hmax : ∀ y' ∈ N, p₀ ⬝ᵥ (y' ∘ Sum.inl) + q ⬝ᵥ (y' ∘ Sum.inr) ≤ p₀ ⬝ᵥ ω₀ →
      u₀ (y' ∘ Sum.inl) + portfolioObjective π v w₀ R (y' ∘ Sum.inr) ≤
        u₀ x₀ + portfolioObjective π v w₀ R z)
    (hb : p₀ ⬝ᵥ x₀ + q ⬝ᵥ z ≤ p₀ ⬝ᵥ ω₀) {gu : Fin L → ℝ}
    (hgu : ∀ d, HasDerivAt (fun t : ℝ => u₀ (x₀ + t • d)) (gu ⬝ᵥ d) 0) {dv : Fin S → ℝ}
    (hdv : ∀ s, HasDerivAt (v s) (dv s) (w₀ s + (R *ᵥ z) s)) :
    ∃ α : ℝ, 0 ≤ α ∧ gu = α • p₀ ∧ ∀ k, α * q k = ∑ s, π s * dv s * R s k := by
  set F : ((Fin L ⊕ Fin K) → ℝ) → ℝ :=
    fun y' => u₀ (y' ∘ Sum.inl) + portfolioObjective π v w₀ R (y' ∘ Sum.inr) with hF
  set a : (Fin L ⊕ Fin K) → ℝ := Sum.elim gu fun k => ∑ s, π s * dv s * R s k with ha
  have hdot : ∀ y' : (Fin L ⊕ Fin K) → ℝ,
      Sum.elim p₀ q ⬝ᵥ y' = p₀ ⬝ᵥ (y' ∘ Sum.inl) + q ⬝ᵥ (y' ∘ Sum.inr) := by
    intro y'
    rw [← Sum.elim_comp_inl_inr y', sumElim_dotProduct_sumElim, Sum.elim_comp_inl_inr]
  obtain ⟨α, hα, hav⟩ := foc_halfspace (F := F) (q := Sum.elim p₀ q) (c := p₀ ⬝ᵥ ω₀) (a := a)
    hN (fun y' hy' hq => by rw [hdot] at hq; exact hmax y' hy' hq)
    (by rw [hdot]; simpa using hb) (fun d => by
      have h1 := hgu (d ∘ Sum.inl)
      have h2 := hasDerivAt_portfolioObjective (π := π) (w₀ := w₀) hdv (d ∘ Sum.inr)
      have e : a ⬝ᵥ d = gu ⬝ᵥ (d ∘ Sum.inl) +
          (fun k => ∑ s, π s * dv s * R s k) ⬝ᵥ (d ∘ Sum.inr) := by
        rw [ha, ← Sum.elim_comp_inl_inr d, sumElim_dotProduct_sumElim, Sum.elim_comp_inl_inr]
      rw [e]
      have hfun : (fun t : ℝ => F (Sum.elim x₀ z + t • d)) =
          (fun t : ℝ => u₀ (x₀ + t • (d ∘ Sum.inl))) +
            fun t : ℝ => portfolioObjective π v w₀ R (z + t • (d ∘ Sum.inr)) := by
        funext t
        simp only [hF, Pi.add_apply]
        congr 2
      rw [hfun]
      exact h1.add h2)
  refine ⟨α, hα, funext fun l => ?_, fun k => ?_⟩
  · have := congrFun hav (Sum.inl l); simpa [ha] using this
  · have := congrFun hav (Sum.inr k); simp [ha] at this; linarith

/-- **Exercise 19.E.1(b)** (MWG, p. 727). With a single good at both dates (price `1` at `t = 0`
and spot prices `1`), the multipliers are `μ_s = π_s u₁'(x_{1s}) / u₀'(x₀)`: the ratio of the
marginal utility of one unit of consumption in state `s` (weighted by `π_s`) to the marginal
utility of consumption at `t = 0`. -/
theorem exercise_19_E_1b {π : Fin S → ℝ} {u₁ : ℝ → ℝ} {w₀ : Fin S → ℝ}
    {R : Matrix (Fin S) (Fin K) ℝ} {u₀ : ℝ → ℝ} {ω₀ x₀ : ℝ} {q z : Fin K → ℝ}
    {N : Set ((Fin 1 ⊕ Fin K) → ℝ)} (hN : N ∈ 𝓝 (Sum.elim (fun _ => x₀) z))
    (hmax : ∀ y' ∈ N, y' (Sum.inl 0) + q ⬝ᵥ (y' ∘ Sum.inr) ≤ ω₀ →
      u₀ (y' (Sum.inl 0)) + portfolioObjective π (fun _ => u₁) w₀ R (y' ∘ Sum.inr) ≤
        u₀ x₀ + portfolioObjective π (fun _ => u₁) w₀ R z)
    (hb : x₀ + q ⬝ᵥ z ≤ ω₀) {du₀ : ℝ} (hdu₀ : HasDerivAt u₀ du₀ x₀) (hpos : 0 < du₀)
    {du₁ : Fin S → ℝ} (hdu₁ : ∀ s, HasDerivAt u₁ (du₁ s) (w₀ s + (R *ᵥ z) s)) :
    ∀ k, q k = ∑ s, (π s * du₁ s / du₀) * R s k := by
  have hgu : ∀ d : Fin 1 → ℝ, HasDerivAt (fun t : ℝ => u₀ (((fun (_ : Fin 1) => x₀) + t • d) 0))
      ((fun _ => du₀) ⬝ᵥ d) 0 := by
    intro d
    have hin : HasDerivAt (fun t : ℝ => x₀ + t * d 0) (d 0) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (d 0)).const_add x₀
    have := (show HasDerivAt u₀ du₀ (x₀ + 0 * d 0) by simpa using hdu₀).comp (0 : ℝ) hin
    have e : (fun _ => du₀) ⬝ᵥ d = du₀ * d 0 := by simp [dotProduct]
    rw [e]
    exact this
  obtain ⟨α, _, hg, hq⟩ := exercise_19_E_1a (L := 1) (u₀ := fun y => u₀ (y 0))
    (p₀ := fun _ => 1) (ω₀ := fun _ => ω₀) (x₀ := fun _ => x₀) (v := fun _ => u₁) (π := π)
    (w₀ := w₀) (R := R) (q := q) (z := z) (N := N) hN
    (fun y' hy' hq' => by
      have := hmax y' hy' (by simpa [dotProduct] using hq')
      simpa using this) (by simpa [dotProduct] using hb) hgu hdu₁
  have hα : α = du₀ := by have := congrFun hg 0; simp at this; linarith
  subst hα
  intro k
  have : ∑ s, π s * du₁ s / α * R s k = (∑ s, π s * du₁ s * R s k) / α := by
    rw [Finset.sum_div]; exact Finset.sum_congr rfl fun s _ => by ring
  rw [this, ← hq k]; field_simp

end MWG.EquilibriumUncertainty
