/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGMarketPower.NashReversion
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Severer punishments: stick-and-carrot strategies

MWG, Propositions 12.AA.1 and 12.AA.4, Exercise 12.AA.2 and Example 12.AA.1, pp. 419-423.

A three-state automaton (`scProfile`): in the *stick* state play `s`; if everybody conforms move
to the *carrot* state, where `c` is played as long as nobody deviates; a deviation in the stick
state restarts the stick, a deviation in the carrot state moves to the target state `tgt` (the
stick again, or the *Nash* state, where the stage Nash equilibrium `n` is played forever).

* `scProfile_spne`: the automaton is an SPNE when the stick is a credible one-period punishment,
  `π_i(a, s_{-i}) ≤ (1 − δ)π_i(s) + δπ_i(c)`, and deviations from the carrot are deterred.
* `stage_pareto_improvement`, `proposition_12_AA_1`: near `q*`, with differentiable payoffs,
  nonzero cross partials and the envelope property (12.AA.6), a Pareto improvement satisfies
  (12.AA.3) for every `δ > 0`, so its repetition is sustained by Nash reversion.
* `stage_severe_punishment`, `proposition_12_AA_4` (Exercise 12.AA.2): under the same
  conditions, some stick-and-carrot SPNE gives both players average payoffs below `π_i(q*)`.
* `example_12_AA_1`: the Cournot stick-and-carrot equilibrium with average payoff zero, and
  `example_12_AA_1_qbar`: the stick `q̄ ≥ q_c` solving (12.AA.7) exists for `δ` near `1`;
  `example_12_AA_1_instance`: a linear instance.

Departure: Propositions 12.AA.1 and 12.AA.4 are proved under the envelope property (12.AA.6)
(`π̂_i` differentiable at `q_j*` with derivative `∂π_i(q*)/∂q_j`), which MWG's proof invokes;
MWG lists only the differentiability of `π_i` at `q*`; without (12.AA.6) both propositions
are false (`StickCarrotLiteral`).
-/

namespace MWG.MarketPower

open MWG.DynamicGames Function Filter Topology

variable {I : Type*} [DecidableEq I] {A : I → Type*}

/-- The profile prescribed in the stick (`0`), carrot (`1`) and Nash (`2`) states. -/
def scPresc (s c n : (i : I) → A i) : Fin 3 → (i : I) → A i
  | 0 => s
  | 1 => c
  | 2 => n

open Classical in
/-- The transitions of the stick-and-carrot automaton. -/
noncomputable def scTrans (s c : (i : I) → A i) (tgt : Fin 3) : Fin 3 → ((i : I) → A i) → Fin 3
  | 0, x => if x = s then 1 else 0
  | 1, x => if x = c then 1 else tgt
  | 2, _ => 2

/-- The state after a history (play starts in the stick state). -/
noncomputable def scStateOf (s c : (i : I) → A i) (tgt : Fin 3) : OSHist A → Fin 3
  | [] => 0
  | x :: h => scTrans s c tgt (scStateOf s c tgt h) x

/-- The stick-and-carrot profile. -/
noncomputable def scProfile (s c n : (i : I) → A i) (tgt : Fin 3) : OSProfile A :=
  fun i h => scPresc s c n (scStateOf s c tgt h) i

/-- The value of each state. -/
noncomputable def scVal (g : I → ((i : I) → A i) → ℝ) (δ : ℝ) (s c n : (i : I) → A i) (i : I) :
    Fin 3 → ℝ
  | 0 => g i s + δ * (g i c / (1 - δ))
  | 1 => g i c / (1 - δ)
  | 2 => g i n / (1 - δ)

omit [DecidableEq I] in
theorem scTrans_conform (s c n : (i : I) → A i) (tgt : Fin 3) (k : Fin 3) :
    scTrans s c tgt k (scPresc s c n k) = if k = 2 then 2 else 1 := by
  fin_cases k <;> simp [scTrans, scPresc]

theorem scTrans_deviate (s c n : (i : I) → A i) (tgt : Fin 3) (k : Fin 3) {i : I} {a : A i}
    (ha : a ≠ scPresc s c n k i) :
    scTrans s c tgt k (update (scPresc s c n k) i a) =
      if k = 0 then 0 else if k = 1 then tgt else 2 := by
  have hne : update (scPresc s c n k) i a ≠ scPresc s c n k := by
    intro heq
    have := congrFun heq i
    rw [update_self] at this
    exact ha this
  fin_cases k <;> simp only [scPresc] at hne <;> simp [scTrans, scPresc, hne]

/-- **The stick-and-carrot automaton is an SPNE** under the one-shot conditions: `n` is a stage
Nash equilibrium; the stick is accepted, `π_i(a, s_{-i}) ≤ (1 − δ)π_i(s) + δπ_i(c)` for all `a`;
and every deviation from the carrot is deterred, `π_i(a, c_{-i}) + δV_tgt ≤ π_i(c)/(1 − δ)` for
`a ≠ c_i`. Its value from the start is `π_i(s) + δπ_i(c)/(1 − δ)`. -/
theorem scProfile_spne {g : I → ((i : I) → A i) → ℝ} {δ M : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hg : ∀ i x, |g i x| ≤ M) (s c n : (i : I) → A i) (tgt : Fin 3)
    (hn : IsStageNash g n)
    (hs : ∀ i a, g i (update s i a) ≤ (1 - δ) * g i s + δ * g i c)
    (hc : ∀ i a, a ≠ c i → g i (update c i a) + δ * scVal g δ s c n i tgt ≤ g i c / (1 - δ)) :
    IsRepeatedSPNE g δ (scProfile s c n tgt) ∧
      ∀ i, osValue (stageU g) δ (scProfile s c n tgt) [] i = g i s + δ * (g i c / (1 - δ)) := by
  have h1δ : (1 - δ) ≠ 0 := by linarith
  have h1δp : 0 < 1 - δ := by linarith
  have hB : ∀ i k, |scVal g δ s c n i k| ≤ M + M / (1 - δ) := by
    intro i k
    have hM0 : 0 ≤ M := (abs_nonneg _).trans (hg i s)
    have hdiv : ∀ x, |g i x / (1 - δ)| ≤ M / (1 - δ) := fun x => by
      rw [abs_div, abs_of_pos h1δp]; exact div_le_div_of_nonneg_right (hg i x) h1δp.le
    have hMd : 0 ≤ M / (1 - δ) := div_nonneg hM0 h1δp.le
    rcases (by fin_cases k <;> simp : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
    · simp only [scVal]
      refine (abs_add_le _ _).trans (add_le_add (hg i s) ?_)
      rw [abs_mul, abs_of_nonneg hδ0]
      calc δ * |g i c / (1 - δ)| ≤ 1 * (M / (1 - δ)) :=
            mul_le_mul (by linarith) (hdiv c) (abs_nonneg _) zero_le_one
        _ = M / (1 - δ) := one_mul _
    · simp only [scVal]; linarith [hdiv c]
    · simp only [scVal]; linarith [hdiv n]
  have hval : ∀ i h, osValue (stageU g) δ (scProfile s c n tgt) h i =
      scVal g δ s c n i (scStateOf s c tgt h) := by
    intro i h
    refine osValue_eq_of_rec hδ0 hδ1 (stageU_bound hg) _ i _ (fun h => hB i _) (fun h => ?_) h
    have hp : osPlay (scProfile s c n tgt) h = scPresc s c n (scStateOf s c tgt h) := rfl
    simp only [hp, scStateOf, scTrans_conform, stageU]
    generalize scStateOf s c tgt h = k
    rcases (by fin_cases k <;> simp : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl <;>
      simp [scVal, scPresc] <;> field_simp <;> ring
  refine ⟨?_, fun i => by rw [hval]; rfl⟩
  unfold IsRepeatedSPNE
  rw [oneShot_deviation_principle_discounted_iff hδ0 hδ1 (stageU_bound hg)]
  intro i h a
  have hp : osPlay (scProfile s c n tgt) h = scPresc s c n (scStateOf s c tgt h) := rfl
  by_cases ha : a = scPresc s c n (scStateOf s c tgt h) i
  · rw [hp, ha, update_eq_self, ← hp]
    exact (osValue_succ hδ0 hδ1 (stageU_bound hg) _ h i).ge
  rw [hval, hval, hp]
  simp only [scStateOf]
  rw [scTrans_deviate s c n tgt _ ha]
  simp only [stageU]
  generalize hk : scStateOf s c tgt h = k at ha ⊢
  rcases (by fin_cases k <;> simp : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
  · simp only [scVal, scPresc, ite_true]
    have := hs i a
    have e : g i s + δ * (g i c / (1 - δ)) =
        (1 - δ) * g i s + δ * g i c + δ * (g i s + δ * (g i c / (1 - δ))) := by
      field_simp; ring
    linarith
  · simp only [scPresc] at ha ⊢
    simp only [show ((1 : Fin 3) = 0) = False by decide, ite_false, ite_true]
    exact hc i a ha
  · simp only [scVal, scPresc, show ((2 : Fin 3) = 0) = False by decide,
      show ((2 : Fin 3) = 1) = False by decide, ite_false]
    have := hn i a
    have e : g i n / (1 - δ) = g i n + δ * (g i n / (1 - δ)) := by field_simp; ring
    linarith

/-! ### Local constructions near `q*` -/

/-- Along a ray with common slope `a > 0`, the payoff `f` rises and the deviation gain `h − f`
is small relative to it: for every `κ > 0`, eventually (as `s ↓ 0`) `f(0) < f(s)` and
`h(s) − f(s) ≤ κ(f(s) − f(0))`. -/
theorem stage_local_pos {f h : ℝ → ℝ} {a κ : ℝ} (hf : HasDerivAt f a 0) (hh : HasDerivAt h a 0)
    (h0 : f 0 = h 0) (ha : 0 < a) (hκ : 0 < κ) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), f 0 < f s ∧ h s - f s ≤ κ * (f s - f 0) := by
  set ε := min (a / 2) (κ * a / 4) with hε
  have hεpos : 0 < ε := lt_min (by linarith) (by positivity)
  have hf' := (hf.isLittleO.bound hεpos)
  have hh' := (hh.isLittleO.bound hεpos)
  filter_upwards [nhdsWithin_le_nhds hf', nhdsWithin_le_nhds hh', self_mem_nhdsWithin]
    with s h1 h2 (hs : 0 < s)
  simp only [sub_zero, smul_eq_mul, Real.norm_eq_abs, abs_of_pos hs] at h1 h2
  rw [abs_le] at h1 h2
  have e1 : ε ≤ a / 2 := min_le_left _ _
  have e2 : ε ≤ κ * a / 4 := min_le_right _ _
  have k1 : κ * (s * a - ε * s) ≤ κ * (f s - f 0) := mul_le_mul_of_nonneg_left (by linarith) hκ.le
  have k2 : ε * s ≤ κ * a / 4 * s := mul_le_mul_of_nonneg_right e2 hs.le
  have k3 : κ * (ε * s) ≤ κ * (a / 2 * s) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right e1 hs.le) hκ.le
  constructor
  · nlinarith
  · nlinarith

/-- Along a ray with common slope `a < 0`: eventually `f(s) < f(0)` and
`h(s) ≤ (1 − δ)f(s) + δf(0)`, for any `δ ∈ (0, 1)`. -/
theorem stage_local_neg {f h : ℝ → ℝ} {a δ : ℝ} (hf : HasDerivAt f a 0) (hh : HasDerivAt h a 0)
    (h0 : f 0 = h 0) (ha : a < 0) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), f s < f 0 ∧ h s ≤ (1 - δ) * f s + δ * f 0 := by
  set ε := -(δ * a) / 2 with hε
  have hεpos : 0 < ε := by rw [hε]; nlinarith
  have hf' := (hf.isLittleO.bound hεpos)
  have hh' := (hh.isLittleO.bound hεpos)
  filter_upwards [nhdsWithin_le_nhds hf', nhdsWithin_le_nhds hh', self_mem_nhdsWithin]
    with s h1 h2 (hs : 0 < s)
  simp only [sub_zero, smul_eq_mul, Real.norm_eq_abs, abs_of_pos hs] at h1 h2
  rw [abs_le] at h1 h2
  constructor
  · nlinarith
  · nlinarith [mul_pos hδ0 hs]

/-- Best-response payoffs do not depend on the player's own action. -/
theorem bestReplyValue_update (g : I → ((i : I) → A i) → ℝ) (i : I) (x : (i : I) → A i)
    (b : A i) : bestReplyValue g i (update x i b) = bestReplyValue g i x := by
  unfold bestReplyValue
  congr 1
  funext a
  rw [update_idem]

/-- The payoff along the ray `q* + s·d` has derivative `L d` at `s = 0`. -/
theorem hasDerivAt_along {φ : (Fin 2 → ℝ) → ℝ} {L : (Fin 2 → ℝ) →L[ℝ] ℝ} {q d : Fin 2 → ℝ}
    (hφ : HasFDerivAt φ L q) :
    HasDerivAt (fun s : ℝ => φ (q + s • d)) (L d) 0 := by
  have hline : HasDerivAt (fun s : ℝ => q + s • d) d 0 := by
    have hid : HasDerivAt (fun s : ℝ => s) 1 0 := hasDerivAt_id' 0
    simpa using HasDerivAt.smul_const hid d
  exact HasFDerivAt.comp_hasDerivAt (f := fun s : ℝ => q + s • d) 0 (by simpa using hφ) hline

theorem L_apply_two {L : (Fin 2 → ℝ) →L[ℝ] ℝ} (d : Fin 2 → ℝ) :
    L d = d 0 * L (Pi.single 0 1) + d 1 * L (Pi.single 1 1) := by
  have : d = d 0 • (Pi.single 0 1 : Fin 2 → ℝ) + d 1 • Pi.single 1 1 := by
    funext k; fin_cases k <;> simp
  conv_lhs => rw [this]
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

/-- The data of Propositions 12.AA.1 and 12.AA.4: a two-player game with actions in `ℝ`,
payoffs differentiable at the stage Nash equilibrium `q*` (derivatives `L₀`, `L₁`), the
first-order conditions `∂π_i/∂q_i(q*) = 0`, nonzero cross partials `∂π_i/∂q_j(q*) ≠ 0`, and the
envelope property (12.AA.6): `q_j ↦ π̂_i(q_j)` is differentiable at `q_j*` with derivative
`∂π_i/∂q_j(q*)`. -/
structure LocalGameData (g : Fin 2 → (Fin 2 → ℝ) → ℝ) (qs : Fin 2 → ℝ) where
  L0 : (Fin 2 → ℝ) →L[ℝ] ℝ
  L1 : (Fin 2 → ℝ) →L[ℝ] ℝ
  deriv0 : HasFDerivAt (g 0) L0 qs
  deriv1 : HasFDerivAt (g 1) L1 qs
  own0 : L0 (Pi.single 0 1) = 0
  own1 : L1 (Pi.single 1 1) = 0
  cross0 : L0 (Pi.single 1 1) ≠ 0
  cross1 : L1 (Pi.single 0 1) ≠ 0
  env0 : HasDerivAt (fun y => bestReplyValue g 0 (update qs 1 y)) (L0 (Pi.single 1 1)) (qs 1)
  env1 : HasDerivAt (fun y => bestReplyValue g 1 (update qs 0 y)) (L1 (Pi.single 0 1)) (qs 0)

/-- Slopes along the ray `d = (σ∂π₂/∂q₁, σ∂π₁/∂q₂)`: player `i`'s payoff and best-response
payoff both have slope `σ(∂π_i/∂q_j)²`. -/
theorem localGame_slopes {g : Fin 2 → (Fin 2 → ℝ) → ℝ} {qs : Fin 2 → ℝ}
    (D : LocalGameData g qs) (σ : ℝ) :
    HasDerivAt (fun s : ℝ => g 0 (qs + s • ![σ * D.L1 (Pi.single 0 1), σ * D.L0 (Pi.single 1 1)]))
      (σ * D.L0 (Pi.single 1 1) ^ 2) 0 ∧
    HasDerivAt (fun s : ℝ => bestReplyValue g 0
      (qs + s • ![σ * D.L1 (Pi.single 0 1), σ * D.L0 (Pi.single 1 1)]))
      (σ * D.L0 (Pi.single 1 1) ^ 2) 0 ∧
    HasDerivAt (fun s : ℝ => g 1 (qs + s • ![σ * D.L1 (Pi.single 0 1), σ * D.L0 (Pi.single 1 1)]))
      (σ * D.L1 (Pi.single 0 1) ^ 2) 0 ∧
    HasDerivAt (fun s : ℝ => bestReplyValue g 1
      (qs + s • ![σ * D.L1 (Pi.single 0 1), σ * D.L0 (Pi.single 1 1)]))
      (σ * D.L1 (Pi.single 0 1) ^ 2) 0 := by
  set d : Fin 2 → ℝ := ![σ * D.L1 (Pi.single 0 1), σ * D.L0 (Pi.single 1 1)] with hd
  have hd0 : d 0 = σ * D.L1 (Pi.single 0 1) := rfl
  have hd1 : d 1 = σ * D.L0 (Pi.single 1 1) := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := hasDerivAt_along (d := d) D.deriv0
    rw [L_apply_two, D.own0, hd1] at h
    convert h using 1; ring
  · have hfun : (fun s : ℝ => bestReplyValue g 0 (qs + s • d)) =
        fun s => bestReplyValue g 0 (update qs 1 (qs 1 + s * d 1)) := by
      funext s
      rw [← bestReplyValue_update g 0 (qs + s • d) (qs 0)]
      congr 1
      funext k; fin_cases k <;> simp [update]
    rw [hfun]
    have hid : HasDerivAt (fun s : ℝ => s) 1 0 := hasDerivAt_id' 0
    have hin : HasDerivAt (fun s : ℝ => qs 1 + s * d 1) (d 1) 0 := by
      simpa using HasDerivAt.mul_const hid (d 1)
    have := D.env0.comp_of_eq (0 : ℝ) hin (by simp)
    exact this.congr_deriv (by rw [hd1]; ring)
  · have h := hasDerivAt_along (d := d) D.deriv1
    rw [L_apply_two, D.own1, hd0] at h
    convert h using 1; ring
  · have hfun : (fun s : ℝ => bestReplyValue g 1 (qs + s • d)) =
        fun s => bestReplyValue g 1 (update qs 0 (qs 0 + s * d 0)) := by
      funext s
      rw [← bestReplyValue_update g 1 (qs + s • d) (qs 1)]
      congr 1
      funext k; fin_cases k <;> simp [update]
    rw [hfun]
    have hid : HasDerivAt (fun s : ℝ => s) 1 0 := hasDerivAt_id' 0
    have hin : HasDerivAt (fun s : ℝ => qs 0 + s * d 0) (d 0) 0 := by
      simpa using HasDerivAt.mul_const hid (d 0)
    have := D.env1.comp_of_eq (0 : ℝ) hin (by simp)
    exact this.congr_deriv (by rw [hd0]; ring)

theorem bestReplyValue_nash {I : Type*} [DecidableEq I] {A : I → Type*}
    {g : I → ((i : I) → A i) → ℝ} {M : ℝ} (hg : ∀ i x, |g i x| ≤ M) {qs : (i : I) → A i}
    (hqs : IsStageNash g qs) (i : I) : bestReplyValue g i qs = g i qs := by
  have : Nonempty (A i) := ⟨qs i⟩
  refine le_antisymm (ciSup_le fun a => hqs i a) ?_
  have := le_bestReplyValue hg i qs (qs i)
  rwa [update_eq_self] at this

/-- **Proposition 12.AA.1** (MWG, p. 419), under the envelope property (12.AA.6). In a
two-player game with actions in `ℝ`, bounded payoffs and stage Nash equilibrium `q*` satisfying
the conditions of `LocalGameData`, for every `δ ∈ (0, 1)` there is `q'` with
`π_i(q') > π_i(q*)` for both players whose infinite repetition is the outcome path of a Nash
reversion SPNE. -/
theorem proposition_12_AA_1 {g : Fin 2 → (Fin 2 → ℝ) → ℝ} {qs : Fin 2 → ℝ} {δ M : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hg : ∀ i x, |g i x| ≤ M) (hqs : IsStageNash g qs)
    (D : LocalGameData g qs) :
    ∃ q', (∀ i, g i qs < g i q') ∧ IsRepeatedSPNE g δ (nashReversion (fun _ => q') qs) := by
  obtain ⟨h0, h0', h1, h1'⟩ := localGame_slopes D 1
  have hbr := bestReplyValue_nash hg hqs
  have hκ : 0 < δ / (1 - δ) := div_pos hδ0 (by linarith)
  have e0 := stage_local_pos h0 h0' (by simp [hbr 0]) (by
    have := D.cross0; positivity) hκ
  have e1 := stage_local_pos h1 h1' (by simp [hbr 1]) (by
    have := D.cross1; positivity) hκ
  obtain ⟨s, ⟨a0, b0⟩, ⟨a1, b1⟩⟩ := (e0.and e1).exists
  simp only [zero_smul, add_zero] at a0 b0 a1 b1
  set q' := qs + s • ![1 * D.L1 (Pi.single 0 1), 1 * D.L0 (Pi.single 1 1)]
  refine ⟨q', by rw [Fin.forall_fin_two]; exact ⟨a0, a1⟩, ?_⟩
  refine lemma_12_AA_1_if hδ0.le hδ1 hg _ hqs fun t i => ?_
  rw [eq_12_AA_3 g hδ0.le hδ1 q' qs t i]
  fin_cases i
  · exact b0
  · exact b1

/-- **Proposition 12.AA.4 and Exercise 12.AA.2** (MWG, pp. 421 and 435), under the envelope
property (12.AA.6). Under the conditions of Proposition 12.AA.1, for every `δ ∈ (0, 1)` some
stick-and-carrot SPNE (play `q'` once, then `q*` forever, restarting after any deviation) gives
both players average payoffs `(1 − δ)v_i' < π_i(q*)`. -/
theorem proposition_12_AA_4 {g : Fin 2 → (Fin 2 → ℝ) → ℝ} {qs : Fin 2 → ℝ} {δ M : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hg : ∀ i x, |g i x| ≤ M) (hqs : IsStageNash g qs)
    (D : LocalGameData g qs) :
    ∃ q', (∀ i, g i q' < g i qs) ∧ IsRepeatedSPNE g δ (scProfile q' qs qs 0) ∧
      ∀ i, (1 - δ) * osValue (stageU g) δ (scProfile q' qs qs 0) [] i < g i qs := by
  obtain ⟨h0, h0', h1, h1'⟩ := localGame_slopes D (-1)
  have hbr := bestReplyValue_nash hg hqs
  have e0 := stage_local_neg h0 h0' (by simp [hbr 0]) (by
    have : 0 < D.L0 (Pi.single 1 1) ^ 2 := by have := D.cross0; positivity
    linarith) hδ0 hδ1
  have e1 := stage_local_neg h1 h1' (by simp [hbr 1]) (by
    have : 0 < D.L1 (Pi.single 0 1) ^ 2 := by have := D.cross1; positivity
    linarith) hδ0 hδ1
  obtain ⟨s, ⟨a0, b0⟩, ⟨a1, b1⟩⟩ := (e0.and e1).exists
  simp only [zero_smul, add_zero] at a0 b0 a1 b1
  set q' := qs + s • ![-1 * D.L1 (Pi.single 0 1), -1 * D.L0 (Pi.single 1 1)]
  have hlt : ∀ i, g i q' < g i qs := by rw [Fin.forall_fin_two]; exact ⟨a0, a1⟩
  have hb : ∀ i, bestReplyValue g i q' ≤ (1 - δ) * g i q' + δ * g i qs := by
    rw [Fin.forall_fin_two]; exact ⟨b0, b1⟩
  have h1δ : (1 - δ) ≠ 0 := by linarith
  obtain ⟨hspne, hval⟩ := scProfile_spne hδ0.le hδ1 hg q' qs qs 0 hqs
    (fun i a => (le_bestReplyValue hg i q' a).trans (hb i))
    (fun i a _ => by
      simp only [scVal]
      have := hqs i a
      have := hlt i
      have e : g i qs / (1 - δ) = g i qs + δ * (g i qs / (1 - δ)) := by field_simp; ring
      nlinarith)
  refine ⟨q', hlt, hspne, fun i => ?_⟩
  rw [hval]
  have := hlt i
  have e : (1 - δ) * (g i q' + δ * (g i qs / (1 - δ))) = (1 - δ) * g i q' + δ * g i qs := by
    field_simp
  rw [e]
  nlinarith

end MWG.MarketPower
