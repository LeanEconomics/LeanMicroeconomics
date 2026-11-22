/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPositiveEquilibriumTheory.SMDDebreu

/-!
# Proposition 17.E.3 (Sonnenschein-Mantel-Debreu) and footnote 30 (MWG pp. 602-606)

`proposition_17_E_3`: every `z` continuous on `P_ε`, homogeneous of degree zero and satisfying
Walras' law coincides on `P_ε` with the aggregate excess demand of an exchange economy with `L`
consumers, each with consumption set `ℝ^L_+`, an endowment `ωᵢ ≫ 0`, and continuous, convex,
strongly monotone preferences whose demand at every `p ∈ P_ε` is a single bundle. (The book's
"strictly convex" is not obtained; see `docs/corrections.md`.)

The degenerate cases are treated directly: `L = 0`; `ε > 1` (then `P_ε = ∅`); `L = 1` (then
`z = 0` on `P_ε` and one consumer who keeps his endowment suffices). For `L ≥ 2` and `ε ≤ 1` the
proof is Debreu's: the decomposition `z(p) = ∑ᵢ αᵢ(p)(eⁱ - pᵢ p)` on normalized prices with
`αᵢ = zᵢ + r pᵢ ≥ 1`, each `αᵢ` extended by Tietze, and `debreu_consumer` for the preferences.

`footnote_17_30`: adding `k` consumers with no endowment (their only affordable bundle at
`p ≫ 0` is `0`) gives an economy with `L + k` consumers and the same aggregate excess demand.
-/

namespace MWG.PositiveEquilibriumTheory

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.GeneralEquilibriumExamples Filter Topology

variable {L : ℕ}

/-- **Proposition 17.E.3** (MWG, p. 602), the Sonnenschein-Mantel-Debreu theorem. Suppose that
`z` is continuous on `P_ε = {p ∈ ℝ^L_+ : pₗ/pₗ' ≥ ε}` (`ε > 0`), homogeneous of degree zero
and satisfies Walras' law there. Then there is an exchange economy with `L` consumers
(consumption sets `ℝ^L_+`, endowments `≫ 0`, continuous, convex and strongly monotone
preferences) whose demand at each `p ∈ P_ε` is single-valued and whose aggregate excess demand
function coincides with `z` on `P_ε`. -/
theorem proposition_17_E_3 {ε : ℝ} (hε : 0 < ε) {z : (Fin L → ℝ) → Fin L → ℝ}
    (hc : ContinuousOn z (pEps L ε)) (hH : ∀ p ∈ pEps L ε, ∀ α : ℝ, 0 < α → z (α • p) = z p)
    (hW : ∀ p ∈ pEps L ε, p ⬝ᵥ z p = 0) :
    ∃ E : ExchangeEconomy (Fin L) L, (∀ i, E.X i = nonnegOrthant L) ∧
      (∀ i, StrictlyPositive (E.ω i)) ∧
      (∀ i, Continuous (E.u i) ∧ UtilityStronglyMonotone (E.u i) ∧
        PrefConvex (nonnegOrthant L) (utilityPref (E.u i))) ∧
      ∀ p ∈ pEps L ε, (∀ i, ∃ x, E.demand i p = {x}) ∧ excessDemand E p = z p := by
  obtain ⟨hs1, hs2, hs3⟩ := smd_sum_props (L := L)
  have hP0 := smd_consumer_props (0 : Fin L → ℝ) hs1 hs2 hs3
  -- `L = 0`
  rcases Nat.eq_zero_or_pos L with hL0 | hL0
  · subst hL0
    refine ⟨ExchangeEconomy.ofOrthant (fun _ x => ∑ l, (x - 0) l) (fun _ _ => 1),
      fun _ => rfl, fun _ _ => one_pos, fun _ => hP0, fun p _ => ⟨fun i => i.elim0, ?_⟩⟩
    funext l; exact l.elim0
  -- `ε > 1`: `P_ε` is empty
  rcases lt_or_ge 1 ε with hε1 | hε1
  · have hempty : ∀ p ∈ pEps L ε, False := fun p hp => by
      have := hp.2 ⟨0, hL0⟩ ⟨0, hL0⟩
      rw [div_self (pEps_pos hε hp ⟨0, hL0⟩).ne'] at this
      linarith
    exact ⟨ExchangeEconomy.ofOrthant (fun _ x => ∑ l, (x - 0) l) (fun _ _ => 1),
      fun _ => rfl, fun _ _ => one_pos, fun _ => hP0, fun p hp => (hempty p hp).elim⟩
  -- `L = 1`: `z = 0` on `P_ε`
  rcases Nat.lt_or_ge L 2 with hL1 | hL2
  · have hL : L = 1 := by omega
    subst hL
    let E : ExchangeEconomy (Fin 1) 1 :=
      ExchangeEconomy.ofOrthant (fun _ (x : Fin 1 → ℝ) => ∑ l, (x - (fun _ : Fin 1 => (1 : ℝ))) l)
        (fun _ _ => 1)
    have hP1 := smd_consumer_props (fun _ => (1 : ℝ)) hs1 hs2 hs3
    have hdem : ∀ p ∈ pEps 1 ε, ∀ i, E.demand i p = {(fun _ => (1 : ℝ)) + 0} := by
      intro p hp i
      have hp0 := pEps_pos hε hp 0
      have h := smd_demand_eq (u := fun z : Fin 1 → ℝ => ∑ l, z l) (ω := fun _ => 1) (p := p)
        (ζp := 0) one_pos (fun y hy => by
          simp only [dotProduct, Fin.sum_univ_one] at hy ⊢
          have hy0 : y 0 ≤ 0 := by nlinarith
          refine ⟨by simpa using hy0, fun h0 => ?_⟩
          funext l; fin_cases l; simp at h0 ⊢; linarith)
        (by simp) (fun l => by simp)
      rw [one_smul] at h
      exact h
    refine ⟨E, fun _ => rfl, fun _ _ => one_pos, fun _ => hP1, fun p hp =>
      ⟨fun i => ⟨_, hdem p hp i⟩, ?_⟩⟩
    have hw := hW p hp
    simp only [dotProduct, Fin.sum_univ_one] at hw
    have hz0 : z p 0 = 0 := (mul_eq_zero.1 hw).resolve_left (pEps_pos hε hp 0).ne'
    rw [excessDemand, Fin.sum_univ_one, indivExcessDemand, demandFn_eq E (hdem p hp 0)]
    funext l; fin_cases l
    simp [E, ExchangeEconomy.ofOrthant, hz0]
  -- `L ≥ 2`, `ε ≤ 1`: Debreu's construction
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL0
  set K := unitPEps L ε with hK
  have hKc : IsCompact K := unitPEps_isCompact L ε
  have hKsub : K ⊆ pEps L ε := unitPEps_subset hε
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn (hc.mono hKsub)
  have hzM : ∀ p ∈ K, ∀ l, |z p l| ≤ |M| := fun p hp l =>
    ((norm_le_pi_norm (z p) l).trans (hM p hp)).trans (le_abs_self M)
  set r : ℝ := (|M| + 1) * L / ε with hr
  have hr0 : 0 ≤ r := by positivity
  -- `αᵢ(p) = zᵢ(p) + r pᵢ ≥ 1` on `K`
  have hα1 : ∀ i, ∀ p ∈ K, 1 ≤ z p i + r * p i := by
    intro i p hp
    have hb := (unitPEps_bounds hε hp i).1
    have h1 : r * (ε / L) = |M| + 1 := by rw [hr]; field_simp
    have h2 : r * (ε / L) ≤ r * p i := mul_le_mul_of_nonneg_left hb hr0
    have h3 := neg_abs_le (z p i)
    linarith [hzM p hp i]
  -- Tietze extension of `αᵢ`
  have hext : ∀ i : Fin L, ∃ α : (Fin L → ℝ) → ℝ, Continuous α ∧ (∀ p, 1 ≤ α p) ∧
      ∀ p ∈ K, α p = z p i + r * p i := by
    intro i
    have hcont : ContinuousOn (fun p => z p i + r * p i) K :=
      ((continuous_apply i).comp_continuousOn (hc.mono hKsub)).add
        (continuous_const.mul (continuous_apply i)).continuousOn
    let f : C(K, ℝ) := ⟨K.domRestrict (fun p => z p i + r * p i), hcont.domRestrict⟩
    obtain ⟨g, hg, hgf⟩ := ContinuousMap.exists_restrict_eq_forall_mem_of_closed f
      (t := Set.Ici 1) (fun x => hα1 i x.1 x.2) ⟨1, Set.mem_Ici.2 le_rfl⟩ hKc.isClosed
    refine ⟨g, g.continuous, fun p => hg p, fun p hp => ?_⟩
    have := congrArg (fun h : C(K, ℝ) => h ⟨p, hp⟩) hgf
    simpa [f] using this
  choose α hαc hαge hαeq using hext
  -- the consumers
  have hcons : ∀ i : Fin L, ∃ u : (Fin L → ℝ) → ℝ, Continuous u ∧
      (∀ c, Convex ℝ {z | c ≤ u z}) ∧ (∀ z z', z ≤ z' → z ≠ z' → u z < u z') ∧
      ∀ p ∈ unitPEps L ε, ∀ z, p ⬝ᵥ z ≤ 0 → u z ≤ u (α i p • debreuZ i p) ∧
        (u (α i p • debreuZ i p) ≤ u z → z = α i p • debreuZ i p) :=
    fun i => debreu_consumer (by omega) hε hε1 i (hαc i) (hαge i)
  choose u hu1 hu2 hu3 hu4 using hcons
  set R : ℝ := |M| + r + 1 with hR
  set ω : Fin L → ℝ := fun _ => R with hω
  have hR0 : 0 < R := by positivity
  have hX : ∀ i, ∀ p ∈ K, ω + α i p • debreuZ i p ∈ nonnegOrthant L := by
    intro i p hp l
    have hb := unitPEps_bounds hε hp
    have hαle : α i p ≤ |M| + r := by
      rw [hαeq i p hp]
      have := le_abs_self (z p i)
      have h2 : r * p i ≤ r * 1 := mul_le_mul_of_nonneg_left (hb i).2 hr0
      linarith [hzM p hp i]
    have hpp : p i * p l ≤ 1 := by
      have := mul_le_mul (hb i).2 (hb l).2 (hp.1 l) zero_le_one
      linarith
    have hpp0 : 0 ≤ p i * p l := mul_nonneg (hp.1 i) (hp.1 l)
    have hαpos : 0 ≤ α i p := zero_le_one.trans (hαge i p)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, debreuZ, Pi.sub_apply, hω]
    have hsingle : 0 ≤ (Pi.single i (1 : ℝ) : Fin L → ℝ) l := by
      by_cases h : l = i
      · subst h; simp
      · simp [h]
    have : α i p * (p i * p l) ≤ |M| + r := by nlinarith
    nlinarith
  let E : ExchangeEconomy (Fin L) L :=
    ExchangeEconomy.ofOrthant (fun i x => u i (x - ω)) fun _ => ω
  refine ⟨E, fun _ => rfl, fun _ _ => hR0, fun i => smd_consumer_props ω (hu1 i) (hu2 i) (hu3 i),
    fun p hp => ?_⟩
  obtain ⟨ht, hpK, hpe⟩ := pEps_normalize hL0 hε hp
  set t := Real.sqrt (p ⬝ᵥ p)
  set q := t⁻¹ • p with hq
  have hdem : ∀ i, E.demand i p = {ω + α i q • debreuZ i q} := by
    intro i
    have h := smd_demand_eq (u := u i) (ω := ω) (p := q) ht (hu4 i q hpK)
      (by rw [dotProduct_smul, debreuZ_walras i hpK.2.1, smul_zero]) (hX i q hpK)
    rw [← hpe] at h
    exact h
  refine ⟨fun i => ⟨_, hdem i⟩, ?_⟩
  have hzq : z p = z q := by
    conv_lhs => rw [hpe]
    exact hH q (hKsub hpK) t ht
  rw [excessDemand]
  simp only [indivExcessDemand, demandFn_eq E (hdem _)]
  have hωE : ∀ i, E.ω i = ω := fun _ => rfl
  simp only [hωE, add_sub_cancel_left]
  rw [hzq]
  have := debreu_decomposition hpK.2.1 (hW q (hKsub hpK)) r
  rw [← this]
  exact Finset.sum_congr rfl fun i _ => by rw [hαeq i q hpK]

/-- **Footnote 30** (MWG, p. 602). Adding `k` consumers with no endowment (consumption sets
`ℝ^L_+`, any utility, here `x ↦ 0`) to an economy with consumption sets `ℝ^L_+` changes neither
single-valuedness of demand nor the aggregate excess demand at any `p ≫ 0`: at such prices the
only affordable bundle of a consumer without endowment is `0`. So for any `I ≥ L` there is an
economy of `I` consumers generating `z` on `P_ε`. -/
theorem footnote_17_30 (E : ExchangeEconomy (Fin L) L) (hX : ∀ i, E.X i = nonnegOrthant L)
    (k : ℕ) : ∃ E' : ExchangeEconomy (Fin (L + k)) L, (∀ i, E'.X i = nonnegOrthant L) ∧
      ∀ p, StrictlyPositive p → (∀ i, ∃ x, E.demand i p = {x}) →
        (∀ i, ∃ x, E'.demand i p = {x}) ∧ excessDemand E' p = excessDemand E p := by
  let E' : ExchangeEconomy (Fin (L + k)) L :=
    ⟨fun _ => nonnegOrthant L, Fin.addCases E.u fun _ _ => 0, Fin.addCases E.ω fun _ => 0⟩
  refine ⟨E', fun _ => rfl, fun p hp hE => ?_⟩
  have hold : ∀ j : Fin L, E'.demand (Fin.castAdd k j) p = E.demand j p := by
    intro j
    simp only [ExchangeEconomy.demand, E', Fin.addCases_left, hX j]
  have hnew : ∀ j : Fin k, E'.demand (Fin.natAdd L j) p = {0} := by
    intro j
    simp only [ExchangeEconomy.demand, E', Fin.addCases_right, dotProduct_zero]
    ext x
    simp only [Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨hx0, hxb⟩, -⟩
      funext l
      have hterm : ∀ l', 0 ≤ p l' * x l' := fun l' => mul_nonneg (hp l').le (hx0 l')
      have hsum : ∑ l', p l' * x l' = 0 :=
        le_antisymm hxb (Finset.sum_nonneg fun l' _ => hterm l')
      have := (Finset.sum_eq_zero_iff_of_nonneg fun l' _ => hterm l').1 hsum l
        (Finset.mem_univ l)
      exact (mul_eq_zero.1 this).resolve_left (hp l).ne'
    · rintro rfl
      exact ⟨⟨fun _ => le_rfl, by simp⟩, fun _ _ => le_rfl⟩
  refine ⟨fun i => ?_, ?_⟩
  · refine Fin.addCases (fun j => ?_) (fun j => ⟨0, hnew j⟩) i
    rw [hold j]; exact hE j
  · rw [excessDemand, excessDemand, Fin.sum_univ_add]
    have h1 : ∀ j : Fin L, indivExcessDemand E' (Fin.castAdd k j) p =
        indivExcessDemand E j p := by
      intro j
      obtain ⟨x, hx⟩ := hE j
      have hx' : E'.demand (Fin.castAdd k j) p = {x} := by rw [hold j, hx]
      simp only [indivExcessDemand, demandFn_eq E' hx', demandFn_eq E hx]
      simp [E']
    have h2 : ∀ j : Fin k, indivExcessDemand E' (Fin.natAdd L j) p = 0 := by
      intro j
      simp only [indivExcessDemand, demandFn_eq E' (hnew j)]
      simp [E']
    simp only [h1, h2, Finset.sum_const_zero, add_zero]

end MWG.PositiveEquilibriumTheory
