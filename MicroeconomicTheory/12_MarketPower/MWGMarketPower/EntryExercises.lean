/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGMarketPower.OneStageEntry
import MWGMarketPower.CompetitiveLimitExercises
import MWGMarketPower.CircularCity

/-!
# Entry exercises

MWG, Exercises 12.E.1 and 12.E.3-12.E.7, pp. 434-435.

* `exercise_12_E_1`: two-stage entry with price competition and firms of different efficiency
  (costs `1 < 2`, demand `max{0, 10 − p}`, entry cost `10`; in the duopoly subgame ties go to the
  low-cost firm, Exercise 12.C.4). For every selection of stage-2 equilibria, "only the
  inefficient firm enters" is an equilibrium of the entry stage: the most efficient firm need not
  be active.
* `exercise_12_E_3_cournot`, `exercise_12_E_3_bertrand`: the welfare loss of free entry relative
  to the optimal number of firms. In Example 12.E.1 it is
  `((a − c)²/2b)(1/(J* + 1)² − 1/(J° + 1)²) − (J° − J*)K` (`26K/25` when `J° = 2`) and tends to
  `0` as `K → 0`; in Example 12.E.2 it is `max{0, (a − c)²/8b − K}`, which tends to the monopoly
  deadweight loss `(a − c)²/8b > 0`.
* `exercise_12_E_4`: a perfect cartel after entry: welfare `S − JK` is maximized by one firm; free
  entry gives `J* = ⌊πᵐ/K⌋` firms, which dissipate the monopoly profit (`πᵐ − K < J*K ≤ πᵐ`), so
  welfare falls by `(J* − 1)K` to within `K` of the monopoly consumer surplus.
* `exercise_12_E_5`: the circular city with quadratic travel cost (Exercise 12.C.16): the
  welfare-maximizing number of firms, the same whether the planner controls entry and pricing or
  only entry, is at most the free-entry number; `exercise_12_E_5_instance`: `J° = 3 < 6 = J*`.
* `exercise_12_E_6_two_to_one`, `exercise_12_E_6_fewer`, `exercise_12_E_6_converse_fails`:
  Cournot entry with cost `cq`: every two-stage equilibrium number of firms is a one-stage one;
  not conversely; one-stage equilibria never have more firms.
* `exercise_12_E_7`: one-stage entry with announced prices and U-shaped average cost: if
  `x(c̄) = J*q̄` with `J* ≥ 2`, every equilibrium is perfectly competitive and efficient
  (`exercise_12_E_7_efficient`); `exercise_12_E_7_counterexample` (correction): with `J* = 1`
  the claim fails.

Departures are listed in the theorem docstrings and in `docs/corrections.md`.
-/

namespace MWG.MarketPower

open Set Function Filter Topology MWG.NoncooperativeGames MWG.SimultaneousMoveGames

/-! ### Exercise 12.E.1 -/

/-- Gross stage-2 profits in the entry game of `exercise_12_E_1` (demand `max{0, 10 − p}`, firm
`0` with cost `1`, firm `1` with cost `2`): a lone entrant earns its monopoly profit (`81/4`,
`16`); if both enter they play the duopoly equilibrium `p₁ = p₂ = pd` (ties to firm `0`), where
firm `0` earns `(pd − 1)x(pd)` and firm `1` nothing. -/
noncomputable def e1Profit (pd : ℝ) (j : Fin 2) (e : Fin 2 → Bool) : ℝ :=
  if e 0 = true ∧ e 1 = true then (if j = 0 then (pd - 1) * bcLinDemand 10 pd else 0)
  else if e j = true then (if j = 0 then 81 / 4 else 16) else 0

/-- Equilibrium of the entry stage given stage-2 profits `Pr` and entry cost `K`: entrants earn
at least `K`, and no outsider would earn more than `K` by entering. -/
def IsEntryStageEq (Pr : Fin 2 → (Fin 2 → Bool) → ℝ) (K : ℝ) (e : Fin 2 → Bool) : Prop :=
  ∀ j, (e j = true → K ≤ Pr j e) ∧ (e j = false → Pr j (update e j true) ≤ K)

/-- **Exercise 12.E.1** (MWG, p. 434). Two-stage entry with price competition; potential firm `0`
has unit cost `1`, firm `1` unit cost `2`; demand `max{0, 10 − p}`; entry cost `K = 10`; in the
duopoly ties go to the low-cost firm. Then: the duopoly subgame's equilibria are `p₀ = p₁ = pd`
with `pd ∈ [1, 2]` (Exercise 12.C.4); the monopoly profits are `81/4` (firm 0, at `11/2`) and
`16` (firm 1, at `6`); and for every such `pd`, "firm 1 enters, firm 0 stays out" is an
equilibrium of the entry stage. So the most efficient firm need not be active. -/
theorem exercise_12_E_1 :
    (∀ p₀ p₁, IsNashEquilibrium (bcGame ℝ (bcTieProfit₁ (bcLinDemand 10) 1)
      (bcTieProfit₂ (bcLinDemand 10) 2)) ![p₀, p₁] ↔ p₀ = p₁ ∧ 1 ≤ p₀ ∧ p₀ ≤ 2) ∧
    (∀ p, (p - 1) * bcLinDemand 10 p ≤ 81 / 4) ∧ (11 / 2 - 1) * bcLinDemand 10 (11 / 2) = 81 / 4 ∧
    (∀ p, (p - 2) * bcLinDemand 10 p ≤ 16) ∧ (6 - 2) * bcLinDemand 10 6 = 16 ∧
    ∀ pd : ℝ, 1 ≤ pd → pd ≤ 2 → IsEntryStageEq (e1Profit pd) 10 ![false, true] := by
  obtain ⟨m1, s1, _⟩ := rbx_lin_facts (c := 1) (by norm_num)
  obtain ⟨m2, -, _⟩ := rbx_lin_facts (c := 2) (by norm_num)
  norm_num at m1 s1 m2
  have hv1 : (11 / 2 - 1) * bcLinDemand 10 (11 / 2) = 81 / 4 := by norm_num [bcLinDemand]
  have hv2 : (6 - 2) * bcLinDemand 10 6 = 16 := by norm_num [bcLinDemand]
  refine ⟨(exercise_12_C_4a_tieRule (bcLinDemand_isBertrand 10) (by norm_num) (by norm_num)
    (by norm_num [bcLinDemand]) (show (2 : ℝ) < 11 / 2 by norm_num) s1).1,
    fun p => by have := m1 p; norm_num [bcLinDemand] at this ⊢; linarith, hv1,
    fun p => by have := m2 p; norm_num [bcLinDemand] at this ⊢; linarith, hv2,
    fun pd h1 h2 => ?_⟩
  intro j
  fin_cases j
  · refine ⟨fun h => by simp at h, fun _ => ?_⟩
    have hupd : update ![false, true] (0 : Fin 2) true = ![true, true] := by
      funext k; fin_cases k <;> simp
    change e1Profit pd 0 (update ![false, true] (0 : Fin 2) true) ≤ 10
    rw [hupd]
    have h0 : e1Profit pd 0 ![true, true] = (pd - 1) * bcLinDemand 10 pd := by
      simp [e1Profit]
    rw [h0]
    simp only [bcLinDemand]
    rw [max_eq_right (by linarith)]
    nlinarith
  · refine ⟨fun _ => ?_, fun h => by simp at h⟩
    norm_num [e1Profit]

/-! ### Exercise 12.E.3 -/

/-- **Exercise 12.E.3, the Cournot model of Example 12.E.1** (MWG, p. 434). With
`W(J) = ((a − c)²/b)(J² + 2J)/(2(J + 1)²) − JK`, the welfare loss of `J*` firms relative to `J°`
firms is `((a − c)²/2b)(1/(J* + 1)² − 1/(J° + 1)²) − (J° − J*)K`; it is nonnegative when `J°`
maximizes welfare; when `J° = 2` (i.e. `(a − c)²/b = 27K`, so `J* = 4`) it equals `26K/25`; and
it tends to `0` as `K → 0`. -/
theorem exercise_12_E_3_cournot {a b c : ℝ} (hac : c < a) (hb : 0 < b) :
    (∀ K (J Jo : ℕ), entryWelfare (fun s => a - b * s) (fun q => c * q)
        (fun J => (a - c) / (b * (J + 1))) K Jo -
      entryWelfare (fun s => a - b * s) (fun q => c * q) (fun J => (a - c) / (b * (J + 1))) K J =
      (a - c) ^ 2 / (2 * b) * (1 / ((J : ℝ) + 1) ^ 2 - 1 / ((Jo : ℝ) + 1) ^ 2) -
        ((Jo : ℝ) - J) * K) ∧
    (∀ K, 0 < K → (a - c) ^ 2 / b = 27 * K →
      IsEntryEquilibrium (cournotEntryProfit a b c) K 4 ∧
      (∀ J : ℕ, entryWelfare (fun s => a - b * s) (fun q => c * q)
        (fun J => (a - c) / (b * (J + 1))) K J ≤ entryWelfare (fun s => a - b * s)
        (fun q => c * q) (fun J => (a - c) / (b * (J + 1))) K 2) ∧
      entryWelfare (fun s => a - b * s) (fun q => c * q) (fun J => (a - c) / (b * (J + 1))) K 2 -
        entryWelfare (fun s => a - b * s) (fun q => c * q)
          (fun J => (a - c) / (b * (J + 1))) K 4 = 26 * K / 25) ∧
    ∀ ε, 0 < ε → ∃ δ, 0 < δ ∧ ∀ K, 0 < K → K < δ → ∀ J,
      IsEntryEquilibrium (cournotEntryProfit a b c) K J → ∀ Jo : ℕ, 1 ≤ Jo →
        entryWelfare (fun s => a - b * s) (fun q => c * q)
            (fun J => (a - c) / (b * (J + 1))) K Jo -
          entryWelfare (fun s => a - b * s) (fun q => c * q)
            (fun J => (a - c) / (b * (J + 1))) K J < ε := by
  refine ⟨fun K J Jo => ?_, fun K hK hA => ?_, fun ε hε => ?_⟩
  · rw [entryWelfare_linear hb, entryWelfare_linear hb]
    field_simp
    ring
  · have h27 : (a - c) ^ 2 / b = ((2 : ℕ) + 1 : ℝ) ^ 3 * K := by rw [hA]; norm_num
    have h3 := example_12_E_3 hb hK 2 (by norm_num) h27
    refine ⟨h3.2.1 rfl, h3.1, ?_⟩
    rw [entryWelfare_linear hb, entryWelfare_linear hb, hA]
    norm_num
    ring
  · obtain ⟨δ, hδ, h⟩ := (exercise_12_F_3 hac hb).2.2 ε hε
    exact ⟨δ, hδ, fun K hK hKδ J hJ Jo hJo => (h K hK hKδ J hJ).2 Jo _ hJo⟩

/-- Output per firm with Bertrand competition after entry (Example 12.E.2): the monopoly output
`(a − c)/2b` with one firm, and an equal share of the competitive output `(a − c)/b` with
`J ≥ 2` firms. -/
noncomputable def bertrandEntryOutput (a b c : ℝ) (J : ℕ) : ℝ :=
  if J = 1 then (a - c) / (2 * b) else (a - c) / (b * J)

/-- **Exercise 12.E.3, the Bertrand model of Example 12.E.2** (MWG, p. 434). With linear demand
and Bertrand competition after entry, `W(1) = 3(a − c)²/8b − K` and `W(J) = (a − c)²/2b − JK`
for `J ≥ 2`. If `K ≤ πᵐ = (a − c)²/4b` the free-entry number is `J* = 1`; when also
`K ≤ (a − c)²/8b`, `J° = 2` is welfare-optimal and the loss is `(a − c)²/8b − K`, which tends to
the monopoly deadweight loss `(a − c)²/8b > 0` as `K → 0`: unlike Example 12.E.1, the loss does
not vanish. -/
theorem exercise_12_E_3_bertrand {a b c : ℝ} (hac : c < a) (hb : 0 < b) :
    (∀ K, entryWelfare (fun s => a - b * s) (fun q => c * q) (bertrandEntryOutput a b c) K 1 =
      3 * (a - c) ^ 2 / (8 * b) - K) ∧
    (∀ K (J : ℕ), 2 ≤ J →
      entryWelfare (fun s => a - b * s) (fun q => c * q) (bertrandEntryOutput a b c) K J =
        (a - c) ^ 2 / (2 * b) - J * K) ∧
    (∀ K, 0 < K → K ≤ (a - c) ^ 2 / (8 * b) →
      (∀ J : ℕ, 1 ≤ J →
        entryWelfare (fun s => a - b * s) (fun q => c * q) (bertrandEntryOutput a b c) K J ≤
        entryWelfare (fun s => a - b * s) (fun q => c * q) (bertrandEntryOutput a b c) K 2) ∧
      entryWelfare (fun s => a - b * s) (fun q => c * q) (bertrandEntryOutput a b c) K 2 -
        entryWelfare (fun s => a - b * s) (fun q => c * q) (bertrandEntryOutput a b c) K 1 =
        (a - c) ^ 2 / (8 * b) - K) ∧
    Tendsto (fun K => (a - c) ^ 2 / (8 * b) - K) (𝓝[>] 0) (𝓝 ((a - c) ^ 2 / (8 * b))) ∧
    0 < (a - c) ^ 2 / (8 * b) := by
  have hW1 : ∀ K, entryWelfare (fun s => a - b * s) (fun q => c * q)
      (bertrandEntryOutput a b c) K 1 = 3 * (a - c) ^ 2 / (8 * b) - K := by
    intro K
    rw [entryWelfare_linear_general]
    simp only [bertrandEntryOutput, ite_true, Nat.cast_one]
    field_simp
    ring
  have hWJ : ∀ K (J : ℕ), 2 ≤ J →
      entryWelfare (fun s => a - b * s) (fun q => c * q) (bertrandEntryOutput a b c) K J =
        (a - c) ^ 2 / (2 * b) - J * K := by
    intro K J hJ
    rw [entryWelfare_linear_general]
    have hJ1 : J ≠ 1 := by omega
    have hJ0 : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
    simp only [bertrandEntryOutput, hJ1, ite_false]
    field_simp
    ring
  have hpos : 0 < (a - c) ^ 2 / (8 * b) := by have := sub_pos.2 hac; positivity
  refine ⟨hW1, hWJ, fun K hK hKle => ⟨fun J hJ => ?_, ?_⟩, ?_, hpos⟩
  · rw [hWJ K 2 le_rfl]
    rcases eq_or_lt_of_le hJ with h | h
    · subst h; rw [hW1]
      have : (a - c) ^ 2 / (2 * b) = 3 * (a - c) ^ 2 / (8 * b) + (a - c) ^ 2 / (8 * b) := by
        field_simp; ring
      push_cast; linarith
    · rw [hWJ K J h]
      have : (2 : ℝ) ≤ J := by exact_mod_cast h
      push_cast; nlinarith
  · rw [hWJ K 2 le_rfl, hW1]
    push_cast
    field_simp
    ring
  · have := (tendsto_const_nhds (x := (a - c) ^ 2 / (8 * b))).sub
      (tendsto_id.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0))
    simpa using this

/-! ### Exercise 12.E.4 -/

/-- **Exercise 12.E.4** (MWG, p. 434). After entry the `J` firms (unit cost `c`) form a perfect
cartel, so the market outcome is the monopoly one whatever `J`: total surplus is `S − JK`, where
`S` is the monopoly consumer surplus plus the monopoly profit `πᵐ`, and each firm earns `πᵐ/J`.
* A planner who controls entry but not the cartel chooses `J° = 1`, the unique maximizer.
* With free entry (and `K ≤ πᵐ`), `J*` is an equilibrium number iff `J* = ⌊πᵐ/K⌋`.
* Entry costs then dissipate the monopoly profit, `πᵐ − K < J*K ≤ πᵐ`, so welfare falls by
  `(J* − 1)K` relative to `J° = 1`, to within `K` of the monopoly consumer surplus `S − πᵐ`. -/
theorem exercise_12_E_4 {S πm K : ℝ} (hK : 0 < K) (hπ : K ≤ πm) :
    (∀ J : ℕ, 1 ≤ J → S - J * K ≤ S - 1 * K ∧ (S - J * K = S - 1 * K → J = 1)) ∧
    (∀ J : ℕ, IsEntryEquilibrium (fun J : ℕ => πm / J) K J ↔ J = ⌊πm / K⌋₊) ∧
    (πm - K < ⌊πm / K⌋₊ * K ∧ (⌊πm / K⌋₊ : ℝ) * K ≤ πm) ∧
    (S - 1 * K) - (S - ⌊πm / K⌋₊ * K) = (⌊πm / K⌋₊ - 1) * K ∧
    S - πm ≤ S - ⌊πm / K⌋₊ * K ∧ S - ⌊πm / K⌋₊ * K < S - πm + K := by
  have hr : 0 ≤ πm / K := div_nonneg (by linarith) hK.le
  have hfl := Nat.floor_le hr
  have hfl2 := Nat.lt_floor_add_one (πm / K)
  have h1 : (⌊πm / K⌋₊ : ℝ) * K ≤ πm := by rwa [le_div_iff₀ hK] at hfl
  have h2 : πm < (⌊πm / K⌋₊ + 1) * K := by rwa [div_lt_iff₀ hK] at hfl2
  refine ⟨fun J hJ => ?_, fun J => ?_, ⟨by linarith, h1⟩, by ring, by linarith, by linarith⟩
  · have : (1 : ℝ) ≤ J := by exact_mod_cast hJ
    refine ⟨by nlinarith, fun h => ?_⟩
    have : (J : ℝ) = 1 := by
      have := mul_right_cancel₀ hK.ne' (show (J : ℝ) * K = 1 * K by linarith)
      exact this
    exact_mod_cast this
  · unfold IsEntryEquilibrium
    dsimp only
    rw [eq_comm, Nat.floor_eq_iff hr]
    constructor
    · rintro ⟨hJ, h1', h2'⟩
      have hJ' : (0 : ℝ) < J := by exact_mod_cast hJ
      push_cast at h2'
      rw [le_div_iff₀ hJ'] at h1'
      rw [div_lt_iff₀ (by positivity)] at h2'
      exact ⟨by rw [le_div_iff₀ hK]; linarith, by rw [div_lt_iff₀ hK]; linarith⟩
    · rintro ⟨h1', h2'⟩
      have hJ : 1 ≤ J := by
        by_contra h0; push Not at h0
        have : J = 0 := by omega
        rw [this] at h2'
        have : 1 ≤ πm / K := by rw [le_div_iff₀ hK]; linarith
        push_cast at h2'; linarith
      have hJ' : (0 : ℝ) < J := by exact_mod_cast hJ
      rw [le_div_iff₀ hK] at h1'
      rw [div_lt_iff₀ hK] at h2'
      refine ⟨hJ, by rw [le_div_iff₀ hJ']; linarith, ?_⟩
      push_cast
      rw [div_lt_iff₀ (by positivity)]; linarith

/-! ### Exercise 12.E.5 -/

/-- Total travel cost in the circular city (circumference `1`, `M` consumers, quadratic travel
cost `td²`) when `J` equally spaced firms each serve the consumers nearest to them: each of the
`2J` half-arcs of length `1/(2J)` contributes `M∫₀^{1/(2J)} tx² dx`. -/
noncomputable def circTravelCost (t M : ℝ) (J : ℕ) : ℝ :=
  2 * J * M * ∫ x in (0 : ℝ)..1 / (2 * J), t * x ^ 2

theorem circTravelCost_eq {t M : ℝ} {J : ℕ} (hJ : 1 ≤ J) :
    circTravelCost t M J = t * M / (12 * (J : ℝ) ^ 2) := by
  have hJ' : (0 : ℝ) < J := by exact_mod_cast hJ
  unfold circTravelCost
  rw [intervalIntegral.integral_const_mul, integral_pow]
  norm_num
  field_simp
  ring

/-- Aggregate surplus in the circular city with `J` firms, valuation `v`, unit cost `c` and entry
cost `K`, when every consumer buys from the nearest firm: `M(v − c) − JK − tM/(12J²)` (prices are
transfers). -/
noncomputable def circWelfare (v c t M K : ℝ) (J : ℕ) : ℝ :=
  M * (v - c) - J * K - circTravelCost t M J

/-- **Exercise 12.E.5** (MWG, p. 434). Two-stage entry into the circular city of Exercise 12.C.16
(quadratic travel cost, `v` large): with `J` firms each earns `tM/J³` (`exercise_12_C_16`).
(a) A planner controlling entry and pricing has every consumer buy from the nearest firm and
maximizes `circWelfare`; (b) a planner controlling only entry faces the equilibrium prices
`c + t/J²`, which are equal, so consumers again buy from the nearest firm and welfare is again
`circWelfare`. Both choose `J°` maximizing `M(v − c) − JK − tM/(12J²)`. Every such `J°` is at most
the free-entry number `J*`: there is (weakly) excessive entry. -/
theorem exercise_12_E_5 {v c t M K : ℝ} (ht : 0 < t) (hM : 0 < M) (hK : 0 < K) {Js Jo : ℕ}
    (hJs : IsEntryEquilibrium (fun J : ℕ => t * M / (J : ℝ) ^ 3) K Js)
    (hmax : ∀ J : ℕ, 1 ≤ J → circWelfare v c t M K J ≤ circWelfare v c t M K Jo) :
    Jo ≤ Js := by
  obtain ⟨hJs1, -, hJs2⟩ := hJs
  have htM : 0 < t * M := mul_pos ht hM
  -- welfare strictly decreases from `J*` on
  have hstep : ∀ n : ℕ, Js ≤ n →
      circWelfare v c t M K (n + 1) < circWelfare v c t M K n := by
    intro n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_trans hJs1 hn
    have hlt : t * M < K * ((n : ℝ) + 1) ^ 3 := by
      have h := hJs2
      simp only at h
      push_cast at h
      rw [div_lt_iff₀ (by positivity)] at h
      have : ((Js : ℝ) + 1) ^ 3 ≤ ((n : ℝ) + 1) ^ 3 := by
        have : (Js : ℝ) ≤ n := by exact_mod_cast hn
        gcongr
      nlinarith
    unfold circWelfare
    rw [circTravelCost_eq (by omega), circTravelCost_eq (by omega)]
    push_cast
    have hn0 : (0 : ℝ) < n := by linarith
    rw [← sub_pos]
    have key : M * (v - c) - n * K - t * M / (12 * (n : ℝ) ^ 2) -
        (M * (v - c) - (n + 1) * K - t * M / (12 * ((n : ℝ) + 1) ^ 2)) =
        (12 * (n : ℝ) ^ 2 * ((n : ℝ) + 1) ^ 2 * K - t * M * (2 * n + 1)) /
          (12 * (n : ℝ) ^ 2 * ((n : ℝ) + 1) ^ 2) := by
      field_simp; ring
    rw [key]
    apply div_pos _ (by positivity)
    have h1 : t * M * (2 * n + 1) < K * ((n : ℝ) + 1) ^ 3 * (2 * n + 1) :=
      mul_lt_mul_of_pos_right hlt (by linarith)
    have h2 : ((n : ℝ) + 1) * (2 * n + 1) ≤ 12 * (n : ℝ) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h2 (show 0 ≤ K * ((n : ℝ) + 1) ^ 2 by positivity)]
  have hdec : ∀ k : ℕ, circWelfare v c t M K (Js + k + 1) < circWelfare v c t M K Js := by
    intro k
    induction k with
    | zero => simpa using hstep Js le_rfl
    | succ k ih =>
      have := hstep (Js + k + 1) (by omega)
      rw [show Js + (k + 1) + 1 = Js + k + 1 + 1 by ring]
      linarith
  by_contra hlt
  push Not at hlt
  obtain ⟨k, hk⟩ : ∃ k, Jo = Js + k + 1 := ⟨Jo - Js - 1, by omega⟩
  have := hdec k
  rw [← hk] at this
  linarith [hmax Js hJs1]

/-- **Exercise 12.E.5, instance** (MWG, p. 434). With `t = M = 1` and `K = 1/216`: the free-entry
number of firms is `J* = 6` (profit `1/J³`), while welfare is maximized at `J° = 3`. -/
theorem exercise_12_E_5_instance (v c : ℝ) :
    IsEntryEquilibrium (fun J : ℕ => 1 * 1 / (J : ℝ) ^ 3) (1 / 216) 6 ∧
    ∀ J : ℕ, 1 ≤ J → circWelfare v c 1 1 (1 / 216) J ≤ circWelfare v c 1 1 (1 / 216) 3 := by
  refine ⟨⟨by norm_num, by norm_num, by norm_num⟩, fun J hJ => ?_⟩
  unfold circWelfare
  rw [circTravelCost_eq hJ, circTravelCost_eq (by norm_num)]
  have hJ' : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  rw [← sub_nonneg]
  have hnum : 0 ≤ ((J : ℝ) - 3) * ((J : ℝ) ^ 2 - 2 * J - 6) := by
    rcases le_or_gt J 3 with h | h
    · interval_cases J <;> norm_num
    · have : (4 : ℝ) ≤ J := by exact_mod_cast h
      exact mul_nonneg (by linarith) (by nlinarith)
  have hpos : 0 ≤ ((J : ℝ) - 3) * ((J : ℝ) ^ 2 - 2 * J - 6) / (216 * (J : ℝ) ^ 2) :=
    div_nonneg hnum (by positivity)
  convert hpos using 1
  push_cast
  field_simp
  ring

/-! ### Exercise 12.E.6 -/

/-- **A one-stage Cournot entry equilibrium with `J` active firms** (MWG, p. 410 and
Exercise 12.E.6), cost `c(q) = cq` plus `K` for a firm producing a positive amount, and the
symmetric Cournot outputs `q_J` of the `J`-firm market: the `J` active firms produce `q_J` (a
best response among active firms) and earn at least `K` (so not producing does not pay), and no
inactive firm can earn a positive net profit by producing any `y ≥ 0` against them. The linear
case is `IsOneStageCournotEntry` (`CompetitiveLimitExercises`). -/
def IsOneStageCournotEntryGen (p : ℝ → ℝ) (c K : ℝ) (q : ℕ → ℝ) (J : ℕ) : Prop :=
  1 ≤ J ∧ K ≤ (p (J * q J) - c) * q J ∧ ∀ y, 0 ≤ y → (p (J * q J + y) - c) * y - K ≤ 0

/-- **Exercise 12.E.6, two-stage outcomes are one-stage outcomes** (MWG, p. 434). Let `p` be
nonincreasing, `q_J ≥ 0` the symmetric Cournot outputs (`q_{J+1}` a best response to `J` rivals
producing `q_{J+1}`), with business stealing `q_{J+1} ≤ q_J` (A2). If `J` firms is a two-stage
equilibrium (`π_J ≥ K > π_{J+1}`), it is a one-stage equilibrium: an entrant facing `J` firms
producing `q_J ≥ q_{J+1}` can earn at most `π_{J+1} < K`. -/
theorem exercise_12_E_6_two_to_one {p : ℝ → ℝ} {c K : ℝ} {q : ℕ → ℝ} (hp : Antitone p)
    (hA2 : ∀ J, q (J + 1) ≤ q J)
    (hBR : ∀ (J : ℕ) (y : ℝ), 0 ≤ y →
      (p (J * q (J + 1) + y) - c) * y ≤ (p ((J + 1 : ℕ) * q (J + 1)) - c) * q (J + 1))
    {J : ℕ} (hJ : IsEntryEquilibrium (fun J : ℕ => (p (J * q J) - c) * q J) K J) :
    IsOneStageCournotEntryGen p c K q J := by
  obtain ⟨h1, h2, h3⟩ := hJ
  refine ⟨h1, h2, fun y hy => ?_⟩
  have hmono : p (J * q J + y) ≤ p (J * q (J + 1) + y) :=
    hp (by have := hA2 J; have : (0 : ℝ) ≤ J := Nat.cast_nonneg J; nlinarith)
  have := hBR J y hy
  simp only at h3
  nlinarith [mul_le_mul_of_nonneg_right hmono hy]

/-- **Exercise 12.E.6, no more firms in the one-stage game** (MWG, p. 434). If `π_J` is
nonincreasing, a one-stage equilibrium never has more active firms than a two-stage
equilibrium. -/
theorem exercise_12_E_6_fewer {p : ℝ → ℝ} {c K : ℝ} {q : ℕ → ℝ}
    (hπ : Antitone fun J : ℕ => (p (J * q J) - c) * q J) {J Js : ℕ}
    (h1 : IsOneStageCournotEntryGen p c K q J)
    (h2 : IsEntryEquilibrium (fun J : ℕ => (p (J * q J) - c) * q J) K Js) : J ≤ Js := by
  by_contra hlt
  push Not at hlt
  have := hπ (show Js + 1 ≤ J by omega)
  simp only at this
  linarith [h1.2.1, h2.2.2]

/-- The linear Cournot model satisfies the hypotheses of `exercise_12_E_6_two_to_one`: with
`p(Q) = A − BQ` and `q_J = (A − c)/(B(J + 1))`, an entrant facing `J` firms producing `q_{J+1}`
earns at most `π_{J+1}` (the difference is `B(y − q_{J+1})²`), and `q_J` is decreasing; the
general one-stage notion is MWG's linear one. -/
theorem exercise_12_E_6_linear {A B c K : ℝ} (hB : 0 < B) :
    (∀ (J : ℕ) (y : ℝ), 0 ≤ y →
      (A - B * (J * ((A - c) / (B * ((J + 1 : ℕ) + 1))) + y) - c) * y ≤
        (A - B * ((J + 1 : ℕ) * ((A - c) / (B * ((J + 1 : ℕ) + 1)))) - c) *
          ((A - c) / (B * ((J + 1 : ℕ) + 1)))) ∧
    (c ≤ A → ∀ J : ℕ, (A - c) / (B * ((J + 1 : ℕ) + 1)) ≤ (A - c) / (B * (J + 1))) ∧
    (∀ J, IsOneStageCournotEntryGen (fun s => A - B * s) c K (fun J => (A - c) / (B * (J + 1))) J
      ↔ IsOneStageCournotEntry A B c K J) ∧
    (∀ J : ℕ, (A - B * (J * ((A - c) / (B * (J + 1)))) - c) * ((A - c) / (B * (J + 1))) =
      cournotEntryProfit A B c J) := by
  refine ⟨fun J y _ => ?_, fun hAc J => ?_, fun J => ?_, fun J => ?_⟩
  · set u := (A - c) / (B * ((J + 1 : ℕ) + 1)) with hu
    have key : A - c - B * (J * u) = 2 * B * u := by
      rw [hu]; push_cast; field_simp; ring
    have key2 : A - c - B * ((J + 1 : ℕ) * u) = B * u := by
      push_cast; linarith
    have hL : A - B * (J * u + y) - c = 2 * B * u - B * y := by linarith [key]
    have hR : A - B * ((J + 1 : ℕ) * u) - c = B * u := by linarith [key2]
    rw [hL, hR]
    nlinarith [mul_nonneg hB.le (sq_nonneg (y - u))]
  · push_cast
    exact div_le_div_of_nonneg_left (by linarith) (by positivity)
      (by nlinarith)
  · unfold IsOneStageCournotEntryGen IsOneStageCournotEntry
    have e : (A - B * (J * ((A - c) / (B * (J + 1)))) - c) * ((A - c) / (B * (J + 1))) =
        cournotEntryProfit A B c J := by
      unfold cournotEntryProfit; field_simp; ring
    simp only [e]
  · unfold cournotEntryProfit; field_simp; ring

/-- **Exercise 12.E.6, the converse fails** (MWG, p. 434). Linear demand `p(Q) = 6 − Q`, `c = 0`,
`K = 4`: one active firm is a one-stage equilibrium (`π₁ = 9 ∈ [K, 4K]`), but not a two-stage
equilibrium (`π₂ = 4 ≥ K`, so a second firm would enter); the two-stage equilibrium has two
firms. -/
theorem exercise_12_E_6_converse_fails :
    IsOneStageCournotEntry 6 1 0 4 1 ∧ ¬ IsEntryEquilibrium (cournotEntryProfit 6 1 0) 4 1 ∧
      IsEntryEquilibrium (cournotEntryProfit 6 1 0) 4 2 := by
  refine ⟨⟨le_rfl, by norm_num [cournotEntryProfit], fun y _ => ?_⟩, fun h => ?_,
    ⟨by norm_num, by norm_num [cournotEntryProfit], by norm_num [cournotEntryProfit]⟩⟩
  · norm_num; nlinarith [sq_nonneg (y - 3 / 2)]
  · have := h.2.2; norm_num [cournotEntryProfit] at this

/-! ### Exercise 12.E.7 -/

/-- **An equilibrium of the one-stage entry game with announced prices** (MWG, Exercise 12.E.7),
formalized as a sustainable configuration: inverse demand `P`, average cost `AC(y)` for output
`y > 0` (including setup costs); firms `j` produce `q_j ≥ 0` and all sales occur at the price `m`
with `P(∑ q_j) = m`; active firms cover their costs (`AC(q_j) ≤ m`); and no firm can profit by
announcing a lower price `p' < m` and serving any amount `y > 0` that consumers demand at `p'`
(`p' ≤ P(y)`), i.e. `p' ≤ AC(y)`. (Departure: an undercutting firm may serve part of the demand
it attracts; MWG does not specify how demand is rationed.) -/
def IsPriceEntryConfig {n : ℕ} (P AC : ℝ → ℝ) (m : ℝ) (q : Fin n → ℝ) : Prop :=
  (∀ j, 0 ≤ q j) ∧ P (∑ j, q j) = m ∧ (∀ j, 0 < q j → AC (q j) ≤ m) ∧
    ∀ p' y, p' < m → 0 < y → p' ≤ P y → p' ≤ AC y

/-- **Exercise 12.E.7** (MWG, pp. 434-435), for `J* ≥ 2`. Let `P` be strictly decreasing on
`[0, ∞)`, and let the average cost satisfy `AC(y) ≥ c̄` for `y > 0` with the minimum `c̄` reached
only at `q̄ > 0`. If `P(J*q̄) = c̄` (i.e. `x(c̄) = J*q̄`) with `J* ≥ 2`, then in every equilibrium
the price is `c̄`, every active firm produces `q̄`, and exactly `J*` firms are active: the
perfectly competitive outcome. -/
theorem exercise_12_E_7 {n : ℕ} {P AC : ℝ → ℝ} {cbar qbar m : ℝ} {Js : ℕ}
    (hP : StrictAntiOn P (Ici 0)) (hq : 0 < qbar) (hAC : ∀ y, 0 < y → cbar ≤ AC y)
    (hmin : AC qbar = cbar) (huniq : ∀ y, 0 < y → AC y = cbar → y = qbar) (hJs : 2 ≤ Js)
    (hclear : P (Js * qbar) = cbar) {q : Fin n → ℝ} (hq_eq : IsPriceEntryConfig P AC m q) :
    m = cbar ∧ (∀ j, 0 < q j → q j = qbar) ∧ ∑ j, q j = Js * qbar ∧
      ∑ j, (if 0 < q j then (1 : ℝ) else 0) = Js := by
  obtain ⟨hq0, hclr, hcov, hund⟩ := hq_eq
  have hJs' : (2 : ℝ) ≤ Js := by exact_mod_cast hJs
  have hQ0 : 0 ≤ ∑ j, q j := Finset.sum_nonneg fun j _ => hq0 j
  have hQs0 : (0 : ℝ) ≤ Js * qbar := by positivity
  have hPq : cbar < P qbar := by
    rw [← hclear]
    exact hP (mem_Ici.2 hq.le) (mem_Ici.2 hQs0) (by nlinarith)
  have hmle : m ≤ cbar := by
    by_contra hgt; push Not at hgt
    have hmin' : cbar < min m (P qbar) := lt_min hgt hPq
    have := hund ((cbar + min m (P qbar)) / 2) qbar (by linarith [min_le_left m (P qbar)]) hq
      (by linarith [min_le_right m (P qbar)])
    rw [hmin] at this
    linarith
  have hmge : cbar ≤ m := by
    by_contra hlt; push Not at hlt
    have hQ : Js * qbar < ∑ j, q j := by
      by_contra hle; push Not at hle
      have := hP.antitoneOn (mem_Ici.2 hQ0) (mem_Ici.2 hQs0) hle
      rw [hclr, hclear] at this; linarith
    obtain ⟨j, hj⟩ : ∃ j, 0 < q j := by
      by_contra hall; push Not at hall
      have : ∑ j, q j ≤ 0 := Finset.sum_nonpos fun j _ => hall j
      linarith
    linarith [hcov j hj, hAC (q j) hj]
  have hm : m = cbar := le_antisymm hmle hmge
  have hQ : ∑ j, q j = Js * qbar := by
    have := hclr.trans (hm.trans hclear.symm)
    exact hP.injOn (mem_Ici.2 hQ0) (mem_Ici.2 hQs0) this
  have hact : ∀ j, 0 < q j → q j = qbar := fun j hj =>
    huniq (q j) hj (le_antisymm (hm ▸ hcov j hj) (hAC (q j) hj))
  refine ⟨hm, hact, hQ, ?_⟩
  have hsplit : ∑ j, q j = (∑ j, (if 0 < q j then (1 : ℝ) else 0)) * qbar := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs with h
    · rw [hact j h, one_mul]
    · rw [zero_mul]; exact le_antisymm (not_lt.1 h) (hq0 j)
  rw [hQ] at hsplit
  exact (mul_right_cancel₀ hq.ne' hsplit).symm

/-- **Exercise 12.E.7, the competitive configuration is an equilibrium and efficient** (MWG,
p. 435). Under the hypotheses of `exercise_12_E_7` (any `J* ≥ 1`), `J*` firms producing `q̄` at
the price `c̄` form an equilibrium; and with `P` nonincreasing and continuous, no outputs
`y_1, …, y_n ≥ 0` (costs `y_j AC(y_j)` for active firms) give more aggregate surplus than
`∫₀^{J*q̄} P − c̄J*q̄`, which the competitive configuration attains: it is first-best efficient. -/
theorem exercise_12_E_7_efficient {P AC : ℝ → ℝ} {cbar qbar : ℝ} {Js : ℕ}
    (hPa : Antitone P) (hPc : Continuous P) (hq : 0 < qbar) (hAC : ∀ y, 0 < y → cbar ≤ AC y)
    (hmin : AC qbar = cbar) (hclear : P (Js * qbar) = cbar) :
    IsPriceEntryConfig P AC cbar (fun _ : Fin Js => qbar) ∧
    (∀ (n : ℕ) (y : Fin n → ℝ), (∀ j, 0 ≤ y j) →
      (∫ s in (0 : ℝ)..∑ j, y j, P s) - ∑ j, (if 0 < y j then y j * AC (y j) else 0) ≤
        (∫ s in (0 : ℝ)..Js * qbar, P s) - cbar * (Js * qbar)) ∧
    (∫ s in (0 : ℝ)..∑ _j : Fin Js, qbar, P s) -
        ∑ _j : Fin Js, (if 0 < qbar then qbar * AC qbar else 0) =
      (∫ s in (0 : ℝ)..Js * qbar, P s) - cbar * (Js * qbar) := by
  have hsum : ∑ _j : Fin Js, qbar = Js * qbar := by simp
  refine ⟨⟨fun _ => hq.le, by rw [hsum, hclear], fun _ _ => by rw [hmin],
    fun p' y hp' hy _ => le_trans hp'.le (hAC y hy)⟩, fun n y hy0 => ?_, ?_⟩
  · set Q := ∑ j, y j
    set Qs := (Js : ℝ) * qbar
    have hcost : cbar * Q ≤ ∑ j, (if 0 < y j then y j * AC (y j) else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun j _ => ?_
      split_ifs with h
      · nlinarith [hAC (y j) h]
      · rw [le_antisymm (not_lt.1 h) (hy0 j), mul_zero]
    -- `∫₀^Q P − c̄Q ≤ ∫₀^{Qs} P − c̄Qs` since `P ≥ c̄` below `Qs` and `P ≤ c̄` above
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (hPc.intervalIntegrable (μ := MeasureTheory.volume) 0 Qs) (hPc.intervalIntegrable Qs Q)
    have hmid : (∫ s in Qs..Q, P s) ≤ cbar * (Q - Qs) := by
      rcases le_total Qs Q with h | h
      · have := intervalIntegral.integral_mono_on h (hPc.intervalIntegrable _ _)
          (intervalIntegrable_const (μ := MeasureTheory.volume) (c := cbar))
          (fun s hs => by rw [← hclear]; exact hPa hs.1)
        simpa [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using this
      · rw [intervalIntegral.integral_symm]
        have := intervalIntegral.integral_mono_on h
          (intervalIntegrable_const (μ := MeasureTheory.volume) (c := cbar))
          (hPc.intervalIntegrable _ _) (fun s hs => by rw [← hclear]; exact hPa hs.2)
        simp only [intervalIntegral.integral_const, smul_eq_mul] at this
        linarith
    linarith
  · rw [hsum]
    simp [hq, hmin]
    ring

/-- **Exercise 12.E.7, instance** (`J* = 2`). `P(Q) = 4 − Q`, `AC(y) = y + 1/y` (setup cost `1`,
variable cost `y²`): `c̄ = 2` at `q̄ = 1`, uniquely, and `P(2·1) = 2`. -/
theorem exercise_12_E_7_instance :
    StrictAntiOn (fun Q : ℝ => 4 - Q) (Ici 0) ∧ (∀ y : ℝ, 0 < y → 2 ≤ y + 1 / y) ∧
    (1 : ℝ) + 1 / 1 = 2 ∧ (∀ y : ℝ, 0 < y → y + 1 / y = 2 → y = 1) ∧
    (4 : ℝ) - ((2 : ℕ) : ℝ) * 1 = 2 := by
  refine ⟨fun a _ b _ h => by linarith, fun y hy => ?_, by norm_num, fun y hy h => ?_,
    by norm_num⟩
  · rw [← sub_nonneg]
    have : y + 1 / y - 2 = (y - 1) ^ 2 / y := by field_simp; ring
    rw [this]; positivity
  · have : (y - 1) ^ 2 / y = 0 := by
      have e : y + 1 / y - 2 = (y - 1) ^ 2 / y := by field_simp; ring
      rw [← e, h, sub_self]
    rcases div_eq_zero_iff.1 this with h' | h'
    · nlinarith [pow_eq_zero_iff (n := 2) (a := y - 1) two_ne_zero |>.1 h']
    · linarith

/-- Average cost of the counterexample to Exercise 12.E.7 with `J* = 1`: `2 − y` up to `y = 1`
and `y` above (minimum `c̄ = 1`, reached only at `q̄ = 1`). -/
noncomputable def e7CexAC (y : ℝ) : ℝ := if y ≤ 1 then 2 - y else y

/-- **Exercise 12.E.7 fails for `J* = 1`** (MWG, p. 435; correction). With `P(Q) = 2 − Q` and
`AC = e7CexAC`, the hypotheses hold with `q̄ = 1`, `c̄ = 1`, `J* = 1` (`P(1) = 1`), yet one firm
producing `1/2` at the price `3/2` is an equilibrium: the price exceeds `c̄` and output falls
short of the efficient `1`. (For `J* ≥ 2` the claim holds: `exercise_12_E_7`.) -/
theorem exercise_12_E_7_counterexample :
    StrictAntiOn (fun Q : ℝ => 2 - Q) (Ici 0) ∧ (∀ y, 0 < y → 1 ≤ e7CexAC y) ∧
    e7CexAC 1 = 1 ∧ (∀ y, 0 < y → e7CexAC y = 1 → y = 1) ∧ (2 : ℝ) - ((1 : ℕ) : ℝ) * 1 = 1 ∧
    IsPriceEntryConfig (fun Q : ℝ => 2 - Q) e7CexAC (3 / 2) ![1 / 2] ∧ (3 / 2 : ℝ) ≠ 1 := by
  refine ⟨fun a _ b _ h => by linarith, fun y _ => ?_, by norm_num [e7CexAC], fun y _ h => ?_,
    by norm_num, ⟨fun j => ?_, by simp; norm_num, fun j _ => ?_, fun p' y hp' hy hpy => ?_⟩,
    by norm_num⟩
  · unfold e7CexAC; split_ifs with h <;> linarith
  · unfold e7CexAC at h; split_ifs at h with h' <;> linarith
  · fin_cases j; norm_num
  · fin_cases j; norm_num [e7CexAC]
  · unfold e7CexAC; split_ifs with h <;> linarith

end MWG.MarketPower
