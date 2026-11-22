/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGCompetitiveMarkets.Surplus
import MWGProduction.ExercisesB
import MWGProduction.Geometry

/-!
# Free entry and long-run competitive equilibria (MWG Section 10.F, pp. 334-341)

* **Definition 10.F.1**: a long-run competitive equilibrium `(p*, q*, J*)` for an aggregate
  demand `x(·)` and an individual cost `c(·)` with `c(0) = 0` (`IsLREqm`; `IsLREqmReal` ignores
  the integer constraint). The long-run supply correspondence (p. 335): `PosProfit` (`Q(p) = ∞`)
  and `InLRSupply`; footnote 27: `(p*, q*, J*)` is an equilibrium iff `x(p*) ∈ Q(p*)`.
* Constant returns (p. 336, Figure 10.F.1): `p* = c`, `J*` and `q*` indeterminate.
* Strictly convex costs: **Exercise 10.F.1** (`π(p) > 0` iff `p > c'(0)`), nonexistence of a
  long-run equilibrium (Figure 10.F.2), Figure 10.F.3 (industry marginal cost `c'(Q/J)` approaches
  but never reaches `c'(0)`), and the nonclosed long-run technology (Exercise 5.B.4 from
  Chapter 5).
* A unique efficient scale `q̄` (pp. 337-338, Figure 10.F.4): `p* = c̄`, `q* = q̄`,
  `J* = x(c̄)/q̄`; the integer problem; footnote 28 (`c'(q*) = p* = c(q*)/q*`); footnote 29 (a
  range of efficient scales); footnote 25 (uniqueness of the positive output).
* p. 339: the long-run equilibrium maximizes Marshallian aggregate surplus over all aggregate
  outputs and numbers of firms (first welfare theorem without convexity).
* Example 10.F.1 (pp. 340-341): short-run versus long-run comparative statics with fixed costs
  that are sunk in the short run.
-/

namespace MWG.CompetitiveMarkets

open Filter Topology

/-- `q ≥ 0` maximizes profit `pq - c(q)` on `q ≥ 0`. -/
def IsProfitMax (c : ℝ → ℝ) (p q : ℝ) : Prop :=
  0 ≤ q ∧ ∀ q', 0 ≤ q' → p * q' - c q' ≤ p * q - c q

/-- **Definition 10.F.1** (MWG, p. 335). `(p*, q*, J*)` is a long-run competitive equilibrium
for demand `x` and individual cost `c` (with `c(0) = 0`): (i) profit maximization,
(ii) `x(p*) = J* q*`, (iii) zero profit (free entry). -/
def IsLREqm (x c : ℝ → ℝ) (p q : ℝ) (J : ℕ) : Prop :=
  IsProfitMax c p q ∧ x p = J * q ∧ p * q - c q = 0

/-- **Definition 10.F.1** (MWG, p. 335), unfolded. -/
theorem definition_10_F_1 (x c : ℝ → ℝ) (p q : ℝ) (J : ℕ) :
    IsLREqm x c p q J ↔ (0 ≤ q ∧ ∀ q', 0 ≤ q' → p * q' - c q' ≤ p * q - c q) ∧
      x p = J * q ∧ p * q - c q = 0 := Iff.rfl

/-- Definition 10.F.1 ignoring the integer constraint on the number of firms (used in
Exercises 10.F.2-10.F.4). -/
def IsLREqmReal (x c : ℝ → ℝ) (p q J : ℝ) : Prop :=
  0 ≤ J ∧ IsProfitMax c p q ∧ x p = J * q ∧ p * q - c q = 0

/-- `π(p) > 0`: some output earns positive profit (`Q(p) = ∞`, p. 335). -/
def PosProfit (c : ℝ → ℝ) (p : ℝ) : Prop := ∃ q, 0 ≤ q ∧ 0 < p * q - c q

/-- **(MWG, p. 335)** `Q ∈ Q(p)` for the long-run aggregate supply correspondence when
`π(p) = 0`: `Q = Jq` for an integer `J ≥ 0` and a profit-maximizing `q`. -/
def InLRSupply (c : ℝ → ℝ) (p Q : ℝ) : Prop :=
  ¬ PosProfit c p ∧ ∃ (J : ℕ) (q : ℝ), IsProfitMax c p q ∧ Q = J * q

/-- **Footnote 27** (MWG, p. 336). With `c(0) = 0`, `p*` is a long-run equilibrium price iff
`x(p*) ∈ Q(p*)`. -/
theorem footnote_10_F_27 {x c : ℝ → ℝ} (hc0 : c 0 = 0) (p : ℝ) :
    (∃ q J, IsLREqm x c p q J) ↔ InLRSupply c p (x p) := by
  constructor
  · rintro ⟨q, J, hmax, hx, hz⟩
    refine ⟨fun ⟨q', hq', hpos⟩ => ?_, J, q, hmax, hx⟩
    have := hmax.2 q' hq'
    linarith
  · rintro ⟨hno, J, q, hmax, hx⟩
    refine ⟨q, J, hmax, hx, le_antisymm ?_ ?_⟩
    · by_contra hlt; push Not at hlt; exact hno ⟨q, hmax.1, hlt⟩
    · have := hmax.2 0 le_rfl
      rw [hc0] at this
      linarith

/-- **(MWG, p. 335)** If `π(p) > 0`, entry makes aggregate supply unbounded: for every `M` some
number of firms, each earning positive profit, supply more than `M`. -/
theorem posProfit_unbounded {c : ℝ → ℝ} (hc0 : c 0 = 0) {p : ℝ} (h : PosProfit c p) (M : ℝ) :
    ∃ (J : ℕ) (q : ℝ), 0 < q ∧ 0 < p * q - c q ∧ M < J * q := by
  obtain ⟨q, hq, hpos⟩ := h
  have hq0 : 0 < q := by
    rcases eq_or_lt_of_le hq with h0 | h0
    · rw [← h0, hc0] at hpos; simp at hpos
    · exact h0
  obtain ⟨J, hJ⟩ := exists_nat_gt (M / q)
  exact ⟨J, q, hq0, hpos, by rwa [div_lt_iff₀ hq0] at hJ⟩

/-! ## Constant returns to scale (Figure 10.F.1) -/

/-- **(MWG, p. 336)** With `c(q) = cq` (`c > 0`) and `x(c) > 0` (demand nonincreasing below `c`),
`(p*, q*, J*)` is a long-run equilibrium iff `p* = c`, `q* ≥ 0` and `J* q* = x(c)`. -/
theorem lr_crs {x : ℝ → ℝ} {c : ℝ} (hxc : 0 < x c) (hmono : AntitoneOn x (Set.Iic c))
    {p q : ℝ} {J : ℕ} :
    IsLREqm x (fun q => c * q) p q J ↔ p = c ∧ 0 ≤ q ∧ (J : ℝ) * q = x c := by
  constructor
  · rintro ⟨⟨hq, hmax⟩, hx, hz⟩
    have hpc : p ≤ c := by
      by_contra hlt
      push Not at hlt
      have := hmax (q + 1) (by linarith)
      nlinarith
    have hxp : 0 < x p := hxc.trans_le (hmono (Set.mem_Iic.2 hpc) (Set.mem_Iic.2 le_rfl) hpc)
    have hq0 : 0 < q := by
      rw [hx] at hxp
      exact pos_of_mul_pos_right hxp (Nat.cast_nonneg J)
    have hpeq : p = c := by
      have : (p - c) * q = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · linarith
      · exact absurd h hq0.ne'
    subst hpeq
    exact ⟨rfl, hq, hx.symm⟩
  · rintro ⟨rfl, hq, hJ⟩
    exact ⟨⟨hq, fun q' _ => by ring_nf; exact le_rfl⟩, hJ.symm, by ring⟩

/-- **(MWG, p. 336)** With constant returns, `J*` and `q*` are indeterminate: `(c, x(c), 1)` and
`(c, x(c)/2, 2)` are both long-run equilibria. -/
theorem lr_crs_indeterminate {x : ℝ → ℝ} {c : ℝ} (hxc : 0 < x c)
    (hmono : AntitoneOn x (Set.Iic c)) :
    IsLREqm x (fun q => c * q) c (x c) 1 ∧ IsLREqm x (fun q => c * q) c (x c / 2) 2 ∧
      x c ≠ x c / 2 := by
  refine ⟨(lr_crs hxc hmono).2 ⟨rfl, hxc.le, by simp⟩,
    (lr_crs hxc hmono).2 ⟨rfl, by positivity, by push_cast; ring⟩, by linarith⟩

/-- **(MWG, p. 336)** The long-run supply correspondence with constant returns:
`Q(c) = [0, ∞)`, `Q(p) = {0}` for `p < c`, `Q(p) = ∞` for `p > c`. -/
theorem lrSupply_crs (c : ℝ) :
    (∀ Q, InLRSupply (fun q => c * q) c Q ↔ 0 ≤ Q) ∧
    (∀ p, 0 < p → p < c → ∀ Q, InLRSupply (fun q => c * q) p Q ↔ Q = 0) ∧
    (∀ p, c < p → PosProfit (fun q => c * q) p) := by
  refine ⟨fun Q => ⟨?_, fun hQ => ?_⟩, fun p _ hpc Q => ⟨?_, ?_⟩, fun p hcp => ⟨1, zero_le_one,
    by linarith⟩⟩
  · rintro ⟨-, J, q, ⟨hq, -⟩, rfl⟩
    exact mul_nonneg (Nat.cast_nonneg J) hq
  · refine ⟨fun ⟨q, _, hpos⟩ => by linarith, 1, Q, ⟨hQ, fun q' _ => by linarith⟩, by simp⟩
  · rintro ⟨-, J, q, ⟨hq, hmax⟩, rfl⟩
    have := hmax 0 le_rfl
    have hq0 : q = 0 := by
      by_contra hne
      have hq' : 0 < q := lt_of_le_of_ne hq (Ne.symm hne)
      nlinarith
    rw [hq0, mul_zero]
  · rintro rfl
    refine ⟨fun ⟨q, hq, hpos⟩ => by nlinarith, 0, 0, ⟨le_rfl, fun q' hq' => by nlinarith⟩,
      by simp⟩

/-! ## Strictly convex costs -/

/-- **Exercise 10.F.1** (MWG, p. 347). If `c` is strictly convex on `q ≥ 0`, differentiable there
(one-sided at `0`) and `c(0) = 0`, then `π(p) > 0` iff `p > c'(0)`. -/
theorem exercise_10_F_1 {c dc : ℝ → ℝ} (hc0 : c 0 = 0)
    (hd : ∀ q ∈ Set.Ici (0 : ℝ), HasDerivWithinAt c (dc q) (Set.Ici 0) q)
    (hconv : StrictConvexOn ℝ (Set.Ici 0) c) (p : ℝ) : PosProfit c p ↔ dc 0 < p := by
  constructor
  · rintro ⟨q, hq, hpos⟩
    by_contra hle
    push Not at hle
    rcases eq_or_lt_of_le hq with h0 | hq0
    · rw [← h0, hc0] at hpos; simp at hpos
    · have h := hconv.lt_slope_of_hasDerivWithinAt (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hq)
        hq0 (hd 0 (Set.mem_Ici.2 le_rfl))
      rw [slope_def_field, hc0, sub_zero, sub_zero, lt_div_iff₀ hq0] at h
      nlinarith
  · intro hlt
    have hg : HasDerivWithinAt (fun q => p * q - c q) (p - dc 0) (Set.Ioi 0) 0 := by
      have h := ((hasDerivWithinAt_id (0 : ℝ) (Set.Ici 0)).const_mul p).sub
        (hd 0 (Set.mem_Ici.2 le_rfl))
      rw [mul_one] at h
      exact h.mono Set.Ioi_subset_Ici_self
    obtain ⟨q, -, hq, hgt⟩ := foc_exists_gt_of_deriv_pos hg (by linarith) Set.univ Filter.univ_mem
    refine ⟨q, hq.le, ?_⟩
    simp only [mul_zero, hc0, sub_zero] at hgt
    exact hgt

/-- **(MWG, pp. 336-337, Figure 10.F.2)** With strictly convex costs, `c(0) = 0` and
`x(c'(0)) > 0`, no long-run competitive equilibrium exists. -/
theorem lr_strictConvex_nonexistence {x c dc : ℝ → ℝ} (hc0 : c 0 = 0)
    (hd : ∀ q ∈ Set.Ici (0 : ℝ), HasDerivWithinAt c (dc q) (Set.Ici 0) q)
    (hconv : StrictConvexOn ℝ (Set.Ici 0) c) (hx : 0 < x (dc 0))
    (hmono : AntitoneOn x (Set.Iic (dc 0))) : ¬ ∃ p q J, IsLREqm x c p q J := by
  rintro ⟨p, q, J, ⟨hq, hmax⟩, hxp, hz⟩
  by_cases hp : dc 0 < p
  · obtain ⟨q', hq', hpos⟩ := (exercise_10_F_1 hc0 hd hconv p).2 hp
    have := hmax q' hq'
    linarith
  · push Not at hp
    have hnpos := (exercise_10_F_1 hc0 hd hconv p).not.2 (not_lt.2 hp)
    have hq0 : q = 0 := by
      by_contra hne
      have hq' : 0 < q := lt_of_le_of_ne hq (Ne.symm hne)
      -- positive output earns negative profit
      have h := hconv.lt_slope_of_hasDerivWithinAt (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hq)
        hq' (hd 0 (Set.mem_Ici.2 le_rfl))
      rw [slope_def_field, hc0, sub_zero, sub_zero, lt_div_iff₀ hq'] at h
      nlinarith
    rw [hq0, mul_zero] at hxp
    have := hmono (Set.mem_Iic.2 hp) (Set.mem_Iic.2 le_rfl) hp
    linarith

/-- **(MWG, p. 337)** The long-run supply correspondence with strictly convex costs:
`Q(p) = ∞` for `p > c'(0)` and `Q(p) = {0}` for `p ≤ c'(0)`. -/
theorem lrSupply_strictConvex {c dc : ℝ → ℝ} (hc0 : c 0 = 0)
    (hd : ∀ q ∈ Set.Ici (0 : ℝ), HasDerivWithinAt c (dc q) (Set.Ici 0) q)
    (hconv : StrictConvexOn ℝ (Set.Ici 0) c) (p : ℝ) :
    (dc 0 < p → PosProfit c p) ∧ (p ≤ dc 0 → ∀ Q, InLRSupply c p Q ↔ Q = 0) := by
  refine ⟨(exercise_10_F_1 hc0 hd hconv p).2, fun hp Q => ⟨?_, ?_⟩⟩
  · rintro ⟨-, J, q, ⟨hq, hmax⟩, rfl⟩
    have hq0 : q = 0 := by
      by_contra hne
      have hq' : 0 < q := lt_of_le_of_ne hq (Ne.symm hne)
      have h := hconv.lt_slope_of_hasDerivWithinAt (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hq)
        hq' (hd 0 (Set.mem_Ici.2 le_rfl))
      rw [slope_def_field, hc0, sub_zero, sub_zero, lt_div_iff₀ hq'] at h
      have := hmax 0 le_rfl
      rw [hc0] at this
      nlinarith
    rw [hq0, mul_zero]
  · rintro rfl
    refine ⟨(exercise_10_F_1 hc0 hd hconv p).not.2 (not_lt.2 hp), 0, 0, ⟨le_rfl, fun q' hq' => ?_⟩,
      by simp⟩
    rw [hc0]
    rcases eq_or_lt_of_le hq' with h0 | hq0
    · rw [← h0, hc0]
    · have h := hconv.lt_slope_of_hasDerivWithinAt (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hq')
        hq0 (hd 0 (Set.mem_Ici.2 le_rfl))
      rw [slope_def_field, hc0, sub_zero, sub_zero, lt_div_iff₀ hq0] at h
      nlinarith

/-- **Figure 10.F.3** (MWG, p. 337). With strictly convex costs the industry marginal cost with
`J` firms, `c'(Q/J)`, exceeds `c'(0)` for every `J` (at `Q > 0`) but tends to `c'(0)` as
`J → ∞`. -/
theorem figure_10_F_3 {dc : ℝ → ℝ} (hmono : StrictMonoOn dc (Set.Ici 0))
    (hcont : ContinuousWithinAt dc (Set.Ici 0) 0) {Q : ℝ} (hQ : 0 < Q) :
    (∀ J : ℕ, 0 < J → dc 0 < dc (Q / J)) ∧
      Tendsto (fun J : ℕ => dc (Q / J)) atTop (𝓝 (dc 0)) := by
  refine ⟨fun J hJ => hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 (by positivity))
    (by positivity), ?_⟩
  have h1 : Tendsto (fun J : ℕ => Q / (J : ℝ)) atTop (𝓝[Set.Ici 0] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun J => ?_⟩
    · exact tendsto_const_div_atTop_nhds_zero_nat Q
    · exact Set.mem_Ici.2 (by positivity)
  exact hcont.tendsto.comp h1

/-- **(MWG, p. 337; Exercise 5.B.4)** The long-run aggregate technology generated by a
strictly convex technology need not be closed: for `{y₁ ≤ 0, y₂ ≤ √(-y₁)}` (cost `c(q) = q²`
with free disposal) the additive closure `Y⁺` is not closed (Chapter 5). -/
theorem lr_technology_not_closed : ¬ IsClosed (MWG.Production.addClosure MWG.Production.sqrtTech) :=
  MWG.Production.exercise_5_B_4_not_closed.2.2.2.2

/-! ## Efficient scale (Figure 10.F.4) -/

/-- `q̄ > 0` is an efficient scale: it minimizes average cost `c(q)/q` over `q > 0`. -/
def IsEfficientScale (c : ℝ → ℝ) (qb : ℝ) : Prop :=
  0 < qb ∧ ∀ q, 0 < q → c qb / qb ≤ c q / q

/-- At an efficient scale `q̄` with minimized average cost `c̄`, `c(q) ≥ c̄ q` for all `q ≥ 0`
(when `c(0) = 0`). -/
theorem IsEfficientScale.le_cost {c : ℝ → ℝ} {qb : ℝ} (h : IsEfficientScale c qb)
    (hc0 : c 0 = 0) {q : ℝ} (hq : 0 ≤ q) : c qb / qb * q ≤ c q := by
  rcases eq_or_lt_of_le hq with h0 | hq0
  · rw [← h0, hc0, mul_zero]
  · have := h.2 q hq0
    rw [le_div_iff₀ hq0] at this
    exact this

/-- **(MWG, pp. 337-338, Figure 10.F.4)** With a unique efficient scale `q̄`, `c(0) = 0`,
`c̄ = c(q̄)/q̄` and `x(c̄) > 0` (demand nonincreasing below `c̄`), `(p*, q*, J*)` is a long-run
equilibrium iff `p* = c̄`, `q* = q̄` and `J* q̄ = x(c̄)`. -/
theorem lr_efficientScale {x c : ℝ → ℝ} {qb : ℝ} (hc0 : c 0 = 0) (hqb : IsEfficientScale c qb)
    (huniq : ∀ q, 0 < q → c q / q = c qb / qb → q = qb) (hx : 0 < x (c qb / qb))
    (hmono : AntitoneOn x (Set.Iic (c qb / qb))) {p q : ℝ} {J : ℕ} :
    IsLREqm x c p q J ↔ p = c qb / qb ∧ q = qb ∧ (J : ℝ) * qb = x (c qb / qb) := by
  set cb := c qb / qb with hcb
  have hqb0 := hqb.1
  have hcbq : c qb = cb * qb := by rw [hcb]; field_simp
  constructor
  · rintro ⟨⟨hq, hmax⟩, hxp, hz⟩
    have hp1 : p ≤ cb := by
      by_contra hlt
      push Not at hlt
      have := hmax qb hqb0.le
      nlinarith
    have hp2 : cb ≤ p := by
      by_contra hlt
      push Not at hlt
      have hq0 : q = 0 := by
        by_contra hne
        have hq' : 0 < q := lt_of_le_of_ne hq (Ne.symm hne)
        have := hqb.le_cost hc0 hq
        nlinarith
      rw [hq0, mul_zero] at hxp
      have := hmono (Set.mem_Iic.2 hlt.le) (Set.mem_Iic.2 le_rfl) hlt.le
      linarith
    have hpeq : p = cb := le_antisymm hp1 hp2
    subst hpeq
    have hq0 : 0 < q := by
      rw [hxp] at hx
      exact pos_of_mul_pos_right hx (Nat.cast_nonneg J)
    have hAC : c q / q = cb := by
      rw [div_eq_iff hq0.ne']; linarith
    have := huniq q hq0 hAC
    subst this
    exact ⟨rfl, rfl, hxp.symm⟩
  · rintro ⟨rfl, rfl, hJ⟩
    refine ⟨⟨hqb0.le, fun q' hq' => ?_⟩, hJ.symm, by rw [hcbq]; ring⟩
    have := hqb.le_cost hc0 hq'
    rw [hcbq]
    nlinarith

/-- **(MWG, p. 338)** The integer problem: if `x(c̄)/q̄` is not an integer, no long-run
equilibrium exists. -/
theorem lr_integer_problem {x c : ℝ → ℝ} {qb : ℝ} (hc0 : c 0 = 0)
    (hqb : IsEfficientScale c qb) (huniq : ∀ q, 0 < q → c q / q = c qb / qb → q = qb)
    (hx : 0 < x (c qb / qb)) (hmono : AntitoneOn x (Set.Iic (c qb / qb)))
    (hnot : ¬ ∃ J : ℕ, (J : ℝ) * qb = x (c qb / qb)) : ¬ ∃ p q J, IsLREqm x c p q J := by
  rintro ⟨p, q, J, h⟩
  obtain ⟨-, -, hJ⟩ := (lr_efficientScale hc0 hqb huniq hx hmono).1 h
  exact hnot ⟨J, hJ⟩

/-- **(MWG, p. 338)** The long-run supply correspondence with an efficient scale:
`Q(c̄) = {Jq̄ : J ∈ ℕ}`, `Q(p) = {0}` for `p < c̄`, `Q(p) = ∞` for `p > c̄`. -/
theorem lrSupply_efficientScale {c : ℝ → ℝ} {qb : ℝ} (hc0 : c 0 = 0)
    (hqb : IsEfficientScale c qb) (huniq : ∀ q, 0 < q → c q / q = c qb / qb → q = qb) :
    (∀ Q, InLRSupply c (c qb / qb) Q ↔ ∃ J : ℕ, Q = J * qb) ∧
    (∀ p, p < c qb / qb → ∀ Q, InLRSupply c p Q ↔ Q = 0) ∧
    (∀ p, c qb / qb < p → PosProfit c p) := by
  set cb := c qb / qb with hcb
  have hqb0 := hqb.1
  have hcbq : c qb = cb * qb := by rw [hcb]; field_simp
  have hnopos : ¬ PosProfit c cb := fun ⟨q, hq, hpos⟩ => by
    have := hqb.le_cost hc0 hq; linarith
  have hmaxqb : IsProfitMax c cb qb := ⟨hqb0.le, fun q' hq' => by
    have := hqb.le_cost hc0 hq'; rw [hcbq]; nlinarith⟩
  refine ⟨fun Q => ⟨?_, ?_⟩, fun p hp Q => ⟨?_, ?_⟩, fun p hp => ⟨qb, hqb0.le, by
    rw [hcbq]; nlinarith⟩⟩
  · rintro ⟨-, J, q, ⟨hq, hmax⟩, rfl⟩
    rcases eq_or_lt_of_le hq with h0 | hq0
    · exact ⟨0, by rw [← h0]; simp⟩
    · have h1 := hmax qb hqb0.le
      have h2 := hqb.le_cost hc0 hq
      have hAC : c q / q = cb := by
        rw [div_eq_iff hq0.ne']; rw [hcbq] at h1; nlinarith
      exact ⟨J, by rw [huniq q hq0 hAC]⟩
  · rintro ⟨J, rfl⟩
    exact ⟨hnopos, J, qb, hmaxqb, rfl⟩
  · rintro ⟨-, J, q, ⟨hq, hmax⟩, rfl⟩
    have hq0 : q = 0 := by
      by_contra hne
      have hq' : 0 < q := lt_of_le_of_ne hq (Ne.symm hne)
      have h1 := hmax 0 le_rfl
      have h2 := hqb.le_cost hc0 hq
      rw [hc0] at h1
      nlinarith
    rw [hq0, mul_zero]
  · rintro rfl
    refine ⟨fun ⟨q, hq, hpos⟩ => by
      have := hqb.le_cost hc0 hq; nlinarith, 0, 0, ⟨le_rfl, fun q' hq' => ?_⟩, by simp⟩
    have := hqb.le_cost hc0 hq'
    rw [hc0]
    nlinarith

/-- **Footnote 28** (MWG, p. 338). If `c` is differentiable at a positive equilibrium output
`q*`, then `c'(q*) = p* = c(q*)/q*`: `q*` is a critical point of average cost. -/
theorem footnote_10_F_28 {x c : ℝ → ℝ} {p q d : ℝ} {J : ℕ} (h : IsLREqm x c p q J)
    (hq : 0 < q) (hd : HasDerivAt c d q) : d = p ∧ p = c q / q := by
  obtain ⟨⟨-, hmax⟩, -, hz⟩ := h
  have hder : HasDerivWithinAt (fun z => p * z - c z) (p - d) (Set.Ici 0) q := by
    have h1 := ((hasDerivAt_id q).const_mul p).sub hd
    rw [mul_one] at h1
    exact h1.hasDerivWithinAt
  have := (foc_max_necessary hder hq.le hmax).2 hq
  refine ⟨by linarith, ?_⟩
  rw [eq_div_iff hq.ne']
  linarith

/-- **Footnote 28** (MWG, p. 338) with Exercise 5.D.1 (Chapter 5): at an efficient scale where `c`
is differentiable, `c'(q̄) = c(q̄)/q̄`; hence when average cost is U-shaped (no other critical
point), `q* = q̄` and `p* = c̄`. -/
theorem footnote_10_F_28_ushaped {x c dc : ℝ → ℝ} {qb p q : ℝ} {J : ℕ}
    (hqb : IsEfficientScale c qb) (hd : ∀ q, 0 < q → HasDerivAt c (dc q) q)
    (hcrit : ∀ q, 0 < q → dc q = c q / q → q = qb) (h : IsLREqm x c p q J) (hq : 0 < q) :
    q = qb ∧ p = c qb / qb ∧ dc qb = c qb / qb := by
  have hb := (MWG.Production.exercise_5_D_1 hqb.1 hqb.2 (hd qb hqb.1)).symm
  obtain ⟨h1, h2⟩ := footnote_10_F_28 h hq (hd q hq)
  have hqq := hcrit q hq (h1.trans h2)
  subst hqq
  exact ⟨rfl, h2, hb⟩

/-- **Footnote 29** (MWG, p. 339). If average cost attains its minimum `c̄` exactly on an
interval `[q₋, q̄]` of efficient scales, a long-run equilibrium exists iff `x(c̄) = Jq` for some
`q ∈ [q₋, q̄]` and integer `J`. -/
theorem footnote_10_F_29 {x c : ℝ → ℝ} {a b cb : ℝ} (hc0 : c 0 = 0) (ha : 0 < a)
    (hab : a ≤ b) (hmin : ∀ q, 0 < q → cb ≤ c q / q)
    (heff : ∀ q, 0 < q → (c q / q = cb ↔ q ∈ Set.Icc a b)) (hx : 0 < x cb)
    (hmono : AntitoneOn x (Set.Iic cb)) :
    (∃ p q J, IsLREqm x c p q J) ↔ ∃ q ∈ Set.Icc a b, ∃ J : ℕ, (J : ℝ) * q = x cb := by
  have hle : ∀ q, 0 ≤ q → cb * q ≤ c q := fun q hq => by
    rcases eq_or_lt_of_le hq with h0 | hq0
    · rw [← h0, hc0, mul_zero]
    · have := hmin q hq0; rwa [le_div_iff₀ hq0] at this
  have hca : c a = cb * a := by
    have := (heff a ha).2 ⟨le_rfl, hab⟩
    rw [div_eq_iff ha.ne'] at this; linarith
  constructor
  · rintro ⟨p, q, J, ⟨hq, hmax⟩, hxp, hz⟩
    have hp1 : p ≤ cb := by
      by_contra hlt; push Not at hlt
      have := hmax a ha.le; nlinarith
    have hp2 : cb ≤ p := by
      by_contra hlt; push Not at hlt
      have hq0 : q = 0 := by
        by_contra hne
        have hq' : 0 < q := lt_of_le_of_ne hq (Ne.symm hne)
        have := hle q hq; nlinarith
      rw [hq0, mul_zero] at hxp
      have := hmono (Set.mem_Iic.2 hlt.le) (Set.mem_Iic.2 le_rfl) hlt.le
      linarith
    have hpeq : p = cb := le_antisymm hp1 hp2
    subst hpeq
    have hq0 : 0 < q := by
      rw [hxp] at hx; exact pos_of_mul_pos_right hx (Nat.cast_nonneg J)
    have hAC : c q / q = p := by rw [div_eq_iff hq0.ne']; linarith
    exact ⟨q, (heff q hq0).1 hAC, J, hxp.symm⟩
  · rintro ⟨q, hq, J, hJ⟩
    have hq0 : 0 < q := ha.trans_le hq.1
    have hcq : c q = cb * q := by
      have := (heff q hq0).2 hq; rw [div_eq_iff hq0.ne'] at this; linarith
    exact ⟨cb, q, J, ⟨hq0.le, fun q' hq' => by have := hle q' hq'; rw [hcq]; nlinarith⟩,
      hJ.symm, by rw [hcq]; ring⟩

/-- **Footnote 25** (MWG, p. 335). If `c` is strictly convex on `(0, ∞)`, a firm's supply
correspondence contains at most one positive output at any price. -/
theorem footnote_10_F_25 {c : ℝ → ℝ} (hconv : StrictConvexOn ℝ (Set.Ioi 0) c) {p q₁ q₂ : ℝ}
    (h₁ : IsProfitMax c p q₁) (h₂ : IsProfitMax c p q₂) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂) :
    q₁ = q₂ := by
  by_contra hne
  have hmid := hconv.2 (Set.mem_Ioi.2 hq₁) (Set.mem_Ioi.2 hq₂) hne
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at hmid
  have e1 := h₁.2 _ (by positivity : (0 : ℝ) ≤ 1 / 2 * q₁ + 1 / 2 * q₂)
  have e2 := h₁.2 q₂ hq₂.le
  have e3 := h₂.2 q₁ hq₁.le
  nlinarith

/-! ## Efficiency of the long-run equilibrium (p. 339) -/

/-- **(MWG, p. 339)** The long-run equilibrium maximizes aggregate surplus even without convexity.
If `c(0) = 0` and `c(q) ≥ c̄ q` for all `q ≥ 0` (efficient scale with average cost `c̄ > 0`),
then the competitive aggregate `x(c̄)` gives aggregate surplus `γ(x(c̄)) - c̄ x(c̄)` at least
`γ(x̂) - J c(x̂/J)` for every aggregate `x̂ ≥ 0` and every number `J ≥ 1` of firms. -/
theorem lr_maximizes_surplus {ι : Type*} [Fintype ι] [Nonempty ι] (C : ι → QLConsumer) {c : ℝ → ℝ}
    {cb : ℝ} (hcb : 0 < cb) (hle : ∀ q, 0 ≤ q → cb * q ≤ c q) {X : ℝ} (hX : 0 ≤ X) {J : ℕ}
    (hJ : 0 < J) :
    grossBenefit C X - J * c (X / J) ≤ grossBenefit C (aggDemand C cb) - cb * aggDemand C cb := by
  have hfoc : ∀ i, IsFOCSol (C i).dφ cb ((C i).demand cb) := fun i => (C i).demand_spec hcb
  have hγ := grossBenefit_eq_of_foc hfoc
  have hJ' : (0 : ℝ) < J := Nat.cast_pos.2 hJ
  have hcost : cb * X ≤ J * c (X / J) := by
    have := hle (X / J) (by positivity)
    have e : cb * X = J * (cb * (X / J)) := by field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left this hJ'.le
  have hγX : grossBenefit C X ≤ grossBenefit C (aggDemand C cb) + cb * (X - aggDemand C cb) := by
    rw [grossBenefit_eq C hX, aggDemand, hγ]
    have := foc_benefit_le hfoc (fun i => (optAlloc_foc C hX i).1)
    rwa [optAlloc_sum C hX] at this
  linarith

/-! ## Example 10.F.1: short-run and long-run comparative statics -/

/-- **(10.F.1)** (MWG, p. 340). The long-run cost `c(q) = K + ψ(q)` for `q > 0`, `c(0) = 0`. -/
noncomputable def lumpyCost (K : ℝ) (ψ : ℝ → ℝ) (q : ℝ) : ℝ := if q = 0 then 0 else K + ψ q

/-- **Example 10.F.1** (MWG, pp. 340-341). Let the long-run cost be (10.F.1) with `K > 0` and
`ψ` a strictly convex cost (`ψ(0) = 0`, `ψ' > 0`, `ψ'' ≥ 0`, `ψ' → ∞`), with efficient scale
`q̄` and `c̄ = c(q̄)/q̄`, and let the industry start in a long-run equilibrium with `J₀` firms
for demand `x₀` (`J₀ q̄ = x₀(c̄)`). After a fall in demand to `x₁ < x₀` (nonincreasing), at the
short-run equilibrium price `p_s` with the `J₀` firms (cost (10.F.2), `K` sunk) we have
`p_s < c̄` and active firms make losses; in the new long-run equilibrium the price returns to
`c̄`, each firm produces `q̄`, and the number of firms falls to `J₁ < J₀`. -/
theorem example_10_F_1 {K : ℝ} (hK : 0 < K) (F : QLFirmStrict) (hψ0 : F.c 0 = 0) {qb : ℝ}
    (hqb : IsEfficientScale (lumpyCost K F.c) qb) {x₀ x₁ : ℝ → ℝ} (hfall : ∀ p, x₁ p < x₀ p)
    (hmono : AntitoneOn x₁ (Set.Ioi 0))
    {J₀ : ℕ} (hJ₀ : (J₀ : ℝ) * qb = x₀ (lumpyCost K F.c qb / qb))
    {ps : ℝ} (hps : 0 < ps) (hSR : x₁ ps = J₀ * F.supply ps) :
    ps < lumpyCost K F.c qb / qb ∧
    ps * F.supply ps - (K + F.c (F.supply ps)) < 0 ∧
    ∀ J₁ : ℕ, (J₁ : ℝ) * qb = x₁ (lumpyCost K F.c qb / qb) →
      J₁ < J₀ ∧ IsLREqm x₁ (lumpyCost K F.c) (lumpyCost K F.c qb / qb) qb J₁ := by
  set c := lumpyCost K F.c with hcdef
  set cb := c qb / qb with hcb
  have hqb0 := hqb.1
  have hc0 : c 0 = 0 := by simp [hcdef, lumpyCost]
  have hcq : ∀ q, q ≠ 0 → c q = K + F.c q := fun q hq => by simp [hcdef, lumpyCost, hq]
  have hcb0 : 0 < cb := by
    rw [hcb, hcq qb hqb0.ne']
    have : F.c 0 ≤ F.c qb := F.toQLFirm.c_strictMono.monotoneOn (Set.mem_Ici.2 le_rfl)
      (Set.mem_Ici.2 hqb0.le) hqb0.le
    rw [hψ0] at this
    exact div_pos (by linarith) hqb0
  -- the short-run supply at `c̄` is `q̄` (footnote 28 / Exercise 5.D.1)
  have hdc : F.dc qb = cb := by
    have hd : HasDerivAt c (F.dc qb) qb := by
      have h1 : HasDerivAt (fun q => K + F.c q) (F.dc qb) qb :=
        (foc_hasDerivAt F.hasDeriv hqb0).const_add K
      refine h1.congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds hqb0] with q hq
      exact hcq q (ne_of_gt hq)
    exact (MWG.Production.exercise_5_D_1 hqb0 hqb.2 hd).symm
  have hsupp : F.supply cb = qb := F.supply_eq ⟨hqb0.le, hdc.symm.le, fun _ => hdc.symm⟩
  have hps_lt : ps < cb := by
    by_contra hle
    push Not at hle
    have h1 : qb ≤ F.supply ps := hsupp ▸ F.supply_monotone hle
    have h2 : x₁ ps ≤ x₁ cb := hmono hcb0 hps hle
    have h3 := hfall cb
    have h4 : (J₀ : ℝ) * qb ≤ J₀ * F.supply ps := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
    linarith
  refine ⟨hps_lt, ?_, fun J₁ hJ₁ => ⟨?_, ?_⟩⟩
  · set qs := F.supply ps
    rcases eq_or_lt_of_le (F.supply_nonneg ps : 0 ≤ qs) with h0 | hq0
    · have h0' : qs = 0 := h0.symm
      rw [h0', hψ0]; linarith
    · have hle := hqb.le_cost hc0 hq0.le
      rw [hcq qs hq0.ne'] at hle
      nlinarith
  · have h1 := hfall cb
    have : (J₁ : ℝ) * qb < J₀ * qb := by rw [hJ₁, hJ₀]; exact h1
    exact_mod_cast lt_of_mul_lt_mul_right this hqb0.le
  · refine ⟨⟨hqb0.le, fun q' hq' => ?_⟩, hJ₁.symm, ?_⟩
    · have := hqb.le_cost hc0 hq'
      have e : c qb = cb * qb := by rw [hcb]; field_simp
      rw [e]
      nlinarith
    · have e : c qb = cb * qb := by rw [hcb]; field_simp
      rw [e]; ring

end MWG.CompetitiveMarkets
