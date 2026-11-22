/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGCoreFoundations.Basic
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Calculus.Deriv.Abs

/-!
# Noncooperative foundations of Walrasian equilibria (MWG Section 18.C, pp. 660-665)

* The abstract trading model (p. 660, `TradingModel`, requirements `TradingModel.IsValid`),
  **Definition 18.C.1** (`TradingModel.IsTradingEqm`, `definition_18_C_1`), the notation of
  **footnote 7** (`footnote_18_7`), the effective budget set `Bᵢ(a)` (p. 661,
  `TradingModel.effBudget`; equilibrium bundles are maximal there,
  `TradingModel.isTradingEqm_maximal_effBudget`) and **footnote 8** (`footnote_18_8`: if the
  price does not react to `a'ᵢ`, achievable net trades lie in the hyperplane `p̄·z = 0` and, for
  `p̄ ≥ 0`, `Bᵢ(a)` is inside the Walrasian budget `B(p̄, p̄·ωᵢ)`).
* p. 661, insensitivity to own actions (`price_insensitivity`): if `p(a) = φ((1/r) ∑ᵢ aᵢ)` with
  `φ` continuous and the actions in a bounded set of `ℝ^m`, a unilateral deviation moves the price
  by less than any `ε > 0` once `r` is large, uniformly. (Actions are taken in `ℝ^m`.)
* **Example 18.C.1** (pp. 661-663, footnotes 10, 12): the Cournot model as a trading model
  (`cournotModel`), the Walrasian benchmark (`example_18_C_1_walras`), the Cournot equilibria
  bounded away from the Walrasian outcome (`example_18_C_1`), why they are not Walrasian
  (`example_18_C_1_not_walrasian`) and a concrete selection satisfying all hypotheses
  (`example_18_C_1_instance`). "Very elastic" is made precise as: `p` nonincreasing and
  `s p(s)` nondecreasing on `[0, b']` (both as drawn in Figure 18.C.3).
* **Example 18.C.2** (p. 663, footnote 13): the complements model (`complementsModel`), the
  null-production equilibrium (`example_18_C_2`; it needs only `ψ(·,0) ≡ 0 ≡ ψ(0,·)`), and for
  `ψ = √(x₁x₂)` the price discontinuity at the origin (`footnote_18_13_prices`,
  `footnote_18_13_discontinuous`), the failure of differentiability
  (`footnote_18_13_not_differentiable`), homotheticity, nonlinearity and concavity
  (`footnote_18_13_psi`, `footnote_18_13_psi_concave`). As printed, `p(q₁, q₂) ≫ 0` cannot hold
  on the axes when `ψ(·, 0) ≡ 0` (`partialOne_axis_eq_zero`).
* **Example 18.C.3** (pp. 663-665, footnote 14): trading posts with the price (18.C.1)
  (`tpPrice`) and the share form of the trading rule (`tpGood`, `tpMoney`), which is the book's
  `a''/p - a'` with `p·g = 0` and clearing when both sides are active (`example_18_C_3_rule`);
  continuity of (18.C.1) where goods are offered (`example_18_C_3_continuous`) and the
  impossibility of a continuous price at the inactive post
  (`example_18_C_3_no_continuous_price`); footnote 14 (`footnote_18_14`); an inactive post
  preserves equilibrium (`example_18_C_3_inactive_post`, for nondecreasing utilities); a
  consumer without money cannot buy goods (`example_18_C_3_no_money`).
* **Exercise 18.C.1** (`L = 2`): with the others active on both sides (`A', A'' > 0`) every
  bid, one- or two-sided, yields the net trades `((bA' - sA'')/(b + A''), (sA'' - bA')/(s + A'))`
  (`tp_outcome`, one-sided cases `exercise_18_C_1_one_sided`), all on the curve
  `m = φ(g) = -gA''/(A' - g)` (`tp_outcome_on_frontier`); the achievable `g` form
  `[-ω₁, ω₂A'/(ω₂ + A'')]` (`tp_reachable`); the effective budget set is the region under `φ`
  (`exercise_18_C_1_eq`), convex (`exercise_18_C_1_convex`), with upper boundary the graph of
  the strictly concave `φ` (`tpFrontier_strictConcaveOn`, `exercise_18_C_1_boundary`: no
  straight segments).

Verbal or graphical: Figures 18.C.1-18.C.4, footnote 9 (references), footnote 11 (money is a
Giffen good in the example), the quasilinear partial-equilibrium remark on p. 662, the
individual-spanning discussion (p. 661) and the cash-in-advance remark (p. 665).
-/

namespace MWG.CoreFoundations

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.WelfareTheorems

/-! ### The abstract trading model (p. 660) -/

/-- **Section 18.C** (MWG, p. 660). The abstract model of price-mediated competition: agents
`i : ι`, a set `P ⊆ ℝ^L` of price vectors, action sets `Aᵢ` of market actions (elements of
`Act`), endowments `ωᵢ`, a trading rule `g(aᵢ; p) ∈ ℝ^L`, a market clearing process `a ↦ p(a)`
and utilities `uᵢ`, evaluated at `g(aᵢ; p(a)) + ωᵢ`. -/
structure TradingModel (ι Act : Type*) (L : ℕ) where
  /-- The set `P` of possible price vectors. -/
  P : Set (Fin L → ℝ)
  /-- The action sets `Aᵢ ⊆ A`. -/
  A : ι → Set Act
  /-- The endowments `ωᵢ`. -/
  ω : ι → Fin L → ℝ
  /-- The trading rule `g(aᵢ; p)`. -/
  g : Act → (Fin L → ℝ) → Fin L → ℝ
  /-- The market clearing price `p(a)`. -/
  price : (ι → Act) → Fin L → ℝ
  /-- The utility functions `uᵢ`. -/
  u : ι → (Fin L → ℝ) → ℝ

variable {ι Act : Type*} {L : ℕ}

/-- **Section 18.C** (MWG, p. 660). The requirements of the abstract model: the trading rule
satisfies `p·g(a; p) = 0` for every action and every `p ∈ P`, and the clearing price of every
profile of feasible actions lies in `P`. -/
def TradingModel.IsValid (M : TradingModel ι Act L) : Prop :=
  (∀ a, ∀ p ∈ M.P, p ⬝ᵥ M.g a p = 0) ∧ ∀ a : ι → Act, (∀ i, a i ∈ M.A i) → M.price a ∈ M.P

/-- The utility agent `i` obtains at the action profile `a`: `uᵢ(g(aᵢ; p(a)) + ωᵢ)`. -/
def TradingModel.payoff (M : TradingModel ι Act L) (a : ι → Act) (i : ι) : ℝ :=
  M.u i (M.g (a i) (M.price a) + M.ω i)

/-- **Definition 18.C.1** (MWG, p. 660). `a*` is a trading equilibrium: `a*ᵢ ∈ Aᵢ` for every
`i`, and no agent gains by a unilateral deviation,
`uᵢ(g(a*ᵢ; p(a*)) + ωᵢ) ≥ uᵢ(g(aᵢ; p(aᵢ, a*₋ᵢ)) + ωᵢ)` for all `aᵢ ∈ Aᵢ` (the profile
`(aᵢ, a*₋ᵢ)` of footnote 7 is `Function.update a* i aᵢ`). -/
def TradingModel.IsTradingEqm [DecidableEq ι] (M : TradingModel ι Act L) (a : ι → Act) :
    Prop :=
  (∀ i, a i ∈ M.A i) ∧
    ∀ i, ∀ b ∈ M.A i, M.u i (M.g b (M.price (Function.update a i b)) + M.ω i) ≤
      M.u i (M.g (a i) (M.price a) + M.ω i)

/-- **Footnote 7** (MWG, p. 660). The notation `(aᵢ, a*₋ᵢ)`: the profile that agrees with `a*`
except in coordinate `i`; replacing `a*ᵢ` by itself gives back `a*`. -/
theorem footnote_18_7 [DecidableEq ι] (a : ι → Act) (i : ι) (b : Act) :
    Function.update a i b i = b ∧ (∀ j, j ≠ i → Function.update a i b j = a j) ∧
      Function.update a i (a i) = a :=
  ⟨Function.update_self i b a, fun _ hj => Function.update_of_ne hj b a,
    Function.update_eq_self i a⟩

/-- **Definition 18.C.1** (MWG, p. 660), in terms of payoffs. -/
theorem definition_18_C_1 [DecidableEq ι] (M : TradingModel ι Act L) (a : ι → Act) :
    M.IsTradingEqm a ↔ (∀ i, a i ∈ M.A i) ∧
      ∀ i, ∀ b ∈ M.A i, M.payoff (Function.update a i b) i ≤ M.payoff a i := by
  unfold TradingModel.IsTradingEqm TradingModel.payoff
  simp only [Function.update_self]

/-- **Section 18.C** (MWG, p. 661). The effective budget set of agent `i` at `a`:
`Bᵢ(a) = {xᵢ ∈ ℝ^L₊ : xᵢ - ωᵢ ≤ g(a'ᵢ; p(a'ᵢ, a₋ᵢ))` for some `a'ᵢ ∈ Aᵢ}`. (The Walrasian
budget `B(p, p·ωᵢ)` of the text is `budgetSetOn (nonnegOrthant L) p (p ⬝ᵥ ωᵢ)`.) -/
def TradingModel.effBudget [DecidableEq ι] (M : TradingModel ι Act L) (a : ι → Act) (i : ι) :
    Set (Fin L → ℝ) :=
  {x | x ∈ nonnegOrthant L ∧
    ∃ b ∈ M.A i, x - M.ω i ≤ M.g b (M.price (Function.update a i b))}

/-- **Section 18.C** (MWG, p. 661). At a trading equilibrium every agent's equilibrium bundle,
when nonnegative, lies in her effective budget set, and it is maximal there for a utility that
is nondecreasing: no point of `Bᵢ(a*)` is better. -/
theorem TradingModel.isTradingEqm_maximal_effBudget [DecidableEq ι] (M : TradingModel ι Act L)
    {a : ι → Act} (h : M.IsTradingEqm a) (i : ι)
    (hmono : ∀ x y : Fin L → ℝ, x ≤ y → M.u i x ≤ M.u i y)
    (hx : M.g (a i) (M.price a) + M.ω i ∈ nonnegOrthant L) :
    M.g (a i) (M.price a) + M.ω i ∈ M.effBudget a i ∧
      ∀ x ∈ M.effBudget a i, M.u i x ≤ M.u i (M.g (a i) (M.price a) + M.ω i) := by
  refine ⟨⟨hx, a i, h.1 i, ?_⟩, ?_⟩
  · rw [Function.update_eq_self, add_sub_cancel_right]
  · rintro x ⟨-, b, hb, hle⟩
    refine (hmono _ _ fun l => ?_).trans (h.2 i b hb)
    have := hle l
    simp only [Pi.sub_apply] at this
    simp only [Pi.add_apply]
    linarith

/-- **Footnote 8** (MWG, p. 661). Since `p(a'ᵢ, a₋ᵢ)·g(a'ᵢ; p(a'ᵢ, a₋ᵢ)) = 0`, if the price
`p(a'ᵢ, a₋ᵢ) = p̄` does not depend on `a'ᵢ ∈ Aᵢ`, then every achievable net trade lies in the
hyperplane `{z : p̄·z = 0}` perpendicular to `p̄`, and, when `p̄ ≥ 0`, the effective budget set
is contained in the Walrasian budget set `B(p̄, p̄·ωᵢ)`. -/
theorem footnote_18_8 [DecidableEq ι] (M : TradingModel ι Act L) (hv : M.IsValid)
    {a : ι → Act} (ha : ∀ j, a j ∈ M.A j) (i : ι) {pbar : Fin L → ℝ}
    (hconst : ∀ b ∈ M.A i, M.price (Function.update a i b) = pbar) :
    (∀ b ∈ M.A i, pbar ⬝ᵥ M.g b (M.price (Function.update a i b)) = 0) ∧
      (0 ≤ pbar → M.effBudget a i ⊆ budgetSetOn (nonnegOrthant L) pbar (pbar ⬝ᵥ M.ω i)) := by
  have hzero : ∀ b ∈ M.A i, pbar ⬝ᵥ M.g b (M.price (Function.update a i b)) = 0 := by
    intro b hb
    have hall : ∀ j, Function.update a i b j ∈ M.A j := by
      intro j
      by_cases hj : j = i
      · subst hj
        simpa using hb
      · rw [Function.update_of_ne hj]
        exact ha j
    have := hv.1 b _ (hv.2 _ hall)
    rwa [hconst b hb] at this ⊢
  refine ⟨hzero, fun hp x ⟨hx, b, hb, hle⟩ => ⟨hx, ?_⟩⟩
  have h1 : pbar ⬝ᵥ (x - M.ω i) ≤ pbar ⬝ᵥ M.g b (M.price (Function.update a i b)) := by
    simp only [dotProduct]
    exact Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (hle l) (hp l)
  rw [hzero b hb, dotProduct_sub] at h1
  linarith

/-- **Section 18.C** (MWG, p. 661), insensitivity of prices to own actions made precise. If the
price depends only on the average action, `p(a) = φ((1/r) ∑ᵢ aᵢ)`, with `φ` continuous and the
actions in a bounded set `K ⊆ ℝ^m`, then the effect of one agent's action on the price becomes
negligible as the economy grows: for every `ε > 0` there is `R` such that in every economy with
`r ≥ R` agents, any unilateral change of action moves the price by less than `ε`. (Uniformly in
the profile, the agent and the deviation; the proof uses uniform continuity of `φ` on the
compact closure of the convex hull of `K`.) -/
theorem price_insensitivity {m : ℕ} {F : Type*} [PseudoMetricSpace F]
    (φ : (Fin m → ℝ) → F) (hφ : Continuous φ) {K : Set (Fin m → ℝ)}
    (hK : Bornology.IsBounded K) :
    ∀ ε > 0, ∃ R : ℕ, ∀ r : ℕ, R ≤ r → ∀ a : Fin r → Fin m → ℝ, (∀ i, a i ∈ K) →
      ∀ i, ∀ b ∈ K, dist (φ ((r : ℝ)⁻¹ • ∑ j, Function.update a i b j))
        (φ ((r : ℝ)⁻¹ • ∑ j, a j)) < ε := by
  intro ε hε
  set C := closure (convexHull ℝ K) with hC
  have hCc : IsCompact C :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure
      (isBounded_convexHull.mpr hK).closure
  obtain ⟨δ, hδ, hunif⟩ :=
    Metric.uniformContinuousOn_iff.mp (hCc.uniformContinuousOn_of_continuous hφ.continuousOn)
      ε hε
  obtain ⟨M, hM⟩ := hK.subset_closedBall 0
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * |M| / δ)
  refine ⟨n + 1, fun r hr a ha i b hb => ?_⟩
  have hr0 : (0 : ℝ) < r := by
    have : (1 : ℝ) ≤ r := by exact_mod_cast (Nat.le_add_left 1 n).trans hr
    linarith
  -- the averages lie in the convex hull of `K`
  have hmean : ∀ c : Fin r → Fin m → ℝ, (∀ j, c j ∈ K) →
      (r : ℝ)⁻¹ • ∑ j, c j ∈ C := by
    intro c hc
    apply subset_closure
    rw [Finset.smul_sum]
    refine (convex_convexHull ℝ K).sum_mem (fun _ _ => inv_nonneg.mpr hr0.le) ?_
      fun j _ => subset_convexHull ℝ K (hc j)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_inv_cancel₀ hr0.ne'
  have hupd : ∀ j, Function.update a i b j ∈ K := by
    intro j
    by_cases hj : j = i
    · subst hj
      simpa using hb
    · rw [Function.update_of_ne hj]
      exact ha j
  refine hunif _ (hmean _ hupd) _ (hmean _ ha) ?_
  -- the two averages differ by `(b - aᵢ)/r`
  have hsum : ∑ j, Function.update a i b j = ∑ j, a j + (b - a i) := by
    have : Function.update a i b = a + Pi.single i (b - a i) := by
      funext j
      by_cases hj : j = i
      · subst hj
        simp
      · simp [hj]
    rw [this]
    simp only [Pi.add_apply]
    rw [Finset.sum_add_distrib]
    simp
  rw [dist_eq_norm, hsum, smul_add, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
    abs_inv, abs_of_pos hr0]
  have hb' : ‖b‖ ≤ M := mem_closedBall_zero_iff.mp (hM hb)
  have ha' : ‖a i‖ ≤ M := mem_closedBall_zero_iff.mp (hM (ha i))
  have hdiff : ‖b - a i‖ ≤ 2 * |M| := by
    have := norm_sub_le b (a i)
    have := le_abs_self M
    linarith
  have hrn : (n : ℝ) + 1 ≤ r := by exact_mod_cast hr
  have hlt : 2 * |M| < δ * r := by
    rw [div_lt_iff₀ hδ] at hn
    nlinarith
  calc (r : ℝ)⁻¹ * ‖b - a i‖ ≤ (r : ℝ)⁻¹ * (2 * |M|) :=
        mul_le_mul_of_nonneg_left hdiff (inv_nonneg.mpr hr0.le)
    _ < (r : ℝ)⁻¹ * (δ * r) := mul_lt_mul_of_pos_left hlt (inv_pos.mpr hr0)
    _ = δ := by field_simp

/-! ### Example 18.C.1: general equilibrium, single-good Cournot competition (pp. 661-663) -/

/-- **Example 18.C.1** and **footnote 10** (MWG, pp. 661-662). The Cournot model as a trading
model: the players are the `J` firms; good `0` is the consumption good and good `1` is money
(price `1`); firm `j` is "endowed" with one unit of the good, chooses `qⱼ ∈ [0, 1] = Aⱼ`, and
the trading rule is `g(qⱼ; p, 1) = (-qⱼ, p qⱼ)`. With `r` consumers the market selects the price
`p(∑ⱼ qⱼ / r)` (the price selection `sel`), and the owners care only about money. -/
noncomputable def cournotModel (J r : ℕ) (sel : ℝ → ℝ) : TradingModel (Fin J) ℝ 2 where
  P := {p | p 1 = 1}
  A := fun _ => Set.Icc 0 1
  ω := fun _ => ![1, 0]
  g := fun q p => ![-q, p 0 * q]
  price := fun a => ![sel ((∑ j, a j) / r), 1]
  u := fun _ x => x 1

/-- The Cournot model satisfies the requirements of the abstract model:
`(p, 1)·(-q, pq) = 0`. -/
theorem cournotModel_isValid (J r : ℕ) (sel : ℝ → ℝ) : (cournotModel J r sel).IsValid := by
  refine ⟨fun q p hp => ?_, fun a _ => ?_⟩
  · change p 1 = 1 at hp
    simp [cournotModel, dotProduct, Fin.sum_univ_two, hp]
  · rfl

/-- The profit of firm `j` in the Cournot model: `p(∑ₖ qₖ / r) qⱼ`. -/
theorem cournotModel_payoff (J r : ℕ) (sel : ℝ → ℝ) (a : Fin J → ℝ) (j : Fin J) :
    (cournotModel J r sel).payoff a j = sel ((∑ k, a k) / r) * a j := by
  simp [TradingModel.payoff, cournotModel]

/-- The total production after firm `j` changes its output from `c` to `q`, when all firms
produce `c`: `q + (J - 1)c`. -/
theorem cournot_sum_update (J : ℕ) (j : Fin J) (c q : ℝ) :
    ∑ k, Function.update (fun _ : Fin J => c) j q k = q - c + J * c := by
  have : Function.update (fun _ : Fin J => c) j q = (fun _ => c) + Pi.single j (q - c) := by
    funext k
    by_cases hk : k = j
    · subst hk
      simp
    · simp [hk]
  rw [this]
  simp only [Pi.add_apply]
  rw [Finset.sum_add_distrib]
  simp
  ring

/-- **Example 18.C.1** (MWG, p. 662), the Walrasian benchmark. A price-taking firm facing a
positive price `p*` maximizes profit `p* q` over `q ∈ [0, 1]` exactly at capacity `q = 1`; when
every firm produces at capacity the production per consumer is `J/r`, so the Walrasian price is
the selected price `p* = p(J/r)`. -/
theorem example_18_C_1_walras {pstar : ℝ} (hp : 0 < pstar) (J r : ℕ) :
    (∀ q ∈ Set.Icc (0 : ℝ) 1, pstar * q ≤ pstar * 1) ∧
      (∀ q ∈ Set.Icc (0 : ℝ) 1, pstar * 1 ≤ pstar * q → q = 1) ∧
      (∑ _j : Fin J, (1 : ℝ)) / r = J / r := by
  refine ⟨fun q hq => mul_le_mul_of_nonneg_left hq.2 hp.le, fun q hq h => ?_, by simp⟩
  have := le_of_mul_le_mul_left h hp
  linarith [hq.2]

/-- **Example 18.C.1** and **footnote 12** (MWG, pp. 662-663). Cournot equilibria bounded away
from the Walrasian outcome. Let the price selection satisfy `p(s) ≥ 1/λ` on `[0, b']`,
`p(s) ≤ 1/γ` for `s > b'`, and be "very elastic" on `[0, b']`: `p` is nonincreasing and the
revenue `s p(s)` nondecreasing there (Figure 18.C.3). If `r > Jλ/(γ b')` and `r b'/J < 1`,
then every firm producing `r b'/J` is a trading (Cournot) equilibrium: the profit
`p(b') r b'/J ≥ r b'/(Jλ)` exceeds `1/γ`, an upper bound for the profit of a firm that produces
more (the price drops to at most `1/γ` and `q ≤ 1`), and contracting does not pay because
revenue is nondecreasing and the price nonincreasing on `[0, b']`. -/
theorem example_18_C_1 {J r : ℕ} (hJ : 0 < J) {sel : ℝ → ℝ} {lam gam b : ℝ}
    (hlam : 0 < lam) (hgam : 0 < gam) (hb : 0 < b)
    (hhigh : ∀ s ∈ Set.Icc 0 b, 1 / lam ≤ sel s) (hlow : ∀ s, b < s → sel s ≤ 1 / gam)
    (hanti : AntitoneOn sel (Set.Icc 0 b))
    (hel : MonotoneOn (fun s => s * sel s) (Set.Icc 0 b))
    (hr : J * lam / (gam * b) < r) (hcap : r * b / J < 1) :
    (cournotModel J r sel).IsTradingEqm (fun _ => r * b / J) := by
  have hJ' : (0 : ℝ) < J := by exact_mod_cast hJ
  have hJ1 : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have hr0 : (0 : ℝ) < r := lt_of_le_of_lt (by positivity) hr
  set c := r * b / J with hc
  have hc0 : 0 ≤ c := by positivity
  have hJc : J * c = r * b := by rw [hc]; field_simp
  refine ⟨fun _ => ⟨hc0, hcap.le⟩, fun j q hq => ?_⟩
  have hdev := cournotModel_payoff J r sel (Function.update (fun _ => c) j q) j
  have heq := cournotModel_payoff J r sel (fun _ => c) j
  simp only [TradingModel.payoff] at hdev heq
  rw [Function.update_self] at hdev
  beta_reduce
  rw [hdev, heq, cournot_sum_update]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hJc]
  have hbr : r * b / r = b := by field_simp
  rw [hbr]
  set s := (q - c + r * b) / r with hs
  have hsr : r * s = q - c + r * b := by rw [hs]; field_simp
  -- the equilibrium profit exceeds `1/γ`
  have hpb : 1 / lam ≤ sel b := hhigh b ⟨hb.le, le_rfl⟩
  have hprofit : 1 / gam < sel b * c := by
    have h1 : 1 / gam < c / lam := by
      rw [hc, div_lt_div_iff₀ hgam hlam, div_mul_eq_mul_div, lt_div_iff₀ hJ']
      rw [div_lt_iff₀ (by positivity)] at hr
      linarith
    have h2 : c / lam ≤ sel b * c := by
      rw [div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_right hpb hc0
    linarith
  rcases lt_or_ge c q with hqc | hqc
  · -- expanding production: the price drops to at most `1/γ`
    have hsb : b < s := by
      rw [hs, lt_div_iff₀ hr0]
      linarith
    have hps := hlow s hsb
    have : sel s * q ≤ 1 / gam := by
      have h1 : sel s * q ≤ 1 / gam * q := mul_le_mul_of_nonneg_right hps hq.1
      have h2 : 1 / gam * q ≤ 1 / gam := by
        have := hq.2
        have : 0 < 1 / gam := by positivity
        nlinarith
      linarith
    linarith
  · -- contracting production: revenue is nondecreasing and the price nonincreasing
    have hs0 : 0 ≤ s := by
      rw [hs]
      apply div_nonneg _ hr0.le
      have : c ≤ r * b := by
        rw [← hJc]
        nlinarith
      linarith [hq.1]
    have hsb : s ≤ b := by
      rw [hs, div_le_iff₀ hr0]
      linarith
    have hmem : s ∈ Set.Icc 0 b := ⟨hs0, hsb⟩
    have hbmem : b ∈ Set.Icc 0 b := ⟨hb.le, le_rfl⟩
    have hrev : s * sel s ≤ b * sel b := hel hmem hbmem hsb
    have hprice : sel b ≤ sel s := hanti hmem hbmem hsb
    have hK : 0 ≤ r * b - c := by
      have : c ≤ r * b := by
        rw [← hJc]
        nlinarith
      linarith
    have hq' : q = r * s - (r * b - c) := by linarith
    rw [hq']
    have : r * (s * sel s) ≤ r * (b * sel b) := mul_le_mul_of_nonneg_left hrev hr0.le
    have : (r * b - c) * sel b ≤ (r * b - c) * sel s := mul_le_mul_of_nonneg_left hprice hK
    nlinarith

/-- **Example 18.C.1** (MWG, p. 663). The Cournot equilibrium of `example_18_C_1` is not
Walrasian: production per consumer is `b' < J/r` (so not every firm produces at capacity), and
at the prevailing price `p(b') > 0` a price-taking firm would rather produce the capacity
output `1` than `r b'/J`. -/
theorem example_18_C_1_not_walrasian {J r : ℕ} (hJ : 0 < J) {sel : ℝ → ℝ} {lam b : ℝ}
    (hlam : 0 < lam) (hb : 0 < b) (hhigh : ∀ s ∈ Set.Icc 0 b, 1 / lam ≤ sel s)
    (hr : 0 < r) (hcap : r * b / J < 1) :
    b < J / r ∧ sel b * (r * b / J) < sel b * 1 := by
  have hJ' : (0 : ℝ) < J := by exact_mod_cast hJ
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hpos : 0 < sel b := lt_of_lt_of_le (by positivity) (hhigh b ⟨hb.le, le_rfl⟩)
  refine ⟨?_, mul_lt_mul_of_pos_left hcap hpos⟩
  rw [div_lt_one hJ'] at hcap
  rw [lt_div_iff₀ hr']
  linarith

/-- A concrete price selection for Example 18.C.1 (a step version of Figure 18.C.3):
`p(s) = 1` for `s ≤ 1/2` and `p(s) = 1/2` for `s > 1/2`. -/
noncomputable def cournotStepSel (s : ℝ) : ℝ := if s ≤ 1 / 2 then 1 else 1 / 2

/-- **Example 18.C.1** (MWG, pp. 662-663), a concrete instance: with `J = 2` firms, `r = 3`
consumers and the selection `cournotStepSel` (`λ = 1`, `γ = 2`, `b' = 1/2`), every firm
producing `3/4 < 1` is a Cournot equilibrium; production per consumer `1/2` is below the
Walrasian `J/r = 2/3`. -/
theorem example_18_C_1_instance :
    (cournotModel 2 3 cournotStepSel).IsTradingEqm (fun _ => 3 / 4) ∧ (1 / 2 : ℝ) < 2 / 3 := by
  have h := example_18_C_1 (J := 2) (r := 3) (sel := cournotStepSel) (lam := 1) (gam := 2)
    (b := 1 / 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun s hs => by
      have : s ≤ 1 / 2 := hs.2
      simp only [cournotStepSel, this, ↓reduceIte]
      norm_num)
    (fun s hs => by
      have : ¬ s ≤ 1 / 2 := not_le.mpr hs
      simp only [cournotStepSel, this, ↓reduceIte]
      norm_num)
    (fun x hx y hy _ => by
      have h1 : x ≤ 1 / 2 := hx.2
      have h2 : y ≤ 1 / 2 := hy.2
      simp only [cournotStepSel, h1, h2, ↓reduceIte, le_refl])
    (fun x hx y hy hxy => by
      have h1 : x ≤ 1 / 2 := hx.2
      have h2 : y ≤ 1 / 2 := hy.2
      simp only [cournotStepSel, h1, h2, ↓reduceIte, mul_one]
      exact hxy)
    (by norm_num) (by norm_num)
  refine ⟨?_, by norm_num⟩
  have he : (fun _ : Fin 2 => ((3 : ℕ) : ℝ) * (1 / 2) / ((2 : ℕ) : ℝ)) = fun _ => 3 / 4 := by
    funext _
    norm_num
  rwa [he] at h

/-! ### Example 18.C.2: Cournot competition among complements (p. 663) -/

/-- The partial derivative `∂ψ/∂x₁ (x₁, x₂)`. -/
noncomputable def partialOne (ψ : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ := deriv (fun s => ψ s y) x

/-- The partial derivative `∂ψ/∂x₂ (x₁, x₂)`. -/
noncomputable def partialTwo (ψ : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ := deriv (fun s => ψ x s) y

/-- **Example 18.C.2** (MWG, p. 663). The market clearing prices at total productions
`(q₁, q₂)` with `r` consumers of quasilinear utility `ψ(x₁, x₂) + money`:
`p(q₁, q₂) = ∇ψ(q₁/r, q₂/r)`, with money (the third good) as numeraire. -/
noncomputable def complementsPrice (ψ : ℝ → ℝ → ℝ) (r : ℕ) (q₁ q₂ : ℝ) : Fin 3 → ℝ :=
  ![partialOne ψ (q₁ / r) (q₂ / r), partialTwo ψ (q₁ / r) (q₂ / r), 1]

/-- **Example 18.C.2** (MWG, p. 663) as a trading model: `J₁` firms producing good 1 and `J₂`
firms producing good 2, each with capacity one and zero cost (as in Example 18.C.1). An action
is a pair `(q₁, q₂)`: a firm of the first kind chooses `(q, 0)`, `q ∈ [0, 1]`, one of the second
kind `(0, q)`; the trading rule is `g((q₁, q₂); p) = (-q₁, -q₂, p₁q₁ + p₂q₂)` and owners care
only about money. -/
noncomputable def complementsModel (J₁ J₂ r : ℕ) (ψ : ℝ → ℝ → ℝ) :
    TradingModel (Fin J₁ ⊕ Fin J₂) (ℝ × ℝ) 3 where
  P := {p | p 2 = 1}
  A := Sum.elim (fun _ => Set.Icc 0 1 ×ˢ {0}) (fun _ => {0} ×ˢ Set.Icc 0 1)
  ω := Sum.elim (fun _ => ![1, 0, 0]) (fun _ => ![0, 1, 0])
  g := fun q p => ![-q.1, -q.2, p 0 * q.1 + p 1 * q.2]
  price := fun a => complementsPrice ψ r (∑ k, (a k).1) (∑ k, (a k).2)
  u := fun _ x => x 2

/-- The complements model satisfies the requirements of the abstract model. -/
theorem complementsModel_isValid (J₁ J₂ r : ℕ) (ψ : ℝ → ℝ → ℝ) :
    (complementsModel J₁ J₂ r ψ).IsValid := by
  refine ⟨fun q p hp => ?_, fun a _ => rfl⟩
  change p 2 = 1 at hp
  simp [complementsModel, dotProduct, Fin.sum_univ_three, hp]
  ring

/-- **Example 18.C.2** (MWG, p. 663). If `ψ(·, 0) ≡ 0`, then `∂ψ/∂x₁ (s, 0) = 0` for every `s`:
when nothing of good 2 is produced, any supply of good 1 is absorbed only at price `0`. (In
particular the book's `p(q₁, q₂) ≫ 0` fails on the axes.) -/
theorem partialOne_axis_eq_zero {ψ : ℝ → ℝ → ℝ} (h : ∀ x, ψ x 0 = 0) (s : ℝ) :
    partialOne ψ s 0 = 0 := by
  have : (fun t => ψ t 0) = fun _ => 0 := funext h
  simp [partialOne, this]

/-- The symmetric statement for good 2. -/
theorem partialTwo_axis_eq_zero {ψ : ℝ → ℝ → ℝ} (h : ∀ y, ψ 0 y = 0) (s : ℝ) :
    partialTwo ψ 0 s = 0 := by
  have : (fun t => ψ 0 t) = fun _ => 0 := funext h
  simp [partialTwo, this]

/-- Changing one coordinate of the zero profile: the sum of the first components is that of the
new action. -/
theorem complements_sum_update_zero {κ : Type*} [Fintype κ] [DecidableEq κ] (i : κ) (b : ℝ × ℝ) :
    (∑ k, (Function.update (fun _ : κ => ((0 : ℝ), (0 : ℝ))) i b k).1 = b.1) ∧
      ∑ k, (Function.update (fun _ : κ => ((0 : ℝ), (0 : ℝ))) i b k).2 = b.2 := by
  constructor
  · rw [Finset.sum_eq_single i (fun k _ hk => by simp [Function.update_of_ne hk])
      (fun h => absurd (Finset.mem_univ i) h)]
    simp
  · rw [Finset.sum_eq_single i (fun k _ hk => by simp [Function.update_of_ne hk])
      (fun h => absurd (Finset.mem_univ i) h)]
    simp

/-- **Example 18.C.2** (MWG, p. 663). If the two goods are complements in the extreme sense
`ψ(0, x₂) = ψ(x₁, 0) = 0`, the null production is a trading equilibrium: a firm that produces
`q > 0` of good 1 while nothing of good 2 is produced faces the price `∂ψ/∂x₁(q/r, 0) = 0`
and earns nothing (and symmetrically for good 2). No concavity or monotonicity of `ψ` is
needed for this claim. -/
theorem example_18_C_2 (J₁ J₂ r : ℕ) {ψ : ℝ → ℝ → ℝ} (h₁ : ∀ x, ψ x 0 = 0)
    (h₂ : ∀ y, ψ 0 y = 0) :
    (complementsModel J₁ J₂ r ψ).IsTradingEqm (fun _ => (0, 0)) := by
  classical
  refine ⟨fun i => ?_, fun i b hb => ?_⟩
  · cases i with
    | inl i => exact ⟨⟨le_rfl, zero_le_one⟩, rfl⟩
    | inr i => exact ⟨rfl, ⟨le_rfl, zero_le_one⟩⟩
  obtain ⟨hs1, hs2⟩ := complements_sum_update_zero i b
  cases i with
  | inl i =>
    obtain ⟨q, z⟩ := b
    obtain ⟨-, hz⟩ := hb
    change z = 0 at hz
    subst hz
    simp only [complementsModel, complementsPrice] at hs1 hs2 ⊢
    rw [hs1, hs2]
    simp [partialOne_axis_eq_zero h₁]
  | inr i =>
    obtain ⟨q, z⟩ := b
    obtain ⟨hq, -⟩ := hb
    change q = 0 at hq
    subst hq
    simp only [complementsModel, complementsPrice] at hs1 hs2 ⊢
    rw [hs1, hs2]
    simp [partialTwo_axis_eq_zero h₂]

/-- **Footnote 13** (MWG, p. 663). The homothetic, nonlinear complementary utility
`ψ(x₁, x₂) = √(x₁ x₂)`. -/
noncomputable def fn13GeomMean (x y : ℝ) : ℝ := Real.sqrt (x * y)

/-- `√(x₁x₂)` vanishes on the axes, is homogeneous of degree one (hence homothetic) and is not
linear. -/
theorem footnote_18_13_psi :
    (∀ x, fn13GeomMean x 0 = 0) ∧ (∀ y, fn13GeomMean 0 y = 0) ∧
      (∀ c x y : ℝ, 0 ≤ c → fn13GeomMean (c * x) (c * y) = c * fn13GeomMean x y) ∧
      fn13GeomMean 1 0 + fn13GeomMean 0 1 ≠ fn13GeomMean 1 1 := by
  refine ⟨fun x => by simp [fn13GeomMean], fun y => by simp [fn13GeomMean],
    fun c x y hc => ?_, ?_⟩
  · unfold fn13GeomMean
    rw [show c * x * (c * y) = (c * c) * (x * y) by ring, Real.sqrt_mul (mul_self_nonneg c),
      Real.sqrt_mul_self hc]
  · simp [fn13GeomMean]

/-- `√(x₁x₂)` is concave on `ℝ²₊`: `a√(x₁x₂) + b√(y₁y₂) ≤ √((ax₁ + by₁)(ax₂ + by₂))` for
`a, b ≥ 0` (in particular for `a + b = 1`). -/
theorem footnote_18_13_psi_concave {x₁ x₂ y₁ y₂ a b : ℝ} (hx₁ : 0 ≤ x₁) (hx₂ : 0 ≤ x₂)
    (hy₁ : 0 ≤ y₁) (hy₂ : 0 ≤ y₂) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a * fn13GeomMean x₁ x₂ + b * fn13GeomMean y₁ y₂ ≤
      fn13GeomMean (a * x₁ + b * y₁) (a * x₂ + b * y₂) := by
  unfold fn13GeomMean
  set s := Real.sqrt (x₁ * x₂)
  set t := Real.sqrt (y₁ * y₂)
  have hs : s ^ 2 = x₁ * x₂ := Real.sq_sqrt (mul_nonneg hx₁ hx₂)
  have ht : t ^ 2 = y₁ * y₂ := Real.sq_sqrt (mul_nonneg hy₁ hy₂)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  apply Real.le_sqrt_of_sq_le
  -- the cross term: `2st ≤ x₁y₂ + y₁x₂`
  have hst : (s * t) ^ 2 = (x₁ * y₂) * (y₁ * x₂) := by
    rw [mul_pow, hs, ht]
    ring
  have hcross : 2 * (s * t) ≤ x₁ * y₂ + y₁ * x₂ := by
    nlinarith [sq_nonneg (x₁ * y₂ - y₁ * x₂), mul_nonneg hs0 ht0, mul_nonneg hx₁ hy₂,
      mul_nonneg hy₁ hx₂]
  have hab2 : 0 ≤ a * b := mul_nonneg ha hb
  have e1 : (a * s + b * t) ^ 2 =
      a ^ 2 * (x₁ * x₂) + 2 * (a * b) * (s * t) + b ^ 2 * (y₁ * y₂) := by
    rw [← hs, ← ht]
    ring
  have e2 : (a * x₁ + b * y₁) * (a * x₂ + b * y₂) =
      a ^ 2 * (x₁ * x₂) + (a * b) * (x₁ * y₂ + y₁ * x₂) + b ^ 2 * (y₁ * y₂) := by ring
  rw [e1, e2]
  nlinarith [mul_le_mul_of_nonneg_left hcross hab2]

/-- **Footnote 13** (MWG, p. 663). With `ψ = √(x₁x₂)`, the price of good 1 is `0` at every
`(ε, 0)`, while at `(ε, ε)`, `ε > 0`, both prices equal `1/2`: the clearing prices are bounded
away from `0` along the diagonal but vanish on the axis. -/
theorem footnote_18_13_prices (r : ℕ) (hr : 0 < r) {ε : ℝ} (hε : 0 < ε) :
    complementsPrice fn13GeomMean r ε 0 0 = 0 ∧ complementsPrice fn13GeomMean r ε ε 0 = 1 / 2 ∧
      complementsPrice fn13GeomMean r ε ε 1 = 1 / 2 := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  set e := ε / r with he
  have he0 : 0 < e := div_pos hε hr'
  have hsq : Real.sqrt (e * e) = e := Real.sqrt_mul_self he0.le
  have hd1 : HasDerivAt (fun s => fn13GeomMean s e) (1 / 2) e := by
    have := ((hasDerivAt_id e).mul_const e).sqrt (by simp [he0.ne'])
    simp only [id, one_mul, hsq] at this
    convert this using 1
    · rfl
    · field_simp
  have hd2 : HasDerivAt (fun s => fn13GeomMean e s) (1 / 2) e := by
    have := ((hasDerivAt_id e).const_mul e).sqrt (by simp [he0.ne'])
    simp only [id, mul_one, hsq] at this
    convert this using 1
    · rfl
    · field_simp
  refine ⟨?_, ?_, ?_⟩
  · simp only [complementsPrice, zero_div, Matrix.cons_val_zero]
    exact partialOne_axis_eq_zero footnote_18_13_psi.1 _
  · simp only [complementsPrice, Matrix.cons_val_zero, partialOne]
    exact hd1.deriv
  · simp only [complementsPrice, Matrix.cons_val_one, Matrix.cons_val_zero, partialTwo]
    exact hd2.deriv

/-- **Footnote 13** (MWG, p. 663). With `ψ = √(x₁x₂)` the clearing price of good 1 is
discontinuous at the origin: it is `0` at `(0, 0)` but `1/2` at every `(ε, ε)`, `ε > 0`. -/
theorem footnote_18_13_discontinuous (r : ℕ) (hr : 0 < r) :
    ¬ ContinuousAt (fun q : ℝ × ℝ => complementsPrice fn13GeomMean r q.1 q.2 0) (0, 0) := by
  intro hc
  have h0 : complementsPrice fn13GeomMean r 0 0 0 = 0 := by
    simp only [complementsPrice, zero_div, Matrix.cons_val_zero]
    exact partialOne_axis_eq_zero footnote_18_13_psi.1 _
  have hdiag : Filter.Tendsto (fun t : ℝ => ((t, t) : ℝ × ℝ)) (nhds 0) (nhds (0, 0)) :=
    (continuous_id.prodMk continuous_id).tendsto' 0 (0, 0) rfl
  have hlim := (hc.tendsto.comp hdiag).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  rw [h0] at hlim
  have hev : (fun t : ℝ => complementsPrice fn13GeomMean r t t 0) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      fun _ => 1 / 2 :=
    eventually_nhdsWithin_of_forall fun t ht => (footnote_18_13_prices r hr ht).2.1
  have h2 : Filter.Tendsto (fun t : ℝ => complementsPrice fn13GeomMean r t t 0)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 / 2)) :=
    tendsto_const_nhds.congr' hev.symm
  have := tendsto_nhds_unique hlim h2
  norm_num at this

/-- **Footnote 13** (MWG, p. 663). `ψ = √(x₁x₂)` is not differentiable at the origin (along the
diagonal it is `|t|`), as the footnote says complementarity forces. -/
theorem footnote_18_13_not_differentiable :
    ¬ DifferentiableAt ℝ (fun v : ℝ × ℝ => fn13GeomMean v.1 v.2) (0, 0) := by
  intro hd
  have hdiag : DifferentiableAt ℝ (fun t : ℝ => ((t, t) : ℝ × ℝ)) 0 :=
    differentiableAt_id.prodMk differentiableAt_id
  have := hd.comp (f := fun t : ℝ => ((t, t) : ℝ × ℝ)) (0 : ℝ) hdiag
  have habs : ((fun v : ℝ × ℝ => fn13GeomMean v.1 v.2) ∘ fun t : ℝ => ((t, t) : ℝ × ℝ)) =
      (abs : ℝ → ℝ) := by
    funext t
    simp [fn13GeomMean, Real.sqrt_mul_self_eq_abs]
  rw [habs] at this
  exact not_differentiableAt_abs_zero this

/-! ### Example 18.C.3: trading posts (pp. 663-665) -/

/-- **Example 18.C.3**, (18.C.1) (MWG, p. 664). The price at one trading post, given the bids
`cₖ = (a'ₖ, a''ₖ)` (good offered, money offered) of all consumers: `p = ∑ₖ a''ₖ / ∑ₖ a'ₖ`.
(Lean's convention `x / 0 = 0` gives `p = 0` at a post with no goods offered.) -/
noncomputable def tpPrice {κ : Type*} [Fintype κ] (c : κ → ℝ × ℝ) : ℝ :=
  (∑ k, (c k).2) / (∑ k, (c k).1)

/-- **Example 18.C.3** (MWG, p. 664). Consumer `i`'s net trade in the good at a trading post:
she receives the share `a''ᵢ / ∑ₖ a''ₖ` of the goods offered and gives up her offer `a'ᵢ`,
`a''ᵢ ∑ₖ a'ₖ / ∑ₖ a''ₖ - a'ᵢ`. This is the book's `a''ᵢ / p - a'ᵢ` whenever both sides of the
post are active (`example_18_C_3_rule`); the share form fixes the convention at inactive posts:
a side of the market facing no offers on the other side receives nothing. -/
noncomputable def tpGood {κ : Type*} [Fintype κ] (c : κ → ℝ × ℝ) (i : κ) : ℝ :=
  (c i).2 * (∑ k, (c k).1) / (∑ k, (c k).2) - (c i).1

/-- **Example 18.C.3** (MWG, p. 664). Consumer `i`'s net receipt of money at a trading post:
the share `a'ᵢ / ∑ₖ a'ₖ` of the money offered minus her money bid `a''ᵢ` (the book's
`p a'ᵢ - a''ᵢ`, obtained from her budget constraint). -/
noncomputable def tpMoney {κ : Type*} [Fintype κ] (c : κ → ℝ × ℝ) (i : κ) : ℝ :=
  (c i).1 * (∑ k, (c k).2) / (∑ k, (c k).1) - (c i).2

/-- **Example 18.C.3** (MWG, p. 664). When both sides of the post are active the trading rule
is the book's `gₗ = a''ᵢ/pₗ - a'ᵢ` with money receipt `pₗ a'ᵢ - a''ᵢ`, so the net trade is
orthogonal to the prices (`p·g = 0`), and the post clears: net trades in the good and in money
sum to zero. -/
theorem example_18_C_3_rule {κ : Type*} [Fintype κ] (c : κ → ℝ × ℝ)
    (h₁ : 0 < ∑ k, (c k).1) (h₂ : 0 < ∑ k, (c k).2) (i : κ) :
    tpGood c i = (c i).2 / tpPrice c - (c i).1 ∧ tpMoney c i = tpPrice c * (c i).1 - (c i).2 ∧
      tpPrice c * tpGood c i + tpMoney c i = 0 ∧ ∑ k, tpGood c k = 0 ∧ ∑ k, tpMoney c k = 0 := by
  have h₁' := h₁.ne'
  have h₂' := h₂.ne'
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [tpGood, tpPrice]
    field_simp
  · simp only [tpMoney, tpPrice]
    field_simp
  · simp only [tpGood, tpMoney, tpPrice]
    field_simp
    ring
  · simp only [tpGood]
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_mul]
    field_simp
    ring
  · simp only [tpMoney]
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_mul]
    field_simp
    ring

/-- The aggregate offer on one side of a post is continuous in the bids. -/
theorem tp_continuous_sum_fst {κ : Type*} [Fintype κ] :
    Continuous fun c : κ → ℝ × ℝ => ∑ k, (c k).1 :=
  continuous_finsetSum _ fun k _ => (continuous_apply k).fst

/-- The aggregate money bid at a post is continuous in the bids. -/
theorem tp_continuous_sum_snd {κ : Type*} [Fintype κ] :
    Continuous fun c : κ → ℝ × ℝ => ∑ k, (c k).2 :=
  continuous_finsetSum _ fun k _ => (continuous_apply k).snd

/-- **Example 18.C.3** (MWG, p. 664). The price (18.C.1) is well defined and continuous at every
bid profile with goods offered at the post (`∑ᵢ a'ᵢ ≠ 0`). -/
theorem example_18_C_3_continuous {κ : Type*} [Fintype κ] :
    ContinuousOn (tpPrice (κ := κ)) {c | ∑ k, (c k).1 ≠ 0} :=
  tp_continuous_sum_snd.continuousOn.div tp_continuous_sum_fst.continuousOn fun _ hc => hc

/-- The bid profile in which only consumer `i` bids `(t, m t)` at the post. -/
def tpLoneBid {κ : Type*} [DecidableEq κ] (i : κ) (m t : ℝ) : κ → ℝ × ℝ :=
  fun k => if k = i then (t, m * t) else 0

/-- The lone bid is continuous in `t`. -/
theorem tp_continuous_loneBid {κ : Type*} [DecidableEq κ] (i : κ) (m : ℝ) :
    Continuous (tpLoneBid i m) := by
  refine continuous_pi fun k => ?_
  by_cases hk : k = i
  · simp only [tpLoneBid, hk, ↓reduceIte]
    exact continuous_id.prodMk (continuous_const.mul continuous_id)
  · simp only [tpLoneBid, hk, ↓reduceIte]
    exact continuous_const

/-- With a lone bid `(t, m t)`, `t > 0`, the price is `m`. -/
theorem tpPrice_loneBid {κ : Type*} [Fintype κ] [DecidableEq κ] (i : κ) (m : ℝ) {t : ℝ}
    (ht : 0 < t) : tpPrice (tpLoneBid i m t) = m ∧ 0 < ∑ k, (tpLoneBid i m t k).1 := by
  have h1 : ∑ k, (tpLoneBid i m t k).1 = t := by
    rw [Finset.sum_eq_single i (fun k _ hk => by simp [tpLoneBid, hk])
      (fun h => absurd (Finset.mem_univ i) h)]
    simp [tpLoneBid]
  have h2 : ∑ k, (tpLoneBid i m t k).2 = m * t := by
    rw [Finset.sum_eq_single i (fun k _ hk => by simp [tpLoneBid, hk])
      (fun h => absurd (Finset.mem_univ i) h)]
    simp [tpLoneBid]
  refine ⟨?_, by rw [h1]; exact ht⟩
  rw [tpPrice, h1, h2]
  field_simp

/-- **Example 18.C.3** (MWG, p. 665). "The impossibility of assigning prices continuously when
`aₗᵢ = 0` for all `i`": no function that agrees with the price (18.C.1) wherever both sides
of the post are active is continuous at the inactive profile `0` (lone bids `(t, t)` give
price `1`, lone bids `(t, 2t)` price `2`, and both tend to `0`). -/
theorem example_18_C_3_no_continuous_price {κ : Type*} [Fintype κ] [Nonempty κ]
    (f : (κ → ℝ × ℝ) → ℝ)
    (hf : ∀ c, 0 < ∑ k, (c k).1 → 0 < ∑ k, (c k).2 → f c = tpPrice c) :
    ¬ ContinuousAt f 0 := by
  classical
  intro hc
  obtain ⟨i⟩ := ‹Nonempty κ›
  have hval : ∀ m : ℝ, 0 < m → f 0 = m := by
    intro m hm
    have h0 : tpLoneBid i m 0 = 0 := by
      funext k
      by_cases hk : k = i <;> simp [tpLoneBid, hk]
    have ht : Filter.Tendsto (tpLoneBid i m) (nhds 0) (nhds 0) := by
      have := (tp_continuous_loneBid i m).tendsto 0
      rwa [h0] at this
    have hcomp := (hc.tendsto.comp ht).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    have hev : (f ∘ tpLoneBid i m) =ᶠ[nhdsWithin 0 (Set.Ioi 0)] fun _ => m := by
      refine eventually_nhdsWithin_of_forall fun t (ht : 0 < t) => ?_
      obtain ⟨hp, h1⟩ := tpPrice_loneBid i m ht
      have h2 : 0 < ∑ k, (tpLoneBid i m t k).2 := by
        rw [Finset.sum_eq_single i (fun k _ hk => by simp [tpLoneBid, hk])
          (fun h => absurd (Finset.mem_univ i) h)]
        simp only [tpLoneBid, ↓reduceIte]
        positivity
      change f (tpLoneBid i m t) = m
      rw [hf _ h1 h2, hp]
    exact tendsto_nhds_unique hcomp (tendsto_const_nhds.congr' hev.symm)
  have := (hval 1 one_pos).symm.trans (hval 2 two_pos)
  norm_num at this

/-- **Footnote 14** (MWG, p. 664). With a single trading post (`L = 2`) the relative price of
money in terms of the good, `∑ᵢ a'ᵢ / ∑ᵢ a''ᵢ`, is well defined and continuous wherever money is
offered (`∑ᵢ a''ᵢ ≠ 0`), and it is `0` when money but no good is offered; the essential
difficulty is at `∑ᵢ a'ᵢ = ∑ᵢ a''ᵢ = 0`, where it cannot be extended continuously. -/
theorem footnote_18_14 {κ : Type*} [Fintype κ] [Nonempty κ] :
    ContinuousOn (fun c : κ → ℝ × ℝ => (∑ k, (c k).1) / (∑ k, (c k).2))
        {c | ∑ k, (c k).2 ≠ 0} ∧
      (∀ c : κ → ℝ × ℝ, ∑ k, (c k).1 = 0 → (∑ k, (c k).1) / (∑ k, (c k).2) = 0) ∧
      ∀ f : (κ → ℝ × ℝ) → ℝ,
        (∀ c, 0 < ∑ k, (c k).1 → 0 < ∑ k, (c k).2 →
          f c = (∑ k, (c k).1) / (∑ k, (c k).2)) → ¬ ContinuousAt f 0 := by
  refine ⟨tp_continuous_sum_fst.continuousOn.div tp_continuous_sum_snd.continuousOn fun _ hc => hc,
    fun c hc => by rw [hc, zero_div], fun f hf hcont => ?_⟩
  -- swap the two sides of the post
  set sw : (κ → ℝ × ℝ) → κ → ℝ × ℝ := fun c k => (c k).swap with hsw
  have hswc : Continuous sw := continuous_pi fun k => continuous_swap.comp (continuous_apply k)
  have hsw0 : sw 0 = 0 := by
    funext k
    simp [hsw]
  refine example_18_C_3_no_continuous_price (f ∘ sw) (fun c h1 h2 => ?_) ?_
  · simp only [Function.comp, hsw]
    rw [hf _ h2 h1]
    rfl
  · have : ContinuousAt f (sw 0) := by rwa [hsw0]
    exact this.comp hswc.continuousAt

/-- An economy with trading posts (Example 18.C.3, MWG, p. 664): `n = L - 1` goods traded for
money at `n` posts; consumer `i` has endowments `ωₗᵢ` of the goods and `ω_Lᵢ` of money, and a
utility over the bundle of goods and money. -/
structure TradingPostEconomy (κ : Type*) (n : ℕ) where
  /-- Endowments of the goods `ωₗᵢ`, `l ≤ L - 1`. -/
  ωg : κ → Fin n → ℝ
  /-- Endowments of money `ω_Lᵢ`. -/
  ωm : κ → ℝ
  /-- Utilities over goods and money. -/
  u : κ → (Fin n → ℝ) → ℝ → ℝ

variable {κ : Type*} {n : ℕ}

/-- **Example 18.C.3** (MWG, p. 664). The feasible bids of consumer `i`: at every post
`aₗᵢ = (a'ₗᵢ, a''ₗᵢ) ∈ ℝ²₊` with `a'ₗᵢ ≤ ωₗᵢ`, and `∑ₗ a''ₗᵢ ≤ ω_Lᵢ`. -/
def TradingPostEconomy.FeasibleBid (E : TradingPostEconomy κ n) (i : κ)
    (b : Fin n → ℝ × ℝ) : Prop :=
  (∀ l, 0 ≤ (b l).1 ∧ (b l).1 ≤ E.ωg i l ∧ 0 ≤ (b l).2) ∧ ∑ l, (b l).2 ≤ E.ωm i

/-- The goods consumer `i` ends up with: `ωₗᵢ` plus her net trade at post `l`. -/
noncomputable def TradingPostEconomy.goodsOut [Fintype κ] (E : TradingPostEconomy κ n)
    (a : κ → Fin n → ℝ × ℝ) (i : κ) : Fin n → ℝ :=
  fun l => E.ωg i l + tpGood (fun k => a k l) i

/-- The money consumer `i` ends up with: `ω_Lᵢ` plus her net money receipts at all posts. -/
noncomputable def TradingPostEconomy.moneyOut [Fintype κ] (E : TradingPostEconomy κ n)
    (a : κ → Fin n → ℝ × ℝ) (i : κ) : ℝ :=
  E.ωm i + ∑ l, tpMoney (fun k => a k l) i

/-- **Definition 18.C.1** for the trading-post game in which only the posts in `O` exist (bids
at the other posts are zero): every consumer bids feasibly and no feasible unilateral change of
bids raises her utility. -/
def TradingPostEconomy.IsEqm [Fintype κ] [DecidableEq κ] (E : TradingPostEconomy κ n)
    (O : Set (Fin n)) (a : κ → Fin n → ℝ × ℝ) : Prop :=
  (∀ i, E.FeasibleBid i (a i) ∧ ∀ l ∉ O, a i l = 0) ∧
    ∀ i b, E.FeasibleBid i b → (∀ l ∉ O, b l = 0) →
      E.u i (E.goodsOut (Function.update a i b) i) (E.moneyOut (Function.update a i b) i) ≤
        E.u i (E.goodsOut a i) (E.moneyOut a i)

/-- A lone bidder at a post gets nothing back: if all other bids at the post are `0` and
consumer `i`'s bid is nonnegative, her net trades in the good and in money are `≤ 0`. -/
theorem tp_lone_bidder [Fintype κ] {c : κ → ℝ × ℝ} {i : κ} (hc : ∀ k, k ≠ i → c k = 0)
    (h₁ : 0 ≤ (c i).1) (h₂ : 0 ≤ (c i).2) : tpGood c i ≤ 0 ∧ tpMoney c i ≤ 0 := by
  have s1 : ∑ k, (c k).1 = (c i).1 := Finset.sum_eq_single i
    (fun k _ hk => by simp [hc k hk]) (fun h => absurd (Finset.mem_univ i) h)
  have s2 : ∑ k, (c k).2 = (c i).2 := Finset.sum_eq_single i
    (fun k _ hk => by simp [hc k hk]) (fun h => absurd (Finset.mem_univ i) h)
  simp only [tpGood, tpMoney, s1, s2]
  constructor
  · rcases h₂.eq_or_lt with h | h
    · rw [← h]
      simp [h₁]
    · rw [mul_div_cancel_left₀ _ h.ne', sub_self]
  · rcases h₁.eq_or_lt with h | h
    · rw [← h]
      simp [h₂]
    · rw [mul_div_cancel_left₀ _ h.ne', sub_self]

/-- At a post where nobody bids, every net trade is zero. -/
theorem tp_all_zero [Fintype κ] {c : κ → ℝ × ℝ} (hc : ∀ k, c k = 0) (i : κ) :
    tpGood c i = 0 ∧ tpMoney c i = 0 := by
  simp [tpGood, tpMoney, hc]

/-- **Example 18.C.3** (MWG, p. 665). An inactive trading post does not destroy an equilibrium:
any trading equilibrium of the model in which post `l` is closed remains an equilibrium when the
post is open but inactive (`aₗᵢ = (0, 0)` for all `i`), provided utilities are nondecreasing in
goods and money. A consumer who bids alone at post `l` receives nothing in return
(`tp_lone_bidder`), so dropping her bid there is a feasible deviation in the closed model that is
at least as good. -/
theorem example_18_C_3_inactive_post [Fintype κ] [DecidableEq κ] (E : TradingPostEconomy κ n)
    (hmono : ∀ i (x x' : Fin n → ℝ) (m m' : ℝ), x ≤ x' → m ≤ m' → E.u i x m ≤ E.u i x' m')
    {O : Set (Fin n)} {a : κ → Fin n → ℝ × ℝ} (h : E.IsEqm O a) {l : Fin n} (hl : l ∉ O) :
    E.IsEqm (insert l O) a := by
  refine ⟨fun i => ⟨(h.1 i).1, fun l' hl' => (h.1 i).2 l' fun h' => hl'
    (Set.mem_insert_of_mem _ h')⟩, fun i b hb hbO => ?_⟩
  set b' := Function.update b l 0 with hb'
  have hfeas : E.FeasibleBid i b' := by
    refine ⟨fun l' => ?_, ?_⟩
    · by_cases hl' : l' = l
      · subst hl'
        have := (h.1 i).1.1 l'
        rw [hb', Function.update_self]
        exact ⟨le_rfl, this.1.trans this.2.1, le_rfl⟩
      · simp only [hb', Function.update_of_ne hl']
        exact hb.1 l'
    · refine le_trans (Finset.sum_le_sum fun l' _ => ?_) hb.2
      by_cases hl' : l' = l
      · subst hl'
        simp [hb', (hb.1 l').2.2]
      · simp [hb', Function.update_of_ne hl']
  have hO : ∀ l' ∉ O, b' l' = 0 := by
    intro l' hl'
    by_cases hll : l' = l
    · subst hll
      simp [hb']
    · simp only [hb', Function.update_of_ne hll]
      exact hbO l' fun h' => (Set.mem_insert_iff.mp h').elim hll hl'
  refine le_trans (hmono i _ _ _ _ ?_ ?_) (h.2 i b' hfeas hO)
  · -- post by post, the goods obtained are no larger with the bid at post `l`
    intro l'
    simp only [TradingPostEconomy.goodsOut]
    by_cases hll : l' = l
    · subst hll
      have hother : ∀ k, k ≠ i → Function.update a i b k l' = 0 := fun k hk => by
        rw [Function.update_of_ne hk]
        exact (h.1 k).2 l' hl
      have h1 := (tp_lone_bidder (c := fun k => Function.update a i b k l') hother
        (by simpa using (hb.1 l').1) (by simpa using (hb.1 l').2.2)).1
      have h2 := (tp_all_zero (c := fun k => Function.update a i b' k l') (fun k => by
        by_cases hk : k = i
        · subst hk
          simp [hb']
        · rw [Function.update_of_ne hk]
          exact (h.1 k).2 l' hl) i).1
      linarith
    · have : (fun k => Function.update a i b k l') = fun k => Function.update a i b' k l' := by
        funext k
        by_cases hk : k = i
        · subst hk
          simp [hb', Function.update_of_ne hll]
        · simp [Function.update_of_ne hk]
      rw [this]
  · simp only [TradingPostEconomy.moneyOut, add_le_add_iff_left]
    refine Finset.sum_le_sum fun l' _ => ?_
    by_cases hll : l' = l
    · subst hll
      have hother : ∀ k, k ≠ i → Function.update a i b k l' = 0 := fun k hk => by
        rw [Function.update_of_ne hk]
        exact (h.1 k).2 l' hl
      have h1 := (tp_lone_bidder (c := fun k => Function.update a i b k l') hother
        (by simpa using (hb.1 l').1) (by simpa using (hb.1 l').2.2)).2
      have h2 := (tp_all_zero (c := fun k => Function.update a i b' k l') (fun k => by
        by_cases hk : k = i
        · subst hk
          simp [hb']
        · rw [Function.update_of_ne hk]
          exact (h.1 k).2 l' hl) i).2
      linarith
    · have : (fun k => Function.update a i b k l') = fun k => Function.update a i b' k l' := by
        funext k
        by_cases hk : k = i
        · subst hk
          simp [hb', Function.update_of_ne hll]
        · simp [Function.update_of_ne hk]
      rw [this]

/-- **Example 18.C.3** (MWG, p. 665). A consumer without money (`ω_Lᵢ = 0`) cannot buy goods:
whatever the others bid, every feasible bid leaves her with no more of any good than her
endowment. -/
theorem example_18_C_3_no_money [Fintype κ] [DecidableEq κ] (E : TradingPostEconomy κ n)
    {i : κ} (h0 : E.ωm i = 0) {b : Fin n → ℝ × ℝ} (hb : E.FeasibleBid i b)
    (a : κ → Fin n → ℝ × ℝ) (l : Fin n) :
    E.goodsOut (Function.update a i b) i l ≤ E.ωg i l := by
  have hzero : ∀ l', (b l').2 = 0 := by
    have hsum := hb.2
    rw [h0] at hsum
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun l' _ => (hb.1 l').2.2)).mp
      (le_antisymm hsum (Finset.sum_nonneg fun l' _ => (hb.1 l').2.2))
    exact fun l' => this l' (Finset.mem_univ l')
  simp only [TradingPostEconomy.goodsOut, tpGood, Function.update_self, hzero l, zero_mul,
    zero_div, zero_sub, add_neg_le_iff_le_add, le_add_iff_nonneg_right]
  exact (hb.1 l).1

/-! ### Exercise 18.C.1: effective budget sets at a trading post (L = 2) -/

/-- **Exercise 18.C.1** (MWG, p. 685), `L = 2`. The effective budget set of consumer `i` at a
single trading post, given the bids `c` of the others: the bundles `x ∈ ℝ²₊` (good, money) with
`x ≤ ωᵢ + (gᵢ, mᵢ)` for some feasible bid `(s, b)` of `i` (`0 ≤ s ≤ ω₁ᵢ` of the good offered,
`0 ≤ b ≤ ω₂ᵢ` of money offered; two-sided bids allowed). -/
noncomputable def tpBudget [Fintype κ] [DecidableEq κ] (c : κ → ℝ × ℝ) (i : κ)
    (ω : Fin 2 → ℝ) : Set (Fin 2 → ℝ) :=
  {x | x ∈ nonnegOrthant 2 ∧ ∃ s b : ℝ, 0 ≤ s ∧ s ≤ ω 0 ∧ 0 ≤ b ∧ b ≤ ω 1 ∧
    x 0 ≤ ω 0 + tpGood (Function.update c i (s, b)) i ∧
    x 1 ≤ ω 1 + tpMoney (Function.update c i (s, b)) i}

/-- The others' aggregate offers at the post: `A' = ∑_{k ≠ i} a'ₖ`, `A'' = ∑_{k ≠ i} a''ₖ`,
and the aggregates after `i` bids `(s, b)`: `s + A'` and `b + A''`. -/
theorem tp_update_sums [Fintype κ] [DecidableEq κ] (c : κ → ℝ × ℝ) (i : κ) (s b : ℝ) :
    ∑ k, (Function.update c i (s, b) k).1 = s + ∑ k ∈ Finset.univ.erase i, (c k).1 ∧
      ∑ k, (Function.update c i (s, b) k).2 = b + ∑ k ∈ Finset.univ.erase i, (c k).2 := by
  constructor
  · rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), Function.update_self]
    congr 1
    exact Finset.sum_congr rfl fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  · rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), Function.update_self]
    congr 1
    exact Finset.sum_congr rfl fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]

/-- **Exercise 18.C.1** (MWG, p. 685). With the others' aggregates `A', A'' > 0`, the bid
`(s, b) ≥ 0` yields the net trades `g = (bA' - sA'')/(b + A'')` in the good and
`m = (sA'' - bA')/(s + A')` in money. -/
theorem tp_outcome [Fintype κ] [DecidableEq κ] (c : κ → ℝ × ℝ) (i : κ) {s b : ℝ}
    (hs : 0 ≤ s) (hb : 0 ≤ b) (hA₁ : 0 < ∑ k ∈ Finset.univ.erase i, (c k).1)
    (hA₂ : 0 < ∑ k ∈ Finset.univ.erase i, (c k).2) :
    tpGood (Function.update c i (s, b)) i =
        (b * ∑ k ∈ Finset.univ.erase i, (c k).1 - s * ∑ k ∈ Finset.univ.erase i, (c k).2) /
          (b + ∑ k ∈ Finset.univ.erase i, (c k).2) ∧
      tpMoney (Function.update c i (s, b)) i =
        (s * ∑ k ∈ Finset.univ.erase i, (c k).2 - b * ∑ k ∈ Finset.univ.erase i, (c k).1) /
          (s + ∑ k ∈ Finset.univ.erase i, (c k).1) := by
  obtain ⟨h1, h2⟩ := tp_update_sums c i s b
  set A₁ := ∑ k ∈ Finset.univ.erase i, (c k).1
  set A₂ := ∑ k ∈ Finset.univ.erase i, (c k).2
  have hb' : b + A₂ ≠ 0 := by positivity
  have hs' : s + A₁ ≠ 0 := by positivity
  simp only [tpGood, tpMoney, h1, h2, Function.update_self]
  constructor
  · field_simp
    ring
  · field_simp
    ring

/-- **Exercise 18.C.1** (MWG, p. 664, p. 685). The displayed outcomes of one-sided bids: selling
`s` gives `x = (ω₁ - s, ω₂ + sA''/(s + A'))` and buying with `b` gives
`x = (ω₁ + bA'/(b + A''), ω₂ - b)`. -/
theorem exercise_18_C_1_one_sided [Fintype κ] [DecidableEq κ] (c : κ → ℝ × ℝ) (i : κ)
    {s b : ℝ} (hs : 0 ≤ s) (hb : 0 ≤ b) (hA₁ : 0 < ∑ k ∈ Finset.univ.erase i, (c k).1)
    (hA₂ : 0 < ∑ k ∈ Finset.univ.erase i, (c k).2) :
    (tpGood (Function.update c i (s, 0)) i = -s ∧
      tpMoney (Function.update c i (s, 0)) i =
        s * (∑ k ∈ Finset.univ.erase i, (c k).2) / (s + ∑ k ∈ Finset.univ.erase i, (c k).1)) ∧
    (tpGood (Function.update c i (0, b)) i =
        b * (∑ k ∈ Finset.univ.erase i, (c k).1) / (b + ∑ k ∈ Finset.univ.erase i, (c k).2) ∧
      tpMoney (Function.update c i (0, b)) i = -b) := by
  obtain ⟨g1, m1⟩ := tp_outcome c i hs le_rfl hA₁ hA₂
  obtain ⟨g2, m2⟩ := tp_outcome c i le_rfl hb hA₁ hA₂
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [g1]
    field_simp
    ring
  · rw [m1]
    ring
  · rw [g2]
    ring
  · rw [m2]
    field_simp
    ring

/-- The frontier of the effective budget set in net-trade coordinates: a net trade `d` in the
good comes with the money trade `φ(d) = -dA''/(A' - d)` (defined for `d < A'`). -/
noncomputable def tpFrontier (A₁ A₂ d : ℝ) : ℝ := -(d * A₂) / (A₁ - d)

/-- Every feasible bid, one- or two-sided, lands on the frontier: `m = φ(g)`. -/
theorem tp_outcome_on_frontier [Fintype κ] [DecidableEq κ] (c : κ → ℝ × ℝ) (i : κ) {s b : ℝ}
    (hs : 0 ≤ s) (hb : 0 ≤ b) (hA₁ : 0 < ∑ k ∈ Finset.univ.erase i, (c k).1)
    (hA₂ : 0 < ∑ k ∈ Finset.univ.erase i, (c k).2) :
    tpMoney (Function.update c i (s, b)) i =
      tpFrontier (∑ k ∈ Finset.univ.erase i, (c k).1) (∑ k ∈ Finset.univ.erase i, (c k).2)
        (tpGood (Function.update c i (s, b)) i) := by
  obtain ⟨g, m⟩ := tp_outcome c i hs hb hA₁ hA₂
  rw [g, m]
  set A₁ := ∑ k ∈ Finset.univ.erase i, (c k).1
  set A₂ := ∑ k ∈ Finset.univ.erase i, (c k).2
  have hb' : 0 < b + A₂ := by positivity
  have hs' : 0 < s + A₁ := by positivity
  have hden : A₁ - (b * A₁ - s * A₂) / (b + A₂) = A₂ * (s + A₁) / (b + A₂) := by
    field_simp
    ring
  unfold tpFrontier
  rw [hden]
  field_simp
  ring

/-- `φ(d) = A'' - A'A''/(A' - d)`. -/
theorem tpFrontier_eq {A₁ A₂ d : ℝ} (hd : d < A₁) :
    tpFrontier A₁ A₂ d = A₂ - A₁ * A₂ / (A₁ - d) := by
  have : A₁ - d ≠ 0 := by linarith
  unfold tpFrontier
  field_simp
  ring

/-- **Exercise 18.C.1** (MWG, p. 685). The frontier `φ` is strictly concave on `d < A'`: the
upper boundary of the effective budget set contains no straight segments. -/
theorem tpFrontier_strictConcaveOn {A₁ A₂ : ℝ} (hA₁ : 0 < A₁) (hA₂ : 0 < A₂) :
    StrictConcaveOn ℝ (Set.Iio A₁) (tpFrontier A₁ A₂) := by
  refine ⟨convex_Iio A₁, fun x hx y hy hxy a b ha hb hab => ?_⟩
  simp only [Set.mem_Iio] at hx hy
  have hz : a * x + b * y < A₁ := by
    have : a * x + b * y < a * A₁ + b * A₁ := by
      rcases lt_or_gt_of_ne hxy with h | h
      · nlinarith
      · nlinarith
    linarith [show a * A₁ + b * A₁ = A₁ by rw [← add_mul, hab, one_mul]]
  simp only [smul_eq_mul]
  rw [tpFrontier_eq hx, tpFrontier_eq hy, tpFrontier_eq hz]
  set u := A₁ - x with hu
  set v := A₁ - y with hv
  have hu0 : 0 < u := by linarith
  have hv0 : 0 < v := by linarith
  have hw : A₁ - (a * x + b * y) = a * u + b * v := by
    rw [hu, hv]
    linear_combination (-A₁) * hab
  rw [hw]
  have huv : u ≠ v := fun h => hxy (by linarith)
  have hw0 : 0 < a * u + b * v := by positivity
  -- the strict convexity of `t ↦ 1/t`
  have key : 1 / (a * u + b * v) < a / u + b / v := by
    rw [div_add_div _ _ hu0.ne' hv0.ne', div_lt_div_iff₀ hw0 (mul_pos hu0 hv0)]
    have hsq : 0 < (u - v) ^ 2 := by
      have : u - v ≠ 0 := sub_ne_zero.mpr huv
      positivity
    have hb' : b = 1 - a := by linarith
    subst hb'
    nlinarith [mul_pos ha hb, mul_pos (mul_pos ha hb) hsq]
  have hK : 0 < A₁ * A₂ := mul_pos hA₁ hA₂
  have e1 : a * (A₂ - A₁ * A₂ / u) + b * (A₂ - A₁ * A₂ / v) =
      A₂ - A₁ * A₂ * (a / u + b / v) := by
    have hb' : b = 1 - a := by linarith
    subst hb'
    field_simp
    ring
  have e2 : A₂ - A₁ * A₂ / (a * u + b * v) = A₂ - A₁ * A₂ * (1 / (a * u + b * v)) := by
    rw [mul_one_div]
  rw [e1, e2]
  nlinarith [mul_lt_mul_of_pos_left key hK]

/-- The frontier is nonincreasing on `d < A'`. -/
theorem tpFrontier_antitoneOn {A₁ A₂ : ℝ} (hA₁ : 0 < A₁) (hA₂ : 0 < A₂) :
    AntitoneOn (tpFrontier A₁ A₂) (Set.Iio A₁) := by
  intro x hx y hy hxy
  simp only [Set.mem_Iio] at hx hy
  rw [tpFrontier_eq hx, tpFrontier_eq hy]
  have : A₁ * A₂ / (A₁ - x) ≤ A₁ * A₂ / (A₁ - y) :=
    div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)
  linarith

/-- The largest net purchase of the good: spending all money, `b = ω₂`, buys
`ω₂A'/(ω₂ + A'')`. -/
noncomputable def tpMaxBuy (A₁ A₂ w : ℝ) : ℝ := w * A₁ / (w + A₂)

/-- The achievable net trades in the good are exactly `[-ω₁, ω₂A'/(ω₂ + A'')]`: every feasible
bid lands there, and every point of the interval is reached by a one-sided bid. -/
theorem tp_reachable [Fintype κ] [DecidableEq κ] (c : κ → ℝ × ℝ) (i : κ) {ω : Fin 2 → ℝ}
    (hω : ω ∈ nonnegOrthant 2) (hA₁ : 0 < ∑ k ∈ Finset.univ.erase i, (c k).1)
    (hA₂ : 0 < ∑ k ∈ Finset.univ.erase i, (c k).2) (d : ℝ) :
    (∃ s b : ℝ, 0 ≤ s ∧ s ≤ ω 0 ∧ 0 ≤ b ∧ b ≤ ω 1 ∧
      tpGood (Function.update c i (s, b)) i = d) ↔
    d ∈ Set.Icc (-ω 0) (tpMaxBuy (∑ k ∈ Finset.univ.erase i, (c k).1)
      (∑ k ∈ Finset.univ.erase i, (c k).2) (ω 1)) := by
  have hout : ∀ s b : ℝ, 0 ≤ s → 0 ≤ b → tpGood (Function.update c i (s, b)) i =
      (b * ∑ k ∈ Finset.univ.erase i, (c k).1 - s * ∑ k ∈ Finset.univ.erase i, (c k).2) /
        (b + ∑ k ∈ Finset.univ.erase i, (c k).2) :=
    fun s b hs hb => (tp_outcome c i hs hb hA₁ hA₂).1
  set A₁ := ∑ k ∈ Finset.univ.erase i, (c k).1 with hA₁def
  set A₂ := ∑ k ∈ Finset.univ.erase i, (c k).2 with hA₂def
  have hw : 0 ≤ ω 1 := hω 1
  constructor
  · rintro ⟨s, b, hs, hsω, hb, hbω, rfl⟩
    rw [hout s b hs hb]
    have hb' : 0 < b + A₂ := by positivity
    refine ⟨?_, ?_⟩
    · rw [le_div_iff₀ hb']
      nlinarith
    · unfold tpMaxBuy
      rw [div_le_div_iff₀ hb' (by positivity)]
      nlinarith [mul_nonneg (sub_nonneg.2 hbω) (mul_pos hA₁ hA₂).le,
        mul_nonneg hs (mul_nonneg hA₂.le (add_nonneg hw hA₂.le))]
  · rintro ⟨hd0, hd1⟩
    rcases le_or_gt d 0 with hd | hd
    · refine ⟨-d, 0, by linarith, by linarith, le_rfl, hw, ?_⟩
      rw [hout _ _ (by linarith) le_rfl]
      field_simp
      ring
    · have hlt : d < A₁ := by
        have : tpMaxBuy A₁ A₂ (ω 1) < A₁ := by
          unfold tpMaxBuy
          rw [div_lt_iff₀ (by positivity)]
          nlinarith
        linarith
      have hden : 0 < A₁ - d := by linarith
      refine ⟨0, d * A₂ / (A₁ - d), le_rfl, hω 0, by positivity, ?_, ?_⟩
      · rw [div_le_iff₀ hden]
        unfold tpMaxBuy at hd1
        rw [le_div_iff₀ (by positivity)] at hd1
        linarith
      · rw [hout _ _ le_rfl (by positivity)]
        field_simp
        ring

/-- **Exercise 18.C.1** (MWG, p. 685). The effective budget set of a trading-post consumer
(with the others active on both sides, `A', A'' > 0`) is
`{x ≥ 0 : x₁ - ω₁ ≤ ω₂A'/(ω₂ + A''), x₂ - ω₂ ≤ φ(x₁ - ω₁)}`: the region below the graph of the
strictly concave, nonincreasing frontier `φ`. -/
theorem exercise_18_C_1_eq [Fintype κ] [DecidableEq κ] (c : κ → ℝ × ℝ) (i : κ)
    {ω : Fin 2 → ℝ} (hω : ω ∈ nonnegOrthant 2) (hA₁ : 0 < ∑ k ∈ Finset.univ.erase i, (c k).1)
    (hA₂ : 0 < ∑ k ∈ Finset.univ.erase i, (c k).2) :
    tpBudget c i ω = {x | x ∈ nonnegOrthant 2 ∧
      x 0 - ω 0 ≤ tpMaxBuy (∑ k ∈ Finset.univ.erase i, (c k).1)
        (∑ k ∈ Finset.univ.erase i, (c k).2) (ω 1) ∧
      x 1 - ω 1 ≤ tpFrontier (∑ k ∈ Finset.univ.erase i, (c k).1)
        (∑ k ∈ Finset.univ.erase i, (c k).2) (x 0 - ω 0)} := by
  have hfr := fun (s b : ℝ) (hs : 0 ≤ s) (hb : 0 ≤ b) =>
    tp_outcome_on_frontier c i hs hb hA₁ hA₂
  have hreach := tp_reachable c i hω hA₁ hA₂
  set A₁ := ∑ k ∈ Finset.univ.erase i, (c k).1 with hA₁def
  set A₂ := ∑ k ∈ Finset.univ.erase i, (c k).2 with hA₂def
  have hmax : tpMaxBuy A₁ A₂ (ω 1) < A₁ := by
    unfold tpMaxBuy
    rw [div_lt_iff₀ (by have := hω 1; positivity)]
    nlinarith [hω 1]
  ext x
  constructor
  · rintro ⟨hx, s, b, hs, hsω, hb, hbω, h0, h1⟩
    have hd := (hreach _).mp ⟨s, b, hs, hsω, hb, hbω, rfl⟩
    rw [hfr s b hs hb] at h1
    refine ⟨hx, by linarith [hd.2], ?_⟩
    have hx0 : x 0 - ω 0 < A₁ := by linarith [hd.2]
    have := tpFrontier_antitoneOn hA₁ hA₂ (Set.mem_Iio.mpr hx0)
      (Set.mem_Iio.mpr (hd.2.trans_lt hmax)) (by linarith)
    linarith
  · rintro ⟨hx, h0, h1⟩
    obtain ⟨s, b, hs, hsω, hb, hbω, hg⟩ :=
      (hreach (x 0 - ω 0)).mpr ⟨by linarith [hx 0], h0⟩
    refine ⟨hx, s, b, hs, hsω, hb, hbω, by linarith, ?_⟩
    rw [tp_outcome_on_frontier c i hs hb hA₁ hA₂, hg]
    linarith

/-- **Exercise 18.C.1** (MWG, pp. 664, 685), convexity. With the other consumers active on
both sides of the post (`∑_{k≠i} a'ₖ > 0`, `∑_{k≠i} a''ₖ > 0`), the effective budget set of
consumer `i` (two-sided bids included) is convex. -/
theorem exercise_18_C_1_convex [Fintype κ] [DecidableEq κ] (c : κ → ℝ × ℝ) (i : κ)
    {ω : Fin 2 → ℝ} (hω : ω ∈ nonnegOrthant 2) (hA₁ : 0 < ∑ k ∈ Finset.univ.erase i, (c k).1)
    (hA₂ : 0 < ∑ k ∈ Finset.univ.erase i, (c k).2) :
    Convex ℝ (tpBudget c i ω) := by
  rw [exercise_18_C_1_eq c i hω hA₁ hA₂]
  set A₁ := ∑ k ∈ Finset.univ.erase i, (c k).1 with hA₁def
  set A₂ := ∑ k ∈ Finset.univ.erase i, (c k).2 with hA₂def
  have hmax : tpMaxBuy A₁ A₂ (ω 1) < A₁ := by
    unfold tpMaxBuy
    rw [div_lt_iff₀ (by have := hω 1; positivity)]
    nlinarith [hω 1]
  have hconc := (tpFrontier_strictConcaveOn hA₁ hA₂).concaveOn
  rintro x ⟨hx, hx0, hx1⟩ y ⟨hy, hy0, hy1⟩ a b ha hb hab
  refine ⟨fun l => by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hx l)) (mul_nonneg hb (hy l)), ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have : a * x 0 + b * y 0 - ω 0 = a * (x 0 - ω 0) + b * (y 0 - ω 0) := by
      linear_combination (ω 0) * hab
    rw [this]
    nlinarith
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have e0 : a * x 0 + b * y 0 - ω 0 = a * (x 0 - ω 0) + b * (y 0 - ω 0) := by
      linear_combination (ω 0) * hab
    have e1 : a * x 1 + b * y 1 - ω 1 = a * (x 1 - ω 1) + b * (y 1 - ω 1) := by
      linear_combination (ω 1) * hab
    rw [e0, e1]
    have hc := hconc.2 (Set.mem_Iio.mpr (hx0.trans_lt hmax)) (Set.mem_Iio.mpr (hy0.trans_lt hmax))
      ha hb hab
    simp only [smul_eq_mul] at hc
    nlinarith

/-- **Exercise 18.C.1** (MWG, pp. 664, 685), the upper boundary. For every achievable net trade
`d ∈ [-ω₁, ω₂A'/(ω₂ + A'')]` the point `(ω₁ + d, ω₂ + φ(d))` lies in the effective budget set
and nothing above it does; and the boundary contains no straight segment: for two distinct
boundary points, every point strictly between them lies in the budget set strictly below the
boundary. -/
theorem exercise_18_C_1_boundary [Fintype κ] [DecidableEq κ] (c : κ → ℝ × ℝ) (i : κ)
    {ω : Fin 2 → ℝ} (hω : ω ∈ nonnegOrthant 2) (hA₁ : 0 < ∑ k ∈ Finset.univ.erase i, (c k).1)
    (hA₂ : 0 < ∑ k ∈ Finset.univ.erase i, (c k).2) :
    (∀ d ∈ Set.Icc (-ω 0) (tpMaxBuy (∑ k ∈ Finset.univ.erase i, (c k).1)
        (∑ k ∈ Finset.univ.erase i, (c k).2) (ω 1)),
      ![ω 0 + d, ω 1 + tpFrontier (∑ k ∈ Finset.univ.erase i, (c k).1)
        (∑ k ∈ Finset.univ.erase i, (c k).2) d] ∈ tpBudget c i ω) ∧
    (∀ x ∈ tpBudget c i ω, x 1 ≤ ω 1 + tpFrontier (∑ k ∈ Finset.univ.erase i, (c k).1)
        (∑ k ∈ Finset.univ.erase i, (c k).2) (x 0 - ω 0)) ∧
    ∀ d₁ ∈ Set.Icc (-ω 0) (tpMaxBuy (∑ k ∈ Finset.univ.erase i, (c k).1)
        (∑ k ∈ Finset.univ.erase i, (c k).2) (ω 1)),
      ∀ d₂ ∈ Set.Icc (-ω 0) (tpMaxBuy (∑ k ∈ Finset.univ.erase i, (c k).1)
        (∑ k ∈ Finset.univ.erase i, (c k).2) (ω 1)), d₁ ≠ d₂ → ∀ t : ℝ, 0 < t → t < 1 →
      t * tpFrontier (∑ k ∈ Finset.univ.erase i, (c k).1)
          (∑ k ∈ Finset.univ.erase i, (c k).2) d₁ +
        (1 - t) * tpFrontier (∑ k ∈ Finset.univ.erase i, (c k).1)
          (∑ k ∈ Finset.univ.erase i, (c k).2) d₂ <
      tpFrontier (∑ k ∈ Finset.univ.erase i, (c k).1)
        (∑ k ∈ Finset.univ.erase i, (c k).2) (t * d₁ + (1 - t) * d₂) := by
  have hfr := fun (s b : ℝ) (hs : 0 ≤ s) (hb : 0 ≤ b) =>
    tp_outcome_on_frontier c i hs hb hA₁ hA₂
  have hmo := fun (s b : ℝ) (hs : 0 ≤ s) (hb : 0 ≤ b) => (tp_outcome c i hs hb hA₁ hA₂).2
  have heq := exercise_18_C_1_eq c i hω hA₁ hA₂
  have hreach := tp_reachable c i hω hA₁ hA₂
  set A₁ := ∑ k ∈ Finset.univ.erase i, (c k).1 with hA₁def
  set A₂ := ∑ k ∈ Finset.univ.erase i, (c k).2 with hA₂def
  have hmax : tpMaxBuy A₁ A₂ (ω 1) < A₁ := by
    unfold tpMaxBuy
    rw [div_lt_iff₀ (by have := hω 1; positivity)]
    nlinarith [hω 1]
  refine ⟨fun d hd => ?_, fun x hx => ?_, fun d₁ hd₁ d₂ hd₂ hne t ht0 ht1 => ?_⟩
  · obtain ⟨s, b, hs, hsω, hb, hbω, hg⟩ := (hreach d).mpr hd
    have hm := hfr s b hs hb
    rw [hg] at hm
    -- the bid `(s, b)` attains the point, which is therefore nonnegative
    have hnn : ![ω 0 + d, ω 1 + tpFrontier A₁ A₂ d] ∈ nonnegOrthant 2 := by
      intro l
      fin_cases l
      · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
        linarith [hd.1]
      · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
        rw [← hm, hmo s b hs hb]
        have hs' : 0 < s + A₁ := by positivity
        rw [← sub_nonneg]
        have : ω 1 + (s * A₂ - b * A₁) / (s + A₁) - 0 =
            ((ω 1 - b) * (s + A₁) + b * s + s * A₂) / (s + A₁) := by
          field_simp
          ring
        rw [this]
        apply div_nonneg _ hs'.le
        nlinarith
    refine ⟨hnn, s, b, hs, hsω, hb, hbω, ?_, ?_⟩
    · simp [hg]
    · simp [hm]
  · rw [heq] at hx
    linarith [hx.2.2]
  · have hs := tpFrontier_strictConcaveOn hA₁ hA₂
    have := hs.2 (Set.mem_Iio.mpr (hd₁.2.trans_lt hmax)) (Set.mem_Iio.mpr (hd₂.2.trans_lt hmax))
      hne ht0 (by linarith : (0 : ℝ) < 1 - t) (by ring)
    simpa only [smul_eq_mul] using this

end MWG.CoreFoundations
