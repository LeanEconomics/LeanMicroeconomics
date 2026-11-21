/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGExternalitiesPublicGoods.Tools
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Public goods (MWG Section 11.C)

MWG, pp. 359-364, and Exercises 11.C.1-11.C.2 (p. 379).

* **Definition 11.C.1** and the depletable/nondepletable distinction (`DepletableFeasible`,
  `NondepletableFeasible`), footnote 9 (pure public goods).
* The model `PublicGood ι`: `I` consumers with derived utilities `φᵢ(q)` (strictly decreasing
  `φᵢ'`) and a cost `c(q)` with strictly increasing `c'` (MWG: `φᵢ'' < 0`, `c'' > 0`).
* Pareto optimality (footnote 4 / Section 10.D: `pareto_iff_optimal`) and the **Samuelson
  condition (11.C.1)** (`eq_11_C_1`).
* Private provision: (11.C.2)-(11.C.4) (`consumer_foc`, `firm_foc`), (11.C.5), `q* < q°` and
  footnote 10 (also for a public bad), the stark free-rider result.
* Corrective subsidies for consumers (p. 363; **Exercise 11.C.1**) and a subsidy on the firm's
  output (**Exercise 11.C.2**): one model of equilibrium with consumer subsidies `sᵢ` and an
  output subsidy `σ` (`IsSubsidyEq`) covers all three.
* **Lindahl equilibrium**: (11.C.6)-(11.C.8), `q** = q°`, existence with prices `φᵢ'(q°)`;
  footnote 11 (exclusion is inefficient at a Pareto optimum).
* A concrete instance: `φᵢ(q) = -aᵢ e^{-q}`, `c(q) = e^q`, `a = (1, 3)`: `q° = log 2`,
  `q* = (log 3)/2`, Lindahl prices `(1/2, 3/2)`.
-/

namespace MWG.ExternalitiesPublicGoods

open MWG.CompetitiveMarkets

/-! ## Definition 11.C.1 -/

/-- Feasible consumptions of a private (depletable) good: `∑ xᵢ ≤ q`. -/
def DepletableFeasible {ι : Type*} [Fintype ι] (q : ℝ) (x : ι → ℝ) : Prop :=
  (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ q

/-- **Definition 11.C.1** (MWG, p. 359). Feasible consumptions of a public (nondepletable) good:
each consumer can use the whole amount, `xᵢ ≤ q` for all `i`. -/
def NondepletableFeasible {ι : Type*} (q : ℝ) (x : ι → ℝ) : Prop :=
  (∀ i, 0 ≤ x i) ∧ ∀ i, x i ≤ q

/-- **Definition 11.C.1** (MWG, p. 359), unfolded. -/
theorem definition_11_C_1 {ι : Type*} (q : ℝ) (x : ι → ℝ) :
    NondepletableFeasible q x ↔ (∀ i, 0 ≤ x i) ∧ ∀ i, x i ≤ q := Iff.rfl

/-- **Definition 11.C.1** (MWG, p. 359): use of a public good by one agent does not preclude its
use by others. Any consumer can raise her use to the whole amount `q` while the others keep
theirs. -/
theorem nondepletable_not_preclude {ι : Type*} [DecidableEq ι] {q : ℝ} {x : ι → ℝ}
    (hx : NondepletableFeasible q x) (hq : 0 ≤ q) (i : ι) :
    NondepletableFeasible q (Function.update x i q) := by
  refine ⟨fun j => ?_, fun j => ?_⟩
  · rcases eq_or_ne j i with h | h
    · rw [h, Function.update_self]; exact hq
    · rw [Function.update_of_ne h]; exact hx.1 j
  · rcases eq_or_ne j i with h | h
    · rw [h, Function.update_self]
    · rw [Function.update_of_ne h]; exact hx.2 j

/-- For a private good (p. 360), each unit consumed by `i` is one unit less for the others: if
`i` consumes all of `q`, every other consumer gets nothing. -/
theorem depletable_precludes {ι : Type*} [Fintype ι] {q : ℝ} {x : ι → ℝ}
    (hx : DepletableFeasible q x) {i : ι} (hi : x i = q) (j : ι) (hj : j ≠ i) : x j = 0 := by
  classical
  have hsum : x i + x j ≤ ∑ k, x k := by
    rw [← Finset.sum_pair hj.symm]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun k _ _ => hx.1 k)
  exact le_antisymm (by linarith [hx.2]) (hx.1 j)

/-- **Footnote 9** (MWG, p. 360). Every depletable-feasible profile is nondepletable-feasible:
the public good imposes weakly fewer constraints (a pure public good has no depletability). -/
theorem depletable_imp_nondepletable {ι : Type*} [Fintype ι] {q : ℝ} {x : ι → ℝ}
    (hx : DepletableFeasible q x) : NondepletableFeasible q x := by
  classical
  refine ⟨hx.1, fun i => le_trans ?_ hx.2⟩
  exact Finset.single_le_sum (fun k _ => hx.1 k) (Finset.mem_univ i)

/-! ## The model -/

/-- **The public good model** (MWG, p. 360). Consumers `i ∈ ι` with derived utilities `φᵢ(q) + wᵢ`
and a cost `c(q)` of supplying the public good. -/
structure PublicGood (ι : Type*) where
  /-- Consumer `i`'s derived utility from the public good. -/
  φ : ι → ℝ → ℝ
  /-- `φᵢ'`. -/
  dφ : ι → ℝ → ℝ
  /-- The cost function. -/
  c : ℝ → ℝ
  /-- `c'`. -/
  dc : ℝ → ℝ
  hφ : ∀ i x, HasDerivAt (φ i) (dφ i x) x
  hc : ∀ x, HasDerivAt c (dc x) x
  antiφ : ∀ i, StrictAntiOn (dφ i) (Set.Ici 0)
  monoc : StrictMonoOn dc (Set.Ici 0)

namespace PublicGood

variable {ι : Type*} [Fintype ι] (G : PublicGood ι)

/-- The aggregate surplus `∑ᵢ φᵢ(q) - c(q)`. -/
def surplus (q : ℝ) : ℝ := ∑ i, G.φ i q - G.c q

/-- The marginal social surplus `∑ᵢ φᵢ'(q) - c'(q)`. -/
def msurplus (q : ℝ) : ℝ := ∑ i, G.dφ i q - G.dc q

theorem hasDerivAt_surplus (q : ℝ) : HasDerivAt G.surplus (G.msurplus q) q :=
  (HasDerivAt.fun_sum fun i _ => G.hφ i q).sub (G.hc q)

theorem anti_msurplus : StrictAntiOn G.msurplus (Set.Ici 0) := by
  intro a ha b hb hab
  have h1 : ∑ i, G.dφ i b ≤ ∑ i, G.dφ i a :=
    Finset.sum_le_sum fun i _ => (G.antiφ i ha hb hab).le
  have h2 := G.monoc ha hb hab
  simp only [msurplus]
  linarith

/-- The optimal level `q°`: it maximizes the aggregate surplus on `ℝ₊`. -/
def IsOptimal (q : ℝ) : Prop := 0 ≤ q ∧ ∀ y, 0 ≤ y → G.surplus y ≤ G.surplus q

/-- **Pareto optimality** (MWG, p. 360, via Section 10.D). With utilities `φᵢ(q) + mᵢ` and
`∑ mᵢ = W - c(q)`, an allocation is Pareto optimal iff its level of the public good is optimal. -/
theorem pareto_iff_optimal [Nonempty ι] (W : ℝ) (a : QLAlloc ι ℝ)
    (ha : QLFeasible (Set.Ici 0) G.c W a) :
    QLPareto G.φ (Set.Ici 0) G.c W a ↔ G.IsOptimal a.x := by
  rw [ql_pareto_iff _ _ _ _ a ha]
  exact ⟨fun h => ⟨ha.1, fun y hy => h y hy⟩, fun h y hy => h.2 y hy⟩

/-- **The Samuelson condition (11.C.1)** (MWG, p. 360). `q°` is optimal iff
`∑ᵢ φᵢ'(q°) ≤ c'(q°)`, with equality if `q° > 0`. -/
theorem eq_11_C_1 (q : ℝ) :
    G.IsOptimal q ↔ 0 ≤ q ∧ ∑ i, G.dφ i q ≤ G.dc q ∧ (0 < q → ∑ i, G.dφ i q = G.dc q) := by
  rw [IsOptimal, kt_isMax_iff G.hasDerivAt_surplus G.anti_msurplus.antitoneOn]
  simp only [IsFOCSol, msurplus]
  constructor
  · rintro ⟨h0, h1, h2⟩
    exact ⟨h0, by linarith, fun hp => by linarith [h2 hp]⟩
  · rintro ⟨h0, h1, h2⟩
    exact ⟨h0, by linarith, fun hp => by linarith [h2 hp]⟩

/-- The optimal level is unique. -/
theorem optimal_unique {q q' : ℝ} (hq : G.IsOptimal q) (hq' : G.IsOptimal q') : q = q' :=
  kt_max_unique G.hasDerivAt_surplus G.anti_msurplus hq.1 hq.2 hq'.1 hq'.2

/-! ## Equilibrium with subsidies: private provision, Exercises 11.C.1-11.C.2 -/

/-- Consumer `i`'s problem (11.C.2), with a per-unit subsidy `s`: given the others' purchases `R`,
`xᵢ ≥ 0` maximizes `φᵢ(xᵢ + R) + s xᵢ - p xᵢ`. -/
def IsConsumerChoice (i : ι) (s p R x : ℝ) : Prop :=
  0 ≤ x ∧ ∀ y, 0 ≤ y → G.φ i (y + R) + s * y - p * y ≤ G.φ i (x + R) + s * x - p * x

omit [Fintype ι] in
/-- **(11.C.3)** (MWG, p. 361). Given others' purchases `R ≥ 0`, consumer `i`'s choice `x` is
optimal iff `φᵢ'(x + R) + s ≤ p`, with equality if `x > 0`. -/
theorem consumer_foc (i : ι) (s p R x : ℝ) (hR : 0 ≤ R) :
    G.IsConsumerChoice i s p R x ↔
      0 ≤ x ∧ G.dφ i (x + R) + s ≤ p ∧ (0 < x → G.dφ i (x + R) + s = p) := by
  have hf : ∀ y, HasDerivAt (fun y => G.φ i (y + R) + s * y - p * y)
      (G.dφ i (y + R) + s - p) y := fun y => by
    have h1 : HasDerivAt (fun y => G.φ i (y + R)) (G.dφ i (y + R)) y :=
      (G.hφ i (y + R)).comp_add_const y R
    have h2 : HasDerivAt (fun y => s * y) s y := by simpa using (hasDerivAt_id y).const_mul s
    have h3 : HasDerivAt (fun y => p * y) p y := by simpa using (hasDerivAt_id y).const_mul p
    exact (h1.add h2).sub h3
  have hanti : AntitoneOn (fun y => G.dφ i (y + R) + s - p) (Set.Ici 0) := by
    intro a ha b hb hab
    have := (G.antiφ i).antitoneOn (show 0 ≤ a + R by linarith [ha.out])
      (show 0 ≤ b + R by linarith [hb.out]) (by linarith)
    simp only
    linarith
  rw [IsConsumerChoice, kt_isMax_iff hf hanti]
  simp only [IsFOCSol]
  constructor
  · rintro ⟨h0, h1, h2⟩
    exact ⟨h0, by linarith, fun hp => by linarith [h2 hp]⟩
  · rintro ⟨h0, h1, h2⟩
    exact ⟨h0, by linarith, fun hp => by linarith [h2 hp]⟩

/-- The firm's problem with a per-unit output subsidy `σ`: `q ≥ 0` maximizes
`(p + σ) q - c(q)`. -/
def IsFirmChoice (σ p q : ℝ) : Prop :=
  0 ≤ q ∧ ∀ y, 0 ≤ y → (p + σ) * y - G.c y ≤ (p + σ) * q - G.c q

omit [Fintype ι] in
/-- **(11.C.4)** (MWG, p. 361). The firm's supply `q` is optimal iff `p + σ ≤ c'(q)`, with
equality if `q > 0`. -/
theorem firm_foc (σ p q : ℝ) :
    G.IsFirmChoice σ p q ↔ 0 ≤ q ∧ p + σ ≤ G.dc q ∧ (0 < q → p + σ = G.dc q) := by
  have hf : ∀ y, HasDerivAt (fun y => (p + σ) * y - G.c y) (p + σ - G.dc y) y := fun y => by
    have h2 : HasDerivAt (fun y => (p + σ) * y) (p + σ) y := by
      simpa using (hasDerivAt_id y).const_mul (p + σ)
    exact h2.sub (G.hc y)
  have hanti : AntitoneOn (fun y => p + σ - G.dc y) (Set.Ici 0) := by
    intro a ha b hb hab
    have := G.monoc.monotoneOn ha hb hab
    simp only
    linarith
  rw [IsFirmChoice, kt_isMax_iff hf hanti]
  simp only [IsFOCSol]
  constructor
  · rintro ⟨h0, h1, h2⟩
    exact ⟨h0, by linarith, fun hp => by linarith [h2 hp]⟩
  · rintro ⟨h0, h1, h2⟩
    exact ⟨h0, by linarith, fun hp => by linarith [h2 hp]⟩

/-- A competitive equilibrium of private provision with consumer subsidies `sᵢ` and an output
subsidy `σ` (MWG, pp. 361-363): purchases `xᵢ`, price `p`, output `q`; each consumer takes the
others' purchases as given (11.C.2), the firm maximizes profit, and `q = ∑ xᵢ`. -/
def IsSubsidyEq (s : ι → ℝ) (σ : ℝ) (x : ι → ℝ) (p q : ℝ) : Prop :=
  (∀ i, G.IsConsumerChoice i (s i) p (q - x i) (x i)) ∧ G.IsFirmChoice σ p q ∧ q = ∑ i, x i

/-- The unsubsidized private-provision equilibrium. -/
def IsPrivateEq (x : ι → ℝ) (p q : ℝ) : Prop := G.IsSubsidyEq (fun _ => 0) 0 x p q

theorem others_nonneg {x : ι → ℝ} (hx : ∀ i, 0 ≤ x i) (i : ι) :
    0 ≤ (∑ j, x j) - x i := by
  classical
  have := Finset.single_le_sum (fun k _ => hx k) (Finset.mem_univ i)
  linarith

/-- The equilibrium conditions in first-order form: `φᵢ'(q) + sᵢ ≤ p` (equality if `xᵢ > 0`),
`p + σ ≤ c'(q)` (equality if `q > 0`), `xᵢ ≥ 0`, `q = ∑ xᵢ`. -/
theorem subsidyEq_iff (s : ι → ℝ) (σ : ℝ) (x : ι → ℝ) (p q : ℝ) :
    G.IsSubsidyEq s σ x p q ↔
      (∀ i, 0 ≤ x i ∧ G.dφ i q + s i ≤ p ∧ (0 < x i → G.dφ i q + s i = p)) ∧
        (p + σ ≤ G.dc q ∧ (0 < q → p + σ = G.dc q)) ∧ q = ∑ i, x i := by
  constructor
  · rintro ⟨hc, hf, hq⟩
    have hx : ∀ i, 0 ≤ x i := fun i => (hc i).1
    refine ⟨fun i => ?_, ((G.firm_foc σ p q).1 hf).2, hq⟩
    have hR : 0 ≤ q - x i := by rw [hq]; exact others_nonneg hx i
    have := (G.consumer_foc i (s i) p (q - x i) (x i) hR).1 (hc i)
    simpa only [add_sub_cancel] using this
  · rintro ⟨hc, hf, hq⟩
    have hx : ∀ i, 0 ≤ x i := fun i => (hc i).1
    have hq0 : 0 ≤ q := by rw [hq]; exact Finset.sum_nonneg fun i _ => hx i
    refine ⟨fun i => ?_, (G.firm_foc σ p q).2 ⟨hq0, hf⟩, hq⟩
    have hR : 0 ≤ q - x i := by rw [hq]; exact others_nonneg hx i
    rw [G.consumer_foc i (s i) p (q - x i) (x i) hR]
    simpa only [add_sub_cancel] using hc i

/-- **(11.C.3)-(11.C.4)** (MWG, p. 361). At a private-provision equilibrium,
`φᵢ'(x*) ≤ p*` with equality if `xᵢ* > 0`, and `p* ≤ c'(q*)` with equality if `q* > 0`. -/
theorem eq_11_C_3_4 {x : ι → ℝ} {p q : ℝ} (he : G.IsPrivateEq x p q) :
    (∀ i, G.dφ i q ≤ p ∧ (0 < x i → G.dφ i q = p)) ∧ p ≤ G.dc q ∧ (0 < q → p = G.dc q) := by
  obtain ⟨hc, hf, -⟩ := (G.subsidyEq_iff _ _ x p q).1 he
  refine ⟨fun i => ⟨by simpa using (hc i).2.1, fun h => by simpa using (hc i).2.2 h⟩,
    by simpa using hf.1, fun h => by simpa using hf.2 h⟩

/-- **(11.C.5)** (MWG, p. 361). If the public good is desirable (`φᵢ' > 0`), there are at least
two consumers and `q* > 0`, then `∑ᵢ φᵢ'(q*) > c'(q*)`. -/
theorem eq_11_C_5 {x : ι → ℝ} {p q : ℝ} (he : G.IsPrivateEq x p q)
    (hdes : ∀ i y, 0 ≤ y → 0 < G.dφ i y) (hI : ∃ i j : ι, i ≠ j) (hq : 0 < q) :
    G.dc q < ∑ i, G.dφ i q := by
  classical
  obtain ⟨hc, hf, hsum⟩ := (G.subsidyEq_iff _ _ x p q).1 he
  have hq0 : 0 ≤ q := hq.le
  obtain ⟨i, hi⟩ : ∃ i, 0 < x i := by
    by_contra hno
    push Not at hno
    have : ∑ i, x i ≤ 0 := Finset.sum_nonpos fun i _ => hno i
    linarith
  have hpi : G.dφ i q = p := by simpa using (hc i).2.2 hi
  have hpc : p = G.dc q := by simpa using hf.2 hq
  obtain ⟨j₁, j₂, hj⟩ := hI
  obtain ⟨j, hji⟩ : ∃ j, j ≠ i := by
    by_cases h : j₁ = i
    · exact ⟨j₂, fun h' => hj (h.trans h'.symm)⟩
    · exact ⟨j₁, h⟩
  have h2 : G.dφ i q + G.dφ j q ≤ ∑ k, G.dφ k q := by
    rw [← Finset.sum_pair (f := fun k => G.dφ k q) hji.symm]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun k _ _ => (hdes k q hq0).le)
  have := hdes j q hq0
  linarith

/-- **Underprovision** (MWG, p. 362, footnote 10). With a desirable public good (`φᵢ' > 0`,
`c' > 0`), at least two consumers and `q° > 0`, the private-provision level is too low:
`q* < q°`. -/
theorem underprovision {x : ι → ℝ} {p q qo : ℝ} (he : G.IsPrivateEq x p q)
    (ho : G.IsOptimal qo) (hdes : ∀ i y, 0 ≤ y → 0 < G.dφ i y) (hI : ∃ i j : ι, i ≠ j)
    (hqo : 0 < qo) : q < qo := by
  obtain ⟨hc, hf, hsum⟩ := (G.subsidyEq_iff _ _ x p q).1 he
  have hq0 : 0 ≤ q := by rw [hsum]; exact Finset.sum_nonneg fun i _ => (hc i).1
  rcases eq_or_lt_of_le hq0 with h0 | hpos
  · rw [← h0]; exact hqo
  · have h5 := G.eq_11_C_5 he hdes hI hpos
    by_contra hle
    push Not at hle
    have hopt := (G.eq_11_C_1 qo).1 ho
    rcases eq_or_lt_of_le hle with heq | hlt
    · rw [← heq] at h5; linarith [hopt.2.2 hqo]
    · have := G.anti_msurplus ho.1 hq0 hlt
      simp only [msurplus] at this
      linarith [hopt.2.2 hqo]

/-- **Footnote 10, public bad** (MWG, p. 362). If `φᵢ' < 0` and `c' < 0` (a public bad whose
reduction is costly), there are at least two consumers and `q* > 0`, the inequalities reverse:
`q° < q*`. (For `q* = 0` no reversal is possible, since `q° ≥ 0`.) -/
theorem public_bad_excess {x : ι → ℝ} {p q qo : ℝ} (he : G.IsPrivateEq x p q)
    (ho : G.IsOptimal qo) (hbad : ∀ i y, 0 ≤ y → G.dφ i y < 0) (hI : ∃ i j : ι, i ≠ j)
    (hq : 0 < q) : qo < q := by
  classical
  obtain ⟨hc, hf, hsum⟩ := (G.subsidyEq_iff _ _ x p q).1 he
  obtain ⟨i, hi⟩ : ∃ i, 0 < x i := by
    by_contra hno
    push Not at hno
    have : ∑ i, x i ≤ 0 := Finset.sum_nonpos fun i _ => hno i
    linarith
  have hpi : G.dφ i q = p := by simpa using (hc i).2.2 hi
  have hpc : p = G.dc q := by simpa using hf.2 hq
  obtain ⟨j₁, j₂, hj⟩ := hI
  obtain ⟨j, hji⟩ : ∃ j, j ≠ i := by
    by_cases h : j₁ = i
    · exact ⟨j₂, fun h' => hj (h.trans h'.symm)⟩
    · exact ⟨j₁, h⟩
  have h2 : ∑ k, G.dφ k q ≤ G.dφ i q + G.dφ j q := by
    rw [← Finset.sum_pair (f := fun k => G.dφ k q) hji.symm]
    exact Finset.sum_le_sum_of_subset_of_nonpos (Finset.subset_univ _)
      (fun k _ _ => (hbad k q hq.le).le)
  have hj' := hbad j q hq.le
  have hlt : ∑ k, G.dφ k q < G.dc q := by linarith
  by_contra hle
  push Not at hle
  have hopt := (G.eq_11_C_1 qo).1 ho
  rcases eq_or_lt_of_le hle with heq | hlt'
  · rw [heq] at hlt; linarith [hopt.2.2 (heq ▸ hq)]
  · have := G.anti_msurplus hq.le ho.1 hlt'
    simp only [msurplus] at this
    linarith [hopt.2.2 (hq.trans hlt')]

/-- **The stark free-rider problem** (MWG, p. 362). If the consumers are ordered by marginal
benefit, `φ₁'(x) < ⋯ < φ_I'(x)` at all `x ≥ 0`, only consumer `I` can purchase a positive amount in
equilibrium, and the equilibrium level satisfies `φ_I'(q*) = c'(q*)` if `q* > 0`. -/
theorem stark_free_rider {n : ℕ} (G : PublicGood (Fin (n + 1))) {x : Fin (n + 1) → ℝ}
    {p q : ℝ} (he : G.IsPrivateEq x p q)
    (hord : ∀ i j : Fin (n + 1), i < j → ∀ y, 0 ≤ y → G.dφ i y < G.dφ j y) :
    (∀ i, 0 < x i → i = Fin.last n) ∧ (0 < q → G.dφ (Fin.last n) q = G.dc q) := by
  obtain ⟨hc, hf, hsum⟩ := (G.subsidyEq_iff _ _ x p q).1 he
  have hq0 : 0 ≤ q := by rw [hsum]; exact Finset.sum_nonneg fun i _ => (hc i).1
  have hbuy : ∀ i, 0 < x i → i = Fin.last n := by
    intro i hi
    by_contra hne
    have hlt : i < Fin.last n := lt_of_le_of_ne (Fin.le_last i) hne
    have h1 : G.dφ i q = p := by simpa using (hc i).2.2 hi
    have h2 : G.dφ (Fin.last n) q ≤ p := by simpa using (hc (Fin.last n)).2.1
    have := hord i (Fin.last n) hlt q hq0
    linarith
  refine ⟨hbuy, fun hq => ?_⟩
  have hxl : 0 < x (Fin.last n) := by
    by_contra hle
    push Not at hle
    have : ∑ i, x i ≤ 0 := Finset.sum_nonpos fun i _ => by
      rcases eq_or_ne i (Fin.last n) with h | h
      · rw [h]; exact hle
      · exact le_of_not_gt fun hi => h (hbuy i hi)
    linarith
  have h1 : G.dφ (Fin.last n) q = p := by simpa using (hc (Fin.last n)).2.2 hxl
  have h2 : p = G.dc q := by simpa using hf.2 hq
  rw [h1, h2]

/-- **Corrective subsidies** (MWG, pp. 362-363; **Exercise 11.C.1**, p. 379). With consumer
subsidies `sᵢ = ∑_{j ≠ i} φⱼ'(q°)`, the total amount of the public good in any equilibrium is
`q°`. -/
theorem exercise_11_C_1 [Nonempty ι] {qo : ℝ} (ho : G.IsOptimal qo) {x : ι → ℝ} {p q : ℝ}
    (he : G.IsSubsidyEq (fun i => ∑ j, G.dφ j qo - G.dφ i qo) 0 x p q) : q = qo := by
  classical
  obtain ⟨hc, hf, hsum⟩ := (G.subsidyEq_iff _ _ x p q).1 he
  have hopt := (G.eq_11_C_1 qo).1 ho
  have hq0 : 0 ≤ q := by rw [hsum]; exact Finset.sum_nonneg fun i _ => (hc i).1
  simp only [add_zero] at hf
  rcases eq_or_lt_of_le hq0 with h0 | hpos
  · -- `q = 0`
    rcases eq_or_lt_of_le ho.1 with h0' | hqo
    · rw [← h0, ← h0']
    · exfalso
      obtain ⟨i⟩ := ‹Nonempty ι›
      have h1 := (hc i).2.1
      rw [← h0] at h1 hf
      have h2 := (G.antiφ i) (le_refl (0 : ℝ)) ho.1 hqo
      have h3 := G.monoc (le_refl (0 : ℝ)) ho.1 hqo
      linarith [hopt.2.2 hqo, hf.1]
  · obtain ⟨i, hi⟩ : ∃ i, 0 < x i := by
      by_contra hno
      push Not at hno
      have : ∑ i, x i ≤ 0 := Finset.sum_nonpos fun i _ => hno i
      linarith
    have hpi := (hc i).2.2 hi
    have hpc := hf.2 hpos
    rcases lt_trichotomy q qo with hlt | heq | hgt
    · exfalso
      have h2 := (G.antiφ i) hq0 ho.1 hlt
      have h3 := G.monoc hq0 ho.1 hlt
      linarith [hopt.2.2 (hpos.trans hlt)]
    · exact heq
    · exfalso
      have h2 := (G.antiφ i) ho.1 hq0 hgt
      have h3 := G.monoc ho.1 hq0 hgt
      linarith [hopt.2.1]

/-- **Exercise 11.C.1**, existence: the corrective subsidies support an equilibrium at `q°`
(consumer `i₀` buys `q°` at price `c'(q°)`). -/
theorem exercise_11_C_1_exists [DecidableEq ι] {qo : ℝ} (ho : G.IsOptimal qo) (i₀ : ι) :
    G.IsSubsidyEq (fun i => ∑ j, G.dφ j qo - G.dφ i qo) 0 (Pi.single i₀ qo) (G.dc qo) qo := by
  have hopt := (G.eq_11_C_1 qo).1 ho
  rw [subsidyEq_iff]
  refine ⟨fun i => ⟨?_, by linarith [hopt.2.1], fun hi => ?_⟩, ⟨by simp, fun _ => by simp⟩,
    by simp⟩
  · rcases eq_or_ne i i₀ with h | h
    · rw [h, Pi.single_eq_same]; exact ho.1
    · rw [Pi.single_eq_of_ne h]
  · have hpos : 0 < qo := by
      rcases eq_or_ne i i₀ with h | h
      · rw [h, Pi.single_eq_same] at hi; exact hi
      · rw [Pi.single_eq_of_ne h] at hi; exact absurd hi (lt_irrefl 0)
    linarith [hopt.2.2 hpos]

/-- **Exercise 11.C.2** (MWG, p. 379). A per-unit subsidy on the firm's output also restores
efficiency: with `q° > 0` and `i₀` a consumer with the largest marginal benefit at `q°`, the
output subsidy `σ = ∑ᵢ φᵢ'(q°) - φ_{i₀}'(q°)` makes `q°` the total in every equilibrium. -/
theorem exercise_11_C_2 [Nonempty ι] {qo : ℝ} (ho : G.IsOptimal qo) (hqo : 0 < qo) (i₀ : ι)
    (hi₀ : ∀ k, G.dφ k qo ≤ G.dφ i₀ qo) {x : ι → ℝ} {p q : ℝ}
    (he : G.IsSubsidyEq (fun _ => 0) (∑ j, G.dφ j qo - G.dφ i₀ qo) x p q) : q = qo := by
  obtain ⟨hc, hf, hsum⟩ := (G.subsidyEq_iff _ _ x p q).1 he
  have hopt := (G.eq_11_C_1 qo).1 ho
  have hS := hopt.2.2 hqo
  have hq0 : 0 ≤ q := by rw [hsum]; exact Finset.sum_nonneg fun i _ => (hc i).1
  simp only [add_zero] at hc
  rcases eq_or_lt_of_le hq0 with h0 | hpos
  · exfalso
    have h1 := (hc i₀).2.1
    rw [← h0] at h1 hf
    have h2 := (G.antiφ i₀) (le_refl (0 : ℝ)) ho.1 hqo
    have h3 := G.monoc (le_refl (0 : ℝ)) ho.1 hqo
    linarith [hf.1]
  · obtain ⟨i, hi⟩ : ∃ i, 0 < x i := by
      by_contra hno
      push Not at hno
      have : ∑ i, x i ≤ 0 := Finset.sum_nonpos fun i _ => hno i
      linarith
    have hpi := (hc i).2.2 hi
    have hpc := hf.2 hpos
    rcases lt_trichotomy q qo with hlt | heq | hgt
    · exfalso
      have h1 := (hc i₀).2.1
      have h2 := (G.antiφ i₀) hq0 ho.1 hlt
      have h3 := G.monoc hq0 ho.1 hlt
      linarith
    · exact heq
    · exfalso
      have h2 := (G.antiφ i) ho.1 hq0 hgt
      have h3 := G.monoc ho.1 hq0 hgt
      have := hi₀ i
      linarith

/-- **Exercise 11.C.2**, existence: under the output subsidy, consumer `i₀` buying `q°` at price
`φ_{i₀}'(q°)` is an equilibrium. -/
theorem exercise_11_C_2_exists [DecidableEq ι] {qo : ℝ} (ho : G.IsOptimal qo) (hqo : 0 < qo)
    (i₀ : ι) (hi₀ : ∀ k, G.dφ k qo ≤ G.dφ i₀ qo) :
    G.IsSubsidyEq (fun _ => 0) (∑ j, G.dφ j qo - G.dφ i₀ qo) (Pi.single i₀ qo)
      (G.dφ i₀ qo) qo := by
  have hS := ((G.eq_11_C_1 qo).1 ho).2.2 hqo
  rw [subsidyEq_iff]
  refine ⟨fun i => ⟨?_, by simpa using hi₀ i, fun hi => ?_⟩, ⟨by linarith, fun _ => by linarith⟩,
    by simp⟩
  · rcases eq_or_ne i i₀ with h | h
    · rw [h, Pi.single_eq_same]; exact ho.1
    · rw [Pi.single_eq_of_ne h]
  · rcases eq_or_ne i i₀ with h | h
    · rw [h]; simp
    · rw [Pi.single_eq_of_ne h] at hi; exact absurd hi (lt_irrefl 0)

/-! ## Lindahl equilibrium -/

/-- A **Lindahl equilibrium** (MWG, pp. 363-364): personalized prices `pᵢ`, consumptions `xᵢ`
maximizing `φᵢ(xᵢ) - pᵢ xᵢ` on `ℝ₊` (11.C.6), output `q` maximizing `(∑ pᵢ) q - c(q)` (11.C.7),
and market clearing `xᵢ = q` for all `i`. -/
def IsLindahlEq (p : ι → ℝ) (x : ι → ℝ) (q : ℝ) : Prop :=
  (∀ i, 0 ≤ x i ∧ ∀ y, 0 ≤ y → G.φ i y - p i * y ≤ G.φ i (x i) - p i * x i) ∧
    G.IsFirmChoice 0 (∑ i, p i) q ∧ ∀ i, x i = q

omit [Fintype ι] in
/-- **(11.C.6)** (MWG, p. 363). Consumer `i`'s Lindahl demand: `φᵢ'(xᵢ) ≤ pᵢ`, equality if
`xᵢ > 0`. -/
theorem eq_11_C_6 (i : ι) (pi xi : ℝ) :
    (0 ≤ xi ∧ ∀ y, 0 ≤ y → G.φ i y - pi * y ≤ G.φ i xi - pi * xi) ↔
      0 ≤ xi ∧ G.dφ i xi ≤ pi ∧ (0 < xi → G.dφ i xi = pi) := by
  have h := G.consumer_foc i 0 pi 0 xi le_rfl
  simp only [IsConsumerChoice, add_zero, zero_mul] at h
  rw [← h]

/-- **(11.C.8)** (MWG, p. 364) and **`q** = q°`**: in a Lindahl equilibrium the level of the
public good satisfies the Samuelson condition, hence is optimal. -/
theorem lindahl_optimal {p x : ι → ℝ} {q : ℝ} (he : G.IsLindahlEq p x q) : G.IsOptimal q := by
  obtain ⟨hc, hf, hclear⟩ := he
  have hf' := (G.firm_foc 0 (∑ i, p i) q).1 hf
  simp only [add_zero] at hf'
  have hci : ∀ i, G.dφ i q ≤ p i ∧ (0 < q → G.dφ i q = p i) := fun i => by
    have := (G.eq_11_C_6 i (p i) (x i)).1 (hc i)
    rw [hclear i] at this
    exact this.2
  rw [eq_11_C_1]
  refine ⟨hf'.1, (Finset.sum_le_sum fun i _ => (hci i).1).trans hf'.2.1, fun hq => ?_⟩
  rw [Finset.sum_congr rfl fun i _ => (hci i).2 hq]
  exact hf'.2.2 hq

/-- **Existence of the Lindahl equilibrium**: at `q°`, the personalized prices `pᵢ = φᵢ'(q°)`
support it. -/
theorem lindahl_exists {qo : ℝ} (ho : G.IsOptimal qo) :
    G.IsLindahlEq (fun i => G.dφ i qo) (fun _ => qo) qo := by
  have hopt := (G.eq_11_C_1 qo).1 ho
  refine ⟨fun i => (G.eq_11_C_6 i _ _).2 ⟨ho.1, le_rfl, fun _ => rfl⟩,
    (G.firm_foc 0 _ qo).2 ⟨ho.1, by simpa using hopt.2.1, fun h => by simpa using hopt.2.2 h⟩,
    fun _ => rfl⟩

omit [Fintype ι] in
/-- **Footnote 11** (MWG, p. 364). A Pareto optimal allocation involves no exclusion: if consumer
`i` is excluded from part of the public good (`xᵢ < q`) and `φᵢ` is strictly increasing, giving her
the whole amount costs nothing and makes her strictly better off. -/
theorem footnote_11 [DecidableEq ι] {q : ℝ} {x : ι → ℝ} (hx : NondepletableFeasible q x)
    (hq : 0 ≤ q) (i : ι) (hi : x i < q) (hmono : StrictMono (G.φ i)) :
    NondepletableFeasible q (Function.update x i q) ∧
      (∀ j, G.φ j (x j) ≤ G.φ j (Function.update x i q j)) ∧
      G.φ i (x i) < G.φ i (Function.update x i q i) := by
  refine ⟨nondepletable_not_preclude hx hq i, fun j => ?_, ?_⟩
  · rcases eq_or_ne j i with h | h
    · subst h; rw [Function.update_self]; exact (hmono hi).le
    · rw [Function.update_of_ne h]
  · rw [Function.update_self]; exact hmono hi

end PublicGood

/-! ## A concrete instance -/

/-- `φᵢ(q) = -aᵢ e^{-q}` with `a = (1, 3)` and `c(q) = e^q`. -/
noncomputable def pgEx : PublicGood (Fin 2) where
  φ i q := -(if i = 0 then 1 else 3) * Real.exp (-q)
  dφ i q := (if i = 0 then 1 else 3) * Real.exp (-q)
  c q := Real.exp q
  dc q := Real.exp q
  hφ i q := by
    have h := ((Real.hasDerivAt_exp (-q)).comp q (hasDerivAt_neg q)).const_mul
      (-(if i = 0 then (1 : ℝ) else 3))
    exact (h.congr_deriv (by ring) :
      HasDerivAt (fun q => -(if i = 0 then (1 : ℝ) else 3) * Real.exp (-q))
        ((if i = 0 then (1 : ℝ) else 3) * Real.exp (-q)) q)
  hc q := Real.hasDerivAt_exp q
  antiφ i a _ b _ hab := by
    have hk : (0 : ℝ) < if i = 0 then 1 else 3 := by split_ifs <;> norm_num
    have := Real.exp_lt_exp.2 (neg_lt_neg hab)
    exact mul_lt_mul_of_pos_left this hk
  monoc _ _ _ _ hab := Real.exp_lt_exp.2 hab

/-- In the instance, `q° = log 2`, Lindahl prices are `(1/2, 3/2)`, and private provision has
consumer 2 buying `q* = (log 3)/2 < q°` at price `√3`-equivalent `c'(q*)`. -/
theorem pgEx_values :
    pgEx.IsOptimal (Real.log 2) ∧ pgEx.IsLindahlEq ![1 / 2, 3 / 2] (fun _ => Real.log 2)
      (Real.log 2) ∧ pgEx.IsPrivateEq ![0, Real.log 3 / 2] (Real.exp (Real.log 3 / 2))
      (Real.log 3 / 2) ∧ Real.log 3 / 2 < Real.log 2 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have e2 : Real.exp (-Real.log 2) = 1 / 2 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  have ho : pgEx.IsOptimal (Real.log 2) := by
    rw [PublicGood.eq_11_C_1]
    simp only [pgEx, Fin.sum_univ_two, Fin.isValue, ↓reduceIte, one_ne_zero, e2,
      Real.exp_log (show (0 : ℝ) < 2 by norm_num)]
    refine ⟨hl2.le, by norm_num, fun _ => by norm_num⟩
  have hL := pgEx.lindahl_exists ho
  have hp : (fun i => pgEx.dφ i (Real.log 2)) = ![1 / 2, 3 / 2] := by
    ext i
    fin_cases i <;> norm_num [pgEx, e2]
  rw [hp] at hL
  have e3 : Real.exp (Real.log 3 / 2) * Real.exp (Real.log 3 / 2) = 3 := by
    rw [← Real.exp_add, add_halves, Real.exp_log (by norm_num)]
  have hpos3 : 0 < Real.exp (Real.log 3 / 2) := Real.exp_pos _
  have e3' : 3 * Real.exp (-(Real.log 3 / 2)) = Real.exp (Real.log 3 / 2) := by
    set a := Real.log 3 / 2
    rw [Real.exp_neg, ← e3, mul_inv_cancel_right₀ hpos3.ne']
  refine ⟨ho, hL, ?_, ?_⟩
  · rw [PublicGood.IsPrivateEq, PublicGood.subsidyEq_iff]
    refine ⟨fun i => ?_, ⟨by simp [pgEx], fun _ => by simp [pgEx]⟩, by simp⟩
    fin_cases i
    · simp only [pgEx, Fin.zero_eta, Fin.isValue, ↓reduceIte, one_mul, add_zero,
        Matrix.cons_val_zero, le_refl, lt_self_iff_false, IsEmpty.forall_iff, and_true,
        true_and]
      rw [Real.exp_le_exp]
      linarith
    · simp only [pgEx, Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte, add_zero,
        Matrix.cons_val_one, Matrix.cons_val_zero, e3', le_refl, implies_true, and_true]
      positivity
  · have : Real.log 3 < Real.log 4 := Real.log_lt_log (by norm_num) (by norm_num)
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    linarith

end MWG.ExternalitiesPublicGoods
