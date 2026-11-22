/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGClassicalDemand.FrobeniusIntegrability
import Mathlib.Analysis.Calculus.Deriv.Pi

/-!
# Solving (3.H.2) one price at a time

MWG, Section 3.H, p. 80 (small type): "once we know that `S(p, w)` is symmetric at all `(p, w)`,
we can in fact use (3.H.1) to solve (3.H.2) ... By changing prices one at a time, we can decompose
this problem into `L` subproblems where only one price changes at each step."

* Each subproblem is the scalar equation `e'(r) = x_l(p[l ↦ r], e(r))` along a coordinate line,
  with the other prices `p_k` (`k ≠ l`) fixed. It has a positive solution on all of `r > 0`
  through every initial condition, whether or not `S` is symmetric ("this method makes mechanical
  sense even if `S(p, w)` is not symmetric": `frob_line_exists`), and the solution is unique
  (`frob_line_unique`). Both use logarithmic coordinates, as for footnote 18.
* Along a coordinate line every solution `E` of (3.H.2) solves the subproblem
  (`frob_line_hasDerivAt`).
* Hence, if (3.H.2) has a solution `E` with `E(p⁰) = w⁰` (`frob_3_H_2_exists` when `S` is
  symmetric), raising the prices of goods `1, ..., L` in turn from `p⁰` to `p̄` and solving the
  subproblems gives exactly `E(p̄)` (`frob_one_price_at_a_time`); in particular the result does
  not depend on how the path is decomposed. When `S` is not symmetric no solution of (3.H.2)
  exists (`pde_slutsky_symmetric`), which is the book's "absurdity" remark.
-/

namespace MWG.ClassicalDemand

open MWG.ConsumerChoice Filter Topology

variable {L : ℕ}

/-- Changing one price of a strictly positive price vector to a positive value keeps it strictly
positive. -/
theorem frob_update_strictlyPositive {p : Fin L → ℝ} (hp : StrictlyPositive p) (l : Fin L)
    {r : ℝ} (hr : 0 < r) : StrictlyPositive (Function.update p l r) := fun j => by
  rw [Function.update_apply]
  split_ifs
  · exact hr
  · exact hp j

/-- Along a coordinate line, a solution of (3.H.2) solves the one-price equation
`e'(r) = x_l(p[l ↦ r], e(r))`. -/
theorem frob_line_hasDerivAt {x : DemandFunction L} {E : (Fin L → ℝ) → ℝ}
    (hE : SolvesPDE x E) {p : Fin L → ℝ} (hp : StrictlyPositive p) (l : Fin L) {r : ℝ}
    (hr : 0 < r) :
    HasDerivAt (fun s => E (Function.update p l s))
      (x (Function.update p l r) (E (Function.update p l r)) l) r := by
  have h := (hE _ (frob_update_strictlyPositive hp l hr)).comp_hasDerivAt r
    (hasDerivAt_update p l r)
  rwa [dualityDotCLM_apply, dotProduct_single, mul_one] at h

/-- The one-price equation in logarithmic coordinates `s = log r`, `ζ = log e`:
`ζ'(s) = r x_l(p[l ↦ r], e) / e`. -/
noncomputable def frobLineField (x : DemandFunction L) (p : Fin L → ℝ) (l : Fin L)
    (s ζ : ℝ) : ℝ :=
  Real.exp s * x (Function.update p l (Real.exp s)) (Real.exp ζ) l / Real.exp ζ

/-- The logarithmic one-price field is `C¹` on `ℝ²`. -/
theorem frobLineField_contDiff {x : DemandFunction L}
    (hx : ContDiffOn ℝ 1 (Function.uncurry x) (demandDomain L)) {p : Fin L → ℝ}
    (hp : StrictlyPositive p) (l : Fin L) :
    ContDiff ℝ 1 (fun z : ℝ × ℝ => frobLineField x p l z.1 z.2) := by
  have hg : ContDiff ℝ 1
      (fun z : ℝ × ℝ => (Function.update p l (Real.exp z.1), Real.exp z.2)) :=
    ((contDiff_update 1 p l).comp (Real.contDiff_exp.comp contDiff_fst)).prodMk
      (Real.contDiff_exp.comp contDiff_snd)
  have hc := hx.comp_contDiff hg fun z =>
    ⟨frob_update_strictlyPositive hp l (Real.exp_pos _), Real.exp_pos _⟩
  have h0 : ContDiff ℝ 1 (fun z : ℝ × ℝ =>
      x (Function.update p l (Real.exp z.1)) (Real.exp z.2) l) := contDiff_pi.mp hc l
  exact ((Real.contDiff_exp.comp contDiff_fst).mul h0).div
    (Real.contDiff_exp.comp contDiff_snd) fun z => (Real.exp_pos _).ne'

/-- By Walras' law and `x ≥ 0`, `0 ≤ r x_l / e ≤ 1`: the logarithmic one-price field is bounded
by `1`. -/
theorem frobLineField_abs_le {x : DemandFunction L} (hW : WalrasLaw x)
    (hnn : ∀ q w, StrictlyPositive q → 0 < w → x q w ∈ nonnegOrthant L) {p : Fin L → ℝ}
    (hp : StrictlyPositive p) (l : Fin L) (s ζ : ℝ) : |frobLineField x p l s ζ| ≤ 1 := by
  set P := Function.update p l (Real.exp s) with hPdef
  have hP := frob_update_strictlyPositive hp l (Real.exp_pos s)
  have hw := Real.exp_pos ζ
  have hwal := hW P (Real.exp ζ) ⟨hP, hw⟩
  have hn := hnn P (Real.exp ζ) hP hw
  have hPl : P l = Real.exp s := Function.update_self l _ p
  have hle : P l * x P (Real.exp ζ) l ≤ P ⬝ᵥ x P (Real.exp ζ) :=
    Finset.single_le_sum (f := fun j => P j * x P (Real.exp ζ) j)
      (fun j _ => mul_nonneg (hP j).le (hn j)) (Finset.mem_univ l)
  rw [hPl, hwal] at hle
  have h0 : 0 ≤ Real.exp s * x P (Real.exp ζ) l := mul_nonneg (Real.exp_pos s).le (hn l)
  unfold frobLineField
  rw [← hPdef, abs_le]
  constructor
  · have : 0 ≤ Real.exp s * x P (Real.exp ζ) l / Real.exp ζ := div_nonneg h0 hw.le
    linarith
  · rw [div_le_one hw]
    exact hle

/-- From the logarithmic equation back to the one-price equation: if `ζ' = V(s, ζ)` on `ℝ`, then
`e(r) = exp ζ(log r)` solves `e'(r) = x_l(p[l ↦ r], e(r))` at every `r > 0`. -/
theorem frob_line_lift {x : DemandFunction L} {p : Fin L → ℝ} {l : Fin L} {Z : ℝ → ℝ}
    (hZ : ∀ s, HasDerivAt Z (frobLineField x p l s (Z s)) s) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun t => Real.exp (Z (Real.log t)))
      (x (Function.update p l r) (Real.exp (Z (Real.log r))) l) r := by
  have h1 := (hZ (Real.log r)).comp r (Real.hasDerivAt_log hr.ne')
  have h2 := (Real.hasDerivAt_exp _).comp r h1
  refine h2.congr_deriv ?_
  unfold frobLineField
  rw [Real.exp_log hr]
  simp only [Function.comp_apply]
  field_simp

/-- From the one-price equation to the logarithmic equation: a positive solution `e` on `r > 0`
gives the solution `ζ(s) = log e(exp s)` on `ℝ`. -/
theorem frob_line_log {x : DemandFunction L} {p : Fin L → ℝ} {l : Fin L} {e : ℝ → ℝ}
    (hpos : ∀ r, 0 < r → 0 < e r)
    (he : ∀ r, 0 < r → HasDerivAt e (x (Function.update p l r) (e r) l) r) (s : ℝ) :
    HasDerivAt (fun t => Real.log (e (Real.exp t)))
      (frobLineField x p l s (Real.log (e (Real.exp s)))) s := by
  have hes := Real.exp_pos s
  have h1 := (he _ hes).comp s (Real.hasDerivAt_exp s)
  have h2 := h1.log (hpos _ hes).ne'
  refine h2.congr_deriv ?_
  unfold frobLineField
  rw [Real.exp_log (hpos _ hes)]
  simp only [Function.comp_apply]
  field_simp

/-- **Section 3.H** (MWG, p. 80, small type). Each one-price subproblem
`e'(r) = x_l(p[l ↦ r], e(r))` (the other prices `p ≫ 0` fixed) has a positive solution on all
of `r > 0` through every `(r₀, w₀)` with `w₀ > 0` (the book takes `r₀ > 0`; the statement
needs no condition on `r₀`). Symmetry of `S` is not needed. -/
theorem frob_line_exists {x : DemandFunction L} (hW : WalrasLaw x)
    (hnn : ∀ q w, StrictlyPositive q → 0 < w → x q w ∈ nonnegOrthant L)
    (hx : ContDiffOn ℝ 1 (Function.uncurry x) (demandDomain L)) {p : Fin L → ℝ}
    (hp : StrictlyPositive p) (l : Fin L) (r₀ : ℝ) {w₀ : ℝ} (hw₀ : 0 < w₀) :
    ∃ e : ℝ → ℝ, e r₀ = w₀ ∧ ∀ r, 0 < r → 0 < e r ∧
      HasDerivAt e (x (Function.update p l r) (e r) l) r := by
  obtain ⟨Z, hZ0, hZ⟩ := hardInt_exists_global (frobLineField_contDiff hx hp l)
    (frobLineField_abs_le hW hnn hp l) (Real.log r₀) (Real.log w₀)
  refine ⟨fun t => Real.exp (Z (Real.log t)), by simp only [hZ0, Real.exp_log hw₀],
    fun r hr => ⟨Real.exp_pos _, frob_line_lift hZ hr⟩⟩

/-- **Section 3.H** (MWG, p. 80, small type). Uniqueness for each one-price subproblem: two
positive solutions on `r > 0` that agree at one `r₀ > 0` agree at every `r > 0`. -/
theorem frob_line_unique {x : DemandFunction L}
    (hx : ContDiffOn ℝ 1 (Function.uncurry x) (demandDomain L)) {p : Fin L → ℝ}
    (hp : StrictlyPositive p) (l : Fin L) {e₁ e₂ : ℝ → ℝ}
    (hpos₁ : ∀ r, 0 < r → 0 < e₁ r) (hpos₂ : ∀ r, 0 < r → 0 < e₂ r)
    (h₁ : ∀ r, 0 < r → HasDerivAt e₁ (x (Function.update p l r) (e₁ r) l) r)
    (h₂ : ∀ r, 0 < r → HasDerivAt e₂ (x (Function.update p l r) (e₂ r) l) r) {r₀ : ℝ}
    (hr₀ : 0 < r₀) (h0 : e₁ r₀ = e₂ r₀) {r : ℝ} (hr : 0 < r) : e₁ r = e₂ r := by
  have hu := hardInt_unique (frobLineField_contDiff hx hp l) (t₀ := Real.log r₀)
    (frob_line_log hpos₁ h₁) (frob_line_log hpos₂ h₂) (by simp only [Real.exp_log hr₀, h0])
  have := congrFun hu (Real.log r)
  simp only [Real.exp_log hr] at this
  exact Real.log_injOn_pos (hpos₁ r hr) (hpos₂ r hr) this

/-- The `k`-th intermediate price vector of the one-price-at-a-time path from `p⁰` to `p̄`: goods
with index `< k` have reached `p̄`, the others are still at `p⁰`. -/
def frobOnePricePath (p₀ p₁ : Fin L → ℝ) (k : ℕ) : Fin L → ℝ :=
  fun j => if (j : ℕ) < k then p₁ j else p₀ j

/-- The intermediate price vectors are strictly positive. -/
theorem frobOnePricePath_pos {p₀ p₁ : Fin L → ℝ} (h₀ : StrictlyPositive p₀)
    (h₁ : StrictlyPositive p₁) (k : ℕ) : StrictlyPositive (frobOnePricePath p₀ p₁ k) :=
  fun j => by
    unfold frobOnePricePath
    split_ifs
    · exact h₁ j
    · exact h₀ j

/-- The path starts at `p⁰`. -/
theorem frobOnePricePath_zero (p₀ p₁ : Fin L → ℝ) : frobOnePricePath p₀ p₁ 0 = p₀ := by
  funext j
  simp [frobOnePricePath]

/-- The path ends at `p̄`. -/
theorem frobOnePricePath_last (p₀ p₁ : Fin L → ℝ) : frobOnePricePath p₀ p₁ L = p₁ := by
  funext j
  simp [frobOnePricePath, j.isLt]

/-- At step `k` only the price of good `k` changes: `path k` with good `k` at `p⁰_k` is
`path k`. -/
theorem frobOnePricePath_update_start (p₀ p₁ : Fin L → ℝ) {k : ℕ} (hk : k < L) :
    Function.update (frobOnePricePath p₀ p₁ k) ⟨k, hk⟩ (p₀ ⟨k, hk⟩) =
      frobOnePricePath p₀ p₁ k := by
  funext j
  rw [Function.update_apply]
  split_ifs with h
  · subst h
    simp [frobOnePricePath]
  · rfl

/-- At step `k`, raising good `k` to `p̄_k` gives `path (k + 1)`. -/
theorem frobOnePricePath_update_end (p₀ p₁ : Fin L → ℝ) {k : ℕ} (hk : k < L) :
    Function.update (frobOnePricePath p₀ p₁ k) ⟨k, hk⟩ (p₁ ⟨k, hk⟩) =
      frobOnePricePath p₀ p₁ (k + 1) := by
  funext j
  rw [Function.update_apply]
  split_ifs with h
  · subst h
    simp [frobOnePricePath]
  · have h' : (j : ℕ) ≠ k := fun h'' => h (Fin.ext h'')
    simp only [frobOnePricePath]
    by_cases hj : (j : ℕ) < k
    · simp [hj, Nat.lt_succ_of_lt hj]
    · have : ¬ (j : ℕ) < k + 1 := by omega
      simp [hj, this]

/-- **Section 3.H** (MWG, p. 80, small type): solving (3.H.2) one price at a time. Let `E` be
a positive solution of (3.H.2) on `p ≫ 0` with `E(p⁰) = w⁰`, and let `x` be `C¹`. Raise the
prices of goods `0, 1, ..., L - 1` in turn from `p⁰` to `p̄ ≫ 0`: at step `k`, `e_k` is a positive
solution of `e'(r) = x_k(path_k[k ↦ r], e(r))` on `r > 0` starting from the value `c_k` reached
so far (`e_k(p⁰_k) = c_k`, `c_0 = w⁰`, `c_{k+1} = e_k(p̄_k)`). Then the final value is
`c_L = E(p̄)`: the construction recovers the solution of (3.H.2). -/
theorem frob_one_price_at_a_time {x : DemandFunction L}
    (hx : ContDiffOn ℝ 1 (Function.uncurry x) (demandDomain L)) {E : (Fin L → ℝ) → ℝ}
    (hE : SolvesPDE x E) (hEpos : ∀ q, StrictlyPositive q → 0 < E q) {p₀ p₁ : Fin L → ℝ}
    (h₀ : StrictlyPositive p₀) (h₁ : StrictlyPositive p₁) {w₀ : ℝ} (hEw : E p₀ = w₀)
    {c : ℕ → ℝ} {e : ℕ → ℝ → ℝ} (hc0 : c 0 = w₀)
    (hpos : ∀ k, k < L → ∀ r, 0 < r → 0 < e k r)
    (hode : ∀ k (hk : k < L), ∀ r, 0 < r → HasDerivAt (e k)
      (x (Function.update (frobOnePricePath p₀ p₁ k) ⟨k, hk⟩ r) (e k r) ⟨k, hk⟩) r)
    (hstart : ∀ k (hk : k < L), e k (p₀ ⟨k, hk⟩) = c k)
    (hstep : ∀ k (hk : k < L), c (k + 1) = e k (p₁ ⟨k, hk⟩)) :
    c L = E p₁ := by
  have key : ∀ k, k ≤ L → c k = E (frobOnePricePath p₀ p₁ k) := by
    intro k
    induction k with
    | zero => intro _; rw [frobOnePricePath_zero, hc0, hEw]
    | succ k ih =>
      intro hk
      have hkL : k < L := hk
      have hpath := frobOnePricePath_pos h₀ h₁ k
      have hEline : ∀ r, 0 < r → HasDerivAt (fun s => E (Function.update
          (frobOnePricePath p₀ p₁ k) ⟨k, hkL⟩ s))
          (x (Function.update (frobOnePricePath p₀ p₁ k) ⟨k, hkL⟩ r)
            (E (Function.update (frobOnePricePath p₀ p₁ k) ⟨k, hkL⟩ r)) ⟨k, hkL⟩) r :=
        fun r hr => frob_line_hasDerivAt hE hpath _ hr
      have hu := frob_line_unique hx hpath ⟨k, hkL⟩ (hpos k hkL)
        (fun r hr => hEpos _ (frob_update_strictlyPositive hpath _ hr)) (hode k hkL) hEline
        (h₀ ⟨k, hkL⟩)
        (by rw [hstart k hkL, frobOnePricePath_update_start p₀ p₁ hkL, ih hkL.le])
        (h₁ ⟨k, hkL⟩)
      rw [hstep k hkL, hu, frobOnePricePath_update_end p₀ p₁ hkL]
  rw [key L le_rfl, frobOnePricePath_last]

/-- **Section 3.H** (MWG, p. 80, small type), from primitive hypotheses. If `x` is `C¹`,
nonnegative, satisfies Walras' law and has a symmetric Slutsky matrix, then for every
`(p⁰, w⁰) ≫ 0` there is a solution `E` of (3.H.2) with `E(p⁰) = w⁰`, and the one-price-at-a-time
construction from `p⁰` to any `p̄ ≫ 0` ends at `E(p̄)`, whatever solutions of the subproblems
are used. -/
theorem frob_one_price_at_a_time_exists {x : DemandFunction L} (hW : WalrasLaw x)
    (hnn : ∀ q w, StrictlyPositive q → 0 < w → x q w ∈ nonnegOrthant L)
    (hx : ContDiffOn ℝ 1 (Function.uncurry x) (demandDomain L))
    (hS : ∀ p w, StrictlyPositive p → 0 < w → ∀ i j,
      slutskyMatrix (fderiv ℝ (Function.uncurry x) (p, w)) (x p w) i j =
        slutskyMatrix (fderiv ℝ (Function.uncurry x) (p, w)) (x p w) j i)
    {p₀ : Fin L → ℝ} (h₀ : StrictlyPositive p₀) {w₀ : ℝ} (hw₀ : 0 < w₀) :
    ∃ E : (Fin L → ℝ) → ℝ, E p₀ = w₀ ∧ SolvesPDE x E ∧
      ∀ p₁ : Fin L → ℝ, StrictlyPositive p₁ → ∀ (c : ℕ → ℝ) (e : ℕ → ℝ → ℝ), c 0 = w₀ →
        (∀ k, k < L → ∀ r, 0 < r → 0 < e k r) →
        (∀ k (hk : k < L), ∀ r, 0 < r → HasDerivAt (e k)
          (x (Function.update (frobOnePricePath p₀ p₁ k) ⟨k, hk⟩ r) (e k r) ⟨k, hk⟩) r) →
        (∀ k (hk : k < L), e k (p₀ ⟨k, hk⟩) = c k) →
        (∀ k (hk : k < L), c (k + 1) = e k (p₁ ⟨k, hk⟩)) → c L = E p₁ := by
  obtain ⟨E, hE0, hpos, hE⟩ := frob_3_H_2_exists hW hnn hx hS p₀ hw₀
  exact ⟨E, hE0, hE, fun p₁ h₁ c e hc0 hp hode hst hstep =>
    frob_one_price_at_a_time hx hE (fun q _ => hpos q) h₀ h₁ hE0 hc0 hp hode hst hstep⟩

end MWG.ClassicalDemand
