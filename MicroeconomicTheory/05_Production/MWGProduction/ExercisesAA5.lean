/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGProduction.ExercisesAA

/-!
# Exercise 5.AA.5 (MWG, pp. 165-166)

Eight elementary activities in `ℝ⁴`, `Y = {Σ_m α_m a_m : α ≥ 0}` (no disposal activities).

* (a) `Y` is a convex cone; (b) no free lunch, via `p = (2, 2, 2, 1)`; (c) no free disposal, and
  adding the disposal activities restores it (`freeDisposal_withDisposal`).
* (d) by direct comparison `a₄ ≤ a₂`, `a₅ ≤ 3a₁`, `a₆ ≤ a₇/2` are inefficient; correction: the
  comparison of `a₃` with `a₈` shows nothing, both are efficient (`exercise_5_AA_5d_correction`).
* (e) `a₁ ≤ (4/3)a₃ + (2/15)a₇` and `a₂ ≤ a₃ + (3/10)a₇`.
* (f) the efficient set is `cone(a₃, a₈) ∪ cone(a₇, a₈)` (`exercise_5_AA_5f`).
* (g)-(h) maximizing net output of good 3 with resources `(480, 300, 0, 0)` is a linear program
  with value `412.5`, attained at `75a₃ + 37.5a₈` (`exercise_5_AA_5gh`).
-/

namespace MWG.Production

open MWG.ClassicalDemand MWG.ConsumerChoice Filter Topology

/-- The eight activities of Exercise 5.AA.5. -/
def aa5 : Fin 8 → Fin 4 → ℝ :=
  ![![-3, -6, 4, 0], ![-7, -9, 3, 2], ![-1, -2, 3, -1], ![-8, -13, 3, 1],
    ![-11, -19, 12, 0], ![-4, -3, -2, 5], ![-8, -5, 0, 10], ![-2, -4, 5, 2]]

/-- Adding the disposal activities gives free disposal. -/
theorem freeDisposal_withDisposal {L M : ℕ} (a : Fin M → Fin L → ℝ) :
    FreeDisposal (coneOf (withDisposal a)) := by
  rintro _ ⟨lam, hlam, rfl⟩ y' hy'
  set d := ∑ j, lam j • withDisposal a j - y' with hd
  set E : Fin M ⊕ Fin L → ℝ := Sum.elim (0 : Fin M → ℝ) d with hE
  refine ⟨lam + E, add_nonneg hlam (fun j => ?_), ?_⟩
  · rcases j with j | j
    · exact le_rfl
    · exact sub_nonneg.mpr hy' j
  · have hEs : ∑ j, E j • withDisposal a j = -d := by
      rw [Fintype.sum_sum_type]
      funext i
      simp [hE, withDisposal, Finset.sum_apply, Pi.single_apply]
    have hsplit : ∑ j, (lam + E) j • withDisposal a j =
        ∑ j, lam j • withDisposal a j + ∑ j, E j • withDisposal a j := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by rw [Pi.add_apply, add_smul]
    rw [hsplit, hEs, hd]
    abel

theorem aa5_dot (p : Fin 4 → ℝ) (m : Fin 8) :
    p ⬝ᵥ aa5 m = p 0 * aa5 m 0 + p 1 * aa5 m 1 + p 2 * aa5 m 2 + p 3 * aa5 m 3 := by
  simp [dotProduct, Fin.sum_univ_four]

/-- **Exercise 5.AA.5(a)-(c)** (MWG, p. 166). `Y` is convex (a convex cone); it has no free lunch
(`p = (2, 2, 2, 1) ≫ 0` makes every activity unprofitable); it does not have free disposal
(`(-1, 0, 0, 0) ∉ Y`, since every activity uses good 2); with the four disposal activities added
it does. -/
theorem exercise_5_AA_5abc :
    Convex ℝ (coneOf aa5) ∧ NoFreeLunch (coneOf aa5) ∧ ¬ FreeDisposal (coneOf aa5) ∧
      FreeDisposal (coneOf (withDisposal aa5)) := by
  have hp : ∀ m, (![2, 2, 2, 1] : Fin 4 → ℝ) ⬝ᵥ aa5 m ≤ 0 := by
    intro m; rw [aa5_dot]; fin_cases m <;> simp [aa5] <;> norm_num
  refine ⟨convex_coneOf aa5, ?_, ?_, freeDisposal_withDisposal aa5⟩
  · rintro _ ⟨lam, hlam, rfl⟩ h0
    have hle : (![2, 2, 2, 1] : Fin 4 → ℝ) ⬝ᵥ ∑ m, lam m • aa5 m ≤ 0 := by
      rw [activity_profit]
      exact Finset.sum_nonpos fun m _ => mul_nonpos_of_nonneg_of_nonpos (hlam m) (hp m)
    set y := ∑ m, lam m • aa5 m
    have hy0 : 0 ≤ y 0 := h0 0
    have hy1 : 0 ≤ y 1 := h0 1
    have hy2 : 0 ≤ y 2 := h0 2
    have hy3 : 0 ≤ y 3 := h0 3
    simp [dotProduct, Fin.sum_univ_four] at hle
    have e0 : y 0 = 0 := by linarith
    have e1 : y 1 = 0 := by linarith
    have e2 : y 2 = 0 := by linarith
    have e3 : y 3 = 0 := by linarith
    funext i
    fin_cases i
    exacts [e0, e1, e2, e3]
  · intro h
    obtain ⟨lam, hlam, hy⟩ := h 0 (zero_mem_coneOf aa5) ![-1, 0, 0, 0]
      (fun i => by fin_cases i <;> simp)
    have h0 := congrFun hy 0
    have h1 := congrFun hy 1
    simp [Finset.sum_apply, Fin.sum_univ_eight, aa5] at h0 h1
    have := hlam 0; have := hlam 1; have := hlam 2; have := hlam 3
    have := hlam 4; have := hlam 5; have := hlam 6; have := hlam 7
    simp only [Pi.zero_apply] at *
    linarith

/-- **Exercise 5.AA.5(d)** (MWG, p. 166). By direct comparison `a₄ ≤ a₂`, `a₅ ≤ 3a₁` and
`a₆ ≤ (1/2)a₇` (with strict inequalities somewhere), so `a₄`, `a₅`, `a₆` are not efficient. -/
theorem exercise_5_AA_5d :
    ¬ Efficient (coneOf aa5) (aa5 3) ∧ ¬ Efficient (coneOf aa5) (aa5 4) ∧
      ¬ Efficient (coneOf aa5) (aa5 5) := by
  have hg : ∀ m, aa5 m ∈ coneOf aa5 := generator_mem_coneOf aa5
  refine ⟨fun h => h.2 ⟨aa5 1, hg 1, fun i => ?_, fun he => ?_⟩,
    fun h => h.2 ⟨(3 : ℝ) • aa5 0, smul_mem_coneOf (hg 0) (by norm_num), fun i => ?_, fun he => ?_⟩,
    fun h => h.2 ⟨(1 / 2 : ℝ) • aa5 6, smul_mem_coneOf (hg 6) (by norm_num), fun i => ?_,
      fun he => ?_⟩⟩
  all_goals first
    | (fin_cases i <;> simp [aa5] <;> norm_num)
    | (have := congrFun he 1; norm_num [aa5] at this)

/-- **Exercise 5.AA.5(d)**, correction (MWG, p. 166): the "direct comparison of `a₃` with `a₈`"
proves nothing; both are efficient, being profit maximizing at `p = (30, 30, 31, 3) ≫ 0` and
`p = (2, 2, 2, 1) ≫ 0` respectively. -/
theorem exercise_5_AA_5d_correction :
    Efficient (coneOf aa5) (aa5 2) ∧ Efficient (coneOf aa5) (aa5 7) := by
  constructor
  · have hp : ∀ m, (![30, 30, 31, 3] : Fin 4 → ℝ) ⬝ᵥ aa5 m ≤ 0 := by
      intro m; rw [aa5_dot]; fin_cases m <;> simp [aa5] <;> norm_num
    refine proposition_5_F_1 (p := ![30, 30, 31, 3]) (fun i => by fin_cases i <;> simp) ?_
    rw [activity_supply_eq hp]
    refine ⟨Pi.single 2 1, Pi.single_nonneg.mpr zero_le_one, fun m hm => ?_, ?_⟩
    · by_contra h
      have : m = 2 := by by_contra hm2; simp [hm2] at h
      subst this; rw [aa5_dot] at hm; simp [aa5] at hm; norm_num at hm
    · rw [Finset.sum_eq_single 2 (fun j _ hj => by simp [hj]) (by simp)]; simp
  · have hp : ∀ m, (![2, 2, 2, 1] : Fin 4 → ℝ) ⬝ᵥ aa5 m ≤ 0 := by
      intro m; rw [aa5_dot]; fin_cases m <;> simp [aa5] <;> norm_num
    refine proposition_5_F_1 (p := ![2, 2, 2, 1]) (fun i => by fin_cases i <;> simp) ?_
    rw [activity_supply_eq hp]
    refine ⟨Pi.single 7 1, Pi.single_nonneg.mpr zero_le_one, fun m hm => ?_, ?_⟩
    · by_contra h
      have : m = 7 := by by_contra hm2; simp [hm2] at h
      subst this; rw [aa5_dot] at hm; simp [aa5] at hm; norm_num at hm
    · rw [Finset.sum_eq_single 7 (fun j _ hj => by simp [hj]) (by simp)]; simp

/-- **Exercise 5.AA.5(e)** (MWG, p. 166). `a₁ ≤ (4/3)a₃ + (2/15)a₇` and `a₂ ≤ a₃ + (3/10)a₇`, with
strict inequality somewhere: `a₁` and `a₂` are not efficient. -/
theorem exercise_5_AA_5e :
    ¬ Efficient (coneOf aa5) (aa5 0) ∧ ¬ Efficient (coneOf aa5) (aa5 1) := by
  have hg : ∀ m, aa5 m ∈ coneOf aa5 := generator_mem_coneOf aa5
  constructor
  · intro h
    apply h.2 ⟨(4 / 3 : ℝ) • aa5 2 + (2 / 15 : ℝ) • aa5 6,
      add_mem_coneOf (smul_mem_coneOf (hg 2) (by norm_num)) (smul_mem_coneOf (hg 6) (by norm_num)),
      fun i => ?_, fun he => ?_⟩
    · fin_cases i <;> simp [aa5] <;> norm_num
    · have := congrFun he 0; simp [aa5] at this; norm_num at this
  · intro h
    apply h.2 ⟨aa5 2 + (3 / 10 : ℝ) • aa5 6,
      add_mem_coneOf (hg 2) (smul_mem_coneOf (hg 6) (by norm_num)), fun i => ?_, fun he => ?_⟩
    · fin_cases i <;> simp [aa5] <;> norm_num
    · have := congrFun he 0; simp [aa5] at this; norm_num at this

theorem aa5_mem_supply_of_price {p y : Fin 4 → ℝ} (hp : ∀ m, p ⬝ᵥ aa5 m ≤ 0)
    (hy : y ∈ coneOf aa5) (hpy : p ⬝ᵥ y = 0) : y ∈ supply (coneOf aa5) p := by
  refine ⟨hy, ?_⟩
  rintro _ ⟨lam, hlam, rfl⟩
  rw [activity_profit, hpy]
  exact Finset.sum_nonpos fun m _ => mul_nonpos_of_nonneg_of_nonpos (hlam m) (hp m)

theorem aa5_two_mem {i j : Fin 8} {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    s • aa5 i + t • aa5 j ∈ coneOf aa5 :=
  add_mem_coneOf (smul_mem_coneOf (generator_mem_coneOf aa5 i) hs)
    (smul_mem_coneOf (generator_mem_coneOf aa5 j) ht)

/-- **Exercise 5.AA.5(f)** (MWG, p. 166). The efficient production vectors are exactly the
nonnegative combinations of `a₃` and `a₈` or of `a₇` and `a₈`:
`cone(a₃, a₈) ∪ cone(a₇, a₈)`. -/
theorem exercise_5_AA_5f (y : Fin 4 → ℝ) :
    Efficient (coneOf aa5) y ↔
      (∃ s t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧ y = s • aa5 2 + t • aa5 7) ∨
        (∃ s t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧ y = s • aa5 6 + t • aa5 7) := by
  constructor
  · intro hy
    obtain ⟨p, hp, hsup⟩ := linear_activity_efficient_pos_price aa5 hy
    have hpa := (activity_supply_nonempty_iff aa5 p).mp ⟨y, hsup⟩
    obtain ⟨lam, hlam, hz, rfl⟩ := (activity_supply_eq hpa y).mp hsup
    have p0 := hp 0; have p1 := hp 1; have p2 := hp 2; have p3 := hp 3
    have hd : ∀ m, p ⬝ᵥ aa5 m = p 0 * aa5 m 0 + p 1 * aa5 m 1 + p 2 * aa5 m 2 + p 3 * aa5 m 3 :=
      aa5_dot p
    have q : ∀ m, p ⬝ᵥ aa5 m ≤ 0 := hpa
    have e : ∀ m, m ≠ 2 → m ≠ 6 → m ≠ 7 → lam m = 0 := by
      intro m h2 h6 h7
      apply hz m
      have q0 := q 0; have q1 := q 1; have q2 := q 2; have q6 := q 6
      rw [hd] at q0 q1 q2 q6 ⊢
      fin_cases m <;> simp [aa5] at h2 h6 h7 q0 q1 q2 q6 ⊢ <;> linarith
    have hnot : ¬ (p ⬝ᵥ aa5 2 = 0 ∧ p ⬝ᵥ aa5 6 = 0) := by
      rintro ⟨h2, h6⟩
      have q7 := q 7
      rw [hd] at h2 h6 q7
      simp [aa5] at h2 h6 q7
      linarith
    have hsum : ∑ m, lam m • aa5 m = lam 2 • aa5 2 + lam 6 • aa5 6 + lam 7 • aa5 7 := by
      rw [Fin.sum_univ_eight, e 0 (by decide) (by decide) (by decide),
        e 1 (by decide) (by decide) (by decide), e 3 (by decide) (by decide) (by decide),
        e 4 (by decide) (by decide) (by decide), e 5 (by decide) (by decide) (by decide)]
      simp only [zero_smul, zero_add, add_zero]
    rw [hsum]
    by_cases h2 : p ⬝ᵥ aa5 2 = 0
    · have h6 : lam 6 = 0 := hz 6 fun h => hnot ⟨h2, h⟩
      exact Or.inl ⟨lam 2, lam 7, hlam 2, hlam 7, by rw [h6, zero_smul, add_zero]⟩
    · have h2' : lam 2 = 0 := hz 2 h2
      exact Or.inr ⟨lam 6, lam 7, hlam 6, hlam 7, by rw [h2', zero_smul, zero_add]⟩
  · rintro (⟨s, t, hs, ht, rfl⟩ | ⟨s, t, hs, ht, rfl⟩)
    · have hp : ∀ m, (![1, 5, 4, 1] : Fin 4 → ℝ) ⬝ᵥ aa5 m ≤ 0 := by
        intro m; rw [aa5_dot]; fin_cases m <;> simp [aa5] <;> norm_num
      refine proposition_5_F_1 (p := ![1, 5, 4, 1]) (fun i => by fin_cases i <;> simp)
        (aa5_mem_supply_of_price hp (aa5_two_mem hs ht) ?_)
      rw [dotProduct_add, dotProduct_smul, dotProduct_smul, aa5_dot, aa5_dot]
      simp [aa5]; norm_num
    · have hp : ∀ m, (![25, 60, 38, 50] : Fin 4 → ℝ) ⬝ᵥ aa5 m ≤ 0 := by
        intro m; rw [aa5_dot]; fin_cases m <;> simp [aa5] <;> norm_num
      refine proposition_5_F_1 (p := ![25, 60, 38, 50]) (fun i => by fin_cases i <;> simp)
        (aa5_mem_supply_of_price hp (aa5_two_mem hs ht) ?_)
      rw [dotProduct_add, dotProduct_smul, dotProduct_smul, aa5_dot, aa5_dot]
      simp [aa5]; norm_num

open Matrix in
/-- **Exercise 5.AA.5(g)-(h)** (MWG, p. 166). With resources `s = (480, 300, 0, 0)`, maximizing the
net production of good 3 is the linear program `max Σ_m α_m a_{3m}` s.t. `-Σ_m α_m a_{ℓm} ≤ s_ℓ`,
`α ≥ 0`. Its value is `412.5`, attained by `75a₃ + 37.5a₈`; the dual solution
`λ = (0, 11/8, 0, 1/4)` (shadow prices of the resources) certifies optimality. -/
theorem exercise_5_AA_5gh :
    let B : Matrix (Fin 4) (Fin 8) ℝ := fun l m => -aa5 m l
    let f : Fin 8 → ℝ := fun m => aa5 m 2
    let s : Fin 4 → ℝ := ![480, 300, 0, 0]
    let α : Fin 8 → ℝ := ![0, 0, 75, 0, 0, 0, 0, 75 / 2]
    α ∈ primalFeasible B s ∧ f ⬝ᵥ α = 825 / 2 ∧
      ![0, 11 / 8, 0, 1 / 4] ∈ dualFeasible B f ∧ s ⬝ᵥ ![0, 11 / 8, 0, 1 / 4] = 825 / 2 ∧
      ∀ α' ∈ primalFeasible B s, f ⬝ᵥ α' ≤ f ⬝ᵥ α := by
  intro B f s α
  have hα : α ∈ primalFeasible B s := by
    refine ⟨fun m => by fin_cases m <;> norm_num [α], fun l => ?_⟩
    fin_cases l <;> simp [B, s, α, aa5, Matrix.mulVec, dotProduct, Fin.sum_univ_eight] <;>
      norm_num
  have hval : f ⬝ᵥ α = 825 / 2 := by
    simp [f, α, aa5, dotProduct, Fin.sum_univ_eight]; norm_num
  have hlam : (![0, 11 / 8, 0, 1 / 4] : Fin 4 → ℝ) ∈ dualFeasible B f := by
    refine ⟨fun l => by fin_cases l <;> norm_num, fun m => ?_⟩
    have hcomp : (Bᵀ *ᵥ (![0, 11 / 8, 0, 1 / 4] : Fin 4 → ℝ)) m =
        -(11 / 8) * aa5 m 1 - (1 / 4) * aa5 m 3 := by
      have hT : ∀ i j, Bᵀ i j = -aa5 i j := fun i j => rfl
      simp only [Matrix.mulVec, dotProduct, hT, Fin.sum_univ_four]
      simp
      ring
    rw [hcomp]
    fin_cases m <;> simp [f, aa5] <;> norm_num
  have hdual : s ⬝ᵥ ![0, 11 / 8, 0, 1 / 4] = 825 / 2 := by
    simp [s, dotProduct, Fin.sum_univ_four]; norm_num
  refine ⟨hα, hval, hlam, hdual, fun α' hα' => ?_⟩
  rw [hval, ← hdual]
  exact equation_M_M_3 hα' hlam

end MWG.Production
