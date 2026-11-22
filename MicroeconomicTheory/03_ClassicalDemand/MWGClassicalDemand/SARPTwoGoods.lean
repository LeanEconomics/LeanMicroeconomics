/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGClassicalDemand.SARPBasic
import MWGConsumerChoice.SlutskyExamples
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The weak and strong axioms with two goods

MWG, Section 3.J, p. 92, and Exercise 3.J.1, p. 104.

* Minimal revealed-preference cycles: a cycle `a ≻¹ ⋯ ≻¹ a` of least length has distinct
  bundles and no chords (`sarp_exists_minimal_relCycle`).
* **Exercise 3.J.1**: with `L = 2` and Walras' law, the weak axiom implies the strong axiom
  (Rose's theorem). In a minimal cycle every bundle `x^{k+1}` minimises the expenditure
  `p^k·y` over the cycle and `x^k` is the unique minimiser of the others, so the bundles are
  pairwise unordered and, sorted by their first coordinate, consecutive bundles of the cycle
  are adjacent. A cycle of length at least three cannot visit the leftmost bundle from and to
  two different neighbours, and length two is excluded by the weak axiom
  (`strongAxiom_of_weakAxiom_two`, `exercise_3_J_1`).
* The consequence stated on p. 92: with `L = 2` and the weak axiom, demand is rationalizable
  (`weakAxiom_rationalizable_two`).
* "When `L > 2`, the SA is stronger than the WA" (p. 92): the demand of Exercise 2.F.15
  (consumption set `ℝ³`) satisfies Walras' law and the weak axiom but has an explicit
  seven-bundle revealed-preference cycle (`strongAxiom_stronger_three`).

Walras' law is the standing assumption on Walrasian demand of Section 2.F, under which the
weak axiom is studied; Exercise 3.J.1 is proved under it.
-/

namespace MWG.ClassicalDemand

open MWG.ConsumerChoice Kreps.PreferenceProperties

variable {X : Type*}

/-- A cycle of length `n`: a sequence with `R (g k) (g (k + 1))` for all `k` and period `n`. -/
def SarpRelCycle (R : X → X → Prop) (n : ℕ) (g : ℕ → X) : Prop :=
  (∀ k, R (g k) (g (k + 1))) ∧ ∀ k, g (k + n) = g k

/-- The successor of a residue modulo `n`. -/
theorem sarp_succ_mod_cases (k n : ℕ) (hn : 0 < n) :
    (k % n + 1 < n ∧ (k + 1) % n = k % n + 1) ∨ (k % n + 1 = n ∧ (k + 1) % n = 0) := by
  have h1 := Nat.mod_lt k hn
  have h2 := Nat.mod_add_div k n
  by_cases h : k % n + 1 < n
  · left
    refine ⟨h, ?_⟩
    have e : k + 1 = (k % n + 1) + n * (k / n) := by omega
    rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h]
  · right
    have h3 : k % n + 1 = n := by omega
    refine ⟨h3, ?_⟩
    have e : k + 1 = n * (k / n + 1) := by rw [Nat.mul_add, mul_one]; omega
    rw [e, Nat.mul_mod_right]

/-- A cycle of a relation is periodic: `g (a + n q) = g a`. -/
theorem SarpRelCycle.periodic {R : X → X → Prop} {n : ℕ} {g : ℕ → X} (hg : SarpRelCycle R n g)
    (a q : ℕ) : g (a + n * q) = g a := by
  induction q with
  | zero => simp
  | succ q ih => rw [Nat.mul_succ, ← add_assoc, hg.2, ih]

/-- A transitive-closure loop `a ≻ ⋯ ≻ a` gives a periodic cycle through `a`. -/
theorem sarp_relCycle_of_transGen {R : X → X → Prop} {a : X} (h : Relation.TransGen R a a) :
    ∃ n, 1 ≤ n ∧ ∃ g, SarpRelCycle R n g ∧ g 0 = a := by
  obtain ⟨N, hN, g, h0, hN', hstep⟩ := sarp_transGen_iff_chain.mp h
  refine ⟨N, hN, fun k => g (k % N), ⟨fun k => ?_, fun k => ?_⟩, by simpa using h0⟩
  · change R (g (k % N)) (g ((k + 1) % N))
    rcases sarp_succ_mod_cases k N hN with ⟨hlt, he⟩ | ⟨heq, he⟩
    · rw [he]
      exact hstep _ (Nat.mod_lt k hN)
    · rw [he]
      have := hstep (k % N) (Nat.mod_lt k hN)
      rw [heq, hN', ← h0] at this
      exact this
  · simp

/-- Shortcutting a cycle: a step from `g (s + m - 1)` back to `g s` closes a cycle of length
`m` through `g s, ..., g (s + m - 1)`. -/
theorem SarpRelCycle.shortcut {R : X → X → Prop} {n : ℕ} {g : ℕ → X} (hg : SarpRelCycle R n g)
    {s m : ℕ} (hm : 1 ≤ m) (hR : R (g (s + m - 1)) (g s)) :
    SarpRelCycle R m (fun k => g (s + k % m)) := by
  refine ⟨fun k => ?_, fun k => by simp⟩
  rcases sarp_succ_mod_cases k m hm with ⟨_, he⟩ | ⟨heq, he⟩
  · simp only
    rw [he, ← add_assoc]
    exact hg.1 _
  · simp only
    rw [he, add_zero]
    have e : s + k % m = s + m - 1 := by omega
    rw [e]
    exact hR

/-- **Exercise 3.J.1**, combinatorial step. If some loop exists for a relation,
there is a cycle of least length `n ≥ 1`; its bundles `g 0, ..., g (n - 1)` are distinct and it
has no chords: `R (g i) (g j)` only for `j` the successor of `i`. -/
theorem sarp_exists_minimal_relCycle {R : X → X → Prop}
    (hex : ∃ a, Relation.TransGen R a a) :
    ∃ n, 1 ≤ n ∧ ∃ g, SarpRelCycle R n g ∧
      (∀ i j, i < n → j < n → R (g i) (g j) → j = i + 1 ∨ (i + 1 = n ∧ j = 0)) ∧
      (∀ i j, i < n → j < n → g i = g j → i = j) := by
  classical
  have hP : ∃ n, 1 ≤ n ∧ ∃ g, SarpRelCycle R n g := by
    obtain ⟨a, ha⟩ := hex
    obtain ⟨n, hn, g, hg, -⟩ := sarp_relCycle_of_transGen ha
    exact ⟨n, hn, g, hg⟩
  obtain ⟨hn1, g, hg⟩ := Nat.find_spec hP
  have hmin : ∀ m, m < Nat.find hP → 1 ≤ m → ∀ g' : ℕ → X, ¬SarpRelCycle R m g' :=
    fun m hm h1 g' hg' => Nat.find_min hP hm ⟨h1, g', hg'⟩
  set n := Nat.find hP
  have hinj : ∀ i j, i < j → j < n → g i = g j → False := by
    intro i j hij hj heq
    have hR : R (g (j + (n - j + i) - 1)) (g j) := by
      have e : j + (n - j + i) - 1 = i + n - 1 := by omega
      have := hg.1 (i + n - 1)
      rw [show i + n - 1 + 1 = i + n by omega, hg.2, heq] at this
      rw [e]
      exact this
    exact hmin (n - j + i) (by omega) (by omega) _ (hg.shortcut (by omega) hR)
  refine ⟨n, hn1, g, hg, fun i j hi hj hR => ?_, fun i j hi hj heq => ?_⟩
  · rcases Nat.lt_or_ge j (i + 1) with hji | hji
    · by_cases hlast : i + 1 = n ∧ j = 0
      · exact Or.inr hlast
      · have hR' : R (g (j + (i - j + 1) - 1)) (g j) := by
          rw [show j + (i - j + 1) - 1 = i by omega]
          exact hR
        exact absurd (hg.shortcut (by omega) hR') (hmin _ (by omega) (by omega) _)
    · rcases hji.eq_or_lt with hji | hji
      · exact Or.inl hji.symm
      · have hR' : R (g (j + (n - j + i + 1) - 1)) (g j) := by
          rw [show j + (n - j + i + 1) - 1 = i + n by omega, hg.2]
          exact hR
        exact absurd (hg.shortcut (by omega) hR') (hmin _ (by omega) (by omega) _)
  · by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact hinj i j h hj heq
    · exact hinj j i h hi heq.symm

/-- **Exercise 3.J.1**, geometric step. In the plane, a bundle `c` strictly between `a` and `b`
in its first coordinate cannot be strictly dearer than `a` and `b` at a price `q` and at most
as dear as both at a price `r` (both prices with positive second component). -/
theorem sarp_twoGoods_between_false {q r a b c : Fin 2 → ℝ} (hq : 0 < q 1) (hr : 0 < r 1)
    (hac : a 0 < c 0) (hcb : c 0 < b 0) (hqa : q ⬝ᵥ a < q ⬝ᵥ c) (hqb : q ⬝ᵥ b < q ⬝ᵥ c)
    (hra : r ⬝ᵥ c ≤ r ⬝ᵥ a) (hrb : r ⬝ᵥ c ≤ r ⬝ᵥ b) : False := by
  simp only [dotProduct, Fin.sum_univ_two] at hqa hqb hra hrb
  set μ := b 0 - c 0 with hμ
  set ν := c 0 - a 0 with hν
  have hμ0 : 0 < μ := by rw [hμ]; linarith
  have hν0 : 0 < ν := by rw [hν]; linarith
  set D := (μ + ν) * c 1 - μ * a 1 - ν * b 1 with hD
  have e1 : μ * ((q 0 * c 0 + q 1 * c 1) - (q 0 * a 0 + q 1 * a 1)) +
      ν * ((q 0 * c 0 + q 1 * c 1) - (q 0 * b 0 + q 1 * b 1)) = q 1 * D := by
    rw [hD, hμ, hν]; ring
  have e2 : μ * ((r 0 * c 0 + r 1 * c 1) - (r 0 * a 0 + r 1 * a 1)) +
      ν * ((r 0 * c 0 + r 1 * c 1) - (r 0 * b 0 + r 1 * b 1)) = r 1 * D := by
    rw [hD, hμ, hν]; ring
  have h1 : 0 < q 1 * D := by
    rw [← e1]
    exact add_pos (mul_pos hμ0 (by linarith)) (mul_pos hν0 (by linarith))
  have h2 : r 1 * D ≤ 0 := by
    rw [← e2]
    exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos hμ0.le (by linarith))
      (mul_nonpos_of_nonneg_of_nonpos hν0.le (by linarith))
  have hDpos : 0 < D := pos_of_mul_pos_right h1 hq.le
  nlinarith

/-- **Exercise 3.J.1** (MWG, p. 104), the substantive direction. With two goods, a demand
function satisfying Walras' law and the weak axiom satisfies the strong axiom. -/
theorem strongAxiom_of_weakAxiom_two {x : DemandFunction 2} (hW : WalrasLaw x)
    (hWA : WeakAxiom x) : StrongAxiom x := by
  classical
  rw [strongAxiom_iff_acyclic]
  intro a0 ha0
  obtain ⟨n, hn1, g, hg, hchord, hinj⟩ := sarp_exists_minimal_relCycle ⟨a0, ha0⟩
  have hs : ∀ k, ∃ q : (Fin 2 → ℝ) × ℝ, PWDomain q.1 q.2 ∧ x q.1 q.2 = g k ∧
      q.1 ⬝ᵥ g (k + 1) ≤ q.2 ∧ g (k + 1) ≠ g k := by
    intro k
    obtain ⟨p, w, h⟩ := hg.1 k
    exact ⟨(p, w), h⟩
  choose q hq using hs
  set P : ℕ → Fin 2 → ℝ := fun k => (q k).1 with hP
  have hwal : ∀ k, P k ⬝ᵥ g k = (q k).2 := by
    intro k
    rw [hP, ← (hq k).2.1]
    exact hW _ _ (hq k).1
  have hstep : ∀ k, P k ⬝ᵥ g (k + 1) ≤ P k ⬝ᵥ g k := fun k => by
    rw [hwal k]
    exact (hq k).2.2.1
  -- the cycle has length at least three
  have hn3 : 3 ≤ n := by
    by_contra hlt
    rcases (show n = 1 ∨ n = 2 by omega) with h1 | h2
    · have := hg.2 0
      rw [h1] at this
      exact (hq 0).2.2.2 this
    · have hc := hWA (q 0).1 (q 0).2 (q 1).1 (q 1).2 (hq 0).1 (hq 1).1
        (by rw [(hq 1).2.1]; exact (hq 0).2.2.1)
        (by rw [(hq 1).2.1, (hq 0).2.1]; exact (hq 0).2.2.2)
      have h20 : g (1 + 1) = g 0 := by
        have := hg.2 0
        rw [h2] at this
        exact this
      have := (hq 1).2.2.1
      rw [h20, ← (hq 0).2.1] at this
      linarith
  -- (B): every bundle other than `g k` and its successor is strictly dearer at `p^k`
  have hB : ∀ k j, k < n → j < n → j ≠ k → ¬(j = k + 1 ∨ (k + 1 = n ∧ j = 0)) →
      P k ⬝ᵥ g k < P k ⬝ᵥ g j := by
    intro k j hk hj hjk hnot
    by_contra hle
    rw [not_lt, hwal k] at hle
    by_cases hgj : g j = g k
    · exact hjk (hinj j k hj hk hgj)
    · exact hnot (hchord k j hk hj ⟨(q k).1, (q k).2, (hq k).1, (hq k).2.1, hle, hgj⟩)
  -- the predecessor of an index
  set pr : ℕ → ℕ := fun c => if c = 0 then n - 1 else c - 1 with hpr
  have hpr_lt : ∀ c, c < n → pr c < n := by
    intro c hc
    simp only [hpr]
    split_ifs <;> omega
  have hpr_succ : ∀ c, c < n → g (pr c + 1) = g c := by
    intro c hc
    simp only [hpr]
    split_ifs with h0
    · rw [show n - 1 + 1 = 0 + n by omega, hg.2, h0]
    · rw [show c - 1 + 1 = c by omega]
  -- (M): `g c` minimises the expenditure at the price of its predecessor
  have hM : ∀ c j, c < n → j < n → P (pr c) ⬝ᵥ g c ≤ P (pr c) ⬝ᵥ g j := by
    intro c j hc hj
    have h1 : P (pr c) ⬝ᵥ g c ≤ P (pr c) ⬝ᵥ g (pr c) := by
      rw [← hpr_succ c hc]
      exact hstep (pr c)
    by_cases hjc : j = c
    · rw [hjc]
    by_cases hjp : j = pr c
    · rw [hjp]
      exact h1
    refine h1.trans (hB (pr c) j (hpr_lt c hc) hj hjp ?_).le
    simp only [hpr] at hjp ⊢
    split_ifs at hjp ⊢ <;> omega
  have hPpos : ∀ k, 0 < P k 0 ∧ 0 < P k 1 := fun k => ⟨(hq k).1.1 0, (hq k).1.1 1⟩
  -- (I): distinct bundles of the cycle are unordered, hence have distinct first coordinates
  have hI : ∀ i j, i < n → j < n → i ≠ j → g i 0 ≤ g j 0 → g i 1 ≤ g j 1 → False := by
    intro i j hi hj hij h0 h1
    have hm := hM j i hj hi
    have hne : g i ≠ g j := fun h => hij (hinj i j hi hj h)
    have hlt : g i 0 < g j 0 ∨ g i 1 < g j 1 := by
      by_contra hc
      rw [not_or, not_lt, not_lt] at hc
      apply hne
      funext l
      fin_cases l
      · exact le_antisymm h0 hc.1
      · exact le_antisymm h1 hc.2
    simp only [dotProduct, Fin.sum_univ_two] at hm
    obtain ⟨hp0, hp1⟩ := hPpos (pr j)
    rcases hlt with h | h
    · nlinarith [mul_le_mul_of_nonneg_left h1 hp1.le]
    · nlinarith [mul_le_mul_of_nonneg_left h0 hp0.le]
  have hI' : ∀ i j, i < n → j < n → i ≠ j → g i 0 ≠ g j 0 := by
    intro i j hi hj hij heq
    rcases le_total (g i 1) (g j 1) with h | h
    · exact hI i j hi hj hij heq.le h
    · exact hI j i hj hi (Ne.symm hij) heq.ge h
  -- (C): no bundle lies strictly between two consecutive bundles in its first coordinate
  have hC : ∀ k c, k < n → c < n → c ≠ k → ¬(c = k + 1 ∨ (k + 1 = n ∧ c = 0)) →
      ((g k 0 < g c 0 ∧ g c 0 < g (k + 1) 0) ∨ (g (k + 1) 0 < g c 0 ∧ g c 0 < g k 0)) →
      False := by
    intro k c hk hc hck hnot hbet
    have hq1 := hB k c hk hc hck hnot
    have hq2 := hstep k
    set kk := if k + 1 = n then 0 else k + 1 with hkk
    have hkk_lt : kk < n := by rw [hkk]; split_ifs <;> omega
    have hgkk : g (k + 1) = g kk := by
      rw [hkk]
      split_ifs with h
      · rw [h, show n = 0 + n by omega, hg.2]
      · rfl
    have hr1 := hM c k hc hk
    have hr2 := hM c kk hc hkk_lt
    rw [← hgkk] at hr2
    rcases hbet with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact sarp_twoGoods_between_false (hPpos k).2 (hPpos (pr c)).2 h1 h2 hq1
        (lt_of_le_of_lt hq2 hq1) hr1 hr2
    · exact sarp_twoGoods_between_false (hPpos k).2 (hPpos (pr c)).2 h1 h2
        (lt_of_le_of_lt hq2 hq1) hq1 hr2 hr1
  -- the leftmost bundle has two distinct neighbours, which contradicts (C)
  obtain ⟨a, ha, hmin⟩ := Finset.exists_min_image (Finset.range n) (fun k => g k 0)
    ⟨0, Finset.mem_range.mpr (by omega)⟩
  rw [Finset.mem_range] at ha
  set s := if a + 1 = n then 0 else a + 1 with hsdef
  set t := pr a with htdef
  have hs_lt : s < n := by rw [hsdef]; split_ifs <;> omega
  have ht_lt : t < n := hpr_lt a ha
  have hgs : g (a + 1) = g s := by
    rw [hsdef]
    split_ifs with h
    · rw [h, show n = 0 + n by omega, hg.2]
    · rfl
  have hgt : g (t + 1) = g a := hpr_succ a ha
  have ht_cases : (a = 0 ∧ t = n - 1) ∨ (a ≠ 0 ∧ t = a - 1) := by
    by_cases h : a = 0
    · exact Or.inl ⟨h, by simp only [htdef, hpr, h, ↓reduceIte]⟩
    · exact Or.inr ⟨h, by simp only [htdef, hpr, h, ↓reduceIte]⟩
  have hs_cases : (a + 1 = n ∧ s = 0) ∨ (a + 1 ≠ n ∧ s = a + 1) := by
    by_cases h : a + 1 = n
    · exact Or.inl ⟨h, by simp only [hsdef, h, ↓reduceIte]⟩
    · exact Or.inr ⟨h, by simp only [hsdef, h, ↓reduceIte]⟩
  have hsa : s ≠ a := by omega
  have hta : t ≠ a := by omega
  have hst : s ≠ t := by omega
  have has : g a 0 < g s 0 :=
    lt_of_le_of_ne (hmin s (Finset.mem_range.mpr hs_lt)) (hI' a s ha hs_lt (Ne.symm hsa))
  have hat : g a 0 < g t 0 :=
    lt_of_le_of_ne (hmin t (Finset.mem_range.mpr ht_lt)) (hI' a t ha ht_lt (Ne.symm hta))
  rcases lt_or_gt_of_ne (hI' s t hs_lt ht_lt hst) with h | h
  · exact hC t s ht_lt hs_lt hst (by omega) (Or.inr ⟨by rw [hgt]; exact has, h⟩)
  · exact hC a t ha ht_lt hta (by omega) (Or.inl ⟨hat, by rw [hgs]; exact h⟩)

/-- **Exercise 3.J.1** (MWG, p. 104). When `L = 2`, a demand function satisfying Walras' law
satisfies the strong axiom if and only if it satisfies the weak axiom. -/
theorem exercise_3_J_1 {x : DemandFunction 2} (hW : WalrasLaw x) :
    StrongAxiom x ↔ WeakAxiom x :=
  ⟨weakAxiom_of_strongAxiom, strongAxiom_of_weakAxiom_two hW⟩

/-- **Section 3.J** (MWG, p. 92). "When `L = 2` and demand satisfies the WA, we can always find a
rationalizing preference relation": Exercise 3.J.1 and Proposition 3.J.1. -/
theorem weakAxiom_rationalizable_two {x : DemandFunction 2} (hW : WalrasLaw x)
    (hWA : WeakAxiom x) :
    ∃ r : (Fin 2 → ℝ) → (Fin 2 → ℝ) → Prop, Rational r ∧
      ∀ p w, PWDomain p w → ∀ y ∈ budgetSet p w, y ≠ x p w → Strict r (x p w) y :=
  proposition_3_J_1 (strongAxiom_of_weakAxiom_two hW hWA)

/-- One revealed-preference step for the demand of Exercise 2.F.15 at prices `(a, b, 1)`. -/
theorem sarp_demand_2_F_15_revealed {a b w a' b' w' : ℝ} (ha : 0 < a) (hb : 0 < b) (hw : 0 < w)
    (hcost : a * (b' - a') - b * b' + w' + (a' ^ 2 - a' * b' + b' ^ 2) ≤ w)
    (hne : b' - a' ≠ b - a) :
    sarpRevealedDirect demand_2_F_15 (demand_2_F_15 ![a, b, 1] w)
      (demand_2_F_15 ![a', b', 1] w') := by
  refine ⟨![a, b, 1], w, ⟨fun l => ?_, hw⟩, rfl, ?_, fun h => hne ?_⟩
  · fin_cases l <;> simp [ha, hb]
  · simp only [demand_2_F_15, dotProduct, Fin.sum_univ_three]
    simp
    linarith
  · have := congrFun h 0
    simpa [demand_2_F_15] using this

/-- **Section 3.J** (MWG, p. 92): "when `L > 2`, the SA is stronger than the WA". The demand of
Exercise 2.F.15 (consumption set `ℝ³`) satisfies Walras' law and the weak axiom, but at the
prices `(a, b, 1)` with `(a, b) = (21,11), (17,3), (9,1), (2,7), (2,15), (9,21), (17,19)` and
wealth `94, 174, 240, 163, 43, 1, 55` each chosen bundle is revealed preferred to the next and
the last to the first. -/
theorem strongAxiom_stronger_three :
    WalrasLaw demand_2_F_15 ∧ WeakAxiom demand_2_F_15 ∧ ¬StrongAxiom demand_2_F_15 := by
  refine ⟨exercise_2_F_15_basic.2.1, exercise_2_F_15_weakAxiom, ?_⟩
  rw [strongAxiom_iff_acyclic]
  intro h
  apply h (demand_2_F_15 ![21, 11, 1] 94)
  have s1 := sarp_demand_2_F_15_revealed (a := 21) (b := 11) (w := 94) (a' := 17) (b' := 3)
    (w' := 174) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s2 := sarp_demand_2_F_15_revealed (a := 17) (b := 3) (w := 174) (a' := 9) (b' := 1)
    (w' := 240) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s3 := sarp_demand_2_F_15_revealed (a := 9) (b := 1) (w := 240) (a' := 2) (b' := 7)
    (w' := 163) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s4 := sarp_demand_2_F_15_revealed (a := 2) (b := 7) (w := 163) (a' := 2) (b' := 15)
    (w' := 43) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s5 := sarp_demand_2_F_15_revealed (a := 2) (b := 15) (w := 43) (a' := 9) (b' := 21)
    (w' := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s6 := sarp_demand_2_F_15_revealed (a := 9) (b := 21) (w := 1) (a' := 17) (b' := 19)
    (w' := 55) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s7 := sarp_demand_2_F_15_revealed (a := 17) (b := 19) (w := 55) (a' := 21) (b' := 11)
    (w' := 94) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ((((((Relation.TransGen.single s1).tail s2).tail s3).tail s4).tail s5).tail s6).tail s7

end MWG.ClassicalDemand
