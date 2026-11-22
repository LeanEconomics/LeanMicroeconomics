/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Int.LeastGreatest
import Mathlib.Algebra.Group.End

/-!
# Continuous associative operations on the line (for Debreu's theorem, MWG p. 838)

The one-dimensional step of the proof of Debreu's separability theorem quoted in the small type
of MWG, Section 22.D (p. 838): a continuous, commutative, associative operation `⊕` on `ℝ` with
neutral element `0`, strictly increasing in each argument and solvable (`a ⊕ b = c` has a
solution `b` for all `a`, `c`), is isomorphic to addition: there is a continuous strictly
increasing `g` with `g (a ⊕ b) = g a + g b` (`aczel_associativity`; Aczél's associativity
theorem, here in the form needed for the separability theorem).

Proof. Translations `y ↦ y ⊕ c` are permutations of `ℝ`; the grid `k ⊙ c` (`k ∈ ℤ`) is the
orbit of `0` under the integer powers of this permutation. Continuity gives halving (`h ⊕ h = x`
by the intermediate value theorem), an Archimedean property and `hₘ → 0` for the iterated
halves `hₘ` of `1`. With `kₘ(x)` the integer part of `x` on the grid of `hₘ`,
`g(x) = sup kₘ(x) / 2ᵐ` satisfies `kₘ(x) / 2ᵐ ≤ g(x) ≤ (kₘ(x) + 1) / 2ᵐ`, whence additivity,
strict monotonicity, a dense range, and continuity.
-/

namespace MWG.WelfareBargaining

/-- The hypotheses on a binary operation of the one-dimensional step of Debreu's theorem
(MWG, p. 838): continuous, commutative, associative, `0` neutral, strictly increasing in each
argument, and solvable. -/
structure IsAczelOp (op : ℝ → ℝ → ℝ) : Prop where
  cont : Continuous fun p : ℝ × ℝ => op p.1 p.2
  comm : ∀ a b, op a b = op b a
  assoc : ∀ a b c, op (op a b) c = op a (op b c)
  zero : ∀ a, op a 0 = a
  mono : ∀ a, StrictMono (op a)
  solv : ∀ a c, ∃ b, op a b = c

/-- Addition satisfies the hypotheses. -/
theorem isAczelOp_add : IsAczelOp (· + ·) where
  cont := continuous_fst.add continuous_snd
  comm := add_comm
  assoc := add_assoc
  zero := add_zero
  mono := fun _ _ _ h => by simpa using h
  solv := fun a c => ⟨c - a, by ring⟩

variable {op : ℝ → ℝ → ℝ}

theorem aczel_zero_op (h : IsAczelOp op) (a : ℝ) : op 0 a = a := by rw [h.comm, h.zero]

theorem aczel_mono_left (h : IsAczelOp op) (b : ℝ) : StrictMono fun a => op a b :=
  fun x y hxy => by
    simp only
    rw [h.comm x, h.comm y]
    exact h.mono b hxy

theorem aczel_le_op (h : IsAczelOp op) {a a' b b' : ℝ} (ha : a ≤ a') (hb : b ≤ b') :
    op a b ≤ op a' b' :=
  ((h.mono a).monotone hb).trans ((aczel_mono_left h b').monotone ha)

theorem aczel_lt_op (h : IsAczelOp op) {a a' b b' : ℝ} (ha : a < a') (hb : b < b') :
    op a b < op a' b' :=
  (h.mono a hb).trans (aczel_mono_left h b' ha)

theorem aczel_continuous_diag (h : IsAczelOp op) : Continuous fun y => op y y :=
  h.cont.comp (continuous_id.prodMk continuous_id)

/-- The translation `y ↦ op y c` as a permutation of `ℝ`. -/
noncomputable def aczelShift (h : IsAczelOp op) (c : ℝ) : Equiv.Perm ℝ :=
  Equiv.ofBijective (fun y => op y c) ⟨(aczel_mono_left h c).injective, fun z => by
    obtain ⟨b, hb⟩ := h.solv c z
    exact ⟨b, by simp only; rw [h.comm]; exact hb⟩⟩

theorem aczelShift_apply (h : IsAczelOp op) (c y : ℝ) : aczelShift h c y = op y c := rfl

theorem aczelShift_inv_apply (h : IsAczelOp op) (c y : ℝ) :
    (aczelShift h c)⁻¹ y = op y ((aczelShift h c)⁻¹ 0) := by
  rw [Equiv.Perm.inv_eq_iff_eq, aczelShift_apply, h.assoc]
  have e : op ((aczelShift h c)⁻¹ 0) c = 0 := Equiv.apply_symm_apply (aczelShift h c) 0
  rw [e, h.zero]

theorem aczelShift_zpow_apply (h : IsAczelOp op) (c : ℝ) (k : ℤ) (y : ℝ) :
    (aczelShift h c ^ k) y = op y ((aczelShift h c ^ k) 0) := by
  induction k using Int.induction_on generalizing y with
  | zero => simp [h.zero]
  | succ n ih =>
    rw [zpow_add_one, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ih (aczelShift h c y),
      ih (aczelShift h c 0), aczelShift_apply, aczelShift_apply, h.assoc, aczel_zero_op h]
  | pred n ih =>
    rw [zpow_sub_one, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ih ((aczelShift h c)⁻¹ y),
      ih ((aczelShift h c)⁻¹ 0), aczelShift_inv_apply h c y, h.assoc]

/-- The grid point `k ⊙ c`: the `k`-th power of the translation by `c`, applied to `0`. -/
noncomputable def aczelGrid (h : IsAczelOp op) (c : ℝ) (k : ℤ) : ℝ := (aczelShift h c ^ k) 0

theorem aczelGrid_add (h : IsAczelOp op) (c : ℝ) (k l : ℤ) :
    aczelGrid h c (k + l) = op (aczelGrid h c k) (aczelGrid h c l) := by
  unfold aczelGrid
  rw [zpow_add, Equiv.Perm.mul_apply, aczelShift_zpow_apply h c k, h.comm]

theorem aczelGrid_zero (h : IsAczelOp op) (c : ℝ) : aczelGrid h c 0 = 0 := by
  simp [aczelGrid]

theorem aczelGrid_one (h : IsAczelOp op) (c : ℝ) : aczelGrid h c 1 = c := by
  simp [aczelGrid, aczelShift_apply, aczel_zero_op h]

theorem aczelGrid_succ (h : IsAczelOp op) (c : ℝ) (k : ℤ) :
    aczelGrid h c (k + 1) = op (aczelGrid h c k) c := by
  rw [aczelGrid_add, aczelGrid_one]

theorem aczelGrid_strictMono (h : IsAczelOp op) {c : ℝ} (hc : 0 < c) :
    StrictMono (aczelGrid h c) := by
  refine strictMono_int_of_lt_succ fun k => ?_
  rw [aczelGrid_succ]
  conv_lhs => rw [← h.zero (aczelGrid h c k)]
  exact h.mono _ hc

theorem aczelGrid_sq (h : IsAczelOp op) {c d : ℝ} (hd : op d d = c) (k : ℤ) :
    aczelGrid h c k = aczelGrid h d (2 * k) := by
  have e : aczelShift h c = aczelShift h d ^ (2 : ℤ) := by
    ext y
    rw [zpow_two, Equiv.Perm.mul_apply, aczelShift_apply, aczelShift_apply, aczelShift_apply,
      h.assoc, hd]
  unfold aczelGrid
  rw [e, ← zpow_mul]

/-- Halving: every `x` is `y ⊕ y` for some `y`. -/
theorem aczel_half (h : IsAczelOp op) (x : ℝ) : ∃ y, op y y = x := by
  rcases le_total 0 x with hx | hx
  · obtain ⟨y, -, hy⟩ := intermediate_value_Icc hx (aczel_continuous_diag h).continuousOn
      ⟨by simp only [h.zero]; exact hx, by
        conv_lhs => rw [← h.zero x]
        exact (h.mono x).monotone hx⟩
    exact ⟨y, hy⟩
  · obtain ⟨y, -, hy⟩ := intermediate_value_Icc hx (aczel_continuous_diag h).continuousOn
      ⟨by
        have := (h.mono x).monotone hx
        simp only [h.zero] at this ⊢
        exact this, by simp only [h.zero]; exact hx⟩
    exact ⟨y, hy⟩

/-- A chosen half of `x`. -/
noncomputable def aczelRoot (h : IsAczelOp op) (x : ℝ) : ℝ := (aczel_half h x).choose

theorem aczelRoot_spec (h : IsAczelOp op) (x : ℝ) : op (aczelRoot h x) (aczelRoot h x) = x :=
  (aczel_half h x).choose_spec

theorem aczelRoot_pos (h : IsAczelOp op) {x : ℝ} (hx : 0 < x) : 0 < aczelRoot h x := by
  by_contra hn
  have h1 := aczel_le_op h (not_lt.1 hn) (not_lt.1 hn)
  rw [aczelRoot_spec h, h.zero] at h1
  linarith

theorem aczelRoot_lt (h : IsAczelOp op) {x : ℝ} (hx : 0 < x) : aczelRoot h x < x := by
  by_contra hn
  have h1 := aczel_le_op h (not_lt.1 hn) (not_lt.1 hn)
  have h2 : x < op x x := by
    conv_lhs => rw [← h.zero x]
    exact h.mono x hx
  rw [aczelRoot_spec h] at h1
  linarith

/-- The iterated halves `hₘ` of `1`. -/
noncomputable def aczelSeq (h : IsAczelOp op) (m : ℕ) : ℝ := (aczelRoot h)^[m] 1

theorem aczelSeq_succ (h : IsAczelOp op) (m : ℕ) :
    aczelSeq h (m + 1) = aczelRoot h (aczelSeq h m) := by
  rw [aczelSeq, Function.iterate_succ_apply']
  rfl

theorem aczelSeq_spec (h : IsAczelOp op) (m : ℕ) :
    op (aczelSeq h (m + 1)) (aczelSeq h (m + 1)) = aczelSeq h m := by
  rw [aczelSeq_succ, aczelRoot_spec h]

theorem aczelSeq_pos (h : IsAczelOp op) (m : ℕ) : 0 < aczelSeq h m := by
  induction m with
  | zero => simp [aczelSeq]
  | succ n ih => rw [aczelSeq_succ]; exact aczelRoot_pos h ih

open Filter Topology in
/-- The halves tend to `0`: below every `δ > 0` there is some `hₘ`. -/
theorem aczelSeq_small (h : IsAczelOp op) {δ : ℝ} (hδ : 0 < δ) : ∃ m, aczelSeq h m < δ := by
  have hanti : Antitone (aczelSeq h) := antitone_nat_of_succ_le fun m => by
    rw [aczelSeq_succ]
    exact (aczelRoot_lt h (aczelSeq_pos h m)).le
  have hbdd : BddBelow (Set.range (aczelSeq h)) := ⟨0, by
    rintro _ ⟨m, rfl⟩
    exact (aczelSeq_pos h m).le⟩
  have hlim := tendsto_atTop_ciInf hanti hbdd
  set L := ⨅ m, aczelSeq h m
  have hL : 0 ≤ L := le_ciInf fun m => (aczelSeq_pos h m).le
  have h1 : Tendsto (fun m => op (aczelSeq h (m + 1)) (aczelSeq h (m + 1))) atTop (𝓝 (op L L)) :=
    ((aczel_continuous_diag h).tendsto L).comp (hlim.comp (tendsto_add_atTop_nat 1))
  simp only [aczelSeq_spec] at h1
  have hLL : op L L = L := tendsto_nhds_unique h1 hlim
  have hL0 : L = 0 := by
    by_contra hne
    have hpos : 0 < L := lt_of_le_of_ne hL (Ne.symm hne)
    have : L < op L L := by
      conv_lhs => rw [← h.zero L]
      exact h.mono L hpos
    linarith
  rw [hL0] at hlim
  exact ((tendsto_order.1 hlim).2 δ hδ).exists

open Filter Topology in
/-- Archimedean property: the grid of `c > 0` is unbounded above. -/
theorem aczelGrid_unbounded (h : IsAczelOp op) {c : ℝ} (hc : 0 < c) (x : ℝ) :
    ∃ k : ℤ, x < aczelGrid h c k := by
  by_contra hne
  simp only [not_exists, not_lt] at hne
  set f : ℕ → ℝ := fun n => aczelGrid h c n
  have hmono : Monotone f := fun a b hab =>
    (aczelGrid_strictMono h hc).monotone (by exact_mod_cast hab)
  have hbdd : BddAbove (Set.range f) := ⟨x, by
    rintro _ ⟨n, rfl⟩
    exact hne n⟩
  have hlim := tendsto_atTop_ciSup hmono hbdd
  set L := ⨆ n, f n
  have h1 : Tendsto (fun n => op (f n) c) atTop (𝓝 (op L c)) :=
    (h.cont.tendsto (L, c)).comp (hlim.prodMk_nhds tendsto_const_nhds)
  have h2 : Tendsto (fun n => op (f n) c) atTop (𝓝 L) := by
    have e : (fun n => op (f n) c) = fun n => f (n + 1) := by
      funext n
      simp only [f, Nat.cast_succ, aczelGrid_succ]
    rw [e]
    exact hlim.comp (tendsto_add_atTop_nat 1)
  have e : op L c = op L 0 := by rw [tendsto_nhds_unique h1 h2, h.zero]
  exact hc.ne' ((h.mono L).injective e)

/-- The grid of `c > 0` is unbounded below. -/
theorem aczelGrid_unbounded_below (h : IsAczelOp op) {c : ℝ} (hc : 0 < c) (x : ℝ) :
    ∃ k : ℤ, aczelGrid h c k < x := by
  obtain ⟨y, hy⟩ := h.solv x 0
  obtain ⟨k, hk⟩ := aczelGrid_unbounded h hc y
  refine ⟨-k, ?_⟩
  have e : op (aczelGrid h c k) (aczelGrid h c (-k)) = 0 := by
    rw [← aczelGrid_add h, add_neg_cancel, aczelGrid_zero]
  have h1 : op (aczelGrid h c k) (aczelGrid h c (-k)) < op (aczelGrid h c k) x := by
    rw [e, h.comm, ← hy]
    exact h.mono x hk
  exact (h.mono _).lt_iff_lt.1 h1

/-- The integer part of `x` on the grid of `c > 0`. -/
theorem aczelGrid_floor (h : IsAczelOp op) {c : ℝ} (hc : 0 < c) (x : ℝ) :
    ∃ k : ℤ, aczelGrid h c k ≤ x ∧ x < aczelGrid h c (k + 1) := by
  classical
  obtain ⟨k₁, hk₁⟩ := aczelGrid_unbounded h hc x
  obtain ⟨k₀, hk₀⟩ := aczelGrid_unbounded_below h hc x
  obtain ⟨k, hk, hmax⟩ := Int.exists_greatest_of_bdd (P := fun z => aczelGrid h c z ≤ x)
    ⟨k₁, fun z hz => ((aczelGrid_strictMono h hc).lt_iff_lt.1 (hz.trans_lt hk₁)).le⟩
    ⟨k₀, hk₀.le⟩
  refine ⟨k, hk, not_le.1 fun h' => ?_⟩
  have := hmax (k + 1) h'
  omega

/-- The grid of level `m`: multiples of the `m`-th half `hₘ`. -/
noncomputable def aczelLevel (h : IsAczelOp op) (m : ℕ) (k : ℤ) : ℝ :=
  aczelGrid h (aczelSeq h m) k

theorem aczelLevel_strictMono (h : IsAczelOp op) (m : ℕ) : StrictMono (aczelLevel h m) :=
  aczelGrid_strictMono h (aczelSeq_pos h m)

theorem aczelLevel_refine (h : IsAczelOp op) (m r : ℕ) (k : ℤ) :
    aczelLevel h m k = aczelLevel h (m + r) (2 ^ r * k) := by
  induction r generalizing k with
  | zero => simp
  | succ r ih =>
    rw [ih, aczelLevel, aczelLevel, aczelGrid_sq h (aczelSeq_spec h (m + r)), ← add_assoc]
    congr 1
    ring

/-- The additive representation: `g(x) = sup {k / 2ᵐ : k ⊙ hₘ ≤ x}`. -/
noncomputable def aczelRep (h : IsAczelOp op) (x : ℝ) : ℝ :=
  sSup {d : ℝ | ∃ (m : ℕ) (k : ℤ), aczelLevel h m k ≤ x ∧ d = k / 2 ^ m}

theorem aczelRep_bracket (h : IsAczelOp op) {m : ℕ} {k : ℤ} {x : ℝ}
    (hk : aczelLevel h m k ≤ x) (hk' : x < aczelLevel h m (k + 1)) :
    (k : ℝ) / 2 ^ m ≤ aczelRep h x ∧ aczelRep h x ≤ ((k : ℝ) + 1) / 2 ^ m := by
  have hub : ∀ d ∈ {d : ℝ | ∃ (m : ℕ) (k : ℤ), aczelLevel h m k ≤ x ∧ d = k / 2 ^ m},
      d ≤ ((k : ℝ) + 1) / 2 ^ m := by
    rintro d ⟨m', k', hle, rfl⟩
    have e1 := aczelLevel_refine h m' m k'
    have e2 := aczelLevel_refine h m m' (k + 1)
    rw [add_comm m m'] at e2
    rw [e1] at hle
    rw [e2] at hk'
    have hlt : (2 : ℤ) ^ m * k' < 2 ^ m' * (k + 1) :=
      (aczelLevel_strictMono h _).lt_iff_lt.1 (hle.trans_lt hk')
    have hlt' : (2 : ℝ) ^ m * k' < 2 ^ m' * (k + 1) := by exact_mod_cast hlt
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  exact ⟨le_csSup ⟨_, hub⟩ ⟨m, k, hk, rfl⟩, csSup_le ⟨_, m, k, hk, rfl⟩ hub⟩

/-- The representation is additive. -/
theorem aczelRep_add (h : IsAczelOp op) (a b : ℝ) :
    aczelRep h (op a b) = aczelRep h a + aczelRep h b := by
  have key : ∀ m : ℕ, |aczelRep h (op a b) - aczelRep h a - aczelRep h b| ≤ 2 / 2 ^ m := by
    intro m
    have hs := aczelSeq_pos h m
    obtain ⟨ka, ha, ha'⟩ := aczelGrid_floor h hs a
    obtain ⟨kb, hb, hb'⟩ := aczelGrid_floor h hs b
    obtain ⟨kc, hc, hc'⟩ := aczelGrid_floor h hs (op a b)
    have hsm := aczelGrid_strictMono h hs
    have l1 : aczelGrid h (aczelSeq h m) (ka + kb) ≤ op a b := by
      rw [aczelGrid_add]
      exact aczel_le_op h ha hb
    have l2 : op a b < aczelGrid h (aczelSeq h m) (ka + 1 + (kb + 1)) := by
      rw [aczelGrid_add]
      exact aczel_lt_op h ha' hb'
    have i1 : ka + kb < kc + 1 := hsm.lt_iff_lt.1 (l1.trans_lt hc')
    have i2 : kc < ka + 1 + (kb + 1) := hsm.lt_iff_lt.1 (hc.trans_lt l2)
    have r1 : (ka : ℝ) + kb ≤ kc := by exact_mod_cast (by omega : ka + kb ≤ kc)
    have r2 : (kc : ℝ) ≤ ka + kb + 1 := by exact_mod_cast (by omega : kc ≤ ka + kb + 1)
    have Ba := aczelRep_bracket h ha ha'
    have Bb := aczelRep_bracket h hb hb'
    have Bc := aczelRep_bracket h hc hc'
    have hp : (0 : ℝ) < 2 ^ m := by positivity
    rw [abs_le]
    simp only [add_div] at Ba Bb Bc ⊢
    have q1 : (kc : ℝ) / 2 ^ m ≥ ka / 2 ^ m + kb / 2 ^ m := by
      rw [← add_div]
      exact div_le_div_of_nonneg_right r1 hp.le
    have q2 : (kc : ℝ) / 2 ^ m ≤ ka / 2 ^ m + kb / 2 ^ m + 1 / 2 ^ m := by
      rw [← add_div, ← add_div]
      exact div_le_div_of_nonneg_right r2 hp.le
    have q3 : (2 : ℝ) / 2 ^ m = 1 / 2 ^ m + 1 / 2 ^ m := by ring
    constructor <;> linarith
  by_contra hne
  have hpos : 0 < |aczelRep h (op a b) - aczelRep h a - aczelRep h b| / 2 := by
    have : aczelRep h (op a b) - aczelRep h a - aczelRep h b ≠ 0 := fun h0 => hne (by linarith)
    positivity
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hpos (by norm_num : (1 / 2 : ℝ) < 1)
  have := key m
  have e : (2 : ℝ) / 2 ^ m = 2 * (1 / 2) ^ m := by rw [one_div_pow]; ring
  linarith

theorem aczelRep_strictMono (h : IsAczelOp op) : StrictMono (aczelRep h) := by
  intro a b hab
  obtain ⟨δ, hδ⟩ := h.solv a b
  have hδpos : 0 < δ := by
    rw [← hδ] at hab
    conv_lhs at hab => rw [← h.zero a]
    exact (h.mono a).lt_iff_lt.1 hab
  obtain ⟨m, hm⟩ := aczelSeq_small h hδpos
  obtain ⟨k, hk, hk'⟩ := aczelGrid_floor h (aczelSeq_pos h m) δ
  have hk1 : 1 ≤ k := by
    by_contra hlt
    have hle : k + 1 ≤ 1 := by omega
    have := (aczelGrid_strictMono h (aczelSeq_pos h m)).monotone hle
    rw [aczelGrid_one] at this
    linarith
  have B := aczelRep_bracket h (m := m) hk hk'
  have h1 : (0 : ℝ) < k / 2 ^ m := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    positivity
  rw [← hδ, aczelRep_add]
  linarith [B.1]

theorem aczelRep_continuous (h : IsAczelOp op) : Continuous (aczelRep h) := by
  refine (aczelRep_strictMono h).monotone.continuous_of_denseRange ?_
  refine dense_of_exists_between fun a b hab => ?_
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (by linarith : 0 < (b - a) / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  set k : ℤ := ⌊a * 2 ^ m⌋ + 1
  have hp : (0 : ℝ) < 2 ^ m := by positivity
  have f1 := Int.floor_le (a * 2 ^ m)
  have f2 := Int.lt_floor_add_one (a * 2 ^ m)
  have hkR : (k : ℝ) = ⌊a * 2 ^ m⌋ + 1 := by simp [k]
  have B := aczelRep_bracket h (m := m) (k := k) le_rfl ((aczelLevel_strictMono h m)
    (lt_add_one k))
  refine ⟨aczelRep h (aczelLevel h m k), ⟨_, rfl⟩, ?_, ?_⟩
  · refine lt_of_lt_of_le ?_ B.1
    rw [lt_div_iff₀ hp, hkR]
    exact f2
  · refine lt_of_le_of_lt B.2 ?_
    rw [div_lt_iff₀ hp, hkR]
    have e : (1 / 2 : ℝ) ^ m * 2 ^ m = 1 := by rw [one_div_pow, div_mul_cancel₀ _ hp.ne']
    nlinarith

/-- **Debreu's theorem, one-dimensional step** (MWG, p. 838). A continuous, commutative,
associative operation on `ℝ` with neutral element `0`, strictly increasing in each argument and
solvable, is isomorphic to addition through a continuous strictly increasing `g`. -/
theorem aczel_associativity (h : IsAczelOp op) :
    ∃ g : ℝ → ℝ, StrictMono g ∧ Continuous g ∧ ∀ a b, g (op a b) = g a + g b :=
  ⟨aczelRep h, aczelRep_strictMono h, aczelRep_continuous h, aczelRep_add h⟩

end MWG.WelfareBargaining
