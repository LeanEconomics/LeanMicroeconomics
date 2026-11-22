/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGConsumerChoice.WeakAxiom
import ChoicePreferenceUtility.Basic
import MWGPreferenceChoice.ChoiceRules

/-!
# The weak axiom: Figure 2.F.5 and Exercises 2.F.1, 2.F.6, 2.F.12–2.F.14

MWG, Section 2.F (p. 33) and Exercises 2.F.1, 2.F.6, 2.F.12, 2.F.13 and 2.F.14
(pp. 37–39).

MWG's choice structures and weak axiom (Definition 1.C.1) are imported from MWG Chapter 1
(`MWG.PreferenceChoice.ChoiceStructure`, `MWG.PreferenceChoice.WeakAxiom`); the Walrasian
budget family with the demand's choice rule is shown to be such a choice structure
(`walrasianChoiceStructure`, `walrasianCorrStructure`). Exercise 2.F.12
uses Kreps' rational preferences (`Kreps.ChoicePreferenceUtility.Rational`, complete and
transitive) and Kreps' set of best elements `PrefChoice`, which is MWG's `C*(B, ≿)`.
-/

namespace MWG.ConsumerChoice

/-- **Section 2.E** (MWG, p. 24). The choice rule of a demand function on Walrasian budgets:
`C(B) = {x(p, w) : B = B_{p,w}}`. -/
def walrasianChoiceRule {L : ℕ} (x : DemandFunction L) (B : Set (Fin L → ℝ)) :
    Set (Fin L → ℝ) :=
  {y | ∃ p w, PWDomain p w ∧ B = budgetSet p w ∧ y = x p w}

/-- The zero bundle lies in every Walrasian budget set with `w ≥ 0`. -/
theorem zero_mem_budgetSet {L : ℕ} {p : Fin L → ℝ} {w : ℝ} (hw : 0 ≤ w) :
    (0 : Fin L → ℝ) ∈ budgetSet p w :=
  ⟨fun _ => le_rfl, by simpa using hw⟩

/-- **Section 2.E** (MWG, p. 24). A Walrasian demand function with values in the budget sets
makes `(𝓑^W, x(·))` a choice structure in the sense of MWG Chapter 1. -/
def walrasianChoiceStructure {L : ℕ} (x : DemandFunction L)
    (hB : ∀ p w, PWDomain p w → x p w ∈ budgetSet p w) :
    MWG.PreferenceChoice.ChoiceStructure (Fin L → ℝ) :=
  ⟨walrasianBudgetFamily L, walrasianChoiceRule x,
    by rintro _ ⟨p, w, hd, rfl⟩; exact ⟨0, zero_mem_budgetSet hd.2.le⟩,
    by
      rintro _ ⟨p, w, hd, rfl⟩ y ⟨p', w', hd', hBB, rfl⟩
      rw [hBB]
      exact hB _ _ hd',
    by rintro _ ⟨p, w, hd, rfl⟩; exact ⟨x p w, p, w, hd, rfl, rfl⟩⟩

/-- Under homogeneity of degree zero, `C(B_{p,w}) = {x(p, w)}`. -/
theorem walrasianChoiceRule_budgetSet {L : ℕ} {x : DemandFunction L} (hH : HomogeneousZero x)
    {p : Fin L → ℝ} {w : ℝ} (hd : PWDomain p w) :
    walrasianChoiceRule x (budgetSet p w) = {x p w} := by
  ext y
  constructor
  · rintro ⟨p', w', hd', hB, rfl⟩
    exact Set.mem_singleton_iff.mpr (demand_depends_only_on_budget hH hd' hd hB.symm)
  · intro hy
    exact ⟨p, w, hd, rfl, hy⟩

/-- **Exercise 2.F.1** (MWG, p. 37). For a Walrasian demand function (values in `B_{p,w}`,
homogeneous of degree zero, so that `(𝓑^W, x(·))` is a choice structure), Definition 2.F.1
coincides with Definition 1.C.1. -/
theorem exercise_2_F_1 {L : ℕ} {x : DemandFunction L} (hH : HomogeneousZero x)
    (hB : ∀ p w, PWDomain p w → x p w ∈ budgetSet p w) :
    WeakAxiom x ↔ MWG.PreferenceChoice.WeakAxiom (walrasianChoiceStructure x hB) := by
  constructor
  · rintro hWA B ⟨p, w, hd, rfl⟩ B' ⟨p', w', hd', rfl⟩ a y _ hy ha ha' _ hy'
    change a ∈ walrasianChoiceRule x (budgetSet p w) at ha
    change y ∈ walrasianChoiceRule x (budgetSet p' w') at hy'
    change a ∈ walrasianChoiceRule x (budgetSet p' w')
    rw [walrasianChoiceRule_budgetSet hH hd] at ha
    rw [walrasianChoiceRule_budgetSet hH hd'] at hy' ⊢
    rw [Set.mem_singleton_iff] at ha hy' ⊢
    subst ha hy'
    by_contra hne
    have := hWA p w p' w' hd hd' hy.2 (Ne.symm hne)
    linarith [ha'.2]
  · intro hC p w p' w' hd hd' hle hne
    by_contra hcon
    push Not at hcon
    have hx := hB p w hd
    have hx' := hB p' w' hd'
    have hmem := hC (budgetSet p w) ⟨p, w, hd, rfl⟩ (budgetSet p' w') ⟨p', w', hd', rfl⟩
      (x p w) (x p' w') hx ⟨hx'.1, hle⟩
      (show x p w ∈ walrasianChoiceRule x (budgetSet p w) from ⟨p, w, hd, rfl, rfl⟩)
      ⟨hx.1, hcon⟩ hx'
      (show x p' w' ∈ walrasianChoiceRule x (budgetSet p' w') from ⟨p', w', hd', rfl, rfl⟩)
    change x p w ∈ walrasianChoiceRule x (budgetSet p' w') at hmem
    rw [walrasianChoiceRule_budgetSet hH hd', Set.mem_singleton_iff] at hmem
    exact hne hmem.symm

/-- **Exercise 2.F.6** (MWG, p. 38). For a demand function homogeneous of degree zero, the
weak axiom holds if and only if, for some `w > 0` and all `p, p' ≫ 0`, `p·x(p', w) ≤ w` and
`x(p', w) ≠ x(p, w)` imply `p'·x(p, w) > w`. -/
theorem exercise_2_F_6 {L : ℕ} {x : DemandFunction L} (hH : HomogeneousZero x) :
    WeakAxiom x ↔ ∃ w, 0 < w ∧ ∀ p p', StrictlyPositive p → StrictlyPositive p' →
      p ⬝ᵥ x p' w ≤ w → x p' w ≠ x p w → w < p' ⬝ᵥ x p w := by
  constructor
  · intro h
    exact ⟨1, one_pos, fun p p' hp hp' => h p 1 p' 1 ⟨hp, one_pos⟩ ⟨hp', one_pos⟩⟩
  · rintro ⟨v, hv, h⟩ p w p' w' hd hd' hle hne
    set a := v / w with ha
    set a' := v / w' with ha'
    have ha0 : 0 < a := div_pos hv hd.2
    have ha0' : 0 < a' := div_pos hv hd'.2
    have e : x (a • p) v = x p w := by
      have := hH p w a hd ha0
      rwa [ha, div_mul_cancel₀ _ hd.2.ne'] at this
    have e' : x (a' • p') v = x p' w' := by
      have := hH p' w' a' hd' ha0'
      rwa [ha', div_mul_cancel₀ _ hd'.2.ne'] at this
    have key := h (a • p) (a' • p') (pwDomain_smul hd ha0).1 (pwDomain_smul hd' ha0').1
      (by
        rw [e', smul_dotProduct, smul_eq_mul, ha]
        rw [div_mul_eq_mul_div, div_le_iff₀ hd.2]
        nlinarith)
      (by rw [e, e']; exact hne)
    rw [e, smul_dotProduct, smul_eq_mul, ha', div_mul_eq_mul_div, lt_div_iff₀ hd'.2] at key
    nlinarith

/-- **Exercise 2.F.12** (MWG, p. 38). A Walrasian demand function generated by a rational
preference relation `≿` (for every `(p, w)`, `x(p, w)` is the unique `≿`-best bundle of
`B_{p,w}`) satisfies the weak axiom. Kreps' `Rational` (complete and transitive) is MWG's
rationality, and Kreps' `PrefChoice` is MWG's `C*(B, ≿)`. -/
theorem exercise_2_F_12 {L : ℕ} {x : DemandFunction L}
    {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop} (hr : Kreps.ChoicePreferenceUtility.Rational r)
    (hgen : ∀ p w, PWDomain p w →
      Kreps.ChoicePreferenceUtility.PrefChoice r (budgetSet p w) = {x p w}) :
    WeakAxiom x := by
  intro p w p' w' hd hd' hle hne
  by_contra hcon
  push Not at hcon
  have hbest : x p w ∈ Kreps.ChoicePreferenceUtility.PrefChoice r (budgetSet p w) := by
    rw [hgen p w hd]; rfl
  have hbest' : x p' w' ∈ Kreps.ChoicePreferenceUtility.PrefChoice r (budgetSet p' w') := by
    rw [hgen p' w' hd']; rfl
  have hxB' : x p w ∈ budgetSet p' w' := ⟨hbest.1.1, hcon⟩
  have hx'B : x p' w' ∈ budgetSet p w := ⟨hbest'.1.1, hle⟩
  have h1 : r (x p w) (x p' w') := hbest.2 _ hx'B
  have hin : x p w ∈ Kreps.ChoicePreferenceUtility.PrefChoice r (budgetSet p' w') :=
    ⟨hxB', fun y hy => hr.2 _ _ _ h1 (hbest'.2 y hy)⟩
  rw [hgen p' w' hd', Set.mem_singleton_iff] at hin
  exact hne hin.symm

/-- **Exercise 2.F.14** (MWG, p. 39). A Walrasian demand function (values in `B_{p,w}`) that
satisfies the weak axiom is homogeneous of degree zero. -/
theorem exercise_2_F_14 {L : ℕ} {x : DemandFunction L} (hWA : WeakAxiom x)
    (hB : ∀ p w, PWDomain p w → x p w ∈ budgetSet p w) : HomogeneousZero x := by
  intro p w a hd ha
  have hd' := pwDomain_smul hd ha
  by_contra hne
  have hmem : x (a • p) (a * w) ∈ budgetSet p w := by
    rw [← budgetSet_smul p w ha]
    exact hB _ _ hd'
  have := hWA p w (a • p) (a * w) hd hd' hmem.2 hne
  rw [smul_dotProduct, smul_eq_mul] at this
  have hle := (hB p w hd).2
  nlinarith

/-! ### Exercise 2.F.13: multivalued demand -/

/-- **Exercise 2.F.13(a)** (MWG, p. 38). The weak axiom for Walrasian demand correspondences:
if `x ∈ x(p, w)`, `x' ∈ x(p', w')`, `x' ∈ B_{p,w}` and `x ∈ B_{p',w'}`, then
`x ∈ x(p', w')`. -/
def GeneralizedWeakAxiom {L : ℕ} (x : DemandCorrespondence L) : Prop :=
  ∀ p w p' w', PWDomain p w → PWDomain p' w' → ∀ y ∈ x p w, ∀ y' ∈ x p' w',
    y' ∈ budgetSet p w → y ∈ budgetSet p' w' → y ∈ x p' w'

/-- **Exercise 2.F.13(a)** (MWG, p. 38). A Walrasian demand correspondence with nonempty
values in the budget sets makes `(𝓑^W, x(·))` a choice structure (MWG Chapter 1). -/
def walrasianCorrStructure {L : ℕ} (x : DemandCorrespondence L)
    (hB : ∀ p w, PWDomain p w → x p w ⊆ budgetSet p w)
    (hne : ∀ p w, PWDomain p w → (x p w).Nonempty) :
    MWG.PreferenceChoice.ChoiceStructure (Fin L → ℝ) :=
  ⟨walrasianBudgetFamily L, fun B => {y | ∃ p w, PWDomain p w ∧ B = budgetSet p w ∧ y ∈ x p w},
    by rintro _ ⟨p, w, hd, rfl⟩; exact ⟨0, zero_mem_budgetSet hd.2.le⟩,
    by
      rintro _ ⟨p, w, hd, rfl⟩ y ⟨p', w', hd', hBB, hy⟩
      rw [hBB]
      exact hB _ _ hd' hy,
    by
      rintro _ ⟨p, w, hd, rfl⟩
      obtain ⟨y, hy⟩ := hne p w hd
      exact ⟨y, p, w, hd, rfl, hy⟩⟩

/-- **Exercise 2.F.13(a)** (MWG, p. 38). The generalisation is Definition 1.C.1 specialised to
Walrasian budgets: for a homogeneous correspondence with nonempty values in the budget sets,
with `C(B_{p,w}) = x(p, w)`. -/
theorem exercise_2_F_13a {L : ℕ} {x : DemandCorrespondence L} (hH : HomogeneousZeroCorr x)
    (hB : ∀ p w, PWDomain p w → x p w ⊆ budgetSet p w)
    (hne : ∀ p w, PWDomain p w → (x p w).Nonempty) :
    GeneralizedWeakAxiom x ↔ MWG.PreferenceChoice.WeakAxiom (walrasianCorrStructure x hB hne)
    := by
  have hC : ∀ p w, PWDomain p w →
      {y | ∃ p' w', PWDomain p' w' ∧ budgetSet p w = budgetSet p' w' ∧ y ∈ x p' w'} =
        x p w := by
    intro p w hd
    ext y
    constructor
    · rintro ⟨p', w', hd', hBB, hy⟩
      have hp := budgetSet_eq_imp_proportional hd hd' hBB
      have hw : w' = (w' / w) * w := by field_simp [hd.2.ne']
      have e : x p' w' = x p w := by
        calc x p' w' = x ((w' / w) • p) ((w' / w) * w) := by rw [← hp, ← hw]
          _ = x p w := hH p w _ hd (div_pos hd'.2 hd.2)
      rwa [e] at hy
    · intro hy
      exact ⟨p, w, hd, rfl, hy⟩
  constructor
  · rintro h B ⟨p, w, hd, rfl⟩ B' ⟨p', w', hd', rfl⟩ a y _ hy ha ha' _ hy'
    change a ∈ {y | ∃ p' w', PWDomain p' w' ∧ budgetSet p w = budgetSet p' w' ∧ y ∈ x p' w'}
      at ha
    change y ∈ {y | ∃ p'' w'', PWDomain p'' w'' ∧ budgetSet p' w' = budgetSet p'' w'' ∧
      y ∈ x p'' w''} at hy'
    change a ∈ {y | ∃ p'' w'', PWDomain p'' w'' ∧ budgetSet p' w' = budgetSet p'' w'' ∧
      y ∈ x p'' w''}
    rw [hC p w hd] at ha
    rw [hC p' w' hd'] at hy' ⊢
    exact h p w p' w' hd hd' a ha y hy' hy ha'
  · intro h p w p' w' hd hd' y hy y' hy' hy'B hyB
    have hres := h (budgetSet p w) ⟨p, w, hd, rfl⟩ (budgetSet p' w') ⟨p', w', hd', rfl⟩ y y'
      (hB p w hd hy) hy'B (show y ∈ {z | ∃ p'' w'', PWDomain p'' w'' ∧
        budgetSet p w = budgetSet p'' w'' ∧ z ∈ x p'' w''} from ⟨p, w, hd, rfl, hy⟩)
      hyB (hB p' w' hd' hy') (show y' ∈ {z | ∃ p'' w'', PWDomain p'' w'' ∧
        budgetSet p' w' = budgetSet p'' w'' ∧ z ∈ x p'' w''} from ⟨p', w', hd', rfl, hy'⟩)
    change y ∈ {z | ∃ p'' w'', PWDomain p'' w'' ∧
        budgetSet p' w' = budgetSet p'' w'' ∧ z ∈ x p'' w''} at hres
    rwa [hC p' w' hd'] at hres

/-- For a single-valued demand with values in `ℝ^L_+`, the generalised weak axiom of its
singleton correspondence is Definition 2.F.1. -/
theorem generalizedWeakAxiom_toCorrespondence_iff {L : ℕ} {x : DemandFunction L}
    (hX : ValuesInOrthant x) :
    GeneralizedWeakAxiom (toCorrespondence x) ↔ WeakAxiom x := by
  constructor
  · intro h p w p' w' hd hd' hle hne
    by_contra hcon
    push Not at hcon
    have := h p w p' w' hd hd' (x p w) rfl (x p' w') rfl ⟨hX p' w' hd', hle⟩ ⟨hX p w hd, hcon⟩
    exact hne (Set.mem_singleton_iff.mp this).symm
  · intro h p w p' w' hd hd' y hy y' hy' hy'B hyB
    simp only [toCorrespondence, Set.mem_singleton_iff] at hy hy' ⊢
    subst hy hy'
    by_contra hne
    have := h p w p' w' hd hd' hy'B.2 (Ne.symm hne)
    linarith [hyB.2]

/-- A nonnegative bundle with positive value at some prices has positive value at every
strictly positive price vector. -/
theorem dotProduct_pos_of_nonneg {L : ℕ} {y p p' : Fin L → ℝ} (hy : y ∈ nonnegOrthant L)
    (h : 0 < p ⬝ᵥ y) (hp' : StrictlyPositive p') : 0 < p' ⬝ᵥ y := by
  by_contra hneg
  push Not at hneg
  have hsum : ∀ l ∈ Finset.univ, 0 ≤ p' l * y l := fun l _ => mul_nonneg (hp' l).le (hy l)
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg hsum).mp
    (le_antisymm hneg (Finset.sum_nonneg hsum))
  have hz : ∀ l, y l = 0 := by
    intro l
    rcases mul_eq_zero.mp (h0 l (Finset.mem_univ l)) with h' | h'
    · exact absurd h' (hp' l).ne'
    · exact h'
  have : p ⬝ᵥ y = 0 := by simp [dotProduct, hz]
  linarith

/-- **Exercise 2.F.13(b)** (MWG, p. 38). The generalised weak axiom and Walras' law imply
property (*): for `y ∈ x(p, w)` and `y' ∈ x(p', w')`, if `p·y' < w` then `p'·y > w'`. -/
theorem exercise_2_F_13b {L : ℕ} {x : DemandCorrespondence L} (hG : GeneralizedWeakAxiom x)
    (hW : WalrasLawCorr x) (hB : ∀ p w, PWDomain p w → x p w ⊆ budgetSet p w) :
    ∀ p w p' w', PWDomain p w → PWDomain p' w' → ∀ y ∈ x p w, ∀ y' ∈ x p' w',
      p ⬝ᵥ y' < w → w' < p' ⬝ᵥ y := by
  intro p w p' w' hd hd' y hy y' hy' hlt
  by_contra hcon
  push Not at hcon
  have hmem := hG p' w' p w hd' hd y' hy' y hy ⟨(hB p w hd hy).1, hcon⟩
    ⟨(hB p' w' hd' hy').1, hlt.le⟩
  have := hW p w hd y' hmem
  linarith

/-- **Exercise 2.F.13(c)** (MWG, p. 39). The generalised compensated law of demand: from
`(p, w)` with `y ∈ x(p, w)`, for a compensated change to `(p', p'·y)`, every
`y' ∈ x(p', p'·y)` has `(p' - p)·(y' - y) ≤ 0`, strictly if `y' ∉ x(p, w)`. -/
def GeneralizedCompensatedLaw {L : ℕ} (x : DemandCorrespondence L) : Prop :=
  ∀ p w, PWDomain p w → ∀ y ∈ x p w, ∀ p', StrictlyPositive p' → 0 < p' ⬝ᵥ y →
    ∀ y' ∈ x p' (p' ⬝ᵥ y),
      (p' - p) ⬝ᵥ (y' - y) ≤ 0 ∧ (y' ∉ x p w → (p' - p) ⬝ᵥ (y' - y) < 0)

/-- **Exercise 2.F.13(c)** (MWG, p. 39). The generalised weak axiom and Walras' law imply the
generalised compensated law of demand. -/
theorem exercise_2_F_13c {L : ℕ} {x : DemandCorrespondence L} (hG : GeneralizedWeakAxiom x)
    (hW : WalrasLawCorr x) (hB : ∀ p w, PWDomain p w → x p w ⊆ budgetSet p w) :
    GeneralizedCompensatedLaw x := by
  intro p w hd y hy p' hp' hw' y' hy'
  set w' := p' ⬝ᵥ y with hw'def
  have hd' : PWDomain p' w' := ⟨hp', hw'⟩
  have hWy := hW p w hd y hy
  have hWy' := hW p' w' hd' y' hy'
  have hexp : (p' - p) ⬝ᵥ (y' - y) = w - p ⬝ᵥ y' := by
    rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, hWy, hWy', ← hw'def]
    ring
  have hge : w ≤ p ⬝ᵥ y' := by
    by_contra hlt
    push Not at hlt
    have := exercise_2_F_13b hG hW hB p w p' w' hd hd' y hy y' hy' hlt
    linarith
  refine ⟨by rw [hexp]; linarith, fun hnot => ?_⟩
  rw [hexp]
  rcases eq_or_lt_of_le hge with heq | hlt
  · exfalso
    apply hnot
    exact hG p' w' p w hd' hd y' hy' y hy ⟨(hB p w hd hy).1, le_of_eq hw'def.symm⟩
      ⟨(hB p' w' hd' hy').1, heq.symm.le⟩
  · linarith

/-- **Exercise 2.F.13(d)** (MWG, p. 39). Walras' law and the generalised compensated law of
demand imply the generalised weak axiom (for a demand correspondence with nonempty values in
the budget sets). -/
theorem exercise_2_F_13d {L : ℕ} {x : DemandCorrespondence L} (hW : WalrasLawCorr x)
    (hC : GeneralizedCompensatedLaw x) (hB : ∀ p w, PWDomain p w → x p w ⊆ budgetSet p w)
    (hne : ∀ p w, PWDomain p w → (x p w).Nonempty) : GeneralizedWeakAxiom x := by
  intro p w p' w' hd hd' y hy y' hy' hy'B hyB
  have hWy := hW p w hd y hy
  have hWy' := hW p' w' hd' y' hy'
  have hyO := (hB p w hd hy).1
  have hy'O := (hB p' w' hd' hy').1
  -- (p - p')·(y - y') = (w - p·y') + (w' - p'·y)
  have hsum : (p - p') ⬝ᵥ (y - y') = (w - p ⬝ᵥ y') + (w' - p' ⬝ᵥ y) := by
    rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, hWy, hWy']
    ring
  have hA := hy'B.2
  have hBn := hyB.2
  rcases eq_or_lt_of_le hBn with heq' | hlt'
  · -- the change to (p', w') is compensated for y
    have hpos : 0 < p' ⬝ᵥ y := by rw [heq']; exact hd'.2
    have hy'' : y' ∈ x p' (p' ⬝ᵥ y) := by rw [heq']; exact hy'
    obtain ⟨h1, _⟩ := hC p w hd y hy p' hd'.1 hpos y' hy''
    have e1 : (p' - p) ⬝ᵥ (y' - y) = w - p ⬝ᵥ y' := by
      rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, hWy, hWy', heq']
      ring
    have hpy' : p ⬝ᵥ y' = w := by linarith
    have hpos2 : 0 < p ⬝ᵥ y' := by rw [hpy']; exact hd.2
    have hy2 : y ∈ x p (p ⬝ᵥ y') := by rw [hpy']; exact hy
    obtain ⟨_, h2⟩ := hC p' w' hd' y' hy' p hd.1 hpos2 y hy2
    by_contra hnot
    have := h2 hnot
    rw [hsum, hpy', heq'] at this
    linarith
  · rcases eq_or_lt_of_le hA with heq | hlt
    · exfalso
      have hpos : 0 < p ⬝ᵥ y' := by rw [heq]; exact hd.2
      have hy2 : y ∈ x p (p ⬝ᵥ y') := by rw [heq]; exact hy
      obtain ⟨h1, _⟩ := hC p' w' hd' y' hy' p hd.1 hpos y hy2
      rw [hsum, heq] at h1
      linarith
    · exfalso
      set a := p ⬝ᵥ (y' - y) with ha
      set b := p' ⬝ᵥ (y' - y) with hb
      have ha0 : a < 0 := by rw [ha, dotProduct_sub]; linarith
      have hb0 : 0 < b := by rw [hb, dotProduct_sub]; linarith
      set α := b / (b - a) with hα
      have hba : 0 < b - a := by linarith
      have hα0 : 0 < α := div_pos hb0 hba
      have hα1 : α < 1 := (div_lt_one hba).mpr (by linarith)
      set q := α • p + (1 - α) • p' with hq
      have hqpos : StrictlyPositive q := fun l => by
        simp only [hq, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        have := hd.1 l
        have := hd'.1 l
        nlinarith
      have hqeq : q ⬝ᵥ y' = q ⬝ᵥ y := by
        have : q ⬝ᵥ (y' - y) = 0 := by
          rw [hq, add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul,
            ← ha, ← hb, hα]
          field_simp
          ring
        rw [dotProduct_sub, sub_eq_zero] at this
        exact this
      have hwq : 0 < q ⬝ᵥ y := dotProduct_pos_of_nonneg hyO (by rw [hWy]; exact hd.2) hqpos
      have hwq' : 0 < q ⬝ᵥ y' := by rw [hqeq]; exact hwq
      obtain ⟨yq, hyq⟩ := hne q (q ⬝ᵥ y) ⟨hqpos, hwq⟩
      have hyq' : yq ∈ x q (q ⬝ᵥ y') := by rw [hqeq]; exact hyq
      obtain ⟨c1, _⟩ := hC p w hd y hy q hqpos hwq yq hyq
      obtain ⟨c2, _⟩ := hC p' w' hd' y' hy' q hqpos hwq' yq hyq'
      have e1 : q - p = (1 - α) • (p' - p) := by
        rw [hq]; funext l; simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
        ring
      have e2 : q - p' = α • (p - p') := by
        rw [hq]; funext l; simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
        ring
      rw [e1, smul_dotProduct, smul_eq_mul] at c1
      rw [e2, smul_dotProduct, smul_eq_mul] at c2
      have d1 : (p' - p) ⬝ᵥ (yq - y) ≤ 0 := by
        by_contra hc; push Not at hc; nlinarith
      have d2 : (p - p') ⬝ᵥ (yq - y') ≤ 0 := by
        by_contra hc; push Not at hc; nlinarith
      have e3 : (p' - p) ⬝ᵥ (y' - y) = b - a := by
        rw [ha, hb, sub_dotProduct]
      have e4 : (p' - p) ⬝ᵥ (y' - y) = (p' - p) ⬝ᵥ (yq - y) + (p - p') ⬝ᵥ (yq - y') := by
        have : (p - p') = -(p' - p) := by rw [neg_sub]
        rw [this, neg_dotProduct, dotProduct_sub, dotProduct_sub, dotProduct_sub]
        ring
      linarith

end MWG.ConsumerChoice
