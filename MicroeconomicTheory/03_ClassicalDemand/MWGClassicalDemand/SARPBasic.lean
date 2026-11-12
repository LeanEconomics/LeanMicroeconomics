/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGClassicalDemand.Basic
import MWGConsumerChoice.WeakAxiom
import MWGConsumerChoice.RevealedData
import MWGPreferenceChoice.Rationalization
import ChoicePreferenceUtility.SGARP
import RevealedPreference.MarketData
import Mathlib.Order.Extension.Linear
import Mathlib.Logic.Relation

/-!
# The strong axiom of revealed preference

MWG, Section 3.J, pp. 91-92.

* The abstract setting of the small-type remark on p. 92: menus `B i` indexed by `i : I` and a
  single-valued choice `c i`. The relation `x ≻¹ y` ("directly revealed preferred") holds when
  `x = c i`, `y ∈ B i` and `y ≠ x`; `≻²` is its transitive closure. If `≻²` is irreflexive,
  Richter's argument (a linear extension of the partial order `= ∪ ≻²`, by Zorn's lemma via
  Mathlib's `LinearExtension`) gives a complete and transitive `≿` with `c i ≻ y` for every
  other `y ∈ B i` (`sarp_rationalization`); the converse holds for any rationalizing rational
  relation (`sarpAcyclic_of_rationalizes`).
* **Definition 3.J.1** for a Walrasian demand function (`StrongAxiom`), its equivalence with
  irreflexivity of `≻²` (`strongAxiom_iff_acyclic`), **Proposition 3.J.1** and its converse
  (`proposition_3_J_1`, `strongAxiom_of_rationalizes`, `proposition_3_J_1_iff`), and the strong
  axiom implying the weak axiom of Chapter 2 (`weakAxiom_of_strongAxiom`).
* Bridges: Kreps Chapter 1's SGARP and Proposition 1.23 (`sgarp_of_strongAxiom`,
  `strongAxiom_iff_sgarp`), Kreps Chapter 4's GARP for finite market data drawn from a demand
  function (`garp_of_strongAxiom`), MWG Chapter 1's choice structures
  (`chapter1_sarp_rationalizable`),
  and the violation of the strong axiom by the data of Example 2.F.1 (`example_2_F_1_not_sa`).

Departure (correction C1): as printed, Definition 3.J.1 quantifies over every list
`(p¹, w¹), ..., (p^N, w^N)`, including `N = 1`, where it demands `p¹·x(p¹, w¹) > w¹`; no
demand function with `x(p, w) ∈ B_{p,w}` satisfies that (`strongAxiomPrinted_false`). The
lists must have `N ≥ 2`; `StrongAxiom` indexes them `0, ..., N` with `N ≥ 1`.
-/

namespace MWG.ClassicalDemand

open MWG.ConsumerChoice Kreps.PreferenceProperties

variable {X I : Type*}

/-- **Proof of Proposition 3.J.1** (MWG, p. 92), abstract form. `a ≻¹ b`: for some menu `i`,
`a = c i` is chosen, `b ∈ B i` is available and `b ≠ a`. -/
def sarpDirect (B : I → Set X) (c : I → X) (a b : X) : Prop :=
  ∃ i, c i = a ∧ b ∈ B i ∧ b ≠ a

/-- **Proof of Proposition 3.J.1** (MWG, p. 92), abstract form. `≻²` is irreflexive: no
chain `a ≻¹ ⋯ ≻¹ a`. -/
def SarpAcyclic (B : I → Set X) (c : I → X) : Prop :=
  ∀ a, ¬Relation.TransGen (sarpDirect B c) a a

/-- **Proposition 3.J.1** (MWG, p. 91), abstract form. `≿` rationalizes the single-valued
choice `c`: `c i ≻ y` for every `y ∈ B i` with `y ≠ c i`. -/
def RationalizesChoice (r : X → X → Prop) (B : I → Set X) (c : I → X) : Prop :=
  ∀ i, ∀ y ∈ B i, y ≠ c i → Strict r (c i) y

/-- Strict preference of a rational relation is transitive. -/
theorem sarp_strict_trans {r : X → X → Prop} (hr : Rational r) {a b d : X}
    (hab : Strict r a b) (hbd : Strict r b d) : Strict r a d :=
  ⟨hr.2 a b d hab.1 hbd.1, fun hda => hbd.2 (hr.2 d a b hda hab.1)⟩

/-- **Proof of Proposition 3.J.1** (MWG, p. 92), abstract form (the remark that only
single-valuedness is used). If `≻²` is irreflexive, a total extension `≻³` of `≻²` gives a
rational `≿` (`x ≿ y` iff `x = y` or `x ≻³ y`) that rationalizes the choices and extends
`≻²`. -/
theorem sarp_rationalization {B : I → Set X} {c : I → X} (h : SarpAcyclic B c) :
    ∃ r : X → X → Prop, Rational r ∧ RationalizesChoice r B c ∧
      ∀ a b, Relation.TransGen (sarpDirect B c) a b → Strict r a b := by
  classical
  let : PartialOrder X :=
    { le := fun a b => a = b ∨ Relation.TransGen (sarpDirect B c) b a
      le_refl := fun _ => Or.inl rfl
      le_trans := by
        rintro a b d (rfl | hab) (rfl | hbd)
        · exact Or.inl rfl
        · exact Or.inr hbd
        · exact Or.inr hab
        · exact Or.inr (hbd.trans hab)
      le_antisymm := by
        rintro a b (rfl | hab) (hba | hba)
        · rfl
        · rfl
        · exact hba.symm
        · exact absurd (hab.trans hba) (h b) }
  let f : X → LinearExtension X := fun a => toLinearExtension a
  have hflift : StrictMono (toLinearExtension (α := X)) :=
    toLinearExtension.monotone.strictMono_of_injective (fun _ _ h => h)
  have hlt : ∀ a b, Relation.TransGen (sarpDirect B c) a b → f b < f a := by
    intro a b hab
    apply hflift
    refine lt_iff_le_not_ge.mpr ⟨Or.inr hab, ?_⟩
    rintro (hba | hba)
    · subst hba
      exact h a hab
    · exact h a (hab.trans hba)
  refine ⟨fun a b => f b ≤ f a, ⟨fun a b => le_total (f b) (f a),
    fun _ _ _ hab hbd => hbd.trans hab⟩, ?_, ?_⟩
  · intro i y hy hne
    have := hlt (c i) y (Relation.TransGen.single ⟨i, rfl, hy, hne⟩)
    exact ⟨this.le, not_le.mpr this⟩
  · intro a b hab
    have := hlt a b hab
    exact ⟨this.le, not_le.mpr this⟩

/-- **Section 3.J** (MWG, p. 91): "the SA is satisfied if demand originates in rational
preferences", abstract form. A rationalizing rational relation makes every `≻²`-chain strict,
so `≻²` is irreflexive. -/
theorem sarpAcyclic_of_rationalizes {B : I → Set X} {c : I → X} {r : X → X → Prop}
    (hr : Rational r) (h : RationalizesChoice r B c) : SarpAcyclic B c := by
  have key : ∀ a b, Relation.TransGen (sarpDirect B c) a b → Strict r a b := by
    intro a b hab
    induction hab with
    | single hab =>
      obtain ⟨i, hi, hb, hne⟩ := hab
      subst hi
      exact h i _ hb hne
    | tail _ hbd ih =>
      obtain ⟨i, hi, hd, hne⟩ := hbd
      subst hi
      exact sarp_strict_trans hr ih (h i _ hd hne)
  intro a ha
  exact (key a a ha).2 (key a a ha).1

/-- **Proposition 3.J.1** (MWG, pp. 91-92), abstract form, both directions: single-valued
choice is rationalizable by a rational preference iff `≻²` is irreflexive. -/
theorem sarpAcyclic_iff_rationalizable {B : I → Set X} {c : I → X} :
    SarpAcyclic B c ↔ ∃ r : X → X → Prop, Rational r ∧ RationalizesChoice r B c :=
  ⟨fun h => (sarp_rationalization h).imp fun _ h => ⟨h.1, h.2.1⟩,
    fun ⟨_, hr, h⟩ => sarpAcyclic_of_rationalizes hr h⟩

/-- A transitive-closure chain written as a finite sequence `a = g 0, ..., g N = b`, `N ≥ 1`. -/
theorem sarp_transGen_iff_chain {R : X → X → Prop} {a b : X} :
    Relation.TransGen R a b ↔
      ∃ N, 1 ≤ N ∧ ∃ g : ℕ → X, g 0 = a ∧ g N = b ∧ ∀ n, n < N → R (g n) (g (n + 1)) := by
  classical
  constructor
  · intro h
    induction h with
    | @single d hd =>
      refine ⟨1, le_rfl, fun n => if n = 0 then a else d, by simp, by simp, ?_⟩
      intro n hn
      obtain rfl : n = 0 := by omega
      simpa using hd
    | @tail d e _ hde ih =>
      obtain ⟨N, hN, g, h0, hNd, hstep⟩ := ih
      refine ⟨N + 1, by omega, fun n => if n ≤ N then g n else e, ?_, ?_, ?_⟩
      · simpa using h0
      · simp
      · intro n hn
        by_cases hnN : n < N
        · have h1 : n ≤ N := hnN.le
          have h2 : n + 1 ≤ N := hnN
          simp only [h1, h2, ↓reduceIte]
          exact hstep n hnN
        · obtain rfl : n = N := by omega
          simp only [le_refl, ↓reduceIte, Nat.not_succ_le_self]
          rw [hNd]
          exact hde
  · rintro ⟨N, hN, g, h0, hNb, hstep⟩
    subst h0 hNb
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    clear hN
    induction M with
    | zero => exact Relation.TransGen.single (hstep 0 (by omega))
    | succ M ih =>
      exact (ih fun n hn => hstep n (by omega)).tail (hstep (M + 1) (by omega))

variable {L : ℕ}

/-- The price-wealth situations `(p, w) ≫ 0`, used as menu indices. -/
abbrev SarpPWIndex (L : ℕ) := {q : (Fin L → ℝ) × ℝ // PWDomain q.1 q.2}

/-- The half-space `{y : p·y ≤ w}` of a situation (the affordability condition of `≻¹`). -/
def sarpHalfspace (q : SarpPWIndex L) : Set (Fin L → ℝ) := {y | q.1.1 ⬝ᵥ y ≤ q.1.2}

/-- The choice `x(p, w)` of a demand function at a situation. -/
def sarpChoice (x : DemandFunction L) (q : SarpPWIndex L) : Fin L → ℝ := x q.1.1 q.1.2

/-- **Proof of Proposition 3.J.1** (MWG, p. 92). `a ≻¹ b` ("directly revealed preferred"):
`a ≠ b`, `a = x(p, w)` and `p·b ≤ w` for some `(p, w) ≫ 0`. -/
def sarpRevealedDirect (x : DemandFunction L) (a b : Fin L → ℝ) : Prop :=
  ∃ p w, PWDomain p w ∧ x p w = a ∧ p ⬝ᵥ b ≤ w ∧ b ≠ a

/-- **Proof of Proposition 3.J.1** (MWG, p. 92). `≻²` ("directly or indirectly revealed
preferred"): a chain `a ≻¹ x² ≻¹ ⋯ ≻¹ b`. -/
def sarpRevealedIndirect (x : DemandFunction L) : (Fin L → ℝ) → (Fin L → ℝ) → Prop :=
  Relation.TransGen (sarpRevealedDirect x)

/-- `≻¹` of a demand function is the abstract `≻¹` of its half-space menus. -/
theorem sarpRevealedDirect_eq (x : DemandFunction L) :
    sarpRevealedDirect x = sarpDirect sarpHalfspace (sarpChoice x) := by
  funext a b
  apply propext
  constructor
  · rintro ⟨p, w, hd, ha, hb, hne⟩
    exact ⟨⟨(p, w), hd⟩, ha, hb, hne⟩
  · rintro ⟨q, ha, hb, hne⟩
    exact ⟨q.1.1, q.1.2, q.2, ha, hb, hne⟩

/-- **Proof of Proposition 3.J.1** (MWG, p. 92). "By construction, `≻²` is transitive." -/
theorem sarpRevealedIndirect_trans {x : DemandFunction L} {a b d : Fin L → ℝ}
    (hab : sarpRevealedIndirect x a b) (hbd : sarpRevealedIndirect x b d) :
    sarpRevealedIndirect x a d :=
  Relation.TransGen.trans hab hbd

/-- **Definition 3.J.1** (MWG, p. 91), with the lists of length at least two (correction C1).
For every list `(p⁰, w⁰), ..., (p^N, w^N)` of price-wealth situations, `N ≥ 1`, with
`x(pⁿ⁺¹, wⁿ⁺¹) ≠ x(pⁿ, wⁿ)` and `pⁿ·x(pⁿ⁺¹, wⁿ⁺¹) ≤ wⁿ` for all `n < N`, we have
`p^N·x(p⁰, w⁰) > w^N`. -/
def StrongAxiom (x : DemandFunction L) : Prop :=
  ∀ (N : ℕ) (p : ℕ → Fin L → ℝ) (w : ℕ → ℝ), 1 ≤ N → (∀ n, n ≤ N → PWDomain (p n) (w n)) →
    (∀ n, n < N → x (p (n + 1)) (w (n + 1)) ≠ x (p n) (w n)) →
    (∀ n, n < N → p n ⬝ᵥ x (p (n + 1)) (w (n + 1)) ≤ w n) → w N < p N ⬝ᵥ x (p 0) (w 0)

/-- **Definition 3.J.1** (MWG, p. 91) exactly as printed: lists of every length `N ≥ 1`
(here `N ≥ 0`, indices `0, ..., N`). -/
def StrongAxiomPrinted (x : DemandFunction L) : Prop :=
  ∀ (N : ℕ) (p : ℕ → Fin L → ℝ) (w : ℕ → ℝ), (∀ n, n ≤ N → PWDomain (p n) (w n)) →
    (∀ n, n < N → x (p (n + 1)) (w (n + 1)) ≠ x (p n) (w n)) →
    (∀ n, n < N → p n ⬝ᵥ x (p (n + 1)) (w (n + 1)) ≤ w n) → w N < p N ⬝ᵥ x (p 0) (w 0)

/-- **Correction C1** (Definition 3.J.1, p. 91). The one-element list makes the printed
definition demand `p·x(p, w) > w`, so no demand function that is affordable at some
`(p, w) ≫ 0` satisfies it. -/
theorem strongAxiomPrinted_false {x : DemandFunction L} {p : Fin L → ℝ} {w : ℝ}
    (hd : PWDomain p w) (hx : p ⬝ᵥ x p w ≤ w) : ¬StrongAxiomPrinted x := by
  intro h
  have := h 0 (fun _ => p) (fun _ => w) (fun _ _ => hd) (fun n hn => absurd hn (by omega))
    (fun n hn => absurd hn (by omega))
  linarith

/-- **Correction C1**. In particular no demand function satisfying Walras' law satisfies the
printed definition. -/
theorem strongAxiomPrinted_false_of_walrasLaw {x : DemandFunction L} (hW : WalrasLaw x) :
    ¬StrongAxiomPrinted x := by
  have hd : PWDomain (fun _ : Fin L => (1 : ℝ)) 1 := ⟨fun _ => one_pos, one_pos⟩
  exact strongAxiomPrinted_false hd (hW _ _ hd).le

/-- The corrected definition is the printed one restricted to lists of length at least two. -/
theorem strongAxiom_of_printed {x : DemandFunction L} (h : StrongAxiomPrinted x) :
    StrongAxiom x := fun N p w _ hd hne hle => h N p w hd hne hle

/-- **Proof of Proposition 3.J.1** (MWG, p. 92): "according to the SA, `≻²` is irreflexive",
and conversely. The strong axiom holds iff no chain `a ≻¹ ⋯ ≻¹ a` exists. -/
theorem strongAxiom_iff_acyclic {x : DemandFunction L} :
    StrongAxiom x ↔ ∀ a, ¬sarpRevealedIndirect x a a := by
  constructor
  · intro hSA a ha
    obtain ⟨N, hN, g, h0, hN', hstep⟩ := sarp_transGen_iff_chain.mp ha
    have hq : ∀ n, ∃ q : (Fin L → ℝ) × ℝ, n < N → PWDomain q.1 q.2 ∧ x q.1 q.2 = g n ∧
        q.1 ⬝ᵥ g (n + 1) ≤ q.2 ∧ g (n + 1) ≠ g n := by
      intro n
      by_cases hn : n < N
      · obtain ⟨p, w, hd, hx, hle, hne⟩ := hstep n hn
        exact ⟨(p, w), fun _ => ⟨hd, hx, hle, hne⟩⟩
      · exact ⟨(0, 0), fun h => absurd h hn⟩
    choose q hq using hq
    have hN2 : 2 ≤ N := by
      by_contra hlt
      obtain rfl : N = 1 := by omega
      exact (hq 0 one_pos).2.2.2 (by rw [hN', h0])
    have hlast := hq (N - 1) (by omega)
    rw [Nat.sub_add_cancel hN, hN', ← h0] at hlast
    have := hSA (N - 1) (fun n => (q n).1) (fun n => (q n).2) (by omega)
      (fun n hn => (hq n (by omega)).1)
      (fun n hn => by
        rw [(hq (n + 1) (by omega)).2.1, (hq n (by omega)).2.1]
        exact (hq n (by omega)).2.2.2)
      (fun n hn => by
        rw [(hq (n + 1) (by omega)).2.1]
        exact (hq n (by omega)).2.2.1)
    rw [(hq 0 (by omega)).2.1] at this
    linarith [hlast.2.2.1]
  · intro hac N p w hN hd hne hle
    by_contra hlt
    rw [not_lt] at hlt
    have hchain : sarpRevealedIndirect x (x (p 0) (w 0)) (x (p N) (w N)) :=
      sarp_transGen_iff_chain.mpr ⟨N, hN, fun n => x (p n) (w n), rfl, rfl,
        fun n hn => ⟨p n, w n, hd n hn.le, rfl, hle n hn, hne n hn⟩⟩
    by_cases heq : x (p N) (w N) = x (p 0) (w 0)
    · rw [heq] at hchain
      exact hac _ hchain
    · exact hac _ (hchain.tail ⟨p N, w N, hd N le_rfl, rfl, hlt, fun h => heq h.symm⟩)

/-- **Proposition 3.J.1** (MWG, pp. 91-92). If the Walrasian demand function satisfies the
strong axiom, there is a rational preference relation `≿` that rationalizes it:
`x(p, w) ≻ y` for every `y ≠ x(p, w)` with `y ∈ B_{p,w}`, at every `(p, w) ≫ 0`. -/
theorem proposition_3_J_1 {x : DemandFunction L} (h : StrongAxiom x) :
    ∃ r : (Fin L → ℝ) → (Fin L → ℝ) → Prop, Rational r ∧
      ∀ p w, PWDomain p w → ∀ y ∈ budgetSet p w, y ≠ x p w → Strict r (x p w) y := by
  have hac : SarpAcyclic sarpHalfspace (sarpChoice x) := by
    intro a ha
    rw [← sarpRevealedDirect_eq] at ha
    exact strongAxiom_iff_acyclic.mp h a ha
  obtain ⟨r, hr, hrat, -⟩ := sarp_rationalization hac
  exact ⟨r, hr, fun p w hd y hy hne => hrat ⟨(p, w), hd⟩ y hy.2 hne⟩

/-- **Proof of Proposition 3.J.1** (MWG, p. 92), in full: the relation constructed from `≻³`
extends `≻²` and ranks `x(p, w)` strictly above every other `y` with `p·y ≤ w` (not only
those in `ℝ^L_+`). -/
theorem proposition_3_J_1_extends {x : DemandFunction L} (h : StrongAxiom x) :
    ∃ r : (Fin L → ℝ) → (Fin L → ℝ) → Prop, Rational r ∧
      (∀ p w, PWDomain p w → ∀ y, p ⬝ᵥ y ≤ w → y ≠ x p w → Strict r (x p w) y) ∧
      ∀ a b, sarpRevealedIndirect x a b → Strict r a b := by
  have hac : SarpAcyclic sarpHalfspace (sarpChoice x) := by
    intro a ha
    rw [← sarpRevealedDirect_eq] at ha
    exact strongAxiom_iff_acyclic.mp h a ha
  obtain ⟨r, hr, hrat, hext⟩ := sarp_rationalization hac
  refine ⟨r, hr, fun p w hd y hy hne => hrat ⟨(p, w), hd⟩ y hy hne, fun a b hab => ?_⟩
  rw [sarpRevealedIndirect, sarpRevealedDirect_eq] at hab
  exact hext a b hab

/-- **Section 3.J** (MWG, p. 91): "the SA is satisfied if demand originates in rational
preferences". If a rational `≿` rationalizes a demand function with values in `ℝ^L_+`, the
demand satisfies the strong axiom. -/
theorem strongAxiom_of_rationalizes {x : DemandFunction L} (hv : ValuesInOrthant x)
    {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop} (hr : Rational r)
    (h : ∀ p w, PWDomain p w → ∀ y ∈ budgetSet p w, y ≠ x p w → Strict r (x p w) y) :
    StrongAxiom x := by
  have key : ∀ a b, sarpRevealedIndirect x a b → b ∈ nonnegOrthant L → Strict r a b := by
    intro a b hab
    induction hab with
    | single hab =>
      intro hb
      obtain ⟨p, w, hd, hx, hle, hne⟩ := hab
      subst hx
      exact h p w hd _ ⟨hb, hle⟩ hne
    | tail _ hbd ih =>
      intro hd'
      obtain ⟨p, w, hd, hx, hle, hne⟩ := hbd
      subst hx
      exact sarp_strict_trans hr (ih (hv p w hd)) (h p w hd _ ⟨hd', hle⟩ hne)
  rw [strongAxiom_iff_acyclic]
  intro a ha
  obtain ⟨b, ⟨p, w, hd, hx, -, -⟩, -⟩ := Relation.TransGen.head'_iff.mp ha
  have ha0 : a ∈ nonnegOrthant L := hx ▸ hv p w hd
  exact (key a a ha ha0).2 (key a a ha ha0).1

/-- **Proposition 3.J.1** with its converse (MWG, p. 91): for a demand function with values in
`ℝ^L_+`, the strong axiom holds iff some rational preference relation rationalizes it. -/
theorem proposition_3_J_1_iff {x : DemandFunction L} (hv : ValuesInOrthant x) :
    StrongAxiom x ↔ ∃ r : (Fin L → ℝ) → (Fin L → ℝ) → Prop, Rational r ∧
      ∀ p w, PWDomain p w → ∀ y ∈ budgetSet p w, y ≠ x p w → Strict r (x p w) y :=
  ⟨proposition_3_J_1, fun ⟨_, hr, h⟩ => strongAxiom_of_rationalizes hv hr h⟩

/-- **Section 3.J** (MWG, p. 92). The strong axiom implies the weak axiom (Definition 2.F.1):
the weak axiom is the case of lists of length two. -/
theorem weakAxiom_of_strongAxiom {x : DemandFunction L} (h : StrongAxiom x) :
    WeakAxiom x := by
  classical
  intro p w p' w' hd hd' hle hne
  have := h 1 (fun n => if n = 0 then p else p') (fun n => if n = 0 then w else w') le_rfl
    (fun n hn => by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn with rfl | rfl
      · simpa using hd
      · simpa using hd')
    (fun n hn => by
      obtain rfl : n = 0 := by omega
      simpa using hne)
    (fun n hn => by
      obtain rfl : n = 0 := by omega
      simpa using hle)
  simpa using this

/-- The Walrasian menus `B_{p,w}`, indexed by situations, for Kreps's revealed preference. -/
def sarpMenus (q : SarpPWIndex L) : Set (Fin L → ℝ) := budgetSet q.1.1 q.1.2

/-- The chosen sets `{x(p, w)}` of a demand function, for Kreps's revealed preference. -/
def sarpChosen (x : DemandFunction L) (q : SarpPWIndex L) : Set (Fin L → ℝ) := {x q.1.1 q.1.2}

/-- Bridge to Kreps Chapter 1. For a demand function with `x(p, w) ∈ B_{p,w}` and a rational
`≿`, MWG's rationalization of Proposition 3.J.1 is Kreps's exact rationalization of the data
`(B_{p,w}, {x(p, w)})` (`RationalizesData`). -/
theorem sarp_rationalizes_iff_rationalizesData {x : DemandFunction L}
    (hfeas : ∀ p w, PWDomain p w → x p w ∈ budgetSet p w)
    {r : (Fin L → ℝ) → (Fin L → ℝ) → Prop} (hr : Rational r) :
    (∀ p w, PWDomain p w → ∀ y ∈ budgetSet p w, y ≠ x p w → Strict r (x p w) y) ↔
      Kreps.ChoicePreferenceUtility.RationalizesData r sarpMenus (sarpChosen x) := by
  constructor
  · intro h q
    ext z
    constructor
    · intro hz
      rw [sarpChosen, Set.mem_singleton_iff] at hz
      subst hz
      refine ⟨hfeas _ _ q.2, fun y hy => ?_⟩
      by_cases hyx : y = x q.1.1 q.1.2
      · rw [hyx]
        exact (hr.1 _ _).elim id id
      · exact (h _ _ q.2 y hy hyx).1
    · rintro ⟨hz, hbest⟩
      by_contra hne
      exact (h _ _ q.2 z hz hne).2 (hbest _ (hfeas _ _ q.2))
  · intro h p w hd y hy hne
    have hx : x p w ∈ Kreps.ChoicePreferenceUtility.PrefChoice r (sarpMenus ⟨(p, w), hd⟩) := by
      rw [← h ⟨(p, w), hd⟩]
      rfl
    refine ⟨hx.2 y hy, fun hyx => hne ?_⟩
    have hy' : y ∈ Kreps.ChoicePreferenceUtility.PrefChoice r (sarpMenus ⟨(p, w), hd⟩) :=
      ⟨hy, fun z hz => hr.2 _ _ _ hyx (hx.2 z hz)⟩
    rw [← h ⟨(p, w), hd⟩] at hy'
    exact hy'

/-- Bridge to Kreps Chapter 1 (Definition 1.22). A demand function with `x(p, w) ∈ B_{p,w}`
satisfying the strong axiom satisfies SGARP on the Walrasian data. -/
theorem sgarp_of_strongAxiom {x : DemandFunction L}
    (hfeas : ∀ p w, PWDomain p w → x p w ∈ budgetSet p w) (h : StrongAxiom x) :
    Kreps.ChoicePreferenceUtility.SGARP sarpMenus (sarpChosen x) := by
  obtain ⟨r, hr, hrat⟩ := proposition_3_J_1 h
  exact Kreps.ChoicePreferenceUtility.sgarp_of_rationalizes hr
    ((sarp_rationalizes_iff_rationalizesData hfeas hr).mp hrat)

/-- Bridge to Kreps's **Proposition 1.23**: for a demand function with values in `B_{p,w}`, the
strong axiom is SGARP of the Walrasian data. The direction SGARP ⇒ SA goes through Kreps's
rationalization theorem, giving a second proof of Proposition 3.J.1 in this case. -/
theorem strongAxiom_iff_sgarp {x : DemandFunction L}
    (hfeas : ∀ p w, PWDomain p w → x p w ∈ budgetSet p w) :
    StrongAxiom x ↔ Kreps.ChoicePreferenceUtility.SGARP sarpMenus (sarpChosen x) := by
  refine ⟨sgarp_of_strongAxiom hfeas, fun h => ?_⟩
  obtain ⟨r, hr, hdata⟩ := Kreps.ChoicePreferenceUtility.rationalizes_of_sgarp
    (fun q z hz => by
      change z = _ at hz
      subst hz
      exact hfeas _ _ q.2)
    (fun q => Set.singleton_nonempty _) h
  exact strongAxiom_of_rationalizes (fun p w hd => (hfeas p w hd).1) hr
    ((sarp_rationalizes_iff_rationalizesData hfeas hr).mpr hdata)

/-- **Section 3.J, small type** (MWG, p. 92): "provided choice is single-valued, the same result
applies to the abstract theory of choice of Chapter 1". A choice structure (Section 1.C) with
single-valued choice `C(B) = {c B}` and irreflexive `≻²` is rationalizable (Definition 1.D.1). -/
theorem chapter1_sarp_rationalizable (S : MWG.PreferenceChoice.ChoiceStructure X) (c : Set X → X)
    (hc : ∀ B ∈ S.budgets, S.C B = {c B})
    (h : SarpAcyclic (fun B : S.budgets => (B : Set X)) (fun B => c B)) :
    MWG.PreferenceChoice.Rationalizable S := by
  obtain ⟨r, hr, hrat, -⟩ := sarp_rationalization h
  refine ⟨r, hr, fun B hB => ?_⟩
  have hcB : c B ∈ B := by
    have := S.choice_subset B hB
    rw [hc B hB] at this
    exact this rfl
  rw [hc B hB]
  ext z
  constructor
  · intro hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    refine ⟨hcB, fun y hy => ?_⟩
    by_cases hyc : y = c B
    · rw [hyc]
      exact (hr.1 _ _).elim id id
    · exact (hrat ⟨B, hB⟩ y hy hyc).1
  · rintro ⟨hz, hbest⟩
    by_contra hne
    exact (hrat ⟨B, hB⟩ z hz hne).2 (hbest _ hcB)

/-- **Section 3.J** (MWG, p. 91): "the SA was violated in Example 2.F.1". In the data of
Example 2.F.1 (menus `B_{pⁱ, 8}`, choices `xⁱ`), `x¹ ≻¹ x³ ≻¹ x² ≻¹ x¹`, so `≻²` is not
irreflexive. -/
theorem example_2_F_1_not_sa :
    ¬SarpAcyclic (fun i : Fin 3 => budgetSet (example_2_F_1_prices i) 8)
      example_2_F_1_choices := by
  obtain ⟨⟨h21, n21⟩, ⟨h10, n10⟩, ⟨h02, n02⟩⟩ := exercise_2_F_2_cycle
  have hnn : ∀ i, example_2_F_1_choices i ∈ nonnegOrthant 3 := by
    intro i l
    fin_cases i <;> fin_cases l <;> simp [example_2_F_1_choices]
  intro h
  apply h (example_2_F_1_choices 0)
  exact (((Relation.TransGen.single ⟨0, rfl, ⟨hnn 2, h02⟩, n02⟩).tail
    ⟨2, rfl, ⟨hnn 1, h21⟩, n21⟩).tail ⟨1, rfl, ⟨hnn 0, h10⟩, n10⟩)

/-- Bridge to Kreps Chapter 4 (Definition 4.2). Finite market data drawn from a demand function
that satisfies Walras' law and the strong axiom (observations `xⁱ = x(pⁱ, wⁱ)`, `wⁱ > 0`)
satisfy GARP: a revealed strict cycle would give a `≻²`-cycle of distinct demanded bundles. -/
theorem garp_of_strongAxiom {I : Type*} {x : DemandFunction L} (hW : WalrasLaw x)
    (hSA : StrongAxiom x) (D : Kreps.RevealedPreference.MarketData I L)
    (hobs : ∀ i, (D.bundle i).val = x (D.price i) (D.income i)) (hinc : ∀ i, 0 < D.income i) :
    Kreps.RevealedPreference.GARP D := by
  rw [strongAxiom_iff_acyclic] at hSA
  have hdom : ∀ j, PWDomain (D.price j) (D.income j) := fun j => ⟨D.price_pos j, hinc j⟩
  have hcost : ∀ j k, D.cost j k = D.price j ⬝ᵥ x (D.price k) (D.income k) - D.income j := by
    intro j k
    rw [Kreps.RevealedPreference.MarketData.cost, hobs k]
    rfl
  have hweak : ∀ j k, Kreps.RevealedPreference.RevealedWeak D.cost j k →
      Relation.ReflTransGen (sarpRevealedDirect x) (x (D.price j) (D.income j))
        (x (D.price k) (D.income k)) := by
    intro j k h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | @tail k' k _ hstep ih =>
      by_cases heq : x (D.price k) (D.income k) = x (D.price k') (D.income k')
      · rw [heq]
        exact ih
      · refine ih.tail ⟨D.price k', D.income k', hdom k', rfl, ?_, heq⟩
        have := hstep
        rw [Kreps.RevealedPreference.DirectWeak, hcost] at this
        linarith
  intro i hcyc
  obtain ⟨a, b, hia, hab, hbi⟩ := hcyc
  have hstrict : sarpRevealedDirect x (x (D.price a) (D.income a))
      (x (D.price b) (D.income b)) := by
    have h := hab
    rw [Kreps.RevealedPreference.DirectStrict, hcost] at h
    refine ⟨D.price a, D.income a, hdom a, rfl, by linarith, fun heq => ?_⟩
    rw [heq, hW _ _ (hdom a)] at h
    linarith
  exact hSA _ (Relation.TransGen.trans_right (hweak i a hia)
    (Relation.TransGen.head' hstrict (hweak b i hbi)))

end MWG.ClassicalDemand
