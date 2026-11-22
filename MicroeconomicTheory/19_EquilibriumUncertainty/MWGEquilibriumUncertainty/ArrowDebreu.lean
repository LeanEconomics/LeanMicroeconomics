/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGEquilibriumUncertainty.Basic
import MWGWelfareTheorems.FirstWelfare
import MWGWelfareTheorems.SecondWelfare

/-!
# Arrow-Debreu equilibrium (MWG Section 19.C, pp. 691-693)

An economy with uncertainty (`CEconomy`) has consumption sets `Xᵢ ⊆ ℝ^{LS}`, preferences `≿ᵢ`,
endowments `ωᵢ ∈ ℝ^{LS}`, production sets `Yⱼ ⊆ ℝ^{LS}` and shares `θⱼᵢ`.

* **Definition 19.C.1**: Arrow-Debreu equilibrium (`CEconomy.IsADEqm`).
* An Arrow-Debreu equilibrium *is* a Walrasian equilibrium (Definition 16.B.3) of the economy
  with the `LS` contingent commodities, ordered as in Definition 19.B.1 (`flat`, `unflat`,
  `isADEqm_iff_isWalrasEqm`). Through this bridge the welfare theorems of Chapter 16 apply
  without modification (p. 692): `adEqm_paretoOptimal` (Proposition 16.C.1) and
  `paretoOptimal_supported` (Proposition 16.D.1).
* Exchange economies with utility functions on `ℝ^{LS}_+` (`IsADEqmU`, used from Section 19.D
  on) are the case of no firms (`isADEqmU_iff`).
* **Exercise 19.C.1** and the claim of p. 692: concave Bernoulli utilities give a concave
  expected utility on `ℝ^{LS}_+`, hence convex preferences (`exercise_19_C_1`,
  `euPref_convex`).
* The instance: expected utility with strictly positive probabilities and strongly monotone
  Bernoulli utilities is rational and locally nonsatiated, so Arrow-Debreu equilibria of such
  economies are Pareto optimal (`adEqm_paretoOptimal_eu`).
-/

namespace MWG.EquilibriumUncertainty

open MWG.ClassicalDemand MWG.ConsumerChoice MWG.Production MWG.WelfareTheorems
open MWG.CompetitiveMarkets (Allocation)

variable {S L : ℕ}

/-! ## Ordering the contingent commodities -/

/-- The contingent vector as a vector of `ℝ^{LS}` with the book's ordering
`(x₁₁, …, x_{L1}, …, x_{1S}, …, x_{LS})` (Definition 19.B.1). -/
def flat (x : CVec S L) : Fin (S * L) → ℝ :=
  fun k => x (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2

/-- The inverse of `flat`. -/
def unflat (v : Fin (S * L) → ℝ) : CVec S L := fun s l => v (finProdFinEquiv (s, l))

theorem unflat_flat (x : CVec S L) : unflat (flat x) = x := by
  funext s l; simp [unflat, flat]

theorem flat_unflat (v : Fin (S * L) → ℝ) : flat (unflat v) = v := by
  funext k; simp only [unflat, flat]; rw [Prod.mk.eta, Equiv.apply_symm_apply]

theorem flat_injective : Function.Injective (flat (S := S) (L := L)) := fun a b h => by
  rw [← unflat_flat a, h, unflat_flat]

/-- The value `p·x` is the dot product in `ℝ^{LS}`. -/
theorem flat_dotProduct (p x : CVec S L) : flat p ⬝ᵥ flat x = cval p x := by
  unfold dotProduct cval flat
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
  simp [dotProduct]

theorem flat_add (x y : CVec S L) : flat (x + y) = flat x + flat y := rfl

theorem flat_smul (a : ℝ) (x : CVec S L) : flat (a • x) = a • flat x := rfl

theorem flat_sum {ι : Type*} (t : Finset ι) (x : ι → CVec S L) :
    flat (∑ i ∈ t, x i) = ∑ i ∈ t, flat (x i) := by
  funext k; simp [flat, Finset.sum_apply]

theorem unflat_add (v w : Fin (S * L) → ℝ) : unflat (v + w) = unflat v + unflat w := rfl

theorem unflat_smul (a : ℝ) (v : Fin (S * L) → ℝ) : unflat (a • v) = a • unflat v := rfl

/-! ## The economy and Definition 19.C.1 -/

/-- **Sections 19.B-19.C** (MWG, pp. 688-691). An economy under uncertainty: consumption sets
`Xᵢ ⊆ ℝ^{LS}`, preference relations (`pref i x x'` reads `x ≿ᵢ x'`), endowments `ωᵢ ∈ ℝ^{LS}`,
production sets `Yⱼ ⊆ ℝ^{LS}` and shares `θ j i` of firm `j` owned by consumer `i`. -/
structure CEconomy (ι κ : Type*) (S L : ℕ) where
  /-- Consumption sets. -/
  X : ι → Set (CVec S L)
  /-- Preference relations. -/
  pref : ι → CVec S L → CVec S L → Prop
  /-- Endowments. -/
  ω : ι → CVec S L
  /-- Production sets. -/
  Y : κ → Set (CVec S L)
  /-- Shares: `θ j i` is the share of firm `j` owned by consumer `i`. -/
  θ : κ → ι → ℝ

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Consumer `i`'s wealth `p·ωᵢ + ∑ⱼ θⱼᵢ p·yⱼ`. -/
def CEconomy.wealth (E : CEconomy ι κ S L) (y : κ → CVec S L) (p : CVec S L) (i : ι) : ℝ :=
  cval p (E.ω i) + ∑ j, E.θ j i * cval p (y j)

/-- **Definition 19.C.1** (MWG, p. 692). `(x*, y*)` and contingent prices `p ∈ ℝ^{LS}` form an
Arrow-Debreu equilibrium: (i) every `y*ⱼ` maximizes `p·yⱼ` on `Yⱼ`; (ii) every `x*ᵢ` is maximal
for `≿ᵢ` in `{xᵢ ∈ Xᵢ : p·xᵢ ≤ p·ωᵢ + ∑ⱼ θⱼᵢ p·y*ⱼ}`; (iii) `∑ᵢ x*ᵢ = ∑ⱼ y*ⱼ + ∑ᵢ ωᵢ`. -/
def CEconomy.IsADEqm (E : CEconomy ι κ S L) (x : ι → CVec S L) (y : κ → CVec S L)
    (p : CVec S L) : Prop :=
  (∀ j, y j ∈ E.Y j ∧ ∀ y' ∈ E.Y j, cval p y' ≤ cval p (y j)) ∧
    (∀ i, (x i ∈ E.X i ∧ cval p (x i) ≤ E.wealth y p i) ∧
      ∀ x' ∈ E.X i, cval p x' ≤ E.wealth y p i → E.pref i (x i) x') ∧
    ∑ i, x i = ∑ j, y j + ∑ i, E.ω i

/-- **p. 691**. The economy with the `LS` contingent commodities as an ordinary private ownership
economy of Chapter 16 (`L` there is `LS` here). -/
def CEconomy.toPriv (E : CEconomy ι κ S L) : PrivPrefEconomy ι κ (S * L) where
  X := fun i => unflat ⁻¹' E.X i
  pref := fun i a b => E.pref i (unflat a) (unflat b)
  Y := fun j => unflat ⁻¹' E.Y j
  ωi := fun i => flat (E.ω i)
  θ := fun i j => E.θ j i

/-- The allocation `(x, y)` in `ℝ^{LS}`. -/
def flatAlloc (x : ι → CVec S L) (y : κ → CVec S L) : Allocation ι κ (S * L) :=
  ⟨fun i => flat (x i), fun j => flat (y j)⟩

/-- **p. 692**. "The market economy just described is nothing but a particular case of the
economies we have studied": an Arrow-Debreu equilibrium is exactly a Walrasian equilibrium
(Definition 16.B.3) of the economy with `LS` contingent commodities. -/
theorem isADEqm_iff_isWalrasEqm (E : CEconomy ι κ S L) (x : ι → CVec S L)
    (y : κ → CVec S L) (p : CVec S L) :
    E.IsADEqm x y p ↔ E.toPriv.IsWalrasEqm (flatAlloc x y) (flat p) := by
  have hw : ∀ i, E.toPriv.wealth (flatAlloc x y) (flat p) i = E.wealth y p i := by
    intro i
    simp [PrivPrefEconomy.wealth, CEconomy.wealth, CEconomy.toPriv, flatAlloc,
      flat_dotProduct]
  rw [definition_16_B_3]
  simp only [hw]
  have hall : ∀ (P : (Fin (S * L) → ℝ) → Prop), (∀ v, P v) ↔ ∀ z : CVec S L, P (flat z) :=
    fun P => ⟨fun h z => h _, fun h v => by rw [← flat_unflat v]; exact h _⟩
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun j => ⟨?_, ?_⟩, fun i => ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · simp only [CEconomy.toPriv, flatAlloc, Set.mem_preimage, unflat_flat]; exact (h1 j).1
    · rw [hall]; intro z hz
      simp only [CEconomy.toPriv, Set.mem_preimage, unflat_flat] at hz
      simp only [flatAlloc, flat_dotProduct]; exact (h1 j).2 z hz
    · simp only [CEconomy.toPriv, flatAlloc, Set.mem_preimage, unflat_flat]
      exact (h2 i).1.1
    · simp only [flatAlloc, flat_dotProduct]; exact (h2 i).1.2
    · rw [hall]; intro z hz hb
      simp only [CEconomy.toPriv, Set.mem_preimage, unflat_flat, flatAlloc] at hz ⊢
      rw [flat_dotProduct] at hb
      exact (h2 i).2 z hz hb
    · simp only [flatAlloc, CEconomy.toPriv, ← flat_sum, ← flat_add]; rw [h3, add_comm]
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun j => ⟨?_, fun y' hy' => ?_⟩, fun i => ⟨⟨?_, ?_⟩, fun x' hx' hb => ?_⟩, ?_⟩
    · have := (h1 j).1
      simpa [CEconomy.toPriv, flatAlloc, unflat_flat] using this
    · have := (h1 j).2 (flat y') (by simpa [CEconomy.toPriv, unflat_flat] using hy')
      simpa [flatAlloc, flat_dotProduct] using this
    · have := (h2 i).1.1
      simpa [CEconomy.toPriv, flatAlloc, unflat_flat] using this
    · have := (h2 i).1.2
      simpa [flatAlloc, flat_dotProduct] using this
    · have := (h2 i).2 (flat x') (by simpa [CEconomy.toPriv, unflat_flat] using hx')
        (by rw [flat_dotProduct]; exact hb)
      simpa [CEconomy.toPriv, flatAlloc, unflat_flat] using this
    · apply flat_injective
      simp only [flatAlloc, CEconomy.toPriv] at h3
      rw [flat_add, flat_sum, flat_sum, flat_sum, h3, add_comm]

/-- **Definition 16.B.2** for the contingent economy: Pareto optimality of `(x, y)` in `ℝ^{LS}`. -/
def CEconomy.IsParetoOptimal (E : CEconomy ι κ S L) (x : ι → CVec S L) (y : κ → CVec S L) :
    Prop :=
  E.toPriv.toEconomy.IsParetoOptimal (flatAlloc x y)

/-- **p. 692** (Proposition 16.C.1 applied). With rational, locally nonsatiated preferences and
shares summing to one, every Arrow-Debreu equilibrium allocation is Pareto optimal: trading in
contingent commodities leads to an efficient allocation of risk. -/
theorem adEqm_paretoOptimal {E : CEconomy ι κ S L}
    (hrat : ∀ i, RationalOn (E.toPriv.X i) (E.toPriv.pref i))
    (hlns : ∀ i, LocallyNonsatiated (E.toPriv.X i) (E.toPriv.pref i))
    (hθ : ∀ j, ∑ i, E.θ j i = 1) {x : ι → CVec S L} {y : κ → CVec S L} {p : CVec S L}
    (h : E.IsADEqm x y p) : E.IsParetoOptimal x y :=
  proposition_16_C_1_walras hrat hlns hθ ((isADEqm_iff_isWalrasEqm E x y p).mp h)

/-- **p. 692** (Proposition 16.D.1 applied). With convex production sets and rational, convex,
locally nonsatiated preferences, every Pareto optimal allocation is supported by contingent prices
`p ≠ 0` as a price quasiequilibrium with transfers (wealth levels `p·x*ᵢ`). -/
theorem paretoOptimal_supported [Nonempty ι] {E : CEconomy ι κ S L}
    (hY : ∀ j, Convex ℝ (E.toPriv.Y j)) (hrat : ∀ i, RationalOn (E.toPriv.X i) (E.toPriv.pref i))
    (hc : ∀ i, PrefConvex (E.toPriv.X i) (E.toPriv.pref i))
    (hlns : ∀ i, LocallyNonsatiated (E.toPriv.X i) (E.toPriv.pref i))
    {x : ι → CVec S L} {y : κ → CVec S L} (hpo : E.IsParetoOptimal x y) :
    ∃ p : CVec S L, p ≠ 0 ∧ E.toPriv.toEconomy.IsPriceQuasiEqmWithTransfers (flatAlloc x y)
      (flat p) (fun i => cval p (x i)) := by
  obtain ⟨v, hv, hq⟩ := proposition_16_D_1 (E := E.toPriv.toEconomy) hY hrat hc hlns hpo
  refine ⟨unflat v, fun h0 => hv ?_, ?_⟩
  · rw [← flat_unflat v, h0]; rfl
  · simp only [flat_unflat]
    convert hq using 2
    rename_i i
    rw [← flat_dotProduct, flat_unflat]; rfl

/-! ## Exchange economies with utility functions -/

/-- **Definition 19.C.1** for an exchange economy (no firms) with consumption sets `ℝ^{LS}_+` and
utility functions `Uᵢ`: `x*ᵢ` maximizes `Uᵢ` on `{xᵢ ≥ 0 : p·xᵢ ≤ p·ωᵢ}` and `∑ᵢ x*ᵢ = ∑ᵢ ωᵢ`. -/
def IsADEqmU (U : ι → CVec S L → ℝ) (ω : ι → CVec S L) (x : ι → CVec S L) (p : CVec S L) :
    Prop :=
  (∀ i, (NonnegC (x i) ∧ cval p (x i) ≤ cval p (ω i)) ∧
    ∀ x', NonnegC x' → cval p x' ≤ cval p (ω i) → U i x' ≤ U i (x i)) ∧
    ∑ i, x i = ∑ i, ω i

/-- The exchange economy `({ℝ^{LS}_+, Uᵢ, ωᵢ})` with no firms. -/
def exchangeCE (U : ι → CVec S L → ℝ) (ω : ι → CVec S L) : CEconomy ι (Fin 0) S L where
  X := fun _ => {x | NonnegC x}
  pref := fun i a b => U i b ≤ U i a
  ω := ω
  Y := fun _ => ∅
  θ := fun _ _ => 0

/-- `IsADEqmU` is Definition 19.C.1 for the exchange economy with no firms. -/
theorem isADEqmU_iff (U : ι → CVec S L → ℝ) (ω : ι → CVec S L) (x : ι → CVec S L)
    (p : CVec S L) : IsADEqmU U ω x p ↔ (exchangeCE U ω).IsADEqm x Fin.elim0 p := by
  simp [IsADEqmU, CEconomy.IsADEqm, exchangeCE, CEconomy.wealth]

/-! ## Convexity and Exercise 19.C.1 -/

/-- **Exercise 19.C.1** (MWG, p. 725). If every Bernoulli utility `u_s` is concave on `ℝ^L_+`
(and `π ≥ 0`), the expected utility `∑_s π_s u_s(x_s)` is concave on `ℝ^{LS}_+`. -/
theorem exercise_19_C_1 {π : Fin S → ℝ} (hπ : ∀ s, 0 ≤ π s) {u : Fin S → (Fin L → ℝ) → ℝ}
    (hu : ∀ s, ConcaveOn ℝ {a : Fin L → ℝ | ∀ l, 0 ≤ a l} (u s)) :
    ConcaveOn ℝ {x : CVec S L | NonnegC x} (expUtil π u) := by
  refine ⟨?_, ?_⟩
  · intro x hx y hy a b ha hb _ s l
    have := hx s l; have := hy s l
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; positivity
  · intro x hx y hy a b ha hb hab
    simp only [expUtil, smul_eq_mul, Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun s _ => ?_
    have h := (hu s).2 (hx s) (hy s) ha hb hab
    simp only [smul_eq_mul, Pi.add_apply, Pi.smul_apply] at h ⊢
    have h' : a * u s (x s) + b * u s (y s) ≤ u s (a • x s + b • y s) := h
    calc a * (π s * u s (x s)) + b * (π s * u s (y s))
        = π s * (a * u s (x s) + b * u s (y s)) := by ring
      _ ≤ π s * u s (a • x s + b • y s) := mul_le_mul_of_nonneg_left h' (hπ s)
      _ = π s * u s ((a • x + b • y) s) := rfl

/-- **p. 692** (Sections 6.C and 6.E recalled). With concave Bernoulli utilities the
expected-utility preference of Example 19.B.1 is convex: its upper contour sets in `ℝ^{LS}_+` are
convex. -/
theorem euPref_convex {π : Fin S → ℝ} (hπ : ∀ s, 0 ≤ π s) {u : Fin S → (Fin L → ℝ) → ℝ}
    (hu : ∀ s, ConcaveOn ℝ {a : Fin L → ℝ | ∀ l, 0 ≤ a l} (u s)) (x : CVec S L) :
    Convex ℝ {x' : CVec S L | NonnegC x' ∧ euPref π u x' x} :=
  (exercise_19_C_1 hπ hu).convex_ge (expUtil π u x)

/-- The convexity of `euPref_convex` in Chapter 3's sense on `ℝ^{LS}` (`PrefConvex`). -/
theorem euPref_prefConvex {π : Fin S → ℝ} (hπ : ∀ s, 0 ≤ π s) {u : Fin S → (Fin L → ℝ) → ℝ}
    (hu : ∀ s, ConcaveOn ℝ {a : Fin L → ℝ | ∀ l, 0 ≤ a l} (u s)) :
    PrefConvex (unflat ⁻¹' {x : CVec S L | NonnegC x})
      (fun a b => euPref π u (unflat a) (unflat b)) := by
  intro v _ a ha b hb α β hα hβ hαβ
  have h := euPref_convex hπ hu (unflat v) ⟨ha.1, ha.2⟩ ⟨hb.1, hb.2⟩ hα hβ hαβ
  exact ⟨h.1, h.2⟩

/-! ## The expected-utility instance of the welfare theorem -/

/-- With `S, L ≥ 1`, strictly positive probabilities and strongly monotone Bernoulli utilities,
the expected-utility preference on `ℝ^{LS}_+` is rational and locally nonsatiated. -/
theorem euPref_rational_lns [NeZero S] [NeZero L] {π : Fin S → ℝ} (hπ : ∀ s, 0 < π s)
    {u : Fin S → (Fin L → ℝ) → ℝ} (hu : ∀ s, StronglyMonotoneL (u s)) :
    RationalOn (unflat ⁻¹' {x : CVec S L | NonnegC x})
        (fun a b => euPref π u (unflat a) (unflat b)) ∧
      LocallyNonsatiated (unflat ⁻¹' {x : CVec S L | NonnegC x})
        (fun a b => euPref π u (unflat a) (unflat b)) := by
  refine ⟨⟨fun a _ b _ => le_total _ _, fun _ _ _ _ _ _ h1 h2 => le_trans h2 h1⟩, ?_⟩
  intro v hv ε hε
  have hn : (0 : ℝ) < (S * L : ℕ) := by
    have := NeZero.pos S; have := NeZero.pos L; positivity
  set δ := ε / Real.sqrt (S * L : ℕ) with hδ
  have hδ0 : 0 < δ := div_pos hε (Real.sqrt_pos.mpr hn)
  refine ⟨v + fun _ => δ, ?_, ?_, ?_⟩
  · intro s l
    have := hv s l
    simp only [unflat, Pi.add_apply] at this ⊢
    linarith
  · unfold euclidDist
    simp only [Pi.add_apply, add_sub_cancel_left, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hδ0.le, hδ,
      mul_div_cancel₀ _ (Real.sqrt_pos.mpr hn).ne']
  · have hlt : expUtil π u (unflat v) < expUtil π u (unflat (v + fun _ => δ)) := by
      apply expUtil_stronglyMonotone hπ hu
      · exact hv
      · intro s l; simp only [unflat, Pi.add_apply]; linarith
      · intro h
        have := congrFun (congrFun h ⟨0, NeZero.pos S⟩) ⟨0, NeZero.pos L⟩
        simp only [unflat, Pi.add_apply] at this
        linarith
    exact ⟨hlt.le, not_le.mpr hlt⟩

/-- **p. 692**, instance of `adEqm_paretoOptimal`: in an economy whose consumers have consumption
sets `ℝ^{LS}_+` and expected-utility preferences with strictly positive probabilities and
strongly monotone Bernoulli utilities, every Arrow-Debreu equilibrium allocation is Pareto
optimal. -/
theorem adEqm_paretoOptimal_eu [NeZero S] [NeZero L] {E : CEconomy ι κ S L}
    {π : ι → Fin S → ℝ} (hπ : ∀ i s, 0 < π i s) {u : ι → Fin S → (Fin L → ℝ) → ℝ}
    (hu : ∀ i s, StronglyMonotoneL (u i s)) (hX : ∀ i, E.X i = {x | NonnegC x})
    (hpref : ∀ i, E.pref i = euPref (π i) (u i)) (hθ : ∀ j, ∑ i, E.θ j i = 1)
    {x : ι → CVec S L} {y : κ → CVec S L} {p : CVec S L} (h : E.IsADEqm x y p) :
    E.IsParetoOptimal x y := by
  have hX' : ∀ i, E.toPriv.X i = unflat ⁻¹' {x : CVec S L | NonnegC x} := fun i => by
    simp [CEconomy.toPriv, hX i]
  have hp' : ∀ i, E.toPriv.pref i = fun a b => euPref (π i) (u i) (unflat a) (unflat b) :=
    fun i => by simp [CEconomy.toPriv, hpref i]
  refine adEqm_paretoOptimal (fun i => ?_) (fun i => ?_) hθ h
  · rw [hX' i, hp' i]; exact (euPref_rational_lns (hπ i) (hu i)).1
  · rw [hX' i, hp' i]; exact (euPref_rational_lns (hπ i) (hu i)).2

end MWG.EquilibriumUncertainty
