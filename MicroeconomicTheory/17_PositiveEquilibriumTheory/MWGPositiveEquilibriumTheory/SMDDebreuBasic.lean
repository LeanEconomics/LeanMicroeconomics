/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPositiveEquilibriumTheory.SMDTwoGoods

/-!
# Debreu's construction: revealed preference for excess demand (MWG pp. 604-606)

The small-type "Proof of Proposition 17.E.3 continued" (Debreu, 1974).

* Prices are normalized to `‖p‖² = p·p = 1` (`unitPEps`: the normalized prices of `P_ε`).
* **(17.E.4)** `p` is directly revealed preferred to `p'` for the excess demand `z` if
  `z(p) ≠ z(p')` and `p·z(p') ≤ 0` (`RevPrefDirect`); indirectly if there is a finite chain
  (`Relation.TransGen`); the strong axiom (`StrongAxiomED`) says no `p` indirectly revealed
  preferred to `p'` has `p'` directly revealed preferred to `p`.
* Proportionally one-to-one excess demand (`PropOneToOne`); for such `z`, (17.E.4) is
  equivalent to **(17.E.4')** `p ≠ p'` and `p·z(p') ≤ 0` (`revPrefDirect_iff`). The book's basic
  observation: multiplying by a positive function `α(·)` preserves all of this
  (`propOneToOne_smul`, `revPrefDirect_smul_iff`, `strongAxiomED_smul`).
* Debreu's functions `zⁱ(p) = eⁱ - pᵢ p` (`debreuZ`): the projection of `eⁱ` on
  `T_p = {z : p·z = 0}`, i.e. the maximizer of `-‖z - eⁱ‖` on `T_p` (`debreuZ_dist`);
  proportionally one-to-one (**Exercise 17.E.6**, `exercise_17_E_6`) and satisfying the strong
  axiom (**Exercise 17.E.7**, `exercise_17_E_7`): the direct revealed preference
  `p·zⁱ(p') ≤ 0`, `p ≠ p'` forces `pᵢ < p'ᵢ` (`debreuZ_revPref_lt`).
* The decomposition `∑ᵢ (zᵢ(p) + r pᵢ)(eⁱ - pᵢ p) = z(p)` for `‖p‖ = 1`, `p·z(p) = 0`
  (`debreu_decomposition`, p. 606).
-/

namespace MWG.PositiveEquilibriumTheory

open MWG.ConsumerChoice Filter Topology

variable {L : ℕ}

/-- The normalized prices of `P_ε`: `p ≥ 0`, `p·p = 1`, `ε pₗ' ≤ pₗ` for all `ℓ, ℓ'`. -/
def unitPEps (L : ℕ) (ε : ℝ) : Set (Fin L → ℝ) :=
  {p | (∀ l, 0 ≤ p l) ∧ p ⬝ᵥ p = 1 ∧ ∀ l l', ε * p l' ≤ p l}

/-- **(17.E.4)** (MWG, p. 605). `p` is directly revealed preferred to `p'`. -/
def RevPrefDirect (z : (Fin L → ℝ) → Fin L → ℝ) (p p' : Fin L → ℝ) : Prop :=
  z p ≠ z p' ∧ p ⬝ᵥ z p' ≤ 0

/-- **(17.E.4')** (MWG, p. 605). The restatement for proportionally one-to-one `z`. -/
def RevPrefDirect' (z : (Fin L → ℝ) → Fin L → ℝ) (p p' : Fin L → ℝ) : Prop :=
  p ≠ p' ∧ p ⬝ᵥ z p' ≤ 0

/-- **Section 17.E** (MWG, p. 605). `z` is proportionally one-to-one on `S`: `p ≠ p'` implies
that `z(p)` is not a positive multiple of `z(p')`. -/
def PropOneToOne (S : Set (Fin L → ℝ)) (z : (Fin L → ℝ) → Fin L → ℝ) : Prop :=
  ∀ p ∈ S, ∀ p' ∈ S, p ≠ p' → ¬ ∃ α : ℝ, 0 < α ∧ z p = α • z p'

/-- **Section 17.E** (MWG, p. 605). The strong axiom of revealed preference for an excess demand
function on the normalized prices `S`: if `p` is (directly or indirectly) revealed preferred to
`p'`, then `p'` is not directly revealed preferred to `p`. -/
def StrongAxiomED (S : Set (Fin L → ℝ)) (z : (Fin L → ℝ) → Fin L → ℝ) : Prop :=
  ∀ p ∈ S, ∀ p' ∈ S, Relation.TransGen (fun a b => a ∈ S ∧ b ∈ S ∧ RevPrefDirect z a b) p p' →
    ¬ RevPrefDirect z p' p

/-- For proportionally one-to-one `z`, (17.E.4) and (17.E.4') agree (MWG, p. 605). -/
theorem revPrefDirect_iff {S : Set (Fin L → ℝ)} {z : (Fin L → ℝ) → Fin L → ℝ}
    (hz : PropOneToOne S z) {p p' : Fin L → ℝ} (hp : p ∈ S) (hp' : p' ∈ S) :
    RevPrefDirect z p p' ↔ RevPrefDirect' z p p' := by
  constructor
  · rintro ⟨hne, h⟩
    exact ⟨fun he => hne (by rw [he]), h⟩
  · rintro ⟨hne, h⟩
    exact ⟨fun he => hz p hp p' hp' hne ⟨1, one_pos, by rw [he, one_smul]⟩, h⟩

/-- **Section 17.E** (MWG, p. 605), the basic observation: `α(·) z(·)` with `α > 0` is
proportionally one-to-one when `z` is. -/
theorem propOneToOne_smul {S : Set (Fin L → ℝ)} {z : (Fin L → ℝ) → Fin L → ℝ}
    (hz : PropOneToOne S z) {α : (Fin L → ℝ) → ℝ} (hα : ∀ p ∈ S, 0 < α p) :
    PropOneToOne S (fun p => α p • z p) := by
  rintro p hp p' hp' hne ⟨β, hβ, he⟩
  refine hz p hp p' hp' hne ⟨β * α p' / α p, by have := hα p hp; have := hα p' hp'; positivity,
    ?_⟩
  have hαp := (hα p hp).ne'
  have := congrArg (fun v => (α p)⁻¹ • v) he
  simp only [smul_smul, inv_mul_cancel₀ hαp, one_smul] at this
  rw [this]
  congr 1
  field_simp

/-- **Section 17.E** (MWG, p. 605), the basic observation: the revealed preference inequalities
(17.E.4') hold for `α(·) z(·)` iff they hold for `z`. -/
theorem revPrefDirect_smul_iff {z : (Fin L → ℝ) → Fin L → ℝ} {α : (Fin L → ℝ) → ℝ}
    {p p' : Fin L → ℝ} (hα : 0 < α p') :
    RevPrefDirect' (fun p => α p • z p) p p' ↔ RevPrefDirect' z p p' := by
  simp only [RevPrefDirect', dotProduct_smul, smul_eq_mul]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    by_contra hc
    push Not at hc
    have := mul_pos hα hc
    linarith
  · rintro ⟨h1, h2⟩
    exact ⟨h1, mul_nonpos_of_nonneg_of_nonpos hα.le h2⟩

/-- **Section 17.E** (MWG, p. 605), the basic observation: if `z` is proportionally one-to-one and
satisfies the strong axiom, so does `α(·) z(·)` for any `α > 0`. -/
theorem strongAxiomED_smul {S : Set (Fin L → ℝ)} {z : (Fin L → ℝ) → Fin L → ℝ}
    (hz : PropOneToOne S z) (hSA : StrongAxiomED S z) {α : (Fin L → ℝ) → ℝ}
    (hα : ∀ p ∈ S, 0 < α p) : StrongAxiomED S (fun p => α p • z p) := by
  have hz' := propOneToOne_smul hz hα
  have hrel : ∀ a b, a ∈ S → b ∈ S →
      (RevPrefDirect (fun p => α p • z p) a b ↔ RevPrefDirect z a b) := by
    intro a b ha hb
    rw [revPrefDirect_iff hz' ha hb, revPrefDirect_iff hz ha hb, revPrefDirect_smul_iff (hα b hb)]
  intro p hp p' hp' hch hrev
  refine hSA p hp p' hp' ?_ ((hrel p' p hp' hp).1 hrev)
  exact Relation.TransGen.mono (p := fun a b => a ∈ S ∧ b ∈ S ∧ RevPrefDirect z a b)
    (fun a b (h : a ∈ S ∧ b ∈ S ∧ RevPrefDirect (fun p => α p • z p) a b) =>
      ⟨h.1, h.2.1, (hrel a b h.1 h.2.1).1 h.2.2⟩) p p' hch

/-! ### Debreu's functions `eⁱ - pᵢ p` -/

/-- **Section 17.E** (MWG, p. 605). Debreu's excess demand function `zⁱ(p) = eⁱ - pᵢ p`, for
`‖p‖ = 1`. -/
def debreuZ (i : Fin L) (p : Fin L → ℝ) : Fin L → ℝ := Pi.single i 1 - p i • p

/-- Walras' law for `zⁱ` on the unit sphere. -/
theorem debreuZ_walras (i : Fin L) {p : Fin L → ℝ} (hp : p ⬝ᵥ p = 1) :
    p ⬝ᵥ debreuZ i p = 0 := by
  simp [debreuZ, dotProduct_sub, dotProduct_smul, hp]

/-- **Section 17.E** (MWG, p. 605). `zⁱ(p)` is the point of `T_p = {z : p·z = 0}` closest to
`eⁱ`: for `z ∈ T_p`, `‖z - eⁱ‖² = ‖z - zⁱ(p)‖² + pᵢ²`, so `zⁱ(p)` uniquely maximizes the
concave "utility function" `-‖z - eⁱ‖` on `T_p`. -/
theorem debreuZ_dist (i : Fin L) {p z : Fin L → ℝ} (hp : p ⬝ᵥ p = 1) (hz : p ⬝ᵥ z = 0) :
    (z - Pi.single i 1) ⬝ᵥ (z - Pi.single i 1) =
      (z - debreuZ i p) ⬝ᵥ (z - debreuZ i p) + p i ^ 2 := by
  have e : z - Pi.single i 1 = (z - debreuZ i p) - p i • p := by
    simp only [debreuZ]; abel
  have hpw : p ⬝ᵥ (z - debreuZ i p) = 0 := by
    rw [dotProduct_sub, hz, debreuZ_walras i hp, sub_zero]
  have key : ∀ w : Fin L → ℝ, p ⬝ᵥ w = 0 →
      (w - p i • p) ⬝ᵥ (w - p i • p) = w ⬝ᵥ w + p i ^ 2 := by
    intro w hw
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul, hp,
      hw, dotProduct_comm w p]
    ring
  rw [e, key _ hpw]

/-- Unit vectors: `p·p' ≤ 1`, with equality only if `p = p'`. -/
theorem unit_dot_le {p p' : Fin L → ℝ} (hp : p ⬝ᵥ p = 1) (hp' : p' ⬝ᵥ p' = 1) :
    p ⬝ᵥ p' ≤ 1 ∧ (p ⬝ᵥ p' = 1 → p = p') := by
  have h : (p - p') ⬝ᵥ (p - p') = 2 - 2 * (p ⬝ᵥ p') := by
    simp only [sub_dotProduct, dotProduct_sub, hp, hp', dotProduct_comm p' p]; ring
  have hnn : 0 ≤ (p - p') ⬝ᵥ (p - p') := Finset.sum_nonneg fun l _ => mul_self_nonneg _
  refine ⟨by linarith, fun h1 => ?_⟩
  rw [h1] at h
  have := dotProduct_self_eq_zero.1 (by linarith : (p - p') ⬝ᵥ (p - p') = 0)
  exact sub_eq_zero.1 this

/-- **Exercise 17.E.7** (MWG, p. 645), the key step: for unit price vectors with `pᵢ > 0` and
`p'ᵢ ≥ 0`, if `p ≠ p'` and `p·zⁱ(p') ≤ 0` then `pᵢ < p'ᵢ`. -/
theorem debreuZ_revPref_lt (i : Fin L) {p p' : Fin L → ℝ} (hp : p ⬝ᵥ p = 1)
    (hp' : p' ⬝ᵥ p' = 1) (hpi : 0 < p i) (hpi' : 0 ≤ p' i) (hne : p ≠ p')
    (h : p ⬝ᵥ debreuZ i p' ≤ 0) : p i < p' i := by
  obtain ⟨hle, heq⟩ := unit_dot_le hp hp'
  have hlt : p ⬝ᵥ p' < 1 := lt_of_le_of_ne hle fun h1 => hne (heq h1)
  simp only [debreuZ, dotProduct_sub, dotProduct_single, mul_one, dotProduct_smul,
    smul_eq_mul] at h
  rcases hpi'.lt_or_eq with h' | h'
  · nlinarith
  · rw [← h'] at h; linarith

/-- **Exercise 17.E.6** (MWG, p. 645). On normalized prices with `pᵢ > 0`, `zⁱ(p) = eⁱ - pᵢ p` is
proportionally one-to-one. -/
theorem exercise_17_E_6 (i : Fin L) :
    PropOneToOne {p | p ⬝ᵥ p = 1 ∧ 0 < p i} (debreuZ i) := by
  rintro p ⟨hp, hpi⟩ p' ⟨hp', hpi'⟩ hne ⟨α, hα, he⟩
  -- dot the identity `eⁱ - pᵢ p = α (eⁱ - p'ᵢ p')` with `p` and with `p'`
  have h1 := congrArg (fun v => p ⬝ᵥ v) he
  have h2 := congrArg (fun v => p' ⬝ᵥ v) he
  simp only [debreuZ, dotProduct_sub, dotProduct_single, mul_one, dotProduct_smul,
    smul_eq_mul, hp, hp', dotProduct_comm p' p] at h1 h2
  obtain ⟨hle, heq⟩ := unit_dot_le hp hp'
  -- `h1 : 0 = α (pᵢ - p'ᵢ c)`, `h2 : p'ᵢ - pᵢ c = 0` with `c = p·p'`
  set c := p ⬝ᵥ p'
  have hA : p i = p' i * c := by
    have : α * (p i - p' i * c) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hα.ne'
    · linarith
  have hB : p' i = p i * c := by linarith
  have hc : c = 1 := by
    have : p i * (1 - c * c) = 0 := by rw [hA] at hB ⊢; nlinarith
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hpi.ne'
    · have hcc : (c - 1) * (c + 1) = 0 := by nlinarith
      rcases mul_eq_zero.1 hcc with h | h
      · linarith
      · exfalso
        have : c = -1 := by linarith
        rw [this] at hB
        linarith
  exact hne (heq hc)

/-- **Exercise 17.E.7** (MWG, p. 645). On the normalized prices of `P_ε` (`ε > 0`), Debreu's
function `zⁱ(p) = eⁱ - pᵢ p` satisfies the strong axiom of revealed preference. -/
theorem exercise_17_E_7 (i : Fin L) {ε : ℝ} (hε : 0 < ε) :
    StrongAxiomED (unitPEps L ε) (debreuZ i) := by
  have hpos : ∀ p ∈ unitPEps L ε, 0 < p i := by
    intro p hp
    by_contra h
    push Not at h
    have hpi : p i = 0 := le_antisymm h (hp.1 i)
    have hall : ∀ l, p l = 0 := by
      intro l
      have := hp.2.2 i l
      rw [hpi] at this
      exact le_antisymm (by nlinarith [hp.1 l]) (hp.1 l)
    have : p ⬝ᵥ p = 0 := by simp [dotProduct, hall]
    rw [hp.2.1] at this
    exact one_ne_zero this
  have key : ∀ a b, a ∈ unitPEps L ε → b ∈ unitPEps L ε → RevPrefDirect (debreuZ i) a b →
      a i < b i := by
    intro a b ha hb hab
    refine debreuZ_revPref_lt i ha.2.1 hb.2.1 (hpos a ha) (hb.1 i) ?_ hab.2
    rintro rfl
    exact hab.1 rfl
  intro p hp p' hp' hch hrev
  have hlt : p i < p' i := by
    clear hrev hp'
    induction hch with
    | single h => exact key _ _ h.1 h.2.1 h.2.2
    | tail _ h ih => exact ih.trans (key _ _ h.1 h.2.1 h.2.2)
  have := key p' p hp' hp hrev
  linarith

/-- **Section 17.E** (MWG, p. 606), Debreu's decomposition: for `‖p‖ = 1` and `p·w = 0`,
`∑ᵢ (wᵢ + r pᵢ)(eⁱ - pᵢ p) = w`. -/
theorem debreu_decomposition {p w : Fin L → ℝ} (hp : p ⬝ᵥ p = 1) (hw : p ⬝ᵥ w = 0) (r : ℝ) :
    ∑ i, (w i + r * p i) • debreuZ i p = w := by
  funext l
  simp only [debreuZ, Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
    Pi.single_apply, mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib,
    Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  have h1 : ∑ i, (w i + r * p i) * (p i * p l) = p l * (p ⬝ᵥ w) + r * p l * (p ⬝ᵥ p) := by
    simp only [dotProduct, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [h1, hw, hp]
  ring

end MWG.PositiveEquilibriumTheory
