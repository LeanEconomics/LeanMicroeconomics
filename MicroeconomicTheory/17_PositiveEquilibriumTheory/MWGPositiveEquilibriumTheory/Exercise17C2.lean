/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPositiveEquilibriumTheory.Existence
import MWGClassicalDemand.AppendixMH

/-!
# Exercise 17.C.2: existence for excess demand correspondences (MWG p. 642)

A convex-valued, upper hemicontinuous (Definition M.H.3) correspondence `z(·)` on `ℝ^L_{++}`
satisfying the correspondence versions (i)-(v) of the conditions of Proposition 17.C.1 has a
`p ≫ 0` with `0 ∈ z(p)` (`exercise_17_C_2`). The proof follows the book's hint:

1. (`ex17C2_uniform`) for `ε > 0` small, at every `p ∈ Δ` with some `p_ℓ < ε`, every
   `z ∈ z(p)` has a component above `1` (by (v), compactness of `Δ` and a pigeonhole choice of
   the vanishing coordinate);
2. on `Δ_δ = {p ∈ Δ : p_ℓ ≥ δ}` the values lie in `[-r, r]^L` (by (iii)-(iv));
3. Kakutani's theorem on `Δ_δ × [-r, r]^L` for `(p, z) ↦ argmax_{q ∈ Δ_δ} q·z × z(p)` gives
   `(p, z)` with `z ∈ z(p)` and `q·z ≤ p·z = 0` on `Δ_δ`; by step 1 and the choice of `δ`,
   `p_ℓ ≥ ε > δ` for all `ℓ`, and then all `z_ℓ` are equal, hence `0`.

Correction: the correspondence must be nonempty valued (otherwise `z(p) = ∅` satisfies (i)-(v)
and has no solution, `exercise_17_C_2_needs_nonempty`).
-/

namespace MWG.PositiveEquilibriumTheory

open MWG.ConsumerChoice MWG.ClassicalDemand
open Filter Topology

variable {L : ℕ}

/-- **Exercise 17.C.2**, condition (v) for a correspondence: if `pⁿ → p ≠ 0` (`pⁿ ≫ 0`),
`zⁿ ∈ z(pⁿ)` and `p_ℓ = 0` for some `ℓ`, then `Max {zⁿ₁, ..., zⁿ_L} → ∞`. -/
def CorrBoundary (Z : (Fin L → ℝ) → Set (Fin L → ℝ)) : Prop :=
  ∀ (ps : ℕ → Fin L → ℝ) (p : Fin L → ℝ) (zs : ℕ → Fin L → ℝ), (∀ n, ps n ∈ posOrthant L) →
    Tendsto ps atTop (𝓝 p) → p ≠ 0 → (∃ l, p l = 0) → (∀ n, zs n ∈ Z (ps n)) →
    ∀ M : ℝ, ∀ᶠ n in atTop, ∃ l, M < zs n l

/-- Walras' law and a lower bound `z_k > -s` bound expenditure: `p_ℓ z_ℓ ≤ s ∑ₖ pₖ`. -/
theorem coord_bound_of_walras {p z : Fin L → ℝ} (hp : ∀ l, 0 ≤ p l) (hw : p ⬝ᵥ z = 0)
    {s : ℝ} (hs0 : 0 < s) (hs : ∀ k, -s < z k) (l : Fin L) : p l * z l ≤ s * ∑ k, p k := by
  have hterm : ∀ k ∈ Finset.univ, 0 ≤ p k * z k + s * p k := fun k _ => by
    nlinarith [hs k, hp k]
  have hsum : ∑ k, (p k * z k + s * p k) = s * ∑ k, p k := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    simp only [dotProduct] at hw
    rw [hw, zero_add]
  have h := Finset.single_le_sum hterm (Finset.mem_univ l)
  rw [hsum] at h
  nlinarith [hp l]

/-- **Exercise 17.C.2, step 1** (MWG, p. 642). Under (i) and (v), for some `ε > 0`, at every
`p ∈ Δ ∩ ℝ^L_{++}` with a coordinate below `ε`, every `z ∈ z(p)` has a component above `M`. -/
theorem ex17C2_uniform {Z : (Fin L → ℝ) → Set (Fin L → ℝ)} (hbd : CorrBoundary Z) (M : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ p ∈ priceSimplex L, p ∈ posOrthant L → (∃ l, p l < ε) →
      ∀ z ∈ Z p, ∃ k, M < z k := by
  by_contra hcon
  have hex : ∀ n : ℕ, ∃ p : Fin L → ℝ, ∃ l : Fin L, ∃ z : Fin L → ℝ, p ∈ priceSimplex L ∧
      p ∈ posOrthant L ∧ p l < 1 / ((n : ℝ) + 1) ∧ z ∈ Z p ∧ ∀ k, z k ≤ M := by
    intro n
    by_contra h'
    refine hcon ⟨1 / ((n : ℝ) + 1), by positivity, fun p hp hpos ⟨l, hl⟩ z hz => ?_⟩
    by_contra hk
    push Not at hk
    exact h' ⟨p, l, z, hp, hpos, hl, hz, hk⟩
  choose ps idx zs hΔ hpos hsmall hz hM using hex
  obtain ⟨l, hl⟩ : ∃ l, ∃ᶠ n in atTop, idx n = l := by
    by_contra hc
    simp only [not_exists, Filter.not_frequently] at hc
    obtain ⟨n, hn⟩ := (eventually_all.2 hc).exists
    exact hn (idx n) rfl
  obtain ⟨φ, hφ, hφl⟩ := Filter.extraction_of_frequently_atTop hl
  obtain ⟨p, hpΔ, ψ, hψ, hlim⟩ :=
    (isCompact_priceSimplex L).tendsto_subseq (fun n => hΔ (φ n))
  have hlim' : Tendsto (fun n => ps (φ (ψ n))) atTop (𝓝 p) := hlim
  have hpl : p l = 0 := by
    refine le_antisymm ?_ (hpΔ.1 l)
    have hb : ∀ n, ps (φ (ψ n)) l ≤ 1 / ((n : ℝ) + 1) := fun n => by
      have h1 := hsmall (φ (ψ n))
      rw [hφl (ψ n)] at h1
      have h2 : (n : ℝ) ≤ φ (ψ n) := by exact_mod_cast (hφ.comp hψ).le_apply
      have h3 : 1 / ((φ (ψ n) : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      linarith
    exact le_of_tendsto_of_tendsto' (((continuous_apply l).tendsto p).comp hlim')
      tendsto_one_div_add_atTop_nhds_zero_nat hb
  have hp0 : p ≠ 0 := fun h => (dotProduct_self_pos_of_mem_priceSimplex hpΔ).ne' (by rw [h]; simp)
  obtain ⟨n, k, hk⟩ := (hbd _ p _ (fun n => hpos (φ (ψ n))) hlim' hp0 ⟨l, hpl⟩
    (fun n => hz (φ (ψ n))) M).exists
  linarith [hM (φ (ψ n)) k]

/-- The truncated simplex `Δ_δ = {p ∈ Δ : p_ℓ ≥ δ for all ℓ}`. -/
def deltaSimplex (L : ℕ) (δ : ℝ) : Set (Fin L → ℝ) := {p | p ∈ priceSimplex L ∧ ∀ l, δ ≤ p l}

/-- `Δ_δ` is compact. -/
theorem isCompact_deltaSimplex (L : ℕ) (δ : ℝ) : IsCompact (deltaSimplex L δ) := by
  have hc : IsClosed (deltaSimplex L δ) := by
    have h : deltaSimplex L δ = priceSimplex L ∩ ⋂ l, {p : Fin L → ℝ | δ ≤ p l} := by
      ext p
      simp [deltaSimplex]
    rw [h]
    exact (isClosed_priceSimplex L).inter
      (isClosed_iInter fun l => isClosed_le continuous_const (continuous_apply l))
  exact (isCompact_priceSimplex L).of_isClosed_subset hc fun p hp => hp.1

/-- `Δ_δ` is convex. -/
theorem convex_deltaSimplex (L : ℕ) (δ : ℝ) : Convex ℝ (deltaSimplex L δ) := by
  intro p hp q hq a b ha hb hab
  refine ⟨convex_priceSimplex L hp.1 hq.1 ha hb hab, fun l => ?_⟩
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have h1 := mul_le_mul_of_nonneg_left (hp.2 l) ha
  have h2 := mul_le_mul_of_nonneg_left (hq.2 l) hb
  have h3 : a * δ + b * δ = δ := by rw [← add_mul, hab, one_mul]
  linarith

/-- The maximizers of `q·z` over `Δ_δ`. -/
def deltaArgmax (L : ℕ) (δ : ℝ) (z : Fin L → ℝ) : Set (Fin L → ℝ) :=
  {q | q ∈ deltaSimplex L δ ∧ ∀ q' ∈ deltaSimplex L δ, q' ⬝ᵥ z ≤ q ⬝ᵥ z}

/-- **Exercise 17.C.2** (MWG, p. 642). Let `z(·)` be a correspondence on `ℝ^L_{++}`, nonempty and
convex valued, with (i) upper hemicontinuity, (ii) homogeneity of degree zero, (iii) Walras'
law `p·z = 0` for `z ∈ z(p)`, (iv) a bound `z_ℓ > -s`, and (v) the boundary condition. Then
`0 ∈ z(p)` for some `p ≫ 0`. -/
theorem exercise_17_C_2 {Z : (Fin L → ℝ) → Set (Fin L → ℝ)}
    (hU : UpperHemicontinuousMWG (posOrthant L) Z) (hne : ∀ p ∈ posOrthant L, (Z p).Nonempty)
    (hconv : ∀ p ∈ posOrthant L, Convex ℝ (Z p))
    (_hH : ∀ p ∈ posOrthant L, ∀ α : ℝ, 0 < α → Z (α • p) = Z p)
    (hW : ∀ p ∈ posOrthant L, ∀ z ∈ Z p, p ⬝ᵥ z = 0)
    (hs : ∃ s : ℝ, ∀ p ∈ posOrthant L, ∀ z ∈ Z p, ∀ l, -s < z l) (hbd : CorrBoundary Z) :
    ∃ p ∈ posOrthant L, (0 : Fin L → ℝ) ∈ Z p := by
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · have hp : (0 : Fin 0 → ℝ) ∈ posOrthant 0 := fun l => l.elim0
    obtain ⟨z, hz⟩ := hne 0 hp
    refine ⟨0, hp, ?_⟩
    have : z = 0 := funext fun l => l.elim0
    rwa [this] at hz
  obtain ⟨s0, hs0⟩ := hs
  set s : ℝ := |s0| + 1 with hsdef
  have hspos : 0 < s := by positivity
  have hsb : ∀ p ∈ posOrthant L, ∀ z ∈ Z p, ∀ l, -s < z l := fun p hp z hz l => by
    have := hs0 p hp z hz l
    have : -s ≤ -s0 := by rw [hsdef]; linarith [le_abs_self s0]
    linarith
  obtain ⟨ε, hε, hεA⟩ := ex17C2_uniform hbd 1
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  set δ : ℝ := min (ε / 2) (1 / (L * (1 + s))) with hδdef
  have hδ0 : 0 < δ := lt_min (by linarith) (by positivity)
  have hδε : δ ≤ ε / 2 := min_le_left _ _
  have hδs : L * δ * (1 + s) ≤ 1 := by
    have h := min_le_right (ε / 2) (1 / (L * (1 + s)))
    rw [← hδdef] at h
    calc L * δ * (1 + s) = δ * (L * (1 + s)) := by ring
      _ ≤ 1 / (L * (1 + s)) * (L * (1 + s)) := mul_le_mul_of_nonneg_right h (by positivity)
      _ = 1 := by field_simp
  have hLδ : L * δ < 1 := by nlinarith
  -- the uniform vector lies in Δ_δ
  have huni : (fun _ : Fin L => (L : ℝ)⁻¹) ∈ deltaSimplex L δ := by
    refine ⟨⟨fun _ => by positivity, by simp [hLr.ne']⟩, fun _ => ?_⟩
    rw [← one_div, le_div_iff₀ hLr]
    linarith
  have hΔpos : ∀ p ∈ deltaSimplex L δ, p ∈ posOrthant L := fun p hp l =>
    lt_of_lt_of_le hδ0 (hp.2 l)
  set r : ℝ := s / δ + s
  have hbox : ∀ p ∈ deltaSimplex L δ, Z p ⊆ Set.Icc (fun _ => -r) (fun _ => r) := by
    intro p hp z hz
    have hpos := hΔpos p hp
    refine ⟨fun l => ?_, fun l => ?_⟩
    · have := hsb p hpos z hz l
      have : 0 ≤ s / δ := by positivity
      change -r ≤ z l
      linarith
    · have hb := coord_bound_of_walras (fun k => (hpos k).le) (hW p hpos z hz) hspos
        (hsb p hpos z hz) l
      rw [hp.1.2, mul_one] at hb
      have hpl := hp.2 l
      change z l ≤ r
      have : z l ≤ s / δ := by
        rw [le_div_iff₀ hδ0]
        rcases le_or_gt (z l) 0 with h | h
        · nlinarith
        · nlinarith
      linarith
  -- Kakutani on K = Δ_δ × [-r, r]^L
  set K : Set ((Fin L → ℝ) × (Fin L → ℝ)) :=
    deltaSimplex L δ ×ˢ Set.Icc (fun _ => -r) (fun _ => r)
  set F : (Fin L → ℝ) × (Fin L → ℝ) → Set ((Fin L → ℝ) × (Fin L → ℝ)) :=
    fun x => deltaArgmax L δ x.2 ×ˢ Z x.1
  have hKc : IsCompact K := (isCompact_deltaSimplex L δ).prod isCompact_Icc
  have hKconv : Convex ℝ K := (convex_deltaSimplex L δ).prod (convex_Icc _ _)
  have hKne : K.Nonempty := by
    obtain ⟨z, hz⟩ := hne _ (hΔpos _ huni)
    exact ⟨(_, z), huni, hbox _ huni hz⟩
  have hdotc : ∀ z : Fin L → ℝ, Continuous fun q : Fin L → ℝ => q ⬝ᵥ z := fun z => by
    simp only [dotProduct]
    fun_prop
  have hFne : ∀ x ∈ K, (F x).Nonempty := by
    intro x hx
    obtain ⟨q, hq, hmax⟩ := (isCompact_deltaSimplex L δ).exists_isMaxOn ⟨_, huni⟩
      (hdotc x.2).continuousOn
    obtain ⟨z, hz⟩ := hne _ (hΔpos _ hx.1)
    exact ⟨(q, z), ⟨hq, fun q' hq' => hmax hq'⟩, hz⟩
  have hFconv : ∀ x ∈ K, Convex ℝ (F x) := by
    intro x hx
    refine Convex.prod ?_ (hconv _ (hΔpos _ hx.1))
    intro q hq q₂ hq₂ a b ha hb hab
    refine ⟨convex_deltaSimplex L δ hq.1 hq₂.1 ha hb hab, fun q' hq' => ?_⟩
    rw [add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul]
    have h1 := mul_le_mul_of_nonneg_left (hq.2 q' hq') ha
    have h2 := mul_le_mul_of_nonneg_left (hq₂.2 q' hq') hb
    have h3 : q' ⬝ᵥ x.2 = a * q' ⬝ᵥ x.2 + b * q' ⬝ᵥ x.2 := by rw [← add_mul, hab, one_mul]
    linarith
  have hFK : ∀ x ∈ K, F x ⊆ K := fun x hx y hy => ⟨hy.1.1, hbox _ hx.1 hy.2⟩
  have hgraph : IsClosed (LeanEconomics.FixedPoint.graphOn K F) := by
    refine IsSeqClosed.isClosed fun {xs} {a} hxs hlim => ?_
    have h1 : Tendsto (fun n => (xs n).1) atTop (𝓝 a.1) := (continuous_fst.tendsto a).comp hlim
    have h2 : Tendsto (fun n => (xs n).2) atTop (𝓝 a.2) := (continuous_snd.tendsto a).comp hlim
    have hP : Tendsto (fun n => (xs n).1.1) atTop (𝓝 a.1.1) := (continuous_fst.tendsto _).comp h1
    have hZ : Tendsto (fun n => (xs n).1.2) atTop (𝓝 a.1.2) := (continuous_snd.tendsto _).comp h1
    have hQ : Tendsto (fun n => (xs n).2.1) atTop (𝓝 a.2.1) := (continuous_fst.tendsto _).comp h2
    have hWl : Tendsto (fun n => (xs n).2.2) atTop (𝓝 a.2.2) :=
      (continuous_snd.tendsto _).comp h2
    have haK : a.1 ∈ K := (hKc.isClosed).mem_of_tendsto h1 (Eventually.of_forall fun n => (hxs n).1)
    refine ⟨haK, ⟨(isCompact_deltaSimplex L δ).isClosed.mem_of_tendsto hQ
      (Eventually.of_forall fun n => (hxs n).2.1.1), fun q' hq' => ?_⟩, ?_⟩
    · exact le_of_tendsto_of_tendsto (appendixA_tendsto_dotProduct_seq tendsto_const_nhds hZ)
        (appendixA_tendsto_dotProduct_seq hQ hZ)
        (Eventually.of_forall fun n => (hxs n).2.1.2 q' hq')
    · exact hU.1 (fun n => (xs n).1.1) (fun n => (xs n).2.2) a.1.1 a.2.2
        (fun n => hΔpos _ (hxs n).1.1) (hΔpos _ haK.1) (fun n => (hxs n).2.2) hP hWl
  obtain ⟨⟨p, z⟩, ⟨hpδ, -⟩, hfix⟩ := LeanEconomics.FixedPoint.kakutani hKc hKconv hKne hFne
    hFconv hFK hgraph
  obtain ⟨⟨-, hpmax⟩, hzZ⟩ := hfix
  have hppos := hΔpos p hpδ
  have hpz : p ⬝ᵥ z = 0 := hW p hppos z hzZ
  have hqz : ∀ q ∈ deltaSimplex L δ, q ⬝ᵥ z ≤ 0 := fun q hq => hpz ▸ hpmax q hq
  -- every coordinate of p is at least ε
  have hpε : ∀ l, ε ≤ p l := by
    intro l
    by_contra hl
    push Not at hl
    obtain ⟨k, hk⟩ := hεA p hpδ.1 hppos ⟨l, hl⟩ z hzZ
    classical
    set q : Fin L → ℝ := fun j => δ + if j = k then 1 - L * δ else 0
    have hq : q ∈ deltaSimplex L δ := by
      refine ⟨⟨fun j => ?_, ?_⟩, fun j => ?_⟩
      · simp only [q]
        split_ifs <;> linarith
      · simp only [q, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
          Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
      · simp only [q]
        split_ifs <;> linarith
    have hqz' : q ⬝ᵥ z = δ * ∑ j, z j + (1 - L * δ) * z k := by
      simp only [q, dotProduct, add_mul, Finset.sum_add_distrib, ← Finset.mul_sum, ite_mul,
        zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    have hsum : -(L * s) ≤ ∑ j, z j := by
      have : ∑ _j : Fin L, -s ≤ ∑ j, z j :=
        Finset.sum_le_sum fun j _ => (hsb p hppos z hzZ j).le
      simpa [mul_comm] using this
    have := hqz q hq
    rw [hqz'] at this
    nlinarith
  -- hence all coordinates of z are equal, and Walras' law makes them zero
  have hle : ∀ k j, z k ≤ z j := by
    intro k j
    by_cases hkj : k = j
    · rw [hkj]
    classical
    set t : ℝ := ε - δ
    have ht : 0 < t := by simp only [t]; linarith
    set q : Fin L → ℝ := p + t • (Pi.single k 1 - Pi.single j 1)
    have hqk : q k = p k + t := by simp [q, hkj]
    have hqj : q j = p j - t := by simp [q, Ne.symm hkj, sub_eq_add_neg]
    have hqo : ∀ m, m ≠ k → m ≠ j → q m = p m := fun m h1 h2 => by simp [q, h1, h2]
    have hq : q ∈ deltaSimplex L δ := by
      refine ⟨⟨fun m => ?_, ?_⟩, fun m => ?_⟩
      · by_cases h1 : m = k
        · rw [h1, hqk]; linarith [hpδ.1.1 k]
        · by_cases h2 : m = j
          · rw [h2, hqj]; linarith [hpε j]
          · rw [hqo m h1 h2]; exact hpδ.1.1 m
      · simp [q, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, hpδ.1.2]
      · by_cases h1 : m = k
        · rw [h1, hqk]; linarith [hpδ.2 k]
        · by_cases h2 : m = j
          · rw [h2, hqj]; linarith [hpε j]
          · rw [hqo m h1 h2]; exact hpδ.2 m
    have hval : q ⬝ᵥ z = p ⬝ᵥ z + t * (z k - z j) := by
      simp only [q, add_dotProduct, smul_dotProduct, sub_dotProduct, single_dotProduct,
        smul_eq_mul]
      ring
    have := hqz q hq
    rw [hval, hpz] at this
    nlinarith
  refine ⟨p, hppos, ?_⟩
  have hzero : z = 0 := by
    funext l
    have hall : ∀ k, z k = z l := fun k => le_antisymm (hle k l) (hle l k)
    have hw := hpz
    simp only [dotProduct, hall, ← Finset.sum_mul, hpδ.1.2, one_mul] at hw
    exact hw
  rw [← hzero]
  exact hzZ

/-- **Correction to Exercise 17.C.2** (MWG, p. 642). Nonempty values are needed: the empty
correspondence satisfies conditions (i)-(v) (vacuously) and is convex valued, but `0 ∈ z(p)` has
no solution. -/
theorem exercise_17_C_2_needs_nonempty :
    UpperHemicontinuousMWG (posOrthant 2) (fun _ => (∅ : Set (Fin 2 → ℝ))) ∧
      CorrBoundary (fun _ => (∅ : Set (Fin 2 → ℝ))) ∧
      ¬ ∃ p ∈ posOrthant 2, (0 : Fin 2 → ℝ) ∈ (∅ : Set (Fin 2 → ℝ)) := by
  refine ⟨⟨fun _ _ _ _ _ _ hys _ _ => (hys 0).elim, fun _ _ _ => by simp⟩,
    fun _ _ _ _ _ _ _ hzs _ => (hzs 0).elim, fun ⟨_, _, h⟩ => h⟩

/-- **Exercise 17.C.2**, the single-valued case: an excess demand function `z` satisfying
(i)-(v) of Proposition 17.B.2 defines a correspondence `p ↦ {z(p)}` satisfying all hypotheses
of `exercise_17_C_2` (so they have an instance, e.g. `sqrtEconomy`), and `exercise_17_C_2`
recovers Proposition 17.C.1. -/
theorem exercise_17_C_2_of_function {z : (Fin L → ℝ) → Fin L → ℝ}
    (hz : IsStandardExcessDemand z) :
    UpperHemicontinuousMWG (posOrthant L) (fun p => {z p}) ∧
      (∀ p ∈ posOrthant L, ({z p} : Set (Fin L → ℝ)).Nonempty) ∧
      (∀ p ∈ posOrthant L, Convex ℝ ({z p} : Set (Fin L → ℝ))) ∧
      (∀ p ∈ posOrthant L, ∀ α : ℝ, 0 < α → ({z (α • p)} : Set (Fin L → ℝ)) = {z p}) ∧
      (∀ p ∈ posOrthant L, ∀ w ∈ ({z p} : Set (Fin L → ℝ)), p ⬝ᵥ w = 0) ∧
      (∃ s : ℝ, ∀ p ∈ posOrthant L, ∀ w ∈ ({z p} : Set (Fin L → ℝ)), ∀ l, -s < w l) ∧
      CorrBoundary (fun p => ({z p} : Set (Fin L → ℝ))) := by
  obtain ⟨s, -, hs⟩ := hz.boundedBelow
  refine ⟨⟨fun xs ys x y hxs hx hys hxl hyl => ?_, fun B hB hBc => ?_⟩,
    fun p _ => Set.singleton_nonempty _, fun p _ => convex_singleton _,
    fun p hp α hα => by rw [hz.homogeneous p hp α hα], fun p hp w hw => ?_,
    ⟨s, fun p hp w hw l => ?_⟩, fun ps p zs hps hlim hp0 hl hzs M => ?_⟩
  · have hzl : Tendsto (fun n => z (xs n)) atTop (𝓝 (z x)) :=
      (hz.continuous x hx).tendsto.comp (tendsto_nhdsWithin_iff.2
        ⟨hxl, Eventually.of_forall hxs⟩)
    have hys' : ys = fun n => z (xs n) := funext fun n => hys n
    rw [hys'] at hyl
    exact tendsto_nhds_unique hyl hzl
  · have himg : (⋃ x ∈ B, ({z x} : Set (Fin L → ℝ))) = z '' B := by
      ext y
      simp [eq_comm]
    rw [himg]
    exact ((hBc.image_of_continuousOn (hz.continuous.mono hB))).isBounded
  · rw [Set.mem_singleton_iff.1 hw]
    exact hz.walras p hp
  · rw [Set.mem_singleton_iff.1 hw]
    exact hs p hp l
  · have hzs' : zs = fun n => z (ps n) := funext fun n => hzs n
    rw [hzs']
    exact hz.boundary ps p hps hlim hp0 hl M

end MWG.PositiveEquilibriumTheory
