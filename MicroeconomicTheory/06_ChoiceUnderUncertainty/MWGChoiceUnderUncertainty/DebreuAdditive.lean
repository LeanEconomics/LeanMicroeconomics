/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGChoiceUnderUncertainty.StateDependent
import MWGClassicalDemand.UtilityRepresentation
import PreferenceProperties.PrimitiveAdditiveExistence

/-!
# The sure-thing axiom and additive representations

MWG, Section 6.E, p. 204: Proposition 6.E.2 (stated in the book without proof: "a complete
proof is too advanced"). A continuous rational preference on state-contingent money outcomes
`ℝ^S_+` satisfying the sure-thing axiom (Definition 6.E.4) has an additively separable
(extended expected utility) representation `∑_s u_s(x_s)`.

As printed the proposition is false: "at least three states" must be "at least three
*essential* states". If only two states matter, the sure-thing axiom reduces to the
independence of each state's ranking from the other, which does not give an additive
representation (the Thomsen condition fails). `proposition_6_E_2_false` gives a continuous
rational preference on `ℝ³_+` (and on `ℝ^S_+` for every `S ≥ 2`) satisfying the sure-thing
axiom, with utility `x₁ + x₂ + min(x₁, x₂)`, and with no representation `∑_s u_s(x_s)`.

The corrected statement (`proposition_6_E_2`) is Debreu's (1960) additive representation
theorem. It is derived from Kreps's Proposition 2.14 (`proposition_2_14_exists`, Kreps I,
p. 42, proved in the `PreferenceProperties` dependency by the local cardinal scales and
global continuation described in its construction guide), applied to the blocks
`B_s = ℝ₊`: MWG's continuity (Definition 3.C.1) is Kreps's open strict-preference graph
(`prefContinuous_iff_continuousPreference`), the sure-thing axiom is Kreps's strong
separability, and essential states are nontrivial blocks. The state utilities are moreover
continuous on `ℝ₊`.
-/

namespace MWG.ChoiceUnderUncertainty

open Set MWG.ConsumerChoice MWG.ClassicalDemand

/-- **Definition 6.E.4** (MWG, p. 204) on a domain `X` of outcome vectors (MWG: `X = ℝ^S_+`):
the sure-thing axiom for vectors of `X`. -/
def SureThingOn {S : Type*} (X : Set (S → ℝ)) (r : (S → ℝ) → (S → ℝ) → Prop) : Prop :=
  ∀ (E : Set S) (x x' y y' : S → ℝ), x ∈ X → x' ∈ X → y ∈ X → y' ∈ X →
    (∀ s ∉ E, x s = x' s ∧ y s = y' s) → (∀ s ∈ E, x s = y s ∧ x' s = y' s) →
      (r x x' ↔ r y y')

/-- The sure-thing axiom on all of `ℝ^S` gives it on every domain. -/
theorem SureThing.sureThingOn {S : Type*} {r : (S → ℝ) → (S → ℝ) → Prop} (h : SureThing r)
    (X : Set (S → ℝ)) : SureThingOn X r :=
  fun E x x' y y' _ _ _ _ hout hin => h E x x' y y' hout hin

/-- State `s` is essential (non-null) on `X`: two outcome vectors of `X` that differ only in
state `s` are strictly ranked. -/
def EssentialState {n : ℕ} (X : Set (Fin n → ℝ)) (r : (Fin n → ℝ) → (Fin n → ℝ) → Prop)
    (s : Fin n) : Prop :=
  ∃ x ∈ X, ∃ y ∈ X, (∀ t, t ≠ s → x t = y t) ∧ r x y ∧ ¬ r y x

/-- **Proposition 6.E.2** (MWG, p. 204), corrected (Debreu 1960). If `≿` on `ℝ^S_+` is
rational, continuous (Definition 3.C.1) and satisfies the sure-thing axiom, and at least three
states are essential, then `≿` has an additively separable representation
`x ≿ x' ⟺ ∑_s u_s(x'_s) ≤ ∑_s u_s(x_s)`, with every `u_s` continuous on `ℝ₊`. The book asks
for at least three states; `proposition_6_E_2_false` shows that three essential states are
needed. -/
theorem proposition_6_E_2 {n : ℕ} {r : (Fin n → ℝ) → (Fin n → ℝ) → Prop}
    (hr : RationalOn (nonnegOrthant n) r) (hc : PrefContinuous (nonnegOrthant n) r)
    (hs : SureThingOn (nonnegOrthant n) r)
    (h3 : ∃ s₁ s₂ s₃, s₁ ≠ s₂ ∧ s₁ ≠ s₃ ∧ s₂ ≠ s₃ ∧ EssentialState (nonnegOrthant n) r s₁ ∧
      EssentialState (nonnegOrthant n) r s₂ ∧ EssentialState (nonnegOrthant n) r s₃) :
    ∃ u : Fin n → ℝ → ℝ, (∀ s, ContinuousOn (u s) (Ici 0)) ∧
      ∀ x ∈ nonnegOrthant n, ∀ y ∈ nonnegOrthant n,
        (r x y ↔ ∑ s, u s (y s) ≤ ∑ s, u s (x s)) := by
  classical
  let emb : (∀ _ : Fin n, Ici (0 : ℝ)) → Fin n → ℝ := fun a i => (a i : ℝ)
  have hemb (a : ∀ _ : Fin n, Ici (0 : ℝ)) : emb a ∈ nonnegOrthant n := fun i => (a i).2
  let r' : (∀ _ : Fin n, Ici (0 : ℝ)) → (∀ _ : Fin n, Ici (0 : ℝ)) → Prop :=
    fun a b => r (emb a) (emb b)
  have hrat : Kreps.PreferenceProperties.Rational r' :=
    ⟨fun a b => hr.1 _ (hemb a) _ (hemb b),
      fun a b c h1 h2 => hr.2 _ (hemb a) _ (hemb b) _ (hemb c) h1 h2⟩
  have hcont : Kreps.PreferenceProperties.ContinuousPreference r' := by
    have ho := (prefContinuous_iff_continuousPreference hr).mp hc
    let e : (∀ _ : Fin n, Ici (0 : ℝ)) → nonnegOrthant n := fun a => ⟨emb a, hemb a⟩
    have he : Continuous e :=
      Continuous.subtype_mk (continuous_pi fun i => continuous_subtype_val.comp
        (continuous_apply i)) _
    exact ho.preimage ((he.comp continuous_fst).prodMk (he.comp continuous_snd))
  have hsep : Kreps.PreferenceProperties.StronglySeparable r' := by
    intro S a b z t
    refine hs (↑S) _ _ _ _ (hemb _) (hemb _) (hemb _) (hemb _) (fun s hsS => ?_)
      (fun s hsS => ?_)
    · have hsS' : s ∉ S := hsS
      simp only [emb, Finset.piecewise_eq_of_notMem _ _ _ hsS', and_self]
    · have hsS' : s ∈ S := hsS
      simp only [emb, Finset.piecewise_eq_of_mem _ _ _ hsS', and_self]
  have hnt (s : Fin n) (h : EssentialState (nonnegOrthant n) r s) :
      Kreps.PreferenceProperties.NontrivialBlock r' s := by
    obtain ⟨x, hx, y, hy, hxy, h1, h2⟩ := h
    let z : ∀ _ : Fin n, Ici (0 : ℝ) := fun i => ⟨x i, hx i⟩
    refine ⟨⟨x s, hx s⟩, ⟨y s, hy s⟩, z, ?_⟩
    have ex : emb (Function.update z s ⟨x s, hx s⟩) = x := by
      funext t
      by_cases hts : t = s
      · subst hts; simp [emb]
      · simp [emb, z]
    have ey : emb (Function.update z s ⟨y s, hy s⟩) = y := by
      funext t
      by_cases hts : t = s
      · subst hts; simp [emb]
      · simp [emb, Function.update_of_ne hts, z, hxy t hts]
    exact ⟨by change r _ _; rw [ex, ey]; exact h1, by change ¬ r _ _; rw [ex, ey]; exact h2⟩
  have hthree : Kreps.PreferenceProperties.ThreeNontrivialBlocks r' := by
    obtain ⟨s₁, s₂, s₃, h12, h13, h23, e1, e2, e3⟩ := h3
    exact ⟨s₁, s₂, s₃, h12, h13, h23, hnt s₁ e1, hnt s₂ e2, hnt s₃ e3⟩
  have hpc : PreconnectedSpace (Ici (0 : ℝ)) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Ici
  obtain ⟨w, hwc, hwr⟩ := Kreps.PreferenceProperties.proposition_2_14_exists
    (B := fun _ : Fin n => Ici (0 : ℝ)) hrat hcont hsep hthree
  refine ⟨fun s t => if h : 0 ≤ t then w s ⟨t, h⟩ else 0, fun s => ?_, fun x hx y hy => ?_⟩
  · have hproj : Continuous (Set.projIci (0 : ℝ)) :=
      (continuous_const.max continuous_id).subtype_mk _
    refine ((hwc s).comp hproj).continuousOn.congr fun t ht => ?_
    have ht' : (0 : ℝ) ≤ t := ht
    simp [ht', Set.projIci_of_mem ht]
  · have := hwr (fun i => ⟨x i, hx i⟩) (fun i => ⟨y i, hy i⟩)
    have hx' : ∀ s, 0 ≤ x s := hx
    have hy' : ∀ s, 0 ≤ y s := hy
    simp only [Kreps.PreferenceProperties.AdditiveUtility] at this
    simp only [hx', hy', ↓reduceDIte]
    exact this

/-- The utility `V(x) = x₀ + x₁ + min(x₀, x₁)` of the counterexample to Proposition 6.E.2 as
printed: only the first two states matter. -/
noncomputable def thomsenV {k : ℕ} (x : Fin (k + 2) → ℝ) : ℝ := x 0 + x 1 + min (x 0) (x 1)

/-- The preference represented by `thomsenV`. -/
def thomsenPref {k : ℕ} (x y : Fin (k + 2) → ℝ) : Prop := thomsenV y ≤ thomsenV x

theorem thomsen_mono_left (a b c : ℝ) : a + c + min a c ≤ b + c + min b c ↔ a ≤ b := by
  constructor
  · intro h
    by_contra hn
    push Not at hn
    have : min b c ≤ min a c := min_le_min_right c hn.le
    linarith
  · intro h
    have : min a c ≤ min b c := min_le_min_right c h
    linarith

theorem thomsen_mono_right (a b c : ℝ) : c + a + min c a ≤ c + b + min c b ↔ a ≤ b := by
  rw [min_comm c a, min_comm c b, add_comm c a, add_comm c b]
  exact thomsen_mono_left a b c

/-- The counterexample preference is rational on `ℝ^S_+`. -/
theorem thomsenPref_rational (k : ℕ) : RationalOn (nonnegOrthant (k + 2)) thomsenPref :=
  ⟨fun _ _ _ _ => le_total _ _, fun _ _ _ _ _ _ h1 h2 => h2.trans h1⟩

/-- The counterexample preference is continuous (Definition 3.C.1). -/
theorem thomsenPref_continuous (k : ℕ) : PrefContinuous (nonnegOrthant (k + 2)) thomsenPref := by
  intro xs ys x y _ _ _ _ h hx hy
  have hV : Continuous (thomsenV (k := k)) := by unfold thomsenV; fun_prop
  exact le_of_tendsto_of_tendsto' ((hV.tendsto y).comp hy) ((hV.tendsto x).comp hx) h

/-- The counterexample preference satisfies the sure-thing axiom (on all of `ℝ^S`). -/
theorem thomsenPref_sureThing (k : ℕ) : SureThing (thomsenPref (k := k)) := by
  intro E x x' y y' hout hin
  unfold thomsenPref thomsenV
  by_cases h0 : (0 : Fin (k + 2)) ∈ E <;> by_cases h1 : (1 : Fin (k + 2)) ∈ E
  · rw [(hin 0 h0).1, (hin 0 h0).2, (hin 1 h1).1, (hin 1 h1).2]
  · rw [(hin 0 h0).1, (hin 0 h0).2, (hout 1 h1).1, (hout 1 h1).2, thomsen_mono_left,
      thomsen_mono_left]
  · rw [(hin 1 h1).1, (hin 1 h1).2, (hout 0 h0).1, (hout 0 h0).2, thomsen_mono_right,
      thomsen_mono_right]
  · rw [(hout 0 h0).1, (hout 0 h0).2, (hout 1 h1).1, (hout 1 h1).2]
    simp

/-- The outcome vector paying `a` in state `0`, `b` in state `1` and `0` elsewhere. -/
noncomputable def twoStateVec {k : ℕ} (a b : ℝ) : Fin (k + 2) → ℝ :=
  fun s => if s = 0 then a else if s = 1 then b else 0

theorem twoStateVec_zero {k : ℕ} (a b : ℝ) : twoStateVec (k := k) a b 0 = a := by
  simp [twoStateVec]

theorem twoStateVec_one {k : ℕ} (a b : ℝ) : twoStateVec (k := k) a b 1 = b := by
  have : (1 : Fin (k + 2)) ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp at this
  simp [twoStateVec, this]

theorem twoStateVec_mem {k : ℕ} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    twoStateVec (k := k) a b ∈ nonnegOrthant (k + 2) := by
  intro s
  unfold twoStateVec
  split_ifs
  · exact ha
  · exact hb
  · exact le_rfl

theorem thomsenV_twoStateVec {k : ℕ} (a b : ℝ) :
    thomsenV (twoStateVec (k := k) a b) = a + b + min a b := by
  unfold thomsenV; rw [twoStateVec_zero, twoStateVec_one]

/-- The counterexample preference has no additively separable representation on `ℝ^S_+`: the
Thomsen condition fails, `(0,4) ∼ (2,1)` and `(2,2) ∼ (1,4)` but `(0,2) ≺ (1,1)`, whereas any
`f(x₀) + g(x₁)` would give `(0,2) ∼ (1,1)`. -/
theorem thomsenPref_not_additive (k : ℕ) : ¬ ∃ u : Fin (k + 2) → ℝ → ℝ,
    ∀ x ∈ nonnegOrthant (k + 2), ∀ y ∈ nonnegOrthant (k + 2),
      (thomsenPref x y ↔ ∑ s, u s (y s) ≤ ∑ s, u s (x s)) := by
  rintro ⟨u, hu⟩
  set T : ℝ → ℝ → ℝ := fun a b => ∑ s, u s (twoStateVec (k := k) a b s) with hT
  have hrect (a b c d : ℝ) : T a b + T c d = T a d + T c b := by
    simp only [hT, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    unfold twoStateVec
    split_ifs <;> ring
  have hrep {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
      (c + d + min c d ≤ a + b + min a b ↔ T c d ≤ T a b) := by
    have := hu _ (twoStateVec_mem (k := k) ha hb) _ (twoStateVec_mem (k := k) hc hd)
    simp only [thomsenPref, thomsenV_twoStateVec] at this
    exact this
  have e1 : T 0 4 = T 2 1 := le_antisymm
    ((hrep (by norm_num) (by norm_num) (by norm_num) (by norm_num)).mp (by norm_num))
    ((hrep (by norm_num) (by norm_num) (by norm_num) (by norm_num)).mp (by norm_num))
  have e2 : T 2 2 = T 1 4 := le_antisymm
    ((hrep (by norm_num) (by norm_num) (by norm_num) (by norm_num)).mp (by norm_num))
    ((hrep (by norm_num) (by norm_num) (by norm_num) (by norm_num)).mp (by norm_num))
  have r1 := hrect 0 4 2 2
  have r2 := hrect 2 1 1 4
  have hlt : ¬ (1 + 1 + min (1 : ℝ) 1 ≤ 0 + 2 + min 0 2) := by norm_num
  rw [hrep (by norm_num) (by norm_num) (by norm_num) (by norm_num)] at hlt
  linarith

/-- **Proposition 6.E.2** (MWG, p. 204) as printed is false, for every number `S ≥ 2` of states
(in particular `S = 3`): the counterexample preference is rational, continuous and satisfies
the sure-thing axiom on `ℝ^S_+`, but has no additively separable representation. Only two of
its states are essential (`thomsenPref_essential`). -/
theorem proposition_6_E_2_false (k : ℕ) : ¬ ∀ r : (Fin (k + 2) → ℝ) → (Fin (k + 2) → ℝ) → Prop,
    RationalOn (nonnegOrthant (k + 2)) r → PrefContinuous (nonnegOrthant (k + 2)) r →
      SureThingOn (nonnegOrthant (k + 2)) r → ∃ u : Fin (k + 2) → ℝ → ℝ,
        ∀ x ∈ nonnegOrthant (k + 2), ∀ y ∈ nonnegOrthant (k + 2),
          (r x y ↔ ∑ s, u s (y s) ≤ ∑ s, u s (x s)) :=
  fun h => thomsenPref_not_additive k (h _ (thomsenPref_rational k) (thomsenPref_continuous k)
    ((thomsenPref_sureThing k).sureThingOn _))

/-- In the counterexample, states `0` and `1` are essential and every other state is not, so
it has exactly two essential states. -/
theorem thomsenPref_essential (k : ℕ) :
    EssentialState (nonnegOrthant (k + 2)) thomsenPref 0 ∧
      EssentialState (nonnegOrthant (k + 2)) thomsenPref 1 ∧
      ∀ s, s ≠ 0 → s ≠ 1 → ¬ EssentialState (nonnegOrthant (k + 2)) thomsenPref s := by
  refine ⟨⟨twoStateVec 1 0, twoStateVec_mem (by norm_num) le_rfl, twoStateVec 0 0,
    twoStateVec_mem le_rfl le_rfl, fun t ht => ?_, ?_, ?_⟩,
    ⟨twoStateVec 0 1, twoStateVec_mem le_rfl (by norm_num), twoStateVec 0 0,
    twoStateVec_mem le_rfl le_rfl, fun t ht => ?_, ?_, ?_⟩, ?_⟩
  · simp [twoStateVec, ht]
  · simp only [thomsenPref, thomsenV_twoStateVec]; norm_num
  · simp only [thomsenPref, thomsenV_twoStateVec]; norm_num
  · unfold twoStateVec; split_ifs <;> simp_all
  · simp only [thomsenPref, thomsenV_twoStateVec]; norm_num
  · simp only [thomsenPref, thomsenV_twoStateVec]; norm_num
  · rintro s h0 h1 ⟨x, -, y, -, hxy, -, h2⟩
    apply h2
    unfold thomsenPref thomsenV
    rw [hxy 0 (Ne.symm h0), hxy 1 (Ne.symm h1)]

/-- A concrete instance of the hypotheses of the corrected Proposition 6.E.2: the risk-neutral
preference `∑_s x_s` on `ℝ³_+` is rational, continuous, satisfies the sure-thing axiom, and all
three states are essential. -/
theorem proposition_6_E_2_instance :
    let r : (Fin 3 → ℝ) → (Fin 3 → ℝ) → Prop := fun x y => ∑ s, y s ≤ ∑ s, x s
    RationalOn (nonnegOrthant 3) r ∧ PrefContinuous (nonnegOrthant 3) r ∧
      SureThingOn (nonnegOrthant 3) r ∧ ∀ s, EssentialState (nonnegOrthant 3) r s := by
  intro r
  refine ⟨⟨fun x _ y _ => le_total _ _, fun _ _ _ _ _ _ h1 h2 => h2.trans h1⟩, ?_, ?_, ?_⟩
  · intro xs ys x y _ _ _ _ h hx hy
    have hV : Continuous fun z : Fin 3 → ℝ => ∑ s, z s := by fun_prop
    exact le_of_tendsto_of_tendsto' ((hV.tendsto y).comp hy) ((hV.tendsto x).comp hx) h
  · exact (sureThing_of_additive (fun _ t => t)).sureThingOn _
  · intro s
    refine ⟨Pi.single s 1, fun t => ?_, 0, fun _ => le_rfl, fun t ht => ?_, ?_, ?_⟩
    · by_cases h : t = s
      · subst h; simp
      · simp [h]
    · simp [ht]
    · simp only [r]; simp
    · simp only [r]; simp

end MWG.ChoiceUnderUncertainty
