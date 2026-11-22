/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGWelfareTheorems.Exercise16G5

/-!
# The second welfare theorem for Lindahl equilibria (MWG Example 16.G.3, p. 570)

"Every Pareto optimal allocation can be implemented using a Lindahl equilibrium (with appropriate
wealth transfers and, perhaps, with the usual quasiequilibrium qualification)." We carry out the
book's reduction. With `n` consumers the artificial economy has `n + 1` commodities: the private
good (coordinate `0`) and one personalized public good per consumer (coordinate `i.succ`).

* Consumer `i`'s consumption set is `{v : v₀ ≥ 0, v_{i+1} ≥ 0, v_{k+1} = 0 for k ≠ i}` and her
  preference compares `(v₀, v_{i+1})` by `≿ᵢ` (`lindahlArtificialEconomy`).
* The firm's technology `{(-z, q, ..., q) : z ≥ 0, q ≤ f(z)}` is convex when `f` is concave.
* A Pareto optimum of the public goods economy is a Pareto optimum of the artificial economy
  (`lindahl_pareto_artificial`); Proposition 16.D.1 gives a price quasiequilibrium with transfers
  there, which translates into a Lindahl quasiequilibrium with transfers (`IsLindahlQuasiEqm`,
  the corrected Definition 16.G.1 with condition (ii) weakened as in Definition 16.D.1):
  `lindahl_second_welfare`.
* A concrete instance: one consumer with `u = x₁ + x₂`, `f(z) = z`, `ω̄₁ = 1`
  (`lindahl_second_welfare_instance`).
-/

namespace MWG.WelfareTheorems

open MWG.ConsumerChoice MWG.ClassicalDemand MWG.Production Kreps.PreferenceProperties
open MWG.CompetitiveMarkets (Allocation)

variable {n : ℕ}

/-- Consumer `i`'s bundle `(a, b)` (private good, public good) as a vector of the artificial
economy: `a` in coordinate `0`, `b` in coordinate `i.succ`, zero elsewhere. -/
def lindahlEmb (i : Fin n) (a b : ℝ) : Fin (n + 1) → ℝ :=
  Fin.cons a (Pi.single i b : Fin n → ℝ)

/-- Consumer `i`'s view `(v₀, v_{i+1})` of a vector of the artificial economy. -/
def lindahlProj (i : Fin n) (v : Fin (n + 1) → ℝ) : Fin 2 → ℝ := ![v 0, v i.succ]

/-- Consumer `i`'s consumption set in the artificial economy. -/
def lindahlX (i : Fin n) : Set (Fin (n + 1) → ℝ) :=
  {v | 0 ≤ v 0 ∧ 0 ≤ v i.succ ∧ ∀ k : Fin n, k ≠ i → v k.succ = 0}

/-- The firm's technology `{(-z, q, ..., q) : z ≥ 0, q ≤ f(z)}` in the artificial economy. -/
def lindahlY (f : ℝ → ℝ) : Set (Fin (n + 1) → ℝ) :=
  {y | 0 ≤ -y 0 ∧ ∃ q, q ≤ f (-y 0) ∧ ∀ k : Fin n, y k.succ = q}

/-- **Example 16.G.3** (MWG, p. 569). The artificial economy with personalized commodities. -/
def lindahlArtificialEconomy (pref : Fin n → (Fin 2 → ℝ) → (Fin 2 → ℝ) → Prop) (ω₁ : ℝ)
    (f : ℝ → ℝ) : PrefEconomy (Fin n) Unit (n + 1) where
  X := lindahlX
  pref := fun i v v' => pref i (lindahlProj i v) (lindahlProj i v')
  Y := fun _ => lindahlY f
  ω := Fin.cons ω₁ 0

/-- **Example 16.G.3** (MWG, p. 570). A Lindahl quasiequilibrium with transfers: Definition
16.G.1 (corrected) with prices not all zero and condition (ii) replaced by "anything strictly
preferred to `(x*₁ᵢ, q*)` costs at least `wᵢ`" (as in Definition 16.D.1). -/
def IsLindahlQuasiEqm (pref : Fin n → (Fin 2 → ℝ) → (Fin 2 → ℝ) → Prop) (ω₁ : ℝ)
    (f : ℝ → ℝ) (x : Fin n → ℝ) (q z p₁ : ℝ) (p₂ w : Fin n → ℝ) : Prop :=
  (p₁ ≠ 0 ∨ ∃ i, p₂ i ≠ 0) ∧
    ∑ i, w i = p₁ * ω₁ + (∑ i, p₂ i) * q - p₁ * z ∧
    (q ≤ f z ∧ 0 ≤ z ∧ ∀ q' z', 0 ≤ z' → q' ≤ f z' →
      (∑ i, p₂ i) * q' - p₁ * z' ≤ (∑ i, p₂ i) * q - p₁ * z) ∧
    (∀ i, ∀ v : Fin 2 → ℝ, (∀ l, 0 ≤ v l) → Strict (pref i) v ![x i, q] →
      w i ≤ p₁ * v 0 + p₂ i * v 1) ∧
    ∑ i, x i + z = ω₁

theorem lindahlEmb_zero (i : Fin n) (a b : ℝ) : lindahlEmb i a b 0 = a := rfl

theorem lindahlEmb_succ (i k : Fin n) (a b : ℝ) :
    lindahlEmb i a b k.succ = (Pi.single i b : Fin n → ℝ) k := rfl

theorem lindahlProj_emb (i : Fin n) (a b : ℝ) : lindahlProj i (lindahlEmb i a b) = ![a, b] := by
  funext l
  fin_cases l <;> simp [lindahlProj, lindahlEmb_zero, lindahlEmb_succ]

/-- The value of a vector of the artificial economy. -/
theorem dot_succ (p v : Fin (n + 1) → ℝ) :
    p ⬝ᵥ v = p 0 * v 0 + ∑ k : Fin n, p k.succ * v k.succ := by
  simp [dotProduct, Fin.sum_univ_succ]

theorem dot_lindahlEmb (p : Fin (n + 1) → ℝ) (i : Fin n) (a b : ℝ) :
    p ⬝ᵥ lindahlEmb i a b = p 0 * a + p i.succ * b := by
  rw [dot_succ, lindahlEmb_zero]
  congr 1
  rw [Finset.sum_eq_single i (fun k _ hk => by simp [lindahlEmb_succ, hk]) (by simp)]
  simp [lindahlEmb_succ]

/-- A vector of consumer `i`'s consumption set is the embedding of its projection. -/
theorem emb_proj {i : Fin n} {v : Fin (n + 1) → ℝ}
    (hv : v ∈ lindahlX i) :
    v = lindahlEmb i (v 0) (v i.succ) := by
  funext l
  refine Fin.cases ?_ (fun k => ?_) l
  · rfl
  · rw [lindahlEmb_succ]
    by_cases hk : k = i
    · subst hk; simp
    · rw [hv.2.2 k hk]; simp [hk]

theorem emb_mem (i : Fin n) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    lindahlEmb i a b ∈ lindahlX i :=
  ⟨ha, by simpa [lindahlEmb_succ] using hb, fun k hk => by simp [lindahlEmb_succ, hk]⟩

theorem proj_mem {i : Fin n} {v : Fin (n + 1) → ℝ} (hv : v ∈ lindahlX i) :
    lindahlProj i v ∈ nonnegOrthant 2 := fun l => by
  fin_cases l
  · exact hv.1
  · exact hv.2.1

/-- Embedding preserves Euclidean distances between bundles of consumer `i`. -/
theorem euclidDist_emb (i : Fin n) (a b c d : ℝ) :
    euclidDist (lindahlEmb i a b) (lindahlEmb i c d) = euclidDist ![a, b] ![c, d] := by
  unfold euclidDist
  congr 1
  rw [Fin.sum_univ_succ, Fin.sum_univ_two]
  simp only [lindahlEmb_zero, lindahlEmb_succ, Matrix.cons_val_zero, Matrix.cons_val_one]
  congr 1
  rw [Finset.sum_eq_single i (fun k _ hk => by simp [hk]) (by simp)]
  simp

/-- The artificial allocation of a public goods allocation. -/
def lindahlAlloc (x : Fin n → ℝ) (q z : ℝ) : Allocation (Fin n) Unit (n + 1) :=
  ⟨fun i => lindahlEmb i (x i) q, fun _ => Fin.cons (-z) (fun _ => q)⟩

/-- **Example 16.G.3** (MWG, p. 569). A Pareto optimum of the public goods economy (with `n ≥ 1`
consumers) is a Pareto optimum of the artificial economy. -/
theorem lindahl_pareto_artificial [NeZero n] {pref : Fin n → (Fin 2 → ℝ) → (Fin 2 → ℝ) → Prop}
    {ω₁ : ℝ} {f : ℝ → ℝ} {x : Fin n → ℝ} {q z : ℝ}
    (hpo : PublicParetoOptimal pref ω₁ f x q z) :
    (lindahlArtificialEconomy pref ω₁ f).IsParetoOptimal (lindahlAlloc x q z) := by
  obtain ⟨⟨hx, hq, hz, hf, hc⟩, hno⟩ := hpo
  refine ⟨⟨⟨fun i => emb_mem i (hx i) hq, fun _ => ⟨by simpa [lindahlAlloc] using hz, q,
    by simpa [lindahlAlloc] using hf, fun k => by simp [lindahlAlloc]⟩⟩, ?_⟩, ?_⟩
  · funext l
    refine Fin.cases ?_ (fun k => ?_) l
    · change (∑ i, lindahlEmb i (x i) q) 0 = (Fin.cons ω₁ 0 : Fin (n + 1) → ℝ) 0 +
        (∑ _j : Unit, (Fin.cons (-z) (fun _ => q) : Fin (n + 1) → ℝ)) 0
      simp only [Finset.sum_apply, lindahlEmb_zero, Fin.cons_zero, Finset.univ_unique,
        Finset.sum_singleton]
      linarith
    · change (∑ i, lindahlEmb i (x i) q) k.succ = (Fin.cons ω₁ 0 : Fin (n + 1) → ℝ) k.succ +
        (∑ _j : Unit, (Fin.cons (-z) (fun _ => q) : Fin (n + 1) → ℝ)) k.succ
      simp only [Finset.sum_apply, lindahlEmb_succ, Fin.cons_succ, Finset.univ_unique,
        Finset.sum_singleton, Pi.zero_apply, zero_add]
      rw [Finset.sum_eq_single k (fun i _ hi => by simp [Ne.symm hi]) (by simp)]
      simp
  · rintro ⟨a', ⟨⟨hx', hy'⟩, hc'⟩, hle, k, hk⟩
    obtain ⟨hz', q', hq'f, hq'⟩ := hy' ()
    -- consumer `i`'s public good is the common output `q'`
    have hpub : ∀ i, a'.x i i.succ = q' := by
      intro i
      have h1 := congrFun hc' i.succ
      simp only [Finset.sum_apply, Pi.add_apply, lindahlArtificialEconomy, Fin.cons_succ,
        Pi.zero_apply, zero_add, Finset.univ_unique, Finset.sum_singleton, hq'] at h1
      rw [← h1, Finset.sum_eq_single i (fun j _ hj => (hx' j).2.2 i (Ne.symm hj)) (by simp)]
    have hproj : ∀ i, lindahlProj i (a'.x i) = ![a'.x i 0, q'] := fun i => by
      simp [lindahlProj, hpub i]
    have hproj0 : ∀ i, lindahlProj i ((lindahlAlloc x q z).x i) = ![x i, q] := fun i =>
      lindahlProj_emb i (x i) q
    apply hno
    refine ⟨fun i => a'.x i 0, q', -a'.y () 0, ⟨fun i => (hx' i).1, ?_, hz', hq'f, ?_⟩,
      fun i => ?_, k, ?_⟩
    · have := (hx' (0 : Fin n)).2.1; rwa [hpub] at this
    · have h1 := congrFun hc' 0
      simp only [Finset.sum_apply, Pi.add_apply, lindahlArtificialEconomy, Fin.cons_zero,
        Finset.univ_unique, Finset.sum_singleton] at h1
      linarith
    · have h1 : pref i (lindahlProj i (a'.x i)) (lindahlProj i ((lindahlAlloc x q z).x i)) :=
        hle i
      rwa [hproj, hproj0] at h1
    · have h1 : Strict (pref k) (lindahlProj k (a'.x k))
          (lindahlProj k ((lindahlAlloc x q z).x k)) := hk
      rwa [hproj, hproj0] at h1

/-- **Example 16.G.3** (MWG, p. 570): the second welfare theorem for Lindahl equilibria. With
`n ≥ 1` consumers whose preferences on `ℝ²₊` are rational, convex and locally nonsatiated and a
concave production function `f` on `[0, ∞)`, every Pareto optimal allocation of the public goods
economy is a Lindahl quasiequilibrium with transfers for some personalized prices
`(p₁, p₂₁, ..., p₂ₙ) ≠ 0`, with wealth levels `wᵢ = p₁x*₁ᵢ + p₂ᵢq*`. -/
theorem lindahl_second_welfare [NeZero n] {pref : Fin n → (Fin 2 → ℝ) → (Fin 2 → ℝ) → Prop}
    (hr : ∀ i, RationalOn (nonnegOrthant 2) (pref i))
    (hc : ∀ i, PrefConvex (nonnegOrthant 2) (pref i))
    (hlns : ∀ i, LocallyNonsatiated (nonnegOrthant 2) (pref i)) {ω₁ : ℝ} {f : ℝ → ℝ}
    (hf : ConcaveOn ℝ (Set.Ici 0) f) {x : Fin n → ℝ} {q z : ℝ}
    (hpo : PublicParetoOptimal pref ω₁ f x q z) :
    ∃ (p₁ : ℝ) (p₂ : Fin n → ℝ), IsLindahlQuasiEqm pref ω₁ f x q z p₁ p₂
      (fun i => p₁ * x i + p₂ i * q) := by
  set E := lindahlArtificialEconomy pref ω₁ f with hE
  -- hypotheses of Proposition 16.D.1 for the artificial economy
  have hY : ∀ j, Convex ℝ (E.Y j) := by
    intro _ y ⟨hy0, qy, hqy, hyq⟩ y' ⟨hy0', qy', hqy', hyq'⟩ a b ha hb hab
    refine ⟨by simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; nlinarith, a * qy + b * qy',
      ?_, fun k => by simp [hyq, hyq']⟩
    have hcon := hf.2 (Set.mem_Ici.mpr hy0) (Set.mem_Ici.mpr hy0') ha hb hab
    simp only [smul_eq_mul] at hcon
    have h0 : -(a • y + b • y') 0 = a * -y 0 + b * -y' 0 := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [h0]
    nlinarith [mul_le_mul_of_nonneg_left hqy ha, mul_le_mul_of_nonneg_left hqy' hb]
  have hvec : ∀ w : Fin 2 → ℝ, (![w 0, w 1] : Fin 2 → ℝ) = w := fun w => by
    funext l; fin_cases l <;> rfl
  have hrat : ∀ i, RationalOn (E.X i) (E.pref i) := fun i =>
    ⟨fun v hv v' hv' => (hr i).1 _ (proj_mem hv) _ (proj_mem hv'),
      fun v hv v' hv' v'' hv'' h1 h2 => (hr i).2 _ (proj_mem hv) _ (proj_mem hv') _
        (proj_mem hv'') h1 h2⟩
  have hprojlin : ∀ (i : Fin n) (v v' : Fin (n + 1) → ℝ) (a b : ℝ),
      lindahlProj i (a • v + b • v') = a • lindahlProj i v + b • lindahlProj i v' := by
    intro i v v' a b; funext l; fin_cases l <;> simp [lindahlProj]
  have hconvE : ∀ i, PrefConvex (E.X i) (E.pref i) := by
    intro i v0 hv0 v ⟨hv, hvr⟩ v' ⟨hv', hvr'⟩ a b ha hb hab
    refine ⟨⟨?_, ?_, fun k hk => ?_⟩, ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      nlinarith [mul_nonneg ha hv.1, mul_nonneg hb hv'.1]
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      nlinarith [mul_nonneg ha hv.2.1, mul_nonneg hb hv'.2.1]
    · simp [hv.2.2 k hk, hv'.2.2 k hk]
    · change pref i (lindahlProj i (a • v + b • v')) (lindahlProj i v0)
      rw [hprojlin]
      exact (hc i _ (proj_mem hv0) ⟨proj_mem hv, hvr⟩ ⟨proj_mem hv', hvr'⟩ ha hb hab).2
  have hlnsE : ∀ i, LocallyNonsatiated (E.X i) (E.pref i) := by
    intro i v hv ε hε
    obtain ⟨w, hw, hd, hs⟩ := hlns i (lindahlProj i v) (proj_mem hv) ε hε
    refine ⟨lindahlEmb i (w 0) (w 1), emb_mem i (hw 0) (hw 1), ?_, ?_⟩
    · rw [emb_proj hv, euclidDist_emb, hvec]
      exact hd
    · change Strict (pref i) (lindahlProj i (lindahlEmb i (w 0) (w 1))) (lindahlProj i v)
      rw [lindahlProj_emb, hvec]
      exact hs
  obtain ⟨p, hp, hq⟩ := proposition_16_D_1 hY hrat hconvE hlnsE (lindahl_pareto_artificial hpo)
  obtain ⟨⟨hx, hq0, hz, hf', hc'⟩, -⟩ := hpo
  have hdotω : p ⬝ᵥ E.ω = p 0 * ω₁ := by
    change p ⬝ᵥ (Fin.cons ω₁ 0 : Fin (n + 1) → ℝ) = _
    simp [dot_succ]
  have hdoty : ∀ q' z' : ℝ, p ⬝ᵥ (Fin.cons (-z') (fun _ => q') : Fin (n + 1) → ℝ) =
      (∑ i : Fin n, p i.succ) * q' - p 0 * z' := fun q' z' => by
    rw [dot_succ, Finset.sum_mul]; simp; ring
  have hwx : ∀ i, p ⬝ᵥ (lindahlAlloc x q z).x i = p 0 * x i + p i.succ * q := fun i =>
    dot_lindahlEmb p i (x i) q
  refine ⟨p 0, fun i => p i.succ, ⟨?_, ?_, ⟨hf', hz, fun q' z' hz' hq' => ?_⟩, fun i v hv hs => ?_,
    hc'⟩⟩
  · by_contra h
    push Not at h
    apply hp
    funext l
    refine Fin.cases ?_ (fun k => ?_) l
    · exact h.1
    · exact h.2 k
  · have := hq.2.1
    simp only [hwx, hdotω, Finset.univ_unique, Finset.sum_singleton] at this
    change ∑ i, (p 0 * x i + p i.succ * q) = _
    rw [this]
    change p 0 * ω₁ + p ⬝ᵥ (Fin.cons (-z) (fun _ => q) : Fin (n + 1) → ℝ) = _
    rw [hdoty]; ring
  · have := (hq.2.2.1 ()).2 (Fin.cons (-z') (fun _ => q'))
      ⟨by simpa using hz', q', by simpa using hq', fun k => by simp⟩
    change p ⬝ᵥ _ ≤ p ⬝ᵥ (Fin.cons (-z) (fun _ => q) : Fin (n + 1) → ℝ) at this
    rw [hdoty, hdoty] at this
    exact this
  · have h1 := (hq.2.2.2.1 i).2 (lindahlEmb i (v 0) (v 1)) (emb_mem i (hv 0) (hv 1)) (by
      change Strict (pref i) (lindahlProj i (lindahlEmb i (v 0) (v 1)))
        (lindahlProj i (lindahlEmb i (x i) q))
      rw [lindahlProj_emb, lindahlProj_emb, hvec]
      exact hs)
    have h2 : p ⬝ᵥ (lindahlAlloc x q z).x i ≤ p ⬝ᵥ lindahlEmb i (v 0) (v 1) := h1
    rw [hwx, dot_lindahlEmb] at h2
    exact h2

/-- **Example 16.G.3** (MWG, p. 570), a concrete instance of `lindahl_second_welfare`: one
consumer with `u(x₁, x₂) = x₁ + x₂` (rational, convex, locally nonsatiated), `f(z) = z`,
`ω̄₁ = 1`. The allocation `x₁ = q = z = 1/2` is Pareto optimal and hence a Lindahl
quasiequilibrium with transfers. -/
theorem lindahl_second_welfare_instance :
    PublicParetoOptimal (fun _ : Fin 1 => utilityPref lindahlExampleU) 1 id (fun _ => 1 / 2)
        (1 / 2) (1 / 2) ∧
      ∃ (p₁ : ℝ) (p₂ : Fin 1 → ℝ), IsLindahlQuasiEqm (fun _ => utilityPref lindahlExampleU) 1 id
        (fun _ => 1 / 2) (1 / 2) (1 / 2) p₁ p₂ (fun i => p₁ * (1 / 2) + p₂ i * (1 / 2)) := by
  have hpo : PublicParetoOptimal (fun _ : Fin 1 => utilityPref lindahlExampleU) 1 id
      (fun _ => 1 / 2) (1 / 2) (1 / 2) := by
    refine ⟨⟨fun _ => by norm_num, by norm_num, by norm_num, le_rfl, by simp; norm_num⟩, ?_⟩
    rintro ⟨x', q', z', ⟨hx', hq', hz', hf', hc'⟩, -, k, hk⟩
    apply hk.2
    change lindahlExampleU ![x' k, q'] ≤ lindahlExampleU ![1 / 2, 1 / 2]
    simp only [lindahlExampleU, Matrix.cons_val_zero, Matrix.cons_val_one, id] at hf' ⊢
    simp only [Finset.univ_unique, Finset.sum_singleton] at hc'
    have : k = default := Subsingleton.elim _ _
    subst this
    rw [Fin.default_eq_zero] at hc'
    norm_num
    linarith
  refine ⟨hpo, lindahl_second_welfare (fun _ => rationalOn_utilityPref _ _) (fun _ => ?_)
    (fun _ => lns_of_strictMono_coord 0 fun x _ c hc => by simp [lindahlExampleU]; linarith)
    (concaveOn_id (convex_Ici 0)) hpo⟩
  intro y _ v hv w hw a b ha hb hab
  refine ⟨fun l => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [mul_nonneg ha (hv.1 l), mul_nonneg hb (hw.1 l)]
  · have h1 : lindahlExampleU y ≤ lindahlExampleU v := hv.2
    have h2 : lindahlExampleU y ≤ lindahlExampleU w := hw.2
    change lindahlExampleU y ≤ lindahlExampleU (a • v + b • w)
    simp only [lindahlExampleU, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 ⊢
    have : y 0 + y 1 = a * (y 0 + y 1) + b * (y 0 + y 1) := by rw [← add_mul, hab, one_mul]
    nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]

end MWG.WelfareTheorems
