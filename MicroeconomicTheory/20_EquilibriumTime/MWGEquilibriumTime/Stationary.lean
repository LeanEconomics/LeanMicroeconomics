/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGEquilibriumTime.SmoothPrices
import MWGEquilibriumTime.OneConsumer

/-!
# Stationary paths, interest rates and golden rules (MWG Section 20.E, pp. 754-756)

MWG, Chapter 20, Section 20.E: Definitions 20.E.1-20.E.2, Propositions 20.E.1-20.E.2, and
Exercises 20.E.1, 20.E.2 and 20.E.9 (pp. 784-785).

* **Definition 20.E.1** (`IsStationary`); proportional price sequences `p_t = α^t p₀`
  (`propPrices`) and the implicit rate of interest `r = (1 - α)/α` (`exercise_20_E_1`).
* **Proposition 20.E.1** in the smooth case MWG treat: an efficient stationary path is supported
  by proportional prices (`proposition_20_E_1`), and every supporting sequence is proportional
  (`supporting_prices_proportional`). The nonsmooth case is OPEN (MWG: "too delicate").
* **Proposition 20.E.2**: efficiency for `r > 0` (`proposition_20_E_2_pos`) and inefficiency
  for `r < 0` in the smooth case (`proposition_20_E_2_neg`), via the fact that a direction below
  the tangent hyperplane of a smooth convex body points into it (`exists_mem_of_smooth_neg`).
* **Definition 20.E.2** (`IsModifiedGoldenRule`, `IsGoldenRule`); a stationary interior
  equilibrium is a modified golden rule (`stationary_equilibrium_modified_golden_rule`).
* **Exercise 20.E.2** (proportional paths under constant returns): (a)
  `exercise_20_E_2a`, (b) `exercise_20_E_2b_pos`, `exercise_20_E_2b_neg`.
* **Exercise 20.E.9**: the golden rule is not a stationary equilibrium (`exercise_20_E_9`).
-/

open Filter Topology

namespace MWG.EquilibriumTime

variable {ι : Type*} [Fintype ι]

/-- **Definition 20.E.1** (MWG, p. 754): a path is stationary (a steady state) if `y_t = ȳ` for
all `t`, for some `ȳ ∈ Y`. -/
def IsStationary (Y : Set (ProdPlan ι)) (y : ℕ → ProdPlan ι) : Prop :=
  ∃ yb ∈ Y, ∀ t, y t = yb

/-- The proportional price sequence `(p₀, α p₀, α² p₀, ...)` (MWG, p. 754). -/
def propPrices (α : ℝ) (p₀ : ι → ℝ) : ℕ → ι → ℝ := fun t => α ^ t • p₀

omit [Fintype ι] in
/-- **Exercise 20.E.1** (MWG, p. 784): with `r = (1 - α)/α`, the proportional prices satisfy
`p_t = (1 + r) p_{t+1}`, so `r` is the own rate of interest of every commodity (Exercise 20.C.1)
at every date. -/
theorem exercise_20_E_1 {α : ℝ} (hα : 0 < α) (p₀ : ι → ℝ) (t : ℕ) :
    propPrices α p₀ t = (1 + (1 - α) / α) • propPrices α p₀ (t + 1) ∧
      ∀ l, p₀ l ≠ 0 → ownRate (propPrices α p₀) t l = (1 - α) / α := by
  constructor
  · funext l
    simp only [propPrices, Pi.smul_apply, smul_eq_mul, pow_succ]
    field_simp
    ring
  · intro l hl
    simp only [ownRate, propPrices, Pi.smul_apply, smul_eq_mul, pow_succ]
    have : α ^ t ≠ 0 := pow_ne_zero t hα.ne'
    field_simp

/-- A continuous linear functional on `ℝ^L × ℝ^L` is the value function of its coefficient
vectors. -/
theorem clm_prod_eq_planValue [DecidableEq ι] (f : ProdPlan ι →L[ℝ] ℝ) (z : ProdPlan ι) :
    f z = planValue (fun i => f (Pi.single i 1, 0)) (fun i => f (0, Pi.single i 1)) z := by
  have h1 : z.1 = ∑ i, z.1 i • (Pi.single i 1 : ι → ℝ) := by
    funext j; simp [Finset.sum_apply, Pi.single_apply]
  have h2 : z.2 = ∑ i, z.2 i • (Pi.single i 1 : ι → ℝ) := by
    funext j; simp [Finset.sum_apply, Pi.single_apply]
  have hz : z = ∑ i, z.1 i • ((Pi.single i 1 : ι → ℝ), (0 : ι → ℝ))
      + ∑ i, z.2 i • ((0 : ι → ℝ), (Pi.single i 1 : ι → ℝ)) := by
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add, Prod.fst_sum, Prod.smul_fst, smul_zero, Finset.sum_const_zero,
        add_zero]
      exact h1
    · simp only [Prod.snd_add, Prod.snd_sum, Prod.smul_snd, smul_zero, Finset.sum_const_zero,
        zero_add]
      exact h2
  conv_lhs => rw [hz]
  simp only [map_add, map_sum, map_smul, smul_eq_mul, planValue, dotProduct]
  congr 1 <;> exact Finset.sum_congr rfl fun i _ => by ring

/-- **A direction below the tangent hyperplane points into a smooth convex body** (the test used
in the proof of Proposition 20.E.2, MWG, p. 755): if `Y` is convex with nonempty interior and
smooth at `ȳ ∈ Y` with normal `q`, and `q · d < 0`, then `ȳ + ε d ∈ Y` for some `ε > 0`. -/
theorem exists_mem_of_smooth_neg {Y : Set (ProdPlan ι)} (hY : Convex ℝ Y)
    (hint : (interior Y).Nonempty) {yb q d : ProdPlan ι} (hyb : yb ∈ Y) (hs : SmoothAt Y yb q)
    (hd : planValue q.1 q.2 d < 0) : ∃ ε : ℝ, 0 < ε ∧ yb + ε • d ∈ Y := by
  classical
  by_contra hno
  push Not at hno
  set ray : Set (ProdPlan ι) := {z | ∃ ε : ℝ, 0 < ε ∧ z = yb + ε • d} with hray
  have hrayc : Convex ℝ ray := by
    rintro _ ⟨ε₁, h₁, rfl⟩ _ ⟨ε₂, h₂, rfl⟩ a b ha hb hab
    refine ⟨a * ε₁ + b * ε₂, ?_, ?_⟩
    · rcases eq_or_lt_of_le ha with rfl | ha'
      · have hb1 : b = 1 := by linarith
        subst hb1; simpa using h₂
      · nlinarith [mul_pos ha' h₁, mul_nonneg hb h₂.le]
    · rw [smul_add, smul_add, smul_smul, smul_smul, add_add_add_comm, ← add_smul, hab,
        one_smul, ← add_smul]
  have hdisj : Disjoint (interior Y) ray := by
    rw [Set.disjoint_left]
    rintro z hz ⟨ε, hε, rfl⟩
    exact hno ε hε (interior_subset hz)
  obtain ⟨f, u, hfs, hft⟩ := geometric_hahn_banach_open hY.interior isOpen_interior
    hrayc hdisj
  -- `f ≤ u` on `Y`, and `f ȳ ≥ u`
  have hclos : Y ⊆ {z | f z ≤ u} := by
    intro z hz
    have hz' : z ∈ closure (interior Y) := by
      rw [hY.closure_interior_eq_closure_of_nonempty_interior hint]; exact subset_closure hz
    exact closure_lt_subset_le f.continuous continuous_const
      (closure_mono (fun w hw => hfs w hw) hz')
  have hfyb : u ≤ f yb := by
    by_contra hlt
    push Not at hlt
    -- choose `ε` small so that `f (ȳ + ε d) < u`
    have hcont : Tendsto (fun ε : ℝ => f (yb + ε • d)) (𝓝 0) (𝓝 (f yb)) := by
      have : Continuous fun ε : ℝ => f (yb + ε • d) := by fun_prop
      simpa using this.tendsto 0
    have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), f (yb + ε • d) < u :=
      (hcont.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds hlt)
    obtain ⟨ε, hεlt, hε⟩ := (hev.and self_mem_nhdsWithin).exists
    exact absurd (hft _ ⟨ε, hε, rfl⟩) (not_le.2 hεlt)
  -- `f` supports `Y` at `ȳ`, so it is a positive multiple of `q`
  set qf : ProdPlan ι := (fun i => f (Pi.single i 1, 0), fun i => f (0, Pi.single i 1))
  have hfeq : ∀ z, f z = planValue qf.1 qf.2 z := clm_prod_eq_planValue f
  have hqf0 : qf ≠ 0 := by
    intro h0
    obtain ⟨z, hz⟩ := hint
    have h1 := hfs z hz
    have h2 := hft (yb + (1 : ℝ) • d) ⟨1, one_pos, rfl⟩
    rw [hfeq z, h0] at h1
    rw [hfeq, h0] at h2
    simp [planValue] at h1 h2
    linarith
  obtain ⟨c, hc, hceq⟩ := hs.2 qf ⟨hqf0, fun z hz => by
    rw [← hfeq, ← hfeq]; exact (hclos hz).trans hfyb⟩
  have h1 := hft (yb + (1 : ℝ) • d) ⟨1, one_pos, rfl⟩
  have h2 : f yb ≤ u := hclos hyb
  rw [hfeq] at h1 h2
  rw [hceq] at h1 h2
  simp only [Prod.smul_fst, Prod.smul_snd] at h1 h2
  rw [planValue_smul] at h1 h2
  simp only [planValue, Prod.fst_add, Prod.snd_add, one_smul, dotProduct_add] at h1 h2 hd
  nlinarith [mul_neg_of_pos_of_neg hc hd]

/-- **Every supporting price sequence of a smooth stationary path is proportional** (MWG, p. 754,
proof of Proposition 20.E.1): if `Y` is smooth at `ȳ` with normal `q`, `q_b ≠ 0`, and `p` is a
Malinvaud price sequence for the stationary path with `(p_t, p_{t+1}) ≠ 0` for all `t`, then
`p_t = α^t p₀` for some `α > 0`. -/
theorem supporting_prices_proportional {Y : Set (ProdPlan ι)} {yb q : ProdPlan ι}
    (hs : SmoothAt Y yb q) (hqb : q.1 ≠ 0) {p : ℕ → ι → ℝ}
    (hmy : MyopicProfitMax Y p (fun _ => yb)) (hp : ∀ t, ((p t, p (t + 1)) : ProdPlan ι) ≠ 0) :
    ∃ α : ℝ, 0 < α ∧ ∀ t, p t = α ^ t • p 0 := by
  have hlam : ∀ t, ∃ c : ℝ, 0 < c ∧ ((p t, p (t + 1)) : ProdPlan ι) = c • q := fun t =>
    hs.2 _ ⟨hp t, fun z hz => hmy.2 t z hz⟩
  choose c hc hceq using hlam
  have hb : ∀ t, p t = c t • q.1 := fun t => by
    have := congrArg Prod.fst (hceq t); simpa using this
  have ha : ∀ t, p (t + 1) = c t • q.2 := fun t => by
    have := congrArg Prod.snd (hceq t); simpa using this
  -- `q_a = (c_{t+1} / c_t) q_b` for every `t`, so the ratio is constant
  have hratio : ∀ t, c (t + 1) = (c 1 / c 0) * c t := by
    intro t
    obtain ⟨i, hi⟩ : ∃ i, q.1 i ≠ 0 := by
      by_contra h; push Not at h; exact hqb (funext h)
    have e1 : c t * q.2 i = c (t + 1) * q.1 i := by
      have := congrFun ((ha t).symm.trans (hb (t + 1))) i; simpa using this
    have e0 : c 0 * q.2 i = c 1 * q.1 i := by
      have := congrFun ((ha 0).symm.trans (hb 1)) i; simpa using this
    have hc0 := (hc 0).ne'
    have hct := (hc t).ne'
    field_simp
    have : c (t + 1) * q.1 i * c 0 = c 1 * q.1 i * c t := by
      rw [← e1, ← e0]; ring
    exact mul_right_cancel₀ hi (by linarith [this])
  refine ⟨c 1 / c 0, div_pos (hc 1) (hc 0), fun t => ?_⟩
  have hct : ∀ t, c t = (c 1 / c 0) ^ t * c 0 := by
    intro t
    induction t with
    | zero => simp
    | succ t ih => rw [hratio t, ih, pow_succ]; ring
  rw [hb t, hb 0, hct t, smul_smul]

/-- **Proposition 20.E.1** (MWG, p. 754), the smooth case: an efficient stationary path of a
convex technology that is smooth at `ȳ` with normal `q`, `q_b ≫ 0`, `q_a ≫ 0`, is myopically
profit maximizing for a proportional price sequence `(p₀, α p₀, α² p₀, ...)` with `α > 0` and
`p₀ ≫ 0`. -/
theorem proposition_20_E_1 {L : ℕ} (hL : 0 < L) {Y : Set (ProdPlan (Fin L))} (hY : Convex ℝ Y)
    {yb q : ProdPlan (Fin L)} (hs : SmoothAt Y yb q) (hqb : StrictPos q.1) (hqa : StrictPos q.2)
    (heff : ProdEfficient Y (fun _ => yb)) :
    ∃ α : ℝ, 0 < α ∧ StrictPos q.1 ∧ MyopicProfitMax Y (propPrices α q.1) (fun _ => yb) := by
  have h2 : TEfficient Y (fun _ => yb) 2 :=
    ⟨heff.1, fun ⟨y', hy', hle, hne, _, _⟩ => heff.2 ⟨y', hy', hle, hne⟩⟩
  have hne : ∀ v : Fin L → ℝ, StrictPos v → v ≠ 0 := fun v hv h => by
    have := hv ⟨0, hL⟩; rw [h] at this; exact lt_irrefl _ this
  obtain ⟨β, hβ, hβeq⟩ := proportional_normals_of_twoEfficient (q := fun _ => q) hL hY h2 0 hs hs
    (hne _ hqa) (hne _ hqb)
  refine ⟨β, hβ, hqb, heff.1, fun t z hz => ?_⟩
  have hpair : ((propPrices β q.1 t, propPrices β q.1 (t + 1)) : ProdPlan (Fin L))
      = β ^ t • q := by
    refine Prod.ext ?_ ?_
    · simp [propPrices]
    · simp only [propPrices, Prod.smul_snd, pow_succ, mul_smul]
      exact congrArg _ hβeq.symm
  simp only [periodProfit]
  have hval : ∀ w, planValue (propPrices β q.1 t) (propPrices β q.1 (t + 1)) w
      = β ^ t * planValue q.1 q.2 w := by
    intro w
    have e1 := congrArg Prod.fst hpair
    have e2 := congrArg Prod.snd hpair
    simp only [Prod.smul_fst, Prod.smul_snd] at e1 e2
    rw [e1, e2, planValue_smul]
  rw [hval, hval]
  exact mul_le_mul_of_nonneg_left (hs.1.2 z hz) (pow_nonneg hβ.le t)

/-- **Proposition 20.E.2**, first part (MWG, p. 755): a stationary path supported by
proportional prices with `p₀ ≫ 0` and rate of interest `r > 0` (that is, `0 < α < 1`) satisfies
the transversality condition and is therefore efficient (Proposition 20.C.1). -/
theorem proposition_20_E_2_pos {Y : Set (ProdPlan ι)} (htr : ∀ z ∈ Y, (z.1, 0) ∈ Y)
    {yb : ProdPlan ι} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {p₀ : ι → ℝ} (hp₀ : StrictPos p₀)
    (hmy : MyopicProfitMax Y (propPrices α p₀) (fun _ => yb)) : ProdEfficient Y (fun _ => yb) := by
  refine proposition_20_C_1 htr (fun t i => ?_) hmy ?_
  · simp only [propPrices, Pi.smul_apply, smul_eq_mul]
    exact mul_pos (pow_pos hα0 t) (hp₀ i)
  · unfold Transversality
    simp only [propPrices, smul_dotProduct, smul_eq_mul]
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one hα0.le hα1).comp (tendsto_add_atTop_nat 1)
    simpa using this.mul_const (p₀ ⬝ᵥ yb.2)

/-- **Proposition 20.E.2**, second part (MWG, p. 755): in the smooth case (convex `Y` with
nonempty interior, smooth at `ȳ`), a stationary path supported by proportional prices with
`p₀ ≥ 0`, `p₀ ≠ 0`, and rate of interest `r < 0` (`α > 1`) is inefficient: for small `ε > 0` the
stationary path `ȳ + ε (e, -e)` dominates it (it overaccumulates). -/
theorem proposition_20_E_2_neg [Nonempty ι] {Y : Set (ProdPlan ι)} (hY : Convex ℝ Y)
    (hint : (interior Y).Nonempty) {yb q : ProdPlan ι} (hyb : yb ∈ Y) (hs : SmoothAt Y yb q)
    {α : ℝ} (hα : 1 < α) {p₀ : ι → ℝ} (hp₀ : 0 ≤ p₀) (hp₀ne : p₀ ≠ 0)
    (hmy : MyopicProfitMax Y (propPrices α p₀) (fun _ => yb)) :
    ¬ ProdEfficient Y (fun _ => yb) := by
  set e : ι → ℝ := fun _ => 1
  set d : ProdPlan ι := (e, -e)
  -- the supporting functional at date 0 is a positive multiple of `q`
  have hsup : SupportsAt Y yb (p₀, α • p₀) := by
    refine ⟨fun h => hp₀ne (congrArg Prod.fst h), fun z hz => ?_⟩
    have := hmy.2 0 z hz
    simpa [periodProfit, propPrices] using this
  obtain ⟨c, hc, hceq⟩ := hs.2 _ hsup
  have hpe : 0 < p₀ ⬝ᵥ e := by
    obtain ⟨i, hi⟩ : ∃ i, p₀ i ≠ 0 := by
      by_contra h; push Not at h; exact hp₀ne (funext h)
    refine Finset.sum_pos' (fun j _ => by simpa [e] using hp₀ j) ⟨i, Finset.mem_univ _, ?_⟩
    simpa [e] using lt_of_le_of_ne (hp₀ i) (Ne.symm hi)
  have hqd : planValue q.1 q.2 d < 0 := by
    have hv : planValue p₀ (α • p₀) d = c * planValue q.1 q.2 d := by
      have e1 := congrArg Prod.fst hceq
      have e2 := congrArg Prod.snd hceq
      simp only [Prod.smul_fst, Prod.smul_snd] at e1 e2
      rw [e2, e1, planValue_smul]
    have : planValue p₀ (α • p₀) d = (1 - α) * (p₀ ⬝ᵥ e) := by
      simp only [planValue, d, smul_dotProduct, dotProduct_neg, smul_eq_mul]; ring
    have hneg : planValue p₀ (α • p₀) d < 0 := by
      rw [this]; exact mul_neg_of_neg_of_pos (by linarith) hpe
    rw [hv] at hneg
    by_contra hge
    push Not at hge
    exact absurd hneg (not_lt.2 (mul_nonneg hc.le hge))
  obtain ⟨ε, hε, hmem⟩ := exists_mem_of_smooth_neg hY hint hyb hs hqd
  rintro ⟨-, hno⟩
  refine hno ⟨fun _ => yb + ε • d, fun _ => hmem, fun t => ?_, ?_⟩
  · cases t with
    | zero =>
      intro i
      simp [netOutput, d, e, hε.le]
    | succ t =>
      intro i
      simp only [netOutput, d, e, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, mul_one, mul_neg]
      linarith
  · intro h
    have := congrFun (congrFun h 0) (Classical.arbitrary ι)
    exact hε.ne' (by simpa [netOutput, d, e] using this)

/-- **Definition 20.E.2** (MWG, p. 755): a stationary path is a **modified golden rule path** if it
is myopically supported by proportional prices `p_t = δ^t p₀`. -/
def IsModifiedGoldenRule (Y : Set (ProdPlan ι)) (δ : ℝ) (yb : ProdPlan ι) : Prop :=
  yb ∈ Y ∧ ∃ p₀ : ι → ℝ, p₀ ≠ 0 ∧ MyopicProfitMax Y (propPrices δ p₀) (fun _ => yb)

/-- **Definition 20.E.2** (MWG, p. 755): a stationary path is a **golden rule path** if it is
myopically supported by constant prices `p_t = p₀`. -/
def IsGoldenRule (Y : Set (ProdPlan ι)) (yb : ProdPlan ι) : Prop :=
  IsModifiedGoldenRule Y 1 yb

/-- **A stationary equilibrium is a modified golden rule** (MWG, p. 755): at a Walrasian
equilibrium whose path is stationary with constant strictly positive consumption `c̄ ≫ 0`, with
`u` concave and strictly increasing on `ℝ^L_+`, differentiable at `c̄` with strictly positive
marginal utilities, and `0 < δ`, the prices are `p_t = δ^t p₀` (by Exercise 20.D.3 and (20.D.6)),
so the path is a modified golden rule path for `δ`. In particular, the candidates for stationary
equilibria depend only on the technology and `δ`, not on `u`. -/
theorem stationary_equilibrium_modified_golden_rule {L : ℕ} [NeZero L]
    {Y : Set (ProdPlan (Fin L))} {δ : ℝ} (hδ : 0 < δ) {u : (Fin L → ℝ) → ℝ}
    (hconc : ConcaveOn ℝ (Set.Ici 0) u) (hmono : StrictMonoOn u (Set.Ici 0))
    {ω p : ℕ → Fin L → ℝ} {yb : ProdPlan (Fin L)}
    (he : WalrasEq (Set.Ici 0) Y δ u ω p (fun _ => yb)) {cb : Fin L → ℝ}
    (hcb : ∀ t, consumption ω (fun _ => yb) t = cb) (hcpos : StrictPos cb)
    {Du : (Fin L → ℝ) →L[ℝ] ℝ} (hDu : HasFDerivAt u Du cb)
    (hDpos : ∀ i, 0 < Du (Pi.single i 1)) :
    ∃ p₀ : Fin L → ℝ, StrictPos p₀ ∧ p = propPrices δ p₀ ∧ IsModifiedGoldenRule Y δ yb := by
  obtain ⟨hbud, hs, hmax⟩ := he.utilityMax
  set c := consumption ω (fun _ => yb) with hc
  have hmyo : MyopicUtilityMax (Set.Ici 0) δ u p
      (∑' t, (periodProfit p (fun _ => yb) t + p t ⬝ᵥ ω t)) c := by
    refine ⟨hbud, hs, fun t c' hc' hdiff => hmax c' hc' ?_⟩
    exact summable_of_finite_change {t, t + 1} (fun s hst => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hst
      exact hdiff s hst.1 hst.2) hs
  have hcpos' : ∀ t, StrictPos (c t) := fun t => by rw [hcb t]; exact hcpos
  obtain ⟨-, hfoc⟩ := (exercise_20_D_3 hδ hconc hmono hcpos' hbud.2.1 hs
    (fun t => by rw [hcb t]; exact hDu) (fun t i => hDpos i)).1 hmyo
  -- prices are strictly positive
  have hppos : ∀ t, StrictPos (p t) := by
    intro t i
    obtain ⟨lam, hlam, h1, -⟩ := hfoc t
    have := h1 (Pi.single i 1)
    rw [dotProduct_single, mul_one] at this
    have := hDpos i
    nlinarith
  have hpne : ∀ t, p t ≠ 0 := fun t h => by
    have := hppos t ⟨0, Nat.pos_of_ne_zero (NeZero.ne L)⟩
    rw [h] at this; exact lt_irrefl _ this
  obtain ⟨lam, hlam, h6⟩ := (foc_20_D_5_iff_20_D_6 hδ hpne).1 hfoc
  have hprop : p = propPrices δ (p 0) := by
    funext t i
    have e1 := h6 t (Pi.single i 1)
    have e0 := h6 0 (Pi.single i 1)
    simp only [dotProduct_single, mul_one, pow_zero, one_mul] at e1 e0
    simp only [propPrices, Pi.smul_apply, smul_eq_mul]
    rw [← e0] at e1
    have : lam * p t i = lam * (δ ^ t * p 0 i) := by rw [e1]; ring
    exact mul_left_cancel₀ hlam.ne' this
  refine ⟨p 0, hppos 0, hprop, he.myopic.1 0, p 0, hpne 0, ?_⟩
  rw [← hprop]
  exact he.myopic

/-! ### Proportional paths (Exercise 20.E.2) and the golden rule (Exercise 20.E.9) -/

/-- A technology is a **cone** (constant returns): `y ∈ Y` and `λ ≥ 0` imply `λ y ∈ Y`. -/
def IsConeTech (Y : Set (ProdPlan ι)) : Prop := ∀ y ∈ Y, ∀ c : ℝ, 0 ≤ c → c • y ∈ Y

/-- Under constant returns, a normal at `ȳ` is a normal at every `λ ȳ`, `λ > 0`, and smoothness is
inherited. -/
theorem smoothAt_smul_of_cone {Y : Set (ProdPlan ι)} (hc : IsConeTech Y) {yb q : ProdPlan ι}
    (hyb : yb ∈ Y) (hs : SmoothAt Y yb q) {c : ℝ} (hc0 : 0 < c) : SmoothAt Y (c • yb) q := by
  -- every supporting functional vanishes at `ȳ`
  have hzero : ∀ q', SupportsAt Y yb q' → planValue q'.1 q'.2 yb = 0 := by
    intro q' hq'
    have h0 := hq'.2 _ (hc yb hyb 0 le_rfl)
    have h2 := hq'.2 _ (hc yb hyb 2 (by norm_num))
    simp only [planValue, zero_smul, Prod.smul_fst, Prod.smul_snd, Prod.fst_zero,
      Prod.snd_zero, dotProduct_zero, dotProduct_smul, smul_eq_mul, add_zero] at h0 h2
    simp only [planValue]
    linarith
  have hval : ∀ q' : ProdPlan ι, planValue q'.1 q'.2 (c • yb) = c * planValue q'.1 q'.2 yb := by
    intro q'; simp only [planValue, Prod.smul_fst, Prod.smul_snd, dotProduct_smul, smul_eq_mul]
    ring
  refine ⟨⟨hs.1.1, fun z hz => ?_⟩, fun q' hq' => hs.2 q' ⟨hq'.1, fun z hz => ?_⟩⟩
  · rw [hval, hzero q hs.1, mul_zero, ← hzero q hs.1]; exact hs.1.2 z hz
  · -- `q'` supports at `c ȳ`, hence vanishes there and supports at `ȳ`
    have h0 := hq'.2 _ (hc _ (hc yb hyb c hc0.le) 0 le_rfl)
    simp only [zero_smul] at h0
    simp only [planValue, Prod.fst_zero, Prod.snd_zero, dotProduct_zero, add_zero] at h0
    have h2 := hq'.2 _ (hc _ (hc yb hyb c hc0.le) 2 (by norm_num))
    have hc' := hq'.2 z hz
    rw [hval] at hc'
    simp only [planValue, Prod.smul_fst, Prod.smul_snd, dotProduct_smul, smul_eq_mul] at h0 h2 hc' ⊢
    nlinarith

/-- Malinvaud prices from a **common smooth normal**: if a `2`-efficient path of a convex
technology is smooth at every `y_t` with the same normal `q` (`q_b, q_a ≫ 0`), it is myopically
profit maximizing for a proportional sequence `p_t = β^t q_b`. -/
theorem malinvaud_prop_of_common_normal {L : ℕ} (hL : 0 < L) {Y : Set (ProdPlan (Fin L))}
    (hY : Convex ℝ Y) {y : ℕ → ProdPlan (Fin L)} (h2 : TEfficient Y y 2) {q : ProdPlan (Fin L)}
    (hs : ∀ t, SmoothAt Y (y t) q) (hqb : StrictPos q.1) (hqa : StrictPos q.2) :
    ∃ β : ℝ, 0 < β ∧ MyopicProfitMax Y (propPrices β q.1) y := by
  have hne : ∀ v : Fin L → ℝ, StrictPos v → v ≠ 0 := fun v hv h => by
    have := hv ⟨0, hL⟩; rw [h] at this; exact lt_irrefl _ this
  obtain ⟨β, hβ, hβeq⟩ := proportional_normals_of_twoEfficient (q := fun _ => q) hL hY h2 0
    (hs 0) (hs 1) (hne _ hqa) (hne _ hqb)
  refine ⟨β, hβ, h2.1, fun t z hz => ?_⟩
  have hval : ∀ w, planValue (propPrices β q.1 t) (propPrices β q.1 (t + 1)) w
      = β ^ t * planValue q.1 q.2 w := by
    intro w
    simp only [propPrices, pow_succ, mul_smul]
    rw [← hβeq, planValue_smul]
  simp only [periodProfit]
  rw [hval, hval]
  exact mul_le_mul_of_nonneg_left ((hs t).1.2 z hz) (pow_nonneg hβ.le t)

/-- **Exercise 20.E.2(a)** (MWG, p. 784): under constant returns, Proposition 20.E.1 holds for
proportional paths `y_t = (1 + n)^t ȳ` (`n > -1`): an efficient proportional path of a convex cone
technology that is smooth at `ȳ` (normal parts `≫ 0`) is supported by proportional prices. -/
theorem exercise_20_E_2a {L : ℕ} (hL : 0 < L) {Y : Set (ProdPlan (Fin L))} (hY : Convex ℝ Y)
    (hcone : IsConeTech Y) {yb q : ProdPlan (Fin L)} (hyb : yb ∈ Y) (hs : SmoothAt Y yb q)
    (hqb : StrictPos q.1) (hqa : StrictPos q.2) {n : ℝ} (hn : -1 < n)
    (heff : ProdEfficient Y (fun t => (1 + n) ^ t • yb)) :
    ∃ β : ℝ, 0 < β ∧ MyopicProfitMax Y (propPrices β q.1) (fun t => (1 + n) ^ t • yb) :=
  malinvaud_prop_of_common_normal hL hY ⟨heff.1, fun ⟨y', hy', hle, hne, _, _⟩ =>
    heff.2 ⟨y', hy', hle, hne⟩⟩
    (fun t => smoothAt_smul_of_cone hcone hyb hs (pow_pos (by linarith) t)) hqb hqa

/-- **Exercise 20.E.2(b)**, efficiency (MWG, p. 784): a proportional path `y_t = (1+n)^t ȳ`
supported by `p_t = α^t p₀` (`p₀ ≫ 0`) with `α (1 + n) < 1` (rate of interest `r > n`) satisfies
transversality and is efficient. -/
theorem exercise_20_E_2b_pos {Y : Set (ProdPlan ι)} (htr : ∀ z ∈ Y, (z.1, 0) ∈ Y)
    {yb : ProdPlan ι} {α n : ℝ} (hα0 : 0 < α) (hn : -1 < n) (hαn : α * (1 + n) < 1)
    {p₀ : ι → ℝ} (hp₀ : StrictPos p₀)
    (hmy : MyopicProfitMax Y (propPrices α p₀) (fun t => (1 + n) ^ t • yb)) :
    ProdEfficient Y (fun t => (1 + n) ^ t • yb) := by
  refine proposition_20_C_1 htr (fun t i => ?_) hmy ?_
  · simp only [propPrices, Pi.smul_apply, smul_eq_mul]
    exact mul_pos (pow_pos hα0 t) (hp₀ i)
  · unfold Transversality
    have hn0 : 0 ≤ α * (1 + n) := mul_nonneg hα0.le (by linarith)
    have hlim := (tendsto_pow_atTop_nhds_zero_of_lt_one hn0 hαn).mul_const (α * (p₀ ⬝ᵥ yb.2))
    rw [zero_mul] at hlim
    refine hlim.congr fun t => ?_
    simp only [propPrices, Prod.smul_snd, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      mul_pow, pow_succ]
    ring

/-- **Exercise 20.E.2(b)**, inefficiency (MWG, p. 784): in the smooth constant-returns case, a
proportional path supported by `p_t = α^t p₀` (`p₀ ≥ 0`, `p₀ ≠ 0`) with `α (1 + n) > 1` (rate of
interest `r < n`) is inefficient: `(1+n)^t (ȳ + ε(e, -(1+n) e))` dominates it. -/
theorem exercise_20_E_2b_neg [Nonempty ι] {Y : Set (ProdPlan ι)} (hY : Convex ℝ Y)
    (hcone : IsConeTech Y) (hint : (interior Y).Nonempty) {yb q : ProdPlan ι} (hyb : yb ∈ Y)
    (hs : SmoothAt Y yb q) {α n : ℝ} (hn : -1 < n) (hαn : 1 < α * (1 + n)) {p₀ : ι → ℝ}
    (hp₀ : 0 ≤ p₀) (hp₀ne : p₀ ≠ 0)
    (hmy : MyopicProfitMax Y (propPrices α p₀) (fun t => (1 + n) ^ t • yb)) :
    ¬ ProdEfficient Y (fun t => (1 + n) ^ t • yb) := by
  set e : ι → ℝ := fun _ => 1
  set d : ProdPlan ι := (e, -((1 + n) • e))
  have hsup : SupportsAt Y yb (p₀, α • p₀) := by
    refine ⟨fun h => hp₀ne (congrArg Prod.fst h), fun z hz => ?_⟩
    have := hmy.2 0 z hz
    simpa [periodProfit, propPrices] using this
  obtain ⟨c, hc, hceq⟩ := hs.2 _ hsup
  have hpe : 0 < p₀ ⬝ᵥ e := by
    obtain ⟨i, hi⟩ : ∃ i, p₀ i ≠ 0 := by
      by_contra h; push Not at h; exact hp₀ne (funext h)
    refine Finset.sum_pos' (fun j _ => by simpa [e] using hp₀ j) ⟨i, Finset.mem_univ _, ?_⟩
    simpa [e] using lt_of_le_of_ne (hp₀ i) (Ne.symm hi)
  have hqd : planValue q.1 q.2 d < 0 := by
    have hv : planValue p₀ (α • p₀) d = c * planValue q.1 q.2 d := by
      have e1 := congrArg Prod.fst hceq
      have e2 := congrArg Prod.snd hceq
      simp only [Prod.smul_fst, Prod.smul_snd] at e1 e2
      rw [e2, e1, planValue_smul]
    have : planValue p₀ (α • p₀) d = (1 - α * (1 + n)) * (p₀ ⬝ᵥ e) := by
      simp only [planValue, d, smul_dotProduct, dotProduct_neg, dotProduct_smul, smul_eq_mul]
      ring
    have hneg : planValue p₀ (α • p₀) d < 0 := by
      rw [this]; exact mul_neg_of_neg_of_pos (by linarith) hpe
    rw [hv] at hneg
    by_contra hge
    push Not at hge
    exact absurd hneg (not_lt.2 (mul_nonneg hc.le hge))
  obtain ⟨ε, hε, hmem⟩ := exists_mem_of_smooth_neg hY hint hyb hs hqd
  rintro ⟨-, hno⟩
  have h1n : 0 < 1 + n := by linarith
  refine hno ⟨fun t => (1 + n) ^ t • (yb + ε • d),
    fun t => hcone _ hmem _ (pow_nonneg h1n.le t), fun t => ?_, ?_⟩
  · cases t with
    | zero =>
      intro i
      simp [netOutput, d, e, hε.le]
    | succ t =>
      intro i
      simp only [netOutput, d, e, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, mul_one, mul_neg, pow_succ]
      nlinarith [pow_pos h1n t]
  · intro h
    have := congrFun (congrFun h 0) (Classical.arbitrary ι)
    exact hε.ne' (by simpa [netOutput, d, e] using this)

/-- **Exercise 20.E.9** (MWG, p. 785): in the one-consumer model with `δ < 1`, a stationary
equilibrium path (interior, as in `stationary_equilibrium_modified_golden_rule`) of a technology
that is smooth at `ȳ` with `q_b ≠ 0` is not a golden rule path: the golden rule needs constant
supporting prices, the equilibrium needs prices declining at the rate `δ`, and smoothness allows
only one proportionality factor. -/
theorem exercise_20_E_9 {L : ℕ} [NeZero L] {Y : Set (ProdPlan (Fin L))} {δ : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ < 1) {u : (Fin L → ℝ) → ℝ} (hconc : ConcaveOn ℝ (Set.Ici 0) u)
    (hmono : StrictMonoOn u (Set.Ici 0)) {ω p : ℕ → Fin L → ℝ} {yb q : ProdPlan (Fin L)}
    (he : WalrasEq (Set.Ici 0) Y δ u ω p (fun _ => yb)) {cb : Fin L → ℝ}
    (hcb : ∀ t, consumption ω (fun _ => yb) t = cb) (hcpos : StrictPos cb)
    {Du : (Fin L → ℝ) →L[ℝ] ℝ} (hDu : HasFDerivAt u Du cb)
    (hDpos : ∀ i, 0 < Du (Pi.single i 1)) (hs : SmoothAt Y yb q) :
    ¬ IsGoldenRule Y yb := by
  rintro ⟨-, p', hp'ne, hmy'⟩
  obtain ⟨p₀, hp₀, -, hmgr⟩ := stationary_equilibrium_modified_golden_rule hδ0 hconc hmono he hcb
    hcpos hDu hDpos
  obtain ⟨-, p₀', hp₀'ne, hmy⟩ := hmgr
  -- both `(p', p')` and `(p₀', δ p₀')` are positive multiples of `q`
  obtain ⟨c, hc, hceq⟩ := hs.2 (p', (1 : ℝ) • p') ⟨fun h => hp'ne (congrArg Prod.fst h),
    fun z hz => by simpa [periodProfit, propPrices] using hmy'.2 0 z hz⟩
  obtain ⟨c', hc', hc'eq⟩ := hs.2 (p₀', δ • p₀') ⟨fun h => hp₀'ne (congrArg Prod.fst h),
    fun z hz => by simpa [periodProfit, propPrices] using hmy.2 0 z hz⟩
  have h1 : p' = c • q.1 := by have := congrArg Prod.fst hceq; simpa using this
  have h2 : p' = c • q.2 := by have := congrArg Prod.snd hceq; simpa using this
  have h3 : p₀' = c' • q.1 := by have := congrArg Prod.fst hc'eq; simpa using this
  have h4 : δ • p₀' = c' • q.2 := by have := congrArg Prod.snd hc'eq; simpa using this
  have hq : q.1 = q.2 := by
    have := h1.symm.trans h2
    have := congrArg (fun v => c⁻¹ • v) this
    simpa [smul_smul, inv_mul_cancel₀ hc.ne'] using this
  have : δ • p₀' = p₀' := by rw [h4, ← hq, ← h3]
  have : (δ - 1) • p₀' = 0 := by rw [sub_smul, this, one_smul, sub_self]
  rcases smul_eq_zero.1 this with h | h
  · linarith
  · exact hp₀'ne h

end MWG.EquilibriumTime
