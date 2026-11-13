/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGAggregateDemand.HildenbrandStrict
import MWGAggregateDemand.Representative

/-!
# Exercise 4.D.11: a three-good Hildenbrand economy with no positive representative

MWG, Exercise 4.D.11 (p. 126). For `L > 2` the Hildenbrand case of Proposition 4.C.4 need not
admit a positive representative consumer. The book's hint is that the aggregate Slutsky matrix
may fail to be symmetric; here the failure is exhibited in finite form, as a cycle of revealed
preferences of length three, which no rational preference can rationalize.

Every consumer has the L-shaped utility `u(y) = min(φ₀(y₀), y₁, φ₂(y₂))` (`l3U`) whose expansion
path is the polygonal curve `γ(τ) = (γ₀(τ), τ, γ₂(τ))` through `0`, `(1, 1, 1)`, `(2, 2, 21/20)`
with directions `a = (1, 1, 1)`, `b = (1, 1, 1/20)`, `c = (4, 1, 1/40)` (not coplanar). Wealth is
uniform on `[0, 2m]`; aggregate (mean) demand is `X(p, m) = (1/2m) ∫₀^{2m} x̃(p, w) dw`
(`hildMeanDemand`). With `A = p·a`, `B = p·b`, `C = p·c` and `W = 2m ≥ A + B`,
`X(p, m) = [a (W - A/2) + b (W - A - B/2) + c (W - A - B)²/(2C)]/W` (`l3_agg`).

* `exercise_4_D_11`: at `(p₁, m₁) = ((1, 1/3, 4/3), 63/20)`,
  `(p₂, m₂) = ((1, 12/5, 3/10), 1017/200)`,
  `(p₃, m₃) = ((1, 3, 1), 647/100)`, each `X(p_{k+1}, m_{k+1})` is affordable at `(p_k, m_k)` and
  differs from `X(p_k, m_k)` (indices mod 3), so the aggregate demand violates the strong axiom
  and has no positive representative consumer.
-/

namespace MWG.AggregateDemand

open MWG.ConsumerChoice MWG.ClassicalDemand MeasureTheory Kreps.PreferenceProperties

/-- The first coordinate of the expansion path: slopes `1, 1, 4` (kink at `τ = 2`). -/
noncomputable def l3G0 (τ : ℝ) : ℝ := max τ (4 * τ - 6)

/-- The third coordinate of the expansion path: slopes `1, 1/20, 1/40`. -/
noncomputable def l3G2 (τ : ℝ) : ℝ := min (min τ (τ / 20 + 19 / 20)) (τ / 40 + 1)

/-- The inverse of `l3G0`. -/
noncomputable def l3P0 (s : ℝ) : ℝ := min s ((s + 6) / 4)

/-- The inverse of `l3G2`. -/
noncomputable def l3P2 (s : ℝ) : ℝ := max (max s (20 * s - 19)) (40 * s - 40)

/-- The L-shaped utility `min(φ₀(y₀), y₁, φ₂(y₂))` of Exercise 4.D.11's economy. -/
noncomputable def l3U (y : Fin 3 → ℝ) : ℝ := min (min (l3P0 (y 0)) (y 1)) (l3P2 (y 2))

theorem strictMono_l3P0 : StrictMono l3P0 := by
  have := strictMono_min_fun strictMono_id (strictMono_affine (a := 1 / 4) (b := 3 / 2)
    (by norm_num))
  convert this using 2 with s
  simp only [l3P0, id]
  ring_nf

theorem strictMono_l3P2 : StrictMono l3P2 := by
  have := strictMono_max_fun (strictMono_max_fun strictMono_id
    (strictMono_affine (a := 20) (b := -19) (by norm_num)))
    (strictMono_affine (a := 40) (b := -40) (by norm_num))
  convert this using 2 with s
  simp only [l3P2, id]
  ring_nf

theorem l3P0_l3G0 (τ : ℝ) : l3P0 (l3G0 τ) = τ := by
  simp only [l3P0, l3G0, max_def, min_def]
  split_ifs <;> linarith

theorem l3P2_l3G2 (τ : ℝ) : l3P2 (l3G2 τ) = τ := by
  simp only [l3P2, l3G2, max_def, min_def]
  split_ifs <;> linarith

theorem continuous_l3U : Continuous l3U := by
  unfold l3U l3P0 l3P2
  fun_prop

/-- The bundle `γ(τ)` on the expansion path is the unique demand at its own cost. -/
theorem l3U_demand {p : Fin 3 → ℝ} (hp : StrictlyPositive p) {τ : ℝ} (hτ : 0 ≤ τ) :
    walrasianDemand l3U p (p ⬝ᵥ ![l3G0 τ, τ, l3G2 τ]) = {![l3G0 τ, τ, l3G2 τ]} := by
  set y : Fin 3 → ℝ := ![l3G0 τ, τ, l3G2 τ] with hy
  have hy0 : l3P0 (y 0) = τ := l3P0_l3G0 τ
  have hy2 : l3P2 (y 2) = τ := l3P2_l3G2 τ
  have huy : l3U y = τ := by
    simp only [l3U, hy0, hy2]
    simp [y]
  have hynn : y ∈ nonnegOrthant 3 := by
    intro l
    fin_cases l
    · exact hτ.trans (le_max_left _ _)
    · simpa [y] using hτ
    · simp only [y, l3G2, Fin.reduceFinMk, Matrix.cons_val, le_min_iff]
      refine ⟨⟨hτ, by linarith⟩, by linarith⟩
  have hge : ∀ z : Fin 3 → ℝ, τ ≤ l3U z → ∀ l, y l ≤ z l := by
    intro z hz l
    simp only [l3U, le_min_iff] at hz
    fin_cases l
    · exact strictMono_l3P0.le_iff_le.mp (hy0 ▸ hz.1.1)
    · simpa [y] using hz.1.2
    · exact strictMono_l3P2.le_iff_le.mp (hy2 ▸ hz.2)
  have hdot : ∀ z : Fin 3 → ℝ, (∀ l, y l ≤ z l) → p ⬝ᵥ y ≤ p ⬝ᵥ z := fun z h =>
    Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (h l) (hp l).le
  have hmax : ∀ z ∈ budgetSet p (p ⬝ᵥ y), l3U z ≤ τ := by
    intro z hz
    by_contra hlt
    push Not at hlt
    have hgt : ∀ l, y l < z l := by
      intro l
      simp only [l3U, lt_min_iff] at hlt
      fin_cases l
      · exact strictMono_l3P0.lt_iff_lt.mp (hy0 ▸ hlt.1.1)
      · simpa [y] using hlt.1.2
      · exact strictMono_l3P2.lt_iff_lt.mp (hy2 ▸ hlt.2)
    have : p ⬝ᵥ y < p ⬝ᵥ z := Finset.sum_lt_sum_of_nonempty ⟨0, Finset.mem_univ _⟩
      fun l _ => mul_lt_mul_of_pos_left (hgt l) (hp l)
    linarith [hz.2]
  ext z
  constructor
  · intro hz
    have h1 : τ ≤ l3U z := huy ▸ hz.2 y ⟨hynn, le_rfl⟩
    have hle := hge z h1
    have hsum : ∑ l, p l * (z l - y l) = 0 := by
      apply le_antisymm
      · have := hz.1.2
        simp only [dotProduct] at this
        rw [show ∑ l, p l * (z l - y l) = ∑ l, p l * z l - ∑ l, p l * y l by
          rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun l _ => by ring]
        linarith
      · exact Finset.sum_nonneg fun l _ => mul_nonneg (hp l).le (by linarith [hle l])
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg fun l _ =>
      mul_nonneg (hp l).le (by linarith [hle l])).mp hsum
    funext l
    have := h0 l (Finset.mem_univ l)
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (hp l).ne'
    · linarith
  · rintro rfl
    exact ⟨⟨hynn, le_rfl⟩, fun z hz => huy ▸ hmax z hz⟩

/-- `p·a`, `a = (1, 1, 1)`. -/
noncomputable def l3A (p : Fin 3 → ℝ) : ℝ := p 0 + p 1 + p 2

/-- `p·b`, `b = (1, 1, 1/20)`. -/
noncomputable def l3B (p : Fin 3 → ℝ) : ℝ := p 0 + p 1 + p 2 / 20

/-- `p·c`, `c = (4, 1, 1/40)`. -/
noncomputable def l3C (p : Fin 3 → ℝ) : ℝ := 4 * p 0 + p 1 + p 2 / 40

theorem dotProduct_three (p y : Fin 3 → ℝ) : p ⬝ᵥ y = p 0 * y 0 + p 1 * y 1 + p 2 * y 2 := by
  simp [dotProduct, Fin.sum_univ_three]

/-- The individual demand of Exercise 4.D.11's economy, affine in `w` on three pieces. -/
theorem l3_demand {x : DemandFunction 3}
    (hx : ∀ p w, PWDomain p w → x p w ∈ walrasianDemand l3U p w) {p : Fin 3 → ℝ}
    (hp : StrictlyPositive p) {w : ℝ} (hw : 0 < w) :
    (w ≤ l3A p → x p w = ![w / l3A p, w / l3A p, w / l3A p]) ∧
    (l3A p ≤ w → w ≤ l3A p + l3B p → x p w = ![1 + (w - l3A p) / l3B p,
      1 + (w - l3A p) / l3B p, 1 + (w - l3A p) / l3B p / 20]) ∧
    (l3A p + l3B p ≤ w → x p w = ![2 + 4 * ((w - l3A p - l3B p) / l3C p),
      2 + (w - l3A p - l3B p) / l3C p, 21 / 20 + (w - l3A p - l3B p) / l3C p / 40]) := by
  have h0 := hp 0
  have h1 := hp 1
  have h2 := hp 2
  have hA : 0 < l3A p := by unfold l3A; positivity
  have hB : 0 < l3B p := by unfold l3B; positivity
  have hC : 0 < l3C p := by unfold l3C; positivity
  have key : ∀ τ : ℝ, 0 ≤ τ → ∀ y : Fin 3 → ℝ, y = ![l3G0 τ, τ, l3G2 τ] → w = p ⬝ᵥ y →
      x p w = y := by
    intro τ hτ y hy hwy
    have := hx p w ⟨hp, hw⟩
    rw [hwy, hy, l3U_demand hp hτ] at this
    rw [hwy, hy]
    exact this
  have hv : ∀ a b c : ℝ, (![a, b, c] : Fin 3 → ℝ) 0 = a ∧ (![a, b, c] : Fin 3 → ℝ) 1 = b ∧
      (![a, b, c] : Fin 3 → ℝ) 2 = c := fun a b c => ⟨rfl, rfl, rfl⟩
  refine ⟨fun h => ?_, fun ha hb => ?_, fun h => ?_⟩
  · set τ := w / l3A p with hτ
    have hτ1 : τ ≤ 1 := (div_le_one hA).mpr h
    have g0 : l3G0 τ = τ := max_eq_left (by linarith)
    have g2 : l3G2 τ = τ := by
      unfold l3G2
      rw [min_eq_left (show τ ≤ τ / 20 + 19 / 20 by linarith),
        min_eq_left (show τ ≤ τ / 40 + 1 by linarith)]
    apply key τ (by positivity) _ (by rw [g0, g2])
    rw [dotProduct_three, (hv _ _ _).1, (hv _ _ _).2.1, (hv _ _ _).2.2, hτ]
    unfold l3A at *
    field_simp
  · set τ := 1 + (w - l3A p) / l3B p with hτ
    have hτ1 : 1 ≤ τ := by have := div_nonneg (sub_nonneg.mpr ha) hB.le; linarith
    have hτ2 : τ ≤ 2 := by
      have : (w - l3A p) / l3B p ≤ 1 := (div_le_one hB).mpr (by linarith)
      linarith
    have g0 : l3G0 τ = τ := max_eq_left (by linarith)
    have g2 : l3G2 τ = τ / 20 + 19 / 20 := by
      unfold l3G2
      rw [min_eq_right (show τ / 20 + 19 / 20 ≤ τ by linarith),
        min_eq_left (show τ / 20 + 19 / 20 ≤ τ / 40 + 1 by linarith)]
    apply key τ (by linarith)
    · rw [g0, g2, hτ]
      funext l; fin_cases l <;> simp
      ring
    · rw [dotProduct_three, (hv _ _ _).1, (hv _ _ _).2.1, (hv _ _ _).2.2, hτ]
      unfold l3A l3B at *
      field_simp
      ring
  · set τ := 2 + (w - l3A p - l3B p) / l3C p with hτ
    have hτ2 : 2 ≤ τ := by
      have := div_nonneg (show 0 ≤ w - l3A p - l3B p by linarith) hC.le; linarith
    have g0 : l3G0 τ = 4 * τ - 6 := max_eq_right (by linarith)
    have g2 : l3G2 τ = τ / 40 + 1 := by
      unfold l3G2
      rw [min_eq_right (show τ / 20 + 19 / 20 ≤ τ by linarith),
        min_eq_right (show τ / 40 + 1 ≤ τ / 20 + 19 / 20 by linarith)]
    apply key τ (by linarith)
    · rw [g0, g2, hτ]
      funext l; fin_cases l <;> simp <;> ring
    · rw [dotProduct_three, (hv _ _ _).1, (hv _ _ _).2.1, (hv _ _ _).2.2, hτ]
      unfold l3A l3B l3C at *
      field_simp
      ring

/-- `∫` over `(0, W]` of a function that is affine on `(0, A]`, `(A, M]` and `(M, W]`. -/
theorem integral_three_piece {f : ℝ → ℝ} {A M W c₁ e₁ c₂ e₂ c₃ e₃ : ℝ} (hA : 0 ≤ A)
    (hAM : A ≤ M) (hMW : M ≤ W) (h₁ : ∀ w ∈ Set.Ioc 0 A, f w = c₁ * w + e₁)
    (h₂ : ∀ w ∈ Set.Ioc A M, f w = c₂ * w + e₂) (h₃ : ∀ w ∈ Set.Ioc M W, f w = c₃ * w + e₃) :
    ∫ w in Set.Ioc 0 W, f w = (c₁ * ((A ^ 2 - 0 ^ 2) / 2) + e₁ * (A - 0)) +
      (c₂ * ((M ^ 2 - A ^ 2) / 2) + e₂ * (M - A)) +
        (c₃ * ((W ^ 2 - M ^ 2) / 2) + e₃ * (W - M)) := by
  have piece : ∀ {s t c e : ℝ}, s ≤ t → (∀ w ∈ Set.Ioc s t, f w = c * w + e) →
      IntervalIntegrable f volume s t ∧
        ∫ w in s..t, f w = c * ((t ^ 2 - s ^ 2) / 2) + e * (t - s) := by
    intro s t c e hst h
    have hg : IntegrableOn (fun w => c * w + e) (Set.Ioc s t) :=
      (by fun_prop : Continuous fun w : ℝ => c * w + e).integrableOn_Ioc
    refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le hst).mpr
      (hg.congr_fun (fun w hw => (h w hw).symm) measurableSet_Ioc), ?_⟩
    rw [intervalIntegral.integral_of_le hst, setIntegral_congr_fun measurableSet_Ioc h,
      ← intervalIntegral.integral_of_le hst, integral_affine]
  obtain ⟨i₁, e₁'⟩ := piece hA h₁
  obtain ⟨i₂, e₂'⟩ := piece hAM h₂
  obtain ⟨i₃, e₃'⟩ := piece hMW h₃
  rw [← intervalIntegral.integral_of_le (hA.trans (hAM.trans hMW)),
    ← intervalIntegral.integral_add_adjacent_intervals (i₁.trans i₂) i₃,
    ← intervalIntegral.integral_add_adjacent_intervals i₁ i₂, e₁', e₂', e₃']

/-- **Exercise 4.D.11** (MWG, p. 126), aggregate demand of the three-good Hildenbrand economy:
for `W = 2m ≥ A + B`, `X(p, m) = [a (W - A/2) + b (W - A - B/2) + c (W - A - B)²/(2C)]/W`. -/
theorem l3_agg {x : DemandFunction 3}
    (hx : ∀ p w, PWDomain p w → x p w ∈ walrasianDemand l3U p w) {p : Fin 3 → ℝ}
    (hp : StrictlyPositive p) {m : ℝ} (hm : l3A p + l3B p ≤ 2 * m) :
    hildMeanDemand x p m =
      ![((2 * m - l3A p / 2) + (2 * m - l3A p - l3B p / 2) +
          4 * (2 * m - l3A p - l3B p) ^ 2 / (2 * l3C p)) / (2 * m),
        ((2 * m - l3A p / 2) + (2 * m - l3A p - l3B p / 2) +
          (2 * m - l3A p - l3B p) ^ 2 / (2 * l3C p)) / (2 * m),
        ((2 * m - l3A p / 2) + (2 * m - l3A p - l3B p / 2) / 20 +
          (2 * m - l3A p - l3B p) ^ 2 / (2 * l3C p) / 40) / (2 * m)] := by
  have hA : 0 < l3A p := by have := hp 0; have := hp 1; have := hp 2; unfold l3A; positivity
  have hB : 0 < l3B p := by have := hp 0; have := hp 1; have := hp 2; unfold l3B; positivity
  have hC : 0 < l3C p := by have := hp 0; have := hp 1; have := hp 2; unfold l3C; positivity
  have hW : 0 < 2 * m := by linarith
  have d := fun w (hw : 0 < w) => l3_demand hx hp hw
  set A := l3A p
  set B := l3B p
  set C := l3C p
  have hint : ∀ l : Fin 3, ∀ c₁ e₁ c₂ e₂ c₃ e₃ : ℝ,
      (∀ w ∈ Set.Ioc 0 A, x p w l = c₁ * w + e₁) →
      (∀ w ∈ Set.Ioc A (A + B), x p w l = c₂ * w + e₂) →
      (∀ w ∈ Set.Ioc (A + B) (2 * m), x p w l = c₃ * w + e₃) →
      hildMeanDemand x p m l = (1 / (2 * m)) * ((c₁ * ((A ^ 2 - 0 ^ 2) / 2) + e₁ * (A - 0)) +
        (c₂ * (((A + B) ^ 2 - A ^ 2) / 2) + e₂ * (A + B - A)) +
        (c₃ * (((2 * m) ^ 2 - (A + B) ^ 2) / 2) + e₃ * (2 * m - (A + B)))) := by
    intro l c₁ e₁ c₂ e₂ c₃ e₃ h₁ h₂ h₃
    simp only [hildMeanDemand, hildenbrandDemand, Pi.smul_apply, smul_eq_mul]
    rw [integral_three_piece hA.le (by linarith) hm h₁ h₂ h₃]
  funext l
  fin_cases l
  · refine (hint _ (1 / A) 0 (1 / B) (1 - A / B) (4 / C) (2 - 4 * (A + B) / C) ?_ ?_ ?_).trans ?_
    · intro w hw; rw [(d w hw.1).1 hw.2]; simp; field_simp
    · intro w hw; rw [(d w (by linarith [hw.1])).2.1 hw.1.le hw.2]; simp; field_simp; ring
    · intro w hw; rw [(d w (by linarith [hw.1])).2.2 hw.1.le]; simp; field_simp; ring
    · simp; field_simp; ring
  · refine (hint _ (1 / A) 0 (1 / B) (1 - A / B) (1 / C) (2 - (A + B) / C) ?_ ?_ ?_).trans ?_
    · intro w hw; rw [(d w hw.1).1 hw.2]; simp; field_simp
    · intro w hw; rw [(d w (by linarith [hw.1])).2.1 hw.1.le hw.2]; simp; field_simp; ring
    · intro w hw; rw [(d w (by linarith [hw.1])).2.2 hw.1.le]; simp; field_simp; ring
    · simp; field_simp; ring
  · refine (hint _ (1 / A) 0 (1 / (20 * B)) (1 - A / (20 * B)) (1 / (40 * C))
      (21 / 20 - (A + B) / (40 * C)) ?_ ?_ ?_).trans ?_
    · intro w hw; rw [(d w hw.1).1 hw.2]; simp; field_simp
    · intro w hw; rw [(d w (by linarith [hw.1])).2.1 hw.1.le hw.2]; simp; field_simp; ring
    · intro w hw; rw [(d w (by linarith [hw.1])).2.2 hw.1.le]; simp; field_simp; ring
    · simp; field_simp; ring

/-- The economy of Exercise 4.D.11 exists: `l3U` is continuous, so it has a demand function. -/
theorem l3_demand_exists :
    ∃ x : DemandFunction 3, ∀ p w, PWDomain p w → x p w ∈ walrasianDemand l3U p w :=
  exists_demandFunction continuous_l3U.continuousOn

/-- **Exercise 4.D.11** (MWG, p. 126). The Hildenbrand economy with three goods, identical
L-shaped preferences `l3U` and wealth uniform on `[0, 2m]` has no positive representative
consumer: its aggregate demand has a cycle of three revealed preferences. -/
theorem exercise_4_D_11 {x : DemandFunction 3}
    (hx : ∀ p w, PWDomain p w → x p w ∈ walrasianDemand l3U p w) :
    ¬ ∃ r, IsPositiveRepresentative r (hildMeanDemand x) := by
  rintro ⟨r, hr⟩
  have hpos : ∀ a b : ℝ, 0 < a → 0 < b → StrictlyPositive (![1, a, b] : Fin 3 → ℝ) := by
    intro a b ha hb l; fin_cases l <;> simp [ha, hb]
  have hp1 := hpos (1 / 3) (4 / 3) (by norm_num) (by norm_num)
  have hp2 := hpos (12 / 5) (3 / 10) (by norm_num) (by norm_num)
  have hp3 := hpos 3 1 (by norm_num) (by norm_num)
  have hd1 : PWDomain ![1, 1 / 3, 4 / 3] (63 / 20) := ⟨hp1, by norm_num⟩
  have hd2 : PWDomain ![1, 12 / 5, 3 / 10] (1017 / 200) := ⟨hp2, by norm_num⟩
  have hd3 : PWDomain ![1, 3, 1] (647 / 100) := ⟨hp3, by norm_num⟩
  have e1 := l3_agg hx hp1 (m := 63 / 20) (by norm_num [l3A, l3B])
  have e2 := l3_agg hx hp2 (m := 1017 / 200) (by norm_num [l3A, l3B])
  have e3 := l3_agg hx hp3 (m := 647 / 100) (by norm_num [l3A, l3B])
  simp only [l3A, l3B, l3C, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons] at e1 e2 e3
  norm_num at e1 e2 e3
  -- each step of the cycle is a strict revealed preference
  have step : ∀ p m p' m', PWDomain p m → PWDomain p' m' →
      p ⬝ᵥ hildMeanDemand x p' m' ≤ m → hildMeanDemand x p' m' ≠ hildMeanDemand x p m →
      Strict r (hildMeanDemand x p m) (hildMeanDemand x p' m') :=
    fun p m p' m' hd hd' hle hne => (hr.2 p m hd).2 _ ⟨(hr.2 p' m' hd').1.1, hle⟩ hne
  have s12 := step _ _ _ _ hd1 hd2 (by rw [e2, dotProduct_three]; norm_num)
    (by rw [e1, e2]; intro h; have := congrFun h 0; norm_num at this)
  have s23 := step _ _ _ _ hd2 hd3 (by rw [e3, dotProduct_three]; norm_num)
    (by rw [e2, e3]; intro h; have := congrFun h 0; norm_num at this)
  have s31 := step _ _ _ _ hd3 hd1 (by rw [e1, dotProduct_three]; norm_num)
    (by rw [e3, e1]; intro h; have := congrFun h 0; norm_num at this)
  exact s31.2 (hr.1.2 _ (hr.2 _ _ hd1).1.1 _ (hr.2 _ _ hd2).1.1 _ (hr.2 _ _ hd3).1.1 s12.1 s23.1)

end MWG.AggregateDemand
