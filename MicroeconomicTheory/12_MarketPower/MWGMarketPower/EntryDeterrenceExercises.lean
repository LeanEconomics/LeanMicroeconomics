/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGMarketPower.EntryDeterrence

/-!
# Exercise 12.BB.3: entry deterrence by plant proliferation in the linear city

MWG, Exercise 12.BB.3, p. 435, in the linear city of Example 12.C.2 (consumers of mass `M`
uniform on `[0, 1]`, unit demand with value `v`, transport cost `t` per unit distance, marginal
cost `c`, and `v > c + 3t`). Firm I first builds one plant (at an end) or two plants (one at
each end), each costing `F > 0`; then E decides whether to build one plant and at which end;
then the plants compete in prices.

Demand. With prices `m` at end `0` (the lowest price there) and `q` at end `1`, the consumers
buying at end `0` are the `z ∈ [0, 1]` with `m + tz ≤ v` and `m + tz ≤ q + t(1 − z)`, of mass
`M·clamp(min{(v − m)/t, (t + q − m)/(2t)})` (`bb3D`, `clamp x = max 0 (min x 1)`); a plant alone
in the market at end `0` sells `M·clamp((v − m)/t)`; two plants at the same end share their
customers by price, equally at a tie (`bb3ShareE`).

Subgames.
* `exercise_12_BB_3_monopoly_one`: one plant, no entry: the unique optimal price is `v − t`
  (the whole market is served), profit `(v − t − c)M`.
* `exercise_12_BB_3_monopoly_two`: two plants, no entry: the unique optimal prices are
  `v − t/2` at both ends, profit `(v − t/2 − c)M`.
* `exercise_12_BB_3_duopoly`: one plant each at opposite ends: Example 12.C.2 (`example_12_C_2`),
  unique equilibrium `c + t`, profit `tM/2` each.
* `exercise_12_BB_3_coloc_two`, `exercise_12_BB_3_coloc_one`: E's plant at the same end as one of
  I's plants: in every price equilibrium E earns zero (`bb3_coloc_zero`, a Bertrand argument),
  and an equilibrium exists. (E at end `1` against I's two plants is the mirror image
  `z ↦ 1 − z` of E at end `0`.)

Equilibrium (`exercise_12_BB_3`): against two plants E stays out; against one plant E enters at
the far end iff `F < tM/2`. Hence if `F < tM/2`, I builds two plants and E stays out (prices
`v − t/2`); if `F > tM/2`, I builds one plant and E stays out (price `v − t`).

Welfare (`exercise_12_BB_3_welfare`): the transport costs are `tM/2` with one plant and `tM/4`
with plants at both ends (`bb3_transport_one`, `bb3_transport_two`). A monopolist with no
entrant makes the same plant choice (two plants iff `F < tM/2`), so welfare is the same as with
the entrant; if I may build only one plant, then for `F < tM/2` E enters at the other end and
total surplus is again the same (the plant configuration is the same), while consumer surplus
is strictly higher, by `M(v − c − 3t/2)`.

The prices in the opposite-ends duopoly are those of Example 12.C.2 (`lcDemand`, where every
consumer buys); with `v > c + 3t` no consumer facing prices at most `c + 2t` at both ends
prefers not to buy, which is why Example 12.C.2's model applies there.
-/

namespace MWG.MarketPower

/-- `clamp x = max 0 (min x 1)`. -/
noncomputable def bb3Cl (x : ℝ) : ℝ := max 0 (min x 1)

theorem bb3Cl_nonneg (x : ℝ) : 0 ≤ bb3Cl x := le_max_left _ _

theorem bb3Cl_le_one (x : ℝ) : bb3Cl x ≤ 1 := max_le zero_le_one (min_le_right _ _)

theorem bb3Cl_mono {x y : ℝ} (h : x ≤ y) : bb3Cl x ≤ bb3Cl y :=
  max_le_max le_rfl (min_le_min_right _ h)

theorem bb3Cl_le_max (x : ℝ) : bb3Cl x ≤ max 0 x := max_le_max le_rfl (min_le_left _ _)

theorem bb3Cl_le_of_pos {x : ℝ} (h : 0 < bb3Cl x) : bb3Cl x ≤ x := by
  unfold bb3Cl at h ⊢
  rcases le_total 0 (min x 1) with h1 | h1
  · rw [max_eq_right h1]; exact min_le_left _ _
  · rw [max_eq_left h1] at h; exact absurd h (lt_irrefl 0)

theorem bb3Cl_lip {x y : ℝ} (h : x ≤ y) : bb3Cl y - bb3Cl x ≤ y - x := by
  unfold bb3Cl
  rcases le_total y 1 with h1 | h1 <;> rcases le_total x 1 with h2 | h2 <;>
    simp only [min_eq_left, min_eq_right, h1, h2] <;>
    rcases le_total 0 x with h3 | h3 <;> rcases le_total 0 y with h4 | h4 <;>
    simp only [max_eq_left, max_eq_right, h3, h4, zero_le_one] <;> linarith

theorem bb3Cl_of_mem {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : bb3Cl x = x := by
  unfold bb3Cl; rw [min_eq_left h1, max_eq_right h0]

/-- Demand at end `0` when the lowest price there is `m` and the price at end `1` is `q`:
`M·clamp(min{(v − m)/t, (t + q − m)/(2t)})`. Demand at end `1` is `bb3D v t M q m`. -/
noncomputable def bb3D (v t M m q : ℝ) : ℝ := M * bb3Cl (min ((v - m) / t) ((t + q - m) / (2 * t)))

/-- E's share of the end-`0` demand `D` when E charges `e` and I's plant there charges `p`. -/
noncomputable def bb3ShareE (e p D : ℝ) : ℝ := if e < p then D else if e = p then D / 2 else 0

theorem bb3ShareE_nonneg {e p D : ℝ} (hD : 0 ≤ D) : 0 ≤ bb3ShareE e p D := by
  unfold bb3ShareE; split_ifs <;> linarith

theorem bb3ShareE_le {e p D : ℝ} (hD : 0 ≤ D) : bb3ShareE e p D ≤ D := by
  unfold bb3ShareE; split_ifs <;> linarith

theorem bb3D_nonneg {v t M m q : ℝ} (hM : 0 ≤ M) : 0 ≤ bb3D v t M m q :=
  mul_nonneg hM (bb3Cl_nonneg _)

theorem bb3D_le {v t M m q : ℝ} (hM : 0 ≤ M) : bb3D v t M m q ≤ M := by
  unfold bb3D; nlinarith [bb3Cl_le_one (min ((v - m) / t) ((t + q - m) / (2 * t)))]

/-- Demand at an end falls with the price there. -/
theorem bb3D_anti {v t M q : ℝ} (ht : 0 < t) (hM : 0 ≤ M) : Antitone (fun m => bb3D v t M m q) := by
  intro m m' h
  simp only [bb3D]
  apply mul_le_mul_of_nonneg_left (bb3Cl_mono (min_le_min _ _)) hM
  · exact div_le_div_of_nonneg_right (by linarith) ht.le
  · exact div_le_div_of_nonneg_right (by linarith) (by linarith)

/-- Demand at end `1` rises with the price at end `0`, with slope at most `M/(2t)`. -/
theorem bb3D_lip {v t M q m m' : ℝ} (ht : 0 < t) (hM : 0 ≤ M) (h : m' ≤ m) :
    bb3D v t M q m' ≤ bb3D v t M q m ∧
      bb3D v t M q m - bb3D v t M q m' ≤ M * (m - m') / (2 * t) := by
  have hB : (t + m' - q) / (2 * t) ≤ (t + m - q) / (2 * t) :=
    div_le_div_of_nonneg_right (by linarith) (by linarith)
  have hmin : min ((v - q) / t) ((t + m' - q) / (2 * t)) ≤
      min ((v - q) / t) ((t + m - q) / (2 * t)) := min_le_min_left _ hB
  have hdiff : min ((v - q) / t) ((t + m - q) / (2 * t)) -
      min ((v - q) / t) ((t + m' - q) / (2 * t)) ≤ (m - m') / (2 * t) := by
    have e : (t + m - q) / (2 * t) - (t + m' - q) / (2 * t) = (m - m') / (2 * t) := by ring
    rcases min_cases ((v - q) / t) ((t + m - q) / (2 * t)) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
      rcases min_cases ((v - q) / t) ((t + m' - q) / (2 * t)) with ⟨h2, _⟩ | ⟨h2, _⟩ <;>
      rw [h1, h2] <;> nlinarith [div_nonneg (sub_nonneg.2 h) (by linarith : (0 : ℝ) ≤ 2 * t)]
  unfold bb3D
  refine ⟨mul_le_mul_of_nonneg_left (bb3Cl_mono hmin) hM, ?_⟩
  have := bb3Cl_lip hmin
  have e : M * (m - m') / (2 * t) = M * ((m - m') / (2 * t)) := by ring
  rw [e, ← mul_sub]
  exact mul_le_mul_of_nonneg_left (by linarith) hM

/-- **Bertrand competition at a shared location.** Let `D₀(m)` (decreasing, with values in
`[0, M]`) be the demand at an end where E (price `e`) and one of I's plants (price `p`) are
both located, and let `R(m)` be the profit of I's other plants as a function of the lowest
price `m` at that end, with `R(m') ≥ R(m) − L(m − m')` for `m' ≤ m`. If neither E (changing
`e`) nor I (changing `p`) can gain, E's profit is zero. -/
theorem bb3_coloc_zero {D0 R : ℝ → ℝ} {M L c e p : ℝ} (hD0 : Antitone D0)
    (hD0n : ∀ m, 0 ≤ D0 m) (hD0M : ∀ m, D0 m ≤ M) (hL : 0 ≤ L)
    (hR : ∀ m m', m' ≤ m → R m - L * (m - m') ≤ R m')
    (hE : ∀ e', (e' - c) * bb3ShareE e' p (D0 (min e' p)) ≤
      (e - c) * bb3ShareE e p (D0 (min e p)))
    (hI : ∀ p', (p' - c) * (D0 (min e p') - bb3ShareE e p' (D0 (min e p'))) + R (min e p') ≤
      (p - c) * (D0 (min e p) - bb3ShareE e p (D0 (min e p))) + R (min e p)) :
    (e - c) * bb3ShareE e p (D0 (min e p)) = 0 := by
  have hge : 0 ≤ (e - c) * bb3ShareE e p (D0 (min e p)) := by
    have := hE c; rw [sub_self, zero_mul] at this; exact this
  refine le_antisymm ?_ hge
  by_contra hpos
  have hpos : 0 < (e - c) * bb3ShareE e p (D0 (min e p)) := lt_of_not_ge hpos
  have hsn : 0 ≤ bb3ShareE e p (D0 (min e p)) := bb3ShareE_nonneg (hD0n _)
  have hec : 0 < e - c := by
    by_contra h
    have : (e - c) * bb3ShareE e p (D0 (min e p)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt h) hsn
    linarith
  have hs : 0 < bb3ShareE e p (D0 (min e p)) := by
    by_contra h
    have : bb3ShareE e p (D0 (min e p)) = 0 := le_antisymm (le_of_not_gt h) hsn
    rw [this, mul_zero] at hpos; exact lt_irrefl 0 hpos
  have hep : e ≤ p := by
    by_contra h
    have h : p < e := lt_of_not_ge h
    have : bb3ShareE e p (D0 (min e p)) = 0 := by
      unfold bb3ShareE
      simp only [not_lt.2 h.le, ne_of_gt h, ↓reduceIte]
    linarith
  have hm : min e p = e := min_eq_left hep
  rw [hm] at hpos hs hsn hI
  have hold : (p - c) * (D0 e - bb3ShareE e p (D0 e)) =
      (e - c) * (D0 e - bb3ShareE e p (D0 e)) := by
    rcases eq_or_lt_of_le hep with h | h
    · rw [h]
    · have : bb3ShareE e p (D0 e) = D0 e := by unfold bb3ShareE; simp only [h, ↓reduceIte]
      rw [this]; ring
  have hM0 : 0 ≤ M := (hD0n 0).trans (hD0M 0)
  obtain ⟨ε, hε0, hε1, hε2⟩ : ∃ ε : ℝ, 0 < ε ∧ ε ≤ (e - c) / 2 ∧
      ε * (2 * (M + L + 1)) ≤ (e - c) * bb3ShareE e p (D0 e) := by
    refine ⟨min ((e - c) / 2) ((e - c) * bb3ShareE e p (D0 e) / (2 * (M + L + 1))),
      lt_min (by linarith) (div_pos hpos (by linarith)), min_le_left _ _, ?_⟩
    have := min_le_right ((e - c) / 2) ((e - c) * bb3ShareE e p (D0 e) / (2 * (M + L + 1)))
    rwa [le_div_iff₀ (by linarith)] at this
  have hdev := hI (e - ε)
  have hm' : min e (e - ε) = e - ε := min_eq_right (by linarith)
  have hsh : bb3ShareE e (e - ε) (D0 (e - ε)) = 0 := by
    unfold bb3ShareE
    have h1 : ¬ e < e - ε := by linarith
    have h2 : e ≠ e - ε := by intro h; linarith
    simp only [h1, h2, ↓reduceIte]
  rw [hm', hsh, hold] at hdev
  have hD0e : D0 e ≤ D0 (e - ε) := hD0 (by linarith)
  have hRe : R e - L * ε ≤ R (e - ε) := by
    have := hR e (e - ε) (by linarith)
    rwa [show e - (e - ε) = ε by ring] at this
  have h1 : (e - ε - c) * D0 e ≤ (e - ε - c) * D0 (e - ε) :=
    mul_le_mul_of_nonneg_left hD0e (by linarith)
  have h2 : ε * D0 e ≤ ε * M := mul_le_mul_of_nonneg_left (hD0M e) hε0.le
  have h3 : 0 < ε * (M + L + 1) := mul_pos hε0 (by linarith)
  nlinarith

/-- Profits in the colocation subgame against two plants: E at end `0` (price `e`), I's plants
at end `0` (price `p`) and end `1` (price `q`). -/
noncomputable def bb3ProfitE2 (v t M c e p q : ℝ) : ℝ :=
  (e - c) * bb3ShareE e p (bb3D v t M (min e p) q)

noncomputable def bb3ProfitI2 (v t M c e p q : ℝ) : ℝ :=
  (p - c) * (bb3D v t M (min e p) q - bb3ShareE e p (bb3D v t M (min e p) q)) +
    (q - c) * bb3D v t M q (min e p)

/-- Price equilibrium of the colocation subgame against two plants (I chooses both prices). -/
def IsBB3Coloc2Nash (v t M c e p q : ℝ) : Prop :=
  (∀ e', bb3ProfitE2 v t M c e' p q ≤ bb3ProfitE2 v t M c e p q) ∧
    ∀ p' q', bb3ProfitI2 v t M c e p' q' ≤ bb3ProfitI2 v t M c e p q

/-- Profits in the colocation subgame against one plant: E and I both at end `0`. -/
noncomputable def bb3ProfitE1 (v t M c e p : ℝ) : ℝ :=
  (e - c) * bb3ShareE e p (M * bb3Cl ((v - min e p) / t))

noncomputable def bb3ProfitI1 (v t M c e p : ℝ) : ℝ :=
  (p - c) * (M * bb3Cl ((v - min e p) / t) - bb3ShareE e p (M * bb3Cl ((v - min e p) / t)))

/-- Price equilibrium of the colocation subgame against one plant. -/
def IsBB3Coloc1Nash (v t M c e p : ℝ) : Prop :=
  (∀ e', bb3ProfitE1 v t M c e' p ≤ bb3ProfitE1 v t M c e p) ∧
    ∀ p', bb3ProfitI1 v t M c e p' ≤ bb3ProfitI1 v t M c e p

/-- Pricing below a rival at the same location never earns E a positive profit when E's price
is at most the rival's: `(e − p)·share ≤ 0`. -/
theorem bb3_shareE_profit_le {e p D : ℝ} (hD : 0 ≤ D) : (e - p) * bb3ShareE e p D ≤ 0 := by
  unfold bb3ShareE
  split_ifs with h1 h2
  · exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hD
  · rw [h2, sub_self, zero_mul]
  · rw [mul_zero]

/-- I's plant facing E's price `e` at the same location: `(p − e)·(D − share_E) ≤ 0`. -/
theorem bb3_I_term_le {e p D : ℝ} (hD : 0 ≤ D) : (p - e) * (D - bb3ShareE e p D) ≤ 0 := by
  unfold bb3ShareE
  split_ifs with h1 h2
  · rw [sub_self, mul_zero]
  · rw [h2, sub_self, zero_mul]
  · have : p < e := lt_of_le_of_ne (le_of_not_gt h1) (fun h => h2 h.symm)
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)

/-- **Exercise 12.BB.3, E next to one of I's two plants** (MWG, p. 435). In every price
equilibrium of the subgame in which E has located at an end where I has a plant (I having
plants at both ends), E's operating profit is zero; and such an equilibrium exists
(`e = p = c`, `q = c + t/2`, I earning `tM/8`). -/
theorem exercise_12_BB_3_coloc_two {v t M c : ℝ} (ht : 0 < t) (hM : 0 < M) (hv : c + 3 * t < v) :
    (∀ e p q, IsBB3Coloc2Nash v t M c e p q → bb3ProfitE2 v t M c e p q = 0) ∧
    IsBB3Coloc2Nash v t M c c c (c + t / 2) ∧
    bb3ProfitI2 v t M c c c (c + t / 2) = t * M / 8 := by
  have hval : bb3ProfitI2 v t M c c c (c + t / 2) = t * M / 8 := by
    unfold bb3ProfitI2
    rw [sub_self, zero_mul, zero_add, min_self]
    have hmin : min ((v - (c + t / 2)) / t) ((t + c - (c + t / 2)) / (2 * t)) = 1 / 4 := by
      have e : (t + c - (c + t / 2)) / (2 * t) = 1 / 4 := by field_simp; ring
      rw [e, min_eq_right]
      rw [le_div_iff₀ ht]; linarith
    unfold bb3D
    rw [hmin, bb3Cl_of_mem (x := 1 / 4) (by norm_num) (by norm_num)]
    ring
  refine ⟨fun e p q hN => ?_, ⟨fun e' => ?_, fun p' q' => ?_⟩, hval⟩
  · obtain ⟨hE, hI⟩ := hN
    refine bb3_coloc_zero (D0 := fun m => bb3D v t M m q)
      (R := fun m => (q - c) * bb3D v t M q m) (M := M) (L := |q - c| * M / (2 * t))
      (bb3D_anti ht hM.le) (fun _ => bb3D_nonneg hM.le) (fun _ => bb3D_le hM.le)
      (by positivity) ?_ (fun e' => hE e') (fun p' => hI p' q)
    intro m m' hmm
    obtain ⟨h1, h2⟩ := bb3D_lip (v := v) (q := q) ht hM.le hmm
    have h3 : (q - c) * (bb3D v t M q m - bb3D v t M q m') ≤
        |q - c| * (bb3D v t M q m - bb3D v t M q m') :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
    have h4 : |q - c| * (bb3D v t M q m - bb3D v t M q m') ≤ |q - c| * (M * (m - m') / (2 * t)) :=
      mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
    have e : |q - c| * M / (2 * t) * (m - m') = |q - c| * (M * (m - m') / (2 * t)) := by ring
    nlinarith
  · unfold bb3ProfitE2
    rw [sub_self, zero_mul]
    exact bb3_shareE_profit_le (bb3D_nonneg hM.le)
  · rw [hval]
    unfold bb3ProfitI2
    have h1 := bb3_I_term_le (e := c) (p := p') (D := bb3D v t M (min c p') q')
      (bb3D_nonneg hM.le)
    have h2 : (q' - c) * bb3D v t M q' (min c p') ≤ t * M / 8 := by
      rcases le_or_gt q' c with hq | hq
      · nlinarith [bb3D_nonneg (v := v) (t := t) (m := q') (q := min c p') hM.le]
      · have hle : bb3D v t M q' (min c p') ≤ M * max 0 ((t + c - q') / (2 * t)) := by
          unfold bb3D
          apply mul_le_mul_of_nonneg_left _ hM.le
          refine (bb3Cl_le_max _).trans (max_le_max le_rfl ((min_le_right _ _).trans ?_))
          exact div_le_div_of_nonneg_right (by linarith [min_le_left c p']) (by linarith)
        have hb : (q' - c) * max 0 ((t + c - q') / (2 * t)) ≤ t / 8 := by
          rcases le_total 0 ((t + c - q') / (2 * t)) with h | h
          · rw [max_eq_right h]
            have e : (q' - c) * ((t + c - q') / (2 * t)) = (q' - c) * (t + c - q') / (2 * t) := by
              ring
            rw [e, div_le_iff₀ (by linarith)]
            nlinarith [sq_nonneg (q' - c - t / 2)]
          · rw [max_eq_left h, mul_zero]; linarith
        have := mul_le_mul_of_nonneg_left hle (by linarith : (0 : ℝ) ≤ q' - c)
        nlinarith
    linarith

/-- **Exercise 12.BB.3, E next to I's single plant** (MWG, p. 435). In every price equilibrium
of the subgame in which E has located at the same end as I's only plant, E's operating profit
is zero (Bertrand); and `e = p = c` is an equilibrium. -/
theorem exercise_12_BB_3_coloc_one {v t M c : ℝ} (ht : 0 < t) (hM : 0 < M) :
    (∀ e p, IsBB3Coloc1Nash v t M c e p → bb3ProfitE1 v t M c e p = 0) ∧
    IsBB3Coloc1Nash v t M c c c := by
  have hD : ∀ m, 0 ≤ M * bb3Cl ((v - m) / t) := fun _ => mul_nonneg hM.le (bb3Cl_nonneg _)
  refine ⟨fun e p hN => ?_, fun e' => ?_, fun p' => ?_⟩
  · obtain ⟨hE, hI⟩ := hN
    refine bb3_coloc_zero (D0 := fun m => M * bb3Cl ((v - m) / t)) (R := fun _ => 0) (M := M)
      (L := 0) ?_ hD (fun m => by nlinarith [bb3Cl_le_one ((v - m) / t)]) le_rfl
      (fun _ _ _ => by simp) (fun e' => hE e') (fun p' => by
        have := hI p'; unfold bb3ProfitI1 at this; simpa using this)
    intro m m' h
    exact mul_le_mul_of_nonneg_left (bb3Cl_mono (div_le_div_of_nonneg_right (by linarith) ht.le))
      hM.le
  · unfold bb3ProfitE1
    rw [sub_self, zero_mul]
    exact bb3_shareE_profit_le (hD _)
  · unfold bb3ProfitI1
    rw [sub_self, zero_mul]
    exact bb3_I_term_le (hD _)

/-- **Exercise 12.BB.3, one plant and no entry** (MWG, p. 435). A monopolist with one plant at an
end earns at most `(v − t − c)M`; the price `v − t` (serving the whole market) attains it and is
the unique optimal price. -/
theorem exercise_12_BB_3_monopoly_one {v t M c : ℝ} (ht : 0 < t) (hM : 0 < M)
    (hv : c + 3 * t < v) :
    (∀ p, (p - c) * (M * bb3Cl ((v - p) / t)) ≤ (v - t - c) * M) ∧
    (v - t - c) * (M * bb3Cl ((v - (v - t)) / t)) = (v - t - c) * M ∧
    ∀ p, (p - c) * (M * bb3Cl ((v - p) / t)) = (v - t - c) * M → p = v - t := by
  have key : ∀ p, (p - c) * bb3Cl ((v - p) / t) ≤
      (v - c) * bb3Cl ((v - p) / t) - t * bb3Cl ((v - p) / t) ^ 2 := by
    intro p
    rcases eq_or_lt_of_le (bb3Cl_nonneg ((v - p) / t)) with h | h
    · rw [← h]; ring_nf; exact le_rfl
    · have hx := bb3Cl_le_of_pos h
      rw [le_div_iff₀ ht] at hx
      nlinarith
  have hg : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → (v - c) * x - t * x ^ 2 ≤ v - t - c := by
    intro x h0 h1
    have : 0 ≤ v - c - t * (1 + x) := by nlinarith [mul_le_mul_of_nonneg_left h1 ht.le]
    nlinarith [mul_nonneg (sub_nonneg.2 h1) this]
  refine ⟨fun p => ?_, ?_, fun p hp => ?_⟩
  · have := (key p).trans (hg _ (bb3Cl_nonneg _) (bb3Cl_le_one _))
    nlinarith
  · rw [show (v - (v - t)) / t = 1 by field_simp; ring, bb3Cl_of_mem zero_le_one le_rfl]; ring
  · have hp' : (p - c) * bb3Cl ((v - p) / t) = v - t - c := by
      have : M * ((p - c) * bb3Cl ((v - p) / t)) = M * (v - t - c) := by linarith
      exact mul_left_cancel₀ hM.ne' this
    have h0 := bb3Cl_nonneg ((v - p) / t)
    have h1 := bb3Cl_le_one ((v - p) / t)
    have hk := key p
    have hx : bb3Cl ((v - p) / t) = 1 := by
      by_contra hne
      have hlt : bb3Cl ((v - p) / t) < 1 := lt_of_le_of_ne h1 hne
      have : 0 < v - c - t * (1 + bb3Cl ((v - p) / t)) := by
        nlinarith [mul_le_mul_of_nonneg_left h1 ht.le]
      nlinarith [mul_pos (sub_pos.2 hlt) this]
    rw [hx] at hp'
    linarith

/-- **Exercise 12.BB.3, two plants and no entry** (MWG, p. 435). A monopolist with plants at
both ends earns at most `(v − t/2 − c)M`; the prices `v − t/2` at both ends attain it and are
the unique optimal prices. -/
theorem exercise_12_BB_3_monopoly_two {v t M c : ℝ} (ht : 0 < t) (hM : 0 < M)
    (hv : c + 3 * t < v) :
    (∀ p q, (p - c) * bb3D v t M p q + (q - c) * bb3D v t M q p ≤ (v - t / 2 - c) * M) ∧
    (v - t / 2 - c) * bb3D v t M (v - t / 2) (v - t / 2) +
      (v - t / 2 - c) * bb3D v t M (v - t / 2) (v - t / 2) = (v - t / 2 - c) * M ∧
    ∀ p q, (p - c) * bb3D v t M p q + (q - c) * bb3D v t M q p = (v - t / 2 - c) * M →
      p = v - t / 2 ∧ q = v - t / 2 := by
  -- per-plant bound: price at most `v − t·x` when the plant sells `x > 0`
  have hplant : ∀ p q, (p - c) * bb3Cl (min ((v - p) / t) ((t + q - p) / (2 * t))) ≤
      (v - c) * bb3Cl (min ((v - p) / t) ((t + q - p) / (2 * t))) -
        t * bb3Cl (min ((v - p) / t) ((t + q - p) / (2 * t))) ^ 2 := by
    intro p q
    rcases eq_or_lt_of_le (bb3Cl_nonneg (min ((v - p) / t) ((t + q - p) / (2 * t)))) with h | h
    · rw [← h]; ring_nf; exact le_rfl
    · have hx := (bb3Cl_le_of_pos h).trans (min_le_left _ _)
      rw [le_div_iff₀ ht] at hx
      nlinarith
  -- the two plants sell at most the whole market
  have hsum : ∀ p q, bb3Cl (min ((v - p) / t) ((t + q - p) / (2 * t))) +
      bb3Cl (min ((v - q) / t) ((t + p - q) / (2 * t))) ≤ 1 := by
    intro p q
    rcases eq_or_lt_of_le (bb3Cl_nonneg (min ((v - p) / t) ((t + q - p) / (2 * t)))) with h | h
    · rw [← h, zero_add]; exact bb3Cl_le_one _
    rcases eq_or_lt_of_le (bb3Cl_nonneg (min ((v - q) / t) ((t + p - q) / (2 * t)))) with h' | h'
    · rw [← h', add_zero]; exact bb3Cl_le_one _
    have h1 := (bb3Cl_le_of_pos h).trans (min_le_right _ _)
    have h2 := (bb3Cl_le_of_pos h').trans (min_le_right _ _)
    have e : (t + q - p) / (2 * t) + (t + p - q) / (2 * t) = 1 := by field_simp; ring
    linarith
  -- the slack identity
  have hslack : ∀ x0 x1 : ℝ,
      (v - t / 2 - c) - ((v - c) * x0 - t * x0 ^ 2 + ((v - c) * x1 - t * x1 ^ 2)) =
        t * (x0 - x1) ^ 2 / 2 + (1 - (x0 + x1)) * (v - c - t * (1 + (x0 + x1)) / 2) := by
    intro x0 x1; ring
  refine ⟨fun p q => ?_, ?_, fun p q hpq => ?_⟩
  · have h1 := hplant p q
    have h2 := hplant q p
    have h3 := hsum p q
    have hs := hslack (bb3Cl (min ((v - p) / t) ((t + q - p) / (2 * t))))
      (bb3Cl (min ((v - q) / t) ((t + p - q) / (2 * t))))
    have h0 := bb3Cl_nonneg (min ((v - p) / t) ((t + q - p) / (2 * t)))
    have h0' := bb3Cl_nonneg (min ((v - q) / t) ((t + p - q) / (2 * t)))
    have hpos : 0 ≤ (1 - (bb3Cl (min ((v - p) / t) ((t + q - p) / (2 * t))) +
        bb3Cl (min ((v - q) / t) ((t + p - q) / (2 * t))))) *
        (v - c - t * (1 + (bb3Cl (min ((v - p) / t) ((t + q - p) / (2 * t))) +
          bb3Cl (min ((v - q) / t) ((t + p - q) / (2 * t))))) / 2) :=
      mul_nonneg (by linarith) (by nlinarith)
    have hsq := mul_nonneg ht.le (sq_nonneg (bb3Cl (min ((v - p) / t) ((t + q - p) / (2 * t))) -
      bb3Cl (min ((v - q) / t) ((t + p - q) / (2 * t)))))
    unfold bb3D
    nlinarith
  · have e : min ((v - (v - t / 2)) / t) ((t + (v - t / 2) - (v - t / 2)) / (2 * t)) = 1 / 2 := by
      rw [show (v - (v - t / 2)) / t = 1 / 2 by field_simp; ring,
        show (t + (v - t / 2) - (v - t / 2)) / (2 * t) = 1 / 2 by field_simp; ring, min_self]
    unfold bb3D
    rw [e, bb3Cl_of_mem (by norm_num) (by norm_num)]
    ring
  · set x0 := bb3Cl (min ((v - p) / t) ((t + q - p) / (2 * t))) with hx0
    set x1 := bb3Cl (min ((v - q) / t) ((t + p - q) / (2 * t))) with hx1
    have h1 := hplant p q
    have h2 := hplant q p
    rw [← hx0] at h1
    rw [← hx1] at h2
    have h3 : x0 + x1 ≤ 1 := hsum p q
    have hs := hslack x0 x1
    have h0 : 0 ≤ x0 := bb3Cl_nonneg _
    have h0' : 0 ≤ x1 := bb3Cl_nonneg _
    have hpq' : (p - c) * x0 + (q - c) * x1 = v - t / 2 - c := by
      unfold bb3D at hpq
      rw [← hx0, ← hx1] at hpq
      have : M * ((p - c) * x0 + (q - c) * x1) = M * (v - t / 2 - c) := by linarith
      exact mul_left_cancel₀ hM.ne' this
    have hA : 0 ≤ (1 - (x0 + x1)) * (v - c - t * (1 + (x0 + x1)) / 2) :=
      mul_nonneg (by linarith) (by nlinarith)
    have hB : 0 ≤ t * (x0 - x1) ^ 2 / 2 := by positivity
    have hA0 : (1 - (x0 + x1)) * (v - c - t * (1 + (x0 + x1)) / 2) = 0 := by linarith
    have hB0 : t * (x0 - x1) ^ 2 / 2 = 0 := by linarith
    have hs1 : x0 + x1 = 1 := by
      rcases mul_eq_zero.1 hA0 with h | h
      · linarith
      · nlinarith
    have hx01 : x0 = x1 := by
      have : (x0 - x1) ^ 2 = 0 := by
        have := mul_eq_zero.1 (show t * (x0 - x1) ^ 2 = 0 by linarith)
        rcases this with h | h
        · linarith
        · exact h
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
      linarith
    have hx0v : x0 = 1 / 2 := by linarith
    have hx1v : x1 = 1 / 2 := by linarith
    rw [hx0v] at h1
    rw [hx1v] at h2
    rw [hx0v, hx1v] at hpq'
    constructor <;> linarith

/-- **Exercise 12.BB.3, one plant each at opposite ends** (MWG, p. 435; Example 12.C.2): the
unique price equilibrium is `c + t` at both ends, each firm earning `tM/2`. -/
theorem exercise_12_BB_3_duopoly {t M c : ℝ} (ht : 0 < t) (hM : 0 < M) :
    IsLCNash t M c (c + t) (c + t) ∧ lcProfit t M c (c + t) (c + t) = t * M / 2 ∧
    ∀ p1 p2, IsLCNash t M c p1 p2 → p1 = c + t ∧ p2 = c + t := by
  obtain ⟨h1, _, h3, h4⟩ := example_12_C_2 (c := c) ht hM
  exact ⟨h1, h3, h4⟩

/-- I's overall payoff with one plant, when E enters at the far end iff that is strictly
profitable (`F < tM/2`). -/
noncomputable def bb3PayOne (v t M c F : ℝ) : ℝ :=
  if F < t * M / 2 then t * M / 2 - F else (v - t - c) * M - F

/-- I's overall payoff with two plants (E stays out). -/
noncomputable def bb3PayTwo (v t M c F : ℝ) : ℝ := (v - t / 2 - c) * M - 2 * F

/-- **Exercise 12.BB.3, the equilibrium** (MWG, p. 435). With `t, M, F > 0` and `v > c + 3t`, and
the subgame values above: (i) against two plants E stays out (`0 > 0 − F`, its operating profit
next to an I plant being `0`); (ii) against one plant E's best location is the far end
(`tM/2 − F > 0 − F`), and E enters iff `F < tM/2`; (iii) if `F < tM/2`, I builds two plants
(`bb3PayTwo > bb3PayOne`) and E stays out, prices `v − t/2`; (iv) if `F > tM/2`, I builds one
plant (`bb3PayOne > bb3PayTwo`) and E stays out, price `v − t` (entry is blockaded). -/
theorem exercise_12_BB_3 {v t M c F : ℝ} (ht : 0 < t) (hM : 0 < M) (hv : c + 3 * t < v)
    (hF : 0 < F) :
    0 - F < 0 ∧ 0 - F < t * M / 2 - F ∧
    (F < t * M / 2 → 0 < t * M / 2 - F ∧ bb3PayOne v t M c F < bb3PayTwo v t M c F) ∧
    (t * M / 2 < F → t * M / 2 - F < 0 ∧ bb3PayTwo v t M c F < bb3PayOne v t M c F) := by
  have htm : 0 < t * M := mul_pos ht hM
  refine ⟨by linarith, by linarith, fun h => ⟨by linarith, ?_⟩, fun h => ⟨by linarith, ?_⟩⟩
  · unfold bb3PayOne bb3PayTwo
    simp only [h, ↓reduceIte]
    nlinarith
  · unfold bb3PayOne bb3PayTwo
    simp only [not_lt.2 h.le, ↓reduceIte]
    nlinarith

/-- Total transport cost with one plant at an end serving everyone: `M∫₀¹ tz dz = tM/2`. -/
theorem bb3_transport_one (t M : ℝ) : M * ∫ z in (0 : ℝ)..1, t * z = t * M / 2 := by
  rw [intervalIntegral.integral_const_mul, integral_id]; ring

/-- Total transport cost with plants at both ends, each consumer using the nearer plant:
`M∫₀¹ t·min{z, 1 − z} dz = tM/4`. -/
theorem bb3_transport_two (t M : ℝ) : M * ∫ z in (0 : ℝ)..1, t * min z (1 - z) = t * M / 4 := by
  have hc : Continuous (fun z : ℝ => t * min z (1 - z)) :=
    continuous_const.mul (continuous_id.min (continuous_const.sub continuous_id))
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 1 / 2)
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  have h1 : ∫ z in (0 : ℝ)..1 / 2, t * min z (1 - z) = ∫ z in (0 : ℝ)..1 / 2, t * z := by
    apply intervalIntegral.integral_congr
    intro z hz
    rw [Set.uIcc_of_le (by norm_num)] at hz
    simp only
    rw [min_eq_left (by linarith [hz.2])]
  have h2 : ∫ z in (1 / 2 : ℝ)..1, t * min z (1 - z) = ∫ z in (1 / 2 : ℝ)..1, t * (1 - z) := by
    apply intervalIntegral.integral_congr
    intro z hz
    rw [Set.uIcc_of_le (by norm_num)] at hz
    simp only
    rw [min_eq_right (by linarith [hz.1])]
  rw [h1, h2, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_id, intervalIntegral.integral_sub intervalIntegrable_const
      intervalIntegral.intervalIntegrable_id, integral_id, intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

/-- Total surplus with every consumer served: gross value minus production, transport and plant
costs, `(v − c)M − T − nF`. -/
noncomputable def bb3Welfare (v M c T F : ℝ) (n : ℕ) : ℝ := (v - c) * M - T - n * F

/-- **Exercise 12.BB.3, welfare comparisons** (MWG, p. 435). (i) With no entrant, a monopolist
builds two plants iff `F < tM/2` (`bb3PayTwo > (v − t − c)M − F`), the same choice as in the
equilibrium with an entrant, so the outcome and total surplus coincide. (ii) If I may build
only one plant and `F < tM/2`, E enters at the far end; total surplus is the same as in the
equilibrium (two plants at the ends, transport cost `tM/4`), while consumer surplus is higher
by `M(v − c − 3t/2) > 0` (prices `c + t` instead of `v − t/2`). -/
theorem exercise_12_BB_3_welfare {v t M c F : ℝ} (ht : 0 < t) (hM : 0 < M) (hv : c + 3 * t < v) :
    ((v - t - c) * M - F < bb3PayTwo v t M c F ↔ F < t * M / 2) ∧
    bb3Welfare v M c (t * M / 4) F 2 = (v - t / 2 - c) * M - 2 * F + t * M / 4 ∧
    bb3Welfare v M c (t * M / 4) F 2 = (t * M / 2 - F) + (t * M / 2 - F) +
      (M * (v - (c + t)) - t * M / 4) ∧
    (M * (v - (c + t)) - t * M / 4) - (M * (v - (v - t / 2)) - t * M / 4) =
      M * (v - c - 3 * t / 2) ∧
    0 < M * (v - c - 3 * t / 2) := by
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, ?_, ?_, by ring, mul_pos hM (by linarith)⟩
  · unfold bb3PayTwo at h; nlinarith
  · unfold bb3PayTwo; nlinarith
  · unfold bb3Welfare; push_cast; ring
  · unfold bb3Welfare; push_cast; ring

/-- A proved instance of the hypotheses of the Exercise 12.BB.3 theorems in both regimes:
`t = M = 1`, `c = 0`, `v = 4 > c + 3t`, and `F = 1/4 < tM/2` (two plants) or `F = 1 > tM/2`
(one plant). -/
theorem exercise_12_BB_3_instance :
    (0 : ℝ) < 1 ∧ (0 : ℝ) + 3 * 1 < 4 ∧ (0 : ℝ) < 1 / 4 ∧ (1 : ℝ) / 4 < 1 * 1 / 2 ∧
    (1 : ℝ) * 1 / 2 < 1 := by
  norm_num

end MWG.MarketPower
