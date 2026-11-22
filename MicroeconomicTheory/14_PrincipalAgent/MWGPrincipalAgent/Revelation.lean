/-
Copyright (c) 2026 KrepsFoundations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KrepsFoundations contributors
-/
import MWGPrincipalAgent.Screen

/-!
# The revelation principle and hybrid models

MWG, Section 14.C, pp. 492-494 (Proposition 14.C.2), and Section 14.D, pp. 500-502.

* `proposition_14_C_2`: the revelation principle. For any contract (a set of messages or choices
  `Msg` for the manager and an outcome for each) and any optimal behaviour of the manager, the
  direct mechanism that assigns to each announced state the outcome the manager would have chosen
  in that state is truthful and yields the same outcome in every state.
* `revelation_example`: the example of p. 493: a compensation schedule `w(π)` with the effort left
  to the manager.
* `hybrid_revelation`: Section 14.D (Myerson 1982): mechanisms whose outcome after a message is a
  hidden-action contract can be replaced by truthful and obedient direct mechanisms.
* `hybrid_forcing`: Section 14.D, p. 502: with deterministic profits a "forcing" scheme implements
  any wage-effort pair (with a finite penalty instead of MWG's wage of `-∞`).
* `hybrid_change_of_variables`: p. 502: with forcing contracts the hybrid model is the hidden
  information model with effort variable `π`, disutility `g(ẽ(π), θ)` and profit function `π`.
-/

namespace MWG.PrincipalAgent

open Set

/-- **Proposition 14.C.2 (the revelation principle)** (MWG, p. 493). Let the manager in state `θ`
choose `σ θ` optimally among the messages/choices `Msg` allowed by a contract with outcome `o`.
The direct revelation mechanism `d θ̂ = o (σ θ̂)` makes truthful announcement optimal in every
state and yields exactly the same outcome in every state. -/
theorem proposition_14_C_2 {Θ Msg Out : Type*} (o : Msg → Out) (U : Θ → Out → ℝ)
    (σ : Θ → Msg) (hσ : ∀ θ m, U θ (o m) ≤ U θ (o (σ θ))) :
    ∃ d : Θ → Out, (∀ θ θ', U θ (d θ') ≤ U θ (d θ)) ∧ ∀ θ, d θ = o (σ θ) :=
  ⟨fun θ => o (σ θ), fun θ θ' => hσ θ (σ θ'), fun _ => rfl⟩

/-- **Proposition 14.C.2, "without loss"** (MWG, p. 493): whatever the owner's payoff from an
outcome in a state, the truthful direct mechanism gives the owner the same payoff in every state as
the original contract. -/
theorem proposition_14_C_2_payoff {Θ Msg Out : Type*} (o : Msg → Out) (U : Θ → Out → ℝ)
    (V : Θ → Out → ℝ) (σ : Θ → Msg) (hσ : ∀ θ m, U θ (o m) ≤ U θ (o (σ θ))) :
    ∃ d : Θ → Out, (∀ θ θ', U θ (d θ') ≤ U θ (d θ)) ∧ ∀ θ, V θ (d θ) = V θ (o (σ θ)) := by
  obtain ⟨d, h1, h2⟩ := proposition_14_C_2 o U σ hσ
  exact ⟨d, h1, fun θ => by rw [h2]⟩

/-- **The example of p. 493.** The owner offers a compensation schedule `w(π)` and leaves the
effort to the manager; in state `θ` the manager chooses `e θ ≥ 0` maximizing
`v(w(π(e)) - g(e, θ))`. The revelation mechanism assigning `[w(π(e θ̂)), e θ̂]` to the announcement
`θ̂` is truthful. -/
theorem revelation_example {Θ : Type*} (w prof v : ℝ → ℝ) (g : ℝ → Θ → ℝ) (e : Θ → ℝ)
    (he : ∀ θ, 0 ≤ e θ)
    (hopt : ∀ θ e', 0 ≤ e' → v (w (prof e') - g e' θ) ≤ v (w (prof (e θ)) - g (e θ) θ)) :
    ∀ θ θ', v (w (prof (e θ')) - g (e θ') θ) ≤ v (w (prof (e θ)) - g (e θ) θ) :=
  fun θ θ' => hopt θ (e θ') (he θ')

/-- **Section 14.D, the revelation principle for hybrid models** (MWG, p. 501; Myerson 1982). In a
general mechanism the manager sends a message `m` and then takes a hidden action `a`, obtaining
utility `U θ m a`. If `(σ θ, α θ)` is optimal in state `θ`, the direct mechanism that, after the
announcement `θ̂`, offers the contract of message `σ θ̂` and recommends the action `α θ̂` makes the
manager willing to be truthful and obedient. -/
theorem hybrid_revelation {Θ Msg Act : Type*} (U : Θ → Msg → Act → ℝ) (σ : Θ → Msg)
    (α : Θ → Act) (hopt : ∀ θ m a, U θ m a ≤ U θ (σ θ) (α θ)) :
    ∀ θ θ' a, U θ (σ θ') a ≤ U θ (σ θ) (α θ) :=
  fun θ θ' a => hopt θ (σ θ') a

/-- **Forcing contracts** (MWG, Section 14.D, p. 502). With deterministic, strictly increasing
profits `π(e)`, strictly increasing `v`, and `g(e, θ) ≥ 0` for `e ≥ 0`, the scheme paying `ŵ` if
profits are `π(ê)` and `ŵ - K` otherwise (with `K` above `g(ê, θ)` for the states considered)
makes `ê` the unique optimal effort in each of these states. (MWG uses a wage of `-∞`; any
finite penalty `K > max g(ê, θ)` suffices.) -/
theorem hybrid_forcing {Θ : Type*} (prof v : ℝ → ℝ) (hprof : StrictMono prof) (hv : StrictMono v)
    (g : ℝ → Θ → ℝ) (hg : ∀ e θ, 0 ≤ e → 0 ≤ g e θ) (what ehat K : ℝ)
    (S : Set Θ) (hK : ∀ θ ∈ S, g ehat θ < K) :
    let w : ℝ → ℝ := fun x => if x = prof ehat then what else what - K
    ∀ θ ∈ S, ∀ e, 0 ≤ e → e ≠ ehat → v (w (prof e) - g e θ) < v (w (prof ehat) - g ehat θ) := by
  intro w θ hθ e he hne
  have hne' : prof e ≠ prof ehat := hprof.injective.ne hne
  simp only [w, hne', ↓reduceIte]
  apply hv
  linarith [hg e θ he, hK θ hθ]

/-- **The hybrid model as a hidden-information model** (MWG, Section 14.D, p. 502). Suppose
profits are a deterministic function `π(e)` with an inverse `ẽ` on the relevant profit levels.
Writing a contract in terms of wage-profit pairs, the hidden-information program with effort
variable `π`, disutility `g̃(π, θ) = g(ẽ(π), θ)` and profit function `π ↦ π` has the same owner's
payoff and the same constraints as the program in terms of wage-effort pairs. -/
theorem hybrid_change_of_variables (P : Screen) (prof etil : ℝ → ℝ) (hpH : P.pH = prof)
    (hpL : P.pL = prof) (hinv : ∀ e, 0 ≤ e → etil (prof e) = e)
    (hpos : ∀ e, 0 ≤ e ↔ 0 ≤ prof e) (K : HIContract) (hH : 0 ≤ K.eH) (hL : 0 ≤ K.eL) :
    let P' : Screen := ⟨id, id, fun x θ => P.g (etil x) θ, P.θL, P.θH, P.lam, P.c⟩
    let K' : HIContract := ⟨K.wH, prof K.eH, K.wL, prof K.eL⟩
    P'.Pi K' = P.Pi K ∧ (P'.Feas K' ↔ P.Feas K) := by
  intro P' K'
  have h1 : etil (prof K.eH) = K.eH := hinv _ hH
  have h2 : etil (prof K.eL) = K.eL := hinv _ hL
  refine ⟨by simp [P', K', Screen.Pi, hpH, hpL], ?_⟩
  simp only [Screen.Feas, Screen.C1, Screen.C2, Screen.C3, Screen.C4, P', K', h1, h2,
    ← hpos]

end MWG.PrincipalAgent
