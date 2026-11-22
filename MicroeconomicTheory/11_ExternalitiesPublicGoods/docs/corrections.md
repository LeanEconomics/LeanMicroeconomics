# Corrections and departures

Each item states what MWG prints, what is proved, and the Lean names. Page references are to
the printed book.

1. **(11.D.1), p. 365.** MWG prints `πⱼ(hⱼ*) ≤ 0, with equality if hⱼ* > 0`. The condition is
   the first-order condition on the derivative, `πⱼ'(hⱼ*) ≤ 0` (a misprint; the page image shows
   no prime). Proved: `Multilateral.eq_11_D_1`.

2. **"depletable" for "nondepletable", p. 367.** "Purely market-based solutions ... are unlikely
   to work in the case of a depletable externality" refers, by the preceding argument, to a
   *nondepletable* externality (for depletable ones the text shows the market works:
   `Multilateral.deplMarket_optimal`). The nondepletable statements are
   `Multilateral.nondepl_excess`, `Multilateral.eq_11_D_6`.

3. **"The solution" of (11.E.1), p. 369.** MWG asserts that the consumer's problem
   `max_T (1 - G(T))(T - c)` has a solution `T_c*`, and that `T_c* > c`. Under the text's
   assumptions (density `g > 0` on `b > 0`) a solution need not exist: for `G(b) = b/(1 + b)`
   every demand is beaten by a larger one (`eq_11_E_1_no_solution`). Corrected statement: every
   solution, when one exists, satisfies `T_c* > c`, and then the firm rejects with positive
   probability although `b > c` (`eq_11_E_1_gt`, `eq_11_E_1_inefficient`). With exponential
   benefits the solution is `T* = c + 1` (`eq_11_E_1_exponential`).

4. **Example 11.AA.1, p. 375: `α ∈ [0, 1]`.** At `α = 1` firm 2's profit `(h^β - 1)z` is
   unbounded for `h > 1`, so there is no derived profit function `γ h^{β/(1-α)}` (the exponent is
   undefined): `example_11_AA_1_alpha_one`. The formula holds for `0 < α < 1` with
   `γ = (1 - α)α^{α/(1-α)}` (`example_11_AA_1`) and at `α = 0` with `γ = 1`
   (`example_11_AA_1_alpha_zero`).

5. **Example 11.AA.3, p. 377.** MWG says the outcome `h = 1` is "implemented by setting a tax rate
   on firm 1 of `t = 0`" and "satisfies both the first-order and second-order conditions". With
   `t = 0` firm 1 is indifferent among all `h ≥ 1` (`example_11_AA_3_local`), and aggregate surplus
   is not differentiable at `h = 1` (left derivative `1`, right derivative `0`:
   `example_11_AA_3_kink`). What is true: `h = 1` is a (weak) local maximum and surplus exceeds its
   value exactly for `h < 1/2` (`example_11_AA_3_local`); the optimum `h = 0` and the tax `t > 1`
   are as printed (`example_11_AA_3_optimum`).

6. **Exercise 11.B.2(c), p. 379.** As printed (comparative statics in `w₂` "for a given `ū₂`"),
   the claim is false: with `ū₂` fixed, the Pareto optimal levels of `h` do not depend on `w₂` at
   all, only the transfer `T° = ζ(h°) - w₂` does (`exercise_11_B_2c_invariant`). Counterexample
   with a normal externality demand: `φ₁(h) = -h²/2`, `φ₂(h, z) = zh`, `ū₂ = 1`; demand is
   `w/(2p)` (wealth effect `1/(2p) > 0`), yet `h° = 1` for every `(w₁, w₂)`
   (`exercise_11_B_2c_counterexample`). Corrected statement: holding consumer 1's utility fixed
   (the extra wealth goes to consumer 2), `dh°/dw₂` satisfies
   `h°'(D + φ₁''φ₂_w) + (φ₂ₕ_w - p̄φ₂_ww) = 0` (`exercise_11_B_2c_corrected`) and has the sign of
   the wealth effect `∂h/∂w` of the demand (`exercise_11_B_2b`) when `D < 0` and `φ₁''φ₂_w < 0`
   (`exercise_11_B_2c_sign`). The wealth effect must be evaluated where demand at `p̄` equals
   `h°`, i.e. at wealth `z° + p̄h°` (consumer 2's final numeraire plus her expenditure on `h`),
   not at the printed `w̄₂ = w₂ - T°`.

7. **Exercise 11.D.6(a), p. 380.** "When `I > 1` we have `θ < 1` in equilibrium" fails at `I = 2`.
   In the exact model (integer coalition size `k`, a member compares staying with leaving, a
   non-member joining with staying out), staying is optimal iff `k ≤ 2` and staying out iff
   `k ≥ 1` (`LandModel.exercise_11_D_6_stay`, `LandModel.exercise_11_D_6_join`,
   `LandModel.membershipEq_iff`), so with `I = 2` the full coalition `θ = 1` is an equilibrium
   (`LandModel.exercise_11_D_6a`). The continuous approximation (indifference of the marginal
   member) gives `θ = min(1, 2/I)`, again `1` at `I = 2`. Corrected statement: for `I = 1` the
   optimum results; for `I ≥ 3` every equilibrium has `θ ≤ 2/I < 1` and too much externality
   (`LandModel.exercise_11_D_6a`); part (b) holds as printed (`LandModel.exercise_11_D_6b`,
   `LandModel.exercise_11_D_6b_limit`).

8. **Exercise 11.D.7(a), p. 381.** "In any equilibrium both neighborhoods must be occupied"
   depends on the prestige assigned to an empty neighborhood. Everyone in `A` is never an
   equilibrium (`exercise_11_D_7a_allA`); everyone in `B` is not one when a lone mover to `A`
   obtains her own prestige (`exercise_11_D_7a_allB`), but it is an equilibrium if the empty
   neighborhood `A` has prestige `0` (`exercise_11_D_7a_counterexample`).

9. **Exercise 11.E.7, p. 382.** The tax whose total is `φ(h, η̄)` does not work; the correct
   schedule is `-φ(h, η̄)` (plus any constant, e.g. `φ(0, η̄) - φ(h, η̄) ≥ 0`), which makes the firm
   maximize aggregate surplus for every `θ` (`exercise_11_E_7`). Counterexample to the printed
   schedule: `π(h, θ) = θh - h²/2`, `φ(h) = -h`; the firm chooses `θ + 1`, the optimum is
   `max(θ - 1, 0)` (`exercise_11_E_7_printed`).

10. **Footnote 10, public bad, p. 362.** "The inequalities reverse and `q° < q*`" needs `q* > 0`
    (if `q* = 0`, `q° ≥ 0 = q*`). Proved with that hypothesis: `PublicGood.public_bad_excess`.

11. **Exercise 11.D.1, p. 380 ("compare it with the Pareto optimal symmetric outcome").** There is
    no Pareto optimal symmetric outcome with positive hours: halving everyone's hours makes everyone
    strictly better off (`exercise_11_D_1_pareto`), so the symmetric payoff `φ(1) - h²/2` has
    supremum `φ(1)`, approached as `h → 0`. The equilibrium is characterized as
    `h² = φ'(1)(n - 1)/n` (`exercise_11_D_1`); the assumption `φ'(0+) = ∞` is not needed.

Departures in modelling (not errors of the book):

12. **Differentiability and concavity.** MWG assumes `φᵢ'' < 0` (and `c'' > 0`). We assume
    differentiable `φᵢ` with strictly decreasing derivative on `[0, ∞)`, which `φᵢ'' < 0` implies
    (`strictAntiOn_of_second_deriv_neg`); the results therefore hold slightly more generally.
    Multivariable concavity (Exercises 11.B.5, 11.D.2, 11.D.4) is `ConcaveOn`/`ConvexOn` with a
    Fréchet derivative given by its partials.

13. **Footnote 3, p. 353.** We keep the nonnegativity of all goods and assume wealth covers the
    optimal purchases of the non-numeraire goods; then derived utility is `φ(p, h) + w`
    (`footnote_3`).

14. **Exercise 11.E.1-11.E.2.** As in the text's linear-quadratic analysis, the firm's level
    under a tax, `(β - t + θ)/b`, is not truncated at `0`; expectations are integrals against a
    probability measure with the stated moments (instance: `exercise_11_E_moments_instance`).

15. **Exercise 11.D.5.** `f(0) = 0` (no boats, no fish) is assumed; MWG leaves it implicit.

16. **Exercise 11.D.3.** The conditions `c_q + J c_Q > 0` and the `n = 1` second-order condition
    are not used; the comparison needs only that `P` decreases, `MSC = c_q + Jc_Q` increases (MWG's
    `n = J` condition, `exercise_11_D_3_msc_deriv`) and `c_Q < 0`.

17. **Exercise 11.C.3.** The derivatives of welfare and of the government budget in the taxes and
    the public good (from the consumers' first-order conditions, the envelope argument of
    Exercise 10.E.3) are taken as data; the optimality conditions are then derived with Mathlib's
    Lagrange multiplier theorem (`exercise_11_C_3`). The instance (`exercise_11_C_3_instance`) is
    degenerate (zero taxes).

18. **Section 11.E, Groves-Clarke budget balance (small type, p. 374).** "We generally cannot
    achieve budget balance" is proved within the class of mechanisms of Exercise 11.E.4 (Groves
    transfers plus arbitrary payments depending on the other's announcement):
    `gc_no_budget_balance`, `gc_surplus_somewhere`. That every dominant-strategy efficient
    mechanism is of this form (Green-Laffont) is Chapter 23 material. Footnote 18 cites the
    Myerson-Satterthwaite theorem, which the book states and proves in Chapter 23; it is not
    restated here.
