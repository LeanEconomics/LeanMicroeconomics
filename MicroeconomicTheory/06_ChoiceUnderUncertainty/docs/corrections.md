# Corrections

Departures from the printed text of MWG Chapter 6, checked against the page images.

1. **Money lotteries, p. 183.** MWG takes "all distribution functions over `[a, +∞)`" without
   stating integrability. Here a money lottery is a probability measure concentrated on a
   compact interval (`IsMoneyLottery`), so `∫ x dF` and `∫ u dF` exist for continuous `u`;
   Section 6.D's own restriction (`F(0) = 0`, `F(x̄) = 1`, `IsMWGDist`) is of this kind. The
   St. Petersburg discussion (`stPetersburg`) shows why unbounded supports need care.
2. **Expression (6.C.1), p. 184.** "The application of the expected utility theorem to
   outcomes defined by a continuous variable tells us … `U(F) = ∫ u dF`" is false under MWG's
   axioms (rationality, continuity in the sense of Definition 6.B.3, independence) on general
   distributions: ranking lotteries by the total mass of their atoms satisfies all three
   axioms but has no Bernoulli utility (`expectedUtility_6_C_1_counterexample`, using
   `atomicMass`). The integral form holds on finitely supported lotteries (Kreps
   `proposition_5_3`); on all Borel laws it needs weak continuity (Kreps Proposition 5.10).
3. **`r_A(x) = 4π'(0)`, p. 190.** MWG differentiates (6.C.4) assuming `π` differentiable. We
   prove `π(x, ε, u)/ε → r_A(x)/4` as `ε ↓ 0` for `u` twice continuously differentiable at `x`
   with `u'(x) > 0`, with no assumption on `π` (`arrowPratt_eq_four_probPremium_slope`).
4. **"Decreasing" in Definition 6.C.4 and Propositions 6.C.3-6.C.4, pp. 193-194.** Read as
   nonincreasing (`Antitone`). With the strict reading, Proposition 6.C.3(iii) fails for every
   degenerate risk (`x - c_x` is then constant), so the equivalence would be false.
5. **Example 6.C.2 continued, p. 192.** MWG assumes interior optima and differentiates under
   the integral. We prove, for continuous utilities and any optimum, that a more risk-averse
   investor never gains by investing more than `α₁*` (`invest_compare`), hence `α₂* ≤ α₁*` when
   `α₂*` is the unique optimum (`example_6_C_2_continued`); the same is used for Exercises
   6.C.8 and 6.C.11, which accordingly assume uniqueness of the relevant optimum.
6. **Exercise 6.C.12(a), p. 211.** "CRRA `ρ ≠ 1` iff `u(x) = βx^{1-ρ} + γ` with `β > 0`" is
   false for `ρ > 1`: such `u` are strictly decreasing, while `-1/x` is strictly increasing
   with constant relative risk aversion `2` (`exercise_6_C_12a_printed_counterexample`).
   Correct: `u(x) = βx^{1-ρ}/(1-ρ) + γ`, `β > 0` (`exercise_6_C_12a`). The domain is `x > 0`
   (at `x = 0` relative risk aversion is `0`).
7. **Exercise 6.C.12(c), p. 211.** `lim_{ρ→1} x^{1-ρ}/(1-ρ) = ln x` fails (at `x = 1` the
   expression is `1/(1-ρ)`; `exercise_6_C_12c_printed_counterexample`). Correct:
   `lim (x^{1-ρ} - 1)/(1-ρ) = ln x` (`exercise_6_C_12c`).
8. **Exercise 6.C.9(c), p. 211.** The strict inequality `E[v'(x+y)] > v'(x)` needs `y` not
   identically zero; for `y ≡ 0` it is an equality (`exercise_6_C_9c_degenerate`). Proved for
   nondegenerate `y` (`exercise_6_C_9c`).
9. **Exercise 6.C.9(d), p. 211.** With (weakly) decreasing `r_A` the conclusion is
   `-v'''/v'' ≥ -v''/v'`, with equality under constant absolute risk aversion
   (`exercise_6_C_9d_cara`); strict where `r_A' < 0`; `v''' > 0` holds in all cases
   (`exercise_6_C_9d`).
10. **Proposition 6.E.1, p. 203.** For arbitrary distribution functions in each state the
    statement contains the case `S = 1`, which is (6.C.1) and fails (correction 2). Proved, as
    in MWG's own proof, for state lotteries of finite support over an arbitrary outcome set
    (`proposition_6_E_1`).
11. **Proposition 6.F.1 and Exercise 6.F.1, pp. 206, 214.** The probabilities are unique only
    when the utility on money is nonconstant; under total indifference every probability
    vector works (`exercise_6_F_1_probabilities_not_unique`). Proved with the nonconstancy
    hypothesis (`exercise_6_F_1_probabilities`).
12. **Exercise 6.C.4(a), p. 210, and Example 6.C.3, p. 189.** "Increasing" is proved in the
    weak sense (`exercise_6_C_4a`); strict increase fails when some return is zero almost
    surely. Returns have compact support (correction 1).
13. **Exercise 6.C.15(a)-(b), p. 212.** The necessary conditions proved are: `x₁ > 0` optimal
    ⇒ `a < 1` or `b < 1` or `a = b = 1` (strictly increasing `u`, `0 < π < 1`); `x₂ > 0`
    optimal ⇒ `πa + (1-π)b > 1` (strictly concave increasing `u`, `a ≠ b`). Parts (d) and (f)
    are proved by implicit differentiation along a differentiable demand, assuming
    `u' > 0`, `u'' < 0`; they give strict signs.
14. **Exercises 6.C.17 and 6.C.19, pp. 212-213.** In 6.C.17 returns take finitely many positive
    values and the fraction in the risky asset lies in `[0,1]`; the CARA failure is shown by
    proving that optimal *amounts* are wealth-independent, so optimal fractions differ at
    different wealth levels when the amount problem has a unique positive solution. In
    6.C.19 joint normality is expressed through the moment generating function
    `E e^{t·z} = e^{t·μ + t'Vt/2}` (instantiated with Mathlib's `gaussianReal`).
15. **Proposition 6.D.2, p. 199.** Equal means are not needed for (iii) ⇒ (i)
    (`sosd_of_integralCondition`). (i) ⇒ (ii) is proved for arbitrary MWG distributions with
    equal means (`proposition_6_D_2_i_ii`); MWG's mean-preserving spread is formalized as a
    Markov kernel `H_x` with `∫ z dH_x(z) = 0` for every `x` and `G` the law of `x + z`
    (`IsMeanPreservingSpread`). No departure in the statement.
16. **Proposition 6.E.2, p. 204.** The book: continuity and the sure-thing axiom on `ℝ^S_+`
    with "at least three states" give an extended expected utility representation
    `∑_s u_s(x_s)`. This is false as printed: if only two states are essential (the others
    null), the sure-thing axiom only says that each of the two states' rankings is independent
    of the other, and the Thomsen condition can fail. Counterexample, for every `S ≥ 2`
    (including `S = 3`): `x ≿ x'` iff `V(x) ≥ V(x')` with `V(x) = x₁ + x₂ + min(x₁, x₂)`; it is
    rational, continuous and satisfies the sure-thing axiom, but `(0,4) ∼ (2,1)` and
    `(2,2) ∼ (1,4)` while `(0,2) ≺ (1,1)`, impossible for `f(x₁) + g(x₂)`
    (`proposition_6_E_2_false`, `thomsenPref_not_additive`, `thomsenPref_essential`). What is
    true (Debreu 1960) is the statement with at least three *essential* states
    (`proposition_6_E_2`, rationality made explicit as `RationalOn`, continuity as MWG's
    Definition 3.C.1 `PrefContinuous`, the sure-thing axiom on `ℝ^S_+` as `SureThingOn`); the
    `u_s` are then also continuous on `ℝ₊`. Not formalized: the remaining cases with at most
    one essential state, where a representation also exists.
