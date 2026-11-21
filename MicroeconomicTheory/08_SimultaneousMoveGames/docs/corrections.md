# Corrections

Departures from the printed text of MWG Chapter 8 and Appendix M.I, checked against the page
images. Items 1, 3, 5, 6, 7, 8, 9 and 10 are printed claims that are false as stated (each has a
counterexample theorem and a corrected statement); items 2, 4 and 11 are implicit assumptions
or encodings.

1. **Exercise 8.B.4 and p. 239: order independence needs finitely many strategies.** The text
   says the order of iterated deletion of strictly dominated strategies never matters. With
   infinitely many strategies this fails: in the one-player game with strategies `ℕ` and
   payoff `u(n) = n`, every strategy is strictly dominated, and the complete deletion processes
   "delete all but `0`" and "delete all but `1`" end at `{0}` and `{1}`
   (`exercise_8_B_4_infinite_counterexample`). `exercise_8_B_4` proves the claim for games with
   finitely many (nonempty) strategy sets, which is the setting of the chapter's examples.
2. **Proposition 8.D.2: the strategy sets must be nonempty.** If some `S_i` is empty there is no
   mixed strategy for player `i` and no mixed equilibrium (`no_mixedProfile_of_isEmpty`).
   `proposition_8_D_2` assumes `Nonempty (S_i)`, as MWG implicitly do.
3. **Footnote 5, p. 253: "a finite strategy set cannot be convex".** A one-point set is finite
   and convex (`footnote_8_5_singleton`). True statement: a finite convex set has at most one
   point (`footnote_8_5`).
4. **Bayesian games, p. 255: payoffs `u_i(s, θ)` instead of `u_i(s_i, s_{-i}, θ_i)`.**
   `BayesianGame` lets payoffs depend on the whole type profile, which contains MWG's case and
   is needed for Exercise 8.E.1 (an army's payoff depends on the rival's strength). Proposition
   8.E.1 is proved in this generality, with conditional expectations over `θ_{-i}` given `θ_i`
   (`proposition_8_E_1`), for finitely many types as in footnote 8. Example 8.E.2 (a continuum
   of types) is formalized type by type through condition (8.E.3), as in the text.
5. **Exercise 8.B.1: "a strictly dominant strategy iff `β = 0`".** The "if" direction holds
   (`exercise_8_B_1_dominant`: `h_i = max(α, 0)/(2w_i)`). The "only if" direction fails with a
   single firm (`exercise_8_B_1_one_firm`: then `∏_j h_j = h_1` and the maximizer of
   `(α + β)h - wh²` is dominant for any `β`) and when `α ≤ 0` and `β < 0`
   (`exercise_8_B_1_nonpositive`: `h_i = 0` is strictly dominant). It holds with at least two
   firms and `α > 0` (`exercise_8_B_1_only_if`).
6. **Exercise 8.B.2: two weakly dominant strategies are impossible under Definition 8.B.3.**
   Each would weakly dominate the other, requiring a strict inequality in both directions
   (`weaklyDominant_unique`); so (a) holds vacuously and (b) has no example. With the weaker
   notion "at least as good as every other strategy against every `s_{-i}`"
   (`AtLeastAsGoodAsAll`), (a) holds (`exercise_8_B_2a`) and (b) has an example
   (`exercise_8_B_2b`).
7. **Exercise 8.D.8: strictly quasiconvex payoffs do not force degenerate equilibria.** One
   player choosing `s ∈ [-1, 1]` with `u(s) = s²` (strictly convex, hence strictly quasiconvex):
   mixing `-1` and `1` with probability `½` each attains the maximal expected payoff `1` and is
   not degenerate (`exercise_8_D_8_counterexample`). Corrected statement: if a player's expected
   payoff is strictly concave in his own strategy on a convex strategy set, every finite mixture
   that is a best response is degenerate (`exercise_8_D_8`, by strict Jensen).
8. **Exercise 8.C.4(a): the printed entry `η + 4ε` at `(D, ℓ)` for `L`.** With it, `M` is a best
   response to the pure (degenerate independent) profile `(D, ℓ)` whenever `π ≥ η/2 + 4ε`, e.g.
   `π = 10, ε = η = 1` (`exercise_8_C_4a_printed_false`). With the symmetric entry `π + 4ε`,
   `M` is never a best response to independent randomizations (`exercise_8_C_4a`). Parts (b) and
   (c) hold for both entries (`exercise_8_C_4b`, `exercise_8_C_4c`).

9. **p. 245 (small type): with two players, rationalizable = iteratively undominated.** Under
   Definition 8.C.2 read literally (a conjecture is a profile of the rivals' *remaining* mixed
   strategies) this is false. In the 3 × 3 game `ratGap` nothing is strictly dominated, but row
   `a` is a best response only to `½L + ½R`, which is strictly dominated by `M` and removed in
   the first round; so `a` survives iterated strict dominance but is not rationalizable
   (`rationalizable_two_counterexample`). Footnote 1's claim that an optimal choice under a
   probabilistic conjecture is optimal under a deterministic one holds only if the compound
   profile may lie outside the remaining set. With probabilistic conjectures (the compound
   profile is a convex combination of remaining strategies, `RationalizableConv`) the equivalence
   holds for pure strategies in two-player games, both directions (`rationalizableConv_iff_two`).
10. **Exercise 8.B.3 with one bidder.** With `I = 1` every bid pays `v_1` and no bid is weakly
   dominant (`exercise_8_B_3_one_bidder`); the claim holds with at least two bidders
   (`exercise_8_B_3`).
11. **Exercise 8.E.3: interior condition.** The closed-form BNE `q_t = (2a - 3c_t + c̄)/(6b)`
   requires `q_H ≥ 0`, i.e. `3c_H ≤ 2a + c̄`; `exercise_8_E_3` assumes it and proves the BNE is
   unique. Without it the high-cost type's output is `0` (the general best reply is
   `max((a - c_t - b E[q_j])/(2b), 0)`, `bayesCournot_isBNE_iff`). Exercise 8.B.5 likewise
   assumes `a > c` and `b > 0`, and Exercise 8.E.1 `M > 0`, `0 < s < w` (implicit in the text).

Encodings that are not departures: rivals' profiles `s_{-i}` are full profiles whose `i`-th
coordinate is ignored; the mixed extension's strict and weak domination quantify over profiles
of the rivals' mixed strategies, and the pure tests of p. 240 are theorems
(`mixedStrictlyDominates_iff_pure`, `mixedWeaklyDominates_iff_pure`); Proposition 8.D.3 is
proved for strategy sets in arbitrary real normed spaces (`nash_exists_of_quasiconcave`), with
the Euclidean statement as `proposition_8_D_3`; Kakutani's theorem uses MWG's upper
hemicontinuity (Definition M.H.3, from Chapter 3). Exercises 8.B.5 and 8.D.3 use the maximal
deletion process / dollar bids `ℕ`; Exercise 8.E.2 is formalized type by type, like
Example 8.E.2, with ties of probability zero (`fpTie_zero`); in Exercise 8.D.5 vendors at the
same location split the market evenly.
