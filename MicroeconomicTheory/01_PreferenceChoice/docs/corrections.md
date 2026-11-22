# Corrections and departures

No printed statement in MWG Chapter 1 was found to be false. The following are the
places where the Lean statement departs from, or makes precise, the printed one.

1. **Exercise 1.B.4, p. 15 (hypothesis dropped).** The book assumes `≿` rational. The
   proof that `u` represents `≿` uses only the two hypotheses on `u`, so
   `exercise_1_B_4` omits rationality (it then follows from `proposition_1_B_2`).
2. **Exercise 1.C.1, p. 15 (generality).** The book's `𝓑` is exactly
   `{{x,y},{x,y,z}}`. `exercise_1_C_1` holds for any choice structure on any `X` whose
   family contains these two budgets, and `x, y, z` need not be distinct.
3. **Proposition 1.D.2, p. 13 (uniqueness).** "The only preference relation that does so":
   `proposition_1_D_2_unique` shows that any relation, rational or not, with
   `C(B) = C*(B, ≿)` on `𝓑` equals `≿*`. Hypothesis (ii) is read as "all nonempty
   subsets with at most three elements" (`ContainsSmallSubsets`, stated with
   `Set.encard ≤ 3`); budget sets are nonempty by definition, so this is the book's
   hypothesis. `X` is arbitrary, as in the book.
4. **Exercise 1.D.1, p. 15 (second sentence).** The uniqueness claim is for rationalizing
   relations in the sense of Definition 1.D.1, i.e. rational ones (`exercise_1_D_1b`);
   reflexivity, which comes from completeness, settles the diagonal.
5. **Exercise 1.D.5, p. 16 (encoding and part (c)).** The six strict preference relations on
   `X = {x,y,z}` are encoded as the permutations of `Fin 3` read as rankings
   (`rankPrefers`); `rankPrefers_strictTotal` and `rankPrefers_injective` show these are
   six distinct strict total orders. Part (c) asks for "the" `α` at which the function
   switches; there are two: the function is rationalizable exactly for
   `1/3 ≤ α ≤ 2/3` (`cyclicChoice_rationalizable_iff`, `exercise_1_D_5c`).
