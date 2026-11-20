# Corrections

Departures from the printed text of MWG Chapter 7, checked against the page images. None of
the chapter's claims is false as printed; the items below are imprecisions, encodings and
places where the formalization proves more than the text states.

1. **Item (iv), p. 227: the domain of `H(·)`.** MWG write `H : 𝒳 → ℋ`, "assigning each
   decision node" an information set, and say the information sets "form a partition of `𝒳`".
   Information sets contain only decision nodes, so they partition `𝒳 \ T`, not `𝒳`. Here
   `info` is a total function whose values off the decision nodes play no role, and
   `infoSet_partition` proves that the information sets are nonempty and partition the decision
   nodes.
2. **Item (iii), p. 227: `α` at the initial node.** MWG's `α` is defined on `𝒳 \ {x₀}`.
   `GameTree.act` is total; its value at `x₀` is never used (`act_inj` only compares nodes
   with a predecessor). In a history tree the action is the head of the history.
3. **Representation of the tree, p. 227.** MWG's nodes form an abstract finite set with a
   predecessor function. `ExtensiveForm` identifies each node with its history (actions from
   `x₀`, most recent first). This is not a restriction: `GameTree` is MWG's abstract definition
   and `GameTree.hist_root`, `hist_of_pred`, `hist_injective`, `historyNodes_tail_mem` and
   `cons_mem_historyNodes_iff` show that every finite MWG tree is a history tree up to renaming
   its nodes, while `ExtensiveForm.toGameTree` and `gameTree_of_history` go the other way.
4. **Behaviour strategies, Definition 7.E.2, p. 233.** MWG define `λ_i(a, H)` only for
   `a ∈ C(H)`. Here a behaviour strategy is a function on all actions that is zero off `C(H)`
   (`IsBehaviorStrategy`), which is the same object.
5. **Kuhn's theorem, p. 233: weaker hypotheses than "perfect recall".** MWG state the
   equivalence for games of perfect recall. The formalization proves each direction under the
   part of perfect recall it needs: behaviour to mixed (`kuhn_behavior_to_mixed`) assumes only
   condition (i) of footnote 1 (no information set is crossed twice on a path), and mixed to
   behaviour (`kuhn_mixed_to_behavior`) assumes only condition (ii) for the player concerned.
   `kuhn_theorem` is the printed statement. This is what Exercise 7.E.1(d) asks about: in the
   merged game condition (ii) fails, (b) still holds and (c) fails (`exercise_7_E_1d`, with
   the counterexample `ex7E1Sigma = ½ (M, x) + ½ (R, y)`).
6. **Realization equivalence, p. 233 and Exercise 7.E.1(b).** MWG require the same outcome
   distribution "for any strategies, mixed or behavior, that might be played by i's rivals".
   `RealizationEquivalent` requires it against arbitrary move probabilities of the rivals at
   their information sets (covering pure and behaviour strategies, and more), and
   `realizationEquivalent_mixed_rivals` / `kuhn_mixed_rivals` cover rivals' mixed strategies.
7. **Private signal, small type p. 232.** MWG take `θ_i` uniform on `[0, 1]`.
   `mixedStrategy_signal` partitions `[0, 1)`, which differs from `[0, 1]` by a null set, into
   measurable sets of Lebesgue measure `σ(s)`, on which the plan plays `s`.
8. **Unspecified payoffs.** Figure 7.C.4 and Figure 7.Ex.1 give no payoffs; the formal games
   (`figure7C4a`, `figure7C4b`, `exercise7E1`, `exercise7E1Merged`) set them to `0`. None of the
   claims about them depends on payoffs.
9. **Exercise 7.C.1, p. 233.** The exercise asks for "an" extensive form. `exercise7C1` draws
   Mr. Thomas first and Mr. Schelling at one information set; by Example 7.C.4 the reversed
   order is equally valid (`matchingPenniesReversed` illustrates this for Matching Pennies).
10. **Tick-Tack-Toe, Figure 7.C.2, p. 223.** The figure shows part of the tree. `tickTackToe`
   is the whole tree: a node is a sequence of distinct squares in which no earlier position had
   three in a row. The claims proved are those the text makes (perfect information,
   alternating moves, zero-sum payoffs, different move orders give different nodes).
