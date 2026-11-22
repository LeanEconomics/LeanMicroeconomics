# MWGEquilibriumTime

Formalization of Mas-Colell, Whinston and Green, *Microeconomic Theory*, Chapter 20,
"Equilibrium and Time", pp. 732-786 (Sections 20.A-20.I), with Mathematical Appendix Section
M.N, "Dynamic Programming" (pp. 968-970), and the chapter's exercises: discounted utility,
stationarity, separability and recursive utility (20.B); intertemporal production, efficiency,
Malinvaud prices, Proposition 20.C.1 and the smooth-case construction of supporting prices from
short-run efficiency (20.C); the one-consumer equilibrium, transversality, the first-order
characterization of utility maximization, the planning problem with existence, uniqueness and
both welfare theorems, the Euler equations, Proposition 20.D.7, policy and value functions
(20.D); stationary paths, interest rates, golden rules and the efficiency of the golden rule
(20.E); dynamics, contractions and monotone policies (20.F); several consumers, the first
welfare theorem and the Negishi representative consumer (20.G); overlapping generations,
Propositions 20.H.1-20.H.2 and the nominal asset (20.H); short-run demand and learning (20.I);
and Theorem M.N.1 with value function iteration (M.N). The `Closer` modules add Exercises
20.B.5 (uniqueness), 20.C.5(c), 20.G.2, 20.G.3(a)-(b) and 20.G.4, the efficiency of the multisector
golden rule, the optimality of the monetary steady state, the bubble characterization of optimal
nominal equilibria, OLG cycles of periods 2 and 3, and global tâtonnement stability. The audit
passed **321 theorems and 460 declarations across 21 modules**. Coverage, including the OPEN items, is in the
[source map](docs/source-map.md); departures from the printed text, among them the refutation
of Example 20.D.1(iii), the factor `δ` in (20.D.11), the reversed bound on `|ψ'|` on p. 762,
Exercise 20.F.2 on `ℝ_{++}`, and the recursive-utility aside after (20.B.3), are in
[corrections](docs/corrections.md).

This is a Lake project pinned to Lean and Mathlib `v4.34.0`. It imports (Lake `path`
requirement) MWG Chapter 15
(`MWGGeneralEquilibriumExamples`: the gradient inequalities `concave_le_fderiv` and
`concave_le_tangent`), Chapter 5 (`MWGProduction`: no free lunch, free disposal, efficiency and
Proposition 5.F.2, used for the smooth Malinvaud prices; reached through Chapter 15) and LeanEconomics (pinned `04deccaf63`:
the `DynamicProgramming` Bellman operator, value function and principle of optimality, used for
Section M.N). See [third-party notices](THIRD_PARTY_NOTICES.md).

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Utility](MWGEquilibriumTime/Utility.lean) | 30 | (20.B.1)-(20.B.3), comments (1)-(6), Exercises 20.B.1-20.B.5 |
| [Production](MWGEquilibriumTime/Production.lean) | 33 | Assumptions (i)-(iv), Examples 20.C.1-20.C.5, Definitions 20.C.1-20.C.3, Proposition 20.C.1, Exercises 20.C.1-20.C.5(a) |
| [Closer20C](MWGEquilibriumTime/Closer20C.lean) | 4 | Exercise 20.C.5(c): chain of intermediate goods, 2-efficient but not 3-efficient |
| [SmoothPrices](MWGEquilibriumTime/SmoothPrices.lean) | 14 | Smooth-case Malinvaud prices from 2-efficiency, Exercise 20.C.5(b) |
| [RamseySolowPrices](MWGEquilibriumTime/RamseySolowPrices.lean) | 11 | Examples 20.C.6-20.C.7, (20.C.1)-(20.C.2), Exercise 20.C.6 |
| [OneConsumer](MWGEquilibriumTime/OneConsumer.lean) | 23 | (20.D.1), Definitions 20.D.1-20.D.2, Propositions 20.D.1-20.D.2, Example 20.D.1, Exercises 20.D.1-20.D.4 |
| [Planning](MWGEquilibriumTime/Planning.lean) | 12 | (20.D.7), Propositions 20.D.3-20.D.6 |
| [Euler](MWGEquilibriumTime/Euler.lean) | 24 | (20.D.8)-(20.D.12), Proposition 20.D.7, Exercises 20.D.6, 20.D.8, 20.D.9 |
| [EulerExamples](MWGEquilibriumTime/EulerExamples.lean) | 24 | Examples 20.D.2-20.D.4, Exercises 20.D.5, 20.D.7, footnote 17 |
| [Stationary](MWGEquilibriumTime/Stationary.lean) | 14 | Definitions 20.E.1-20.E.2, Propositions 20.E.1-20.E.2, Exercises 20.E.1, 20.E.2, 20.E.9 |
| [SteadyStates](MWGEquilibriumTime/SteadyStates.lean) | 28 | Ramsey-Solow steady states, golden rule efficiency, (20.E.1), Exercises 20.E.3-20.E.8 |
| [Closer20E](MWGEquilibriumTime/Closer20E.lean) | 3 | Golden rule efficiency in the multisector model (p. 758) |
| [Dynamics](MWGEquilibriumTime/Dynamics.lean) | 21 | Section 20.F, Example 20.F.1, Exercises 20.F.1-20.F.5 |
| [Several](MWGEquilibriumTime/Several.lean) | 11 | Definition 20.G.1, Propositions 20.G.1-20.G.2, (20.G.6), Exercises 20.G.1, 20.G.5 |
| [Closer20G](MWGEquilibriumTime/Closer20G.lean) | 12 | Exercise 20.G.2 (marginal utilities of wealth at a Pareto optimum), footnote 32 and Exercise 20.G.4 (repetitions of static equilibria), Exercise 20.G.3(a)-(b) (Negishi) |
| [Closer20B](MWGEquilibriumTime/Closer20B.lean) | 6 | Exercise 20.B.5: uniqueness of the additive form up to positive affine maps |
| [OLG](MWGEquilibriumTime/OLG.lean) | 17 | Definition 20.H.1, Propositions 20.H.1-20.H.2, the nominal asset, Exercise 20.H.1 |
| [Closer20H](MWGEquilibriumTime/Closer20H.lean) | 12 | Optimality of the monetary steady state; optimal nominal equilibria iff bubble bounded away from zero, (20.H.3) and Exercise 20.H.2(b) for `√b + √a`; period-2 and period-3 cycles (Figures 20.H.5-20.H.6) |
| [AppendixMN](MWGEquilibriumTime/AppendixMN.lean) | 11 | Section M.N: Theorem M.N.1, Bellman equation, value iteration, (M.N.4) |
| [Nonequilibrium](MWGEquilibriumTime/Nonequilibrium.lean) | 7 | Section 20.I, Exercise 20.I.1 |
| [Closer20I](MWGEquilibriumTime/Closer20I.lean) | 4 | Section 20.I: global tâtonnement stability of the short-run equilibrium |

## Build and verify

From this directory:

```sh
lake build
python3 -m unittest discover -s scripts -p 'test_*.py' -v
python3 scripts/verify.py
```
