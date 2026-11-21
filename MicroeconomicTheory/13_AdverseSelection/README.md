# MWGAdverseSelection

Formalization of Mas-Colell, Whinston and Green, *Microeconomic Theory*, Chapter 13,
"Adverse Selection, Signaling, and Screening", pp. 436-476. It covers the Akerlof labor market
with unobservable productivity (13.B): competitive equilibrium, adverse selection and
unraveling (Example 13.B.1), the two-firm wage game (Proposition 13.B.1) and constrained
Pareto optimality (Proposition 13.B.2, mechanisms in small type). It covers education signaling
(13.C): Lemmas 13.C.1-13.C.2, separating and pooling perfect Bayesian equilibria, welfare, and
cross-subsidization. It covers competitive screening (13.D): Proposition 13.D.1, Lemmas
13.D.1-13.D.5, Proposition 13.D.2 and nonexistence. Appendix A on reasonable-beliefs
refinements is also covered: equilibrium dominance, the intuitive criterion, Example 13.AA.1,
and the selection of the best separating equilibrium. All end-of-chapter exercises are covered.
The audit passed **501 theorems and 795 declarations across 37 modules**. Coverage is in
the [source map](docs/source-map.md); nothing is left open; departures from the printed text are in
[corrections](docs/corrections.md). Among them are counterexamples to the inefficiency claim
for constant `r` with an atom, to Proposition 13.B.1(i) without continuity of `r`, to the
constrained optimality of screening equilibria (footnote 25), to the uniqueness claimed in
Exercise 13.C.4, and to Exercises 13.B.6(d)(ii) and 13.B.8 as printed.

This is a Lake project pinned to Lean and Mathlib `v4.34.0`. It imports (Lake requirement, no
copies) MWG Chapter 8 (`MWGSimultaneousMoveGames`: `IsNashEquilibrium`) and Chapter 7
(`MWGNoncooperativeGames`: `NormalForm`), which it obtains through the `MWGDynamicGames`
requirement. Chapter 9's finite extensive forms do not fit the continuous signaling and
screening games (corrections, item 5). See [third-party
notices](THIRD_PARTY_NOTICES.md).

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Basic](MWGAdverseSelection/Basic.lean) | 11 | Θ(w) (13.B.2), E[θ], `condMean`, Definition 13.B.1, `W*`, (13.B.3), firm profit, standing assumptions |
| [Continuity](MWGAdverseSelection/Continuity.lean) | 4 | Continuity of the profit in the wage (dominated convergence), losses above θ̄ |
| [Regular](MWGAdverseSelection/Regular.lean) | 16 | The model of p. 441: footnote 7, Figure 13.B.2, positive employment above r(θ̲), existence of `Max W*` |
| [CondMeanMono](MWGAdverseSelection/CondMeanMono.lean) | 5 | Monotonicity of `E[θ | r(θ) ≤ w]` (p. 441): weak for monotone `r`, strict in the regular model |
| [WageGame](MWGAdverseSelection/WageGame.lean) | 10 | The two-firm wage game (Chapter 8 normal form): uniqueness and flat-profit characterizations |
| [GameTheoretic](MWGAdverseSelection/GameTheoretic.lean) | 6 | Proposition 13.B.1(i)-(ii), workers' stage-2 behaviour |
| [Uniform](MWGAdverseSelection/Uniform.lean) | 9 | Uniform type distributions |
| [Unraveling](MWGAdverseSelection/Unraveling.lean) | 16 | Example 13.B.1, footnote 10, instance of Proposition 13.B.1(i), correction 2 counterexample |
| [Efficiency](MWGAdverseSelection/Efficiency.lean) | 15 | Full information, footnote 4, (13.B.1), constant r (p. 440), correction 1, Pareto ranking |
| [Constrained](MWGAdverseSelection/Constrained.lean) | 16 | Constrained Pareto optimality, Proposition 13.B.2 and Exercise 13.B.10, (13.B.7)-(13.B.12), footnote 15 |
| [Mechanism](MWGAdverseSelection/Mechanism.lean) | 6 | (13.B.13), mandated employment, direct revelation mechanisms (13.B.14)-(13.B.17) |
| [Signaling](MWGAdverseSelection/Signaling.lean) | 20 | The signaling model, Bertrand wages, PBE (p. 452) and its reduced form |
| [SignalingEq](MWGAdverseSelection/SignalingEq.lean) | 21 | Lemmas 13.C.1-13.C.2, separating and pooling PBE, welfare, refinement (pp. 457-458), small type |
| [CrossSubsidy](MWGAdverseSelection/CrossSubsidy.lean) | 7 | Exercise 13.C.3 (Figure 13.C.11), concrete signaling model |
| [Refinements](MWGAdverseSelection/Refinements.lean) | 6 | Appendix A: signaling games, (13.AA.1)-(13.AA.4), Θ(a), Θ*(a), Θ**(a), intuitive criterion |
| [ExampleAA1](MWGAdverseSelection/ExampleAA1.lean) | 11 | Example 13.AA.1 |
| [TwoTypes](MWGAdverseSelection/TwoTypes.lean) | 5 | Concrete two-type instance of `two_types_reasonable` (p. 472) |
| [EducationIC](MWGAdverseSelection/EducationIC.lean) | 6 | Appendix A in the education model: the intuitive criterion selects the best separating equilibrium |
| [Screening](MWGAdverseSelection/Screening.lean) | 15 | The screening game, Proposition 13.D.1 |
| [ScreeningEq](MWGAdverseSelection/ScreeningEq.lean) | 22 | Both types work in every SPNE (p. 462), Lemmas 13.D.1-13.D.5, Proposition 13.D.2, nonexistence (Figures 13.D.7(b), 13.D.8) |
| [ScreeningWelfare](MWGAdverseSelection/ScreeningWelfare.lean) | 13 | Existence criterion and concrete SPNE (Figure 13.D.7(a)), welfare (p. 466), footnote 25 counterexample |
| [Exercises](MWGAdverseSelection/Exercises.lean) | 10 | Exercises 13.B.4, 13.B.5, 13.C.5, 13.C.6(a); instance of Proposition 13.B.2 |
| [ExerciseC4](MWGAdverseSelection/ExerciseC4.lean) | 9 | Exercise 13.C.4: separating and pooling PBE, uniqueness of the separating PBE |
| [ExercisesB](MWGAdverseSelection/ExercisesB.lean) | 26 | Exercises 13.B.1, 13.B.2, 13.B.3 |
| [ExercisesB7](MWGAdverseSelection/ExercisesB7.lean) | 15 | Exercise 13.B.7 and its proof of Proposition 13.B.2 |
| [ExercisesB8](MWGAdverseSelection/ExercisesB8.lean) | 7 | Exercise 13.B.8 (counterexample and corrected statement) |
| [ExercisesB9](MWGAdverseSelection/ExercisesB9.lean) | 7 | Exercise 13.B.9 |
| [ExercisesB6](MWGAdverseSelection/ExercisesB6.lean) | 38 | Exercise 13.B.6: Wilson's model with heterogeneous firms and the wage-offer game |
| [ExercisesC1](MWGAdverseSelection/ExercisesC1.lean) | 2 | Exercise 13.C.1: costless test |
| [ExercisesC2](MWGAdverseSelection/ExercisesC2.lean) | 12 | Exercise 13.C.2: productive education |
| [ExercisesC6](MWGAdverseSelection/ExercisesC6.lean) | 14 | Exercise 13.C.6(b): self-financing as a signal |
| [ScreeningGen](MWGAdverseSelection/ScreeningGen.lean) | 24 | A general two-type screening game; zero profits and deviation lemmas |
| [ExercisesD1](MWGAdverseSelection/ExercisesD1.lean) | 18 | Exercise 13.D.1: productive tasks |
| [ExercisesD2](MWGAdverseSelection/ExercisesD2.lean) | 32 | Exercise 13.D.2: Rothschild-Stiglitz insurance, existence and nonexistence |
| [ExercisesD3](MWGAdverseSelection/ExercisesD3.lean) | 11 | Exercise 13.D.3: observable output |
| [ExercisesD4](MWGAdverseSelection/ExercisesD4.lean) | 15 | Exercise 13.D.4: free entry with single contracts |
| [ExerciseAA1](MWGAdverseSelection/ExerciseAA1.lean) | 21 | Exercise 13.AA.1: two PBE passing the intuitive criterion |

## Build and verify

From this chapter directory:

```sh
lake build
python3 -m unittest discover -s scripts -p 'test_*.py' -v
python3 scripts/verify.py
```

The verifier builds the library, recompiles all sources in a fresh file, and audits every
declaration's axioms (only `propext`, `Classical.choice` and `Quot.sound` are allowed).
