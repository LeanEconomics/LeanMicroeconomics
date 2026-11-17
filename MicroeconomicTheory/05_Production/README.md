# MWGProduction

Formalization of Mas-Colell, Whinston and Green, *Microeconomic Theory*, Chapter 5,
"Production", pp. 127-166: production sets (5.B), profit maximization and cost minimization
(5.C), the geometry of cost and supply (5.D), aggregation (5.E), efficient production (5.F),
the objectives of the firm (5.G), Appendix 5.A (the linear activity model, including the
nonsubstitution theorem and the result the book states without proof that efficient plans are
supported by strictly positive prices), the end-of-chapter exercises, and Mathematical Appendix
Section M.M (linear programming, Theorem M.M.1, proved from Farkas' lemma). The audit passed
**306 theorems and 383 declarations across 24 modules**. Coverage is in the
[source map](docs/source-map.md); no item is OPEN. Departures from the printed text are in
[corrections](docs/corrections.md).

This is a Lake project pinned to Lean and Mathlib `v4.34.0`. It imports (Lake `path`
requirements) MWG Chapter 3 (`MWGClassicalDemand`: the support function and duality theorem
Proposition 3.F.1, separating hyperplanes M.G.2, Examples 3.E.1 and Exercise 3.E.6 for the
Cobb-Douglas and CES cost functions, line-derivative lemmas of M.C) and MWG Chapter 2
(`MWGConsumerChoice`: Jacobians, Hessians, definiteness, Theorem M.D.5(v) on Neumann series),
with bridge theorems (`profit_eq_neg_supportFn`, `cd_inputReq_eq`, `exercise_5_C_10c`). See
[third-party notices](THIRD_PARTY_NOTICES.md).

`Basic` holds the properties of production sets and the single-output set; `Profit` and `Cost`
hold the profit function, supply correspondence, cost function and conditional factor demand.
Results about cost functions are proved for an arbitrary input requirement set `V ⊆ ℝ^n_+`
(`vcost_*`), covering single and multiple outputs.

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Basic](MWGProduction/Basic.lean) | 24 | Section 5.B: properties (i)-(xii), Propositions 5.B.1-5.B.2, transformation function and MRT, single-output sets, MRTS; Example 5.B.1, Exercises 5.B.1-5.B.3, Figure 5.B.8 |
| [Profit](MWGProduction/Profit.lean) | 30 | Section 5.C: profit function and supply, `π = -μ_{-Y}`, Proposition 5.C.1 (i)-(vii) for convex `Y` (corrections 3-4), law of supply, Exercises 5.C.1-5.C.2 |
| [ProfitFOC](MWGProduction/ProfitFOC.lean) | 10 | (5.C.1) with constraint qualification (correction 2), MRT ratio, sufficiency; (5.C.2), MRTS, sufficiency |
| [Cost](MWGProduction/Cost.lean) | 32 | CMP: input requirement sets, cost function as support function, Proposition 5.C.2 (i)-(ix) (Shephard's lemma without convexity), Exercises 5.C.3, 5.C.5 |
| [CostFOC](MWGProduction/CostFOC.lean) | 16 | Footnotes 8-9, `λ = ∂c/∂q`, (5.C.5)-(5.C.6), Exercise 5.C.4 (multiple outputs) |
| [Aggregation](MWGProduction/Aggregation.lean) | 16 | Section 5.E: Proposition 5.E.1, aggregate law of supply, Exercises 5.E.1-5.E.3 (correction 3) |
| [Efficiency](MWGProduction/Efficiency.lean) | 10 | Section 5.F: Definition 5.F.1, Propositions 5.F.1-5.F.2, footnote 13, Exercise 5.F.1, Figure 5.F.4 |
| [AppendixMM](MWGProduction/AppendixMM.lean) | 16 | Section M.M: finitely generated cones (Carathéodory, closedness), Farkas, Stiemke, weak duality, Theorem M.M.1, complementary slackness, figures (correction 11) |
| [LinearActivity](MWGProduction/LinearActivity.lean) | 15 | Appendix 5.A: linear activity model, `y(p)` = cone of `A(p)`, efficient ⇒ `p ≫ 0`, Leontief model, Proposition 5.AA.1 and Neumann series, Example 5.AA.1, LP production function and dual variables |
| [Nonsubstitution](MWGProduction/Nonsubstitution.lean) | 2 | Proposition 5.AA.2 (the nonsubstitution theorem) |
| [Geometry](MWGProduction/Geometry.lean) | 13 | Section 5.D: nonconvex supply locus, Exercises 5.D.1-5.D.2, setup and sunk costs (correction 8), short-run and long-run costs |
| [Objectives](MWGProduction/Objectives.lean) | 9 | Section 5.G: unanimity, price-dependent objectives, Exercise 5.G.1 (correction 10) |
| [CobbDouglas](MWGProduction/CobbDouglas.lean) | 13 | Examples 5.B.2, 5.B.3, 5.C.1 (via Chapter 3's Example 3.E.1; corrections 6-7) |
| [ExercisesB](MWGProduction/ExercisesB.lean) | 7 | Exercises 5.B.4-5.B.6 |
| [ExercisesC](MWGProduction/ExercisesC.lean) | 15 | (5.C.4) necessity (correction 5); Exercises 5.C.6-5.C.13 (correction 12) |
| [ExercisesAA](MWGProduction/ExercisesAA.lean) | 10 | Exercises 5.AA.2-5.AA.4 |
| [ExercisesAA5](MWGProduction/ExercisesAA5.lean) | 10 | Exercise 5.AA.5 (correction 13) |
| [ExercisesDE](MWGProduction/ExercisesDE.lean) | 6 | Exercises 5.D.4(a), 5.D.5(b)-(c), 5.E.5 |
| [SupplySymmetry](MWGProduction/SupplySymmetry.lean) | 14 | Proposition 5.C.1(vii) without convexity: symmetry of `Dy(p̄)` by cyclic monotonicity, continuity of single-valued supply, Hotelling's lemma, `D²π = Dy` (correction 4) |
| [ExercisesB4](MWGProduction/ExercisesB4.lean) | 4 | Exercise 5.B.4, the closed additive closure of Figure 5.B.5(b) (correction 18) |
| [ExercisesC7](MWGProduction/ExercisesC7.lean) | 7 | Exercise 5.C.7: explicit demand realizing the counterexample, `n`-input correction (correction 12) |
| [ExercisesD345](MWGProduction/ExercisesD345.lean) | 10 | Exercises 5.D.3 (Le Chatelier), 5.D.4(b)-(c), 5.D.5(a) (corrections 16-17) |
| [ExercisesE4](MWGProduction/ExercisesE4.lean) | 7 | Exercise 5.E.4(a)-(d), uniform population of Leontief technologies (correction 19) |
| [ExercisesAA1](MWGProduction/ExercisesAA1.lean) | 10 | Exercise 5.AA.1, cost and demand of Figure 5.AA.4, `z = ∇_w c` |

From this directory, run:

```sh
export PATH="$HOME/.elan/bin:$PATH"
lake build
python3 -m unittest discover -s scripts -p 'test_*.py' -v
python3 scripts/verify.py
```

The verifier builds the project, freshly recompiles the contributed modules and audits every
named declaration; only `propext`, `Classical.choice` and `Quot.sound` occur.
