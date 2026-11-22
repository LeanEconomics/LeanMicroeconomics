# MWGCoreFoundations

Formalization of Mas-Colell, Whinston and Green, *Microeconomic Theory*, Chapter 18, "Some
Foundations for Competitive Equilibria", pp. 652-686, with Appendix A (cooperative game theory)
and Exercises 18.B.1-18.AA.10. Highlights: the core and blocking (Definitions 18.B.1-18.B.2),
Walrasian allocations are in the core for any constant returns technology (Proposition 18.B.1),
equal treatment in replica economies (Proposition 18.B.2), the Debreu-Scarf core convergence
theorem (Proposition 18.B.3) proved in full generality by the convex hull of improving trades,
rounding and separation, after refuting the printed version with boundary endowments; the
abstract trading model with the Cournot, complements and trading-post examples and the
convexity of trading-post budget sets (18.C); self-selective allocations, a Pareto optimal
self-selective non-Walrasian allocation and Proposition 18.D.1 in a corrected smooth form and
in a continuum form for `L = 2` with a population measure, where the continuity of the net-trade
path is derived (18.D); the no-surplus characterization of Walrasian equilibrium (Proposition 18.E.1) with
Euler's formula and (18.E.5), and the exact hypergeometric-average formula for the Shapley value
of an economy with types (18.E); and in Appendix A NTU and TU games, superadditivity, the
core, the Bondareva-Shapley theorem (Exercise 18.AA.1, via Farkas's lemma), the Shapley value by
preservation of differences with its uniqueness and the formulas (18.AA.3)-(18.AA.4), the glove
market, Proposition 18.AA.1 (convex games), the convexity of production games under the printed
cross-partial condition for any number of inputs, and the closedness of `V(S)` for closed cones
with no free production. The fresh-source audit passes **387 theorems
and 552 audited declarations across 18 modules**. Coverage, including the OPEN items, is in the
[source map](docs/source-map.md); departures are in [corrections](docs/corrections.md) (refuted
printed claims: Proposition 18.B.3 with `ωₕ ≥ 0`, the supporting-price claim of p. 659,
Exercise 18.B.5(a), the closedness claim of Example 18.AA.1, footnote 28, Example 18.C.2's
assumptions, the hypergeometric formula of p. 673 as printed, and the misprint `B = {x*ᵢ}` of
p. 666).

This is a Lake project pinned to Lean and Mathlib `v4.34.0`. It imports (Lake `path`
requirements, no copies) MWG Chapter 16 (`MWGWelfareTheorems`: `IsMaximalFor`, Walrasian
equilibrium and Pareto optimality, the first welfare theorem, the replica and cheaper-point
lemmas, `concaveOn_le_tangent`) and through it Chapters 15, 10, 5 (`farkas`), 3 (preference
properties, `duality_exists_dot_of_clm`) and 2 (`budgetSetOn`, `nonnegOrthant`), and MWG
Chapter 22 (`MWGWelfareBargaining`: TU games, the Shapley value, unanimity games and Harsanyi
dividends).
See [third-party notices](THIRD_PARTY_NOTICES.md).

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Basic](MWGCoreFoundations/Basic.lean) | 10 | Economy, Definitions 18.B.1-18.B.2, Walrasian equilibrium, replicas, `C_N`, an instance of the standing assumptions |
| [CoreWalras](MWGCoreFoundations/CoreWalras.lean) | 24 | Proposition 18.B.1, Exercise 18.B.1, core ⊆ Pareto, footnote 2, Figures 18.B.1-18.B.2, the converse is false |
| [EqualTreatment](MWGCoreFoundations/EqualTreatment.lean) | 21 | Proposition 18.B.2, footnote 5, `C_{N+1} ⊆ C_N`, Exercises 18.B.2-18.B.3 |
| [DebreuScarf](MWGCoreFoundations/DebreuScarf.lean) | 9 | Proposition 18.B.3: counterexample as printed, corrected general proof |
| [DebreuScarfSpecial](MWGCoreFoundations/DebreuScarfSpecial.lean) | 13 | The book's special-case proof, Exercise 18.B.4, the sets `V` of p. 659 |
| [ShoeMarket](MWGCoreFoundations/ShoeMarket.lean) | 17 | Exercise 18.B.5(a)-(d) |
| [TradingGames](MWGCoreFoundations/TradingGames.lean) | 45 | Definition 18.C.1, footnotes 7-8, 12-14, Examples 18.C.1-18.C.3, Exercise 18.C.1 |
| [Redistribution](MWGCoreFoundations/Redistribution.lean) | 14 | Definition 18.D.1, Figures 18.D.2-18.D.3, Proposition 18.D.1 (partial), Exercise 18.D.1 |
| [MarginalProduct](MWGCoreFoundations/MarginalProduct.lean) | 44 | `v(μ)`, footnote 20, Exercises 18.E.1-18.E.2, Definition 18.E.1, Proposition 18.E.1, finite-economy claims |
| [MarginalProductExamples](MWGCoreFoundations/MarginalProductExamples.lean) | 34 | Instances, Exercise 18.E.3, the Shapley sum of p. 673 |
| [CoopGames](MWGCoreFoundations/CoopGames.lean) | 31 | Definitions 18.AA.1-18.AA.6, Examples 18.AA.1-18.AA.6, Exercises 18.AA.2-18.AA.3, footnote 28 |
| [Balanced](MWGCoreFoundations/Balanced.lean) | 8 | Exercise 18.AA.1: Bondareva-Shapley |
| [ShapleyValue](MWGCoreFoundations/ShapleyValue.lean) | 34 | (18.AA.1)-(18.AA.4), Definition 18.AA.7, properties (a)-(d), Exercises 18.AA.4-18.AA.6 |
| [ShapleyExamples](MWGCoreFoundations/ShapleyExamples.lean) | 20 | Example 18.AA.7, Definition 18.AA.8, Proposition 18.AA.1, Example 18.AA.8, Exercises 18.AA.7-18.AA.8 |
| [ShapleyExercises](MWGCoreFoundations/ShapleyExercises.lean) | 19 | Exercises 18.AA.9-18.AA.10 |
| [Closer18AA](MWGCoreFoundations/Closer18AA.lean) | 19 | Example 18.AA.8 / Exercise 18.AA.7 with `∂²f/∂z_h∂z_k ≥ 0` for any `N`; Example 18.AA.1: `V(S)` closed for closed cones with no free production, and the free-production counterexample |
| [Closer18Value](MWGCoreFoundations/Closer18Value.lean) | 11 | p. 673: profile counting, the exact hypergeometric-average formula for the Shapley value, weights sum to one, the printed formula refuted |
| [Closer18D](MWGCoreFoundations/Closer18D.lean) | 14 | Proposition 18.D.1 for a continuum of types (`L = 2`): planar flatness, flatness from no envy, continuity of `z(t)` derived, measure feasibility, measure-theoretic Pareto optimality, the main theorem and an instance |

From this directory, run:

```sh
export PATH="$HOME/.elan/bin:$PATH"
lake build
python3 -m unittest discover -s scripts -p 'test_*.py' -v
python3 scripts/verify.py
```
