# MWGSocialChoice

Formalization of Mas-Colell, Whinston and Green, *Microeconomic Theory*, Chapter 21, "Social
Choice Theory", pp. 789-816, with the Part Five introduction (p. 787): Sections 21.A-21.E and
Exercises 21.B.1-21.E.4, every subpart. The fresh-source audit passes **281 theorems and 418
audited declarations across 20 modules**, with all 14 verifier tests passing. Highlights: May's
theorem (Proposition 21.B.1); Arrow's impossibility theorem (Proposition 21.C.1) by the book's
decisive-set proof, every step, on `𝓡^I` and `𝓟^I` with any set of alternatives; Black's
median-voter results (Propositions 21.D.1-21.D.2) and acyclicity of majority voting on
single-peaked domains; Example 21.D.6 (Condorcet winner iff median, for every probability
distribution of Euclidean peaks); Propositions 21.E.1-21.E.2 (monotonic and strategy-proof
social choice functions are dictatorial); no median for the uniform distribution on any
triangle (Figure 21.D.8(b)), by exact area computations and affine invariance; directional
median agents exist iff the gradient cone is not the whole plane (Exercise 21.D.8(a)). The
[source map](docs/source-map.md) records exact coverage; no item is OPEN.
[Corrections](docs/corrections.md) lists the departures, including three false printed
exercise claims (21.D.9(c), 21.D.10(d), 21.E.2), the false literal reading of 21.D.8(a) and the
false first-order reading of 21.D.8(c) for nonlinear utilities, each refuted with a
counterexample and replaced by a corrected statement. Generated proof checks and source
hashes are in [verification](verification/verification.json).

This is an independent Lake project pinned to Lean and Mathlib `v4.34.0`. It depends, through
a Lake `path` requirement, on MWG Chapter 1
([`MWGPreferenceChoice`](../01_PreferenceChoice/README.md)) and through it on Kreps Chapter 1:
Kreps's `Rational`, `Strict`, `Indifferent` and `UtilityPref` are MWG's rational preference,
`≻`, `∼` and utility-represented preference; MWG Proposition 1.B.1 gives footnote 3, and the
Condorcet example of Section 1.B is reused for Example 21.C.2. The reusable vocabulary for
Chapters 22-23 (profiles, `𝓡`, `𝓟`, social welfare functionals, Paretian, pairwise
independence, dictatorship, pairwise majority, social choice functions, weak Pareto,
monotonicity) is in `Aggregation` and `SocialChoiceFunctions`. All declarations are in
`MWG.SocialChoice`.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Aggregation](MWGSocialChoice/Aggregation.lean) | 23 | Profiles, `𝓡`, `𝓟`, Definitions 21.C.1-21.C.3, dictatorship, majority relation, footnotes 3, 4, 7, profile builders |
| [TwoAlternatives](MWGSocialChoice/TwoAlternatives.lean) | 24 | Section 21.B: Definitions 21.B.1-21.B.5, Examples 21.B.1-21.B.2, May's theorem, Exercises 21.B.1-21.B.3 |
| [Borda](MWGSocialChoice/Borda.lean) | 15 | Example 21.C.1 (Borda count) with footnote 6, Example 21.C.2 (Condorcet paradox), agenda remark |
| [Arrow](MWGSocialChoice/Arrow.lean) | 17 | Definition 21.C.4, Proposition 21.C.1 Steps 1-10, Exercise 21.C.1, non-vacuity |
| [WeakRationality](MWGSocialChoice/WeakRationality.lean) | 15 | Definition 21.D.1, footnote 9, Examples 21.D.1-21.D.2, Exercises 21.D.1-21.D.3 |
| [SinglePeaked](MWGSocialChoice/SinglePeaked.lean) | 21 | Definitions 21.D.2-21.D.5, Example 21.D.3, median agent, Propositions 21.D.1-21.D.2, acyclicity |
| [SinglePeakedExercises](MWGSocialChoice/SinglePeakedExercises.lean) | 8 | Exercises 21.D.5, 21.D.6, 21.D.11 |
| [ArrowConditions](MWGSocialChoice/ArrowConditions.lean) | 12 | Exercises 21.C.2(a)-(f), 21.C.3 |
| [SocialChoiceFunctions](MWGSocialChoice/SocialChoiceFunctions.lean) | 32 | Section 21.E: Definitions 21.E.1-21.E.6, Propositions 21.E.1-21.E.2, Exercises 21.E.1-21.E.4 |
| [IntervalPreferences](MWGSocialChoice/IntervalPreferences.lean) | 6 | Example 21.D.4, Exercise 21.D.4 |
| [TaxVoting](MWGSocialChoice/TaxVoting.lean) | 14 | Exercise 21.D.10(b)-(d) |
| [WeakPeaks](MWGSocialChoice/WeakPeaks.lean) | 6 | Exercise 21.D.14(a)-(d) |
| [Multidimensional](MWGSocialChoice/Multidimensional.lean) | 10 | Example 21.D.5, Exercise 21.D.12 |
| [Euclidean](MWGSocialChoice/Euclidean.lean) | 11 | Example 21.D.6: Euclidean preferences, `A(y, z)`, median iff Condorcet winner |
| [EuclideanExercises](MWGSocialChoice/EuclideanExercises.lean) | 13 | Figure 21.D.8(a), Exercise 21.D.9(a)-(f) (existence half of (d)) |
| [Plane](MWGSocialChoice/Plane.lean) | 9 | Exercise 21.D.13(a)-(b) |
| [GradientCycles](MWGSocialChoice/GradientCycles.lean) | 9 | Exercise 21.D.7(a)-(b), Exercise 21.D.8(c) (linear utilities) |
| [NonVacuity](MWGSocialChoice/NonVacuity.lean) | 6 | Instances for Proposition 21.D.1, Example 21.D.6, Exercises 21.D.7 and 21.D.13 |
| [TriangleMedian](MWGSocialChoice/TriangleMedian.lean) | 11 | Affine invariance of medians, Figure 21.D.8(b) (no median on any triangle), Exercise 21.D.9(d) nonexistence |
| [DirectionalMedian](MWGSocialChoice/DirectionalMedian.lean) | 19 | Exercise 21.D.8(a)-(c): existence iff cone is not the plane, literal-reading counterexample, Euclidean cycle example, literal (c), first-order (c) counterexample |

## Build and verify

```sh
export PATH="$HOME/.elan/bin:$PATH"
lake build MWGSocialChoice
python3 -m unittest discover -s scripts -p 'test_*.py' -v
python3 scripts/verify.py
```
