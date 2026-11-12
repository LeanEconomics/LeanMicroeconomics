# MWGPreferenceChoice

Formalization of Mas-Colell, Whinston and Green, *Microeconomic Theory*, Chapter 1,
"Preference and Choice", pp. 5-16: Sections 1.A-1.D and Exercises 1.B.1-1.D.5, every
subpart. The fresh-source audit passes **73 theorems and 101 audited declarations across
4 modules**, with all 14 verifier tests passing. The [source map](docs/source-map.md)
records exact coverage (nothing is open); [corrections](docs/corrections.md) lists the
departures from the printed statements (no printed claim was found false). Generated proof
checks and source hashes are in [verification](verification/verification.json).

This is an independent Lake project pinned to Lean and Mathlib `v4.34.0`. It depends,
through a Lake `path` requirement, on Kreps Chapter 1
([`ChoicePreferenceUtility`](../../Volume1/01_ChoicePreferenceUtility/README.md)), whose
`Rational`, `Strict`, `Indifferent`, `Represents` and `PrefChoice` are MWG's rational
preference, `≻`, `∼`, utility representation and `C*(B, ≿)`; its Proposition 1.8 gives
Exercise 1.B.5, Problem 1.10 the non-representable rational relation, and its finite
nonemptiness result Exercise 1.D.2. MWG's choice structures, weak axiom and revealed
preference are defined here, with a bridge to Kreps's coherence. All declarations are in
`MWG.PreferenceChoice`.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [PreferenceRelations](MWGPreferenceChoice/PreferenceRelations.lean) | 21 | Section 1.B: Definitions 1.B.1-1.B.2, Propositions 1.B.1-1.B.2, intransitivity examples, Exercises 1.B.1-1.B.5 |
| [ChoiceRules](MWGPreferenceChoice/ChoiceRules.lean) | 20 | Section 1.C: choice structures, weak axiom, revealed preference, Examples 1.C.1-1.C.2, Exercises 1.C.1-1.C.3 |
| [Rationalization](MWGPreferenceChoice/Rationalization.lean) | 20 | Section 1.D: Propositions 1.D.1-1.D.2, Definition 1.D.1, Example 1.D.1, Exercises 1.D.1-1.D.4 |
| [StochasticChoice](MWGPreferenceChoice/StochasticChoice.lean) | 12 | Exercise 1.D.5: random-preference rationalization iff `1/3 ≤ α ≤ 2/3` |

## Build and verify

```sh
export PATH="$HOME/.elan/bin:$PATH"
lake build MWGPreferenceChoice
python3 -m unittest discover -s scripts -p 'test_*.py' -v
python3 scripts/verify.py
```
