# Source map

Mas-Colell, Whinston and Green, *Microeconomic Theory*, Chapter 1, "Preference and Choice",
pp. 5-16. Printed pages; Lean names relative to `MWG.PreferenceChoice`.
Every definition, proposition, example, small-type claim and exercise subpart of Sections
1.A-1.D and Exercises 1.B.1-1.D.5 is accounted for below. Notions that coincide with Kreps
Chapter 1 (`Kreps.ChoicePreferenceUtility`: `Rational`, `Strict`, `Indifferent`,
`Represents`, `PrefChoice`) are imported from that project with bridge theorems; MWG's
choice structures `(𝓑, C(·))`, the weak axiom and revealed preference are defined here.
No Mathematical Appendix section belongs to this chapter. Nothing is OPEN.

## Section 1.A and Section 1.B: preference relations

| Source | Claim | Lean |
| --- | --- | --- |
| Section 1.A, pp. 5-6 | Introduction; no mathematical claim | Listed only (exposition) |
| Section 1.B, p. 6 | Preference relation, strict preference `≻`, indifference `∼` | `strict_iff`, `indifferent_iff` (Kreps `Strict`, `Indifferent`) |
| Footnote 1, p. 6 | Terminology "weakly/strictly preferred" | Listed only (terminology) |
| Definition 1.B.1, p. 6 | Rational = complete and transitive | `definition_1_B_1` (Kreps `Rational`) |
| Footnote 2, p. 6 | Completeness implies reflexivity | `footnote_1_2` |
| Proposition 1.B.1(i), p. 7 | `≻` irreflexive and transitive | `proposition_1_B_1_i` |
| Proposition 1.B.1(ii), p. 7 | `∼` reflexive, transitive, symmetric | `proposition_1_B_1_ii` |
| Proposition 1.B.1(iii), p. 7 | `x ≻ y ≿ z` implies `x ≻ z` | `proposition_1_B_1_iii` |
| Section 1.B, small type, pp. 7-8 | Common form: a rational relation has no strict 3-cycle | `prefRel_no_strict_cycle` |
| Section 1.B, small type, p. 7 | Just perceptible differences violate transitivity | `prefRel_just_perceptible` |
| Section 1.B, small type, pp. 7-8 | Framing: `x ≻ z`, `z ≻ y`, `x ∼ y` is intransitive | `prefRel_framing` |
| Footnote 3, p. 8 | Mental accounts | Listed only (empirical) |
| Section 1.B, small type, p. 8 | Condorcet paradox: rational members, cyclic majority | `condorcetRank`, `condorcetMajority`, `prefRel_condorcet` |
| Section 1.B, small type, p. 8 | Change of tastes: apparent cycle `z ≻ x ≻ y`, `x ≻ y ≻ z` | `prefRel_change_of_tastes` |
| Definition 1.B.2, p. 9 | Utility function representing `≿` | `definition_1_B_2` (Kreps `Represents`) |
| Section 1.B, p. 9 | `f ∘ u` represents `≿` for strictly increasing `f` | `exercise_1_B_3` |
| Section 1.B, p. 9 | Utility differences are cardinal, not ordinal | `prefRel_differences_not_ordinal` |
| Proposition 1.B.2, p. 9 | Representable implies rational | `proposition_1_B_2` |
| Section 1.B, p. 9 | Not every rational relation is representable (Section 3.G) | `prefRel_rational_not_representable` (via Kreps Problem 1.10) |
| Section 1.B, p. 9 | Finite `X`: every rational relation is representable | `exercise_1_B_5` |

## Section 1.C: choice rules

| Source | Claim | Lean |
| --- | --- | --- |
| Section 1.C, pp. 9-10 | Choice structure `(𝓑, C(·))`: nonempty budgets, `∅ ≠ C(B) ⊆ B` | `ChoiceStructure` |
| Example 1.C.1, p. 10 | `X = {x,y,z}`, `𝓑 = {{x,y},{x,y,z}}`, rules `C₁`, `C₂` | `threeChoice`, `threeChoice_budgets`, `threeChoice_ne`, `threeChoice_C_xy`, `threeChoice_C_xyz`, `example_1_C_1_C₁`, `example_1_C_1_C₂` |
| Footnote 4, p. 10 | Origin of the proclivity | Listed only (interpretation) |
| Definition 1.C.1, p. 10 | Weak axiom of revealed preference | `WeakAxiom`; bridge to Kreps coherence `weakAxiom_iff_coherentOn` |
| Section 1.C and footnote 5, p. 11 | `C({x,y}) = {x}` forces `C({x,y,z}) ∈ {{x},{z},{x,z}}` | `exercise_1_C_1` |
| Definition 1.C.2, p. 11 | Revealed preference relation `≿*` | `RevealedPref` |
| Section 1.C, p. 11 | "Revealed preferred" | `RevealedStrict` |
| Section 1.C, p. 11 | `≿*` need not be complete | `revealedPref_not_complete` |
| Section 1.C, p. 11 | `≿*` need not be transitive | `revealedPref_not_transitive` |
| Section 1.C, p. 11 | Restatement: `x ≿* y` excludes `y` revealed preferred to `x` | `weakAxiom_iff_revealed` |
| Example 1.C.2, p. 11 | `C₁` satisfies the weak axiom; revealed relations | `example_1_C_2_C₁` |
| Example 1.C.2, p. 11 | `C₂` violates the weak axiom; revealed relations | `example_1_C_2_C₂` |

## Section 1.D: relationship between preferences and choice rules

| Source | Claim | Lean |
| --- | --- | --- |
| Section 1.D, p. 12 | `C*(B, ≿)` | `mem_prefChoice_iff` (Kreps `PrefChoice`) |
| Section 1.D, p. 12 | `C*(B, ≿)` may be empty | `prefChoice_can_be_empty` |
| Footnote 6, p. 12 | Nonempty for finite `X` | `exercise_1_D_2` |
| Section 1.D, p. 12 | `≿` generates `(𝓑, C*(·, ≿))` | `generatedStructure` |
| Proposition 1.D.1, p. 12 | Generated structure satisfies the weak axiom | `proposition_1_D_1` |
| Definition 1.D.1, p. 12 | `≿` rationalizes `C(·)` relative to `𝓑` | `Rationalizes`, `Rationalizable` |
| Section 1.D, p. 13 | Rationalizing relation need not be unique | `exercise_1_D_1a` |
| Section 1.D, p. 13 | Only weak-axiom rules can be rationalized | `weakAxiom_of_rationalizes` |
| Example 1.D.1, p. 13 | The structure and its weak axiom ("verify this") | `cyclicPairs`, `cyclicPairs_values`, `cyclicPairs_budget_cases`, `cyclicPairs_weakAxiom` |
| Example 1.D.1, p. 13 | No rationalizing preference | `example_1_D_1` |
| Section 1.D, p. 13 | `{x,y,z} ∉ 𝓑` is crucial | `exercise_1_D_3` |
| Proposition 1.D.2, hypothesis (ii), p. 13 | `𝓑` contains all subsets with at most three elements | `ContainsSmallSubsets`, `containsSmallSubsets_pair`, `containsSmallSubsets_triple` |
| Proposition 1.D.2 proof (i), p. 13 | `≿*` complete and transitive | `proposition_1_D_2_rational` |
| Proposition 1.D.2 proof (ii), pp. 13-14 | `C(B) = C*(B, ≿*)` | `proposition_1_D_2_generates` |
| Proposition 1.D.2 proof (iii), p. 14 | Uniqueness via pairwise choices | `revealedPref_iff_mem_pair`, `proposition_1_D_2_unique` |
| Proposition 1.D.2, p. 13 | Existence and uniqueness of a rationalizing rational relation | `proposition_1_D_2` |
| Section 1.D, p. 14 | With all small subsets, weak axiom iff rationalizable | `weakAxiom_iff_rationalizable` |
| Section 1.D, p. 14 | Strengthened axiom in Section 3.J | Listed only (forward reference to Chapter 3) |
| Section 1.D, small type, p. 14 | Alternative notion `C(B) ⊆ C*(B, ≿)` | `WeaklyRationalizes` |
| Section 1.D, small type, p. 14 | It is weaker | `weaklyRationalizes_of_rationalizes` |
| Section 1.D, small type, p. 14 | Total indifference rationalizes anything in this sense | `weaklyRationalizes_indifference` |

## Exercises

| Source | Claim | Lean |
| --- | --- | --- |
| Exercise 1.B.1, p. 15 | Proposition 1.B.1(iii) | `exercise_1_B_1` |
| Exercise 1.B.2, p. 15 | Proposition 1.B.1(i)-(ii) | `exercise_1_B_2` |
| Exercise 1.B.3, p. 15 | Strictly increasing transforms preserve representation | `exercise_1_B_3` |
| Exercise 1.B.4, p. 15 | Indifference/strict conditions imply representation | `exercise_1_B_4` (rationality not needed; see corrections) |
| Exercise 1.B.5, p. 15 | Finite `X`: rational relation has a utility representation | `exercise_1_B_5` (via Kreps Proposition 1.8) |
| Exercise 1.C.1, p. 15 | `C({x,y,z})` is `{x}`, `{z}` or `{x,z}` | `exercise_1_C_1` |
| Exercise 1.C.2, p. 15 | Equivalent form of the weak axiom | `exercise_1_C_2` |
| Exercise 1.C.3, p. 15 | `≻**` | `RevealedStrict'`, `revealedStrict_of_revealedStrict'` |
| Exercise 1.C.3(a), p. 15 | `≻* = ≻**` under the weak axiom; not without it | `exercise_1_C_3a`, `exercise_1_C_3a_without_weakAxiom` |
| Exercise 1.C.3(b), p. 15 | `≻*` need not be transitive (answer: no) | `exercise_1_C_3b` |
| Exercise 1.C.3(c), p. 15 | Three-element subsets in `𝓑` make `≻*` transitive | `exercise_1_C_3c` |
| Exercise 1.D.1, p. 15 | Several rationalizing preferences | `exercise_1_D_1_structure`, `exercise_1_D_1a` |
| Exercise 1.D.1, p. 15 | At most one when `𝓑` contains all pairs | `exercise_1_D_1b` |
| Exercise 1.D.2, p. 16 | Finite `X`: `C*(B, ≿) ≠ ∅` for nonempty `B` | `exercise_1_D_2` |
| Exercise 1.D.3, p. 16 | Example 1.D.1 plus `{x,y,z}` violates the weak axiom | `exercise_1_D_3` |
| Exercise 1.D.4, p. 16 | Rationalizable implies path invariance | `exercise_1_D_4` |
| Exercise 1.D.5, p. 16 | Six strict relations, random preferences, stochastic rationalization | `rankPrefers`, `rankPrefers_strictTotal`, `rankPrefers_injective`, `StochasticRationalizable`, `cyclicChoice`, `cyclicChoice_valid` |
| Exercise 1.D.5, p. 16 | Characterization `1/3 ≤ α ≤ 2/3` | `cyclicCount`, `cyclicCount_bounds`, `cyclicChoice_bounds_of_rationalizable`, `rankPrefers_card`, `rankPrefers_cyclicCount_sum`, `cyclicDistribution`, `cyclicChoice_rationalizable_of_bounds`, `cyclicChoice_rationalizable_iff` |
| Exercise 1.D.5(a), p. 16 | `(1/2, 1/2)` is rationalizable | `exercise_1_D_5a` |
| Exercise 1.D.5(b), p. 16 | `(1/4, 3/4)` is not rationalizable | `exercise_1_D_5b` |
| Exercise 1.D.5(c), p. 16 | Switches at `α = 1/3` and `α = 2/3` | `exercise_1_D_5c` |
