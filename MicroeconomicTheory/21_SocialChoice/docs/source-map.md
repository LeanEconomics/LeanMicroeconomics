# Source map

Mas-Colell, Whinston and Green, *Microeconomic Theory*, Part Five introduction (p. 787) and
Chapter 21, "Social Choice Theory", pp. 789-816. Printed pages; Lean names relative to
`MWG.SocialChoice`. Every definition, proposition, example, small-type claim, footnote and
exercise subpart of Sections 21.A-21.E and Exercises 21.B.1-21.E.4 is accounted for below.
Rational preferences, strict preference and indifference are Kreps's `Rational`, `Strict`,
`Indifferent` (via MWG Chapter 1, `MWGPreferenceChoice`). Profiles are maps
`ι → X → X → Prop` (`Profile`); social welfare functionals, Paretian, pairwise independence,
dictatorship and pairwise majority (`majorityRel`) are defined in `Aggregation` for reuse in
Chapters 22-23. The plane of Section 21.D's exercises is modelled by `ℂ` with its real inner
product; Example 21.D.6 is proved in any real inner product space. No item is OPEN. No
Mathematical Appendix section belongs to this chapter.

## Part Five introduction and Section 21.A

| Source | Claim | Lean |
| --- | --- | --- |
| Part Five introduction, p. 787 | Overview of Chapters 21-23 | Listed only (no precise claim) |
| Section 21.A, pp. 789-790 | Introduction and overview | Listed only (exposition) |

## Section 21.B: two alternatives

| Source | Claim | Lean |
| --- | --- | --- |
| Section 21.B, p. 790 | Profiles `α ∈ {-1,0,1}^I` | `TwoAltProfiles` |
| Footnote 1, p. 790 | Only rankings matter; no cardinal information | Listed only (modelling remark) |
| Definition 21.B.1, p. 790 | Social welfare functional | `IsTwoAltSWF` |
| Definition 21.B.2, p. 790 | Paretian | `TwoAltParetian` |
| Example 21.B.1, pp. 790-791 | `sign ∑ βᵢαᵢ`, `β ≥ 0` not all zero, is a Paretian SWF | `weightedVoting`, `weightedVoting_isSWF`, `example_21_B_1`, `signType_cast_cases` |
| Example 21.B.1, p. 791 | Majority voting `β = 1`; `F = 1, -1, 0` by counts | `majorityVoting`, `majorityVoting_eq_weighted`, `majorityVoting_isSWF`, `nPlus`, `nMinus`, `sum_eq_nPlus_sub_nMinus`, `majorityVoting_spec`, `int_sign_cases` |
| Example 21.B.2, p. 791 | Dictatorship; dictatorial implies Paretian; `βₕ > 0`, others `0` gives `F = αₕ` | `IsTwoAltDictator`, `example_21_B_2_paretian`, `example_21_B_2` |
| Definition 21.B.3, p. 791 | Symmetric among agents | `SymmetricAmongAgents` |
| Definition 21.B.4, p. 791 | Neutral between alternatives | `NeutralBetweenAlternatives`, `neg_mem_twoAltProfiles` |
| Definition 21.B.5, p. 791 | Positively responsive | `PositivelyResponsive` |
| Proposition 21.B.1 (May), p. 792 | Majority iff symmetric, neutral, positively responsive | `proposition_21_B_1` (proof steps `may_tie`, `may_plus`) |
| Footnote 2, p. 792 | Notation `#A` | Listed only (notation) |
| Section 21.B, p. 792 | Exercise 21.B.2 shows independence of the three properties | `exercise_21_B_2_symmetry`, `exercise_21_B_2_neutrality`, `exercise_21_B_2_responsiveness` |

## Section 21.C: Arrow's impossibility theorem

| Source | Claim | Lean |
| --- | --- | --- |
| Section 21.C, p. 793 | Sets `𝓡`, `𝓟`, `𝓟 ⊂ 𝓡`; domains `𝓡^I`, `𝓟^I` | `RationalPrefs`, `StrictPrefs`, `NoIndifference`, `strictPrefs_subset`, `RationalProfiles`, `StrictProfiles`, `strictProfiles_subset`, `Profile` |
| Footnote 3, p. 793 | Properties of `≻ᵢ`, `∼ᵢ` (Prop. 1.B.1) | `footnote_21_3_strict`, `footnote_21_3_indifferent` (imported Chapter 1); `strict_trans`, `strict_of_weak_strict`, `weak_of_not_strict`, `strict_asymm` |
| Footnote 4, p. 793 | `𝓟` = reflexive, transitive, total relations | `footnote_21_4` |
| Definition 21.C.1, p. 793 | Social welfare functional on `𝒜` | `IsSWF` |
| Footnote 5, p. 793 | No utility levels | Listed only (modelling remark) |
| Section 21.C, p. 793 | Strict social preference `F_p` | Kreps `Strict` applied to `F p` |
| Definition 21.C.2, p. 794 | Paretian | `Paretian` |
| Example 21.C.1, p. 794 | Borda count; rational; Paretian | `bordaPoints`, `bordaSWF`, `example_21_C_1_rational`, `bordaPoints_lt`, `example_21_C_1_paretian` |
| Example 21.C.1, p. 794 | Without indifference `cᵢ(x)` = rank | `example_21_C_1_rank` |
| Footnote 6, p. 794 | `x ≻ y ∼ z`: `c(x) = 1`, `c(y) = c(z) = 2.5` | `footnote_21_6` (with `bordaPoints_natPref`) |
| Definition 21.C.3, p. 794 | Pairwise independence | `PairwiseIndependent`, `PairwiseIndependent.strict_transfer`, `agree_of_same_ranking` |
| Footnote 7, p. 794 | Equivalent form with restrictions `≿|{x,y}` | `restrictPair`, `restrictPair_eq_iff`, `footnote_21_7` |
| Example 21.C.1 continued, p. 795 | Two agents: `c(x) = 3 < 4`, then `4 > 3`; Borda violates pairwise independence | `bordaProfileA`, `bordaProfileB`, `example_21_C_1_two_agents`, `bordaSWF_two` |
| Example 21.C.1 continued, p. 795 | Three agents, four alternatives: `8 > 7`, (21.C.1) `4 < 5`, then `6 > 5` | `bordaProfileC`, `bordaProfileD`, `bordaProfileE`, `example_21_C_1_three_agents`, `bordaSWF_three` |
| Example 21.C.2 (Condorcet paradox), p. 796 | Pairwise majority cycles; not a SWF on `𝓡^I` or `𝓟^I` | `condorcetProfile`, `condorcetProfile_mem`, `majorityRel`, `majorityRel_iff`, `majorityRel_natPref`, `condorcet_majority`, `example_21_C_2` |
| Footnote 8, p. 796 | Already in Section 1.B | `condorcetProfile` (built on Chapter 1's `condorcetRank`) |
| Proposition 21.C.1 (Arrow), p. 796 | Paretian + pairwise independence on `𝓡^I`/`𝓟^I`, `≥ 3` alternatives: dictatorial | `proposition_21_C_1`, `StandardDomain`, `StandardDomain.score_mem`, `StandardDomain.rational`, `scorePref`, `scorePref_mem`, `scorePref_strict_of_lt`, `rank3`, `rank3_strict`, `exists_third` |
| Proposition 21.C.1, non-vacuity | Instances of the hypotheses; dictatorship attained | `dictatorSWF`, `dictatorSWF_spec`, `proposition_21_C_1_nonvacuous` |
| Definition 21.C.4, p. 797 | Decisive for `x` over `y`; decisive; completely decisive | `DecisiveFor`, `Decisive`, `CompletelyDecisiveFor` |
| Step 1, p. 797 | Decisive `x` over `y` ⇒ decisive `x` over `z` | `arrow_step_1` |
| Step 1 (second half), p. 797 | ⇒ decisive `z` over `y` | `exercise_21_C_1` |
| Step 2, p. 797 | Decisive `z` over `w` and `w` over `z` | `arrow_step_2` |
| Step 3, p. 797 | Decisive for one pair ⇒ decisive | `arrow_step_3` |
| Step 4, p. 798 | Intersections of decisive sets are decisive | `arrow_step_4` |
| Step 5, p. 798 | `S` or `I \ S` decisive | `arrow_step_5` |
| Step 6, p. 798 | `∅` not decisive; supersets of decisive sets decisive | `arrow_empty_not_decisive`, `arrow_step_6` |
| Step 7, p. 798 | Decisive set with `≥ 2` agents has a decisive strict subset | `arrow_step_7` |
| Step 8, p. 798 | A decisive singleton exists | `arrow_step_8` |
| Step 9, pp. 798-799 | Decisive ⇒ completely decisive (proof repaired, see corrections) | `arrow_step_9`, `pairTop` |
| Step 10, p. 799 | Decisive singleton is a dictator | `arrow_step_10` |

## Section 21.D: restricted domains

| Source | Claim | Lean |
| --- | --- | --- |
| Section 21.D, p. 799 | Agenda: with Condorcet preferences the last alternative always survives | `pairWinner`, `agendaWinner`, `condorcet_agenda` |
| Definition 21.D.1(i), p. 800 | Quasitransitive | `Quasitransitive` |
| Definition 21.D.1(ii), p. 800 | Acyclic (corrected: nonempty finite sets) | `Acyclic`, `AcyclicAsPrinted`, `acyclic_as_printed_false` |
| Section 21.D and footnote 9, p. 800 | Quasitransitive ⇒ acyclic; rational ⇒ quasitransitive; converses fail | `footnote_21_9_acyclic`, `rational_quasitransitive`, `rational_acyclic`, `exercise_21_D_2_not_transitive`, `exercise_21_D_3_not_quasitransitive` |
| Section 21.D, p. 800 | Condorcet social preferences violate acyclicity | `condorcet_not_acyclic` |
| Example 21.D.1 (oligarchy), p. 800 | Definition; strict iff all oligarchs strict; Paretian, independent; `{h}` dictatorship, `I` unanimity; only transitivity fails | `oligarchyRel`, `example_21_D_1_strict`, `example_21_D_1_paretian_independent`, `example_21_D_1_extremes`, `example_21_D_1_not_dictatorial` |
| Example 21.D.2 (vetoers), pp. 800-801 | Definition | `vetoRel`, `vetoRel_strict` |
| Definition 21.D.2, p. 801 | Linear order | `IsLinearOrderRel`, `linearOrderRel_of_linearOrder`, `linearOrderRel_dual`, `linearOrderOfRel` |
| Example 21.D.3, p. 801 | `X ⊆ ℝ` with `≥` | `example_21_D_3` |
| Definition 21.D.3, p. 801 | Single peaked; the peak is the unique best alternative | `IsPeak`, `SinglePeaked`, `IsPeak.strict_best`, `IsPeak.unique` |
| Example 21.D.4, p. 801 | Continuous `≿` on `[a,b]` single peaked iff strictly convex | `example_21_D_4`, `example_21_D_4_sufficiency`, `exercise_21_D_4`, `example_21_D_4_empty`, `iccComb`, `StrictlyConvexPref`, `ContinuousPref`, `exists_max_of_continuousPref` |
| Example 21.D.4, p. 801 | Strictly quasiconcave utility gives strictly convex preference | `strictlyConvex_of_strictQuasiconcave` |
| Figures 21.D.1-21.D.2, p. 802 | Single-peaked / not single-peaked utility graphs | Listed only (graphical) |
| Definition 21.D.4, p. 801 | `𝓡_≥`; domains `𝓡_≥^I`, `𝓟_≥^I` | `SinglePeakedPrefs`, `StrictSinglePeakedPrefs`, `SinglePeakedProfiles`, `StrictSinglePeakedProfiles`, `strictSinglePeaked_subset`, `strictSinglePeaked_subset_strict` |
| Section 21.D, p. 802 | Pairwise majority `F̂` complete on any domain | `majorityRel_complete` |
| Section 21.D, p. 802 | Condorcet winner | `IsCondorcetWinner` |
| Definition 21.D.5, p. 802 | Median agent; exists (needs `I ≥ 1`) | `IsMedianAgent`, `median_exists` |
| Section 21.D, p. 802 | No ties, `I` odd: `(I-1)/2` below and above, unique median | `median_odd_unique` |
| Figure 21.D.3, p. 803 | Determination of a median | Listed only (graphical) |
| Proposition 21.D.1, p. 802 | Median peak is a Condorcet winner (strict with odd `I`); existence | `proposition_21_D_1`, `proposition_21_D_1_exists`, `majority_of_supporters`, `proposition_21_D_1_instance` |
| Section 21.D, p. 803 | `F̂` is acyclic on `𝓡_≥^I` | `majorityRel_acyclic`, `IsPeak.restrict`, `strict_singlePeaked_condorcet_finset`, `tieBreak`, `tieBreak_spec`, `doubleProfile`, `doubleProfile_card`, `majorityRel_doubleProfile`, `doubleProfile_mem` |
| Section 21.D, p. 803 | Odd `I`, `𝓟_≥`: strict majority for one of each pair; Condorcet winner defeats every other alternative | `strict_majority_odd`, `proposition_21_D_1` (second part), `condorcetWinner_unique` |
| Proposition 21.D.2, p. 803 | Odd `I`: majority voting is a SWF on `𝓟_≥^I` (values in `𝓟`) | `proposition_21_D_2` |
| Section 21.D, p. 804 | One-dimensional single-peakedness from quasiconcavity | `example_21_D_4`, `strictlyConvex_of_strictQuasiconcave` |
| Example 21.D.5, p. 804 | Cases (i)-(iii); no Condorcet winner | `ex21D5u`, `unitSquare`, `example_21_D_5_i`, `example_21_D_5_ii`, `example_21_D_5_iii`, `example_21_D_5` |
| Example 21.D.5, pp. 804-805 | Single maximal elements; gradient cone is `ℝ²` | `example_21_D_5_unique_max`, `example_21_D_5_cone` |
| Footnote 10, p. 804 | Preferences not strictly convex; immaterial | Listed only (remark) |
| Figure 21.D.4, p. 804 | Indifference curves | Listed only (graphical) |
| Example 21.D.6, p. 805 | Euclidean preferences; peak identifies the preference | `euclidPref`, `euclidPref_spec`, `euclidPref_injective` |
| Footnote 11, p. 805 | Grandmont, Exercise 21.D.9 | `exercise_21_D_9f` |
| Example 21.D.6, Figure 21.D.6, p. 805 | `A(y,z)`; open half-space; boundary is the perpendicular bisector | `prefRegion`, `strict_euclidPref_iff`, `mem_prefRegion_iff`, `prefRegion_eq_halfspace`, `bisector_iff`, `disjoint_prefRegion` |
| Example 21.D.6, Figure 21.D.7, pp. 805-806 | Median ⇔ Condorcet winner | `openHalfSpace`, `measurableSet_openHalfSpace`, `disjoint_openHalfSpace`, `IsMedianPoint`, `IsCondorcetWinnerMeasure`, `isMedianPoint_iff_book`, `example_21_D_6`, `example_21_D_6_instance` |
| Figures 21.D.5, p. 805 | Euclidean indifference curves | Listed only (graphical) |
| Figure 21.D.8(a), p. 806 | Centre of a rectangle is a median of the uniform distribution | `isMedianPoint_of_symmetric`, `measurePreserving_reflect`, `rectangle`, `figure_21_D_8a`, `figure_21_D_8a_center` |
| Figure 21.D.8(b), p. 806 | Uniform distribution on a triangle has no median (every triangle; the three lines through the point parallel to the sides cannot all bisect the area) | `isMedianPoint_of_affine_image`, `stdTriangle`, `triangle_coords_measurePreserving`, `triangle_strip_volume`, `stdTriangle_eq_preimage`, `stdTriangle_median_coord`, `triSwapLin`, `triShearLin`, `triSwapLin_involutive`, `triShearLin_involutive`, `stdTriangle_median_three`, `figure_21_D_8b`, `figure_21_D_8b_affine` |
| Footnote 12, p. 806 | Caplin-Nalebuff `1 - 1/e` result | Listed only (cited literature) |

## Section 21.E: social choice functions

| Source | Claim | Lean |
| --- | --- | --- |
| Definition 21.E.1, p. 807 | Social choice function `f : 𝒜 → X` | functions `Profile ι X → X` |
| Footnotes 13-14, p. 807 | Single-valuedness; comparison with Section 1.C | Listed only (remarks) |
| Section 21.E, p. 807 | Finite `X`: every SWF induces a SCF; with single peaks, odd `I`, the Condorcet winner | `induced_scf_exists`, `induced_scf_condorcet` |
| Definition 21.E.2, p. 808 | Weakly Paretian | `WeaklyParetian` |
| Definition 21.E.3 and footnote 15, p. 808 | Maintains its position; lower contour sets | `MaintainsPosition`, `lowerContour`, `maintainsPosition_iff` |
| Definition 21.E.4, p. 808 | Monotonic | `Monotonic` |
| Definition 21.E.5, p. 808 | Dictator; dictatorial | `IsSCFDictator`, `DictatorialSCF` |
| Section 21.E, p. 808 | On `𝓟^I` a dictatorial SCF is weakly Paretian and monotonic | `dictatorial_strict_spec` |
| Proposition 21.E.1, p. 809 | Weakly Paretian + monotonic on `𝓡^I`/`𝓟^I`, `≥ 3` alternatives: dictatorial | `proposition_21_E_1` |
| Definition 21.E.6, p. 809 | Takes `X'` to the top; example; elements of `X'` maintain position | `TakesToTop`, `topProfile`, `topProfile_spec`, `definition_21_E_6_example`, `TakesToTop.maintains`, `TakesToTop.trans` |
| Step 1, p. 809 | Same choice at profiles taking `X'` to the top | `scf_step_1`, `WeaklyParetian.mem_top` |
| Step 2, p. 809 | Definition of `F`; well defined | `scfRelation`, `scf_step_2`, `StandardDomain.topProfile_mem` |
| Step 3, pp. 809-810 | `F(≿) ∈ 𝓟` | `scf_step_3`, `scf_choice_pair`, `scf_not_chosen` |
| Step 4, p. 810 | `F` rationalizes `f` | `scf_step_4` |
| Step 5, p. 810 | `F` Paretian | `scf_step_5` |
| Step 6, p. 810 | `F` pairwise independent | `scf_step_6` |
| Step 7, pp. 810-811 | `f` dictatorial | `proposition_21_E_1` |
| Proposition 21.E.2, p. 811 | Weakly Paretian, no incentive to misrepresent on `𝓟^I`: dictatorial | `NoIncentiveToMisrepresent`, `no_incentive_step`, `monotonic_of_noIncentive`, `proposition_21_E_2` |
| Proposition 21.E.2, non-vacuity | A dictatorial rule with no incentive to misrepresent | `smallestTopLabel_noIncentive` |

## Exercises

| Source | Claim | Lean |
| --- | --- | --- |
| Exercise 21.B.1, p. 812 | Majority voting has the three properties | `exercise_21_B_1`, `exercise_21_B_1_symmetric`, `exercise_21_B_1_neutral`, `exercise_21_B_1_responsive` |
| Exercise 21.B.2, p. 812 | Rule without symmetry | `tiltedVoting`, `exercise_21_B_2_symmetry` |
| Exercise 21.B.2, p. 812 | Rule without neutrality | `xBiasedVoting`, `exercise_21_B_2_neutrality` |
| Exercise 21.B.2, p. 812 | Rule without positive responsiveness | `exercise_21_B_2_responsiveness` |
| Exercise 21.B.3, p. 812 | Majority Pareto optimal without transfers | `ParetoOptimalNoTransfers`, `MajorityDecision`, `exercise_21_B_3_pareto_no_transfers` |
| Exercise 21.B.3, p. 812 | Not Pareto optimal with transfers | `FeasibleWithTransfers`, `ParetoOptimalWithTransfers`, `exercise_21_B_3_not_pareto_with_transfers` |
| Exercise 21.B.3, p. 812 | Median vs mean ("compare and contrast") | `exercise_21_B_3_mean` (Pareto with transfers iff `∑ vᵢ` sign); comparison listed only |
| Exercise 21.C.1, p. 812 | Second half of Step 1 | `exercise_21_C_1` |
| Exercise 21.C.2(a), p. 812 | Two alternatives | `exercise_21_C_2a`, `majorityRel_paretian`, `majorityRel_independent`, `majorityRel_not_dictatorial`, `splitProfile` |
| Exercise 21.C.2(b), p. 812 | Restricted domain | `exercise_21_C_2b` |
| Exercise 21.C.2(c), p. 812 | No social rationality | `exercise_21_C_2c` |
| Exercise 21.C.2(d), p. 812 | No pairwise independence (Borda) | `exercise_21_C_2d` |
| Exercise 21.C.2(e), p. 812 | No Pareto (total indifference) | `totalIndifference`, `exercise_21_C_2e` |
| Exercise 21.C.2(f), p. 812 | Dictatorship | `exercise_21_C_2f` |
| Exercise 21.C.3, p. 812 | Lexical dictatorship: rational, Paretian, independent, dictator; not identical to any individual | `lexRel`, `exercise_21_C_3_rational`, `exercise_21_C_3_arrow`, `exercise_21_C_3_not_identical` |
| Exercise 21.D.1, p. 812 | Max on every nonempty strict subset, not acyclic (corrected) | `cyclicRel`, `exercise_21_D_1` |
| Exercise 21.D.2, p. 812 | Oligarchy quasitransitive; indifference not transitive; interpretation | `exercise_21_D_2_quasitransitive`, `exercise_21_D_2_not_transitive`; interpretation listed only |
| Exercise 21.D.3, p. 813 | Vetoers acyclic, not quasitransitive; `x` the only maximal alternative | `exercise_21_D_3_acyclic`, `exercise_21_D_3_not_quasitransitive` |
| Exercise 21.D.4, p. 813 | Single peaked ⇒ strictly convex | `exercise_21_D_4` |
| Exercise 21.D.5, p. 813 | Condorcet preferences single peaked for no linear order | `exercise_21_D_5`, `three_middle`, `IsPeak.middle_not_worst` |
| Exercise 21.D.6, p. 813 | Even number of agents, intransitive majority | `exercise21D6Profile`, `exercise_21_D_6`, `natPref_singlePeaked_of_isPeak` |
| Exercise 21.D.7(a), p. 813 | Condorcet cycle near a spanning gradient cone | `exercise_21_D_7a`, `cone_directions`, `eventually_gradient_lt`, `area_antisymm`, `area_self`, `TwoAgentsPrefer`, `exercise_21_D_7_instance`, `hasGradientAt_inner_const` |
| Exercise 21.D.7(b), p. 813 | Majority move towards any `x ≠ 0` (corrected: `x ≠ 0`; no linearity needed) | `exercise_21_D_7b`, `exercise_21_D_7b_zero` |
| Exercise 21.D.8(a), p. 813 | Directional median agent for a pointed cone (first-order notion); sharp form: exists iff the cone is not the plane | `IsDirectionalMedian`, `ConeContainsHalfSpace`, `dm_three_term`, `dm_binet_cauchy`, `dm_not_median`, `dm_spans_of_relation`, `dm_median_or_spans`, `dm_spans_no_median`, `exercise_21_D_8a`, `exercise_21_D_8a_iff`, `not_coneContainsHalfSpace_of_pos`, `exercise_21_D_8a_instance` |
| Exercise 21.D.8(a), p. 813 | Literal (global, utility-level) reading false, even for concave utilities | `IsGlobalDirectionalMedian`, `e218aUtil`, `exercise_21_D_8a_global_counterexample` |
| Exercise 21.D.8(b), p. 813 | Changing median; Condorcet cycles possible (Euclidean utilities on a half-plane, pointed cone everywhere) | `e218bPeak`, `e218bUtil`, `e218bGrad`, `e218bUtil_eq`, `e218bUtil_concave`, `e218bUtil_hasGradientAt`, `exercise_21_D_8b` |
| Exercise 21.D.8(c), p. 813 | Same directional median everywhere ⇒ no cycle: linear utilities (first-order notion) | `exercise_21_D_8c`, `exercise_21_D_8c_instance` |
| Exercise 21.D.8(c), p. 813 | Same, literal notion, arbitrary utilities on any `X` | `exercise_21_D_8c_global`, `exercise_21_D_8c_global_instance` |
| Exercise 21.D.8(c), p. 813 | Same, first-order notion, nonlinear utilities: false (concave counterexample with a cycle) | `e218c_hasDerivAt_sqPos`, `e218cUtil`, `e218cGrad`, `exercise_21_D_8c_counterexample` |
| Exercise 21.D.9(a), p. 813 | `ψu + γu'` intermediate | `Intermediate`, `exercise_21_D_9a` |
| Exercise 21.D.9(b), p. 813 | `B(x,y)` is `ℝ^N_{++}` ∩ half-space | `linParamUtil`, `exercise_21_D_9b` |
| Exercise 21.D.9(c), p. 814 | False as printed; corrected statement and counterexample | `exercise_21_D_9c`, `e219Family`, `exercise_21_D_9c_counterexample` |
| Exercise 21.D.9(d), p. 814 | Median agent may exist | `exercise_21_D_9d_exists` |
| Exercise 21.D.9(d), p. 814 | ... or not exist (uniform density on a triangle in `ℝ²_{++}`) | `exercise_21_D_9d_not_exists` |
| Exercise 21.D.9(e), p. 814 | Median agent's top alternative defeats every other | `exercise_21_D_9e`, `exercise_21_D_9e_instance` |
| Exercise 21.D.9(f), p. 814 | Euclidean preferences in this framework | `exercise_21_D_9f`, `exercise_21_D_9f_intermediate` |
| Exercise 21.D.10(a), p. 814 | Interpret `w̄` vs `w*` | Listed only (interpretation) |
| Exercise 21.D.10(b), p. 814 | Single peaked (except `wᵢ = w̄`, corrected); `t_c = 0` or `1` | `TaxRates`, `wealthPref`, `wealthPref_iff`, `wealthPref_strict_iff`, `wealthPref_rational`, `isPeak_zero`, `isPeak_one`, `wealthB`, `exercise_21_D_10b_singlePeaked`, `exercise_21_D_10b_mean_agent`, `exercise_21_D_10b_condorcet`; interpretation listed only |
| Exercise 21.D.10(c), p. 814 | Single peaked; `t_c ≤ 1/2`; `t_c = 0` vs `> 0` | `wealthC`, `peakC`, `peakC_mem`, `peakCRate`, `peakC_antitone`, `exercise_21_D_10c_singlePeaked`, `exercise_21_D_10c`; comparison listed only |
| Exercise 21.D.10(d), p. 814 | False: preferences remain single peaked | `wealthD`, `wealthD_strictQuasiconcave`, `exercise_21_D_10d` |
| Exercise 21.D.11, p. 814 | Odd oligarchy majority is Paretian, independent, into `𝓟`; another such functional | `oligarchyMajority`, `exercise_21_D_11_oligarchy`, `phantomUtil`, `withPhantoms`, `phantomMajority`, `phantom_mem`, `phantomTestA`, `phantomTestB`, `exercise_21_D_11` |
| Exercise 21.D.12(a), p. 815 | No strictly positive Condorcet winner | `taxShares`, `taxDefeats`, `taxDefeats_iff`, `exercise_21_D_12a` |
| Exercise 21.D.12(b), p. 815 | Discussion of boundary alternatives (made precise) | `exercise_21_D_12b_one_zero`, `exercise_21_D_12b_one_payer` |
| Exercise 21.D.13(a), p. 815 | `J` odd, equal masses: Condorcet winner is a peak; not for `J` even | `typeMass`, `IsTypeCondorcetWinner`, `eventually_small_step`, `condorcet_halfplane`, `complex_inner_eq`, `exists_generic_direction`, `exercise_21_D_13a`, `exercise_21_D_13a_even`, `exercise_21_D_13a_instance` |
| Exercise 21.D.13(b), p. 815 | De Marzo: dominant type's peak | `GeneralPosition`, `inner_I_mul`, `collinear_of_orth`, `exercise_21_D_13b`, `exercise_21_D_13b_instance` |
| Exercise 21.D.14(a), p. 815 | No Condorcet winner | `e2114`, `exercise_21_D_14a` |
| Exercise 21.D.14(b), p. 815 | Weakly increasing towards the peak | `WeaklySinglePeaked`, `exercise_21_D_14b` |
| Exercise 21.D.14(c), p. 815 | Points of `[0,1]`, quasiconcave utilities | `e2114u`, `e2114pos`, `quasiconcaveOn_of_unimodal`, `exercise_21_D_14_quasiconcave`, `exercise_21_D_14c` |
| Exercise 21.D.14(d), p. 815 | Interval example without Condorcet winner | `e2114Defeats`, `exercise_21_D_14d`, `exercise_21_D_14_quasiconcave` |
| Exercise 21.E.1, p. 815 | Condorcet-winner SCF weakly Paretian, monotonic | `condorcetSCF`, `condorcetWinner_unique`, `exercise_21_E_1` |
| Exercise 21.E.2, p. 816 | Smallest-label rule on `𝓡^I`: dictatorial, weakly Paretian, *not* monotonic (corrected); on `𝓟^I` all three | `smallestTopLabel`, `smallestTopLabel_spec`, `exercise_21_E_2_dictatorial`, `exercise_21_E_2_not_monotonic`, `exercise_21_E_2_strict` |
| Exercise 21.E.3, p. 816 | `{y, z}` case of Step 3 | `exercise_21_E_3` |
| Exercise 21.E.4, p. 816 | Two alternatives, `𝒜 = 𝓟^I` | `parityRule`, `exercise_21_E_4_two` |
| Exercise 21.E.4, p. 816 | More than two alternatives, small `𝒜` | `e214A`, `e214B`, `e214F`, `exercise_21_E_4_three` |
