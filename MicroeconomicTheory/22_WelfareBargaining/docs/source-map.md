# Source map

Mas-Colell, Whinston and Green, *Microeconomic Theory*, Chapter 22, "Elements of Welfare
Economics and Axiomatic Bargaining", pp. 817-856 (Sections 22.A-22.F, Exercises 22.B.1-22.F.7).
Printed pages; Lean names relative to `MWG.WelfareBargaining`. Rational preferences are Kreps's
`Rational`; Chapter 21's social welfare functionals, Pareto, pairwise independence and
dictatorship are imported from `MWGSocialChoice`; Chapter 10's economies and utility
possibility set from `MWGCompetitiveMarkets`; Example 3.C.1 (lexicographic order not
representable) from `MWGClassicalDemand`; Example 9.AA.2 (Rubinstein's theorem) from
`MWGDynamicGames`. No Mathematical Appendix section belongs to this
chapter. Items marked **OPEN** are not formalized; the reason is given. Remaining OPEN item: Debreu's separability theorem (p. 838) without the added unrestricted-solvability hypothesis (the theorem itself is proved with that hypothesis and with strict increase in each agent's utility, correction 17).

## Sections 22.A-22.B

| Source | Claim | Lean |
| --- | --- | --- |
| 22.A, p. 817 | Introduction | Listed only (exposition) |
| Def. 22.B.1, p. 818 | Utility possibility set; Pareto frontier | `ups`, `IsParetoFrontier` |
| Ex. 22.B.1, p. 818 | UPS of the exchange/production economies of Ch. 10 | `ups_economy` |
| Exercise 22.B.1, p. 850 | Convex `Xᵢ`, `Yⱼ`, concave `uᵢ` ⇒ convex UPS | `exercise_22_B_1` |
| Ex. 22.B.1, p. 818 | Quasilinear UPS boundary is a hyperplane | Ch. 10 (`MWGCompetitiveMarkets`, Section 10.D); listed |
| Ex. 22.B.2, p. 820 | Ramsey FOCs, (22.B.1) | `exercise_22_B_2_ramsey` (`λ > 1`, `α = (λ-1)/λ ∈ (0,1)`), `example_22_B_2_correction` (instance; correction 1) |
| Exercise 22.B.2, p. 850 | Derive the FOCs in general | `exercise_22_B_2` (Mathlib's Lagrange multiplier theorem plus a sign argument; `λ ≥ 0`), `exercise_22_B_2_instance` |
| Ex. 22.B.3, p. 821; Exercise 22.B.3 | (22.B.2), compensatory distortion `p̄₂ ≠ 1` | `exercise_22_B_3`, `example_22_B_3`, `example_22_B_3_instance` |
| Ex. 22.B.4, p. 821; Exercise 22.B.4 | Second-best UPS; may be nonconvex; frontier on a one-parameter curve | `secondBestUPS`, `exercise_22_B_4`, `exercise_22_B_4_demand`, `unitDemand`, `example_22_B_4_frontier` |
| Ex. 22.B.5, p. 822 | Indivisibility and externality nonconvexities | `example_22_B_5_locations`, `example_22_B_5_externality` |
| p. 823 | Randomization convexifies the UPS | `randomizedUPS`, `mem_randomizedUPS`, `randomized_convex`, `randomized_locations` |
| Ex. 22.B.6, pp. 823-824 | Unproductive taxation: leisure choice, first-best frontier, `Q` not monotone | `example_22_B_6_leisure`, `taxLocus`, `firstBestUPS`, `example_22_B_6_firstBest`, `taxLocus_mem_firstBest`, `example_22_B_6_nonmonotone` (`a = 1/4`) |
| Footnote 7, p. 824 | Only `t = 0` gives a first-best outcome | `footnote_22_7` |
| Footnote 6, p. 824 | Second-best frontier may or may not be convex | Listed only (remark) |
| Footnotes 1-5 | References, remarks | Listed only |

## Section 22.C

| Source | Claim | Lean |
| --- | --- | --- |
| (22.C.1), p. 825 | Social optimum | `IsSocialOptimum` |
| Properties (i)-(ii), p. 825 | Paretian, strictly Paretian; optimum is Pareto optimal | `IsIncreasingSWF`, `IsStrictlyParetian`, `socialOptimum_pareto` |
| Property (iii), p. 826 | Symmetry | `IsSymmetricSWF` |
| Property (iv), p. 826 | Concavity and inequality aversion | `concave_inequality_aversion` |
| p. 826, Exercise 22.C.1 | Symmetric convex `U`, symmetric strictly concave `W` ⇒ egalitarian optimum; strictly convex `U` variant | `exercise_22_C_1`, `exercise_22_C_1_strictConvex` |
| Ex. 22.C.1, p. 827 | Utilitarian strictly Paretian; equal split of wealth | `example_22_C_1_3`, `example_22_C_1_equal_split` |
| Ex. 22.C.1, p. 827 | Equalization of marginal utilities; uniqueness | `example_22_C_1_marginal`, `example_22_C_1_unique`, `example_22_C_1_instance` |
| Ex. 22.C.2, p. 827-828 | Maximin Paretian, not strictly; equal-coordinate PO point is optimal | `example_22_C_2_paretian`, `example_22_C_2_equal` |
| Footnote 11, pp. 827-828 | Maximin optimum not Pareto optimal; leximin | `footnote_22_11_example`, `leximin2` |
| Ex. 22.C.3, p. 828 | Generalized utilitarian strictly Paretian, concave | `example_22_C_1_3` |
| Ex. 22.C.4, p. 829 | `g_ρ`, constant elasticity `ug''/g' = -ρ`; `W_ρ` represents `∑ g_ρ`; `W₀ = ∑ uᵢ` | `cesG`, `cesW`, `example_22_C_4_elasticity`, `example_22_C_4_h`, `example_22_C_4_represent`, `cesW_zero`, `example_22_C_4_printed_h` (correction 8) |
| Exercise 22.C.5, p. 851 | `W_ρ(u) → min uᵢ` as `ρ → ∞` | `exercise_22_C_5` |
| Compensation principle, pp. 829-831 | Strong/weak tests, paradox (Fig. 22.C.7) | `StrongCompensation`, `WeakCompensation`, `compensation_paradox` |
| Exercise 22.C.2(a) | Veil of ignorance (verbal) | Listed only |
| Exercise 22.C.2(b) | Symmetric additive utility: `uᵢ = u_{i₀} + cᵢ` | `exercise_22_C_2b`, `exercise_22_C_2b_instance` |
| Exercise 22.C.3(a) | Symmetric two-outcome lotteries all indifferent | `exercise_22_C_3a` (discussion verbal) |
| Exercise 22.C.3(b) | `N = 3`, `I = 2` illustration | Listed only (graphical) |
| Exercise 22.C.3(c) | Pareto determines the map / any `U` Paretian / not determined in general | `exercise_22_C_3c_unique`, `exercise_22_C_3c_unique_instance`, `exercise_22_C_3c_any`, `exercise_22_C_3c_not_unique` |
| Exercise 22.C.3(d) | Harsanyi's theorem (`I = 2`, any `N`) | `exercise_22_C_3d` (corrected), `exercise_22_C_3d_instance`, `exercise_22_C_3d_constant`, `exercise_22_C_3d_opposed` (correction 10); `HarsanyiParetian`, `eu`, `lotteries`; any number of individuals: `exercise_22_C_3d_general`, `harsanyi_direction_gen`, `exercise_22_C_3d_general_instance` (Farkas's lemma `MWG.Production.farkas`, imported from Chapter 5) |
| Exercise 22.C.4(a)-(c) | Leximin refines maximin; not representable; leximin optimum PO | `I = 2`: `exercise_22_C_4a`, `exercise_22_C_4b`, `exercise_22_C_4c`; any `I`: `sortVec`, `leximin`, `sortVec_le_sortVec`, `exercise_22_C_4a_general`, `exercise_22_C_4b_general` (`I ≥ 2`), `exercise_22_C_4c_general`, `exercise_22_C_4c_instance` |
| Exercise 22.C.6(a) | Strong test passed yet utilitarian-worse outcome | `exercise_22_C_6a` |
| Exercise 22.C.6(b) | Quasilinear: weak ⇒ strong test, utilitarian improvement; fails for maximin | `qlUPS`, `qlUPS_pareto`, `exercise_22_C_6b`, `exercise_22_C_6b_instance`, `exercise_22_C_6b_maximin` |
| Exercise 22.C.7 | Edgeworth box economies passing the weak test over each other's equilibrium | `Exchange22`, `exercise_22_C_7_same_total`, `econA`, `econB`, `exercise_22_C_7` (correction 12) |
| Exercise 22.C.8(a)-(c) | Kaldor test: (a) graphical; (b) asymmetric; (c) not transitive | `Kaldor`, `exercise_22_C_8b`, `exercise_22_C_8c`; (a) listed |

## Section 22.D

| Source | Claim | Lean |
| --- | --- | --- |
| Defs. 22.D.1-22.D.3, p. 832 | SWF on utility profiles; Pareto; pairwise independence | `IsUSWF`, `UParetian`, `UPairwiseIndependent`, `GeneratedBy`, `swfFunctional` |
| p. 832 | Generated ⇒ pairwise independent | `generatedBy_pairwiseIndependent` |
| Prop. 22.D.1, p. 833 (proof, footnote 17) | Generation by a rational relation on `ℝ^I` | `proposition_22_D_1`, `pairRel_replace_snd`, `footnote_22_17` |
| Exercise 22.D.1(a)-(c) | Each hypothesis indispensable | `exercise_22_D_1a`, `exercise_22_D_1b`, `exercise_22_D_1c` |
| Exercise 22.D.2 | Replacement `(x, y) → (z, y)` | `exercise_22_D_2` |
| Exercise 22.D.3 | Generating relation is monotone | `exercise_22_D_3` (correction 7) |
| p. 834 | Lexical dictatorship not representable | `exercise_22_D_4b_not_generated` |
| Defs. 22.D.4-22.D.5 | Invariance notions | `InvCommonCardinal`, `InvCommonOrigins`, `InvCommonUnits`, `NoInterpersonalComparisons`, `InvIndepOrigins`, `InvIndepUnits`, `invCommonCardinal_iff`, `noInterpersonalComparisons_iff` |
| p. 834 | Common origins ⇒ parallel indifference sets | `common_origin_parallel`, `transfer_invariance` |
| Prop. 22.D.2, p. 835 | Form (22.D.1); homogeneity of `g` | `proposition_22_D_2`, `eqLevel_spec`, `eqLevel_add_const` |
| Prop. 22.D.3, p. 837 | Utilitarian form; dictatorship | `proposition_22_D_3`, `indiff_midpoint`, `proposition_22_D_3_dictatorial` |
| p. 837 | Dictatorship for a generating relation | `proposition_22_D_3_relation`, `dictator_of_invariant_relation` |
| p. 837, Exercise 22.D.5 | Arrow via invariance | `inducedFunctional`, `exercise_22_D_5_isUSWF`, `exercise_22_D_5_strict`, `exercise_22_D_5_pairwise`, `exercise_22_D_5_noInterpersonal`, `exercise_22_D_5_dictator`, `exercise_22_D_5` (correction 2) |
| Exercise 22.D.4(a)-(c) | Lexical dictatorship | `exercise_22_D_4a`, `exercise_22_D_4b_single`, `exercise_22_D_4b_not_generated`, `exercise_22_D_4c` |
| Exercise 22.D.6(a)-(e) | Form (22.D.1) | `exercise_22_D_6a`, `exercise_22_D_6b_counterexample`, `exercise_22_D_6b` (correction 3), `exercise_22_D_6c`, `exercise_22_D_6c_nonsymmetric`, `exercise_22_D_6d`, `exercise_22_D_6e` |
| Exercise 22.D.7(a) | CES functionals invariant to common units | `cesFunctional`, `PosProfile`, `InvCommonUnitsPos`, `exercise_22_D_7a`, `cesSum_smul` (correction 13) |
| Exercise 22.D.7(b) | Only `ρ = 0`, `ρ = ∞` invariant to common origins | `exercise_22_D_7b` (`0 < ρ < ∞` not invariant), `exercise_22_D_7b_utilitarian`, `exercise_22_D_7b_rawls`, `InvCommonOriginsPos`, `cesG_midpoint` |
| Small type, p. 838 | Common ordinal invariance (min) | `InvCommonOrdinal`, `exercise_22_D_8ab` |
| Small type, p. 838 | Independence of irrelevant individuals; additively separable ⇒ independent | `IndepIrrelevantIndividuals`, `additive_independent_irrelevant` |
| Small type, p. 838 | Debreu: continuous, increasing, independent of irrelevant individuals, `I > 2` ⇒ additively separable up to an increasing transformation | Proved with corrected and added hypotheses (correction 17): `debreu_separability` (`2 < card ι`, `W` continuous, `IsStrictlyIncreasingEach`, `IndepIrrelevantIndividuals`, `IsSolvableSWF` ⇒ continuous strictly increasing `gᵢ` with `W u ≤ W u' ↔ ∑ gᵢ(uᵢ) ≤ ∑ gᵢ(u'ᵢ)`), `debreu_separability_transform` (`W = h ∘ ∑ gᵢ`, `h` strictly increasing on the range), `debreu_calibrated`, `isSolvableSWF_of_unbounded`; instances `debreu_hypotheses_utilitarian`, `unbounded_utilitarian`. Proof: merging agents (`deb_merge`, `debOp_triple`, `debOp_change`) and the one-dimensional step `aczel_associativity` (`IsAczelOp`, instance `isAczelOp_add`). **OPEN**: the theorem without `IsSolvableSWF` (sections of `W` may be bounded, e.g. `∑ arctan uᵢ`; this needs local additive representations and their patching) |
| Small type, p. 838 | The claim as printed is false: MWG's "increasing" allows an agent who never matters | `debreu_counterexample_null_agent` (`I = 3`, `W(u) = u₁ + u₂ + min(u₁, u₂)`: continuous, `IsIncreasingSWF`, independent of irrelevant individuals, no additive representation) |
| Small type, p. 838 | Why `I > 2` matters | `debreu_fails_two_agents` (`I = 2`: the same `W` is continuous, strictly increasing in each utility, solvable and independent of irrelevant individuals, `indepIrrelevant_two`, but violates the Thomsen condition, `thomsenSWF_not_additive`) |
| Small type, p. 838 | Maskin | Corrected (correction 4) |
| Ex. 22.D.1, p. 838 | Rational, invariant to independent origins; not pairwise independent (`gᵢ = t³`), hence not generated by any SWF (neither utilitarian nor dictatorial) | `example22D1F`, `example_22_D_1`, `example_22_D_1_not_pairwise`; independence of irrelevant individuals is informal (listed) |
| Exercise 22.D.8(a)-(d) | Rawlsian, anti-Rawlsian, dictatorial invariant; (d) non-invariance and classification | `exercise_22_D_8ab`, `exercise_22_D_8c`, `exercise_22_D_8d`, `exercise_22_D_8d_classification` (dictatorial, Rawlsian or anti-Rawlsian), `exercise_22_D_8d_classification_instance`, `OrdInvVec`, `ordInv_upper` |
| Non-vacuity | Instances of the hypotheses | `proposition_22_D_1_instance`, `proposition_22_D_3_instance`, `proposition_22_D_3_dictatorial_instance` |

## Section 22.E

| Source | Claim | Lean |
| --- | --- | --- |
| p. 839 | Bargaining problem | `BargainingProblem`, `BargainingProblem.isBounded`, `exists_gt` |
| Defs. 22.E.1-22.E.7 | Solution, IUO, IUU, P, S, IR, IIA | `IsBargainingSolution`, `IUO`, `IUU`, `ParetoBS`, `SymmetricBS`, `IndivRational`, `IIA` |
| p. 839 | Normalisation `f(U,u*) = f(U-u*,0)+u*` | `normalize_eq` (correction 6) |
| Ex. 22.E.1, p. 841 | Egalitarian: properties, IIA, maximin, monotone; violates IUU | `egal`, `example_22_E_1`, `egal_maximin`, `egal_monotone`, `egal_not_IUU` |
| Ex. 22.E.2, p. 841 | Utilitarian; unique and IIA for strictly convex `U`; violates IUU | `utilSol`, `example_22_E_2`, `utilPoint_unique_of_strictConvex`, `utilSol_IIA_of_unique`, `utilSol_not_IUU` (correction 5) |
| Ex. 22.E.3, pp. 842-843 | Nash solution: existence, uniqueness, all properties | `nash`, `nashSol`, `exists_nashPoint`, `nashPoint_unique`, `example_22_E_3`, `nashPoint_strong_pareto` |
| Small type, p. 843, footnote 27 | Utilitarian + egalitarian after rescaling ⇒ Nash | `nash_of_utilitarian_egalitarian`, `nash_foc` |
| Prop. 22.E.1, pp. 843-844 | Nash characterization | `proposition_22_E_1`, `simplexProblem_value` |
| Footnote 28 | IR implied | `footnote_22_28` |
| Ex. 22.E.4, p. 844, footnote 29 | Kalai-Smorodinsky: properties; differs from Nash; violates IIA | `ks`, `example_22_E_4`, `ks_not_IIA` |
| Small type (i), p. 845 | Linearity fails for egalitarian, Nash, Kalai-Smorodinsky; sequential settlement under IUO | `linearity_fails`, `box13_add_symHalf`, `sequential_settlement`; "only the modified utilitarian solution" is informal (listed) |
| Small type (ii), p. 845 | Monotonicity: egalitarian yes; others no (Fig. 22.E.9) | `MonotoneBS`, `egal_monotone`, `egal_monotoneBS`, `not_monotone_nash_ks_util` |
| Small type (iii), pp. 845-846 | Consistency; utilitarian and Nash consistent | `IsGUMax`, `reduceSet`, `exercise_22_E_7`, `nash_isGUMax`; Lensberg's characterization is a citation (listed) |
| Exercise 22.E.1 | IUO, P, S, IR of the four solutions | `example_22_E_1`, `example_22_E_2`, `example_22_E_3`, `example_22_E_4` |
| Exercise 22.E.2 | Nonsymmetric versions | `nashSol` (weighted Nash) with `nashSol_IUO`, `nashSol_IUU`, `nashSol_pareto`, `nashSol_IR`, `nashSol_IIA`; rest verbal |
| Exercise 22.E.3(a)-(b) | Tangent-midpoint geometry; Nash simultaneously utilitarian and egalitarian | `exercise_22_E_3a_tangent`, `exercise_22_E_3a_converse`, `exercise_22_E_3b` |
| Exercise 22.E.4 | KS satisfies IUU, violates IIA | `ks_IUU`, `ks_not_IIA` |
| Exercise 22.E.5(a) | Egalitarian is the only IUO, Paretian, symmetric, monotone solution | `exercise_22_E_5a`, `exercise_22_E_5a_instance`, `exists_pos_supporting`, `sym_box` |
| Exercise 22.E.5(b) | Strong monotonicity ⇒ solution on a strictly increasing curve from the origin (`I = 2`) | `StrongMonotoneBS`, `solutionCurve`. False as stated: `exercise_22_E_5b_needs_IR` (egalitarian from threat point `(-1, 0)`: IUO, Paretian, strongly monotonic, values on `u₂ = u₁ + 1`, one with a negative coordinate). Corrected with individual rationality: `exercise_22_E_5b` (values `≫ 0`, strictly ordered chain, points arbitrarily close to the origin, `f(U)` the unique point of the curve on the weak Pareto boundary of `U`, `f(U) - u*` on the curve), `exercise_22_E_5b_instance` (egalitarian); steps `mp_box_fixed`, `mp_box_fixed_aux`, `mp_incomparable`, `mp_strict`, `exercise_22_E_5b_chain` (no IR needed for strictly positive values), `mp_pos`, `egal_strongMonotone`, `addSeg`, `shiftThreat`, `shiftEgal`, `shiftEgal_props` |
| Exercise 22.E.6 | KS characterized by IUO, IUU, P, S, partial monotonicity (`I = 2`) | `PartiallyMonotoneBS`, `ks_partiallyMonotone`, `exercise_22_E_6`, `exercise_22_E_6_instance`, `ksQuad` |
| Exercise 22.E.7 | Generalized utilitarian families are consistent | `exercise_22_E_7`, `isGUMax_unique`, `exercise_22_E_7_instance` |
| Exercise 22.E.8 | Kalai-Smorodinsky is not consistent (three agents) | `ks3`, `ks3red`, `ks_ks3`, `ks_ks3red`, `exercise_22_E_8` |
| Exercise 22.E.9 | Independence of the axioms | `exercise_22_E_9`; violators: `signNash` (IUO, `signNash_props`), `egal` (IUU), threat point (P, `threat_props`), weighted Nash `(1,2)` (S, `weightedNash_props`, `nashSol_halfSpace`), `ks` (IIA) |
| Exercise 22.E.10 | Utilitarian violating IIA | `exercise_22_E_10` |
| Exercise 22.E.11(a) | Stationary SPNE equations; at most one stationary configuration | `IsStationary`, `RubinsteinData`, `stationary_interior`, `exercise_22_E_11a`, `stationary_linear` (instance); existence: `exercise_22_E_11a_exists` (utilities also continuous on `[0, m]`, implied by the book's differentiability; Knaster-Tarski on the monotone map `x ↦ T(x)`), `exercise_22_E_11a_exists_instance` |
| Exercise 22.E.11(b) | `δ → 1`: stationary shares → Nash solution | `exercise_22_E_11b_bracket` (Nash product equal at both proposals, `z*` between them), `exercise_22_E_11b` (shares within `ε` of `z*`), `exercise_22_E_11b_instance` |
| Exercise 22.E.11(c) | Every SPNE payoff configuration is that of a stationary SPNE; uniqueness of Example 9.AA.2 extends to concave, possibly different utilities | `exercise_22_E_11c` (existence of the stationary configuration, its stationary profile `statProfile` is an SPNE, every SPNE has at every feasible history the same utility payoffs), `uSPNE_unique` (in every SPNE the proposer offers the stationary split, it is accepted, payoffs stationary), `exercise_22_E_11c_instance` (`m = 1`, `δ = 1/2`, linear: payoffs `2/3`, `1/3`); game with utility payoffs on the Chapter 9 game form: `uValue`, `uRespValue`, `UIsSPNE`, `uValue_le_of_bound` (one-stage deviation), `statProfile_isSPNE`, Shaked-Sutton bounds `uValue_ge_of_uIsSPNE`, `uValue_le_of_uIsSPNE`, `uValue_frontier`, `fixed_point_bounds`; linear case also via Chapter 9: `exercise_22_E_11c_linear`. Utilities assumed continuous on `[0, m]` (correction 16) |
| Half-space and box computations | Used above | `nash_halfSpace`, `ks_halfSpace`, `ideal_halfSpace`, `nash_box`, `ks_box`, `utilSol_box`, `interHalf` |

## Section 22.F

| Source | Claim | Lean |
| --- | --- | --- |
| p. 846 | Games in characteristic form; equal split in TU bargaining; Exercise 22.F.1 | `Game`, `exercise_22_F_1`, `exercise_22_F_1_threat` |
| Defs. 22.F.1-22.F.5 | Solution, IUO+common units, Pareto, symmetry, dummy | `IsCoopSolution`, `CoopIUO`, `CoopPareto`, `CoopSymmetric`, `CoopDummy` |
| p. 847-848 | Marginal contributions add to `v(I)` | `margContrib`, `sum_margContrib` |
| Def. 22.F.6 | Shapley value | `shapley` |
| Exercise 22.F.2 | Shapley satisfies the properties | `exercise_22_F_2`, `shapley_IUO`, `shapley_pareto`, `shapley_symmetric`, `shapley_dummy` |
| Exercise 22.F.3(a)-(b) | Linearity; (b) interpretation | `exercise_22_F_3a`, `shapley_smul`; (b) verbal |
| Exercise 22.F.4(a)-(c) | Unanimity games; weak linearity ⇒ linearity; uniqueness | `unanimity`, `exercise_22_F_4a`, `exercise_22_F_4b`, `exercise_22_F_4c`, `dividend`, `sum_dividend`, `eq_sum_unanimity` |
| Footnote 31 | Take-it-or-leave-it interpretation | Listed only |
| Cost allocation, pp. 848-849 | Shapley charges each project of a type its average cost | `typeGame`, `shapley_typeGame` |
| Ex. 22.F.1, p. 849 | Shapley split 400/600/600 | `tourCost`, `shapley3`, `shapley3_expand`, `example_22_F_1` |
| Exercise 22.F.5 | Nucleolus definitions (`m₁`, `m₂`) | `pairEx`, `nucC`, `Feas3`, `nucM1`, `nucM2`, `IsNucleolus`, `NucGame`, `pairEx_eq`, `m2_eq_book` |
| Exercise 22.F.5(a) | Three excesses equal, or two equal and the third larger | `exercise_22_F_5a` |
| Exercise 22.F.5(b) | Exactly one nucleolus profile | `exercise_22_F_5b`, `nucleolus_of_equal`, `nucleolus_of_corner` |
| Exercise 22.F.5(c) | Symmetry | `exercise_22_F_5c` |
| Exercise 22.F.5(d) | Dummy gets `0` | `exercise_22_F_5d` |
| Exercise 22.F.5(e) | `v(I)/2 ≤ v(S)` ⇒ equal excesses | `exercise_22_F_5e` |
| Exercise 22.F.5(f) | Shapley `(5/3, 13/6, 13/6)` vs nucleolus `(4/3, 7/3, 7/3)` | `game5f`, `nucGame_game5f`, `exercise_22_F_5f` |
| Exercise 22.F.5(g) | Nonempty core ⇒ nucleolus in core | `IsCore3`, `exercise_22_F_5g` |
| Exercise 22.F.6(a) | MC pricing loses money; AC pricing not first best | `exercise_22_F_6a_loss`, `exercise_22_F_6a_ac`, `exercise_22_F_6a_instance` |
| Exercise 22.F.6(b) | Second-best (break-even) solution | `costEx`, `exercise_22_F_6b` (example; graphical illustration listed) |
| Exercise 22.F.6(c) | Shapley cost per unit = average cost | `exercise_22_F_6c` |
| Exercise 22.F.7(a) | Boiteux FOCs, Ramsey form | `separable_kkt`, `exercise_22_F_7a`, `exercise_22_F_7a_instance` |
| Exercise 22.F.7(b) | Shapley value with many small projects | `exercise_22_F_7b` (exact: average cost of the type) |
| Exercise 22.F.7(c) | Shapley unit-cost prices neither first nor second best | `costEx₂`, `exercise_22_F_7c` |
