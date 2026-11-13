# Kreps Foundations in Lean

A chapter-by-chapter formalization of David M. Kreps, *Microeconomic Foundations I:
Choice and Competitive Markets*. The [proposal](PROPOSAL-KrepsFoundations.md) specifies
all sixteen chapters and eight appendices, following
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming).
The repository also follows the mathematical and provenance practices of
[LeanEconomics/LeanEconomics](https://github.com/LeanEconomics/LeanEconomics);
[PROVENANCE.md](PROVENANCE.md) records the inspected revisions and convention choices.

Each chapter is an independent Lean/Mathlib project pinned to `v4.34.0`, with source
maps, corrections and fresh proof audits. Under `Volume1/`, each directory starts with
its two-digit chapter number. The Lake package and Lean imports use the name after the
underscore, for example `import ChoicePreferenceUtility` for Chapter 1.

| Project | Chapter | Checked results | Start here |
| --- | --- | --- | --- |
| [Volume1/01_ChoicePreferenceUtility](Volume1/01_ChoicePreferenceUtility/README.md) | 1. Choice, Preference, and Utility | 263 theorems / 387 declarations; fresh audit passed | [Chapter overview](Volume1/01_ChoicePreferenceUtility/README.md) |
| [Volume1/02_PreferenceProperties](Volume1/02_PreferenceProperties/README.md) | 2. Structural Properties of Preferences and Utility Functions | 1064 theorems / 1378 declarations; fresh audit passed | [Chapter overview](Volume1/02_PreferenceProperties/README.md) |
| [Volume1/03_ConsumerDemand](Volume1/03_ConsumerDemand/README.md) | 3. Basics of Consumer Demand | 455 theorems / 615 declarations; fresh audit passed | [Chapter overview](Volume1/03_ConsumerDemand/README.md) |
| [Volume1/04_RevealedPreference](Volume1/04_RevealedPreference/README.md) | 4. Revealed Preference and Afriat’s Theorem | 137 theorems / 192 declarations; fresh audit passed | [Chapter overview](Volume1/04_RevealedPreference/README.md) |
| [Volume1/05_ChoiceUnderUncertainty](Volume1/05_ChoiceUnderUncertainty/README.md) | 5. Choice under Uncertainty | 276 theorems / 415 declarations; fresh audit passed | [Chapter overview](Volume1/05_ChoiceUnderUncertainty/README.md) |
| [Volume1/06_UtilityForMoney](Volume1/06_UtilityForMoney/README.md) | 6. Utility for Money | 458 theorems / 629 declarations; fresh audit passed | [Chapter overview](Volume1/06_UtilityForMoney/README.md) |

Counts cover each complete independent project, including attributed local prerequisites.
Declarations include theorems, definitions and generated structure constants. Chapter
overviews and source maps give the breakdown and precise chapter/appendix coverage.

Chapters 1–6 are complete within the scope recorded in their source maps, including
their mathematical exercises, examples and documented corrections. Chapters 5–6
passed source review, full builds, fresh compilation and all declaration axiom
audits on 2026-11-07. The appendix inventories record the foundations covered
by each project. Chapters 7–16 remain planned.

The chapters build on one another through attributed local copies of earlier foundations,
while retaining independent Lake projects. The [cross-chapter checks](consistency/README.md)
compare those copies and jointly compile the six libraries with explicit compatibility
proofs. These connect Afriat rationalization to consumer demand and bundle lotteries
to preferences over income after optimal consumption. CI runs these checks
alongside the individual chapter audits.

## Mas-Colell, Whinston and Green, *Microeconomic Theory*

A second programme formalizes Mas-Colell, Whinston and Green, *Microeconomic Theory*
(Oxford University Press, 1995), chapter by chapter in book order, under
`MicroeconomicTheory/`. The [proposal](PROPOSAL-MicroeconomicTheory.md) gives the
chapter plan and the settled decisions. Each chapter is an independent Lean/Mathlib
project `MicroeconomicTheory/NN_Project/`, with Lake library `MWG<Project>` and namespace
`MWG.<Project>`. It covers every definition, numbered result, example and mathematical
exercise, with source maps, corrections and the same fresh proof audit.

Unlike `Volume1/`, MWG chapters **depend on** earlier material rather than copying it.
They use Lake `path` requirements on Kreps chapters and earlier MWG chapters, and `git`
requirements pinned to a commit for other LeanEconomics repositories. All share the
Mathlib pin above. Each chapter audits only its own modules.

| Project | Chapter | Checked results | Start here |
| --- | --- | --- | --- |
| [MicroeconomicTheory/01_PreferenceChoice](MicroeconomicTheory/01_PreferenceChoice/README.md) | 1. Preference and Choice | 73 theorems / 101 declarations; fresh audit passed | [Chapter overview](MicroeconomicTheory/01_PreferenceChoice/README.md) |
| [MicroeconomicTheory/02_ConsumerChoice](MicroeconomicTheory/02_ConsumerChoice/README.md) | 2. Consumer Choice (with Appendix M.A, M.B, M.D) | 273 theorems / 356 declarations; fresh audit passed; 1 exercise converse open | [Chapter overview](MicroeconomicTheory/02_ConsumerChoice/README.md) |
| [MicroeconomicTheory/03_ClassicalDemand](MicroeconomicTheory/03_ClassicalDemand/README.md) | 3. Classical Demand Theory (with Appendix M.C, M.E, M.F, M.G, M.H, M.J, M.K, M.L) | 949 theorems / 1152 declarations; fresh audit passed; 1 item open | [Chapter overview](MicroeconomicTheory/03_ClassicalDemand/README.md) |
| [MicroeconomicTheory/04_AggregateDemand](MicroeconomicTheory/04_AggregateDemand/README.md) | 4. Aggregate Demand | 204 theorems / 274 declarations; fresh audit passed | [Chapter overview](MicroeconomicTheory/04_AggregateDemand/README.md) |

MWG Chapters 1–4 are implemented.

## Build and verify

From an implemented chapter directory:

```sh
lake exe cache get
python scripts/verify.py
```

Only `propext`, `Classical.choice`, and `Quot.sound` are allowed in the transitive
axiom audit. The verifier checks the complete library and freshly re-elaborates its
source. Documentation distinguishes verified results from outstanding source coverage.

## License and provenance

Apache 2.0; see [LICENSE](LICENSE) and each chapter's third-party notices. Formalization
is developed with OpenAI Codex under the user's direction; the MWG programme is
developed with Claude Code under the user's direction. The textbooks are cited and are
not distributed. Read the [working guidance](AGENTS.md) before contributing;
[UPSTREAM.md](UPSTREAM.md) records possible reusable mathematical contributions and
the duplication checks still required before an upstream proposal.
