# Proposal: Mas-Colell, Whinston and Green, *Microeconomic Theory*, in Lean

**Source.** Andreu Mas-Colell, Michael D. Whinston and Jerry R. Green, *Microeconomic
Theory*, Oxford University Press, 1995. The local copy is
`MWG - Microeconomic Theory.pdf` (kept outside version control): a 501-page **image scan
with no text layer**, two printed pages per PDF page (landscape spreads). PDF page `q`
shows printed pages `2q − 22` and `2q − 21` in the main text (e.g. PDF 100 = pp. 178–179;
checked at PDF 13, 14, 100 and 150, and to be rechecked at each chapter's start).
A working OCR text is kept outside the repository at `~/.cache/lean-builds/mwg-work/ocr/`;
it is a search aid only. Every statement, number and page cited in Lean must be checked
against the rendered page image, since OCR garbles mathematics.

**Book.** 23 chapters in five parts plus a Mathematical Appendix (M.A–M.N), pp. 1–981:

- Part One, Individual Decision Making (Ch 1–6, pp. 3–216)
- Part Two, Game Theory (Ch 7–9, pp. 217–306)
- Part Three, Market Equilibrium and Market Failure (Ch 10–14, pp. 307–510)
- Part Four, General Equilibrium (Ch 15–20, pp. 511–786)
- Part Five, Welfare Economics and Incentives (Ch 21–23, pp. 787–925)
- Mathematical Appendix (pp. 926–971)

Unlike the AKMM macroeconomics text, MWG is theorem-dense: definitions, propositions
and examples are numbered `N.X.k` (chapter, section, item), with proofs given or
assigned. Each chapter ends with graded exercises (A easiest to C hardest), and some
exercises also appear within the text. §3 gives the per-chapter counts.

**Target.** This repository (`LeanEconomics/KrepsFoundations`), in a new top-level folder
`MicroeconomicTheory/` alongside `Volume1/` (Kreps).

**Status.** Proposal 2026-11-12; decisions settled 2026-11-13 (§5). Phase 0 done 2026-11-13
(scaffold branch `mwg-scaffold`): the dependency arrangement was tested with a temporary
stub (see `PROVENANCE.md`). Chapters 1–7 implemented.

---

## 1. Layout

```text
KrepsFoundations/
├── Volume1/                       Kreps, Microeconomic Foundations I (existing)
├── MicroeconomicTheory/           MWG, one independent Lake project per chapter
│   ├── 01_PreferenceChoice/
│   ├── 02_ConsumerChoice/
│   ├── ...
│   └── 23_MechanismDesign/
└── PROPOSAL-MicroeconomicTheory.md
```

- Directory `MicroeconomicTheory/NN_Project/`, with the two-digit chapter number, as in
  `Volume1/`.
- **Lake package and library `MWG<Project>`, namespace `MWG.<Project>`.** These are
  prefixed, unlike Kreps's bare `ConsumerDemand`, because several MWG and Kreps chapters
  share subject names. The joint consistency compile (`consistency/`) and any path
  dependency on a Kreps chapter need distinct library and module roots.
- Per chapter, the existing package layout: README with library map, `CONTRIBUTING.md`,
  `LICENSE`, `THIRD_PARTY_NOTICES.md`, `lakefile.toml`, `lean-toolchain`,
  `lake-manifest.json`, `proof-manifest.json`, `docs/source-map.md`,
  `docs/corrections.md`, `scripts/verify.py` + `test_verify.py` (byte-identical to the
  baseline hashes in `PROVENANCE.md`), and generated `verification/`.
- Root README gets a "Mas-Colell, Whinston and Green" section with the same
  `Project | Chapter | Checked results | Start here` table. CI gets one matrix entry per
  implemented chapter.

## 2. Environment: one shared Mathlib

- Lean `leanprover/lean4:v4.34.0`, Mathlib `v4.34.0` (`5ed2965256430c3649e86755f9576b54eca72435`),
  and the same transitive pins as the Kreps chapters. Copy a Kreps `lake-manifest.json` and
  change only the package name.
- **Exactly one Mathlib on disk.** It lives at
  `~/.cache/lean-builds/EconomicGrowth-SolowSwan/packages/` (14 GB, checked 2026-11-12: the
  only real `packages/mathlib` directory on the machine). Every MWG project gets
  `.lake → ~/.cache/lean-builds/KrepsFoundations-MWG-<Project>/`, whose `packages` is a
  symlink to that shared directory. Never run `lake update` or `lake exe cache get` in a
  way that writes a second Mathlib. If a chapter needs a non-Mathlib git dependency
  (§5 item 2), `packages/` becomes a real directory of per-package symlinks to the shared
  packages plus that one clone, the setup that already works for AKMM. Nothing is written
  into the shared directory.
- The six existing Kreps chapters in this new clone have no `.lake` yet. They get the same
  symlink setup (`KrepsFoundations-<Project>`) before their first build.
- Builds run from a worktree under `~/.cache/lean-builds/worktrees/`, not in Dropbox,
  following the Miao/AKMM practice. Branches `mwg-chNN-<name>` are stacked in book order,
  committed only after `verify.py` passes, and never pushed by the assistant.

## 3. Chapter projects

Counts are from the OCR, normalised for garbled section letters (`8`→B, `0`→D, `€`→E,
`6`→G). They are **lower bounds**: OCR still drops some labels, and theorem-like
claims in small type or running text are not counted. Columns: **D** definitions,
**P** propositions (with lemmas/corollaries in text), **Ex** numbered examples,
**IT** in-text exercises, **EC** end-of-chapter exercises. The book has about
**190 definitions, 170 propositions, 160 examples and 570 end-of-chapter exercises**
(roughly 370 in-text exercises, many repeated at the chapter end), plus 21 definitions
and 31 theorems in the Mathematical Appendix. Kreps chapters K1–K6 are complete in
this repository; K7–K16 are planned. **LE** = LeanEconomics research repo,
**DP** = DynamicProgramming.

| Ch | Directory under `MicroeconomicTheory/` | Pages | D | P | Ex | IT | EC | Closest existing material | Main obstacle |
| ---: | --- | --- | ---: | ---: | ---: | ---: | ---: | --- | --- |
| 1 | `01_PreferenceChoice` | 5–16 | 6 | 4 | 3 | 6 | 10 | K1 (rationality, choice rules, WARP-type coherence, rationalization) | none; mostly bridges to K1 |
| 2 | `02_ConsumerChoice` | 17–39 | 4 | 7 | 1 | 14 | 14 | K3 budgets; K4 | WARP ⇒ Slutsky negative semidefiniteness (differentiable demand) |
| 3 | `03_ClassicalDemand` | 40–104 | 9 | 17 | 5 | 28 | 55 | K2, K3, K4 (SARP/Afriat); K10–K12 planned | duality and integrability (Frobenius/PDE route in 3.H); App A differentiability of demand via implicit function theorem |
| 4 | `04_AggregateDemand` | 105–126 | 4 | 6 | 3 | 17 | 23 | K13 planned | Gorman form ⇔ aggregation; App A regularising effects (distributions over consumers) |
| 5 | `05_Production` | 127–166 | 1 | 7 | 4 | 14 | 20 | K9 planned | App A linear activity model (LP duality, M.M) |
| 6 | `06_ChoiceUnderUncertainty` | 167–216 | 17 | 13 | 13 | 19 | 32 | K5, K6 (vNM, risk aversion, comparative risk aversion, stochastic dominance) | state-dependent and subjective EU (6.E–F), Savage only as stated |
| 7 | `07_NoncooperativeGames` | 219–234 | 5 | 0 | 11 | 2 | 4 | none (Mathlib has no games) | representation of extensive forms, information sets, perfect recall (§5 item 6) |
| 8 | `08_SimultaneousMoveGames` | 235–266 | 11 | 7 | 11 | 10 | 24 | LE Kakutani; DP SetValuedFixedPoints | rationalizability; Nash existence (App A); Bayesian games; trembling-hand perfection |
| 9 | `09_DynamicGames` | 267–306 | 6 | 6 | 10 | 11 | 20 | — | sequential equilibrium (consistency as limits of totally mixed strategies); Rubinstein bargaining (App A) |
| 10 | `10_CompetitiveMarkets` | 311–349 | 4 | 2 | 3 | 15 | 30 | K12 planned (surplus) | partial-equilibrium welfare with quasilinear utility; free-entry long-run equilibria |
| 11 | `11_ExternalitiesPublicGoods` | 350–382 | 2 | 0 | 0 | 10 | 16 | — | App A nonconvexities; mostly derivations |
| 12 | `12_MarketPower` | 383–435 | 0 | 7 | 10 | 23 | 38 | ch 8–9 | folk theorem (App A); Cournot convergence to competition (12.F) |
| 13 | `13_AdverseSelection` | 436–476 | 1 | 5 | 1 | 11 | 19 | ch 9 | signalling equilibria, intuitive criterion (App A); Rothschild–Stiglitz nonexistence |
| 14 | `14_PrincipalAgent` | 477–510 | 0 | 6 | 0 | 7 | 18 | K6 | MLRP/convexity conditions; App B optimal control-style screening solution |
| 15 | `15_GeneralEquilibriumExamples` | 515–544 | 4 | 2 | 2 | 9 | 20 | K14 planned | 2×2 production model (Stolper–Samuelson, Rybczynski): calculus |
| 16 | `16_WelfareTheorems` | 545–577 | 7 | 9 | 3 | 15 | 18 | K15 planned; DP SLP ParetoOptimaEquilibria | second welfare theorem via separation; App A compactness of feasible set |
| 17 | `17_PositiveEquilibriumTheory` | 578–651 | 8 | 23 | 3 | 36 | 42 | LE Kakutani, Brouwer; K14 planned | existence; index theorem and generic regularity (Sard, degree: not in Mathlib); SMD theorem; Shapley–Folkman (17.I); tâtonnement stability |
| 18 | `18_CoreFoundations` | 652–686 | 5 | 5 | 3 | 7 | 10 | K15 planned | core convergence (Debreu–Scarf); App A cooperative games (Bondareva–Shapley) |
| 19 | `19_EquilibriumUncertainty` | 687–731 | 10 | 7 | 22 | 22 | 29 | K16 planned; DP Miao CompleteMarkets | Radner equilibrium; incomplete markets (generic existence is cited, not proved) |
| 20 | `20_EquilibriumTime` | 732–786 | 9 | 13 | 12 | 31 | 38 | DP SLP/Miao (growth, OLG, DP); LE OLG | infinite-dimensional commodity spaces; turnpike/dynamics; OLG inefficiency |
| 21 | `21_SocialChoice` | 789–816 | 19 | 6 | 10 | 14 | 20 | K8 planned (Arrow) | Arrow's theorem; single-peaked domains (Black); Gibbard–Satterthwaite-type results in 21.E |
| 22 | `22_WelfareBargaining` | 817–856 | 15 | 4 | 17 | 30 | 35 | K8 planned | invariance/informational characterisations of SWFs; Nash bargaining and Shapley value axiomatics |
| 23 | `23_MechanismDesign` | 857–925 | 18 | 12 | 13 | 20 | 33 | ch 8, 14, 21 | revelation principle; Gibbard–Satterthwaite; VCG; revenue equivalence; Myerson optimal auction; Myerson–Satterthwaite |
| M | Mathematical Appendix (owned by chapters, §5 item 3) | 926–971 | 21 | 31 thms | 2 | — | — | Mathlib (implicit function, separation, Banach, Tarski); LE Brouwer/Kakutani/Berge | envelope theorem and Kuhn–Tucker as stated; M.N dynamic programming (reuse DP) |

The overlap with Kreps is substantial in Part One (K1–K6 are done) and Part Four
(K9–K16, planned). Under §5 item 2 those chapters are required, not copied. Part Two and
the information chapters (13, 14, 23) have no existing Lean base; Chapter 7's
game-tree design is the foundation for them. No theorem-count estimate is given before
each chapter's source inventory, following the Kreps rule. As a scale guide, Kreps
Chapters 1–6 (147 printed pages) produced about 2,650 audited theorems including copies;
MWG is about six times as long.

## 4. Conventions carried over from Kreps

All of `AGENTS.md` applies unchanged. In particular:

- **Coverage.** The source map accounts for every definition, numbered proposition and
  example, significant unnumbered claim, small-type proof and exercise subpart. Exercises
  that are purely verbal, numerical or graphical are listed as such, and their
  mathematical claims are still proved.
- **Faithfulness.** Preserve the book's domains, quantifiers, strict/weak inequalities and
  differentiability assumptions. A finite special case or an assumed conclusion is
  partial progress, not completion. Where MWG assumes differentiability "for simplicity",
  the source map records whether the result is proved at that generality or more
  generally.
- **Corrections.** A false or imprecise printed claim gets a counterexample and a corrected
  statement in `docs/corrections.md`. An OCR artefact is never a correction: check the
  page image first.
- **Proof standard.** No `sorry`, `admit`, new axioms, `unsafe` or `native_decide`. Only
  `propext`, `Classical.choice` and `Quot.sound`. No Prop-valued hypothesis bundle
  without a proved concrete instance.
- **Citations.** Docstrings cite `MWG, Prop. 3.D.3, p. 56` or `MWG, Exercise 3.D.6, p. 98`.
  Source-numbered aliases follow the existing style: `proposition_3_D_3`,
  `definition_16_C_1`, `exercise_3_D_6`, `proposition_M_K_2`. Nothing from the book is
  reproduced.

## 5. Decisions (settled by the user, 2026-11-13)

1. **Folder, prefix and namespace.** `MicroeconomicTheory/NN_Project/`, Lake package and
   library `MWG<Project>`, namespace `MWG.<Project>`.
2. **Depend, not copy.** An MWG chapter uses existing material through Lake requirements,
   not local copies:
   - `path` requires for projects in this repository (Kreps `Volume1/*` and earlier
     `MicroeconomicTheory/*` chapters);
   - `git` requires pinned to a commit for other LeanEconomics repositories, e.g.
     LeanEconomics (`FixedPoint/` Brouwer, Kakutani, Fan–Glicksberg; `Topology/Berge`) and
     DynamicProgramming (SLP, Miao).

   Every dependency must pin the same Mathlib (v4.34.0). Only the chapter's own modules
   are in its `proof-manifest.json` and audited, and `verify.py` treats dependency modules
   as library imports. This differs from the repository's existing copy rule for
   `Volume1/`. That rule stays in force for Kreps chapters. `AGENTS.md`, `PROVENANCE.md`
   and the CI cache step get an MWG paragraph in Phase 0. Requiring a Kreps chapter
   whose library root is unprefixed (e.g. `ConsumerDemand`) works because MWG roots are
   all prefixed. Phase 0 tests one such co-import. An unused dependency is removed
   before the chapter commits.
3. **Mathematical Appendix.** Each M-section belongs to the first chapter that uses it,
   with appendix-numbered declarations and source-map entries there. Provisional
   owners: M.A–M.E with Ch 2–3, M.F–M.H with Ch 3/8/17, M.I fixed points with Ch 8,
   M.J–M.L with Ch 3/5, M.M linear programming with Ch 5 App A, and M.N dynamic
   programming with Ch 20. Each owner is confirmed at that chapter's dependency
   assessment. There is no separate appendix project, so the `MA_MathematicalAppendix`
   entry in §1 is dropped.
4. **Exercises.** All mathematical exercises, A–C, in-text and end-of-chapter, each subpart
   separately. Verbal, numerical or graphical parts are listed as such, with their
   mathematical claims proved.
5. **Order.** Book order, Chapters 1 → 23.
6. **Game-theory foundations, in scope.** Chapter 7 builds the extensive-form foundation:
   finite game trees, information sets, perfect recall, pure, mixed and behaviour
   strategies, the normal form and Kuhn's theorem where the book uses it. A short design
   note in Chapter 7's README fixes the representation before Chapter 8 starts. Later game
   chapters depend on it.
7. **Hard results in scope.** Sonnenschein–Mantel–Debreu, the index theorem and generic
   local uniqueness (with the needed Sard/degree theory), Shapley–Folkman, core
   convergence, Arrow, Gibbard–Satterthwaite, Myerson's optimal auction,
   Myerson–Satterthwaite and the folk theorem are all built in their chapters. A chapter
   is not complete until they are done or a printed claim is refuted and corrected.

## 6. Plan

- **Phase 0 (on approval).** Worktree from `origin/main`, branch `mwg-scaffold`. Add this
  proposal, the root README section, and the MWG paragraphs in `AGENTS.md`/`PROVENANCE.md`.
  Add `.lake` symlinks to the shared Mathlib for the new and existing projects. Confirm
  `lake build` reuses the shared oleans and fetches no second Mathlib. Test a stub MWG
  project that path-requires one Kreps chapter and git-requires LeanEconomics:
  co-import, `verify.py` and the CI cache step.
- **Per chapter.** (1) OCR-assisted read of the chapter, checking each item against page
  images, and write `docs/source-map.md` with every item. (2) Dependency assessment
  (Mathlib, Kreps chapters, LeanEconomics). (3) Scaffold with its Lake requirements (§5 item 2).
  (4) Formalise in source order. Parallel agents on separate sections, at most two Lean
  processes at once (laptop has 15 GB RAM), with scratch under `~/.cache/lean-builds/`,
  never `/tmp`. (5) Fidelity review against page images. (6) `verify.py`, then commit.
- Stop and ask between chapters unless told otherwise.
