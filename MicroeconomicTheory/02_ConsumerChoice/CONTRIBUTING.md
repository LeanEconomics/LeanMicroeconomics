# Contributing

Fixes, examples and clearer statements are welcome. Contribute only material you have
the right to contribute. Original contributions use the repository's Apache License 2.0;
identify third-party material and preserve its copyright and license notices.

Read the repository [working guidance](../../AGENTS.md), including its section on the
Mas-Colell, Whinston and Green chapters, and the
[programme proposal](../../PROPOSAL-MicroeconomicTheory.md). This chapter is a Lake project
pinned to Lean and Mathlib `v4.34.0`. It depends, through Lake `path` requirements, on Kreps
Chapter 1 (`Volume1/01_ChoicePreferenceUtility`), Kreps Chapter 3
(`Volume1/03_ConsumerDemand`) and MWG Chapter 1 (`01_PreferenceChoice`); it imports their results rather than copying them. Check a
dependency's hypotheses against MWG's statement before using it, and record each use in the
source map.

Use explicit hypotheses and the book's domains (`p ≫ 0`, `w > 0`, consumption set `ℝ^L_+`
unless an exercise says otherwise). Connect each source result to its Lean name and printed
page. Preserve the distinction between a full source theorem, a supporting lemma and an
unresolved obligation. If the printed statement needs correction, explain it in
`docs/corrections.md` and prove the corrected statement or a counterexample. The source is an
image scan: check statements against the page images; OCR artefacts are never corrections.

Search the pinned local Mathlib before adding a general result. Verify lemma names and
hypotheses, use focused imports, and keep useful mathematics separate from the economic
specialization. Each Lean file needs its Apache header, module documentation, UTF-8/LF
format and lines no longer than 100 characters.

Do not introduce proof placeholders, new axioms, `unsafe` shortcuts or `native_decide`.
Keep the verifier and its failure-path tests unchanged. The allowed transitive axioms are
`propext`, `Classical.choice`, and `Quot.sound`; warnings also fail verification.

From this chapter directory, use `lake build MWGConsumerChoice.ModuleName` while developing.
Before reporting an audited contribution, run:

```sh
python3 -m unittest discover -s scripts -p 'test_*.py' -v
python3 scripts/verify.py
```

Update the root Lean module, `proof-manifest.json`, the README library map,
`docs/source-map.md` and `docs/corrections.md` with mathematical changes. A passing Lean check
establishes the encoded statements; source review establishes their correspondence to MWG.
Describe the checks actually performed in the contribution.

Disclose AI assistance accurately and preserve the original attribution of copied work.
