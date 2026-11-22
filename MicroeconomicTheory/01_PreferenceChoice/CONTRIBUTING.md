# Contributing

Fixes, examples and clearer statements are welcome. Contribute only material you have
the right to contribute. Original contributions use the repository's Apache License 2.0;
identify third-party material and preserve its copyright and license notices.

Read the repository [working guidance](../../AGENTS.md) and
[convention provenance](../../PROVENANCE.md). This chapter is an independent Lake project
on the pinned Lean/Mathlib environment. It depends, through a Lake `path` requirement, on
Kreps Chapter 1 (`Volume1/01_ChoicePreferenceUtility`) and uses that material by import,
not by copying. Changes to the dependency must keep this project building.

Use explicit hypotheses and the book's domains, including boundary and empty-set cases.
Connect each source result to its Lean name and printed page. Preserve the distinction
between a full source theorem, a supporting lemma and an unresolved obligation. If the
printed statement needs correction, explain it in `docs/corrections.md` and prove the
corrected statement or an appropriate counterexample.

Search the pinned local Mathlib and the dependency before adding a general result. Verify
lemma names and hypotheses, use focused imports, and keep useful mathematics separate from
the economic specialization. Each Lean file needs its Apache header, module documentation,
UTF-8/LF format and lines no longer than 100 characters. Keep established API names.

Do not introduce proof placeholders, new axioms, `unsafe` shortcuts or `native_decide`.
Keep the verifier and its failure-path tests unchanged. The allowed transitive axioms are
`propext`, `Classical.choice`, and `Quot.sound`; warnings also fail verification.

From this chapter directory, use `lake build MWGPreferenceChoice.ModuleName` while
developing. Before reporting an audited contribution, run:

```sh
python -m unittest discover -s scripts -p 'test_*.py' -v
python scripts/verify.py
```

The verifier builds the whole project, freshly recompiles contributed proofs, and audits
named declarations. Update the root Lean module, `proof-manifest.json`, README library
map, `docs/source-map.md` and `docs/corrections.md` with mathematical changes.
A passing Lean check establishes the encoded statements; source review establishes their
correspondence to MWG. Describe the checks actually performed in the contribution.

Disclose AI assistance accurately and preserve the original attribution of copied work.
