# Contributing

Fixes, examples and clearer statements are welcome. Contribute only material you have
the right to contribute. Original contributions use the repository's Apache License 2.0;
identify third-party material and preserve its copyright and license notices.

Read the repository [working guidance](../../AGENTS.md) (including its MWG section) and
[convention provenance](../../PROVENANCE.md). This chapter is an independent Lake project
pinned to Lean and Mathlib `v4.34.0`. It depends on MWG Chapter 8 (`MWGSimultaneousMoveGames`)
through a Lake `path` requirement, and through it on MWG Chapters 7, 5 and 3 and on
LeanEconomics (fixed-point theorems); their results are imported rather
than copied, and a dependency's hypotheses are checked against MWG before use.

Use explicit hypotheses and the book's domains, including boundary and degenerate cases.
Connect each source result to its Lean name and printed page. Preserve the distinction
between a full source theorem, a supporting lemma and an unresolved obligation. If the
printed statement needs correction, explain it in `docs/corrections.md` and prove the
corrected statement or an appropriate counterexample.

Search the pinned local Mathlib before adding a general result. Verify lemma names and
hypotheses, use focused imports, and keep useful mathematics separate from the economic
specialization. Each Lean file needs its Apache header, module documentation, UTF-8/LF
format and lines no longer than 100 characters.

Do not introduce proof placeholders, new axioms, `unsafe` shortcuts or `native_decide`.
Keep the verifier and its failure-path tests unchanged. The allowed transitive axioms are
`propext`, `Classical.choice`, and `Quot.sound`; warnings also fail verification.

From this chapter directory, use `lake build MWGDynamicGames.ModuleName` while
developing. Before reporting an audited contribution, run:

```sh
python3 -m unittest discover -s scripts -p 'test_*.py' -v
python3 scripts/verify.py
```

Update the root Lean module, `proof-manifest.json`, README library map,
`docs/source-map.md` and `docs/corrections.md` with mathematical changes. A passing Lean
check establishes the encoded statements; source review establishes their correspondence to
MWG. Describe the checks actually performed, and disclose AI assistance accurately.
